    async function run(ui, mode, options) {
        const runOptions = normalizeRunOptions(options, mode);
        const runResult = runOptions.automation
            ? (runOptions.result || newAutomationResult(mode, state.cid, runOptions.deferFinalize))
            : null;
        if (runResult) {
            runOptions.result = runResult;
            runOptions.errors = runResult.errors;
        }
        const { details, statsEl, barWrap, barDownload, barDescramble, barMokuro, barUpload } = ui;
        let finishedOk = false;
        // Lock the buttons + destination pickers for the whole run: no second
        // download can start concurrently (the 10 s bridge-health tick must
        // never re-enable anything mid-run) and the destination cannot change
        // under it. Previous reader/stored buttons and the Upload bar are cleared.
        ui.setRunLock(true);
        ui.hideReaderButton();
        ui.hideStoredButton();
        barUpload.wrap.style.display = 'none';
        details.textContent = '';
        const t0 = performance.now();
        let cleanupRunCalled = false;
        const runCleanups = [];
        const registerRunCleanup = (fn) => {
            if (typeof fn === 'function') runCleanups.push(fn);
        };
        runOptions.registerRunCleanup = registerRunCleanup;
        const cleanupRun = () => {
            if (cleanupRunCalled) return;
            cleanupRunCalled = true;
            for (let i = runCleanups.length - 1; i >= 0; i--) {
                try { runCleanups[i](); } catch (e) {}
            }
            runCleanups.length = 0;
        };
        reportRunProgress(runOptions, 'started', { mode: mode, cid: state.cid || '' });
        try {
            resetRunState();
            if (runResult) {
                runResult.cid = state.cid || '';
                runResult.mode = mode;
                runResult.deferredFinalize = !!runOptions.deferFinalize;
                reportRunProgress(runOptions, 'book', { cid: runResult.cid, mode: mode });
            }
            reportRunProgress(runOptions, 'state-refresh-start');
            await ensureStateFresh();
            reportRunProgress(runOptions, 'state-refresh-ready');
            const config = state.decodedConfig || decodeConfig(state.configBody);
            const contents = config['configuration'] && config['configuration']['contents'];
            if (!contents || !contents.length) throw new Error('Configuration manifest contains no readable pages.');
            const keys = state.keys;
            let total = contents.length;
            if (runResult) {
                runResult.total = total;
                reportRunProgress(runOptions, 'manifest', {
                    total: total, plaintext: !!(state.plaintextConfig || !keys)
                });
            }

            if ((state.plaintextConfig || !keys) && (mode === 'zip' || mode === 'ocr')) {
                const titleT = cleanTitle(state.cti || document.title) || state.cid;
                const svT = splitSeriesVolume(state.cti || titleT);
                const archiveNameT = ui.syncArchiveDefault(state.cti || document.title || '');
                if (runResult) {
                    runResult.title = titleT;
                    reportRunProgress(runOptions, 'book', { title: titleT, cid: state.cid || '' });
                }
                barWrap.style.display = 'flex';
                barDownload.wrap.style.display = 'flex';
                barDescramble.wrap.style.display = 'flex';
                barDownload.fill.style.width = '0%';
                barDescramble.fill.style.width = '0%';
                const firstCfgT = config[contents[0] && contents[0].file];
                const firstPageT = firstCfgT && firstCfgT.FileLinkInfo && firstCfgT.FileLinkInfo.PageLinkInfoList &&
                    firstCfgT.FileLinkInfo.PageLinkInfoList[0].Page;
                const WT = firstPageT && firstPageT.Size ? firstPageT.Size.Width : '?';
                const HT = firstPageT && firstPageT.Size ? firstPageT.Size.Height : '?';
                let expT = 0;
                for (const it of contents) {
                    const cf = config[it.file] || {};
                    const fli = cf.FileLinkInfo || {};
                    expT += fli.PageCount || Math.max(1, (fli.PageLinkInfoList || []).length) || 1;
                }
                if (!runOptions.headless) {
                    renderBookCard(statsEl, {
                        title: titleT,
                        pages: expT,
                        resolution: `${WT} × ${HT}`,
                        type: 'Sample / Trial'
                    });
                    if (svT.series) fetchAndRenderStats(statsEl, svT.series, svT.volNum);
                }
                const trialResult = await downloadTrialZip(ui, config, contents, titleT, svT, mode, details, archiveNameT, runOptions);
                if (runResult) {
                    if (trialResult && typeof trialResult === 'object') return trialResult;
                    return runResult;
                }
                if (trialResult) finishedOk = true;
                return;
            }

            const firstCfg = config[contents[0].file];
            const firstPage = firstCfg && firstCfg.FileLinkInfo && firstCfg.FileLinkInfo.PageLinkInfoList &&
                firstCfg.FileLinkInfo.PageLinkInfoList[0] && firstCfg.FileLinkInfo.PageLinkInfoList[0].Page;
            const W = firstPage && firstPage.Size ? firstPage.Size.Width : '?';
            const H = firstPage && firstPage.Size ? firstPage.Size.Height : '?';
            const title = cleanTitle(state.cti || document.title) || state.cid;
            const sv = splitSeriesVolume(state.cti || title);
            const archiveName = ui.syncArchiveDefault(state.cti || document.title || '');
            if (runResult) {
                runResult.title = title;
                reportRunProgress(runOptions, 'book', { title: title, cid: state.cid || '' });
            }

            if (!runOptions.headless) renderBookCard(statsEl, {
                title,
                pages: total,
                resolution: `${W} × ${H}`,
                type: 'Full Edition'
            });

            barWrap.style.display = 'flex';
            barDownload.wrap.style.display = 'flex';
            barDescramble.wrap.style.display = 'flex';
            barDownload.fill.style.width = '0%';
            barDescramble.fill.style.width = '0%';

            if (!runOptions.headless && sv.series) fetchAndRenderStats(statsEl, sv.series, sv.volNum);

            const zip = mode === 'zip' ? { entries: [] } : null;

            let mokuroSessionId = null;
            let ocrPoll = null;
            let runSafeTitle = '';
            // One upload-bar feed shared by the early cover upload and finalize
            // so the bar tracks the whole multi-file upload (cover = file 1/N).
            const runUploadFeed = makeUploadBarUpdater(barUpload);
            const runCoverState = { fired: false };
            if (mode === 'ocr') {
                barWrap.style.display = 'flex';
                barMokuro.wrap.style.display = 'flex';
                barMokuro.fill.style.width = '0%';
                barMokuro.labRate.textContent = '0/' + total;
                const bridgeOk = await ensureBridgeRunning(25000);
                if (!bridgeOk) {
                    throw new Error(MOKURO_BRIDGE_OFFLINE_MSG);
                }
                // Don't start a capture while the bridge is still working on a
                // previous run, unless an automation caller explicitly skips
                // this global wait.
                if (!runOptions.skipBridgeIdleWait && !(await waitForBridgeIdle(60000))) {
                    throw new Error('The Mokuro Bridge is still busy with a previous OCR/upload — wait for it to finish, then try again.');
                }
                const sess = await mokuroStartSession(archiveName || title);
                mokuroSessionId = sess && sess.session_id;
                if (runOptions.automation && !mokuroSessionId) {
                    throw new Error('Mokuro bridge did not return a session_id');
                }
                runSafeTitle = sess.safe_title || sess.title || '';
                if (runResult) {
                    runResult.sessionId = mokuroSessionId;
                    runResult.safeTitle = runSafeTitle;
                }
                reportRunProgress(runOptions, 'session', {
                    sessionId: mokuroSessionId || null, safeTitle: runSafeTitle, total: total
                });
                if (runOptions.pollBridgeStatus) {
                    ocrPoll = setInterval(async () => {
                        const st = await mokuroStatus(mokuroSessionId);
                        if (!st) return;
                        const done = st.pages_ocr_done ?? 0;
                        const got = st.pages_received ?? 0;
                        updateMokuroBar(barMokuro, done, got, total);
                        reportRunProgress(runOptions, 'bridge-status', {
                            pageCount: got, ocrPageCount: done, total: total
                        });
                    }, 700);
                    registerRunCleanup(() => {
                        if (ocrPoll) { clearInterval(ocrPoll); ocrPoll = null; }
                    });
                }
            }

            const usePool = detectWorkers();
            const poolSize = usePool ? workerPoolSize() : 0;
            const poolBatchSize = usePool ? workerBatchSize(IMAGE_CODEC.type) : 1;
            const JOB_TIMEOUT = 60000;
            let pool = null;
            if (usePool) pool = makePool(poolSize, buildWorkerSource(), onDone, JOB_TIMEOUT, poolBatchSize);

            let authTimers = [];
            const startAuthTimers = () => {
                authTimers.push(setInterval(async () => {
                    try {
                        if (authRequestBudgetExhausted()) await refreshAuthBest();
                    } catch (e) {}
                }, 5000));
                authTimers.push(setInterval(async () => {
                    try { await refreshAuthBest(); } catch (e) {}
                }, 25000));
            };
            const stopAuthTimers = () => {
                for (const t of authTimers) clearInterval(t);
                authTimers = [];
            };
            startAuthTimers();
            registerRunCleanup(() => {
                stopAuthTimers();
                if (ocrPoll) { clearInterval(ocrPoll); ocrPoll = null; }
                if (pool) pool.terminate();
            });

            let seq = 0;
            const pending = new Map();
            const okIdx = new Set();
            const failedIdx = new Set();
            const missingSections = [];
            let totalJobsSubmitted = 0;
            const errors = runResult ? runResult.errors : [];
            const ocrBuffer = new Map();
            const pageNames = new Map();
            let nextOcr = 1;
            let ocrSent = 0;
            let ocrSendChain = Promise.resolve();
            let pipelineDrain = null;

            async function sendOcrStreaming() {
                while (true) {
                    if (failedIdx.has(nextOcr)) { nextOcr++; continue; }
                    if (!ocrBuffer.has(nextOcr)) break;
                    const blob = ocrBuffer.get(nextOcr);
                    ocrBuffer.delete(nextOcr);
                    const fn = pageNames.get(nextOcr) || ('page-' + String(nextOcr).padStart(4, '0') + '.' + IMAGE_CODEC.ext);
                    try {
                        await mokuroStreamPage(mokuroSessionId, blob, fn, nextOcr);
                        ocrSent++;
                        reportRunProgress(runOptions, 'page-stream', {
                            page: nextOcr, pageCount: okIdx.size, total: total
                        });
                    }
                    catch (e) { errors.push('OCR send page ' + nextOcr + ': ' + safeLogText((e && e.message) || e)); }
                    nextOcr++;
                }
            }
            function scheduleOcrStreaming() {
                // Keep the existing concurrent GUI behavior, but serialize the
                // headless stream so the returned promise cannot race a POST
                // that is still in flight after the last page is decoded.
                if (!runOptions.headless) {
                    sendOcrStreaming();
                    return;
                }
                ocrSendChain = ocrSendChain.then(sendOcrStreaming, sendOcrStreaming).catch(e => {
                    errors.push('OCR stream: ' + safeLogText((e && e.message) || e));
                });
            }

            let fetchedCount = 0;
            function bumpFetched(n) { fetchedCount += n; try { refreshProgress(); } catch (e) {} }
            function refreshProgress() {
                const deCount = okIdx.size;
                const dlCount = Math.min(fetchedCount, total);
                setBar(barDownload, (dlCount / total) * 100, dlCount + '/' + total);
                setBar(barDescramble, (deCount / total) * 100, deCount + '/' + total);
                // NOTE: the Mokuro bar is owned by the dedicated bridge status
                // poll (updateMokuroBar, done/received/total), never write it
                // from here or the two writers fight and the label flickers.
            }

            function settleJob(job, error, blob, crc) {
                if (job.resolved) return;
                job.resolved = true;
                pending.delete(job.id);
                if (error) {
                    errors.push(job.fid + ': ' + error);
                    failedIdx.add(job.index);
                    okIdx.delete(job.index);
                } else {
                    okIdx.add(job.index);
                    failedIdx.delete(job.index);
                    if (zip) zip.entries.push({
                        path: job.name || ('page-' + String(job.index).padStart(4, '0') + '.' + IMAGE_CODEC.ext),
                        blob,
                        crc: Number.isInteger(crc) ? crc : undefined,
                    });
                    if (runOptions.usePageCache && state.cid) cachePage(state.cid, job.index, blob, crc);
                    // Cover = first page: push it before OCR finishes so the
                    // folder + upload bar show life; headless automation
                    // suppresses this extra endpoint and streams pages only.
                    if (!runOptions.skipCover && mokuroSessionId && job.index === 1 && !runCoverState.fired) {
                        runCoverState.fired = true;
                        uploadCoverEarly({
                            ui, barUpload, feed: runUploadFeed,
                            mokuroSessionId, safeTitle: runSafeTitle,
                            blob,
                        }).catch(() => {});
                    }
                    if (mokuroSessionId) {
                        ocrBuffer.set(job.index, blob);
                        if (job.index === nextOcr) scheduleOcrStreaming();
                    }
                }
                reportRunProgress(runOptions, 'page', {
                    page: job.index, pageCount: okIdx.size, total: total, error: error || null
                });
                if (job._resolve) job._resolve();
                refreshProgress();
                if (pipelineDrain) {
                    try { pipelineDrain(); } catch (e) {}
                }
            }

            function onDone(data) {
                const job = pending.get(data.id);
                if (!job) return;
                if (data.error === 'auth-expired' && !job.retried) {
                    job.retried = true;
                    pending.delete(job.id);
                    refreshAuthBest().then(() => {
                        const j2 = Object.assign({}, job, { id: ++seq, retried: true, auth: state.auth, baseUrl: state.baseUrl });
                        pending.set(j2.id, j2);
                        if (pool) pool.submit(j2);
                        else {
                            fetchAndDescramble(j2.relPath, j2.seeds, IMAGE_CODEC.quality, JOB_TIMEOUT, IMAGE_CODEC.type)
                                .then(blob => settleJob(j2, null, blob))
                                .catch(e => settleJob(j2, safeLogText((e && e.message) || e), null));
                        }
                    }).catch(() => settleJob(job, 'Session auth refresh failed', null));
                    return;
                }
                settleJob(job, data.error, data.blob, data.crc);
            }

            async function runJobs(jobList) {
                if (!jobList.length) return;
                try {
                totalJobsSubmitted = jobList.length;
                let prefetchIdx = 0;
                const ready = [];
                const LANE_SLOTS = fetchSocketBudget(true);
                let inflightCap = 4096;
                try {
                    if (typeof window !== 'undefined' && window.__bwddMaxInflight > 0) {
                        inflightCap = Math.max(8, Math.min(4096, window.__bwddMaxInflight | 0));
                    }
                } catch (e) {}
                const NETWORK_BURST = Math.max(8, Math.min(inflightCap,
                    LANE_SLOTS + Math.max(8, Math.round(LANE_SLOTS * 0.2))));
                const PIPELINE_LIMIT = Math.min(NETWORK_BURST, pool
                    ? Math.max(32, poolSize * poolBatchSize * 12)
                    : 8);
                if (BWDD_DEBUG) console.info('[bwdd] lanes=' + allLanes().length + ' sockets=' + LANE_SLOTS +
                    ' in-flight window=' + NETWORK_BURST + ' pipeline cap=' + PIPELINE_LIMIT +
                    ' workers=' + poolSize + ' batch=' + poolBatchSize);
                const prefetchInFlight = new Set();
                const inflightFetch = new Map();

                const wakeChannel = new MessageChannel();
                const wake = () => wakeChannel.port2.postMessage(0);
                let wakePromise = null;
                function waitForWake() {
                    if (!wakePromise) {
                        wakePromise = new Promise(res => {
                            wakeChannel.port1.onmessage = () => { wakePromise = null; res(); };
                        });
                    }
                    return wakePromise;
                }
                pipelineDrain = () => {
                    pumpPrefetch();
                    wake();
                };

                async function fetchOneBlob(j) {
                    const fKey = j.fid ? j.fid.split('/').pop() : null;
                    for (let attempt = 0; attempt < 3; attempt++) {
                        try {
                            const t0 = performance.now();
                            const res = await cdnFetchWithFallback(j.rel, fKey, 45000);
                            if (!res.ok) throw new Error('HTTP ' + res.status);
                            const blob = await res.blob();
                            // Time the whole fetch+body: GM_xhr's onload and
                            // fetch()'s resolution fire at different points, so
                            // header-only timing would under-report the gm lane.
                            recordLane(res._lane, performance.now() - t0, blob.size);
                            return { blob };
                        } catch (e) {
                            const status = e && e.status;
                            if (breakerOpen()) {
                                const wait = Math.min(breakerRemainingMs(), 10000);
                                await new Promise(r => setTimeout(r, Math.max(wait, 800)));
                                continue;
                            }
                            if (status === 403 || status === 0) {
                                try { await refreshAuthBest(); } catch (e2) {}
                                if (attempt < 2) continue;
                            }
                            return { blob: null, error: safeLogText((e && e.message) || e) };
                        }
                    }
                    return { blob: null, error: 'blocked' };
                }

                async function prefetchOne(j) {
                    try {
                        const r = await dedupeInflight(inflightFetch, j.rel, () => fetchOneBlob(j));
                        ready.push({ job: j, blob: r.blob, error: r.error });
                    } catch (e) {
                        const msg = safeLogText((e && e.message) || e);
                        ready.push({ job: j, blob: null, error: msg });
                    } finally {
                        // Exactly one progress tick per job, including the
                        // 'blocked' path (which the old code silently skipped).
                        bumpFetched(1);
                        wake();
                        prefetchInFlight.delete(j.index);
                        pumpPrefetch();
                    }
                }
                function pumpPrefetch() {
                    if (breakerOpen()) return;
                    const burst = effectiveBurst(NETWORK_BURST);
                    while (prefetchInFlight.size < burst && prefetchIdx < jobList.length &&
                        pending.size + prefetchInFlight.size + ready.length < PIPELINE_LIMIT) {
                        const j = jobList[prefetchIdx++];
                        prefetchInFlight.add(j.index);
                        (async () => { try { await prefetchOne(j); } catch (e) {} })();
                    }
                }
                pumpPrefetch();

                const promises = [];
                const totalJobs = jobList.length;
                let consumed = 0;

                async function consumeOne() {
                    while (consumed < totalJobs) {
                        // Keep a small multiple of worker capacity buffered: an
                        // unbounded pool queue would retain the whole volume.
                        while (pending.size >= PIPELINE_LIMIT) {
                            await Promise.race([
                                waitForWake(),
                                new Promise(r => setTimeout(r, 100)),
                            ]);
                        }
                        let item = null;
                        while (!item) {
                            const idx = ready.length ? 0 : -1;
                            if (idx !== -1) {
                                // Remove on dispatch: a `dispatched` flag alone
                                // kept every source Blob alive until runJobs ended.
                                item = ready.splice(idx, 1)[0];
                            } else if (prefetchInFlight.size === 0 && prefetchIdx >= jobList.length && ready.length === 0) {
                                break;
                            } else if (breakerOpen()) {
                                const wait = Math.min(breakerRemainingMs(), 3000);
                                await new Promise(r => setTimeout(r, Math.max(wait, 500)));
                                pumpPrefetch();
                            } else {
                                await Promise.race([
                                    waitForWake(),
                                    new Promise(r => setTimeout(r, 250)),
                                ]);
                            }
                        }
                        if (!item) break;
                        consumed++;
                        const j = item.job;
                        const id = ++seq;
                        const job = { id, index: j.index, name: j.name, fid: j.fid, relPath: j.rel, seeds: j.seeds, auth: state.auth, baseUrl: state.baseUrl, q: IMAGE_CODEC.quality, fmt: IMAGE_CODEC.type, needCrc: !!zip, retried: false };
                        pending.set(id, job);
                        job._resolve = null;
                        const p = new Promise(res => { job._resolve = res; });
                        promises.push(p);
                        if (item.error) {
                            // Prefetch already exhausted its retry/auth path; let
                            // the outer retry round handle it.
                            settleJob(job, item.error, null);
                        } else if (pool && item.blob) {
                            pool.submit({ ...job, blob: item.blob });
                        } else if (pool && !item.blob) {
                            pool.submit(job);
                        } else {
                            (async () => {
                                try {
                                    const blob = item.blob
                                        ? await decodeBlobMain(item.blob, job.seeds, job.q, job.fmt)
                                        : await fetchAndDescramble(job.relPath, job.seeds, job.q, JOB_TIMEOUT, job.fmt);
                                    settleJob(job, null, blob);
                                } catch (e) {
                                    settleJob(job, safeLogText((e && e.message) || e), null);
                                }
                            })();
                        }
                    }
                }
                await consumeOne();

                const deadline = Date.now() + 20 * 60 * 1000;
                let lastCount = -1;
                let lastProgress = Date.now();
                while (true) {
                    const unsettled = [...pending.values()].filter(j => !j.resolved);
                    if (unsettled.length === 0) break;
                    if (Date.now() > deadline) {
                        for (const j of unsettled) settleJob(j, 'Pipeline overall timeout', null);
                        break;
                    }
                    const settledCount = totalJobsSubmitted - unsettled.length;
                    if (settledCount !== lastCount) { lastCount = settledCount; lastProgress = Date.now(); }
                    if (Date.now() - lastProgress > 120000) {
                        for (const j of unsettled) settleJob(j, 'Pipeline stall (' + unsettled.length + ' unfinished)', null);
                        break;
                    }
                    await new Promise(r => setTimeout(r, 300));
                }
                await Promise.all(promises);
                stopAuthTimers();

                // What each transport lane delivered: a separate origin carries a
                // real share at similar latency; one sharing a socket pool stays ~0%.
                if (BWDD_DEBUG) console.info('[bwdd] transport lanes:', laneSummary());
                } finally {
                    pipelineDrain = null;
                    try { wakeChannel.port1.onmessage = null; wakeChannel.port1.close(); } catch (e) {}
                    try { wakeChannel.port2.close(); } catch (e) {}
                }
            }

            const allJobs = [];
            const jobMap = new Map();
            let cachedCount = 0;
            let jobSeq = 0;
            const cacheKey = (i) => i + 1;
            for (let i = 0; i < total; i++) {
                const item = contents[i];
                const fid = item.file;
                const pageCfg = config[fid];
                if (!pageCfg) { errors.push(fid + ': Manifest section missing'); missingSections.push(fid); continue; }
                const list = (pageCfg.FileLinkInfo && pageCfg.FileLinkInfo.PageLinkInfoList) || [];
                const nPages = Math.max(1, list.length);
                for (let no = 0; no < nPages; no++) {
                    jobSeq++;
                    const idx = jobSeq;
                    const cached = (runOptions.usePageCache && state.cid) ? await getCachedPage(state.cid, cacheKey(idx)) : null;
                    if (cached) {
                        const pageName = bookWalkerPageName(idx, fid);
                        pageNames.set(idx, pageName);
                        okIdx.add(idx);
                        if (zip) zip.entries.push({
                            path: pageName,
                            blob: cached,
                            crc: cachedPageCrc.get(cached),
                        });
                        if (mokuroSessionId) { ocrBuffer.set(idx, cached); if (idx === nextOcr) scheduleOcrStreaming(); }
                        cachedCount++;
                        continue;
                    }
                    const seeds = pageSeedsNo(fid, pageCfg, keys[0], keys[1], keys[2], no);
                    const rel = b8gNo(fid, keys[0], keys[1], keys[2], no);
                    const pageName = bookWalkerPageName(idx, fid);
                    pageNames.set(idx, pageName);
                    allJobs.push({ index: idx, name: pageName, fid, rel, seeds, no });
                    jobMap.set(idx, { fid, no });
                }
            }

            const realTotal = jobSeq;
            if (realTotal !== total) {
                total = realTotal;
                if (!runOptions.headless) renderBookCard(statsEl, {
                    title,
                    pages: total,
                    resolution: `${W} × ${H}`,
                    type: 'Full Edition'
                });
            }
            if (runResult) {
                runResult.total = total;
                reportRunProgress(runOptions, 'total', { total: total });
            }
            if (cachedCount) {
                // Cache hits were fetched in an earlier run; count them so the
                // Download bar shares the Descramble bar's baseline instead of
                // showing only pages newly fetched this run.
                fetchedCount += cachedCount;
                refreshProgress();
            }

            // Probe optional transport mirrors only for the normal panel path:
            // headless callers own the browser/bridge lifecycle.
            if (!runOptions.headless) {
                try { await probeFetchProxy(); } catch (e) {}
                try { await probeEdgeMirror(); } catch (e) {}
                try {
                    const firstJob = allJobs[0];
                    if (firstJob) {
                        await probeDotLane(state.baseUrl + firstJob.rel + '?' + authQuery(state.auth));
                    }
                } catch (e) {}
            }

            await runJobs(allJobs);

            for (let round = 0; round < 4; round++) {
                const failedIndexes = [...failedIdx];
                if (!failedIndexes.length) break;
                await refreshAuthBest();
                if (breakerOpen()) {
                    const wait = Math.min(breakerRemainingMs(), 15000);
                    await new Promise(r => setTimeout(r, Math.max(wait, 2000)));
                }
                const beforeCount = failedIdx.size;
                const retryJobs = failedIndexes.map(ix => {
                    const jm = jobMap.get(ix);
                    if (!jm) return null;
                    const pageCfg = config[jm.fid];
                    return {
                        index: ix, name: pageNames.get(ix) || bookWalkerPageName(ix, jm.fid), fid: jm.fid, no: jm.no,
                        rel: b8gNo(jm.fid, keys[0], keys[1], keys[2], jm.no),
                        seeds: pageSeedsNo(jm.fid, pageCfg, keys[0], keys[1], keys[2], jm.no),
                    };
                }).filter(Boolean);
                await runJobs(retryJobs);
                if (failedIdx.size >= beforeCount && round >= 1) break;
            }

            if (mokuroSessionId) {
                if (runOptions.headless) await ocrSendChain;
                for (let i = 1; i <= total; i++) {
                    if (failedIdx.has(i)) continue;
                    const blob = ocrBuffer.get(i);
                    if (!blob) continue;
                    ocrBuffer.delete(i);
                    const fn = pageNames.get(i) || ('page-' + String(i).padStart(4, '0') + '.' + IMAGE_CODEC.ext);
                    try {
                        await mokuroStreamPage(mokuroSessionId, blob, fn, i);
                        ocrSent++;
                        reportRunProgress(runOptions, 'page-stream', {
                            page: i, pageCount: okIdx.size, total: total
                        });
                    }
                    catch (e) { errors.push('Final OCR send page ' + i + ': ' + safeLogText((e && e.message) || e)); }
                }
                if (ocrPoll) { clearInterval(ocrPoll); ocrPoll = null; }
                const missingOcr = total - okIdx.size;
                if (runOptions.deferFinalize) {
                    // Return only after every descrambled page POST has settled;
                    // the external CLI owns the later /finalize request.
                    runResult.pageCount = okIdx.size;
                    runResult.total = total;
                    runResult.errors = errors;
                    runResult.deferredFinalize = true;
                    runResult.ok = missingOcr === 0 && errors.length === 0 && ocrSent === okIdx.size;
                    reportRunProgress(runOptions, 'deferred-finalize', {
                        pageCount: okIdx.size, total: total, deferredFinalize: true,
                        streamed: ocrSent, ok: runResult.ok
                    });
                    return runResult;
                }
                barMokuro.wrap.style.display = 'flex';
                const { result, plan } = await finalizeOcrSession(mokuroSessionId, ui, barUpload, barMokuro, total, runUploadFeed, runOptions);
                const secs = ((performance.now() - t0) / 1000).toFixed(1);
                if (failedIdx.size === 0 && errors.length === 0) finishedOk = true;
                barMokuro.fill.style.width = '100%';
                barMokuro.labRate.textContent = okIdx.size + '/' + okIdx.size;
                if (missingOcr > 0) {
                    if (!runOptions.headless) setRunDetails(details,
                        msgOcrPartial(missingOcr, total),
                        errors);
                } else {
                    if (!runOptions.headless && plan && plan.method === 'local') {
                        const localPath = storedPathOf(result) || plan.localDir;
                        if (localPath) details.textContent = msgStoredLocal(localPath);
                    } else if (!runOptions.headless && plan && plan.method) {
                        const rp = result && (result.remote_path || result.mega_path);
                        if (rp) details.textContent = msgUploadedTo(methodShortLabel(plan.method), rp);
                    }
                    if (!runOptions.headless && errors.length) appendRunDetails(details, errors, 'Issues during the run');
                }
                if (runResult) {
                    runResult.pageCount = okIdx.size;
                    runResult.total = total;
                    runResult.errors = errors;
                    runResult.deferredFinalize = false;
                    runResult.ok = missingOcr === 0 && errors.length === 0;
                    reportRunProgress(runOptions, 'finalized', {
                        pageCount: okIdx.size, total: total, ok: runResult.ok
                    });
                    return runResult;
                }
                ui.showReaderButton(result);
                ui.showStoredButton(result);
                return;
            }

            if (!zip) {
                if (runResult) {
                    runResult.pageCount = okIdx.size;
                    runResult.total = total;
                    runResult.errors = errors;
                    runResult.ok = false;
                    return runResult;
                }
                return;
            }
            if (okIdx.size === 0) {
                setRunDetails(details,
                    msgAllFailedZip(),
                    errors);
                if (runResult) {
                    runResult.pageCount = 0;
                    runResult.total = total;
                    runResult.errors = errors;
                    runResult.ok = false;
                    reportRunProgress(runOptions, 'complete', runResult);
                    return runResult;
                }
                return;
            }

            barDownload.wrap.style.display = 'flex';
            barDescramble.wrap.style.display = 'flex';
            barMokuro.wrap.style.display = 'none';
            barDownload.fill.style.width = '0%';
            barDownload.labRate.textContent = 'Storing';
            barDescramble.fill.style.width = '100%';
            barDescramble.labRate.textContent = '100%';

            const zipEntries = zip.entries.slice();
            const totalEntries = zipEntries.length;
            const zipBlob = await buildStoreZip(zipEntries, (done) => {
                const pct = Math.round((done / totalEntries) * 100);
                barDownload.fill.style.width = pct + '%';
                barDownload.labRate.textContent = pct + '%';

            });

            const url = URL.createObjectURL(zipBlob);
            const a = document.createElement('a');
            a.href = url;
            a.download = (archiveName || zipBaseName(sv, title)) + '.zip';
            const anchorHost = document.body || document.documentElement;
            if (anchorHost) anchorHost.appendChild(a);
            a.click();
            setTimeout(() => { URL.revokeObjectURL(url); a.remove(); }, 4000);

            const secs = ((performance.now() - t0) / 1000).toFixed(1);
            if (errors.length === 0) finishedOk = true;
            const missing = total - okIdx.size;
            // A missing manifest section contributes no page indices, so `missing`
            // alone would still read "Saved 250 of 250" while a section failed.
            if (missing > 0 || missingSections.length) {
                setRunDetails(details, msgZipPartial(okIdx.size, total), errors);
            } else {
                details.textContent = msgZipSaved(totalEntries, fmtBytes(zipBlob.size), secs);
                if (errors.length) appendRunDetails(details, errors, 'Issues during the run');
            }
            if (runResult) {
                runResult.pageCount = okIdx.size;
                runResult.total = total;
                runResult.errors = errors;
                runResult.ok = missing === 0 && errors.length === 0;
                reportRunProgress(runOptions, 'complete', runResult);
                return runResult;
            }
        } catch (e) {
            const message = e && e.message ? safeLogText(e.message) : 'something went wrong — see the browser console for details.';
            if (runResult) {
                runResult.ok = false;
                if (message && !runResult.errors.includes(message)) runResult.errors.push(message);
                reportRunProgress(runOptions, 'failed', {
                    ok: false, errors: runResult.errors
                });
                const error = e instanceof Error ? e : new Error(String(message));
                error.bwddResult = runResult;
                throw error;
            }
            details.textContent = 'Error: ' + message;
        } finally {
            try { cleanupRun(); } catch (e) {}
            if (finishedOk && runOptions.usePageCache) await clearPageCache();
            // Re-derive the enabled state from the bridge health, if the
            // bridge dropped mid-run, the OCR button stays disabled afterwards.
            ui.setRunLock(false);
        }
    }

