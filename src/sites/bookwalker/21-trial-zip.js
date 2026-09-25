    async function downloadTrialZip(ui, config, contents, title, sv, mode, details, archiveName, options = {}) {
        const { barDownload, barDescramble, barMokuro, barUpload } = ui;
        const zip = mode === 'zip' ? { entries: [] } : null;
        const errors = options.errors || [];
        const runResult = options.result || null;
        const okIdx = new Set();
        const t1 = performance.now();

        const jobs = [];
        for (const item of contents) {
            const fid = item.file;
            const isShared = String(fid).indexOf('../shared/') === 0 || String(fid).indexOf('shared/') === 0;
            const base = String(fid).replace(/^(\.\.\/)?shared\//, '');
            const cfg = config[fid] || {};
            const fli = cfg.FileLinkInfo || {};
            const nPages = fli.PageCount || Math.max(1, (fli.PageLinkInfoList || []).length) || 1;
            for (let no = 0; no < nPages; no++) jobs.push({ fid, base, no, isShared });
        }
        const total = jobs.length;
        const outcome = (ok) => {
            if (!runResult) return ok;
            runResult.total = total;
            runResult.pageCount = okIdx.size;
            runResult.errors = errors;
            runResult.ok = !!ok && errors.length === 0;
            return runResult;
        };

        async function cropToSize(blob, S) {
            if (!S || !S.Width || !S.Height) return blob;
            try {
                const bmp = await createImageBitmap(blob);
                if (bmp.width === S.Width && bmp.height === S.Height) { if (bmp.close) bmp.close(); return blob; }
                const c = document.createElement('canvas');
                c.width = S.Width; c.height = S.Height;
                c.getContext('2d').drawImage(bmp, 0, 0);
                if (bmp.close) bmp.close();
                return await new Promise((res2, rej) => c.toBlob(b => b ? res2(b) : rej(new Error('toBlob')), IMAGE_CODEC.type, IMAGE_CODEC.quality));
            } catch (e) { return blob; }
        }

        let mokuroSessionId = null;
        let ocrPoll = null;
        let runSafeTitle = '';
        if (mode === 'ocr') {
            barMokuro.wrap.style.display = 'flex';
            barMokuro.fill.style.width = '0%';
            barMokuro.labRate.textContent = '0/' + total;
            if (!(await ensureBridgeRunning(25000))) {
                throw new Error(MOKURO_BRIDGE_OFFLINE_MSG);
            }
            // Don't start a capture while the bridge is still working on a
            // previous run, unless the automation caller explicitly owns the
            // bridge lifecycle and asks us to skip this global wait.
            if (!options.skipBridgeIdleWait && !(await waitForBridgeIdle(60000))) {
                throw new Error('The Mokuro Bridge is still busy with a previous OCR/upload — wait for it to finish, then try again.');
            }
            const sess = await mokuroStartSession(archiveName || title || 'book');
            mokuroSessionId = sess && sess.session_id;
            if (options.automation && !mokuroSessionId) {
                throw new Error('Mokuro bridge did not return a session_id');
            }
            runSafeTitle = sess.safe_title || sess.title || '';
            if (runResult) {
                runResult.sessionId = mokuroSessionId;
                runResult.safeTitle = runSafeTitle;
            }
            reportRunProgress(options, 'session', {
                sessionId: mokuroSessionId || null, safeTitle: runSafeTitle, total: total
            });
            if (options.pollBridgeStatus !== false) {
                ocrPoll = setInterval(async () => {
                    const st = await mokuroStatus(mokuroSessionId);
                    if (!st) return;
                    const done = (st.pages_ocr_done ?? 0);
                    const got = (st.pages_received ?? 0) || done;
                    updateMokuroBar(barMokuro, done, got, total);
                    reportRunProgress(options, 'bridge-status', {
                        pageCount: got, ocrPageCount: done, total: total
                    });
                }, 700);
                if (options.registerRunCleanup) options.registerRunCleanup(() => {
                    if (ocrPoll) { clearInterval(ocrPoll); ocrPoll = null; }
                });
            }
        }

        let fetched = 0;
        let nextIdx = 0;
        // One upload-bar feed shared by the early cover upload and finalize so
        // the bar tracks the whole multi-file upload (cover = file 1/N).
        const trialUploadFeed = makeUploadBarUpdater(barUpload);
        const trialCoverState = { fired: false };
        async function worker() {
            while (true) {
                const i = nextIdx++;
                if (i >= total) return;
                const j = jobs[i];
                const pageIdx = i + 1;
                try {
                    const rel = j.base + '/' + j.no + '.jpeg';
                    let base = state.baseUrl;
                    const fKey = j.base.split('/').pop();
                    if (state.fileBases && state.fileBases[fKey]) {
                        base = state.fileBases[fKey];
                    } else {
                        const m = (state.baseUrl || '').match(/^(.*\/SVGA\/)(?:[^/]+\/)?$/);
                        if (m) base = m[1] + (j.isShared ? 'shared' : 'normal_default') + '/';
                    }
                    const res = await cdnFetch(() => base + rel + '?' + authQuery(state.auth), 45000);
                    if (!res.ok) throw new Error('HTTP ' + res.status);
                    let blob = await res.blob();
                    const cfg = config[j.fid] || {};
                    const pl = (cfg.FileLinkInfo && cfg.FileLinkInfo.PageLinkInfoList) || [];
                    const S = (pl[j.no] && pl[j.no].Page && pl[j.no].Page.Size) ||
                             (pl[0] && pl[0].Page && pl[0].Page.Size);
                    blob = await cropToSize(blob, S);
                    const pageName = bookWalkerPageName(pageIdx, j.fid);
                    okIdx.add(pageIdx);
                    fetched++;
                    if (zip) zip.entries.push({ path: pageName, blob });
                    if (mode === 'ocr' && mokuroSessionId) {
                        // Cover = first page: push it before OCR finishes so the
                        // folder + upload bar show life; deferred automation
                        // intentionally sends pages only.
                        if (!options.skipCover && pageIdx === 1 && !trialCoverState.fired) {
                            trialCoverState.fired = true;
                            uploadCoverEarly({
                                ui, barUpload, feed: trialUploadFeed,
                                mokuroSessionId, safeTitle: runSafeTitle,
                                blob,
                            }).catch(() => {});
                        }
                        try {
                            await mokuroStreamPage(mokuroSessionId, blob, pageName, pageIdx);
                            reportRunProgress(options, 'page-stream', {
                                page: pageIdx, pageCount: okIdx.size, total: total
                            });
                        }
                        catch (e) { errors.push('OCR page ' + pageIdx + ': ' + safeLogText((e && e.message) || e)); }
                    }
                    if (options.usePageCache && state.cid) cachePage(state.cid, pageIdx, blob);
                } catch (e) {
                    errors.push(j.fid + '#' + j.no + ': ' + safeLogText((e && e.message) || e));
                }
                const el = (performance.now() - t1) / 1000;
                // Download bar tracks pages fetched from the CDN; Descramble
                // bar tracks pages processed (zipped / sent to OCR).
                setBar(barDownload, (fetched / total) * 100, fetched + '/' + total);
                setBar(barDescramble, (okIdx.size / total) * 100, okIdx.size + '/' + total);
                reportRunProgress(options, 'page', {
                    page: pageIdx, pageCount: okIdx.size, total: total
                });
            }
        }
        const CONC = 8;
        const ws = [];
        for (let w = 0; w < CONC; w++) ws.push(worker());
        await Promise.all(ws);

        const secs = ((performance.now() - t1) / 1000).toFixed(1);
        if (okIdx.size === 0) {
            setRunDetails(details,
                msgAllFailedZip(),
                errors);
            if (ocrPoll) { clearInterval(ocrPoll); ocrPoll = null; }
            return outcome(false);
        }
        if (mode === 'ocr' && mokuroSessionId) {
            if (ocrPoll) { clearInterval(ocrPoll); ocrPoll = null; }
            const missingOcr = total - okIdx.size;
            if (options.deferFinalize) {
                // Deferred mode is deliberately page-stream-only.  The external
                // CLI owns /finalize (and any upload/delete policy) later.
                reportRunProgress(options, 'deferred-finalize', {
                    pageCount: okIdx.size, total: total, deferredFinalize: true
                });
                return outcome(missingOcr === 0);
            }
            const { result, plan } = await finalizeOcrSession(mokuroSessionId, ui, barUpload, barMokuro, total, trialUploadFeed, options);
            barMokuro.fill.style.width = '100%';
            barMokuro.labRate.textContent = okIdx.size + '/' + okIdx.size;
            if (missingOcr > 0) {
                setRunDetails(details,
                    msgOcrPartial(missingOcr, total),
                    errors);
            } else {
                if (plan && plan.method === 'local') {
                    const localPath = storedPathOf(result) || plan.localDir;
                    if (localPath) details.textContent = msgStoredLocal(localPath);
                } else if (plan && plan.method) {
                    const rp = result && (result.remote_path || result.mega_path);
                    if (rp) details.textContent = msgUploadedTo(methodShortLabel(plan.method), rp);
                }
                if (errors.length) appendRunDetails(details, errors, 'Issues during the run');
            }
            ui.showReaderButton(result);
            ui.showStoredButton(result);
            return outcome(missingOcr === 0);
        }
        if (zip && okIdx.size > 0) {
            const zipEntries = zip.entries.slice();
            const zipBlob = await buildStoreZip(zipEntries, (done) => {
                const pct = Math.round((done / total) * 100);
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
            const missing = total - okIdx.size;
            if (missing > 0) {
                setRunDetails(details, msgZipPartial(okIdx.size, total), errors);
            } else {
                details.textContent = msgZipSaved(zipEntries.length, fmtBytes(zipBlob.size), secs);
                if (errors.length) appendRunDetails(details, errors, 'Issues during the run');
            }
            // Return success only when nothing is missing: a partial run keeps
            // its page cache so the next run resumes the missing pages.
            return outcome(missing === 0);
        }
        return outcome(false);
    }

    function snapshotViewerResources() {
        try {
            const entries = performance.getEntriesByType('resource') || [];
            state.viewerEntries = entries.map(e => e.name).filter(u => u && (
                u.indexOf('bw-bv-epubs') !== -1 || u.indexOf('epubs-trial') !== -1
            ));
        } catch (e) { state.viewerEntries = []; }
    }
    function resetRunState() {
        // All captured state below is per-book. If this tab has moved to a
        // different cid (SPA-style navigation), the cached config/keys belong
        // to the previous book and would silently download the wrong pages
        // (every CDN path 403s as "session auth expired").
        const currentCid = (new URLSearchParams(location.search)).get('cid') || '';
        const cidChanged = currentCid !== state.cid;
        state.cid = currentCid;
        state.fileBases = {};
        state.auth = null;
        state.baseUrl = null;
        state.viewerEntries = [];
        if (isHeadlessPage()) headlessBid = null;
        if (cidChanged) {
            state.decodedConfig = null;
            state.configBody = null;
            state.configFromUrl = null;
            state.keys = null;
            state.plaintextConfig = false;
            state.cti = null;
        }
    }

