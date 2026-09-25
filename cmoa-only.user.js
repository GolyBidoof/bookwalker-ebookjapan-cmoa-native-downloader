// ==UserScript==
// @name         CMOA Native Downloader
// @namespace    http://tampermonkey.net/
// @version      2.0.0
// @description  Saves a book from the CMOA speed reader as a ZIP or CBZ of full-resolution page images, fetched from the CDN and unscrambled offline. Optional Japanese OCR through mokuro-bridge, with upload to MEGA, Google Drive or OneDrive.
// @author       GolyBidoof
// @homepageURL  https://github.com/GolyBidoof/bookwalker-ebookjapan-cmoa-native-downloader
// @supportURL   https://github.com/GolyBidoof/bookwalker-ebookjapan-cmoa-native-downloader/issues
// @updateURL    https://github.com/GolyBidoof/bookwalker-ebookjapan-cmoa-native-downloader/releases/latest/download/cmoa-only.user.js
// @downloadURL  https://github.com/GolyBidoof/bookwalker-ebookjapan-cmoa-native-downloader/releases/latest/download/cmoa-only.user.js
// @match        https://www.cmoa.jp/bib/speedreader/*
// @icon         https://www.google.com/s2/favicons?sz=64&domain=cmoa.jp
// @grant        GM_xmlhttpRequest
// @connect      learnnatively.com
// @connect      manga-kotoba.com
// @connect      www.cmoa.jp
// @connect      free-binb-cmoa.akamaized.net
// @connect      binb-cmoa.akamaized.net
// @run-at       document-end
// @license      MIT
//
// CMOA only, built from the same shared core as the BookWalker script. It
// matches nothing outside the CMOA speed reader and does not carry a single
// line of BookWalker code. Install this OR the combined script, never both:
// they match the same hosts and you would get two panels.
//
// CREDITS
//   - BookWalker viewer protocol reverse-engineered and validated against
//     live HAR captures + the bookworm offline client (github.com/aaa4xu/bookworm).
//   - CMOA speed-reader protocol ported from the original standalone CMOA
//     userscript; the page descriptors and the tile-shuffle geometry come from
//     the store's own SpeedBinb viewer.
//   - Reading stats from LearnNatively (learnnatively.com, by Brandon) and
//     manga-kotoba (manga-kotoba.com, by ChristopherFritz); they own that
//     data and its styling.
//   - OCR via mokuro: a performant fork of kha-white/mokuro
//     (github.com/GolyBidoof/mokuro), run through the companion
//     mokuro-bridge app (github.com/GolyBidoof/mokuro-bridge);
//     upload backend is the bridge's own.
//   - Built with DeepSeek V4 Flash (deepseek.com), the coding model that
//     reverse-engineered and ported the crypto/descramble logic with the author.
//
// NOTE ON PERMISSIONS:
//   On first install Tampermonkey asks for cross-origin access to
//   learnnatively.com, manga-kotoba.com and whichever storefronts this build
//   queries. Those permissions power the reading-stat cards and, in the
//   combined build, the "also available on" store links, which ask each shop's
//   own search page whether it carries the series. If you decline them, the
//   script still works fully for downloading/Mokuro; the LearnNatively card
//   falls back to a public CORS proxy (or hides), and the store links cannot be
//   resolved, so they are simply not shown.
// ==/UserScript==
(function () {
    'use strict';

    // Derived from the installed metadata, not a hardcoded copy: a pinned literal
    // silently goes stale across releases, so the panel reports an old version no
    // matter which build is actually running.
    const BWDD_VERSION = (() => {
        try {
            const v = (typeof GM_info !== 'undefined') && GM_info.script && GM_info.script.version;
            if (v) return v;
        } catch (e) { /* not in a userscript manager (e.g. injected in a test) */ }
        return '2.0.0';   // the single source of truth: build.mjs substitutes this into @version
    })();
    // Debug-only: internals on window.* are exposed only when the page URL
    // carries ?bwddDebug=1, so page scripts cannot reach mutable script state by
    // default. It lives in the shared core because the core itself logs through
    // it.
    const BWDD_DEBUG = (() => {
        try { return new URLSearchParams(location.search).has('bwddDebug'); } catch (e) { return false; }
    })();
    const BWDD_AUTHOR = 'GolyBidoof';
    const BWDD_REPO_URL = 'https://github.com/GolyBidoof/bookwalker-ebookjapan-cmoa-native-downloader';

    // Headless automation is deliberately a page-level opt-in.  Keeping the
    // check in one helper means the normal panel path never has to know about
    // it, while a Puppeteer caller can inject the flag before the script runs.
    function isHeadlessPage() {
        try {
            return window.__BWDD_HEADLESS__ === true || !!window.__BWDD_CLI__;
        } catch (e) { return false; }
    }

    // Error messages from fetch failures can echo a request URL. Keep signed CDN
    // query parameters and URL credentials out of page logs even in headed mode;
    // this is deliberately independent of the CLI's queue sanitization.
    function safeLogText(value) {
        let text = String(value == null ? '' : value);
        text = text.replace(/https?:\/\/[^\s"'<>]+/gi, match => {
            try {
                const url = new URL(match);
                if (url.username || url.password) return '[redacted-url]';
                url.search = '';
                url.hash = '';
                return url.toString();
            } catch (_) {
                return '[redacted-url]';
            }
        });
        text = text.replace(
            /\b(authorization|proxy-authorization|cookie|set-cookie|x-api-key|api-key|password|passwd|client-secret|client_secret)\s*([:=])\s*[^\r\n,}]*/gi,
            '$1$2[redacted]'
        );
        return text.replace(
            /\b(auth[_-]?info|policy|signature|key[-_]?pair[-_]?id|token|csrf|xsrf|api[_-]?key|apikey|password|passwd|secret|private[_-]?key|client[_-]?secret)\s*([:=])\s*("[^"]*"|[^\s,;}]+)/gi,
            '$1$2[redacted]'
        );
    }

    const automationMemory = {
        status: {
            state: 'idle', status: 'idle', ok: false, mode: null, cid: '', title: '',
            total: 0, pageCount: 0, sessionId: null, safeTitle: null,
            deferredFinalize: false, errors: []
        },
        events: [], listeners: new Set(), running: null, lastEvent: null
    };
    function automationSnapshot() {
        const s = automationMemory.status;
        return {
            state: s.state, status: s.status || s.state || 'idle', ok: !!s.ok, mode: s.mode || null,
            cid: s.cid || '', title: s.title || '', total: s.total || 0,
            pageCount: s.pageCount || 0, sessionId: s.sessionId || null,
            bridgeSessionId: s.sessionId || null,
            safeTitle: s.safeTitle || null, deferredFinalize: !!s.deferredFinalize,
            errors: Array.isArray(s.errors) ? s.errors.slice() : []
        };
    }
    function automationEvent(event, runtime) {
        const ev = Object.assign({ at: Date.now() }, event || {});
        automationMemory.events.push(ev);
        if (automationMemory.events.length > 200) automationMemory.events.shift();
        automationMemory.lastEvent = ev;
        for (const fn of automationMemory.listeners) {
            try { fn(Object.assign({}, ev, { errors: Array.isArray(ev.errors) ? ev.errors.slice() : undefined })); } catch (e) {}
        }
        if (runtime && typeof runtime.onEvent === 'function') {
            try { runtime.onEvent(Object.assign({}, ev)); } catch (e) {}
        }
    }
    function reportRunProgress(options, type, fields) {
        if (!options) return;
        const patch = fields || {};
        const event = Object.assign({
            type: type || 'progress', mode: options.mode || null
        }, patch);
        if (options.automation) {
            const s = automationMemory.status;
            const keys = ['ok', 'status', 'mode', 'cid', 'title', 'total', 'pageCount', 'sessionId', 'safeTitle', 'deferredFinalize', 'errors'];
            for (const key of keys) if (Object.prototype.hasOwnProperty.call(patch, key)) s[key] = patch[key];
            s.state = type === 'complete' ? 'complete' : (type === 'failed' ? 'failed' : 'running');
            s.status = type === 'complete' ? (s.deferredFinalize ? 'ocr_pending' : 'completed')
                : (type === 'failed' ? 'failed' : 'running');
            automationEvent(Object.assign({}, automationSnapshot(), event), options.automationRuntime);
        }
        if (typeof options.onProgress === 'function') {
            try {
                options.onProgress(Object.assign({}, event, {
                    errors: Array.isArray(event.errors) ? event.errors.slice() : undefined
                }));
            } catch (e) { /* a consumer callback must never break a download */ }
        }
        try {
            if (typeof window.__bwddProgress === 'function') {
                window.__bwddProgress(Object.assign({}, event, {
                    errors: Array.isArray(event.errors) ? event.errors.slice() : undefined
                }));
            }
        } catch (e) { /* the page-level hook is best effort */ }
    }
    function newAutomationResult(mode, cid, deferredFinalize) {
        return {
            ok: false, mode: mode, cid: cid || '', title: '', total: 0,
            pageCount: 0, errors: [], deferredFinalize: !!deferredFinalize
        };
    }
    function headlessBar() {
        return {
            style: {}, wrap: { style: {} },
            fill: { style: {}, setAttribute() {} },
            labName: { textContent: '' }, labRate: { textContent: '' }
        };
    }
    function makeHeadlessUI() {
        const details = {
            textContent: '',
            append() {}, appendChild() {}, removeChild() {}
        };
        return {
            details: details, statsEl: null,
            barWrap: headlessBar(), barDownload: headlessBar(),
            barDescramble: headlessBar(), barMokuro: headlessBar(),
            barUpload: headlessBar(), destSelect: null, localDirInput: null,
            setRunLock() {}, hideReaderButton() {}, hideStoredButton() {},
            showReaderButton() {}, showStoredButton() {},
            syncArchiveDefault(raw) {
                if (ACTIVE_SITE && typeof ACTIVE_SITE.archiveDefault === 'function') {
                    return ACTIVE_SITE.archiveDefault(raw) || 'book';
                }
                return archiveDefaultName(raw) || fsSafePath(siteCid()) || 'book';
            }
        };
    }
    function normalizeRunOptions(options, mode) {
        const o = options && typeof options === 'object' ? Object.assign({}, options) : {};
        const headless = o.headless === true || o.automation === true || isHeadlessPage();
        const onProgress = typeof o.onProgress === 'function' ? o.onProgress : null;
        const deferredFinalize = mode === 'ocr' && (
            o.deferFinalize === true || o.deferredFinalize === true || o.finalize === false || o.finalizeLater === true
        );
        return Object.assign({}, o, {
            mode: mode,
            automation: headless || o.automation === true,
            headless: headless,
            deferFinalize: deferredFinalize,
            deferredFinalize: deferredFinalize,
            skipBridgeIdleWait: o.skipBridgeIdleWait === true || o.skipBridgeIdle === true || o.skipIdleWait === true,
            skipCover: headless || o.skipCover === true,
            pollBridgeStatus: o.pollBridgeStatus === true || (!headless && o.pollBridgeStatus !== false),
            usePageCache: !headless && o.usePageCache !== false,
            onProgress: onProgress,
            result: o.result || null,
            automationRuntime: o.automationRuntime || null
        });
    }
    function installHeadlessAutomation() {
        if (!isHeadlessPage()) return;
        const api = {
            version: BWDD_VERSION,
            get status() { return automationSnapshot(); },
            get lastStatus() { return automationMemory.lastEvent ? Object.assign({}, automationMemory.lastEvent) : null; },
            get events() { return automationMemory.events.slice(); },
            getState() { return automationSnapshot(); },
            progress() { return automationSnapshot(); },
            getProgress() { return automationSnapshot(); },
            activateCapture() {
                try {
                    if (ACTIVE_SITE && typeof ACTIVE_SITE.install === 'function') ACTIVE_SITE.install();
                    return true;
                } catch (_) {
                    return false;
                }
            },
            subscribe(fn) {
                if (typeof fn !== 'function') throw new TypeError('Automation event listener must be a function');
                automationMemory.listeners.add(fn);
                return () => automationMemory.listeners.delete(fn);
            },
            onEvent(fn) { return api.subscribe(fn); },
            async start(options) {
                if (automationMemory.running) {
                    throw new Error('A BookWalker downloader automation run is already in progress');
                }
                const requestedMode = options && options.mode ? String(options.mode).toLowerCase() : 'ocr';
                if (requestedMode !== 'ocr' && requestedMode !== 'zip') {
                    throw new Error('Automation mode must be "ocr" or "zip"');
                }
                if (ACTIVE_SITE && typeof ACTIVE_SITE.install === 'function') {
                    try { ACTIVE_SITE.install(); } catch (_) {}
                }
                const runOptions = normalizeRunOptions(options, requestedMode);
                const result = runOptions.result || newAutomationResult(requestedMode, siteCid(), runOptions.deferFinalize);
                runOptions.result = result;
                runOptions.automation = true;
                runOptions.headless = true;
                runOptions.automationRuntime = { onEvent: options && options.onEvent };
                automationMemory.running = runOptions.automationRuntime;
                Object.assign(automationMemory.status, automationSnapshot(), result, {
                    state: 'starting', status: 'running', ok: false, errors: result.errors
                });
                automationEvent(Object.assign({}, automationSnapshot(), { type: 'starting' }), runOptions.automationRuntime);
                try {
                    const finished = await siteRun(makeHeadlessUI(), requestedMode, runOptions);
                    const value = finished && finished.ok !== undefined ? finished : result;
                    value.bridgeSessionId = value.sessionId || value.bridgeSessionId || null;
                    value.pageCount = Number(value.pageCount || 0);
                    value.total = Number(value.total || 0);
                    value.ok = value.ok === true && value.errors.length === 0;
                    value.status = value.deferFinalize || value.deferredFinalize
                        ? (value.ok ? 'ocr_pending' : 'failed')
                        : (value.ok ? 'completed' : 'failed');
                    reportRunProgress(runOptions, value.ok ? 'complete' : 'failed', value);
                    automationMemory.running = null;
                    return value;
                } catch (e) {
                    const error = e instanceof Error ? e : new Error(String(e && e.message || e || 'Automation failed'));
                    reportRunProgress(runOptions, 'failed', {
                        ok: false, errors: result.errors.concat([error.message])
                    });
                    automationMemory.running = null;
                    throw error;
                }
            }
        };
        window.__bwddAutomation = api;
    }

    // A property of the archiver rather than of either store's reader, so the
    // core owns it.
    const JPEG_QUALITY = 0.92;
    //   localStorage.bwddImageFormat  = 'jpeg' | 'webp' | 'lossless' | 'png'
    //   localStorage.bwddImageQuality = 0.85      (0-1, lossy formats only)
    // The CDN already hands us a lossy JPEG, so re-encoding is a second
    // generation. Measured on a 1600x2400 manga page (bytes / encode ms):
    // jpeg 0.92 0.94 MB / 14 (default), jpeg 0.85 0.79 / 13, webp 0.92 0.75 / 180,
    // webp lossless 0.18 / 47 (bit-exact), png 0.69 / 15. On photo pages lossless
    // costs far more (webp lossless 3.4 MB / 592 ms), so it stays a choice rather
    // than a default. image/jxl and image/avif are not encodable here:
    // convertToBlob silently returns PNG for both.
    function resolveImageCodec() {
        let fmt = 'jpeg', quality = JPEG_QUALITY;
        try {
            const f = String((window.__bwddImageFormat != null
                ? window.__bwddImageFormat
                : (!isHeadlessPage() ? localStorage.getItem('bwddImageFormat') : '')) || '').toLowerCase();
            if (f === 'jpeg' || f === 'jpg' || f === 'webp' || f === 'png' || f === 'lossless') {
                fmt = (f === 'jpg') ? 'jpeg' : f;
            }
            const raw = window.__bwddImageQuality != null
                ? window.__bwddImageQuality
                : (!isHeadlessPage() ? localStorage.getItem('bwddImageQuality') : null);
            const qv = parseFloat(raw);
            if (isFinite(qv) && qv > 0 && qv <= 1) quality = qv;
        } catch (e) { /* opaque origin, or storage disabled, keep the defaults */ }
        // 'lossless' is WebP at quality 1, which is bit-exact; browsers without a
        // WebP encoder fall back to PNG, which is lossless too. Either way the
        // lossless setting really is lossless.
        if (fmt === 'lossless') return { fmt, type: 'image/webp', quality: 1, ext: 'webp', lossless: true };
        if (fmt === 'webp') return { fmt, type: 'image/webp', quality, ext: 'webp', lossless: false };
        if (fmt === 'png') return { fmt, type: 'image/png', quality, ext: 'png', lossless: true };
        return { fmt: 'jpeg', type: 'image/jpeg', quality, ext: 'jpg', lossless: false };
    }
    // Mutable: the panel changes it, and the next download must pick it up without
    // a page reload, so nothing may cache this at load time.
    let IMAGE_CODEC = resolveImageCodec();
    function refreshImageCodec() {
        IMAGE_CODEC = resolveImageCodec();
        return IMAGE_CODEC;
    }
    // -----------------------------------------------------------------
    // Page cache (IndexedDB)
    // -----------------------------------------------------------------
    let pageDB = null;
    function openPageDB() {
        return new Promise((resolve, reject) => {
            if (pageDB) return resolve(pageDB);
            try {
                const req = indexedDB.open('bwdd-pages-v2', 1);
                req.onupgradeneeded = () => {
                    const db = req.result;
                    if (!db.objectStoreNames.contains('pages')) db.createObjectStore('pages');
                };
                req.onsuccess = () => { pageDB = req.result; resolve(pageDB); };
                req.onerror = () => reject(req.error);
            } catch (e) { reject(e); }
        });
    }
    // Entries are {blob, ts, crc}: ts enforces the TTL and the size cap keeps the
    // cache from eating the browser's disk. Keys include the codec and quality so
    // a format change cannot reuse the wrong output blob or CRC.
    const PAGE_CACHE_TTL_MS = 20 * 60 * 1000;
    const PAGE_CACHE_MAX_ENTRIES = 4000;        // safety cap (~3 GB at 700 KB/page)
    const PAGE_CACHE_PRUNE_INTERVAL_MS = 30 * 1000;
    const cachedPageCrc = new WeakMap();
    let pageCachePruneTimer = null;
    let pageCachePruneInFlight = null;
    let pageCachePruneRequested = false;
    let lastPageCachePruneAt = 0;
    function schedulePageCachePrune(delayMs) {
        // Headless automation intentionally does not keep a page-cache
        // housekeeping timer alive between Puppeteer runs.
        if (isHeadlessPage()) return;
        // A full cursor scan after every put turns a 300-page run into hundreds
        // of overlapping O(cache-size) scans. Keep at most one periodic prune.
        if (pageCachePruneInFlight) {
            // A write that arrived while the cursor was walking would otherwise
            // leave no future trigger once that walk finishes.
            pageCachePruneRequested = true;
            return;
        }
        if (pageCachePruneTimer !== null) return;
        const earliest = lastPageCachePruneAt + PAGE_CACHE_PRUNE_INTERVAL_MS;
        const delay = Math.max(delayMs || 0, earliest - Date.now());
        pageCachePruneTimer = setTimeout(() => {
            pageCachePruneTimer = null;
            lastPageCachePruneAt = Date.now();
            pageCachePruneInFlight = prunePageCache();
            const done = () => {
                pageCachePruneInFlight = null;
                if (pageCachePruneRequested) {
                    pageCachePruneRequested = false;
                    schedulePageCachePrune();
                }
            };
            pageCachePruneInFlight.then(done, done);
        }, delay);
    }
    function pageCacheKey(cid, index) {
        const type = (typeof IMAGE_CODEC !== 'undefined' && IMAGE_CODEC.type) || 'image/jpeg';
        const quality = (typeof IMAGE_CODEC !== 'undefined' && IMAGE_CODEC.quality) || '';
        return cid + ':' + index + ':' + type + ':' + quality;
    }
    async function cachePage(cid, index, blob, crc) {
        try {
            const db = await openPageDB();
            const key = pageCacheKey(cid, index);
            const record = { blob, ts: Date.now() };
            if (Number.isInteger(crc)) record.crc = crc;
            await new Promise((res, rej) => {
                const tx = db.transaction('pages', 'readwrite');
                tx.objectStore('pages').put(record, key);
                tx.oncomplete = () => res(true);
                tx.onerror = () => rej(tx.error);
            });
            schedulePageCachePrune();
            return true;
        } catch (e) { return false; }
    }
    async function getCachedPage(cid, index) {
        try {
            const db = await openPageDB();
            const v = await new Promise((res) => {
                const tx = db.transaction('pages', 'readonly');
                const rq = tx.objectStore('pages').get(pageCacheKey(cid, index));
                rq.onsuccess = () => res(rq.result || null);
                rq.onerror = () => res(null);
            });
            if (v && v.blob) {
                if (Number.isInteger(v.crc)) cachedPageCrc.set(v.blob, v.crc);
                return v.blob;
            }
            return null;
        } catch (e) { return null; }
    }
    async function prunePageCache() {
        try {
            const db = await openPageDB();
            const now = Date.now();
            await new Promise((res) => {
                const tx = db.transaction('pages', 'readwrite');
                const st = tx.objectStore('pages');
                const req = st.openCursor();
                req.onsuccess = () => {
                    const cur = req.result;
                    if (!cur) { res(true); return; }
                    const val = cur.value;
                    if (val && val.ts && (now - val.ts) > PAGE_CACHE_TTL_MS) {
                        cur.delete();
                    }
                    cur.continue();
                };
                tx.oncomplete = () => res(true);
                req.onerror = () => res(true);
            });
            await new Promise((res) => {
                const tx = db.transaction('pages', 'readwrite');
                const st = tx.objectStore('pages');
                const countReq = st.count();
                countReq.onsuccess = () => {
                    const n = countReq.result;
                    if (n <= PAGE_CACHE_MAX_ENTRIES) { res(true); return; }
                    const delReq = st.openCursor();
                    let toDelete = n - PAGE_CACHE_MAX_ENTRIES;
                    delReq.onsuccess = () => {
                        const cur = delReq.result;
                        if (!cur || toDelete <= 0) { res(true); return; }
                        cur.delete(); toDelete--;
                        cur.continue();
                    };
                    delReq.onerror = () => res(true);
                };
                countReq.onerror = () => res(true);
            });
        } catch (e) {}
    }
    async function clearPageCache() {
        try {
            if (pageCachePruneTimer !== null) {
                clearTimeout(pageCachePruneTimer);
                pageCachePruneTimer = null;
            }
            if (pageCachePruneInFlight) {
                try { await pageCachePruneInFlight; } catch (e) {}
                pageCachePruneInFlight = null;
            }
            if (pageCachePruneTimer !== null) {
                clearTimeout(pageCachePruneTimer);
                pageCachePruneTimer = null;
            }
            pageCachePruneRequested = false;
            const db = await openPageDB();
            await new Promise((res, rej) => {
                const tx = db.transaction('pages', 'readwrite');
                tx.objectStore('pages').clear();
                tx.oncomplete = () => res(true);
                tx.onerror = () => rej(tx.error);
            });
            if (BWDD_DEBUG) console.log('[bwdd] Page cache cleared');
            return true;
        } catch (e) { return false; }
    }
    const WORKER_BATCH_SIZE = 2;

    function workerBatchSize(type) {
        // JPEG is the default and benefits from two overlapping codec jobs.
        // Lossless WebP/PNG encoders have much higher peak memory/CPU cost, so
        // keep a conservative single-page queue for those formats.
        return type === 'image/jpeg' ? WORKER_BATCH_SIZE : 1;
    }

    function workerPoolSize() {
        let cores = 8;
        try { cores = navigator.hardwareConcurrency || 8; } catch (e) {}
        return Math.min(Math.max(4, cores), 16);
    }

    function makePool(size, workerSrc, onDone, jobTimeoutMs, requestedBatchSize, buildMessage) {
        const batchSize = Math.max(1, Math.min(4, requestedBatchSize || WORKER_BATCH_SIZE));
        const queue = [];
        const workers = [];
        const timers = new Map();
        const workerUrl = URL.createObjectURL(new Blob([workerSrc], { type: 'text/javascript' }));
        let nextBatchId = 1;
        let pumpScheduled = false;

        // The job envelope belongs to the site module: BookWalker ships its own
        // relPath/seeds/q shape, ebookjapan ships page geometry and session
        // material. A site that supplies no builder keeps the original shape.
        const messageFor = typeof buildMessage === 'function' ? buildMessage : function (job) {
            const message = {
                id: job.id, relPath: job.relPath, seeds: job.seeds,
                q: job.q, fmt: job.fmt, needCrc: !!job.needCrc, timeoutMs: jobTimeoutMs,
            };
            // The main-thread prefetcher already downloaded this page, so pass
            // the Blob (structured-cloneable, unlike an ArrayBuffer) instead of
            // re-fetching through the six-socket origin.
            if (job.blob) message.blob = job.blob;
            else {
                message.auth = job.auth;
                message.baseUrl = job.baseUrl;
            }
            return message;
        };
        function clearJobTimer(id) {
            const timer = timers.get(id);
            if (timer) clearTimeout(timer);
            timers.delete(id);
        }
        function replaceWorker(w) {
            const idx = workers.indexOf(w);
            if (idx !== -1) workers[idx] = spawn();
            try { w.terminate(); } catch (e) {}
        }
        function failWorker(w, error) {
            const ids = w.jobIds.slice();
            w.busy = false;
            w.batchId = null;
            w.hadTimeout = false;
            w.jobIds = [];
            for (const id of ids) {
                clearJobTimer(id);
                onDone({ id, error });
            }
            replaceWorker(w);
            pump();
        }
        function timeoutJob(w, id) {
            if (!w.jobIds.includes(id)) return;
            clearJobTimer(id);
            w.jobIds = w.jobIds.filter(jobId => jobId !== id);
            w.hadTimeout = true;
            onDone({ id, error: 'timeout' });
            if (w.jobIds.length === 0) releaseWorker(w);
        }
        function releaseWorker(w) {
            w.busy = false;
            w.batchId = null;
            const recycle = w.hadTimeout;
            w.hadTimeout = false;
            // A timed-out page may still own native codec work. Preserve every
            // sibling that did finish, but never reuse that worker.
            if (recycle) replaceWorker(w);
            pump();
        }
        function spawn() {
            const w = new Worker(workerUrl);
            w.busy = false;
            w.batchId = null;
            w.hadTimeout = false;
            w.jobIds = [];
            w.onmessage = (ev) => {
                const result = ev.data && ev.data.result ? ev.data.result : ev.data;
                if (!result || result.id == null || !w.jobIds.includes(result.id)) return;
                if (ev.data.batchId != null && ev.data.batchId !== w.batchId) return;
                if (!result.error && !(result.blob instanceof Blob)) {
                    clearJobTimer(result.id);
                    w.jobIds = w.jobIds.filter(id => id !== result.id);
                    onDone({ id: result.id, error: 'Worker returned no image Blob' });
                    if (w.jobIds.length === 0) releaseWorker(w);
                    return;
                }
                clearJobTimer(result.id);
                w.jobIds = w.jobIds.filter(id => id !== result.id);
                onDone(result);
                if (w.jobIds.length === 0) releaseWorker(w);
            };
            w.onerror = () => failWorker(w, 'worker crash');
            return w;
        }
        for (let i = 0; i < size; i++) workers.push(spawn());

        function pump() {
            let retry = false;
            for (const w of workers) {
                if (w.busy) continue;
                const jobs = [];
                while (jobs.length < batchSize && queue.length) jobs.push(queue.shift());
                if (!jobs.length) break;
                w.busy = true;
                w.jobIds = jobs.map(job => job.id);
                const batchId = nextBatchId++;
                w.batchId = batchId;
                w.hadTimeout = false;
                for (const job of jobs) {
                    timers.set(job.id, setTimeout(() => timeoutJob(w, job.id), jobTimeoutMs));
                }
                try {
                    w.postMessage({ batchId, jobs: jobs.map(messageFor) });
                } catch (e) {
                    for (const job of jobs) {
                        clearJobTimer(job.id);
                        onDone({ id: job.id, error: 'post failed' });
                    }
                    w.busy = false;
                    w.batchId = null;
                    w.hadTimeout = false;
                    w.jobIds = [];
                    retry = true;
                }
            }
            // A failed structured clone leaves this worker idle. Revisit the
            // queue once so one bad job cannot stall every page behind it.
            if (retry) schedulePump();
        }
        function schedulePump() {
            if (pumpScheduled) return;
            pumpScheduled = true;
            Promise.resolve().then(() => {
                pumpScheduled = false;
                pump();
            });
        }
        return {
            // Coalesce synchronous submissions: pumping on every submit would
            // defeat batching before the second page ever reached the queue.
            submit(job) { queue.push(job); schedulePump(); },
            terminate() {
                queue.length = 0;
                for (const w of workers) { try { w.terminate(); } catch (e) {} }
                for (const timer of timers.values()) clearTimeout(timer);
                timers.clear();
                try { URL.revokeObjectURL(workerUrl); } catch (e) {}
            },
        };
    }

    function detectWorkers() {
        try {
            if (typeof Worker === 'undefined' || typeof OffscreenCanvas === 'undefined') return false;
            // The worker source belongs to a site module, so a build without
            // one simply has no worker pool rather than a broken reference.
            if (typeof buildWorkerSource !== 'function') return false;
            const src = buildWorkerSource();
            const url = URL.createObjectURL(new Blob([src], { type: 'text/javascript' }));
            const w = new Worker(url);
            w.terminate();
            URL.revokeObjectURL(url);
            return true;
        } catch (e) { return false; }
    }

    async function fetchWithTimeout(url, opts, ms) {
        const ctrl = new AbortController();
        let timer = setTimeout(() => ctrl.abort(), ms);
        let cleared = false;
        const clear = () => {
            if (cleared) return;
            cleared = true;
            clearTimeout(timer);
            timer = null;
        };
        try {
            const res = await fetch(url, Object.assign({}, opts, { signal: ctrl.signal }));
            try { Object.defineProperty(res, '_bwddClearTimeout', { value: clear, configurable: true }); } catch (e) {}
            for (const name of ['arrayBuffer', 'blob', 'formData', 'json', 'text']) {
                if (typeof res[name] !== 'function') continue;
                const original = res[name].bind(res);
                try {
                    Object.defineProperty(res, name, {
                        configurable: true,
                        value: async (...args) => {
                            try { return await original(...args); }
                            finally { clear(); }
                        },
                    });
                } catch (e) {
                    clear();
                }
            }
            return res;
        } catch (e) {
            clear();
            throw e;
        }
    }

    async function releaseResponse(res) {
        try { if (res && res.body && res.body.cancel) await res.body.cancel(); } catch (e) {}
        try { if (res && res._bwddClearTimeout) res._bwddClearTimeout(); } catch (e) {}
    }

    // Chrome allows 6 concurrent HTTP/1.1 connections per origin (scheme + host
    // + PORT), and the CDN is a single HTTP/1.1 host, so the page alone is pinned
    // at 6. Extra lanes: `gm` (Tampermonkey's own pool) and `px:N` (a local helper
    // port; each is a separate origin and the script bounds the fan-out).
    const PROXY_HOST = 'http://127.0.0.1:';
    const PROXY_BASE_PORT = 7010;
    // Each localhost port is a separate HTTP/1.1 origin. Chromium's normal
    // group limit is 6 per origin; it is not a 300-socket global cap. Keep a
    // finite bridge fan-out so a misconfigured helper cannot create unbounded
    // work, while allowing a bridge that exposes more ports to use them.
    const PROXY_MAX_PORTS = 64;
    // A failing port is parked, not deleted: a wide burst can fail every port at
    // once, and deleting them collapses the run onto the 6-socket page lane.
    const PROXY_ERROR_PARK = 12;
    const PROXY_PARK_MAX = 5;
    const PROXY_PARK_MS = 4000;
    let gmUsable = (typeof GM_xmlhttpRequest === 'function');
    const proxyPorts = [];
    const proxyPortSources = new Map();
    const retiredProxyPorts = new Set();

    const laneStats = {};
    function addLane(name) {
        if (!laneStats[name]) {
            laneStats[name] = {
                inflight: 0, done: 0, bytes: 0, ms: 0, errors: 0,
                parkUntil: 0, parks: 0,
            };
        }
        return laneStats[name];
    }
    addLane('page');
    addLane('gm');

    // Chrome keys its socket pool by *site*, so a subdomain of a host we can
    // already reach buys nothing; "host." (trailing dot) is a distinct host and
    // gets its own pool. The signed policy covers a path wildcard, so the dot
    // cannot break the signature, but whether CloudFront serves it is not
    // knowable in advance, so the lane self-verifies on a real page and a
    // rejection costs one request.
    let dotLaneEnabled = false;
    function dottedUrl(url) {
        // Dot the HOSTNAME only: appending it to the authority would give
        // "host:8443." and corrupt the port. The rest of
        // the URL is left byte-identical so the signed query is untouched.
        //   https://a.example.com:8443/x -> https://a.example.com.:8443/x
        return url.replace(/^(https?:\/\/)([^/?#:]+)(:\d+)?/, (m, scheme, hostname, port) => {
            if (hostname.endsWith('.') || /^[\d.]+$/.test(hostname)) return m; // already dotted / an IP
            return scheme + hostname + '.' + (port || '');
        });
    }
    async function probeDotLane(probeUrl) {
        if (!probeUrl) return false;
        try {
            const res = await fetchWithTimeout(dottedUrl(probeUrl), { credentials: 'omit' }, 8000);
            if (res && res.ok) {
                dotLaneEnabled = true;
                addLane('dot');
                const dottedHost = (dottedUrl(probeUrl).match(/^https?:\/\/([^/?#]+)/) || [])[1] || '';
                if (BWDD_DEBUG) {
                    console.info('[bwdd] trailing-dot lane ENABLED: the CDN also serves ' +
                        dottedHost + ' as its own site (+6 sockets)');
                }
                return true;
            }
            if (BWDD_DEBUG) {
                console.info('[bwdd] trailing-dot lane off (probe returned HTTP ' +
                    (res && res.status) + ')');
            }
        } catch (e) {
            if (BWDD_DEBUG) console.info('[bwdd] trailing-dot lane off (' + safeLogText((e && e.message) || e) + ')');
        }
        return false;
    }

    // HTTP/2 edge-mirror lane (self-verifying, strictly opt-in). The CDN answers
    // "http/1.1 only" over ALPN, which is what makes the 6-socket cap bind; a host
    // speaking HTTP/2 multiplexes many streams over one connection (measured: 100
    // concurrent, ~8.9x the direct path). It is the only route past the cap with
    // nothing running locally, but it sends the signed URL through whoever runs
    // the mirror, so it stays opt-in. See bw-edge-mirror.js.
    let edgeUrl = '';
    let edgeToken = '';
    let edgeLaneEnabled = false;

    function loadEdgeConfig() {
        try {
            const stored = localStorage.getItem('bwddEdgeMirror');
            if (stored) edgeUrl = String(stored).replace(/\/+$/, '');
            const tok = localStorage.getItem('bwddEdgeToken');
            if (tok) edgeToken = String(tok);
        } catch (e) {}
        try {
            if (window.__bwddEdgeMirror) edgeUrl = String(window.__bwddEdgeMirror).replace(/\/+$/, '');
            if (window.__bwddEdgeToken) edgeToken = String(window.__bwddEdgeToken);
        } catch (e) {}
        return edgeUrl;
    }

    async function probeEdgeMirror() {
        if (edgeLaneEnabled) return true;
        if (!loadEdgeConfig()) return false;
        try {
            const r = await fetchWithTimeout(edgeUrl + '/__bwdd_health',
                { credentials: 'omit', cache: 'no-store' }, 5000);
            if (!r.ok) {
                console.info('[bwdd] edge mirror off: health returned HTTP ' + r.status);
                return false;
            }
            const j = await r.json();
            if (!j || !j.bwddEdgeMirror) {
                console.info('[bwdd] edge mirror off: that URL is not a bwdd worker');
                return false;
            }
            if (j.tokenRequired && !edgeToken) {
                console.warn('[bwdd] edge mirror needs a token; set localStorage.bwddEdgeToken');
                return false;
            }
            edgeLaneEnabled = true;
            addLane('edge');
            console.info('[bwdd] HTTP/2 edge mirror ENABLED at ' + edgeUrl +
                ': multiplexed streams instead of 6 sockets');
            return true;
        } catch (e) {
            console.info('[bwdd] edge mirror off (' + safeLogText((e && e.message) || e) + ')');
        }
        return false;
    }

    function edgeUrlFor(url) {
        // Same path and signed query, different front-end.
        return edgeUrl + url.replace(/^https?:\/\/[^/]+/, '');
    }

    function allLanes(onlineOnly) {
        const out = [{ name: 'page', kind: 'page' }];
        if (gmUsable) out.push({ name: 'gm', kind: 'gm' });
        if (dotLaneEnabled) out.push({ name: 'dot', kind: 'dot' });
        if (edgeLaneEnabled) out.push({ name: 'edge', kind: 'edge' });
        const now = Date.now();
        for (const p of proxyPorts) {
            if (onlineOnly && !proxyPortOnline(p)) continue;
            const st = laneStats['px:' + p];
            if (st && st.parkUntil > now) continue;
            out.push({ name: 'px:' + p, kind: 'proxy', port: p });
        }
        return out;
    }
    // Six everywhere except the edge mirror, which multiplexes many streams over
    // one HTTP/2 connection, so it should absorb proportionally more traffic.
    function laneCapacity(L) {
        return L && L.kind === 'edge' ? 100 : 6;
    }
    // Sizes the prefetch window: a small multiple of the real socket capacity.
    function fetchSocketBudget(onlineOnly) {
        let n = 0;
        for (const L of allLanes(onlineOnly)) n += laneCapacity(L);
        return n;
    }

    // NOTE: named gmBlobFetch, not gmFetch, the stats section further down
    // already declares a `gmFetch` in this same scope, and a duplicate function
    // declaration hoists with the *last* one winning for the whole scope.
    function gmBlobFetch(url, timeoutMs) {
        return new Promise((resolve, reject) => {
            let settled = false;
            const fail = (msg) => {
                if (settled) return;
                settled = true;
                const e = new Error(msg); e.status = 0; reject(e);
            };
            try {
                GM_xmlhttpRequest({
                    method: 'GET',
                    url,
                    timeout: timeoutMs || 45000,
                    responseType: 'blob',
                    onload: (r) => {
                        if (settled) return;
                        settled = true;
                        let body = r.response;
                        if (body instanceof ArrayBuffer) body = new Blob([body], { type: 'image/jpeg' });
                        if (!(body instanceof Blob)) { fail('GM_xhr: no blob body'); return; }
                        const ok = r.status >= 200 && r.status < 300;
                        resolve({ ok, status: r.status, blob: async () => body, _lane: 'gm' });
                    },
                    onerror: () => fail('GM_xhr: request failed'),
                    ontimeout: () => fail('GM_xhr: timeout'),
                    onabort: () => fail('GM_xhr: aborted'),
                });
            } catch (e) { fail('GM_xhr: ' + safeLogText((e && e.message) || e)); }
        });
    }

    // Which hosts the bridge's proxy ports will fetch: it rewrites the request
    // onto x-bwdd-upstream and refuses any host outside its own allowlist, so a
    // port is only usable for a CDN the bridge accepts ("*" = generic). A bridge
    // too old to advertise the list is assumed to serve only the BookWalker CDN,
    // which keeps an existing setup working without aiming a CMOA path at a host
    // that would answer from the wrong CDN.
    let proxyUpstreamPatterns = ['bw-bv-epubs.bookwalker.jp'];
    let proxyDefaultHost = 'bw-bv-epubs.bookwalker.jp';
    function setProxyUpstreams(list, defaultUpstream) {
        if (defaultUpstream) {
            const d = String(defaultUpstream).replace(/^https?:\/\//, '').replace(/\/.*$/, '').toLowerCase();
            if (d) proxyDefaultHost = d;
        }
        if (!Array.isArray(list) || !list.length) return false;
        const patterns = list
            .map(p => String(p || '').toLowerCase().trim())
            .filter(Boolean);
        if (!patterns.length) return false;
        proxyUpstreamPatterns = patterns;
        return true;
    }
    function proxyCanServe(host) {
        const h = String(host || '').toLowerCase();
        if (!h) return false;
        for (const pattern of proxyUpstreamPatterns) {
            if (pattern === '*') return true;
            if (pattern === h) return true;
            if (pattern.indexOf('*') !== -1) {
                const rx = new RegExp('^' + pattern.split('*')
                    .map(part => part.replace(/[.+?^${}()|[\]\\]/g, '\\$&'))
                    .join('[^.]*') + '$');
                if (rx.test(h)) return true;
            }
        }
        return false;
    }
    function hostOf(url) {
        const m = /^https?:\/\/([^/?#]+)/.exec(String(url || ''));
        return m ? m[1].replace(/:\d+$/, '').toLowerCase() : '';
    }

    function proxyPortOnline(port) {
        const sources = proxyPortSources.get(port);
        return !!(sources && (sources.has('bridge') || sources.has('helper')));
    }

    function activeProxyPortCount() {
        let n = 0;
        for (const sources of proxyPortSources.values()) {
            if (sources.has('bridge') || sources.has('helper')) n++;
        }
        return n;
    }

    function addProxyPorts(list, source) {
        const key = source || 'legacy';
        const advertised = new Set();
        for (const raw of (Array.isArray(list) ? list : [])) {
            const port = parseInt(raw, 10);
            if (port > 0 && port < 65536) advertised.add(port);
        }
        for (const [port, sources] of proxyPortSources) {
            if (!sources.has(key)) continue;
            if (advertised.has(port)) sources.add(key);
            else {
                sources.delete(key);
                if (!sources.size) proxyPortSources.delete(port);
            }
        }
        pruneProxyPorts();
        for (const port of advertised) {
            if (retiredProxyPorts.has(port)) continue;
            if (!proxyPorts.includes(port) && activeProxyPortCount() < PROXY_MAX_PORTS) {
                proxyPorts.push(port);
                addLane('px:' + port);
            }
            if (proxyPorts.includes(port)) {
                const sources = proxyPortSources.get(port) || new Set();
                sources.add(key);
                proxyPortSources.set(port, sources);
            }
        }
    }

    function pruneProxyPorts() {
        for (let i = proxyPorts.length - 1; i >= 0; i--) {
            const port = proxyPorts[i];
            if (!proxyPortOnline(port) || retiredProxyPorts.has(port)) {
                proxyPorts.splice(i, 1);
                delete laneStats['px:' + port];
            }
        }
    }

    function clearProxySource(source) {
        for (const [port, sources] of proxyPortSources) {
            sources.delete(source);
            if (!sources.size) proxyPortSources.delete(port);
        }
        pruneProxyPorts();
    }

    // mokuro-bridge doubles as an accelerator: it serves the CDN on extra
    // localhost ports (each its own 6-socket origin) advertised in /health, so a
    // user already running it for OCR gets those lanes with no setup.
    // Downloading never *depends* on it, no bridge simply means no lanes.
    async function probeBridgeFetchProxy() {
        clearProxySource('bridge');
        try {
            const r = await fetchWithTimeout(MOKURO_BRIDGE_URL + '/health',
                { cache: 'no-store' }, 2500);
            if (!r.ok) return;
            const j = await r.json();
            if (j && (j.fetchUpstreams || j.upstream)) {
                setProxyUpstreams(j.fetchUpstreams, j.upstream);
            }
            if (j && Array.isArray(j.fetchProxyPorts) && j.fetchProxyPorts.length) {
                addProxyPorts(j.fetchProxyPorts, 'bridge');
            }
        } catch (e) { /* bridge not running */ }
    }

    // Discover the optional local fetch proxy. If the helper is not running this
    // is one failed request to a closed local port and the run proceeds on the
    // page + gm lanes exactly as before. If it had to move off 7010 (port in use),
    // point the script at it with `window.__bwddProxyBasePort = 7100;`.
    async function probeFetchProxy() {
        return await discoverProxyPorts();
    }

    // Re-run discovery so the panel's pre-flight indicator lights up bridge ports
    // that started *after* the page loaded; source ownership and retirement decide
    // which lanes remain selectable.
    async function discoverProxyPorts() {
        clearProxySource('helper');
        let basePort = PROXY_BASE_PORT;
        try {
            if (typeof window !== 'undefined' && window.__bwddProxyBasePort) {
                basePort = parseInt(window.__bwddProxyBasePort, 10) || PROXY_BASE_PORT;
            }
        } catch (e) {}
        try {
            const r = await fetchWithTimeout(PROXY_HOST + basePort + '/__bwdd_health',
                { credentials: 'omit', cache: 'no-store' }, 800);
            if (r.ok) {
                const j = await r.json();
                if (j && j.bwddFetchProxy) {
                    if (Array.isArray(j.upstreams) && j.upstreams.length) setProxyUpstreams(j.upstreams);
                    addProxyPorts(
                        Array.isArray(j.portList) && j.portList.length
                            ? j.portList
                            : Array.from(
                                { length: Math.min(PROXY_MAX_PORTS, j.ports || 1) },
                                (_, i) => basePort + i),
                        'helper'
                    );
                }
            }
        } catch (e) { /* helper not running */ }
        await probeBridgeFetchProxy();
        return proxyPorts;
    }

    // Last known bridge reachability, mirrored out of buildUI's poll, for the
    // bridge/OCR status shown in the panel; the per-port source map decides which
    // discovered proxy lanes are usable now.
    let laneBridgeOnline = false;

    function capabilitySummary() {
        const lanes = allLanes(true);
        const ports = lanes.filter(l => l.kind === 'proxy').length;
        const sockets = fetchSocketBudget(true);
        const offlineSockets = 6 + (gmUsable ? 6 : 0) + (dotLaneEnabled ? 6 : 0) +
            (edgeLaneEnabled ? 100 : 0);
        return {
            ports,
            sockets,
            withoutBridge: offlineSockets,
            effectiveSockets: sockets,
            workers: workerPoolSize(),
            decodePages: workerPoolSize() * workerBatchSize(IMAGE_CODEC.type),
            laneCount: lanes.length,
            bridge: ports > 0,
            bridgeOnline: laneBridgeOnline,
        };
    }

    // Least-*utilised* lane wins (in-flight divided by capacity), so the 6-socket
    // lanes fill up while the edge mirror keeps absorbing work; the tie-break
    // rotates so even a low-concurrency run touches every lane.
    let laneRR = 0;
    // allowProxy=false keeps a request off the local fetch-proxy lanes: they are
    // not transparent forwarders, so a port advertised for one store's CDN would
    // answer every other store's path from the wrong host (a 404 at best). A
    // caller fetching a CDN the proxy was not configured for must opt out.
    function pickLane(allowProxy) {
        let lanes = allLanes(true);
        if (allowProxy === false) {
            lanes = lanes.filter(L => L.kind !== 'proxy');
            if (!lanes.length) lanes = [{ name: 'page', kind: 'page' }];
        }
        const n = lanes.length;
        let best = null, bestScore = Infinity;
        for (let i = 0; i < n; i++) {
            const L = lanes[(laneRR + i) % n];
            const score = laneStats[L.name].inflight / laneCapacity(L);
            if (score < bestScore) { bestScore = score; best = L; }
        }
        laneRR = (laneRR + 1) % Math.max(1, n);
        return best;
    }

    function proxyUrlFor(port, url) {
        // Same path + signed query, different origin.
        return PROXY_HOST + port + url.replace(/^https?:\/\/[^/]+/, '');
    }

    // A failing lane is parked (helper port) or retired rather than deleted
    // outright: a wide burst can fail every lane at once, and dropping them
    // collapses the run onto the page lane.
    function laneRetireLimit(lane) {
        if (lane.kind === 'gm') return 5;
        if (lane.kind === 'proxy') return PROXY_ERROR_PARK;
        return 8;   // edge, dot
    }

    function retireLane(lane, err) {
        const st = laneStats[lane.name];
        st.errors = 0;
        const why = safeLogText((err && err.message) || err || '');
        if (lane.kind === 'gm') {
            gmUsable = false;
            console.warn('[bwdd] GM transport disabled after repeated failures:', why);
        } else if (lane.kind === 'edge') {
            edgeLaneEnabled = false;
            console.warn('[bwdd] edge mirror retired: ' + why);
        } else if (lane.kind === 'dot') {
            dotLaneEnabled = false;
            console.warn('[bwdd] trailing-dot lane retired: ' + why);
        } else if (lane.kind === 'proxy') {
            st.parkUntil = Date.now() + PROXY_PARK_MS;
            if (++st.parks >= PROXY_PARK_MAX) {
                const ix = proxyPorts.indexOf(lane.port);
                if (ix !== -1) proxyPorts.splice(ix, 1);
                proxyPortSources.delete(lane.port);
                retiredProxyPorts.add(lane.port);
                console.warn('[bwdd] fetch proxy port ' + lane.port + ' retired after repeated parks');
            }
        }
    }

    async function laneAttempt(lane, url, timeoutMs) {
        const to = timeoutMs || 45000;
        if (lane.kind === 'gm') return await gmBlobFetch(url, to);
        if (lane.kind === 'edge') {
            const opts = { credentials: 'omit' };
            if (edgeToken) opts.headers = { 'x-bwdd-token': edgeToken };
            return await fetchWithTimeout(edgeUrlFor(url), opts, to);
        }
        if (lane.kind === 'dot') {
            return await fetchWithTimeout(dottedUrl(url), { credentials: 'omit' }, to);
        }
        if (lane.kind === 'proxy') {
            // The proxy carries only path + query, so it must be told which CDN
            // the bytes come from. The bridge rejects any host outside its
            // allowlist with a JSON 403, which laneFetch treats as a lane failure
            // rather than an answer from the CDN. A request for the CDN the
            // bridge already defaults to sends no header (so no CORS preflight);
            // only a different CDN names itself, which lets one bridge serve
            // several stores without a second instance.
            const opts = { credentials: 'omit' };
            const host = hostOf(url);
            if (host && host !== proxyDefaultHost) opts.headers = { 'x-bwdd-upstream': host };
            const res = await fetchWithTimeout(proxyUrlFor(lane.port, url), opts, to);
            if (res.status === 403) {
                const ct = res.headers && res.headers.get && res.headers.get('content-type');
                if (ct && ct.indexOf('application/json') !== -1) {
                    await releaseResponse(res);
                    throw new Error('fetch proxy refused host ' + host);
                }
            }
            if (res.status >= 500 && res.status <= 504) {
                await releaseResponse(res);
                throw new Error('fetch proxy transport error ' + res.status);
            }
            return res;
        }
        return await fetchWithTimeout(url, { credentials: 'omit' }, to);
    }

    function tagLane(res, name) {
        try { Object.defineProperty(res, '_lane', { value: name, configurable: true }); } catch (e) {}
        return res;
    }

    async function laneFetch(url, timeoutMs, opts) {
        const lane = pickLane(opts && opts.allowProxy);
        const st = laneStats[lane.name];
        const isPage = lane.kind === 'page';
        const countsNonOk = lane.kind === 'edge' || lane.kind === 'dot';
        st.inflight++;
        try {
            const res = await laneAttempt(lane, url, timeoutMs);
            if (res && res.status >= 500 && res.status <= 504 &&
                (lane.kind === 'edge' || lane.kind === 'dot' || lane.kind === 'gm')) {
                await releaseResponse(res);
                throw new Error('lane transport HTTP ' + res.status);
            }
            if (res && res.ok) st.errors = 0;
            else if (countsNonOk && ++st.errors >= laneRetireLimit(lane)) retireLane(lane, null);
            return tagLane(res, lane.name);
        } catch (e) {
            if (isPage) throw e;
            if (++st.errors >= laneRetireLimit(lane)) retireLane(lane, e);
        } finally {
            st.inflight--;
        }
        return await onPageLane(url, timeoutMs);
    }

    async function onPageLane(url, timeoutMs) {
        laneStats.page.inflight++;
        try {
            return tagLane(await fetchWithTimeout(url, { credentials: 'omit' }, timeoutMs || 45000), 'page');
        } finally {
            laneStats.page.inflight--;
        }
    }

    function recordLane(lane, ms, bytes) {
        const s = laneStats[lane] || laneStats.page;
        s.done++; s.ms += ms; s.bytes += (bytes || 0);
    }

    // Deliberately no per-lane pages/sec: a lane has no wall-clock window of its
    // own, so dividing pages by *summed request time* just reports 1/latency (a
    // real run printed 0.7/s per lane while the batch did 15 pages/s, ~21 requests
    // in flight). Share plus mean latency shows whether a lane is pulling weight.
    function laneSummary() {
        const out = {};
        let total = 0;
        for (const k of Object.keys(laneStats)) total += laneStats[k].done;
        for (const k of Object.keys(laneStats)) {
            const s = laneStats[k];
            if (!s.done) continue;
            out[k] = {
                pages: s.done,
                mb: +(s.bytes / 1048576).toFixed(2),
                avgMs: Math.round(s.ms / s.done),
                share: Math.round(100 * s.done / total) + '%',
            };
        }
        return out;
    }
    // Collapse concurrent requests for the same key onto one promise: retry rounds
    // and duplicated manifest entries legitimately ask for the same page twice
    // otherwise. The entry is dropped as soon as it settles, so a later retry
    // round can still re-fetch a page that genuinely failed.
    function dedupeInflight(map, key, start) {
        let p = map.get(key);
        if (!p) {
            p = start();
            map.set(key, p);
            const drop = () => { if (map.get(key) === p) map.delete(key); };
            p.then(drop, drop);
        }
        return p;
    }


    let rateLimitCooldownUntil = 0;
    let consecutiveBlocks = 0;
    function corsLikeError(e, status) {
        if (status === 429 || status === 503) return true;
        if (status === 403) return true;
        const msg = safeLogText((e && e.message) || e);
        return /Failed to fetch|NetworkError|load failed|ERR_|TypeError/i.test(msg);
    }
    async function sleepMs(ms) { await new Promise(r => setTimeout(r, ms)); }
    async function waitOutCooldown() {
        while (rateLimitCooldownUntil > Date.now()) {
            const wait = Math.min(rateLimitCooldownUntil - Date.now(), 10000);
            await sleepMs(wait);
        }
    }
    function tripBreaker() {
        const now = Date.now();
        if (rateLimitCooldownUntil > now) return breakerRemainingMs();
        consecutiveBlocks = Math.min(consecutiveBlocks + 1, 3);
        const cooldownMs = [8000, 16000, 30000][consecutiveBlocks - 1] || 30000;
        rateLimitCooldownUntil = now + cooldownMs;
        console.warn(`[bwdd] CDN protection active: cooling down for ${cooldownMs / 1000}s`);
        return cooldownMs;
    }
    function breakerOpen() { return rateLimitCooldownUntil > Date.now(); }
    function breakerRemainingMs() { return Math.max(0, rateLimitCooldownUntil - Date.now()); }

    let reqsSinceAuth = 0;
    const REQS_PER_POLICY_RENEW = 100;
    function authRequestBudgetExhausted() { return reqsSinceAuth >= REQS_PER_POLICY_RENEW; }
    function resetAuthBudget() { reqsSinceAuth = 0; }
    function effectiveBurst(base) {
        if (consecutiveBlocks === 0) return base;
        return Math.max(4, Math.floor(base / (consecutiveBlocks + 1)));
    }
    // =====================================================================
    // 7. Manga stats bridge (manga-kotoba + LearnNatively)
    // =====================================================================
    // Cross-origin fetch for the stats bridges. Neither site is usable with a
    // plain page fetch: learnnatively.com sends no CORS headers, and
    // manga-kotoba.com stopped reflecting the Origin (a bare fetch now fails with
    // "No 'Access-Control-Allow-Origin' header"). GM_xmlhttpRequest bypasses CORS
    // but only if the user accepted the permission; otherwise it falls back to a
    // public CORS proxy so the cards still work.
    const CORS_PROXIES = [
        'https://corsproxy.io/?url=',
        'https://api.allorigins.win/raw?url=',
    ];
    async function gmFetch(url, timeoutMs = 20000) {
        if (typeof GM_xmlhttpRequest === 'function') {
            try {
                return await new Promise((resolve, reject) => {
                    GM_xmlhttpRequest({
                        method: 'GET', url, timeout: timeoutMs,
                        onload: (r) => resolve({ status: r.status, text: r.responseText }),
                        onerror: (e) => reject(new Error('GM_xhr: ' + (e && e.error))),
                        ontimeout: () => reject(new Error('GM_xhr: Timeout')),
                    });
                });
            } catch (e) { /* fall through to proxies */ }
        }
        // Bounded like the other two paths: without a signal a host that accepts
        // the connection and never answers leaves the card pending forever.
        try {
            const ctrl = new AbortController();
            const timer = setTimeout(() => ctrl.abort(), timeoutMs);
            try {
                const r = await fetch(url, { credentials: 'omit', signal: ctrl.signal });
                return { status: r.status, text: await r.text() };
            } finally { clearTimeout(timer); }
        } catch (e) { /* fall through to proxies */ }
        for (const proxy of CORS_PROXIES) {
            try {
                const ctrl = new AbortController();
                const timer = setTimeout(() => ctrl.abort(), timeoutMs);
                let r;
                try {
                    r = await fetch(proxy + encodeURIComponent(url), { signal: ctrl.signal });
                    if (r.ok) return { status: r.status, text: await r.text() };
                } finally { clearTimeout(timer); }
            } catch (e) { /* try next proxy */ }
        }
        throw new Error('fetch failed: ' + url.slice(0, 80));
    }
    function extractVolumeNumber(title) {
        const t = String(title || '');
        const full = t.match(/([0-9０-９]+)/);
        if (full) {
            const digits = full[1].replace(/[０-９]/g, c => String.fromCharCode(c.charCodeAt(0) - 0xFEE0));
            return parseInt(digits, 10);
        }
        const kanji = t.match(/[一二三四五六七八九十百]+[巻話]/);
        if (kanji) return kanjiNum(kanji[0]);
        return NaN;
    }
    function kanjiNum(s) {
        const map = { '一': 1, '二': 2, '三': 3, '四': 4, '五': 5, '六': 6, '七': 7, '八': 8, '九': 9 };
        let n = 0, m = 0;
        for (const ch of s) {
            if (map[ch]) m = map[ch];
            else if (ch === '十') { n += (m || 1) * 10; m = 0; }
            else if (ch === '百') { n += (m || 1) * 100; m = 0; }
        }
        return n + m || 1;
    }
    function parseMangaKotobaTable(html) {
        const doc = new DOMParser().parseFromString(html, 'text/html');
        const rows = doc.querySelectorAll('#series-volume-stats tbody tr, table#series-volume-stats tr');
        const out = [];
        for (const tr of rows) {
            const a = tr.querySelector('a[href*="/volume/"]');
            if (!a) continue;
            const cells = tr.querySelectorAll('td');
            if (cells.length < 7) continue;
            const num = (s) => parseInt((s || '').replace(/,/g, '').trim(), 10);
            const pct = (s) => parseFloat((s || '').replace('%', '').trim());
            out.push({
                title: a.textContent.trim(),
                href: a.getAttribute('href'),
                total: num(cells[2] ? cells[2].textContent : ''),
                unique: num(cells[3] ? cells[3].textContent : ''),
                usedOnce: num(cells[4] ? cells[4].textContent : ''),
                usedOncePct: pct(cells[5] ? cells[5].textContent : ''),
                newWords: num(cells[6] ? cells[6].textContent : ''),
                density: parseFloat((cells[7] ? cells[7].textContent : '').trim()),
            });
        }
        return out;
    }
    async function lookupMangaKotoba(seriesTitle, volumeNum) {
        try {
            let links = null;
            let search = '';
            let usedTitle = seriesTitle;
            for (const cand of searchTitleCandidates(seriesTitle)) {
                const q = encodeURIComponent(cand);
                const text = (await gmFetch('https://manga-kotoba.com/search/series/?q=' + q)).text;
                const doc = new DOMParser().parseFromString(text, 'text/html');
                const l = [...doc.querySelectorAll('a[href*="/series/"]')];
                if (l.length) { links = l; search = text; usedTitle = cand; break; }
            }
            if (!links) return null;
            const norm = (x) => String(x || '').replace(/[\s　\u30fb・:：()（）]/g, '').toLowerCase();
            const target = norm(usedTitle);
            // manga-kotoba's /series/ results wrap an entire card in the anchor,
            // so anchor.textContent is far broader than the series name: scoring
            // the whole anchor made a spin-off listed before the base series win
            // merely by *containing* the name (幸色のワンルーム　外伝　正壊の名探偵
            // beat 幸色のワンルーム). Match the card's own Japanese title, and
            // break substring ties toward the closest (shortest) title.
            const titleOf = (a) => {
                const h = a.querySelector('.japanese-title, .series-title, h3');
                if (h) { const x = (h.textContent || '').trim(); if (x) return x; }
                const line = String(a.textContent || '').split(/\n/).map(x => x.trim()).find(Boolean);
                return line || '';
            };
            let best = null, bestScore = 0, bestExtra = Infinity;
            for (const a of links) {
                const t = norm(titleOf(a));
                if (!t || !target) continue;
                let score = 0;
                if (t === target) score = 1000;
                else if (t.indexOf(target) !== -1) score = target.length;
                else if (target.indexOf(t) !== -1) score = t.length;
                if (!score) continue;
                const extra = t.length - target.length;
                if (score > bestScore || (score === bestScore && extra < bestExtra)) {
                    bestScore = score; bestExtra = extra; best = a;
                }
            }
            if (!best) return null;
            const slug = best.getAttribute('href');
            const page = (await gmFetch('https://manga-kotoba.com' + slug)).text;
            const vols = parseMangaKotobaTable(page);
            if (!vols.length) return { seriesUrl: 'https://manga-kotoba.com' + slug, volume: null };
            let vol = null;
            for (const v of vols) {
                const n = extractVolumeNumber(v.title);
                if (n === volumeNum) { vol = v; break; }
            }
            if (!vol && vols.length === 1) vol = vols[0];
            return {
                seriesUrl: 'https://manga-kotoba.com' + slug,
                volume: vol ? { ...vol, url: 'https://manga-kotoba.com' + vol.href } : null,
                volumeCount: vols.length,
            };
        } catch (e) {
            if (BWDD_DEBUG) console.warn('[bwdd] Manga-kotoba lookup error:', safeLogText(e && e.message));
            return null;
        }
    }
    function searchTitleCandidates(raw) {
        const t = String(raw || '').trim();
        const out = [t];
        const seen = new Set([t]);
        const push = (s) => { s = String(s || '').trim(); if (s && !seen.has(s)) { seen.add(s); out.push(s); } };
        let s = t.replace(/【[^】]*】/g, ' ').replace(/[\s　]+/g, ' ').trim();
        push(s);
        let cur = s;
        for (let i = 0; i < 6; i++) {
            const before = cur;
            cur = cur
                .replace(/[\s　]*(文庫版|新装版|完全版|愛蔵版|廉価版|普及版|電子版|特装版|限定版|豪華版|分冊版|合本版|オンデマンド版|デジタル版|単行本版|ノベルズ版|ペーパーバック版)[\s　]*$/u, '')
                .replace(/[\s　]*[(（]*(文庫|新装|完全|愛蔵|廉価|普及)[)）]*[\s　]*$/u, '')
                .replace(/[\s　]*第?[一二三四五六七八九十百0-9０-９]*[巻話版編]?[\s　]*$/u, '')
                .trim();
            push(cur);
            if (cur === before) break;
        }
        push(s.replace(/[\s　]*版$/u, '').trim());
        return out.filter(Boolean);
    }
    async function lnSearchBook(candidates) {
        for (const cand of candidates) {
            const q = encodeURIComponent(cand);
            const r = await gmFetch('https://learnnatively.com/api/ninja/search/books/?language=jpn&q=' + q);
            if (r.status !== 200) continue;
            try {
                const d = JSON.parse(r.text);
                const items = (d.results || []).map(x => x.item).filter(i => i && i.series_id);
                if (items.length) return { cand, items };
            } catch (e) {}
        }
        return null;
    }

    async function lookupLearnNatively(seriesTitle, volumeNum) {
        try {
            const cands = searchTitleCandidates(seriesTitle);
            const found = await lnSearchBook(cands);
            if (!found) return null;
            const items = found.items;
            const first = items[0];
            const sid = first.series_id.replace(/-/g, '').slice(0, 10);
            let volUrl = null, volTitle = null, level = null;
            let matchedNo = null;      // which volume the resolved link actually is
            let fallbackNearest = null; // nearest available volume when exact not found
            try {
                const shtml = (await gmFetch('https://learnnatively.com/series/' + sid + '/')).text;
                const sdoc = new DOMParser().parseFromString(shtml, 'text/html');
                const links = [...sdoc.querySelectorAll('a.title[href*="/book/"]')];
                for (const a of links) {
                    const parent = a.closest('.item, .subitems > div, li, div') || a;
                    const notice = parent.querySelector('.item-type-notice');
                    const numMatch = (notice ? notice.textContent : '') + ' ' + (a.getAttribute('title') || a.textContent);
                    // Book #N (series page) is authoritative; fall back to title patterns
                    const m = numMatch.match(/Book\s*#?\s*(\d+)/i) || numMatch.match(/第?\s*(\d+)\s*巻/) ||
                             numMatch.match(/(\d+)\s*$/) || numMatch.match(/[（(]?([0-9０-９]{1,3})[）)]/);
                    const an = m ? parseInt(m[1].replace(/[０-９]/g, c => String.fromCharCode(c.charCodeAt(0) - 0xFEE0)), 10) : NaN;
                    if (an === volumeNum) {
                        volUrl = a.getAttribute('href');
                        volTitle = a.getAttribute('title') || a.textContent.trim();
                        matchedNo = an;
                        break;
                    }
                    if (!isNaN(an)) {
                        // nearest volume at or below the current one, as a fallback
                        if (!fallbackNearest || (an > fallbackNearest.an && an <= volumeNum) ||
                            (an <= volumeNum && (fallbackNearest.an > volumeNum || an > fallbackNearest.an))) {
                            fallbackNearest = { an, href: a.getAttribute('href'), title: a.getAttribute('title') || a.textContent.trim() };
                        }
                    }
                }
                if (!volUrl && links.length === 1) {
                    volUrl = links[0].getAttribute('href');
                    volTitle = links[0].getAttribute('title') || links[0].textContent.trim();
                    matchedNo = 1;
                }
                if (!volUrl && fallbackNearest) {
                    volUrl = fallbackNearest.href;
                    volTitle = fallbackNearest.title;
                    matchedNo = fallbackNearest.an;
                }
                const lvl = sdoc.querySelector('.key-tags .level, [class*="level"], [class*="Level"]');
                level = lvl ? lvl.textContent.trim() : null;
            } catch (e) {}
            const lvlFromRating = first.rating ? first.rating.lvl : null;
            const tmpFlag = first.rating ? !!(first.rating.temporary || first.rating.always_temporary) : false;
            const bookUrl = volUrl ? 'https://learnnatively.com' + volUrl : ('https://learnnatively.com' + first.url);
            // enriched from the search API response, no extra fetch needed
            const rd = first.review_data || {};
            const badges = [];
            if (first.wanikani) badges.push('WK');
            if (first.book_club) badges.push('BC');
            // reading/finished counts still come from the book page
            const meta = await fetchLnBookMeta(bookUrl);
            // Label the card with the *resolved* book (volTitle/matchedNo), not
            // the raw first search hit: the API ranks by popularity, so for
            // 幸色のワンルーム it returns "幸色のワンルーム 1" even when the
            // resolved book is volume 3, and the card read "… 1".
            return Object.assign({
                seriesUrl: 'https://learnnatively.com/series/' + sid + '/',
                bookUrl,
                title: volTitle || first.title,
                volume: matchedNo != null ? matchedNo
                    : (first.series_order != null ? first.series_order : null),
                level: lvlFromRating != null ? lvlFromRating : level,
                temporary: tmpFlag,
                avgRating: rd.avg_rating != null ? rd.avg_rating : null,
                ratings: rd.rating_count != null ? rd.rating_count : null,
                reviews: rd.review_count != null ? rd.review_count : null,
                badges,
                altTitles: first.alternative_titles || null,
            }, meta || {});
        } catch (e) {
            if (BWDD_DEBUG) console.warn('[bwdd] LearnNatively lookup error:', safeLogText(e && e.message));
            return null;
        }
    }
    async function fetchLnBookMeta(bookUrl) {
        try {
            const r = await gmFetch(bookUrl);
            if (r.status !== 200) return null;
            const doc = new DOMParser().parseFromString(r.text, 'text/html');
            const out = {};
            const rs = doc.querySelector('.ratings-summary');
            if (rs) {
                const m = rs.textContent.replace(/\s+/g, ' ').match(/([\d,]+)\s*ratings?,?\s*([\d,]+)\s*reviews?/i);
                if (m) {
                    out.ratings = parseInt(m[1].replace(/,/g, ''), 10) || 0;
                    out.reviews = parseInt(m[2].replace(/,/g, ''), 10) || 0;
                }
            }
            const inc = doc.querySelector('.count.in-progress');
            const fin = doc.querySelector('.count.finished');
            const num = (s) => { const v = s && s.textContent.replace(/[^\d]/g, ''); return v ? parseInt(v, 10) : 0; };
            out.reading = num(inc);
            out.finished = num(fin);
            const badges = [...doc.querySelectorAll('.key-tags .wanikani')].map(b => b.textContent.trim()).filter(Boolean);
            if (badges.length) out.badges = badges;
            const alt = doc.querySelector('.alternative-titles .alt-titles');
            if (alt) out.altTitles = alt.textContent.trim();
            return out;
        } catch (e) { return null; }
    }
    // Fire both catalog lookups at once and render each card as soon as its own
    // lookup resolves, so a slow or missing site only delays its own card. Both
    // lookups swallow their failures and resolve to null, which renders nothing.
    function fetchAndRenderStats(statsEl, seriesTitle, volumeNum) {
        if (!statsEl || !seriesTitle) return;
        lookupMangaKotoba(seriesTitle, volumeNum)
            .then(mk => { if (mk) upsertCard(statsEl, 'manga-kotoba', () => renderMangaKotobaCard(mk)); })
            .catch(e => { if (BWDD_DEBUG) console.warn('[bwdd] Manga-kotoba lookup error:', safeLogText(e && e.message)); });
        lookupLearnNatively(seriesTitle, volumeNum)
            .then(ln => { if (ln) upsertCard(statsEl, 'natively', () => renderNativelyCard(ln)); })
            .catch(e => { if (BWDD_DEBUG) console.warn('[bwdd] LearnNatively lookup error:', safeLogText(e && e.message)); });
    }

    // Card helpers (accessible: real links, labelled pills, dl rows)
    function el(tag, cls, text) {
        const n = document.createElement(tag);
        if (cls) n.className = cls;
        if (text != null) n.textContent = text;
        return n;
    }
    function cardLink(href, label, hint) {
        const a = el('a', 'bwdd-link', label + ' ↗');
        a.href = href;
        a.target = '_blank';
        a.rel = 'noopener noreferrer';
        a.setAttribute('aria-label', hint ? `${label}, ${hint} (new tab)` : `${label} (new tab)`);
        return a;
    }
    function statRow(grid, label, value, tip) {
        const dt = el('dt', null, label);
        if (tip) dt.title = tip;
        grid.append(dt, el('dd', null, value == null ? '—' : String(value)));
    }
    function upsertCard(container, key, buildFn) {
        if (!container) return null;
        const old = container.querySelector('.bwdd-card[data-card="' + key + '"]');
        if (old) old.remove();
        // buildFn may legitimately return null when there is nothing to show.
        const card = buildFn();
        if (!card) return null;
        card.dataset.card = key;
        const book = container.querySelector('.bwdd-card[data-card="book"]');
        if (key === 'book') {
            if (book) container.insertBefore(card, book);
            else if (container.firstChild) container.insertBefore(card, container.firstChild);
            else container.appendChild(card);
            return card;
        }
        const last = container.querySelector('.bwdd-card:last-child');
        if (last) last.after(card);
        else container.appendChild(card);
        return card;
    }
    function emptyCard(kicker) {
        const card = el('article', 'bwdd-card');
        card.appendChild(el('h3', null, kicker));
        return card;
    }
    // Single lookup: [pill bg, JLPT hint]. Darkened for ≥4.5:1 white-text contrast.
    function levelInfo(level) {
        const l = Number(level);
        if (isNaN(l)) return ['#5b21b6', ''];
        if (l <= 12) return ['#075985', 'N5'];
        if (l <= 19) return ['#9f1239', 'N4'];
        if (l <= 26) return ['#5b21b6', 'N3'];
        if (l <= 33) return ['#9a3412', 'N2'];
        if (l <= 40) return ['#166534', 'N1'];
        return ['#0e7490', 'N1+'];
    }
    function lightenHex(hex, amount) {
        const n = parseInt(hex.slice(1), 16);
        const mix = (c) => Math.round(c + (255 - c) * amount);
        const r = mix((n >> 16) & 255), g = mix((n >> 8) & 255), b = mix(n & 255);
        return '#' + ((1 << 24) | (r << 16) | (g << 8) | b).toString(16).slice(1);
    }
    function renderLevelPill(level, temporary) {
        const [bg, jlpt] = levelInfo(level);
        const b = el('span', 'bwdd-nlvl-pill', `Level ${level}${temporary ? '??' : ''}`);
        b.style.background = temporary ? lightenHex(bg, 0.55) : bg;
        b.style.color = temporary ? bg : '#fff';
        b.setAttribute('role', 'img');
        b.setAttribute('aria-label', temporary
            ? `Provisional Natively level ${level}${jlpt ? `, ${jlpt}` : ''}`
            : `Natively level ${level}${jlpt ? `, ${jlpt}` : ''}`);
        return b;
    }
    function renderNativelyCard(ln) {
        const card = emptyCard('LearnNatively');
        const meta = el('div', 'bwdd-ln-meta');
        if (ln.level != null) {
            const [, jlpt] = levelInfo(ln.level);
            meta.appendChild(renderLevelPill(ln.level, ln.temporary));
            if (jlpt) {
                const cap = el('span', 'bwdd-lvl-cap', jlpt);
                cap.setAttribute('aria-hidden', 'true');
                meta.appendChild(cap);
            }
        }
        for (const b of ln.badges || []) {
            const t = { WK: 'WaniKani vocab', BC: 'Book club' }[String(b).toUpperCase()] || '';
            const s = el('span', 'bwdd-lnbadge', String(b).toUpperCase());
            if (t) s.title = t;
            meta.appendChild(s);
        }
        const head = el('div', 'bwdd-ln-head');
        if (meta.childElementCount) head.appendChild(meta);
        if (ln.title) {
            // If the title already carries the volume number ("…」 1", "…（２）",
            // "…1巻"), don't repeat it as "· Vol. N".
            const titleHasVol = ln.volume != null && (() => {
                // normalize full-width digits so （２） and 2 both match
                const t = String(ln.title).replace(/[０-９]/g, c => String.fromCharCode(c.charCodeAt(0) - 0xFEE0));
                return new RegExp('(^|[^0-9])' + ln.volume + '([^0-9]|$)').test(t) ||
                       new RegExp('[（(]' + ln.volume + '[）)]').test(t);
            })();
            const sub = el('div', 'bwdd-card-sub bwdd-ln-title-row',
                ln.title + (ln.volume != null && !titleHasVol ? ` · Vol. ${ln.volume}` : ''));
            head.appendChild(sub);
        }
        if (head.childElementCount) card.appendChild(head);
        const bits = [];
        if (ln.avgRating != null) {
            // Label the count: ratings when present, otherwise reviews.
            if (ln.ratings != null) {
                bits.push(`★ ${Number(ln.avgRating).toFixed(1)} · ${Number(ln.ratings).toLocaleString()} ratings`);
            } else if (ln.reviews != null) {
                bits.push(`★ ${Number(ln.avgRating).toFixed(1)} · ${Number(ln.reviews).toLocaleString()} reviews`);
            } else {
                bits.push(`★ ${Number(ln.avgRating).toFixed(1)}`);
            }
        }
        if (ln.reading || ln.finished) bits.push(`${ln.reading || 0} reading · ${ln.finished || 0} finished`);
        if (bits.length) {
            const social = el('div', 'bwdd-ln-social');
            for (const bit of bits) social.appendChild(el('span', null, bit));
            card.appendChild(social);
        }
        const links = el('div', 'bwdd-card-links');
        links.appendChild(cardLink(ln.bookUrl, 'Book', ln.title));
        if (ln.seriesUrl) links.appendChild(cardLink(ln.seriesUrl, 'Series', ln.title));
        card.appendChild(links);
        return card;
    }
    function renderMangaKotobaCard(mk) {
        const card = emptyCard('Manga-Kotoba');
        const v = mk && mk.volume;
        if (!v) {
            if (mk && mk.seriesUrl) {
                card.appendChild(el('p', 'bwdd-none', 'Volume pending — series cataloged.'));
                card.appendChild(cardLink(mk.seriesUrl, 'Series', 'Manga-Kotoba'));
                return card;
            }
            return null;
        }
        if (v.title) card.appendChild(el('div', 'bwdd-card-sub bwdd-mk-title', v.title));
        const grid = el('dl', 'bwdd-grid');
        const pct = String(v.usedOncePct ?? '').replace('%', '');
        const num = (x) => x != null ? Number(x).toLocaleString() : '—';
        statRow(grid, 'Total words', num(v.total), 'All words in this volume, counting repeats');
        statRow(grid, 'Unique words', num(v.unique), 'Distinct words used in this volume');
        statRow(grid, 'Used once', v.usedOnce != null ? `${num(v.usedOnce)}${pct ? ` (${pct}%)` : ''}` : '—', 'Words that appear exactly once in the volume — new-vocabulary fodder');
        statRow(grid, 'Density', v.density, 'Lexical density — share of distinct words in the text');
        card.appendChild(grid);
        const url = v.url || (mk.seriesUrl ? mk.seriesUrl + '/' : null);
        if (url) card.appendChild(cardLink(url, 'Breakdown', v.title));
        return card;
    }
    function renderStatsCards(statsEl, stats) {
        if (!stats) return;
        if (stats.mangaKotoba) upsertCard(statsEl, 'manga-kotoba', () => renderMangaKotobaCard(stats.mangaKotoba));
        if (stats.learnNatively) upsertCard(statsEl, 'natively', () => renderNativelyCard(stats.learnNatively));
    }
    function renderBookCard(statsEl, metaObj) {
        if (!statsEl) return;
        upsertCard(statsEl, 'book', () => {
            const card = emptyCard('Book Details');
            card.setAttribute('role', 'region');
            card.setAttribute('aria-label', 'Current book metadata');

            const titleEl = document.createElement('div');
            titleEl.className = 'bwdd-book-title';
            titleEl.textContent = metaObj.title || 'BookWalker Volume';
            card.appendChild(titleEl);

            const grid = document.createElement('div');
            grid.className = 'bwdd-spec-badges';

            function badge(label, value, tip) {
                const b = document.createElement('div');
                b.className = 'bwdd-spec-badge';
                if (tip) b.title = tip;
                const l = document.createElement('span');
                l.className = 'bwdd-spec-lbl';
                l.textContent = label;
                const v = document.createElement('span');
                v.className = 'bwdd-spec-val';
                v.textContent = value;
                b.append(l, v);
                return b;
            }

            if (metaObj.pages) grid.appendChild(badge('Pages', metaObj.pages, 'Number of page images in this book'));
            if (metaObj.resolution) grid.appendChild(badge('Page Size', metaObj.resolution, 'Resolution of the page images (width × height)'));
            if (metaObj.type) grid.appendChild(badge('Edition', metaObj.type, 'Whether this is a purchased edition or a sample / trial volume'));

            card.appendChild(grid);
            return card;
        });
    }

    // =====================================================================
    // 8. Mokuro bridge client
    // =====================================================================
    const MOKURO_BRIDGE_URL = (() => {
        const defaultUrl = 'http://127.0.0.1:62642';
        try {
            const marker = window.__BWDD_CLI__;
            const configured = marker && marker.bridgeUrl;
            if (configured) {
                const parsed = new URL(String(configured));
                if (parsed.protocol === 'http:' || parsed.protocol === 'https:') {
                    return parsed.toString().replace(/\/+$/, '');
                }
            }
        } catch (_) { /* malformed marker: retain the local default */ }
        return defaultUrl;
    })();
    const MOKURO_BRIDGE_START_URL = 'bw-mokuro-bridge://start';
    // Shown (via the run's catch-all) when the bridge cannot be reached.
    const MOKURO_BRIDGE_OFFLINE_MSG =
        'The Mokuro Bridge app is not running.\n\n' +
        'Get and start mokuro-bridge (github.com/GolyBidoof/mokuro-bridge) — its ' +
        'README shows the start command for your OS (macOS/Linux: ./run.sh from ' +
        'its folder), then click “Save and run through Mokuro” again.';

    // Hysteresis so a single dropped /health probe (or a slow response during
    // a heavy upload) can't flip the UI to "offline" and hide the bars. The
    // dot/message only go grey after BRIDGE_FAIL_LIMIT consecutive failures.
    const BRIDGE_FAIL_LIMIT = 3;
    let bridgeConsecFail = 0;
    // Strictly "did the last probe actually answer". bridgeHealth() below is
    // deliberately sticky so the OCR button does not flap on one missed poll,
    // but the pre-flight socket readout must not promise ports that are not
    // reachable this instant, so it reads this instead.
    let bridgeReachableNow = false;
    // Misses are only forgiven once the bridge has actually answered at least
    // once. Without this a cold page load with no bridge advertises "online" for
    // the first BRIDGE_FAIL_LIMIT polls, contradicting the socket readout.
    let bridgeEverReachable = false;
    // One CSP-proof GET against the local bridge, shaped like a fetch Response
    // so every caller keeps its `r.ok` / `r.status` / `r.json()` / `r.text()`
    // code unchanged. ebookjapan serves `connect-src 'self' https: wss:` (no
    // plain http:/ws:), so a page fetch to http://127.0.0.1:62642 is refused
    // there while the same request is fine on BookWalker/CMOA. GM_xmlhttpRequest
    // is issued by the userscript manager and is exempt from the page CSP, so it
    // is tried first whenever the manager grants it, with the page fetch as the
    // fallback. GM hands back the whole body at once, so this helper covers the
    // read-only GET endpoints; mokuroBridgePost does the multipart writes.
    async function mokuroBridgeGet(url, timeoutMs = 5000) {
        if (typeof GM_xmlhttpRequest === 'function') {
            const gm = await new Promise((resolve, reject) => {
                GM_xmlhttpRequest({
                    method: 'GET', url, timeout: timeoutMs,
                    headers: { 'Cache-Control': 'no-cache' },
                    onload: (r) => resolve(r),
                    onerror: (e) => reject(new Error('GM_xhr: ' + (e && e.error))),
                    ontimeout: () => reject(new Error('GM_xhr: Timeout')),
                });
            });
            const status = Number(gm && gm.status) || 0;
            const body = gm && gm.responseText != null ? String(gm.responseText) : '';
            return {
                ok: status >= 200 && status < 300,
                status,
                json: async () => JSON.parse(body),
                text: async () => body,
            };
        }
        return await fetchWithTimeout(url, { cache: 'no-store' }, timeoutMs);
    }
    // POST twin of mokuroBridgeGet for the multipart write endpoints
    // (session/start, session/<id>/page, session/<id>/cover, finalize): same
    // contract, GM_xmlhttpRequest first for the same CSP reason, fetchWithTimeout
    // otherwise. The FormData goes over as `data` with no Content-Type set by
    // hand, so Tampermonkey encodes the multipart body and boundary itself.
    async function mokuroBridgePost(url, timeoutMs, formData) {
        if (typeof GM_xmlhttpRequest === 'function') {
            const gm = await new Promise((resolve, reject) => {
                GM_xmlhttpRequest({
                    method: 'POST', url, data: formData, timeout: timeoutMs,
                    onload: (r) => resolve(r),
                    onerror: (e) => reject(new Error('GM_xhr: ' + (e && e.error))),
                    ontimeout: () => reject(new Error('GM_xhr: Timeout')),
                });
            });
            const status = Number(gm && gm.status) || 0;
            const body = gm && gm.responseText != null ? String(gm.responseText) : '';
            return {
                ok: status >= 200 && status < 300,
                status,
                json: async () => JSON.parse(body),
                text: async () => body,
            };
        }
        return await fetchWithTimeout(url, { method: 'POST', body: formData }, timeoutMs);
    }
    async function bridgeHealth() {
        try {
            const r = await mokuroBridgeGet(MOKURO_BRIDGE_URL + '/health', 2000);
            const ok = r.ok;
            bridgeReachableNow = ok;
            if (ok) bridgeEverReachable = true;
            bridgeConsecFail = ok ? 0 : bridgeConsecFail + 1;
            return ok || (bridgeEverReachable && bridgeConsecFail < BRIDGE_FAIL_LIMIT);
        } catch (e) {
            bridgeReachableNow = false;
            bridgeConsecFail++;
            return bridgeEverReachable && bridgeConsecFail < BRIDGE_FAIL_LIMIT;
        }
    }
    // Cached /health payload (upload backends, output dir, version…).
    let bridgeInfo = null;
    async function refreshBridgeInfo() {
        try {
            const r = await mokuroBridgeGet(MOKURO_BRIDGE_URL + '/health', 3000);
            if (r.ok) { bridgeInfo = await r.json(); return bridgeInfo; }
        } catch (e) {}
        return null;
    }
    // --- Generic upload-method support (mokuro-bridge >= 0.3) ---
    // The bridge exposes GET /upload-methods listing every method plus the
    // default; we pick the first configured one (or 'local') and remember its
    // folder. Falls back to /health mega_configured on older bridges.
    let uploadMethods = null;
    async function fetchUploadMethods() {
        try {
            const r = await mokuroBridgeGet(MOKURO_BRIDGE_URL + '/upload-methods', 3000);
            if (r.ok) { uploadMethods = await r.json(); return uploadMethods; }
        } catch (e) {}
        return null;
    }
    // Resolve which upload method + destination folder to use:
    // { method, folder, label }. The bridge's sticky default is reported only
    // when it is actually usable: "local" is always configured, so picking the
    // first *configured* method would always say "saving locally", while an
    // unconfigured default (e.g. drive not set up) must not be advertised as
    // the destination.
    async function mokuroUploadPlan() {
        const methods = uploadMethods || await fetchUploadMethods();
        if (methods && Array.isArray(methods.methods)) {
            const list = methods.methods;
            const def = methods.upload_method_default || 'local';
            const byDefault = list.find(m => m.id === def);
            const usableDefault = byDefault && byDefault.configured ? byDefault : null;
            const firstConfigured = list.find(m => m.configured);
            const picked =
                usableDefault ||
                firstConfigured ||
                list.find(m => m.id === 'local') ||
                list[0];
            if (picked) return { method: picked.id, folder: picked.current_folder || null, label: picked.name || picked.id };
        }
        // older bridge: only /health
        const info = bridgeInfo || await refreshBridgeInfo();
        if (info && info.mega_configured) return { method: 'mega', folder: info.mega_library_root || null, label: 'MEGA' };
        return { method: 'local', folder: info && info.output_dir || null, label: 'Local' };
    }
    // Final decision for a run: the panel's pick wins, else the bridge default.
    async function resolveUploadChoice(ui) {
        const plan = await mokuroUploadPlan().catch(() => ({ method: null, folder: null, label: null }));
        let method = plan.method, folder = plan.folder;
        if (ui && ui.destSelect && ui.destSelect.value) {
            method = ui.destSelect.value;
            folder = null;
            if (method === 'local' && ui.localDirInput && ui.localDirInput.value.trim()) folder = ui.localDirInput.value.trim();
        }
        return { method, folder, label: plan.label || method, localDir: method === 'local' ? folder : null };
    }

    async function ensureBridgeRunning(timeoutMs = 15000) {
        if (await bridgeHealth()) return true;
        // The extension adapter owns bridge discovery and startup. Never click
        // the custom protocol from an automation page: that creates a browser
        // permission prompt and turns a local bridge outage into a surprising
        // UI side effect. The caller receives the same clear offline error.
        let bridgeManaged = false;
        try { bridgeManaged = !!(window.__BWDD_CLI__ && window.__BWDD_CLI__.bridgeManaged); } catch (e) {}
        if (!bridgeManaged) {
            try {
                const a = document.createElement('a');
                a.href = MOKURO_BRIDGE_START_URL;
                a.style.display = 'none';
                document.body.appendChild(a);
                a.click();
                a.remove();
            } catch (e) {}
        }
        const start = Date.now();
        while (Date.now() - start < timeoutMs) {
            await new Promise(r => setTimeout(r, 600));
            if (await bridgeHealth()) return true;
        }
        return false;
    }
    // Wait for the bridge to report idle (busy=false, which also covers
    // ocr_queue_depth > 0) before starting a capture, so a new run cannot
    // interleave with OCR/upload work already in flight.
    async function waitForBridgeIdle(timeoutMs = 30000) {
        const start = Date.now();
        while (Date.now() - start < timeoutMs) {
            try {
                const r = await mokuroBridgeGet(MOKURO_BRIDGE_URL + '/health', 3000);
                if (r.ok) {
                    const h = await r.json();
                    if (!h.busy) return true;
                }
            } catch (e) {}
            await new Promise(res => setTimeout(res, 1000));
        }
        return false;   // still busy after the timeout, caller decides
    }

    function bridgeSessionPath(sessionId, suffix) {
        const id = String(sessionId || '');
        if (!/^[A-Za-z0-9_-]{1,64}$/.test(id)) throw new Error('Invalid bridge session id');
        return MOKURO_BRIDGE_URL + '/session/' + encodeURIComponent(id) + suffix;
    }
    async function mokuroStartSession(title) {
        const fd = new FormData();
        fd.append('title', title || 'manga');
        const res = await mokuroBridgePost(MOKURO_BRIDGE_URL + '/session/start', 15000, fd);
        const d = await res.json().catch(() => ({}));
        if (!res.ok) throw new Error(d.detail || 'HTTP ' + res.status);
        return d;
    }
    async function mokuroStreamPage(sessionId, blob, filename, pageNum) {
        const fd = new FormData();
        fd.append('page', blob, filename);
        fd.append('filename', filename);
        fd.append('page_num', String(pageNum));
        const res = await mokuroBridgePost(bridgeSessionPath(sessionId, '/page'), 60000, fd);
        const d = await res.json().catch(() => ({}));
        if (!res.ok) throw new Error(d.detail || 'HTTP ' + res.status);
        return d;
    }
    // Early cover upload: push the first page to the destination as
    // <title>.webp immediately, before OCR finishes, so the user sees upload
    // activity at once. {method, localDir} must match the run's destination.
    async function mokuroUploadCover(sessionId, blob, opts = {}) {
        const fd = new FormData();
        fd.append('cover', blob, 'cover.jpg');
        if (opts.method) fd.append('upload_method', opts.method);
        if (opts.method === 'local' && opts.localDir) fd.append('local_dir', opts.localDir);
        const res = await mokuroBridgePost(bridgeSessionPath(sessionId, '/cover'), 120000, fd);
        const d = await res.json().catch(() => ({}));
        if (!res.ok) throw new Error((d && d.detail) || 'HTTP ' + res.status);
        return d;
    }
    async function mokuroStatus(sessionId) {
        try {
            const res = await mokuroBridgeGet(bridgeSessionPath(sessionId, '/status'), 5000);
            if (!res.ok) return null;
            return await res.json();
        } catch (e) { return null; }
    }
    // Frames of the bridge's finalize NDJSON, shared so the live streaming
    // reader and the buffered GM fallback emit exactly the same callbacks for
    // exactly the same frames.
    function makeNdjsonSink(onStage, onUpload) {
        // Collect per-file storage URLs the bridge reports (upload_file's third
        // value, and/or done.uploads[]). Deduped, exposed as
        //   uploadUrls: [{file, url}]   storedUrl: first http(s).
        const uploadUrls = [];
        let storedUrl = null;
        let finalResult = null;
        function rememberUrl(msg) {
            const seen = new Set();
            const add = (file, url) => {
                const u = typeof url === 'string' ? url.trim() : '';
                if (!u) return;
                const f = typeof file === 'string' ? file : '';
                const key = f + '\u0000' + u;
                if (seen.has(key)) return;
                seen.add(key);
                if (uploadUrls.some(e => e.file === f && e.url === u)) return;
                uploadUrls.push({ file: f, url: u });
                // Prefer the .cbz (the volume archive itself) for the "Open
                // stored file" action; the cover .webp uploads first, so
                // without this preference the button would point at an image.
                if (/^https?:\/\//i.test(u)) {
                    if (!storedUrl || /\.cbz$/i.test(f)) storedUrl = u;
                }
            };
            if (typeof msg.url === 'string' && msg.url) add(msg.file, msg.url);
            const up = msg.upload || {};
            if (typeof up.url === 'string' && up.url) add(up.file || msg.file, up.url);
            if (Array.isArray(msg.uploads)) {
                for (const u of msg.uploads) add(u && u.file, u && u.url);
            }
        }
        function processLine(line) {
            if (!line.trim()) return;
            let msg; try { msg = JSON.parse(line); } catch (e) { return; }
            if (onStage) onStage(msg.stage, msg);
            rememberUrl(msg);
            if ((msg.stage === 'upload_progress' || msg.stage === 'upload') && onUpload) {
                const up = msg.upload || {};
                const hasPayload = !!(up.file || msg.file || up.bytes || msg.bytes != null ||
                    up.current_bytes != null || msg.current_bytes != null ||
                    up.total_bytes != null || msg.total_bytes != null);
                if (hasPayload) {
                    onUpload({
                        file: up.file || msg.file || '',
                        percent: msg.percent != null ? msg.percent : (up.percent != null ? up.percent : null),
                        speed: msg.speed_human || up.speed_human || null,
                        currentBytes: msg.current_bytes != null ? msg.current_bytes :
                            (up.current_bytes != null ? up.current_bytes :
                                (up.bytes != null ? up.bytes : (msg.bytes != null ? msg.bytes : 0))),
                        totalBytes: msg.total_bytes != null ? msg.total_bytes :
                            (up.total_bytes != null ? up.total_bytes : 0),
                        method: msg.method || up.method || null,
                        remotePath: msg.remote_path || msg.mega_path || up.remote_path || up.mega_path || null,
                    });
                }
            }
            if (msg.stage === 'done') finalResult = msg;
            if (msg.stage === 'error') throw new Error(msg.message || 'Mokuro bridge pipeline error');
        }
        return {
            processLine,
            // Terminal bookkeeping every caller has always relied on.
            finish() {
                if (!finalResult) throw new Error('Mokuro bridge closed stream without completing.');
                if (uploadUrls.length) finalResult.uploadUrls = uploadUrls;
                if (storedUrl) finalResult.storedUrl = storedUrl;
                return finalResult;
            },
        };
    }
    // Reads the bridge's finalize NDJSON stream (page fetch; has res.body).
    //   onStage(stage, msg)  , every frame
    //   onUpload(ev), live upload progress {file, percent, speed, currentBytes,
    //     totalBytes, method, remotePath}. The bridge streams one file at a time
    //     with that file's own bytes, so the caller must accumulate across
    //     files: use makeUploadBarUpdater() below.
    async function readNdjsonStream(res, onStage, onUpload) {
        if (!res.body) throw new Error('No streaming response body from bridge');
        const reader = res.body.getReader();
        const decoder = new TextDecoder();
        const sink = makeNdjsonSink(onStage, onUpload);
        let buffer = '';
        // Force-flush a partially-buffered line if nothing arrives for a while:
        // a slow upload's trailing NDJSON line (no newline yet) would otherwise
        // sit in `buffer`, making the bar look stuck.
        let lastLineAt = Date.now();
        const flushTimer = setInterval(() => {
            if (!buffer.trim() || Date.now() - lastLineAt < 4000) return;
            const lines = buffer.split('\n');
            buffer = lines.pop() || '';
            for (const line of lines) { sink.processLine(line); }
            lastLineAt = Date.now();
        }, 2000);
        try {
            while (true) {
                const { done, value } = await reader.read();
                if (done) break;
                buffer += decoder.decode(value, { stream: true });
                lastLineAt = Date.now();
                const lines = buffer.split('\n');
                buffer = lines.pop() || '';
                for (const line of lines) { sink.processLine(line); }
            }
            // The tail goes through the same sink as every split line, so a
            // trailing frame without its newline still reaches onUpload.
            if (buffer.trim()) { sink.processLine(buffer); }
            return sink.finish();
        } finally {
            // An error frame or a reader failure must not leave the flush
            // interval (or the stream reader) alive in a Puppeteer page.
            clearInterval(flushTimer);
            try { if (reader.cancel) await reader.cancel(); } catch (e) {}
        }
    }
    // Buffered twin of readNdjsonStream for the GM path, where the whole
    // responseText arrives at once: every line goes through the same sink, so
    // onStage/onUpload see the same frames, just in one burst.
    function readNdjsonText(text, onStage, onUpload) {
        const sink = makeNdjsonSink(onStage, onUpload);
        const lines = String(text == null ? '' : text).split('\n');
        for (const line of lines) { sink.processLine(line); }
        return sink.finish();
    }
    // Multi-file upload progress for the Store/Upload bar. Tracks a list of
    // files in upload order (seeded up front from the bridge's "upload" frame
    // `files:` list, then fed live per-file progress). The label reads
    //   "1/3 · 62% · 65.0 MB / 104.8 MB · 5.1 MiB/s"
    // i.e. file k of N · overall % · bytes · speed, no file name clutter. The
    // fill is the byte-weighted overall %, monotonic because every file's total
    // is known before it uploads; the k/N and size totals are kept after
    // completion rather than blanking the bar.
    function makeUploadBarUpdater(bar) {
        const order = [];              // file names in first-seen (upload) order
        const byName = new Map();      // name -> {cur, tot}
        const rec = (name) => {
            let r = byName.get(name);
            if (!r) { r = { cur: 0, tot: 0 }; byName.set(name, r); order.push(name); }
            return r;
        };
        let seeded = false;            // full plan announced by the bridge
        let done = 0;                  // files fully uploaded (tot>0 && cur>=tot)
        const feed = function onUploadFrame(ev) {
            if (!bar) return;
            bar.wrap.style.display = 'flex';
            const name = ev.file || '';
            if (name) {
                const r = rec(name);
                if (ev.totalBytes > 0) r.tot = Math.max(r.tot, ev.totalBytes);
                if (ev.currentBytes > 0) r.cur = Math.max(r.cur, ev.currentBytes);
            }
            let sumCur = 0, sumTot = 0;
            done = 0;
            for (const n of order) {
                const r = byName.get(n);
                sumCur += r.cur; sumTot += r.tot;
                if (r.tot > 0 && r.cur >= r.tot) done++;
            }
            let overall;
            if (sumTot > 0) overall = Math.min(100, (sumCur / sumTot) * 100);
            else if (ev.percent != null) overall = ev.percent;
            else overall = 0;
            let parts = [];
            if (seeded && order.length > 0) {
                // Always show k/N against the full plan: k = files fully done,
                // never a premature "1/3" just because one file was announced.
                parts.push(Math.min(done, order.length) + '/' + order.length);
            }
            parts.push(overall.toFixed(0) + '%');
            if (sumTot > 0) parts.push(fmtBytes(sumCur) + ' / ' + fmtBytes(sumTot));
            else if (ev.percent != null && ev.totalBytes > 0) parts.push(fmtBytes(ev.currentBytes || 0) + ' / ' + fmtBytes(ev.totalBytes));
            if (ev.speed && overall < 100) parts.push(ev.speed);
            setBar(bar, overall, parts.join(' · '));
        };
        // Pre-register the whole upload plan from the initial "upload" frame
        // ({file, total_bytes}[]): a full denominator up front keeps the overall
        // % honest and makes k/N always count against N.
        feed.seed = function seed(list) {
            if (!Array.isArray(list)) return;
            for (const it of list) {
                if (it && typeof it.file === 'string' && it.file) {
                    const r = rec(it.file);
                    if (it.total_bytes > 0) r.tot = Math.max(r.tot, it.total_bytes);
                }
            }
            if (list.length) seeded = true;
        };
        // True once any file has been registered (used to avoid clobbering
        // early-cover progress when the finalize phase reuses this feed).
        feed.hasAny = function hasAny() { return order.length > 0; };
        // Summary accessors: keep the final k/N and total size readable.
        feed.summary = function summary() {
            let sumCur = 0, sumTot = 0, d = 0;
            for (const n of order) {
                const r = byName.get(n);
                sumCur += r.cur; sumTot += r.tot;
                if (r.tot > 0 && r.cur >= r.tot) d++;
            }
            return { done: d, total: order.length, sumCur, sumTot };
        };
        return feed;
    }
    // Ask the bridge to finalize + store a volume.
    //   opts.method   , upload_method id ('local' | 'mega' | 'drive' | 'onedrive' | 'webdav');
    //                   null/omitted → let the bridge decide (env default).
    //   opts.localDir , when method is 'local', write output to this folder.
    //   opts.forceMega, legacy fallback: when the bridge rejects upload_method,
    //                   retry once with upload_to_mega=true (old bridges).
    // Protocol: github.com/GolyBidoof/mokuro-bridge.
    async function mokuroFinalize(sessionId, opts = {}, onStage, onUpload) {
        const method = opts.method || null;
        const fd = new FormData();
        if (method) {
            fd.append('upload_method', method);
            if (method === 'local' && opts.localDir) fd.append('local_dir', opts.localDir);
        } else if (opts.forceMega) {
            fd.append('upload_to_mega', 'true');
        }
        fd.append('delete_after_upload', 'true');
        const url = bridgeSessionPath(sessionId, '/finalize');
        let res = await mokuroBridgePost(url, 3600000, fd);
        // Legacy fallback: if the new bridge rejects an unknown upload_method
        // (error frame), retry once with the old upload_to_mega flag.
        if (method && !res.ok) {
            const fd2 = new FormData();
            fd2.append('upload_to_mega', method === 'local' ? 'false' : 'true');
            fd2.append('delete_after_upload', 'true');
            res = await mokuroBridgePost(url, 3600000, fd2);
        }
        // The page fetch has a real ReadableStream body, so BookWalker/CMOA keep
        // the live streaming reader; the GM response has none, so its whole NDJSON
        // body is parsed in one pass through the same sink.
        if (res.body && typeof res.body.getReader === 'function') {
            return readNdjsonStream(res, onStage, onUpload);
        }
        return readNdjsonText(await res.text(), onStage, onUpload);
    }
    // Where the post-OCR "Open Reader Mokuro" button points: the reader URL the
    // bridge reported when its done frame carries one, otherwise the reader home.
    function readerJumpUrl(result) {
        const u = result && result.reader_url;
        if (typeof u === 'string' && /^https?:\/\//i.test(u.trim())) return u.trim();
        return 'https://reader.mokuro.app/';
    }

    // =====================================================================
    // 10. "all-in-one downloader" pointer (single-store builds only)
    // =====================================================================
    // Whoever runs this build already chose one store and is the person most
    // likely to want the other two, so a single-store artifact puts a small
    // link in the panel header; the combined build, "Omnimanga Native
    // Downloader", omits this module entirely (it would point at itself). The
    // artifact file name also lives in src/targets.json ("both"), and
    // tests/test_artifacts.js fails if the two ever disagree, so renaming the
    // combined script cannot silently break this.
    const BWDD_UNIFIED_OUT = 'omnimanga-native-downloader.user.js';
    // The GreasyFork install page rather than the release asset: it shows the
    // version and the install button, and it is where the script is reviewed.
    const BWDD_UNIFIED_URL = 'https://greasyfork.org/en/scripts/597313-omnimanga-native-downloader';

    // Styling travels with the feature: a build without this module ships none.
    const UNIFIED_CSS = `
.bwdd-unified {
  display: inline-flex; align-items: center;
  flex-shrink: 0; white-space: nowrap;
  height: 17px; padding: 0 6px;
  border: 1px solid var(--bwdd-border); border-radius: 999px;
  font-size: 10px; font-weight: 600; line-height: 1;
  color: var(--bwdd-text-muted); text-decoration: none;
}
.bwdd-unified:hover { color: var(--bwdd-link); border-color: var(--bwdd-link); background: var(--bwdd-link-hover-bg); text-decoration: none; }
.bwdd-unified:focus-visible { outline: 2px solid var(--bwdd-link); outline-offset: 1px; }
`;
    let unifiedStylesMounted = false;
    function mountUnifiedStyles() {
        if (unifiedStylesMounted || typeof document === 'undefined') return;
        unifiedStylesMounted = true;
        try {
            const style = document.createElement('style');
            style.textContent = UNIFIED_CSS;
            (document.head || document.documentElement).appendChild(style);
        } catch (e) {}
    }

    // Returns the header link, or null when there is nothing to point at.
    function unifiedDownloaderLink() {
        mountUnifiedStyles();
        // 115px at 10px, which is the most the header row can take before the
        // version line starts to ellipsis; see the header budget in the tests.
        const a = el('a', 'bwdd-unified', 'all-in-one downloader');
        a.href = BWDD_UNIFIED_URL;
        a.target = '_blank';
        a.rel = 'noopener noreferrer';
        const tip = 'This build handles one store. One all-in-one downloader covers BookWalker, '
            + 'CMOA and ebookjapan in a single script (' + BWDD_UNIFIED_OUT + ') - get it here: '
            + BWDD_UNIFIED_URL;
        a.title = tip;
        a.setAttribute('aria-label', tip);
        return a;
    }
    // =====================================================================
    // 11. Naming, messages and ZIP base name
    // =====================================================================
    function cleanTitle(t) {
        if (!t) return '';
        let s = String(t).replace(/^【[^】]*】\s*/g, '').trim();
        s = s.replace(/[\\/:*?"<>|\x00-\x1f]/g, '').trim();
        return s;
    }
    function splitSeriesVolume(t) {
        let s = String(t || '').trim();
        s = s.replace(/【[^】]*】/g, '').trim();
        let volNum = null;
        let m = s.match(/(.*?)第?\s*([0-9０-９]{1,3}|[一二三四五六七八九十百]+)\s*[巻話](.*)$/);
        if (m && m[1].trim()) {
            const d = m[2].replace(/[０-９]/g, c => String.fromCharCode(c.charCodeAt(0) - 0xFEE0));
            volNum = /[0-9]/.test(d) ? parseInt(d, 10) : kanjiNum(d);
            s = (m[1] + ' ' + m[3]).trim();
        } else {
            m = s.match(/^(.*?)[\s　]*[：（:　]?[\s　]*[（(]?([0-9０-９]{1,3})[）)]?\s*$/);
            if (m && m[1].trim()) {
                const d = m[2].replace(/[０-９]/g, c => String.fromCharCode(c.charCodeAt(0) - 0xFEE0));
                volNum = parseInt(d, 10);
                s = m[1].trim();
            }
        }
        let series = s.replace(/[：:]\s*$/, '').trim();
        series = series.replace(/[\\/:*?"<>|\x00-\x1f]/g, '').trim();
        const volumeTitle = (series + ' ' + (volNum != null ? volNum : '')).trim();
        return { series, volNum, volumeTitle };
    }
    // ── Cross-platform (Windows / Linux / macOS) output naming ────────────
    // Everything the user saves to disk must also be legal on Windows, the
    // worst case. cleanTitle() above already drops the characters Windows
    // forbids in file names (\/:*?"<>| plus C0 controls); fsSafePath() covers
    // the rules that only bite there: trailing dots/spaces (NTFS strips them
    // silently, so a name that is only dots fails), reserved device names
    // (CON, PRN, NUL, COM1–9, LPT1–9), and a length cap of 190 code points so
    // the whole extraction path stays inside the legacy 260-char limit.
    // Linux/macOS tolerate all of this output unchanged.
    const BWDD_RESERVED_DEVICE = /^(?:con|prn|aux|nul|com[1-9]|lpt[1-9]|conin\$|conout\$)(?:\..*)?$/i;
    function fsSafePath(name) {
        let s = cleanTitle(name);
        if (!s) return '';
        // Strip trailing ASCII dots/spaces (Windows drops them on create).
        s = s.replace(/[. ]+$/, '').trim();
        if (!s || s === '.' || s === '..') return '';
        if (BWDD_RESERVED_DEVICE.test(s)) s = '_' + s;   // CON → _CON
        const cps = Array.from(s);
        if (cps.length > 190) s = cps.slice(0, 190).join('').replace(/[. ]+$/, '');
        return s;
    }
    // Default archive/output name for the current book: the volume's own
    // displayed title (series + volume kept in the store's own format, e.g.
    // "…1巻", "（１）"), with store labels in 【…】 removed wherever they sit.
    // cleanTitle() only strips a *leading* 【…】 group, so a mid/suffix label
    // like "…1巻【無料お試し版】" would leak, and splitSeriesVolume() normalizes
    // digits ("1巻"→"1") for the stat lookups, losing the store's format.
    function archiveDefaultName(rawTitle) {
        let s = String(rawTitle || '').trim();
        s = s.replace(/【[^】]*】/g, ' ');       // drop 【…】 groups, keep word separation
        s = s.replace(/[ \t　]+/g, ' ').trim();  // tidy the whitespace the removal leaves behind
        return fsSafePath(s);
    }
    // ZIPs are flat; the ZIP writer sorts pages by the number in each filename.
    // The series→volume nesting the bridge builds
    // for OCR/upload runs happens bridge-side from the session title.
    function zipBaseName(sv, fallbackTitle) {
        return fsSafePath(sv && sv.series) || fsSafePath(fallbackTitle) || 'book';
    }
    function fmtBytes(n) {
        if (n < 1024) return n + ' B';
        if (n < 1048576) return (n / 1024).toFixed(1) + ' KB';
        return (n / 1048576).toFixed(1) + ' MB';
    }
    // Outcome messages shared by the trial and full download/OCR pipelines,
    // so the two code paths can never drift apart in wording again.
    function msgZipSaved(n, size, secs) {
        return 'ZIP saved: ' + n + ' pages (' + size + ') in ' + secs + 's.';
    }
    function msgZipPartial(ok, total) {
        const missing = total - ok;
        return 'Saved ' + ok + ' of ' + total + ' pages — ' + missing +
            ' could not be fetched. Flip one page in the reader to renew credentials, then click Save as ZIP again — the missing pages resume automatically.';
    }
    function msgAllFailedZip() {
        return 'Every page failed to download — the session auth may have expired. Flip one page in the reader, then click Save as ZIP again.';
    }
    function msgOcrPartial(missing, total) {
        return missing + ' of ' + total + ' pages could not be fetched, so the volume may be incomplete. Flip one page in the reader, then run “Save and run through Mokuro” again.';
    }
    function msgStoredLocal(p) { return 'Stored locally to: ' + p; }
    function msgUploadedTo(label, p) { return 'Uploaded to ' + label + ' → ' + p; }

    // Best filesystem/destination path the bridge reported for a finished
    // volume (output_dir for local forks, staging/remote_path otherwise).
    function storedPathOf(result) {
        return (result && (result.output_dir || result.staging || result.remote_path)) || null;
    }
    // Short user-facing label for an upload-method id ('mega' → 'MEGA'…).
    function methodShortLabel(method) {
        const t = { mega: 'MEGA', drive: 'Google Drive', onedrive: 'OneDrive', webdav: 'WebDAV', local: 'Local' };
        return (t && t[method]) || method || '';
    }
    // The WebDAV base URL as reported by the bridge (/upload-methods extras or
    // /health upload_methods), used to rebuild direct file URLs, since WebDAV
    // has no share-link concept to attach to upload frames.
    function webdavBaseUrl() {
        const lists = [];
        if (uploadMethods && Array.isArray(uploadMethods.methods)) lists.push(uploadMethods.methods);
        if (bridgeInfo && Array.isArray(bridgeInfo.upload_methods)) lists.push(bridgeInfo.upload_methods);
        for (const list of lists) {
            const w = list.find(m => m && m.id === 'webdav');
            const b = w && w.extra && w.extra.base_url;
            if (typeof b === 'string' && /^https?:\/\//i.test(b.trim())) return b.trim().replace(/\/+$/, '');
        }
        return '';
    }
    // Best openable per-file target for a finished OCR run: the http(s) links the
    // bridge attached (uploadUrls / uploads[].url), else a rebuilt direct WebDAV
    // URL (base + remote_path/<volume>.cbz). .cbz is preferred over .mokuro /
    // .webp. Returns {file, url} or null.
    function storedOpenTarget(result) {
        if (!result) return null;
        const cands = [];
        const seen = new Set();
        const add = (file, url) => {
            const u = typeof url === 'string' ? url.trim() : '';
            if (!/^https?:\/\//i.test(u) || seen.has(u)) return;
            seen.add(u);
            cands.push({ file: file || '', url: u });
        };
        for (const u of (result.uploadUrls || [])) add(u && u.file, u && u.url);
        if (Array.isArray(result.uploads)) for (const u of result.uploads) add(u && u.file, u && u.url);
        if (result.storedUrl) add('', result.storedUrl);
        if (cands.length) {
            const rank = (f) => {
                const e = String(f || '').toLowerCase();
                return e.endsWith('.cbz') ? 0 : e.endsWith('.mokuro') ? 1 : e.endsWith('.webp') ? 2 : 3;
            };
            cands.sort((a, b) => (rank(a.file) - rank(b.file)) || (a.file < b.file ? -1 : 1));
            return cands[0];
        }
        if (result.method === 'webdav') {
            const base = webdavBaseUrl();
            const folder = result.remote_path || (result.series ? 'mokuro-reader/' + result.series : '');
            const vol = String(result.title || '');
            if (base && folder && vol) {
                const enc = (s) => encodeURIComponent(s).replace(/%2F/gi, '/');
                const url = base + '/' + folder.split('/').map(enc).join('/') + '/' + enc(vol + '.cbz');
                return { file: vol + '.cbz', url };
            }
        }
        return null;
    }
    let __crcTable = null;
    function crc32Bytes(buf) {
        if (!__crcTable) {
            __crcTable = new Int32Array(256);
            for (let n = 0; n < 256; n++) {
                let c = n;
                for (let k = 0; k < 8; k++) c = (c & 1) ? (0xEDB88320 ^ (c >>> 1)) : (c >>> 1);
                __crcTable[n] = c;
            }
        }
        const u = buf instanceof Uint8Array ? buf : new Uint8Array(buf);
        let c = -1;
        for (let i = 0; i < u.length; i++) c = (c >>> 8) ^ __crcTable[(c ^ u[i]) & 0xFF];
        return (c ^ -1) >>> 0;
    }
    function dosDateTime(d) {
        return {
            t: (d.getHours() << 11) | (d.getMinutes() << 5) | (d.getSeconds() >> 1),
            dt: (((d.getFullYear() - 1980) & 0x7f) << 9) | ((d.getMonth() + 1) << 5) | d.getDate(),
        };
    }
    function leU32(v) { return new Uint8Array([v & 255, (v >>> 8) & 255, (v >>> 16) & 255, (v >>> 24) & 255]); }
    function leU16(v) { return new Uint8Array([v & 255, (v >>> 8) & 255]); }
    function localHeader(nameB, crc, size, dos) {
        const h = new Uint8Array(30 + nameB.length);
        h.set(leU32(0x04034b50), 0);
        h.set(leU16(20), 4);
        h.set(leU16(0x0800), 6);
        h.set(leU16(0), 8);
        h.set(leU16(dos.t), 10);
        h.set(leU16(dos.dt), 12);
        h.set(leU32(crc), 14);
        h.set(leU32(size), 18);
        h.set(leU32(size), 22);
        h.set(leU16(nameB.length), 26);
        h.set(leU16(0), 28);
        h.set(nameB, 30);
        return h;
    }
    function centralEntry(nameB, crc, size, dos, offset) {
        const e = new Uint8Array(46 + nameB.length);
        e.set(leU32(0x02014b50), 0);
        e.set(leU16(20), 4);
        e.set(leU16(20), 6);
        e.set(leU16(0x0800), 8);
        e.set(leU16(0), 10);
        e.set(leU16(dos.t), 12);
        e.set(leU16(dos.dt), 14);
        e.set(leU32(crc), 16);
        e.set(leU32(size), 20);
        e.set(leU32(size), 24);
        e.set(leU16(nameB.length), 28);
        e.set(leU16(0), 30);
        e.set(leU16(0), 32);
        e.set(leU16(0), 34);
        e.set(leU16(0), 36);
        e.set(leU32(0), 38);
        e.set(leU32(offset), 42);
        e.set(nameB, 46);
        return e;
    }
    const enc = new TextEncoder();
    function zipEntryNumber(path) {
        const name = String(path || '').split('/').pop();
        const m = name.match(/^(\d+)(?=[ .])/) || name.match(/page-(\d+)\./i);
        return m ? Number(m[1]) : Infinity;
    }
    async function buildStoreZip(entries, onProgress) {
        const ordered = entries.slice().sort((a, b) => {
            const byPage = zipEntryNumber(a.path) - zipEntryNumber(b.path);
            return byPage || String(a.path).localeCompare(String(b.path));
        });
        const parts = [];
        const centralParts = [];
        let offset = 0;
        const base = new Date(Date.now() - ordered.length * 2000);
        for (let i = 0; i < ordered.length; i++) {
            const ent = ordered[i];
            const dos = dosDateTime(new Date(base.getTime() + i * 2000));
            const nameB = enc.encode(ent.path);
            const size = ent.blob.size;
            let crc = Number.isInteger(ent.crc) ? (ent.crc >>> 0) : null;
            if (crc === null) crc = crc32Bytes(await ent.blob.arrayBuffer());
            // Worker already read the page for its CRC: keep the original Blob as
            // the part rather than a second full-size ArrayBuffer per page.
            parts.push(localHeader(nameB, crc, size, dos), ent.blob);
            centralParts.push(centralEntry(nameB, crc, size, dos, offset));
            offset += 30 + nameB.length + size;
            if (onProgress) onProgress(i + 1, ordered.length);
            if ((i & 15) === 15) await new Promise(r => setTimeout(r, 0));
        }
        const cd = new Blob(centralParts);
        const cdBytes = new Uint8Array(await cd.arrayBuffer());
        const cdSize = cdBytes.length;
        const eocd = new Uint8Array(22);
        eocd.set(leU32(0x06054b50), 0);
        eocd.set(leU16(0), 4); eocd.set(leU16(0), 6);
        eocd.set(leU16(entries.length), 8); eocd.set(leU16(entries.length), 10);
        eocd.set(leU32(cdSize), 12);
        eocd.set(leU32(offset), 16);
        eocd.set(leU16(0), 20);
        parts.push(cd, eocd);
        return new Blob(parts, { type: 'application/zip' });
    }

    // =====================================================================
    // 12. Stylesheet Injection
    // =====================================================================
    // 12a. Light/dark scheme detection (environment / browser / OS)
    // =====================================================================
    // Real detection of the current color scheme, not a styling guess: we ask
    // the platform through prefers-color-scheme, which reflects the OS "dark
    // mode" toggle, the browser's own theme and any per-site override, and make
    // that decision the single authority - <html data-bwdd-theme> mirrors it,
    // bwddTheme gives the script a live value and onChange() subscribers, and
    // the dark palette <style> created in injectStyles() is gated on it, so the
    // theme follows the environment instead of relying on the page honouring a
    // media query. A 'change' listener keeps it in sync while the viewer is
    // already open, no reload needed.
    const bwddTheme = (() => {
        let scheme = 'light';          // resolved value: 'dark' | 'light'
        let started = false;
        let styleEl = null;            // dark-palette <style> gated by detection
        const subscribers = [];

        function mql(pref) {
            try {
                if (typeof window.matchMedia !== 'function') return null;
                return window.matchMedia('(prefers-color-scheme: ' + pref + ')');
            } catch (e) { return null; }
        }
        function readScheme() {
            // 'dark' wins; an explicit 'light' wins over nothing; anything
            // else (unsupported browser, "no-preference") resolves to light,
            // matching the script's default styling.
            const dark = mql('dark');
            if (dark && dark.matches) return 'dark';
            const light = mql('light');
            if (light && light.matches) return 'light';
            return 'light';
        }
        function publish() {
            try {
                if (document.documentElement) document.documentElement.setAttribute('data-bwdd-theme', scheme);
            } catch (e) {}
            for (const fn of subscribers) { try { fn(scheme); } catch (e) {} }
        }
        function gateStyle() {
            // The dark-palette <style> is in the document only while the
            // environment reports dark: attaching/removing the element is the most
            // widely supported gate (no reliance on CSSOM .disabled semantics) and
            // costs nothing - light mode has no dark sheet, dark mode appends one
            // after the base sheet.
            if (!styleEl) return;
            const host = (typeof document !== 'undefined' && (document.head || document.documentElement)) || null;
            if (!host) return;
            const connected = typeof styleEl.isConnected === 'boolean' ? styleEl.isConnected : !!styleEl.parentNode;
            const dark = scheme === 'dark';
            try {
                if (dark && !connected) host.appendChild(styleEl);
                else if (!dark && connected && styleEl.parentNode) styleEl.parentNode.removeChild(styleEl);
            } catch (e) {}
        }
        function onMediaChange() {
            const next = readScheme();
            if (next === scheme) return;
            scheme = next;
            gateStyle();
            publish();
            if (BWDD_DEBUG) { try { console.info('[bwdd] light/dark scheme:', scheme); } catch (e) {} }
        }
        return {
            start() {
                if (started) return scheme;
                started = true;
                scheme = readScheme();
                publish();
                const dark = mql('dark');
                const light = mql('light');
                const attach = (mq) => {
                    if (!mq) return;
                    const fn = () => onMediaChange();
                    if (typeof mq.addEventListener === 'function') mq.addEventListener('change', fn);
                    else if (typeof mq.addListener === 'function') mq.addListener(fn);   // legacy Safari
                };
                attach(dark); attach(light);
                if (BWDD_DEBUG) { try { console.info('[bwdd] light/dark scheme:', scheme); } catch (e) {} }
                return scheme;
            },
            get current() { return scheme; },
            isDark() { return scheme === 'dark'; },
            onChange(fn) {
                if (typeof fn === 'function') subscribers.push(fn);
                if (started) { try { fn(scheme); } catch (e) {} }
            },
            attachStyle(el) {
                styleEl = el;
                gateStyle();
            },
        };
    })();
    try { bwddTheme.start(); } catch (e) {}
    try {
        console.info('[bwdd] ' + sitePanelTitle() + ' v' + BWDD_VERSION + ' loaded, image codec: ' +
            IMAGE_CODEC.fmt + (IMAGE_CODEC.lossless ? ' (lossless)' : ' q' + IMAGE_CODEC.quality) +
            ', extension .' + IMAGE_CODEC.ext);
    } catch (e) {}
    if (BWDD_DEBUG) { try { window.__bwddTheme = bwddTheme; } catch (e) {} }

    let __bwddCssInjected = false;
    function injectStyles() {
        if (__bwddCssInjected) return;
        __bwddCssInjected = true;

        const font = document.createElement('link');
        font.href = 'https://fonts.googleapis.com/css2?family=Outfit:wght@400;500;600;700&display=swap';
        font.rel = 'stylesheet';
        document.head.appendChild(font);

        const css = document.createElement('style');
        css.textContent = `
#bwdd-root {
  --bwdd-accent-fill: #1d4ed8;
  --bwdd-amber-fill: #fcd9a8;
  --bwdd-bg: #ffffff;
  --bwdd-bg-ctrl: #f1f5f9;
  --bwdd-bg-ctrl-hover: #e2e8f0;
  --bwdd-bg-hover: #f1f5f9;
  --bwdd-bg-sunken: #f8fafc;
  --bwdd-border: #e2e8f0;
  --bwdd-border-soft: #f1f5f9;
  --bwdd-border-strong: #cbd5e1;
  --bwdd-code-bg: #f8fafc;
  --bwdd-danger: #b91c1c;
  --bwdd-danger-bg: #fef2f2;
  --bwdd-danger-border: #fecaca;
  --bwdd-glow-offline: 0 0 6px rgba(220, 38, 38, 0.45);
  --bwdd-glow-online: 0 0 6px rgba(21, 128, 61, 0.4);
  --bwdd-icon: #64748b;
  --bwdd-link: #1d4ed8;
  --bwdd-link-hover: #1e40af;
  --bwdd-link-hover-bg: rgba(29, 78, 216, 0.06);
  --bwdd-offline: #dc2626;
  --bwdd-root-fg: #0f172a;
  --bwdd-success: #15803d;
  --bwdd-success-dot: #15803d;
  --bwdd-text: #1e293b;
  --bwdd-text-ctrl: #334155;
  --bwdd-text-faint: #64748b;
  --bwdd-text-fainter: #94a3b8;
  --bwdd-text-muted: #475569;
  --bwdd-text-soft: #334155;
  --bwdd-text-strong: #0f172a;
  --bwdd-title: #1e293b;
  --bwdd-warn-bg: #fffbeb;
  --bwdd-warn-border: #fde68a;
  --bwdd-warn-code-bg: #fef9c3;
  --bwdd-warn-text: #92400e;
  --bwdd-caps-on-bg: #ecfdf5;
  --bwdd-caps-on-border: #a7f3d0;
  --bwdd-caps-on-text: #065f46;
  --bwdd-caps-on-strong: #064e3b;
  --bwdd-caps-off-bg: #f8fafc;
  --bwdd-caps-off-border: #e2e8f0;
  --bwdd-busy: #d97706;   /* amber, bridge busy (OCR/upload) */
  --bwdd-glow-busy: 0 0 6px rgba(217, 119, 6, 0.45);
  --bwdd-white: #ffffff;

  position: fixed;
  top: 16px;
  right: 24px;   /* room to grow leftward when the stats column mounts */
  z-index: 2147483647;
  width: 400px;   /* single-column default; widens to 640px once the stats column mounts */
  max-width: calc(100vw - 24px);
  max-height: calc(100vh - 32px);
  min-height: 0;
  background: var(--bwdd-bg);
  color: var(--bwdd-root-fg);
  border-radius: 14px;
  border: 1px solid var(--bwdd-border);
  box-shadow: 0 12px 32px rgba(15, 23, 42, 0.12), 0 2px 6px rgba(15, 23, 42, 0.04);
  font-family: 'Outfit', -apple-system, BlinkMacSystemFont, "Segoe UI", Roboto, sans-serif;
  font-size: 12px;
  line-height: 1.4;
  display: flex;
  flex-direction: column;
  overflow: hidden;
  user-select: none;
  transition: height 0.2s ease, opacity 0.15s ease, width 0.25s ease, transform 0.25s ease;
}
#bwdd-root * { box-sizing: border-box; }
#bwdd-root.collapsed { height: auto !important; max-height: none !important; }
#bwdd-root.collapsed .bwdd-body { display: none; }
#bwdd-root.bwdd-stats-visible { width: 640px; }   /* two-column width, once there is a stats column to show */
@media (prefers-reduced-motion: reduce) {
  #bwdd-root, #bwdd-root *, .bwdd-btn, .bwdd-bar-fill { transition: none !important; }
}

/* Header with Drag Handle */
.bwdd-head {
  display: flex;
  align-items: center;
  justify-content: space-between;
  gap: 8px;
  padding: 10px 10px 10px 12px;
  background: var(--bwdd-bg);
  border-bottom: 1px solid var(--bwdd-border-soft);
  cursor: grab;
  touch-action: none;
}
.bwdd-head:active { cursor: grabbing; }
.bwdd-title-group { display: flex; flex-direction: column; min-width: 0; }
.bwdd-title {
  margin: 0;
  font-size: 13px;
  font-weight: 700;
  color: var(--bwdd-title);
  display: flex;
  align-items: center;
  gap: 6px;
  line-height: 1.2;
}
.bwdd-title .bwdd-icon { font-size: 14px; }
.bwdd-title-sub {
  display: flex;
  align-items: center;
  gap: 5px;
  min-width: 0;
}
.bwdd-subtitle {
  font-size: 11px;
  color: var(--bwdd-text-muted);
  font-weight: 500;
  margin-top: 1px;
  white-space: nowrap;
  overflow: hidden;
  text-overflow: ellipsis;
  flex: 0 1 auto;   /* natural width, the GitHub link sits right after the text */
  min-width: 0;
}
.bwdd-gh {
  display: inline-flex;
  align-items: center;
  justify-content: center;
  flex-shrink: 0;
  width: 17px;
  height: 17px;
  border-radius: 5px;
  color: var(--bwdd-text-muted);
  text-decoration: none;
  transition: background 0.15s, color 0.15s;
}
.bwdd-gh svg { width: 12px; height: 12px; fill: currentColor; display: block; }
.bwdd-gh:hover { color: var(--bwdd-link); background: var(--bwdd-link-hover-bg); }
.bwdd-gh:focus-visible { outline: 2px solid var(--bwdd-link); outline-offset: 1px; }
.bwdd-head-controls { display: flex; align-items: center; gap: 2px; flex-shrink: 0; }
.bwdd-ctrl-btn {
  background: transparent;
  border: none;
  color: var(--bwdd-text-muted);
  font-size: 15px;
  line-height: 1;
  min-width: 32px;
  min-height: 32px;
  width: 32px;
  height: 32px;
  border-radius: 8px;
  display: inline-flex;
  align-items: center;
  justify-content: center;
  cursor: pointer;
  transition: background 0.15s, color 0.15s;
}
.bwdd-ctrl-btn:hover { background: var(--bwdd-bg-hover); color: var(--bwdd-text-strong); }
.bwdd-ctrl-btn:focus-visible { outline: 2px solid var(--bwdd-link); outline-offset: 2px; }
.bwdd-ctrl-btn:disabled { opacity: 0.5; cursor: not-allowed; }

/* Scrollable Body */
.bwdd-body {
  padding: 10px 12px 12px;
  overflow: hidden;
  display: flex;
  flex-direction: row;
  gap: 10px;
  background: var(--bwdd-bg);
  user-select: text;
  flex: 1 1 auto;
  min-height: 0;
}
.bwdd-col { min-height: 0; }   /* allow the scrollable columns to shrink when the panel is resized vertically */
.bwdd-col {
  display: flex;
  flex-direction: column;
  gap: 8px;
  min-height: 0;
}
.bwdd-col-stats {
  flex: 0 0 250px;
  overflow-y: auto;
  overscroll-behavior: contain;
}
.bwdd-col-main {
  flex: 1 1 auto;
  min-width: 0;
  overflow-y: auto;
  overscroll-behavior: contain;
}
/* Hairline between the controls column and the reading-stats column. It is
   appended together with the stats column, so it only exists once stats do. */
.bwdd-col-sep {
  flex: 0 0 auto;
  align-self: stretch;
  width: 1px;
  margin: 2px 0;
  background: var(--bwdd-border);
}
@media (max-width: 660px) {
  .bwdd-body { flex-direction: column; overflow-y: auto; }
  .bwdd-col-sep { display: none; }
  .bwdd-col-stats, .bwdd-col-main { flex: none; width: 100%; overflow: visible; }
}

/* Bridge Health Indicator */
.bwdd-bridge-pill {
  font-size: 11px;
  color: var(--bwdd-text-muted);
  display: flex;
  align-items: center;
  gap: 6px;
  padding: 0 2px;
  min-height: 24px;
}
.bwdd-indicator-dot {
  width: 8px;
  height: 8px;
  border-radius: 50%;
  background: var(--bwdd-text-fainter);
  display: inline-block;
  flex-shrink: 0;
}
.bwdd-indicator-dot.online { background: var(--bwdd-success-dot); box-shadow: var(--bwdd-glow-online); }

/* "What is the Mokuro Bridge?" help dot + toggleable infobox */
.bwdd-info-dot {
  width: 22px;
  height: 22px;
  border-radius: 50%;
  border: 1px solid var(--bwdd-border-strong);
  background: var(--bwdd-bg-sunken);
  color: var(--bwdd-icon);
  font-size: 11px;
  font-weight: 700;
  line-height: 1;
  padding: 0;
  font-family: inherit;
  display: inline-flex;
  align-items: center;
  justify-content: center;
  cursor: pointer;
  flex-shrink: 0;
  transition: background 0.15s, color 0.15s, border-color 0.15s;
}
.bwdd-info-dot:hover,
.bwdd-info-dot:focus-visible,
.bwdd-info-dot[aria-expanded="true"] {
  background: var(--bwdd-accent-fill);
  border-color: var(--bwdd-accent-fill);
  color: var(--bwdd-white);
}
.bwdd-info-dot:focus-visible { outline: 2px solid rgba(29, 78, 216, 0.4); outline-offset: 1px; }
/* "mokuro missing" alert (below the bridge row) + mokuro detail line in the info box */
.bwdd-mokuro-alert {
  margin: 2px 0 6px;
  padding: 7px 9px;
  font-size: 11px;
  line-height: 1.45;
  color: var(--bwdd-danger);
  background: var(--bwdd-danger-bg);
  border: 1px solid var(--bwdd-danger-border);
  border-radius: 8px;
}
.bwdd-mokuro-alert:empty { display: none; }
.bwdd-indicator-dot.offline {
  background: var(--bwdd-offline);
  box-shadow: var(--bwdd-glow-offline);
}
.bwdd-indicator-dot.busy {
  background: var(--bwdd-busy);
  box-shadow: var(--bwdd-glow-busy);
}
.bwdd-bridge-info-mokuro {
  display: block;
  margin-bottom: 6px;
  font-size: 11px;
  font-weight: 600;
  color: var(--bwdd-success);
}
.bwdd-bridge-info-mokuro.missing { color: var(--bwdd-danger); }
/* The bridge "?" infobox is positioned as an overlay popover (see the shared
   .bwdd-name-pop / .bwdd-bridge-pop box below); this anchor keeps it glued to
   the bridge status row it belongs to. */
.bwdd-bridge-anchor { position: relative; }
.bwdd-bridge-info-title {
  display: block;
  font-size: 11px;
  font-weight: 700;
  text-transform: uppercase;
  letter-spacing: 0.07em;
  color: var(--bwdd-text-muted);
  margin-bottom: 7px;
}
.bwdd-bridge-info-section { display: block; }
.bwdd-bridge-info-subhead {
  display: block;
  font-size: 11px;
  font-weight: 700;
  text-transform: uppercase;
  letter-spacing: 0.06em;
  color: var(--bwdd-text-muted);
  margin-bottom: 2px;
}
.bwdd-bridge-info-divider {
  border: none;
  border-top: 1px solid var(--bwdd-border);
  margin: 7px 0;
}
.bwdd-bridge-info-body { display: block; }
.bwdd-bridge-info-link {
  display: flex;
  align-items: center;
  justify-content: center;
  gap: 4px;
  color: var(--bwdd-link);
  text-decoration: none;
  font-weight: 600;
  font-size: 11px;
  line-height: 1.5;
  border: 1px solid currentColor;
  border-radius: 6px;
  padding: 4px 8px;
  min-height: 24px;
  white-space: nowrap;
}
.bwdd-bridge-info-link:hover { text-decoration: underline; background: var(--bwdd-link-hover-bg); }
.bwdd-bridge-info-link:focus-visible { outline: 2px solid var(--bwdd-link); outline-offset: 2px; }

/* Progress Bars */
.bwdd-bars {
  display: none;
  flex-direction: column;
  gap: 6px;
  padding: 8px 10px;
  background: var(--bwdd-bg-sunken);
  border: 1px solid var(--bwdd-border);
  border-radius: 10px;
}
.bwdd-bar-row { display: none; flex-direction: column; gap: 3px; }
.bwdd-bar-meta {
  display: flex;
  justify-content: space-between;
  gap: 8px;
  font-size: 11px;
  font-weight: 600;
  color: var(--bwdd-text-muted);
}
.bwdd-bar-rate { font-variant-numeric: tabular-nums; color: var(--bwdd-text-strong); }
.bwdd-bar-track {
  position: relative;
  height: 6px;
  background: var(--bwdd-border);
  border-radius: 999px;
  overflow: hidden;
}
.bwdd-bar-fill,
.bwdd-bar-fill-bg {
  position: absolute;
  left: 0;
  top: 0;
  height: 100%;
  width: 0%;
  border-radius: 999px;
  transition: width 0.2s ease;
}
.bwdd-bar-fill { z-index: 2; }
.bwdd-bar-fill-bg {
  z-index: 1;
  background: var(--bwdd-amber-fill);   /* faint amber, pages received, not yet OCR'd */
}
.bwdd-bar-legend {
  font-size: 10px;
  line-height: 1.4;
  color: var(--bwdd-text-faint);
  margin-top: 1px;
}

/* Cards & Badges, compact, LearnNatively / Manga-Kotoba inspired */
.bwdd-cards { display: flex; flex-direction: column; gap: 8px; }
.bwdd-cards:empty { display: none; }
.bwdd-card {
  border: 1px solid var(--bwdd-border);
  background: var(--bwdd-bg);
  border-radius: 10px;
  padding: 8px 10px;
}
.bwdd-card h3 {
  margin: 0 0 5px;
  font-size: 11px;
  font-weight: 700;
  text-transform: uppercase;
  letter-spacing: 0.07em;
  color: var(--bwdd-text-muted);
  line-height: 1.3;
}
.bwdd-card[data-card="book"] {
  background: var(--bwdd-bg-sunken);
  border-color: var(--bwdd-border-strong);
}
.bwdd-book-title {
  font-size: 12px;
  font-weight: 700;
  color: var(--bwdd-text-strong);
  margin-bottom: 5px;
  line-height: 1.3;
  display: -webkit-box;
  -webkit-line-clamp: 2;
  -webkit-box-orient: vertical;
  overflow: hidden;
}
.bwdd-spec-badges {
  display: flex;
  flex-wrap: wrap;
  gap: 4px;
  margin-top: 2px;
}
.bwdd-spec-badges:empty { display: none; }
.bwdd-spec-badge {
  display: inline-flex;
  align-items: baseline;
  gap: 4px;
  font-size: 11px;
  background: var(--bwdd-bg);
  border: 1px solid var(--bwdd-border);
  border-radius: 6px;
  padding: 1px 6px;
  line-height: 1.5;
}
.bwdd-spec-lbl { color: var(--bwdd-text-muted); font-weight: 500; }
.bwdd-spec-val { color: var(--bwdd-text-strong); font-weight: 600; font-variant-numeric: tabular-nums; }

.bwdd-card-sub { font-size: 11px; font-weight: 600; color: var(--bwdd-text); margin-bottom: 4px; line-height: 1.35; }
.bwdd-lvl-cap { font-size: 10px; color: var(--bwdd-text-muted); font-weight: 500; }

/* Compact stat rows (shared LN + MK) */
.bwdd-grid {
  display: grid;
  grid-template-columns: 1fr auto;
  gap: 1px 10px;
  font-size: 11px;
  margin: 2px 0 4px;
}
.bwdd-grid dt { color: var(--bwdd-text-muted); font-weight: 500; line-height: 1.6; }
.bwdd-grid dd { margin: 0; text-align: right; font-variant-numeric: tabular-nums; font-weight: 600; color: var(--bwdd-title); line-height: 1.6; }

.bwdd-card-links { display: flex; gap: 6px; margin-top: 6px; font-size: 11px; }
.bwdd-link {
  color: var(--bwdd-link);
  text-decoration: none;
  font-weight: 600;
  display: inline-flex;
  align-items: center;
  justify-content: center;
  border: 1px solid currentColor;
  border-radius: 6px;
  padding: 3px 8px;
  font-size: 11px;
  line-height: 1.5;
  min-height: 24px;
}
.bwdd-card-links .bwdd-link { flex: 1; text-align: center; }
.bwdd-link:hover { text-decoration: underline; background: var(--bwdd-link-hover-bg); }
.bwdd-link:focus-visible { outline: 2px solid var(--bwdd-link); outline-offset: 2px; }

.bwdd-nlvl-pill {
  display: inline-flex;
  align-items: center;
  gap: 2px;
  border-radius: 6px;
  padding: 2px 9px;
  font-size: 11px;
  font-weight: 700;
  letter-spacing: 0.03em;
  line-height: 1.5;
  min-height: 22px;
}
/* LearnNatively card: warm cream body, brown text, teal links */
.bwdd-card[data-card="natively"] {
  background: #faf6ee;
  border-color: #e8ddc9;
  color: #3f3227;
  box-shadow: none;
}
.bwdd-card[data-card="natively"] h3 { color: #8a6d3b; }
.bwdd-card[data-card="natively"] .bwdd-card-sub { color: #3f3227; }
.bwdd-card[data-card="natively"] .bwdd-lvl-cap { color: #6f5f4d; }
.bwdd-card[data-card="natively"] .bwdd-link { color: #0f766e; border-color: #0f766e; }
.bwdd-card[data-card="natively"] .bwdd-link:hover { background: rgba(15, 118, 110, 0.08); }
.bwdd-card[data-card="natively"] .bwdd-link:focus-visible { outline-color: #0f766e; }
.bwdd-ln-head {
  display: flex;
  align-items: center;
  gap: 10px;
  flex-wrap: wrap;
  margin-bottom: 4px;
}
.bwdd-ln-title-row {
  display: block;
  flex: 1 1 160px;
  min-width: 0;
  margin-bottom: 0;
  line-height: 1.45;
}
.bwdd-ln-meta {
  display: flex;
  align-items: center;
  justify-content: flex-start;
  gap: 6px;
  flex-wrap: wrap;
  margin: 0;
  flex: 0 0 auto;
}
.bwdd-ln-social {
  display: flex;
  justify-content: space-between;
  flex-wrap: wrap;
  gap: 3px 16px;
  border-top: 1px solid #e8ddc9;
  padding-top: 6px;
  margin: 6px 0 0;
  line-height: 1.7;
  font-size: 11px;
  color: #6f5f4d;
  text-align: left;
}
/* Manga-Kotoba card: plain white body, sage text, hairline ledger rows */
.bwdd-card[data-card="manga-kotoba"] {
  background: #ffffff;
  border-color: #dfe3d2;
  color: #243b2a;
  box-shadow: none;
}
.bwdd-card[data-card="manga-kotoba"] h3 { color: #6b5d2e; }
.bwdd-card[data-card="manga-kotoba"] .bwdd-grid { margin-bottom: 2px; }
.bwdd-card[data-card="manga-kotoba"] .bwdd-grid dt,
.bwdd-card[data-card="manga-kotoba"] .bwdd-grid dd {
  padding: 1px 0;
  border-bottom: 1px solid #edf0e3;
}
.bwdd-card[data-card="manga-kotoba"] .bwdd-grid dt { color: #5b6650; }
.bwdd-card[data-card="manga-kotoba"] .bwdd-grid dd { color: #243b2a; }
.bwdd-card[data-card="manga-kotoba"] .bwdd-link { color: #3f6212; }
.bwdd-card[data-card="manga-kotoba"] .bwdd-link:hover { background: rgba(63, 98, 18, 0.07); }
.bwdd-card[data-card="manga-kotoba"] .bwdd-link:focus-visible { outline-color: #3f6212; }
.bwdd-mk-title {
  display: block;
  text-align: center;
  margin-bottom: 2px;
}
.bwdd-lnbadge {
  display: inline-block;
  border: 1px solid var(--bwdd-border-strong);
  border-radius: 5px;
  color: var(--bwdd-text-muted);
  font-size: 10px;
  font-weight: 700;
  padding: 0 5px;
  line-height: 1.6;
}
.bwdd-none { font-size: 11px; color: var(--bwdd-text-muted); margin: 0 0 6px; line-height: 1.5; text-align: center; }

/* Action Buttons */
.bwdd-actions { display: flex; flex-direction: column; gap: 6px; margin-top: 2px; }

/* Upload destination picker */
.bwdd-dest {
  display: flex;
  flex-direction: column;
  gap: 5px;
  margin-top: 6px;
  padding: 8px 10px;
  background: var(--bwdd-bg-sunken);
  border: 1px solid var(--bwdd-border);
  border-radius: 10px;
}
.bwdd-dest-label { font-size: 11px; font-weight: 600; color: var(--bwdd-text-muted); }
.bwdd-opt-row { display: flex; align-items: center; gap: 6px; }
.bwdd-opt-row > * { flex: 1 1 0; min-width: 0; }
.bwdd-opt-row > .bwdd-dest-label { flex: 0 0 auto; white-space: nowrap; }
/* Pre-flight numbers, shown inside the bridge row's "?" popover. */
.bwdd-caps-line {
  display: block;
  font-weight: 600;
  color: var(--bwdd-text-strong);
  margin: 2px 0 4px;
}
.bwdd-bridge-info-section.on .bwdd-caps-line { color: var(--bwdd-caps-on-strong); }
.bwdd-caps-note { font-size: 10px; color: var(--bwdd-text-faint); }
/* Advanced image settings, collapsed so they stay out of the way. */
.bwdd-fmt { margin-top: 8px; }
.bwdd-fmt-summary {
  cursor: pointer;
  font-size: 11px;
  font-weight: 600;
  color: var(--bwdd-text-muted);
  padding: 3px 2px;
  border-radius: 4px;
}
.bwdd-fmt-summary:hover { color: var(--bwdd-link); }
.bwdd-fmt-summary:focus-visible { outline: 2px solid var(--bwdd-link); outline-offset: 1px; }
.bwdd-fmt[open] > .bwdd-fmt-summary { margin-bottom: 2px; }

.bwdd-dest-select, .bwdd-dest-input {
  font: 12px inherit;
  padding: 5px 7px;
  border: 1px solid var(--bwdd-border-strong);
  border-radius: 6px;
  background: var(--bwdd-bg);
  color: var(--bwdd-root-fg);
  width: 100%;
}
.bwdd-dest-select:focus-visible, .bwdd-dest-input:focus-visible { outline: 2px solid var(--bwdd-link); outline-offset: 1px; }
.bwdd-dest-localdir { display: flex; flex-direction: column; gap: 3px; }
.bwdd-dest-hint { font-size: 11px; color: var(--bwdd-warn-text); background: var(--bwdd-warn-bg); border: 1px solid var(--bwdd-warn-border); border-radius: 6px; padding: 5px 7px; line-height: 1.4; }
.bwdd-dest-hint code { font-family: ui-monospace, monospace; font-size: 10px; background: var(--bwdd-warn-code-bg); border-radius: 3px; padding: 0 3px; }
/* Archive-name field (above the action buttons): one compact row of label,
   input and "?" info dot; the popover it opens overlays the buttons below. */
.bwdd-name {
  position: relative;
  display: flex;
  align-items: center;
  gap: 6px;
}
.bwdd-name .bwdd-dest-label { flex: 0 0 auto; }
.bwdd-name .bwdd-dest-input { flex: 1 1 auto; width: auto; min-width: 0; padding-top: 4px; padding-bottom: 4px; }
.bwdd-name .bwdd-info-dot {
  flex: 0 0 auto;
  width: 18px;
  height: 18px;
  min-width: 18px;
  min-height: 18px;
  font-size: 10px;
}
/* "?" popovers (archive-name field + Mokuro Bridge info): one shared overlay
   look. Each popover is absolutely positioned under its own row (its anchor
   sets position:relative) and overlays whatever sits below, so opening one
   never takes layout space or pushes content around. */
.bwdd-name-pop,
.bwdd-bridge-pop {
  position: fixed;
  top: 0;
  left: 0;
  z-index: 8;
  width: 300px;
  max-width: calc(100vw - 24px);
  max-height: calc(100vh - 24px);
  overflow-y: auto;
  overscroll-behavior: contain;
  padding: 9px 11px;
  background: var(--bwdd-bg);
  color: var(--bwdd-text-soft);
  border: 1px solid var(--bwdd-border-strong);
  border-radius: 8px;
  box-shadow: 0 10px 28px rgba(15, 23, 42, 0.18), 0 2px 6px rgba(15, 23, 42, 0.08);
  font-size: 11px;
  line-height: 1.5;
}
.bwdd-name-pop > div + div { margin-top: 5px; }
.bwdd-name-pop[hidden], .bwdd-bridge-pop[hidden] { display: none; }
.bwdd-btn-fill {
  flex: 0 0 auto;
  font: 600 11px inherit;
  padding: 5px 8px;
  border: 1px solid var(--bwdd-border-strong);
  border-radius: 6px;
  background: var(--bwdd-bg-ctrl);
  color: var(--bwdd-text-ctrl);
  cursor: pointer;
  white-space: nowrap;
}
.bwdd-btn-fill:hover { background: var(--bwdd-bg-ctrl-hover); }
.bwdd-btn-fill:focus-visible { outline: 2px solid var(--bwdd-link); outline-offset: 1px; }
.bwdd-btn {
  display: flex;
  flex-direction: column;
  align-items: center;
  justify-content: center;
  width: 100%;
  padding: 8px 12px;
  min-height: 44px;
  border: none;
  border-radius: 10px;
  font-family: inherit;
  font-size: 12px;
  font-weight: 600;
  color: var(--bwdd-white);
  cursor: pointer;
  transition: transform 0.15s ease, box-shadow 0.15s ease, opacity 0.15s;
}
.bwdd-btn-sub {
  font-size: 11px;
  font-weight: 400;
  opacity: 0.9;
  margin-top: 1px;
}
.bwdd-btn > span { text-align: center; width: 100%; }
.bwdd-btn:hover:not(:disabled) {
  transform: translateY(-1px);
}
.bwdd-btn:active:not(:disabled) { transform: translateY(0); }
.bwdd-btn:focus-visible { outline: 2px solid var(--bwdd-root-fg); outline-offset: 2px; }
.bwdd-btn:disabled { opacity: 0.6; cursor: not-allowed; }
@media (forced-colors: active) {
  .bwdd-btn, .bwdd-nlvl-pill { forced-color-adjust: none; }
}

.bwdd-btn.zip {
  background: linear-gradient(135deg, #15803d 0%, #166534 100%);
  box-shadow: 0 4px 12px rgba(22, 101, 52, 0.25);
}
.bwdd-btn.zip:hover:not(:disabled) {
  box-shadow: 0 6px 16px rgba(22, 101, 52, 0.35);
}
.bwdd-btn.ocr {
  background: linear-gradient(135deg, #2563eb 0%, #1d4ed8 100%);
  box-shadow: 0 4px 12px rgba(37, 99, 235, 0.25);
}
.bwdd-btn.ocr:hover:not(:disabled) {
  box-shadow: 0 6px 16px rgba(37, 99, 235, 0.35);
}

/* Destination section dimmed while a run holds the lock */
.bwdd-dest-locked { opacity: 0.7; }

/* "Open Reader Mokuro" + open-file/copy, one quiet row, only after a
   successful OCR run. Both are secondary actions, so they share a calm
   outline-button look instead of loud filled gradients. */
.bwdd-reader-row {
  display: none;
  grid-template-columns: repeat(auto-fit, minmax(150px, 1fr));
  gap: 6px;
  margin-top: 6px;
}
.bwdd-reader-row > .bwdd-ghost-btn {
  min-width: 0;
  width: 100%;
  display: inline-flex;
  align-items: center;
  justify-content: center;
  gap: 5px;
  padding: 6px 10px;
  min-height: 30px;
  border: 1px solid var(--bwdd-border-strong);
  border-radius: 8px;
  background: var(--bwdd-bg);
  color: var(--bwdd-text-muted);
  font-family: inherit;
  font-size: 11px;
  font-weight: 600;
  line-height: 1.4;
  white-space: nowrap;
  overflow: hidden;
  text-overflow: ellipsis;
  cursor: pointer;
  transition: background 0.15s, color 0.15s, border-color 0.15s;
}
.bwdd-reader-row > .bwdd-ghost-btn:hover {
  background: var(--bwdd-bg-sunken);
  color: var(--bwdd-link);
  border-color: var(--bwdd-link);
}
.bwdd-reader-row > .bwdd-ghost-btn:focus-visible {
  outline: 2px solid var(--bwdd-link);
  outline-offset: 1px;
}

.bwdd-hint-box {
  font-size: 11px;
  color: var(--bwdd-text-muted);
  margin: 0;
  white-space: pre-wrap;
  line-height: 1.45;
}
.bwdd-hint-box:empty { display: none; }
/* Collapsible raw-error block inside the status area (see setRunDetails) */
.bwdd-hint-box details { margin-top: 6px; }
.bwdd-hint-box summary {
  cursor: pointer;
  color: var(--bwdd-link);
  font-weight: 600;
  text-decoration: underline;
  text-underline-offset: 2px;
}
.bwdd-hint-box summary:hover { color: var(--bwdd-link-hover); }
.bwdd-hint-box pre {
  margin: 6px 0 0;
  padding: 6px 8px;
  background: var(--bwdd-code-bg);
  border: 1px solid var(--bwdd-border);
  border-radius: 6px;
  font-family: ui-monospace, SFMono-Regular, Menlo, Consolas, monospace;
  font-size: 10px;
  line-height: 1.55;
  white-space: pre-wrap;
  word-break: break-word;
  color: var(--bwdd-text-muted);
  max-height: 140px;
  overflow: auto;
}
/* Panel flapped away to the right, an edge tab stays to bring it back */
#bwdd-root.bwdd-flapped { pointer-events: none; }
.bwdd-edge-tab {
  position: fixed;
  right: 0;
  top: 50%;
  transform: translateY(-50%);
  z-index: 2147483647;
  display: none;
  align-items: center;
  justify-content: center;
  width: 26px;
  height: 76px;
  padding: 0;
  border: none;
  border-radius: 10px 0 0 10px;
  background: #1d4ed8;
  color: #ffffff;
  font-size: 15px;
  line-height: 1;
  cursor: pointer;
  box-shadow: -3px 0 10px rgba(15, 23, 42, 0.18);
  transition: background 0.15s;
}
.bwdd-edge-tab:hover { background: #2563eb; }
.bwdd-edge-tab:focus-visible { outline: 2px solid #1d4ed8; outline-offset: -2px; }
/* Header drag grip + corner resize handle */
.bwdd-drag-grip {
  flex: 0 0 auto;
  display: inline-flex;
  align-items: center;
  justify-content: center;
  align-self: stretch;
  width: 16px;
  color: var(--bwdd-text-fainter);
  font-size: 11px;
  line-height: 1;
  cursor: grab;
  user-select: none;
  touch-action: none;
}
.bwdd-drag-grip:active { cursor: grabbing; }
.bwdd-resize {
  position: absolute;
  right: 0;
  bottom: 0;
  width: 22px;
  height: 22px;
  z-index: 6;
  cursor: nwse-resize;   /* corner: resize both width and height */
  touch-action: none;
  user-select: none;
}
.bwdd-resize::after {
  content: '';
  position: absolute;
  right: 4px;
  bottom: 4px;
  width: 9px;
  height: 9px;
  border-right: 2px solid var(--bwdd-text-fainter);
  border-bottom: 2px solid var(--bwdd-text-fainter);
  border-bottom-right-radius: 3px;
  opacity: 0.65;
  transition: opacity 0.15s;
}
.bwdd-resize:hover::after,
.bwdd-resize:active::after { opacity: 1; }
#bwdd-root.collapsed .bwdd-resize,
#bwdd-root.bwdd-flapped .bwdd-resize { display: none; }

`;
        (document.head || document.documentElement).appendChild(css);

        // Dark palette (only active while bwddTheme detects dark, section 12a).
        // This is a deliberate per-rule remap, not a blanket inversion: the
        // chrome and surfaces get a dark palette chosen for contrast, and the
        // LearnNatively / Manga-Kotoba stat cards get brand-matched dark variants
        // below. The only elements left alone are the Natively difficulty level
        // rectangles (.bwdd-nlvl-pill), whose semantic colors are set inline and
        // already read correctly on dark. The rules have no @media wrapper on
        // purpose: the stylesheet element is attached/removed by
        // bwddTheme.attachStyle() above, so the environment detection is the one
        // gate.
        const darkCss = document.createElement('style');
        darkCss.textContent = `
#bwdd-root {
  --bwdd-accent-fill: #3b82f6;
  --bwdd-amber-fill: rgba(245, 158, 11, 0.22);
  --bwdd-bg: #0f172a;
  --bwdd-bg-ctrl: #334155;
  --bwdd-bg-ctrl-hover: #475569;
  --bwdd-bg-hover: #1e293b;
  --bwdd-bg-sunken: #1e293b;
  --bwdd-border: #334155;
  --bwdd-border-soft: #1e293b;
  --bwdd-border-strong: #475569;
  --bwdd-code-bg: #0f172a;
  --bwdd-danger: #f87171;
  --bwdd-danger-bg: rgba(127, 29, 29, 0.28);
  --bwdd-danger-border: #7f1d1d;
  --bwdd-glow-offline: 0 0 6px rgba(248, 113, 113, 0.4);
  --bwdd-glow-online: 0 0 6px rgba(34, 197, 94, 0.45);
  --bwdd-icon: #cbd5e1;
  --bwdd-link: #60a5fa;
  --bwdd-link-hover: #93c5fd;
  --bwdd-link-hover-bg: rgba(96, 165, 250, 0.12);
  --bwdd-offline: #f87171;
  --bwdd-root-fg: #e2e8f0;
  --bwdd-success: #4ade80;
  --bwdd-success-dot: #22c55e;
  --bwdd-text: #e2e8f0;
  --bwdd-text-ctrl: #e2e8f0;
  --bwdd-text-faint: #94a3b8;
  --bwdd-text-fainter: #64748b;
  --bwdd-text-muted: #94a3b8;
  --bwdd-text-soft: #cbd5e1;
  --bwdd-text-strong: #f1f5f9;
  --bwdd-title: #f1f5f9;
  --bwdd-warn-bg: rgba(251, 191, 36, 0.12);
  --bwdd-warn-border: rgba(251, 191, 36, 0.35);
  --bwdd-warn-code-bg: rgba(251, 191, 36, 0.25);
  --bwdd-warn-text: #fcd34d;
  --bwdd-caps-on-bg: rgba(16, 185, 129, 0.14);
  --bwdd-caps-on-border: rgba(16, 185, 129, 0.38);
  --bwdd-caps-on-text: #6ee7b7;
  --bwdd-caps-on-strong: #a7f3d0;
  --bwdd-caps-off-bg: #1e293b;
  --bwdd-caps-off-border: #334155;
  --bwdd-busy: #f59e0b;
  --bwdd-glow-busy: 0 0 6px rgba(245, 158, 11, 0.5);
  --bwdd-white: #ffffff;
  background: var(--bwdd-bg);
  color: var(--bwdd-root-fg);
  border-color: var(--bwdd-border);
  box-shadow: 0 12px 32px rgba(0, 0, 0, 0.55), 0 2px 6px rgba(0, 0, 0, 0.35);
  color-scheme: dark;
}

/* LearnNatively card, dark variant: warm espresso surfaces with cream text.
   The difficulty level rectangles (.bwdd-nlvl-pill) are deliberately NOT
   restyled here, their semantic colors are set inline by JS and already
   read correctly on the dark card. */
.bwdd-card[data-card="natively"] {
  background: #201a12;
  border-color: #463a27;
  color: #e9dcbf;
  box-shadow: none;
}
.bwdd-card[data-card="natively"] h3 { color: #cfa95f; }
.bwdd-card[data-card="natively"] .bwdd-card-sub { color: #f0e6d2; }
.bwdd-card[data-card="natively"] .bwdd-lvl-cap { color: #bfa97f; }
.bwdd-card[data-card="natively"] .bwdd-lnbadge {
  border-color: #574832;
  background: #2a2319;
  color: #d5c5a6;
}
.bwdd-card[data-card="natively"] .bwdd-link { color: #2dd4bf; border-color: #2dd4bf; }
.bwdd-card[data-card="natively"] .bwdd-link:hover { background: rgba(45, 212, 191, 0.12); }
.bwdd-card[data-card="natively"] .bwdd-link:focus-visible { outline-color: #2dd4bf; }
.bwdd-card[data-card="natively"] .bwdd-ln-social {
  border-top-color: #4a3d2a;
  color: #c8b896;
}


/* Manga-Kotoba card, dark variant: deep sage ink with sage/cream text. */
.bwdd-card[data-card="manga-kotoba"] {
  background: #131a14;
  border-color: #2e3f33;
  color: #d9e4da;
  box-shadow: none;
}
.bwdd-card[data-card="manga-kotoba"] h3 { color: #cfbf7a; }
.bwdd-card[data-card="manga-kotoba"] .bwdd-card-sub { color: #e6efe7; }
.bwdd-card[data-card="manga-kotoba"] .bwdd-grid dt,
.bwdd-card[data-card="manga-kotoba"] .bwdd-grid dd {
  border-bottom-color: #283a2f;
}
.bwdd-card[data-card="manga-kotoba"] .bwdd-grid dt { color: #9db3a1; }
.bwdd-card[data-card="manga-kotoba"] .bwdd-grid dd { color: #e2ebe3; }
.bwdd-card[data-card="manga-kotoba"] .bwdd-link { color: #84cc16; border-color: #84cc16; }
.bwdd-card[data-card="manga-kotoba"] .bwdd-link:hover { background: rgba(132, 204, 22, 0.14); }
.bwdd-card[data-card="manga-kotoba"] .bwdd-link:focus-visible { outline-color: #84cc16; }
.bwdd-card[data-card="manga-kotoba"] .bwdd-none { color: #a9bcab; }
.bwdd-dest-select:focus-visible, .bwdd-dest-input:focus-visible,
.bwdd-btn-fill:focus-visible { outline-color: #60a5fa; }
.bwdd-hint-box summary { color: #60a5fa; }
.bwdd-hint-box summary:hover { color: #93c5fd; }
.bwdd-hint-box pre { background: #0f172a; border-color: #334155; color: #94a3b8; }
/* Edge restore tab (dark) */
.bwdd-edge-tab { background: #3b82f6; color: #ffffff; box-shadow: -3px 0 10px rgba(0, 0, 0, 0.4); }
.bwdd-edge-tab:hover { background: #60a5fa; }
.bwdd-edge-tab:focus-visible { outline-color: #60a5fa; }
/* Quiet reader/stored row (dark), colors come from --bwdd-* tokens */
.bwdd-reader-row > .bwdd-ghost-btn { background: var(--bwdd-bg); color: var(--bwdd-text-muted); border-color: var(--bwdd-border-strong); }
.bwdd-reader-row > .bwdd-ghost-btn:hover { background: var(--bwdd-bg-sunken); color: var(--bwdd-link); border-color: var(--bwdd-link); }

`;
        (document.head || document.documentElement).appendChild(darkCss);
        bwddTheme.attachStyle(darkCss);   // removed from the DOM unless dark is detected
    }
    const PANEL_POS_KEY = 'bwdd-panel-pos';
    const PANEL_COLLAPSED_KEY = 'bwdd-panel-collapsed';
    const PANEL_WIDTH_KEY = 'bwdd-panel-width';   // manual resize, if any
    const PANEL_HEIGHT_KEY = 'bwdd-panel-height';   // manual vertical resize, if any

    function buildUI() {
        injectStyles();
        const root = document.createElement('section');
        root.id = 'bwdd-root';
        // A labelled region, not a modal dialog: the panel never traps focus
        // or blocks the viewer behind it, and Esc collapses rather than closes.
        root.setAttribute('role', 'region');
        root.setAttribute('aria-labelledby', 'bwdd-panel-title');

        const head = document.createElement('div');
        head.className = 'bwdd-head';
        head.setAttribute('title', 'Drag to reposition');

        const titleGroup = document.createElement('div');
        titleGroup.className = 'bwdd-title-group';

        const title = document.createElement('h2');
        title.id = 'bwdd-panel-title';
        title.className = 'bwdd-title';
        title.innerHTML = '<span class="bwdd-icon" aria-hidden="true">📖</span> ' + sitePanelTitle();

        const titleSub = document.createElement('div');
        titleSub.className = 'bwdd-title-sub';

        const sub = document.createElement('div');
        sub.className = 'bwdd-subtitle';
        sub.textContent = `v${BWDD_VERSION} by ${BWDD_AUTHOR}`;

        const ghLink = document.createElement('a');
        ghLink.className = 'bwdd-gh';
        ghLink.href = BWDD_REPO_URL;
        ghLink.target = '_blank';
        ghLink.rel = 'noopener noreferrer';
        ghLink.setAttribute('aria-label', 'Open the GitHub repository in a new tab');
        ghLink.title = 'GitHub repository: ' + BWDD_REPO_URL;
        ghLink.innerHTML = '<svg viewBox="0 0 16 16" aria-hidden="true"><path d="M8 0C3.58 0 0 3.58 0 8c0 3.54 2.29 6.53 5.47 7.59.4.07.55-.17.55-.38 0-.19-.01-.82-.01-1.49-2.01.37-2.53-.49-2.69-.94-.09-.23-.48-.94-.82-1.13-.28-.15-.68-.52-.01-.53.63-.01 1.08.58 1.23.82.72 1.21 1.87.87 2.33.66.07-.52.28-.87.51-1.07-1.78-.2-3.64-.89-3.64-3.95 0-.87.31-1.59.82-2.15-.08-.2-.36-1.02.08-2.12 0 0 .67-.21 2.2.82.64-.18 1.32-.27 2-.27s1.36.09 2 .27c1.53-1.04 2.2-.82 2.2-.82.44 1.1.16 1.92.08 2.12.51.56.82 1.27.82 2.15 0 3.07-1.87 3.75-3.65 3.95.29.25.54.73.54 1.48 0 1.07-.01 1.93-.01 2.2 0 .21.15.46.55.38A8.01 8.01 0 0016 8c0-4.42-3.58-8-8-8z"/></svg>';
        titleSub.append(sub, ghLink);

        // A single-store build also points at the combined script. The module
        // that defines this is not in every target, so check before calling.
        if (typeof unifiedDownloaderLink === 'function') {
            const unified = unifiedDownloaderLink();
            if (unified) titleSub.appendChild(unified);
        }
        titleGroup.append(title, titleSub);

        const ctrlGroup = document.createElement('div');
        ctrlGroup.className = 'bwdd-head-controls';

        const minBtn = document.createElement('button');
        minBtn.type = 'button';
        minBtn.className = 'bwdd-ctrl-btn';
        minBtn.setAttribute('aria-label', 'Minimize panel');
        minBtn.setAttribute('aria-expanded', 'true');
        minBtn.setAttribute('aria-controls', 'bwdd-body');
        minBtn.textContent = '–';
        minBtn.setAttribute('title', 'Minimize panel (Esc)');
        function setCollapsed(isCol) {
            root.classList.toggle('collapsed', isCol);
            minBtn.textContent = isCol ? '+' : '–';
            minBtn.setAttribute('aria-label', isCol ? 'Expand panel' : 'Minimize panel');
            minBtn.setAttribute('aria-expanded', String(!isCol));
            try { localStorage.setItem(PANEL_COLLAPSED_KEY, isCol ? '1' : '0'); } catch (e) {}
        }
        minBtn.onclick = () => setCollapsed(!root.classList.contains('collapsed'));

        const closeBtn = document.createElement('button');
        closeBtn.type = 'button';
        closeBtn.className = 'bwdd-ctrl-btn';
        closeBtn.setAttribute('aria-label', 'Close downloader panel');
        closeBtn.setAttribute('title', 'Close panel');
        closeBtn.textContent = '×';
        // Close tears the panel down completely: it stops the bridge-health poll
        // and removes the window-level listener + observer, so nothing keeps
        // hitting 127.0.0.1:62642 or mutating detached DOM after the user closes
        // the panel. (The edge-tab "flap" is the non-destructive alternative.)
        closeBtn.onclick = () => {
            try { if (bridgeTimer) { clearTimeout(bridgeTimer); bridgeTimer = null; } } catch (e) {}
            try { window.removeEventListener('keydown', onPanelKeydown); } catch (e) {}
            try { document.removeEventListener('click', onNameDocClick); } catch (e) {}
            try { statsObs.disconnect(); } catch (e) {}
            try { root.remove(); } catch (e) {}
            try { if (edgeTab) edgeTab.remove(); } catch (e) {}
        };

        // "Flap" control: slides the whole panel off the right edge of the
        // screen (a small tab on the right edge brings it back).
        const flapBtn = document.createElement('button');
        flapBtn.type = 'button';
        flapBtn.className = 'bwdd-ctrl-btn';
        flapBtn.setAttribute('aria-label', 'Hide the panel to the right edge');
        flapBtn.setAttribute('aria-expanded', 'true');
        flapBtn.setAttribute('title', 'Slide the panel away to the right edge of the screen');
        flapBtn.textContent = '»';

        ctrlGroup.append(flapBtn, minBtn, closeBtn);

        // Visible drag grip at the left of the header (the whole header also
        // drags, this just makes the affordance obvious).
        const dragGrip = document.createElement('span');
        dragGrip.className = 'bwdd-drag-grip';
        dragGrip.setAttribute('aria-hidden', 'true');
        dragGrip.textContent = '\u283F';   // braille dots: grab handle look
        head.append(dragGrip, titleGroup, ctrlGroup);

        const body = document.createElement('div');
        body.className = 'bwdd-body';
        body.id = 'bwdd-body';

        const bridgeRow = document.createElement('div');
        bridgeRow.className = 'bwdd-bridge-pill';
        const dot = document.createElement('span');
        dot.className = 'bwdd-indicator-dot';
        dot.setAttribute('aria-hidden', 'true');
        const bridgeText = document.createElement('span');
        bridgeText.className = 'bwdd-bridge-text';
        bridgeText.textContent = 'Looking for the Mokuro Bridge helper…';
        bridgeRow.title = 'mokuro-bridge: a small local app (github.com/GolyBidoof/mokuro-bridge) that runs mokuro OCR on the downloaded pages and can upload the results.';
        bridgeRow.append(dot, bridgeText);

        // Red alert shown below the bridge row when the bridge runs but mokuro
        // itself is not installed, the OCR button is unusable in that state.
        const mokuroAlert = document.createElement('div');
        mokuroAlert.className = 'bwdd-mokuro-alert';
        mokuroAlert.style.display = 'none';
        mokuroAlert.setAttribute('role', 'alert');

        // "?" dot beside the bridge status row: opens an infobox under the row.
        // Popovers open from inside `.bwdd-col-main`, which scrolls and so clips
        // absolutely positioned children (the bridge one is taller than the
        // column), so they are fixed to the viewport instead.
        function placePopover(pop, anchor, align) {
            pop.hidden = false;
            const a = anchor.getBoundingClientRect();
            const w = pop.offsetWidth;
            const h = pop.offsetHeight;
            let left = align === 'right' ? a.right - w : a.left;
            left = Math.max(8, Math.min(left, window.innerWidth - w - 8));
            let top = a.bottom + 4;
            if (top + h > window.innerHeight - 8) top = Math.max(8, a.top - h - 4);
            pop.style.left = Math.round(left) + 'px';
            pop.style.top = Math.round(top) + 'px';
        }

        const infoDot = document.createElement('button');
        infoDot.type = 'button';
        infoDot.className = 'bwdd-info-dot';
        infoDot.setAttribute('aria-label', 'About the Mokuro Bridge and this run\u2019s connection speed');
        infoDot.setAttribute('aria-expanded', 'false');
        infoDot.textContent = '?';
        bridgeRow.insertBefore(infoDot, bridgeText);

        const bridgeInfoPop = document.createElement('div');
        bridgeInfoPop.className = 'bwdd-bridge-pop';
        bridgeInfoPop.hidden = true;
        const infoTitle = document.createElement('span');
        infoTitle.className = 'bwdd-bridge-info-title';
        infoTitle.textContent = 'What is the Mokuro Bridge?';

        // Section 1, the mokuro OCR engine installed on this machine
        // (version + custom-fork marker), or a red note when it's missing.
        // Updated from /health on each status tick.
        const mokuroSection = document.createElement('div');
        mokuroSection.className = 'bwdd-bridge-info-section';
        const mokuroSectionHeading = document.createElement('span');
        mokuroSectionHeading.className = 'bwdd-bridge-info-subhead';
        mokuroSectionHeading.textContent = 'Mokuro engine';
        const infoMokuro = document.createElement('span');
        infoMokuro.className = 'bwdd-bridge-info-mokuro';
        mokuroSection.append(mokuroSectionHeading, infoMokuro);

        const divider1 = document.createElement('hr');
        divider1.className = 'bwdd-bridge-info-divider';

        const aboutSection = document.createElement('div');
        aboutSection.className = 'bwdd-bridge-info-section';
        const aboutSectionHeading = document.createElement('span');
        aboutSectionHeading.className = 'bwdd-bridge-info-subhead';
        aboutSectionHeading.textContent = 'What it does';
        const infoBody = document.createElement('span');
        infoBody.className = 'bwdd-bridge-info-body';
        infoBody.textContent = 'A small companion app that runs locally on your computer. ' +
            'Choosing “Save and run through Mokuro” sends the downloaded pages to it, where ' +
            'mokuro runs Japanese OCR on them; the finished volume is then saved or ' +
            'uploaded wherever you pick. Plain “Save as ZIP” downloads don\'t use it.';
        aboutSection.append(aboutSectionHeading, infoBody);

        const divider2 = document.createElement('hr');
        divider2.className = 'bwdd-bridge-info-divider';

        const divider3 = document.createElement('hr');
        divider3.className = 'bwdd-bridge-info-divider';

        // Section 3, how many connections this run will actually get. Filled by
        // renderCapabilities() on every bridge poll, so it is accurate whether or
        // not the bridge is running.
        const connSection = document.createElement('div');
        connSection.className = 'bwdd-bridge-info-section';
        const connHeading = document.createElement('span');
        connHeading.className = 'bwdd-bridge-info-subhead';
        connHeading.textContent = 'Connection speed';
        const connNumbers = document.createElement('span');
        connNumbers.className = 'bwdd-caps-line';
        const connBody = document.createElement('span');
        connBody.className = 'bwdd-bridge-info-body';
        connSection.append(connHeading, connNumbers, connBody);

        const infoLink = document.createElement('a');
        infoLink.className = 'bwdd-bridge-info-link';
        infoLink.href = 'https://github.com/GolyBidoof/mokuro-bridge';
        infoLink.target = '_blank';
        infoLink.rel = 'noopener noreferrer';
        infoLink.textContent = 'Download mokuro-bridge ↗';
        bridgeInfoPop.append(infoTitle, mokuroSection, divider1, aboutSection, divider2,
            connSection, divider3, infoLink);
        infoDot.addEventListener('click', (e) => {
            e.stopPropagation();
            const open = bridgeInfoPop.hidden;
            if (open) placePopover(bridgeInfoPop, bridgeRow, 'left');
            else bridgeInfoPop.hidden = true;
            infoDot.setAttribute('aria-expanded', String(open));
        });

        // Anchor for the bridge status row and its "?" infobox, so the infobox
        // overlays just below the row instead of pushing content down.
        const bridgeAnchor = document.createElement('div');
        bridgeAnchor.className = 'bwdd-bridge-anchor';
        bridgeAnchor.append(bridgeRow, bridgeInfoPop);

        // Human-readable busy reason from the bridge's /health fields.
        function busyReason(info) {
            if (!info) return '';
            const stage = info.busy_stage;
            if (info.busy) {
                if (stage === 'uploading') return 'Uploading…';
                if (stage === 'ocr') return info.busy_detail || 'OCR running…';
                return info.busy_detail || 'Busy…';
            }
            return '';
        }
        async function updateBridgeDot() {
            if (!root.isConnected) return;   // panel closed, skip the tick entirely
            const ok = await bridgeHealth();
            let mokuroMissing = false;
            let mokuroDetailText = '';
            let bridgeBusy = false;
            let bridgeBusyStage = '';
            let bridgeBusyDetail = '';
            // The bridge answers /health even when mokuro isn't installed
            // (mokuro_installed:false), so that is "online but unusable for OCR",
            // not offline.
            if (ok && bridgeReachableNow) {
                const info = await refreshBridgeInfo().catch(() => null);
                const hasBridgePorts = !!(info && Array.isArray(info.fetchProxyPorts) && info.fetchProxyPorts.length);
                if (!hasBridgePorts) clearProxySource('bridge');
                // Take the proxy ports from this same /health payload: re-probing
                // separately fired two extra requests at a closed port every 10 s,
                // and the browser logs each refused connection to the console.
                try {
                    if (info && (Array.isArray(info.fetchUpstreams) || info.upstream)) {
                        setProxyUpstreams(info.fetchUpstreams, info.upstream);
                    }
                    addProxyPorts(info && info.fetchProxyPorts, 'bridge');
                } catch (e) {}
                mokuroMissing = !!(info && info.mokuro_installed === false);
                bridgeBusy = !!(info && info.busy);
                bridgeBusyStage = (info && info.busy_stage) || '';
                bridgeBusyDetail = (info && info.busy_detail) || '';
                if (info && info.mokuro_installed === true) {
                    mokuroDetailText = info.mokuro_version
                        ? 'Mokuro v' + info.mokuro_version + (info.mokuro_custom_fork ? ' (custom fork)' : '') + ' is installed on this machine.'
                        : 'Mokuro is installed on this machine.';
                    infoMokuro.classList.remove('missing');
                } else if (mokuroMissing) {
                    mokuroDetailText = 'Mokuro is not installed on this machine — OCR cannot run.';
                    infoMokuro.classList.add('missing');
                } else {
                    mokuroDetailText = '';
                    infoMokuro.classList.remove('missing');
                }
            } else {
                clearProxySource('bridge');
                mokuroDetailText = 'Bridge not reachable — start it to check the installed mokuro.';
                infoMokuro.classList.remove('missing');
            }
            infoMokuro.textContent = mokuroDetailText;
            bridgeOnline = ok && !mokuroMissing;
            if (ok && mokuroMissing) {
                // Bridge up but no OCR engine: block OCR, show a red alert.
                dot.className = 'bwdd-indicator-dot offline';
                mokuroAlert.style.display = 'block';
                mokuroAlert.textContent = 'Mokuro is not installed on this machine. ' +
                    'OCR cannot run until you install it — e.g. run “pip install mokuro” (or point ' +
                    'the bridge at your mokuro checkout) in the mokuro-bridge folder, then restart the bridge.';
            } else if (ok && bridgeBusy) {
                // Bridge is working (OCR/upload), amber dot + reason.
                dot.className = 'bwdd-indicator-dot busy';
                mokuroAlert.style.display = 'none';
            } else {
                dot.className = ok ? 'bwdd-indicator-dot online' : 'bwdd-indicator-dot';
                mokuroAlert.style.display = 'none';
            }
            if (ok && bridgeReachableNow && !mokuroMissing) {
                destWrap.style.display = 'flex';
                // Refresh the destination list only while idle: mid-run the
                // dropdown must keep exactly the pick the run started with
                // (the run reads it again at finalize time).
                if (!runBusy) { try { populateDestMethods(); } catch (e) {} }
                if (bridgeBusy) {
                    // While the bridge is busy, say what it's doing instead of
                    // re-asserting "online" (the dot is already amber).
                    bridgeText.textContent = 'Mokuro Bridge busy — ' + (busyReason({ busy: true, busy_stage: bridgeBusyStage, busy_detail: bridgeBusyDetail }) || 'working');
                    bridgeRow.title = 'mokuro-bridge: ' + (bridgeBusyDetail ? bridgeBusyDetail + ' · ' : '') + 'github.com/GolyBidoof/mokuro-bridge';
                } else {
                    // Idle: describe the destination from the panel's own pick, so
                    // the status line cannot contradict what finalize will use.
                    try {
                        const hasOptions = !!(destSelect.options && destSelect.options.length);
                        const method = hasOptions ? (destSelect.value || 'local') : 'local';
                        let desc, folder = null;
                        if (method === 'local') {
                            folder = localDirInput.value.trim() || (bridgeInfo && bridgeInfo.output_dir) || null;
                            desc = 'saving locally';
                        } else {
                            const opt = destSelect.selectedOptions && destSelect.selectedOptions[0];
                            const text = opt ? String(opt.textContent) : '';
                            const name = opt ? text.split(' — ')[0].trim() : method;
                            const m = text.match(/—\s*(.+)$/);
                            folder = m ? m[1].trim() : null;
                            desc = 'uploading via ' + (name || method);
                        }
                        bridgeText.textContent = 'Mokuro Bridge + Mokuro online — ' + desc;
                        bridgeRow.title = 'mokuro-bridge: ' + (folder ? 'writes to ' + folder + ' · ' : '') + 'github.com/GolyBidoof/mokuro-bridge';
                    } catch (e) {
                        bridgeText.textContent = 'Mokuro Bridge + Mokuro online';
                    }
                }
            } else {
                destWrap.style.display = 'none';
                bridgeText.textContent = ok
                    ? 'Mokuro Bridge is online but mokuro is missing — install it to enable OCR'
                    : 'Mokuro Bridge is not found on port 62642 — start it to enable OCR';
            }
            // OCR button + destination pickers derive from the run lock, so this
            // periodic tick can never re-enable them mid-run.
            setRunLock(runBusy);
            // Poll fast (1 s) while the bridge is busy - ours or background work
            // it reports via /health - so the UI notices the moment it goes idle;
            // otherwise settle to 10 s.
            bridgePollFast = !!(bridgeBusy || runBusy);
            laneBridgeOnline = bridgeReachableNow;
            renderCapabilities();
            scheduleBridgePoll();
        }

        let bridgeTimer = null;
        let bridgePollFast = false;
        function scheduleBridgePoll() {
            if (bridgeTimer) { clearTimeout(bridgeTimer); bridgeTimer = null; }
            bridgeTimer = setTimeout(updateBridgeDot, bridgePollFast ? 1000 : 10000);
        }
        updateBridgeDot();

        const statsEl = document.createElement('div');
        statsEl.className = 'bwdd-cards';

        // Run status area: live region so screen readers announce new
        // outcome/warning messages the moment they land here.
        const details = document.createElement('div');
        details.className = 'bwdd-hint-box';
        details.setAttribute('aria-live', 'polite');

        function mkBar(label, gradient, a11yLabel) {
            const row = document.createElement('div');
            row.className = 'bwdd-bar-row';
            const meta = document.createElement('div');
            meta.className = 'bwdd-bar-meta';
            const name = document.createElement('span');
            name.textContent = label;
            const rate = document.createElement('span');
            rate.className = 'bwdd-bar-rate';
            rate.textContent = '—';
            meta.append(name, rate);

            const track = document.createElement('div');
            track.className = 'bwdd-bar-track';
            // faint background segment (used by the Mokuro bar to show "received
            // but not yet OCR'd"); stays 0-width for the other bars
            const fillBg = document.createElement('div');
            fillBg.className = 'bwdd-bar-fill-bg';
            fillBg.style.width = '0%';
            track.appendChild(fillBg);
            const fill = document.createElement('div');
            fill.className = 'bwdd-bar-fill';
            fill.style.background = gradient;
            fill.setAttribute('role', 'progressbar');
            fill.setAttribute('aria-label', a11yLabel);
            fill.setAttribute('aria-valuemin', '0');
            fill.setAttribute('aria-valuemax', '100');
            fill.setAttribute('aria-valuenow', '0');
            track.appendChild(fill);

            row.append(meta, track);
            return { wrap: row, fill, fillBg, labRate: rate, labName: name };
        }

        const barDownload = mkBar('1. Network Fetch', 'linear-gradient(90deg, #10b981, #059669)', 'Download Progress');
        const barDescramble = mkBar('2. Tile Descramble', 'linear-gradient(90deg, #3b82f6, #1d4ed8)', 'Descramble Progress');
        const barMokuro = mkBar('3. Mokuro Bridge', 'linear-gradient(90deg, #f59e0b, #d97706)', 'OCR Pipeline Progress');
        const barUpload = mkBar('4. Upload', 'linear-gradient(90deg, #8b5cf6, #6d28d9)', 'Upload Progress');
        // What each bar counts (hover/AT hint; the Mokuro rate reads done/received/total,
        // and the faint amber underlay is pages the bridge received but hasn't OCR'd yet).
        barDownload.wrap.title = 'Pages fetched from ' + siteLabel() + '\u2019s CDN';
        barDescramble.wrap.title = 'Pages reassembled from their scrambled tiles';
        barMokuro.wrap.title = 'Pages OCR\u2019d / pages received by the bridge / total pages \u2014 faint amber = received but not yet OCR\u2019d';
        barUpload.wrap.title = 'Finished volume being stored or uploaded by the mokuro-bridge';

        const barWrap = document.createElement('div');
        barWrap.className = 'bwdd-bars';
        barWrap.setAttribute('role', 'region');
        barWrap.setAttribute('aria-label', 'Task Progress');
        barWrap.append(barDownload.wrap, barDescramble.wrap, barMokuro.wrap, barUpload.wrap);

        const btnRow = document.createElement('div');
        btnRow.className = 'bwdd-actions';

        const btnZip = document.createElement('button');
        btnZip.type = 'button';
        btnZip.className = 'bwdd-btn zip';
        btnZip.innerHTML = '<span>Save as ZIP</span><span class="bwdd-btn-sub">Pages bundled, ready to read offline</span>';

        const btnOcr = document.createElement('button');
        btnOcr.type = 'button';
        btnOcr.className = 'bwdd-btn ocr';
        btnOcr.innerHTML = '<span>Save and run through Mokuro</span><span class="bwdd-btn-sub">Run pages through the local Mokuro Bridge, then optionally upload</span>';
        const btnOcrTip = 'Mokuro = Japanese OCR (mokuro). Runs through the local mokuro-bridge app — see https://github.com/GolyBidoof/mokuro-bridge';
        btnOcr.title = btnOcrTip;

        btnRow.append(btnZip, btnOcr);

        // --- Archive name (above the download buttons) ---------------------
        // One compact row (label + textbox + "?" tooltip button) that sets the
        // name of the archive the buttons below generate: the .zip "Save as ZIP"
        // downloads, or the volume the bridge stores/uploads (.cbz) when OCR
        // runs. Auto-filled with this book's displayed title and refreshed when
        // the reader moves to another book, but a name the user typed is never
        // overwritten; empty = back to the default.
        const nameWrap = document.createElement('div');
        nameWrap.className = 'bwdd-name';
        const nameLabel = document.createElement('label');
        nameLabel.className = 'bwdd-dest-label';
        nameLabel.textContent = 'Archive name';
        nameLabel.setAttribute('for', 'bwdd-archive-name');
        const nameInput = document.createElement('input');
        nameInput.id = 'bwdd-archive-name';
        nameInput.type = 'text';
        nameInput.className = 'bwdd-dest-input';
        nameInput.autocomplete = 'off';
        nameInput.spellcheck = false;
        nameInput.placeholder = 'Auto-filled from this book';
        nameInput.setAttribute('aria-label', 'Archive name - the name of the generated download (leave empty to use this book\u2019s series + volume)');
        const nameInfoDot = document.createElement('button');
        nameInfoDot.type = 'button';
        nameInfoDot.className = 'bwdd-info-dot';
        nameInfoDot.setAttribute('aria-label', 'About the archive name field');
        nameInfoDot.setAttribute('aria-expanded', 'false');
        nameInfoDot.setAttribute('aria-controls', 'bwdd-archive-name-pop');
        nameInfoDot.title = 'What this field does';
        nameInfoDot.textContent = '?';
        // The popover overlays the buttons below rather than taking layout space.
        const namePop = document.createElement('div');
        namePop.className = 'bwdd-name-pop';
        namePop.id = 'bwdd-archive-name-pop';
        namePop.hidden = true;
        namePop.setAttribute('role', 'note');
        const namePopP1 = document.createElement('div');
        namePopP1.textContent = 'Name of the generated archive: the .zip \u201cSave as ZIP\u201d downloads, or the volume the Mokuro bridge stores/uploads when OCR runs.';
        const namePopP2 = document.createElement('div');
        namePopP2.textContent = 'Empty = this book\u2019s series + volume, exactly as the store writes it (e.g. \u2026 1\u5dfb, \uff08\uff11\uff09, \u2026 1).';
        const namePopP3 = document.createElement('div');
        namePopP3.textContent = 'ZIP pages sit flat inside the archive; OCR uploads still land under the series folder. Invalid file-name characters are stripped.';
        namePop.append(namePopP1, namePopP2, namePopP3);
        nameWrap.append(nameLabel, nameInput, nameInfoDot, namePop);
        // Click the "?" to toggle the popover; click elsewhere to dismiss it.
        function setArchivePop(open) {
            if (open) placePopover(namePop, nameWrap, 'right');
            else namePop.hidden = true;
            nameInfoDot.setAttribute('aria-expanded', String(open));
        }
        nameInfoDot.addEventListener('click', (e) => {
            e.stopPropagation();
            setArchivePop(namePop.hidden);
        });
        // Hoisted declaration so the panel's close button can detach it.
        function onNameDocClick(e) {
            if (!namePop.hidden && !nameWrap.contains(e.target)) setArchivePop(false);
        }
        document.addEventListener('click', onNameDocClick);

        // The default the field was last auto-filled with (null = never, or the
        // user has typed their own name since), so syncArchiveDefault can tell
        // "still showing the auto default" from "user's own text".
        let archiveAutoDefault = null;
        // Keep the field's default in sync with the book shown in the reader and
        // return the effective archive name for the current run (never empty):
        //   • Empty field → fill with this book's default.
        //   • Field still holding the previous auto default → swap in the new one.
        //   • Anything the user typed → never touched.
        // Self-corrects while the title arrives in stages (document.title first,
        // then the richer state.cti).
        function syncArchiveDefault(rawTitle) {
            const dflt = archiveDefaultName(rawTitle);
            const cur = nameInput.value;
            if (!cur.trim()) {
                if (dflt) { nameInput.value = dflt; archiveAutoDefault = dflt; }
                else { archiveAutoDefault = null; }
            } else if (archiveAutoDefault !== null && cur === archiveAutoDefault && dflt && dflt !== archiveAutoDefault) {
                nameInput.value = dflt;
                archiveAutoDefault = dflt;
            } else {
                archiveAutoDefault = (dflt && cur === dflt) ? dflt : null;
            }
            const safe = fsSafePath(nameInput.value.trim());
            if (safe) return safe;
            return dflt || fsSafePath(siteCid() || '') || 'book';
        }

        // --- Upload destination picker (OCR mode) ---
        // Lets the user choose where mokuro-bridge stores the finished volume, per
        // request: any configured remote method, or 'local' + a directory.
        const destWrap = document.createElement('div');
        destWrap.className = 'bwdd-dest';
        destWrap.style.display = 'none';   // shown only while the bridge is running
        const destLabel = document.createElement('label');
        destLabel.className = 'bwdd-dest-label';
        destLabel.textContent = 'Mokuro output destination';
        destLabel.setAttribute('for', 'bwdd-upload-method');
        const destSelect = document.createElement('select');
        destSelect.id = 'bwdd-upload-method';
        destSelect.className = 'bwdd-dest-select';
        destSelect.setAttribute('aria-label', 'Mokuro upload method');
        const localDirRow = document.createElement('div');
        localDirRow.className = 'bwdd-dest-localdir';
        localDirRow.style.display = 'none';
        const localDirLabel = document.createElement('label');
        localDirLabel.className = 'bwdd-dest-label';
        localDirLabel.textContent = 'Output folder (on this computer)';
        localDirLabel.setAttribute('for', 'bwdd-local-dir');
        const localDirInput = document.createElement('input');
        localDirInput.id = 'bwdd-local-dir';
        localDirInput.type = 'text';
        localDirInput.className = 'bwdd-dest-input';
        localDirInput.placeholder = 'absolute path on this computer — e.g. C:\\Users\\you\\manga or /home/you/manga';
        localDirInput.title = 'Where mokuro-bridge should write the finished volume. This is a path on the machine running the bridge (your computer).';
        // A web page cannot read your filesystem path via a folder picker
        // (showDirectoryPicker yields an opaque handle), so we fill the path from
        // the bridge's own configured output_dir and let you edit it freely.
        const localDirFill = document.createElement('button');
        localDirFill.type = 'button';
        localDirFill.className = 'bwdd-btn-fill';
        localDirFill.textContent = 'Use bridge default';
        localDirFill.addEventListener('click', async () => {
            const info = bridgeInfo || await refreshBridgeInfo();
            if (info && info.output_dir) localDirInput.value = info.output_dir;
        });
        const localDirWrap = document.createElement('div');
        localDirWrap.style.cssText = 'display:flex;gap:6px;align-items:center;';
        localDirWrap.append(localDirInput, localDirFill);
        localDirRow.append(localDirLabel, localDirWrap);
        const destHint = document.createElement('div');
        destHint.className = 'bwdd-dest-hint';
        destHint.style.display = 'none';
        destWrap.append(destLabel, destSelect, localDirRow, destHint);

        // Which method the user actually picked, kept separate from
        // destSelect.value because populateDestMethods() rebuilds the dropdown on
        // every 10s bridge-health tick: a refresh that cannot represent the
        // current pick must not forget it and fall back to the default forever.
        let userMethod = null;
        // A value is "usable" only when it maps to a configured, enabled option
        //, an unconfigured provider is selectable (to read its setup hint) but
        // must never be restored/seeded as the effective destination.
        const hasUsableOption = (v) => v != null && [...destSelect.options]
            .some(o => o.value === v && !o.disabled && !(o.dataset && o.dataset.unconfigured));

        async function populateDestMethods() {
            const methods = await fetchUploadMethods().catch(() => null);
            // A run may have started while this fetch was in flight: never
            // repopulate (and thereby change) the pick it will finalize with.
            if (runBusy) return;
            const prevValue = destSelect.value;   // keep the user's visible pick
            destSelect.textContent = '';
            let def = 'local';
            if (methods && Array.isArray(methods.methods) && methods.methods.length) {
                def = methods.upload_method_default || 'local';
                for (const m of methods.methods) {
                    const opt = document.createElement('option');
                    opt.value = m.id;
                    if (m.id === 'local') {
                        opt.textContent = 'Local folder' + (m.current_folder ? ' — ' + m.current_folder : '');
                    } else if (m.configured) {
                        opt.textContent = m.name + (m.current_folder ? ' — ' + m.current_folder : '');
                    } else {
                        // Unconfigured methods stay selectable so the user can read
                        // about them: choosing one shows the setup hint below and
                        // disables OCR until the provider is set up.
                        opt.textContent = m.name + ' — needs setup';
                        opt.dataset.unconfigured = '1';
                        opt.title = 'Not set up yet — enable it once in the mokuro-bridge terminal (from its folder): python server.py --setup-upload ' + (m.id || '');
                    }
                    destSelect.appendChild(opt);
                }
            } else {
                for (const [id, name] of [['local', 'Local (default output)'], ['mega', 'MEGA']]) {
                    const opt = document.createElement('option');
                    opt.value = id; opt.textContent = name;
                    destSelect.appendChild(opt);
                }
            }
            // Seed the remembered method from localStorage on the first
            // population; later rebuilds preserve the visible pick instead.
            if (!userMethod && !prevValue) {
                try {
                    const saved = localStorage.getItem('bwdd-upload-method');
                    if (saved && hasUsableOption(saved)) userMethod = saved;
                } catch (e) {}
            }
            // Pick the value to show after the rebuild:
            //   1. the current selection, if it still exists (a "needs setup" pick
            //      must survive a tick so its hint keeps showing),
            //   2. else the remembered usable method (seeded from localStorage),
            //   3. else the bridge's usable default, else 'local'.
            let picked = null;
            if (prevValue) {
                const stillThere = [...destSelect.options].some(o => o.value === prevValue);
                if (stillThere) picked = prevValue;
            }
            if (picked == null && userMethod && hasUsableOption(userMethod)) picked = userMethod;
            if (picked == null && hasUsableOption(def)) picked = def;
            if (picked == null) picked = 'local';
            destSelect.value = picked;
            onDestChange();
        }

        function rememberMethod(v) {
            userMethod = v;
            try { localStorage.setItem('bwdd-upload-method', v); } catch (e) {}
        }

        function onDestChange() {
            const v = destSelect.value || 'local';
            const showLocal = v === 'local';
            localDirRow.style.display = showLocal ? 'flex' : 'none';
            if (showLocal) {
                if (!localDirInput.value) {
                    const planDefault = bridgeInfo && bridgeInfo.output_dir || '';
                    if (planDefault) localDirInput.placeholder = 'default: ' + planDefault;
                }
            }
            updateDestHint();
            refreshOcrButton();
        }
        // Whether the destination currently chosen in the dropdown is one the
        // bridge hasn't been set up for yet.
        function selectedNeedsSetup() {
            const o = destSelect.selectedOptions && destSelect.selectedOptions[0];
            return !!(o && o.dataset && o.dataset.unconfigured);
        }
        // OCR button availability = not busy ∧ bridge online ∧ destination is
        // actually usable. While a not-yet-configured destination is selected
        // the button is disabled so a run can't start toward a dead end.
        function refreshOcrButton() {
            const blockedBySetup = selectedNeedsSetup();
            btnOcr.disabled = runBusy || !bridgeOnline || blockedBySetup;
            btnOcr.setAttribute('aria-disabled', String(btnOcr.disabled));
            btnOcr.title = blockedBySetup
                ? 'This destination is not set up yet — run the command below once, then it will be usable here.'
                : ((runBusy || bridgeOnline) ? btnOcrTip : 'Start the Mokuro Bridge to enable OCR');
        }
        // The setup hint is tied to the selection: it appears only when the
        // chosen destination isn't configured yet (and the OCR button stays
        // disabled until it is). Once the provider is set up, the next health
        // tick lists it as configured and the hint disappears.
        function updateDestHint() {
            const selOpt = destSelect.selectedOptions && destSelect.selectedOptions[0];
            if (!selOpt || !selOpt.dataset || !selOpt.dataset.unconfigured) {
                destHint.style.display = 'none';
                return;
            }
            destHint.style.display = 'block';
            destHint.textContent = '';
            destHint.appendChild(document.createTextNode('This destination needs one-time setup in the bridge terminal: '));
            const code = document.createElement('code');
            code.textContent = 'python server.py --setup-upload ' + (selOpt.value || '');
            destHint.appendChild(code);
            destHint.appendChild(document.createTextNode('  (from the mokuro-bridge folder)'));
        }
        destSelect.addEventListener('change', () => { rememberMethod(destSelect.value); onDestChange(); });
        localDirInput.addEventListener('change', () => { try { localStorage.setItem('bwdd-local-dir', localDirInput.value); } catch (e) {} });
        try { const saved = localStorage.getItem('bwdd-local-dir'); if (saved) localDirInput.value = saved; } catch (e) {}
        populateDestMethods();
        // --- Run-state lock --------------------------------------------------
        // While a run is in progress the action buttons and the destination
        // section are disabled: no second download, and no changing the
        // destination an OCR run re-reads at finalize time.
        let bridgeOnline = false;   // last known bridge /health result
        let runBusy = false;        // a download/OCR run is in progress

        function setRunLock(busy) {
            runBusy = busy;
            btnZip.disabled = busy;
            btnZip.setAttribute('aria-disabled', String(busy));
            // OCR availability folds in the destination-setup state too, see
            // refreshOcrButton (kept in sync on every selection change).
            refreshOcrButton();
            const destLocked = busy || !bridgeOnline;
            destSelect.disabled = destLocked;
            localDirInput.disabled = destLocked;
            localDirFill.disabled = destLocked;
            nameInput.disabled = busy;
            destWrap.classList.toggle('bwdd-dest-locked', busy);
            if (busy) {
                destWrap.setAttribute('aria-busy', 'true');
                destWrap.title = 'Locked while a download or OCR run is in progress';
            } else {
                destWrap.removeAttribute('aria-busy');
                destWrap.title = '';
            }
            // Closing or flapping the panel mid-run would orphan the pipeline
            // (auth timers, OCR polls, the finalize stream) that keeps posting
            // into a detached DOM, hold both header buttons until it finishes.
            closeBtn.disabled = busy;
            flapBtn.disabled = busy;
            if (busy) {
                closeBtn.title = 'Closes after the run finishes';
                flapBtn.title = 'Available after the run finishes';
            } else {
                closeBtn.title = 'Close panel';
                flapBtn.title = 'Slide the panel away to the right edge of the screen';
            }
        }

        // Post-run actions, "Open Reader Mokuro" + "Open stored file / Copy path":
        // one quiet row of secondary (ghost) buttons after a successful OCR run,
        // each spanning the row when the other has nothing to offer (grid auto-fit).
        const postRunRow = document.createElement('div');
        postRunRow.className = 'bwdd-reader-row';
        postRunRow.style.display = 'none';
        const btnReader = document.createElement('button');
        btnReader.type = 'button';
        btnReader.className = 'bwdd-ghost-btn';
        btnReader.textContent = 'Open Reader Mokuro';
        btnReader.setAttribute('aria-label', 'Open Reader Mokuro in a new tab');
        const btnStored = document.createElement('button');
        btnStored.type = 'button';
        btnStored.className = 'bwdd-ghost-btn';
        btnStored.setAttribute('aria-label', 'Open stored file');
        postRunRow.append(btnReader, btnStored);
        let readerReady = false;
        let storedReady = false;
        function syncPostRunRow() {
            btnReader.style.display = readerReady ? '' : 'none';
            btnStored.style.display = storedReady ? '' : 'none';
            postRunRow.style.display = (readerReady || storedReady) ? 'grid' : 'none';
        }
        function showReaderButton(result) {
            btnReader.onclick = () => {
                const a = document.createElement('a');
                a.href = readerJumpUrl(result);
                a.target = '_blank';
                a.rel = 'noopener noreferrer';
                a.style.display = 'none';
                document.body.appendChild(a);
                a.click();
                a.remove();
            };
            readerReady = true;
            syncPostRunRow();
        }
        function hideReaderButton() {
            btnReader.onclick = null;
            readerReady = false;
            syncPostRunRow();
        }
        function showStoredButton(result) {
            const target = storedOpenTarget(result);
            if (target) {
                const isCbz = /\.cbz$/i.test(target.file || '');
                btnStored.textContent = isCbz ? 'Open stored file (.cbz)' : 'Open stored file';
                btnStored.setAttribute('aria-label', isCbz
                    ? 'Open the stored .cbz file in a new tab'
                    : 'Open the stored file in a new tab');
                btnStored.title = target.url;
                btnStored.onclick = () => {
                    const a = document.createElement('a');
                    a.href = target.url;
                    a.target = '_blank';
                    a.rel = 'noopener noreferrer';
                    a.style.display = 'none';
                    document.body.appendChild(a);
                    a.click();
                    a.remove();
                };
            } else {
                const method = result && result.method;
                const isLocal = !method || method === 'local';
                const copyText = isLocal
                    ? (result && (result.output_dir || result.staging))
                    : (result && (result.remote_path || result.mega_path || result.staging));
                const mainLabel = isLocal ? 'Copy local folder path' : 'Copy destination path';
                const a11yLabel = mainLabel + ' to the clipboard';
                btnStored.textContent = mainLabel;
                btnStored.setAttribute('aria-label', a11yLabel);
                btnStored.title = copyText || '';
                btnStored.onclick = () => {
                    const text = copyText || 'about:blank';
                    try { navigator.clipboard.writeText(text); } catch (e) {}
                    btnStored.textContent = 'Path copied ✓';
                    btnStored.setAttribute('aria-label', 'Path copied to the clipboard');
                    setTimeout(() => {
                        btnStored.textContent = mainLabel;
                        btnStored.setAttribute('aria-label', a11yLabel);
                    }, 1500);
                };
            }
            storedReady = true;
            syncPostRunRow();
        }
        function hideStoredButton() {
            btnStored.onclick = null;
            storedReady = false;
            syncPostRunRow();
        }

        // Two-column layout: download & bridge controls on the left, reading stats
        // on the right. The stats column mounts only once the first card lands in
        // statsEl; until then the panel is a single controls column.
        // ---- pre-flight readout ------------------------------------------
        // These numbers live in the bridge row's "?" popover, not the panel body:
        // they matter before a run, but not often enough to earn permanent space.
        function renderCapabilities() {
            const c = capabilitySummary();
            connSection.classList.toggle('on', c.bridgeOnline);
            connSection.classList.toggle('off', !c.bridgeOnline);
            // "no bridge", not "page only": the count can still include the GM and
            // trailing-dot lanes, so naming just the page lane would be wrong.
            const speed = c.bridgeOnline ? c.ports + ' ports'
                : (c.ports ? 'bridge offline' : 'no bridge');
            connNumbers.textContent = speed + ' · ' + c.effectiveSockets +
                ' sockets · ' + c.workers + ' workers';

            let explain;
            if (c.bridgeOnline) {
                explain = 'mokuro-bridge is serving ' + c.ports + ' extra local ports. The browser ' +
                    'allows 6 connections per origin, and every port counts as its own origin, so ' +
                    'this run has up to ' + c.sockets + ' network sockets instead of ' +
                    c.withoutBridge + '. Up to ' + c.decodePages + ' pages decode concurrently; ' +
                    'the fetch window is bounded separately to avoid retaining the whole volume.';
            } else if (c.ports) {
                explain = 'mokuro-bridge answered earlier (' + c.ports + ' ports) but is not ' +
                    'reachable now, so this run would use ' + c.effectiveSockets + ' connections. ' +
                    'Restart it to get the extra ports back.';
            } else {
                // Quote the real count, not "6": the GM and trailing-dot lanes
                // already add more than the page's own 6.
                explain = 'mokuro-bridge is not running, so this run uses ' + c.effectiveSockets +
                    ' browser connections. Starting it adds its advertised local ports, ' +
                    'worth up to six connections each. Downloads work the same either way.';
            }
            connBody.textContent = explain + ' ' + c.workers + ' Web Workers unscramble ' +
                workerBatchSize(IMAGE_CODEC.type) + ' page each concurrently as they arrive; that number follows your CPU, not the bridge.';
        }

        // ---- page image format (advanced, collapsed) ----------------------
        const fmtDetails = document.createElement('details');
        fmtDetails.className = 'bwdd-fmt';
        const fmtSummary = document.createElement('summary');
        fmtSummary.className = 'bwdd-fmt-summary';
        const fmtBody = document.createElement('div');
        fmtBody.className = 'bwdd-dest';

        function labelledSelect(labelText, id, options, ariaLabel) {
            const row = document.createElement('div');
            row.className = 'bwdd-opt-row';
            const lab = document.createElement('label');
            lab.className = 'bwdd-dest-label';
            lab.textContent = labelText;
            lab.setAttribute('for', id);
            const sel = document.createElement('select');
            sel.id = id;
            sel.className = 'bwdd-dest-select';
            sel.setAttribute('aria-label', ariaLabel || labelText);
            for (const [v, text] of options) {
                const o = document.createElement('option');
                o.value = v;
                o.textContent = text;
                sel.appendChild(o);
            }
            row.append(lab, sel);
            return { row, sel };
        }

        const FORMAT_LABELS = {
            jpeg: 'JPEG', webp: 'WebP', lossless: 'Lossless', png: 'PNG',
        };
        const fmtCtl = labelledSelect('Format', 'bwdd-image-format', [
            ['jpeg', 'JPEG (smallest)'],
            ['webp', 'WebP (smaller, slower)'],
            ['lossless', 'Lossless (perfect copy)'],
            ['png', 'PNG (largest)'],
        ], 'Page image format');
        const qCtl = labelledSelect('Quality', 'bwdd-image-quality', [
            ['0.95', 'Highest'], ['0.92', 'High (default)'],
            ['0.85', 'Balanced'], ['0.75', 'Small'],
        ], 'Page image quality');
        const fmtNote = document.createElement('div');
        fmtNote.className = 'bwdd-caps-note';

        function onFormatChange(save) {
            if (save !== false) {
                try {
                    localStorage.setItem('bwddImageFormat', fmtCtl.sel.value);
                    localStorage.setItem('bwddImageQuality', qCtl.sel.value);
                } catch (e) {}
            }
            const c = refreshImageCodec();
            // Quality does nothing for the lossless settings, so hide it rather
            // than offer a control with no effect.
            qCtl.row.style.display = c.lossless ? 'none' : 'flex';
            fmtSummary.textContent = 'Image format · ' + FORMAT_LABELS[c.fmt] +
                (c.lossless ? '' : ' q' + c.quality);
            fmtNote.textContent = c.lossless
                ? 'Lossless keeps every pixel the CDN sent. Often smaller than JPEG on line art, much larger on photo pages.'
                : 'Pages are re-encoded from the CDN\u2019s own JPEG, so this is a second generation.';
            renderCapabilities();
        }

        // Reflect whatever is already configured (console or a previous visit).
        {
            const wantedFmt = IMAGE_CODEC.fmt;
            if (![...fmtCtl.sel.options].some(o => o.value === wantedFmt)) {
                const o = document.createElement('option');
                o.value = wantedFmt;
                o.textContent = wantedFmt;
                fmtCtl.sel.appendChild(o);
            }
            fmtCtl.sel.value = wantedFmt;
            const wantedQ = String(IMAGE_CODEC.quality);
            if (![...qCtl.sel.options].some(o => o.value === wantedQ)) {
                const o = document.createElement('option');
                o.value = wantedQ;
                o.textContent = wantedQ;
                qCtl.sel.appendChild(o);
            }
            qCtl.sel.value = wantedQ;
        }
        fmtCtl.sel.addEventListener('change', () => onFormatChange(true));
        qCtl.sel.addEventListener('change', () => onFormatChange(true));
        fmtBody.append(fmtCtl.row, qCtl.row, fmtNote);
        fmtDetails.append(fmtSummary, fmtBody);
        onFormatChange(false);

        const colMain = document.createElement('div');
        colMain.className = 'bwdd-col bwdd-col-main';
        colMain.append(bridgeAnchor, mokuroAlert, destWrap, nameWrap, fmtDetails, btnRow, barWrap, details, postRunRow);

        const colStats = document.createElement('div');
        colStats.className = 'bwdd-col bwdd-col-stats';
        colStats.append(statsEl);

        const colSep = document.createElement('div');
        colSep.className = 'bwdd-col-sep';

        // Mount the stats column (+ separator) and widen the panel to its
        // two-column size the moment the first card lands.
        function mountStatsColumn() {
            const manual = parseFloat(root.style.width);
            const manualWide = isFinite(manual) && manual >= 620;
            body.append(colSep, colStats);
            root.classList.add('bwdd-stats-visible');
            // A manual width only sticks once it is wide enough for two columns;
            // otherwise fall back to the auto two-column width.
            if (!manualWide) root.style.width = '';
        }
        let statsMounted = false;
        const statsObs = new MutationObserver(() => {
            if (statsMounted || !statsEl.childElementCount) return;
            statsMounted = true;
            statsObs.disconnect();
            mountStatsColumn();
        });
        statsObs.observe(statsEl, { childList: true });
        if (statsEl.childElementCount) { statsMounted = true; mountStatsColumn(); }   // safety net

        body.append(colMain);
        root.append(head, body);
        document.documentElement.appendChild(root);
        // updateBridgeDot() ran above, before root was connected, and bailed at
        // the `!root.isConnected` guard, so refresh it now instead of waiting for
        // the first 10 s interval tick.
        try { updateBridgeDot(); } catch (e) {}

        // "Flap": slide the whole panel off the right edge of the screen. A
        // small tab stays docked on the right edge to bring it back.
        const edgeTab = document.createElement('button');
        edgeTab.type = 'button';
        edgeTab.className = 'bwdd-edge-tab';
        edgeTab.setAttribute('aria-label', 'Show the ' + sitePanelTitle() + ' panel');
        edgeTab.title = 'Show the ' + sitePanelTitle() + ' panel';
        edgeTab.textContent = '\u00AB';   // fancy "<<", pull the panel back in from the right
        edgeTab.style.display = 'none';
        document.documentElement.appendChild(edgeTab);

        function flapOut() {
            if (edgeTab.style.display === 'flex') return;   // already away
            const r = root.getBoundingClientRect();
            // Push the panel fully past the right edge. Its left/top position is
            // untouched, so clearing the transform returns it exactly where it was.
            const shift = Math.max(24, Math.ceil(window.innerWidth - r.left) + 4);
            root.style.transform = 'translateX(' + shift + 'px)';
            root.classList.add('bwdd-flapped');
            root.setAttribute('aria-hidden', 'true');
            // inert takes every control out of the tab order / a11y tree, so a
            // keyboard user can't Tab into invisible controls (aria-hidden
            // alone does not do that).
            root.inert = true;
            // Anchor the restore tab to the panel's own vertical span, so a
            // bottom-docked panel leaves its tab near the bottom edge.
            const tabH = 76;   // .bwdd-edge-tab height
            const vh = window.innerHeight || document.documentElement.clientHeight || 800;
            const tabTop = Math.max(0, Math.min(r.top + (r.height - tabH) / 2, vh - tabH - 8));
            edgeTab.style.top = tabTop + 'px';
            edgeTab.style.display = 'flex';
            flapBtn.setAttribute('aria-expanded', 'false');
            flapBtn.setAttribute('aria-label', 'Show the panel (from the right edge)');
            try { edgeTab.focus(); } catch (e) {}
        }
        function flapIn() {
            if (edgeTab.style.display !== 'flex') return;
            root.classList.remove('bwdd-flapped');
            root.style.transform = '';
            root.removeAttribute('aria-hidden');
            root.inert = false;   // restore tab order + focusability
            edgeTab.style.display = 'none';
            flapBtn.setAttribute('aria-expanded', 'true');
            flapBtn.setAttribute('aria-label', 'Hide the panel to the right edge');
            try { flapBtn.focus(); } catch (e) {}
        }
        edgeTab.addEventListener('click', () => flapIn());
        flapBtn.onclick = () => flapOut();

        // --- Manual resize (corner handle) + remembered width -------------
        const resizeHandle = document.createElement('div');
        resizeHandle.className = 'bwdd-resize';
        resizeHandle.setAttribute('aria-hidden', 'true');
        resizeHandle.setAttribute('title', 'Drag to resize the panel');
        root.appendChild(resizeHandle);

        let resizing = false;
        let resizeStartX = 0, resizeStartY = 0;
        let resizeStartW = 0, resizeStartH = 0;
        function resizeMinW() {
            return root.classList.contains('bwdd-stats-visible') ? 620 : 360;
        }
        function resizeMinH() { return 120; }
        function persistPanelSize() {
            try {
                const r = root.getBoundingClientRect();
                localStorage.setItem(PANEL_WIDTH_KEY, String(Math.round(r.width)));
                localStorage.setItem(PANEL_HEIGHT_KEY, String(Math.round(r.height)));
            } catch (e) {}
        }
        resizeHandle.addEventListener('pointerdown', (e) => {
            if (e.pointerType === 'mouse' && e.button !== 0) return;
            e.preventDefault();
            e.stopPropagation();
            const r = root.getBoundingClientRect();
            // Anchor by the top-left so the bottom-right corner follows the
            // pointer while resizing (works for both docked and dragged states).
            root.style.left = r.left + 'px';
            root.style.top = r.top + 'px';
            root.style.right = 'auto';
            resizing = true;
            resizeStartX = e.clientX; resizeStartY = e.clientY;
            resizeStartW = r.width;   resizeStartH = r.height;
            try { resizeHandle.setPointerCapture(e.pointerId); } catch (err) {}
        });
        resizeHandle.addEventListener('pointermove', (e) => {
            if (!resizing) return;
            const vw = window.innerWidth || 1200;
            const vh = window.innerHeight || 800;
            const left = root.getBoundingClientRect().left;
            const top = root.getBoundingClientRect().top;
            const minW = resizeMinW();
            const maxW = Math.max(minW, Math.min(1200, vw - left - 12));
            const w = Math.max(minW, Math.min(maxW, resizeStartW + (e.clientX - resizeStartX)));
            root.style.width = Math.round(w) + 'px';
            // The panel is top-anchored, so growing downward is what the user
            // expects; clamp to the viewport too.
            const minH = resizeMinH();
            const maxH = Math.max(minH, Math.min(1000, vh - top - 12));
            const h = Math.max(minH, Math.min(maxH, resizeStartH + (e.clientY - resizeStartY)));
            root.style.height = Math.round(h) + 'px';
        });
        resizeHandle.addEventListener('pointerup', () => { resizing = false; persistPanelSize(); });
        resizeHandle.addEventListener('pointercancel', () => { resizing = false; });
        resizeHandle.addEventListener('lostpointercapture', () => { if (resizing) { resizing = false; persistPanelSize(); } });

        try {
            const savedW = parseInt(localStorage.getItem(PANEL_WIDTH_KEY) || '', 10);
            if (isFinite(savedW) && savedW > 0) root.style.width = Math.min(Math.max(savedW, 300), 1200) + 'px';
        } catch (e) {}
        try {
            const savedH = parseInt(localStorage.getItem(PANEL_HEIGHT_KEY) || '', 10);
            if (isFinite(savedH) && savedH > 0) root.style.height = Math.min(Math.max(savedH, 120), 1000) + 'px';
        } catch (e) {}

        try {
            const savedPos = JSON.parse(localStorage.getItem(PANEL_POS_KEY) || 'null');
            if (savedPos && typeof savedPos.x === 'number' && typeof savedPos.y === 'number') {
                root.style.left = clampPanelX(savedPos.x) + 'px';
                root.style.top = clampPanelY(savedPos.y) + 'px';
                root.style.right = 'auto';
            }
        } catch (e) {}
        try { if (localStorage.getItem(PANEL_COLLAPSED_KEY) === '1') setCollapsed(true); } catch (e) {}

        // Draggable Functionality (pointer + keyboard; Esc collapses)
        let dragging = false;
        let dragPointerId = null;
        let pos = { x: 0, y: 0 };
        function clampPanelX(x) { return Math.max(0, Math.min(x, Math.max(0, (window.innerWidth || 1200) - 60))); }
        function clampPanelY(y) { return Math.max(0, Math.min(y, Math.max(0, (window.innerHeight || 800) - 70))); }
        function savePanelPos() {
            try {
                const r = root.getBoundingClientRect();
                localStorage.setItem(PANEL_POS_KEY, JSON.stringify({ x: r.left, y: r.top }));
            } catch (e) {}
        }
        function applyDragPos(clientX, clientY) {
            root.style.left = clampPanelX(clientX - pos.x) + 'px';
            root.style.top = clampPanelY(clientY - pos.y) + 'px';
            root.style.right = 'auto';
        }
        // Pointer events cover mouse, touch and pen (with capture so the drag keeps
        // tracking even when the pointer leaves the header).
        head.addEventListener('pointerdown', (e) => {
            if (e.pointerType === 'mouse' && e.button !== 0) return;
            if (e.target.closest('button, a')) return;
            dragging = true;
            dragPointerId = e.pointerId;
            pos.x = e.clientX - root.offsetLeft;
            pos.y = e.clientY - root.offsetTop;
            try { head.setPointerCapture(e.pointerId); } catch (err) {}
            e.preventDefault();
        });
        head.addEventListener('pointermove', (e) => {
            if (!dragging || dragPointerId !== e.pointerId) return;
            applyDragPos(e.clientX, e.clientY);
        });
        function stopDrag(e) {
            if (!dragging || (e && dragPointerId != null && e.pointerId !== dragPointerId)) return;
            dragging = false;
            dragPointerId = null;
            savePanelPos();
        }
        head.addEventListener('pointerup', stopDrag);
        head.addEventListener('pointercancel', stopDrag);
        head.addEventListener('lostpointercapture', () => {
            if (dragging) savePanelPos();
            dragging = false;
            dragPointerId = null;
        });
        // The panel deliberately does NOT capture arrow keys: the viewer uses
        // Left/Right to flip pages, so arrow handling must never be eaten or
        // preventDefault'ed while the panel holds focus. Reposition by dragging the
        // header, resize with the corner grip.

        // Keyboard shortcut: Escape toggles collapse. Named so the close button can
        // remove it: a closed panel must not keep a window-level listener alive.
        function onPanelKeydown(e) {
            if (e.key !== 'Escape') return;
            // An open archive-name popover is closed by Esc first, then a second
            // Esc collapses the panel as usual.
            if (!namePop.hidden) { setArchivePop(false); return; }
            // don't hijack Esc while the user is typing in a form control
            const t = e.target;
            if (t && (t.tagName === 'INPUT' || t.tagName === 'TEXTAREA' || t.tagName === 'SELECT' || t.isContentEditable)) return;
            if (document.contains(root) && !e.defaultPrevented) {
                setCollapsed(!root.classList.contains('collapsed'));
            }
        }
        window.addEventListener('keydown', onPanelKeydown);

        // Exposed last: this names elements (fmtCtl/qCtl) created further down, so
        // publishing it any earlier hits the TDZ and exports nothing.
        if (BWDD_DEBUG) {
            try {
                window.__bwddUI = Object.assign(window.__bwddUI || {}, {
                    populateDestMethods, onDestChange,
                    renderCapabilities, capabilitySummary, workerPoolSize, discoverProxyPorts,
                    fmtSelect: fmtCtl.sel, qSelect: qCtl.sel,
                    // programmatic control, for tests and console use
                    setImageFormat(fmt, quality) {
                        if (fmt) fmtCtl.sel.value = fmt;
                        if (quality != null) qCtl.sel.value = String(quality);
                        onFormatChange(true);
                        return IMAGE_CODEC;
                    },
                });
            } catch (e) { try { console.error('[bwdd] UI export failed:', safeLogText(e)); } catch (e2) {} }
        }
        return { root, details, statsEl, barWrap, barDownload, barDescramble, barMokuro, barUpload, btnZip, btnOcr, destSelect, localDirInput, destHint, populateDestMethods, setRunLock, showReaderButton, hideReaderButton, showStoredButton, hideStoredButton, syncArchiveDefault };
    }

    // Three-value Mokuro progress: done / received / total.
    // fillBg (faint) = pages received by the bridge; fill (solid) = pages
    // actually OCR'd. No flicker, every update sets all three consistently.
    function updateMokuroBar(bar, done, received, total) {
        if (!bar || !bar.fill) return;
        const t = total || 1;
        const r = Math.max(0, Math.min(received || 0, t));
        const d = Math.max(0, Math.min(done || 0, r));
        if (bar.fillBg) bar.fillBg.style.width = Math.round((r / t) * 100) + '%';
        bar.fill.style.width = Math.round((d / t) * 100) + '%';
        bar.fill.setAttribute('aria-valuenow', String(Math.round((d / t) * 100)));
        bar.fill.setAttribute('aria-valuetext', d + ' of ' + t + ' pages OCR\u2019d, ' + r + ' received by the bridge');
        bar.labRate.textContent = d + '/' + r + '/' + t;
    }

    function setBar(bar, pct, text) {
        if (!bar) return;
        const p = Math.max(0, Math.min(100, Math.round(pct || 0)));
        bar.fill.style.width = p + '%';
        bar.fill.setAttribute('aria-valuenow', String(p));
        bar.fill.setAttribute('aria-valuetext', `${p}% complete`);
        if (text != null) bar.labRate.textContent = text;
    }
    // Build (but don't insert) the collapsible raw-error block; returns null
    // when there is nothing to show. Both setRunDetails and the success paths
    // use it so recovered/retried errors surface without dominating the copy.
    function makeTechDetails(rawLines, label) {
        const lines = (rawLines || []).filter(Boolean);
        const capped = lines.slice(0, 15);
        const overflow = lines.length - capped.length;
        if (!capped.length) return null;
        const det = document.createElement('details');
        const sum = document.createElement('summary');
        sum.textContent = (label || 'Technical details') + ' (' + capped.length + (overflow ? '+' : '') + ')';
        const pre = document.createElement('pre');
        pre.textContent = capped.join('\n') + (overflow > 0 ? '\n\u2026 and ' + overflow + ' more' : '');
        det.append(sum, pre);
        return det;
    }
    // Show a run outcome in the status area: a plain summary plus (when the
    // caller has raw per-page error lines) a collapsible "technical details"
    // block so the raw internals never dominate the message.
    function setRunDetails(el, summary, rawLines) {
        if (!el) return;
        el.textContent = '';
        el.appendChild(document.createTextNode(summary));
        const det = makeTechDetails(rawLines);
        if (det) el.appendChild(det);
    }
    // Append diagnostics to an already-set status line (used when a run fully
    // succeeded but some pages needed retries, nothing silently swallowed).
    function appendRunDetails(el, rawLines, label) {
        if (!el) return;
        const det = makeTechDetails(rawLines, label);
        if (det) el.appendChild(det);
    }
    function showBars(ui) {
        ui.barWrap.style.display = 'flex';
        ui.barDownload.wrap.style.display = 'flex';
        ui.barDescramble.wrap.style.display = 'flex';
        setBar(ui.barDownload, 0, '0%');
        setBar(ui.barDescramble, 0, '0%');
    }

    async function uploadCoverEarly(opts) {
        const { ui, barUpload, feed, mokuroSessionId, safeTitle, blob } = opts;
        if (!mokuroSessionId || !blob) return null;
        const plan = await resolveUploadChoice(ui).catch(() => ({ method: null, label: null, localDir: null }));
        const coverName = (safeTitle || 'volume') + '.webp';
        try {
            barUpload.labName.textContent = '4. ' + (plan.method === 'local' ? 'Store' : 'Upload');
            barUpload.wrap.style.display = 'flex';
            // Seed the 1-file plan up front so the bar reads "1/1 · 0%" from
            // the very first moment (no bare "0%" without a file count).
            if (feed.seed) feed.seed([{ file: coverName, total_bytes: blob.size }]);
            feed({ file: coverName, currentBytes: 0, totalBytes: blob.size, percent: 0 });
            const res = await mokuroUploadCover(mokuroSessionId, blob, { method: plan.method || null, localDir: plan.localDir });
            feed({ file: res && res.file ? res.file : coverName, currentBytes: res && res.size ? res.size : blob.size, totalBytes: res && res.size ? res.size : blob.size, percent: 100 });
            return res;
        } catch (e) {
            // A failed early cover must never break the download/OCR run.
            if (BWDD_DEBUG) console.warn('[bwdd] Early cover upload skipped:', safeLogText(e && e.message || e));
            return null;
        }
    }

    // Finalize phase shared by the trial and full OCR pipelines (kept in one
    // place so the two paths can never drift apart again): ask the bridge to
    // finalize the session (store locally or upload), stream live byte/percent
    // progress into the Store/Upload bar via the NDJSON frames, and keep the
    // Mokuro bar polled until the stream closes. Returns { result, plan }.
    async function finalizeOcrSession(mokuroSessionId, ui, barUpload, barMokuro, total, sharedFeed, options = {}) {
        const plan = await resolveUploadChoice(ui).catch(() => ({ method: null, label: null, localDir: null }));
        // The 4th stage only uploads when the destination is remote, so name the
        // bar honestly. If the early cover upload already started this feed, keep
        // the visible progress and just seed the rest.
        barUpload.labName.textContent = '4. ' + (plan.method === 'local' ? 'Store' : 'Upload');
        const uploadFeed = sharedFeed || makeUploadBarUpdater(barUpload);
        if (!sharedFeed || !sharedFeed.hasAny || !sharedFeed.hasAny()) {
            barUpload.wrap.style.display = 'none';
            setBar(barUpload, 0, '0%');
        }
        const result = await new Promise((resolve, reject) => {
            const fp = mokuroFinalize(mokuroSessionId, { method: plan.method || null, localDir: plan.localDir }, (stage, msg) => {
                if (stage === 'upload_progress' || stage === 'upload') barUpload.wrap.style.display = 'flex';
                // The initial "upload" frame announces every file + size, so
                // pre-size the bar before the first byte arrives.
                if (stage === 'upload' && msg && Array.isArray(msg.files) && uploadFeed.seed) {
                    uploadFeed.seed(msg.files);
                }
                // Keep the file count + total size on the bar when done.
                if (stage === 'done' && uploadFeed.summary) {
                    const s = uploadFeed.summary();
                    if (barUpload.wrap.style.display === 'flex' && s.total > 0) {
                        setBar(barUpload, 100, s.done + '/' + s.total + ' · 100% · ' + fmtBytes(s.sumTot) + ' / ' + fmtBytes(s.sumTot));
                    } else if (barUpload.wrap.style.display === 'flex') {
                        setBar(barUpload, 100, '100%');
                    }
                }
                if (options.automation) reportRunProgress(options, 'finalize', { stage: stage || null });
            }, uploadFeed);
            // Poll the bridge's OCR status ~2.5/s so the Mokuro bar keeps moving
            // while the finalize stream is open; the bridge also publishes live
            // upload progress to the same /status endpoint, which keeps the bar
            // moving even with older bridges that buffer their NDJSON frames.
            // Headless callers can opt out.
            let poll = null;
            if (options.pollBridgeStatus !== false) {
                poll = setInterval(async () => {
                    try {
                        const st = await mokuroStatus(mokuroSessionId);
                        if (!st) return;
                        updateMokuroBar(barMokuro, st.pages_ocr_done ?? 0, st.pages_received ?? 0, total);
                        const up = st.upload;
                        if (up && (up.active === true || (up.current_bytes || 0) > 0 || (up.percent || 0) > 0)) {
                            barUpload.wrap.style.display = 'flex';
                            uploadFeed({
                                file: up.file || '',
                                currentBytes: up.current_bytes || 0,
                                totalBytes: up.total_bytes || 0,
                                percent: up.percent,
                                speed: up.speed_human || null,
                            });
                        }
                    } catch (e) {}
                }, 400);
            }
            if (poll && options.registerRunCleanup) {
                options.registerRunCleanup(() => { if (poll) { clearInterval(poll); poll = null; } });
            }
            fp.then(r => { if (poll) { clearInterval(poll); poll = null; } resolve(r); },
                   e => { if (poll) { clearInterval(poll); poll = null; } reject(e); });
        });
        return { result, plan };
    }

    // =====================================================================
    // Shared run harness
    // =====================================================================
    // Driven by the CMOA and ebookjapan pipelines; BookWalker's full and trial
    // pipelines never call it and keep their own plumbing. It owns everything the
    // user can see and everything the Mokuro bridge is told - same bars, same
    // progress reporting, same session/finalize conversation, same ZIP assembly
    // and naming - so the stores cannot drift apart.
    //
    // What stays site-specific is only *how* pages are fetched: BookWalker's
    // lane/worker/descramble engine and CMOA's token/quality/quality-blacklist
    // retry loop have nothing in common, and forcing them through one generic
    // fetch loop would mean rewriting the tuned path that already works.
    //
    // Usage:
    //   const H = createRunHarness(ui, mode, options, { title, archiveName, cid });
    //   await H.mokuro.open();          // OCR runs only
    //   H.showBars();
    //   ...per page: H.notePage(idx, blob, crc) / H.noteFailure(idx, message)
    //   await H.finishZip();  |  await H.finishOcr();
    //   return H.outcome(missing === 0);
    //   ...always: await H.cleanup()
    function createRunHarness(ui, mode, options, meta) {
        options = options || {};
        meta = meta || {};
        const { details, barWrap, barDownload, barDescramble, barMokuro, barUpload } = ui;
        const runResult = options.result || null;
        const errors = options.errors || (runResult ? runResult.errors : []);
        const okIdx = new Set();
        const failedIdx = new Set();
        const zip = mode === 'zip' ? { entries: [] } : null;
        const startedAt = performance.now();

        let total = Math.max(0, Number(meta.total) || 0);
        let fetched = 0;
        let finishedOk = false;
        let cleanedUp = false;

        // Cleanup registry. run() used to own this list; the harness owns it now
        // so a site pipeline cannot forget to unwind a poll or a worker pool.
        const cleanups = [];
        const registerCleanup = fn => { if (typeof fn === 'function') cleanups.push(fn); };
        options.registerRunCleanup = registerCleanup;

        // Hold the panel for the whole run; cleanup() releases it, and both
        // callers (cmoa/02-run.js, ebookjapan/05-run.js) run cleanup() in a
        // finally, so the lock cannot outlive a failed run either. Without this
        // only BookWalker locked, and the other two stores could start a second
        // run over the same book while the first was still fetching.
        if (typeof ui.setRunLock === 'function') ui.setRunLock(true);

        // One upload-bar feed shared by the early cover upload and finalize, so
        // the bar tracks the whole multi-file upload (cover = file 1/N).
        const uploadFeed = makeUploadBarUpdater(barUpload);
        const coverState = { fired: false };

        const setTotal = n => { total = Math.max(0, Number(n) || 0); return total; };
        const seconds = () => ((performance.now() - startedAt) / 1000).toFixed(1);

        function showBars() {
            barWrap.style.display = 'flex';
            barDownload.wrap.style.display = 'flex';
            barDescramble.wrap.style.display = 'flex';
            setBar(barDownload, 0, '0%');
            setBar(barDescramble, 0, '0%');
        }

        // Download bar = pages fetched from the CDN; Descramble bar = pages
        // actually processed (zipped / handed to OCR). They diverge naturally.
        function refreshProgress() {
            const done = okIdx.size;
            const dl = Math.min(fetched, total);
            setBar(barDownload, total ? (dl / total) * 100 : 0, dl + '/' + total);
            setBar(barDescramble, total ? (done / total) * 100 : 0, done + '/' + total);
            // The Mokuro bar is owned by the bridge status poll (updateMokuroBar,
            // done/received/total). Never write it from here or the two writers
            // fight and the label flickers.
        }

        const bumpFetched = n => { fetched += (Number(n) || 0); refreshProgress(); };
        const bumpCached = n => { fetched += (Number(n) || 0); refreshProgress(); };

        function reportPage(idx) {
            reportRunProgress(options, 'page', {
                page: idx, pageCount: okIdx.size, total: total, error: null
            });
        }

        function reportPageError(idx, message) {
            reportRunProgress(options, 'page', {
                page: idx, pageCount: okIdx.size, total: total, error: message || 'error'
            });
        }

        function noteFailure(idx, message) {
            const msg = safeLogText(message || 'failed');
            errors.push(msg);
            failedIdx.add(idx);
            okIdx.delete(idx);
            reportPageError(idx, msg);
            refreshProgress();
        }

        // ---------------------------------------------------------------
        // Mokuro bridge conversation
        // ---------------------------------------------------------------
        // Pages are streamed to the bridge in strict page order (buffered until
        // the gaps fill) rather than in completion order: BookWalker's lane engine
        // settles pages out of order and CMOA's retry loop skips forward, so
        // completion order is not a reliable sequence. A failed page is skipped,
        // which keeps the volume contiguous.
        const mokuro = (mode !== 'ocr') ? null : (() => {
            let sessionId = null;
            let safeTitle = '';
            let poll = null;
            let nextIdx = 1;
            let sent = 0;
            const buffer = new Map();
            let chain = Promise.resolve();

            async function sendOrdered() {
                while (true) {
                    if (failedIdx.has(nextIdx)) { nextIdx++; continue; }
                    if (!buffer.has(nextIdx)) break;
                    const blob = buffer.get(nextIdx);
                    buffer.delete(nextIdx);
                    const page = nextIdx;
                    const fn = 'page-' + String(page).padStart(4, '0') + '.' + IMAGE_CODEC.ext;
                    try {
                        await mokuroStreamPage(sessionId, blob, fn, page);
                        sent++;
                        reportRunProgress(options, 'page-stream', {
                            page: page, pageCount: okIdx.size, total: total
                        });
                    } catch (e) {
                        errors.push('OCR send page ' + page + ': ' + safeLogText((e && e.message) || e));
                    }
                    nextIdx++;
                }
            }

            function schedule() {
                // Keep the concurrent GUI behaviour, but serialize the headless
                // stream so the returned promise cannot race a POST that is
                // still in flight after the last page is decoded.
                if (!options.headless) { sendOrdered(); return; }
                chain = chain.then(sendOrdered, sendOrdered).catch(e => {
                    errors.push('OCR stream: ' + safeLogText((e && e.message) || e));
                });
            }

            function startPoll() {
                if (!sessionId || poll) return;
                poll = setInterval(async () => {
                    const st = await mokuroStatus(sessionId);
                    if (!st) return;
                    const done = st.pages_ocr_done ?? 0;
                    const got = st.pages_received ?? 0;
                    updateMokuroBar(barMokuro, done, got, total);
                    reportRunProgress(options, 'bridge-status', {
                        pageCount: got, ocrPageCount: done, total: total
                    });
                }, 700);
                registerCleanup(() => { if (poll) { clearInterval(poll); poll = null; } });
            }

            return {
                get sessionId() { return sessionId; },
                get safeTitle() { return safeTitle; },
                get sent() { return sent; },

                // Opening the session is deliberately identical for both stores:
                // same bridge health gate, same idle gate, same session title.
                async open() {
                    barWrap.style.display = 'flex';
                    barMokuro.wrap.style.display = 'flex';
                    setBar(barMokuro, 0, '0/' + total);
                    if (!(await ensureBridgeRunning(25000))) {
                        throw new Error(MOKURO_BRIDGE_OFFLINE_MSG);
                    }
                    // Never start a capture while the bridge is still working on a
                    // previous run, unless an automation caller owns the bridge
                    // lifecycle and asks us to skip this wait.
                    if (!options.skipBridgeIdleWait && !(await waitForBridgeIdle(60000))) {
                        throw new Error('The Mokuro Bridge is still busy with a previous OCR/upload — wait for it to finish, then try again.');
                    }
                    const sess = await mokuroStartSession(meta.archiveName || meta.title || 'book');
                    sessionId = sess && sess.session_id;
                    if (options.automation && !sessionId) {
                        throw new Error('Mokuro bridge did not return a session_id');
                    }
                    safeTitle = sess && (sess.safe_title || sess.title) || '';
                    if (runResult) {
                        runResult.sessionId = sessionId;
                        runResult.safeTitle = safeTitle;
                    }
                    reportRunProgress(options, 'session', {
                        sessionId: sessionId || null, safeTitle: safeTitle, total: total
                    });
                    if (options.pollBridgeStatus !== false) startPoll();
                    return sessionId;
                },

                note(idx, blob) {
                    buffer.set(idx, blob);
                    if (idx === nextIdx) schedule();
                },

                // Cover = first page: push it to the destination immediately
                // (before OCR finishes) so the folder and upload bar show life right
                // away. Headless/deferred runs stream pages only, with no cover
                // side effect.
                cover(idx, blob) {
                    if (options.skipCover || idx !== 1 || coverState.fired || !sessionId) return;
                    coverState.fired = true;
                    uploadCoverEarly({
                        ui, barUpload, feed: uploadFeed,
                        mokuroSessionId: sessionId, safeTitle: safeTitle, blob,
                    }).catch(() => {});
                },

                async settle() {
                    if (options.headless) await chain;
                    for (let i = 1; i <= total; i++) {
                        if (failedIdx.has(i)) continue;
                        const blob = buffer.get(i);
                        if (!blob) continue;
                        buffer.delete(i);
                        const fn = 'page-' + String(i).padStart(4, '0') + '.' + IMAGE_CODEC.ext;
                        try {
                            await mokuroStreamPage(sessionId, blob, fn, i);
                            sent++;
                            reportRunProgress(options, 'page-stream', {
                                page: i, pageCount: okIdx.size, total: total
                            });
                        } catch (e) {
                            errors.push('Final OCR send page ' + i + ': ' + safeLogText((e && e.message) || e));
                        }
                    }
                    if (poll) { clearInterval(poll); poll = null; }
                },

                async finalize() {
                    barMokuro.wrap.style.display = 'flex';
                    const { result, plan } = await finalizeOcrSession(
                        sessionId, ui, barUpload, barMokuro, total, uploadFeed, options);
                    const missing = total - okIdx.size;
                    if (missing > 0) {
                        if (!options.headless) setRunDetails(details, msgOcrPartial(missing, total), errors);
                        return { result, plan, missing, ok: false };
                    }
                    if (!options.headless) {
                        if (plan && plan.method === 'local') {
                            const localPath = storedPathOf(result) || plan.localDir;
                            if (localPath) details.textContent = msgStoredLocal(localPath);
                        } else if (plan && plan.method) {
                            const rp = result && (result.remote_path || result.mega_path);
                            if (rp) details.textContent = msgUploadedTo(methodShortLabel(plan.method), rp);
                        }
                        if (errors.length) appendRunDetails(details, errors, 'Issues during the run');
                    }
                    if (!options.headless) {
                        ui.showReaderButton(result);
                        ui.showStoredButton(result);
                    }
                    return { result, plan, missing, ok: true };
                },

                // Deferred mode is deliberately page-stream-only: the external
                // CLI owns /finalize (and any upload/delete policy) later.
                deferred() {
                    if (runResult) {
                        runResult.pageCount = okIdx.size;
                        runResult.total = total;
                        runResult.errors = errors;
                        runResult.deferredFinalize = true;
                        runResult.ok = (total - okIdx.size) === 0 && errors.length === 0 && sent === okIdx.size;
                    }
                    reportRunProgress(options, 'deferred-finalize', {
                        pageCount: okIdx.size, total: total, deferredFinalize: true,
                        streamed: sent, ok: runResult ? runResult.ok : false
                    });
                    return runResult;
                },
            };
        })();

        // ---------------------------------------------------------------
        // Page accounting
        // ---------------------------------------------------------------
        // A successfully fetched+processed page: counted for both bars, added to
        // the archive, cached for a resume, and handed to OCR. Sites call this
        // exactly once per page that produced usable output. `ext` overrides the
        // archive extension for a page whose bytes could not be re-encoded to the
        // selected codec (CMOA passes the real one when it kept raw bytes).
        function notePage(idx, blob, crc, ext) {
            okIdx.add(idx);
            failedIdx.delete(idx);
            if (zip && blob) zip.entries.push({
                path: 'page-' + String(idx).padStart(4, '0') + '.' + (ext || IMAGE_CODEC.ext),
                blob,
                crc: Number.isInteger(crc) ? crc : undefined,
            });
            if (options.usePageCache && meta.cid && blob) {
                try { cachePage(meta.cid, idx, blob, crc); } catch (e) {}
            }
            if (mokuro && blob) {
                mokuro.cover(idx, blob);
                mokuro.note(idx, blob);
            }
            reportPage(idx);
            refreshProgress();
        }

        // A page served from the page cache: already correct, no fetch, no
        // descramble, no re-upload of the source, so it counts as both.
        function noteCached(idx, blob, crc) {
            okIdx.add(idx);
            failedIdx.delete(idx);
            if (zip && blob) zip.entries.push({
                path: 'page-' + String(idx).padStart(4, '0') + '.' + IMAGE_CODEC.ext,
                blob,
                crc: Number.isInteger(crc) ? crc : undefined,
            });
            if (mokuro && blob) mokuro.note(idx, blob);
            refreshProgress();
        }

        // ---------------------------------------------------------------
        // Finishing
        // ---------------------------------------------------------------
        async function finishZip() {
            if (!zip || okIdx.size === 0) {
                setRunDetails(details, msgAllFailedZip(), errors);
                return outcome(false);
            }
            const secs = seconds();
            barDownload.wrap.style.display = 'flex';
            barDescramble.wrap.style.display = 'flex';
            barMokuro.wrap.style.display = 'none';
            barDownload.fill.style.width = '0%';
            barDownload.labRate.textContent = 'Storing';
            barDescramble.fill.style.width = '100%';
            barDescramble.labRate.textContent = '100%';

            const entries = zip.entries.slice();
            const zipBlob = await buildStoreZip(entries, done => {
                const pct = Math.round((done / Math.max(1, entries.length)) * 100);
                barDownload.fill.style.width = pct + '%';
                barDownload.labRate.textContent = pct + '%';
            });

            const url = URL.createObjectURL(zipBlob);
            const a = document.createElement('a');
            a.href = url;
            a.download = (meta.archiveName || zipBaseName(meta.sv, meta.title)) + '.zip';
            const anchorHost = document.body || document.documentElement;
            if (anchorHost) anchorHost.appendChild(a);
            a.click();
            setTimeout(() => { URL.revokeObjectURL(url); a.remove(); }, 4000);

            const missing = total - okIdx.size;
            if (missing > 0) {
                setRunDetails(details, msgZipPartial(okIdx.size, total), errors);
            } else {
                details.textContent = msgZipSaved(entries.length, fmtBytes(zipBlob.size), secs);
                if (errors.length) appendRunDetails(details, errors, 'Issues during the run');
            }
            // Matches the long-standing rule: an error-free run clears the page
            // cache, any run that logged an error keeps it so the next attempt
            // resumes instead of re-fetching the whole volume.
            finishedOk = errors.length === 0;
            return outcome(missing === 0);
        }

        // ---------------------------------------------------------------
        // Outcome + teardown
        // ---------------------------------------------------------------
        // Normalize the result object for automated callers. Sites pass whether
        // the run was good; the page accounting is filled in here so every store
        // reports identically.
        function outcome(ok) {
            if (!runResult) return ok;
            runResult.total = total;
            runResult.pageCount = okIdx.size;
            runResult.errors = errors;
            runResult.deferredFinalize = false;
            runResult.ok = !!ok && errors.length === 0;
            return runResult;
        }

        async function cleanup() {
            if (cleanedUp) return;
            cleanedUp = true;
            for (let i = cleanups.length - 1; i >= 0; i--) {
                try { cleanups[i](); } catch (e) {}
            }
            cleanups.length = 0;
            if (finishedOk && options.usePageCache) { try { await clearPageCache(); } catch (e) {} }
            // Guarded to match the acquire above: a reduced ui (the headless
            // mirror) must degrade to "no lock", not throw during teardown.
            if (typeof ui.setRunLock === 'function') ui.setRunLock(false);
        }

        // Report a thrown run: automation callers get a structured result, the
        // panel gets the one-line message.
        function reportFailure(e) {
            const message = (e && e.message) ? safeLogText(e.message)
                : 'something went wrong — see the browser console for details.';
            if (runResult) {
                runResult.ok = false;
                if (message && !runResult.errors.includes(message)) runResult.errors.push(message);
                reportRunProgress(options, 'failed', { ok: false, errors: runResult.errors });
                const error = e instanceof Error ? e : new Error(String(message));
                error.bwddResult = runResult;
                return error;
            }
            details.textContent = 'Error: ' + message;
            return null;
        }

        return {
            mode, options, errors, okIdx, failedIdx, zip, mokuro,
            get total() { return total; },
            get fetched() { return fetched; },
            get runResult() { return runResult; },
            get finishedOk() { return finishedOk; },
            setTotal, showBars, refreshProgress, bumpFetched, bumpCached,
            notePage, noteCached, noteFailure,
            registerCleanup, finishZip, outcome, cleanup, reportFailure, seconds,
            markFinished() { finishedOk = true; },
            details,
        };
    }
    // =====================================================================
    // Site adapters — one userscript, three stores
    // =====================================================================
    // A site adapter supplies only the four things that genuinely differ between
    // the stores: detection (which store is this page?), metadata (title,
    // series/volume, page count, archive name), page enumeration (what to fetch,
    // in reading order), and fetch + descramble (one page → finished image Blob).
    // Everything else - panel, controls, bars, Mokuro conversation, stat cards,
    // ZIP naming/assembly, page cache, headless automation - lives in core and is
    // shared verbatim, which is what keeps the paths from drifting apart.
    //
    // Contract:
    //   id, label, panelTitle      identity shown in the panel
    //   matches()                  true when this adapter owns the page
    //   install()                  page hooks; called once, at load
    //   refresh()                  optional: top up metadata before it is read
    //   getBook()                  { rawTitle, title, series, volNum } or null
    //   getPreview()               { title, pages, resolution, type } or null
    //   getCid()                   stable id, used for the page cache
    //   run(ui, mode, options)     the download pipeline for this store
    const SITE_REGISTRY = [];
    let ACTIVE_SITE = null;

    function registerSite(adapter) {
        if (adapter && adapter.id) SITE_REGISTRY.push(adapter);
        return adapter;
    }

    function detectSite() {
        for (const adapter of SITE_REGISTRY) {
            let owned = false;
            try { owned = !!adapter.matches(); } catch (e) { owned = false; }
            if (owned) return adapter;
        }
        // BookWalker is the default: it is the original site for this script,
        // and its panel is also what a bare injected copy (tests, devtools)
        // expects to get on a host no adapter claims.
        return SITE_REGISTRY.find(a => a.id === 'bookwalker') || SITE_REGISTRY[0] || null;
    }

    function activeSite() { return ACTIVE_SITE; }
    function siteCid() {
        if (ACTIVE_SITE && typeof ACTIVE_SITE.getCid === 'function') {
            try { return ACTIVE_SITE.getCid() || ''; } catch (e) { return ''; }
        }
        return '';
    }
    // detectSite() always yields an adapter, so naming one store's pipeline as a
    // fallback here was dead code and a dependency the shared core should not have.
    function siteRun(ui, mode, options) {
        if (ACTIVE_SITE && typeof ACTIVE_SITE.run === 'function') {
            return ACTIVE_SITE.run(ui, mode, options);
        }
        throw new Error('no site adapter is registered for this page');
    }
    function siteLabel() { return (ACTIVE_SITE && ACTIVE_SITE.label) || 'BookWalker'; }
    function sitePanelTitle() {
        return (ACTIVE_SITE && ACTIVE_SITE.panelTitle) || 'BookWalker Native Downloader';
    }

    // Shared panel bring-up. Both stores get the identical UI, the identical
    // button wiring and the identical "wait for the viewer, then show the book
    // card + reading stats" loop; only the adapter's own answers differ.
    function bootSharedPanel(site) {
        ACTIVE_SITE = site;
        installHeadlessAutomation();
        // A headless/CLI page gets no panel, no bridge-health tick and no stats
        // loop: the caller owns all of that.
        if (isHeadlessPage()) return null;

        const ui = buildUI();
        const launch = mode => {
            Promise.resolve()
                .then(() => site.run(ui, mode))
                .catch(e => {
                    const text = safeLogText((e && e.message) || e);
                    console.warn('[bwdd] ' + site.id + ' run failed: ' + text);
                    // A rejected run must land on the panel, not only in the
                    // console, or the bars sit at 0/0 and the click looks like it did
                    // nothing. Un-hide the details box too.
                    try {
                        setRunDetails(ui.details, 'the run failed: ' + text, []);
                        if (ui.details) ui.details.hidden = false;
                    } catch (e2) {}
                });
        };
        ui.btnZip.onclick = () => launch('zip');
        ui.btnOcr.onclick = () => launch('ocr');

        try { schedulePageCachePrune(0); } catch (e) {}
        if (typeof site.afterBoot === 'function') {
            try { site.afterBoot(ui); } catch (e) {}
        }

        (async () => {
            let statsKicked = false;
            let lastStoresKey = null;
            let lastArchiveSource = null;
            // The viewer fills its metadata in asynchronously, so poll briefly
            // rather than reading the title once and settling for document.title.
            for (let i = 0; i < 40; i++) {
                await new Promise(r => setTimeout(r, 500));
                // Let the adapter top up its own metadata first: CMOA's viewer
                // fills its page list in after the document is ready, so the
                // answers below are only as good as the last refresh.
                if (typeof site.refresh === 'function') {
                    try { await site.refresh(); } catch (e) {}
                }
                let book = null;
                try { book = site.getBook(); } catch (e) { book = null; }
                const rawTitle = (book && book.rawTitle) || document.title || '';
                if (rawTitle && rawTitle !== lastArchiveSource) {
                    lastArchiveSource = rawTitle;
                    try { ui.syncArchiveDefault(rawTitle); } catch (e) {}
                }
                if (!statsKicked && book && book.series) {
                    try {
                        fetchAndRenderStats(ui.statsEl, book.series, book.volNum);
                        statsKicked = true;
                    } catch (e) {}
                }
                // Which other shops carry it, linked to their store pages. This
                // re-runs when the title or volume changes rather than latching on the
                // first pass: the viewer publishes metadata asynchronously, and a
                // lookup fired against a placeholder title comes back "not found" at
                // every shop. typeof, not try/catch: the availability module is in the
                // combined build only, so the identifier may not exist at all.
                if (typeof lookupAvailability === 'function' && book && (book.series || book.title)) {
                    const storesKey = String(book.series || book.title).trim() + '|' +
                        (book.volNum == null ? '' : book.volNum);
                    if (storesKey !== lastStoresKey) {
                        lastStoresKey = storesKey;
                        try { lookupAvailability(ui.statsEl, book.series, book.title, book.volNum); } catch (e) {}
                    }
                }
                let preview = null;
                try { preview = site.getPreview(); } catch (e) { preview = null; }
                if (preview) {
                    renderBookCard(ui.statsEl, preview);
                    break;
                }
            }
        })();

        return ui;
    }
    // =====================================================================
    // CMOA site adapter — metadata
    // =====================================================================
    // CMOA (コミックシーモア) serves its "speed reader" from a per-volume CDN
    // (binb-cmoa.akamaized.net) as individually scrambled JPEG tiles. The page
    // list lives on viewer.content.page, and the viewer's reader exposes
    // getImageDescrambleCoords(), the only correct way to unshuffle a page.
    //
    // Everything the user sees (panel, bars, Mokuro bridge, stats, automation
    // protocol) comes from core, identical to the BookWalker path.
    // The image endpoint's `q` parameter is a quality *index* and lower is
    // better: the reader's own getImageUrl() uses q=0 for high-quality images
    // and q=1 for the viewer default, never 2 or 3. So the ladder tries the
    // original first and falls back to the standard rendition only when the
    // store refuses the best one (as a free/trial volume does).
    const CMOA_QUALITY_ORDER = (function () {
        try {
            const custom = window.__bwddCmoaQualityOrder;
            if (Array.isArray(custom) && custom.length && custom.every(q => /^[0-9]+$/.test(String(q)))) {
                return custom.map(String);
            }
        } catch (e) {}
        return ['0', '1'];
    })();
    const CMOA_FETCH_CONCURRENCY = 6;
    const cmoaState = {
        // True while a download owns the quality field, so a state refresh
        // cannot reset the rung the run has settled on.
        running: false,
        cid: null,
        contentsServer: null,
        token: null,
        viewMode: null,
        dmytime: null,
        u0: null,
        u1: null,
        extraParams: {},
        title: null,          // display title (SubTitle when the API gives one)
        rawTitle: null,       // whatever the page/viewer called this volume
        pages: [],
        quality: null,
        originalQuality: null,
        ready: false,
        collecting: false,
        error: null,
        tokenPool: [],
        lastGoodToken: null,
        reader: null,
        viewer: null,
        qualityBlacklist: new Set(),
    };

    // The viewer's globals (SpeedBinb, its reader) live on the page window. A
    // userscript manager may hand us a sandboxed `window`, so prefer the real
    // page window when it is reachable and fall back when it is not.
    function cmoaPageWindow() {
        try {
            if (typeof unsafeWindow !== 'undefined' && unsafeWindow) {
                if (unsafeWindow.SpeedBinb) return unsafeWindow;
            }
        } catch (e) {}
        return window;
    }

    function cmoaLog() {
        if (!BWDD_DEBUG) return;
        try { console.log.apply(console, ['[bwdd/cmoa]'].concat([].slice.call(arguments))); } catch (e) {}
    }

    // --- token pool -------------------------------------------------------
    // CMOA signs image requests with a short-lived `p` token that the viewer
    // mints as the reader pages through the volume. Keeping every token seen
    // and retrying the next on a 403 is what makes a long download survive a
    // token rolling over mid-run.
    function cmoaRememberToken(tokenValue, options) {
        options = options || {};
        if (!tokenValue && tokenValue !== 0) return;
        const token = String(tokenValue).trim();
        if (!token || token.toLowerCase() === 'null') return;
        if (!cmoaState.tokenPool.includes(token)) cmoaState.tokenPool.push(token);
        if (options.markGood) cmoaState.lastGoodToken = token;
        if (!cmoaState.token || options.force || (options.prefer && cmoaState.token !== token)) {
            cmoaState.token = token;
        }
    }

    function cmoaEvictToken(tokenValue) {
        if (!tokenValue && tokenValue !== 0) return;
        const token = String(tokenValue).trim();
        if (!token) return;
        cmoaState.tokenPool = cmoaState.tokenPool.filter(t => t !== token);
        if (cmoaState.lastGoodToken === token) cmoaState.lastGoodToken = null;
        if (cmoaState.token === token) {
            cmoaState.token = cmoaState.lastGoodToken || cmoaState.tokenPool[0] || null;
        }
    }

    // --- parameter ingestion ---------------------------------------------
    // Every URL the viewer touches (page URL, data-ptbinb, its API calls)
    // carries a slice of the session; merge them all in, first writer wins for
    // the identity fields.
    function cmoaAssignParam(key, rawValue, force) {
        if (rawValue == null) return;
        const value = typeof rawValue === 'string' ? rawValue.trim() : String(rawValue);
        if (!value) return;
        const lower = key.toLowerCase();
        const shouldSet = current => force || current == null || current === '';
        if (lower === 'cid') { if (shouldSet(cmoaState.cid)) cmoaState.cid = value; return; }
        if (lower === 'contentsserver' || lower === 'sbcurl') {
            if (shouldSet(cmoaState.contentsServer)) cmoaState.contentsServer = value.replace(/\/$/, '');
            return;
        }
        if (lower === 'p' || lower === 'token') { cmoaRememberToken(value, { force: force }); return; }
        if (lower === 'vm' || lower === 'viewmode') { if (shouldSet(cmoaState.viewMode)) cmoaState.viewMode = value; return; }
        if (lower === 'dmytime' || lower === 'contentdate') { if (shouldSet(cmoaState.dmytime)) cmoaState.dmytime = value; return; }
        if (lower === 'qualitymode' || lower === 'quality' || lower === 'q') {
            cmoaState.originalQuality = value;
            if (force || !cmoaState.quality) cmoaState.quality = value;
            return;
        }
        if (lower === 'u0') { if (shouldSet(cmoaState.u0)) cmoaState.u0 = value; return; }
        if (lower === 'u1') { if (shouldSet(cmoaState.u1)) cmoaState.u1 = value; return; }
        cmoaState.extraParams[key] = value;
    }

    function cmoaApplySearchParams(searchParams, force) {
        if (!searchParams || typeof searchParams.forEach !== 'function') return;
        searchParams.forEach((value, key) => cmoaAssignParam(key, value, force));
    }

    function cmoaGatherFromUrl() {
        try {
            cmoaApplySearchParams(new URLSearchParams(location.search || ''));
            if (!cmoaState.cid) {
                const m = location.href.match(/[?&]cid=([^&#]+)/);
                if (m) cmoaState.cid = decodeURIComponent(m[1]);
            }
        } catch (e) {}
    }

    function cmoaGatherFromDataset() {
        let node = null;
        try { node = document.querySelector('[data-ptbinb]'); } catch (e) {}
        if (!node) return;
        const attr = node.getAttribute('data-ptbinb');
        if (attr) {
            try {
                cmoaApplySearchParams(new URL(attr, location.origin).searchParams);
            } catch (e) {
                const i = attr.indexOf('?');
                if (i !== -1) cmoaApplySearchParams(new URLSearchParams(attr.slice(i + 1)));
            }
        }
        const cidAttr = node.getAttribute('data-ptbinb-cid');
        if (cidAttr && !cmoaState.cid) cmoaState.cid = cidAttr;
    }

    // The viewer's performance timeline still holds the signed URLs it used,
    // including the ContentsServer origin, token and quality. This is what
    // keeps working when the script starts after the viewer's own requests.
    function cmoaExtractFromPerformance() {
        if (!window.performance || typeof window.performance.getEntriesByType !== 'function') return;
        let entries = [];
        try { entries = window.performance.getEntriesByType('resource') || []; } catch (e) { return; }
        for (const entry of entries) {
            const name = entry && entry.name;
            if (typeof name !== 'string') continue;
            if (!/sbcGet(?:Cntnt|Img)\.php/i.test(name)) continue;
            let parsed = null;
            try { parsed = new URL(name, location.origin); } catch (e) { continue; }
            const cidParam = parsed.searchParams.get('cid');
            if (cmoaState.cid && cidParam && cidParam !== cmoaState.cid) continue;
            if (/sbcGetCntnt\.php/i.test(parsed.pathname)) {
                const base = new URL('.', parsed).href.replace(/\/$/, '');
                if (!cmoaState.contentsServer) cmoaState.contentsServer = base;
                cmoaApplySearchParams(parsed.searchParams, true);
            } else {
                const q = parsed.searchParams.get('q');
                if (q) cmoaState.originalQuality = q;
                const p = parsed.searchParams.get('p');
                if (p) cmoaRememberToken(p, { prefer: true });
                const vm = parsed.searchParams.get('vm');
                if (vm && !cmoaState.viewMode) cmoaState.viewMode = vm;
                const dmy = parsed.searchParams.get('dmytime');
                if (dmy && !cmoaState.dmytime) cmoaState.dmytime = dmy;
            }
        }
    }

    // --- viewer access ----------------------------------------------------
    function cmoaGetViewer() {
        try {
            const w = cmoaPageWindow();
            if (w.SpeedBinb && typeof w.SpeedBinb.getInstance === 'function') {
                return w.SpeedBinb.getInstance('content');
            }
        } catch (e) {}
        return null;
    }

    function cmoaSafe(fn) {
        try { return fn(); } catch (e) { return null; }
    }

    function cmoaIsReader(candidate) {
        return !!(candidate && typeof candidate.getImageDescrambleCoords === 'function');
    }

    // The reader is the object that can unshuffle a page. Ask the viewer
    // directly first, then walk one level of its own properties, because the
    // exact accessor has changed between viewer builds.
    function cmoaGetReader() {
        const viewer = cmoaState.viewer || cmoaGetViewer();
        if (!viewer) return cmoaState.reader;
        const direct = cmoaSafe(() => viewer.reader);
        if (cmoaIsReader(direct)) return direct;
        if (typeof direct === 'function') {
            const invoked = cmoaSafe(() => direct.call(viewer));
            if (cmoaIsReader(invoked)) return invoked;
        }
        const viaGetter = cmoaSafe(() => (typeof viewer.getReader === 'function' ? viewer.getReader() : null));
        if (cmoaIsReader(viaGetter)) return viaGetter;
        const seeds = [viewer, cmoaSafe(() => viewer.content), cmoaSafe(() => viewer.state)];
        for (const seed of seeds) {
            if (!seed || typeof seed !== 'object') continue;
            if (cmoaIsReader(seed)) return seed;
            let keys = [];
            try { keys = Object.keys(seed); } catch (e) { keys = []; }
            for (const key of keys) {
                if (!/reader/i.test(key)) continue;
                const value = cmoaSafe(() => seed[key]);
                if (cmoaIsReader(value)) return value;
                if (typeof value === 'function') {
                    const invoked = cmoaSafe(() => value.call(seed));
                    if (cmoaIsReader(invoked)) return invoked;
                }
            }
        }
        return cmoaState.reader;
    }

    // Page list. Each entry keeps the image descriptor the viewer parsed from
    // the volume's XML (relative path, dimensions, spread hint) because that
    // descriptor is what getImageDescrambleCoords() expects, not a flat path.
    function cmoaCollectPages(viewer) {
        const pages = [];
        if (!viewer) return pages;
        const pageArray = cmoaSafe(() => {
            const content = viewer.content;
            return content && content.page;
        });
        if (!Array.isArray(pageArray)) return pages;
        const seen = new Set();
        pageArray.forEach((entry, idx) => {
            const image = cmoaSafe(() => entry && entry.image) || null;
            const src = (image && typeof image.src === 'string') ? image.src.trim()
                : (entry && typeof entry.src === 'string' ? entry.src.trim() : '');
            if (!src || seen.has(src)) return;
            seen.add(src);
            pages.push({
                index: idx,
                src: src,
                id: (entry && entry.id) || (image && image.id) || 'page_' + (idx + 1),
                width: image && Number.isFinite(Number(image.orgwidth)) ? Number(image.orgwidth) : null,
                height: image && Number.isFinite(Number(image.orgheight)) ? Number(image.orgheight) : null,
                spread: image && typeof image.pagespread !== 'undefined' ? image.pagespread : null,
                image: image || null,
            });
        });
        pages.sort((a, b) => a.index - b.index);
        return pages;
    }

    // --- content info -----------------------------------------------------
    // The viewer only keeps items[0].Title, the store's SEO page title
    // ("無料・試し読みページ … ｜ author ｜ 漫画…"). The API also returns a clean
    // SubTitle ("… 1巻"), so re-issuing the viewer's own request gives the
    // archive a real name and the stat lookups a real series to search for.
    function cmoaContentInfoUrl() {
        const reader = cmoaGetReader();
        const fromReader = cmoaSafe(() => reader && reader.requestUrl);
        if (typeof fromReader === 'string' && /bibGetCntntInfo/i.test(fromReader)) return fromReader;
        if (!cmoaState.cid) return null;
        const u0 = cmoaState.u0 || '1';
        return location.origin + '/bib/sws/bibGetCntntInfo.php?cid=' +
            encodeURIComponent(cmoaState.cid) + '&dmytime=' + Date.now() + '&u0=' + encodeURIComponent(u0);
    }

    function cmoaIngestContentInfo(payload, sourceUrl) {
        let data = payload;
        if (typeof payload === 'string') {
            try { data = JSON.parse(payload); } catch (e) { data = null; }
        }
        if (data && typeof data === 'object' && Array.isArray(data.items) && data.items.length) {
            const item = data.items[0] || {};
            if (item.ContentsServer && !cmoaState.contentsServer) {
                cmoaState.contentsServer = String(item.ContentsServer).replace(/\/$/, '');
            }
            if (item.p) cmoaRememberToken(item.p, { force: !cmoaState.lastGoodToken });
            if (item.ViewMode != null && cmoaState.viewMode == null) cmoaState.viewMode = String(item.ViewMode);
            if (item.ContentDate && !cmoaState.dmytime) cmoaState.dmytime = String(item.ContentDate);
            // Prefer the clean product title the store itself uses for the
            // volume; fall back to the SEO title only when it is absent.
            const clean = typeof item.SubTitle === 'string' ? item.SubTitle.trim() : '';
            const raw = typeof item.Title === 'string' ? item.Title.trim() : '';
            if (clean) cmoaState.title = clean;
            if (raw) cmoaState.rawTitle = raw;
            if (!cmoaState.title && raw) cmoaState.title = cmoaCleanTitle(raw);
        }
        if (typeof sourceUrl === 'string') {
            try { cmoaApplySearchParams(new URL(sourceUrl, location.href).searchParams, true); } catch (e) {}
        }
    }

    async function cmoaFetchContentInfo() {
        if (cmoaState.title && cmoaState.contentsServer) return true;
        const url = cmoaContentInfoUrl();
        if (!url) return false;
        try {
            const res = await fetchWithTimeout(url, {
                headers: { 'Accept': 'application/json, text/javascript, */*; q=0.01' },
                credentials: 'include',
            }, 15000);
            if (!res || !res.ok) return false;
            const text = await res.text();
            cmoaIngestContentInfo(text, url);
            return true;
        } catch (e) {
            cmoaLog('content info fetch failed', safeLogText(e && e.message));
            return false;
        }
    }

    // The SEO title is "<label> <volume> ｜ <author> ｜ <store>"; the volume is
    // the part before the first full-width pipe, minus the store's own prefix.
    const CMOA_JUNK_TITLE = /^(?:binb(?:\s*speed\s*reader)?|speed\s*binb(?:\s*reader)?|speed\s*reader|cmoa|コミックシーモア|無料[・･]?試し読み(?:ページ)?|試し読みページ|ローディング|loading)$/i;
    function cmoaCleanTitle(raw) {
        let s = String(raw || '').trim();
        if (!s) return '';
        s = s.split('｜')[0].trim();
        s = s.replace(/^(?:無料[・･]?)?(?:試し読み|立ち読み)(?:ページ)?\s*/, '').trim();
        // A trailing imprint group ("（ビッグガンガンコミックス）") belongs to the
        // publisher, not the series, and would derail the manga-kotoba search.
        const m = s.match(/^(.*?[0-9０-９]{1,3}\s*[巻話])\s*[（(][^）)]*[）)]\s*$/);
        if (m && m[1]) s = m[1].trim();
        // The viewer rewrites document.title to its own name ("BinB Speed
        // Reader") once it boots; that is not the volume's title.
        if (CMOA_JUNK_TITLE.test(s)) return '';
        return s;
    }

    // Where the volume title can come from, best first. The viewer's own
    // bibliography only ever carries the store's SEO title, so the API's
    // SubTitle (see cmoaIngestContentInfo) is the one that yields a real name.
    function cmoaTitleFromDom() {
        // The reader's header still holds the SEO title after the viewer has
        // replaced document.title with its own name.
        try {
            const el = document.getElementById('menu_header_tittle');
            const t = el && el.textContent ? el.textContent.trim() : '';
            if (t) return t;
        } catch (e) {}
        return document.title || '';
    }

    // --- readiness --------------------------------------------------------
    function cmoaComputeReadiness() {
        const missing = [];
        if (!cmoaState.cid) missing.push('content ID');
        if (!cmoaState.contentsServer) missing.push('contents server');
        if (!cmoaState.pages.length) missing.push('page list');
        cmoaState.ready = missing.length === 0;
        return missing;
    }

    async function cmoaRefreshState() {
        if (cmoaState.collecting) return;
        cmoaState.collecting = true;
        try {
            cmoaGatherFromUrl();
            cmoaGatherFromDataset();
            cmoaExtractFromPerformance();
            // The performance timeline normally supplies the contents server and
            // the token before this runs, but it can never supply the volume's
            // real name: only bibGetCntntInfo carries SubTitle. So fetch until we
            // actually have a title, not merely until we can fetch pages.
            if (!cmoaState.contentsServer || !cmoaState.token || !cmoaState.title) {
                await cmoaFetchContentInfo();
            }
            const viewer = cmoaGetViewer();
            if (viewer) {
                cmoaState.viewer = viewer;
                const pages = cmoaCollectPages(viewer);
                if (pages.length) cmoaState.pages = pages;
                const reader = cmoaGetReader();
                if (reader) cmoaState.reader = reader;
            }
            if (!cmoaState.title) {
                const fromViewer = cmoaSafe(() => viewer && viewer.content && viewer.content.bibliography && viewer.content.bibliography.title);
                // The reader header keeps the store's SEO title even after the
                // viewer has renamed document.title, so it ranks above it.
                const candidates = [cmoaState.rawTitle, cmoaTitleFromDom(), fromViewer, document.title];
                for (const cand of candidates) {
                    const cleaned = cmoaCleanTitle(cand);
                    if (cleaned) {
                        cmoaState.rawTitle = cand;
                        cmoaState.title = cleaned;
                        break;
                    }
                }
            }
            // A run in progress owns this field (cmoaFetchPage records the rung
            // that actually worked), so a state refresh must not fight it. When
            // idle, always reset to the head of the ladder: the viewer's own
            // default (q=1) must never cap what we are willing to fetch.
            if (!cmoaState.running && cmoaState.quality !== CMOA_QUALITY_ORDER[0]) {
                cmoaState.quality = CMOA_QUALITY_ORDER[0];
            }
            if (BWDD_DEBUG) {
                cmoaLog('state', {
                    cid: cmoaState.cid, title: cmoaState.title, raw: cmoaState.rawTitle,
                    server: cmoaState.contentsServer, token: !!cmoaState.token,
                    quality: cmoaState.quality, pages: cmoaState.pages.length,
                });
            }
            cmoaComputeReadiness();
        } catch (e) {
            cmoaState.error = e;
            cmoaLog('state refresh failed', safeLogText(e && e.message));
        } finally {
            cmoaState.collecting = false;
        }
    }

    // --- passive capture --------------------------------------------------
    // Everything above already works without this, so the fetch wrapper is a
    // best-effort bonus: it keeps the token pool and quality fresh while the
    // user pages, which is what lets a long download ride out a token rollover.
    let cmoaCaptureInstalled = false;
    function cmoaInstallCapture() {
        if (cmoaCaptureInstalled) return;
        cmoaCaptureInstalled = true;
        const w = cmoaPageWindow();
        const nativeFetch = typeof w.fetch === 'function' ? w.fetch.bind(w) : null;
        if (!nativeFetch) return;
        try {
            w.fetch = function (...args) {
                let url = '';
                try {
                    const input = args[0];
                    url = typeof input === 'string' ? input : ((input && input.url) || '');
                } catch (e) { url = ''; }
                const promise = nativeFetch(...args);
                if (url && /sbcGet(?:Cntnt|Img)\.php|bibGetCntntInfo\.php/i.test(url)) {
                    promise.then(res => {
                        try {
                            if (/bibGetCntntInfo\.php/i.test(url)) {
                                return res.clone().text().then(text => cmoaIngestContentInfo(text, url)).catch(() => {});
                            }
                            if (/sbcGetImg\.php/i.test(url)) {
                                let parsed = null;
                                try { parsed = new URL(url, location.href); } catch (e) { return; }
                                const token = parsed.searchParams.get('p');
                                if (token) {
                                    if (res.status === 403) cmoaEvictToken(token);
                                    else cmoaRememberToken(token, { markGood: res.ok, force: res.ok && !cmoaState.lastGoodToken });
                                }
                            }
                        } catch (e) {}
                        return null;
                    }).catch(() => {});
                }
                return promise;
            };
        } catch (e) { /* a frozen fetch is not fatal: passive capture is optional */ }
    }

    // =====================================================================
    // CMOA site adapter — fetch & descramble
    // =====================================================================
    // One CMOA page is a scrambled JPEG tile served by sbcGetImg.php; the URL
    // carries the volume id, page path, quality and a short-lived `p` token,
    // and the CDN answers 403 for any of them wrong. The retry ladder below
    // walks quality × token, so one bad token cannot fail a whole volume.
    function cmoaBuildImageUrl(descriptor, qualityOverride, tokenOverride) {
        if (!cmoaState.contentsServer) throw new Error('CMOA contents server is not available');
        if (!cmoaState.cid) throw new Error('CMOA content ID is not available');
        if (!descriptor || !descriptor.src) throw new Error('CMOA page source URL unavailable');
        let base = cmoaState.contentsServer;
        if (!base.endsWith('/')) base += '/';
        const url = new URL('sbcGetImg.php', base);
        url.searchParams.set('cid', cmoaState.cid);
        url.searchParams.set('src', descriptor.src);
        const quality = qualityOverride != null ? qualityOverride : (cmoaState.quality || CMOA_QUALITY_ORDER[0]);
        if (quality != null) url.searchParams.set('q', String(quality));
        const token = tokenOverride != null ? tokenOverride : cmoaState.token;
        if (token) url.searchParams.set('p', token);
        if (cmoaState.viewMode != null) url.searchParams.set('vm', cmoaState.viewMode);
        if (cmoaState.dmytime) url.searchParams.set('dmytime', cmoaState.dmytime);
        if (cmoaState.u0 != null) url.searchParams.set('u0', cmoaState.u0);
        if (cmoaState.u1 != null) url.searchParams.set('u1', cmoaState.u1);
        Object.keys(cmoaState.extraParams).forEach(key => {
            const value = cmoaState.extraParams[key];
            if (value == null || value === '') return;
            const lower = key.toLowerCase();
            if (['cid', 'src', 'p', 'vm', 'q', 'dmytime', 'u0', 'u1'].includes(lower)) return;
            url.searchParams.set(key, value);
        });
        return url.toString();
    }

    function cmoaContentType(headerString) {
        if (!headerString || typeof headerString !== 'string') return null;
        for (const line of headerString.split(/\r?\n/)) {
            const i = line.indexOf(':');
            if (i === -1) continue;
            if (line.slice(0, i).trim().toLowerCase() === 'content-type') {
                return line.slice(i + 1).trim() || null;
            }
        }
        return null;
    }

    // The image CDN is cross-origin, so a plain page fetch is CORS-blocked.
    // Real parallelism comes from the shared transport lanes: the gm lane plus
    // every local fetch-proxy port the bridge advertises, each its own
    // HTTP/1.1 origin, so the 6-connections-per-origin limit stops being the
    // ceiling. Hence laneFetch() rather than GM_xmlhttpRequest (one lane).
    async function cmoaFetchViaLanes(url) {
        await waitOutCooldown();
        const t0 = performance.now();
        // Opt in only when the bridge is willing to fetch this CDN: the fetch
        // proxy is not transparent - it forwards to the host named in
        // x-bwdd-upstream and refuses the rest - so a port configured for
        // another store would answer a CMOA path from the wrong CDN. A generic
        // bridge allows every port; one hardcoded to BookWalker allows none.
        const allowProxy = proxyCanServe(hostOf(url));
        const res = await laneFetch(url, 45000, { allowProxy: allowProxy });
        if (!res || !res.ok) {
            const e = new Error('HTTP ' + (res ? res.status : '0'));
            e.status = res ? res.status : 0;
            throw e;
        }
        const buf = await res.arrayBuffer();
        const bytes = new Uint8Array(buf);
        recordLane(res._lane, performance.now() - t0, bytes.byteLength);
        const type = (res.headers && typeof res.headers.get === 'function' && res.headers.get('content-type')) || 'image/jpeg';
        return { bytes, type };
    }

    // Fallback for environments with no gm lane (no GM_xmlhttpRequest exposed,
    // or no grant); a plain same-context fetch is the last resort.
    async function cmoaFetchBinary(url) {
        const referer = location.href;
        const viaGM = () => new Promise((resolve, reject) => {
            if (typeof GM_xmlhttpRequest !== 'function') { reject(new Error('GM_xmlhttpRequest unavailable')); return; }
            let settled = false;
            const finish = fn => { if (!settled) { settled = true; fn(); } };
            try {
                GM_xmlhttpRequest({
                    method: 'GET',
                    url,
                    timeout: 45000,
                    responseType: 'arraybuffer',
                    headers: { 'Referer': referer, 'Accept': 'image/avif,image/webp,image/apng,image/*,*/*;q=0.8' },
                    onload: r => finish(() => {
                        if (r.status >= 200 && r.status < 300) {
                            const bytes = new Uint8Array(r.response || []);
                            resolve({ bytes, type: cmoaContentType(r.responseHeaders) || 'image/jpeg' });
                        } else {
                            const e = new Error('HTTP ' + r.status);
                            e.status = r.status;
                            reject(e);
                        }
                    }),
                    onerror: () => finish(() => reject(new Error('GM_xhr failed'))),
                    ontimeout: () => finish(() => reject(new Error('GM_xhr timeout'))),
                    onabort: () => finish(() => reject(new Error('GM_xhr aborted'))),
                });
            } catch (e) { finish(() => reject(e)); }
        });
        try {
            return await cmoaFetchViaLanes(url);
        } catch (laneError) {
            // A real HTTP answer (403/404/...) is meaningful and repeating the
            // identical request on another lane just wastes a round trip; only a
            // transport failure (status 0 / no response) is worth another lane.
            if (laneError && laneError.status) throw laneError;
            cmoaLog('lane transport failed, falling back', safeLogText(laneError && laneError.message));
        }
        try {
            return await viaGM();
        } catch (gmError) {
            if (typeof GM_xmlhttpRequest === 'function' && !/unavailable/.test(gmError && gmError.message || '')) throw gmError;
            // The CDN URL is self-signed (cid + src + p), so it needs no
            // cookies; sending them would also make this request fail CORS
            // preflight, since a credentialed request cannot use a wildcard
            // Access-Control-Allow-Origin.
            const res = await fetchWithTimeout(url, { credentials: 'omit', referer: referer }, 45000);
            if (!res.ok) { const e = new Error('HTTP ' + res.status); e.status = res.status; throw e; }
            const buf = await res.arrayBuffer();
            return { bytes: new Uint8Array(buf), type: res.headers.get('content-type') || 'image/jpeg' };
        }
    }

    async function cmoaDecodeImage(bytes, mimeType) {
        const buffer = bytes instanceof Uint8Array ? bytes : new Uint8Array(bytes || []);
        const blobType = (typeof mimeType === 'string' && mimeType !== 'application/octet-stream') ? mimeType : undefined;
        const blob = new Blob([buffer], { type: blobType });
        if (typeof createImageBitmap === 'function') {
            try {
                const bmp = await createImageBitmap(blob);
                return {
                    element: bmp, width: bmp.width, height: bmp.height,
                    cleanup: () => { try { if (bmp.close) bmp.close(); } catch (e) {} },
                };
            } catch (e) { /* fall through to an <img> decode */ }
        }
        return new Promise((resolve, reject) => {
            const objectUrl = URL.createObjectURL(blob);
            const img = new Image();
            img.decoding = 'async';
            img.onload = () => resolve({
                element: img,
                width: img.naturalWidth || img.width,
                height: img.naturalHeight || img.height,
                cleanup: () => { try { URL.revokeObjectURL(objectUrl); img.src = ''; } catch (e) {} },
            });
            img.onerror = e => { try { URL.revokeObjectURL(objectUrl); } catch (_) {} reject(e || new Error('image decode failed')); };
            img.src = objectUrl;
        });
    }

    // Re-encode through a canvas. This is where the correct output codec is
    // applied (and, for a lossless selection, where PNG/WebP is chosen).
    async function cmoaCanvasToBlob(canvas, mime, quality) {
        const q = typeof quality === 'number' ? quality : undefined;
        if (typeof canvas.toBlob === 'function') {
            const direct = await new Promise(resolve => canvas.toBlob(resolve, mime, q));
            if (direct) return direct;
            if (mime && mime !== 'image/png') {
                const fallback = await new Promise(resolve => canvas.toBlob(resolve, 'image/png'));
                if (fallback) return fallback;
            }
        }
        const dataUrl = canvas.toDataURL(mime || 'image/png');
        const comma = dataUrl.indexOf(',');
        const binary = atob(comma !== -1 ? dataUrl.slice(comma + 1) : dataUrl);
        const out = new Uint8Array(binary.length);
        for (let i = 0; i < binary.length; i++) out[i] = binary.charCodeAt(i);
        return new Blob([out], { type: mime || 'image/png' });
    }

    function cmoaExtFor(type) {
        const t = typeof type === 'string' ? type.split(';')[0].trim().toLowerCase() : '';
        if (t === 'image/png') return 'png';
        if (t === 'image/webp') return 'webp';
        if (t === 'image/jpeg' || t === 'image/jpg') return 'jpg';
        return null;
    }

    // Reassemble one scrambled page and re-encode it to the selected codec.
    // ext is set only when the original payload was kept as-is.
    async function cmoaProcessPage(descriptor, payload) {
        const reader = cmoaState.reader || cmoaGetReader();
        if (!reader || typeof reader.getImageDescrambleCoords !== 'function' || !descriptor || !descriptor.image) {
            cmoaLog('descramble skipped: reader unavailable', descriptor && descriptor.index);
            return { blob: new Blob([payload.bytes], { type: payload.type }), ext: cmoaExtFor(payload.type) };
        }
        let decoded = null;
        try {
            decoded = await cmoaDecodeImage(payload.bytes, payload.type);
        } catch (e) {
            cmoaLog('decode failed', safeLogText(e && e.message));
            return { blob: new Blob([payload.bytes], { type: payload.type }), ext: cmoaExtFor(payload.type) };
        }
        if (!decoded || !decoded.element || !decoded.width || !decoded.height) {
            if (decoded && decoded.cleanup) decoded.cleanup();
            return { blob: new Blob([payload.bytes], { type: payload.type }), ext: cmoaExtFor(payload.type) };
        }
        let plan = null;
        try {
            plan = reader.getImageDescrambleCoords(descriptor.image, decoded.width, decoded.height);
        } catch (e) {
            cmoaLog('getImageDescrambleCoords failed', safeLogText(e && e.message));
        }
        try {
            const canvas = document.createElement('canvas');
            canvas.width = (plan && plan.width > 0) ? plan.width : decoded.width;
            canvas.height = (plan && plan.height > 0) ? plan.height : decoded.height;
            const ctx = canvas.getContext('2d');
            if (!ctx) throw new Error('no 2D context');
            // With no plan the page is already whole; the straight copy still
            // re-encodes, so the archive extension always matches the bytes.
            ctx.clearRect(0, 0, canvas.width, canvas.height);
            if (plan && Array.isArray(plan.transfers) && plan.transfers.length) {
                plan.transfers.forEach(transfer => {
                    if (!transfer || (typeof transfer.index === 'number' && transfer.index !== 0)) return;
                    const coords = Array.isArray(transfer.coords) ? transfer.coords : [];
                    coords.forEach(piece => {
                        if (!piece) return;
                        const pw = piece.width || 0;
                        const ph = piece.height || 0;
                        if (pw <= 0 || ph <= 0) return;
                        try {
                            ctx.drawImage(decoded.element,
                                piece.xsrc || 0, piece.ysrc || 0, pw, ph,
                                piece.xdest || 0, piece.ydest || 0, pw, ph);
                        } catch (drawError) { /* keep the remaining pieces */ }
                    });
                });
            } else {
                ctx.drawImage(decoded.element, 0, 0);
            }
            const blob = await cmoaCanvasToBlob(canvas, IMAGE_CODEC.type, IMAGE_CODEC.quality);
            if (!blob) throw new Error('canvas encode produced nothing');
            return { blob, ext: cmoaExtFor(blob.type) };
        } catch (e) {
            cmoaLog('descramble pipeline failed', safeLogText(e && e.message));
            return { blob: new Blob([payload.bytes], { type: payload.type }), ext: cmoaExtFor(payload.type) };
        } finally {
            if (decoded && decoded.cleanup) decoded.cleanup();
        }
    }

    // Walk quality × token until a page comes back. A 403 means that
    // combination is refused: blacklist the quality and evict the token, then
    // try the next, so a stale credential degrades instead of failing the volume.
    async function cmoaFetchPage(descriptor, index) {
        const preferred = cmoaState.quality || CMOA_QUALITY_ORDER[0];
        const qualities = [];
        const pushQuality = q => {
            if (q == null) return;
            const s = String(q);
            if (qualities.includes(s)) return;
            if (cmoaState.qualityBlacklist.has(s)) return;
            qualities.push(s);
        };
        pushQuality(preferred);
        CMOA_QUALITY_ORDER.forEach(pushQuality);
        if (!qualities.length) qualities.push('1');

        const tokens = [];
        const pushToken = t => {
            if (!t) return;
            const s = String(t);
            if (!tokens.includes(s)) tokens.push(s);
        };
        pushToken(cmoaState.lastGoodToken);
        pushToken(cmoaState.token);
        cmoaState.tokenPool.forEach(pushToken);
        if (!tokens.length) tokens.push(null);

        let lastError = null;
        for (const token of tokens) {
            let forbidden = false;
            for (const quality of qualities) {
                if (cmoaState.qualityBlacklist.has(String(quality))) continue;
                try {
                    const url = cmoaBuildImageUrl(descriptor, quality, token);
                    cmoaLog('fetching page', index, 'quality', quality, 'token', token);
                    const tFetch = performance.now();
                    const payload = await cmoaFetchBinary(url);
                    const fetchMs = performance.now() - tFetch;
                    if (quality !== cmoaState.quality) cmoaState.quality = quality;
                    if (token) cmoaRememberToken(token, { markGood: true, force: true });
                    cmoaState.qualityBlacklist.delete(String(quality));
                    const tProc = performance.now();
                    const processed = await cmoaProcessPage(descriptor, payload);
                    if (BWDD_DEBUG) {
                        cmoaLog('page timing', index, {
                            fetchMs: Math.round(fetchMs),
                            processMs: Math.round(performance.now() - tProc),
                            bytes: payload.bytes ? payload.bytes.length : 0,
                            quality: quality,
                        });
                    }
                    return processed;
                } catch (e) {
                    lastError = e || new Error('fetch failed');
                    const text = safeLogText((e && e.message) || e);
                    cmoaLog('page fetch failed', index, 'quality', quality, text);
                    if (/(^|\D)403(\D|$)/.test(text)) {
                        forbidden = true;
                        cmoaState.qualityBlacklist.add(String(quality));
                    }
                }
            }
            if (token && forbidden) cmoaEvictToken(token);
        }
        throw lastError || new Error('Failed to download page ' + (index + 1));
    }
    // =====================================================================
    // CMOA site adapter — run pipeline & registration
    // =====================================================================
    // The shared harness owns the bars, Mokuro session, ZIP assembly and
    // reporting; what is left here is CMOA's own shape: wait for the viewer,
    // enumerate its pages, fetch a bounded number at a time.
    async function cmoaRun(ui, mode, options) {
        const runOptions = normalizeRunOptions(options, mode);
        const runResult = runOptions.automation
            ? (runOptions.result || newAutomationResult(mode, cmoaState.cid || '', runOptions.deferFinalize))
            : null;
        if (runResult) {
            runOptions.result = runResult;
            runOptions.errors = runResult.errors;
        }

        let harness = null;
        try {
            reportRunProgress(runOptions, 'started', { mode: mode, cid: cmoaState.cid || '' });
            cmoaState.qualityBlacklist.clear();
            cmoaState.running = true;
            // Always start at the head of the ladder, whatever rung the viewer
            // itself was using.
            cmoaState.quality = CMOA_QUALITY_ORDER[0];

            // The viewer learns the volume a beat after the page loads; poll
            // rather than failing a click that lands a moment too early.
            let ready = false;
            for (let i = 0; i < 30; i++) {
                await cmoaRefreshState();
                if (cmoaState.ready) { ready = true; break; }
                await new Promise(r => setTimeout(r, 500));
            }
            if (!ready) {
                const missing = cmoaComputeReadiness();
                throw new Error('CMOA reader is not ready yet (missing ' + missing.join(', ') + '). ' +
                    'Open the volume in the speed reader and let a page render, then try again.');
            }
            reportRunProgress(runOptions, 'state-refresh-ready');

            const rawTitle = cmoaState.rawTitle || cmoaState.title || document.title || '';
            const title = cmoaState.title || cmoaCleanTitle(rawTitle) || cmoaState.cid || 'CMOA volume';
            const sv = splitSeriesVolume(title);
            const archiveName = ui.syncArchiveDefault(cmoaState.title || rawTitle) ||
                zipBaseName(sv, title);
            if (runResult) {
                runResult.cid = cmoaState.cid || '';
                runResult.mode = mode;
                runResult.title = title;
                reportRunProgress(runOptions, 'book', { title: title, cid: cmoaState.cid || '' });
            }

            const descriptors = cmoaState.pages.map((page, index) => ({
                index: index + 1,
                src: page.src,
                image: page.image || null,
            }));
            const total = descriptors.length;
            if (!total) throw new Error('CMOA reader reported no pages for this volume.');

            const resolution = (() => {
                const first = cmoaState.pages.find(p => p.width && p.height);
                return first ? (first.width + ' × ' + first.height) : '?';
            })();

            harness = createRunHarness(ui, mode, runOptions, {
                title, archiveName, sv, total, cid: cmoaState.cid,
            });
            harness.setTotal(total);
            if (runResult) {
                runResult.total = total;
                reportRunProgress(runOptions, 'manifest', { total: total, plaintext: true });
            }

            if (!runOptions.headless) {
                renderBookCard(ui.statsEl, {
                    title, pages: total, resolution, type: 'Full Edition',
                });
                if (sv.series) fetchAndRenderStats(ui.statsEl, sv.series, sv.volNum);
            }
            harness.showBars();
            if (harness.mokuro) await harness.mokuro.open();

            // The CDN is HTTP/1.1 only, so the browser pins a download to 6
            // sockets per origin and that cap - not the worker count - sets the
            // ceiling. The trailing-dot hostname is the same server but a
            // different origin, worth 6 more sockets, with no local helper; if it
            // does not answer the lane simply stays off.
            try {
                // Probe with the least-restricted rung, not the best one: a free
                // or trial volume refuses the original rendition, so probing q=0
                // would 403 on exactly the most common volumes and leave the
                // extra origin quietly switched off.
                const probeRung = CMOA_QUALITY_ORDER[CMOA_QUALITY_ORDER.length - 1];
                const probeUrl = cmoaBuildImageUrl(
                    cmoaState.pages[0],
                    probeRung,
                    cmoaState.lastGoodToken || cmoaState.token || cmoaState.tokenPool[0] || null
                );
                await probeDotLane(probeUrl);
            } catch (e) {
                cmoaLog('dot lane probe skipped', safeLogText(e && e.message));
            }

            let nextIndex = 0;
            const worker = async () => {
                while (true) {
                    const i = nextIndex++;
                    if (i >= total) return;
                    const descriptor = descriptors[i];
                    const pageIdx = descriptor.index;
                    try {
                        // A page from a previous run needs neither a fetch nor a
                        // descramble; replaying it keeps a resumed volume cheap.
                        let cached = null;
                        if (runOptions.usePageCache && cmoaState.cid) {
                            cached = await getCachedPage(cmoaState.cid, pageIdx);
                        }
                        if (cached) {
                            harness.bumpCached(1);
                            harness.noteCached(pageIdx, cached, cachedPageCrc.get(cached));
                            continue;
                        }
                        const processed = await cmoaFetchPage(descriptor, i);
                        harness.bumpFetched(1);
                        if (processed && processed.blob) {
                            harness.notePage(pageIdx, processed.blob, undefined, processed.ext);
                        } else {
                            harness.noteFailure(pageIdx, 'page ' + pageIdx + ': empty response');
                        }
                    } catch (e) {
                        harness.bumpFetched(1);
                        harness.noteFailure(pageIdx, safeLogText((e && e.message) || e));
                    }
                }
            };
            // Size the fan-out from real transport capacity, like the BookWalker
            // pipeline: every online lane carries ~6 connections and is a
            // separate origin, so the page's 6-connection ceiling is not the
            // limit. A hardcoded worker count leaves those ports idle, which is
            // what made CMOA run at one page per request round-trip.
            const LANE_SLOTS = fetchSocketBudget(true);
            // Unlike BookWalker, a CMOA worker *is* its own concurrency: it
            // holds a fetched page then a decoded bitmap, so the ceiling is about
            // memory as much as sockets. 256 matches what the bridge can feed (48
            // proxy ports x 6 sockets plus the page and dot origins) while staying
            // short of the browser's ~300 socket budget; lower it with
            // window.__bwddMaxInflight if a low-RAM machine starts swapping.
            let inflightCap = 256;
            try {
                if (typeof window !== 'undefined' && window.__bwddMaxInflight > 0) {
                    inflightCap = Math.max(4, Math.min(256, window.__bwddMaxInflight | 0));
                }
            } catch (e) {}
            const concurrency = Math.max(
                Math.max(1, Math.min(CMOA_FETCH_CONCURRENCY, total)),
                Math.min(inflightCap, Math.min(total,
                    LANE_SLOTS + Math.max(8, Math.round(LANE_SLOTS * 0.2))))
            );
            if (BWDD_DEBUG) {
                console.info('[bwdd/cmoa] lanes=' + allLanes().length + ' sockets=' + LANE_SLOTS +
                    ' page workers=' + concurrency);
            }

            const workers = [];
            for (let w = 0; w < concurrency; w++) workers.push(worker());
            await Promise.all(workers);

            // Retry failed pages once after re-reading viewer state: a token
            // rollover mid-run is the common cause.
            if (harness.failedIdx.size && !runOptions.headless) {
                await cmoaRefreshState();
                const retry = descriptors.filter(d => harness.failedIdx.has(d.index));
                for (const descriptor of retry) {
                    try {
                        const processed = await cmoaFetchPage(descriptor, descriptor.index - 1);
                        if (processed && processed.blob) harness.notePage(descriptor.index, processed.blob, undefined, processed.ext);
                    } catch (e) { /* stays failed; reported below */ }
                }
            }

            const missing = total - harness.okIdx.size;

            if (mode === 'ocr' && harness.mokuro) {
                await harness.mokuro.settle();
                if (runOptions.deferFinalize) return harness.mokuro.deferred();
                const fin = await harness.mokuro.finalize();
                harness.markFinished();
                return harness.outcome(fin.ok);
            }

            if (mode === 'ocr' && !harness.mokuro) {
                throw new Error('Mokuro OCR is unavailable for this run');
            }

            if (missing === total) {
                setRunDetails(harness.details, msgAllFailedZip(), harness.errors);
                return harness.outcome(false);
            }
            return await harness.finishZip();
        } catch (e) {
            const reported = harness ? harness.reportFailure(e) : null;
            if (reported) throw reported;
            throw e;
        } finally {
            cmoaState.running = false;
            if (harness) await harness.cleanup();
        }
    }

    registerSite({
        id: 'cmoa',
        label: 'CMOA',
        panelTitle: 'CMOA Native Downloader',
        matches() {
            try {
                return /(^|\.)cmoa\.jp$/i.test(location.hostname);
            } catch (e) { return false; }
        },
        install() {
            try { cmoaInstallCapture(); } catch (e) {}
        },
        getBook() {
            if (!cmoaState.title && !cmoaState.rawTitle) return null;
            const title = cmoaState.title || cmoaCleanTitle(cmoaState.rawTitle);
            const sv = splitSeriesVolume(title);
            return { rawTitle: cmoaState.title || cmoaState.rawTitle, title: title, series: sv.series, volNum: sv.volNum };
        },
        getPreview() {
            if (!cmoaState.ready || !cmoaState.pages.length) return null;
            const first = cmoaState.pages.find(p => p.width && p.height);
            const title = cmoaState.title || cmoaCleanTitle(cmoaState.rawTitle) || cmoaState.cid;
            return {
                title: title,
                pages: cmoaState.pages.length,
                resolution: first ? (first.width + ' × ' + first.height) : '?',
                type: 'CMOA Speed Reader',
            };
        },
        getCid() { return cmoaState.cid || ''; },
        // The panel calls this before getBook/getPreview, so the page list and
        // real title show up as soon as the viewer has them.
        refresh() { return cmoaRefreshState(); },
        afterBoot() {
            // Keep refreshing while the viewer is still coming up; stop as soon
            // as it is ready so an idle page does not poll forever.
            let ticks = 0;
            const timer = setInterval(async () => {
                ticks++;
                if (cmoaState.ready || ticks > 60) { clearInterval(timer); return; }
                try { await cmoaRefreshState(); } catch (e) {}
            }, 1500);
        },
        archiveDefault(rawTitle) { return archiveDefaultName(rawTitle) || fsSafePath(cmoaState.cid || ''); },
        run(ui, mode, options) { return cmoaRun(ui, mode, options); },
        state: cmoaState,
        debug: { cmoaState },
        debugGlobals: { __bwddCmoa: cmoaState },
    });
    // =====================================================================
    // Initialization
    // =====================================================================
    // One entry point for both stores. The adapter is chosen from the host,
    // given the chance to install its page hooks, and then the shared panel is
    // brought up against it. A host no adapter claims still gets the
    // BookWalker adapter, which is what a bare injected copy expects.
    const BWDD_SITE = detectSite();
    ACTIVE_SITE = BWDD_SITE;
    if (BWDD_SITE && typeof BWDD_SITE.install === 'function') {
        try { BWDD_SITE.install(); } catch (e) {}
    }

    // Install the page API before DOMContentLoaded so a CLI can call start()
    // as soon as the userscript has been injected.
    installHeadlessAutomation();
    if (document.readyState === 'loading') {
        document.addEventListener('DOMContentLoaded', () => bootSharedPanel(BWDD_SITE));
    } else {
        bootSharedPanel(BWDD_SITE);
    }

    if (BWDD_DEBUG && !isHeadlessPage()) {
        try {
            const dbg = {
                cleanTitle, splitSeriesVolume, fsSafePath, zipBaseName, crc32Bytes, buildStoreZip,
                get imageCodec() { return IMAGE_CODEC; }, resolveImageCodec,
                // transport lanes: exposed for the lane/burst test harness
                allLanes, fetchSocketBudget, laneStats, laneSummary, recordLane, dedupeInflight,
                probeFetchProxy, probeDotLane, probeEdgeMirror, discoverProxyPorts,
                setProxyUpstreams, proxyCanServe,
                dottedUrl, edgeUrlFor, proxyPorts, laneFetch, capabilitySummary, workerPoolSize, workerBatchSize, makePool,
                get gmUsable() { return gmUsable; },
            };
            // Whatever the active store wants on the console, so this file never
            // names one of them.
            Object.assign(dbg, (BWDD_SITE && BWDD_SITE.debug) || {});
            window.__bwdd = dbg;
        } catch (e) {}
        try { window.__bwddUI = Object.assign(window.__bwddUI || {}, { renderStatsCards, renderBookCard, renderNativelyCard, renderMangaKotobaCard, setBar, showBars }); } catch (e) {}
        // The active adapter, for the site-adapter tests.
        try { window.__bwddSite = BWDD_SITE; } catch (e) {}
        for (const k in ((BWDD_SITE && BWDD_SITE.debugGlobals) || {})) {
            try { window[k] = BWDD_SITE.debugGlobals[k]; } catch (e) {}
        }
    }
})();
