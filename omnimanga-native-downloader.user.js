// ==UserScript==
// @name         Omnimanga Native Downloader
// @namespace    http://tampermonkey.net/
// @version      2.0.0
// @description  Saves a book from the BookWalker viewer, the CMOA speed reader or the ebookjapan reader as a ZIP or CBZ of full-resolution page images, fetched from the CDN and unscrambled offline. Optional Japanese OCR through mokuro-bridge, with upload to MEGA, Google Drive or OneDrive.
// @author       GolyBidoof
// @homepageURL  https://github.com/GolyBidoof/bookwalker-ebookjapan-cmoa-native-downloader
// @supportURL   https://github.com/GolyBidoof/bookwalker-ebookjapan-cmoa-native-downloader/issues
// @updateURL    https://github.com/GolyBidoof/bookwalker-ebookjapan-cmoa-native-downloader/releases/latest/download/omnimanga-native-downloader.user.js
// @downloadURL  https://github.com/GolyBidoof/bookwalker-ebookjapan-cmoa-native-downloader/releases/latest/download/omnimanga-native-downloader.user.js
// @match        https://viewer.bookwalker.jp/*
// @match        https://viewer-trial.bookwalker.jp/*
// @match        https://viewer-ptrial.bookwalker.jp/*
// @match        https://viewer-subscription.bookwalker.jp/*
// @match        https://www.cmoa.jp/bib/speedreader/*
// @match        https://ebookjapan.yahoo.co.jp/viewer/*
// @icon         https://www.google.com/s2/favicons?sz=64&domain=bookwalker.jp
// @grant        GM_xmlhttpRequest
// @connect      learnnatively.com
// @connect      manga-kotoba.com
// @connect      ebookjapan.yahoo.co.jp
// @connect      bookwalker.jp
// @connect      bw-bv-epubs.bookwalker.jp
// @connect      *.bookwalker.jp
// @connect      www.cmoa.jp
// @connect      free-binb-cmoa.akamaized.net
// @connect      binb-cmoa.akamaized.net
// @connect      prod-contents-br-page.akamaized.net
// @connect      127.0.0.1
// @connect      localhost
// @run-at       document-end
// @license      MIT
//
// One script, three stores. The panel, its controls, the Mokuro bridge, the
// reading-stat cards, the ZIP naming and the headless automation API are shared
// verbatim; only the store-specific protocol lives in its own module under
// src/sites/. BookWalker is the default for any page no adapter claims.
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

    // =====================================================================
    // 1. Capture the viewer's own network responses (browser data reuse)
    // =====================================================================
    const state = {
        cid: (new URLSearchParams(location.search)).get('cid') || '',
        fileBases: {},
        auth: null,        // {hti, cfg, bid, uuid, pfCd, Policy, Signature, Key-Pair-Id}
        baseUrl: null,     // e.g. https://bw-bv-epubs.bookwalker.jp/3_product/<cid>/1/<pid>/
        cti: null,         // title
        configBody: null,  // encrypted configuration_pack.json text
        configFromUrl: null
    };
    function bookWalkerPageName(index, source) {
        const path = String(source || '').split(/[?#]/, 1)[0];
        const base = path.slice(path.lastIndexOf('/') + 1);
        const stem = fsSafePath(base.replace(/\.(?:x?html?)$/i, ''));
        // Manifest-only naming stays independent of the viewer's reading position.
        // The ordinal distinguishes multiple images from the same source file.
        const prefix = String(index).padStart(4, '0');
        const suffix = '.' + IMAGE_CODEC.ext;
        const encoder = new TextEncoder();
        const budget = 255 - encoder.encode(prefix + ' ' + suffix).length;
        let name = '';
        let bytes = 0;
        for (const char of stem) {
            const size = encoder.encode(char).length;
            if (bytes + size > budget) break;
            name += char;
            bytes += size;
        }
        return prefix + (name ? ' ' + name : '') + suffix;
    }

    // Headless auth refreshes must correlate like one browser session. Do not
    // mint a new BID on every retry/endpoint call, but never consult browser
    // storage in this mode.
    let headlessBid = null;

    // Shared protocol/presentation constants (single source of truth).
    const AUTH_PARAM_KEYS = ['hti', 'cfg', 'bid', 'uuid', 'pfCd', 'Policy', 'Signature', 'Key-Pair-Id'];

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
    // BookWalker-only helper: locate the viewer's own NFBR engine object, which
    // holds the signed auth the capture hooks read. BWDD_DEBUG itself lives in
    // the shared core now.
    function findInNFBR(win) {
        const out = { auth: null, baseUrl: null, config: null, cti: null };
        if (!win || !win.NFBR) return out;
        const seen = new Set();
        let budget = 200000;
        function isPlain(o) { return o && typeof o === 'object' && !Array.isArray(o) && !(o instanceof Date) && !(o instanceof RegExp); }
        function skipVal(v) {
            if (v instanceof ArrayBuffer) return true;
            if (ArrayBuffer.isView && ArrayBuffer.isView(v)) return true;
            if (typeof Node !== 'undefined' && v instanceof Node) return true;
            return false;
        }
        function looksLikeAuth(o) {
            return o && typeof o === 'object' && typeof o.Policy === 'string' &&
                typeof o.Signature === 'string' && typeof o['Key-Pair-Id'] === 'string';
        }
        function looksLikeAuthInfo(o) {
            return o && typeof o === 'object' && o.auth_info && looksLikeAuth(o.auth_info);
        }
        function looksLikeConfig(o) {
            return o && typeof o === 'object' && o.configuration && o.configuration.contents &&
                Array.isArray(o.configuration.contents) && o.configuration.contents.length > 0;
        }
        function walk(o, depth) {
            if (!isPlain(o) || depth > 9 || seen.has(o) || budget <= 0) return;
            seen.add(o);
            budget--;
            if (!out.baseUrl && typeof o.url === 'string' && o.url.indexOf('bw-bv-epubs') !== -1 && looksLikeAuthInfo(o)) {
                out.baseUrl = o.url.replace(/\/$/, '') + '/';
                out.auth = o.auth_info;
                if (typeof o.cti === 'string') out.cti = o.cti;
            }
            if (!out.auth && looksLikeAuth(o)) out.auth = o;
            if (!out.config && looksLikeConfig(o)) out.config = o;
            if (out.auth && out.baseUrl && out.config) return;
            for (const k of Object.keys(o)) {
                if (budget <= 0) return;
                const v = o[k];
                if (skipVal(v)) continue;
                if (isPlain(v)) walk(v, depth + 1);
            }
        }
        try {
            walk(win.NFBR, 0);
            try {
                const frames = win.document ? win.document.querySelectorAll('iframe') : [];
                for (const f of frames) {
                    try {
                        const fw = f.contentWindow;
                        if (fw) {
                            const r = findInNFBR(fw);
                            if (r.auth) { out.auth = r.auth; out.baseUrl = r.baseUrl; out.config = r.config; out.cti = r.cti; }
                            if (out.auth && out.baseUrl) break;
                        }
                    } catch (e) {}
                }
            } catch (e) {}
        } catch (e) { if (BWDD_DEBUG) console.warn('[bwdd] findInNFBR:', safeLogText(e && e.message)); }
        return out;
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

    function apiOriginFromUrl(url) {
        try {
            const m = url.match(/^(https?:\/\/[^/]+)/);
            return m ? m[1] : null;
        } catch (e) { return null; }
    }
    function recordApiBase(url) {
        const o = apiOriginFromUrl(url);
        if (o) state.apiBase = o;
    }
    function apiBase() {
        if (state.apiBase) return state.apiBase;
        try {
            const configured = window.__BWDD_CLI__ && window.__BWDD_CLI__.publicApiBase;
            if (configured) return String(configured).replace(/\/+$/, '');
        } catch (e) {}
        try { return window.location.origin; } catch (e) { return ''; }
    }

    // Single reader for captured API/config responses, used by both the
    // fetch and XHR hooks below so the two capture paths can never classify an
    // endpoint differently (they once duplicated this and drifted). Handles:
    //   /browserWebApi/c | /trial-page/c  → full auth reply (auth_info + url)
    //   /browserWebApi/pb                 → incremental auth_info (policy refresh)
    //   configuration_pack.json           → encrypted manifest text (best dir wins)
    function absorbApiResponse(url, text) {
        try {
            if (url.includes('/browserWebApi/c') || url.includes('/trial-page/c')) {
                recordApiBase(url);
                const d = JSON.parse(text);
                if (d.auth_info && d.url) { state.auth = d.auth_info; state.baseUrl = d.url; state.cti = d.cti || state.cti; }
                if (d.auth_info && !d.url) { state.auth = Object.assign({}, state.auth || {}, d.auth_info); }
            } else if (url.includes('/browserWebApi/pb')) {
                recordApiBase(url);
                const d = JSON.parse(text);
                if (d.auth_info) {
                    // pb rotates the CloudFront policy; a changed signature
                    // resets the request-count budget.
                    const before = authPolicySig();
                    state.auth = Object.assign({}, state.auth || {}, d.auth_info);
                    if (authPolicySig() !== before) resetAuthBudget();
                }
            } else if (url.includes('configuration_pack.json')) {
                const dir = (url.split('?')[0] || '').replace(/configuration_pack\.json$/, '');
                if (!state.configBody || !state.configFromUrl || configPrio(dir) < configPrio(state.configFromUrl)) {
                    state.configBody = text;
                    state.configFromUrl = dir;
                }
            }
        } catch (e) {}
    }

    // Hooks. Headless callers can defer these wrappers until the automation
    // run starts; some viewer builds keep their document-start loader alive
    // when a fetch wrapper is installed before their own bootstrap finishes.
    let networkCaptureInstalled = false;
    function installNetworkCapture() {
        if (networkCaptureInstalled) return;
        networkCaptureInstalled = true;
        const origFetch = window.fetch;
        window.fetch = function (...args) {
            const url = typeof args[0] === 'string' ? args[0] : (args[0] && args[0].url) || '';
            const p = origFetch.apply(this, args);
            if (url.includes('/browserWebApi/c') || url.includes('/trial-page/c') ||
                url.includes('/browserWebApi/pb') || url.includes('configuration_pack.json')) {
                p.then(r => r.clone().text()).then(t => absorbApiResponse(url, t)).catch(() => {});
            }
            return p;
        };
        const origOpen = XMLHttpRequest.prototype.open;
        const origSend = XMLHttpRequest.prototype.send;
        XMLHttpRequest.prototype.open = function (m, u) { this.__bwUrl = u; return origOpen.apply(this, arguments); };
        XMLHttpRequest.prototype.send = function () {
            try {
                this.addEventListener('load', () => {
                    const u = this.__bwUrl || '';
                    if (u.includes('/browserWebApi/c') || u.includes('/trial-page/c') ||
                        u.includes('/browserWebApi/pb') || u.includes('configuration_pack.json')) {
                        absorbApiResponse(u, this.responseText);
                    }
                });
            } catch (e) {}
            return origSend.apply(this, arguments);
        };
    }
    function shouldDeferNetworkCapture() {
        try {
            return isHeadlessPage() && !!(window.__BWDD_CLI__ && window.__BWDD_CLI__.deferCapture);
        } catch (_) {
            return false;
        }
    }
    // NOTE: the install call lives in this site's adapter (install()), so the
    // entry point can decide per page which store's capture to bring up.

    // =====================================================================
    // 2. Crypto: decrypt configuration_pack.json
    // =====================================================================
    //
    // The viewer's configuration_pack.json is a custom envelope:
    //   { "version":"1.0", "data":"<custom-base64 payload>" }
    // Decoding is a fixed pipeline: custom base64 (A8j) -> a byte-keyed
    // key schedule (A3b / B0p / A7L / A6I / A2F / B0L / tB0l, an RC4 variant)
    // -> UTF-8 JSON of the page manifest. The first 128 chars of the payload
    // are three 32-byte keys (key1/key2/key3) later used to derive per-page
    // descramble seeds (section 3) and image filename tokens (section 4).
    //
    // NOTE: identifiers like A8j, A3b, B0p, v4..v9 are the original names
    // from the minified viewer, preserved verbatim because this port is
    // validated byte-for-byte against live HAR data and the bookworm
    // offline client. Renaming them would risk silent drift; the
    // pipeline below is annotated instead.
    // =====================================================================

    // Used by the key-schedule shuffles below.
    function arraySwap(arr, a, b) { const t = arr[a]; arr[a] = arr[b]; arr[b] = t; }

    // --- Custom base64 lookup tables (4 chars -> 3 bytes) ---
    // BookWalker's base64 alphabet is the standard A-Z a-z 0-9 + / set, but
    // the decode uses shifted bit masks per byte position (v5..v9).
    const ARR1 = 'ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/'.split('');
    const ARR2 = ARR1.map(c => c.charCodeAt(0));
    const v4 = [], v5 = [], v6 = [], v7 = [], v8 = [], v9 = [], vak = [];
    for (let i = 0; i < 64; i++) {
        const ch = ARR2[i];
        v4[ch] = i; v5[ch] = i << 2; v6[ch] = (i << 4) & 255;
        v7[ch] = (i << 6) & 255; v8[ch] = i >> 2; v9[ch] = i >> 4; vak[ch] = true;
    }
    const A8f = [v4, v5, v6, v7, v8, v9, vak];

    // Decode the custom base64 payload between dataOffset..dataEndOffset.
    // Returns [decodedBytes, decodedLength, key1, key2, key3] where the keys
    // are the first 128 chars split into three 32-byte registers.
    function A8j(content, dataOffset, dataEndOffset) {
        const arrayLength = 32, keyDataLength = 128;
        const payloadOffset = dataOffset + keyDataLength;
        const payloadLength = dataEndOffset - payloadOffset;
        if (payloadLength & 3) throw new Error('Invalid A8j payload length');
        const k1 = new Array(arrayLength), k2 = new Array(arrayLength), k3 = new Array(arrayLength);
        for (let i = dataOffset, active = k1, ai = 0; i < payloadOffset; ) {
            const a = content.charCodeAt(i++), b = content.charCodeAt(i++), c = content.charCodeAt(i++), d = content.charCodeAt(i++);
            if (!(A8f[6][a] && A8f[6][b] && A8f[6][c] && A8f[6][d])) throw new Error('Corrupted A8j characters');
            active[ai++] = A8f[1][a] | A8f[5][b];
            if (i === dataOffset + 88) { active = k3; ai = 0; }
            active[ai++] = A8f[2][b] | A8f[4][c];
            if (i === dataOffset + 44) { active = k2; ai = 0; }
            active[ai++] = A8f[3][c] | A8f[0][d];
        }
        if (payloadLength === 0) return [new Uint8Array(0), 0, k1, k2, k3];
        let resultLength = (payloadLength * 3) >> 2;
        if (content.charCodeAt(dataEndOffset - 2) === 61) resultLength -= 2;
        else if (content.charCodeAt(dataEndOffset - 1) === 61) resultLength -= 1;
        const result = new Uint8Array(resultLength);
        let off = payloadOffset, idx = 0;
        for (; off < dataEndOffset - 4; ) {
            const c1 = content.charCodeAt(off++), c2 = content.charCodeAt(off++), c3 = content.charCodeAt(off++), c4 = content.charCodeAt(off++);
            if (!(A8f[6][c1] && A8f[6][c2] && A8f[6][c3] && A8f[6][c4])) throw new Error('A8j char failure');
            result[idx++] = A8f[1][c1] | A8f[5][c2];
            result[idx++] = A8f[2][c2] | A8f[4][c3];
            result[idx++] = A8f[3][c3] | A8f[0][c4];
        }
        const u = content.charCodeAt(off++), v = content.charCodeAt(off++), w = content.charCodeAt(off++), x = content.charCodeAt(off++);
        if (!A8f[6][u] || !A8f[6][v]) throw new Error('A8j tail parsing error');
        result[idx++] = A8f[1][u] | A8f[5][v];
        if (A8f[6][w]) {
            result[idx++] = A8f[2][v] | A8f[4][w];
            if (A8f[6][x]) result[idx++] = A8f[3][w] | A8f[0][x];
            else if (x !== 61) throw new Error('A8j tail alignment error');
        } else if (w !== 61 || x !== 61) throw new Error('A8j tail padding error');
        return [result, resultLength, k1, k2, k3];
    }

    function a0F(input) {
        const result = new Array(256).fill(0).map((_, i) => i);
        const get = typeof input === 'string' ? input.charCodeAt.bind(input) : i => input[i];
        for (let c = 0, i = 0; i < 256; i++) {
            c = (c + result[i] + get(i % input.length)) % 256;
            arraySwap(result, i, c);
        }
        return result;
    }
    function a0g(key, b) {
        const result = [], g = a0F(b);
        for (let i = 0, c = 0, d = 0; i < key.length; i++) {
            c = (c + 1) % 256;
            d = (d + g[c]) % 256;
            arraySwap(g, c, d);
            result.push(key[i] ^ g[(g[c] + g[d]) % 256]);
        }
        return result;
    }
    const v_qmi = (p1, p2, p3) => a0F([...p1, ...p2, ...p3]);
    const v_smi = (content, p1, p2, p3) => a0g(content, [...p1, ...p2, ...p3]);

    function step(v7, v8, i, key, content) {
        v7 = (v7 + 1) % 256;
        v8 = (v8 + key[v7]) % 256;
        arraySwap(key, v7, v8);
        content[i] ^= key[(key[v7] + key[v8]) % 256];
        return [v7, v8];
    }
    function processContentStep(st, key, i) {
        const [content, clen, k1, k2, k3] = st;
        let v7 = 0, v8 = 0;
        for (; i >= 0; i -= 2) [v7, v8] = step(v7, v8, i, key, content);
        return [content, clen, k1, k2, k3];
    }

    function check1(n, m) { return (n & m) === m; }
    function process1(v0, v1, key) {
        for (let i = 0; i < 32; i++) { v0 = (v0 + key[i]) & 255; v1 ^= key[i]; }
        return [v0, v1];
    }
    function process2(y, u, g) {
        for (let v = y; u > y; u--, v--) arraySwap(g, u, v);
    }
    function A3b(of, st) {
        let [content, clen, k1, k2, k3] = st;
        let jki, kki, lki, mki, nki;
        switch (of) {
            case 3: jki = k1; kki = 32; lki = k2; mki = k3; nki = null; break;
            case 2: jki = k2; kki = 32; lki = k1; mki = k3; nki = null; break;
            case 1: jki = k3; kki = 32; lki = k1; mki = k2; nki = null; break;
            default: jki = content; kki = clen; lki = k1; mki = k2; nki = k3;
        }
        let [w0, x1] = process1(0, 0, lki);
        [w0, x1] = process1(w0, x1, mki);
        if (nki) [w0, x1] = process1(w0, x1, nki);
        const f2 = !check1(w0, 2), f4 = !check1(w0, 4), f8 = !check1(w0, 8);
        const s5 = x1 >>> 5, s6 = 8 - s5;
        let p7 = 0;
        const gli = [];
        for (let pli, qli, rli, sli, tli, uli, wli, xli, zli; p7 < kki; ) {
            for (
                pli = p7 + 32, qli = pli > kki,
                    qli ? ((pli = kki), (rli = pli - p7)) : (rli = 32),
                    wli = w0, xli = x1, tli = 0, uli = p7;
                tli < rli;
            ) {
                sli = jki[uli++];
                if (f2) sli = ((sli & 85) << 1) | ((sli >>> 1) & 85);
                if (f4) sli = ((sli & 51) << 2) | ((sli >>> 2) & 51);
                if (f8) sli = ((sli & 15) << 4) | ((sli >>> 4) & 15);
                gli[tli++] = sli;
                wli = (wli + sli) & 255;
                xli ^= sli;
            }
            for (let j = 0; j < rli; j++) {
                for (let i = 1; i <= 6; i++) {
                    const a = Math.pow(2, i);
                    if (!check1(j, a - 1)) break;
                    if (!check1(wli, a)) process2(j - Math.pow(2, i - 1), j, gli);
                }
            }
            zli = xli >>> 3;
            qli ? (zli %= rli) : (zli &= 31);
            if (s5 === 0) {
                for (let i = p7, j = rli - zli; i < pli; ) {
                    if (j === rli) j = 0;
                    jki[i++] = gli[j++];
                }
            } else {
                for (let i = p7, j = rli - zli - 1; i < pli; ) {
                    sli = gli[j] << s6;
                    if (++j === rli) j = 0;
                    sli |= gli[j] >>> s5;
                    jki[i++] = sli & 255;
                }
            }
            p7 = pli;
        }
        return [content, clen, k1, k2, k3];
    }

    function B0p(fk, st) {
        const [content, clen, k1, k2, k3] = st;
        const key = v_qmi(k2, fk, k3);
        for (let off = 0, omi = 0; off < clen; omi %= 256) content[off++] ^= key[omi++];
        return [content, clen, k1, k2, k3];
    }
    function A7L(fk, st) {
        const [content, clen, k1, k2, k3] = st;
        const i = (clen | 1) - 2;
        const key = v_qmi(fk, k1, k2);
        return processContentStep([content, clen, k1, k2, k3], key, i);
    }
    function A6I(fk, st) {
        const [content, clen, k1, k2, k3] = st;
        const i = (clen - 1) & -2;
        const key = v_qmi(k3, fk, k1);
        return processContentStep([content, clen, k1, k2, k3], key, i);
    }
    function A2F(st) {
        const [content, clen, k1, k2, k3] = st;
        const dmi = Math.min(32, clen);
        let a, b;
        for (let i = 0; i < dmi; i++) {
            const x = content[i] ^ k1[i] ^ k2[i] ^ k3[i];
            switch (x & 12) { case 0: a = k1[i]; break; case 4: a = k2[i]; break; case 8: a = k3[i]; break; case 12: a = content[i]; }
            switch (x & 3) {
                case 0: b = k1[i]; k1[i] = a; break;
                case 1: b = k2[i]; k2[i] = a; break;
                case 2: b = k3[i]; k3[i] = a; break;
                case 3: b = content[i]; content[i] = a;
            }
            switch (x & 12) { case 0: k1[i] = b; break; case 4: k2[i] = b; break; case 8: k3[i] = b; break; case 12: content[i] = b; }
            switch (x & 192) { case 0: a = k1[i]; break; case 64: a = k2[i]; break; case 128: a = k3[i]; break; case 192: a = content[i]; }
            switch (x & 48) {
                case 0: b = k1[i]; k1[i] = a; break;
                case 16: b = k2[i]; k2[i] = a; break;
                case 32: b = k3[i]; k3[i] = a; break;
                case 48: b = content[i]; content[i] = a;
            }
            switch (x & 192) { case 0: k1[i] = b; break; case 64: k2[i] = b; break; case 128: k3[i] = b; break; case 192: content[i] = b; }
        }
        return [content, clen, k1, k2, k3];
    }
    function B0L(fk, st) {
        let [content, clen, k1, k2, k3] = st;
        k3 = v_smi(k3, k2, k1, fk);
        k2 = v_smi(k2, k1, fk, k3);
        k1 = v_smi(k1, fk, k3, k2);
        return [content, clen, k1, k2, k3];
    }
    function tB0l(fk, st) {
        const [content, clen, k1, k2, k3] = st;
        const key = v_qmi(k3, k2, fk);
        let v7 = 0, v8 = 0;
        for (let i = 0; i < clen; i++) [v7, v8] = step(v7, v8, i, key, content);
        return [content, clen, k1, k2, k3];
    }
    function processFilename(filename) { return Array.from(new TextEncoder().encode(filename)); }
    function A6e(st) {
        const [content, clen] = st;
        return [new TextDecoder('utf-8').decode(content.slice(0, clen))];
    }
    // =====================================================================
    // 3. Tile shuffle & descramble arithmetic (A9p)
    // =====================================================================
    const B2Y_TRIPLES = JSON.parse('[[1,3,10],[1,5,16],[1,5,19],[1,9,29],[1,11,6],[1,11,16],[1,19,3],[1,21,20],[1,27,27],[2,5,15],[2,5,21],[2,7,7],[2,7,9],[2,7,25],[2,9,15],[2,15,17],[2,15,25],[2,21,9],[3,1,14],[3,3,26],[3,3,28],[3,3,29],[3,5,20],[3,5,22],[3,5,25],[3,7,29],[3,13,7],[3,23,25],[3,25,24],[3,27,11],[4,3,17],[4,3,27],[4,5,15],[5,3,21],[5,7,22],[5,9,7],[5,9,28],[5,9,31],[5,13,6],[5,15,17],[5,17,13],[5,21,12],[5,27,8],[5,27,21],[5,27,25],[5,27,28],[6,1,11],[6,3,17],[6,17,9],[6,21,7],[6,21,13],[7,1,9],[7,1,18],[7,1,25],[7,13,25],[7,17,21],[7,25,12],[7,25,20],[8,7,23],[8,9,23],[9,5,14],[9,5,25],[9,11,19],[9,21,16],[10,9,21],[10,9,25],[11,7,12],[11,7,16],[11,17,13],[11,21,13],[12,9,23],[13,3,17],[13,3,27],[13,5,19],[13,17,15],[14,1,15],[14,13,15],[15,1,29],[17,15,20],[17,15,23],[17,15,26]]');
    const XSHIFT = [
        (p1, p2, p3, p4) => { p1 ^= p1 << p2; p1 ^= p1 >>> p3; p1 ^= p1 << p4; return p1; },
        (p1, p2, p3, p4) => { p1 ^= p1 << p4; p1 ^= p1 >>> p3; p1 ^= p1 << p2; return p1; },
        (p1, p2, p3, p4) => { p1 ^= p1 >>> p2; p1 ^= p1 << p3; p1 ^= p1 >>> p4; return p1; },
        (p1, p2, p3, p4) => { p1 ^= p1 >>> p4; p1 ^= p1 << p3; p1 ^= p1 >>> p2; return p1; },
        (p1, p2, p3, p4) => { p1 ^= p1 << p2; p1 ^= p1 << p4; p1 ^= p1 >>> p3; return p1; },
        (p1, p2, p3, p4) => { p1 ^= p1 >>> p2; p1 ^= p1 >>> p4; p1 ^= p1 << p3; return p1; },
    ];
    const B2Y_SEED = 2463534242;
    class B2y {
        constructor() {
            this.vk = 0; this.j = B2Y_SEED;
            this.l = B2Y_TRIPLES[74][this.vk++];
            this.m = B2Y_TRIPLES[74][this.vk++];
            this.n = B2Y_TRIPLES[74][this.vk++];
            this.f = XSHIFT[0];
        }
        b9es(E, L) {
            this.j = B2Y_SEED;
            const p = B2Y_TRIPLES[E];
            this.l = p[0]; this.m = p[1]; this.n = p[2]; this.f = XSHIFT[L];
        }
        B0o(p1) { const r = p1 >>> 0; this.j = r || B2Y_SEED; }
        b4K(p1) {
            if (p1 <= 1) return 0;
            const vv = 4294967295 - p1;
            let u = this.j, t, s;
            do {
                u = this.f(u, this.l, this.m, this.n) >>> 0;
                t = u - 1;
                s = t % p1;
            } while (vv < t - s);
            this.j = u;
            return s;
        }
    }
    B2y.b6o = B2Y_TRIPLES.length;
    B2y.b6b = XSHIFT.length;
    B2y.b4v = B2y.b6o * B2y.b6b;

    function v_mqg(fn, total) {
        const o = [];
        for (let i = 0; i < total; i++) { const n = fn(i + 1); o[i] = o[n]; o[n] = i; }
        return o;
    }
    function v_6qg(fn, v) { return v < 4 ? fn(v + 1) : fn(v - 1) + 1; }
    function v_7qg(fn, ye, ee) { if (ee <= 0) return 0; const r = fn(ee); return r < ye ? r : r + 1; }
    function v_9qg(fn, p2, p3, p4, p5, p6, p7) {
        for (let a, b, c, d = p6, e = p7, f = p4, g = p5, h = 0, i = 0, j = -1; d + e > 0; ) {
            const k = 0, l = j;
            a = fn(d + e);
            if (a < d) {
                if (a < f) {
                    for (b = i; b > k && !(h >= p2[b + l]); b--);
                    for (c = i + e; c < p7 && !(h >= p2[c]); c++);
                    p3[h] = fn(c - b) + b;
                    h++; f--;
                } else {
                    for (b = i; b > k && !(h + d <= p2[b + l]); b--);
                    for (c = i + e; c < p7 && !(h + d <= p2[c]); c++);
                    p3[h + d + l] = fn(c - b) + b;
                }
                d--;
            } else {
                if (a - d < g) {
                    for (b = h; b > k && !(i >= p3[b + l]); b--);
                    for (c = h + d; c < p6 && !(i >= p3[c]); c++);
                    p2[i] = fn(c - b) + b;
                    i++; g--;
                } else {
                    for (b = h; b > k && !(i + e <= p3[b + l]); b--);
                    for (c = h + d; c < p6 && !(i + e <= p3[c]); c++);
                    p2[i + e + l] = fn(c - b) + b;
                }
                e--;
            }
        }
    }
    function v_qpg(p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13) {
        const result = [], q1 = p1 + 1, q2 = p2 + 1, q3 = q1 << 1, q4 = q2 << 1;
        for (let v = 0; v < p1; v++) for (let w = 0; w < p2; w++) {
            const z = p3[v + w * p1], x = z % p1, y = (z - x) / p1;
            const r = v < p11[w] ? v : v + q1;
            const s = w < p10[v] ? w : w + q2;
            const t = x < p7[y] ? x : x + q1;
            const u = y < p6[x] ? y : y + q2;
            result.push(u * q3 + r);
            result.push(t * q4 + s);
        }
        result.push(p9 * q3 + p12);
        result.push(p8 * q4 + p13);
        for (let v = 0; v < p1; v++) {
            const x = p4[v], r = v < p12 ? v : v + q1, t = x < p8 ? x : x + q1;
            result.push(p6[x] * q3 + r);
            result.push(t * q4 + p10[v]);
        }
        for (let w = 0; w < p2; w++) {
            const y = p5[w], s = w < p13 ? w : w + q2, u = y < p9 ? y : y + q2;
            result.push(u * q3 + p11[w]);
            result.push(p7[y] * q4 + s);
        }
        return result;
    }
    function a3f(p1, p2, p3, p4) {
        const tog = new B2y();
        const uog = p2 ^ p3 ^ p4;
        const vog = Math.floor(p1 / 65536);
        const wog = Math.floor(p2 / 65536);
        const xog = Math.floor(p3 / 65536);
        const yog = Math.floor(p4 / 65536);
        const zo = B2y.b6o, zp = B2y.b6b;
        let q1 = wog ^ xog ^ yog, q2 = vog ^ yog, q3 = p1 ^ p2, q4 = p1 ^ p3, q5 = p1 ^ p4;
        q1 >>>= 16;
        const r6 = q1 % zp, r7 = ((q1 - r6) / zp) % zo;
        const b4k = tog.b4K.bind(tog);
        tog.b9es(r7, r6);
        tog.B0o(uog);
        const r9 = b4k(65536) | (b4k(65536) << 16);
        const apg = b4k(512);
        const bpg = wog >>> 16, cpg = xog >>> 16;
        q2 = (q2 >>> 16) ^ apg;
        q3 = (q3 ^ r9) >>> 0;
        q4 = (q4 ^ r9) >>> 0;
        q5 = (q5 ^ r9) >>> 0;
        const dpg = q2 % zp, epg = ((q2 - dpg) / zp) % zo;
        tog.b9es(epg, dpg);
        tog.B0o(q3);
        const fpg = v_mqg(b4k, bpg * cpg);
        tog.B0o(q4);
        const gpg = v_6qg(b4k, bpg), hpg = v_6qg(b4k, cpg);
        const ipg = v_7qg(b4k, gpg, bpg), jpg = v_7qg(b4k, hpg, cpg);
        tog.B0o(q5);
        const kpg = [], lpg = [];
        v_9qg(b4k, kpg, lpg, gpg, hpg, bpg, cpg);
        const mpg = v_mqg(b4k, bpg), npg = v_mqg(b4k, cpg);
        const opg = [], ppg = [];
        v_9qg(b4k, ppg, opg, ipg, jpg, bpg, cpg);
        return v_qpg(bpg, cpg, fpg, mpg, npg, opg, ppg, ipg, jpg, lpg, kpg, gpg, hpg);
    }
    function A9p(page, width, height) {
        const bw = page.b8A, bh = page.b6V;
        const r = page.B0J, s = page.B0K, t = page.B0n, u = page.B0A;
        const vo = B2y.b6o, wo = B2y.b6b;
        const bx = Math.floor(width / bw), by = Math.floor(height / bh);
        const lbw = width % bw, lbh = height % bh;
        const d14 = (bx + 1) << 1, d24 = (by + 1) << 1;
        const lxvs = (bx + 1) * bw - lbw, lyvs = (by + 1) * bh - lbh;
        const b54 = new B2y();
        const b64 = u ^ bx ^ by;
        const b74 = b64 % wo, b84 = ((b64 - b74) / wo) % vo;
        const out = [];
        b54.b9es(b84, b74);
        b54.B0o(r ^ s ^ t);
        const b94 = b54.b4K(65536) + b54.b4K(65536) * 65536 + b54.b4K(512) * 4294967296;
        const a4j = bx * 4294967296 + r, b4j = by * 4294967296 + s, c4j = u * 4294967296 + t;
        const d4j = a3f(b94, a4j, b4j, c4j);
        const e4j = (index, total, sbw, sbh) => {
            if (sbw !== 0 && sbh !== 0) for (; index < total; ) {
                const f = d4j[index++], g = d4j[index++];
                const h = f % d14, i = g % d24;
                const j = (g - i) / d24, k = (f - h) / d14;
                out.push({
                    srcX: h * bw - (h > bx ? lxvs : 0),
                    srcY: i * bh - (i > by ? lyvs : 0),
                    destX: j * bw - (j > bx ? lxvs : 0),
                    destY: k * bh - (k > by ? lyvs : 0),
                    width: sbw, height: sbh,
                });
            }
        };
        let x = 0, y = bx * by * 2;
        e4j(x, y, bw, bh);
        x = y; y += 2;
        e4j(x, y, lbw, lbh);
        x = y; y += bx * 2;
        e4j(x, y, bw, lbh);
        x = y; y += by * 2;
        e4j(x, y, lbw, bh);
        return out;
    }
    function pageSeedsNo(pageId, pageConfig, k1, k2, k3, no) {
        const list = pageConfig.FileLinkInfo.PageLinkInfoList;
        const Page = (list[no] && list[no].Page) || list[0].Page;
        const NS = Page.NS, PS = Page.PS, RS = Page.RS, No = Page.No;
        let v0 = 47;
        for (let i = 0; i < pageId.length; i++) v0 += pageId.charCodeAt(i);
        const fn = No.toString(10);
        for (let i = 0; i < fn.length; i++) v0 += fn.charCodeAt(i);
        v0 += k1.reduce((a, b) => a + b, 0) + k2.reduce((a, b) => a + b, 0) + k3.reduce((a, b) => a + b, 0);
        let v9 = v0 & 255;
        v9 |= v9 << 8;
        v9 |= v9 << 16;
        function xorHash(key) {
            let nhf = 0, ohf = key.length & -4;
            if (ohf > 32) ohf = 32;
            for (let phf = 0; phf < ohf; ) {
                nhf ^= key[phf++] << 24;
                nhf ^= key[phf++] << 16;
                nhf ^= key[phf++] << 8;
                nhf ^= key[phf++] << 0;
            }
            return nhf >>> 0;
        }
        const noDescramble = NS === null || NS === undefined || PS === null || PS === undefined || RS === null || RS === undefined;
        return {
            B0A: v0 % B2y.b4v,
            B0J: (v9 ^ xorHash(k1) ^ (NS || 0)) >>> 0,
            B0K: (v9 ^ xorHash(k2) ^ (PS || 0)) >>> 0,
            B0n: (v9 ^ xorHash(k3) ^ (RS || 0)) >>> 0,
            b8A: Page.BlockWidth,
            b6V: Page.BlockHeight,
            Size: Page.Size,
            noDescramble,
        };
    }

    // =====================================================================
    // 4. Page image filename token
    // =====================================================================
    function v_jdf(filename) {
        const n = parseInt(filename, 10);
        if (!isNaN(n) && n >= 0 && n <= 1152921504606847000) {
            const h = n.toString(16);
            return h.length.toString(16) + h;
        }
        return '0' + filename;
    }
    function v_hdf(k1, k2, k3) {
        const out = [];
        out.length = Math.max(k1.length, k2.length, k3.length);
        for (let i = 0; i < out.length; i++) out[i] = 0;
        for (let i = 0; i < k1.length; i++) out[i] ^= k1[i];
        for (let i = 0; i < k2.length; i++) out[i] ^= k2[i];
        for (let i = 0; i < k3.length; i++) out[i] ^= k3[i];
        return out;
    }
    const vval = (value) => (value < 10 ? 48 : 87) + value;
    function v_ndf(b9w, pageId, fileName) {
        const parentFolder = pageId + '/';
        const pathLength = parentFolder.length + fileName.length;
        const v_bef = (1 + pathLength) << 1;
        const cef = new Array(v_bef);
        cef[0] = 0; cef[1] = 59;
        const def = String.prototype.charCodeAt.bind(parentFolder + fileName);
        for (let p = 2, o = 0; o < pathLength; o++) {
            const s = def(o);
            cef[p++] = s >>> 8;
            cef[p++] = s % 256;
        }
        let fef = 3;
        for (let eef = (fileName.length << 1) + v_bef + v_bef; eef < 256; fef++) eef += v_bef;
        let jef = 1670739, kef = 1282576, lef = 2237221;
        for (let i = (1 + parentFolder.length) << 1, j = 0, k = 0; k < fef; k++, i = 0) {
            for (; i < v_bef; ) {
                lef ^= cef[i++] ^ b9w[j++];
                const ief = 435 * lef;
                const hef = 435 * kef + ((lef & 7) << 18) + (ief >>> 22);
                const gef = 435 * jef + ((kef & 3) << 19) + ((lef & 4194296) >>> 3) + (hef >>> 21);
                lef = ief & 4194303;
                kef = hef & 2097151;
                jef = gef & 2097151;
                j >= b9w.length && (j = 0);
            }
        }
        const mef = new Array(16);
        const pval = (idx, value) => { mef[idx] = vval(value >>> 4); mef[idx + 1] = vval(value & 15); };
        pval(0, (jef >>> 13) ^ b9w[0]);
        pval(2, ((jef >>> 5) & 255) ^ b9w[1]);
        pval(4, (((jef & 31) << 3) | (kef >>> 18)) ^ b9w[2]);
        pval(6, ((kef >>> 10) & 255) ^ b9w[3]);
        pval(8, ((kef >>> 2) & 255) ^ b9w[4]);
        pval(10, (((kef & 3) << 6) | (lef >>> 16)) ^ b9w[5]);
        pval(12, ((lef >>> 8) & 255) ^ b9w[6]);
        pval(14, (lef & 255) ^ b9w[7]);
        return String.fromCharCode(...mef);
    }
    function b8gNo(pageId, k1, k2, k3, no) {
        const fname = String(no == null ? 0 : no);
        return pageId + '/' + v_jdf(fname) + v_ndf(v_hdf(k1, k2, k3), pageId, fname) + '.jpeg';
    }

    // =====================================================================
    // 5. Auth helpers
    // =====================================================================
    function isPublicBootstrapPage() {
        try { return !!(window.__BWDD_CLI__ && window.__BWDD_CLI__.publicBootstrap); } catch (_) { return false; }
    }
    function isPublicFreeBootstrapPage() {
        try { return !!(window.__BWDD_CLI__ && window.__BWDD_CLI__.publicBootstrap &&
            window.__BWDD_CLI__.publicBootstrap.route === 'free'); } catch (_) { return false; }
    }
    function getU1() {
        if (isHeadlessPage() && !isPublicBootstrapPage()) return '';
        const m = document.cookie.match(/(?:^|;\s*)u1=([^;]+)/);
        return m ? decodeURIComponent(m[1]) : '';
    }
    function generatedBid() {
        // The native viewer mints this value client-side and persists it under
        // localStorage['NFBR.Global/BrowserId']; the observed shape is
        // <epoch-ms><8 digits>NFBR and the server accepts a self-minted one
        // (verified against /trial-page/c with status 200). When the viewer
        // engine has not run yet, mint the same shape instead of refusing.
        if (!headlessBid) {
            headlessBid = (state.auth && state.auth.bid) ||
                (Date.now() + '' + Math.floor(Math.random() * 1e8) + 'NFBR');
        }
        return headlessBid;
    }
    function getBID() {
        if (isHeadlessPage() && !isPublicBootstrapPage()) return generatedBid();
        try { const v = localStorage.getItem('NFBR.Global/BrowserId'); if (v) return v; } catch (e) {}
        if (state.auth && state.auth.bid) return state.auth.bid;
        return generatedBid();
    }
    function authQuery(auth) {
        const p = new URLSearchParams();
        for (const k of AUTH_PARAM_KEYS) {
            if (auth[k] !== undefined && auth[k] !== null) p.set(k, auth[k]);
        }
        return p.toString();
    }

    // =====================================================================
    // 6. Worker Pool & Descramble Engine
    // =====================================================================
    function buildWorkerSource() {
        const deps = [
            'const AUTH_PARAM_KEYS = ' + JSON.stringify(AUTH_PARAM_KEYS) + ';',
            'const B2Y_TRIPLES = ' + JSON.stringify(B2Y_TRIPLES) + ';',
            'const XSHIFT = [' + XSHIFT.map(f => f.toString()).join(',') + '];',
            'const B2Y_SEED = 2463534242;',
            B2y.toString(),
            'B2y.b6o = ' + B2y.b6o + ';',
            'B2y.b6b = ' + B2y.b6b + ';',
            'B2y.b4v = ' + B2y.b4v + ';',
            v_mqg.toString(),
            v_6qg.toString(),
            v_7qg.toString(),
            v_9qg.toString(),
            v_qpg.toString(),
            a3f.toString(),
            A9p.toString(),
            workerMain.toString(),
            'workerMain();',
        ];
        return deps.join('\n');
    }

    const WORKER_BATCH_SIZE = 2;

    function workerBatchSize(type) {
        // JPEG is the default and benefits from two overlapping codec jobs.
        // Lossless WebP/PNG encoders have much higher peak memory/CPU cost, so
        // keep a conservative single-page queue for those formats.
        return type === 'image/jpeg' ? WORKER_BATCH_SIZE : 1;
    }

    function workerMain() {
        let crcTable = null;
        async function crcForZip(blob) {
            if (!crcTable) {
                crcTable = new Int32Array(256);
                for (let n = 0; n < 256; n++) {
                    let c = n;
                    for (let k = 0; k < 8; k++) c = (c & 1) ? (0xEDB88320 ^ (c >>> 1)) : (c >>> 1);
                    crcTable[n] = c;
                }
            }
            const bytes = new Uint8Array(await blob.arrayBuffer());
            let crc = -1;
            for (let i = 0; i < bytes.length; i++) {
                crc = (crc >>> 8) ^ crcTable[(crc ^ bytes[i]) & 255];
            }
            return (crc ^ -1) >>> 0;
        }
        async function processPage(data) {
            const { id, relPath, seeds, auth, baseUrl, q, fmt, timeoutMs, needCrc, blob: inputBlob } = data;
            const outType = fmt || 'image/jpeg';
            try {
                let blob = inputBlob;
                if (!blob) {
                    const qs = new URLSearchParams();
                    for (const k of AUTH_PARAM_KEYS) {
                        if (auth[k] !== undefined && auth[k] !== null) qs.set(k, auth[k]);
                    }
                    const url = baseUrl + relPath + '?' + qs.toString();
                    let res = null, lastErr = null;
                    for (let attempt = 0; attempt < 3; attempt++) {
                        const ctrl = new AbortController();
                        const timer = setTimeout(() => ctrl.abort(), timeoutMs || 60000);
                        try {
                            res = await fetch(url, { credentials: 'omit', signal: ctrl.signal });
                            if (res && res.ok) {
                                try { blob = await res.blob(); }
                                catch (e) { lastErr = e; res = null; }
                            }
                        } catch (e) {
                            lastErr = e;
                            res = null;
                        } finally {
                            clearTimeout(timer);
                        }
                        if (res && (res.ok || res.status === 403)) break;
                        await new Promise(r => setTimeout(r, 1200 * (attempt + 1)));
                    }
                    if (res && res.status === 403) return { id, error: 'auth-expired' };
                    if (!res) throw lastErr || new Error('fetch failed after retries');
                    if (!res.ok) throw new Error('HTTP ' + res.status);
                }
                const bmp = await createImageBitmap(blob);
                const W = bmp.width, H = bmp.height;
                const S = seeds.Size;
                const needsScale = !!(S && S.Width && S.Height && (W !== S.Width || H !== S.Height));
                const needsTiles = !seeds.noDescramble;
                if (!needsTiles && !needsScale && outType === 'image/jpeg' && blob.type === 'image/jpeg') {
                    // Nothing has to change about this page. Decoding and
                    // re-encoding it costs ~57ms on a 1600x2400 scan (measured)
                    // to produce a slightly worse copy of the bytes we already
                    // hold, so hand the original straight back.
                    if (bmp.close) bmp.close();
                    const unchanged = { id, blob };
                    if (needCrc) unchanged.crc = await crcForZip(blob);
                    return unchanged;
                }
                const canvas = new OffscreenCanvas(W, H);
                const ctx = canvas.getContext('2d');
                if (needsTiles) {
                    // Blit each tile straight from the decoded bitmap into its
                    // destination rect. The previous version pulled the whole
                    // frame back with getImageData, copied the tiles in JS and
                    // pushed it back with putImageData, about 46MB of avoidable
                    // memory traffic per page, which is what stopped the decoder
                    // keeping up with the fetcher. Measured 2.08x on 14 cores.
                    for (const t of A9p(seeds, W, H)) {
                        ctx.drawImage(bmp, t.destX, t.destY, t.width, t.height,
                            t.srcX, t.srcY, t.width, t.height);
                    }
                } else {
                    ctx.drawImage(bmp, 0, 0);
                }
                if (bmp.close) bmp.close();
                let outCanvas = canvas;
                if (needsScale) {
                    outCanvas = new OffscreenCanvas(S.Width, S.Height);
                    outCanvas.getContext('2d').drawImage(canvas, 0, 0);
                }
                let outBlob;
                if (typeof outCanvas.convertToBlob === 'function') {
                    outBlob = await outCanvas.convertToBlob({ type: outType, quality: q });
                } else {
                    outBlob = await new Promise((res2, rej) => outCanvas.toBlob(b => b ? res2(b) : rej(new Error('toBlob')), outType, q));
                }
                const result = { id, blob: outBlob };
                if (needCrc) result.crc = await crcForZip(outBlob);
                return result;
            } catch (e) {
                const msg = safeLogText((e && e.message) || e);
                return { id, error: /abor/i.test(msg) ? 'timeout' : msg };
            }
        }

        self.onmessage = async (ev) => {
            const isBatch = Array.isArray(ev.data.jobs);
            const jobs = isBatch ? ev.data.jobs : [ev.data];
            // processPage allocates an independent bitmap/canvas per item, so
            // Promise.all overlaps codec work without sharing mutable surfaces.
            // Acknowledge each result as soon as it finishes: if a sibling hangs,
            // the pool can commit this page and time out only the unfinished one.
            if (!isBatch) {
                self.postMessage(await processPage(ev.data));
                return;
            }
            await Promise.all(jobs.map(async job => {
                const result = await processPage(job);
                self.postMessage({ batchId: ev.data.batchId, result });
            }));
        };
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


    async function decodeBlobMain(blob, seeds, q, fmt) {
        // Same approach as workerMain: blit tiles straight from the decoded
        // bitmap instead of round-tripping the frame through getImageData.
        const codec = fmt ? { type: fmt, ext: IMAGE_CODEC.ext } : IMAGE_CODEC;
        const bmp = await createImageBitmap(blob);
        const W = bmp.width, H = bmp.height;
        const S = seeds.Size;
        const needsScale = !!(S && S.Width && S.Height && (W !== S.Width || H !== S.Height));
        const needsTiles = !seeds.noDescramble;
        if (!needsTiles && !needsScale && codec.type === 'image/jpeg' && blob.type === 'image/jpeg') {
            if (bmp.close) bmp.close();
            return blob;
        }
        const canvas = document.createElement('canvas');
        canvas.width = W;
        canvas.height = H;
        const ctx = canvas.getContext('2d');
        if (needsTiles) {
            for (const t of A9p(seeds, W, H)) {
                ctx.drawImage(bmp, t.destX, t.destY, t.width, t.height,
                    t.srcX, t.srcY, t.width, t.height);
            }
        } else {
            ctx.drawImage(bmp, 0, 0);
        }
        if (bmp.close) bmp.close();
        let outCanvas = canvas;
        if (needsScale) {
            outCanvas = document.createElement('canvas');
            outCanvas.width = S.Width;
            outCanvas.height = S.Height;
            outCanvas.getContext('2d').drawImage(canvas, 0, 0);
        }
        return await new Promise((res2, rej) =>
            outCanvas.toBlob(b => b ? res2(b) : rej(new Error('toBlob')), codec.type, q));
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
    function cdnBaseCandidates(fileKey, relPath) {
        const out = [];
        const add = (u) => { if (u && out.indexOf(u) === -1) out.push(u); };
        if (fileKey && state.fileBases && state.fileBases[fileKey]) add(state.fileBases[fileKey]);
        if (state.baseUrl) {
            const m = state.baseUrl.match(/^(.*?\/SVGA\/)(?:[^/]+\/)?$/);
            if (m) {
                // Pick the variant this rel actually lives in FIRST. Captures:
                // cover/front-matter/shared pages sit under SVGA/shared while
                // the body pages sit under SVGA/normal_default, a mismatched
                // first guess 403s and (in the old code) stalled the whole run
                // on breaker cooldowns. Guessing right means the first probe
                // usually 200s.
                const isShared = /(^|\/)shared\//.test(relPath || '');
                const variants = isShared ? ['shared', 'normal_default'] : ['normal_default', 'shared'];
                for (const v of variants) add(m[1] + v + '/');
            }
            add(state.baseUrl);
        }
        return out;
    }
    async function cdnFetchWithFallback(relPath, fileKey, timeoutMs) {
        const bases = cdnBaseCandidates(fileKey, relPath);
        let lastErr = null;
        for (let bi = 0; bi < bases.length; bi++) {
            try {
                const res = await cdnFetch((attempt) => {
                    const base = bases[bi] + relPath + '?' + authQuery(state.auth);
                    // Only retries carry a cache-buster, so the first attempt
                    // stays byte-identical to what the viewer itself requests.
                    return attempt > 0 ? base + '&_bwr=' + attempt + '-' + Date.now().toString(36) : base;
                }, timeoutMs || 45000);
                // Remember which base dir actually served this page family so
                // later pages skip the probe chain entirely (state.fileBases is
                // reset per run in resetRunState).
                if (fileKey && state.fileBases && !state.fileBases[fileKey]) state.fileBases[fileKey] = bases[bi];
                return res;
            } catch (e) {
                lastErr = e;
                // 403 with a still-valid policy = this base-dir guess does not
                // host the file (wrong SVGA variant). That is NOT a rate limit:
                // move to the next candidate immediately, no breaker, no auth
                // churn. (Genuinely expired policies are retried inside
                // cdnFetch, and prefetchOne rotates auth when every candidate
                // path-denies.)
                if (e && e.pathDenied) continue;
                if (breakerOpen()) {
                    await waitOutCooldown();
                    try { await refreshAuthBest(); } catch (e2) {}
                }
            }
        }
        throw lastErr || new Error('All variant endpoints failed for ' + relPath);
    }

    async function cdnFetch(urlBuilder, timeoutMs) {
        await waitOutCooldown();
        // Policy-clock renewal: every /browserWebApi/pb response mints a
        // CloudFront policy whose DateLessThan is ~60 s out (verified on all
        // live captures), and no capture shows a per-policy *request* quota on
        // valid paths. Refresh when the current policy is about to lapse OR the
        // legacy request-count budget trips; count alone was refreshing far too
        // eagerly during 128-wide bursts.
        if ((!authLooksFresh() || reqsSinceAuth >= REQS_PER_POLICY_RENEW) && authRefreshPromise === null) {
            try {
                const before = authPolicySig();
                await refreshAuthBest();
                if (authPolicySig() !== before) reqsSinceAuth = 0;
            } catch (e) {}
        }
        let lastStatus = 0;
        let lastErr = null;
        for (let attempt = 0; attempt < 3; attempt++) {
            let res = null, err = null;
            try {
                res = await laneFetch(urlBuilder(attempt), timeoutMs || 45000);
            } catch (e) { err = e; }
            const status = res ? res.status : 0;
            reqsSinceAuth++;
            if (res && res.ok) {
                consecutiveBlocks = 0;
                return res;
            }
            lastStatus = status; lastErr = err;
            if (status === 403) {
                // A 403 while the policy still has runway is a PATH denial: this
                // base-dir guess does not host the file (captures show the same
                // token 200s under .../SVGA/shared while bare .../SVGA 403s
                // forever). Refreshing auth cannot fix a wrong path and must not
                // trip the global breaker, so signal pathDenied. Only a lapsed
                // policy is rotated and retried first.
                if (!authLooksFresh() && attempt < 2) {
                    const before = authPolicySig();
                    try { await refreshAuthBest(); } catch (e2) {}
                    if (authPolicySig() !== before) { reqsSinceAuth = 0; continue; }
                }
                // A fresh policy that still 403s is usually BookWalker's cached S3
                // error page for one object, per-URL and transient (in a
                // 308-request capture every 403 cleared on a plain retry), not a
                // path denial. One jittered retry before concluding the path
                // is wrong, so one bad edge entry cannot cost a whole page. The
                // retry carries a cache-buster: the signed policy's Resource is
                // a path wildcard, so the query string is not part of the
                // signature and the extra param cannot invalidate it.
                if (attempt === 0) {
                    await sleepMs(120 + Math.random() * 240);
                    continue;
                }
                const e2 = new Error('CDN denied path (Status: 403)');
                e2.status = 403;
                e2.pathDenied = true;
                throw e2;
            }
            const blocked = corsLikeError(err, status);
            if (blocked) {
                if (attempt < 2) { await sleepMs(1200 * (attempt + 1)); continue; }
                tripBreaker();
                const e2 = new Error('CDN rate limiter reached (Status: ' + status + ')');
                e2.status = status;
                throw e2;
            }
            if (res) { const e2 = new Error('HTTP ' + status); e2.status = status; throw e2; }
            throw (err || new Error('CDN request failed'));
        }
        const e4 = new Error('Retries exhausted for CDN slice (Last status: ' + lastStatus + ')');
        e4.status = lastStatus;
        throw e4;
    }
    function effectiveBurst(base) {
        if (consecutiveBlocks === 0) return base;
        return Math.max(4, Math.floor(base / (consecutiveBlocks + 1)));
    }
    function authPolicySig() {
        try { return (state.auth && state.auth['Policy'] || '') + '|' + (state.auth && state.auth['Signature'] || ''); }
        catch (e) { return ''; }
    }

    async function fetchAndDescramble(relPath, seeds, q, timeoutMs, fmt) {
        const res = await cdnFetch(() => state.baseUrl + relPath + '?' + authQuery(state.auth), timeoutMs || 60000);
        if (!res.ok) throw new Error('HTTP error ' + res.status);
        const blob = await res.blob();
        return await decodeBlobMain(blob, seeds, q, fmt);
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
    // 9. Cross-store availability ("also available on ...")
    // =====================================================================
    // Asks each store's own search page whether it carries the book and links
    // to that store's product page - never to a viewer. The stores are external
    // facts rather than adapter concerns, so they live here as a catalog; the
    // module is in the combined target ("Omnimanga Native Downloader") only, so
    // the single-store scripts carry none of these hosts either.
    //
    // Matching is necessarily fuzzy (BookWalker appends the imprint in brackets,
    // ebookjapan wraps the whole card in one anchor), so it is scored in tiers
    // (exact > prefix > contains) and reported honestly: a confirmed match links
    // to the product page, anything else to the store's search.
    const AVAILABILITY_STORES = [
        {
            id: 'bookwalker', siteId: 'bookwalker', label: 'BookWalker', short: 'B',
            color: '#0f7dc4', origin: 'https://bookwalker.jp', hosts: ['bookwalker.jp'],
            search: (q) => 'https://bookwalker.jp/search/?word=' + encodeURIComponent(q),
            // /series/<id>/ lists every volume, so prefer it over a /de<uuid> page.
            product: (p) => /^\/series\/\d+\//.test(p) || /^\/de[0-9a-f-]{6,}\/?$/i.test(p),
            rank: (p) => (/^\/series\//.test(p) ? 0.5 : 0),
            // One card per edition, each with its own price; a 0-yen card is
            // the free 無料お試し版 and also says 無料で読む. Volumes 8 and 6 each
            // exist as 通常版 and 特装版, so a volume can have several rows.
            volumes: (doc) => {
                const out = [];
                for (const a of doc.querySelectorAll('a.m-book-item__title')) {
                    const title = (a.getAttribute('title') || a.textContent || '').trim();
                    let url = '';
                    try { url = new URL(a.getAttribute('href') || '', 'https://bookwalker.jp/').href; } catch (e) { continue; }
                    let num = null, free = false, row = a;
                    for (let i = 0; i < 6 && row; i++, row = row.parentElement) {
                        const el = row.querySelector('.m-book-item__price-num');
                        if (!el) continue;
                        const n = parseInt(String(el.textContent).replace(/[^0-9]/g, ''), 10);
                        num = isFinite(n) ? n : null;
                        free = /無料で読む/.test(row.textContent || '') || num === 0;
                        break;
                    }
                    out.push({ title: title, url: url, vol: extractVolumeNumber(title), price: num, free: free, until: '' });
                }
                return out;
            },
        },
        {
            id: 'cmoa', siteId: 'cmoa', label: 'CMOA', short: 'C',
            color: '#e2574c', origin: 'https://www.cmoa.jp', hosts: ['cmoa.jp'],
            search: (q) => 'https://www.cmoa.jp/search/result/?search_word=' + encodeURIComponent(q),
            product: (p) => /^\/title\/\d+\/?/.test(p),
            rank: () => 0,
            // A free volume keeps its regular 720pt/792円(税込) price on the same
            // row, so "free" must be read from the 無料で読む block, never from the
            // price. The expiry ("9/27まで") rides along in the same block.
            volumes: (doc) => {
                const out = [];
                for (const row of doc.querySelectorAll('.title_vol_vox_vols_i')) {
                    const a = row.querySelector('h3.title_details_title_name_h2 a') || row.querySelector('a[href*="/title/"]');
                    const img = row.querySelector('img[alt]');
                    const title = ((a && a.textContent) || (img && img.getAttribute('alt')) || '').trim();
                    let url = '';
                    if (a) { try { url = new URL(a.getAttribute('href') || '', 'https://www.cmoa.jp/').href; } catch (e) {} }
                    // GA_free alone is NOT a free marker: every volume row also
                    // carries an empty <div class="title_vol_each_free_btn GA_free">
                    // placeholder, so matching the class marks the whole series free.
                    // A free volume is one whose free button says something, or
                    // whose row shows a 0 price.
                    let freeEl = null;
                    for (const el of row.querySelectorAll('.GA_free')) {
                        if ((el.textContent || '').trim()) { freeEl = el; break; }
                    }
                    const markEl = row.querySelector('.mark .em');
                    const zeroMarked = !!markEl && (markEl.textContent || '').replace(/[^0-9]/g, '') === '0';
                    let until = '';
                    if (freeEl) {
                        for (const sp of freeEl.querySelectorAll('span')) {
                            const t = (sp.textContent || '').trim();
                            if (/まで/.test(t)) until = t;
                        }
                    }
                    let price = null;
                    const point = row.querySelector('.price .point');
                    if (point) {
                        const m = /([0-9][0-9,]*)円/.exec(point.textContent || '');
                        if (m) price = parseInt(m[1].replace(/,/g, ''), 10);
                    }
                    let vol = NaN;
                    const vm = /\/vol\/([0-9]+)\//.exec(url);
                    if (vm) vol = parseInt(vm[1], 10);
                    if (!isFinite(vol) || !vol) vol = extractVolumeNumber(title);
                    out.push({ title: title, url: url, vol: vol, price: price, free: !!(freeEl || zeroMarked), until: until });
                }
                return out;
            },
        },
        {
            id: 'ebookjapan', siteId: 'ebookjapan', label: 'ebookjapan', short: 'e',
            color: '#e8820c', origin: 'https://ebookjapan.yahoo.co.jp', hosts: ['ebookjapan.yahoo.co.jp'],
            search: (q) => 'https://ebookjapan.yahoo.co.jp/search/?keyword=' + encodeURIComponent(q),
            product: (p) => /^\/books\/\d+\/?/.test(p),
            rank: () => 0,
            // ebookjapan is a Vue app: its series and search pages carry no
            // server-rendered prices or per-volume rows at all, so the only
            // price/free fact available is the campaign badge on the search
            // card ("2冊無料"). Everything else stays blank rather than guessed.
            freeBadge: (html) => {
                const all = [];
                const re = /([0-9]+)\s*冊無料/g;
                let m;
                while ((m = re.exec(String(html || '')))) all.push(parseInt(m[1], 10));
                return all.length ? Math.max.apply(null, all) : 0;
            },
        },
    ];
    // One lookup per title per page: the panel re-renders, the answers do not.
    const availabilityMemory = new Map();
    // One shared in-flight promise per key: the boot poll often asks again while
    // the first round-trip is still running, and the same three stores must not
    // be queried twice.
    const availabilityInflight = new Map();
    const AVAILABILITY_CACHE_MAX = 50;

    // A viewer's document title often carries the shop's own branding
    // ("... | BOOK☆WALKER"); searching for that finds nothing.
    function cleanStoreSeed(t) {
        let s = String(t || '');
        s = s.replace(/[\s|｜\-\u2013\u2014]*(?:BOOK\s*[☆★]?\s*WALKER|ブックウォーカー|ebookjapan|イーブックジャパン|コミックシーモア|CMOA|シーモア)\s*$/i, '');
        s = s.replace(/[\s|｜\-\u2013\u2014]+$/, '');
        return s.trim();
    }

    function availabilityNorm(s) {
        return String(s || '')
            .replace(/[\s\u3000]+/g, '')
            .replace(/[（）()【】\[\]「」『』]/g, '')
            .toLowerCase();
    }

    function availabilityScore(anchorText, candidates, bonus) {
        const t = availabilityNorm(anchorText);
        if (!t) return null;
        let tier = 0;
        for (const cand of candidates) {
            const n = availabilityNorm(cand);
            if (n.length < 3) continue;
            if (t === n) tier = Math.max(tier, 3);
            else if (t.startsWith(n)) tier = Math.max(tier, 2);
            // A bare "contains" is the only signal ebookjapan offers, so it
            // counts - but only for a title long enough that a stray mention of
            // it in another book's card is unlikely.
            else if (n.length >= 4 && t.includes(n)) tier = Math.max(tier, 1);
        }
        if (!tier) return null;
        return { score: tier + (bonus || 0), len: t.length };
    }

    function hostMatches(hostname, hosts) {
        const h = String(hostname || '').toLowerCase();
        return hosts.some(want => h === want || h.endsWith('.' + want));
    }

    function bestStoreMatch(html, store, candidates) {
        let doc = null;
        try { doc = new DOMParser().parseFromString(html, 'text/html'); } catch (e) { return null; }
        if (!doc) return null;
        let best = null;
        for (const a of doc.querySelectorAll('a[href]')) {
            let url = null;
            try {
                const u = new URL(a.getAttribute('href') || '', store.origin + '/');
                if (!hostMatches(u.hostname, store.hosts)) continue;
                if (!store.product(u.pathname)) continue;
                url = u.origin + u.pathname;
            } catch (e) { continue; }
            const text = (a.textContent || '').replace(/\s+/g, ' ').trim();
            const s = availabilityScore(text, candidates, store.rank(new URL(url).pathname));
            if (!s) continue;
            if (!best || s.score > best.score || (s.score === best.score && s.len < best.len)) {
                best = { score: s.score, len: s.len, url: url, text: text, card: a.outerHTML || '' };
            }
        }
        return best;
    }

    // Price and free-volume detail for the book the user is actually reading,
    // read from the store page we just linked to. Stores that have no such page
    // (ebookjapan) contribute only their search-page badge.
    function blankDetail() {
        return { freeCount: 0, volTotal: 0, freeMine: false, price: null, until: '', volFound: false, rows: 0 };
    }

    async function storeDetail(store, url, cardHtml, volNum, bookTitle) {
        const d = blankDetail();
        // Scoped to the matched result card, never the whole results page: a
        // "N冊無料" badge belongs to one title's card, and the other cards on the
        // page carry their own badges, often larger ones.
        if (typeof store.freeBadge === 'function' && cardHtml) {
            try { d.freeCount = store.freeBadge(cardHtml) || 0; } catch (e) {}
        }
        if (typeof store.volumes !== 'function' || !url) return d;
        let page = null;
        try { page = await gmFetch(url, 15000); } catch (e) { return d; }
        if (!page || page.status !== 200 || !page.text) return d;
        let doc = null;
        try { doc = new DOMParser().parseFromString(page.text, 'text/html'); } catch (e) { return d; }
        if (!doc) return d;
        let items = [];
        try { items = store.volumes(doc) || []; } catch (e) { return d; }
        d.rows = items.length;
        if (!items.length) return d;

        // How many distinct volumes can be read free. A volume with no readable
        // number still counts as one, so a free row is never silently dropped.
        const freeKeys = new Set();
        for (const it of items) {
            if (it.free) freeKeys.add(isFinite(it.vol) && it.vol ? 'v' + it.vol : 't' + it.title);
        }
        d.freeCount = Math.max(d.freeCount, freeKeys.size);
        const vols = new Set();
        for (const it of items) { if (isFinite(it.vol) && it.vol) vols.add(it.vol); }
        d.volTotal = vols.size;

        // Match the row this book actually is. A numbered volume matches on its
        // number; a book with no number (a one-shot, or an unnumbered first
        // volume) can only be matched on its exact title.
        const want = Number(volNum);
        const wantTitle = availabilityNorm(bookTitle || '');
        let mine = [];
        if (isFinite(want) && want > 0) mine = items.filter(it => isFinite(it.vol) && it.vol === want);
        if (!mine.length && wantTitle) mine = items.filter(it => availabilityNorm(it.title) === wantTitle);
        if (!mine.length) return d;
        d.volFound = true;
        const freeOne = mine.find(it => it.free);
        if (freeOne) {
            d.freeMine = true;
            d.until = freeOne.until || '';
            return d;
        }
        const prices = mine.map(it => it.price).filter(p => isFinite(p) && p > 0);
        if (prices.length) d.price = Math.min.apply(null, prices);
        return d;
    }

    // Walk the title candidates until one search page yields a match, so a
    // decorated title ("... 1巻 (ビッグガンガンコミックス)") still lands.
    async function checkStoreAvailability(store, candidates, volNum, bookTitle) {
        for (const cand of candidates) {
            if (!cand) continue;
            let res = null;
            try { res = await gmFetch(store.search(cand), 15000); }
            catch (e) {
                // Every transport failed; do not hammer. Say so, because an
                // unreachable shop and an absent book look identical otherwise.
                if (BWDD_DEBUG) { try { console.info('[bwdd] availability: ' + store.id + ' fetch failed: ' + ((e && e.message) || e)); } catch (_) {} }
                return null;
            }
            if (!res || res.status !== 200 || !res.text) {
                if (BWDD_DEBUG) { try { console.info('[bwdd] availability: ' + store.id + ' HTTP ' + (res && res.status)); } catch (_) {} }
                continue;
            }
            const hit = bestStoreMatch(res.text, store, candidates);
            if (hit) {
                const detail = await storeDetail(store, hit.url, hit.card, volNum, bookTitle);
                return Object.assign({}, hit, detail);
            }
        }
        return null;
    }

    // CMOA's speed-reader URL carries the store page it was opened from as
    // rurl, which is an exact answer for free - no search, no guessing.
    function exactStorePageUrl(store) {
        if (store.id !== 'cmoa') return null;
        try {
            const rurl = new URLSearchParams(location.search).get('rurl');
            if (!rurl) return null;
            const u = new URL(rurl);
            if (!hostMatches(u.hostname, store.hosts)) return null;
            if (!store.product(u.pathname)) return null;
            return u.origin + u.pathname;
        } catch (e) { return null; }
    }

    // "free" when this volume is free; otherwise the price for this volume,
    // alongside how many volumes in the series are free.
    function storeMetaText(r) {
        const bits = [];
        if (r.freeMine) bits.push('free');
        else if (isFinite(r.price) && r.price > 0) bits.push('\u00a5' + r.price.toLocaleString('en-US'));
        // The series count is a separate fact from this volume's own state, so it
        // is reported either way; it is only dropped when it would just repeat
        // "free" for a single free volume.
        if (r.freeCount > 0 && !(r.freeMine && r.freeCount <= 1)) {
            bits.push(r.freeCount + (r.freeCount === 1 ? ' vol free' : ' vols free'));
        }
        return bits.join(' \u00b7 ');
    }

    function storeTipFacts(r, store) {
        const facts = [];
        if (r.freeMine) facts.push('this volume is free' + (r.until ? ' (' + r.until + ')' : ''));
        else if (isFinite(r.price) && r.price > 0) facts.push('this volume is \u00a5' + r.price.toLocaleString('en-US'));
        if (r.freeCount > 0 && !(r.freeMine && r.freeCount <= 1)) {
            const n = r.freeCount;
            if (typeof store.freeBadge === 'function') {
                // ebookjapan renders nothing per-volume, so this number is the
                // shop's own campaign badge rather than rows we counted.
                facts.push('its campaign badge offers ' + n + (n === 1 ? ' volume' : ' volumes') + ' free');
            } else if (r.volTotal > n) {
                facts.push(n + ' of ' + r.volTotal + ' volumes can be read free');
            } else if (n > 1) {
                facts.push('all ' + n + ' volumes can be read free');
            } else {
                facts.push('1 volume can be read free');
            }
        }
        if (!facts.length && r.rows) facts.push('no price or free-volume marker for this volume');
        return facts;
    }

    // The card's CSS travels with the feature: a build that does not include
    // this module carries neither the markup nor the styling.
    const STORE_CSS = `
.bwdd-store-row { display: flex; flex-wrap: wrap; gap: 6px; }
.bwdd-store-link {
  display: inline-flex; align-items: center; gap: 5px;
  border: 1px solid var(--bwdd-border);
  border-radius: 999px;
  padding: 2px 8px 2px 3px;
  font-size: 11px; font-weight: 600; line-height: 1.7;
  text-decoration: none; color: var(--bwdd-text);
  background: var(--bwdd-bg);
}
.bwdd-store-link:hover { border-color: var(--bwdd-store, var(--bwdd-link)); background: var(--bwdd-link-hover-bg); text-decoration: none; }
.bwdd-store-link:focus-visible { outline: 2px solid var(--bwdd-link); outline-offset: 2px; }
.bwdd-store-badge {
  display: inline-flex; align-items: center; justify-content: center;
  width: 16px; height: 16px; border-radius: 50%;
  background: var(--bwdd-store, #6b7280); color: #fff;
  font-size: 10px; font-weight: 700; line-height: 1; flex: 0 0 auto;
}
.bwdd-store-state { color: var(--bwdd-text-muted); font-weight: 500; }
.bwdd-store-link.is-free .bwdd-store-state { color: #15803d; font-weight: 700; }
`;
    let storeStylesMounted = false;
    function mountStoreStyles() {
        if (storeStylesMounted || typeof document === 'undefined') return;
        storeStylesMounted = true;
        try {
            const style = document.createElement('style');
            style.textContent = STORE_CSS;
            (document.head || document.documentElement).appendChild(style);
        } catch (e) {}
    }

    function renderStoresCard(statsEl, results) {
        if (!statsEl || !results || !results.length) return null;
        mountStoreStyles();
        return upsertCard(statsEl, 'stores', () => {
            // Only shops that actually carry it. A pill for a shop that does not
            // have the book is not an availability badge, it is a search link,
            // and a card with nothing in it is not worth a frame.
            const shown = results.filter(r => r.available);
            if (!shown.length) return null;
            const card = emptyCard('Also available on');
            const row = el('div', 'bwdd-store-row');
            const activeId = (ACTIVE_SITE && ACTIVE_SITE.id) || '';
            for (const r of shown) {
                const store = r.store;
                const here = store.siteId && store.siteId === activeId;
                const meta = storeMetaText(r);
                const a = el('a', 'bwdd-store-link is-found' +
                    ((r.freeMine || r.freeCount > 0) ? ' is-free' : ''));
                a.href = r.url;
                a.target = '_blank';
                a.rel = 'noopener noreferrer';
                a.style.setProperty('--bwdd-store', store.color);
                let tip = (r.why === 'exact')
                    ? store.label + ' \u2014 the store page for this book'
                    : 'On ' + store.label + ' \u2014 open its page for this book';
                const facts = storeTipFacts(r, store);
                if (facts.length) tip += ' \u2014 ' + facts.join('; ');
                if (here) tip += ' (the store you are reading on)';
                a.title = tip;
                a.setAttribute('aria-label', tip);
                const badge = el('span', 'bwdd-store-badge', store.short);
                badge.setAttribute('aria-hidden', 'true');
                a.append(badge, el('span', null, store.label));
                // No "available" filler: an empty state is left empty.
                if (meta) a.appendChild(el('span', 'bwdd-store-state', meta));
                row.appendChild(a);
            }
            card.appendChild(row);
            return card;
        });
    }

    async function lookupAvailability(statsEl, seriesTitle, bookTitle, volNum) {
        const raw = String(seriesTitle || bookTitle || '').trim();
        const seed = cleanStoreSeed(raw) || raw;
        if (!seed || !statsEl) return null;
        const cacheKey = seed + '|' + (volNum == null ? '' : volNum);
        const cached = availabilityMemory.get(cacheKey);
        if (cached) { renderStoresCard(statsEl, cached); return cached; }
        const candidates = [];
        for (const base of [seed, raw]) {
            if (!base) continue;
            for (const c of searchTitleCandidates(base)) {
                if (c && candidates.indexOf(c) === -1) candidates.push(c);
            }
        }
        let work = availabilityInflight.get(cacheKey);
        if (!work) {
            work = Promise.all(AVAILABILITY_STORES.map(async (store) => {
                const base = Object.assign(blankDetail(), { store: store });
                const exact = exactStorePageUrl(store);
                if (exact) {
                    // The viewer told us the store page outright, so go straight to
                    // it for the price and free-volume rows.
                    const d = await storeDetail(store, exact, '', volNum, bookTitle);
                    return Object.assign(base, d, { available: true, url: exact, why: 'exact' });
                }
                try {
                    const hit = await checkStoreAvailability(store, candidates, volNum, bookTitle);
                    if (hit) return Object.assign(base, hit, { available: true, url: hit.url, why: 'match' });
                } catch (e) { /* fall through to the search link */ }
                base.available = false;
                base.why = 'search';
                base.url = store.search(candidates[0] || seed);
                return base;
            }));
            availabilityInflight.set(cacheKey, work);
        }
        let results;
        try { results = await work; }
        finally { if (availabilityInflight.get(cacheKey) === work) availabilityInflight.delete(cacheKey); }
        availabilityMemory.set(cacheKey, results);
        // Session-lifetime cache, one entry per series|volume: drop the oldest
        // rather than letting a long browsing session grow it without bound.
        while (availabilityMemory.size > AVAILABILITY_CACHE_MAX) {
            availabilityMemory.delete(availabilityMemory.keys().next().value);
        }
        if (BWDD_DEBUG) {
            try {
                console.info('[bwdd] availability seed="' + seed + '" vol=' + (volNum == null ? '?' : volNum) +
                    ' -> ' + results.map(r => r.store.id + ':' + (r.available ? 'found' : 'not-carried')).join(' '));
            } catch (e) {}
        }
        renderStoresCard(statsEl, results);
        return results;
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

    // =====================================================================
    // 13. Orchestration & Token Lifecycle
    // =====================================================================
    let authRefreshPromise = null;
    let pbCounter = 0;
    // Refresh the CloudFront auth policy, coalesced so concurrent callers share
    // one in-flight request. A fresh public viewer must use its native opening
    // exchange first; rolling renewal uses the viewer's bookmark channel:
    //   'c' , GET /browserWebApi/c with the params the viewer sends when
    //          opening a book; a fresh reply replaces auth/baseUrl/cti.
    //   'pb', POST a reading-position bookmark to the viewer's own
    //          token-renewal channel; only used after capture starts.
    function refreshAuthOnce(mode) {
        if (!authRefreshPromise) {
            authRefreshPromise = (async () => {
                let d;
                if (mode === 'pb') {
                    const ts = new Date();
                    const pad = n => String(n).padStart(2, '0');
                    const dateStr = ts.getFullYear() + '-' + pad(ts.getMonth() + 1) + '-' + pad(ts.getDate()) +
                        'T' + pad(ts.getHours()) + ':' + pad(ts.getMinutes()) + ':' + pad(ts.getSeconds()) + '+0900';
                    pbCounter = (pbCounter || 0) + 1;
                    const pbPos = 'OEBPS/text/p-' + String((pbCounter % 900) + 1).padStart(4, '0') + '.xhtml';
                    const bookmark = JSON.stringify({
                        date: dateStr, position: pbPos,
                        position_later_page: '', pr: (pbCounter % 7), type: 'epub', finished: 0,
                        bookmark_suffix_max: 1, bookmarks: [],
                    });
                    const form = new URLSearchParams();
                    form.set('cid', state.cid);
                    if (getU1()) form.set('u1', getU1());
                    form.set('BID', getBID());
                    form.set('timestamp', '');
                    form.set('bookmark', bookmark);
                    const res = await fetchWithTimeout(apiBase() + '/browserWebApi/pb', {
                        method: 'POST',
                        credentials: isPublicBootstrapPage() ? 'include' : (isHeadlessPage() ? 'omit' : 'include'),
                        headers: { 'Content-Type': 'application/x-www-form-urlencoded; charset=UTF-8' },
                        body: form.toString(),
                    }, isPublicBootstrapPage() ? 12000 : 20000);
                    d = await res.json();
                    if (d && d.auth_info) {
                        // pb merges over the current auth; only a changed
                        // policy/signature resets the request-count budget.
                        const before = authPolicySig();
                        state.auth = Object.assign({}, state.auth || {}, d.auth_info);
                        if (authPolicySig() !== before) resetAuthBudget();
                    }
                } else {
                    const cr = Math.floor(Math.random() * 9e18);
                    const u1 = getU1();
                    const bid = getBID();
                    // The native viewer's opening exchange sends only cid/BID/cr.
                    // It has no u1 cookie on this route, so u1 is optional and must
                    // never fail the request closed. (The previous guard returned a
                    // fabricated status 503 whenever u1 was absent, which is why the
                    // free-volume capture never reached the server.)
                    let url = apiBase() + '/browserWebApi/c?cid=' + encodeURIComponent(state.cid);
                    if (u1) url += '&u1=' + encodeURIComponent(u1);
                    url += '&BID=' + encodeURIComponent(bid) + '&cr=' + cr;
                    const res = await fetchWithTimeout(url, { credentials: isPublicBootstrapPage() ? 'include' : (isHeadlessPage() ? 'omit' : 'include') }, isPublicBootstrapPage() ? 12000 : 20000);
                    d = await res.json();
                    if (d.status === '200' && d.auth_info && d.url) {
                        state.auth = d.auth_info;
                        state.baseUrl = d.url;
                        state.cti = d.cti || state.cti;
                    }
                }
                return d;
            })();
            // Attach both cleanup branches explicitly. A bare finally() returns
            // a second promise that can become an unhandled rejection when the
            // refresh request itself fails, even though its caller catches the
            // original promise.
            authRefreshPromise.then(
                () => { authRefreshPromise = null; },
                () => { authRefreshPromise = null; }
            );
        }
        return authRefreshPromise;
    }
    const refreshAuthViaPb = () => refreshAuthOnce('pb');
    const refreshAuthViaC = () => refreshAuthOnce('c');

    async function refreshAuthBest() {
        const before = authPolicySig();
        try {
            const d = await refreshAuthViaPb();
            if (authPolicySig() !== before) return { method: 'pb', fresh: true, d };
        } catch (e) {}
        try {
            const d = await refreshAuthViaC();
            if (authPolicySig() !== before) return { method: 'c', fresh: true, d };
        } catch (e) {}
        return { method: 'none', fresh: false };
    }

    async function refreshAuthTrial() {
        const cr = Math.floor(Math.random() * 9e18);
        const bid = getBID();
        const url = apiBase() + '/trial-page/c?cid=' + encodeURIComponent(state.cid) + '&BID=' + encodeURIComponent(bid) + '&cr=' + cr;
        const res = await fetchWithTimeout(url, { credentials: isPublicBootstrapPage() ? 'include' : (isHeadlessPage() ? 'omit' : 'include') }, 20000);
        const d = await res.json();
        if (d && d.auth_info) {
            const before = authPolicySig();
            state.auth = Object.assign({}, state.auth || {}, d.auth_info);
            if (d.url) state.baseUrl = d.url;
            if (d.cti) state.cti = d.cti;
            if (authPolicySig() !== before) resetAuthBudget();
            return d;
        }
        return d;
    }

    function authLooksFresh() {
        try {
            const p = state.auth && state.auth['Policy'];
            if (!p) return false;
            const json = JSON.parse(atob(p));
            const lt = json && json.Statement && json.Statement[0] && json.Statement[0].Condition &&
                json.Statement[0].Condition.DateLessThan && json.Statement[0].Condition.DateLessThan['AWS:EpochTime'];
            if (!lt) return true;
            return (lt * 1000) > Date.now() + 10000;
        } catch (e) { return true; }
    }

    function configPrio(dir) {
        if (dir.indexOf('normal_default') !== -1) return 0;
        if (dir.indexOf('large_default') !== -1) return 1;
        if (dir.indexOf('x-large_default') !== -1) return 2;
        if (dir.indexOf('small_default') !== -1) return 3;
        return 4;
    }

    function deriveAuthFromResources() {
        try {
            let entries = state.viewerEntries && state.viewerEntries.length
                ? state.viewerEntries.map(name => ({ name }))
                : (performance.getEntriesByType('resource') || []);
            const hosts = ['bw-bv-epubs.bookwalker.jp', 'viewer-epubs-trial.bookwalker.jp', 'viewer-epubs.bookwalker.jp'];
            let best = null;
            let bestConfig = null;
            for (const e of entries) {
                const u = e.name;
                if (!u) continue;
                const hostMatch = hosts.find(h => u.indexOf(h) !== -1);
                if (!hostMatch) continue;
                const qIdx = u.indexOf('?');
                if (qIdx === -1) continue;
                const params = new URLSearchParams(u.slice(qIdx + 1));
                const auth = {};
                for (const k of AUTH_PARAM_KEYS) {
                    const v = params.get(k);
                    if (v !== null && v !== undefined) auth[k] = v;
                }
                if (!auth['Policy'] || !auth['Signature']) continue;
                const path = u.split('?')[0];
                if (state.cid && path.indexOf(state.cid) === -1) continue;
                if (path.indexOf('configuration_pack.json') !== -1) {
                    const dir = path.replace(/configuration_pack\.json$/, '');
                    const prio = configPrio(dir);
                    if (!bestConfig || prio < bestConfig.prio) {
                        bestConfig = { baseUrl: dir, auth, prio };
                    }
                    continue;
                }
                const m = path.match(/^(https?:\/\/[^\/]+\/[^\/]+\/[^\/]+\/.*?)\/item\//);
                if (m) {
                    const dir = m[1] + '/';
                    const fm = path.match(/item\/xhtml\/(p-[^/]+)\.xhtml/);
                    if (fm) {
                        if (!state.fileBases) state.fileBases = {};
                        state.fileBases[fm[1] + '.xhtml'] = dir;
                    }
                    const prio = configPrio(dir);
                    const depth = (dir.match(/\//g) || []).length;
                    if (!best) {
                        best = { baseUrl: dir, auth, prio, depth };
                    } else if (depth > best.depth) {
                        best = { baseUrl: dir, auth, prio, depth };
                    } else if (depth === best.depth && prio < (best.prio === undefined ? 9 : best.prio)) {
                        best = { baseUrl: dir, auth, prio, depth };
                    }
                }
            }
            const chosen = best || bestConfig;
            if (chosen) {
                state.baseUrl = chosen.baseUrl;
                state.auth = chosen.auth;
                return true;
            }
        } catch (e) { console.warn('[bwdd] deriveAuthFromResources:', safeLogText(e && e.message)); }
        return false;
    }

    async function ensureStateFresh() {
        // The CLI intentionally defers the wrappers until the document-start
        // viewer bootstrap has passed. Activate them here, before inspecting
        // resources and issuing explicit auth/manifest refreshes, so later
        // viewer requests are still captured without wrapping bootstrap itself.
        if (shouldDeferNetworkCapture()) {
            try { installNetworkCapture(); } catch (_) {}
        }
        snapshotViewerResources();
        const publicBootstrap = (() => {
            try { return !!(window.__BWDD_CLI__ && window.__BWDD_CLI__.publicBootstrap); } catch (e) { return false; }
        })();
        const skipNFBR = (() => {
            try { return isHeadlessPage() && (publicBootstrap || !!(window.__BWDD_CLI__ && window.__BWDD_CLI__.skipNFBR)); } catch (_) { return false; }
        })();
        const found = skipNFBR ? { auth: null, baseUrl: null, config: null, cti: null } : findInNFBR(window);
        if (found.auth && found.baseUrl) {
            if (!state.auth) state.auth = found.auth;
            if (!state.baseUrl) state.baseUrl = found.baseUrl;
            if (found.cti && !state.cti) state.cti = found.cti;
            if (found.config && !state.configBody) state.decodedConfig = found.config;
        }
        if ((!state.auth || !state.baseUrl) && deriveAuthFromResources()) {}
        if (!state.auth || !state.baseUrl) {
            for (let attempt = 0; attempt < (publicBootstrap ? 0 : 8) && (!state.auth || !state.baseUrl); attempt++) {
                await new Promise(r => setTimeout(r, 750));
                const f2 = skipNFBR ? { auth: null, baseUrl: null, config: null, cti: null } : findInNFBR(window);
                if (f2.auth && f2.baseUrl) {
                    state.auth = f2.auth;
                    state.baseUrl = f2.baseUrl;
                    if (f2.cti && !state.cti) state.cti = f2.cti;
                    if (f2.config && !state.decodedConfig) state.decodedConfig = f2.config;
                }
                if ((!state.auth || !state.baseUrl) && deriveAuthFromResources()) {}
            }
        }
        if (!state.auth || !state.baseUrl) {
            let d = null;
            const attemptStatuses = [];
            try {
                if (location.hostname.indexOf('trial') !== -1 || (state.baseUrl && state.baseUrl.indexOf('epubs-trial') !== -1)) {
                    d = await refreshAuthTrial();
                    if (d && d.status != null) attemptStatuses.push(String(d.status));
                }
            } catch (e) {}
            if (!state.auth || !state.baseUrl) {
                // A fresh viewer boot obtains its signed CloudFront policy from
                // /c. Do not send a synthetic bookmark (and advance a public
                // reader's position) before that first native auth exchange.
                // /pb remains the rolling renewal path after capture starts.
                const cFirst = publicBootstrap && (publicBootstrap.route === 'free' || location.hostname.indexOf('trial') === -1);
                if (cFirst) {
                    try { d = await refreshAuthViaC(); } catch (e) { d = null; }
                    if (d && d.status != null) attemptStatuses.push(String(d.status));
                }
                if (!cFirst && (!state.auth || !state.baseUrl)) {
                    try {
                        d = await refreshAuthViaPb();
                        if (d && d.status != null) attemptStatuses.push(String(d.status));
                    } catch (e) {
                        if (e && e.status != null) attemptStatuses.push(String(e.status));
                    }
                }
                // v1.5.1 called /c at most once per sequence, and only after /pb
                // had left us still missing (see the nested guards in its run
                // loop). When cFirst already made that call above, this would be
                // a second identical request; && binds tighter than ||, so the
                // still-missing guard needs its own parentheses to mean that.
                if ((!state.auth || !state.baseUrl) && !cFirst) {
                    try { d = await refreshAuthViaC(); } catch (e) { d = null; }
                    if (d && d.status != null) attemptStatuses.push(String(d.status));
                }
            }
            if (!state.auth || !state.baseUrl) {
                const st = attemptStatuses.find(status => status === '401' || status === '995') ||
                    (d && d.status);
                let hint = 'Failed to capture session auth. Flip one page in the reader and try again.';
                if (st === '503') hint = 'BookWalker returned 503 (session busy/rate-limited). Wait a moment, then try again.';
                else if (st === '401') hint = 'Session cookie expired. Reopen this book from your BookWalker library.';
                else if (st === '995') hint = 'This public sample is not available to an unauthenticated reader.';
                const authError = new Error(hint);
                if (st === '401' || st === '995') authError.code = 'LOGIN_REQUIRED';
                throw authError;
            }
        }
        const bodyDirMatches = !state.configBody || !state.configFromUrl ||
            !state.baseUrl || state.configFromUrl.indexOf(state.baseUrl) === 0;
        if (state.decodedConfig && bodyDirMatches && !state.configBody) {
            try {
                const url = state.baseUrl + 'configuration_pack.json?' + authQuery(state.auth);
                const res = await fetchWithTimeout(url, { credentials: 'omit' }, 60000);
                if (res.ok) { state.configBody = await res.text(); state.configFromUrl = state.baseUrl; }
            } catch (e) { console.warn('[bwdd] Config fetch failed, falling back to memory copy', safeLogText(e && e.message)); }
        } else if (!state.decodedConfig && (!state.configBody || !bodyDirMatches)) {
            const url = state.baseUrl + 'configuration_pack.json?' + authQuery(state.auth);
            const res = await fetchWithTimeout(url, { credentials: 'omit' }, 60000);
            if (!res.ok) throw new Error('Failed to download configuration manifest (HTTP ' + res.status + ')');
            state.configBody = await res.text();
            state.configFromUrl = state.baseUrl;
        }
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

    function decodeConfig(content) {
        const c = String(content || '');
        if (c.indexOf('"data":"') === -1) {
            try {
                const j = JSON.parse(c);
                if (j && j.configuration && j.configuration.contents) {
                    state.keys = null;
                    state.plaintextConfig = true;
                    return j;
                }
            } catch (e) {}
        }
        const DATA_STR = '"data":"';
        const dataOffset = c.indexOf(DATA_STR) + DATA_STR.length;
        const dataEndOffset = c.indexOf('"', dataOffset);
        if (dataOffset < DATA_STR.length || dataEndOffset < dataOffset) {
            throw new Error('Invalid configuration pack');
        }
        const fk = processFilename('configuration_pack.json');
        let st = A8j(c, dataOffset, dataEndOffset);
        st = A3b(0, st); st = B0p(fk, st); st = A7L(fk, st); st = A6I(fk, st); st = A2F(st);
        st = B0L(fk, st); st = A3b(1, st); st = A3b(2, st); st = A3b(3, st); st = tB0l(fk, st);
        const [jsonStr] = A6e(st);
        state.keys = [st[2], st[3], st[4]];
        return JSON.parse(jsonStr);
    }

    function buildBookPreview() {
        try {
            const rawTitle = state.cti || document.title || '';
            const title = cleanTitle(rawTitle) || state.cid || 'Unknown Book';
            if (!state.decodedConfig && !state.configBody) return null;
            const config = state.decodedConfig || decodeConfig(state.configBody);
            const contents = config && config['configuration'] && config['configuration']['contents'];
            if (!contents || !contents.length) return null;
            const isPlain = state.plaintextConfig || !state.keys;
            let pages = 0, W = '?', H = '?';
            for (const it of contents) {
                const cfg = config[it.file];
                if (!cfg || !cfg.FileLinkInfo) { pages++; continue; }
                const fli = cfg.FileLinkInfo;
                const pl = fli.PageLinkInfoList || [];
                const n = fli.PageCount || Math.max(1, pl.length);
                pages += n;
                if (W === '?' && pl.length) {
                    const p = pl[0].Page;
                    if (p && p.Size) { W = p.Size.Width; H = p.Size.Height; }
                }
            }
            return {
                title,
                pages,
                resolution: `${W} × ${H}`,
                type: isPlain ? 'Sample / Trial' : 'Full Edition'
            };
        } catch (e) { return null; }
    }

    // =====================================================================
    // BookWalker site adapter
    // =====================================================================
    // BookWalker is the original site, so its pipeline is unchanged; only its
    // identity and metadata answers are exposed here.
    registerSite({
        id: 'bookwalker',
        label: 'BookWalker',
        panelTitle: 'BookWalker Native Downloader',
        matches() {
            try {
                return /(^|\.)bookwalker\.jp$/i.test(location.hostname);
            } catch (e) { return false; }
        },
        install() {
            // A headless CLI run may deliberately defer the capture and call
            // activateCapture() itself once the page is where it wants it.
            if (!shouldDeferNetworkCapture()) installNetworkCapture();
        },
        getBook() {
            const rawTitle = state.cti || document.title || '';
            const title = cleanTitle(rawTitle) || state.cid || '';
            const sv = splitSeriesVolume(state.cti || title);
            return { rawTitle, title, series: sv.series, volNum: sv.volNum };
        },
        getPreview() { return buildBookPreview(); },
        getCid() { return state.cid || ''; },
        archiveDefault(rawTitle) { return archiveDefaultName(rawTitle) || fsSafePath(state.cid || ''); },
        run(ui, mode, options) { return run(ui, mode, options); },
        state: state,
        // Console surface for this store only; the entry point merges whatever
        // the active adapter puts here into window.__bwdd.
        debug: {
            decodeConfig, pageSeedsNo, A9p, b8gNo, state, buildWorkerSource,
            fetchAndDescramble, cdnFetch, cdnFetchWithFallback,
        },
    });
    // =====================================================================
    // ebookjapan — page detection, the viewer URL, and the book manifest
    // =====================================================================
    // Ported from the standalone ebookjapan userscript, which had this working
    // against live volumes. What it answers:
    //
    //   ebjParseTarget(href)   the volume code and the viewer path
    //   ebjResolveCodes(spec)  cheap: the code and, when the page has it, a title
    //   ebjResolvePages(...)   the real thing: session payloads, the book's own
    //                          manifest, the page list and the canvas box
    //
    // ebjResolvePages also records the session payloads and the open_param
    // arguments in ebjState, because a Web Worker has to install its own copy of
    // the pack (the wasm module is single-shot) and can only do that if it is
    // handed the same payloads this run used.
    const ebjState = {
        // The other stores publish their id as `cid` on the active debug
        // surface; mirror the volume code there too.
        get cid() { return ebjState.code || ''; },
        code: '',
        fileId: '',
        payload: null,      // { sessionId, code, fileId, openPayload, drmPayload }
        params: null,       // the open_param arguments those payloads were opened with
        book: null,         // { name, title, code, pages, canvas, direction, autograph }
        running: false,
    };

    // ebjPage is the page realm when the userscript manager exposes one; every
    // canvas the wasm draws into has to come from there (see 02-realms.js).
    const ebjPage = (typeof unsafeWindow !== 'undefined' && unsafeWindow) || window;

    const EBJ_BASE = 'https://ebookjapan.yahoo.co.jp';
    const EBJ_CDN = 'https://prod-contents-br-page.akamaized.net';
    const EBJ_NAME_CONCURRENCY = 8;
    const EBJ_PARAM_PROBE = { dpr: 2, limit: 10000, size: 10000, flag: 0 };

    // Request headers for the viewer's own API. This came across with the
    // resolve helpers; dropping it with the standalone's GM layer left every
    // resolve throwing a ReferenceError that only ever reached console.warn,
    // so the panel's Save button looked like it did nothing at all.
    const apiHeaders = referer => ({
        'Content-Type': 'application/json',
        Origin: EBJ_BASE,
        Referer: referer || (location.origin + '/'),
        'X-Requested-With': 'FetchAPI',
    });

    function ebjParseTarget(href) {
        const url = String(href || location.href);
        let m;
        if ((m = url.match(/\/viewer\/([^/?#]+)\/([A-Za-z0-9]+)/))) {
            return { type: m[1], code: m[2], referer: `${EBJ_BASE}/viewer/${m[1]}/${m[2]}/` };
        }
        if ((m = url.match(/\/books\/(\d+)\/([A-Za-z0-9]+)/))) {
            return { titleId: m[1], publication: m[2], type: null, code: null, referer: url };
        }
        if ((m = url.match(/\/br_api\/books\/(\d+)\/([A-Za-z0-9]+)/))) {
            return { titleId: m[1], publication: m[2], type: null, code: null, referer: `${EBJ_BASE}/books/${m[1]}/${m[2]}/` };
        }
        throw new Error('open an ebookjapan book or reader page first ' +
            '(a /books/<id>/<code>/ or /viewer/<type>/<code>/ URL)');
    }

    async function ebjResolveCodes(spec) {
        if (spec.type && spec.code) return spec;
        if (!spec.titleId || !spec.publication) return spec;

        const r = await fetch(`${EBJ_BASE}/br_api/books/${spec.titleId}/${spec.publication}?device=pc`,
            { headers: apiHeaders(spec.referer) });
        if (!r.ok) throw new Error(`book detail ${r.status}: ${(await r.text()).slice(0, 160)}`);
        const detail = (await r.json())?.detail;
        if (!detail) throw new Error('book detail response had no `detail` object');
        const isFree = !!(detail.isFree || detail.isTrialReadableWithBrowser);
        const code = detail.code || detail.trial;
        if (!code) throw new Error('could not determine the reading code for this volume');
        return {
            ...spec,
            type: isFree ? 'free' : 'purchased',
            code,
            trialCode: detail.trial || null,
            title: detail.title || detail.itemName || null,
            allowPurchasedFallback: true,
        };
    }

    // The boot poll and the run can both ask for the same volume while the first
    // resolve is still in flight: it makes three network calls and instantiates
    // the wasm module, so it reliably outlives the timers that trigger it.
    // Without a shared promise each caller opens its own open_book session and
    // builds a second module to race over the same ebjState.
    let ebjResolveInflight = null;

    async function ebjResolvePages(target, opts) {
        const key = String(target || location.href);
        if (ebjResolveInflight && ebjResolveInflight.key === key) return ebjResolveInflight.promise;
        const promise = ebjResolvePagesOnce(target, opts);
        ebjResolveInflight = { key, promise };
        try { return await promise; }
        finally { if (ebjResolveInflight && ebjResolveInflight.promise === promise) ebjResolveInflight = null; }
    }

    async function ebjResolvePagesOnce(target, { onStatus } = {}) {
        const say = m => { if (onStatus) onStatus(m); };
        const spec = await ebjResolveCodes(ebjParseTarget(target));
        say(`code ${spec.code} (${spec.type})`);

        const openBook = (type, code) => fetch(`${EBJ_BASE}/br_api/open_book`, {
            method: 'POST',
            headers: apiHeaders(spec.referer),
            body: JSON.stringify({ type, code, light: false }),
        });

        let obRes = await openBook(spec.type, spec.code);
        if (!obRes.ok && spec.type === 'free' && spec.allowPurchasedFallback) {
            ebjLog('resolve', 'open_book(free) refused, retrying as purchased');
            const altCode = (spec.trialCode && spec.trialCode !== spec.code) ? spec.trialCode : spec.code;
            const alt = await openBook('purchased', altCode);
            if (alt.ok) { obRes = alt; spec.type = 'purchased'; spec.code = altCode; }
        }
        if (!obRes.ok) {
            const body = (await obRes.text()).slice(0, 200);
            if (spec.type === 'purchased') {
                throw new Error(`Could not open this volume (${obRes.status}).\n` +
                    `It is not a free or sample volume, so the API needs your logged-in ebookjapan session.\n` +
                    `Make sure you are signed in and have opened this book in the reader once.\n${body}`);
            }
            throw new Error(`open_book ${obRes.status}: ${body}`);
        }
        const open = await obRes.json();
        if (!open || !open.session_id) throw new Error('open_book returned no session_id');

        const drmRes = await fetch(`${EBJ_BASE}/br_api/get_drm?session_id=${encodeURIComponent(open.session_id)}`,
            { headers: apiHeaders(spec.referer) });
        if (!drmRes.ok) throw new Error(`get_drm ${drmRes.status}: ${(await drmRes.text()).slice(0, 200)}`);
        const drm = await drmRes.json();
        if (!drm || !drm.file_id) throw new Error('get_drm returned no file_id');

        say('decrypting configuration pack');
        const glue = await ebjLoadGlue();
        await glue.decrypt_session(open.session_id, drm.code, open.payload, drm.payload);
        // Keep what it takes to install the pack again. The decrypted pack lives
        // in the wasm module's own memory, and shuffle() traps with a bare
        // "unreachable" when it is not there — a panic that names no cause and
        // stops every page at once.
        ebjAutographImg = null;   // a new book means a new overlay
        ebjState.payload = { sessionId: open.session_id, code: drm.code, fileId: drm.file_id,
                         openPayload: open.payload, drmPayload: drm.payload };

        // Ask for the biggest box the book has, then scale to what comes back:
        // open_param normalises to fit `limit`/`size`, so a probe with a huge
        // limit reports the intrinsic size, and a second call at that size ends
        // up as close to 1:1 as the manifest allows.
        const probe = await glue.open_param(EBJ_PARAM_PROBE);
        const probePages = (probe && probe.pages) || [];
        if (!probePages.length) throw new Error('the page manifest came back empty');

        let maxW = 0, maxH = 0;
        for (const p of probePages) {
            if (Number(p.width) > maxW) maxW = Number(p.width);
            if (Number(p.height) > maxH) maxH = Number(p.height);
        }
        let manifest = probe;
        if (maxW > 0 && maxH > 0 &&
            (maxW !== EBJ_PARAM_PROBE.size || maxH !== EBJ_PARAM_PROBE.limit)) {
            const params = { dpr: 2, limit: maxH, size: maxW, flag: 0 };
            manifest = await glue.open_param(params);
            ebjState.params = params;
        }
        const pages = (manifest && manifest.pages) || [];

        say(`resolving ${pages.length} page names`);
        const names = new Array(pages.length);
        for (let i = 0; i < pages.length; i += EBJ_NAME_CONCURRENCY) {
            const slice = pages.slice(i, i + EBJ_NAME_CONCURRENCY);
            await Promise.all(slice.map(async (_, k) => {
                const n = i + k;
                try { names[n] = await glue.get_page_name(drm.file_id, n); }
                catch (e) { names[n] = null; }
            }));
        }

        // Canvas the whole book is composed into: big enough for its largest
        // page. shuffle() places every tile at a destination offset derived from
        // the intrinsic geometry, so one canvas size serves every page and the
        // smaller pages simply carry transparent padding past their own box.
        let canvasW = 0, canvasH = 0;
        for (const p of pages) {
            if (Number(p.width) > canvasW) canvasW = Number(p.width);
            if (Number(p.height) > canvasH) canvasH = Number(p.height);
        }

        const rows = pages.map((p, n) => {
            const name = names[n];
            return {
                page: n,
                name,
                view: p.view ?? null,
                width: p.width ?? null,
                height: p.height ?? null,
                position: p.position ?? null,
                width: Number(p.width) || 0,
                height: Number(p.height) || 0,
                jumps: (p.jumps || []).length,
                url: name ? `${EBJ_CDN}/pages/${String(name).replace(/\.jpe?g$/i, '.webp')}` : null,
            };
        });

        return {
            source: target,
            publication: drm.publication,
            autograph: autographSpec(drm),
            fileId: drm.file_id,
            path: drm.path,
            code: drm.code,
            name: drm.name || drm.title || spec.title || null,
            title: drm.title || null,
            formatId: Number(drm.format_id),
            direction: manifest && manifest.direction != null ? manifest.direction : null,
            version: manifest ? manifest.version : null,
            imageTypes: manifest ? manifest.image_types : null,
            chapters: (manifest && manifest.chapters) || [],
            totalPages: pages.length,
            canvas: { width: canvasW, height: canvasH },
            pages: rows,
        };
    }

    /** ebookjapan's viewer is the only page this adapter owns. */
    // A breadcrumb the instant this script is evaluated, before any adapter
    // logic. If the attribute below never appears, Tampermonkey did not run the
    // script at all (wrong URL, stale install, script disabled) — which looks
    // exactly like a crash from the panel, and is the first thing to rule out.
    try {
        document.documentElement.setAttribute('data-bwdd-ebookjapan', 'evaluated');
        console.log('[ebookjapan] evaluated on ' + location.href);
    } catch (e) {}

    function ebjIsViewerPage(href) {
        try {
            return /(^|\.)ebookjapan\.yahoo\.co\.jp$/i.test(new URL(href, location.href).hostname);
        } catch (e) {
            return /ebookjapan\.yahoo\.co\.jp/.test(String(href));
        }
    }
    // =====================================================================
    // ebookjapan — the viewer's wasm core, embedded and pinned
    // =====================================================================
    // The viewer descrambles a page with a small Rust/wasm module driven by a
    // glue script. Both are embedded here as base64, for the same two reasons
    // BookWalker's configuration_pack is captured rather than guessed: a run
    // must not depend on the hashed asset names the site ships that week, and
    // it must not race the viewer's own module load.
    //
    // The glue is embedded ALREADY PATCHED. Two edits make it survive outside
    // the viewer's own bundler:
    //   * the module's `import` / `import.meta` usage is removed, so the source
    //     can be compiled with `new Function` instead of being a real module;
    //   * `__wbg_instanceof_Window_def73ea0955fc569` is widened to accept any
    //     window-shaped global, which is what lets the same glue run inside a
    //     Web Worker (a worker's global is a DedicatedWorkerGlobalScope, not a
    //     Window) and inside Tampermonkey's sandbox.
    //
    // EBJ_GLUE_SUM pins exactly that patched text. ebookjapan redeploys this
    // viewer regularly, so the pin is a deliberate tripwire: when it stops
    // matching, ebjLoadGlue says the site has probably moved on rather than
    // silently descrambling nothing. Re-extract the glue and the wasm, drop
    // them in and rebuild.
    const EBJ_GLUE_B64 = 'dmFyIGUsdD1BcnJheSgxMjgpLmZpbGwodm9pZCAwKTt0LnB1c2godm9pZCAwLG51bGwsITAsITEpO2Z1bmN0aW9uIG4oZSl7cmV0dXJuIHRbZV19dmFyIHI9dC5sZW5ndGg7ZnVuY3Rpb24gaShlKXtyPT09dC5sZW5ndGgmJnQucHVzaCh0Lmxlbmd0aCsxKTtsZXQgbj1yO3JldHVybiByPXRbbl0sdFtuXT1lLG59ZnVuY3Rpb24gYSh0LG4pe3RyeXtyZXR1cm4gdC5hcHBseSh0aGlzLG4pfWNhdGNoKHQpe2UuX193YmluZGdlbl9leG5fc3RvcmUoaSh0KSl9fWZ1bmN0aW9uIG8oZSl7cmV0dXJuIGU9PW51bGx9dmFyIHM9bnVsbDtmdW5jdGlvbiBjKCl7cmV0dXJuKHM9PT1udWxsfHxzLmJ5dGVMZW5ndGg9PT0wKSYmKHM9bmV3IFVpbnQ4QXJyYXkoZS5tZW1vcnkuYnVmZmVyKSksc31mdW5jdGlvbiBsKGUsdCl7cmV0dXJuIGU+Pj49MCxjKCkuc3ViYXJyYXkoZS8xLGUvMSt0KX12YXIgdT10eXBlb2YgVGV4dERlY29kZXI8YHVgP25ldyBUZXh0RGVjb2RlcihgdXRmLThgLHtpZ25vcmVCT006ITAsZmF0YWw6ITB9KTp7ZGVjb2RlOigpPT57dGhyb3cgRXJyb3IoYFRleHREZWNvZGVyIG5vdCBhdmFpbGFibGVgKX19O3R5cGVvZiBUZXh0RGVjb2RlcjxgdWAmJnUuZGVjb2RlKCk7ZnVuY3Rpb24gZChlLHQpe3JldHVybiBlPj4+PTAsdS5kZWNvZGUoYygpLnN1YmFycmF5KGUsZSt0KSl9ZnVuY3Rpb24gZihlKXtlPDEzMnx8KHRbZV09cixyPWUpfWZ1bmN0aW9uIHAoZSl7bGV0IHQ9bihlKTtyZXR1cm4gZihlKSx0fXZhciBtPXR5cGVvZiBGaW5hbGl6YXRpb25SZWdpc3RyeT5gdWA/e3JlZ2lzdGVyOigpPT57fSx1bnJlZ2lzdGVyOigpPT57fX06bmV3IEZpbmFsaXphdGlvblJlZ2lzdHJ5KHQ9PntlLl9fd2JpbmRnZW5fZXhwb3J0XzEuZ2V0KHQuZHRvcikodC5hLHQuYil9KTtmdW5jdGlvbiBoKHQsbixyLGkpe2xldCBhPXthOnQsYjpuLGNudDoxLGR0b3I6cn0sbz0oLi4udCk9PnthLmNudCsrO2xldCBuPWEuYTthLmE9MDt0cnl7cmV0dXJuIGkobixhLmIsLi4udCl9ZmluYWxseXstLWEuY250PT09MD8oZS5fX3diaW5kZ2VuX2V4cG9ydF8xLmdldChhLmR0b3IpKG4sYS5iKSxtLnVucmVnaXN0ZXIoYSkpOmEuYT1ufX07cmV0dXJuIG8ub3JpZ2luYWw9YSxtLnJlZ2lzdGVyKG8sYSxhKSxvfWZ1bmN0aW9uIGcoZSl7bGV0IHQ9dHlwZW9mIGU7aWYodD09YG51bWJlcmB8fHQ9PWBib29sZWFuYHx8ZT09bnVsbClyZXR1cm5gJHtlfWA7aWYodD09YHN0cmluZ2ApcmV0dXJuYCIke2V9ImA7aWYodD09YHN5bWJvbGApe2xldCB0PWUuZGVzY3JpcHRpb247cmV0dXJuIHQ9PW51bGw/YFN5bWJvbGA6YFN5bWJvbCgke3R9KWB9aWYodD09YGZ1bmN0aW9uYCl7bGV0IHQ9ZS5uYW1lO3JldHVybiB0eXBlb2YgdD09YHN0cmluZ2AmJnQubGVuZ3RoPjA/YEZ1bmN0aW9uKCR7dH0pYDpgRnVuY3Rpb25gfWlmKEFycmF5LmlzQXJyYXkoZSkpe2xldCB0PWUubGVuZ3RoLG49YFtgO3Q+MCYmKG4rPWcoZVswXSkpO2ZvcihsZXQgcj0xO3I8dDtyKyspbis9YCwgYCtnKGVbcl0pO3JldHVybiBuKz1gXWAsbn1sZXQgbj0vXFtvYmplY3QgKFteXF1dKylcXS8uZXhlYyh0b1N0cmluZy5jYWxsKGUpKSxyO2lmKG4mJm4ubGVuZ3RoPjEpcj1uWzFdO2Vsc2UgcmV0dXJuIHRvU3RyaW5nLmNhbGwoZSk7aWYocj09YE9iamVjdGApdHJ5e3JldHVybmBPYmplY3QoYCtKU09OLnN0cmluZ2lmeShlKStgKWB9Y2F0Y2h7cmV0dXJuYE9iamVjdGB9cmV0dXJuIGUgaW5zdGFuY2VvZiBFcnJvcj9gJHtlLm5hbWV9OiAke2UubWVzc2FnZX1cbiR7ZS5zdGFja31gOnJ9dmFyIF89MCx2PXR5cGVvZiBUZXh0RW5jb2RlcjxgdWA/bmV3IFRleHRFbmNvZGVyKGB1dGYtOGApOntlbmNvZGU6KCk9Pnt0aHJvdyBFcnJvcihgVGV4dEVuY29kZXIgbm90IGF2YWlsYWJsZWApfX0seT10eXBlb2Ygdi5lbmNvZGVJbnRvPT1gZnVuY3Rpb25gP2Z1bmN0aW9uKGUsdCl7cmV0dXJuIHYuZW5jb2RlSW50byhlLHQpfTpmdW5jdGlvbihlLHQpe2xldCBuPXYuZW5jb2RlKGUpO3JldHVybiB0LnNldChuKSx7cmVhZDplLmxlbmd0aCx3cml0dGVuOm4ubGVuZ3RofX07ZnVuY3Rpb24gYihlLHQsbil7aWYobj09PXZvaWQgMCl7bGV0IG49di5lbmNvZGUoZSkscj10KG4ubGVuZ3RoLDEpPj4+MDtyZXR1cm4gYygpLnN1YmFycmF5KHIscituLmxlbmd0aCkuc2V0KG4pLF89bi5sZW5ndGgscn1sZXQgcj1lLmxlbmd0aCxpPXQociwxKT4+PjAsYT1jKCksbz0wO2Zvcig7bzxyO28rKyl7bGV0IHQ9ZS5jaGFyQ29kZUF0KG8pO2lmKHQ+MTI3KWJyZWFrO2FbaStvXT10fWlmKG8hPT1yKXtvIT09MCYmKGU9ZS5zbGljZShvKSksaT1uKGkscixyPW8rZS5sZW5ndGgqMywxKT4+PjA7bGV0IHQ9YygpLnN1YmFycmF5KGkrbyxpK3IpLGE9eShlLHQpO28rPWEud3JpdHRlbixpPW4oaSxyLG8sMSk+Pj4wfXJldHVybiBfPW8saX12YXIgeD1udWxsO2Z1bmN0aW9uIFMoKXtyZXR1cm4oeD09PW51bGx8fHguYnVmZmVyLmRldGFjaGVkPT09ITB8fHguYnVmZmVyLmRldGFjaGVkPT09dm9pZCAwJiZ4LmJ1ZmZlciE9PWUubWVtb3J5LmJ1ZmZlcikmJih4PW5ldyBEYXRhVmlldyhlLm1lbW9yeS5idWZmZXIpKSx4fWZ1bmN0aW9uIEModCxuLHIsaSl7bGV0IGE9Yih0LGUuX193YmluZGdlbl9tYWxsb2MsZS5fX3diaW5kZ2VuX3JlYWxsb2MpLG89XyxzPWIobixlLl9fd2JpbmRnZW5fbWFsbG9jLGUuX193YmluZGdlbl9yZWFsbG9jKSxjPV8sbD1iKHIsZS5fX3diaW5kZ2VuX21hbGxvYyxlLl9fd2JpbmRnZW5fcmVhbGxvYyksdT1fLGQ9YihpLGUuX193YmluZGdlbl9tYWxsb2MsZS5fX3diaW5kZ2VuX3JlYWxsb2MpLGY9XztyZXR1cm4gcChlLmRlY3J5cHRfc2Vzc2lvbihhLG8scyxjLGwsdSxkLGYpKX1mdW5jdGlvbiB3KHQsbixyKXtyZXR1cm4gcChlLmRlY3J5cHRfeGooaSh0KSxuLHIpKX1mdW5jdGlvbiBUKHQpe2Uuc2h1ZmZsZShpKHQpKX1mdW5jdGlvbiBFKHQpe3JldHVybiBwKGUucmFuZ2VzKHQpKX1mdW5jdGlvbiBEKHQpe3JldHVybiBwKGUub3Blbl9wYXJhbShpKHQpKSl9ZnVuY3Rpb24gTygpe2xldCB0LG47dHJ5e2xldCBhPWUuX193YmluZGdlbl9hZGRfdG9fc3RhY2tfcG9pbnRlcigtMTYpO2UuZ2V0X3NwZWNpYWxfdXJsKGEpO3ZhciByPVMoKS5nZXRJbnQzMihhKzAsITApLGk9UygpLmdldEludDMyKGErNCwhMCk7cmV0dXJuIHQ9cixuPWksZChyLGkpfWZpbmFsbHl7ZS5fX3diaW5kZ2VuX2FkZF90b19zdGFja19wb2ludGVyKDE2KSxlLl9fd2JpbmRnZW5fZnJlZSh0LG4sMSl9fWZ1bmN0aW9uIGsodCxuKXtsZXQgcj1iKHQsZS5fX3diaW5kZ2VuX21hbGxvYyxlLl9fd2JpbmRnZW5fcmVhbGxvYyksaT1fO3JldHVybiBwKGUuZ2V0X3BhZ2VfbmFtZShyLGksbikpfWZ1bmN0aW9uIEEodCxuLHIpe2UuX2R5bl9jb3JlX19vcHNfX2Z1bmN0aW9uX19Gbk11dF9fQV9fX19PdXRwdXRfX19SX2FzX3dhc21fYmluZGdlbl9fY2xvc3VyZV9fV2FzbUNsb3N1cmVfX19kZXNjcmliZV9faW52b2tlX19oZDViNmRmMGFhNWE1YmYxNCh0LG4saShyKSl9ZnVuY3Rpb24gaih0LG4scixhLG8pe2Uud2FzbV9iaW5kZ2VuX19jb252ZXJ0X19jbG9zdXJlc19faW52b2tlM19tdXRfX2gyODQwZDQ1NmNmOTA1YTE3KHQsbixpKHIpLGEsaShvKSl9ZnVuY3Rpb24gTSh0LG4scixhKXtlLndhc21fYmluZGdlbl9fY29udmVydF9fY2xvc3VyZXNfX2ludm9rZTJfbXV0X19oMTZiZjg3NTEyODdjZTM2MSh0LG4saShyKSxpKGEpKX1hc3luYyBmdW5jdGlvbiBOKGUsdCl7aWYodHlwZW9mIFJlc3BvbnNlPT1gZnVuY3Rpb25gJiZlIGluc3RhbmNlb2YgUmVzcG9uc2Upe2lmKHR5cGVvZiBXZWJBc3NlbWJseS5pbnN0YW50aWF0ZVN0cmVhbWluZz09YGZ1bmN0aW9uYCl0cnl7cmV0dXJuIGF3YWl0IFdlYkFzc2VtYmx5Lmluc3RhbnRpYXRlU3RyZWFtaW5nKGUsdCl9Y2F0Y2godCl7aWYoZS5oZWFkZXJzLmdldChgQ29udGVudC1UeXBlYCkhPWBhcHBsaWNhdGlvbi93YXNtYCljb25zb2xlLndhcm4oImBXZWJBc3NlbWJseS5pbnN0YW50aWF0ZVN0cmVhbWluZ2AgZmFpbGVkIGJlY2F1c2UgeW91ciBzZXJ2ZXIgZG9lcyBub3Qgc2VydmUgV2FzbSB3aXRoIGBhcHBsaWNhdGlvbi93YXNtYCBNSU1FIHR5cGUuIEZhbGxpbmcgYmFjayB0byBgV2ViQXNzZW1ibHkuaW5zdGFudGlhdGVgIHdoaWNoIGlzIHNsb3dlci4gT3JpZ2luYWwgZXJyb3I6XG4iLHQpO2Vsc2UgdGhyb3cgdH1sZXQgbj1hd2FpdCBlLmFycmF5QnVmZmVyKCk7cmV0dXJuIGF3YWl0IFdlYkFzc2VtYmx5Lmluc3RhbnRpYXRlKG4sdCl9e2xldCBuPWF3YWl0IFdlYkFzc2VtYmx5Lmluc3RhbnRpYXRlKGUsdCk7cmV0dXJuIG4gaW5zdGFuY2VvZiBXZWJBc3NlbWJseS5JbnN0YW5jZT97aW5zdGFuY2U6bixtb2R1bGU6ZX06bn19ZnVuY3Rpb24gUCgpe2xldCB0PXt9O3JldHVybiB0LndiZz17fSx0LndiZy5fX3diZ19idWZmZXJfNjA5Y2MzZWVlNTFlZDE1OD1mdW5jdGlvbihlKXtsZXQgdD1uKGUpLmJ1ZmZlcjtyZXR1cm4gaSh0KX0sdC53YmcuX193YmdfY2FsbF82NzJhNGQyMTYzNGQ0YTI0PWZ1bmN0aW9uKCl7cmV0dXJuIGEoZnVuY3Rpb24oZSx0KXtyZXR1cm4gaShuKGUpLmNhbGwobih0KSkpfSxhcmd1bWVudHMpfSx0LndiZy5fX3diZ19jYWxsXzdjY2NkZDY5ZTA3OTFhZTI9ZnVuY3Rpb24oKXtyZXR1cm4gYShmdW5jdGlvbihlLHQscil7cmV0dXJuIGkobihlKS5jYWxsKG4odCksbihyKSkpfSxhcmd1bWVudHMpfSx0LndiZy5fX3diZ19jYW52YXNfOWJiY2RiOTRhOTc3ODA3YT1mdW5jdGlvbihlKXtsZXQgdD1uKGUpLmNhbnZhcztyZXR1cm4gbyh0KT8wOmkodCl9LHQud2JnLl9fd2JnX2NsZWFyUmVjdF84ZTRiYTdlYTBlMDY3MTFhPWZ1bmN0aW9uKGUsdCxyLGksYSl7bihlKS5jbGVhclJlY3QodCxyLGksYSl9LHQud2JnLl9fd2JnX2NyeXB0b18xMjU3NmNkNjYyNDY5OThiPWZ1bmN0aW9uKCl7cmV0dXJuIGEoZnVuY3Rpb24oZSl7bGV0IHQ9bihlKS5jcnlwdG87cmV0dXJuIGkodCl9LGFyZ3VtZW50cyl9LHQud2JnLl9fd2JnX2RlY3J5cHRfZDUyZjJkNzFhNWI4YmVkZj1mdW5jdGlvbigpe3JldHVybiBhKGZ1bmN0aW9uKGUsdCxyLGEsbyl7cmV0dXJuIGkobihlKS5kZWNyeXB0KG4odCksbihyKSxsKGEsbykpKX0sYXJndW1lbnRzKX0sdC53YmcuX193YmdfZGlnZXN0X2FjNTU0ZGVhMDE4MGM2NGQ9ZnVuY3Rpb24oKXtyZXR1cm4gYShmdW5jdGlvbihlLHQscixhLG8pe3JldHVybiBpKG4oZSkuZGlnZXN0KGQodCxyKSxsKGEsbykpKX0sYXJndW1lbnRzKX0sdC53YmcuX193YmdfZHJhd0ltYWdlXzAzZjdhZTJhOTVhOTYwNWY9ZnVuY3Rpb24oKXtyZXR1cm4gYShmdW5jdGlvbihlLHQscixpKXtuKGUpLmRyYXdJbWFnZShuKHQpLHIsaSl9LGFyZ3VtZW50cyl9LHQud2JnLl9fd2JnX2RyYXdJbWFnZV8wN2MzN2Y4NTYwZTU4YmJkPWZ1bmN0aW9uKCl7cmV0dXJuIGEoZnVuY3Rpb24oZSx0LHIsaSxhLG8scyxjLGwsdSl7bihlKS5kcmF3SW1hZ2Uobih0KSxyLGksYSxvLHMsYyxsLHUpfSxhcmd1bWVudHMpfSx0LndiZy5fX3diZ19lbmNyeXB0Xzc2NjIyMWQ2Njc5YTAwY2Q9ZnVuY3Rpb24oKXtyZXR1cm4gYShmdW5jdGlvbihlLHQscixhLG8pe3JldHVybiBpKG4oZSkuZW5jcnlwdChuKHQpLG4ociksbChhLG8pKSl9LGFyZ3VtZW50cyl9LHQud2JnLl9fd2JnX2ZvckVhY2hfZDZhMDVjYTk2NDIyZWZmOT1mdW5jdGlvbihlLHQscil7dHJ5e3ZhciBpPXthOnQsYjpyfTtuKGUpLmZvckVhY2goKGUsdCxuKT0+e2xldCByPWkuYTtpLmE9MDt0cnl7cmV0dXJuIGoocixpLmIsZSx0LG4pfWZpbmFsbHl7aS5hPXJ9fSl9ZmluYWxseXtpLmE9aS5iPTB9fSx0LndiZy5fX3diZ19mcm9tXzJhNWQzZTIxOGU2N2FhODU9ZnVuY3Rpb24oZSl7cmV0dXJuIGkoQXJyYXkuZnJvbShuKGUpKSl9LHQud2JnLl9fd2JnX2dldFByb3RvdHlwZU9mXzA4YWFhY2VhN2UzMDBhMzg9ZnVuY3Rpb24oKXtyZXR1cm4gYShmdW5jdGlvbihlKXtyZXR1cm4gaShSZWZsZWN0LmdldFByb3RvdHlwZU9mKG4oZSkpKX0sYXJndW1lbnRzKX0sdC53YmcuX193YmdfZ2V0XzY3YjJiYTYyZmMzMGRlMTI9ZnVuY3Rpb24oKXtyZXR1cm4gYShmdW5jdGlvbihlLHQpe3JldHVybiBpKFJlZmxlY3QuZ2V0KG4oZSksbih0KSkpfSxhcmd1bWVudHMpfSx0LndiZy5fX3diZ19oYXNfYTVlYTkxMTdmMjU4YTBlYz1mdW5jdGlvbigpe3JldHVybiBhKGZ1bmN0aW9uKGUsdCl7cmV0dXJuIFJlZmxlY3QuaGFzKG4oZSksbih0KSl9LGFyZ3VtZW50cyl9LHQud2JnLl9fd2JnX2hlaWdodF9kM2YzOWUxMmYwZjYyMTIxPWZ1bmN0aW9uKGUpe3JldHVybiBuKGUpLmhlaWdodH0sdC53YmcuX193YmdfaW1wb3J0S2V5Xzk1M2FiYWE4ZTY1NWFiMDQ9ZnVuY3Rpb24oKXtyZXR1cm4gYShmdW5jdGlvbihlLHQscixhLG8scyxjLGwpe3JldHVybiBpKG4oZSkuaW1wb3J0S2V5KGQodCxyKSxuKGEpLGQobyxzKSxjIT09MCxuKGwpKSl9LGFyZ3VtZW50cyl9LHQud2JnLl9fd2JnX2luc3RhbmNlb2ZfV2luZG93X2RlZjczZWEwOTU1ZmM1Njk9ZnVuY3Rpb24oZSl7dmFyIHQ7dHJ5e3ZhciBnPW4oZSk7dD1nIGluc3RhbmNlb2YgV2luZG93fHxnPT09Z2xvYmFsVGhpc3x8ISFnJiZnLndpbmRvdz09PWcmJiEhZy5kb2N1bWVudH1jYXRjaChnKXt0PSExfXJldHVybiB0fSx0LndiZy5fX3diZ19sZW5ndGhfYTQ0NjE5M2RjMjJjMTJmOD1mdW5jdGlvbihlKXtyZXR1cm4gbihlKS5sZW5ndGh9LHQud2JnLl9fd2JnX2xlbmd0aF9kNTY3Mzc5OTEwNzg1ODFiPWZ1bmN0aW9uKGUpe3JldHVybiBuKGUpLmxlbmd0aH0sdC53YmcuX193YmdfbGVuZ3RoX2UyZDJhNDkxMzJjMWIyNTY9ZnVuY3Rpb24oZSl7cmV0dXJuIG4oZSkubGVuZ3RofSx0LndiZy5fX3diZ19uZXdfMjNhMjY2NWZhYzgzYzYxMT1mdW5jdGlvbihlLHQpe3RyeXt2YXIgbj17YTplLGI6dH07cmV0dXJuIGkobmV3IFByb21pc2UoKGUsdCk9PntsZXQgcj1uLmE7bi5hPTA7dHJ5e3JldHVybiBNKHIsbi5iLGUsdCl9ZmluYWxseXtuLmE9cn19KSl9ZmluYWxseXtuLmE9bi5iPTB9fSx0LndiZy5fX3diZ19uZXdfNDA1ZTIyZjM5MDU3NmNlMj1mdW5jdGlvbigpe3JldHVybiBpKHt9KX0sdC53YmcuX193YmdfbmV3Xzc4ZmViMTA4YjY0NzI3MTM9ZnVuY3Rpb24oKXtyZXR1cm4gaShbXSl9LHQud2JnLl9fd2JnX25ld19hMTIwMDJhN2Y5MWM3NWJlPWZ1bmN0aW9uKGUpe3JldHVybiBpKG5ldyBVaW50OEFycmF5KG4oZSkpKX0sdC53YmcuX193YmdfbmV3bm9hcmdzXzEwNWVkNDcxNDc1YWFmNTA9ZnVuY3Rpb24oZSx0KXtyZXR1cm4gaShGdW5jdGlvbihkKGUsdCkpKX0sdC53YmcuX193YmdfbmV3d2l0aGJ5dGVvZmZzZXRhbmRsZW5ndGhfZDk3ZTYzN2ViZTE0NWE5YT1mdW5jdGlvbihlLHQscil7cmV0dXJuIGkobmV3IFVpbnQ4QXJyYXkobihlKSx0Pj4+MCxyPj4+MCkpfSx0LndiZy5fX3diZ19wYXJzZV9kZWYyZTI0ZWYxMjUyYWZmPWZ1bmN0aW9uKCl7cmV0dXJuIGEoZnVuY3Rpb24oZSx0KXtyZXR1cm4gaShKU09OLnBhcnNlKGQoZSx0KSkpfSxhcmd1bWVudHMpfSx0LndiZy5fX3diZ19wdXNoXzczN2NmYzhjMTQzMmMyYzY9ZnVuY3Rpb24oZSx0KXtyZXR1cm4gbihlKS5wdXNoKG4odCkpfSx0LndiZy5fX3diZ19xdWV1ZU1pY3JvdGFza185N2Q5MmI0ZmNjOGE2MWM1PWZ1bmN0aW9uKGUpe3F1ZXVlTWljcm90YXNrKG4oZSkpfSx0LndiZy5fX3diZ19xdWV1ZU1pY3JvdGFza19kMzIxOWRlZjgyNTUyNDg1PWZ1bmN0aW9uKGUpe2xldCB0PW4oZSkucXVldWVNaWNyb3Rhc2s7cmV0dXJuIGkodCl9LHQud2JnLl9fd2JnX3Jlc29sdmVfNDg1MTc4NWM5YzVmNTczZD1mdW5jdGlvbihlKXtyZXR1cm4gaShQcm9taXNlLnJlc29sdmUobihlKSkpfSx0LndiZy5fX3diZ19yb3RhdGVfOWEzYzc0NzdlN2ZiY2Q0MD1mdW5jdGlvbigpe3JldHVybiBhKGZ1bmN0aW9uKGUsdCl7bihlKS5yb3RhdGUodCl9LGFyZ3VtZW50cyl9LHQud2JnLl9fd2JnX3NldFRyYW5zZm9ybV84YzRkOTU0Y2FmYjM0Yjc1PWZ1bmN0aW9uKCl7cmV0dXJuIGEoZnVuY3Rpb24oZSx0LHIsaSxhLG8scyl7bihlKS5zZXRUcmFuc2Zvcm0odCxyLGksYSxvLHMpfSxhcmd1bWVudHMpfSx0LndiZy5fX3diZ19zZXRfNjU1OTViZGQ4NjhiMzAwOT1mdW5jdGlvbihlLHQscil7bihlKS5zZXQobih0KSxyPj4+MCl9LHQud2JnLl9fd2JnX3NldF9iYjhjZWNmNmE2MmI5ZjQ2PWZ1bmN0aW9uKCl7cmV0dXJuIGEoZnVuY3Rpb24oZSx0LHIpe3JldHVybiBSZWZsZWN0LnNldChuKGUpLG4odCksbihyKSl9LGFyZ3VtZW50cyl9LHQud2JnLl9fd2JnX3N0YXRpY19hY2Nlc3Nvcl9HTE9CQUxfODhhOTAyZDEzYTU1N2QwNz1mdW5jdGlvbigpe2xldCBlPXR5cGVvZiBnbG9iYWw+YHVgP251bGw6Z2xvYmFsO3JldHVybiBvKGUpPzA6aShlKX0sdC53YmcuX193Ymdfc3RhdGljX2FjY2Vzc29yX0dMT0JBTF9USElTXzU2NTc4YmU3ZTlmODMyYjA9ZnVuY3Rpb24oKXtsZXQgZT10eXBlb2YgZ2xvYmFsVGhpcz5gdWA/bnVsbDpnbG9iYWxUaGlzO3JldHVybiBvKGUpPzA6aShlKX0sdC53YmcuX193Ymdfc3RhdGljX2FjY2Vzc29yX1NFTEZfMzdjNWQ0MThlNGJmNTgxOT1mdW5jdGlvbigpe2xldCBlPXR5cGVvZiBzZWxmPmB1YD9udWxsOnNlbGY7cmV0dXJuIG8oZSk/MDppKGUpfSx0LndiZy5fX3diZ19zdGF0aWNfYWNjZXNzb3JfV0lORE9XXzVkZTM3MDQzYTkxYTljNDA9ZnVuY3Rpb24oKXtsZXQgZT10eXBlb2Ygd2luZG93PmB1YD9udWxsOndpbmRvdztyZXR1cm4gbyhlKT8wOmkoZSl9LHQud2JnLl9fd2JnX3N1YnN0cmluZ19jMjEyYzA0NGUzMzliYmIwPWZ1bmN0aW9uKGUsdCxyKXtyZXR1cm4gaShuKGUpLnN1YnN0cmluZyh0Pj4+MCxyPj4+MCkpfSx0LndiZy5fX3diZ19zdWJ0bGVfZDA2MTQxOTNhMGI3YTYyNj1mdW5jdGlvbihlKXtsZXQgdD1uKGUpLnN1YnRsZTtyZXR1cm4gaSh0KX0sdC53YmcuX193YmdfdGhlbl80NGI3Mzk0NmQyZmIzZTdkPWZ1bmN0aW9uKGUsdCl7cmV0dXJuIGkobihlKS50aGVuKG4odCkpKX0sdC53YmcuX193YmdfdGhlbl9jZDY0OWNjYmE3M2JkODlhPWZ1bmN0aW9uKGUsdCxyKXtyZXR1cm4gaShuKGUpLnRoZW4obih0KSxuKHIpKSl9LHQud2JnLl9fd2JnX3dpZHRoXzRmMzM0ZmM0N2VmMDNkZTE9ZnVuY3Rpb24oZSl7cmV0dXJuIG4oZSkud2lkdGh9LHQud2JnLl9fd2JpbmRnZW5fY2JfZHJvcD1mdW5jdGlvbihlKXtsZXQgdD1wKGUpLm9yaWdpbmFsO3JldHVybiB0LmNudC0tPT0xJiYodC5hPTAsITApfSx0LndiZy5fX3diaW5kZ2VuX2Nsb3N1cmVfd3JhcHBlcjIxOT1mdW5jdGlvbihlLHQsbil7cmV0dXJuIGkoaChlLHQsNzIsQSkpfSx0LndiZy5fX3diaW5kZ2VuX2RlYnVnX3N0cmluZz1mdW5jdGlvbih0LHIpe2xldCBpPWIoZyhuKHIpKSxlLl9fd2JpbmRnZW5fbWFsbG9jLGUuX193YmluZGdlbl9yZWFsbG9jKSxhPV87UygpLnNldEludDMyKHQrNCxhLCEwKSxTKCkuc2V0SW50MzIodCswLGksITApfSx0LndiZy5fX3diaW5kZ2VuX2lzX2Z1bmN0aW9uPWZ1bmN0aW9uKGUpe3JldHVybiB0eXBlb2YgbihlKT09YGZ1bmN0aW9uYH0sdC53YmcuX193YmluZGdlbl9pc19udWxsPWZ1bmN0aW9uKGUpe3JldHVybiBuKGUpPT09bnVsbH0sdC53YmcuX193YmluZGdlbl9pc191bmRlZmluZWQ9ZnVuY3Rpb24oZSl7cmV0dXJuIG4oZSk9PT12b2lkIDB9LHQud2JnLl9fd2JpbmRnZW5fbWVtb3J5PWZ1bmN0aW9uKCl7bGV0IHQ9ZS5tZW1vcnk7cmV0dXJuIGkodCl9LHQud2JnLl9fd2JpbmRnZW5fbnVtYmVyX2dldD1mdW5jdGlvbihlLHQpe2xldCByPW4odCksaT10eXBlb2Ygcj09YG51bWJlcmA/cjp2b2lkIDA7UygpLnNldEZsb2F0NjQoZSs4LG8oaSk/MDppLCEwKSxTKCkuc2V0SW50MzIoZSswLCFvKGkpLCEwKX0sdC53YmcuX193YmluZGdlbl9udW1iZXJfbmV3PWZ1bmN0aW9uKGUpe3JldHVybiBpKGUpfSx0LndiZy5fX3diaW5kZ2VuX29iamVjdF9jbG9uZV9yZWY9ZnVuY3Rpb24oZSl7cmV0dXJuIGkobihlKSl9LHQud2JnLl9fd2JpbmRnZW5fb2JqZWN0X2Ryb3BfcmVmPWZ1bmN0aW9uKGUpe3AoZSl9LHQud2JnLl9fd2JpbmRnZW5fc3RyaW5nX2dldD1mdW5jdGlvbih0LHIpe2xldCBpPW4ociksYT10eXBlb2YgaT09YHN0cmluZ2A/aTp2b2lkIDA7dmFyIHM9byhhKT8wOmIoYSxlLl9fd2JpbmRnZW5fbWFsbG9jLGUuX193YmluZGdlbl9yZWFsbG9jKSxjPV87UygpLnNldEludDMyKHQrNCxjLCEwKSxTKCkuc2V0SW50MzIodCswLHMsITApfSx0LndiZy5fX3diaW5kZ2VuX3N0cmluZ19uZXc9ZnVuY3Rpb24oZSx0KXtyZXR1cm4gaShkKGUsdCkpfSx0LndiZy5fX3diaW5kZ2VuX3Rocm93PWZ1bmN0aW9uKGUsdCl7dGhyb3cgRXJyb3IoZChlLHQpKX0sdH1mdW5jdGlvbiBGKHQsbil7cmV0dXJuIGU9dC5leHBvcnRzLEkuX193YmluZGdlbl93YXNtX21vZHVsZT1uLHg9bnVsbCxzPW51bGwsZX1hc3luYyBmdW5jdGlvbiBJKHQpe2lmKGUhPT12b2lkIDApcmV0dXJuIGU7dCE9PXZvaWQgMCYmKE9iamVjdC5nZXRQcm90b3R5cGVPZih0KT09PU9iamVjdC5wcm90b3R5cGU/e21vZHVsZV9vcl9wYXRoOnR9PXQ6Y29uc29sZS53YXJuKGB1c2luZyBkZXByZWNhdGVkIHBhcmFtZXRlcnMgZm9yIHRoZSBpbml0aWFsaXphdGlvbiBmdW5jdGlvbjsgcGFzcyBhIHNpbmdsZSBvYmplY3QgaW5zdGVhZGApKSx0PT09dm9pZCAwJiYodD0odHlwZW9mIGdsb2JhbFRoaXMuX19FQkpEX0dMVUVfV0FTTV9fPT1gZnVuY3Rpb25gP2dsb2JhbFRoaXMuX19FQkpEX0dMVUVfV0FTTV9fKCk6bnVsbCl8fGBicl9jb3JlX2JnLkJZNDlrclVvLndhc21gKTtsZXQgbj1QKCk7KHR5cGVvZiB0PT1gc3RyaW5nYHx8dHlwZW9mIFJlcXVlc3Q9PWBmdW5jdGlvbmAmJnQgaW5zdGFuY2VvZiBSZXF1ZXN0fHx0eXBlb2YgVVJMPT1gZnVuY3Rpb25gJiZ0IGluc3RhbmNlb2YgVVJMKSYmKHQ9ZmV0Y2godCkpO2xldHtpbnN0YW5jZTpyLG1vZHVsZTppfT1hd2FpdCBOKGF3YWl0IHQsbik7cmV0dXJuIEYocixpKX1yZXR1cm4geyJkZWNyeXB0X3Nlc3Npb24iOkMsImRlY3J5cHRfeGoiOncsImRlZmF1bHQiOkksImdldF9wYWdlX25hbWUiOmssImdldF9zcGVjaWFsX3VybCI6Tywib3Blbl9wYXJhbSI6RCwicmFuZ2VzIjpFLCJzaHVmZmxlIjpUfTs=';
    const EBJ_WASM_B64 = 'AGFzbQEAAAABhAIhYAJ/fwF/YAF/AGACf38AYAF/AX9gA39/fwF/YAN/f38AYAR/f39/AGAAAX9gBX9/f39/AGAFf39/f38Bf2AGf39/f39/AGAHf39/f39/fwBgBH9/f38Bf2AIf39/f39/f38Bf2AGf39/f39/AX9gAABgAXwBf2AEf398fABgCn9/fHx8fHx8fHwAYAV/fHx8fABgAn98AGAHf3x8fHx8fABgB39/f39/f38Bf2ADfn9/AX9gC39/f39/f39/f39/AX9gC39/f3x8fHx8fHx8AGADf398AGAFf39+f38AYAR/fn9/AGAFf398f38AYAR/fH9/AGAFf399f38AYAR/fX9/AAL6EDwDd2JnGl9fd2JpbmRnZW5fb2JqZWN0X2Ryb3BfcmVmAAEDd2JnFV9fd2JpbmRnZW5fc3RyaW5nX25ldwAAA3diZxVfX3diaW5kZ2VuX251bWJlcl9uZXcAEAN3YmcbX193YmluZGdlbl9vYmplY3RfY2xvbmVfcmVmAAMDd2JnFV9fd2JpbmRnZW5fbnVtYmVyX2dldAACA3diZxdfX3diaW5kZ2VuX2lzX3VuZGVmaW5lZAADA3diZxVfX3diaW5kZ2VuX3N0cmluZ19nZXQAAgN3YmcSX193YmluZGdlbl9jYl9kcm9wAAMDd2JnEl9fd2JpbmRnZW5faXNfbnVsbAADA3diZyVfX3diZ19xdWV1ZU1pY3JvdGFza185N2Q5MmI0ZmNjOGE2MWM1AAEDd2JnJV9fd2JnX3F1ZXVlTWljcm90YXNrX2QzMjE5ZGVmODI1NTI0ODUAAwN3YmcWX193YmluZGdlbl9pc19mdW5jdGlvbgADA3diZyhfX3diZ19pbnN0YW5jZW9mX1dpbmRvd19kZWY3M2VhMDk1NWZjNTY5AAMDd2JnHV9fd2JnX2NyeXB0b18xMjU3NmNkNjYyNDY5OThiAAMDd2JnHl9fd2JnX2RlY3J5cHRfZDUyZjJkNzFhNWI4YmVkZgAJA3diZx1fX3diZ19kaWdlc3RfYWM1NTRkZWEwMTgwYzY0ZAAJA3diZx5fX3diZ19lbmNyeXB0Xzc2NjIyMWQ2Njc5YTAwY2QACQN3YmcgX193YmdfaW1wb3J0S2V5Xzk1M2FiYWE4ZTY1NWFiMDQADQN3YmcdX193YmdfY2FudmFzXzliYmNkYjk0YTk3NzgwN2EAAwN3YmcgX193YmdfZHJhd0ltYWdlXzAzZjdhZTJhOTVhOTYwNWYAEQN3YmcgX193YmdfZHJhd0ltYWdlXzA3YzM3Zjg1NjBlNThiYmQAEgN3YmcgX193YmdfY2xlYXJSZWN0XzhlNGJhN2VhMGUwNjcxMWEAEwN3YmcdX193Ymdfcm90YXRlXzlhM2M3NDc3ZTdmYmNkNDAAFAN3YmcjX193Ymdfc2V0VHJhbnNmb3JtXzhjNGQ5NTRjYWZiMzRiNzUAFQN3YmcdX193Ymdfc3VidGxlX2QwNjE0MTkzYTBiN2E2MjYAAwN3YmccX193Ymdfd2lkdGhfNGYzMzRmYzQ3ZWYwM2RlMQADA3diZx1fX3diZ19oZWlnaHRfZDNmMzllMTJmMGY2MjEyMQADA3diZx1fX3diZ19sZW5ndGhfZTJkMmE0OTEzMmMxYjI1NgADA3diZxpfX3diZ19uZXdfNzhmZWIxMDhiNjQ3MjcxMwAHA3diZyBfX3diZ19uZXdub2FyZ3NfMTA1ZWQ0NzE0NzVhYWY1MAAAA3diZxpfX3diZ19nZXRfNjdiMmJhNjJmYzMwZGUxMgAAA3diZxtfX3diZ19jYWxsXzY3MmE0ZDIxNjM0ZDRhMjQAAAN3YmcaX193YmdfbmV3XzQwNWUyMmYzOTA1NzZjZTIABwN3YmcdX193YmdfbGVuZ3RoX2Q1NjczNzk5MTA3ODU4MWIAAwN3YmcbX193YmdfZnJvbV8yYTVkM2UyMThlNjdhYTg1AAMDd2JnHl9fd2JnX2ZvckVhY2hfZDZhMDVjYTk2NDIyZWZmOQAFA3diZxtfX3diZ19wdXNoXzczN2NmYzhjMTQzMmMyYzYAAAN3YmcbX193YmdfY2FsbF83Y2NjZGQ2OWUwNzkxYWUyAAQDd2JnIF9fd2JnX3N1YnN0cmluZ19jMjEyYzA0NGUzMzliYmIwAAQDd2JnGl9fd2JnX25ld18yM2EyNjY1ZmFjODNjNjExAAADd2JnHl9fd2JnX3Jlc29sdmVfNDg1MTc4NWM5YzVmNTczZAADA3diZxtfX3diZ190aGVuXzQ0YjczOTQ2ZDJmYjNlN2QAAAN3YmcbX193YmdfdGhlbl9jZDY0OWNjYmE3M2JkODlhAAQDd2JnMl9fd2JnX3N0YXRpY19hY2Nlc3Nvcl9HTE9CQUxfVEhJU181NjU3OGJlN2U5ZjgzMmIwAAcDd2JnK19fd2JnX3N0YXRpY19hY2Nlc3Nvcl9TRUxGXzM3YzVkNDE4ZTRiZjU4MTkABwN3YmctX193Ymdfc3RhdGljX2FjY2Vzc29yX1dJTkRPV181ZGUzNzA0M2E5MWE5YzQwAAcDd2JnLV9fd2JnX3N0YXRpY19hY2Nlc3Nvcl9HTE9CQUxfODhhOTAyZDEzYTU1N2QwNwAHA3diZx1fX3diZ19idWZmZXJfNjA5Y2MzZWVlNTFlZDE1OAADA3diZzFfX3diZ19uZXd3aXRoYnl0ZW9mZnNldGFuZGxlbmd0aF9kOTdlNjM3ZWJlMTQ1YTlhAAQDd2JnGl9fd2JnX25ld19hMTIwMDJhN2Y5MWM3NWJlAAMDd2JnGl9fd2JnX3NldF82NTU5NWJkZDg2OGIzMDA5AAUDd2JnHV9fd2JnX2xlbmd0aF9hNDQ2MTkzZGMyMmMxMmY4AAMDd2JnJV9fd2JnX2dldFByb3RvdHlwZU9mXzA4YWFhY2VhN2UzMDBhMzgAAwN3YmcaX193YmdfaGFzX2E1ZWE5MTE3ZjI1OGEwZWMAAAN3YmcaX193Ymdfc2V0X2JiOGNlY2Y2YTYyYjlmNDYABAN3YmccX193YmdfcGFyc2VfZGVmMmUyNGVmMTI1MmFmZgAAA3diZxdfX3diaW5kZ2VuX2RlYnVnX3N0cmluZwACA3diZxBfX3diaW5kZ2VuX3Rocm93AAIDd2JnEV9fd2JpbmRnZW5fbWVtb3J5AAcDd2JnHV9fd2JpbmRnZW5fY2xvc3VyZV93cmFwcGVyMjE5AAQDlgKUAgMABAAGCAUGAQoGCwsEAAQLAQUOBQgCAgQDBQICBAIPAgUGAQIAAwIWAwMJAAIXAAIGAQEFAgAGAgYHAQoCBgIBAAEABwECBQECAgIGAwUIBQIFBgUFBwUFGAEKAQAAAgAHAgIBAQEBDQEIAwIIAAECAwMDAgUGBQUFBQIEAgICGQYCBgEFBQQEAQIAAgICBQIFAAAGGgkBDwICAAwAAAAAAAYGBgIABgUAAAICAQEHAAUOCBsdCR8AAgICBgIFBQQDAQEAAwMCAAAAAQIBAQEBAAAMBQMCAQMACAACAAIEAAUBAgIAAAIDAAMDBgUCAwMCAwAAAAAABAMAAAIDAwMDAgQCBAUEAgMAAwAAAAMDAwMBBQQHAXABmQGZAQUDAQARBgkBfwFBgIDAAAsHhwQRBm1lbW9yeQIAD2RlY3J5cHRfc2Vzc2lvbgCkAQpkZWNyeXB0X3hqAJsCB3NodWZmbGUA0wEGcmFuZ2VzAMwCCm9wZW5fcGFyYW0AzQIPZ2V0X3NwZWNpYWxfdXJsAJYBDWdldF9wYWdlX25hbWUAuAEUX193YmluZGdlbl9leG5fc3RvcmUAngITX193YmluZGdlbl9leHBvcnRfMQEAEV9fd2JpbmRnZW5fbWFsbG9jAM8BEl9fd2JpbmRnZW5fcmVhbGxvYwDYAR9fX3diaW5kZ2VuX2FkZF90b19zdGFja19wb2ludGVyALUCD19fd2JpbmRnZW5fZnJlZQCQAnxfZHluX2NvcmVfX29wc19fZnVuY3Rpb25fX0ZuTXV0X19BX19fX091dHB1dF9fX1JfYXNfd2FzbV9iaW5kZ2VuX19jbG9zdXJlX19XYXNtQ2xvc3VyZV9fX2Rlc2NyaWJlX19pbnZva2VfX2hkNWI2ZGYwYWE1YTViZjE0APsBP3dhc21fYmluZGdlbl9fY29udmVydF9fY2xvc3VyZXNfX2ludm9rZTNfbXV0X19oMjg0MGQ0NTZjZjkwNWExNwDvAT93YXNtX2JpbmRnZW5fX2NvbnZlcnRfX2Nsb3N1cmVzX19pbnZva2UyX211dF9faDE2YmY4NzUxMjg3Y2UzNjEA+AEJrQICAEEBC0WOArEClwKZAsABxwLOAuABQ/0BrQGuAd8BRocCnAGJAd4BbagCdZcCtgLOApMBkAGUAZEBoAE/oQE9sgKaAf4BlwKiAsMCmgKSAs8CswL+Ac4C1gH3AewBwQHOAogC9gHHAbEBzgLaAYUChAKXAs4CtwH5AZgCrwH+Ac4C4QGYAcUBpQEAQccAC1L7AegB+gGrAZ8BY5MCyQG7AcgBugHOAn7OAf4BwwKaAs8CzgLlAc4C2QHyAZcB7wHyAe4B/AH4Ae8B7wHzAfEB8AGAAYkCigKLAowClwL/AbkBzgLDAWjbAeYBzgL0Af4BogKhAp8CmALMAaMC6gGCAZ4BzgKgAoACzgLEAa8C3AHOAoYCsAKVAqUCqgFyzgKgAs4CWX/iAbQCfd0BCqWJB5QC+yECD38BfiMAQRBrIgskAAJA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NgIADAELQazlwQAoAgANAUG05cEAKAIAIQVBsOXBACgCACEGQbDlwQAgASkCADcCAEG45cEAIAFBCGooAgA2AgBBrOXBAEEANgIAIAZFIAVFcg0AIAYQRAsgA0EQaiQADAELQdynwABBECADQQ9qQeynwABB+KrAABCpAQALQQALIQMgAEGwAWooAgAEQCAAQawBaigCABBECyAAQZwBaigCAARAIABBmAFqKAIAEEQLIABBkAFqKAIABEAgAEGMAWooAgAQRAsgAEGEAWooAgAEQCAAQYABaigCABBECyAAQbwBaigCAARAIABBuAFqKAIAEEQLIABBqAFqKAIAIgFBhAFJDQEgARAADAELIABBhAFqKAIARQRAQQEhAwwBC0EBIQMgAEGAAWooAgAQRAsgAEH4AGooAgAEQCAAQfQAaigCABBECyAAQewAaigCAARAIABB6ABqKAIAEEQLIABB4ABqKAIABEAgAEHcAGooAgAQRAsgAEHUAGooAgAEQCAAQdAAaigCABBECyAJQQE6AAALAkACQCADQQJGBEBBAyEEIABBAzoA/AEMAQsgCxBNIABBAToA/AEgBEGAASADGyEBAkAgAwRAIAIgATYCUCACQYABNgIwIAJBCGogAEGEAmogAkEwaiACQdAAahC/ASACKAIIRQRAIAIoAgwiAUGEAU8EQCABEAALIAIoAjAiAUGEAU8EQCABEAALIAIoAlAiAUGEAUkNAiABEAAMAgtBsJ/AAEExELgCAAsgAiABNgJQIAJBgAE2AjAgAiAAQYACaiACQTBqIAJB0ABqEL8BIAIoAgANAiACKAIEIgFBhAFPBEAgARAACyACKAIwIgFBhAFPBEAgARAACyACKAJQIgFBhAFJDQAgARAACyAAKAKAAiIBQYQBTwRAIAEQAAtBASEEIAAoAoQCIgFBhAFJDQAgARAACyAAIAQ6AIgEIAJB4ABqJAAgA0ECRg8LQbCfwABBMRC4AgALrxMBCn8jAEHQAWsiAyQAIAMCf0Gg5cEALQAARQRAQaTlwQBBAjYCAEGg5cEAQQE6AABBAgwBC0Gk5cEAKAIACzYCkAEgA0EgaiADQZABahBXAkACQAJAAkACQAJAIANBxQBqLQAARQRAAkAgAUUEQEEBIQcMAQsgAUEASA0FQb3lwQAtAAAaIAFBARCcAiIHRQ0CCyAHIAAgARDAAhogASEJDAMLIANBkAFqIgVBtYvAACAAIAEQeiADKAKQASIARQ0BIAMoApQBIANB6ABqIAAgAygCmAEQXSADKAJsIQkgBSADKAJoIgcgAygCcCIBEFACQCADKAKQAUUNACADQZgBajEAAEIghkKAgICAIFENAEEAIQEgCUUEQEEBIQdBACEJDAELIAcQREEAIQlBASEHC0UNAiAAEEQMAgtBASABEL0CAAtBmI7AAEETQayOwAAQ5AEACwJAIANBxABqLQAARQ0AIANBEGogA0HoAGogA0GEAWoCfwJAIAIgA0FAaygCACIASQRAIAMoAjggA0EANgJwIANCATcCaCADIAE2ApgBIAMgCTYClAEgAyAHNgKQASADQZABaiIAKAIAIgEgACgCCBABIQQgACgCBARAIAEQRAsgAyAENgKEASACQRRsaiIEKAIQIgkNAUEAIQBBACEFQQAMAgsgAiAAQfiNwAAQtAEACyAEQRBqIARBDGohCEEAIQJBACEFQQAhAEEAIQECQANAIAQoAggiBiABSwRAIANBGGogA0HoAGogA0GEAWogCCgCACIGIAQoAgAgAmooAgBsIAYgBSAAQQFxEEwgAkEEaiECIAMtABlBAXEhACADLQAYIQUgAUEBaiIBIAlHDQEMAgsLIAEgBkGIjsAAELQBAAsoAgALIAQoAgxsQQAgBSAAEEwgAygCbCEJIANBkAFqIAMoAmgiByADKAJwIgEQUAJAIAMoApABRQ0AIANBmAFqMQAAQiCGQoCAgIAgUQ0AQQAhASAJBEAgBxBEC0EBIQdBACEJCyADKAKEASIAQYQBSQ0AIAAQAAsgA0GQAWoiACAHIAFBmIvAABBAIANB6ABqIAAQUwJAIAMoAmgEQAJAIAMoAmwiAEUNACAAIAFPBEAgACABRg0BDAYLIAAgB2osAABBv39MDQULIAMgBzYCYCADIAA2AmRBACEIIANBADYCjAEgA0IBNwKEASADQZABaiICIAAgB2oiBiABIABrIgpBrIvAABBAIANB6ABqIAIQUwJAIAMoAmhFBEBBASECQQAhAUEAIQUMAQtBACEBQQEhAkEAIQADQCADKAJwIQUgAygCbCAAayIEIAMoAogBIAFrSwRAIANBhAFqIAEgBBCKASADKAKEASECIAMoAowBIQELIAEgAmogACAGaiAEEMACGiADIAEgBGoiATYCjAEgAygCiAEgAWtBAU0EQCADQYQBaiABQQIQigEgAygCjAEhAQsgAygChAEiAiABakGsxAA7AAAgAyABQQJqIgE2AowBIANB6ABqIANBkAFqEFMgBSEAIAMoAmgNAAsgAygCiAEhCAsgCiAFayIEIAggAWtLBEAgA0GEAWogASAEEIoBIAMoAoQBIQIgAygCjAEhAQsgASACaiAFIAZqIAQQwAIaIAMoAogBQQAhACADQQA2AowBIANCATcChAEgA0GQAWoiBSACIAEgBGoiBkGvi8AAEEAgA0HoAGogBRBTAkAgAygCaEUEQEEBIQhBACEBQQAhBAwBC0EAIQFBASEIQQAhBQNAIAMoAnAhBCADKAJsIAVrIgAgAygCiAEgAWtLBEAgA0GEAWogASAAEIoBIAMoAoQBIQggAygCjAEhAQsgASAIaiACIAVqIAAQwAIaIAMgACABaiIBNgKMASADKAKIASABa0EBTQRAIANBhAFqIAFBAhCKASADKAKMASEBCyADKAKEASIIIAFqQfvEADsAACADIAFBAmoiATYCjAEgA0HoAGogA0GQAWoQUyAEIQUgAygCaA0ACyADKAKIASEACyAGIARrIgYgACABa0sEQCADQYQBaiABIAYQigEgAygChAEhCCADKAKMASEBCyABIAhqIAIgBGogBhDAAhogAygCiAFBACEFIANBADYCjAEgA0IBNwKEASADQZABaiIAIAggASAGaiIMQbKLwAAQQCADQegAaiAAEFMCQCADKAJoRQRAQQEhBEEAIQFBACEADAELQQAhAUEBIQQDQCADKAJwIQAgAygCbCAFayIGIAMoAogBIAFrSwRAIANBhAFqIAEgBhCKASADKAKEASEEIAMoAowBIQELIAEgBGogBSAIaiAGEMACGiADIAEgBmoiATYCjAEgAygCiAEgAWtBAU0EQCADQYQBaiABQQIQigEgAygCjAEhAQsgAygChAEiBCABakGi9AA7AAAgAyABQQJqIgE2AowBIANB6ABqIANBkAFqEFMgACEFIAMoAmgNAAsgAygCiAEhBQsgDCAAayIGIAUgAWtLBEAgA0GEAWogASAGEIoBIAMoAoQBIQQgAygCjAEhAQsgASAEaiAAIAhqIAYQwAIaIANBgAFqIAEgBmo2AgAgA0H0AGpBAzYC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IAIgAiAHSRshCgNAIAIgCkYNAiADIAJBAWoiBzoAGiACIAtGDQQgA0EQaiACaiEGIAchAiAMIAYtAAAgDhEAAEUNAAsLDAcLAn9BASAJQYABSQ0AGkECIAlBgBBJDQAaQQNBBCAJQYCABEkbCyAFaiECCyAFIAhrIARqIQUgBCAQRw0BDAMLCyALQQpB3PnAABC0AQALIAAgASACIAVB6ObAABCWAgALIAJFBEBBACECDAELAkAgASACTQRAIAEgAkYNAQwECyAAIAJqLAAAQb9/TA0DCyABIAJrIQELIAwgACACaiABIA8oAgwRBAANACAMQSIgDhEAACENCyADQSBqJAAgDQ8LIAAgASACIAFB2ObAABCWAgALxAYBA38jAEEQayIHJAACfyAERQRAIAIoAgAQIQwBCyADIARqCyEEIAdBCGogAigCACADIAQQJiICEAYCQAJAAkAgBygCCCIJBEAgBygCDCEIIAJBgwFLBEAgAhAACyAIRQ0DQQAhBANAIAQgCWotAAAhAgJAAkACQCAGQQFxRQRAAkACQAJAIAJB3ABHBEAgAkEJRgRAIAEoAggiAiABKAIERgR/IAEgAhCNASABKAIIBSACCyABKAIAakH9ADoAACABIAEoAghBAWoiAjYCCCABKAIEIAJGBH8gASACEI0BIAEoAggFIAILIAEoAgBqQSw6AAAgASABKAIIQQFqNgIIQfsAIQILIAVB/wFxDgIBAgMLIAEoAggiAyABKAIERw0GDAULIAEoAggiAyABKAIERgR/IAEgAxCNASABKAIIBSADCyABKAIAaiACOgAAIAEgASgCCEEBaiIDNgIIIAJBLEYgAkH7AEZyRQRAIAJBIkZBAXQhBQwECyABKAIEIANGBH8gASADEI0BIAEoAggFIAMLIAEoAgBqQSI6AABBASEFIAEgASgCCEEBajYCCAwDCyABKAIEIQUgASgCCCEDIAJBOkcEQCADIAVGBH8gASADEI0BIAEoAggFIAMLIAEoAgBqIAI6AABBASEFIAEgASgCCEEBajYCCAwDCyADIAVGBH8gASADEI0BIAEoAggFIAMLIAEoAgBqQSI6AAAgASABKAIIQQFqIgI2AgggASgCBCACRgR/IAEgAhCNASABKAIIBSACCyABKAIAakE6OgAAIAEgASgCCEEBajYCCEEAIQUMAgsgASgCCCIDIAEoAgRGBH8gASADEI0BIAEoAggFIAMLIAEoAgBqIAI6AAAgASABKAIIQQFqNgIIIAJBIkdBAXQhBQwBCyABKAIIIgMgASgCBEYNAQwCC0EAIQYgBEEBaiIEIAhJDQIMBQsgASADEI0BIAEoAgghAwsgASgCACADaiACOgAAIAEgASgCCEEBajYCCCAGQQFzIQYgCCAEQQFqIgRLDQALDAELQeyBwABBK0GIi8AAEM0BAAsgBkEBcSEGCyAJEEQLIAAgBjoAASAAIAU6AAAgB0EQaiQAC8QFAQF/AkACfwJAAkACQAJAAkAgAC0AhAEOBgAGBgECAwYLIAAoAgQEQCAAKAIAEEQLIABBEGooAgAEQCAAKAIMEEQLIABBHGooAgAEQCAAKAIYEEQLIABBJGoMBAsCQAJAAkAgAEGsAWotAABBA2sOAgABBQsgAEGwAWoQfAwBCyAAQbQBahB8IABBsAFqKAIAIgFBhAFJDQAgARAACyAAQaQBaigCAEUNAiAAQaABaigCABBEDAILAkAgAEHMAWotAABBA0cNAAJAAkACQCAAQbUBai0AAEEDaw4CAAEDCyAAQbgBahB8DAELIABBwAFqEHwgAEG8AWooAgAiAUGEAU8EQCABEAALIABBuAFqKAIAIgFBhAFJDQAgARAACyAAQagBaigCACIBQYQBSQ0AIAEQAAsgAEGQAWooAgAEQCAAKAKMARBECyAAKAKIASIBQYQBTwRAIAEQAAsgAEHwAGooAgAEQCAAKAJsEEQLIABB5ABqKAIARQ0BIAAoAmAQRAwBCwJAIABB2AFqLQAAQQNHDQACQAJAAkAgAEHBAWotAABBA2sOAgABAwsgAEHEAWoQfAwBCyAAQcwBahB8IABByAFqKAIAIgFBhAFPBEAgARAACyAAQcQBaigCACIBQYQBSQ0AIAEQAAsgAEG0AWooAgAiAUGEAUkNACABEAALIABBkAFqKAIABEAgACgCjAEQRAsgAEH8AGooAgAEQCAAKAJ4EEQLIABB8ABqKAIABEAgACgCbBBECyAAQeQAaigCAARAIAAoAmAQRAsgAEGcAWooAgAEQCAAKAKYARBECyAAKAKIASIBQYQBSQ0AIAEQAAsgAEHYAGooAgAEQCAAKAJUEEQLIABBzABqKAIABEAgACgCSBBECyAAQUBrKAIABEAgACgCPBBECyAAQTBqCyIAKAIERQ0AIAAoAgAQRAsLtgsBBX8jAEEQayIDJAACQAJAAkACQAJAAkACQAJAAkACQCABDigFCAgICAgICAgBAwgIAggICAgICAgICAgICAgICAgICAgIBggICAgHAAsgAUHcAEYNAwwHCyAAQYAEOwEKIABCADcBAiAAQdzoATsBAAwHCyAAQYAEOwEKIABCADcBAiAAQdzkATsBAAwGCyAAQYAEOwEKIABCADcBAiAAQdzcATsBAAwFCyAAQYAEOwEKIABCADcBAiAAQdy4ATsBAAwECyAAQYAEOwEKIABCADcBAiAAQdzgADsBAAwDCyACQYCABHFFDQEgAEGABDsBCiAAQgA3AQIgAEHcxAA7AQAMAgsgAkGAAnFFDQAgAEGABDsBCiAAQgA3AQIgAEHczgA7AQAMAQsCQAJAAkACQCACQQFxBEACfyABQQt0IQZBISEFQSEhAgJAA0ACQAJAQX8gBUEBdiAEaiIFQQJ0QYCFwQBqKAIAQQt0IgcgBkcgBiAHSxsiB0EBRgRAIAUhAgwBCyAHQf8BcUH/AUcNASAFQQFqIQQLIAIgBGshBSACIARLDQEMAgsLIAVBAWohBAsCfwJ/AkAgBEEgTQRAIARBAnQiBUGAhcEAaigCAEEVdiECIARBIEcNAUHXBSEFQR8MAgsgBEEhQfz4wAAQtAEACyAFQYSFwQBqKAIAQRV2IQVBACAERQ0BGiAEQQFrC0ECdEGAhcEAaigCAEH///8AcQshBAJAAkAgBSACQX9zakUNACABIARrIQdB1wUgAiACQdcFTRshBiAFQQFrIQVBACEEA0AgAiAGRg0CIAQgAkGEhsEAai0AAGoiBCAHSw0BIAUgAkEBaiICRw0ACyAFIQILIAJBAXEMAQsgBkHXBUGM+cAAELQBAAsNAQsCfwJAIAFBIEkNAAJAAn9BASABQf8ASQ0AGiABQYCABEkNAQJAIAFBgIAITwRAIAFBsMcMa0HQuitJIAFBy6YMa0EFSXIgAUGe9AtrQeILSSABQeHXC2tBnxhJcnIgAUF+cUGe8ApGIAFBop0La0EOSXJyDQQgAUFgcUHgzQpHDQEMBAsgAUHY7cAAQSxBsO7AAEHEAUH078AAQcIDEGQMBAtBACABQbruCmtBBkkNABogAUGAgMQAa0Hwg3RJCwwCCyABQbbzwABBKEGG9MAAQZ8CQaX2wABBrwIQZAwBC0EAC0UNASAAIAE2AgQgAEGAAToAAAwECyADQQhqQQA6AAAgA0EAOwEGIANB/QA6AA8gAyABQQ9xQZz5wABqLQAAOgAOIAMgAUEEdkEPcUGc+cAAai0AADoADSADIAFBCHZBD3FBnPnAAGotAAA6AAwgAyABQQx2QQ9xQZz5wABqLQAAOgALIAMgAUEQdkEPcUGc+cAAai0AADoACiADIAFBFHZBD3FBnPnAAGotAAA6AAkgAUEBcmdBAnZBAmsiAUELTw0BIANBBmogAWoiAkHY+cAALwAAOwAAIAJBAmpB2vnAAC0AADoAACAAIAMpAQY3AAAgAEEIaiADQQ5qLwEAOwAAIABBCjoACyAAIAE6AAoMAwsgA0EIakEAOgAAIANBADsBBiADQf0AOgAPIAMgAUEPcUGc+cAAai0AADoADiADIAFBBHZBD3FBnPnAAGotAAA6AA0gAyABQQh2QQ9xQZz5wABqLQAAOgAMIAMgAUEMdkEPcUGc+cAAai0AADoACyADIAFBEHZBD3FBnPnAAGotAAA6AAogAyABQRR2QQ9xQZz5wABqLQAAOgAJIAFBAXJnQQJ2QQJrIgFBC08NASADQQZqIAFqIgJB2PnAAC8AADsAACACQQJqQdr5wAAtAAA6AAAgACADKQEGNwAAIABBCGogA0EOai8BADsAACAAQQo6AAsgACABOgAKDAILIAFBCkHI+cAAELMBAAsgAUEKQcj5wAAQswEACyADQRBqJAAL3gUBB38CfyABBEBBK0GAgMQAIAAoAhwiCEEBcSIBGyEKIAEgBWoMAQsgACgCHCEIQS0hCiAFQQFqCyEGAkAgCEEEcUUEQEEAIQIMAQsCQCADQRBPBEAgAiADEEohAQwBCyADRQRAQQAhAQwBCyADQQNxIQkCQCADQQRJBEBBACEBDAELIANBfHEhDEEAIQEDQCABIAIgB2oiCywAAEG/f0pqIAtBAWosAABBv39KaiALQQJqLAAAQb9/SmogC0EDaiwAAEG/f0pqIQEgDCAHQQRqIgdHDQALCyAJRQ0AIAIgB2ohBwNAIAEgBywAAEG/f0pqIQEgB0EBaiEHIAlBAWsiCQ0ACwsgASAGaiEGCwJAAkAgACgCAEUEQEEBIQEgACgCFCIGIAAoAhgiACAKIAIgAxDSAQ0BDAILIAYgACgCBCIHTwRAQQEhASAAKAIUIgYgACgCGCIAIAogAiADENIBDQEMAgsgCEEIcQRAIAAoAhAhCyAAQTA2AhAgAC0AICEMQQEhASAAQQE6ACAgACgCFCIIIAAoAhgiCSAKIAIgAxDSAQ0BIAcgBmtBAWohAQJAA0AgAUEBayIBRQ0BIAhBMCAJKAIQEQAARQ0AC0EBDwtBASEBIAggBCAFIAkoAgwRBAANASAAIAw6ACAgACALNgIQQQAhAQwBCyAHIAZrIQYCQAJAAkAgAC0AICIBQQFrDgMAAQACCyAGIQFBACEGDAELIAZBAXYhASAGQQFqQQF2IQYLIAFBAWohASAAQRhqKAIAIQcgACgCECEIIAAoAhQhAAJAA0AgAUEBayIBRQ0BIAAgCCAHKAIQEQAARQ0AC0EBDwtBASEBIAAgByAKIAIgAxDSAQ0AIAAgBCAFIAcoAgwRBAANAEEAIQEDQCABIAZGBEBBAA8LIAFBAWohASAAIAggBygCEBEAAEUNAAsgAUEBayAGSQ8LIAEPCyAGIAQgBSAAKAIMEQQAC9sFAgZ/An4CQCACRQ0AIAJBB2siA0EAIAIgA08bIQcgAUEDakF8cSABayEIQQAhAwNAAkACQCABIANqLQAAIgXAIgZBAE4EQCAIIANrQQNxRQRAIAMgB08NAgNAIAEgA2oiBCgCAEGAgYKEeHENAyAEQQRqKAIAQYCBgoR4cQ0DIAcgA0EIaiIDSw0ACwwCCyADQQFqIQMMAgtCgICAgIAgIQpCgICAgBAhCQJAAkACfgJAAkACQAJAAkACQAJAAkACQCAFQZDowABqLQAAQQJrDgMAAQIKCyADQQFqIgQgAkkNAkIAIQpCACEJDAkLQgAhCiADQQFqIgQgAkkNAkIAIQkMCAtCACEKIANBAWoiBCACSQ0CQgAhCQwHCyABIARqLAAAQb9/Sg0GDAcLIAEgBGosAAAhBAJAAkAgBUHgAWsiBQRAIAVBDUYEQAwCBQwDCwALIARBYHFBoH9GDQQMAwsgBEGff0oNAgwDCyAGQR9qQf8BcUEMTwRAIAZBfnFBbkcNAiAEQUBIDQMMAgsgBEFASA0CDAELIAEgBGosAAAhBAJAAkACQAJAIAVB8AFrDgUBAAAAAgALIAZBD2pB/wFxQQJLIARBQE5yDQMMAgsgBEHwAGpB/wFxQTBPDQIMAQsgBEGPf0oNAQsgAiADQQJqIgRNBEBCACEJDAULIAEgBGosAABBv39KDQJCACEJIANBA2oiBCACTw0EIAEgBGosAABBv39MDQVCgICAgIDgAAwDC0KAgICAgCAMAgtCACEJIANBAmoiBCACTw0CIAEgBGosAABBv39MDQMLQoCAgICAwAALIQpCgICAgBAhCQsgACAKIAOthCAJhDcCBCAAQQE2AgAPCyAEQQFqIQMMAQsgAiADTQ0AA0AgASADaiwAAEEASA0BIAIgA0EBaiIDRw0ACwwCCyACIANLDQALCyAAIAE2AgQgAEEIaiACNgIAIABBADYCAAuMBQEFfyMAQeAAayIFJAAgBSAEOgAIIAUgAzsBBiAFIAI7AQQCQCABLwEARQ0AIAEvAQIgAkH//wNxRw0AIAFBAToAECABQRFqIAQ6AAALIAUgBEH/AXEiBiACQQV0cjsBCkEAIQICQCAGRQ0AIARBA3EhCAJAIAZBBEkEQAwBCyAEQfwBcSEJQQAhBgNAIANBA3ZBAXEgA0ECdkEBcSADQQJxIANBAnRBBHEgAkEDdHJyckEBdHIhAiADQfD/A3FBBHYhAyAGQQRqIgZB/wFxIAlHDQALCyAIRQ0AQQAhBgNAIANBAXEgAkEBdHIhAiADQf7/A3FBAXYhAyAGQQFqIgZB/wFxIAhHDQALCyABLQASIARrQQ9xIQQgAUEMaigCACEDIAEoAgQhBgJAAkACQAJAA0AgBSAHIAUtAAhBD3F0IAJyQf//A3EiATYCDCABIANPDQEgBiABQQF0aiIBLwEAQRBHDQIgASAFLwEKOwEAIAdBAWoiB0H//wNxIAR2RQ0ACyAAQQQ6AAAMAgsgASADQeDFwAAQtAEACyAFQcwAakHUADYCACAFQcQAakEqNgIAIAVBPGpBKjYCACAFQTRqQSo2AgAgBUEcakIFNwIAIAVBBTYCFCAFQbDGwAA2AhAgBSABNgIwIAVBAjYCLCAFIAVBKGoiAjYCGCAFIAVBBmo2AkggBSAFQQRqNgJAIAUgBUEKajYCOCAFIAVBDGo2AiggBUHQAGogBUEQahBgQb3lwQAtAAAaQQxBBBCcAiIBRQ0BIAEgBSkDUDcCACABQQhqIAVB2ABqKAIANgIAIAJBFSABQejGwAAQ0AEgACAFKQMoNwIACyAFQeAAaiQADwtBBEEMEL0CAAubCAINfwF+IwBBQGoiAiQAIAJBADYCFCACQgQ3AgwgAkEANgIgIAJCBDcCGCACQSRqIAEQdCACKAIsIgYEQANAQQAhBSACKAIkIQxBACEIA0ACfyAGIAhPBEADQCAIIAxqIQQCfyAGIAhrIgpBCE8EQCACQSwgBCAKEHMgAigCBCEDIAIoAgAMAQtBACEDQQAgCkUNABoDQEEBIAMgBGotAABBLEYNARogCiADQQFqIgNHDQALIAohA0EAC0EBRwRAQQAhDSAGIQggBiEDIAUMAwsgAyAIaiIDQQFqIQgCQCADIAZPDQAgAyAMai0AAEEsRw0AQQEhDSAIDAMLIAYgCE8NAAsLQQAhDSAGIQMgBQsgBSAMaiEEQQAhByMAQTBrIg4kACAOQQo2AgwgAkEwaiIJAn8CQCADIAVrIgNFBEAgCUEAOgABDAELAkACQAJAAkACQCAELQAAQStrDgMBAgACCyADQQFGDQMgBEEBaiEEAkAgA0EISwRAIANBAWshAwNAIANFDQUgBC0AAEEwayIFQQpPDQYgB6xCCn4iD0IgiKcgD6ciC0EfdUcNAiAEQQFqIQQgA0EBayEDIAsgCyAFayIHSiAFQQBKc0UNAAsgCUEDOgABDAYLIANBAWshAwNAIAQtAABBMGsiBUEKTw0FIARBAWohBCAHQQpsIAVrIQcgA0EBayIDDQALDAMLIAlBAzoAAQwECyADQQFrIgNFDQIgBEEBaiEECyADQQhPBEACQANAIANFDQMgBC0AAEEwayIFQQpPDQQgB6xCCn4iD0IgiKcgD6ciC0EfdUcNASAEQQFqIQQgA0EBayEDIAVBAEggCyAFIAtqIgdKc0UNAAsgCUECOgABDAQLIAlBAjoAAQwDCwNAIAQtAABBMGsiBUEKTw0CIARBAWohBCAFIAdBCmxqIQcgA0EBayIDDQALCyAJIAc2AgRBAAwCCyAJQQE6AAFBAQwBC0EBCzoAACAOQTBqJAAgAigCNCEFIAItADAhBCACKAIgIgMgAigCHEYEQCACQRhqIAMQhgEgAigCICEDCyACKAIYIANBAnRqQQAgBSAEGzYCACACIAIoAiBBAWo2AiAhBSANDQALIAJBOGoiBiACQSBqKAIANgIAIAIgAikCGDcDMCACKAIUIgMgAigCEEYEQCACQQxqIAMQhQEgAigCFCEDCyACKAIMIANBDGxqIgMgAikDMDcCACADQQhqIAYoAgA2AgAgAiACKAIUQQFqNgIUIAIoAigEQCAMEEQLIAJBADYCICACQgQ3AhggAkEkaiABEHQgAigCLCIGDQALCyACKAIoBEAgAigCJBBECyACKAIcBEAgAigCGBBECyAAIAIpAgw3AgAgAEEIaiACQRRqKAIANgIAIAJBQGskAAvNBAEIfwJAIAECfwJAAkACQCABKAIARQRAIAFBDmotAABFBEAgAUEMai0AACEFIAEoAjAhBiABQTRqKAIAIgQhAwJAAkACQAJAIAEoAgQiAgR/AkAgAiAETwRAIAIgBEYNAQwDCyACIAZqLAAAQUBIDQILIAQgAmsFIAMLRQ0BAn8gAiAGaiIILAAAIgNBAEgEQCAILQABQT9xIQcgA0EfcSEJIAlBBnQgB3IgA0FgSQ0BGiAILQACQT9xIAdBBnRyIQcgByAJQQx0ciADQXBJDQEaIAlBEnRBgIDwAHEgCC0AA0E/cSAHQQZ0cnIMAQsgA0H/AXELIQMgBUH/AXENCCADQYCAxABGDQIgAQJ/QQEgA0GAAUkNABpBAiADQYAQSQ0AGkEDQQQgA0GAgARJGwsgAmoiAjYCBCACRQ0HAkAgAiAETwRAIAIgBEcNAQwICyACIAZqLAAAQb9/Sg0HC0EBIQULIAEgBUEBczoADCAGIAQgAiAEQdyBwAAQlgIACyABIAVBAXM6AAwgBUH/AXENCAwBCyABQQE6AAwLIAFBAToADgsgAEEANgIADwsgAUEIaiECIAFBPGooAgAhBCABQTRqKAIAIQUgASgCOCEDIAEoAjAhBiABQSRqKAIAQX9HBEAgACACIAYgBSADIARBABBIDwsgACACIAYgBSADIARBARBIDwsgBCACayEEC0EAIARFDQEaQQEhBSACIAZqLAAAQQBODQALIAVBAXMLOgAMCyAAIAI2AgQgAEEIaiACNgIAIABBATYCAAuFBQEKfyMAQTBrIgMkACADQSRqIAE2AgAgA0EDOgAsIANBIDYCHCADQQA2AiggAyAANgIgIANBADYCFCADQQA2AgwCfwJAAkAgAigCECIKRQRAIAJBDGooAgAiAEUNASACKAIIIQEgAEEDdCEFIABBAWtB/////wFxQQFqIQcgAigCACEAA0AgAEEEaigCACIEBEAgAygCICAAKAIAIAQgAygCJCgCDBEEAA0ECyABKAIAIANBDGogAUEEaigCABEAAA0DIAFBCGohASAAQQhqIQAgBUEIayIFDQALDAELIAJBFGooAgAiAEUNACAAQQV0IQsgAEEBa0H///8/cUEBaiEHIAIoAgghCCACKAIAIQADQCAAQQRqKAIAIgEEQCADKAIgIAAoAgAgASADKAIkKAIMEQQADQMLIAMgBSAKaiIBQRBqKAIANgIcIAMgAUEcai0AADoALCADIAFBGGooAgA2AiggAUEMaigCACEGQQAhCUEAIQQCQAJAAkAgAUEIaigCAEEBaw4CAAIBCyAGQQN0IAhqIgwoAgRBiwFHDQEgDCgCACgCACEGC0EBIQQLIAMgBjYCECADIAQ2AgwgAUEEaigCACEEAkACQAJAIAEoAgBBAWsOAgACAQsgBEEDdCAIaiIGKAIEQYsBRw0BIAYoAgAoAgAhBAtBASEJCyADIAQ2AhggAyAJNgIUIAggAUEUaigCAEEDdGoiASgCACADQQxqIAEoAgQRAAANAiAAQQhqIQAgCyAFQSBqIgVHDQALCyACKAIEIAdLBEAgAygCICACKAIAIAdBA3RqIgAoAgAgACgCBCADKAIkKAIMEQQADQELQQAMAQtBAQsgA0EwaiQAC4QFAQR/IwBB4ABrIgEkAEG95cEALQAAGiABIAA2AgwCQAJAAkBBNEEEEJwCIgAEQCAAQQA2AhwgAEEANgIUIABBAjYCDCAAQgE3AgQgAEECNgIAQb3lwQAtAAAaQQRBBBCcAiICRQ0BIAIgADYCACACQYy9wAAQtwIhAyABQYy9wAA2AhQgASACNgIQIAEgAzYCGCAAIAAoAgBBAWoiAjYCACACRQ0CQb3lwQAtAAAaQQRBBBCcAiICRQ0DIAIgADYCACACQaC9wAAQtwIhAyABQaC9wAA2AiAgASACNgIcIAEgAzYCJCABQQxqKAIAIAFBEGooAgggAUEcaigCCBAqIgJBhAFPBEAgAhAACyABQcgAaiICIAFBGGooAgA2AgAgAUHUAGogAUEkaigCADYCACABIAEpAhw3AkwgAUEwaiACKQMANwMAIAFBOGogAUHQAGopAwA3AwAgASABKQIQNwMoIAAoAghFBEAgAEEcaiECIABBfzYCCCAAKAIcIgMEfwJAIABBJGooAgAQB0UNACADIAAoAiAiBCgCABEBACAEKAIERQ0AIAQoAggaIAMQRAsCQCAAQTBqKAIAEAdFDQAgAEEoaigCACIEIABBLGooAgAiAygCABEBACADKAIERQ0AIAMoAggaIAQQRAsgACgCCEEBagVBAAshAyACIAEpAyg3AgAgAkEQaiABQThqKQMANwIAIAJBCGogAUEwaikDADcCACAAIAM2AgggASgCDCICQYQBTwRAIAIQAAsgAUHgAGokACAADwtB6L3AAEEQIAFB3wBqQfi9wABBoMDAABCpAQALQQRBNBC9AgALQQRBBBC9AgALAAtBBEEEEL0CAAuKBQEFfyMAQdAAayIDJAACQAJAIAItAABFBEAgAi0AASEFIAEoAggiAiABKAIERgR/IAEgAhCNASABKAIIBSACCyABKAIAaiAFOgAAIAEgASgCCEEBajYCCAwBCyACLwECIQUgAyACLwEEIgI7AQ4CQAJAAkACQAJAAkAgAiABKAIIIgRNBEAgAkUNASAFIAEoAgQgBGtLBEAgASAEIAUQigELIAQgAmshBiACIAVNBEADQCACIAZqIgcgAkkNBSAHIAEoAggiBEsNBiACIAEoAgQgBGtLBEAgASAEIAIQigEgASgCCCEECyABKAIAIgcgBGogBiAHaiACEMACGiABIAIgBGo2AgggBSACayIFIAJBAXQiAk8NAAsLIAUgBmoiBCAFSQ0CIAQgASgCCCICSw0GIAUgASgCBCACa0sEQCABIAIgBRCKASABKAIIIQILIAEoAgAiBCACaiAEIAZqIAUQwAIaIAEgAiAFajYCCAwHCyADQRxqQgI3AgAgA0E4akEqNgIAIANBAjYCFCADQbytwAA2AhAgA0ECNgIwIAMgBDYCPCADIANBLGo2AhggAyADQQ5qNgI0IAMgA0E8ajYCLCADQUBrIANBEGoiAhBgQb3lwQAtAAAaQQxBBBCcAiIBRQ0EIAEgAykDQDcCACABQQhqIANByABqKAIANgIAIAJBFSABQdytwAAQ0AEgACADKQMQNwIADAcLQcTJwABBJEHMysAAEM0BAAtBkK/AAEEbQayvwAAQzQEAC0GQr8AAQRtBrK/AABDNAQALQeyuwABBFEGAr8AAEM0BAAtBBEEMEL0CAAtB7K7AAEEUQYCvwAAQzQEACyAAQQQ6AAALIANB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QAJAIAFBEGohAiABQW9LDQAgAiADSw0CIAkgCCABIAVqIgEtAABqIghqIAggAS0AAWoiCWogCSABQQJqLQAAaiIJaiAJIAFBA2otAABqIglqIAkgAUEEai0AAGoiCWogCSABQQVqLQAAaiIJaiAJIAFBBmotAABqIglqIAkgAUEHai0AAGoiCWogCSABQQhqLQAAaiIJaiAJIAFBCWotAABqIglqIAkgAUEKai0AAGoiCWogCSABQQtqLQAAaiIJaiAJIAFBDGotAABqIglqIAkgAUENai0AAGoiCWogCSABQQ5qLQAAaiIJaiAJIAFBD2otAABqIghqIQkgAiEBIAMgBEEQayIEakEPSw0BDAULCyABIAJBoMjAABC2AQALIAIgA0GgyMAAELUBAAsgBygCACEJIAMEQCAHKAIEIQgCQCADQQNxIhhFBEAgBSEBIAMhBAwBCyADIQQDQCAEQQFrIQQgCSACLQAAaiIJIAhqIQggAkEBaiIBIQIgGEEBayIYDQALCwJAIANBBEkNACADIAVqIQMgBEEEayECA0AgCSABLQAAaiIEIAEtAAFqIgUgAS0AAmoiGCABQQNqLQAAaiIJIBggBSAEIAhqampqIQggAkUNASACQQRrIQIgAUEEaiIBIANHDQALCyAHIAg2AgQgByAJNgIACyAJQfD/A0sEQCAHIAlB8f8DazYCAAsgBygCBCEJIAdBBGoMAgsgByAHKAIAIAUtAABqQfH/A3AiATYCACAHKAIEIAFqIQkgB0EEagwBCwJAIAIgA0YNACACQX9zIANqIAMgAmtBA3EiBARAIAIhAQNAIAggASAFai0AAGoiCCAJaiEJIAFBAWoiAiEBIARBAWsiBA0ACwtBA0kNACACIAVqIQEgAyACayECA0AgCCABLQAAaiIDIAFBAWotAABqIgQgAUECai0AAGoiBSABQQNqLQAAaiIIIAUgBCADIAlqampqIQkgAUEEaiEBIAJBBGsiAg0ACwsgByAIQfH/A3A2AgAgB0EEagsgCUHx/wNwNgIACyAAQQQ6AAAgACAONgIEDAULIAFBAToANiABQRRqKAIAIgJBBEkNAyABIAJBBGs2AhQgAUEQaiICIAIoAgAiAkEEajYCACATIAIoAAAiAkEYdCACQYD+A3FBCHRyIAJBCHZBgP4DcSACQRh2cnIiAjYCDCABEJQCIAJGBEAgAEEEOgAAIABBADYCBAwFCyABEJQCIQEgE0E4akECNgIAIBNBHGpCAjcCACATQQI2AjAgEyABNgI8IBNBAjYCFCATQYiawAA2AhAgEyATQQxqNgI0IBMgE0E8ajYCLCATIBNBLGo2AhggE0FAayECIBNBEGoiBSIBQQxqKAIAIQMCQAJAAkACQAJAAkACQAJAIAEoAgQOAgABAgsgAw0BQQEhA0EAIQFB/JjAACEEDAMLIANFDQELIAIgARBgDAQLIAEoAgAiASgCACEEIAEoAgQiAUUEQEEBIQNBACEBDAELIAFBAEgNAUG95cEALQAAGiABQQEQnAIiA0UNAgsgAyAEIAEQwAIhAyACIAE2AgggAiABNgIEIAIgAzYCAAwCCxDUAQALQQEgARC9AgALEOsBIgFBCGogE0HIAGooAgA2AgAgASATKQNANwIAIAVBFSABQaiawAAQ0AEgACATKQMQNwIADAQLIABBBDoAACAAQQA2AgQMAwsgACATLwAROwABIABBA2ogEy0AEzoAACAAIBMoAhQ2AgQgACAEOgAADAILIA4gA0G0m8AAELUBAAsgAEHcmMAANgIEIABBAjoAAAsgE0HQAGokAAuUAwEHfwJAIAAoAgwiAUUNACAAKAIAIQUgACgCBCICIAAoAggiACACQQAgACACTxtrIgAgAWogASACIABrIgRLGyICIABHBEAgAiAAayEGIAUgAEECdGohAgNAIAIoAgAiACAAKAIAQQFrIgM2AgACQCADDQAgAEEMaigCACIDBEAgAyAAQRBqKAIAIgcoAgARAQAgBygCBARAIAcoAggaIAMQRAsgAEEYaigCACAAQRRqKAIAKAIMEQEACyAAQQRqIgMgAygCAEEBayIDNgIAIAMNACAAEEQLIAJBBGohAiAGQQFrIgYNAAsLIAEgBE0NACABIARrIgBBACAAIAFNGyECA0AgBSgCACIAIAAoAgBBAWsiATYCAAJAIAENACAAQQxqKAIAIgEEQCABIABBEGooAgAiBCgCABEBACAEKAIEBEAgBCgCCBogARBECyAAQRhqKAIAIABBFGooAgAoAgwRAQALIABBBGoiASABKAIAQQFrIgE2AgAgAQ0AIAAQRAsgBUEEaiEFIAJBAWsiAg0ACwsLjAMBB38jAEEgayIEJAACQAJAAkACQAJA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AgAQRAsgAUEgaigCACICBEAgASgCGCEAA0AgAEEEaigCAARAIAAoAgAQRAsgAEEUaiEAIAJBAWsiAg0ACwsgAUEYaiIAKAIEBEAgACgCABBECyABQTBqKAIAIgIEQCABKAIoIQADQCAAQQRqKAIABEAgACgCABBECyAAQRRqIQAgAkEBayICDQALCyABQShqIgAoAgQEQCAAKAIAEEQLIANBAWoiAyAERw0ACwsLuwIBBX8gACgCGCEDAkACQCAAIAAoAgxGBEAgAEEUQRAgAEEUaiIBKAIAIgQbaigCACICDQFBACEBDAILIAAoAggiAiAAKAIMIgE2AgwgASACNgIIDAELIAEgAEEQaiAEGyEEA0AgBCEFIAIiAUEUaiICIAFBEGogAigCACICGyEEIAFBFEEQIAIbaigCACICDQALIAVBADYCAAsCQCADRQ0AAkAgACAAKAIcQQJ0QejlwQBqIgIoAgBHBEAgA0EQQRQgAygCECAARhtqIAE2AgAgAQ0BDAILIAIgATYCACABDQBBhOnBAEGE6cEAKAIAQX4gACgCHHdxNgIADwsgASADNgIYIAAoAhAiAgRAIAEgAjYCECACIAE2AhgLIABBFGooAgAiAEUNACABQRRqIAA2AgAgACABNgIYCwu4AgEGfyMAQRBrIgYkACAAKAIARQRAIABBfzYCACAAQRRqIgMoAgAhBCADQQA2AgACQCAERQ0AIABBKGooAgAgAEEkaigCACEDIABBIGooAgAhByAAQRhqKAIAIQUCQCAAQRxqKAIAEAdFDQAgBCAFKAIAEQEAIAUoAgRFDQAgBSgCCBogBBBECxAHRQ0AIAcgAygCABEBACADKAIERQ0AIAMoAggaIAcQRAsgAEEIaiEEAkAgAEEEaigCAEECRg0AIAQoAgAiA0GEAUkNACADEAALIAAgATYCBCAEIAI2AgAgAEEMaiICKAIAIQEgAkEANgIAIAAgACgCAEEBajYCACABBEAgAEEQaigCACABKAIEEQEACyAGQRBqJAAPC0HovcAAQRAgBkEPakH4vcAAQbDAwAAQqQEAC6MCAQR/IABCADcCECAAAn9BACABQYACSQ0AGkEfIAFB////B0sNABogAUEGIAFBCHZnIgJrdkEBcSACQQF0a0E+agsiAzYCHCADQQJ0QejlwQBqIQICQAJAAkACQEGE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AgQiBEEBdCIDIAEgASADSRsiASABQQhNGyIDQX9zQR92IQECQCAEBEAgAiAENgIcIAJBATYCGCACIAAoAgA2AhQMAQsgAkEANgIYCyACQQhqIAEgAyACQRRqEI8BIAIoAgwhASACKAIIRQRAIAAgAzYCBCAAIAE2AgAMAgsgAUGBgICAeEYNASABRQ0AIAEgAkEQaigCABC9AgALENQBAAsgAkEgaiQAC9UBAQV/IwBBEGsiAyQAIAEoAgAiASgCCEUEQCABQQxqKAIAIQUgAUL/////LzcCCCABQRBqKAIAIQYgASAFQQJGBH8gAyACKAIAIgIoAgQgAigCACgCABECACADKAIEIQIgAygCACEEIAFBFGooAgAiBwRAIAFBGGooAgAgBygCDBEBAAsgASAENgIUIAFBGGogAjYCACABKAIIQQFqBSAECzYCCCAAIAY2AgQgACAFNgIAIANBEGokAA8LQei9wABBECADQQ9qQfi9wABBwMDAABCpAQALrgEBAX8CQAJAIAEEQCACQQBIDQECfyADKAIEBEACQCADQQhqKAIAIgRFBEAMAQsgAygCACAEIAEgAhCPAgwCCwsgASACRQ0AGkG95cEALQAAGiACIAEQnAILIgMEQCAAIAM2AgQgAEEIaiACNgIAIABBADYCAA8LIAAgATYCBCAAQQhqIAI2AgAMAgsgAEEANgIEIABBCGogAjYCAAwBCyAAQQA2AgQLIABBATYCAAvdAQEDfyMAQcABayIDJAAgACgCACIALQBYIQQgAEEEOgBYAkAgBEEERwRAIANBBmoiBSAAQdsAai0AADoAACADIAAvAFk7AQQgA0HkAGogAEHYABDAAhpBveXBAC0AABpBxAFBBBCcAiIARQ0BIAAgAjYCBCAAIAE2AgAgAEEIaiADQQhqQbQBEMACGiAAIAQ6ALwBIABBADoAwAEgACADLwEEOwC9ASAAQb8BaiAFLQAAOgAAIABBsJDAABCwASADQcABaiQADwtBwJDAAEExELgCAAtBBEHEARC9AgAL4QEBBH8jAEGQAmsiAyQAIAAoAgAiAC0A/AEhBCAAQQQ6APwBAkAgBEEERwRAIANBEGoiBSAAQfwBEMACGiADQQ5qIgYgAEH/AWotAAA6AABBveXBAC0AABogAyAALwD9ATsBDEGMBEEEEJwCIgBFDQEgACAC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//8DcbggBEH//wNxuCAWIBYgGJogFqEgFyAWIBYQvAEgASgCqAENBiABQaABaiAJEMYBIAEoAqABRQ0BIAEgASgCpAE2AqADQbSCwABBKyABQaADakGchsAAQfyHwAAQqQEACyABQegAaiABQegCaiABQeQCaiADQf//A3G4IARB//8DcbggFiAWIBcgGCAWIBYQvAEgASgCaA0KCyAQIAAgE2ogAEH//wNxIBRGGyEAIAUgCGoiA0EAIANB//8DcSALSSIDGyEIIAJBAWohAkEAIAUgAxsgB2ohByAGQQFrIgYNAAsgASgCjANFDQwgASgCiAMQRAwMC0HAhMAAQRlBvIjAABDNAQALIAEgASgCfDYCoANBtILAAEErIAFBoANqQZyGwABBrIfAABCpAQALIAEgASgClAE2AqADQbSCwABBKyABQaADakGchsAAQdyHwAAQqQEACyABIAEoAqwBNgKgA0G0gsAAQSsgAUGgA2pBnIbAAEGMiMAAEKkBAAtB4IbAAEE5QcyIwAAQzQEACyABIAEoAoQBNgKgA0G0gsAAQSsgAUGgA2pBnIbAAEG8h8AAEKkBAAsgASABKAKcATYCoANBtILAAEErIAFBoANqQZyGwABB7IfAABCpAQALIAEgASgCtAE2AqADQbSCwABBKyABQaADakGchsAAQZyIwAAQqQEACyABIAEoAmw2AqADQbSCwABBKyABQaADakGchsAAQayIwAAQqQEACyADDQELQeCGwABBOUHciMAAEM0BAAsCQCABQYgDaiIAKAIIIgIgDiADcCIDSwRAIAAoAgAgA0ECdGoiBSgCABogBSAFQQRqIAIgA0F/c2pBAnQQwQIgACACQQFrNgIIDAELIwBBMGsiACQAIAAgAjYCBCAAIAM2AgAgAEEsakECNgIAIABBAjYCJCAAIABBBGo2AiggACAANgIgIwBBIGsiAyQAIABBCGoiAkEANgIQIAJBAzYCBCACQZThwAA2AgAgAiAAQSBqNgIIIAJBDGpBAjYCACADQSBqJAAgAkHsiMAAENUBAAtB4IbAAEE5QfyIwAAQzQEACyABKAL0AiIABEAgASgC7AIhAwNAIANBBGooAgAEQCADKAIAEEQLIANBDGohAyAAQQFrIgANAAsLIAEoAvACBEAgASgC7AIQRAsgAUH8AmooAgBFDQEgASgC+AIQRAwBCwJAICAgHKIiGCAWY0UNACABQThqIAFB6AJqIAFB5AJqRAAAAAAAAAAAIBggFyAWIBihIhYgGiAZIBigIBcgFhC8ASABKAI4RQ0AIAFBMGogASgCPBAGQQAhAwJ/QQEgASgCMCICRQ0AGiABKAI0IQAgASACNgLsAiABIAA2AvQCIAEgADYC8AIgAUEoaiABQewCahCoAUEBIAEoAigiAEUNABogASgCLCEDIAALIQAgAUH4AmpCATcCACABIAM2AqgDIAEgAzYCpAMgASAANgKgAyABQQM2ApwDIAFBATYC8AIgAUHwicAANgLsAiABIAFBoANqNgKYAyABIAFBmANqNgL0AiABQewCakGIisAAENUBAAsgASgCjANFDQAgAxBECyABQdiJwABBCxABNgLsAiABQSBqIBEgAUHsAmoQwgEgASgCJCECAkAgASgCIARAIAJBhAFPBEAgAhAAC0GAARAFIQAMAQsgAhAFIQAgAkGEAUkNACACEAALIAEoAuwCIgJBhAFPBEAgAhAACwJAIABBAUYNACABQdiJwABBCxABNgLsAiABQRhqIBEgAUHsAmoQwgEgASgCHCEAAkAgASgCGEUEQCAAIQIMAQtBgQEhAiAAQYQBSQ0AIAAQAAsgASACNgKYAyABKALsAiIAQYQBTwRAIAAQAAsjAEEQayIAJAAgAUHoAmooAgAgAUGYA2ooAgAgGiAZEBMgAEEIahDpASAAKAIMIQIgAUEQaiIDIAAoAgg2AgAgAyACNgIEIABBEGokACABKAIQRQRAIAEoApgDIgBBhAFJDQEgABAADAELIAFBCGogASgCFBAGQQAhAwJ/QQEgASgCCCICRQ0AGiABKAIMIQAgASACNgLsAiABIAA2AvQCIAEgADYC8AIgASABQewCahCoAUEBIAEoAgAiAEUNABogASgCBCEDIAALIQAgAUH4AmpCATcCACABIAM2ApADIAEgAzYCjAMgASAANgKIAyABQQM2AqQDIAFBATYC8AIgAUHwicAANgLsAiABIAFBiANqNgKgAyABIAFBoANqNgL0AiABQewCakGYisAAENUBAAsgASgC6AIiAEGEAU8EQCAAEAALIAEoAuQCIgBBhAFPBEAgABAACyABKALgAiIAQYQBTwRAIAAQAAsgASgC0AJFDQAgASgCzAIQRAsgAUGwA2okACASKAIMIgBBhAFPBEAgABAACyASQRBqJAALQAEBfyMAQSBrIgAkACAAQRRqQgA3AgAgAEEBNgIMIABBrN/AADYCCCAAQezewAA2AhAgAEEIakG038AAENUBAAvDAgECfyMAQSBrIgIkACACIAA2AhggAkGk48AANgIQIAJBrOHAADYCDCACQQE6ABwgAiABNgIUIwBBEGsiASQAAkAgAkEMaiIAKAIIIgIEQCAAKAIMIgNFDQEgASACNgIMIAEgADYCCCABIAM2AgQjAEEQayIAJAAgAUEEaiIBKAIAIgJBDGooAgAhAwJAAn8CQAJAIAIoAgQOAgABAwsgAw0CQQAhAkH80sAADAELIAMNASACKAIAIgMoAgQhAiADKAIACyEDIAAgAjYCBCAAIAM2AgAgAEGk1sAAIAEoAgQiACgCDCABKAIIIAAtABAQiwEACyAAQQA2AgQgACACNgIAIABBuNbAACABKAIEIgAoAgwgASgCCCAALQAQEIsBAAtB2NPAAEErQeTVwAAQzQEAC0HY08AAQStB9NXAABDNAQALLwEBfyAAIAEoAgAiAgR/IAEgAkEBazYCACABLQAEBSABCzoAASAAIAJBAEc6AAALLAECfxA6IgIQLyIDIAAgARAwIAJBhAFPBEAgAhAACyADQYQBTwRAIAMQAAsLLgACQCADaUEBR0GAgICAeCADayABSXJFBEAgACABIAMgAhCPAiIADQELAAsgAAu5AgEDfyAAKAIAIQAgARCmAkUEQCABEKcCRQRAIAAgARCzAg8LIwBBgAFrIgMkACAALwEAIQADQCACIANqQf8AakEwQTcgAEEPcSIEQQpJGyAEajoAACACQQFrIQIgACIEQQR2IQAgBEEQTw0ACyACQYABaiIAQYABSwRAIABBgAFB2OTAABCzAQALIAFBAUG55MAAQQIgAiADakGAAWpBACACaxBPIANBgAFqJAAPCyMAQYABayIDJAAgAC8BACEAA0AgAiADakH/AGpBMEHXACAAQQ9xIgRBCkkbIARqOgAAIAJBAWshAiAAIgRBBHYhACAEQRBPDQALIAJBgAFqIgBBgAFLBEAgAEGAAUHY5MAAELMBAAsgAUEBQbnkwABBAiACIANqQYABakEAIAJrEE8gA0GAAWokAAssAQF/IwBBEGsiACQAIABBCGoiAiABQYPUwABBCxDjASACEKcBIABBEGokAAssAQF/IwBBEGsiAiQAIAIgACgCADYCDCACQQxqQdDSwAAgARBUIAJBEGokAAssAQF/IwBBEGsiAiQAIAIgACgCADYCDCACQQxqQfTdwAAgARBUIAJBEGokAAssAQF/IwBBEGsiAiQAIAIgACgCADYCDCACQQxqQbDmwAAgARBUIAJBEGokAAspACMAQRBrIgIkACACIAApAgA3AgggAkEIaiABIAIgAxBtIAJBEGokAAspACMAQRBrIgIkACACIAAoAgA2AgwgAkEMaiABIAIgAxBGIAJBEGokAAspACMAQRBrIgIkACACIAAoAgA2AgwgAkEMaiABIAIgAxBDIAJBEGokAAswAQF/IAFBCGsiAiACKAIAQQFqIgI2AgAgAkUEQAALIAAgATYCBCAAQaS8wAA2AgALKQEBfyMAQRBrIgIkACACIAA2AgwgAkEMakGw5sAAIAEQVCACQRBqJAALMAAgASgCFCACIAMgAUEYaigCACgCDBEEACECIABBADoABSAAIAI6AAQgACABNgIAC1EBAX8jAEEQayIDJAAgAyACNgIMIAMgATYCCCADIAA2AgQjAEEQayIAJAAgACADQQRqIgEpAgA3AgggAEEIakGoq8AAQQAgASgCCEEBEIsBAAuvAQEDfyABEKYCRQRAIAEQpwJFBEAgACABELICDwsjAEGAAWsiAyQAIAAtAAAhAANAIAIgA2pB/wBqQTBBNyAAQQ9xIgRBCkkbIARqOgAAIAJBAWshAiAAIgRBBHYhACAEQRBPDQALIAJBgAFqIgBBgAFLBEAgAEGAAUHY5MAAELMBAAsgAUEBQbnkwABBAiACIANqQYABakEAIAJrEE8gA0GAAWokAA8LIAAgARCZAQvEAQEDfyABEKYCRQRAIAEQpwJFBEAgACgCACIArUIAIACsfSAAQQBOIgAbIAAgARBqDwsgACABEJoBDwsjAEGAAWsiAyQAIAAoAgAhAANAIAIgA2pB/wBqQTBB1wAgAEEPcSIEQQpJGyAEajoAACACQQFrIQIgAEEQSSAAQQR2IQBFDQALIAJBgAFqIgBBgAFLBEAgAEGAAUHY5MAAELMBAAsgAUEBQbnkwABBAiACIANqQYABakEAIAJrEE8gA0GAAWokAAsnACAAIAAoAgRBAXEgAXJBAnI2AgQgACABaiIAIAAoAgRBAXI2AgQLJgACQCAARQ0AIAAgASgCABEBACABKAIERQ0AIAEoAggaIAAQRAsLMwECf0HI5cEAKAIAIQFBzOXBACgCACECQcjlwQBCADcDACAAIAI2AgQgACABQQFGNgIACyABAX8CQCAAKAIEIgFFDQAgAEEIaigCAEUNACABEEQLCyQBAX9BveXBAC0AABpBDEEEEJwCIgAEQCAADwtBBEEMEL0CAAsgACAAIAAoAgAiACAAIAEgACABSRsiAGs2AgAgASAAawsjACACIAIoAgRBfnE2AgQgACABQQFyNgIEIAAgAWogATYCAAslACAARQRAQfjKwABBMhC4AgALIAAgAiADIAQgBSABKAIQEQkACyMAIABFBEBB+MrAAEEyELgCAAsgACACIAMgBCABKAIQEQYACyMAIABFBEBB+MrAAEEyELgCAAsgACACIAMgBCABKAIQERwACyMAIABFBEBB+MrAAEEyELgCAAsgACACIAMgBCABKAIQER4ACyMAIABFBEBB+MrAAEEyELgCAAsgACACIAMgBCABKAIQEQwACyMAIABFBEBB+MrAAEEyELgCAAsgACACIAMgBCABKAIQESAACzMAIAEoAhQgAC0AAEECdCIAQdDcwABqKAIAIABBrNvAAGooAgAgAUEYaigCACgCDBEEAAseACAAIAFBA3I2AgQgACABaiIAIAAoAgRBAXI2AgQLHwAgAEEBNgIEIABBCGogAS0AACIBNgIAIAAgATYCAAsfACAAQQE2AgQgAEEIaiABKAIAIgE2AgAgACABNgIACyEAIABFBEBB+MrAAEEyELgCAAsgACACIAMgASgCEBEFAAsdACABKAIARQRAAAsgAEG8q8AANgIEIAAgATYCAAsfACAARQRAQYy5wABBMhC4AgALIAAgAiABKAIQEQIACx8AIABFBEBBxLzAAEEyELgCAAsgACACIAEoAhARAgALHwAgAEUEQEH4ysAAQTIQuAIACyAAIAIgASgCEBEAAAsdAQF/QezkwQAhAUHo5MEAKAIABH8gAQUgABBiCwsRACAAKAIEBEAgACgCABBECwsaACAAQgA3AgQgAEEENgIAIABBDGpCADcCAAscACAAKAIAIgAoAgAgASAAQQRqKAIAKAIMEQAACxkBAX8gACgCECIBBH8gAQUgAEEUaigC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QSBqIAAQBiADKAIgIgRFDQMgAygCJCICRQ0DIAJBAEgNBkG95cEALQAAGiACQQEQnAIiAEUNAiAAIAQgAhDAAhogBBBEIAIhAQwECyAAIAhBvI7AABC0AQALIAMgABADNgJsDAMLQQEgAhC9AgALQQEhAEEBIQYLIANBkAFqIAAgARBdIANBoAFqIAMoApABIgQgAygCmAEiARBQAn8gAygCoAFFBEAgAygClAEMAQsgAygClAEiAiADQagBajEAAEIghkKAgICAIFENABpBACEBIAJFBEBBASEEQQAMAQsgBBBEQQEhBEEACyADQRhqIAQgARDLASADKAIcIQECQCADKAIYRQRAIAMgATYCbAwBCyADQYEBNgJsIAFBhAFJDQAgARAACyAGRQRAIAAQRAtFDQAgBBBECyADQcyOwABBARABNgKQASMAQRBrIgAkACADQewAaigCACADQZABaigCABA1IQIgAEEIahDpASADQaABaiIBAn8gACgCCEUEQCABIAJBAEc6AAFBAAwBCyABIAAoAgw2AgRBAQs6AAAgAEEQaiQAAkACQAJAAkAgAy0AoAFFBEAgAy0AoQEgAygCkAEiAUGEAU8EQCABEAALRQ0BIANBzI7AAEEBEAE2AqABIANBEGogA0HsAGogA0GgAWoQwgEgAygCFCEBIAMoAhANAiABIQAMAwsgAygCpAEiAEGEAU8EQCAAEAALIAMoApABIgBBhAFJDQAgABAACyADQQA2AnggA0IBNwNwDAILQYEBIQAgAUGEAUkNACABEAALIANBCGogABAGIAMgAygCDEEAIAMoAggiARsiAjYCeCADIAI2AnQgAyABQQEgARs2AnAgAEGEAU8EQCAAEAALIAMoAqABIgBBhAFJDQAgABAACyADQQA2AogBIANCBDcCgAEgA0HNjsAAQQEQATYCoAEgAyADQewAaiADQaABahDCASADKAIEIQACQCADKAIARQRAIAMgADYCkAEMAQsgA0GBATYCkAEgAEGEAUkNACAAEAALIAMgA0GQAWoQxAI2AowBIAMoApABIgBBhAFPBEAgABAACyADKAKgASIAQYQBTwRAIAAQAAsgAyADQfAAajYCpAEgAyADQYABajYCoAEgA0GMAWogA0GgAWpB0I7AABCpAgJ/IAlBBEYEQAJAIAMoAogBIgRFBEAgA0EANgKYASADIAQ2ApQBIANBBDYCkAEMAQsgBEGq1arVAEsNAyAEQQxsIgBBAEgNAwJAIABFBEAgA0EANgKYASADIAQ2ApQBIANBBDYCkAEMAQtBveXBAC0AABogAEEEEJwCIgFFDQUgA0EANgKYASADIAQ2ApQBIAMgATYCkAEgAygCiAEiBEUNAQtBACEAA0AgAygClAEgAEYEQCADQZABaiAAEIUBIAMoApgBIQALIAMoApABIABBDGxqIgBBADYCCCAAQgE3AgAgAyADKAKYAUEBaiIANgKYASAEQQFrIgQNAAsLIAMgA0GMAWoiACgCABAbQQF2NgKcASADIANBgAFqNgKsASADIANB6ABqNgKoASADIANBkAFqNgKkASADIANBnAFqNgKgASAAIANBoAFqQeSOwAAQqQIgAygCkAEhASADKAKUASEGIAMoApgBDAELIAMoAoQBIQYgAygCgAEhASADKAKIAQshBCADEBwiADYCkAEgBAR/IAEgBEEMbGohAiABIQADQCADIAAoAgAgAEEIaigCABABNgKgASADQZABaiADQaABahCqAiADKAKgASIKQYQBTwRAIAoQAAsgAEEMaiIAIAJHDQALIAMoApABBSAACxADIQIgAygCkAEiAEGEAU8EQCAAEAALIAQEQCABIQADQCAAQQRqKAIABEAgACgCABBECyAAQQxqIQAgBEEBayIEDQALCyAGBEAgARBECyADKAKMASIAQYQBTwRAIAAQAAsgCUEERw0CIAMoAogBIgQEQCADKAKAASEAA0AgAEEEaigCAARAIAAoAgAQRAsgAEEMaiEAIARBAWsiBA0ACwsgAygChAFFDQIgAygCgAEQRAwCCxDUAQALQQQgABC9AgALIAMoAnQEQCADKAJwEEQLIAMoAmwiAEGEAU8EQCAAEAALIAMoAiwEQCADKAIoEEQLIANBOGooAgAEQCADKAI0EEQLIAMoAkAhASADQcgAaigCACIEBEAgASEAA0AgAEEEaigCAARAIAAoAgAQRAsgAEEUaiEAIARBAWsiBA0ACwsgA0HEAGooAgAEQCABEEQLIAchAANAIABBBGooAgAEQCAAKAIAEEQLIABBFGohACAIQQFrIggNAAsgA0HUAGooAgAEQCAHEEQLIANBsAFqJAAgAiEBIAUoAgwhAAwBC0EBQQAgARA+IQEL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QCABECA2AlQgAUGYhcAAQQQQATYClAECQAJAAkACQAJAAkACQAJAAkACQAJAAkACQCABKAIYIgMgAEsEQCAAQQFqIANPDS4gASABKAIQIABqLwAAIgNBCHQgA0EIdnJB//8DcbgQAjYCOCABQfgAaiABQdQAaiABQZQBaiABQThqELIBIAEtAHgEQCABIABBAmo2AhwMLQsgASgCOCIDQYQBTwRAIAMQAAsgASgClAEiA0GEAU8EQCADEAALIAFBnIXAAEEFEAE2ApQBIAEoAhgiAyAAQQJqTQ0BIABBA2ogA08NAiABIAEoAhAgAGpBAmovAAAiA0EIdCADQQh2ckH//wNxuBACNgI4IAFB+ABqIAFB1ABqIAFBlAFqIAFBOGoQsgEgAS0AeA0DIAEoAjgiA0GEAU8EQCADEAALIAEoApQBIgNBhAFPBEAgAxAACyABQaGFwABBAxABNgKUASABKAIYIgMgAEEEak0NBCAAQQVqIANPDQUgASABKAIQIABqQQRqLwAAIgNBCHQgA0EIdnJB//8DcbgQAjYCOCABQfgAaiABQdQAaiABQZQBaiABQThqELIBIAEtAHgNBiABKAI4IgNBhAFPBEAgAxAACyABKAKUASIDQYQBTwRAIAMQAAsgAUGkhcAAQQYQATYClAEgASgCGCIDIABBBmpNDQcgAEEHaiADTw0IIAEgASgCECAAakEGai8AACIDQQh0IANBCHZyQf//A3G4EAI2AjggAUH4AGogAUHUAGogAUGUAWogAUE4ahCyASABLQB4DQkgASgCOCIDQYQBTwRAIAMQAAsgASgClAEiA0GEAU8EQCADEAALIAEoAhgiAyAAQQhqTQ0KIABBCWogA08NCyABKAIQIABqQQhqLwAAIQMgAUH4hMAAQQQQATYClAEgASADQQh0IANBCHZyQf//A3EiBLgQAjYCOCABQfgAaiABQdQAaiABQZQBaiABQThqELIBIAEtAHgNDCABKAI4IgNBhAFPBEAgAxAACyABKAKUASIDQYQBTwRAIAMQAAtBASEDIAFBNGogAUHUAGoQqgIgAkEBcQ0NIARBuBdGIARBiJ4DRnIhAwwNCwwsCyABIABBAmoiADYCHAwtCyABIABBAmo2AhwMLQsgASAAQQRqNgIcDCgLIAEgAEEEaiIANgIcDCoLIAEgAEEEajYCHAwrCyABIABBBmo2AhwMJQsgASAAQQZqIgA2AhwMJwsgASAAQQZqNgIcDCkLIAEgAEEIajYCHAwiCyABIABBCGoiADYCHAwkCyABIABBCGo2AhwgAEEJaiADQYCDwAAQtAEACyABIABBCmo2AhwMHwsgASgCVCICQYQBTwRAIAIQAAsgAEEKaiEAIAMhAiAFQQFrIgVB//8DcQ0ACwwVCwwfCyABIAA2AhwMIQsgASAANgIcIABBBmogA0GAg8AAELQBAAsgASAANgIcDB4LIAEgADYCHCAAQQRqIANBgIPAABC0AQALIAEgADYCHAwbCyABIAA2AhwgAEECaiADQYCDwAAQtAEACwwWCyAEIABBgIPAABC0AQALDBsLDB4LDBELDBALDBYLDBELDA0LIAQgAEGAg8AAELQBAAsMEwsMCgsMEQsMFAsgASAANgIcCyABQYABaiICIAFB4ABqKAIANgIAIAEgASkCWDcDeCABKAIsIgAgASgCKEYEQCABQSRqIAAQhwEgASgCLCEACyABKAIkIABBFGxqIgAgASkDeDcCACAAIAM6ABEgACAUOgAQIAAgDDsBDiAAIA87AQwgAEEIaiACKAIANgIAIAEgASgCLEEBajYCLCABQZOFwABBBRABNgI4IAFB+ABqIAFBMGogAUE4aiABQTRqELIBIAEtAHgNBiABKAI4IgBBhAFPBEAgABAACyABQSBqIAFBMGoQqgIgASgCNCIAQYQBTwRAIAAQAAsgDCAKQf//A3EiAEshAiABKAIwIgNBhAFPBEAgAxAACyAMIAAgAhshCiAQIAdBAWoiB0H//wNxSw0ACwwECwwEC0ECQQJBgIPAABC0AQALQQFBAUGAg8AAELQBAAtBAEEAQYCDwAAQtAEACyABQYWEwABBBRABNgJYIAFB+ABqIAFBDGogAUHYAGogAUEgahCyASABLQB4DQAgASgCWCIAQYQBTwRAIAAQAAsCQAJAIAEoAhwiACABKAIYIgNJBEAgAEEBaiICIANPDQogASgCECIFIABqLQAAIQYgASAAQQJqIgQ2AhwgAiAFai0AACABEBw2AjQgBkEIdHIiAgRAA0AgARAgNgKUASABQfSEwABBBBABNgI4IAFB+ABqIAFBEGoQdCABKAJ4IgAgASgCgAEQASEDIAEoAnwEQCAAEEQLIAEgAzYCWCABQfgAaiABQZQBaiABQThqIAFB2ABqELIBIAEtAHgNBSABKAJYIgBBhAFPBEAgABAACyABKAI4IgBBhAFPBEAgABAACyABQfiEwABBBBABNgI4IAEoAhwiACABKAIYIgNPDQggAEEBaiIGIANPDQMgASgCECIFIABqLQAAIQcgASAAQQJqIgQ2AhwgASAFIAZqLQAAIAdBCHRyuBACNgJYIAFB+ABqIAFBlAFqIAFBOGogAUHYAGoQsgEgAS0AeA0FIAEoAlgiAEGEAU8EQCAAEAALIAEoAjgiAEGEAU8EQCAAEAALIAFBNGogAUGUAWoQqgIgASgClAEiAEGEAU8EQCAAEAALIAJBAWsiAkH//wNxDQALCyABQYqEwABBCBABNgJYIAFB+ABqIAFBDGogAUHYAGogAUE0ahCyASABLQB4RQ0CDAMLDAULIAYgA0GAg8AAELQBAAsgASgCWCIAQYQBTwRAIAAQAAsCQAJAAkACQAJAAkACQAJAAkACQAJAAkACQAJAAkACQAJAIAlBwABxBEAgAUGShMAAQQcQATYCOCABRAAAAAAAAPA/EAI2AlggAUH4AGogAUEMaiABQThqIAFB2ABqELIBIAEtAHhFDQEMEgsgAUEANgKcASABQgQ3ApQBIAMgBE0NAiABIARBAWo2AhwgBCAFai0AACINBEADQCABKAIcIgAgASgCGCICTw0LIABBAWoiAyACTw0MIAEoAhAiAiAAai0AACETIAEgAEECajYCHCACIANqLQAAIRAgAUH4AGogAUEQahB0IAFBOGohEiABKAJ4Ig4hCiABKAKAASEAQQAhAyMAQSBrIgckAAJAAkACQAJAAkAgAEUEQEEBIQYMAQsgAEEASA0jQb3lwQAtAAAaIABBARCcAiIGRQ0BIABBCEkNAANAIAMgCmoiAkEEaigAACIEIAIoAAAiBXJBgIGChHhxDQEgAyAGaiICQQRqIARBwQBrQf8BcUEaSUEFdCAEcjoAACACIAVBwQBrQf8BcUEaSUEFdCAFcjoAACACQQdqIARBGHYiCUHBAGtB/wFxQRpJQQV0IAlyOgAAIAJBBmogBEEQdiIJQcEAa0H/AXFBGklBBXQgCXI6AAAgAkEFaiAEQQh2IgRBwQBrQf8BcUEaSUEFdCAEcjoAACACQQNqIAVBGHYiBEHBAGtB/wFxQRpJQQV0IARyOgAAIAJBAmogBUEQdiIEQcEAa0H/AXFBGklBBXQgBHI6AAAgAkEBaiAFQQh2IgJBwQBrQf8BcUEaSUEFdCACcjoAACADQRBqIQIgA0EIaiEDIAAgAk8NAAsLIAcgBjYCCCAHIAA2AgwgByADNgIQIAAgA0YNAyAAIApqIREgACADayEJQQAhDCADIApqIgohBANAAn8gBCwAACIAQQBOBEAgAEH/AXEhACAEQQFqDAELIAQtAAFBP3EhAyAAQR9xIQIgAEFfTQRAIAJBBnQgA3IhACAEQQJqDAELIAQtAAJBP3EgA0EGdHIhAyAAQXBJBEAgAyACQQx0ciEAIARBA2oMAQsgAkESdEGAgPAAcSAELQADQT9xIANBBnRyciIAQYCAxABGDQUgBEEEagshBQJAAkAgAEGjB0cEQCAAQYCAxABHDQEMBwsCQCAMRQ0AIAkgDE0EQCAJIAxGDQEMBwsgCiAMaiwAAEG/f0wNBgsgCiAMaiEAQQAhAwJAAkACQAJAA0AgACAKRg0BIABBAWsiAi0AACIGwCILQQBIBEAgC0E/cQJ/IABBAmsiAi0AACIGwCILQUBOBEAgBkEfcQwBCyALQT9xAn8gAEEDayICLQAAIgbAIgtBQE4EQCAGQQ9xDAELIAtBP3EgAEEEayICLQAAQQdxQQZ0cgtBBnRyC0EGdHIiBkGAgMQARg0CCwJ/AkAgA0H/AXENACAGEGVFDQBBgIDEACEGQQAMAQtBAQshAyACIQAgBkGAgMQARg0ACyAGEGZFDQAgDEECaiIABH8CQCAAIAlPBEAgACAJRg0BDAsLIAAgCmosAABBv39MDQoLIAkgAGsFIAkLIAAgCmoiAGohD0EAIQIDQCAAIA9GDQICfyAALAAAIgNBAE4EQCADQf8BcSEGIABBAWoMAQsgAC0AAUE/cSELIANBH3EhBiADQV9NBEAgBkEGdCALciEGIABBAmoMAQsgAC0AAkE/cSALQQZ0ciELIANBcEkEQCALIAZBDHRyIQYgAEEDagwBCyAGQRJ0QYCA8ABxIAAtAANBP3EgC0EGdHJyIgZBgIDEAEYNAyAAQQRqCyEAAn8CQCACQf8BcQ0AIAYQZUUNAEGAgMQAIQZBAAwBC0EBCyECIAZBgIDEAEYNAAsgBhBmRQ0BC0HPhwIhBiAHKAIMIAcoAhAiAGtBAkkNAQwCC0HPhQIhBiAHKAIMIAcoAhAiAGtBAUsNAQsgB0EIaiAAQQIQjAEgBygCECEACyAHKAIIIABqIAY7AAAgByAAQQJqNgIQDAELIAdBFGohBkEAIQsCQCAAQYABTwRAQf8KIQJB/wohAwJAA0ACQEF/IAJBAXYgC2oiAkEDdEHci8EAaigCACIPIABHIAAgD0sbIg9BAUYEQCACIQMMAQsgD0H/AXFB/wFHDQIgAkEBaiELCyADIAtrIQIgAyALSw0ACyAGQgA3AgQgBiAANgIADAILIAZChwZCACACQQN0QeCLwQBqKAIAIgBBgIDEAEYgAEGAsANzQYCAxABrQYCQvH9JciICGzcCBCAGQekAIAAgAhs2AgAMAQsgBkIANwIEIAYgAEHBAGtB/wFxQRpJQQV0IAByNgIACwJAIAcoAhgiAgRAIAcoAhwhACAHQQhqIgMgBygCFBBpIAMgAhBpIABFDQIMAQsgBygCFCEACyAHQQhqIAAQaQsgDCAEayAFaiEMIBEgBSIERw0ACwwDC0EBIAAQvQIACyAKIAkgACAJQdjgwAAQlgIACyAKIAlBACAMQcjgwAAQlgIACyASIAcpAgg3AgAgEkEIaiAHQRBqKAIANgIAIAdBIGokACABKAJ8BEAgDhBECyABKAI4IQcgASgCQCEDIAFBADYCgAEgAUIBNwJ4IANBBU8EQCADQQVuIQZBACEFQQQhAANAIABBAmsgA08NDyAAQQFrIANPDRAgACADTw0RQQJBASAAIAdqIgJBAmstAABB4QBrIgpBAXEbIQsgAkEDay0AAEHhAGshEiACQQRrLQAAQeEAayEOIAItAABB4QBrIREgAkEBay0AAEHhAGshDyABKAJ8IAVGBEAgAUH4AGohBCMAQSBrIgIkACAFQQFqIgVFDSFBBCAEKAIEIglBAXQiDCAFIAUgDEkbIgUgBUEETRsiDEHWqtWqAUkhBSAMQQZsIRQCQCAJBEAgAkEBNgIYIAIgCUEGbDYCHCACIAQoAgA2AhQMAQsgAkEANgIYCyACQQhqIAUgFCACQRRqEI8BIAIoAgwhBQJAIAIoAghFBEAgBCAMNgIEIAQgBTYCAAwBCyAFQYGAgIB4Rg0AIAVFDSIgBSACQRBqKAIAEL0CAAsgAkEgaiQAIAEoAoABIQULIAEoAnggBUEGbGoiAiAROgAFIAIgDzoABCACIAs6AAMgAkECQQEgCkECcRs6AAIgAiASOgABIAIgDjoAACABIAEoAoABQQFqIgU2AoABIABBBWohACAGQQFrIgYNAAsLIAFB4ABqIgYgAUGAAWooAgA2AgAgASABKQJ4NwNYIAEoApwBIgAgASgCmAFGBEAgAUGUAWohAyMAQSBrIgIkACAAQQFqIgBFDR9BBCADKAIEIgRBAXQiBSAAIAAgBUkbIgAgAEEETRsiBUEEdCEAIAVBgICAwABJQQJ0IQkCQCAEBEAgAiADKAIANgIUIAJBBDYCGCACIARBBHQ2AhwMAQsgAkEANgIYCyACQQhqIAkgACACQRRqEI8BIAIoAgwhAAJAIAIoAghFBEAgAyAFNgIEIAMgADYCAAwBCyAAQYGAgIB4Rg0AIABFDSAgACACQRBqKAIAEL0CAAsgAkEgaiQAIAEoApwBIQALIAEoApQBIABBBHRqIgAgASkDWDcCACAAIBBBAXRBAWs7AQ4gACATQQF0OwEMIABBCGogBigCADYCACABIAEoApwBQQFqNgKcASABKAI8BEAgBxBECyANQQFrIg1B/wFxDQALC0HA5MEAKAIADQFBwOTBAEIBNwIAQcjkwQAgASkClAE3AgBB0OTBACABQZwBaigCADYCAAwQCyABKAJYIgBBhAFPBEAgABAACyABKAI4IgBBhAFPBEAgABAACyABQdgAaiABQRBqEHQgASgCHCIDIAEoAhgiB08NAiADQQFqIgAgB08NAyADQQJqIgIgB08NBCAJQSBxIQ0gASgCECIJIANqLQAAIRAgACAJai0AACEMIAEgA0EDaiIANgIcIAIgCWotAAAhBiABQQA2AoABIAFCBDcCeCAGRQRAIAAhAgwPCwJAAkAgDQRAIAlBA2ohCyABKAIcIQUDQCADQQ1qIAdLDQMgA0EDakF1Sw0CQb3lwQAtAAAaQQpBARCcAiIERQ0JIAQgAyALaiICKQAANwAAIARBCGogAkEIai8AADsAACABKAKAASICIAEoAnxGBEAgAUH4AGogAhCFASABKAKAASECCyABKAJ4IAJBDGxqIgJCioCAgKABNwIEIAIgBDYCACABIAEoAoABQQFqNgKAASADQQpqIQMgAEEKaiIFIQAgBkEBayIGQf8BcQ0ACyADQQNqIQIMEAsgDCAMbCEDIAEoAhwhBEEAIQUDQAJAIAcgACADaiICTwRAIAAgAk0NASABIAQ2AhwgACACQayDwAAQtgEACyABIAQ2AhxBkIPAAEEKQbyDwAAQ5AEACwJAIAxFBEBBASEEDAELQb3lwQAtAAAaIANBARCcAiIERQ0KIAEoAoABIQULIAQgACAJaiADEMACIQQgASgCfCAFRgRAIAFB+ABqIAUQhQEgASgCgAEhBQsgASgCeCAFQQxsaiIAIAM2AgggACADNgIEIAAgBDYCACABIAEoAoABQQFqIgU2AoABIAIhBCACIQAgBkEBayIGQf8BcQ0ACwwPCyABIAU2AhwgA0EDaiADQQ1qQayDwAAQtgEACyABIAU2AhxBkIPAAEEKQbyDwAAQ5AEAC0HE5MEAKAIADQZBzOTBACgCAEHI5MEAKAIAIQJByOTBACABKQKUATcCAEHQ5MEAKAIAIQNB0OTBACABQZwBaigCADYCAEHE5MEAQQA2AgAgAkUNDiADBEAgAiEAA0AgAEEEaigCAARAIAAoAgAQRAsgAEEQaiEAIANBAWsiAw0ACwtFDQ4gAhBEDA4LIAQgA0GAg8AAELQBAAsgAyAHQYCDwAAQtAEACyAAIAdBgIPAABC0AQALIAIgB0GAg8AAELQBAAsgASADQQ1qNgIcQQFBChC9AgALIAEgAjYCHEEBIAMQvQIAC0Hcp8AAQRAgAUH4AGpB7KfAAEGYqMAAEKkBAAsgACACQYCDwAAQtAEACyADIAJBgIPAABC0AQALIABBAmsgA0HMg8AAELQBAAsgAEEBayADQdyDwAAQtAEACyAAIANB7IPAABC0AQALIAEgAjYCHAsgAUFAayIOIAFBgAFqIhEoAgA2AgAgAUHMAGogAUHgAGooAgA2AgAgASABKQJ4NwM4IAEgASkCWDcCRAJAIAIgB08NACACIAlqLQAAIQMCQAJAAkACQAJAIBNB/wFxQQFrDgIDAQALIAogEkH//wNxTQ0CIANBGnENAQwCCyADQRpxRQ0BCwJAAkACQCABKAIsIgAEQCAAQRRsIQYgASgCJEEOaiEAIAEvAQohBANAAkAgAEECayIKLwEAIgsgAC8BACIFSwRAIAogBDsBACAAIAQgBWwgC247AQAMAQsgBUUNAyAAIAQ7AQAgCiAEIAtsIAVuOwEACyAAQRRqIQAgBkEUayIGDQALCyABQYWEwABBBRABNgJYIAEgAUEMaiABQdgAahDCASABKAIEIQAgASgCAA0BIAEgADYClAEMAgtBwITAAEEZQbCEwAAQzQEACyABQYEBNgKUASAAQYQBSQ0AIAAQAAsgASABQZQBahDEAjYCVCABIAFBCmo2AnggAUHUAGogAUH4AGpBnITAABCpAiABKAJUIgBBhAFPBEAgABAACyABKAKUASIAQYQBTwRAIAAQAAsgASgCWCIAQYQBSQ0BIAAQAAwBCyADQeUBcSEDCwJAIAJBAWoiACAHTw0AIAAgCWotAABBAUcNACABQdmEwABBAxABNgKUASABRAAAAAAAAPA/EAI2AlggAUH4AGogAUEMaiABQZQBaiABQdgAahCyASABLQB4RQRAIAEoAlgiAEGEAU8EQCAAEAALIAEoApQBIgBBhAFJDQEgABAADAELDAMLIAFB3ITAAEELEAE2ApQBIAEgA7gQAjYCWCABQfgAaiABQQxqIAFBlAFqIAFB2ABqELIBIAEtAHgNAiABKAJYIgBBhAFPBEAgABAACyABKAKUASIAQYQBSQ0AIAAQAAsgAUGIAWogAUHIAGopAwA3AwAgESAOKQMANwMAIAEgASkDODcDeCABIA1BBXY6AJIBIAEgDDoAkQEgASAQOgCQASABQdgAaiEEIAFB+ABqIQAjAEEgayIDJAACQAJAAkBBAEHohMAAKAIAEQMAIgIEQCACKAIARQ0BQdynwABBECADQR9qQeynwABBiKjAABCpAQALIAAoAggiDQRAIAAoAgAhBANAIARBBGooAgAEQCAEKAIAEEQLIARBDGohBCANQQFrIg0NAAsLIAAoAgQEQCAAKAIAEEQLIABBEGooAgBFDQEgACgCDBBEDAELIAIpAgQhHSACIAApAgA3AgQgA0EYaiIGIAJBHGoiBy8BADsBACADQRBqIgkgAkEUaiIMKQIANwMAIANBCGoiCiACQQxqIg0pAgA3AwAgAkEfai0AACELIAJBHmotAAAhBSAHIABBGGooAgA2AgAgDSAAQQhqKQIANwIAIAwgAEEQaikCADcCACADIB03AwAgAkEANgIAIAVBA0YNACAEIAMpAwA3AgAgBCALOgAbIAQgBToAGiAEQRhqIAYvAQA7AQAgBEEQaiAJKQMANwIAIARBCGogCikDADcCACADQSBqJAAMAQtBpKbAAEHGACADQR9qQeymwABBzKfAABCpAQALIAEtAHJBAkYNACABKAJYIQIgASgCYCIDBEAgAiEAA0AgAEEEaigCAARAIAAoAgAQRAsgAEEMaiEAIANBAWsiAw0ACwsgASgCXARAIAIQRAsgAUHoAGooAgBFDQAgASgCZBBECwJAAkBB1OTBACgCAEUEQEHU5MEAQgE3AgBB3OTBACABKQIkNwIAQeTkwQAgAUEsaigCADYCAAwBC0HY5MEAKAIADQFB4OTBACgCAEHc5MEAKAIAIQJB3OTBACABKQIkNwIAQeTkwQAoAgAhA0Hk5MEAIAFBLGooAgA2AgBB2OTBAEEANgIAIAJFDQAgAwRAIAIhAANAIABBBGooAgAEQCAAKAIAEEQLIABBFGohACADQQFrIgMNAAsLRQ0AIAIQRAsgASgCDBADIAEoAjQiAkGEAU8EQCACEAALIAEoAiAiAkGEAU8EQCACEAALIAEoAhQEQCABKAIQEEQLIAEoAgwiAkGEAU8EQCACEAALIAFBoAFqJAAMCgtB3KfAAEEQIAFB+ABqQeynwABBqKjAABCpAQALIAEoAnwQowEACyABIAA2AhwMAQsgASAANgIcIABBAWogA0GAg8AAELQBAAsgACADQYCDwAAQtAEACyAAQQNqIANBgIPAABC0AQALIABBBWogA0GAg8AAELQBAAsgAEEHaiADQYCDwAAQtAEACyACIANBgIPAABC0AQALIAIgAEGAg8AAELQBAAshACAIKAKIAUUNACAIKAKEARBECyAVQYQBTwRAIBUQAAsgCCgCgAEiAkGEAU8EQCACEAALIAhBkAFqJAAgAAwCCxDUAQALIAMgAEGAg8AAELQBAAsLAgALAgALC+vjAQUAQYCAwAALkGkvcnVzdGMvY2M2NmFkNDY4OTU1NzE3YWI5MjYwMGM3NzBkYThjMTYwMWE0ZmYzMy9saWJyYXJ5L2NvcmUvc3JjL3N0ci9tb2QucnMAAAAQAEsAAACSAgAADQAAAC9ydXN0Yy9jYzY2YWQ0Njg5NTU3MTdhYjkyNjAwYzc3MGRhOGMxNjAxYTRmZjMzL2xpYnJhcnkvY29yZS9zcmMvc3RyL3BhdHRlcm4ucnMAXAAQAE8AAACzBQAAFAAAAFwAEABPAAAAswUAACEAAABcABAATwAAAKcFAAAhAAAAXAAQAE8AAAA3BAAAJAAAAGNhbGxlZCBgT3B0aW9uOjp1bndyYXAoKWAgb24gYSBgTm9uZWAgdmFsdWVzcmMvYm9vay5ycwAAFwEQAAsAAAAPAAAAOQAAAGNhbGxlZCBgUmVzdWx0Ojp1bndyYXAoKWAgb24gYW4gYEVycmAgdmFsdWUABQAAAAgAAAAEAAAABgAAABcBEAALAAAAEAAAACMAAAAXARAACwAAACIAAAAcAAAAb3ZlcmZsb3cgIQAAFwEQAAsAAABKAAAAIwAAABcBEAALAAAAUQAAACAAAAAXARAACwAAAE8AAAANAAAAFwEQAAsAAACGAAAAFQAAABcBEAALAAAAjAAAABgAAAAXARAACwAAAI0AAAAYAAAAZGlyZWN0aW9ucGFnZXNjaGFwdGVyc3ZlcnNpb24AAAAHAAAABAAAAAQAAAAIAAAACQAAABcBEAALAAAAUgEAACQAAABhdHRlbXB0IHRvIGRpdmlkZSBieSB6ZXJvbmF2aW1hZ2VfdHlwZXMACgAAAAsAAAAMAAAAbmFtZXBhZ2V2aWV3d2lkdGhoZWlnaHRwb3NpdGlvbmp1bXBzbGVmdHJpZ2h0dG9wYm90dG9tAAAXARAACwAAAHQBAAAjAAAABwAAAAQAAAAEAAAADQAAAA4AAABieXRlcz0tANACEAAGAAAA1gIQAAEAAAAXARAACwAAAAMCAAA3AAAAZ2V0IGVycm9ydG9CbG9idG9EYXRhVVJMZ2V0SW1hZ2VEYXRhDwAAAAQAAAAEAAAAEAAAABcBEAALAAAABAIAADMAAAAXARAACwAAAAMCAABBAAAAFwEQAAsAAAAXAgAADwAAAAAAAABhdHRlbXB0IHRvIGNhbGN1bGF0ZSB0aGUgcmVtYWluZGVyIHdpdGggYSBkaXZpc29yIG9mIHplcm8AAAAXARAACwAAAGICAAA9AAAAFwEQAAsAAABhAgAADgAAABcBEAALAAAAVQIAACsAAAAXARAACwAAAHICAAA9AAAAFwEQAAsAAABxAgAADgAAABcBEAALAAAAZQIAACwAAAAXARAACwAAAIICAAA9AAAAFwEQAAsAAACBAgAADgAAABcBEAALAAAAdQIAACwAAAAXARAACwAAAJACAAAOAAAAFwEQAAsAAAC9AgAADgAAABcBEAALAAAAvwIAAA0AAAAXARAACwAAAM0CAAAVAAAAFwEQAAsAAADNAgAADgAAABcBEAALAAAAzgIAABUAAABkYXRhaW1hZ2VjdHh4eWRyYXcgZmFpbGVkAAAAFwEQAAsAAABsAwAADgAAABcBEAALAAAALQMAACIAAAAXARAACwAAACIDAAAiAAAAYXV0b2dyYXBoZWRmYXRhbCBlcnJvciAA4wQQAAwAAAAXARAACwAAAFgDAAARAAAAFwEQAAsAAAB8AwAAEQAAABcBEAALAAAAjgMAABEAAAAXARAACwAAAM0DAAAcAAAAFwEQAAsAAADSAwAAHAAAABcBEAALAAAA5AMAACwAAAAXARAACwAAAOUDAAAjAAAAFwEQAAsAAAAXBAAARAAAABEAAABsYXlvdXRwYXRoAAAXARAACwAAAGQEAABGAAAAXFwiAAAAEAAAAAAAAAAQAAAAAAAsIiJ7IiIiIjoBAAFBQkNERUZHSElKS0xNTk9QUVJTVFVWV1hZWmFiY2RlZmdoaWprbG1ub3BxcnN0dXZ3eHl6MDEyMzQ1Njc4OSsv/////////////////////////////////////////////////////////z7///8/NDU2Nzg5Ojs8Pf////////8AAQIDBAUGBwgJCgsMDQ4PEBESExQVFhcYGf///////xobHB0eHyAhIiMkJSYnKCkqKywtLi8wMTIz/////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////xcBEAALAAAAsAQAABsAAAAXARAACwAAALoEAAAaAAAAYmFzZTY0IGRlY29kZSBlcnJvcgAXARAACwAAAKgEAAAXAAAAFwEQAAsAAADRBAAAIwAAAGhkAAAHAAAACAAAAAQAAAASAAAAEwAAAAcAAAAQAAAABAAAABQAAAAVAAAAFwEQAAsAAAD+BAAARQAAABcBEAALAAAA/gQAAB0AAAAXARAACwAAAP4EAAAUAAAAL3J1c3RjL2NjNjZhZDQ2ODk1NTcxN2FiOTI2MDBjNzcwZGE4YzE2MDFhNGZmMzMvbGlicmFyeS9jb3JlL3NyYy9zdHIvcGF0dGVybi5ycwCoBxAATwAAALgBAAA3AAAAGAAAAAQAAAAEAAAAGQAAABoAAAAYAAAABAAAAAQAAAAbAAAAHAAAAB0AAADEAAAABAAAAB4AAABjYWxsZWQgYE9wdGlvbjo6dW53cmFwX3Rocm93KClgIG9uIGEgYE5vbmVgIHZhbHVlAAAAHwAAAAwCAAAEAAAAIAAAAC9Vc2Vycy9oa2FuZWRhLy5jYXJnby9yZWdpc3RyeS9zcmMvaW5kZXguY3JhdGVzLmlvLTZmMTdkMjJiYmExNTAwMWYvd2FzbS1iaW5kZ2VuLWZ1dHVyZXMtMC40LjUwL3NyYy9saWIucnMAAIQIEABqAAAA5gAAABUAAABgYXN5bmMgZm5gIHJlc3VtZWQgYWZ0ZXIgY29tcGxldGlvbgBhc3NlcnRpb24gZmFpbGVkOiBtaWQgPD0gc2VsZi5sZW4oKVNIQS0yNTZzcmMvY3J5cHRvLnJzAE4JEAANAAAADwAAAFcAAABOCRAADQAAADYAAAAbAAAAAAAAAGF0dGVtcHQgdG8gY2FsY3VsYXRlIHRoZSByZW1haW5kZXIgd2l0aCBhIGRpdmlzb3Igb2YgemVybwAAAE4JEAANAAAAQAAAACEAAABlbmNyeXB0ZGVjcnlwdHJhd0FFUy1HQ01OCRAADQAAAD8AAAAfAAAATgkQAA0AAABRAAAAHAAAAG5hbWVpdgAATgkQAA0AAABuAAAAYAAAAE4JEAANAAAAcgAAAEQAAABzcmMvbGliLnJzAAAsChAACgAAAC0AAAAaAAAAAQABQUJDREVGR0hJSktMTU5PUFFSU1RVVldYWVphYmNkZWZnaGlqa2xtbm9wcXJzdHV2d3h5ejAxMjM0NTY3ODkrL/////////////////////////////////////////////////////////8+////PzQ1Njc4OTo7PD3/////////AAECAwQFBgcICQoLDA0ODxAREhMUFRYXGBn///////8aGxwdHh8gISIjJCUmJygpKissLS4vMDEyM/////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////9kZWNvZGUgZXJyb3IALAoQAAoAAAAnAAAAAQAAAG5mOi9fZWJqqAsQAAMAAACrCxAAAQAAAKwLEAAEAAAALAoQAAoAAACCAAAAVQAAAC5qcGckCRAAAAAAAKsLEAABAAAAqwsQAAEAAACrCxAAAQAAANgLEAAEAAAALAoQAAoAAACGAAAAFQAAACwKEAAKAAAAgQAAAAEAAADTAAAAHQAAAMUAAAArAAAAswAAAFkAAABPAAAAZmFpbGVkIHRvIGZpbGwgd2hvbGUgYnVmZmVyAEAMEAAbAAAAJQAAAGludmFsaWQgYXJnc2gMEAAMAAAAL3J1c3RjL2NjNjZhZDQ2ODk1NTcxN2FiOTI2MDBjNzcwZGE4YzE2MDFhNGZmMzMvbGlicmFyeS9jb3JlL3NyYy9mbXQvbW9kLnJzAHwMEABLAAAANQEAAA0AAABBZGxlcjMyIGNoZWNrc3VtIG1pc21hdGNoZWQ6IHZhbHVlPSwgZXhwZWN0ZWQ9AADYDBAAIwAAAPsMEAALAAAAIwAAAAwAAAAEAAAAJAAAACMAAAAMAAAABAAAACUAAAAkAAAAGA0QACYAAAAnAAAAKAAAACYAAAApAAAAL1VzZXJzL2hrYW5lZGEvLmNhcmdvL3JlZ2lzdHJ5L3NyYy9pbmRleC5jcmF0ZXMuaW8tNmYxN2QyMmJiYTE1MDAxZi9saWJmbGF0ZS0xLjQuMC9zcmMvemxpYi5ycwAAVA0QAF4AAAChAQAAKQAAAFZlYyBpcyBzaXplZCBjb25zZXJ2YXRpdmVseQDEDRAAGwAAAGludGVybmFsIGVycm9yOiBlbnRlcmVkIHVucmVhY2hhYmxlIGNvZGU6IAAA6A0QACoAAAAvVXNlcnMvaGthbmVkYS8uY2FyZ28vcmVnaXN0cnkvc3JjL2luZGV4LmNyYXRlcy5pby02ZjE3ZDIyYmJhMTUwMDFmL2Jhc2U2NC0wLjIyLjEvc3JjL2VuZ2luZS9tb2QucnMAHA4QAGMAAAABAQAAGQAAAFByZXNldCBkaWN0aW9uYXJpZXMgYXJlIG5vdCBzdXBwb3J0ZWQ6IGRpY3Rpb25hcnlfaWQ9MHgAkA4QADcAAABDb21wcmVzc2lvbiBtZXRob2RzIG90aGVyIHRoYW4gREVGTEFURSg4KSBhcmUgdW5zdXBwb3J0ZWQ6IG1ldGhvZD0AANAOEABCAAAASW5jb25zaXN0ZW50IFpMSUIgY2hlY2sgYml0czogYENNRigpICogMjU2ICsgRkxHKClgIG11c3QgYmUgYSBtdWx0aXBsZSBvZiAzMRwPEAAjAAAAPw8QAA4AAABNDxAAGwAAAENJTkZPIGFib3ZlIDcgYXJlIG5vdCBhbGxvd2VkOiB2YWx1ZT0AAACADxAAJQAAAGNhbGxlZCBgUmVzdWx0Ojp1bndyYXBfdGhyb3coKWAgb24gYW4gYEVycmAgdmFsdWVjYWxsZWQgYE9wdGlvbjo6dW53cmFwKClgIG9uIGEgYE5vbmVgIHZhbHVlc3JjL2NyeXB0by5ycwAAAAwQEAANAAAACQAAAAoAAABmYXRhbCBlcnJvcgAMEBAADQAAAAsAAAAdAAAAfAwQAAAAAAAQAAAAEQAAABIAAAAAAAAACAAAAAcAAAAJAAAABgAAAAoAAAAFAAAACwAAAAQAAAAMAAAAAwAAAA0AAAACAAAADgAAAAEAAAAPAAAAVGhlIGxlbmd0aCBvZiBgZGlzdGFuY2VfY29kZV9iaXR3aWR0aGVzYCBpcyB0b28gbGFyZ2U6IGFjdHVhbD0sIGV4cGVjdGVkPQAAAJwQEAA+AAAA2hAQAAsAAAArAAAADAAAAAQAAAAkAAAAKwAAAAwAAAAEAAAAJQAAACQAAAD4EBAAJgAAACcAAAAoAAAAJgAAACkAAAAvVXNlcnMvaGthbmVkYS8uY2FyZ28vcmVnaXN0cnkvc3JjL2luZGV4LmNyYXRlcy5pby02ZjE3ZDIyYmJhMTUwMDFmL2xpYmZsYXRlLTEuNC4wL3NyYy9kZWZsYXRlL3N5bWJvbC5yczQREABoAAAAnQEAAA0AAABUaGUgdmFsdWUgb2YgSERJU1QgaXMgdG9vIGJpZzogbWF4PSwgYWN0dWFsPawREAAjAAAAzxEQAAkAAAAeAAAAZmFpbGVkIHRvIGZpbGwgd2hvbGUgYnVmZmVyAOwREAAbAAAAJQAAACwAAAAIAAAABAAAAC0AAAAuAAAALwAAADAAAABpbnRlcm5hbCBlcnJvcjogZW50ZXJlZCB1bnJlYWNoYWJsZSBjb2RlNBEQAGgAAADlAQAADgAAADEAAAACAAAAAQAAADIAAAAzAAAANAAAADUAAABObyBwcmVjZWRpbmcgdmFsdWUvVXNlcnMvaGthbmVkYS8uY2FyZ28vcmVnaXN0cnkvc3JjL2luZGV4LmNyYXRlcy5pby02ZjE3ZDIyYmJhMTUwMDFmL2xpYmZsYXRlLTEuNC4wL3NyYy9odWZmbWFuLnJzAJYSEABhAAAAqwAAAB8AAABJbnZhbGlkIGh1ZmZtYW4gY29kZWQgc3RyZWFtY2Fubm90IGFjY2VzcyBhIFRocmVhZCBMb2NhbCBTdG9yYWdlIHZhbHVlIGR1cmluZyBvciBhZnRlciBkZXN0cnVjdGlvbgAANgAAAAAAAAABAAAANwAAAC9ydXN0Yy9jYzY2YWQ0Njg5NTU3MTdhYjkyNjAwYzc3MGRhOGMxNjAxYTRmZjMzL2xpYnJhcnkvc3RkL3NyYy90aHJlYWQvbG9jYWwucnMAfBMQAE8AAAD2AAAAGgAAAGFscmVhZHkgYm9ycm93ZWQ2AAAAAAAAAAEAAAA4AAAAc3JjL2Jvb2sucnMA/BMQAAsAAAC8AQAAIAAAAPwTEAALAAAAywEAAB0AAAD8ExAACwAAAM0BAAAWAAAAYWxyZWFkeSBtdXRhYmx5IGJvcnJvd2VkY2FsbGVkIGBPcHRpb246OnVud3JhcCgpYCBvbiBhIGBOb25lYCB2YWx1ZQD8ExAACwAAANUBAAAOAAAA/BMQAAsAAADXAQAADgAAADYAAAAAAAAAAQAAADkAAAD8ExAACwAAANMBAAALAAAA/BMQAAsAAADuAQAADgAAAPwTEAALAAAA8AEAAA4AAAD8ExAACwAAAOwBAAALAAAA/BMQAAsAAAD2AQAAHAAAAPwTEAALAAAA+gEAAC0AAAD8ExAACwAAAPoBAAAcAAAA/BMQAAsAAAAuBAAAKgAAAPwTEAALAAAALgQAAD0AAAD8ExAACwAAAC4EAAAZAAAA/BMQAAsAAAA1BAAADwAAAPwTEAALAAAANAQAAA4AAABzcmMvbGliLnJzAABsFRAACgAAACAAAAAZAAAAbBUQAAoAAAAkAAAAKgAAAGwVEAAKAAAAJAAAABkAAAA7AAAACAAAAAQAAAA8AAAAPQAAADsAAAAIAAAABAAAAD4AAABmYXRhbCBlcnJvciDMFRAADAAAAHNyYy9saWIucnMAAOAVEAAKAAAAFQAAAAUAAAA/AAAAbW9kZWRwcmxpbWl0c2l6ZWZsYWcvVXNlcnMvaGthbmVkYS8uY2FyZ28vcmVnaXN0cnkvc3JjL2luZGV4LmNyYXRlcy5pby02ZjE3ZDIyYmJhMTUwMDFmL2xpYmZsYXRlX2x6NzctMS4yLjAvc3JjL2xpYi5ycwAAFBYQAGIAAADfAAAAFQAAAFRvbyBsb25nIGJhY2t3b3JkIHJlZmVyZW5jZTogYnVmZmVyLmxlbj0sIGRpc3RhbmNlPQCIFhAAKAAAALAWEAALAAAAQAAAAAwAAAAEAAAAJAAAAEAAAAAMAAAABAAAACUAAAAkAAAAzBYQACYAAAAnAAAAKAAAACYAAAApAAAAL1VzZXJzL2hrYW5lZGEvLmNhcmdvL3JlZ2lzdHJ5L3NyYy9pbmRleC5jcmF0ZXMuaW8tNmYxN2QyMmJiYTE1MDAxZi9ybGUtZGVjb2RlLWZhc3QtMS4wLjMvc3JjL2xpYi5yc3NyYyBpcyBvdXQgb2YgYm91bmRzCBcQAGQAAABOAAAABQAAAHNyYyBlbmQgaXMgYmVmb3JlIHNyYyBzdGFydAAIFxAAZAAAAE0AAAAFAAAAZmFpbGVkIHRvIGZpbGwgd2hvbGUgYnVmZmVyALwXEAAbAAAAJQAAAGJ0eXBlIDB4MTEgb2YgREVGTEFURSBpcyByZXNlcnZlZChlcnJvcikgdmFsdWVpbnRlcm5hbCBlcnJvcjogZW50ZXJlZCB1bnJlYWNoYWJsZSBjb2RlL1VzZXJzL2hrYW5lZGEvLmNhcmdvL3JlZ2lzdHJ5L3NyYy9pbmRleC5jcmF0ZXMuaW8tNmYxN2QyMmJiYTE1MDAxZi9saWJmbGF0ZS0xLjQuMC9zcmMvZGVmbGF0ZS9kZWNvZGUucnMAADoYEABoAAAAqAAAABYAAABMRU49IGlzIG5vdCB0aGUgb25lJ3MgY29tcGxlbWVudCBvZiBOTEVOPQAAALQYEAAEAAAAuBgQACUAAABUaGUgcmVhZGVyIGhhcyBpbmNvcnJlY3QgbGVuZ3RoOiBleHBlY3RlZCAsIHJlYWQgAAAA8BgQACoAAAAaGRAABwAAAAEAAAACAAAAAwAAAAQAAAAFAAEABwABAAkAAgANAAIAEQADABkAAwAhAAQAMQAEAEEABQBhAAUAgQAGAMEABgABAQcAgQEHAAECCAABAwgAAQQJAAEGCQABCAoAAQwKAAEQCwABGAsAASAMAAEwDAABQA0AAWANAC9Vc2Vycy9oa2FuZWRhLy5jYXJnby9yZWdpc3RyeS9zcmMvaW5kZXguY3JhdGVzLmlvLTZmMTdkMjJiYmExNTAwMWYvbGliZmxhdGUtMS40LjAvc3JjL2RlZmxhdGUvc3ltYm9sLnJzrBkQAGgAAADzAAAAIgAAAFRoZSB2YWx1ZSAgbXVzdCBub3Qgb2NjdXIgaW4gY29tcHJlc3NlZCBkYXRhJBoQAAoAAAAuGhAAIgAAAAMAAAAEAAAABQAAAAYAAAAHAAAACAAAAAkAAAAKAAAACwABAA0AAQAPAAEAEQABABMAAgAXAAIAGwACAB8AAgAjAAMAKwADADMAAwA7AAMAQwAEAFMABABjAAQAcwAEAIMABQCjAAUAwwAFAOMABQACAQAArBkQAGgAAADkAAAAKgAAAC9Vc2Vycy9oa2FuZWRhLy5jYXJnby9yZWdpc3RyeS9zcmMvaW5kZXguY3JhdGVzLmlvLTZmMTdkMjJiYmExNTAwMWYvbGliZmxhdGUtMS40LjAvc3JjL2h1ZmZtYW4ucnMAAADkGhAAYQAAAKsAAAAfAAAASW52YWxpZCBodWZmbWFuIGNvZGVkIHN0cmVhbS9ydXN0Yy9jYzY2YWQ0Njg5NTU3MTdhYjkyNjAwYzc3MGRhOGMxNjAxYTRmZjMzL2xpYnJhcnkvc3RkL3NyYy9pby9yZWFkYnVmLnJzAAAAdBsQAE0AAADjAAAAGgAAAC9ydXN0Yy9jYzY2YWQ0Njg5NTU3MTdhYjkyNjAwYzc3MGRhOGMxNjAxYTRmZjMzL2xpYnJhcnkvc3RkL3NyYy9pby9tb2QucnMAAAB0GxAATQAAANIAAABCAAAA1BsQAEkAAAClAQAANQAAAG51bWJlciBvZiByZWFkIGJ5dGVzIGV4Y2VlZHMgbGltaXQAAEAcEAAiAAAA1BsQAEkAAABCCgAACQAAANQbEABJAAAAVAoAADIAAABjbG9zdXJlIGludm9rZWQgcmVjdXJzaXZlbHkgb3IgYWZ0ZXIgYmVpbmcgZHJvcHBlZAAATGF6eSBpbnN0YW5jZSBoYXMgcHJldmlvdXNseSBiZWVuIHBvaXNvbmVkAADAHBAAKgAAAC9Vc2Vycy9oa2FuZWRhLy5jYXJnby9yZWdpc3RyeS9zcmMvaW5kZXguY3JhdGVzLmlvLTZmMTdkMjJiYmExNTAwMWYvb25jZV9jZWxsLTEuMjEuMy9zcmMvbGliLnJzAPQcEABfAAAACAMAABkAAAByZWVudHJhbnQgaW5pdAAAZB0QAA4AAAD0HBAAXwAAAHoCAAANAAAAYWxyZWFkeSBib3Jyb3dlZEEAAAAAAAAAAQAAADgAAAAvVXNlcnMvaGthbmVkYS8uY2FyZ28vcmVnaXN0cnkvc3JjL2luZGV4LmNyYXRlcy5pby02ZjE3ZDIyYmJhMTUwMDFmL3dhc20tYmluZGdlbi1mdXR1cmVzLTAuNC41MC9zcmMvdGFzay9zaW5nbGV0aHJlYWQucnNCAAAAQwAAAEQAAABFAAAArB0QAHgAAABnAAAAJQAAAGNsb3N1cmUgaW52b2tlZCByZWN1cnNpdmVseSBvciBhZnRlciBiZWluZyBkcm9wcGVkAABKAAAABAAAAAQAAABLAAAATAAAAE0AAAAEAAAABAAAAE4AAABPAAAATQAAAAQAAAAEAAAAUAAAAFEAAABGbk9uY2UgY2FsbGVkIG1vcmUgdGhhbiBvbmNlYWxyZWFkeSBtdXRhYmx5IGJvcnJvd2VkYWxyZWFkeSBib3Jyb3dlZFIAAAAAAAAAAQAAADgAAAAvVXNlcnMvaGthbmVkYS8uY2FyZ28vcmVnaXN0cnkvc3JjL2luZGV4LmNyYXRlcy5pby02ZjE3ZDIyYmJhMTUwMDFmL3dhc20tYmluZGdlbi1mdXR1cmVzLTAuNC41MC9zcmMvcXVldWUucnMIHxAAbAAAACgAAAApAAAAUgAAAAAAAAABAAAAOQAAAAgfEABsAAAAJQAAAC4AAAAIHxAAbAAAAD4AAAAaAAAAL1VzZXJzL2hrYW5lZGEvLmNhcmdvL3JlZ2lzdHJ5L3NyYy9pbmRleC5jcmF0ZXMuaW8tNmYxN2QyMmJiYTE1MDAxZi93YXNtLWJpbmRnZW4tZnV0dXJlcy0wLjQuNTAvc3JjL2xpYi5ycwAAtB8QAGoAAACxAAAADwAAALQfEABqAAAAkQAAACcAAAC0HxAAagAAALsAAAAkAAAAaW50ZXJuYWwgZXJyb3I6IGVudGVyZWQgdW5yZWFjaGFibGUgY29kZS9Vc2Vycy9oa2FuZWRhLy5jYXJnby9yZWdpc3RyeS9zcmMvaW5kZXguY3JhdGVzLmlvLTZmMTdkMjJiYmExNTAwMWYvbGliZmxhdGUtMS40LjAvc3JjL3psaWIucnMAAHggEABeAAAAOgAAABIAAABJbmRleCBvdXQgb2YgYm91bmRzAOggEAATAAAAL3J1c3RjL2NjNjZhZDQ2ODk1NTcxN2FiOTI2MDBjNzcwZGE4YzE2MDFhNGZmMzMvbGlicmFyeS9jb3JlL3NyYy9zbGljZS9zb3J0LnJzAAAEIRAATgAAADQEAAAOAAAABCEQAE4AAABBBAAAHAAAAAQhEABOAAAAQgQAAB0AAAAEIRAATgAAAEMEAAAlAAAAY2FsbGVkIGBPcHRpb246OnVud3JhcCgpYCBvbiBhIGBOb25lYCB2YWx1ZQAEIRAATgAAAIcEAABAAAAABCEQAE4AAACtBAAATgAAAAQhEABOAAAAuwQAAFYAAAAEIRAATgAAADcFAAApAAAAYXNzZXJ0aW9uIGZhaWxlZDogZW5kID49IHN0YXJ0ICYmIGVuZCA8PSBsZW4EIRAATgAAACYFAAAFAAAAYXNzZXJ0aW9uIGZhaWxlZDogb2Zmc2V0ICE9IDAgJiYgb2Zmc2V0IDw9IGxlbgAABCEQAE4AAACbAAAABQAAAC9Vc2Vycy9oa2FuZWRhLy5jYXJnby9yZWdpc3RyeS9zcmMvaW5kZXguY3JhdGVzLmlvLTZmMTdkMjJiYmExNTAwMWYvbGliZmxhdGUtMS40LjAvc3JjL2h1ZmZtYW4ucnMAAAB8IhAAYQAAAHIAAAAaAAAAQml0IHJlZ2lvbiBjb25mbGljdDogaT0sIG9sZF92YWx1ZT0sIG5ld192YWx1ZT0sIHN5bWJvbD0sIGNvZGU9APAiEAAXAAAAByMQAAwAAAATIxAADAAAAB8jEAAJAAAAKCMQAAcAAABVAAAADAAAAAQAAAAkAAAAVQAAAAwAAAAEAAAAJQAAACQAAABYIxAAVgAAAFcAAAAoAAAAVgAAAFgAAABDb2Rld2lkdGgAAABZAAAAAQAAAAEAAABaAAAAYml0c1sAAAAEAAAABAAAAFwAAAAvVXNlcnMvaGthbmVkYS8uY2FyZ28vcmVnaXN0cnkvc3JjL2luZGV4LmNyYXRlcy5pby02ZjE3ZDIyYmJhMTUwMDFmL2FkbGVyMzItMS4yLjAvc3JjL2xpYi5yc8QjEABcAAAAtAAAADcAAADEIxAAXAAAAKkAAAA3AAAAL1VzZXJzL2hrYW5lZGEvLmNhcmdvL3JlZ2lzdHJ5L3NyYy9pbmRleC5jcmF0ZXMuaW8tNmYxN2QyMmJiYTE1MDAxZi9saWJmbGF0ZV9sejc3LTEuMi4wL3NyYy9saWIucnMAAEAkEABiAAAA3wAAABUAAABAJBAAYgAAAPQAAAA2AAAAYXR0ZW1wdCB0byByZXBlYXQgZnJhZ21lbnQgb2Ygc2l6ZSAwL1VzZXJzL2hrYW5lZGEvLmNhcmdvL3JlZ2lzdHJ5L3NyYy9pbmRleC5jcmF0ZXMuaW8tNmYxN2QyMmJiYTE1MDAxZi9ybGUtZGVjb2RlLWZhc3QtMS4wLjMvc3JjL2xpYi5yc+gkEABkAAAAYQAAAAUAAAByZXR1cm4gdGhpcwD0cRAAAHIQAAxyEAAYchAAY2xvc3VyZSBpbnZva2VkIHJlY3Vyc2l2ZWx5IG9yIGFmdGVyIGJlaW5nIGRyb3BwZWQAAExhenkgaW5zdGFuY2UgaGFzIHByZXZpb3VzbHkgYmVlbiBwb2lzb25lZAAArCUQACoAAAAvVXNlcnMvaGthbmVkYS8uY2FyZ28vcmVnaXN0cnkvc3JjL2luZGV4LmNyYXRlcy5pby02ZjE3ZDIyYmJhMTUwMDFmL29uY2VfY2VsbC0xLjIxLjMvc3JjL2xpYi5ycwDgJRAAXwAAAAgDAAAZAAAAcmVlbnRyYW50IGluaXQAAFAmEAAOAAAA4CUQAF8AAAB6AgAADQAAAEpzVmFsdWUoKQAAAHgmEAAIAAAAgCYQAAEAAABMYXp5IGluc3RhbmNlIGhhcyBwcmV2aW91c2x5IGJlZW4gcG9pc29uZWQAAJQmEAAqAAAAL1VzZXJzL2hrYW5lZGEvLmNhcmdvL3JlZ2lzdHJ5L3NyYy9pbmRleC5jcmF0ZXMuaW8tNmYxN2QyMmJiYTE1MDAxZi9vbmNlX2NlbGwtMS4yMS4zL3NyYy9saWIucnMAyCYQAF8AAAAIAwAAGQAAAHJlZW50cmFudCBpbml0AAA4JxAADgAAAMgmEABfAAAAegIAAA0AAAAvVXNlcnMvaGthbmVkYS8uY2FyZ28vcmVnaXN0cnkvc3JjL2luZGV4LmNyYXRlcy5pby02ZjE3ZDIyYmJhMTUwMDFmL2Jhc2U2NC0wLjIyLjEvc3JjL2VuZ2luZS9nZW5lcmFsX3B1cnBvc2UvZGVjb2RlLnJzAABgJxAAdgAAAI0AAAAZAAAAL1VzZXJzL2hrYW5lZGEvLmNhcmdvL3JlZ2lzdHJ5L3NyYy9pbmRleC5jcmF0ZXMuaW8tNmYxN2QyMmJiYTE1MDAxZi9iYXNlNjQtMC4yMi4xL3NyYy9lbmdpbmUvZ2VuZXJhbF9wdXJwb3NlL2RlY29kZV9zdWZmaXgucnMAAADoJxAAfQAAAFQAAAAJAAAA6CcQAH0AAAAfAAAAJgAAAC9Vc2Vycy9oa2FuZWRhLy5jYXJnby9yZWdpc3RyeS9zcmMvaW5kZXguY3JhdGVzLmlvLTZmMTdkMjJiYmExNTAwMWYvYmFzZTY0LTAuMjIuMS9zcmMvZW5naW5lL2dlbmVyYWxfcHVycG9zZS9kZWNvZGUucnMAAIgoEAB2AAAAOAAAACYAAACIKBAAdgAAAF4AAAAuAAAAiCgQAHYAAABhAAAADQAAAIgoEAB2AAAAZQAAADgAAACIKBAAdgAAAD0AAAAnAAAAcQAAAAQAAAAEAAAAcgAAAHMAAAB0AAAAaW52YWxpZCBhcmdzaCkQAAwAAAAvcnVzdGMvY2M2NmFkNDY4OTU1NzE3YWI5MjYwMGM3NzBkYThjMTYwMWE0ZmYzMy9saWJyYXJ5L2NvcmUvc3JjL2ZtdC9tb2QucnMAfCkQAEsAAAA1AQAADQAAAGNhbGxlZCBgT3B0aW9uOjp1bndyYXAoKWAgb24gYSBgTm9uZWAgdmFsdWVBY2Nlc3NFcnJvck9zY29kZXEAAAAEAAAABAAAAHUAAABraW5kdgAAAAEAAAABAAAAdwAAAG1lc3NhZ2UAeAAAAAwAAAAEAAAAeQAAAEtpbmRFcnJvcgAAAHEAAAAIAAAABAAAAHoAAABtZW1vcnkgYWxsb2NhdGlvbiBvZiAgYnl0ZXMgZmFpbGVkAABsKhAAFQAAAIEqEAANAAAAbGlicmFyeS9zdGQvc3JjL2FsbG9jLnJzoCoQABgAAABUAQAACQAAAGxpYnJhcnkvc3RkL3NyYy9wYW5pY2tpbmcucnPIKhAAHAAAAFECAAAfAAAAyCoQABwAAABSAgAAHgAAAHgAAAAMAAAABAAAAHsAAABxAAAACAAAAAQAAAB8AAAAcQAAAAgAAAAEAAAAfQAAAH4AAAB/AAAAEAAAAAQAAACAAAAAgQAAAIIAAAAAAAAAAQAAAIMAAABVbnN1cHBvcnRlZEN1c3RvbWVycm9yAABxAAAABAAAAAQAAACEAAAATm90Rm91bmRQZXJtaXNzaW9uRGVuaWVkQ29ubmVjdGlvblJlZnVzZWRDb25uZWN0aW9uUmVzZXRIb3N0VW5yZWFjaGFibGVOZXR3b3JrVW5yZWFjaGFibGVDb25uZWN0aW9uQWJvcnRlZE5vdENvbm5lY3RlZEFkZHJJblVzZUFkZHJOb3RBdmFpbGFibGVOZXR3b3JrRG93bkJyb2tlblBpcGVBbHJlYWR5RXhpc3RzV291bGRCbG9ja05vdEFEaXJlY3RvcnlJc0FEaXJlY3RvcnlEaXJlY3RvcnlOb3RFbXB0eVJlYWRPbmx5RmlsZXN5c3RlbUZpbGVzeXN0ZW1Mb29wU3RhbGVOZXR3b3JrRmlsZUhhbmRsZUludmFsaWRJbnB1dEludmFsaWREYXRhVGltZWRPdXRXcml0ZVplcm9TdG9yYWdlRnVsbE5vdFNlZWthYmxlRmlsZXN5c3RlbVF1b3RhRXhjZWVkZWRGaWxlVG9vTGFyZ2VSZXNvdXJjZUJ1c3lFeGVjdXRhYmxlRmlsZUJ1c3lEZWFkbG9ja0Nyb3NzZXNEZXZpY2VzVG9vTWFueUxpbmtzSW52YWxpZEZpbGVuYW1lQXJndW1lbnRMaXN0VG9vTG9uZ0ludGVycnVwdGVkVW5leHBlY3RlZEVvZk91dE9mTWVtb3J5T3RoZXJVbmNhdGVnb3JpemVkb3BlcmF0aW9uIHN1Y2Nlc3NmdWwACAAAABAAAAARAAAADwAAAA8AAAASAAAAEQAAAAwAAAAJAAAAEAAAAAsAAAAKAAAADQAAAAoAAAANAAAADAAAABEAAAASAAAADgAAABYAAAAMAAAACwAAAAgAAAAJAAAACwAAAAsAAAAXAAAADAAAAAwAAAASAAAACAAAAA4AAAAMAAAADwAAABMAAAALAAAACwAAAA0AAAALAAAABQAAAA0AAACEKxAAjCsQAJwrEACtKxAAvCsQAMsrEADdKxAA7isQAPorEAADLBAAEywQAB4sEAAoLBAANSwQAD8sEABMLBAAWCwQAGksEAB7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AQAAKgEAACsBAAAsAQAALQEAAC4BAAAvAQAAMAEAAAAAQAAyAQAAMwEAADQBAAA1AQAANgEAADcBAAA5AQAAOgEAADsBAAA8AQAAPQEAAD4BAAA/AQAAQAEAAEEBAABCAQAAQwEAAEQBAABFAQAARgEAAEcBAABIAQAASgEAAEsBAABMAQAATQEAAE4BAABPAQAAUAEAAFEBAABSAQAAUwEAAFQBAABVAQAAVgEAAFcBAABYAQAAWQEAAFoBAABbAQAAXAEAAF0BAABeAQAAXwEAAGABAABhAQAAYgEAAGMBAABkAQAAZQEAAGYBAABnAQAAaAEAAGkBAABqAQAAawEAAGwBAABtAQAAbgEAAG8BAABwAQAAcQEAAHIBAABzAQAAdAEAAHUBAAB2AQAAdwEAAHgBAAD/AAAAeQEAAHoBAAB7AQAAfAEAAH0BAAB+AQAAgQEAAFMCAACCAQAAgwEAAIQBAACFAQAAhgEAAFQCAACHAQAAiAEAAIkBAABWAgAAigEAAFcCAACLAQAAjAEAAI4BAADdAQAAjwEAAFkCAACQAQAAWwIAAJEBAACSAQAAkwEAAGACAACUAQAAYwIAAJYBAABpAgAAlwEAAGgCAACYAQAAmQEAAJwBAABvAgAAnQEAAHICAACfAQAAdQIAAKABAAChAQAAogEAAKMBAACkAQAApQEAAKYBAACAAgAApwEAAKgBAACpAQAAgwIAAKwBAACtAQAArgEAAIgCAACvAQAAsAEAALEBAACKAgAAsgEAAIsCAACzAQAAtAEAALUBAAC2AQAAtwEAAJICAAC4AQAAuQEAALwBAAC9AQAAxAEAAMYBAADFAQAAxgEAAMcBAADJAQAAyAEAAMkBAADKAQAAzAEAAMsBAADMAQAAzQEAAM4BAADPAQAA0AEAANEBAADSAQAA0wEAANQBAADVAQAA1gEAANcBAADYAQAA2QEAANoBAADbAQAA3AEAAN4BAADfAQAA4AEAAOEBAADiAQAA4wEAAOQBAADlAQAA5gEAAOcBAADoAQAA6QEAAOoBAADrAQAA7AEAAO0BAADuAQAA7wEAAPEBAADzAQAA8gEAAPMBAAD0AQAA9QEAAPYBAACVAQAA9wEAAL8BAAD4AQAA+QEAAPoBAAD7AQAA/AEAAP0BAAD+AQAA/wEAAAACAAABAgAAAgIAAAMCAAAEAgAABQIAAAYCAAAHAgAACAIAAAkCAAAKAgAACwIAAAwCAAANAgAADgIAAA8CAAAQAgAAEQIAABICAAATAgAAFAIAABUCAAAWAgAAFwIAABgCAAAZAgAAGgIAABsCAAAcAgAAHQIAAB4CAAAfAgAAIAIAAJ4BAAAiAgAAIwIAACQCAAAlAgAAJgIAACcCAAAoAgAAKQIAACoCAAArAgAALAIAAC0CAAAuAgAALwIAADACAAAxAgAAMgIAADMCAAA6AgAAZSwAADsCAAA8AgAAPQIAAJoBAAA+AgAAZiwAAEECAABCAgAAQwIAAIABAABEAgAAiQIAAEUCAACMAgAARgIAAEcCAABIAgAASQIAAEoCAABLAgAATAIAAE0CAABOAgAATwIAAHADAABxAwAAcgMAAHMDAAB2AwAAdwMAAH8DAADzAwAAhgMAAKwDAACIAwAArQMAAIkDAACuAwAAigMAAK8DAACMAwAAzAMAAI4DAADNAwAAjwMAAM4DAACRAwAAsQMAAJIDAACyAwAAkwMAALMDAACUAwAAtAMAAJUDAAC1AwAAlgMAALYDAACXAwAAtwMAAJgDAAC4AwAAmQMAALkDAACaAwAAugMAAJsDAAC7AwAAnAMAALwDAACdAwAAvQMAAJ4DAAC+AwAAnwMAAL8DAACgAwAAwAMAAKEDAADBAwAAowMAAMMDAACkAwAAxAMAAKUDAADFAwAApgMAAMYDAACnAwAAxwMAAKgDAADIAwAAqQMAAMkDAACqAwAAygMAAKsDAADLAwAAzwMAANcDAADYAwAA2QMAANoDAADbAwAA3AMAAN0DAADeAwAA3wMAAOADAADhAwAA4gMAAOMDAADkAwAA5QMAAOYDAADnAwAA6AMAAOkDAADqAwAA6wMAAOwDAADtAwAA7gMAAO8DAAD0AwAAuAMAAPcDAAD4AwAA+QMAAPIDAAD6AwAA+wMAAP0DAAB7AwAA/gMAAHwDAAD/AwAAfQMAAAAEAABQBAAAAQQAAFEEAAACBAAAUgQAAAMEAABTBAAABAQAAFQEAAAFBAAAVQQAAAYEAABWBAAABwQAAFcEAAAIBAAAWAQAAAkEAABZBAAACgQAAFoEAAALBAAAWwQAAAwEAABcBAAADQQAAF0EAAAOBAAAXgQAAA8EAABfBAAAEAQAADAEAAARBAAAMQQAABIEAAAyBAAAEwQAADMEAAAUBAAANAQAABUEAAA1BAAAFgQAADYEAAAXBAAANwQAABgEAAA4BAAAGQQAADkEAAAaBAAAOgQAABsEAAA7BAAAHAQAADwEAAAdBAAAPQQAAB4EAAA+BAAAHwQAAD8EAAAgBAAAQAQAACEEAABBBAAAIgQAAEIEAAAjBAAAQwQAACQEAABEBAAAJQQAAEUEAAAmBAAARgQAACcEAABHBAAAKAQAAEgEAAApBAAASQQAACoEAABKBAAAKwQAAEsEAAAsBAAATAQAAC0EAABNBAAALgQAAE4EAAAvBAAATwQAAGAEAABhBAAAYgQAAGMEAABkBAAAZQQAAGYEAABnBAAAaAQAAGkEAABqBAAAawQAAGwEAABtBAAAbgQAAG8EAABwBAAAcQQAAHIEAABzBAAAdAQAAHUEAAB2BAAAdwQAAHgEAAB5BAAAegQAAHsEAAB8BAAAfQQAAH4EAAB/BAAAgAQAAIEEAACKBAAAiwQAAIwEAACNBAAAjgQAAI8EAACQBAAAkQQAAJIEAACTBAAAlAQAAJUEAACWBAAAlwQAAJgEAACZBAAAmgQAAJsEAACcBAAAnQQAAJ4EAACfBAAAoAQAAKEEAACiBAAAowQAAKQEAAClBAAApgQAAKcEAACoBAAAqQQAAKoEAACrBAAArAQAAK0EAACuBAAArwQAALAEAACxBAAAsgQAALMEAAC0BAAAtQQAALYEAAC3BAAAuAQAALkEAAC6BAAAuwQAALwEAAC9BAAAvgQAAL8EAADABAAAzwQAAMEEAADCBAAAwwQAAMQEAADFBAAAxgQAAMcEAADIBAAAyQQAAMoEAADLBAAAzAQAAM0EAADOBAAA0AQAANEEAADSBAAA0wQAANQEAADVBAAA1gQAANcEAADYBAAA2QQAANoEAADbBAAA3AQAAN0EAADeBAAA3wQAAOAEAADhBAAA4gQAAOMEAADkBAAA5QQAAOYEAADnBAAA6AQAAOkEAADqBAAA6wQAAOwEAADtBAAA7gQAAO8EAADwBAAA8QQAAPIEAADzBAAA9AQAAPUEAAD2BAAA9wQAAPgEAAD5BAAA+gQAAPsEAAD8BAAA/QQAAP4EAAD/BAAAAAUAAAEFAAACBQAAAwUAAAQFAAAFBQAABgUAAAcFAAAIBQAACQUAAAoFAAALBQAADAUAAA0FAAAOBQAADwUAABAFAAARBQAAEgUAABMFAAAUBQAAFQUAABYFAAAXBQAAGAUAABkFAAAaBQAAGwUAABwFAAAdBQAAHgUAAB8FAAAgBQAAIQUAACIFAAAjBQAAJAUAACUFAAAmBQAAJwUAACgFAAApBQAAKgUAACsFAAAsBQAALQUAAC4FAAAvBQAAMQUAAGEFAAAyBQAAYgUAADMFAABjBQAANAUAAGQFAAA1BQAAZQUAADYFAABmBQAANwUAAGcFAAA4BQAAaAUAADkFAABpBQAAOgUAAGoFAAA7BQAAawUAADwFAABsBQAAPQUAAG0FAAA+BQAAbgUAAD8FAABvBQAAQAUAAHAFAABBBQAAcQUAAEIFAAByBQAAQwUAAHMFAABEBQAAdAUAAEUFAAB1BQAARgUAAHYFAABHBQAAdwUAAEgFAAB4BQAASQUAAHkFAABKBQAAegUAAEsFAAB7BQAATAUAAHwFAABNBQAAfQUAAE4FAAB+BQAATwUAAH8FAABQBQAAgAUAAFEFAACBBQAAUgUAAIIFAABTBQAAgwUAAFQFAACEBQAAVQUAAIUFAABWBQAAhgUAAKAQAAAALQAAoRAAAAEtAACiEAAAAi0AAKMQAAADLQAApBAAAAQtAAClEAAABS0AAKYQAAAGLQAApxAAAActAACoEAAACC0AAKkQAAAJLQAAqhAAAAotAACrEAAACy0AAKwQAAAMLQAArRAAAA0tAACuEAAADi0AAK8QAAAPLQAAsBAAABAtAACxEAAAES0AALIQAAASLQAAsxAAABMtAAC0EAAAFC0AALUQAAAVLQAAthAAABYtAAC3EAAAFy0AALgQAAAYLQAAuRAAABktAAC6EAAAGi0AALsQAAAbLQAAvBAAABwtAAC9EAAAHS0AAL4QAAAeLQAAvxAAAB8tAADAEAAAIC0AAMEQAAAhLQAAwhAAACItAADDEAAAIy0AAMQQAAAkLQAAxRAAACUtAADHEAAAJy0AAM0QAAAtLQAAoBMAAHCrAAChEwAAcasAAKITAAByqwAAoxMAAHOrAACkEwAAdKsAAKUTAAB1qwAAphMAAHarAACnEwAAd6sAAKgTAAB4qwAAqRMAAHmrAACqEwAAeqsAAKsTAAB7qwAArBMAAHyrAACtEwAAfasAAK4TAAB+qwAArxMAAH+rAACwEwAAgKsAALETAACBqwAAshMAAIKrAACzEwAAg6sAALQTAACEqwAAtRMAAIWrAAC2EwAAhqsAALcTAACHqwAAuBMAAIirAAC5EwAAiasAALoTAACKqwAAuxMAAIurAAC8EwAAjKsAAL0TAACNqwAAvhMAAI6rAAC/EwAAj6sAAMATAACQqwAAwRMAAJGrAADCEwAAkqsAAMMTAACTqwAAxBMAAJSrAADFEwAAlasAAMYTAACWqwAAxxMAAJerAADIEwAAmKsAAMkTAACZqwAAyhMAAJqrAADLEwAAm6sAAMwTAACcqwAAzRMAAJ2rAADOEwAAnqsAAM8TAACfqwAA0BMAAKCrAADREwAAoasAANITAACiqwAA0xMAAKOrAADUEwAApKsAANUTAAClqwAA1hMAAKarAADXEwAAp6sAANgTAACoqwAA2RMAAKmrAADaEwAAqqsAANsTAACrqwAA3BMAAKyrAADdEwAArasAAN4TAACuqwAA3xMAAK+rAADgEwAAsKsAAOETAACxqwAA4hMAALKrAADjEwAAs6sAAOQTAAC0qwAA5RMAALWrAADmEwAAtqsAAOcTAAC3qwAA6BMAALirAADpEwAAuasAAOoTAAC6qwAA6xMAALurAADsEwAAvKsAAO0TAAC9qwAA7hMAAL6rAADvEwAAv6sAAPATAAD4EwAA8RMAAPkTAADyEwAA+hMAAPMTAAD7EwAA9BMAAPwTAAD1EwAA/RMAAJAcAADQEAAAkRwAANEQAACSHAAA0hAAAJMcAADTEAAAlBwAANQQAACVHAAA1RAAAJYcAADWEAAAlxwAANcQAACYHAAA2BAAAJkcAADZEAAAmhwAANoQAACbHAAA2xAAAJwcAADcEAAAnRwAAN0QAACeHAAA3hAAAJ8cAADfEAAAoBwAAOAQAAChHAAA4RAAAKIcAADiEAAAoxwAAOMQAACkHAAA5BAAAKUcAADlEAAAphwAAOYQAACnHAAA5xAAAKgcAADoEAAAqRwAAOkQAACqHAAA6hAAAKscAADrEAAArBwAAOwQAACtHAAA7RAAAK4cAADuEAAArxwAAO8QAACwHAAA8BAAALEcAADxEAAAshwAAPIQAACzHAAA8xAAALQcAAD0EAAAtRwAAPUQAAC2HAAA9hAAALccAAD3EAAAuBwAAPgQAAC5HAAA+RAAALocAAD6EAAAvRwAAP0QAAC+HAAA/hAAAL8cAAD/EAAAAB4AAAEeAAACHgAAAx4AAAQeAAAFHgAABh4AAAceAAAIHgAACR4AAAoeAAALHgAADB4AAA0eAAAOHgAADx4AABAeAAARHgAAEh4AABMeAAAUHgAAFR4AABYeAAAXHgAAGB4AABkeAAAaHgAAGx4AABweAAAdHgAAHh4AAB8eAAAgHgAAIR4AACIeAAAjHgAAJB4AACUeAAAmHgAAJx4AACgeAAApHgAAKh4AACseAAAsHgAALR4AAC4eAAAvHgAAMB4AADEeAAAyHgAAMx4AADQeAAA1HgAANh4AADceAAA4HgAAOR4AADoeAAA7HgAAPB4AAD0eAAA+HgAAPx4AAEAeAABBHgAAQh4AAEMeAABEHgAARR4AAEYeAABHHgAASB4AAEkeAABKHgAASx4AAEweAABNHgAATh4AAE8eAABQHgAAUR4AAFIeAABTHgAAVB4AAFUeAABWHgAAVx4AAFgeAABZHgAAWh4AAFseAABcHgAAXR4AAF4eAABfHgAAYB4AAGEeAABiHgAAYx4AAGQeAABlHgAAZh4AAGceAABoHgAAaR4AAGoeAABrHgAAbB4AAG0eAABuHgAAbx4AAHAeAABxHgAAch4AAHMeAAB0HgAAdR4AAHYeAAB3HgAAeB4AAHkeAAB6HgAAex4AAHweAAB9HgAAfh4AAH8eAACAHgAAgR4AAIIeAACDHgAAhB4AAIUeAACGHgAAhx4AAIgeAACJHgAAih4AAIseAACMHgAAjR4AAI4eAACPHgAAkB4AAJEeAACSHgAAkx4AAJQeAACVHgAAnh4AAN8AAACgHgAAoR4AAKIeAACjHgAApB4AAKUeAACmHgAApx4AAKgeAACpHgAAqh4AAKseAACsHgAArR4AAK4eAACvHgAAsB4AALEeAACyHgAAsx4AALQeAAC1HgAAth4AALceAAC4HgAAuR4AALoeAAC7HgAAvB4AAL0eAAC+HgAAvx4AAMAeAADBHgAAwh4AAMMeAADEHgAAxR4AAMYeAADHHgAAyB4AAMkeAADKHgAAyx4AAMweAADNHgAAzh4AAM8eAADQHgAA0R4AANIeAADTHgAA1B4AANUeAADWHgAA1x4AANgeAADZHgAA2h4AANseAADcHgAA3R4AAN4eAADfHgAA4B4AAOEeAADiHgAA4x4AAOQeAADlHgAA5h4AAOceAADoHgAA6R4AAOoeAADrHgAA7B4AAO0eAADuHgAA7x4AAPAeAADxHgAA8h4AAPMeAAD0HgAA9R4AAPYeAAD3HgAA+B4AAPkeAAD6HgAA+x4AAPweAAD9HgAA/h4AAP8eAAAIHwAAAB8AAAkfAAABHwAACh8AAAIfAAALHwAAAx8AAAwfAAAEHwAADR8AAAUfAAAOHwAABh8AAA8fAAAHHwAAGB8AABAfAAAZHwAAER8AABofAAASHwAAGx8AABMfAAAcHwAAFB8AAB0fAAAVHwAAKB8AACAfAAApHwAAIR8AACofAAAiHwAAKx8AACMfAAAsHwAAJB8AAC0fAAAlHwAALh8AACYfAAAvHwAAJx8AADgfAAAwHwAAOR8AADEfAAA6HwAAMh8AADsfAAAzHwAAPB8AADQfAAA9HwAANR8AAD4fAAA2HwAAPx8AADcfAABIHwAAQB8AAEkfAABBHwAASh8AAEIfAABLHwAAQx8AAEwfAABEHwAATR8AAEUfAABZHwAAUR8AAFsfAABTHwAAXR8AAFUfAABfHwAAVx8AAGgfAABgHwAAaR8AAGEfAABqHwAAYh8AAGsfAABjHwAAbB8AAGQfAABtHwAAZR8AAG4fAABmHwAAbx8AAGcfAACIHwAAgB8AAIkfAACBHwAAih8AAIIfAACLHwAAgx8AAIwfAACEHwAAjR8AAIUfAACOHwAAhh8AAI8fAACHHwAAmB8AAJAfAACZHwAAkR8AAJofAACSHwAAmx8AAJMfAACcHwAAlB8AAJ0fAACVHwAAnh8AAJYfAACfHwAAlx8AAKgfAACgHwAAqR8AAKEfAACqHwAAoh8AAKsfAACjHwAArB8AAKQfAACtHwAApR8AAK4fAACmHwAArx8AAKcfAAC4HwAAsB8AALkfAACxHwAAuh8AAHAfAAC7HwAAcR8AALwfAACzHwAAyB8AAHIfAADJHwAAcx8AAMofAAB0HwAAyx8AAHUfAADMHwAAwx8AANgfAADQHwAA2R8AANEfAADaHwAAdh8AANsfAAB3HwAA6B8AAOAfAADpHwAA4R8AAOofAAB6HwAA6x8AAHsfAADsHwAA5R8AAPgfAAB4HwAA+R8AAHkfAAD6HwAAfB8AAPsfAAB9HwAA/B8AAPMfAAAmIQAAyQMAACohAABrAAAAKyEAAOUAAAAyIQAATiEAAGAhAABwIQAAYSEAAHEhAABiIQAAciEAAGMhAABzIQAAZCEAAHQhAABlIQAAdSEAAGYhAAB2IQAAZyEAAHchAABoIQAAeCEAAGkhAAB5IQAAaiEAAHohAABrIQAAeyEAAGwhAAB8IQAAbSEAAH0hAABuIQAAfiEAAG8hAAB/IQAAgyEAAIQhAAC2JAAA0CQAALckAADRJAAAuCQAANIkAAC5JAAA0yQAALokAADUJAAAuyQAANUkAAC8JAAA1iQAAL0kAADXJAAAviQAANgkAAC/JAAA2SQAAMAkAADaJAAAwSQAANskAADCJAAA3CQAAMMkAADdJAAAxCQAAN4kAADFJAAA3yQAAMYkAADgJAAAxyQAAOEkAADIJAAA4iQAAMkkAADjJAAAyiQAAOQkAADLJAAA5SQAAMwkAADmJAAAzSQAAOckAADOJAAA6CQAAM8kAADpJAAAACwAADAsAAABLAAAMSwAAAIsAAAyLAAAAywAADMsAAAELAAANCwAAAUsAAA1LAAABiwAADYsAAAHLAAANywAAAgsAAA4LAAACSwAADksAAAKLAAAOiwAAAssAAA7LAAADCwAADwsAAANLAAAPSwAAA4sAAA+LAAADywAAD8sAAAQLAAAQCwAABEsAABBLAAAEiwAAEIsAAATLAAAQywAABQsAABELAAAFSwAAEUsAAAWLAAARiwAABcsAABHLAAAGCwAAEgsAAAZLAAASSwAABosAABKLAAAGywAAEssAAAcLAAATCwAAB0sAABNLAAAHiwAAE4sAAAfLAAATywAACAsAABQLAAAISwAAFEsAAAiLAAAUiwAACMsAABTLAAAJCwAAFQsAAAlLAAAVSwAACYsAABWLAAAJywAAFcsAAAoLAAAWCwAACksAABZLAAAKiwAAFosAAArLAAAWywAACwsAABcLAAALSwAAF0sAAAuLAAAXiwAAC8sAABfLAAAYCwAAGEsAABiLAAAawIAAGMsAAB9HQAAZCwAAH0CAABnLAAAaCwAAGksAABqLAAAaywAAGwsAABtLAAAUQIAAG4sAABxAgAAbywAAFACAABwLAAAUgIAAHIsAABzLAAAdSwAAHYsAAB+LAAAPwIAAH8sAABAAgAAgCwAAIEsAACCLAAAgywAAIQsAACFLAAAhiwAAIcsAACILAAAiSwAAIosAACLLAAAjCwAAI0sAACOLAAAjywAAJAsAACRLAAAkiwAAJMsAACULAAAlSwAAJYsAACXLAAAmCwAAJksAACaLAAAmywAAJwsAACdLAAAniwAAJ8sAACgLAAAoSwAAKIsAACjLAAApCwAAKUsAACmLAAApywAAKgsAACpLAAAqiwAAKssAACsLAAArSwAAK4sAACvLAAAsCwAALEsAACyLAAAsywAALQsAAC1LAAAtiwAALcsAAC4LAAAuSwAALosAAC7LAAAvCwAAL0sAAC+LAAAvywAAMAsAADBLAAAwiwAAMMsAADELAAAxSwAAMYsAADHLAAAyCwAAMksAADKLAAAyywAAMwsAADNLAAAziwAAM8sAADQLAAA0SwAANIsAADTLAAA1CwAANUsAADWLAAA1ywAANgsAADZLAAA2iwAANssAADcLAAA3SwAAN4sAADfLAAA4CwAAOEsAADiLAAA4ywAAOssAADsLAAA7SwAAO4sAADyLAAA8ywAAECmAABBpgAAQqYAAEOmAABEpgAARaYAAEamAABHpgAASKYAAEmmAABKpgAAS6YAAEymAABNpgAATqYAAE+mAABQpgAAUaYAAFKmAABTpgAAVKYAAFWmAABWpgAAV6YAAFimAABZpgAAWqYAAFumAABcpgAAXaYAAF6mAABfpgAAYKYAAGGmAABipgAAY6YAAGSmAABlpgAAZqYAAGemAABopgAAaaYAAGqmAABrpgAAbKYAAG2mAACApgAAgaYAAIKmAACDpgAAhKYAAIWmAACGpgAAh6YAAIimAACJpgAAiqYAAIumAACMpgAAjaYAAI6mAACPpgAAkKYAAJGmAACSpgAAk6YAAJSmAACVpgAAlqYAAJemAACYpgAAmaYAAJqmAACbpgAAIqcAACOnAAAkpwAAJacAACanAAAnpwAAKKcAACmnAAAqpwAAK6cAACynAAAtpwAALqcAAC+nAAAypwAAM6cAADSnAAA1pwAANqcAADenAAA4pwAAOacAADqnAAA7pwAAPKcAAD2nAAA+pwAAP6cAAECnAABBpwAAQqcAAEOnAABEpwAARacAAEanAABHpwAASKcAAEmnAABKpwAAS6cAAEynAABNpwAATqcAAE+nAABQpwAAUacAAFKnAABTpwAAVKcAAFWnAABWpwAAV6cAAFinAABZpwAAWqcAAFunAABcpwAAXacAAF6nAABfpwAAYKcAAGGnAABipwAAY6cAAGSnAABlpwAAZqcAAGenAABopwAAaacAAGqnAABrpwAAbKcAAG2nAABupwAAb6cAAHmnAAB6pwAAe6cAAHynAAB9pwAAeR0AAH6nAAB/pwAAgKcAAIGnAACCpwAAg6cAAISnAACFpwAAhqcAAIenAACLpwAAjKcAAI2nAABlAgAAkKcAAJGnAACSpwAAk6cAAJanAACXpwAAmKcAAJmnAACapwAAm6cAAJynAACdpwAAnqcAAJ+nAACgpwAAoacAAKKnAACjpwAApKcAAKWnAACmpwAAp6cAAKinAACppwAAqqcAAGYCAACrpwAAXAIAAKynAABhAgAAracAAGwCAACupwAAagIAALCnAACeAgAAsacAAIcCAACypwAAnQIAALOnAABTqwAAtKcAALWnAAC2pwAAt6cAALinAAC5pwAAuqcAALunAAC8pwAAvacAAL6nAAC/pwAAwKcAAMGnAADCpwAAw6cAAMSnAACUpwAAxacAAIICAADGpwAAjh0AAMenAADIpwAAyacAAMqnAADQpwAA0acAANanAADXpwAA2KcAANmnAAD1pwAA9qcAACH/AABB/wAAIv8AAEL/AAAj/wAAQ/8AACT/AABE/wAAJf8AAEX/AAAm/wAARv8AACf/AABH/wAAKP8AAEj/AAAp/wAASf8AACr/AABK/wAAK/8AAEv/AAAs/wAATP8AAC3/AABN/wAALv8AAE7/AAAv/wAAT/8AADD/AABQ/wAAMf8AAFH/AAAy/wAAUv8AADP/AABT/wAANP8AAFT/AAA1/wAAVf8AADb/AABW/wAAN/8AAFf/AAA4/wAAWP8AADn/AABZ/wAAOv8AAFr/AAAABAEAKAQBAAEEAQApBAEAAgQBACoEAQADBAEAKwQBAAQEAQAsBAEABQQBAC0EAQAGBAEALgQBAAcEAQAvBAEACAQBADAEAQAJBAEAMQQBAAoEAQAyBAEACwQBADMEAQAMBAEANAQBAA0EAQA1BAEADgQBADYEAQAPBAEANwQBABAEAQA4BAEAEQQBADkEAQASBAEAOgQBABMEAQA7BAEAFAQBADwEAQAVBAEAPQQBABYEAQA+BAEAFwQBAD8EAQAYBAEAQAQBABkEAQBBBAEAGgQBAEIEAQAbBAEAQwQBABwEAQBEBAEAHQQBAEUEAQAeBAEARgQBAB8EAQBHBAEAIAQBAEgEAQAhBAEASQQBACIEAQBKBAEAIwQBAEsEAQAkBAEATAQBACUEAQBNBAEAJgQBAE4EAQAnBAEATwQBALAEAQDYBAEAsQQBANkEAQCyBAEA2gQBALMEAQDbBAEAtAQBANwEAQC1BAEA3QQBALYEAQDeBAEAtwQBAN8EAQC4BAEA4AQBALkEAQDhBAEAugQBAOIEAQC7BAEA4wQBALwEAQDkBAEAvQQBAOUEAQC+BAEA5gQBAL8EAQDnBAEAwAQBAOgEAQDBBAEA6QQBAMIEAQDqBAEAwwQBAOsEAQDEBAEA7AQBAMUEAQDtBAEAxgQBAO4EAQDHBAEA7wQBAMgEAQDwBAEAyQQBAPEEAQDKBAEA8gQBAMsEAQDzBAEAzAQBAPQEAQDNBAEA9QQBAM4EAQD2BAEAzwQBAPcEAQDQBAEA+AQBANEEAQD5BAEA0gQBAPoEAQDTBAEA+wQBAHAFAQCXBQEAcQUBAJgFAQByBQEAmQUBAHMFAQCaBQEAdAUBAJsFAQB1BQEAnAUBAHYFAQCdBQEAdwUBAJ4FAQB4BQEAnwUBAHkFAQCgBQEAegUBAKEFAQB8BQEAowUBAH0FAQCkBQEAfgUBAKUFAQB/BQEApgUBAIAFAQCnBQEAgQUBAKgFAQCCBQEAqQUBAIMFAQCqBQEAhAUBAKsFAQCFBQEArAUBAIYFAQCtBQEAhwUBAK4FAQCIBQEArwUBAIkFAQCwBQEAigUBALEFAQCMBQEAswUBAI0FAQC0BQEAjgUBALUFAQCPBQEAtgUBAJAFAQC3BQEAkQUBALgFAQCSBQEAuQUBAJQFAQC7BQEAlQUBALwFAQCADAEAwAwBAIEMAQDBDAEAggwBAMIMAQCDDAEAwwwBAIQMAQDEDAEAhQwBAMUMAQCGDAEAxgwBAIcMAQDHDAEAiAwBAMgMAQCJDAEAyQwBAIoMAQDKDAEAiwwBAMsMAQCMDAEAzAwBAI0MAQDNDAEAjgwBAM4MAQCPDAEAzwwBAJAMAQDQDAEAkQwBANEMAQCSDAEA0gwBAJMMAQDTDAEAlAwBANQMAQCVDAEA1QwBAJYMAQDWDAEAlwwBANcMAQCYDAEA2AwBAJkMAQDZDAEAmgwBANoMAQCbDAEA2wwBAJwMAQDcDAEAnQwBAN0MAQCeDAEA3gwBAJ8MAQDfDAEAoAwBAOAMAQChDAEA4QwBAKIMAQDiDAEAowwBAOMMAQCkDAEA5AwBAKUMAQDlDAEApgwBAOYMAQCnDAEA5wwBAKgMAQDoDAEAqQwBAOkMAQCqDAEA6gwBAKsMAQDrDAEArAwBAOwMAQCtDAEA7QwBAK4MAQDuDAEArwwBAO8MAQCwDAEA8AwBALEMAQDxDAEAsgwBAPIMAQCgGAEAwBgBAKEYAQDBGAEAohgBAMIYAQCjGAEAwxgBAKQYAQDEGAEApRgBAMUYAQCmGAEAxhgBAKcYAQDHGAEAqBgBAMgYAQCpGAEAyRgBAKoYAQDKGAEAqxgBAMsYAQCsGAEAzBgBAK0YAQDNGAEArhgBAM4YAQCvGAEAzxgBALAYAQDQGAEAsRgBANEYAQCyGAEA0hgBALMYAQDTGAEAtBgBANQYAQC1GAEA1RgBALYYAQDWGAEAtxgBANcYAQC4GAEA2BgBALkYAQDZGAEAuhgBANoYAQC7GAEA2xgBALwYAQDcGAEAvRgBAN0YAQC+GAEA3hgBAL8YAQDfGAEAQG4BAGBuAQBBbgEAYW4BAEJuAQBibgEAQ24BAGNuAQBEbgEAZG4BAEVuAQBlbgEARm4BAGZuAQBHbgEAZ24BAEhuAQBobgEASW4BAGluAQBKbgEAam4BAEtuAQBrbgEATG4BAGxuAQBNbgEAbW4BAE5uAQBubgEAT24BAG9uAQBQbgEAcG4BAFFuAQBxbgEAUm4BAHJuAQBTbgEAc24BAFRuAQB0bgEAVW4BAHVuAQBWbgEAdm4BAFduAQB3bgEAWG4BAHhuAQBZbgEAeW4BAFpuAQB6bgEAW24BAHtuAQBcbgEAfG4BAF1uAQB9bgEAXm4BAH5uAQBfbgEAf24BAADpAQAi6QEAAekBACPpAQAC6QEAJOkBAAPpAQAl6QEABOkBACbpAQAF6QEAJ+kBAAbpAQAo6QEAB+kBACnpAQAI6QEAKukBAAnpAQAr6QEACukBACzpAQAL6QEALekBAAzpAQAu6QEADekBAC/pAQAO6QEAMOkBAA/pAQAx6QEAEOkBADLpAQAR6QEAM+kBABLpAQA06QEAE+kBADXpAQAU6QEANukBABXpAQA36QEAFukBADjpAQAX6QEAOekBABjpAQA66QEAGekBADvpAQAa6QEAPOkBABvpAQA96QEAHOkBAD7pAQAd6QEAP+kBAB7pAQBA6QEAH+kBAEHpAQAg6QEAQukBACHpAQBD6QEAQejjwQALOQIAAABTAAAAaQAAAAIAAAAAAAAAagAAAAIAAAAAAAAAawAAAAIAAAAAAAAAbAAAAAIAAAAAAAAAbQBBvOTBAAsBbwBwCXByb2R1Y2VycwIIbGFuZ3VhZ2UBBFJ1c3QADHByb2Nlc3NlZC1ieQMFcnVzdGMdMS43My4wIChjYzY2YWQ0NjggMjAyMy0xMC0wMykGd2FscnVzBjAuMjMuMwx3YXNtLWJpbmRnZW4HMC4yLjEwMAAsD3RhcmdldF9mZWF0dXJlcwIrD211dGFibGUtZ2xvYmFscysIc2lnbi1leHQ=';
    const EBJ_GLUE_BYTES = 11072;
    const EBJ_GLUE_SUM = 'b3af6137';

    /** FNV-1a, 32-bit, over UTF-16 code units. Mirrored by the extraction tooling. */
    function ebjGlueChecksum(str) {
        let h = 0x811c9dc5;
        for (let i = 0; i < str.length; i++) {
            h ^= str.charCodeAt(i);
            h = (h + ((h << 1) + (h << 4) + (h << 7) + (h << 8) + (h << 24))) >>> 0;
        }
        return ('0000000' + h.toString(16)).slice(-8);
    }

    /** base64 -> Uint8Array, without a multi-megabyte intermediate string. */
    function ebjB64ToBytes(b64) {
        const bin = atob(b64);
        const out = new Uint8Array(bin.length);
        for (let i = 0; i < bin.length; i++) out[i] = bin.charCodeAt(i);
        return out;
    }

    // The page may have replaced the global Function as an anti-scraping
    // measure. Keep a reference to the intrinsic so the glue can still be
    // compiled, and fall back to an iframe realm if even that is gone.
    const ebjIntrinsicFunction = (function () {
        try {
            const F = Function;
            if (new F('return 1')() === 1) return F;
        } catch (e) {}
        return null;
    })();

    function ebjHonestFunction() {
        if (ebjIntrinsicFunction) return ebjIntrinsicFunction;
        try {
            const frame = document.createElement('iframe');
            frame.style.display = 'none';
            (document.body || document.documentElement).appendChild(frame);
            const F = frame.contentWindow.Function;
            frame.remove();
            if (new F('return 1')() === 1) return F;
        } catch (e) {}
        return null;
    }

    // One module per run: decrypt_session is single-shot and a second call
    // traps, and after the first shuffle even read-only calls trap, so the
    // core is built fresh for each run and rebuilt when a shape has to change.
    let ebjCore = null;

    function ebjResetCore() { ebjCore = null; }

    /**
     * Compile the pinned glue and instantiate the wasm module.
     * Resolves to the module's exports ({ default, decrypt_session, open_param,
     * get_page_name, shuffle, ... }).
     */
    async function ebjLoadGlue() {
        if (ebjCore) return ebjCore;
        let src;
        try {
            src = atob(EBJ_GLUE_B64);
        } catch (e) {
            throw new Error('the embedded ebookjapan glue is not valid base64 — this copy of ' +
                'the userscript is damaged; reinstall it');
        }
        const sum = ebjGlueChecksum(src);
        if (src.length !== EBJ_GLUE_BYTES || sum !== EBJ_GLUE_SUM) {
            throw new Error('the embedded ebookjapan glue does not match this script\'s ' +
                'pinned copy (expected ' + EBJ_GLUE_BYTES + ' bytes / ' + EBJ_GLUE_SUM +
                ', got ' + src.length + ' / ' + sum + '). Most often ebookjapan has ' +
                'redeployed its viewer and the pins need refreshing; otherwise this copy ' +
                'of the script is damaged.');
        }
        const Fn = ebjHonestFunction();
        if (!Fn) {
            throw new Error('this page has replaced Function, so the ebookjapan wasm core ' +
                'cannot be compiled — please report this page');
        }
        let factory;
        try {
            factory = new Fn(src);
        } catch (e) {
            throw new Error('the embedded ebookjapan glue did not compile: ' + ((e && e.message) || e));
        }
        let mod;
        try {
            mod = factory();
        } catch (e) {
            throw new Error('the embedded ebookjapan glue did not initialise: ' + ((e && e.message) || e));
        }
        if (!mod || typeof mod.default !== 'function') {
            throw new Error('the embedded ebookjapan glue returned nothing usable — this copy ' +
                'of the script is damaged or the site has changed its module shape');
        }
        const wasmBytes = ebjB64ToBytes(EBJ_WASM_B64);
        await mod.default({ module_or_path: wasmBytes });
        ebjCore = mod;
        return ebjCore;
    }
    // =====================================================================
    // ebookjapan — canvas realms, the portable encoder, and the descrambler
    // =====================================================================
    // Ported from the standalone script, where every part of this was forced by
    // a real failure rather than chosen:
    //
    //   * The wasm draws with drawImage, and those draws only land on a canvas
    //     from the PAGE's realm — which is why makeCanvas() builds there. The
    //     viewer's own canvases being page-realm is the proof.
    //   * That page deletes getImageData/toBlob/convertToBlob from its own
    //     prototypes, so pixels are read and images encoded through a hidden
    //     about:blank iframe with untouched prototypes. WebIDL brand checks are
    //     per-interface, not per-realm, so its methods read a page-realm canvas.
    //   * If no canvas encoder exists in any realm, pngFromRgba writes the PNG.
    //   * canvasStats() reads pixels so "the shuffle ran" is never mistaken for
    //     "the page painted": a shape that traps nothing and paints nothing is
    //     exactly how a whole book of identical black pages once shipped. The
    //     run's canary refuses to adopt any shape whose first page fails it.
    //   * The wasm module is single-shot, and its autograph argument must be a
    //     loaded <img> for its page and `undefined` everywhere else — never
    //     null, or it unwraps a None and traps at src/book.rs:910:17.
    //
    // Only the functions this fragment owns are defined here: anything else it
    // calls (crc32Bytes, fmtBytes, safeLogText, ...) comes from the shared core,
    // because two definitions of one name in a single closure would shadow it.
    const ebjShuffleUnwraps = {
        '0x1653b': 'src/book.rs:856:17',
        '0x170b5': 'src/book.rs:717:14',
        '0x1723b': 'src/book.rs:892:17',
        '0x17454': 'src/book.rs:910:17',
    };

    const ebjShape = { canvas: 'auto', image: 'img' };
    let ebjLastDecodePath = '';
    let ebjEncodePath = '';
    let ebjLastShuffleTrace = null;
    let ebjTraceNextShuffle = false;
    let ebjProbeOnce = true;
    let ebjAutographImg = null;
    let ebjSimulatedTraps = 0;
    let ebjFrameRealmSlot = null;

    /** Debug-gated log, matching the core's quiet-by-default posture. */
    function ebjLog(kind, text) {
        try {
            if (typeof BWDD_DEBUG !== 'undefined' && BWDD_DEBUG) {
                console.info('[bwdd/ebookjapan] ' + kind + ' ' + text);
            }
        } catch (e) {}
    }

    function autographSpec(drm) {
        const a = drm && drm.autographed;
        if (!a || !a.img) return null;
        return {
            page: parseInt(a.page || '0', 10) || 0,
            type: a.content_type || 'image/png',
            image: a.img,
        };
    }

    async function loadAutographImage(spec) {
        if (ebjAutographImg) return ebjAutographImg;
        const img = document.createElement('img');
        await new Promise((ok, no) => {
            img.onload = () => ok();
            img.onerror = () => no(new Error('the autograph overlay image would not load'));
            img.src = `data:${spec.type};base64,${spec.image}`;
        });
        ebjAutographImg = img;
        return img;
    }

    function wasmFrame(e) {
        const st = String((e && e.stack) || '');
        const hits = [...st.matchAll(/wasm-function\[(\d+)\]:(0x[0-9a-f]+)/gi)].slice(0, 5);
        if (!hits.length) return '';
        const parts = hits.map(m => {
            const off = parseInt(m[2], 16);
            let where = null;
            // Chrome reports either the instruction or its return address.
            for (let d = 0; d <= 4 && !where; d++) {
                where = ebjShuffleUnwraps['0x' + (off - d).toString(16)] || null;
            }
            return `function[${m[1]}]` + (where ? ` (${where})` : '');
        });
        return ', wasm trap at ' + parts.join(' <- ');
    }

    function magic(buf) {
        let s = '';
        const n = Math.min(16, buf ? buf.byteLength : 0);
        const b = new Uint8Array(buf || new ArrayBuffer(0), 0, n);
        for (let i = 0; i < b.length; i++) s += (b[i] >= 32 && b[i] < 127) ? String.fromCharCode(b[i]) : '.';
        return s;
    }

    function bytesToBase64(bytes) {
        let s = '';
        const CHUNK = 0x8000;
        for (let i = 0; i < bytes.length; i += CHUNK) {
            s += String.fromCharCode.apply(null, bytes.subarray(i, i + CHUNK));
        }
        return btoa(s);
    }

    async function decodeImage(buf, { asImage = null } = {}) {
        const wantImg = asImage ? asImage === 'img' : ebjShape.image === 'img';
        const blob = new Blob([buf], { type: 'image/webp' });
        // createImageBitmap() is the fast path, and it decodes from memory, so
        // the page's `img-src` cannot stop it. The bare name can still be
        // missing inside a userscript sandbox even when the page has it, so ask
        // every root before giving up on it.
        const roots = [typeof createImageBitmap === 'function' ? createImageBitmap : null,
            (typeof window !== 'undefined' && window && typeof window.createImageBitmap === 'function')
                ? window.createImageBitmap : null,
            (typeof globalThis !== 'undefined' && globalThis &&
                typeof globalThis.createImageBitmap === 'function') ? globalThis.createImageBitmap : null];
        const cib = wantImg ? null : roots.find(Boolean);
        if (cib) {
            try {
                const bitmap = await cib.call(null, blob);
                try {
                    // Some callers look for the <img> spelling of the size.
                    bitmap.naturalWidth = bitmap.width;
                    bitmap.naturalHeight = bitmap.height;
                } catch (e) { /* expando refused */ }
                ebjLastDecodePath = 'createImageBitmap';
                return bitmap;
            } catch (e) {
                ebjLastDecodePath = 'createImageBitmap threw: ' + ((e && e.message) || e);
            }
        }
        // Fallback for engines without createImageBitmap (or a WebP variant it
        // refuses): decode an <img> from the bytes. This used a blob: URL, which
        // on ebookjapan can never work — the viewer's CSP is
        // `img-src 'self' https: data:` with no blob:, so the load is blocked
        // before it starts. A data: URL is allowed, so the bytes go in as base64.
        ebjLastDecodePath = 'data: URL';
        const url = `data:image/webp;base64,${bytesToBase64(new Uint8Array(buf))}`;
        try {
            const img = new Image();
            img.decoding = 'sync';
            await new Promise((res, rej) => {
                img.onload = () => res();
                img.onerror = () => rej(new Error('the browser refused to decode these bytes'));
                img.src = url;
            });
            if (typeof img.decode === 'function') { try { await img.decode(); } catch (e) {} }
            return img;
        } catch (e) {
            throw new Error(`decode failed after ${ebjLastDecodePath}: ${(e && e.message) || e} ` +
                `(${buf.byteLength} bytes, magic "${magic(buf)}")`);
        }
    }

    function ebjPageDoc() { return (ebjPage && ebjPage.document) || document; }

    /**
     * The page deletes toBlob/toDataURL/convertToBlob/getImageData from its own
     * canvas prototypes (a tainted canvas would still *have* them and throw, so
     * deletion is what the console shows). An about:blank iframe is a fresh
     * realm with its own untouched prototypes, and a method from there works on
     * our canvas: WebIDL brand checks are per-interface, not per-realm.
     */
    function frameRealm() {
        if (ebjFrameRealmSlot !== undefined) return ebjFrameRealmSlot;
        ebjFrameRealmSlot = null;
        let frame = null;
        try {
            const host = ebjPageDoc();
            frame = host.createElement('iframe');
            frame.setAttribute('aria-hidden', 'true');
            frame.style.cssText = 'display:none!important;width:0;height:0;border:0';
            (host.body || host.documentElement).appendChild(frame);
            const w = frame.contentWindow;
            if (w && w.document && w.HTMLCanvasElement && w.CanvasRenderingContext2D) {
                const probe = w.document.createElement('canvas');
                probe.width = probe.height = 1;
                const ctx = probe.getContext('2d');
                if (ctx && typeof ctx.getImageData === 'function') {
                    ebjFrameRealmSlot = w;
                    ebjLog('wasm', 'found a clean canvas realm in a blank iframe ' +
                        '(the page deleted the encoders from its own)');
                }
            }
        } catch (e) { ebjLog('wasm', `no spare canvas realm: ${(e && e.message) || e}`); }
        if (!ebjFrameRealmSlot && frame && frame.parentNode) {
            frame.parentNode.removeChild(frame);
        }
        return ebjFrameRealmSlot;
    }

    function frameRealm() {
        if (ebjFrameRealmSlot !== undefined) return ebjFrameRealmSlot;
        ebjFrameRealmSlot = null;
        let frame = null;
        try {
            const host = ebjPageDoc();
            frame = host.createElement('iframe');
            frame.setAttribute('aria-hidden', 'true');
            frame.style.cssText = 'display:none!important;width:0;height:0;border:0';
            (host.body || host.documentElement).appendChild(frame);
            const w = frame.contentWindow;
            if (w && w.document && w.HTMLCanvasElement && w.CanvasRenderingContext2D) {
                const probe = w.document.createElement('canvas');
                probe.width = probe.height = 1;
                const ctx = probe.getContext('2d');
                if (ctx && typeof ctx.getImageData === 'function') {
                    ebjFrameRealmSlot = w;
                    ebjLog('wasm', 'found a clean canvas realm in a blank iframe ' +
                        '(the page deleted the encoders from its own)');
                }
            }
        } catch (e) { ebjLog('wasm', `no spare canvas realm: ${(e && e.message) || e}`); }
        if (!ebjFrameRealmSlot && frame && frame.parentNode) {
            frame.parentNode.removeChild(frame);
        }
        return ebjFrameRealmSlot;
    }

    function realms() {
        const out = [];
        const push = w => { if (w && out.indexOf(w) === -1) out.push(w); };
        push(frameRealm());
        push(ebjPage);
        try { push(typeof window !== 'undefined' ? window : null); } catch (e) {}
        return out;
    }

    function makeCanvas(w, h, kind = null) {
        const want = kind || ebjShape.canvas;
        // The canvas has to come from the page's realm: that is where the wasm's
        // drawImage actually lands (the viewer's own canvases are proof). The
        // spare realm is only used to *read* pixels back, because the page has
        // deleted getImageData/toBlob from its own prototypes.
        const Off = (ebjPage && ebjPage.OffscreenCanvas) ||
            (typeof OffscreenCanvas === 'function' ? OffscreenCanvas : null);
        if (want !== 'html' && Off) {
            try { return new Off(w, h); } catch (e) { /* fall back */ }
        }
        const doc = (ebjPage && ebjPage.document) || document;
        const c = doc.createElement('canvas');
        c.width = w;
        c.height = h;
        return c;
    }

    function tracedCtx(ctx, sink) {
        return new Proxy(ctx, {
            get(t, k) {
                const v = Reflect.get(t, k);
                if (sink.length < 60) {
                    sink.push(typeof k === 'string' ? k : String(k));
                }
                if (typeof v === 'function') {
                    const bound = v.bind(t);
                    return (...args) => {
                        if (sink.length < 60) sink.push(`${String(k)}(${args.length} args)`);
                        return bound(...args);
                    };
                }
                return v;
            },
        });
    }

    async function canvasStats(canvas) {
        try {
            const px = await rgbaFromCanvas(canvas);
            if (!px) return null;
            const d = px.data;
            const step = Math.max(4, Math.floor(d.length / 4000 / 4) * 4);
            let sum = 0, n = 0, black = 0;
            for (let i = 0; i + 3 < d.length; i += step) {
                const v = (d[i] + d[i + 1] + d[i + 2]) / 3;
                sum += v; n++;
                if (v < 8) black++;
            }
            return { mean: sum / Math.max(1, n), black: black / Math.max(1, n), samples: n, via: px.via };
        } catch (e) { return { error: (e && e.message) || String(e) }; }
    }

    function statsText(st) {
        if (!st) return 'pixels unreadable';
        if (st.error) return `pixels unreadable (${st.error})`;
        return `mean ${st.mean.toFixed(1)}/255, ${(100 * st.black).toFixed(0)}% black, ${st.samples} samples via ${st.via}`;
    }

    function imageReport(img) {
        if (!img) return 'no image';
        const src = img.src;
        return `${img.tagName || (img.constructor && img.constructor.name) || typeof img} ` +
            `width=${img.width} height=${img.height} ` +
            `natural=${img.naturalWidth}x${img.naturalHeight} ` +
            `complete=${img.complete} ` +
            `src=${typeof src === 'string' ? `${typeof src}:${src.length}` : String(src)}`;
    }

    async function descramblePage(glue, bitmap, row, geo,
                                  { codec = IMAGE_CODEC, canvasKind = null, autographed = undefined } = {}) {
        if (ebjSimulatedTraps > 0) {
            ebjSimulatedTraps--;
            const trap = new Error('unreachable');
            trap.name = 'RuntimeError';
            trap.stack = 'RuntimeError: unreachable\n    at wasm://wasm/000914c2:wasm-function[139]:0x137f5\n' +
                '    at wasm://wasm/000914c2:wasm-function[213]:0x175f7';
            throw trap;
        }
        const canvas = makeCanvas(geo.width, geo.height, canvasKind);
        const ctx = canvas.getContext('2d', { alpha: true, willReadFrequently: false });
        if (!ctx) throw new Error('no 2d canvas context');
        ctx.clearRect(0, 0, geo.width, geo.height);

        // The wasm only ever reads ctx.canvas.{width,height} and calls
        // ctx.drawImage(image, sx, sy, sw, sh, dx, dy) — the destination offsets
        // come from the page's own geometry, which is why the canvas must be the
        // book's intrinsic size rather than the page's display box.
        // Control mark: if our own fill is gone after the shuffle, we are reading a
        // different surface than the wasm painted on; if it survives while the rest
        // is black, the wasm genuinely painted nothing.
        const probing = ebjProbeOnce;
        if (probing) {
            ebjProbeOnce = false;
            try {
                ctx.fillStyle = '#ff0000';
                ctx.fillRect(0, 0, 24, 24);
            } catch (e) { ebjLog('wasm', `control fill failed: ${(e && e.message) || e}`); }
        }

        // The first shuffle of a run is traced: a trap that happens before the
        // wasm has asked for a single tile is a state failure, and one after
        // dozens of drawImage calls is a geometry failure. The two need
        // completely different fixes, and the trap itself says neither.
        let ctxForShuffle = ctx;
        if (ebjTraceNextShuffle) {
            ebjTraceNextShuffle = false;
            ebjLastShuffleTrace = [];
            ebjLog('wasm', 'tracing canvas calls for the first page of this shape');
            ctxForShuffle = tracedCtx(ctx, ebjLastShuffleTrace);
        }
        glue.shuffle({ ctx: ctxForShuffle, x: 0, y: 0, data: { image: bitmap },
            autographed, page: row.page });

        // Trim the transparent padding the tile grid leaves past the page box so
        // small pages do not ship as mostly-empty full-intrinsic canvases.
        const w = row.width || geo.width;
        const h = row.height || geo.height;
        let out = canvas;
        let outW = geo.width, outH = geo.height;
        if (w !== geo.width || h !== geo.height) {
            const cropped = makeCanvas(w, h, canvasKind);
            const cctx = cropped.getContext('2d');
            if (!cctx) throw new Error('no 2d canvas context');
            cctx.drawImage(canvas, 0, 0);
            out = cropped;
            outW = w;
            outH = h;
        }

        if (probing) {
            let mark = 'unreadable';
            try {
                const px = await rgbaFromCanvas(out);
                mark = px && px.data.length >= 4
                    ? `${px.data[0]},${px.data[1]},${px.data[2]} (want 255,0,0)`
                    : 'short buffer';
            } catch (e) { mark = (e && e.message) || String(e); }
            const cname = (canvas.constructor && canvas.constructor.name) || typeof canvas;
            ebjLog('wasm', `probe: our control fill at 0,0 = ${mark} | ` +
                `canvas ${cname} ${canvas.width}x${canvas.height} option=${canvasKind || ebjShape.canvas} ` +
                `pageRealm=${ebjPage ? 'yes' : 'no'} spareRealm=${frameRealm() ? 'yes' : 'no'} | ` +
                `image ${imageReport(bitmap)}`);
        }
        const stats = await canvasStats(out);
        const blob = await canvasToBlob(out, codec);
        if (bitmap && typeof bitmap.close === 'function') { try { bitmap.close(); } catch (e) {} }
        const buf = new Uint8Array(await blob.arrayBuffer());
        // An encoder may quietly hand back PNG when asked for something it will
        // not produce, so the blob's own type decides the extension.
        const mime = blob.type || codec.mime;
        const ext = { 'image/png': 'png', 'image/jpeg': 'jpg', 'image/webp': 'webp' }[mime] || codec.ext;
        return { blob, width: outW, height: outH, ext, mime, stats,
                 crc: crc32Bytes(buf), bytes: buf.byteLength };
    }

    async function deflateBytes(bytes) {
        const cs = new CompressionStream('deflate');
        const w = cs.writable.getWriter();
        w.write(bytes);
        w.close();
        return new Uint8Array(await new Response(cs.readable).arrayBuffer());
    }

    function pngChunk(type, data) {
        const out = new Uint8Array(12 + data.length);
        const dv = new DataView(out.buffer);
        dv.setUint32(0, data.length);
        for (let i = 0; i < 4; i++) out[4 + i] = type.charCodeAt(i);
        out.set(data, 8);
        dv.setUint32(8 + data.length, crc32Bytes(out.subarray(4, 8 + data.length)));
        return out;
    }

    async function pngFromRgba(width, height, rgba) {
        const stride = width * 4;
        const raw = new Uint8Array(height * (stride + 1));
        for (let y = 0; y < height; y++) {
            raw[y * (stride + 1)] = 0;                       // filter: none
            raw.set(rgba.subarray(y * stride, (y + 1) * stride), y * (stride + 1) + 1);
        }
        const ihdr = new Uint8Array(13);
        const dv = new DataView(ihdr.buffer);
        dv.setUint32(0, width);
        dv.setUint32(4, height);
        ihdr[8] = 8;    // bit depth
        ihdr[9] = 6;    // colour type: RGBA
        const sig = new Uint8Array([0x89, 0x50, 0x4e, 0x47, 0x0d, 0x0a, 0x1a, 0x0a]);
        return new Blob([sig, pngChunk('IHDR', ihdr), pngChunk('IDAT', await deflateBytes(raw)),
            pngChunk('IEND', new Uint8Array(0))], { type: 'image/png' });
    }

    async function rgbaFromCanvas(canvas) {
        const notes = [];
        try {
            const ctx = canvas.getContext('2d');
            let get = ctx && ctx.getImageData;
            for (const w of realms()) {
                if (get) break;
                const P = w && w.CanvasRenderingContext2D && w.CanvasRenderingContext2D.prototype;
                if (P && typeof P.getImageData === 'function') get = P.getImageData;
            }
            if (get) {
                const d = get.call(ctx, 0, 0, canvas.width, canvas.height);
                if (d && d.data && d.data.length >= canvas.width * canvas.height * 4) {
                    return { width: canvas.width, height: canvas.height, data: d.data, via: 'getImageData', notes };
                }
                notes.push('getImageData: short buffer');
            } else {
                notes.push('getImageData: hidden');
            }
        } catch (e) { notes.push(`getImageData: ${(e && e.message) || e}`); }
        if (typeof VideoFrame === 'function') {
            try {
                const frame = new VideoFrame(canvas, { timestamp: 0 });
                const w = frame.displayWidth, h = frame.displayHeight;
                const buf = new Uint8Array(frame.allocationSize({ format: 'RGBA' }));
                await frame.copyTo(buf, { format: 'RGBA' });
                frame.close();
                if (buf.length >= w * h * 4) {
                    return { width: w, height: h, data: buf, via: 'VideoFrame.copyTo', notes };
                }
                notes.push('VideoFrame: short buffer');
            } catch (e) { notes.push(`VideoFrame: ${(e && e.message) || e}`); }
        } else {
            notes.push('VideoFrame: missing');
        }
        return null;
    }

    function encodeReport(canvas, notes) {
        const kind = (canvas && canvas.constructor && canvas.constructor.name) || typeof canvas;
        const has = (o, k) => (o && typeof o[k] === 'function' ? 'yes' : 'no');
        const proto = canvas && Object.getPrototypeOf(canvas);
        return `${kind} ${canvas && canvas.width}x${canvas && canvas.height} | ` +
            `own{convertToBlob:${has(canvas, 'convertToBlob')},toBlob:${has(canvas, 'toBlob')},` +
            `toDataURL:${has(canvas, 'toDataURL')},getImageData:${has(canvas, 'getImageData')}} | ` +
            `ctxGetImageData:${(() => { try { const c = canvas.getContext('2d'); return c && typeof c.getImageData === 'function' ? 'yes' : 'no'; } catch (e) { return 'throws'; } })()} | ` +
            `VideoFrame:${typeof VideoFrame === 'function' ? 'yes' : 'no'} | ` +
            `CompressionStream:${typeof CompressionStream === 'function' ? 'yes' : 'no'} | ` +
            `transferToImageBitmap:${has(canvas, 'transferToImageBitmap')} | ` +
            `pageRealm:${ebjPage ? 'yes' : 'no'} | ` +
            `proto{convertToBlob:${has(proto, 'convertToBlob')},toBlob:${has(proto, 'toBlob')},` +
            `toDataURL:${has(proto, 'toDataURL')}}` +
            (notes.length ? ' | ' + notes.join(' | ') : '');
    }

    function blobFromDataUrl(url, fallbackMime) {
        const comma = url.indexOf(',');
        const bin = atob(url.slice(comma + 1));
        const bytes = new Uint8Array(bin.length);
        for (let i = 0; i < bin.length; i++) bytes[i] = bin.charCodeAt(i);
        const mime = (url.slice(0, comma).match(/^data:([^;,]+)/) || [])[1] || fallbackMime;
        return new Blob([bytes], { type: mime });
    }

    function canvasToBlob(canvas, codec = IMAGE_CODEC) {
        const q = codec.qualityValue;
        return new Promise((resolve, reject) => {
            const notes = [];
            // A sandbox may strip the encoder off the object it hands over; the
            // page realm still carries it on the prototype, so call that instead.
            const from = name => {
                if (canvas && typeof canvas[name] === 'function') return canvas[name].bind(canvas);
                for (const w of realms()) {
                    if (!w) continue;
                    for (const C of [w.OffscreenCanvas, w.HTMLCanvasElement]) {
                        if (!C || !C.prototype || typeof C.prototype[name] !== 'function') continue;
                        try { if (canvas instanceof C) return C.prototype[name].bind(canvas); }
                        catch (e) { /* cross-realm instanceof can refuse */ }
                    }
                }
                return null;
            };
            const enc = {
                convertToBlob: from('convertToBlob'),
                toBlob: from('toBlob'),
                toDataURL: from('toDataURL'),
            };
            const notPassed = m => { notes.push(m); lastResort(); };
            const fromPng = () => enc.convertToBlob({ type: 'image/png' }).then(
                b => { ebjEncodePath = 'convertToBlob(png)'; resolve(b); },
                e => notPassed(`convertToBlob(png): ${(e && e.message) || e}`));

            let pxNotes = [];
            function lastResort() {
                // toDataURL is the encoder a patched page usually leaves alone.
                if (enc.toDataURL) {
                    try {
                        const url = enc.toDataURL(codec.mime, q);
                        if (url && url.indexOf('data:') === 0) {
                            const blob = blobFromDataUrl(url, codec.mime);
                            ebjEncodePath = 'toDataURL(' + blob.type + ')';
                            resolve(blob);
                            return;
                        }
                        notes.push('toDataURL: not a data URL');
                    } catch (e) { notes.push(`toDataURL threw: ${(e && e.message) || e}`); }
                } else {
                    notes.push('toDataURL: not a function');
                }
                rgbaFromCanvas(canvas).then(px => {
                    if (!px) {
                        reject(new Error('no canvas encoder worked \u2014 ' +
                            encodeReport(canvas, notes.concat(pxNotes))));
                        return;
                    }
                    return pngFromRgba(px.width, px.height, px.data).then(blob => {
                        ebjEncodePath = `rgba->png via ${px.via}`;
                        resolve(blob);
                    });
                }, e => reject(new Error('no canvas encoder worked \u2014 ' +
                    encodeReport(canvas, notes.concat([String((e && e.message) || e)])))));
            }

            if (enc.convertToBlob) {
                enc.convertToBlob({ type: codec.mime, quality: q }).then(
                    b => { ebjEncodePath = 'convertToBlob'; resolve(b); },
                    e => {
                        notes.push(`convertToBlob(${codec.mime}): ${(e && e.message) || e}`);
                        fromPng();
                    });
                return;
            }
            if (enc.toBlob) {
                try {
                    enc.toBlob(b => {
                        if (b) { ebjEncodePath = 'toBlob'; resolve(b); }
                        else notPassed('toBlob: null (tainted or refused)');
                    }, codec.mime, q);
                    return;
                } catch (e) { notes.push(`toBlob threw: ${(e && e.message) || e}`); }
            } else {
                notes.push('toBlob: not a function');
            }
            lastResort();
        });
    }

    function asArrayBuffer(v) {
        if (!v) return null;
        if (typeof v.byteLength === 'number' && typeof v.slice === 'function') {
            // ArrayBuffer, or a typed-array view over one.
            return v instanceof Uint8Array
                ? v.buffer.slice(v.byteOffset, v.byteOffset + v.byteLength)
                : v;
        }
        return null;
    }

    async function asBytes(v) {
        const direct = asArrayBuffer(v);
        if (direct) return direct;
        if (v && typeof v.arrayBuffer === 'function') {   // Blob-like
            const ab = await v.arrayBuffer();
            return asArrayBuffer(ab) || ab;
        }
        if (typeof v === 'string') {                      // a manager that ignored responseType
            return new TextEncoder().encode(v).buffer;
        }
        return null;
    }
    // =====================================================================
    // ebookjapan — off-thread descrambling, on the shared pool
    // =====================================================================
    // The shuffle is a synchronous burst on whatever thread runs it, so a run of
    // pages starves the UI thread. A worker is a clean realm: its OffscreenCanvas
    // keeps convertToBlob and getImageData, and the glue's Window shim already
    // accepts a worker global. Each worker installs its own copy of the pack,
    // because the module is single-shot and a second decrypt_session traps.
    //
    // The pool itself is core's makePool, the same one BookWalker uses. What is
    // local here is only the job envelope and the worker source, which is what
    // makePool's sixth argument exists for.
    const EBJ_MIME_EXT = { 'image/png': 'png', 'image/jpeg': 'jpg', 'image/webp': 'webp' };

    /**
     * The job envelope this store posts. makePool ships BookWalker's
     * relPath/seeds/q shape by default; this one carries the page's geometry and
     * the session material the worker needs to install its own pack.
     */
    function ebjJobMessage(job) {
        return {
            id: job.id,
            page: job.page,
            width: job.width,
            height: job.height,
            withSrc: !!job.withSrc,
            blob: job.blob,
            sessionId: job.sessionId,
            code: job.code,
            openPayload: job.openPayload,
            drmPayload: job.drmPayload,
            params: job.params,
            codec: job.codec,
            autograph: job.autograph || null,
        };
    }

    /**
     * The worker source. Both the glue and the wasm ride inside it as base64, so
     * nothing heavy crosses postMessage and a spawn costs one Blob URL for the
     * whole pool. The module is installed lazily on the first page and reused for
     * every page after, and a batch is walked in order so two pages never race on
     * one canvas.
     */
    function ebjWorkerSource() {
        return '"use strict";\n' +
            'const GLUE = (function () { ' + atob(EBJ_GLUE_B64) + ' })();\n' +
            'const WASM_B64 = "' + EBJ_WASM_B64 + '";\n' +
            'let mod = null, ready = null;\n' +
            'function dec(b) { const s = atob(b), u = new Uint8Array(s.length);\n' +
            '    for (let i = 0; i < s.length; i++) u[i] = s.charCodeAt(i); return u; }\n' +
            'function install(job) {\n' +
            '    if (ready) return ready;\n' +
            '    ready = (async () => {\n' +
            '        const m = GLUE();\n' +
            '        await m.default({ module_or_path: dec(WASM_B64) });\n' +
            '        await m.decrypt_session(job.sessionId, job.code, job.openPayload, job.drmPayload);\n' +
            '        if (job.params) await m.open_param(job.params);\n' +
            '        return m;\n' +
            '    })();\n' +
            '    return ready;\n' +
            '}\n' +
            'async function one(job) {\n' +
            '    const m = await install(job);\n' +
            '    const bytes = new Uint8Array(await job.blob.arrayBuffer());\n' +
            '    const bmp = await createImageBitmap(new Blob([bytes], { type: "image/webp" }));\n' +
            '    try { bmp.naturalWidth = bmp.width; bmp.naturalHeight = bmp.height; } catch (e) {}\n' +
            '    if (job.withSrc) {\n' +
            '        let s = "";\n' +
            '        for (let i = 0; i < bytes.length; i += 0x8000) {\n' +
            '            s += String.fromCharCode.apply(null, bytes.subarray(i, i + 0x8000));\n' +
            '        }\n' +
            '        try { bmp.src = "data:image/webp;base64," + btoa(s); } catch (e) {}\n' +
            '    }\n' +
            '    let overlay;\n' +
            '    if (job.autograph && job.autograph.page === job.page) {\n' +
            '        const ob = dec(job.autograph.image);\n' +
            '        overlay = await createImageBitmap(new Blob([ob], { type: job.autograph.type }));\n' +
            '        try {\n' +
            '            overlay.naturalWidth = overlay.width;\n' +
            '            overlay.naturalHeight = overlay.height;\n' +
            '            overlay.src = "data:" + job.autograph.type + ";base64," + job.autograph.image;\n' +
            '        } catch (e) {}\n' +
            '    }\n' +
            '    const canvas = new OffscreenCanvas(job.width, job.height);\n' +
            '    const ctx = canvas.getContext("2d");\n' +
            '    m.shuffle({ ctx: ctx, x: 0, y: 0, data: { image: bmp },\n' +
            '        autographed: overlay, page: job.page });\n' +
            '    let stats = null;\n' +
            '    try {\n' +
            '        const d = ctx.getImageData(0, 0, canvas.width, canvas.height).data;\n' +
            '        const step = Math.max(4, Math.floor(d.length / 4000 / 4) * 4);\n' +
            '        let sum = 0, n = 0, black = 0;\n' +
            '        for (let i = 0; i + 3 < d.length; i += step) {\n' +
            '            const v = (d[i] + d[i + 1] + d[i + 2]) / 3;\n' +
            '            sum += v; n++; if (v < 8) black++;\n' +
            '        }\n' +
            '        stats = { mean: sum / Math.max(1, n), black: black / Math.max(1, n),\n' +
            '            samples: n, via: "worker getImageData" };\n' +
            '    } catch (e) { stats = { error: (e && e.message) || String(e) }; }\n' +
            '    if (bmp.close) { try { bmp.close(); } catch (e) {} }\n' +
            '    const blob = await canvas.convertToBlob({ type: job.codec.mime, quality: job.codec.quality });\n' +
            '    return { blob: blob, mime: job.codec.mime, width: canvas.width, height: canvas.height, stats: stats };\n' +
            '}\n' +
            'self.onmessage = async ev => {\n' +
            '    const m = ev.data || {};\n' +
            '    const jobs = m.jobs || [];\n' +
            '    for (const job of jobs) {\n' +
            '        try {\n' +
            '            const out = await one(job);\n' +
            '            self.postMessage({ id: job.id, batchId: m.batchId, blob: out.blob, mime: out.mime,\n' +
            '                width: out.width, height: out.height, stats: out.stats });\n' +
            '        } catch (e) {\n' +
            '            self.postMessage({ id: job.id, batchId: m.batchId, error: (e && e.message) || String(e) });\n' +
            '        }\n' +
            '    }\n' +
            '};\n';
    }

    // Core's pool is callback per job; the run wants a promise per page.
    const ebjPoolWaiters = new Map();

    function ebjPoolDone(result) {
        const waiter = result && ebjPoolWaiters.get(result.id);
        if (!waiter) return;
        ebjPoolWaiters.delete(result.id);
        if (result.error || !result.blob) waiter.no(new Error(result.error || 'the worker returned no image'));
        else waiter.ok(result);
    }

    function ebjPoolPage(pool, job) {
        return new Promise((ok, no) => {
            ebjPoolWaiters.set(job.id, { ok: ok, no: no });
            pool.submit(job);
        });
    }

    /**
     * One page as a pool job. The worker installs its pack from the first job it
     * sees and keeps it, so this carries the session material every time and the
     * worker ignores it after the first.
     */
    function ebjPoolJob(geo, codec, index, row, buf, withSrc) {
        const p = ebjState.payload || {};
        const book = ebjState.book;
        return {
            id: index,
            page: row.page,
            width: geo.width,
            height: geo.height,
            withSrc: !!withSrc,
            blob: new Blob([buf], { type: 'image/webp' }),
            sessionId: p.sessionId,
            code: p.code,
            openPayload: p.openPayload,
            drmPayload: p.drmPayload,
            params: ebjState.params,
            codec: codec,
            autograph: (book && book.autograph) ? book.autograph : null,
        };
    }

    /**
     * Can this page run a worker at all? ebookjapan sets no worker-src, so
     * script-src governs and it allows no blob:, which means new Worker(blobURL)
     * is refused. That refusal does not throw the constructor — the worker fires
     * error instead — so core's pool would respawn a blocked worker on every
     * failure and bury the console. One probe answers it, and the run then stays
     * on this thread by choice rather than by accident.
     */
    function ebjWorkerAllowed() {
        return new Promise(resolve => {
            let url = null, w = null, done = false;
            const finish = ok => {
                if (done) return;
                done = true;
                if (w) { try { w.terminate(); } catch (e) {} }
                if (url) { try { URL.revokeObjectURL(url); } catch (e) {} }
                resolve(ok);
            };
            try {
                url = URL.createObjectURL(new Blob(['self.postMessage(1);'], { type: 'text/javascript' }));
                w = new Worker(url);
            } catch (e) { finish(false); return; }
            w.onmessage = () => finish(true);
            w.onerror = () => finish(false);
            setTimeout(() => finish(false), 1500);
        });
    }
    // =====================================================================
    // ebookjapan — run pipeline and adapter registration
    // =====================================================================
    // The shape follows sites/cmoa/02-run.js: wait for the viewer, take the
    // title, hand everything to the shared run harness, fetch and descramble
    // pages across a worker pool, and let the harness own the bars, the Mokuro
    // session, the ZIP and the reporting.
    function ebjSleep(ms) { return new Promise(r => setTimeout(r, ms)); }

    /**
     * The shared codec speaks {fmt,type,quality,ext,lossless}; the ported
     * encoder reads {mime,qualityValue}. Left unmapped, every page would be
     * encoded with the wrong MIME and nobody would notice until the file was
     * opened again.
     */
    function ebjCodec() {
        const c = resolveImageCodec();
        return {
            fmt: c.fmt, mime: c.type, ext: c.ext, lossless: !!c.lossless,
            quality: c.quality,
            qualityValue: c.lossless ? 1 : (Number(c.quality) || 0.92),
        };
    }

    // =====================================================================
    // Per-page stage timing
    // =====================================================================
    // "It starts off fast and then slows down to 1 page/s" has three candidate
    // owners: the network fetch, the main-thread decode+descramble+encode, and
    // handing the finished blob to the run harness (ZIP entry, page cache, OCR
    // queue). Guessing between them is what makes a slow run expensive, so
    // every page records how long each stage took and the run ends with the
    // totals and the distribution.
    //
    // It is deliberately cheap: two performance.now() calls per stage per page,
    // no per-page log line, and a bounded sample ring so a 1000-page volume
    // cannot grow the accumulator. The ring keeps min/max exactly (running
    // values) and the median from a fixed 512-slot rotating sample, which is
    // representative without holding a million numbers for a long series.
    const EBJ_TIMING_SAMPLES = 512;

    function ebjNow() {
        try { return performance.now(); } catch (e) { return Date.now(); }
    }

    function ebjTimingNew() {
        const stage = () => ({ total: 0, n: 0, min: Infinity, max: 0, ring: [], next: 0 });
        return {
            fetch: stage(), decode: stage(), descramble: stage(), write: stage(),
            lanes: Object.create(null),
            pages: 0,   // pages that reached the harness (the write stage)
            failed: 0,  // pages whose stage threw; excluded from the min/median/max
            retried: 0,
            start: 0,   // set when the page phase begins, not at run entry
            phaseMs: 0, // wall clock the page phase actually took
        };
    }

    function ebjTimingAdd(t, name, ms) {
        const s = t[name];
        if (!s) return;
        const v = (isFinite(ms) && ms > 0) ? ms : 0;
        s.total += v;
        s.n++;
        if (v < s.min) s.min = v;
        if (v > s.max) s.max = v;
        if (s.ring.length < EBJ_TIMING_SAMPLES) s.ring.push(v);
        else s.ring[s.next++ % EBJ_TIMING_SAMPLES] = v;
    }

    /** Which transport actually served a page (gm / page / px:7010 / edge). */
    function ebjTimingLane(t, lane) {
        const k = lane || '?';
        t.lanes[k] = (t.lanes[k] || 0) + 1;
    }

    function ebjMedian(ring) {
        if (!ring || !ring.length) return 0;
        const a = ring.slice().sort((x, y) => x - y);
        const mid = a.length >> 1;
        return a.length % 2 ? a[mid] : (a[mid - 1] + a[mid]) / 2;
    }

    function ebjMs(v) {
        if (!isFinite(v) || v <= 0) return '0ms';
        return v >= 1000 ? (v / 1000).toFixed(1) + 's' : Math.round(v) + 'ms';
    }

    function ebjTimingStageText(t, name) {
        const s = t[name];
        if (!s || !s.n) return null;
        return name + ': ' + ebjMs(s.total) + ' total, ' +
            ebjMs(s.min) + ' / ' + ebjMs(ebjMedian(s.ring)) + ' / ' + ebjMs(s.max) +
            ' min/median/max over ' + s.n + ' pages';
    }

    /**
     * The one-line breakdown. fetch is the CDN/GM transport, cpu is everything
     * this thread spent between the bytes arriving and an encoded blob existing
     * (decode split out so a slow JPEG decode is not blamed on the shuffle),
     * write is the harness hand-off. The stage that dominates is the one to fix.
     */
    function ebjTimingLine(t) {
        const parts = [
            'fetch ' + ebjMs(t.fetch.total),
            'cpu ' + ebjMs(t.decode.total + t.descramble.total) +
                ' (decode ' + ebjMs(t.decode.total) + ' + descramble ' + ebjMs(t.descramble.total) + ')',
            'write ' + ebjMs(t.write.total),
            'wall ' + ebjMs(t.phaseMs) + ebjTimingRate(t),
            t.pages + ' pages timed' +
                (t.retried ? ', ' + t.retried + ' retried' : '') +
                (t.failed ? ', ' + t.failed + ' failed attempt(s)' : ''),
        ];
        const lanes = Object.keys(t.lanes).sort((a, b) => t.lanes[b] - t.lanes[a]);
        if (lanes.length) parts.push('lanes ' + lanes.map(k => k + ' ' + t.lanes[k]).join(' / '));
        return 'timing: ' + parts.join(' \u00b7 ');
    }

    function ebjTimingRate(t) {
        if (!(t.phaseMs > 0) || !t.pages) return '';
        return ' (' + (t.pages / (t.phaseMs / 1000)).toFixed(1) + ' pages/s)';
    }

    function ebjTimingRaw(t) {
        const lines = ['fetch', 'decode', 'descramble', 'write']
            .map(name => ebjTimingStageText(t, name))
            .filter(Boolean);
        // The wall clock is what makes the stages interpretable: stage totals are
        // summed over concurrent workers, so only the descramble total (one main
        // thread) and this wall clock are directly comparable.
        if (t.phaseMs > 0) {
            lines.push('wall: ' + ebjMs(t.phaseMs) + ' for the page phase' + ebjTimingRate(t));
        }
        return lines;
    }

    function ebjTimingEmpty(t) {
        return !t || (!t.pages && !t.failed);
    }

    /**
     * Surface the measurement where a run is actually read. The harness has
     * usually already written the outcome into the details element, so append
     * the timing line instead of replacing it, and put the per-stage
     * distribution plus the raw failure lines in the collapsible block. EbjLog
     * carries the same line to the console, debug-gated like every other
     * ebookjapan diagnostic. A failure path calls this too: "which stage ate
     * the run" is exactly what a failed run needs to answer.
     */
    function ebjTimingPublish(ui, harness, t) {
        if (ebjTimingEmpty(t)) return;
        const line = ebjTimingLine(t);
        try { ebjLog('timing', line); } catch (e) {}
        // Automation callers read the result object, not the panel; put the same
        // numbers there so a headless run can be measured without scraping logs.
        try {
            const rr = harness && harness.runResult;
            if (rr) {
                rr.timing = {
                    phaseMs: Math.round(t.phaseMs),
                    fetchMs: Math.round(t.fetch.total), decodeMs: Math.round(t.decode.total),
                    descrambleMs: Math.round(t.descramble.total), writeMs: Math.round(t.write.total),
                    pages: t.pages, failed: t.failed, retried: t.retried,
                    lanes: Object.assign({}, t.lanes),
                };
            }
        } catch (e) {}
        try {
            const el = ui && ui.details;
            if (!el) return;
            const existing = (el.textContent || '').trim();
            const raw = ebjTimingRaw(t).concat((harness && harness.errors) || []);
            setRunDetails(el, existing ? (existing + ' \u2014 ' + line) : line, raw);
        } catch (e) {}
    }

    /**
     * Fetch one page. GM first, the shared lanes as backup — and that order is
     * deliberate, not inertia. It was re-derived from the transport code:
     *
     * - `laneFetch()` is the only path that can pick a mokuro-bridge proxy lane
     *   (the bridge's accelerator ports). Its eligibility opt is `allowProxy`:
     *   a lane table with proxy entries is used unless the caller passes
     *   `{allowProxy:false}`, so a bare `laneFetch(url, ms)` is nominally
     *   eligible. But the ports have to be *discovered* first, and every
     *   discovery and every proxy request is a page-realm fetch to
     *   `http://127.0.0.1:<port>` (`probeBridgeFetchProxy` -> the bridge's
     *   /health; `laneAttempt` -> `proxyUrlFor`). ebookjapan serves
     *   `connect-src 'self' https: wss:` (see core/31-mokuro.js, which is why
     *   the bridge client there goes through GM_xmlhttpRequest), so those plain
     *   http:// loopback fetches are refused by this page's CSP. The proxy lane
     *   therefore cannot carry a byte here, and `laneFetch` would burn a
     *   refused request per page before falling through.
     * - The remaining lanes cannot beat GM either: `page`/`dot` hit the CDN
     *   cross-origin (no ACAO -> CORS refusal), and `gm` is GM_xmlhttpRequest —
     *   the same transport this function already uses first. `edge` is an
     *   opt-in mirror that is not configured by default.
     *
     * So the accelerator is genuinely unreachable for prod-contents-br-page
     * .akamaized.net on this site, and reordering cannot help; GM is the one
     * lane that works and the lanes stay the fallback for managers without it.
     * If ebookjapan's CSP ever gains a loopback connect-src, revisit this.
     */
    async function ebjFetchPage(url) {
        // The page CDN sends no Access-Control-Allow-Origin, so a page-realm
        // fetch is refused outright — one CORS error per lane attempt per page.
        // GM_xmlhttpRequest is not subject to that and @connect already lists
        // the host, so go through it first and keep the shared lanes as backup.
        if (typeof GM_xmlhttpRequest === 'function') {
            try {
                const r = await new Promise((ok, no) => {
                    GM_xmlhttpRequest({
                        method: 'GET', url: url, responseType: 'blob', timeout: 30000,
                        onload: ok, onerror: no, ontimeout: no,
                    });
                });
                if (r && r.status >= 200 && r.status < 300 && r.response) {
                    return { buf: await r.response.arrayBuffer(), lane: 'gm' };
                }
            } catch (e) { /* fall through to the shared lanes */ }
        }
        // laneFetch resolves rather than rejecting, and the gm lane answers with
        // {ok,status,blob} only — no headers, no arrayBuffer. So: check res.ok,
        // then go through blob().
        const res = await laneFetch(url, 30000);
        if (!res || !res.ok) throw new Error('HTTP ' + ((res && res.status) || '?'));
        const blob = await res.blob();
        return { buf: await blob.arrayBuffer(), lane: (res._lane && res._lane.kind) || '?' };
    }

    async function ebjRun(ui, mode, options) {
        const runOptions = normalizeRunOptions(options, mode);
        // Function scope on purpose: the arming block below sets these inside a
        // try, but the finally has to terminate the pool, and a `let` inside that
        // try is invisible there — which threw ebjPool is not defined after a
        // run had already saved successfully.
        let ebjPool = null;
        let ebjCanary = null;
        // Per-page stage totals for this whole run (main pass, retry pass and
        // the canary fetches). Function scope for the same reason as ebjPool:
        // the failure path has to be able to report it.
        const ebjTiming = ebjTimingNew();
        const runResult = runOptions.automation
            ? (runOptions.result || newAutomationResult(mode, ebjState.code || '', runOptions.deferFinalize))
            : null;
        if (runResult) { runOptions.result = runResult; runOptions.errors = runResult.errors; }

        let harness = null;
        try {
            reportRunProgress(runOptions, 'started', { mode: mode, cid: ebjState.code || '' });
            ebjLog('run', 'entered: mode=' + mode + ' url=' + location.href +
                ' code=' + (ebjState.code || '?'));
            ebjState.running = true;
            ebjResetCore();

            // The viewer learns the volume a beat after the page loads, and its
            // manifest needs a session the viewer has already negotiated.
            let book = null;
            let lastErr = null;
            for (let i = 0; i < 30; i++) {
                try {
                    book = await ebjResolvePages(location.href);
                    lastErr = null;
                } catch (e) {
                    lastErr = e;
                    book = null;
                    // Say it the first time it happens, not fifteen seconds later:
                    // swallowing this is what made the whole failure invisible.
                    if (i === 0) ebjLog('resolve', 'attempt failed: ' + safeLogText((e && e.message) || e));
                }
                if (book && book.pages && book.pages.length) break;
                await ebjSleep(500);
            }
            if (!book || !book.pages || !book.pages.length) {
                throw new Error('the ebookjapan viewer has not reported this volume yet — open ' +
                    'the book and let a page render, then try again.' +
                    (lastErr ? ' (last resolve error: ' + safeLogText((lastErr && lastErr.message) || lastErr) + ')'
                             : ' (the resolve returned no pages and reported no error)'));
            }
            // The autograph overlay is the one page whose scrambled tiles are a
            // separate image. ebjState.payload is what decrypt_session was given.
            try {
                book.autograph = autographSpec(ebjState.payload && ebjState.payload.drmPayload);
            } catch (e) { book.autograph = null; }

            const rawTitle = book.name || book.title || '';
            const title = rawTitle || ebjState.code || 'ebookjapan volume';
            const sv = splitSeriesVolume(title);
            const archiveName = ui.syncArchiveDefault(rawTitle) || zipBaseName(sv, title);
            const rows = book.pages;
            const total = rows.length;
            const geo = { width: (book.canvas && book.canvas.width) || 0, height: (book.canvas && book.canvas.height) || 0 };
            if (!geo.width || !geo.height) throw new Error('could not determine the page canvas size');
            const cid = ebjState.code || '';

            if (runResult) {
                runResult.cid = cid;
                runResult.mode = mode;
                runResult.title = title;
                runResult.total = total;
                reportRunProgress(runOptions, 'book', { title: title, cid: cid });
            }

            harness = createRunHarness(ui, mode, runOptions, { title, archiveName, sv, total, cid });
            harness.setTotal(total);
            if (!runOptions.headless) {
                renderBookCard(ui.statsEl, {
                    title: title, pages: total, resolution: geo.width + ' \u00d7 ' + geo.height,
                    type: (book.direction === true || book.direction === 1) ? 'Right-to-left' : 'Full Edition',
                });
                if (sv.series) fetchAndRenderStats(ui.statsEl, sv.series, sv.volNum);
            }
            harness.showBars();
            if (harness.mokuro) await harness.mokuro.open();
            ebjLog('run', total + ' pages \u00b7 ' + geo.width + 'x' + geo.height + ' \u00b7 ' + title);

            const codec = ebjCodec();
            ebjShape.canvas = 'auto';
            ebjShape.image = 'img';
            let glue = null;
            let gatePassed = false;

            // One cursor drives both passes. During the main pass it walks every
            // row in order; the retry pass below re-points it at only the indexes
            // that failed and runs the *same* worker() under the *same*
            // concurrency gate. That is what turns the retry tail from N serial
            // main-thread descrambles into one bounded batch, without a second
            // scheduling mechanism to keep in sync with the first.
            let nextIndex = 0;
            let ebjRetryList = null;
            let ebjRetryAt = 0;
            const ebjNextJob = () => {
                if (ebjRetryList) {
                    return ebjRetryAt < ebjRetryList.length ? ebjRetryList[ebjRetryAt++] : -1;
                }
                return nextIndex < total ? nextIndex++ : -1;
            };

            const worker = async () => {
                while (true) {
                    const i = ebjNextJob();
                    if (i < 0) return;
                    const row = rows[i];
                    const pageIdx = i + 1;
                    try {
                        if (!row.url) throw new Error('no page name');
                        const tFetch = ebjNow();
                        const got = await ebjFetchPage(row.url);
                        const tFetched = ebjNow();
                        ebjTimingAdd(ebjTiming, 'fetch', tFetched - tFetch);
                        ebjTimingLane(ebjTiming, got.lane);
                        harness.bumpFetched(1);
                        let out = null;
                        let tDone = tFetched;
                        // A run that adopted the pool descrambles there, which is
                        // what the canary was for and what the retry pass always
                        // did. No pool (ebookjapan's CSP refuses blob: workers)
                        // means the in-thread path below, exactly as before.
                        if (ebjPool && ebjCanary) {
                            try {
                                const res = await ebjPoolPage(ebjPool,
                                    ebjPoolJob(geo, codec, pageIdx, row, got.buf, ebjCanary.withSrc));
                                out = { blob: res.blob, ext: EBJ_MIME_EXT[res.mime] || codec.ext, stats: res.stats };
                                tDone = ebjNow();
                                ebjTimingAdd(ebjTiming, 'descramble', tDone - tFetched);
                            } catch (e) {
                                ebjLog('worker', 'fell back to this thread: ' +
                                    safeLogText((e && e.message) || e));
                            }
                        }
                        if (!out) {
                            const bitmap = await decodeImage(got.buf);
                            const tDecoded = ebjNow();
                            ebjTimingAdd(ebjTiming, 'decode', tDecoded - tFetched);
                            const aov = (book.autograph && book.autograph.page === row.page)
                                ? await loadAutographImage(book.autograph) : undefined;
                            out = await descramblePage(glue, bitmap, row, geo,
                                { codec: codec, autographed: aov });
                            tDone = ebjNow();
                            ebjTimingAdd(ebjTiming, 'descramble', tDone - tDecoded);
                        }
                        // The paint gate: "the shuffle ran" is not "the page
                        // painted". The first page decides whether this shape is
                        // believable at all.
                        if (!gatePassed) {
                            const st = out.stats || await canvasStats(null);
                            if (st && !st.error && st.mean < 6) {
                                gatePassed = true;
                                throw new Error('the descrambler painted an empty page (' + statsText(st) +
                                    ') — refusing to save a book of blank images');
                            }
                            gatePassed = true;
                            ebjLog('canary', 'page 1 painted ' + statsText(st));
                        }
                        harness.notePage(pageIdx, out.blob, out.crc, out.ext);
                        ebjTimingAdd(ebjTiming, 'write', ebjNow() - tDone);
                        ebjTiming.pages++;
                    } catch (e) {
                        ebjTiming.failed++;
                        harness.bumpFetched(1);
                        harness.noteFailure(pageIdx, safeLogText((e && e.message) || e));
                    }
                }
            };

            // Off-thread, on core's own pool. Nothing is trusted on faith: the
            // first page goes through a worker and is adopted only if those pixels
            // pass the same paint gate as any other page. Otherwise this run keeps
            // descrambling on this thread and the cost is one log line.
            // The page phase is what the user experiences as "the download", so
            // its wall clock starts here, after the viewer resolve and the bars.
            ebjTiming.start = ebjNow();
            try {
                if (typeof makePool === 'function' && typeof Worker !== 'undefined' &&
                    typeof OffscreenCanvas !== 'undefined' && rows[0] && rows[0].url) {
                    if (!(await ebjWorkerAllowed())) {
                        ebjLog('worker-canary', 'this page\u2019s CSP refuses a blob: worker — ' +
                            'descrambling on this thread');
                        throw { ebjSkipPool: true };
                    }
                    // workerPoolSize() is core's own answer for this machine. The old
                    // cap of 8 was mine, and the real bottleneck here is the shuffle plus
                    // the encode, so use what core asks for. Two pages in flight per
                    // worker overlaps convertToBlob with the next page's shuffle, which is
                    // the same ~10% BookWalker measured.
                    const size = Math.max(2, workerPoolSize());
                    ebjPool = makePool(size, ebjWorkerSource(), ebjPoolDone, 60000, 2, ebjJobMessage);
                    const tCanaryFetch = ebjNow();
                    const first = await ebjFetchPage(rows[0].url);
                    ebjTimingAdd(ebjTiming, 'fetch', ebjNow() - tCanaryFetch);
                    ebjTimingLane(ebjTiming, first.lane);
                    harness.bumpFetched(1);
                    for (const withSrc of [false, true]) {
                        try {
                            const tCanary = ebjNow();
                            const res = await ebjPoolPage(ebjPool, ebjPoolJob(geo, codec, 1, rows[0], first.buf, withSrc));
                            ebjTimingAdd(ebjTiming, 'descramble', ebjNow() - tCanary);
                            ebjLog('worker-canary', 'src=' + withSrc + ' ' + statsText(res.stats));
                            if (res.stats && !res.stats.error && res.stats.mean >= 6) {
                                ebjCanary = { res: res, withSrc: withSrc };
                                break;
                            }
                        } catch (e) {
                            ebjLog('worker-canary', 'src=' + withSrc + ' failed: ' +
                                safeLogText((e && e.message) || e));
                        }
                    }
                    if (ebjCanary) {
                        harness.notePage(1, ebjCanary.res.blob, undefined,
                            EBJ_MIME_EXT[ebjCanary.res.mime] || codec.ext);
                        nextIndex = 1;
                        ebjLog('worker-canary', 'adopted ' + size + ' workers (src=' + ebjCanary.withSrc + ')');
                    } else {
                        try { ebjPool.terminate(); } catch (e) {}
                        ebjPool = null;
                        ebjLog('worker-canary', 'the pool painted nothing — descrambling on this thread');
                    }
                }
            } catch (e) {
                if (ebjPool) { try { ebjPool.terminate(); } catch (e2) {} ebjPool = null; }
                if (!e || !e.ebjSkipPool) {
                    ebjLog('worker-canary', 'pool unavailable: ' + safeLogText((e && e.message) || e));
                }
            }

            const budget = (typeof fetchSocketBudget === 'function' ? fetchSocketBudget(true) : 6) || 6;
            const concurrency = Math.max(1, Math.min(total, Math.max(2, Math.min(16, budget))));
            ebjLog('run', 'concurrency ' + concurrency + ' on ' + budget + ' sockets');
            glue = await ebjLoadGlue();
            const workers = [];
            for (let w = 0; w < concurrency; w++) workers.push(worker());
            await Promise.all(workers);

            // One retry pass: a page that failed once is usually a transient lane
            // or session rollover, and the viewer will have settled by now. It is
            // driven through the same worker() and the same `concurrency` gate as
            // the main pass, just with the cursor re-pointed at the failed
            // indexes — a serial awaited loop here was one full main-thread
            // descramble per iteration, which is the "fast, then one page a
            // second" tail this run was reported for. A page that throws again
            // stays failed and is reported below, exactly as before.
            if (harness.failedIdx.size && !runOptions.headless) {
                ebjRetryList = Array.from(harness.failedIdx)
                    .map(n => n - 1)
                    .filter(n => n >= 0 && n < total && rows[n] && rows[n].url)
                    .sort((a, b) => a - b);
                ebjRetryAt = 0;
                if (ebjRetryList.length) {
                    ebjTiming.retried = ebjRetryList.length;
                    ebjLog('run', 'retrying ' + ebjRetryList.length + ' failed page(s) across ' +
                        concurrency + ' workers');
                    const retryWorkers = [];
                    for (let w = 0; w < concurrency; w++) retryWorkers.push(worker());
                    await Promise.all(retryWorkers);
                }
            }

            // Close the page-phase clock here, before the ZIP is assembled or
            // the OCR finalize runs, so "wall" means fetch+descramble time only.
            if (ebjTiming.start) ebjTiming.phaseMs = ebjNow() - ebjTiming.start;

            const missing = total - harness.okIdx.size;
            if (mode === 'ocr' && harness.mokuro) {
                await harness.mokuro.settle();
                if (runOptions.deferFinalize) {
                    ebjTimingPublish(ui, harness, ebjTiming);
                    return harness.mokuro.deferred();
                }
                const fin = await harness.mokuro.finalize();
                harness.markFinished();
                ebjTimingPublish(ui, harness, ebjTiming);
                return harness.outcome(fin.ok);
            }
            if (mode === 'ocr' && !harness.mokuro) throw new Error('Mokuro OCR is unavailable for this run');
            if (missing === total) {
                setRunDetails(harness.details, msgAllFailedZip(), harness.errors);
                ebjTimingPublish(ui, harness, ebjTiming);
                return harness.outcome(false);
            }
            const finished = await harness.finishZip();
            ebjTimingPublish(ui, harness, ebjTiming);
            return finished;
        } catch (e) {
            const text = safeLogText((e && e.stack) || (e && e.message) || e);
            ebjLog('run', 'failed: ' + text);
            // Core's launch() catches a rejected run and only console.warns it,
            // which from the panel is indistinguishable from the button doing
            // nothing. Put it where it will actually be read.
            try {
                setRunDetails(ui.details, 'the run failed: ' + text,
                    harness ? harness.errors : []);
            } catch (e2) {}
            const reported = harness ? harness.reportFailure(e) : null;
            // Last, because reportFailure writes its own one-line panel message:
            // a failed run is exactly when "which stage ate the time" matters,
            // so the timing line is appended after it rather than erased by it.
            ebjTimingPublish(ui, harness, ebjTiming);
            if (reported) throw reported;
            throw e;
        } finally {
            if (ebjPool) { try { ebjPool.terminate(); } catch (e) {} ebjPool = null; }
            ebjState.running = false;
            if (harness) await harness.cleanup();
        }
    }

    registerSite({
        id: 'ebookjapan',
        label: 'ebookjapan',
        panelTitle: 'ebookjapan Native Downloader',
        matches() {
            try { return /(^|\.)ebookjapan\.yahoo\.co\.jp$/i.test(location.hostname); } catch (e) { return false; }
        },
        install() {
            // The viewer URL carries the volume code, so the adapter knows
            // its id from load. A network resolve only confirms it.
            try {
                const t = ebjParseTarget(location.href);
                if (t && t.code) ebjState.code = t.code;
            } catch (e) {}
        },
        getBook() {
            const b = ebjState.book;
            if (!b) return null;
            const title = b.name || b.title || ebjState.code || '';
            const sv = splitSeriesVolume(title);
            return { rawTitle: b.name || b.title || '', title: title, series: sv.series, volNum: sv.volNum };
        },
        getPreview() {
            const b = ebjState.book;
            if (!b || !b.pages || !b.pages.length) return null;
            const geo = b.canvas || {};
            return {
                title: b.name || b.title || ebjState.code || '',
                pages: b.pages.length,
                resolution: geo.width ? (geo.width + ' \u00d7 ' + geo.height) : '?',
                type: (b.direction === true || b.direction === 1) ? 'Right-to-left' : 'Full Edition',
            };
        },
        getCid() {
            if (ebjState.code) return ebjState.code;
            // Fall back to the URL: the page-cache key and the availability
            // badge read this before anything has been fetched.
            try {
                const t = ebjParseTarget(location.href);
                return (t && (t.code || t.publication)) || '';
            } catch (e) { return ''; }
        },
        // The shared panel awaits this before reading getBook/getPreview, so the
        // title, page count and page size are on the card before a run starts —
        // which is exactly where the standalone script had to bolt this on.
        async refresh() {
            try {
                const b = await ebjResolvePages(location.href);
                if (b && b.pages && b.pages.length) { ebjState.book = b; return true; }
            } catch (e) { ebjLog('refresh', safeLogText((e && e.message) || e)); }
            return false;
        },
        afterBoot() {
            let ticks = 0;
            const timer = setInterval(async () => {
                ticks++;
                if ((ebjState.book && ebjState.book.pages && ebjState.book.pages.length) || ticks > 60) {
                    clearInterval(timer);
                    return;
                }
                try { await ebjResolvePages(location.href); } catch (e) {}
            }, 1500);
        },
        archiveDefault(rawTitle) { return archiveDefaultName(rawTitle) || fsSafePath(ebjState.code || ''); },
        run(ui, mode, options) { return ebjRun(ui, mode, options); },
        state: ebjState,
        debug: {
            get state() { return ebjState; },
            get shape() { return ebjShape; },
            get lastDecodePath() { return ebjLastDecodePath; },
            get encodePath() { return ebjEncodePath; },
            get lastShuffleTrace() { return ebjLastShuffleTrace; },
            get probeOnce() { return ebjProbeOnce; },
            get simulatedTraps() { return ebjSimulatedTraps; },
        },
        // Call __bwddEbookjapanDebug() from the console for a live answer to
        // "where did it stop?". The standalone had this and it was the fastest
        // way to tell a realm problem from a session problem.
        debugGlobals: {
            __bwddEbookjapan: ebjState,
            __bwddEbookjapanDebug: function ebjDiag() {
                return {
                    href: location.href,
                    code: ebjState.code || '',
                    running: !!ebjState.running,
                    payload: ebjState.payload ? Object.keys(ebjState.payload) : null,
                    pages: (ebjState.book && ebjState.book.pages) ? ebjState.book.pages.length : 0,
                    canvas: ebjState.book && ebjState.book.canvas ? ebjState.book.canvas : null,
                    shape: { canvas: ebjShape.canvas, image: ebjShape.image },
                    lastDecodePath: ebjLastDecodePath,
                    encodePath: ebjEncodePath,
                    lastShuffleTrace: ebjLastShuffleTrace,
                    probeOnce: ebjProbeOnce,
                    simulatedTraps: ebjSimulatedTraps,
                };
            },
        },
    });
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
