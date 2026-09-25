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
