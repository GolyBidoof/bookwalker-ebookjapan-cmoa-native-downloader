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

