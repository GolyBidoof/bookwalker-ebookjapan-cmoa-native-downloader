// Check the shipped naming and ZIP code without requiring a browser. Filename
// order matters after extraction and in readers that sort ZIP names themselves.
'use strict';
const fs = require('fs');
const path = require('path');
const vm = require('vm');

const root = path.resolve(__dirname, '..');
const fragment = file => fs.readFileSync(path.join(root, 'src', file), 'utf8');
let storageReads = 0;
class Storage { setItem() {} }
const originalSetItem = Storage.prototype.setItem;
const context = vm.createContext({
  URLSearchParams, TextEncoder, Blob, FormData, setTimeout,
  window: { Storage },
  localStorage: { getItem() { storageReads++; return JSON.stringify({ page: 0, url: "changed.xhtml" }); } },
  location: { search: '?cid=book-1' },
  isHeadlessPage: () => false,
  IMAGE_CODEC: { ext: 'jpg' },
});
vm.runInContext(
  fragment('sites/bookwalker/00-state.js') +
  fragment('core/40-naming.js') +
  fragment('core/41-zip.js') +
  '\nglobalThis.api = { bookWalkerPageName, buildStoreZip, zipEntryNumber };',
  context
);
const { bookWalkerPageName, buildStoreZip, zipEntryNumber } = context.api;
const results = [];
function check(name, pass, detail) {
  results.push(pass);
  console.log((pass ? 'PASS  ' : 'FAIL  ') + name + ' — ' + detail);
}

(async () => {
  const names = Array.from({ length: 12 }, (_, i) =>
    bookWalkerPageName(i + 1, 'OEBPS/text/p-' + String(i + 1).padStart(4, '0') + '.xhtml'));
  check('BookWalker names retain the source stem and padded page number',
    names[0] === '0001 p-0001.jpg' && names[9] === '0010 p-0010.jpg',
    names[0] + ', ' + names[9]);
  check('double-digit pages remain in filename order',
    names.slice().sort().join('|') === names.join('|'), names.slice().sort().join(', '));

  check('nested paths sort by their basename ordinal',
    zipEntryNumber('2026 Series/Volume/0010 表紙.jpg') === 10 &&
    zipEntryNumber('Series/Volume/page-0002.jpg') === 2,
    'numbered parent directories do not affect page order');
  for (const stem of ['界'.repeat(190), '😀'.repeat(190)]) {
    const name = bookWalkerPageName(12345, stem + '.xhtml');
    check('Unicode filenames fit the 255-byte component limit',
      new TextEncoder().encode(name).length <= 255 && !name.includes('\uFFFD') && name.endsWith('.jpg'), name);
  }
  check('missing source still has a padded ordinal', bookWalkerPageName(1, '') === '0001.jpg', '0001.jpg');

  check('naming does not read bookmarks or patch storage',
    storageReads === 0 && Storage.prototype.setItem === originalSetItem, 'no storage side effects');

  const blob = new Blob(['page'], { type: 'image/jpeg' });
  const zip = await buildStoreZip(names.slice().reverse().map(name => ({ path: name, blob })));
  const bytes = new Uint8Array(await zip.arrayBuffer());
  const view = new DataView(bytes.buffer);
  const decoder = new TextDecoder();
  const zipNames = [];
  let offset = 0;
  while (view.getUint32(offset, true) === 0x04034b50) {
    const nameLength = view.getUint16(offset + 26, true);
    const extraLength = view.getUint16(offset + 28, true);
    zipNames.push(decoder.decode(bytes.subarray(offset + 30, offset + 30 + nameLength)));
    offset += 30 + nameLength + extraLength + view.getUint32(offset + 18, true);
  }
  check('ZIP entries are in page order even when submitted in reverse',
    zipNames.join('|') === names.join('|'), zipNames.join(', '));

  const streamed = [];
  let trialZip;
  const noop = () => {};
  vm.runInContext(fragment('core/31-mokuro.js') + fragment('sites/bookwalker/21-trial-zip.js') +
    '\nglobalThis.downloadTrialZip = downloadTrialZip;', context);
  Object.assign(context, {
    performance: { now: () => 0 },
    cdnFetch: async () => ({ ok: true, blob: async () => blob }),
    authQuery: () => '', makeUploadBarUpdater: () => noop,
    setBar: noop, reportRunProgress: noop,
    ensureBridgeRunning: async () => true, waitForBridgeIdle: async () => true,
    mokuroStartSession: async () => ({ session_id: 'test', safe_title: 'test' }),
    safeLogText: String,
    bridgeSessionPath: (id, route) => id + route,
    mokuroBridgePost: async (route, timeout, fd) => {
      streamed.push([fd.get('filename'), Number(fd.get('page_num')), fd.get('page').name]);
      return { ok: true, json: async () => ({}) };
    },
    URL: { createObjectURL: value => { trialZip = value; return 'blob:test'; }, revokeObjectURL: noop },
    document: { body: { appendChild: noop }, createElement: () => ({ click: noop, remove: noop }) },
    setTimeout: noop,
  });
  const bar = () => ({ wrap: { style: {} }, fill: { style: {} }, labRate: {} });
  const ui = { barDownload: bar(), barDescramble: bar(), barMokuro: bar(), barUpload: bar() };
  const fid = 'OEBPS/text/表紙 page.xhtml';
  const config = { [fid]: { FileLinkInfo: { PageCount: 2 } } };
  const expected = ['0001 表紙 page.jpg', '0002 表紙 page.jpg'];
  const trialOk = await context.downloadTrialZip(ui, config, [{ file: fid }], 'test', {}, 'zip', {}, 'test');
  const trialBytes = Buffer.from(await trialZip.arrayBuffer());
  check('trial ZIP preserves manifest names for multiple images per source',
    trialOk && expected.every(name => trialBytes.includes(Buffer.from(name))), expected.join(', '));
  const ocrOk = await context.downloadTrialZip(ui, config, [{ file: fid }], 'test', {}, 'ocr', {}, 'test',
    { skipCover: true, pollBridgeStatus: false, deferFinalize: true });
  check('trial OCR sends Unicode filenames and explicit page ordinals',
    ocrOk && JSON.stringify(streamed) === JSON.stringify(expected.map((name, i) => [name, i + 1, name])),
    JSON.stringify(streamed));

  const failed = results.filter(pass => !pass).length;
  console.log(failed ? '\n' + failed + ' FAILED' : '\nALL ' + results.length + ' CHECKS PASSED');
  process.exitCode = failed ? 1 : 0;
})().catch(error => { console.error('FATAL', error); process.exitCode = 1; });
