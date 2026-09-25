# Tests

Browser-driven checks for the userscript (built from `src/`; run
`npm run build` first, or `npm run check:build` to see whether it is stale). The default
suite loads the userscript into headless Chrome against local stub servers; the
live bridge check is opt-in.

```sh
npm install          # puppeteer
npm run browser      # one-time Chrome download for puppeteer
npm test             # hermetic tests
npm test -- lane     # only files whose name contains "lane"
npm run test:bridge  # opt-in live bridge check (needs ~/Projects/mokuro-bridge)
```

Each script prints `ALL n CHECKS PASSED` on success and exits non-zero
otherwise, so they work individually (`node tests/test_lanes.js`) or via
`npm test`.

| File | Covers |
| --- | --- |
| `test_lanes.js` | lane balance, GM fallback, 403 recovery, inflight de-dupe |
| `test_dot_lane.js` | trailing-dot lane probing and fallback |
| `test_edge_lane.js` | HTTP/2 edge mirror lane |
| `test_proxy_parking.js` | helper-port parking and recovery after cooldown |
| `test_descramble_equivalence.js` | descrambled output is byte-identical to reference |
| `test_bookwalker_naming.js` | BookWalker page names and ZIP entry order across double-digit pages |
| `test_image_codec.js` | format/quality resolution, emitted type, extension |
| `test_ui_panel.js` | panel readout, popovers, format picker and link |
| `test_site_dispatch.js` | adapter selection per host, capture install, BookWalker fallback |
| `test_cmoa_adapter.js` | full CMOA ZIP run: detection, clean title, naming, quality ladder, descramble |
| `test_cmoa_ocr.js` | CMOA mokuro path and transport lanes: session title, page order/naming, early cover, finalize, descrambled bytes, dot lane, host-scoped proxy ports |
| `test_split_builds.js` | every target in `src/targets.json`: header, version, match/connect lists, module isolation, and each artifact booted in Chrome |
| `test_artifacts.js` | every built artifact on disk compiles (as a script and as a function body), is not truncated or stale, and carries no excluded module - no browser needed |
| `test_availability.js` | cross-store "also available on" card; skips an artifact that does not carry the module |
| `test_bridge_e2e.js` | opt-in live mokuro-bridge check (`:62642`) |

`tests/_userscript.js` loads the built userscript for injection with the bridge
URL pointed at a closed port. The suite has to be hermetic: with the real mokuro
bridge running, its 48 fetch-proxy ports would be discovered by every test page
and mixed into the lane pool, turning distribution assertions into measurements
of the bridge instead of the code. Tests that want a bridge supply their own stub
and pass `{ bridge: true }`.

`tests/tls/` holds a self-signed localhost certificate, used so the page can
serve HTTPS (a secure context) while local stub servers stay on HTTP.

`test_cmoa_ocr.js` serves its synthetic storefront from a real local HTTPS
server reached as `www.cmoa.jp` through Chrome's `--host-resolver-rules`, rather
than fulfilling requests with puppeteer interception. That is deliberate:
interception cannot relay a binary multipart upload faithfully (`postData()` is
string-only, and the bridge uploads JPEGs), and it will not carry a
public-origin -> loopback hop at all, which is exactly the hop to the bridge.
