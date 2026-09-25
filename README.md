# Omnimanga Native Downloader · v2.0.0

One userscript for **BookWalker**, **CMOA** and **ebookjapan**. It reads the
viewer's own signed CDN URLs, fetches every page file directly, rebuilds each
page offline at full resolution, and hands you either a ZIP or a finished volume
in your Mokuro reader, without turning a single page.

**[Install from GreasyFork](https://greasyfork.org/en/scripts/597313-omnimanga-native-downloader)** ·
[raw userscript](omnimanga-native-downloader.user.js) ·
[changelog](CHANGELOG.md) · MIT

Only need one store? There are single-store builds too:
[BookWalker](https://greasyfork.org/en/scripts/594508-bookwalker-native-downloader) ·
[CMOA](https://greasyfork.org/en/scripts/597317-cmoa-native-downloader) ·
[ebookjapan](https://greasyfork.org/en/scripts/597318-ebookjapan-native-downloader).

<table align="center">
  <tr>
    <td align="center">
      <img width="400" alt="image" src="https://github.com/user-attachments/assets/1f459486-330e-4fdc-b7a6-d0280b945cc4" />
    </td>
    <td align="center">
      <img width="400" alt="image" src="https://github.com/user-attachments/assets/155da3f4-bafd-4831-a16e-100980adf1ba" />
    </td>
    <td align="center">
      <img width="400" alt="image" src="https://github.com/user-attachments/assets/3a23070e-4839-4331-a558-0c9c86bf3f95" />
    </td>
  </tr>
</table>

## Features

- **Download the open book as a ZIP.** Full editions, trial/free samples and
  subscription viewers. BookWalker pages use names such as `0001 sourcename.jpg`
  inside the archive, derived from manifest order and source filenames, independent
  of reading position. Names fit within 255 UTF-8 bytes, including the extension.
  Each image is saved as published rather than as displayed. Rename the file `.cbz` for CBZ readers.
- **Or run it through Mokuro OCR.** Pages stream to
  [mokuro-bridge](https://github.com/GolyBidoof/mokuro-bridge) as they are
  descrambled and come back as the `.cbz` / `.mokuro` / `.webp` trio that
  [reader.mokuro.app](https://reader.mokuro.app/) reads. Choose the destination
  per run (local, MEGA, Google Drive, OneDrive, WebDAV) and jump straight to
  the finished volume from the panel.
- **Reading-stats cards, before you commit to a book.** [Natively](https://learnnatively.com)
  level with its JLPT-band colours, ratings and reader counts, plus
  [Manga Kotoba](https://manga-kotoba.com) word totals, unique words, used-once
  rate and lexical density.
- **"Also available on" store links** *(combined build only)*. Pills under the
  book details tell you whether the other shops carry the series, what the volume
  costs (`¥792`) and how many volumes are free (`2 vols free`), linking to the
  shop's product page, never a viewer. A shop that does not carry the book gets
  no pill at all, so the card never claims a book is somewhere it isn't.
- **Resume, not restart.** Pages are cached as they arrive. An interrupted run
  picks up where it stopped, a partial failure names the missing pages, and the
  next run fetches only those.
- **Parallel end to end.** Pages are prefetched in a bounded window and
  descrambled across a worker pool, with live fetch and descramble bars. Fetches
  are also spread across every origin available: the page, Tampermonkey's
  background context, a trailing-dot host and the bridge's fetch-proxy ports.
  Chrome's 6-connections-per-origin cap is per port, so this is real bandwidth:
  measured **294 concurrent sockets** with the bridge running, against 6 without.
- **Pick the image format.** JPEG q0.92 (default), WebP, lossless or PNG. The CDN
  already serves a lossy JPEG, so this is a second generation; lossless pays off
  mainly on flat line art.
- **A panel that stays out of the way.** Draggable, resizable, minimisable, with
  ARIA roles; remembers its size and position; **»** flaps it off-screen; and it
  never takes the arrow keys, so Left/Right still turn the viewer's pages.

## Install

1. Install a userscript manager: [Tampermonkey](https://www.tampermonkey.net/)
   (Chrome/Firefox/Edge) or [Violentmonkey](https://violentmonkey.github.io/).
2. [Install Omnimanga Native Downloader](https://greasyfork.org/en/scripts/597313-omnimanga-native-downloader)
   from GreasyFork, or open
   [`omnimanga-native-downloader.user.js`](omnimanga-native-downloader.user.js)
   and click **Install**.
3. Open a book in any of the three viewers and use the panel.

> **Turn off other BookWalker userscripts first.** This script works by reading
> the viewer's own network traffic to capture the signed CDN URLs it downloads
> with. Other downloaders and page-capture scripts interfere with that traffic.
> Disable them in your userscript manager before running this one.

The file is self-contained: the only thing it needs from the network is the book
itself. It runs the same on Windows, macOS and Linux, and saved archives are
filesystem-agnostic: ZIP entry names are UTF-8-flagged so Japanese titles
survive Windows Explorer, and every folder and file name is sanitised against
Windows rules (reserved characters, device names like `CON`/`NUL`, trailing dots
and spaces).

### Permissions

Tampermonkey asks for cross-origin access to `learnnatively.com`,
`manga-kotoba.com` and the three storefronts. That permission powers **only** the
stats cards and the store pills, both of which read each site's own public page.

- **Accept**: stats and store links load directly.
- **Decline**: downloading and OCR work exactly as before. The Natively card is
  fetched through a public CORS proxy instead, and the store pills are simply not
  shown. If that proxy is unreachable the card says so and nothing breaks.

Change it later under Tampermonkey → this script → **Settings → User
permissions → External connections**.

## How it works

Each store gets its own module; everything the user sees is shared. There is no
bundler and no minifier: the shipped file is the concatenation of `src/` in
manifest order, so it stays readable and can be diffed against the repository
line for line ([src/README.md](src/README.md)).

| Stage | BookWalker | CMOA | ebookjapan |
| --- | --- | --- | --- |
| **Capture** | Passively reads the viewer's `fetch`/XHR traffic for the signed CloudFront auth and the encrypted page manifest | Reads the page list and descramble geometry from the reader | `open_book` → `get_drm` on the viewer's own API |
| **Fetch** | CDN files, through every lane that can be opened | `sbcGetImg.php`, walking a quality × token ladder | The viewer's page endpoints |
| **Rebuild** | Per-page permutation of `32×32` tiles, reversed in a worker pool | Tiles reassembled on a canvas | Descrambled by the viewer's own wasm module |
| **Shared** | Panel and bars · run harness · Mokuro session · ZIP naming and writer · page cache and resume · stats and store cards | | |

The pipeline, in short:

1. **Capture** while you read. Nothing is requested by the script at this stage.
2. **Decrypt and plan** the page manifest, so the full page list is known before
   anything is downloaded.
3. **Fetch** in parallel. Signed URLs last only minutes, so auth is re-negotiated
   mid-run through the viewer's own endpoints, with a request budget per policy,
   403/429 breakers with cooldowns, and retry rounds, so there is no 403 wall at
   page 87.
4. **Rebuild** each page offline and verify it.
5. **Deliver**: pack a ZIP, or stream pages to the bridge as they finish so
   capture and OCR overlap.

### The BookWalker tile shuffle

BookWalker does not serve plain images. Each page is cut into scrambled `32×32`
blocks before it reaches the CDN and the viewer reassembles them on a canvas,
which is why capture-based scripts only ever see screen output. This script
decrypts the manifest, derives each page's seeds, and applies the inverse
permutation with direct canvas blits plus a JPEG re-encode, then crops to the
declared size so no padding edge remains. The seed derivation, PRNG, permutation
and block-move logic were validated byte-for-byte against live captures; all of
it runs in Web Workers.

### The OCR pipeline

Three projects, one pipeline:

- **[GolyBidoof/mokuro](https://github.com/GolyBidoof/mokuro)**: this project's
  OCR engine, a fork of [kha-white/mokuro](https://github.com/kha-white/mokuro)
  that batches text-line crops into single inference calls, loads pages
  concurrently and picks hardware-aware defaults. Output is byte-format identical
  to upstream and measured **2.09× faster** (173 s vs 362 s on a 187-page volume).
- **[GolyBidoof/mokuro-bridge](https://github.com/GolyBidoof/mokuro-bridge)**: the
  local FastAPI server on `127.0.0.1:62642` that runs mokuro for the script. It
  creates a session per volume, OCRs pages in chunks as they arrive (default 8
  pages, 1.5 s idle flush), assembles the `.cbz` / `.mokuro` / `.webp` trio, and
  keeps it or uploads it. It also doubles as the socket multiplier above: its
  fetch-proxy ports are advertised on `/health` and used as extra lanes.
- **[reader.mokuro.app](https://reader.mokuro.app/)**: the hosted reader that
  shows each page beside its selectable OCR text.

For OCR you run the bridge locally; it is configured in its own terminal, not in
the browser, and by default results stay on your machine under `output/`.

## Project layout

| Path | Description |
| --- | --- |
| `omnimanga-native-downloader.user.js` | The combined userscript (BookWalker, CMOA, ebookjapan) |
| `bookwalker-only.user.js`, `cmoa-only.user.js`, `ebookjapan-only.user.js` | Single-store builds from the same sources |
| `src/` | The sources; see [src/README.md](src/README.md) |
| `build.mjs`, `bump.mjs` | Assembles `src/` into the artifacts; bumps the version |
| `tools/` | Release helpers: `release-notes.mjs`, `sync-urls.mjs` |
| `tests/` | Hermetic browser and artifact tests (`npm test`) |
| `.github/workflows/` | CI and release automation; see [RELEASING.md](RELEASING.md) |

> **Do not edit a `.user.js` by hand**: they are generated. Edit `src/` and run
> `npm run build`; `npm run check:build` fails when the two disagree.
>
> To ship: `npm run bump <part>`, add the changelog section, `npm test`, commit,
> then tag and push. See [RELEASING.md](RELEASING.md).

## Credits

**Built by [GolyBidoof](https://github.com/GolyBidoof)**, author and maintainer of
this userscript and of the companion [mokuro-bridge](https://github.com/GolyBidoof/mokuro-bridge),
**together with DeepSeek V4 Flash**, the coding model that reverse-engineered
BookWalker's protocol, ported the crypto and descramble logic, and iterated
against live captures until every step matched byte-for-byte.

- **[BookWalker](https://bookwalker.jp)**, **[CMOA](https://www.cmoa.jp)** and
  **[ebookjapan](https://ebookjapan.yahoo.co.jp)**, for the services this tool
  works with. All downloaded content remains subject to their terms of service.
- **[Brandon](https://learnnatively.com/user/brandon/)**, founder and lead
  developer of [Natively](https://learnnatively.com), for the difficulty levels,
  JLPT-band colours, ratings and book metadata shown in the stats card.
- **[ChristopherFritz](https://community.wanikani.com/u/christopherfritz)**, who
  built [Manga Kotoba](https://manga-kotoba.com) alone, for the vocabulary
  statistics. Its English word data builds on
  [JMDict](https://www.edrdg.org/jmdict/j_jmdict.html).
- **[kha-white/mokuro](https://github.com/kha-white/mokuro)** and
  **[manga-ocr](https://github.com/kha-white/manga-ocr)**, the upstream OCR
  engine and model; detection uses
  [comic-text-detector](https://github.com/dmMaze/comic-text-detector).
- **[megatools](https://megatools.megous.com)**, the MEGA upload backend.
- **[aaa4xu/bookworm](https://github.com/aaa4xu/bookworm)**, the offline
  BookWalker client whose algorithm the descramble implementation was validated
  against, and **[VermiIIi0n/fuckBookWalker](https://github.com/VermiIIi0n/fuckBookWalker)**,
  an early inspiration for the direct-download approach.

"BookWalker", "CMOA" and "ebookjapan" are trademarks of their respective owners.
The store links are ordinary search and product URLs, and this project is not
affiliated with or endorsed by any of them. Natively and Manga Kotoba data belong
to their respective projects.

## Disclaimer

For **personal, lawful use**: download only content you are entitled to access
(purchased books, free samples, trial chapters). Respect the services' terms of
service and the rights of authors and publishers. The maintainer assumes no
liability for misuse.

## License

[MIT](LICENSE)
