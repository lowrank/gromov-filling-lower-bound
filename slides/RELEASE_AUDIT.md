# Gold-standard release audit

Audit date: 2026-09-04

## Frozen inputs and artifacts

- Manuscript repository commit:
  `f166e04054b397efdcb7c1ac5217ede715c1cfd0`
- Manuscript source blob:
  `42a9c8d2e856943f6109031f8bf914ae65872d63`
- Formalization-ledger blob:
  `87e8e97236dff07e615a6c1a463fb95328034e7c`
- Source-retention boundary: current `main` removed the draft at `ecb50eb`
  pending an official arXiv source; all deck claims and private source links
  remain pinned to the immutable `f166e04` snapshots above.
- Deck-source SHA-256:
  `306a37c4e76033a29f45f3b95d8fd946b3045f537df6588ccf3a6e71680b1d3b`
- Canonical-PDF SHA-256:
  `15ff189f5888c9f3202be62b5f89e309b3494bcd014fb19cd0a86a5b42f4e6b8`

## Audit A: mathematical claims and scope

- All 21 `fr:*` labels (20 numbered core frames plus the unnumbered close)
  reconcile exactly with [`CLAIM_LEDGER.md`](CLAIM_LEDGER.md).
- Every load-bearing formula, decimal, orientation hypothesis, parameter
  range, and formalization badge was compared with the frozen manuscript and
  `FORMALIZATION.md` loci recorded in the ledger.
- The deck consistently distinguishes the open `2π` conjecture, the
  orientation-free `14 ζ(3)/π` theorem, the oriented strict `5.38982446`
  theorem, and the method-specific one-high-leg ceiling below `5.466`.
- Primary references were cross-checked against their DOI, MathSciNet, or
  arXiv records; the PDF exposes clickable DOI/MR/arXiv links.

Result: pass.

## Audit B: first-year-graduate story and pacing

- The core has one visible chain: no-shortcuts metric data, distance
  profiles, odd Fourier coordinates, one Jacobian budget, covered planar
  regions, and area lower bounds.
- Definitions precede use; specialist vocabulary is translated on first use;
  proof-detail frames are placed in backup.
- Core text counts range from 78 to 122 extracted words per numbered frame.
  The two densest frames were inspected at full resolution and remain legible.
- Every core frame has a speaker cue. Optional switches support 35-, 55-, and
  90-minute variants without forking the source.

Result: pass.

## Audit C: build, pagination, and visual integrity

- Clean `latexmk -pdf -interaction=nonstopmode -halt-on-error` build: pass.
- Determinism: `SOURCE_DATE_EPOCH` is pinned to the frozen manuscript commit
  time; two clean builds on the release toolchain (pdfTeX 1.40.25, TeX Live
  2023/Debian) produced byte-identical PDFs.
- Cross-toolchain check: Greenwood's pdfTeX 1.40.29 / TeX Live 2026 build also
  passed all release gates. It produced distribution-dependent PDF bytes, so
  `make check` uses the ignored `.build/` directory and leaves the canonical
  release artifact untouched.
- Log scan for TeX errors, undefined references/citations, PDF-string
  warnings, and overfull/underfull boxes: zero findings.
- Pagination: 20 numbered core frames, unnumbered title and close, and 16
  separately numbered backup frames; 38 physical pages; no overlays.
- PDF metadata: exact title and authors present.
- Font audit: all 28 listed fonts embedded and subsetted.
- Structural rendering check: Ghostscript `nullpage` pass. (`qpdf` was not
  available in the release environment.)
- Visual audit: all 38 pages rastered after the final TeX change and inspected
  as contact sheets; title, close, diagrams, dense formulas, formalization
  table, and references were additionally inspected at full resolution.

Result: pass.

## Reproduce

```sh
cd slides
make distclean
make
make check
sha256sum gromov_filling_mother_deck.tex gromov_filling_mother_deck.pdf
```

Release verdict: **GOLD STANDARD** — the claims, teaching architecture,
compiled artifact, and documented source boundary all pass their gates.
