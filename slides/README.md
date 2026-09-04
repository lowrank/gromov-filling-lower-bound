# Gromov filling-area Beamer mother deck

This directory contains the master teaching deck for Gromov's filling-area
conjecture and the Fourier/resonance program developed in this repository.
The intended audience is first-year graduate students who know basic real
analysis, linear algebra, and the fundamental group, but may not know
Riemannian geometry, geometric measure theory, or calibrations.

## Files

- [`gromov_filling_mother_deck.tex`](gromov_filling_mother_deck.tex) is the
  editable mother deck, including speaker notes and optional core modules.
- [`gromov_filling_mother_deck.pdf`](gromov_filling_mother_deck.pdf) is the
  canonical compiled deck.
- [`CLAIM_LEDGER.md`](CLAIM_LEDGER.md) maps every load-bearing core frame to
  its manuscript locus and scope guard.
- [`RELEASE_AUDIT.md`](RELEASE_AUDIT.md) records the reproducible release
  evidence for the canonical PDF.
- [`Makefile`](Makefile) provides the build and release gates.

## Source contract

The mathematical source of record is
[`../fourier_resonant_filling_area_v3.tex`](../fourier_resonant_filling_area_v3.tex)
as present at repository commit
`f166e04054b397efdcb7c1ac5217ede715c1cfd0` (file blob
`42a9c8d2e856943f6109031f8bf914ae65872d63`). The claim-status source is
[`../FORMALIZATION.md`](../FORMALIZATION.md) at the same repository commit
(file blob `87e8e97236dff07e615a6c1a463fb95328034e7c`).

The deck must preserve four boundaries:

1. Gromov's conjectural sharp value is `2π`; the conjecture is not proved.
2. The paper proves `14 ζ(3)/π` without orientability and the strict bound
   `5.38982446` with orientation.
3. The one-high-leg ceiling applies to a specified resonance family, not to
   every nonlinear Fourier method.
4. Lean verification is reported only at the exact interfaces recorded in
   `FORMALIZATION.md`; partial and open manuscript items stay visibly partial
   or open.

## Teaching architecture

The core talk has 20 numbered frames, plus an unnumbered title and close. It
uses one recurring story:

```text
no-shortcuts boundary data
        -> distance profiles
        -> odd Fourier coordinates
        -> one Jacobian budget
        -> planar coverage certificates
        -> explicit area lower bounds.
```

The first half develops the orientation-free linear certificate. The second
half explains why a resonant cubic perturbation gains boundary action at
first order while paying comass only at second order. Technical derivations,
the spectral ceiling, formalization details, and linked references live in
backup frames so the main narrative remains readable.

The mother deck is venue-neutral. A speaker can shorten it by omitting the
optional modules marked in the TeX source; the full PDF remains the canonical
archive and question bank.

## Build and adapt

From this directory, run:

```sh
make
make check
```

The full release contains 20 numbered core frames, an unnumbered title and
close, and 16 separately numbered backup frames: 38 physical PDF pages in
all. There are no overlays, so source frames and physical pages reconcile
directly. The Makefile pins `SOURCE_DATE_EPOCH` to the frozen manuscript
commit time so clean builds produce the same canonical PDF bytes.

Five switches near the top of the TeX source control optional core modules:
`showoddslack`, `showcalibration`, `showbarriers`, `showfrontier`, and
`showverification`. Keep all five enabled for the mother deck. Suggested
venue cuts are:

- 35 minutes: omit the odd-slack, barriers, frontier, and verification
  modules; use backup only for questions;
- 55 minutes: present the complete 20-frame core;
- 90 minutes or a mini-course: present the core and insert selected backup
  derivations immediately after their parent frames.

Every core frame and the title/close have a `\\note{...}` speaker cue. To
prepare a presenter copy, enable Beamer's notes option locally; do not commit
that presenter-only rendering in place of the canonical audience PDF.

## Release bar

Before a PDF is released:

- reconcile every load-bearing frame with [`CLAIM_LEDGER.md`](CLAIM_LEDGER.md);
- compile from a clean auxiliary state and reject errors, undefined
  references/citations, PDF-string warnings, and unexplained box warnings;
- verify title/author PDF metadata and embedded fonts;
- reconcile source frames, numbered frames, backup frames, and physical PDF
  pages;
- raster and inspect every page after the last source change;
- stage the source, README, ledger, and canonical PDF as one release unit.

The current release evidence is frozen in
[`RELEASE_AUDIT.md`](RELEASE_AUDIT.md).
