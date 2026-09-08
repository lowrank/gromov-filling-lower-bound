# Repository contract

This repository formalizes the Fourier filling-area paper by Le Chen,
Xiaolong Li, and Yimin Zhong. Read `docs/current-manuscript.md` first, then
the relevant Lean declarations. `FORMALIZATION.md` also retains a historical
ledger whose numbers differ from the current manuscript.

- Theorems 1.1, 1.2, and 4.1 are the headline targets. The orientable bound is
  `5.40154`, with parameter `1/25`; the all-parameter interval is
  `0 ≤ λ < π²/32`.
- Preserve the exact geometric hypotheses and the project-defined
  `RiemannianSurfaceOrientation` boundary. Broader Hilbert-space statements
  remain partial. The project does not prove the conjectural `2π` bound.
- Keep unavailable inputs visible. Never add proof placeholders, custom
  axioms, unsafe declarations, or native reduction to the mathematical sources.
- Keep the Lean, mathlib, and Jordan revisions pinned unless a maintainer
  authorizes an upgrade.
- Use GitHub CI for full Lean/Lake builds. Do not run them on Dell or Greenwood.
- Use small feature branches, atomic commits, and pull requests. Do not push
  directly to `main`; require terminal CI success before requesting review.
- `scripts/verify.sh` runs the complete reproduction. The live audit driver is
  checker tooling, outside the mathematical import closure. Preserve positive
  and negative evidence separately and verify exact source and declaration sets.
- Keep historical receipts immutable. Record a new receipt after a successful
  live audit of the new candidate. A checked branch is not a merged release.
- Keep private manuscript editing, correspondence, and local execution records
  outside this repository. Changing visibility also exposes Git history.
