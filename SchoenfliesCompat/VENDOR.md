# Graph compatibility modules for Jordan–Schönflies

`Basic` and `Subgraph` are namespace-isolated copies from the repository's
pinned mathlib commit
`8a178386ffc0f5fef0b77738bb5449d50efeea95`. `Delete` and `Maps` are
compatibility ports of the corresponding mathlib APIs at commit
`db584cd6d46c92f209a44c0f1c829460d327499d`. Together, the four modules supply
exactly the multigraph layer required by the vendored Jordan–Schönflies closure
while the main project remains on Lean 4.29.0 and mathlib v4.29.0.

All definitions live in namespace `SchoenfliesGraph`. This alpha-renaming is
required because the independently pinned HOL Light Jordan-curve development
defines a different global `Graph` structure with overlapping projection
names. The port also adjusts record fields, generated projection names, and
set-difference API names. The upstream Apache-2.0 license is included as
[`LICENSE`](LICENSE).
