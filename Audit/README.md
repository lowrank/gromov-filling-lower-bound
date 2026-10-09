# Comparator audit

`UniversalFourierBound/` restates Theorem 1.1 (the universal Fourier bound,
`GromovFilling.riemannian_universal_fourier_bound`) for
[lean-pkg](https://github.com/lean-pkg/lean-pkg)'s comparator tier.

- `Defs.lean` imports Mathlib modules only and copies, verbatim, the project
  definitions the statement needs: the constant `14 ζ(3) / π`, isometric circle
  boundaries, the Riemannian two-Jacobian, chart and atlas area measures, and
  `ControlledInteriorAtlas` with its `areaMeasure`. A reader can check what
  "area" means here without trusting the rest of the project.
- `Challenge.lean` imports `Defs.lean` and states the theorem; its proof is
  `sorry` by design. It says that a controlled interior atlas exists and that
  every one gives the surface area at least `14 ζ(3) / π`. That is Theorem 1.1,
  because the project proves every controlled atlas computes the canonical
  measure (`ControlledInteriorAtlas.areaMeasure_eq`); asserting existence keeps
  the "every atlas" part from being vacuous.
- `Solution.lean` imports `Defs.lean` and the project, identifies each copied
  definition with the project's by `rfl`, and proves the statement from the
  project's Theorem 1.1. Sharing `Defs.lean` keeps the two sides on the same
  constants: when the Solution repeated the definitions, the project's extra
  instances changed how they elaborated and the comparator refused them.
- `comparator/config-universal-fourier-bound.json` lists the pair. The
  comparator checks that the Solution theorem has exactly the Challenge's type,
  uses only `propext`, `Classical.choice` and `Quot.sound`, and replays in a
  second kernel.

The comparator does not check that the Challenge matches the paper; that needs
a reader. Both files import specific Mathlib modules rather than `Mathlib`: the
Jordan curve dependency defines `Graph.vertexSet`, which full Mathlib also
defines, so the two cannot be imported together.

`Challenge.lean` is the only file allowed to contain `sorry`, and it and
`Defs.lean` may import only Mathlib (plus `Defs.lean`, for the challenge)
(`scripts/check_no_proof_escapes.sh`). Build with `lake build Audit`.
