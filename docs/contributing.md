# Contributing

Contributions should be small, claim-bounded, and easy to review against the
manuscript.

## Proof workflow

1. Start from a fresh `main` and create a focused feature branch.
2. State the exact theorem contract before editing: objects, hypotheses,
   quantifier order, conclusion, and manuscript dependency.
3. Keep unavailable foundations visible in theorem signatures. Do not hide an
   open theorem behind a project axiom.
4. Run the static source scan before committing.
5. Push an atomic commit and open a pull request with a precise
   formalized-versus-remaining statement.
6. Require terminal CI success before declaring the proof ready.

## Project constraints

- Do not change Lean, mathlib, or Jordan curve pins without maintainer
  agreement.
- Do not push directly to `main`.
- Do not introduce placeholder, custom axiom, unsafe, or native reduction
  escapes.
- Keep the root statement ledger synchronized with manuscript theorem status.

## Preview the documentation

```bash
python3 -m venv .venv-docs
.venv-docs/bin/pip install -r requirements-docs.txt
.venv-docs/bin/mkdocs serve
```

Before opening a documentation pull request, run:

```bash
.venv-docs/bin/mkdocs build --strict
```

The Pages workflow deploys the exact `main` documentation tree after merge.

