# Fourier bounds for filling area

<div class="research-hero" markdown>
![A circle boundary, triangulated spanning surface, and Fourier traces](assets/hero.webp)
</div>

This project is a Lean 4 formalization of the Fourier, topology, planar area,
and certificate arguments accompanying Yimin Zhong's research note on
Gromov's filling-area problem.

!!! warning "Current verification boundary"
    The repository does not prove Gromov's conjecture. The manuscript proves
    lower bounds below the conjectural value `2π`. Lean verifies both headline
    theorems at the exact Riemannian-surface and orientation interfaces stated
    on the formalization page.

<div class="status-strip">
  <div><strong>6,677</strong><span>project declarations accepted by the live axiom audit</span></div>
  <div><strong>Lean 4.29</strong><span>pinned toolchain with mathlib 4.29 and a fixed Jordan input</span></div>
  <div><strong>MIT</strong><span>public source, reproducible CI, and explicit claim boundaries</span></div>
</div>

## What is verified

The kernel-checked development includes exact Fourier coefficients, the Givens
mixing matrix, dominant-harmonic Jordan curves, integer circle degree, finite
mod-2 surface obstruction, boundary-regular Radó triangulation, faithful
compact-surface polygonal classification, planar area and Jacobian
inequalities, rigorous constant evaluation, off-diagonal
logarithmic-sine-kernel positivity, de Sitter profile identities, finite
one-high-leg Gram/Rayleigh algebra, exact scalar resonance-trace arithmetic,
and end-to-end assembly of Theorems 1.1 and 1.2.

The general glued-polygon theorem now handles every fixed-point-free
involutive side pairing, including orientation-reversing identifications. The
lower boundary obstruction is derived automatically rather than supplied as a
caller assumption.

## Explore the project

<div class="grid cards" markdown>

-   **Mathematics**

    Follow the argument from boundary distance profiles to Fourier maps,
    Jordan coverage, Jacobian budgets, and explicit constants.

    [Read the mathematical map](mathematics.md)

-   **Formalization boundary**

    See exactly which manuscript statements are verified, partial, or still
    open, with no headline overclaim.

    [Inspect the claim boundary](formalization.md)

-   **Lean modules**

    Navigate the source by proof layer and find the canonical umbrella import.

    [Browse the module map](modules.md)

-   **Verification**

    Reproduce the build and understand the source scan, import check, and live
    axiom audit.

    [Run the verification](verification.md)

-   **Reusable libraries**

    See how the general topology, geometry, and analysis infrastructure can be
    extracted and contributed without changing the verified theorem artifact.

    [Review the contribution roadmap](library-contributions.md)

</div>

## Current frontier

Lemma 5.4 and both headline surface bounds are now end-to-end verified at
their exact interfaces. Theorem 1.2 uses the project-defined conventional
surface orientation and derives its controlled boundary direction for the
supplied parametrization or its reversal. Broader formulations remain outside
the headline closures, including:

1. Riemannian eikonal and parameter-integral differentiation;
2. a standalone global differential-form Stokes/comass API;
3. an equivalence with a future generic library-level orientation API.

The repository keeps those independent boundaries visible. They are not
assumptions of either headline endpoint, and the project does not replace them
with custom axioms or conclusion-bearing hypotheses.
