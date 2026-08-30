import GromovFilling.FiniteResonantRiemannian
import GromovFilling.OddProfileParameterFourierBounds

/-!
# Unconditional metric-profile input to the finite resonant comass bound

This module feeds the sharp weighted-energy and first-mode bounds for the
genuine angular odd-distance profile into the finite Riemannian resonant
comass theorem.  The resulting statement no longer asks callers to supply
the manuscript's two pointwise profile inequalities.
-/

open Bundle Manifold

namespace GromovFilling

noncomputable section

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
attribute [local instance] normedSpaceTangentSpaceVectorSpace

/-- The genuine pulled-back finite resonant symplectic density satisfies the
verified comass bound without separate profile-energy or first-mode
hypotheses. -/
theorem abs_finiteResonantRiemannianSymplecticDensity_le_comassBound_of_isometricBoundary
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    [PseudoMetricSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    {boundary : UnitAddCircle → M}
    (hboundary : IsometricCircleBoundary boundary)
    (N : ℕ) (lam delta : ℝ) (x : M) (hx : I.IsInteriorPoint x)
    (e : OrthonormalBasis (Fin 2) ℝ (TangentSpace I x))
    (hdiff : ∀ k : Fin (N + 1),
      MDifferentiableAt I 𝓘(ℝ, ℂ)
        (oddProfileFourierMap boundary (oddMode k)) x)
    (cPos cNeg : Fin (N + 1) → ℂ)
    (hcolumn0 :
      finiteOddProfileRiemannianDerivative I boundary (N + 1) x (e 0) =
        finiteFourierTangentVector cPos cNeg)
    (hcolumn1 :
      finiteOddProfileRiemannianDerivative I boundary (N + 1) x (e 1) =
        finiteFourierQuarterTurnVector cPos cNeg)
    (hlam0 : 0 ≤ lam) (hlam : lam < Real.pi ^ 2 / 32)
    (hcoeffEnergy :
      finiteComplexEnergy cPos + finiteComplexEnergy cNeg ≤ 1)
    (hbase :
      |finiteBaseSymplecticDensity
        (finiteFourierTangentVector cPos cNeg)
        (finiteFourierQuarterTurnVector cPos cNeg)| ≤ 1 - delta)
    (hFull :
      ‖finiteFullShiftCorrelation cPos cNeg‖ ≤
        delta - 2 * finiteComplexEnergy cNeg) :
    |finiteResonantRiemannianSymplecticDensity
        I boundary N lam x e| ≤ comassBound lam := by
  exact abs_finiteResonantRiemannianSymplecticDensity_le_comassBound
    I N lam delta x hx e hdiff cPos cNeg hcolumn0 hcolumn1
      hlam0 hlam hcoeffEnergy hbase hFull
      (oddProfileFourierMap_first_add_nine_tail_energy_le_two
        hboundary x N)
      (norm_oddProfileFourierMap_first_le_four_div_pi hboundary x)

#print axioms
  abs_finiteResonantRiemannianSymplecticDensity_le_comassBound_of_isometricBoundary

end

end GromovFilling
