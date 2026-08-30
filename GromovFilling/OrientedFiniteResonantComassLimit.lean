import GromovFilling.FiniteResonantRiemannianComassLimit
import GromovFilling.OrientedRiemannianDensity

/-!
# Frame-free oriented finite resonant comass limits

The pointwise finite-to-infinite comass theorem is naturally proved in one
orthonormal tangent frame.  This file removes that auxiliary frame from its
conclusion: the absolute intrinsic oriented density has the same value in
every orthonormal frame, so the coherent Fourier error sequence controls the
canonical oriented magnitude directly.
-/

open Bundle Filter Manifold MeasureTheory
open scoped Bundle InnerProductSpace Manifold Topology

namespace GromovFilling

noncomputable section

/-- At every regular interior tangent plane, the intrinsic oriented finite
resonant densities satisfy the sharp infinite comass bound up to one scalar
error sequence tending to zero.  The auxiliary coherent Fourier field and
orthonormal frame have both been eliminated from the statement. -/
theorem exists_orientedFiniteResonantRiemannian_comass_error
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    [PseudoMetricSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
    [IsRiemannianManifold I M] [Fact (Module.finrank ℝ E = 2)]
    {boundary : UnitAddCircle → M}
    (hboundary : IsometricCircleBoundary boundary)
    (o : RiemannianTangentPlaneOrientation I M)
    (lam : ℝ) (hlam0 : 0 ≤ lam) (hlam : lam < Real.pi ^ 2 / 32)
    (x : M) (hx : I.IsInteriorPoint x)
    (hprofileDiff : ∀ᵐ t : ℝ ∂volume.restrict
      (Set.Ioc (-Real.pi) Real.pi),
      MDifferentiableAt I 𝓘(ℝ, ℝ)
        (oddDistanceProfile boundary (angleToUnitAddCircle t)) x)
    (hFourierDiff : ∀ k : ℕ,
      MDifferentiableAt I 𝓘(ℝ, ℂ)
        (oddProfileFourierMap boundary (oddMode k)) x) :
    ∃ error : ℕ → ℝ,
      Tendsto error atTop (nhds 0) ∧
      ∀ N : ℕ,
        |orientedFiniteResonantRiemannianSymplecticDensity
            I o boundary N lam x| ≤
          comassBound lam + |error N| := by
  let e := o.positiveOrthonormalBasis I x
  obtain ⟨f, _hf, _hanti, _hunit, _heq, herror, hbound⟩ :=
    exists_coherentProfile_finiteResonantRiemannian_comass_limit
      I hboundary lam hlam0 hlam x hx e hprofileDiff hFourierDiff
  let error : ℕ → ℝ :=
    finiteTruncationResonantBaseFirstError lam
      (oddProfileFourierMap boundary (oddMode 0) x)
      (fun n ↦ oddProfileFourierMap boundary (oddMode n.succ) x)
      (fun n ↦ fourierCoeffOn
        (by linarith [Real.pi_pos] : -Real.pi < Real.pi) f n)
  refine ⟨error, ?_, ?_⟩
  · simpa only [error] using herror
  · intro N
    rw [abs_orientedFiniteResonantRiemannianSymplecticDensity_eq_frame
      I o boundary N lam x e]
    simpa only [error] using hbound N

end

end GromovFilling

#print axioms
  GromovFilling.exists_orientedFiniteResonantRiemannian_comass_error
