import Mathlib.Analysis.InnerProductSpace.TwoDim

/-!
# Orientation transport and signed area forms

This small linear-algebra bridge applies to arbitrary continuous linear
equivalences between two-dimensional real inner-product spaces.  Unlike the
standard determinant API, it does not require source and target to be the
same vector space.  It will be used to turn local orientation transport into
the sign of a chart Jacobian.
-/

open Module

namespace GromovFilling

noncomputable section

/-- If a continuous linear equivalence carries an orthonormal frame's
orientation to the target orientation, its oriented area form is positive on
the image frame. -/
theorem orientation_map_eq_areaForm_pos
    {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [Fact (Module.finrank ℝ F = 2)]
    (b : OrthonormalBasis (Fin 2) ℝ E)
    (o : Orientation ℝ F (Fin 2))
    (e : E ≃L[ℝ] F)
    (h : Orientation.map (Fin 2) e.toLinearEquiv b.toBasis.orientation = o) :
    0 < o.areaForm (e (b 0)) (e (b 1)) := by
  let p : OrthonormalBasis (Fin 2) ℝ F :=
    o.finOrthonormalBasis (by norm_num) Fact.out
  have hp : p.toBasis.orientation = o := by
    simpa only [p] using
      (o.finOrthonormalBasis_orientation (by norm_num)
        (Fact.out : Module.finrank ℝ F = 2))
  have hmap : (b.toBasis.map e.toLinearEquiv).orientation =
      p.toBasis.orientation := by
    rw [Module.Basis.orientation_map]
    exact h.trans hp.symm
  have hdet : 0 < p.toBasis.det (b.toBasis.map e.toLinearEquiv) := by
    rw [← p.toBasis.orientation_eq_iff_det_pos]
    exact hmap.symm
  have hframe : (b.toBasis.map e.toLinearEquiv : Fin 2 → F) =
      ![e (b 0), e (b 1)] := by
    funext i
    fin_cases i <;> simp
  rw [hframe] at hdet
  rw [o.areaForm_to_volumeForm, o.volumeForm_robust p hp]
  exact hdet

/-- If a continuous linear equivalence carries an orthonormal frame's
orientation to the opposite target orientation, its oriented area form is
negative on the image frame. -/
theorem orientation_map_eq_neg_areaForm_neg
    {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [Fact (Module.finrank ℝ F = 2)]
    (b : OrthonormalBasis (Fin 2) ℝ E)
    (o : Orientation ℝ F (Fin 2))
    (e : E ≃L[ℝ] F)
    (h : Orientation.map (Fin 2) e.toLinearEquiv b.toBasis.orientation = -o) :
    o.areaForm (e (b 0)) (e (b 1)) < 0 := by
  have hpos := orientation_map_eq_areaForm_pos b (-o) e h
  simpa only [Orientation.areaForm_neg_orientation, LinearMap.neg_apply, neg_pos] using hpos

#print axioms orientation_map_eq_areaForm_pos
#print axioms orientation_map_eq_neg_areaForm_neg

end

end GromovFilling
