import Wikipedia.SchoenfliesTheorem.JordanSchoenflies

/-!
# Jordan–Schönflies foundation for Lemma 5.4

This module exposes the vendored relative Jordan–Schönflies theorem through
the project umbrella.  It is the ambient-plane extension input needed to
remove the explicit odd-degree hypothesis from the manuscript-facing Jordan
coverage theorem.
-/

namespace GromovFilling

noncomputable section

/-- Every homeomorphism between two interval-parametrized Jordan curves in
the Euclidean plane extends to a self-homeomorphism of the plane. -/
theorem planeJordanSchoenflies_of_homeomorph
    {C C' : Set Schoenflies.Plane}
    (hC : Schoenflies.IsJordanCurve C)
    (hC' : Schoenflies.IsJordanCurve C')
    (e : C ≃ₜ C') :
    ∃ F : Schoenflies.Plane ≃ₜ Schoenflies.Plane,
      ∀ z : C, F z = e z :=
  Schoenflies.jordan_schoenflies_of_homeomorph hC hC' e

end

end GromovFilling

#print axioms Schoenflies.squareExtension
#print axioms Schoenflies.jordan_schoenflies
#print axioms Schoenflies.jordan_schoenflies_homeomorph
#print axioms GromovFilling.planeJordanSchoenflies_of_homeomorph
