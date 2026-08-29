import GromovFilling.CanonicalBoundaryLocus

/-!
# Connected canonical boundary loci

The free `h_j` sides in a canonical surface word descend to pairwise
disjoint compact subsets of the surface quotient.  Consequently, when the
complete free-side locus is connected, the canonical normal form has exactly
one boundary block.  This is the connected-boundary step needed in Lemma 5.4.
-/

open Complex Set
open LeanEval.Topology.ClassificationOfSurfaces
open LeanEval.Topology.ClassificationOfSurfaces.NormalForm
open LeanEval.Topology.ClassificationOfSurfaces.SurfaceCellComplex

namespace GromovFilling

private theorem bdyPtOfReal_eq_iff (x y : ℝ) :
    ClosedUnitDisc.bdyPtOfReal x = ClosedUnitDisc.bdyPtOfReal y ↔
      ∃ k : ℤ, x = y + k := by
  constructor
  · intro h
    have hcircle : Real.fourierChar x = Real.fourierChar y := by
      apply Circle.ext
      change ((ClosedUnitDisc.bdyPtOfReal x : ClosedUnitDisc) : ℂ) =
        ((ClosedUnitDisc.bdyPtOfReal y : ClosedUnitDisc) : ℂ)
      exact congrArg (fun z : ClosedUnitDisc ↦ (z : ℂ)) h
    rw [Real.fourierChar_apply', Real.fourierChar_apply', Circle.exp_eq_exp] at hcircle
    obtain ⟨k, hk⟩ := hcircle
    refine ⟨k, ?_⟩
    have hpi : 2 * Real.pi ≠ 0 := by positivity
    apply (mul_left_cancel₀ hpi)
    calc
      2 * Real.pi * x = 2 * Real.pi * y + (k : ℝ) * (2 * Real.pi) := hk
      _ = 2 * Real.pi * (y + k) := by ring
  · rintro ⟨k, rfl⟩
    apply Subtype.ext
    change ((Real.fourierChar (y + (k : ℝ)) : Circle) : ℂ) =
      ((Real.fourierChar y : Circle) : ℂ)
    apply congrArg ((↑) : Circle → ℂ)
    rw [Real.fourierChar_apply', Real.fourierChar_apply']
    exact Circle.exp_eq_exp.mpr ⟨k, by ring⟩

private theorem equal_normalized_arcs
    {m a b : ℕ} (hm : 0 < m) (ha : a < m) (hb : b < m)
    (s t : unitInterval)
    (h : ClosedUnitDisc.bdyPtOfReal
          (((a : ℝ) + (s : ℝ)) / m) =
        ClosedUnitDisc.bdyPtOfReal
          (((b : ℝ) + (t : ℝ)) / m)) :
    (a = b ∧ s = t) ∨
      (a + 1 = b ∧ s = 1 ∧ t = 0) ∨
      (b + 1 = a ∧ s = 0 ∧ t = 1) ∨
      (a + 1 = m ∧ b = 0 ∧ s = 1 ∧ t = 0) ∨
      (b + 1 = m ∧ a = 0 ∧ s = 0 ∧ t = 1) := by
  obtain ⟨k, hk⟩ := (bdyPtOfReal_eq_iff _ _).mp h
  have hmR : 0 < (m : ℝ) := by exact_mod_cast hm
  have heq : (a : ℝ) + s = (b : ℝ) + t + (k : ℝ) * m := by
    field_simp at hk
    nlinarith
  have haRlt : (a : ℝ) < m := by exact_mod_cast ha
  have hbRlt : (b : ℝ) < m := by exact_mod_cast hb
  have haR : (a : ℝ) ≤ (m : ℝ) - 1 := by
    have : (a : ℝ) + 1 ≤ m := by exact_mod_cast (Nat.add_one_le_iff.mpr ha)
    linarith
  have hbR : (b : ℝ) ≤ (m : ℝ) - 1 := by
    have : (b : ℝ) + 1 ≤ m := by exact_mod_cast (Nat.add_one_le_iff.mpr hb)
    linarith
  have hkLower : (-1 : ℝ) ≤ (k : ℝ) := by
    nlinarith [s.property.1, s.property.2, t.property.1, t.property.2]
  have hkUpper : (k : ℝ) ≤ 1 := by
    nlinarith [s.property.1, s.property.2, t.property.1, t.property.2]
  have hkLowerZ : (-1 : ℤ) ≤ k := by exact_mod_cast hkLower
  have hkUpperZ : k ≤ (1 : ℤ) := by exact_mod_cast hkUpper
  have hkCases : k = -1 ∨ k = 0 ∨ k = 1 := by omega
  rcases hkCases with rfl | rfl | rfl
  · right; right; right; right
    norm_num at heq
    have ha0 : a = 0 := by
      have haR0 : (a : ℝ) = 0 := by
        nlinarith [s.property.1, s.property.2, t.property.1, t.property.2]
      exact_mod_cast haR0
    have hbLast : b + 1 = m := by
      have hbRLast : (b : ℝ) + 1 = m := by
        nlinarith [s.property.1, s.property.2, t.property.1, t.property.2]
      exact_mod_cast hbRLast
    have hs0 : s = 0 := by
      apply Subtype.ext
      simp only [Set.Icc.coe_zero]
      nlinarith [s.property.1, s.property.2, t.property.1, t.property.2]
    have ht1 : t = 1 := by
      apply Subtype.ext
      simp only [Set.Icc.coe_one]
      nlinarith [s.property.1, s.property.2, t.property.1, t.property.2]
    exact ⟨hbLast, ha0, hs0, ht1⟩
  · simp only [Int.cast_zero, zero_mul, add_zero] at heq
    have hab : a ≤ b + 1 := by
      exact_mod_cast (show (a : ℝ) ≤ b + 1 by
        nlinarith [s.property.1, s.property.2, t.property.1, t.property.2])
    have hba : b ≤ a + 1 := by
      exact_mod_cast (show (b : ℝ) ≤ a + 1 by
        nlinarith [s.property.1, s.property.2, t.property.1, t.property.2])
    rcases lt_trichotomy a b with hablt | rfl | hbalt
    · right; left
      have hab1 : a + 1 = b := by omega
      have hab1R : (a : ℝ) + 1 = b := by exact_mod_cast hab1
      have hs1 : s = 1 := by
        apply Subtype.ext
        simp only [Set.Icc.coe_one]
        nlinarith [s.property.1, s.property.2, t.property.1, t.property.2]
      have ht0 : t = 0 := by
        apply Subtype.ext
        simp only [Set.Icc.coe_zero]
        nlinarith [s.property.1, s.property.2, t.property.1, t.property.2]
      exact ⟨hab1, hs1, ht0⟩
    · left
      refine ⟨rfl, ?_⟩
      apply Subtype.ext
      nlinarith
    · right; right; left
      have hba1 : b + 1 = a := by omega
      have hba1R : (b : ℝ) + 1 = a := by exact_mod_cast hba1
      have hs0 : s = 0 := by
        apply Subtype.ext
        simp only [Set.Icc.coe_zero]
        nlinarith [s.property.1, s.property.2, t.property.1, t.property.2]
      have ht1 : t = 1 := by
        apply Subtype.ext
        simp only [Set.Icc.coe_one]
        nlinarith [s.property.1, s.property.2, t.property.1, t.property.2]
      exact ⟨hba1, hs0, ht1⟩
  · right; right; right; left
    norm_num at heq
    have habove : (a : ℝ) + s ≤ m := by
      linarith [haR, s.property.2]
    have hbelow : 0 ≤ (b : ℝ) + t := by
      exact add_nonneg (Nat.cast_nonneg b) t.property.1
    have hbsum : (b : ℝ) + t = 0 := by
      linarith [heq, habove, hbelow]
    have hasum : (a : ℝ) + s = m := by
      linarith [heq, hbsum]
    have hb0 : b = 0 := by
      have hbR0 : (b : ℝ) = 0 := by
        have hbnonneg : (0 : ℝ) ≤ b := by positivity
        linarith [hbsum, t.property.1, hbnonneg]
      exact_mod_cast hbR0
    have haLast : a + 1 = m := by
      have haRLast : (a : ℝ) + 1 = m := by
        linarith [hasum, haR, s.property.2]
      exact_mod_cast haRLast
    have hs1 : s = 1 := by
      apply Subtype.ext
      simp only [Set.Icc.coe_one]
      linarith [hasum, haR, s.property.2]
    have ht0 : t = 0 := by
      apply Subtype.ext
      simp only [Set.Icc.coe_zero]
      have hbnonneg : (0 : ℝ) ≤ b := by positivity
      exact le_antisymm (by linarith [hbsum, hbnonneg]) t.property.1
    exact ⟨haLast, hb0, hs1, ht0⟩

private def orientableBoundaryPrecomponent (p n : ℕ) (j : Fin n) :
    Set (orientableCellComplex p n).PolygonalPreRealization :=
  Set.range (orientableOccurrencePoint p n
    (orientableBoundaryPosition p n j 1))

private theorem orientableOccurrencePoint_boundary_eq_cases
    {p n : ℕ} (j : Fin n)
    (r : Fin (orientableBoundaryWord p n).length)
    (t u : unitInterval)
    (h : orientableOccurrencePoint p n
        (orientableBoundaryPosition p n j 1) t =
      orientableOccurrencePoint p n r u) :
    (r = orientableBoundaryPosition p n j 1 ∧ u = t) ∨
      (r.val + 1 = (orientableBoundaryPosition p n j 1).val ∧
        t = 0 ∧ u = 1) ∨
      ((orientableBoundaryPosition p n j 1).val + 1 = r.val ∧
        t = 1 ∧ u = 0) := by
  have hcarrier := congrArg
    (oneFacePolygonalPreRealizationHomeomorph (orientableBoundaryWord p n)) h
  rw [orientableCarrier_occurrencePoint, orientableCarrier_occurrencePoint] at hcarrier
  have hlength : 0 < (orientableBoundaryWord p n).length := by
    rw [orientableBoundaryWord_length]
    have := j.isLt
    omega
  rcases equal_normalized_arcs hlength
      (orientableBoundaryPosition p n j 1).isLt r.isLt t u hcarrier with
    ⟨hir, htu⟩ | ⟨hnext, ht1, hu0⟩ | ⟨hprev, ht0, hu1⟩ |
      ⟨hwrap, hr0, _ht1, _hu0⟩ | ⟨_rwrap, hi0, _ht0, _hu1⟩
  · left
    exact ⟨Fin.ext hir.symm, htu.symm⟩
  · right; right
    exact ⟨hnext, ht1, hu0⟩
  · right; left
    exact ⟨hprev, ht0, hu1⟩
  · have hwrap' :
        4 * p + j.val * 3 + 1 + 1 = 4 * p + 3 * n := by
      simpa only [orientableBoundaryPosition_val,
        orientableBoundaryWord_length] using hwrap
    omega
  · simp only [orientableBoundaryPosition_val] at hi0
    omega

private theorem orientableBoundaryInterior_ne_occurrencePoint
    {p n : ℕ} (j : Fin n) (t : unitInterval)
    (ht0 : t ≠ 0) (ht1 : t ≠ 1)
    (r : Fin (orientableBoundaryWord p n).length) (u : unitInterval)
    (hr : r ≠ orientableBoundaryPosition p n j 1) :
    orientableOccurrencePoint p n
        (orientableBoundaryPosition p n j 1) t ≠
      orientableOccurrencePoint p n r u := by
  intro h
  rcases orientableOccurrencePoint_boundary_eq_cases j r t u h with
    ⟨hr', _hu⟩ | ⟨_hprev, ht0', _hu1⟩ | ⟨_hnext, ht1', _hu0⟩
  · exact hr hr'
  · exact ht0 ht0'
  · exact ht1 ht1'

private theorem orientableBoundaryOccurrencePoint_injective
    {p n : ℕ} (j : Fin n) (t u : unitInterval)
    (h : orientableOccurrencePoint p n
          (orientableBoundaryPosition p n j 1) t =
        orientableOccurrencePoint p n
          (orientableBoundaryPosition p n j 1) u) :
    t = u := by
  rcases orientableOccurrencePoint_boundary_eq_cases j
      (orientableBoundaryPosition p n j 1) t u h with
    ⟨_hr, hut⟩ | ⟨hprev, _ht0, _hu1⟩ | ⟨hnext, _ht1, _hu0⟩
  · exact hut.symm
  · omega
  · omega

private theorem orientableOccurrencePoint_eq_of_sum_eq
    {p n : ℕ} (i r : Fin (orientableBoundaryWord p n).length)
    (t u : unitInterval)
    (h : (i.val : ℝ) + t = (r.val : ℝ) + u) :
    orientableOccurrencePoint p n i t = orientableOccurrencePoint p n r u := by
  apply (oneFacePolygonalPreRealizationHomeomorph
    (orientableBoundaryWord p n)).injective
  rw [orientableCarrier_occurrencePoint, orientableCarrier_occurrencePoint]
  exact congrArg ClosedUnitDisc.bdyPtOfReal (congrArg (fun x : ℝ ↦
    x / (orientableBoundaryWord p n).length) h)

private theorem orientableOccurrencePoint_mem_boundaryPrecomponent_iff
    {p n : ℕ} (j : Fin n)
    (r : Fin (orientableBoundaryWord p n).length) (u : unitInterval) :
    orientableOccurrencePoint p n r u ∈
        orientableBoundaryPrecomponent p n j ↔
      r = orientableBoundaryPosition p n j 1 ∨
        (r.val + 1 = (orientableBoundaryPosition p n j 1).val ∧ u = 1) ∨
        ((orientableBoundaryPosition p n j 1).val + 1 = r.val ∧ u = 0) := by
  constructor
  · rintro ⟨t, ht⟩
    rcases orientableOccurrencePoint_boundary_eq_cases j r t u ht with
      ⟨hr, _hu⟩ | ⟨hprev, _ht0, hu1⟩ | ⟨hnext, _ht1, hu0⟩
    · exact Or.inl hr
    · exact Or.inr (Or.inl ⟨hprev, hu1⟩)
    · exact Or.inr (Or.inr ⟨hnext, hu0⟩)
  · intro h
    rcases h with rfl | ⟨hprev, rfl⟩ | ⟨hnext, rfl⟩
    · exact ⟨u, rfl⟩
    · refine ⟨0, ?_⟩
      apply orientableOccurrencePoint_eq_of_sum_eq
      norm_num
      have hnat : 4 * p + j.val * 3 = r.val := by
        simp only [orientableBoundaryPosition_val] at hprev
        omega
      exact_mod_cast hnat
    · refine ⟨1, ?_⟩
      apply orientableOccurrencePoint_eq_of_sum_eq
      norm_num
      have hnat : 4 * p + j.val * 3 + 2 = r.val := by
        simpa only [orientableBoundaryPosition_val] using hnext
      exact_mod_cast hnat

private theorem orientableBoundary_c_pos_mem_iff
    {p n : ℕ} (j k : Fin n) (u : unitInterval) :
    orientableOccurrencePoint p n
        (orientableBoundaryPosition p n k 0) u ∈
        orientableBoundaryPrecomponent p n j ↔
      k = j ∧ u = 1 := by
  rw [orientableOccurrencePoint_mem_boundaryPrecomponent_iff]
  simp only [orientableBoundaryPosition_val]
  constructor
  · intro h
    rcases h with h | ⟨h, hu⟩ | ⟨h, _hu⟩
    · have := congrArg Fin.val h
      simp only [orientableBoundaryPosition_val] at this
      omega
    · refine ⟨Fin.ext ?_, hu⟩
      omega
    · omega
  · rintro ⟨rfl, rfl⟩
    exact Or.inr (Or.inl ⟨by omega, rfl⟩)

private theorem orientableBoundary_c_neg_symm_mem_iff
    {p n : ℕ} (j k : Fin n) (u : unitInterval) :
    orientableOccurrencePoint p n
        (orientableBoundaryPosition p n k 2) (unitInterval.symm u) ∈
        orientableBoundaryPrecomponent p n j ↔
      k = j ∧ u = 1 := by
  rw [orientableOccurrencePoint_mem_boundaryPrecomponent_iff]
  simp only [orientableBoundaryPosition_val]
  constructor
  · intro h
    rcases h with h | ⟨h, _hu⟩ | ⟨h, hu⟩
    · have := congrArg Fin.val h
      simp only [orientableBoundaryPosition_val] at this
      omega
    · omega
    · refine ⟨Fin.ext ?_, ?_⟩
      · omega
      · apply (unitInterval.symmHomeomorph.injective)
        simpa using hu
  · rintro ⟨rfl, rfl⟩
    exact Or.inr (Or.inr ⟨by omega, by simp⟩)

private theorem orientableBoundary_c_neg_mem_iff
    {p n : ℕ} (j k : Fin n) (u : unitInterval) :
    orientableOccurrencePoint p n
        (orientableBoundaryPosition p n k 2) u ∈
        orientableBoundaryPrecomponent p n j ↔
      k = j ∧ u = 0 := by
  rw [orientableOccurrencePoint_mem_boundaryPrecomponent_iff]
  simp only [orientableBoundaryPosition_val]
  constructor
  · intro h
    rcases h with h | ⟨h, _hu⟩ | ⟨h, hu⟩
    · have := congrArg Fin.val h
      simp only [orientableBoundaryPosition_val] at this
      omega
    · omega
    · exact ⟨Fin.ext (by omega), hu⟩
  · rintro ⟨rfl, rfl⟩
    exact Or.inr (Or.inr ⟨by omega, rfl⟩)

private theorem orientableBoundary_c_pos_symm_mem_iff
    {p n : ℕ} (j k : Fin n) (u : unitInterval) :
    orientableOccurrencePoint p n
        (orientableBoundaryPosition p n k 0) (unitInterval.symm u) ∈
        orientableBoundaryPrecomponent p n j ↔
      k = j ∧ u = 0 := by
  rw [orientableOccurrencePoint_mem_boundaryPrecomponent_iff]
  simp only [orientableBoundaryPosition_val]
  constructor
  · intro h
    rcases h with h | ⟨h, hu⟩ | ⟨h, _hu⟩
    · have := congrArg Fin.val h
      simp only [orientableBoundaryPosition_val] at this
      omega
    · refine ⟨Fin.ext (by omega), ?_⟩
      apply unitInterval.symmHomeomorph.injective
      simpa using hu
    · omega
  · rintro ⟨rfl, rfl⟩
    exact Or.inr (Or.inl ⟨by omega, by simp⟩)

private theorem orientableHandleOccurrence_not_mem
    {p n : ℕ} (j : Fin n) (i : Fin p) (k : Fin 4) (u : unitInterval) :
    orientableOccurrencePoint p n (orientableHandlePosition p n i k) u ∉
      orientableBoundaryPrecomponent p n j := by
  rw [orientableOccurrencePoint_mem_boundaryPrecomponent_iff]
  simp only [orientableHandlePosition_val, orientableBoundaryPosition_val]
  intro h
  rcases h with h | ⟨h, _hu⟩ | ⟨h, _hu⟩
  · have := congrArg Fin.val h
    simp only [orientableHandlePosition_val,
      orientableBoundaryPosition_val] at this
    omega
  · omega
  · omega

private theorem orientableGenerator_preserves_boundaryPrecomponent
    {p n : ℕ} (hvalid : 1 ≤ p ∨ 1 ≤ n) (j : Fin n)
    {x y : (orientableCellComplex p n).PolygonalPreRealization}
    (hxy : PolygonGluing.Generator
      ((orientableCellComplex p n).polygonalIdentifications
        (orientableCellComplex_occurrencePairingValid hvalid)) x y) :
    x ∈ orientableBoundaryPrecomponent p n j ↔
      y ∈ orientableBoundaryPrecomponent p n j := by
  cases hxy with
  | glue identification hidentification u =>
      rw [mem_orientable_polygonalIdentifications_iff hvalid] at hidentification
      rcases hidentification with
        ⟨i, rfl | rfl⟩ | ⟨i, rfl | rfl⟩ | ⟨k, rfl | rfl⟩
      · change orientableOccurrencePoint p n
            (orientableHandlePosition p n i 0) u ∈ _ ↔
          orientableOccurrencePoint p n
            (orientableHandlePosition p n i 2) (unitInterval.symm u) ∈ _
        simp only [orientableHandleOccurrence_not_mem]
      · change orientableOccurrencePoint p n
            (orientableHandlePosition p n i 2) u ∈ _ ↔
          orientableOccurrencePoint p n
            (orientableHandlePosition p n i 0) (unitInterval.symm u) ∈ _
        simp only [orientableHandleOccurrence_not_mem]
      · change orientableOccurrencePoint p n
            (orientableHandlePosition p n i 1) u ∈ _ ↔
          orientableOccurrencePoint p n
            (orientableHandlePosition p n i 3) (unitInterval.symm u) ∈ _
        simp only [orientableHandleOccurrence_not_mem]
      · change orientableOccurrencePoint p n
            (orientableHandlePosition p n i 3) u ∈ _ ↔
          orientableOccurrencePoint p n
            (orientableHandlePosition p n i 1) (unitInterval.symm u) ∈ _
        simp only [orientableHandleOccurrence_not_mem]
      · change orientableOccurrencePoint p n
            (orientableBoundaryPosition p n k 0) u ∈ _ ↔
          orientableOccurrencePoint p n
            (orientableBoundaryPosition p n k 2) (unitInterval.symm u) ∈ _
        rw [orientableBoundary_c_pos_mem_iff,
          orientableBoundary_c_neg_symm_mem_iff]
      · change orientableOccurrencePoint p n
            (orientableBoundaryPosition p n k 2) u ∈ _ ↔
          orientableOccurrencePoint p n
            (orientableBoundaryPosition p n k 0) (unitInterval.symm u) ∈ _
        rw [orientableBoundary_c_neg_mem_iff,
          orientableBoundary_c_pos_symm_mem_iff]

private theorem orientableGenerator_avoids_boundaryInterior
    {p n : ℕ} (hvalid : 1 ≤ p ∨ 1 ≤ n) (j : Fin n)
    (t : unitInterval) (ht0 : t ≠ 0) (ht1 : t ≠ 1)
    {x y : (orientableCellComplex p n).PolygonalPreRealization}
    (hxy : PolygonGluing.Generator
      ((orientableCellComplex p n).polygonalIdentifications
        (orientableCellComplex_occurrencePairingValid hvalid)) x y)
    (hpoint : x = orientableOccurrencePoint p n
          (orientableBoundaryPosition p n j 1) t ∨
        y = orientableOccurrencePoint p n
          (orientableBoundaryPosition p n j 1) t) :
    False := by
  cases hxy with
  | glue identification hidentification u =>
      rw [mem_orientable_polygonalIdentifications_iff hvalid] at hidentification
      rcases hidentification with
        ⟨i, rfl | rfl⟩ | ⟨i, rfl | rfl⟩ | ⟨k, rfl | rfl⟩
      · change
          orientableOccurrencePoint p n
                (orientableHandlePosition p n i 0) u =
              orientableOccurrencePoint p n
                (orientableBoundaryPosition p n j 1) t ∨
            orientableOccurrencePoint p n
                (orientableHandlePosition p n i 2)
                  (unitInterval.symm u) =
              orientableOccurrencePoint p n
                (orientableBoundaryPosition p n j 1) t at hpoint
        rcases hpoint with hx | hy
        · exact (orientableBoundaryInterior_ne_occurrencePoint j t ht0 ht1
            (orientableHandlePosition p n i 0) u (by
              intro h
              have := congrArg Fin.val h
              simp only [orientableHandlePosition_val,
                orientableBoundaryPosition_val] at this
              omega)) hx.symm
        · exact (orientableBoundaryInterior_ne_occurrencePoint j t ht0 ht1
            (orientableHandlePosition p n i 2) (unitInterval.symm u) (by
              intro h
              have := congrArg Fin.val h
              simp only [orientableHandlePosition_val,
                orientableBoundaryPosition_val] at this
              omega)) hy.symm
      · change
          orientableOccurrencePoint p n
                (orientableHandlePosition p n i 2) u =
              orientableOccurrencePoint p n
                (orientableBoundaryPosition p n j 1) t ∨
            orientableOccurrencePoint p n
                (orientableHandlePosition p n i 0)
                  (unitInterval.symm u) =
              orientableOccurrencePoint p n
                (orientableBoundaryPosition p n j 1) t at hpoint
        rcases hpoint with hx | hy
        · exact (orientableBoundaryInterior_ne_occurrencePoint j t ht0 ht1
            (orientableHandlePosition p n i 2) u (by
              intro h
              have := congrArg Fin.val h
              simp only [orientableHandlePosition_val,
                orientableBoundaryPosition_val] at this
              omega)) hx.symm
        · exact (orientableBoundaryInterior_ne_occurrencePoint j t ht0 ht1
            (orientableHandlePosition p n i 0) (unitInterval.symm u) (by
              intro h
              have := congrArg Fin.val h
              simp only [orientableHandlePosition_val,
                orientableBoundaryPosition_val] at this
              omega)) hy.symm
      · change
          orientableOccurrencePoint p n
                (orientableHandlePosition p n i 1) u =
              orientableOccurrencePoint p n
                (orientableBoundaryPosition p n j 1) t ∨
            orientableOccurrencePoint p n
                (orientableHandlePosition p n i 3)
                  (unitInterval.symm u) =
              orientableOccurrencePoint p n
                (orientableBoundaryPosition p n j 1) t at hpoint
        rcases hpoint with hx | hy
        · exact (orientableBoundaryInterior_ne_occurrencePoint j t ht0 ht1
            (orientableHandlePosition p n i 1) u (by
              intro h
              have := congrArg Fin.val h
              simp only [orientableHandlePosition_val,
                orientableBoundaryPosition_val] at this
              omega)) hx.symm
        · exact (orientableBoundaryInterior_ne_occurrencePoint j t ht0 ht1
            (orientableHandlePosition p n i 3) (unitInterval.symm u) (by
              intro h
              have := congrArg Fin.val h
              simp only [orientableHandlePosition_val,
                orientableBoundaryPosition_val] at this
              omega)) hy.symm
      · change
          orientableOccurrencePoint p n
                (orientableHandlePosition p n i 3) u =
              orientableOccurrencePoint p n
                (orientableBoundaryPosition p n j 1) t ∨
            orientableOccurrencePoint p n
                (orientableHandlePosition p n i 1)
                  (unitInterval.symm u) =
              orientableOccurrencePoint p n
                (orientableBoundaryPosition p n j 1) t at hpoint
        rcases hpoint with hx | hy
        · exact (orientableBoundaryInterior_ne_occurrencePoint j t ht0 ht1
            (orientableHandlePosition p n i 3) u (by
              intro h
              have := congrArg Fin.val h
              simp only [orientableHandlePosition_val,
                orientableBoundaryPosition_val] at this
              omega)) hx.symm
        · exact (orientableBoundaryInterior_ne_occurrencePoint j t ht0 ht1
            (orientableHandlePosition p n i 1) (unitInterval.symm u) (by
              intro h
              have := congrArg Fin.val h
              simp only [orientableHandlePosition_val,
                orientableBoundaryPosition_val] at this
              omega)) hy.symm
      · change
          orientableOccurrencePoint p n
                (orientableBoundaryPosition p n k 0) u =
              orientableOccurrencePoint p n
                (orientableBoundaryPosition p n j 1) t ∨
            orientableOccurrencePoint p n
                (orientableBoundaryPosition p n k 2)
                  (unitInterval.symm u) =
              orientableOccurrencePoint p n
                (orientableBoundaryPosition p n j 1) t at hpoint
        rcases hpoint with hx | hy
        · exact (orientableBoundaryInterior_ne_occurrencePoint j t ht0 ht1
            (orientableBoundaryPosition p n k 0) u (by
              intro h
              have := congrArg Fin.val h
              simp only [orientableBoundaryPosition_val] at this
              omega)) hx.symm
        · exact (orientableBoundaryInterior_ne_occurrencePoint j t ht0 ht1
            (orientableBoundaryPosition p n k 2) (unitInterval.symm u) (by
              intro h
              have := congrArg Fin.val h
              simp only [orientableBoundaryPosition_val] at this
              omega)) hy.symm
      · change
          orientableOccurrencePoint p n
                (orientableBoundaryPosition p n k 2) u =
              orientableOccurrencePoint p n
                (orientableBoundaryPosition p n j 1) t ∨
            orientableOccurrencePoint p n
                (orientableBoundaryPosition p n k 0)
                  (unitInterval.symm u) =
              orientableOccurrencePoint p n
                (orientableBoundaryPosition p n j 1) t at hpoint
        rcases hpoint with hx | hy
        · exact (orientableBoundaryInterior_ne_occurrencePoint j t ht0 ht1
            (orientableBoundaryPosition p n k 2) u (by
              intro h
              have := congrArg Fin.val h
              simp only [orientableBoundaryPosition_val] at this
              omega)) hx.symm
        · exact (orientableBoundaryInterior_ne_occurrencePoint j t ht0 ht1
            (orientableBoundaryPosition p n k 0) (unitInterval.symm u) (by
              intro h
              have := congrArg Fin.val h
              simp only [orientableBoundaryPosition_val] at this
              omega)) hy.symm

private theorem orientableEqvGen_preserves_boundaryInterior
    {p n : ℕ} (hvalid : 1 ≤ p ∨ 1 ≤ n) (j : Fin n)
    (t : unitInterval) (ht0 : t ≠ 0) (ht1 : t ≠ 1)
    {x y : (orientableCellComplex p n).PolygonalPreRealization}
    (hxy : Relation.EqvGen
      (PolygonGluing.Generator
        ((orientableCellComplex p n).polygonalIdentifications
          (orientableCellComplex_occurrencePairingValid hvalid))) x y) :
    (x = orientableOccurrencePoint p n
          (orientableBoundaryPosition p n j 1) t) ↔
      (y = orientableOccurrencePoint p n
          (orientableBoundaryPosition p n j 1) t) := by
  induction hxy with
  | rel x y h =>
      constructor <;> intro hpoint
      · exact (orientableGenerator_avoids_boundaryInterior
          hvalid j t ht0 ht1 h (Or.inl hpoint)).elim
      · exact (orientableGenerator_avoids_boundaryInterior
          hvalid j t ht0 ht1 h (Or.inr hpoint)).elim
  | refl => exact Iff.rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

private theorem orientableEqvGen_preserves_boundaryPrecomponent
    {p n : ℕ} (hvalid : 1 ≤ p ∨ 1 ≤ n) (j : Fin n)
    {x y : (orientableCellComplex p n).PolygonalPreRealization}
    (hxy : Relation.EqvGen
      (PolygonGluing.Generator
        ((orientableCellComplex p n).polygonalIdentifications
          (orientableCellComplex_occurrencePairingValid hvalid))) x y) :
    x ∈ orientableBoundaryPrecomponent p n j ↔
      y ∈ orientableBoundaryPrecomponent p n j := by
  induction hxy with
  | rel _ _ h =>
      exact orientableGenerator_preserves_boundaryPrecomponent hvalid j h
  | refl => exact Iff.rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

private theorem orientableBoundary_h_mem_iff
    {p n : ℕ} (j k : Fin n) (u : unitInterval) :
    orientableOccurrencePoint p n
        (orientableBoundaryPosition p n k 1) u ∈
        orientableBoundaryPrecomponent p n j ↔
      k = j := by
  rw [orientableOccurrencePoint_mem_boundaryPrecomponent_iff]
  simp only [orientableBoundaryPosition_val]
  constructor
  · intro h
    rcases h with h | ⟨h, _hu⟩ | ⟨h, _hu⟩
    · apply Fin.ext
      have := congrArg Fin.val h
      simp only [orientableBoundaryPosition_val] at this
      omega
    · omega
    · omega
  · rintro rfl
    exact Or.inl rfl

private def orientableBoundaryComponent
    {p n : ℕ} (hvalid : 1 ≤ p ∨ 1 ≤ n) (j : Fin n) :
    Set ((orientableCellComplex p n).PolygonalRealization
      (orientableCellComplex_occurrencePairingValid hvalid)) :=
  Set.range (fun t ↦
    (orientableCellComplex p n).polygonalMk
      (orientableCellComplex_occurrencePairingValid hvalid)
      (orientableOccurrencePoint p n
        (orientableBoundaryPosition p n j 1) t))

private theorem orientableBoundaryComponent_pairwise_disjoint
    {p n : ℕ} (hvalid : 1 ≤ p ∨ 1 ≤ n)
    {j k : Fin n} (hjk : j ≠ k) :
    Disjoint (orientableBoundaryComponent hvalid j)
      (orientableBoundaryComponent hvalid k) := by
  rw [Set.disjoint_left]
  intro q hqj hqk
  rcases hqj with ⟨t, rfl⟩
  rcases hqk with ⟨u, hu⟩
  have heqv := Quotient.exact hu.symm
  have hpreserve :=
    (orientableEqvGen_preserves_boundaryPrecomponent hvalid j heqv).mp
      (show orientableOccurrencePoint p n
          (orientableBoundaryPosition p n j 1) t ∈
          orientableBoundaryPrecomponent p n j from ⟨t, rfl⟩)
  rw [orientableBoundary_h_mem_iff] at hpreserve
  exact hjk hpreserve.symm

private theorem continuous_orientableOccurrencePoint
    (p n : ℕ) (i : Fin (orientableBoundaryWord p n).length) :
    Continuous (orientableOccurrencePoint p n i) := by
  let e := oneFacePolygonalPreRealizationHomeomorph
    (orientableBoundaryWord p n)
  have hcarrier : Continuous (fun t : unitInterval ↦
      ClosedUnitDisc.bdyPtOfReal
        (((i.val : ℝ) + (t : ℝ)) /
          (orientableBoundaryWord p n).length)) := by
    apply Continuous.subtype_mk
    fun_prop
  have heq : orientableOccurrencePoint p n i = fun t : unitInterval ↦
      e.symm (ClosedUnitDisc.bdyPtOfReal
        (((i.val : ℝ) + (t : ℝ)) /
          (orientableBoundaryWord p n).length)) := by
    funext t
    apply e.injective
    rw [Homeomorph.apply_symm_apply]
    exact orientableCarrier_occurrencePoint p n i t
  rw [heq]
  exact e.symm.continuous.comp hcarrier

private theorem isCompact_orientableBoundaryComponent
    {p n : ℕ} (hvalid : 1 ≤ p ∨ 1 ≤ n) (j : Fin n) :
    IsCompact (orientableBoundaryComponent hvalid j) := by
  apply isCompact_range
  exact ((orientableCellComplex p n).continuous_polygonalMk _).comp
    (continuous_orientableOccurrencePoint p n _)

private def orientableBoundaryComponentsLocus
    {p n : ℕ} (hvalid : 1 ≤ p ∨ 1 ≤ n) :
    Set ((orientableCellComplex p n).PolygonalRealization
      (orientableCellComplex_occurrencePairingValid hvalid)) :=
  ⋃ j : Fin n, orientableBoundaryComponent hvalid j

private theorem isCompact_orientableBoundaryComponentsLocus
    {p n : ℕ} (hvalid : 1 ≤ p ∨ 1 ≤ n) :
    IsCompact (orientableBoundaryComponentsLocus hvalid) := by
  apply isCompact_iUnion
  exact isCompact_orientableBoundaryComponent hvalid

private theorem orientableBoundaryComponents_eq_one_of_isConnected
    {p n : ℕ} (hvalid : 1 ≤ p ∨ 1 ≤ n)
    [T2Space ((orientableCellComplex p n).PolygonalRealization
      (orientableCellComplex_occurrencePairingValid hvalid))]
    (hconnected : IsConnected
      (orientableBoundaryComponentsLocus hvalid)) :
    n = 1 := by
  have hnpos : 0 < n := by
    rcases hconnected.nonempty with ⟨q, hq⟩
    rcases Set.mem_iUnion.mp hq with ⟨j, _hj⟩
    exact Nat.pos_of_ne_zero (by
      intro hn
      subst n
      exact Fin.elim0 j)
  by_contra hnOne
  have hnTwo : 2 ≤ n := by omega
  let j₀ : Fin n := ⟨0, hnpos⟩
  let j₁ : Fin n := ⟨1, hnTwo⟩
  let A := orientableBoundaryComponent hvalid j₀
  let B := ⋃ k : {k : Fin n // k ≠ j₀},
    orientableBoundaryComponent hvalid k.1
  have hAclosed : IsClosed A :=
    (isCompact_orientableBoundaryComponent hvalid j₀).isClosed
  have hBcompact : IsCompact B := by
    apply isCompact_iUnion
    intro k
    exact isCompact_orientableBoundaryComponent hvalid k.1
  have hBclosed : IsClosed B := hBcompact.isClosed
  have hcover : orientableBoundaryComponentsLocus hvalid ⊆ A ∪ B := by
    intro q hq
    rcases Set.mem_iUnion.mp hq with ⟨k, hk⟩
    by_cases hkj₀ : k = j₀
    · left
      simpa only [A, hkj₀] using hk
    · right
      exact Set.mem_iUnion.mpr ⟨⟨k, hkj₀⟩, hk⟩
  have hAmeet :
      (orientableBoundaryComponentsLocus hvalid ∩ A).Nonempty := by
    let q := (orientableCellComplex p n).polygonalMk
      (orientableCellComplex_occurrencePairingValid hvalid)
      (orientableOccurrencePoint p n
        (orientableBoundaryPosition p n j₀ 1) 0)
    have hqA : q ∈ A := ⟨0, rfl⟩
    refine ⟨q, ?_, hqA⟩
    exact Set.mem_iUnion.mpr ⟨j₀, hqA⟩
  have hj₁j₀ : j₁ ≠ j₀ := by
    intro h
    have := congrArg Fin.val h
    simp only [j₀, j₁] at this
    omega
  have hBmeet :
      (orientableBoundaryComponentsLocus hvalid ∩ B).Nonempty := by
    let q := (orientableCellComplex p n).polygonalMk
      (orientableCellComplex_occurrencePairingValid hvalid)
      (orientableOccurrencePoint p n
        (orientableBoundaryPosition p n j₁ 1) 0)
    have hqj₁ : q ∈ orientableBoundaryComponent hvalid j₁ := ⟨0, rfl⟩
    refine ⟨q, Set.mem_iUnion.mpr ⟨j₁, hqj₁⟩, ?_⟩
    exact Set.mem_iUnion.mpr ⟨⟨j₁, hj₁j₀⟩, hqj₁⟩
  have hABdisjoint : Disjoint A B := by
    rw [Set.disjoint_left]
    intro q hqA hqB
    rcases Set.mem_iUnion.mp hqB with ⟨k, hqk⟩
    exact Set.disjoint_left.mp
      (orientableBoundaryComponent_pairwise_disjoint hvalid
        (j := j₀) (k := k.1) (Ne.symm k.property))
      hqA hqk
  obtain ⟨q, _hqL, hqA, hqB⟩ :=
    (isPreconnected_closed_iff.mp hconnected.isPreconnected)
      A B hAclosed hBclosed hcover hAmeet hBmeet
  exact Set.disjoint_left.mp hABdisjoint hqA hqB

/-! Nonorientable normal forms. -/

private def nonOrientableBoundaryPrecomponent (p n : ℕ) (j : Fin n) :
    Set (nonOrientableCellComplex p n).PolygonalPreRealization :=
  Set.range (nonOrientableOccurrencePoint p n
    (nonOrientableBoundaryPosition p n j 1))

private theorem nonOrientableOccurrencePoint_boundary_eq_cases
    {p n : ℕ} (j : Fin n)
    (r : Fin (nonOrientableBoundaryWord p n).length)
    (t u : unitInterval)
    (h : nonOrientableOccurrencePoint p n
        (nonOrientableBoundaryPosition p n j 1) t =
      nonOrientableOccurrencePoint p n r u) :
    (r = nonOrientableBoundaryPosition p n j 1 ∧ u = t) ∨
      (r.val + 1 = (nonOrientableBoundaryPosition p n j 1).val ∧
        t = 0 ∧ u = 1) ∨
      ((nonOrientableBoundaryPosition p n j 1).val + 1 = r.val ∧
        t = 1 ∧ u = 0) := by
  have hcarrier := congrArg
    (oneFacePolygonalPreRealizationHomeomorph
      (nonOrientableBoundaryWord p n)) h
  rw [nonOrientableCarrier_occurrencePoint,
    nonOrientableCarrier_occurrencePoint] at hcarrier
  have hlength : 0 < (nonOrientableBoundaryWord p n).length := by
    rw [nonOrientableBoundaryWord_length]
    have := j.isLt
    omega
  rcases equal_normalized_arcs hlength
      (nonOrientableBoundaryPosition p n j 1).isLt r.isLt t u hcarrier with
    ⟨hir, htu⟩ | ⟨hnext, ht1, hu0⟩ | ⟨hprev, ht0, hu1⟩ |
      ⟨hwrap, hr0, _ht1, _hu0⟩ | ⟨_rwrap, hi0, _ht0, _hu1⟩
  · left
    exact ⟨Fin.ext hir.symm, htu.symm⟩
  · right; right
    exact ⟨hnext, ht1, hu0⟩
  · right; left
    exact ⟨hprev, ht0, hu1⟩
  · have hwrap' :
        2 * p + j.val * 3 + 1 + 1 = 2 * p + 3 * n := by
      simpa only [nonOrientableBoundaryPosition_val,
        nonOrientableBoundaryWord_length] using hwrap
    omega
  · simp only [nonOrientableBoundaryPosition_val] at hi0
    omega

private theorem nonOrientableBoundaryInterior_ne_occurrencePoint
    {p n : ℕ} (j : Fin n) (t : unitInterval)
    (ht0 : t ≠ 0) (ht1 : t ≠ 1)
    (r : Fin (nonOrientableBoundaryWord p n).length) (u : unitInterval)
    (hr : r ≠ nonOrientableBoundaryPosition p n j 1) :
    nonOrientableOccurrencePoint p n
        (nonOrientableBoundaryPosition p n j 1) t ≠
      nonOrientableOccurrencePoint p n r u := by
  intro h
  rcases nonOrientableOccurrencePoint_boundary_eq_cases j r t u h with
    ⟨hr', _hu⟩ | ⟨_hprev, ht0', _hu1⟩ | ⟨_hnext, ht1', _hu0⟩
  · exact hr hr'
  · exact ht0 ht0'
  · exact ht1 ht1'

private theorem nonOrientableBoundaryOccurrencePoint_injective
    {p n : ℕ} (j : Fin n) (t u : unitInterval)
    (h : nonOrientableOccurrencePoint p n
          (nonOrientableBoundaryPosition p n j 1) t =
        nonOrientableOccurrencePoint p n
          (nonOrientableBoundaryPosition p n j 1) u) :
    t = u := by
  rcases nonOrientableOccurrencePoint_boundary_eq_cases j
      (nonOrientableBoundaryPosition p n j 1) t u h with
    ⟨_hr, hut⟩ | ⟨hprev, _ht0, _hu1⟩ | ⟨hnext, _ht1, _hu0⟩
  · exact hut.symm
  · omega
  · omega

private theorem nonOrientableOccurrencePoint_eq_of_sum_eq
    {p n : ℕ} (i r : Fin (nonOrientableBoundaryWord p n).length)
    (t u : unitInterval)
    (h : (i.val : ℝ) + t = (r.val : ℝ) + u) :
    nonOrientableOccurrencePoint p n i t =
      nonOrientableOccurrencePoint p n r u := by
  apply (oneFacePolygonalPreRealizationHomeomorph
    (nonOrientableBoundaryWord p n)).injective
  rw [nonOrientableCarrier_occurrencePoint,
    nonOrientableCarrier_occurrencePoint]
  exact congrArg ClosedUnitDisc.bdyPtOfReal (congrArg (fun x : ℝ ↦
    x / (nonOrientableBoundaryWord p n).length) h)

private theorem nonOrientableOccurrencePoint_mem_boundaryPrecomponent_iff
    {p n : ℕ} (j : Fin n)
    (r : Fin (nonOrientableBoundaryWord p n).length) (u : unitInterval) :
    nonOrientableOccurrencePoint p n r u ∈
        nonOrientableBoundaryPrecomponent p n j ↔
      r = nonOrientableBoundaryPosition p n j 1 ∨
        (r.val + 1 = (nonOrientableBoundaryPosition p n j 1).val ∧ u = 1) ∨
        ((nonOrientableBoundaryPosition p n j 1).val + 1 = r.val ∧ u = 0) := by
  constructor
  · rintro ⟨t, ht⟩
    rcases nonOrientableOccurrencePoint_boundary_eq_cases j r t u ht with
      ⟨hr, _hu⟩ | ⟨hprev, _ht0, hu1⟩ | ⟨hnext, _ht1, hu0⟩
    · exact Or.inl hr
    · exact Or.inr (Or.inl ⟨hprev, hu1⟩)
    · exact Or.inr (Or.inr ⟨hnext, hu0⟩)
  · intro h
    rcases h with rfl | ⟨hprev, rfl⟩ | ⟨hnext, rfl⟩
    · exact ⟨u, rfl⟩
    · refine ⟨0, ?_⟩
      apply nonOrientableOccurrencePoint_eq_of_sum_eq
      norm_num
      have hnat : 2 * p + j.val * 3 = r.val := by
        simp only [nonOrientableBoundaryPosition_val] at hprev
        omega
      exact_mod_cast hnat
    · refine ⟨1, ?_⟩
      apply nonOrientableOccurrencePoint_eq_of_sum_eq
      norm_num
      have hnat : 2 * p + j.val * 3 + 2 = r.val := by
        simpa only [nonOrientableBoundaryPosition_val] using hnext
      exact_mod_cast hnat

private theorem nonOrientableBoundary_c_pos_mem_iff
    {p n : ℕ} (j k : Fin n) (u : unitInterval) :
    nonOrientableOccurrencePoint p n
        (nonOrientableBoundaryPosition p n k 0) u ∈
        nonOrientableBoundaryPrecomponent p n j ↔
      k = j ∧ u = 1 := by
  rw [nonOrientableOccurrencePoint_mem_boundaryPrecomponent_iff]
  simp only [nonOrientableBoundaryPosition_val]
  constructor
  · intro h
    rcases h with h | ⟨h, hu⟩ | ⟨h, _hu⟩
    · have := congrArg Fin.val h
      simp only [nonOrientableBoundaryPosition_val] at this
      omega
    · exact ⟨Fin.ext (by omega), hu⟩
    · omega
  · rintro ⟨rfl, rfl⟩
    exact Or.inr (Or.inl ⟨by omega, rfl⟩)

private theorem nonOrientableBoundary_c_neg_symm_mem_iff
    {p n : ℕ} (j k : Fin n) (u : unitInterval) :
    nonOrientableOccurrencePoint p n
        (nonOrientableBoundaryPosition p n k 2) (unitInterval.symm u) ∈
        nonOrientableBoundaryPrecomponent p n j ↔
      k = j ∧ u = 1 := by
  rw [nonOrientableOccurrencePoint_mem_boundaryPrecomponent_iff]
  simp only [nonOrientableBoundaryPosition_val]
  constructor
  · intro h
    rcases h with h | ⟨h, _hu⟩ | ⟨h, hu⟩
    · have := congrArg Fin.val h
      simp only [nonOrientableBoundaryPosition_val] at this
      omega
    · omega
    · refine ⟨Fin.ext (by omega), ?_⟩
      apply unitInterval.symmHomeomorph.injective
      simpa using hu
  · rintro ⟨rfl, rfl⟩
    exact Or.inr (Or.inr ⟨by omega, by simp⟩)

private theorem nonOrientableBoundary_c_neg_mem_iff
    {p n : ℕ} (j k : Fin n) (u : unitInterval) :
    nonOrientableOccurrencePoint p n
        (nonOrientableBoundaryPosition p n k 2) u ∈
        nonOrientableBoundaryPrecomponent p n j ↔
      k = j ∧ u = 0 := by
  rw [nonOrientableOccurrencePoint_mem_boundaryPrecomponent_iff]
  simp only [nonOrientableBoundaryPosition_val]
  constructor
  · intro h
    rcases h with h | ⟨h, _hu⟩ | ⟨h, hu⟩
    · have := congrArg Fin.val h
      simp only [nonOrientableBoundaryPosition_val] at this
      omega
    · omega
    · exact ⟨Fin.ext (by omega), hu⟩
  · rintro ⟨rfl, rfl⟩
    exact Or.inr (Or.inr ⟨by omega, rfl⟩)

private theorem nonOrientableBoundary_c_pos_symm_mem_iff
    {p n : ℕ} (j k : Fin n) (u : unitInterval) :
    nonOrientableOccurrencePoint p n
        (nonOrientableBoundaryPosition p n k 0) (unitInterval.symm u) ∈
        nonOrientableBoundaryPrecomponent p n j ↔
      k = j ∧ u = 0 := by
  rw [nonOrientableOccurrencePoint_mem_boundaryPrecomponent_iff]
  simp only [nonOrientableBoundaryPosition_val]
  constructor
  · intro h
    rcases h with h | ⟨h, hu⟩ | ⟨h, _hu⟩
    · have := congrArg Fin.val h
      simp only [nonOrientableBoundaryPosition_val] at this
      omega
    · refine ⟨Fin.ext (by omega), ?_⟩
      apply unitInterval.symmHomeomorph.injective
      simpa using hu
    · omega
  · rintro ⟨rfl, rfl⟩
    exact Or.inr (Or.inl ⟨by omega, by simp⟩)

private theorem nonOrientableCrosscapOccurrence_not_mem
    {p n : ℕ} (j : Fin n) (i : Fin p) (k : Fin 2) (u : unitInterval) :
    nonOrientableOccurrencePoint p n
        (nonOrientableCrosscapPosition p n i k) u ∉
      nonOrientableBoundaryPrecomponent p n j := by
  rw [nonOrientableOccurrencePoint_mem_boundaryPrecomponent_iff]
  simp only [nonOrientableCrosscapPosition_val,
    nonOrientableBoundaryPosition_val]
  intro h
  rcases h with h | ⟨h, _hu⟩ | ⟨h, _hu⟩
  · have := congrArg Fin.val h
    simp only [nonOrientableCrosscapPosition_val,
      nonOrientableBoundaryPosition_val] at this
    omega
  · omega
  · omega

private theorem nonOrientableGenerator_preserves_boundaryPrecomponent
    {p n : ℕ} (hp : 1 ≤ p) (j : Fin n)
    {x y : (nonOrientableCellComplex p n).PolygonalPreRealization}
    (hxy : PolygonGluing.Generator
      ((nonOrientableCellComplex p n).polygonalIdentifications
        (nonOrientableCellComplex_occurrencePairingValid hp)) x y) :
    x ∈ nonOrientableBoundaryPrecomponent p n j ↔
      y ∈ nonOrientableBoundaryPrecomponent p n j := by
  cases hxy with
  | glue identification hidentification u =>
      rw [mem_nonOrientable_polygonalIdentifications_iff hp] at hidentification
      rcases hidentification with ⟨i, rfl | rfl⟩ | ⟨k, rfl | rfl⟩
      · change nonOrientableOccurrencePoint p n
            (nonOrientableCrosscapPosition p n i 0) u ∈ _ ↔
          nonOrientableOccurrencePoint p n
            (nonOrientableCrosscapPosition p n i 1) u ∈ _
        simp only [nonOrientableCrosscapOccurrence_not_mem]
      · change nonOrientableOccurrencePoint p n
            (nonOrientableCrosscapPosition p n i 1) u ∈ _ ↔
          nonOrientableOccurrencePoint p n
            (nonOrientableCrosscapPosition p n i 0) u ∈ _
        simp only [nonOrientableCrosscapOccurrence_not_mem]
      · change nonOrientableOccurrencePoint p n
            (nonOrientableBoundaryPosition p n k 0) u ∈ _ ↔
          nonOrientableOccurrencePoint p n
            (nonOrientableBoundaryPosition p n k 2) (unitInterval.symm u) ∈ _
        rw [nonOrientableBoundary_c_pos_mem_iff,
          nonOrientableBoundary_c_neg_symm_mem_iff]
      · change nonOrientableOccurrencePoint p n
            (nonOrientableBoundaryPosition p n k 2) u ∈ _ ↔
          nonOrientableOccurrencePoint p n
            (nonOrientableBoundaryPosition p n k 0) (unitInterval.symm u) ∈ _
        rw [nonOrientableBoundary_c_neg_mem_iff,
          nonOrientableBoundary_c_pos_symm_mem_iff]

private theorem nonOrientableGenerator_avoids_boundaryInterior
    {p n : ℕ} (hp : 1 ≤ p) (j : Fin n)
    (t : unitInterval) (ht0 : t ≠ 0) (ht1 : t ≠ 1)
    {x y : (nonOrientableCellComplex p n).PolygonalPreRealization}
    (hxy : PolygonGluing.Generator
      ((nonOrientableCellComplex p n).polygonalIdentifications
        (nonOrientableCellComplex_occurrencePairingValid hp)) x y)
    (hpoint : x = nonOrientableOccurrencePoint p n
          (nonOrientableBoundaryPosition p n j 1) t ∨
        y = nonOrientableOccurrencePoint p n
          (nonOrientableBoundaryPosition p n j 1) t) :
    False := by
  cases hxy with
  | glue identification hidentification u =>
      rw [mem_nonOrientable_polygonalIdentifications_iff hp] at hidentification
      rcases hidentification with ⟨i, rfl | rfl⟩ | ⟨k, rfl | rfl⟩
      · change
          nonOrientableOccurrencePoint p n
                (nonOrientableCrosscapPosition p n i 0) u =
              nonOrientableOccurrencePoint p n
                (nonOrientableBoundaryPosition p n j 1) t ∨
            nonOrientableOccurrencePoint p n
                (nonOrientableCrosscapPosition p n i 1) u =
              nonOrientableOccurrencePoint p n
                (nonOrientableBoundaryPosition p n j 1) t at hpoint
        rcases hpoint with hx | hy
        · exact (nonOrientableBoundaryInterior_ne_occurrencePoint j t ht0 ht1
            (nonOrientableCrosscapPosition p n i 0) u (by
              intro h
              have := congrArg Fin.val h
              simp only [nonOrientableCrosscapPosition_val,
                nonOrientableBoundaryPosition_val] at this
              omega)) hx.symm
        · exact (nonOrientableBoundaryInterior_ne_occurrencePoint j t ht0 ht1
            (nonOrientableCrosscapPosition p n i 1) u (by
              intro h
              have := congrArg Fin.val h
              simp only [nonOrientableCrosscapPosition_val,
                nonOrientableBoundaryPosition_val] at this
              omega)) hy.symm
      · change
          nonOrientableOccurrencePoint p n
                (nonOrientableCrosscapPosition p n i 1) u =
              nonOrientableOccurrencePoint p n
                (nonOrientableBoundaryPosition p n j 1) t ∨
            nonOrientableOccurrencePoint p n
                (nonOrientableCrosscapPosition p n i 0) u =
              nonOrientableOccurrencePoint p n
                (nonOrientableBoundaryPosition p n j 1) t at hpoint
        rcases hpoint with hx | hy
        · exact (nonOrientableBoundaryInterior_ne_occurrencePoint j t ht0 ht1
            (nonOrientableCrosscapPosition p n i 1) u (by
              intro h
              have := congrArg Fin.val h
              simp only [nonOrientableCrosscapPosition_val,
                nonOrientableBoundaryPosition_val] at this
              omega)) hx.symm
        · exact (nonOrientableBoundaryInterior_ne_occurrencePoint j t ht0 ht1
            (nonOrientableCrosscapPosition p n i 0) u (by
              intro h
              have := congrArg Fin.val h
              simp only [nonOrientableCrosscapPosition_val,
                nonOrientableBoundaryPosition_val] at this
              omega)) hy.symm
      · change
          nonOrientableOccurrencePoint p n
                (nonOrientableBoundaryPosition p n k 0) u =
              nonOrientableOccurrencePoint p n
                (nonOrientableBoundaryPosition p n j 1) t ∨
            nonOrientableOccurrencePoint p n
                (nonOrientableBoundaryPosition p n k 2)
                  (unitInterval.symm u) =
              nonOrientableOccurrencePoint p n
                (nonOrientableBoundaryPosition p n j 1) t at hpoint
        rcases hpoint with hx | hy
        · exact (nonOrientableBoundaryInterior_ne_occurrencePoint j t ht0 ht1
            (nonOrientableBoundaryPosition p n k 0) u (by
              intro h
              have := congrArg Fin.val h
              simp only [nonOrientableBoundaryPosition_val] at this
              omega)) hx.symm
        · exact (nonOrientableBoundaryInterior_ne_occurrencePoint j t ht0 ht1
            (nonOrientableBoundaryPosition p n k 2) (unitInterval.symm u) (by
              intro h
              have := congrArg Fin.val h
              simp only [nonOrientableBoundaryPosition_val] at this
              omega)) hy.symm
      · change
          nonOrientableOccurrencePoint p n
                (nonOrientableBoundaryPosition p n k 2) u =
              nonOrientableOccurrencePoint p n
                (nonOrientableBoundaryPosition p n j 1) t ∨
            nonOrientableOccurrencePoint p n
                (nonOrientableBoundaryPosition p n k 0)
                  (unitInterval.symm u) =
              nonOrientableOccurrencePoint p n
                (nonOrientableBoundaryPosition p n j 1) t at hpoint
        rcases hpoint with hx | hy
        · exact (nonOrientableBoundaryInterior_ne_occurrencePoint j t ht0 ht1
            (nonOrientableBoundaryPosition p n k 2) u (by
              intro h
              have := congrArg Fin.val h
              simp only [nonOrientableBoundaryPosition_val] at this
              omega)) hx.symm
        · exact (nonOrientableBoundaryInterior_ne_occurrencePoint j t ht0 ht1
            (nonOrientableBoundaryPosition p n k 0) (unitInterval.symm u) (by
              intro h
              have := congrArg Fin.val h
              simp only [nonOrientableBoundaryPosition_val] at this
              omega)) hy.symm

private theorem nonOrientableEqvGen_preserves_boundaryInterior
    {p n : ℕ} (hp : 1 ≤ p) (j : Fin n)
    (t : unitInterval) (ht0 : t ≠ 0) (ht1 : t ≠ 1)
    {x y : (nonOrientableCellComplex p n).PolygonalPreRealization}
    (hxy : Relation.EqvGen
      (PolygonGluing.Generator
        ((nonOrientableCellComplex p n).polygonalIdentifications
          (nonOrientableCellComplex_occurrencePairingValid hp))) x y) :
    (x = nonOrientableOccurrencePoint p n
          (nonOrientableBoundaryPosition p n j 1) t) ↔
      (y = nonOrientableOccurrencePoint p n
          (nonOrientableBoundaryPosition p n j 1) t) := by
  induction hxy with
  | rel x y h =>
      constructor <;> intro hpoint
      · exact (nonOrientableGenerator_avoids_boundaryInterior
          hp j t ht0 ht1 h (Or.inl hpoint)).elim
      · exact (nonOrientableGenerator_avoids_boundaryInterior
          hp j t ht0 ht1 h (Or.inr hpoint)).elim
  | refl => exact Iff.rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

private theorem nonOrientableEqvGen_preserves_boundaryPrecomponent
    {p n : ℕ} (hp : 1 ≤ p) (j : Fin n)
    {x y : (nonOrientableCellComplex p n).PolygonalPreRealization}
    (hxy : Relation.EqvGen
      (PolygonGluing.Generator
        ((nonOrientableCellComplex p n).polygonalIdentifications
          (nonOrientableCellComplex_occurrencePairingValid hp))) x y) :
    x ∈ nonOrientableBoundaryPrecomponent p n j ↔
      y ∈ nonOrientableBoundaryPrecomponent p n j := by
  induction hxy with
  | rel _ _ h =>
      exact nonOrientableGenerator_preserves_boundaryPrecomponent hp j h
  | refl => exact Iff.rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

private theorem nonOrientableBoundary_h_mem_iff
    {p n : ℕ} (j k : Fin n) (u : unitInterval) :
    nonOrientableOccurrencePoint p n
        (nonOrientableBoundaryPosition p n k 1) u ∈
        nonOrientableBoundaryPrecomponent p n j ↔
      k = j := by
  rw [nonOrientableOccurrencePoint_mem_boundaryPrecomponent_iff]
  simp only [nonOrientableBoundaryPosition_val]
  constructor
  · intro h
    rcases h with h | ⟨h, _hu⟩ | ⟨h, _hu⟩
    · apply Fin.ext
      have := congrArg Fin.val h
      simp only [nonOrientableBoundaryPosition_val] at this
      omega
    · omega
    · omega
  · rintro rfl
    exact Or.inl rfl

private def nonOrientableBoundaryComponent
    {p n : ℕ} (hp : 1 ≤ p) (j : Fin n) :
    Set ((nonOrientableCellComplex p n).PolygonalRealization
      (nonOrientableCellComplex_occurrencePairingValid hp)) :=
  Set.range (fun t ↦
    (nonOrientableCellComplex p n).polygonalMk
      (nonOrientableCellComplex_occurrencePairingValid hp)
      (nonOrientableOccurrencePoint p n
        (nonOrientableBoundaryPosition p n j 1) t))

private theorem nonOrientableBoundaryComponent_pairwise_disjoint
    {p n : ℕ} (hp : 1 ≤ p)
    {j k : Fin n} (hjk : j ≠ k) :
    Disjoint (nonOrientableBoundaryComponent hp j)
      (nonOrientableBoundaryComponent hp k) := by
  rw [Set.disjoint_left]
  intro q hqj hqk
  rcases hqj with ⟨t, rfl⟩
  rcases hqk with ⟨u, hu⟩
  have heqv := Quotient.exact hu.symm
  have hpreserve :=
    (nonOrientableEqvGen_preserves_boundaryPrecomponent hp j heqv).mp
      (show nonOrientableOccurrencePoint p n
          (nonOrientableBoundaryPosition p n j 1) t ∈
          nonOrientableBoundaryPrecomponent p n j from ⟨t, rfl⟩)
  rw [nonOrientableBoundary_h_mem_iff] at hpreserve
  exact hjk hpreserve.symm

private theorem continuous_nonOrientableOccurrencePoint
    (p n : ℕ) (i : Fin (nonOrientableBoundaryWord p n).length) :
    Continuous (nonOrientableOccurrencePoint p n i) := by
  let e := oneFacePolygonalPreRealizationHomeomorph
    (nonOrientableBoundaryWord p n)
  have hcarrier : Continuous (fun t : unitInterval ↦
      ClosedUnitDisc.bdyPtOfReal
        (((i.val : ℝ) + (t : ℝ)) /
          (nonOrientableBoundaryWord p n).length)) := by
    apply Continuous.subtype_mk
    fun_prop
  have heq : nonOrientableOccurrencePoint p n i = fun t : unitInterval ↦
      e.symm (ClosedUnitDisc.bdyPtOfReal
        (((i.val : ℝ) + (t : ℝ)) /
          (nonOrientableBoundaryWord p n).length)) := by
    funext t
    apply e.injective
    rw [Homeomorph.apply_symm_apply]
    exact nonOrientableCarrier_occurrencePoint p n i t
  rw [heq]
  exact e.symm.continuous.comp hcarrier

private theorem isCompact_nonOrientableBoundaryComponent
    {p n : ℕ} (hp : 1 ≤ p) (j : Fin n) :
    IsCompact (nonOrientableBoundaryComponent hp j) := by
  apply isCompact_range
  exact ((nonOrientableCellComplex p n).continuous_polygonalMk _).comp
    (continuous_nonOrientableOccurrencePoint p n _)

private def nonOrientableBoundaryComponentsLocus
    {p n : ℕ} (hp : 1 ≤ p) :
    Set ((nonOrientableCellComplex p n).PolygonalRealization
      (nonOrientableCellComplex_occurrencePairingValid hp)) :=
  ⋃ j : Fin n, nonOrientableBoundaryComponent hp j

private theorem isCompact_nonOrientableBoundaryComponentsLocus
    {p n : ℕ} (hp : 1 ≤ p) :
    IsCompact (nonOrientableBoundaryComponentsLocus
      (p := p) (n := n) hp) := by
  apply isCompact_iUnion
  exact isCompact_nonOrientableBoundaryComponent hp

private theorem nonOrientableBoundaryComponents_eq_one_of_isConnected
    {p n : ℕ} (hp : 1 ≤ p)
    [T2Space ((nonOrientableCellComplex p n).PolygonalRealization
      (nonOrientableCellComplex_occurrencePairingValid hp))]
    (hconnected : IsConnected
      (nonOrientableBoundaryComponentsLocus
        (p := p) (n := n) hp)) :
    n = 1 := by
  have hnpos : 0 < n := by
    rcases hconnected.nonempty with ⟨q, hq⟩
    rcases Set.mem_iUnion.mp hq with ⟨j, _hj⟩
    exact Nat.pos_of_ne_zero (by
      intro hn
      subst n
      exact Fin.elim0 j)
  by_contra hnOne
  have hnTwo : 2 ≤ n := by omega
  let j₀ : Fin n := ⟨0, hnpos⟩
  let j₁ : Fin n := ⟨1, hnTwo⟩
  let A := nonOrientableBoundaryComponent hp j₀
  let B := ⋃ k : {k : Fin n // k ≠ j₀},
    nonOrientableBoundaryComponent hp k.1
  have hAclosed : IsClosed A :=
    (isCompact_nonOrientableBoundaryComponent hp j₀).isClosed
  have hBcompact : IsCompact B := by
    apply isCompact_iUnion
    intro k
    exact isCompact_nonOrientableBoundaryComponent hp k.1
  have hBclosed : IsClosed B := hBcompact.isClosed
  have hcover :
      nonOrientableBoundaryComponentsLocus
          (p := p) (n := n) hp ⊆ A ∪ B := by
    intro q hq
    rcases Set.mem_iUnion.mp hq with ⟨k, hk⟩
    by_cases hkj₀ : k = j₀
    · left
      simpa only [A, hkj₀] using hk
    · right
      exact Set.mem_iUnion.mpr ⟨⟨k, hkj₀⟩, hk⟩
  have hAmeet :
      (nonOrientableBoundaryComponentsLocus
          (p := p) (n := n) hp ∩ A).Nonempty := by
    let q := (nonOrientableCellComplex p n).polygonalMk
      (nonOrientableCellComplex_occurrencePairingValid hp)
      (nonOrientableOccurrencePoint p n
        (nonOrientableBoundaryPosition p n j₀ 1) 0)
    have hqA : q ∈ A := ⟨0, rfl⟩
    refine ⟨q, ?_, hqA⟩
    exact Set.mem_iUnion.mpr ⟨j₀, hqA⟩
  have hj₁j₀ : j₁ ≠ j₀ := by
    intro h
    have := congrArg Fin.val h
    simp only [j₀, j₁] at this
    omega
  have hBmeet :
      (nonOrientableBoundaryComponentsLocus
          (p := p) (n := n) hp ∩ B).Nonempty := by
    let q := (nonOrientableCellComplex p n).polygonalMk
      (nonOrientableCellComplex_occurrencePairingValid hp)
      (nonOrientableOccurrencePoint p n
        (nonOrientableBoundaryPosition p n j₁ 1) 0)
    have hqj₁ : q ∈ nonOrientableBoundaryComponent hp j₁ := ⟨0, rfl⟩
    refine ⟨q, Set.mem_iUnion.mpr ⟨j₁, hqj₁⟩, ?_⟩
    exact Set.mem_iUnion.mpr ⟨⟨j₁, hj₁j₀⟩, hqj₁⟩
  have hABdisjoint : Disjoint A B := by
    rw [Set.disjoint_left]
    intro q hqA hqB
    rcases Set.mem_iUnion.mp hqB with ⟨k, hqk⟩
    exact Set.disjoint_left.mp
      (nonOrientableBoundaryComponent_pairwise_disjoint hp
        (j := j₀) (k := k.1) (Ne.symm k.property))
      hqA hqk
  obtain ⟨q, _hqL, hqA, hqB⟩ :=
    (isPreconnected_closed_iff.mp hconnected.isPreconnected)
      A B hAclosed hBclosed hcover hAmeet hBmeet
  exact Set.disjoint_left.mp hABdisjoint hqA hqB

private theorem orientableBoundaryComponent_injective_Ico
    (p : ℕ) (t u : unitInterval)
    (ht : (t : ℝ) < 1) (hu : (u : ℝ) < 1)
    (h : (orientableCellComplex p 1).polygonalMk
          (orientableCellComplex_occurrencePairingValid (Or.inr (by omega)))
          (orientableOccurrencePoint p 1
            (orientableBoundaryPosition p 1 0 1) t) =
        (orientableCellComplex p 1).polygonalMk
          (orientableCellComplex_occurrencePairingValid (Or.inr (by omega)))
          (orientableOccurrencePoint p 1
            (orientableBoundaryPosition p 1 0 1) u)) :
    t = u := by
  have heqv := Quotient.exact h
  by_cases ht0 : t = 0
  · subst t
    by_cases hu0 : u = 0
    · exact hu0.symm
    · have hu1 : u ≠ 1 := by
        intro hu1
        subst u
        norm_num at hu
      have hpoint :=
        (orientableEqvGen_preserves_boundaryInterior
          (p := p) (n := 1) (Or.inr (by omega)) 0 u hu0 hu1
          heqv.symm).mp rfl
      exact orientableBoundaryOccurrencePoint_injective 0 0 u hpoint
  · have ht1 : t ≠ 1 := by
      intro ht1
      subst t
      norm_num at ht
    have hpoint :=
      (orientableEqvGen_preserves_boundaryInterior
        (p := p) (n := 1) (Or.inr (by omega)) 0 t ht0 ht1 heqv).mp rfl
    exact orientableBoundaryOccurrencePoint_injective 0 t u hpoint.symm

private theorem nonOrientableBoundaryComponent_injective_Ico
    (p : ℕ) (hp : 1 ≤ p) (t u : unitInterval)
    (ht : (t : ℝ) < 1) (hu : (u : ℝ) < 1)
    (h : (nonOrientableCellComplex p 1).polygonalMk
          (nonOrientableCellComplex_occurrencePairingValid hp)
          (nonOrientableOccurrencePoint p 1
            (nonOrientableBoundaryPosition p 1 0 1) t) =
        (nonOrientableCellComplex p 1).polygonalMk
          (nonOrientableCellComplex_occurrencePairingValid hp)
          (nonOrientableOccurrencePoint p 1
            (nonOrientableBoundaryPosition p 1 0 1) u)) :
    t = u := by
  have heqv := Quotient.exact h
  by_cases ht0 : t = 0
  · subst t
    by_cases hu0 : u = 0
    · exact hu0.symm
    · have hu1 : u ≠ 1 := by
        intro hu1
        subst u
        norm_num at hu
      have hpoint :=
        (nonOrientableEqvGen_preserves_boundaryInterior
          (p := p) (n := 1) hp 0 u hu0 hu1 heqv.symm).mp rfl
      exact nonOrientableBoundaryOccurrencePoint_injective 0 0 u hpoint
  · have ht1 : t ≠ 1 := by
      intro ht1
      subst t
      norm_num at ht
    have hpoint :=
      (nonOrientableEqvGen_preserves_boundaryInterior
        (p := p) (n := 1) hp 0 t ht0 ht1 heqv).mp rfl
    exact nonOrientableBoundaryOccurrencePoint_injective 0 t u hpoint.symm

private theorem orientablePolygonalRealizationHomeomorph_boundaryPoint
    {p n : ℕ} (hvalid : 1 ≤ p ∨ 1 ≤ n)
    (j : Fin n) (t : unitInterval) :
    orientablePolygonalRealizationHomeomorph hvalid
        ((orientableCellComplex p n).polygonalMk
          (orientableCellComplex_occurrencePairingValid hvalid)
          (orientableOccurrencePoint p n
            (orientableBoundaryPosition p n j 1) t)) =
      Quot.mk (OrientableRel p n)
        (ClosedUnitDisc.bdyPtOfReal
          ((4 * (p : ℝ) + 3 * (j : ℝ) + 1 + (t : ℝ)) /
            (4 * p + 3 * n))) := by
  change Quot.mk (OrientableRel p n)
      (oneFacePolygonalPreRealizationHomeomorph
        (orientableBoundaryWord p n)
        (orientableOccurrencePoint p n
          (orientableBoundaryPosition p n j 1) t)) = _
  rw [orientableCarrier_boundary_h_pos]

private theorem nonOrientablePolygonalRealizationHomeomorph_boundaryPoint
    {p n : ℕ} (hp : 1 ≤ p) (j : Fin n) (t : unitInterval) :
    nonOrientablePolygonalRealizationHomeomorph hp
        ((nonOrientableCellComplex p n).polygonalMk
          (nonOrientableCellComplex_occurrencePairingValid hp)
          (nonOrientableOccurrencePoint p n
            (nonOrientableBoundaryPosition p n j 1) t)) =
      Quot.mk (NonOrientableRel p n)
        (ClosedUnitDisc.bdyPtOfReal
          ((2 * (p : ℝ) + 3 * (j : ℝ) + 1 + (t : ℝ)) /
            (2 * p + 3 * n))) := by
  change Quot.mk (NonOrientableRel p n)
      (oneFacePolygonalPreRealizationHomeomorph
        (nonOrientableBoundaryWord p n)
        (nonOrientableOccurrencePoint p n
          (nonOrientableBoundaryPosition p n j 1) t)) = _
  rw [nonOrientableCarrier_boundary_h_pos]

private theorem orientablePolygonalBoundaryPoint_one_eq_normalBoundaryArc
    (p : ℕ) (t : unitInterval) :
    orientablePolygonalRealizationHomeomorph (Or.inr (by omega))
        ((orientableCellComplex p 1).polygonalMk
          (orientableCellComplex_occurrencePairingValid (Or.inr (by omega)))
          (orientableOccurrencePoint p 1
            (orientableBoundaryPosition p 1 0 1) t)) =
      orientableNormalBoundaryArc p t := by
  rw [orientablePolygonalRealizationHomeomorph_boundaryPoint]
  unfold orientableNormalBoundaryArc orientableNormalBoundaryCarrierArc
  apply congrArg (Quot.mk (OrientableRel p 1))
  norm_num only [Fin.coe_ofNat_eq_mod, Nat.one_mod, Nat.cast_zero,
    Nat.cast_one, mul_zero, add_zero, mul_one]
  have harg :
      (4 * (p : ℝ) + 1 + (t : ℝ)) / (4 * p + 3) =
        ((t : ℝ) - 2) / (4 * p + 3) + (1 : ℤ) := by
    norm_num only [Int.cast_one]
    have hden : 4 * (p : ℝ) + 3 ≠ 0 := by positivity
    field_simp
    ring
  rw [harg]
  exact ClosedUnitDisc.bdyPtOfReal_add_int _ 1

private theorem nonOrientablePolygonalBoundaryPoint_one_eq_normalBoundaryArc
    (p : ℕ) (hp : 1 ≤ p) (t : unitInterval) :
    nonOrientablePolygonalRealizationHomeomorph hp
        ((nonOrientableCellComplex p 1).polygonalMk
          (nonOrientableCellComplex_occurrencePairingValid hp)
          (nonOrientableOccurrencePoint p 1
            (nonOrientableBoundaryPosition p 1 0 1) t)) =
      nonOrientableNormalBoundaryArc p t := by
  rw [nonOrientablePolygonalRealizationHomeomorph_boundaryPoint]
  unfold nonOrientableNormalBoundaryArc nonOrientableNormalBoundaryCarrierArc
  apply congrArg (Quot.mk (NonOrientableRel p 1))
  norm_num only [Fin.coe_ofNat_eq_mod, Nat.one_mod, Nat.cast_zero,
    Nat.cast_one, mul_zero, add_zero, mul_one]
  have harg :
      (2 * (p : ℝ) + 1 + (t : ℝ)) / (2 * p + 3) =
        ((t : ℝ) - 2) / (2 * p + 3) + (1 : ℤ) := by
    norm_num only [Int.cast_one]
    have hden : 2 * (p : ℝ) + 3 ≠ 0 := by positivity
    field_simp
    ring
  rw [harg]
  exact ClosedUnitDisc.bdyPtOfReal_add_int _ 1

/-- The canonical free boundary loop of an orientable one-boundary normal
form is a Jordan parametrization. -/
theorem injective_orientableNormalBoundaryLoop (p : ℕ) :
    Function.Injective (orientableNormalBoundaryLoop p) := by
  intro x y hxy
  obtain ⟨a, ha, hax⟩ := AddCircle.eq_coe_Ico x
  obtain ⟨b, hb, hby⟩ := AddCircle.eq_coe_Ico y
  let t : unitInterval := ⟨a, ha.1, ha.2.le⟩
  let u : unitInterval := ⟨b, hb.1, hb.2.le⟩
  have hnormal : orientableNormalBoundaryArc p t =
      orientableNormalBoundaryArc p u := by
    rw [← hax, ← hby] at hxy
    change orientableNormalBoundaryLoop p
        (((t : unitInterval) : ℝ) : UnitAddCircle) =
      orientableNormalBoundaryLoop p
        (((u : unitInterval) : ℝ) : UnitAddCircle) at hxy
    rw [orientableNormalBoundaryLoop_apply_unitInterval,
      orientableNormalBoundaryLoop_apply_unitInterval] at hxy
    exact hxy
  have himage :
      orientablePolygonalRealizationHomeomorph (Or.inr (by omega))
          ((orientableCellComplex p 1).polygonalMk
            (orientableCellComplex_occurrencePairingValid (Or.inr (by omega)))
            (orientableOccurrencePoint p 1
              (orientableBoundaryPosition p 1 0 1) t)) =
        orientablePolygonalRealizationHomeomorph (Or.inr (by omega))
          ((orientableCellComplex p 1).polygonalMk
            (orientableCellComplex_occurrencePairingValid (Or.inr (by omega)))
            (orientableOccurrencePoint p 1
              (orientableBoundaryPosition p 1 0 1) u)) := by
    rw [orientablePolygonalBoundaryPoint_one_eq_normalBoundaryArc,
      orientablePolygonalBoundaryPoint_one_eq_normalBoundaryArc]
    exact hnormal
  have hquotient :=
    (orientablePolygonalRealizationHomeomorph
      (p := p) (n := 1) (Or.inr (by omega))).injective himage
  have htu : t = u := orientableBoundaryComponent_injective_Ico
    p t u (by simpa only [t] using ha.2) (by simpa only [u] using hb.2)
    hquotient
  calc
    x = (a : UnitAddCircle) := hax.symm
    _ = (b : UnitAddCircle) := congrArg (fun z : ℝ ↦ (z : UnitAddCircle))
      (congrArg Subtype.val htu)
    _ = y := hby

/-- The canonical free boundary loop of a nonorientable one-boundary normal
form is a Jordan parametrization. -/
theorem injective_nonOrientableNormalBoundaryLoop (p : ℕ) (hp : 1 ≤ p) :
    Function.Injective (nonOrientableNormalBoundaryLoop p) := by
  intro x y hxy
  obtain ⟨a, ha, hax⟩ := AddCircle.eq_coe_Ico x
  obtain ⟨b, hb, hby⟩ := AddCircle.eq_coe_Ico y
  let t : unitInterval := ⟨a, ha.1, ha.2.le⟩
  let u : unitInterval := ⟨b, hb.1, hb.2.le⟩
  have hnormal : nonOrientableNormalBoundaryArc p t =
      nonOrientableNormalBoundaryArc p u := by
    rw [← hax, ← hby] at hxy
    change nonOrientableNormalBoundaryLoop p
        (((t : unitInterval) : ℝ) : UnitAddCircle) =
      nonOrientableNormalBoundaryLoop p
        (((u : unitInterval) : ℝ) : UnitAddCircle) at hxy
    rw [nonOrientableNormalBoundaryLoop_apply_unitInterval,
      nonOrientableNormalBoundaryLoop_apply_unitInterval] at hxy
    exact hxy
  have himage :
      nonOrientablePolygonalRealizationHomeomorph hp
          ((nonOrientableCellComplex p 1).polygonalMk
            (nonOrientableCellComplex_occurrencePairingValid hp)
            (nonOrientableOccurrencePoint p 1
              (nonOrientableBoundaryPosition p 1 0 1) t)) =
        nonOrientablePolygonalRealizationHomeomorph hp
          ((nonOrientableCellComplex p 1).polygonalMk
            (nonOrientableCellComplex_occurrencePairingValid hp)
            (nonOrientableOccurrencePoint p 1
              (nonOrientableBoundaryPosition p 1 0 1) u)) := by
    rw [nonOrientablePolygonalBoundaryPoint_one_eq_normalBoundaryArc,
      nonOrientablePolygonalBoundaryPoint_one_eq_normalBoundaryArc]
    exact hnormal
  have hquotient :=
    (nonOrientablePolygonalRealizationHomeomorph
      (p := p) (n := 1) hp).injective himage
  have htu : t = u := nonOrientableBoundaryComponent_injective_Ico
    p hp t u (by simpa only [t] using ha.2) (by simpa only [u] using hb.2)
    hquotient
  calc
    x = (a : UnitAddCircle) := hax.symm
    _ = (b : UnitAddCircle) := congrArg (fun z : ℝ ↦ (z : UnitAddCircle))
      (congrArg Subtype.val htu)
    _ = y := hby

private theorem image_orientablePolygonalRealizationHomeomorph_boundaryComponentsLocus
    {p n : ℕ} (hvalid : 1 ≤ p ∨ 1 ≤ n) :
    orientablePolygonalRealizationHomeomorph hvalid ''
        orientableBoundaryComponentsLocus hvalid =
      orientableRawBoundaryLocus p n := by
  ext q
  constructor
  · rintro ⟨x, hx, rfl⟩
    rcases Set.mem_iUnion.mp hx with ⟨j, t, rfl⟩
    exact ⟨j, t,
      orientablePolygonalRealizationHomeomorph_boundaryPoint
        hvalid j t⟩
  · rintro ⟨j, t, rfl⟩
    let x := (orientableCellComplex p n).polygonalMk
      (orientableCellComplex_occurrencePairingValid hvalid)
      (orientableOccurrencePoint p n
        (orientableBoundaryPosition p n j 1) t)
    refine ⟨x, Set.mem_iUnion.mpr ⟨j, t, rfl⟩, ?_⟩
    exact orientablePolygonalRealizationHomeomorph_boundaryPoint
      hvalid j t

private theorem image_nonOrientablePolygonalRealizationHomeomorph_boundaryComponentsLocus
    {p n : ℕ} (hp : 1 ≤ p) :
    nonOrientablePolygonalRealizationHomeomorph hp ''
        nonOrientableBoundaryComponentsLocus
          (p := p) (n := n) hp =
      nonOrientableRawBoundaryLocus p n := by
  ext q
  constructor
  · rintro ⟨x, hx, rfl⟩
    rcases Set.mem_iUnion.mp hx with ⟨j, t, rfl⟩
    exact ⟨j, t,
      nonOrientablePolygonalRealizationHomeomorph_boundaryPoint hp j t⟩
  · rintro ⟨j, t, rfl⟩
    let x := (nonOrientableCellComplex p n).polygonalMk
      (nonOrientableCellComplex_occurrencePairingValid hp)
      (nonOrientableOccurrencePoint p n
        (nonOrientableBoundaryPosition p n j 1) t)
    refine ⟨x, Set.mem_iUnion.mpr ⟨j, t, rfl⟩, ?_⟩
    exact nonOrientablePolygonalRealizationHomeomorph_boundaryPoint hp j t

/-- A connected complete free-side locus in an orientable canonical quotient
forces the normal form to have exactly one boundary block. -/
theorem orientableRawBoundaryLocus_eq_one_of_isConnected
    {p n : ℕ} (hvalid : 1 ≤ p ∨ 1 ≤ n)
    [T2Space (Quot (OrientableRel p n))]
    (hconnected : IsConnected (orientableRawBoundaryLocus p n)) :
    n = 1 := by
  letI : T2Space ((orientableCellComplex p n).PolygonalRealization
      (orientableCellComplex_occurrencePairingValid hvalid)) :=
    (orientablePolygonalRealizationHomeomorph hvalid).symm.t2Space
  apply orientableBoundaryComponents_eq_one_of_isConnected hvalid
  rw [← (orientablePolygonalRealizationHomeomorph hvalid).isConnected_image]
  rw [image_orientablePolygonalRealizationHomeomorph_boundaryComponentsLocus]
  exact hconnected

/-- A connected complete free-side locus in a nonorientable canonical quotient
forces the normal form to have exactly one boundary block. -/
theorem nonOrientableRawBoundaryLocus_eq_one_of_isConnected
    {p n : ℕ} (hp : 1 ≤ p)
    [T2Space (Quot (NonOrientableRel p n))]
    (hconnected : IsConnected (nonOrientableRawBoundaryLocus p n)) :
    n = 1 := by
  letI : T2Space ((nonOrientableCellComplex p n).PolygonalRealization
      (nonOrientableCellComplex_occurrencePairingValid hp)) :=
    (nonOrientablePolygonalRealizationHomeomorph hp).symm.t2Space
  apply nonOrientableBoundaryComponents_eq_one_of_isConnected hp
  rw [← (nonOrientablePolygonalRealizationHomeomorph hp).isConnected_image]
  rw [image_nonOrientablePolygonalRealizationHomeomorph_boundaryComponentsLocus]
  exact hconnected

end GromovFilling
