/-
Copyright (c) 2026 ClassificationOfSurfaces contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ClassificationOfSurfaces contributors
-/
/-
Modified by GromovFilling contributors in 2026 for compatibility with
Lean/mathlib v4.29.0; see `ClassificationOfSurfaces/VENDOR.md`.
-/
import ClassificationOfSurfaces.Moise.EmbeddedComplexValence
import ClassificationOfSurfaces.Triangulation

/-!
# Boundary edges of an embedded triangle complex

This file supplies the local half-disk/disk charts at the midpoint of a simplicial edge.  A
single incident triangle gives a boundary point, while two incident triangles give an interior
point.  These are the local topological inputs needed to identify the combinatorial boundary of
a boundary-regular Radó triangulation with the ambient manifold boundary.
-/

open scoped Manifold

namespace LeanEval
namespace Topology
namespace ClassificationOfSurfaces
namespace Moise

open InvarianceOfDomain Set

/-- The midpoint of an intrinsic edge in barycentric coordinates. -/
noncomputable def IntrinsicTwoComplex.edgeMidpoint
    (K : IntrinsicTwoComplex) (e : K.Edge) : K.realization :=
  K.edgePath e ⟨1 / 2, by constructor <;> norm_num⟩

@[simp] theorem IntrinsicTwoComplex.edgeMidpoint_apply_first
    (K : IntrinsicTwoComplex) (e : K.Edge) :
    (K.edgeMidpoint e).1 (K.edgeFirst e) = 1 / 2 := by
  rw [IntrinsicTwoComplex.edgeMidpoint, K.edgePath_apply_first]
  ring

@[simp] theorem IntrinsicTwoComplex.edgeMidpoint_apply_second
    (K : IntrinsicTwoComplex) (e : K.Edge) :
    (K.edgeMidpoint e).1 (K.edgeSecond e) = 1 / 2 := by
  simp [IntrinsicTwoComplex.edgeMidpoint]

/-- A barycentric carrier on at most one vertex contains at most one realization point. -/
theorem IntrinsicTwoComplex.eq_of_mem_faceCarrier_of_card_le_one
    (K : IntrinsicTwoComplex) {b : Finset K.Vertex}
    (hb : b.card ≤ 1) {x y : K.realization}
    (hx : x ∈ K.faceCarrier b) (hy : y ∈ K.faceCarrier b) :
    x = y := by
  classical
  rcases Nat.lt_or_eq_of_le hb with hzero | hone
  · have hbempty : b = ∅ := Finset.card_eq_zero.mp (by omega)
    have hxzero : ∀ v, x.1 v = 0 := by
      intro v
      apply (K.mem_faceCarrier_iff b x).mp hx
      rw [hbempty]
      simp
    have : (0 : ℝ) = 1 := by
      calc
        0 = ∑ v, x.1 v := by simp [hxzero]
        _ = 1 := x.2.1.2
    norm_num at this
  · obtain ⟨v, hbcard⟩ := Finset.card_eq_one.mp hone
    apply Subtype.ext
    funext w
    by_cases hw : w = v
    · subst w
      have hxsum : x.1 v = 1 := by
        calc
          x.1 v = ∑ z ∈ b, x.1 z := by rw [hbcard]; simp
          _ = ∑ z, x.1 z := Finset.sum_subset
            (Finset.subset_univ b)
            (fun z _ hz => (K.mem_faceCarrier_iff b x).mp hx z hz)
          _ = 1 := x.2.1.2
      have hysum : y.1 v = 1 := by
        calc
          y.1 v = ∑ z ∈ b, y.1 z := by rw [hbcard]; simp
          _ = ∑ z, y.1 z := Finset.sum_subset
            (Finset.subset_univ b)
            (fun z _ hz => (K.mem_faceCarrier_iff b y).mp hy z hz)
          _ = 1 := y.2.1.2
      rw [hxsum, hysum]
    · have hwb : w ∉ b := by simpa [hbcard]
      rw [(K.mem_faceCarrier_iff b x).mp hx w hwb,
        (K.mem_faceCarrier_iff b y).mp hy w hwb]

/-- If an edge belongs to exactly one triangle, its barycentric midpoint is a boundary point
after any homeomorphic realization as a surface with boundary.

The proof constructs an explicit open half-plane chart.  Positivity of the two edge weights
cuts out an open neighborhood in the realization; the unique-page hypothesis identifies that
neighborhood with an open subset of `EuclideanHalfSpace 2`. -/
theorem IntrinsicTwoComplex.isBoundaryPoint_homeo_edgeMidpoint_of_faceValence_one
    {S : Type*} [TopologicalSpace S]
    [ChartedSpace (EuclideanHalfSpace 2) S]
    (K : IntrinsicTwoComplex) (h : K.realization ≃ₜ S)
    (e : K.Edge)
    (hone : (K.faces.filter fun t => e.1 ⊆ t).card = 1) :
    (modelWithCornersEuclideanHalfSpace 2).IsBoundaryPoint
      (h (K.edgeMidpoint e)) := by
  classical
  let a := K.edgeFirst e
  let b := K.edgeSecond e
  let t := K.edgeParent e
  have hab : a ≠ b := K.edgeFirst_ne_edgeSecond e
  have htF : t ∈ K.faces := K.edgeParent_mem e
  have het : e.1 ⊆ t := K.edge_subset_parent e
  have htUnique : ∀ u ∈ K.faces, e.1 ⊆ u → u = t := by
    intro u huF heu
    obtain ⟨q, hfilter⟩ := Finset.card_eq_one.mp hone
    have huq : u = q := by
      have : u ∈ K.faces.filter fun s => e.1 ⊆ s :=
        Finset.mem_filter.mpr ⟨huF, heu⟩
      rw [hfilter] at this
      exact Finset.mem_singleton.mp this
    have htq : t = q := by
      have : t ∈ K.faces.filter fun s => e.1 ⊆ s :=
        Finset.mem_filter.mpr ⟨htF, het⟩
      rw [hfilter] at this
      exact Finset.mem_singleton.mp this
    exact huq.trans htq.symm
  have hdiffcard : (t \ e.1).card = 1 := by
    rw [Finset.card_sdiff_of_subset het, K.faces_card t htF,
      K.card_of_mem_edges e.2]
  obtain ⟨c, htcDiff⟩ := Finset.card_eq_one.mp hdiffcard
  have hce : c ∉ e.1 := by
    have hc : c ∈ t \ e.1 := by rw [htcDiff]; simp
    exact (Finset.mem_sdiff.mp hc).2
  have htc : t = insert c e.1 := by
    rw [← Finset.sdiff_union_of_subset het, htcDiff]
    simp
  have hac : a ≠ c := by
    intro heq
    apply hce
    rw [← heq]
    exact K.edgeFirst_mem e
  have hbc : b ≠ c := by
    intro heq
    apply hce
    rw [← heq]
    exact K.edgeSecond_mem e
  let O : Set (EuclideanHalfSpace 2) :=
    {x | (1 / 4 : ℝ) < (1 - x.1 0) / 2 - x.1 1 ∧
      (1 / 4 : ℝ) < (1 - x.1 0) / 2 + x.1 1}
  have hOopen : IsOpen O := by
    have hleft : Continuous fun x : EuclideanHalfSpace 2 =>
        (1 - x.1 0) / 2 - x.1 1 := by fun_prop
    have hright : Continuous fun x : EuclideanHalfSpace 2 =>
        (1 - x.1 0) / 2 + x.1 1 := by fun_prop
    exact (isOpen_lt continuous_const hleft).inter
      (isOpen_lt continuous_const hright)
  let weight (x : EuclideanHalfSpace 2) : K.Vertex → ℝ :=
    ((1 - x.1 0) / 2 - x.1 1) •
        (Pi.single a (1 : ℝ) : K.Vertex → ℝ) +
      ((1 - x.1 0) / 2 + x.1 1) •
        (Pi.single b (1 : ℝ) : K.Vertex → ℝ) +
      x.1 0 • (Pi.single c (1 : ℝ) : K.Vertex → ℝ)
  have weight_a (x : EuclideanHalfSpace 2) :
      weight x a = (1 - x.1 0) / 2 - x.1 1 := by
    simp [weight, hab, hac]
  have weight_b (x : EuclideanHalfSpace 2) :
      weight x b = (1 - x.1 0) / 2 + x.1 1 := by
    simp [weight, hab, hbc]
  have weight_c (x : EuclideanHalfSpace 2) : weight x c = x.1 0 := by
    simp [weight, hac, hbc]
  have weight_other (x : EuclideanHalfSpace 2) {z : K.Vertex}
      (hza : z ≠ a) (hzb : z ≠ b) (hzc : z ≠ c) :
      weight x z = 0 := by
    simp [weight, hza, hzb, hzc]
  have sum_pi_single (q : K.Vertex) :
      ∑ z, Pi.single q (1 : ℝ) z = 1 := by
    rw [Fintype.sum_eq_single q]
    · simp
    · intro z hz
      exact Pi.single_eq_of_ne hz 1
  have weight_nonneg (x : O) (z : K.Vertex) : 0 ≤ weight x.1 z := by
    by_cases hza : z = a
    · subst z
      rw [weight_a]
      linarith [x.2.1]
    by_cases hzb : z = b
    · subst z
      rw [weight_b]
      linarith [x.2.2]
    by_cases hzc : z = c
    · subst z
      rw [weight_c]
      exact x.1.2
    rw [weight_other _ hza hzb hzc]
  have weight_sum (x : EuclideanHalfSpace 2) : ∑ z, weight x z = 1 := by
    simp_rw [weight, Pi.add_apply, Pi.smul_apply]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
      ← Finset.smul_sum, ← Finset.smul_sum, ← Finset.smul_sum,
      sum_pi_single a, sum_pi_single b, sum_pi_single c]
    simp only [smul_eq_mul, mul_one]
    ring
  have weight_supported (x : O) :
      ∃ s ∈ K.faces, ∀ z ∉ s, weight x.1 z = 0 := by
    refine ⟨t, htF, ?_⟩
    intro z hzt
    have hza : z ≠ a := fun hz => hzt (hz ▸ het (K.edgeFirst_mem e))
    have hzb : z ≠ b := fun hz => hzt (hz ▸ het (K.edgeSecond_mem e))
    have hzc : z ≠ c := fun hz => hzt (hz ▸ by rw [htc]; simp)
    exact weight_other _ hza hzb hzc
  let fan : O → K.realization := fun x =>
    ⟨weight x.1, ⟨weight_nonneg x, weight_sum x.1⟩,
      weight_supported x⟩
  have fan_continuous : Continuous fan := by
    apply Continuous.subtype_mk
    apply continuous_pi
    intro z
    change Continuous fun x : O => weight x.1 z
    simp only [weight, Pi.add_apply, Pi.smul_apply]
    fun_prop
  have fan_injective : Function.Injective fan := by
    intro x y hxy
    have hval : weight x.1 = weight y.1 := congrArg Subtype.val hxy
    have hc := congrFun hval c
    rw [weight_c, weight_c] at hc
    have ha := congrFun hval a
    rw [weight_a, weight_a] at ha
    have h1 : x.1.1 1 = y.1.1 1 := by linarith
    apply Subtype.ext
    apply EuclideanHalfSpace.ext
    apply PiLp.ext
    intro i
    fin_cases i
    · exact hc
    · exact h1
  let W : Set K.realization :=
    {y | (1 / 4 : ℝ) < y.1 a ∧ (1 / 4 : ℝ) < y.1 b}
  have hWopen : IsOpen W := by
    have haCont : Continuous fun y : K.realization => y.1 a :=
      (continuous_apply a).comp continuous_subtype_val
    have hbCont : Continuous fun y : K.realization => y.1 b :=
      (continuous_apply b).comp continuous_subtype_val
    exact (isOpen_lt continuous_const haCont).inter
      (isOpen_lt continuous_const hbCont)
  have fan_range : Set.range fan = W := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨by change (1 / 4 : ℝ) < weight x.1 a; rw [weight_a]; exact x.2.1,
        by change (1 / 4 : ℝ) < weight x.1 b; rw [weight_b]; exact x.2.2⟩
    · intro hy
      obtain ⟨s, hsF, hysupp⟩ := y.2.2
      have has : a ∈ s := by
        by_contra ha
        have := hysupp a ha
        linarith [hy.1]
      have hbs : b ∈ s := by
        by_contra hb
        have := hysupp b hb
        linarith [hy.2]
      have hes : e.1 ⊆ s := by
        rw [K.edge_eq_pair e]
        simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
        exact ⟨has, hbs⟩
      have hst : s = t := htUnique s hsF hes
      have hysuppT : ∀ z ∉ t, y.1 z = 0 := by
        simpa [hst] using hysupp
      have hsumT : y.1 a + y.1 b + y.1 c = 1 := by
        have hcPair : c ∉ ({a, b} : Finset K.Vertex) := by
          simp [Ne.symm hac, Ne.symm hbc]
        calc
          y.1 a + y.1 b + y.1 c = ∑ z ∈ t, y.1 z := by
            rw [htc, K.edge_eq_pair e]
            rw [Finset.sum_insert hcPair, Finset.sum_pair hab]
            ring
          _ = ∑ z, y.1 z := Finset.sum_subset
            (Finset.subset_univ t) (fun z _ hz => hysuppT z hz)
          _ = 1 := y.2.1.2
      let p : EuclideanHalfSpace 2 :=
        ⟨WithLp.toLp 2 (fun i => if i = 0 then y.1 c
          else (y.1 b - y.1 a) / 2), by simp; exact y.2.1.1 c⟩
      have p_zero : p.1 0 = y.1 c := by simp [p]
      have p_one : p.1 1 = (y.1 b - y.1 a) / 2 := by simp [p]
      have hpO : p ∈ O := by
        have hpa : (1 - y.1 c) / 2 - (y.1 b - y.1 a) / 2 = y.1 a := by
          linarith [hsumT]
        have hpb : (1 - y.1 c) / 2 + (y.1 b - y.1 a) / 2 = y.1 b := by
          linarith [hsumT]
        constructor
        · simp only [p_zero, p_one, hpa]
          exact hy.1
        · simp only [p_zero, p_one, hpb]
          exact hy.2
      let x : O := ⟨p, hpO⟩
      refine ⟨x, ?_⟩
      apply Subtype.ext
      funext z
      by_cases hza : z = a
      · subst z
        change weight p a = y.1 a
        rw [weight_a, p_zero, p_one]
        linarith
      by_cases hzb : z = b
      · subst z
        change weight p b = y.1 b
        rw [weight_b, p_zero, p_one]
        linarith
      by_cases hzc : z = c
      · subst z
        change weight p c = y.1 c
        exact weight_c p
      change weight p z = y.1 z
      rw [weight_other p hza hzb hzc]
      symm
      apply hysuppT
      rw [htc, K.edge_eq_pair e]
      simpa [a, b] using And.intro hzc (And.intro hza hzb)
  let recover : K.realization → EuclideanHalfSpace 2 := fun y =>
    ⟨WithLp.toLp 2 (fun i => if i = 0 then y.1 c
      else (y.1 b - y.1 a) / 2), by simp; exact y.2.1.1 c⟩
  have recover_continuous : Continuous recover := by
    apply Continuous.subtype_mk
    apply (PiLp.continuous_toLp 2 (fun _ : Fin 2 => ℝ)).comp
    apply continuous_pi
    intro i
    fin_cases i
    · simp only [Fin.zero_eta, ↓reduceIte]
      exact (continuous_apply c).comp continuous_subtype_val
    · simp only [Fin.mk_one, one_ne_zero, ↓reduceIte]
      exact (((continuous_apply b).comp continuous_subtype_val).sub
        ((continuous_apply a).comp continuous_subtype_val)).div_const 2
  have recover_fan : recover ∘ fan = ((↑) : O → EuclideanHalfSpace 2) := by
    funext x
    apply EuclideanHalfSpace.ext
    apply PiLp.ext
    intro i
    fin_cases i
    · change weight x.1 c = x.1.1 0
      exact weight_c x.1
    · change (weight x.1 b - weight x.1 a) / 2 = x.1.1 1
      rw [weight_a, weight_b]
      ring
  have fan_embedding : _root_.Topology.IsEmbedding fan := by
    apply _root_.Topology.IsEmbedding.of_comp fan_continuous recover_continuous
    rw [recover_fan]
    exact _root_.Topology.IsEmbedding.subtypeVal
  have fan_openEmbedding : _root_.Topology.IsOpenEmbedding fan :=
    ⟨fan_embedding, fan_range ▸ hWopen⟩
  have h_openEmbedding : _root_.Topology.IsOpenEmbedding (h ∘ fan) :=
    h.isOpenEmbedding.comp fan_openEmbedding
  have hzeroMem : (0 : EuclideanHalfSpace 2) ∈ O := by
    change (1 / 4 : ℝ) < (1 - 0) / 2 - 0 ∧
      (1 / 4 : ℝ) < (1 - 0) / 2 + 0
    norm_num
  let zeroO : O := ⟨0, hzeroMem⟩
  letI : Nonempty O := ⟨zeroO⟩
  let page : OpenPartialHomeomorph O S :=
    h_openEmbedding.toOpenPartialHomeomorph (h ∘ fan)
  let includeO : OpenPartialHomeomorph O (EuclideanHalfSpace 2) :=
    (⟨O, hOopen⟩ : TopologicalSpace.Opens (EuclideanHalfSpace 2))
      |>.openPartialHomeomorphSubtypeCoe ⟨zeroO⟩
  let chart : OpenPartialHomeomorph S (EuclideanHalfSpace 2) :=
    page.symm.trans includeO
  have fan_zero : fan zeroO = K.edgeMidpoint e := by
    apply Subtype.ext
    funext z
    by_cases hza : z = a
    · subst z
      rw [show (fan zeroO).1 a = weight zeroO.1 a by rfl,
        weight_a, K.edgeMidpoint_apply_first]
      change (1 - 0) / 2 - 0 = 1 / 2
      ring
    by_cases hzb : z = b
    · subst z
      rw [show (fan zeroO).1 b = weight zeroO.1 b by rfl,
        weight_b, K.edgeMidpoint_apply_second]
      change (1 - 0) / 2 + 0 = 1 / 2
      ring
    have hze : z ∉ e.1 := by
      rw [K.edge_eq_pair e]
      simpa [a, b] using And.intro hza hzb
    rw [show (fan zeroO).1 z = weight zeroO.1 z by rfl]
    have hmidCarrier : K.edgeMidpoint e ∈ K.faceCarrier e.1 := by
      rw [← K.range_edgePath e]
      exact ⟨⟨1 / 2, by constructor <;> norm_num⟩, rfl⟩
    have hmidZero := (K.mem_faceCarrier_iff e.1 (K.edgeMidpoint e)).mp
      hmidCarrier z hze
    by_cases hzc : z = c
    · subst z
      rw [weight_c]
      change 0 = (K.edgeMidpoint e).1 c
      exact hmidZero.symm
    · rw [weight_other _ hza hzb hzc]
      exact hmidZero.symm
  have hpageZero : page zeroO = h (K.edgeMidpoint e) := by
    change (h ∘ fan) zeroO = h (K.edgeMidpoint e)
    simp only [Function.comp_apply]
    rw [fan_zero]
  have hmidSource : h (K.edgeMidpoint e) ∈ chart.source := by
    change h (K.edgeMidpoint e) ∈ page.symm.source ∩
      page.symm ⁻¹' includeO.source
    constructor
    · have hzSource : zeroO ∈ page.source := by simp [page]
      have hzTarget : page zeroO ∈ page.target := page.map_source hzSource
      rw [hpageZero] at hzTarget
      simpa using hzTarget
    · change page.symm (h (K.edgeMidpoint e)) ∈ Set.univ
      trivial
  apply (isBoundaryPoint_iff_any_chart
    (modelWithCornersEuclideanHalfSpace 2) hmidSource).mpr
  rw [frontier_range_modelWithCornersEuclideanHalfSpace]
  change 0 = (chart (h (K.edgeMidpoint e))).1 0
  have hpage : page.symm (h (K.edgeMidpoint e)) = zeroO := by
    rw [← hpageZero]
    exact page.left_inv (by simp [page])
  change 0 = (page.symm (h (K.edgeMidpoint e))).1.1 0
  rw [hpage]
  rfl

/-- If an edge belongs to exactly two triangles, its barycentric midpoint is an ambient interior
point after any embedded realization in a surface with boundary. -/
theorem IntrinsicTwoComplex.not_isBoundaryPoint_homeo_edgeMidpoint_of_faceValence_two
    {S : Type*} [TopologicalSpace S]
    [ChartedSpace (EuclideanHalfSpace 2) S]
    (K : IntrinsicTwoComplex) (h : K.realization ≃ₜ S)
    (e : K.Edge)
    (htwo : (K.faces.filter fun t => e.1 ⊆ t).card = 2) :
    ¬(modelWithCornersEuclideanHalfSpace 2).IsBoundaryPoint
      (h (K.edgeMidpoint e)) := by
  classical
  obtain ⟨t, u, htu, hfilter⟩ := Finset.card_eq_two.mp htwo
  have htFilter : t ∈ K.faces.filter fun q => e.1 ⊆ q := by
    rw [hfilter]
    simp
  have huFilter : u ∈ K.faces.filter fun q => e.1 ⊆ q := by
    rw [hfilter]
    simp
  have htF : t ∈ K.faces := (Finset.mem_filter.mp htFilter).1
  have huF : u ∈ K.faces := (Finset.mem_filter.mp huFilter).1
  have het : e.1 ⊆ t := (Finset.mem_filter.mp htFilter).2
  have heu : e.1 ⊆ u := (Finset.mem_filter.mp huFilter).2
  let a := K.edgeFirst e
  let b := K.edgeSecond e
  have hab : a ≠ b := K.edgeFirst_ne_edgeSecond e
  have extra_vertex
      (s : Finset K.Vertex) (hsF : s ∈ K.faces) (hes : e.1 ⊆ s) :
      ∃ c : K.Vertex, c ∉ e.1 ∧ s = insert c e.1 := by
    have hdiffcard : (s \ e.1).card = 1 := by
      rw [Finset.card_sdiff_of_subset hes, K.faces_card s hsF,
        K.card_of_mem_edges e.2]
    obtain ⟨c, hc⟩ := Finset.card_eq_one.mp hdiffcard
    refine ⟨c, ?_, ?_⟩
    · have hcMem : c ∈ s \ e.1 := by rw [hc]; simp
      exact (Finset.mem_sdiff.mp hcMem).2
    · symm
      rw [← Finset.sdiff_union_of_subset hes, hc]
      simp
  obtain ⟨c, hce, htc⟩ := extra_vertex t htF het
  obtain ⟨d, hde, hud⟩ := extra_vertex u huF heu
  have hac : a ≠ c := by
    intro heq
    apply hce
    rw [← heq]
    exact K.edgeFirst_mem e
  have hbc : b ≠ c := by
    intro heq
    apply hce
    rw [← heq]
    exact K.edgeSecond_mem e
  have had : a ≠ d := by
    intro heq
    apply hde
    rw [← heq]
    exact K.edgeFirst_mem e
  have hbd : b ≠ d := by
    intro heq
    apply hde
    rw [← heq]
    exact K.edgeSecond_mem e
  have hcd : c ≠ d := by
    intro heq
    apply htu
    rw [htc, hud, heq]
  obtain ⟨mid, _W, _hW, hmid, _hsupport, hmidInterior⟩ :=
    exists_pair_pages_open_neighborhood K.faces h h.isEmbedding
      t u htF huF a b c d hab hac hbc had hbd hcd
      (by simpa [K.edge_eq_pair e] using htc)
      (by simpa [K.edge_eq_pair e] using hud)
  have hmidEq : mid = K.edgeMidpoint e := by
    apply Subtype.ext
    rw [hmid]
    funext z
    by_cases hza : z = a
    · subst z
      simp [a, b, hab, K.edgeMidpoint_apply_first]
    by_cases hzb : z = b
    · subst z
      simp [a, b, hab, K.edgeMidpoint_apply_second]
    have hze : z ∉ e.1 := by
      rw [K.edge_eq_pair e]
      simpa [a, b] using And.intro hza hzb
    have hcarrier : K.edgeMidpoint e ∈ K.faceCarrier e.1 := by
      rw [← K.range_edgePath e]
      exact ⟨⟨1 / 2, by constructor <;> norm_num⟩, rfl⟩
    have hz := (K.mem_faceCarrier_iff e.1 (K.edgeMidpoint e)).mp
      hcarrier z hze
    simp [hza, hzb, hz]
  rwa [hmidEq] at hmidInterior

end Moise

namespace GeometricTriangulation

open InvarianceOfDomain Set

variable {S : Type*} [TopologicalSpace S]
  [ChartedSpace (EuclideanHalfSpace 2) S]

/-- At the midpoint of an edge of a geometric surface triangulation, ambient manifold-boundary
status is equivalent to simplicial valence one. -/
theorem isBoundaryPoint_homeo_edgeMidpoint_iff_isBoundaryEdge
    (T : GeometricTriangulation S) (e : T.Edge) :
    (modelWithCornersEuclideanHalfSpace 2).IsBoundaryPoint
        (T.homeo (T.toIntrinsic.edgeMidpoint e)) ↔
      T.IsBoundaryEdge e := by
  constructor
  · intro hboundary
    have hle : (T.faces.filter fun t => e.1 ⊆ t).card ≤ 2 :=
      Moise.edge_valence_le_two_of_isEmbedding T.faces T.faces_card
        T.homeo T.homeo.isEmbedding e.1 (T.edge_card e)
    have hpos : 0 < (T.faces.filter fun t => e.1 ⊆ t).card := by
      apply Finset.card_pos.mpr
      rcases Finset.mem_biUnion.mp e.2 with ⟨t, htF, het⟩
      exact ⟨t, Finset.mem_filter.mpr
        ⟨htF, (Finset.mem_powersetCard.mp het).1⟩⟩
    by_contra hnot
    change ¬(T.faces.filter fun t => e.1 ⊆ t).card = 1 at hnot
    have htwo : (T.faces.filter fun t => e.1 ⊆ t).card = 2 := by
      omega
    exact (T.toIntrinsic
      |>.not_isBoundaryPoint_homeo_edgeMidpoint_of_faceValence_two
        T.homeo e htwo) hboundary
  · intro hone
    change (T.faces.filter fun t => e.1 ⊆ t).card = 1 at hone
    exact T.toIntrinsic.isBoundaryPoint_homeo_edgeMidpoint_of_faceValence_one
      T.homeo e hone

end GeometricTriangulation

end ClassificationOfSurfaces
end Topology
end LeanEval
