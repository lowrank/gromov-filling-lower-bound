/-
Compatibility backport for the connected-cover intersection-chain lemma added
after mathlib v4.29.0.  The statement and proof are adapted from
Mathlib.Topology.Connected.Basic at mathlib commit
81a5d257c8e410db227a6665ed08f64fea08e997.
-/
import Mathlib.Topology.Connected.Basic

open Set

variable {α : Type*} [TopologicalSpace α]

lemma IsPreconnected.transGen_of_iUnion {ι : Type*} {s : ι → Set α}
    (hs : IsPreconnected (⋃ n, s n)) (hs' : ∀ i, IsOpen (s i))
    (i j : ι) (hi : (s i).Nonempty) (hj : (s j).Nonempty) :
    Relation.TransGen (fun a b ↦ (s a ∩ s b).Nonempty) i j := by
  by_contra hij
  let S : Set ι := {k | Relation.TransGen
    (fun a b ↦ (s a ∩ s b).Nonempty) i k}
  let U : Set α := ⋃ k ∈ S, s k
  let V : Set α := ⋃ k ∈ Sᶜ, s k
  have hsplit : (⋃ n, s n) = U ∪ V := iSup_split s (· ∈ S)
  obtain ⟨a, ha⟩ := hi
  obtain ⟨b, hb⟩ := hj
  let hi_S : i ∈ S := Relation.TransGen.single ⟨a, ha, ha⟩
  have hUne : ((⋃ n, s n) ∩ U).Nonempty :=
    ⟨a, mem_iUnion_of_mem i ha, mem_iUnion₂_of_mem hi_S ha⟩
  have hVne : ((⋃ n, s n) ∩ V).Nonempty :=
    ⟨b, mem_iUnion_of_mem j hb, mem_iUnion₂_of_mem hij hb⟩
  obtain ⟨x, -, hxU, hxV⟩ := hs U V
    (isOpen_biUnion fun i _ ↦ hs' i)
    (isOpen_biUnion fun i _ ↦ hs' i) hsplit.le hUne hVne
  simp only [mem_iUnion, exists_prop, mem_compl_iff, U, V] at hxU hxV
  obtain ⟨k, hk, hxk⟩ := hxU
  obtain ⟨l, hl, hxl⟩ := hxV
  exact hl (hk.tail ⟨x, hxk, hxl⟩)
