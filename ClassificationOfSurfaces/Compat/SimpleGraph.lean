/-
Compatibility backports for simple paths added after mathlib v4.29.0.
The statements and proofs are adapted from Mathlib.Combinatorics.SimpleGraph.Paths.
-/
import Mathlib.Combinatorics.SimpleGraph.Paths

namespace SimpleGraph
namespace Walk

variable {V : Type*} {G : SimpleGraph V} {u v : V}

theorem IsPath.length_eq_one_of_mem_edges {p : G.Walk u v}
    (hp : p.IsPath) (h : s(u, v) ∈ p.edges) : p.length = 1 := by
  suffices p.length - 1 = 0 by grind [length_edges]
  rw [← hp.getVert_eq_start_iff <| p.length.sub_le 1]
  exact (hp.eq_penultimate_of_mem_edges <| Sym2.eq_swap ▸ h).symm

theorem IsPath.disjoint_edges_of_disjoint_support
    {p : G.Walk u v} {q : G.Walk v u} (hp : p.IsPath)
    (hd : p.support.tail.Disjoint q.support.tail) (hl : p.length ≠ 1) :
    p.edges.Disjoint q.edges := by
  simp only [List.disjoint_left] at hd ⊢
  contrapose! hd
  obtain ⟨⟨a, b⟩, hep, heq⟩ := hd
  have := p.mem_support_iff.mp <| p.fst_mem_support_of_mem_edges hep
  have := p.mem_support_iff.mp <| p.snd_mem_support_of_mem_edges hep
  have := q.mem_support_iff.mp <| q.fst_mem_support_of_mem_edges heq
  have := q.mem_support_iff.mp <| q.snd_mem_support_of_mem_edges heq
  grind [p.adj_of_mem_edges hep |>.ne, length_eq_one_of_mem_edges]

lemma IsPath.isCycle_append {p : G.Walk u v} {q : G.Walk v u}
    (hp : p.IsPath) (hq : q.IsPath)
    (h : p.support.tail.Disjoint q.support.tail)
    (hn : 1 < p.length ∨ 1 < q.length) :
    (p.append q).IsCycle := by
  rw [isCycle_def, isTrail_def, edges_append, List.nodup_append']
  refine ⟨⟨hp.isTrail.edges_nodup, hq.isTrail.edges_nodup, ?_⟩, ?_, ?_⟩
  · rcases hn with hpLen | hqLen
    · exact hp.disjoint_edges_of_disjoint_support h (Nat.ne_of_gt hpLen)
    · exact (hq.disjoint_edges_of_disjoint_support h.symm (Nat.ne_of_gt hqLen)).symm
  · intro happend
    have hlength := congrArg Walk.length happend
    simp only [length_append, length_nil] at hlength
    omega
  · rw [tail_support_append, List.nodup_append']
    exact ⟨hp.support_nodup.tail, hq.support_nodup.tail, h⟩

end Walk
end SimpleGraph
