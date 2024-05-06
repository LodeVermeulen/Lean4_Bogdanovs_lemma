import MyProject.PerfectMatchings
import MyProject.HamiltonianCycle
import Mathlib.Combinatorics.SimpleGraph.Connectivity


/- The main results of this file are:
  • The union of 2 PMs is 2-regular
  TODO:
  • The union of 2 disjoint PMs in an exclusively disjoint PM graph is connected

 -/

universe u

namespace SimpleGraph

variable [Fintype V] {V : Type u} {G : SimpleGraph V} (v : V)

namespace Subgraph

variable (M₁ M₂ : Subgraph G) [LocallyFinite M₁] [LocallyFinite M₂]
  [LocallyFinite (M₁ ⊔ M₂)] [Fintype (M₁ ⊔ M₂).verts] [DecidableEq (M₁ ⊔ M₂).verts]


/- Ported from https://github.com/leanprover-community/mathlib/blob/kmill_hamiltonian/src/hamiltonian2.lean -/
lemma disj_union_perfect_matchings_2_regular (hd : Disjoint M₁.edgeSet M₂.edgeSet)
  (hM₁ : M₁.IsPerfectMatching) (hM₂ : M₂.IsPerfectMatching) :
  (M₁ ⊔ M₂).IsRegularOfDegree 2 := by
    rw [PM_is_1_regular] at hM₁ hM₂
    exact disj_union_regular M₁ M₂ hd hM₁ hM₂

/-- The union of two distinct perfect matchings in a graph with the property that all perfect
matchings are disjoint is connected. -/
/- Ported from: https://github.com/leanprover-community/mathlib/blob/kmill_hamiltonian/src/hamiltonian2.lean-/
theorem excl_disj_PM_graph_union_connected (hed : G.IsExclusivelyDisjointPMGraph)
  (hM₁ : M₁.IsPerfectMatching) (hM₂ : M₂.IsPerfectMatching) (hne : M₁ ≠ M₂) :
  (M₁ ⊔ M₂).spanningCoe.Connected := by
    rw [connected_iff]
    refine ⟨?_, ?_⟩
    /- Show that M₁ ⊔ M₂ is Preconnected -/
    · by_contra h
      simp only [Preconnected, not_forall] at h
      obtain ⟨v, v', h⟩ := h
      have hdisj := hed hM₁ hM₂ hne
      have unionleqG : M₁.spanningCoe ⊔ M₂.spanningCoe ≤ G := sup_le (sub_graph_leq_G M₁) (sub_graph_leq_G M₂)
      let c := (M₁ ⊔ M₂).spanningCoe.connectedComponentMk v
      let symmDiffM1_c := symmDiff M₁.spanningCoe c.induce
      have symmDiffleqG : symmDiffM1_c ≤ G := le_trans (flip_part_of_disjoint_le M₁ M₂ c) unionleqG
      have symmDiffSubgraph := G.toSubgraph symmDiffM1_c symmDiffleqG
      have symmDiffIsPM := flip_part_of_disjoint M₁ M₂ hdisj hM₁ hM₂ c symmDiffleqG
      have M1neqsymmDiff : M₁.spanningCoe ≠ symmDiff M₁.spanningCoe c.induce := ne_symm_diff hed M₁ M₂ hM₁ hM₂ hne v
      /- M₁ ≤ G and M₁ ∆ c ≤ G but also M₁ isPM and (M₁ ∆ c).isPM, so M₁ and (M₁ ∆ c) are disjoint (remember this is a proof by contradiction)-/
      have symmDiffDisjoint : Disjoint M₁.edgeSet symmDiffSubgraph.edgeSet := by
        sorry
        -- hed M₁ hM₁ symmDiffSubgraph symmDiffIsPM
      sorry
    /- Show that V is nonempty -/
    · by_contra h
      rw [not_nonempty_iff] at h
      apply hne
      ext v w
      exact h.elim v
      refine ⟨?_,?_⟩
      -- use disjoint_iff to show M₁.Adj v w → M₂.Adj v w and its reverse
      · sorry
      · sorry
