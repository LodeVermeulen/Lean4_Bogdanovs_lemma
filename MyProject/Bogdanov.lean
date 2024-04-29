import MyProject.PerfectMatchings
import MyProject.HamiltonianCycle

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

/- The union of two disjoint PMs in an exclusively disjoint PM graph form a Hamiltonian cycle -/
lemma excl_disj_PM_graph_H_cycle (hed : G.IsExclusivelyDisjointPMGraph)
  (hM₁ : M₁.IsPerfectMatching) (hM₂ : M₂.IsPerfectMatching) :
    ((M₁ ⊔ M₂).coe).IsHamiltonian := by
    intro v_neq_1
    simp_all only [verts_sup, ne_eq, Subtype.exists, Set.mem_union]
    have vte : M₁.verts = M₂.verts := by exact PMs_same_verts M₁ M₂ hM₁.2 hM₂.2
    simp_rw [vte]

    sorry

/-- The union of two distinct perfect matchings in a graph with the property that all perfect
matchings are disjoint is connected. -/
/- Ported from: https://github.com/leanprover-community/mathlib/blob/kmill_hamiltonian/src/hamiltonian2.lean-/
theorem excl_disj_PM_graph_union_connected (hed : G.IsExclusivelyDisjointPMGraph)
  (hM₁ : M₁.IsPerfectMatching) (hM₂ : M₂.IsPerfectMatching) (hne : M₁ ≠ M₂) :
  (M₁ ⊔ M₂).coe.Connected := by sorry
