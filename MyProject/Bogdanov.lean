import MyProject.PerfectMatchings

/- The main result of this file is Bogdanov's lemma. -/

universe u

namespace SimpleGraph

variable [Fintype V] {V : Type u} {G : SimpleGraph V} (v : V)

namespace Subgraph

/- Ported from https://github.com/leanprover-community/mathlib/blob/kmill_hamiltonian/src/hamiltonian2.lean -/
lemma disj_union_perfect_matchings (M₁ M₂ : Subgraph G) [LocallyFinite M₁] [LocallyFinite M₂]
  (hd : Disjoint M₁.edgeSet M₂.edgeSet) [LocallyFinite (M₁ ⊔ M₂)]
  (hM₁ : M₁.IsPerfectMatching) (hM₂ : M₂.IsPerfectMatching) :
  (M₁ ⊔ M₂).IsRegularOfDegree 2 := by
    rw [PM_is_1_regular] at hM₁ hM₂
    exact disj_union_regular M₁ M₂ hd hM₁ hM₂
