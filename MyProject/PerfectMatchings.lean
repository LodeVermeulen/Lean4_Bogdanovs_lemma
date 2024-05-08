import MyProject.Base

/- Some lemmas about perfect matchings -/

universe u

namespace SimpleGraph

variable [Fintype V] {V : Type u} {G : SimpleGraph V} (v : V)

/- A graph with exclusively disjoint perfect matchings -/
def IsExclusivelyDisjointPMGraph (G : SimpleGraph V) : Prop :=
  {M : Subgraph G | M.IsPerfectMatching}.PairwiseDisjoint Subgraph.edgeSet

def perfect_matchings_disjoint (G : SimpleGraph V) : Prop :=
∀ {M₁ M₂ : Subgraph G}, M₁.spanningCoe ≤ G → M₂.spanningCoe ≤ G →
  M₁.IsPerfectMatching → M₂.IsPerfectMatching → M₁ ≠ M₂ → Disjoint M₁.edgeSet M₂.edgeSet

namespace Subgraph

/- The vertex set of a spanning subgraph is
 the same as the graph it is a subgraph of -/
lemma PM_verts_eq_vertex_set (M : Subgraph G) (hm : M.IsSpanning) :
  M.verts = Set.univ := by -- could show = G.support instead
  rw [←isSpanning_iff]
  exact hm

/- Two spanning subgraphs of the same graph have the same vertex sets -/
lemma PMs_same_verts (M₁ M₂ : Subgraph G) (hM₁ : M₁.IsSpanning)
  (hM₂ : M₂.IsSpanning) : M₁.verts = M₂.verts := by
    have hM₁_univ : M₁.verts = Set.univ := by simp_all only [isSpanning_iff]
    have hM₂_univ : M₂.verts = Set.univ := by simp_all only [isSpanning_iff]
    simp_all

/- Ported from https://github.com/leanprover-community/mathlib/blob/kmill_hamiltonian/src/hamiltonian2.lean -/
lemma PM_is_1_regular (M : Subgraph G) [LocallyFinite M] :
    M.IsPerfectMatching ↔ M.IsRegularOfDegree 1 := by
      rw [isPerfectMatching_iff_forall_degree, IsRegularOfDegree]

/- Ported from https://github.com/leanprover-community/mathlib/blob/kmill_hamiltonian/src/hamiltonian2.lean -/
-- The predicate that the graph of the symmetric difference of M₁ and a connected component is a perfect matching
lemma flip_part_of_disjoint (M₁ M₂ : Subgraph G) (hd : Disjoint M₁.edgeSet M₂.edgeSet)
  (hM₁ : M₁.IsPerfectMatching) (hM₂ : M₂.IsPerfectMatching)
  (c : (M₁ ⊔ M₂).spanningCoe.ConnectedComponent)
  (hsd : (symmDiff M₁.spanningCoe c.induce) ≤ G) :
  (SimpleGraph.toSubgraph (symmDiff M₁.spanningCoe c.induce) hsd).IsPerfectMatching := by sorry

/- Ported from https://github.com/leanprover-community/mathlib/blob/kmill_hamiltonian/src/hamiltonian2.lean -/
lemma flip_part_of_disjoint_le (M₁ M₂ : Subgraph G)
  (c : (M₁ ⊔ M₂).spanningCoe.ConnectedComponent) :
  symmDiff M₁.spanningCoe c.induce ≤ M₁.spanningCoe ⊔ M₂.spanningCoe := by
    sorry

/- Ported from https://github.com/leanprover-community/mathlib/blob/kmill_hamiltonian/src/hamiltonian2.lean -/
lemma ne_symm_diff (hed : G.IsExclusivelyDisjointPMGraph) (M₁ M₂ : Subgraph G)
  (hM₁ : M₁.IsPerfectMatching) (hM₂ : M₂.IsPerfectMatching) (hne : M₁ ≠ M₂) (v : V) :
  M₁.spanningCoe ≠ symmDiff M₁.spanningCoe ((M₁ ⊔ M₂).spanningCoe.connectedComponentMk v).induce := by
    sorry
