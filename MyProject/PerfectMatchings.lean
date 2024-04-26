import MyProject.Base

/- Some lemmas about perfect matchings -/

universe u

namespace SimpleGraph

variable [Fintype V] {V : Type u} {G : SimpleGraph V} (v : V)

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
