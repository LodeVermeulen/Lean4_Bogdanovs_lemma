import Mathlib.Combinatorics.SimpleGraph.Matching

/- The main result of this file is Bogdanov's lemma. -/

universe u

namespace SimpleGraph

variable [Fintype V] {V : Type u} {G : SimpleGraph V} (v : V)

namespace Subgraph

/-- Adjusted from https://github.com/leanprover-community/mathlib4/blob/6096b4a14c21be6102c467d7a49b93faa9993e64/Mathlib/Combinatorics/SimpleGraph/Finite.lean#L292-L293 -/
@[reducible]
def LocallyFinite (M : Subgraph G) :=
  ∀ v : V, Fintype (M.neighborSet v)

/-- Adjusted from https://github.com/leanprover-community/mathlib4/blob/6096b4a14c21be6102c467d7a49b93faa9993e64/Mathlib/Combinatorics/SimpleGraph/Finite.lean#L299-L300 -/
def IsRegularOfDegree (d : ℕ) (M : Subgraph G) [LocallyFinite M] : Prop :=
  ∀ v : V, M.degree v = d

/- Adjusted from https://github.com/leanprover-community/mathlib4/blob/e8ccef95c108e09c84c807751af9ab5611cc857b/Mathlib/Combinatorics/SimpleGraph/Finite.lean#L198-L199 -/
def neighborFinset (M : Subgraph G) [LocallyFinite M] : Finset V :=
  (M.neighborSet v).toFinset

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
lemma neighbor_finset_sup (M₁ M₂ : Subgraph G) [DecidableEq V]
  [LocallyFinite (M₁ ⊔ M₂)] [LocallyFinite M₁] [LocallyFinite M₂] :
  (M₁ ⊔ M₂).neighborSet v = M₁.neighborSet v ∪ M₂.neighborSet v := by
    ext w
    simp

lemma disjoint_neighbor_set_of_disjoint (M₁ M₂ : Subgraph G)
  (hd : Disjoint M₁.edgeSet M₂.edgeSet) :
    Disjoint (M₁.neighborSet v) (M₂.neighborSet v) := by
    rw [Set.disjoint_iff]
    rintro w ⟨hM₁, hM₂⟩
    exfalso
    rw [disjoint_iff] at hd
    simp_all only [Set.inf_eq_inter, Set.bot_eq_empty, mem_neighborSet]
    -- exact hd
    sorry

/- Ported from https://github.com/leanprover-community/mathlib/blob/kmill_hamiltonian/src/hamiltonian2.lean -/
lemma disj_union_regular (M₁ M₂ : Subgraph G) [LocallyFinite M₁] [LocallyFinite M₂]
  (hd : Disjoint M₁.edgeSet M₂.edgeSet) {m n : ℕ} [LocallyFinite (M₁ ⊔ M₂)]
  (hM₁ : M₁.IsRegularOfDegree n) (hM₂ : M₂.IsRegularOfDegree m) :
  (M₁ ⊔ M₂).IsRegularOfDegree (n + m) := by
    intro v
    specialize hM₁ v
    specialize hM₂ v
    classical
    rw [degree]
    simp_rw [neighbor_finset_sup]
    simp_all only [Fintype.card_ofFinset]
    rw [Finset.card_union_of_disjoint]
    simp [← hM₁, ← hM₂]
    exact rfl
    simp_all only [Set.disjoint_toFinset]
    exact disjoint_neighbor_set_of_disjoint v M₁ M₂ hd

/- Ported from https://github.com/leanprover-community/mathlib/blob/kmill_hamiltonian/src/hamiltonian2.lean -/
lemma disj_union_perfect_matchings (M₁ M₂ : Subgraph G) [LocallyFinite M₁] [LocallyFinite M₂]
  (hd : Disjoint M₁.edgeSet M₂.edgeSet) [LocallyFinite (M₁ ⊔ M₂)]
  (hM₁ : M₁.IsPerfectMatching) (hM₂ : M₂.IsPerfectMatching) :
  (M₁ ⊔ M₂).IsRegularOfDegree 2 := by
    rw [PM_is_1_regular] at hM₁ hM₂
    exact disj_union_regular M₁ M₂ hd hM₁ hM₂
