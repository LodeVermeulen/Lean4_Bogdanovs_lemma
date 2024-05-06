import Mathlib.Combinatorics.SimpleGraph.Matching
import Mathlib.Combinatorics.SimpleGraph.Connectivity
import Mathlib.Order.SymmDiff

/- Some lemmas for disjoint graphs -/

universe u

namespace SimpleGraph

variable [Fintype V] {V : Type u} {G : SimpleGraph V} {M : Subgraph G} (v : V)

/- Ported from https://github.com/leanprover-community/mathlib/blob/kmill_hamiltonian/src/hamiltonian2.lean -/
-- Keeping only the part of the graph that includes the connected component
def ConnectedComponent.induce (c : G.ConnectedComponent) : SimpleGraph V :=
  (G.induce c.supp).spanningCoe

namespace Subgraph

lemma sub_graph_leq_G (M : Subgraph G) : M.spanningCoe ≤ G := by
  intros u v
  simp
  exact Adj.adj_sub

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

/- Ported from https://github.com/leanprover-community/mathlib/blob/kmill_hamiltonian/src/hamiltonian2.lean -/
theorem disjoint_iff (M M' : Subgraph G) :
  Disjoint M.edgeSet M'.edgeSet ↔ ∀ v w, M.Adj v w → M'.Adj v w → false := by
  refine ⟨?_,?_⟩
  · intros hd v w h h'
    simp_all only [←mem_edgeSet]
    exact hd inf_le_left inf_le_right ⟨h, h'⟩
  · sorry

/- Ported from https://github.com/leanprover-community/mathlib/blob/kmill_hamiltonian/src/hamiltonian2.lean -/
lemma neighbor_finset_sup (M₁ M₂ : Subgraph G) [DecidableEq V]
  [LocallyFinite (M₁ ⊔ M₂)] [LocallyFinite M₁] [LocallyFinite M₂] :
  (M₁ ⊔ M₂).neighborSet v = M₁.neighborSet v ∪ M₂.neighborSet v := by
    ext w
    simp

/- Ported from https://github.com/leanprover-community/mathlib/blob/kmill_hamiltonian/src/hamiltonian2.lean -/
lemma disjoint_neighbor_set_of_disjoint (M₁ M₂ : Subgraph G)
  (hd : Disjoint M₁.edgeSet M₂.edgeSet) :
    Disjoint (M₁.neighborSet v) (M₂.neighborSet v) := by
    rw [Set.disjoint_iff]
    rintro w ⟨hM₁, hM₂⟩
    exfalso
    rw [disjoint_iff] at hd
    simp_all only [imp_false, mem_neighborSet]

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
