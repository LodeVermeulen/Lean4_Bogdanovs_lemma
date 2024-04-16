import Mathlib.Combinatorics.SimpleGraph.Matching
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Connectivity

universe u -- v

namespace SimpleGraph

variable [Fintype V] {V : Type u} {G : SimpleGraph V}

namespace Subgraph

/- Two disjoint perfect matchings -/
def IsDisjointPerfectMatchingPair (M₁ M₂ : Subgraph G) : Prop :=
M₁.IsPerfectMatching ∧ M₂.IsPerfectMatching ∧ Disjoint M₁.edgeSet M₂.edgeSet

/- A graph with exclusively disjoint perfect matchings -/
def IsExclusivelyDisjointPMGraph (G : SimpleGraph V) : Prop :=
{M : Subgraph G | M.IsPerfectMatching}.PairwiseDisjoint id

def IsDisjointUnionOfCycles (G : SimpleGraph V) : Prop :=
∃ P : Set (Subgraph G), -- There exists a set `P` of subgraphs of `G`, such that:
  P.PairwiseDisjoint id -- The subgraphs are pairwise disjoint,
  ∧ sSup P = ⊤ -- The union of all of the subgraphs is the whole graph, and
  ∧ ∀ H ∈ P, ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧ H = c.toSubgraph /- every subgraph `H ∈ P`
    consists of the vertices and edges of some cycle of `G`. -/

variable (M₁ M₂ : Subgraph G) (unionGraph := fromEdgeSet (M₁.edgeSet ∪ M₂.edgeSet))
  [LocallyFinite unionGraph] [∀ v, Fintype (M₁.neighborSet v)] [∀ v, Fintype (M₂.neighborSet v)]

/- The degree of the union of 2 disjoint graphs are their degrees added -/
lemma degree_of_disjoint_union_eq_sum_of_degrees (hd : Disjoint M₁.edgeSet M₂.edgeSet)
  (hM₁ : ∀ v : V, v ∈ M₁.verts → M₁.degree v = n) -- M₁ = n-regular
  (hM₂ : ∀ v : V, v ∈ M₂.verts → M₂.degree v = m) : -- M₂ = m-regular
   unionGraph.IsRegularOfDegree (n + m) := by
    intro v
    simp_all only
    sorry

lemma disjoint_PMs_form_2_regular_graph (hm : IsDisjointPerfectMatchingPair M₁ M₂):
  unionGraph.IsRegularOfDegree 2 := by
  -- show M₁.verts = M₂.verts = V
  intro v
  obtain ⟨hM₁, hM₂, hd⟩ := hm
  obtain ⟨hM₁m, -⟩ := hM₁
  obtain ⟨hM₂m, -⟩ := hM₂
  rw [isMatching_iff_forall_degree] at hM₁m hM₂m

  -- use degree_of_disjoint_union_eq_sum_of_degrees
  sorry


/-
LEMMA IDEAS:
  ⬝ cycles in the union of perfect matchings are of even length ≥ 4
  ⬝ an exclusively disjoint pm graph can only contain 1 such cycle

THEOREM IDEAS:
  ⬝ It might be useful to show that c_max(2n)>=2. Prove by using cycles.
-/
