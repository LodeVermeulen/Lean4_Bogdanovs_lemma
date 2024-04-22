import Mathlib.Combinatorics.SimpleGraph.Matching
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Connectivity

universe u -- v

namespace SimpleGraph

variable [Fintype V] {V : Type u} {G : SimpleGraph V} (v : V)

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

-- To show that M.verts = Set.univ use IsSpanning (concretely: isSpanning_iff)
-- Use this to show that M₁.verts = M₂.verts

/- The vertex set of the union of two graphs is the same as the vertex sets of the composing
  graphs, assuming they have the same vertex set too. -/
-- lemma union_graph_verts_eq_composing_verts (M₁ M₂ : Subgraph G) (hM₁ : M₁.IsPerfectMatching)
--   (hM₂ : M₂.IsPerfectMatching) : (M₁ ⊔ M₂) := by
--     sorry

variable (M₁ M₂ : Subgraph G) (unionGraph := fromEdgeSet (M₁.edgeSet ∪ M₂.edgeSet))
  [LocallyFinite unionGraph] [Fintype (M₁.neighborSet v)] [Fintype (M₂.neighborSet v)]
  [Fintype ((M₁ ⊔ M₂).neighborSet v)]

/- The degree of the union of 2 finite (edge)disjoint graphs on the same vertex set
 are their degrees added -/
lemma degree_of_disjoint_union_eq_sum_of_degrees
  (hd : Disjoint M₁.edgeSet M₂.edgeSet) (hv₁ : M₁.verts = Set.univ)
  (hv₂ : M₂.verts = Set.univ)
  (hM₁ : M₁.degree v = n) (hM₂ : M₂.degree v = m) : -- M₁ = n-regular, M₂ = m-regular
    (M₁ ⊔ M₂).degree v = n + m := by
    specialize hM₁ v
      -- intro v'
        -- Show that v' has degree n in M₁ and degree m in M₂
        -- then use that Disjoint M₁.edgeSet M₂.edgeSet to add n and m
        -- then it is necessary to use that M₁.verts = M₂.verts

      -- intro v
      -- rw [← finset_card_neighborSet_eq_degree]
      sorry

lemma disjoint_PMs_form_2_regular_graph (hm : IsDisjointPerfectMatchingPair M₁ M₂):
  unionGraph.IsRegularOfDegree 2 := by
  -- show M₁.verts = M₂.verts = V
  have hv₁ : M₁.verts = Set.univ := isSpanning_iff.mp ?_
  have hv₂ : M₂.verts = Set.univ := isSpanning_iff.mp ?_
  apply degree_of_disjoint_union_eq_sum_of_degrees hm.2.2 M₁ M₂
  intro v
  obtain ⟨hM₁, hM₂, hd⟩ := hm
  obtain ⟨hM₁m, -⟩ := hM₁
  obtain ⟨hM₂m, -⟩ := hM₂
  rw [isMatching_iff_forall_degree] at hM₁m hM₂m

  use degree_of_disjoint_union_eq_sum_of_degrees
  sorry


/-
LEMMA IDEAS:
  ⬝ cycles in the union of perfect matchings are of even length ≥ 4
  ⬝ an exclusively disjoint pm graph can only contain 1 such cycle

THEOREM IDEAS:
  ⬝ It might be useful to show that c_max(2n)>=2. Prove by using cycles.
-/
