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

lemma two_regular_is_disjoint_union_of_cycles (G : SimpleGraph V) [LocallyFinite G]
  (hr : G.IsRegularOfDegree 2) : IsDisjointUnionOfCycles G := by
    rw [IsDisjointUnionOfCycles]
    refine ⟨?_,?_,?_,?_⟩
    · sorry
    · sorry
    · sorry
    · sorry

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



/-
LEMMA IDEAS:
  ⬝ cycles in the union of perfect matchings are of even length ≥ 4
  ⬝ an exclusively disjoint pm graph can only contain 1 such cycle

THEOREM IDEAS:
  ⬝ It might be useful to show that c_max(2n)>=2. Prove by using cycles.
-/
