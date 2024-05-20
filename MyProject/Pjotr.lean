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

/- We have 2*|E| = d*|V| for d-regular graphs by the handshaking lemma.-/
lemma VertexEdgeCountRegular {d : ℕ} {G : SimpleGraph V} [Fintype V] [DecidableRel G.Adj] (h : G.IsRegularOfDegree d) :
  2 * (G.edgeFinset.card) = d * (Fintype.card V) := by
    convert (sum_degrees_eq_twice_card_edges G).symm
    have hCons : (Finset.univ.sum fun v ↦ G.degree v) = (Finset.univ.sum fun (_: V) ↦ d) := by
      congr
      ext v
      exact IsRegularOfDegree.degree_eq h v
    convert hCons.symm
    rw [Finset.sum_const, mul_comm]
    congr

/- The following is true without connectedness assumption by applying the lemma to a connected component. -/
lemma RegularGraphContainsCycle {d: ℕ} (G : SimpleGraph V) [Fintype V] [DecidableRel G.Adj]
    (hDeg : 2 ≤ d) (hReg: G.IsRegularOfDegree d) (hCon : G.Connected) : ¬ G.IsAcyclic := by
  by_contra hAcyc
  have hCount := VertexEdgeCountRegular hReg
  rw [←(IsTree.card_edgeFinset ⟨hCon,hAcyc⟩), mul_add, mul_one] at hCount
  have _ : 2 * G.edgeFinset.card  < d * G.edgeFinset.card + d := by
    calc
      2 * G.edgeFinset.card ≤ d * G.edgeFinset.card     := by gcongr
      _                     < d * G.edgeFinset.card + d := by linarith
  linarith

lemma RegularConnectedSubgraphRegularGraph {d : ℕ} (G : SimpleGraph V) [G.LocallyFinite]
    (hcon: G.Connected) (hReg: G.IsRegularOfDegree d) (H : G.Subgraph) [H.coe.LocallyFinite] (hReg2 : H.coe.IsRegularOfDegree d) :
  H = ⊤ := by
  ext v u
  .
      sorry
  . sorry

  sorry


/- Attempt to define a cycle graph. -/
def IsCycleGraph (G : SimpleGraph V) : Prop :=
    ∃ (v : V), ∃ (c : Walk G v v), c.IsCycle ∧ c.toSubgraph = ⊤

lemma TwoRegularConnectedIsCycle (G: SimpleGraph V) [Fintype V] [DecidableRel G.Adj]
    (hReg : G.IsRegularOfDegree 2) (hCon : G.Connected) : IsCycleGraph G := by
  have hCycEx := RegularGraphContainsCycle G (by linarith) hReg hCon
  unfold IsAcyclic at hCycEx
  push_neg at hCycEx
  rcases hCycEx with ⟨v,c,hCyc⟩
  refine ⟨v,c,hCyc, ?_⟩
  sorry




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
