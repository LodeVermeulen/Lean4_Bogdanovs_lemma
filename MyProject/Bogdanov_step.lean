import Mathlib.Combinatorics.SimpleGraph.Matching
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Connectivity
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph
import Mathlib.Combinatorics.SimpleGraph.Subgraph
import Mathlib.Data.Set.Basic
import Mathlib.Data.Fintype.Basic

universe u -- v

namespace SimpleGraph


open Classical

/-This all seems silly but can maybe be fixed later?-/
noncomputable instance [Fintype V] (A : Set V) : Fintype A := Fintype.ofFinite ↑A

noncomputable instance [Fintype V] (G: SimpleGraph V) : LocallyFinite G := by
  intro V
  exact Fintype.ofFinite _

noncomputable instance [Fintype V] (G: SimpleGraph V) (H : G.Subgraph) : LocallyFinite H.coe := by
  intro v
  apply Subgraph.coeFiniteAt

noncomputable instance (G : SimpleGraph V) : DecidableRel G.Adj := by
  exact Classical.decRel G.Adj

noncomputable instance (G : SimpleGraph V) (H : G.Subgraph) [DecidableEq V] : DecidableEq H.verts := by
  exact Subtype.instDecidableEq


namespace Subgraph

/- Some tests: -/

/- We have 2*|E| = d*|V| for d-regular graphs by the handshaking lemma.-/
lemma VertexEdgeCountRegular {d : ℕ} {G : SimpleGraph V} [Fintype V] [DecidableRel G.Adj] (h : G.IsRegularOfDegree d) :
  2 * (G.edgeFinset.card) = d * (Fintype.card V) := by
    convert (sum_degrees_eq_twice_card_edges G).symm
    rw [mul_comm]
    convert (Finset.sum_const d).symm
    convert (h _)

/-  Any connected d-regular graph with 2 ≤ d contains a cycle.
    This statement is also true without the connectedness assumption, which we might prove later.
    Ofcourse mathematically this is trivial, because any tree/forrest contains a
    degree 1 vertex. I haven't been able to find this statement in the Lean library.
-/
lemma RegularGraphContainsCycle {d: ℕ} (G : SimpleGraph V) [Fintype V] [DecidableRel G.Adj]
    (hDeg : 2 ≤ d) (hReg: G.IsRegularOfDegree d) (hCon : G.Connected) : ¬ G.IsAcyclic := by
  by_contra hAcyc
  have hCount := VertexEdgeCountRegular hReg
  rw [←(IsTree.card_edgeFinset ⟨hCon,hAcyc⟩), mul_add, mul_one] at hCount
  apply (lt_self_iff_false (2 * G.edgeFinset.card)).1
  nth_rw 2 [hCount]
  rw [←add_zero (2 * G.edgeFinset.card)]
  exact Nat.add_lt_add_of_le_of_lt (by gcongr) (by omega)


/- Definition of a regular subgraph. -/
def SubgraphIsRegular [Fintype V] (G : SimpleGraph V) (H : Subgraph G) (d : ℕ) : Prop :=
    ∀ v, v ∈ H.verts → degree H v = d

/-
  The following statements prove that the only (nontrivial) d-regular subgraph of a connected d-regular graph is the graph itself.
-/

/- This is essentially Walk.exists_boundary_dart. -/
def CrossingEdgeConnected (G : SimpleGraph V) (hCon: G.Connected) (S : Set V) (hNonEmpty : S ≠ ∅) (hNonSpan : S ≠ Set.univ)
: ∃ u v, u ∈ S ∧ ¬(v ∈ S) ∧ G.Adj u v := by
  rcases Set.nonempty_def.mp (Set.nonempty_iff_ne_empty.mpr hNonEmpty) with ⟨a, ha⟩
  rcases (Set.ne_univ_iff_exists_not_mem S).mp hNonSpan with ⟨b, hb⟩
  rcases Walk.exists_boundary_dart (Classical.choice (hCon a b)) S ha hb with ⟨d,_,d1,d2⟩
  refine ⟨d.toProd.1,d.toProd.2,d1,d2,d.adj⟩

lemma DegAdjImpEdge [Fintype V] (G: SimpleGraph V) (H : Subgraph G) {v u : V}
    (hDeg : G.degree v = degree H v) (hAdj: G.Adj v u) : s(v,u) ∈ H.edgeSet := by
  rw [SimpleGraph.Subgraph.mem_edgeSet]
  change u ∈ neighborSet H v
  convert (?_ : u ∈ SimpleGraph.neighborSet G v) using 1
  . refine Set.eq_of_subset_of_card_le (neighborSet_subset _ _) ?_
    rw [card_neighborSet_eq_degree G v]
    convert Nat.le_of_eq hDeg
  . exact hAdj

lemma DegAdjImpVtx [Fintype V] (G: SimpleGraph V) (H : Subgraph G) {v u : V}
    (hDeg : G.degree v = degree H v) (hAdj: G.Adj v u) : u ∈ H.verts :=
  Adj.snd_mem (DegAdjImpEdge G H hDeg hAdj)

/- Main statement. -/
lemma RegularConnectedSubgraphRegularGraph [Fintype V] [DecidableEq V] {d : ℕ} (G : SimpleGraph V)
    (hCon: G.Connected) (hReg: G.IsRegularOfDegree d) (H : G.Subgraph) (hNonEmpty : H.verts ≠ ∅) (hReg2 : SubgraphIsRegular G H d) :
  H = ⊤ := by
  have HSpan : H.verts = Set.univ := by
    by_contra hNonSpan
    rcases CrossingEdgeConnected G hCon H.verts hNonEmpty hNonSpan with ⟨u,v,uH,vnH,uvAdj⟩
    refine vnH (DegAdjImpVtx G H ?_ uvAdj)
    rw [hReg, hReg2 u uH]
  ext a b
  . rw [HSpan]
    exact Set.mem_def
  . refine ⟨by intro this; exact (Adj.adj_sub this),?_⟩
    intro hAdj
    convert DegAdjImpEdge G H ?_ hAdj
    rw [hReg, hReg2 a (by rw [HSpan]; exact trivial)]


/- We need a bunch of lemmas about the degrees of vertices in a path/cycle viewed as subgraphs. -/
lemma SubgraphDegreeNbrSet [Fintype V] {v : V} (G : SimpleGraph V) (H: Subgraph G) : H.degree v = Fintype.card (neighborSet H v) := rfl

/- The degree of the vertex at the start of a (nontrivial) path is 1. -/
lemma DegreePathFirst [Fintype V] (G: SimpleGraph V) {v u : V} (p : G.Walk v u) (hp : p.IsPath) :
    0 < p.length → (degree p.toSubgraph v = 1) := by
  intro plen
  match p with
  | .nil => simp at plen
  | .cons hab pbc =>
    simp
    rw [SubgraphDegreeNbrSet, neighborSet_sup]
    have aNotRest : (pbc.toSubgraph.neighborSet v) = ∅ := by
      have hNoDup := hp.support_nodup
      simp at hNoDup
      by_contra hanbr
      rcases Set.nonempty_def.mp (Set.nonempty_iff_ne_empty.mpr hanbr) with ⟨_, hd⟩
      convert hNoDup.1 ((Walk.mem_verts_toSubgraph _).1 (edge_vert _ hd))
    rw [aNotRest]
    simp

/- The degree of the vertex at the end of a (nontrivial) path is 1 -/
lemma DegreePathLast [Fintype V] (G: SimpleGraph V) {v u : V} (p : G.Walk v u) (hp : p.IsPath) :
    0 < p.length → (degree p.toSubgraph u = 1) := by
  convert DegreePathFirst G p.reverse ((Walk.isPath_reverse_iff p).mpr hp) using 1
  . simp
  . rw [Walk.toSubgraph_reverse p]

/- Inclusion Exclusion type lemma for Fintype.card. I could not find this in the library, but
   I would not be surprised if it is in there somewhere. -/
lemma FintypeInclExcl [Fintype V] [DecidableEq V] (S T : Set V)
    : Fintype.card ↑(S ∪ T) = Fintype.card ↑S + Fintype.card ↑T - Fintype.card ↑(S ∩ T)  := by
  simp_rw [←Set.toFinset_card, Set.toFinset_union, Set.toFinset_inter, Finset.card_union]


/- If p is a cycle rooted at v then the degree of v within p as viewed as a subgraph is 2. -/
lemma DegreeCycleRoot [Fintype V] [DecidableEq V] {v : V} {G: SimpleGraph V} (p : G.Walk v v) (hCyc : p.IsCycle) :
    degree p.toSubgraph v = 2  := by
  have plen := Walk.IsCycle.three_le_length hCyc
  match p with
  | .nil => simp at plen
  | .cons' _ b _ hvb pbv =>
    simp
    rw [SubgraphDegreeNbrSet, neighborSet_sup, FintypeInclExcl]
    simp
    rw [←SubgraphDegreeNbrSet, DegreePathLast G pbv ((SimpleGraph.Walk.cons_isCycle_iff pbv hvb).1 hCyc).1 (?_)]
    . simp
      have this : Fintype.card ↑({b} ∩ pbv.toSubgraph.neighborSet v) = 0 := by
        by_contra hNonEmpty
        rcases nonempty_subtype.mp (Fintype.card_pos_iff.1 (Nat.zero_lt_of_ne_zero hNonEmpty)) with ⟨x,hx⟩
        simp at hx
        have vbAdj := hx.2
        rw [hx.1] at vbAdj
        change s(v,b) ∈ pbv.toSubgraph.edgeSet at vbAdj
        convert ((SimpleGraph.Walk.cons_isCycle_iff pbv hvb).1 hCyc).2 ((Walk.mem_edges_toSubgraph pbv).1 vbAdj)
      rw [this]
    . rw [SimpleGraph.Walk.length_cons] at plen
      linarith

/- A cycle is a 2-regular subgraph. -/
lemma CycleRegularSubgraph [Fintype V] [DecidableEq V] {v : V} (G: SimpleGraph V) (c : Walk G v v) (hCyc : c.IsCycle) :
  SubgraphIsRegular G c.toSubgraph 2 := by
  intro _ hu
  have hu := (Walk.mem_verts_toSubgraph c).mp hu
  convert DegreeCycleRoot (SimpleGraph.Walk.rotate c hu) ?_ using 1
  . rw [Walk.toSubgraph_rotate c hu]
  . exact Walk.IsCycle.rotate hCyc hu

/- Attempt to define a cycle graph. -/
def IsCycleGraph (G : SimpleGraph V) : Prop :=
    ∃ (v : V), ∃ (c : Walk G v v), c.IsCycle ∧ c.toSubgraph = ⊤

/- A 2-regular connected graph is a cycle as defined above. -/
lemma TwoRegularConnectedIsCycle (G: SimpleGraph V) [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (hReg : G.IsRegularOfDegree 2) (hCon : G.Connected) : IsCycleGraph G := by
  have hCycEx := RegularGraphContainsCycle G (by linarith) hReg hCon
  unfold IsAcyclic at hCycEx
  push_neg at hCycEx
  rcases hCycEx with ⟨v,c,hCyc⟩
  refine ⟨v,c,hCyc, ?_⟩
  refine RegularConnectedSubgraphRegularGraph G hCon hReg c.toSubgraph ?_ (CycleRegularSubgraph G c hCyc)
  exact Set.nonempty_iff_ne_empty.mp ⟨v,Walk.start_mem_verts_toSubgraph c⟩


/- To make it an if and only if statement we need a few simple lemmas. -/
@[simp]
lemma DegreeTopSubgraph [Fintype V] {G: SimpleGraph V} {v : V} : (⊤ : Subgraph G).degree v = G.degree v  := by
  unfold SimpleGraph.degree; unfold degree
  simp

@[simp]
lemma RegularTop {d : ℕ} [Fintype V] {G: SimpleGraph V} :
    SubgraphIsRegular G ⊤ d ↔ G.IsRegularOfDegree d := by
  refine ⟨?_,?_⟩
  . intro hReg _
    rw [←DegreeTopSubgraph, hReg _ (by trivial)]
  . intro hReg _ _
    rw [DegreeTopSubgraph, hReg]

/- The goal of this section: A connected graph is 2-regular if and only if it is a cycle. -/
theorem ConnectedImpCycleIffTwoReg [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hCon : G.Connected) : G.IsRegularOfDegree 2 ↔ IsCycleGraph G := by
  refine ⟨by intro hReg; exact TwoRegularConnectedIsCycle G hReg hCon, ?_⟩
  intro hCyc
  rcases hCyc with ⟨_,_,hCyc,hcTop⟩
  rw [←RegularTop,←hcTop]
  exact CycleRegularSubgraph _ _ hCyc


/- We want to move some statements from Simplegraphs to coerced Subgraphs -/
lemma RegularityCoerced [Fintype V] [DecidableEq V] (G : SimpleGraph V) (H : Subgraph G) (d : ℕ) :
    H.coe.IsRegularOfDegree d ↔ SubgraphIsRegular G H d := by
  refine ⟨?_,?_⟩
  . intro HcoeReg v hv
    convert HcoeReg ⟨v, hv⟩
    rw [Subgraph.coe_degree]
  . intro Hreg v
    have this := Hreg v
    simp at this
    convert this
    rw [Subgraph.coe_degree]

/-The proof of the following (trivial) statement is not very clean.-/
@[simp]
lemma InducedTopSub (G : SimpleGraph V) (H : Subgraph G) : Subgraph.map H.hom (⊤ : Subgraph H.coe) = H := by
  refine (Subgraph.ext_iff (Subgraph.map H.hom ⊤) H).mpr ⟨by simp,?_⟩
  ext a b
  refine ⟨?_,?_⟩
  . intro h
    simp at h
    rw [Relation.map_apply] at h
    rcases h with ⟨a,b,hAdj,eq1,eq2⟩
    rw [←eq1, ←eq2]
    exact hAdj
  . intro h
    simp
    refine Relation.map_apply.mpr ?_
    use ⟨a,?_⟩, ⟨b,?_⟩
    . simp [h]
    . exact H.edge_vert h
    . exact H.edge_vert (id (adj_symm H h))

/-
  A cycle coerced to a Simplegraph is a cyclegraph.
  We prove this in a very silly way: namely by using ConnectedImpCycleIffTwoReg.
  A more traditional proof would use the definition of a cycle, but this seems trickier.
-/
lemma CycleCoeIsCycleGraph {v : V} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (c : Walk G v v) (hCyc : c.IsCycle) :
    IsCycleGraph c.toSubgraph.coe := by
  rw [←ConnectedImpCycleIffTwoReg]
  . convert (RegularityCoerced G c.toSubgraph 2).2 (CycleRegularSubgraph G c hCyc)
  . exact Subgraph.connected_iff'.1 (SimpleGraph.Walk.toSubgraph_connected c)

/- We want to also apply this statement to subgraphs. We define when a subgraph is a cycle. -/
def IsCycleSubgraph (G : SimpleGraph V) (H : Subgraph G) : Prop :=
    ∃ (v : V), ∃ (c : Walk G v v), c.IsCycle ∧ c.toSubgraph = H

/- A cycle should be a CycleSubgraph -/
lemma CycleIsCycleSubgraph {v : V} (G : SimpleGraph V) (c : Walk G v v) (hCyc : c.IsCycle) :
    IsCycleSubgraph G c.toSubgraph := by use v, c, hCyc

/- The definition should coincide with the original definition when H is coerced to a simple graph. -/
lemma CycleSubgraphCoe [Fintype V] [DecidableEq V] (G : SimpleGraph V) (H : Subgraph G) :
    IsCycleGraph H.coe ↔ IsCycleSubgraph G H  := by
  refine ⟨?_,?_⟩
  . intro HCyc
    rcases HCyc with ⟨v, c, hc, htop⟩
    use v, SimpleGraph.Walk.map (SimpleGraph.Subgraph.hom H) c, ?_, ?_
    . exact (Walk.map_isCycle_iff_of_injective hom.injective).mpr hc
    . simp [htop]
  . intro hCycSub
    rcases hCycSub with ⟨v, c, hCyc,Hc⟩
    rw [←Hc]
    exact CycleCoeIsCycleGraph G c hCyc

/- A 2-regular connected subgraph is a cycle. -/
theorem SubConnectedImpCycleIffTwoReg [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (H : Subgraph G) (hCon: Subgraph.Connected H) : SubgraphIsRegular G H 2 ↔ (IsCycleSubgraph G H) := by
  rw [←CycleSubgraphCoe, ←ConnectedImpCycleIffTwoReg, ←RegularityCoerced]
  . refine ⟨by intro h; convert h, by intro h; convert h⟩
  . exact Subgraph.connected_iff'.mp hCon



/- We want to understand matchings as subgraphs. We want to do some operations on
   connected components of subgraphs. -/

/- An existence proof of transativity of reachability within subgraphs. -/
lemma SubReachableTrans {a b c} (G : SimpleGraph V) (H : Subgraph G) (p : Walk G a b) (hp : p.toSubgraph ≤ H) (hAdj : H.Adj b c) :
    ∃ (p2 : Walk G a c), p2.toSubgraph ≤ H := by
  use (Walk.cons (Subgraph.Adj.adj_sub hAdj.symm) p.reverse).reverse
  simp
  refine ⟨hp, subgraphOfAdj_le_of_adj H hAdj⟩

/- We seem to have used the following lemma a few of times already. Let us prove it seperately. -/
lemma NoVertsImpliesBot (G : SimpleGraph V) (H : Subgraph G) (hNonempty : H.verts = ∅) :
    H = ⊥ := by
  refine (Subgraph.ext_iff H ⊥).mpr ⟨?_,?_⟩
  . exact hNonempty
  . ext a b
    simp
    by_contra hAdj
    have this := H.edge_vert hAdj
    rwa [hNonempty] at this

/- The proof of the following statement is horrible. It could probably be improved a lot. -/
lemma DecomposableSubgraph (G : SimpleGraph V) (H : Subgraph G) (hnCon : ¬ Subgraph.Connected H) (hnBot : H ≠ ⊥) :
    ∃ (H1 H2 : Subgraph G), H1 ≠ ⊥ ∧ H2 ≠ ⊥ ∧ (H1 ⊓ H2 = ⊥) ∧ (H1 ⊔ H2 = H)  := by
  have vExists : ∃ v, v ∈ H.verts := by
    rw [←Set.nonempty_def, Set.nonempty_iff_ne_empty]
    by_contra this
    refine hnBot (NoVertsImpliesBot G H this)
  rcases vExists with ⟨v,hv⟩
  let S1 : Set V := {w : V | ∃ (p : Walk G v w), p.toSubgraph ≤ H}
  let S2 : Set V := {w : V | w ∈ H.verts ∧ ¬(∃ (p : Walk G v w), p.toSubgraph ≤ H)}
  use induce H S1, induce H S2
  refine ⟨?_,?_,?_,?_⟩
  . have this : (H.induce S1).verts ≠ (⊥ : Subgraph G).verts := by
      simp
      refine Set.nonempty_iff_ne_empty.mp (Set.nonempty_def.mpr ?_)
      use v
      refine Set.mem_setOf.mpr ?_
      use Walk.nil' v
      simp [hv]
    apply fun a ↦ this (congrArg verts a)
  . have this : (H.induce S2).verts ≠ (⊥ : Subgraph G).verts := by
      simp
      refine Set.nonempty_iff_ne_empty.mp (Set.nonempty_def.mpr ?_)
      by_contra allReachable; push_neg at allReachable
      revert hnCon
      simp
      refine Subgraph.connected_iff.2 ⟨?_,Set.nonempty_of_mem hv⟩
      refine (preconnected_iff_forall_exists_walk_subgraph H).mpr ?_
      intro x1 x2 x1H x2H
      simp [S2] at allReachable
      rcases allReachable x1 x1H with ⟨p1,hp1⟩
      rcases allReachable x2 x2H with ⟨p2,hp2⟩
      use Walk.append p1.reverse p2
      simp_all only [ne_eq, Walk.toSubgraph_append, Walk.toSubgraph_reverse, sup_le_iff, and_self]
    apply fun a ↦ this (congrArg verts a)
  . refine NoVertsImpliesBot _ _ ?_
    rw [Subgraph.verts_inf, induce_verts,induce_verts]
    ext a
    simp [S1,S2]
    intro pa hpa ?_
    use pa
  . apply (Subgraph.ext_iff _ _).2
    refine ⟨?_,?_⟩
    . rw [verts_sup]
      refine Set.ext ?_
      intro w
      rw [Set.mem_union]
      refine ⟨?_, ?_⟩
      . intro this
        cases' this with h h
        . simp at h
          rcases h with ⟨p,hp⟩
          refine hp.1 ?_
          rw [Walk.verts_toSubgraph, Set.mem_setOf_eq]
          exact Walk.end_mem_support p
        . exact h.1
      . intro hw
        by_cases h2 : ∃ (p : Walk G v w), p.toSubgraph ≤ H
        . left
          exact h2
        . right
          exact ⟨hw,h2⟩
    . ext a b
      refine ⟨?_,?_⟩
      . rw [←mem_edgeSet,←mem_edgeSet,Subgraph.edgeSet_sup]
        intro a_1
        simp_all only [ne_eq, not_exists, Set.mem_union, mem_edgeSet, induce_adj, Set.mem_setOf_eq, S1, S2]
        cases a_1
        · simp_all only
        · simp_all only
      . intro hAdj
        rw [←mem_edgeSet,Subgraph.edgeSet_sup, Set.mem_union,mem_edgeSet, mem_edgeSet]
        by_cases hPath : ∃ (p : Walk G v a), p.toSubgraph ≤ H
        . left
          rw [induce_adj]
          refine ⟨hPath,?_,hAdj⟩
          rw [Set.mem_setOf_eq]
          rcases hPath with ⟨pva, hpva⟩
          refine (SubReachableTrans G H pva hpva hAdj)
        . right
          refine ⟨⟨H.edge_vert hAdj, hPath⟩,⟨⟨H.edge_vert hAdj.symm,?_⟩,hAdj⟩⟩
          by_contra hpvb
          rcases hpvb with ⟨pvb,hpvb⟩
          exact hPath (SubReachableTrans G H pvb hpvb hAdj.symm)

/-  We define a (perfect) matching of a subgraph. -/

def IsPerfectMatchingOfSubgraph (G : SimpleGraph V) (H M : Subgraph G) : Prop :=
    M.verts = H.verts ∧ M ≤ H ∧ IsMatching M

lemma PerfectMatchingOfSpanningSubIsPerfect (G : SimpleGraph V) (H M : Subgraph G)
    (hMatch : IsPerfectMatchingOfSubgraph G H M) (hSpan : H.IsSpanning) : IsPerfectMatching M := by
  refine ⟨hMatch.2.2,?_⟩
  unfold IsSpanning
  rw [hMatch.1]
  exact hSpan

lemma SubgraphWithPerfectMatchingIsSpanning (G : SimpleGraph V) (H M : Subgraph G)
    (hMatch : IsPerfectMatching M) (hsub : M ≤ H) : H.IsSpanning := by
  intro v
  exact hsub.1 (hMatch.2 v)

lemma MathcingUnionHalf (G : SimpleGraph V) (M1 M2 : Subgraph G) (hInter : M1 ⊓ M2 = ⊥)
    (hM1 : IsMatching M1) (hv1 : v ∈ M1.verts) : ∃! w, (M1 ⊔ M2).Adj v w := by
  rcases hM1 hv1 with ⟨w, hwAdj,hwUniq⟩
  use w
  refine ⟨?_,?_⟩
  . simp [hwAdj]
  . intro y hy
    simp at hy
    cases' hy with hy1 hy2
    . exact hwUniq y hy1
    . exfalso
      have hcontra : v ∈ (M1 ⊓ M2).verts := Set.mem_inter hv1 (M2.edge_vert hy2)
      simp_all


lemma MatchingUnion (G : SimpleGraph V) (M1 M2 : Subgraph G) (hInter : M1 ⊓ M2 = ⊥)
    (hM1 : IsMatching M1) (hM2 : IsMatching M2) : IsMatching (M1 ⊔ M2) := by
  intro v hv
  simp at hv
  cases' hv with hv1 hv2
  . exact MathcingUnionHalf G M1 M2 hInter hM1 hv1
  . convert MathcingUnionHalf G M2 M1 ?_ hM2 hv2 using 3
    . rw [sup_comm]
    . rw [inf_comm, hInter]


lemma SubgraphMatchingUnion (G : SimpleGraph V) (H1 H2 M1 M2 : Subgraph G) (hInter : H1 ⊓ H2 = ⊥)
    (hM1 : IsPerfectMatchingOfSubgraph G H1 M1) (hM2 : IsPerfectMatchingOfSubgraph G H2 M2) :
    IsPerfectMatchingOfSubgraph G (H1 ⊔ H2) (M1 ⊔ M2) := by
  refine ⟨?_,?_,?_⟩
  . simp [hM1.1, hM2.1]
  . gcongr
    . exact hM1.2.1
    . exact hM2.2.1
  . refine MatchingUnion G M1 M2 ?_ hM1.2.2 hM2.2.2
    rw [←le_bot_iff, ←hInter]
    gcongr
    . exact hM1.2.1
    . exact hM2.2.1

lemma DifSubgraphsNonBot (G : SimpleGraph V) (H1 H2 : Subgraph G) (hdif : H1 ≠ H2) :
    H1 ⊔ H2 ≠ ⊥ := by
  by_contra H1H2bot
  rw [sup_eq_bot_iff] at H1H2bot
  rw [H1H2bot.1,H1H2bot.2] at hdif
  exact hdif rfl

/- A helper statement. -/
lemma DisjointPMGraphImpConHelper1 (G : SimpleGraph V) (H1 H2 M1 M2 : Subgraph G) (H1H2Inter : H1 ⊓ H2 = ⊥)
    (H1H2Union : H1 ⊔ H2 = M1 ⊔ M2) (hM1 : IsPerfectMatching M1) : IsPerfectMatchingOfSubgraph G H1 (H1 ⊓ M1) := by
  refine ⟨by simp; intro v _; exact hM1.2 v, inf_le_left,?_⟩
  intro v hv
  rcases hM1.1 (hM1.2 v) with ⟨w, hwAdj, hwUniq⟩
  use w
  refine ⟨?_,?_⟩
  . simp
    refine ⟨?_,hwAdj⟩
    have this : (H1 ⊔ H2).Adj v w := by
      rw [H1H2Union, sup_adj]
      left
      exact hwAdj
    cases' sup_adj.1 this with h1Adj h2Adj
    . exact h1Adj
    . exfalso
      have this2 : v ∈ (H1 ⊓ H2).verts := by
        rw [verts_inf]
        refine Set.mem_inter ?_ (Adj.fst_mem h2Adj)
        rw [verts_inf] at hv
        exact hv.1
      rw [H1H2Inter] at this2
      simp at this2
  . intro y hyAdj
    apply hwUniq y
    exact (inf_adj.1 hyAdj).2

lemma DisjointPMGraphImpConHelper2 (G : SimpleGraph V) (H1 H2 M1 M2 : Subgraph G) (H1H2Inter : H1 ⊓ H2 = ⊥)
    (H1H2Union : H1 ⊔ H2 = M1 ⊔ M2) (hM1 : IsPerfectMatching M1) (H1nBot: H1 ≠ ⊥) :
    M1.edgeSet ∩ ((H1 ⊓ M1) ⊔ (H2 ⊓ M2)).edgeSet ≠ ∅ := by
  have h := DisjointPMGraphImpConHelper1 G H1 H2 M1 M2 H1H2Inter H1H2Union hM1
  simp
  have this : ∃ e, e ∈ (H1 ⊓ M1).edgeSet := by
    have this2 : ∃ v, v ∈ H1.verts := by
      by_contra H1empty
      exact H1nBot (NoVertsImpliesBot G H1 (Set.not_nonempty_iff_eq_empty.mp H1empty))
    rcases this2 with ⟨v,hv⟩
    rcases h.2.2 ⟨hv, hM1.2 v⟩ with ⟨w,wAdj,_⟩
    use s(v,w)
    exact wAdj
  rcases this with ⟨e,he⟩
  push_neg
  use e
  refine ⟨by rw [edgeSet_inf] at he; exact he.2 ,by left; convert he; exact edgeSet_inf.symm⟩

/- A graph with exclusively disjoint perfect matchings -/
def HasExclusivelyDisjointPM (G : SimpleGraph V) : Prop :=
  ∀ (M1 M2 : Subgraph G), (IsPerfectMatching M1 ∧ IsPerfectMatching M2 ∧ M1 ≠ M2) → M1.edgeSet ∩ M2.edgeSet = ∅

theorem DisjointPMGraphImpCon (G : SimpleGraph V) (hprop : HasExclusivelyDisjointPM G) (M1 M2 : Subgraph G)
    (hM1 : IsPerfectMatching M1) (hM2 : IsPerfectMatching M2) (hdif : M1 ≠ M2) : Subgraph.Connected (M1 ⊔ M2) := by
  by_contra hnCon
  rcases DecomposableSubgraph G _ hnCon (DifSubgraphsNonBot G _ _ hdif) with ⟨H1,H2,H1nBot,H2nBot,H1H2Inter,H1H2Union⟩
  have hM3 : IsPerfectMatching ((H1 ⊓ M1) ⊔ (H2 ⊓ M2)) := by
    refine PerfectMatchingOfSpanningSubIsPerfect G (H1 ⊔ H2) _ ?_ ?_
    . convert SubgraphMatchingUnion G _ _ _ _ H1H2Inter ?_ ?_
      . exact DisjointPMGraphImpConHelper1 G _ _ _ _ H1H2Inter H1H2Union hM1
      . refine DisjointPMGraphImpConHelper1 G H2 H1 M2 M1 ?_ ?_ hM2
        . convert H1H2Inter using 1
          rw [inf_comm]
        . convert H1H2Union using 1
          . rw [sup_comm]
          . rw [sup_comm]
    . refine SubgraphWithPerfectMatchingIsSpanning G _ M1 hM1 ?_
      rw [H1H2Union]
      exact SemilatticeSup.le_sup_left _ _
  have this := hprop M1 ((H1 ⊓ M1) ⊔ (H2 ⊓ M2)) ⟨hM1,hM3,?_⟩
  . convert (DisjointPMGraphImpConHelper2 G H1 H2 M1 M2 H1H2Inter H1H2Union hM1 H1nBot) this
  . by_contra M1All
    have this2 := (DisjointPMGraphImpConHelper2 G H2 H1 M2 M1 ?_ ?_ hM2 H2nBot)
    . have this3 : H1 ⊓ M1 ⊔ H2 ⊓ M2 = H2 ⊓ M2 ⊔ H1 ⊓ M1 := by rw [sup_comm]
      rw [this3] at M1All
      rw [←M1All,Set.inter_comm] at this2
      exact this2 (hprop M1 M2 ⟨hM1,hM2,hdif⟩)
    . convert H1H2Inter using 1
      rw [inf_comm]
    . rw [sup_comm,H1H2Union,sup_comm]


/- Back to proving some things about regular subgraphs. -/

lemma DegreeSubgraphAdd [Fintype V] [DecidableEq V] {G : SimpleGraph V} {d1 d2 : ℕ} (H1 H2 : Subgraph G)
    (hd1 : SubgraphIsRegular G H1 d1) (hd2 : SubgraphIsRegular G H2 d2) (hverts : H1.verts = H2.verts)
    (hEdges : H1.edgeSet ∩ H2.edgeSet = ∅) : SubgraphIsRegular G (H1 ⊔ H2) (d1 + d2) := by
  intro v hv
  have hv1 : v ∈ H1.verts := by rw [verts_sup, ←hverts, Set.union_self] at hv; exact hv
  have hv2 : v ∈ H2.verts := by rw [verts_sup, hverts, Set.union_self] at hv; exact hv
  rw [SubgraphDegreeNbrSet, neighborSet_sup, FintypeInclExcl, ←SubgraphDegreeNbrSet, ←SubgraphDegreeNbrSet, hd1 v hv1, hd2 v hv2]
  convert tsub_zero (d1 + d2)
  convert Fintype.card_eq_zero
  by_contra hNonempty; simp at hNonempty
  rcases hNonempty with ⟨w,hvw1,hvw2⟩
  rw [←(Set.mem_empty_iff_false s(v,w)), ←hEdges]
  exact ⟨hvw1, hvw2⟩

lemma DegreeMatching [Fintype V] {G : SimpleGraph V} (M : Subgraph G) :
  IsMatching M ↔ SubgraphIsRegular G M 1 := isMatching_iff_forall_degree

lemma DegreePerfectMatching [Fintype V] {G : SimpleGraph V} {M : Subgraph G} (hM : IsPerfectMatching M):
  SubgraphIsRegular G M 1 := (DegreeMatching M).1 hM.1

lemma SpSubEqSupp {G : SimpleGraph V} {H1 H2 : Subgraph G} (h1 : IsSpanning H1) (h2: IsSpanning H2) :
    H1.verts = H2.verts := by rw [isSpanning_iff.1 h1, isSpanning_iff.1 h2]

lemma SpUnionLeft {G : SimpleGraph V} {H1 H2 : Subgraph G} (hsp : IsSpanning H1) :
    IsSpanning (H1 ⊔ H2) := by rw [isSpanning_iff, verts_sup, isSpanning_iff.1 hsp, Set.univ_union]

lemma SpUnionRight {G : SimpleGraph V} {H1 H2 : Subgraph G} (hsp : IsSpanning H2) :
    IsSpanning (H1 ⊔ H2) := by rw [sup_comm]; exact SpUnionLeft hsp


/- Definition of a Hamiltonian cycle. -/

def IsHamiltonianCycle {G : SimpleGraph V} (H : Subgraph G) : Prop := IsCycleSubgraph G H ∧ IsSpanning H

theorem TwoMatchingsHamiltonian [Fintype V] [DecidableEq V] (G : SimpleGraph V) (M1 M2 : Subgraph G)
    (hprop : HasExclusivelyDisjointPM G) (hM1 : IsPerfectMatching M1) (hM2 : IsPerfectMatching M2)
    (hdif : M1 ≠ M2) : IsHamiltonianCycle (M1 ⊔ M2) := by
  refine ⟨?_,?_⟩
  . rw [←SubConnectedImpCycleIffTwoReg]
    . exact DegreeSubgraphAdd M1 M2 (DegreePerfectMatching hM1) (DegreePerfectMatching hM2) (SpSubEqSupp hM1.2 hM2.2) (hprop M1 M2 ⟨hM1, hM2, hdif⟩)
    . exact DisjointPMGraphImpCon G hprop M1 M2 hM1 hM2 hdif
  . exact SpUnionLeft hM1.2
