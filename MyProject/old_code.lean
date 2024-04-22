/- A graph that consists of a disjoint union of cycles -/
def IsCyclic (G : SimpleGraph V) : Prop :=
∀ ⦃v : V⦄, (∃ w : G.Walk v v, w ≠ Walk.nil) ∧ ∀ (w : G.Walk v v), w.IsTrail → w.IsCycle

/- Two disjoint PMs form a union of cycles -/
lemma disjoint_PMs_form_union_of_cycles (M₁ M₂ : Subgraph G)
  (hm : IsDisjointPerfectMatchingPair M₁ M₂):
  IsCyclic (fromEdgeSet (M₁.edgeSet ∪ M₂.edgeSet)) :=
  fun v => by
  refine ⟨?_, ?_⟩ -- split into the two goals
  · obtain ⟨hm, -⟩ := hm -- obtain hm:=M₁.IsPerfectMatching by using hm (original)
    rw [isPerfectMatching_iff] at hm -- hm now states that ∀ (v : V), ∃! w, M₁.Adj v w
    obtain ⟨w, hw, -⟩ := hm v -- here hw := M₁.Adj v w
    have hvw : G.Adj v w := hw.adj_sub
    have walk := Adj.toWalk hvw
    -- exact Adj.ne walk
    -- Use Adj.ne to show that v ≠ w
    -- let hn := w ≠ Walk.nil
    -- Use not_nil_of_ne to show that the walk is not nil
    sorry
  · intro w
    sorry

lemma disjoint_PMs_form_union_of_cycles' (M₁ M₂ : Subgraph G)
  (hm : IsDisjointPerfectMatchingPair M₁ M₂) :
  IsDisjointUnionOfCycles (fromEdgeSet (M₁.edgeSet ∪ M₂.edgeSet)) := by
  refine ⟨?_,?_,?_,?_⟩
  · exact Set.univ
  · intro sG₁ hsG₁ sG₂ hsG₂ hne sG₃ hse₁ hse₂
    simp_all only [Set.mem_univ, ne_eq, id_eq, le_bot_iff]
    sorry -- prove this by
  · exact sSup_univ
  · intro H hH
    simp_all only [Set.mem_univ]
    refine ⟨?_,?_,?_⟩
    · sorry
    · exact Walk.nil' (sorryAx V)
    · refine ⟨?_,?_⟩
      · simp_all only [Walk.IsCycle.not_of_nil]
        sorry
      · simp_all only [Walk.toSubgraph]
        refine (eq_singletonSubgraph_iff_verts_eq H).mpr ?refine_4.refine_3.refine_2.a
        refine (eq_singletonSubgraph_iff_verts_eq H).mp ?refine_4.refine_3.refine_2.a.a
    -- sorry
      -- · sorry
      -- · sorry

lemma disjoint_PMs_form_union_of_cycles' (M₁ M₂ : Subgraph G)
  (hm : IsDisjointPerfectMatchingPair M₁ M₂) :
  IsDisjointUnionOfCycles (fromEdgeSet (M₁.edgeSet ∪ M₂.edgeSet)) := by
  obtain ⟨hM₁, hM₂, hd⟩ := hm
  refine ⟨?_,?_,?_,?_⟩
  · exact Set.univ  -- The set P consisting of the union of M₁ and M₂
  · rw [Set.PairwiseDisjoint]
    intro sG₁ hsG₁ sG₂ hsG₂ hne
    simp_all only [Set.mem_univ, ne_eq]
    sorry -- need to use hd to show that (Disjoint on id) sG₁ sG₂
  · exact sSup_univ
  · sorry -- use hM₁, hM₂ to show that subgraphs made with M₁, M₂ exist that are cycles

/- The vertex set of a PM is the same as the graph it is a subgraph of -/
lemma PM_verts_eq_vertex_set (M : Subgraph G) (hm : M.IsPerfectMatching) :
  M.verts = Set.univ := by -- could show = G.support instead
  refine isSpanning_iff.mp ?_
  obtain ⟨-,hs⟩ := hm
  exact hs

/- Two PMs of the same graph have the same vertex sets -/
lemma PMs_same_verts (M₁ M₂ : Subgraph G) (hM₁ : M₁.IsSpanning)
  (hM₂ : M₂.IsSpanning) : M₁.verts = M₂.verts := by
    have hM₁_univ : M₁.verts = Set.univ := isSpanning_iff.mp ?_
    have hM₂_univ : M₂.verts = Set.univ := isSpanning_iff.mp ?_
    simp_all only
    simp_all only
    simp_all only

/- A Hamiltonian cycle. Copied from github.com/leanprover-community/mathlib/pull/8737 -/
-- def isHamiltonianCycle {u : V} (p : G.Walk u u) : Prop :=
-- p.IsTrail ∧ ∀ v, p.support.tail.count v = 1

-- lemma disjoint_PMs_form_Hamiltonian_cycle (M₁ M₂ : Subgraph G)
-- (hm : IsDisjointPerfectMatchingPair M₁ M₂) (hg : IsExclusivelyDisjointPMGraph G) :
-- let PM_union := Subgraph.coe (M₁ ⊔ M₂);
-- isHamiltonianCycle PM_union := by sorry

-- define an inductive that constructs a path by alternating between PMs
-- inductive:
-- Assumption: G is made with 2 PMs -> G is 2-regular
-- sub_graphs = []
-- turn = 0
-- for edge in G.edgeSet:
--  edge_added = False
--  for sub_graph in sub_graphs:
--    if hasVertexInCommon(sub_graph, edge):
--      sub_graph.append(edge)
--      edge_added = True
--      break
--  if edge_added:
--    continue
--  subGraphs.append([edge])

-- let P := we can use this to make the set of subgraphs
-- use P we can use this to solve the first subgoal (defining the required set)
