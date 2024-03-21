import mathlib.combinatorics.simpleGraph.connectivity
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.Subgraph
import Mathlib.Combinatorics.SimpleGraph.Matching
import Mathlib.Combinatorics.SimpleGraph.Subgraph
import Mathlib.Data.List.Rotate

universe u

namespace SimpleGraph

variable {V : Type u} {G : SimpleGraph V}

namespace Subgraph

-- previous variables copied from Matching.lean (added N : Subgraph G)

/-
Needed:
SimpleGraph.Connectivity.Walk.isCycle

Cant find anymore:
simpleGraph.Hamiltonian.walk.is_cycle

Step 1:
Prove that for a graph with only monochromatic PMs,
2 perfect matchings form a Hamiltonian cycle:=
- Show that any 2 PMs form a disjoint union of cycles.
- Show that if more than one cycle appears, the graph is not
  monochromatic, i.e. there exists another PM that is multicolored.
Because the PMs are monochromatic, their union then forms a
Hamiltonian cycle.

Definitions required for this:
-

Step 2:
You cannot split the graph into an even number of vertices,
because then a multichromatic PM would appear.
Step 3:
Prove the same for splitting into an odd number of vertices.

It might be useful to show that c_max(2n)>=2. Prove by using cycles
-/

/-
Two disjoint PMs form a disjoint union of cycles

Prove by using that every vertex in a graph is matched by an edge from a perfect
matching. Because the two PMs are disjoint, they share no edges. This means that
every vertex is matched by two edges in M1 ∪ M2. This constitutes a union of cycles.
-/
-- lemma disjoint_PMs_union_of_cycles {M1 : Subgraph G} {M2 : Subgraph G} {u v : V}
--  (hm1 : M1.IsPerfectMatching) (hm2 : M2.IsPerfectMatching) (hu : G.Adj u v):
--  G.reachable u v := by
--   sorry

-- Show that the union of two disjoint perfect matchings is empty

/- Two disjoint perfect matchings -/
def IsDisjointPerfectMatchingPair (M₁ M₂ : Subgraph G) : Prop :=
M₁.IsPerfectMatching ∧ M₂.IsPerfectMatching ∧ M₁.edgeSet ∩ M₂.edgeSet = ∅

lemma disjoint_PMs_form_union_of_cycles (M1 M₂ : Subgraph G)
(h : IsDisjointPerfectMatchingPair M₁ M₂) :
let PM_union := (M₁.edgeSet ∪ M₂.edgeSet)
∀ ⦃v : V⦄ (w : G.Walk v v), w.IsCycle := by -- from IsAcyclic
-- M1.edgeSet ∪ M2.edgeSet = ∅ := by
sorry
