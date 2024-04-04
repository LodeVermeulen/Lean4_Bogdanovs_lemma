import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.Subgraph
import Mathlib.Combinatorics.SimpleGraph.Matching
import Mathlib.Combinatorics.SimpleGraph.Subgraph
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Basic
-- import Mathlib.Combinatorics.SimpleGraph.Connectivity
import Mathlib.Data.List.Rotate

universe u -- v

namespace SimpleGraph

variable {V : Type u} {G : SimpleGraph V}

namespace Subgraph

-- previous variables copied from Matching.lean (added N : Subgraph G)

/-
Needed:
SimpleGraph.Connectivity.Walk.isCycle
Maybe use disjoint_edgeSet from SimpleGraph/Basic.lean

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

/- A graph with exclusively disjoint perfect matchings -/
def IsExclusivelyDisjointPMGraph (G : SimpleGraph V) : Prop :=
∀ (M₁ M₂ : Subgraph G), IsDisjointPerfectMatchingPair M₁ M₂

/- A graph that consists of a disjoint union of cycles -/
def IsCyclic (G : SimpleGraph V) : Prop := ∀ ⦃v : V⦄ (c : G.Walk v v), c.IsCycle

lemma disjoint_PMs_form_union_of_cycles (M₁ M₂ : Subgraph G)
(hm : IsDisjointPerfectMatchingPair M₁ M₂) (hg : IsExclusivelyDisjointPMGraph G) :
let PM_union := Subgraph.coe (M₁ ⊔ M₂);
IsCyclic PM_union := by
sorry
