import MyProject.Base
import Mathlib.Combinatorics.SimpleGraph.Trails

/- Some lemmas about Hamiltonian cycles -/

universe u

namespace SimpleGraph

variable {V : Type u} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {v w : V}
  {p : G.Walk v w}

namespace Walk

-- Copied from https://github.com/leanprover-community/mathlib4/compare/master...lftcm-combi
lemma Nil_iff_eq_nil : ∀ {p : G.Walk v v}, p.Nil ↔ p = nil
  | .nil | .cons _ _ => by simp

-- Copied from https://github.com/leanprover-community/mathlib4/compare/master...lftcm-combi
lemma Nil.eq_nil {p : G.Walk v v} (hp : p.Nil) : p = Walk.nil := Nil_iff_eq_nil.1 hp

-- Copied from https://github.com/leanprover-community/mathlib4/compare/master...lftcm-combi
lemma IsCycle.not_Nil {p : G.Walk v v} (hp : IsCycle p) : ¬ p.Nil := (hp.ne_nil ·.eq_nil)

-- Copied from https://github.com/leanprover-community/mathlib4/compare/master...lftcm-combi
def IsHamiltonian (p : G.Walk a b) : Prop := ∀ a, p.support.count a = 1

-- Copied from https://github.com/leanprover-community/mathlib4/compare/master...lftcm-combi
structure IsHamiltonianCycle (p : G.Walk a a) extends p.IsCycle : Prop :=
  isHamiltonian_tail : (p.tail toIsCycle.not_Nil).IsHamiltonian

end Walk

-- Copied from https://github.com/leanprover-community/mathlib4/compare/master...lftcm-combi
def IsHamiltonian (G : SimpleGraph V) : Prop :=
  Fintype.card V ≠ 1 → ∃ a, ∃ p : G.Walk a a, p.IsHamiltonianCycle

namespace Subgraph
