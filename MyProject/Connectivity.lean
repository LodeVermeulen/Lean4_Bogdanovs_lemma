import MyProject.Base
import Mathlib.Combinatorics.SimpleGraph.Connectivity

/- Some lemmas about connectivity -/

universe u

namespace SimpleGraph

variable {V : Type u} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {v w : V}
  {p : G.Walk v w}

namespace Walk
