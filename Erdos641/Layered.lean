import Erdos641.Statement

/-!
# The layered graph

Layers `0, …, C-1` of sizes `s 0 ≥ s 1 ≥ …`. A configuration `ω` chooses, for every vertex `x`
of layer `i` and every later layer `j > i`, one vertex `ω(i, j, x)` of layer `j`; the graph joins
`x` to exactly these vertices. (This is the construction of Janzer–Steiner–Sudakov; the random
choice is replaced later by a counting argument.)
-/

namespace Erdos641

open Finset

variable {C : ℕ} (s : Fin C → ℕ)

/-- Vertices: a layer and a position in it. -/
abbrev Vtx := Σ i : Fin C, Fin (s i)

/-- A key of the configuration: a lower layer `i`, an upper layer `j > i`, a vertex of `i`. -/
abbrev Key := Σ p : {p : Fin C × Fin C // p.1 < p.2}, Fin (s p.1.1)

/-- Configurations. -/
abbrev Omega := ∀ k : Key s, Fin (s k.1.1.2)

variable {s}

def key (x : Vtx s) (j : Fin C) (h : x.1 < j) : Key s := ⟨⟨(x.1, j), h⟩, x.2⟩

/-- `x` (lower layer) chose `y` (upper layer). -/
def Chose (ω : Omega s) (x y : Vtx s) : Prop :=
  ∃ h : x.1 < y.1, ((ω (key x y.1 h) : ℕ) = y.2)

def graph (ω : Omega s) : SimpleGraph (Vtx s) where
  Adj x y := Chose ω x y ∨ Chose ω y x
  symm := ⟨fun _ _ h => Or.symm h⟩
  loopless := ⟨fun x h => by rcases h with ⟨h, _⟩ | ⟨h, _⟩ <;> exact lt_irrefl _ h⟩

theorem graph_adj {ω : Omega s} {x y : Vtx s} :
    (graph ω).Adj x y ↔ Chose ω x y ∨ Chose ω y x := Iff.rfl

theorem not_adj_same_layer {ω : Omega s} {x y : Vtx s} (h : x.1 = y.1) : ¬ (graph ω).Adj x y := by
  rintro (⟨h', -⟩ | ⟨h', -⟩) <;> omega

/-- The unique neighbour of `x` in a later layer `j`. -/
def nb (ω : Omega s) (x : Vtx s) (j : Fin C) (h : x.1 < j) : Vtx s := ⟨j, ω (key x j h)⟩

theorem eq_nb_of_adj {ω : Omega s} {x y : Vtx s} (hxy : (graph ω).Adj x y) (h : x.1 < y.1) :
    y = nb ω x y.1 h := by
  rcases hxy with ⟨h', hv⟩ | ⟨h', -⟩
  · obtain ⟨j, v⟩ := y
    simp only [nb] at hv ⊢
    congr 1
    exact (Fin.ext hv).symm
  · exact absurd h' (by omega)

end Erdos641
