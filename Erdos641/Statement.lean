import Mathlib

/-!
# Erdős Problem 641 — statement

Source: P. Erdős, *Some of my favourite problems in various branches of combinatorics* (1992),
and [Er97d, p. 84]; https://www.erdosproblems.com/641. A problem of Erdős and Hajnal:

> Is there some function `f` such that for all `k ≥ 1`, if a finite graph `G` has chromatic
> number `≥ f(k)` then `G` has `k` edge-disjoint cycles on the same set of vertices?

The answer is **no** (Janzer, Steiner and Sudakov, 2024); it already fails for `k = 2`.
-/

namespace Erdos641

open SimpleGraph

/-- `G` contains `k` pairwise edge-disjoint cycles which all have the same vertex set. -/
def HasDisjointCyclesSameVertexSet {V : Type*} (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∃ (u : Fin k → V) (c : ∀ i, G.Walk (u i) (u i)),
    (∀ i, (c i).IsCycle) ∧
    (∀ i j, i ≠ j → ∀ e ∈ (c i).edges, e ∉ (c j).edges) ∧
    (∀ i j v, v ∈ (c i).support ↔ v ∈ (c j).support)

/-- **Erdős Problem 641** (negative answer): there is no function `f` such that every finite
graph of chromatic number at least `f k` contains `k` edge-disjoint cycles on the same vertex
set. -/
def Erdos641Negation : Prop :=
  ¬ ∃ f : ℕ → ℕ, ∀ k, 1 ≤ k → ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
      (f k : ℕ∞) ≤ G.chromaticNumber → HasDisjointCyclesSameVertexSet G k

/-- A finite set `F` of edges spanning a vertex set `S`, with `|F| = 2|S|` and every vertex
incident to at most four edges of `F` (e.g. the union of two edge-disjoint cycles on `S`). -/
def Dense4 {V : Type*} [DecidableEq V] (G : SimpleGraph V) : Prop :=
  ∃ (S : Finset V) (F : Finset (Sym2 V)), S.Nonempty ∧ F.card = 2 * S.card ∧
    (∀ e ∈ F, e ∈ G.edgeSet) ∧ (∀ e ∈ F, ∀ v ∈ e, v ∈ S) ∧
    ∀ v, (F.filter (fun e => v ∈ e)).card ≤ 4

section Cycles

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}

theorem cycle_card_support {u : V} {c : G.Walk u u} (hc : c.IsCycle) :
    c.support.toFinset.card = c.length := by
  have hnd := hc.support_nodup
  have hne : ¬ c.Nil := hc.not_nil
  have hmem : u ∈ c.support.tail := c.end_mem_tail_support hne
  rw [← c.cons_tail_support, List.toFinset_cons,
    Finset.insert_eq_of_mem (List.mem_toFinset.mpr hmem), List.toFinset_card_of_nodup hnd]
  have := c.length_support
  rw [← c.cons_tail_support] at this
  simp at this ⊢

theorem cycle_card_edges {u : V} {c : G.Walk u u} (hc : c.IsCycle) :
    c.edges.toFinset.card = c.length := by
  rw [List.toFinset_card_of_nodup hc.edges_nodup, c.length_edges]

theorem cycle_incident_le_two {u : V} {c : G.Walk u u} (hc : c.IsCycle) (v : V) :
    (c.edges.toFinset.filter (fun e => v ∈ e)).card ≤ 2 := by
  by_cases hv : v ∈ c.support
  · have h2 := hc.ncard_neighborSet_toSubgraph_eq_two hv
    have hfin : (c.toSubgraph.neighborSet v).Finite :=
      Set.finite_of_ncard_ne_zero (by rw [h2]; norm_num)
    have hsub : c.edges.toFinset.filter (fun e => v ∈ e) ⊆
        hfin.toFinset.image (fun w => s(v, w)) := by
      intro e he
      rw [Finset.mem_filter, List.mem_toFinset] at he
      obtain ⟨he, hve⟩ := he
      obtain ⟨w, rfl⟩ := Sym2.mem_iff_exists.mp hve
      rw [Finset.mem_image]
      refine ⟨w, ?_, rfl⟩
      rw [Set.Finite.mem_toFinset]
      exact Walk.adj_toSubgraph_iff_mem_edges.mpr he
    calc _ ≤ (hfin.toFinset.image (fun w => s(v, w))).card := Finset.card_le_card hsub
      _ ≤ hfin.toFinset.card := Finset.card_image_le
      _ = 2 := by rw [← Set.ncard_eq_toFinset_card _ hfin, h2]
  · have : c.edges.toFinset.filter (fun e => v ∈ e) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro e he hve
      rw [List.mem_toFinset] at he
      exact hv (c.mem_support_of_mem_edges he hve)
    rw [this]; simp

/-- Two edge-disjoint cycles on the same vertex set give a `Dense4` configuration. -/
theorem dense4_of_cycles (h : HasDisjointCyclesSameVertexSet G 2) : Dense4 G := by
  obtain ⟨u, c, hcyc, hdisj, hsupp⟩ := h
  set S := (c 0).support.toFinset
  have hS1 : (c 1).support.toFinset = S := by
    ext v; simp only [S, List.mem_toFinset]; exact hsupp 1 0 v
  refine ⟨S, (c 0).edges.toFinset ∪ (c 1).edges.toFinset, ⟨u 0, ?_⟩, ?_, ?_, ?_, ?_⟩
  · simp [S, Walk.start_mem_support]
  · rw [Finset.card_union_of_disjoint]
    · rw [cycle_card_edges (hcyc 0), cycle_card_edges (hcyc 1), ← cycle_card_support (hcyc 0),
        ← cycle_card_support (hcyc 1), hS1]; ring
    · rw [Finset.disjoint_left]
      intro e h0 h1
      rw [List.mem_toFinset] at h0 h1
      exact hdisj 0 1 (by decide) e h0 h1
  · intro e he
    rcases Finset.mem_union.mp he with he | he <;> rw [List.mem_toFinset] at he
    · exact (c 0).edges_subset_edgeSet he
    · exact (c 1).edges_subset_edgeSet he
  · intro e he v hv
    rcases Finset.mem_union.mp he with he | he <;> rw [List.mem_toFinset] at he
    · simp only [S, List.mem_toFinset]; exact (c 0).mem_support_of_mem_edges he hv
    · rw [← hS1]; simp only [List.mem_toFinset]; exact (c 1).mem_support_of_mem_edges he hv
  · intro v
    rw [Finset.filter_union]
    calc _ ≤ ((c 0).edges.toFinset.filter (fun e => v ∈ e)).card +
          ((c 1).edges.toFinset.filter (fun e => v ∈ e)).card := Finset.card_union_le _ _
      _ ≤ 2 + 2 := Nat.add_le_add (cycle_incident_le_two (hcyc 0) v)
          (cycle_incident_le_two (hcyc 1) v)

end Cycles

end Erdos641
