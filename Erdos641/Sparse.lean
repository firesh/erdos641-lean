import Erdos641.Layered

/-!
# From a `Dense4` configuration to a locally dense set in the lower layers

This is the deterministic part of Lemma 2.1 of Janzer–Steiner–Sudakov.
-/

namespace Erdos641

open Finset

variable {C : ℕ} {s : Fin C → ℕ}

/-- Layer sizes extended by `0`. -/
def sN (s : Fin C → ℕ) (n : ℕ) : ℕ := if h : n < C then s ⟨n, h⟩ else 0

theorem sN_eq (s : Fin C → ℕ) (i : Fin C) : sN s i = s i := by simp [sN]

theorem card_layers_ge (s : Fin C → ℕ) (r : ℕ) :
    (univ.filter (fun v : Vtx s => r ≤ v.1.val)).card =
      ∑ j ∈ univ.filter (fun j : Fin C => r ≤ j.val), s j := by
  classical
  have : univ.filter (fun v : Vtx s => r ≤ v.1.val) =
      (univ.filter (fun j : Fin C => r ≤ j.val)).sigma (fun _ => univ) := by
    ext v; simp
  rw [this, card_sigma]
  simp

section
variable (hdec : ∀ i j : Fin C, i ≤ j → s j ≤ s i)
  (htail : ∀ r : Fin C, ∑ j ∈ univ.filter (fun j : Fin C => r ≤ j), s j ≤ 2 * s r)
include hdec htail

omit htail in
theorem sN_anti {m n : ℕ} (h : m ≤ n) : sN s n ≤ sN s m := by
  unfold sN
  by_cases hn : n < C
  · simp only [hn, (by omega : m < C), ↓reduceDIte]
    exact hdec ⟨m, by omega⟩ ⟨n, hn⟩ (by simp [Fin.le_def]; omega)
  · simp [hn]

omit hdec in
theorem tail_le (r : ℕ) :
    ∑ j ∈ univ.filter (fun j : Fin C => r ≤ j.val), s j ≤ 2 * sN s r := by
  by_cases hr : r < C
  · have := htail ⟨r, hr⟩
    rw [show sN s r = s ⟨r, hr⟩ by simp [sN, hr]]
    convert this using 2
    ext j; simp [Fin.le_def]
  · rw [show univ.filter (fun j : Fin C => r ≤ j.val) = ∅ by
      ext j; simp; omega]
    simp

open Classical in
/-- **Deterministic part of Lemma 2.1.** -/
theorem local_dense_of_dense4 (ω : Omega s) (hD : Dense4 (graph ω)) :
    ∃ (a : Fin C) (X : Finset (Vtx s)) (F : Finset (Sym2 (Vtx s))),
      0 < a.val ∧ X.Nonempty ∧ (∀ x ∈ X, x.1 < a) ∧ X.card ≤ 1000 * s a ∧
      (∀ e ∈ F, e ∈ (graph ω).edgeSet) ∧ (∀ e ∈ F, ∀ v ∈ e, v ∈ X) ∧
      11 * X.card ≤ 10 * F.card := by
  obtain ⟨S, F, hne, hcard, hedge, hend, hdeg⟩ := hD
  set s0 := S.card with hs0
  have hs0pos : 0 < s0 := hne.card_pos
  have hex : ∃ n, 1000 * sN s n < s0 := ⟨C, by simp [sN]; omega⟩
  set r := Nat.find hex with hr_def
  have hr : 1000 * sN s r < s0 := Nat.find_spec hex
  have hlt : ∀ n < r, s0 ≤ 1000 * sN s n := fun n hn => by
    have := Nat.find_min hex hn; omega
  have hrC : r ≤ C := Nat.find_min' hex (by simp [sN]; omega)
  have hhigh : ∀ v : Vtx s, r ≤ v.1.val → 1000 * s v.1 < s0 := fun v hv => by
    have := sN_anti hdec hv; rw [sN_eq] at this; omega
  -- vertices in high layers
  set Sh := S.filter (fun v => r ≤ v.1.val)
  have hSh : 1000 * Sh.card < 2 * s0 := by
    have h1 : Sh.card ≤ ∑ j ∈ univ.filter (fun j : Fin C => r ≤ j.val), s j := by
      rw [← card_layers_ge]
      exact card_le_card (fun v hv => by simp [Sh] at hv ⊢; exact hv.2)
    have h2 := tail_le htail r
    omega
  have hr1 : 1 ≤ r := by
    by_contra h0
    have : Sh = S := by
      ext v; simp only [Sh, mem_filter, and_iff_left_iff_imp]; intro; omega
    rw [this] at hSh; omega
  set a := r - 1 with ha_def
  have haC : a < C := by omega
  set aF : Fin C := ⟨a, haC⟩
  set X := S.filter (fun v => v.1.val < a)
  set Y := S.filter (fun v => v.1.val = a)
  set Fh := F.filter (fun e => ∃ v ∈ e, r ≤ v.1.val)
  set Fxy := F.filter (fun e => (∀ v ∈ e, v.1.val ≤ a) ∧ ∃ v ∈ e, v.1.val = a)
  set Fxx := F.filter (fun e => ∀ v ∈ e, v.1.val < a)
  -- the three classes cover `F`
  have hcover : F ⊆ Fh ∪ Fxy ∪ Fxx := by
    intro e he
    simp only [Fh, Fxy, Fxx, mem_union, mem_filter]
    by_cases h1 : ∃ v ∈ e, r ≤ v.1.val
    · exact Or.inl (Or.inl ⟨he, h1⟩)
    push Not at h1
    by_cases h2 : ∃ v ∈ e, v.1.val = a
    · exact Or.inl (Or.inr ⟨he, fun v hv => by have := h1 v hv; omega, h2⟩)
    push Not at h2
    exact Or.inr ⟨he, fun v hv => by have := h1 v hv; have := h2 v hv; omega⟩
  -- degree bounds
  have hdegset : ∀ T : Finset (Vtx s), ∀ G' ⊆ F, (∀ e ∈ G', ∃ v ∈ T, v ∈ e) →
      G'.card ≤ 4 * T.card := by
    intro T G' hG' hT
    have : G' ⊆ T.biUnion (fun v => F.filter (fun e => v ∈ e)) := by
      intro e he
      obtain ⟨v, hv, hve⟩ := hT e he
      exact mem_biUnion.mpr ⟨v, hv, mem_filter.mpr ⟨hG' he, hve⟩⟩
    calc G'.card ≤ _ := card_le_card this
      _ ≤ ∑ v ∈ T, (F.filter (fun e => v ∈ e)).card := card_biUnion_le
      _ ≤ ∑ _v ∈ T, 4 := sum_le_sum (fun v _ => hdeg v)
      _ = 4 * T.card := by rw [sum_const, smul_eq_mul, mul_comm]
  have hFh : Fh.card ≤ 4 * Sh.card := hdegset Sh Fh (filter_subset _ _) (by
    intro e he
    obtain ⟨he, v, hv, hrv⟩ := mem_filter.mp he
    exact ⟨v, mem_filter.mpr ⟨hend e he v hv, hrv⟩, hv⟩)
  have hFxyY : Fxy.card ≤ 4 * Y.card := hdegset Y Fxy (filter_subset _ _) (by
    intro e he
    obtain ⟨he, -, v, hv, hav⟩ := mem_filter.mp he
    exact ⟨v, mem_filter.mpr ⟨hend e he v hv, hav⟩, hv⟩)
  -- each vertex below layer `a` has at most one edge to layer `a`
  have hFxyX : Fxy.card ≤ X.card := by
    have : Fxy ⊆ X.image (fun x => if h : x.1 < aF then s(x, nb ω x aF h) else s(x, x)) := by
      intro e he
      obtain ⟨he, hle, v, hv, hav⟩ := mem_filter.mp he
      have hE := hedge e he
      induction e using Sym2.ind with
      | h p q =>
        have hadj : (graph ω).Adj p q := hE
        rcases Sym2.mem_iff.mp hv with rfl | rfl
        · -- `v = p` is in layer `a`, so `q` is below
          have hq : q.1.val ≤ a := hle q (Sym2.mem_mk_right _ _)
          have hne' : q.1 ≠ v.1 := fun h => not_adj_same_layer h.symm hadj
          have hqa : q.1 < aF := by
            show q.1.val < a; have : q.1.val ≠ a := fun h => hne' (Fin.ext (h.trans hav.symm)); omega
          have hva : v.1 = aF := Fin.ext hav
          refine mem_image.mpr ⟨q, mem_filter.mpr ⟨hend _ he q (Sym2.mem_mk_right _ _), hqa⟩, ?_⟩
          rw [dite_eq_left_of_eq_true (eq_true hqa), Sym2.eq_swap]
          congr 1
          have h' : q.1 < v.1 := hva ▸ hqa
          rw [eq_nb_of_adj hadj.symm h']
          congr 1; simp [hva]
        · have hp : p.1.val ≤ a := hle p (Sym2.mem_mk_left _ _)
          have hne' : p.1 ≠ v.1 := fun h => not_adj_same_layer h hadj
          have hpa : p.1 < aF := by
            show p.1.val < a; have : p.1.val ≠ a := fun h => hne' (Fin.ext (h.trans hav.symm)); omega
          have hva : v.1 = aF := Fin.ext hav
          refine mem_image.mpr ⟨p, mem_filter.mpr ⟨hend _ he p (Sym2.mem_mk_left _ _), hpa⟩, ?_⟩
          rw [dite_eq_left_of_eq_true (eq_true hpa)]
          congr 1
          have h' : p.1 < v.1 := hva ▸ hpa
          rw [eq_nb_of_adj hadj h']
          congr 1; simp [hva]
    exact (card_le_card this).trans card_image_le
  have hXY : X.card + Y.card ≤ s0 := by
    rw [← card_union_of_disjoint (disjoint_filter.mpr (fun v _ h1 h2 => by omega))]
    exact card_le_card (union_subset (filter_subset _ _) (filter_subset _ _))
  have hX : X.card ≤ s0 := by omega
  have hsum : 2 * s0 ≤ Fh.card + Fxy.card + Fxx.card := by
    rw [← hcard]
    exact (card_le_card hcover).trans ((card_union_le _ _).trans
      (Nat.add_le_add_right (card_union_le _ _) _))
  have hFxx : 10000 * Fxx.card ≥ 11000 * X.card := by omega
  have hFxxpos : 0 < Fxx.card := by omega
  obtain ⟨e0, he0⟩ := card_pos.mp hFxxpos
  have hXne : X.Nonempty := by
    obtain ⟨he0, hall⟩ := mem_filter.mp he0
    induction e0 using Sym2.ind with
    | h p q => exact ⟨p, mem_filter.mpr ⟨hend _ he0 p (Sym2.mem_mk_left _ _),
        hall p (Sym2.mem_mk_left _ _)⟩⟩
  have hapos : 0 < a := by
    obtain ⟨x, hx⟩ := hXne
    have := (mem_filter.mp hx).2; omega
  refine ⟨aF, X, Fxx, hapos, hXne, fun x hx => by
      rw [Fin.lt_def]; exact (mem_filter.mp hx).2, ?_, fun e he => hedge e (filter_subset _ _ he),
    fun e he v hv => mem_filter.mpr ⟨hend e (filter_subset _ _ he) v hv, (mem_filter.mp he).2 v hv⟩,
    by omega⟩
  have := hlt a (by omega)
  rw [show sN s a = s aF by simp [sN, haC, aF]] at this
  omega

end

end Erdos641
