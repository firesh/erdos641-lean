import Erdos641.Counting

/-!
# The independent-set event (Lemma 2.3 of Janzer–Steiner–Sudakov)

For `T` inside layer `i` and `J` inside the later layers, the configurations with no edge
between `T` and `J` form at most a fraction `exp (-|T| · Σ_{j > i} |J ∩ L_j| / s_j)`.
-/

namespace Erdos641

open Finset

variable {C : ℕ} {s : Fin C → ℕ}

/-- Density of `J` in layer `j`. -/
noncomputable def dens (s : Fin C → ℕ) (J : Finset (Vtx s)) (j : Fin C) : ℝ :=
  ((J.filter (fun y => y.1 = j)).card : ℝ) / s j

theorem card_positions (J : Finset (Vtx s)) (j : Fin C) :
    (univ.filter (fun v : Fin (s j) => (⟨j, v⟩ : Vtx s) ∈ J)).card =
      (J.filter (fun y => y.1 = j)).card := by
  classical
  refine card_bij (fun v _ => (⟨j, v⟩ : Vtx s)) ?_ ?_ ?_
  · intro v hv; simp only [mem_filter, mem_univ, true_and] at hv ⊢; simpa using hv
  · intro v _ w _ h; simpa using h
  · intro y hy
    obtain ⟨hy, rfl⟩ := mem_filter.mp hy
    exact ⟨y.2, by simpa using hy, rfl⟩

theorem one_sub_dens (hs : ∀ i, 0 < s i) (J : Finset (Vtx s)) (j : Fin C) :
    ((univ.filter (fun v : Fin (s j) => (⟨j, v⟩ : Vtx s) ∉ J)).card : ℝ) / s j =
      1 - dens s J j := by
  classical
  have hsj : (s j : ℝ) ≠ 0 := by have := hs j; positivity
  have h1 := card_filter_add_card_filter_not
    (s := (univ : Finset (Fin (s j)))) (fun v => (⟨j, v⟩ : Vtx s) ∈ J)
  rw [card_univ, Fintype.card_fin, card_positions] at h1
  unfold dens
  rw [eq_sub_iff_add_eq, ← add_div, div_eq_one_iff_eq hsj]
  exact_mod_cast (by omega : _)

theorem sum_keys (i : Fin C) (T : Finset (Vtx s)) (hT : ∀ x ∈ T, x.1 = i) (g : Fin C → ℝ) :
    ∑ k ∈ univ.filter (fun k : Key s => (⟨k.1.1.1, k.2⟩ : Vtx s) ∈ T), g k.1.1.2 =
      T.card * ∑ j ∈ univ.filter (fun j : Fin C => i < j), g j := by
  classical
  rw [show (T.card : ℝ) * ∑ j ∈ univ.filter (fun j : Fin C => i < j), g j =
      ∑ p ∈ T ×ˢ univ.filter (fun j : Fin C => i < j), g p.2 by
    simp only [sum_product, sum_const, nsmul_eq_mul]]
  refine sum_bij' (fun k _ => ((⟨k.1.1.1, k.2⟩ : Vtx s), k.1.1.2))
    (fun p hp => ⟨⟨(p.1.1, p.2), by
        obtain ⟨h1, h2⟩ := mem_product.mp hp
        rw [hT _ h1]; exact (mem_filter.mp h2).2⟩, p.1.2⟩) ?_ ?_ ?_ ?_ ?_
  · intro k hk
    simp only [mem_filter, mem_univ, true_and] at hk
    refine mem_product.mpr ⟨hk, mem_filter.mpr ⟨mem_univ _, ?_⟩⟩
    rw [← hT _ hk]; exact k.1.2
  · intro p hp
    simp only [mem_filter, mem_univ, true_and]
    exact (mem_product.mp hp).1
  · intro k _; rfl
  · intro p _; rfl
  · intro k _; rfl

open Classical in
/-- **Event B.** -/
theorem eventB_card (hs : ∀ i, 0 < s i) (i : Fin C) (T J : Finset (Vtx s))
    (hT : ∀ x ∈ T, x.1 = i) :
    ((univ.filter (fun ω : Omega s => ∀ x ∈ T, ∀ y ∈ J, ¬ (graph ω).Adj x y)).card : ℝ) ≤
      (Fintype.card (Omega s) : ℝ) *
        Real.exp (-(T.card * ∑ j ∈ univ.filter (fun j : Fin C => i < j), dens s J j)) := by
  classical
  set K := univ.filter (fun k : Key s => (⟨k.1.1.1, k.2⟩ : Vtx s) ∈ T)
  set A : ∀ k : Key s, Finset (Fin (s k.1.1.2)) :=
    fun k => univ.filter (fun v => (⟨k.1.1.2, v⟩ : Vtx s) ∉ J)
  have hle := card_le_constrained hs
    (fun ω : Omega s => ∀ x ∈ T, ∀ y ∈ J, ¬ (graph ω).Adj x y) K A (by
    intro ω hω k hk
    simp only [K, mem_filter, mem_univ, true_and] at hk
    simp only [A, mem_filter, mem_univ, true_and]
    intro hJ
    exact hω _ hk _ hJ (Or.inl ⟨k.1.2, rfl⟩))
  refine hle.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
  calc ∏ k ∈ K, ((A k).card : ℝ) / s k.1.1.2
      ≤ ∏ k ∈ K, Real.exp (-dens s J k.1.1.2) :=
        prod_le_prod (fun k _ => by positivity)
          (fun k _ => by rw [one_sub_dens hs]; exact Real.one_sub_le_exp_neg _)
    _ = Real.exp (∑ k ∈ K, -dens s J k.1.1.2) := (Real.exp_sum _ _).symm
    _ = _ := by rw [sum_neg_distrib, sum_keys i T hT]

end Erdos641
