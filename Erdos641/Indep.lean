import Erdos641.EventB

/-!
# Colourings give heavy independent sets

Weight of `I`: `Σ_j |I ∩ L_j| / s_j`. The colour classes of a `q`-colouring have total weight
`C`, so one of them has weight at least `C / q`. A heavy independent set produces the
configuration `(i, T, J)` that Lemma 2.3 of Janzer–Steiner–Sudakov excludes.
-/

namespace Erdos641

open Finset

variable {C : ℕ} {s : Fin C → ℕ}

theorem card_layer (s : Fin C → ℕ) (j : Fin C) :
    (univ.filter (fun y : Vtx s => y.1 = j)).card = s j := by
  classical
  have : univ.filter (fun y : Vtx s => y.1 = j) = ({j} : Finset (Fin C)).sigma (fun _ => univ) := by
    ext v; simp
  rw [this, card_sigma]; simp

theorem sum_dens_classes (hs : ∀ i, 0 < s i) {q : ℕ} (col : Vtx s → Fin q) (j : Fin C) :
    ∑ c, dens s (univ.filter (fun v => col v = c)) j = 1 := by
  classical
  unfold dens
  rw [← sum_div, div_eq_one_iff_eq (by have := hs j; positivity)]
  have : ∀ c, ((univ.filter (fun v => col v = c)).filter (fun y : Vtx s => y.1 = j)) =
      (univ.filter (fun y : Vtx s => y.1 = j)).filter (fun v => col v = c) := by
    intro c; ext v; simp [and_comm]
  simp_rw [this]
  have h := card_eq_sum_card_fiberwise (s := univ.filter (fun y : Vtx s => y.1 = j))
    (t := (univ : Finset (Fin q))) (f := col) (fun _ _ => mem_univ _)
  have hL : (univ.filter (fun y : Vtx s => y.1 = j)).card = s j := by
    exact card_layer s j
  exact_mod_cast (h.trans (by simp [filter_filter])).symm.trans hL

theorem exists_heavy_class (hs : ∀ i, 0 < s i) {q : ℕ} (hq : 0 < q) (col : Vtx s → Fin q) :
    ∃ c : Fin q, (C : ℝ) / q ≤ ∑ j, dens s (univ.filter (fun v => col v = c)) j := by
  classical
  have htot : ∑ c : Fin q, ∑ j, dens s (univ.filter (fun v => col v = c)) j = C := by
    rw [sum_comm]; simp [sum_dens_classes hs col]
  have hne : (univ : Finset (Fin q)).Nonempty := ⟨⟨0, hq⟩, mem_univ _⟩
  obtain ⟨c, -, hc⟩ := exists_le_of_sum_le hne (f := fun _ => (C : ℝ) / q)
    (g := fun c => ∑ j, dens s (univ.filter (fun v => col v = c)) j) (by
      rw [htot, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
      rw [mul_div_cancel₀ _ (by exact_mod_cast hq.ne')])
  exact ⟨c, hc⟩

/-- A heavy independent set yields the configuration of Lemma 2.3. -/
theorem extract (hs : ∀ i, 0 < s i) (ω : Omega s) (I : Finset (Vtx s))
    (hI : ∀ x ∈ I, ∀ y ∈ I, ¬ (graph ω).Adj x y) (δ γ : ℝ) (hδ : 0 ≤ δ) (hγ : 0 ≤ γ)
    (hW : γ + C * δ + 1 ≤ ∑ j, dens s I j) :
    ∃ (i : Fin C) (T J : Finset (Vtx s)), (∀ x ∈ T, x.1 = i) ∧ (∀ y ∈ J, i < y.1) ∧
      δ * s i ≤ T.card ∧ γ ≤ ∑ j ∈ univ.filter (fun j : Fin C => i < j), dens s J j ∧
      ∀ x ∈ T, ∀ y ∈ J, ¬ (graph ω).Adj x y := by
  classical
  set d := dens s I
  have hd0 : ∀ j, 0 ≤ d j := fun j => by unfold d dens; positivity
  have hd1 : ∀ j, d j ≤ 1 := fun j => by
    unfold d dens
    rw [div_le_one (by have := hs j; positivity)]
    have : (I.filter (fun y => y.1 = j)).card ≤ s j := by
      calc _ ≤ (univ.filter (fun y : Vtx s => y.1 = j)).card :=
            card_le_card (fun v hv => by simp at hv ⊢; exact hv.2)
        _ = s j := card_layer s j
    exact_mod_cast this
  set P := univ.filter (fun j : Fin C => δ ≤ d j)
  have hP : P.Nonempty := by
    by_contra hP
    rw [not_nonempty_iff_eq_empty] at hP
    have : ∑ j, d j ≤ ∑ _j : Fin C, δ := sum_le_sum (fun j _ => by
      have : j ∉ P := by rw [hP]; exact notMem_empty j
      simp only [P, mem_filter, mem_univ, true_and, not_le] at this; exact this.le)
    rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul] at this
    linarith
  set i := P.min' hP
  have hi : δ ≤ d i := (mem_filter.mp (P.min'_mem hP)).2
  have hbelow : ∀ j < i, d j < δ := fun j hj => by
    by_contra h; push Not at h
    exact absurd (P.min'_le j (mem_filter.mpr ⟨mem_univ _, h⟩)) (not_le.mpr hj)
  -- split the weight
  have hsplit : ∑ j, d j = ∑ j ∈ univ.filter (· < i), d j + d i +
      ∑ j ∈ univ.filter (fun j => i < j), d j := by
    rw [← sum_filter_add_sum_filter_not univ (· < i)]
    have : univ.filter (fun j => ¬ j < i) = insert i (univ.filter (fun j => i < j)) := by
      ext j; simp only [mem_filter, mem_univ, true_and, mem_insert, not_lt]
      constructor
      · intro h; rcases h.lt_or_eq with h | h
        · exact Or.inr h
        · exact Or.inl h.symm
      · rintro (rfl | h); exact le_rfl; exact h.le
    rw [this, sum_insert (by simp)]; ring
  have hlow : ∑ j ∈ univ.filter (· < i), d j ≤ C * δ := by
    calc _ ≤ ∑ _j ∈ univ.filter (· < i), δ := sum_le_sum (fun j hj => (hbelow j (by simpa using hj)).le)
      _ ≤ ∑ _j : Fin C, δ := sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ => hδ)
      _ = C * δ := by rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
  refine ⟨i, I.filter (fun y => y.1 = i), I.filter (fun y => i < y.1), ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx; exact (mem_filter.mp hx).2
  · intro y hy; exact (mem_filter.mp hy).2
  · have := hi
    unfold d dens at this
    rwa [le_div_iff₀ (by have := hs i; positivity)] at this
  · have : ∀ j ∈ univ.filter (fun j : Fin C => i < j), dens s (I.filter (fun y => i < y.1)) j = d j := by
      intro j hj
      have hj : i < j := (mem_filter.mp hj).2
      unfold d dens; congr 3; ext v; simp only [mem_filter]
      constructor
      · rintro ⟨⟨h1, -⟩, h2⟩; exact ⟨h1, h2⟩
      · rintro ⟨h1, h2⟩; exact ⟨⟨h1, h2 ▸ hj⟩, h2⟩
    rw [sum_congr rfl this]
    linarith [hd1 i]
  · intro x hx y hy
    exact hI x (mem_filter.mp hx).1 y (mem_filter.mp hy).1

end Erdos641
