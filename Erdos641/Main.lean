import Erdos641.Params

/-!
# The main theorem

For every `m ≥ 2` some configuration avoids both bad events. Its graph is not
`(m - 1)`-colourable and has no `Dense4` configuration, so it has no two edge-disjoint cycles on
the same vertex set. This answers Erdős Problem 641 in the negative.
-/

namespace Erdos641

open Finset

section
variable {C : ℕ} {s : Fin C → ℕ}

open Classical in
/-- Outside the locally dense event there is no `Dense4` configuration. -/
theorem not_dense4_of_not_badA (hdec : ∀ i j : Fin C, i ≤ j → s j ≤ s i)
    (htail : ∀ r : Fin C, ∑ j ∈ univ.filter (fun j : Fin C => r ≤ j), s j ≤ 2 * s r)
    (ω : Omega s) (hA : ¬ BadA ω) : ¬ Dense4 (graph ω) := by
  intro hD
  obtain ⟨a, X, F, ha, hXne, hXa, hXcard, hFe, hFX, hdense⟩ :=
    local_dense_of_dense4 hdec htail ω hD
  have hle := card_edges_le_keys ω a.val X (fun x hx => hXa x hx) F hFe hFX
  obtain ⟨Q, hQsub, hQcard⟩ := exists_subset_card_eq
    (s := (keysIn a.val X).filter (fun k => ω k ∈ posIn X k)) (n := fA X.card)
    (by unfold fA; omega)
  exact hA ⟨a, mem_filter.mpr ⟨mem_univ _, ha⟩, X,
    mem_filter.mpr ⟨mem_powerset.mpr (subset_univ _), hXa, hXne.card_pos, hXcard⟩,
    Q, mem_powersetCard.mpr ⟨hQsub.trans (filter_subset _ _), hQcard⟩,
    fun k hk => (mem_filter.mp (hQsub hk)).2⟩

open Classical in
/-- Outside the heavy independent set event the graph is not `q`-colourable. -/
theorem not_colorable_of_not_badB (hs : ∀ i, 0 < s i) {q : ℕ} (hq : 0 < q) (δ γ : ℝ)
    (hδ : 0 ≤ δ) (hγ : 0 ≤ γ) (hW : γ + C * δ + 1 ≤ (C : ℝ) / q) (ω : Omega s)
    (hB : ¬ BadB δ γ ω) : ¬ (graph ω).Colorable q := by
  rintro ⟨col⟩
  obtain ⟨c, hc⟩ := exists_heavy_class hs hq col
  have hI : ∀ x ∈ univ.filter (fun v => col v = c), ∀ y ∈ univ.filter (fun v => col v = c),
      ¬ (graph ω).Adj x y := by
    intro x hx y hy hxy
    exact col.valid hxy ((mem_filter.mp hx).2.trans (mem_filter.mp hy).2.symm)
  obtain ⟨i, T, J, hT, hJ, hTc, hJd, hTJ⟩ := extract hs ω _ hI δ γ hδ hγ (hW.trans hc)
  exact hB ⟨i, mem_univ _, T,
    mem_filter.mpr ⟨mem_powerset.mpr (fun x hx => mem_layer.mpr (hT x hx)), hTc⟩, J,
    mem_filter.mpr ⟨mem_powerset.mpr (fun y hy => mem_above.mpr (hJ y hy)), hJd⟩, hTJ⟩

theorem card_vtx : Fintype.card (Vtx s) = ∑ i, s i := by
  simp [Fintype.card_sigma]

end

/-- For every `m ≥ 2` there is a layered graph that is not `(m - 1)`-colourable and has no
`Dense4` configuration. -/
theorem exists_good_graph (m : ℕ) (hm : 2 ≤ m) :
    ∃ (C : ℕ) (s : Fin C → ℕ) (ω : Omega s),
      ¬ (graph ω).Colorable (m - 1) ∧ ¬ Dense4 (graph ω) := by
  classical
  have hm1 : 1 ≤ m := by omega
  have hC : 1 ≤ CC m := one_le_CC m hm1
  have hs : ∀ i, 0 < ss m i := ss_pos m
  have hdec := ss_anti m
  have htail := ss_tail m hm1
  set N := Fintype.card (Vtx (ss m)) with hNdef
  have hN : ∀ i, ss m i ≤ N := fun i => by
    rw [hNdef, card_vtx]; exact single_le_sum (fun j _ => Nat.zero_le _) (mem_univ i)
  have hN0 : N ≤ 2 * ss m ⟨0, by omega⟩ := by
    rw [hNdef, card_vtx]
    have := htail ⟨0, by omega⟩
    have hf : univ.filter (fun j : Fin (CC m) => (⟨0, by omega⟩ : Fin (CC m)) ≤ j) = univ := by
      ext j; simp [Fin.le_def]
    rwa [hf] at this
  have hΩpos : 0 < Fintype.card (Omega (ss m)) :=
    Fintype.card_pos_iff.mpr ⟨fun k => ⟨0, hs _⟩⟩
  have hΩ : (0 : ℝ) < Fintype.card (Omega (ss m)) := by exact_mod_cast hΩpos
  -- the locally dense event
  have hA : ((univ.filter (fun ω : Omega (ss m) => BadA ω)).card : ℝ) ≤
      Fintype.card (Omega (ss m)) * (1 / 4) := by
    refine (card_badA_le hs hdec).trans (mul_le_mul_of_nonneg_left ?_ hΩ.le)
    refine sumA_le hC hs N hN (fun a ha => ?_)
    refine le_trans ?_ (ss_gapA m a ha)
    refine Nat.mul_le_mul_right _ (Nat.pow_le_pow_left ?_ 10)
    calc 72 * CC m ^ 2 * N ≤ 72 * CC m ^ 2 * (2 * ss m ⟨0, by omega⟩) :=
          Nat.mul_le_mul_left _ hN0
      _ = 144 * CC m ^ 2 * ss m ⟨0, by omega⟩ := by ring
  -- the heavy independent set event
  have hB : ((univ.filter (fun ω : Omega (ss m) => BadB (1 / (4 * m)) (24 * m) ω)).card : ℝ) ≤
      Fintype.card (Omega (ss m)) * (1 / 4) := by
    refine (card_badB_le hs _ _).trans (mul_le_mul_of_nonneg_left ?_ hΩ.le)
    refine sumB_le (C := CC m) hm1 rfl hs _ (fun i => ?_)
    have h1 : (above (ss m) i).card ≤ 2 * sN (ss m) (i.val + 1) := by
      rw [card_above_eq]
      have := tail_le htail (i.val + 1)
      convert this using 2
      ext j; simp only [mem_filter, mem_univ, true_and, Fin.lt_def]; omega
    have h2 := ss_gapB m hm1 i.val
    rw [sN_eq] at h2
    calc 4 * m * (above (ss m) i).card ≤ 4 * m * (2 * sN (ss m) (i.val + 1)) :=
          Nat.mul_le_mul_left _ h1
      _ = 8 * m * sN (ss m) (i.val + 1) := by ring
      _ ≤ ss m i := h2
  -- a configuration avoiding both events
  obtain ⟨ω, hωA, hωB⟩ : ∃ ω : Omega (ss m), ¬ BadA ω ∧ ¬ BadB (1 / (4 * m)) (24 * m) ω := by
    by_contra hcon
    push Not at hcon
    have hsub : (univ : Finset (Omega (ss m))) ⊆ univ.filter (fun ω => BadA ω) ∪
        univ.filter (fun ω => BadB (1 / (4 * m)) (24 * m) ω) := by
      intro ω _
      by_cases h : BadA ω
      · exact mem_union_left _ (mem_filter.mpr ⟨mem_univ _, h⟩)
      · exact mem_union_right _ (mem_filter.mpr ⟨mem_univ _, hcon ω h⟩)
    have h1 := (card_le_card hsub).trans (card_union_le _ _)
    rw [card_univ] at h1
    have h2 : (Fintype.card (Omega (ss m)) : ℝ) ≤
        ((univ.filter (fun ω : Omega (ss m) => BadA ω)).card : ℝ) +
          ((univ.filter (fun ω : Omega (ss m) => BadB (1 / (4 * m)) (24 * m) ω)).card : ℝ) := by
      exact_mod_cast h1
    linarith
  refine ⟨CC m, ss m, ω, ?_, not_dense4_of_not_badA hdec htail ω hωA⟩
  refine not_colorable_of_not_badB hs (by omega) (1 / (4 * m)) (24 * m) (by positivity)
    (by positivity) ?_ ω hωB
  have hm' : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hcast : ((m - 1 : ℕ) : ℝ) = m - 1 := by rw [Nat.cast_sub hm1, Nat.cast_one]
  have hCm : ((CC m : ℕ) : ℝ) = 64 * m ^ 2 := by unfold CC; push_cast; ring
  have h16 : (64 * m ^ 2 : ℝ) * (1 / (4 * m)) = 16 * m := by field_simp; ring
  rw [hcast, hCm, h16, le_div_iff₀ (by linarith)]
  nlinarith

/-- **Erdős Problem 641**, negative answer: no function `f` makes every finite graph of
chromatic number at least `f k` contain `k` edge-disjoint cycles on the same vertex set. It
already fails for `k = 2`. -/
theorem erdos_641 : Erdos641Negation := by
  rintro ⟨f, hf⟩
  obtain ⟨M, hM⟩ : ∃ M, M = max (f 2) 2 := ⟨_, rfl⟩
  have hM2 : 2 ≤ M := hM ▸ le_max_right _ _
  have hMf : f 2 ≤ M := hM ▸ le_max_left _ _
  obtain ⟨C, s, ω, hcol, hD⟩ := exists_good_graph M hM2
  apply hD
  apply dense4_of_cycles
  refine hf 2 (by norm_num) (Vtx s) (graph ω) ?_
  by_contra hlt
  push Not at hlt
  apply hcol
  rw [← SimpleGraph.chromaticNumber_le_iff_colorable]
  have h1 : (graph ω).chromaticNumber < ((M - 1 : ℕ) : ℕ∞) + 1 := by
    have : ((M - 1 : ℕ) : ℕ∞) + 1 = (M : ℕ∞) := by norm_cast; omega
    rw [this]
    exact lt_of_lt_of_le hlt (by exact_mod_cast hMf)
  exact (ENat.lt_add_one_iff (ENat.natCast_ne_top _)).mp h1

end Erdos641
