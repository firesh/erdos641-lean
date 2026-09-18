import Erdos641.Bounds

/-!
# Concrete layer sizes

For a target number of colours `m ≥ 1`, take `C = 64 m²` layers, `D = 9 + 2C` and
`s i = 2 ^ (D (12^C - 12^i))`. Layer `i + 1` is smaller than layer `i` by the factor
`2 ^ (11 D 12^i)`.
-/

namespace Erdos641

open Finset

/-- A geometric tail: if every layer is at most half the previous one, the layers from `r` on
have total size at most `2 s r`. -/
theorem tail_of_half {C : ℕ} {s : Fin C → ℕ} (h : ∀ j : ℕ, 2 * sN s (j + 1) ≤ sN s j)
    (r : Fin C) : ∑ j ∈ univ.filter (fun j : Fin C => r ≤ j), s j ≤ 2 * s r := by
  have key : ∀ k r : ℕ, C - r = k → ∑ j ∈ Ico r C, sN s j ≤ 2 * sN s r := by
    intro k
    induction k with
    | zero => intro r hr; rw [Ico_eq_empty_of_le (by omega)]; simp
    | succ k ih =>
      intro r hr
      rw [sum_eq_sum_Ico_succ_bot (by omega)]
      have h1 := ih (r + 1) (by omega)
      have h2 := h r
      omega
  have hmap : (univ.filter (fun j : Fin C => r ≤ j)).map Fin.valEmbedding = Ico r.val C := by
    ext n
    simp only [mem_map, mem_filter, mem_univ, true_and, Fin.valEmbedding_apply, mem_Ico]
    constructor
    · rintro ⟨j, hj, rfl⟩; exact ⟨hj, j.isLt⟩
    · rintro ⟨h1, h2⟩; exact ⟨⟨n, h2⟩, h1, rfl⟩
  have hsum : ∑ j ∈ univ.filter (fun j : Fin C => r ≤ j), s j = ∑ j ∈ Ico r.val C, sN s j := by
    rw [← hmap, sum_map]
    simp [sN_eq]
  rw [hsum]
  calc _ ≤ 2 * sN s r.val := key _ _ rfl
    _ = 2 * s r := by rw [sN_eq]

/-- The number of layers. -/
def CC (m : ℕ) : ℕ := 64 * m ^ 2

/-- The growth constant. -/
def DD (m : ℕ) : ℕ := 9 + 2 * CC m

/-- The exponent of the size of layer `i`. -/
def ee (m i : ℕ) : ℕ := DD m * (12 ^ CC m - 12 ^ i)

/-- The layer sizes. -/
def ss (m : ℕ) (i : Fin (CC m)) : ℕ := 2 ^ ee m i

section
variable (m : ℕ)

theorem ss_pos (i : Fin (CC m)) : 0 < ss m i := by unfold ss; positivity

theorem ee_anti {i j : ℕ} (h : i ≤ j) : ee m j ≤ ee m i := by
  unfold ee
  apply Nat.mul_le_mul_left
  have : 12 ^ i ≤ 12 ^ j := Nat.pow_le_pow_right (by norm_num) h
  omega

theorem ss_anti (i j : Fin (CC m)) (h : i ≤ j) : ss m j ≤ ss m i :=
  Nat.pow_le_pow_right (by norm_num) (ee_anti m h)

/-- Consecutive exponents differ by `11 D 12^i`. -/
theorem ee_succ {i : ℕ} (hi : i + 1 ≤ CC m) :
    ee m i = ee m (i + 1) + DD m * (11 * 12 ^ i) := by
  unfold ee
  have h1 : 12 ^ (i + 1) ≤ 12 ^ CC m := Nat.pow_le_pow_right (by norm_num) hi
  have h2 : 12 ^ (i + 1) = 12 * 12 ^ i := by rw [pow_succ]; ring
  rw [← mul_add]
  congr 1
  omega

theorem sN_ss (i : ℕ) : sN (ss m) i = if i < CC m then 2 ^ ee m i else 0 := by
  unfold sN ss; split_ifs <;> rfl

theorem one_le_CC (hm : 1 ≤ m) : 1 ≤ CC m := by
  unfold CC; nlinarith

theorem m_le_CC (hm : 1 ≤ m) : m ≤ CC m := by
  unfold CC; nlinarith

theorem eight_m_le (hm : 1 ≤ m) : 8 * m ≤ 2 ^ (11 * DD m) := by
  have h1 : m < 2 ^ m := Nat.lt_two_pow_self
  have h2 := m_le_CC m hm
  calc 8 * m ≤ 2 ^ 3 * 2 ^ m := by omega
    _ = 2 ^ (3 + m) := by rw [pow_add]
    _ ≤ 2 ^ (11 * DD m) := Nat.pow_le_pow_right (by norm_num) (by unfold DD; omega)

/-- Consecutive layers shrink by a factor of at least `8m`. -/
theorem ss_gapB (hm : 1 ≤ m) (i : ℕ) : 8 * m * sN (ss m) (i + 1) ≤ sN (ss m) i := by
  rw [sN_ss, sN_ss]
  by_cases h1 : i + 1 < CC m
  · simp only [h1, (by omega : i < CC m), ↓reduceIte]
    rw [ee_succ m (by omega : i + 1 ≤ CC m), pow_add]
    have h3 : 8 * m ≤ 2 ^ (DD m * (11 * 12 ^ i)) := by
      refine (eight_m_le m hm).trans (Nat.pow_le_pow_right (by norm_num) ?_)
      have : 1 ≤ 12 ^ i := Nat.one_le_pow _ _ (by norm_num)
      nlinarith
    calc 8 * m * 2 ^ ee m (i + 1) ≤ 2 ^ (DD m * (11 * 12 ^ i)) * 2 ^ ee m (i + 1) :=
          Nat.mul_le_mul_right _ h3
      _ = 2 ^ ee m (i + 1) * 2 ^ (DD m * (11 * 12 ^ i)) := mul_comm _ _
  · simp [h1]

theorem ss_tail (hm : 1 ≤ m) (r : Fin (CC m)) :
    ∑ j ∈ univ.filter (fun j : Fin (CC m) => r ≤ j), ss m j ≤ 2 * ss m r :=
  tail_of_half (fun j => (Nat.mul_le_mul_right _ (by omega : 2 ≤ 8 * m)).trans
    (ss_gapB m hm j)) r

theorem const_le : (144 * CC m ^ 2) ^ 10 * (3000 * CC m) ≤ 2 ^ (11 * DD m) := by
  have hC : CC m ≤ 2 ^ CC m := Nat.lt_two_pow_self.le
  calc (144 * CC m ^ 2) ^ 10 * (3000 * CC m)
      ≤ (2 ^ 8 * (2 ^ CC m) ^ 2) ^ 10 * (2 ^ 12 * 2 ^ CC m) := by
        gcongr <;> norm_num
    _ = 2 ^ (92 + 21 * CC m) := by ring
    _ ≤ 2 ^ (11 * DD m) := Nat.pow_le_pow_right (by norm_num) (by unfold DD; omega)

/-- The gap needed by the locally dense union bound. -/
theorem ss_gapA (a : Fin (CC m)) (ha : 0 < a.val) :
    (144 * CC m ^ 2 * ss m ⟨0, by omega⟩) ^ 10 * (3000 * CC m * ss m a) ≤
      ss m ⟨a.val - 1, by omega⟩ ^ 11 := by
  unfold ss
  have hexp : 11 * DD m + (10 * ee m 0 + ee m a) ≤ 11 * ee m (a.val - 1) := by
    unfold ee
    have hP1 : 1 ≤ 12 ^ (a.val - 1) := Nat.one_le_pow _ _ (by norm_num)
    have hPa : 12 ^ a.val = 12 * 12 ^ (a.val - 1) := by
      rw [← pow_succ']; congr 1; omega
    have hX : 12 ^ a.val ≤ 12 ^ CC m := Nat.pow_le_pow_right (by norm_num) a.isLt.le
    have key : 11 + (10 * (12 ^ CC m - 1) + (12 ^ CC m - 12 ^ a.val)) ≤
        11 * (12 ^ CC m - 12 ^ (a.val - 1)) := by omega
    calc 11 * DD m + (10 * (DD m * (12 ^ CC m - 12 ^ 0)) + DD m * (12 ^ CC m - 12 ^ a.val))
        = DD m * (11 + (10 * (12 ^ CC m - 1) + (12 ^ CC m - 12 ^ a.val))) := by
          rw [pow_zero]; ring
      _ ≤ DD m * (11 * (12 ^ CC m - 12 ^ (a.val - 1))) := Nat.mul_le_mul_left _ key
      _ = 11 * (DD m * (12 ^ CC m - 12 ^ (a.val - 1))) := by ring
  calc (144 * CC m ^ 2 * 2 ^ ee m 0) ^ 10 * (3000 * CC m * 2 ^ ee m a)
      = (144 * CC m ^ 2) ^ 10 * (3000 * CC m) * 2 ^ (10 * ee m 0 + ee m a) := by ring
    _ ≤ 2 ^ (11 * DD m) * 2 ^ (10 * ee m 0 + ee m a) := Nat.mul_le_mul_right _ (const_le m)
    _ = 2 ^ (11 * DD m + (10 * ee m 0 + ee m a)) := by rw [← pow_add]
    _ ≤ 2 ^ (11 * ee m (a.val - 1)) := Nat.pow_le_pow_right (by norm_num) hexp
    _ = (2 ^ ee m (a.val - 1)) ^ 11 := by rw [← pow_mul, mul_comm]

end

end Erdos641
