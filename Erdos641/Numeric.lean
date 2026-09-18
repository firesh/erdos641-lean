import Mathlib

/-!
# Numerical estimates for the union bounds
-/

namespace Erdos641

open Finset

theorem exp_le_three_pow (x : ℕ) : Real.exp x ≤ 3 ^ x := by
  rw [← Real.exp_one_pow]
  exact pow_le_pow_left₀ (Real.exp_pos 1).le
    (le_of_lt (lt_trans Real.exp_one_lt_d9 (by norm_num))) x

/-- `C(N, x) ≤ (3N/x)^x`. -/
theorem choose_le_three (N x : ℕ) (hx : 0 < x) : (N.choose x : ℝ) ≤ (3 * N / x) ^ x := by
  have h1 : (N.choose x : ℝ) ≤ (N : ℝ) ^ x / x.factorial := Nat.choose_le_pow_div x N
  have h2 : (x : ℝ) ^ x / x.factorial ≤ Real.exp x :=
    Real.pow_div_factorial_le_exp (x := (x : ℝ)) (by positivity) x
  have hf : (0 : ℝ) < x.factorial := by exact_mod_cast Nat.factorial_pos x
  have hxpos : (0 : ℝ) < (x : ℝ) ^ x := by positivity
  calc (N.choose x : ℝ) ≤ (N : ℝ) ^ x / x.factorial := h1
    _ ≤ (N : ℝ) ^ x * (3 ^ x / (x : ℝ) ^ x) := by
      rw [div_le_iff₀ hf, mul_assoc]
      have : (x : ℝ) ^ x ≤ 3 ^ x * x.factorial := by
        have := h2.trans (exp_le_three_pow x)
        rwa [div_le_iff₀ hf] at this
      have h3 : 1 ≤ 3 ^ x / (x : ℝ) ^ x * x.factorial := by
        rw [div_mul_eq_mul_div, le_div_iff₀ hxpos, one_mul]; exact this
      calc (N : ℝ) ^ x = (N : ℝ) ^ x * 1 := (mul_one _).symm
        _ ≤ _ := mul_le_mul_of_nonneg_left h3 (by positivity)
    _ = (3 * N / x) ^ x := by rw [div_pow, mul_pow]; ring

/-- A geometric tail. -/
theorem sum_geom_le (q : ℝ) (hq0 : 0 ≤ q) (hq : q ≤ 1 / 2) (S : Finset ℕ) (hS : ∀ x ∈ S, 1 ≤ x) :
    ∑ x ∈ S, q ^ x ≤ 2 * q := by
  classical
  obtain ⟨M, hM⟩ : ∃ M, S ⊆ Finset.Icc 1 M :=
    ⟨S.sup id, fun x hx => Finset.mem_Icc.mpr ⟨hS x hx, Finset.le_sup (f := id) hx⟩⟩
  calc ∑ x ∈ S, q ^ x ≤ ∑ x ∈ Finset.Icc 1 M, q ^ x :=
        sum_le_sum_of_subset_of_nonneg hM (fun _ _ _ => by positivity)
    _ = q * ∑ x ∈ Finset.range M, q ^ x := by
        rw [mul_sum]
        rw [show Finset.Icc 1 M = (Finset.range M).map ⟨(· + 1), add_left_injective 1⟩ by
          ext x
          simp only [mem_Icc, mem_map, mem_range, Function.Embedding.coeFn_mk]
          constructor
          · rintro ⟨h1, h2⟩; exact ⟨x - 1, by omega, by omega⟩
          · rintro ⟨a, ha, rfl⟩; omega]
        rw [sum_map]; refine sum_congr rfl (fun x _ => ?_); simp [pow_succ]; ring
    _ ≤ q * 2 := by
        refine mul_le_mul_of_nonneg_left ?_ hq0
        rcases eq_or_lt_of_le hq0 with h | h
        · rw [← h]; cases M <;> simp
        · have h1q : q < 1 := by linarith
          rw [geom_sum_eq h1q.ne]
          rw [div_le_iff_of_neg (by linarith)]
          have : 0 ≤ q ^ M := by positivity
          nlinarith
    _ = 2 * q := by ring

end Erdos641
