import Erdos641.Numeric
import Erdos641.Union

/-!
# The two union bounds are small

Every term of either union bound is at most `(1 / (8 C)) ^ x`. A geometric sum over `x ≥ 1` is
then at most `2 / (8 C)`, and summing over the `C` layers gives `1 / 4`.
-/

namespace Erdos641

open Finset

theorem fA_eq (x : ℕ) : fA x = x + (x + 9) / 10 := by unfold fA; omega

/-- One term of the locally dense union bound. -/
theorem termA_le (C N S sa x : ℕ) (hC : 1 ≤ C) (hS : 0 < S) (hNS : S ≤ N) (hx : 1 ≤ x)
    (hxa : x ≤ 1000 * sa) (hgap : (72 * C ^ 2 * N) ^ 10 * (3000 * C * sa) ≤ S ^ 11) :
    (N.choose x : ℝ) * ((x * C).choose (fA x) : ℝ) * ((x : ℝ) / S) ^ fA x ≤
      (1 / (8 * C : ℝ)) ^ x := by
  set z := (x + 9) / 10 with hz
  have hy : fA x = x + z := fA_eq x
  have hx10 : x ≤ 10 * z := by omega
  have hxpos : (0 : ℝ) < x := by exact_mod_cast hx
  have hSpos : (0 : ℝ) < S := by exact_mod_cast hS
  have hC1 : (1 : ℝ) ≤ C := by exact_mod_cast hC
  have hCpos : (0 : ℝ) < C := by linarith
  have h1 : (N.choose x : ℝ) ≤ (3 * N / x) ^ x := choose_le_three N x hx
  have h2 : ((x * C).choose (fA x) : ℝ) ≤ (3 * C) ^ fA x := by
    refine (choose_le_three (x * C) (fA x) (by omega)).trans
      (pow_le_pow_left₀ (by positivity) ?_ _)
    rw [div_le_iff₀ (by exact_mod_cast (show 0 < fA x by omega))]
    have : (x : ℝ) ≤ (fA x : ℕ) := by exact_mod_cast (show x ≤ fA x by omega)
    push_cast
    nlinarith
  set κ : ℝ := 72 * C ^ 2 * N / S with hκ
  set ρ : ℝ := 3000 * C * sa / S with hρ
  have hκ1 : 1 ≤ κ := by
    rw [hκ, le_div_iff₀ hSpos, one_mul]
    have hN' : (S : ℝ) ≤ N := by exact_mod_cast hNS
    have hC2 : (1 : ℝ) ≤ C ^ 2 := one_le_pow₀ hC1
    have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    nlinarith
  have hρ0 : 0 ≤ ρ := by positivity
  have hκρ : κ ^ 10 * ρ ≤ 1 := by
    rw [hκ, hρ, div_pow, div_mul_div_comm, div_le_one (by positivity)]
    have : ((72 * C ^ 2 * N) ^ 10 * (3000 * C * sa) : ℝ) ≤ (S : ℝ) ^ 11 := by
      exact_mod_cast hgap
    calc _ ≤ (S : ℝ) ^ 11 := this
      _ = (S : ℝ) ^ 10 * S := by ring
  have hv : 3 * C * x / S ≤ ρ := by
    rw [hρ]
    apply div_le_div_of_nonneg_right _ hSpos.le
    have : (x : ℝ) ≤ 1000 * sa := by exact_mod_cast hxa
    nlinarith
  have hw0 : (0 : ℝ) ≤ 1 / (8 * C) := by positivity
  calc (N.choose x : ℝ) * ((x * C).choose (fA x) : ℝ) * ((x : ℝ) / S) ^ fA x
      ≤ (3 * N / x) ^ x * (3 * C) ^ fA x * ((x : ℝ) / S) ^ fA x :=
        mul_le_mul_of_nonneg_right (mul_le_mul h1 h2 (by positivity) (by positivity))
          (by positivity)
    _ = (3 * N / x) ^ x * (3 * C * x / S) ^ x * (3 * C * x / S) ^ z := by
        rw [hy]; ring
    _ = (1 / (8 * C) * κ) ^ x * (3 * C * x / S) ^ z := by
        rw [← mul_pow]
        congr 2
        have hx0 : (x : ℝ) ≠ 0 := hxpos.ne'
        have hS0 : (S : ℝ) ≠ 0 := hSpos.ne'
        have hC0 : (C : ℝ) ≠ 0 := hCpos.ne'
        rw [hκ]; field_simp; ring
    _ ≤ (1 / (8 * C) * κ) ^ x * ρ ^ z :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hv z)
          (pow_nonneg (mul_nonneg hw0 (by linarith)) x)
    _ = (1 / (8 * C)) ^ x * κ ^ x * ρ ^ z := by rw [mul_pow]
    _ ≤ (1 / (8 * C)) ^ x * κ ^ (10 * z) * ρ ^ z :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hκ1 hx10) (pow_nonneg hw0 x))
          (pow_nonneg hρ0 z)
    _ = (1 / (8 * C)) ^ x * (κ ^ 10 * ρ) ^ z := by rw [pow_mul, mul_pow]; ring
    _ ≤ (1 / (8 * C)) ^ x * 1 :=
        mul_le_mul_of_nonneg_left
          (pow_le_one₀ (mul_nonneg (pow_nonneg (by linarith) 10) hρ0) hκρ) (pow_nonneg hw0 x)
    _ = (1 / (8 * C)) ^ x := mul_one _

/-- The locally dense union bound is at most `1 / 4`. -/
theorem sumA_le {C : ℕ} {s : Fin C → ℕ} (hC : 1 ≤ C) (hs : ∀ i, 0 < s i) (N : ℕ)
    (hN : ∀ i, s i ≤ N)
    (hgap : ∀ a : Fin C, 0 < a.val →
      (72 * C ^ 2 * N) ^ 10 * (3000 * C * s a) ≤ s ⟨a.val - 1, by omega⟩ ^ 11) :
    ∑ a ∈ univ.filter (fun a : Fin C => 0 < a.val), ∑ x ∈ Icc 1 (1000 * s a),
      (N.choose x : ℝ) * ((x * C).choose (fA x) : ℝ) *
        ((x : ℝ) / s ⟨a.val - 1, by omega⟩) ^ fA x ≤ 1 / 4 := by
  have hC' : (1 : ℝ) ≤ C := by exact_mod_cast hC
  have hw0 : (0 : ℝ) ≤ 1 / (8 * C) := by positivity
  have hw : (1 / (8 * C : ℝ)) ≤ 1 / 2 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
  calc _ ≤ ∑ a ∈ univ.filter (fun a : Fin C => 0 < a.val), ∑ x ∈ Icc 1 (1000 * s a),
          (1 / (8 * C : ℝ)) ^ x := by
        refine sum_le_sum (fun a ha => sum_le_sum (fun x hx => ?_))
        have ha' : 0 < a.val := (mem_filter.mp ha).2
        obtain ⟨hx1, hx2⟩ := mem_Icc.mp hx
        exact termA_le C N _ (s a) x hC (hs _) (hN _) hx1 hx2 (hgap a ha')
    _ ≤ ∑ _a ∈ univ.filter (fun a : Fin C => 0 < a.val), 2 * (1 / (8 * C : ℝ)) :=
        sum_le_sum (fun a _ => sum_geom_le _ hw0 hw _ (fun x hx => (mem_Icc.mp hx).1))
    _ ≤ ∑ _a : Fin C, 2 * (1 / (8 * C : ℝ)) :=
        sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ => by positivity)
    _ = 1 / 4 := by
        rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]; field_simp; ring

/-- One term of the independent-set union bound, with `δ = 1 / (4m)`, `γ = 24m` and
`C = 64 m²`. -/
theorem termB_le (m S A t : ℕ) (hm : 1 ≤ m) (hS : 0 < S) (hA : 4 * m * A ≤ S)
    (ht : 1 / (4 * m : ℝ) * S ≤ t) :
    (S.choose t : ℝ) * 2 ^ A * Real.exp (-(t * (24 * m : ℝ))) ≤
      (1 / (8 * (64 * m ^ 2)) : ℝ) ^ t := by
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hmpos : (0 : ℝ) < m := by linarith
  have hSpos : (0 : ℝ) < S := by exact_mod_cast hS
  have hSt : (S : ℝ) ≤ 4 * m * t := by
    rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ (by positivity)] at ht; linarith
  have htpos : 0 < t := by
    have : (0 : ℝ) < t := by nlinarith
    exact_mod_cast this
  have hAt : A ≤ t := by
    have h1 : (4 * m * A : ℝ) ≤ S := by exact_mod_cast hA
    have : (A : ℝ) ≤ t := by nlinarith
    exact_mod_cast this
  have h1 : (S.choose t : ℝ) ≤ (12 * m) ^ t := by
    refine (choose_le_three S t htpos).trans (pow_le_pow_left₀ (by positivity) ?_ t)
    rw [div_le_iff₀ (by exact_mod_cast htpos)]; linarith
  have h2 : (2 : ℝ) ^ A ≤ 2 ^ t := pow_le_pow_right₀ (by norm_num) hAt
  have h3 : Real.exp (-(t * (24 * m : ℝ))) = Real.exp (-(24 * m)) ^ t := by
    rw [← Real.exp_nat_mul]; ring_nf
  have hkey : 24 * m * Real.exp (-(24 * m)) ≤ 1 / (8 * (64 * m ^ 2)) := by
    have hexp : (24 * m : ℝ) ^ 4 / 24 ≤ Real.exp (24 * m) := by
      have := Real.pow_div_factorial_le_exp (x := 24 * m) (by positivity) 4
      simpa [Nat.factorial] using this
    rw [Real.exp_neg, ← div_eq_mul_inv, div_le_div_iff₀ (Real.exp_pos _) (by positivity)]
    nlinarith [mul_nonneg (pow_nonneg hmpos.le 3) (sub_nonneg.mpr hm1)]
  calc (S.choose t : ℝ) * 2 ^ A * Real.exp (-(t * (24 * m : ℝ)))
      ≤ (12 * m) ^ t * 2 ^ t * Real.exp (-(24 * m)) ^ t := by
        rw [h3]
        exact mul_le_mul_of_nonneg_right (mul_le_mul h1 h2 (by positivity) (by positivity))
          (by positivity)
    _ = (24 * m * Real.exp (-(24 * m))) ^ t := by rw [← mul_pow, ← mul_pow]; ring_nf
    _ ≤ (1 / (8 * (64 * m ^ 2))) ^ t := pow_le_pow_left₀ (by positivity) hkey t

/-- The independent-set union bound is at most `1 / 4`. -/
theorem sumB_le {m : ℕ} (hm : 1 ≤ m) {C : ℕ} (hC : C = 64 * m ^ 2) {s : Fin C → ℕ}
    (hs : ∀ i, 0 < s i) (A : Fin C → ℕ) (hA : ∀ i, 4 * m * A i ≤ s i) :
    ∑ i : Fin C, ∑ t ∈ (range (s i + 1)).filter (fun t : ℕ => 1 / (4 * m : ℝ) * s i ≤ (t : ℝ)),
      ((s i).choose t : ℝ) * 2 ^ A i * Real.exp (-(t * (24 * m : ℝ))) ≤ 1 / 4 := by
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  set w : ℝ := 1 / (8 * (64 * m ^ 2)) with hw
  have hw0 : 0 ≤ w := by positivity
  have hw2 : w ≤ 1 / 2 := by
    rw [hw, div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
  calc _ ≤ ∑ i : Fin C, ∑ t ∈ (range (s i + 1)).filter
          (fun t : ℕ => 1 / (4 * m : ℝ) * s i ≤ (t : ℝ)), w ^ t := by
        refine sum_le_sum (fun i _ => sum_le_sum (fun t ht => ?_))
        exact termB_le m (s i) (A i) t hm (hs i) (hA i) (mem_filter.mp ht).2
    _ ≤ ∑ _i : Fin C, 2 * w := by
        refine sum_le_sum (fun i _ => sum_geom_le w hw0 hw2 _ (fun t ht => ?_))
        have h := (mem_filter.mp ht).2
        have hsi : (0 : ℝ) < s i := by exact_mod_cast hs i
        have : (0 : ℝ) < t := lt_of_lt_of_le (by positivity) h
        have : 0 < t := by exact_mod_cast this
        omega
    _ = 1 / 4 := by
        rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, hC, hw]; push_cast
        field_simp; ring

end Erdos641
