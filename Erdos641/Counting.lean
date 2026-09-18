import Erdos641.Layered

/-!
# Counting constrained configurations

The "probability" of an event is its number of configurations divided by `card (Omega s)`.
For an event of the form `∀ k ∈ K, ω k ∈ A k` the count is an explicit product.
-/

namespace Erdos641

open Finset

variable {C : ℕ} {s : Fin C → ℕ}

theorem card_omega : Fintype.card (Omega s) = ∏ k : Key s, s k.1.1.2 := by
  simp [Fintype.card_pi]

theorem card_constrained (K : Finset (Key s)) (A : ∀ k : Key s, Finset (Fin (s k.1.1.2))) :
    (univ.filter (fun ω : Omega s => ∀ k ∈ K, ω k ∈ A k)).card =
      ∏ k, (if k ∈ K then (A k).card else s k.1.1.2) := by
  classical
  have : univ.filter (fun ω : Omega s => ∀ k ∈ K, ω k ∈ A k) =
      Fintype.piFinset (fun k => if k ∈ K then A k else univ) := by
    ext ω
    simp only [mem_filter, mem_univ, true_and, Fintype.mem_piFinset]
    constructor
    · intro h k; split_ifs with hk
      · exact h k hk
      · exact mem_univ _
    · intro h k hk; have := h k; simpa [hk] using this
  rw [this, Fintype.card_piFinset]
  refine prod_congr rfl (fun k _ => ?_)
  split_ifs <;> simp

/-- The count of a constrained event, as a fraction of all configurations. -/
theorem card_constrained_real (hs : ∀ i, 0 < s i) (K : Finset (Key s))
    (A : ∀ k : Key s, Finset (Fin (s k.1.1.2))) :
    ((univ.filter (fun ω : Omega s => ∀ k ∈ K, ω k ∈ A k)).card : ℝ) =
      (Fintype.card (Omega s) : ℝ) * ∏ k ∈ K, ((A k).card : ℝ) / s k.1.1.2 := by
  classical
  rw [card_constrained, card_omega]
  push_cast
  have hpos : ∀ k : Key s, (s k.1.1.2 : ℝ) ≠ 0 := fun k => by
    have := hs k.1.1.2; positivity
  have : ∀ k : Key s, (if k ∈ K then ((A k).card : ℝ) else (s k.1.1.2 : ℝ)) =
      (s k.1.1.2 : ℝ) * (if k ∈ K then ((A k).card : ℝ) / s k.1.1.2 else 1) := by
    intro k
    split_ifs
    · rw [mul_comm, div_mul_cancel₀ _ (hpos k)]
    · ring
  simp_rw [this, prod_mul_distrib]
  congr 1
  rw [prod_ite_mem, univ_inter]

/-- Monotonicity: an event contained in a constrained event. -/
theorem card_le_constrained (hs : ∀ i, 0 < s i) (P : Omega s → Prop) [DecidablePred P]
    (K : Finset (Key s)) (A : ∀ k : Key s, Finset (Fin (s k.1.1.2)))
    (h : ∀ ω, P ω → ∀ k ∈ K, ω k ∈ A k) :
    ((univ.filter P).card : ℝ) ≤
      (Fintype.card (Omega s) : ℝ) * ∏ k ∈ K, ((A k).card : ℝ) / s k.1.1.2 := by
  rw [← card_constrained_real hs K A]
  exact_mod_cast card_le_card (fun ω hω => by
    simp only [mem_filter, mem_univ, true_and] at hω ⊢; exact h ω hω)

end Erdos641
