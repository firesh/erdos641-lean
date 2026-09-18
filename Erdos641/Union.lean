import Erdos641.EventA
import Erdos641.Indep
import Erdos641.Sparse

/-!
# Union bounds for the two bad events
-/

namespace Erdos641

open Finset

variable {C : ℕ} {s : Fin C → ℕ}

/-- Union bound. The decidability instances are implicit so that they are unified with the
goal instead of being synthesized. -/
theorem card_exists_le {α ι : Type*} [Fintype α] (P : Finset ι) (E : ι → α → Prop)
    {dE : ∀ p, DecidablePred (E p)} {dQ : DecidablePred (fun a => ∃ p ∈ P, E p a)} :
    ((@Finset.filter α (fun a => ∃ p ∈ P, E p a) dQ univ).card : ℝ) ≤
      ∑ p ∈ P, ((@Finset.filter α (E p) (dE p) univ).card : ℝ) := by
  classical
  have : @Finset.filter α (fun a => ∃ p ∈ P, E p a) dQ univ ⊆
      P.biUnion (fun p => @Finset.filter α (E p) (dE p) univ) := by
    intro a ha
    obtain ⟨p, hp, h⟩ := (mem_filter.mp ha).2
    exact mem_biUnion.mpr ⟨p, hp, mem_filter.mpr ⟨mem_univ _, h⟩⟩
  exact_mod_cast (card_le_card this).trans card_biUnion_le

theorem sum_by_card {α : Type*} [Fintype α] [DecidableEq α] (Xs : Finset (Finset α)) (M : ℕ)
    (hXs : ∀ X ∈ Xs, 1 ≤ X.card ∧ X.card ≤ M) (g : ℕ → ℝ) (hg : ∀ x, 0 ≤ g x) :
    ∑ X ∈ Xs, g X.card ≤ ∑ x ∈ Icc 1 M, ((Fintype.card α).choose x : ℝ) * g x := by
  classical
  have hsub : Xs ⊆ (Icc 1 M).biUnion (fun x => powersetCard x (univ : Finset α)) := by
    intro X hX
    obtain ⟨h1, h2⟩ := hXs X hX
    exact mem_biUnion.mpr ⟨X.card, mem_Icc.mpr ⟨h1, h2⟩,
      mem_powersetCard.mpr ⟨subset_univ _, rfl⟩⟩
  calc ∑ X ∈ Xs, g X.card
      ≤ ∑ X ∈ (Icc 1 M).biUnion (fun x => powersetCard x (univ : Finset α)), g X.card :=
        sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => hg _)
    _ = ∑ x ∈ Icc 1 M, ∑ X ∈ powersetCard x (univ : Finset α), g X.card := by
        rw [sum_biUnion]
        intro x _ y _ hxy
        rw [Function.onFun, disjoint_left]
        intro X hX hY
        exact hxy ((mem_powersetCard.mp hX).2.symm.trans (mem_powersetCard.mp hY).2)
    _ = ∑ x ∈ Icc 1 M, ((Fintype.card α).choose x : ℝ) * g x := by
        refine sum_congr rfl (fun x _ => ?_)
        rw [sum_congr rfl (fun X hX => by rw [(mem_powersetCard.mp hX).2]), sum_const,
          card_powersetCard, card_univ, nsmul_eq_mul]

/-- Number of required edges for a set of size `x`: `⌈11x/10⌉`. -/
def fA (x : ℕ) : ℕ := (11 * x + 9) / 10

/-- The locally dense bad event. -/
def BadA (ω : Omega s) : Prop :=
  ∃ a ∈ univ.filter (fun a : Fin C => 0 < a.val),
    ∃ X ∈ (univ : Finset (Vtx s)).powerset.filter
        (fun X => (∀ x ∈ X, x.1 < a) ∧ 1 ≤ X.card ∧ X.card ≤ 1000 * s a),
      ∃ Q ∈ powersetCard (fA X.card) (keysIn a X), ∀ k ∈ Q, ω k ∈ posIn X k

/-- Vertices of layer `i` and of the layers above `i`. -/
def layer (s : Fin C → ℕ) (i : Fin C) : Finset (Vtx s) := by
  classical exact univ.filter (fun v => v.1 = i)
def above (s : Fin C → ℕ) (i : Fin C) : Finset (Vtx s) := by
  classical exact univ.filter (fun v => i < v.1)

theorem mem_layer {i : Fin C} {v : Vtx s} : v ∈ layer s i ↔ v.1 = i := by
  unfold layer; simp

theorem mem_above {i : Fin C} {v : Vtx s} : v ∈ above s i ↔ i < v.1 := by
  unfold above; simp

theorem card_layer_eq (i : Fin C) : (layer s i).card = s i := by
  classical
  rw [← card_layer s i]
  congr 1

theorem card_above_eq (i : Fin C) :
    (above s i).card = ∑ j ∈ univ.filter (fun j : Fin C => i < j), s j := by
  classical
  have : above s i = (univ.filter (fun j : Fin C => i < j)).sigma (fun _ => univ) := by
    ext v; rw [mem_above]; simp
  rw [this, card_sigma]; simp

/-- The heavy independent set bad event. -/
def BadB (δ γ : ℝ) (ω : Omega s) : Prop :=
  ∃ i ∈ (univ : Finset (Fin C)),
    ∃ T ∈ (layer s i).powerset.filter (fun T => δ * s i ≤ T.card),
      ∃ J ∈ (above s i).powerset.filter
          (fun J => γ ≤ ∑ j ∈ univ.filter (fun j : Fin C => i < j), dens s J j),
        ∀ x ∈ T, ∀ y ∈ J, ¬ (graph ω).Adj x y

section
variable (hs : ∀ i, 0 < s i) (hdec : ∀ i j : Fin C, i ≤ j → s j ≤ s i)
include hs

open Classical in
theorem card_badA_le (hdec : ∀ i j : Fin C, i ≤ j → s j ≤ s i) :
    ((univ.filter (fun ω : Omega s => BadA ω)).card : ℝ) ≤
      (Fintype.card (Omega s) : ℝ) *
        ∑ a ∈ univ.filter (fun a : Fin C => 0 < a.val),
          ∑ x ∈ Icc 1 (1000 * s a),
            ((Fintype.card (Vtx s)).choose x : ℝ) * ((x * C).choose (fA x) : ℝ) *
              ((x : ℝ) / s ⟨a.val - 1, by omega⟩) ^ fA x := by
  set Ω := (Fintype.card (Omega s) : ℝ)
  have hΩ : 0 ≤ Ω := by positivity
  calc ((univ.filter (fun ω : Omega s => BadA ω)).card : ℝ)
      ≤ ∑ a ∈ univ.filter (fun a : Fin C => 0 < a.val),
          ((univ.filter (fun ω : Omega s => ∃ X ∈ (univ : Finset (Vtx s)).powerset.filter
            (fun X => (∀ x ∈ X, x.1 < a) ∧ 1 ≤ X.card ∧ X.card ≤ 1000 * s a),
              ∃ Q ∈ powersetCard (fA X.card) (keysIn a X), ∀ k ∈ Q, ω k ∈ posIn X k)).card : ℝ) :=
        card_exists_le _ _
    _ ≤ ∑ a ∈ univ.filter (fun a : Fin C => 0 < a.val),
          ∑ X ∈ (univ : Finset (Vtx s)).powerset.filter
            (fun X => (∀ x ∈ X, x.1 < a) ∧ 1 ≤ X.card ∧ X.card ≤ 1000 * s a),
          ∑ Q ∈ powersetCard (fA X.card) (keysIn a X),
            ((univ.filter (fun ω : Omega s => ∀ k ∈ Q, ω k ∈ posIn X k)).card : ℝ) :=
        sum_le_sum (fun a _ => (card_exists_le _ _ (dE := fun _ => Classical.decPred _)).trans
          (sum_le_sum (fun X _ => card_exists_le _ _)))
    _ ≤ ∑ a ∈ univ.filter (fun a : Fin C => 0 < a.val),
          ∑ X ∈ (univ : Finset (Vtx s)).powerset.filter
            (fun X => (∀ x ∈ X, x.1 < a) ∧ 1 ≤ X.card ∧ X.card ≤ 1000 * s a),
          Ω * (((X.card * C).choose (fA X.card) : ℝ) *
            ((X.card : ℝ) / s ⟨a.val - 1, by omega⟩) ^ fA X.card) := by
        refine sum_le_sum (fun a ha => sum_le_sum (fun X hX => ?_))
        have ha' : 0 < a.val := (mem_filter.mp ha).2
        calc ∑ Q ∈ powersetCard (fA X.card) (keysIn a X),
              ((univ.filter (fun ω : Omega s => ∀ k ∈ Q, ω k ∈ posIn X k)).card : ℝ)
            ≤ ∑ Q ∈ powersetCard (fA X.card) (keysIn a X),
                Ω * ((X.card : ℝ) / s ⟨a.val - 1, by omega⟩) ^ fA X.card := by
              refine sum_le_sum (fun Q hQ => ?_)
              obtain ⟨hQs, hQc⟩ := mem_powersetCard.mp hQ
              have := eventA_card hs hdec a ha' X Q hQs
              rwa [hQc] at this
          _ = ((keysIn a X).card.choose (fA X.card) : ℝ) *
                (Ω * ((X.card : ℝ) / s ⟨a.val - 1, by omega⟩) ^ fA X.card) := by
              rw [sum_const, card_powersetCard, nsmul_eq_mul]
          _ ≤ ((X.card * C).choose (fA X.card) : ℝ) *
                (Ω * ((X.card : ℝ) / s ⟨a.val - 1, by omega⟩) ^ fA X.card) := by
              refine mul_le_mul_of_nonneg_right ?_ (by positivity)
              exact_mod_cast Nat.choose_le_choose _ (card_keysIn a X)
          _ = _ := by ring
    _ ≤ ∑ a ∈ univ.filter (fun a : Fin C => 0 < a.val),
          ∑ x ∈ Icc 1 (1000 * s a), ((Fintype.card (Vtx s)).choose x : ℝ) *
            (Ω * (((x * C).choose (fA x) : ℝ) * ((x : ℝ) / s ⟨a.val - 1, by omega⟩) ^ fA x)) := by
        refine sum_le_sum (fun a ha => ?_)
        exact sum_by_card _ _ (fun X hX => ⟨(mem_filter.mp hX).2.2.1, (mem_filter.mp hX).2.2.2⟩)
          (fun x => Ω * (((x * C).choose (fA x) : ℝ) *
            ((x : ℝ) / s ⟨a.val - 1, by have := (mem_filter.mp ha).2; omega⟩) ^ fA x))
          (fun x => by positivity)
    _ = _ := by
        rw [mul_sum]; refine sum_congr rfl (fun a _ => ?_)
        rw [mul_sum]; refine sum_congr rfl (fun x _ => ?_); ring

open Classical in
theorem card_badB_le (δ γ : ℝ) :
    ((univ.filter (fun ω : Omega s => BadB δ γ ω)).card : ℝ) ≤
      (Fintype.card (Omega s) : ℝ) *
        ∑ i : Fin C, ∑ t ∈ (range (s i + 1)).filter (fun t : ℕ => δ * s i ≤ (t : ℝ)),
          ((s i).choose t : ℝ) * 2 ^ (above s i).card * Real.exp (-(t * γ)) := by
  set Ω := (Fintype.card (Omega s) : ℝ)
  have hΩ : 0 ≤ Ω := by positivity
  calc ((univ.filter (fun ω : Omega s => BadB δ γ ω)).card : ℝ)
      ≤ ∑ i : Fin C, ∑ T ∈ (layer s i).powerset.filter (fun T => δ * s i ≤ T.card),
          ∑ J ∈ (above s i).powerset.filter
            (fun J => γ ≤ ∑ j ∈ univ.filter (fun j : Fin C => i < j), dens s J j),
          ((univ.filter (fun ω : Omega s => ∀ x ∈ T, ∀ y ∈ J, ¬ (graph ω).Adj x y)).card : ℝ) :=
        (card_exists_le _ _ (dE := fun _ => Classical.decPred _)).trans
          (sum_le_sum (fun i _ => (card_exists_le _ _ (dE := fun _ => Classical.decPred _)).trans
            (sum_le_sum (fun T _ => card_exists_le _ _))))
    _ ≤ ∑ i : Fin C, ∑ T ∈ (layer s i).powerset.filter (fun T => δ * s i ≤ T.card),
          ∑ _J ∈ (above s i).powerset, Ω * Real.exp (-(T.card * γ)) := by
        refine sum_le_sum (fun i _ => sum_le_sum (fun T hT => ?_))
        have hTi : ∀ x ∈ T, x.1 = i := fun x hx =>
          mem_layer.mp ((mem_powerset.mp (mem_filter.mp hT).1) hx)
        refine (sum_le_sum (fun J hJ => ?_)).trans
          (sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ => by positivity))
        refine (eventB_card hs i T J hTi).trans (mul_le_mul_of_nonneg_left ?_ hΩ)
        apply Real.exp_le_exp.mpr
        have hJ' := (mem_filter.mp hJ).2
        have hT0 : (0 : ℝ) ≤ T.card := by positivity
        nlinarith
    _ = ∑ i : Fin C, ∑ T ∈ (layer s i).powerset.filter (fun T => δ * s i ≤ T.card),
          Ω * (2 ^ (above s i).card * Real.exp (-(T.card * γ))) := by
        refine sum_congr rfl (fun i _ => sum_congr rfl (fun T _ => ?_))
        rw [sum_const, card_powerset, nsmul_eq_mul]; push_cast; ring
    _ = Ω * ∑ i : Fin C, ∑ t ∈ (range (s i + 1)).filter (fun t : ℕ => δ * s i ≤ (t : ℝ)),
          ((s i).choose t : ℝ) * 2 ^ (above s i).card * Real.exp (-(t * γ)) := by
        rw [mul_sum]; refine sum_congr rfl (fun i _ => ?_)
        rw [mul_sum, sum_filter, sum_filter]
        have key := sum_powerset_apply_card (x := layer s i) (fun t : ℕ =>
          if δ * s i ≤ (t : ℝ) then Ω * (2 ^ (above s i).card * Real.exp (-(t * γ))) else 0)
        rw [key, card_layer_eq]
        refine sum_congr rfl (fun t _ => ?_)
        split_ifs
        · rw [nsmul_eq_mul]; ring
        · simp

end

end Erdos641
