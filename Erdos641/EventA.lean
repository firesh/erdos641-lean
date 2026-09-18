import Erdos641.Counting
import Erdos641.EventB

/-!
# The locally-dense event (Lemma 2.1 of Janzer–Steiner–Sudakov)

For a vertex set `X` below layer `a`, an edge of the graph inside `X` is the same as a key
`k` (a vertex `x ∈ X` and a later layer `j < a`) whose chosen vertex `ω k` lies in `X`.
-/

namespace Erdos641

open Finset

variable {C : ℕ} {s : Fin C → ℕ}

/-- The lower vertex of a key. -/
def low (k : Key s) : Vtx s := ⟨k.1.1.1, k.2⟩

/-- Keys with lower vertex in `X` and target layer below `a`. -/
def keysIn (a : ℕ) (X : Finset (Vtx s)) : Finset (Key s) := by
  classical exact univ.filter (fun k : Key s => low k ∈ X ∧ k.1.1.2.val < a)

/-- Positions of `X` in the target layer of `k`. -/
def posIn (X : Finset (Vtx s)) (k : Key s) : Finset (Fin (s k.1.1.2)) := by
  classical exact univ.filter (fun v => (⟨k.1.1.2, v⟩ : Vtx s) ∈ X)

theorem card_keysIn (a : ℕ) (X : Finset (Vtx s)) : (keysIn a X).card ≤ X.card * C := by
  classical
  have : (keysIn a X).card ≤ (X ×ˢ (univ : Finset (Fin C))).card := by
    refine card_le_card_of_injOn (fun k => (low k, k.1.1.2)) ?_ ?_
    · intro k hk
      simp only [keysIn, coe_filter, Set.mem_ofPred_eq, mem_univ, true_and] at hk
      exact mem_coe.mpr (mem_product.mpr ⟨hk.1, mem_univ _⟩)
    · intro k _ l _ h
      simp only [low, Prod.mk.injEq, Sigma.mk.inj_iff] at h
      obtain ⟨⟨h1, h2⟩, h3⟩ := h
      obtain ⟨⟨⟨i, j⟩, hij⟩, u⟩ := k
      obtain ⟨⟨⟨i', j'⟩, hij'⟩, u'⟩ := l
      simp only at h1 h2 h3
      subst h1; subst h3
      simp only [heq_eq_eq] at h2
      subst h2; rfl
  rwa [card_product, card_univ, Fintype.card_fin] at this

section
variable (hs : ∀ i, 0 < s i) (hdec : ∀ i j : Fin C, i ≤ j → s j ≤ s i)
include hs hdec

/-- **Event A.** For fixed `a ≥ 1`, `X` and `Q ⊆ keysIn a X`, the configurations sending every
key of `Q` into `X` form at most a fraction `(|X| / s (a - 1)) ^ |Q|`. -/
theorem eventA_card (a : Fin C) (ha : 0 < a.val) (X : Finset (Vtx s)) (Q : Finset (Key s))
    (hQ : Q ⊆ keysIn a X) :
    ((univ.filter (fun ω : Omega s => ∀ k ∈ Q, ω k ∈ posIn X k)).card : ℝ) ≤
      (Fintype.card (Omega s) : ℝ) *
        ((X.card : ℝ) / s ⟨a.val - 1, by omega⟩) ^ Q.card := by
  classical
  rw [card_constrained_real hs Q (posIn X)]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  rw [← prod_const]
  refine prod_le_prod (fun k _ => by positivity) (fun k hk => ?_)
  have hk' := hQ hk
  simp only [keysIn, mem_filter, mem_univ, true_and] at hk'
  have h1 : ((posIn X k).card : ℝ) ≤ X.card := by
    have : (posIn X k).card ≤ X.card := by
      unfold posIn
      rw [card_positions]
      exact card_filter_le _ _
    exact_mod_cast this
  have h2 : (s ⟨a.val - 1, by omega⟩ : ℝ) ≤ s k.1.1.2 := by
    exact_mod_cast hdec _ _ (by rw [Fin.le_def]; simp; omega)
  have h3 : (0 : ℝ) < s ⟨a.val - 1, by omega⟩ := by exact_mod_cast hs _
  calc ((posIn X k).card : ℝ) / s k.1.1.2 ≤ X.card / s k.1.1.2 :=
        div_le_div_of_nonneg_right h1 (by positivity)
    _ ≤ X.card / s ⟨a.val - 1, by omega⟩ := div_le_div_of_nonneg_left (by positivity) h3 h2

end

/-- Edges inside `X` are bounded by the keys of `X` landing in `X`. -/
theorem card_edges_le_keys (ω : Omega s) (a : ℕ) (X : Finset (Vtx s)) (hX : ∀ x ∈ X, x.1.val < a)
    (F : Finset (Sym2 (Vtx s))) (hF : ∀ e ∈ F, e ∈ (graph ω).edgeSet)
    (hFX : ∀ e ∈ F, ∀ v ∈ e, v ∈ X) :
    F.card ≤ ((keysIn a X).filter (fun k => ω k ∈ posIn X k)).card := by
  classical
  have : F ⊆ ((keysIn a X).filter (fun k => ω k ∈ posIn X k)).image
      (fun k => s(low k, (⟨k.1.1.2, ω k⟩ : Vtx s))) := by
    intro e he
    have hE := hF e he
    induction e using Sym2.ind with
    | h p q =>
      have hp := hFX _ he p (Sym2.mem_mk_left _ _)
      have hq := hFX _ he q (Sym2.mem_mk_right _ _)
      rcases hE with ⟨h, hv⟩ | ⟨h, hv⟩
      · obtain ⟨j, v⟩ := q
        have hω : ω ⟨⟨(p.1, j), h⟩, p.2⟩ = v := Fin.ext hv
        refine mem_image.mpr ⟨key p j h, ?_, ?_⟩
        · simp only [keysIn, posIn, mem_filter, mem_univ, true_and]
          exact ⟨⟨hp, hX _ hq⟩, by simp only [key]; rw [hω]; exact hq⟩
        · simp only [low, key]; rw [hω]
      · obtain ⟨j, v⟩ := p
        have hω : ω ⟨⟨(q.1, j), h⟩, q.2⟩ = v := Fin.ext hv
        refine mem_image.mpr ⟨key q j h, ?_, ?_⟩
        · simp only [keysIn, posIn, mem_filter, mem_univ, true_and]
          exact ⟨⟨hq, hX _ hp⟩, by simp only [key]; rw [hω]; exact hp⟩
        · simp only [low, key]; rw [hω, Sym2.eq_swap]
  exact (card_le_card this).trans card_image_le

end Erdos641
