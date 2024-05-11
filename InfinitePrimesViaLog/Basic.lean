import Mathlib
import Mathlib.NumberTheory.PrimeCounting

set_option autoImplicit false

noncomputable def primeCountingReal (x : ℝ) : ℕ :=
  if (x ≤ 0) then 0 else Nat.primeCounting ⌊x⌋₊

open Finset Nat BigOperators Filter
variable (x : ℝ)

def S₁ (x : ℝ) : Set ℕ :=
 { n | ∀ p, Nat.Prime p → p ∣ n → p ≤ x }


theorem monotone_primeCountingReal : Monotone primeCountingReal := by
  intro a b hab
  unfold primeCountingReal
  by_cases ha : a ≤ 0
  · by_cases hb : b ≤ 0
    · simp [ha, hb]
    · simp [ha, hb]
  · by_cases hb : b ≤ 0
    · linarith
    · simp [ha, hb]
      exact monotone_primeCounting <| Nat.floor_mono hab

theorem primeCountingReal_three : primeCountingReal 3 = 2 := by
  unfold primeCountingReal
  norm_num
  have : π 3 = 2 := by decide
  sorry

theorem primeCountingReal_ge_two (hx : x ≥ 3) : primeCountingReal x ≥ 2 := by sorry

lemma H_P4_4a {k p: ℝ} (hk: k > 0) (hp: p ≥ k + 1): p / (p - 1) ≤ (k + 1) / k := by
  have h_k_nonzero: k ≠ 0 := ne_iff_lt_or_gt.mpr (Or.inr hk)
  have h_p_pred_pos: p - 1 > 0 := by linarith
  have h_p_pred_nonzero: p - 1 ≠ 0 := ne_iff_lt_or_gt.mpr (Or.inr h_p_pred_pos)
  have h₁: p / (p - 1) = 1 + 1 / (p - 1) := by
    rw [one_add_div h_p_pred_nonzero, sub_add_cancel]
  rw [← one_add_div h_k_nonzero, h₁, add_le_add_iff_left,
    one_div_le_one_div h_p_pred_pos hk, @le_sub_iff_add_le]
  exact hp

lemma prod_Icc_succ_div (n : ℕ) (hn : 2 ≤ n) : (∏ x in Icc 1 n, ((x + 1) : ℝ) / x) = n + 1 := by
  rw [← Nat.Ico_succ_right]
  induction' n with n h
  · simp
  · rw [Finset.prod_Ico_succ_top <| Nat.le_add_left 1 n]
    norm_num
    cases' lt_or_ge n 2 with _ h2
    · interval_cases n
      · tauto
      · norm_num
    specialize h h2
    field_simp [Finset.prod_eq_zero_iff] at h ⊢
    rw [h]
    ring

lemma H_P4_4 : (∏ k in Icc 1 (primeCountingReal x), (nth Nat.Prime k : ℝ) / ((nth Nat.Prime k) - 1))
    ≤ (∏ k in Icc 1 (primeCountingReal x), (k + 1 : ℝ) / k) := by
  --rw [H_P4_4a]
  sorry

lemma H_P4_5 (hx : x ≥ 3) : (∏ k in Icc 1 (primeCountingReal x), ((k + 1) : ℝ)/ k) = primeCountingReal x + 1 := by
  rw [prod_Icc_succ_div]
  rw [← primeCountingReal_three]
  refine Monotone.imp monotone_primeCountingReal ?h
  exact hx

theorem log_le_primeCountingReal_add_one (n : ℕ) (x : ℝ) (hxge : x ≥ n) (hxlt : x < n + 1) :
      Real.log x ≤ primeCountingReal x + 1 :=
  calc
    Real.log x ≤ ∑ k in Icc 1 n, (k : ℝ)⁻¹ := by sorry
    _ ≤ (∑' m : (S₁ x), (m : ℝ)⁻¹) := by sorry
    _ ≤ (∏ p in primesBelow ⌊x⌋.natAbs, (∑' k : ℕ, (p ^ k : ℝ)⁻¹)) := by sorry
    _ ≤ (∏ k in Icc 1 (primeCountingReal x), (nth Nat.Prime k : ℝ) / ((nth Nat.Prime k) - 1)) := by sorry
    _ ≤ (∏ k in Icc 1 (primeCountingReal x), (k + 1 : ℝ) / k) := by sorry
    _ ≤ primeCountingReal x + 1 := by sorry

theorem primeCountingReal_unbounded : Tendsto primeCountingReal atTop atTop := by sorry

--theorem infinity_of_primes₄ :
