import Mathlib
import Mathlib.NumberTheory.PrimeCounting

set_option autoImplicit false

noncomputable def primeCountingReal (x : ℝ) : ℕ :=
  if (x ≤ 0) then 0 else Nat.primeCounting ⌊x⌋₊

open Finset Nat BigOperators Filter
variable (x : ℝ)

def S₁ (x : ℝ) : Set ℕ := smoothNumbers (⌊x⌋₊ + 1)

lemma log_le_harmonic (n : ℕ) (hn : 0 < n) (hnx : n ≤ x) (hxn : x < n + 1) :
    Real.log x ≤ harmonic n := by
  have hxpos : 0 < x := LT.lt.trans_le (cast_pos.mpr hn) hnx
  have h₁ : Real.log x ≤ Real.log (n + 1 : ℝ) := by
    rw [Real.log_le_log_iff hxpos]; linarith; linarith
  have h₂ : Real.log (n + 1 : ℝ) ≤ harmonic n := by
    norm_cast
    exact log_add_one_le_harmonic n
  exact LE.le.trans h₁ h₂

lemma H_P4_2 : (∑' m : (S₁ x), (m : ℝ)⁻¹) = (∏ p ∈ primesBelow ⌊x⌋.natAbs, (∑' k : ℕ, (p ^ k : ℝ)⁻¹)) := by sorry

lemma H_P4_3 : (∏ p in primesBelow ⌊x⌋₊, (∑' k : ℕ, (p ^ k : ℝ)⁻¹)) ≤ (∏ p ∈ primesBelow ⌊x⌋₊, (p : ℝ) / (p - 1)) := by
  sorry

lemma H_P4_4a {k p: ℝ} (hk: k > 0) (hp: p ≥ k + 1): p / (p - 1) ≤ (k + 1) / k := by
  have h_k_nonzero: k ≠ 0 := ne_iff_lt_or_gt.mpr (Or.inr hk)
  have h_p_pred_pos: p - 1 > 0 := by linarith
  have h_p_pred_nonzero: p - 1 ≠ 0 := ne_iff_lt_or_gt.mpr (Or.inr h_p_pred_pos)
  have h₁: p / (p - 1) = 1 + 1 / (p - 1) := by
    rw [one_add_div h_p_pred_nonzero, sub_add_cancel]
  rw [← one_add_div h_k_nonzero, h₁, add_le_add_iff_left,
    one_div_le_one_div h_p_pred_pos hk, le_sub_iff_add_le]
  exact hp

theorem monotone_primeCountingReal : Monotone primeCountingReal := by
  intro a b hab
  unfold primeCountingReal
  by_cases ha : a ≤ 0
  · by_cases hb : b ≤ 0
    · simp [ha, hb]
    · simp [ha, hb]
  · by_cases hb : b ≤ 0
    · linarith
    · simp only [ha, hb]
      exact monotone_primeCounting <| Nat.floor_mono hab

theorem primeCountingReal_three : primeCountingReal 3 = 2 := by
  unfold primeCountingReal
  norm_num
  have : π 3 = 2 := by decide
  sorry

theorem primeCountingReal_ge_two (hx : x ≥ 3) : primeCountingReal x ≥ 2 := by
 sorry

/-theorem nth_prime_ge_add_two : nth Nat.Prime n ≥ n + 2 := by
  induction' n with n ih
  . norm_num
    rw [le_iff_eq_or_lt]
    exact Or.inl zeroth_prime_eq_two.symm
  . rw [succ_eq_add_one]
    rw [ge_iff_le, ← add_le_add_iff_right 1, add_assoc] at ih
    norm_num at ih
    simp_arith
    have h : nth Nat.Prime n + 1 ≤ nth Nat.Prime (n + 1) := by
      rw [succ_le_iff, nth_lt_nth]
      exact lt_add_one n
      sorry
    exact LE.le.trans ih h -/

lemma H_P4_4 : (∏ p ∈ primesBelow ⌊x⌋₊, (p : ℝ) / (p - 1))
    ≤ (∏ k ∈ Icc 1 (primeCountingReal x), (k + 1 : ℝ) / k) := by
  --rw [H_P4_4a]
  sorry

lemma prod_Icc_succ_div (n : ℕ) (hn : 2 ≤ n) : (∏ x ∈ Icc 1 n, ((x + 1) : ℝ) / x) = n + 1 := by
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

lemma H_P4_5 (hx : x ≥ 3) : (∏ k ∈ Icc 1 (primeCountingReal x), ((k + 1) : ℝ)/ k) = primeCountingReal x + 1 := by
  rw [prod_Icc_succ_div (primeCountingReal x)
    (primeCountingReal_three ▸ Monotone.imp monotone_primeCountingReal hx)]

--lemma H_P4_5' : (∏ k in Icc 1 (primeCountingReal x), (nth primesBelow k : ℝ) / ((nth primesBelow k) - 1))
--    ≤ (∏ k in Icc 1 (primeCountingReal x), (k + 1 : ℝ) / k) := by
--  sorry

/-- All `m`, `0 < m < n` are `n`-smooth numbers -/
lemma mem_smoothNumbers_of_lt {m n : ℕ} (hm : 0 < m) (hmn : m < n) : m ∈ n.smoothNumbers :=
  smoothNumbers_eq_factoredNumbers _ ▸ ⟨not_eq_zero_of_lt hm,
  fun _ h => Finset.mem_range.mpr <| lt_of_le_of_lt (le_of_mem_factors h) hmn⟩

/-- The prime factors of an `n`-smooth number are contained in the set of primes below `n`. -/
lemma primeFactors_subset_of_mem_smoothNumbers {m n : ℕ} (hms : m ∈ n.smoothNumbers) :
    m.primeFactors ⊆ n.primesBelow :=
  have hxle {x : ℕ} (hpf : x ∈ m.primeFactors) : x < n := by
    obtain ⟨_, h⟩ := mem_smoothNumbers.mp hms
    exact h x (mem_primeFactors_iff_mem_factors.mp hpf)
  fun _ h ↦ mem_primesBelow.mpr ⟨hxle h, prime_of_mem_primeFactors h⟩

/-- `m` is an `n`-smooth number if all of its prime factors are contained in the set of
  primes below `n`. -/
lemma mem_smoothNumbers_of_primeFactors_subset {m n : ℕ} (hm : m ≠ 0)
    (hp : m.primeFactors ⊆ n.primesBelow) : m ∈ n.smoothNumbers :=
  ⟨hm, fun _ h ↦ lt_of_mem_primesBelow <| hp <| mem_primeFactors_iff_mem_factors.mpr h⟩

/-- The product of two `n`-smooth numbers is an `n`-smooth number -/
theorem mul_mem_smoothNumbers {m₁ m₂ n : ℕ}
    (hm1 : m₁ ∈ n.smoothNumbers) (hm2 : m₂ ∈ n.smoothNumbers) : m₁ * m₂ ∈ n.smoothNumbers :=
  have hm1' := primeFactors_subset_of_mem_smoothNumbers hm1
  have hm2' := primeFactors_subset_of_mem_smoothNumbers hm2
  mem_smoothNumbers_of_primeFactors_subset (mul_ne_zero hm1.1 hm2.1)
    <| primeFactors_mul hm1.1 hm2.1 ▸ Finset.union_subset hm1' hm2'

lemma two_n_smooth (n : ℕ) (hn : 1 < n) : n * 2 ∈ (n + 1).smoothNumbers := by
  have h1 : n ∈ (n + 1).smoothNumbers := by
    apply mem_smoothNumbers_of_lt (zero_lt_of_lt hn); linarith
  have h2 : 2 ∈ (n + 1).smoothNumbers := by
    apply mem_smoothNumbers_of_lt ofNat_pos; linarith
  apply mul_mem_smoothNumbers
  assumption'

/- The natural numbers `[1 ... n]` are a strict subset of the `(n+1)`-smooth numbers -/
theorem Icc_ssubset_smoothNumbers (n : ℕ) (hn : 1 < n): Set.Icc 1 n ⊂ smoothNumbers (n + 1) := by
  refine (Set.ssubset_iff_of_subset ?h).mpr ?_
  . intro x; intro h
    rw [Set.mem_Icc] at h
    exact (mem_smoothNumbers_of_lt (lt_of_succ_le h.1) (lt_succ_of_le h.2))
  . exact ⟨n * 2, And.intro (two_n_smooth n hn) (Set.not_mem_Icc_of_gt (by linarith))⟩

/--lemma Nonempty_S1_diff (n : ℕ) (hn : 1 < n) (hnx : n = ⌊x⌋₊)
    : Nonempty ((S₁ x) \ (Set.Icc 1 n) : Set ℕ) := by
  rw [nonempty_subtype]
  use n * 2
  constructor
  . unfold S₁
    exact hnx ▸ two_n_smooth n hn
  . rw [Set.mem_Icc, not_and, not_le]
    exact fun _ => (lt_mul_iff_one_lt_right (zero_lt_of_lt hn)).mpr one_lt_two
-/

lemma H_P4_1 (n : ℕ) (hn : 1 < n) (hnx : n = ⌊x⌋₊) : (∑ k ∈ Set.Icc 1 n, (k : ℝ)⁻¹) ≤ (∑' m : (S₁ x), (m : ℝ)⁻¹) := by
  have h (hs : Set.Icc 1 n ⊆ S₁ x) : (∑' m : (S₁ x), 1 / (m : ℝ)) = (∑ k ∈ Set.Icc 1 n, 1 / (k : ℝ)) + (∑' m : ((S₁ x) \ (Set.Icc 1 n) : Set ℕ), 1 / (m : ℝ)):= by sorry
  have h' : 0 ≤ (∑' m : ((S₁ x) \ (Set.Icc 1 n) : Set ℕ), 1 / (m : ℝ)) := by sorry
  simp_rw [inv_eq_one_div (_ : ℝ)]
  rw [h <| subset_of_ssubset <| hnx.symm ▸ (Icc_ssubset_smoothNumbers n hn)]
  exact (le_add_iff_nonneg_right (∑ k ∈ Set.Icc 1 n, 1 / (k : ℝ))).mpr h'

theorem log_le_primeCountingReal_add_one (n : ℕ) (x : ℝ) (hxge : x ≥ n) (hxlt : x < n + 1) :
      Real.log x ≤ primeCountingReal x + 1 :=
  calc
    Real.log x ≤ ∑ k ∈ Icc 1 n, (k : ℝ)⁻¹ := by sorry
    _ ≤ (∑' m : (S₁ x), (m : ℝ)⁻¹) := by sorry
    _ ≤ (∏ p ∈ primesBelow ⌊x⌋.natAbs, (∑' k : ℕ, (p ^ k : ℝ)⁻¹)) := by sorry
    _ ≤ (∏ k ∈ Icc 1 (primeCountingReal x), (nth Nat.Prime k : ℝ) / ((nth Nat.Prime k) - 1)) := by sorry
    _ ≤ (∏ k ∈ Icc 1 (primeCountingReal x), (k + 1 : ℝ) / k) := by sorry
    _ ≤ primeCountingReal x + 1 := by sorry

theorem primeCountingReal_unbounded : Tendsto primeCountingReal atTop atTop := by sorry

theorem infinite_setOf_prime : { p | Nat.Prime p }.Infinite :=
  sorry
