import Mathlib
import Mathlib.NumberTheory.PrimeCounting

set_option autoImplicit false

noncomputable def primeCountingReal (x : ℝ) : ℕ :=
  if (x < 2) then 1 else Nat.primeCounting ⌊x⌋₊

open Finset Nat BigOperators Filter
variable (x : ℝ)

def S₁ (x : ℝ) : Set ℕ := smoothNumbers (⌊x⌋₊ + 1)

/- This is already in Mathlib -/
lemma mem_smoothNumbers_of_lt' {m n : ℕ} (hm : 0 < m) (hmn : m < n) : m ∈ n.smoothNumbers := by sorry

/- This is already in Mathlib -/
theorem mul_mem_smoothNumbers' {m₁ m₂ n : ℕ}
    (hm1 : m₁ ∈ n.smoothNumbers) (hm2 : m₂ ∈ n.smoothNumbers) : m₁ * m₂ ∈ n.smoothNumbers := by sorry

/- This is already in Mathlib -/
theorem Fin.prod_univ_get' (α β : Type) [CommMonoid β] (l : List α) (f : α → β) : ∏ i, f (l.get i) = (l.map f).prod := by sorry

lemma primeCountingReal_pos (hxg3 : 3 ≤ x) : primeCountingReal x > 0 := by
  have count_primes_upto_four : 0 < count Nat.Prime (⌊3⌋₊ + 1) := by rw [floor_nat]; norm_num; decide
  unfold primeCountingReal
  apply ite_pos Nat.one_pos
  unfold primeCounting
  unfold primeCounting'
  exact gt_of_ge_of_gt
    (count_monotone Nat.Prime (Nat.add_le_add_right (le_floor hxg3) 1))
    count_primes_upto_four

lemma range_eq_Icc_zero_minus (n : ℕ) (hn : n > 0): range n = Icc 0 (n - 1) := by
  ext b
  simp_all only [mem_Icc, _root_.zero_le, true_and, mem_range]
  exact lt_iff_le_pred hn

lemma log_le_harmonic (n : ℕ) (hn : 0 < n) (hnx : n ≤ x) (hxn : x < n + 1) :
    Real.log x ≤ ∑ k ∈ Icc 1 n, (k : ℝ)⁻¹ :=
  have hxpos : 0 < x := LT.lt.trans_le (cast_pos.mpr hn) hnx
  calc
    Real.log x ≤ Real.log (n + 1 : ℝ) := by
        rw [Real.log_le_log_iff hxpos]; linarith; linarith
    _ ≤ harmonic n := by
        norm_cast; exact log_add_one_le_harmonic n
    _ = ∑ k ∈ range n, (k + 1 : ℝ)⁻¹ := by
        unfold harmonic
        simp_all only [cast_add, cast_one, Rat.cast_sum, Rat.cast_inv,
          Rat.cast_add, Rat.cast_natCast, Rat.cast_one]
    _ = ∑ k ∈ Ico 1 (n + 1), (k : ℝ)⁻¹ := by
        simp_rw [sum_Ico_eq_sum_range, Nat.add_one_sub_one, add_comm]
        simp_all only [cast_add, cast_one]
    _ = ∑ k ∈ Icc 1 n, (k : ℝ)⁻¹ := by rfl

lemma H_P4_2 : (∑' m : (S₁ x), (m : ℝ)⁻¹)
    = (∏ p ∈ primesBelow ⌊x⌋₊, (∑' k : ℕ, (p ^ k : ℝ)⁻¹)) := by sorry

lemma H_P4_3 : (∏ p ∈ primesBelow ⌊x⌋₊, (∑' k : ℕ, ((p : ℝ) ^ k)⁻¹)) =
    (∏ p ∈ primesBelow ⌊x⌋₊, ((p : ℝ) / (p - 1))) := by
  have h_p_nonzero (p' : ℕ) (hp : p' ∈ ⌊x⌋₊.primesBelow) : p' ≠ 0 :=
      Nat.Prime.ne_zero (mem_primesBelow.mp hp).2
  refine Finset.prod_congr rfl fun x hx ↦ ?_
  rw [(inv_div (_ - 1 : ℝ) (_ : ℝ)).symm]
  rw [sub_div, div_self (by exact_mod_cast h_p_nonzero x hx), one_div]
  rw [← tsum_geometric_of_lt_one]
  simp_rw [inv_pow]
  simp only [ne_eq, forall_mem_not_eq', inv_nonneg, cast_nonneg]
  rw [mem_primesBelow] at hx
  exact inv_lt_one <| one_lt_cast.mpr <| Prime.one_lt hx.2

lemma H_P4_4a {k p: ℝ} (hk: k > 0) (hp: p ≥ k + 1): p / (p - 1) ≤ (k + 1) / k := by
  have h_k_nonzero: k ≠ 0 := ne_iff_lt_or_gt.mpr (Or.inr hk)
  have h_p_pred_pos: p - 1 > 0 := by linarith
  have h_p_pred_nonzero: p - 1 ≠ 0 := ne_iff_lt_or_gt.mpr (Or.inr h_p_pred_pos)
  have h₁: p / (p - 1) = 1 + 1 / (p - 1) := by
    rw [one_add_div h_p_pred_nonzero, sub_add_cancel]
  rw [← one_add_div h_k_nonzero, h₁, add_le_add_iff_left,
    one_div_le_one_div h_p_pred_pos hk, le_sub_iff_add_le]
  exact hp

def PrimeBelow (p n : ℕ) :=
  Irreducible p ∧ p < n

theorem H_P4_4b (k : ℕ) (hk₁ : k ≥ 3) (hk₂ : k < primeCountingReal x)
    : nth (PrimeBelow ⌊x⌋.natAbs) k ≥ k + 2 := by sorry

theorem monotone_primeCountingReal : Monotone primeCountingReal := by sorry
/--  intro a b hab
  unfold primeCountingReal
  by_cases ha : a ≤ 0
  · by_cases hb : b ≤ 0
    · simp [ha, hb]
    · simp [ha, hb]
  · by_cases hb : b ≤ 0
    · linarith
    · simp only [ha, hb]
      exact monotone_primeCounting <| Nat.floor_mono hab
-/
lemma primeCountingReal_three : primeCountingReal 3 = 2 := by
  unfold primeCountingReal
  norm_num
  have : π 3 = 2 := by decide
  sorry

lemma primeCountingReal_ge_two (hx : x ≥ 3) : primeCountingReal x ≥ 2 := by
 sorry

lemma H_P4_4 : (∏ k ∈ Icc 0 ((primeCountingReal x) - 1),
    (nth (PrimeBelow ⌊x⌋₊) k : ℝ) / (nth (PrimeBelow ⌊x⌋₊) k - 1))
    ≤ (∏ k ∈ Icc 1 (primeCountingReal x), (k + 1 : ℝ) / k) := by
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

lemma H_P4_5 (hx : x ≥ 3) : (∏ k ∈ Icc 1 (primeCountingReal x), (k + 1 : ℝ) / k) = primeCountingReal x + 1 := by
  rw [prod_Icc_succ_div (primeCountingReal x)
    (primeCountingReal_three ▸ Monotone.imp monotone_primeCountingReal hx)]

--lemma H_P4_5' : (∏ k in Icc 1 (primeCountingReal x), (nth primesBelow k : ℝ) / ((nth primesBelow k) - 1))
--    ≤ (∏ k in Icc 1 (primeCountingReal x), (k + 1 : ℝ) / k) := by
--  sorry

lemma two_n_smooth (n : ℕ) (hn : 1 < n) : n * 2 ∈ (n + 1).smoothNumbers := by
  have h1 : n ∈ (n + 1).smoothNumbers := by
    apply mem_smoothNumbers_of_lt' (zero_lt_of_lt hn); linarith
  have h2 : 2 ∈ (n + 1).smoothNumbers := by
    apply mem_smoothNumbers_of_lt' ofNat_pos; linarith
  apply mul_mem_smoothNumbers'
  assumption'

/- The natural numbers `[1 ... n]` are a strict subset of the `(n+1)`-smooth numbers -/
theorem Icc_ssubset_smoothNumbers (n : ℕ) (hn : 1 < n): Set.Icc 1 n ⊂ smoothNumbers (n + 1) := by
  refine (Set.ssubset_iff_of_subset ?h).mpr ?_
  . intro x; intro h
    rw [Set.mem_Icc] at h
    exact (mem_smoothNumbers_of_lt' (lt_of_succ_le h.1) (lt_succ_of_le h.2))
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

lemma H_P4_1 (n : ℕ) (hn : 1 < n) (hnx : n = ⌊x⌋₊) :
    (∑ k ∈ Icc 1 n, (k : ℝ)⁻¹) ≤ (∑' m : (S₁ x), (m : ℝ)⁻¹) := by
  have h (hs : Set.Icc 1 n ⊆ S₁ x) : (∑' m : (S₁ x), 1 / (m : ℝ)) = (∑ k ∈ Icc 1 n, 1 / (k : ℝ)) + (∑' m : ((S₁ x) \ (Icc 1 n) : Set ℕ), 1 / (m : ℝ)):= by sorry
  have h' : 0 ≤ (∑' m : ((S₁ x) \ (Icc 1 n) : Set ℕ), 1 / (m : ℝ)) := by sorry
  simp_rw [inv_eq_one_div (_ : ℝ)]
  rw [h <| subset_of_ssubset <| hnx.symm ▸ (Icc_ssubset_smoothNumbers n hn)]
  exact (le_add_iff_nonneg_right (∑ k ∈ Icc 1 n, 1 / (k : ℝ))).mpr h'

@[simp]
lemma getbang_natCast_eq_get {α : Type*} [Inhabited α] (l : List α) (i : Fin l.length) :
    l[(i : ℕ)]! = l[i] := by
  exact getElem!_pos l (↑i) (Fin.val_lt_of_le i (le_refl l.length))

lemma H_P4_3a2 : ⌊x⌋₊.primesBelow.toList.length = (primeCountingReal x) := by sorry

lemma H_P4_3a1' {α G : Type*} [CommMonoid G] [Inhabited α] (L : List α) (f : α → G) :
    (L.map f).prod = ∏ (i : Fin L.length), f (L.get i) := by
-- works with newest Mathlib
--  simp only [Fin.getElem_fin, List.getElem_eq_get, Fin.eta, Fin.prod_univ_get']
  sorry

lemma H_P4_3a' (f : ℕ → ℝ) (hxg3 : 3 ≤ x) : (∏ p ∈ primesBelow ⌊x⌋₊, f p) =
    (∏ k ∈ Icc 0 ((primeCountingReal x) - 1), f ((primesBelow ⌊x⌋₊).toList)[k]!) :=
  calc
    ∏ p ∈ primesBelow ⌊x⌋₊, f p = ∏ (k : Fin ((primesBelow ⌊x⌋₊).toList.length)), f (List.get ((primesBelow ⌊x⌋₊).toList) k) := by
      rw [← prod_to_list, H_P4_3a1']
    _ = ∏ k : Fin ((primesBelow ⌊x⌋₊).toList.length), f ((primesBelow ⌊x⌋₊).toList)[k]! := by
      simp only [Fin.getElem!_fin, getbang_natCast_eq_get, Fin.getElem_fin, List.getElem_eq_get, Fin.eta]
    _ = ∏ k ∈ range (primeCountingReal x), f ((primesBelow ⌊x⌋₊).toList)[k]! := by
      rw [← H_P4_3a2]
      sorry
    _ = ∏ k ∈ Icc 0 ((primeCountingReal x) - 1), f ((primesBelow ⌊x⌋₊).toList)[k]! := by
      rw [range_eq_Icc_zero_minus]
      exact primeCountingReal_pos x hxg3

lemma H_P4_3a'' (hxg3 : 3 ≤ x) (k : ℕ): ((primesBelow ⌊x⌋₊).toList)[k]! = nth (PrimeBelow ⌊x⌋₊) k := by
  sorry

lemma H_P4_3a (hxg3 : 3 ≤ x) : (∏ p ∈ primesBelow ⌊x⌋₊, ((p : ℝ) / (p - 1))) =
    (∏ k ∈ Icc 0 ((primeCountingReal x) - 1),
    (nth (PrimeBelow ⌊x⌋₊) k : ℝ) / (nth (PrimeBelow ⌊x⌋₊) k - 1)) := by
  rw [H_P4_3a' x (f := fun (k : ℕ) => ((k : ℝ) / (k - 1))) hxg3]
  simp_rw [H_P4_3a'' x hxg3]

theorem log_le_primeCountingReal_add_one (n : ℕ) (x : ℝ)
    (hn : 1 < n) (hnx : n = ⌊x⌋₊) (hxg3 : 3 ≤ x) (hxgn : x ≥ n) (hxlt : x < n + 1) :
    Real.log x ≤ primeCountingReal x + 1 :=
  calc
    Real.log x ≤ ∑ k ∈ Icc 1 n, (k : ℝ)⁻¹ := log_le_harmonic x n (zero_lt_of_lt hn) hxgn hxlt
    _ ≤ (∑' m : (S₁ x), (m : ℝ)⁻¹) := H_P4_1 x n hn hnx
    _ = (∏ p ∈ primesBelow ⌊x⌋₊, (∑' k : ℕ, (p ^ k : ℝ)⁻¹)) := H_P4_2 x
    _ = (∏ p ∈ primesBelow ⌊x⌋₊, ((p : ℝ) / (p - 1))) := H_P4_3 x
    _ = (∏ k ∈ Icc 0 ((primeCountingReal x) - 1), (nth (PrimeBelow ⌊x⌋₊) k : ℝ) / (nth (PrimeBelow ⌊x⌋₊) k - 1)) := H_P4_3a x hxg3
    _ ≤ (∏ k ∈ Icc 1 (primeCountingReal x), (k + 1 : ℝ) / k) := H_P4_4 x
    _ = primeCountingReal x + 1 := H_P4_5 x hxg3

theorem primeCountingReal_unbounded : Tendsto primeCountingReal atTop atTop := by sorry

theorem infinite_setOf_prime : { p | Nat.Prime p }.Infinite :=
  sorry
