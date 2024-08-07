import Mathlib
import Mathlib.NumberTheory.PrimeCounting

set_option autoImplicit false

noncomputable def primeCountingReal (x : ℝ) : ℕ :=
  if (x < 3) then 1 else Nat.primeCounting' (Nat.floor x)

open Finset Nat BigOperators Filter
variable (x : ℝ) (h_x : 2 < (Nat.floor x))

def S₁ (x : ℝ) : Set ℕ := smoothNumbers ((Nat.floor x) + 1)

lemma primeCountingReal_pos (hxg3 : 3 ≤ x) : primeCountingReal x > 0 := by
  have count_primes_upto_three : 0 < count Nat.Prime ⌊3⌋₊ := by rw [floor_nat]; norm_num; decide
  unfold primeCountingReal
  apply ite_pos Nat.one_pos
  unfold primeCounting'
  exact gt_of_ge_of_gt (count_monotone Nat.Prime (le_floor hxg3)) count_primes_upto_three

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

lemma H_P4_4c {k p: ℝ} (hk: k > 0) (hp: p ≥ k + 1): p / (p - 1) ≤ (k + 1) / k := by
  have h_k_nonzero: k ≠ 0 := ne_iff_lt_or_gt.mpr (Or.inr hk)
  have h_p_pred_pos: p - 1 > 0 := by linarith
  have h_p_pred_nonzero: p - 1 ≠ 0 := ne_iff_lt_or_gt.mpr (Or.inr h_p_pred_pos)
  have h₁: p / (p - 1) = 1 + 1 / (p - 1) := by
    rw [one_add_div h_p_pred_nonzero, sub_add_cancel]
  rw [← one_add_div h_k_nonzero, h₁, add_le_add_iff_left,
    one_div_le_one_div h_p_pred_pos hk, le_sub_iff_add_le]
  exact hp

abbrev PrimeBelow (n p : ℕ) :=
  p ∈ (primesBelow n)

theorem monotone_primeCountingReal : Monotone primeCountingReal := by
  have count_primes_upto_three : 1 ≤ count Nat.Prime ⌊3⌋₊ := by rw [floor_nat]; norm_num; decide
  intro a b hab
  unfold primeCountingReal
  by_cases ha : a < 3
  · by_cases hb : b < 3
    · simp only [ha, hb]
      exact le_of_ble_eq_true rfl
    · simp [ha, hb]
      unfold primeCounting'
      exact le_trans count_primes_upto_three <| count_monotone Nat.Prime
        <| le_floor <| le_of_not_lt hb
  · by_cases hb : b < 3
    · linarith
    · simp only [ha, hb, not_lt, ite_false]
      simp_all only [not_lt]
      exact monotone_primeCounting' <| Nat.floor_le_floor a b hab

lemma primeCountingReal_three : primeCountingReal 3 = 1 := by
  unfold primeCountingReal
  simp only [lt_self_iff_false, ↓reduceIte, floor_ofNat]
  decide

lemma prod_Icc_add_one {a b : ℕ} (f : ℕ → ℝ) : (∏ k ∈ Icc a b, f k) =
    (∏ k ∈ Icc (a + 1) (b + 1), f (k - 1)) := by
  rw [← image_add_right_Icc a b 1]
  have h : ∀ x ∈ Icc a b, ∀ y ∈ Icc a b, succ x = succ y → x = y := by omega
  rw [prod_image h]
  simp only [succ_eq_add_one, add_tsub_cancel_right]

lemma H_P4_4a (hxg4 : 4 ≤ x) : (∏ k ∈ Icc 0 ((primeCountingReal x) - 1),
    (nth (PrimeBelow (Nat.floor x)) k : ℝ) / ((nth (PrimeBelow (Nat.floor x)) k) - 1))
    = (∏ k ∈ Icc 1 (primeCountingReal x),
    (nth (PrimeBelow (Nat.floor x)) (k - 1) : ℝ) / (nth (PrimeBelow (Nat.floor x)) (k - 1) - 1)) := by
  rw [prod_Icc_add_one, zero_add]
  rw [←Nat.sub_add_comm (n := (primeCountingReal x)) (k := 1) (m := 1)]
  rw [Nat.add_sub_cancel]
  apply primeCountingReal_pos x
  linarith
  exact x

lemma count_PrimeBelow (n : ℕ) : count (PrimeBelow n) 2 = 0 := by
  have : (filter (PrimeBelow n) (range 2)).card = 0 := by
    unfold PrimeBelow
    unfold primesBelow
    simp_rw [mem_filter, mem_range, Finset.card_eq_zero]
    rw [Finset.filter_eq_empty_iff]
    intro m hm
    match m, hm with
    | 0, _ =>
      intro h
      simp_all only [mem_range, ofNat_pos, not_and]
      exact not_prime_zero h.2
    | 1, _ =>
      intro h
      simp_all only [mem_range, ofNat_pos, not_and]
      exact not_prime_one h.2
  rw [← this]
  apply count_eq_card_filter_range

lemma nth_zero_PrimeBelow  (n : ℕ) (hn : 2 < n) : nth (PrimeBelow n) 0 = 2 := by
  rw [← count_PrimeBelow]
  · apply nth_count (p := PrimeBelow n) (n := 2)
    · unfold PrimeBelow
      unfold primesBelow
      rw [Finset.mem_filter, Finset.mem_range]
      exact ⟨ hn, by decide ⟩
  · exact hn

lemma le_PrimeBelow (n : ℕ) (hn : n < primeCountingReal x) (hxg4 : 4 ≤ x) : 1 ≤ nth (PrimeBelow ⌊x⌋₊) n := by
  induction n with
  | zero =>
    rw [nth_zero_PrimeBelow ⌊x⌋₊ h_x]
    exact NeZero.one_le
  | succ n' ih =>
    have h₁ (m : ℕ) (hm : m + 1 < primeCountingReal x) :
        nth (PrimeBelow ⌊x⌋₊) m ≤ nth (PrimeBelow ⌊x⌋₊) (m + 1) := by
      apply nth_le_nth_of_lt_card (p := PrimeBelow ⌊x⌋₊)
      · exact le_add_right m 1
      · have : ¬x < 3 := by linarith
        have h₂ : (primesBelow ⌊x⌋₊).card = primeCountingReal x := by
          unfold primeCountingReal
          split_ifs
          · contradiction
          · rw [primesBelow_card_eq_primeCounting']
        simp_rw [setOf_mem, Set.toFinite_toFinset, toFinset_coe]
        rw [h₂]
        unfold primeCountingReal
        split_ifs
        · contradiction
        · unfold primeCountingReal at hm
          split_ifs at hm
          exact hm
      · unfold PrimeBelow
        exact Multiset.finite_toSet ⌊x⌋₊.primesBelow.val
    apply Nat.le_trans (n := 1) (m := nth (PrimeBelow ⌊x⌋₊) n') (k := nth (PrimeBelow ⌊x⌋₊) (n' + 1))
    · omega
    · exact h₁ n' hn

lemma H_P4_4e (hxg4 : 4 ≤ x) : ∀ i ∈ Icc 1 (primeCountingReal x),
    0 ≤ (nth (PrimeBelow ⌊x⌋₊) (i - 1) : ℝ) / ((nth (PrimeBelow ⌊x⌋₊) (i - 1)) - 1) := by
  have h₁ (a : ℝ) (ha1 : 1 ≤ a) : 0 ≤ a - 1 := by linarith
  intro i j
  apply div_nonneg (a := (nth (PrimeBelow ⌊x⌋₊) (_ - 1) : ℝ)) (b := ((nth (PrimeBelow ⌊x⌋₊) (_ - 1)) - 1))
    (ha := by linarith) _
  apply h₁
  norm_cast
  apply (mem_Icc).mp at j
  apply le_PrimeBelow
  · exact h_x
  · rcases j with ⟨h₂, h₃⟩
    exact sub_one_lt_of_le h₂ h₃
  · exact hxg4

lemma H_P4_4b : ∀ i ∈ Icc 1 (primeCountingReal x),
    (nth (PrimeBelow ⌊x⌋₊) (i - 1) : ℝ) / ((nth (PrimeBelow ⌊x⌋₊) (i - 1) : ℝ) - 1) ≤ ((i : ℝ) + 1) / (i : ℝ) := by
  sorry

lemma H_P4_4 (hxg4 : 4 ≤ x) : (∏ k ∈ Icc 0 ((primeCountingReal x) - 1),
    ((nth (PrimeBelow (Nat.floor x)) k : ℝ) / (nth (PrimeBelow (Nat.floor x)) k - 1)))
    ≤ (∏ k ∈ Icc 1 (primeCountingReal x), ((k + 1 : ℝ) / k)) := by
  rw [H_P4_4a x hxg4]
  apply Finset.prod_le_prod
  · apply H_P4_4e
    · exact h_x
    · exact hxg4
  · apply H_P4_4b

lemma prod_Icc_succ_div (n : ℕ) (hn : 1 ≤ n) : (∏ x ∈ Icc 1 n, ((x + 1) : ℝ) / x) = n + 1 := by
  rw [← Nat.Ico_succ_right]
  induction' n with n h
  · simp
  · rw [Finset.prod_Ico_succ_top <| Nat.le_add_left 1 n]
    norm_num
    cases' lt_or_ge n 2 with _ h2
    · interval_cases n
      · norm_num
      · norm_num
    apply one_le_of_lt at h2
    specialize h h2
    field_simp [Finset.prod_eq_zero_iff] at h ⊢
    rw [h]
    ring

lemma H_P4_5 (hx : x ≥ 4) : (∏ k ∈ Icc 1 (primeCountingReal x), (k + 1 : ℝ) / k) = primeCountingReal x + 1 := by
  exact prod_Icc_succ_div (primeCountingReal x)
    (primeCountingReal_three ▸ Monotone.imp monotone_primeCountingReal (by linarith))

--lemma H_P4_5' : (∏ k in Icc 1 (primeCountingReal x), (nth primesBelow k : ℝ) / ((nth primesBelow k) - 1))
--    ≤ (∏ k in Icc 1 (primeCountingReal x), (k + 1 : ℝ) / k) := by
--  sorry

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

lemma H_P4_3a2 (hxg4 : 4 ≤ x) : ⌊x⌋₊.primesBelow.toList.length = (primeCountingReal x) := by
  unfold primeCountingReal
  split <;> rename_i h
  have H (_ : x < 3) : ¬4 ≤ x := by apply not_le.mpr; linarith
  apply H at h
  contradiction
  rw [length_toList, primesBelow_card_eq_primeCounting']

lemma H_P4_3a1' {α G : Type*} [CommMonoid G] [Inhabited α] (L : List α) (f : α → G) :
    (L.map f).prod = ∏ (i : Fin L.length), f (L.get i) := by
  simp only [List.get_eq_getElem, Fin.prod_univ_get']

lemma H_P4_3a' (f : ℕ → ℝ) (hxg4 : 4 ≤ x) : (∏ p ∈ primesBelow (Nat.floor x), f p) =
    (∏ k ∈ Icc 0 ((primeCountingReal x) - 1), f ((primesBelow (Nat.floor x)).toList)[k]!) :=
  calc
    ∏ p ∈ primesBelow (Nat.floor x), f p = ∏ (k : Fin ((primesBelow (Nat.floor x)).toList.length)), f (List.get ((primesBelow ⌊x⌋₊).toList) k) := by
      rw [← prod_to_list, H_P4_3a1']
    _ = ∏ k : Fin ((primesBelow (Nat.floor x)).toList.length), f ((primesBelow (Nat.floor x)).toList)[k]! := by
      simp only [List.get_eq_getElem, Fin.prod_univ_get', prod_to_list, Fin.getElem!_fin,
        getbang_natCast_eq_get, Fin.getElem_fin]
    _ = ∏ k ∈ range (primeCountingReal x), f ((primesBelow (Nat.floor x)).toList)[k]! := by
      rw [← H_P4_3a2, prod_range]; rfl; exact hxg4
    _ = ∏ k ∈ Icc 0 ((primeCountingReal x) - 1), f ((primesBelow (Nat.floor x)).toList)[k]! := by
      rw [range_eq_Icc_zero_sub_one]
      exact zero_lt_iff.mp (primeCountingReal_pos x (by linarith))

lemma H_P4_3a'' (hxg4 : 4 ≤ x) (k : ℕ): ((primesBelow (Nat.floor x)).toList)[k]! = nth (PrimeBelow (Nat.floor x)) k := by
-- Nat.primesBelow_card_eq_primeCounting'
  sorry

lemma H_P4_3a (hxg4 : 4 ≤ x) : (∏ p ∈ primesBelow (Nat.floor x), ((p : ℝ) / (p - 1))) =
    (∏ k ∈ Icc 0 ((primeCountingReal x) - 1),
    ((nth (PrimeBelow (Nat.floor x)) k : ℝ) / (nth (PrimeBelow (Nat.floor x)) k - 1))) := by
  rw [H_P4_3a' x (f := fun (k : ℕ) => ((k : ℝ) / (k - 1))) hxg4]
  simp_rw [H_P4_3a'' x hxg4]

theorem log_le_primeCountingReal_add_one (n : ℕ)
    (hn : 1 < n) (hnx : n = ⌊x⌋₊) (hxg4 : 4 ≤ x) (hxgn : x ≥ n) (hxlt : x < n + 1) :
    Real.log x ≤ primeCountingReal x + 1 :=
  calc
    Real.log x ≤ ∑ k ∈ Icc 1 n, (k : ℝ)⁻¹ := log_le_harmonic x n (zero_lt_of_lt hn) hxgn hxlt
    _ ≤ (∑' m : (S₁ x), (m : ℝ)⁻¹) := H_P4_1 x n hn hnx
    _ = (∏ p ∈ primesBelow (Nat.floor x), (∑' k : ℕ, (p ^ k : ℝ)⁻¹)) := H_P4_2 x
    _ = (∏ p ∈ primesBelow (Nat.floor x), ((p : ℝ) / (p - 1))) := H_P4_3 x
    _ = (∏ k ∈ Icc 0 ((primeCountingReal x) - 1),
        ((nth (PrimeBelow (Nat.floor x)) k : ℝ) / (nth (PrimeBelow (Nat.floor x)) k - 1))) := H_P4_3a x hxg4
    _ ≤ (∏ k ∈ Icc 1 (primeCountingReal x), (k + 1 : ℝ) / k) := H_P4_4 x h_x hxg4
    _ = primeCountingReal x + 1 := H_P4_5 x hxg4

theorem primeCountingReal_unbounded : Tendsto primeCountingReal atTop atTop := by sorry
--  rw [not_bddAbove_iff]

theorem infinite_setOf_prime : { p | Nat.Prime p }.Infinite :=
  sorry
