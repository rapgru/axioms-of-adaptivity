import Mathlib

open Finset

-- ANCHOR: summability_defs
def uniform_summability (a : ℕ → NNReal) :=
  Summable (a^2)
  ∧ ∃ C > 0, ∀ l : ℕ, ∑' k, (a^2) (k + l + 1) ≤ C * (a^2) l

def inverse_summability (a : ℕ → NNReal) :=
  ∀ s : ℝ, s > 0 →
    ∃ C > 0, ∀ l : ℕ, ∑ k ∈ range l, (a k)^(-1/s) ≤ C * (a l)^(-1/s)

def uniform_r_linear_convergence (a : ℕ → NNReal) :=
  ∃ q ∈ (Set.Ioo 0 1), ∃ C > 0, ∀ k, ∀ l,
    (a^2) (l+k) ≤ C * q^k * (a^2) l
-- ANCHOR_END: summability_defs

-- ANCHOR: a_var
variable {a : ℕ → NNReal}
-- ANCHOR_END: a_var

-- ANCHOR: uniform_of_uniform_r_linear_1
lemma uniform_of_uniform_r_linear (h : uniform_r_linear_convergence a) :
    uniform_summability a := by
  rcases h with ⟨q,hq,C,hC,h⟩
  -- ANCHOR_END: uniform_of_uniform_r_linear_1

  -- this result is a uniform bound on the partial sums of the series we
  -- are interested in
  -- ANCHOR: uniform_of_uniform_r_linear_2
  have : ∀ l n, ∑ k ∈ range n, (a^2) (k + l + 1) ≤ C * q * (1 - q)⁻¹ * (a^2) l := by
    intros l n
    calc ∑ k ∈ range n, (a^2) (k + l + 1)
      _ ≤ ∑ k ∈ range n, C * q^(k + 1) * (a^2) l := by {
        gcongr with k
        specialize h (k + 1) l
        rw [← add_assoc, add_comm l k] at h
        assumption
      }
      _ = ∑ k ∈ range n, (C * q * (a^2) l) * q^k := by congr with _; ring_nf
      _ = C * q * (a^2) l * ∑ k ∈ range n, q^k := by rw [← mul_sum]
      _ ≤ C * q * (a^2) l * ∑' k, q^k := by
        gcongr

        apply Summable.sum_le_tsum
        · intros i hi
          exact pow_nonneg (le_of_lt hq.1) i

        exact NNReal.summable_coe.mp <| summable_geometric_of_lt_one (le_of_lt hq.1) hq.2
      _ = C * q * (a^2) l * (1 - q)⁻¹ := by
        congr
        rw [← NNReal.coe_inj]
        push_cast [le_of_lt hq.2]
        exact tsum_geometric_of_lt_one (le_of_lt hq.1) hq.2
      _ = C * q * (1 - q)⁻¹ * (a^2) l := by ring
  -- ANCHOR_END: uniform_of_uniform_r_linear_2

  -- now we take the limit, i.e. show summability and bound the series from above
  -- ANCHOR: uniform_of_uniform_r_linear_3
  constructor
  swap
  · use C * q * (1-q)⁻¹
    constructor
    · apply mul_pos
      exact mul_pos hC hq.1
      apply Right.inv_pos.mpr
      exact tsub_pos_of_lt hq.2

    intros l
    apply NNReal.tsum_le_of_sum_range_le (this l)
  -- ANCHOR_END: uniform_of_uniform_r_linear_3

  -- ANCHOR: uniform_of_uniform_r_linear_4
  · apply NNReal.summable_of_sum_range_le

    intros n
    calc ∑ i ∈ range n, (a ^ 2) i
      _ ≤ ∑ i ∈ range (n+1), (a ^ 2) i := by
        apply sum_le_sum_of_subset_of_nonneg (range_subset.mpr (by simp)) ?_
        · intros
          apply sq_nonneg
      _ = ∑ i ∈ range n, (a ^ 2) (i + 1) + (a ^ 2) 0 := by simp [Finset.sum_range_succ']
      _ ≤ C * q * (1 - q)⁻¹ * (a ^ 2) 0 + (a ^ 2) 0 := by rel [this 0 n]
  -- ANCHOR_END: uniform_of_uniform_r_linear_4

-- ANCHOR: uniform_recursive_bound
lemma uniform_recursive_bound {C:NNReal} (hC : C > 0) (hSum: Summable (a ^ 2))
      (hBound : ∀ (l : ℕ), ∑' (k : ℕ), (a ^ 2) (k + l + 1) ≤ C * (a ^ 2) l):
    ∀ l n, ∑' k, (a^2) (k + l + n) ≤ 1/(1+C⁻¹)^n *  ∑' k, (a^2) (k + l) := by
  intros l n
  induction' n with n ih
  · simp

  calc ∑' (k : ℕ), (a ^ 2) (k + l + (n + 1))
    _ = 1/(1+C⁻¹) * (1+C⁻¹) * ∑' (k : ℕ), (a ^ 2) (k + l + (n + 1)) := by field_simp
    _ = 1/(1+C⁻¹) * (∑' (k : ℕ), (a ^ 2) (k + l + (n + 1))
        + C⁻¹ * ∑' (k : ℕ), (a ^ 2) (k + l + (n + 1))) := by ring
    _ = 1/(1+C⁻¹) * (∑' (k : ℕ), (a ^ 2) (k + l + (n + 1))
        + C⁻¹ * ∑' (k : ℕ), (a ^ 2) (k + (l + n) + 1)) := by simp [add_assoc]
    _ ≤ 1/(1+C⁻¹) * (∑' (k : ℕ), (a ^ 2) (k + l + (n + 1))
        + C⁻¹ * (C * (a^2) (l+n))) := by rel [hBound (l+n)]
    _ = 1/(1+C⁻¹) * (∑' (k : ℕ), (a ^ 2) (k + l + (n + 1)) + (a^2) (l+n)) := by field_simp
    _ = 1/(1+C⁻¹) * (∑' (k : ℕ), (a ^ 2) (k + (l + n) + 1) + (a^2) (l+n)) := by simp [add_assoc]
    _ = 1/(1+C⁻¹) * (∑' (k : ℕ), (a ^ 2) (k + (l + n))) := by
      nth_rw 2 [NNReal.sum_add_tsum_nat_add 1]
      · simp [← add_assoc]
        nth_rw 3 [add_comm]
        congr with x
        congr 3
        ring
      · exact (NNReal.summable_nat_add_iff (l + n)).mpr hSum
    _ = 1/(1+C⁻¹) * (∑' (k : ℕ), (a ^ 2) (k + l + n)) := by simp [add_assoc]
    _ ≤ 1/(1+C⁻¹) * (1 / (1 + C⁻¹) ^ n * ∑' (k : ℕ), (a ^ 2) (k + l)) := by rel [ih]
    _ = 1/(1+C⁻¹) * (1 / (1 + C⁻¹) ^ n) * ∑' (k : ℕ), (a ^ 2) (k + l) := by ring
    _ = 1/((1+C⁻¹) * (1 + C⁻¹)^n) * ∑' (k : ℕ), (a ^ 2) (k + l) := by field_simp
    _ = 1/(1 + C⁻¹)^(n+1) * ∑' (k : ℕ), (a ^ 2) (k + l) := by rw [pow_succ' (1 + C⁻¹)]
-- ANCHOR_END: uniform_recursive_bound


-- ANCHOR: uniform_r_linear_of_uniform
lemma uniform_r_linear_of_uniform (h : uniform_summability a) :
    uniform_r_linear_convergence a := by
  rcases h with ⟨hSum, C, hC, hBound⟩

  use 1/(1+C⁻¹)
  constructor
  · have h₁ : 1 < 1 + C⁻¹ := by simp [Right.inv_pos.mpr hC]
    constructor
    · simp [one_div, inv_pos, h₁]
    · simp only [one_div]
      exact inv_lt_one_of_one_lt₀ h₁

  use (1+C)
  constructor
  · simp [hC]

  intros k l
  let g := fun j ↦ (a^2) (j + l + k)
  calc (a ^ 2) (l + k)
    _ = g 0 := by unfold g; simp only [Pi.pow_apply, zero_add]
    _ ≤ ∑' j, (a^2) (j + l + k) := by
      apply Summable.le_tsum
      · unfold g
        simp only [add_assoc]
        apply NNReal.summable_nat_add _ hSum (l+k)
      · simp
    _ ≤ 1/(1 + C⁻¹)^k * ∑' (j : ℕ), (a ^ 2) (j + l) := by apply uniform_recursive_bound hC hSum hBound l k
    _ = 1/(1 + C⁻¹)^k * (∑' (j : ℕ), (a ^ 2) (j + l + 1) + (a ^ 2) l) := by
      rw [NNReal.sum_add_tsum_nat_add 1]
      simp [← add_assoc, add_comm]
      apply NNReal.summable_nat_add _ hSum l
    _ ≤ 1/(1 + C⁻¹)^k * (C * (a ^ 2) l + (a ^ 2) l) := by rel [hBound l]
    _ = (1 + C) * (1/(1 + C⁻¹))^k * (a ^ 2) l := by rw [← NNReal.coe_inj]; push_cast; ring
-- ANCHOR_END: uniform_r_linear_of_uniform

example : (0:ℝ)^(0:ℝ) = 1 := Real.rpow_zero 0
example : (0:ℝ)^(-(1:ℝ)) = 0 := by simp

-- ANCHOR: inverse_of_uniform_r_linear_1
lemma inverse_of_uniform_r_linear (ha : ∀ n, a n ≠ 0) (h : uniform_r_linear_convergence a):
    inverse_summability a := by
  rcases h with ⟨q,hq,C,hC,h⟩
  intros s hs
  use C^(1/(2*s))*(1-q^(1/(2*s)))⁻¹
  constructor
  · apply Left.mul_pos (NNReal.rpow_pos hC) ?_
    simp
    apply NNReal.rpow_lt_one hq.2
    simp [hs]
-- ANCHOR_END: inverse_of_uniform_r_linear_1

-- ANCHOR: inverse_of_uniform_r_linear_2
  have h_inv : ∀ l, ∀ k:ℕ, (a l)^(-1/s) ≤ C^(1/(2*s)) * q^(k/(2*s)) * a (l+k) ^ (-1/s) := by
    intros l k
    specialize h k l
    have hss : 1/(2*s) > 0 := by simp [hs]

    rw [← NNReal.rpow_le_rpow_iff hss] at h
    simp only [Pi.pow_apply] at h
    replace h := mul_le_mul_left' h (a (l + k) ^ (-1/s))
    replace h := mul_le_mul_left' h (a l ^ (-1/s))

    calc a l ^ (-1 / s)
      _ = a l ^ (-1 / s) * (a (l + k) ^ (-(1 / s)) * (a (l + k)) ^ (1 / s)) := by
        simp [← NNReal.rpow_add (ha (l+k))]
      _ = a l ^ (-1 / s) * (a (l + k) ^ (-1 / s) * (a (l + k) ^ 2) ^ (1 / (2 * s))) := by
        congr 2
        · rw [neg_div' s 1]
        · rw [← NNReal.rpow_natCast, ← NNReal.rpow_mul (a (l + k))]
          congr
          field_simp
      _ ≤ a l ^ (-1 / s) * (a (l + k) ^ (-1 / s) * (C * q ^ k * a l ^ 2) ^ (1 / (2 * s))) := h
      _ = a l ^ (-1 / s) * a (l + k) ^ (-1 / s) * C ^ (1 / (2 * s)) * q ^ (↑k * (1 / (2 * s))) * a l ^ (1 / s) := by
        simp only [NNReal.mul_rpow, ← mul_assoc]
        rw [← NNReal.rpow_natCast, ← NNReal.rpow_natCast]
        simp only [← NNReal.rpow_mul]
        congr 2
        field_simp
      _ = (a l ^ (-1 / s) * a l ^ (1 / s)) * a (l + k) ^ (-1 / s) * C ^ (1 / (2 * s)) * q ^ (↑k * (1 / (2 * s))) := by ring
      _ = C ^ (1 / (2 * s)) * q ^ (↑k / (2 * s)) * a (l + k) ^ (-1/ s) := by
        simp only [← NNReal.rpow_add (ha l)]
        field_simp
        ring
-- ANCHOR_END: inverse_of_uniform_r_linear_2

-- ANCHOR: inverse_of_uniform_r_linear_3
  intros l
  have h_qbound : ∀ p ∈ (Set.Ioo (0:NNReal) 1), ∑ k ∈ range l, p^(l - k) < (1-p)⁻¹ := by
    intros p hp
    calc ∑ k ∈ range l, p^(l - k)
      _ = ∑ k ∈ range l, p^(k + 1) := by
        let e : ℕ → ℕ := fun x ↦ l - x - 1
        have he_range : ∀ x ∈ range l, e x ∈ range l := by
          intros x hx
          apply mem_range.mpr
          unfold e
          calc l
            _ ≥ l - x := by exact Nat.sub_le l x
            _ > l - x - 1 := by
              refine Nat.sub_succ_lt_self (l - x) 0 ?_
              apply Nat.zero_lt_sub_of_lt
              exact List.mem_range.mp hx
        have he_involution : ∀ x ∈ range l, e (e x) = x := by
          intros x hx
          unfold e
          rw [← Int.natCast_inj]
          rw [Int.natCast_sub, Int.natCast_sub, Int.natCast_sub, Int.natCast_sub]
          group
          · exact mem_range_le hx
          · apply Nat.succ_le_of_lt
            apply Nat.zero_lt_sub_of_lt
            exact mem_range.mp hx
          · apply mem_range_le (he_range x hx)
          · apply Nat.succ_le_of_lt
            apply Nat.zero_lt_sub_of_lt
            exact mem_range.mp (he_range x hx)

        apply Finset.sum_nbij' e e he_range he_range he_involution he_involution
        · intros x hx
          unfold e
          congr
          apply Nat.eq_add_of_sub_eq ?_ rfl
          apply Nat.le_sub_of_add_le
          apply Nat.one_add_le_iff.mpr
          exact List.mem_range.mp hx
      _ = ∑ k ∈ range l, p * p^k := by
        congr with k
        apply NNReal.eq_iff.mp
        exact pow_succ' p k
      _ = p * ∑ k ∈ range l, p^k := by simp only [mul_sum]
      _ ≤ ∑ k ∈ range l, p^k := mul_le_of_le_one_left' (le_of_lt hp.2)
      _ < (1 - p)⁻¹ := geom_sum_lt (ne_of_gt hp.1) hp.2 l
-- ANCHOR_END: inverse_of_uniform_r_linear_3

-- ANCHOR: inverse_of_uniform_r_linear_4
  calc ∑ k ∈ range l, a k ^ (-1 / s)
    _ ≤ ∑ k ∈ range l, C ^ (1 / (2 * s)) * q ^ (↑(l - k) / (2 * s)) * a (k + (l - k)) ^ (-1/s) := by
      gcongr with k hk
      apply h_inv
    _ = ∑ k ∈ range l, C ^ (1 / (2 * s)) * q ^ (↑(l - k) / (2 * s)) * a l ^ (-1/s) := by
      apply Finset.sum_congr rfl
      intros k hk
      congr
      apply Nat.add_sub_of_le
      exact mem_range_le hk
    _ = ∑ k ∈ range l, (C ^ (1 / (2 * s)) * a l ^ (-1/s)) * q ^ (↑(l - k) / (2 * s)) := by
      congr
      funext
      ring
    _ = C ^ (1 / (2 * s)) * a l ^ (-1/s) * ∑ k ∈ range l, q ^ (↑(l - k) / (2 * s)) := by simp [← mul_sum, mul_assoc]
    _ = C ^ (1 / (2 * s)) * a l ^ (-1/s) * ∑ k ∈ range l, (q ^ (1 / (2 * s)))^(l - k) := by
      congr
      funext
      rw [← NNReal.rpow_natCast, ← NNReal.rpow_mul q]
      field_simp
    _ ≤ C ^ (1 / (2 * s)) * a l ^ (-1/s) * (1-q^(1/(2*s)))⁻¹ := by
      have : q^(1/(2*s)) ∈ Set.Ioo (0:NNReal) 1 := by
        constructor
        · apply NNReal.rpow_pos
          exact hq.1
        · apply NNReal.rpow_lt_one
          exact hq.2
          apply one_div_pos.mpr
          linarith [hs]
      rel [h_qbound (q^(1/(2*s))) this]
    _ = C ^ (1 / (2 * s)) * (1 - q ^ (1 / (2 * s)))⁻¹ * a l ^ (-1 / s) := by ring
-- ANCHOR_END: inverse_of_uniform_r_linear_4

lemma inverse_recursive_bound {C:NNReal} {a:ℕ→NNReal} (hC : C > 0) (hBound : ∀ (l : ℕ), ∑ k ∈ range l, a k ≤ C * a l):
    ∀ n l, ∑ k ∈ range l, a k ≤ 1/(1 + C⁻¹)^n *  ∑ k ∈ range (l + n), a k := by
  intros n
  induction' n with n ih
  · simp

  intros l

  calc ∑ k ∈ range l, a k
    _ = 1/(1+C⁻¹) * (1+C⁻¹) * ∑ k ∈ range l, a k := by field_simp
    _ = 1/(1+C⁻¹) * ((∑ k ∈ range l, a k) + C⁻¹ * (∑ k ∈ range l, a k)) := by ring
    _ ≤ 1/(1+C⁻¹) * ((∑ k ∈ range l, a k) + C⁻¹ * (C * a l)) := by rel [hBound l]
    _ = 1/(1+C⁻¹) * ((∑ k ∈ range l, a k) + a l) := by field_simp
    _ = 1/(1+C⁻¹) * ((∑ k ∈ range (l+1), a k)) := by simp only [one_div, sum_range_succ]
    _ ≤ 1/(1+C⁻¹) * (1/(1+C⁻¹)^n * (∑ k ∈ range ((l+1)+n), a k)) := by rel [ih (l+1)]
    _ = 1/(1+C⁻¹) * (1/(1+C⁻¹)^n * (∑ k ∈ range (l+(n+1)), a k)) := by {congr 4; ring}
    _ = 1/(1 + C⁻¹)^(n+1) * ∑ k ∈ range (l+(n+1)), a k := by simp [pow_add, ← mul_assoc]

-- ANCHOR: uniform_r_linear_of_inverse_1
lemma uniform_r_linear_of_inverse (ha : ∀ n, a n ≠ 0) (h : inverse_summability a) : uniform_r_linear_convergence a := by
  rcases (h (1/2) (by simp only [one_div, gt_iff_lt, inv_pos, Nat.ofNat_pos])) with ⟨C, hC, hBound⟩
  simp at hBound
  use (1+C⁻¹)⁻¹
  constructor
  · simp
    refine inv_lt_one_of_one_lt₀ ?_
    refine lt_add_of_pos_right 1 ?_
    simp [hC]

  use (1+C)
  constructor
  · simp [hC]

  intros k l
-- ANCHOR_END: uniform_r_linear_of_inverse_1
-- ANCHOR: uniform_r_linear_of_inverse_2
  have h := by
    let g : ℕ → NNReal := fun k ↦ (a k)^(-2:ℝ)
    calc (a l)^(-2:ℝ)
      _ = g l  := by rfl
      _ ≤ ∑ j ∈ range (l+1), g j := by apply Finset.single_le_sum <;> simp
      _ ≤ 1/(1 + C⁻¹)^k *  ∑ j ∈ range ((l + 1) + k), g j := by apply inverse_recursive_bound hC hBound
      _ = 1/(1 + C⁻¹)^k * (∑ j ∈ range ((l + k) + 1), g j) := by {congr 3; ring}
      _ = 1/(1 + C⁻¹)^k * (∑ j ∈ range (l + k), g j + g (l+k)) := by simp [sum_range_succ]
      _ ≤ 1/(1 + C⁻¹)^k * (C * g (l+k) + g (l+k)) := by rel [hBound (l+k)]
      _ = 1/(1 + C⁻¹)^k * (1+C) * g (l+k) := by ring
      _ = 1/(1 + C⁻¹)^k * (1+C) * (a (l+k))^(-2:ℝ) := by rfl
-- ANCHOR_END: uniform_r_linear_of_inverse_2

-- ANCHOR: uniform_r_linear_of_inverse_3
  calc (a ^ 2) (l + k)
    _ = a (l+k) ^ 2 * ((a l) ^ (-2:ℝ) * (a l) ^ (2:ℝ)) := by
      rw [← NNReal.rpow_add (ha l)]
      simp
    _ = a (l+k) ^ 2 * ((a l) ^ (-2:ℝ) * (a l) ^ 2) := by simp
    _ = a l ^ 2 * a l ^ (-2:ℝ) * a (l + k) ^ 2 := by ring
    _ ≤ a l ^ 2 * (1 / (1 + C⁻¹) ^ k * (1 + C) * a (l + k) ^ (-2:ℝ)) * a (l + k) ^ 2 := by rel[h]
    _ = a l ^ 2 * (1 / (1 + C⁻¹) ^ k * (1 + C)) * (a (l + k) ^ (-2:ℝ) * a (l + k) ^ 2) := by ring
    _ = a l ^ 2 * (1 / (1 + C⁻¹) ^ k * (1 + C)) * (a (l + k) ^ (-2:ℝ) * a (l + k) ^ (2:ℝ)) := by simp
    _ = a l ^ 2 * (1 / (1 + C⁻¹) ^ k * (1 + C)) := by
      rw [← NNReal.rpow_add (ha (l+k))]
      simp
    _ = (1 / (1 + C⁻¹) ^ k * (1 + C)) * (a l) ^ 2 := by ring
    _ = ((1 + C⁻¹)⁻¹ ^ k * (1 + C)) * (a ^ 2) l := by simp
    _ = (1 + C) * (1 + C⁻¹)⁻¹ ^ k * (a ^ 2) l := by ring
-- ANCHOR_END: uniform_r_linear_of_inverse_3

-- ANCHOR: uniform_of_uniform_r_linear
theorem summability_equivalence (ha : ∀ n, a n ≠ 0) :
    List.TFAE [uniform_summability a, inverse_summability a, uniform_r_linear_convergence a] := by
  tfae_have 1 → 3 := uniform_r_linear_of_uniform
  tfae_have 3 → 1 := uniform_of_uniform_r_linear
  tfae_have 3 → 2 := inverse_of_uniform_r_linear ha
  tfae_have 2 → 3 := uniform_r_linear_of_inverse ha
  tfae_finish
-- ANCHOR_END: uniform_of_uniform_r_linear
