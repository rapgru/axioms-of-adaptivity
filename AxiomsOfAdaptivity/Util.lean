import Mathlib

open Filter
open Finset

lemma square_estimate_of_small_distance {a b c : ℝ} (ha : 0 ≤ a) (h : |a-b| ≤ c) :
  a^2 ≤ (b+c)^2 := by
  have := le_of_max_le_left h
  have := tsub_le_iff_left.mp this
  exact pow_le_pow_left₀ ha this 2

example : 2^(1/2) = 1 := rfl

lemma young_with_delta {a b δ p q : ℝ} (ha : 0 ≤ a)  (hb : 0 ≤ b) (hδ : 0 < δ) (hpq : p.HolderConjugate q): a*b ≤ δ/p * a^p + 1/(q*δ^(q/p)) * b^q := by
  have hδ₂ := le_of_lt hδ
  have hpow_nonneg := Real.rpow_nonneg hδ₂

  calc a*b
    _ = a * b * (δ ^ p⁻¹ * (δ ^ p⁻¹)⁻¹) := by field_simp
    _ = a * δ ^ (1 / p) * (b * 1 / δ ^ (1 / p)) := by ring_nf
    _ ≤ (a * δ ^ (1 / p)) ^ p / p + (b * 1 / δ ^ (1 / p)) ^ q / q := by
      apply Real.young_inequality_of_nonneg _ _ hpq
      · exact mul_nonneg ha (hpow_nonneg _)
      · apply mul_nonneg <;> simp [hb, ha, hpow_nonneg]
    _ = δ/p * a^p + (b * 1 / δ ^ (1 / p)) ^ q / q := by
      rw [Real.mul_rpow ha <| hpow_nonneg _, ←Real.rpow_mul hδ₂]
      simp [inv_mul_cancel₀ <| Real.HolderTriple.ne_zero hpq, mul_comm]
      ring
    _ = δ/p * a^p + 1/(q*δ^(q/p)) * b^q := by
      field_simp
      rw [Real.div_rpow hb <| hpow_nonneg _, ←Real.rpow_mul hδ₂]
      ring_nf

lemma sum_square_le_square_sum {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    ∀ δ > 0, (a+b)^2 ≤ (1+δ)*a^2 + (1+δ⁻¹)*b^2 := by
  intros δ hδ
  have := young_with_delta ha hb hδ Real.HolderConjugate.two_two
  calc (a + b) ^ 2
    _ = a^2 + 2*(a*b) + b^2 := by ring
    _ ≤ a^2 + 2*(δ/2 * a^2 + 1/(2*δ) * b^2) + b^2 := by simpa using this
    _ = (1+δ)*a^2 + (1+δ⁻¹)*b^2 := by ring

lemma Ioo_01_mul_lt {a b : ℝ} (ha : a < 1) (hb : 0 < b) : a * b < b := mul_lt_of_lt_one_left hb ha

lemma nnreal_fun_bbd_below (f : ℕ → NNReal) : BddBelow (Set.range f) := by
  simp only [OrderBot.bddBelow]

lemma lift_bound_above (f : ℕ → NNReal) (hf : BddAbove (Set.range f)) : BddAbove (Set.range (λ n ↦ ↑(f n) : ℕ → ℝ)) := by
  exact BddAbove.range_comp hf fun ⦃a b⦄ a ↦ a

lemma lift_bound_below (f : ℕ → NNReal) : BddBelow (Set.range (λ n ↦ ↑(f n) : ℕ → ℝ)) := by
  refine BddBelow.range_comp ?_ fun ⦃a b⦄ a ↦ a
  exact nnreal_fun_bbd_below f

lemma nnreal_limsup_const_mul {u : ℕ → NNReal} {a : NNReal} (hu: IsBoundedUnder (· ≤ ·) atTop u):
    Filter.limsup (fun n ↦ a * u n) atTop = a * Filter.limsup u atTop := by
  rw [← ENNReal.coe_inj]
  push_cast
  rw [ENNReal.ofNNReal_limsup hu, ENNReal.ofNNReal_limsup]
  push_cast
  rw [ENNReal.limsup_const_mul_of_ne_top (by simp)]

  let f : NNReal → NNReal := fun x ↦ a * x
  have hf : Monotone f := mul_left_mono
  exact Monotone.isBoundedUnder_le_comp hf hu

lemma smaller_q_eq_zero (a q: NNReal) (hq : q < 1) (ha : a ≤ q*a) : a = 0 := by
  by_contra h
  nth_rw 1 [← mul_one a] at ha
  rw [mul_comm, mul_le_mul_iff_of_pos_right <| pos_of_ne_zero h] at ha

  have hc : ¬q < 1 := not_lt_of_ge ha
  contradiction

lemma monotone_map_bdd_above_range {h : NNReal → NNReal} {f : ℕ → NNReal} (hh : Monotone h) (hf: BddAbove (Set.range f)) :
    BddAbove (Set.range (h∘f)) := by
  rw [Set.range_comp]
  exact Monotone.map_bddAbove hh hf

-- limsup of unbounded functions is 0, but this is not troublesome
-- because the theorem we use to conclude the limit from the limsup
-- needs an additional proof of boundedness
example : limsup (λ n : NNReal ↦ n) atTop = 0 := by
  apply NNReal.limsup_of_not_isBoundedUnder
  apply Filter.not_isBoundedUnder_of_tendsto_atTop
  exact fun _ a ↦ a
