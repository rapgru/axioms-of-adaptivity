import Mathlib
open Filter
open TopologicalSpace
open BigOperators
open Finset
open scoped Topology

-- Utils
lemma nnreal_fun_bbd_below (f : ℕ → NNReal) : BddBelow (Set.range f) := by {
  simp only [OrderBot.bddBelow]
}

lemma lift_bound_above (f : ℕ → NNReal) (hf : BddAbove (Set.range f)) : BddAbove (Set.range (λ n ↦ ↑(f n) : ℕ → ℝ)) := by {
  exact BddAbove.range_comp hf fun ⦃a b⦄ a ↦ a
}

lemma lift_bound_below (f : ℕ → NNReal) : BddBelow (Set.range (λ n ↦ ↑(f n) : ℕ → ℝ)) := by {
  refine BddBelow.range_comp ?_ fun ⦃a b⦄ a ↦ a
  exact nnreal_fun_bbd_below f
}

lemma nnreal_limsup_const_mul {u : ℕ → NNReal} {a : NNReal} (hu: IsBoundedUnder (· ≤ ·) atTop u):
    Filter.limsup (fun n ↦ a * u n) atTop = a * Filter.limsup u atTop := by {
  rw [← ENNReal.coe_inj]
  push_cast
  rw [ENNReal.ofNNReal_limsup hu, ENNReal.ofNNReal_limsup]
  push_cast
  rw [ENNReal.limsup_const_mul_of_ne_top (by simp)]

  let f : NNReal → NNReal := fun x ↦ a * x
  have hf : Monotone f := by exact mul_left_mono
  exact Monotone.isBoundedUnder_le_comp hf hu
}

lemma smaller_q_eq_zero (a q: NNReal) (hq : q < 1) (ha : a ≤ q*a) : a = 0 := by {
  by_contra h
  have h' : a > 0 := by exact pos_of_ne_zero h
  nth_rw 1 [← mul_one a] at ha
  rw [mul_comm, mul_le_mul_iff_of_pos_right h'] at ha

  have hc : ¬q < 1 := by exact not_lt_of_ge ha
  contradiction
}

lemma monotone_map_bdd_above_range {h : NNReal → NNReal} {f : ℕ → NNReal} (hh : Monotone h) (hf: BddAbove (Set.range f)) :
    BddAbove (Set.range (h∘f)) := by {
  rw [Set.range_comp]
  exact Monotone.map_bddAbove hh hf
}

-- limsup of unbounded functions is 0, but this is not troublesome
-- because the theorem we use to conclude the limit from the limsup
-- needs an additional proof of boundedness
example : limsup (λ n : NNReal ↦ n) atTop = 0 := by {
  refine NNReal.limsup_of_not_isBoundedUnder ?_
  refine Filter.not_isBoundedUnder_of_tendsto_atTop ?_
  -- TODO understand what the heck this does
  exact fun ⦃U⦄ a ↦ a
}

-- 4.18
structure EstimatorReduction (η d : ℕ → NNReal) where
  q : NNReal
  q_range : q ∈ Set.Ioo 0 1
  C : NNReal
  C_pos : C > 0
  bound : ∀ n, (η (n + 1))^2 ≤ q * (η n)^2 + C * (d n)^2

-- Theorems about EstimatorReduction
namespace EstimatorReduction

variable {η d : ℕ → NNReal} (h : EstimatorReduction η d)
include h

def weightedSum (n : ℕ) : NNReal :=
  ∑ k ∈ Finset.range (n + 1), h.q ^ (n - k) * (d k)^2

def upperBound (n : ℕ) : NNReal :=
  h.q ^ (n + 1) * (η 0)^2 + h.C * h.weightedSum n

lemma estimator_recursive_upper_bound (n : ℕ) :
    (η (n+1))^2 ≤ h.upperBound n := by {
  induction' n with n ih
  · unfold upperBound weightedSum
    simp
    apply h.bound 0
  · calc  η (n + 1 + 1) ^ 2
      _ ≤ h.q * (η (n + 1))^2 + h.C * (d (n + 1))^2 := by apply h.bound
      _ ≤ h.q * h.upperBound n + h.C * (d (n + 1))^2 := by gcongr
      _ = h.upperBound (n+1) := by {
        -- TODO maybe split this up into smaller chunks
        unfold upperBound weightedSum
        nth_rw 2 [sum_range_succ]
        rw [mul_add, ← mul_assoc, ← pow_succ', ← mul_assoc, mul_comm h.q h.C, mul_assoc, mul_sum, mul_add]
        rw [Finset.sum_congr rfl fun k hk => by
          rw [← mul_assoc, ← pow_succ', ← Nat.sub_add_comm (mem_range_succ_iff.mp hk)]]
        simp [pow_zero, add_assoc]
      }
}

lemma weighted_sum_bound (hd : BddAbove (Set.range d)) (n : ℕ):
    h.weightedSum n ≤ (⨆ i, d i)^2 * (1/h.q) / (1/h.q - 1) := by {
  let ⟨q, q_range, C, C_pos, bound⟩ := h
  unfold weightedSum

  have hq₁ : 1/q ≥ 1 := by {
    simp
    apply one_le_inv_iff₀.mpr
    exact ⟨q_range.1, le_of_lt q_range.2⟩
  }
  have hq₂ : (1 / q) ^ (n + 1) ≥ 1 := one_le_pow₀ hq₁

  have h₁ : ∀ k, d k ≤ (⨆ i, d i) := by {
    intros k
    exact (le_ciSup_iff' hd).mpr fun b a ↦ a k
  }

  have h₂ : ∑ k ∈ (range (n + 1)), q^(n-k) = ∑ k ∈ (range (n + 1)), q^n/q^k := by {
    apply Finset.sum_congr rfl
    intros k hk
    rw [← NNReal.rpow_natCast]
    rw [Nat.cast_sub (mem_range_succ_iff.mp hk)]
    rw [NNReal.rpow_sub_natCast (ne_of_gt q_range.1)]
    simp
  }

  have h₃ : ∑ k ∈ range (n + 1), (1/q)^k = ((1/q)^(n+1) - 1)/(1/q - 1) := by {
    rw[← NNReal.coe_inj]
    push_cast [hq₁, hq₂]
    apply geom_sum_eq
    · simp [ne_of_lt q_range.2]
  }

  have h₄ : q^n * (1/q^(n+1) - 1)/(1/q - 1) = ((1/q) - q^n)/(1/q - 1) := by {
    rw [mul_tsub, mul_one, one_div]
    group
    rw [← zpow_add₀ (ne_of_gt q_range.1)]
    simp
  }

  have h₅ : (1/q) - q^n ≤ 1/q := by {
    have : q^n ≤ 1/q := by {
      trans 1
      · exact pow_le_one₀ (le_of_lt q_range.1) (le_of_lt q_range.2)
      · exact hq₁
    }
    rw [← NNReal.coe_le_coe]
    push_cast [this]
    simp
  }

  calc ∑ k ∈ (range (n + 1)), q^(n-k) * (d k)^2
    _ ≤ ∑ k ∈ (range (n + 1)), q^(n-k) * (⨆ i, d i)^2 := by gcongr; apply h₁
    _ = ∑ k ∈ (range (n + 1)), (⨆ i, d i)^2 * q^(n-k) := by simp_rw [mul_comm]
    _ = (⨆ i, d i)^2 * ∑ k ∈ range (n + 1), q^(n-k) := by simp [mul_sum]
    _ = (⨆ i, d i)^2 * ∑ k ∈ range (n + 1), q^n/q^k := by rw [h₂]
    _ = (⨆ i, d i)^2 * ∑ k ∈ range (n + 1), q^n * (1/q)^k := by field_simp
    _ = (⨆ i, d i)^2 * q^n * ∑ k ∈ range (n + 1), (1/q)^k := by simp [← mul_sum, mul_assoc]
    _ = (⨆ i, d i)^2 * (q^n * (1/q^(n+1) - 1)/(1/q - 1)) := by rw [h₃]; field_simp [mul_assoc]
    _ = (⨆ i, d i)^2 * ((1/q) - q^n)/(1/q - 1) := by rw [h₄, ← mul_div_assoc']
    _ ≤ (⨆ i, d i)^2 * (1/q)/(1/q - 1) := by gcongr
}

lemma estimator_bounded (hd : BddAbove (Set.range d)) : BddAbove (Set.range η) := by {
  let K := ((η 0)^2 + h.C * ((⨆ i, d i)^2 * (1/h.q)/(1/h.q - 1))) ⊔ ((η 0)^2)
  use NNReal.sqrt K

  intros x hx
  rcases hx with ⟨n,hn⟩
  rw [← hn]

  apply NNReal.le_sqrt_iff_sq_le.mpr
  by_cases hn : n = 0
  case pos =>
    unfold K
    rw [hn]
    apply le_max_right
  case neg =>
    have : n-1+1 = n := by rw [tsub_add_eq_add_tsub (pos_of_ne_zero hn), Nat.add_sub_assoc (by simp), Nat.sub_self 1, Nat.add_zero]
    calc (η n)^2
      _ = (η ((n-1)+1))^2 := by rw [this]
      _ ≤ h.upperBound (n-1) := by exact estimator_recursive_upper_bound h (n-1)
      _ = h.q^n * (η 0)^2 + h.C * h.weightedSum (n-1) := by {unfold upperBound; simp [this]}
      _ ≤ h.q^n * (η 0)^2 + h.C * ((⨆ i, d i)^2 * (1/h.q)/(1/h.q - 1)) := by rel [weighted_sum_bound h hd (n-1)]
      _ ≤ (η 0)^2 + h.C * ((⨆ i, d i)^2 * (1/h.q)/(1/h.q - 1)) := by {
        gcongr
        by_cases hη : (η 0)^2 = 0
        case pos =>
          simp [hη]
        case neg =>
          have : h.q^n ≤ 1 := by exact pow_le_one' (le_of_lt h.q_range.2) n
          rw [← mul_le_mul_right (pos_of_ne_zero hη)] at this
          simp at this
          assumption
      }
      _ ≤ K := by unfold K; apply le_max_left
}

lemma estimator_limsup_zero (hd : Tendsto d atTop (𝓝 0)) (hη₁ : BddAbove (Set.range η)) : limsup (η^2) atTop = 0 := by {
  let ⟨q, q_range, C, C_pos, bound⟩ := h

  apply smaller_q_eq_zero _ q q_range.2

  have hdc : Tendsto (C • d^2) atTop (𝓝 0) := by {
    let f : NNReal → NNReal := fun x ↦ C * x^2
    have hf : Continuous f := by continuity
    have hf0 : f 0 = 0 := by unfold f; simp

    change Tendsto (f ∘ d) atTop (𝓝 0)
    rw [← hf0]
    exact Tendsto.comp (hf.tendsto 0) hd
  }

  have hη₂ : BddAbove (Set.range (η^2)) := by {
    let f : NNReal → NNReal := fun x ↦ x^2
    change BddAbove (Set.range (f ∘ η))
    apply monotone_map_bdd_above_range (pow_left_mono 2) hη₁
  }

  have hη₃ : BddAbove (Set.range (q • η^2)) := by {
    let f : NNReal → NNReal := fun x ↦ q * x
    change BddAbove (Set.range (f ∘ (η^2)))
    apply monotone_map_bdd_above_range mul_left_mono hη₂
  }

  have h₁ : limsup ((η^2) ∘ (· + 1)) atTop ≤ limsup (q • η^2 + C • d^2) atTop := by {
    apply Filter.limsup_le_limsup
    · apply Filter.Eventually.of_forall
      intros x
      simp
      apply (bound x)
    · apply Filter.IsBoundedUnder.isCoboundedUnder_le
      apply BddBelow.isBoundedUnder_of_range
      apply nnreal_fun_bbd_below
    · apply BddAbove.isBoundedUnder_of_range
      apply BddAbove.range_add hη₃ <| Tendsto.bddAbove_range hdc
  }

  -- TODO: write these anonymous functions with pointwise operations
  have h₂ : limsup (q • η^2 + C • d^2) atTop ≤ limsup (q • η^2) atTop + limsup (C • d^2) atTop := by {
    rw [← NNReal.coe_le_coe]
    push_cast
    simp_rw [← NNReal.toReal_limsup]

    apply limsup_add_le ?cη_below ?cη_above ?cd_below ?cd_above
    case cη_below =>
      exact BddBelow.isBoundedUnder_of_range <| lift_bound_below _
    case cη_above =>
      exact BddAbove.isBoundedUnder_of_range <| lift_bound_above _ hη₃
    case cd_below =>
      exact Filter.IsBoundedUnder.isCoboundedUnder_le <| BddBelow.isBoundedUnder_of_range <| lift_bound_below _
    case cd_above =>
      exact BddAbove.isBoundedUnder_of_range <| lift_bound_above _ <| Tendsto.bddAbove_range hdc
  }

  calc limsup (η^2) atTop
    _ = limsup (λ n ↦ (η (n+1))^2) atTop := by rw [← Filter.limsup_nat_add _ 1]; rfl
    _ = limsup ((η^2) ∘ (· + 1)) atTop := by rfl
    _ ≤ limsup (q • η^2 + C • d^2) atTop := by exact h₁
    _ ≤ limsup (q • η^2) atTop + limsup (C • d^2) atTop := by exact h₂
    _ = limsup (q • η^2) atTop := by simp [Tendsto.limsup_eq hdc]
    _ = q * limsup (η^2) atTop := by exact nnreal_limsup_const_mul <| BddAbove.isBoundedUnder_of_range hη₂
    _ = q * limsup (η^2) atTop := by rfl
}

theorem convergence_of_estimator (hd_lim : Tendsto d atTop (𝓝 0)) : Tendsto (η^2) atTop (𝓝 0) := by {
  let hd_above := Tendsto.bddAbove_range hd_lim
  let hη_above := estimator_bounded h hd_above
  have hη2_above : BddAbove (Set.range (η^2)) := by {
    let f : NNReal → NNReal := fun x ↦ x^2
    change BddAbove (Set.range (f ∘ η))
    apply monotone_map_bdd_above_range (pow_left_mono 2)
    exact hη_above
  }
  have hη2_below : BddBelow (Set.range (η^2)) := by exact nnreal_fun_bbd_below _
  let hη_limsup := estimator_limsup_zero h hd_lim hη_above

  apply tendsto_of_liminf_eq_limsup
  case hinf =>
    apply nonpos_iff_eq_zero.mp
    rw [← hη_limsup]
    apply liminf_le_limsup
    · exact BddAbove.isBoundedUnder_of_range hη2_above
    · exact BddBelow.isBoundedUnder_of_range hη2_below
  case hsup => exact hη_limsup
  case h => exact BddAbove.isBoundedUnder_of_range hη2_above
  case h' => exact BddBelow.isBoundedUnder_of_range hη2_below
}

end EstimatorReduction
