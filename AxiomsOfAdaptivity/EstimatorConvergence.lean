import Mathlib
import AxiomsOfAdaptivity.Basics
import AxiomsOfAdaptivity.Summability

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
  exact fun _ a ↦ a
}

-- 4.18
structure SimpleEstimatorReduction (η d : ℕ → NNReal) where
  q : NNReal
  q_range : q ∈ Set.Ioo 0 1
  C : NNReal
  C_pos : C > 0
  bound : ∀ n, (η (n + 1))^2 ≤ q * (η n)^2 + C * (d n)^2

namespace SimpleEstimatorReduction

variable {η d : ℕ → NNReal} (h : SimpleEstimatorReduction η d)
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
    have : n-1+1 = n := Nat.succ_pred_eq_of_ne_zero hn
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
          have : h.q^n ≤ 1 := pow_le_one' (le_of_lt h.q_range.2) n
          rw [← mul_le_mul_right (pos_of_ne_zero hη)] at this
          simpa using this
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

theorem convergence_of_estimator_simple (hd_lim : Tendsto d atTop (𝓝 0)) : Tendsto (η^2) atTop (𝓝 0) := by {
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

-- TODO real estimator reduction
end SimpleEstimatorReduction

variable {α β : Type*} [DecidableEq α] [Lattice α] [OrderBot α] (alg : AdaptiveAlgorithm α β)

-- TODO Feischl: Which limit is meant in the a priori convergence and
-- how does the convergence of this d_seq to zero follow from that?
def d_seq n := alg.d (alg.𝒯 <| n + 1) (alg.U <| alg.𝒯 <| n + 1) (alg.U <| alg.𝒯 n)

-- TODO move all theorems about the algorithm into an algorithm namespace so that they
-- can be accessed with dot notation on the algorithm
theorem convergence_of_estimator (hd_seq_lim : Tendsto (d_seq alg) atTop (𝓝 0)) :
    Tendsto alg.glob_err_nat atTop (𝓝 0) := by {

  -- first define the object we want to apply the simplified convergence
  -- theorem to
  rcases alg.estimator_reduction_delta_exists with ⟨δ, hδ, ⟨hρ_est, hC_est⟩⟩

  let ρ_est := alg.ρ_est δ
  let C_est := alg.C_est δ

  have estimator_reduction := alg.estimator_reduction δ hδ hρ_est.2

  let d n := (d_seq alg n).toNNReal

  let est_red := {
    q := ρ_est.toNNReal,
    C := C_est.toNNReal,
    C_pos := by simpa using hC_est
    q_range := by simpa using hρ_est
    bound := by {
      intros n
      apply NNReal.coe_le_coe.mp
      push_cast

      have hd : d n = d_seq alg n := by {
        apply Real.coe_toNNReal
        apply alg.non_neg
      }

      have hq : ρ_est.toNNReal = ρ_est := by {
        apply Real.coe_toNNReal
        exact le_of_lt hρ_est.1
      }

      have hC : C_est.toNNReal = C_est := by {
        apply Real.coe_toNNReal
        exact le_of_lt hC_est
      }

      simp only [alg.hgη, hd, hq, hC]
      unfold d_seq
      exact estimator_reduction n
    }
  : SimpleEstimatorReduction alg.gη d}

  have hd_lim : Tendsto d atTop (𝓝 0) := by {
    rw [Eq.symm Real.toNNReal_zero]
    apply tendsto_real_toNNReal hd_seq_lim
  }

  conv =>
    enter [1, n]
    rw [← alg.hgη n]
    norm_cast
  rw [← NNReal.coe_zero]
  apply NNReal.tendsto_coe.mpr
  exact est_red.convergence_of_estimator_simple hd_lim
}

lemma cancel {δ a} (hδ : δ > 0) : a * (alg.C_rel^2 * alg.C_est δ / (alg.C_rel^2 * alg.C_est δ)) = a := by {
  apply mul_right_eq_self₀.mpr
  left
  apply EuclideanDomain.div_self
  apply ne_of_gt
  exact alg.C_rel_mul_C_est_pos hδ
}

-- Lemma 4.10
theorem summability : uniform_summability alg.gη := by {
  rcases alg.ε_qo_lt_est_consts with ⟨δ, hδ, hε_qo, hρ_est⟩
  -- TODO clean up the lt_est_consts lemma !!

  let v := alg.ε_qo * alg.C_rel^2 * alg.C_est δ
  have hv₁ : v < 1 - alg.ρ_est δ := by {
    calc v
      _ = alg.ε_qo * alg.C_rel^2 * alg.C_est δ := by rfl
      _ < (1 - alg.ρ_est δ) / (alg.C_rel^2 * alg.C_est δ) * alg.C_rel^2 * alg.C_est δ := by {
        gcongr
        · exact alg.C_est_pos hδ
        · exact pow_pos alg.hC_rel 2
      }
      _ = (1 - alg.ρ_est δ) * (alg.C_rel^2 * alg.C_est δ / (alg.C_rel^2 * alg.C_est δ)) := by {
        field_simp
        rw [mul_assoc]
      }
      _ = 1 - alg.ρ_est δ := by {
        exact cancel alg hδ
      }
  }
  have hv₂ : 0 ≤ v := by {
    simp [v, mul_assoc]
    apply Left.mul_nonneg alg.hε_qo.1
    exact le_of_lt <| alg.C_rel_mul_C_est_pos hδ
  }

  have : ∀ N l:ℕ, ∑ k ∈ range N, alg.glob_err_nat (k + l + 1) ≤ ∑ k ∈ range N, (alg.ρ_est δ + v) * alg.glob_err_nat (k + l) + alg.C_est δ * alg.C_qo * glob_err alg.η (alg.𝒯 l) (alg.U <| alg.𝒯 l) := by {
    intros N l
    calc ∑ k ∈ range N, alg.glob_err_nat (k + l + 1)
      _ ≤ ∑ k ∈ range N, (alg.ρ_est δ * alg.glob_err_nat (k + l) + alg.C_est δ * d_seq alg (k + l)^2) := by {
        gcongr with k hk
        exact alg.estimator_reduction δ hδ hρ_est (k+l)
      }
      _ = ∑ k ∈ range N, ((alg.ρ_est δ + v) * alg.glob_err_nat (k + l) + alg.C_est δ * (d_seq alg (k + l)^2 - v * (alg.C_est δ)⁻¹ * alg.glob_err_nat (k + l))) := by {
        congr
        funext k
        rw [add_mul, mul_sub]
        conv in _ - _ =>
          rhs
          rw [← mul_assoc]
          lhs
          tactic =>
            calc alg.C_est δ * (v * (alg.C_est δ)⁻¹)
              _ = (alg.C_est δ * (alg.C_est δ)⁻¹) * v := by ring
              _ = v := by rw [mul_inv_cancel₀ <| ne_of_gt <| alg.C_est_pos hδ, one_mul]

        ring
      }
      _ ≤ ∑ k ∈ range N, ((alg.ρ_est δ + v) * alg.glob_err_nat (k + l) + alg.C_est δ * (d_seq alg (k + l)^2 - v * (alg.C_est δ)⁻¹ * (alg.C_rel⁻¹ * alg.d (alg.𝒯 <| k + l) alg.u (alg.U <| alg.𝒯 <| k + l))^2)) := by {
        gcongr with k hk
        · exact le_of_lt <| alg.C_est_pos hδ
        · refine mul_nonneg hv₂ ?_
          exact inv_nonneg.mpr <| le_of_lt <| alg.C_est_pos hδ
        · rw [mul_pow]
          calc alg.C_rel⁻¹ ^ 2 * alg.d (alg.𝒯 (k + l)) alg.u (alg.U (alg.𝒯 (k + l))) ^ 2
            _ ≤ alg.C_rel⁻¹ ^ 2 * (alg.C_rel ^ 2 * alg.glob_err_nat (k + l)) := by {
              have := (sq_le_sq₀ (alg.non_neg _ _ _) ?_).mpr (alg.reliability <| alg.𝒯 <| k + l)
              swap
              · apply mul_nonneg
                · exact le_of_lt <| alg.hC_rel
                · apply Real.sqrt_nonneg
              simp [mul_pow, Real.sq_sqrt (glob_err_nonneg _ _ _)] at this
              unfold AdaptiveAlgorithm.glob_err_nat
              rel [this]
            }
            _ = alg.glob_err_nat (k + l) := by {
              rw [← mul_assoc, ← mul_pow, inv_mul_cancel₀ <| ne_of_gt <| alg.hC_rel]
              simp
            }
      }
      _ = ∑ k ∈ range N, ((alg.ρ_est δ + v) * alg.glob_err_nat (k + l) + alg.C_est δ * (d_seq alg (k + l)^2 - v / (alg.C_rel^2 * alg.C_est δ) * (alg.d (alg.𝒯 <| k + l) alg.u (alg.U <| alg.𝒯 <| k + l))^2)) := by {
        field_simp
        rw [mul_comm]
      }
      _ = ∑ k ∈ range N, ((alg.ρ_est δ + v) * alg.glob_err_nat (k + l) + alg.C_est δ * (d_seq alg (k + l)^2 - alg.ε_qo * alg.d (alg.𝒯 <| k + l) alg.u (alg.U <| alg.𝒯 <| k + l)^2)) := by {
        dsimp [v]
        rw [mul_assoc, EuclideanDomain.mul_div_assoc, cancel alg hδ]
        · exact dvd_of_eq rfl
      }
      _ = ∑ k ∈ range N, (alg.ρ_est δ + v) * alg.glob_err_nat (k + l) + alg.C_est δ * ∑ k ∈ range N, (d_seq alg (k + l)^2 - alg.ε_qo * alg.d (alg.𝒯 <| k + l) alg.u (alg.U <| alg.𝒯 <| k + l)^2) := by {
        rw [Finset.sum_add_distrib]
        conv =>
          lhs
          rhs
          rw [← Finset.mul_sum]
      }
      _ ≤ ∑ k ∈ range N, (alg.ρ_est δ + v) * alg.glob_err_nat (k + l) + alg.C_est δ * alg.C_qo * glob_err alg.η (alg.𝒯 l) (alg.U <| alg.𝒯 l) := by {
        unfold d_seq
        have := alg.a3 l N
        apply add_le_add (by simp)
        rw [mul_assoc]
        exact (mul_le_mul_left <| alg.C_est_pos hδ).mpr this
      }
  }

  have : ∀ N l:ℕ, (1-(alg.ρ_est δ + v)) * ∑ k ∈ range N, alg.glob_err_nat (k + l + 1) ≤ (alg.C_est δ * alg.C_qo + alg.ρ_est δ + v) * alg.glob_err_nat l := by {
    intros N l
    calc (1-(alg.ρ_est δ + v)) * ∑ k ∈ range N, alg.glob_err_nat (k + l + 1)
      _ = (1-(alg.ρ_est δ + v)) * (∑ k ∈ range N, alg.glob_err_nat (k + l + 1) + alg.glob_err_nat l - alg.glob_err_nat l) := by ring
      _ = (1-(alg.ρ_est δ + v)) * (∑ k ∈ range (N + 1), alg.glob_err_nat (k + l) - alg.glob_err_nat l) := by {
        congr
        rw [Finset.sum_range_succ']
        conv =>
          rhs
          congr
          · rhs
            intro k
            rw [Nat.add_right_comm]
          · simp
      }
      _ = (1-(alg.ρ_est δ + v)) * ∑ k ∈ range (N + 1), alg.glob_err_nat (k + l) - (1-(alg.ρ_est δ + v)) * alg.glob_err_nat l := by ring
      _ = (1-(alg.ρ_est δ + v)) * (∑ k ∈ range N, alg.glob_err_nat (k + l) + alg.glob_err_nat (N + l)) - (1-(alg.ρ_est δ + v)) * alg.glob_err_nat l := by {
        rw [Finset.sum_range_succ]
      }
      _ ≤ (1-(alg.ρ_est δ + v)) * ∑ k ∈ range N, alg.glob_err_nat (k + l) + alg.glob_err_nat (N + l) - (1-(alg.ρ_est δ + v)) * alg.glob_err_nat l := by {
        rw [mul_add]
        gcongr
        apply mul_le_of_le_one_left
        · exact alg.glob_err_nat_nonneg _
        · rw [← sub_sub]
          linarith [hv₁, hv₂, alg.ρ_est_pos hδ]
      }
      _ = ∑ k ∈ range N, alg.glob_err_nat (k + l) - (alg.ρ_est δ + v) * ∑ k ∈ range N, alg.glob_err_nat (k + l) + alg.glob_err_nat (N + l) - alg.glob_err_nat l + (alg.ρ_est δ + v) * alg.glob_err_nat l := by {
        simp [sub_mul, one_mul, sub_add]
      }
      _ = ∑ k ∈ range (N+1), alg.glob_err_nat (k + l) - (alg.ρ_est δ + v) * ∑ k ∈ range N, alg.glob_err_nat (k + l) - alg.glob_err_nat l + (alg.ρ_est δ + v) * alg.glob_err_nat l := by {
        rw [Finset.sum_range_succ]
        ring
      }
      _ = ∑ k ∈ range N, alg.glob_err_nat (k + l + 1) - (alg.ρ_est δ + v) * ∑ k ∈ range N, alg.glob_err_nat (k + l) + (alg.ρ_est δ + v) * alg.glob_err_nat l := by {
        -- TODO this is the same as the second step without the factor in front
        rw [Finset.sum_range_succ']
        conv =>
          enter [1,1,1,1]
          congr
          · rhs
            intro k
            rw [Nat.add_right_comm]
          · simp
        ring
      }
      _ ≤ ∑ k ∈ range N, (alg.ρ_est δ + v) * alg.glob_err_nat (k + l)
        + alg.C_est δ * alg.C_qo * glob_err alg.η (alg.𝒯 l) (alg.U <| alg.𝒯 l)
        - (alg.ρ_est δ + v) * ∑ k ∈ range N, alg.glob_err_nat (k + l)
        + (alg.ρ_est δ + v) * alg.glob_err_nat l := by {
        rel [this N l]
      }
      _ = alg.C_est δ * alg.C_qo * glob_err alg.η (alg.𝒯 l) (alg.U <| alg.𝒯 l) + (alg.ρ_est δ + v) * alg.glob_err_nat l := by {
        rw [Finset.mul_sum]
        ring
      }
      _ = (alg.C_est δ * alg.C_qo + alg.ρ_est δ + v) * alg.glob_err_nat l := by {
        unfold AdaptiveAlgorithm.glob_err_nat
        ring
      }
  }

  let C := (alg.C_est δ * alg.C_qo + alg.ρ_est δ + v)/(1-(alg.ρ_est δ + v))

  have key : ∀ N l:ℕ, ∑ k ∈ range N, alg.glob_err_nat (k + l + 1) ≤ C * alg.glob_err_nat l := by {
    intros N l
    unfold C
    rw [div_mul_eq_mul_div₀]
    apply (le_div_iff₀ ?_).mpr
    · rw [mul_comm]
      apply this
    · linarith [hv₁]
  }

  have summable : Summable alg.glob_err_nat := by {
    apply (summable_nat_add_iff 1).mp
    apply summable_of_sum_range_le
    · intros n
      apply alg.glob_err_nat_nonneg

    have := fun N ↦ key N 0
    simpa using this
  }

  constructor
  · rw [← NNReal.summable_coe]
    conv =>
      arg 1
      intro n
      simp
      rw [alg.hgη n]
    exact summable
  · have C_pos : C > 0 := by {
      refine (lt_div_iff₀' ?_).mpr ?_
      · linarith [hv₁]
      · simp only [mul_zero]
        refine Left.add_pos_of_pos_of_nonneg ?_ hv₂
        refine add_pos ?_ <| alg.ρ_est_pos hδ
        apply mul_pos (alg.C_est_pos hδ)
        linarith [alg.hC_qo]
    }

    have C_cast : ↑C.toNNReal = C := by {
      rw [Real.coe_toNNReal]
      exact le_of_lt C_pos
    }

    use C.toNNReal
    refine ⟨Real.toNNReal_pos.mpr C_pos, ?_⟩

    intros l
    apply NNReal.coe_le_coe.mp
    push_cast
    rw [C_cast]
    simp only [Pi.pow_apply, NNReal.coe_pow, alg.hgη l]
    conv =>
      lhs
      arg 1
      intro k
      rw [alg.hgη _]
    refine Real.tsum_le_of_sum_range_le ?_ fun n ↦ key n l
    intros n
    apply alg.glob_err_nat_nonneg
}
