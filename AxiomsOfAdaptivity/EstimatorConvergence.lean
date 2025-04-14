import Mathlib
open Filter
open TopologicalSpace
open BigOperators
open Finset
open scoped Topology

-- 4.18
def estimator_reduction (η : ℕ → NNReal) (d : ℕ → NNReal) :=
  ∃ q ∈ (Set.Ioo 0 1), ∃ C > 0, ∀ n, (η (n+1))^2 ≤ q * (η n)^2 + C * (d n)^2

lemma finset_sum_const (c : ℝ) (s : Finset ℕ) (f : ℕ → ℝ) :
  c * (∑ i ∈ s, f i) = ∑ i ∈ s, c * (f i) := by {
    exact mul_sum s f c
}

lemma estimator_upper_bound (η : ℕ → NNReal) (d : ℕ → NNReal) (h_est : estimator_reduction η d) :
  ∃ q ∈ (Set.Ioo 0 1), ∃ C > 0, ∀ n,
  (η (n+1))^2 ≤ q^(n+1) * (η 0)^2 + C * (∑ k ∈ (range (n + 1)), q^(n-k) * (d k)^2) := by {

  rcases h_est with ⟨q, hq, C, hC, hη⟩
  use q
  use hq
  use C
  use hC

  intros n
  induction' n with n ih
  · simp
    apply hη
  · calc
      η (n + 1 + 1) ^ 2 <= q * (η (n + 1))^2 + C * (d (n + 1))^2 := by apply hη
                      _ <= q * (q ^ (n + 1) * η 0 ^ 2 + C * ∑ k ∈ range (n + 1), q ^ (n - k) * d k ^ 2) + C * (d (n + 1))^2 := by simp [mul_le_mul_left hq.1, ih]
                      _ = q^(n+1+1) * (η 0)^2 + C * (∑ k ∈ (range (n + 1 + 1)), q^(n+1-k) * (d k)^2) := by {
                        nth_rw 2 [sum_range_succ]
                        rw [mul_add, ← mul_assoc, ← pow_succ', ← mul_assoc, mul_comm q C, mul_assoc, mul_sum, mul_add]
                        rw [Finset.sum_congr rfl fun x hx => by rw[← mul_assoc, ← pow_succ', ← Nat.sub_add_comm (by exact mem_range_succ_iff.mp hx)]] -- took me ages to come up with Nat.sub_add_comm
                        simp [pow_zero, add_assoc]
                      }
}

lemma estimator_bounded (η : ℕ → NNReal) (d : ℕ → NNReal) (hd : Tendsto d atTop (𝓝 0)) (h_est : estimator_reduction η d) : BddAbove (Set.range η) := by {
  have h_dbound : BddAbove (Set.range d) := by exact Tendsto.bddAbove_range hd
  rcases h_dbound with ⟨M, hM⟩
  reduce at hM

  rcases estimator_upper_bound η d h_est with ⟨q, hq, C, hC, hη⟩
  let K := ((η 0)^2 + C * (M^2 * (1/q)/(1/q - 1))) ⊔ ((η 0)^2)
  use NNReal.sqrt K
  intros x hx

  have terms : ∀ n, ∀ k ∈ range (n+1), q^(n-k) * (d k)^2 <= q^(n-k) * M^2 := by {
    intros n
    intros k hk
    have hran : (d k) ∈ Set.range d := by simp
    rw [mul_le_mul_left]
    exact pow_le_pow_left' (hM hran) 2
    exact pow_pos hq.1 (n - k)
  }

  have q_pow : ∀n, ∀ k ∈ range (n+1), q^(n-k) = q^n*(1/q)^(k) := by {
    intros n
    intros k hk
    rw [one_div]
    rw [← NNReal.rpow_natCast] -- took me ages to use `NNReal.` instead of `Real.` here
    rw [Nat.cast_sub (by exact mem_range_succ_iff.mp hk)]
    rw [NNReal.rpow_sub_natCast (by exact ne_of_gt hq.1)]
    simp only [NNReal.rpow_natCast, inv_pow]
    congr
  }

  have sum_bound : ∀ n, ∑ k ∈ (range (n + 1)), q^(n-k) * (d k)^2 <= M^2 * (1/q)/(1/q - 1) := by {
  intros n
  calc
    ∑ k ∈ (range (n + 1)), q^(n-k) * (d k)^2 <= ∑ k ∈ (range (n + 1)), q^(n-k) * M^2 := by exact Finset.sum_le_sum (terms n)
                                             _ = M^2 * ∑ k ∈ (range (n + 1)), q^(n-k) := by {
                                              rw [Finset.sum_congr rfl fun x hx => by rw[mul_comm]]
                                              simp[mul_sum]
                                             }
                                             _ = M^2 * ∑ k ∈ (range (n + 1)), q^n*(1/q)^k := by {
                                              rw [Finset.sum_congr rfl fun k hk => by {
                                                exact q_pow n k hk
                                                }]
                                             }
                                             _ = M^2 * q^n * ∑ k ∈ (range (n + 1)), (1/q)^k := by simp[← mul_sum, mul_assoc]
                                             _ = M^2 * q^n * ((1/q)^(n+1) - 1)/(1/q - 1) := by {
                                              have hqq : ((1:Real)/q) ≠ 1 := by {
                                                refine div_ne_one_of_ne ?_
                                                rw [← NNReal.coe_one, NNReal.ne_iff]
                                                exact ne_of_gt hq.2
                                              }
                                              rw[← NNReal.coe_inj]
                                              push_cast
                                              rw[geom_sum_eq hqq (n+1)]
                                              norm_cast
                                              rw[← NNReal.coe_one]
                                              have h_geone_pow : ∀ k:ℕ, k > 0 → (1/q)^k >= 1 := by {
                                                intros k hk
                                                simp
                                                have key : q^k < 1 := by exact Right.pow_lt_one_of_lt hk hq.2
                                                rw [one_le_inv_iff₀] -- need this because the sign might change, Right.one_le_inv_iff is not applicable
                                                constructor
                                                · exact pow_pos hq.1 k
                                                · exact le_of_lt key
                                              }
                                              have h_geone : 1/q >= 1 := by {
                                                rw [← pow_one (1/q)]
                                                exact h_geone_pow 1 Nat.one_pos
                                              }
                                              rw[← NNReal.coe_sub (h_geone_pow (n+1) (Nat.zero_lt_succ n))]
                                              rw[← NNReal.coe_sub h_geone]
                                              norm_cast
                                              simp[mul_div_assoc]
                                             }
                                             _ = M^2 * ((1/q) - q^n)/(1/q - 1) := by {
                                               simp only [mul_assoc]
                                               rw [mul_tsub]
                                               rw [mul_one]
                                               have key : q^n = q^(n+1)/q := by {
                                                rw [pow_succ']
                                                refine Eq.symm (mul_div_cancel_left₀ (q ^ n) (ne_of_gt hq.1))
                                               }
                                               nth_rw 1 [key]
                                               rw [div_mul_eq_mul_div, ← mul_pow, one_div, CommGroupWithZero.mul_inv_cancel q (ne_of_gt hq.1), one_pow]
                                               simp
                                             }
                                             _ <= M^2 * (1/q)/(1/q - 1) := by {
                                              have key : q^n <= 1 := by exact pow_le_one₀ (le_of_lt hq.1) (le_of_lt hq.2)
                                              by_cases h : M = 0
                                              case pos =>
                                                rw [h]
                                                simp
                                              case neg =>
                                                rw [mul_div_assoc, mul_div_assoc]
                                                rw [mul_le_mul_left (pow_two_pos_of_ne_zero h)]
                                                rw [div_le_div_iff_of_pos_right (by {rw[tsub_pos_iff_lt]; exact one_lt_one_div (hq.1) (hq.2)})]
                                                simp
                                             }
  }

  have sqrt : ∀n, (η (n+1))^2 ≤ K := by {
    intros n
    calc
      (η (n+1)) ^ 2 <= q^(n+1) * (η 0)^2 + C * (∑ k ∈ (range (n + 1)), q^(n-k) * (d k)^2) := by exact hη n
                  _ = q^(n+1) * (η 0)^2 + (C * (∑ k ∈ (range (n + 1)), q^(n-k) * (d k)^2)) := by simp
                  _ <= q^(n+1) * (η 0)^2 + C * (M^2 * (1/q)/(1/q - 1)) := by {
                    rw[add_le_add_iff_left, mul_le_mul_left hC]
                    exact sum_bound n
                  }
                  _ <= (η 0)^2 + C * (M^2 * (1/q)/(1/q - 1)) := by {
                    by_cases h : (η 0)^2 = 0
                    case pos =>
                      simp [h]
                    case neg =>
                      rw[add_le_add_iff_right]
                      nth_rw 2 [← mul_one ((η 0)^2)]
                      nth_rw 2 [mul_comm]
                      rw[mul_le_mul_right (pos_of_ne_zero h)]
                      exact le_of_lt (Right.pow_lt_one_of_lt (Nat.zero_lt_succ n) hq.2)
                  }
                  _ <= K := by {unfold K; apply le_max_left}
  }

  have sqrt2 : ∀n, (η n)^2 ≤ K := by {
    intros n
    by_cases h : n = 0
    case pos =>
      unfold K
      rw [h]
      apply le_max_right
    case neg =>
      have h_bound : (η (n-1+1))^2 ≤ K := by exact sqrt (n-1)
      rw [tsub_add_eq_add_tsub (pos_of_ne_zero h), Nat.add_sub_assoc (by simp), Nat.sub_self 1, Nat.add_zero] at h_bound
      exact h_bound
  }

  rcases hx with ⟨n,hn⟩
  rw [← hn]
  exact NNReal.le_sqrt_iff_sq_le.mpr (sqrt2 n)
}

-- maybe the calculations get easier when i use the Reals? i cant use most theorems
-- because the NNReals are not a field.

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

lemma nnreal_limsup_const_mul {u : ℕ → NNReal} {a : NNReal} (hu: IsBoundedUnder (fun x1 x2 ↦ x1 ≤ x2) atTop u):
    Filter.limsup (fun n => a * u n) atTop = a * Filter.limsup u atTop := by {
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

-- could be that limsup in NNReal is not what we want
-- unbounded functions have limsup 0
example : limsup (λ n : NNReal ↦ n) atTop = 0 := by {
  refine NNReal.limsup_of_not_isBoundedUnder ?_
  refine Filter.not_isBoundedUnder_of_tendsto_atTop ?_
  -- TODO understand what the heck this does
  exact fun ⦃U⦄ a ↦ a
}

-- we need to check what statement we need to show in order to conclude convergence to zero to state
-- the limsup result correctly

-- tendsto_of_liminf_eq_limsup should be fitting with a bit of extra work
-- and limsup = 0 is sufficient because we have to supply proofs for boundedness

theorem limsup_zero_of_estimator_reduction (η d : ℕ → NNReal) (hd : Tendsto d atTop (𝓝 0)) (h_est : estimator_reduction η d) (h_top : BddAbove (Set.range η)) : limsup (λ n ↦ (η n)^2) atTop = 0 := by {
  let h_est' := h_est
  rcases h_est with ⟨q, hq, C, hC, hη⟩

  have hdd : (Tendsto (fun n ↦ C * d n ^ 2) atTop (𝓝 0)) := by {
            let f : NNReal → NNReal := fun x ↦ C * x^2
            have hf : Continuous f := by continuity
            have h : (fun n ↦ C * d n ^ 2) = f ∘ d := by rfl
            have h' : f 0 = 0 := by {unfold f; simp}
            rw [h,← h']
            exact Tendsto.comp (hf.tendsto 0) hd
          }

  have hh : limsup (λ n ↦ (η (n+1))^2) atTop <= limsup (λ n ↦ q * (η n)^2 + C * (d n)^2) atTop := by {
    apply Filter.limsup_le_limsup
    case h =>
      apply Filter.Eventually.of_forall
      intros x
      simp
      apply (hη x)
    case hu =>
      exact Filter.IsBoundedUnder.isCoboundedUnder_le (BddBelow.isBoundedUnder_of_range (nnreal_fun_bbd_below (fun n ↦ η (n + 1) ^ 2)))
    case hv =>
      have hhh : BddAbove (Set.range fun n ↦ q * η n ^ 2 + C * d n ^ 2) := by {
        refine BddAbove.range_add ?_ ?_
        case refine_1 =>
          let f : NNReal → NNReal := fun x ↦ q * x^2
          have hm : Monotone f := by exact Monotone.const_mul' (pow_left_mono 2) q
          have hf : (fun n ↦ q * η n ^ 2) = f ∘ η := by rfl
          rw [hf, Set.range_comp]
          exact Monotone.map_bddAbove hm h_top
        case refine_2 =>
          exact Tendsto.bddAbove_range hdd
      }
      exact BddAbove.isBoundedUnder_of_range hhh
  }

  have hmul : limsup (λ n ↦ q * (η n)^2 + C * (d n)^2) atTop ≤ limsup (λ n ↦ q * (η n)^2) atTop := by {
    calc limsup (λ n ↦ q * (η n)^2 + C * (d n)^2) atTop = limsup ((λ n ↦ q * (η n)^2) + (λ n ↦ C * (d n)^2)) atTop := by rfl
                                                      _ <= limsup (λ n ↦ q * (η n)^2) atTop + limsup (λ n ↦ C * (d n)^2) atTop := by {
                                                        have h₁ : BddBelow (Set.range (fun n ↦ q * (η n) ^ 2)) := by apply nnreal_fun_bbd_below _
                                                        have h₂ : BddAbove (Set.range (fun n ↦ q * (η n) ^ 2)) := by {
                                                          -- TODO deduplicate
                                                          let f : NNReal → NNReal := fun x ↦ q * x^2
                                                          have hm : Monotone f := by exact Monotone.const_mul' (pow_left_mono 2) q
                                                          have hf : (fun n ↦ q * (η n) ^ 2) = f ∘ η := by rfl
                                                          rw [hf, Set.range_comp]
                                                          exact Monotone.map_bddAbove hm h_top
                                                        }
                                                        have h₃ : BddBelow (Set.range (λ n ↦ C * (d n)^2)) := by apply nnreal_fun_bbd_below _
                                                        have h₄ : BddAbove (Set.range (λ n ↦ C * (d n)^2)) := by exact Tendsto.bddAbove_range hdd

                                                        rw [← NNReal.coe_le_coe]
                                                        push_cast
                                                        simp_rw [← NNReal.toReal_limsup]

                                                        -- this is a monstrosity
                                                        apply limsup_add_le (BddBelow.isBoundedUnder_of_range (lift_bound_below (fun n ↦ q * (η n) ^ 2))) (BddAbove.isBoundedUnder_of_range (lift_bound_above (fun n ↦ q * (η n) ^ 2) h₂)) (Filter.IsBoundedUnder.isCoboundedUnder_le (BddBelow.isBoundedUnder_of_range (lift_bound_below (λ n ↦ C * (d n)^2)))) (BddAbove.isBoundedUnder_of_range (lift_bound_above (λ n ↦ C * (d n)^2) h₄))
                                                      }
                                                      _ = limsup (λ n ↦ q * (η n)^2) atTop := by {
                                                        have key : limsup (λ n ↦ C * (d n)^2) atTop = 0 := by {
                                                          exact Tendsto.limsup_eq hdd
                                                        }
                                                        simp [key]
                                                      }
  }

  let ls := limsup (λ n ↦ (η n)^2) atTop
  have key : ls <= q * ls := by {
    calc
      ls = limsup (λ n ↦ (η (n+1))^2) atTop := by {
        unfold ls
        rw [← Filter.limsup_nat_add _ 1]
        }
       _ <= limsup (λ n ↦ q * (η n)^2 + C * (d n)^2) atTop := by exact hh
       _ <= limsup (λ n ↦ q * (η n)^2) atTop := by exact hmul
       _ = q * limsup (λ n ↦ (η n)^2) atTop := by {
        have h₂ : BddAbove (Set.range (fun n ↦ (η n) ^ 2)) := by {
          -- TODO deduplicate
          let f : NNReal → NNReal := fun x ↦ x^2
          have hm : Monotone f := by exact pow_left_mono 2
          have hf : (fun n ↦ (η n) ^ 2) = f ∘ η := by rfl
          rw [hf, Set.range_comp]
          exact Monotone.map_bddAbove hm h_top
        }
        apply nnreal_limsup_const_mul (BddAbove.isBoundedUnder_of_range h₂)
       }
       _ = q * ls := by rfl
  }

  exact (smaller_q_eq_zero ls q hq.2 key)
}

theorem convergence_of_estimator (η d : ℕ → NNReal) (hd : Tendsto d atTop (𝓝 0)) (h_est : estimator_reduction η d) : Tendsto (λ n ↦ (η n)^2) atTop (𝓝 0) := by {
  have h_top : BddAbove (Set.range η) := by exact estimator_bounded η d hd h_est

  -- TODO rewrite this so that we dont have to restate all parameters here,
  -- mostly only hypothesises are required args, others are stated with {}
  have h_limsup : limsup (λ n ↦ (η n)^2) atTop = 0 := by exact limsup_zero_of_estimator_reduction η d hd h_est h_top

  have h_above : BddAbove (Set.range (fun n ↦ (η n) ^ 2)) := by {
        -- TODO deduplicate
        let f : NNReal → NNReal := fun x ↦ x^2
        have hm : Monotone f := by exact pow_left_mono 2
        have hf : (fun n ↦ (η n) ^ 2) = f ∘ η := by rfl
        rw [hf, Set.range_comp]
        exact Monotone.map_bddAbove hm h_top
      }
  have h_below : BddBelow (Set.range (fun n ↦ (η n) ^ 2)) := by exact nnreal_fun_bbd_below _

  have h_liminf : liminf (λ n ↦ (η n)^2) atTop <= 0 := by {
    rw[← h_limsup]
    exact liminf_le_limsup (BddAbove.isBoundedUnder_of_range h_above) (BddBelow.isBoundedUnder_of_range h_below)
  }

  have h_liminf' : liminf (λ n ↦ (η n)^2) atTop = 0 := by exact nonpos_iff_eq_zero.mp h_liminf
  refine tendsto_of_liminf_eq_limsup h_liminf' h_limsup (BddAbove.isBoundedUnder_of_range h_above) (BddBelow.isBoundedUnder_of_range h_below)
}
