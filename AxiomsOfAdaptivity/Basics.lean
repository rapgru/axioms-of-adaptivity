import Mathlib
import AxiomsOfAdaptivity.Mesh
import AxiomsOfAdaptivity.Util

open Finset

variable {α: Type*} [DecidableEq α] [Lattice α] [OrderBot α]

-- ANCHOR: RefinementIndicator
abbrev RefinementIndicator (α : Type*) [DecidableEq α] [Lattice α] [OrderBot α] (β : Type*) :=
  Mesh α → β → α → ℝ
-- ANCHOR_END: RefinementIndicator

-- ANCHOR: beta
variable {β : Type*}
-- ANCHOR_END: beta

-- ANCHOR: gη2
def gη2 (ri: RefinementIndicator α β) (triang: Mesh α) v :=
  ∑ t ∈ triang, (ri triang v t)^2
-- ANCHOR_END: gη2

theorem gη2_nonneg (ri: RefinementIndicator α β) (triang: Mesh α) v : 0 ≤ gη2 ri triang v := by {
  apply sum_nonneg
  exact fun _ _ ↦ sq_nonneg _
}

/- This indexed supremum (iSup) looks like this after `dsimp [iSup]`, quite clever.
sSup
    (Set.range fun δ ↦
      sSup
        (Set.range fun h ↦
          (1 - (1 + δ) * (1 - (1 - alg.ρ_red) * alg.θ)) / (alg.C_rel ^ 2 * (alg.C_red + (1 + δ⁻¹) * alg.C_stab ^ 2)))) -/
private noncomputable def ε_qos' (ρ_red C_rel C_red C_stab θ : ℝ) := ⨆ δ > 0, (1-(1+δ)*(1-(1-ρ_red)*θ)) / (C_rel^2 * (C_red + (1+δ⁻¹)*C_stab^2))
private def C_rel' (C_Δ C_drel : ℝ) := C_Δ * C_drel

-- ANCHOR: AdaptiveAlgorithm
structure AdaptiveAlgorithm (α β: Type*) [DecidableEq α] [Lattice α] [OrderBot α] where
  -- Numerical solver --
  U : Mesh α → β

  -- Limit --
  u : β

  -- Refinement indicator --
  η : RefinementIndicator α β
  hη : η ≥ 0

  -- Error measure --
  d : Mesh α → β → β → ℝ
  C_Δ : ℝ
  hC_Δ : 0 < C_Δ
  non_neg : ∀ T v w, d T v w ≥ 0
  quasi_symmetry : ∀ T v w, d T v w ≤ C_Δ * d T w v
  quasi_triangle_ineq : ∀ T v w y, C_Δ⁻¹ * d T v y ≤ d T v w + d T w y
  -- Because we assume reliability directly compatibility is not used
  -- compatibility: ∀ T v w, ∀ T' ≤ T, d T' v w = d T v w
  further_approximation : ∀ T, ∀ ε > 0, ∃ T' ≤ T, d T' u (U T') ≤ ε

  -- Triangulation sequence --
  𝒯 : ℕ → Mesh α
  h𝒯 : ∀ l, 𝒯 (Nat.succ l) ≤ 𝒯 l

  -- Dörfler marking --
  θ : ℝ
  hθ : θ ∈ Set.Ioc 0 1
  ℳ : ℕ → Mesh α
  -- Equation (2.5)
  -- Slightly stronger than AoA because it assumes the selected subset is
  -- of minimal instead of almost minimal cardinality
  hℳ : ∀ l,
    let doerfler M :=
      θ * gη2 η (𝒯 l) (U <| 𝒯 l) ≤ ∑ t ∈ M, η (𝒯 l) (U <| 𝒯 l) t ^ 2
    ℳ l ⊆ (𝒯 l \ 𝒯 (l+1))
    ∧ doerfler (ℳ l)
    ∧ ∀ M' ⊆ 𝒯 l, doerfler M' → (ℳ l).card ≤ M'.card

  -- A1: stability on non-refined element domains --
  C_stab : ℝ
  hC_stab : C_stab > 0
  a1 : ∀ T : Mesh α, ∀ T' ≤ T, ∀ S ⊆ T ∩ T', ∀ v v',
    |√(∑ t ∈ S, η T' v' t ^ 2) - √(∑ t ∈ S, η T v t ^ 2)| ≤ C_stab * d T' v' v

  -- A2: reduction property on refined elements --
  ρ_red : ℝ
  hρ_red : ρ_red ∈ Set.Ioo 0 1
  C_red : ℝ
  hC_red : 0 < C_red
  a2 : ∀ T : Mesh α, ∀ T' ≤ T,
    ∑ t ∈ T' \ T, η T' (U T') t ^ 2 ≤ ρ_red * ∑ t ∈ T \ T', η T (U T) t ^ 2 + C_red * d T' (U T') (U T) ^ 2

  -- A4: reliability --
  C_drel : ℝ
  hC_drel : 0 < C_drel
  -- This is a result from A4 and the compatibility condition of the measure d (Lemma 3.4).
  -- Because this proof is not formalized we assume this result instead of A4.
  reliability' : ∀ T, d T u (U T) ≤ C_rel' C_Δ C_drel * √(gη2 η T (U T))

  -- A3: general quasi-orthogonality --
  -- Comes last so that all constants are already available
  ε_qo : ℝ
  hε_qo' : 0 ≤ ε_qo ∧ ε_qo < ε_qos' ρ_red (C_rel' C_Δ C_drel) C_red C_stab θ
  C_qo : ℝ
  hC_qo : C_qo ≥ 1
  -- Here n + 1 is the number of summands, we don't need N ≥ l from AoA
  a3 : ∀ l n,
    ∑ k ∈ range n, (d (𝒯 <| k + l + 1) (U <| 𝒯 <| k + l + 1) (U <| 𝒯 <| k + l) ^ 2 - ε_qo * d (𝒯 <| k + l) u (U <| 𝒯 <| k + l) ^ 2)
    ≤ C_qo * gη2 η (𝒯 l) (U <| 𝒯 l)
-- ANCHOR_END: AdaptiveAlgorithm

namespace AdaptiveAlgorithm

-- ANCHOR: alg
variable (alg : AdaptiveAlgorithm α β)
include alg
-- ANCHOR_END: alg

-- ANCHOR: lemma47_consts
def ρ_est δ := (1+δ) * (1 - (1 - alg.ρ_red) * alg.θ)
noncomputable def C_est δ := alg.C_red + (1 + δ⁻¹) * alg.C_stab ^ 2
-- ANCHOR_END: lemma47_consts

-- redefinitions for general field access
def C_rel := C_rel' alg.C_Δ alg.C_drel
noncomputable def ε_qos := ε_qos' alg.ρ_red alg.C_rel alg.C_red alg.C_stab alg.θ
lemma reliability : ∀ T, alg.d T alg.u (alg.U T) ≤ alg.C_rel * √(gη2 alg.η T (alg.U T)) := alg.reliability'

-- ANCHOR: seq_abbrev
def gη2_seq l := gη2 alg.η (alg.𝒯 <| l) (alg.U <| alg.𝒯 <| l)
noncomputable def nn_gη_seq n := NNReal.sqrt (alg.gη2_seq n).toNNReal
-- ANCHOR_END: seq_abbrev

-- lemmas for constants
lemma hε_qo : 0 ≤ alg.ε_qo ∧ alg.ε_qo < alg.ε_qos := by {
  exact alg.hε_qo'
}

lemma hC_rel : 0 < alg.C_rel := Left.mul_pos alg.hC_Δ alg.hC_drel

lemma C_est_pos {δ} (hδ : δ > 0) : 0 < alg.C_est δ := by {
  apply Left.add_pos_of_pos_of_nonneg alg.hC_red
  apply mul_nonneg _ (sq_nonneg _)
  apply add_nonneg (zero_le_one' ℝ)
  apply inv_nonneg.mpr
  exact le_of_lt hδ
}

lemma C_rel_mul_C_est_pos {δ} (hδ : δ > 0) : 0 < alg.C_rel ^ 2 * alg.C_est δ := by {
  apply mul_pos
  · exact pow_pos alg.hC_rel 2
  · exact alg.C_est_pos hδ
}

-- TODO This is absolutely illlegible
lemma ε_qo_lt_est_consts : ∃ δ > 0, alg.ε_qo < (1 - alg.ρ_est δ) / (alg.C_rel^2 * alg.C_est δ) ∧ alg.ρ_est δ < 1 := by {
  rcases @Real.add_neg_lt_sSup (Set.range fun δ ↦ sSup (Set.range fun (h:δ > 0) ↦ (1 - (1 + δ) * (1 - (1 - alg.ρ_red) * alg.θ)) / (alg.C_rel ^ 2 * (alg.C_red + (1 + δ⁻¹) * alg.C_stab ^ 2)))) (by {
    apply Set.range_nonempty
  }) (alg.ε_qo - alg.ε_qos) (sub_neg.mpr alg.hε_qo.2) with ⟨a, ha⟩

  conv at ha =>
    rhs
    lhs
    lhs
    change alg.ε_qos

  rcases Set.mem_range.mp ha.1 with ⟨δ, hδ⟩
  use δ

  have : (Set.range fun (h:δ > 0) ↦
      (1 - (1 + δ) * (1 - (1 - alg.ρ_red) * alg.θ)) / (alg.C_rel ^ 2 * (alg.C_red + (1 + δ⁻¹) * alg.C_stab ^ 2))) ≠ ∅ := by {
    by_contra h
    have : a = 0 := by {
      rw [← hδ, h]
      exact Real.sSup_empty
    }
    have : ¬ a = 0 := by {
      apply ne_of_gt
      linarith [ha.2, alg.hε_qo]
    }
    contradiction
  }

  rcases Set.nonempty_iff_ne_empty.mpr this with ⟨b, hb⟩
  rcases Set.mem_range.mp hb with ⟨hδ', hbb⟩
  constructor
  · exact hδ'

  simp at ha

  have key : alg.ε_qo < (1 - alg.ρ_est δ) / (alg.C_rel^2 * alg.C_est δ) := by {
    unfold ρ_est C_est
    rw [hbb]
    have : Nonempty (δ > 0) := Nonempty.intro hδ'
    have : (Set.range fun (h:δ > 0) ↦
        (1 - (1 + δ) * (1 - (1 - alg.ρ_red) * alg.θ)) / (alg.C_rel ^ 2 * (alg.C_red + (1 + δ⁻¹) * alg.C_stab ^ 2))) = {(1 - (1 + δ) * (1 - (1 - alg.ρ_red) * alg.θ)) / (alg.C_rel ^ 2 * (alg.C_red + (1 + δ⁻¹) * alg.C_stab ^ 2))} := by {
      apply Set.range_const
    }
    have : a = b := by {
      calc a
        _ = sSup (Set.range fun h ↦ (1 - (1 + δ) * (1 - (1 - alg.ρ_red) * alg.θ)) / (alg.C_rel ^ 2 * (alg.C_red + (1 + δ⁻¹) * alg.C_stab ^ 2))) := by {
          rw [hδ]
        }
        _ = (1 - (1 + δ) * (1 - (1 - alg.ρ_red) * alg.θ)) / (alg.C_rel ^ 2 * (alg.C_red + (1 + δ⁻¹) * alg.C_stab ^ 2)) := by {
          rw [this]
          apply csSup_singleton
        }
        _ = b := by {
          rw [hbb]
        }
    }
    rw [← this]
    exact ha.2
  }

  constructor
  · unfold ρ_est C_est
    exact key
  · have : 0 < 1 - alg.ρ_est δ := by {
      have := by calc 0
        _ ≤ alg.ε_qo := alg.hε_qo.1
        _ < (1 - alg.ρ_est δ) / (alg.C_rel^2 * alg.C_est δ) := key

      refine (div_pos_iff_of_pos_right ?_).mp this
      exact alg.C_rel_mul_C_est_pos hδ'
    }
    linarith
}

theorem gη2_seq_nonneg :
  0 ≤ gη2_seq alg := by {
    intros l
    -- example where simp alone does not work without
    -- specifying a closing theorem to use
    simpa using gη2_nonneg _ _ _
}

lemma hnn_gη_seq : ∀ n, alg.nn_gη_seq n ^ 2 = alg.gη2_seq n := by {
  intros n
  unfold nn_gη_seq
  push_cast
  rw [Real.coe_toNNReal]
  apply Real.sq_sqrt
  all_goals exact alg.gη2_seq_nonneg n
}

-- ANCHOR: doerfler_for_refined_elements
lemma doerfler_for_refined_elements :
    ∀ l, alg.θ * gη2_seq alg l
      ≤ ∑ t ∈ (alg.𝒯 l \ alg.𝒯 (l+1)), alg.η (alg.𝒯 l) (alg.U <| alg.𝒯 l) t ^ 2 := by {
  intros l
  calc alg.θ * gη2_seq alg l
    _ ≤ ∑ t ∈ alg.ℳ l, alg.η (alg.𝒯 l) (alg.U <| alg.𝒯 l) t ^ 2 := by exact (alg.hℳ l).2.1
    _ ≤ ∑ t ∈ (alg.𝒯 l \ alg.𝒯 (l+1)), alg.η (alg.𝒯 l) (alg.U <| alg.𝒯 l) t ^ 2 := by {
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · exact (alg.hℳ l).1
      · exact fun _ _ _ ↦ sq_nonneg _
    }
}
-- ANCHOR_END: doerfler_for_refined_elements

-- ρ_est is linear, positive rate is the key to monotonicity
lemma ρ_est_pos_rate : 0 < 1 - (1 - alg.ρ_red) * alg.θ := by {
  field_simp
  apply mul_lt_one_of_nonneg_of_lt_one_left
  · simpa using le_of_lt alg.hρ_red.2
  · simpa using alg.hρ_red.1
  · exact alg.hθ.2
}

lemma ρ_est_strict_mono : StrictMono alg.ρ_est := by {
  intros a b hab
  unfold AdaptiveAlgorithm.ρ_est
  have := alg.ρ_est_pos_rate
  gcongr
}

lemma ρ_est_pos {δ} (hδ : δ > 0) : 0 < alg.ρ_est δ := by {
  calc alg.ρ_est δ
    _ > alg.ρ_est 0 := alg.ρ_est_strict_mono hδ
    _ > 0 := by {
      unfold AdaptiveAlgorithm.ρ_est
      simp [alg.ρ_est_pos_rate]
    }
}

lemma estimator_reduction_delta_exists : ∃ δ > 0, alg.ρ_est δ ∈ Set.Ioo 0 1 ∧ 0 < alg.C_est δ := by {
  let δ := 1/2 * ((1 - alg.ρ_red) * alg.θ * (1 - (1 - alg.ρ_red) * alg.θ)⁻¹)

  -- 2*delta is positive
  have hδ_pre_pos : 0 < (1 - alg.ρ_red) * alg.θ * (1 - (1 - alg.ρ_red) * alg.θ)⁻¹ := by {
    apply mul_pos _ (inv_pos.mpr alg.ρ_est_pos_rate)
    simp [sub_mul]
    exact mul_lt_of_lt_one_left alg.hθ.1 alg.hρ_red.2
  }
  have hδ : 0 < δ := by {unfold δ; simp [hδ_pre_pos]}

  use δ

  -- TODO: when working with Set.Ioo 0 1 so much, maybe it is worth it to add
  -- a type for this interval that has simp theorems for operations that
  -- stay inside the interval. for example 1/2 * x or 1 - x.

  -- example where refine is a perfect match instead of apply
  refine ⟨hδ, ?ρ_est_range, ?C_est_pos⟩
  case ρ_est_range =>
    constructor
    · exact alg.ρ_est_pos hδ
    · calc alg.ρ_est δ
        _ < alg.ρ_est ((1 - alg.ρ_red) * alg.θ * (1 - (1 - alg.ρ_red) * alg.θ)⁻¹) := by {
          apply alg.ρ_est_strict_mono
          apply mul_lt_of_lt_one_left hδ_pre_pos
          simp [two_inv_lt_one]
        }
        _ = 1 := by {
          unfold AdaptiveAlgorithm.ρ_est
          rw [add_mul, mul_assoc, inv_mul_cancel₀ <| Ne.symm (ne_of_lt alg.ρ_est_pos_rate)]
          ring
        }
  case C_est_pos =>
    exact alg.C_est_pos hδ
}

-- Lemma 4.7
theorem estimator_reduction : ∀ δ > 0, (alg.ρ_est δ < 1) →
    ∀ l, alg.gη2_seq (l + 1)
         ≤ alg.ρ_est δ * alg.gη2_seq l
           + alg.C_est δ * alg.d (alg.𝒯 <| l + 1) (alg.U <| alg.𝒯 <| l+1) (alg.U <| alg.𝒯 <| l) ^ 2 := by {
  -- ANCHOR: estimator_reduction_1
  intros δ hδ hρ_est l

  let summand n t := alg.η (alg.𝒯 n) (alg.U <| alg.𝒯 <| n) t ^ 2
  let distance n := alg.d (alg.𝒯 <| n + 1) (alg.U <| alg.𝒯 <| n + 1) (alg.U <| alg.𝒯 <| n) ^ 2
  -- ANCHOR_END: estimator_reduction_1

  -- ANCHOR: estimator_reduction_2
  calc gη2_seq alg (l + 1)
    _ = ∑ t ∈ alg.𝒯 (l + 1) \ alg.𝒯 l, summand (l+1) t
        + ∑ t ∈ alg.𝒯 l ∩ alg.𝒯 (l+1), summand (l+1) t := by {
      unfold gη2_seq gη2
      have h_eq : (alg.𝒯 (l + 1)).val = (↑(alg.𝒯 (l + 1)) \ ↑(alg.𝒯 l)) ∪ (↑(alg.𝒯 (l + 1)) ∩ ↑(alg.𝒯 l)) := by {
        exact Eq.symm (sdiff_union_inter _ _)
      }
      nth_rw 1 [h_eq]
      simp [sum_union (disjoint_sdiff_inter _ _)]
      nth_rw 1 [inter_comm]
    }
    -- ANCHOR_END: estimator_reduction_2
    -- ANCHOR: estimator_reduction_3
    _ ≤ alg.ρ_red * ∑ t ∈ alg.𝒯 l \ alg.𝒯 (l + 1), summand l t
        + alg.C_red * distance l
        + (∑ t ∈ alg.𝒯 l ∩ alg.𝒯 (l + 1), summand (l + 1) t) := by
      rel[alg.a2 (alg.𝒯 l) (alg.𝒯 <| l + 1) (alg.h𝒯 l)]
    -- ANCHOR_END: estimator_reduction_3
    -- ANCHOR: estimator_reduction_4
    _ ≤ alg.ρ_red * ∑ t ∈ alg.𝒯 l \ alg.𝒯 (l + 1), summand l t
        + alg.C_red * distance l
        + ((1 + δ) * ∑ t ∈ alg.𝒯 l ∩ alg.𝒯 (l + 1), summand l t
        + (1 + δ⁻¹) * (alg.C_stab ^ 2 * distance l)) := by {
      have := alg.a1
        (alg.𝒯 l)
        (alg.𝒯 <| l + 1)
        (alg.h𝒯 l)
        (alg.𝒯 l ∩ alg.𝒯 (l + 1))
        (fun _ a ↦ a)
        (alg.U <| alg.𝒯 <| l)
        (alg.U <| alg.𝒯 <| l + 1)
      have := square_estimate_of_small_distance (Real.sqrt_nonneg _) this
      have h₁ : 0 ≤ alg.C_stab * alg.d (alg.𝒯 (l + 1)) (alg.U (alg.𝒯 (l + 1))) (alg.U (alg.𝒯 l)) := by {
        apply mul_nonneg (le_of_lt alg.hC_stab)
        apply alg.non_neg
      }
      have := le_trans this <| sum_square_le_square_sum (Real.sqrt_nonneg _) h₁ δ hδ

      rw [Real.sq_sqrt, Real.sq_sqrt, mul_pow] at this
      change ∑ t ∈ alg.𝒯 l ∩ alg.𝒯 (l + 1), summand (l + 1) t ≤ (1 + δ) * ∑ t ∈ alg.𝒯 l ∩ alg.𝒯 (l + 1), summand l t + (1 + δ⁻¹) * (alg.C_stab ^ 2 * distance l) at this
      rel [this]
      all_goals apply_rules [sum_nonneg', fun _ ↦ sq_nonneg _]
    }
    -- ANCHOR_END: estimator_reduction_4
    -- ANCHOR: estimator_reduction_5
    _ = alg.ρ_red * ∑ t ∈ alg.𝒯 l \ alg.𝒯 (l+1), summand l t
        + (1+δ) * ∑ t ∈ alg.𝒯 l ∩ alg.𝒯 (l+1), summand l t
        + (alg.C_red + (1 + δ⁻¹) * alg.C_stab ^ 2) * distance l := by ring
    -- ANCHOR_END: estimator_reduction_5
    -- ANCHOR: estimator_reduction_6
    _ = alg.ρ_red * ∑ t ∈ alg.𝒯 l \ alg.𝒯 (l+1), summand l t
        + (1+δ) * (gη2_seq alg l -  ∑ t ∈ alg.𝒯 l \ alg.𝒯 (l+1), summand l t)
        + (alg.C_red + (1 + δ⁻¹) * alg.C_stab ^ 2) * distance l := by {
      congr
      have h_eq : (alg.𝒯 l).val = (↑(alg.𝒯 l) \ ↑(alg.𝒯 (l + 1))) ∪ (↑(alg.𝒯 l) ∩ ↑(alg.𝒯 (l+1))) := by exact Eq.symm (sdiff_union_inter _ _)
      have h_dis: @Disjoint (Finset α) Finset.partialOrder Finset.instOrderBot (alg.𝒯 l \ alg.𝒯 (l + 1)) (alg.𝒯 l ∩ alg.𝒯 (l+1)) := by {
        exact disjoint_sdiff_inter _ _
      }
      unfold gη2_seq gη2
      nth_rw 2 [h_eq]
      rw [sum_union (disjoint_sdiff_inter _  _)]
      ring
    }
    -- ANCHOR_END: estimator_reduction_6
    -- ANCHOR: estimator_reduction_7
    _ ≤ (1+δ) * alg.ρ_red * ∑ t ∈ alg.𝒯 l \ alg.𝒯 (l+1), summand l t
        + (1+δ) * (gη2_seq alg l - ∑ t ∈ alg.𝒯 l \ alg.𝒯 (l+1), summand l t)
        + (alg.C_red + (1 + δ⁻¹) * alg.C_stab ^ 2) * distance l := by {
      gcongr
      refine (le_mul_iff_one_le_left ?_).mpr ?_
      · exact alg.hρ_red.1
      · linarith
    }
    -- ANCHOR_END: estimator_reduction_7
    -- ANCHOR: estimator_reduction_8
    _ = (1+δ) * (gη2_seq alg l - (1-alg.ρ_red) * ∑ t ∈ alg.𝒯 l \ alg.𝒯 (l+1), summand l t)
        + (alg.C_red + (1 + δ⁻¹) * alg.C_stab ^ 2) * distance l := by ring
    _ ≤ (1+δ) * (gη2_seq alg l - (1-alg.ρ_red) * (alg.θ * gη2_seq alg l))
        + (alg.C_red + (1 + δ⁻¹) * alg.C_stab ^ 2) * distance l := by {
      have h₁ : 0 ≤ 1 - alg.ρ_red := sub_nonneg_of_le <| le_of_lt alg.hρ_red.2
      rel[alg.doerfler_for_refined_elements l, h₁]
    }
    _ = (1+δ) * (1 - (1-alg.ρ_red) * alg.θ) * gη2_seq alg l
        + (alg.C_red + (1 + δ⁻¹) * alg.C_stab ^ 2) * distance l := by ring
    -- ANCHOR_END: estimator_reduction_8
}

end AdaptiveAlgorithm
