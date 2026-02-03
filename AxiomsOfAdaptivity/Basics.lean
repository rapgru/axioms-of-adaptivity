import Mathlib
import AxiomsOfAdaptivity.Mesh

open Filter
open TopologicalSpace
open BigOperators
open Finset
open scoped Topology

variable {α: Type*} [DecidableEq α] [Lattice α] [OrderBot α]

abbrev RefinementIndicator (α : Type*) [DecidableEq α] [Lattice α] [OrderBot α] (β : Type*) := Mesh α → β → α → ℝ
variable {β : Type*}

def glob_err (ri: RefinementIndicator α β) (triang: Mesh α) v :=
  ∑ t ∈ triang, (ri triang v t)^2

theorem glob_err_nonneg (ri: RefinementIndicator α β) (triang: Mesh α) v : 0 ≤ glob_err ri triang v := by {
  apply sum_nonneg
  exact fun _ _ ↦ sq_nonneg _
}

-- TODO utility, move to file
lemma square_estimate_of_small_distance {a b c : ℝ} (ha : 0 ≤ a) (h : |a-b| ≤ c) :
  a^2 ≤ (b+c)^2 := by {
  have : a - b ≤ c := le_of_max_le_left h
  have : a ≤ b + c := tsub_le_iff_left.mp this
  exact pow_le_pow_left₀ ha this 2
}

example : 2^(1/2) = 1 := rfl

lemma young_with_delta {a b δ p q : ℝ} (ha : 0 ≤ a)  (hb : 0 ≤ b) (hδ : 0 < δ) (hpq : p.HolderConjugate q): a*b ≤ δ/p * a^p + 1/(q*δ^(q/p)) * b^q := by {
  have hδ₂ := le_of_lt hδ
  have hpow_nonneg x := (Real.rpow_nonneg hδ₂ x)
  have ha₂ : 0 ≤ a * δ^(1/p) := mul_nonneg ha (hpow_nonneg _)
  have hb₂ : 0 ≤ b * 1/δ^(1/p) := by apply mul_nonneg <;> simp [hb, ha, hpow_nonneg _]
  have := Real.young_inequality_of_nonneg ha₂ hb₂ hpq

  calc a*b
    _ = a * b * (δ ^ p⁻¹ * (δ ^ p⁻¹)⁻¹) := by field_simp
    _ = a * δ ^ (1 / p) * (b * 1 / δ ^ (1 / p)) := by ring_nf
    _ ≤ (a * δ ^ (1 / p)) ^ p / p + (b * 1 / δ ^ (1 / p)) ^ q / q := this
    _ = δ/p * a^p + (b * 1 / δ ^ (1 / p)) ^ q / q := by {
      rw [Real.mul_rpow ha <| hpow_nonneg _, ←Real.rpow_mul hδ₂]
      simp [inv_mul_cancel₀ <| Real.HolderTriple.ne_zero hpq, mul_comm]
      ring
    }
    _ = δ/p * a^p + 1/(q*δ^(q/p)) * b^q := by {
      field_simp
      rw [Real.div_rpow hb <| hpow_nonneg _, ←Real.rpow_mul hδ₂]
      ring_nf
    }
}

lemma sum_square_le_square_sum {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    ∀ δ > 0, (a+b)^2 ≤ (1+δ)*a^2 + (1+δ⁻¹)*b^2 := by {
  intros δ hδ
  have := young_with_delta ha hb hδ Real.HolderConjugate.two_two
  calc (a + b) ^ 2
    _ = a^2 + 2*(a*b) + b^2 := by ring
    _ ≤ a^2 + 2*(δ/2 * a^2 + 1/(2*δ) * b^2) + b^2 := by simpa using this
    _ = (1+δ)*a^2 + (1+δ⁻¹)*b^2 := by ring
}

lemma Ioo_01_mul_lt {a b : ℝ} (ha : a < 1) (hb : 0 < b) : a * b < b := by {
  exact mul_lt_of_lt_one_left hb ha
}

-- TOOD maybe move constants to their own structure that is already available before
-- AdaptiveAlgorithm and only put the Props into the structure

/- This indexed supremum (iSup) looks like this after `dsimp [iSup]`, quite clever.
sSup
    (Set.range fun δ ↦
      sSup
        (Set.range fun h ↦
          (1 - (1 + δ) * (1 - (1 - alg.ρ_red) * alg.θ)) / (alg.C_rel ^ 2 * (alg.C_red + (1 + δ⁻¹) * alg.C_stab ^ 2)))) -/
private noncomputable def ε_qos' (ρ_red C_rel C_red C_stab θ : ℝ) := ⨆ δ > 0, (1-(1+δ)*(1-(1-ρ_red)*θ)) / (C_rel^2 * (C_red + (1+δ⁻¹)*C_stab^2))

private def C_rel' (C_Δ C_drel : ℝ) := C_Δ * C_drel

-- TODO unify notation for meshes, triangles and vectors (how much special characters to use?)
structure AdaptiveAlgorithm (α β: Type*) [DecidableEq α] [Lattice α] [OrderBot α] where
  U : Mesh α → β
  -- limit
  u : β
  -- error estimator
  η : RefinementIndicator α β
  hη : η ≥ 0
  -- error measure
  d : Mesh α → β → β → ℝ
  C_Δ : ℝ
  hC_Δ : 0 < C_Δ
  non_neg : ∀ T v w, d T v w ≥ 0
  quasi_symmetry : ∀ T v w, d T v w ≤ C_Δ * d T w v
  quasi_triangle_ineq : ∀ T v w y, C_Δ⁻¹ * d T v y ≤ d T v w + d T w y
  -- TODO error measure on X ∪ X(T) ?
  -- compatibility: ∀ T v w, ∀ T' ≤ T, d T' v w = d T v w
  further_approximation : ∀ T, ∀ ε > 0, ∃ T' ≤ T, d T' u (U T') ≤ ε
  -- Triangulations
  𝒯 : ℕ → Mesh α
  h𝒯 : ∀ l, 𝒯 (Nat.succ l) ≤ 𝒯 l
  -- Dörfler marking
  θ : ℝ
  hθ : θ ∈ Set.Ioc 0 1
  ℳ : ℕ → Mesh α
  hℳ : ∀ l,
    -- Doerfler marking (2.5)
    -- TODO this says that the set has minimal cardinality, should be weakened
    -- to almost minimal cardinality
    let doerfler triang := θ * glob_err η (𝒯 l) (U <| 𝒯 l) ≤ ∑ t ∈ triang, η (𝒯 l) (U <| 𝒯 l) t ^ 2
    ℳ l ⊆ (𝒯 l \ 𝒯 (l+1)) ∧ doerfler (ℳ l) ∧ ∀ M' ⊆ 𝒯 l, doerfler M' → (ℳ l).card ≤ M'.card
  -- A1: stability on non-refined element domains
  C_stab : ℝ
  hC_stab : C_stab > 0
  a1 : ∀ T : Mesh α, ∀ T' ≤ T, ∀ S ⊆ T ∩ T', ∀ v v',
    |√(∑ t ∈ S, η T' v' t ^ 2) - √(∑ t ∈ S, η T v t ^ 2)| ≤ C_stab * d T' v' v
  -- A2: reduction property on refined elements
  ρ_red : ℝ
  hρ_red : ρ_red ∈ Set.Ioo 0 1
  C_red : ℝ
  hC_red : 0 < C_red
  a2 : ∀ T : Mesh α, ∀ T' ≤ T, ∑ t ∈ T' \ T, η T' (U T') t ^ 2 ≤ ρ_red * ∑ t ∈ T \ T', η T (U T) t ^ 2 + C_red * d T' (U T') (U T) ^ 2
  -- A4: reliability
  C_drel : ℝ
  hC_drel : 0 < C_drel
  -- TODO this should be a result from A4 and the compatibility condition of the measure d
  -- would already be nicer as a sorry theorem
  reliability' : ∀ T, d T u (U T) ≤ C_rel' C_Δ C_drel * √(glob_err η T (U T))
  -- A3: general quasi-orthogonality
  -- this is last so that all constants are already available
  ε_qo : ℝ
  hε_qo' : 0 ≤ ε_qo ∧ ε_qo < ε_qos' ρ_red (C_rel' C_Δ C_drel) C_red C_stab θ
  C_qo : ℝ
  hC_qo : C_qo ≥ 1
  -- n + 1 is the number of summands here, don't need N ≥ l from paper
  a3 : ∀ l n, ∑ k ∈ range n, (d (𝒯 <| k + l + 1) (U <| 𝒯 <| k + l + 1) (U <| 𝒯 <| k + l) ^ 2 - ε_qo * d (𝒯 <| k + l) u (U <| 𝒯 <| k + l) ^ 2) ≤ C_qo * glob_err η (𝒯 l) (U <| 𝒯 l)

namespace AdaptiveAlgorithm

variable (alg : AdaptiveAlgorithm α β)
include alg

def ρ_est δ := (1+δ) * (1 - (1 - alg.ρ_red) * alg.θ)
noncomputable def C_est δ := alg.C_red + (1 + δ⁻¹) * alg.C_stab ^ 2

-- definitions for general field access
def C_rel := C_rel' alg.C_Δ alg.C_drel
noncomputable def ε_qos := ε_qos' alg.ρ_red alg.C_rel alg.C_red alg.C_stab alg.θ
lemma reliability : ∀ T, alg.d T alg.u (alg.U T) ≤ alg.C_rel * √(glob_err alg.η T (alg.U T)) := alg.reliability'

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

-- TODO make name better so that it is clear this is the η^2 from the paper
def glob_err_nat l := glob_err alg.η (alg.𝒯 <| l) (alg.U <| alg.𝒯 <| l)

theorem glob_err_nat_nonneg :
  0 ≤ glob_err_nat alg := by {
    intros l
    -- example where simp alone does not work without
    -- specifying a closing theorem to use
    simpa using glob_err_nonneg _ _ _
}

-- TODO really rethink the naming and the NNReal vs Real situation
noncomputable def gη n := NNReal.sqrt (alg.glob_err_nat n).toNNReal

lemma hgη : ∀ n, alg.gη n ^ 2 = alg.glob_err_nat n := by {
  intros n
  unfold gη
  push_cast
  rw [Real.coe_toNNReal]
  apply Real.sq_sqrt
  all_goals exact alg.glob_err_nat_nonneg n
}

lemma doerfler_for_refined_elements :
    ∀ l, alg.θ * glob_err_nat alg l ≤ ∑ t ∈ (alg.𝒯 l \ alg.𝒯 (l+1)), alg.η (alg.𝒯 l) (alg.U <| alg.𝒯 l) t ^ 2 := by {
  intros l
  calc alg.θ * glob_err_nat alg l
    _ ≤ ∑ t ∈ alg.ℳ l, alg.η (alg.𝒯 l) (alg.U <| alg.𝒯 l) t ^ 2 := by exact (alg.hℳ l).2.1
    _ ≤ ∑ t ∈ (alg.𝒯 l \ alg.𝒯 (l+1)), alg.η (alg.𝒯 l) (alg.U <| alg.𝒯 l) t ^ 2 := by {
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · exact (alg.hℳ l).1
      · exact fun _ _ _ ↦ sq_nonneg _
    }
}

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
theorem estimator_reduction : ∀ δ > 0, (alg.ρ_est δ < 1) → ∀ l, alg.glob_err_nat (l + 1) ≤ alg.ρ_est δ * alg.glob_err_nat l + alg.C_est δ * alg.d (alg.𝒯 <| l + 1) (alg.U <| alg.𝒯 <| l+1) (alg.U <| alg.𝒯 <| l) ^ 2 := by {
  intros δ hδ hρ_est l

  let summand n t := alg.η (alg.𝒯 n) (alg.U <| alg.𝒯 <| n) t ^ 2
  let distance n := alg.d (alg.𝒯 <| n + 1) (alg.U <| alg.𝒯 <| n + 1) (alg.U <| alg.𝒯 <| n) ^ 2

  calc glob_err_nat alg (l + 1)
    _ = ∑ t ∈ alg.𝒯 (l + 1) \ alg.𝒯 l, summand (l+1) t + ∑ t ∈ alg.𝒯 l ∩ alg.𝒯 (l+1), summand (l+1) t := by {
      unfold glob_err_nat glob_err
      have h_eq : (alg.𝒯 (l + 1)).val = (↑(alg.𝒯 (l + 1)) \ ↑(alg.𝒯 l)) ∪ (↑(alg.𝒯 (l + 1)) ∩ ↑(alg.𝒯 l)) := by {
        exact Eq.symm (sdiff_union_inter _ _)
      }
      nth_rw 1 [h_eq]
      simp [sum_union (disjoint_sdiff_inter _ _)]
      nth_rw 1 [inter_comm]
    }
    _ ≤ alg.ρ_red * ∑ t ∈ alg.𝒯 l \ alg.𝒯 (l + 1), summand l t + alg.C_red * distance l + (∑ t ∈ alg.𝒯 l ∩ alg.𝒯 (l + 1), summand (l + 1) t) := by rel[alg.a2 (alg.𝒯 l) (alg.𝒯 <| l + 1) (alg.h𝒯 l)]
    _ ≤ alg.ρ_red * ∑ t ∈ alg.𝒯 l \ alg.𝒯 (l + 1), summand l t + alg.C_red * distance l + ((1 + δ) * ∑ t ∈ alg.𝒯 l ∩ alg.𝒯 (l + 1), summand l t + (1 + δ⁻¹) * (alg.C_stab ^ 2 * distance l)) := by {
      have := alg.a1 (alg.𝒯 l) (alg.𝒯 <| l + 1) (alg.h𝒯 l) (alg.𝒯 l ∩ alg.𝒯 (l + 1)) (fun _ a ↦ a) (alg.U <| alg.𝒯 <| l) (alg.U <| alg.𝒯 <| l + 1)
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
    _ = alg.ρ_red * ∑ t ∈ alg.𝒯 l \ alg.𝒯 (l+1), summand l t + (1+δ) * ∑ t ∈ alg.𝒯 l ∩ alg.𝒯 (l+1), summand l t + (alg.C_red + (1 + δ⁻¹) * alg.C_stab ^ 2) * distance l := by ring
    _ = alg.ρ_red * ∑ t ∈ alg.𝒯 l \ alg.𝒯 (l+1), summand l t + (1+δ) * (glob_err_nat alg l -  ∑ t ∈ alg.𝒯 l \ alg.𝒯 (l+1), summand l t) + (alg.C_red + (1 + δ⁻¹) * alg.C_stab ^ 2) * distance l := by {
      congr
      have h_eq : (alg.𝒯 l).val = (↑(alg.𝒯 l) \ ↑(alg.𝒯 (l + 1))) ∪ (↑(alg.𝒯 l) ∩ ↑(alg.𝒯 (l+1))) := by exact Eq.symm (sdiff_union_inter _ _)
      have h_dis: @Disjoint (Finset α) Finset.partialOrder Finset.instOrderBot (alg.𝒯 l \ alg.𝒯 (l + 1)) (alg.𝒯 l ∩ alg.𝒯 (l+1)) := by {
        exact disjoint_sdiff_inter _ _
      }
      unfold glob_err_nat glob_err
      nth_rw 2 [h_eq]
      rw [sum_union (disjoint_sdiff_inter _  _)]
      ring
    }
    _ ≤ (1+δ) * alg.ρ_red * ∑ t ∈ alg.𝒯 l \ alg.𝒯 (l+1), summand l t + (1+δ) * (glob_err_nat alg l - ∑ t ∈ alg.𝒯 l \ alg.𝒯 (l+1), summand l t) + (alg.C_red + (1 + δ⁻¹) * alg.C_stab ^ 2) * distance l := by {
      gcongr
      refine (le_mul_iff_one_le_left ?_).mpr ?_
      · exact alg.hρ_red.1
      · linarith
    }
    _ = (1+δ) * (glob_err_nat alg l - (1-alg.ρ_red) * ∑ t ∈ alg.𝒯 l \ alg.𝒯 (l+1), summand l t) + (alg.C_red + (1 + δ⁻¹) * alg.C_stab ^ 2) * distance l := by ring
    _ ≤ (1+δ) * (glob_err_nat alg l - (1-alg.ρ_red) * (alg.θ * glob_err_nat alg l)) + (alg.C_red + (1 + δ⁻¹) * alg.C_stab ^ 2) * distance l := by {
      have h₁ : 0 ≤ 1 - alg.ρ_red := sub_nonneg_of_le <| le_of_lt alg.hρ_red.2
      rel[alg.doerfler_for_refined_elements l, h₁]
    }
    _ = (1+δ) * (1 - (1-alg.ρ_red) * alg.θ) * glob_err_nat alg l + (alg.C_red + (1 + δ⁻¹) * alg.C_stab ^ 2) * distance l := by ring
}

end AdaptiveAlgorithm
