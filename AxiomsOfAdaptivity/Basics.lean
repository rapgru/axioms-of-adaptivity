import Mathlib
open Filter
open TopologicalSpace
open BigOperators
open Finset
open scoped Topology

class Partitionable (α : Type _) [DecidableEq α] where
  part : Finset α → α → Prop
  self_part : ∀ t : α, part {t} t
  union_part :
    ∀ {s : α} (m : Finset α) (ms : α → Finset α),
      (∀ t ∈ m, part (ms t) t) ∧ part m s → part (m.biUnion ms) s
  unique_part :
    ∀ {s : α} (p m : Finset α),
      p ⊆ m ∧ part p s → p = {s}
  unique_element : ∀ (s t : α),
      part {s} t → t = s

notation:50 ts " ⇒ " t => Partitionable.part ts t
abbrev Mesh (α : Type*) := Finset α

variable {α: Type*} [DecidableEq α] [Partitionable α]
instance Mesh.orderBot : OrderBot (Mesh α) := by
  infer_instance

def refines (A B : Mesh α) : Prop :=
  ∀ t ∈ B, ∃ ts ⊆ A, ts ⇒ t

theorem refines_trans (X Y Z : Mesh α) (hxy: refines X Y) (hyz: refines Y Z) :
    refines X Z := by {
  intros t ht
  rcases hyz t ht with ⟨S,hS,hU⟩
  choose f hf using fun t ht => hxy t (hS ht)

  -- trick: use empty set when element is not in S because biUnion does
  -- not supply membership proof
  let U := S.biUnion fun x =>
    if hx : x ∈ S then f x hx else ∅
  use U

  constructor
  · apply Finset.biUnion_subset.mpr
    exact fun _ hs ↦ by simp [hs, hf]
  · apply Partitionable.union_part
    exact ⟨fun _ hs ↦ by simp [hs, hf], hU⟩
}

lemma biunion_is_singleton {α β : Type*} [DecidableEq β] (f : α → Finset β)
      (A : Finset α) (b : β) (h : A.biUnion f = {b}) :
      ∃ s ∈ A, f s = {b} := by {
    have hb : b ∈ A.biUnion f := by simp [h]
    rcases mem_biUnion.mp hb with ⟨s, hsA, hbs⟩
    have hsub : f s ⊆ {b} := fun x hx =>
    by simpa [h] using mem_biUnion.mpr ⟨s, hsA, hx⟩
    exact ⟨s, hsA, Finset.eq_singleton_iff_unique_mem.mpr
    ⟨hbs, fun x hx => mem_singleton.1 (hsub hx)⟩⟩
}

lemma refines_antisymm_subset (A B : Mesh α) (hAB: refines A B) (hBA: refines B A) :
    A ⊆ B := by {
  intros t htA
  -- TODO: deduplicate this construction!
  obtain ⟨ts, hts_part, hts_sub⟩ := hBA t htA
  choose f hf using fun t ht => hAB t (hts_part ht)
  let g := fun x =>
     if hx : x ∈ ts then f x hx else ∅
  let U := ts.biUnion g

  have h₁: U ⇒ t := by {
     apply Partitionable.union_part
     exact ⟨fun _ hs ↦ by unfold g; simp [hs, hf], hts_sub⟩
  }
  have h₂: U ⊆ A := by {
    apply Finset.biUnion_subset.mpr
    exact fun _ hs ↦ by unfold g; simp [hs, hf]
  }
  have : U = {t} := Partitionable.unique_part U A ⟨h₂, h₁⟩
  have : ∃ (s:α) (h : s ∈ ts), f s h = {t} := by {
    obtain ⟨s,hs,hsf⟩ :=  biunion_is_singleton g ts t this
    use s, hs
    unfold g at hsf
    simp [hs] at hsf
    simp [hsf]
  }
  rcases this with ⟨s, hs, hss⟩
  have : s = t := Partitionable.unique_element t s (by {
    simp [← hss, (hf s hs).2]
  })
  subst this
  apply hts_part
  exact hs
}

theorem refines_antisymm (A B : Mesh α) (hAB: refines A B) (hBA: refines B A) :
    A = B := by {
  apply Subset.antisymm_iff.mpr
  exact ⟨refines_antisymm_subset A B hAB hBA, refines_antisymm_subset B A hBA hAB⟩
}

instance : LE (Mesh α) := ⟨refines⟩
instance : LT (Mesh α) := ⟨fun f g => f ≤ g ∧ f ≠ g⟩

instance Mesh.partialOrder : PartialOrder (Mesh α) where
  le := (· ≤ ·)
  lt := (· < ·)
  le_antisymm := refines_antisymm
  lt_iff_le_not_le a b := by
    constructor
    · intros h
      exact ⟨h.1, by
        by_contra h₂
        have : a = b ∧ ¬ a = b := ⟨refines_antisymm a b h.1 h₂, h.2⟩
        exact (and_not_self_iff (a = b)).mp this
      ⟩
    · intros h
      exact ⟨h.1, by
        by_contra h₂
        rw [← h₂] at h
        exact (and_not_self_iff (a ≤ a)).mp h
      ⟩
  le_refl _ t h := ⟨{t}, singleton_subset_iff.mpr h, Partitionable.self_part t⟩
  le_trans := refines_trans

abbrev RefinementIndicator (α : Type*) (β : Type*) := Mesh α → β → α → ℝ
variable {β : Type*}

def glob_err (ri: RefinementIndicator α β) (triang: Mesh α) v :=
  ∑ t ∈ triang, (ri triang v t)^2

-- TOOD maybe move constants to their own structure that is already available before
-- AdaptiveAlgorithm and only put the Props into the structure
private noncomputable def ε_qos' (ρ_red C_rel C_red C_stab θ : ℝ) := ⨆ δ > 0, (1-(1+δ)*(1-(1-ρ_red)*θ)) / (C_rel^2 * (C_red + (1+δ⁻¹)*C_stab^2))
private def C_rel' (C_Δ C_drel : ℝ) := C_Δ * C_drel

-- TODO unify notation for meshes, triangles and vectors (how much special characters to use?)
structure AdaptiveAlgorithm where
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
  a1 : ∀ T, ∀ T' ≤ T, ∀ S ⊆ T ∩ T', ∀ v v',
    |√(∑ t ∈ S, η T' v' t ^ 2) - √(∑ t ∈ S, η T v t ^ 2)| ≤ C_stab * d T' v' v
  -- A2: reduction property on refined elements
  ρ_red : ℝ
  hρ_red : ρ_red ∈ Set.Ioo 0 1
  C_red : ℝ
  hC_red : 0 < C_red
  a2 : ∀ T, ∀ T' ≤ T, ∑ t ∈ T' \ T, η T' (U T') t ^ 2 ≤ ρ_red * ∑ t ∈ T \ T', η T (U T) t ^ 2 + C_red * d T' (U T') (U T) ^ 2
  -- A4: reliability
  C_drel : ℝ
  hC_drel : 0 < C_drel
  -- TODO this should be a result from A4 and the compatibility condition of the measure d
  -- would already be nicer as a sorry theorem
  reliability : ∀ T, d T u (U T) ≤ C_rel' C_Δ C_drel * √(glob_err η T (U T))
  -- A3: general quasi-orthogonality
  -- this is last so that all constants are already available
  ε_qo : ℝ
  hε_qo : 0 ≤ ε_qo ∧ ε_qo < ε_qos' ρ_red (C_rel' C_Δ C_drel) C_red C_stab θ
  C_qo : ℝ
  hC_qo : C_qo ≥ 1
  -- n + 1 is the number of summands here, don't need N ≥ l from paper
  a3 : ∀ l n, ∑ k ∈ range n, (d (𝒯 <| k + l + 1) (U <| 𝒯 <| k + l + 1) (U <| 𝒯 k) ^ 2 - ε_qo * d (𝒯 <| k + l) u (U <| 𝒯 <| k + l) ^ 2) ≤ C_qo * glob_err η (𝒯 l) (U <| 𝒯 l)

namespace AdaptiveAlgorithm

variable (alg : @AdaptiveAlgorithm α _ _ β)
include alg

def ρ_est_fun δ := (1+δ) * (1 - (1 - alg.ρ_red) * alg.θ)
noncomputable def C_est_fun δ := alg.C_red + (1 + δ⁻¹) * alg.C_stab ^ 2

-- definitions for general field access
def C_rel := C_rel' alg.C_Δ alg.C_drel
noncomputable def ε_qoss := ε_qos' alg.ρ_red alg.C_rel alg.C_red alg.C_stab

end AdaptiveAlgorithm

-- TODO make name better so that it is clear this is the η^2 from the paper
def glob_err_nat (alg : @AdaptiveAlgorithm α _ _ β) l := glob_err alg.η (alg.𝒯 <| l) (alg.U <| alg.𝒯 <| l)

omit [DecidableEq α] [Partitionable α] in
theorem glob_err_nonneg (ri: RefinementIndicator α β) (triang: Mesh α) v : 0 ≤ glob_err ri triang v := by {
  apply sum_nonneg
  exact fun _ _ ↦ sq_nonneg _
}

theorem glob_err_nat_nonneg (alg : @AdaptiveAlgorithm α _ _ β) :
  0 ≤ glob_err_nat alg := by {
    intros l
    -- example where simp alone does not work without
    -- specifying a closing theorem to use
    simpa using glob_err_nonneg _ _ _
}

theorem C_rel_pos (alg : @AdaptiveAlgorithm α _ _ β): 0 < alg.C_rel := by {
  exact mul_pos alg.hC_Δ alg.hC_drel
}

structure EstConst where
  ρ_est : ℝ
  hρ_est : ρ_est ∈ Set.Ioo 0 1
  C_est : ℝ
  hC_est : 0 < C_est

def EstimatorReduction (alg : @AdaptiveAlgorithm α _ _ β) (c : EstConst) δ := c.ρ_est = alg.ρ_est_fun δ ∧ c.C_est = alg.C_est_fun δ ∧ ∀ l, glob_err_nat alg (l + 1) ≤ c.ρ_est * glob_err_nat alg l + c.C_est * alg.d (alg.𝒯 <| l + 1) (alg.U <| alg.𝒯 <| l+1) (alg.U <| alg.𝒯 <| l) ^ 2

-- Start of lemma 4.7
-- TODO move to file

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

lemma doerfler_for_refined_elements (alg : @AdaptiveAlgorithm α _ _ β) :
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

-- Lemma 4.7
theorem adaptive_alg_estimator_reduction (alg : @AdaptiveAlgorithm α _ _ β) : ∃ c δ, EstimatorReduction alg c δ := by {
  -- TODO this is alg.ρ_est_fun. refactor mono results etc out of here
  let h := fun δ ↦ (1+δ) * (1 - (1-alg.ρ_red) * alg.θ)
  let δ := 1/2 * ((1 - alg.ρ_red) * alg.θ * (1 - (1 - alg.ρ_red) * alg.θ)⁻¹)

  -- h is linear, positive rate is the key to monotonicity
  have key : 0 < 1 - (1 - alg.ρ_red) * alg.θ := by {
    field_simp
    apply mul_lt_one_of_nonneg_of_lt_one_left
    · simpa using le_of_lt alg.hρ_red.2
    · simpa using alg.hρ_red.1
    · exact alg.hθ.2
  }
  have h_mono : StrictMono h := by {
    intros a b hab
    unfold h
    rel [key, hab]
  }
  -- 2*delta is positive
  have hδ_pre_pos : 0 < (1 - alg.ρ_red) * alg.θ * (1 - (1 - alg.ρ_red) * alg.θ)⁻¹ := by {
    apply mul_pos _ (inv_pos.mpr key)
    simp [sub_mul]
    exact mul_lt_of_lt_one_left alg.hθ.1 alg.hρ_red.2
  }
  have hδ : 0 < δ := by {unfold δ; simp [hδ_pre_pos]}
  -- TODO: when working with Set.Ioo 0 1 so much, maybe it is worth it to add
  -- a type for this interval that has simp theorems for operations that
  -- stay inside the interval. for example 1/2 * x or 1 - x.

  use {
    ρ_est := h δ
    hρ_est := by {
      constructor
      · calc h δ
          _ > h 0 := h_mono hδ
          _ > 0 := by {
            unfold h
            simp [key]
          }
      · calc h δ
          _ < h ((1 - alg.ρ_red) * alg.θ * (1 - (1 - alg.ρ_red) * alg.θ)⁻¹) := by {
            apply h_mono
            unfold δ
            -- TODO this might be a good time for the mode where you can cursor around the expression
            -- giving this long argument to one_mul for it to recognise the right place is
            -- not very nice
            rw [one_div, ← one_mul ((1 - alg.ρ_red) * alg.θ * (1 - (1 - alg.ρ_red) * alg.θ)⁻¹)]
            apply mul_lt_mul two_inv_lt_one <;> simp [hδ_pre_pos]
          }
          _ = 1 := by {
            unfold h
            rw [add_mul, mul_assoc, inv_mul_cancel₀ <| Ne.symm (ne_of_lt key)]
            ring
          }
    }
    C_est := alg.C_red + (1 + δ⁻¹) * alg.C_stab ^ 2
    hC_est := by {
      apply Left.add_pos_of_pos_of_nonneg alg.hC_red
      apply mul_nonneg _ (sq_nonneg _)
      apply add_nonneg (zero_le_one' ℝ)
      apply inv_nonneg.mpr
      exact le_of_lt hδ
    }
  }
  use δ

  -- example where refine is a perfect match instead of apply
  refine ⟨by rfl, by rfl, ?_⟩

  intros l
  let summand n t := alg.η (alg.𝒯 n) (alg.U <| alg.𝒯 <| n) t ^ 2
  let distance n := alg.d (alg.𝒯 <| n + 1) (alg.U <| alg.𝒯 <| n + 1) (alg.U <| alg.𝒯 <| n) ^ 2

  calc glob_err_nat alg (l + 1)
    _ = ∑ t ∈ alg.𝒯 (l + 1) \ alg.𝒯 l, summand (l+1) t + ∑ t ∈ alg.𝒯 l ∩ alg.𝒯 (l+1), summand (l+1) t := by {
      unfold glob_err_nat glob_err
      have h_eq : alg.𝒯 (l + 1) = (alg.𝒯 (l + 1) \ alg.𝒯 l) ∪ (alg.𝒯 (l + 1) ∩ alg.𝒯 l) := by {
        exact Eq.symm (sdiff_union_inter (alg.𝒯 (l + 1)) (alg.𝒯 l))
      }
      nth_rw 1 [h_eq]
      simp [sum_union (disjoint_sdiff_inter _ _)]
      nth_rw 1 [inter_comm]
    }
    _ ≤ alg.ρ_red * ∑ t ∈ alg.𝒯 l \ alg.𝒯 (l + 1), summand l t + alg.C_red * distance l + (∑ t ∈ alg.𝒯 l ∩ alg.𝒯 (l + 1), summand (l + 1) t) := by rel[alg.a2 (alg.𝒯 l) (alg.𝒯 <| l + 1) (alg.h𝒯 l)]
    _ ≤ alg.ρ_red * ∑ t ∈ alg.𝒯 l \ alg.𝒯 (l + 1), summand l t + alg.C_red * distance l + ((1 + δ) * ∑ t ∈ alg.𝒯 l ∩ alg.𝒯 (l + 1), summand l t + (1 + δ⁻¹) * (alg.C_stab ^ 2 * distance l)) := by {
      have := alg.a1 (alg.𝒯 l) (alg.𝒯 <| l + 1) (alg.h𝒯 l) (alg.𝒯 l ∩ alg.𝒯 (l + 1)) (by rfl) (alg.U <| alg.𝒯 <| l) (alg.U <| alg.𝒯 <| l + 1)
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
      have h_eq : alg.𝒯 l = (alg.𝒯 l \ alg.𝒯 (l + 1)) ∪ (alg.𝒯 l ∩ alg.𝒯 (l+1)) := by exact Eq.symm (sdiff_union_inter (alg.𝒯 l) (alg.𝒯 (l + 1)))
      have h_dis: @Disjoint (Finset α) Finset.partialOrder Finset.instOrderBot (alg.𝒯 l \ alg.𝒯 (l + 1)) (alg.𝒯 l ∩ alg.𝒯 (l+1)) := by {
        exact disjoint_sdiff_inter (alg.𝒯 l) (alg.𝒯 (l + 1))
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
      have h : 0 ≤ 1 - alg.ρ_red := sub_nonneg_of_le <| le_of_lt alg.hρ_red.2
      rel[doerfler_for_refined_elements alg l, h]
    }
    _ = (1+δ) * (1 - (1-alg.ρ_red) * alg.θ) * glob_err_nat alg l + (alg.C_red + (1 + δ⁻¹) * alg.C_stab ^ 2) * distance l := by ring
}
