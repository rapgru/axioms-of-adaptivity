import Mathlib
open Filter
open TopologicalSpace
open Finset

lemma tsum_indx {x y : ℝ} (f : ℕ -> ℝ) (hf: HasSum f x) (hfs: HasSum (fun k ↦ f (k+1)) y) : x = y + f 0 := by {
  rw [Summable.hasSum_iff_tendsto_nat] at hf hfs

  suffices : Tendsto (fun n ↦ ∑ i ∈ range n, f i) atTop (nhds (y + f 0))
  · apply tendsto_nhds_unique hf this

  -- TODO this should not be suffices and is the worst code imaginable
  suffices : Tendsto (fun n ↦ ∑ i ∈ range (n+1), f i - f 0) atTop (nhds y)
  · have h₁ : Tendsto (fun n : ℕ ↦ f 0) atTop (nhds (f 0)) := by exact tendsto_const_nhds
    have h₂ := Filter.Tendsto.add this h₁
    simp at h₂
    have h₃ : Tendsto (fun n : ℕ ↦ n - 1) atTop atTop := by {
      exact tendsto_sub_atTop_nat 1
    }
    change Tendsto (fun n ↦ ∑ i ∈ range (n + 1 - 1), f i) atTop (nhds (y + f 0))
    have h₄ : Tendsto ((fun x ↦ ∑ i ∈ range (x + 1), f i) ∘ fun n ↦ n - 1) atTop (nhds (y + f 0)) := Filter.Tendsto.comp h₂ h₃
    have h₅ : ((fun n ↦ ∑ i ∈ range (n + 1), f i) ∘ fun n ↦ n - 1) =ᶠ[atTop] fun x ↦ ∑ i ∈ range x, f i := by {
      unfold Filter.EventuallyEq
      rw [Filter.eventually_atTop]
      use 1
      intros n hn
      simp [Nat.sub_add_cancel hn]
    }
    exact Filter.Tendsto.congr' h₅ h₄

  have : ∀ n, ∑ i ∈ range n, f (i + 1) = ∑ i ∈ range (n+1), f i - f 0 := by {
    simp [Finset.sum_range_succ']
  }

  apply Filter.Tendsto.congr this hfs
  exact HasSum.summable hfs
  exact HasSum.summable hf
}

lemma tsum_indx' (f : ℕ -> ℝ) (hf: Summable f) : ∑' (k : ℕ), f k = ∑' (k : ℕ), f (k+1) + f 0 := by {
  apply tsum_indx
  exact Summable.hasSum hf
  apply Summable.hasSum
  apply Summable.comp_injective hf
  exact add_left_injective 1
}

lemma tsum_indx'' {n : ℕ} (f : ℕ -> ℝ) (hf: Summable f) : ∑' (k : ℕ), f (k+n) = ∑' (k : ℕ), f (k+n+1) + f n := by {
  let g := fun k ↦ k + n
  have := tsum_indx' (f ∘ g) (Summable.comp_injective hf <| add_left_injective n)
  have wild : ∑' (k : ℕ), f (k + 1 + n) = ∑' (k : ℕ), f (k + n + 1) := by {
    congr with k
    congr 1
    ring
  }
  unfold g at this
  simp [wild] at this
  assumption
}

def uniform_summability (η : ℕ → ℝ) :=
  Summable (η^2) ∧ ∃ C > 0, ∀ l : ℕ, ∑' k, (η^2) (k + l + 1) ≤ C * (η^2) l

def inverse_summability (η : ℕ → ℝ) :=
  ∀ s : ℝ, s > 0 → ∃ C > 0, ∀ l : ℕ, ∑ k ∈ range l, (η k)^(-1/s) ≤ C * (η^2) l

def uniform_r_linear_convergence (η : ℕ → ℝ) :=
  ∃ q ∈ (Set.Ioo 0 1), ∃ C > 0, ∀ k, ∀ l,
    (η^2) (l+k) ≤ C * q^k * (η^2) l

variable {η : ℕ → ℝ}

lemma uniform_of_uniform_r_linear (h : uniform_r_linear_convergence η) :
    uniform_summability η := by {
  rcases h with ⟨q,hq,C,hC,h⟩

  have : ∀ l n, ∑ k ∈ range n, (η^2) (k + l + 1) ≤ C * q * (1 - q)⁻¹ * (η^2) l := by {
    intros l n
    calc ∑ k ∈ range n, (η^2) (k + l + 1)
      _ ≤ ∑ k ∈ range n, C * q^(k + 1) * (η^2) l := by {
        gcongr with k
        specialize h (k + 1) l
        rw [← add_assoc, add_comm l k] at h
        assumption
      }
      _ = ∑ k ∈ range n, (C * q * (η^2) l) * q^k := by congr with _; ring
      _ = C * q * (η^2) l * ∑ k ∈ range n, q^k := by rw [← mul_sum]
      _ ≤ C * q * (η^2) l * ∑' k, q^k := by {
        gcongr
        · apply mul_nonneg
          apply mul_nonneg (le_of_lt hC)
          exact le_of_lt hq.1
          simp only [Pi.pow_apply]
          exact sq_nonneg (η l)

        apply Summable.sum_le_tsum
        · intros i hi
          exact pow_nonneg (le_of_lt hq.1) i

        exact summable_geometric_of_lt_one (le_of_lt hq.1) hq.2
      }
      _ = C * q * (η^2) l * (1 - q)⁻¹ := by rw [tsum_geometric_of_lt_one (le_of_lt hq.1) hq.2]
      _ = C * q * (1 - q)⁻¹ * (η^2) l := by ring
  }

  -- TODO show positivity of constant
  -- TODO this block essentially shows that uniform summability is equivalent
  --      to the statement from the have block. this should be its own lemma
  constructor
  swap
  · use C * q * (1-q)⁻¹
    constructor
    · apply mul_pos
      exact mul_pos hC hq.1
      apply Right.inv_pos.mpr
      linarith [hq.2]

    intros l

    apply Real.tsum_le_of_sum_range_le ?_ (this l)
    · intros
      apply sq_nonneg

  · apply summable_of_sum_range_le
    · intros
      apply sq_nonneg

    intros n
    calc ∑ i ∈ range n, (η ^ 2) i
      _ ≤ ∑ i ∈ range (n+1), (η ^ 2) i := by {
        apply sum_le_sum_of_subset_of_nonneg (range_subset.mpr (by simp)) ?_
        · intros
          apply sq_nonneg
      }
      _ = ∑ i ∈ range n, (η ^ 2) (i + 1) + (η ^ 2) 0 := by simp [Finset.sum_range_succ']
      _ ≤ C * q * (1 - q)⁻¹ * (η ^ 2) 0 + (η ^ 2) 0 := by rel [this 0 n]
}

-- take away the assumption C > 0 here and watch magic happen
lemma uniform_recursive_bound {C:ℝ} (hC : C > 0) (hSum: Summable (η ^ 2)) (hBound : ∀ (l : ℕ), ∑' (k : ℕ), (η ^ 2) (k + l + 1) ≤ C * (η ^ 2) l):
    ∀ l n, ∑' k, (η^2) (k + l + n) ≤ 1/(1+C⁻¹)^n *  ∑' k, (η^2) (k + l) := by {
  intros l n
  induction' n with n ih
  · simp

  calc ∑' (k : ℕ), (η ^ 2) (k + l + (n + 1))
    _ = 1/(1+C⁻¹) * (1+C⁻¹) * ∑' (k : ℕ), (η ^ 2) (k + l + (n + 1)) := by field_simp
    _ = 1/(1+C⁻¹) * (∑' (k : ℕ), (η ^ 2) (k + l + (n + 1)) + C⁻¹ * ∑' (k : ℕ), (η ^ 2) (k + l + (n + 1))) := by ring
    _ = 1/(1+C⁻¹) * (∑' (k : ℕ), (η ^ 2) (k + l + (n + 1)) + C⁻¹ * ∑' (k : ℕ), (η ^ 2) (k + (l + n) + 1)) := by simp [add_assoc]
    _ ≤ 1/(1+C⁻¹) * (∑' (k : ℕ), (η ^ 2) (k + l + (n + 1)) + C⁻¹ * (C * (η^2) (l+n))) := by rel [hBound (l+n)]
    _ = 1/(1+C⁻¹) * (∑' (k : ℕ), (η ^ 2) (k + l + (n + 1)) + (η^2) (l+n)) := by field_simp
    _ = 1/(1+C⁻¹) * (∑' (k : ℕ), (η ^ 2) (k + (l + n) + 1) + (η^2) (l+n)) := by simp [add_assoc]
    _ = 1/(1+C⁻¹) * (∑' (k : ℕ), (η ^ 2) (k + l + n)) := by {
      rw [← tsum_indx'' _ hSum]; congr with _; simp; congr 2; ring
    }
    _ ≤ 1/(1+C⁻¹) * (1 / (1 + C⁻¹) ^ n * ∑' (k : ℕ), (η ^ 2) (k + l)) := by rel [ih]
    _ = 1/(1+C⁻¹) * (1 / (1 + C⁻¹) ^ n) * ∑' (k : ℕ), (η ^ 2) (k + l) := by ring
    _ = 1/((1+C⁻¹) * (1 + C⁻¹)^n) * ∑' (k : ℕ), (η ^ 2) (k + l) := by field_simp
    _ = 1/(1 + C⁻¹)^(n+1) * ∑' (k : ℕ), (η ^ 2) (k + l) := by rw [pow_succ' (1 + C⁻¹)]
}

lemma uniform_r_linear_of_uniform (h : uniform_summability η) :
    uniform_r_linear_convergence η := by {
  rcases h with ⟨hSum, C, hC, hBound⟩

  use 1/(1+C⁻¹)
  constructor
  have h₁ : 1 < 1 + C⁻¹ := by linarith [Right.inv_pos.mpr hC]
  · constructor
    · simp only [one_div, inv_pos]
      linarith [h₁]
    · simp only [one_div]
      exact inv_lt_one_of_one_lt₀ h₁

  use (1+C)
  constructor
  · linarith

  intros k l
  let g := fun j ↦ (η^2) (j + l + k)
  calc (η ^ 2) (l + k)
    _ = g 0 := by unfold g; simp only [Pi.pow_apply, zero_add]
    _ ≤ ∑' j, (η^2) (j + l + k) := by {
      apply Summable.le_tsum
      · apply Summable.comp_injective hSum
        have : (fun (x:ℕ) ↦ x + (l + k)) = fun x ↦ x + l + k := by funext; ring
        rw [← this]
        exact add_left_injective (l+k)
      · intros j hj
        unfold g
        simp only [Pi.pow_apply]
        apply sq_nonneg
    }
    _ ≤ 1/(1 + C⁻¹)^k * ∑' (j : ℕ), (η ^ 2) (j + l) := by apply uniform_recursive_bound hC hSum hBound l k
    _ = 1/(1 + C⁻¹)^k * (∑' (j : ℕ), (η ^ 2) (j + l + 1) + (η ^ 2) l) := by {
      congr
      apply tsum_indx''
      exact hSum
    }
    _ ≤ 1/(1 + C⁻¹)^k * (C * (η ^ 2) l + (η ^ 2) l) := by rel [hBound l]
    _ = (1 + C) * (1/(1 + C⁻¹))^k * (η ^ 2) l := by ring
}
