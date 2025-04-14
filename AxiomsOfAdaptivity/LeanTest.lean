-- This module serves as the root of the `LeanTest` library.
-- Import modules here that should be built as part of the library.
import Mathlib
open Filter
open TopologicalSpace

-- 4.18
def estimator_reduction (η : ℕ → ENNReal) :=
  ∃ q ∈ (Set.Ioo (0:NNReal) (1:NNReal)), ∀ n, (η (n+1))^2 ≤ q * (η n)^2

-- example (a b : ℕ → ENNReal) : limsup (a+b) atTop ≤ limsup a atTop+limsup b atTop := by {
--   have h1 : IsBoundedUnder (fun x1 x2 ↦ x1 ≥ x2) atTop a := by {
--     apply isBounded_ge_of_bot
--   }
--   have h2 : IsBoundedUnder (fun x1 x2 ↦ x1 ≤ x2) atTop a := by {
--     apply isBounded_le_of_top
--   }
--   have h3 : IsCoboundedUnder (fun x1 x2 ↦ x1 ≥ x2) atTop a := by {
--     apply isCobounded_ge_of_top
--   }
--   have h4 : IsCoboundedUnder (fun x1 x2 ↦ x1 ≤ x2) atTop a := by {
--     apply isCobounded_le_of_bot
--   }
--   exact limsup_add_le h1 h2 h3 h4

-- }


lemma my_limsup_monotone (fa fb : ℕ → ENNReal)(hf : fa ≤ fb) : limsup fa atTop ≤ limsup fb atTop := by {
  apply limsup_le_limsup
  case h := by{
    apply Eventually.of_forall
    apply hf
  }
  case hu := by {
    apply isCobounded_le_of_bot
  }
  case hv := by {
    apply isBounded_le_of_top
  }
}

lemma my_limsup_mul_constant (f : ℕ → ENNReal  ) : ∀ q ∈  (Set.Ioo (0:NNReal ) (1:NNReal ) ),  q*(limsup f atTop) = limsup (q•f) atTop := by{
  intro q hq
  have hqq : (q : ENNReal) ≠ 0 := by{
    apply ne_of_gt
    let ⟨h1, h2⟩ := hq
    apply ENNReal.coe_lt_coe.2
    exact h1
  }
  have hqqq : (q : ENNReal) ≠ ⊤ := by{
    apply ENNReal.coe_ne_top
  }

  let g : ENNReal  ≃o ENNReal
  := {
    toFun := λ x ↦  q*x,
    invFun := λ x ↦  x/q,
    left_inv := by {
      intro x
      simp
      calc
        q*x/q = q*(x/q) := by rw [@mul_div_assoc]
        _ = x := by refine ENNReal.mul_div_cancel hqq hqqq
    },
    right_inv := by {
      intro x
      simp
      refine ENNReal.mul_div_cancel hqq hqqq
    },
    map_rel_iff' := by {
      intros x y
      simp
      exact ENNReal.mul_le_mul_left hqq hqqq
    }
  }
  have hid : g (limsup f atTop)= limsup (λ x ↦ g (f x)) atTop := by {
    apply OrderIso.limsup_apply
    case hu := by {
      apply isBounded_le_of_top
    }
    case hu_co := by {
      apply isCobounded_le_of_bot
    }
    case hgu := by {
      apply isBounded_le_of_top
    }
    case hgu_co := by {
      apply isCobounded_le_of_bot
    }
  }
  calc
    q*(limsup f atTop) = g (limsup f atTop) := by rfl
    _ = limsup (λ x ↦ g (f x)) atTop := by apply hid
}

lemma smaller_q (a q : ℝ)(h : q ∈ (Set.Ioo (0:ℝ) (1:ℝ)) ∧   a ≤ q*a) : a≤ 0 := by {
  let ⟨hb1, hb2⟩ := h
  apply sub_le_sub_right at hb2
  specialize hb2 (q*a)
  rw[sub_self] at hb2
  nth_rw 1 [← mul_one a] at hb2
  nth_rw 1 [mul_comm q a] at hb2
  rw[← mul_sub_left_distrib] at hb2
  rw[← zero_mul (1-q)] at hb2
  rw[mul_le_mul_right ?c2] at hb2
  case c2 := by {
    simp
    apply hb1.2
  }
  exact hb2
}

lemma smaller_q_eq_zero (a : ENNReal )(hab1 : ∃ q ∈ (Set.Ioo (0:NNReal ) (1:NNReal ) ),  a ≤ q*a)(hab3 : a ≠  ⊤) : a =  0 := by {
  rcases hab1 with ⟨q, hq⟩
  have h : a = a.toNNReal := by {
    refine Eq.symm (ENNReal.coe_toNNReal ?_)
    exact hab3
  }
  let b : NNReal  := q*a.toNNReal
  have hb :( b : ENNReal) = q*(a.toNNReal : ENNReal) := by rfl
  have hbb : b = q*a.toNNReal := by rfl
  have hab' : a.toNNReal =0 := by{
    rw[h] at hq
    rw[← hb] at hq
    rw[ENNReal.coe_le_coe] at hq
    rw[hbb] at hq
    have ha : a.toReal ≤ 0 := by{
      apply smaller_q a.toReal q hq
    }
    apply le_antisymm
    exact ha
    simp
  }
  rw[ENNReal.toNNReal_eq_zero_iff] at hab'
  cases hab' with
  | inl h5 => exact h5
  | inr h5 => {
    rw[h5] at hab3
    simp at hab3
  }
}

theorem convergence_of_estimator_reduction (η: ℕ → ENNReal) (h : estimator_reduction η) (htop : limsup (λ n ↦ (η n)^2) atTop ≠ ⊤) : limsup (λ n ↦ (η n)^2) atTop =0 := by{

  have Lq: ∃ q ∈  (Set.Ioo (0:NNReal ) (1:NNReal ) ),  limsup (λ n ↦ (η n)^2) atTop ≤  q*limsup (λ n ↦ (η n)^2) atTop := by {
    have h':  ∃ q ∈   (Set.Ioo (0:NNReal ) (1:NNReal ) ), limsup (λ n ↦ (η (n+1))^2) atTop ≤ limsup (λ n ↦ q * (η n)^2) atTop := by {
      rcases h with ⟨q, hq⟩
      rcases hq with ⟨hq1, hq2⟩
      use q
      constructor
      case h.left := by exact hq1
      case h.right := by {
        apply my_limsup_monotone
        apply hq2
      }
    }

    have hh : ∀ q : NNReal,  (λ n ↦ q * (η n)^2) =  q • (λ n ↦ (η n)^2) := by{
      intro x
      ext n
      simp
      apply smul_eq_mul
    }

    rcases h' with ⟨q, hq⟩
    rcases hq with ⟨hq1, hq2⟩
    use q
    constructor
    case h.left := by apply hq1
    case h.right := by {

      calc
      limsup (λ n ↦ (η n)^2) atTop = limsup (λ n ↦ (λ n ↦ (η n)^2) (n+1)) atTop := by rw[← limsup_nat_add]
        _ ≤ limsup (λ n ↦ q * (η n)^2) atTop := by apply hq2
        _ = limsup (q • (λ n ↦ (η n)^2)) atTop := by rw[← hh]
        _ = q * limsup (λ n ↦ (η n)^2) atTop := by rw[← my_limsup_mul_constant (λ n ↦ (η n)^2) q hq1]
    }
  }
  rcases Lq with ⟨q, hq⟩
  rcases hq with ⟨hq1, hq2⟩
  apply smaller_q_eq_zero (limsup (λ n ↦ (η n)^2) atTop)
  case intro.intro.hab1 := by {
    use q
  }
  case intro.intro.hab3 := by {
    exact htop
  }
}
