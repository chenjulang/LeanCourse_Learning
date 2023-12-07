import Mathlib.LinearAlgebra.Matrix.Basis
import Mathlib.Data.Real.Sqrt


variable {m n : Type} [Fintype m] [Fintype n]
variable (A : Matrix m n ℝ)
variable (R₁ R₂ : Matrix m n ℝ)

-- 定义简化阶梯形矩阵
def is_reduced_row_echelon_form (R : matrix m n ℝ) : Prop
:=
∀ (i j : m), i < j
→ R i = 0
  ∨
  Nat.find (λ k, R i k ≠ 0) < Nat.find (λ k, R j k ≠ 0)

-- 唯一性定理的陈述
theorem reduced_row_echelon_form_unique :
  is_reduced_row_echelon_form R₁ → is_reduced_row_echelon_form R₂ → R₁ = R₂ :=
  intros h₁ h₂
  ext i j
  by_cases hij : i < j
  { have := h₁ i j hij
    rw h₁ i at this
    cases this with h1 h2
    { rw h1
      exact (h₂ i j hij).left }
    { rw ←nat.find_eq_zero h2
      exact (h₂ i j hij).right } }
  { by_contra contra
    push_neg at contra
    exact hij (contra.symm ▸ not_lt.1 hij) }
