import Mathlib.LinearAlgebra.Matrix.Basis
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.Data.Real.Sqrt


-- variable (k1 k2 k3 : ℝ)

-- def v1 : Fin 3 → ℝ := λ i => if i = 0 then 1 else 0
-- def v2 : Fin 3 → ℝ := λ i => if i = 1 then 1 else 0
-- def v3 : Fin 3 → ℝ := λ i => if i = 2 then 1 else 0

-- theorem linear_independence_example
-- : ∀ k1 k2 k3 : ℝ, k1 • v1 + k2 • v2 + k3 • v3 = 0
--   →
--   k1 = 0 ∧ k2 = 0 ∧ k3 = 0
-- := by
--   intros k1 k2 k3 h
--   constructor
--   · sorry
--   · constructor
--     · sorry
--     · sorry
--   -- have h₁ := eq_zero_of_add_eq_zero_left h

--   -- have h₁ : k1 = 0 := by eq_zero_of_add_eq_zero_left h
--   -- have h₂ : k2 = 0, from eq_zero_of_add_eq_zero_left (eq_zero_of_eq_zero_of_eq_zero h₁),
--   -- have h₃ : k3 = 0, from eq_zero_of_add_eq_zero_left (eq_zero_of_eq_zero_of_eq_zero (eq_zero_of_eq_zero_of_eq_zero h₁)),
--   -- exact ⟨h₁, h₂, h₃⟩,



------------------------
-- 定义一个简单的矩阵类型
-- structure matrix (m n : Type*) (α : Type*) :=
-- (entries : m → n → α)

-- namespace matrix

-- -- 矩阵加法
-- def add {m n : Type*} [has_add α] (A B : matrix m n α) : matrix m n α :=
-- ⟨λ i j => A.entries i j + B.entries i j⟩
