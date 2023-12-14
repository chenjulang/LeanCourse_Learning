import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.Data.Real.Sqrt

namespace Matrix

  -- universe u2 u2' v2
  def m2 : Type := ℕ
  def n2 : Type := ℕ
  def α2 : Type := ℝ

  variable
    -- {m2 := ℕ  } --三个类型
    -- {n2 : ℕ  }
    -- {α2 : ℝ  }
    -- Fintype α意思是α是有限的（即只有有限多个不同的类型元素α）。
    [Fintype n2]
    -- 断言α具有可判定的相等性（即对全部a b : α，a = b是可判定的）
    [DecidableEq n2]
    -- 交换的环，例如实数R
      -- 一个带有两个二元运算的集合 R 是环，即将环中的任意两个元素变为第三个的运算。
        -- 他们称为加法与乘法，通常记作 + 与 ⋅ ，例如 a + b 与 a ⋅ b。
      -- 为了形成一个群这两个运算需满足一些性质：
        -- 环在加法下是一个阿贝尔群（即满足交换律），
        -- 在乘法下为一个幺半群，使得乘法对加法有分配律，即 a ⋅ (b + c) = (a ⋅ b) + (a ⋅ c)。
        -- 关于加法与乘法的单位元素分别记作 0 和 1。
        -- 另外如果乘法也是交换的，即a ⋅ b = b ⋅ a，环 R 称为交换的。
    [CommRing α2]
  -- open Equiv Equiv.Perm Finset Function --这个不用

  -- ---/ 引入MainGoal需要定义的变量
  variable (A : Matrix n2 n2 α2) (B : Matrix n2 n2 α2)
  -- ---/

  def matrix1 : Matrix (Fin 2) (Fin 2) ℝ :=
    ![![1, 2],
      ![3, 4]]

  def matrix2 : Matrix (Fin 2) (Fin 2) ℝ :=
    ![![5, 6],
      ![7, 8]]

  def matrix_product : Matrix (Fin 2) (Fin 2) ℝ := (matrix1 * matrix2)
  #eval matrix_product

  def matrix1_adjugate : Matrix (Fin 2) (Fin 2) ℝ := adjugate matrix1
  def matrix1_det := matrix1.det
  #eval matrix1_adjugate
  -- [ 4 -2
  --  -3  1 ]
  #eval (matrix1_adjugate * matrix1)
  -- [ -2  0
  --    0 -2 ]
  #eval matrix1_det
  --  (-2)
  def scalar : ℝ := 2
  #eval scalar • matrix1




  lemma mul_adjugate2 (A : Matrix n2 n2 α2)
  : A * adjugate A = A.det • (1 : Matrix n2 n2 α2)
  := by
    -- have h1:= A * adjugate A -- : Matrix n n α
    ext i j
    rw [mul_apply, Pi.smul_apply, Pi.smul_apply, one_apply, smul_eq_mul, mul_boole]
    simp only [mul_adjugate_apply]
    simp only [sum_cramer_apply]
    simp only [ne_eq, Finset.sum_pi_single, Finset.mem_univ, ite_true]
    simp only [cramer_transpose_row_self]
    simp only [Pi.single_apply]
    simp only [eq_comm]
    done


  theorem MainGoal [Invertible A.det] : A * (⅟(det A) • adjugate A) = (1 : Matrix n2 n2 α2)
  := by
    rw [mul_smul_comm, mul_adjugate2, smul_smul, invOf_mul_self, one_smul]
    done


end Matrix
