import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.Data.Real.Sqrt

set_option trace.Meta.synthInstance true

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

  -- 实际案例：
  def matrix1 : Matrix (Fin 2) (Fin 2) ℝ :=
    ![![1, 2],
      ![3, 4]]
  def matrix2 : Matrix (Fin 2) (Fin 2) ℝ :=
    ![![5, 6],
      ![7, 8]]
  def matrixUnit : Matrix (Fin 2) (Fin 2) ℝ :=
    ![![1, 0],
      ![0, 1]]

  -- #check A * B

  def matrix1_adjugate : Matrix (Fin 2) (Fin 2) ℝ := adjugate matrix1
  def matrix1_det := matrix1.det
  #eval matrix1
  #eval matrix1_adjugate -- 伴随矩阵
  -- [ 4 -2
  --  -3  1 ]
  #eval (matrix1_adjugate * matrix1) -- 伴随矩阵 矩阵乘 矩阵
  -- [ -2  0
  --    0 -2 ]
  #eval matrix1_det -- 矩阵的行列式，是一个实数
  --  (-2)
  #eval matrix1_det • matrixUnit -- 矩阵的行列式 数乘 矩阵
  -- [ -2  0
  --    0 -2 ]
  -- 可以看出matrix1_det • matrixUnit 和 matrix1_det • matrixUnit 结果相等



  -- Finset.sum Finset.univ的使用：
    -- def my_set := (Finset.univ : (Finset (Fin 2)))
    -- #eval my_set
    --   Finset.sum需要两个参数：
    -- 一个有限集合，表示对该集合中的元素进行求和。
    -- -- 一个返回可相加的类型（即带有has_add类型类）的函数表达式，用于指定如何将集合中的元素相加。
    -- def sum_of_numbers : ℕ
    --   := Finset.sum (Finset.range 11) (fun x => x)
    -- #eval sum_of_numbers
    -- def sum_of_numbers2 : ℕ
    --   := Finset.sum my_set (fun x => x)
    -- #eval sum_of_numbers2





  -- 抽象证明：
 -- 四个领域 1.adjugate 2.cramer 3.det 4.Pi.single
  -- 1↔2,4 2↔3,4 1↔3

  -- 1↔2,4的桥梁
  lemma mul_adjugate_apply2 (A : Matrix n2 n2 α2) (i j k) :
    (A i k) * (adjugate A k j) = (cramer Aᵀ) (Pi.single k (A i k)) j
  := by
    rw [
    ← smul_eq_mul,
    adjugate, -- 1↔2,4 伴随矩阵的定义来的。伴随矩阵即每一项先变余子式行列式，再加正负号(定义为-1的i+j次方)，再转置
    of_apply,
    ← Pi.smul_apply,
    ← LinearMap.map_smul,
    ← Pi.single_smul',
    smul_eq_mul,
    mul_one]


  -- 1↔3 的桥梁(由1↔2,4 和 2↔3,4 和 4↔null 得到)
  lemma mul_adjugate2
  (A : Matrix n2 n2 α2)
  : A * adjugate A = A.det • (1 : Matrix n2 n2 α2)
  := by
    -- have h1:= A * adjugate A -- : Matrix n n α
    -- have h2:= A.det • (1 : Matrix n2 n2 α2) -- : Matrix n2 n2 α2
    ext i k
    rw [
    mul_apply,  -- 作用：(M * N) i k = Finset.sum Finset.univ fun j ↦ M i j * N j k
    -- 将 (A * adjugate A) i k
    -- 其中 M=>A, N=>adjugate A
    -- 变成了等号右边 (Finset.sum Finset.univ fun j ↦ A i j * adjugate A j k)
    Pi.smul_apply, -- 作用：(b • x) i = b • (x i)
    -- 将 (det A • 1) i k
    -- 其中 b=>det A,x=>1,i=>i
    -- 变成了 ( det A • (1 i) ) k
    -- * 暂时理解成OfNat.ofNat 1 就是 1的单位矩阵(1 : Matrix n n α)
    Pi.smul_apply,
    -- 再作用一次 (b • x) i = b • (x i)
    -- 其中 b=>det A,x=>(1 i),i=>k
    -- 变成了det A • (1 i k)
    one_apply,
    smul_eq_mul,
    mul_boole]
    simp only [mul_adjugate_apply2] -- 1↔2,4的桥梁
    simp only [sum_cramer_apply]
    simp only [Finset.sum_pi_single]
    simp only [Finset.mem_univ]
    simp only [ite_true]
    -- simp only [ne_eq, Finset.sum_pi_single, Finset.mem_univ, ite_true]
    simp only [cramer_transpose_row_self] -- 2↔3,4的桥梁
    simp only [Pi.single_apply] -- 4↔null的桥梁
    simp only [eq_comm]
    done

  -- 1↔3 的桥梁
  theorem MainGoal [Invertible A.det] : A * (⅟(det A) • adjugate A) = (1 : Matrix n2 n2 α2)
  := by
    rw [
    mul_smul_comm,
    mul_adjugate2,
    smul_smul,
    invOf_mul_self,
    one_smul]
    done


end Matrix
