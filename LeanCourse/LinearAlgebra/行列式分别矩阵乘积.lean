import Mathlib.LinearAlgebra.Matrix.Determinant
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Paperproof

namespace Matrix

universe u v w z

open Equiv Equiv.Perm Finset Function

-- open Matrix
open BigOperators

variable {m n : Type*} [DecidableEq n] [Fintype n] [DecidableEq m] [Fintype m]

variable {R : Type v} [CommRing R]

local notation "ε " σ:arg => ((sign σ : ℤ) : R)


theorem det_mul2 (M N : Matrix n n R) : det (M * N) = det M * det N :=
  calc
    det (M * N) = ∑ p : n → n, ∑ σ : Perm n, ε σ * ∏ i, M (σ i) (p i) * N (p i) i := by
      simp only [det_apply']
      simp only [mul_apply]
      simp only [prod_univ_sum]
      simp only [mul_sum]
      simp only [Fintype.piFinset_univ]
      rw [Finset.sum_comm]
    _ =
        ∑ p in (@univ (n → n) _).filter Bijective,
          ∑ σ : Perm n, ε σ * ∏ i, M (σ i) (p i) * N (p i) i :=
      (Eq.symm <|
        sum_subset (filter_subset _ _) fun f _ hbij =>
          det_mul_aux <| by simpa only [true_and_iff, mem_filter, mem_univ] using hbij)
    _ = ∑ τ : Perm n, ∑ σ : Perm n, ε σ * ∏ i, M (σ i) (τ i) * N (τ i) i :=
      (sum_bij (fun p h => Equiv.ofBijective p (mem_filter.1 h).2) (fun _ _ => mem_univ _)
        (fun _ _ => rfl) (fun _ _ _ _ h => by injection h) fun b _ =>
        ⟨b, mem_filter.2 ⟨mem_univ _, b.bijective⟩, coe_fn_injective rfl⟩)
    _ = ∑ σ : Perm n, ∑ τ : Perm n, (∏ i, N (σ i) i) * ε τ * ∏ j, M (τ j) (σ j) := by
      simp only [mul_comm, mul_left_comm, prod_mul_distrib, mul_assoc]
    _ = ∑ σ : Perm n, ∑ τ : Perm n, (∏ i, N (σ i) i) * (ε σ * ε τ) * ∏ i, M (τ i) i :=
      (sum_congr rfl fun σ _ =>
        Fintype.sum_equiv (Equiv.mulRight σ⁻¹) _ _ fun τ => by
          have : (∏ j, M (τ j) (σ j)) = ∏ j, M ((τ * σ⁻¹) j) j := by
            rw [← (σ⁻¹ : _ ≃ _).prod_comp]
            simp only [Equiv.Perm.coe_mul, apply_inv_self, Function.comp_apply]
          have h : ε σ * ε (τ * σ⁻¹) = ε τ :=
            calc
              ε σ * ε (τ * σ⁻¹) = ε (τ * σ⁻¹ * σ) := by
                rw [mul_comm, sign_mul (τ * σ⁻¹)]
                simp only [Int.cast_mul, Units.val_mul]
              _ = ε τ := by simp only [inv_mul_cancel_right]

          simp_rw [Equiv.coe_mulRight, h]
          simp only [this])
    _ = det M * det N := by
      simp only [det_apply', Finset.mul_sum, mul_comm, mul_left_comm, mul_assoc]



-- Perm n：表示一个大小为n的置换集合。置换是一种重新排列一组元素的操作，其中元素的顺序被改变。
--        对于给定的n，Perm n由所有可能的从1到n的排列组成。例如，当n=3时，Perm n表示可能的排列集合为{[1, 2, 3], [1, 3, 2], [2, 1, 3], [2, 3, 1], [3, 1, 2], [3, 2, 1]}。
theorem det_apply2 (M : Matrix n n R) : M.det = ∑ σ : Perm n, Equiv.Perm.sign σ • ∏ i, M (σ i) i
:=
  MultilinearMap.alternatization_apply _ M

def detRowAlternating2 : AlternatingMap R (n → R) R n :=
  MultilinearMap.alternatization ((MultilinearMap.mkPiAlgebra R n R).compLinearMap LinearMap.proj)
-- 因为alternatization是在namespace为MultilinearMap的namespace里面定义的，所以使用的时候需要传入一个默认的主体参数，
-- 参数类型就是MultilinearMap结构的类型，例如MultilinearMap R (n → R) R

--  proj 方法返回一个线性映射，该映射接受一个函数并在索引 i 处提取该函数的值
#check LinearMap.proj

--  toFun 方法定义了生成的多线性映射对类型 M₁ 的输入 m 的操作。它将每个线性映射 f i 应用于相应的组件 (m i) ，然后将转换后的组件传递给多线性映射 g 。换句话说， toFun m 通过将 f i 应用于每个组件 (m i) ，然后将这些转换后的组件传递给 g 来计算多线性映射输出。
#check (MultilinearMap.mkPiAlgebra R n R).compLinearMap

--  toFun m := ∏ i, m i ，表达式 ∏ i, m i 表示每个索引 i 的函数 m 的所有值的乘积。该表达式用作 MultilinearMap 对象的 toFun 方法的实现
#check MultilinearMap.mkPiAlgebra R n R -- : MultilinearMap R (fun x ↦ R) R

-- MultilinearMap R (fun x ↦ R) R表示一个从(x → R)（即函数类型）到R的
-- “多线性映射对象”：
#check MultilinearMap R (fun x ↦ R) R
-- 张量是一个多元线性映射，它接受一些向量、矩阵或其他张量作为输入，并生成一个标量或另一个张量作为输出。



-- /---------------------/
-- /---------------------/
-- /---------------------/

universe u2 u2' v2
variable {l2 : Type*} {m2 : Type u2} {n2 : Type u2'} {α2 : Type v2}
-- open Matrix BigOperators Equiv Equiv.Perm Finset
variable [Fintype n2] [DecidableEq n2] [CommRing α2]
-- noncomputable instance inv2 : Inv (Matrix n2 n2 α2) :=
--   ⟨fun A => Ring.inverse A.det • A.adjugate⟩
-- theorem inv_def2 (A : Matrix n2 n2 α2) : A⁻¹ = Ring.inverse A.det • A.adjugate :=
--   rfl

set_option trace.Meta.synthInstance true
theorem mul_inv_rev2 (A B : Matrix n2 n2 α2) : (A * B)⁻¹ = B⁻¹ * A⁻¹ := by
  simp only [inv_def]
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, det_mul, adjugate_mul_distrib,
    Ring.mul_inverse_rev]


theorem mul_adjugate2 (A : Matrix n2 n2 α2) : A * adjugate A = A.det • (1 : Matrix n2 n2 α2) := by
  -- have h1:= A * adjugate A -- : Matrix n n α
  ext i j
  rw [mul_apply, Pi.smul_apply, Pi.smul_apply, one_apply, smul_eq_mul, mul_boole]
  simp only [mul_adjugate_apply]
  simp only [sum_cramer_apply]
  simp only [ne_eq, sum_pi_single, mem_univ, ite_true]
  simp only [cramer_transpose_row_self]
  simp only [Pi.single_apply]
  simp only [eq_comm]





end Matrix
