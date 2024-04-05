import Mathlib.Algebra.Module.Basic

-- 学习策略：从已知到未知，逐个符号解释意思，就能解锁所有符号结构的使用了。分解到最细的知识点就是成功了。
-- 1.线性空间：Module
-- #check Module
-- 拆解学习这个smul_left_injective
#check smul_left_injective
variable {R M: Type*}
variable [Ring R] [AddCommGroup M] [Module R M] [NoZeroSMulDivisors R M] -- smul报错的解决方法。
variable (R)
theorem My_smul_left_injective {x : M} (hx : x ≠ 0) : Function.Injective fun c : R => c • x :=
  fun c d h =>
  sub_eq_zero.mp
    ((smul_eq_zero.mp
          (calc
            (c - d) • x = c • x - d • x := sub_smul c d x
            _ = 0 := sub_eq_zero.mpr h
            )).resolve_right
      hx)

-- 2.基的变换： basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix
