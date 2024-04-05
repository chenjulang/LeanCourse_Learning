import Mathlib.Algebra.Module.Basic
import Mathlib.Algebra.Module.Prod
import Mathlib.Algebra.Module.Submodule.Basic

-- 学习策略：从已知到未知，逐个符号解释意思，就能解锁所有符号结构的使用了。分解到最细的知识点就是成功了。
-- 1.向量空间：Module
#check Module
-- Module的定义不需要证明，是一个定义的结构，拆解学习这个定理smul_left_injective
#check smul_left_injective -- 意思：“左乘”是单射的。
-- variable {R M: Type*}
-- variable [Ring R] [AddCommGroup M] [Module R M] [NoZeroSMulDivisors R M] -- smul报错的解决方法。
-- variable (R)
-- theorem My_smul_left_injective {x : M} (hx : x ≠ 0) : Function.Injective fun c : R => c • x :=
--   by
--   intro c d h
--   have h1:=
--   sub_eq_zero.mp
--     ((smul_eq_zero.mp
--           (calc
--             (c - d) • x = c • x - d • x := sub_smul c d x
--             _ = 0 := sub_eq_zero.mpr h
--             )).resolve_right
--       hx)
--   exact h1


-- 2. 向量空间的乘积:
#check Prod.instModule
-- 定义本身要证明，没有相关定理。
-- open Prod
-- variable {R : Type*} {S : Type*} {M : Type*} {N : Type*}
-- 估计全过程是这样的：
-- instance My_instModule [Semiring R] [AddCommMonoid M] [AddCommMonoid N] [Module R M] [Module R N] :
-- Module R (M × N)
--  where
--   smul := by exact fun a a ↦ a
--   one_smul := by exact fun b ↦ rfl
--   mul_smul := by exact fun x y b ↦ rfl
--   smul_zero := by exact fun a ↦ rfl
--   smul_add := by exact fun a x y ↦ rfl
--   add_smul := by
--     intros R Rt M
--     apply ext_iff.mpr
--     have h1:= add_smul R Rt M
--     apply And.intro
--     have h1' := (ext_iff.1 h1).left
--     have h2' := (ext_iff.1 h1).right
--   zero_smul := sorry
-- instance My2_instModule [Semiring R] [AddCommMonoid M] [AddCommMonoid N] [Module R M] [Module R N] :
-- Module R (M × N)
--   :=
--   {
--     Prod.distribMulAction with -- 这里为什么用到with不知道，去掉也可以。
--     add_smul := fun _ _ _ => mk.inj_iff.mpr ⟨add_smul _ _ _, add_smul _ _ _⟩
--     zero_smul := fun _ => mk.inj_iff.mpr ⟨zero_smul _ _, zero_smul _ _⟩
--   }

-- 3.向量子空间
#check Subspace
-- Submodule是一个直接定义的结构，拆解学习这个ne_zero_of_ortho
open Submodule
#check ne_zero_of_ortho
universe u'' u' u v w
variable {G : Type u''} {S : Type u'} {R : Type u} {M : Type v} {ι : Type w}
variable [Ring R] [IsDomain R]
variable [AddCommGroup M] [Module R M] {b : ι → M}
--
theorem My_ne_zero_of_ortho {x : M} {N : Submodule R M}
(ortho : ∀ (c : R), ∀ y ∈ N, c • x + y = (0 : M) → c = 0)
: x ≠ 0 :=
  mt (fun h => show x ∈ N from h.symm ▸ N.zero_mem) (not_mem_of_ortho ortho)


-- .基的变换： basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix
