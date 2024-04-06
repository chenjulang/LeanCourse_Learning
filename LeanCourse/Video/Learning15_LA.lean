import Mathlib.Algebra.Module.Basic
import Mathlib.Algebra.Module.Prod
import Mathlib.Algebra.Module.Submodule.Basic
import Mathlib.LinearAlgebra.Quotient

-- 学习策略：从已知到未知，逐个符号解释意思，就能解锁所有符号结构的使用了。分解到最细的知识点就是成功了。

section s1

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

end s1

section s2
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
end s2

section s3
-- 3.向量子空间
#check Subspace
-- Submodule是一个直接定义的结构，拆解学习这个ne_zero_of_ortho
open Submodule
#check ne_zero_of_ortho
-- universe u'' u' u v w
-- variable {G : Type u''} {S : Type u'} {R : Type u} {M : Type v} {ι : Type w}
-- variable [Ring R] [IsDomain R]
-- variable [AddCommGroup M] [Module R M] {b : ι → M}
-- --
-- theorem My_ne_zero_of_ortho {x : M} {N : Submodule R M}
-- (ortho : ∀ (c : R), ∀ y ∈ N, c • x + y = (0 : M) → c = 0)
-- : x ≠ 0 :=
--   by
--   have h1: x = 0 → x ∈ N := by
--     intro h
--     -- exact (h.symm ▸ N.zero_mem) -- 写法1 下面是等价代码：
--     -- have h2:= @Eq.rec M 0 (fun x h ↦ x ∈ N) (Submodule.zero_mem N) x h.symm  -- 写法2
--     -- exact h2
--     let h3:= h.symm ▸ Submodule.zero_mem N -- 写法3
--     exact h3
--   have h2: x ∉ N := by
--     apply not_mem_of_ortho -- 只能用0来组合得到0，那么这个x不属于这个空间。也就是不能合并抵消。
--     exact ortho
--   exact mt h1 h2
end s3

section s4
-- 4.商空间
open Submodule
#check hasQuotient
-- 定义需要证明，拆解学习定理：coe_quotEquivOfEqBot_symm
variable {R M : Type*} {r : R} {x y : M} [Ring R] [AddCommGroup M] [Module R M]
instance hasQuotient : HasQuotient M (Submodule R M) where
  quotient' := fun p => Quotient (quotientRel p) -- 意思：由一个子空间出发，提供一个等价关系，能得到一个商空间。注意：商空间里的元素是等价类。
-- 三维的等价关系之一是：2个向量空间中的元素相减的结果A，A在子空间上。
-- 那要怎么在lean上写出来呢？完全想不出来。
--
#check coe_quotEquivOfEqBot_symm -- 意思：
variable (p p' : Submodule R M)
theorem My_coe_quotEquivOfEqBot_symm (hp : p = ⊥) :
    ((p.quotEquivOfEqBot hp).symm : M →ₗ[R] M ⧸ p) = p.mkQ :=
  rfl
  -- 假设我们有一个整数环 Z，并考虑一个等价关系 p，其中 p 表示能够被 2 整除的整数。
  -- 也就是说，p 是一个偶数的等价类。
  -- 根据给定的等价关系 p，我们可以构建商空间 Z ⧸ p，其中每个等价类代表一组具有相同余数的整数。
  -- 例如，商空间中的等价类 [0] 代表了所有能够被 2 整除的整数，等价类 [1] 代表了所有余数为 1 的奇数。
  -- 在这个例子中，我们可以使用定理 coe_quotEquivOfEqBot_symm 来说明等价类映射的对称性。
  --
  -- 假设我们有一个整数 n，我们可以使用等价类映射 p.mkQ 将其映射到商空间 Z ⧸ p 中的等价类。
  -- 例如，如果 n 是一个偶数，那么 n 会被映射到 [0] 这个等价类中。
  -- 如果 n 是一个奇数，那么 n 会被映射到 [1] 这个等价类中。
  -- 根据定理 coe_quotEquivOfEqBot_symm，我们可以知道等价类映射的逆映射是成立的。
  -- 也就是说，商空间中的等价类 [0] 对应的逆映射将整数 n 映射回原始的整数 n（如果 n 是偶数），
  -- 而等价类 [1] 对应的逆映射将整数 n 映射回原始的整数 n（如果 n 是奇数）。
  -- 这个定理的含义是，当等价关系 p 是一个底元素（在这个例子中是 2），
  -- 商空间的等价类映射的逆映射将整数映射回原始的整数。
end s4




-- 通过项目学数学：人造卫星拍照用的“线性码“，丘维声《大学高等代数课程创新教材第二版下册》P.226

-- .基的变换： basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix
