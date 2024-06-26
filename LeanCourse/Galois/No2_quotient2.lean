import Mathlib.LinearAlgebra.Basic
import Mathlib.GroupTheory.QuotientGroup
import Mathlib.GroupTheory.Subgroup.Basic
import Mathlib.GroupTheory.Coset

open Subgroup QuotientGroup

namespace my_quotient_group
-- 当我们具体化这个例子时，假设我们考虑整数的加法群 (ℤ, +)。
-- 首先，我们定义一个子集 H，表示所有偶数的集合，即 H = {2k | k ∈ ℤ}。我们可以证明这个子集 H
  -- 是整数加法群 (ℤ, +) 的一个子群。
-- 然后，我们将 H 视为正规子群。在这个例子中，正规子群的概念是由 [Normal H] 约束表示的。
  -- 接下来，我们定义 lcoset_setoid2 函数，它创建了关于 H 的等价关系。这个等价关系的定义是基于左陪集
  -- 的概念。具体来说，对于整数集合中的两个元素 a 和 b，我们定义它们属于相同的左陪集，当且仅当它们的差
  --  a - b 是偶数。这个等价关系满足自反性、对称性和传递性的性质，从而构成了一个等价关系。
-- 最后，我们使用 quotient 定义了商集。商集是由与子集 H 相关的等价类组成的集合。在这个例子中，商集可
  -- 以看作是整数加法群 (ℤ, +) 中与偶数集合 H 相关的左陪集的集合。每一个商集中的元素对应于一个左陪集，
  -- 其中左陪集包含了与偶数集合 H 相关的整数。

  variable {A B C : Type}
  variable [Group A] (H : Set A) (H : Subgroup A) [Normal H]

  def lcoset_setoid2: Setoid A
  := by
    apply Setoid.mk
    · exact leftCosetEquivalence_rel H
    done

  def quotient := Quot (lcoset_setoid2 H).1

  -- #check QuotientGroup
end my_quotient_group
