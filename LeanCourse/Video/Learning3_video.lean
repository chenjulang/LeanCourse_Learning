import Mathlib.LinearAlgebra.Matrix.Determinant
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.GroupTheory.Perm.Sign
import Mathlib.Data.Real.Sqrt
import Mathlib.Data.List.Perm

-- 本文件最终目标是证明行列式中矩阵相乘的运算规律：第二篇
  -- det (M * N) = det M * det N

universe u v w z

open Equiv Equiv.Perm Finset Function

namespace Matrix --目的是避免模糊定义mul_apply

  open Matrix BigOperators

  variable {m n : Type*} [DecidableEq n] [Fintype n] [DecidableEq m] [Fintype m]
  variable {R : Type v} [CommRing R]

  local notation "ε " σ:arg => ((sign σ : ℤ) : R) -- “元编程”，创造新符号，ε 接收一个参数，结果就是sign σ
  set_option linter.unusedVariables false --

  -- 没讲到的部分会分别用“前置知识”视频发出来，先记???


  def detRowAlternating2
  : AlternatingMap R (n → R) R n  --- 最后这个参数n属于补充说明,实际形式上只需传三个参数即可
  :=
    MultilinearMap.alternatization ( -- ???基本的要素都齐了，求和，连乘，全体置换，置换的符号。具体逻辑还不懂
      (MultilinearMap.mkPiAlgebra R n R).compLinearMap
        LinearMap.proj)

  abbrev det2 (M : Matrix n n R): R :=
    (detRowAlternating2) M

  def printPerms (n : ℕ) : List (List ℕ) :=
    List.map List.reverse (List.permutations (List.range n))
  -- ???Perm n的理解错了：Perm n即Equiv α α
  -- α ≃ α 则是 Equiv α α的记号
  -- α ≃ β is the type of functions from α → β with a two-sided inverse，是有双边逆的映射，而不是等价关系。
  -- #eval printPerms 4
  -- #eval printPerms 3


  -- 正式开始：
  lemma MainGoal_1 (M N : Matrix n n R):
  det (M * N)
  = ∑ p : n → n,
      ∑ σ : Perm n,
        (ε σ)
        *
        ∏ i,
          M (σ i) (p i) * N (p i) i
    := by
    simp only [det_apply']
    simp only [mul_apply]
    simp only [prod_univ_sum] -- ???与"先连加，再连乘，等于，先连乘，再连加"，还有笛卡尔积“全覆盖”，相关的定理
    -- 如何理解Fintype.piFinset t
    -- 假设 t 是一个从集合 {1, 2} 到有限集合的映射，其中 t(1) = {a, b}，t(2) = {x, y}。
        -- 那么 Fintype.piFinset t 就表示集合 {(a, x), (a, y), (b, x), (b, y)}，即这两个集合的笛卡尔积。
    -- 举例说明prod_univ_sum
    --     首先，让我们假设集合α包含元素1和2，对应的集合分别为t1和t2。而且我们有以下映射关系：
    -- t1 = {a, b}, t2 = {x, y}
    -- 对应的函数f如下：
    -- f(1, a) = 2, f(1, b) = 3, f(2, x) = 1, f(2, y) = 4
    -- 现在我们来计算左侧和右侧的值。
    -- 左侧：(∏ a, ∑ b in t a, f a b)
    -- = (∑ b in t1, f(1, b)) * (∑ b in t2, f(2, b))
    -- = (f(1, a) + f(1, b)) * (f(2, x) + f(2, y))
    -- = (2 + 3) * (1 + 4)
    -- = 5 * 5
    -- = 25
    -- 右侧：∑ p in Fintype.piFinset t, ∏ x, f x (p x)
    -- = f(1, a) * f(2, x) + f(1, a) * f(2, y) + f(1, b) * f(2, x) + f(1, b) * f(2, y)
    -- = 2 * 1 + 2 * 4 + 3 * 1 + 3 * 4
    -- = 2 + 8 + 3 + 12
    -- = 25
-- 因此，根据 Finset.prod_univ_sum 定理，左侧和右侧的值相等，都等于25。
    simp only [mul_sum] --???用gpt举个例子来理解
    simp only [Fintype.piFinset_univ] --???Fintype.piFinset的使用 -- 1，2，3 =》 3，2，1
    rw [Finset.sum_comm] --???两阶求和顺序互换的相关定理
    done

  lemma MainGoal_2 (M N : Matrix n n R):
  ∑ p : n → n,
    ∑ σ : Perm n,
      ε σ
      *
      ∏ i,
        M (σ i) (p i) * N (p i) i
  = ∑ p in (@univ (n → n) _).filter Bijective,
      ∑ σ: Perm n,
        (ε σ)
        *
        (∏ i,
          M (σ i) (p i) * N (p i) i)
    := by
    apply Eq.symm
    apply sum_subset --s₁ ⊆ s₂， x ∈ s₂, x ∉ s₁的情况为0，则可以直接去掉
    · intro h1 h2
      exact mem_univ h1
    · intros h3 h4 h5
      apply det_mul_aux -- ???这个先不理解，后面专门出一个视频来教如何读证明并且分解证明成策略模式。
        -- 一个先连乘，再连加的东西，结果是0，关键是非双射导致的，有点意思
        -- 举个例子，p=[1,1],Perm 2只有两个变换：1.恒等变换，简称id；2.换位变换，简称swap
        -- ε id * (M (id 1)(p 1) * N (p 1)1) * (M (id 2)(p 2) * N (p 2)2)
        -- = 1 * (M 1 1 * N 1 1) * (M 2 1 * N 1 2)
        -- = M 1 1 * N 1 1 * M 2 1 * N 1 2

        -- ε swap * (M (swap 1)(p 1) * N (p 1)1) * (M (swap 2)(p 2) * N (p 2)2)
        -- = -1 * (M 2 1 * N 1 2) * (M 1 1 * N 1 1)
        -- = -M 2 1 * N 1 2 * M 1 1 * N 1 1
      simp only [mem_filter] at h5 -- 就是filter的定义呗，是属于某个集合里面的，而且满足条件1
      simp only [mem_univ] at h5
      simp only [true_and_iff] at h5
      set h6 := fun x ↦ h3 x -- 写这个h6,h7是为了补充说明，其实这里h6就是和h3同一个映射，写法不一样而已
      -- have h7: h6=h3 -- 为了让大家理解
      -- := by
      --   exact rfl
      exact h5
    done

  lemma MainGoal_3 (M N : Matrix n n R):
  ∑ p in (@univ (n → n) _).filter Bijective,
    ∑ σ: Perm n,
      ε σ
      *
      (∏ i,
        M (σ i) (p i) * N (p i) i)
  =
  ∑ τ : Perm n,
    ∑ σ : Perm n,
      (ε σ)
      *
      (∏ i,
        M (σ i) (τ i) * N (τ i) i)
    := by
    rw [sum_comm]
    rw [sum_comm] -- 这两步sum_comm相当于没变，只改成了x,y
    refine' sum_bij _ _ _ _ _ -- ???这个需要问一下gpt找到数学世界里的对应定理名称。
    -- 不一样的定义域s、t，不同的函数f、g，求和相同，需要什么条件呢。5个条件
    -- 举例：
    -- 假设我们有以下集合和映射：
    -- 令 α = {1, 2, 3}，即集合 {1, 2, 3}。
    -- 令 β = {a, b, c}，即集合 {a, b, c}。
    -- 令 γ = {x, y, z}，即集合 {x, y, z}。
    -- 定义函数 f: α → β 和 g: γ → β 如下：
    -- 对于 f，我们定义 f(1) = a，f(2) = b，f(3) = c。
    -- 对于 g，我们定义 g(x) = a，g(y) = b，g(z) = c。
    -- 接下来，定义函数 i: α → γ 如下：
    -- i(1) = x
    -- i(2) = y
    -- i(3) = z
    -- 现在，我们可以检查定理的条件是否满足：
    -- 映射关系 (h)： 对于所有 a 属于 {1, 2, 3}，我们有 f a = g (i a)。
    -- 这是满足的，例如，对于 a = 1，我们有 f(1) = a 和 g(i(1)) = g(x) = a。
    -- i 是单射 (i_inj)： 如果 i a₁ = i a₂，则 a₁ = a₂。
    -- 这是满足的，因为 i 的定义是一对一的，不同的 a 映射到不同的 γ 中的元素。
    -- i 是满射 (i_surj)： 对于任意 b 属于 {x, y, z}，存在 a 属于 {1, 2, 3}，使得 b = i a。
    -- 这也是满足的，因为 i 的定义覆盖了整个 γ。
    -- 如果这些条件满足，我们可以应用定理，从而得出：
    -- [
    -- \prod_{x \in {1, 2, 3}} f(x) = \prod_{x \in {x, y, z}} g(x)
    -- ]
    -- 即，
    -- [
    -- abc = abc
    -- ]
    · intros ih1 ih2 -- 这里ih1潜台词是随机的ih1
      have ih3:= (mem_filter.mp ih2).right
      have ih4:= ofBijective ih1 ih3 --???现实中的意义有待
      simp only [Perm]
      exact ih4
    -- 如果这里定义错了，下面满盘皆输
    -- 注意不能像以下这样定义
    -- intros ih1 ih2
    --   have ih3:= Equiv.refl n
    --   simp only [Perm]
    --   exact ih3
    · intro h1
      intro h2 --原来这里会用到refine1的证明
      simp only [mem_univ]
    · intros h_1 h_2
      have h_3:= mem_filter.1 h_2
      obtain ⟨h_4,h_5⟩ := h_3
      simp only [id_eq]
      set h_6 := ofBijective h_1 h_5 -- h_1和h_6相等吗？，由ofBijective的toFun定义知道就是h_1
      -- have h1_equal_h6 : h_1=h_6 -- 为了说明而写的，因为ofBijective的实际效果是和toFun相同的，是定义导致的相同
      --   := by
      --   exact rfl
      rfl
    · intros inj_1 inj_2 inj_3 inj_4 inj_5
      simp only [id_eq] at inj_5 -- 看起来很明显，但就是完成不了
      ext x
      have inj_6:= ofBijective_apply inj_1
      have inj_7:= ofBijective_apply inj_2
      have bij_inj_3:= (mem_filter.mp inj_3).right
      rw [← inj_6]
      rw[inj_5,
      inj_7]
      done
    · intros b x
      refine' Exists.intro b _ -- 要证明存在某个原始使得某个命题成立，只需要，给出例子，然后让例子代入后面描述的命题中，该命题为真即可。
      -- 比如这里就是把a全部替换成了b
      -- 如果第二个参数中不用直接替换的，比如下面这行，就直接证明第二个参数代表的命题即可
      refine' Exists.intro _ _ -- 比如这里ha在第二个参数中没有需要替换的，直接证明第二个命题即可
      · refine' mem_filter.mpr _
        constructor
        · refine' mem_univ (↑b)
        · exact Equiv.bijective b
      · refine' coe_fn_injective _ --在外层套了一个不变的映射
        simp only [id_eq]
        simp only [FunLike.coe_fn_eq]
        refine' Equiv.ext _
        intros x2
        -- ↑(ofBijective ↑b (_ : Bijective ↑b))前面这个和↑b作用效果一样吗?查一下ofBijective的toFun := f定义就知道，就是f本身
        -- 下面是进一步的探究，不看了
        -- have equalTest: (ofBijective ↑b (_ : Bijective ↑b)) = b
          -- := by
          -- refine ((fun {α β} {e₁ e₂} ↦ Equiv.coe_inj.mp) rfl).symm
        rfl
      done
    done




end Matrix
