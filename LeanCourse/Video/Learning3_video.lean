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
    (detRowAlternating2) M -- 这里为什么类型是R，因为detRowAlternating2相当于detRowAlternating2.toFun


    --  前置知识
  -- Perm 的使用,排列组合
  -- 以下是一些关于 Perm n 的示例，其中 n 取不同的值：
  -- 当 n = 1 时，Perm 1 表示长度为 1 的置换，即 [0]。
  -- 当 n = 2 时，Perm 2 表示长度为 2 的置换，共有两种情况：[0, 1] 和 [1, 0]。
  -- 当 n = 3 时，Perm 3 表示长度为 3 的置换，共有六种情况：[0, 1, 2]、[0, 2, 1]、[1, 0, 2]、[1, 2, 0]、[2, 0, 1] 和 [2, 1, 0]。
-- #eval Finset.val (Finset.univ : Finset (Fin 4))
def printPerms (n : ℕ) : List (List ℕ) :=
  List.map List.reverse (List.permutations (List.range n))
 -- Perm n的理解错了：Perm n即Equiv α α
  -- α ≃ α 则是 Equiv α α的记号
  -- α ≃ β is the type of functions from α → β with a two-sided inverse，是有双边逆的映射，而不是等价关系。
-- #check Perm n
-- #eval printPerms 4
-- #eval printPerms 3 -- [0, 1, 2] [2, 1, 0]



  -- 正式开始：
  lemma MainGoal_1 (M N : Matrix n n R) :
  det (M * N)
  = ∑ p : n → n, -- {1,2,3} → {1,2,3}
      ∑ σ : Perm n,
        ε σ
        *
        ∏ i,
          M (σ i) (p i) * N (p i) i
    := by
    simp only [det_apply']
    simp only [mul_apply]
    simp only [prod_univ_sum] -- 我称之为连加和连乘之间的分配律，与"先连加，再连乘，等于，先连乘，再连加"，还有笛卡尔积“全覆盖”，相关的定理
    -- Fintype.piFinset的使用：
    -- 接受1个参数，参数一：t 是一个从集合到有限集合的映射。
    -- 结果是一个笛卡尔积
    -- ∏ a : α, ∑ b in t a, f a b = ∑ p in Fintype.piFinset t, ∏ x : α, f x (p x)
    -- ∏ x_1 : n, ∑ j : n, M (↑x x_1) j * N j x_1
    -- = ∑ p in Fintype.piFinset fun a ↦ univ, ∏ x_1 : n, M (↑x x_1) (p x_1) * N (p x_1) x_1
    -- 实际上就是：
    -- 比如n=2
    -- α = {1, 2}
    --  f₁(a,b) = M (↑x a) b * N b a
    -- t a由于j : n范围还是{1, 2} ，所以知道定义t为 t(1) = {1，2}, t(2)= {1，2}
    -- 左边就是：（
    --    (M (↑x 1) 1 * N 1 1 + M (↑x 1) 2 * N 2 1）) //x_1=1，j=1，2
    -- *  (M (↑x 2) 1 * N 1 2 + M (↑x 2) 2 * N 2 2）) //x_1=2，j=1，2
    --  = (f₁ 1 1 + f₁ 1 2)
    --  * (f₁ 2 1 + f₁ 2 2)
    -- 右边是：
    -- Fintype.piFinset t 是{(1, 1), (1, 2), (2, 1), (2, 2)}
    -- f₂(a,b) = M (↑x b) (a b) * N (a b) b
    --   M (↑x 1) (1) * N (1) 1  *  M (↑x 2) (1) * N (1) 2  //a=(1, 1) b=1，2
    -- + M (↑x 1) (1) * N (1) 1  *  M (↑x 2) (2) * N (2) 2  //a=(1, 2) b=1，2
    -- + M (↑x 1) (2) * N (2) 1  *  M (↑x 2) (1) * N (1) 2  //a=(2, 1) b=1，2
    -- + M (↑x 1) (2) * N (2) 1  *  M (↑x 2) (2) * N (2) 2 //a=(2, 2) b=1，2
    -- 假设 t 是一个从集合 {1, 2} 到有限集合的映射，其中 t(1) = {a, b}，t(2) = {x, y}。
        -- 那么 Fintype.piFinset t 就表示集合 {(a, x), (a, y), (b, x), (b, y)}，即这两个集合t(1)和t(2)的笛卡尔积。
    -- 举例说明prod_univ_sum
    --     首先，让我们假设集合α包含元素1和2，对应的集合分别为t1和t2。而且我们有以下映射关系：
    -- α = {1, 2}
    -- t(1) = {a, b}, t(2) = {x, y}
    -- 对应的函数f假设定义如下：
    -- f(1, a) = A1 , f(1, b) = A2, f(2, x) = A3, f(2, y) = A4
    -- 现在我们来计算左侧和右侧的值。
    -- 左侧：(∏ a, ∑ b in t a, f a b)
    -- = (∑ b in t(1), f(1, b)) * (∑ b in t(2), f(2, b))
    -- = (f(1, a) + f(1, b)) * (f(2, x) + f(2, y))
    -- = (A1 + A2) * (A3 + A4)
    -- 右侧：∑ p in Fintype.piFinset t, ∏ x, f x (p x)
    -- = f(1, a) * f(2, x)
    -- + f(1, a) * f(2, y)
    -- + f(1, b) * f(2, x)
    -- + f(1, b) * f(2, y)
    -- = A1 * A3 + A1 * A4 + A2 * A3 + A2 * A4
-- 因此，根据 Finset.prod_univ_sum 定理，左侧和右侧的值相等，都等于25。
    simp only [mul_sum]
    simp only [Fintype.piFinset_univ]
    --n是有限的 n → n
    -- Fintype.piFinset fun a ↦ univ 笛卡尔积 ， t(1)={1,2}, t(2)={1,2}
    -- 两者为什么恰好相等？
    -- 举例说明n=2 , n={1,2} → n={1,2}
    -- 对于任意个映射f : n → n
      -- 1  => ? 1/2
      -- 2  => ? 1/2
      -- 1  => 2
      -- 2  => 1
      -- 写成（2，1），
        -- （1，1），（1，2）， （2，2）
      -- 实际上就是n={1,2} 分别映射到→ n={2,1}
    -- 笛卡尔积是什么呢(1,1) (1,2) (2,1) (2,2)
    -- //
    -- 再举例说明n=3,  t(1)={1,2,3}, t(2)={1,2,3}， t(3)={1,2,3}
    -- n={1,2,3} → n={1,2,3}
    -- 对于某个映射f : n → n
      -- 1  => ? 1/2/3
      -- 2  => ? 1/2/3
      -- 3  => ? 1/2/3
       -- 写成（2，1，3）......
    -- 笛卡尔积是什么呢（1，3，2），（2，1，3）
    rw [Finset.sum_comm]
    done


  lemma MainGoal_2 (M N : Matrix n n R):
  ∑ p : n → n,
    ∑ σ : Perm n,
      (ε σ)
      *
      ∏ i,
        M (σ i) (p i) * N (p i) i
  = ∑ p in (@univ (n → n) _).filter Bijective,
      ∑ σ : Perm n,
        ε σ
        *
        (∏ i,
          M (σ i) (p i) * N (p i) i)
    := by
    apply Eq.symm
    apply sum_subset --s₁ ⊆ s₂， x ∈ s₂, x ∉ s₁的情况为0，则可以直接去掉
    · intro h1 h2
      exact mem_univ h1
    · intros h3 h4 h5
      apply det_mul_aux -- 这个先感性理解。
      --  ∑ σ : Perm n, ↑↑(↑sign σ) * ∏ x : n, M (↑σ x) (p x) * N (p x) x = 0
        -- 一个先连乘，再连加的东西，结果是0，关键是非双射导致的，有点意思
        -- 举个例子n=2，p不是双射，举例p=(1,1) (1=>1,2=>1),Perm 2只有两个变换：(1,2) => (1,2) 2!
        -- 固定式： M？(1)*N(1)[1] * M？(1)*N(1)[2]
        -- 1.恒等变换，简称id=σ=(1,2)；2.换位变换，简称swap=σ=(2,1)
        -- ε id * (M (id 1)(p 1) * N (p 1)1) * (M (id 2)(p 2) * N (p 2)2)
        -- = 1 * (M 1 1 * N 1 1) * (M 2 1 * N 1 2)
        -- = + M 1 1*N 1 1 * M 2 1*N 1 2
        -- 第二个是
        -- ε swap * (M (swap 1)(p 1) * N (p 1)1) * (M (swap 2)(p 2) * N (p 2)2)
        -- = -1 * (M 2 1 * N 1 1) * (M 1 1 * N 1 2)
        -- = - M 2 1 * N 1 1 * M 1 1 * N 1 2
        -- 因为有重复的参数，所以交换后原来的项仍然可以找到。
        -- //
        -- p是双射，就不行吗？
        --  ↑↑(↑sign σ) * ∏ x : n, M (↑σ x) (p x) * N (p x) x
        -- -- 举个例子n=2，p不是双射，举例p=(1,2),Perm 2只有两个变换：
        --  M？(1)*N(1)[1] * M？(2)*N(2)[2]
        -- 1.恒等变换，简称id=σ=(1,2)；2.换位变换，简称swap=σ=(2,1)
        -- = M 1 1 * N 1 1 * M 2 2 * N 2 2
        -- 第二个是
        -- = -M 2 1 * N 1 1 * M 1 2 * N 2 2
        -- 因为没有了重复的参数，所以多个项经过变换后找不回来了。

        -- 再举例n=3的情况
        -- 非双射情况：p=(1,1,1)，非双射导致了重复，导致了“填坑自由度”变高了。
        --  ↑↑(↑sign σ) * ∏ x : n, M (↑σ x) (p x) * N (p x) x
        -- 固定求和式是： M？(1)*N(1)[1] * M？(1)*N(1)[2] * M？(1)*N(1)[3]
        -- σ=(1,2,3) (+1) * M1(1)*N(1)[1] * M2(1)*N(1)[2] * M3(1)*N(1)[3]
        -- 要找相反项：σ=(3,2,1) σ=(3,2,1)
                        -- M3(1)*N(1)[1] * M2(1)*N(1)[2] * M1(1)*N(1)[3]
        --           (-1) * M3(1)*N(1)[1] * M2(1)*N(1)[2] * M1(1)*N(1)[3]
        -- //
         -- 双射情况：p=(1,2,3)
        --  ↑↑(↑sign σ) * ∏ x : n, M (↑σ x) (p x) * N (p x) x
        -- 固定求和式是： M？(1)*N(1)[1] * M？(2)*N(2)[2] * M？(3)*N(3)[3]
        -- σ=(1,2,3) (+1) * M1(1)*N(1)[1] * M2(2)*N(2)[2] * M3(3)*N(3)[3]
        -- 要找相反项：σ=(,,) ， 要想项一致，只能填σ=(1,2,3)
        --           (-1) * M1(1)*N(1)[1] * M2(2)*N(2)[2] * M3(3)*N(3)[3]



      simp only [mem_filter] at h5 -- 就是filter的定义呗，是属于某个集合里面的，而且满足条件1
      simp only [mem_univ] at h5
      simp only [true_and_iff] at h5
      set h6 := fun x ↦ h3 x -- 写这个h6,h7是为了补充说明，其实这里h6就是和h3同一个映射，写法不一样而已
      -- have h7: h6=h3 --为了讲解而写的
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
    -- 反向推理
    refine' sum_bij _ _ _ _ _
    -- {s : Finset α} {t : Finset γ} {f : α → β} {g : γ → β}
    -- (i : ∀ a ∈ s, γ)
    -- (hi : ∀ a ha, i a ha ∈ t)
    -- (h : ∀ a ha, f a = g (i a ha))
    -- (i_inj : ∀ a₁ a₂ ha₁ ha₂, i a₁ ha₁ = i a₂ ha₂ → a₁ = a₂)
    -- (i_surj : ∀ b ∈ t, ∃ a ha, b = i a ha) :
    -- ∏ x in s, f x = ∏ x in t, g x
    -- 不一样的定义域s、t，不同的函数f、g，求和相同，需要什么条件呢。5个条件
    -- 举例：
    -- 假设我们有以下集合和映射：
    -- 令 α = {1, 2, 3}，即集合 {1, 2, 3}。 //s
    -- 令 β = {a, b, c}，即集合 {a, b, c}。 //
    -- 令 γ = {x, y, z}，即集合 {x, y, z}。 //t
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
    -- 即，
    -- [
    -- abc = abc
    -- ]
    · intros ih1 ih2 -- 这里ih1潜台词是随机的ih1
      -- 感性理解就是容易犯错，不想犯错还是得程序验证
      simp only [Perm]
      have ih3:= (mem_filter.mp ih2).right
      have ih4:= ofBijective ih1 ih3 -- 单射+满射的映射，向上升级概念为（或者叫自然拓展性质）：具有双边逆的映射（实质并没有发生任何变化）
      -- 提一句：通常名字为of的函数，就是讲一些等价的概念互相转换。
      exact ih4 -- 如果这里定义错了，下面满盘皆输
      -- 证明的一个哲学意义是：给出某一个例子，是属于这个命题说的类的。
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
      -- have h1_equal_h6 : h_1=h_6 --为了讲解
      --   := by
      --   exact rfl
      rfl
    · intros inj_1 inj_2 inj_3 inj_4 inj_5
      simp only [id_eq] at inj_5 -- 看起来很明显，但就是完成不了
      ext x
      have inj_6:= ofBijective_apply inj_1
      have inj_7:= ofBijective_apply inj_2
      rw [
      ← inj_6,
      inj_5,
      inj_7]
      done
    · intros b x
      refine' Exists.intro b _ -- 存在，给出例子，然后代入第二个参数中，比如这里就是把a全部替换成了b
      -- 如果第二个参数中不用直接替换的，比如下面这行，就直接证明第二个参数代表的命题即可
      refine' Exists.intro _ _ -- 比如这里ha在第二个参数中没有需要替换的，直接证明第二个命题即可
      · refine' mem_filter.2 _
        constructor
        · refine' mem_univ (↑b)
        · exact Equiv.bijective b
      · -- refine' coe_fn_injective _ --在外层套了一个不变的映射
        simp only [id_eq]
        -- simp only [FunLike.coe_fn_eq]
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


  lemma MainGoal_4 (M N : Matrix n n R):
  ∑ τ : Perm n,
    ∑ σ : Perm n,
      (ε σ)
      *
      (∏ i,
        M (σ i) (τ i) * N (τ i) i)
  = ∑ σ : Perm n,
      ∑ τ : Perm n,
        (∏ i,
           N (σ i) i)
        *
        (ε τ)
        * ∏ j, M (τ j) (σ j)
    := by
    simp only [mul_comm]
    simp only [mul_left_comm]
    simp only [prod_mul_distrib] --  1个连乘变成2个连乘相关的定理
    simp only [mul_assoc]
    done

-- ///

      def hhh3_h4 (M N : Matrix n n R) (h5: Perm n) (h1: Perm n)
      : --映射间组合的一个定理
      ∏ j,
         M (h5 j) (h1 j) =
      ∏ j,
        M ((h5 * h1⁻¹) j) j -- perm n之间的乘法是什么结果呢？还是perm n
        := by
        rw [← (h1⁻¹ : _ ≃ _).prod_comp] -- 两个函数的连乘的结果一样的相关证明（感性理解：置换后反正都要遍历的对吧，连乘应该都一样的哦）
        simp only [Equiv.Perm.coe_mul]
        simp only [apply_inv_self]
        simp only [Function.comp_apply]
        done

      def h6  (h5: Perm n) (h1: Perm n)
      : (ε h1) * (ε (h5 * h1⁻¹))  -- [1,2,3] => [3,1,2]
      = (ε h5) -- 转置的符号相关的定理
        :=
        calc
          (ε h1) * ε (h5 * h1⁻¹)
          = ε (h5 * h1⁻¹ * h1)
            := by
            rw [mul_comm, sign_mul (h5 * h1⁻¹)] --???sign_mul
            -- simp only [_root_.map_mul]
            simp only [sign_mul]
            simp only [map_inv]--???map_inv这个证明可以细讲
            simp only [Int.units_inv_eq_self] -- 1或-1的倒数还是自己
            simp only [Units.val_mul] --明明一看就知道相等的。。。
            simp only [Int.cast_mul]
          _ = ε h5
            := by
            simp only [inv_mul_cancel_right]

  lemma MainGoal_5 (M N : Matrix n n R):
  ∑ σ : Perm n,
    ∑ τ : Perm n,
      (∏ i, N (σ i) i)
      *
      (ε τ)
      *
      ∏ j, M (τ j) (σ j)
  =
  ∑ σ : Perm n,
    ∑ τ : Perm n,
      (∏ i, N (σ i) i)
      *
      (ε σ * ε τ)
      *
      ∏ i,
        M (τ i) i
    := by
    refine' sum_congr _ _ --定义域一样，定义域内f和g的映射值一样，则两个求和结果一样
    · rfl
    · intros h1 h2
      refine' Fintype.sum_equiv _ _ _ _ --两个不同函数求和的结果一样的相关证明
      · exact Equiv.mulRight h1⁻¹ -- 将映射1变成映射2的一个映射，具体作用是右乘，这是一步需要后面依赖的证明，所以不能随意证明，通常都是第一步这样
      -- [1,2,3] h1=> [3,2,1] h1⁻¹=> [1,2,3]
      -- [1,2,3] h10=> [2,3,1] => [2,1,3]
      -- h10 * h1⁻¹ (Perm n)
      -- (? * h1⁻¹)
      · intros h5 --其实infoview里面的 ?1:?2 这样的写法，?1就是一个随机的属于?2的对象或元素
        simp_rw [Equiv.coe_mulRight]
        simp_rw [(h6 h5 h1)]
        simp only [(hhh3_h4 M N h5 h1)]
    done



        def MainGoal_6_1_1_1 (M: Matrix n n R)
          := (det_apply' M)

        def MainGoal_6_1_1_2 (M: Matrix n n R):
        ∑ x : Perm n, (ε x) * ∏ x_1 : n, M (x x_1) x_1
        = ∑ x : Perm n, (∏ x_1 : n, M (x x_1) x_1) * (ε x) -- 这明明就是一个交换律能完成的，偏要congr一下拆开。。。
          := by
          refine' sum_congr _ _
          · exact (Eq.refl univ)
          · intros h212x h212a
            have h2_1_2_1
              : (ε h212x) * ∏ x_1 : n, M (h212x x_1) x_1 = (ε h212x) * ∏ x_1 : n, M (h212x x_1) x_1
              := by
              exact rfl --竟然直接搞定了
            have h2_1_2_2 := mul_comm (ε h212x) (∏ x_1 : n, M (h212x x_1) x_1)
            have h2_1_2_3 := h2_1_2_1.trans h2_1_2_2
            exact h2_1_2_3

      def MainGoal_6_1_1 (M N : Matrix n n R):
      det M = ∑ x : Perm n, (∏ x_1 : n, M (x x_1) x_1) * (ε x)
        := by
        exact (MainGoal_6_1_1_1 M).trans (MainGoal_6_1_1_2 M) -- .trans就是等号传递

        def h2_2_1(N : Matrix n n R):= det_apply' N

        def h2_2_2(N : Matrix n n R):  ∑ x : Perm n, (ε x) * ∏ x_1 : n, N (x x_1) x_1
        = ∑ x : Perm n, (∏ x_1 : n, N (x x_1) x_1) * (ε x) -- 又是一个内部交换就好了
            := by
            refine' sum_congr _ _
            · exact Eq.refl univ
            · intros h222x h222a
              have h2_2_2_1 : (ε h222x) * ∏ x_1 : n, N (h222x x_1) x_1 = (ε h222x) * ∏ x_1 : n, N (h222x x_1) x_1
                := by
                rfl
              have h2_2_2_2:= (mul_comm ((ε h222x)) (∏ x_1 : n, N (h222x x_1) x_1))
              have h2_2_2_3:= h2_2_2_1.trans h2_2_2_2
              exact h2_2_2_3

      def MainGoal_6_1_2 (N : Matrix n n R): det N = ∑ x : Perm n, (∏ x_1 : n, N (x x_1) x_1) * (ε x)
        := by
        exact (h2_2_1 N).trans (h2_2_2 N)

    lemma MainGoal_6_1 (M N : Matrix n n R):
    det M * det N
    = ∑ x : Perm n,
        (∑ x : Perm n, (∏ x_1 : n, M (x x_1) x_1) * (ε x))
        *
        ((∏ x_1 : n, N (x x_1) x_1) * (ε x))
      := by
      have temp1:= (MainGoal_6_1_1 M N)
      have temp2:= (MainGoal_6_1_2 N)
      have h1 := congr (congrArg HMul.hMul temp1) (temp2) -- congr就是相同函数，相同参数，结果一样的意思；congrArg也是类似的意思
      rw [h1]
      exact mul_sum
      -- exact h1.trans mul_sum
    --

      def h3_3 (M N : Matrix n n R) (h3_1: Perm n) (h3_2: h3_1 ∈ univ)
      : (∑ x : Perm n,
          (∏ x_1 : n, M (x x_1) x_1)
          *
          (ε x)
        )
        *
        (
          (∏ x_1 : n, N (h3_1 x_1) x_1)
        *
          (ε h3_1)
        )
      = ∑ x : Perm n,
          (∏ x_1 : n, N (h3_1 x_1) x_1)
          *
          (ε h3_1)
          *
          (
            (∏ x_1 : n, M (x x_1) x_1)
          *
            (ε x)
          )

        := by
        have h3_3_1 :
        (∑ x : Perm n,
          (∏ x_1 : n, M (x x_1) x_1)
          *
          (ε x)
        )
        *
        (
          (∏ x_1 : n, N (h3_1 x_1) x_1)
          *
          (ε h3_1)
        )
        =
        (∏ x_1 : n, N (h3_1 x_1) x_1)
        *
        (ε h3_1)
        *
        ∑ x : Perm n,
          (∏ x_1 : n, M (x x_1) x_1)
          *
          (ε x)
        := by
          have h3_3_1_1 := mul_comm
            (∑ x : Perm n, (∏ x_1 : n, M (x x_1) x_1) * (ε x))
            ((∏ x_1 : n, N (h3_1 x_1) x_1) * (ε h3_1))
          exact h3_3_1_1
        have h3_3_2:= h3_3_1.trans mul_sum
        exact h3_3_2

      def h3_4 (M N : Matrix n n R) (h3_1: Perm n) (h3_2: h3_1 ∈ univ)
      :
      ∑ x_1 : Perm n,
        (∏ x_2 : n, N (h3_1 x_2) x_2)
        *
        (ε h3_1)
        *
        (
          (∏ x : n, M (x_1 x) x)
        *
          (ε x_1)
        )
      =
      ∑ x_1 : Perm n,
        (∏ x_2 : n, N (h3_1 x_2) x_2)
        *
        (
          (∏ x : n, M (x_1 x) x)
        *
          ((ε h3_1) * (ε x_1))
        ) -- 又是交换就可以了。。。
        := by
        refine' sum_congr _ _
        · exact (Eq.refl univ)
        · intros h34x_1 h34a
          have h3_4_1 : (∏ x_2 : n, N (h3_1 x_2) x_2) * (ε h3_1) * ((∏ x : n, M (h34x_1 x) x) * (ε h34x_1))
          = (∏ x : n, M (h34x_1 x) x) * ((∏ x_2 : n, N (h3_1 x_2) x_2) * ((ε h3_1) * (ε h34x_1)))
            := ((mul_left_comm ((∏ x_2 : n, N (h3_1 x_2) x_2) * (ε h3_1)) (∏ x : n, M (h34x_1 x) x)
                      (ε h34x_1)).trans
                  (congrArg (HMul.hMul (∏ x : n, M (h34x_1 x) x))
                    (mul_assoc (∏ x_2 : n, N (h3_1 x_2) x_2) (ε h3_1) (ε h34x_1))))
          have h3_4_2 :  (∏ x : n, M (h34x_1 x) x) * ((∏ x_2 : n, N (h3_1 x_2) x_2) * ((ε h3_1) * (ε h34x_1)))
          =(∏ x_2 : n, N (h3_1 x_2) x_2) * ((∏ x : n, M (h34x_1 x) x) * ((ε h3_1) * (ε h34x_1)))
            := (mul_left_comm (∏ x : n, M (h34x_1 x) x) (∏ x_2 : n, N (h3_1 x_2) x_2)
                ((ε h3_1) * (ε h34x_1)))
          have h3_4_3:= h3_4_1.trans h3_4_2
          exact h3_4_3

    lemma MainGoal_6_2 (M N : Matrix n n R)
    :
    ∑ x : Perm n,
      (∑ x : Perm n,
        (∏ x_1 : n, M (x x_1) x_1)
        *
        (ε x)
      )
    *
    (
      (∏ x_1 : n, N (x x_1) x_1)
    *
      (ε x)
    )
    =
    ∑ x : Perm n,
      ∑ x_1 : Perm n,
        (∏ x_2 : n, N (x x_2) x_2)
        *
        (
          (∏ x : n,M (x_1 x) x)
        *
          ((ε x) * (ε x_1))
        )
      := by
      have h2 := MainGoal_6_1 M N
      refine' sum_congr _ _
      · exact (Eq.refl univ)
      · intros h3_1 h3_2
        have h3_5:= (h3_3 M N h3_1 h3_2).trans (h3_4 M N h3_1 h3_2)
        exact h3_5


    def MainGoal_6_3 (M N : Matrix n n R):= (MainGoal_6_1 M N).trans (MainGoal_6_2 M N)

  lemma MainGoal_6 (M N : Matrix n n R):
  ∑ σ : Perm n,
    ∑ τ : Perm n,
      (∏ i, N (σ i) i)
      *
      (ε σ * ε τ)
      *
      (∏ i, M (τ i) i)
  = det M * det N
    := by
    have h4:= MainGoal_6_3 M N
    simp only [h4]
    congr -- 去掉两边套在最外的，恰好是相同的函数
    funext xx1
    congr
    funext xx2
    rw [mul_right_comm]
    repeat rw [← mul_assoc]
    done




   -- @[simp]
  theorem MainGoal (M N : Matrix n n R)
  : det (M * N) = det M * det N
  := by
    have h1 :det (M * N) = det M * det N :=
      calc
          det (M * N)
          = ∑ p : n → n, ∑ σ : Perm n, ε σ * ∏ i, M (σ i) (p i) * N (p i) i --第1个变式
            := by
            exact MainGoal_1 M N
          _ = ∑ p in (@univ (n → n) _).filter Bijective,--第2个变式
                ∑ σ : Perm n,
                  ε σ
                  *
                  (∏ i, M (σ i) (p i) * N (p i) i)
            := by
            exact MainGoal_2 M N
          _ = ∑ τ : Perm n, --第3个变式
                ∑ σ : Perm n,
                  (ε σ)
                  *
                  (∏ i,
                    M (σ i) (τ i) * N (τ i) i)
            := by
            exact MainGoal_3 M N
          _ = ∑ σ : Perm n,--第4个变式
                ∑ τ : Perm n,
                  (∏ i, N (σ i) i)
                  *
                  ε τ
                  *
                  ∏ j, M (τ j) (σ j)
            := by
            exact MainGoal_4 M N
          _ = ∑ σ : Perm n, --第5个变式
                ∑ τ : Perm n,
                  (∏ i, N (σ i) i)
                  *
                  (ε σ * ε τ)
                  *
                  ∏ i,
                    M (τ i) i
            := by
            exact MainGoal_5 M N
          _ = det M * det N --第6个变式
            := by
            -- simp only [det_apply', Finset.mul_sum, mul_comm, mul_left_comm, mul_assoc] --这里无法分步，所以直接分析print来写成下面这样子：
            exact MainGoal_6 M N
    exact h1
    done



end Matrix
