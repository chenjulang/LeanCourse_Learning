import Mathlib.LinearAlgebra.Matrix.Determinant
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.GroupTheory.Perm.Sign
import Mathlib.Data.Real.Sqrt
import Mathlib.Data.List.Perm


-- set_option trace.Meta.synthInstance true
-- set_option maxHeartbeats 400000 -- 原来要很多时间的


universe u v w z

open Equiv Equiv.Perm Finset Function

namespace Matrix --目的是避免模糊定义mul_apply

  open Matrix BigOperators

  variable {m n : Type*} [DecidableEq n] [Fintype n] [DecidableEq m] [Fintype m]
  variable {R : Type v} [CommRing R]

  local notation "ε " σ:arg => ((sign σ : ℤ) : R)
set_option linter.unusedVariables false

-- -- -----/行列式

-- -- 原来有toFun的结构，直接写名词的话，它要用toFun来替换，
-- -- 所以detRowAlternating2具体类型应该是和这个相同(↑detRowAlternating2).toFun : (?m.32939 → ?m.32939 → ?m.32941) → ?m.32941
-- -- 因此detRowAlternating2 M的类型就是R
--   def detRowAlternating2
--   : AlternatingMap R (n → R) R n  --- 最后这个参数n属于补充说明,实际形式上只需传三个参数即可
--   :=
--   -- have h1:= (
--   --   (MultilinearMap.mkPiAlgebra R n R).compLinearMap
--   --     LinearMap.proj
--   -- )
--   -- have h1fun:= h1.toFun
--   MultilinearMap.alternatization ( -- ???
--     (MultilinearMap.mkPiAlgebra R n R).compLinearMap
--       LinearMap.proj
--   )

-- -- 问题：v是什么？
-- -- MultilinearMap R (fun x（x就是n） ↦ n → R) R 也就是(n → n → R) → R
--   abbrev det2 (M : Matrix n n R): R :=
--     -- have h1 := detRowAlternating2 M
--     detRowAlternating2 M -- 这里为什么类型是R，因为detRowAlternating2相当于detRowAlternating2.toFun
--     -- 也就是(?m.33147 → ?m.33147 → ?m.33149) → ?m.33149
--   -- #check detRowAlternating2.toFun -- 所以上面M不是参数，而是被作用了，detRowAlternating2是一个映射作用到M上了


--   --  前置知识

--   -- Perm 的使用
--   -- 以下是一些关于 Perm n 的示例，其中 n 取不同的值：
--   -- 当 n = 1 时，Perm 1 表示长度为 1 的置换，即 [0]。
--   -- 当 n = 2 时，Perm 2 表示长度为 2 的置换，共有两种情况：[0, 1] 和 [1, 0]。
--   -- 当 n = 3 时，Perm 3 表示长度为 3 的置换，共有六种情况：[0, 1, 2]、[0, 2, 1]、[1, 0, 2]、[1, 2, 0]、[2, 0, 1] 和 [2, 1, 0]。
-- -- #eval Finset.val (Finset.univ : Finset (Fin 4))
-- def printPerms (n : ℕ) : List (List ℕ) :=
--   List.map List.reverse (List.permutations (List.range n))
-- #eval printPerms 4



  -- 正式开始：

  -- def example_function : n → n :=
  -- λ x => x
  -- @[nolint unusedArguments]
  -- set_option linter.unusedVariables false in
  lemma hhh1 (M N : Matrix n n R) :
      ∑ p : n → n,
        ∑ σ : Perm n,
          ε σ
          *
          ∏ i,
            M (σ i) (p i) * N (p i) i
      =
      ∑ p in (@univ (n → n) _).filter Bijective, -- (@univ (n → n) _) 表示一个集合，包含了 n 到 n 函数类型的所有可能的函数
        ∑ σ : Perm n,
          ε σ
          *
          ∏ i,
             M (σ i) (p i) * N (p i) i
      := by
      apply Eq.symm
      apply sum_subset --s₁ ⊆ s₂， x ∈ s₂, x ∉ s₁的情况为0，则可以直接去掉
      · intro h1 h2
        exact mem_univ h1
      intros h3 h4 h5
      apply det_mul_aux -- ???这个先不理解，后面专门出一个视频来教如何读证明并且分解证明成策略模式。一个先连乘，再连加的东西，结果是0，关键是非双射导致的，有点意思
      simp only [mem_filter] at h5 -- 就是filter的定义呗，是属于某个集合里面的，而且满足条件1
      simp only [mem_univ] at h5
      simp only [true_and_iff] at h5
      set h6 := fun x ↦ h3 x -- 写这个h6,h7是为了补充说明，其实这里h6就是和h3同一个映射，写法不一样而已
      have h7: h6=h3
      := by
        exact rfl
      exact h5

  lemma hhh2 (M N : Matrix n n R) :
  ∑
    p in (@univ (n → n) _).filter Bijective,
      ∑
        σ : Perm n,
          (
            ε σ
            *
            ∏ i, M (σ i) (p i) * N (p i) i
          )
      = ∑ τ : Perm n,
          ∑ σ : Perm n,
              ε σ
              *
              ∏ i,
                M (σ i) (τ i) * N (τ i) i
      := by
      rw [sum_comm]
      rw [sum_comm] -- 这两步sum_comm相当于没变，只改成了x,y
      refine' sum_bij _ _ _ _ _ -- ???这个需要问一下gpt找到数学世界里的对应定理名称。不一样的定义域s、t，不同的函数f、g，求和相同，需要什么条件呢。5个条件
      · intros ih1 ih2 -- 这里ih1潜台词是随机的ih1
        have ih3:= (mem_filter.mp ih2).right
        have ih4:= ofBijective ih1 ih3
        simp only [Perm]
        exact ih4 -- 如果这里定义错了，下面满盘皆输
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
        have h1_equal_h6 : h_1=h_6
          := by
          exact rfl
        rfl
      · intros inj_1 inj_2 inj_3 inj_4 inj_5
        refine' Equiv.noConfusion inj_5 _ ---??? 不知道对inj_5做了什么
        intros inj_6 inj_7
        exact inj_6
        done
      · intros b x
        refine' Exists.intro b _ -- 存在，给出例子，然后代入第二个参数中，比如这里就是把a全部替换成了b
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

--

    def hhh3_h4 (M N : Matrix n n R) (h5: Perm n) (h1: Perm n)
    : (∏ j, M (h5 j) (h1 j)) = ∏ j, M ((h5 * h1⁻¹) j) j -- perm n之间的乘法是什么结果呢？还是perm n
      := by
      rw [← (h1⁻¹ : _ ≃ _).prod_comp] -- 两个函数的连乘的结果一样的相关证明（感性理解：置换后反正都要遍历的对吧，连乘应该都一样的哦）
      simp only [Equiv.Perm.coe_mul]
      simp only [apply_inv_self]
      simp only [Function.comp_apply]

    def h6  (h5: Perm n) (h1: Perm n)
    : ε h1 * ε (h5 * h1⁻¹) = ε h5 -- 转置的符号相关的定理
      :=
      calc
        ε h1 * ε (h5 * h1⁻¹) = ε (h5 * h1⁻¹ * h1)
          := by
          rw [mul_comm, sign_mul (h5 * h1⁻¹)]
          simp only [_root_.map_mul]
          simp only [map_inv]
          simp only [Int.units_inv_eq_self] -- 1或-1的倒数还是自己
          simp only [Units.val_mul] --明明一看就知道相等的。。。
          simp only [Int.cast_mul]
        _ = ε h5
          := by
          simp only [inv_mul_cancel_right]

  lemma hhh3 (M N : Matrix n n R) : ∑ σ : Perm n, ∑ τ : Perm n, (∏ i, N (σ i) i) * ε τ * (∏ j, M (τ j) (σ j))
      = ∑ σ : Perm n, ∑ τ : Perm n, (∏ i, N (σ i) i) * (ε σ * ε τ) * (∏ i, M (τ i) i)
      := by
      refine' sum_congr _ _ --定义域一样，定义域内f和g的映射值一样，则两个求和结果一样
      · rfl
      · intros h1 h2
        refine' Fintype.sum_equiv _ _ _ _ --两个不同函数求和的结果一样的相关证明
        · exact Equiv.mulRight h1⁻¹ -- 这是一步需要后面依赖的证明，所以不能随意证明，通常都是第一步这样
        · intros h5 --其实infoview里面的 ?1:?2 这样的写法，?1就是一个随机的属于?2的对象或元素
          simp_rw [Equiv.coe_mulRight]
          simp_rw [(h6 h5 h1)]
          simp only [(hhh3_h4 M N h5 h1)]
      done


  lemma MainGoal_1 (M N : Matrix n n R): det (M * N)
  = ∑ p : n → n, ∑ σ : Perm n, ε σ * ∏ i, M (σ i) (p i) * N (p i) i
    := by
    simp only [det_apply']
    simp only [mul_apply]
    simp only [prod_univ_sum] -- 与"先连加，再连乘，等于，先连乘，再连加"相关的定理
    -- ???Fintype.piFinset是什么东西
    simp only [mul_sum]
    simp only [Fintype.piFinset_univ]
    rw [Finset.sum_comm]
    done

  lemma MainGoal_2 (M N : Matrix n n R): ∑ p : n → n, ∑ σ : Perm n, ε σ * ∏ i, M (σ i) (p i) * N (p i) i
  = ∑ p in (@univ (n → n) _).filter Bijective,∑ σ: Perm n, ε σ * (∏ i, M (σ i) (p i) * N (p i) i)
    := by
    exact (hhh1 M N)

  lemma MainGoal_3 (M N : Matrix n n R): ∑ p in (@univ (n → n) _).filter Bijective,∑ σ: Perm n, ε σ * (∏ i, M (σ i) (p i) * N (p i) i)
  = ∑ τ : Perm n,∑ σ : Perm n, (ε σ) * (∏ i, M (σ i) (τ i) * N (τ i) i)
    := by
    exact (hhh2 M N)

  lemma MainGoal_4 (M N : Matrix n n R): ∑ τ : Perm n,∑ σ : Perm n, (ε σ) * (∏ i, M (σ i) (τ i) * N (τ i) i)
  = ∑ σ : Perm n, ∑ τ : Perm n, (∏ i, N (σ i) i) * (ε τ) * ∏ j, M (τ j) (σ j)
    := by
    simp only [mul_comm]
    simp only [mul_left_comm]
    simp only [prod_mul_distrib] --  1个连乘变成2个连乘相关的定理
    simp only [mul_assoc]
    done

  lemma MainGoal_5 (M N : Matrix n n R): ∑ σ : Perm n, ∑ τ : Perm n, (∏ i, N (σ i) i) * (ε τ) * ∏ j, M (τ j) (σ j)
  = ∑ σ : Perm n, ∑ τ : Perm n, (∏ i, N (σ i) i) * (ε σ * ε τ) * ∏ i, M (τ i) i
    := by
    exact (hhh3 M N)

  -- /////////////////////////////////////////////////////////////////////////////////////////////////////

      def MainGoal_6_1_1_1 (M: Matrix n n R)
        := (det_apply' M)

      def MainGoal_6_1_1_2 (M: Matrix n n R): ∑ x : Perm n, (ε x) * ∏ x_1 : n, M (x x_1) x_1
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

      def MainGoal_6_1_1_3 (M N: Matrix n n R):= (MainGoal_6_1_1_1 M).trans (MainGoal_6_1_1_2 M) -- .trans就是等号传递


    def MainGoal_6_1_1 (M N : Matrix n n R): det M = ∑ x : Perm n, (∏ x_1 : n, M (x x_1) x_1) * (ε x)
      := by exact (MainGoal_6_1_1_3 M N)


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

    def h2_2_3(N : Matrix n n R):= (h2_2_1 N).trans (h2_2_2 N)

    def MainGoal_6_1_2 (N : Matrix n n R): det N = ∑ x : Perm n, (∏ x_1 : n, N (x x_1) x_1) * (ε x)
      := by exact (h2_2_3 N)


  lemma MainGoal_6_1 (M N : Matrix n n R): det M * det N
  = ∑ x : Perm n, (∑ x : Perm n, (∏ x_1 : n, M (x x_1) x_1) * (ε x)) * ((∏ x_1 : n, N (x x_1) x_1) * (ε x))
    := by
    have temp1:= (MainGoal_6_1_1 M N)
    have temp2:= (MainGoal_6_1_2 N)
    have h1 := congr (congrArg HMul.hMul temp1) (temp2) -- congr就是相同函数，相同参数，结果一样的意思；congrArg也是类似的意思
    exact h1.trans mul_sum


  --

    def h3_3 (M N : Matrix n n R) (h3_1: Perm n) (h3_2: h3_1 ∈ univ)
    : (∑ x : Perm n, (∏ x_1 : n, M (x x_1) x_1) * (ε x)) * ((∏ x_1 : n, N (h3_1 x_1) x_1) * (ε h3_1))
    = ∑ x : Perm n, (∏ x_1 : n, N (h3_1 x_1) x_1) * (ε h3_1) * ((∏ x_1 : n, M (x x_1) x_1) * (ε x)) -- 又是一个内部交换的东西，太简单了吧。。。
      := by
      have h3_3_1 : (∑ x : Perm n, (∏ x_1 : n, M (x x_1) x_1) * (ε x)) * ((∏ x_1 : n, N (h3_1 x_1) x_1) * (ε h3_1))
      = (∏ x_1 : n, N (h3_1 x_1) x_1) * (ε h3_1) * ∑ x : Perm n, (∏ x_1 : n, M (x x_1) x_1) * (ε x)
      := by
        have h3_3_1_1 := mul_comm (∑ x : Perm n, (∏ x_1 : n, M (x x_1) x_1) * (ε x)) ((∏ x_1 : n, N (h3_1 x_1) x_1) * (ε h3_1))
        exact h3_3_1_1
      have h3_3_2:= h3_3_1.trans mul_sum
      exact h3_3_2


    def h3_4 (M N : Matrix n n R) (h3_1: Perm n) (h3_2: h3_1 ∈ univ)
    : ∑ x_1 : Perm n, (∏ x_2 : n, N (h3_1 x_2) x_2) * (ε h3_1) * ((∏ x : n, M (x_1 x) x) * (ε x_1))
    = ∑ x_1 : Perm n, (∏ x_2 : n, N (h3_1 x_2) x_2) * ((∏ x : n, M (x_1 x) x) * ((ε h3_1) * (ε x_1))) -- 又是交换就可以了。。。
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
  : ∑ x : Perm n,
  (∑ x : Perm n, (∏ x_1 : n, M (x x_1) x_1) * (ε x))
  *
  ((∏ x_1 : n, N (x x_1) x_1) * (ε x))
  = ∑ x : Perm n, ∑ x_1 : Perm n,
  (∏ x_2 : n, N (x x_2) x_2)
  *
  ((∏ x : n, M (x_1 x) x) * ((ε x) * (ε x_1)))
    := by
    have h2 := MainGoal_6_1 M N
    refine' sum_congr _ _
    · exact (Eq.refl univ)
    · intros h3_1 h3_2
      have h3_5:= (h3_3 M N h3_1 h3_2).trans (h3_4 M N h3_1 h3_2)
      exact h3_5

  --

  def MainGoal_6_3 (M N : Matrix n n R):= (MainGoal_6_1 M N).trans (MainGoal_6_2 M N)


  lemma MainGoal_6 (M N : Matrix n n R):
  ∑ σ : Perm n,
    ∑ τ : Perm n,
      (∏ i, N (σ i) i)
      *
      (ε σ * ε τ)
      *
      (∏ i, M (τ i) i)
  = det M * det N --todo
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
          = ∑ p : n → n, ∑ σ : Perm n, ε σ * ∏ i, M (σ i) (p i) * N (p i) i
            := by
            exact MainGoal_1 M N
          _ = ∑ p
                in (@univ (n → n) _).filter Bijective,
                  ∑ σ
                    : Perm n,
                      ε σ
                      *
                      (∏ i, M (σ i) (p i) * N (p i) i)
            := by
            exact MainGoal_2 M N
          _ = ∑ τ : Perm n,∑ σ : Perm n, (ε σ) * (∏ i, M (σ i) (τ i) * N (τ i) i)
            := by
            exact MainGoal_3 M N
          _ = ∑ σ
                : Perm n,
                  ∑ τ
                    : Perm n,
                      (∏ i, N (σ i) i)
                      *
                      ε τ
                      *
                      ∏ j, M (τ j) (σ j)
            := by
            exact MainGoal_4 M N
          _ = ∑ σ : Perm n, ∑ τ : Perm n, (∏ i, N (σ i) i) * (ε σ * ε τ) * ∏ i, M (τ i) i
            := by
            exact MainGoal_5 M N
          _ = det M * det N
            := by
            -- simp only [det_apply', Finset.mul_sum, mul_comm, mul_left_comm, mul_assoc] --这里无法分步，所以直接分析print来写成下面这样子：
            exact MainGoal_6 M N
    exact h1
    done


end Matrix
