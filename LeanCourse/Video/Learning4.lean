import Mathlib.LinearAlgebra.LinearIndependent
import Mathlib.LinearAlgebra.Matrix.Basis
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.Data.Real.Sqrt
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.GroupTheory.Perm.Sign


-- 线性独立
noncomputable section

  open Function Set Submodule Matrix
  open Equiv Equiv.Perm Finset Function

  open BigOperators Cardinal

  universe u' u

  variable {ι : Type u'} {ι' : Type*} {R : Type*} {K : Type*}
  variable {M : Type*} {M' M'' : Type*} {V : Type u} {V' : Type*}

  section Module

    variable {v : ι → M}

    variable [Semiring R] [AddCommMonoid M] [AddCommMonoid M'] [AddCommMonoid M'']
    variable [Module R M] [Module R M'] [Module R M'']
    variable {a b : R} {x y : M}
    variable (R) (v)

    -- 线性独立的定义，后面还有定义linearIndependent_iff2'，是比较符合传统数学上的理解的。
    -- 1.LinearMap.ker 2.Finsupp.total 3.⊥
    -- 零空间（Zero Space）： 在线性代数中，给定一个线性映射（如矩阵），其零空间是所有映射到零向量的输入组成的集合。零空间也被称为核（kernel）。
    -- 零子空间（zero subspace）：是向量空间中的一个特殊子空间。它单独由零向量（所有分量都为零的向量）构成。
    -- LinearMap.ker：
      --   def ker (f : F) : Submodule R M :=
      -- comap f ⊥
      -- comap f ⊥ ：的含义是将零子空间通过逆映射 f 映射回原始的定义域。
      -- 最终，ker (f : F) 返回的是线性映射 f 的核，即所有映射到零向量的输入的集合。
      -- Submodule R M：环 R 上的模 M 的子模组成的集合类型
    def LinearIndependent2 : Prop :=
      LinearMap.ker (Finsupp.total ι M R v) = ⊥ -- 在线性代数中，⊥ 经常用于表示零空间或零子空间。
    -- 举例说明
    -- 已知2个条件：
    -- 已知任意的一维向量d，即(x,y),举例（7，8）
    -- 已知一个映射v，将（1，0）=>(2,3),将（0，1）=> (4,5)

    -- 推理：

    -- Finsupp.total ι M R v具体结果就是：fun d => d.sum fun i => F i
    -- d.sum (fun i => F i) 具体做的是：
    -- 展开d.sum: ∑ a in d.support, g a (d a)
    -- 展开g，g就是(fun i => F i)：∑ a in d.support, (fun i => F i) a (d a)
    -- a是什么，先看d.support是指d中有非零元素的索引位置的集合，即{1,2},因为(7，8)的第1，2位都是非零数
    -- 所以展开a就是
    -- (fun i => F i) 1 (d 1) +
    -- (fun i => F i) 2 (d 2)
    -- 代入(fun i => F i）得到,并且代入变量d：(F 1) (7) + (F 2) (8)
    -- F是什么呢？是LinearMap.id.smulRight (v i)
    -- LinearMap.id.smulRight (v 1) (7) + LinearMap.id.smulRight (v 2) (8)
    -- 这里不代入比较好，变回由已知条件变量d，映射v来表示：
    -- LinearMap.id.smulRight (v 1) (d 1) + LinearMap.id.smulRight (v 2) (d 2)
    -- 即(v 1)•(d 1) + (v 2)•(d 2)
    -- 这就是(Finsupp.total ι M R v)映射具体代表的，它将任意的向量d，变成了向量(v 1)•(d 1) + (v 2)•(d 2)
    -- 因此LinearMap.ker (Finsupp.total ι M R v)指的是由上述映射，从像为零向量，反向映射回去后，得到的所有向量，只有零向量一个。
    -- 则ι M R v共同形成一个关系：线性无关
    -- v : ι → M 指的是一个映射，根据这里举的例子，将（1，0）=>(2,3),将（0，1）=> (4,5)，
      -- ι就是第一个向量空间（一维2项向量组成的集合），M指的是第二个向量空间（一维2项向量组成的集合）
    -- R应该指的是数乘取的元素的集合，比如我们举例就是R实数


    theorem linearIndependent2_iff
    : LinearIndependent2 R v
    ↔
    ∀ l, Finsupp.total ι M R v l = 0 → l = 0
      := by
      simp only [LinearIndependent2]
      simp only [LinearMap.ker_eq_bot']
      done

-- //

        theorem linearIndependent2_iff'_1:
        (∀ (l : ι →₀ R), (Finsupp.total ι M R v) l = 0 → l = 0)
        ↔
        ∀ (s : Finset ι) (g : ι → R),
          ∑ i in s, g i • v i = 0
          →
          ∀ i ∈ s, g i = 0
          := by
          constructor
          · intros hf s g hg i his
            have h : (∑ i in s, fun₀ | i => g i) = 0
              := by
              refine' hf _ _
              simp only [map_sum]
              simp only [Finsupp.total_single] --???
              exact hg
            calc
              g i
              = (Finsupp.lapply i : (ι →₀ R) →ₗ[R] R) (Finsupp.single i (g i)) --???
                := by
                rw [Finsupp.lapply_apply, Finsupp.single_eq_same]
              _ = ∑ j in s, (Finsupp.lapply i : (ι →₀ R) →ₗ[R] R) (Finsupp.single j (g j)) --???
                := by
                refine' Eq.symm _
                refine' Finset.sum_eq_single i _ _
                · intros j _hjs hji
                  rw [Finsupp.lapply_apply, Finsupp.single_eq_of_ne hji]
                · exact (fun hnis => hnis.elim his)
                done
              _ = (∑ j in s, Finsupp.single j (g j)) i
                := by
                simp only [Finsupp.lapply_apply, ne_eq]
                exact (Finset.sum_apply' i).symm
                -- exact (map_sum ..).symm --???
              _ = 0
                := by
                have h2:= FunLike.ext_iff.1 h i
                exact h2
            done
          · intros hf l hl --???
            refine' Finsupp.ext _
            intros i
            refine' _root_.by_contradiction _
            intros hni
            have h3:= Finsupp.mem_support_iff.2 hni
            refine' hni _
            refine' hf _ _ hl _ h3
            done
          done


    theorem linearIndependent2_iff' :
      LinearIndependent2 R v
      ↔
      ∀ s : Finset ι,
         ∀ g : ι → R,
            ∑ i in s, g i • v i = 0 -- g i应该就是系数，v i是第i个向量
            →
            ∀ i ∈ s, g i = 0 -- 推出每一个系数都是0
        := by
        have h1 := linearIndependent2_iff'_1 R v
        exact (linearIndependent_iff).trans (h1)

-- //

        theorem linearIndependent2_iff''_1
        : (∀ (s : Finset ι) (g : ι → R), ∑ i in s, g i • v i = 0 → ∀ i ∈ s, g i = 0)
        ↔
        ∀ (s : Finset ι) (g : ι → R),
          (∀ i ∉ s, g i = 0)
          →
          ∑ i in s, g i • v i = 0 → ∀ (i : ι), g i = 0
          := by
          classical -- 可以使用局部变量，比如下面的这个his
          constructor
          · intros H s g hg hv i
            have h1 := (if his : i ∈ s then H s g hv i his else hg i his) --???
            exact h1
            done
          · intros H s g hg i hi
            have h2 :(if i ∈ s then g i else 0) = 0
            := H
              s
              (fun j => if j ∈ s then g j else 0)
              (fun j hj => if_neg hj)
              (by simp_rw [ite_smul, zero_smul, Finset.sum_extend_by_zero, hg]) i
            rw [← h2] -- convert h2 --一个意思
            exact (if_pos hi).symm
            done
          done

    theorem linearIndependent2_iff'' :
      LinearIndependent R v
      ↔
      ∀ (s : Finset ι)
      (g : ι → R)
      (_hg : ∀ (i) (_ : i ∉ s), g i = 0),
        ∑ i in s, g i • v i = 0
        →
        ∀ i, g i = 0
        := by
        have h2 := (linearIndependent2_iff''_1 R v)
        exact linearIndependent_iff'.trans h2
        done



      -- 最终目标：已知A是m*n矩阵，
      -- 对于任意m维向量b，
      -- 线性方程组AX=b至多只有一个解，
      -- =>用lean代码证明：A的各列向量线性无关

      -- 最终目标：已知A是m*n矩阵，对于任意m维向量b，线性方程组AX=b至多只有一个解，用lean代码证明：A的各列向量线性无关

      -- 命题还没有写出来。最后A的各列向量线性无关应该怎么写呢？？用哪个定义比较好？
      variable {m n : Type*} [Fintype m] [Fintype n]

      -- theorem MainGoal4  {R : Type*} [CommRing R]
      -- {A : Matrix m n R}
      -- {x : Matrix n (Fin 1) R}
      -- {b : Matrix m (Fin 1) R}
      -- (hA : ∀ (b : Matrix m (Fin 1) R), ∃! (x: Matrix n (Fin 1) R), A * x = b)
      -- : LinearIndependent R (fun i ↦ Aᵀ i)
      --   := by
      --   rw [LinearIndependent]
      --   refine' _root_.by_contradiction _
      --   intro oppo
      --   let b1 : Matrix m (Fin 1) R := 0
      --   have h2 : ∃! (x: Matrix n (Fin 1) R), A * x = 0
      --     := by exact hA 0
      --   have h3 : A * (0: Matrix n (Fin 1) R) = 0
      --     := by exact Matrix.mul_zero A
      --   --todo
      --   -- refine' Matrix.mulVec_injective_iff.1 _
      --   sorry

      -- theorem MainGoal4 {R : Type*} [CommRing R] {A : Matrix m n R} -- 一个大神的证明
      -- (hA : ∀ b : m → R, ∃! (x: n → R), A.mulVec x = b) :
      -- LinearIndependent R (fun i ↦ A.transpose i)
      --   := by
      --   rw [LinearIndependent]
      --   refine' _root_.by_contradiction _
      --   intro oppo
      --   let b1 : m → R := 0
      --   have h2 : ∃! x, A.mulVec x = 0
      --     := by exact hA 0
      --   have h3 : A.mulVec (0: n → R) = (0: m → R)
      --     := by exact mulVec_zero A
      --   have h2_oppo : ¬ (∃! x, A.mulVec x = 0)
      --     := by
      --     apply?
      --   exact h2_oppo (hA 0)

      theorem MainGoal8 {R : Type*} [CommRing R]
      {A : Matrix m n R}
      (hA : ∀ b : m → R, ∃! x, A.mulVec x = b)
      :LinearIndependent R (fun i ↦ A.transpose i)
        := by
        by_contra h
        rw [LinearIndependent, LinearMap.ker_eq_bot'] at h
        push_neg at h
        obtain ⟨v, hv, hv'⟩ := h
        let b1 : m → R := 0
        have h2 : ∃! x, A.mulVec x = 0
          := by exact hA 0
        have h3 : A.mulVec (0: n → R) = (0: m → R)
          := by exact mulVec_zero A
        have h2_oppo : ∃ x y ,(x≠y) ∧ A.mulVec x = 0 ∧ A.mulVec y = 0
          := by sorry
          -- use 0
          -- use v
          -- constructor
          -- · exact h3
          -- · sorry
          -- rw [Finsupp.total] at hv
        obtain ⟨x1,x2,x3,x4,x5⟩ := h2_oppo
        have h4:= (ExistsUnique.unique h2 x4 x5)
        exact x3 h4

      -- theorem MainGoal6 {R : Type*} [CommRing R]
      -- {A : Matrix m n R}
      -- (hA : ∀ b : m → R, ∃! x, A.mulVec x = b)
      -- :LinearIndependent R (fun i ↦ A.transpose i)
      --   := by
      --   by_contra h
      --   rw [LinearIndependent, LinearMap.ker_eq_bot'] at h
      --   push_neg at h
      --   obtain ⟨v, hv, hv'⟩ := h
      --   let b1 : m → R := 0
      --   have h2 : ∃! x, A.mulVec x = 0
      --     := by exact hA 0
      --   have h3 : A.mulVec (0: n → R) = (0: m → R)
      --     := by exact mulVec_zero A
      --   have h2_oppo : ∃ x y ,(x≠y) ∧ A.mulVec x = 0 ∧ A.mulVec y = 0
      --     := by sorry
      --     -- use 0
      --     -- use v
      --     -- constructor
      --     -- · exact h3
      --     -- · sorry
      --     -- rw [Finsupp.total] at hv
      --   have h5: ((∃ x1,∃ x2, x1≠x2 ∧ mulVec A x1 = 0 ∧ mulVec A x2 = 0))
      --   →
      --   (¬ (∃! x, mulVec A x = 0))
      --     := by
      --     intro h5_1
      --     obtain ⟨x1,x2,x3,x4,x5⟩ := h5_1
      --     by_contra h5_2
      --     apply?
      --     sorry
      --     -- apply?
      --   have h4: ¬ (∃! x, mulVec A x = 0)
      --     := by
      --     apply h5
      --     exact h2_oppo
      --   -- exact h4 (hA 0)
      --   exact h4 (hA 0)

          theorem MainGoal7_1 {R : Type*} [CommRing R]
          (A : Matrix m n R)
          (x : n → R):
          mulVec A x = fun yi ↦ ∑ xi : n, x xi • A yi xi
            := by
            simp only [mulVec]
            ext h7_x
            rw [dotProduct]
            simp only [smul_eq_mul]
            refine' sum_congr _ _
            · rfl
            · exact fun x_1 a ↦ mul_comm (A h7_x x_1) (x x_1)

      theorem MainGoal7 {R : Type*} [CommRing R]
      {A : Matrix m n R}
      (hA : ∀ b : m → R, ∃! x, A.mulVec x = b) -- mulVec就是矩阵和向量的乘法运算
      :LinearIndependent R (fun i ↦ A.transpose i)
        := by
        refine' linearIndependent_iff'.2 _
        have h6:= hA 0
        have _h6:= hA 0
        obtain ⟨x, h6_1, h6_2⟩ := h6
        have h7: mulVec A x -- 这个引理可以单独抽出来
        = fun yi => ∑ xi, (x xi) • (A yi xi)
          := by
          exact (MainGoal7_1 A x)
        rw [h7] at h6_1
        intro h1 h2 h3
        by_contra oppo
        push_neg at oppo
        simp only [Matrix.transpose] at h3
        have h3_2 :∑ x in h1, h2 x • of (fun x y ↦ A y x) x
        = ∑ x in h1, h2 x • (fun x y ↦ A y x) x
          := by
          exact rfl
        rw [h3_2] at h3
        clear h3_2
        simp only at h3
        -- have h8: (fun yi ↦ ∑ xi in Fintype n, x xi • A yi xi)
        -- = (∑ x in h1, h2 x • fun y ↦ A y x)
        --   := by
        --   ext h8_1
        --   simp only [smul_eq_mul, Finset.sum_apply, Pi.smul_apply]
        --   refine' sum_congr _ _
        clear hA
        have h6_oppo : ∃ x y ,(x≠y) ∧ A.mulVec x = 0 ∧ A.mulVec y = 0
          := by
          use 0
          use h2
          constructor
          · sorry -- 很明显的不想等，因为oppo描述h2存在非0的
          constructor
          · sorry
          · sorry
          --   sorry
          -- constructor
          -- constructor
          -- · have oppo1:= 0 ≠ h2
          -- constructor
          -- · rw [h7]
          --   sorry
          -- · rw [h7]
          --   sorry
          done
        obtain ⟨x1,x2,x3,x4,x5⟩ := h6_oppo
        have h4:= (ExistsUnique.unique _h6 x4 x5)
        exact x3 h4
        done





      theorem MainGoal5 {R : Type*} [CommRing R] {A : Matrix m n R} -- 一个大神的证明
      (hA : ∀ b : m → R, ∃! x, A.mulVec x = b) :
      LinearIndependent R (fun i ↦ A.transpose i)
        := by
        exact Matrix.mulVec_injective_iff.1 ((Function.bijective_iff_existsUnique _).mpr hA).injective
        done





  end Module

end
