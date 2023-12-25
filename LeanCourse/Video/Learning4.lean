import Mathlib.LinearAlgebra.LinearIndependent

-- 线性独立
noncomputable section

  open Function Set Submodule

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





    theorem linearIndependent2_iff : LinearIndependent2 R v ↔ ∀ l, Finsupp.total ι M R v l = 0 → l = 0 :=
      by simp [LinearIndependent2, LinearMap.ker_eq_bot']

    theorem linearIndependent2_iff' :
        LinearIndependent2 R v ↔
          ∀ s : Finset ι, ∀ g : ι → R, ∑ i in s, g i • v i = 0 → ∀ i ∈ s, g i = 0
      :=
      (linearIndependent_iff).trans
        ⟨fun hf s g hg i his =>
          have h :=
            hf (∑ i in s, Finsupp.single i (g i)) <| by
              simpa only [map_sum, Finsupp.total_single] using hg
          calc
            g i = (Finsupp.lapply i : (ι →₀ R) →ₗ[R] R) (Finsupp.single i (g i)) := by
              { rw [Finsupp.lapply_apply, Finsupp.single_eq_same] }
            _ = ∑ j in s, (Finsupp.lapply i : (ι →₀ R) →ₗ[R] R) (Finsupp.single j (g j)) :=
              Eq.symm <|
                Finset.sum_eq_single i
                  (fun j _hjs hji => by rw [Finsupp.lapply_apply, Finsupp.single_eq_of_ne hji])
                  fun hnis => hnis.elim his
            _ = (∑ j in s, Finsupp.single j (g j)) i := (map_sum ..).symm
            _ = 0 := FunLike.ext_iff.1 h i,
          fun hf l hl =>
          Finsupp.ext fun i =>
            _root_.by_contradiction fun hni => hni <| hf _ _ hl _ <| Finsupp.mem_support_iff.2 hni⟩





  end Module

end
