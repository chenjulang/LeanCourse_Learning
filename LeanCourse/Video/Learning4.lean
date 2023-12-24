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
      -- comap f ⊥ 的含义是将零子空间通过逆映射 f 映射回原始的定义域。
      -- 最终，ker (f : F) 返回的是线性映射 f 的核，即所有映射到零向量的输入的集合。
      -- Submodule R M：环 R 上的模 M 的子模组成的集合类型
    def LinearIndependent2 : Prop :=
      LinearMap.ker (Finsupp.total ι M R v) = ⊥ -- 在线性代数中，⊥ 经常用于表示零空间或零子空间。
    -- 假设我们有一个向量空间 V，它是由实数组成，记作 {v0, v1, v2, ...}。接下来，让我们考虑一个具体的例子，其中有限支撑函数 f 从整数集合到这个向量空间 V 上的向量。假设 f 是这样一个函数：
    -- f(0) = 2
    -- f(1) = -3
    -- f(3) = 5
    -- 现在，我们可以使用 Finsupp.total 函数将这些特殊的函数组合起来，得到一个 V 中的向量，即把所有函数 f 的值加在一起得到的结果。在这个例子中，我们可以计算如下：
    -- plaintext
    -- Finsupp.total ι V R (λ i, f i)
    -- 根据上述定义的函数 f，我们可以计算出：
    -- plaintext
    -- Finsupp.total ι V R (λ i, f i) = 2 * v0 + (-3) * v1 + 5 * v3
    -- 这里，v0, v1 和 v3 是 V 中的基向量。因此，Finsupp.total ι V R (λ i, f i) 将是向量 2v0 - 3v1 + 5v3。
    -- 希望这个例子能够帮助你更好地理解 Finsupp.total ι M R v 的意义。

    -- smulRight:
    -- M₁ = ℝ²
    -- M = ℝ³
    -- S = ℝ
    -- f: M₁ →ₗ[ℝ] S
    -- f b = b₁ + 2b₂
    -- x: M
    -- x = [1, 2, 3]
    -- 在这个例子中，M₁ 是二维实数向量空间，M 是三维实数向量空间，S 是实数域。
    -- f 是一个线性映射，将 M₁ 中的向量 [b₁, b₂] 映射到实数域 S 上，根据定义，f b = b₁ + 2b₂。
    -- x 是一个三维实数向量 [1, 2, 3]。
    -- 现在我们可以应用 smulRight 方法，并提供上述定义中的参数值f 和 x：
    -- result = smulRight(f, x)
    -- 计算结果如下：
    -- 对于给定的输入 b，result 的线性映射将 b 应用到 f 上，然后乘以向量 x。
    -- 假设我们选择 b = [2, 3]，那么根据 f 的定义，f [2, 3] = 2 + 2 * 3 = 8。
    -- 将 f [2, 3] 与向量 x = [1, 2, 3] 相乘得到 [8, 16, 24]。
    -- 因此，对于这个例子，result 的线性映射将输入向量 [2, 3] 映射为 [8, 16, 24]。

    -- lsum:
    -- 假设你有三个朋友：Alice、Bob 和 Charlie。你想创建一个函数，将每个人的名字映射到他们的年龄。你可以使用以下映射函数来实现：
    -- F: str → int
    -- F "Alice" = 25
    -- F "Bob" = 30
    -- F "Charlie" = 28
    -- 这里，F 是一个从字符串到整数的函数，它将每个名字映射到相应的年龄。
    -- 现在，假设你有一个名字列表，其中包含 Alice、Bob 和 Charlie：
    -- d: str →₀ int
    -- d = {"Alice" → 2, "Bob" → 1, "Charlie" → 3}
    -- 在这个例子中，我们有三个名字及其对应的数量。Alice 的数量是 2，Bob 的数量是 1，Charlie 的数量是 3。
    -- 现在，我们可以使用 lsum 方法将映射函数 F 和名字函数 d 组合起来：
    -- lsumResult = lsum F d
    -- lsumResult 是一个从 (str →₀ int) 到 int 的线性映射。
    -- 具体的计算步骤如下：
    -- 对于给定的输入 {"Alice" → 2, "Bob" → 1, "Charlie" → 3}，toFun 方法将遍历每个名字，并根据映射函数 F 将每个名字映射到相应的年龄。
    -- 根据我们之前定义的 F 函数，我们得到 Alice 的年龄是 25，Bob 的年龄是 30，Charlie 的年龄是 28。
    -- 根据 toFun 方法的定义，我们将对输入 {"Alice" → 2, "Bob" → 1, "Charlie" → 3} 中的每个名字进行遍历。对于 "Alice"，我们将应用 F "Alice"，对于 "Bob"，我们将应用 F "Bob"，对于 "Charlie"，我们将应用 F "Charlie"。然后，我们将所有结果进行求和，并得到最终的结果。

    -- lsum：
    -- 让我们通过一个具体的例子来说明这个同构关系：
    -- 假设我们有一个线性映射 f: ℝ² → ℝ，它将二维实数向量映射到实数。这个映射可以表示为：
    -- f((x, y)) = 2x + 3y
    -- 其中 x 和 y 是实数。
    -- 现在，我们希望找到一个同构关系，将这个线性映射 f 表示为一个有限支持函数经过另一个线性映射的组合。
    -- 首先，我们定义一个特殊的有限支持函数 g: {1, 2} →₀ ℝ²，它对应着一个从索引集合 {1, 2} 到 ℝ² 的映射，并且只在索引集合中的有限个位置取非零值。我们可以定义 g 如下：
    -- g(1) = (1, 0)
    -- g(2) = (0, 1)
    -- 接下来，根据同构关系 (α → M →ₗ[R] N) ≃ₗ[S] (α →₀ M) →ₗ[R] N，我们可以找到一个线性同构，将 f 转换为另一种表达形式。
    -- 我们可以定义一个线性映射 L: (α →₀ M) →ₗ[R] N，它将有限支持函数映射到实数。我们可以选择 L(g) = 2g(1) + 3g(2)，即 L(g) = 2 * g(1)_1 + 3 * g(2)_2，其中 g(i)_j 表示 g(i) 中第 j 个分量。
    -- 通过这样的构造，我们可以将原始的线性映射 f 表示为一个有限支持函数 g 经过另一个线性映射 L 的组合。这展示了 (α → M →ₗ[R] N) 和 (α →₀ M) →ₗ[R] N 之间的同构关系。



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
