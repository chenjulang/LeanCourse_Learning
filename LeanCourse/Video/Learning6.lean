import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Span

-- 生成集，引入：我们想知道由有限的东西扩展出来的集合，会有什么特别之处。能否解释其他东西？
  -- 横看成岭侧成峰
  -- 最终证明:某个矩阵A,A的各列,实数,（这样的实数排列起来就是任意向量x）。A的各列和实数的所有线性组合 = 矩阵A乘以任意n*1向量x的值域
    -- 换句话说，列向量生成了一个矩阵乘积的所有结果。
    -- 准确来说，矩阵乘积的所有结果和列向量生成的集合刚好相等。

open LinearMap Matrix Set Submodule
open BigOperators
open Matrix
universe u v w --两部分都用到的参数
--span部分的参数
variable {R R₂ K M M₂ V S : Type*}

open Function Set
open Pointwise

variable [Semiring R] [AddCommMonoid M] [Module R M]
variable {x : M} (p p' : Submodule R M)
variable [Semiring R₂] {σ₁₂ : R →+* R₂}
variable [AddCommMonoid M₂] [Module R₂ M₂] {F : Type*} [SemilinearMapClass F σ₁₂ M M₂]

variable (R) -- 这个是span2的隐式参数,但是不知道为什么不能写在span2的名称后面
def span2 (s : Set M) : Submodule R M :=
-- 换句话说就是R和s中集合的线性集合的总和集合
-- R：就是线性组合的系数，这样的系数的取值范围，比如实数ℝ
-- 参数s：是一个由M中元素组成的集合
  sInf { p | s ⊆ p } -- p是能包含s集合的一个子空间，{ p | s ⊆ p }指所有这样的p的集合
  -- 而整个式子sInf { p | s ⊆ p } 说的是满足这样条件的子空间p里面，最小的那一个
  -- sInf的作用是Set α → α 即：(Set (Submodule R M)) → (Submodule R M),得到的是(Submodule R M)
  -- 但在哪里定义体现了最小呢???


-- //// 下面是应用在矩阵的代码：



noncomputable section
  open LinearMap Matrix Set Submodule
  open BigOperators
  open Matrix

  section ToMatrixRight
    variable {R : Type*} [Semiring R]
    variable {l m n : Type*}
    variable [Fintype m] [DecidableEq m]

    theorem range_vecMulLinear2 (M : Matrix m n R) :  --第二层
    LinearMap.range M.vecMulLinear
    = span R (range M)
      := by --todo
      letI := Classical.decEq m
      simp_rw [range_eq_map, --???
      ← iSup_range_stdBasis,--???
      Submodule.map_iSup,
      range_eq_map,
      ← Ideal.span_singleton_one,
      Ideal.span,
      Submodule.map_span,
      image_image,
      image_singleton,
      Matrix.vecMulLinear_apply,
      iSup_span,
      range_eq_iUnion,
      iUnion_singleton_eq_range,
      LinearMap.stdBasis,
      coe_single]
      unfold vecMul
      simp_rw [single_dotProduct,
      one_mul]
      done
  end ToMatrixRight

  section mulVec
    variable {R : Type*} [CommSemiring R]
    variable {k l m n : Type*}
    variable [Fintype n]

    -- 关键的小引理，思想通常很简单：就是定义
    lemma vecMul_transpose2 [Fintype n] (A : Matrix m n R) (x : n → R)
    : vecMul x Aᵀ = mulVec A x := by
      ext x1
      rw[vecMul]
      rw[mulVec]
      simp only [transpose_apply]
      exact dotProduct_comm x fun i ↦ A x1 i

    lemma Matrix.vecMulLinear_transpose2 [Fintype n] (M : Matrix m n R)
    : Mᵀ.vecMulLinear = M.mulVecLin
      := by
      ext;
      simp only [vecMulLinear_apply, mulVecLin_apply]--这里可以顺便讲一下递归定义和函数定义的等价性：
                                                      --     def vecMul [Fintype m] (v : m → α) (M : Matrix m n α) : n → α
                                                      -- | j => v ⬝ᵥ fun i => M i j
                                                      -- -- := fun j => v ⬝ᵥ fun i => M i j -- 一个意思
      simp [vecMul_transpose2]

    theorem Matrix.range_mulVecLin2 (M : Matrix m n R) : --第一层
    LinearMap.range M.mulVecLin
    = span R (range Mᵀ)
    := by --todo
      rw [← vecMulLinear_transpose2,
      range_vecMulLinear2]
  end mulVec

  section ToMatrix'
    variable {R : Type*} [CommSemiring R]
    variable {k l m n : Type*} [DecidableEq n] [Fintype n]

    theorem MainGoal6 (M : Matrix m n R) : --左右映射的值域相等
    LinearMap.range (Matrix.toLin' M) -- Matrix.toLin'： 将这个矩阵转换为一个线性映射（linear map）。就是将n维数列映射成m维数列的这样一个数列。这个线性映射的定义域是 Rn，值域是 Rm。
    = span R (range Mᵀ) --因为Mᵀ类型是n→ m→ R的映射，range Mᵀ即第一个参数n传入后，得到的m→ R的集合。比如就是由矩阵
    -- ![![1, 2, 3],
    -- ![4, 5, 6],
    -- ![7, 8, 9]]   的第1列的矩阵+第2列的矩阵+第3列的矩阵 加起来的这个3*1矩阵的集合。
      :=
      Matrix.range_mulVecLin2 M

    -- lemma equal1  (M : Matrix m n R):Matrix.toLin' M = M.mulVecLin
    --   := by
    --   exact Eq.refl (toLin' M)
    -- tolin 需要作用到M上，看到invFun 是 Matrix.mulVecLin，一摸一样的，结果当然也是M.mulVec
    -- M.mulVecLin则是这样,直接作用于M后的结果是,所以不需要参数M写在后面：结果都是M.mulVec,也就是M准备和一个向量做矩阵乘法



  end ToMatrix'

end
