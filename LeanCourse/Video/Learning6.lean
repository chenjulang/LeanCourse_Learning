import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Span
import Mathlib.Data.Real.Sqrt


-- 生成集，引入：我们想知道由有限的东西扩展出来的集合，会有什么特别之处。能否解释其他东西？
  -- 横看成岭侧成峰
  -- 最终证明:某个矩阵A,A的各列,实数,（这样的实数组合起来在一列就是任意向量x）。
  -- A的各列和实数的所有线性组合 = 矩阵A乘以任意n*1向量x的值域
    -- 换句话说，列向量生成了一个矩阵乘积A*X的所有结果。
    -- 准确来说，矩阵乘积A*X的所有结果和列向量生成的集合刚好相等。

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
-- R：就是线性组合的系数，这样的系数的取值范围，比如实数ℝ
-- 参数s：是一个由M中元素组成的集合
  sInf { p | s ⊆ p } -- p是能包含s集合的一个子空间，{ p | s ⊆ p }指所有这样的p的集合
  -- 而整个式子sInf { p | s ⊆ p } 说的是满足这样条件的子空间p里面，最小的那一个
  -- sInf的作用是Set α → α 即：(Set (Submodule R M)) → (Submodule R M),得到的是(Submodule R M)


-- 生成集明明讲的是“生成的最大的范围”的一个东西，为什么定义却使用“最小的模块”这样的字眼来定义呢？
  -- 首先集合s必然能通过线性组合生成一个封闭的模块，{ p | s ⊆ p }中的p是包含s的模块。如果往大的来说，
  -- 那举例：v1,v2是本来的向量，可以加上不能组合出来的v3,v4,v5等等，这样v1到v5也能形成一个封闭的模块，要多大都行，
  -- 这样定义的模块显然不是我们想要的所谓“生成集”。
  -- 如果往小的方向来说，那只由v1和v2形成的就是最小的封闭模块。
-- 为什么线性组合的所有集合就是封闭的？
  -- 具体而言，对于集合 s 中的向量 v₁ 和 v₂，它们的线性组合可以表示为 a₁v₁ + a₂v₂，其中 a₁ 和 a₂ 是标量（实数或复数）。
  -- 对于线性组合 a₁v₁ + a₂v₂，我们可以应用模块的加法和标量乘法操作：
  -- 加法：对于任意两个线性组合 a₁v₁ + a₂v₂ 和 b₁v₁ + b₂v₂，其中 a₁、a₂、b₁、b₂ 是标量，我们可以将它们相加
  -- 得到 (a₁+b₁)v₁ + (a₂+b₂)v₂。这个结果仍然是集合 s 的线性组合，因此属于线性组合的集合。
  -- 标量乘法：对于线性组合 a₁v₁ + a₂v₂ 和标量 c，我们可以将其乘以 c 得到 c(a₁v₁ + a₂v₂) = (ca₁)v₁ + (ca₂)v₂。这个结果
  -- 仍然是集合 s 的线性组合，因此也属于线性组合的集合。
-- 为什么最小子模块必然存在？
  -- 因为比如从已有的n个向量，进行线性组合，它这个集合肯定是封闭的对于加法和乘法，所以首先必然能形成一个模块。这就是它为什么存在。
  -- （这样的模块是无法全部列举的，只能用一般形式来表示(r₁)v₁ + (r₂)v₂
  -- 至于为什么最小，看下一行：
-- 为什么没有更小的最小子模块存在？
  -- 举例：某个N（封闭的模块）由v1和v2组合了一些对象出来，但元素数量不及最小子模块M，那对于任意的M中有的，目前没生成出来的
  -- 比如（c+d+p）v1+(e+w+q)v2，
  -- 是目前空间没有封闭的一个例证。必然要扩展到和M相同才能算封闭，否则和定义矛盾。
-- 为什么唯一？
  -- 假设有另一个最小子模块N（其元素都能由v1和v2组合出来），不同于M，除了包含集合s以外，还有一个集合s1是M不包含的，具体举例：
  -- 比如集合s有向量v1,v2,那么N多出来的集合s1是不能用v1和v2表示的（如果可以表示，那就包含于M，那N于M就没有差异了），
  -- 要想有新的元素，必须有v1和v2组合不出来的v3，这与定义“其元素都能由v1和v2组合出来”矛盾。所以比M大的N不存在。
-- 为什么包含集合s，且封闭的最小生成模块不能生成新的线性组合？
  -- 举例来说还是v1，v2,如果有新的线性组合(?1)v1+(?2)v2,这个必然已经在已有的组合中，新的组合需要新的不能由v1和v2组合出来的某个v3，
  -- 但是最小生成模块是基于v1和v2的，一开始并不存在这样的v3。


-- //// 下面是应用在矩阵的代码：

noncomputable section
  open LinearMap Matrix Set Submodule
  open BigOperators
  open Matrix


  section ToMatrixRight
    variable {R : Type*} [Semiring R]
    variable {l m n : Type*}
    variable [Fintype m] [DecidableEq m]

    -- def fai : ℕ → ℝ := sorry
    -- #check LinearMap.stdBasis R fai

    theorem range_vecMulLinear2 (M : Matrix m n R) :  --第二层这个太难了群论知识很深
    LinearMap.range M.vecMulLinear
    = span R (range M)
      := by
      letI := Classical.decEq m --???
      simp_rw [
      range_eq_map, --range f = map f ⊤，

      -- ⊤:其中⊤表示全体定义域的集合，也是空间
      -- （⊤也是因地制宜的，这里指所有的m → R向量形成的空间），
      -- 这里指所有(m → R)的m*1矩阵

      -- LinearMap.stdBasis ：
        --举例⊤
        -- = (⨆ i, LinearMap.range (LinearMap.stdBasis R (fun i ↦ R) i)
        --左右都是一个空间
        -- 左边是所有m → R向量线性组合的空间
        -- 右边是n个空间并起来的大空间，比如说i=1时
        --LinearMap.stdBasis R (fun i ↦ R) i的类型是 R →ₗ[R] m → R ，（能否理解成1=》（1，0，0，0，...）呢？）
        -- LinearMap.stdBasis R (fun i ↦ R) i可以理解成直接替换成Pi.single i ， 那值域就是任意取R得到的（R，0，0，0，...）
        -- i=1时 就是（0，R，0，0，0，...） 当然这个是一个空间来的，R是一个一般形式，实际上是无数个向量
        -- （0，1，0，0，0，...）， （0，1.1，0，0，0，...），（0，2，0，0，0，...），......

      ← iSup_range_stdBasis,
      Submodule.map_iSup,----分开基向量
      -- def vecMul [Fintype m] (v : m → α) (M : Matrix m n α) : n → α
      -- | j => v ⬝ᵥ fun i => M i j -- 列向量点乘
      -- ![![1, 2],
      --   ![3, 4]]
      -- 分开（m，0），（0，n）再加起来即
      -- i=1时： ![1m+0 , 2m+0]
      -- i=2时： ![0+3n , 0+4n]
      -- 和不分开（m,n）
      -- ![m+3n , 2m+4n]
      -- 的值域相等吗？当然值域是一样的
      range_eq_map,--LinearMap.range和Submodule.map两种写法互换
      ← Ideal.span_singleton_one,--理解成Pi.single的第一个参数是自然数，自然数可以由1和加法减法生成
      Ideal.span,--由1这个元素加法乘法减法生成的空间
      Submodule.map_span,--先组合再映射=先映射再组合
      -- s = {(1, 0, 0), (0, 1, 0)}
      -- f((x₁, x₂, x₃)) = (x₁, x₂)
      -- (span ℝ {(1, 0, 0), (0, 1, 0)}).map f = span ℝ₂ (f '' {(1, 0, 0), (0, 1, 0)})
      -- 左边即：map f（m,n,0） , 也就是（m,n）
      -- 右边即：由于f '' {(1, 0, 0), (0, 1, 0)}={(1, 0), (0, 1)}
      -- {(1, 0), (0, 1)}的生成集是 (m,n)
      image_image,--变成复合函数
      image_singleton,--只有一个值映射
      Matrix.vecMulLinear_apply,
      iSup_span,--类似于之前的Submodule.map_iSup，单个向量生成集，有多个，并起来=多个向量直接生成集。这里不举例子了。
      range_eq_iUnion,--函数结果=定义域列举，分别代入后得到所有值并起来。
      iUnion_singleton_eq_range,--和上一行反过来，所以把上一行的也作用到了，而且把等号左边的也作用到了
      LinearMap.stdBasis,
      coe_single]--看single的toFun定义可知
      unfold vecMul
      simp_rw [
      single_dotProduct,--只有一处为非零的向量，当然了，结果只有一项
      one_mul] -- fun x x_1 ↦ 1 * M x x_1和 fun x ↦ M x 是一样的：这样验证，都给两个参数进去，得到的值是同一个矩阵的同一项
      done

    -- #print range_vecMulLinear2
  end ToMatrixRight


  section mulVec
    variable {R : Type*} [CommSemiring R]
    variable {k l m n : Type*}
    variable [Fintype n]

    -- 关键的小引理，思想通常很简单：就是定义
    lemma vecMul_transpose2 [Fintype n] (A : Matrix m n R) (x : n → R)
    : vecMul x Aᵀ
    = mulVec A x
      := by
      ext x1
      rw[vecMul]
      rw[mulVec]
      simp only [transpose_apply]
      exact dotProduct_comm x fun i ↦ A x1 i --点乘顺序无关
      done

    lemma Matrix.vecMulLinear_transpose2 [Fintype n] (M : Matrix m n R)
    : Mᵀ.vecMulLinear
    = M.mulVecLin
      := by
      ext
      simp only [vecMulLinear_apply] --2个向下兼容
      simp only [mulVecLin_apply]
      --这里可以顺便讲一下递归定义和函数定义的等价性：
      --     def vecMul [Fintype m] (v : m → α) (M : Matrix m n α) : n → α
          -- | j => v ⬝ᵥ fun i => M i j
          -- -- := fun j => v ⬝ᵥ fun i => M i j -- 一个意思
      simp [vecMul_transpose2]
      done



    theorem Matrix.range_mulVecLin2 (M : Matrix m n R) : --第一层
    LinearMap.range M.mulVecLin -- 函数加个Lin说明不止是映射，而且满足“线性”
    = span R (range Mᵀ)
    := by
      rw [
      ← vecMulLinear_transpose2,
      range_vecMulLinear2]
      done

  end mulVec


  section ToMatrix'
    variable {R : Type*} [CommSemiring R]
    variable {k l m n : Type*} [DecidableEq n] [Fintype n]

    theorem MainGoal6 (M : Matrix m n R) : --左右映射的值域相等
    LinearMap.range (Matrix.toLin' M) -- Matrix.toLin'： 将这个矩阵转换为一个
    -- 线性映射（linear map）。
    -- 就是将n维数列映射成m维数列。这个线性映射的定义域是 Rn，值域是 Rm。（注意和这里顺序
    -- 刚好相反Matrix m n R）
    = span2 R (range Mᵀ) --因为Mᵀ类型是n → m → R的映射，range Mᵀ即第一个参数n传入后，
    -- 得到的值域，即m → R类型的集合。比如就是由矩阵
    -- ![![1, 2, 3],
    --   ![4, 5, 6],
    --   ![7, 8, 9]]   的第1列的矩阵+第2列的矩阵+第3列的矩阵 加起来的3*1矩阵的集合，共3个元素。
      :=
      Matrix.range_mulVecLin2 M

  -- 用于讲解：
      lemma equal1  (M : Matrix m n R):Matrix.toLin' M = M.mulVecLin
      := by
      exact Eq.refl (toLin' M)
    -- tolin 需要作用到M上，看到symm，看到invFun 是 Matrix.mulVecLin，一摸一样的，结果当然也是M.mulVec
    -- M.mulVecLin则是这样,直接作用于M后的结果是,所以不需要参数M写在后面：结果都是M.mulVec,
    -- 也就是M准备接受一个向量参数做矩阵乘法




  end ToMatrix'

end
