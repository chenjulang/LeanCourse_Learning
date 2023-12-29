import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Span

-- 生成集，最终证明:矩阵的各列生成Rn空间

open LinearMap Matrix Set Submodule
open BigOperators
open Matrix
universe u v w

--span的参数
variable {R R₂ K M M₂ V S : Type*}

open Function Set
open Pointwise

variable [Semiring R] [AddCommMonoid M] [Module R M]
variable {x : M} (p p' : Submodule R M)
variable [Semiring R₂] {σ₁₂ : R →+* R₂}
variable [AddCommMonoid M₂] [Module R₂ M₂] {F : Type*} [SemilinearMapClass F σ₁₂ M M₂]

variable (R) -- 这个是span2的隐式参数,但是不知道为什么不能写在span2的名称后面
def span2 (s : Set M) : Submodule R M :=
  sInf { p | s ⊆ p }


-- //// 下面是应用在矩阵的代码：




noncomputable section

open LinearMap Matrix Set Submodule

open BigOperators

open Matrix

-- universe u v w

-- instance {n m} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n] (R) [Fintype R] :
--     Fintype (Matrix m n R) := by unfold Matrix; infer_instance




section mulVec

  variable {R : Type*} [CommSemiring R]

  variable {k l m n : Type*}

  variable [Fintype n]

  theorem Matrix.range_mulVecLin2 (M : Matrix m n R) :
  LinearMap.range M.mulVecLin
  = span R (range Mᵀ) := by
    rw [
    ← vecMulLinear_transpose,
    range_vecMulLinear]

end mulVec

section ToMatrix'

  variable {R : Type*} [CommSemiring R]

  variable {k l m n : Type*} [DecidableEq n] [Fintype n]

  theorem Matrix.range_toLin'2 (M : Matrix m n R) :
  LinearMap.range (Matrix.toLin' M)
  = span2 R (range Mᵀ)
    :=
    Matrix.range_mulVecLin2 M

end ToMatrix'

end
