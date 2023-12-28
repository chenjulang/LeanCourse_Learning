import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Span

open LinearMap Matrix Set Submodule
open BigOperators
open Matrix
universe u v w

-- instance {n m} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n] (R) [Fintype R] :
--     Fintype (Matrix m n R) := by unfold Matrix; infer_instance
--span的参数
variable {R R₂ K M M₂ V S : Type*}

-- namespace Submodule
open Function Set
open Pointwise

  -- section AddCommMonoid

variable [Semiring R] [AddCommMonoid M] [Module R M]
variable {x : M} (p p' : Submodule R M)
variable [Semiring R₂] {σ₁₂ : R →+* R₂}
variable [AddCommMonoid M₂] [Module R₂ M₂] {F : Type*} [SemilinearMapClass F σ₁₂ M M₂]

-- section
variable (R)

def span2 (s : Set M) : Submodule R M :=
sInf { p | s ⊆ p }

-- end

  -- end AddCommMonoid

-- end Submodule



--

-- 生成集，最终证明矩阵的各列生成Rn空间
section ToMatrix'

  variable {R : Type*} [CommSemiring R]

  variable {k l m n : Type*} [DecidableEq n] [Fintype n]

  theorem Matrix.range_toLin2' (M : Matrix m n R) :
      LinearMap.range (Matrix.toLin' M) = span2 R (range Mᵀ) :=
    Matrix.range_mulVecLin _

end ToMatrix'
