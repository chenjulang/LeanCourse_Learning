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

variable (R)

def span2 (s : Set M) : Submodule R M :=
sInf { p | s ⊆ p }

-- //

variable {R2 : Type*} [CommSemiring R2]
variable {k2 l2 m2 n2 : Type*} [DecidableEq n2] [Fintype n2]

theorem Matrix.range_toLin2' (M2 : Matrix m2 n2 R2) :
    LinearMap.range (Matrix.toLin' M2) = span2 R2 (range M2ᵀ) :=
  Matrix.range_mulVecLin _
