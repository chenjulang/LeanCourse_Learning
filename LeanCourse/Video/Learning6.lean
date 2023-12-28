import Mathlib.LinearAlgebra.Matrix.ToLin


noncomputable section

open LinearMap Matrix Set Submodule

open BigOperators

open Matrix

universe u v w

instance {n m} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n] (R) [Fintype R] :
    Fintype (Matrix m n R) := by unfold Matrix; infer_instance

-- 生成集，最终证明矩阵的各列生成Rn空间
section ToMatrix'

variable {R : Type*} [CommSemiring R]

variable {k l m n : Type*} [DecidableEq n] [Fintype n]

theorem Matrix.range_toLin' (M : Matrix m n R) :
    LinearMap.range (Matrix.toLin' M) = span R (range Mᵀ) :=
  Matrix.range_mulVecLin _

end
