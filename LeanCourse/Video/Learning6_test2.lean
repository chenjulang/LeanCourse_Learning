-- import Mathlib.LinearAlgebra.Matrix.ToLin



-- noncomputable section

-- open LinearMap Matrix Set Submodule

-- open BigOperators

-- open Matrix

-- universe u v w

-- -- instance {n m} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n] (R) [Fintype R] :
-- --     Fintype (Matrix m n R) := by unfold Matrix; infer_instance




-- section mulVec

--   variable {R : Type*} [CommSemiring R]

--   variable {k l m n : Type*}

--   variable [Fintype n]

--   theorem Matrix.range_mulVecLin2 (M : Matrix m n R) :
--       LinearMap.range M.mulVecLin = span R (range Mᵀ) := by
--     rw [← vecMulLinear_transpose, range_vecMulLinear]

-- end mulVec

-- section ToMatrix'

--   variable {R : Type*} [CommSemiring R]

--   variable {k l m n : Type*} [DecidableEq n] [Fintype n]

--   theorem Matrix.range_toLin'2 (M : Matrix m n R) :
--       LinearMap.range (Matrix.toLin' M) = span R (range Mᵀ) :=
--     Matrix.range_mulVecLin2 _

-- end ToMatrix'

-- end
