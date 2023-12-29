-- import Mathlib.LinearAlgebra.Matrix.ToLin

-- noncomputable section
--   open LinearMap Matrix Set Submodule
--   open BigOperators
--   open Matrix
--   universe u v w

--   section ToMatrixRight
--     variable {R : Type*} [Semiring R]
--     variable {l m n : Type*}
--     variable [Fintype m] [DecidableEq m]
--     theorem range_vecMulLinear2 (M : Matrix m n R) :
--     LinearMap.range M.vecMulLinear
--     = span R (range M)
--       := by
--       letI := Classical.decEq m
--       simp_rw [range_eq_map, ← iSup_range_stdBasis, Submodule.map_iSup, range_eq_map, ←
--         Ideal.span_singleton_one, Ideal.span, Submodule.map_span, image_image, image_singleton,
--         Matrix.vecMulLinear_apply, iSup_span, range_eq_iUnion, iUnion_singleton_eq_range,
--         LinearMap.stdBasis, coe_single]
--       unfold vecMul
--       simp_rw [single_dotProduct, one_mul]
--   end ToMatrixRight

--   section mulVec
--     variable {R : Type*} [CommSemiring R]
--     variable {k l m n : Type*}
--     variable [Fintype n]
--     theorem Matrix.range_mulVecLin2 (M : Matrix m n R) :
--         LinearMap.range M.mulVecLin = span R (range Mᵀ) := by
--       rw [← vecMulLinear_transpose,
--       range_vecMulLinear2]
--   end mulVec

--   section ToMatrix'
--     variable {R : Type*} [CommSemiring R]
--     variable {k l m n : Type*} [DecidableEq n] [Fintype n]
--     theorem Matrix.range_toLin'2 (M : Matrix m n R) :
--         LinearMap.range (Matrix.toLin' M) = span R (range Mᵀ) :=
--       Matrix.range_mulVecLin2 _
--   end ToMatrix'

-- end
