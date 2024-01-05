import Mathlib.LinearAlgebra.Matrix.Transvection
-- 高斯：任意矩阵可化成对角形式 -- 线性方程组的人肉解

theorem exists_list_transvec_mul_diagonal_mul_list_transvec
(M : Matrix n n 𝕜) :
∃ (L L' : List (TransvectionStruct n 𝕜))
(D : n → 𝕜),
M =
(L.map toMatrix).prod * diagonal D * (L'.map toMatrix).prod
  := by
  rcases exists_list_transvec_mul_mul_list_transvec_eq_diagonal M with ⟨L, L', D, h⟩
  refine' ⟨L.reverse.map TransvectionStruct.inv, L'.reverse.map TransvectionStruct.inv, D, _⟩
  suffices
    M =
      (L.reverse.map (toMatrix ∘ TransvectionStruct.inv)).prod * (L.map toMatrix).prod * M *
        ((L'.map toMatrix).prod * (L'.reverse.map (toMatrix ∘ TransvectionStruct.inv)).prod)
    by simpa [← h, Matrix.mul_assoc]
  rw [reverse_inv_prod_mul_prod, prod_mul_reverse_inv_prod, Matrix.one_mul, Matrix.mul_one]
