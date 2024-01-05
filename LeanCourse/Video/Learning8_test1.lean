import Mathlib.LinearAlgebra.Matrix.Transvection
-- 高斯：任意矩阵可化成对角形式 -- 线性方程组的人肉解



universe u₁ u₂

namespace Matrix

open Matrix

variable (n p : Type*) (R : Type u₂) {𝕜 : Type*} [Field 𝕜]

variable [DecidableEq n] [DecidableEq p]

variable [CommRing R]

section Transvection

variable {R n} (i j : n)

def transvection2 (c : R) : Matrix n n R :=
  1 + Matrix.stdBasisMatrix i j c
  -- stdBasisMatrix i j a是
  -- 矩阵a在里面i行，j列， 和其他地方的零。

section

variable [Fintype n]

end

variable (R n)

/-- A structure containing all the information from which one can build a nontrivial transvection.
This structure is easier to manipulate than transvections as one has a direct access to all the
relevant fields. -/
-- porting note: removed @[nolint has_nonempty_instance]
structure TransvectionStruct2 where
  (i j : n)
  hij : i ≠ j
  c : R

namespace TransvectionStruct

variable {R n}

/-- Associating to a `transvection_struct` the corresponding transvection matrix. -/
def toMatrix2 (t : TransvectionStruct n R) : Matrix n n R :=
  transvection t.i t.j t.c

section

variable [Fintype n]

end

open Sum


variable {p}

variable [Fintype n] [Fintype p]

end TransvectionStruct

end Transvection


namespace Pivot

variable {R} {r : ℕ} (M : Matrix (Sum (Fin r) Unit) (Sum (Fin r) Unit) 𝕜)

open Sum Unit Fin TransvectionStruct

variable {n p} [Fintype n] [Fintype p]

/-- Any matrix can be written as the product of transvections, a diagonal matrix, and
transvections.-/
theorem exists_list_transvec_mul_diagonal_mul_list_transvec2
(M : Matrix n n 𝕜) :
∃ (L L' : List (TransvectionStruct n 𝕜))
(D : n → 𝕜),
M
= (L.map toMatrix).prod
  *
  diagonal D
  *
  (L'.map toMatrix).prod
  := by
  rcases exists_list_transvec_mul_mul_list_transvec_eq_diagonal M with ⟨L, L', D, h⟩
  refine' ⟨L.reverse.map TransvectionStruct.inv, L'.reverse.map TransvectionStruct.inv, D, _⟩
  suffices
    M =
      (L.reverse.map (toMatrix ∘ TransvectionStruct.inv)).prod * (L.map toMatrix).prod * M *
        ((L'.map toMatrix).prod * (L'.reverse.map (toMatrix ∘ TransvectionStruct.inv)).prod)
    by simpa [← h, Matrix.mul_assoc]
  rw [
  reverse_inv_prod_mul_prod,
  prod_mul_reverse_inv_prod,
  Matrix.one_mul,
  Matrix.mul_one]

-- #print exists_list_transvec_mul_diagonal_mul_list_transvec2


end Pivot


--TransvectionStruct是行变换的结构，保存了关键信息
-- L.map是 L.map f 即应用f到列表的每个元素，结果也是一个List。
-- List.prod是列表中的元素从左到右全部乘起来
-- Sum n p是不相交并集类型
-- inl是上一行的特殊化：左并
-- todo Transvection.lean看到toMatrix_sumInl
-- diagonal是什么？
