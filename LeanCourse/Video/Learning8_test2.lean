import Mathlib.LinearAlgebra.Matrix.Transvection
-- 高斯：任意矩阵可化成对角形式 -- 线性方程组的人肉解



--TransvectionStruct：是行变换的结构，保存了关键信息
-- L.map：是 L.map f 即应用f到列表的每个元素，结果也是一个List。
-- List.prod：是列表中的元素从左到右全部乘起来
-- Sum n p：是不相交并集类型，用来拼一个新的更大的矩阵用的。比如：n*n扩充成m*m的矩阵，需要补充三个块
  -- inl是上一行的特殊化：左并
-- diagonal：是对角矩阵

universe u₁ u₂

namespace Matrix

open Matrix

variable (n p : Type*) (R : Type u₂) {𝕜 : Type*} [Field 𝕜]

variable [DecidableEq n] [DecidableEq p]

variable [CommRing R]

section Transvection

variable {R n} (i j : n)

/-- stdBasisMatrix i j a是 : 第i行，j列为a，其他地方为0的一个矩阵。 -/
def transvection2 (c : R) : Matrix n n R :=
  1 + Matrix.stdBasisMatrix i j c

section

variable [Fintype n]

end

variable (R n)

/-- 实际上代表的是行变换，有一个矩阵，操作是：将第i行的c倍加到第j行上。 -/
structure TransvectionStruct2 where
  (i j : n)
  hij : i ≠ j
  c : R

namespace TransvectionStruct

variable {R n}

/--将单位矩阵通过行变换t后得到的一个矩阵 -/
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


theorem exists_list_transvec_mul_mul_list_transvec_eq_diagonal2 (M : Matrix n n 𝕜) : --todo
    ∃ (L L' : List (TransvectionStruct n 𝕜)) (D : n → 𝕜),
      (L.map toMatrix).prod * M * (L'.map toMatrix).prod = diagonal D := by
  have e : n ≃ Fin (Fintype.card n) := Fintype.equivOfCardEq (by simp)
  apply reindex_exists_list_transvec_mul_mul_list_transvec_eq_diagonal M e
  apply exists_list_transvec_mul_mul_list_transvec_eq_diagonal_aux


/-- 任何矩阵可以写成：三个矩阵的乘积，第一个矩阵的作用效果是一系列的行变换左乘，第二个是一个对角矩阵，第三个是一系列的行变换右乘-/
theorem exists_list_transvec_mul_diagonal_mul_list_transvec2
(M : Matrix n n 𝕜) :
∃ (L L' : List (TransvectionStruct n 𝕜))
(D : n → 𝕜),

M
=
(L.map toMatrix).prod
*
diagonal D --左上->右下的对角线才有非零的数的方阵
*
(L'.map toMatrix).prod

  := by
  have h1 := exists_list_transvec_mul_mul_list_transvec_eq_diagonal2 M
  obtain ⟨L, L', D, h⟩ := h1
  --另一种写法： rcases exists_list_transvec_mul_mul_list_transvec_eq_diagonal M with ⟨L, L', D, h⟩
  refine' ⟨L.reverse.map TransvectionStruct.inv, L'.reverse.map TransvectionStruct.inv, D, _⟩ -- 这里是在填充Goal里面的那几个存在的假设
  -- TransvectionStruct.inv就是将第i行的-c倍加到第j行， 之所以说是逆操作，是因为操作完TransvectionStruct以后再操作TransvectionStruct.inv结果就变回单位矩阵了。
  simp only [List.map_map] --//先后作用2个函数=一次作用2个函数的复合函数。定义而已。
  have changeTarget :
    List.prod (List.map (toMatrix ∘ TransvectionStruct.inv) (List.reverse L))
    *
    diagonal D
    *
    List.prod (List.map (toMatrix ∘ TransvectionStruct.inv) (List.reverse L'))
    =
      (L.reverse.map (toMatrix ∘ TransvectionStruct.inv)).prod
      * (L.map toMatrix).prod
      * M
      * ((L'.map toMatrix).prod
          *
          (L'.reverse.map (toMatrix ∘ TransvectionStruct.inv)).prod
        )
    := by
      simp only [← h]
      simp only [Matrix.mul_assoc]
      done
  rw [changeTarget]
  rw [
  reverse_inv_prod_mul_prod,
  prod_mul_reverse_inv_prod,
  Matrix.one_mul,
  Matrix.mul_one]



end Pivot
