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



theorem exists_isTwoBlockDiagonal_of_ne_zero2 (hM : M (inr unit) (inr unit) ≠ 0) : --???
    ∃ L L' : List (TransvectionStruct (Sum (Fin r) Unit) 𝕜),
      IsTwoBlockDiagonal ((L.map toMatrix).prod * M * (L'.map toMatrix).prod)
  := by
  let L : List (TransvectionStruct (Sum (Fin r) Unit) 𝕜) :=
    List.ofFn fun i : Fin r =>
      ⟨inl i, inr unit, by simp, -M (inl i) (inr unit) / M (inr unit) (inr unit)⟩
  let L' : List (TransvectionStruct (Sum (Fin r) Unit) 𝕜) :=
    List.ofFn fun i : Fin r =>
      ⟨inr unit, inl i, by simp, -M (inr unit) (inl i) / M (inr unit) (inr unit)⟩
  refine' ⟨L, L', _⟩
  have A : L.map toMatrix = listTransvecCol M := by simp [listTransvecCol, (· ∘ ·)]
  have B : L'.map toMatrix = listTransvecRow M := by simp [listTransvecRow, (· ∘ ·)]
  rw [A, B]
  exact isTwoBlockDiagonal_listTransvecCol_mul_mul_listTransvecRow M hM



theorem reindex_exists_list_transvec_mul_mul_list_transvec_eq_diagonal2 (M : Matrix p p 𝕜) --???
    (e : p ≃ n)
    (H :
      ∃ (L L' : List (TransvectionStruct n 𝕜)) (D : n → 𝕜),
        (L.map toMatrix).prod * Matrix.reindexAlgEquiv 𝕜 e M * (L'.map toMatrix).prod =
          diagonal D) :
    ∃ (L L' : List (TransvectionStruct p 𝕜)) (D : p → 𝕜),
      (L.map toMatrix).prod * M * (L'.map toMatrix).prod = diagonal D := by
  rcases H with ⟨L₀, L₀', D₀, h₀⟩
  refine' ⟨L₀.map (reindexEquiv e.symm), L₀'.map (reindexEquiv e.symm), D₀ ∘ e, _⟩
  have : M = reindexAlgEquiv 𝕜 e.symm (reindexAlgEquiv 𝕜 e M) := by
    simp only [Equiv.symm_symm, submatrix_submatrix, reindex_apply, submatrix_id_id,
      Equiv.symm_comp_self, reindexAlgEquiv_apply]
  rw [this]
  simp only [toMatrix_reindexEquiv_prod, List.map_map, reindexAlgEquiv_apply]
  simp only [← reindexAlgEquiv_apply, ← reindexAlgEquiv_mul, h₀]
  simp only [Equiv.symm_symm, reindex_apply, submatrix_diagonal_equiv, reindexAlgEquiv_apply]



theorem exists_isTwoBlockDiagonal_list_transvec_mul_mul_list_transvec2
    (M : Matrix (Sum (Fin r) Unit) (Sum (Fin r) Unit) 𝕜) :
    ∃ L L' : List (TransvectionStruct (Sum (Fin r) Unit) 𝕜),
      IsTwoBlockDiagonal ((L.map toMatrix).prod * M * (L'.map toMatrix).prod) := by
  by_cases H : IsTwoBlockDiagonal M
  · refine' ⟨List.nil, List.nil, by simpa using H⟩
  -- we have already proved this when the last coefficient is nonzero
  by_cases hM : M (inr unit) (inr unit) ≠ 0
  · exact exists_isTwoBlockDiagonal_of_ne_zero2 M hM
  -- when the last coefficient is zero but there is a nonzero coefficient on the last row or the
  -- last column, we will first put this nonzero coefficient in last position, and then argue as
  -- above.
  push_neg at hM
  simp only [not_and_or, IsTwoBlockDiagonal, toBlocks₁₂, toBlocks₂₁, ← Matrix.ext_iff] at H
  have : ∃ i : Fin r, M (inl i) (inr unit) ≠ 0 ∨ M (inr unit) (inl i) ≠ 0 := by
    cases' H with H H
    · contrapose! H
      rintro i ⟨⟩
      exact (H i).1
    · contrapose! H
      rintro ⟨⟩ j
      exact (H j).2
  rcases this with ⟨i, h | h⟩
  · let M' := transvection (inr Unit.unit) (inl i) 1 * M
    have hM' : M' (inr unit) (inr unit) ≠ 0 := by simpa [hM]
    rcases exists_isTwoBlockDiagonal_of_ne_zero2 M' hM' with ⟨L, L', hLL'⟩
    rw [Matrix.mul_assoc] at hLL'
    refine' ⟨L ++ [⟨inr unit, inl i, by simp, 1⟩], L', _⟩
    simp only [List.map_append, List.prod_append, Matrix.mul_one, toMatrix_mk, List.prod_cons,
      List.prod_nil, List.map, Matrix.mul_assoc (L.map toMatrix).prod]
    exact hLL'
  · let M' := M * transvection (inl i) (inr unit) 1
    have hM' : M' (inr unit) (inr unit) ≠ 0 := by simpa [hM]
    rcases exists_isTwoBlockDiagonal_of_ne_zero2 M' hM' with ⟨L, L', hLL'⟩
    refine' ⟨L, ⟨inl i, inr unit, by simp, 1⟩::L', _⟩
    simp only [← Matrix.mul_assoc, toMatrix_mk, List.prod_cons, List.map]
    rw [Matrix.mul_assoc (L.map toMatrix).prod]
    exact hLL'


theorem exists_list_transvec_mul_mul_list_transvec_eq_diagonal_induction2 --???
    (IH :
      ∀ M : Matrix (Fin r) (Fin r) 𝕜,
        ∃ (L₀ L₀' : List (TransvectionStruct (Fin r) 𝕜)) (D₀ : Fin r → 𝕜),
          (L₀.map toMatrix).prod * M * (L₀'.map toMatrix).prod = diagonal D₀)
    (M : Matrix (Sum (Fin r) Unit) (Sum (Fin r) Unit) 𝕜) :
    ∃ (L L' : List (TransvectionStruct (Sum (Fin r) Unit) 𝕜)) (D : Sum (Fin r) Unit → 𝕜),
      (L.map toMatrix).prod * M * (L'.map toMatrix).prod = diagonal D := by
  rcases exists_isTwoBlockDiagonal_list_transvec_mul_mul_list_transvec2 M with ⟨L₁, L₁', hM⟩
  let M' := (L₁.map toMatrix).prod * M * (L₁'.map toMatrix).prod
  let M'' := toBlocks₁₁ M'
  rcases IH M'' with ⟨L₀, L₀', D₀, h₀⟩
  set c := M' (inr unit) (inr unit)
  refine'
    ⟨L₀.map (sumInl Unit) ++ L₁, L₁' ++ L₀'.map (sumInl Unit),
      Sum.elim D₀ fun _ => M' (inr unit) (inr unit), _⟩
  suffices (L₀.map (toMatrix ∘ sumInl Unit)).prod * M' * (L₀'.map (toMatrix ∘ sumInl Unit)).prod =
      diagonal (Sum.elim D₀ fun _ => c) by
    simpa [Matrix.mul_assoc]
  have : M' = fromBlocks M'' 0 0 (diagonal fun _ => c) := by
    -- porting note: simplified proof, because `congr` didn't work anymore
    rw [← fromBlocks_toBlocks M', hM.1, hM.2]
    rfl
  rw [this]
  simp [h₀]


theorem exists_list_transvec_mul_mul_list_transvec_eq_diagonal_aux2 (n : Type) [Fintype n] --???
    [DecidableEq n] (M : Matrix n n 𝕜) :
∃ (L L' : List (TransvectionStruct n 𝕜)) (D : n → 𝕜),
  (L.map toMatrix).prod
  *
  M
  *
  (L'.map toMatrix).prod
  =
  diagonal D
  := by
  induction' hn : Fintype.card n with r IH generalizing n M
  · refine' ⟨List.nil, List.nil, fun _ => 1, _⟩
    ext i j
    rw [Fintype.card_eq_zero_iff] at hn
    exact hn.elim' i
  · have e : n ≃ Sum (Fin r) Unit := by
      refine' Fintype.equivOfCardEq _
      rw [hn]
      rw [@Fintype.card_sum (Fin r) Unit _ _]
      simp
    apply reindex_exists_list_transvec_mul_mul_list_transvec_eq_diagonal2 M e
    apply
      exists_list_transvec_mul_mul_list_transvec_eq_diagonal_induction2 fun N =>
        IH (Fin r) N (by simp)





theorem exists_list_transvec_mul_mul_list_transvec_eq_diagonal2 (M : Matrix n n 𝕜) : --???
∃ (L L' : List (TransvectionStruct n 𝕜))
(D : n → 𝕜),
  (L.map toMatrix).prod
  *
  M
  *
  (L'.map toMatrix).prod
  =
  diagonal D
  := by
  have e : n ≃ Fin (Fintype.card n)
    := Fintype.equivOfCardEq (by simp)
  apply reindex_exists_list_transvec_mul_mul_list_transvec_eq_diagonal2 M e
  apply exists_list_transvec_mul_mul_list_transvec_eq_diagonal_aux2


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
    *
    (L.map toMatrix).prod
    *
    M
    *
    (
      (L'.map toMatrix).prod
      *
      (L'.reverse.map (toMatrix ∘ TransvectionStruct.inv)).prod
    )
    := by
      simp only [← h]
      simp only [Matrix.mul_assoc]
      done
  rw [changeTarget]
  rw [
  reverse_inv_prod_mul_prod, --???
  prod_mul_reverse_inv_prod, --???
  Matrix.one_mul,
  Matrix.mul_one
  ]
  done


end Pivot
