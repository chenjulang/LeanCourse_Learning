import Mathlib.LinearAlgebra.Matrix.Transvection
-- 高斯：任意矩阵可化成对角形式 -- 线性方程组的人肉解







/-
Copyright (c) 2021 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import Mathlib.Data.Matrix.Basis
import Mathlib.Data.Matrix.DMatrix
import Mathlib.LinearAlgebra.Matrix.Determinant
import Mathlib.LinearAlgebra.Matrix.Reindex
import Mathlib.Tactic.FieldSimp

#align_import linear_algebra.matrix.transvection from "leanprover-community/mathlib"@"0e2aab2b0d521f060f62a14d2cf2e2c54e8491d6"

/-!
# Transvections

Transvections are matrices of the form `1 + StdBasisMatrix i j c`, where `StdBasisMatrix i j c`
is the basic matrix with a `c` at position `(i, j)`. Multiplying by such a transvection on the left
(resp. on the right) amounts to adding `c` times the `j`-th row to the `i`-th row
(resp `c` times the `i`-th column to the `j`-th column). Therefore, they are useful to present
algorithms operating on rows and columns.

Transvections are a special case of *elementary matrices* (according to most references, these also
contain the matrices exchanging rows, and the matrices multiplying a row by a constant).

We show that, over a field, any matrix can be written as `L * D * L'`, where `L` and `L'` are
products of transvections and `D` is diagonal. In other words, one can reduce a matrix to diagonal
form by operations on its rows and columns, a variant of Gauss' pivot algorithm.

## Main definitions and results

* `Transvection i j c` is the matrix equal to `1 + StdBasisMatrix i j c`.
* `TransvectionStruct n R` is a structure containing the data of `i, j, c` and a proof that
  `i ≠ j`. These are often easier to manipulate than straight matrices, especially in inductive
  arguments.

* `exists_list_transvec_mul_diagonal_mul_list_transvec` states that any matrix `M` over a field can
  be written in the form `t_1 * ... * t_k * D * t'_1 * ... * t'_l`, where `D` is diagonal and
  the `t_i`, `t'_j` are transvections.

* `diagonal_transvection_induction` shows that a property which is true for diagonal matrices and
  transvections, and invariant under product, is true for all matrices.
* `diagonal_transvection_induction_of_det_ne_zero` is the same statement over invertible matrices.

## Implementation details

The proof of the reduction results is done inductively on the size of the matrices, reducing an
`(r + 1) × (r + 1)` matrix to a matrix whose last row and column are zeroes, except possibly for
the last diagonal entry. This step is done as follows.

If all the coefficients on the last row and column are zero, there is nothing to do. Otherwise,
one can put a nonzero coefficient in the last diagonal entry by a row or column operation, and then
subtract this last diagonal entry from the other entries in the last row and column to make them
vanish.

This step is done in the type `Fin r ⊕ Unit`, where `Fin r` is useful to choose arbitrarily some
order in which we cancel the coefficients, and the sum structure is useful to use the formalism of
block matrices.

To proceed with the induction, we reindex our matrices to reduce to the above situation.
-/


universe u₁ u₂

namespace Matrix

open Matrix

variable (n p : Type*) (R : Type u₂) {𝕜 : Type*} [Field 𝕜]

variable [DecidableEq n] [DecidableEq p]

variable [CommRing R]

section Transvection

variable {R n} (i j : n)

/-- The transvection matrix `Transvection i j c` is equal to the identity plus `c` at position
`(i, j)`. Multiplying by it on the left (as in `Transvection i j c * M`) corresponds to adding
`c` times the `j`-th line of `M` to its `i`-th line. Multiplying by it on the right corresponds
to adding `c` times the `i`-th column to the `j`-th column. -/
def transvection2 (c : R) : Matrix n n R :=
  1 + Matrix.stdBasisMatrix i j c

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

instance [Nontrivial n] : Nonempty (TransvectionStruct n R) := by
  choose x y hxy using exists_pair_ne n
  exact ⟨⟨x, y, hxy, 0⟩⟩

namespace TransvectionStruct

variable {R n}

/-- Associating to a `transvection_struct` the corresponding transvection matrix. -/
def toMatrix2 (t : TransvectionStruct n R) : Matrix n n R :=
  transvection t.i t.j t.c

@[simp]
theorem toMatrix_mk2 (i j : n) (hij : i ≠ j) (c : R) :
    TransvectionStruct.toMatrix ⟨i, j, hij, c⟩ = transvection i j c :=
  rfl

@[simp]
protected theorem det2 [Fintype n] (t : TransvectionStruct n R) : det t.toMatrix = 1 :=
  det_transvection_of_ne _ _ t.hij _

@[simp]
theorem det_toMatrix_prod2 [Fintype n] (L : List (TransvectionStruct n 𝕜)) :
    det (L.map toMatrix).prod = 1 := by
  induction' L with t L IH
  · simp
  · simp [IH]

/-- The inverse of a `TransvectionStruct`, designed so that `t.inv.toMatrix` is the inverse of
`t.toMatrix`. -/
@[simps]
protected def inv2 (t : TransvectionStruct n R) : TransvectionStruct n R where
  i := t.i
  j := t.j
  hij := t.hij
  c := -t.c

section

variable [Fintype n]

end

open Sum

/-- Given a `TransvectionStruct` on `n`, define the corresponding `TransvectionStruct` on `n ⊕ p`
using the identity on `p`. -/
def sumInl2 (t : TransvectionStruct n R) : TransvectionStruct (Sum n p) R where
  i := inl t.i
  j := inl t.j
  hij := by simp [t.hij]
  c := t.c

variable {p}

variable [Fintype n] [Fintype p]

end TransvectionStruct

end Transvection


namespace Pivot

variable {R} {r : ℕ} (M : Matrix (Sum (Fin r) Unit) (Sum (Fin r) Unit) 𝕜)

open Sum Unit Fin TransvectionStruct

/-- A list of transvections such that multiplying on the left with these transvections will replace
the last column with zeroes. -/
def listTransvecCol2 : List (Matrix (Sum (Fin r) Unit) (Sum (Fin r) Unit) 𝕜) :=
  List.ofFn fun i : Fin r =>
    transvection (inl i) (inr unit) <| -M (inl i) (inr unit) / M (inr unit) (inr unit)

/-- A list of transvections such that multiplying on the right with these transvections will replace
the last row with zeroes. -/
def listTransvecRow2 : List (Matrix (Sum (Fin r) Unit) (Sum (Fin r) Unit) 𝕜) :=
  List.ofFn fun i : Fin r =>
    transvection (inr unit) (inl i) <| -M (inr unit) (inl i) / M (inr unit) (inr unit)

variable {n p} [Fintype n] [Fintype p]

/-- Any matrix can be written as the product of transvections, a diagonal matrix, and
transvections.-/
theorem exists_list_transvec_mul_diagonal_mul_list_transvec2 (M : Matrix n n 𝕜) :
    ∃ (L L' : List (TransvectionStruct n 𝕜)) (D : n → 𝕜),
      M = (L.map toMatrix).prod * diagonal D * (L'.map toMatrix).prod := by
  rcases exists_list_transvec_mul_mul_list_transvec_eq_diagonal M with ⟨L, L', D, h⟩
  refine' ⟨L.reverse.map TransvectionStruct.inv, L'.reverse.map TransvectionStruct.inv, D, _⟩
  suffices
    M =
      (L.reverse.map (toMatrix ∘ TransvectionStruct.inv)).prod * (L.map toMatrix).prod * M *
        ((L'.map toMatrix).prod * (L'.reverse.map (toMatrix ∘ TransvectionStruct.inv)).prod)
    by simpa [← h, Matrix.mul_assoc]
  rw [reverse_inv_prod_mul_prod, prod_mul_reverse_inv_prod, Matrix.one_mul, Matrix.mul_one]

end Pivot
