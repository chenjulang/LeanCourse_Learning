-- import Mathlib.Data.Matrix.Invertible
import Mathlib.LinearAlgebra.Matrix.Adjugate

namespace Matrix

universe u u' v

variable {l : Type*} {m : Type u} {n : Type u'} {α : Type v}

-- open Matrix BigOperators Equiv Equiv.Perm Finset

variable [Fintype n] [DecidableEq n] [CommRing α]
-- variable (A : Matrix n n α) (B : Matrix n n α)

noncomputable instance inv : Inv (Matrix n n α) :=
  ⟨fun A => Ring.inverse A.det • A.adjugate⟩

theorem inv_def (A : Matrix n n α) : A⁻¹ = Ring.inverse A.det • A.adjugate :=
  rfl

theorem mul_inv_rev (A B : Matrix n n α) : (A * B)⁻¹ = B⁻¹ * A⁻¹ := by
  simp only [inv_def]
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, det_mul, adjugate_mul_distrib,
    Ring.mul_inverse_rev]


end Matrix
