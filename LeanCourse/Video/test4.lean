import Mathlib.LinearAlgebra.LinearIndependent
import Mathlib.LinearAlgebra.Matrix.Basis
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.Data.Real.Sqrt
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.GroupTheory.Perm.Sign

noncomputable section

  open Function Set Submodule Matrix
  open Equiv Equiv.Perm Finset Function

  open BigOperators Cardinal

  universe u' u

  variable {ι : Type u'} {ι' : Type*} {R : Type*} {K : Type*}
  variable {M : Type*} {M' M'' : Type*} {V : Type u} {V' : Type*}

  section Module

  variable {v : ι → M}
  variable [Semiring R] [AddCommMonoid M] [AddCommMonoid M'] [AddCommMonoid M'']
  variable [Module R M] [Module R M'] [Module R M'']
  variable {a b : R} {x y : M}
  variable (R) (v)

  theorem linearIndependent2_iff''_1
          : (∀ (s : Finset ι) (g : ι → R), ∑ i in s, g i • v i = 0 → ∀ i ∈ s, g i = 0)
          ↔
          ∀ (s : Finset ι) (g : ι → R),
            (∀ i ∉ s, g i = 0)
            →
            ∑ i in s, g i • v i = 0 → ∀ (i : ι), g i = 0
            := by
            classical -- 可以使用局部变量，比如下面的这个his
            constructor
            · intros H s g hg hv i
              by_cases his : i ∈ s
              · exact H s g hv i his
              · exact hg i his
              -- have h1 := (if his : i ∈ s then H s g hv i his else hg i his) -- 这里相当于分类讨论了
              -- exact h1
              done
            · intros H s g hg i hi

              -- have h3_ :(if i ∈ s then g i else 0) = 0
              --   := by
              --   by_cases i ∈ s
              --   · simp only [ite_eq_right_iff]
              --     intro i2
              --     set g2 :ι → R  := (fun j => if j ∈ s then g j else 0)
              --     refine' H s g2 _ _ _
              --     sorry

              have h3 :(if i ∈ s then g i else 0) = 0 --refine' H理解不了，就用exact H好了
                := by
                exact
                (H
                s
                (fun j1 => if j1 ∈ s then g j1 else 0)
                (fun i2 hj => if_neg hj)
                (by simp_rw [ite_smul, zero_smul, Finset.sum_extend_by_zero, hg])
                i)
                --done
              rw [← h3] -- convert h2 -- 一个意思
              exact (if_pos hi).symm

              done
            done

    end Module

end
