import Mathlib.LinearAlgebra.Basic
import Mathlib.GroupTheory.QuotientGroup
import Mathlib.GroupTheory.Subgroup.Basic
import Mathlib.GroupTheory.Coset

open Subgroup QuotientGroup

namespace my_quotient_group

  variable {A B C : Type}
  variable [Group A] (H : Set A) (H : Subgroup A) [Normal H]

  def lcoset_setoid2: Setoid A
  := by
    apply Setoid.mk
    · exact leftCosetEquivalence_rel H
    done
    -- Setoid.mk (lcoset_equiv H) (equivalence_lcoset_equiv H)

  -- def leftRel2 : Setoid A :=
  -- MulAction.orbitRel H.op A

  def quotient := Quot (lcoset_setoid2 H).1

end my_quotient_group
