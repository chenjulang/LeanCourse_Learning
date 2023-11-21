import Mathlib.Data.Real.Sqrt
open Real

attribute [simp] div_left_inj' eq_neg_self_iff

lemma h1 : ¬1 + sqrt 5 = 1 + -sqrt 5
:= by
  norm_num

#print h1


macro "foo" : command =>
  `(#print $(Lean.mkCIdent (.num `Mathlib.Algebra.Group.Defs._auxLemma 2)))
foo
-- theorem Mathlib.Algebra.Group.Defs._auxLemma.2.{u_1} : ∀ {G : Type u_1} [inst : Add G] [inst_1 : IsLeftCancelAdd G]
--   (a : G) {b c : G}, (a + b = a + c) = (b = c) :=
-- fun {G} [Add G] [IsLeftCancelAdd G] a {b c} ↦ propext (add_right_inj a)
