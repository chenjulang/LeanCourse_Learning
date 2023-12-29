
-- 二次型 --如何引入的？

structure QuadraticForm (R : Type u) (M : Type v) [CommSemiring R] [AddCommMonoid M] [Module R M]
    where
  toFun : M → R
  toFun_smul : ∀ (a : R) (x : M), toFun (a • x) = a * a * toFun x
  exists_companion' : ∃ B : BilinForm R M, ∀ x y, toFun (x + y) = toFun x + toFun y + B x y
