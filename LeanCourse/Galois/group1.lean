set_option checkBinderAnnotations false

-- namespace Mygroup4

--   variable (A : Type)

--   structure has_mul1 (A : Type) :=
--   (mul2 : A → A → A)

--   structure semigroup (A : Type) extends has_mul1 A :=
--   (mul3_assoc : ∀a b c, mul2 (mul2 a b) c = mul2 a (mul2 b c))

--   theorem mul_assoc2 (A : Type) (self : semigroup A) (a b c : A)
--   :has_mul1.mul2 self.tohas_mul1 (has_mul1.mul2 self.tohas_mul1 a b) c =
--     has_mul1.mul2 self.tohas_mul1 a (has_mul1.mul2 self.tohas_mul1 b c)
--   := by
--     apply semigroup.mul3_assoc


-- end Mygroup4


-- namespace Mygroup3

--   variable (A : Type)


--   -- @[inherit_doc] infixl:70 " * "   => HMul.hMul -- 因为这个写在了Lean4源码里，所以在VSCode里无法查看。
--   -- https://github.com/leanprover/lean4/blob/dcccfb73cb247e9478220375ab7de03f7c67e505/src/Init/Notation.lean#L277-L277

--   class semigroup (A : Type) extends Mul A where
--     mul3_assoc : ∀a b c : A, (a * b) * c = a * (b * c)

--   theorem mul_assoc2 (A : Type) [semigroup A] (a b c : A)
--   : (a * b) * c =
--     a * (b * c)
--   := by
--     apply semigroup.mul3_assoc


-- end Mygroup3



-- namespace Mygroup2

--   variable (A : Type)

--   class has_mul1 (A : Type) where
--     mul2 : A → A → A

--   infixl:70 " * "   => has_mul1.mul2

--   class semigroup (A : Type) extends has_mul1 A where
--     mul3_assoc : ∀a b c : A, (a * b) * c = a * (b * c)


--   theorem mul_assoc2 (A : Type) [semigroup A] (a b c : A)
--   : (a * b) * c =
--     a * (b * c)
--   := by
--     apply semigroup.mul3_assoc


-- end Mygroup2


namespace Mygroup1 -- 最适合入门的版本。

  variable (A : Type)

  class has_mul1 (A : Type) where
    mul2 : A → A → A
  class has_add (A : Type) :=
    (add : A → A → A)

  infixl:70 " * "   => has_mul1.mul2
  infixl:65 " + "   => has_add.add

  /-- 乘法_半群 = 乘法映射+乘法映射的结合律 -/
  class semigroup (A : Type) extends (has_mul1 A) where
    mul3_assoc : ∀a b c : A, (a * b) * c = a * (b * c)

  -- theorem mul.assoc2 (A : Type) [semigroup A] (a b c : A)
  -- : (a * b) * c =
  --   a * (b * c)
  -- := by
  --   apply semigroup.mul3_assoc
  theorem mul_assoc2 (A : Type) [semigroup A] (a b c : A)
  : (a * b) * c =
    a * (b * c)
  := by
    apply semigroup.mul3_assoc

  /-- 加法_半群 = 加法映射+加法映射的结合律 -/
  class add_semigroup (A : Type) extends (has_add A) :=
  (add_assoc : ∀a b c, add (add a b) c = add a (add b c))

  theorem add.assoc [s : add_semigroup A] (a b c : A) : a + b + c = a + (b + c) :=
  by apply add_semigroup.add_assoc


end Mygroup1
