import Mathlib.Tactic.Core

set_option checkBinderAnnotations false
set_option autoImplicit true

-- 代码只是一种具象，你大可以不用深究代码的逻辑，因为语言规则本身是人为规定的，你抽象的连贯的思想才是关键且唯一重要的。




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
    (mul2 : A → A → A)
  class has_add (A : Type) :=
    (add : A → A → A)
  class has_one (A : Type) where
    (one : A)
  class has_zero (A : Type) :=
    (zero : A)
  class has_inv  (A : Type) :=
    (inv : A → A)
  class has_neg  (A : Type) :=
   (neg : A → A)

  infixl:70 " * "   => has_mul1.mul2
  infixl:65 " + "   => has_add.add
  postfix:max "⁻¹"  => has_inv.inv
  postfix:75 "-"    => has_neg.neg
  -- notation 1   := !has_one.one
  -- notation 0   := !has_zero.zero

  section mul_semmi_group

    /-- 乘法_半群 = 乘法映射+乘法映射的结合律 -/
    class semigroup (A : Type) extends (has_mul1 A) where
      mul3_assoc : ∀a b c : A, (a * b) * c = a * (b * c)

    -- theorem mul.assoc2 (A : Type) [semigroup A] (a b c : A)
    -- : (a * b) * c =
    --   a * (b * c)
    -- := by
    --   apply semigroup.mul3_assoc
    theorem mul_assoc (A : Type) [semigroup A] (a b c : A)
    : (a * b) * c =
      a * (b * c)
    := by
      apply semigroup.mul3_assoc

    class comm_semigroup (A : Type) extends semigroup A where
      (mul_comm : ∀a b:A , a * b = b * a)

    theorem mul.comm [s : comm_semigroup A] (a b : A) : a * b = b * a :=
    by apply comm_semigroup.mul_comm
    theorem mul.left_comm [s : comm_semigroup A] (a b c : A) : a * (b * c) = b * (a * c) :=
    by
      rw [comm_semigroup.mul_comm]
      rw [mul_assoc]
      rw [comm_semigroup.mul_comm c a]
      done
    theorem mul.right_comm [s : comm_semigroup A] (a b c : A) : (a * b) * c = (a * c) * b :=
    by
      rw [mul_assoc]
      rw [comm_semigroup.mul_comm b c]
      rw [← mul_assoc]
      done

    class left_cancel_semigroup (A : Type) extends semigroup A :=
      (mul_left_cancel : ∀a b c:A,  a * b = a * c → b = c)

    theorem mul.left_cancel [s : left_cancel_semigroup A] {a b c : A} :
      a * b = a * c → b = c :=
    by apply left_cancel_semigroup.mul_left_cancel

    class right_cancel_semigroup (A : Type) extends semigroup A :=
      (mul_right_cancel : ∀a b c:A, a * b = c * b → a = c)

    theorem mul.right_cancel [s : right_cancel_semigroup A] {a b c : A} :
      a * b = c * b → a = c :=
    by apply right_cancel_semigroup.mul_right_cancel

  end mul_semmi_group



  section add_semmi_group

    /-- 加法_半群 = 加法映射+加法映射的结合律 -/
    class add_semigroup (A : Type) extends (has_add A) :=
    (add_assoc : ∀a b c, add (add a b) c = add a (add b c))

    @[simp]
    theorem add.assoc [s : add_semigroup A] (a b c : A) : a + b + c = a + (b + c) :=
    by apply add_semigroup.add_assoc

    class add_comm_semigroup (A : Type) extends add_semigroup A :=
    (add_comm : ∀a b, add a b = add b a)

    @[simp]
    theorem add.comm [s : add_comm_semigroup A] (a b : A) : a + b = b + a :=
    by apply add_comm_semigroup.add_comm
    @[simp]
    theorem add.left_comm [s : add_comm_semigroup A] (a b c : A) :
      a + (b + c) = b + (a + c) :=
    by
      rw [add.comm]
      rw [add.assoc]
      rw [add.comm A a c]
    @[simp]
    theorem add.right_comm [s : add_comm_semigroup A] (a b c : A) : (a + b) + c = (a + c) + b :=
    by
      simp only [comm, left_comm]

    class add_left_cancel_semigroup (A : Type) extends add_semigroup A :=
      (add_left_cancel : ∀a b c, add a b = add a c → b = c)

    @[simp]
    theorem add.left_cancel [s : add_left_cancel_semigroup A] {a b c : A} :
      a + b = a + c → b = c :=
    by apply add_left_cancel_semigroup.add_left_cancel

    class add_right_cancel_semigroup (A : Type) extends add_semigroup A :=
      (add_right_cancel : ∀a b c, add a b = add c b → a = c)

    theorem add.right_cancel [s : add_right_cancel_semigroup A] {a b c : A} :
      a + b = c + b → a = c :=
    by apply add_right_cancel_semigroup.add_right_cancel

  end add_semmi_group



end Mygroup1
