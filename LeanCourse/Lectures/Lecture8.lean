import LeanCourse.Common
open BigOperators Finset Function Real
noncomputable section
set_option linter.unusedVariables false
local macro_rules | `($x ^ $y) => `(HPow.hPow $x $y)
variable {n : ℕ}


/- # Today: Structures and Classes

We cover chapter 6 from Mathematics in Lean. -/

/-
Last time we discussed natural numbers, induction, and casts.
-/

/- Warning: sometimes you have to use `clear` to get rid of hypotheses when doing induction. -/
example (hn : 2 ∣ n) :
    (∑ i in range (n + 1), i : ℚ) = n * (n + 1) / 2 := by
  clear hn
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, ih]
    push_cast
    ring



/- New homework assignment will be posted this afternoon. -/

/-
# Structures and classes

Learning about structures is the next step towards doing sophisticated mathematics.

Structures are used to build data and properties together.
For example in the structure below `Point` bundles three coordinates together.
-/

@[ext] structure Point where
  x : ℝ
  y : ℝ
  z : ℝ

#check Point




section

/- Given a point, we get access to its coordinates / projections. -/
variable (a : Point)
#check (Point)
#check a.x
#check a.y
#check a.z
#check Point.x a

example : a.x = Point.x a := rfl

end





/- We can prove that two points are equal using the `ext` tactic. -/

example (a b : Point) (hx : a.x = b.x) (hy : a.y = b.y) (hz : a.z = b.z) :
    a = b := by
  ext
  all_goals assumption

example (a b : Point) (hx : a.x = b.x) (hy : a.y = b.y) (hz : a.z = b.z) :
  a = b := by ext <;> assumption

#check Point.ext
#check Point.ext_iff

/- There are multiple ways to define a point (or more generally an instance of a structure).

Tip: if you write `_` for a Point, a lightbulb 💡 will appear.
Clicking it will give you the skeleton -/]

def myPoint1 : Point where
  x := 1
  y := 2
  z := 3

def myPoint2 :=
  { x := 1, y := 2, z := 3 : Point }

def myPoint3 : Point :=
 id {
   x := 1
   y := 2
   z := 3
 }

def myPoint4 : Point := ⟨1, 2, 3⟩

def myPoint5 := Point.mk 1 2 3



namespace Point

/- We can define operations on points, like addition. -/

def add (a b : Point) : Point where
  x := a.x + b.x
  y := a.y + b.y
  z := a.z + b.z

def add' : Point → Point → Point :=
fun ⟨ux, uy, uz⟩ ⟨vx, vy, vz⟩ ↦ ⟨ux + vx, uy + vy, uz + vz⟩

def add'' : Point → Point → Point
  | ⟨ux, uy, uz⟩, ⟨vx, vy, vz⟩ => ⟨ux + vx, uy + vy, uz + vz⟩

/- We define these operations in `namespace Point`. This means that if this namespace is open
we can write `add p q`, but if the namespace isn't open, we have to write `Point.add p q`.
In either case, we can use the *projection notation*, `p.add q` where `p q : Point`.
Lean knows that we mean the function `Point.add`, since the type of `p` is `Point`. -/

#check add myPoint1 myPoint2
#check myPoint1.add myPoint2

end Point

#check Point.add myPoint1 myPoint2
#check myPoint1.add myPoint2

#check Add
open Point

structure Something where
  add : ℕ → ℕ → ℕ

open Something

-- Lean can figure out overloaded names.
#check add myPoint1 myPoint2
#check fun x : Something ↦ add x (1 : ℕ) 2
-- #check add (3 : ℂ)


namespace Point

/- We can prove properties about points. `protected` in the line below means that
even in the namespace `Point` we still have to write `Point.add_commutative` -/

protected lemma add_comm (a b : Point) :
  add a b = add b a := by simp [add, add_comm]

#check Point.add_comm

/- We can also state that we want to use the `+` notation here.
In that case, we have to write lemmas stating how `+` computes. -/

instance : Add Point := ⟨add⟩

@[simp]
lemma add_x (a b : Point) : (a + b).x = a.x + b.x := by rfl
@[simp]
lemma add_y (a b : Point) : (a + b).y = a.y + b.y := by rfl
@[simp]
lemma add_z (a b : Point) : (a + b).z = a.z + b.z := by rfl

example (a b : Point) : a + b = b + a := by
  ext
  <;> simp [add_comm]

end Point





/- We can bundle properties in structures -/

structure PosPoint where
  x : ℝ
  y : ℝ
  z : ℝ
  x_pos : 0 < x
  y_pos : 0 < y
  z_pos : 0 < z

-- 下面这个def定义由部分属性也要证明的，因为需要合理的定义（即well-founded），需要符合PosPoint的Structure的6条要求
def PointPoint.add (a b : PosPoint) : PosPoint :=
{ x := a.x + b.x
  y := a.y + b.y
  z := a.z + b.z
  x_pos := by apply add_pos; exact a.x_pos; exact b.x_pos
  y_pos := by linarith [a.y_pos, b.y_pos]
  z_pos := by linarith [a.z_pos, b.z_pos] }

/- Going from `Point` to `PosPoint` has code duplication.
We don't want this when defining monoids, groups, rings, fields. -/

structure PosPoint' extends Point where
  x_pos : 0 < x
  y_pos : 0 < y
  z_pos : 0 < z

#check PosPoint'.toPoint -- 这个应该是固定写法“to”+“Point”

def PointPoint'.add (a b : PosPoint') : PosPoint' :=
--这里又是一个大括号的特殊定义方法
{
  a.toPoint + b.toPoint
  with
  x_pos := by
    dsimp; linarith [a.x_pos, b.x_pos]
  y_pos := by
    dsimp; linarith [a.y_pos, b.y_pos]
  z_pos := by
    dsimp; linarith [a.z_pos, b.z_pos]
}

/- We could also define a type like this using a subtype. It's notation is very similar to sets,
but written as `{x : α // p x}` instead of `{x : α | p x}`. -/

def PosReal : Type :=
  { x : ℝ // x > 0 }

def set_of_positive_reals : Set ℝ :=
  { x : ℝ | x > 0 }

/- However, that doesn't give you nice projections names (automatically).
And it gets ugly when you have more than 2 projections. -/

example (x : PosReal) : x.1 > 0 := x.2 -- 这里的PosReal指的是最近的PosReal

def PosPoint'' : Type :=
  { x : ℝ × (ℝ × ℝ) // x.1 > 0 ∧ x.2.1 > 0 ∧ x.2.2 > 0 }





/- Structures can have parameters -/

@[ext] structure Triple (α : Type*) where
  x : α
  y : α
  z : α

#check Triple.mk 1 2 3

#check Triple.mk cos sin tan




/- # A note on universes

Lean has a hierarchy of universes. -/

#check ℝ
#check Type 0 -- 和 Type 一样
#check Type 1
#check Type 2

/- You can also work in a variable universe. -/

universe u v
#check Type u
#check Type (v + 3)
#check Type (max u v)
#check fun (α : Type u) (β : Type v) ↦ α → β --？
-- #check Type (u + v) -- the operations on universes are very limited.

/-
* `Type*` means `Type u` for some new variable `u`
* `Type _` means an arbitary universe -/

#check Type*
#check Type _


example : Type (u + 3) = Type _ := rfl
-- example : Type (u + 3) = Type* := rfl -- error

/-
* `Prop` is a bottom universe below `Type`.
* `Sort` is used to write "`Prop` or `Type`" -/

#check Prop

example : Sort 0 = Prop := by rfl
example : Sort 1 = Type := by rfl -- Type的别称是(Type 0)
example : Sort 2 = Type 1 := rfl
example : Sort (u + 1) = Type u := rfl
example : Sort _ = Type u := rfl
-- example : Sort* = Type u := rfl -- error



/- # Equiv

An important structure is equivalences between two types,
i.e. a bijection (with a chosen inverse).
This exists in the library as `Equiv α β` or `α ≃ β`.  -/

#check Equiv

example {α β : Type*} (e : α ≃ β) (x : α)
: β
:= e.toFun x
example {α β : Type*} (e : α ≃ β) (x : α)
: β
:= e x

example {α β : Type*} (e : α ≃ β)
: β ≃ α
:= e.symm
example {α β : Type*} (e : α ≃ β) (y : β)
: α
:= e.symm.toFun y





/- # Abelian groups
Let's define abelians group in Lean. -/

structure AbelianGroup where -- 太美了
  G : Type* -- 这是等待被推断的类型，或者直接定义的
  add (x : G) (y : G) : G
  comm (x y : G) : add x y = add y x
  assoc (x y z : G) : add (add x y) z = add x (add y z)
  zero : G
  add_zero : ∀ x : G, add x zero = x
  neg : G → G
  add_neg : ∀ x : G, add x (neg x) = zero

def IntGroup : AbelianGroup where
  G := ℤ
  add := fun a b ↦ a + b
  comm := add_comm
  assoc := add_assoc
  zero := 0
  add_zero := by simp
  neg := fun a ↦ -a
  add_neg := by exact fun x ↦ Int.add_right_neg x -- exact?

--下面这行这里AbelianGroup.zero_add完全可以改成其他名字foo1，写成这样是为了后面方便调用，或者其他抽象的使用
lemma AbelianGroup.zero_add (g : AbelianGroup) (x : g.G)
: g.add g.zero x = x
:= by
  rw [g.comm, g.add_zero] -- 这里一切都用自己定义的一些映射自己证明了




/-
Issues with this approach:
* we want a notation for `AbelianGroup.add` and `AbelianGroup.neg`.
* we want this to be automatically attached to certain concrete type such as `ℕ`, `ℝ`...
* we want a way to automatically build new examples from old ones

Using `class` instead of `structure` tells Lean to create a database of "instances of this class".
The `instance` command allows to add entries to this database.
-/

-- class AbelianGroup' (G : Type*) where -- 对比structure发现G的写的位置不同了，写在了第一行
--   add (x : G) (y : G) : G
--   comm (x y : G) : add x y = add y x
--   assoc (x y z : G) : add (add x y) z = add x (add y z)
--   zero : G
--   add_zero : ∀ x : G, add x zero = x
--   neg : G → G
--   add_neg : ∀ x : G, add x (neg x) = zero

-- 这里我故意将G改成H，说明add的第一个参数x：H中的H其实只是一个形参，可以是任意的类型比如G × G'
class AbelianGroup' (H : Type*) where
  add (x : H) (y : H) : H
  comm (x y : H) : add x y = add y x
  assoc (x y z : H) : add (add x y) z = add x (add y z)
  zero : H
  add_zero : ∀ x : H, add x zero = x
  neg : H → H
  add_neg : ∀ x : H, add x (neg x) = zero

instance : AbelianGroup' ℤ where
  add := fun a b ↦ a + b -- 这里a的类型能推断出Z是因为上面这行AbelianGroup' ℤ，在实例化时填进去了class AbelianGroup' (H : Type*)里的H : Type*这个坑
  -- ，自然从class AbelianGroup'来看，后面的所有H就正是Z
  comm := add_comm
  assoc := add_assoc
  zero := 0
  add_zero := by simp
  neg := fun a ↦ -a
  add_neg := by exact fun x ↦ Int.add_right_neg x

#eval AbelianGroup'.add (2 : ℤ) 5 -- 然后这里就开始找instance，找到了上面这个instance : AbelianGroup' ℤ,
-- 第一个参数是(2 : ℤ)，正好符号instance : AbelianGroup' ℤ 的add方法的类型

infixl:70 " +' " => AbelianGroup'.add -- infixl指的是在两个对象A，B中间的运算符，实际效果相当于AbelianGroup'.add A B

#eval (-2) +' 5 -- 相当于 AbelianGroup'.add （-2） 5 所以又和AbelianGroup'.add (2 : ℤ) 5的推断思路一样了

notation " 𝟘 " => AbelianGroup'.zero

prefix:max "-'" => AbelianGroup'.neg

/- When you assume you have an object in a certain class, you put them in square brackets
(and giving a name to them is optional).
Such arguments are called instance-implicit arguments,
Lean will provide them automatically by searching the corresponding database.
-/

#check AbelianGroup'.add

instance AbelianGroup'.prod
(G G' : Type*)
[instance1 : AbelianGroup' G]
[instance2 : AbelianGroup' G']
:AbelianGroup' (G × G') where
  add := fun a b ↦ (a.1 +' b.1, a.2 +' b.2) -- 这里a推断为a : G × G'，是因为上面一行写的AbelianGroup' (G × G')
  -- 一定要加这两行：
  -- [instance1 : AbelianGroup' G]
  -- [instance2 : AbelianGroup' G']
  -- 的原因估计是fun a b ↦ (a.1 +' b.1, a.2 +' b.2)中拆出第一项的时候默认需要，该抽象项AbelianGroup' G需要找到确切的instance
  -- [instance1 : AbelianGroup' G]等于告知了lean的确存在这样的instance，这一切都可以在“瞒骗”的过程中继续下去定义这个add的映射
  comm := by
    intros x y
    simp only [Prod.mk.injEq]
    constructor
    · exact comm x.1 y.1 -- 在classclass AbelianGroup' (H : Type*) 里面定义的comm是可以直接用的
    · exact comm x.2 y.2
  assoc := by
    intros x y z
    simp only [Prod.mk.injEq]
    constructor
    · exact assoc x.1 y.1 z.1
    · exact assoc x.2 y.2 z.2
  zero := (𝟘, 𝟘)
  add_zero := by
    intros x
    simp only [Prod.mk.injEq]
    have h1 : x = (x.1,x.2) := by simp only [Prod.mk.eta]
    nth_rewrite 3 [h1]
    simp only [Prod.mk.injEq]
    constructor
    · exact add_zero x.1
    · exact add_zero x.2
  neg := fun a ↦ (-' a.1, -' a.2)
  add_neg := by
    intros x
    simp only [Prod.mk.injEq]
    constructor
    · exact add_neg x.1
    · exact add_neg x.2

set_option trace.Meta.synthInstance true in -- lean的思考过程都可以看出来，这就是元编程，有几乎最高的编程权限
#eval ((2, 3) : ℤ × ℤ) +' (4, 5)

#check (3 : ℝ) * 5




/- In mathlib, there are two notions of abelian groups,
one written using `(*,1,⁻¹)` and one using `(+, 0, -)`. -/

#check CommGroup
#check AddCommGroup


/- To explain this distinction, consider monoids (groups without inverses).
`(ℝ, +, 0)` and `(ℝ, *, 1)` are both monoids, and we want to have a distinction in notation and
lemma names of these two structures. -/

example : Monoid ℝ := by
  exact instMonoidReal
--  exact inferInstance
example : AddMonoid ℝ := by
  exact instAddMonoidReal
  -- infer_instance
example (x : ℝ) : x + 0 = x :=
  add_zero x
example (x : ℝ) : x * 1 = x :=
  mul_one x

#check Monoid
#check AddMonoid









/- ## Exercises -/

/- 1. Define the structure of "strict bipointed types", i.e. a type together with 2 unequal points
`x₀ ≠ x₁` in it.
Then state and prove the lemma that for any object in this class we have `∀ z, z ≠ x₀ ∨ z ≠ x₁.` -/



/- 2. Define scalar multiplication of a real number and a `Point`.
Also define scalar multiplication of a positive real number and a `PosPoint`. -/



/- 3. Define Pythagorean triples, i.e. triples `a b c : ℕ` with `a^2 + b^2 = c^2`.
Give an example of a Pythagorean triple, and show that multiplying a Pythagorean triple by a
constant gives another Pythagorean triple. -/



/- 4. Prove that triples of equivalent types are equivalent. -/

example (α β : Type*) (e : α ≃ β) : Triple α ≃ Triple β := sorry


/- 5. Show that if `G` is an abelian group then triples from elements of `G` is an abelian group. -/

example (G : Type*) [AbelianGroup' G] : AbelianGroup' (Triple G) := sorry














/- ## Coercions

You can specify *coercions* to say that an element of one type can be silently coerced to an element
of another type. We've already seen the coercions
`ℕ → ℤ → ℚ → ℝ → ℂ`
for numbers.
-/

recall PosReal := {x : ℝ // x > 0} -- 正实数

instance
: Coe PosReal Real
:= ⟨fun x ↦ x.1⟩ -- 大概意思就是将PosReal的第一项x : R直接强制转成R使用
--?总之缺了这一行下面#check fun (x : PosReal) ↦ (x : ℂ)会强制转换报错
-- instance : Coe PosReal Real where
--   coe := fun
--     | .mk val property =>  {
--       cauchy := _
--     }

def diff (x y : PosReal) : ℝ := x - y

#check fun (x : PosReal) ↦ (x : ℂ)




/-
* We use `CoeSort` to coerce to `Type _` (or `Sort _`)
* We use `CoeFun` to coerce to functions.
-/
structure PointedType where
  carrier : Type*
  pt : carrier -- pt < carrier < Type*

instance
: CoeSort PointedType Type*
:= ⟨fun α ↦ α.carrier⟩ -- 因为PointedType的第一项正好是carrier : Type*，能墙转成Type*

structure PointedFunction (X Y : PointedType) where
  toFun : X → Y
  toFun_pt : toFun X.pt = Y.pt

#check PointedFunction.toFun

infix:50 " →. " => PointedFunction -- A →. B 相当于 PointedFunction A B

instance {X Y : PointedType}
: CoeFun (X →. Y) (fun _ ↦ X → Y)
:= ⟨fun e ↦ e.toFun⟩ -- 因为X →. Y类的toFun刚好就是toFun : X → Y，可以强转成(fun _ ↦ X → Y)，即 X → Y

-- these two are hints to the pretty printer to print these operations a bit nicer. --？
attribute [pp_dot] PointedType.pt --？
attribute [coe] PointedFunction.toFun --？

namespace PointedFunction

variable {X Y Z : PointedType}

@[simp] lemma coe_pt (f : X →. Y)
: f X.pt = Y.pt
:= by
  have h1 := f.toFun_pt --?
  exact h1

lemma comp (g : Y →. Z) (f : X →. Y)
: X →. Z
:= by
 refine { toFun := ?toFun, toFun_pt := ?toFun_pt }
 · exact fun a ↦ Z.pt
 · exact rfl
-- { toFun := g ∘ f
--   toFun_pt := by sorry }

end PointedFunction
