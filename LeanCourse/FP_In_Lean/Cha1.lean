#eval 1 - 2 -- 0
#eval (1 - 2 : Int) -- -1


structure Point where
  x : Float
  y : Float
deriving Repr -- 最后一行 deriving Repr ，要求 Lean 生成代码来显示 Point 类型的值。


structure Point3D where
  x : Float
  y : Float
  z : Float
deriving Repr

#check Point.mk 1.5 2.8 -- 默认情况下，名为 S 的结构的构造函数名为 S.mk 。这里， S 是命名空间限定符， mk 是构造函数本身的名称。也可以直接应用构造函数，而不是使用大括号初始化语法。

def Point.modifyBoth (f : Float → Float) (p : Point) : Point :=
  { x := f p.x, y := f p.y }
-- 函数 Point.modifyBoth （即 Point 命名空间中定义的 modifyBoth ）将函数应用于 Point 中的两个字段：
-- 即使 Point 参数位于函数参数之后，它也可以与点表示法一起使用：


def isZero (n : Nat) : Bool :=
  match n with
  | Nat.zero => true
  | Nat.succ k => false


def depth (p : Point3D) : Float :=
  match p with
  | { x:= h, y := w, z := d } => d


def even (n : Nat) : Bool :=
  match n with
  | Nat.zero => true
  | Nat.succ k => not (even k) -- 接受新参数k

def even2 (n : Nat) : Bool :=
  match n with
  | Nat.zero => true
  | Nat.succ k => not (even2 n) -- 不接受原参数n


def div (n : Nat) (k : Nat) : Nat :=
  if n < k then
    0
  else Nat.succ (div (n - k) k)

structure PPoint (α : Type) where
  x : α
  y : α
deriving Repr

def replaceX (α : Type) (point : PPoint α) (newX : α) : PPoint α :=
{ point with x := newX } --* with 的使用

inductive Sign where
  | pos
  | neg

def posOrNegThree (s : Sign) : match s with | Sign.pos => Nat | Sign.neg => Int --* 这类型是个函数的骨架！！
:=
  match s with
  | Sign.pos => (3 : Nat)
  | Sign.neg => (-3 : Int)


namespace TestList

  inductive List (α : Type) where --* List的定义
    | nil : List α
    | cons : α → List α → List α

  def explicitPrimesUnder10 : List Nat := --* 过于离奇又简单的使用
    List.cons 2 (List.cons 3 (List.cons 5 (List.cons 7 List.nil)))

  #eval explicitPrimesUnder10 -- 无法打印怎么办

  def length (α : Type) (xs : List α) : Nat :=
    match xs with
    | List.nil => Nat.zero
    | List.cons y ys => Nat.succ (length α ys) --* List的长度List.length的定义
end TestList

def length2 (α : Type) (xs : List α) : Nat := --* List.length的直观定义
  match xs with
  | [] => 0
  | y :: ys => Nat.succ (length2 α ys)

namespace TestList

  inductive Option (α : Type) : Type where
    | none : Option α
    | some (val : α) : Option α



end TestList

def List.head2? {α : Type} (xs : List α) : Option α :=
  match xs with
  | [] => none
  | y :: _ => some y

def PetName : Type := String ⊕ String

def animals : List PetName :=
  [Sum.inl "Spot", Sum.inr "Tiger", Sum.inl "Fifi", Sum.inl "Rex", Sum.inr "Floof"]

def howManyDogs (pets : List PetName) : Nat :=
  match pets with
  | [] => 0
  | Sum.inl _ :: morePets => howManyDogs morePets + 1 --* Sum的使用
  | Sum.inr _ :: morePets => howManyDogs morePets

#eval howManyDogs animals


inductive ArithExpr (ann : Type) : Type where
  | int : ann → Int → ArithExpr ann
  | plus : ann → ArithExpr ann → ArithExpr ann → ArithExpr ann
  | minus : ann → ArithExpr ann → ArithExpr ann → ArithExpr ann
  | times : ann → ArithExpr ann → ArithExpr ann → ArithExpr ann

#check  ArithExpr Unit --* Unit的使用

inductive MyType : Type where
  | ctor : (MyType → Int) → MyType -- 如果构造函数的参数是一个将定义的数据类型作为参数的函数，则该定义将被拒绝

inductive MyType2 (α : Type) : Type where
  | ctor : α → MyType2 α

def ofFive : MyType2 := ctor 5


-- todo 1.7
