import Mathlib.Algebra.Algebra.Opposite
-- 单文件示例
-- 参考lake-packages/mathlib/Mathlib/Data/Matrix/Basic.lean

universe u u' v w

def Matrix (m : Type u) (n : Type u') (α : Type v): Type max u u' v
:=
  m → n → α

  variable
  {l m n o : Type*}
  {m' : o → Type*}
  {n' : o → Type*}

  variable
  {R : Type*}
  {S : Type*}
  {α : Type v}
  {β : Type w}
  {γ : Type*}

  variable
  {M N : Matrix m n α}

namespace Matrix

theorem ext_iff: (∀ i j, M i j = N i j)  ↔  M = N
:= by
  -- 第一种写法：
  -- ⟨fun h => funext (fun i => funext <| h i)
  -- ,
  -- fun h => by simp [h]⟩
  constructor
  · intro h
    refine' funext _
    intro x
    have h1 := h x
    have h2 := funext h1
    exact h2 -- 这一步有点奇妙
  · intro h2
    intro h3
    intro h4
    rw [h2]

theorem ext: (∀ i j, M i j = N i j) → M = N
:= by
  exact ext_iff.mp

@[ext]
theorem ext' : (∀ i, M i = N i) → M = N
:= by
  -- 第一种写法：:=
  -- fun h => ext <| fun i => by simp[h]
  -- have h1 :=
  intro h1
  refine' funext _
  have h2 := fun x ↦ h1 x
  exact h2

-- ---//


def of : (m → n → α) ≃ Matrix m n α
:= by
  -- 第一种证明 :=
  -- Equiv.refl _
  ---
  simp only [Matrix]
  rfl

@[simp]
theorem of_apply (f : m → n → α) (i j) : (of f) i j = f i j
:= by
  -- 第一种证明:=
  -- rfl
  ---
  have h1 := (of f)
  have h2 := (of f) --用于对比
  simp only [Matrix] at h1 h2 -- 这里说明 (of f) 就等价于映射 m → n → α ，而目标右边f也是映射m → n → α
  rfl

@[simp]
theorem of_symm_apply (f : Matrix m n α) (i j) : of.symm f i j = f i j
:= by
  -- :=
  -- rfl
  ---
  have h1 := (of.symm f)
  -- have h2 := (of.symm f)
  have h2 := f
  simp only [Matrix] at h2 h1
  rfl


-- ---//
def map (M : Matrix m n α) (f : α → β) : Matrix m n β :=
  -- of fun i j => f (M i j)
  by
  intro x y
  have h1 := M x y
  have h2 := f h1
  exact h2
  done

@[simp]
theorem map_apply {M : Matrix m n α} {f : α → β} {i : m} {j : n} : (M.map f) i j = f (M i j) :=
  -- rfl
  by
  have map_M_f := map M f
  have M_i_j := M i j
  have left := map_M_f i j
  have right := f M_i_j -- 用于比较
  rfl

@[simp]
theorem map_id (M : Matrix m n α) : M.map id = M := by
  ext i j
  -- 中间是用了map_apply
  simp only [map_apply]
  simp only [id_eq]
  -- rfl

@[simp]
theorem map_map {M : Matrix m n α} {β γ : Type*} {f : α → β} {g : β → γ} : (M.map f).map g = M.map (g ∘ f) := by
  ext i j
  have h1 := map M f
  have h2 := map h1 g
  have h3 := g ∘ f
  have h4 := map M h3
  rfl
  -- simp only [map_apply]
  -- simp only [Function.comp_apply]
  -- rfl

-- theorem map_injective {f : α → β} (hf : Function.Injective f) : Function.Injective (fun (M : Matrix m n α) => (M.map f))
-- :=
--   fun _ _ h =>
--   ext fun i j => hf <| (ext_iff.mpr h) i j
-- #print map_injective₁
-- theorem Matrix.map_injective₁.{u_3, u_2, v, w} : ∀ {m : Type u_2} {n : Type u_3} {α : Type v} {β : Type w} {f : α → β},
--   Function.Injective f → Function.Injective fun M ↦ map M f :=
-- fun {m} {n} {α} {β} {f} hf x x_1 h ↦ ext fun i j ↦ hf (ext_iff.mpr h i j)
-- theorem map_injective₂ {f : α → β} (hf : Function.Injective f) : Function.Injective (fun (M : Matrix m n α) => (M.map f))
-- :=
--   by
--   intro M1 M2 Inj
--   simp only at Inj
--   simp only [map] at Inj
--   -- ext m1 n1
--   have h1 := (@ext_iff m n α)
--   specialize h1
--   · exact M1
--   · exact M2
--   -- apply symm at h1
--   apply h1.1
--   intro m1 n1
--   sorry
theorem map_injective {f : α → β} (hf : Function.Injective f) : Function.Injective (fun (M : Matrix m n α) => (M.map f))
:=
  by
  intros M1 M2 Inj
  -- hf (ext_iff.mpr h i j)
  -- ext_iff.mpr h i j   :   (fun M ↦ map M f) x i j = (fun M ↦ map M f) x_1 i j
  ext m1 n1
  have h1 :  (fun M ↦ map M f) M1 m1 n1 = (fun M ↦ map M f) M2 m1 n1
    := by
    have h2 := (ext_iff.mpr Inj)
    apply h2
    done
  have h3:= hf h1
  exact h3
  done -- 太牛了嘿嘿嘿，print大法 -!!!



/--矩阵的转置 The transpose of a matrix. -/
def transpose (M : Matrix m n α) : Matrix n m α :=
  -- of fun x y => M y x
  by
  intro n1 m1
  have h1 := M m1 n1
  exact h1
  done
  -- 这里究竟算是定义还是证明，在lean里面其实有一点玄妙 !!!

@[simp]
theorem transpose_apply (M : Matrix m n α) (j i) : transpose M i j = M j i :=
  -- rfl
  by
  have h1 := transpose M
  have h2 := h1 i j
  have h3 :=(M j i)
  set a1 := transpose M
  rfl
  done


@[inherit_doc] --从这个文件找transpose
scoped postfix:1024 "ᵀ" => Matrix.transpose --定义了符号表示转置



def conjTranspose [Star α] (M : Matrix m n α) : Matrix n m α :=
  M.transpose.map star
  -- by
  -- exact Mᵀ
-- def conjTranspose₂ [inst : Star α] (M : Matrix m n α) : Matrix n m α :=
--   -- M.transpose.map star
--   -- map Mᵀ star
--   by
--   have h1 := M.transpose
--   have h2 := h1.map inst.star
--   exact h2

-- -- 这里可以看到conjTranspose和conjTranspose₃的不同，后者根本不用到Star，所以定义的时候是很自由的，只要目的类符合即可，只是名字不一样
-- def conjTranspose₃ [inst : Star α] (M : Matrix m n α) : Matrix n m α :=
--   by
--   have h1 := M.transpose
--   exact h1


@[inherit_doc]
scoped postfix:1024 "ᴴ" => Matrix.conjTranspose

-- 矩阵的列
-- 这里Unit类似于void，不需要放参数
def col (w : m → α) : Matrix m Unit α :=
  -- of fun x _ => w x
  by
  intro m1 empty1
  apply w at m1
  exact m1
  done


@[simp]
theorem col_apply (w : m → α) (i j) : col w i j = w i :=
  -- rfl
  by
  set col1 := col w
  have left := col1 i j
  have right := w i
  rfl

--  矩阵的行
def row (v : n → α) : Matrix Unit n α :=
  -- of fun _ y => v y
  by
  intro empty1 n1
  apply v at n1
  exact n1
  done

@[simp]
theorem row_apply (v : n → α) (i j) : row v i j = v j :=
  -- rfl
  by
  set row1 := row v
  have left := row1 i j
  have right := v j
  rfl

-- Inhabited感觉像是一个默认值,先不管
-- instance inhabited [Inhabited α] : Inhabited (Matrix m n α) :=
--   instInhabitedForAll_1 _
-- #print inhabited

-- -- DecidableEq感觉说的是(Matrix m n α)的任意两个对象是可以判断是否相等的，先不管
-- instance decidableEq [DecidableEq α] [Fintype m] [Fintype n] : DecidableEq (Matrix m n α) :=
--   Fintype.decidablePiFintype
-- #print decidableEq

-- 加法实例
instance add [Add α] : Add (Matrix m n α) :=
  Pi.instAdd

-- #print Pi.instAdd

-- 加法结合律
instance addSemigroup [AddSemigroup α] : AddSemigroup (Matrix m n α) :=
  Pi.addSemigroup

-- 加法交换律
instance addCommSemigroup [AddCommSemigroup α] : AddCommSemigroup (Matrix m n α) :=
  Pi.addCommSemigroup

-- 零：也是一个同Matrix m n α类型的对象
instance zero [Zero α] : Zero (Matrix m n α) :=
  Pi.instZero

-- 加零，零加，都等于本身
instance addZeroClass [AddZeroClass α] : AddZeroClass (Matrix m n α) :=
  Pi.addZeroClass

--  0 + a = a + 0 = a 为什么还要重复写呢？不知道
instance addMonoid [AddMonoid α] : AddMonoid (Matrix m n α) :=
  Pi.addMonoid

-- 加法交换律 和   0 + a = a + 0 = a
instance addCommMonoid [AddCommMonoid α] : AddCommMonoid (Matrix m n α) :=
  Pi.addCommMonoid

-- 有对象-a : α
instance neg [Neg α] : Neg (Matrix m n α) :=
  Pi.instNeg

-- 有对象 a - b : α
instance sub [Sub α] : Sub (Matrix m n α) :=
  Pi.instSub

-- 满足0 + a = a + 0 = a
-- -a + a = 0
-- a - b = a + -b
instance addGroup [AddGroup α] : AddGroup (Matrix m n α) :=
  Pi.addGroup

-- 加法群(+)
-- 加法交换律
instance addCommGroup [AddCommGroup α] : AddCommGroup (Matrix m n α) :=
  Pi.addCommGroup

-- 唯一还是什么？不太清晰
instance unique [Unique α] : Unique (Matrix m n α) :=
  Pi.unique

-- (a b : α) → a = b 感觉意思是 某个特定的矩阵A是唯一的，若有另一个矩阵B，那也和A相等
instance subsingleton [Subsingleton α] : Subsingleton (Matrix m n α) :=
  instSubsingletonForAll

-- 至少有两个元素？0 ≠ 1？不太清晰
instance nonempty [Nonempty m] [Nonempty n] [Nontrivial α] : Nontrivial (Matrix m n α) :=
  Function.nontrivial

-- 具有标量乘法运算
instance smul [SMul R α] : SMul R (Matrix m n α) :=
  Pi.instSMul

-- 标量乘法的交换律 m • n • a = n • m • a
instance smulCommClass [SMul R α] [SMul S α] [SMulCommClass R S α] : SMulCommClass R S (Matrix m n α) :=
  Pi.smulCommClass

-- 标量乘法的结合律(x • y) • z = x • y • z
instance isScalarTower [SMul R S] [SMul R α] [SMul S α] [IsScalarTower R S α] : IsScalarTower R S (Matrix m n α) :=
  Pi.isScalarTower

-- 左右标量乘法是平等的
instance isCentralScalar [SMul R α] [SMul Rᵐᵒᵖ α] [IsCentralScalar R α] : IsCentralScalar R (Matrix m n α) :=
  Pi.isCentralScalar

-- 标量乘法(1 : α) • b = b
-- 这个不知道是什么运算*，满足 (x * y) • b = x • y • b
instance mulAction [Monoid R] [MulAction R α] : MulAction R (Matrix m n α) :=
  Pi.mulAction _

-- 标量乘法a • (0 : A) = 0
-- 加法和标量乘法的分配律a • (x + y) = a • x + a • y
instance distribMulAction [Monoid R] [AddMonoid α] [DistribMulAction R α] :
    DistribMulAction R (Matrix m n α) :=
  Pi.distribMulAction _

-- 满足以下条件，•是标量乘法，+是矩阵加法，*不知道是什么
-- (r + s) • x = r • x + s • x
-- (0 : R) • x = 0
-- a • (0 : A) = 0
-- a • (x + y) = a • x + a • y
-- (1 : α) • b = b
-- (x * y) • b = x • y • b
instance module [Semiring R] [AddCommMonoid α] [Module R α] : Module R (Matrix m n α) :=
  Pi.module _ _ _

section --/

@[simp]
theorem zero_apply [Zero α] (i : m) (j : n) : (0 : Matrix m n α) i j = 0 :=
  rfl --?

-- 矩阵相加，取项。
-- 等价于
-- 矩阵取项，相加
@[simp]
theorem add_apply [Add α] (A B : Matrix m n α) (i : m) (j : n) : (A + B) i j = (A i j) + (B i j) :=
  -- rfl
  by
  set AplusB := A + B
  have left := AplusB i j
  set Aij := A i j
  set Bij := B i j
  have right := Aij + Bij
  rfl

@[simp]
theorem smul_apply [SMul β α] (r : β) (A : Matrix m n α) (i : m) (j : n) : (r • A) i j = r • (A i j) :=
  -- rfl
  by
  set rmulA := (r • A)
  have l := rmulA i j
  set Aij := A i j
  have r := r • Aij
  rfl

@[simp]
theorem sub_apply [Sub α] (A B : Matrix m n α) (i : m) (j : n) : (A - B) i j = (A i j) - (B i j) :=
  -- rfl
  by
  rfl

@[simp]
theorem neg_apply [Neg α] (A : Matrix m n α) (i : m) (j : n) : (-A) i j = -(A i j) :=
  -- rfl
  by
  rfl

end --/


@[simp]
theorem of_zero [Zero α] : of (0 : m → n → α) = 0 :=
  -- rfl
  by
  set l := of (0 : m → n → α)
  rfl

@[simp]
theorem of_add_of [Add α] (f g : m → n → α) : of f + of g = of (f + g) :=
  -- rfl
  by
  set of_f := of f
  set of_g := of g
  set r := of (f+g)
  set l := of_f + of_g
  rfl

@[simp]
theorem of_sub_of [Sub α] (f g : m → n → α) : of f - of g = of (f - g) :=
  -- rfl
  by
  rfl

@[simp]
theorem neg_of [Neg α] (f : m → n → α) : -of f = of (-f) :=
  -- rfl
  by
  rfl

@[simp]
theorem smul_of [SMul R α] (r : R) (f : m → n → α) : r • of f = of (r • f) :=
  rfl

-- theorem wrong [Sub α] [Neg α] (f g : m → n → α) : ¬  (of f - of g = of (-f)) :=
--   by
--   set of_f := of f
--   set of_g := of g
--   set l := of_f - of_g
--   set r := of (-f)
--   refine Ne.intro ?h
--   intro


@[simp]
protected theorem map_zero [Zero α] [Zero β] (f : α → β) (h : f 0 = 0) : (0 : Matrix m n α).map f = 0
:= by
  ext
  simp only [map_apply]
  simp only [zero_apply]
  exact h
  done

protected theorem map_add [Add α] [Add β] (f : α → β) (hf : ∀ a₁ a₂, f (a₁ + a₂) = f a₁ + f a₂) (M N : Matrix m n α) : (M + N).map f = M.map f + N.map f
:=
-- ext fun _ _ => hf _ _
  by
  ext m1 n1
  -- apply?
  have h2 := hf (M m1 n1) (N m1 n1)
  simp only [map_apply, add_apply]
  exact h2
  done

protected theorem map_sub [Sub α] [Sub β] (f : α → β) (hf : ∀ a₁ a₂, f (a₁ - a₂) = f a₁ - f a₂) (M N : Matrix m n α) : (M - N).map f = M.map f - N.map f
:=
  ext fun _ _ => hf _ _

theorem map_smul [SMul R α] [SMul R β] (f : α → β) (r : R) (hf : ∀ a, f (r • a) = r • f a) (M : Matrix m n α) : (r • M).map f = r • M.map f
:=
  ext fun _ _ => hf _

theorem map_smul' [Mul α] [Mul β] (f : α → β) (r : α) (A : Matrix n n α) (hf : ∀ a₁ a₂, f (a₁ * a₂) = f a₁ * f a₂) : (r • A).map f = f r • A.map f
:=
  ext fun _ _ => hf _ _

-- MulOpposite.op是标量乘法的倒数吧
theorem map_op_smul' [Mul α] [Mul β] (f : α → β) (r : α) (A : Matrix n n α) (hf : ∀ a₁ a₂, f (a₁ * a₂) = f a₁ * f a₂) :
(MulOpposite.op r • A).map f = MulOpposite.op (f r) • A.map f
  :=
  ext fun _ _ => hf _ _

-- 左标量乘法是单射
theorem _root_.IsSMulRegular.matrix [SMul R S] {k : R} (hk : IsSMulRegular S k) : IsSMulRegular (Matrix m n S) k
:=
  IsSMulRegular.pi fun _ => IsSMulRegular.pi fun _ => hk

-- 好像也是说的左乘法是单射
theorem _root_.IsLeftRegular.matrix [Mul α] {k : α} (hk : IsLeftRegular k) : IsSMulRegular (Matrix m n α) k :=
  hk.isSMulRegular.matrix

instance subsingleton_of_empty_left [IsEmpty m] : Subsingleton (Matrix m n α) :=
  ⟨fun M N => by
    ext i
    exact isEmptyElim i⟩
#align matrix.subsingleton_of_empty_left Matrix.subsingleton_of_empty_left

instance subsingleton_of_empty_right [IsEmpty n] : Subsingleton (Matrix m n α) :=
  ⟨fun M N => by
    ext i j
    exact isEmptyElim j⟩
#align matrix.subsingleton_of_empty_right Matrix.subsingleton_of_empty_right

end Matrix
