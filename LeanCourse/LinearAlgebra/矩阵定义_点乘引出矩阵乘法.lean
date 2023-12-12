-- import Mathlib.Algebra.Algebra.Opposite
-- import Mathlib.Algebra.Algebra.Pi
-- import Mathlib.Algebra.Module.LinearMap
-- import Mathlib.Algebra.Module.Pi
-- import Mathlib.Algebra.Star.BigOperators
-- import Mathlib.Algebra.Star.Module
-- import Mathlib.Algebra.Star.Pi
-- import Mathlib.Algebra.BigOperators.Pi
-- import Mathlib.Algebra.BigOperators.Ring
-- import Mathlib.Algebra.BigOperators.RingEquiv
-- import Mathlib.Data.Fintype.BigOperators
-- -- 单文件示例
-- -- 参考lake-packages/mathlib/Mathlib/Data/Matrix/Basic.lean

-- universe u u' v w

-- open BigOperators


-- def Matrix (m : Type u) (n : Type u') (α : Type v): Type max u u' v
-- :=
--   m → n → α

--   variable
--   {l m n o : Type*}
--   {m' : o → Type*}
--   {n' : o → Type*}

--   variable
--   {R : Type*}
--   {S : Type*}
--   {α : Type v}
--   {β : Type w}
--   {γ : Type*}

--   variable
--   {M N : Matrix m n α}

-- namespace Matrix

-- theorem ext_iff: (∀ i j, M i j = N i j)  ↔  M = N
-- := by
--   -- 第一种写法：
--   -- ⟨fun h => funext (fun i => funext <| h i)
--   -- ,
--   -- fun h => by simp [h]⟩
--   constructor
--   · intro h
--     refine' funext _
--     intro x
--     have h1 := h x
--     have h2 := funext h1
--     exact h2 -- 这一步有点奇妙
--   · intro h2
--     intro h3
--     intro h4
--     rw [h2]

-- theorem ext: (∀ i j, M i j = N i j) → M = N
-- := by
--   exact ext_iff.mp

-- @[ext]
-- theorem ext' : (∀ i, M i = N i) → M = N
-- := by
--   -- 第一种写法：:=
--   -- fun h => ext <| fun i => by simp[h]
--   -- have h1 :=
--   intro h1
--   refine' funext _
--   have h2 := fun x ↦ h1 x
--   exact h2

-- -- ---//


-- def of : (m → n → α) ≃ Matrix m n α
-- := by
--   -- 第一种证明 :=
--   -- Equiv.refl _
--   ---
--   simp only [Matrix]
--   rfl

-- @[simp]
-- theorem of_apply (f : m → n → α) (i j) : (of f) i j = f i j
-- := by
--   -- 第一种证明:=
--   -- rfl
--   ---
--   have h1 := (of f)
--   have h2 := (of f) --用于对比
--   simp only [Matrix] at h1 h2 -- 这里说明 (of f) 就等价于映射 m → n → α ，而目标右边f也是映射m → n → α
--   rfl

-- @[simp]
-- theorem of_symm_apply (f : Matrix m n α) (i j) : of.symm f i j = f i j
-- := by
--   -- :=
--   -- rfl
--   ---
--   have h1 := (of.symm f)
--   -- have h2 := (of.symm f)
--   have h2 := f
--   simp only [Matrix] at h2 h1
--   rfl


-- -- ---//
-- def map (M : Matrix m n α) (f : α → β) : Matrix m n β :=
--   -- of fun i j => f (M i j)
--   by
--   intro x y
--   have h1 := M x y
--   have h2 := f h1
--   exact h2
--   done

-- @[simp]
-- theorem map_apply {M : Matrix m n α} {f : α → β} {i : m} {j : n} : (M.map f) i j = f (M i j) :=
--   -- rfl
--   by
--   have map_M_f := map M f
--   have M_i_j := M i j
--   have left := map_M_f i j
--   have right := f M_i_j -- 用于比较
--   rfl

-- @[simp]
-- theorem map_id (M : Matrix m n α) : M.map id = M := by
--   ext i j
--   -- 中间是用了map_apply
--   simp only [map_apply]
--   simp only [id_eq]
--   -- rfl

-- @[simp]
-- theorem map_map {M : Matrix m n α} {β γ : Type*} {f : α → β} {g : β → γ} : (M.map f).map g = M.map (g ∘ f) := by
--   ext i j
--   have h1 := map M f
--   have h2 := map h1 g
--   have h3 := g ∘ f
--   have h4 := map M h3
--   rfl
--   -- simp only [map_apply]
--   -- simp only [Function.comp_apply]
--   -- rfl

-- -- theorem map_injective {f : α → β} (hf : Function.Injective f) : Function.Injective (fun (M : Matrix m n α) => (M.map f))
-- -- :=
-- --   fun _ _ h =>
-- --   ext fun i j => hf <| (ext_iff.mpr h) i j
-- -- #print map_injective₁
-- -- theorem Matrix.map_injective₁.{u_3, u_2, v, w} : ∀ {m : Type u_2} {n : Type u_3} {α : Type v} {β : Type w} {f : α → β},
-- --   Function.Injective f → Function.Injective fun M ↦ map M f :=
-- -- fun {m} {n} {α} {β} {f} hf x x_1 h ↦ ext fun i j ↦ hf (ext_iff.mpr h i j)
-- -- theorem map_injective₂ {f : α → β} (hf : Function.Injective f) : Function.Injective (fun (M : Matrix m n α) => (M.map f))
-- -- :=
-- --   by
-- --   intro M1 M2 Inj
-- --   simp only at Inj
-- --   simp only [map] at Inj
-- --   -- ext m1 n1
-- --   have h1 := (@ext_iff m n α)
-- --   specialize h1
-- --   · exact M1
-- --   · exact M2
-- --   -- apply symm at h1
-- --   apply h1.1
-- --   intro m1 n1
-- --   sorry
-- theorem map_injective {f : α → β} (hf : Function.Injective f) : Function.Injective (fun (M : Matrix m n α) => (M.map f))
-- :=
--   by
--   intros M1 M2 Inj
--   -- hf (ext_iff.mpr h i j)
--   -- ext_iff.mpr h i j   :   (fun M ↦ map M f) x i j = (fun M ↦ map M f) x_1 i j
--   ext m1 n1
--   have h1 :  (fun M ↦ map M f) M1 m1 n1 = (fun M ↦ map M f) M2 m1 n1
--     := by
--     have h2 := (ext_iff.mpr Inj)
--     apply h2
--     done
--   have h3:= hf h1
--   exact h3
--   done -- 太牛了嘿嘿嘿，print大法 -!!!



-- /--矩阵的转置 The transpose of a matrix. -/
-- def transpose (M : Matrix m n α) : Matrix n m α :=
--   -- of fun x y => M y x
--   by
--   intro n1 m1
--   have h1 := M m1 n1
--   exact h1
--   done
--   -- 这里究竟算是定义还是证明，在lean里面其实有一点玄妙 !!!

-- @[simp]
-- theorem transpose_apply (M : Matrix m n α) (j i) : transpose M i j = M j i :=
--   -- rfl
--   by
--   have h1 := transpose M
--   have h2 := h1 i j
--   have h3 :=(M j i)
--   set a1 := transpose M
--   rfl
--   done


-- @[inherit_doc] --从这个文件找transpose
-- scoped postfix:1024 "ᵀ" => Matrix.transpose --定义了符号表示转置



-- def conjTranspose [Star α] (M : Matrix m n α) : Matrix n m α :=
--   M.transpose.map star
--   -- by
--   -- exact Mᵀ
-- -- def conjTranspose₂ [inst : Star α] (M : Matrix m n α) : Matrix n m α :=
-- --   -- M.transpose.map star
-- --   -- map Mᵀ star
-- --   by
-- --   have h1 := M.transpose
-- --   have h2 := h1.map inst.star
-- --   exact h2

-- -- -- 这里可以看到conjTranspose和conjTranspose₃的不同，后者根本不用到Star，所以定义的时候是很自由的，只要目的类符合即可，只是名字不一样
-- -- def conjTranspose₃ [inst : Star α] (M : Matrix m n α) : Matrix n m α :=
-- --   by
-- --   have h1 := M.transpose
-- --   exact h1


-- @[inherit_doc]
-- scoped postfix:1024 "ᴴ" => Matrix.conjTranspose

-- -- 矩阵的列
-- -- 这里Unit类似于void，不需要放参数
-- def col (w : m → α) : Matrix m Unit α :=
--   -- of fun x _ => w x
--   by
--   intro m1 empty1
--   apply w at m1
--   exact m1
--   done


-- @[simp]
-- theorem col_apply (w : m → α) (i j) : col w i j = w i :=
--   -- rfl
--   by
--   set col1 := col w
--   have left := col1 i j
--   have right := w i
--   rfl

-- --  矩阵的行
-- def row (v : n → α) : Matrix Unit n α :=
--   -- of fun _ y => v y
--   by
--   intro empty1 n1
--   apply v at n1
--   exact n1
--   done

-- @[simp]
-- theorem row_apply (v : n → α) (i j) : row v i j = v j :=
--   -- rfl
--   by
--   set row1 := row v
--   have left := row1 i j
--   have right := v j
--   rfl

-- -- Inhabited感觉像是一个默认值,先不管
-- -- instance inhabited [Inhabited α] : Inhabited (Matrix m n α) :=
-- --   instInhabitedForAll_1 _
-- -- #print inhabited

-- -- -- DecidableEq感觉说的是(Matrix m n α)的任意两个对象是可以判断是否相等的，先不管
-- -- instance decidableEq [DecidableEq α] [Fintype m] [Fintype n] : DecidableEq (Matrix m n α) :=
-- --   Fintype.decidablePiFintype
-- -- #print decidableEq

-- -- 加法实例
-- instance add [Add α] : Add (Matrix m n α) :=
--   Pi.instAdd

-- -- #print Pi.instAdd

-- -- 加法结合律
-- instance addSemigroup [AddSemigroup α] : AddSemigroup (Matrix m n α) :=
--   Pi.addSemigroup

-- -- 加法交换律
-- instance addCommSemigroup [AddCommSemigroup α] : AddCommSemigroup (Matrix m n α) :=
--   Pi.addCommSemigroup

-- -- 零：也是一个同Matrix m n α类型的对象
-- instance zero [Zero α] : Zero (Matrix m n α) :=
--   Pi.instZero

-- -- 加零，零加，都等于本身
-- instance addZeroClass [AddZeroClass α] : AddZeroClass (Matrix m n α) :=
--   Pi.addZeroClass

-- --  0 + a = a + 0 = a 为什么还要重复写呢？不知道
-- instance addMonoid [AddMonoid α] : AddMonoid (Matrix m n α) :=
--   Pi.addMonoid

-- -- 加法交换律 和   0 + a = a + 0 = a
-- instance addCommMonoid [AddCommMonoid α] : AddCommMonoid (Matrix m n α) :=
--   Pi.addCommMonoid

-- -- 有对象-a : α
-- instance neg [Neg α] : Neg (Matrix m n α) :=
--   Pi.instNeg

-- -- 有对象 a - b : α
-- instance sub [Sub α] : Sub (Matrix m n α) :=
--   Pi.instSub

-- -- 满足0 + a = a + 0 = a
-- -- -a + a = 0
-- -- a - b = a + -b
-- instance addGroup [AddGroup α] : AddGroup (Matrix m n α) :=
--   Pi.addGroup

-- -- 加法群(+)
-- -- 加法交换律
-- instance addCommGroup [AddCommGroup α] : AddCommGroup (Matrix m n α) :=
--   Pi.addCommGroup

-- -- 唯一还是什么？不太清晰
-- instance unique [Unique α] : Unique (Matrix m n α) :=
--   Pi.unique

-- -- (a b : α) → a = b 感觉意思是 某个特定的矩阵A是唯一的，若有另一个矩阵B，那也和A相等
-- instance subsingleton [Subsingleton α] : Subsingleton (Matrix m n α) :=
--   instSubsingletonForAll

-- -- 至少有两个元素？0 ≠ 1？不太清晰
-- instance nonempty [Nonempty m] [Nonempty n] [Nontrivial α] : Nontrivial (Matrix m n α) :=
--   Function.nontrivial

-- -- 具有标量乘法运算
-- instance smul [SMul R α] : SMul R (Matrix m n α) :=
--   Pi.instSMul

-- -- 标量乘法的交换律 m • n • a = n • m • a
-- instance smulCommClass [SMul R α] [SMul S α] [SMulCommClass R S α] : SMulCommClass R S (Matrix m n α) :=
--   Pi.smulCommClass

-- -- 标量乘法的结合律(x • y) • z = x • y • z
-- instance isScalarTower [SMul R S] [SMul R α] [SMul S α] [IsScalarTower R S α] : IsScalarTower R S (Matrix m n α) :=
--   Pi.isScalarTower

-- -- 左右标量乘法是平等的
-- instance isCentralScalar [SMul R α] [SMul Rᵐᵒᵖ α] [IsCentralScalar R α] : IsCentralScalar R (Matrix m n α) :=
--   Pi.isCentralScalar

-- -- 标量乘法(1 : α) • b = b
-- -- 这个不知道是什么运算*，满足 (x * y) • b = x • y • b
-- instance mulAction [Monoid R] [MulAction R α] : MulAction R (Matrix m n α) :=
--   Pi.mulAction _

-- -- 标量乘法a • (0 : A) = 0
-- -- 加法和标量乘法的分配律a • (x + y) = a • x + a • y
-- instance distribMulAction [Monoid R] [AddMonoid α] [DistribMulAction R α] :
--     DistribMulAction R (Matrix m n α) :=
--   Pi.distribMulAction _

-- -- 满足以下条件，•是标量乘法，+是矩阵加法，*不知道是什么
-- -- (r + s) • x = r • x + s • x
-- -- (0 : R) • x = 0
-- -- a • (0 : A) = 0
-- -- a • (x + y) = a • x + a • y
-- -- (1 : α) • b = b
-- -- (x * y) • b = x • y • b
-- instance module [Semiring R] [AddCommMonoid α] [Module R α] : Module R (Matrix m n α) :=
--   Pi.module _ _ _

-- section --/

-- @[simp]
-- theorem zero_apply [Zero α] (i : m) (j : n) : (0 : Matrix m n α) i j = 0 :=
--   rfl --?

-- -- 矩阵相加，取项。
-- -- 等价于
-- -- 矩阵取项，相加
-- @[simp]
-- theorem add_apply [Add α] (A B : Matrix m n α) (i : m) (j : n) : (A + B) i j = (A i j) + (B i j) :=
--   -- rfl
--   by
--   set AplusB := A + B
--   have left := AplusB i j
--   set Aij := A i j
--   set Bij := B i j
--   have right := Aij + Bij
--   rfl

-- @[simp]
-- theorem smul_apply [SMul β α] (r : β) (A : Matrix m n α) (i : m) (j : n) : (r • A) i j = r • (A i j) :=
--   -- rfl
--   by
--   set rmulA := (r • A)
--   have l := rmulA i j
--   set Aij := A i j
--   have r := r • Aij
--   rfl

-- @[simp]
-- theorem sub_apply [Sub α] (A B : Matrix m n α) (i : m) (j : n) : (A - B) i j = (A i j) - (B i j) :=
--   -- rfl
--   by
--   rfl

-- @[simp]
-- theorem neg_apply [Neg α] (A : Matrix m n α) (i : m) (j : n) : (-A) i j = -(A i j) :=
--   -- rfl
--   by
--   rfl

-- end --/


-- @[simp]
-- theorem of_zero [Zero α] : of (0 : m → n → α) = 0 :=
--   -- rfl
--   by
--   set l := of (0 : m → n → α)
--   rfl

-- @[simp]
-- theorem of_add_of [Add α] (f g : m → n → α) : of f + of g = of (f + g) :=
--   -- rfl
--   by
--   set of_f := of f
--   set of_g := of g
--   set r := of (f+g)
--   set l := of_f + of_g
--   rfl

-- @[simp]
-- theorem of_sub_of [Sub α] (f g : m → n → α) : of f - of g = of (f - g) :=
--   -- rfl
--   by
--   rfl

-- @[simp]
-- theorem neg_of [Neg α] (f : m → n → α) : -of f = of (-f) :=
--   -- rfl
--   by
--   rfl

-- @[simp]
-- theorem smul_of [SMul R α] (r : R) (f : m → n → α) : r • of f = of (r • f) :=
--   rfl

-- -- theorem wrong [Sub α] [Neg α] (f g : m → n → α) : ¬  (of f - of g = of (-f)) :=
-- --   by
-- --   set of_f := of f
-- --   set of_g := of g
-- --   set l := of_f - of_g
-- --   set r := of (-f)
-- --   refine Ne.intro ?h
-- --   intro


-- @[simp]
-- protected theorem map_zero [Zero α] [Zero β] (f : α → β) (h : f 0 = 0) : (0 : Matrix m n α).map f = 0
-- := by
--   ext
--   simp only [map_apply]
--   simp only [zero_apply]
--   exact h
--   done

-- protected theorem map_add [Add α] [Add β] (f : α → β) (hf : ∀ a₁ a₂, f (a₁ + a₂) = f a₁ + f a₂) (M N : Matrix m n α) : (M + N).map f = M.map f + N.map f
-- :=
-- -- ext fun _ _ => hf _ _
--   by
--   ext m1 n1
--   -- apply?
--   have h2 := hf (M m1 n1) (N m1 n1)
--   simp only [map_apply, add_apply]
--   exact h2
--   done

-- protected theorem map_sub [Sub α] [Sub β] (f : α → β) (hf : ∀ a₁ a₂, f (a₁ - a₂) = f a₁ - f a₂) (M N : Matrix m n α) : (M - N).map f = M.map f - N.map f
-- :=
--   ext fun _ _ => hf _ _

-- theorem map_smul [SMul R α] [SMul R β] (f : α → β) (r : R) (hf : ∀ a, f (r • a) = r • f a) (M : Matrix m n α) : (r • M).map f = r • M.map f
-- :=
--   ext fun _ _ => hf _

-- theorem map_smul' [Mul α] [Mul β] (f : α → β) (r : α) (A : Matrix n n α) (hf : ∀ a₁ a₂, f (a₁ * a₂) = f a₁ * f a₂) : (r • A).map f = f r • A.map f
-- :=
--   ext fun _ _ => hf _ _

-- -- MulOpposite.op是标量乘法的倒数吧
-- theorem map_op_smul' [Mul α] [Mul β] (f : α → β) (r : α) (A : Matrix n n α) (hf : ∀ a₁ a₂, f (a₁ * a₂) = f a₁ * f a₂) :
-- (MulOpposite.op r • A).map f = MulOpposite.op (f r) • A.map f
--   :=
--   ext fun _ _ => hf _ _

-- -- 左标量乘法是单射
-- theorem _root_.IsSMulRegular.matrix [SMul R S] {k : R} (hk : IsSMulRegular S k) : IsSMulRegular (Matrix m n S) k
-- :=
--   IsSMulRegular.pi fun _ => IsSMulRegular.pi fun _ => hk

-- -- 好像也是说的左乘法是单射
-- theorem _root_.IsLeftRegular.matrix [Mul α] {k : α} (hk : IsLeftRegular k) : IsSMulRegular (Matrix m n α) k :=
--   hk.isSMulRegular.matrix


-- instance subsingleton_of_empty_left [IsEmpty m] : Subsingleton (Matrix m n α) :=
--   ⟨fun M N => by
--     ext i
--     exact isEmptyElim i⟩

-- instance subsingleton_of_empty_right [IsEmpty n] : Subsingleton (Matrix m n α) :=
--   ⟨fun M N => by
--     ext i j
--     exact isEmptyElim j⟩

-- end Matrix




-- open Matrix --/

-- namespace Matrix

-- section Diagonal --/

-- variable [DecidableEq n]



-- -- 对角矩阵，只有左上到右下的对角线有对象，其他为0
-- def diagonal [Zero α] (d : n → α) : Matrix n n α :=
--   -- of fun i j => if i = j then d i else 0
--   by
--   have f1:= fun i j => if i = j then d i else 0
--   have M1:= of f1
--   exact M1

-- theorem diagonal_apply [Zero α] (d : n → α) (i j) : diagonal d i j = if i = j then d i else 0 :=
--   -- rfl
--   by
--   simp only [diagonal]
--   simp only [of_apply]
--   done

-- @[simp]
-- theorem diagonal_apply_eq [Zero α] (d : n → α) (i : n) : (diagonal d) i i = d i
-- := by
--   simp only [diagonal]
--   simp only [of_apply, ite_true]


-- @[simp]
-- theorem diagonal_apply_ne [Zero α] (d : n → α) {i j : n} (h : i ≠ j) : (diagonal d) i j = 0 := by
--   -- simp [diagonal, h]
--   simp only [diagonal, h]
--   simp only [of_apply, ite_eq_right_iff]
--   intro h2
--   exact (h h2).elim

-- theorem diagonal_apply_ne' [Zero α] (d : n → α) {i j : n} (h : j ≠ i) : (diagonal d) i j = 0 :=
--   diagonal_apply_ne d h.symm

-- @[simp]
-- theorem diagonal_eq_diagonal_iff [Zero α] {d₁ d₂ : n → α} : diagonal d₁ = diagonal d₂ ↔ ∀ i, d₁ i = d₂ i
-- :=
--   ⟨fun h i => by simpa using congr_arg (fun m : Matrix n n α => m i i) h,
--   fun h => by
--     rw [show d₁ = d₂ from funext h]⟩

-- theorem diagonal_injective [Zero α] : Function.Injective (diagonal : (n → α) → Matrix n n α)
-- := fun d₁ d₂ h => funext fun i => by simpa using Matrix.ext_iff.mpr h i i

-- @[simp]
-- theorem diagonal_zero [Zero α] : (diagonal fun _ => 0 : Matrix n n α) = 0
-- := by
--   ext
--   simp [diagonal]

-- @[simp]
-- theorem diagonal_transpose [Zero α] (v : n → α) : (diagonal v)ᵀ = diagonal v
-- := by
--   ext i j
--   by_cases h : i = j
--   · simp [h, transpose]
--   · simp [h, transpose, diagonal_apply_ne' _ h]

-- @[simp]
-- theorem diagonal_add [AddZeroClass α] (d₁ d₂ : n → α) : diagonal d₁ + diagonal d₂ = diagonal fun i => d₁ i + d₂ i
--     := by
--   ext i j
--   by_cases h : i = j <;>
--   simp [h]

-- @[simp]
-- theorem diagonal_smul [Monoid R] [AddMonoid α] [DistribMulAction R α] (r : R) (d : n → α) : diagonal (r • d) = r • diagonal d
-- := by
--   ext i j
--   by_cases h : i = j <;>
--   simp [h]

-- variable (n α)


-- @[simps] -- 注意这个符号 →+， 和“加幺半群”有关
-- def diagonalAddMonoidHom [AddZeroClass α] : (n → α) →+ Matrix n n α where
--   toFun := diagonal
--   map_zero' := diagonal_zero
--   map_add' x y := (diagonal_add x y).symm

-- variable (R)

-- @[simps] -- 线性映射
-- def diagonalLinearMap [Semiring R] [AddCommMonoid α] [Module R α] : (n → α) →ₗ[R] Matrix n n α :=
--   { diagonalAddMonoidHom n α with map_smul' := diagonal_smul }

-- variable {n α R}

-- @[simp]
-- theorem diagonal_map [Zero α] [Zero β] {f : α → β} (h : f 0 = 0) {d : n → α} : (diagonal d).map f = diagonal fun m => f (d m) := by
--   ext
--   simp only [diagonal_apply, map_apply]
--   split_ifs <;> simp [h]


-- @[simp] -- star 类似复共轭这样的运算
-- theorem diagonal_conjTranspose [AddMonoid α] [StarAddMonoid α] (v : n → α) : (diagonal v)ᴴ = diagonal (star v)
-- := by
--   rw [conjTranspose, diagonal_transpose, diagonal_map (star_zero _)]
--   rfl

-- section One

-- variable [Zero α] [One α]

-- instance one : One (Matrix n n α) :=
--   ⟨diagonal fun _ => 1⟩

-- @[simp]
-- theorem diagonal_one : (diagonal fun _ => 1 : Matrix n n α) = 1 :=
--   rfl

-- theorem one_apply {i j} : (1 : Matrix n n α) i j = if i = j then 1 else 0 :=
--   rfl

-- @[simp]
-- theorem one_apply_eq (i) : (1 : Matrix n n α) i i = 1 :=
--   diagonal_apply_eq _ i

-- @[simp]
-- theorem one_apply_ne {i j} : i ≠ j → (1 : Matrix n n α) i j = 0 :=
--   diagonal_apply_ne _

-- theorem one_apply_ne' {i j} : j ≠ i → (1 : Matrix n n α) i j = 0 :=
--   diagonal_apply_ne' _

-- @[simp]
-- theorem map_one [Zero β] [One β] (f : α → β) (h₀ : f 0 = 0) (h₁ : f 1 = 1) : (1 : Matrix n n α).map f = (1 : Matrix n n β) := by
--   ext
--   simp only [one_apply, map_apply]
--   split_ifs <;> simp [h₀, h₁]

-- theorem one_eq_pi_single {i j} : (1 : Matrix n n α) i j = Pi.single (f := fun _ => α) i 1 j
-- := by
--   simp only [one_apply, Pi.single_apply, eq_comm]

-- end One

-- section Numeral

-- -- 弃用警告 关闭
-- set_option linter.deprecated false

-- @[deprecated, simp]
-- theorem bit0_apply [Add α] (M : Matrix m m α) (i : m) (j : m) : (bit0 M) i j = bit0 (M i j)
-- :=
--   rfl

-- variable [AddZeroClass α] [One α]

-- @[deprecated]
-- theorem bit1_apply (M : Matrix n n α) (i : n) (j : n) :
--     (bit1 M) i j = if i = j then bit1 (M i j) else bit0 (M i j) := by
--   dsimp [bit1]
--   by_cases h : i = j <;>
--   simp [h]

-- @[deprecated, simp]
-- theorem bit1_apply_eq (M : Matrix n n α) (i : n) : (bit1 M) i i = bit1 (M i i)
-- := by
--   simp [bit1_apply]

-- @[deprecated, simp]
-- theorem bit1_apply_ne (M : Matrix n n α) {i j : n} (h : i ≠ j) : (bit1 M) i j = bit0 (M i j)
-- := by
--   simp [bit1_apply, h]

-- end Numeral

-- end Diagonal


-- section Diag

-- -- 正方阵的对角线
-- -- @[simp] -- Porting note: simpNF does not like this.
-- def diag (A : Matrix n n α) (i : n) : α :=
--   A i i


-- @[simp]
-- theorem diag_apply (A : Matrix n n α) (i) : diag A i = A i i
-- :=
--   rfl

-- @[simp]
-- theorem diag_diagonal [DecidableEq n] [Zero α] (a : n → α) : diag (diagonal a) = a
-- :=
--   funext <| @diagonal_apply_eq _ _ _ _ a

-- @[simp]
-- theorem diag_transpose (A : Matrix n n α) : diag Aᵀ = diag A :=
--   rfl

-- @[simp]
-- theorem diag_zero [Zero α] : diag (0 : Matrix n n α) = 0 :=
--   rfl

-- @[simp]
-- theorem diag_add [Add α] (A B : Matrix n n α) : diag (A + B) = diag A + diag B :=
--   rfl

-- @[simp]
-- theorem diag_sub [Sub α] (A B : Matrix n n α) : diag (A - B) = diag A - diag B :=
--   rfl

-- @[simp]
-- theorem diag_neg [Neg α] (A : Matrix n n α) : diag (-A) = -diag A :=
--   rfl

-- @[simp]
-- theorem diag_smul [SMul R α] (r : R) (A : Matrix n n α) : diag (r • A) = r • diag A :=
--   rfl

-- @[simp]
-- theorem diag_one [DecidableEq n] [Zero α] [One α] : diag (1 : Matrix n n α) = 1 :=
--   diag_diagonal _

-- variable (n α)

-- /-- 加幺半群`Matrix.diag` as an `AddMonoidHom`. -/
-- @[simps]
-- def diagAddMonoidHom [AddZeroClass α] : Matrix n n α →+ n → α where
--   toFun := diag
--   map_zero' := diag_zero
--   map_add' := diag_add

-- variable (R)

-- -- 线性映射
-- @[simps]
-- def diagLinearMap [Semiring R] [AddCommMonoid α] [Module R α] : Matrix n n α →ₗ[R] n → α
-- :=
--   { diagAddMonoidHom n α with map_smul' := diag_smul }

-- variable {n α R}

-- theorem diag_map {f : α → β} {A : Matrix n n α} : diag (A.map f) = f ∘ diag A
-- :=
--   rfl

-- @[simp]
-- theorem diag_conjTranspose [AddMonoid α] [StarAddMonoid α] (A : Matrix n n α) : diag Aᴴ = star (diag A)
-- :=
--   rfl

-- @[simp]
-- theorem diag_list_sum [AddMonoid α] (l : List (Matrix n n α)) : diag l.sum = (l.map diag).sum
-- :=
--   map_list_sum (diagAddMonoidHom n α) l

-- -- 即“求和 s 中所有矩阵的对角线元素之和”的结果等于“把 s 中的每个矩阵映射为其对角矩阵再求和”的结果。
-- @[simp]
-- theorem diag_multiset_sum [AddCommMonoid α] (s : Multiset (Matrix n n α)) : diag s.sum = (s.map diag).sum :=
--   map_multiset_sum (diagAddMonoidHom n α) s

-- -- 对于集合s中的每个元素f i，对其取对角线元素并求和得到∑ i in s, diag (f i)；
-- -- 对集合s中的所有元素f i 求和，并取其对角线元素得到diag (∑ i in s, f i)；
-- -- 两个结果相等。
-- @[simp]
-- theorem diag_sum {ι} [AddCommMonoid α] (s : Finset ι) (f : ι → Matrix n n α) : diag (∑ i in s, f i) = ∑ i in s, diag (f i)
-- :=
--   map_sum (diagAddMonoidHom n α) f s

-- end Diag --/

-- section DotProduct --\

-- variable [Fintype m] [Fintype n]

-- -- 逐项乘积，也就是点积
-- def dotProduct [Mul α] [AddCommMonoid α] (v w : m → α) : α :=
--   ∑ i, v i * w i

-- @[inherit_doc]
-- scoped infixl:72 " ⬝ᵥ " => Matrix.dotProduct

-- -- 点积的结合律
-- theorem dotProduct_assoc [NonUnitalSemiring α] (u : m → α) (w : n → α) (v : Matrix m n α) : ( (fun j => (u) ⬝ᵥ (fun i => v i j)) ⬝ᵥ w )  =  ( u ⬝ᵥ fun i => v i ⬝ᵥ w )
-- := by
--   simpa [dotProduct, Finset.mul_sum, Finset.sum_mul, mul_assoc] using Finset.sum_comm

-- --点积的交换律
-- theorem dotProduct_comm [AddCommMonoid α] [CommSemigroup α] (v w : m → α) : v ⬝ᵥ w = w ⬝ᵥ v
-- := by
-- simp_rw [dotProduct, mul_comm]

-- -- PUnit 是一个类型，它只有一个元素，用 ⟨⟩ 表示出
-- -- 假设有两个函数 v 和 w，它们都从类型为 PUnit 到类型为 α 的值域。由于 PUnit 只有一个元素 ⟨⟩，所以这两个函数在 ⟨⟩ 上的取值分别为 v ⟨⟩ 和 w ⟨⟩。
-- -- 这个定理的表述是说，点积运算 v ⬝ᵥ w 的结果等于将这两个函数在 ⟨⟩ 上的取值相乘。也就是说，v ⬝ᵥ w 等于 v ⟨⟩ * w ⟨⟩。
-- -- 点积是一种向量运算，用于计算两个向量之间的相似性或者进行向量的变换。在这个定理中，点积的定义是将两个函数在所有可能输入的位置上的值相乘并求和。然而，由于 PUnit 只有一个元素，所以 v 和 w 的取值只与 ⟨⟩ 相关。
-- -- 因此，这个定理实际上在说，当向量的输入空间只有一个元素时，点积运算可以简化为将两个函数在该元素上的取值相乘。
-- @[simp]
-- theorem dotProduct_pUnit [AddCommMonoid α] [Mul α] (v w : PUnit → α) : v ⬝ᵥ w = v ⟨⟩ * w ⟨⟩
-- := by
--   simp [dotProduct]

-- section MulOneClass

-- variable [MulOneClass α] [AddCommMonoid α]

-- theorem dotProduct_one (v : n → α) : v ⬝ᵥ 1 = ∑ i, v i
-- := by simp [(· ⬝ᵥ ·)]

-- theorem one_dotProduct (v : n → α) : 1 ⬝ᵥ v = ∑ i, v i
-- := by simp [(· ⬝ᵥ ·)]

-- end MulOneClass

-- section NonUnitalNonAssocSemiring

-- variable [NonUnitalNonAssocSemiring α] (u v w : m → α) (x y : n → α)

-- @[simp]
-- theorem dotProduct_zero : v ⬝ᵥ 0 = 0
-- := by simp [dotProduct]

-- @[simp]
-- theorem dotProduct_zero' : (v ⬝ᵥ fun _ => 0) = 0
-- :=
--   dotProduct_zero v

-- @[simp]
-- theorem zero_dotProduct : 0 ⬝ᵥ v = 0
-- := by simp [dotProduct]

-- @[simp]
-- theorem zero_dotProduct' : (fun _ => (0 : α)) ⬝ᵥ v = 0
-- :=
--   zero_dotProduct v

-- -- 点积的分配律
-- @[simp]
-- theorem add_dotProduct : (u + v) ⬝ᵥ w = u ⬝ᵥ w + v ⬝ᵥ w
-- := by
--   simp [dotProduct, add_mul, Finset.sum_add_distrib]

-- @[simp]
-- theorem dotProduct_add : u ⬝ᵥ (v + w) = u ⬝ᵥ v + u ⬝ᵥ w := by
--   simp [dotProduct, mul_add, Finset.sum_add_distrib]

-- -- 假设有 u = [1, 2]、v = [3, 4]、x = [5, 6] 和 y = [7, 8]，这些数字代表了四个向量。现在我们想要计算 Sum.elim u x ⬝ᵥ Sum.elim v y 的值。
-- -- 首先， Sum.elim u x 表示将两个向量 u = [1, 2] 和 x = [5, 6] 进行组合，得到新的向量 [1, 2, 5, 6]；Sum.elim v y 表示将两个向量 v = [3, 4] 和 y = [7, 8] 进行组合，得到新的向量 [3, 4, 7, 8]。
-- -- 接下来，我们将新得到的两个向量 [1, 2, 5, 6] 和 [3, 4, 7, 8] 进行点积运算。根据点积的定义，这个点积的计算方式如下：
-- -- (1 * 3) + (2 * 4) + (5 * 7) + (6 * 8) = 3 + 8 + 35 + 48 = 94
-- -- 同样，我们也可以直接计算 u ⬝ᵥ v + x ⬝ᵥ y 的值：
-- -- (1 * 3 + 2 * 4) + (5 * 7 + 6 * 8) = 3 + 8 + 35 + 48 = 94
-- @[simp]
-- theorem sum_elim_dotProduct_sum_elim : (Sum.elim u x) ⬝ᵥ (Sum.elim v y) = u ⬝ᵥ v + x ⬝ᵥ y
-- := by
--   simp [dotProduct]


-- -- 举一个实际的例子。
-- -- 假设在一个二维坐标系中，有两个点 (1, 2) 和 (3, 4)（即一维坐标为 1 和 3，二维坐标为 2 和 4）。我们可以将这两个点分别表示为 m 中的向量 u = [1, 2] 和 x = [3, 4]。现在我们想要将这两个点从一个坐标系之间映射到另一个坐标系。
-- -- 首先，我们有一个双射 e，这个双射将第一个坐标系上的点 (1, 2) 映射到第二个坐标系的点 (4, 5) 上，将第一个坐标系上的点 (3, 4) 映射到第二个坐标系中的点 (6, 7) 上。那么，我们可以使用双射 e 将向量 u 和 x 转换为类型为 n 的向量，表示它们在第二个坐标系中的位置关系。即：
-- -- u 通过 e 映射为向量 u' = [4, 5]
-- -- x 通过 e 映射为向量 x' = [6, 7]
-- -- 接下来，我们可以用这两个向量在第二个坐标系中进行点积运算，得到它们在空间中的位置关系。即：
-- -- u' ⬝ᵥ x' = (4 * 6) + (5 * 7) = 62
-- -- 如果我们按照原始的方式，将点在第一个坐标系中的位置通过点积运算得到它们在空间中的位置关系，也可以应用双射 e 将点转换为类型为 n 的向量，再用它们在第二个坐标系中的向量进行点积运算。即：
-- -- u 在第一个坐标系中的位置为 (1,2)，那么向量 u 在 e 映射下变成 u' = [4, 5]
-- -- x 在第一个坐标系中的位置为 (3, 4)，那么向量 x 在 e 映射下变成 x' = [6, 7]
-- -- 然后，使用这两个类型为 n 的向量进行点积运算，即 u' ⬝ᵥ x' = 62。
-- -- 可以看到，无论是将两个点直接进行点积运算，还是先将它们进行双射 e 的映射，得到对应的向量，再进行点积运算，最终得到的结果都是相同的，即点积的结果是 62，表示这两个点之间的相似度为 62。这说明了该定理在空间变换中的应用。
-- @[simp]
-- theorem comp_equiv_symm_dotProduct (e : m ≃ n) : u ∘ e.symm ⬝ᵥ x = u ⬝ᵥ x ∘ e
-- :=
--   (e.sum_comp _).symm.trans <|
--     Finset.sum_congr rfl fun _ _ => by simp only [Function.comp, Equiv.symm_apply_apply]


-- @[simp]
-- theorem dotProduct_comp_equiv_symm (e : n ≃ m) : u ⬝ᵥ x ∘ e.symm = u ∘ e ⬝ᵥ x
-- := by
--   simpa only [Equiv.symm_symm] using (comp_equiv_symm_dotProduct u x e.symm).symm

-- @[simp]
-- theorem comp_equiv_dotProduct_comp_equiv (e : m ≃ n) : x ∘ e ⬝ᵥ y ∘ e = x ⬝ᵥ y
-- := by
--   -- Porting note: was `simp only` with all three lemmas
--   rw [← dotProduct_comp_equiv_symm]; simp only [Function.comp, Equiv.apply_symm_apply]

-- end NonUnitalNonAssocSemiring

-- section NonUnitalNonAssocSemiringDecidable

-- variable [DecidableEq m] [NonUnitalNonAssocSemiring α] (u v w : m → α)

-- @[simp]
-- theorem diagonal_dotProduct (i : m) : diagonal v i ⬝ᵥ w = v i * w i
-- := by
--   have : ∀ (j) (_ : j ≠ i), diagonal v i j * w j = 0 := fun j hij => by
--     simp [diagonal_apply_ne' _ hij]
--   convert Finset.sum_eq_single i (fun j _ => this j) _ using 1 <;> simp

-- @[simp]
-- theorem dotProduct_diagonal (i : m) : v ⬝ᵥ diagonal w i = v i * w i
-- := by
--   have : ∀ (j) (_ : j ≠ i), v j * diagonal w i j = 0 := fun j hij => by
--     simp [diagonal_apply_ne' _ hij]
--   convert Finset.sum_eq_single i (fun j _ => this j) _ using 1 <;> simp

-- @[simp]
-- theorem dotProduct_diagonal' (i : m) : (v ⬝ᵥ fun j => diagonal w j i) = v i * w i
-- := by
--   have : ∀ (j) (_ : j ≠ i), v j * diagonal w j i = 0 := fun j hij => by
--     simp [diagonal_apply_ne _ hij]
--   convert Finset.sum_eq_single i (fun j _ => this j) _ using 1 <;> simp

-- @[simp]
-- theorem single_dotProduct (x : α) (i : m) : Pi.single i x ⬝ᵥ v = x * v i := by
--   -- Porting note: (implicit arg) added `(f := fun _ => α)`
--   have : ∀ (j) (_ : j ≠ i), Pi.single (f := fun _ => α) i x j * v j = 0 := fun j hij => by
--     simp [Pi.single_eq_of_ne hij]
--   convert Finset.sum_eq_single i (fun j _ => this j) _ using 1 <;> simp

-- -- 这个定理是一个关于点积（dot product）的定理，表达了一个向量 v 和一个特定位置 i 上的标量 x 进行点积运算的结果。
-- -- 具体地说，该定理的公式如下：
-- -- 对于一个加法可交换幺半群 α，一个类型为 m 到 α 的函数 v，以及一个位置 i : m 和一个标量 x : α，有 v ⬝ᵥ Pi.single i x = v i * x。
-- -- 在这个公式中，⬝ᵥ 表示点积运算， Pi.single i x 表示一个类型为 m 的向量，只有在位置 i 上的元素是 x，其他位置上的值都是 0。
-- -- 在该定理中，点积运算的结果等于从 v 函数中取出位置 i 上的元素乘以标量 x 的结果。
-- -- 一个实际的例子可以是，在一个计算模型中，对向量中的数据进行模型更新。假设向量 v 表示了一些计算机网络的负载均衡数据，每个位置上保存着一个特定的负载数据。假设某个位置 i 上的负载需要进行调整，那么我们可以通过给该位置施加一个标量 x 来调整该负载。在施加这个标量 x 时，就要使用该定理进行计算该施加标量后的负载均衡数据。
-- -- 例如，将向量 v 变量设置如下：
-- -- v = [1, 2, 3, 4, 5]
-- -- 现在我们想要将位置 2 上的数字 3 调整为 2。则根据该定理，可以计算出调整后的 v 向量中位置 2 上的数字：
-- -- v ⬝ᵥ Pi.single 2 2 = v 2 *
-- @[simp] -- Pi.single i x 表示一个类型为 m 的向量，只有在位置 i 上的元素是 x，其他位置上的值都是 0。
-- theorem dotProduct_single (x : α) (i : m) : v ⬝ᵥ Pi.single i x = v i * x
-- := by
--   have : ∀ (j) (_ : j ≠ i), v j * Pi.single (f := fun _ => α) i x j = 0 := fun j hij => by
--     simp [Pi.single_eq_of_ne hij]
--   convert Finset.sum_eq_single i (fun j _ => this j) _ using 1 <;> simp

-- end NonUnitalNonAssocSemiringDecidable


-- section NonAssocSemiring

-- variable [NonAssocSemiring α]

-- -- 该定理表明，在一个长度为 n 的向量空间中，假设有一个由全 1 组成的向量 （1 : n → α），与另一个也是全 1 的向量 1 进行点积运算，结果将等于空间中元素的数量（Fintype.card n）。
-- -- 具体解释如下：
-- -- 首先，应用点积的定义，我们可以展开点积运算： (1 : n → α) ⬝ᵥ 1 = ∑ i, (1 i) * (1 i) 因为向量 （1 : n → α）中的所有元素都为 1，所以每一项可以简化为 (1 i) * (1 i) = 1 * 1 = 1。于是，上述求和式可以进一步简化为： (1 : n → α) ⬝ᵥ 1 = ∑ i, 1
-- -- 直观上来看，由于所有的项都是 1，所以求和式 ∑ i, 1 可以看作是将 1 重复相加的次数。而在一个有限类型的向量空间中，元素的数量可以用 Fintype.card n 表示。因此，求和式 ∑ i, 1 实际上等于 Fintype.card n，即空间中的元素数量。
-- -- 接着，我们可以将得到的结果应用到原始的点积展开式中，即 (1 : n → α) ⬝ᵥ 1 = Fintype.card n。这说明了定理的正确性。
-- -- 一个实际例子可以是考虑一个有 n 本书籍的图书馆。我们可以用一个向量 （1 : n → α）来表示每本书的借出状况，其中 1 表示书被借出，0 表示书可供借阅。另外，我们有一个长度为 n 的权重向量 1 ，表示每本书的权重都一样（即相同的重要性或借出待遇）。根据这个定理，对向量 （1 : n → α）和向量 1 进行点积运算，结果将等于图书馆中书籍的数量（Fintype.card n）。这个例子中，点积的结果可以表示为图书馆中已借出的书籍数量，以及标识图书馆中可供借阅的书籍总数。
-- @[simp] -- 在一个有限类型的向量空间中，元素的数量可以用 Fintype.card n 表示
-- theorem one_dotProduct_one : (1 : n → α) ⬝ᵥ 1 = Fintype.card n := by
--   simp [dotProduct, Fintype.card]

-- end NonAssocSemiring

-- section NonUnitalNonAssocRing

-- variable [NonUnitalNonAssocRing α] (u v w : m → α)

-- @[simp]
-- theorem neg_dotProduct : -v ⬝ᵥ w = -(v ⬝ᵥ w)
-- := by simp [dotProduct]

-- @[simp]
-- theorem dotProduct_neg : v ⬝ᵥ -w = -(v ⬝ᵥ w)
-- := by simp [dotProduct]

-- @[simp]
-- theorem sub_dotProduct : (u - v) ⬝ᵥ w = u ⬝ᵥ w - v ⬝ᵥ w
-- := by simp [sub_eq_add_neg]

-- @[simp]
-- theorem dotProduct_sub : u ⬝ᵥ (v - w) = u ⬝ᵥ v - u ⬝ᵥ w := by simp [sub_eq_add_neg]

-- end NonUnitalNonAssocRing

-- section DistribMulAction

-- variable [Monoid R] [Mul α] [AddCommMonoid α] [DistribMulAction R α]

-- @[simp]
-- theorem smul_dotProduct [IsScalarTower R α α] (x : R) (v w : m → α) : x • v ⬝ᵥ w = x • (v ⬝ᵥ w)
-- :=
--   by simp [dotProduct, Finset.smul_sum, smul_mul_assoc]

-- @[simp]
-- theorem dotProduct_smul [SMulCommClass R α α] (x : R) (v w : m → α) : v ⬝ᵥ x • w = x • (v ⬝ᵥ w)
-- :=
--   by simp [dotProduct, Finset.smul_sum, mul_smul_comm]

-- end DistribMulAction

-- section StarRing

-- variable [NonUnitalSemiring α] [StarRing α] (v w : m → α)

-- theorem star_dotProduct_star : star v ⬝ᵥ star w = star (w ⬝ᵥ v)
-- := by simp [dotProduct]

-- theorem star_dotProduct : star v ⬝ᵥ w = star (star w ⬝ᵥ v)
-- := by simp [dotProduct]

-- theorem dotProduct_star : v ⬝ᵥ star w = star (w ⬝ᵥ star v)
-- := by simp [dotProduct]

-- end StarRing


-- end DotProduct

-- open Matrix

-- -- !!!重点矩阵乘法终于到了，线性方程组还会远吗？
-- /-- `M * N` is the usual product of matrices `M` and `N`, i.e. we have that
-- `(M * N) i k` is the dot product of the `i`-th row of `M` by the `k`-th column of `N`.
-- This is currently only defined when `m` is finite. -/
-- -- We want to be lower priority than `instHMul`, but without this we can't have operands with
-- -- implicit dimensions.
-- @[default_instance 100]
-- instance [Fintype m] [Mul α] [AddCommMonoid α] : HMul (Matrix l m α) (Matrix m n α) (Matrix l n α) where
--   hMul M N : l → n → α :=
--     fun i k =>
--       (fun j => M i j) ⬝ᵥ (fun j => N j k)

-- theorem mul_apply [Fintype m] [Mul α] [AddCommMonoid α] {M : Matrix l m α} {N : Matrix m n α} {i k} : (M * N) i k = ∑ j, M i j * N j k
-- :=
--   rfl
--   -- by
--   -- have h1 := (M * N) i k

-- -- #print mul_apply

-- instance [Fintype n] [Mul α] [AddCommMonoid α] : Mul (Matrix n n α) where
--   mul M N := M * N


-- theorem mul_apply' [Fintype m] [Mul α] [AddCommMonoid α] {M : Matrix l m α} {N : Matrix m n α} {i k} : (M * N) i k = (fun j => M i j) ⬝ᵥ fun j => N j k
-- :=
--   rfl

-- @[simp]
-- theorem diagonal_neg [DecidableEq n] [AddGroup α] (d : n → α) : -diagonal d = diagonal fun i => -d i
-- :=
--   ((diagonalAddMonoidHom n α).map_neg d).symm

-- theorem sum_apply [AddCommMonoid α] (i : m) (j : n) (s : Finset β) (g : β → Matrix m n α) : (∑ c in s, g c) i j = ∑ c in s, g c i j
-- :=
--   (congr_fun (s.sum_apply i g) j).trans (s.sum_apply j _)

-- theorem two_mul_expl {R : Type*} [CommRing R] (A B : Matrix (Fin 2) (Fin 2) R) :
--     (A * B) 0 0 = A 0 0 * B 0 0 + A 0 1 * B 1 0 ∧
--     (A * B) 0 1 = A 0 0 * B 0 1 + A 0 1 * B 1 1 ∧
--     (A * B) 1 0 = A 1 0 * B 0 0 + A 1 1 * B 1 0 ∧
--     (A * B) 1 1 = A 1 0 * B 0 1 + A 1 1 * B 1 1
--   := by
--   refine ⟨?_, ?_, ?_, ?_⟩ <;>
--   · rw [Matrix.mul_apply, Finset.sum_fin_eq_sum_range, Finset.sum_range_succ, Finset.sum_range_succ]
--     -- simp?
--     simp only [Finset.range_zero, Finset.sum_empty, Fin.zero_eta, dite_eq_ite, ite_true, zero_add,
--       Fin.mk_one]
--     done
--     -- simp

-- section AddCommMonoid

-- variable [AddCommMonoid α] [Mul α]

-- @[simp]
-- theorem smul_mul [Fintype n] [Monoid R] [DistribMulAction R α] [IsScalarTower R α α] (a : R)
--     (M : Matrix m n α) (N : Matrix n l α) : (a • M) * N = a • (M * N) := by
--   ext
--   apply smul_dotProduct a
-- #align matrix.smul_mul Matrix.smul_mul

-- @[simp]
-- theorem mul_smul [Fintype n] [Monoid R] [DistribMulAction R α] [SMulCommClass R α α]
--     (M : Matrix m n α) (a : R) (N : Matrix n l α) : M * (a • N) = a • (M * N) := by
--   ext
--   apply dotProduct_smul
-- #align matrix.mul_smul Matrix.mul_smul

-- end AddCommMonoid

-- section NonUnitalNonAssocSemiring

-- variable [NonUnitalNonAssocSemiring α]

-- @[simp]
-- protected theorem mul_zero [Fintype n] (M : Matrix m n α) : M * (0 : Matrix n o α) = 0 := by
--   ext
--   apply dotProduct_zero
-- #align matrix.mul_zero Matrix.mul_zero

-- @[simp]
-- protected theorem zero_mul [Fintype m] (M : Matrix m n α) : (0 : Matrix l m α) * M = 0 := by
--   ext
--   apply zero_dotProduct
-- #align matrix.zero_mul Matrix.zero_mul

-- protected theorem mul_add [Fintype n] (L : Matrix m n α) (M N : Matrix n o α) :
--     L * (M + N) = L * M + L * N := by
--   ext
--   apply dotProduct_add
-- #align matrix.mul_add Matrix.mul_add

-- -- !!!
-- protected theorem add_mul [Fintype m] (L M : Matrix l m α) (N : Matrix m n α) :
--     (L + M) * N = L * N + M * N := by
--   ext
--   apply add_dotProduct
-- #align matrix.add_mul Matrix.add_mul

-- instance nonUnitalNonAssocSemiring [Fintype n] : NonUnitalNonAssocSemiring (Matrix n n α) :=
--   { Matrix.addCommMonoid with
--     mul_zero := Matrix.mul_zero
--     zero_mul := Matrix.zero_mul
--     left_distrib := Matrix.mul_add
--     right_distrib := Matrix.add_mul }

-- @[simp]
-- theorem diagonal_mul [Fintype m] [DecidableEq m] (d : m → α) (M : Matrix m n α) (i j) :
--     (diagonal d * M) i j = d i * M i j :=
--   diagonal_dotProduct _ _ _
-- #align matrix.diagonal_mul Matrix.diagonal_mul

-- @[simp]
-- theorem mul_diagonal [Fintype n] [DecidableEq n] (d : n → α) (M : Matrix m n α) (i j) :
--     (M * diagonal d) i j = M i j * d j := by
--   rw [← diagonal_transpose]
--   apply dotProduct_diagonal
-- #align matrix.mul_diagonal Matrix.mul_diagonal

-- @[simp]
-- theorem diagonal_mul_diagonal [Fintype n] [DecidableEq n] (d₁ d₂ : n → α) :
--     diagonal d₁ * diagonal d₂ = diagonal fun i => d₁ i * d₂ i := by
--   ext i j
--   by_cases i = j <;>
--   simp [h]
-- #align matrix.diagonal_mul_diagonal Matrix.diagonal_mul_diagonal

-- theorem diagonal_mul_diagonal' [Fintype n] [DecidableEq n] (d₁ d₂ : n → α) :
--     diagonal d₁ * diagonal d₂ = diagonal fun i => d₁ i * d₂ i :=
--   diagonal_mul_diagonal _ _
-- #align matrix.diagonal_mul_diagonal' Matrix.diagonal_mul_diagonal'

-- theorem smul_eq_diagonal_mul [Fintype m] [DecidableEq m] (M : Matrix m n α) (a : α) :
--     a • M = (diagonal fun _ => a) * M := by
--   ext
--   simp
-- #align matrix.smul_eq_diagonal_mul Matrix.smul_eq_diagonal_mul

-- @[simp]
-- theorem diag_col_mul_row (a b : n → α) : diag (col a * row b) = a * b := by
--   ext
--   simp [Matrix.mul_apply, col, row]
-- #align matrix.diag_col_mul_row Matrix.diag_col_mul_row

-- /-- Left multiplication by a matrix, as an `AddMonoidHom` from matrices to matrices. -/
-- @[simps]
-- def addMonoidHomMulLeft [Fintype m] (M : Matrix l m α) : Matrix m n α →+ Matrix l n α where
--   toFun x := M * x
--   map_zero' := Matrix.mul_zero _
--   map_add' := Matrix.mul_add _
-- #align matrix.add_monoid_hom_mul_left Matrix.addMonoidHomMulLeft

-- /-- Right multiplication by a matrix, as an `AddMonoidHom` from matrices to matrices. -/
-- @[simps]
-- def addMonoidHomMulRight [Fintype m] (M : Matrix m n α) : Matrix l m α →+ Matrix l n α where
--   toFun x := x * M
--   map_zero' := Matrix.zero_mul _
--   map_add' _ _ := Matrix.add_mul _ _ _
-- #align matrix.add_monoid_hom_mul_right Matrix.addMonoidHomMulRight

-- protected theorem sum_mul [Fintype m] (s : Finset β) (f : β → Matrix l m α) (M : Matrix m n α) :
--     (∑ a in s, f a) * M = ∑ a in s, f a * M :=
--   (addMonoidHomMulRight M : Matrix l m α →+ _).map_sum f s
-- #align matrix.sum_mul Matrix.sum_mul

-- protected theorem mul_sum [Fintype m] (s : Finset β) (f : β → Matrix m n α) (M : Matrix l m α) :
--     (M * ∑ a in s, f a) = ∑ a in s, M * f a :=
--   (addMonoidHomMulLeft M : Matrix m n α →+ _).map_sum f s
-- #align matrix.mul_sum Matrix.mul_sum

-- /-- This instance enables use with `smul_mul_assoc`. -/
-- instance Semiring.isScalarTower [Fintype n] [Monoid R] [DistribMulAction R α]
--     [IsScalarTower R α α] : IsScalarTower R (Matrix n n α) (Matrix n n α) :=
--   ⟨fun r m n => Matrix.smul_mul r m n⟩
-- #align matrix.semiring.is_scalar_tower Matrix.Semiring.isScalarTower

-- /-- This instance enables use with `mul_smul_comm`. -/
-- instance Semiring.smulCommClass [Fintype n] [Monoid R] [DistribMulAction R α]
--     [SMulCommClass R α α] : SMulCommClass R (Matrix n n α) (Matrix n n α) :=
--   ⟨fun r m n => (Matrix.mul_smul m r n).symm⟩
-- #align matrix.semiring.smul_comm_class Matrix.Semiring.smulCommClass

-- end NonUnitalNonAssocSemiring

-- section NonAssocSemiring

-- variable [NonAssocSemiring α]

-- @[simp]
-- protected theorem one_mul [Fintype m] [DecidableEq m] (M : Matrix m n α) :
--     (1 : Matrix m m α) * M = M := by
--   ext
--   rw [← diagonal_one, diagonal_mul, one_mul]
-- #align matrix.one_mul Matrix.one_mul

-- @[simp]
-- protected theorem mul_one [Fintype n] [DecidableEq n] (M : Matrix m n α) :
--     M * (1 : Matrix n n α) = M := by
--   ext
--   rw [← diagonal_one, mul_diagonal, mul_one]
-- #align matrix.mul_one Matrix.mul_one

-- instance nonAssocSemiring [Fintype n] [DecidableEq n] : NonAssocSemiring (Matrix n n α) :=
--   { Matrix.nonUnitalNonAssocSemiring with
--     one := 1
--     one_mul := Matrix.one_mul
--     mul_one := Matrix.mul_one
--     natCast := fun n => diagonal fun _ => n
--     natCast_zero := by
--       ext
--       simp [Nat.cast]
--     natCast_succ := fun n => by
--       ext i j
--       by_cases i = j <;>
--       simp [Nat.cast, *]}

-- @[simp]
-- theorem map_mul [Fintype n] {L : Matrix m n α} {M : Matrix n o α} [NonAssocSemiring β]
--     {f : α →+* β} : (L * M).map f = L.map f * M.map f := by
--   ext
--   simp [mul_apply, map_sum]
-- #align matrix.map_mul Matrix.map_mul

-- variable (α n)

-- /-- `Matrix.diagonal` as a `RingHom`. -/
-- @[simps]
-- def diagonalRingHom [Fintype n] [DecidableEq n] : (n → α) →+* Matrix n n α :=
--   { diagonalAddMonoidHom n α with
--     toFun := diagonal
--     map_one' := diagonal_one
--     map_mul' := fun _ _ => (diagonal_mul_diagonal' _ _).symm }
-- #align matrix.diagonal_ring_hom Matrix.diagonalRingHom

-- end NonAssocSemiring















-- end Matrix --/
