import Mathlib.LinearAlgebra.Basis
import LeanCourse.Video.Learning4

-- 学习策略：从已知到未知，逐个符号解释意思，就能解锁所有符号结构的使用了。分解到最细的知识点就是成功了。
-- 基的变换： basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix

-- 向量空间的基 -- 这集跳过，不做视频。材料不足。
-- 最终目标:任何向量可以由基线性组合得到，这节很容易的一个定理。
universe u

open Function Set Submodule
open BigOperators

variable {ι : Type*} {ι' : Type*} {R : Type*} {R₂ : Type*} {K : Type*}
variable {M : Type*} {M' M'' : Type*} {V : Type u} {V' : Type*}
variable [Semiring R]
variable [AddCommMonoid M] [Module R M] [AddCommMonoid M'] [Module R M']
variable (ι R M)


structure Basis2 where
/-- `Basis.ofRepr` constructs a basis given an assignment of coordinates to each vector. -/
ofRepr ::
  /-- `repr` is the linear equivalence sending a vector `x` to its coordinates:
  the `c`s such that `x = ∑ i, c i`. -/
  repr : M ≃ₗ[R] ι →₀ R

-- 这里定义的基，只需要满足性质repr，repr是一个等价映射，它能将空间M中的元素，映射成一个映射：按索引来映射每一个分量的一个映射。


-- 从哪里看出：参数repr，该参数是一个从向量到坐标的线性等价映射（linear equivalence）
-- 假设我们有一个向量空间 M，其中的向量由三个分量组成，可以表示为三维实数向量空间。
-- 指标集合 ι 是 {1, 2, 3}，域 R 是实数域。
-- 那么，M ≃ₗ[ℝ] ι →₀ ℝ 表示一个线性等价映射，它将三维实数向量空间中的向量映射到
-- 由 {1, 2, 3} 到实数域的有限线性组合上。
-- 具体来说，假设我们有一个向量 v = (2.5, -1.3, 0)，它在基 {e₁, e₂, e₃} 下的坐标
-- 表示是 {2.5, -1.3, 0}。那么，根据线性等价映射 M ≃ₗ[ℝ] ι →₀ ℝ，我们可以
-- 将向量 v 映射到指标集合 {1, 2, 3} 到实数域的有限线性组合上，即 {1 → 2.5, 2 → -1.3, 3 → 0}。



-- #check Basis2.repr -- : M ≃ₗ[R] ι →₀ R
-- 什么是线性等价映射≃ₗ？
  -- 一个从 V 到 W 的映射 f 被称为线性等价映射，如果满足以下条件：
  -- 线性性质：对于任意的向量 u 和 v，以及标量 c，有 f(u + v) = f(u) + f(v) 和 f(cu) = cf(u)。
  -- 双射性质：映射 f 是一对一且满射的。也就是说，对于任意的向量 w ∈ W，存在唯一的向量 v ∈ V，使得 f(v) = w。



namespace Basis
  variable (b b₁ : Basis ι R M) (i : ι) (c : R) (x : M)

  -- theorem coe_repr_symm2 : ↑b.repr.symm = Finsupp.total ι M R b
  -- := by
  --   refine' LinearMap.ext _
  --   intros v
  --   exact b.repr_symm_apply v


  -- theorem repr_total2 (v) :
  -- b.repr (Finsupp.total _ _ _ b v)
  -- -- 把b理解成（3，0）映射成{1=>3,2=>0}即（3,0）?
  -- -- （0，1）映射成{1=>0,2=>1}即(0,1)?
  -- -- 这样的映射（将向量映射成“映射”）
  -- = v
  --   := by
  --   rw [← b.coe_repr_symm2]
  --   exact b.repr.apply_symm_apply v -- todo

  -- 基是线性独立的
  protected theorem linearIndependent2
  : LinearIndependent2 R b
    := by
    refine' linearIndependent_iff.2 _
    intros l hl
    calc
      l
      = b.repr (Finsupp.total _ _ _ b l) -- 如何理解b.repr (Finsupp.total _ _ _ b l)
        := by
        exact (b.repr_total l).symm
      _ = 0
        := by
        rw [hl, LinearEquiv.map_zero] --todo
    done



end Basis



/-- If the submodule `P` has a basis, `x ∈ P` iff it is a linear combination of basis vectors. -/
theorem mem_submodule_iff {P : Submodule R M} (b : Basis ι R P) {x : M} :
x ∈ P
↔
∃ c : ι →₀ R, x = Finsupp.sum c fun i x => x • (b i : M)
  := by
  -- constructor
  -- · sorry
  -- · intros h1
  --   rw [← P.range_subtype, ← Submodule.map_top, ← b.span_eq, Submodule.map_span, ← Set.range_comp,
  --       ← Finsupp.range_total]
  --   simp only [coeSubtype, LinearMap.mem_range]
  conv_lhs => -- conv_lhs是什么意思？
    rw [← P.range_subtype, ← Submodule.map_top, ← b.span_eq, Submodule.map_span, ← Set.range_comp,
        ← Finsupp.range_total]
  simp [@eq_comm _ x, Function.comp, Finsupp.total_apply]

















-- /-- Each vector space has a basis. -/
-- noncomputable def ofVectorSpace : Basis2 (ofVectorSpaceIndex K V) K V :=
--   Basis.extend (linearIndependent_empty K V)



-- protected theorem linearIndependent : LinearIndependent R b :=
--   linearIndependent_iff.mpr fun l hl =>
--     calc
--       l = b.repr (Finsupp.total _ _ _ b l) := (b.repr_total l).symm
--       _ = 0 := by rw [hl, LinearEquiv.map_zero]

-- theorem eq_bot_of_rank_eq_zero [NoZeroDivisors R] (b : Basis ι R M) (N : Submodule R M)
--     (rank_eq : ∀ {m : ℕ} (v : Fin m → N), LinearIndependent R ((↑) ∘ v : Fin m → M) → m = 0) :
--     N = ⊥ := by
--   rw [Submodule.eq_bot_iff]
--   intro x hx
--   contrapose! rank_eq with x_ne
--   refine' ⟨1, fun _ => ⟨x, hx⟩, _, one_ne_zero⟩
--   rw [Fintype.linearIndependent_iff]
--   rintro g sum_eq i
--   cases' i with _ hi
--   simp only [Function.const_apply, Fin.default_eq_zero, Submodule.coe_mk, Finset.univ_unique,
--     Function.comp_const, Finset.sum_singleton] at sum_eq
--   convert (b.smul_eq_zero.mp sum_eq).resolve_right x_ne


-- protected noncomputable def mk : Basis ι R M :=
--   .ofRepr
--     { hli.repr.comp (LinearMap.id.codRestrict _ fun _ => hsp Submodule.mem_top) with
--       invFun := Finsupp.total _ _ _ v
--       left_inv := fun x => hli.total_repr ⟨x, _⟩
--       right_inv := fun _ => hli.repr_eq rfl }



-- theorem repr_injective2 : Injective (repr : Basis2 ι R M → M ≃ₗ[R] ι →₀ R) := fun f g h => by
--   cases f; cases g; congr

-- goal：？
-- theorem eq_ofRepr_eq_repr {b₁ b₂ : Basis2 ι R M} (h : ∀ x i, b₁.repr x i = b₂.repr x i) : b₁ = b₂ :=
--   repr_injective2 <| by ext; apply h



-- theorem Basis.mem_submodule_iff' {P : Submodule R M} (b : Basis ι R P) {x : M} :
--     x ∈ P ↔ ∃ c : ι → R, x = ∑ i, c i • (b i : M) :=
--   b.mem_submodule_iff.trans <|
--     Finsupp.equivFunOnFinite.exists_congr_left.trans <|
--       exists_congr fun c => by simp [Finsupp.sum_fintype, Finsupp.equivFunOnFinite]

-- theorem maximal [Nontrivial R] (b : Basis ι R M) : b.linearIndependent.Maximal := fun w hi h => by
--   -- If `w` is strictly bigger than `range b`,
--   apply le_antisymm h
--   -- then choose some `x ∈ w \ range b`,
--   intro x p
--   by_contra q
--   -- and write it in terms of the basis.
--   have e := b.total_repr x
--   -- This then expresses `x` as a linear combination
--   -- of elements of `w` which are in the range of `b`,
--   let u : ι ↪ w :=
--     ⟨fun i => ⟨b i, h ⟨i, rfl⟩⟩, fun i i' r =>
--       b.injective (by simpa only [Subtype.mk_eq_mk] using r)⟩
--   simp_rw [Finsupp.total_apply] at e
--   change ((b.repr x).sum fun (i : ι) (a : R) ↦ a • (u i : M)) = ((⟨x, p⟩ : w) : M) at e
--   rw [← Finsupp.sum_embDomain (f := u) (g := fun x r ↦ r • (x : M)), ← Finsupp.total_apply] at e
--   -- Now we can contradict the linear independence of `hi`
--   refine' hi.total_ne_of_not_mem_support _ _ e
--   simp only [Finset.mem_map, Finsupp.support_embDomain]
--   rintro ⟨j, -, W⟩
--   simp only [Embedding.coeFn_mk, Subtype.mk_eq_mk] at W
--   apply q ⟨j, W⟩
-- #align basis.maximal Basis.maximal

-- /-- A linear independent family of vectors spanning the whole module is a basis. -/
-- protected noncomputable def mk : Basis ι R M :=
--   .ofRepr
--     { hli.repr.comp (LinearMap.id.codRestrict _ fun _ => hsp Submodule.mem_top) with
--       invFun := Finsupp.total _ _ _ v
--       left_inv := fun x => hli.total_repr ⟨x, _⟩
--       right_inv := fun _ => hli.repr_eq rfl }


-- theorem basis_toMatrix_mul [DecidableEq κ] (b₁ : Basis ι R M) (b₂ : Basis ι' R M) (b₃ : Basis κ R N)
--     (A : Matrix ι' κ R) : b₁.toMatrix b₂ * A = LinearMap.toMatrix b₃ b₁ (toLin b₃ b₂ A) := by
--   have := basis_toMatrix_mul_linearMap_toMatrix b₃ b₁ b₂ (Matrix.toLin b₃ b₂ A)
--   rwa [LinearMap.toMatrix_toLin] at this
