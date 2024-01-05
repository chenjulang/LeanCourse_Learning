import Mathlib.LinearAlgebra.Basis

-- 向量空间的基
-- 最终目标?下面里选一个


structure Basis2 where
  /-- `Basis.ofRepr` constructs a basis given an assignment of coordinates to each vector. -/
  ofRepr ::
    /-- `repr` is the linear equivalence sending a vector `x` to its coordinates:
    the `c`s such that `x = ∑ i, c i`. -/
    repr : M ≃ₗ[R] ι →₀ R


-- /-- Each vector space has a basis. -/
-- noncomputable def ofVectorSpace : Basis (ofVectorSpaceIndex K V) K V :=
--   Basis.extend (linearIndependent_empty K V)
-- #align basis.of_vector_space Basis.ofVectorSpace



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



-- -- goal：？
-- theorem eq_ofRepr_eq_repr {b₁ b₂ : Basis ι R M} (h : ∀ x i, b₁.repr x i = b₂.repr x i) : b₁ = b₂ :=
--   repr_injective <| by ext; apply h

-- /-- If the submodule `P` has a basis, `x ∈ P` iff it is a linear combination of basis vectors. -/
-- theorem mem_submodule_iff {P : Submodule R M} (b : Basis ι R P) {x : M} :
--     x ∈ P ↔ ∃ c : ι →₀ R, x = Finsupp.sum c fun i x => x • (b i : M) := by
--   conv_lhs =>
--     rw [← P.range_subtype, ← Submodule.map_top, ← b.span_eq, Submodule.map_span, ← Set.range_comp,
--         ← Finsupp.range_total]
--   simp [@eq_comm _ x, Function.comp, Finsupp.total_apply]


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
