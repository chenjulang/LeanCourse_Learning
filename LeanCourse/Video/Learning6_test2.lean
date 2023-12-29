import Mathlib.LinearAlgebra.Matrix.ToLin



noncomputable section

open LinearMap Matrix Set Submodule

open BigOperators

open Matrix

universe u v w

-- instance {n m} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n] (R) [Fintype R] :
--     Fintype (Matrix m n R) := by unfold Matrix; infer_instance

section ToMatrixRight

variable {R : Type*} [Semiring R]

variable {l m n : Type*}

def Matrix.vecMulLinear2 [Fintype m] (M : Matrix m n R) : (m → R) →ₗ[R] n → R where
  toFun x := M.vecMul x
  map_add' _ _ := funext fun _ => add_dotProduct _ _ _
  map_smul' _ _ := funext fun _ => smul_dotProduct _ _ _

@[simp] theorem Matrix.vecMulLinear_apply2 [Fintype m] (M : Matrix m n R) (x : m → R) :
    M.vecMulLinear x = M.vecMul x := rfl

theorem Matrix.coe_vecMulLinear2 [Fintype m] (M : Matrix m n R) :
    (M.vecMulLinear : _ → _) = M.vecMul := rfl

variable [Fintype m] [DecidableEq m]

@[simp]
theorem Matrix.vecMul_stdBasis2 (M : Matrix m n R) (i j) :
    M.vecMul (LinearMap.stdBasis R (fun _ => R) i 1) j = M i j := by
  have : (∑ i', (if i = i' then 1 else 0) * M i' j) = M i j := by
    simp_rw [boole_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  simp only [vecMul, dotProduct]
  convert this
  split_ifs with h <;> simp only [stdBasis_apply]
  · rw [h, Function.update_same]
  · rw [Function.update_noteq (Ne.symm h), Pi.zero_apply]

theorem range_vecMulLinear2 (M : Matrix m n R) :
    LinearMap.range M.vecMulLinear = span R (range M) := by
  letI := Classical.decEq m
  simp_rw [range_eq_map, ← iSup_range_stdBasis, Submodule.map_iSup, range_eq_map, ←
    Ideal.span_singleton_one, Ideal.span, Submodule.map_span, image_image, image_singleton,
    Matrix.vecMulLinear_apply, iSup_span, range_eq_iUnion, iUnion_singleton_eq_range,
    LinearMap.stdBasis, coe_single]
  unfold vecMul
  simp_rw [single_dotProduct, one_mul]

theorem Matrix.vecMul_injective_iff2 {R : Type*} [CommRing R] {M : Matrix m n R} :
    Function.Injective M.vecMul ↔ LinearIndependent R (fun i ↦ M i) := by
  rw [← coe_vecMulLinear]
  simp only [← LinearMap.ker_eq_bot, Fintype.linearIndependent_iff, Submodule.eq_bot_iff,
    LinearMap.mem_ker, vecMulLinear_apply]
  refine ⟨fun h c h0 ↦ congr_fun <| h c ?_, fun h c h0 ↦ funext <| h c ?_⟩
  · rw [← h0]
    ext i
    simp [vecMul, dotProduct]
  · rw [← h0]
    ext j
    simp [vecMul, dotProduct]

def LinearMap.toMatrixRight'2 : ((m → R) →ₗ[R] n → R) ≃ₗ[Rᵐᵒᵖ] Matrix m n R where
  toFun f i j := f (stdBasis R (fun _ => R) i 1) j
  invFun := Matrix.vecMulLinear
  right_inv M := by
    ext i j
    simp only [Matrix.vecMul_stdBasis, Matrix.vecMulLinear_apply]
  left_inv f := by
    apply (Pi.basisFun R m).ext
    intro j; ext i
    simp only [Pi.basisFun_apply, Matrix.vecMul_stdBasis, Matrix.vecMulLinear_apply]
  map_add' f g := by
    ext i j
    simp only [Pi.add_apply, LinearMap.add_apply, Matrix.add_apply]
  map_smul' c f := by
    ext i j
    simp only [Pi.smul_apply, LinearMap.smul_apply, RingHom.id_apply, Matrix.smul_apply]

/-- A `Matrix m n R` is linearly equivalent over `Rᵐᵒᵖ` to a linear map `(m → R) →ₗ[R] (n → R)`,
by having matrices act by right multiplication. -/
abbrev Matrix.toLinearMapRight'2 : Matrix m n R ≃ₗ[Rᵐᵒᵖ] (m → R) →ₗ[R] n → R :=
  LinearEquiv.symm LinearMap.toMatrixRight'

@[simp]
theorem Matrix.toLinearMapRight'_apply2 (M : Matrix m n R) (v : m → R) :
    -- porting note: needs type annotation for `⇑` to resolve
    (Matrix.toLinearMapRight' : _ ≃ₗ[Rᵐᵒᵖ] _) M v = M.vecMul v :=
  rfl

@[simp]
theorem Matrix.toLinearMapRight'_mul2 [Fintype l] [DecidableEq l] (M : Matrix l m R)
    (N : Matrix m n R) :
    -- porting note: needs type annotation for `⇑` to resolve
    (Matrix.toLinearMapRight' : _ ≃ₗ[Rᵐᵒᵖ] _) (M * N) =
      ((Matrix.toLinearMapRight' : _ ≃ₗ[Rᵐᵒᵖ] _) N).comp
        ((Matrix.toLinearMapRight' : _ ≃ₗ[Rᵐᵒᵖ] _) M) :=
  LinearMap.ext fun _x => (vecMul_vecMul _ M N).symm

theorem Matrix.toLinearMapRight'_mul_apply2 [Fintype l] [DecidableEq l] (M : Matrix l m R)
    (N : Matrix m n R) (x) :
    -- porting note: needs type annotation for `⇑` to resolve
    (Matrix.toLinearMapRight' : _ ≃ₗ[Rᵐᵒᵖ] _) (M * N) x =
      (Matrix.toLinearMapRight' : _ ≃ₗ[Rᵐᵒᵖ] _) N
        ((Matrix.toLinearMapRight' : _ ≃ₗ[Rᵐᵒᵖ] _) M x) :=
  (vecMul_vecMul _ M N).symm

@[simp]
theorem Matrix.toLinearMapRight'_one2:
    -- porting note: needs type annotation for `⇑` to resolve
    (Matrix.toLinearMapRight' : _ ≃ₗ[Rᵐᵒᵖ] _) (1 : Matrix m m R) = LinearMap.id := by
  ext
  simp [LinearMap.one_apply, stdBasis_apply]

/-- If `M` and `M'` are each other's inverse matrices, they provide an equivalence between `n → A`
and `m → A` corresponding to `M.vecMul` and `M'.vecMul`. -/
@[simps]
def Matrix.toLinearEquivRight'OfInv2 [Fintype n] [DecidableEq n] {M : Matrix m n R}
    {M' : Matrix n m R} (hMM' : M * M' = 1) (hM'M : M' * M = 1) : (n → R) ≃ₗ[R] m → R :=
  { -- porting note: needs type annotation for `⇑` to resolve
    (LinearMap.toMatrixRight' : _ ≃ₗ[Rᵐᵒᵖ] _).symm
      M' with
    -- porting note: needs type annotation for `⇑` to resolve
    toFun := (Matrix.toLinearMapRight' : _ ≃ₗ[Rᵐᵒᵖ] _) M'
    -- porting note: needs type annotation for `⇑` to resolve
    invFun := (Matrix.toLinearMapRight' : _ ≃ₗ[Rᵐᵒᵖ] _) M
    left_inv := fun x => by
      dsimp only -- porting note: needed due to non-flat structures
      rw [← Matrix.toLinearMapRight'_mul_apply, hM'M, Matrix.toLinearMapRight'_one, id_apply]
    right_inv := fun x => by
      dsimp only -- porting note: needed due to non-flat structures
      rw [← Matrix.toLinearMapRight'_mul_apply, hMM', Matrix.toLinearMapRight'_one, id_apply] }

end ToMatrixRight


section mulVec

  variable {R : Type*} [CommSemiring R]

  variable {k l m n : Type*}

  variable [Fintype n]

  /-- `Matrix.mulVec M` is a linear map. -/
  def Matrix.mulVecLin2 [Fintype n] (M : Matrix m n R) : (n → R) →ₗ[R] m → R where
    toFun := M.mulVec
    map_add' _ _ := funext fun _ => dotProduct_add _ _ _
    map_smul' _ _ := funext fun _ => dotProduct_smul _ _ _

  theorem Matrix.coe_mulVecLin2 [Fintype n] (M : Matrix m n R) :
      (M.mulVecLin : _ → _) = M.mulVec := rfl

  @[simp]
  theorem Matrix.mulVecLin_apply2 [Fintype n] (M : Matrix m n R) (v : n → R) :
      M.mulVecLin v = M.mulVec v :=
    rfl

  @[simp]
  theorem Matrix.mulVecLin_zero2 [Fintype n] : Matrix.mulVecLin (0 : Matrix m n R) = 0 :=
    LinearMap.ext zero_mulVec

  @[simp]
  theorem Matrix.mulVecLin_add2 [Fintype n] (M N : Matrix m n R) :
      (M + N).mulVecLin = M.mulVecLin + N.mulVecLin :=
    LinearMap.ext fun _ => add_mulVec _ _ _

  @[simp] theorem Matrix.mulVecLin_transpose2 [Fintype m] (M : Matrix m n R) :
      Mᵀ.mulVecLin = M.vecMulLinear := by
    ext; simp [mulVec_transpose]

  @[simp] theorem Matrix.vecMulLinear_transpose2 [Fintype n] (M : Matrix m n R) :
      Mᵀ.vecMulLinear = M.mulVecLin := by
    ext; simp [vecMul_transpose]

  theorem Matrix.mulVecLin_submatrix2 [Fintype n] [Fintype l] (f₁ : m → k) (e₂ : n ≃ l)
      (M : Matrix k l R) :
      (M.submatrix f₁ e₂).mulVecLin = funLeft R R f₁ ∘ₗ M.mulVecLin ∘ₗ funLeft _ _ e₂.symm :=
    LinearMap.ext fun _ => submatrix_mulVec_equiv _ _ _ _

  theorem Matrix.mulVecLin_reindex2 [Fintype n] [Fintype l] (e₁ : k ≃ m) (e₂ : l ≃ n)
      (M : Matrix k l R) :
      (reindex e₁ e₂ M).mulVecLin =
        ↑(LinearEquiv.funCongrLeft R R e₁.symm) ∘ₗ
          M.mulVecLin ∘ₗ ↑(LinearEquiv.funCongrLeft R R e₂) :=
    Matrix.mulVecLin_submatrix _ _ _

  variable [Fintype n]

  @[simp]
  theorem Matrix.mulVecLin_one2 [DecidableEq n] :
      Matrix.mulVecLin (1 : Matrix n n R) = LinearMap.id := by
    ext; simp [Matrix.one_apply, Pi.single_apply]

  @[simp]
  theorem Matrix.mulVecLin_mul2 [Fintype m] (M : Matrix l m R) (N : Matrix m n R) :
      Matrix.mulVecLin (M * N) = (Matrix.mulVecLin M).comp (Matrix.mulVecLin N) :=
    LinearMap.ext fun _ => (mulVec_mulVec _ _ _).symm

  theorem Matrix.ker_mulVecLin_eq_bot_iff2 {M : Matrix m n R} :
      (LinearMap.ker M.mulVecLin) = ⊥ ↔ ∀ v, M.mulVec v = 0 → v = 0 := by
    simp only [Submodule.eq_bot_iff, LinearMap.mem_ker, Matrix.mulVecLin_apply]

  theorem Matrix.mulVec_stdBasis2 [DecidableEq n] (M : Matrix m n R) (i j) :
      M.mulVec (LinearMap.stdBasis R (fun _ => R) j 1) i = M i j :=
    (congr_fun (Matrix.mulVec_single _ _ (1 : R)) i).trans <| mul_one _

  @[simp]
  theorem Matrix.mulVec_stdBasis_apply2 [DecidableEq n] (M : Matrix m n R) (j) :
      M.mulVec (LinearMap.stdBasis R (fun _ => R) j 1) = Mᵀ j :=
    funext fun i => Matrix.mulVec_stdBasis M i j

  theorem Matrix.range_mulVecLin2 (M : Matrix m n R) :
      LinearMap.range M.mulVecLin = span R (range Mᵀ) := by
    rw [← vecMulLinear_transpose, range_vecMulLinear]

end mulVec

section ToMatrix'

  variable {R : Type*} [CommSemiring R]

  variable {k l m n : Type*} [DecidableEq n] [Fintype n]

  theorem Matrix.range_toLin'2 (M : Matrix m n R) :
      LinearMap.range (Matrix.toLin' M) = span R (range Mᵀ) :=
    Matrix.range_mulVecLin2 _

end ToMatrix'

end
