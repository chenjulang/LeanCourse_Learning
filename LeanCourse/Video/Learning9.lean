


-- 线性方程组可解的充分必要条件,与行列式之间的关系：
theorem exists_mulVec_eq_zero_iff' {A : Type*} (K : Type*) [DecidableEq n] [CommRing A]
    [Nontrivial A] [Field K] [Algebra A K] [IsFractionRing A K] {M : Matrix n n A} :
    (∃ (v : _) (_ : v ≠ 0), M.mulVec v = 0) ↔ M.det = 0
    := by
  have : (∃ (v : _) (_ : v ≠ 0), mulVec ((algebraMap A K).mapMatrix M) v = 0) ↔ _ :=
    exists_mulVec_eq_zero_iff_aux
  rw [← RingHom.map_det, IsFractionRing.to_map_eq_zero_iff] at this
  refine' Iff.trans _ this; constructor <;> rintro ⟨v, hv, mul_eq⟩
  · refine' ⟨fun i => algebraMap _ _ (v i), mt (fun h => funext fun i => _) hv, _⟩
    · exact IsFractionRing.to_map_eq_zero_iff.mp (congr_fun h i)
    · ext i
      refine' (RingHom.map_mulVec _ _ _ i).symm.trans _
      rw [mul_eq, Pi.zero_apply, RingHom.map_zero, Pi.zero_apply]
  · letI := Classical.decEq K
    obtain ⟨⟨b, hb⟩, ba_eq⟩ :=
      IsLocalization.exist_integer_multiples_of_finset (nonZeroDivisors A) (Finset.univ.image v)
    choose f hf using ba_eq
    refine'
      ⟨fun i => f _ (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩),
        mt (fun h => funext fun i => _) hv, _⟩
    · have := congr_arg (algebraMap A K) (congr_fun h i)
      rw [hf, Subtype.coe_mk, Pi.zero_apply, RingHom.map_zero, Algebra.smul_def, mul_eq_zero,
        IsFractionRing.to_map_eq_zero_iff] at this
      exact this.resolve_left (nonZeroDivisors.ne_zero hb)
    · ext i
      refine' IsFractionRing.injective A K _
      calc
        algebraMap A K (M.mulVec (fun i : n => f (v i) _) i) =
            ((algebraMap A K).mapMatrix M).mulVec (algebraMap _ K b • v) i := ?_
        _ = 0 := ?_
        _ = algebraMap A K 0 := (RingHom.map_zero _).symm
      · simp_rw [RingHom.map_mulVec, mulVec, dotProduct, Function.comp_apply, hf,
          RingHom.mapMatrix_apply, Pi.smul_apply, smul_eq_mul, Algebra.smul_def]
      · rw [mulVec_smul, mul_eq, Pi.smul_apply, Pi.zero_apply, smul_zero]
