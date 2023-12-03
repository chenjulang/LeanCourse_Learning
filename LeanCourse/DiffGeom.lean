import Mathlib.Geometry.Manifold.VectorBundle.SmoothSection
import Mathlib.Geometry.Manifold.VectorBundle.Hom
import Mathlib.Geometry.Manifold.VectorBundle.Pullback
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.Instances.sphere

/-! Missing bits that should be added to mathlib after cleaning them up -/
open Set BigOperators ENNReal

section PiLp_smooth

variable
  {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {ι : Type*} [Fintype ι]
  {p : ℝ≥0∞} [hp : Fact (1 ≤ p)] {α : ι → Type*} {n : WithTop ℕ} (i : ι)
  [∀i, NormedAddCommGroup (α i)] [∀ i, NormedSpace 𝕜 (α i)]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]


lemma PiLp.norm_coord_le_norm (x : PiLp p α) (i : ι) : ‖x i‖ ≤ ‖x‖ := by
  rcases p.trichotomy with (rfl | rfl | h)
  · exact False.elim (lt_irrefl _ (zero_lt_one.trans_le hp.out))
  · rw [PiLp.norm_eq_ciSup]
    exact le_ciSup (f := fun i ↦ ‖x i‖) (finite_range _).bddAbove i
  · calc ‖x i‖
        ≤ (‖x i‖ ^ p.toReal) ^ (1 / p.toReal) := by
          rw [← Real.rpow_mul (norm_nonneg _), mul_one_div_cancel h.ne', Real.rpow_one]
      _ ≤ ‖x‖ := by
          have A : ∀ j, 0 ≤ ‖x j‖ ^ p.toReal :=
            fun j ↦ Real.rpow_nonneg_of_nonneg (norm_nonneg _) _
          simp only [PiLp.norm_eq_sum h, one_mul, LinearMap.coe_mk]
          apply Real.rpow_le_rpow (A i)
          · exact Finset.single_le_sum (fun j _ ↦ A j) (Finset.mem_univ _)
          · exact div_nonneg zero_le_one h.le

lemma PiLp.contDiff_coord :
  ContDiff 𝕜 n (fun x : PiLp p α ↦ x i) :=
let F : PiLp p α →ₗ[𝕜] α i :=
  { toFun := fun x ↦ x i
    map_add' := fun x y ↦ rfl
    map_smul' := fun x c ↦ rfl }
(F.mkContinuous 1 (fun x ↦ by simpa using PiLp.norm_coord_le_norm x i)).contDiff

variable {f : E → PiLp p α} {s : Set E} {x : E}
lemma PiLp.contDiffWithinAt_iff_coord :
  ContDiffWithinAt 𝕜 n f s x ↔ ∀ i, ContDiffWithinAt 𝕜 n (fun x ↦ f x i) s x := by
  classical
  constructor
  · intro h i
    have : ContDiff 𝕜 n (fun x : PiLp p α ↦ x i) := PiLp.contDiff_coord i
    exact this.comp_contDiffWithinAt h
  · intro h
    let F : ∀ (i : ι), α i →ₗ[𝕜] PiLp p α := fun i ↦
    { toFun := fun y ↦ Function.update 0 i y
      map_add' := by
        intro y y'
        ext j
        by_cases h : j = i
        · rw [h]; simp
        · simp [h]
      map_smul' := by
        intro c x
        ext j
        by_cases h : j = i
        · rw [h]; simp
        · simp [h] }
    let G : ∀ (i : ι), α i →L[𝕜] PiLp p α := fun i ↦ by
      refine (F i).mkContinuous 1 (fun x ↦ ?_)
      rcases p.trichotomy with (rfl | rfl | h)
      · exact False.elim (lt_irrefl _ (zero_lt_one.trans_le hp.out))
      · haveI : Nonempty ι := ⟨i⟩
        simp only [PiLp.norm_eq_ciSup, LinearMap.coe_mk, one_mul]
        refine ciSup_le ?_
        simp only [AddHom.coe_mk, ne_eq]
        intro j
        by_cases hji : j = i
        · rw [hji]; simp [Function.update_same]
        · simp only [hji, Function.update_noteq, Ne.def, not_false_iff, Pi.zero_apply, norm_zero,
            norm_nonneg]
      · have : (fun j ↦ ‖Function.update (0 : ∀ i, α i) i x j‖ ^ p.toReal) =
          (fun j ↦ if j = i then ‖x‖ ^ p.toReal else 0)
        · ext j
          by_cases hji : j = i
          · rw [hji]; simp
          · simp [hji, h.ne']
        simp only [LinearMap.coe_mk, AddHom.coe_mk, PiLp.norm_eq_sum h, ne_eq, this,
          Finset.sum_ite_eq', Finset.mem_univ, ite_true, one_div, one_mul]
        rw [← Real.rpow_mul (norm_nonneg _), mul_inv_cancel h.ne', Real.rpow_one]
    have : ContDiffWithinAt 𝕜 n (fun x ↦ (∑ i : ι, G i ((f x) i))) s x
    · refine ContDiffWithinAt.sum (fun i _ ↦ ?_)
      exact (G i).contDiff.comp_contDiffWithinAt (h i)
    convert this with x
    ext j
    simp
    change f x j = (∑ i : ι, Function.update (0 : ∀ i, α i) i (f x i)) j
    rw [Finset.sum_apply]
    have : ∀ i, Function.update (0 : ∀ i, α i) i (f x i) j = (if j = i then f x j else 0)
    · intro i
      by_cases h : j = i
      · rw [h]; simp
      · simp [h]
    simp [this]

lemma PiLp.contDiffAt_iff_coord :
    ContDiffAt 𝕜 n f x ↔ ∀ i, ContDiffAt 𝕜 n (fun x ↦ f x i) x := by
  simp [← contDiffWithinAt_univ, PiLp.contDiffWithinAt_iff_coord]

lemma PiLp.contDiffOn_iff_coord :
    ContDiffOn 𝕜 n f s ↔ ∀ i, ContDiffOn 𝕜 n (fun x ↦ f x i) s := by
  simp_rw [ContDiffOn, PiLp.contDiffWithinAt_iff_coord]
  tauto

lemma PiLp.contDiff_iff_coord :
    ContDiff 𝕜 n f ↔ ∀ i, ContDiff 𝕜 n (fun x ↦ f x i) := by
  simp [← contDiffOn_univ, PiLp.contDiffOn_iff_coord]

end PiLp_smooth

section Icc

open unitInterval ChartedSpace
attribute [local instance] Real.fact_zero_lt_one

@[simp]
lemma chartAt_unitInterval (x : I) : chartAt (EuclideanHalfSpace 1) x =
    if (x : ℝ) < 1 then IccLeftChart (0 : ℝ) 1 else IccRightChart 0 1 := by
  rfl

end Icc
