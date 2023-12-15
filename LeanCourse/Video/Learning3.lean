import Mathlib.LinearAlgebra.Matrix.Determinant
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.GroupTheory.Perm.Sign
import Mathlib.Data.Real.Sqrt


-- set_option trace.Meta.synthInstance true

universe u v w z

open Equiv Equiv.Perm Finset Function

namespace Matrix --目的是避免模糊定义mul_apply

  open Matrix BigOperators

  variable {m n : Type*} [DecidableEq n] [Fintype n] [DecidableEq m] [Fintype m]
  variable {R : Type v} [CommRing R]

  local notation "ε " σ:arg => ((sign σ : ℤ) : R)

-- -----/行列式

-- 原来有toFun的结构，直接写名词的话，它要用toFun来替换，
-- 所以detRowAlternating2具体类型应该是和这个相同(↑detRowAlternating2).toFun : (?m.32939 → ?m.32939 → ?m.32941) → ?m.32941
-- 因此detRowAlternating2 M的类型就是R
  def detRowAlternating2
  : AlternatingMap R (n → R) R n  --- 最后这个参数n属于补充说明,实际形式上只需传三个参数即可
  :=
  MultilinearMap.alternatization (
    (MultilinearMap.mkPiAlgebra R n R).compLinearMap
      LinearMap.proj
  )
  -- 按道理这个实例应该也是属于这个类型(?m.33147 → ?m.33147 → ?m.33149) → ?m.33149



  abbrev det2 (M : Matrix n n R): R :=
    -- have h1 := detRowAlternating2 M
    detRowAlternating2 M -- 这里为什么类型是R，因为detRowAlternating2相当于detRowAlternating2.toFun
    -- 也就是(?m.33147 → ?m.33147 → ?m.33149) → ?m.33149
  #check detRowAlternating2.toFun


  @[simp]
  theorem det_mul2 (M N : Matrix n n R) : det (M * N) = det M * det N
  := by
    have h1 :det (M * N) = det M * det N :=
      calc
          det (M * N) = ∑ p : n → n, ∑ σ : Perm n, ε σ * ∏ i, M (σ i) (p i) * N (p i) i := by
            simp only [det_apply', mul_apply, prod_univ_sum, mul_sum, Fintype.piFinset_univ]
            rw [Finset.sum_comm]
          _ =
              ∑ p in (@univ (n → n) _).filter Bijective,
                ∑ σ : Perm n, ε σ * ∏ i, M (σ i) (p i) * N (p i) i :=
            (Eq.symm <|
              sum_subset (filter_subset _ _) fun f _ hbij =>
                det_mul_aux <| by simpa only [true_and_iff, mem_filter, mem_univ] using hbij)
          _ = ∑ τ : Perm n, ∑ σ : Perm n, ε σ * ∏ i, M (σ i) (τ i) * N (τ i) i :=
            (sum_bij (fun p h => Equiv.ofBijective p (mem_filter.1 h).2) (fun _ _ => mem_univ _)
              (fun _ _ => rfl) (fun _ _ _ _ h => by injection h) fun b _ =>
              ⟨b, mem_filter.2 ⟨mem_univ _, b.bijective⟩, coe_fn_injective rfl⟩)
          _ = ∑ σ : Perm n, ∑ τ : Perm n, (∏ i, N (σ i) i) * ε τ * ∏ j, M (τ j) (σ j) := by
            simp only [mul_comm, mul_left_comm, prod_mul_distrib, mul_assoc]
          _ = ∑ σ : Perm n, ∑ τ : Perm n, (∏ i, N (σ i) i) * (ε σ * ε τ) * ∏ i, M (τ i) i :=
            (sum_congr rfl fun σ _ =>
              Fintype.sum_equiv (Equiv.mulRight σ⁻¹) _ _ fun τ => by
                have : (∏ j, M (τ j) (σ j)) = ∏ j, M ((τ * σ⁻¹) j) j := by
                  rw [← (σ⁻¹ : _ ≃ _).prod_comp]
                  simp only [Equiv.Perm.coe_mul, apply_inv_self, Function.comp_apply]
                have h : ε σ * ε (τ * σ⁻¹) = ε τ :=
                  calc
                    ε σ * ε (τ * σ⁻¹) = ε (τ * σ⁻¹ * σ) := by
                      rw [mul_comm, sign_mul (τ * σ⁻¹)]
                      simp only [Int.cast_mul, Units.val_mul]
                    _ = ε τ := by simp only [inv_mul_cancel_right]

                simp_rw [Equiv.coe_mulRight, h]
                simp only [this])
          _ = det M * det N := by
            simp only [det_apply', Finset.mul_sum, mul_comm, mul_left_comm, mul_assoc]
    exact h1
    done

end Matrix
