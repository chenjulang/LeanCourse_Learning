import Mathlib.LinearAlgebra.Matrix.Determinant
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.GroupTheory.Perm.Sign
import Mathlib.Data.Real.Sqrt


-- set_option trace.Meta.synthInstance true
-- set_option maxHeartbeats 0


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
  -- have h1:= (
  --   (MultilinearMap.mkPiAlgebra R n R).compLinearMap
  --     LinearMap.proj
  -- )
  -- have h1fun:= h1.toFun
  MultilinearMap.alternatization (
    (MultilinearMap.mkPiAlgebra R n R).compLinearMap
      LinearMap.proj
  )

-- 问题：v是什么？
-- MultilinearMap R (fun x（x就是n） ↦ n → R) R 也就是(n → n → R) → R


  abbrev det2 (M : Matrix n n R): R :=
    -- have h1 := detRowAlternating2 M
    detRowAlternating2 M -- 这里为什么类型是R，因为detRowAlternating2相当于detRowAlternating2.toFun
    -- 也就是(?m.33147 → ?m.33147 → ?m.33149) → ?m.33149
  #check detRowAlternating2.toFun -- 所以上面M不是参数，而是被作用了，detRowAlternating2是一个映射作用到M上了




  lemma hhh1 (M N : Matrix n n R) :∑ p : n → n, ∑ σ : Perm n, ε σ * ∏ i, M (σ i) (p i) * N (p i) i =
      ∑ p in (@univ (n → n) _).filter Bijective, ∑ σ : Perm n, ε σ * ∏ i, M (σ i) (p i) * N (p i) i
      := by
      apply Eq.symm
      apply sum_subset
      · intro h1 h2
        exact mem_univ h1
      intros h3 h4 h5
      apply det_mul_aux
      simp only [true_and_iff] at h5
      simp only [mem_filter] at h5
      simp only [mem_univ] at h5
      simp at h5
      apply h5

  lemma hhh2 (M N : Matrix n n R) : ∑ p in (@univ (n → n) _).filter Bijective, ∑ σ : Perm n, ε σ * ∏ i, M (σ i) (p i) * N (p i) i
      = ∑ τ : Perm n, ∑ σ : Perm n, ε σ * ∏ i, M (σ i) (τ i) * N (τ i) i
      := by
      -- apply sum_bij
      -- · intro h1
      --   intro h2
      --   simp only [mem_univ]
      -- · intro h3
      --   intro h4
      --   simp only
      --   sorry
      -- · intro h5
      --   intro h6
      --   intro h7
      --   intro h8
      --   intro h9
      --   sorry
      -- · intro h10
      --   intro h11
      --   simp only [mem_univ, forall_true_left, mem_filter, true_and]
      --   sorry
      -- · intro h12
      --   intro h13
      --   exact Equiv.refl n
      exact (sum_bij (fun p h => Equiv.ofBijective p (mem_filter.1 h).2) (fun _ _ => mem_univ _)
              (fun _ _ => rfl) (fun _ _ _ _ h => by injection h) fun b _ =>
              ⟨b, mem_filter.2 ⟨mem_univ _, b.bijective⟩, coe_fn_injective rfl⟩)

  lemma hhh3 (M N : Matrix n n R) : ∑ σ : Perm n, ∑ τ : Perm n, (∏ i, N (σ i) i) * ε τ * ∏ j, M (τ j) (σ j)
      = ∑ σ : Perm n, ∑ τ : Perm n, (∏ i, N (σ i) i) * (ε σ * ε τ) * ∏ i, M (τ i) i
      := by
      exact (sum_congr rfl fun σ _ =>
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

  -- @[simp]
  theorem det_mul2 (M N : Matrix n n R) : det (M * N) = det M * det N
  := by
    have h1 :det (M * N) = det M * det N :=
      calc
          det (M * N) = ∑ p : n → n, ∑ σ : Perm n, ε σ * ∏ i, M (σ i) (p i) * N (p i) i := by
            simp only [det_apply']
            simp only [mul_apply]
            simp only [prod_univ_sum]
            simp only [mul_sum]
            simp only [Fintype.piFinset_univ]
            rw [Finset.sum_comm]
          _ = ∑ p in (@univ (n → n) _).filter Bijective,
                ∑ σ : Perm n, ε σ * ∏ i, M (σ i) (p i) * N (p i) i
            := by exact (hhh1 M N)
          _ = ∑ τ : Perm n, ∑ σ : Perm n, ε σ * ∏ i, M (σ i) (τ i) * N (τ i) i
            := by exact (hhh2 M N)
          _ = ∑ σ : Perm n, ∑ τ : Perm n, (∏ i, N (σ i) i) * ε τ * ∏ j, M (τ j) (σ j) := by
            simp only [mul_comm, mul_left_comm, prod_mul_distrib, mul_assoc]
          _ = ∑ σ : Perm n, ∑ τ : Perm n, (∏ i, N (σ i) i) * (ε σ * ε τ) * ∏ i, M (τ i) i
            := by exact (hhh3 M N)
          _ = det M * det N
            := by
            simp only [det_apply', Finset.mul_sum, mul_comm, mul_left_comm, mul_assoc]
            -- simp only [det_apply']
            -- simp only [Finset.mul_sum]
            -- simp only [mul_comm]
            -- simp only [mul_left_comm]
            -- simp only [mul_assoc]
    exact h1
    done

end Matrix
