import Mathlib.LinearAlgebra.Matrix.Determinant
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.GroupTheory.Perm.Sign
import Mathlib.Data.Real.Sqrt


-- set_option trace.Meta.synthInstance true
set_option maxHeartbeats 400000


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



  -- 正式开始：


  lemma hhh1 (M N : Matrix n n R) :∑ p : n → n, ∑ σ : Perm n, ε σ * ∏ i, M (σ i) (p i) * N (p i) i =
      ∑ p in (@univ (n → n) _).filter Bijective, ∑ σ : Perm n, ε σ * ∏ i, M (σ i) (p i) * N (p i) i
      := by
      apply Eq.symm
      apply sum_subset
      · intro h1 h2
        exact mem_univ h1
      intros h3 h4 h5
      apply det_mul_aux -- ???
      simp only [mem_filter] at h5 -- ???
      simp only [mem_univ] at h5
      simp only [true_and_iff] at h5
      set h6 := fun x ↦ h3 x
      exact h5

  lemma hhh2 (M N : Matrix n n R) :
  ∑
    p in (@univ (n → n) _).filter Bijective,
      ∑
        σ : Perm n,
          (
            ε σ
            *
            ∏ i, M (σ i) (p i) * N (p i) i
          )
      = ∑ τ : Perm n, ∑ σ : Perm n, ε σ * ∏ i, M (σ i) (τ i) * N (τ i) i
      := by
      rw [sum_comm]
      rw [sum_comm] -- 相当于没变，只改成了x,y
      refine' sum_bij _ _ _ _ _
      · intros ih1 ih2
        have ih3:= (mem_filter.mp ih2).right
        have ih4:= ofBijective ih1 ih3
        exact ih4 -- 如果这里定义错了，下面满盘皆输
      -- intros ih1 ih2
      --   have ih3:= Equiv.refl n
      --   simp only [Perm]
      --   exact ih3
      -- apply sum_bij -- ???
      · intro h1
        intro h2
        simp only [mem_univ]
      · intros h_1 h_2
        have h_3:= mem_filter.1 h_2
        obtain ⟨h_4,h_5⟩ := h_3
        -- have h_6:= Equiv.ofBijective h_1 h_5 -- ???
        simp only [id_eq, refl_apply]
        rfl
      · exact (fun _ _ _ _ h => by injection h) ---?
        done
      -- intros inj_1 inj_2 inj_3 inj_4 inj_5
      · exact fun b _ => ⟨b, mem_filter.2 ⟨mem_univ _, b.bijective⟩, coe_fn_injective rfl⟩ ---?
        done
      done

  lemma hhh3 (M N : Matrix n n R) : ∑ σ : Perm n, ∑ τ : Perm n, (∏ i, N (σ i) i) * ε τ * (∏ j, M (τ j) (σ j))
      = ∑ σ : Perm n, ∑ τ : Perm n, (∏ i, N (σ i) i) * (ε σ * ε τ) * (∏ i, M (τ i) i)
      := by
      refine' sum_congr _ _
      · rfl
      · intros h1 h2
        refine' Fintype.sum_equiv _ _ _ _
        · exact Equiv.mulRight h1⁻¹
        · intros h5
          have h4 : (∏ j, M (h5 j) (h1 j)) = ∏ j, M ((h5 * h1⁻¹) j) j
            := by
            rw [← (h1⁻¹ : _ ≃ _).prod_comp]
            simp only [Equiv.Perm.coe_mul, apply_inv_self, Function.comp_apply]
          have h6 : ε h1 * ε (h5 * h1⁻¹) = ε h5
            :=
            calc
              ε h1 * ε (h5 * h1⁻¹) = ε (h5 * h1⁻¹ * h1) := by
                rw [mul_comm, sign_mul (h5 * h1⁻¹)]
                simp only [Int.cast_mul, Units.val_mul]
              _ = ε h5 := by simp only [inv_mul_cancel_right]
          simp_rw [Equiv.coe_mulRight, h6]
          simp only [h4]
      done


  -- @[simp]
  theorem det_mul2 (M N : Matrix n n R)
  : det (M * N) = det M * det N
  := by
    have h1 :det (M * N) = det M * det N :=
      calc
          det (M * N)
          = ∑ p : n → n, ∑ σ : Perm n, ε σ * ∏ i, M (σ i) (p i) * N (p i) i
            := by
            simp only [det_apply']
            simp only [mul_apply]
            simp only [prod_univ_sum]
            simp only [mul_sum]
            simp only [Fintype.piFinset_univ]
            rw [Finset.sum_comm]
          _ = ∑ p
                in (@univ (n → n) _).filter Bijective,
                  ∑ σ
                    : Perm n,
                      ε σ
                      *
                      (∏ i, M (σ i) (p i) * N (p i) i)
            := by
            exact (hhh1 M N)
          _ = ∑ τ
                : Perm n,
                  ∑ σ
                    : Perm n,
                      ε σ
                      *
                      (∏ i, M (σ i) (τ i) * N (τ i) i)
            := by
            exact (hhh2 M N)
          _ = ∑ σ
                : Perm n,
                  ∑ τ
                    : Perm n,
                      (∏ i, N (σ i) i)
                      *
                      ε τ
                      *
                      ∏ j, M (τ j) (σ j)
            := by
            simp only [mul_comm]
            simp only [mul_left_comm]
            simp only [prod_mul_distrib]
            simp only [mul_assoc]
          _ = ∑ σ : Perm n, ∑ τ : Perm n, (∏ i, N (σ i) i) * (ε σ * ε τ) * ∏ i, M (τ i) i
            := by
            exact (hhh3 M N)
          _ = det M * det N
            := by
            -- simp only [det_apply', Finset.mul_sum, mul_comm, mul_left_comm, mul_assoc] --这里无法分步，所以直接分析print来写成下面这样子：
            have h2 : det M * det N =
              ∑ x : Perm n, (∑ x : Perm n, (∏ x_1 : n, M (x x_1) x_1) * (ε x)) * ((∏ x_1 : n, N (x x_1) x_1) * (ε x))
              := by
              have h2_1 : det M = ∑ x : Perm n, (∏ x_1 : n, M (x x_1) x_1) * (ε x)
                := by
                have h2_1_1 :=(det_apply' M)
                have h2_1_2 : ∑ x : Perm n, (ε x) * ∏ x_1 : n, M (x x_1) x_1
                  = ∑ x : Perm n, (∏ x_1 : n, M (x x_1) x_1) * (ε x)
                  := by
                  refine' sum_congr _ _
                  · exact (Eq.refl univ)
                  · intros h212x h212a
                    have h2_1_2_1
                      : (ε h212x) * ∏ x_1 : n, M (h212x x_1) x_1 = (ε h212x) * ∏ x_1 : n, M (h212x x_1) x_1
                      := by
                      exact rfl --竟然直接搞定了
                    have h2_1_2_2 := mul_comm ((ε h212x)) (∏ x_1 : n, M (h212x x_1) x_1)
                    have h2_1_2_3 := h2_1_2_1.trans h2_1_2_2
                    exact h2_1_2_3
                have h2_1_3 := h2_1_1.trans h2_1_2
                exact h2_1_3
              have h2_2 : det N = ∑ x : Perm n, (∏ x_1 : n, N (x x_1) x_1) * (ε x)
                := by
                have h2_2_1:= det_apply' N
                have h2_2_2:  ∑ x : Perm n, (ε x) * ∏ x_1 : n, N (x x_1) x_1 = ∑ x : Perm n, (∏ x_1 : n, N (x x_1) x_1) * (ε x)
                  := by
                  refine' sum_congr _ _
                  · exact Eq.refl univ
                  · intros h222x h222a
                    have h2_2_2_1 : (ε h222x) * ∏ x_1 : n, N (h222x x_1) x_1 = (ε h222x) * ∏ x_1 : n, N (h222x x_1) x_1
                      := by
                      -- exact rfl
                      -- refine' congrArg _ _
                      exact (congrArg (HMul.hMul (ε h222x))
                                  (prod_congr (Eq.refl univ) fun x_1 a ↦ Eq.refl (N (h222x x_1) x_1)))
                    have h2_2_2_2:= (mul_comm ((ε h222x)) (∏ x_1 : n, N (h222x x_1) x_1))
                    have h2_2_2_3:= h2_2_2_1.trans h2_2_2_2
                    exact h2_2_2_3
                have h2_2_3:= h2_2_1.trans h2_2_2
                exact h2_2_3
              exact (congr (congrArg HMul.hMul h2_1) h2_2).trans mul_sum
            have h3 : ∑ x : Perm n, (∑ x : Perm n, (∏ x_1 : n, M (x x_1) x_1) * (ε x)) * ((∏ x_1 : n, N (x x_1) x_1) * (ε x))
                = ∑ x : Perm n, ∑ x_1 : Perm n, (∏ x_2 : n, N (x x_2) x_2) * ((∏ x : n, M (x_1 x) x) * ((ε x) * (ε x_1)))
              := by
              refine' sum_congr _ _
              · exact (Eq.refl univ)
              · intros h3_1 h3_2
                have h3_3:= ((mul_comm (∑ x : Perm n, (∏ x_1 : n, M (x x_1) x_1) * (ε x))
                            ((∏ x_1 : n, N (h3_1 x_1) x_1) * (ε h3_1))).trans
                        mul_sum)
                have h3_4:= (sum_congr (Eq.refl univ) fun x_1 a ↦
                      ((mul_left_comm ((∏ x_2 : n, N (h3_1 x_2) x_2) * (ε h3_1)) (∏ x : n, M (x_1 x) x)
                                (ε x_1)).trans
                            (congrArg (HMul.hMul (∏ x : n, M (x_1 x) x))
                              (mul_assoc (∏ x_2 : n, N (h3_1 x_2) x_2) (ε h3_1) (ε x_1)))).trans
                        (mul_left_comm (∏ x : n, M (x_1 x) x) (∏ x_2 : n, N (h3_1 x_2) x_2)
                          ((ε h3_1) * (ε x_1))))
                have h3_5:= h3_3.trans h3_4
                exact h3_5
            have h4:= h2.trans h3
            simp only [h4]
            congr
            funext xx1
            congr
            funext xx2
            rw [mul_right_comm]
            repeat rw [← mul_assoc]
    exact h1
    done


end Matrix