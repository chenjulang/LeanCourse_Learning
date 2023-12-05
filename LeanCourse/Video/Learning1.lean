-- 十八世纪六十年代 2016 2022年11月30日 lean4
import Mathlib.Data.Real.Sqrt
open Real

namespace Nat

open Lean Elab Term Meta
  -- @[elab_as_elim]
  def two_step_induction --二步归纳法
  {P : ℕ → Sort*}
  (zero : P 0)
  (one : P 1)
  (step : ∀ (k : ℕ), (IH0 : P k) → (IH1 : P (k + 1)) → P (k + 2))
  (n : ℕ)
  : P n
  := by
    induction n using Nat.strongRec with
    | ind n ih =>
      rcases n with _|n
      · exact zero
      rcases n with _|n
      · exact one
      apply step
      · apply ih; linarith
      · apply ih; linarith

end Nat

--证明斐波那契数列的通项公式

noncomputable section

  def fib : ℕ → ℕ  --归纳定义
  | 0 => 0
  | 1 => 1
  | n + 2 => fib (n+1) + fib (n)

  def ϕ : ℝ := (1+ sqrt 5) /2
  def ψ : ℝ := (1- sqrt 5) /2

  @[simp]
  lemma ϕ_sub_ψ_ne_zero : ϕ - ψ ≠ 0
  := by
  rw [ϕ]
  rw [ψ]
  simp [sub_eq_zero]
  rw [sub_eq_add_neg]
  field_simp
  simp only [eq_neg_self_iff]
  norm_num

  @[simp] lemma ϕ_sq : ϕ ^ 2 = ϕ + 1 := by
    -- simp [ϕ, add_sq]
    simp [ϕ]
    simp [add_sq]
    field_simp
    -- norm_num
    ring
    done

  @[simp] lemma ψ_sq : ψ ^ 2 = ψ + 1 := by
    -- simp [ψ, sub_sq]
    simp [ψ]
    simp [sub_sq]
    field_simp
    ring

  lemma coe_fib_eq (n : ℕ)
  : ((fib n) : ℝ) = (ϕ ^ n - ψ ^ n) / (ϕ - ψ)
  := by
  induction n using Nat.two_step_induction
  case zero =>
    -- simp
    simp only [pow_zero]
    simp only [sub_self]
    simp only [zero_div]
    simp only [Nat.cast_eq_zero]
  case one =>
    -- simp
    simp only [pow_one, ne_eq, ϕ_sub_ψ_ne_zero, not_false_eq_true, div_self, Nat.cast_eq_one]
  case step k ih1 ih2 =>
    simp [fib]
    simp [ih1]
    simp [ih2]
    field_simp
    simp [pow_add]
    set a₁ := ψ ^ k
    set a₂ := ϕ ^ k
    rw[add_sub,mul_add,mul_add]
    rw[← sub_sub]
    repeat rw [mul_one]
    rw [sub_left_inj]
    have foo1 := sub_add_eq_add_sub (a₂ * ϕ) (a₁ * ψ) a₂
    exact foo1
    done

end
