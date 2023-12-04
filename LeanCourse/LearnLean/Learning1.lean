-- 看着材料空打这样比较引人入胜
import Mathlib.Data.Real.Sqrt
open Real

-- 数学归纳法之一：二步归纳
namespace Nat
open Lean Elab Term Meta
  -- @[elab_as_elim]
  def two_step_induction
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

-- attribute [simp] div_left_inj' eq_neg_self_iff

noncomputable section
  -- def An : Nat -> Nat
  -- | 0 => 1
  -- | (n + 1) => (n) + 1

  def fib : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | n + 2 => fib (n + 1) + fib n

  def ϕ : ℝ := (1 + sqrt 5) / 2
  def ψ : ℝ := (1 - sqrt 5) / 2

  @[simp] lemma ϕ_sub_ψ_ne_zero : ϕ - ψ ≠ 0
  := by
  -- simp [ϕ, ψ, sub_eq_zero]
  simp [ϕ]
  simp [ψ]
  simp [sub_eq_zero]
  rw [sub_eq_add_neg]
  -- simp only [add_right_inj, eq_neg_self_iff, sqrt_eq_zero', not_le] --可省略的一行
  field_simp
  simp only [eq_neg_self_iff]
  norm_num
  done


  -- example :  ¬1 + sqrt 5 = 1 + -sqrt 5 := by
  --   simp only [add_right_inj, eq_neg_self_iff]
  --   -- simp only [add_right_inj, eq_neg_self_iff, sqrt_eq_zero', not_le]
  --   norm_num
  --   done

  -- lemma foo2: ¬sqrt 5 = 0 := by
  --   norm_num

  -- #print foo2

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

  -- #check Nat.two_step_induction

lemma coe_fib_eq (n : ℕ)
: ((fib n) : ℝ) = (ϕ ^ n - ψ ^ n) / (ϕ - ψ)
:= by
  induction n using Nat.two_step_induction
  case zero =>
    simp
    -- simp only [pow_zero, sub_self, zero_div, Nat.cast_eq_zero]
  case one => simp
  case step k ih1 ih2 =>
    -- simp [fib, ih1, ih2]
    simp [fib]
    simp [ih1]
    simp [ih2]
    field_simp
    simp [pow_add]
    set a₁:= ψ ^ k
    set a₂:= ϕ ^ k
    rw[add_sub,mul_add,mul_add]
    rw[← sub_sub]
    repeat rw[mul_one]
    -- rw[sub_right_cancel]
    rw[sub_left_inj]
    -- apply?
    -- exact sub_add_eq_add_sub (a₄ * ϕ) (a₃ * ψ) a₄
    rw[sub_add_eq_add_sub]
    -- ring

#print coe_fib_eq

    -- 推荐一下自然数游戏，可以从零推理出自然数的运算法则。体验一下从零搭建公理化地基的过程。
    -- 点赞超100，三天内更新下一个初等定理的形式化，后面希望能够边学习边介绍大学数学的形式化，比如线性代数抽象代数微积分等。
end
