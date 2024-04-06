import Paperproof
import Mathlib.Data.Real.Sqrt
-- 十八世纪六十年代 2016 2022年11月30日 lean4
-- 斐波拉契数列通项公式

-- variable (m:ℕ) (n:ℕ) (q:ℚ)
-- lemma test001 (h1:q=m/n) : sorry := by sorry

open Real -- 把前缀省略
#check (sqrt 2:ℝ )

-- 数学归纳法：二步归纳
namespace Nat

open Lean Elab Term Meta

  def two_step_induction -- 名称
  {P : ℕ → Sort*} --条件若干
  (zero : P 0)
  (one : P 1)
  (step : ∀ (k : ℕ), (IH0 : P k) → (IH1 : P (k + 1)) → P (k + 2))
  (n : ℕ)

  : P n -- 命题具体描述（或理解成 ：意思是属于某一个集合）

  := by --证明过程（策略模式：给出大boss，goal，给一些策略作用到它上面，直到他粉碎为止）
    induction n using Nat.strongRec with
    | ind n ih =>
      rcases n with _|n
      · exact zero
      rcases n with _|n
      · exact one
      apply step
      · apply ih; linarith
      · apply ih; linarith
    done --命题得证

end Nat

noncomputable section

  def fib : ℕ → ℕ  --(理解成映射；数列；函数)
  | 0 => 0
  | 1 => 1 -- 1,1,2,3,5,8,13...
  | n + 2 => (fib (n+1)) + (fib n)

  #eval (fib 7) --13

  def ϕ : ℝ := (1 + sqrt 5)/2
  def ψ : ℝ := (1 - sqrt 5)/2

  @[simp]
  lemma ϕ_sub_ψ_ne_zero : ϕ - ψ ≠ 0
  := by
    rw [ϕ]
    rw [ψ]
    simp only [ne_eq]
    simp [sub_eq_zero]
    rw [sub_eq_add_neg]
    field_simp --通分
    simp only [eq_neg_self_iff]
    norm_num -- 不等号的简单证明
    done

  @[simp]
  lemma ϕ_sq : ϕ ^ 2 = ϕ + 1 := by
    simp [ϕ]
    simp [add_sq]
    field_simp
    ring -- 等号的简单证明
    done

  @[simp]
  lemma ψ_sq : ψ ^ 2 = ψ + 1 := by
    simp [ψ]
    simp [sub_sq]
    field_simp
    ring
    done

  theorem coe_fib_eq (n : ℕ)
  : ((fib n) : ℝ) = (ϕ ^ n - ψ ^ n) / (ϕ - ψ)
  := by
    induction n using Nat.two_step_induction
    case zero =>
      simp only [pow_zero]
      simp only [sub_self]
      simp only [zero_div]
      simp [fib]
      done
      -- simp only [Nat.cast_eq_zero]
    case one =>
      simp only [pow_one]
      simp [fib]
      done
    case step k ih1 ih2 => -- 重点在这一步!!!
      simp [fib]
      rw [ih1]
      rw [ih2]
      field_simp
      simp [pow_add]
      set a₁ := ψ ^ k
      set a₂ := ϕ ^ k
      rw [add_sub,mul_add,mul_add]
      rw[← sub_sub]
      repeat rw [mul_one]
      rw [sub_left_inj]
      have aaa1 := (sub_add_eq_add_sub (a₂ * ϕ) (a₁ * ψ) a₂)
      -- exact (sub_add_eq_add_sub (a₂ * ϕ) (a₁ * ψ) a₂)
      exact aaa1
      done

    -- 基于有限的几个公理，可以推出高深的数学。
end


lemma test1 (a b c d e f g h : ℕ) : (d + f) + (h + (a + c)) + (g + e + b) = a + b + c + d + e + f + g + h
:= by
  simp only [add_assoc,add_left_comm,add_comm]
  -- ring

-- lemma test2 : 20+20 =40 :=by decide
-- #print test2

-- #print test1

-- #minimize_imports
