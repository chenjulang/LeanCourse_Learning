import Mathlib.Data.Rat.Sqrt
import Mathlib.Data.Real.Sqrt
import Mathlib.RingTheory.Algebraic
import Mathlib.RingTheory.Int.Basic

import Mathlib.RingTheory.NonZeroDivisors

open Rat Real multiplicity

-- 类似定义“无理数”这个映射 ℝ → Prop
def Irrational (x : ℝ) :=
  have reflect1 : ℚ → ℝ := (↑)
  have set1 : Set ℝ := Set.range (reflect1)
  ¬ x ∈ set1
  -- x ∉ Set.range ((↑) : ℚ → ℝ) --可以代替上面的3行

def Irrational₂ (x : ℝ)(reflect1 : ℚ → ℝ) (set1 : Set ℝ :=Set.range (reflect1)):=
  ¬ x ∈ set1
  -- x ∉ Set.range ((↑) : ℚ → ℝ) --可以代替上面的3行

-- #check Rat.cast
-- #check (Irrational)



-- 定理描述：x是实数，n是自然数，m、y是整数；
-- x的n次方等于m；
-- x等于某个y不可能；
-- n大于0；
--->（推出）
-- x是无理数
theorem irrational_nrt_of_notint_nrt
{x : ℝ}
(n : ℕ)
(m : ℤ)
(hxr : x ^ n = m)
(hv : ¬∃ y : ℤ, x = y)
(hnpos : 0 < n)

  : Irrational x
:= by
  unfold Irrational
  intro H_x_In_Rat
  rcases H_x_In_Rat with ⟨X_Rat, X_Rat_CanCastTo_Real⟩ -- 解构出原像
  rcases X_Rat with ⟨N,D,P,C⟩
  rw [symm X_Rat_CanCastTo_Real] at hxr
  -- rintro ⟨⟨N, D, P, C⟩, rfl⟩ -- 这一行可以代替上面4行
  rw [← cast_pow] at hxr
  have c1 : ((D : ℤ) : ℝ) ≠ 0 := by
    rw [Int.cast_ne_zero, Int.coe_nat_ne_zero]
    exact P
  have c2 : ((D : ℤ) : ℝ) ^ n ≠ 0 := by
    exact pow_ne_zero n c1
  -- have c2 : ((D : ℤ) : ℝ) ^ n ≠ 0 := pow_ne_zero _ c1 -- 写个_，让程序自己猜可以用哪个
  rw [num_den', cast_pow, cast_mk, div_pow, div_eq_iff_mul_eq c2, ← Int.cast_pow, ← Int.cast_pow,
    ← Int.cast_mul, Int.cast_inj] at hxr
  have hdivn : (D : ℤ) ^ n ∣ N ^ n := by
    set c := m
    set h := hxr -- 加上这两行这样比较好读对于新手的我
    exact Dvd.intro_left c h
  rw [← Int.dvd_natAbs, ← Int.coe_nat_pow, Int.coe_nat_dvd, Int.natAbs_pow,
    Nat.pow_dvd_pow_iff hnpos] at hdivn
  have D_eq_one : D = 1 := by
    rw [← Nat.gcd_eq_right hdivn, C.gcd_eq_one]
  rw [D_eq_one] at P C hxr c1 c2 hdivn
  -- obtain rfl : D = 1 := by  --这里可以代替上面的3行
  --   rw [← Nat.gcd_eq_right hdivn, C.gcd_eq_one]
  apply absurd hv
  simp only [not_exists]
  simp only [not_forall]
  simp only [not_not]
  have : x = ↑N := by
    rw [symm X_Rat_CanCastTo_Real]
    rw [num_den',D_eq_one, Int.ofNat_one, divInt_one, cast_coe_int]
  use ↑N
  -- refine' hv ⟨N, _⟩ --这里可以代替上面的6行
  -- exact this
  done



-- 定理描述：n、p是自然数，m是整数，x是实数
-- m不等于0
-- p是素数
-- x的n次方等于m
-- ?? 这样的假设：N模n不等于0。（N是什么呢？p^N能整除m，N是满足条件的最大的那个自然数。）
-- -->推出
-- x是无理数

-- def hhh01 {p:ℕ} : Prime p := sorry
-- def hhh02 (p:ℕ)(m : ℤ):Int.natAbs p ≠ 1 ∧ m ≠ 0 := sorry
-- def hhh03 (p : ℕ)(m : ℤ):=multiplicity (p : ℤ) m

-- #check (hhh03 3 18) -- PartENat
-- #check (hhh02 3 18) -- Int.natAbs ↑3 ≠ 1 ∧ 18 ≠ 0
-- #check finite_int_iff.2 (hhh02 3 18) -- Prop
-- #check Part.get (hhh03 3 18) ( finite_int_iff.2 (hhh02 3 18) ) --  ℕ
-- #eval Part.get (hhh03 3 18) ( finite_int_iff.2 (hhh02 3 18) ) -- 2

-- Int.natAbs ?m.3176 ≠ 1 ∧ ?m.3177 ≠ 0 → multiplicity.Finite ?m.3176 ?m.3177


theorem irrational_nrt_of_n_not_dvd_multiplicity
{x : ℝ}
(n : ℕ)
{m : ℤ}
(hm : m ≠ 0)
(p : ℕ)
[hp : Fact p.Prime]
(hxr : x ^ n = m)
(hv :
(Part.get
  (multiplicity (p : ℤ) m)
  (finite_int_iff.2
    ⟨hp.1.ne_one, hm⟩
  )
)
  % n ≠ 0)

    :Irrational x

    := by
  rcases Nat.eq_zero_or_pos n with (h1 | hnpos)
  · subst h1
    rw [eq_comm, pow_zero, ← Int.cast_one, Int.cast_inj] at hxr
    subst hxr
    -- simp only [hxr] at hv
    have h1 := (mt Int.coe_nat_dvd.1 hp.1.not_dvd_one)
    have h2 := mt isUnit_iff_dvd_one.1 (h1)
    have h3 := multiplicity.one_right (h2)
    simp only [h3] at hv
    exact (hv rfl).elim --这一行不太懂，和Part有关。先普通意义上理解hv可推出0≠ 0
    -- simp [hxr,  -- 这个可以代替上面的6行
    --   multiplicity.one_right (mt isUnit_iff_dvd_one.1 (mt Int.coe_nat_dvd.1 hp.1.not_dvd_one)),
    --   Nat.zero_mod] at hv
  -- have h4 : irrational_nrt_of_notint_nrt _ _ hxr _ hnpos
  refine' irrational_nrt_of_notint_nrt _ _ hxr _ hnpos
  -- 如果之前有相同结论的命题，可以将这个命题的已满足的参数填进去，
  -- 还不满足的用下划线“_”代替，这些下划线代表内容就变成了还须证明的目标，lean自动修改了最终的goal
  rintro ⟨y, rfl⟩
  rw [← Int.cast_pow, Int.cast_inj] at hxr
  subst m
  -- have h4 : Prop := zero_pow hnpos
  have h5: y ≠ 0 := by
    intro y_eq_zero
    subst y_eq_zero
    -- rintro rfl --可以代替上面的2行
    rw [zero_pow] at hm
    exact hm rfl -- 丢两个互相相反的命题，得到False
    exact hnpos
  have h6 := (Nat.prime_iff_prime_int.1 hp.1)
  set h7 := multiplicity.pow' h6 (finite_int_iff.2 ⟨hp.1.ne_one, h5⟩)
  -- 这个讲的大概是如果p的M次方整除y，M一开始最大取的是m₁。
  -- 当y变大成y的n次方后，M最大可以取就变成了m₁*n
  erw [h7] at hv
  rw [Nat.mul_mod_right] at hv
  exact hv rfl -- hv: 0 ≠ 0
  done


theorem irrational_sqrt_of_multiplicity_odd
(m : ℤ)
(hm : 0 < m)
(p : ℕ)
[hp : Fact p.Prime]
(Hpv :
  (multiplicity (p : ℤ) m).get (finite_int_iff.2 ⟨hp.1.ne_one, (ne_of_lt hm).symm⟩) % 2 = 1)

    :Irrational (Real.sqrt m)
    := by
    have h1:= Ne.symm (ne_of_lt hm)
    have h2:= sq_sqrt (Int.cast_nonneg.2 (le_of_lt hm) )
    -- have h2:= sq_sqrt (Int.cast_nonneg.2 <| le_of_lt hm) -- f <| g <| x被解释为f (g x)而不是(f g) x
    refine' @irrational_nrt_of_n_not_dvd_multiplicity _ 2 _ h1 p hp h2 _
    rw [Hpv]
    exact one_ne_zero
    -- exact @irrational_nrt_of_n_not_dvd_multiplicity _ 2 _ h1 p hp h2 (by rw [Hpv]; exact one_ne_zero)
    --这个代替上面的3行
    done


theorem irrational_sqrt
{p : ℕ}
(hp : Nat.Prime p)

: Irrational (Real.sqrt p)
:= by
  have h1:= Int.coe_nat_pos.2 hp.pos
  -- exact @irrational_sqrt_of_multiplicity_odd p h1 p ⟨hp⟩ <| by
  --   simp [multiplicity.multiplicity_self
  --     (mt isUnit_iff_dvd_one.1 (mt Int.coe_nat_dvd.1 hp.not_dvd_one))]
  refine' @irrational_sqrt_of_multiplicity_odd p h1 p ⟨hp⟩ _
  have h2 := mt Int.coe_nat_dvd.1 hp.not_dvd_one
  have h3 := mt isUnit_iff_dvd_one.1 h2
  -- have h4 := multiplicity.multiplicity_self h3
  have h5 : p ≠ 0 := by
    exact Nat.Prime.ne_zero hp
  -- have h6 : multiplicity ↑p ↑p = 1 := by
    -- exact Nat.Prime.multiplicity_self hp
  have h7 : multiplicity (p : ℤ) (p : ℤ) = 1 := by
    refine multiplicity_self h3 ?ha0
    exact Int.ofNat_ne_zero.2 h5
  simp only [h7]
  have h9:= PartENat.get_one
  rw [h9]
  have h8:= Nat.one_mod 0
  rw [zero_add] at h8
  exact h8
  done


-- def prime2 : Nat.Prime 2 := by
--     exact Nat.prime_two
-- #check Nat.Prime.irrational_sqrt prime2

-- 终于来了：根号2是无理数的形式化证明

theorem irrational_sqrt_two : Irrational (Real.sqrt 2) := by
  have prime2 : Nat.Prime 2 := by
    exact Nat.prime_two
  apply irrational_sqrt at prime2
  exact prime2
  done
  -- simpa using Nat.prime_two.irrational_sqrt
