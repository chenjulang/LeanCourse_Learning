import Mathlib.Tactic.LinearCombination
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Mathlib.Data.Polynomial.Eval
import Mathlib.Data.Real.Sqrt

-- 这集的终极目标是证明一般3次方程的求根公式的充分必要条件。
-- 也就是，除了验证3个解的合理性以外，还会给出刚好能推出3个根的这个严格证明。


namespace testroot3

section Field

open Polynomial

variable {K : Type*} [Field K]

variable [Invertible (2 : K)] [Invertible (3 : K)] --实际的例子可以是一个二维平面上的线性变换，比如逆时针旋转或者放大缩小。在三维空间中，可以是一个三维物体的旋转变换，比如围绕某个轴的旋转。这些都可以用矩阵来表示，并且这些矩阵都是可逆的，因为它们可以被逆转回原始状态。
-- ???好像不是这样定义的，就是纯粹的K集合上的2，3元素有逆

variable (a b c d : K)

variable {ω p q r s t : K}

-- 欧拉万岁！！！
-- 1.IsPrimitiveRoot ω k：就是k-单位根,即 (ω ^ k = 1) ∧ (∀ l : ℕ, ω ^ l = 1  →  k ∣ l)
-- 2.hω.isRoot_cyclotomic
--  2.1.cyclotomic n R：n-分圆多项式，系数在R集合里，即
        -- 2.1.1.为什么：复数单位根是z = e^((2πik) / n)：
          -- 复数单位根z = e^((2πik) / n)的形式可以通过欧拉公式推导得出。
          -- 欧拉公式是一个重要的数学公式，它描述了复指数函数和三角函数之间的关系。欧拉公式的表达式为：
          -- e^(ix) = cos(x) + i sin(x)
          -- 其中，e是自然对数的底数，i是虚数单位，x是实数。这个公式将指数函数和三角函数联系在一起。
          -- 现在我们考虑复数单位根，即满足zⁿ = 1的复数。假设z可以表示为z = Ce^(iθ)，C是实数，可以表示的原因是：z是一个任意的复数C(cos(θ) + i sin(θ))=Ce^(iθ)
          -- ，其中θ是实数。我们希望找到满足zⁿ = 1，即zⁿ =(C^n)e^(iθn)=1中θ的取值，此时n和i已固定。
          -- zⁿ =(C^n)e^(iθn)=1
          -- 应用指数函数的幂运算法则，我们可以将上述方程改写为：

          -- (C^n)e^(iθn)=1
          -- 根据欧拉公式，左侧的e^(inθ)可以表示为：
          -- e^(inθ) = cos(nθ) + i sin(nθ) = 1 = 1 + i * 0
          -- 左边整体就是：(C^n) (cos(nθ) + i sin(nθ)) = (C^n)*cos(nθ) + (C^n)*isin(nθ)  =  1 = 1 + i * 0
          -- 由于右侧等于1，由于实数部分和复数部分分别对应相同，我们可以得到两个等式：
          -- (C^n)*cos(nθ) = 1
          -- (C^n)*isin(nθ)  = 0 -- 小引理：常数(C^n)值只能是1， 因为满足第二行的nθ只能是2πk，即2π的整数倍，代入第一行之后，就是(C^n)= 1
          -- 实际上就变成了新问题：
          -- cos(nθ) = 1
          -- isin(nθ)  = 0
          -- z = Ce^(iθ) = e^(iθ) 因为满足(C^n)= 1的实数，一维数轴上的数C只有1

          -- 我们可以观察到，当nθ = 2πk （360度的整数k倍）时，也只有这个时候，其中k是整数，上述两个等式成立。因此，
          -- 我们可以得到：
          -- nθ = 2πk  也就是说，e^(inθ)这个形式的项，只有能改写成e^(i2πk)这个形式下，值为1
            --  e^(i2πk) = cos(2πk) + i sin(2πk) = 1 + i*0 = 1
          -- 所有满足的θ可以表示为θ = (2πk) / n，我们就得到了复数单位根的表达式：

          -- z 定义表示为= e^(iθ) = e^((2πik) / n)

          -- 比如计算z^3=1 , 得到 z= e^((2πik) / 3) = e^(i(2πk) / 3)
          -- e^(i(2πk) / 3)由欧拉公式= cos((2πk) / 3) + i sin((2πk) / 3) , 用k=0，1，2，3，4...代入可知
          -- x1= cos(2π/3) + i*sin(2π/3) ,
          -- x2= cos(4π/3) + i*sin(4π/3)
          -- x3= cos(6π/3) + i*sin(6π/3) = cos(2π) + i*sin(2π) = 1 + i*0
          -- x4= cos(8π/3) + i*sin(8π/3) = cos(2π/3) + i*sin(2π/3) = x1 重复了
          -- 以后也一直重复 x1,x2,x3这3个。

          -- e^(ix) = cos(x) + i sin(x)
          -- 这里证明一个定理两边多项式相等x^3 - 1 = （x-e^(i(2π) / 3)）*（x-e^(i(2*2π) / 3)）* （x-e^(i(3*2π) / 3)）
          -- 右边= （x-e^(i(1*2π) / 3)）*（x-e^(i(2*2π) / 3)）* （x-e^(i(3*2π) / 3)）
          -- 分配律= x^3 - e^(i(2π) / 3)*e^(i(2*2π) / 3)*e^(i(3*2π) / 3) + ...
          --抽象写法= x^3 - 1 + x*(（2+3）+（1+3）+（1+2）) + x^2*（-1）(3+2+1)
          -- =  x^3 - 1 + x * (cos(5* 2π/3)+cos(4* 2π/3)+ cos(3* 2π/3)  +  i sin(5* 2π/3) +  i sin(4* 2π/3) +  i sin(3* 2π/3)) +
          -- x^2* （-1）（cos(3* 2π/3)+cos(2* 2π/3)+cos(1* 2π/3) + i sin(3* 2π/3 + i sin(2* 2π/3）+i sin(1* 2π/3）） -- 关于x轴对称的一对对，对称的奇妙之处

          -- 我们试一下n=4,x^4 - 1 = （x-e^(i(1*2π) / 4)）*（x-e^(i(2*2π) / 4)）* （x-e^(i(3*2π) / 4)） * （x-e^(i(4*2π) / 4)）
          -- x^4 - 1(这个1只要π的整数倍即得1，不需要2π得整数倍)
          -- 抽象写法 x^1* （(2+3+4)+(1+3+4)+(1+2+4)+(1+2+3)）

          -- 验证一下是否满足：(ω ^ m = 1) ∧ (∀ l : ℕ, ω ^ l = 1  →  m ∣ l)
          -- 此时m=3,
          -- 验证ω=x1，即ω=e^(i(2π) / 3)=cos(2π/3) + i*sin(2π/3) 是否满足，∀ l : ℕ, ω ^ l = 1 ，只有l是m=3的倍数时成立
            -- 我们尝试l=1,2,3不用尝试代入就知道结果为1,4即1，5即2，6即3所以结果也是1，后面都是循环的，所以实际上只需要验证l=1,2
            -- l=1,2是否满足ω ^ l = 1 呢？我们要证明它不满足，因为e^(i(2π1) / 3) 、 e^(i(2π2) / 3) 都不是 e^(i2πk) 这个2π的整数倍，所以不等于1
          -- 验证ω=x2，即ω=e^(i(4π) / 3)=cos(4π/3) + i*sin(2π/3) 是否满足，∀ l : ℕ, ω ^ l = 1 ，只有l是m=3的倍数时成立
            -- 我们尝试l=1,2,3不用尝试代入知道是2π的整数倍，所以就变成了验证次数，i后面的项是否2π的整数倍。
            -- l=1,2代入可知e^(i(4π) *1/ 3) 、 e^(i(4π)*2 / 3)， 都无法和分母3约掉，即不是整数倍，所以不等于1
          -- 验证ω=x3，即ω=e^(i(6π) / 3) = e^(i(2π))=1， 这个却是不满足：(ω ^ m = 1) ∧ (∀ l : ℕ, ω ^ l = 1  →  m ∣ l)的，因为l是1，2也满足。

          -- 所以在lean里面定义的IsPrimitiveRoot ω k这个根呢，是去掉1的。

          -- 这就是复数单位根的一般形式。它表示了复数单位根与欧拉公式之间的关系，其中k是整数，
          -- 满足0 ≤ k < n。这个形式允许我们通过指数函数来表示复数单位根，从而方便地进行计算和处理。
        -- 2.1.2.为什么：复数单位根是圆周上均匀分布的n个点
          -- 由于根形式是z = e^(iθ) = e^((2πik) / n) 根据欧拉公式e^(iθ) = cos(θ) + i sin(θ)变成
          --  这里θ即(2πk) / n， 所以就是 （360度/n）* 1，2，3，4......，
          -- 也就是z = e^(iθ) = e^((2πik) / n) = cos((2πk) / n) + i sin((2πk) / n) 表示成二维的数就知道

--  2.2.IsRoot p x:就是x代入p的值为0，即p的根
-- 3.cyclotomic_prime p R：是一个多项式， p是素数, cyclotomic p R = ∑ i in range p, X ^ i
--    即： p分圆多项式=多项式（∑ i in range p, X ^ i），（X是多项式变量）
-- 4. Finset.sum_range_succ ： 求和n+1项=求和n项 +（第n+1项）

-- theorem cube_root_of_unity_sum (hω : IsPrimitiveRoot ω 3) : 1 + ω + ω ^ 2 = 0 := by
-- 为什么可以这样定义k-单位根的第二个属性：∀ l : ℕ, ζ ^ l = 1 → k ∣ l ？ 举例说明就知道了
--   have h1:= hω.isRoot_cyclotomic (by decide)
--   simpa [cyclotomic_prime, Finset.sum_range_succ] using h1
-- #print cube_root_of_unity_sum

  theorem cube_root_of_unity_sum2
  (hω : IsPrimitiveRoot ω 3)
  : 1 + ω + ω ^ 2 = 0
    := by
    let h1 : IsRoot (cyclotomic 3 K) ω
      := by
      refine' IsPrimitiveRoot.isRoot_cyclotomic _ _ -- 前面的2个根，也是后面多项式1 + x + x^2的根？
      -- ω ^ 3 = 1
      -- 现实中已知x^3 - 1 = （x-e^(i(2π) / 3)）*（x-e^(i(2*2π) / 3)）* （x-e^(i(3*2π) / 3)）
      -- 即(x-ω)(x-ω^2)(x-ω^2) = x^3 - 1
      -- 两边除以(x-1)，得到(x-ω)(x-ω^2) = 1 + x + x^2
      -- 得出 (x-ω)(x-ω^2)的根 = 1 + x + x^2的根
      -- 也就是ω，ω^2= 1 + x + x^2的根
      · exact Nat.succ_pos 2
      · exact hω
      done
      -- exact IsPrimitiveRoot.isRoot_cyclotomic (@of_decide_eq_true (0 < 3) (Nat.decLt 0 3) (Eq.refl true)) hω
    have h2 :  IsRoot (cyclotomic 3 K) = IsRoot (1 + X + X ^ 2)
      := by
      rw [cyclotomic_prime]--看成定义
      refine' congrArg _ _
      rw [Finset.sum_range_succ]
      rw [Finset.sum_range_succ]
      rw [Finset.sum_range_succ]
      simp only [Finset.range_zero]
      simp only [Finset.sum_empty]
      simp only [pow_zero]
      simp only [zero_add]
      simp only [pow_one]
      done
    have h3 : (eval ω (1 + X + X ^ 2)=0) = (1 + ω + ω ^ 2 = 0) -- eval x p是: x代入多项式p的值
      := by
      simp only [eval_add, eval_one, eval_X, eval_pow] --大概就是代入的过程
    rw [← h3]
    simp only [eval_add, eval_one, eval_X, eval_pow]
    have h4 :IsRoot (cyclotomic 3 K) ω = IsRoot (1 + X + X ^ 2) ω
      := by
      exact congrFun h2 ω
    have h5 : IsRoot (1 + X + X ^ 2) ω = (eval ω (1 + X + X ^ 2) = 0)
      := by
      simp only [IsRoot.def, eval_add, eval_one, eval_X, eval_pow]
    clear h2
    have h6:= h4.trans h5
    clear h4 h5
    have h7:= h6.trans h3
    clear h6 h3
    rw [h7] at h1
    exact h1
    done

  -- //

  /-- 去掉二次方项的形式 -/
  theorem cubic_basic_eq_zero_iff2
  (hω : IsPrimitiveRoot ω 3) -- p q可以任意取
  (hp_nonzero : p ≠ 0)
  (hr : r ^ 2 = q ^ 2 + p ^ 3) -- r 从p和q定义出来
  (hs3 : s ^ 3 = q + r) -- s 从q和r定义出来
  (ht : t * s = p)  -- t 从s和p定义出来
  (x : K) :

  (x ^ 3 + 3 * p * x - 2 * q = 0)
  ↔
  (x = s - t
  ∨
  x = s * ω - t * ω ^ 2
  ∨
  x = s * ω ^ 2 - t * ω)

    := by
    have h₁ : ∀ x a₁ a₂ a₃ : K,
      x = a₁ ∨ x = a₂ ∨ x = a₃
      ↔ (x - a₁) * (x - a₂) * (x - a₃) = 0
      := by
      intros
      simp only [mul_eq_zero]
      simp only [sub_eq_zero]
      simp only [or_assoc]
    rw [h₁]
    clear h₁
    refine' Eq.congr _ rfl
    have hs_nonzero : s ≠ 0
      := by
      contrapose! hp_nonzero with hs_nonzero
      linear_combination -1 * ht + t * hs_nonzero -- linear_combination：多个等式,等号左右分别相加
    rw [← mul_left_inj' (pow_ne_zero 3 hs_nonzero)] -- 为什么要变复杂呢？
    have H := cube_root_of_unity_sum2 hω
    clear hω -- 是好习惯吗？清掉用过的条件
    -- 下面会构造几个线性组合的等式，简称lc
    have lc1: (-q + r + s ^ 3) * s ^ 3
    = (-q + r + s ^ 3) * (q + r)
      := by
      simp only [mul_eq_mul_left_iff]
      have lc1_1 := congrArg (HMul.hMul (-q + r + s ^ 3)) hs3
      exact mul_eq_mul_left_iff.mp (lc1_1)
    have lc2: (3 * x * s ^ 3 + (t * s) ^ 2 + t * s * p + p ^ 2) * (t * s)
    = (3 * x * s ^ 3 + (t * s) ^ 2 + t * s * p + p ^ 2) * p
      := by
      simp only [mul_eq_mul_left_iff]
      have lc2_1 := (congrArg (HMul.hMul (3 * x * s ^ 3 + (t * s) ^ 2 + t * s * p + p ^ 2)) ht)
      exact mul_eq_mul_left_iff.mp lc2_1
    have lc3:
    (
      x ^ 2 * (s - t) + x * (-ω * (s ^ 2 + t ^ 2) + s * t * (3 + ω ^ 2 - ω)) -
        (-(s ^ 3 - t ^ 3) * (ω - 1) + s ^ 2 * t * ω ^ 2 - s * t ^ 2 * ω ^ 2)
    )
    *
    (s ^ 3)
    *
    (1 + ω + ω ^ 2)
     =
    (x ^ 2 * (s - t) + x * (-ω * (s ^ 2 + t ^ 2) + s * t * (3 + ω ^ 2 - ω)) -
          (-(s ^ 3 - t ^ 3) * (ω - 1) + s ^ 2 * t * ω ^ 2 - s * t ^ 2 * ω ^ 2)
    )
    *
    s ^ 3
    *
    0
      := by
      simp only [neg_mul]
      simp only [mul_zero]
      simp only [mul_eq_zero]
      simp only [pow_eq_zero_iff]
      exact Or.inr H
    -- clear hs3 ht hs_nonzero H
    -- 很神奇的变参数防近视过程
    -- set s_3:= s ^ 3
    -- set x_3:= x ^ 3
    -- set px:= p * x
    -- set x3:= ω ^ 2
    -- set x4:= s ^ 2 + t ^ 2
    -- set x5:= 3 + x3 - ω
    -- set x6:= (-ω * x4 + s * t * x5)
    -- set x7:= x ^ 2 * (s - t)
    -- set x8:= 3 * x * x1
    linear_combination
      hr +
      lc1 -
      lc2 +
      lc3
    -- linear_combination -- 原始写法
    --   hr + (-q + r + s ^ 3) * hs3 - (3 * x * s ^ 3 + (t * s) ^ 2 + t * s * p + p ^ 2) * ht +
    --   (x ^ 2 * (s - t) + x * (-ω * (s ^ 2 + t ^ 2) + s * t * (3 + ω ^ 2 - ω)) -
    --     (-(s ^ 3 - t ^ 3) * (ω - 1) + s ^ 2 * t * ω ^ 2 - s * t ^ 2 * ω ^ 2)) * s ^ 3 * H
    done

  -- #print cubic_basic_eq_zero_iff2

  /-- 三次方项系数为1的形式 -/
  theorem cubic_monic_eq_zero_iff2
  (hω : IsPrimitiveRoot ω 3) --b c任意取
  (hp : p = (3 * c - b ^ 2) / 9) -- p 从b和c定义出来
  (hp_nonzero : p ≠ 0) -- p有一个限制条件
  (hq : q = (9 * b * c - 2 * b ^ 3 - 27 * d) / 54) -- p 从b和c和d定义出来
  (hr : r ^ 2 = q ^ 2 + p ^ 3) -- r 从q和p定义出来
  (hs3 : s ^ 3 = q + r) -- s 从r和q定义出来
  (ht : t * s = p) -- t 从s和p定义出来
  (x : K)
  : (x ^ 3 + b * x ^ 2 + c * x + d = 0)
  ↔
    x = s - t - b / 3
    ∨
    x = s * ω - t * ω ^ 2 - b / 3
    ∨
    x = s * ω ^ 2 - t * ω - b / 3

    := by
    let y := x + b / 3
    have hi2 : (2 : K) ≠ 0 := nonzero_of_invertible _ -- 有倒数的数不为零
    have hi3 : (3 : K) ≠ 0 := nonzero_of_invertible _
    have h9 : (9 : K) = 3 ^ 2 := by norm_num
    have h54 : (54 : K) = 2 * 3 ^ 3 := by norm_num
    have h₁ : x ^ 3 + b * x ^ 2 + c * x + d
    = y ^ 3 + 3 * p * y - 2 * q := by
      rw [hp, hq]
      field_simp [h9, h54]; -- 通分细节略过
      ring
    rw [h₁, cubic_basic_eq_zero_iff2 hω hp_nonzero hr hs3 ht y]
    simp only
    rw [eq_sub_iff_add_eq] -- rw长龙～～～
    rw [eq_sub_iff_add_eq]
    rw [eq_sub_iff_add_eq]
    rw [eq_sub_iff_add_eq]
    rw [eq_sub_iff_add_eq]
    rw [eq_sub_iff_add_eq]
    rw [eq_sub_iff_add_eq]
    rw [eq_sub_iff_add_eq]
    rw [eq_sub_iff_add_eq]
    -- simp_rw [eq_sub_iff_add_eq] --替换写法
    done

  /-- 判定式为非零，通用的一般形式，求出三个解 -/
  theorem MainGoal5 -- a b c d任意取
  (ha : a ≠ 0) -- a有一个限制条件
  (hω : IsPrimitiveRoot ω 3)
  (hp : p = (3 * a * c - b ^ 2) / (9 * a ^ 2)) -- p 由a,b,c定义出来
  (hp_nonzero : p ≠ 0) -- p的一个限制条件
  (hq : q = (9 * a * b * c - 2 * b ^ 3 - 27 * a ^ 2 * d) / (54 * a ^ 3)) -- q 由a,b,c,d定义出来
  (hr : r ^ 2 = q ^ 2 + p ^ 3) -- r 由q,p定义出来
  (hs3 : s ^ 3 = q + r) -- s 由r,q定义出来
  (ht : t * s = p)  -- t 由s,p定义出来
  (x : K)
  : (a * x ^ 3 + b * x ^ 2 + c * x + d = 0)
  ↔
    x = s - t - b / (3 * a) -- 第一个解
    ∨
    x = s * ω - t * ω ^ 2 - b / (3 * a) -- 第二个解
    ∨
    x = s * ω ^ 2 - t * ω - b / (3 * a) -- 第三个解
    := by
    have hi2 : (2 : K) ≠ 0 := nonzero_of_invertible _
    have hi3 : (3 : K) ≠ 0 := nonzero_of_invertible _
    have h9 : (9 : K) = 3 ^ 2 := by norm_num
    have h54 : (54 : K) = 2 * 3 ^ 3 := by norm_num
    have h₁ : a * x ^ 3 + b * x ^ 2 + c * x + d
    = a * (x ^ 3 + b / a * x ^ 2 + c / a * x + d / a) --a写到分母
      := by
      field_simp;
      ring
    have h₂ : ∀ x, a * x = 0 ↔ x = 0
      := by
      intro x;
      simp [ha]
    have hp' : p = (3 * (c / a) - (b / a) ^ 2) / 9
      := by
      rw [hp]
      field_simp [hp, h9];
      ring_nf
    have hq' : q
    = (9 * (b / a) * (c / a) - 2 * (b / a) ^ 3 - 27 * (d / a)) / 54
    := by
      rw [hq]
      field_simp [hq, h54];
      ring_nf
    rw [h₁, h₂, cubic_monic_eq_zero_iff2 (b / a) (c / a) (d / a) hω hp' hp_nonzero hq' hr hs3 ht x]
    have h₄ :=
      calc
        b / a / 3
          = b / (a * 3)
            := by
            field_simp [ha]
        _ = b / (3 * a)
            := by rw [mul_comm]
    rw [h₄]
    done


  --  def a_2 :ℚ :=1/3
  -- def b_2 :ℚ :=-1
  -- def c_2 :ℚ :=1
  -- def d_2 :ℚ :=-1/3

  /-- 判定式为零，通用的一般形式，求出三个解 -/
  theorem cubic_eq_zero_iff_of_p_eq_zero
  (ha : a ≠ 0)
  (hω : IsPrimitiveRoot ω 3)
  (hpz : 3 * a * c - b ^ 2 = 0)
  (hq : q = (9 * a * b * c - 2 * b ^ 3 - 27 * a ^ 2 * d) / (54 * a ^ 3))
  (hs3 : s ^ 3 = 2 * q)
  (x : K) :
    a * x ^ 3 + b * x ^ 2 + c * x + d = 0
    ↔

    x = s - b / (3 * a)
    ∨
    x = s * ω - b / (3 * a)
    ∨
    x = s * ω ^ 2 - b / (3 * a)
    := by
    have h₁ : ∀ x a₁ a₂ a₃ : K, x = a₁ ∨ x = a₂ ∨ x = a₃
    ↔ (x - a₁) * (x - a₂) * (x - a₃) = 0
    := by
      intros;
      simp only [mul_eq_zero, sub_eq_zero, or_assoc]
    have hi2 : (2 : K) ≠ 0 := nonzero_of_invertible _
    have hi3 : (3 : K) ≠ 0 := nonzero_of_invertible _
    have h54 : (54 : K) = 2 * 3 ^ 3 := by norm_num
    have hb2 : b ^ 2 = 3 * a * c
      := by
      rw [sub_eq_zero] at hpz;
      rw [hpz]
    have hb3 : b ^ 3 = 3 * a * b * c
      := by
      rw [pow_succ, hb2];
      ring
    have h₂ :=
      calc
        a * x ^ 3 + b * x ^ 2 + c * x + d
        = a * (x + b / (3 * a)) ^ 3 + (c - b ^ 2 / (3 * a)) * x + (d - b ^ 3 * a / (3 * a) ^ 3) :=
          by field_simp; ring
        _ = a * (x + b / (3 * a)) ^ 3 + (d - (9 * a * b * c - 2 * b ^ 3) * a / (3 * a) ^ 3)
          := by
          simp only [hb2];
          simp only [hb3];
          field_simp;
          ring
        _ = a * ((x + b / (3 * a)) ^ 3 - s ^ 3) := by rw [hs3, hq]; field_simp [h54]; ring
    have h₃ : ∀ x, a * x = 0 ↔ x = 0
      := by intro x; simp [ha]
    have h₄ : ∀ x : K, x ^ 3 - s ^ 3 = (x - s) * (x - s * ω) * (x - s * ω ^ 2)
      := by
      intro x
      calc
        x ^ 3 - s ^ 3 = (x - s) * (x ^ 2 + x * s + s ^ 2) := by ring
        _ = (x - s) * (x ^ 2 - (ω + ω ^ 2) * x * s + (1 + ω + ω ^ 2) * x * s + s ^ 2) := by ring
        _ = (x - s) * (x ^ 2 - (ω + ω ^ 2) * x * s + ω ^ 3 * s ^ 2) := by
          rw [hω.pow_eq_one, cube_root_of_unity_sum2 hω]; simp
        _ = (x - s) * (x - s * ω) * (x - s * ω ^ 2) := by ring
    rw [h₁, h₂, h₃, h₄ (x + b / (3 * a))]
    ring_nf




  def a2 :ℚ :=1/3
  def b2 :ℚ :=-1
  def c2 :ℚ :=1
  def d2 :ℚ :=-1/3
  def q2 :ℚ := (9 * a2 * b2 * c2 - 2 * b2 ^ 3 - 27 * a2 ^ 2 * d2) / (54 * a2 ^ 3)
  #eval q2 -- 0
  def s_2_pre :=  2 * q --0
  -- def s_2 := Cubic.roots (s_2_pre) --0
  -- x = s - b / (3 * a) -- x₁ = 0 - (-1)/1 = 1
  -- ∨
  -- x = s * ω - b / (3 * a) -- x₂ = - (-1)/1 = 1
  -- ∨
  -- x = s * ω ^ 2 - b / (3 * a) -- x₃ = - (-1)/1 = 1




  -- -- 最后再看看如何解方程？
  -- -- def equation1 {x : K} := 1/3 * x ^ 3 - 1 * x ^ 2 + 1 * x - 1/3 = 0
  -- -- IsPrimitiveRoot ω 3 的ω如何显式表示？

end Field

end testroot3
