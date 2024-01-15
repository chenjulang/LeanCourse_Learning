import Mathlib.Tactic.LinearCombination
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Mathlib.Data.Polynomial.Eval
import Mathlib.Data.Real.Sqrt

-- 这集的终极目标:是证明一般3次方程的求根公式的充分必要条件。
-- 也就是，除了验证3个解的合理性以外
-- ，还会给出刚好能推出3个根的过程证明。
-- 又涉及到了很有趣的关于对称的现象


namespace testroot3

section Field

open Polynomial
variable {K : Type*} [Field K]
variable [Invertible (2 : K)] [Invertible (3 : K)] --实际的例子可以是一个二维平面上的线性变换，比如逆时针旋转或者放大缩小。在三维空间中，可以是一个三维物体的旋转变换，比如围绕某个轴的旋转。这些都可以用矩阵来表示，并且这些矩阵都是可逆的，因为它们可以被逆转回原始状态。
-- ???好像不是这样定义的，就是纯粹的K集合上的2，3元素有逆
variable (a b c d : K)
variable {ω p q r s t : K}




-- 1.IsPrimitiveRoot ω k：就是k-单位根,即
-- (ω ^ k = 1)
-- ∧ (∀ l : ℕ, ω ^ l = 1  →  k ∣ l) 这样定义的合理性在哪呢？下面会讲：
-- 2.hω.isRoot_cyclotomic
--  2.1.cyclotomic n R：n-分圆多项式，z^n=1,(x-x1)(x-x2)(x-x3)...(x-xn)，系数在R集合里，即 为什么是n个单位根呢？下面会讲：
        -- 2.1.1.为什么：复数单位根是z = e^((i2πk) / n) (k=1,2,3...n) 为什么？为什么所有都可以表示呢？
          -- 复数单位根z = e^((2πik) / n)的形式可以通过欧拉公式推导得出。
          -- 欧拉公式是一个重要的数学公式，它描述了复指数函数和三角函数之间的关系。欧拉公式的表达式为：
          -- e^(ix) = cos(x) + isin(x)
          -- e^(iπ) = cos(π) + isin(π) = -1 ， e^(i2π) = 1

          -- 其中，e是自然对数的底数，i是虚数单位，x是实数。这个公式将指数函数和三角函数联系在一起。
          -- 现在我们考虑复数单位根，即满足zⁿ = 1的复数。假设z可以表示为
          -- z = Ce^(iθ)，C是实数，可以表示的原因是：z是一个任意的复数(Ccos(θ) + iCsin(θ)) =C(cos(θ) + isin(θ))=Ce^(iθ)
          -- z = Ce^(iθ)
          -- ，其中θ是实数。我们希望找到满足zⁿ = 1，即zⁿ =(C^n)e^(iθn)=1中θ的取值，此时n和i已固定。
          -- zⁿ =  (Ce^(iθ)）^n =(C^n)*e^(iθn)=1
          -- 应用指数函数的幂运算法则，我们可以将上述方程改写为：

          -- (C^n)*e^(iθn)=1
          -- 根据欧拉公式，左侧的e^(inθ)可以表示为：
          -- e^(inθ) = cos(nθ) + i sin(nθ) = 1 = e^(i2π) = cos(2π) + isin(2π) = 1 + i * 0
          -- 左边整体就是：(C^n) (cos(nθ) + i sin(nθ)) = (C^n)*cos(nθ) + i(C^n)sin(nθ)  =  1 = 1 + i * 0
          -- 由于右侧等于1，由于实数部分和复数部分分别对应相同，我们可以得到两个等式：
          -- (C^n)*cos(nθ) = 1
          -- (C^n)sin(nθ)  = 0
          -- z = Ce^(iθ)
          -- 原来的问题是求zⁿ=1的根,问题变成了要找出所有满足条件的C θ，代入到z = Ce^(iθ)，这个就是根的一般形式了
          -- (C^n)*cos(nθ) = 1
          -- (C^n)sin(nθ)  = 0  -- (C^n)=0， C=0 , 不可能的。

          -- n分为奇数，偶数讨论:
          -- n为奇数
            -- nθ = kπ , (C^n) = 1/cos(kπ)
            -- 所有满足的θ可以表示为θ = (πk) / n，我们就得到了复数单位根的表达式：
            -- z 定义= Ce^(iθ) =Ce^(iπk/n)
            -- k=奇数，C^n=-1，C=-1，-1*e^(iπk/n)
            -- k=偶数，C^n=1，C=1，1*e^(iπk/n)
              -- 由欧拉公式知道+1，-1的e表示：
              --  -1 = e^(iπ3/3) = e^(iπn/n)  由于 e^(ix) = cos(x) + isin(x)
            -- 继续改写：
            -- k=奇数，C^n=-1，C=-1，-1*e^(iπk/n)= e^(iπn/n) * e^(iπk/n) = e^(iπ(k+n)/n)
            -- k=偶数，C^n=1，C=1，1*e^(iπk/n) = e^(iπk/n)
          -- n为偶数
            -- nθ = kπ 不行的，因为代入第一行后：(C^n) = 1/cos(kπ)， k是奇数时，(C^n) = -1 ，C为实数没有虚部，不可能成立的。
            -- nθ = 2kπ 才行
            -- nθ = 2kπ, (C^n)*cos(2kπ) = (C^n) *1=1 所以 (C^n) = 1，C为实数没有虚部， 所以C=1,-1
            -- C=1的情况 z = Ce^(iθ) = 1*e^(i2kπ/n)=(cos(2kπ/n) + i*sin(2kπ/n)) k=1,2,3,4...
            -- C=-1的情况 z = Ce^(iθ) = (-1)*e^(i2kπ/n) k=1,2,3,4...
              -- 考虑(-1)*e^(i2kπ/n)的情况：(-1)*e^(i2kπ/n) = (-1*cos(2kπ/n) + i*-1*sin(2kπ/n))可以看到偶数情况下是对称的点。
              -- cos(θ) + i*sin(θ)
              -- 举例： n=4
              -- 抽象过程除了iπ外的部分： (2*1/4)  (2*2/4)  (2*3/4) (2*4/4) (2*5/4)=[2/4]
            -- 也是可以合并成e^(i2k₂π/n) k₂=1,2,3,4...

          -- 由欧拉公式知道+1，-1的e表示：
          --  -1 = e^(iπ3/3)
          --  1 = e^(iπ6/3)

          -- n是奇数的情况也可以合并成e^(i2k₂π/n) k₂=1,2,3,4...的：
          -- k=奇数，C^n=-1，C=-1，-1*e^(iπk/n)= e^(iπn/n) * e^(iπk/n) = e^(iπ(k+n)/n)
          -- k=偶数，C^n=1，C=1，1*e^(iπk/n) = e^(iπk/n)
          --  n=3 , 每次分子+2，就是2,4,6的重复
          -- 抽象过程除了iπ外的部分： （1+3）/3=4/3      （3+3）/3=6/3         （5+3）/3=8/3 = [2/3]          [4/3]
          --                                    2/3                 [4/3]                          [6/3]         [8/3]=[2/3]
          -- 所以人们就从这个规律重写了一遍公式，和并起来了，写成e^(iπ(2k₂)/n) , k₂=1,2,3,4.....

          -- ???视频 n=5，6的情况讲解一下



          -- z = e^(i2k₂π/n) k₂=1,2,3,4...
          -- e^(ix) = cos(x) + i sin(x)
          -- 以n=3举例
          -- 这里证明一个定理两边多项式相等x^3 - 1 = （x-e^(i(2π) / 3)）*（x-e^(i(2*2π) / 3)）* （x-e^(i(3*2π) / 3)）=(x-x1)(x-x2)(x-x3)
          --
          -- 右边= （x-e^(i(1*2π) / 3)）*（x-e^(i(2*2π) / 3)）* （x-e^(i(3*2π) / 3)）
            -- 分配律= x^3 - e^(i(2π) / 3)*e^(i(2*2π) / 3)*e^(i(3*2π) / 3) + ...
            -- e^(i(2π) / 3)*e^(i(2*2π) / 3)*e^(i(3*2π) / 3) = e^(i(4π)
            --抽象写法= x^3 - 1 + x*(（2+3）+（1+3）+（1+2）) + x^2*（-1）(3+2+1)
          -- =  x^3 - 1 + x * (cos(5* 2π/3)+cos(4* 2π/3)+ cos(3* 2π/3)  +  i sin(5* 2π/3) +  i sin(4* 2π/3) +  i sin(3* 2π/3)) +
          -- x^2* （-1）（cos(3* 2π/3)+cos(2* 2π/3)+cos(1* 2π/3) + i sin(3* 2π/3 + i sin(2* 2π/3）+i sin(1* 2π/3））
          -- 关于x轴对称的一对对，对称的奇妙之处，后面讲一下???n=5的情况

          -- todo???后面单独讲：我们试一下n=4,x^4 - 1 = （x-e^(i(1*2π) / 4)）*（x-e^(i(2*2π) / 4)）* （x-e^(i(3*2π) / 4)） * （x-e^(i(4*2π) / 4)）
          -- x^4 - 1(这个1只要π的整数倍即得1，不需要2π得整数倍)
          -- 抽象写法 x^1* （(2+3+4)+(1+3+4)+(1+2+4)+(1+2+3)）
          -- 后面讲一下???n=6的情况

          -- z = e^(i2k₂π/n) k₂=1,2,3,4...
          -- 验证一下是否满足：(ω ^ m = 1) ∧ (∀ l : ℕ, ω ^ l = 1  →  m ∣ l)
          -- 此时m=3,
          -- 验证ω=x1，即ω=e^(i(2π) / 3)=cos(2π/3) + i*sin(2π/3) 是否满足，∀ l : ℕ, ω ^ l = 1 ，只有l是m=3的倍数时成立?
            -- 我们尝试l=1,2,3则不用尝试代入就知道结果为1,4即1，5即2，6即3所以结果也是1，后面都是循环的，所以实际上只需要验证l=1,2
            -- l=1,2是否满足ω ^ l = 1 呢？我们要证明它不满足，因为e^(i(2π1) / 3) 、 e^(i(2π2) / 3) 都不是 e^(i2πk) 这个2π的整数倍，所以不等于1
          -- 验证ω=x2，即ω=e^(i(4π) / 3)=cos(4π/3) + i*sin(2π/3) 是否满足，∀ l : ℕ, ω ^ l = 1 ，只有l是m=3的倍数时成立
            -- 我们尝试l=1,2,3不用尝试代入知道是2π的整数倍，所以就变成了验证次数，i后面的项是否2π的整数倍。
            -- l=1,2代入可知e^(i(4π) *1/ 3) 、 e^(i(4π)*2 / 3)， 都无法和分母3约掉，即不是整数倍，所以不等于1
          -- 验证ω=x3，即ω=e^(i(6π) / 3) = e^(i(2π))=1， 这个却是不满足：(ω ^ m = 1) ∧ (∀ l : ℕ, ω ^ l = 1  →  m ∣ l)的，因为l是1，2也满足。

          -- 所以在lean里面定义的IsPrimitiveRoot ω k这个根呢，是去掉1的。

          -- 这就是复数单位根的一般形式。它表示了复数单位根与欧拉公式之间的关系，其中k是整数，
          -- 满足0 ≤ k < n。这个形式允许我们通过指数函数来表示复数单位根，从而方便地进行计算和处理。
        -- 2.1.2.为什么：复数单位根是圆周上均匀分布的n个点
          -- 由于根形式是z = e^(iθ) = e^((i2πk) / n) 根据欧拉公式e^(iθ) = cos(θ) + i sin(θ)变成
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
    let h1 : IsRoot (cyclotomic 3 K) ω -- cyclotomic 3 K代表的是 (x-x1)(x-x2)(x-x3)
      := by
      refine' IsPrimitiveRoot.isRoot_cyclotomic _ _
      -- 我们就不点进去看了，只感性的证明：
      · exact Nat.succ_pos 2
      · exact hω
      -- ω ^ 3 = 1
      -- 现实中已知x^3 - 1 = （x-e^(i(2π) / 3)）*（x-e^(i(2*2π) / 3)）* （x-e^(i(3*2π) / 3)）
      -- 举例：ω = e^(i(2π) / 3)   -- e^(i(2*2π) / 3）
      -- 即x^3 - 1 = (x-ω)(x-ω^2)(x-ω^3) --???为什么这么巧呢？任意一个k-单位根，都可以自乘生成所有的复数根
      -- 两边除以(x-1)，得到(x-ω)(x-ω^2) = 1 + x + x^2
      -- 得出 (x-ω)(x-ω^2)的根 = 1 + x + x^2的根
      -- 也就是ω，ω^2= 1 + x + x^2的根
      -- 也就是ω，ω^2,1这三个数= (1 + x + x^2)(x-1)的根 = x^3 - 1的根 = （x-e^(i(2π) / 3)）*（x-e^(i(2*2π) / 3)）* （x-e^(i(3*2π) / 3)）的根= 分圆多项式的根
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
    have h3 : (eval ω (1 + X + X ^ 2)=0) = (1 + ω + ω ^ 2 = 0) -- ???eval x p是: x代入多项式p的值
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








end Field
end testroot3
