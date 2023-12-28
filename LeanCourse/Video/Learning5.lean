import Mathlib.Tactic.LinearCombination
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Mathlib.Data.Polynomial.Eval

namespace testroot3

section Field

open Polynomial

variable {K : Type*} [Field K]

variable [Invertible (2 : K)] [Invertible (3 : K)] --实际的例子可以是一个二维平面上的线性变换，比如逆时针旋转或者放大缩小。在三维空间中，可以是一个三维物体的旋转变换，比如围绕某个轴的旋转。这些都可以用矩阵来表示，并且这些矩阵都是可逆的，因为它们可以被逆转回原始状态。
-- ???好像不是这样定义的，就是纯粹的K集合上的2，3元素有逆

variable (a b c d : K)

variable {ω p q r s t : K}

-- 欧拉万岁！！！
-- 1.IsPrimitiveRoot ω k；就是k-单位根,即 (ω ^ k = 1) ∧ (∀ l : ℕ, ω ^ l = 1 → k ∣ l)
-- 2.hω.isRoot_cyclotomic
--  2.1.cyclotomic n R：n-分圆多项式，系数在R集合里，即
        -- 2.1.1.为什么：复数单位根z = e^((2πik) / n)：
          -- 复数单位根z = e^((2πik) / n)的形式可以通过欧拉公式推导得出。
          -- 欧拉公式是一个重要的数学公式，它描述了复指数函数和三角函数之间的关系。欧拉公式的表达式为：
          -- e^(ix) = cos(x) + i sin(x)
          -- 其中，e是自然对数的底数，i是虚数单位，x是实数。这个公式将指数函数和三角函数联系在一起。
          -- 现在我们考虑复数单位根，即满足zⁿ = 1的复数。假设z可以表示为z = e^(iθ)，其中θ是实数。我们希望找到满足zⁿ = 1的θ的取值。
          -- 将z代入zⁿ = 1的方程中，我们得到：
          -- (e^(iθ))ⁿ = 1
          -- 应用指数函数的幂运算法则，我们可以将上述方程改写为：
          -- e^(inθ) = 1
          -- 根据欧拉公式，左侧的e^(inθ)可以表示为：
          -- e^(inθ) = cos(nθ) + i sin(nθ)
          -- 由于右侧等于1，我们可以得到两个等式：
          -- cos(nθ) = 1
          -- sin(nθ) = 0
          -- 从三角函数的性质可知，当θ取特定值时，cos(nθ) = 1且sin(nθ) = 0成立。其中，θ的取值范围是由解方程zⁿ = 1所决定的。
          -- 我们可以观察到，当nθ = 2πk时，其中k是整数，上述两个等式成立。因此，我们可以得到：
          -- nθ = 2πk
          -- 将θ表示为θ = (2πk) / n，我们就得到了复数单位根的表达式：
          -- z = e^((2πik) / n)
          -- 这就是复数单位根的一般形式。它表示了复数单位根与欧拉公式之间的关系，其中k是整数，满足0 ≤ k < n。这个形式允许我们通过指数函数来表示复数单位根，从而方便地进行计算和处理。
        -- 2.1.2.为什么：复数单位根是圆周上均匀分布的n个点
          -- 复数单位根是圆周上均匀分布的n个点的原因与欧拉公式和三角函数的周期性特性有关。
          -- 根据欧拉公式，对于任意实数θ，有e^(iθ) = cos(θ) + i sin(θ)，其中i是虚数单位。当θ取特定值时，e^(iθ)的结果是一个复数，这个复数落在复平面上的单位圆上。
          -- 考虑复数单位根z = e^((2πik) / n)，其中k是整数，满足0 ≤ k < n。我们可以看到，当k取不同的整数值时，对应的复数单位根z落在复平面上的单位圆上。而根据欧拉公式，当θ = (2πk) / n 时，e^(iθ)的结果就是复数单位根。
          -- 由于θ的取值范围是从0到2π，我们可以将这个范围等分为n份，即0，2π/n，4π/n，...，2π(1-1/n)，这样可以得到n个不同的θ值。对应地，我们得到了n个不同的复数单位根，它们均匀地分布在单位圆上的n个点上。
          -- 这是因为三角函数（正弦和余弦）具有周期性的性质，当θ增加2π时，对应的正弦和余弦值会重新回到初始值。这意味着复数单位根也具有周期性，当k增加n时，对应的复数单位根会重新回到初始值。
          -- 因此，复数单位根是圆周上均匀分布的n个点，这是由于欧拉公式和三角函数的周期性特性导致的。
--  2.2.IsRoot p x:就是x代入p的值为0，即p的根
-- 3.cyclotomic_prime p R这个现实世界感觉没见过： p是素数的话, cyclotomic p R = ∑ i in range p, X ^ i 即： p分圆多项式=多项式（∑ i in range p, X ^ i），（X是多项式变量）
-- 4. Finset.sum_range_succ ： 求和n+1项=求和n项+（第n+1项）
theorem cube_root_of_unity_sum (hω : IsPrimitiveRoot ω 3) : 1 + ω + ω ^ 2 = 0 := by -- ???为什么可以这样定义k-单位根的第二个属性：∀ l : ℕ, ζ ^ l = 1 → k ∣ l
  have h1:= hω.isRoot_cyclotomic (by decide)
  simpa [cyclotomic_prime, Finset.sum_range_succ] using h1
#print cube_root_of_unity_sum

-- theorem cube_root_of_unity_sum2 (hω : IsPrimitiveRoot ω 3) : 1 + ω + ω ^ 2 = 0
--   := by
--   let h1 : IsRoot (cyclotomic 3 K) ω
--     := by
--     exact IsPrimitiveRoot.isRoot_cyclotomic (@of_decide_eq_true (0 < 3) (Nat.decLt 0 3) (Eq.refl true)) hω
--   have h2 :  IsRoot (cyclotomic 3 K) = IsRoot (1 + X + X ^ 2)
--     := by
--     sorry
--   simp only [IsRoot] at h2
--   simp only [IsRoot] at h1

-- theorem cube_root_of_unity_sum3 : ∀ {K : Type u_1} [inst : Field K] {ω : K},
--   IsPrimitiveRoot ω 3 → 1 + ω + ω ^ 2 = 0 :=
-- fun {K} [Field K] {ω} hω ↦
--   let_fun h1 := IsPrimitiveRoot.isRoot_cyclotomic (@of_decide_eq_true (0 < 3) (Nat.decLt 0 3) (Eq.refl true)) hω;
--   Eq.mp
--     (((congrFun
--               (congrArg IsRoot
--                 (((cyclotomic_prime K 3).trans (Finset.sum_range_succ (fun x ↦ X ^ x) 2)).trans
--                   (congrFun
--                     (congrArg HAdd.hAdd
--                       ((Finset.sum_range_succ (fun x ↦ X ^ x) 1).trans
--                         (congr (congrArg HAdd.hAdd ((Finset.sum_singleton (fun x ↦ X ^ x) 0).trans (pow_zero X)))
--                           (pow_one X))))
--                     (X ^ 2))))
--               ω).trans
--           (@IsRoot.def K ω Ring.toSemiring (1 + X + X ^ 2))).trans
--       (congrFun
--         (congrArg Eq
--           (eval_add.trans
--             (congr (congrArg HAdd.hAdd (eval_add.trans (congr (congrArg HAdd.hAdd eval_one) eval_X)))
--               ((eval_pow 2).trans (congrFun (congrArg HPow.hPow eval_X) 2)))))
--         0))
--     (IsPrimitiveRoot.isRoot_cyclotomic (@of_decide_eq_true (0 < 3) (Nat.decLt 0 3) (Eq.refl true)) hω)

-- /-- the solution of the cubic equation when p equals zero. -/
-- theorem cubic_eq_zero_iff_of_p_eq_zero
--     (ha : a ≠ 0)
--     (hω : IsPrimitiveRoot ω 3)
--     (hpz : 3 * a * c - b ^ 2 = 0)
--     (hq : q = (9 * a * b * c - 2 * b ^ 3 - 27 * a ^ 2 * d) / (54 * a ^ 3))
--     (hs3 : s ^ 3 = 2 * q)
--     (x : K) :
--     a * x ^ 3 + b * x ^ 2 + c * x + d = 0
--     ↔
--     x = s - b / (3 * a) ∨ x = s * ω - b / (3 * a) ∨ x = s * ω ^ 2 - b / (3 * a)
--       := by
--       have h₁ : ∀ x a₁ a₂ a₃ : K, x = a₁ ∨ x = a₂ ∨ x = a₃
--       ↔
--       (x - a₁) * (x - a₂) * (x - a₃) = 0
--         := by
--         intros
--         simp only [mul_eq_zero, sub_eq_zero, or_assoc]
--       have hi2 : (2 : K) ≠ 0 := nonzero_of_invertible _
--       have hi3 : (3 : K) ≠ 0 := nonzero_of_invertible _
--       have h54 : (54 : K) = 2 * 3 ^ 3 := by norm_num
--       have hb2 : b ^ 2 = 3 * a * c := by rw [sub_eq_zero] at hpz; rw [hpz]
--       have hb3 : b ^ 3 = 3 * a * b * c := by rw [pow_succ, hb2]; ring
--       have h₂ :=
--         calc
--           a * x ^ 3 + b * x ^ 2 + c * x + d =
--               a * (x + b / (3 * a)) ^ 3 + (c - b ^ 2 / (3 * a)) * x + (d - b ^ 3 * a / (3 * a) ^ 3) :=
--             by field_simp; ring
--           _ = a * (x + b / (3 * a)) ^ 3 + (d - (9 * a * b * c - 2 * b ^ 3) * a / (3 * a) ^ 3) := by
--             simp only [hb2, hb3]; field_simp; ring
--           _ = a * ((x + b / (3 * a)) ^ 3 - s ^ 3) := by rw [hs3, hq]; field_simp [h54]; ring
--       have h₃ : ∀ x, a * x = 0 ↔ x = 0 := by intro x; simp [ha]
--       have h₄ : ∀ x : K, x ^ 3 - s ^ 3 = (x - s) * (x - s * ω) * (x - s * ω ^ 2) := by
--         intro x
--         calc
--           x ^ 3 - s ^ 3 = (x - s) * (x ^ 2 + x * s + s ^ 2) := by ring
--           _ = (x - s) * (x ^ 2 - (ω + ω ^ 2) * x * s + (1 + ω + ω ^ 2) * x * s + s ^ 2) := by ring
--           _ = (x - s) * (x ^ 2 - (ω + ω ^ 2) * x * s + ω ^ 3 * s ^ 2) := by
--             rw [hω.pow_eq_one, cube_root_of_unity_sum hω]; simp
--           _ = (x - s) * (x - s * ω) * (x - s * ω ^ 2) := by ring
--       rw [h₁, h₂, h₃, h₄ (x + b / (3 * a))]
--       ring_nf

end Field

end testroot3
