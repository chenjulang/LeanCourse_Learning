  import Mathlib.Tactic.LinearCombination
  import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
  import Mathlib.Data.Polynomial.Eval
  import Mathlib.Data.Real.Sqrt

  -- 这集的终极目标:是证明一般3次方程的求根公式的充分必要条件。当然不是一个初等的证明，应该找一个初等的证明形式化比较好。
  -- 也就是，除了验证3个解的合理性以外
  -- ，还会给出刚好能推出3个根的过程证明。
  -- 又涉及到了很有趣的关于对称的现象


  namespace testroot3

  section Field

  open Polynomial
  variable {K : Type*} [Field K]
  variable [Invertible (2 : K)] [Invertible (3 : K)] --实际的例子可以是一个二维平面上的线性变换，比如逆时针旋转或者放大缩小。在三维空间中，可以是一个三维物体的旋转变换，比如围绕某个轴的旋转。这些都可以用矩阵来表示，并且这些矩阵都是可逆的，因为它们可以被逆转回原始状态。
  -- 好像不是这样定义的，就是纯粹的K集合上的2，3元素有逆
  variable (a b c d : K)
  variable {ω p q r s t : K}




  -- 1.IsPrimitiveRoot ω k：w就是k-本原单位根,即
  -- (ω ^ k = 1)
  -- ∧ (∀ l : ℕ, ω ^ l = 1  →  k ∣ l) 这样定义的合理性在哪呢？下面会讲：
  -- 2.hω.isRoot_cyclotomic
  --  2.1.cyclotomic n R：n-分圆多项式，z^n=1,(x-x1)(x-x2)(x-x3)...(x-xn)，系数在R集合里，即 为什么是n个复数根呢？下面会讲：
          -- 2.1.1.为什么：z^n=1的复数单位根一般形式是 z = e^((i2πk) / n) (k=1,2,3...n) 为什么？为什么所有都可以表示呢？
            -- 复数单位根z = e^((2πik) / n)的形式可以通过欧拉公式推导得出。
            -- 欧拉公式是一个重要的数学公式，它描述了复指数函数和三角函数之间的关系。欧拉公式的表达式为：
            -- e^(ix) = cos(x) + isin(x)
            -- e^(iπ) = cos(π) + isin(π) = -1 ， e^(i2π) = 1

            -- 其中，e是自然对数的底数，i是虚数单位，x是实数。这个公式将指数函数和三角函数联系在一起。
            -- 现在我们考虑复数单位根，即满足zⁿ = 1的复数。假设z可以表示为 如何表示任意的复数呢？
            -- z = Ce^(iθ)，C是实数，可以表示的原因是：z是一个任意的复数(Ccos(θ) + iCsin(θ)) =C(cos(θ) + isin(θ))=Ce^(iθ)
            -- z = Ce^(iθ) ， C，θ 一同代表了一个复数
            -- ，其中θ是实数。我们希望找到满足zⁿ = 1，即zⁿ =(C^n)e^(iθn)=1中θ的取值，此时n和i已固定。
            -- 问题转化成：(C^n)*e^(iθn)=1
            -- 根据欧拉公式，左侧的e^(inθ)可以表示为：
            -- e^(inθ) = cos(nθ) + i sin(nθ) = 1 = e^(i2π) = cos(2π) + isin(2π) = 1 + i * 0
            -- 左边整体就是：(C^n) (cos(nθ) + i sin(nθ)) = (C^n)*cos(nθ) + i(C^n)sin(nθ)  =  1 = 1 + i * 0
            -- 由于右侧等于1，由于实数部分和复数部分分别对应相同，我们可以得到两个等式：
            -- 问题转化成：所有满足以下2个条件的C,θ
            -- (C^n)*cos(nθ) = 1
            -- (C^n)sin(nθ)  = 0
            -- 第二个等式是突破口
            -- (C^n)*cos(nθ) = 1
            -- (C^n)sin(nθ)  = 0  -- (C^n)=0， C=0 , z = 0，zⁿ = 1 不可能的。排除了左边为0
            -- nθ = kπ // 第一个结论

            -- 分类讨论n
            -- n分为奇数，偶数讨论:
            -- n为奇数
              -- nθ = kπ , (C^n) = 1/cos(kπ)
              -- 所有满足的θ可以表示为θ = (πk) / n，我们就得到了复数单位根的表达式：
              -- z 定义= Ce^(iθ) = Ce^(iπk/n)
              -- 分类讨论k
              -- k=奇数，C^n=-1，C是实数， C=-1，z= -1*e^(iπk/n)
              -- k=偶数，C^n=1，C是实数,C=1，z= 1*e^(iπk/n)
                -- 由欧拉公式知道+1，-1的e表示：
                --  -1 = e^(iπ3/3) = e^(iπn/n)  由于 e^(ix) = cos(x) + isin(x)
              -- 继续改写：
              -- k=奇数，C^n=-1，C=-1，-1*e^(iπk/n)= e^(iπn/n) * e^(iπk/n) = e^(iπ(k+n)/n)
              -- k=偶数，C^n=1，C=1，1*e^(iπk/n) = e^(iπk/n)
              -- 由欧拉公式知道+1，-1的e表示：
              --  -1 = e^(iπ3/3)
              --  1 = e^(iπ6/3)
              -- n是奇数的情况也可以合并成e^(i2k₂π/n) k₂=1,2,3,4...的：
              -- k=奇数，C^n=-1，C=-1，-1*e^(iπk/n)= e^(iπn/n) * e^(iπk/n) = e^(iπ(k+n)/n)
              -- k=偶数，C^n=1，C=1，1*e^(iπk/n) = e^(iπk/n)
              --  n=3 , 每次分子+2，就是2,4,6的重复
              -- (k+n)/n
              -- k/n
              -- e^(iπA) = cos(Aπ) + isin(Aπ)
              -- 抽象过程除了iπ外的部分： （1+3）/3=4/3      （3+3）/3=6/3         （5+3）/3=8/3 = [2/3]          [4/3]
              --                                    2/3                 [4/3]                          [6/3]         [8/3]=[2/3]
              -- 所以人们就从这个规律重写了一遍公式，和并起来了，写成e^(iπ(2k₂)/n) , k₂=1,2,3,4.....
              -- 这里也把奇偶情况合并成了统一的形式：e^(i2kπ/n)，k=1,2,3,4...
            -- n为偶数
              -- nθ = kπ k是奇数时，是不行的，因为代入第一行后：(C^n) = 1/cos(kπ)， k是奇数时，(C^n) = -1 ，C为实数没有虚部，不可能成立的。
              -- nθ = 2kπ 才行
              -- nθ = 2kπ, (C^n)*cos(2kπ) = (C^n) *1= 1 所以 (C^n) = 1，C为实数没有虚部， 所以C=1,-1
              -- 分类讨论C=+1,-1
              -- C=1的情况 z = Ce^(iθ) = 1*e^(i2kπ/n)=(cos(2kπ/n) + i*sin(2kπ/n)) k=1,2,3,4...
              -- C=-1的情况 z = Ce^(iθ) = (-1)*e^(i2kπ/n) k=1,2,3,4...
                -- 考虑(-1)*e^(i2kπ/n)的情况：(-1)*e^(i2kπ/n) = (-1*cos(2kπ/n) + i*-1*sin(2kπ/n))可以看到偶数情况下是对称的点。
                -- e^(iπn/n) * e^(i2kπ/n) = e^(iπ(2k+n)/n) k=1,2,3,4...
                -- e^(iπA) = cos(Aπ) + isin(Aπ)
                -- 举例： n=4
                -- (2k+n)/n:
                -- 6/4 8/4 10/4=2/4 12/4=4/4 [6/4]
                -- 也是可以合并成e^(iπ2k₂/n) k₂=1,2,3,4...
              -- 合并成了统一的形式e^(i2kπ/n)，k=1,2,3,4...


            -- 视频 n=5，6分别是奇数，偶数的情况讲解一下
            -- n=5
            -- k=奇数，C^n=-1，C=-1，-1*e^(iπk/n)= e^(iπn/n) * e^(iπk/n) = e^(iπ(k+n)/n)
            -- k=偶数，C^n=1，C=1，1*e^(iπk/n) = e^(iπk/n)
            -- (1+5)/5=6/5        (3+5)/5=8/5           (5+5)/5=10/5=0           (7+5)/5=12/5=[2/5]
            --              2/5                  4/5                      [6/5]                       [8/5]
            -- n=6
            -- C=1的情况 z = Ce^(iθ) = 1*e^(i2kπ/n)=(cos(2kπ/n) + i*sin(2kπ/n)) k=1,2,3,4...
            -- C=-1的情况 z = Ce^(iθ) = (-1)*e^(i2kπ/n) k=1,2,3,4...
            -- 抽象过程除了iπ外的部分： 2*1/6=2/6  2*2/6=4/6 2*3/6=6/6 2*4/6=8/6 2*5/6=10/6 2*6/6=12/6=0 2*7/6=14/6=[2/6]


          -- ----------------分割线，以上就证明了n次复数根的一般表达方式，能表达全体的n次复数根---------------/
          -- 下面讨论分圆多项式

            -- “递进式证明”，中国古代数学类似这样，可以证明起来舒服一点～～～，而不是直接一般化

          -- 以下部分分析n取各个值时{z = e^(i2k₂π/n) k₂=1,2,3,4...}的分圆多项式是什么： （注意：k=1的项必定为本原根。）
            -- 分圆多项式，只是一个构造定义，良定义，<=n的，指所有能生成全体复数根的复数根，也叫本原根，x1,x2,...xm , 然后拼成多项式(x-x1)(x-x2)...(x-xm)：
            -- n=1 ,z^n=1 很明显只有一个复数根，本原根也只有一个。
              --（x-e^(i(2π) / 1)）= x-1
            -- n=2 ，除了k=1,就没有了。
              -- （x-e^(i(1*2π) / 2)） = （x-e^(i1π）） = (x- -1) = (x+1)
            -- n=3, 除了k=1, 还有k=2,因为所有根为 2/3 4/3 6/3=0 ， 所以4/3 通过整数倍可以生成其他的2*4/3=8/3=[2/3] 3*4/3=12/3=[6/3]=0 16/3=[4/3] [8/3]每次分子加4
              -- （x-e^(i(1*2π)/3)）* （x-e^(i(2*2π)/3)））=
              -- x^2系数:4/3 + 2/3 = 2 ， 是1
              -- x^1系数: -e^(i(1*2π)/3) -e^(i(2*2π)/3)） =  -e^(i(1*2π)/3) -e^(i(2*2π)/3)）= - （-1/2 + -1/2） = -（-1） = 1 刚好凑成1?试下其他奇数
              -- x^0系数:（2+4）/3 = 2 ， 也是1
              -- 所以结果是 x^2 + x + 1
             -- n=4 ，除了k=1,还有k=3 , （其实这里已经发现规律，满足的k，k都是和n互质的）
              -- （x-e^(i(1*2π)/4)）* （x-e^(i(3*2π)/4)））= x^2+1
              -- x^2系数: 1
              -- x^1系数: -e^(i(1*2π)/4) -e^(i(3*2π)/4)）= - （0 + 0 ） = 0
              -- x^0系数: 2/4 + 6/4 = 8/4 = 2 刚好是2的整数倍,所以是1
             -- n=5, 除了k=1,还有k=2,3,4 , 因为2，3，4都和5互质
              -- （x-e^(i(1*2π)/5)）* （x-e^(i(2*2π)/5)） *（x-e^(i(3*2π)/5)）*（x-e^(i(4*2π)/5)）=
              -- x^4系数:1
              -- x^3系数: -(e^(i(1*2π)/5) + e^(i(2*2π)/5) + e^(i(3*2π)/5) + e^(i(4*2π)/5)) = ? 画图可知，这4个
                -- cos(2π/5) + cos(4π/5) 为什么是-0.5?
                -- 因为单独每一项化成根号计算，是不一定能成功的，所以要找规律，其实是一个巧合，是韦达定理得到的：
                -- 因为(2π/5)和(4π/5) 都满足 5θ = 2kπ , 也就是说θ这里可以取(2π/5)和(4π/5)
                -- cos3θ =cos (5θ - 2θ) (由5θ = 2kπ)=  cos(2kπ - 2θ) = cos2θ
                -- 根据n倍角公式 cos3θ = 4(cosθ)^3 - 3cosθ ; cos2θ = 2(cosθ)^2 - 1
                -- 4(cosθ)^3 - 3cosθ = 2(cosθ)^2 - 1
                -- 记cosθ 为 x
                -- 4x^3 - 2x^2 - 3x + 1 = 0
                -- 上面方程有根x=1, 因此可以化简：(x-1)(4x^2 + 2x - 1) = 0
                -- x化回来cosθ :(x-1)(4cosθ^2 + 2cosθ - 1) = 0，θ这里可以取(2π/5)和(4π/5)
                -- 所以(2π/5)和(4π/5) 代入(4cosθ^2 + 2cosθ - 1) 后为0， 不可能代入x-1=0
                -- 所以(2π/5)和(4π/5) 是(4cosθ^2 + 2cosθ - 1)=0的根
                -- 韦达定理知根与系数的关系：x1+x2 = -b/a = -2/4 = -1/2
                -- 因此-(e^(i(1*2π)/5) + e^(i(2*2π)/5) + e^(i(3*2π)/5) + e^(i(4*2π)/5)) = -（2* -1/2） = 1
                  -- (可以总结规律n=奇数时，x轴上的cos(2kπ/n)和都是-1/2,x轴下面是对称同样的值，所以就是-1/2的2倍= -1，加上符号就是1)
              -- x^2系数:（2+4）/5  +  （2+6）/5  +  （2+8）/5  +  （4+6）/5  +  （4+8）/5  +  （6+8）/5 =  （2+4+6+8）*3/5 = （2+8）*4/2 *3/5 = 12，所以是1
              -- x^1系数: （4+6+8）/5 + （2+6+8）/5 + （2+4+8）/5 + （2+4+6）/5 = （2+4+6+8）*3/5 = 12 ， 所以是1
              -- x^0系数:（2+4+6+8）/5 = (2+8) * 4/2/5 = 4, 所以是1
            -- n=6, 除了k=1,还有k=5
              -- （x-e^(i(1*2π)/6)）*（x-e^(i(5*2π)/6)） = x^2-x+1?
              -- x^2系数:1
              -- x^1系数:cos(1*2π/6) + cos(5*2π/6) = (-1/2 + -1/2) = -1
              -- x^0系数:2/6 + 10/6 = 12/6 = 2 ， 所以是1
            -- n=8, 除了k=1,还有k=3,5,7
              -- （x-e^(i(1*2π)/8)）*（x-e^(i(3*2π)/8)）*（x-e^(i(5*2π)/8)） *（x-e^(i(7*2π)/8)）=x^4+1？
              -- x^4系数:1
              -- x^3系数: cos(1*2π/8) + cos(3*2π/8) + cos(5*2π/8) + cos(7*2π/8) -- x轴上下对称的点，上面是互质的，下面也是互质的
              -- x^2系数: cos(（1+3）*2π/8)  + cos(（1+5）*2π/8) + cos(（1+7）*2π/8) + cos(（3+5）*2π/8) + cos(（3+7）*2π/8) + cos(（5+7）*2π/8) = 0 分别是16减去某两项，会有对称???
              -- x^1系数: cos(1*2π/8) + cos(3*2π/8) + cos(5*2π/8) + cos(7*2π/8) = 0 对称抵消
              -- x^0系数:(1+3+5+7)*2/8 = 16*2/8 = 4, 所以是1


          -- 以下部分是引理1的举例和证明：x^n-1 = (满足n|3 的所有n分圆多项式连乘)
          -- lean的名称是prod_cyclotomic_eq_X_pow_sub_one （其中关键子引理是nthRoots_one_eq_biUnion_primitiveRoots'）
            -- 举例：x^3-1 = d|3 的所有d分圆多项式连乘,此处数量是3的因子的个数 = 1分圆 * 3分圆
            -- n=3
              -- （x-1） *  (x^2 + x + 1) = ? 通过计算互相抵消的巧合，得到是x^3-1
            -- ???也就是冯克勤的P.143的23节定理1：
              -- 要严格证明这一点，需要单独出一个视频讲，其实就是转化成原根类似的问题，证明方法基本一摸一样，作图解释就知道了：
              -- 20节定理2的推论
              --    第8节定理4 给出了类似的证明，所以要自己再做一次类似证明 还没证明--todo
                --    原根是什么？ 因为φ(7)= 与7互质且小于7的整数个数,有1,2,3,4,5,6=6。3 是模 7 的一个“原根”，因为3^n = 分别等于3,2,6,4,5,1  (mod 7) n=1,2,3,...6
                  --即最小的次数为6 = φ(7)的话，3就是模7的一个原根，这里数3的“阶”是6，因为6满足3^n=1的这些n里面，6是最小的那个。换句话说，它可以生成模 7环境下的小于7的所有数。
                -- 开始证明：
                  -- 先举例：
                    -- m=7 , d 是
                    -- φ(7)=6的一个约数，比如
                    -- 取d=2,g是原根比如
                    -- g=3, 则模7环境下共有φ(d)=φ(2)=1个数A，A满足阶为d=2。其实A=6 ，
                    --  具体定义是{g^(φ(m)*k/d) | 1<=k<=d,(k,d)=1}
                    -- 验证一下是不是： 与d=2互质的数只有取k=1，g^(φ(m)*k/d) = g^(6*k/2) = 3^(6*1/2) = 3^(3) = 27 ，它在模7环境下是6
                  -- 再举例证明：
                  -- 引理1: 任意l，
                    -- g^l的阶为d ↔ φ(m)/(l,φ(m))=d， 换位φ(m)/d=(l,φ(m))  换句话说， 任意l,d, 这里d取2，  3^l的阶为2 ↔ 6/(l,6)=2 --todo这里就不深入下去了，有兴趣可以看一下，我发一下资源，还有相关up主。
                    -- 取φ(m)=dd' , l=d'k , 具体就是6 = 2 * 3 ，所以取d'=3, l = 3 * k ,
                    -- l可以取1<=l<=φ(m)=6, 取l=3,则k=1
                    -- ↔  3^3=27 = 6（mod 7） 的阶为 2 , 验证6^2= 36 = 1 (mod 7)
                    -- 因为l=d'k, 所以k取1，l=3; 满足 (l,φ(m))=φ(m)/d=6/2=3
                      -- k取2，l=6;不满足 (l,φ(m))=3
                  -- 再一般证明：
              -- + 20节中（6）的证明：
              --      需要看第8节定理1


          -- 以下部分是IsPrimitiveRoot定义的合理性说明：换句话说，是否存在这样的复数根，满足第二个条件的呢？：
            -- 即验证一下是否满足：(ω ^ m = 1) ∧ (∀ l : ℕ, ω ^ l = 1  →  m ∣ l)
            -- z = e^(i2k₂π/n) k₂=1,2,3,4...
            -- 举例取m=3,
            -- 验证两个本原根：e^(i(2π) / 3)，e^(i(4π) / 3)
              -- 验证ω=x1，即ω=e^(i(2π) / 3)=cos(2π/3) + i*sin(2π/3) 是否满足，∀ l : ℕ, ω ^ l = 1  →  m ∣ l
                -- 列举所有l的值，先分析一下：
                -- l=1, ω ^ l = e^(i(2π1) / 3) ≠ 1 (只有i的系数是2π，整体结果才是1)
                -- l=2, ω ^ l = e^(i(2π2) / 3) ≠ 1
                -- l=3, ω ^ l = e^(i(2π3) / 3) = 1
                -- 由于2π 为周期，4等价于1，5即2，6即3所以结果也是1，后面都是循环的。
              -- 验证ω=x2，即ω=e^(i(4π) / 3)=cos(4π/3) + i*sin(2π/3) 是否满足，∀ l : ℕ, ω ^ l = 1 ，只有l是m=3的倍数时成立
                -- 我们尝试l=1,2,3不用尝试代入知道是2π的整数倍，所以就变成了验证次数，i后面的项是否2π的整数倍。
                -- l=1, ω ^ l = e^(i(4π1) / 3)  ≠ 1
                -- l=2, ω ^ l = e^(i(4π2) / 3)  ≠ 1
                -- l=3, ω ^ l = e^(i(4π3) / 3)  = 1


            -- 这就是复数单位根的一般形式。它表示了复数单位根与欧拉公式之间的关系，其中k是整数，
            -- 满足0 ≤ k < n。这个形式允许我们通过指数函数来表示复数单位根，从而方便地进行计算和处理。
          -- 2.1.2.为什么：复数单位根是圆周上均匀分布的n个点：
            -- 由于根形式是z = e^(iθ) = e^((i2πk) / n) 根据欧拉公式e^(iθ) = cos(θ) + i sin(θ)变成
            --  这里θ即(2πk) / n， 所以就是 （360度/n）* 1，2，3，4......，
            -- 也就是z = e^(iθ) = e^((2πik) / n) = cos((2πk) / n) + i sin((2πk) / n) 表示成二维的数就知道
  --  2.2.IsRoot p x:就是x代入p的值为0，即p的根
  -- 3.cyclotomic_prime p R：是一个多项式， p是素数, cyclotomic p R = ∑ i in range p, X ^ i
  --    即： p分圆多项式=多项式（∑ i in range p, X ^ i），（X是多项式变量）
  -- 4. Finset.sum_range_succ ： 求和n+1项=求和n项 +（第n+1项）


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
        -- 3分圆 定义= (x-x1)(x-x2)
        -- IsPrimitiveRoot.isRoot_cyclotomic 说的是：
        -- ω是3次本原根 → ω是3分圆多项式的根 ； 换句话说，ω是{x1,x2}其中一个，代入多项式(x-x1)(x-x2)当然结果为0.
        done
        -- exact IsPrimitiveRoot.isRoot_cyclotomic (@of_decide_eq_true (0 < 3) (Nat.decLt 0 3) (Eq.refl true)) hω
      have h2 :  IsRoot (cyclotomic 3 K) = IsRoot (1 + X + X ^ 2)
        := by
        rw [cyclotomic_prime]-- ???其实就是引理1的推论：(x^n-1)/(x-1) = 一个次数从n-1递减到0的多项式。
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
        ↔
        (x - a₁) * (x - a₂) * (x - a₃) = 0
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
        contrapose! hp_nonzero with hs_nonzero --contrapose! 是逆否命题 非A→ 非B  换句话说 B→ A
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
        exact mul_eq_mul_left_iff.1 (lc1_1)
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
        -- simp only [pow_eq_zero_iff]
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
      linear_combination --???这里抽一集具体算一下为什么等式左右成立，以及为何要这样拆。
        hr +
        lc1 -
        lc2 +
        lc3
      -- linear_combination -- 原始写法
      --   hr + (-q + r + s ^ 3) * hs3 - (3 * x * s ^ 3 + (t * s) ^ 2 + t * s * p + p ^ 2) * ht +
      --   (x ^ 2 * (s - t) + x * (-ω * (s ^ 2 + t ^ 2) + s * t * (3 + ω ^ 2 - ω)) -
      --     (-(s ^ 3 - t ^ 3) * (ω - 1) + s ^ 2 * t * ω ^ 2 - s * t ^ 2 * ω ^ 2)) * s ^ 3 * H
      done


    /-- 三次方项系数为1的形式 -/
    theorem cubic_monic_eq_zero_iff2
    (hω : IsPrimitiveRoot ω 3) --b c任意取
    (hp : p = (3 * c - b ^ 2) / 9) -- p 从b和c定义出来
    (hp_nonzero : p ≠ 0) -- p有一个限制条件
    (hq : q = (9 * b * c - 2 * b ^ 3 - 27 * d) / 54) -- q 从b和c和d定义出来
    (hr : r ^ 2 = q ^ 2 + p ^ 3) -- r 从q和p定义出来
    (hs3 : s ^ 3 = q + r) -- s 从r和q定义出来
    (ht : t * s = p) -- t 从s和p定义出来
    (x : K)
    :
    (x ^ 3 + b * x ^ 2 + c * x + d = 0)
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
      have h₁ : x ^ 3 + b * x ^ 2 + c * x + d -- 这个就是把二次项去掉的核心定理
      = y ^ 3 + 3 * p * y - 2 * q := by
        rw [hp, hq]
        field_simp [h9] -- 所有分母都乘了一遍其实，由y导致的
        field_simp [h54]
        ring
      have h2 := cubic_basic_eq_zero_iff2 hω hp_nonzero hr hs3 ht y
      rw [h₁, h2]
      simp only
      repeat rw [eq_sub_iff_add_eq] -- rw长龙～～～
      -- rw [eq_sub_iff_add_eq]
      -- rw [eq_sub_iff_add_eq]
      -- rw [eq_sub_iff_add_eq]
      -- rw [eq_sub_iff_add_eq]
      -- rw [eq_sub_iff_add_eq]
      -- rw [eq_sub_iff_add_eq]
      -- rw [eq_sub_iff_add_eq]
      -- rw [eq_sub_iff_add_eq]
      -- rw [eq_sub_iff_add_eq]
      -- simp_rw [eq_sub_iff_add_eq] --替换写法
      done



    /-- 判定式为非零，通用的一般形式，求出三个解 -/
    theorem MainGoal5 -- a b c d任意取
    (ha : a ≠ 0) -- a有一个限制条件
    (hω : IsPrimitiveRoot ω 3)
    (hp : p = (3 * a * c - b ^ 2) / (9 * a ^ 2)) -- p 由a,b,c定义出来
    (hp_nonzero : p ≠ 0) -- 判定式p的一个限制条件
    (hq : q = (9 * a * b * c - 2 * b ^ 3 - 27 * a ^ 2 * d) / (54 * a ^ 3)) -- q 由a,b,c,d定义出来
    (hr : r ^ 2 = q ^ 2 + p ^ 3) -- r 由q,p定义出来
    (hs3 : s ^ 3 = q + r) -- s 由r,q定义出来
    (ht : t * s = p)  -- t 由s,p定义出来
    (x : K)
    :

    (a * x ^ 3 + b * x ^ 2 + c * x + d = 0)
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
      have h54 : (54 : K) = 2 * 3 ^ 3 := by norm_num -- 模进的感觉
      have h₁ : a * x ^ 3 + b * x ^ 2 + c * x + d
      = a * (x ^ 3 + b / a * x ^ 2 + c / a * x + d / a) --a写到分母
        := by
        field_simp
        ring
      have h₂ : ∀ x,
      a * x = 0
      ↔
      x = 0
        := by
        intro x
        simp [ha]
      have hp' :
      p
      = (3 * (c / a) - (b / a) ^ 2) / 9
        := by
        rw [hp]
        field_simp --将分子上的分母先约分去掉
        field_simp [h9] --先用h9替换，再去分母的意思
        ring_nf
      have hq' : q
      = (9 * (b / a) * (c / a) - 2 * (b / a) ^ 3 - 27 * (d / a)) / 54
      := by
        rw [hq]
        field_simp
        field_simp [h54]
        ring_nf
      have h3:= cubic_monic_eq_zero_iff2 (b / a) (c / a) (d / a) hω hp' hp_nonzero hq' hr hs3 ht x
      rw [h₁, h₂, h3] -- h1和h2去掉三次项系数，
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




    /-- 判定式为零，通用的一般形式，求出三个解 -/
    theorem cubic_eq_zero_iff_of_p_eq_zero
    (ha : a ≠ 0)
    (hω : IsPrimitiveRoot ω 3)
    (hpz : 3 * a * c - b ^ 2 = 0) --判定式3 * a * c - b ^ 2 为零
    (hq : q = (9 * a * b * c - 2 * b ^ 3 - 27 * a ^ 2 * d) / (54 * a ^ 3)) -- q 从a,b,c,d定义而来
    (hs3 : s ^ 3 = 2 * q) -- s 从q定义而来
    (x : K) :

    a * x ^ 3 + b * x ^ 2 + c * x + d = 0
    ↔
    x = s - b / (3 * a)
    ∨
    x = s * ω - b / (3 * a)
    ∨
    x = s * ω ^ 2 - b / (3 * a)
      := by
      have h₁ : ∀ x a₁ a₂ a₃ : K,
        x = a₁ ∨ x = a₂ ∨ x = a₃
        ↔
        (x - a₁) * (x - a₂) * (x - a₃) = 0
        := by
        intros
        simp only [mul_eq_zero]
        simp only [sub_eq_zero]
        simp only [or_assoc]
      have hi2 : (2 : K) ≠ 0 := nonzero_of_invertible _
      have hi3 : (3 : K) ≠ 0 := nonzero_of_invertible _
      have h54 : (54 : K) = 2 * 3 ^ 3 := by norm_num
      have hb2 : b ^ 2 = 3 * a * c
        := by
        rw [sub_eq_zero] at hpz
        rw [hpz]
      have hb3 : b ^ 3 = 3 * a * b * c
        := by
        rw [pow_succ, hb2]
        ring
      have h₂ :=
        calc
          a * x ^ 3 + b * x ^ 2 + c * x + d
          = a * (x + b / (3 * a)) ^ 3 + (c - b ^ 2 / (3 * a)) * x + (d - b ^ 3 * a / (3 * a) ^ 3)
            :=by
            field_simp --???为什么可以这样拼凑去掉二次项
            ring
          _ = a * (x + b / (3 * a)) ^ 3 + (d - (9 * a * b * c - 2 * b ^ 3) * a / (3 * a) ^ 3)
            := by
            simp only [hb2]
            simp only [hb3]
            field_simp
            ring --???
          _ = a * ((x + b/(3 * a)) ^ 3 - s ^ 3) -- 这整个步骤其实就是把x的二次项，一次项都消除了
            := by
            rw [hs3, hq]
            field_simp [h54]
            ring_nf --???
      have h₃ : ∀ x,
      a * x = 0
      ↔
      x = 0
        := by
        intro x
        simp [ha]
      have h₄ : ∀ x : K,
      x ^ 3 - s ^ 3
      = (x - s) * (x - s * ω) * (x - s * ω ^ 2)
        := by
        intro x
        calc
          x ^ 3 - s ^ 3
          = (x - s) * (x ^ 2 + x * s + s ^ 2)
            := by
            ring
          _ = (x - s) * (x ^ 2 - (ω + ω ^ 2) * x * s + (1 + ω + ω ^ 2) * x * s + s ^ 2)
            := by
            ring
          _ = (x - s) * (x ^ 2 - (ω + ω ^ 2) * x * s + ω ^ 3 * s ^ 2)
            := by
            rw [hω.pow_eq_one, cube_root_of_unity_sum2 hω]
            simp
          _ = (x - s) * (x - s * ω) * (x - s * ω ^ 2)
            := by
            ring --???因式分解的来处
      rw [h₁, h₂, h₃, h₄ (x + b / (3 * a))]
      ring_nf



  end Field
  end testroot3
