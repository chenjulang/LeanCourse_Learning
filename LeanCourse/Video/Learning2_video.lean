import Paperproof
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.Data.Real.Sqrt

-- 从零开始用数学AI形式化证明：“矩阵的逆”

namespace Matrix

  def m2 : Type := ℕ
  def n2 : Type := ℕ
  def α2 : Type := ℝ

  -- #check (Finset Nat)

  variable
  [Fintype n2]
  [DecidableEq n2]
  [CommRing α2]

  variable (A : Matrix n2 n2 α2) (B : Matrix n2 n2 α2)

  -- 前置的知识
  def matrix1 : Matrix (Fin 2) (Fin 2) ℝ :=
  ![![1, 2],
    ![3, 4]]
  -- #eval matrix1 0 0 -- 1
  -- #eval matrix1 1 0
  def matrix2 : Matrix (Fin 2) (Fin 2) ℝ :=
  ![![5, 6],
    ![7, 8]]
  def matrixUnit : Matrix (Fin 2) (Fin 2) ℝ :=
  ![![1, 0],
    ![0, 1]]
  def matrix1_adjugate : Matrix (Fin 2) (Fin 2) ℝ := adjugate matrix1
  -- #eval matrix1_adjugate
  -- [ 4 -2
  --  -3  1 ]
  def matrix1_det := matrix1.det
  -- #eval matrix1_det
  -- (-2)
  -- #eval (matrix1_adjugate * matrix1)
  -- [ -2 0
  --   0  -2 ]
  -- #eval matrix1_det • matrixUnit
  -- [ -2 0
  --   0  -2 ]
  --  (matrix1_adjugate * matrix1) = matrix1_det • matrixUnit  为什么相等？？？这集的终极问题

  --  Finset.sum 的使用
 def my_set := (Finset.univ : (Finset (Fin 2)))
    -- #eval my_set -- {0, 1}
    --   Finset.sum需要两个参数：
      -- 1.一个有限集合，表示对该集合中的元素进行求和。
      -- 2.一个返回可相加的类型（即带有has_add类型类）的函数表达式，用于指定如何将集合中的元素相加。
    def sum_of_numbers : ℕ
      := Finset.sum (Finset.range 11) (fun x => x) -- 也就是x为0到10自然数，f(x)=x求和
    -- #eval sum_of_numbers -- 55
    def sum_of_numbers2 : ℕ
      := Finset.sum my_set (fun x => x) -- 也就是x为{0, 1}，f(x)=x求和
    -- #eval sum_of_numbers2 -- 1

  -- cramer 的使用 A*X=b
    def matrixb :  Fin 2 → ℝ :=
      ![5, 6]
    -- #eval matrixb
    def cramer001 := (cramer matrix1 matrixb)
    -- 可以看成一个n*1维的矩阵；也可以看成Fin 2 → ℝ，类似于数列；相当于 A.det • x ； 比如这里![8 -9]里，8就是matrix1第一列换成matrixb之后的矩阵，计算出来的行列式；9就是第2列替换matrixb后计算的行列式
    -- #eval cramer001
    def solution := (matrix1_det) • (cramer matrix1 matrixb)
    --  如何表示除法要有理数才行的
    #eval solution -- 解应该是x=![-4 4.5]

  -- Pi.single 的使用
  def matrixPiSingle : Matrix (Fin 3) (Fin 3) ℝ :=
    ![![1, 2, 3],
      ![4, 5, 6],
      ![7, 8, 9]]
  -- #eval matrixPiSingle 0 0
  -- #eval matrixPiSingle 0 1
  -- #eval matrixPiSingle 2 0
  def Single001 (i k j:Fin 3)
      :Fin 3 → ℝ
      := Pi.single j (matrixPiSingle (i-1) (k-1)) -- 这里j是标志判断位，
  -- #eval (Single001 3 1 2) 2 --最后一个输入2才是重点，如何和j相同，就输出预设好的(matrixPiSingle (i-1) (k-1))的值，否则输出0
  -- #eval (Single001 3 1 2) 0
  -- #eval (Single001 3 1 2) 1


  -- 证明正式开始：
  -- 四个领域 1.adjugate 2.cramer 3.det 4.Pi.single
  -- 1↔2,4
  -- 2↔3,4
  -- 1↔3

   -- 1↔2,4的桥梁
  lemma mul_adjugate_apply2 (A : Matrix n2 n2 α2) (i j k) :
    (A i k) * (adjugate A k j) = (cramer Aᵀ) (Pi.single k (A i k)) j
  := by
    have test: (cramer Aᵀ) (A i k • Pi.single k 1) j
    = (A i k • (cramer Aᵀ) (Pi.single k 1)) j
    := by
      simp only [SMulHomClass.map_smul]---我知道了，你要知道f代表什么，f代表(cramer Aᵀ) (参数一) j
    rw [
    ← smul_eq_mul,
    adjugate, -- 1↔2,4 伴随矩阵的定义来的。伴随矩阵即每一项先变余子式行列式，再加正负号(定义为-1的i+j次方)，再转置
    -- asfsadf,
    of_apply,
    ← Pi.smul_apply,
    ← test,
    ]
    rw [← Pi.single_smul',
    smul_eq_mul,
    mul_one]
    done

    -- 1↔3 的桥梁(由1↔2,4 和 2↔3,4 和 4↔null 得到)
  lemma mul_adjugate2
  (A : Matrix n2 n2 α2)
  : A * adjugate A = A.det • (1 : Matrix n2 n2 α2)
  := by
    -- have h1:= A * adjugate A -- : Matrix n n α
    -- have h2:= A.det • (1 : Matrix n2 n2 α2) -- : Matrix n2 n2 α2
    ext i k
    rw [
    mul_apply,  -- 作用：(M * N) i k = Finset.sum Finset.univ fun j ↦ M i j * N j k
    -- 将 (A * adjugate A) i k
    -- 其中 M=>A, N=>adjugate A
    -- 变成了等号右边 (Finset.sum Finset.univ fun j ↦ A i j * adjugate A j k)
    Pi.smul_apply, -- 作用：(b • x) i = b • (x i)
    -- 将 (det A • 1) i k
    -- 其中 b=>det A,x=>1,i=>i
    -- 变成了 ( det A • (1 i) ) k
    -- * 暂时理解成OfNat.ofNat 1 就是 1的单位矩阵(1 : Matrix n n α)
    Pi.smul_apply,
    -- 再作用一次 (b • x) i = b • (x i)
    -- 其中 b=>det A,x=>(1 i),i=>k
    -- 变成了det A • (1 i k)
    one_apply,
    smul_eq_mul,
    mul_boole]
    simp only [mul_adjugate_apply2] -- 1↔2,4的桥梁
    simp only [sum_cramer_apply]
    -- have :sorry:=sorry
    simp only [Finset.sum_pi_single] -- Pi.single就是一个按特定索引得到单值，其他索引得到0 ； 这里理解是：
    -- 首先对于Finset.sum Finset.univ fun x ↦ Pi.single x (A i x) j 我们知道x会进行遍历n2，其实只有x=j时有值，其余为0，所以j是否属于n2就决定了一切
    simp only [Finset.mem_univ]
    simp only [ite_true]
    -- simp only [ne_eq, Finset.sum_pi_single, Finset.mem_univ, ite_true]
    simp only [cramer_transpose_row_self] --好像是这么一回事，这就是行列式有两列相等，行列式就是0 -- 2↔3,4的桥梁 --单独cramer Aᵀ是再穿一个系数矩阵b，就得到由行列式组成的n*1维矩阵或看成数列
    simp only [Pi.single_apply] -- 4↔null的桥梁
    simp only [eq_comm]
    done

    -- 1↔3 的桥梁
  theorem MainGoal [Invertible A.det] : (A) * (⅟(det A) • adjugate A) = (1 : Matrix n2 n2 α2)
  := by
    rw [
    mul_smul_comm,
    mul_adjugate2,
    smul_smul,
    invOf_mul_self,
    one_smul]
    done


end Matrix

-- #minimize_imports
