import Mathlib.LinearAlgebra.Matrix.Transvection
-- 高斯：任意矩阵可化成对角形式 -- 线性方程组的人肉解



--TransvectionStruct：是行变换的结构，保存了关键信息
-- L.map：是 L.map f 即应用f到列表的每个元素，结果也是一个List。
-- toMatrix : 就是某个基本行变换TransvectionStruct操作单位矩阵后得到的矩阵。
-- List.prod：是列表中的元素从左到右全部乘起来
-- Sum n p：是不相交并集类型，用来拼一个新的更大的矩阵用的。比如：
  -- n*n扩充成m*m的矩阵，需要补充三个块
  -- inl是上一行的特殊化：左并
-- diagonal：是对角矩阵

universe u₁ u₂

namespace Matrix

open Matrix

variable (n p : Type*) (R : Type u₂) {𝕜 : Type*} [Field 𝕜]

variable [DecidableEq n] [DecidableEq p]

variable [CommRing R]

section Transvection

variable {R n} (i j : n)

/-- stdBasisMatrix i j a是 : 第i行，j列为a，其他地方为0的一个矩阵。 -/
def transvection2 (c : R) : Matrix n n R :=
  1 + Matrix.stdBasisMatrix i j c

section

variable [Fintype n]

end

variable (R n)

/-- 实际上代表的是行变换，有一个矩阵，操作是：将第i行的c倍加到第j行上。 -/
structure TransvectionStruct2 where
  (i j : n)
  hij : i ≠ j
  c : R

namespace TransvectionStruct

variable {R n}

/--将单位矩阵通过行变换t后得到的一个矩阵 -/
def toMatrix2 (t : TransvectionStruct n R) : Matrix n n R :=
  transvection t.i t.j t.c

section

variable [Fintype n]

end

open Sum


variable {p}

variable [Fintype n] [Fintype p]

end TransvectionStruct

end Transvection


namespace Pivot

variable {R} {r : ℕ} (M : Matrix (Sum (Fin r) Unit) (Sum (Fin r) Unit) 𝕜)

open Sum Unit Fin TransvectionStruct

variable {n p} [Fintype n] [Fintype p]

-- 改成追查3层定理算了，时间不充裕。

/-第3层引理 -------------------/
-- 可能真正能理解的精髓都在这里，一个递推有关的定理
-- Sum (Fin r) Unit是什么意思？是加一个位置的意思吗？
theorem exists_list_transvec_mul_mul_list_transvec_eq_diagonal_induction2 --???
(IH :
  ∀ M : Matrix (Fin r) (Fin r) 𝕜,
    ∃ (L₀ L₀' : List (TransvectionStruct (Fin r) 𝕜))
    (D₀ : Fin r → 𝕜),
      (L₀.map toMatrix).prod * M * (L₀'.map toMatrix).prod
      = diagonal D₀
)
(M : Matrix (Sum (Fin r) Unit) (Sum (Fin r) Unit) 𝕜)
:
∃ (L L' : List (TransvectionStruct (Sum (Fin r) Unit) 𝕜))
(D : Sum (Fin r) Unit → 𝕜),
  (L.map toMatrix).prod * M * (L'.map toMatrix).prod
  = diagonal D
  := by
  rcases exists_isTwoBlockDiagonal_list_transvec_mul_mul_list_transvec M with ⟨L₁, L₁', hM⟩ --???弱化的定理，先能变成块对角矩阵
  let M' := (L₁.map toMatrix).prod * M * (L₁'.map toMatrix).prod -- (r+1)*(r+1)
  let M'' := toBlocks₁₁ M' -- 提取对应的 “左上角”子矩阵 r*r
  rcases IH M'' with ⟨L₀, L₀', D₀, h₀⟩ -- IH和M''得到的结论拿到
  set c := M' (inr unit) (inr unit) -- 1*1的矩阵，用0扩充，扩充成(r+1)*(r+1)矩阵
  refine' -- 填充Goal的存在假设
    ⟨L₀.map (sumInl Unit) ++ L₁,
     L₁' ++ L₀'.map (sumInl Unit),
    Sum.elim D₀ fun _ => M' (inr unit) (inr unit),
      _⟩
  suffices (L₀.map (toMatrix ∘ sumInl Unit)).prod
  * M'
  * (L₀'.map (toMatrix ∘ sumInl Unit)).prod =
      diagonal (Sum.elim D₀ fun _ => c) by
    simpa [Matrix.mul_assoc]
  have : M' = fromBlocks M'' 0 0 (diagonal fun _ => c) := by
    -- porting note: simplified proof, because `congr` didn't work anymore
    rw [← fromBlocks_toBlocks M', hM.1, hM.2]
    rfl
  rw [this]
  simp [h₀]
  done


/-- 第2层引理 -------------------/
theorem reindex_exists_list_transvec_mul_mul_list_transvec_eq_diagonal2
(M : Matrix p p 𝕜)
(e : p ≃ n)
(H :
  ∃ (L L' : List (TransvectionStruct n 𝕜))
  (D : n → 𝕜),
    (L.map toMatrix).prod * Matrix.reindexAlgEquiv 𝕜 e M * (L'.map toMatrix).prod
-- Matrix.reindexAlgEquiv 重新建立索引,我理解是从1-n索引改成0-（n-1）这样子来取矩阵的值
-- ，实际上矩阵本体没有变，类型变了，不影响理解：
-- Matrix p p 𝕜 变成了：
-- Matrix (Fin (Fintype.card n)) (Fin (Fintype.card n)) R
    = diagonal D
)
:
∃ (L L' : List (TransvectionStruct p 𝕜))
(D : p → 𝕜),
  (L.map toMatrix).prod * M * (L'.map toMatrix).prod
  = diagonal D
  := by
  rcases H with ⟨L₀, L₀', D₀, h₀⟩ -- 获取已知假设
  refine' ⟨L₀.map (reindexEquiv e.symm), L₀'.map (reindexEquiv e.symm), D₀ ∘ e, _⟩ -- 填充Goal里面的存在假设
  -- 在我看来reindexEquiv e.symm没有变本体
  have : M = reindexAlgEquiv 𝕜 e.symm (reindexAlgEquiv 𝕜 e M) := by --  两次重新建索引而已，变回自己
    simp only [Equiv.symm_symm, submatrix_submatrix, reindex_apply, submatrix_id_id,
      Equiv.symm_comp_self, reindexAlgEquiv_apply]-- 但可能蕴藏别的意义，所以打个???
  rw [this]
  simp only [toMatrix_reindexEquiv_prod, List.map_map, reindexAlgEquiv_apply]-- 但可能蕴藏别的意义，所以打个??
  simp only [← reindexAlgEquiv_apply, ← reindexAlgEquiv_mul, h₀]-- 但可能蕴藏别的意义，所以打个??
  simp only [Equiv.symm_symm, reindex_apply, submatrix_diagonal_equiv, reindexAlgEquiv_apply]-- 但可能蕴藏别的意义，所以打个??
  done


/-- 第2层引理 -------------------/
theorem exists_list_transvec_mul_mul_list_transvec_eq_diagonal_aux2
(n : Type)
[Fintype n]
[DecidableEq n]
(M : Matrix n n 𝕜)
:
∃ (L L' : List (TransvectionStruct n 𝕜))
(D : n → 𝕜),
  (L.map toMatrix).prod * M * (L'.map toMatrix).prod
  = diagonal D
  := by
  -- 下面这里对n的数量进行归纳，0-（n-1）
  -- 还有n数量为n₁时（记为r），成立假设即IH
  -- 要推r+1的情况也成立。
  induction' hn : Fintype.card n with r IH generalizing n M
  · refine' ⟨List.nil, List.nil, fun _ => 1, _⟩ --填充Goal里的存在假设
    ext i j
    rw [Fintype.card_eq_zero_iff] at hn
    exact hn.elim' i -- 这里用到了矛盾推一切
    -- 已知p真，任意命题q，p∨q
    -- 1.则：p∨q是真的。
    -- 2. ∨的两边至少一个真的，命题才是真的
    -- 3. 给到¬p, 则分析p∨q已知是真的，由2知p和q至少一个真的，但是¬p说的是p不是真的，所以只能是q是真的
    -- 由此推出q是真的。
    -- 但注意这是一个不一致的系统，有不满足“排中律”的两个命题存在，比如p和¬p
  · have e : n ≃ Sum (Fin r) Unit := by -- n = r+1 所以，1-n 一一对应 0-（n-1）也就是0-r
      refine' Fintype.equivOfCardEq _
      rw [hn]
      rw [@Fintype.card_sum (Fin r) Unit _ _]
      simp
    apply reindex_exists_list_transvec_mul_mul_list_transvec_eq_diagonal2 M e
    apply exists_list_transvec_mul_mul_list_transvec_eq_diagonal_induction2
    intro N
    apply IH
    simp only [Fintype.card_fin]
    done
    -- exact IH (Fin r) N (by simp)
    -- apply exists_list_transvec_mul_mul_list_transvec_eq_diagonal_induction2 fun N => --???
    --     IH (Fin r) N (by simp)
  done

/-- 第1层引理 -------------------/
theorem exists_list_transvec_mul_mul_list_transvec_eq_diagonal2
(M : Matrix n n 𝕜) :
∃ (L L' : List (TransvectionStruct n 𝕜))
(D : n → 𝕜),
  (L.map toMatrix).prod * M * (L'.map toMatrix).prod
  = diagonal D
  := by
  have e : n ≃ Fin (Fintype.card n) --感性认识，1-n 和 0-(n-1) 是可以一一对应的，就是因为数量一样其实
  -- Fintype.card：有限集合的元素数量
  -- Fin n 就是 0到（n-1）这个集合
    := by
    refine' Fintype.equivOfCardEq _
    simp
  apply reindex_exists_list_transvec_mul_mul_list_transvec_eq_diagonal2 M e --反推
  apply exists_list_transvec_mul_mul_list_transvec_eq_diagonal_aux2--反推
  -- 看出来(reindexAlgEquiv 𝕜 e) M的结果也是一个Matrix n n k 的矩阵
  done

/-- 第1层引理 -------------------/
lemma changeTarget1
(M : Matrix n n 𝕜)
(L L' : List (TransvectionStruct n 𝕜))
(D : n → 𝕜)
(h: List.prod (List.map toMatrix L) * M * List.prod (List.map toMatrix L') = diagonal D) -- 这个条件看起来有点苛刻
: -- 这个引理感觉就是将行变换全都变成了逆变换
-- 举个例子：L=[A1,A2,A3] L'=[A4,A5,A6]
-- 前提条件:M(A1)*M(A2)*M(A3) * M * M(A4)*M(A5)*M(A6) = M_d(D)

-- 等式左边 = M(A3⁻¹)*M(A2⁻¹)*M(A1⁻¹)
-- * M_d(D)
-- M(A6⁻¹)*M(A5⁻¹)*M(A4⁻¹)
-- 等式右边 =  M(A3⁻¹)*M(A2⁻¹)*M(A1⁻¹)
-- * M(A1)*M(A2)*M(A3)
-- * M
-- * M(A4)*M(A5)*M(A6)
-- * M(A6⁻¹)*M(A5⁻¹)*M(A4⁻¹)

-- 这很明显的，将h代入就得到了。
  List.prod (
    List.map (toMatrix ∘ TransvectionStruct.inv) (List.reverse L)
  )
  *
  diagonal D
  *
  List.prod (
    List.map (toMatrix ∘ TransvectionStruct.inv) (List.reverse L')
  )
  =
  (L.reverse.map (toMatrix ∘ TransvectionStruct.inv)).prod
  *
  (L.map toMatrix).prod
  *
  M
  *
  (
    (L'.map toMatrix).prod
    *
    (L'.reverse.map (toMatrix ∘ TransvectionStruct.inv)).prod
  )
  := by
    simp only [← h]
    simp only [Matrix.mul_assoc]
    done

/-- 任何矩阵可以写成：三个矩阵的乘积，第一个矩阵的作用效果是一系列的行变换左乘，第二个是一个对角矩阵，第三个是一系列的行变换右乘-/
theorem MainGoal8
(M : Matrix n n 𝕜)
:
∃ (L L' : List (TransvectionStruct n 𝕜)) -- n 𝕜只是一个取值范围
(D : n → 𝕜),
  M =
  (L.map toMatrix).prod *
  diagonal D --左上->右下的对角线才有非零的数的方阵
  * (L'.map toMatrix).prod
  := by
  have h1 := exists_list_transvec_mul_mul_list_transvec_eq_diagonal2 M
  -- 和Goal的相似之处在于该有的项都有了
  obtain ⟨L, L', D, h⟩ := h1
  refine' ⟨L.reverse.map TransvectionStruct.inv, L'.reverse.map TransvectionStruct.inv, D, _⟩
  -- 这里是在填充Goal里面的那几个存在的假设
  -- TransvectionStruct.inv就是将第i行的-c倍加到第j行， 之所以说是逆操作，是因为操作完TransvectionStruct以后再操作TransvectionStruct.inv结果就变回单位矩阵了。
  simp only [List.map_map] --//先后作用2个函数=一次作用2个函数的复合函数。定义而已。
  have changeTarget := changeTarget1 M L L' D h --三项乘积的一个变式
  rw [changeTarget]
  rw [
  reverse_inv_prod_mul_prod,
  -- 描述：(L.reverse.map (toMatrix ∘ TransvectionStruct.inv)).prod * (L.map toMatrix).prod = 1
  -- (L.reverse.map  -- 比如某组操作L=[A1,A2,A3],L.reverse=[A3,A2,A1],
  -- L.reverse.map (toMatrix ∘ TransvectionStruct.inv) 即每一项经过两个函数变换，
    -- 分别是1.取inv，即得到负倍数的行变换，起止行不变。2.将该行变换变成矩阵。
    -- 因此结果是[A3⁻¹,A2⁻¹,A1⁻¹] =>  [M(A3⁻¹),M(A2⁻¹),M(A1⁻¹)]
  --    (toMatrix ∘ TransvectionStruct.inv)
  -- ).prod
  -- 最后.prod是乘起来，即M(A3⁻¹)*M(A2⁻¹)*M(A1⁻¹)
  -- *
  -- (L.map toMatrix).prod
  -- 这里(L.map toMatrix) 即[M(A1),M(A2),M(A3)]
  -- .prod 后就是 M(A1)*M(A2)*M(A3)
  -- 为什么等于1呢，感性认识全部写出来：M(A3⁻¹)*M(A2⁻¹)*M(A1⁻¹) * M(A1)*M(A2)*M(A3)
  -- 很明显中间可用结合律一一合并成1
  -- = 1
  prod_mul_reverse_inv_prod,
  --  (L.map toMatrix).prod * (L.reverse.map (toMatrix ∘ TransvectionStruct.inv)).prod = 1
  -- 这里用上面的例子就是 M(A1)*M(A2)*M(A3) * M(A3⁻¹)*M(A2⁻¹)*M(A1⁻¹)
  -- 一样的用结合律，从中间往两边击破
  Matrix.one_mul,
  Matrix.mul_one
  ]
  done


end Pivot
