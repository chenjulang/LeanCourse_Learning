-- import Mathlib.Data.Real.Sqrt
-- import Mathlib.Data.Fin.Tuple.BubbleSortInduction

-- open Tuple
-- variable  (f2 : Fin 5 → ℕ)

-- -- 假设我们有一个包含5个整数的列表
-- def lst : List ℕ := [3, 5, 2, 1, 4]

-- -- 定义排序性质P，即列表中相邻的两个元素满足前面的元素小于等于后面的元素
-- def prop_P (f : Fin 5 → ℕ) : Prop :=
--   ∀ i : Fin 4, f i ≤ f (i + 1)



-- -- 定义反例函数，用来检查序列是否满足性质P
-- def is_counterexample (P : Prop)  [Decidable P] : Bool := by
--   have h1:= decide P
--   exact h1


-- #check is_counterexample (prop_P f2)

--   -- exact (to_bool h1)


-- -- -- 定义交换函数，用来交换序列中的两个元素
-- -- def swap_elements {α : Type} [Inhabited α] (i j : Fin 5) (lst : Array α) : Array α :=
-- --   let temp := lst.read i;
-- --   lst.write i (lst.read j);
-- --   lst.write j temp

-- -- -- 定义冒泡排序算法
-- -- def bubble_sort (lst : List ℕ) : List ℕ :=
-- --   let n := lst.length;
-- --   let mut arr := lst.toArray;
-- --   for i in [0:n] do
-- --     for j in [0:n - i - 1] do
-- --       if arr.read ⟨j⟩ > arr.read ⟨j + 1⟩ then
-- --         arr := swap_elements ⟨j, _⟩ ⟨j + 1, _⟩ arr;
-- --   arr.toList

-- -- -- 使用bubble_sort_induction'定理证明冒泡排序算法的正确性
-- -- theorem bubble_sort_correctness :
-- --   ∀ f : Fin 5 → ℕ, prop_P f → prop_P (f ∘ bubble_sort) :=
-- -- begin
-- --   intros f h,
-- --   apply bubble_sort_induction' _ h,
-- --   intros σ i j hij hij₂ hfσ,
-- --   -- 在这里证明通过对f进行σ置换后的序列仍然满足性质P
-- --   sorry
-- -- end
