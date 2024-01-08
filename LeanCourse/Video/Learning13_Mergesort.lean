import Mathlib.Data.List.Perm
import Mathlib.Tactic.Linarith

set_option pp.structureInstances false
attribute [pp_dot] Nat.succ List.length List.get List.takeWhile List.dropWhile

variable {α : Type}


-- ## Mergesort implementation

section decidrelle
variable [LE α] [@DecidableRel α (· ≤ ·)]

-- ### Merging and splitting

def merge : List α → List α → List α -- 使用前提通常是x和y列表都已经排列好了
| [ ]   , y      => y
| x     , [ ]    => x
| a :: x, b :: y => if a ≤ b
                    then a :: merge x (b :: y)
                    else b :: merge (a :: x) y
termination_by
  merge x y => x.length + y.length -- 应该是结果长度等于什么（两个列表长度之和）的时候就递归停止。
-- 它接受两个List类型的参数x和y，并返回一个List类型的结果。
-- 函数的作用是将两个有序列表合并成一个有序列表。具体而言，函数的逻辑如下：
-- 如果列表x为空，则返回列表y。
-- 如果列表y为空，则返回列表x。
-- 如果列表x和y都非空，则比较它们的头部元素a和b。
-- 如果a小于等于b，则将a添加到结果列表中，并递归调用merge函数处理剩余的列表x和b :: y。
-- 如果a大于b，则将b添加到结果列表中，并递归调用merge函数处理剩余的列表a :: x和y。

-- result = merge x y
-- 首先，我们比较两个列表的头部元素，即 1 和 2。由于 1 小于 2，所以我们将 1 加入结果列表中，并继续递归地调用 merge 函数来合并剩余的元素：
-- result = [1] + merge [3, 5, 7] [2, 4, 6, 8, 9]
-- 接下来，我们比较 3 和 2。由于 2 小于 3，所以我们将 2 加入结果列表中，并继续递归地调用 merge 函数：
-- result = [1, 2] + merge [3, 5, 7] [4, 6, 8, 9]
-- 继续比较剩余的元素，直到一个或两个列表为空。最终，我们得到合并后的列表：
-- result = [1, 2, 3, 4, 5, 6, 7, 8, 9]



/-- Creates a list made of every odd element of given list, starting with its head.  -/
def eo : List α → List α
| [ ]         => [ ]
| [ a ]       => [ a ]
| a :: _ :: s => a :: eo s -- 这里_占位指的是列表的第二个元素

-- 如果输入列表为空（[ ]），则直接返回一个空列表（[ ]）。
-- 如果输入列表只包含一个元素（[ a ]），则直接返回包含该元素的列表（[ a ]）。
-- 如果输入列表包含至少两个元素，那么从列表的头部取出第一个元素（a），并忽略第二个元素和之后的所有元素，然后递归地调用 eo 函数，只处理剩余的元素（s）。
-- 这种情况下，我们可以理解为每次只保留列表中的奇数位置的元素，也就是从第一个元素开始，每隔一个元素取一个。
-- #eval eo {1,2,3,4,5} --[1, 3, 5]

-- ### We need some lemmas for well-founded induction

lemma length_eo_cons (a : α) (s : List α) :
  (eo s).length ≤ (eo (a :: s)).length
  ∧
  (eo (a :: s)).length ≤ (eo s).length.succ
:= by --todo
  induction s with
  | nil => simp [eo]
  | cons d l ih =>
    cases l with
    | nil => simp [eo, ih]
    | cons d' l' =>
      simp [eo] at ih ⊢
      constructor
      · exact ih.right
      · apply Nat.succ_le_succ
        exact ih.left

lemma length_eo2_lt (a b : α) (s : List α) :
  (eo (a :: b :: s)).length < s.length.succ.succ :=
by
  induction s with
  | nil => simp [eo]
  | cons d l ih =>
    cases l with
    | nil => simp [eo, ih]
    | cons d' l' =>
      simp [eo] at ih ⊢
      have not_longer := (length_eo_cons d' l').left
      linarith

lemma length_eo1_lt (a : α) (s : List α) :
  (eo (a :: s)).length < s.length.succ.succ :=
by
  cases s with
  | nil => simp [eo]
  | cons d l =>
    apply (length_eo2_lt a d l).trans_le
    apply Nat.succ_le_succ
    apply Nat.succ_le_succ
    exact Nat.le_succ l.length

-- ### The algorithm

def mergesort : List α → List α
| [ ]         => [ ]
| [ a ]       => [ a ]
| a :: b :: s => merge (mergesort (eo (a :: b :: s))) (mergesort (eo (b :: s)))
-- the compiler needs the following hints
termination_by mergesort l => l.length
decreasing_by
  simp_wf
  simp [length_eo1_lt, length_eo2_lt]

-- ### A unit test (just for fun) and a definition of the property "is sorted" (crucial later on)

#eval mergesort [3, 5, 7, 1, 9, 5, 0, 2, 4, 6, 8]  -- 0..9 with 5 twice

def Sorted : List α → Prop
| [ ]         => True
| [ _ ]       => True
| a :: b :: s => a ≤ b ∧ Sorted (b :: s)

end decidrelle


/-
## Mergesort verification

You'll find the desired theorem at the very end.
First I proved some lemmas I needed...
-/

lemma suc_sub_sub_ltl (m n : ℕ) : m.succ - n.succ < m.succ :=
by
  rw [Nat.succ_sub_succ_eq_sub]
  exact Nat.sub_lt_succ m n

lemma sub_alter_of_lt {m n : ℕ} (hnm : n < m) : m - n = (m - n.succ).succ :=
by
  cases m with
  | zero => simp at hnm
  | succ k =>
    rw [Nat.succ_sub_succ_eq_sub]
    apply Nat.succ_sub
    exact Nat.lt_succ.mp hnm


section lelo
variable [LinearOrder α] [@DecidableRel α (· ≤ ·)]

lemma sorted_of_sorted_cons {a : α} {s : List α} (has : Sorted (a :: s)) :
  Sorted s :=
by
  cases s with
  | nil => trivial
  | cons => exact has.right

lemma sorted_of_sorted_append {x y : List α} (hxy : Sorted (x ++ y)) :
  Sorted x :=
by
  induction x with
  | nil => trivial
  | cons d l ih =>
    cases l with
    | nil => trivial
    | cons a s =>
      unfold Sorted at hxy
      constructor
      · exact hxy.left
      · apply ih
        exact hxy.right

lemma consecutive_le_of_sorted {l : List α} (hl : Sorted l)
    {n : ℕ} (hnl : n < l.length) (hnsl : n.succ < l.length) :
  l.get ⟨n, hnl⟩ ≤ l.get ⟨n.succ, hnsl⟩ :=
by
  revert n
  induction l with
  | nil =>
    intro n impos
    exfalso
    simp at impos
  | cons a l' ih =>
    cases l' with
    | nil =>
      intro n _ imposs
      exfalso
      simp at imposs
    | cons b s =>
      intro n hnl hnsl
      unfold Sorted at hl
      cases n with
      | zero => convert hl.left
      | succ m =>
        simp only [List.get_cons_succ]
        apply ih hl.right
        simp only [List.length_cons] at hnsl ⊢
        exact Nat.lt_of_succ_lt_succ hnsl

lemma dropWhile_head_false {l : List α} {P : α → Bool} (hlP : l.dropWhile P ≠ []) :
  P ((l.dropWhile P).head hlP) = false :=
by
  induction l with
  | nil => simp at hlP
  | cons a => by_cases P a <;> simp_all [List.dropWhile]

lemma weaken_sorted_merge {x s : List α} {a b : α} (hab : a ≤ b)
    (hx : Sorted x) (hxabs : Sorted (merge x (a :: b :: s))) :
  Sorted (merge x (b :: s)) :=
by
  let x₀ := x.takeWhile (· ≤ a)
  let xₐ := x.dropWhile (· ≤ a)
  have parts : x₀ ++ xₐ = x
  · apply List.takeWhile_append_dropWhile
  have main_observation : merge x (a :: b :: s) = x₀ ++ a :: merge xₐ (b :: s)
  · rw [← parts]
    have almost_observation : merge (x₀ ++ xₐ) (a :: b :: s) = x₀ ++ merge xₐ (a :: b :: s)
    · have key_induction : ∀ n : ℕ, n ≤ x₀.length →
          merge (x₀ ++ xₐ) (a :: b :: s) = x₀.take n ++ merge (x₀.drop n ++ xₐ) (a :: b :: s)
      · intro n hn
        induction n with
        | zero =>
          rw [List.take_zero, List.nil_append, List.drop_zero]
        | succ n ih =>
          specialize ih (Nat.le_of_lt hn)
          rw [List.drop_eq_get_cons hn] at ih
          rw [ih]
          rw [List.take_succ, List.append_assoc]
          have x₀head_le_a : x₀.get ⟨n, hn⟩ ≤ a
          · have head_in : x₀.get ⟨n, hn⟩ ∈ x.takeWhile (· ≤ a)
            · apply List.get_mem
            have goal_is_true : (decide (x₀.get ⟨n, hn⟩ ≤ a)) = true
            · apply List.mem_takeWhile_imp head_in
            rw [decide_eq_true_eq] at goal_is_true
            exact goal_is_true
          have merge_res :
            merge (x₀.get ⟨n, hn⟩ :: x₀.drop n.succ ++ xₐ) (a :: b :: s) =
            x₀.get ⟨n, hn⟩ :: merge (x₀.drop n.succ ++ xₐ) (a :: b :: s)
          · simp [merge, x₀head_le_a]
          have obvious : x₀.get? n = Option.some (x₀.get ⟨n, hn⟩)
          · exact List.get?_eq_get hn
          -- apply List.get!_eq_get
          rw [merge_res, obvious, Option.to_list_some, List.singleton_append]
      convert key_induction x₀.length (by rfl)
      · rw [List.take_length]
      · rw [List.drop_length, List.nil_append]
    rw [almost_observation]
    congr
    cases hxa : xₐ with
    | nil => rfl
    | cons d l =>
      have hda : ¬ (d ≤ a)
      · have goal_as_bool : decide (d ≤ a) = false
        · have hdin : d ∈ x.dropWhile (· ≤ a)
          · simp [hxa]
          have nonempty : (x.dropWhile (· ≤ a)) ≠ []
          · exact List.ne_nil_of_mem hdin
          convert dropWhile_head_false nonempty
          simp_all
        rw [decide_eq_false_iff_not] at goal_as_bool
        exact goal_as_bool
      simp [merge, hda]
  have next_observation : merge (x₀ ++ xₐ) (b :: s) = x₀ ++ merge xₐ (b :: s)
  · have damn_covid : ∀ n : ℕ, n ≤ x₀.length →
        x₀.take (x₀.length - n) ++ merge (x₀.drop (x₀.length - n) ++ xₐ) (b :: s) =
        x₀ ++ merge xₐ (b :: s)
    · intro n hn
      induction n with
      | zero =>
        rw [Nat.sub_zero, List.take_length, List.drop_length, List.nil_append]
      | succ n ih =>
        rw [← ih (Nat.le_of_lt hn)]
        clear ih
        have index_lt : x₀.length - n.succ < x₀.length
        · cases len_x₀ : x₀.length with
          | zero => simp [len_x₀] at hn
          | succ k => apply suc_sub_sub_ltl
        have len_sub_alter : x₀.length - n = (x₀.length - n.succ).succ
        · exact sub_alter_of_lt hn
        have take_mid :
          x₀.take (x₀.length - n) =
          x₀.take (x₀.length - n.succ) ++ [x₀.get ⟨x₀.length - n.succ, index_lt⟩]
        · rw [len_sub_alter, List.take_succ]
          congr
          have get_got : x₀.get? (x₀.length - n.succ) = x₀.get ⟨x₀.length - n.succ, index_lt⟩
          · exact List.get?_eq_get index_lt
          -- apply List.get!_eq_get
          rw [get_got, Option.to_list_some]
        have drop_mid :
          x₀.drop (x₀.length - n.succ) =
          x₀.get ⟨x₀.length - n.succ, index_lt⟩ :: x₀.drop (x₀.length - n)
        · rw [len_sub_alter, List.drop_eq_get_cons index_lt]
        have mid_le_b : x₀.get ⟨x₀.length - n.succ, index_lt⟩ ≤ b
        · have mid_le_a : x₀.get ⟨x₀.length - n.succ, index_lt⟩ ≤ a
          · have mid_in_x₀ : x₀.get ⟨x₀.length - n.succ, index_lt⟩ ∈ x₀
            · apply List.get_mem
            have decide_le_a := List.mem_takeWhile_imp mid_in_x₀
            rwa [decide_eq_true_eq] at decide_le_a
          exact mid_le_a.trans hab
        rw [take_mid, drop_mid]
        simp [merge, mid_le_b]
    specialize damn_covid x₀.length (by rfl)
    rw [Nat.sub_self, List.take_zero, List.nil_append, List.drop_zero] at damn_covid
    exact damn_covid
  rw [← parts]
  rw [main_observation] at hxabs
  rw [next_observation]
  have second_part_sorted : Sorted (merge xₐ (b :: s))
  · have help_indu : ∀ n : ℕ, n ≤ x₀.length → Sorted (x₀.drop n ++ a :: merge xₐ (b :: s))
    · intro n hn
      induction n with
      | zero => convert hxabs
      | succ n ih =>
        specialize ih (Nat.le_of_lt hn)
        rw [List.drop_eq_get_cons hn] at ih
        rw [List.cons_append] at ih
        exact sorted_of_sorted_cons ih
    have dropped := help_indu x₀.length (by rfl)
    rw [List.drop_length, List.nil_append] at dropped
    cases hxbs : merge xₐ (b :: s) with
    | nil => trivial
    | cons d l =>
      rw [hxbs] at dropped
      exact dropped.right
  have main_indu : ∀ n : ℕ, n ≤ x₀.length → Sorted (x₀.drop (x₀.length - n) ++ merge xₐ (b :: s))
  · intro n hn
    induction n with
    | zero =>
      rw [Nat.sub_zero, List.drop_length, List.nil_append]
      exact second_part_sorted
    | succ n ih =>
      specialize ih (Nat.le_of_lt hn)
      have index_lt : x₀.length - n.succ < x₀.length
      · cases len_x₀ : x₀.length with
        | zero => simp [len_x₀] at hn
        | succ k => apply suc_sub_sub_ltl
      rw [sub_alter_of_lt hn] at ih
      rw [List.drop_eq_get_cons index_lt]
      rw [List.cons_append]
      cases rest : x₀.drop (x₀.length - n.succ).succ ++ merge xₐ (b :: s) with
      | nil => trivial
      | cons d l =>
        rw [rest] at ih
        constructor
        · cases dropping : x₀.drop (x₀.length - n.succ).succ with
        | nil =>
          rw [dropping, List.nil_append] at rest
          have hle_a : x₀.get ⟨x₀.length - n.succ, index_lt⟩ ≤ a
          · have hin_x₀ : x₀.get ⟨x₀.length - n.succ, index_lt⟩ ∈ x₀
            · apply List.get_mem
            have goal_eq_true := List.mem_takeWhile_imp hin_x₀
            rwa [decide_eq_true_eq] at goal_eq_true
          apply hle_a.trans
          cases hxa : xₐ with
          | nil =>
            rw [hxa] at rest
            unfold merge at rest
            rw [List.cons.injEq] at rest
            rw [← rest.left]
            exact hab
          | cons d' L' =>
            by_cases hbd' : d' ≤ b <;> simp [merge, hxa, hbd'] at rest
            · have nonempty : xₐ ≠ []
              · by_contra impos
                simp [impos] at hxa
              have big_head := dropWhile_head_false nonempty
              simp [hxa] at big_head
              rw [rest.left] at big_head
              exact le_of_lt big_head
            · rwa [rest.left] at hab
        | cons c z =>
          rw [dropping, List.cons_append] at rest
          convert_to x₀.get ⟨x₀.length - n.succ, index_lt⟩ ≤ c
          · rw [List.cons.injEq] at rest
            exact rest.left.symm
          have index_succ_lt : (x₀.length - n.succ).succ < x₀.length
          · by_contra contr
            rw [not_lt, ← List.drop_eq_nil_iff_le] at contr
            simp [contr] at dropping
          convert_to x₀.get ⟨x₀.length - n.succ, index_lt⟩ ≤ x₀.get ⟨(x₀.length - n.succ).succ, index_succ_lt⟩
          · rw [List.drop_eq_get_cons index_succ_lt, List.cons.injEq] at dropping
            exact dropping.left.symm
          rw [← parts] at hx
          apply consecutive_le_of_sorted
          exact sorted_of_sorted_append hx
        · exact ih
  specialize main_indu x₀.length (by rfl)
  rw [Nat.sub_self, List.drop_zero] at main_indu
  exact main_indu

lemma merge_preserves_sorted {x y : List α} (hx : Sorted x) (hy : Sorted y) :
  Sorted (merge x y) :=
by
  induction x with
  | nil =>
    simp [merge]
    exact hy
  | cons d l ih =>
    induction y with
    | nil =>
      simp [merge]
      exact hx
    | cons d' l' ih' =>
      simp [merge]
      by_cases cmp_heads : d ≤ d'
      · simp [cmp_heads]
        cases l with
        | nil => simp_all [Sorted, merge]
        | cons a z =>
          simp [merge]
          simp [Sorted] at hx
          by_cases cmp_next : a ≤ d'
          · simp [cmp_next]
            constructor
            · exact hx.left
            · simp [cmp_next, merge] at ih
              apply ih
              exact hx.right
          · simp [cmp_next]
            constructor
            · exact cmp_heads
            · simp [cmp_next, merge] at ih
              apply ih
              exact hx.right
      · simp [cmp_heads]
        have hdd : d' ≤ d
        · exact le_of_not_le cmp_heads
        cases l' with
        | nil =>
          simp [Sorted, merge]
          constructor
          · exact hdd
          · exact hx
        | cons a z =>
          simp [merge]
          simp [Sorted] at hy
          specialize ih' hy.right
          by_cases cmp_here : d ≤ a
          · simp [cmp_here]
            constructor
            · exact hdd
            · simp [merge, cmp_here] at ih'
              apply ih'
              intro sure
              apply weaken_sorted_merge hy.left
              · exact sure
              · exact ih sure
          · simp [cmp_here]
            constructor
            · exact hy.left
            · simp [merge, cmp_here] at ih'
              apply ih'
              intro sure
              apply weaken_sorted_merge hy.left
              · exact sure
              · exact ih sure

lemma mergesort_sorts {n : ℕ} {x : List α} (hnxl : x.length ≤ n) :
  Sorted (mergesort x) :=
by
  revert x
  induction n with
  | zero =>
    intro x hyp
    have x_nil : x = []
    · rwa [Nat.le_zero, List.length_eq_zero] at hyp
    simp [x_nil, Sorted]
  | succ m ih =>
    intro x hyp
    match x with
    | [ ] => simp [Sorted]
    | [ _ ] => simp [Sorted]
    | a :: b :: s =>
      unfold mergesort
      simp only [List.length_cons] at hyp
      apply merge_preserves_sorted
      · apply ih
        have leneo := length_eo2_lt a b s
        linarith
      · apply ih
        have leneo := length_eo1_lt b s
        linarith


/-
At this point, we are done with the "is sorted" part.
Now for the "is a permutation of the input" part...

Mathlib defines list permutations as follows.
If `s` and `t` are lists of the same type, then `s ~ t` denotes that `s` is a permutation of `t`
where `~` is a binary relation defined by the following four rules.
• empty list is a permutation of empty list: `[] ~ []`
• if `a` is an element and `x` and `y` are lists such that `x ~ y` then we have: `a :: x ~ a :: y`
• if `a` and `b` are elements and `x` is a list then we have: `b :: a :: x ~ a :: b :: x`
• if `x`, `y`, `z` are lists such that `x ~ y` and `y ~ z` then we have: `x ~ z`
-/

lemma merge_permutes (x y : List α) :
  merge x y ~ x ++ y :=
by
  revert y
  induction x with
  | nil => simp [merge]
  | cons d l ih =>
    intro y
    induction y with
    | nil => simp [merge]
    | cons a z ih' =>
      by_cases cmp_da : d ≤ a
      · simp [cmp_da, merge]
        exact ih (a :: z)
      · simp [cmp_da, merge]
        apply (List.Perm.cons a ih').trans
        rw [List.cons_append]
        apply (List.Perm.swap d a (l ++ z)).trans
        rw [List.perm_cons]
        apply List.Perm.symm
        apply List.perm_middle

lemma split_permutes (a b : α) (s : List α) :
  eo (a :: b :: s) ++ eo (b :: s) ~ a :: b :: s :=
by
  induction s with
  | nil => rfl
  | cons d l ih =>
    simp [eo] at ih ⊢
    cases l with
    | nil => apply List.Perm.swap
    | cons c z =>
      simp [eo] at ih ⊢
      set x := eo (c :: z)
      set y := eo z
      have almost : (y ++ b :: x) ~ b :: c :: z
      · have almost_almost : (y ++ x) ~ c :: z
        · have swap_xy : y ++ x ~ x ++ y
          · apply List.perm_append_comm
          apply swap_xy.trans
          rw [← List.perm_cons b]
          apply List.Perm.trans _ ih
          apply List.Perm.symm
          apply List.perm_middle
        rw [← List.perm_cons b] at almost_almost
        apply List.Perm.trans _ almost_almost
        apply List.perm_middle
      rw [← List.perm_cons d] at almost
      apply almost.trans
      apply List.Perm.swap

lemma mergesort_permutes {n : ℕ} {x : List α} (hnxl : x.length ≤ n) :
  mergesort x ~ x :=
by
  revert x
  induction n with
  | zero =>
    intro x hx
    rw [Nat.le_zero, List.length_eq_zero] at hx
    rw [hx]
    rfl
  | succ n ih =>
    intro x hx
    match x with
    | [ ] => rfl
    | [ _ ] => rfl
    | a :: b :: s =>
      unfold mergesort
      apply (merge_permutes (mergesort (eo (a :: b :: s))) (mergesort (eo (b :: s)))).trans
      have final : eo (a :: b :: s) ++ eo (b :: s) ~ a :: b :: s
      · apply split_permutes
      apply List.Perm.trans _ final
      apply List.Perm.append
      · apply ih
        have len_odd := length_eo2_lt a b s
        simp only [List.length_cons] at hx
        linarith
      · apply ih
        have len_even := length_eo1_lt b s
        simp only [List.length_cons] at hx
        linarith


theorem mergesort_works : ∀ x : List α, Sorted (mergesort x) ∧ (mergesort x) ~ x :=
by
  intro x
  constructor
  · apply mergesort_sorts
    rfl
  · apply mergesort_permutes
    rfl

-- theorem eq_of_bothSorted_and_perm : ∀ x y : List α, Sorted x ∧ Sorted y ∧ x ~ y → x = y :=
-- by
--   intro x y ⟨hx, _, _⟩
--   revert y
--   induction x with
--   | nil => simp_all
--   | cons d l ih =>
--     specialize ih (sorted_of_sorted_cons hx)
--     intro y hy hxy
--     cases y with
--     | nil => simp at hxy
--     | cons d' l' =>
--       specialize ih l' (sorted_of_sorted_cons hy)
--       have hdd : d = d'
--       · have not_lt : ¬ (d < d')
--         · intro hlt
--           have dltall : ∀ a ∈ l', d < a
--           · sorry -- from `hlt` transitivity `hy`
--           have notin : d ∉ d' :: l'
--           · intro ifin
--             cases ifin with
--             | head => exact hlt.false
--             | tail _ din => exact (dltall d din).false
--           have yesin : d ∈ d :: l
--           · apply List.mem_cons_self
--           sorry -- contradictory with `hxy`
--         have not_gt : ¬ (d' < d)
--         · sorry -- symmetric to above
--         apply eq_of_le_of_not_lt (le_of_not_gt not_gt) not_lt
--       simp [hdd] at *
--       exact ih hxy

end lelo
