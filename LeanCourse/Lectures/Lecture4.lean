import LeanCourse.Common
open Real Function
noncomputable section
set_option linter.unusedVariables false


/- # Last Lecture -/

/-
To deal with orders, we can
* apply lemmas from the library
  - to search for a lemma, use `exact?`, `apply?`, `rw?` or guess the name and use auto-complete.
* use tactics like `trans`, `gcongr` and `linarith`
-/







/- # Today: Logic

We cover sections 3.1, 3.2, 3.4 and 3.5 from Mathematics in Lean. -/

/-
We will go over the quantifiers `∀` (for all) and `∃` (exists), and the connectives
`∧` (and), `∨` (or), `→` (implies), `↔` (if and only if) and `¬` (not).
-/



/- ## Universal quantification and implication
The tactics for universal quantification and implication are the same.
* We can use `intro` to prove an universal quantification or implication.
* We can use `apply` or `specialize` to use an universal quantification or implication
  in a hypothesis. -/

def NonDecreasing (f : ℝ → ℝ) : Prop := ∀ x₁ x₂ : ℝ, x₁ ≤ x₂ → f x₁ ≤ f x₂

example (f g : ℝ → ℝ) (hg : NonDecreasing g) (hf : NonDecreasing f) :
    NonDecreasing (g ∘ f) := by {
  rw [NonDecreasing]
  rw [NonDecreasing] at hf hg
  intro x₁ x₂ hx₁x₂
  -- have : f x₁ ≤ f x₂ := by
  --   apply hf
  --   exact hx₁x₂
  specialize hf x₁ x₂ hx₁x₂
  specialize hg (f x₁) (f x₂) hf
  rw [Function.comp, Function.comp]
  exact hg
}

/-- Note: `f + g` is the function defined by `(f + g)(x) := f(x) + g(x)` -/
example (f g : ℝ → ℝ) (hf : NonDecreasing f) (hg : NonDecreasing g) :
    NonDecreasing (f + g) := by {
  intro x₁ x₂ hx₁x₂
  simp
  gcongr
  · specialize hf x₁ x₂ hx₁x₂
    assumption
  · apply hg
    assumption
}








/- ## If and only if
We already saw last time:
* You can use `constructor` to prove an "if and only if" statement
* To use an "if and only if" statement `h`, you can use any of the following
  - `apply h.1`
  - `apply h.2`
  - `rw [h]`
  - `rw [← h]`
-/

example (x : ℝ) : 0 ≤ x ^ 3 ↔ 0 ≤ x ^ 5 := by {
  have h1 : 0 ≤ x ^ 3 ↔ 0 ≤ x := by
    apply Odd.pow_nonneg_iff
    simp
  have h2 : 0 ≤ x ^ 5 ↔ 0 ≤ x := by
    apply Odd.pow_nonneg_iff
    simp
  -- constructor
  -- · intro h3
  --   apply h2.2
  --   apply h1.1
  --   exact h3
  -- · intro h3
  --   apply h1.2
  --   apply h2.1
  --   exact h3
  rw [h1, h2]
}






/- ## Conjunction

In Lean the conjunction of two statements `P` and `Q` is denoted by `P ∧ Q`, read as "P and Q".

We can use a conjunction similarly to the `↔`:
* If `h : P ∧ Q` then `h.1 : P` and `h.2 : Q`.
* To prove `P ∧ Q` use the `constructor` tactic.

Furthermore, we can decompose conjunction and equivalences.
* If `h : P ∧ Q`, the tactic `obtain ⟨hP, hQ⟩ := h`
  gives two new assumptions `hP : P` and `hQ : Q`.
* If `h : P ↔ Q`, the tactic `obtain ⟨hPQ, hQP⟩ := h`
  gives two new assumptions `hPQ : P → Q` and `hQP : Q → P`.
-/

example (p q r s : Prop) (h : p → r) (h' : q → s) : p ∧ q → r ∧ s := by {
  intro hpq
  obtain ⟨hp, hq⟩ := hpq
  constructor
  · apply h
    exact hp
  · apply h'
    exact hq
}

example (p q r : Prop) : (p → (q → r)) ↔ (p ∧ q → r) := by {
  constructor
  · intro hpqr hpq
    apply hpqr
    · exact hpq.1
    · exact hpq.2
  · intro hpqr hp hq
    apply hpqr
    constructor
    · assumption
    · assumption
}







/- ## Extential quantifiers

In order to prove `∃ x, P x`, we give some `x₀` using tactic `use x₀` and
then prove `P x₀`. This `x₀` can be any expression.
-/
example : ∃ n : ℕ, ∀ m : ℕ, m * n = m + m + m := by {
  use 3
  intro m
  ring
}


/-
In order to use `h : ∃ x, P x`, we use can use
`obtain ⟨x₀, hx₀⟩ := h`
to fix one `x₀` that works.
-/
example {α : Type*} [PartialOrder α]
    (IsDense : ∀ x y : α, x < y → ∃ z : α, x < z ∧ z < y)
    (x y : α) (hxy : x < y) :
    ∃ z₁ z₂ : α, x < z₁ ∧ z₁ < z₂ ∧ z₂ < y := by {
  -- specialize IsDense x y hxy
  have h1:= IsDense x y hxy
  obtain ⟨z, h1z, h2z⟩ := h1
  use z
  have h2:= IsDense z y h2z
  obtain ⟨z', h1z', h2z'⟩ := h2
  use z'
}








/- Exercises -/

example {p : ℝ → Prop} (h : ∀ x, p x) : ∃ x, p x := by
  use 42
  exact h 42


example {α : Type*} {p q : α → Prop} (h : ∀ x, p x → q x) :
    (∃ x, p x) → (∃ x, q x) := by {
  intro ⟨x, hx⟩
  use x
  exact h x hx


}


example {α : Type*} {p : α → Prop} {r : Prop} :
    ((∃ x, p x) → r) ↔ (∀ x, p x → r) := by sorry


example {α : Type*} {p : α → Prop} {r : Prop} :
    (∃ x, p x ∧ r) ↔ ((∃ x, p x) ∧ r) := by sorry




/- ## Disjunctions -/

/-
Lean denotes by `∨` the logical OR operator.

In order to make use of an assumption
  `h : P ∨ Q`
we use the obtain tactic:
  `obtain hP|hQ := h`
which creates two proof branches: one branch assuming `hP : P`,
and one branch assuming `hQ : Q`.

In order to directly prove a goal `P ∨ Q`,
we use either the `left` tactic and prove `P` or the `right`
tactic and prove `Q`.
-/

variable (a b : ℝ)
#check (mul_eq_zero : a*b = 0 ↔ a = 0 ∨ b = 0)

example : a = a * b → a = 0 ∨ b = 1 := by {
  intro h
  have hyp : a * (b - 1) = 0 := by
    calc a * (b - 1) = a * b - a := by ring
      _ = a - a := by rw [← h]
      _ = 0 := by ring
  rw [mul_eq_zero] at hyp
  obtain ha|hb := hyp
  · left
    assumption
  · right
    linarith
}


example (f : ℝ → ℝ) (hf : StrictMono f) : Injective f := by {
  rw [Injective]
  rw [StrictMono] at hf
  intro x y hxy
  have h : x < y ∨ x = y ∨ x > y := by
    exact lt_trichotomy x y
  obtain h_lt|h_eq|h_gt := h
  · specialize hf h_lt
    linarith
  · assumption
  · specialize hf h_gt
    linarith
}
