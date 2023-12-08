import Mathlib.Data.Real.Sqrt
-- Define a variable
variable (a b : ℕ)

-- Define a proposition
-- #check Even
-- def is_even (n : ℕ) : Prop := n % 2 = 0

-- Prove a simple theorem
theorem even_plus_odd_is_odd
: ∀ (m n : ℕ), Even m → ¬ Even n → ¬ Even (m + n)
:= by sorry
  -- intros m n h1 h2
  -- -- unfold Even
  -- -- unfold Even at h1 h2
  -- refine Nat.not_even_iff.mpr ?_
  -- unfold Even at h1 h2
  -- specialize r1
  -- intro h3
  -- apply?
  -- rw [h1]
  -- intro h3
  -- rw [h3] at h2
  -- contradiction


-- Define a vector
def v : Fin 3 → ℝ := λ i => if i = 0 then 1 else 0
def v2 : Fin 3 → ℝ := λ i => if i = 1 then 1 else 0

-- Vector addition
def add_vectors (u v : Fin 3 → ℝ)
: Fin 3 → ℝ
:= λ i => u i + v i

#eval v

-- Vector scalar multiplication
def scalar_multiply (k : ℝ) (v : Fin 3 → ℝ)
: Fin 3 → ℝ
:= λ i => k * v i
