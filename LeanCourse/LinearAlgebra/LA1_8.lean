import Mathlib.Algebra.Algebra.Opposite


universe u u' v w

def Matrix (m : Type u) (n : Type u') (α : Type v)
: Type max u u' v
:=
  m → n → α

  variable {l m n o : Type*} {m' : o → Type*} {n' : o → Type*}

  variable {R : Type*} {S : Type*} {α : Type v} {β : Type w} {γ : Type*}

  variable {M N : Matrix m n α}

theorem ext_iff
: (∀ i j, M i j = N i j)
  ↔
  M = N
:= by
  -- 第一种写法：
  -- ⟨fun h => funext (fun i => funext <| h i)
  -- ,
  -- fun h => by simp [h]⟩
  constructor
  · intro h
    refine' funext _
    have h1 := fun x ↦ funext (h x)
    exact h1
  · intro h2
    intro h3
    intro h4
    rw [h2]


theorem ext : (∀ i j, M i j = N i j) → M = N :=
  -- ext_iff.mp
  sorry
