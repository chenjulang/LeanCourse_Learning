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
  -- ⟨fun h => funext (fun i => funext <| h i)
  -- ,
  -- fun h => by simp [h]⟩
  ---
