-- import Mathlib.LinearAlgebra.Basic
-- import Mathlib.GroupTheory.QuotientGroup
-- set_option checkBinderAnnotations false
-- set_option autoImplicit true

-- namespace my_quotient

--   variable {γ : Sort*} {φ : Sort*} {s₁ : Setoid α} {s₂ : Setoid β} {s₃ : Setoid γ}

--   variable (r2 : α → α → Prop)
--   opaque Quot2 {α : Sort u} (r : α → α → Prop) : Sort u

--   #check Quot2 r2
--   -- opaque Quot_mk {α : Sort u} (r : α → α → Prop) (a : α) : Quot2 r2

--   def Quotient2 {α : Sort u} (s : Setoid α) :=
--   @Quot2 α s.r

--   def QuotientGroup2_mk'' (a : α) (s : Setoid α)
--   -- : Quotient2 s₁
--   := Quot2 s.1

--   section my_notioin
--     universe u v

--     class HasQuotient2 (A : outParam <| Type u) (B : Type v) where
--     /-- auxiliary quotient function, the one used will have `A` explicit -/
--     quotient' : B → Type max u v

--     @[reducible]
--     def HasQuotient2.Quotient2 (A : outParam <| Type u) {B : Type v}
--         [HasQuotient2 A B] (b : B) : Type max u v :=
--       HasQuotient2.quotient' b

--     notation:35 G " shang " H:34 => HasQuotient2.Quotient2 G H



--   end my_notioin






--   variable {α : Type*} [Group α] {s : Subgroup α}

--   -- def leftRel2 : Setoid α :=
--   -- MulAction.orbitRel s.op α

--   -- #check leftRel2 s

--   -- instance instHasQuotientSubgroup2 : HasQuotient2 α (Subgroup α) :=
--   --   ⟨fun s => Quotient2 (leftRel2 s)⟩

--   #check QuotientGroup.mk
--   def QuotientGroup2_mk  (a : α)
--   -- : α shang s
--   :=
--   -- Quotient.mk'' a
--   QuotientGroup2_mk'' a

--   #check Quotient2 -- {α : Sort u} → Setoid α → Sort u
--   #check Quotient2 s₁ -- Sort u_3
--   #check s₁.1 -- α → α → Prop
--   #check Quot2 s₁.1 -- Sort u_3


-- end my_quotient

-- #check Quot.sound


-- -- //
-- -- // 下面是旧版的动机代码
-- -- //

-- -- universes u v w
-- -- variables {α : Type u} {β : Type v} {γ : Type w}
-- -- variables [ring α] [module α β] [module α γ] (s : set β) [hs : is_submodule s]
-- -- include α s hs


-- -- def quotient_rel : setoid β :=
-- -- ⟨λb₁ b₂, b₁ - b₂ ∈ s,
-- --   assume b, by simp [zero],
-- --   assume b₁ b₂ hb,
-- --   have - (b₁ - b₂) ∈ s, from is_submodule.neg hb,
-- --   by simpa using this,
-- --   assume b₁ b₂ b₃ hb₁₂ hb₂₃,
-- --   have (b₁ - b₂) + (b₂ - b₃) ∈ s, from add hb₁₂ hb₂₃,
-- --   by simpa using this⟩

-- -- local attribute [instance] quotient_rel

-- -- lemma quotient_rel_eq {b₁ b₂ : β} : (b₁ ≈ b₂) = (b₁ - b₂ ∈ s) := rfl

-- -- section
-- -- variable (β)
-- -- /-- Quotient module. `quotient β s` is the quotient of the module `β` by the submodule `s`. -/
-- -- def quotient : Type v := quotient (quotient_rel s)
