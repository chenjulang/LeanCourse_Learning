import Mathlib.Tactic

variable (G : Type) [Group G] (a b : G) (H K : Subgroup G)

lemma test001 : CompleteLattice (Subgroup G) := by
  apply @Subgroup.instCompleteLatticeSubgroup
lemma test002 : CompleteLattice (Subgroup G) := by
  infer_instance
