import Mettapedia.GSLT.LanguageDef.SortedABTSubstitution

/-!
# Scoped replacement environments agree on available variables

The existing simultaneous substitution reads only the input context. Two
replacement environments that agree there produce the same term, including
beneath mixed-sort binders. Entries outside that context are irrelevant.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.SortedSignatureIndexedABT.Term

variable {VarSort Head : Type} [DecidableEq VarSort]

def AgreeWithin (depth : VarSort → Nat) (σ τ : Substitution VarSort Head) : Prop :=
  ∀ sort index, index < depth sort → σ sort index = τ sort index

theorem liftSubstitution_agree {depth : VarSort → Nat} {σ τ : Substitution VarSort Head}
    (agree : AgreeWithin depth σ τ) (binders : List VarSort) :
    AgreeWithin (enter depth binders) (liftSubstitution binders σ) (liftSubstitution binders τ) := by
  intro sort index available
  by_cases bound : index < binderCount sort binders
  · simp [liftSubstitution, bound]
  · have prior : index - binderCount sort binders < depth sort := by
      simp only [enter] at available
      omega
    simp only [liftSubstitution, bound, ↓reduceIte, agree sort _ prior]

mutual

theorem parallelSubstitute_congr_scoped {depth : VarSort → Nat}
    {σ τ : Substitution VarSort Head} (agree : AgreeWithin depth σ τ)
    (term : Term VarSort Head) (wellScoped : supportedAt depth term = true) :
    parallelSubstitute σ term = parallelSubstitute τ term := by
  cases term with
  | idx sort index =>
      apply agree
      simpa only [supportedAt, decide_eq_true_eq] using wellScoped
  | node head fields =>
      exact congrArg (Term.node head) (Fields.parallelSubstitute_congr_scoped agree fields wellScoped)

theorem Fields.parallelSubstitute_congr_scoped {depth : VarSort → Nat}
    {σ τ : Substitution VarSort Head} (agree : AgreeWithin depth σ τ)
    (fields : Fields VarSort Head) (wellScoped : Fields.supportedAt depth fields = true) :
    Fields.parallelSubstitute σ fields = Fields.parallelSubstitute τ fields := by
  cases fields with
  | nil => rfl
  | cons binders term rest =>
      simp only [Fields.supportedAt, Bool.and_eq_true] at wellScoped
      simp only [Fields.parallelSubstitute]
      rw [parallelSubstitute_congr_scoped (liftSubstitution_agree agree binders) term wellScoped.1,
        Fields.parallelSubstitute_congr_scoped agree rest wellScoped.2]

end

end Mettapedia.GSLT.LanguageDef.SortedSignatureIndexedABT.Term
