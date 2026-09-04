import Mettapedia.Logic.Derivation

/-!
# Conservative extension of finitary rule systems

This file characterizes exactly when adding a second finitary rule predicate
preserves derivability.  The criterion is admissibility of every added rule
instance in the original system.
-/

set_option autoImplicit false

namespace Mettapedia.Logic

universe u

variable {J : Type u}

/-- One instantiated finitary rule is admissible in `rules` when derivability
of all its listed premises entails derivability of its conclusion. -/
def RuleInstanceAdmissible (rules : List J → J → Prop)
    (premises : List J) (conclusion : J) : Prop :=
  (∀ premise ∈ premises, Derives rules premise) → Derives rules conclusion

/-- Add every rule instance accepted by `additional` to `rules`. -/
def extendRules (rules additional : List J → J → Prop) :
    List J → J → Prop :=
  fun premises conclusion =>
    rules premises conclusion ∨ additional premises conclusion

/-- Two rule predicates generate exactly the same derivable judgments. -/
def SameDerivability (left right : List J → J → Prop) : Prop :=
  ∀ judgment, Derives left judgment ↔ Derives right judgment

/-- Exact criterion for conservative rule extension: adding `additional`
preserves all derivability iff every added rule instance is already admissible
in the original system. -/
theorem extendRules_sameDerivability_iff
    (rules additional : List J → J → Prop) :
    SameDerivability (extendRules rules additional) rules ↔
      ∀ premises conclusion, additional premises conclusion →
        RuleInstanceAdmissible rules premises conclusion := by
  constructor
  · intro sameDerivability premises conclusion additionalRule
      premiseDerivations
    apply (sameDerivability conclusion).mp
    exact Derives.node premises conclusion (Or.inr additionalRule)
      (fun premise premiseMem =>
        (sameDerivability premise).mpr
          (premiseDerivations premise premiseMem))
  · intro additionalAdmissible judgment
    constructor
    · apply Derives.least (Derives rules)
      intro premises conclusion extendedRule premiseDerivations
      rcases extendedRule with originalRule | additionalRule
      · exact Derives.node premises conclusion originalRule premiseDerivations
      · exact additionalAdmissible premises conclusion additionalRule
          premiseDerivations
    · exact Derives.mono
        (fun _ _ originalRule => Or.inl originalRule)

/-- Negative boundary: a new premise-free rule for an underivable judgment is
necessarily non-conservative. -/
theorem extendRules_not_sameDerivability_of_new_nullary
    (rules additional : List J → J → Prop)
    (conclusion : J) (additionalRule : additional [] conclusion)
    (notDerivable : ¬ Derives rules conclusion) :
    ¬ SameDerivability (extendRules rules additional) rules := by
  intro sameDerivability
  apply notDerivable
  apply (sameDerivability conclusion).mp
  exact Derives.node [] conclusion (Or.inr additionalRule)
    (by intro premise premiseMem; cases premiseMem)

namespace ConservativeExtensionCanary

inductive Judgment where
  | a
  | b
  | c
  | d
deriving DecidableEq

inductive BaseRule : List Judgment → Judgment → Prop where
  | a : BaseRule [] .a
  | aToB : BaseRule [.a] .b
  | bToC : BaseRule [.b] .c

/-- A shortcut rule that is already admissible in `BaseRule`. -/
inductive ShortcutRule : List Judgment → Judgment → Prop where
  | aToC : ShortcutRule [.a] .c

theorem shortcut_admissible :
    ∀ premises conclusion, ShortcutRule premises conclusion →
      RuleInstanceAdmissible BaseRule premises conclusion := by
  intro premises conclusion shortcut premiseDerivations
  cases shortcut
  have aDerivable := premiseDerivations Judgment.a (by simp)
  have bDerivable : Derives BaseRule Judgment.b :=
    Derives.node [Judgment.a] Judgment.b BaseRule.aToB (by
      intro premise premiseMem
      simp only [List.mem_singleton] at premiseMem
      subst premise
      exact aDerivable)
  exact Derives.node [Judgment.b] Judgment.c BaseRule.bToC (by
    intro premise premiseMem
    simp only [List.mem_singleton] at premiseMem
    subst premise
    exact bDerivable)

/-- Positive control: adjoining the `a ⟶ c` shortcut changes proof shape but
not the set of derivable judgments. -/
theorem shortcut_sameDerivability :
    SameDerivability (extendRules BaseRule ShortcutRule) BaseRule :=
  (extendRules_sameDerivability_iff BaseRule ShortcutRule).mpr
    shortcut_admissible

/-- A premise-free rule deriving the otherwise unreachable judgment `d`. -/
inductive NewFactRule : List Judgment → Judgment → Prop where
  | d : NewFactRule [] .d

theorem d_not_derivable : ¬ Derives BaseRule .d := by
  intro dDerivable
  exact Derives.least (fun judgment => judgment ≠ .d) (by
    intro premises conclusion rule _
    cases rule <;> decide) dDerivable rfl

/-- Negative control: adding a genuinely new fact changes derivability. -/
theorem newFact_not_sameDerivability :
    ¬ SameDerivability (extendRules BaseRule NewFactRule) BaseRule :=
  extendRules_not_sameDerivability_of_new_nullary
    BaseRule NewFactRule .d NewFactRule.d d_not_derivable

end ConservativeExtensionCanary

end Mettapedia.Logic
