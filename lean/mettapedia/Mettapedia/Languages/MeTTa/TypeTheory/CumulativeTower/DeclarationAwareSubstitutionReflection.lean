import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.DeclarationAwareSubstitutionCompiler

/-!
# Relational reflection for authored Prime substitution

The executable compiler computes on an independently defined first-order term
algebra.  This module supplies the opposite authority: relations over public
canonical patterns whose constructors mirror the mathematical operations, not
the proof checker.  They intentionally admit opaque ground payloads at the
generic boundary.  Exact functional reflection is recovered when the source
lies in the canonical encoded image.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.DeclarationAwareSubstitutionReflection

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower
open Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.DeclarationAwarePatternCodec
open Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.DeclarationAwareSubstitutionLanguage
open Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.DeclarationAwareSubstitutionCompiler
open Mettapedia.OSLF.MeTTaIL.Syntax

/-! ## Independent relational semantics -/

/-- Strict order on the authored unary numeral presentation.  The tail is
opaque at this generic layer; canonical encoded naturals form the functional
subfibre used by the compiler. -/
inductive IndexLt : Pattern → Pattern → Prop where
  | zeroSucc (right : Pattern) : IndexLt zero (succ right)
  | succSucc {left right : Pattern} :
      IndexLt left right → IndexLt (succ left) (succ right)

/-- Number of leading authored successor constructors.  Opaque tails have
depth zero, which is sufficient for strict-order irreflexivity without
pretending that every generic payload decodes as a natural number. -/
def unaryDepth : Pattern → Nat
  | .apply "prime-nat-succ" [rest] => unaryDepth rest + 1
  | _ => 0

@[simp] theorem unaryDepth_zero : unaryDepth zero = 0 := rfl

@[simp] theorem unaryDepth_succ (value : Pattern) :
    unaryDepth (succ value) = unaryDepth value + 1 := rfl

theorem IndexLt.depth_lt {left right : Pattern} (less : IndexLt left right) :
    unaryDepth left < unaryDepth right := by
  induction less with
  | zeroSucc right => simp
  | succSucc less lessIH => simpa using Nat.add_lt_add_right lessIH 1

theorem IndexLt.irrefl (value : Pattern) : ¬ IndexLt value value := by
  intro less
  exact (Nat.lt_irrefl (unaryDepth value)) less.depth_lt

theorem IndexLt.no_two_step_to_succ {left middle : Pattern}
    (first : IndexLt left middle) (second : IndexLt middle (succ left)) :
    False := by
  have firstDepth := first.depth_lt
  have secondDepth := second.depth_lt
  rw [unaryDepth_succ] at secondDepth
  omega

theorem IndexLt.asymm {left right : Pattern}
    (first : IndexLt left right) (second : IndexLt right left) : False := by
  exact (Nat.not_lt_of_ge (Nat.le_of_lt second.depth_lt)) first.depth_lt

@[simp] theorem unaryDepth_encodeNat (value : Nat) :
    unaryDepth (encodeNat value) = value := by
  induction value with
  | zero => rfl
  | succ value valueIH =>
      change unaryDepth (succ (encodeNat value)) = value + 1
      rw [unaryDepth_succ, valueIH]

theorem IndexLt.reflect_encode {left right : Nat}
    (less : IndexLt (encodeNat left) (encodeNat right)) : left < right := by
  simpa using less.depth_lt

/-- Weakening by one, expressed wholly over the public term constructors. -/
inductive Weakens : Pattern → Pattern → Pattern → Prop where
  | varBelow {cutoff index : Pattern} :
      IndexLt index cutoff → Weakens cutoff (tmVar index) (tmVar index)
  | varAtOrAbove {cutoff index : Pattern} :
      IndexLt cutoff (succ index) →
        Weakens cutoff (tmVar index) (tmVar (succ index))
  | const (cutoff name : Pattern) :
      Weakens cutoff (tmConst name) (tmConst name)
  | head (cutoff head : Pattern) :
      Weakens cutoff (tmHead head) (tmHead head)
  | pi {cutoff domain body domainResult bodyResult : Pattern} :
      Weakens cutoff domain domainResult →
      Weakens (succ cutoff) body bodyResult →
      Weakens cutoff (tmPi domain body) (tmPi domainResult bodyResult)
  | sigma {cutoff domain body domainResult bodyResult : Pattern} :
      Weakens cutoff domain domainResult →
      Weakens (succ cutoff) body bodyResult →
      Weakens cutoff (tmSigma domain body) (tmSigma domainResult bodyResult)
  | id {cutoff type left right typeResult leftResult rightResult : Pattern} :
      Weakens cutoff type typeResult →
      Weakens cutoff left leftResult →
      Weakens cutoff right rightResult →
      Weakens cutoff (tmId type left right)
        (tmId typeResult leftResult rightResult)
  | lam {cutoff body bodyResult : Pattern} :
      Weakens (succ cutoff) body bodyResult →
      Weakens cutoff (tmLam body) (tmLam bodyResult)
  | app {cutoff function argument functionResult argumentResult : Pattern} :
      Weakens cutoff function functionResult →
      Weakens cutoff argument argumentResult →
      Weakens cutoff (tmApp function argument)
        (tmApp functionResult argumentResult)
  | pair {cutoff first second firstResult secondResult : Pattern} :
      Weakens cutoff first firstResult →
      Weakens cutoff second secondResult →
      Weakens cutoff (tmPair first second) (tmPair firstResult secondResult)
  | fst {cutoff pair pairResult : Pattern} :
      Weakens cutoff pair pairResult →
      Weakens cutoff (tmFst pair) (tmFst pairResult)
  | snd {cutoff pair pairResult : Pattern} :
      Weakens cutoff pair pairResult →
      Weakens cutoff (tmSnd pair) (tmSnd pairResult)
  | refl {cutoff term termResult : Pattern} :
      Weakens cutoff term termResult →
      Weakens cutoff (tmRefl term) (tmRefl termResult)

/-- Capture-avoiding substitution over the same public first-order carrier. -/
inductive Substitutes : Pattern → Pattern → Pattern → Pattern → Prop where
  | varEqual (index replacement : Pattern) :
      Substitutes index replacement (tmVar index) replacement
  | varBelow {index replacement variableTerm : Pattern} :
      IndexLt variableTerm index →
      Substitutes index replacement (tmVar variableTerm) (tmVar variableTerm)
  | varAbove {index replacement predecessor : Pattern} :
      IndexLt index (succ predecessor) →
      Substitutes index replacement (tmVar (succ predecessor))
        (tmVar predecessor)
  | const (index replacement name : Pattern) :
      Substitutes index replacement (tmConst name) (tmConst name)
  | head (index replacement head : Pattern) :
      Substitutes index replacement (tmHead head) (tmHead head)
  | pi {index replacement domain body domainResult liftedReplacement
      bodyResult : Pattern} :
      Substitutes index replacement domain domainResult →
      Weakens zero replacement liftedReplacement →
      Substitutes (succ index) liftedReplacement body bodyResult →
      Substitutes index replacement (tmPi domain body)
        (tmPi domainResult bodyResult)
  | sigma {index replacement domain body domainResult liftedReplacement
      bodyResult : Pattern} :
      Substitutes index replacement domain domainResult →
      Weakens zero replacement liftedReplacement →
      Substitutes (succ index) liftedReplacement body bodyResult →
      Substitutes index replacement (tmSigma domain body)
        (tmSigma domainResult bodyResult)
  | id {index replacement type left right typeResult leftResult rightResult :
      Pattern} :
      Substitutes index replacement type typeResult →
      Substitutes index replacement left leftResult →
      Substitutes index replacement right rightResult →
      Substitutes index replacement (tmId type left right)
        (tmId typeResult leftResult rightResult)
  | lam {index replacement body liftedReplacement bodyResult : Pattern} :
      Weakens zero replacement liftedReplacement →
      Substitutes (succ index) liftedReplacement body bodyResult →
      Substitutes index replacement (tmLam body) (tmLam bodyResult)
  | app {index replacement function argument functionResult argumentResult :
      Pattern} :
      Substitutes index replacement function functionResult →
      Substitutes index replacement argument argumentResult →
      Substitutes index replacement (tmApp function argument)
        (tmApp functionResult argumentResult)
  | pair {index replacement first second firstResult secondResult : Pattern} :
      Substitutes index replacement first firstResult →
      Substitutes index replacement second secondResult →
      Substitutes index replacement (tmPair first second)
        (tmPair firstResult secondResult)
  | fst {index replacement pair pairResult : Pattern} :
      Substitutes index replacement pair pairResult →
      Substitutes index replacement (tmFst pair) (tmFst pairResult)
  | snd {index replacement pair pairResult : Pattern} :
      Substitutes index replacement pair pairResult →
      Substitutes index replacement (tmSnd pair) (tmSnd pairResult)
  | refl {index replacement term termResult : Pattern} :
      Substitutes index replacement term termResult →
      Substitutes index replacement (tmRefl term) (tmRefl termResult)

/-- One root beta contraction, factored through relational substitution. -/
inductive RootBeta : Pattern → Pattern → Prop where
  | intro {body argument result : Pattern} :
      Substitutes zero argument body result →
      RootBeta (tmApp (tmLam body) argument) result

/-- The semantic fibre selected by each authored judgment head. -/
def JudgmentMeaning : Pattern → Prop
  | .apply "prime-index-lt" [left, right] => IndexLt left right
  | .apply "prime-tm-weakens-at" [cutoff, source, target] =>
      Weakens cutoff source target
  | .apply "prime-tm-substitutes-at" [index, replacement, source, target] =>
      Substitutes index replacement source target
  | .apply "prime-tm-root-beta" [source, target] => RootBeta source target
  | _ => False

/-! ## Local rule soundness -/

private theorem argumentsValidAt_one_shape
    {name : String} {arguments : List Pattern}
    (valid : argumentsValidAt [(name, 0)] arguments = true) :
    ∃ first, arguments = [first] := by
  cases arguments with
  | nil => simp [argumentsValidAt] at valid
  | cons first rest =>
      cases rest with
      | nil => exact ⟨first, rfl⟩
      | cons second rest => simp [argumentsValidAt] at valid

private theorem argumentsValidAt_two_shape
    {firstName secondName : String} {arguments : List Pattern}
    (valid : argumentsValidAt [(firstName, 0), (secondName, 0)] arguments = true) :
    ∃ first second, arguments = [first, second] := by
  cases arguments with
  | nil => simp [argumentsValidAt] at valid
  | cons first rest =>
      cases rest with
      | nil => simp [argumentsValidAt] at valid
      | cons second rest =>
          cases rest with
          | nil => exact ⟨first, second, rfl⟩
          | cons third rest => simp [argumentsValidAt] at valid

private theorem argumentsValidAt_three_shape
    {firstName secondName thirdName : String} {arguments : List Pattern}
    (valid : argumentsValidAt
      [(firstName, 0), (secondName, 0), (thirdName, 0)] arguments = true) :
    ∃ first second third, arguments = [first, second, third] := by
  cases arguments with
  | nil => simp [argumentsValidAt] at valid
  | cons first rest =>
      cases rest with
      | nil => simp [argumentsValidAt] at valid
      | cons second rest =>
          cases rest with
          | nil => simp [argumentsValidAt] at valid
          | cons third rest =>
              cases rest with
              | nil => exact ⟨first, second, third, rfl⟩
              | cons fourth rest => simp [argumentsValidAt] at valid

private theorem argumentsValidAt_four_shape
    {firstName secondName thirdName fourthName : String}
    {arguments : List Pattern}
    (valid : argumentsValidAt
      [(firstName, 0), (secondName, 0), (thirdName, 0), (fourthName, 0)]
      arguments = true) :
    ∃ first second third fourth,
      arguments = [first, second, third, fourth] := by
  cases arguments with
  | nil => simp [argumentsValidAt] at valid
  | cons first rest =>
      cases rest with
      | nil => simp [argumentsValidAt] at valid
      | cons second rest =>
          cases rest with
          | nil => simp [argumentsValidAt] at valid
          | cons third rest =>
              cases rest with
              | nil => simp [argumentsValidAt] at valid
              | cons fourth rest =>
                  cases rest with
                  | nil => exact ⟨first, second, third, fourth, rfl⟩
                  | cons fifth rest => simp [argumentsValidAt] at valid

private theorem argumentsValidAt_five_shape
    {firstName secondName thirdName fourthName fifthName : String}
    {arguments : List Pattern}
    (valid : argumentsValidAt
      [(firstName, 0), (secondName, 0), (thirdName, 0), (fourthName, 0),
       (fifthName, 0)] arguments = true) :
    ∃ first second third fourth fifth,
      arguments = [first, second, third, fourth, fifth] := by
  cases arguments with
  | nil => simp [argumentsValidAt] at valid
  | cons first rest =>
      cases rest with
      | nil => simp [argumentsValidAt] at valid
      | cons second rest =>
          cases rest with
          | nil => simp [argumentsValidAt] at valid
          | cons third rest =>
              cases rest with
              | nil => simp [argumentsValidAt] at valid
              | cons fourth rest =>
                  cases rest with
                  | nil => simp [argumentsValidAt] at valid
                  | cons fifth rest =>
                      cases rest with
                      | nil => exact ⟨first, second, third, fourth, fifth, rfl⟩
                      | cons sixth rest => simp [argumentsValidAt] at valid

private theorem argumentsValidAt_six_shape
    {firstName secondName thirdName fourthName fifthName sixthName : String}
    {arguments : List Pattern}
    (valid : argumentsValidAt
      [(firstName, 0), (secondName, 0), (thirdName, 0), (fourthName, 0),
       (fifthName, 0), (sixthName, 0)] arguments = true) :
    ∃ first second third fourth fifth sixth,
      arguments = [first, second, third, fourth, fifth, sixth] := by
  cases arguments with
  | nil => simp [argumentsValidAt] at valid
  | cons first rest =>
      cases rest with
      | nil => simp [argumentsValidAt] at valid
      | cons second rest =>
          cases rest with
          | nil => simp [argumentsValidAt] at valid
          | cons third rest =>
              cases rest with
              | nil => simp [argumentsValidAt] at valid
              | cons fourth rest =>
                  cases rest with
                  | nil => simp [argumentsValidAt] at valid
                  | cons fifth rest =>
                      cases rest with
                      | nil => simp [argumentsValidAt] at valid
                      | cons sixth rest =>
                          cases rest with
                          | nil =>
                              exact ⟨first, second, third, fourth, fifth,
                                sixth, rfl⟩
                          | cons seventh rest =>
                              simp [argumentsValidAt] at valid

private theorem argumentsValidAt_seven_shape
    {firstName secondName thirdName fourthName fifthName sixthName seventhName :
      String} {arguments : List Pattern}
    (valid : argumentsValidAt
      [(firstName, 0), (secondName, 0), (thirdName, 0), (fourthName, 0),
       (fifthName, 0), (sixthName, 0), (seventhName, 0)] arguments = true) :
    ∃ first second third fourth fifth sixth seventh,
      arguments = [first, second, third, fourth, fifth, sixth, seventh] := by
  cases arguments with
  | nil => simp [argumentsValidAt] at valid
  | cons first rest =>
      cases rest with
      | nil => simp [argumentsValidAt] at valid
      | cons second rest =>
          cases rest with
          | nil => simp [argumentsValidAt] at valid
          | cons third rest =>
              cases rest with
              | nil => simp [argumentsValidAt] at valid
              | cons fourth rest =>
                  cases rest with
                  | nil => simp [argumentsValidAt] at valid
                  | cons fifth rest =>
                      cases rest with
                      | nil => simp [argumentsValidAt] at valid
                      | cons sixth rest =>
                          cases rest with
                          | nil => simp [argumentsValidAt] at valid
                          | cons seventh rest =>
                              cases rest with
                              | nil =>
                                  exact ⟨first, second, third, fourth, fifth,
                                    sixth, seventh, rfl⟩
                              | cons eighth rest =>
                                  simp [argumentsValidAt] at valid

private theorem argumentsValidAt_eight_shape
    {firstName secondName thirdName fourthName fifthName sixthName seventhName
      eighthName : String} {arguments : List Pattern}
    (valid : argumentsValidAt
      [(firstName, 0), (secondName, 0), (thirdName, 0), (fourthName, 0),
       (fifthName, 0), (sixthName, 0), (seventhName, 0), (eighthName, 0)]
      arguments = true) :
    ∃ first second third fourth fifth sixth seventh eighth,
      arguments = [first, second, third, fourth, fifth, sixth, seventh,
        eighth] := by
  cases arguments with
  | nil => simp [argumentsValidAt] at valid
  | cons first rest =>
      cases rest with
      | nil => simp [argumentsValidAt] at valid
      | cons second rest =>
          cases rest with
          | nil => simp [argumentsValidAt] at valid
          | cons third rest =>
              cases rest with
              | nil => simp [argumentsValidAt] at valid
              | cons fourth rest =>
                  cases rest with
                  | nil => simp [argumentsValidAt] at valid
                  | cons fifth rest =>
                      cases rest with
                      | nil => simp [argumentsValidAt] at valid
                      | cons sixth rest =>
                          cases rest with
                          | nil => simp [argumentsValidAt] at valid
                          | cons seventh rest =>
                              cases rest with
                              | nil => simp [argumentsValidAt] at valid
                              | cons eighth rest =>
                                  cases rest with
                                  | nil =>
                                      exact ⟨first, second, third, fourth,
                                        fifth, sixth, seventh, eighth, rfl⟩
                                  | cons ninth rest =>
                                      simp [argumentsValidAt] at valid

private theorem ltZeroSucc_application_sound
    (ruleInstance : RuleInstance) (premises : List Pattern)
    (conclusion : Pattern)
    (application : RuleApplication definition ruleInstance premises conclusion)
    (lookup : definition.1.lookupRule? ruleInstance.ruleId =
      some ltZeroSuccRule) :
    JudgmentMeaning conclusion := by
  have executable := instantiateRule?_eq_some_iff_application.mpr application
  cases application with
  | intro rule actualLookup argumentsValid sideConditionsValid
      premisesInstantiate conclusionInstantiates =>
    have ruleEq : rule = ltZeroSuccRule := by
      rw [actualLookup] at lookup
      exact Option.some.inj lookup
    subst rule
    obtain ⟨right, argumentsEq⟩ := argumentsValidAt_one_shape (by
      simpa [ltZeroSuccRule, rule, formal] using argumentsValid)
    simp only [instantiateRule?] at executable
    rw [argumentsEq] at executable
    simp [actualLookup, ltZeroSuccRule, rule, formal, m, indexLt, zero, succ,
      argumentsValidAt, instantiateSchemas?, instantiateSchema?,
      instantiateSchemasAt?, instantiateSchemaAt?, lookupArgumentAt?]
      at executable
    rcases executable with ⟨_, premisesEq, conclusionEq⟩
    rw [← conclusionEq]
    simp only [JudgmentMeaning]
    exact IndexLt.zeroSucc right

private theorem ltSuccSucc_application_sound
    (ruleInstance : RuleInstance) (premises : List Pattern)
    (conclusion : Pattern)
    (application : RuleApplication definition ruleInstance premises conclusion)
    (lookup : definition.1.lookupRule? ruleInstance.ruleId =
      some ltSuccSuccRule)
    (premiseSound : ∀ premise ∈ premises, JudgmentMeaning premise) :
    JudgmentMeaning conclusion := by
  have executable := instantiateRule?_eq_some_iff_application.mpr application
  cases application with
  | intro rule actualLookup argumentsValid sideConditionsValid
      premisesInstantiate conclusionInstantiates =>
    have ruleEq : rule = ltSuccSuccRule := by
      rw [actualLookup] at lookup
      exact Option.some.inj lookup
    subst rule
    obtain ⟨left, right, argumentsEq⟩ := argumentsValidAt_two_shape (by
      simpa [ltSuccSuccRule, rule, formal] using argumentsValid)
    simp only [instantiateRule?] at executable
    rw [argumentsEq] at executable
    simp [actualLookup, ltSuccSuccRule, rule, formal, m, indexLt, succ,
      argumentsValidAt, instantiateSchemas?, instantiateSchema?,
      instantiateSchemasAt?, instantiateSchemaAt?, lookupArgumentAt?]
      at executable
    rcases executable with ⟨_, premisesEq, conclusionEq⟩
    rw [← conclusionEq]
    simp only [JudgmentMeaning]
    apply IndexLt.succSucc
    have premiseMember : indexLt left right ∈ premises := by
      rw [← premisesEq]
      simp [indexLt]
    have premiseMeaning := premiseSound (indexLt left right) premiseMember
    simpa [JudgmentMeaning, indexLt] using premiseMeaning

private theorem weakenVarBelow_application_sound
    (ruleInstance : RuleInstance) (premises : List Pattern)
    (conclusion : Pattern)
    (application : RuleApplication definition ruleInstance premises conclusion)
    (lookup : definition.1.lookupRule? ruleInstance.ruleId =
      some weakenVarBelowRule)
    (premiseSound : ∀ premise ∈ premises, JudgmentMeaning premise) :
    JudgmentMeaning conclusion := by
  have executable := instantiateRule?_eq_some_iff_application.mpr application
  cases application with
  | intro rule actualLookup argumentsValid sideConditionsValid
      premisesInstantiate conclusionInstantiates =>
    have ruleEq : rule = weakenVarBelowRule := by
      rw [actualLookup] at lookup
      exact Option.some.inj lookup
    subst rule
    obtain ⟨cutoff, index, argumentsEq⟩ := argumentsValidAt_two_shape (by
      simpa [weakenVarBelowRule, rule, formal] using argumentsValid)
    simp only [instantiateRule?] at executable
    rw [argumentsEq] at executable
    simp [actualLookup, weakenVarBelowRule, rule, formal, m, indexLt, weakensAt,
      tmVar, argumentsValidAt, instantiateSchemas?, instantiateSchema?,
      instantiateSchemasAt?, instantiateSchemaAt?, lookupArgumentAt?]
      at executable
    rcases executable with ⟨_, premisesEq, conclusionEq⟩
    rw [← conclusionEq]
    simp only [JudgmentMeaning]
    apply Weakens.varBelow
    have member : indexLt index cutoff ∈ premises := by
      rw [← premisesEq]
      simp [indexLt]
    simpa [JudgmentMeaning, indexLt] using
      premiseSound (indexLt index cutoff) member

private theorem weakenVarAtOrAbove_application_sound
    (ruleInstance : RuleInstance) (premises : List Pattern)
    (conclusion : Pattern)
    (application : RuleApplication definition ruleInstance premises conclusion)
    (lookup : definition.1.lookupRule? ruleInstance.ruleId =
      some weakenVarAtOrAboveRule)
    (premiseSound : ∀ premise ∈ premises, JudgmentMeaning premise) :
    JudgmentMeaning conclusion := by
  have executable := instantiateRule?_eq_some_iff_application.mpr application
  cases application with
  | intro rule actualLookup argumentsValid sideConditionsValid
      premisesInstantiate conclusionInstantiates =>
    have ruleEq : rule = weakenVarAtOrAboveRule := by
      rw [actualLookup] at lookup
      exact Option.some.inj lookup
    subst rule
    obtain ⟨cutoff, index, argumentsEq⟩ := argumentsValidAt_two_shape (by
      simpa [weakenVarAtOrAboveRule, rule, formal] using argumentsValid)
    simp only [instantiateRule?] at executable
    rw [argumentsEq] at executable
    simp [actualLookup, weakenVarAtOrAboveRule, rule, formal, m, indexLt,
      weakensAt, tmVar, succ, argumentsValidAt, instantiateSchemas?,
      instantiateSchema?, instantiateSchemasAt?, instantiateSchemaAt?,
      lookupArgumentAt?] at executable
    rcases executable with ⟨_, premisesEq, conclusionEq⟩
    rw [← conclusionEq]
    simp only [JudgmentMeaning]
    apply Weakens.varAtOrAbove
    have member : indexLt cutoff (succ index) ∈ premises := by
      rw [← premisesEq]
      simp [indexLt, succ]
    simpa [JudgmentMeaning, indexLt] using
      premiseSound (indexLt cutoff (succ index)) member

private theorem weakenConst_application_sound
    (ruleInstance : RuleInstance) (premises : List Pattern)
    (conclusion : Pattern)
    (application : RuleApplication definition ruleInstance premises conclusion)
    (lookup : definition.1.lookupRule? ruleInstance.ruleId =
      some weakenConstRule) :
    JudgmentMeaning conclusion := by
  have executable := instantiateRule?_eq_some_iff_application.mpr application
  cases application with
  | intro rule actualLookup argumentsValid sideConditionsValid
      premisesInstantiate conclusionInstantiates =>
    have ruleEq : rule = weakenConstRule := by
      rw [actualLookup] at lookup
      exact Option.some.inj lookup
    subst rule
    obtain ⟨cutoff, name, argumentsEq⟩ := argumentsValidAt_two_shape (by
      simpa [weakenConstRule, rule, formal] using argumentsValid)
    simp only [instantiateRule?] at executable
    rw [argumentsEq] at executable
    simp [actualLookup, weakenConstRule, rule, formal, m, weakensAt, tmConst,
      argumentsValidAt, instantiateSchemas?, instantiateSchema?,
      instantiateSchemasAt?, instantiateSchemaAt?, lookupArgumentAt?]
      at executable
    rcases executable with ⟨_, _, conclusionEq⟩
    rw [← conclusionEq]
    simp only [JudgmentMeaning]
    exact Weakens.const cutoff name

private theorem weakenHead_application_sound
    (ruleInstance : RuleInstance) (premises : List Pattern)
    (conclusion : Pattern)
    (application : RuleApplication definition ruleInstance premises conclusion)
    (lookup : definition.1.lookupRule? ruleInstance.ruleId =
      some weakenHeadRule) :
    JudgmentMeaning conclusion := by
  have executable := instantiateRule?_eq_some_iff_application.mpr application
  cases application with
  | intro rule actualLookup argumentsValid sideConditionsValid
      premisesInstantiate conclusionInstantiates =>
    have ruleEq : rule = weakenHeadRule := by
      rw [actualLookup] at lookup
      exact Option.some.inj lookup
    subst rule
    obtain ⟨cutoff, head, argumentsEq⟩ := argumentsValidAt_two_shape (by
      simpa [weakenHeadRule, rule, formal] using argumentsValid)
    simp only [instantiateRule?] at executable
    rw [argumentsEq] at executable
    simp [actualLookup, weakenHeadRule, rule, formal, m, weakensAt, tmHead,
      argumentsValidAt, instantiateSchemas?, instantiateSchema?,
      instantiateSchemasAt?, instantiateSchemaAt?, lookupArgumentAt?]
      at executable
    rcases executable with ⟨_, _, conclusionEq⟩
    rw [← conclusionEq]
    simp only [JudgmentMeaning]
    exact Weakens.head cutoff head

private theorem weakenPi_application_sound
    (ruleInstance : RuleInstance) (premises : List Pattern)
    (conclusion : Pattern)
    (application : RuleApplication definition ruleInstance premises conclusion)
    (lookup : definition.1.lookupRule? ruleInstance.ruleId = some weakenPiRule)
    (premiseSound : ∀ premise ∈ premises, JudgmentMeaning premise) :
    JudgmentMeaning conclusion := by
  have executable := instantiateRule?_eq_some_iff_application.mpr application
  cases application with
  | intro rule actualLookup argumentsValid sideConditionsValid
      premisesInstantiate conclusionInstantiates =>
    have ruleEq : rule = weakenPiRule := by
      rw [actualLookup] at lookup
      exact Option.some.inj lookup
    subst rule
    obtain ⟨cutoff, domain, body, domainResult, bodyResult, argumentsEq⟩ :=
      argumentsValidAt_five_shape (by
        simpa [weakenPiRule, rule, formal] using argumentsValid)
    simp only [instantiateRule?] at executable
    rw [argumentsEq] at executable
    simp [actualLookup, weakenPiRule, rule, formal, m, weakensAt, tmPi, succ,
      argumentsValidAt, instantiateSchemas?, instantiateSchema?,
      instantiateSchemasAt?, instantiateSchemaAt?, lookupArgumentAt?]
      at executable
    rcases executable with ⟨_, premisesEq, conclusionEq⟩
    rw [← conclusionEq]
    simp only [JudgmentMeaning]
    apply Weakens.pi
    · have member : weakensAt cutoff domain domainResult ∈ premises := by
        rw [← premisesEq]
        simp [weakensAt]
      simpa [JudgmentMeaning, weakensAt] using
        premiseSound (weakensAt cutoff domain domainResult) member
    · have member : weakensAt (succ cutoff) body bodyResult ∈ premises := by
        rw [← premisesEq]
        simp [weakensAt, succ]
      simpa [JudgmentMeaning, weakensAt] using
        premiseSound (weakensAt (succ cutoff) body bodyResult) member

private theorem weakenSigma_application_sound
    (ruleInstance : RuleInstance) (premises : List Pattern)
    (conclusion : Pattern)
    (application : RuleApplication definition ruleInstance premises conclusion)
    (lookup : definition.1.lookupRule? ruleInstance.ruleId =
      some weakenSigmaRule)
    (premiseSound : ∀ premise ∈ premises, JudgmentMeaning premise) :
    JudgmentMeaning conclusion := by
  have executable := instantiateRule?_eq_some_iff_application.mpr application
  cases application with
  | intro rule actualLookup argumentsValid sideConditionsValid
      premisesInstantiate conclusionInstantiates =>
    have ruleEq : rule = weakenSigmaRule := by
      rw [actualLookup] at lookup
      exact Option.some.inj lookup
    subst rule
    obtain ⟨cutoff, domain, body, domainResult, bodyResult, argumentsEq⟩ :=
      argumentsValidAt_five_shape (by
        simpa [weakenSigmaRule, rule, formal] using argumentsValid)
    simp only [instantiateRule?] at executable
    rw [argumentsEq] at executable
    simp [actualLookup, weakenSigmaRule, rule, formal, m, weakensAt, tmSigma,
      succ, argumentsValidAt, instantiateSchemas?, instantiateSchema?,
      instantiateSchemasAt?, instantiateSchemaAt?, lookupArgumentAt?]
      at executable
    rcases executable with ⟨_, premisesEq, conclusionEq⟩
    rw [← conclusionEq]
    simp only [JudgmentMeaning]
    apply Weakens.sigma
    · have member : weakensAt cutoff domain domainResult ∈ premises := by
        rw [← premisesEq]
        simp [weakensAt]
      simpa [JudgmentMeaning, weakensAt] using
        premiseSound (weakensAt cutoff domain domainResult) member
    · have member : weakensAt (succ cutoff) body bodyResult ∈ premises := by
        rw [← premisesEq]
        simp [weakensAt, succ]
      simpa [JudgmentMeaning, weakensAt] using
        premiseSound (weakensAt (succ cutoff) body bodyResult) member

private theorem weakenId_application_sound
    (ruleInstance : RuleInstance) (premises : List Pattern)
    (conclusion : Pattern)
    (application : RuleApplication definition ruleInstance premises conclusion)
    (lookup : definition.1.lookupRule? ruleInstance.ruleId = some weakenIdRule)
    (premiseSound : ∀ premise ∈ premises, JudgmentMeaning premise) :
    JudgmentMeaning conclusion := by
  have executable := instantiateRule?_eq_some_iff_application.mpr application
  cases application with
  | intro rule actualLookup argumentsValid sideConditionsValid
      premisesInstantiate conclusionInstantiates =>
    have ruleEq : rule = weakenIdRule := by
      rw [actualLookup] at lookup
      exact Option.some.inj lookup
    subst rule
    obtain ⟨cutoff, type, left, right, typeResult, leftResult, rightResult,
      argumentsEq⟩ := argumentsValidAt_seven_shape (by
        simpa [weakenIdRule, rule, formal] using argumentsValid)
    simp only [instantiateRule?] at executable
    rw [argumentsEq] at executable
    simp [actualLookup, weakenIdRule, rule, formal, m, weakensAt, tmId,
      argumentsValidAt, instantiateSchemas?, instantiateSchema?,
      instantiateSchemasAt?, instantiateSchemaAt?, lookupArgumentAt?]
      at executable
    rcases executable with ⟨_, premisesEq, conclusionEq⟩
    rw [← conclusionEq]
    simp only [JudgmentMeaning]
    apply Weakens.id
    · have member : weakensAt cutoff type typeResult ∈ premises := by
        rw [← premisesEq]
        simp [weakensAt]
      simpa [JudgmentMeaning, weakensAt] using
        premiseSound (weakensAt cutoff type typeResult) member
    · have member : weakensAt cutoff left leftResult ∈ premises := by
        rw [← premisesEq]
        simp [weakensAt]
      simpa [JudgmentMeaning, weakensAt] using
        premiseSound (weakensAt cutoff left leftResult) member
    · have member : weakensAt cutoff right rightResult ∈ premises := by
        rw [← premisesEq]
        simp [weakensAt]
      simpa [JudgmentMeaning, weakensAt] using
        premiseSound (weakensAt cutoff right rightResult) member

private theorem weakenLam_application_sound
    (ruleInstance : RuleInstance) (premises : List Pattern)
    (conclusion : Pattern)
    (application : RuleApplication definition ruleInstance premises conclusion)
    (lookup : definition.1.lookupRule? ruleInstance.ruleId = some weakenLamRule)
    (premiseSound : ∀ premise ∈ premises, JudgmentMeaning premise) :
    JudgmentMeaning conclusion := by
  have executable := instantiateRule?_eq_some_iff_application.mpr application
  cases application with
  | intro rule actualLookup argumentsValid sideConditionsValid
      premisesInstantiate conclusionInstantiates =>
    have ruleEq : rule = weakenLamRule := by
      rw [actualLookup] at lookup
      exact Option.some.inj lookup
    subst rule
    obtain ⟨cutoff, body, bodyResult, argumentsEq⟩ :=
      argumentsValidAt_three_shape (by
        simpa [weakenLamRule, rule, formal] using argumentsValid)
    simp only [instantiateRule?] at executable
    rw [argumentsEq] at executable
    simp [actualLookup, weakenLamRule, rule, formal, m, weakensAt, tmLam, succ,
      argumentsValidAt, instantiateSchemas?, instantiateSchema?,
      instantiateSchemasAt?, instantiateSchemaAt?, lookupArgumentAt?]
      at executable
    rcases executable with ⟨_, premisesEq, conclusionEq⟩
    rw [← conclusionEq]
    simp only [JudgmentMeaning]
    apply Weakens.lam
    have member : weakensAt (succ cutoff) body bodyResult ∈ premises := by
      rw [← premisesEq]
      simp [weakensAt, succ]
    simpa [JudgmentMeaning, weakensAt] using
      premiseSound (weakensAt (succ cutoff) body bodyResult) member

private theorem weakenApp_application_sound
    (ruleInstance : RuleInstance) (premises : List Pattern)
    (conclusion : Pattern)
    (application : RuleApplication definition ruleInstance premises conclusion)
    (lookup : definition.1.lookupRule? ruleInstance.ruleId = some weakenAppRule)
    (premiseSound : ∀ premise ∈ premises, JudgmentMeaning premise) :
    JudgmentMeaning conclusion := by
  have executable := instantiateRule?_eq_some_iff_application.mpr application
  cases application with
  | intro rule actualLookup argumentsValid sideConditionsValid
      premisesInstantiate conclusionInstantiates =>
    have ruleEq : rule = weakenAppRule := by
      rw [actualLookup] at lookup
      exact Option.some.inj lookup
    subst rule
    obtain ⟨cutoff, function, argument, functionResult, argumentResult,
      argumentsEq⟩ := argumentsValidAt_five_shape (by
        simpa [weakenAppRule, rule, formal] using argumentsValid)
    simp only [instantiateRule?] at executable
    rw [argumentsEq] at executable
    simp [actualLookup, weakenAppRule, rule, formal, m, weakensAt, tmApp,
      argumentsValidAt, instantiateSchemas?, instantiateSchema?,
      instantiateSchemasAt?, instantiateSchemaAt?, lookupArgumentAt?]
      at executable
    rcases executable with ⟨_, premisesEq, conclusionEq⟩
    rw [← conclusionEq]
    simp only [JudgmentMeaning]
    apply Weakens.app
    · have member : weakensAt cutoff function functionResult ∈ premises := by
        rw [← premisesEq]
        simp [weakensAt]
      simpa [JudgmentMeaning, weakensAt] using
        premiseSound (weakensAt cutoff function functionResult) member
    · have member : weakensAt cutoff argument argumentResult ∈ premises := by
        rw [← premisesEq]
        simp [weakensAt]
      simpa [JudgmentMeaning, weakensAt] using
        premiseSound (weakensAt cutoff argument argumentResult) member

private theorem weakenPair_application_sound
    (ruleInstance : RuleInstance) (premises : List Pattern)
    (conclusion : Pattern)
    (application : RuleApplication definition ruleInstance premises conclusion)
    (lookup : definition.1.lookupRule? ruleInstance.ruleId = some weakenPairRule)
    (premiseSound : ∀ premise ∈ premises, JudgmentMeaning premise) :
    JudgmentMeaning conclusion := by
  have executable := instantiateRule?_eq_some_iff_application.mpr application
  cases application with
  | intro rule actualLookup argumentsValid sideConditionsValid
      premisesInstantiate conclusionInstantiates =>
    have ruleEq : rule = weakenPairRule := by
      rw [actualLookup] at lookup
      exact Option.some.inj lookup
    subst rule
    obtain ⟨cutoff, first, second, firstResult, secondResult, argumentsEq⟩ :=
      argumentsValidAt_five_shape (by
        simpa [weakenPairRule, rule, formal] using argumentsValid)
    simp only [instantiateRule?] at executable
    rw [argumentsEq] at executable
    simp [actualLookup, weakenPairRule, rule, formal, m, weakensAt, tmPair,
      argumentsValidAt, instantiateSchemas?, instantiateSchema?,
      instantiateSchemasAt?, instantiateSchemaAt?, lookupArgumentAt?]
      at executable
    rcases executable with ⟨_, premisesEq, conclusionEq⟩
    rw [← conclusionEq]
    simp only [JudgmentMeaning]
    apply Weakens.pair
    · have member : weakensAt cutoff first firstResult ∈ premises := by
        rw [← premisesEq]
        simp [weakensAt]
      simpa [JudgmentMeaning, weakensAt] using
        premiseSound (weakensAt cutoff first firstResult) member
    · have member : weakensAt cutoff second secondResult ∈ premises := by
        rw [← premisesEq]
        simp [weakensAt]
      simpa [JudgmentMeaning, weakensAt] using
        premiseSound (weakensAt cutoff second secondResult) member

private theorem weakenFst_application_sound
    (ruleInstance : RuleInstance) (premises : List Pattern)
    (conclusion : Pattern)
    (application : RuleApplication definition ruleInstance premises conclusion)
    (lookup : definition.1.lookupRule? ruleInstance.ruleId = some weakenFstRule)
    (premiseSound : ∀ premise ∈ premises, JudgmentMeaning premise) :
    JudgmentMeaning conclusion := by
  have executable := instantiateRule?_eq_some_iff_application.mpr application
  cases application with
  | intro rule actualLookup argumentsValid sideConditionsValid
      premisesInstantiate conclusionInstantiates =>
    have ruleEq : rule = weakenFstRule := by
      rw [actualLookup] at lookup
      exact Option.some.inj lookup
    subst rule
    obtain ⟨cutoff, pair, pairResult, argumentsEq⟩ :=
      argumentsValidAt_three_shape (by
        simpa [weakenFstRule, rule, formal] using argumentsValid)
    simp only [instantiateRule?] at executable
    rw [argumentsEq] at executable
    simp [actualLookup, weakenFstRule, rule, formal, m, weakensAt, tmFst,
      argumentsValidAt, instantiateSchemas?, instantiateSchema?,
      instantiateSchemasAt?, instantiateSchemaAt?, lookupArgumentAt?]
      at executable
    rcases executable with ⟨_, premisesEq, conclusionEq⟩
    rw [← conclusionEq]
    simp only [JudgmentMeaning]
    apply Weakens.fst
    have member : weakensAt cutoff pair pairResult ∈ premises := by
      rw [← premisesEq]
      simp [weakensAt]
    simpa [JudgmentMeaning, weakensAt] using
      premiseSound (weakensAt cutoff pair pairResult) member

private theorem weakenSnd_application_sound
    (ruleInstance : RuleInstance) (premises : List Pattern)
    (conclusion : Pattern)
    (application : RuleApplication definition ruleInstance premises conclusion)
    (lookup : definition.1.lookupRule? ruleInstance.ruleId = some weakenSndRule)
    (premiseSound : ∀ premise ∈ premises, JudgmentMeaning premise) :
    JudgmentMeaning conclusion := by
  have executable := instantiateRule?_eq_some_iff_application.mpr application
  cases application with
  | intro rule actualLookup argumentsValid sideConditionsValid
      premisesInstantiate conclusionInstantiates =>
    have ruleEq : rule = weakenSndRule := by
      rw [actualLookup] at lookup
      exact Option.some.inj lookup
    subst rule
    obtain ⟨cutoff, pair, pairResult, argumentsEq⟩ :=
      argumentsValidAt_three_shape (by
        simpa [weakenSndRule, rule, formal] using argumentsValid)
    simp only [instantiateRule?] at executable
    rw [argumentsEq] at executable
    simp [actualLookup, weakenSndRule, rule, formal, m, weakensAt, tmSnd,
      argumentsValidAt, instantiateSchemas?, instantiateSchema?,
      instantiateSchemasAt?, instantiateSchemaAt?, lookupArgumentAt?]
      at executable
    rcases executable with ⟨_, premisesEq, conclusionEq⟩
    rw [← conclusionEq]
    simp only [JudgmentMeaning]
    apply Weakens.snd
    have member : weakensAt cutoff pair pairResult ∈ premises := by
      rw [← premisesEq]
      simp [weakensAt]
    simpa [JudgmentMeaning, weakensAt] using
      premiseSound (weakensAt cutoff pair pairResult) member

private theorem weakenRefl_application_sound
    (ruleInstance : RuleInstance) (premises : List Pattern)
    (conclusion : Pattern)
    (application : RuleApplication definition ruleInstance premises conclusion)
    (lookup : definition.1.lookupRule? ruleInstance.ruleId = some weakenReflRule)
    (premiseSound : ∀ premise ∈ premises, JudgmentMeaning premise) :
    JudgmentMeaning conclusion := by
  have executable := instantiateRule?_eq_some_iff_application.mpr application
  cases application with
  | intro rule actualLookup argumentsValid sideConditionsValid
      premisesInstantiate conclusionInstantiates =>
    have ruleEq : rule = weakenReflRule := by
      rw [actualLookup] at lookup
      exact Option.some.inj lookup
    subst rule
    obtain ⟨cutoff, term, termResult, argumentsEq⟩ :=
      argumentsValidAt_three_shape (by
        simpa [weakenReflRule, rule, formal] using argumentsValid)
    simp only [instantiateRule?] at executable
    rw [argumentsEq] at executable
    simp [actualLookup, weakenReflRule, rule, formal, m, weakensAt, tmRefl,
      argumentsValidAt, instantiateSchemas?, instantiateSchema?,
      instantiateSchemasAt?, instantiateSchemaAt?, lookupArgumentAt?]
      at executable
    rcases executable with ⟨_, premisesEq, conclusionEq⟩
    rw [← conclusionEq]
    simp only [JudgmentMeaning]
    apply Weakens.refl
    have member : weakensAt cutoff term termResult ∈ premises := by
      rw [← premisesEq]
      simp [weakensAt]
    simpa [JudgmentMeaning, weakensAt] using
      premiseSound (weakensAt cutoff term termResult) member

private theorem substVarEqual_application_sound
    (ruleInstance : RuleInstance) (premises : List Pattern)
    (conclusion : Pattern)
    (application : RuleApplication definition ruleInstance premises conclusion)
    (lookup : definition.1.lookupRule? ruleInstance.ruleId =
      some substVarEqualRule) :
    JudgmentMeaning conclusion := by
  have executable := instantiateRule?_eq_some_iff_application.mpr application
  cases application with
  | intro rule actualLookup argumentsValid sideConditionsValid
      premisesInstantiate conclusionInstantiates =>
    have ruleEq : rule = substVarEqualRule := by
      rw [actualLookup] at lookup
      exact Option.some.inj lookup
    subst rule
    obtain ⟨index, replacement, argumentsEq⟩ := argumentsValidAt_two_shape (by
      simpa [substVarEqualRule, rule, formal] using argumentsValid)
    simp only [instantiateRule?] at executable
    rw [argumentsEq] at executable
    simp [actualLookup, substVarEqualRule, rule, formal, m, substitutesAt,
      tmVar, argumentsValidAt, instantiateSchemas?, instantiateSchema?,
      instantiateSchemasAt?, instantiateSchemaAt?, lookupArgumentAt?]
      at executable
    rcases executable with ⟨_, _, conclusionEq⟩
    rw [← conclusionEq]
    simp only [JudgmentMeaning]
    exact Substitutes.varEqual index replacement

private theorem substVarBelow_application_sound
    (ruleInstance : RuleInstance) (premises : List Pattern)
    (conclusion : Pattern)
    (application : RuleApplication definition ruleInstance premises conclusion)
    (lookup : definition.1.lookupRule? ruleInstance.ruleId =
      some substVarBelowRule)
    (premiseSound : ∀ premise ∈ premises, JudgmentMeaning premise) :
    JudgmentMeaning conclusion := by
  have executable := instantiateRule?_eq_some_iff_application.mpr application
  cases application with
  | intro rule actualLookup argumentsValid sideConditionsValid
      premisesInstantiate conclusionInstantiates =>
    have ruleEq : rule = substVarBelowRule := by
      rw [actualLookup] at lookup
      exact Option.some.inj lookup
    subst rule
    obtain ⟨index, replacement, variableTerm, argumentsEq⟩ :=
      argumentsValidAt_three_shape (by
        simpa [substVarBelowRule, rule, formal] using argumentsValid)
    simp only [instantiateRule?] at executable
    rw [argumentsEq] at executable
    simp [actualLookup, substVarBelowRule, rule, formal, m, indexLt,
      substitutesAt, tmVar, argumentsValidAt, instantiateSchemas?,
      instantiateSchema?, instantiateSchemasAt?, instantiateSchemaAt?,
      lookupArgumentAt?] at executable
    rcases executable with ⟨_, premisesEq, conclusionEq⟩
    rw [← conclusionEq]
    simp only [JudgmentMeaning]
    apply Substitutes.varBelow
    have member : indexLt variableTerm index ∈ premises := by
      rw [← premisesEq]
      simp [indexLt]
    simpa [JudgmentMeaning, indexLt] using
      premiseSound (indexLt variableTerm index) member

private theorem substVarAbove_application_sound
    (ruleInstance : RuleInstance) (premises : List Pattern)
    (conclusion : Pattern)
    (application : RuleApplication definition ruleInstance premises conclusion)
    (lookup : definition.1.lookupRule? ruleInstance.ruleId =
      some substVarAboveRule)
    (premiseSound : ∀ premise ∈ premises, JudgmentMeaning premise) :
    JudgmentMeaning conclusion := by
  have executable := instantiateRule?_eq_some_iff_application.mpr application
  cases application with
  | intro rule actualLookup argumentsValid sideConditionsValid
      premisesInstantiate conclusionInstantiates =>
    have ruleEq : rule = substVarAboveRule := by
      rw [actualLookup] at lookup
      exact Option.some.inj lookup
    subst rule
    obtain ⟨index, replacement, predecessor, argumentsEq⟩ :=
      argumentsValidAt_three_shape (by
        simpa [substVarAboveRule, rule, formal] using argumentsValid)
    simp only [instantiateRule?] at executable
    rw [argumentsEq] at executable
    simp [actualLookup, substVarAboveRule, rule, formal, m, indexLt,
      substitutesAt, tmVar, succ, argumentsValidAt, instantiateSchemas?,
      instantiateSchema?, instantiateSchemasAt?, instantiateSchemaAt?,
      lookupArgumentAt?] at executable
    rcases executable with ⟨_, premisesEq, conclusionEq⟩
    rw [← conclusionEq]
    simp only [JudgmentMeaning]
    apply Substitutes.varAbove
    have member : indexLt index (succ predecessor) ∈ premises := by
      rw [← premisesEq]
      simp [indexLt, succ]
    simpa [JudgmentMeaning, indexLt] using
      premiseSound (indexLt index (succ predecessor)) member

private theorem substConst_application_sound
    (ruleInstance : RuleInstance) (premises : List Pattern)
    (conclusion : Pattern)
    (application : RuleApplication definition ruleInstance premises conclusion)
    (lookup : definition.1.lookupRule? ruleInstance.ruleId = some substConstRule) :
    JudgmentMeaning conclusion := by
  have executable := instantiateRule?_eq_some_iff_application.mpr application
  cases application with
  | intro rule actualLookup argumentsValid sideConditionsValid
      premisesInstantiate conclusionInstantiates =>
    have ruleEq : rule = substConstRule := by
      rw [actualLookup] at lookup
      exact Option.some.inj lookup
    subst rule
    obtain ⟨index, replacement, name, argumentsEq⟩ :=
      argumentsValidAt_three_shape (by
        simpa [substConstRule, rule, formal] using argumentsValid)
    simp only [instantiateRule?] at executable
    rw [argumentsEq] at executable
    simp [actualLookup, substConstRule, rule, formal, m, substitutesAt, tmConst,
      argumentsValidAt, instantiateSchemas?, instantiateSchema?,
      instantiateSchemasAt?, instantiateSchemaAt?, lookupArgumentAt?]
      at executable
    rcases executable with ⟨_, _, conclusionEq⟩
    rw [← conclusionEq]
    simp only [JudgmentMeaning]
    exact Substitutes.const index replacement name

private theorem substHead_application_sound
    (ruleInstance : RuleInstance) (premises : List Pattern)
    (conclusion : Pattern)
    (application : RuleApplication definition ruleInstance premises conclusion)
    (lookup : definition.1.lookupRule? ruleInstance.ruleId = some substHeadRule) :
    JudgmentMeaning conclusion := by
  have executable := instantiateRule?_eq_some_iff_application.mpr application
  cases application with
  | intro rule actualLookup argumentsValid sideConditionsValid
      premisesInstantiate conclusionInstantiates =>
    have ruleEq : rule = substHeadRule := by
      rw [actualLookup] at lookup
      exact Option.some.inj lookup
    subst rule
    obtain ⟨index, replacement, head, argumentsEq⟩ :=
      argumentsValidAt_three_shape (by
        simpa [substHeadRule, rule, formal] using argumentsValid)
    simp only [instantiateRule?] at executable
    rw [argumentsEq] at executable
    simp [actualLookup, substHeadRule, rule, formal, m, substitutesAt, tmHead,
      argumentsValidAt, instantiateSchemas?, instantiateSchema?,
      instantiateSchemasAt?, instantiateSchemaAt?, lookupArgumentAt?]
      at executable
    rcases executable with ⟨_, _, conclusionEq⟩
    rw [← conclusionEq]
    simp only [JudgmentMeaning]
    exact Substitutes.head index replacement head

private theorem substPi_application_sound
    (ruleInstance : RuleInstance) (premises : List Pattern)
    (conclusion : Pattern)
    (application : RuleApplication definition ruleInstance premises conclusion)
    (lookup : definition.1.lookupRule? ruleInstance.ruleId = some substPiRule)
    (premiseSound : ∀ premise ∈ premises, JudgmentMeaning premise) :
    JudgmentMeaning conclusion := by
  have executable := instantiateRule?_eq_some_iff_application.mpr application
  cases application with
  | intro rule actualLookup argumentsValid sideConditionsValid
      premisesInstantiate conclusionInstantiates =>
    have ruleEq : rule = substPiRule := by
      rw [actualLookup] at lookup
      exact Option.some.inj lookup
    subst rule
    obtain ⟨index, replacement, domain, body, domainResult,
      liftedReplacement, bodyResult, argumentsEq⟩ :=
      argumentsValidAt_seven_shape (by
        simpa [substPiRule, rule, formal] using argumentsValid)
    simp only [instantiateRule?] at executable
    rw [argumentsEq] at executable
    simp [actualLookup, substPiRule, rule, formal, m, substitutesAt, weakensAt,
      tmPi, zero, succ, argumentsValidAt, instantiateSchemas?,
      instantiateSchema?, instantiateSchemasAt?, instantiateSchemaAt?,
      lookupArgumentAt?] at executable
    rcases executable with ⟨_, premisesEq, conclusionEq⟩
    rw [← conclusionEq]
    simp only [JudgmentMeaning]
    apply Substitutes.pi
    · have member :
          substitutesAt index replacement domain domainResult ∈ premises := by
        rw [← premisesEq]
        simp [substitutesAt]
      simpa [JudgmentMeaning, substitutesAt] using
        premiseSound (substitutesAt index replacement domain domainResult) member
    · have member :
          weakensAt zero replacement liftedReplacement ∈ premises := by
        rw [← premisesEq]
        simp [weakensAt, zero]
      simpa [JudgmentMeaning, weakensAt] using
        premiseSound (weakensAt zero replacement liftedReplacement) member
    · have member : substitutesAt (succ index) liftedReplacement body bodyResult ∈
          premises := by
        rw [← premisesEq]
        simp [substitutesAt, succ]
      simpa [JudgmentMeaning, substitutesAt] using premiseSound
        (substitutesAt (succ index) liftedReplacement body bodyResult) member

private theorem substSigma_application_sound
    (ruleInstance : RuleInstance) (premises : List Pattern)
    (conclusion : Pattern)
    (application : RuleApplication definition ruleInstance premises conclusion)
    (lookup : definition.1.lookupRule? ruleInstance.ruleId = some substSigmaRule)
    (premiseSound : ∀ premise ∈ premises, JudgmentMeaning premise) :
    JudgmentMeaning conclusion := by
  have executable := instantiateRule?_eq_some_iff_application.mpr application
  cases application with
  | intro rule actualLookup argumentsValid sideConditionsValid
      premisesInstantiate conclusionInstantiates =>
    have ruleEq : rule = substSigmaRule := by
      rw [actualLookup] at lookup
      exact Option.some.inj lookup
    subst rule
    obtain ⟨index, replacement, domain, body, domainResult,
      liftedReplacement, bodyResult, argumentsEq⟩ :=
      argumentsValidAt_seven_shape (by
        simpa [substSigmaRule, rule, formal] using argumentsValid)
    simp only [instantiateRule?] at executable
    rw [argumentsEq] at executable
    simp [actualLookup, substSigmaRule, rule, formal, m, substitutesAt,
      weakensAt, tmSigma, zero, succ, argumentsValidAt, instantiateSchemas?,
      instantiateSchema?, instantiateSchemasAt?, instantiateSchemaAt?,
      lookupArgumentAt?] at executable
    rcases executable with ⟨_, premisesEq, conclusionEq⟩
    rw [← conclusionEq]
    simp only [JudgmentMeaning]
    apply Substitutes.sigma
    · have member :
          substitutesAt index replacement domain domainResult ∈ premises := by
        rw [← premisesEq]
        simp [substitutesAt]
      simpa [JudgmentMeaning, substitutesAt] using
        premiseSound (substitutesAt index replacement domain domainResult) member
    · have member :
          weakensAt zero replacement liftedReplacement ∈ premises := by
        rw [← premisesEq]
        simp [weakensAt, zero]
      simpa [JudgmentMeaning, weakensAt] using
        premiseSound (weakensAt zero replacement liftedReplacement) member
    · have member : substitutesAt (succ index) liftedReplacement body bodyResult ∈
          premises := by
        rw [← premisesEq]
        simp [substitutesAt, succ]
      simpa [JudgmentMeaning, substitutesAt] using premiseSound
        (substitutesAt (succ index) liftedReplacement body bodyResult) member

private theorem substId_application_sound
    (ruleInstance : RuleInstance) (premises : List Pattern)
    (conclusion : Pattern)
    (application : RuleApplication definition ruleInstance premises conclusion)
    (lookup : definition.1.lookupRule? ruleInstance.ruleId = some substIdRule)
    (premiseSound : ∀ premise ∈ premises, JudgmentMeaning premise) :
    JudgmentMeaning conclusion := by
  have executable := instantiateRule?_eq_some_iff_application.mpr application
  cases application with
  | intro rule actualLookup argumentsValid sideConditionsValid
      premisesInstantiate conclusionInstantiates =>
    have ruleEq : rule = substIdRule := by
      rw [actualLookup] at lookup
      exact Option.some.inj lookup
    subst rule
    obtain ⟨index, replacement, type, left, right, typeResult, leftResult,
      rightResult, argumentsEq⟩ := argumentsValidAt_eight_shape (by
        simpa [substIdRule, rule, formal] using argumentsValid)
    simp only [instantiateRule?] at executable
    rw [argumentsEq] at executable
    simp [actualLookup, substIdRule, rule, formal, m, substitutesAt, tmId,
      argumentsValidAt, instantiateSchemas?, instantiateSchema?,
      instantiateSchemasAt?, instantiateSchemaAt?, lookupArgumentAt?]
      at executable
    rcases executable with ⟨_, premisesEq, conclusionEq⟩
    rw [← conclusionEq]
    simp only [JudgmentMeaning]
    apply Substitutes.id
    · have member : substitutesAt index replacement type typeResult ∈ premises := by
        rw [← premisesEq]
        simp [substitutesAt]
      simpa [JudgmentMeaning, substitutesAt] using
        premiseSound (substitutesAt index replacement type typeResult) member
    · have member : substitutesAt index replacement left leftResult ∈ premises := by
        rw [← premisesEq]
        simp [substitutesAt]
      simpa [JudgmentMeaning, substitutesAt] using
        premiseSound (substitutesAt index replacement left leftResult) member
    · have member : substitutesAt index replacement right rightResult ∈
          premises := by
        rw [← premisesEq]
        simp [substitutesAt]
      simpa [JudgmentMeaning, substitutesAt] using
        premiseSound (substitutesAt index replacement right rightResult) member

private theorem substLam_application_sound
    (ruleInstance : RuleInstance) (premises : List Pattern)
    (conclusion : Pattern)
    (application : RuleApplication definition ruleInstance premises conclusion)
    (lookup : definition.1.lookupRule? ruleInstance.ruleId = some substLamRule)
    (premiseSound : ∀ premise ∈ premises, JudgmentMeaning premise) :
    JudgmentMeaning conclusion := by
  have executable := instantiateRule?_eq_some_iff_application.mpr application
  cases application with
  | intro rule actualLookup argumentsValid sideConditionsValid
      premisesInstantiate conclusionInstantiates =>
    have ruleEq : rule = substLamRule := by
      rw [actualLookup] at lookup
      exact Option.some.inj lookup
    subst rule
    obtain ⟨index, replacement, body, liftedReplacement, bodyResult,
      argumentsEq⟩ := argumentsValidAt_five_shape (by
        simpa [substLamRule, rule, formal] using argumentsValid)
    simp only [instantiateRule?] at executable
    rw [argumentsEq] at executable
    simp [actualLookup, substLamRule, rule, formal, m, substitutesAt, weakensAt,
      tmLam, zero, succ, argumentsValidAt, instantiateSchemas?,
      instantiateSchema?, instantiateSchemasAt?, instantiateSchemaAt?,
      lookupArgumentAt?] at executable
    rcases executable with ⟨_, premisesEq, conclusionEq⟩
    rw [← conclusionEq]
    simp only [JudgmentMeaning]
    apply Substitutes.lam
    · have member : weakensAt zero replacement liftedReplacement ∈ premises := by
        rw [← premisesEq]
        simp [weakensAt, zero]
      simpa [JudgmentMeaning, weakensAt] using
        premiseSound (weakensAt zero replacement liftedReplacement) member
    · have member : substitutesAt (succ index) liftedReplacement body bodyResult ∈
          premises := by
        rw [← premisesEq]
        simp [substitutesAt, succ]
      simpa [JudgmentMeaning, substitutesAt] using premiseSound
        (substitutesAt (succ index) liftedReplacement body bodyResult) member

private theorem substApp_application_sound
    (ruleInstance : RuleInstance) (premises : List Pattern)
    (conclusion : Pattern)
    (application : RuleApplication definition ruleInstance premises conclusion)
    (lookup : definition.1.lookupRule? ruleInstance.ruleId = some substAppRule)
    (premiseSound : ∀ premise ∈ premises, JudgmentMeaning premise) :
    JudgmentMeaning conclusion := by
  have executable := instantiateRule?_eq_some_iff_application.mpr application
  cases application with
  | intro rule actualLookup argumentsValid sideConditionsValid
      premisesInstantiate conclusionInstantiates =>
    have ruleEq : rule = substAppRule := by
      rw [actualLookup] at lookup
      exact Option.some.inj lookup
    subst rule
    obtain ⟨index, replacement, function, argument, functionResult,
      argumentResult, argumentsEq⟩ := argumentsValidAt_six_shape (by
        simpa [substAppRule, rule, formal] using argumentsValid)
    simp only [instantiateRule?] at executable
    rw [argumentsEq] at executable
    simp [actualLookup, substAppRule, rule, formal, m, substitutesAt, tmApp,
      argumentsValidAt, instantiateSchemas?, instantiateSchema?,
      instantiateSchemasAt?, instantiateSchemaAt?, lookupArgumentAt?]
      at executable
    rcases executable with ⟨_, premisesEq, conclusionEq⟩
    rw [← conclusionEq]
    simp only [JudgmentMeaning]
    apply Substitutes.app
    · have member :
          substitutesAt index replacement function functionResult ∈ premises := by
        rw [← premisesEq]
        simp [substitutesAt]
      simpa [JudgmentMeaning, substitutesAt] using premiseSound
        (substitutesAt index replacement function functionResult) member
    · have member :
          substitutesAt index replacement argument argumentResult ∈ premises := by
        rw [← premisesEq]
        simp [substitutesAt]
      simpa [JudgmentMeaning, substitutesAt] using premiseSound
        (substitutesAt index replacement argument argumentResult) member

private theorem substPair_application_sound
    (ruleInstance : RuleInstance) (premises : List Pattern)
    (conclusion : Pattern)
    (application : RuleApplication definition ruleInstance premises conclusion)
    (lookup : definition.1.lookupRule? ruleInstance.ruleId = some substPairRule)
    (premiseSound : ∀ premise ∈ premises, JudgmentMeaning premise) :
    JudgmentMeaning conclusion := by
  have executable := instantiateRule?_eq_some_iff_application.mpr application
  cases application with
  | intro rule actualLookup argumentsValid sideConditionsValid
      premisesInstantiate conclusionInstantiates =>
    have ruleEq : rule = substPairRule := by
      rw [actualLookup] at lookup
      exact Option.some.inj lookup
    subst rule
    obtain ⟨index, replacement, first, second, firstResult, secondResult,
      argumentsEq⟩ := argumentsValidAt_six_shape (by
        simpa [substPairRule, rule, formal] using argumentsValid)
    simp only [instantiateRule?] at executable
    rw [argumentsEq] at executable
    simp [actualLookup, substPairRule, rule, formal, m, substitutesAt, tmPair,
      argumentsValidAt, instantiateSchemas?, instantiateSchema?,
      instantiateSchemasAt?, instantiateSchemaAt?, lookupArgumentAt?]
      at executable
    rcases executable with ⟨_, premisesEq, conclusionEq⟩
    rw [← conclusionEq]
    simp only [JudgmentMeaning]
    apply Substitutes.pair
    · have member : substitutesAt index replacement first firstResult ∈
          premises := by
        rw [← premisesEq]
        simp [substitutesAt]
      simpa [JudgmentMeaning, substitutesAt] using
        premiseSound (substitutesAt index replacement first firstResult) member
    · have member : substitutesAt index replacement second secondResult ∈
          premises := by
        rw [← premisesEq]
        simp [substitutesAt]
      simpa [JudgmentMeaning, substitutesAt] using
        premiseSound (substitutesAt index replacement second secondResult) member

private theorem substFst_application_sound
    (ruleInstance : RuleInstance) (premises : List Pattern)
    (conclusion : Pattern)
    (application : RuleApplication definition ruleInstance premises conclusion)
    (lookup : definition.1.lookupRule? ruleInstance.ruleId = some substFstRule)
    (premiseSound : ∀ premise ∈ premises, JudgmentMeaning premise) :
    JudgmentMeaning conclusion := by
  have executable := instantiateRule?_eq_some_iff_application.mpr application
  cases application with
  | intro rule actualLookup argumentsValid sideConditionsValid
      premisesInstantiate conclusionInstantiates =>
    have ruleEq : rule = substFstRule := by
      rw [actualLookup] at lookup
      exact Option.some.inj lookup
    subst rule
    obtain ⟨index, replacement, pair, pairResult, argumentsEq⟩ :=
      argumentsValidAt_four_shape (by
        simpa [substFstRule, rule, formal] using argumentsValid)
    simp only [instantiateRule?] at executable
    rw [argumentsEq] at executable
    simp [actualLookup, substFstRule, rule, formal, m, substitutesAt, tmFst,
      argumentsValidAt, instantiateSchemas?, instantiateSchema?,
      instantiateSchemasAt?, instantiateSchemaAt?, lookupArgumentAt?]
      at executable
    rcases executable with ⟨_, premisesEq, conclusionEq⟩
    rw [← conclusionEq]
    simp only [JudgmentMeaning]
    apply Substitutes.fst
    have member : substitutesAt index replacement pair pairResult ∈ premises := by
      rw [← premisesEq]
      simp [substitutesAt]
    simpa [JudgmentMeaning, substitutesAt] using
      premiseSound (substitutesAt index replacement pair pairResult) member

private theorem substSnd_application_sound
    (ruleInstance : RuleInstance) (premises : List Pattern)
    (conclusion : Pattern)
    (application : RuleApplication definition ruleInstance premises conclusion)
    (lookup : definition.1.lookupRule? ruleInstance.ruleId = some substSndRule)
    (premiseSound : ∀ premise ∈ premises, JudgmentMeaning premise) :
    JudgmentMeaning conclusion := by
  have executable := instantiateRule?_eq_some_iff_application.mpr application
  cases application with
  | intro rule actualLookup argumentsValid sideConditionsValid
      premisesInstantiate conclusionInstantiates =>
    have ruleEq : rule = substSndRule := by
      rw [actualLookup] at lookup
      exact Option.some.inj lookup
    subst rule
    obtain ⟨index, replacement, pair, pairResult, argumentsEq⟩ :=
      argumentsValidAt_four_shape (by
        simpa [substSndRule, rule, formal] using argumentsValid)
    simp only [instantiateRule?] at executable
    rw [argumentsEq] at executable
    simp [actualLookup, substSndRule, rule, formal, m, substitutesAt, tmSnd,
      argumentsValidAt, instantiateSchemas?, instantiateSchema?,
      instantiateSchemasAt?, instantiateSchemaAt?, lookupArgumentAt?]
      at executable
    rcases executable with ⟨_, premisesEq, conclusionEq⟩
    rw [← conclusionEq]
    simp only [JudgmentMeaning]
    apply Substitutes.snd
    have member : substitutesAt index replacement pair pairResult ∈ premises := by
      rw [← premisesEq]
      simp [substitutesAt]
    simpa [JudgmentMeaning, substitutesAt] using
      premiseSound (substitutesAt index replacement pair pairResult) member

private theorem substRefl_application_sound
    (ruleInstance : RuleInstance) (premises : List Pattern)
    (conclusion : Pattern)
    (application : RuleApplication definition ruleInstance premises conclusion)
    (lookup : definition.1.lookupRule? ruleInstance.ruleId = some substReflRule)
    (premiseSound : ∀ premise ∈ premises, JudgmentMeaning premise) :
    JudgmentMeaning conclusion := by
  have executable := instantiateRule?_eq_some_iff_application.mpr application
  cases application with
  | intro rule actualLookup argumentsValid sideConditionsValid
      premisesInstantiate conclusionInstantiates =>
    have ruleEq : rule = substReflRule := by
      rw [actualLookup] at lookup
      exact Option.some.inj lookup
    subst rule
    obtain ⟨index, replacement, term, termResult, argumentsEq⟩ :=
      argumentsValidAt_four_shape (by
        simpa [substReflRule, rule, formal] using argumentsValid)
    simp only [instantiateRule?] at executable
    rw [argumentsEq] at executable
    simp [actualLookup, substReflRule, rule, formal, m, substitutesAt, tmRefl,
      argumentsValidAt, instantiateSchemas?, instantiateSchema?,
      instantiateSchemasAt?, instantiateSchemaAt?, lookupArgumentAt?]
      at executable
    rcases executable with ⟨_, premisesEq, conclusionEq⟩
    rw [← conclusionEq]
    simp only [JudgmentMeaning]
    apply Substitutes.refl
    have member : substitutesAt index replacement term termResult ∈ premises := by
      rw [← premisesEq]
      simp [substitutesAt]
    simpa [JudgmentMeaning, substitutesAt] using
      premiseSound (substitutesAt index replacement term termResult) member

private theorem rootBeta_application_sound
    (ruleInstance : RuleInstance) (premises : List Pattern)
    (conclusion : Pattern)
    (application : RuleApplication definition ruleInstance premises conclusion)
    (lookup : definition.1.lookupRule? ruleInstance.ruleId = some rootBetaRule)
    (premiseSound : ∀ premise ∈ premises, JudgmentMeaning premise) :
    JudgmentMeaning conclusion := by
  have executable := instantiateRule?_eq_some_iff_application.mpr application
  cases application with
  | intro rule actualLookup argumentsValid sideConditionsValid
      premisesInstantiate conclusionInstantiates =>
    have ruleEq : rule = rootBetaRule := by
      rw [actualLookup] at lookup
      exact Option.some.inj lookup
    subst rule
    obtain ⟨body, argument, result, argumentsEq⟩ :=
      argumentsValidAt_three_shape (by
        simpa [rootBetaRule, rule, formal] using argumentsValid)
    simp only [instantiateRule?] at executable
    rw [argumentsEq] at executable
    simp [actualLookup, rootBetaRule, rule, formal, m, substitutesAt, rootBeta,
      tmApp, tmLam, zero, argumentsValidAt, instantiateSchemas?,
      instantiateSchema?, instantiateSchemasAt?, instantiateSchemaAt?,
      lookupArgumentAt?] at executable
    rcases executable with ⟨_, premisesEq, conclusionEq⟩
    rw [← conclusionEq]
    simp only [JudgmentMeaning]
    apply RootBeta.intro
    have member : substitutesAt zero argument body result ∈ premises := by
      rw [← premisesEq]
      simp [substitutesAt, zero]
    simpa [JudgmentMeaning, substitutesAt] using
      premiseSound (substitutesAt zero argument body result) member

/-- Every one of the thirty authored rule schemas preserves the independent
relational meaning. -/
theorem ruleApplication_sound
    (ruleInstance : RuleInstance) (premises : List Pattern)
    (conclusion : Pattern)
    (application : RuleApplication definition ruleInstance premises conclusion)
    (premiseSound : ∀ premise ∈ premises, JudgmentMeaning premise) :
    JudgmentMeaning conclusion := by
  cases application with
  | intro rule lookup argumentsValid sideConditionsValid
      premisesInstantiate conclusionInstantiates =>
    have application' :
        RuleApplication definition ruleInstance premises conclusion :=
      .intro rule lookup argumentsValid sideConditionsValid
        premisesInstantiate conclusionInstantiates
    have ruleMember : rule ∈ allRules := by
      have stored := List.mem_of_find?_eq_some lookup
      simpa [definition, substitutionExtension,
        ValidatedCalculusLanguageExtension.target, substitutionDelta,
        CalculusLanguageExtension.apply,
        DeclarationAwareDataLanguage.checked,
        DeclarationAwareDataLanguage.definition] using stored
    simp only [allRules, List.mem_cons, List.mem_nil_iff, or_false] at ruleMember
    rcases ruleMember with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ltZeroSucc_application_sound ruleInstance premises conclusion
        application' lookup
    · exact ltSuccSucc_application_sound ruleInstance premises conclusion
        application' lookup premiseSound
    · exact weakenVarBelow_application_sound ruleInstance premises conclusion
        application' lookup premiseSound
    · exact weakenVarAtOrAbove_application_sound ruleInstance premises conclusion
        application' lookup premiseSound
    · exact weakenConst_application_sound ruleInstance premises conclusion
        application' lookup
    · exact weakenHead_application_sound ruleInstance premises conclusion
        application' lookup
    · exact weakenPi_application_sound ruleInstance premises conclusion
        application' lookup premiseSound
    · exact weakenSigma_application_sound ruleInstance premises conclusion
        application' lookup premiseSound
    · exact weakenId_application_sound ruleInstance premises conclusion
        application' lookup premiseSound
    · exact weakenLam_application_sound ruleInstance premises conclusion
        application' lookup premiseSound
    · exact weakenApp_application_sound ruleInstance premises conclusion
        application' lookup premiseSound
    · exact weakenPair_application_sound ruleInstance premises conclusion
        application' lookup premiseSound
    · exact weakenFst_application_sound ruleInstance premises conclusion
        application' lookup premiseSound
    · exact weakenSnd_application_sound ruleInstance premises conclusion
        application' lookup premiseSound
    · exact weakenRefl_application_sound ruleInstance premises conclusion
        application' lookup premiseSound
    · exact substVarEqual_application_sound ruleInstance premises conclusion
        application' lookup
    · exact substVarBelow_application_sound ruleInstance premises conclusion
        application' lookup premiseSound
    · exact substVarAbove_application_sound ruleInstance premises conclusion
        application' lookup premiseSound
    · exact substConst_application_sound ruleInstance premises conclusion
        application' lookup
    · exact substHead_application_sound ruleInstance premises conclusion
        application' lookup
    · exact substPi_application_sound ruleInstance premises conclusion
        application' lookup premiseSound
    · exact substSigma_application_sound ruleInstance premises conclusion
        application' lookup premiseSound
    · exact substId_application_sound ruleInstance premises conclusion
        application' lookup premiseSound
    · exact substLam_application_sound ruleInstance premises conclusion
        application' lookup premiseSound
    · exact substApp_application_sound ruleInstance premises conclusion
        application' lookup premiseSound
    · exact substPair_application_sound ruleInstance premises conclusion
        application' lookup premiseSound
    · exact substFst_application_sound ruleInstance premises conclusion
        application' lookup premiseSound
    · exact substSnd_application_sound ruleInstance premises conclusion
        application' lookup premiseSound
    · exact substRefl_application_sound ruleInstance premises conclusion
        application' lookup premiseSound
    · exact rootBeta_application_sound ruleInstance premises conclusion
        application' lookup premiseSound

/-- Every declarative derivation has the independent relational meaning of its
goal. -/
theorem derivation_sound {goal : Pattern}
    (derivation : Derivation definition goal) : JudgmentMeaning goal :=
  derivation.sound_of_ruleApplications JudgmentMeaning ruleApplication_sound

/-- End-to-end reflection from the executable generic checker into the
independent relational semantics. -/
theorem checkRaw_relational_sound {goal : Pattern} {proof : RawProof}
    (accepted : checkRaw definition goal proof = true) : JudgmentMeaning goal := by
  obtain ⟨derivation⟩ := checkRaw_soundness accepted
  exact derivation_sound derivation

/-! ## Canonical image is contained in the relational semantics -/

theorem indexLt_encode {left right : Nat} (less : left < right) :
    IndexLt (encodeNat left) (encodeNat right) := by
  induction left generalizing right with
  | zero =>
      cases right with
      | zero => omega
      | succ right => exact .zeroSucc (encodeNat right)
  | succ left leftIH =>
      cases right with
      | zero => omega
      | succ right => exact .succSucc (leftIH (by omega))

@[simp] theorem indexLt_encode_iff {left right : Nat} :
    IndexLt (encodeNat left) (encodeNat right) ↔ left < right :=
  ⟨IndexLt.reflect_encode, indexLt_encode⟩

theorem weakens_encode (cutoff : Nat) (term : RawTerm) :
    Weakens (encodeNat cutoff) (encodeRaw term)
      (encodeRaw (weakenRaw cutoff term)) := by
  induction term generalizing cutoff with
  | var index =>
      by_cases below : index < cutoff
      · simpa [below] using Weakens.varBelow (indexLt_encode below)
      · have above : cutoff < index + 1 := by omega
        simpa [below, encodeNat, succ] using
          Weakens.varAtOrAbove (indexLt_encode above)
  | const name => exact .const _ _
  | head head => exact .head _ _
  | pi domain body domainIH bodyIH =>
      exact .pi (domainIH cutoff) (bodyIH (cutoff + 1))
  | sigma domain body domainIH bodyIH =>
      exact .sigma (domainIH cutoff) (bodyIH (cutoff + 1))
  | id type left right typeIH leftIH rightIH =>
      exact .id (typeIH cutoff) (leftIH cutoff) (rightIH cutoff)
  | lam body bodyIH => exact .lam (bodyIH (cutoff + 1))
  | app function argument functionIH argumentIH =>
      exact .app (functionIH cutoff) (argumentIH cutoff)
  | pair first second firstIH secondIH =>
      exact .pair (firstIH cutoff) (secondIH cutoff)
  | fst pair pairIH => exact .fst (pairIH cutoff)
  | snd pair pairIH => exact .snd (pairIH cutoff)
  | refl term termIH => exact .refl (termIH cutoff)

theorem substitutes_encode (index : Nat) (replacement term : RawTerm) :
    Substitutes (encodeNat index) (encodeRaw replacement) (encodeRaw term)
      (encodeRaw (substituteRaw index replacement term)) := by
  induction term generalizing index replacement with
  | var variableIndex =>
      by_cases equal : variableIndex = index
      · subst variableIndex
        simpa using Substitutes.varEqual (encodeNat index) (encodeRaw replacement)
      · by_cases below : variableIndex < index
        · simpa [equal, below] using Substitutes.varBelow (indexLt_encode below)
        · have above : index < variableIndex := by omega
          have positive : 0 < variableIndex := by omega
          have encoded : succ (encodeNat (variableIndex - 1)) =
              encodeNat variableIndex := by
            have valueEq : variableIndex = (variableIndex - 1) + 1 := by omega
            rw [valueEq]
            rfl
          have predecessorOrder :
              IndexLt (encodeNat index) (succ (encodeNat (variableIndex - 1))) := by
            rw [encoded]
            exact indexLt_encode above
          have step := Substitutes.varAbove
            (replacement := encodeRaw replacement) predecessorOrder
          simpa [equal, below, encoded] using step
  | const name => exact .const _ _ _
  | head head => exact .head _ _ _
  | pi domain body domainIH bodyIH =>
      exact .pi (domainIH index replacement) (weakens_encode 0 replacement)
        (bodyIH (index + 1) (weakenRaw 0 replacement))
  | sigma domain body domainIH bodyIH =>
      exact .sigma (domainIH index replacement) (weakens_encode 0 replacement)
        (bodyIH (index + 1) (weakenRaw 0 replacement))
  | id type left right typeIH leftIH rightIH =>
      exact .id (typeIH index replacement) (leftIH index replacement)
        (rightIH index replacement)
  | lam body bodyIH =>
      exact .lam (weakens_encode 0 replacement)
        (bodyIH (index + 1) (weakenRaw 0 replacement))
  | app function argument functionIH argumentIH =>
      exact .app (functionIH index replacement) (argumentIH index replacement)
  | pair first second firstIH secondIH =>
      exact .pair (firstIH index replacement) (secondIH index replacement)
  | fst pair pairIH => exact .fst (pairIH index replacement)
  | snd pair pairIH => exact .snd (pairIH index replacement)
  | refl term termIH => exact .refl (termIH index replacement)

theorem rootBeta_encode (body argument : RawTerm) :
    RootBeta (tmApp (tmLam (encodeRaw body)) (encodeRaw argument))
      (encodeRaw (substituteRaw 0 argument body)) :=
  .intro (substitutes_encode 0 argument body)

/-! ## Functional reflection on the canonical image -/

private theorem Weakens.functional_aux
    {cutoff firstSource firstTarget : Pattern}
    (first : Weakens cutoff firstSource firstTarget) :
    ∀ {secondSource secondTarget : Pattern}, firstSource = secondSource →
      Weakens cutoff secondSource secondTarget → firstTarget = secondTarget := by
  induction first with
  | varBelow less =>
      intro secondSource secondTarget sourceEq second
      cases second <;>
        simp_all [tmVar, tmConst, tmHead, tmPi, tmSigma, tmId, tmLam,
          tmApp, tmPair, tmFst, tmSnd, tmRefl]
      exfalso
      exact IndexLt.no_two_step_to_succ less (by assumption)
  | varAtOrAbove less =>
      intro secondSource secondTarget sourceEq second
      cases second <;>
        simp_all [tmVar, tmConst, tmHead, tmPi, tmSigma, tmId, tmLam,
          tmApp, tmPair, tmFst, tmSnd, tmRefl]
      exfalso
      exact IndexLt.no_two_step_to_succ (by assumption) less
  | const cutoff name =>
      intro secondSource secondTarget sourceEq second
      cases second <;>
        simp_all [tmVar, tmConst, tmHead, tmPi, tmSigma, tmId, tmLam,
          tmApp, tmPair, tmFst, tmSnd, tmRefl]
  | head cutoff head =>
      intro secondSource secondTarget sourceEq second
      cases second <;>
        simp_all [tmVar, tmConst, tmHead, tmPi, tmSigma, tmId, tmLam,
          tmApp, tmPair, tmFst, tmSnd, tmRefl]
  | pi domain body domainIH bodyIH =>
      intro secondSource secondTarget sourceEq second
      cases second <;>
        simp_all [tmVar, tmConst, tmHead, tmPi, tmSigma, tmId, tmLam,
          tmApp, tmPair, tmFst, tmSnd, tmRefl]
      constructor <;> solve_by_elim
  | sigma domain body domainIH bodyIH =>
      intro secondSource secondTarget sourceEq second
      cases second <;>
        simp_all [tmVar, tmConst, tmHead, tmPi, tmSigma, tmId, tmLam,
          tmApp, tmPair, tmFst, tmSnd, tmRefl]
      constructor <;> solve_by_elim
  | id type left right typeIH leftIH rightIH =>
      intro secondSource secondTarget sourceEq second
      cases second <;>
        simp_all [tmVar, tmConst, tmHead, tmPi, tmSigma, tmId, tmLam,
          tmApp, tmPair, tmFst, tmSnd, tmRefl]
      constructor
      · solve_by_elim
      · constructor <;> solve_by_elim
  | lam body bodyIH =>
      intro secondSource secondTarget sourceEq second
      cases second <;>
        simp_all [tmVar, tmConst, tmHead, tmPi, tmSigma, tmId, tmLam,
          tmApp, tmPair, tmFst, tmSnd, tmRefl]
      solve_by_elim
  | app function argument functionIH argumentIH =>
      intro secondSource secondTarget sourceEq second
      cases second <;>
        simp_all [tmVar, tmConst, tmHead, tmPi, tmSigma, tmId, tmLam,
          tmApp, tmPair, tmFst, tmSnd, tmRefl]
      constructor <;> solve_by_elim
  | pair first second firstIH secondIH =>
      intro secondSource secondTarget sourceEq relation
      cases relation <;>
        simp_all [tmVar, tmConst, tmHead, tmPi, tmSigma, tmId, tmLam,
          tmApp, tmPair, tmFst, tmSnd, tmRefl]
      constructor <;> solve_by_elim
  | fst pair pairIH =>
      intro secondSource secondTarget sourceEq second
      cases second <;>
        simp_all [tmVar, tmConst, tmHead, tmPi, tmSigma, tmId, tmLam,
          tmApp, tmPair, tmFst, tmSnd, tmRefl]
      solve_by_elim
  | snd pair pairIH =>
      intro secondSource secondTarget sourceEq second
      cases second <;>
        simp_all [tmVar, tmConst, tmHead, tmPi, tmSigma, tmId, tmLam,
          tmApp, tmPair, tmFst, tmSnd, tmRefl]
      solve_by_elim
  | refl term termIH =>
      intro secondSource secondTarget sourceEq second
      cases second <;>
        simp_all [tmVar, tmConst, tmHead, tmPi, tmSigma, tmId, tmLam,
          tmApp, tmPair, tmFst, tmSnd, tmRefl]
      solve_by_elim

/-- Authored weakening is deterministic even before restricting to the
canonical image.  The only potentially overlapping variable rules would
require two strict unary-depth inequalities inside an interval of width one. -/
theorem Weakens.functional {cutoff source firstTarget : Pattern}
    (first : Weakens cutoff source firstTarget) :
    ∀ {secondTarget : Pattern}, Weakens cutoff source secondTarget →
      firstTarget = secondTarget := by
  intro secondTarget second
  exact first.functional_aux rfl second

/-- On canonical natural and term encodings, relational weakening has exactly
the independently computed target. -/
theorem Weakens.reflect_encoded (cutoff : Nat) (term : RawTerm)
    {target : Pattern}
    (relation : Weakens (encodeNat cutoff) (encodeRaw term) target) :
    target = encodeRaw (weakenRaw cutoff term) :=
  relation.functional (weakens_encode cutoff term)

private theorem binderTargetsUnique
    {index replacement domain body domainResult₁ liftedReplacement₁
      bodyResult₁ domainResult₂ liftedReplacement₂ bodyResult₂ : Pattern}
    (liftFirst : Weakens zero replacement liftedReplacement₁)
    (domainUnique : ∀ {source target}, domain = source →
      Substitutes index replacement source target → domainResult₁ = target)
    (bodyUnique : ∀ {source target}, body = source →
      Substitutes (succ index) liftedReplacement₁ source target →
        bodyResult₁ = target)
    (domainSecond : Substitutes index replacement domain domainResult₂)
    (liftSecond : Weakens zero replacement liftedReplacement₂)
    (bodySecond : Substitutes (succ index) liftedReplacement₂ body bodyResult₂) :
    domainResult₁ = domainResult₂ ∧ bodyResult₁ = bodyResult₂ := by
  have liftedEq := liftFirst.functional liftSecond
  subst liftedReplacement₂
  exact ⟨domainUnique rfl domainSecond, bodyUnique rfl bodySecond⟩

private theorem liftedBodyTargetUnique
    {index replacement body liftedReplacement₁ bodyResult₁
      liftedReplacement₂ bodyResult₂ : Pattern}
    (liftFirst : Weakens zero replacement liftedReplacement₁)
    (bodyUnique : ∀ {source target}, body = source →
      Substitutes (succ index) liftedReplacement₁ source target →
        bodyResult₁ = target)
    (liftSecond : Weakens zero replacement liftedReplacement₂)
    (bodySecond : Substitutes (succ index) liftedReplacement₂ body bodyResult₂) :
    bodyResult₁ = bodyResult₂ := by
  have liftedEq := liftFirst.functional liftSecond
  subst liftedReplacement₂
  exact bodyUnique rfl bodySecond

private theorem Substitutes.functional_aux
    {index replacement firstSource firstTarget : Pattern}
    (first : Substitutes index replacement firstSource firstTarget) :
    ∀ {secondSource secondTarget : Pattern}, firstSource = secondSource →
      Substitutes index replacement secondSource secondTarget →
        firstTarget = secondTarget := by
  induction first with
  | varEqual index replacement =>
      intro secondSource secondTarget sourceEq second
      cases second <;>
        simp_all [tmVar, tmConst, tmHead, tmPi, tmSigma, tmId, tmLam,
          tmApp, tmPair, tmFst, tmSnd, tmRefl, succ]
      all_goals
        exfalso
        exact IndexLt.irrefl _ (by assumption)
  | varBelow less =>
      intro secondSource secondTarget sourceEq second
      cases second <;>
        simp_all [tmVar, tmConst, tmHead, tmPi, tmSigma, tmId, tmLam,
          tmApp, tmPair, tmFst, tmSnd, tmRefl, succ]
      all_goals
        exfalso
        first
        | exact IndexLt.irrefl _ (by assumption)
        | exact IndexLt.asymm less (by assumption)
  | varAbove less =>
      intro secondSource secondTarget sourceEq second
      cases second <;>
        simp_all [tmVar, tmConst, tmHead, tmPi, tmSigma, tmId, tmLam,
          tmApp, tmPair, tmFst, tmSnd, tmRefl, succ]
      all_goals
        exfalso
        first
        | exact IndexLt.irrefl _ (by assumption)
        | exact IndexLt.asymm less (by assumption)
  | const index replacement name =>
      intro secondSource secondTarget sourceEq second
      cases second <;>
        simp_all [tmVar, tmConst, tmHead, tmPi, tmSigma, tmId, tmLam,
          tmApp, tmPair, tmFst, tmSnd, tmRefl]
  | head index replacement head =>
      intro secondSource secondTarget sourceEq second
      cases second <;>
        simp_all [tmVar, tmConst, tmHead, tmPi, tmSigma, tmId, tmLam,
          tmApp, tmPair, tmFst, tmSnd, tmRefl]
  | pi domain lift body domainIH bodyIH =>
      intro secondSource secondTarget sourceEq second
      cases second <;>
        simp_all [tmVar, tmConst, tmHead, tmPi, tmSigma, tmId, tmLam,
          tmApp, tmPair, tmFst, tmSnd, tmRefl]
      exact binderTargetsUnique lift domainIH bodyIH
        (by assumption) (by assumption) (by assumption)
  | sigma domain lift body domainIH bodyIH =>
      intro secondSource secondTarget sourceEq second
      cases second <;>
        simp_all [tmVar, tmConst, tmHead, tmPi, tmSigma, tmId, tmLam,
          tmApp, tmPair, tmFst, tmSnd, tmRefl]
      exact binderTargetsUnique lift domainIH bodyIH
        (by assumption) (by assumption) (by assumption)
  | id type left right typeIH leftIH rightIH =>
      intro secondSource secondTarget sourceEq second
      cases second <;>
        simp_all [tmVar, tmConst, tmHead, tmPi, tmSigma, tmId, tmLam,
          tmApp, tmPair, tmFst, tmSnd, tmRefl]
      constructor
      · solve_by_elim
      · constructor <;> solve_by_elim
  | lam lift body bodyIH =>
      intro secondSource secondTarget sourceEq second
      cases second <;>
        simp_all [tmVar, tmConst, tmHead, tmPi, tmSigma, tmId, tmLam,
          tmApp, tmPair, tmFst, tmSnd, tmRefl]
      exact liftedBodyTargetUnique lift bodyIH
        (by assumption) (by assumption)
  | app function argument functionIH argumentIH =>
      intro secondSource secondTarget sourceEq second
      cases second <;>
        simp_all [tmVar, tmConst, tmHead, tmPi, tmSigma, tmId, tmLam,
          tmApp, tmPair, tmFst, tmSnd, tmRefl]
      constructor <;> solve_by_elim
  | pair first second firstIH secondIH =>
      intro secondSource secondTarget sourceEq relation
      cases relation <;>
        simp_all [tmVar, tmConst, tmHead, tmPi, tmSigma, tmId, tmLam,
          tmApp, tmPair, tmFst, tmSnd, tmRefl]
      constructor <;> solve_by_elim
  | fst pair pairIH =>
      intro secondSource secondTarget sourceEq second
      cases second <;>
        simp_all [tmVar, tmConst, tmHead, tmPi, tmSigma, tmId, tmLam,
          tmApp, tmPair, tmFst, tmSnd, tmRefl]
      solve_by_elim
  | snd pair pairIH =>
      intro secondSource secondTarget sourceEq second
      cases second <;>
        simp_all [tmVar, tmConst, tmHead, tmPi, tmSigma, tmId, tmLam,
          tmApp, tmPair, tmFst, tmSnd, tmRefl]
      solve_by_elim
  | refl term termIH =>
      intro secondSource secondTarget sourceEq second
      cases second <;>
        simp_all [tmVar, tmConst, tmHead, tmPi, tmSigma, tmId, tmLam,
          tmApp, tmPair, tmFst, tmSnd, tmRefl]
      solve_by_elim

/-- Authored capture-avoiding substitution is functional.  In the binder
cases this theorem reuses weakening functionality to identify the independently
derived lifted replacements before comparing the recursive body results. -/
theorem Substitutes.functional {index replacement source firstTarget : Pattern}
    (first : Substitutes index replacement source firstTarget) :
    ∀ {secondTarget : Pattern},
      Substitutes index replacement source secondTarget →
        firstTarget = secondTarget := by
  intro secondTarget second
  exact first.functional_aux rfl second

/-- On canonical natural and term encodings, relational substitution has
exactly the independently computed target. -/
theorem Substitutes.reflect_encoded (index : Nat) (replacement term : RawTerm)
    {target : Pattern}
    (relation : Substitutes (encodeNat index) (encodeRaw replacement)
      (encodeRaw term) target) :
    target = encodeRaw (substituteRaw index replacement term) :=
  relation.functional (substitutes_encode index replacement term)

private theorem RootBeta.functional_aux
    {firstSource firstTarget : Pattern}
    (first : RootBeta firstSource firstTarget) :
    ∀ {secondSource secondTarget : Pattern}, firstSource = secondSource →
      RootBeta secondSource secondTarget → firstTarget = secondTarget := by
  cases first with
  | @intro body argument result firstSubstitution =>
      intro secondSource secondTarget sourceEq second
      cases second with
      | @intro secondBody secondArgument secondResult secondSubstitution =>
          simp [tmApp, tmLam] at sourceEq
          rcases sourceEq with ⟨rfl, rfl⟩
          exact firstSubstitution.functional secondSubstitution

/-- Root beta is functional because its substitution relation is functional. -/
theorem RootBeta.functional {source firstTarget : Pattern}
    (first : RootBeta source firstTarget) :
    ∀ {secondTarget : Pattern}, RootBeta source secondTarget →
      firstTarget = secondTarget := by
  intro secondTarget second
  exact first.functional_aux rfl second

/-- On the canonical image, relational root beta computes the independent
capture-avoiding substitution result. -/
theorem RootBeta.reflect_encoded (body argument : RawTerm) {target : Pattern}
    (relation : RootBeta
      (tmApp (tmLam (encodeRaw body)) (encodeRaw argument)) target) :
    target = encodeRaw (substituteRaw 0 argument body) :=
  relation.functional (rootBeta_encode body argument)

/-! ## Arbitrary accepted artifacts reflect the functional semantics -/

theorem checkRaw_weakening_reflects (cutoff : Nat) (term : RawTerm)
    {target : Pattern} {proof : RawProof}
    (accepted : checkRaw definition
      (weakensAt (encodeNat cutoff) (encodeRaw term) target) proof = true) :
    target = encodeRaw (weakenRaw cutoff term) := by
  have meaning := checkRaw_relational_sound accepted
  apply Weakens.reflect_encoded cutoff term
  simpa [weakensAt, JudgmentMeaning] using meaning

theorem checkRaw_substitution_reflects
    (index : Nat) (replacement term : RawTerm)
    {target : Pattern} {proof : RawProof}
    (accepted : checkRaw definition
      (substitutesAt (encodeNat index) (encodeRaw replacement)
        (encodeRaw term) target) proof = true) :
    target = encodeRaw (substituteRaw index replacement term) := by
  have meaning := checkRaw_relational_sound accepted
  apply Substitutes.reflect_encoded index replacement term
  simpa [substitutesAt, JudgmentMeaning] using meaning

theorem checkRaw_beta_reflects (body argument : RawTerm)
    {target : Pattern} {proof : RawProof}
    (accepted : checkRaw definition
      (rootBeta (tmApp (tmLam (encodeRaw body)) (encodeRaw argument)) target)
        proof = true) :
    target = encodeRaw (substituteRaw 0 argument body) := by
  have meaning := checkRaw_relational_sound accepted
  apply RootBeta.reflect_encoded body argument
  simpa [rootBeta, JudgmentMeaning] using meaning

/-! ## Discriminating controls -/

/-- Weakening retains both occurrences of a duplicated pair. -/
theorem duplicate_pair_weakening_retains_multiplicity (cutoff : Nat)
    (term : RawTerm) :
    Weakens (encodeNat cutoff) (encodeRaw (.pair term term))
      (encodeRaw (.pair (weakenRaw cutoff term) (weakenRaw cutoff term))) := by
  simpa using weakens_encode cutoff (.pair term term)

/-- Irreflexivity is visible already on a concrete canonical numeral. -/
theorem two_lt_two_impossible :
    ¬ IndexLt (encodeNat 2) (encodeNat 2) :=
  IndexLt.irrefl _

/-! ## Axiom audit -/

#print axioms indexLt_encode
#print axioms weakens_encode
#print axioms substitutes_encode
#print axioms rootBeta_encode
#print axioms two_lt_two_impossible

end Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.DeclarationAwareSubstitutionReflection
