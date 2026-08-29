import Mettapedia.GSLT.LanguageDef.CertificateGSLT

/-!
# Open derivations for CertificateGSLTs

A closed `Derivation` records a proof with no hypotheses.  General
proof-definition interpretations need a stronger object: a derivation with
typed premise holes.  A source rule is interpreted by such an open derivation,
and composition plugs open derivations into those holes.

Premise holes are addressed by `Fin` positions in an ordered context.  Thus
two equal judgments at different positions remain different occurrences.  The
calculus below is proof relevant and supports genuine substitution laws; it
does not identify a shared premise occurrence with two copied derivation
trees.
-/

namespace Mettapedia.GSLT.LanguageDef.CertificateGSLT

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.InferenceChecker

mutual

/-- A derivation of `goal` from an ordered context of premise occurrences. -/
inductive OpenDerivation (definition : ValidatedCalculusLanguageDef)
    (context : List Pattern) : Pattern → Type where
  | assumption (index : Fin context.length) :
      OpenDerivation definition context (context.get index)
  | byRule (ruleInstance : RuleInstance) {premises : List Pattern}
      {conclusion : Pattern}
      (application :
        RuleApplication definition ruleInstance premises conclusion)
      (children : OpenDerivationList definition context premises) :
      OpenDerivation definition context conclusion

/-- Ordered open derivations for an ordered vector of rule premises. -/
inductive OpenDerivationList (definition : ValidatedCalculusLanguageDef)
    (context : List Pattern) : List Pattern → Type where
  | nil : OpenDerivationList definition context []
  | cons {premise : Pattern} {premises : List Pattern}
      (head : OpenDerivation definition context premise)
      (tail : OpenDerivationList definition context premises) :
      OpenDerivationList definition context (premise :: premises)

end

/-! ## Generic semantic interpretation -/

mutual

/-- An interpretation that holds for every context occurrence and is closed
under every admitted rule application holds for every open derivation. -/
theorem OpenDerivation.sound_of_ruleApplications
    {definition : ValidatedCalculusLanguageDef} {context : List Pattern}
    (meaning : Pattern → Prop)
    (ruleSound : ∀ ruleInstance premises conclusion,
      RuleApplication definition ruleInstance premises conclusion →
        (∀ premise ∈ premises, meaning premise) → meaning conclusion)
    (contextSound : ∀ premise ∈ context, meaning premise)
    {goal : Pattern} (derivation : OpenDerivation definition context goal) :
    meaning goal := by
  cases derivation with
  | assumption index =>
      exact contextSound (context.get index) (List.get_mem context index)
  | byRule ruleInstance application children =>
      exact ruleSound ruleInstance _ _ application
        (OpenDerivationList.all_meaning meaning ruleSound contextSound children)
termination_by sizeOf derivation

/-- Ordered open derivation lists satisfy an interpretation pointwise. -/
theorem OpenDerivationList.all_meaning
    {definition : ValidatedCalculusLanguageDef} {context : List Pattern}
    (meaning : Pattern → Prop)
    (ruleSound : ∀ ruleInstance premises conclusion,
      RuleApplication definition ruleInstance premises conclusion →
        (∀ premise ∈ premises, meaning premise) → meaning conclusion)
    (contextSound : ∀ premise ∈ context, meaning premise)
    {premises : List Pattern}
    (derivations : OpenDerivationList definition context premises) :
    ∀ premise ∈ premises, meaning premise := by
  cases derivations with
  | nil => simp
  | cons head tail =>
      intro premise membership
      simp only [List.mem_cons] at membership
      rcases membership with equality | membership
      · exact equality ▸
          OpenDerivation.sound_of_ruleApplications meaning ruleSound
            contextSound head
      · exact OpenDerivationList.all_meaning meaning ruleSound contextSound
          tail premise membership
termination_by sizeOf derivations

decreasing_by
  all_goals simp_all <;> omega

end

namespace OpenDerivationList

/-- Select the derivation at an ordered premise position. -/
def get {definition : ValidatedCalculusLanguageDef} {context goals : List Pattern} :
    OpenDerivationList definition context goals →
      (index : Fin goals.length) →
        OpenDerivation definition context (goals.get index)
  | .nil, index => Fin.elim0 index
  | .cons head tail, index =>
      Fin.cases head (fun tailIndex => tail.get tailIndex) index

/-- Build an ordered derivation vector from its position-indexed entries. -/
def ofFn {definition : ValidatedCalculusLanguageDef} {context : List Pattern} :
    (goals : List Pattern) →
      ((index : Fin goals.length) →
        OpenDerivation definition context (goals.get index)) →
      OpenDerivationList definition context goals
  | [], _ => .nil
  | _ :: _, entries =>
      .cons (entries ⟨0, Nat.zero_lt_succ _⟩)
        (ofFn _ fun index => entries index.succ)

@[simp] theorem get_ofFn
    {definition : ValidatedCalculusLanguageDef} {context goals : List Pattern}
    (entries : (index : Fin goals.length) →
      OpenDerivation definition context (goals.get index))
    (index : Fin goals.length) :
    (ofFn goals entries).get index = entries index := by
  induction goals with
  | nil => exact Fin.elim0 index
  | cons goal goals inductionHypothesis =>
      refine Fin.cases ?_ (fun tailIndex => ?_) index
      · rfl
      · exact inductionHypothesis (fun i => entries i.succ) tailIndex

end OpenDerivationList

mutual

/-- Number of primitive rule nodes in an open derivation.  Premise holes are
not charged as rule applications. -/
def OpenDerivation.ruleCount
    {definition : ValidatedCalculusLanguageDef} {context : List Pattern}
    {goal : Pattern} : OpenDerivation definition context goal → Nat
  | .assumption _ => 0
  | .byRule _ _ children => children.ruleCount + 1

/-- Total primitive rule nodes in an ordered derivation vector. -/
def OpenDerivationList.ruleCount
    {definition : ValidatedCalculusLanguageDef} {context goals : List Pattern} :
    OpenDerivationList definition context goals → Nat
  | .nil => 0
  | .cons head tail => head.ruleCount + tail.ruleCount

end

/-- The identity environment: each premise position refers to itself. -/
def assumptionEnvironment (definition : ValidatedCalculusLanguageDef)
    (context : List Pattern) :
    OpenDerivationList definition context context :=
  OpenDerivationList.ofFn context fun index => .assumption index

mutual

/-- Plug a derivation vector into every premise hole. -/
def OpenDerivation.bind
    {definition : ValidatedCalculusLanguageDef} {sourceContext targetContext : List Pattern}
    {goal : Pattern}
    (derivation : OpenDerivation definition sourceContext goal)
    (environment :
      OpenDerivationList definition targetContext sourceContext) :
    OpenDerivation definition targetContext goal :=
  match derivation with
  | .assumption index => environment.get index
  | .byRule ruleInstance application children =>
      .byRule ruleInstance application (children.bind environment)

/-- Plug an environment pointwise into an ordered derivation vector. -/
def OpenDerivationList.bind
    {definition : ValidatedCalculusLanguageDef} {sourceContext targetContext : List Pattern}
    {goals : List Pattern}
    (derivations : OpenDerivationList definition sourceContext goals)
    (environment :
      OpenDerivationList definition targetContext sourceContext) :
    OpenDerivationList definition targetContext goals :=
  match derivations with
  | .nil => .nil
  | .cons head tail =>
      .cons (head.bind environment) (tail.bind environment)

end

@[simp] theorem OpenDerivation.assumption_bind
    {definition : ValidatedCalculusLanguageDef} {sourceContext targetContext : List Pattern}
    (index : Fin sourceContext.length)
    (environment :
      OpenDerivationList definition targetContext sourceContext) :
    (OpenDerivation.assumption index).bind environment =
      environment.get index := rfl

mutual

/-- Substitution by the identity premise environment changes no derivation. -/
@[simp] theorem OpenDerivation.bind_assumptionEnvironment
    {definition : ValidatedCalculusLanguageDef} {context : List Pattern}
    {goal : Pattern} (derivation : OpenDerivation definition context goal) :
    derivation.bind (assumptionEnvironment definition context) = derivation := by
  cases derivation with
  | assumption index =>
      simp [OpenDerivation.bind, assumptionEnvironment]
  | byRule ruleInstance application children =>
      simp [OpenDerivation.bind,
        OpenDerivationList.bind_assumptionEnvironment children]

/-- Identity substitution acts pointwise on ordered derivation vectors. -/
@[simp] theorem OpenDerivationList.bind_assumptionEnvironment
    {definition : ValidatedCalculusLanguageDef} {context goals : List Pattern}
    (derivations : OpenDerivationList definition context goals) :
    derivations.bind (assumptionEnvironment definition context) = derivations := by
  cases derivations with
  | nil => rfl
  | cons head tail =>
      simp [OpenDerivationList.bind,
        OpenDerivation.bind_assumptionEnvironment head,
        OpenDerivationList.bind_assumptionEnvironment tail]

end

/-! The two unit laws are deliberately distinct.  Substitution by the
identity environment is a right unit for an open derivation; substituting any
environment into the vector of premise assumptions is the left unit. -/

theorem OpenDerivationList.ofFn_bind
    {definition : ValidatedCalculusLanguageDef}
    {sourceContext targetContext goals : List Pattern}
    (entries : (index : Fin goals.length) →
      OpenDerivation definition sourceContext (goals.get index))
    (environment :
      OpenDerivationList definition targetContext sourceContext) :
    (OpenDerivationList.ofFn goals entries).bind environment =
      OpenDerivationList.ofFn goals
        (fun index => (entries index).bind environment) := by
  induction goals with
  | nil => rfl
  | cons goal goals inductionHypothesis =>
      simp only [OpenDerivationList.ofFn, OpenDerivationList.bind]
      congr
      exact inductionHypothesis (fun index => entries index.succ)

@[simp] theorem OpenDerivationList.ofFn_get
    {definition : ValidatedCalculusLanguageDef} {context goals : List Pattern}
    (derivations : OpenDerivationList definition context goals) :
    OpenDerivationList.ofFn goals (fun index => derivations.get index) =
      derivations := by
  cases derivations with
  | nil => rfl
  | cons head tail =>
      simp only [OpenDerivationList.ofFn, OpenDerivationList.get]
      change OpenDerivationList.cons head
          (OpenDerivationList.ofFn _ fun index => tail.get index) =
        OpenDerivationList.cons head tail
      rw [OpenDerivationList.ofFn_get tail]

@[simp] theorem OpenDerivationList.assumptionEnvironment_bind
    {definition : ValidatedCalculusLanguageDef}
    {sourceContext targetContext : List Pattern}
    (environment :
      OpenDerivationList definition targetContext sourceContext) :
    (assumptionEnvironment definition sourceContext).bind environment =
      environment := by
  rw [assumptionEnvironment, OpenDerivationList.ofFn_bind]
  simpa only [OpenDerivation.bind] using
    OpenDerivationList.ofFn_get environment

mutual

/-- Plugging open derivations is associative. -/
theorem OpenDerivation.bind_assoc
    {definition : ValidatedCalculusLanguageDef}
    {firstContext secondContext thirdContext : List Pattern}
    {goal : Pattern}
    (derivation : OpenDerivation definition firstContext goal)
    (first : OpenDerivationList definition secondContext firstContext)
    (second : OpenDerivationList definition thirdContext secondContext) :
    (derivation.bind first).bind second =
      derivation.bind (first.bind second) := by
  cases derivation with
  | assumption index =>
      simp only [OpenDerivation.bind]
      exact (OpenDerivationList.get_bind first second index).symm
  | byRule ruleInstance application children =>
      simp [OpenDerivation.bind, OpenDerivationList.bind_assoc children first second]

/-- Associativity holds pointwise for ordered derivation vectors. -/
theorem OpenDerivationList.bind_assoc
    {definition : ValidatedCalculusLanguageDef}
    {firstContext secondContext thirdContext goals : List Pattern}
    (derivations : OpenDerivationList definition firstContext goals)
    (first : OpenDerivationList definition secondContext firstContext)
    (second : OpenDerivationList definition thirdContext secondContext) :
    (derivations.bind first).bind second =
      derivations.bind (first.bind second) := by
  cases derivations with
  | nil => rfl
  | cons head tail =>
      simp [OpenDerivationList.bind, OpenDerivation.bind_assoc head first second,
        OpenDerivationList.bind_assoc tail first second]

/-- Selecting an entry commutes with pointwise substitution. -/
theorem OpenDerivationList.get_bind
    {definition : ValidatedCalculusLanguageDef}
    {sourceContext targetContext goals : List Pattern}
    (derivations : OpenDerivationList definition sourceContext goals)
    (environment : OpenDerivationList definition targetContext sourceContext)
    (index : Fin goals.length) :
    (derivations.bind environment).get index =
      (derivations.get index).bind environment := by
  cases derivations with
  | nil => exact Fin.elim0 index
  | cons head tail =>
      refine Fin.cases ?_ (fun tailIndex => ?_) index
      · rfl
      · exact OpenDerivationList.get_bind tail environment tailIndex

end

mutual

/-- Regard a closed derivation as an open derivation in any premise context. -/
def OpenDerivation.ofClosed
    {definition : ValidatedCalculusLanguageDef} {context : List Pattern}
    {goal : Pattern} :
    Derivation definition goal → OpenDerivation definition context goal
  | .byRule ruleInstance application children =>
      .byRule ruleInstance application (OpenDerivationList.ofClosed children)

/-- Pointwise embedding of closed premise derivations. -/
def OpenDerivationList.ofClosed
    {definition : ValidatedCalculusLanguageDef} {context goals : List Pattern} :
    DerivationList definition goals →
      OpenDerivationList definition context goals
  | .nil => .nil
  | .cons head tail =>
      .cons (OpenDerivation.ofClosed head)
        (OpenDerivationList.ofClosed tail)

end

mutual

/-- An open derivation over the empty context is a closed derivation. -/
def OpenDerivation.close
    {definition : ValidatedCalculusLanguageDef} {goal : Pattern} :
    OpenDerivation definition [] goal → Derivation definition goal
  | .assumption index => Fin.elim0 index
  | .byRule ruleInstance application children =>
      .byRule ruleInstance application children.close

/-- Close an ordered vector whose open context is empty. -/
def OpenDerivationList.close
    {definition : ValidatedCalculusLanguageDef} {goals : List Pattern} :
    OpenDerivationList definition [] goals →
      DerivationList definition goals
  | .nil => .nil
  | .cons head tail => .cons head.close tail.close

end

mutual

@[simp] theorem OpenDerivation.close_ofClosed
    {definition : ValidatedCalculusLanguageDef} {goal : Pattern}
    (derivation : Derivation definition goal) :
    (OpenDerivation.ofClosed (context := []) derivation).close = derivation := by
  cases derivation with
  | byRule ruleInstance application children =>
      simp [OpenDerivation.ofClosed, OpenDerivation.close,
        OpenDerivationList.close_ofClosed children]

@[simp] theorem OpenDerivationList.close_ofClosed
    {definition : ValidatedCalculusLanguageDef} {goals : List Pattern}
    (derivations : DerivationList definition goals) :
    (OpenDerivationList.ofClosed (context := []) derivations).close = derivations := by
  cases derivations with
  | nil => rfl
  | cons head tail =>
      simp [OpenDerivationList.ofClosed, OpenDerivationList.close,
        OpenDerivation.close_ofClosed head,
        OpenDerivationList.close_ofClosed tail]

end

mutual

/-- Reopening a proof that was closed from the empty context recovers the
same open derivation. -/
@[simp] theorem OpenDerivation.ofClosed_close
    {definition : ValidatedCalculusLanguageDef} {goal : Pattern}
    (derivation : OpenDerivation definition [] goal) :
    OpenDerivation.ofClosed derivation.close = derivation := by
  cases derivation with
  | assumption index => exact Fin.elim0 index
  | byRule ruleInstance application children =>
      simp only [OpenDerivation.close, OpenDerivation.ofClosed]
      congr 1
      exact OpenDerivationList.ofClosed_close children

/-- Pointwise empty-context reopen/close agreement. -/
@[simp] theorem OpenDerivationList.ofClosed_close
    {definition : ValidatedCalculusLanguageDef} {goals : List Pattern}
    (derivations : OpenDerivationList definition [] goals) :
    OpenDerivationList.ofClosed derivations.close = derivations := by
  cases derivations with
  | nil => rfl
  | cons head tail =>
      simp only [OpenDerivationList.close, OpenDerivationList.ofClosed]
      rw [OpenDerivation.ofClosed_close head,
        OpenDerivationList.ofClosed_close tail]

end

end Mettapedia.GSLT.LanguageDef.CertificateGSLT
