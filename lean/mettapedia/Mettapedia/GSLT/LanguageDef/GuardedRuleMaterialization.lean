import Mathlib.Data.List.Basic

/-!
# Guarded materialization for admitted rule bodies

A rule-machine interpreter may materialize a candidate rule body before it
knows whether the candidate head matches the current goal.  This module
isolates the local condition under which that work can be delayed: the body
has passed a decidable admission check and its materializer is total on the
admitted fragment.

The semantic theorem is independent of the rule, goal, environment, and
result representations.  The accompanying cost theorem states that guarded
materialization never performs more body work, and performs strictly less on
a rejected head whose body has positive materialization cost.
-/

namespace Mettapedia.GSLT.LanguageDef.GuardedRuleMaterialization

universe uHead uBody uMaterializedHead uMaterializedBody uGoal uEnvironment
  uResult

/-- The static part of one rule-machine candidate. -/
structure RulePlan (Head : Type uHead) (Body : Type uBody) where
  head : Head
  body : Body

/-- A rule whose body lies in the fragment on which materialization is total. -/
structure AdmittedRule (Head : Type uHead) (Body : Type uBody)
    (bodySupported : Body → Bool) extends RulePlan Head Body where
  body_supported : bodySupported body = true

/-- Decidable local admission for guarded body materialization. -/
def admitRule? (bodySupported : Body → Bool) (rule : RulePlan Head Body) :
    Option (AdmittedRule Head Body bodySupported) :=
  if accepted : bodySupported rule.body = true then
    some {
      head := rule.head
      body := rule.body
      body_supported := accepted }
  else
    none

/-- Admission succeeds exactly when the authored body recognizer accepts. -/
theorem admitRule?_isSome_eq
    (bodySupported : Body → Bool) (rule : RulePlan Head Body) :
    (admitRule? bodySupported rule).isSome = bodySupported rule.body := by
  unfold admitRule?
  split <;> simp_all

/-- Eager schedule: materialize the admitted body before testing the head. -/
def eagerApply
    (bodySupported : Body → Bool)
    (materializeHead : Head → MaterializedHead)
    (materializeBody :
      ∀ body, bodySupported body = true → MaterializedBody)
    (matchHead : Goal → MaterializedHead → Option Environment)
    (resolveBody : Environment → MaterializedBody → Result)
    (rule : AdmittedRule Head Body bodySupported) (goal : Goal) :
    Option Result :=
  let materializedHead := materializeHead rule.head
  let materializedBody :=
    materializeBody rule.body rule.body_supported
  match matchHead goal materializedHead with
  | none => none
  | some environment => some (resolveBody environment materializedBody)

/-- Guarded schedule: materialize the admitted body only after head success. -/
def guardedApply
    (bodySupported : Body → Bool)
    (materializeHead : Head → MaterializedHead)
    (materializeBody :
      ∀ body, bodySupported body = true → MaterializedBody)
    (matchHead : Goal → MaterializedHead → Option Environment)
    (resolveBody : Environment → MaterializedBody → Result)
    (rule : AdmittedRule Head Body bodySupported) (goal : Goal) :
    Option Result :=
  let materializedHead := materializeHead rule.head
  match matchHead goal materializedHead with
  | none => none
  | some environment =>
      let materializedBody :=
        materializeBody rule.body rule.body_supported
      some (resolveBody environment materializedBody)

/-- Delaying total, pure body materialization preserves the complete result. -/
theorem guardedApply_eq_eagerApply
    (bodySupported : Body → Bool)
    (materializeHead : Head → MaterializedHead)
    (materializeBody :
      ∀ body, bodySupported body = true → MaterializedBody)
    (matchHead : Goal → MaterializedHead → Option Environment)
    (resolveBody : Environment → MaterializedBody → Result)
    (rule : AdmittedRule Head Body bodySupported) (goal : Goal) :
    guardedApply bodySupported materializeHead materializeBody matchHead
        resolveBody rule goal =
      eagerApply bodySupported materializeHead materializeBody matchHead
        resolveBody rule goal := by
  unfold guardedApply eagerApply
  cases matchHead goal (materializeHead rule.head) <;> rfl

/-- Eager body work for one candidate. -/
def eagerBodyCost (bodyCost : Body → Nat)
    (rule : AdmittedRule Head Body bodySupported) : Nat :=
  bodyCost rule.body

/-- Guarded body work for one candidate. -/
def guardedBodyCost
    (materializeHead : Head → MaterializedHead)
    (matchHead : Goal → MaterializedHead → Option Environment)
    (bodyCost : Body → Nat)
    (rule : AdmittedRule Head Body bodySupported) (goal : Goal) : Nat :=
  match matchHead goal (materializeHead rule.head) with
  | none => 0
  | some _ => bodyCost rule.body

/-- Guarded scheduling never performs more body-materialization work. -/
theorem guardedBodyCost_le_eagerBodyCost
    (materializeHead : Head → MaterializedHead)
    (matchHead : Goal → MaterializedHead → Option Environment)
    (bodyCost : Body → Nat)
    (rule : AdmittedRule Head Body bodySupported) (goal : Goal) :
    guardedBodyCost materializeHead matchHead bodyCost rule goal ≤
      eagerBodyCost bodyCost rule := by
  unfold guardedBodyCost eagerBodyCost
  cases matchHead goal (materializeHead rule.head) <;> simp

/-- A rejected head with a nonempty body gives a strict cost improvement. -/
theorem guardedBodyCost_lt_eagerBodyCost_of_rejected
    (materializeHead : Head → MaterializedHead)
    (matchHead : Goal → MaterializedHead → Option Environment)
    (bodyCost : Body → Nat)
    (rule : AdmittedRule Head Body bodySupported) (goal : Goal)
    (rejected : matchHead goal (materializeHead rule.head) = none)
    (positive : 0 < bodyCost rule.body) :
    guardedBodyCost materializeHead matchHead bodyCost rule goal <
      eagerBodyCost bodyCost rule := by
  simp [guardedBodyCost, eagerBodyCost, rejected, positive]

/-! ## Cross-shape and rejection canaries -/

private def nonemptyList (body : List Nat) : Bool := !body.isEmpty

private def relationalRule : RulePlan (String × Nat) (List Nat) :=
  { head := ("edge", 2), body := [3, 5] }

private def relationMatch (goal head : String × Nat) : Option Unit :=
  if goal = head then some () else none

/-- A relation-shaped rule is admitted and preserves a successful result. -/
example :
    ∃ rule : AdmittedRule (String × Nat) (List Nat) nonemptyList,
      guardedApply nonemptyList id (fun body _ => body.reverse)
          relationMatch (fun _ body => body.length) rule ("edge", 2) =
        some 2 := by
  refine ⟨{
    head := relationalRule.head
    body := relationalRule.body
    body_supported := by decide }, ?_⟩
  decide

/-- The same admitted rule skips positive body work on a rejected head. -/
example :
    ∃ rule : AdmittedRule (String × Nat) (List Nat) nonemptyList,
      guardedBodyCost id relationMatch List.length rule ("node", 1) <
        eagerBodyCost List.length rule := by
  refine ⟨{
    head := relationalRule.head
    body := relationalRule.body
    body_supported := by decide }, ?_⟩
  decide

/-- A structurally different numeric opcode plan uses the same schedule. -/
example :
    let supported : Nat → Bool := fun body => body != 0
    let rule : AdmittedRule Nat Nat supported := {
      head := 7
      body := 12
      body_supported := by decide }
    guardedApply supported id (fun body _ => body * 2)
        (fun goal head => if goal % 10 = head then some goal else none)
        (fun environment body => environment + body) rule 17 = some 41 := by
  decide

/-- An unsupported empty body is rejected by the local recognizer. -/
example :
    (admitRule? nonemptyList
      ({ head := ("empty", 0), body := [] } :
        RulePlan (String × Nat) (List Nat))).isSome = false := by
  decide

end Mettapedia.GSLT.LanguageDef.GuardedRuleMaterialization
