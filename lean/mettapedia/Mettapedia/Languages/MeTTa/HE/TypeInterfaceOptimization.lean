import Mettapedia.Languages.MeTTa.HE.Spec.Eval
import Mettapedia.Machines.OrderedGuardPipeline

/-!
# HE type-interface optimization boundaries

HE demand is not PeTTa demand. It may retain an expression where PeTTa
translates and checks it. This module states the native demand classification
separately and transports local applicability refinements through the existing
published ordered candidate scan. First-success selection, bindings, coherent
arrow policy, error order and tuple eligibility are all retained.

The pure ordered-path pruning law applies only to trials certified to have no
answers. It does not suppress inference effects or change the diagnostic's
original actual-type list. Root wildcard checks are not recursive wildcards.
This is not a correspondence proof for the entire C HE inference service or
its extension profiles.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.HE.TypeInterfaceOptimization

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.HE
open Spec.Type Spec.Eval Spec.Match.Merge

inductive Demand where
  | keep | cast | interpret
  deriving DecidableEq, Repr

def expressionShape : Atom → Bool
  | .expression _ => true
  | _ => false

/-- `listForm` is the existing runtime's data-list recognition service.
It is distinct from the intrinsic expression constructor. -/
def KeepCondition (subject expected metatype : Atom) : Prop :=
  expected = Atom.atomType ∨ expected = metatype ∨
    (expected = Atom.expressionType ∧ expressionShape subject = true) ∨
    metatype = Atom.variableType

instance (subject expected metatype : Atom) :
    Decidable (KeepCondition subject expected metatype) :=
  inferInstanceAs (Decidable (_ ∨ _ ∨ (_ ∧ _) ∨ _))

def CastCondition (listForm : Atom → Bool) : Atom → Prop
  | .symbol _ => True
  | .grounded _ => True
  | .expression [] => True
  | subject => listForm subject = true

instance (listForm : Atom → Bool) (subject : Atom) :
    Decidable (CastCondition listForm subject) := by
  cases subject with
  | symbol _ => exact isTrue trivial
  | var _ => exact inferInstanceAs (Decidable (_ = true))
  | grounded _ => exact isTrue trivial
  | expression items =>
      cases items with
      | nil => exact isTrue trivial
      | cons _ _ => exact inferInstanceAs (Decidable (_ = true))

inductive DemandRel (listForm : Atom → Bool) (subject expected metatype : Atom) :
    Demand → Prop where
  | keep : KeepCondition subject expected metatype → DemandRel listForm subject expected metatype .keep
  | cast : ¬KeepCondition subject expected metatype → CastCondition listForm subject →
      DemandRel listForm subject expected metatype .cast
  | interpret : ¬KeepCondition subject expected metatype → ¬CastCondition listForm subject →
      DemandRel listForm subject expected metatype .interpret

def demand (listForm : Atom → Bool) (subject expected metatype : Atom) : Demand :=
  if KeepCondition subject expected metatype then .keep
  else if CastCondition listForm subject then .cast else .interpret

theorem demand_sound (listForm : Atom → Bool) (subject expected metatype : Atom) :
    DemandRel listForm subject expected metatype (demand listForm subject expected metatype) := by
  unfold demand
  split
  · exact .keep (by assumption)
  · split
    · exact .cast (by assumption) (by assumption)
    · exact .interpret (by assumption) (by assumption)

theorem demand_complete {listForm : Atom → Bool} {subject expected metatype : Atom}
    {mode : Demand} (source : DemandRel listForm subject expected metatype mode) :
    demand listForm subject expected metatype = mode := by
  cases source <;> simp_all [demand]

/-- A local applicability equivalence suffices to transport the entire
ordered scan, including its negative premises. No selected candidate or
error block is reconstructed by the optimized component. -/
theorem candidate_scan_transport
    {first second : Space → Atom → Atom → Atom → Bindings →
      SelectedTypeApplicabilityOutcome → Prop}
    (localLaw : ∀ space expression candidate expected bindings outcome,
      first space expression candidate expected bindings outcome ↔
        second space expression candidate expected bindings outcome)
    {space : Space} {expression expected : Atom} {bindings : Bindings}
    {candidates : List Atom} {outcome : FunctionCandidateScanOutcome}
    (scan : FunctionCandidateScanRel first space expression expected bindings candidates outcome) :
    FunctionCandidateScanRel second space expression expected bindings candidates outcome := by
  induction scan with
  | nil => exact .nil
  | nonFunctionSuccess notFunction _ ih => exact .nonFunctionSuccess notFunction ih
  | nonFunctionExhausted notFunction _ ih => exact .nonFunctionExhausted notFunction ih
  | functionSuccess isFunction applicable =>
      exact .functionSuccess isFunction ((localLaw _ _ _ _ _ _).mp applicable)
  | functionFailureThenSuccess isFunction noSuccess error nonempty _ ih =>
      exact .functionFailureThenSuccess isFunction
        (fun policy output success => noSuccess policy output
          ((localLaw _ _ _ _ _ _).mpr success))
        ((localLaw _ _ _ _ _ _).mp error) nonempty ih
  | functionFailureExhausted isFunction noSuccess error nonempty _ ih =>
      exact .functionFailureExhausted isFunction
        (fun policy output success => noSuccess policy output
          ((localLaw _ _ _ _ _ _).mpr success))
        ((localLaw _ _ _ _ _ _).mp error) nonempty ih

theorem candidate_scan_exact
    {first second : Space → Atom → Atom → Atom → Bindings →
      SelectedTypeApplicabilityOutcome → Prop}
    (localLaw : ∀ space expression candidate expected bindings outcome,
      first space expression candidate expected bindings outcome ↔
        second space expression candidate expected bindings outcome)
    (space : Space) (expression expected : Atom) (bindings : Bindings)
    (candidates : List Atom) (outcome : FunctionCandidateScanOutcome) :
    FunctionCandidateScanRel first space expression expected bindings candidates outcome ↔
      FunctionCandidateScanRel second space expression expected bindings candidates outcome :=
  ⟨candidate_scan_transport localLaw,
    candidate_scan_transport (fun space expression candidate expected bindings outcome =>
      (localLaw space expression candidate expected bindings outcome).symm)⟩

variable {State TypeFact : Type}

/-- Ordered trials use fresh branch-local states supplied by `refine`.
The caller retains the unfiltered fact list for its error diagnostic. -/
def trials (refine : State → TypeFact → List State)
    (facts : List TypeFact) (state : State) : List State := facts.flatMap (refine state)

theorem sound_pruning_exact (refine : State → TypeFact → List State)
    (possible : State → TypeFact → Bool)
    (sound : ∀ state fact, possible state fact = false → refine state fact = [])
    (facts : List TypeFact) (state : State) :
    trials refine (facts.filter (possible state)) state = trials refine facts state := by
  induction facts with
  | nil => rfl
  | cons fact facts ih =>
      cases decision : possible state fact with
      | false => simp [trials, decision, sound state fact decision, trials] at ih ⊢; exact ih
      | true => simpa [trials, decision] using congrArg (List.append (refine state fact)) ih

/-- Root wildcards leave the complete caller bindings unchanged, for every
right type. Ordinary structural matching remains mandatory below the root. -/
theorem root_wildcard_exact (other : Atom) (bindings output : Bindings)
    (wildcard : Atom) (isWildcard : wildcard = Atom.atomType ∨ wildcard = Atom.undefinedType) :
    TypeMatchRel wildcard other bindings output ↔ output = bindings := by
  constructor
  · intro matched
    cases matched with
    | undefinedLeft => rfl
    | atomLeft => rfl
    | undefinedRight => rfl
    | atomRight => rfl
    | structural notUndefined notAtom _ _ _ _ =>
        rcases isWildcard with same | same
        · exact (notAtom same).elim
        · exact (notUndefined same).elim
  · intro same
    subst output
    rcases isWildcard with rfl | rfl
    · exact .atomLeft other bindings
    · exact .undefinedLeft other bindings

/-- HE's expression result contract asks evaluation for Undefined; the
selected contract itself is still retained by the caller. -/
def resultDemand (codomain : Atom) : Atom :=
  if codomain = Atom.expressionType then Atom.undefinedType else codomain

theorem rigid_symbols_match_eq {left right : String} {bindings : Bindings}
    (matched : MatchRel equalityGroundedSemantic (.symbol left) (.symbol right) bindings) :
    left = right := by
  cases matched
  rfl

namespace Controls

def application : Atom := .expression [.symbol "+", .grounded (.int 2), .grounded (.int 4)]

theorem expression_argument_is_held :
    demand (fun _ => false) application Atom.expressionType Atom.expressionType = .keep := by decide

theorem undefined_expression_is_interpreted :
    demand (fun _ => false) application Atom.undefinedType Atom.expressionType = .interpret := by decide

theorem undefined_literal_is_cast :
    demand (fun _ => false) (.grounded (.int 6)) Atom.undefinedType Atom.groundedType = .cast := by decide

theorem expression_result_demand_is_not_argument_demand :
    resultDemand Atom.expressionType = Atom.undefinedType ∧
      demand (fun _ => false) application Atom.expressionType Atom.expressionType = .keep := by decide

def refine (state fact : Nat) : List Nat := if fact = 0 then [] else [state + fact, state + fact]
def possible (_state fact : Nat) : Bool := fact != 0

theorem pruning_preserves_order_and_duplicates :
    trials refine ([2, 0, 1, 2].filter (possible 4)) 4 = [6, 6, 5, 5, 6, 6] := by decide

theorem deduplication_is_not_pruning :
    trials refine [2, 2] 0 ≠ trials refine [2] 0 := by decide

theorem nested_atom_requires_structural_matching :
    ∀ output, ¬TypeMatchRel (.expression [.symbol "Box", Atom.atomType])
      (.expression [.symbol "Box", .symbol "Number"]) Bindings.empty output := by
  intro output matchType
  have structural := TypeMatchRel.structural_of_nonWildcard
    (by decide) (by decide) (by decide) (by decide) matchType
  obtain ⟨matched, atoms, _⟩ := structural
  cases atoms with
  | expression items _ =>
      cases items with
      | cons _ _ tail =>
          cases tail with
          | cons head _ _ =>
              exact (by decide : ("Atom" : String) ≠ "Number") (rigid_symbols_match_eq head)

end Controls

end Mettapedia.Languages.MeTTa.HE.TypeInterfaceOptimization
