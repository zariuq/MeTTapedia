import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.ComputationReplay
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NativeTypesOnTheStep.Computing.DirectedAnswers.Basic

/-!
# Directed computation descriptors

The existing descriptor grammar carries a root action and a scoped constructor
path. The directed profile accepts beta, projections and declared computations,
and rejects head-conversion actions. This test inspects syntax only.

Coverage reuses the existing complete descriptor and finite-code decoders with
head conversion disabled. Accepted codes then lift to the original presentation
with the same source, target and constructor path.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.DirectedSyntax

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation AlgebraicParallel AlgebraicSchema TypedEquality TypedEquality.Normalization
open ComputationSyntax

variable {Head : Type} {rules : Rules Head}

def directedRules (rules : Rules Head) : Rules Head := {rules with headEq := fun _ _ => False}

instance directedHeadDecidable (rules : Rules Head) : DecidableRel (directedRules rules).headEq :=
  fun _ _ => isFalse id

def directedPresentation (presentation : SchemaPresentation rules) :
    SchemaPresentation (directedRules rules) where
  schema := presentation.schema
  sound := presentation.sound
  cover := presentation.cover

/-- The admission policy is a test of the decoded action constructor. -/
def allowed {presentation : SchemaPresentation rules} {n : Nat} : Action presentation n → Bool
  | .head _ _ _ => false
  | _ => true

theorem action_reduces {presentation : SchemaPresentation rules} {n : Nat}
    (action : Action presentation n) (accepted : allowed action = true) :
    StrongNormalization.Reduces rules action.source action.target := by
  cases action with
  | beta body argument => exact .betaPi body argument
  | first left right => exact .betaSigmaFst left right
  | second left right => exact .betaSigmaSnd left right
  | head left right same => cases accepted
  | declared left right selected arguments => exact .root (presentation.sound selected arguments)

theorem event_reduces {presentation : SchemaPresentation rules} {n : Nat}
    (event : Event presentation n) (accepted : allowed event.action = true) :
    StrongNormalization.Reduces rules event.source event.target :=
  event.context.step (rules := directedRules rules) (action_reduces event.action accepted)

def liftAction {presentation : SchemaPresentation rules} {n : Nat} :
    Action (directedPresentation presentation) n → Action presentation n
  | .beta body argument => .beta body argument
  | .first left right => .first left right
  | .second left right => .second left right
  | .head _ _ impossible => False.elim impossible
  | .declared left right selected arguments => .declared left right selected arguments

def liftEvent {presentation : SchemaPresentation rules} {n : Nat}
    (event : Event (directedPresentation presentation) n) : Event presentation n :=
  ⟨event.innerArity, event.context, liftAction event.action⟩

theorem lift_allowed {presentation : SchemaPresentation rules} {n : Nat}
    (action : Action (directedPresentation presentation) n) : allowed (liftAction action) = true := by
  cases action <;> first | rfl | contradiction

theorem lift_source {presentation : SchemaPresentation rules} {n : Nat}
    (event : Event (directedPresentation presentation) n) : (liftEvent event).source = event.source := by
  obtain ⟨arity, context, action⟩ := event
  cases action <;> first | rfl | contradiction

theorem lift_target {presentation : SchemaPresentation rules} {n : Nat}
    (event : Event (directedPresentation presentation) n) : (liftEvent event).target = event.target := by
  obtain ⟨arity, context, action⟩ := event
  cases action <;> first | rfl | contradiction

/-- Every directed reduction has a descriptor passing the syntactic policy. -/
theorem complete (presentation : SchemaPresentation rules) {n : Nat} {before after : Tm Head n}
    (reduction : StrongNormalization.Reduces rules before after) :
    ∃ event : Event presentation n, allowed event.action = true ∧
      event.source = before ∧ event.target = after := by
  obtain ⟨event, starts, ends⟩ := ComputationSyntax.complete (directedPresentation presentation) reduction
  exact ⟨liftEvent event, lift_allowed event.action, (lift_source event).trans starts,
    (lift_target event).trans ends⟩

variable (presentation : SchemaPresentation rules) (table : SchemaTable Head)
  (same : ∀ {arity : Nat} (left right : Tm Head arity),
    presentation.schema left right ↔ table.family left right)

theorem lift_root {n : Nat} (code : SchemaTableConversionCode.Code Head n) :
    (ComputationReplaySyntax.rootEvent (directedPresentation presentation) table same code).map liftEvent =
      ComputationReplaySyntax.rootEvent presentation table same code := by
  simp only [ComputationReplaySyntax.rootEvent, Option.map_map]
  rfl

variable [DecidableRel rules.headEq]

/-- Disabling head conversion changes no successful directed descriptor. -/
theorem lift_decoded {n : Nat}
    (code : StructuralConversionCode.StepCode Head (SchemaTableConversionCode.Code Head) n)
    {event : Event (directedPresentation presentation) n}
    (parsed : ComputationReplaySyntax.decodeEvent (directedPresentation presentation) table same code = some event) :
    ComputationReplaySyntax.decodeEvent presentation table same code = some (liftEvent event) := by
  induction code
  case betaPi => cases Option.some.inj parsed; rfl
  case betaSigmaFst => cases Option.some.inj parsed; rfl
  case betaSigmaSnd => cases Option.some.inj parsed; rfl
  case head left right =>
    simp [ComputationReplaySyntax.decodeEvent, directedPresentation, directedRules] at parsed
  case root code =>
    change ComputationReplaySyntax.rootEvent (directedPresentation presentation) table same code = some event at parsed
    change ComputationReplaySyntax.rootEvent presentation table same code = _
    rw [← lift_root presentation table same code, parsed]
    rfl
  all_goals
    rename_i ih
    simp only [ComputationReplaySyntax.decodeEvent] at parsed ⊢
    obtain ⟨inner, decoded, rfl⟩ := Option.map_eq_some_iff.mp parsed
    rw [ih decoded]
    rfl

/-- Finite replay syntax covers each directed source step and retains its actual parsed descriptor. -/
theorem source_has_code {n : Nat} {before after : Tm Head n}
    (reduction : StrongNormalization.Reduces rules before after) :
    ∃ code : StructuralConversionCode.StepCode Head (SchemaTableConversionCode.Code Head) n,
      ∃ event : Event presentation n,
        ComputationReplaySyntax.decodeEvent presentation table same code = some event ∧
          allowed event.action = true ∧ event.source = before ∧ event.target = after := by
  obtain ⟨code, decoded⟩ := StructuralConversionCode.StepCode.decode_complete
    (headEq := (directedRules rules).headEq)
    (ComputationReplaySyntax.decoder (directedPresentation presentation) table same) reduction
  obtain ⟨event, parsed, starts, ends⟩ :=
    (ComputationReplaySyntax.decoded_iff (directedPresentation presentation) table same code).mp decoded
  exact ⟨code, liftEvent event, lift_decoded presentation table same code parsed,
    lift_allowed event.action, (lift_source event).trans starts, (lift_target event).trans ends⟩

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.DirectedSyntax

#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.DirectedSyntax.event_reduces
#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.DirectedSyntax.complete
#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.DirectedSyntax.lift_decoded
#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.DirectedSyntax.source_has_code
