import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualTransportedActivation
import Mettapedia.OSLF.Syntax.ClosedCommunicationInstances

/-!
# Communication as a contextual occurrence rule

The rule uses the existing rho binding signature. Its channel and payload
are nullary rule locals; its continuation is a process local open in one
name. The receiver and sender are consumed as two physical occurrences.
The produced process applies that same continuation to the quoted payload.

The constrained form adds a visible payload equation. That extra equation
is separate from the pure communication rule.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualCommunication

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open Mettapedia.OSLF.Binding.RhoSchema (Srt)

abbrev base := RhoSchema.sig

def operatorEquality (sort : base.Srt) : DecidableEq (base.Op sort) := by
  intro first second
  cases first <;> cases second <;> first | exact .isTrue rfl | exact .isFalse (by intro same; cases same)

inductive Port where
  | channel
  | payload
  | continuation
  deriving DecidableEq, Repr

def locals : Port → MetaArity base
  | .channel => ([], .nm)
  | .payload => ([], .pr)
  | .continuation => ([.nm], .pr)

variable {V W : Type} {declaration : V → MetaArity base} {next : W → MetaArity base}

def zero {Γ : Ctx base} : Term (signature base declaration) Γ .pr := .op (.inl .nil) .nil
def quote {Γ : Ctx base} (payload : Term (signature base declaration) Γ .pr) :
    Term (signature base declaration) Γ .nm := .op (.inl .quo) (.cons payload .nil)
def output {Γ : Ctx base} (channel : Term (signature base declaration) Γ .nm)
    (payload : Term (signature base declaration) Γ .pr) : Term (signature base declaration) Γ .pr :=
  .op (.inl .out) (.cons channel (.cons payload .nil))
def input {Γ : Ctx base} (channel : Term (signature base declaration) Γ .nm)
    (body : Term (signature base declaration) (.nm :: Γ) .pr) : Term (signature base declaration) Γ .pr :=
  .op (.inl .inp) (.cons channel (.cons body .nil))
def parallel {Γ : Ctx base} (left right : Term (signature base declaration) Γ .pr) :
    Term (signature base declaration) Γ .pr := .op (.inl .par) (.cons left (.cons right .nil))

private def inputChannel {Γ : Ctx base} : Term (signature base declaration) Γ .pr →
    Option (Term (signature base declaration) Γ .nm)
  | .op (.inl .inp) (.cons channel (.cons _ .nil)) => some channel
  | _ => none

private def outputFields {Γ : Ctx base} : Term (signature base declaration) Γ .pr →
    Option (Term (signature base declaration) Γ .nm × Term (signature base declaration) Γ .pr)
  | .op (.inl .out) (.cons channel (.cons body .nil)) => some (channel, body)
  | _ => none

theorem input_channel {Γ : Ctx base} {left right : Term (signature base declaration) Γ .nm}
    {body other : Term (signature base declaration) (.nm :: Γ) .pr}
    (same : input left body = input right other) : left = right :=
  Option.some.inj (congrArg inputChannel same)

theorem output_channel {Γ : Ctx base} {left right : Term (signature base declaration) Γ .nm}
    {body other : Term (signature base declaration) Γ .pr}
    (same : output left body = output right other) : left = right :=
  congrArg Prod.fst (Option.some.inj (congrArg outputFields same))

theorem output_payload {Γ : Ctx base} {left right : Term (signature base declaration) Γ .nm}
    {body other : Term (signature base declaration) Γ .pr}
    (same : output left body = output right other) : body = other :=
  congrArg Prod.snd (Option.some.inj (congrArg outputFields same))

variable (captures : V → MetaArity base)

abbrev source := ContextualActivatedStep.source (S := base) locals captures
abbrev target := ContextualActivatedStep.target (S := base) locals captures

def channel {Γ : Ctx base} : Term (signature base (source captures)) Γ .nm :=
  .op (.inr (Operator.mk (declaration := source captures) (.inl .channel))) .nil
def payload {Γ : Ctx base} : Term (signature base (source captures)) Γ .pr :=
  .op (.inr (Operator.mk (declaration := source captures) (.inl .payload))) .nil
def continuation {Γ : Ctx base} (name : Term (signature base (source captures)) Γ .nm) :
    Term (signature base (source captures)) Γ .pr :=
  .op (.inr (Operator.mk (declaration := source captures) (.inl .continuation))) (.cons name .nil)

def rule : RuleInstance (Term (signature base (source captures)) [] .pr) where
  take := [input (channel captures) (continuation captures (.var .zero)), output (channel captures) (payload captures)]
  read := []
  tell := []
  checks := []
  produce := [continuation captures (quote (payload captures))]

def constrainedRule (expected : Term (signature base (source captures)) [] .pr) :
    RuleInstance (Term (signature base (source captures)) [] .pr) :=
  { rule captures with tell := [(payload captures, expected)] }

theorem the_payload_constraint_is_explicit (expected : Term (signature base (source captures)) [] .pr) :
    (constrainedRule captures expected).tell = [(payload captures, expected)] ∧ (rule captures).tell = [] := ⟨rfl, rfl⟩

theorem instantiate_result (assignment : Assignment (source captures) next) :
    instantiate assignment (continuation captures (quote (payload captures))) =
      inst (assignment (.inl .continuation)) (quote (assignment (.inl .payload))) := by
  have payloadImage : instantiate assignment (payload captures (Γ := [])) = assignment (.inl .payload) :=
    instantiate_generator assignment (.inl .payload)
  change bind (argsToSub (.cons (instantiate assignment (quote (payload captures))) .nil))
    (assignment (.inl .continuation)) =
      bind (extend (quote (assignment (.inl .payload)))) (assignment (.inl .continuation))
  apply congrArg (fun environment : Sub (signature base next) [.nm] [] =>
    bind environment (assignment (.inl .continuation)))
  funext sort position
  cases position with
  | zero =>
      exact congrArg (fun value : Term (signature base next) [] .pr => quote value) payloadImage
  | succ impossible => cases impossible

/-- When a selected sender is fixed by the model, the two-sided equation
is exactly its older one-way matching condition. -/
theorem one_way_of_fixed (assignment : Assignment declaration declaration) {Γ : Ctx base}
    (pattern sender : Term (signature base declaration) Γ .pr)
    (fixed : instantiate assignment sender = sender) :
    (ContextualFamilies.action declaration Γ .pr).Solves assignment (pattern, sender) ↔
      instantiate assignment pattern = sender :=
  Selection.solves_iff_matching_of_fixed (ContextualFamilies.action declaration Γ .pr) assignment pattern sender fixed

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualCommunication
