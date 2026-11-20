import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualTransportedActivation
import Mettapedia.OSLF.Syntax.ClosedCommunicationInstances
import Mettapedia.OSLF.Syntax.RhoPayloadPresentation

/-!
# Communication as a contextual occurrence rule

The channel and payload are nullary rule locals; the continuation is a process
local open in the declared received sort. One rule constructor serves both
existing binding signatures. The name-binding signature applies the
continuation to the quoted payload. The payload-binding signature applies it
to the received process itself. Both consume two physical occurrences.

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

section CommunicationSchema

variable {S : Signature} {V W : Type}

/-- The received argument's sort is independent of the channel's sort.
Name-binding and payload-binding communication use the same local identities. -/
abbrev portArities (name process received : S.Srt) : Port → MetaArity S
  | .channel => ([], name)
  | .payload => ([], process)
  | .continuation => ([received], process)

abbrev schemaSource (name process received : S.Srt) (captures : V → MetaArity S) :=
  ContextualActivatedStep.source (portArities name process received) captures

def channelFor (name process received : S.Srt) (captures : V → MetaArity S)
    {Γ : Ctx S} : Term (signature S (schemaSource name process received captures)) Γ name :=
  .op (.inr (Operator.mk (declaration := schemaSource name process received captures)
    (.inl .channel))) .nil

def payloadFor (name process received : S.Srt) (captures : V → MetaArity S)
    {Γ : Ctx S} : Term (signature S (schemaSource name process received captures)) Γ process :=
  .op (.inr (Operator.mk (declaration := schemaSource name process received captures)
    (.inl .payload))) .nil

def continuationFor (name process received : S.Srt) (captures : V → MetaArity S)
    {Γ : Ctx S} (argument : Term (signature S (schemaSource name process received captures)) Γ received) :
    Term (signature S (schemaSource name process received captures)) Γ process :=
  .op (.inr (Operator.mk (declaration := schemaSource name process received captures)
    (.inl .continuation))) (.cons argument .nil)

/-- Construct a two-occurrence communication rule using the source signature's
own constructors and its declared payload-to-argument operation. -/
def communicationRule (name process received : S.Srt) (captures : V → MetaArity S)
    (input : {Γ : Ctx S} → Term (signature S (schemaSource name process received captures)) Γ name →
      Term (signature S (schemaSource name process received captures)) (received :: Γ) process →
      Term (signature S (schemaSource name process received captures)) Γ process)
    (output : {Γ : Ctx S} → Term (signature S (schemaSource name process received captures)) Γ name →
      Term (signature S (schemaSource name process received captures)) Γ process →
      Term (signature S (schemaSource name process received captures)) Γ process)
    (receive : {Γ : Ctx S} → Term (signature S (schemaSource name process received captures)) Γ process →
      Term (signature S (schemaSource name process received captures)) Γ received) :
    RuleInstance (Term (signature S (schemaSource name process received captures)) [] process) where
  take := [input (channelFor name process received captures)
      (continuationFor name process received captures (.var .zero)),
    output (channelFor name process received captures) (payloadFor name process received captures)]
  read := []
  tell := []
  checks := []
  produce := [continuationFor name process received captures (receive (payloadFor name process received captures))]

theorem instantiate_continuationFor (name process received : S.Srt)
    (captures : V → MetaArity S) {next : W → MetaArity S}
    (assignment : Assignment (schemaSource name process received captures) next)
    (argument : Term (signature S (schemaSource name process received captures)) [] received) :
    instantiate assignment (continuationFor name process received captures argument) =
      inst (assignment (.inl .continuation)) (instantiate assignment argument) := by
  change bind (argsToSub (.cons (instantiate assignment argument) .nil))
    (assignment (.inl .continuation)) =
      bind (extend (instantiate assignment argument)) (assignment (.inl .continuation))
  apply congrArg (fun environment : Sub (signature S next) [received] [] =>
    bind environment (assignment (.inl .continuation)))
  funext sort position
  cases position with
  | zero => rfl
  | succ impossible => cases impossible

end CommunicationSchema

def locals : Port → MetaArity base := portArities (S := base) .nm .pr .nm

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
  channelFor (S := base) .nm .pr .nm captures
def payload {Γ : Ctx base} : Term (signature base (source captures)) Γ .pr :=
  payloadFor (S := base) .nm .pr .nm captures
def continuation {Γ : Ctx base} (name : Term (signature base (source captures)) Γ .nm) :
    Term (signature base (source captures)) Γ .pr :=
  continuationFor (S := base) .nm .pr .nm captures name

def rule : RuleInstance (Term (signature base (source captures)) [] .pr) :=
  communicationRule (S := base) .nm .pr .nm captures input output quote

def constrainedRule (expected : Term (signature base (source captures)) [] .pr) :
    RuleInstance (Term (signature base (source captures)) [] .pr) :=
  { rule captures with tell := [(payload captures, expected)] }

theorem the_payload_constraint_is_explicit (expected : Term (signature base (source captures)) [] .pr) :
    (constrainedRule captures expected).tell = [(payload captures, expected)] ∧ (rule captures).tell = [] := ⟨rfl, rfl⟩

theorem instantiate_result (assignment : Assignment (source captures) next) :
    instantiate assignment (continuation captures (quote (payload captures))) =
      inst (assignment (.inl .continuation)) (quote (assignment (.inl .payload))) := by
  exact (instantiate_continuationFor (S := base) .nm .pr .nm captures assignment
    (quote (payload captures))).trans
      (congrArg (inst (assignment (.inl .continuation)))
        (congrArg quote (instantiate_generator assignment (.inl .payload))))

/-- When a selected sender is fixed by the model, the two-sided equation
is exactly its older one-way matching condition. -/
theorem one_way_of_fixed (assignment : Assignment declaration declaration) {Γ : Ctx base}
    (pattern sender : Term (signature base declaration) Γ .pr)
    (fixed : instantiate assignment sender = sender) :
    (ContextualFamilies.action declaration Γ .pr).Solves assignment (pattern, sender) ↔
      instantiate assignment pattern = sender :=
  Selection.solves_iff_matching_of_fixed (ContextualFamilies.action declaration Γ .pr) assignment pattern sender fixed

namespace Payload

abbrev base := RhoPayloadPresentation.sig
abbrev locals := portArities (S := base) .nm .pr .pr

variable {V W : Type} (captures : V → MetaArity base) {next : W → MetaArity base}

abbrev source := ContextualActivatedStep.source locals captures
abbrev target := ContextualActivatedStep.target locals captures

def input {declaration : V → MetaArity base} {Γ : Ctx base}
    (channel : Term (signature base declaration) Γ .nm)
    (body : Term (signature base declaration) (.pr :: Γ) .pr) :
    Term (signature base declaration) Γ .pr :=
  .op (.inl .inp) (.cons channel (.cons body .nil))

def output {declaration : V → MetaArity base} {Γ : Ctx base}
    (channel : Term (signature base declaration) Γ .nm)
    (body : Term (signature base declaration) Γ .pr) :
    Term (signature base declaration) Γ .pr :=
  .op (.inl .out) (.cons channel (.cons body .nil))

private def inputFields {declaration : V → MetaArity base} {Γ : Ctx base} :
    Term (signature base declaration) Γ .pr →
      Option (Term (signature base declaration) Γ .nm ×
        Term (signature base declaration) (.pr :: Γ) .pr)
  | .op (.inl .inp) (.cons channel (.cons body .nil)) => some (channel, body)
  | _ => none

private def outputFields {declaration : V → MetaArity base} {Γ : Ctx base} :
    Term (signature base declaration) Γ .pr →
      Option (Term (signature base declaration) Γ .nm × Term (signature base declaration) Γ .pr)
  | .op (.inl .out) (.cons channel (.cons body .nil)) => some (channel, body)
  | _ => none

theorem input_fields {declaration : V → MetaArity base} {Γ : Ctx base}
    {channel other : Term (signature base declaration) Γ .nm}
    {body rest : Term (signature base declaration) (.pr :: Γ) .pr}
    (same : input channel body = input other rest) : channel = other ∧ body = rest := by
  have fields := Option.some.inj (congrArg inputFields same)
  exact ⟨congrArg Prod.fst fields, congrArg Prod.snd fields⟩

theorem output_fields {declaration : V → MetaArity base} {Γ : Ctx base}
    {channel other : Term (signature base declaration) Γ .nm}
    {body rest : Term (signature base declaration) Γ .pr}
    (same : output channel body = output other rest) : channel = other ∧ body = rest := by
  have fields := Option.some.inj (congrArg outputFields same)
  exact ⟨congrArg Prod.fst fields, congrArg Prod.snd fields⟩

/-- The received process itself is the continuation argument. Quotation and
literal drop retain the distinct rules of the payload-binding source. -/
def rule : RuleInstance (Term (signature base (source captures)) [] .pr) :=
  communicationRule (S := base) .nm .pr .pr captures input output (fun payload => payload)

theorem instantiate_result (assignment : Assignment (source captures) next) :
    instantiate assignment (continuationFor (S := base) .nm .pr .pr captures
      (payloadFor (S := base) .nm .pr .pr captures)) =
      inst (assignment (.inl .continuation)) (assignment (.inl .payload)) := by
  exact (instantiate_continuationFor (S := base) .nm .pr .pr captures assignment
    (payloadFor (S := base) .nm .pr .pr captures)).trans
      (congrArg (inst (assignment (.inl .continuation)))
        (instantiate_generator assignment (.inl .payload)))

end Payload

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualCommunication
