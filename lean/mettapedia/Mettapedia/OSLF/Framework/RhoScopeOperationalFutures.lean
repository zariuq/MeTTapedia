import Mettapedia.OSLF.Framework.RhoScopeMinimumReceiptTransport
import Mettapedia.OSLF.Syntax.RhoScopedNativeAbsence

/-!
# Generated scopes with original operational atoms

An atomic premise is the support of the original scoped event graph, not a
supplied transition oracle. Complete quotient-valued substitution preserves
this premise through the earned original event action. Generated scope
certificates therefore transport their depth and ordered process origins.
Retractable future changes earn reflection of membership and equality of
independently searched minimum depths.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.OSLF.Framework.RhoScopeOperationalFutures

open Mettapedia.OSLF.Binding
open _root_.CategoryTheory RhoSchema RhoQuotationClassFibres RhoEquationConstructorControls
open BindingSubstitutionAlgebra BindingConstructorPredicates
open RhoScopedParallelEvents RhoScopedNativeAbsence SyntacticRetractionContexts
open RhoEquationGeneratedScope RhoGeneratedScopeSubstitution RhoScopeMinimumReceipts
open RhoScopeMinimumReceiptTransport

def operationalAtom (admitted : SourceRule → Prop) : Predicate model .pr where
  holds := Enabled admitted
  substitute := by
    intro context destination env process holds
    exact enabled_substitution admitted
      (BindingEquationQuotientSubstitution.representativeEnv rhoSourceE env) holds

def operationalScope (left right : SourceRule → Prop) : Predicate model .nm :=
  native (operationalAtom left) (operationalAtom right)

def rawEnvironment {context destination : Ctx sig} (change : Sub sig context destination) :
    Environment sig (TermQ rhoSourceE) context destination :=
  fun sort position => project (change sort position)

theorem raw_substitution {context destination : Ctx sig} {sort : Srt}
    (change : Sub sig context destination) (value : TermQ rhoSourceE context sort) :
    BindingEquationQuotientSubstitution.substitute rhoSourceE (rawEnvironment change) value =
      bindQ change value :=
  BindingEquationQuotientSubstitution.substitute_eq_bindQ rhoSourceE
    (rawEnvironment change) change (fun _ _ => rfl) value

theorem enabled_environment {context destination : Ctx sig}
    (admitted : SourceRule → Prop) (env : Environment sig (TermQ rhoSourceE) context destination)
    (process : Process context) :
    Enabled admitted process → Enabled admitted (model.substitution.substitute env process) :=
  (operationalAtom admitted).substitute env process

def transportRaw {context destination : Ctx sig} (left right : SourceRule → Prop)
    (change : Sub sig context destination) {name : Name context}
    (receipt : Certificate (Enabled left) (Enabled right) name) :
    Certificate (Enabled left) (Enabled right) (bindQ change name) :=
  (raw_substitution change name) ▸ transport (rawEnvironment change)
    (enabled_environment left (rawEnvironment change))
    (enabled_environment right (rawEnvironment change)) receipt

theorem transportRaw_depth {context destination : Ctx sig} (left right : SourceRule → Prop)
    (change : Sub sig context destination) {name : Name context}
    (receipt : Certificate (Enabled left) (Enabled right) name) :
    (transportRaw left right change receipt).depth = receipt.depth := by
  simp only [transportRaw, depth_cast, transport_depth]

theorem quotient_roundtrip {source target : Object sig} (change : source ⟶ target)
    {sort : Srt} (value : TermQ rhoSourceE target.context.vars sort) :
    bindQ (backward change) (bindQ change.val value) = value := by
  rw [RhoScopedEventPresheaf.substitute_comp]
  change bindQ (backward change ≫ change.val) value = value
  rw [backward_section]
  exact RhoScopedEventPresheaf.substitute_id value

theorem substitution_injective {source target : Object sig} (change : source ⟶ target)
    (sort : Srt) : Function.Injective (bindQ change.val :
      TermQ rhoSourceE target.context.vars sort → TermQ rhoSourceE source.context.vars sort) := by
  intro first second same
  exact (quotient_roundtrip change first).symm.trans
    ((congrArg (bindQ (backward change)) same).trans (quotient_roundtrip change second))

theorem generated_substitution {context destination : Ctx sig}
    (left right : SourceRule → Prop) (change : Sub sig context destination)
    {name : Name context} (member : generated (Enabled left) (Enabled right) name) :
    generated (Enabled left) (Enabled right) (bindQ change name) := by
  have transported := (operationalScope left right).substitute (rawEnvironment change) name member
  exact (raw_substitution change name) ▸ transported

theorem permitted_membership_iff {source target : Object sig} (change : source ⟶ target)
    (left right : SourceRule → Prop) (name : Name target.context.vars) :
    generated (Enabled left) (Enabled right) (bindQ change.val name) ↔
      generated (Enabled left) (Enabled right) name := by
  constructor
  · intro member
    exact (quotient_roundtrip change name) ▸
      generated_substitution left right (backward change) member
  · exact generated_substitution left right change.val

theorem supplied_receipt_readouts {context destination : Ctx sig}
    (left right : SourceRule → Prop) (change : Sub sig context destination)
    {name : Name context} (receipt : Certificate (Enabled left) (Enabled right) name) :
    (transport (rawEnvironment change)
      (enabled_environment left (rawEnvironment change))
      (enabled_environment right (rawEnvironment change)) receipt).depth = receipt.depth ∧
    (transport (rawEnvironment change)
      (enabled_environment left (rawEnvironment change))
      (enabled_environment right (rawEnvironment change)) receipt).atomicOrigins =
      receipt.atomicOrigins.map (Sum.map (bindQ change) (bindQ change)) := by
  have readouts := supplied_transport_readouts (rawEnvironment change)
    (enabled_environment left (rawEnvironment change))
    (enabled_environment right (rawEnvironment change)) receipt
  have functions : (model.substitution.substitute (rawEnvironment change) :
      Process context → Process destination) = bindQ change := funext (raw_substitution change)
  constructor
  · exact readouts.1
  · exact readouts.2.trans (congrArg (fun function =>
      receipt.atomicOrigins.map (Sum.map function function)) functions)

local instance enabledDecision (admitted : SourceRule → Prop) (context : Ctx sig) :
    DecidablePred (Enabled (context := context) admitted) := Classical.decPred _

theorem permitted_minimum_depths {source target : Object sig} (change : source ⟶ target)
    (left right : SourceRule → Prop) {name : Name target.context.vars}
    {earlier : Certificate (Enabled left) (Enabled right) name}
    {later : Certificate (Enabled left) (Enabled right) (bindQ change.val name)}
    (earlierReadout : minimumReceipt? (Enabled left) (Enabled right) name = some earlier)
    (laterReadout : minimumReceipt? (Enabled left) (Enabled right) (bindQ change.val name) = some later) :
    earlier.depth = later.depth := by
  have forwardBound := minimumReceipt?_least (Enabled left) (Enabled right) _
    laterReadout (transportRaw left right change.val earlier)
  rw [transportRaw_depth] at forwardBound
  let recovered : Certificate (Enabled left) (Enabled right) name :=
    (quotient_roundtrip change name) ▸ transportRaw left right (backward change) later
  have backwardBound := minimumReceipt?_least (Enabled left) (Enabled right) name
    earlierReadout recovered
  have depth : recovered.depth = later.depth := by
    simp only [recovered, depth_cast, transportRaw_depth]
  rw [depth] at backwardBound
  exact Nat.le_antisymm backwardBound forwardBound

end Mettapedia.OSLF.Framework.RhoScopeOperationalFutures
