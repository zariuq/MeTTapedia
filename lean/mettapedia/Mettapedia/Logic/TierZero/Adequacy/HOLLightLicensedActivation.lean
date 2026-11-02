import Mettapedia.Logic.TierZero.Adequacy.HOLLightContextLicensing
import Mettapedia.Logic.TierZero.Adequacy.HOLLightContextActivation

/-!
# Ordinary command, context transport and inclusion activations

The private license location is separate from theorem and public request
locations. Commands wrap the already qualified original source activation;
weakening reads an explicit inclusion witness, and inclusion composition is
ordinary persistent metadata computation. Runtime activation does not decide
source derivability or context licensing.

This layer proves rooted licensing safety at the existence observation.
Arbitrary duplicate license rows can add administrative read witnesses; answer
count preservation additionally requires a canonical private registry.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.TierZero.Adequacy.HOLLightLicensedActivation

open Mettapedia.OSLF.Binding.WireCodec
open Mettapedia.Languages.OpenTheory
open Mettapedia.Languages.OpenTheory.SyntaxEncoding
open Mettapedia.Languages.HOLLight.DefinitionAdapters
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
open InferenceSchemaActivation (Tm action)
open HOLLightContextActivation (Entry theoremPayload)

abbrev Location := InferenceSchemaKernel.Space ⊕ Unit
def requests : Location := .inl .requests
def judgments : Location := .inl .judgments
def licenses : Location := .inr ()
abbrev Value := Location × Tm
abbrev locatedAction := LocatedSubstitution.action (N := Location) action

def lift (value : InferenceSchemaKernel.Value) : Value := (.inl value.1, value.2)

def available (context : Nat) : Tm :=
  .node (.inr "registered.context") (.cons 0 (WireDataABT.encode (.atom context)) .nil)

def included (before after : Nat) : Tm :=
  .node (.inr "registered.inclusion") (.cons 0 (WireDataABT.encode (.pair (.atom before) (.atom after))) .nil)

theorem available_injective : Function.Injective available := by
  intro first second same
  have wire : WireDataABT.encode (.atom first) = WireDataABT.encode (.atom second) := by simpa [available] using same
  exact Data.atom.inj (WireDataABT.encode_injective wire)

theorem included_injective {a b c d : Nat} (same : included a b = included c d) : a = c ∧ b = d := by
  have wire : WireDataABT.encode (.pair (.atom a) (.atom b)) = WireDataABT.encode (.pair (.atom c) (.atom d)) := by
    simpa [included] using same
  simpa using WireDataABT.encode_injective wire

theorem available_ne_included (context before after : Nat) : available context ≠ included before after := by
  simp [available, included]

theorem available_fixed (context : Nat) (assignment : ABTProtectedParameters.Assignment InferenceSchemaActivation.Head 0) :
    action.apply assignment (available context) = available context := by
  apply ABTProtectedParameters.supported_term_fixed
  simpa [available, Mettapedia.GSLT.LanguageDef.SignatureIndexedABT.Term.supportedAt,
    Mettapedia.GSLT.LanguageDef.SignatureIndexedABT.Term.Fields.supportedAt] using WireDataABT.encode_supported (.atom context)

theorem included_fixed (before after : Nat) (assignment : ABTProtectedParameters.Assignment InferenceSchemaActivation.Head 0) :
    action.apply assignment (included before after) = included before after := by
  apply ABTProtectedParameters.supported_term_fixed
  simpa [included, Mettapedia.GSLT.LanguageDef.SignatureIndexedABT.Term.supportedAt,
    Mettapedia.GSLT.LanguageDef.SignatureIndexedABT.Term.Fields.supportedAt] using
    WireDataABT.encode_supported (.pair (.atom before) (.atom after))

def administrativeOutputs {contexts : Nat → TheoryContext} (entry : Entry contexts) : List Value :=
  if entry.after = entry.before then [] else
    [(licenses, available entry.after), (licenses, included entry.before entry.after)]

def commandRule {contexts : Nat → TheoryContext} (entry : Entry contexts)
    (raw : RuleInstance InferenceSchemaKernel.Value) : RuleInstance Value :=
  { raw.map lift with
    read := (licenses, available entry.before) :: raw.read.map lift
    produce := administrativeOutputs entry ++ raw.produce.map lift }

def commandActivate (policy : AxiomPolicy) [DecidablePred policy] (contexts : Nat → TheoryContext)
    (entries : Nat → Option (Entry contexts)) (source : Nat) (cache : Array Theorem) : Option (RuleInstance Value) := do
  let entry ← entries source
  let raw ← HOLLightContextActivation.activate policy contexts entries source cache
  pure (commandRule entry raw)

def weakeningRequest (before after : Nat) (fact : Theorem) : Tm :=
  .node (.inr "registered.weaken") (.cons 0
    (WireDataABT.encode (.pair (.pair (.atom before) (.atom after)) (theoremCodec.put fact))) .nil)

def weakeningRule (before after : Nat) (fact : Theorem) : RuleInstance Value :=
  ⟨[(requests, weakeningRequest before after fact)],
    [(licenses, available after), (licenses, included before after), (judgments, theoremPayload before fact)],
    [], [], [(judgments, theoremPayload after fact)]⟩

def compositionRequest (first middle last : Nat) : Tm :=
  .node (.inr "registered.include-compose") (.cons 0
    (WireDataABT.encode (.pair (.atom first) (.pair (.atom middle) (.atom last)))) .nil)

def compositionRule (first middle last : Nat) : RuleInstance Value :=
  ⟨[(requests, compositionRequest first middle last)],
    [(licenses, included first middle), (licenses, included middle last)],
    [], [], [(licenses, included first last)]⟩

abbrev Source := Nat ⊕ Bool
abbrev Inputs := Array Theorem ⊕ ((Nat × Nat × Theorem) ⊕ (Nat × Nat × Nat))

def activate (policy : AxiomPolicy) [DecidablePred policy] (contexts : Nat → TheoryContext)
    (entries : Nat → Option (Entry contexts)) : Source → Inputs → Option (RuleInstance Value)
  | .inl source, .inl cache => commandActivate policy contexts entries source cache
  | .inr false, .inr (.inl (before, after, fact)) => some (weakeningRule before after fact)
  | .inr true, .inr (.inr (first, middle, last)) => some (compositionRule first middle last)
  | _, _ => none

end Mettapedia.Logic.TierZero.Adequacy.HOLLightLicensedActivation
