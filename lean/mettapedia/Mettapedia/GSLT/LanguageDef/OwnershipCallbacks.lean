import Mettapedia.GSLT.LanguageDef.OwnershipRefinement

/-!
# Callable interfaces

A callback interface lists admitted implementations. C type compatibility
alone does not establish a resource contract: every target must resolve to
the same complete signature. The native checker additionally tracks pointer
provenance, receiver/context lifetimes and the C prototype.

These laws justify selecting any listed signature in the existing permission
model. They do not model general C execution or prove the native checker.
Open interfaces instead compare a named implementation's contract to the
field-derived expected contract, with bounded result-nullability refinement.
-/

namespace Mettapedia.GSLT.LanguageDef.Ownership.Callbacks

open Mettapedia.Machines.CMemory.Borrowing

set_option autoImplicit false

def resolve (environment : List Callable) (name : String) : Option Signature :=
  (environment.find? fun c => c.name == name).map Callable.signature

def agrees (environment : List Callable) (signature : Signature) (targets : List String) : Bool :=
  !targets.isEmpty && targets.all (fun name => resolve environment name == some signature)

theorem member_resolves {environment : List Callable} {signature : Signature}
    {targets : List String} (accepted : agrees environment signature targets = true)
    {name : String} (member : name ∈ targets) :
    resolve environment name = some signature := by
  simp only [agrees, Bool.and_eq_true, List.all_eq_true] at accepted
  exact beq_iff_eq.mp (accepted.2 name member)

def invokeTarget (environment : List Callable) (name : String)
    (state : State) (arguments : List Argument) : Option State :=
  (resolve environment name).bind fun signature => invoke signature state arguments

/-- An open callable interface admits a named implementation by its resource
contract. The C checker also requires the authoritative function prototype and
tracked callable provenance; a raw function-pointer type is insufficient. -/
def acceptsSignature (environment : List Callable) (expected : Signature) (name : String) : Bool :=
  match resolve environment name with
  | none => false
  | some provided => Refinement.signatureRefines provided expected

theorem accepted_signature_resolves {environment : List Callable} {expected : Signature} {name : String}
    (accepted : acceptsSignature environment expected name = true) :
    ∃ provided, resolve environment name = some provided ∧
      Refinement.signatureRefines provided expected = true := by
  cases found : resolve environment name with
  | none => simp [acceptsSignature, found] at accepted
  | some provided => exact ⟨provided, rfl, by simpa [acceptsSignature, found] using accepted⟩

theorem open_invocation_agrees {environment : List Callable} {expected : Signature} {name : String}
    (accepted : acceptsSignature environment expected name = true) (state : State) (arguments : List Argument) :
    invokeTarget environment name state arguments = invoke expected state arguments := by
  obtain ⟨provided, found, refined⟩ := accepted_signature_resolves accepted
  simp only [invokeTarget, found, Option.bind_some]
  exact Refinement.signatureRefines_invocation refined state arguments

theorem invocation_agrees {environment : List Callable} {signature : Signature}
    {targets : List String} (accepted : agrees environment signature targets = true)
    {name : String} (member : name ∈ targets) (state : State) (arguments : List Argument) :
    invokeTarget environment name state arguments = invoke signature state arguments := by
  unfold invokeTarget
  rw [member_resolves accepted member]
  rfl

theorem narrowing {environment : List Callable} {signature : Signature}
    {source target : List String} (accepted : agrees environment signature target = true)
    (nonempty : source ≠ []) (included : ∀ name ∈ source, name ∈ target) :
    agrees environment signature source = true := by
  simp only [agrees, Bool.and_eq_true, List.all_eq_true]
  constructor
  · cases source with
    | nil => exact False.elim (nonempty rfl)
    | cons _ _ => rfl
  · exact fun name member => beq_iff_eq.mpr (member_resolves accepted (included name member))

theorem missing_target_refused {environment : List Callable} {signature : Signature}
    {targets : List String} {name : String} (member : name ∈ targets)
    (missing : resolve environment name = none) : agrees environment signature targets = false := by
  cases h : agrees environment signature targets with
  | false => rfl
  | true => have := member_resolves h member; simp [missing] at this

private def reader : Signature := ⟨[.borrowed 4 false], false, .borrowed 0 0 4 false false, [], []⟩
private def writer : Signature := ⟨[.borrowed 4 true], false, .value, [], []⟩

example : agrees [⟨"a", reader⟩, ⟨"b", reader⟩] reader ["a", "b"] = true := by decide
example : agrees [⟨"a", reader⟩, ⟨"b", writer⟩] reader ["a", "b"] = false := by decide
example : agrees [⟨"a", reader⟩] reader [] = false := by decide
example : agrees [⟨"a", reader⟩] reader ["missing"] = false := by decide

example : acceptsSignature [⟨"a", reader⟩]
    { reader with result := .borrowed 0 0 4 false true } "a" = true := by decide
example : acceptsSignature [⟨"a", { reader with result := .borrowed 0 0 4 false true }⟩]
    reader "a" = false := by decide
example : acceptsSignature [⟨"a", writer⟩] reader "a" = false := by decide
example : acceptsSignature [] reader "missing" = false := by decide

#print axioms open_invocation_agrees

end Mettapedia.GSLT.LanguageDef.Ownership.Callbacks
