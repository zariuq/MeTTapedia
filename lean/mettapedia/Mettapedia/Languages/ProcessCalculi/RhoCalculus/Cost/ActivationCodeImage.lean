import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.Activation

/-!
# Purse-free admitted images of authored rho code

The partial wrapper below consumes the existing `Pattern` carrier.  It accepts
rho's zero, Drop, send, receive, parallel collection, bound names and quotation.
It does not synthesize purse constructors.  Each successful constructor case
builds a proof of empty purse inventory and structural agreement with the
existing cost erasure.  Structural fuel bounds compilation, not execution.

Free-variable interpretation, named binders and unrelated constructors are
outside this concrete wrapper's domain.  Admission also records an existing
declaration-derived rho sorting judgment.  Runtime support and binder safety
remain separate operational requirements; a sorted open quotation need not
belong to the closed runtime fragment.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationCodeImage

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.DerivedPresentationSyntax
open Mettapedia.Languages.ProcessCalculi.RhoCalculus
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.Canonical

universe u

/-- A name returned with constructor-local inventory and erasure proofs. -/
abbrev WrappedName {Ground : Type u} (encoding : SignatureNameEncoding Ground)
    (source : Pattern) :=
  {name : CostName Ground // name.purseInventory = 0 ∧
    StructuralCongruence (name.erase encoding) source}

/-- A term returned with constructor-local inventory and erasure proofs. -/
abbrev WrappedCode {Ground : Type u} (encoding : SignatureNameEncoding Ground)
    (source : Pattern) :=
  {term : CostTerm Ground // term.PurseFree ∧
    StructuralCongruence (term.erase encoding) source}

mutual
  /-- Wrap the actual rho name constructors, certifying each successful case. -/
  def wrapName {Ground : Type u} (encoding : SignatureNameEncoding Ground)
      (signatureFor : Pattern → CostSig Ground) :
      (fuel : Nat) → (source : Pattern) → Option (WrappedName encoding source)
    | 0, _ => none
    | _ + 1, .bvar index =>
        some ⟨.bvar index, rfl, .refl _⟩
    | fuel + 1, .apply "NQuote" [source] => do
        let code ← wrapCode encoding signatureFor fuel source
        return ⟨.quote code.val, code.property.1,
          applyCongruence_of_forall₂ "NQuote"
            (.cons code.property.2 .nil)⟩
    | _ + 1, _ => none

  /-- Wrap rho process constructors while keeping the original authored code
  as the source index of the checked erasure comparison. -/
  def wrapCode {Ground : Type u} (encoding : SignatureNameEncoding Ground)
      (signatureFor : Pattern → CostSig Ground) :
      (fuel : Nat) → (source : Pattern) → Option (WrappedCode encoding source)
    | 0, _ => none
    | _ + 1, .apply "PZero" [] =>
        some ⟨.nil, rfl, .par_empty⟩
    | fuel + 1, .apply "PDrop" [source] => do
        let name ← wrapName encoding signatureFor fuel source
        return ⟨.drop name.val, name.property.1,
          applyCongruence_of_forall₂ "PDrop" (.cons name.property.2 .nil)⟩
    | fuel + 1, source@(.apply "POutput" [channel, payload]) => do
        let name ← wrapName encoding signatureFor fuel channel
        let code ← wrapCode encoding signatureFor fuel payload
        return ⟨.signed (.send name.val code.val) (signatureFor source), by
          change name.val.purseInventory + code.val.purseInventory = 0
          rw [name.property.1, show code.val.purseInventory = 0 from code.property.1]
          rfl,
          applyCongruence_of_forall₂ "POutput"
            (.cons name.property.2 (.cons code.property.2 .nil))⟩
    | fuel + 1, source@(.apply "PInput" [channel, .lambda none body]) => do
        let name ← wrapName encoding signatureFor fuel channel
        let code ← wrapCode encoding signatureFor fuel body
        return ⟨.signed (.recv name.val code.val) (signatureFor source), by
          change name.val.purseInventory + code.val.purseInventory = 0
          rw [name.property.1, show code.val.purseInventory = 0 from code.property.1]
          rfl,
          applyCongruence_of_forall₂ "PInput"
            (.cons name.property.2
              (.cons (.lambda_cong none _ _ code.property.2) .nil))⟩
    | fuel + 1, .collection .hashBag sources none =>
        wrapList encoding signatureFor fuel sources
    | _ + 1, _ => none

  /-- Parallel-list compilation uses the existing binary cost parallel term.
  Its erasure proof accounts for the associated nested parallel bags. -/
  def wrapList {Ground : Type u} (encoding : SignatureNameEncoding Ground)
      (signatureFor : Pattern → CostSig Ground) :
      (fuel : Nat) → (sources : List Pattern) →
        Option (WrappedCode encoding (.collection .hashBag sources none))
    | 0, _ => none
    | _ + 1, [] => some ⟨.nil, rfl, .refl _⟩
    | fuel + 1, source :: sources => do
        let head ← wrapCode encoding signatureFor fuel source
        let tail ← wrapList encoding signatureFor fuel sources
        return ⟨.par head.val tail.val, by
          change head.val.purseInventory + tail.val.purseInventory = 0
          rw [show head.val.purseInventory = 0 from head.property.1,
            show tail.val.purseInventory = 0 from tail.property.1]
          rfl,
          StructuralCongruence.trans _ _ _
            (collectionCongruence_of_forall₂ .hashBag none
              (.cons head.property.2 (.cons tail.property.2 .nil)))
            (.par_flatten [source] sources)⟩
end

/-- A successful concrete compiler image, admitted against the existing rho
sorting judgment at its precise free and bound contexts. -/
def AuthoredCodeImage {Ground : Type u} (encoding : SignatureNameEncoding Ground)
    (signatureFor : Pattern → CostSig Ground) (free : FreeSortContext) (bound : List String)
    (source : Pattern) (term : CostTerm Ground) : Prop :=
  ProcWellSorted rhoReflectivePresentation free bound source ∧
    ∃ fuel, (wrapCode encoding signatureFor fuel source).map Subtype.val = some term

/-- Every admitted authored image contains no literal purse, even in quotes. -/
theorem AuthoredCodeImage.purseFree {Ground : Type u}
    {encoding : SignatureNameEncoding Ground} {signatureFor : Pattern → CostSig Ground}
    {free : FreeSortContext} {bound : List String} {source : Pattern}
    {term : CostTerm Ground}
    (image : AuthoredCodeImage encoding signatureFor free bound source term) : term.PurseFree := by
  obtain ⟨_typed, fuel, wrapped⟩ := image
  cases compiled : wrapCode encoding signatureFor fuel source with
  | none => simp [compiled] at wrapped
  | some result =>
      have equality : result.val = term := by simpa [compiled] using wrapped
      exact equality ▸ result.property.1

/-- Existing cost erasure recovers the authored process up to its existing
structural equations, including zero and parallel reassociation. -/
theorem AuthoredCodeImage.erase_structural {Ground : Type u}
    {encoding : SignatureNameEncoding Ground} {signatureFor : Pattern → CostSig Ground}
    {free : FreeSortContext} {bound : List String} {source : Pattern}
    {term : CostTerm Ground}
    (image : AuthoredCodeImage encoding signatureFor free bound source term) :
    StructuralCongruence (term.erase encoding) source := by
  obtain ⟨_typed, fuel, wrapped⟩ := image
  cases compiled : wrapCode encoding signatureFor fuel source with
  | none => simp [compiled] at wrapped
  | some result =>
      have equality : result.val = term := by simpa [compiled] using wrapped
      exact equality ▸ result.property.2

/-- The existing pure canonicalizer therefore observes the authored source
exactly, whenever the chosen signature encoding stays in pure rho syntax. -/
theorem AuthoredCodeImage.erase_canonical {Ground : Type u}
    {encoding : SignatureNameEncoding Ground} {signatureFor : Pattern → CostSig Ground}
    {free : FreeSortContext} {bound : List String} {source : Pattern}
    {term : CostTerm Ground}
    (image : AuthoredCodeImage encoding signatureFor free bound source term)
    (encodingPure : ∀ signature, HashSetFree (encoding signature)) :
    canonicalize (term.erase encoding) = canonicalize source := by
  have erasedPure := term.hashSetFree_erase encodingPure
  exact canonicalize_eq_of_structuralCongruence image.erase_structural erasedPure
    ((hashSetFree_iff_of_structuralCongruence image.erase_structural).mp erasedPure)

/-- Authored code compilation supplies no authority for any newly exposed
redex.  Every enabled firing still needs an external purse. -/
theorem AuthoredCodeImage.commSubst_unfunded_blocked {Ground : Type u}
    {encoding : SignatureNameEncoding Ground} {signatureFor : Pattern → CostSig Ground}
    {free : FreeSortContext} {bound : List String} {bodySource payloadSource : Pattern}
    {body payload : CostTerm Ground}
    (bodyImage : AuthoredCodeImage encoding signatureFor free bound bodySource body)
    (payloadImage : AuthoredCodeImage encoding signatureFor free [] payloadSource payload)
    (location : CostName Ground) (spend : CostSig Ground) (target : CostConfig Ground) :
    ¬ CostStep (body.commSubst payload).components location spend target :=
  CostTerm.code_substitution_unfunded_blocked bodyImage.purseFree payloadImage.purseFree
    location spend target

/-- Admitted image substitution inherits the checked operational closure.
Sorting alone is insufficient: runtime support and quote-aware binder safety
are retained as explicit requirements. -/
theorem AuthoredCodeImage.commSubst_admission {Ground : Type u}
    {encoding : SignatureNameEncoding Ground} {signatureFor : Pattern → CostSig Ground}
    {free : FreeSortContext} {bound : List String} {bodySource payloadSource : Pattern}
    {body payload : CostTerm Ground}
    (bodyImage : AuthoredCodeImage encoding signatureFor free bound bodySource body)
    (payloadImage : AuthoredCodeImage encoding signatureFor free [] payloadSource payload)
    (bodySupported : body.RuntimeSupported) (payloadSupported : payload.RuntimeSupported)
    (bodySafe : body.BinderSafeAt 1) (payloadSafe : payload.BinderSafe) :
    (body.commSubst payload).RuntimeSupported ∧
      (body.commSubst payload).BinderSafe ∧ (body.commSubst payload).PurseFree :=
  CostTerm.code_admission_commSubst bodySupported payloadSupported bodySafe payloadSafe
    bodyImage.purseFree payloadImage.purseFree

def authoredCopyReceiver : Pattern :=
  .apply "PInput" [.apply "NQuote" [.apply "PZero" []],
    .lambda none (.collection .hashBag
      [.apply "PDrop" [.bvar 0], .apply "PDrop" [.bvar 0]] none)]

def authoredNonemptyPayload : Pattern :=
  .apply "POutput" [.apply "NQuote" [.apply "PZero" []], .apply "PZero" []]

def exampleEncoding : SignatureNameEncoding String :=
  fun _ => .apply "NQuote" [.apply "PZero" []]

def exampleSeal : Pattern → CostSig String := fun _ => {"a"}

def wrappedCopyReceiver : CostTerm String :=
  .signed (.recv (.quote .nil)
    (.par (.drop (.bvar 0)) (.par (.drop (.bvar 0)) .nil))) {"a"}

def wrappedNonemptyPayload : CostTerm String :=
  .signed (.send (.quote .nil) .nil) {"a"}

/-- Positive: the nontrivial copying receiver is authored and well sorted. -/
theorem authored_copy_receiver_sorted :
    ProcWellSorted rhoReflectivePresentation FreeSortContext.empty [] authoredCopyReceiver := by
  exact .input (.quote .unit)
    (.parallel (.cons (.drop (.bvar rfl)) (.cons (.drop (.bvar rfl)) .nil)))

/-- Positive: a communicated output is nonempty authored process code. -/
theorem authored_nonempty_payload_sorted :
    ProcWellSorted rhoReflectivePresentation FreeSortContext.empty [] authoredNonemptyPayload :=
  .output (.quote .unit) .unit

/-- Positive: both nontrivial authored terms have genuine compiler images. -/
theorem authored_examples_compile :
    (wrapCode exampleEncoding exampleSeal 12 authoredCopyReceiver).isSome = true ∧
      (wrapCode exampleEncoding exampleSeal 12 authoredNonemptyPayload).isSome = true := by
  decide +kernel

/-- The successful compiler values are actual sealed receiver and output
syntax, not merely an accepted-input Boolean. -/
theorem authored_examples_compile_exact :
    (wrapCode exampleEncoding exampleSeal 12 authoredCopyReceiver).map Subtype.val =
        some wrappedCopyReceiver ∧
      (wrapCode exampleEncoding exampleSeal 12 authoredNonemptyPayload).map Subtype.val =
        some wrappedNonemptyPayload := by
  decide +kernel

/-- Both nonempty authored examples inhabit the named admitted image. -/
theorem authored_examples_admitted :
    AuthoredCodeImage exampleEncoding exampleSeal FreeSortContext.empty []
        authoredCopyReceiver wrappedCopyReceiver ∧
      AuthoredCodeImage exampleEncoding exampleSeal FreeSortContext.empty []
        authoredNonemptyPayload wrappedNonemptyPayload :=
  ⟨⟨authored_copy_receiver_sorted, 12, authored_examples_compile_exact.1⟩,
    ⟨authored_nonempty_payload_sorted, 12, authored_examples_compile_exact.2⟩⟩

/-- The two nonempty compiler values also satisfy the independent positive
runtime and closed-scope requirements. -/
theorem authored_examples_runtime_admitted :
    wrappedCopyReceiver.RuntimeSupported ∧ wrappedCopyReceiver.BinderSafe ∧
      wrappedNonemptyPayload.RuntimeSupported ∧ wrappedNonemptyPayload.BinderSafe := by
  refine ⟨?_, .signed (.recv (.quote .nil)
    (.par (.drop (.bvar (by decide))) (.par (.drop (.bvar (by decide))) .nil))),
    ?_, .signed (.send (.quote .nil) .nil)⟩
  all_goals
    simp [wrappedCopyReceiver, wrappedNonemptyPayload, CostTerm.RuntimeSupported,
      CostProc.RuntimeSupported, CostName.RuntimeSupported, CostSig.RuntimeValid]

/-- Negative: the authored purse spelling has no code-only image. -/
theorem purse_constructor_not_compiled (fuel : Nat) :
    wrapCode exampleEncoding exampleSeal fuel
      (.apply "Purse" [.apply "NQuote" [.apply "PZero" []]]) = none := by
  cases fuel <;> rfl

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationCodeImage
