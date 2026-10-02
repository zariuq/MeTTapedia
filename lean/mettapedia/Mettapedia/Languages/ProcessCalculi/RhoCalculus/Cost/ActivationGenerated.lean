import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.AdministrativeFrame
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationCodeImage
import Mettapedia.GSLT.LanguageDef.CostAuthoredAtom
import Mettapedia.GSLT.LanguageDef.CostInteraction
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefContinuedInteraction

/-!
# Located interpretation of asynchronous generated Cost syntax

Closed signature syntax denotes one opaque literal authority atom. The generated
unit denotes a positive head and a product retains its own exact syntax key;
this is separate from the signature account monoid.

The decoder consumes actual generated constructors and invents no seals.
Quotations reset the binder scope; base quotation currently accepts zero.
Parallel cores contain exactly the selected pair, with no collection rest.
Funding locations are retained interpretation indices.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationGenerated

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.DerivedPresentationSyntax
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.Languages.ProcessCalculi.RhoCalculus
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.Canonical
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefContinuedInteraction

abbrev LiteralAuthority := Pattern

abbrev TypedSignature (source : Pattern) :=
  {signature : CostSig LiteralAuthority // signature = {source} ∧
    HasType rhoCIGSLT.costWholeLanguage FreeTypeContext.empty [] source
      (.base costSignatureSortName)}

/-- The generated language's actual sort checker admits closed authority syntax. -/
def signature? (source : Pattern) : Option (TypedSignature source) :=
  if typed : checkHasType rhoCIGSLT.costWholeLanguage FreeTypeContext.empty []
      source (.base costSignatureSortName) = true then
    some ⟨{source}, rfl, checkHasType_sound typed⟩
  else none

theorem TypedSignature.positive {source : Pattern} (signature : TypedSignature source) :
    signature.val.RuntimeValid := by
  rw [signature.property.1]
  exact Multiset.singleton_ne_zero source

theorem literal_authority_injective :
    Function.Injective (fun source : Pattern => ({source} : CostSig LiteralAuthority)) := by
  intro left right same
  exact Multiset.singleton_inj.mp same

def eraseConstructor (constructor : String) : String :=
  (decodeCostStaticConstructor .base constructor).getD
    ((decodeCostStaticConstructor .wrapped constructor).getD constructor)

mutual
  /-- Independent computational readout: remove colours, seals and funding,
  interpreting contact as pure parallel. -/
  def eraseGenerated : Pattern → Pattern
    | .apply "$cost:apparatus-constructor:signed" [process, _signature] =>
        eraseGenerated process
    | .apply "$cost:apparatus-constructor:funding" [_stack] =>
        .collection .hashBag [] none
    | .apply "$cost:apparatus-constructor:contact" [left, right] =>
        .collection .hashBag [eraseGenerated left, eraseGenerated right] none
    | .apply constructor arguments =>
        .apply (eraseConstructor constructor) (eraseGeneratedList arguments)
    | .bvar index => .bvar index
    | .fvar name => .fvar name
    | .lambda binder body => .lambda binder (eraseGenerated body)
    | .multiLambda arity binders body => .multiLambda arity binders (eraseGenerated body)
    | .subst body replacement => .subst (eraseGenerated body) (eraseGenerated replacement)
    | .collection kind elements rest => .collection kind (eraseGeneratedList elements) rest

  def eraseGeneratedList : List Pattern → List Pattern
    | [] => []
    | source :: sources => eraseGenerated source :: eraseGeneratedList sources
end

abbrev DecodedName (depth : Nat) (source : Pattern) :=
  {name : CostName LiteralAuthority // name.purseInventory = 0 ∧
    name.BinderSafeAt depth ∧ name.RuntimeSupported ∧
    ∀ encoding, StructuralCongruence (name.erase encoding) (eraseGenerated source)}

abbrev DecodedCode (depth : Nat) (source : Pattern) :=
  {term : CostTerm LiteralAuthority // term.PurseFree ∧
    term.BinderSafeAt depth ∧ term.RuntimeSupported ∧
    ∀ encoding, StructuralCongruence (term.erase encoding) (eraseGenerated source)}

abbrev DecodedProc (depth : Nat) (source : Pattern) :=
  {process : CostProc LiteralAuthority // process.purseInventory = 0 ∧
    process.BinderSafeAt depth ∧ process.RuntimeSupported ∧
    ∀ encoding, StructuralCongruence (process.erase encoding) (eraseGenerated source)}

mutual
  def name? : (fuel depth : Nat) → (source : Pattern) → Option (DecodedName depth source)
    | 0, _, _ => none
    | _ + 1, depth, .bvar index =>
        if bound : index < depth then
          some ⟨.bvar index, rfl, .bvar bound, trivial, fun _ => .refl _⟩
        else none
    | _ + 1, _depth,
        .apply "$cost:base-constructor:NQuote" [.apply "$cost:base-constructor:PZero" []] =>
        some ⟨.quote .nil, rfl, .quote .nil, trivial, by
          intro encoding
          change StructuralCongruence (.apply "NQuote" [.collection .hashBag [] none])
            (.apply "NQuote" [.apply "PZero" []])
          exact applyCongruence_of_forall₂ "NQuote" (.cons .par_empty .nil)⟩
    | fuel + 1, _depth, .apply "$cost:wrapped-constructor:NQuote" [source] => do
        let code ← code? fuel 0 source
        return ⟨.quote code.val, code.property.1, .quote code.property.2.1,
          code.property.2.2.1, by
            intro encoding
            change StructuralCongruence (.apply "NQuote" [code.val.erase encoding])
              (.apply "NQuote" [eraseGenerated source])
            exact applyCongruence_of_forall₂ "NQuote"
              (.cons (code.property.2.2.2 encoding) .nil)⟩
    | _ + 1, _, _ => none

  def code? : (fuel depth : Nat) → (source : Pattern) → Option (DecodedCode depth source)
    | 0, _, _ => none
    | _ + 1, _depth, .apply "$cost:wrapped-constructor:PZero" [] =>
        some ⟨.nil, rfl, .nil, trivial, fun _ => .par_empty⟩
    | fuel + 1, depth, .apply "$cost:wrapped-constructor:PDrop" [source] => do
        let name ← name? fuel depth source
        return ⟨.drop name.val, name.property.1, .drop name.property.2.1,
          name.property.2.2.1, by
            intro encoding
            change StructuralCongruence (.apply "PDrop" [name.val.erase encoding])
              (.apply "PDrop" [eraseGenerated source])
            exact applyCongruence_of_forall₂ "PDrop"
              (.cons (name.property.2.2.2 encoding) .nil)⟩
    | fuel + 1, depth, .apply "$cost:apparatus-constructor:signed" [source, authority] => do
        let signature ← signature? authority
        let process ← proc? fuel depth source
        return ⟨.signed process.val signature.val, process.property.1,
          .signed process.property.2.1,
          ⟨process.property.2.2.1, signature.positive⟩,
          process.property.2.2.2⟩
    | fuel + 1, depth, .collection .hashBag sources none => codeList? fuel depth sources
    | _ + 1, _, _ => none

  def proc? : (fuel depth : Nat) → (source : Pattern) → Option (DecodedProc depth source)
    | 0, _, _ => none
    | _ + 1, _depth, .apply "$cost:base-constructor:PZero" [] =>
        some ⟨.nil, rfl, .nil, trivial, fun _ => .par_empty⟩
    | fuel + 1, depth, .apply "$cost:base-constructor:POutput" [channel, payload] => do
        let name ← name? fuel depth channel
        let code ← code? fuel depth payload
        return ⟨.send name.val code.val, by
          change name.val.purseInventory + code.val.purseInventory = 0
          rw [name.property.1, show code.val.purseInventory = 0 from code.property.1]
          rfl,
          .send name.property.2.1 code.property.2.1,
          ⟨name.property.2.2.1, code.property.2.2.1⟩, by
            intro encoding
            change StructuralCongruence
              (.apply "POutput" [name.val.erase encoding, code.val.erase encoding])
              (.apply "POutput" [eraseGenerated channel, eraseGenerated payload])
            exact applyCongruence_of_forall₂ "POutput"
              (.cons (name.property.2.2.2 encoding) (.cons (code.property.2.2.2 encoding) .nil))⟩
    | fuel + 1, depth,
        .apply "$cost:base-constructor:PInput" [channel, .lambda none body] => do
        let name ← name? fuel depth channel
        let code ← code? fuel (depth + 1) body
        return ⟨.recv name.val code.val, by
          change name.val.purseInventory + code.val.purseInventory = 0
          rw [name.property.1, show code.val.purseInventory = 0 from code.property.1]
          rfl,
          .recv name.property.2.1 code.property.2.1,
          ⟨name.property.2.2.1, code.property.2.2.1⟩, by
            intro encoding
            change StructuralCongruence
              (.apply "PInput" [name.val.erase encoding, .lambda none (code.val.erase encoding)])
              (.apply "PInput" [eraseGenerated channel, .lambda none (eraseGenerated body)])
            exact applyCongruence_of_forall₂ "PInput"
              (.cons (name.property.2.2.2 encoding)
                (.cons (.lambda_cong none _ _ (code.property.2.2.2 encoding)) .nil))⟩
    | fuel + 1, depth, .collection .hashBag [left, right] none => do
        let first ← proc? fuel depth left
        let second ← proc? fuel depth right
        return ⟨.par first.val second.val, by
          change first.val.purseInventory + second.val.purseInventory = 0
          rw [first.property.1, second.property.1]
          rfl,
          .par first.property.2.1 second.property.2.1,
          ⟨first.property.2.2.1, second.property.2.2.1⟩, by
            intro encoding
            change StructuralCongruence
              (.collection .hashBag [first.val.erase encoding, second.val.erase encoding] none)
              (.collection .hashBag [eraseGenerated left, eraseGenerated right] none)
            exact collectionCongruence_of_forall₂ .hashBag none
              (.cons (first.property.2.2.2 encoding) (.cons (second.property.2.2.2 encoding) .nil))⟩
    | _ + 1, _, _ => none

  def codeList? : (fuel depth : Nat) → (sources : List Pattern) →
      Option (DecodedCode depth (.collection .hashBag sources none))
    | 0, _, _ => none
    | _ + 1, _depth, [] => some ⟨.nil, rfl, .nil, trivial, fun _ => .refl _⟩
    | fuel + 1, depth, source :: sources => do
        let head ← code? fuel depth source
        let tail ← codeList? fuel depth sources
        return ⟨.par head.val tail.val, by
          change head.val.purseInventory + tail.val.purseInventory = 0
          rw [show head.val.purseInventory = 0 from head.property.1,
            show tail.val.purseInventory = 0 from tail.property.1]
          rfl,
          .par head.property.2.1 tail.property.2.1,
          ⟨head.property.2.2.1, tail.property.2.2.1⟩, by
            intro encoding
            exact StructuralCongruence.trans _ _ _
              (collectionCongruence_of_forall₂ .hashBag none
                (.cons (head.property.2.2.2 encoding) (.cons (tail.property.2.2.2 encoding) .nil)))
              (.par_flatten [eraseGenerated source] (eraseGeneratedList sources))⟩
end

/-- Admission adds the existing generated language's actual typing judgment. -/
def GeneratedCodeImage (depth : Nat) (source : Pattern) (term : CostTerm LiteralAuthority) : Prop :=
  HasType rhoCIGSLT.costWholeLanguage FreeTypeContext.empty
    (List.replicate depth (.base (costBaseSortName "Name"))) source (.base costWrappedSortName) ∧
  ∃ fuel, (code? fuel depth source).map Subtype.val = some term

theorem GeneratedCodeImage.purseFree {depth : Nat} {source : Pattern}
    {term : CostTerm LiteralAuthority} (image : GeneratedCodeImage depth source term) :
    term.PurseFree := by
  obtain ⟨fuel, found⟩ := image.2
  obtain ⟨decoded, _parsed, same⟩ := Option.map_eq_some_iff.mp found
  subst term
  exact decoded.property.1

theorem GeneratedCodeImage.binderSafe {depth : Nat} {source : Pattern}
    {term : CostTerm LiteralAuthority} (image : GeneratedCodeImage depth source term) :
    term.BinderSafeAt depth := by
  obtain ⟨fuel, found⟩ := image.2
  obtain ⟨decoded, _parsed, same⟩ := Option.map_eq_some_iff.mp found
  subst term
  exact decoded.property.2.1

theorem GeneratedCodeImage.runtimeSupported {depth : Nat} {source : Pattern}
    {term : CostTerm LiteralAuthority} (image : GeneratedCodeImage depth source term) :
    term.RuntimeSupported := by
  obtain ⟨fuel, found⟩ := image.2
  obtain ⟨decoded, _parsed, same⟩ := Option.map_eq_some_iff.mp found
  subst term
  exact decoded.property.2.2.1

theorem GeneratedCodeImage.erase_structural {depth : Nat} {source : Pattern}
    {term : CostTerm LiteralAuthority} (image : GeneratedCodeImage depth source term)
    (encoding : SignatureNameEncoding LiteralAuthority) :
    StructuralCongruence (term.erase encoding) (eraseGenerated source) := by
  obtain ⟨fuel, found⟩ := image.2
  obtain ⟨decoded, _parsed, same⟩ := Option.map_eq_some_iff.mp found
  subst term
  exact decoded.property.2.2.2 encoding

abbrev DecodedStack (_source : Pattern) :=
  {stack : CostStack LiteralAuthority // stack.RuntimeSupported}

def stack? : (fuel : Nat) → (source : Pattern) → Option (DecodedStack source)
  | 0, _ => none
  | _ + 1, .apply "$cost:apparatus-constructor:token-stack-empty" [] =>
      some ⟨.empty, trivial⟩
  | fuel + 1, .apply "$cost:apparatus-constructor:token-stack-cons" [head, tail] => do
      let signature ← signature? head
      let stack ← stack? fuel tail
      return ⟨.cons signature.val stack.val, signature.positive, stack.property⟩
  | _ + 1, _ => none

abbrev DecodedConfig (source : Pattern) :=
  {term : CostTerm LiteralAuthority // term.components.ResourceSeparated ∧
    term.BinderSafeAt 0 ∧ term.RuntimeSupported ∧
    ∀ encoding, StructuralCongruence (term.erase encoding) (eraseGenerated source)}

mutual
  /-- Actual nested contacts remain transparent parallel contexts. This
  interpretation preserves funded steps; it does not impose purse ownership. -/
  def config? (location : CostName LiteralAuthority) (locationFree : location.purseInventory = 0)
      (locationSupported : location.RuntimeSupported) :
      (fuel : Nat) → (source : Pattern) → Option (DecodedConfig source)
    | 0, _ => none
    | fuel + 1, .apply "$cost:apparatus-constructor:contact"
        [left, .apply "$cost:apparatus-constructor:funding" [stackSource]] => do
        let code ← config? location locationFree locationSupported fuel left
        let stack ← stack? fuel stackSource
        return ⟨locatedContact location code.val stack.val, by
          change (code.val.components + (CostTerm.purse location stack.val ::ₘ 0)).ResourceSeparated
          rw [CostConfig.resourceSeparated_add_iff, CostConfig.resourceSeparated_singleton_iff]
          exact ⟨code.property.1, locationFree⟩,
          .par code.property.2.1 .purse,
          ⟨code.property.2.2.1, locationSupported, stack.property⟩, by
            intro encoding
            change StructuralCongruence
              (.collection .hashBag [code.val.erase encoding, .collection .hashBag [] none] none)
              (.collection .hashBag [eraseGenerated left, .collection .hashBag [] none] none)
            exact collectionCongruence_of_forall₂ .hashBag none
              (.cons (code.property.2.2.2 encoding) (.cons (.refl _) .nil))⟩
    | fuel + 1, .collection .hashBag sources none =>
        configList? location locationFree locationSupported fuel sources
    | fuel + 1, source => do
        let code ← code? fuel 0 source
        return ⟨code.val, code.property.1.components_resourceSeparated,
          code.property.2.1, code.property.2.2.1, code.property.2.2.2⟩

  def configList? (location : CostName LiteralAuthority) (locationFree : location.purseInventory = 0)
      (locationSupported : location.RuntimeSupported) : (fuel : Nat) → (sources : List Pattern) →
      Option (DecodedConfig (.collection .hashBag sources none))
    | 0, _ => none
    | _ + 1, [] => some ⟨.nil, by simp [CostTerm.components, CostConfig.ResourceSeparated],
        .nil, trivial, fun _ => .refl _⟩
    | fuel + 1, source :: sources => do
        let head ← config? location locationFree locationSupported fuel source
        let tail ← configList? location locationFree locationSupported fuel sources
        return ⟨.par head.val tail.val, by
          change (head.val.components + tail.val.components).ResourceSeparated
          exact (CostConfig.resourceSeparated_add_iff _ _).mpr ⟨head.property.1, tail.property.1⟩,
          .par head.property.2.1 tail.property.2.1,
          ⟨head.property.2.2.1, tail.property.2.2.1⟩, by
            intro encoding
            exact StructuralCongruence.trans _ _ _
              (collectionCongruence_of_forall₂ .hashBag none
                (.cons (head.property.2.2.2 encoding) (.cons (tail.property.2.2.2 encoding) .nil)))
              (.par_flatten [eraseGenerated source] (eraseGeneratedList sources))⟩
end

/-- Successful configuration interpretation admitted against the existing
generated wrapped sort, with the nominal location retained as an index. -/
def GeneratedConfigImage (location : CostName LiteralAuthority) (source : Pattern)
    (term : CostTerm LiteralAuthority) : Prop :=
  HasType rhoCIGSLT.costWholeLanguage FreeTypeContext.empty [] source (.base costWrappedSortName) ∧
  ∃ locationFree locationSupported fuel,
    (config? location locationFree locationSupported fuel source).map Subtype.val = some term

theorem GeneratedConfigImage.resourceSeparated {location : CostName LiteralAuthority}
    {source : Pattern} {term : CostTerm LiteralAuthority}
    (image : GeneratedConfigImage location source term) : term.components.ResourceSeparated := by
  obtain ⟨locationFree, locationSupported, fuel, found⟩ := image.2
  obtain ⟨decoded, _parsed, same⟩ := Option.map_eq_some_iff.mp found
  subst term
  exact decoded.property.1

theorem GeneratedConfigImage.binderSafe {location : CostName LiteralAuthority}
    {source : Pattern} {term : CostTerm LiteralAuthority}
    (image : GeneratedConfigImage location source term) : term.BinderSafe := by
  obtain ⟨locationFree, locationSupported, fuel, found⟩ := image.2
  obtain ⟨decoded, _parsed, same⟩ := Option.map_eq_some_iff.mp found
  subst term
  exact decoded.property.2.1

theorem GeneratedConfigImage.runtimeSupported {location : CostName LiteralAuthority}
    {source : Pattern} {term : CostTerm LiteralAuthority}
    (image : GeneratedConfigImage location source term) : term.RuntimeSupported := by
  obtain ⟨locationFree, locationSupported, fuel, found⟩ := image.2
  obtain ⟨decoded, _parsed, same⟩ := Option.map_eq_some_iff.mp found
  subst term
  exact decoded.property.2.2.1

theorem GeneratedConfigImage.erase_structural {location : CostName LiteralAuthority}
    {source : Pattern} {term : CostTerm LiteralAuthority}
    (image : GeneratedConfigImage location source term) (encoding : SignatureNameEncoding LiteralAuthority) :
    StructuralCongruence (term.erase encoding) (eraseGenerated source) := by
  obtain ⟨locationFree, locationSupported, fuel, found⟩ := image.2
  obtain ⟨decoded, _parsed, same⟩ := Option.map_eq_some_iff.mp found
  subst term
  exact decoded.property.2.2.2 encoding

/-- Actual generated code images satisfy the existing communication admission
invariant; replacing a bound name cannot introduce purse authority. -/
theorem GeneratedCodeImage.commSubst_admission {bodySource payloadSource : Pattern}
    {body payload : CostTerm LiteralAuthority}
    (bodyImage : GeneratedCodeImage 1 bodySource body)
    (payloadImage : GeneratedCodeImage 0 payloadSource payload) :
    (body.commSubst payload).RuntimeSupported ∧ (body.commSubst payload).BinderSafe ∧
      (body.commSubst payload).PurseFree :=
  CostTerm.code_admission_commSubst bodyImage.runtimeSupported payloadImage.runtimeSupported
    bodyImage.binderSafe payloadImage.binderSafe bodyImage.purseFree payloadImage.purseFree

theorem GeneratedCodeImage.commSubst_unfunded {bodySource payloadSource : Pattern}
    {body payload : CostTerm LiteralAuthority}
    (bodyImage : GeneratedCodeImage 1 bodySource body)
    (payloadImage : GeneratedCodeImage 0 payloadSource payload)
    (location : CostName LiteralAuthority) (spend : CostSig LiteralAuthority)
    (target : CostConfig LiteralAuthority) :
    ¬ CostStep (body.commSubst payload).components location spend target :=
  CostTerm.code_substitution_unfunded_blocked bodyImage.purseFree payloadImage.purseFree
    location spend target

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationGenerated

