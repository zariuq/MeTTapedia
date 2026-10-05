import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.AdministrativeFrame
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationCodeImage
import Mettapedia.GSLT.LanguageDef.CostAuthoredAtom
import Mettapedia.GSLT.LanguageDef.CostInteraction
import Mettapedia.GSLT.LanguageDef.ClosedSchemaInstantiation
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefContinuedInteraction

/-!
# The runtime image of generated Cost syntax

The Cost construction on rho generates a syntax: coloured rho constructors, signatures, signed
processes, token stacks, funding and contact. The hand-written runtime has its own terms. This
module relates the two.

* The image. `NameImage`, `CodeImage`, `ProcImage`, `CodeListImage`, `StackImage`, `ConfigImage`
  and `ConfigListImage` say which runtime term a piece of generated syntax stands for. They are
  the definition; everything else in this module is derived from them.
* What every image satisfies: no purse inside code, binders in scope, the runtime-supported
  fragment, the erased pure-rho process, and the type in the generated language.
* The readout. `readName`, `readCode`, `readProc`, `readCodeList`, `readStack`, `readConfig` and
  `readConfigList` compute the image, with a fuel bound on the depth of the syntax. Success of the
  readout is the image (`readCode_image`, `CodeImage.read_eventually`, and their companions).
* The same readout with its guarantees attached: `name?`, `code?`, `proc?`, `codeList?`,
  `stack?`, `config?`, `configList?`.

A closed signature is one literal authority: the whole signature syntax is the key. The unit is a
positive key and a product keeps its own syntax. Quotation resets the binder scope. A parallel
core is exactly a pair. A generated funding has no channel, so the channel of every purse is a
parameter of the configuration image.
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

/-! ## The image -/

mutual
  /-- The runtime name a generated name stands for, under `depth` receiver binders. -/
  inductive NameImage : Nat → Pattern → CostName LiteralAuthority → Prop where
    | bvar {depth index} (bound : index < depth) :
        NameImage depth (.bvar index) (.bvar index)
    | baseZeroQuote {depth} : NameImage depth
        (.apply "$cost:base-constructor:NQuote" [.apply "$cost:base-constructor:PZero" []])
        (.quote .nil)
    | quote {depth source term} (code : CodeImage 0 source term) :
        NameImage depth (.apply "$cost:wrapped-constructor:NQuote" [source]) (.quote term)

  /-- The runtime term a piece of generated code stands for. Code contains no funding. -/
  inductive CodeImage : Nat → Pattern → CostTerm LiteralAuthority → Prop where
    | zero {depth} : CodeImage depth (.apply "$cost:wrapped-constructor:PZero" []) .nil
    | drop {depth source name} (parsed : NameImage depth source name) :
        CodeImage depth (.apply "$cost:wrapped-constructor:PDrop" [source]) (.drop name)
    | signed {depth core source process} (signature : TypedSignature source) (accepted : signature? source = some signature)
        (parsed : ProcImage depth core process) :
        CodeImage depth (.apply "$cost:apparatus-constructor:signed" [core, source])
          (.signed process signature.val)
    | collection {depth sources term} (parsed : CodeListImage depth sources term) :
        CodeImage depth (.collection .hashBag sources none) term

  /-- The runtime process under a signature: zero, a send, a receive, or exactly a pair. -/
  inductive ProcImage : Nat → Pattern → CostProc LiteralAuthority → Prop where
    | zero {depth} : ProcImage depth (.apply "$cost:base-constructor:PZero" []) .nil
    | send {depth channel payload name term}
        (channelImage : NameImage depth channel name) (payloadImage : CodeImage depth payload term) :
        ProcImage depth (.apply "$cost:base-constructor:POutput" [channel, payload]) (.send name term)
    | recv {depth channel body name term}
        (channelImage : NameImage depth channel name) (bodyImage : CodeImage (depth + 1) body term) :
        ProcImage depth (.apply "$cost:base-constructor:PInput" [channel, .lambda none body])
          (.recv name term)
    | pair {depth left right first second}
        (leftImage : ProcImage depth left first) (rightImage : ProcImage depth right second) :
        ProcImage depth (.collection .hashBag [left, right] none) (.par first second)

  /-- A bag of generated code is the parallel composition of the images of its members. -/
  inductive CodeListImage : Nat → List Pattern → CostTerm LiteralAuthority → Prop where
    | nil {depth} : CodeListImage depth [] .nil
    | cons {depth source sources head tail}
        (headImage : CodeImage depth source head) (tailImage : CodeListImage depth sources tail) :
        CodeListImage depth (source :: sources) (.par head tail)
end

/-- The runtime purse stack a generated token stack stands for: one checked signature per cell. -/
inductive StackImage : Pattern → CostStack LiteralAuthority → Prop
  | empty : StackImage (.apply "$cost:apparatus-constructor:token-stack-empty" []) .empty
  | cons {head tail : Pattern} {stack : CostStack LiteralAuthority}
      (signature : TypedSignature head) (accepted : signature? head = some signature)
      (rest : StackImage tail stack) :
      StackImage (.apply "$cost:apparatus-constructor:token-stack-cons" [head, tail])
        (.cons signature.val stack)

mutual
  /-- The runtime configuration a generated term stands for when every funding is a purse at
  `location`. A contact is code beside a purse; a bag is a parallel composition. -/
  inductive ConfigImage (location : CostName LiteralAuthority) :
      Pattern → CostTerm LiteralAuthority → Prop where
    | zero : ConfigImage location (.apply "$cost:wrapped-constructor:PZero" []) .nil
    | drop {source name} (image : NameImage 0 source name) :
        ConfigImage location (.apply "$cost:wrapped-constructor:PDrop" [source]) (.drop name)
    | signed {source authority process} (signature : TypedSignature authority)
        (accepted : signature? authority = some signature) (image : ProcImage 0 source process) :
        ConfigImage location (.apply "$cost:apparatus-constructor:signed" [source, authority])
          (.signed process signature.val)
    | contact {left stackSource code stack}
        (leftImage : ConfigImage location left code) (stackImage : StackImage stackSource stack) :
        ConfigImage location (.apply "$cost:apparatus-constructor:contact"
          [left, .apply "$cost:apparatus-constructor:funding" [stackSource]])
          (locatedContact location code stack)
    | collection {sources term} (image : ConfigListImage location sources term) :
        ConfigImage location (.collection .hashBag sources none) term

  inductive ConfigListImage (location : CostName LiteralAuthority) :
      List Pattern → CostTerm LiteralAuthority → Prop where
    | nil : ConfigListImage location [] .nil
    | cons {source sources head tail} (headImage : ConfigImage location source head)
        (tailImage : ConfigListImage location sources tail) :
        ConfigListImage location (source :: sources) (.par head tail)
end

mutual
  /-- Closed code is a configuration at any location. -/
  theorem CodeImage.toConfigImage {source : Pattern} {term : CostTerm LiteralAuthority}
      (image : CodeImage 0 source term) (location : CostName LiteralAuthority) :
      ConfigImage location source term := by
    cases image with
    | zero => exact .zero
    | drop name => exact .drop name
    | signed signature accepted process => exact .signed signature accepted process
    | collection codes => exact .collection (codes.toConfigListImage location)

  theorem CodeListImage.toConfigListImage {sources : List Pattern} {term : CostTerm LiteralAuthority}
      (image : CodeListImage 0 sources term) (location : CostName LiteralAuthority) :
      ConfigListImage location sources term := by
    cases image with
    | nil => exact .nil
    | cons head tail => exact .cons (head.toConfigImage location) (tail.toConfigListImage location)
end

/-! ## What every image satisfies -/

mutual
  theorem NameImage.purseInventory_zero {depth : Nat} {source : Pattern}
      {name : CostName LiteralAuthority} (image : NameImage depth source name) :
      name.purseInventory = 0 := by
    cases image with
    | bvar bound => rfl
    | baseZeroQuote => rfl
    | quote code => exact code.purseFree

  /-- Code contains no purse, also not under a quote or behind a receive. -/
  theorem CodeImage.purseFree {depth : Nat} {source : Pattern}
      {term : CostTerm LiteralAuthority} (image : CodeImage depth source term) : term.PurseFree := by
    cases image with
    | zero => rfl
    | drop name => exact name.purseInventory_zero
    | signed signature accepted process => exact process.purseInventory_zero
    | collection codes => exact codes.purseFree

  theorem ProcImage.purseInventory_zero {depth : Nat} {source : Pattern}
      {process : CostProc LiteralAuthority} (image : ProcImage depth source process) :
      process.purseInventory = 0 := by
    cases image with
    | zero => rfl
    | send name code =>
      have codeFree : CostTerm.purseInventory _ = 0 := code.purseFree
      change _ + _ = 0
      rw [name.purseInventory_zero, codeFree]
      rfl
    | recv name code =>
      have codeFree : CostTerm.purseInventory _ = 0 := code.purseFree
      change _ + _ = 0
      rw [name.purseInventory_zero, codeFree]
      rfl
    | pair left right =>
      change _ + _ = 0
      rw [left.purseInventory_zero, right.purseInventory_zero]
      rfl

  theorem CodeListImage.purseFree {depth : Nat} {sources : List Pattern}
      {term : CostTerm LiteralAuthority} (image : CodeListImage depth sources term) :
      term.PurseFree := by
    cases image with
    | nil => rfl
    | cons head tail =>
      have headFree : CostTerm.purseInventory _ = 0 := head.purseFree
      have tailFree : CostTerm.purseInventory _ = 0 := tail.purseFree
      change _ + _ = 0
      rw [headFree, tailFree]
      rfl
end

mutual
  theorem NameImage.binderSafe {depth : Nat} {source : Pattern}
      {name : CostName LiteralAuthority} (image : NameImage depth source name) :
      name.BinderSafeAt depth := by
    cases image with
    | bvar bound => exact .bvar bound
    | baseZeroQuote => exact .quote .nil
    | quote code => exact .quote code.binderSafe

  /-- Every bound name of an image is below the number of enclosing receivers. -/
  theorem CodeImage.binderSafe {depth : Nat} {source : Pattern}
      {term : CostTerm LiteralAuthority} (image : CodeImage depth source term) :
      term.BinderSafeAt depth := by
    cases image with
    | zero => exact .nil
    | drop name => exact .drop name.binderSafe
    | signed signature accepted process => exact .signed process.binderSafe
    | collection codes => exact codes.binderSafe

  theorem ProcImage.binderSafe {depth : Nat} {source : Pattern}
      {process : CostProc LiteralAuthority} (image : ProcImage depth source process) :
      process.BinderSafeAt depth := by
    cases image with
    | zero => exact .nil
    | send name code => exact .send name.binderSafe code.binderSafe
    | recv name code => exact .recv name.binderSafe code.binderSafe
    | pair left right => exact .par left.binderSafe right.binderSafe

  theorem CodeListImage.binderSafe {depth : Nat} {sources : List Pattern}
      {term : CostTerm LiteralAuthority} (image : CodeListImage depth sources term) :
      term.BinderSafeAt depth := by
    cases image with
    | nil => exact .nil
    | cons head tail => exact .par head.binderSafe tail.binderSafe
end

mutual
  theorem NameImage.runtimeSupported {depth : Nat} {source : Pattern}
      {name : CostName LiteralAuthority} (image : NameImage depth source name) :
      name.RuntimeSupported := by
    cases image with
    | bvar bound => trivial
    | baseZeroQuote => trivial
    | quote code => exact code.runtimeSupported

  /-- Every signature of an image is a positive product of authorities. -/
  theorem CodeImage.runtimeSupported {depth : Nat} {source : Pattern}
      {term : CostTerm LiteralAuthority} (image : CodeImage depth source term) :
      term.RuntimeSupported := by
    cases image with
    | zero => trivial
    | drop name => exact name.runtimeSupported
    | signed signature accepted process => exact ⟨process.runtimeSupported, signature.positive⟩
    | collection codes => exact codes.runtimeSupported

  theorem ProcImage.runtimeSupported {depth : Nat} {source : Pattern}
      {process : CostProc LiteralAuthority} (image : ProcImage depth source process) :
      process.RuntimeSupported := by
    cases image with
    | zero => trivial
    | send name code => exact ⟨name.runtimeSupported, code.runtimeSupported⟩
    | recv name code => exact ⟨name.runtimeSupported, code.runtimeSupported⟩
    | pair left right => exact ⟨left.runtimeSupported, right.runtimeSupported⟩

  theorem CodeListImage.runtimeSupported {depth : Nat} {sources : List Pattern}
      {term : CostTerm LiteralAuthority} (image : CodeListImage depth sources term) :
      term.RuntimeSupported := by
    cases image with
    | nil => trivial
    | cons head tail => exact ⟨head.runtimeSupported, tail.runtimeSupported⟩
end

mutual
  theorem NameImage.erase_structural {depth : Nat} {source : Pattern}
      {name : CostName LiteralAuthority} (image : NameImage depth source name)
      (encoding : SignatureNameEncoding LiteralAuthority) :
      StructuralCongruence (name.erase encoding) (eraseGenerated source) := by
    cases image with
    | bvar => exact .refl _
    | baseZeroQuote => exact applyCongruence_of_forall₂ "NQuote" (.cons .par_empty .nil)
    | quote code =>
      exact applyCongruence_of_forall₂ "NQuote" (.cons (code.erase_structural encoding) .nil)

  /-- Erasing the cost apparatus from the image gives the erased generated syntax, up to the
  structural equations of rho. -/
  theorem CodeImage.erase_structural {depth : Nat} {source : Pattern}
      {term : CostTerm LiteralAuthority} (image : CodeImage depth source term)
      (encoding : SignatureNameEncoding LiteralAuthority) :
      StructuralCongruence (term.erase encoding) (eraseGenerated source) := by
    cases image with
    | zero => exact .par_empty
    | drop name =>
      exact applyCongruence_of_forall₂ "PDrop" (.cons (name.erase_structural encoding) .nil)
    | signed _ _ process => exact process.erase_structural encoding
    | collection codes => exact codes.erase_structural encoding

  theorem ProcImage.erase_structural {depth : Nat} {source : Pattern}
      {process : CostProc LiteralAuthority} (image : ProcImage depth source process)
      (encoding : SignatureNameEncoding LiteralAuthority) :
      StructuralCongruence (process.erase encoding) (eraseGenerated source) := by
    cases image with
    | zero => exact .par_empty
    | send name code =>
      exact applyCongruence_of_forall₂ "POutput"
        (.cons (name.erase_structural encoding) (.cons (code.erase_structural encoding) .nil))
    | recv name code =>
      exact applyCongruence_of_forall₂ "PInput"
        (.cons (name.erase_structural encoding)
          (.cons (.lambda_cong none _ _ (code.erase_structural encoding)) .nil))
    | pair left right =>
      exact collectionCongruence_of_forall₂ .hashBag none
        (.cons (left.erase_structural encoding) (.cons (right.erase_structural encoding) .nil))

  theorem CodeListImage.erase_structural {depth : Nat} {sources : List Pattern}
      {term : CostTerm LiteralAuthority} (image : CodeListImage depth sources term)
      (encoding : SignatureNameEncoding LiteralAuthority) :
      StructuralCongruence (term.erase encoding)
        (.collection .hashBag (eraseGeneratedList sources) none) := by
    cases image with
    | nil => exact .refl _
    | @cons depth source sources head tail headImage tailImage =>
      exact .trans _ _ _
        (collectionCongruence_of_forall₂ .hashBag none
          (.cons (headImage.erase_structural encoding) (.cons (tailImage.erase_structural encoding) .nil)))
        (.par_flatten [eraseGenerated source] (eraseGeneratedList sources))
end

theorem StackImage.runtimeSupported {source : Pattern} {stack : CostStack LiteralAuthority}
    (image : StackImage source stack) : stack.RuntimeSupported := by
  induction image with
  | empty => trivial
  | cons signature accepted rest ih => exact ⟨signature.positive, ih⟩

mutual
  /-- With a purse-free location, code and purses of a configuration image are separate. -/
  theorem ConfigImage.resourceSeparated {location : CostName LiteralAuthority} {source : Pattern}
      {term : CostTerm LiteralAuthority} (image : ConfigImage location source term)
      (locationFree : location.purseInventory = 0) : term.components.ResourceSeparated := by
    cases image with
    | zero => exact (CodeImage.zero (depth := 0)).purseFree.components_resourceSeparated
    | drop name => exact (CodeImage.drop name).purseFree.components_resourceSeparated
    | signed signature accepted process =>
      exact (CodeImage.signed signature accepted process).purseFree.components_resourceSeparated
    | contact code stack =>
      change CostConfig.ResourceSeparated (_ + (CostTerm.purse location _ ::ₘ 0))
      rw [CostConfig.resourceSeparated_add_iff, CostConfig.resourceSeparated_singleton_iff]
      exact ⟨code.resourceSeparated locationFree, locationFree⟩
    | collection codes => exact codes.resourceSeparated locationFree

  theorem ConfigListImage.resourceSeparated {location : CostName LiteralAuthority}
      {sources : List Pattern} {term : CostTerm LiteralAuthority}
      (image : ConfigListImage location sources term)
      (locationFree : location.purseInventory = 0) : term.components.ResourceSeparated := by
    cases image with
    | nil => simp [CostTerm.components, CostConfig.ResourceSeparated]
    | cons head tail =>
      change CostConfig.ResourceSeparated (_ + _)
      exact (CostConfig.resourceSeparated_add_iff _ _).mpr
        ⟨head.resourceSeparated locationFree, tail.resourceSeparated locationFree⟩
end

mutual
  theorem ConfigImage.binderSafe {location : CostName LiteralAuthority} {source : Pattern}
      {term : CostTerm LiteralAuthority} (image : ConfigImage location source term) :
      term.BinderSafeAt 0 := by
    cases image with
    | zero => exact .nil
    | drop name => exact .drop name.binderSafe
    | signed signature accepted process => exact .signed process.binderSafe
    | contact code stack => exact .par code.binderSafe .purse
    | collection codes => exact codes.binderSafe

  theorem ConfigListImage.binderSafe {location : CostName LiteralAuthority}
      {sources : List Pattern} {term : CostTerm LiteralAuthority}
      (image : ConfigListImage location sources term) : term.BinderSafeAt 0 := by
    cases image with
    | nil => exact .nil
    | cons head tail => exact .par head.binderSafe tail.binderSafe
end

mutual
  theorem ConfigImage.runtimeSupported {location : CostName LiteralAuthority} {source : Pattern}
      {term : CostTerm LiteralAuthority} (image : ConfigImage location source term)
      (locationSupported : location.RuntimeSupported) : term.RuntimeSupported := by
    cases image with
    | zero => trivial
    | drop name => exact name.runtimeSupported
    | signed signature accepted process => exact ⟨process.runtimeSupported, signature.positive⟩
    | contact code stack =>
      exact ⟨code.runtimeSupported locationSupported, locationSupported, stack.runtimeSupported⟩
    | collection codes => exact codes.runtimeSupported locationSupported

  theorem ConfigListImage.runtimeSupported {location : CostName LiteralAuthority}
      {sources : List Pattern} {term : CostTerm LiteralAuthority}
      (image : ConfigListImage location sources term)
      (locationSupported : location.RuntimeSupported) : term.RuntimeSupported := by
    cases image with
    | nil => trivial
    | cons head tail =>
      exact ⟨head.runtimeSupported locationSupported, tail.runtimeSupported locationSupported⟩
end

mutual
  /-- Erasure reads a contact as a parallel composition and a funding as nothing. -/
  theorem ConfigImage.erase_structural {location : CostName LiteralAuthority} {source : Pattern}
      {term : CostTerm LiteralAuthority} (image : ConfigImage location source term)
      (encoding : SignatureNameEncoding LiteralAuthority) :
      StructuralCongruence (term.erase encoding) (eraseGenerated source) := by
    cases image with
    | zero => exact .par_empty
    | drop name => exact (CodeImage.drop name).erase_structural encoding
    | signed signature accepted process =>
      exact (CodeImage.signed signature accepted process).erase_structural encoding
    | contact code stack =>
      exact collectionCongruence_of_forall₂ .hashBag none
        (.cons (code.erase_structural encoding) (.cons (.refl _) .nil))
    | collection codes => exact codes.erase_structural encoding

  theorem ConfigListImage.erase_structural {location : CostName LiteralAuthority}
      {sources : List Pattern} {term : CostTerm LiteralAuthority}
      (image : ConfigListImage location sources term)
      (encoding : SignatureNameEncoding LiteralAuthority) :
      StructuralCongruence (term.erase encoding)
        (.collection .hashBag (eraseGeneratedList sources) none) := by
    cases image with
    | nil => exact .refl _
    | @cons source sources head tail headImage tailImage =>
      exact .trans _ _ _
        (collectionCongruence_of_forall₂ .hashBag none
          (.cons (headImage.erase_structural encoding) (.cons (tailImage.erase_structural encoding) .nil)))
        (.par_flatten [eraseGenerated source] (eraseGeneratedList sources))
end

/-! ## The readout -/

mutual
  /-- Read a generated name. `fuel` bounds the depth of the syntax that is read. -/
  def readName : (fuel depth : Nat) → Pattern → Option (CostName LiteralAuthority)
    | 0, _, _ => none
    | _ + 1, depth, .bvar index => if index < depth then some (.bvar index) else none
    | _ + 1, _, .apply "$cost:base-constructor:NQuote" [.apply "$cost:base-constructor:PZero" []] =>
        some (.quote .nil)
    | fuel + 1, _, .apply "$cost:wrapped-constructor:NQuote" [source] =>
        (readCode fuel 0 source).map CostName.quote
    | _ + 1, _, _ => none

  /-- Read generated code. A funding is not code. -/
  def readCode : (fuel depth : Nat) → Pattern → Option (CostTerm LiteralAuthority)
    | 0, _, _ => none
    | _ + 1, _, .apply "$cost:wrapped-constructor:PZero" [] => some .nil
    | fuel + 1, depth, .apply "$cost:wrapped-constructor:PDrop" [source] =>
        (readName fuel depth source).map CostTerm.drop
    | fuel + 1, depth, .apply "$cost:apparatus-constructor:signed" [source, authority] => do
        let signature ← (signature? authority).map Subtype.val
        let process ← readProc fuel depth source
        some (CostTerm.signed process signature)
    | fuel + 1, depth, .collection .hashBag sources none => readCodeList fuel depth sources
    | _ + 1, _, _ => none

  /-- Read a process under a signature. -/
  def readProc : (fuel depth : Nat) → Pattern → Option (CostProc LiteralAuthority)
    | 0, _, _ => none
    | _ + 1, _, .apply "$cost:base-constructor:PZero" [] => some .nil
    | fuel + 1, depth, .apply "$cost:base-constructor:POutput" [channel, payload] => do
        let location ← readName fuel depth channel
        let sent ← readCode fuel depth payload
        some (CostProc.send location sent)
    | fuel + 1, depth,
        .apply "$cost:base-constructor:PInput" [channel, .lambda none body] => do
        let location ← readName fuel depth channel
        let continuation ← readCode fuel (depth + 1) body
        some (CostProc.recv location continuation)
    | fuel + 1, depth, .collection .hashBag [left, right] none => do
        let first ← readProc fuel depth left
        let second ← readProc fuel depth right
        some (CostProc.par first second)
    | _ + 1, _, _ => none

  /-- Read a bag of generated code as a parallel composition. -/
  def readCodeList : (fuel depth : Nat) → List Pattern → Option (CostTerm LiteralAuthority)
    | 0, _, _ => none
    | _ + 1, _, [] => some .nil
    | fuel + 1, depth, source :: sources => do
        let head ← readCode fuel depth source
        let tail ← readCodeList fuel depth sources
        some (CostTerm.par head tail)
end

/-- Read a generated token stack. -/
def readStack : (fuel : Nat) → Pattern → Option (CostStack LiteralAuthority)
  | 0, _ => none
  | _ + 1, .apply "$cost:apparatus-constructor:token-stack-empty" [] => some .empty
  | fuel + 1, .apply "$cost:apparatus-constructor:token-stack-cons" [head, tail] => do
      let signature ← (signature? head).map Subtype.val
      let stack ← readStack fuel tail
      some (CostStack.cons signature stack)
  | _ + 1, _ => none

mutual
  /-- Read a generated configuration, placing every purse at `location`. -/
  def readConfig (location : CostName LiteralAuthority) :
      (fuel : Nat) → Pattern → Option (CostTerm LiteralAuthority)
    | 0, _ => none
    | fuel + 1, .apply "$cost:apparatus-constructor:contact"
        [left, .apply "$cost:apparatus-constructor:funding" [stackSource]] => do
        let code ← readConfig location fuel left
        let stack ← readStack fuel stackSource
        some (locatedContact location code stack)
    | fuel + 1, .collection .hashBag sources none => readConfigList location fuel sources
    | fuel + 1, source => readCode fuel 0 source

  def readConfigList (location : CostName LiteralAuthority) :
      (fuel : Nat) → List Pattern → Option (CostTerm LiteralAuthority)
    | 0, _ => none
    | _ + 1, [] => some .nil
    | fuel + 1, source :: sources => do
        let head ← readConfig location fuel source
        let tail ← readConfigList location fuel sources
        some (CostTerm.par head tail)
end

/-! ## Success of the readout is the image -/

private theorem read_image :
    (∀ fuel depth source name, readName fuel depth source = some name →
      NameImage depth source name) ∧
    (∀ fuel depth source term, readCode fuel depth source = some term →
      CodeImage depth source term) ∧
    (∀ fuel depth sources term, readCodeList fuel depth sources = some term →
      CodeListImage depth sources term) ∧
    (∀ fuel depth source process, readProc fuel depth source = some process →
      ProcImage depth source process) := by
  apply readName.mutual_induct
    (motive_1 := fun fuel depth source => ∀ name, readName fuel depth source = some name →
      NameImage depth source name)
    (motive_2 := fun fuel depth source => ∀ term, readCode fuel depth source = some term →
      CodeImage depth source term)
    (motive_3 := fun fuel depth sources => ∀ term, readCodeList fuel depth sources = some term →
      CodeListImage depth sources term)
    (motive_4 := fun fuel depth source => ∀ process, readProc fuel depth source = some process →
      ProcImage depth source process)
  · intro source depth name parsed
    simp [readName] at parsed
  · intro fuel depth index bound name parsed
    simp only [readName, if_pos bound, Option.some.injEq] at parsed
    subst name
    exact .bvar bound
  · intro fuel depth index bound name parsed
    simp [readName, bound] at parsed
  · intro fuel depth name parsed
    simp only [readName, Option.some.injEq] at parsed
    subst name
    exact .baseZeroQuote
  · intro fuel depth source childIH name parsed
    cases childParsed : readCode fuel 0 source with
    | none => simp [readName, childParsed] at parsed
    | some child =>
      simp only [readName, childParsed, Option.map_some, Option.some.injEq] at parsed
      subst name
      exact .quote (childIH child childParsed)
  · intro source fuel depth notBvar notBase notWrapped name parsed
    simp_all [readName]
  · intro source depth term parsed
    simp [readCode] at parsed
  · intro fuel depth term parsed
    simp only [readCode, Option.some.injEq] at parsed
    subst term
    exact .zero
  · intro fuel depth source childIH term parsed
    cases childParsed : readName fuel depth source with
    | none => simp [readCode, childParsed] at parsed
    | some child =>
      simp only [readCode, childParsed, Option.map_some, Option.some.injEq] at parsed
      subst term
      exact .drop (childIH child childParsed)
  · intro fuel depth core authority childIH term parsed
    cases signatureParsed : signature? authority with
    | none => simp [readCode, signatureParsed] at parsed
    | some signature =>
      cases childParsed : readProc fuel depth core with
      | none => simp [readCode, signatureParsed, childParsed] at parsed
      | some child =>
        simp [readCode, signatureParsed, childParsed] at parsed
        subst term
        exact .signed signature signatureParsed (childIH child childParsed)
  · intro fuel depth sources childIH term parsed
    exact .collection (childIH term parsed)
  · intro source fuel depth notZero notDrop notSigned notCollection term parsed
    simp_all [readCode]
  · intro source depth process parsed
    simp [readProc] at parsed
  · intro fuel depth process parsed
    simp only [readProc, Option.some.injEq] at parsed
    subst process
    exact .zero
  · intro fuel depth channel payload channelIH childIH process parsed
    cases channelParsed : readName fuel depth channel with
    | none => simp [readProc, channelParsed] at parsed
    | some name =>
      cases childParsed : readCode fuel depth payload with
      | none => simp [readProc, channelParsed, childParsed] at parsed
      | some child =>
        simp [readProc, channelParsed, childParsed] at parsed
        subst process
        exact .send (channelIH name channelParsed) (childIH child childParsed)
  · intro fuel depth channel body channelIH childIH process parsed
    cases channelParsed : readName fuel depth channel with
    | none => simp [readProc, channelParsed] at parsed
    | some name =>
      cases childParsed : readCode fuel (depth + 1) body with
      | none => simp [readProc, channelParsed, childParsed] at parsed
      | some child =>
        simp [readProc, channelParsed, childParsed] at parsed
        subst process
        exact .recv (channelIH name channelParsed) (childIH child childParsed)
  · intro fuel depth left right leftIH rightIH process parsed
    cases leftParsed : readProc fuel depth left with
    | none => simp [readProc, leftParsed] at parsed
    | some first =>
      cases rightParsed : readProc fuel depth right with
      | none => simp [readProc, leftParsed, rightParsed] at parsed
      | some second =>
        simp [readProc, leftParsed, rightParsed] at parsed
        subst process
        exact .pair (leftIH first leftParsed) (rightIH second rightParsed)
  · intro source fuel depth notZero notSend notRecv notPair process parsed
    simp_all [readProc]
  · intro sources depth term parsed
    simp [readCodeList] at parsed
  · intro depth fuel term parsed
    simp only [readCodeList, Option.some.injEq] at parsed
    subst term
    exact .nil
  · intro fuel depth source sources headIH tailIH term parsed
    cases headParsed : readCode fuel depth source with
    | none => simp [readCodeList, headParsed] at parsed
    | some head =>
      cases tailParsed : readCodeList fuel depth sources with
      | none => simp [readCodeList, headParsed, tailParsed] at parsed
      | some tail =>
        simp [readCodeList, headParsed, tailParsed] at parsed
        subst term
        exact .cons (headIH head headParsed) (tailIH tail tailParsed)

/-- A name the readout returns is the image of the syntax it read. -/
theorem readName_image {fuel depth : Nat} {source : Pattern} {name : CostName LiteralAuthority}
    (parsed : readName fuel depth source = some name) : NameImage depth source name :=
  read_image.1 fuel depth source name parsed

/-- A term the readout returns is the image of the code it read. -/
theorem readCode_image {fuel depth : Nat} {source : Pattern} {term : CostTerm LiteralAuthority}
    (parsed : readCode fuel depth source = some term) : CodeImage depth source term :=
  read_image.2.1 fuel depth source term parsed

theorem readCodeList_image {fuel depth : Nat} {sources : List Pattern}
    {term : CostTerm LiteralAuthority}
    (parsed : readCodeList fuel depth sources = some term) : CodeListImage depth sources term :=
  read_image.2.2.1 fuel depth sources term parsed

theorem readProc_image {fuel depth : Nat} {source : Pattern} {process : CostProc LiteralAuthority}
    (parsed : readProc fuel depth source = some process) : ProcImage depth source process :=
  read_image.2.2.2 fuel depth source process parsed

theorem readStack_image {fuel : Nat} {source : Pattern} {stack : CostStack LiteralAuthority}
    (parsed : readStack fuel source = some stack) : StackImage source stack := by
  induction fuel, source using readStack.induct generalizing stack with
  | case1 source => simp [readStack] at parsed
  | case2 fuel =>
    simp only [readStack, Option.some.injEq] at parsed
    subst stack
    exact .empty
  | case3 fuel head tail ih =>
    cases signatureParsed : signature? head with
    | none => simp [readStack, signatureParsed] at parsed
    | some signature =>
      cases tailParsed : readStack fuel tail with
      | none => simp [readStack, signatureParsed, tailParsed] at parsed
      | some rest =>
        simp [readStack, signatureParsed, tailParsed] at parsed
        subst stack
        exact .cons signature signatureParsed (ih tailParsed)
  | case4 fuel source notEmpty notCons => simp_all [readStack]

private theorem read_config_image (location : CostName LiteralAuthority) :
    (∀ fuel source term, readConfig location fuel source = some term →
      ConfigImage location source term) ∧
    (∀ fuel sources term, readConfigList location fuel sources = some term →
      ConfigListImage location sources term) := by
  apply readConfig.mutual_induct
    (motive_1 := fun fuel source => ∀ term, readConfig location fuel source = some term →
      ConfigImage location source term)
    (motive_2 := fun fuel sources => ∀ term, readConfigList location fuel sources = some term →
      ConfigListImage location sources term)
  · intro source term parsed
    simp [readConfig] at parsed
  · intro fuel left stackSource leftIH term parsed
    cases leftParsed : readConfig location fuel left with
    | none => simp [readConfig, leftParsed] at parsed
    | some code =>
      cases stackParsed : readStack fuel stackSource with
      | none => simp [readConfig, leftParsed, stackParsed] at parsed
      | some stack =>
        simp [readConfig, leftParsed, stackParsed] at parsed
        subst term
        exact .contact (leftIH code leftParsed) (readStack_image stackParsed)
  · intro fuel sources listIH term parsed
    exact .collection (listIH term parsed)
  · intro fuel source notContact notCollection term parsed
    rw [readConfig.eq_4 location source fuel notContact notCollection] at parsed
    exact (readCode_image parsed).toConfigImage location
  · intro sources term parsed
    simp [readConfigList] at parsed
  · intro fuel term parsed
    simp only [readConfigList, Option.some.injEq] at parsed
    subst term
    exact .nil
  · intro fuel source sources headIH tailIH term parsed
    cases headParsed : readConfig location fuel source with
    | none => simp [readConfigList, headParsed] at parsed
    | some head =>
      cases tailParsed : readConfigList location fuel sources with
      | none => simp [readConfigList, headParsed, tailParsed] at parsed
      | some tail =>
        simp [readConfigList, headParsed, tailParsed] at parsed
        subst term
        exact .cons (headIH head headParsed) (tailIH tail tailParsed)

/-- A configuration the readout returns is the image of the syntax it read. -/
theorem readConfig_image {location : CostName LiteralAuthority} {fuel : Nat} {source : Pattern}
    {term : CostTerm LiteralAuthority}
    (parsed : readConfig location fuel source = some term) : ConfigImage location source term :=
  (read_config_image location).1 fuel source term parsed

theorem readConfigList_image {location : CostName LiteralAuthority} {fuel : Nat}
    {sources : List Pattern} {term : CostTerm LiteralAuthority}
    (parsed : readConfigList location fuel sources = some term) :
    ConfigListImage location sources term :=
  (read_config_image location).2 fuel sources term parsed

mutual
  theorem NameImage.read_eventually {depth : Nat} {source : Pattern}
      {name : CostName LiteralAuthority} (image : NameImage depth source name) :
      ∃ bound, ∀ fuel, bound ≤ fuel → readName fuel depth source = some name := by
    cases image with
    | bvar inScope =>
      refine ⟨1, ?_⟩
      intro fuel enough
      cases fuel with
      | zero => omega
      | succ fuel => exact if_pos inScope
    | baseZeroQuote =>
      refine ⟨1, ?_⟩
      intro fuel enough
      cases fuel with
      | zero => omega
      | succ fuel => rfl
    | quote code =>
      obtain ⟨bound, readback⟩ := code.read_eventually
      refine ⟨bound + 1, ?_⟩
      intro fuel enough
      cases fuel with
      | zero => omega
      | succ fuel =>
        change (readCode fuel 0 _).map CostName.quote = _
        rw [readback fuel (by omega)]
        rfl

  /-- With enough fuel the readout returns the image. -/
  theorem CodeImage.read_eventually {depth : Nat} {source : Pattern}
      {term : CostTerm LiteralAuthority} (image : CodeImage depth source term) :
      ∃ bound, ∀ fuel, bound ≤ fuel → readCode fuel depth source = some term := by
    cases image with
    | zero =>
      refine ⟨1, ?_⟩
      intro fuel enough
      cases fuel with
      | zero => omega
      | succ fuel => rfl
    | drop name =>
      obtain ⟨bound, readback⟩ := name.read_eventually
      refine ⟨bound + 1, ?_⟩
      intro fuel enough
      cases fuel with
      | zero => omega
      | succ fuel =>
        change (readName fuel depth _).map CostTerm.drop = _
        rw [readback fuel (by omega)]
        rfl
    | signed signature accepted process =>
      obtain ⟨bound, readback⟩ := process.read_eventually
      refine ⟨bound + 1, ?_⟩
      intro fuel enough
      cases fuel with
      | zero => omega
      | succ fuel =>
        change ((signature? _).map Subtype.val).bind
          (fun signature => (readProc fuel depth _).bind
            (fun process => some (CostTerm.signed process signature))) = _
        rw [accepted, readback fuel (by omega)]
        rfl
    | collection codes =>
      obtain ⟨bound, readback⟩ := codes.read_eventually
      refine ⟨bound + 1, ?_⟩
      intro fuel enough
      cases fuel with
      | zero => omega
      | succ fuel => exact readback fuel (by omega)

  theorem ProcImage.read_eventually {depth : Nat} {source : Pattern}
      {process : CostProc LiteralAuthority} (image : ProcImage depth source process) :
      ∃ bound, ∀ fuel, bound ≤ fuel → readProc fuel depth source = some process := by
    cases image with
    | zero =>
      refine ⟨1, ?_⟩
      intro fuel enough
      cases fuel with
      | zero => omega
      | succ fuel => rfl
    | send name code =>
      obtain ⟨nameBound, nameReadback⟩ := name.read_eventually
      obtain ⟨codeBound, codeReadback⟩ := code.read_eventually
      refine ⟨max nameBound codeBound + 1, ?_⟩
      intro fuel enough
      cases fuel with
      | zero => omega
      | succ fuel =>
        change (readName fuel depth _).bind (fun location => (readCode fuel depth _).bind
          (fun sent => some (CostProc.send location sent))) = _
        rw [nameReadback fuel (by omega), codeReadback fuel (by omega)]
        rfl
    | recv name code =>
      obtain ⟨nameBound, nameReadback⟩ := name.read_eventually
      obtain ⟨codeBound, codeReadback⟩ := code.read_eventually
      refine ⟨max nameBound codeBound + 1, ?_⟩
      intro fuel enough
      cases fuel with
      | zero => omega
      | succ fuel =>
        change (readName fuel depth _).bind (fun location => (readCode fuel (depth + 1) _).bind
          (fun continuation => some (CostProc.recv location continuation))) = _
        rw [nameReadback fuel (by omega), codeReadback fuel (by omega)]
        rfl
    | pair left right =>
      obtain ⟨leftBound, leftReadback⟩ := left.read_eventually
      obtain ⟨rightBound, rightReadback⟩ := right.read_eventually
      refine ⟨max leftBound rightBound + 1, ?_⟩
      intro fuel enough
      cases fuel with
      | zero => omega
      | succ fuel =>
        change (readProc fuel depth _).bind (fun first => (readProc fuel depth _).bind
          (fun second => some (CostProc.par first second))) = _
        rw [leftReadback fuel (by omega), rightReadback fuel (by omega)]
        rfl

  theorem CodeListImage.read_eventually {depth : Nat} {sources : List Pattern}
      {term : CostTerm LiteralAuthority} (image : CodeListImage depth sources term) :
      ∃ bound, ∀ fuel, bound ≤ fuel → readCodeList fuel depth sources = some term := by
    cases image with
    | nil =>
      refine ⟨1, ?_⟩
      intro fuel enough
      cases fuel with
      | zero => omega
      | succ fuel => rfl
    | cons head tail =>
      obtain ⟨headBound, headReadback⟩ := head.read_eventually
      obtain ⟨tailBound, tailReadback⟩ := tail.read_eventually
      refine ⟨max headBound tailBound + 1, ?_⟩
      intro fuel enough
      cases fuel with
      | zero => omega
      | succ fuel =>
        change (readCode fuel depth _).bind (fun head => (readCodeList fuel depth _).bind
          (fun tail => some (CostTerm.par head tail))) = _
        rw [headReadback fuel (by omega), tailReadback fuel (by omega)]
        rfl
end

theorem StackImage.read_eventually {source : Pattern} {stack : CostStack LiteralAuthority}
    (image : StackImage source stack) :
    ∃ bound, ∀ fuel, bound ≤ fuel → readStack fuel source = some stack := by
  induction image with
  | empty =>
    refine ⟨1, ?_⟩
    intro fuel enough
    cases fuel with
    | zero => omega
    | succ fuel => rfl
  | cons signature accepted rest ih =>
    obtain ⟨bound, readback⟩ := ih
    refine ⟨bound + 1, ?_⟩
    intro fuel enough
    cases fuel with
    | zero => omega
    | succ fuel =>
      change ((signature? _).map Subtype.val).bind
        (fun signature => (readStack fuel _).bind
          (fun stack => some (CostStack.cons signature stack))) = _
      rw [accepted, readback fuel (by omega)]
      rfl

mutual
  theorem ConfigImage.read_eventually {location : CostName LiteralAuthority}
      {source : Pattern} {term : CostTerm LiteralAuthority}
      (image : ConfigImage location source term) :
      ∃ bound, ∀ fuel, bound ≤ fuel → readConfig location fuel source = some term := by
    cases image with
    | zero =>
      refine ⟨2, ?_⟩
      intro fuel enough
      cases fuel with
      | zero => omega
      | succ fuel =>
        cases fuel with
        | zero => omega
        | succ fuel => rfl
    | drop name =>
      obtain ⟨bound, readback⟩ := (CodeImage.drop name).read_eventually
      refine ⟨bound + 1, ?_⟩
      intro fuel enough
      cases fuel with
      | zero => omega
      | succ fuel => exact readback fuel (by omega)
    | signed signature accepted process =>
      obtain ⟨bound, readback⟩ := (CodeImage.signed signature accepted process).read_eventually
      refine ⟨bound + 1, ?_⟩
      intro fuel enough
      cases fuel with
      | zero => omega
      | succ fuel => exact readback fuel (by omega)
    | contact left stack =>
      obtain ⟨leftBound, leftReadback⟩ := left.read_eventually
      obtain ⟨stackBound, stackReadback⟩ := stack.read_eventually
      refine ⟨max leftBound stackBound + 1, ?_⟩
      intro fuel enough
      cases fuel with
      | zero => omega
      | succ fuel =>
        change (readConfig location fuel _).bind (fun code => (readStack fuel _).bind
          (fun stack => some (locatedContact location code stack))) = _
        rw [leftReadback fuel (by omega), stackReadback fuel (by omega)]
        rfl
    | collection codes =>
      obtain ⟨bound, readback⟩ := codes.read_eventually
      refine ⟨bound + 1, ?_⟩
      intro fuel enough
      cases fuel with
      | zero => omega
      | succ fuel => exact readback fuel (by omega)

  theorem ConfigListImage.read_eventually {location : CostName LiteralAuthority}
      {sources : List Pattern} {term : CostTerm LiteralAuthority}
      (image : ConfigListImage location sources term) :
      ∃ bound, ∀ fuel, bound ≤ fuel → readConfigList location fuel sources = some term := by
    cases image with
    | nil =>
      refine ⟨1, ?_⟩
      intro fuel enough
      cases fuel with
      | zero => omega
      | succ fuel => rfl
    | cons head tail =>
      obtain ⟨headBound, headReadback⟩ := head.read_eventually
      obtain ⟨tailBound, tailReadback⟩ := tail.read_eventually
      refine ⟨max headBound tailBound + 1, ?_⟩
      intro fuel enough
      cases fuel with
      | zero => omega
      | succ fuel =>
        change (readConfig location fuel _).bind (fun head => (readConfigList location fuel _).bind
          (fun tail => some (CostTerm.par head tail))) = _
        rw [headReadback fuel (by omega), tailReadback fuel (by omega)]
        rfl
end

/-! ## The readout with its guarantees attached -/

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

abbrev DecodedStack (_source : Pattern) :=
  {stack : CostStack LiteralAuthority // stack.RuntimeSupported}

abbrev DecodedConfig (source : Pattern) :=
  {term : CostTerm LiteralAuthority // term.components.ResourceSeparated ∧
    term.BinderSafeAt 0 ∧ term.RuntimeSupported ∧
    ∀ encoding, StructuralCongruence (term.erase encoding) (eraseGenerated source)}

/-- Attaching a property that holds of every result does not change the result. -/
private theorem pmap_val {Value : Type} {holds : Value → Prop} (result : Option Value)
    (always : ∀ value, result = some value → holds value) :
    (result.pmap (fun value proof => (⟨value, proof⟩ : {value // holds value})) always).map
      Subtype.val = result := by
  cases result <;> rfl

def name? (fuel depth : Nat) (source : Pattern) : Option (DecodedName depth source) :=
  (readName fuel depth source).pmap (fun name guarantees => ⟨name, guarantees⟩)
    (fun _ parsed => ⟨(readName_image parsed).purseInventory_zero, (readName_image parsed).binderSafe,
      (readName_image parsed).runtimeSupported, (readName_image parsed).erase_structural⟩)

def code? (fuel depth : Nat) (source : Pattern) : Option (DecodedCode depth source) :=
  (readCode fuel depth source).pmap (fun term guarantees => ⟨term, guarantees⟩)
    (fun _ parsed => ⟨(readCode_image parsed).purseFree, (readCode_image parsed).binderSafe,
      (readCode_image parsed).runtimeSupported, (readCode_image parsed).erase_structural⟩)

def proc? (fuel depth : Nat) (source : Pattern) : Option (DecodedProc depth source) :=
  (readProc fuel depth source).pmap (fun process guarantees => ⟨process, guarantees⟩)
    (fun _ parsed => ⟨(readProc_image parsed).purseInventory_zero, (readProc_image parsed).binderSafe,
      (readProc_image parsed).runtimeSupported, (readProc_image parsed).erase_structural⟩)

def codeList? (fuel depth : Nat) (sources : List Pattern) :
    Option (DecodedCode depth (.collection .hashBag sources none)) :=
  (readCodeList fuel depth sources).pmap (fun term guarantees => ⟨term, guarantees⟩)
    (fun _ parsed => ⟨(readCodeList_image parsed).purseFree, (readCodeList_image parsed).binderSafe,
      (readCodeList_image parsed).runtimeSupported,
      (CodeImage.collection (readCodeList_image parsed)).erase_structural⟩)

def stack? (fuel : Nat) (source : Pattern) : Option (DecodedStack source) :=
  (readStack fuel source).pmap (fun stack guarantees => ⟨stack, guarantees⟩)
    (fun _ parsed => (readStack_image parsed).runtimeSupported)

/-- Nested contacts remain transparent parallel contexts. The location is where every purse of
the configuration is placed; it must itself be purse-free and supported. -/
def config? (location : CostName LiteralAuthority) (locationFree : location.purseInventory = 0)
    (locationSupported : location.RuntimeSupported) (fuel : Nat) (source : Pattern) :
    Option (DecodedConfig source) :=
  (readConfig location fuel source).pmap (fun term guarantees => ⟨term, guarantees⟩)
    (fun _ parsed => ⟨(readConfig_image parsed).resourceSeparated locationFree,
      (readConfig_image parsed).binderSafe,
      (readConfig_image parsed).runtimeSupported locationSupported,
      (readConfig_image parsed).erase_structural⟩)

def configList? (location : CostName LiteralAuthority) (locationFree : location.purseInventory = 0)
    (locationSupported : location.RuntimeSupported) (fuel : Nat) (sources : List Pattern) :
    Option (DecodedConfig (.collection .hashBag sources none)) :=
  (readConfigList location fuel sources).pmap (fun term guarantees => ⟨term, guarantees⟩)
    (fun _ parsed => ⟨(readConfigList_image parsed).resourceSeparated locationFree,
      (readConfigList_image parsed).binderSafe,
      (readConfigList_image parsed).runtimeSupported locationSupported,
      (ConfigImage.collection (readConfigList_image parsed)).erase_structural⟩)

theorem name?_val (fuel depth : Nat) (source : Pattern) :
    (name? fuel depth source).map Subtype.val = readName fuel depth source := pmap_val _ _

theorem code?_val (fuel depth : Nat) (source : Pattern) :
    (code? fuel depth source).map Subtype.val = readCode fuel depth source := pmap_val _ _

theorem proc?_val (fuel depth : Nat) (source : Pattern) :
    (proc? fuel depth source).map Subtype.val = readProc fuel depth source := pmap_val _ _

theorem codeList?_val (fuel depth : Nat) (sources : List Pattern) :
    (codeList? fuel depth sources).map Subtype.val = readCodeList fuel depth sources := pmap_val _ _

theorem stack?_val (fuel : Nat) (source : Pattern) :
    (stack? fuel source).map Subtype.val = readStack fuel source := pmap_val _ _

theorem config?_val (location : CostName LiteralAuthority)
    (locationFree : location.purseInventory = 0) (locationSupported : location.RuntimeSupported)
    (fuel : Nat) (source : Pattern) :
    (config? location locationFree locationSupported fuel source).map Subtype.val =
      readConfig location fuel source := pmap_val _ _

theorem configList?_val (location : CostName LiteralAuthority)
    (locationFree : location.purseInventory = 0) (locationSupported : location.RuntimeSupported)
    (fuel : Nat) (sources : List Pattern) :
    (configList? location locationFree locationSupported fuel sources).map Subtype.val =
      readConfigList location fuel sources := pmap_val _ _

/-! ## Every image is well typed in the generated language -/

/-- The constructor declaration of the generated language with a given label. -/
private def declared (label : String) : Option (String × List TermParam) :=
  (rhoCIGSLT.costWholeLanguage.terms.find? fun rule => rule.label == label).map
    fun rule => (rule.category, rule.params)

private theorem apply_hasType {bound : List TypeExpr} {label category : String}
    {parameters : List TermParam} {arguments : List Pattern}
    (row : declared label = some (category, parameters))
    (applied : ∀ name kind element, parameters ≠ [.simple name (.collection kind element)])
    (typed : ArgumentsHaveTypes rhoCIGSLT.costWholeLanguage FreeTypeContext.empty bound
      arguments parameters) :
    HasType rhoCIGSLT.costWholeLanguage FreeTypeContext.empty bound (.apply label arguments)
      (.base category) := by
  obtain ⟨rule, found, same⟩ := Option.map_eq_some_iff.mp row
  have labelled : rule.label = label := by simpa using List.find?_some found
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj same
  subst labelled
  refine .constructor (List.mem_of_find?_eq_some found) ?_ typed
  rintro ⟨name, kind, element, shape⟩
  exact applied name kind element shape

private theorem bag_hasType {bound : List TypeExpr} {label category name : String}
    {element : TypeExpr} {elements : List Pattern}
    (row : declared label = some (category, [.simple name (.collection .hashBag element)]))
    (typed : ElementsHaveType rhoCIGSLT.costWholeLanguage FreeTypeContext.empty bound
      elements element) :
    HasType rhoCIGSLT.costWholeLanguage FreeTypeContext.empty bound
      (.collection .hashBag elements none) (.base category) := by
  obtain ⟨rule, found, same⟩ := Option.map_eq_some_iff.mp row
  obtain ⟨rfl, parameters⟩ := Prod.mk.inj same
  exact .collectionConstructor (List.mem_of_find?_eq_some found) parameters typed

private abbrev nameSort : TypeExpr := .base (costBaseSortName "Name")
private abbrev procSort : TypeExpr := .base (costBaseSortName "Proc")
private abbrev wrappedSort : TypeExpr := .base costWrappedSortName

mutual
  theorem NameImage.hasType {depth : Nat} {source : Pattern} {name : CostName LiteralAuthority}
      (image : NameImage depth source name) :
      HasType rhoCIGSLT.costWholeLanguage FreeTypeContext.empty
        (List.replicate depth (.base (costBaseSortName "Name"))) source
        (.base (costBaseSortName "Name")) := by
    cases image with
    | bvar bound => exact .bvar (by simp [bound])
    | baseZeroQuote =>
      exact (checkHasType_sound (bound := []) (by decide +kernel)).weakenEmptyBound _
    | quote code =>
      exact apply_hasType (category := costBaseSortName "Name")
        (parameters := [.simple "p" wrappedSort]) (by decide +kernel) (by simp)
        (.cons trivial rfl (code.hasType.weakenEmptyBound _) .nil)

  /-- The image is of well typed syntax: generated code has the wrapped sort in a context of
  as many names as there are enclosing receivers. -/
  theorem CodeImage.hasType {depth : Nat} {source : Pattern} {term : CostTerm LiteralAuthority}
      (image : CodeImage depth source term) :
      HasType rhoCIGSLT.costWholeLanguage FreeTypeContext.empty
        (List.replicate depth (.base (costBaseSortName "Name"))) source
        (.base costWrappedSortName) := by
    cases image with
    | zero => exact (checkHasType_sound (bound := []) (by decide +kernel)).weakenEmptyBound _
    | drop name =>
      exact apply_hasType (parameters := [.simple "n" nameSort]) (by decide +kernel) (by simp)
        (.cons trivial rfl name.hasType .nil)
    | signed signature accepted process =>
      exact apply_hasType
        (parameters := [.simple "body" procSort, .simple "signature" (.base costSignatureSortName)])
        (by decide +kernel) (by simp)
        (.cons trivial rfl process.hasType
          (.cons trivial rfl (signature.property.2.weakenEmptyBound _) .nil))
    | collection codes =>
      exact bag_hasType (label := costWrappedConstructorName "PPar") (name := "ps")
        (by decide +kernel) codes.hasType

  theorem ProcImage.hasType {depth : Nat} {source : Pattern} {process : CostProc LiteralAuthority}
      (image : ProcImage depth source process) :
      HasType rhoCIGSLT.costWholeLanguage FreeTypeContext.empty
        (List.replicate depth (.base (costBaseSortName "Name"))) source
        (.base (costBaseSortName "Proc")) := by
    cases image with
    | zero => exact (checkHasType_sound (bound := []) (by decide +kernel)).weakenEmptyBound _
    | send name code =>
      exact apply_hasType (category := costBaseSortName "Proc")
        (parameters := [.simple "n" nameSort, .simple "q" wrappedSort]) (by decide +kernel) (by simp)
        (.cons trivial rfl name.hasType (.cons trivial rfl code.hasType .nil))
    | recv name code =>
      exact apply_hasType (category := costBaseSortName "Proc")
        (parameters := [.simple "n" nameSort,
          .abstractionNamed none "p" (.arrow nameSort wrappedSort)])
        (by decide +kernel) (by simp)
        (.cons trivial rfl name.hasType (.cons trivial rfl (.lambda code.hasType) .nil))
    | pair left right =>
      exact bag_hasType (label := costBaseConstructorName "PPar") (name := "ps")
        (category := costBaseSortName "Proc") (by decide +kernel)
        (.cons left.hasType (.cons right.hasType (.nil _ _)))

  theorem CodeListImage.hasType {depth : Nat} {sources : List Pattern}
      {term : CostTerm LiteralAuthority} (image : CodeListImage depth sources term) :
      ElementsHaveType rhoCIGSLT.costWholeLanguage FreeTypeContext.empty
        (List.replicate depth (.base (costBaseSortName "Name"))) sources
        (.base costWrappedSortName) := by
    cases image with
    | nil => exact .nil _ _
    | cons head tail => exact .cons head.hasType tail.hasType
end

theorem StackImage.hasType {source : Pattern} {stack : CostStack LiteralAuthority}
    (image : StackImage source stack) :
    HasType rhoCIGSLT.costWholeLanguage FreeTypeContext.empty [] source
      (.base costTokenStackSortName) := by
  induction image with
  | empty => exact checkHasType_sound (by decide +kernel)
  | cons signature accepted rest ih =>
    exact apply_hasType
      (parameters := [.simple "head" (.base costSignatureSortName),
        .simple "tail" (.base costTokenStackSortName)])
      (by decide +kernel) (by simp)
      (.cons trivial rfl signature.property.2 (.cons trivial rfl ih .nil))

mutual
  /-- A configuration image is of closed well typed syntax of the wrapped sort. -/
  theorem ConfigImage.hasType {location : CostName LiteralAuthority} {source : Pattern}
      {term : CostTerm LiteralAuthority} (image : ConfigImage location source term) :
      HasType rhoCIGSLT.costWholeLanguage FreeTypeContext.empty [] source
        (.base costWrappedSortName) := by
    cases image with
    | zero => exact (CodeImage.zero (depth := 0)).hasType
    | drop name => exact (CodeImage.drop name).hasType
    | signed signature accepted process => exact (CodeImage.signed signature accepted process).hasType
    | contact code stack =>
      exact apply_hasType
        (parameters := [.simple "left" wrappedSort, .simple "right" wrappedSort])
        (by decide +kernel) (by simp)
        (.cons trivial rfl code.hasType
          (.cons trivial rfl
            (apply_hasType (parameters := [.simple "stack" (.base costTokenStackSortName)])
              (by decide +kernel) (by simp) (.cons trivial rfl stack.hasType .nil)) .nil))
    | collection codes =>
      exact bag_hasType (label := costWrappedConstructorName "PPar") (name := "ps")
        (by decide +kernel) codes.hasType

  theorem ConfigListImage.hasType {location : CostName LiteralAuthority} {sources : List Pattern}
      {term : CostTerm LiteralAuthority} (image : ConfigListImage location sources term) :
      ElementsHaveType rhoCIGSLT.costWholeLanguage FreeTypeContext.empty [] sources
        (.base costWrappedSortName) := by
    cases image with
    | nil => exact .nil _ _
    | cons head tail => exact .cons head.hasType tail.hasType
end

/-! ## The earlier statement of the image: typing together with success of the readout

`GeneratedCodeImage` and `GeneratedConfigImage` ask for a typing derivation and for a fuel at which
the readout succeeds. Both are consequences of the image, so each is the image.
-/

/-- Typing in the generated language together with success of the readout. -/
def GeneratedCodeImage (depth : Nat) (source : Pattern) (term : CostTerm LiteralAuthority) : Prop :=
  HasType rhoCIGSLT.costWholeLanguage FreeTypeContext.empty
    (List.replicate depth (.base (costBaseSortName "Name"))) source (.base costWrappedSortName) ∧
  ∃ fuel, (code? fuel depth source).map Subtype.val = some term

/-- The earlier statement says exactly that `term` is the image of `source`. -/
theorem generatedCodeImage_iff_image {depth : Nat} {source : Pattern}
    {term : CostTerm LiteralAuthority} :
    GeneratedCodeImage depth source term ↔ CodeImage depth source term := by
  constructor
  · rintro ⟨_, fuel, parsed⟩
    exact readCode_image ((code?_val fuel depth source).symm.trans parsed)
  · intro image
    obtain ⟨bound, readback⟩ := image.read_eventually
    exact ⟨image.hasType, bound, (code?_val bound depth source).trans (readback bound (le_refl bound))⟩

theorem GeneratedCodeImage.purseFree {depth : Nat} {source : Pattern}
    {term : CostTerm LiteralAuthority} (image : GeneratedCodeImage depth source term) :
    term.PurseFree := (generatedCodeImage_iff_image.mp image).purseFree

theorem GeneratedCodeImage.binderSafe {depth : Nat} {source : Pattern}
    {term : CostTerm LiteralAuthority} (image : GeneratedCodeImage depth source term) :
    term.BinderSafeAt depth := (generatedCodeImage_iff_image.mp image).binderSafe

theorem GeneratedCodeImage.runtimeSupported {depth : Nat} {source : Pattern}
    {term : CostTerm LiteralAuthority} (image : GeneratedCodeImage depth source term) :
    term.RuntimeSupported := (generatedCodeImage_iff_image.mp image).runtimeSupported

theorem GeneratedCodeImage.erase_structural {depth : Nat} {source : Pattern}
    {term : CostTerm LiteralAuthority} (image : GeneratedCodeImage depth source term)
    (encoding : SignatureNameEncoding LiteralAuthority) :
    StructuralCongruence (term.erase encoding) (eraseGenerated source) :=
  (generatedCodeImage_iff_image.mp image).erase_structural encoding

/-- Typing together with success of the configuration readout at a purse-free, supported
location. -/
def GeneratedConfigImage (location : CostName LiteralAuthority) (source : Pattern)
    (term : CostTerm LiteralAuthority) : Prop :=
  HasType rhoCIGSLT.costWholeLanguage FreeTypeContext.empty [] source (.base costWrappedSortName) ∧
  ∃ locationFree locationSupported fuel,
    (config? location locationFree locationSupported fuel source).map Subtype.val = some term

/-- The earlier statement says exactly that `term` is the configuration image of `source` at a
purse-free, supported location. -/
theorem generatedConfigImage_iff_image {location : CostName LiteralAuthority} {source : Pattern}
    {term : CostTerm LiteralAuthority} :
    GeneratedConfigImage location source term ↔
      location.purseInventory = 0 ∧ location.RuntimeSupported ∧
        ConfigImage location source term := by
  constructor
  · rintro ⟨_, locationFree, locationSupported, fuel, parsed⟩
    exact ⟨locationFree, locationSupported, readConfig_image
      ((config?_val location locationFree locationSupported fuel source).symm.trans parsed)⟩
  · rintro ⟨locationFree, locationSupported, image⟩
    obtain ⟨bound, readback⟩ := image.read_eventually
    exact ⟨image.hasType, locationFree, locationSupported, bound,
      (config?_val location locationFree locationSupported bound source).trans
        (readback bound (le_refl bound))⟩

theorem GeneratedConfigImage.resourceSeparated {location : CostName LiteralAuthority}
    {source : Pattern} {term : CostTerm LiteralAuthority}
    (image : GeneratedConfigImage location source term) : term.components.ResourceSeparated :=
  (generatedConfigImage_iff_image.mp image).2.2.resourceSeparated
    (generatedConfigImage_iff_image.mp image).1

theorem GeneratedConfigImage.binderSafe {location : CostName LiteralAuthority}
    {source : Pattern} {term : CostTerm LiteralAuthority}
    (image : GeneratedConfigImage location source term) : term.BinderSafe :=
  (generatedConfigImage_iff_image.mp image).2.2.binderSafe

theorem GeneratedConfigImage.runtimeSupported {location : CostName LiteralAuthority}
    {source : Pattern} {term : CostTerm LiteralAuthority}
    (image : GeneratedConfigImage location source term) : term.RuntimeSupported :=
  (generatedConfigImage_iff_image.mp image).2.2.runtimeSupported
    (generatedConfigImage_iff_image.mp image).2.1

theorem GeneratedConfigImage.erase_structural {location : CostName LiteralAuthority}
    {source : Pattern} {term : CostTerm LiteralAuthority}
    (image : GeneratedConfigImage location source term) (encoding : SignatureNameEncoding LiteralAuthority) :
    StructuralCongruence (term.erase encoding) (eraseGenerated source) :=
  (generatedConfigImage_iff_image.mp image).2.2.erase_structural encoding

/-- Communication between images keeps the result supported, closed and purse-free: replacing a
bound name cannot introduce purse authority. -/
theorem CodeImage.commSubst_admission {bodySource payloadSource : Pattern}
    {body payload : CostTerm LiteralAuthority}
    (bodyImage : CodeImage 1 bodySource body) (payloadImage : CodeImage 0 payloadSource payload) :
    (body.commSubst payload).RuntimeSupported ∧ (body.commSubst payload).BinderSafe ∧
      (body.commSubst payload).PurseFree :=
  CostTerm.code_admission_commSubst bodyImage.runtimeSupported payloadImage.runtimeSupported
    bodyImage.binderSafe payloadImage.binderSafe bodyImage.purseFree payloadImage.purseFree

theorem GeneratedCodeImage.commSubst_admission {bodySource payloadSource : Pattern}
    {body payload : CostTerm LiteralAuthority}
    (bodyImage : GeneratedCodeImage 1 bodySource body)
    (payloadImage : GeneratedCodeImage 0 payloadSource payload) :
    (body.commSubst payload).RuntimeSupported ∧ (body.commSubst payload).BinderSafe ∧
      (body.commSubst payload).PurseFree :=
  (generatedCodeImage_iff_image.mp bodyImage).commSubst_admission
    (generatedCodeImage_iff_image.mp payloadImage)

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
