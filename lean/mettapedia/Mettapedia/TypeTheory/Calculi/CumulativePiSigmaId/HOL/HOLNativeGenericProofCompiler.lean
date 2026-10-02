import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.FormationSensitiveHOLGenericProofFamily
import Mettapedia.Logic.HOL.ProofSyntax

/-!
# Signature-generic recursive compilation of retained HOL proofs

The proof-tree traversal is independent of the List signature.  Its logical
cases use only the chosen `LogicalSignature`; equality and extensional cases
request operations from an explicit capability algebra.  A missing operation
rejects that proof node with `none`, so a source signature does not acquire
proof rules merely by using the compiler.

The full List algebra below reproduces the earlier recursive compiler.  The
empty algebra still compiles the actual call-guard refinement proof because
that proof uses only hypotheses, implication and universal quantification;
an equality proof is rejected by the same instance.
-/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

set_option autoImplicit false


namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOLNativeGenericProofCompiler

open Presentation Mettapedia.Logic
open FormationSensitiveHOLInterface

universe u v

variable {Base : Type u} {Const : HOL.Ty Base → Type v}

/-- The native representation of source equality at one represented HOL type.
This remains ordinary HOL equality: it is neither native identity nor kernel
conversion. -/
def rawEquality (signature : LogicalSignature Base Const) {n : Nat}
    (type : HOL.Ty Base) (left right : Tower.Tm n) : Tower.Tm n :=
  .app (.app (liftClosed (signature.equality type)) left) right

@[simp] theorem rawEquality_subst (signature : LogicalSignature Base Const)
    {n m : Nat} (sigma : Sub Tower.Head n m) (type : HOL.Ty Base)
    (left right : Tower.Tm n) :
    subst sigma (rawEquality signature type left right) =
      rawEquality signature type (subst sigma left) (subst sigma right) := by
  simp [rawEquality, Presentation.subst]

/-- The computational projection of a proof-operation algebra.  This record
is kept separate only so the law-bearing algebra below has an explicit erasure;
clients compile through that algebra rather than supplying unchecked terms. -/
structure RawOperations (Base : Type u) where
  reflexivity : {n : Nat} → Option (Tower.Tm n)
  symmetry : {n : Nat} → HOL.Ty Base → Tower.Tm n → Tower.Tm n →
    Option (Tower.Tm n)
  transitivity : {n : Nat} → HOL.Ty Base → Tower.Tm n → Tower.Tm n →
    Tower.Tm n → Option (Tower.Tm n)
  propositionExtensionality : {n : Nat} → Tower.Tm n → Tower.Tm n →
    Tower.Tm n → Tower.Tm n → Option (Tower.Tm n)
  propositionForward : {n : Nat} → Tower.Tm n → Option (Tower.Tm n)
  functionCongruence : {n : Nat} → HOL.Ty Base → Tower.Tm n → Tower.Tm n →
    Tower.Tm n → Option (Tower.Tm n)
  argumentCongruence : {n : Nat} → HOL.Ty Base → Tower.Tm n → Tower.Tm n →
    Tower.Tm n → Option (Tower.Tm n)
  functionExtensionality : {n : Nat} → Tower.Tm n → Tower.Tm n →
    Tower.Tm n → Tower.Tm n → Tower.Tm n → Option (Tower.Tm n)

/-- The computational projection with no equality-proof capabilities. -/
def RawOperations.logicalOnly : RawOperations Base where
  reflexivity := none
  symmetry := fun _ _ _ => none
  transitivity := fun _ _ _ _ => none
  propositionExtensionality := fun _ _ _ _ => none
  propositionForward := fun _ => none
  functionCongruence := fun _ _ _ _ => none
  argumentCongruence := fun _ _ _ _ => none
  functionExtensionality := fun _ _ _ _ _ => none

/-- A proof-operation algebra is not merely a table of terms.  It names the
presentation in which those terms run, proves that the generic proof-family
extension maps into that presentation, and certifies every optional operation
at the exact proof family it constructs.  Thus a successful public compilation
cannot outrun the typing and computation laws of its host theory. -/
structure Operations (signature : LogicalSignature Base Const)
    (proofName : DeclName) where
  fresh : signature.rules.constantType proofName = none
  target : Rules Tower.Head
  proofMorphism :
    (FormationSensitiveHOLGenericProofFamily.rules signature proofName).Morphism
      target (fun head => head)
  raw : RawOperations Base
  reflexivity_typed : ∀ {n : Nat} {context : Tower.Ctx n}
      {type : HOL.Ty Base} {left right out : Tower.Tm n},
    raw.reflexivity = some out →
    Presentation.FormationSensitive.Typing signature.rules context left
      (typeAt signature.types n type) →
    Presentation.FormationSensitive.Typing signature.rules context right
      (typeAt signature.types n type) →
    Presentation.Conv target.headEq left right
      target.computation →
    Presentation.FormationSensitive.Typing target context out
      (FormationSensitiveHOLGenericProofFamily.proof proofName
        (rawEquality signature type left right))
  symmetry_typed : ∀ {n : Nat} {context : Tower.Ctx n}
      {type : HOL.Ty Base} {left right comparison out : Tower.Tm n},
    raw.symmetry type left comparison = some out →
    Presentation.FormationSensitive.Typing signature.rules context left
      (typeAt signature.types n type) →
    Presentation.FormationSensitive.Typing signature.rules context right
      (typeAt signature.types n type) →
    Presentation.FormationSensitive.Typing target context comparison
      (FormationSensitiveHOLGenericProofFamily.proof proofName
        (rawEquality signature type left right)) →
    Presentation.FormationSensitive.Typing target context out
      (FormationSensitiveHOLGenericProofFamily.proof proofName
        (rawEquality signature type right left))
  transitivity_typed : ∀ {n : Nat} {context : Tower.Ctx n}
      {type : HOL.Ty Base} {left middle right first second out : Tower.Tm n},
    raw.transitivity type left first second = some out →
    Presentation.FormationSensitive.Typing signature.rules context left
      (typeAt signature.types n type) →
    Presentation.FormationSensitive.Typing signature.rules context middle
      (typeAt signature.types n type) →
    Presentation.FormationSensitive.Typing signature.rules context right
      (typeAt signature.types n type) →
    Presentation.FormationSensitive.Typing target context first
      (FormationSensitiveHOLGenericProofFamily.proof proofName
        (rawEquality signature type left middle)) →
    Presentation.FormationSensitive.Typing target context second
      (FormationSensitiveHOLGenericProofFamily.proof proofName
        (rawEquality signature type middle right)) →
    Presentation.FormationSensitive.Typing target context out
      (FormationSensitiveHOLGenericProofFamily.proof proofName
        (rawEquality signature type left right))
  propositionExtensionality_typed : ∀ {n : Nat} {context : Tower.Ctx n}
      {left right forward backward out : Tower.Tm n},
    raw.propositionExtensionality left right forward backward = some out →
    Presentation.FormationSensitive.Typing signature.rules context left
      (typeAt signature.types n .prop) →
    Presentation.FormationSensitive.Typing signature.rules context right
      (typeAt signature.types n .prop) →
    Presentation.FormationSensitive.Typing target context forward
      (FormationSensitiveHOLGenericProofFamily.proof proofName
        (FormationSensitiveHOLGenericProofFamily.rawImp signature left right)) →
    Presentation.FormationSensitive.Typing target context backward
      (FormationSensitiveHOLGenericProofFamily.proof proofName
        (FormationSensitiveHOLGenericProofFamily.rawImp signature right left)) →
    Presentation.FormationSensitive.Typing target context out
      (FormationSensitiveHOLGenericProofFamily.proof proofName
        (rawEquality signature .prop left right))
  propositionForward_typed : ∀ {n : Nat} {context : Tower.Ctx n}
      {left right comparison out : Tower.Tm n},
    raw.propositionForward comparison = some out →
    Presentation.FormationSensitive.Typing signature.rules context left
      (typeAt signature.types n .prop) →
    Presentation.FormationSensitive.Typing signature.rules context right
      (typeAt signature.types n .prop) →
    Presentation.FormationSensitive.Typing target context comparison
      (FormationSensitiveHOLGenericProofFamily.proof proofName
        (rawEquality signature .prop left right)) →
    Presentation.FormationSensitive.Typing target context out
      (FormationSensitiveHOLGenericProofFamily.proof proofName
        (FormationSensitiveHOLGenericProofFamily.rawImp signature left right))
  functionCongruence_typed : ∀ {n : Nat} {context : Tower.Ctx n}
      {domain result : HOL.Ty Base}
      {function other argument comparison out : Tower.Tm n},
    raw.functionCongruence result function argument comparison = some out →
    Presentation.FormationSensitive.Typing signature.rules context function
      (typeAt signature.types n (.arr domain result)) →
    Presentation.FormationSensitive.Typing signature.rules context other
      (typeAt signature.types n (.arr domain result)) →
    Presentation.FormationSensitive.Typing signature.rules context argument
      (typeAt signature.types n domain) →
    Presentation.FormationSensitive.Typing target context comparison
      (FormationSensitiveHOLGenericProofFamily.proof proofName
        (rawEquality signature (.arr domain result) function other)) →
    Presentation.FormationSensitive.Typing target context out
      (FormationSensitiveHOLGenericProofFamily.proof proofName
        (rawEquality signature result (.app function argument)
          (.app other argument)))
  argumentCongruence_typed : ∀ {n : Nat} {context : Tower.Ctx n}
      {domain result : HOL.Ty Base}
      {function left right comparison out : Tower.Tm n},
    raw.argumentCongruence result function left comparison = some out →
    Presentation.FormationSensitive.Typing signature.rules context function
      (typeAt signature.types n (.arr domain result)) →
    Presentation.FormationSensitive.Typing signature.rules context left
      (typeAt signature.types n domain) →
    Presentation.FormationSensitive.Typing signature.rules context right
      (typeAt signature.types n domain) →
    Presentation.FormationSensitive.Typing target context comparison
      (FormationSensitiveHOLGenericProofFamily.proof proofName
        (rawEquality signature domain left right)) →
    Presentation.FormationSensitive.Typing target context out
      (FormationSensitiveHOLGenericProofFamily.proof proofName
        (rawEquality signature result (.app function left)
          (.app function right)))
  functionExtensionality_typed : ∀ {n : Nat} {context : Tower.Ctx n}
      {domain codomain : HOL.Ty Base}
      {function other pointwise out : Tower.Tm n},
    raw.functionExtensionality
        (typeAt signature.types n domain) (typeAt signature.types n codomain)
        function other pointwise = some out →
    Presentation.FormationSensitive.Typing signature.rules context function
      (typeAt signature.types n (.arr domain codomain)) →
    Presentation.FormationSensitive.Typing signature.rules context other
      (typeAt signature.types n (.arr domain codomain)) →
    Presentation.FormationSensitive.Typing target context pointwise
      (FormationSensitiveHOLGenericProofFamily.proof proofName
        (FormationSensitiveHOLGenericProofFamily.universalProposition signature domain
          (.lam (rawEquality signature codomain
            (.app (Presentation.rename wk function) (.var 0))
            (.app (Presentation.rename wk other) (.var 0)))))) →
    Presentation.FormationSensitive.Typing target context out
      (FormationSensitiveHOLGenericProofFamily.proof proofName
        (rawEquality signature (.arr domain codomain) function other))

/-- The logical fragment is the initial lawful algebra: it targets the generic
proof-family presentation itself and rejects every equality operation. -/
def Operations.logicalOnly (signature : LogicalSignature Base Const)
    (proofName : DeclName)
    (fresh : signature.rules.constantType proofName = none) :
    Operations signature proofName where
  fresh := fresh
  target := FormationSensitiveHOLGenericProofFamily.rules signature proofName
  proofMorphism := Rules.Morphism.identity _
  raw := RawOperations.logicalOnly
  reflexivity_typed := by
    intro _ _ _ _ _ out success
    change none = some out at success
    contradiction
  symmetry_typed := by
    intro _ _ _ _ _ _ out success
    change none = some out at success
    contradiction
  transitivity_typed := by
    intro _ _ _ _ _ _ _ _ out success
    change none = some out at success
    contradiction
  propositionExtensionality_typed := by
    intro _ _ _ _ _ _ out success
    change none = some out at success
    contradiction
  propositionForward_typed := by
    intro _ _ _ _ _ out success
    change none = some out at success
    contradiction
  functionCongruence_typed := by
    intro _ _ _ _ _ _ _ _ out success
    change none = some out at success
    contradiction
  argumentCongruence_typed := by
    intro _ _ _ _ _ _ _ _ out success
    change none = some out at success
    contradiction
  functionExtensionality_typed := by
    intro _ _ _ _ _ _ _ out success
    change none = some out at success
    contradiction

@[simp] theorem Operations.logicalOnly_raw
    (signature : LogicalSignature Base Const) (proofName : DeclName)
    (fresh : signature.rules.constantType proofName = none) :
    (Operations.logicalOnly signature proofName fresh).raw =
      (RawOperations.logicalOnly : RawOperations Base) := rfl

/-- The logical fragment at any rules package receiving the proof family, such
as a program that adds assumed facts and further declarations.  Every equality
operation is rejected, so each law holds whatever the target. -/
def Operations.logicalOnlyAt (signature : LogicalSignature Base Const)
    (proofName : DeclName)
    (fresh : signature.rules.constantType proofName = none)
    (target : Rules Tower.Head)
    (proofMorphism :
      (FormationSensitiveHOLGenericProofFamily.rules signature proofName).Morphism
        target (fun head => head)) :
    Operations signature proofName where
  fresh := fresh
  target := target
  proofMorphism := proofMorphism
  raw := RawOperations.logicalOnly
  reflexivity_typed := by
    intro _ _ _ _ _ out success
    change none = some out at success
    contradiction
  symmetry_typed := by
    intro _ _ _ _ _ _ out success
    change none = some out at success
    contradiction
  transitivity_typed := by
    intro _ _ _ _ _ _ _ _ out success
    change none = some out at success
    contradiction
  propositionExtensionality_typed := by
    intro _ _ _ _ _ _ out success
    change none = some out at success
    contradiction
  propositionForward_typed := by
    intro _ _ _ _ _ out success
    change none = some out at success
    contradiction
  functionCongruence_typed := by
    intro _ _ _ _ _ _ _ _ out success
    change none = some out at success
    contradiction
  argumentCongruence_typed := by
    intro _ _ _ _ _ _ _ _ out success
    change none = some out at success
    contradiction
  functionExtensionality_typed := by
    intro _ _ _ _ _ _ _ out success
    change none = some out at success
    contradiction

/-- A lawful algebra receives the original HOL presentation by the composite
of the source inclusion and its proof-family morphism. -/
theorem Operations.sourceMorphism {signature : LogicalSignature Base Const}
    {proofName : DeclName} (operations : Operations signature proofName) :
    signature.rules.Morphism operations.target (fun head => head) := by
  have composed :=
    (FormationSensitiveHOLGenericProofFamily.sourceMorphism signature proofName).comp
      operations.proofMorphism
  exact {
    headTyping := composed.headTyping
    isUniverse := composed.isUniverse
    join := composed.join
    cumulative := composed.cumulative
    headEq := composed.headEq
    constantType := by
      intro name type known
      simpa only [Function.comp_apply, Function.comp_def, Tm.mapHead_id] using
        composed.constantType known
    computation := by
      intro n left right step
      simpa only [Function.comp_apply, Function.comp_def, Tm.mapHead_id] using
        composed.computation step
  }

theorem Operations.includeSourceTyping
    {signature : LogicalSignature Base Const} {proofName : DeclName}
    (operations : Operations signature proofName)
    {n : Nat} {context : Tower.Ctx n} {term type : Tower.Tm n}
    (typed : Presentation.FormationSensitive.Typing signature.rules context term type) :
    Presentation.FormationSensitive.Typing operations.target context term type := by
  simpa only [Ctx.mapHead_id, Tm.mapHead_id] using
    typed.mapHead operations.sourceMorphism

theorem Operations.includeProofTyping
    {signature : LogicalSignature Base Const} {proofName : DeclName}
    (operations : Operations signature proofName)
    {n : Nat} {context : Tower.Ctx n} {term type : Tower.Tm n}
    (typed : Presentation.FormationSensitive.Typing
      (FormationSensitiveHOLGenericProofFamily.rules signature proofName)
      context term type) :
    Presentation.FormationSensitive.Typing operations.target context term type := by
  simpa only [Ctx.mapHead_id, Tm.mapHead_id] using
    typed.mapHead operations.proofMorphism

theorem Operations.includeProofConversion
    {signature : LogicalSignature Base Const} {proofName : DeclName}
    (operations : Operations signature proofName)
    {n : Nat} {left right : Tower.Tm n}
    (conversion : Presentation.Conv
      (FormationSensitiveHOLGenericProofFamily.rules signature proofName).headEq
      left right
      (FormationSensitiveHOLGenericProofFamily.rules signature proofName).computation) :
    Presentation.Conv operations.target.headEq left right
      operations.target.computation := by
  have mapped := conversion.mapHead (fun head => head)
    operations.proofMorphism.headEq operations.proofMorphism.computation
  simpa only [Tm.mapHead_id] using mapped

/-- The lowest universe of the source remains a universe in every target of
the proof-family morphism.  Target logical constructors use this transported
witness rather than assuming a particular target presentation. -/
theorem Operations.zeroUniverse
    {signature : LogicalSignature Base Const} {proofName : DeclName}
    (operations : Operations signature proofName) :
    operations.target.isUniverse (.sort Tower.zero) := by
  simpa only using
    operations.proofMorphism.isUniverse (LevelTower.IsUniverse.sort Tower.zero)

theorem Operations.implicationIntro
    {signature : LogicalSignature Base Const} {proofName : DeclName}
    (operations : Operations signature proofName)
    {n : Nat} {context : Tower.Ctx n} {left right : Tower.Tm n}
    {body : Tower.Tm (n + 1)}
    (leftTyped : Presentation.FormationSensitive.Typing signature.rules context left
      (typeAt signature.types n .prop))
    (rightTyped : Presentation.FormationSensitive.Typing signature.rules context right
      (typeAt signature.types n .prop))
    (bodyTyped : Presentation.FormationSensitive.Typing operations.target
      (.snoc context (FormationSensitiveHOLGenericProofFamily.proof proofName left))
      body (Presentation.rename wk
        (FormationSensitiveHOLGenericProofFamily.proof proofName right))) :
    Presentation.FormationSensitive.Typing operations.target context (.lam body)
      (FormationSensitiveHOLGenericProofFamily.proof proofName
        (FormationSensitiveHOLGenericProofFamily.rawImp signature left right)) := by
  open FormationSensitiveHOLGenericProofFamily in
  exact .conv
    (.lamIntro
      (operations.includeProofTyping
        (implication_formed signature proofName operations.fresh
          (include_typed signature proofName leftTyped)
          (include_typed signature proofName rightTyped)))
      operations.zeroUniverse bodyTyped)
    (operations.includeProofTyping
      (proof_formed signature proofName operations.fresh
        (implication_proposition signature proofName
          (include_typed signature proofName leftTyped)
          (include_typed signature proofName rightTyped))))
    operations.zeroUniverse
    (.symm _ _ (operations.includeProofConversion
      (implication_conversion signature proofName left right)))

theorem Operations.implicationElim
    {signature : LogicalSignature Base Const} {proofName : DeclName}
    (operations : Operations signature proofName)
    {n : Nat} {context : Tower.Ctx n} {left right major minor : Tower.Tm n}
    (leftTyped : Presentation.FormationSensitive.Typing signature.rules context left
      (typeAt signature.types n .prop))
    (rightTyped : Presentation.FormationSensitive.Typing signature.rules context right
      (typeAt signature.types n .prop))
    (majorTyped : Presentation.FormationSensitive.Typing operations.target context major
      (FormationSensitiveHOLGenericProofFamily.proof proofName
        (FormationSensitiveHOLGenericProofFamily.rawImp signature left right)))
    (minorTyped : Presentation.FormationSensitive.Typing operations.target context minor
      (FormationSensitiveHOLGenericProofFamily.proof proofName left)) :
    Presentation.FormationSensitive.Typing operations.target context
      (.app major minor)
      (FormationSensitiveHOLGenericProofFamily.proof proofName right) := by
  open FormationSensitiveHOLGenericProofFamily in
  have converted := Presentation.FormationSensitive.Typing.conv majorTyped
    (operations.includeProofTyping
      (implication_formed signature proofName operations.fresh
        (include_typed signature proofName leftTyped)
        (include_typed signature proofName rightTyped)))
    operations.zeroUniverse
    (operations.includeProofConversion
      (implication_conversion signature proofName left right))
  simpa only [implicationFamily, inst0_rename_wk] using
    Presentation.FormationSensitive.Typing.appElim converted minorTyped

theorem Operations.universalIntro
    {signature : LogicalSignature Base Const} {proofName : DeclName}
    (operations : Operations signature proofName)
    {n : Nat} {context : Tower.Ctx n} {type : HOL.Ty Base}
    {proposition body : Tower.Tm (n + 1)}
    (domainTyped : Presentation.FormationSensitive.Typing signature.rules context
      (typeAt signature.types n type) (sortTm Tower.zero))
    (propositionTyped : Presentation.FormationSensitive.Typing signature.rules
      (.snoc context (typeAt signature.types n type)) proposition
      (typeAt signature.types (n + 1) .prop))
    (bodyTyped : Presentation.FormationSensitive.Typing operations.target
      (.snoc context (typeAt signature.types n type)) body
      (FormationSensitiveHOLGenericProofFamily.proof proofName proposition)) :
    Presentation.FormationSensitive.Typing operations.target context (.lam body)
      (FormationSensitiveHOLGenericProofFamily.proof proofName
        (FormationSensitiveHOLGenericProofFamily.universalProposition
          signature type (.lam proposition))) := by
  open FormationSensitiveHOLGenericProofFamily in
  exact .conv
    (.lamIntro
      (operations.includeProofTyping
        (pi_zero signature proofName
          (include_typed signature proofName domainTyped)
          (proof_formed signature proofName operations.fresh
            (include_typed signature proofName propositionTyped))))
      operations.zeroUniverse bodyTyped)
    (operations.includeProofTyping
      (proof_formed signature proofName operations.fresh
        (universal_lambda_proposition signature proofName
          (include_typed signature proofName domainTyped)
          (include_typed signature proofName propositionTyped))))
    operations.zeroUniverse
    (.symm _ _ (operations.includeProofConversion
      (universal_lambda_conversion signature proofName type proposition)))

theorem Operations.universalElim
    {signature : LogicalSignature Base Const} {proofName : DeclName}
    (operations : Operations signature proofName)
    {n : Nat} {context : Tower.Ctx n} {type : HOL.Ty Base}
    {proposition : Tower.Tm (n + 1)} {major argument : Tower.Tm n}
    (domainTyped : Presentation.FormationSensitive.Typing signature.rules context
      (typeAt signature.types n type) (sortTm Tower.zero))
    (propositionTyped : Presentation.FormationSensitive.Typing signature.rules
      (.snoc context (typeAt signature.types n type)) proposition
      (typeAt signature.types (n + 1) .prop))
    (majorTyped : Presentation.FormationSensitive.Typing operations.target context major
      (FormationSensitiveHOLGenericProofFamily.proof proofName
        (FormationSensitiveHOLGenericProofFamily.universalProposition
          signature type (.lam proposition))))
    (argumentTyped : Presentation.FormationSensitive.Typing signature.rules context argument
      (typeAt signature.types n type)) :
    Presentation.FormationSensitive.Typing operations.target context
      (.app major argument)
      (FormationSensitiveHOLGenericProofFamily.proof proofName
        (inst0 argument proposition)) := by
  open FormationSensitiveHOLGenericProofFamily in
  have converted := Presentation.FormationSensitive.Typing.conv majorTyped
    (operations.includeProofTyping
      (pi_zero signature proofName
        (include_typed signature proofName domainTyped)
        (proof_formed signature proofName operations.fresh
          (include_typed signature proofName propositionTyped))))
    operations.zeroUniverse
    (operations.includeProofConversion
      (universal_lambda_conversion signature proofName type proposition))
  simpa only [inst0, proof_subst] using
    Presentation.FormationSensitive.Typing.appElim converted
      (operations.includeSourceTyping argumentTyped)

/-- Recursive compilation through a law-bearing proof-operation algebra.
There is no recursive admission path which accepts an unchecked operation
table: every synthesized equality proof is supplied by `operations.raw`, whose
typing laws are retained by the surrounding `Operations`. -/
def compile (signature : LogicalSignature Base Const) (proofName : DeclName)
    (operations : Operations signature proofName)
    {gamma : HOL.Ctx Base} {delta : List (HOL.Formula Const gamma)}
    {phi : HOL.Formula Const gamma} (source : HOL.ProofSyntax Const delta phi)
    {n : Nat} (objects : Sub Tower.Head gamma.length n)
    (hypotheses : Fin delta.length → Tower.Tm n) : Option (Tower.Tm n) :=
  match source with
  | .hyp occurrence => some (hypotheses occurrence)
  | @HOL.ProofSyntax.impI _ _ gamma delta premise _ body => do
      let _ ← represent signature premise
      let nativeBody ← compile signature proofName operations body
        (fun i => rename wk (objects i))
        (Fin.cases (.var 0) (fun i => rename wk (hypotheses i)))
      pure (.lam nativeBody)
  | .impE function argument => do
      let nativeFunction ← compile signature proofName operations function objects hypotheses
      let nativeArgument ← compile signature proofName operations argument objects hypotheses
      pure (.app nativeFunction nativeArgument)
  | .allI body => do
      let nativeBody ← compile signature proofName operations body (liftSub objects)
        (fun i => rename wk
          (hypotheses (i.cast (by simp [HOL.weakenHyps]))))
      pure (.lam nativeBody)
  | .allE term function => do
      let nativeArgument ← represent signature term
      let nativeFunction ← compile signature proofName operations function objects hypotheses
      pure (.app nativeFunction (subst objects nativeArgument))
  | .eqRefl term => do
      let _ ← represent signature term
      operations.raw.reflexivity
  | @HOL.ProofSyntax.eqSymm _ _ _ _ type left right comparison => do
      let leftCode ← represent signature left
      let _ ← represent signature right
      let comparisonNative ← compile signature proofName operations comparison objects hypotheses
      operations.raw.symmetry type (subst objects leftCode) comparisonNative
  | @HOL.ProofSyntax.eqTrans _ _ _ _ type left middle right first second => do
      let leftCode ← represent signature left
      let _ ← represent signature middle
      let _ ← represent signature right
      let firstNative ← compile signature proofName operations first objects hypotheses
      let secondNative ← compile signature proofName operations second objects hypotheses
      operations.raw.transitivity type (subst objects leftCode) firstNative secondNative
  | @HOL.ProofSyntax.eqPropI _ _ _ _ left right forward backward => do
      let leftCode ← represent signature left
      let rightCode ← represent signature right
      let forwardNative ← compile signature proofName operations forward objects hypotheses
      let backwardNative ← compile signature proofName operations backward objects hypotheses
      operations.raw.propositionExtensionality (subst objects leftCode)
        (subst objects rightCode) forwardNative backwardNative
  | @HOL.ProofSyntax.eqPropEL _ _ _ _ left right comparison => do
      let _ ← represent signature left
      let _ ← represent signature right
      let comparisonNative ← compile signature proofName operations comparison objects hypotheses
      operations.raw.propositionForward comparisonNative
  | @HOL.ProofSyntax.eqPropER _ _ _ _ left right comparison => do
      let leftCode ← represent signature left
      let _ ← represent signature right
      let comparisonNative ← compile signature proofName operations comparison objects hypotheses
      let reversed ← operations.raw.symmetry .prop (subst objects leftCode) comparisonNative
      operations.raw.propositionForward reversed
  | @HOL.ProofSyntax.eqApp _ _ _ _ _ result function other argument comparison => do
      let functionCode ← represent signature function
      let _ ← represent signature other
      let argumentCode ← represent signature argument
      let comparisonNative ← compile signature proofName operations comparison objects hypotheses
      operations.raw.functionCongruence result (subst objects functionCode)
        (subst objects argumentCode) comparisonNative
  | @HOL.ProofSyntax.eqAppArg _ _ _ _ _ result function left right comparison => do
      let functionCode ← represent signature function
      let leftCode ← represent signature left
      let _ ← represent signature right
      let comparisonNative ← compile signature proofName operations comparison objects hypotheses
      operations.raw.argumentCongruence result (subst objects functionCode)
        (subst objects leftCode) comparisonNative
  | @HOL.ProofSyntax.eqLam _ _ _ _ domain codomain left right comparison => do
      let leftCode ← represent signature left
      let rightCode ← represent signature right
      let comparisonNative ← compile signature proofName operations comparison (liftSub objects)
        (fun i => rename wk
          (hypotheses (i.cast (by simp [HOL.weakenHyps]))))
      operations.raw.functionExtensionality
        (typeAt signature.types n domain) (typeAt signature.types n codomain)
        (.lam (subst (liftSub objects) leftCode))
        (.lam (subst (liftSub objects) rightCode)) (.lam comparisonNative)
  | @HOL.ProofSyntax.funExt _ _ _ _ domain codomain function other pointwise => do
      let functionCode ← represent signature function
      let otherCode ← represent signature other
      let pointwiseNative ← compile signature proofName operations pointwise objects hypotheses
      operations.raw.functionExtensionality
        (typeAt signature.types n domain) (typeAt signature.types n codomain)
        (subst objects functionCode) (subst objects otherCode) pointwiseNative
  | .beta term body => do
      let _ ← represent signature term
      let _ ← represent signature body
      operations.raw.reflexivity
  | @HOL.ProofSyntax.eta _ _ _ _ domain codomain function => do
      let functionCode ← represent signature function
      let functionTarget := subst objects functionCode
      let pointwise ← operations.raw.reflexivity
      operations.raw.functionExtensionality
        (typeAt signature.types n domain) (typeAt signature.types n codomain)
        (.lam (.app (rename wk functionTarget) (.var 0))) functionTarget
        (.lam pointwise)
  | _ => none

end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOLNativeGenericProofCompiler
