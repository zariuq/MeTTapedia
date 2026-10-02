import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel.ObjectFormFactsBridge
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Annotated.Lifting

/-!
# Lifting the object package's derivations to its annotation

The Church–Curry correspondence for the object package: every derivation of the package
over a formed context is the erasure of a derivation of its annotation `objectChurch`
(`objectRules_lifts`), with no hypothesis. The generic lifting (`Annotated.lifts`) needs four
facts about the annotation, all of which the object package has (`objectLiftingFacts`):

* coherence of annotations (`objectCoherence`);
* root lifting (`objectChurch_lift`), from its first-order, left-linear schemas;
* root preservation (`objectRootPreserving`);
* formed declared types: no declared type of the package has an abstraction
  (`objectChurch_declared_lamFree`), so an annotated declared type is the only annotation of
  its erasure (`objectChurch_rigid`), and a type as soon as some annotation of its erasure is.

In the forms the transfer of the facts about weak-head forms consumes:

* **types lift** (`objectRules_liftType`);
* **equations of types lift** (`objectRules_liftTypeEq`).

So the facts about the weak-head forms of the package's types, and the completeness of its
conversion algorithm, now depend only on the progress of annotated types
(`objectRules_formFacts_of_progress`, `objectRules_algorithmicComplete_of_progress`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation
open Presentation.TypedEquality
open Presentation.TypedEquality.Normalization
open Presentation.TypedEquality.Annotated

namespace CodeModel

/-! ## The facts lifting needs -/

/-- **No declared type of the object package has an abstraction**: every annotated declared
type erases to a term without abstractions. -/
theorem objectChurch_declared_lamFree {c : DeclName} {D : CTm Tower.Head 0}
    (declared : objectChurch.constantType c = some D) : lamFree D.erase = true := by
  rw [objectChurch_constantType] at declared
  unfold elabDeclarations at declared
  cases hT : objectRules.constantType c with
  | none =>
      rw [hT] at declared
      cases declared
  | some T =>
      rw [hT, Option.map_some] at declared
      obtain rfl := Option.some.inj declared
      rw [erase_elabClosed]
      rcases objectRules_constantType_cases hT with ⟨type, rfl, rfl⟩ | ⟨type, rfl, rfl⟩ | hmem
      · exact lamFree_typeAt (.arr (.arr type .prop) .prop) 0
      · exact lamFree_typeAt (.arr type (.arr type .prop)) 0
      · exact fixedDecls_lamFree _ hmem

/-- **The object package's annotated declared types are rigid**: each is the only annotation
of its erasure. -/
theorem objectChurch_rigid : CDeclsRigid objectChurch :=
  rigid_of_lamFree objectChurch_declared_lamFree

/-- **The facts lifting needs, for the object package**, with no hypothesis. -/
theorem objectLiftingFacts : LiftingFacts objectChurch where
  coherent := fun formed typing typing' same => objectCoherence formed typing typing' same
  lift := fun step => objectChurch_lift step
  admitted := objectRootAdmitted
  declared := objectChurch_rigid.formed

/-! ## Lifting -/

/-- **Every derivation of the object package lifts to its annotation**, over every formed
annotated context erasing to its context. -/
theorem objectRules_lifts {statement : Statement Tower.Head}
    (derivation : Derivable objectRules statement) : Lifts objectChurch statement :=
  lifts ConvRules.objectLevels objectLiftingFacts derivation

/-- **A formed context of the object package is the erasure of a formed annotated
context.** -/
theorem objectRules_liftCtx {n : Nat} {Γ : Tower.Ctx n} (formed : CtxFormed objectRules Γ) :
    ∃ Γ' : CCtx Tower.Head n, CCtxFormed objectChurch Γ' ∧ Γ'.erase = Γ :=
  lift_ctxFormed ConvRules.objectLevels objectLiftingFacts formed

/-- **The object package's types lift**: a type of a formed context is the erasure of a type
of a formed annotated context erasing to it. -/
theorem objectRules_liftType {n : Nat} {Γ : Tower.Ctx n} {A : Tower.Tm n}
    (formed : CtxFormed objectRules Γ) (type : IsType objectRules Γ A) :
    ∃ (Γ' : CCtx Tower.Head n) (A' : CTm Tower.Head n),
      CCtxFormed objectChurch Γ' ∧ Γ'.erase = Γ ∧ A'.erase = A ∧ CIsType objectChurch Γ' A' :=
  lift_isType ConvRules.objectLevels objectLiftingFacts formed type

/-- **The object package's equations of types lift**: two equal types of a formed context
are the erasures of two equal types of one formed annotated context erasing to it. -/
theorem objectRules_liftTypeEq {n : Nat} {Γ : Tower.Ctx n} {A B : Tower.Tm n}
    (formed : CtxFormed objectRules Γ) (equal : TypeEq objectRules Γ A B) :
    ∃ (Γ' : CCtx Tower.Head n) (A' B' : CTm Tower.Head n),
      CCtxFormed objectChurch Γ' ∧ Γ'.erase = Γ ∧ A'.erase = A ∧ B'.erase = B ∧
        CTypeEq objectChurch Γ' A' B' :=
  lift_typeEq ConvRules.objectLevels objectLiftingFacts formed equal

/-! ## The facts about weak-head forms, from progress alone -/

/-- **The facts about the weak-head forms of the object package's types**, given only that
the annotated types of a universe progress. -/
theorem objectRules_formFacts_of_progress
    (progress : ∀ {n : Nat} {Γ : CCtx Tower.Head n} {A : CTm Tower.Head n} {u : Tower.Head},
      CCtxFormed objectChurch Γ → objectRules.isUniverse u → CTyped objectChurch Γ A (.head u) →
        (∃ A', CWhStepR objectChurch objectRoles A A') ∨ IsTypeForm objectRoles A.erase) :
    FormFacts objectRules objectRoles :=
  objectRules_formFacts_of objectRules_liftType objectRules_liftTypeEq progress

/-- **The object package's conversion algorithm is complete**, given only that the annotated
types of a universe progress. -/
theorem objectRules_algorithmicComplete_of_progress
    (progress : ∀ {n : Nat} {Γ : CCtx Tower.Head n} {A : CTm Tower.Head n} {u : Tower.Head},
      CCtxFormed objectChurch Γ → objectRules.isUniverse u → CTyped objectChurch Γ A (.head u) →
        (∃ A', CWhStepR objectChurch objectRoles A A') ∨ IsTypeForm objectRoles A.erase) :
    AlgorithmicComplete objectRules objectRoles :=
  objectRules_algorithmicComplete_of objectRules_liftType objectRules_liftTypeEq progress

end CodeModel

end Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel
