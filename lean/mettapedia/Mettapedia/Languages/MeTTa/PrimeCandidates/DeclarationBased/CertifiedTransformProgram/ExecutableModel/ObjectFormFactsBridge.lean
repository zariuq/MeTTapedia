import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel.ObjectChurchRecursor
import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel.ObjectSpineLift
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Annotated.FormFactsTransfer

/-!
# From the annotated facts of the object package to the facts about its raw weak-head forms

The annotation of the object package has the facts about the weak-head forms of its types
with no hypothesis (`objectFormFacts`), its root steps preserve types
(`objectRootPreserving`), and the erasures of its typed terms are strongly normalizing
(`objectChurch_erase_sn`, from the package's strong normalization).

So the facts about the weak-head forms of the package's own types follow from two
properties (`objectRules_formFacts_of`):

* **lifting**: every type, and every pair of equal types, of a formed context of the
  package is the erasure of annotated types over a formed annotated context erasing to it;
* **progress of annotated types**: a type of a universe of a formed annotated context
  takes an annotated weak-head step, or its erasure is in weak-head form.

With them the package's conversion algorithm is complete (`objectRules_algorithmicComplete_of`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation
open Presentation.TypedEquality
open Presentation.TypedEquality.Normalization
open Presentation.TypedEquality.Annotated

namespace CodeModel

/-- **The erasures of the object package's annotated typed terms are strongly
normalizing**: a typed annotated term erases to a typed term of the package. -/
theorem objectChurch_erase_sn {n : Nat} {Γ : CCtx Tower.Head n} {t A : CTm Tower.Head n}
    (formed : CCtxFormed objectChurch Γ) (typing : CTyped objectChurch Γ t A) :
    StrongNormalization.SN objectRules t.erase :=
  (objectRules_sn formed.erase (CDerivable.erase typing)).1

/-- **The facts about the weak-head forms of the object package's types**, from its
annotated facts, given that its types and equations of types lift to the annotation and
that the annotated types of a universe progress. -/
theorem objectRules_formFacts_of
    (liftType : ∀ {n : Nat} {Γ : Tower.Ctx n} {A : Tower.Tm n}, CtxFormed objectRules Γ →
      IsType objectRules Γ A → ∃ (Γ' : CCtx Tower.Head n) (A' : CTm Tower.Head n),
        CCtxFormed objectChurch Γ' ∧ Γ'.erase = Γ ∧ A'.erase = A ∧ CIsType objectChurch Γ' A')
    (liftTypeEq : ∀ {n : Nat} {Γ : Tower.Ctx n} {A B : Tower.Tm n}, CtxFormed objectRules Γ →
      TypeEq objectRules Γ A B → ∃ (Γ' : CCtx Tower.Head n) (A' B' : CTm Tower.Head n),
        CCtxFormed objectChurch Γ' ∧ Γ'.erase = Γ ∧ A'.erase = A ∧ B'.erase = B ∧
          CTypeEq objectChurch Γ' A' B')
    (progress : ∀ {n : Nat} {Γ : CCtx Tower.Head n} {A : CTm Tower.Head n} {u : Tower.Head},
      CCtxFormed objectChurch Γ → objectRules.isUniverse u → CTyped objectChurch Γ A (.head u) →
        (∃ A', CWhStepR objectChurch objectRoles A A') ∨ IsTypeForm objectRoles A.erase) :
    FormFacts objectRules objectRoles :=
  FormFacts.ofAnnotated ConvRules.objectLevels objectFormFacts objectRootAdmitted
    objectChurch_erase_sn liftType liftTypeEq progress

/-- **The object package's conversion algorithm is complete**, given the same two
properties: derivably equal terms of a formed context are algorithmically equal. -/
theorem objectRules_algorithmicComplete_of
    (liftType : ∀ {n : Nat} {Γ : Tower.Ctx n} {A : Tower.Tm n}, CtxFormed objectRules Γ →
      IsType objectRules Γ A → ∃ (Γ' : CCtx Tower.Head n) (A' : CTm Tower.Head n),
        CCtxFormed objectChurch Γ' ∧ Γ'.erase = Γ ∧ A'.erase = A ∧ CIsType objectChurch Γ' A')
    (liftTypeEq : ∀ {n : Nat} {Γ : Tower.Ctx n} {A B : Tower.Tm n}, CtxFormed objectRules Γ →
      TypeEq objectRules Γ A B → ∃ (Γ' : CCtx Tower.Head n) (A' B' : CTm Tower.Head n),
        CCtxFormed objectChurch Γ' ∧ Γ'.erase = Γ ∧ A'.erase = A ∧ B'.erase = B ∧
          CTypeEq objectChurch Γ' A' B')
    (progress : ∀ {n : Nat} {Γ : CCtx Tower.Head n} {A : CTm Tower.Head n} {u : Tower.Head},
      CCtxFormed objectChurch Γ → objectRules.isUniverse u → CTyped objectChurch Γ A (.head u) →
        (∃ A', CWhStepR objectChurch objectRoles A A') ∨ IsTypeForm objectRoles A.erase) :
    AlgorithmicComplete objectRules objectRoles :=
  ConvRules.object_algorithmicComplete_of_facts (objectRules_formFacts_of liftType liftTypeEq progress)

end CodeModel

end Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel
