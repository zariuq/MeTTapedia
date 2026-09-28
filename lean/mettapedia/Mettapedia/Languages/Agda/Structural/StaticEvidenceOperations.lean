import Mettapedia.Languages.Agda.Structural.StaticAdmission
import Mettapedia.Languages.Agda.Structural.StaticContextRegularity
import Mettapedia.Languages.Agda.Structural.StaticTypeEquivalence

/-!
# Shared derived operations on structural static evidence

An evidence family supplies its actual canonical rule algebra and the
renaming, substitution, context and finite-boundary operations already proved
for it. These data are instantiated below by the canonical rule trees and in
the spine extension by its combined rule trees. No endpoint regularity,
conversion injectivity, normalization or preservation result is a field.

The derived operations construct explicit trees. Changing a context declaration
uses identity on raw terms but a nontrivial conversion at its newest variable.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Agda.Structural.Statics

open Mettapedia.OSLF.Binding
open Mettapedia.OSLF.Binding.FiniteRulePremiseLists
open Mettapedia.TypeTheory

structure EvidenceOperations (D : Judgment → Type) where
  algebra : IndexedPolynomial.Algebra presentation.polynomial (fun _ j => D j)
  renameEvidence : ∀ {j : Judgment}, D j → RenamingAction D j
  substituteEvidence : ∀ {j : Judgment}, D j → SubstitutionAction D j
  contexts : ∀ {j : Judgment}, D j → ContextRegularity D j
  typeViews : ∀ {j : Judgment}, D j → TypeViews D j

noncomputable def canonicalOperations : EvidenceOperations Derivation where
  algebra := IndexedPolynomial.Algebra.initial presentation.polynomial
  renameEvidence := Derivation.renaming
  substituteEvidence := Derivation.substitution
  contexts := Derivation.contextRegularity
  typeViews := Derivation.typeViews

namespace EvidenceOperations

variable {D : Judgment → Type} (ops : EvidenceOperations D)

def build {j : Judgment} (shape : RuleShape j) (children : Evidence D (premises shape)) : D j :=
  ops.algebra.act () j ⟨shape, children⟩

def extend {n : Nat} {Γ : RawContext n} {A : RawTy n}
    (context : D (Statics.context Γ)) (domain : D (formed Γ A)) : D (Statics.context (Γ.snoc A)) :=
  ops.build (.extend Γ A) (consEvidence D context (consEvidence D domain (noEvidence D)))

def universeFormed {n : Nat} {Γ : RawContext n}
    (context : D (Statics.context Γ)) (level : Nat) : D (formed Γ (universeType n level).code) :=
  ops.build (.formation Γ (level + 1) (universeTerm level))
    (consEvidence D (ops.build (.sort Γ level) (consEvidence D context (noEvidence D))) (noEvidence D))

def piFormed {n : Nat} {Γ : RawContext n} {A : TypeParameter n} {B : TypeBody n}
    (domain : D (formed Γ A.code)) (codomain : D (formed (Γ.snoc A.code) B.open.code)) :
    D (formed Γ (piType A B).code) :=
  ops.build (.formation Γ (max A.level B.level) (B.pi A))
    (consEvidence D (ops.build (.pi Γ A B)
      (consEvidence D domain (consEvidence D codomain (noEvidence D)))) (noEvidence D))

def typeReflexivity {n : Nat} {Γ : RawContext n} {A : RawTy n}
    (formed : D (Statics.formed Γ A)) : D (typeEqual Γ A A) :=
  (ops.typeViews formed).reflexivity ops.algebra

def typeSymmetry {n : Nat} {Γ : RawContext n} {A B : RawTy n}
    (equal : D (typeEqual Γ A B)) : D (typeEqual Γ B A) :=
  (ops.typeViews equal).symmetry ops.algebra

def typeTransitivity {n : Nat} {Γ : RawContext n} {A B C : RawTy n}
    (first : D (typeEqual Γ A B)) (second : D (typeEqual Γ B C)) : D (typeEqual Γ A C) :=
  (ops.typeViews first).transitivity ops.algebra (ops.typeViews second)

def weakenFormation {n : Nat} {Γ : RawContext n} {A B : RawTy n}
    (domain : D (formed Γ A)) (type : D (formed Γ B)) : D (formed (Γ.snoc A) (weaken B)) := by
  have target := ops.extend (ops.contexts domain) domain
  have image := ops.renameEvidence type (Γ.snoc A)
    (Telescope.RawRen.projection (S := sig) .term n)
    (Telescope.RawRen.respects_projection Γ A) target
  exact (congrArg (fun T => D (formed (Γ.snoc A) T))
    (Telescope.bind_projection (S := sig) (b := .term) B)).mp image

def weakenTypeEquality {n : Nat} {Γ : RawContext n} {A B C : RawTy n}
    (domain : D (formed Γ A)) (equal : D (typeEqual Γ B C)) :
    D (typeEqual (Γ.snoc A) (weaken B) (weaken C)) := by
  have target := ops.extend (ops.contexts domain) domain
  have image := ops.renameEvidence equal (Γ.snoc A)
    (Telescope.RawRen.projection (S := sig) .term n)
    (Telescope.RawRen.respects_projection Γ A) target
  exact (congrArg₂ (fun B C => D (typeEqual (Γ.snoc A) B C))
    (Telescope.bind_projection (S := sig) (b := .term) B)
    (Telescope.bind_projection (S := sig) (b := .term) C)).mp image

def singleSubstitution {n : Nat} {Γ : RawContext n} {A : RawTy n} {argument : RawTm n}
    (domain : D (formed Γ A)) (typed : D (Statics.typed Γ argument A)) :
    TypedSubstitution D (Γ.snoc A) Γ (single argument) :=
  TypedSubstitution.pair ops.algebra
    (TypedSubstitution.identity ops.algebra (ops.contexts domain)) domain
    ((congrArg (fun T => D (Statics.typed Γ argument T)) (Telescope.bind_identity A)).mpr typed)

/-- The raw identity is typed using conversion at the newest declaration. -/
def changeLastSubstitution {n : Nat} {Γ : RawContext n} {A B : RawTy n}
    (first : D (formed Γ A)) (second : D (formed Γ B)) (equal : D (typeEqual Γ A B)) :
    TypedSubstitution D (Γ.snoc A) (Γ.snoc B) (Telescope.identity (S := sig) .term (n + 1)) := by
  let source := ops.extend (ops.contexts first) first
  let target := ops.extend (ops.contexts second) second
  refine ⟨source, target, fun v => ?_⟩
  cases v with
  | zero =>
    have newest := ops.build (.variable (Γ.snoc B) .zero) (consEvidence D target (noEvidence D))
    have converted := ops.build (.conversion (Γ.snoc B) (.var .zero) (weaken B) (weaken A))
      (consEvidence D newest (consEvidence D (ops.weakenTypeEquality second (ops.typeSymmetry equal)) (noEvidence D)))
    exact (congrArg (fun T => D (typed (Γ.snoc B) (.var .zero) T))
      (Telescope.bind_identity (ContextGeometry.lookup (Γ.snoc A) .zero))).mpr converted
  | succ v =>
    have older := ops.build (.variable (Γ.snoc B) (.succ v)) (consEvidence D target (noEvidence D))
    exact (congrArg (fun T => D (typed (Γ.snoc B) (.var (.succ v)) T))
      (Telescope.bind_identity (ContextGeometry.lookup (Γ.snoc A) (.succ v)))).mpr older

def changeLastFormation {n : Nat} {Γ : RawContext n} {A B : RawTy n} {C : RawTy (n + 1)}
    (first : D (formed Γ A)) (second : D (formed Γ B)) (equal : D (typeEqual Γ A B))
    (formed : D (Statics.formed (Γ.snoc A) C)) : D (Statics.formed (Γ.snoc B) C) :=
  (congrArg (fun T => D (Statics.formed (Γ.snoc B) T)) (Telescope.bind_identity C)).mp
    (ops.substituteEvidence formed (Γ.snoc B) (Telescope.identity (S := sig) .term (n + 1))
      (ops.changeLastSubstitution first second equal))

def changeLastTyping {n : Nat} {Γ : RawContext n} {A B : RawTy n} {C : RawTy (n + 1)} {t : RawTm (n + 1)}
    (first : D (formed Γ A)) (second : D (formed Γ B)) (equal : D (typeEqual Γ A B))
    (typed : D (Statics.typed (Γ.snoc A) t C)) : D (Statics.typed (Γ.snoc B) t C) :=
  (congrArg₂ (fun t T => D (Statics.typed (Γ.snoc B) t T))
    (Telescope.bind_identity t) (Telescope.bind_identity C)).mp
    (ops.substituteEvidence typed (Γ.snoc B) (Telescope.identity (S := sig) .term (n + 1))
      (ops.changeLastSubstitution first second equal))

end EvidenceOperations

end Mettapedia.Languages.Agda.Structural.Statics
