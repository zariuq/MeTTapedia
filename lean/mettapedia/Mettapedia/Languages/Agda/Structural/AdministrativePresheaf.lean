import Mettapedia.Languages.Agda.Structural.AdministrativeAdmission
import Mettapedia.Languages.Agda.Structural.Presentation
import Mettapedia.OSLF.Syntax.IntrinsicScopedLocalTelescopePresheaf
import Mettapedia.GSLT.Topos.PresheafEventModalities
import Mathlib.CategoryTheory.Limits.Shapes.FunctorToTypes

/-!
# Structural computation and static predicates over formed contexts

The base consists of admitted contexts and supported typed substitutions.
Raw terms and complete rule-local computation histories are restricted to
this base by forgetting admission. Formation and typing are subfunctors:
their restriction laws consume actual native substitution derivations.

Static derivation histories remain in the separate Type-valued family. This
file takes their support to form predicates; it does not assert that the
history transformation descends to proof-erased substitution arrows. Nor
does it assert that every raw reduction preserves typing. The latter needs
the independent computation-preservation proof.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Agda.Structural.AdministrativeStatics.Presheaf

open CategoryTheory
open Mettapedia.OSLF.Binding
open Mettapedia.GSLT.Topos.ConstructivePresheaf
open scoped Mettapedia.GSLT.Topos.ConstructivePresheaf
open Mettapedia.GSLT.Topos.PresheafEventModalities

abbrev Base := administrativeAdmission.admitted.base.Contextᵒᵖ

noncomputable def terms (s : Srt) : Base ⥤ Type :=
  restrict administrativeAdmission.forgetContext.op
    (IntrinsicScopedLocalTelescopePresheaf.terms sig .term .type s)

noncomputable def events (s : Srt) : Base ⥤ Type :=
  restrict administrativeAdmission.forgetContext.op
    (IntrinsicScopedLocalTelescopePresheaf.events Authored.computationRules .term .type s)

/-- The existing twenty-nine computation rules over formed contexts. -/
noncomputable def computation (s : Srt) : EventGraph Base where
  vertex := terms s
  edge := events s
  source :=
    { app _ := TypeCat.ofHom IntrinsicScopedLocalTelescopePresheaf.Event.source
      naturality _ _ _ := rfl }
  target :=
    { app _ := TypeCat.ofHom IntrinsicScopedLocalTelescopePresheaf.Event.target
      naturality _ _ _ := rfl }

noncomputable def formed : Subfunctor (terms .type) where
  obj X := {A | Nonempty (CoreDerivation (Statics.formed X.unop.val.val.2 A))}
  map {X Y} substitution := by
    rintro A ⟨formation⟩
    obtain ⟨evidence⟩ := substitution.unop.property
    exact ⟨CoreDerivation.substitution formation Y.unop.val.val.2
      substitution.unop.val evidence⟩

/-- A proposed annotated type and a term, before checking their relationship. -/
noncomputable def proposals : Base ⥤ Type :=
  FunctorToTypes.prod (terms .type) (terms .term)

noncomputable def typed : Subfunctor proposals where
  obj X := {pair | Nonempty
    (CoreDerivation (Statics.typed X.unop.val.val.2 pair.2 pair.1))}
  map {X Y} substitution := by
    rintro pair ⟨typing⟩
    obtain ⟨evidence⟩ := substitution.unop.property
    exact ⟨CoreDerivation.substitution typing Y.unop.val.val.2
      substitution.unop.val evidence⟩

noncomputable def proposedType : NatTrans proposals (terms .type) where
  app _ := TypeCat.ofHom Prod.fst
  naturality _ _ _ := rfl

noncomputable def proposedTerm : NatTrans proposals (terms .term) where
  app _ := TypeCat.ofHom Prod.snd
  naturality _ _ _ := rfl

/-- The predicate's endpoint law is the proved regularity fold, at every world. -/
theorem typing_implies_formation : typed ≤ preimage proposedType formed := by
  intro X pair member
  obtain ⟨tree⟩ := member
  exact ⟨CoreDerivation.typingFormation tree⟩

theorem typing_restrict {X Y : Base} (substitution : X ⟶ Y)
    (pair : proposals.obj X) (holds : pair ∈ typed.obj X) :
    proposals.map substitution pair ∈ typed.obj Y :=
  typed.map substitution holds

theorem formation_restrict {X Y : Base} (substitution : X ⟶ Y)
    (A : (terms .type).obj X) (holds : A ∈ formed.obj X) :
    (terms .type).map substitution A ∈ formed.obj Y :=
  formed.map substitution holds

/-- Existence of a native typing derivation at some annotated type. -/
noncomputable def typable : Subfunctor (terms .term) := image proposedTerm typed

theorem typable_iff (X : Base) (term : (terms .term).obj X) :
    term ∈ typable.obj X ↔ ∃ A : (terms .type).obj X,
      Nonempty (CoreDerivation (Statics.typed X.unop.val.val.2 term A)) := by
  constructor
  · rintro ⟨⟨A, term'⟩, proof, same⟩
    cases same
    exact ⟨A, proof⟩
  · rintro ⟨A, proof⟩
    exact ⟨(A, term), proof, rfl⟩

/-- Internal modal adjunction on predicates stable under typed substitution. -/
theorem computation_modal_adjunction (s : Srt) :
    GaloisConnection (diamond (computation s)) (box (computation s)) :=
  galois (computation s)

end Mettapedia.Languages.Agda.Structural.AdministrativeStatics.Presheaf
