import Mettapedia.TypeTheory.ContextualLocalUniversesDecoding
import Mettapedia.TypeTheory.ContextualComprehensionMorphism
import Mettapedia.TypeTheory.ContextualStrictMorphismComposition

/-!
# Actual contextual maps of local family presentations

A contextual morphism maps all three parts of a local presentation: its
parameter context, family and naming substitution. Decoding that result
agrees with mapping the original decoded family. The actual supplied term
is transported through this equality, rather than selected anew.

The family action below derives naturality from the original contextual
map. Its selected terminal and comprehension structure are likewise
derived from the actual source morphism. No logical-constructor preservation
is assumed or inferred from this contextual construction.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.TypeTheory.ContextualLocalUniversesMorphism

open _root_.CategoryTheory
open Mettapedia.GSLT.Core.ContextualLadder
open ContextualLocalUniverses ContextualComprehensionMorphism

universe u v w'
variable {C D E : CwfWithTerminal.{u, v, max u v, w'}}

private theorem family_ext {X Y : Cwf.{u, v, max u v, w'}}
    {first second : CwfFamilyMorphism X Y} (bases : first.base = second.base)
    (families : HEq first.family second.family) : first = second := by
  cases first
  cases second
  cases bases
  cases families
  rfl

def typeAction (F : StrictCwfMorphism C D) {Γ : C.toCwf.Ctx}
    (A : LocalType C.toCwf Γ) : LocalType D.toCwf (context F Γ) where
  parameters := context F A.parameters
  family := F.toFamilyMorphism.mapType A.family
  name := F.toFamilyMorphism.base.map A.name

theorem decoding_square (F : StrictCwfMorphism C D) {Γ : C.toCwf.Ctx}
    (A : LocalType C.toCwf Γ) :
    (typeAction F A).decoded = F.toFamilyMorphism.mapType A.decoded :=
  (F.toFamilyMorphism.mapType_substitution A.name A.family).symm

def termAction (F : StrictCwfMorphism C D) {Γ : C.toCwf.Ctx}
    {A : LocalType C.toCwf Γ} (term : Term C.toCwf Γ A) :
    Term D.toCwf (context F Γ) (typeAction F A) :=
  cast (congrArg (D.toCwf.Tm (context F Γ)) (decoding_square F A).symm)
    (F.toFamilyMorphism.mapTerm term)

theorem termAction_heq (F : StrictCwfMorphism C D) {Γ : C.toCwf.Ctx}
    {A : LocalType C.toCwf Γ} (term : Term C.toCwf Γ A) :
    HEq (termAction F term) (F.toFamilyMorphism.mapTerm term) := cast_heq _ _

theorem typeAction_substitution (F : StrictCwfMorphism C D)
    {Γ Δ : C.toCwf.Ctx} (A : LocalType C.toCwf Δ) (σ : C.toCwf.Sub Γ Δ) :
    typeAction F (A.reindex σ) = (typeAction F A).reindex (F.toFamilyMorphism.base.map σ) := by
  cases A with
  | mk parameters family name =>
    exact congrArg (fun naming =>
      (⟨context F parameters, F.toFamilyMorphism.mapType family, naming⟩ :
        LocalType D.toCwf (context F Γ))) (F.toFamilyMorphism.base.map_comp σ name)

theorem termAction_substitution (F : StrictCwfMorphism C D)
    {Γ Δ : C.toCwf.Ctx} {A : LocalType C.toCwf Δ}
    (term : Term C.toCwf Δ A) (σ : C.toCwf.Sub Γ Δ) :
    HEq (termAction F (substituteTerm term σ))
      (substituteTerm (termAction F term) (F.toFamilyMorphism.base.map σ)) := by
  refine (termAction_heq F (substituteTerm term σ)).trans ?_
  refine (F.mapTerm_heq (A.decoded_reindex σ) (substituteTerm_heq term σ)).trans ?_
  refine (F.toFamilyMorphism.mapTerm_substitution term σ).trans ?_
  refine (tmSub_heq (E := D.toCwf) rfl rfl
    (heq_of_eq (decoding_square F A)).symm (termAction_heq F term).symm HEq.rfl).trans ?_
  exact (substituteTerm_heq (termAction F term) (F.toFamilyMorphism.base.map σ)).symm

def familyAction (F : StrictCwfMorphism C D) :
    CwfFamilyMorphism (localCwf C.toCwf) (localCwf D.toCwf) where
  base := F.toFamilyMorphism.base
  family := {
    app := fun _ => {
      onIndex := typeAction F
      onFibre := fun _ => termAction F }
    naturality := by
      intro first second arrow
      apply IndexedFamily.Hom.ext
      · funext A
        exact typeAction_substitution F A arrow.unop
      · intro A term
        exact termAction_substitution F term arrow.unop }

@[simp] theorem familyAction_type (F : StrictCwfMorphism C D) {Γ : C.toCwf.Ctx}
    (A : LocalType C.toCwf Γ) : (familyAction F).mapType A = typeAction F A := rfl

theorem familyAction_term (F : StrictCwfMorphism C D) {Γ : C.toCwf.Ctx}
    {A : LocalType C.toCwf Γ} (term : Term C.toCwf Γ A) :
    HEq ((familyAction F).mapTerm term) (F.toFamilyMorphism.mapTerm term) :=
  termAction_heq F term

theorem extension_square (F : StrictCwfMorphism C D) (Γ : C.toCwf.Ctx)
    (A : LocalType C.toCwf Γ) :
    F.toFamilyMorphism.base.obj ⟨extension Γ A⟩ =
      ⟨extension (context F Γ) (typeAction F A)⟩ :=
  (F.extension_preserved Γ A.decoded).trans
    (congrArg (fun type => (⟨D.toCwf.ext (context F Γ) type⟩ : D.toCwf.base.Context))
      (decoding_square F A).symm)

def strictAction (F : StrictCwfMorphism C D) :
    StrictCwfMorphism (localCwfWithTerminal C) (localCwfWithTerminal D) where
  toFamilyMorphism := familyAction F
  empty_preserved := F.empty_preserved
  extension_preserved := extension_square F
  projection_preserved := by
    intro Γ A
    change F.toFamilyMorphism.base.map (C.toCwf.wk A.decoded) =
      eqToHom (extension_square F Γ A) ≫ D.toCwf.wk (typeAction F A).decoded
    have related := (projection_heq F Γ A.decoded).trans
      (wk_heq (E := D.toCwf) rfl (heq_of_eq (decoding_square F A)).symm)
    have square := diagram_of_heq (E := D.toCwf) (extension_square F Γ A) rfl
      (F.toFamilyMorphism.base.map (C.toCwf.wk A.decoded))
      (D.toCwf.wk (typeAction F A).decoded) related
    simpa only [eqToHom_refl, Category.comp_id] using square
  variable_preserved := by
    intro Γ A
    refine (termAction_heq F (genericVariable A)).trans ?_
    refine (F.mapTerm_heq (A.decoded_reindex (projection A)) (genericVariable_heq A)).trans ?_
    refine (variable_heq F Γ A.decoded).trans ?_
    refine (vz_heq (E := D.toCwf) rfl (heq_of_eq (decoding_square F A)).symm).trans ?_
    refine (genericVariable_heq (typeAction F A)).symm.trans ?_
    exact (term_eqToHom_heq (E := localCwf D.toCwf) (extension_square F Γ A)
      (genericVariable (typeAction F A))).symm

/-- Both orders of mapping and decoding retain the supplied term. -/
theorem decoder_term_square (F : StrictCwfMorphism C D) {Γ : C.toCwf.Ctx}
    {A : LocalType C.toCwf Γ} (term : Term C.toCwf Γ A) :
    HEq ((familyDecoder D.toCwf).mapTerm ((strictAction F).toFamilyMorphism.mapTerm term))
      (F.toFamilyMorphism.mapTerm ((familyDecoder C.toCwf).mapTerm term)) :=
  termAction_heq F term

@[simp] theorem typeAction_identity {Γ : C.toCwf.Ctx}
    (A : LocalType C.toCwf Γ) : typeAction (StrictCwfMorphism.identity C) A = A := by
  cases A
  rfl

theorem termAction_identity {Γ : C.toCwf.Ctx} {A : LocalType C.toCwf Γ}
    (term : Term C.toCwf Γ A) :
    HEq (termAction (StrictCwfMorphism.identity C) term) term :=
  termAction_heq _ term

@[simp] theorem typeAction_composition (first : StrictCwfMorphism C D)
    (second : StrictCwfMorphism D E) {Γ : C.toCwf.Ctx} (A : LocalType C.toCwf Γ) :
    typeAction (ContextualStrictMorphismComposition.compose first second) A =
      typeAction second (typeAction first A) := rfl

theorem termAction_composition (first : StrictCwfMorphism C D)
    (second : StrictCwfMorphism D E) {Γ : C.toCwf.Ctx} {A : LocalType C.toCwf Γ}
    (term : Term C.toCwf Γ A) :
    HEq (termAction (ContextualStrictMorphismComposition.compose first second) term)
      (termAction second (termAction first term)) := by
  refine (termAction_heq _ term).trans ?_
  refine (second.mapTerm_heq (decoding_square first A).symm
    (termAction_heq first term).symm).trans ?_
  exact (termAction_heq second (termAction first term)).symm

/-- Decoding commutes on the entire natural type-and-term family map. -/
theorem decoder_family_square (F : StrictCwfMorphism C D) :
    (familyAction F).comp (familyDecoder D.toCwf) =
      (familyDecoder C.toCwf).comp F.toFamilyMorphism := by
  refine family_ext ?_ ?_
  · rfl
  · apply heq_of_eq
    apply NatTrans.ext
    funext Γ
    apply IndexedFamily.Hom.ext
    · funext A
      exact decoding_square F A
    · intro A term
      exact decoder_term_square F term

theorem strictAction_identity :
    strictAction (StrictCwfMorphism.identity C) =
      StrictCwfMorphism.identity (localCwfWithTerminal C) := by
  apply ContextualStrictMorphismComposition.ext_of_family
  refine family_ext ?_ ?_
  · rfl
  · apply heq_of_eq
    apply NatTrans.ext
    funext Γ
    apply IndexedFamily.Hom.ext
    · funext A
      exact typeAction_identity A
    · intro A term
      exact termAction_identity term

theorem strictAction_composition (first : StrictCwfMorphism C D)
    (second : StrictCwfMorphism D E) :
    strictAction (ContextualStrictMorphismComposition.compose first second) =
      ContextualStrictMorphismComposition.compose (strictAction first) (strictAction second) := by
  apply ContextualStrictMorphismComposition.ext_of_family
  refine family_ext ?_ ?_
  · rfl
  · apply heq_of_eq
    apply NatTrans.ext
    funext Γ
    apply IndexedFamily.Hom.ext
    · funext A
      exact typeAction_composition first second A
    · intro A term
      exact termAction_composition first second term

end Mettapedia.TypeTheory.ContextualLocalUniversesMorphism
