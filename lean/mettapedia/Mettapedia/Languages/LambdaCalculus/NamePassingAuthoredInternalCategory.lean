import Mettapedia.Languages.LambdaCalculus.NamePassingAuthoredClassified
import Mettapedia.CategoryTheory.InternalCategoryPathMaps
import Mettapedia.GSLT.Core.LambdaTheory

/-!
# Names, terms and retained events in the actual quotient-clone model

The finite-limit and closed ambient category is the real presheaf category
of the authored equation quotient. Names and terms are singleton-context
representables. The reference-binding body object is the genuine presheaf
exponential, with its complete future-section decoder. Event points are
whole free rule trees at their actual equation-class endpoints.

The retained event graph generates an internal path category on the chosen
composable-edge pullback. Its one-edge endpoint image is compared with the
actual classified reduction. This concrete model is not identified with a
free finite-limit/closed guest presentation by the path construction alone.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.Languages.LambdaCalculus.NamePassing.AuthoredInternalCategory

open _root_.CategoryTheory
open Mettapedia.OSLF.Binding
open Mettapedia.CategoryTheory
open Presentation AuthoredClassified
open IntrinsicScopedConditionalPresheaf

abbrev Base := IntrinsicScopedConditionalPresheaf.Base AuthoredClassified.algebra
abbrev Ambient := Base ⥤ Type

def theory : Mettapedia.GSLT.Core.LambdaTheory :=
  Mettapedia.GSLT.Core.LambdaTheory.ofCategory Ambient

def names : Ambient := programs AuthoredClassified.algebra Srt.nm
def terms : Ambient := programs AuthoredClassified.algebra Srt.tm

def boundBodies : Ambient := binderBodies AuthoredClassified.algebra Srt.nm Srt.tm

/-- The entire future-sensitive function section, not only a present value,
corresponds to an authored body in the extended clone context. -/
def boundBodyIso : names.functorHom terms ≅ boundBodies :=
  binderBodiesIso AuthoredClassified.algebra Srt.nm Srt.tm

abbrev treeModel := IntrinsicScopedAuthoredClassifiedInstance.treeModel
  AuthoredOperationalProfile.rules AuthoredClassified.algebra

def events : Ambient :=
  IntrinsicScopedOperationalPresheafEvents.sortEvents treeModel.toAction Srt.tm

def source : events ⟶ terms :=
  IntrinsicScopedOperationalPresheafEventPowers.source treeModel.toAction Srt.tm

def target : events ⟶ terms :=
  IntrinsicScopedOperationalPresheafEventPowers.target treeModel.toAction Srt.tm

def graph : InternalGraph Ambient := ⟨terms, events, source, target⟩

def internalCategory : InternalCategory Ambient := InternalCategoryPathDiagram.category graph

abbrev SourceValue (X : Base) := AuthoredClassified.algebra.substitution.Carrier X.unop.context Srt.tm

abbrev TreeAt (X : Base) (first last : SourceValue X) :=
  IntrinsicScopedLocalPolynomial.Tree AuthoredOperationalProfile.rules AuthoredClassified.algebra
    ⟨X.unop.context, Srt.tm, first, last⟩

def eventAtEquiv (X : Base) : (events.obj X) ≃
    Σ pair : SourceValue X × SourceValue X, TreeAt X pair.1 pair.2 where
  toFun event := by
    rcases event with ⟨⟨sort, pair, evidence⟩, same⟩
    cases same
    exact ⟨pair, evidence⟩
  invFun pair := ⟨⟨Srt.tm, pair.1, pair.2⟩, rfl⟩
  left_inv event := by
    rcases event with ⟨⟨sort, pair, evidence⟩, same⟩
    cases same
    rfl
  right_inv _ := rfl

theorem complete_source_readout (X : Base) (event : events.obj X) :
    programsAtEquiv AuthoredClassified.algebra Srt.tm X (source.app X event) =
      (eventAtEquiv X event).1.1 := by
  rcases event with ⟨⟨sort, pair, evidence⟩, same⟩
  cases same
  change programsAtEquiv AuthoredClassified.algebra Srt.tm X
    ((programsAtEquiv AuthoredClassified.algebra Srt.tm X).symm
      pair.1) = pair.1
  exact (programsAtEquiv AuthoredClassified.algebra Srt.tm X).apply_symm_apply _

theorem complete_target_readout (X : Base) (event : events.obj X) :
    programsAtEquiv AuthoredClassified.algebra Srt.tm X (target.app X event) =
      (eventAtEquiv X event).1.2 := by
  rcases event with ⟨⟨sort, pair, evidence⟩, same⟩
  cases same
  change programsAtEquiv AuthoredClassified.algebra Srt.tm X
    ((programsAtEquiv AuthoredClassified.algebra Srt.tm X).symm
      pair.2) = pair.2
  exact (programsAtEquiv AuthoredClassified.algebra Srt.tm X).apply_symm_apply _

/-- Every supplied tree determines a complete event, and every complete
event determines a tree at exactly the supplied class endpoints. -/
theorem endpoints_iff_tree (X : Base) (first last : SourceValue X) :
    (∃ event : events.obj X,
      programsAtEquiv AuthoredClassified.algebra Srt.tm X (source.app X event) = first ∧
      programsAtEquiv AuthoredClassified.algebra Srt.tm X (target.app X event) = last) ↔
      Nonempty (TreeAt X first last) := by
  constructor
  · rintro ⟨event, before, after⟩
    have firstRead : (eventAtEquiv X event).1.1 = first :=
      (complete_source_readout X event).symm.trans before
    have lastRead : (eventAtEquiv X event).1.2 = last :=
      (complete_target_readout X event).symm.trans after
    have tree := (eventAtEquiv X event).2
    rw [firstRead, lastRead] at tree
    exact ⟨tree⟩
  · rintro ⟨tree⟩
    let event := (eventAtEquiv X).symm ⟨(first, last), tree⟩
    have whole := (eventAtEquiv X).apply_symm_apply (⟨(first, last), tree⟩)
    refine ⟨event, ?_, ?_⟩
    · exact (complete_source_readout X event).trans
        (congrArg (fun whole => whole.1.1) whole)
    · exact (complete_target_readout X event).trans
        (congrArg (fun whole => whole.1.2) whole)

/-- The concrete retained edge diagram and the genuine classified generic
reduction have the same endpoint image at the authored program sections. -/
theorem endpoints_iff_extendedReduction {Γ : Ctx signature} (first last : Program Γ) :
    let X := IntrinsicScopedAuthoredClassifiedReduction.stage AuthoredEquations.equations Γ
    (∃ event : events.obj X,
      programsAtEquiv AuthoredClassified.algebra Srt.tm X (source.app X event) =
        AuthoredClassified.projection.raw.map first ∧
      programsAtEquiv AuthoredClassified.algebra Srt.tm X (target.app X event) =
        AuthoredClassified.projection.raw.map last) ↔
      IntrinsicScopedAuthoredClassifiedReduction.ExtendedReduction AuthoredOperationalProfile.rules
        AuthoredEquations.equations first last := by
  exact (endpoints_iff_tree _ _ _).trans
    (IntrinsicScopedAuthoredClassifiedReduction.extension_iff_tree AuthoredOperationalProfile.rules
      AuthoredEquations.equations first last).symm

end Mettapedia.Languages.LambdaCalculus.NamePassing.AuthoredInternalCategory
