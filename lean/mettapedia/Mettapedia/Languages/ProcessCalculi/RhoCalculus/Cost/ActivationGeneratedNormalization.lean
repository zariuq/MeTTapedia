import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationGenerated

/-!
# Generated reflective normalization through the pure erasure readout

The wrapped rho quote/drop equation survives apparatus erasure as an existing
rho structural equation. This compares observations; it does not identify
literal authority keys or turn structural normalization into a funded firing.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationGenerated

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.DerivedPresentationSyntax
open Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution
open Mettapedia.GSLT.LanguageDef
open Mettapedia.Languages.ProcessCalculi.RhoCalculus
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.Canonical
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefContinuedInteraction

abbrev wrappedRhoDeclaration :=
  costWrappedReflectivePresentationDecl rhoCIGSLT.theory
    rhoReflectivePresentation.toReflectivePresentationDecl

theorem wrappedRhoDeclaration_admitted :
    wrappedRhoDeclaration ∈ rhoCIGSLT.costWholeReflectionProfile.presentations := by
  decide +kernel

theorem wrappedRhoDeclaration_selected :
    substitutionPresentationForRule? rhoCIGSLT.costWholeReflectionProfile
      rhoCIGSLT.costWholeRedexRewrite = some wrappedRhoDeclaration := by
  decide +kernel

theorem eraseGeneratedList_congruent {left right : List Pattern}
    (related : List.Forall₂
      (fun first second => StructuralCongruence (eraseGenerated first) (eraseGenerated second))
      left right) :
    List.Forall₂ StructuralCongruence (eraseGeneratedList left) (eraseGeneratedList right) := by
  induction related with
  | nil => exact .nil
  | cons head tail induction => exact .cons head induction

theorem eraseGenerated_apply_congruent (constructor : String)
    {left right : List Pattern}
    (related : List.Forall₂
      (fun first second => StructuralCongruence (eraseGenerated first) (eraseGenerated second))
      left right) :
    StructuralCongruence (eraseGenerated (.apply constructor left))
      (eraseGenerated (.apply constructor right)) := by
  cases related with
  | nil => exact .refl _
  | @cons first second left right firstRelated tailRelated =>
    cases tailRelated with
    | nil =>
      by_cases funding : constructor = "$cost:apparatus-constructor:funding"
      · subst constructor
        exact .refl _
      · simpa [eraseGenerated, eraseGeneratedList, funding] using
          applyCongruence_of_forall₂ (eraseConstructor constructor)
            (.cons firstRelated .nil)
    | @cons firstTail secondTail leftTail rightTail tailHeadRelated tailsRelated =>
      cases tailsRelated with
      | nil =>
        by_cases signed : constructor = "$cost:apparatus-constructor:signed"
        · subst constructor
          exact firstRelated
        · by_cases contact : constructor = "$cost:apparatus-constructor:contact"
          · subst constructor
            exact collectionCongruence_of_forall₂ .hashBag none
              (.cons firstRelated (.cons tailHeadRelated .nil))
          · simpa [eraseGenerated, eraseGeneratedList, signed, contact] using
              applyCongruence_of_forall₂ (eraseConstructor constructor)
                (.cons firstRelated (.cons tailHeadRelated .nil))
      | @cons third fourth leftTail rightTail thirdRelated remaining =>
        simpa [eraseGenerated, eraseGeneratedList] using
          applyCongruence_of_forall₂ (eraseConstructor constructor)
            (.cons firstRelated (.cons tailHeadRelated
              (.cons thirdRelated (eraseGeneratedList_congruent remaining))))

theorem eraseGenerated_finishNormalizeReflectiveApply (constructor : String)
    (arguments : List Pattern) :
    StructuralCongruence
      (eraseGenerated (finishNormalizeReflectiveApply wrappedRhoDeclaration constructor arguments))
      (eraseGenerated (.apply constructor arguments)) := by
  have quoteName : wrappedRhoDeclaration.quoteConstructor =
      "$cost:wrapped-constructor:NQuote" := rfl
  have dropName : wrappedRhoDeclaration.dropConstructor =
      "$cost:wrapped-constructor:PDrop" := rfl
  unfold finishNormalizeReflectiveApply
  rw [quoteName, dropName]
  by_cases quote : constructor = "$cost:wrapped-constructor:NQuote"
  · subst constructor
    simp only [beq_self_eq_true, ite_true]
    cases arguments with
    | nil => exact .refl _
    | cons argument arguments =>
      cases arguments with
      | cons next remaining =>
        cases argument <;> try exact .refl _
        case apply drop dropArguments =>
          cases dropArguments with
          | nil => exact .refl _
          | cons name dropArguments =>
            cases dropArguments <;> exact .refl _
      | nil =>
        cases argument with
        | bvar index => exact .refl _
        | fvar name => exact .refl _
        | lambda binder body => exact .refl _
        | multiLambda arity binders body => exact .refl _
        | subst body replacement => exact .refl _
        | collection kind elements rest => exact .refl _
        | apply drop arguments =>
          cases arguments with
          | nil => exact .refl _
          | cons name arguments =>
            cases arguments with
            | cons next remaining => exact .refl _
            | nil =>
              by_cases sameDrop : drop = "$cost:wrapped-constructor:PDrop"
              · subst drop
                change StructuralCongruence (eraseGenerated name)
                  (.apply "NQuote" [.apply "PDrop" [eraseGenerated name]])
                exact .symm _ _ (.quote_drop _)
              · simp only [beq_iff_eq, sameDrop, ite_false]
                exact .refl _
  · simp only [beq_iff_eq, quote, ite_false]
    exact .refl _

private theorem erased_normalized_list (sources : List Pattern)
    (each : ∀ source ∈ sources,
      StructuralCongruence (eraseGenerated (normalizeReflective wrappedRhoDeclaration source))
        (eraseGenerated source)) :
    List.Forall₂
      (fun first second => StructuralCongruence (eraseGenerated first) (eraseGenerated second))
      (normalizeReflectiveList wrappedRhoDeclaration sources) sources := by
  induction sources with
  | nil => exact .nil
  | cons source sources induction =>
    exact .cons (each source List.mem_cons_self)
      (induction (fun member membership => each member (List.mem_cons_of_mem source membership)))

/-- Static generated quote/drop normalization preserves the existing
representation-level structural congruence after erasure. This does not
identify literal wrapper or authority keys. -/
theorem eraseGenerated_normalizeReflective (source : Pattern) :
    StructuralCongruence (eraseGenerated (normalizeReflective wrappedRhoDeclaration source))
      (eraseGenerated source) := by
  induction source using Pattern.inductionOn with
  | hbvar index => exact .refl _
  | hfvar name => exact .refl _
  | happly constructor arguments each =>
    exact .trans _ _ _
      (eraseGenerated_finishNormalizeReflectiveApply constructor
        (normalizeReflectiveList wrappedRhoDeclaration arguments))
      (eraseGenerated_apply_congruent constructor (erased_normalized_list arguments each))
  | hlambda binder body induction => exact .lambda_cong _ _ _ induction
  | hmultiLambda arity binders body induction => exact .multiLambda_cong _ _ _ _ induction
  | hsubst body replacement bodyInduction replacementInduction =>
    exact .subst_cong _ _ _ _ bodyInduction replacementInduction
  | hcollection kind elements rest each =>
    exact collectionCongruence_of_forall₂ kind rest
      (eraseGeneratedList_congruent (erased_normalized_list elements each))

/-- Preserving a rewrite-introduced outer quote retains provenance while
static normalization of its payload preserves the same pure observation. -/
theorem eraseGenerated_normalizeReflectiveReplacement (replacement : Pattern) :
    StructuralCongruence
      (eraseGenerated (normalizeReflectiveReplacement wrappedRhoDeclaration replacement))
      (eraseGenerated replacement) := by
  cases replacement <;> try exact eraseGenerated_normalizeReflective _
  case apply constructor arguments =>
    cases arguments with
    | nil => exact eraseGenerated_normalizeReflective _
    | cons payload rest =>
      cases rest with
      | cons next remaining => exact eraseGenerated_normalizeReflective _
      | nil =>
        by_cases quote : constructor = wrappedRhoDeclaration.quoteConstructor
        · simpa only [normalizeReflectiveReplacement, beq_iff_eq, quote, ite_true] using
            eraseGenerated_apply_congruent constructor
              (.cons (eraseGenerated_normalizeReflective payload) .nil)
        · simpa only [normalizeReflectiveReplacement, beq_iff_eq, quote, ite_false] using
            eraseGenerated_normalizeReflective (.apply constructor [payload])

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationGenerated
