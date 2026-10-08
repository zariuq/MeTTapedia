import Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementContextualRefinements
import Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementContextualHeyting

/-!
# Retained refinement values of the generated contextual model

The operations use the actual generated refinement judgments after retyping
the complete supplied term class at a chosen annotation. A guard is the
generated predicate pulled along the actual contextual section. Introduction,
forgetting and their beta and eta equations preserve that supplied class.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.Contextual.RefinementValues

open _root_.CategoryTheory
open QuotientComprehensionSyntax
open Mettapedia.TypeTheory.ContextualProductComparison (selfExtend)

universe u
variable {S : Symbols.{u}} {D : Signature S}

/-- Predicate substitution is the actual quotient-arrow presheaf action. -/
def predicateSub {source target : QuotientCwf.QContext D}
    (predicate : QPredicate target.as) (substitution : source ⟶ target) :
    QPredicate source.as :=
  (QPredicate.presheaf D).map substitution.op predicate

theorem predicateSub_project {source target : Context D}
    (predicate : QPredicate target) (substitution : source ⟶ target) :
    predicateSub predicate (QuotientCwf.project substitution) = predicate.reindex substitution := rfl

theorem predicateSub_representative {source target : QuotientCwf.QContext D}
    (predicate : QPredicate target.as) (substitution : source ⟶ target) :
    predicateSub predicate substitution = predicate.reindex (QuotientCwf.representative substitution) := by
  conv_lhs => rw [← QuotientCwf.project_representative substitution]
  rfl

theorem predicateSub_id {context : QuotientCwf.QContext D} (predicate : QPredicate context.as) :
    predicateSub predicate (𝟙 context) = predicate := QPredicate.reindex_id predicate

theorem predicateSub_comp {source middle target : QuotientCwf.QContext D}
    (predicate : QPredicate target.as) (earlier : source ⟶ middle) (later : middle ⟶ target) :
    predicateSub predicate (earlier ≫ later) =
      predicateSub (predicateSub predicate later) earlier := by
  induction earlier using Quot.inductionOn with
  | h earlier =>
    induction later using Quot.inductionOn with
    | h later => exact QPredicate.reindex_comp predicate earlier later

theorem predicateSub_entails {source target : QuotientCwf.QContext D}
    {predicate : QPredicate target.as} (evidence : predicate.entails)
    (substitution : source ⟶ target) : (predicateSub predicate substitution).entails := by
  rw [predicateSub_representative]
  exact QPredicate.entails_reindex evidence _

noncomputable def predicateRepresentative {context : Context D} (predicate : QPredicate context) :
    PredicateOver context := Quotient.out predicate

theorem predicateRepresentative_class {context : Context D} (predicate : QPredicate context) :
    QPredicate.mk (predicateRepresentative predicate) = predicate := Quotient.out_eq predicate

noncomputable def typeRepresentative {context : QuotientCwf.QContext D}
    {domain : QuotientCwf.Ty context} (predicate : QPredicate (QuotientCwf.ext context domain).as) :
    TypeOver context.as :=
  Refinements.rawType (QuotientCwf.typeRepresentative domain) (predicateRepresentative predicate)

theorem typeRepresentative_class {context : QuotientCwf.QContext D}
    {domain : QuotientCwf.Ty context} (predicate : QPredicate (QuotientCwf.ext context domain).as) :
    QType.mk (typeRepresentative predicate) = Refinements.type domain predicate :=
  congrArg (Refinements.typeAt (QuotientCwf.typeRepresentative domain))
    (predicateRepresentative_class predicate)

/-- A refinement guard is evaluated at the actual supplied contextual section. -/
noncomputable def guard {context : QuotientCwf.QContext D} {domain : QuotientCwf.Ty context}
    (predicate : QPredicate (QuotientCwf.ext context domain).as)
    (argument : QuotientCwf.Tm context domain) : QPredicate context.as :=
  predicateSub predicate (selfExtend (QuotientCwf.cwf D) argument)

theorem predicate_at_supplied_class {context : QuotientCwf.QContext D}
    {domain : QuotientCwf.Ty context} (predicate : QPredicate (QuotientCwf.ext context domain).as)
    (argument : QuotientCwf.Tm context domain)
    (actual : Term context.as (QuotientCwf.typeRepresentative domain))
    (same : QTerm.mk actual = argument.val) :
    QPredicate.mk ((predicateRepresentative predicate).reindex (nativeSection actual)) =
      guard predicate argument := by
  change predicateSub (QPredicate.mk (predicateRepresentative predicate))
    (QuotientCwf.project (nativeSection actual)) = _
  rw [predicateRepresentative_class, nativeSection_projects_of_class argument actual same]
  rfl

theorem raw_guard {context : QuotientCwf.QContext D} {domain : QuotientCwf.Ty context}
    (predicate : QPredicate (QuotientCwf.ext context domain).as)
    (argument : QuotientCwf.Tm context domain) (evidence : (guard predicate argument).entails) :
    Holds D (.entails context.as.raw
      ((predicateRepresentative predicate).code.substitute (instantiate (chosenTerm argument).code))) := by
  have selected := evidence
  rw [← predicate_at_supplied_class predicate argument (chosenTerm argument) (chosenTerm_class argument)]
    at selected
  change Holds D (.entails context.as.raw
    ((predicateRepresentative predicate).code.substitute (nativeSection (chosenTerm argument)).substitution))
    at selected
  rw [nativeSection_substitution] at selected
  exact selected

noncomputable def intro {context : QuotientCwf.QContext D} {domain : QuotientCwf.Ty context}
    (predicate : QPredicate (QuotientCwf.ext context domain).as)
    (argument : QuotientCwf.Tm context domain) (evidence : (guard predicate argument).entails) :
    QuotientCwf.Tm context (Refinements.type domain predicate) :=
  ⟨QTerm.mk (Refinements.rawIntro (predicateRepresentative predicate) (chosenTerm argument)
      (raw_guard predicate argument evidence)), typeRepresentative_class predicate⟩

noncomputable def intro_of_top {context : QuotientCwf.QContext D} {domain : QuotientCwf.Ty context}
    (predicate : QPredicate (QuotientCwf.ext context domain).as)
    (argument : QuotientCwf.Tm context domain) (evidence : guard predicate argument = ⊤) :
    QuotientCwf.Tm context (Refinements.type domain predicate) :=
  intro predicate argument ((Logic.entails_iff_eq_top _).mpr evidence)

theorem intro_argument_congruent {context : QuotientCwf.QContext D}
    {domain : QuotientCwf.Ty context} (predicate : QPredicate (QuotientCwf.ext context domain).as)
    {first second : QuotientCwf.Tm context domain} (same : first = second)
    (firstGuard : (guard predicate first).entails) (secondGuard : (guard predicate second).entails) :
    intro predicate first firstGuard = intro predicate second secondGuard := by
  cases same
  rfl

noncomputable def refinementTermRepresentative {context : QuotientCwf.QContext D}
    {domain : QuotientCwf.Ty context} (predicate : QPredicate (QuotientCwf.ext context domain).as)
    (term : QuotientCwf.Tm context (Refinements.type domain predicate)) :
    Term context.as (typeRepresentative predicate) :=
  QuotientCwf.termRepresentative _ term.val
    (term.property.trans (typeRepresentative_class predicate).symm)

theorem refinementTermRepresentative_class {context : QuotientCwf.QContext D}
    {domain : QuotientCwf.Ty context} (predicate : QPredicate (QuotientCwf.ext context domain).as)
    (term : QuotientCwf.Tm context (Refinements.type domain predicate)) :
    QTerm.mk (refinementTermRepresentative predicate term) = term.val :=
  QuotientCwf.termRepresentative_class _ _ _

noncomputable def forget {context : QuotientCwf.QContext D} {domain : QuotientCwf.Ty context}
    (predicate : QPredicate (QuotientCwf.ext context domain).as)
    (term : QuotientCwf.Tm context (Refinements.type domain predicate)) :
    QuotientCwf.Tm context domain :=
  ⟨QTerm.mk (Refinements.rawForget (refinementTermRepresentative predicate term)),
    QuotientCwf.typeRepresentative_class domain⟩

theorem guard_forget {context : QuotientCwf.QContext D} {domain : QuotientCwf.Ty context}
    (predicate : QPredicate (QuotientCwf.ext context domain).as)
    (term : QuotientCwf.Tm context (Refinements.type domain predicate)) :
    (guard predicate (forget predicate term)).entails := by
  rw [← predicate_at_supplied_class predicate (forget predicate term)
    (Refinements.rawForget (refinementTermRepresentative predicate term)) rfl]
  change Holds D (.entails context.as.raw
    ((predicateRepresentative predicate).code.substitute
      (nativeSection (Refinements.rawForget (refinementTermRepresentative predicate term))).substitution))
  rw [nativeSection_substitution]
  exact Refinements.rawGuard (refinementTermRepresentative predicate term)

theorem guard_forget_top {context : QuotientCwf.QContext D} {domain : QuotientCwf.Ty context}
    (predicate : QPredicate (QuotientCwf.ext context domain).as)
    (term : QuotientCwf.Tm context (Refinements.type domain predicate)) :
    guard predicate (forget predicate term) = ⊤ :=
  (Logic.entails_iff_eq_top _).mp (guard_forget predicate term)

theorem beta {context : QuotientCwf.QContext D} {domain : QuotientCwf.Ty context}
    (predicate : QPredicate (QuotientCwf.ext context domain).as)
    (argument : QuotientCwf.Tm context domain) (evidence : (guard predicate argument).entails) :
    forget predicate (intro predicate argument evidence) = argument := by
  apply Subtype.ext
  let introduced := Refinements.rawIntro (predicateRepresentative predicate) (chosenTerm argument)
    (raw_guard predicate argument evidence)
  have supplied := (QTerm.mk_eq_iff _ _).mp
    (refinementTermRepresentative_class predicate (intro predicate argument evidence))
  have forgotten := (QTerm.mk_eq_iff _ _).mpr
    ⟨typeEquality_refl (QuotientCwf.typeRepresentative domain),
      Refinements.rawForget_congruent supplied.2⟩
  have computed : QTerm.mk (Refinements.rawForget introduced) = QTerm.mk (chosenTerm argument) :=
    (QTerm.mk_eq_iff _ _).mpr
      ⟨typeEquality_refl (QuotientCwf.typeRepresentative domain),
        Refinements.rawBeta (predicateRepresentative predicate) (chosenTerm argument)
          (raw_guard predicate argument evidence)⟩
  exact forgotten.trans (computed.trans (chosenTerm_class argument))

theorem eta {context : QuotientCwf.QContext D} {domain : QuotientCwf.Ty context}
    (predicate : QPredicate (QuotientCwf.ext context domain).as)
    (term : QuotientCwf.Tm context (Refinements.type domain predicate)) :
    intro predicate (forget predicate term) (guard_forget predicate term) = term := by
  apply Subtype.ext
  let actual := refinementTermRepresentative predicate term
  have supplied := chosenTerm_represents (forget predicate term) (Refinements.rawForget actual) rfl
  have introduced := (QTerm.mk_eq_iff _ _).mpr
    ⟨typeEquality_refl (typeRepresentative predicate),
      Refinements.rawIntro_congruent (predicateRepresentative predicate) supplied
        (raw_guard predicate (forget predicate term) (guard_forget predicate term))
        (Refinements.rawGuard actual)⟩
  have computed : QTerm.mk
      (Refinements.rawIntro (predicateRepresentative predicate) (Refinements.rawForget actual)
        (Refinements.rawGuard actual)) = QTerm.mk actual :=
    (QTerm.mk_eq_iff _ _).mpr
      ⟨typeEquality_refl (typeRepresentative predicate), Refinements.rawEta actual⟩
  exact introduced.trans (computed.trans (refinementTermRepresentative_class predicate term))

/-- Refinement inhabitants are determined by their retained underlying
inhabitant; this follows from the actual generated eta equation. -/
theorem forget_injective {context : QuotientCwf.QContext D} {domain : QuotientCwf.Ty context}
    (predicate : QPredicate (QuotientCwf.ext context domain).as) :
    Function.Injective (forget predicate) := by
  intro first second same
  have reconstructed : intro predicate (forget predicate first) (guard_forget predicate first) =
      intro predicate (forget predicate second) (guard_forget predicate second) :=
    intro_argument_congruent predicate same _ _
  exact (eta predicate first).symm.trans (reconstructed.trans (eta predicate second))

end Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.Contextual.RefinementValues
