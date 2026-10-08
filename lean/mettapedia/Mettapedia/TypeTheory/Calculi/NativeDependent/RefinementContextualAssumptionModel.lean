import Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementContextualDoctrine

/-!
# Guarded assumptions in the generated dependent model

An assumed context retains its chosen raw predicate presentation. Selection
uses the supplied substitution and an actual derivation of its pulled guard.
The monic inclusion and its consequence law are earned from the mixed
generated context category and predicate order.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.Contextual.AssumptionModel

open _root_.CategoryTheory
open Mettapedia.TypeTheory.ContextualPredicateCapabilities

universe u
variable {S : Symbols.{u}} {D : Signature S}

noncomputable def chosen {context : Context D} (predicate : QPredicate context) : PredicateOver context :=
  Quotient.out predicate

theorem chosen_class {context : Context D} (predicate : QPredicate context) :
    QPredicate.mk (chosen predicate) = predicate := Quotient.out_eq predicate

noncomputable def selected (context : QuotientCwf.QContext D) (predicate : QPredicate context.as) :
    QuotientCwf.QContext D := (quotientProjection D).obj (assumed context.as (chosen predicate))

noncomputable def inclusion {context : QuotientCwf.QContext D} (predicate : QPredicate context.as) :
    selected context predicate ⟶ context := QuotientCwf.project (assumptionInclusion context.as (chosen predicate))

theorem chosen_reindex {source target : QuotientCwf.QContext D} (predicate : QPredicate target.as)
    (morphism : source ⟶ target) :
    QPredicate.mk ((chosen predicate).reindex (QuotientCwf.representative morphism)) =
      PredicateAction.reindex morphism predicate := by
  exact (congrArg (fun value => value.reindex (QuotientCwf.representative morphism))
    (chosen_class predicate)).trans (Quantifiers.reindex_representative morphism predicate).symm

theorem raw_guard {source target : QuotientCwf.QContext D} (predicate : QPredicate target.as)
    (morphism : source ⟶ target) (guard : PredicateAction.reindex morphism predicate = ⊤) :
    Holds D (.entails source.as.raw
      ((chosen predicate).code.substitute (QuotientCwf.representative morphism).substitution)) := by
  have evidence := (Logic.entails_iff_eq_top _).mpr guard
  have represented : (QPredicate.mk ((chosen predicate).reindex
      (QuotientCwf.representative morphism))).entails := (chosen_reindex predicate morphism).symm ▸ evidence
  exact represented

noncomputable def lift {source target : QuotientCwf.QContext D} (predicate : QPredicate target.as)
    (morphism : source ⟶ target) (guard : PredicateAction.reindex morphism predicate = ⊤) :
    source ⟶ selected target predicate :=
  QuotientCwf.project (select (chosen predicate) (QuotientCwf.representative morphism)
    (raw_guard predicate morphism guard))

theorem lift_beta {source target : QuotientCwf.QContext D} (predicate : QPredicate target.as)
    (morphism : source ⟶ target) (guard : PredicateAction.reindex morphism predicate = ⊤) :
    lift predicate morphism guard ≫ inclusion predicate = morphism := by
  let rawSelected := select (chosen predicate) (QuotientCwf.representative morphism)
    (raw_guard predicate morphism guard)
  have combined := ((quotientProjection D).map_comp rawSelected
    (assumptionInclusion target.as (chosen predicate))).symm
  have beta := congrArg (fun arrow : source.as ⟶ target.as => QuotientCwf.project arrow)
    (select_inclusion (chosen predicate) (QuotientCwf.representative morphism)
      (raw_guard predicate morphism guard))
  exact combined.trans (beta.trans (QuotientCwf.project_representative morphism))

theorem inclusion_monic {source target : QuotientCwf.QContext D} (predicate : QPredicate target.as)
    (first second : source ⟶ selected target predicate)
    (same : first ≫ inclusion predicate = second ≫ inclusion predicate) : first = second :=
  (cancel_mono ((quotientProjection D).map (assumptionInclusion target.as (chosen predicate)))).mp same

theorem consequence {context : QuotientCwf.QContext D} (assumption consequent : QPredicate context.as) :
    PredicateAction.reindex (inclusion assumption) consequent = ⊤ ↔ assumption ≤ consequent := by
  refine _root_.Quotient.inductionOn consequent fun formed => ?_
  calc
    _ ↔ Logic.RawOrder (chosen assumption) formed := by
      rw [← Logic.entails_iff_eq_top]
      change Holds D (.entails (assumed context.as (chosen assumption)).raw
        (formed.code.substitute TermExpr.var)) ↔ _
      rw [PropExpr.substitute_identity]
    _ ↔ QPredicate.mk (chosen assumption) ≤ QPredicate.mk formed := Iff.rfl
    _ ↔ assumption ≤ QPredicate.mk formed := by rw [chosen_class]

noncomputable def operations (D : Signature S) : AssumptionOperations (predicateDoctrine D) where
  assumed := selected
  inclusion := inclusion
  select := lift
  select_beta := lift_beta
  inclusion_monic := inclusion_monic
  consequence := consequence

end Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.Contextual.AssumptionModel
