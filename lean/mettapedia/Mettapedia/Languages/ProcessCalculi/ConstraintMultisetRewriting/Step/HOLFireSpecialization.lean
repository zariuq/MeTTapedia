import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.HOLLoadedFire
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.EffectCore
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.HOLExactSpecialization

/-! # Loaded occurrence update agrees with the indexed finite-store operation

The equality covers the entire raw occurrence domain, including the invalid
sentinel. Its result therefore supports equality reflection as well as
pointwise membership. Admission remains independent.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.HOLFireSpecialization

open Mettapedia.Logic Mettapedia.Languages.OpenTheory
open Mettapedia.Languages.HOLLight
open HOLOccurrenceCoding
open MeTTaCalculus.OccurrenceCommits (Commit fire mem_fire)

universe w uOcc uR

variable (model : HOL.HenkinModel.{0,0,w+1} AtomicTy Symbol) {O : Type uOcc} [DecidableEq O]
  (code : Coding model O) (full : model.FullDomains)
  (equations : ∀ fact ∈ HOLSemanticDefinitions.received.received.registered.cache, ∀ substitution : TypeSubst,
    ∃ formula : HOL.ClosedFormula Symbol,
      TranslatesCompositionally []
        ((TermSubst.mk substitution []).applyDB fact.sequent.concl.term) .prop formula ∧ model.models formula)

include full equations in
theorem fire_function {R : Type uR} (present : Finset O) (commit : Commit O R) :
    model.constDen HOLLoadedFire.symbol (finiteValue model code present)
      (finiteValue model code commit.taken) (finiteValue model code commit.made) =
      finiteValue model code (fire present commit) := by
  funext value
  refine (HOLLoadedFire.operational_meaning model full equations _ _ _ value).trans ?_
  apply ULift.ext
  apply propext
  cases raw : code value with
  | none => simp only [finiteValue, predicateValue, raw, finitePredicate, not_false_eq_true, and_true, or_self]
  | some occurrence =>
      simp only [finiteValue, predicateValue, raw, finitePredicate]
      exact mem_fire.symm

include full equations in
theorem result_iff {R : Type uR} (present after : Finset O) (commit : Commit O R) :
    model.constDen HOLLoadedFire.symbol (finiteValue model code present)
      (finiteValue model code commit.taken) (finiteValue model code commit.made) = finiteValue model code after ↔
      fire present commit = after := by
  rw [fire_function model code full equations]
  exact (finiteValue_injective model code).eq_iff

universe uO uT uH uS uF

include full equations in
theorem prepared_occurrences {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}
    {X : Frames Tm Hom} {State : Type uS} {Firing : State → Type uF}
    (E : EffectCore X O State Firing) {s : State} (f : Firing s) (p : E.Prepares f) :
    model.constDen HOLLoadedFire.symbol (finiteValue model code (E.present s))
      (finiteValue model code ((E.selection f).commit (T := Unit)).taken)
      (finiteValue model code ((E.selection f).commit (T := Unit)).made) =
      finiteValue model code (E.present (E.preparedResult f p)) := by
  rw [fire_function model code full equations, E.present_preparedResult]

theorem constructed_agreement {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}
    (X : Frames Tm Hom)
    (other : TypeFamilySemantics.OperatorFamilies.{max uO uT uH uOcc})
    (prior : TypeFamilySemantics.Assignment.{max uO uT uH uOcc}) :
    ∃ (actual : HOL.HenkinModel.{0,0,(max uO uT uH uOcc)+1} AtomicTy Symbol)
      (frames : HOLFrameCoding.Coding actual Obj Tm Hom) (occurrences : Coding actual O),
      actual.Carrier = (HOLFrameDomains.initial Obj Tm Hom O other prior).Carrier ∧
      HOLExactSpecialization.Agreement actual X frames ∧
      ∀ (present : Finset O) (commit : Commit O Unit),
        actual.constDen HOLLoadedFire.symbol (finiteValue actual occurrences present)
          (finiteValue actual occurrences commit.taken) (finiteValue actual occurrences commit.made) =
          finiteValue actual occurrences (fire present commit) := by
  obtain ⟨actual, same, actualFull, actualEquations⟩ := HOLFrameDomains.loaded_model_exists Obj Tm Hom O other prior
  let frames := (HOLFrameCoding.initialCoding (Obj := Obj) (Tm := Tm) (Hom := Hom) O other prior).changeModel actual same
  let occurrences := changeModel (initialCoding Obj Tm Hom O other prior) actual same
  exact ⟨actual, frames, occurrences, same,
    HOLExactSpecialization.agreement_of_cache actual X frames actualFull actualEquations,
    fun present commit => fire_function actual occurrences actualFull actualEquations present commit⟩

#print axioms fire_function
#print axioms result_iff
#print axioms prepared_occurrences
#print axioms constructed_agreement

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.HOLFireSpecialization
