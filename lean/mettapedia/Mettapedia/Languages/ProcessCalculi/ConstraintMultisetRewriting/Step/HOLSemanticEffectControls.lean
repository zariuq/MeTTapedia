import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.HOLSemanticEffectSpecialization
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.ProfileControls

/-! # General semantic effects beyond literal transport and admission

One constructed interpretation accepts normalization and a consistent strict
extension, rejects forgetting a necessary equation, and interprets the
prepared effect of a refused candidate without manufacturing permission.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.HOLSemanticEffectControls

open Mettapedia.Logic Mettapedia.Languages.OpenTheory
open Mettapedia.Languages.HOLLight
open AdmissionObservationCover.Controls (frame World)
open EffectStoreControls (duplicated extra)
open ProfileControls
open HOLFrameCoding HOLFramesCoding HOLSemanticEffectSpecialization
open MeTTaCalculus.OccurrenceCommits (Commit)

abbrev Terms (_ : Unit) := World → Bool
abbrev Maps (_ _ : Unit) := World → World
def emptyCommit : Commit Nat Unit := { taken := ∅, kept := ∅, made := ∅, queries := [] }

structure Evidence (actual : HOL.HenkinModel.{0,0,1} AtomicTy Symbol)
    (code : Coding actual Unit Terms Maps) (occurrences : HOLOccurrenceCoding.Coding actual Nat) : Prop where
  agreement : Agreement actual frame code occurrences
  normalization : (preparedValue actual frame code occurrences normalize.effectCore
    (s := duplicated) () normalization_prepared).down
  strictExtension : (preparedValue actual frame code occurrences strict.effectCore
    (s := []) () strict_admitted.1).down
  strictConsistent : (actual.constDen HOLLoadedSolvable.symbol (homValue actual code)
    (equalValue actual frame code) (actionValue actual frame code) (code.objects.symm (some ()))
    (storeValue actual code (a := ()) extra)).down
  strictNotExact : ¬(actual.constDen HOLLoadedExact.symbol (homValue actual code)
    (equalValue actual frame code) (actionValue actual frame code) (compositionValue actual frame code)
    (code.objects.symm (some ())) (code.objects.symm (some ()))
    (code.morphisms.symm (HOLFrameEncoding.encodeHom (Hom := Maps) (a := ()) (b := ()) (frame.id ())))
    (storeValue actual code (a := ()) ([] : EquationStore (Terms ()))) (storeValue actual code (a := ()) extra)).down
  refusedPrepared : (preparedValue actual frame code occurrences denied.effectCore
    (s := duplicated) () refused_but_prepared.1).down
  refused : ¬denied.Admits (s := duplicated) ()
  cannotDrop : ¬(effectValue actual frame code occurrences (a := ()) (m := ()) (b := ()) (frame.id ()) (frame.id ())
    extra extra [] ∅ ∅ emptyCommit).down

theorem constructed_controls (other : TypeFamilySemantics.OperatorFamilies.{0})
    (prior : TypeFamilySemantics.Assignment.{0}) :
    ∃ (actual : HOL.HenkinModel.{0,0,1} AtomicTy Symbol)
      (code : Coding actual Unit Terms Maps) (occurrences : HOLOccurrenceCoding.Coding actual Nat),
      Evidence actual code occurrences := by
  obtain ⟨actual, same, full, equations⟩ := HOLFrameDomains.loaded_model_exists Unit Terms Maps Nat other prior
  let code := (initialCoding (Obj := Unit) (Tm := Terms) (Hom := Maps) Nat other prior).changeModel actual same
  let occurrences := HOLOccurrenceCoding.changeModel (HOLOccurrenceCoding.initialCoding Unit Terms Maps Nat other prior) actual same
  have agreement := agreement_of_cache actual frame code occurrences full equations
  refine ⟨actual, code, occurrences, agreement,
    prepared_effect actual frame code occurrences full equations normalize.effectCore () normalization_prepared,
    prepared_effect actual frame code occurrences full equations strict.effectCore () strict_admitted.1,
    ?_, ?_,
    prepared_effect actual frame code occurrences full equations denied.effectCore () refused_but_prepared.1,
    refused_but_prepared.2, ?_⟩
  · exact (agreement.solvable () extra).mpr EffectStoreControls.tell_result_solvable
  · intro claimed
    have exactness := (agreement.exactKnowledge () () (frame.id ()) [] extra).mp claimed
    apply EffectStoreControls.cannot_forget_constraint
    intro sigma _
    exact exactness () sigma (Frames.models_nil _)
  · intro claimed
    have pullbacks := (agreement.semanticEffect () () () (frame.id ()) (frame.id ())
      extra extra [] ∅ ∅ emptyCommit).mp claimed
    apply EffectStoreControls.cannot_forget_constraint
    intro sigma solves
    exact (Frames.models_congr (X := frame) (a := ()) (b := ())
      (f := frame.comp sigma (frame.id ())) (g := sigma)
      (fun t => (Frames.act_comp_id (X := frame) (a := ()) (b := ()) sigma t).symm) extra).mp
      (pullbacks.2.1 () sigma solves)

#print axioms constructed_controls

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.HOLSemanticEffectControls
