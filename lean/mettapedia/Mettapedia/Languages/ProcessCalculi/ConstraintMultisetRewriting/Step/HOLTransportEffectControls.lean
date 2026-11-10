import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.HOLTransportEffectSpecialization
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.HOLFrameEncodingControls

/-! # Predicate transport does not recover duplicate list entries

A transported equation predicate accepts removing a duplicate. The actual
loaded predicate still implies semantic refinement and optional exactness,
while literal equality of the underlying lists is false.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.HOLTransportEffectControls

open Mettapedia.Logic Mettapedia.Languages.OpenTheory
open Mettapedia.Languages.HOLLight
open Mettapedia.Logic.HOL.IndexedCarrier.Controls (family)
open HOLFrameEncoding.Controls (frame maps)
open HOLFrameCoding HOLFramesCoding HOLTransportEffectSpecialization
open MeTTaCalculus.OccurrenceCommits (Commit fire)

def equation : family true × family true := ((0 : Nat), (1 : Nat))
def information : EquationStore (family true) := [equation, equation]
def next : EquationStore (family true) := [equation]
def emptyCommit : Commit Nat Unit := { taken := ∅, kept := ∅, made := ∅, queries := [] }

theorem lists_differ : next ≠ frame.applyStore (frame.id true) information := by
  rw [Frames.applyStore_id]
  intro same
  have lengths := congrArg List.length same
  cases lengths

theorem constructed_controls (other : TypeFamilySemantics.OperatorFamilies.{0})
    (prior : TypeFamilySemantics.Assignment.{0}) :
    ∃ (actual : HOL.HenkinModel.{0,0,1} AtomicTy Symbol) (code : Coding actual Bool family maps)
      (occurrences : HOLOccurrenceCoding.Coding actual Nat),
      HOLSemanticEffectSpecialization.Agreement actual frame code occurrences ∧
      (effectValue actual frame code occurrences (a := true) (m := true) (b := true)
        (frame.id true) (frame.id true) [] information next ∅ ∅ emptyCommit).down ∧
      (HOLSemanticEffectSpecialization.effectValue actual frame code occurrences (a := true) (m := true) (b := true)
        (frame.id true) (frame.id true) [] information next ∅ ∅ emptyCommit).down ∧
      (actual.constDen HOLLoadedExact.symbol (homValue actual code) (equalValue actual frame code)
        (actionValue actual frame code) (compositionValue actual frame code)
        (code.objects.symm (some true)) (code.objects.symm (some true))
        (code.morphisms.symm (HOLFrameEncoding.encodeHom (frame.id true)))
        (storeValue actual code information) (storeValue actual code next)).down ∧
      next ≠ frame.applyStore (frame.id true) information := by
  obtain ⟨actual, same, full, equations⟩ := HOLFrameDomains.loaded_model_exists Bool family maps Nat other prior
  let code := (initialCoding (Obj := Bool) (Tm := family) (Hom := maps) Nat other prior).changeModel actual same
  let occurrences := HOLOccurrenceCoding.changeModel (HOLOccurrenceCoding.initialCoding Bool family maps Nat other prior) actual same
  have transported : (effectValue actual frame code occurrences (a := true) (m := true) (b := true)
      (frame.id true) (frame.id true) [] information next ∅ ∅ emptyCommit).down := by
    apply (transport_iff actual frame code occurrences full equations (frame.id true) (frame.id true)
      [] information next ∅ ∅ emptyCommit).mpr
    refine ⟨by simp, ?_, ?_⟩
    · intro pair
      rw [Frames.applyStore_id]
      simp only [next, information, List.mem_cons, List.not_mem_nil, or_false, or_self]
    · simp only [fire, emptyCommit, Finset.sdiff_empty, Finset.union_empty]
  exact ⟨actual, code, occurrences,
    HOLSemanticEffectSpecialization.agreement_of_cache actual frame code occurrences full equations,
    transported,
    implies_semantic actual frame code occurrences full equations _ _ _ _ _ _ _ _ transported,
    implies_exact actual frame code occurrences full equations _ _ _ _ _ _ _ _ transported,
    lists_differ⟩

#print axioms lists_differ
#print axioms constructed_controls

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.HOLTransportEffectControls
