import Mettapedia.Languages.HOLLight.ImplicationIntroduction

/-!
# Implication introduction over a retained theorem

The producer references its input proof as one external root. It checks the
Boolean sorts and the auxiliary binder's freshness before constructing the
existing primitive DISCH expansion. The result removes only the discharged
premise and retains all axiom provenance.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.HOLLight.CachedImplicationIntroduction
open Mettapedia.Languages.OpenTheory GraphExpansion ImplicationIntroduction

structure Prepared where
  result : Theorem
  certificate : ProofSystem.Certificate

private theorem absentPremise (premise : CanonicalTerm) (input : Theorem) (binder : SourceVar)
    (fresh : ¬ FreeInHypotheses binder ({premise} ∪ input.sequent.hyp)) :
    ¬ DBTerm.FreeOccurrence binder premise.term := by
  intro occurs
  exact fresh ⟨premise,by simp,occurs⟩

private theorem absentConclusion (input : Theorem) (binder : SourceVar)
    (absent : DBTerm.hasFree binder input.sequent.concl.term = false) :
    ¬ DBTerm.FreeOccurrence binder input.sequent.concl.term := by
  intro occurs
  have present := (DBTerm.hasFree_eq_true_iff _ _).mpr occurs
  rw [absent] at present
  contradiction

def prepare? (policy : AxiomPolicy) [DecidablePred policy]
    (premise : CanonicalTerm) (input : Theorem) (name : Name) (origin : ProofExecution.Origin) : Option Prepared :=
  if premiseBool : premise.isBoolB = true then
    if inputBool : input.sequent.concl.isBoolB = true then
      if fresh : hasFreeInHypothesesB ⟨name,ExcludedMiddle.boolBinaryTy⟩ ({premise} ∪ input.sequent.hyp) = false then
        if absent : DBTerm.hasFree ⟨name,ExcludedMiddle.boolBinaryTy⟩ input.sequent.concl.term = false then do
          let block ← dischBlock? policy premise input
            ((CanonicalTerm.isBoolB_eq_true_iff _).mp premiseBool)
            ((CanonicalTerm.isBoolB_eq_true_iff _).mp inputBool) name
            ((hasFreeInHypothesesB_eq_false_iff _ _).mp fresh)
            (absentPremise premise input _ ((hasFreeInHypothesesB_eq_false_iff _ _).mp fresh))
            (absentConclusion input _ absent) origin
          return ⟨dischResult premise input
            ((CanonicalTerm.isBoolB_eq_true_iff _).mp premiseBool)
            ((CanonicalTerm.isBoolB_eq_true_iff _).mp inputBool),block⟩
        else none
      else none
    else none
  else none

theorem prepare?_spec (policy : AxiomPolicy) [DecidablePred policy]
    (premise : CanonicalTerm) (input : Theorem) (name : Name) (origin : ProofExecution.Origin)
    {prepared : Prepared} (accepted : prepare? policy premise input name origin = some prepared) :
    BlockChecked policy [input] prepared.result prepared.certificate ∧
      prepared.result.sequent.hyp = input.sequent.hyp.erase premise ∧
      prepared.result.axioms = input.axioms ∧
      prepared.result.sequent.concl.term = ExcludedMiddle.impAppDB premise.term input.sequent.concl.term := by
  unfold prepare? at accepted
  split at accepted
  next premiseBool =>
    split at accepted
    next inputBool =>
      split at accepted
      next fresh =>
        split at accepted
        next absent =>
          obtain ⟨block,computed,checked⟩ := dischBlock?_checked policy premise input
            ((CanonicalTerm.isBoolB_eq_true_iff _).mp premiseBool)
            ((CanonicalTerm.isBoolB_eq_true_iff _).mp inputBool) name
            ((hasFreeInHypothesesB_eq_false_iff _ _).mp fresh)
            (absentPremise premise input _ ((hasFreeInHypothesesB_eq_false_iff _ _).mp fresh))
            (absentConclusion input _ absent) origin
          simp only [computed] at accepted
          cases accepted
          exact ⟨checked,rfl,rfl,rfl⟩
        next => simp at accepted
      next => simp at accepted
    next => simp at accepted
  next => simp at accepted

theorem prepare?_checked (policy : AxiomPolicy) [DecidablePred policy]
    (premise : CanonicalTerm) (input : Theorem) (name : Name) (origin : ProofExecution.Origin)
    {prepared : Prepared} (accepted : prepare? policy premise input name origin = some prepared) :
    BlockChecked policy [input] prepared.result prepared.certificate :=
  (prepare?_spec policy premise input name origin accepted).1

theorem prepare?_exists (policy : AxiomPolicy) [DecidablePred policy]
    (premise : CanonicalTerm) (input : Theorem) (name : Name) (origin : ProofExecution.Origin)
    (premiseBool : premise.IsBool) (inputBool : input.sequent.concl.IsBool)
    (fresh : ¬ FreeInHypotheses ⟨name,ExcludedMiddle.boolBinaryTy⟩ ({premise} ∪ input.sequent.hyp))
    (absent : ¬ DBTerm.FreeOccurrence ⟨name,ExcludedMiddle.boolBinaryTy⟩ input.sequent.concl.term) :
    ∃ prepared, prepare? policy premise input name origin = some prepared := by
  have absentB : DBTerm.hasFree ⟨name,ExcludedMiddle.boolBinaryTy⟩ input.sequent.concl.term = false := by
    apply Bool.eq_false_iff.mpr
    intro present
    exact absent ((DBTerm.hasFree_eq_true_iff _ _).mp present)
  obtain ⟨block,computed,_⟩ := dischBlock?_checked policy premise input premiseBool inputBool name fresh
    (absentPremise premise input _ fresh) absent origin
  refine ⟨⟨dischResult premise input premiseBool inputBool,block⟩,?_⟩
  simp only [prepare?,(CanonicalTerm.isBoolB_eq_true_iff _).mpr premiseBool,
    (CanonicalTerm.isBoolB_eq_true_iff _).mpr inputBool,
    (hasFreeInHypothesesB_eq_false_iff _ _).mpr fresh,absentB,dif_pos,computed]
  rfl

theorem prepare?_refuses_capture (policy : AxiomPolicy) [DecidablePred policy]
    (premise : CanonicalTerm) (input : Theorem) (name : Name) (origin : ProofExecution.Origin)
    (captured : FreeInHypotheses ⟨name,ExcludedMiddle.boolBinaryTy⟩ ({premise} ∪ input.sequent.hyp)) :
    prepare? policy premise input name origin = none := by
  have present := (hasFreeInHypothesesB_eq_true_iff _ _).mpr captured
  unfold prepare?
  split
  · split
    · simp only [present,Bool.true_eq_false,dite_false]
    · rfl
  · rfl

theorem prepare?_refuses_conclusion_capture (policy : AxiomPolicy) [DecidablePred policy]
    (premise : CanonicalTerm) (input : Theorem) (name : Name) (origin : ProofExecution.Origin)
    (captured : DBTerm.FreeOccurrence ⟨name,ExcludedMiddle.boolBinaryTy⟩ input.sequent.concl.term) :
    prepare? policy premise input name origin = none := by
  have present := (DBTerm.hasFree_eq_true_iff _ _).mpr captured
  unfold prepare?
  split
  · split
    · split
      · simp only [present,Bool.true_eq_false,dite_false]
      · rfl
    · rfl
  · rfl

#print axioms prepare?_checked
end Mettapedia.Languages.HOLLight.CachedImplicationIntroduction
