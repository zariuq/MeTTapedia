import Mettapedia.GSLT.LanguageDef.TptpFofNnfLanguageDef

/-!
# Alpha-explicit TPTP view of canonical first-order NNF

The semantic clausification pipeline uses the canonical binder-resolved NNF
carrier, whose bound variables are de Bruijn indices.  TPTP interchange has a
different presentation requirement: quantified variables need globally
distinguishable printable identities.  This module adds those identities as
an evidence-bearing view instead of replacing the canonical representation.

Every quantifier receives one deterministic preorder `BinderId`.  Bound term
occurrences retain their canonical indices; a serializer can recover their
printable identity from the surrounding binder-ID environment.  Erasing the
extra labels returns exactly the source NNF, so the view cannot change a
formula's binding structure or semantics.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.TptpFofAlphaExplicitNnf

open LO FirstOrder
open Mettapedia.GSLT.LanguageDef.TptpFofNormalizationSemantics

abbrev NnfFormula (depth : Nat) :=
  LO.FirstOrder.Semiformula
    TptpFofNormalizationSemantics.language Empty depth

abbrev BinderId := Nat

/-- Canonical NNF plus a stable printable identity at every quantifier. -/
inductive Formula : Nat -> Type
  | verum {depth : Nat} : Formula depth
  | falsum {depth : Nat} : Formula depth
  | rel {depth arity : Nat} :
      RelationSymbol arity -> (Fin arity -> Term depth) -> Formula depth
  | nrel {depth arity : Nat} :
      RelationSymbol arity -> (Fin arity -> Term depth) -> Formula depth
  | and {depth : Nat} : Formula depth -> Formula depth -> Formula depth
  | or {depth : Nat} : Formula depth -> Formula depth -> Formula depth
  | all {depth : Nat} : BinderId -> Formula (depth + 1) -> Formula depth
  | ex {depth : Nat} : BinderId -> Formula (depth + 1) -> Formula depth

/-- Forget only the presentation labels.  Binding remains represented by the
same de Bruijn indices in the same terms. -/
def erase {depth : Nat} : Formula depth -> NnfFormula depth
  | .verum => .verum
  | .falsum => .falsum
  | .rel relation arguments => .rel relation arguments
  | .nrel relation arguments => .nrel relation arguments
  | .and left right => .and (erase left) (erase right)
  | .or left right => .or (erase left) (erase right)
  | .all _ body => .all (erase body)
  | .ex _ body => .ex (erase body)

/-- Number of quantifier sites in the canonical source formula. -/
def quantifierCount {depth : Nat} : NnfFormula depth -> Nat
  | .verum | .falsum | .rel _ _ | .nrel _ _ => 0
  | .and left right | .or left right =>
      quantifierCount left + quantifierCount right
  | .all body | .ex body => quantifierCount body + 1

/-- Binder identities in preorder. -/
def binderIds {depth : Nat} : Formula depth -> List BinderId
  | .verum | .falsum | .rel _ _ | .nrel _ _ => []
  | .and left right | .or left right => binderIds left ++ binderIds right
  | .all binder body | .ex binder body => binder :: binderIds body

/-- Add binder identities starting at `next`, threading the fresh frontier
through the complete formula rather than restarting it under each branch. -/
def labelFrom {depth : Nat} (source : NnfFormula depth) (next : Nat) :
    Formula depth × Nat :=
  match source with
  | .verum => (.verum, next)
  | .falsum => (.falsum, next)
  | .rel relation arguments => (.rel relation arguments, next)
  | .nrel relation arguments => (.nrel relation arguments, next)
  | .and left right =>
      let leftResult := labelFrom left next
      let rightResult := labelFrom right leftResult.2
      (.and leftResult.1 rightResult.1, rightResult.2)
  | .or left right =>
      let leftResult := labelFrom left next
      let rightResult := labelFrom right leftResult.2
      (.or leftResult.1 rightResult.1, rightResult.2)
  | .all body =>
      let bodyResult := labelFrom body (next + 1)
      (.all next bodyResult.1, bodyResult.2)
  | .ex body =>
      let bodyResult := labelFrom body (next + 1)
      (.ex next bodyResult.1, bodyResult.2)
termination_by sizeOf source

def label {depth : Nat} (source : NnfFormula depth) : Formula depth :=
  (labelFrom source 0).1

theorem labelFrom_erase_exact {depth : Nat} (source : NnfFormula depth)
    (next : Nat) :
    erase (labelFrom source next).1 = source := by
  induction source generalizing next with
  | verum => simp [labelFrom, erase]
  | falsum => simp [labelFrom, erase]
  | rel relation arguments => simp [labelFrom, erase]
  | nrel relation arguments => simp [labelFrom, erase]
  | and left right leftHypothesis rightHypothesis =>
      simp [labelFrom, erase, leftHypothesis, rightHypothesis]
  | or left right leftHypothesis rightHypothesis =>
      simp [labelFrom, erase, leftHypothesis, rightHypothesis]
  | all body inductionHypothesis =>
      simp [labelFrom, erase, inductionHypothesis]
  | ex body inductionHypothesis =>
      simp [labelFrom, erase, inductionHypothesis]

theorem labelFrom_next_exact {depth : Nat} (source : NnfFormula depth)
    (next : Nat) :
    (labelFrom source next).2 = next + quantifierCount source := by
  induction source generalizing next with
  | verum => simp [labelFrom, quantifierCount]
  | falsum => simp [labelFrom, quantifierCount]
  | rel relation arguments => simp [labelFrom, quantifierCount]
  | nrel relation arguments => simp [labelFrom, quantifierCount]
  | and left right leftHypothesis rightHypothesis =>
      simp only [labelFrom]
      rw [rightHypothesis, leftHypothesis]
      simp only [quantifierCount]
      omega
  | or left right leftHypothesis rightHypothesis =>
      simp only [labelFrom]
      rw [rightHypothesis, leftHypothesis]
      simp only [quantifierCount]
      omega
  | all body inductionHypothesis =>
      simp only [labelFrom]
      rw [inductionHypothesis]
      simp only [quantifierCount]
      omega
  | ex body inductionHypothesis =>
      simp only [labelFrom]
      rw [inductionHypothesis]
      simp only [quantifierCount]
      omega

theorem labelFrom_binderIds_exact {depth : Nat} (source : NnfFormula depth)
    (next : Nat) :
    binderIds (labelFrom source next).1 =
      List.range' next (quantifierCount source) := by
  induction source generalizing next with
  | verum => simp [labelFrom, binderIds, quantifierCount]
  | falsum => simp [labelFrom, binderIds, quantifierCount]
  | rel relation arguments => simp [labelFrom, binderIds, quantifierCount]
  | nrel relation arguments => simp [labelFrom, binderIds, quantifierCount]
  | and left right leftHypothesis rightHypothesis =>
      simp only [labelFrom, binderIds]
      rw [leftHypothesis]
      rw [rightHypothesis]
      rw [labelFrom_next_exact]
      change List.range' next (quantifierCount left) ++
          List.range' (next + quantifierCount left) (quantifierCount right) =
        List.range' next (quantifierCount left + quantifierCount right)
      have startExact : next + 1 * quantifierCount left =
          next + quantifierCount left := by
        omega
      rw [← startExact]
      exact (List.range'_append (s := next)
          (m := quantifierCount left) (n := quantifierCount right)
          (step := 1))
  | or left right leftHypothesis rightHypothesis =>
      simp only [labelFrom, binderIds]
      rw [leftHypothesis]
      rw [rightHypothesis]
      rw [labelFrom_next_exact]
      change List.range' next (quantifierCount left) ++
          List.range' (next + quantifierCount left) (quantifierCount right) =
        List.range' next (quantifierCount left + quantifierCount right)
      have startExact : next + 1 * quantifierCount left =
          next + quantifierCount left := by
        omega
      rw [← startExact]
      exact (List.range'_append (s := next)
          (m := quantifierCount left) (n := quantifierCount right)
          (step := 1))
  | all body inductionHypothesis =>
      simp [labelFrom, binderIds, quantifierCount, inductionHypothesis,
        List.range'_succ]
  | ex body inductionHypothesis =>
      simp [labelFrom, binderIds, quantifierCount, inductionHypothesis,
        List.range'_succ]

theorem label_erase_exact {depth : Nat} (source : NnfFormula depth) :
    erase (label source) = source := by
  exact labelFrom_erase_exact source 0

theorem label_binderIds_exact {depth : Nat} (source : NnfFormula depth) :
    binderIds (label source) = List.range (quantifierCount source) := by
  simpa [label, List.range_eq_range'] using labelFrom_binderIds_exact source 0

theorem label_binderIds_nodup {depth : Nat} (source : NnfFormula depth) :
    (binderIds (label source)).Nodup := by
  rw [label_binderIds_exact]
  exact List.nodup_range

/-- The alpha-explicit view has exactly the source semantics because erasure
is exact; no semantic reinterpretation is introduced by printable names. -/
theorem label_semantics_exact {Domain : Type}
    (model : TptpFofNormalizationSemantics.Model Domain)
    {depth : Nat} (environment : Fin depth -> Domain)
    (source : NnfFormula depth) :
    LO.FirstOrder.Semiformula.EvalAux model.interpretation Empty.elim
        environment (erase (label source)) <->
      LO.FirstOrder.Semiformula.EvalAux model.interpretation Empty.elim
        environment source := by
  rw [label_erase_exact]

namespace Canary

def nestedSource : NnfFormula 0 :=
  .all <| .and
    (.rel RelationSymbol.equality ![.bvar 0, .bvar 0])
    (.ex (.nrel RelationSymbol.equality ![.bvar 0, .bvar 0]))

theorem nested_labels_are_exact :
    binderIds (label nestedSource) = [0, 1] := by
  decide +kernel

theorem nested_erasure_is_exact : erase (label nestedSource) = nestedSource := by
  exact label_erase_exact nestedSource

/-- This is syntactically representable as an alpha-explicit object, but it
is rejected by the freshness invariant and cannot be produced by `label`. -/
def duplicateLabels : Formula 0 :=
  .all 0 (.ex 0 .verum)

theorem duplicate_labels_are_not_unique :
    ¬ (binderIds duplicateLabels).Nodup := by
  decide +kernel

theorem duplicate_labels_are_not_in_canonical_image :
    ∀ source : NnfFormula 0, label source ≠ duplicateLabels := by
  intro source equality
  have unique := label_binderIds_nodup source
  rw [equality] at unique
  exact duplicate_labels_are_not_unique unique

end Canary

#print axioms labelFrom_erase_exact
#print axioms labelFrom_next_exact
#print axioms labelFrom_binderIds_exact
#print axioms label_erase_exact
#print axioms label_binderIds_exact
#print axioms label_binderIds_nodup
#print axioms label_semantics_exact
#print axioms Canary.nested_labels_are_exact
#print axioms Canary.nested_erasure_is_exact
#print axioms Canary.duplicate_labels_are_not_unique
#print axioms Canary.duplicate_labels_are_not_in_canonical_image

end Mettapedia.GSLT.LanguageDef.TptpFofAlphaExplicitNnf
