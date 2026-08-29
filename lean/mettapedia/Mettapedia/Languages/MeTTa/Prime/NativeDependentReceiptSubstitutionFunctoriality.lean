import Mettapedia.Languages.MeTTa.Prime.NativeDependentReceiptGeneratorSubstitutionAction

/-!
# Complete functoriality of dependent receipt-cell substitution

The retained Prime root and an authored comparison-generator family each
carry substitution laws.  This module lifts those two independent laws
through the complete free whiskered-cell syntax.  Consequently, successive
strict substitutions agree heterogeneously with the direct substitution by
their syntactic composite, including every conversion receipt, authored
generator, vertical node, and whiskering node.

The result is deliberately conditional on the generator action's
functoriality.  Merely providing a local generator map for every substitution
does not justify direct fusion; the arity-stamping countermodel from the
generator-action layer remains the refusing witness.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.Prime
namespace NativeDependentReceiptSubstitutionFunctoriality

open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.FreeWhiskeredCell
open Mettapedia.TypeTheory.JudgmentalEquality
open Mettapedia.Languages.MeTTa.Prime.NativeDependentReceiptComputad
open Mettapedia.Languages.MeTTa.Prime.NativeDependentReceiptCoherenceCandidates.Canaries
open Mettapedia.Languages.MeTTa.Prime.NativeDependentReceiptSubstitutionTransport
open Mettapedia.Languages.MeTTa.Prime.NativeDependentReceiptSubstitutionTransport.Canaries
open Mettapedia.Languages.MeTTa.Prime.NativeDependentReceiptGeneratorSubstitutionAction
open Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.Presentation
open Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.Presentation.Declaration
open Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.Presentation.ProofRelevantStructuralComputation

universe uEvidence uGenerator

/-! ## Heterogeneous congruence for the free-cell constructors -/

private theorem refl_heq
    {base : Base}
    {Generator : {source target : base.Object} →
      base.Hom source target → base.Hom source target → Type uGenerator}
    {source target source' target' : base.Object}
    {path : base.Hom source target} {path' : base.Hom source' target'}
    (sourceEquality : source = source') (targetEquality : target = target')
    (pathEquality : HEq path path') :
    HEq (Cell.refl (Generator := Generator) path)
      (Cell.refl (Generator := Generator) path') := by
  cases sourceEquality
  cases targetEquality
  cases eq_of_heq pathEquality
  rfl

private theorem generator_heq
    {base : Base}
    {Generator : {source target : base.Object} →
      base.Hom source target → base.Hom source target → Type uGenerator}
    {source target source' target' : base.Object}
    {first second : base.Hom source target}
    {first' second' : base.Hom source' target'}
    {evidence : Generator first second}
    {evidence' : Generator first' second'}
    (sourceEquality : source = source') (targetEquality : target = target')
    (firstEquality : HEq first first') (secondEquality : HEq second second')
    (evidenceEquality : HEq evidence evidence') :
    HEq (Cell.generator evidence) (Cell.generator evidence') := by
  cases sourceEquality
  cases targetEquality
  cases eq_of_heq firstEquality
  cases eq_of_heq secondEquality
  cases eq_of_heq evidenceEquality
  rfl

private theorem vertical_heq
    {base : Base}
    {Generator : {source target : base.Object} →
      base.Hom source target → base.Hom source target → Type uGenerator}
    {source target source' target' : base.Object}
    {first middle last : base.Hom source target}
    {first' middle' last' : base.Hom source' target'}
    {earlier : Cell base Generator first middle}
    {later : Cell base Generator middle last}
    {earlier' : Cell base Generator first' middle'}
    {later' : Cell base Generator middle' last'}
    (sourceEquality : source = source') (targetEquality : target = target')
    (firstEquality : HEq first first') (middleEquality : HEq middle middle')
    (lastEquality : HEq last last')
    (earlierEquality : HEq earlier earlier')
    (laterEquality : HEq later later') :
    HEq (Cell.vertical earlier later) (Cell.vertical earlier' later') := by
  cases sourceEquality
  cases targetEquality
  cases eq_of_heq firstEquality
  cases eq_of_heq middleEquality
  cases eq_of_heq lastEquality
  cases eq_of_heq earlierEquality
  cases eq_of_heq laterEquality
  rfl

private theorem whiskerLeft_heq
    {base : Base}
    {Generator : {source target : base.Object} →
      base.Hom source target → base.Hom source target → Type uGenerator}
    {source middle target source' middle' target' : base.Object}
    {prior : base.Hom source middle}
    {prior' : base.Hom source' middle'}
    {first second : base.Hom middle target}
    {first' second' : base.Hom middle' target'}
    {cell : Cell base Generator first second}
    {cell' : Cell base Generator first' second'}
    (sourceEquality : source = source') (middleEquality : middle = middle')
    (targetEquality : target = target')
    (priorEquality : HEq prior prior')
    (firstEquality : HEq first first') (secondEquality : HEq second second')
    (cellEquality : HEq cell cell') :
    HEq (Cell.whiskerLeft prior cell) (Cell.whiskerLeft prior' cell') := by
  cases sourceEquality
  cases middleEquality
  cases targetEquality
  cases eq_of_heq priorEquality
  cases eq_of_heq firstEquality
  cases eq_of_heq secondEquality
  cases eq_of_heq cellEquality
  rfl

private theorem whiskerRight_heq
    {base : Base}
    {Generator : {source target : base.Object} →
      base.Hom source target → base.Hom source target → Type uGenerator}
    {source middle target source' middle' target' : base.Object}
    {suffix : base.Hom middle target}
    {suffix' : base.Hom middle' target'}
    {first second : base.Hom source middle}
    {first' second' : base.Hom source' middle'}
    {cell : Cell base Generator first second}
    {cell' : Cell base Generator first' second'}
    (sourceEquality : source = source') (middleEquality : middle = middle')
    (targetEquality : target = target')
    (suffixEquality : HEq suffix suffix')
    (firstEquality : HEq first first') (secondEquality : HEq second second')
    (cellEquality : HEq cell cell') :
    HEq (Cell.whiskerRight suffix cell) (Cell.whiskerRight suffix' cell') := by
  cases sourceEquality
  cases middleEquality
  cases targetEquality
  cases eq_of_heq suffixEquality
  cases eq_of_heq firstEquality
  cases eq_of_heq secondEquality
  cases eq_of_heq cellEquality
  rfl

/-- Endpoint casts contain no additional proof-relevant cell data. -/
private theorem cast_forget_heq
    {base : Base}
    {Generator : {source target : base.Object} →
      base.Hom source target → base.Hom source target → Type uGenerator}
    {source target : base.Object}
    {first second first' second' : base.Hom source target}
    (firstEquality : first = first') (secondEquality : second = second')
    (cell : Cell base Generator first second) :
    HEq (Cell.cast firstEquality secondEquality cell) cell := by
  cases firstEquality
  cases secondEquality
  rfl

/-! ## Direct substitution agrees with successive substitution -/

/-- For the canonical retained lift of an authored rule presentation,
successive substitution of a complete generated receipt cell agrees with the
direct action of the composite substitution.  `HEq` records the propositional
substitution laws at every dependent endpoint rather than erasing them. -/
theorem substituteCell_ofRules_comp_heq
    {Head : Type} (rules : Rules Head)
    {headEq : Head → Head → Prop}
    {Generator : ReceiptGeneratorFamily Head
      (SyntacticJudgmentalPi.RetainedRoot.ofRules rules).computation headEq}
    (action : SubstitutionMap Generator)
    (functorial : action.Functorial)
    {n m k : Nat} (later : Sub Head m k) (earlier : Sub Head n m)
    {left right : Tm Head n}
    {first second : StructuralConversionReceipt
      (SyntacticJudgmentalPi.RetainedRoot.ofRules rules).computation
      headEq left right}
    (cell : Cell
      (receiptBase
        (SyntacticJudgmentalPi.RetainedRoot.ofRules rules).computation
        headEq n)
      (Generator n) first second) :
    HEq
      (substituteCell later (action.map later)
        (substituteCell earlier (action.map earlier) cell))
      (substituteCell (fun index => subst later (earlier index))
        (action.map (fun index => subst later (earlier index))) cell) := by
  refine HEq.trans
    (heq_of_eq (substituteCell_canonical_comp action later earlier cell)) ?_
  let rec directAgreement
      {source target : Tm Head n}
      {currentFirst currentSecond : StructuralConversionReceipt
        (SyntacticJudgmentalPi.RetainedRoot.ofRules rules).computation
        headEq source target}
      (current : Cell
        (receiptBase
          (SyntacticJudgmentalPi.RetainedRoot.ofRules rules).computation
          headEq n)
        (Generator n) currentFirst currentSecond) :
      HEq
        (mapCell
          (BaseMap.comp (receiptSubstitutionBaseMap earlier)
            (receiptSubstitutionBaseMap later))
          (GeneratorMap.comp (action.map earlier) (action.map later)) current)
        (substituteCell (fun index => subst later (earlier index))
          (action.map (fun index => subst later (earlier index))) current) :=
    match current with
    | .refl path => by
        exact refl_heq (subst_comp later earlier _)
          (subst_comp later earlier _)
          (SyntacticJudgmentalPi.StructuralConversionReceipt.ofRules_substitute_comp_heq
            rules later earlier path)
    | .generator evidence => by
        exact generator_heq (subst_comp later earlier _)
          (subst_comp later earlier _)
          (SyntacticJudgmentalPi.StructuralConversionReceipt.ofRules_substitute_comp_heq
            rules later earlier _)
          (SyntacticJudgmentalPi.StructuralConversionReceipt.ofRules_substitute_comp_heq
            rules later earlier _)
          (functorial.map_comp later earlier evidence)
    | .vertical earlierCell laterCell => by
        exact vertical_heq (subst_comp later earlier _)
          (subst_comp later earlier _)
          (SyntacticJudgmentalPi.StructuralConversionReceipt.ofRules_substitute_comp_heq
            rules later earlier _)
          (SyntacticJudgmentalPi.StructuralConversionReceipt.ofRules_substitute_comp_heq
            rules later earlier _)
          (SyntacticJudgmentalPi.StructuralConversionReceipt.ofRules_substitute_comp_heq
            rules later earlier _)
          (directAgreement earlierCell) (directAgreement laterCell)
    | .whiskerLeft prior nested => by
        simp only [substituteCell, mapCell]
        exact HEq.trans (cast_forget_heq _ _ _)
          (HEq.trans
            (whiskerLeft_heq
              (subst_comp later earlier _)
              (subst_comp later earlier _)
              (subst_comp later earlier _)
              (SyntacticJudgmentalPi.StructuralConversionReceipt.ofRules_substitute_comp_heq
                rules later earlier prior)
              (SyntacticJudgmentalPi.StructuralConversionReceipt.ofRules_substitute_comp_heq
                rules later earlier _)
              (SyntacticJudgmentalPi.StructuralConversionReceipt.ofRules_substitute_comp_heq
                rules later earlier _)
              (directAgreement nested))
            (HEq.symm (cast_forget_heq _ _ _)))
    | .whiskerRight suffix nested => by
        simp only [substituteCell, mapCell]
        exact HEq.trans (cast_forget_heq _ _ _)
          (HEq.trans
            (whiskerRight_heq
              (subst_comp later earlier _)
              (subst_comp later earlier _)
              (subst_comp later earlier _)
              (SyntacticJudgmentalPi.StructuralConversionReceipt.ofRules_substitute_comp_heq
                rules later earlier suffix)
              (SyntacticJudgmentalPi.StructuralConversionReceipt.ofRules_substitute_comp_heq
                rules later earlier _)
              (SyntacticJudgmentalPi.StructuralConversionReceipt.ofRules_substitute_comp_heq
                rules later earlier _)
              (directAgreement nested))
            (HEq.symm (cast_forget_heq _ _ _)))
  exact directAgreement cell

/-! ## Positive and negative controls -/

/-- Reopening an empty context is the unique substitution out of arity zero.
Together with `closeVariable`, it gives a genuine arity-changing round trip. -/
def reopenEmpty : Sub Tower.Head 0 1 := fun index => Fin.elim0 index

abbrev primeTaggedGeneratorFamily :
    ReceiptGeneratorFamily Tower.Head retainedTower.computation
      Tower.rules.headEq :=
  fun n => TaggedGenerator n

def primeTaggedAction : SubstitutionMap primeTaggedGeneratorFamily :=
  Tagged.action

/-- Closing and then reopening the complete whiskered comparison agrees with
one direct substitution.  The direct action replaces the open variable by
the closed universe code, so this is not merely identity transport. -/
theorem whiskeredTaggedCell_roundTrip_direct :
    HEq
      (substituteCell reopenEmpty (primeTaggedAction.map reopenEmpty)
        (substituteCell closeVariable
          (primeTaggedAction.map closeVariable) whiskeredTaggedCell))
      (substituteCell
        (fun index => subst reopenEmpty (closeVariable index))
        (primeTaggedAction.map
          (fun index => subst reopenEmpty (closeVariable index)))
        whiskeredTaggedCell) :=
  substituteCell_ofRules_comp_heq Tower.rules primeTaggedAction
    Tagged.actionFunctorial reopenEmpty closeVariable whiskeredTaggedCell

/-- The complete-cell fusion license has both a concrete inhabitant and an
independent refusal: local arity-stamping generator maps do not compose. -/
theorem completeSubstitutionFusionBoundary :
    (HEq
      (substituteCell reopenEmpty (primeTaggedAction.map reopenEmpty)
        (substituteCell closeVariable
          (primeTaggedAction.map closeVariable) whiskeredTaggedCell))
      (substituteCell
        (fun index => subst reopenEmpty (closeVariable index))
        (primeTaggedAction.map
          (fun index => subst reopenEmpty (closeVariable index)))
        whiskeredTaggedCell)) ∧
      ¬ StampCanary.action.Functorial :=
  ⟨whiskeredTaggedCell_roundTrip_direct,
    StampCanary.action_not_functorial⟩

/-! ## Axiom audit -/

#print axioms substituteCell_ofRules_comp_heq
#print axioms whiskeredTaggedCell_roundTrip_direct
#print axioms completeSubstitutionFusionBoundary

end NativeDependentReceiptSubstitutionFunctoriality
end Mettapedia.Languages.MeTTa.Prime
