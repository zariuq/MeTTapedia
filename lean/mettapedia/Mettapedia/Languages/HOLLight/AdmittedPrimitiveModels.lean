import Mettapedia.Languages.HOLLight.NaturalModelArithmetic
import Mettapedia.GSLT.LanguageDef.IndexedInductiveHOLRealization
import Mettapedia.Logic.HOL.BooleanFacts

/-!
# Received primitive models for admitted constructor descriptions

The actual source zero/successor and addition equations determine numerical
index evaluation. Bool payloads use the proposition carrier through its two
truth values. Empty payloads keep that ambient carrier with a false guard.
These are semantic interpretations, not executable inverse adapters.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Mettapedia.Languages.HOLLight.AdmittedPrimitiveModels
open Mettapedia.Logic Mettapedia.Languages.OpenTheory
open Mettapedia.GSLT.LanguageDef
open IndexedInductiveHOLRealization ReferenceBooleanSemantics
open SourceProfileModels TypeFamilySemantics
universe w

variable (natural : NaturalModelCategoricity.Signature)
  (addition : HOL.ClosedTerm Symbol (natural.number.arr (natural.number.arr natural.number)))

def arithmetic : IndexedInductiveHOLTerms.Arithmetic Symbol :=
  ⟨natural.number, .prop, natural.zero, natural.successor, addition⟩

structure Operations where
  natural : NaturalModelCategoricity.Signature
  addition : HOL.ClosedTerm Symbol (natural.number.arr (natural.number.arr natural.number))

/-- Resolve source declaration identities. Their numerical laws are supplied
only by the separate checked cache readings. -/
def operations? (symbols : ExportCodec.Symbols) : Option Operations := do
  let operator ← List.lookup "num" symbols.operators
  let zero ← List.lookup "_0" symbols.constants
  let numeral ← List.lookup "NUMERAL" symbols.constants
  let successor ← List.lookup "SUC" symbols.constants
  let plus ← List.lookup "+" symbols.constants
  let number : Ty := .op operator []
  let origin : HOL.ClosedTerm Symbol number.toHOL :=
    .app (.const (.constant numeral (Ty.function number number) (Ty.toHOL_function _ _)))
      (.const (.constant zero number rfl))
  return ⟨⟨number.toHOL,origin,
    .const (.constant successor (Ty.function number number) (Ty.toHOL_function _ _))⟩,
    .const (.constant plus (Ty.function number (Ty.function number number))
      (by simp only [Ty.toHOL_function]))⟩

noncomputable def numbers (model : HOL.HenkinModel.{0,0,w+1} AtomicTy Symbol)
    (full : model.FullDomains) (meanings : Meanings model)
    (separation : model.models natural.successorSeparation)
    (injectivity : model.models natural.successorInjective)
    (induction : model.models natural.induction)
    (atZero : model.models (NaturalModelArithmetic.zeroEquation natural addition))
    (atSuccessor : model.models (NaturalModelArithmetic.successorEquation natural addition)) :
    Numbers (arithmetic natural addition) model where
  equivalence := natural.naturalEquivalence model full meanings separation injectivity induction
  zero := by
    change model.denote natural.zero (IndexedInductiveHOLTerms.Arithmetic.emptyValuation model) = _
    rw [natural.denote_zero]
    exact (natural.naturalEquivalence_zero model full meanings separation injectivity induction).symm
  successor n := by
    change model.denote natural.successor (IndexedInductiveHOLTerms.Arithmetic.emptyValuation model) _ = _
    rw [natural.denote_successor]
    exact (natural.naturalEquivalence_succ model full meanings separation injectivity induction n).symm
  addition n m := by
    change model.denote addition (IndexedInductiveHOLTerms.Arithmetic.emptyValuation model) _ _ = _
    rw [NaturalModelArithmetic.denote_add]
    exact NaturalModelArithmetic.add_naturalEquivalence natural addition model full meanings
      separation injectivity induction atZero atSuccessor n m

noncomputable def boolValues (model : HOL.HenkinModel.{0,0,w+1} AtomicTy Symbol) :
    Bool ≃ HOL.Ty.denote.{0,w+1} model.Carrier .prop :=
  ((Equiv.ulift.symm.trans HOL.BooleanFacts.boolPropEquiv).trans Equiv.ulift).trans Equiv.ulift.symm

noncomputable def boolElements (model : HOL.HenkinModel.{0,0,w+1} AtomicTy Symbol) :
    Elements (arithmetic natural addition) model Bool :=
  fullElements (arithmetic natural addition) model Bool (boolValues model)

theorem boolValues_distinguish (model : HOL.HenkinModel.{0,0,w+1} AtomicTy Symbol) :
    boolValues model false ≠ boolValues model true := by
  intro same
  cases (boolValues model).injective same

noncomputable def emptyElements (model : HOL.HenkinModel.{0,0,w+1} AtomicTy Symbol) :
    Elements (arithmetic natural addition) model Empty :=
  IndexedInductiveHOLRealization.emptyElements (arithmetic natural addition) model

structure RootIndices where
  successorSeparation : Nat
  successorInjective : Nat
  naturalInduction : Nat
  additionZero : Nat
  additionSuccessor : Nat

structure Readings (state : ProofExecution.Registered.State) where
  naturalFacts : NaturalModelCategoricity.CachedFacts natural state
  additionFacts : NaturalModelArithmetic.CachedFacts natural addition state

def read? (state : ProofExecution.Registered.State) (indices : RootIndices) :
    Option (Readings natural addition state) := do
  let separation ← ExactFormulaReadback.read? state indices.successorSeparation natural.successorSeparation
  let injectivity ← ExactFormulaReadback.read? state indices.successorInjective natural.successorInjective
  let induction ← ExactFormulaReadback.read? state indices.naturalInduction natural.induction
  let additions ← NaturalModelArithmetic.read? natural addition state indices.additionZero indices.additionSuccessor
  return ⟨⟨separation.fact, injectivity.fact, induction.fact,
    separation.known, injectivity.known, induction.known,
    separation.closed, injectivity.closed, induction.closed,
    separation.translated, injectivity.translated, induction.translated⟩, additions⟩

variable (commands : List ProofExecution.Registered.Command) (after : ProofExecution.Registered.State)
  (accepted : ProofExecution.Registered.replayFrom policy
    (ProofExecution.Registered.empty SourceProfile.primitiveContext) commands = some after)
  (naturalFacts : NaturalModelCategoricity.CachedFacts natural after)
  (additionFacts : NaturalModelArithmetic.CachedFacts natural addition after)
  (other : OperatorFamilies.{w}) (assignment : Assignment.{w})

private theorem cached_model {fact : Theorem} (known : fact ∈ after.cache)
    {formula : HOL.ClosedFormula Symbol}
    (translated : Translates [] fact.sequent.concl.term .prop formula) (closed : fact.sequent.hyp = ∅) :
    ((sourceReplayFrame commands after accepted).frame.model other assignment).models formula := by
  apply (sourceReplayFrame commands after accepted).frame.cached_models_of_translation other assignment known translated
  intro hypothesis member
  simp [closed, translatedHypotheses] at member

/-- Only five exact cached source readings supply the numerical laws. -/
noncomputable def replayNumbers :
    Numbers (arithmetic natural addition) ((sourceReplayFrame commands after accepted).frame.model other assignment) := by
  let frame := (sourceReplayFrame commands after accepted).frame
  have laws := NaturalModelArithmetic.replay_equations natural addition commands after accepted additionFacts other assignment
  exact numbers natural addition (frame.model other assignment) (frame.model_fullDomains other assignment)
    (replay_meanings commands after accepted other assignment)
    (cached_model commands after accepted other assignment naturalFacts.separation_known
      naturalFacts.separation_read naturalFacts.separation_closed)
    (cached_model commands after accepted other assignment naturalFacts.injectivity_known
      naturalFacts.injectivity_read naturalFacts.injectivity_closed)
    (cached_model commands after accepted other assignment naturalFacts.induction_known
      naturalFacts.induction_read naturalFacts.induction_closed) laws.1 laws.2

noncomputable def replayBoolRealization :=
  realization (arithmetic natural addition) ((sourceReplayFrame commands after accepted).frame.model other assignment)
    Bool (replayNumbers natural addition commands after accepted naturalFacts additionFacts other assignment)
    (boolElements natural addition ((sourceReplayFrame commands after accepted).frame.model other assignment))

noncomputable def replayEmptyRealization :=
  realization (arithmetic natural addition) ((sourceReplayFrame commands after accepted).frame.model other assignment)
    Empty (replayNumbers natural addition commands after accepted naturalFacts additionFacts other assignment)
    (emptyElements natural addition ((sourceReplayFrame commands after accepted).frame.model other assignment))

theorem replayBoolImages :
    HOL.IndexedContainerPositionTerms.FieldImages
      (replayBoolRealization natural addition commands after accepted naturalFacts additionFacts other assignment)
      (guards (arithmetic natural addition) ((sourceReplayFrame commands after accepted).frame.model other assignment)
        Bool (boolElements natural addition ((sourceReplayFrame commands after accepted).frame.model other assignment))) :=
  images _ _ _ _ _

theorem replayEmptyImages :
    HOL.IndexedContainerPositionTerms.FieldImages
      (replayEmptyRealization natural addition commands after accepted naturalFacts additionFacts other assignment)
      (guards (arithmetic natural addition) ((sourceReplayFrame commands after accepted).frame.model other assignment)
        Empty (emptyElements natural addition ((sourceReplayFrame commands after accepted).frame.model other assignment))) :=
  images _ _ _ _ _

theorem replayBoolInjections :
    HOL.IndexedContainerPositionTerms.FieldInjective
      (replayBoolRealization natural addition commands after accepted naturalFacts additionFacts other assignment) :=
  injections _ _ _ _ _
    (boolValues ((sourceReplayFrame commands after accepted).frame.model other assignment)).injective

theorem replayEmptyInjections :
    HOL.IndexedContainerPositionTerms.FieldInjective
      (replayEmptyRealization natural addition commands after accepted naturalFacts additionFacts other assignment) := by
  apply injections
  intro impossible
  exact impossible.elim

#print axioms replayNumbers
#print axioms replayBoolRealization
#print axioms replayEmptyImages
end Mettapedia.Languages.HOLLight.AdmittedPrimitiveModels
