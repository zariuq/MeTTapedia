import Mettapedia.GSLT.Core.IndexedOperational
import Mettapedia.GSLT.Core.LooseRelationEquipment

/-!
# Proof-relevant step evidence for GSLTs

A semantic `GSLT` records one-step reduction as a proposition.  This is the
right extensional boundary, but it cannot by itself retain two distinct rule
occurrences, proof labels, substitution witnesses, or saved-proof cells that
induce the same source and target terms.

`StepEvidence` equips a GSLT with a proof-relevant loose relation whose
inhabited fibres are exactly the semantic steps.  `Translation` then gives the
two-sided operational arrow needed by source-to-target compilers: it maps
authored evidence forward and lifts every target event leaving an image state
back to source evidence.  `ExactTranslation` additionally preserves each
fixed-endpoint evidence fibre up to equivalence.

The definitions reuse the existing loose-relation and covered-translation
theory.  They add only the bridge between those two established layers.
-/

namespace Mettapedia.GSLT.ProofRelevant

open Mettapedia.GSLT
open Mettapedia.GSLT.IndexedOperational
open Mettapedia.GSLT.LooseRelationEquipment

universe u

/-- An authored, proof-relevant evidence family for every one-step reduction in a
semantic GSLT.  `erases_iff` prevents both missing authored events and events
that invent a semantic step. -/
structure StepEvidence (theory : GSLT.{u}) where
  Evidence : Loose theory.Term theory.Term
  erases_iff : forall source target,
    Nonempty (Evidence source target) ↔ theory.Step source target

namespace StepEvidence

variable {theory : GSLT.{u}}

/-- Erase one authored event to the proposition-valued GSLT step. -/
theorem erase (steps : StepEvidence theory)
    {source target : theory.Term}
    (evidence : steps.Evidence source target) :
    theory.Step source target :=
  (steps.erases_iff source target).mp ⟨evidence⟩

/-- Every semantic GSLT step has at least one authored event witness. -/
theorem witness (steps : StepEvidence theory)
    {source target : theory.Term} (step : theory.Step source target) :
    Nonempty (steps.Evidence source target) :=
  (steps.erases_iff source target).mpr step

end StepEvidence

/-- A GSLT bundled with proof-relevant evidence for its steps. -/
structure ProofRelevantGSLT where
  theory : GSLT.{u}
  steps : StepEvidence theory

namespace ProofRelevantGSLT

/-- A proof-relevant labeled event retains the exact evidence occurrence. -/
structure Event (system : ProofRelevantGSLT.{u}) where
  source : system.theory.Term
  target : system.theory.Term
  evidence : system.steps.Evidence source target

/-- Forget occurrence evidence only at the semantic GSLT boundary. -/
def Event.erase {system : ProofRelevantGSLT.{u}}
    (event : system.Event) : system.theory.LabeledStep where
  source := event.source
  target := event.target
  step := system.steps.erase event.evidence

end ProofRelevantGSLT

/-! ## Two-sided proof-relevant translations -/

/-- A source-to-target operational translation that processes step evidence
in both directions.  `liftEvidence` is local to the image: unrelated target
states may have arbitrary behavior, while no event leaving a compiled source
state may be invented by the target. -/
structure Translation (source target : ProofRelevantGSLT.{u}) where
  mapTerm : source.theory.Term → target.theory.Term
  mapEquiv : forall {left right}, source.theory.Equiv left right →
    target.theory.Equiv (mapTerm left) (mapTerm right)
  mapEvidence : forall {sourceTerm sourceTarget},
    source.steps.Evidence sourceTerm sourceTarget →
      target.steps.Evidence (mapTerm sourceTerm) (mapTerm sourceTarget)
  liftEvidence : forall {sourceTerm targetTerm},
    target.steps.Evidence (mapTerm sourceTerm) targetTerm →
      Sigma fun sourceTarget =>
        source.steps.Evidence sourceTerm sourceTarget ×
          EqWitness (mapTerm sourceTarget) targetTerm

namespace Translation

/-- Identity changes neither terms nor proof occurrences. -/
def id (system : ProofRelevantGSLT.{u}) : Translation system system where
  mapTerm := fun term => term
  mapEquiv := fun equivalent => equivalent
  mapEvidence := fun evidence => evidence
  liftEvidence := by
    intro sourceTerm targetTerm evidence
    exact ⟨targetTerm, evidence, ⟨⟨rfl⟩⟩⟩

/-- Proof-relevant translations compose without discarding the intermediate
event or relying on a target scheduler. -/
def comp {first middle last : ProofRelevantGSLT.{u}}
    (earlier : Translation first middle)
    (later : Translation middle last) : Translation first last where
  mapTerm := later.mapTerm ∘ earlier.mapTerm
  mapEquiv := fun equivalent => later.mapEquiv (earlier.mapEquiv equivalent)
  mapEvidence := fun evidence => later.mapEvidence (earlier.mapEvidence evidence)
  liftEvidence := by
    intro sourceTerm targetTerm targetEvidence
    obtain ⟨middleTarget, middleEvidence, middleTarget_eq⟩ :=
      later.liftEvidence targetEvidence
    obtain ⟨sourceTarget, sourceEvidence, sourceTarget_eq⟩ :=
      earlier.liftEvidence middleEvidence
    exact ⟨sourceTarget, sourceEvidence,
      ⟨⟨(congrArg later.mapTerm sourceTarget_eq.down.down).trans
        middleTarget_eq.down.down⟩⟩⟩

/-- Forget occurrence evidence only after deriving the existing locally
covered operational translation. -/
def toCovered {source target : ProofRelevantGSLT.{u}}
    (translation : Translation source target) :
    CoveredTranslation source.theory target.theory where
  mapTerm := translation.mapTerm
  mapEquiv := translation.mapEquiv
  cover :=
    { mapStep := by
        intro sourceTerm sourceTarget step
        obtain ⟨sourceEvidence⟩ := source.steps.witness step
        exact target.steps.erase (translation.mapEvidence sourceEvidence)
      liftStep := by
        intro sourceTerm targetTerm step
        obtain ⟨targetEvidence⟩ := target.steps.witness step
        obtain ⟨sourceTarget, sourceEvidence, target_eq⟩ :=
          translation.liftEvidence targetEvidence
        exact ⟨sourceTarget, source.steps.erase sourceEvidence,
          target_eq.down.down⟩ }

@[simp] theorem comp_mapTerm {first middle last : ProofRelevantGSLT.{u}}
    (earlier : Translation first middle)
    (later : Translation middle last) :
    (earlier.comp later).mapTerm = later.mapTerm ∘ earlier.mapTerm :=
  rfl

end Translation

/-! ## Exact evidence fibres -/

/-- An exact translation retains the full evidence fibre for each pair of
mapped endpoints.  This is stronger than two-sided behavioral hosting: it is
appropriate when proof occurrence or heap identity is a public observation. -/
structure ExactTranslation (source target : ProofRelevantGSLT.{u})
    extends Translation source target where
  evidenceEquiv : forall sourceTerm sourceTarget,
    source.steps.Evidence sourceTerm sourceTarget ≃
      target.steps.Evidence
        (toTranslation.mapTerm sourceTerm)
        (toTranslation.mapTerm sourceTarget)
  evidenceEquiv_agrees : forall sourceTerm sourceTarget
      (evidence : source.steps.Evidence sourceTerm sourceTarget),
    evidenceEquiv sourceTerm sourceTarget evidence =
      toTranslation.mapEvidence evidence

namespace ExactTranslation

/-- Exact identity on a proof-relevant GSLT. -/
def id (system : ProofRelevantGSLT.{u}) : ExactTranslation system system := by
  let underlying := Translation.id system
  refine
    { toTranslation := underlying
      evidenceEquiv := ?_
      evidenceEquiv_agrees := ?_ }
  · intro sourceTerm sourceTarget
    simpa [underlying, Translation.id] using
      (Equiv.refl (system.steps.Evidence sourceTerm sourceTarget))
  · intro sourceTerm sourceTarget evidence
    change (Equiv.refl _ :
        system.steps.Evidence sourceTerm sourceTarget ≃
          system.steps.Evidence sourceTerm sourceTarget) evidence =
      underlying.mapEvidence evidence
    simp [underlying, Translation.id]

/-- Exact proof-fibre translations compose by equivalence composition. -/
def comp {first middle last : ProofRelevantGSLT.{u}}
    (earlier : ExactTranslation first middle)
    (later : ExactTranslation middle last) : ExactTranslation first last where
  toTranslation := earlier.toTranslation.comp later.toTranslation
  evidenceEquiv := by
    intro sourceTerm sourceTarget
    change first.steps.Evidence sourceTerm sourceTarget ≃
      last.steps.Evidence
        (later.toTranslation.mapTerm
          (earlier.toTranslation.mapTerm sourceTerm))
        (later.toTranslation.mapTerm
          (earlier.toTranslation.mapTerm sourceTarget))
    exact (earlier.evidenceEquiv sourceTerm sourceTarget).trans
      (later.evidenceEquiv
        (earlier.toTranslation.mapTerm sourceTerm)
        (earlier.toTranslation.mapTerm sourceTarget))
  evidenceEquiv_agrees := by
    intro sourceTerm sourceTarget evidence
    change
      later.evidenceEquiv
          (earlier.toTranslation.mapTerm sourceTerm)
          (earlier.toTranslation.mapTerm sourceTarget)
          (earlier.evidenceEquiv sourceTerm sourceTarget evidence) =
        later.toTranslation.mapEvidence
          (earlier.toTranslation.mapEvidence evidence)
    rw [earlier.evidenceEquiv_agrees, later.evidenceEquiv_agrees]

end ExactTranslation

/-! ## Positive and negative controls -/

namespace Canary

/-- One state with one extensional self-step.  Different evidence families below
retain different occurrence fibres over this same semantic GSLT. -/
def loopTheory : GSLT where
  Term := Unit
  equations :=
    { r := Eq
      iseqv :=
        { refl := fun _ => rfl
          symm := fun equality => equality.symm
          trans := fun first second => first.trans second } }
  rewrites := fun _ _ => True
  rewrites_resp_left := by
    intro source source' target source_eq _
    subst source_eq
    exact ⟨target, trivial, rfl⟩
  rewrites_resp_right := by
    intros
    trivial

def boolSteps : StepEvidence loopTheory where
  Evidence := fun _ _ => Bool
  erases_iff := by
    intros
    constructor
    · intro _
      trivial
    · intro _
      exact ⟨false⟩

def optionSteps : StepEvidence loopTheory where
  Evidence := fun _ _ => Option Unit
  erases_iff := by
    intros
    constructor
    · intro _
      trivial
    · intro _
      exact ⟨none⟩

def unitSteps : StepEvidence loopTheory where
  Evidence := fun _ _ => Unit
  erases_iff := by
    intros
    constructor
    · intro _
      trivial
    · intro _
      exact ⟨()⟩

def boolSystem : ProofRelevantGSLT := ⟨loopTheory, boolSteps⟩
def optionSystem : ProofRelevantGSLT := ⟨loopTheory, optionSteps⟩
def unitSystem : ProofRelevantGSLT := ⟨loopTheory, unitSteps⟩

/-- Two different carriers can retain exactly the same two occurrences. -/
def boolOptionEquiv : Bool ≃ Option Unit where
  toFun
    | false => none
    | true => some ()
  invFun
    | none => false
    | some _ => true
  left_inv value := by cases value <;> rfl
  right_inv value := by cases value <;> rfl

/-- A nontrivial exact translation changes the evidence representation while
retaining both occurrences. -/
def boolToOptionUnderlying : Translation boolSystem optionSystem where
  mapTerm := fun term => term
  mapEquiv := fun equivalent => equivalent
  mapEvidence := boolOptionEquiv
  liftEvidence := by
    intro sourceTerm targetTerm evidence
    exact ⟨targetTerm, boolOptionEquiv.symm evidence, ⟨⟨rfl⟩⟩⟩

def boolToOption : ExactTranslation boolSystem optionSystem := by
  refine
    { toTranslation := boolToOptionUnderlying
      evidenceEquiv := ?_
      evidenceEquiv_agrees := ?_ }
  · intro sourceTerm sourceTarget
    change Bool ≃ Option Unit
    exact boolOptionEquiv
  · intro sourceTerm sourceTarget evidence
    cases evidence <;> rfl

theorem boolToOption_distinguishes_occurrences :
    boolToOption.toTranslation.mapEvidence (sourceTerm := ())
        (sourceTarget := ()) false ≠
      boolToOption.toTranslation.mapEvidence true := by
  simp [boolToOption, boolToOptionUnderlying, boolOptionEquiv]

/-- Collapsing the two Boolean occurrences to one unit occurrence cannot be
an exact proof-fibre translation, even though the two semantic GSLTs have the
same proposition-valued step relation. -/
theorem no_exact_bool_to_unit :
    Not (Nonempty (ExactTranslation boolSystem unitSystem)) := by
  rintro ⟨translation⟩
  let fibreEquiv : Bool ≃ Unit := translation.evidenceEquiv () ()
  have collision : fibreEquiv false = fibreEquiv true := by
    cases fibreEquiv false
    cases fibreEquiv true
    rfl
  exact Bool.false_ne_true (fibreEquiv.injective collision)

end Canary

#print axioms Translation.toCovered
#print axioms ExactTranslation.comp
#print axioms Canary.boolToOption_distinguishes_occurrences
#print axioms Canary.no_exact_bool_to_unit

end Mettapedia.GSLT.ProofRelevant
