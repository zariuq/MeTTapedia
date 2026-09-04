import Mettapedia.GSLT.LanguageDef.ContextualInferenceRule

/-!
# Proof-relevant semantics for explicit contextual inference

`ContextualInferenceRule` retains ordered variable and relation contexts in
syntax.  This module supplies the corresponding semantic interface without
choosing a particular object logic.

A model assigns an evidence type to every formula and to every ambient
context hole.  Context evidence follows the authored context structure, so
order, duplicate occurrences, and the distinction between an explicit
assumption and an ambient hole remain visible.  Propositional satisfaction is
the mere inhabitation of that evidence type.  Open-sequent validity requires
conclusion evidence for every pair of satisfying contexts.

The wire interpretation is fail-closed: malformed context or sequent codes
have no meaning.  No proof checker, generated derivation, or operational
evaluator participates in these definitions.
-/

set_option autoImplicit false

universe u v w

namespace Mettapedia.GSLT.LanguageDef.ContextualInferenceSemantics

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.ContextualInference
open Mettapedia.GSLT.LanguageDef.InferenceChecker

/-- Independent proof-relevant interpretation of formulas and ambient
context holes at one shared semantic world.  A world may be a valuation, an
operational activation, or another client-selected environment.  Indexing
every evidence component by the same world prevents a context from splicing
evidence obtained from incompatible activations. -/
structure Model where
  World : Type w
  FormulaEvidence : World → Pattern → Type u
  HoleEvidence : World → String → Type v

/-- Empty evidence at an arbitrary universe level. -/
inductive NoEvidence.{x} : Type x

instance : IsEmpty NoEvidence :=
  ⟨fun evidence => nomatch evidence⟩

/-- Ordered evidence for a finite formula row.  Repeated formulas contribute
repeated evidence positions. -/
inductive FormulaRowEvidence (model : Model.{u, v, w})
    (world : model.World) :
    List Pattern → Type (max u w) where
  | nil : FormulaRowEvidence model world []
  | cons {formula : Pattern} {formulas : List Pattern}
      (head : model.FormulaEvidence world formula)
      (tail : FormulaRowEvidence model world formulas) :
      FormulaRowEvidence model world (formula :: formulas)

namespace FormulaRowEvidence

/-- Construct ordered evidence from evidence at every exact list position.
The index, rather than mere list membership, keeps equal formula occurrences
distinct. -/
def ofIndexed (model : Model.{u, v, w}) (world : model.World) :
    {formulas : List Pattern} →
      (∀ index : Fin formulas.length,
        model.FormulaEvidence world (formulas.get index)) →
      FormulaRowEvidence model world formulas
  | [], _ => .nil
  | _formula :: formulas, evidence =>
      .cons (evidence ⟨0, by simp⟩)
        (ofIndexed model world fun index => evidence index.succ)

/-- Retrieve evidence at one exact authored row position. -/
def get {model : Model.{u, v, w}} {world : model.World} :
    {formulas : List Pattern} → FormulaRowEvidence model world formulas →
      (index : Fin formulas.length) →
      model.FormulaEvidence world (formulas.get index)
  | [], .nil, index => Fin.elim0 index
  | _formula :: _formulas, .cons head tail, index =>
      Fin.cases head (fun tailIndex => get tail tailIndex) index

@[simp] theorem get_ofIndexed (model : Model.{u, v, w})
    (world : model.World) {formulas : List Pattern}
    (evidence : ∀ index : Fin formulas.length,
      model.FormulaEvidence world (formulas.get index))
    (index : Fin formulas.length) :
    (ofIndexed model world evidence).get index = evidence index := by
  induction formulas with
  | nil => exact Fin.elim0 index
  | cons formula formulas inductionHypothesis =>
      refine Fin.cases ?_ (fun tailIndex => ?_) index
      · rfl
      · exact inductionHypothesis
          (fun rowIndex => evidence rowIndex.succ) tailIndex

end FormulaRowEvidence

/-- Evidence for an authored context schema.  Explicit extensions and an
ambient hole are deliberately different constructors. -/
inductive ContextEvidence (model : Model.{u, v, w})
    (world : model.World) :
    ContextSchema → Type (max u v w) where
  | empty : ContextEvidence model world .empty
  | hole (name : String) (evidence : model.HoleEvidence world name) :
      ContextEvidence model world (.hole name)
  | extend {formula : Pattern} {tail : ContextSchema}
      (head : model.FormulaEvidence world formula)
      (rest : ContextEvidence model world tail) :
      ContextEvidence model world (.extend formula tail)

namespace ContextEvidence

/-- Split evidence for an explicit context prefix into the exact ordered row
evidence and evidence for the ambient tail.  Equal formulas remain distinct
positions in the returned row. -/
def splitPrepend (model : Model.{u, v, w}) (world : model.World) :
    (formulas : List Pattern) → (tail : ContextSchema) →
      ContextEvidence model world (ContextSchema.prepend formulas tail) →
        FormulaRowEvidence model world formulas ×
          ContextEvidence model world tail
  | [], _tail, evidence => ⟨.nil, evidence⟩
  | _formula :: formulas, tail, .extend head rest =>
      let split := splitPrepend model world formulas tail rest
      ⟨.cons head split.1, split.2⟩

/-- Reassemble an explicit prefix from its ordered formula evidence and its
ambient-tail evidence.  This is the proof-relevant inverse direction used
when one rule retains a context across a premise and conclusion. -/
def joinPrepend (model : Model.{u, v, w}) (world : model.World) :
    {formulas : List Pattern} → {tail : ContextSchema} →
      FormulaRowEvidence model world formulas →
        ContextEvidence model world tail →
          ContextEvidence model world (ContextSchema.prepend formulas tail)
  | [], _tail, .nil, tailEvidence => tailEvidence
  | _formula :: _formulas, _tail, .cons head rest, tailEvidence =>
      .extend head (joinPrepend model world rest tailEvidence)

end ContextEvidence

/-- Propositional satisfaction is inhabitation of the proof-relevant context
evidence type. -/
def ContextSatisfies (model : Model.{u, v, w}) (world : model.World)
    (context : ContextSchema) : Prop :=
  Nonempty (ContextEvidence model world context)

/-- Ordered satisfaction of a finite formula row. -/
def FormulaRowSatisfies (model : Model.{u, v, w}) (world : model.World)
    (formulas : List Pattern) : Prop :=
  Nonempty (FormulaRowEvidence model world formulas)

/-- Evidence for both contexts of one sequent. -/
structure SequentEnvironment (model : Model.{u, v, w})
    (sequent : Sequent) : Type (max u v w) where
  world : model.World
  variableEvidence : ContextEvidence model world sequent.variableContext
  relationEvidence : ContextEvidence model world sequent.relationContext

/-- An open sequent is valid when every environment satisfying both authored
contexts supplies independent evidence for its conclusion. -/
def SequentValid (model : Model.{u, v, w}) (sequent : Sequent) : Prop :=
  ∀ environment : SequentEnvironment model sequent,
    Nonempty (model.FormulaEvidence environment.world sequent.conclusion)

/-! ## Exact context equations -/

@[simp] theorem contextSatisfies_empty (model : Model.{u, v, w})
    (world : model.World) :
    ContextSatisfies model world .empty :=
  ⟨.empty⟩

@[simp] theorem contextSatisfies_hole_iff (model : Model.{u, v, w})
    (world : model.World) (name : String) :
    ContextSatisfies model world (.hole name) ↔
      Nonempty (model.HoleEvidence world name) := by
  constructor
  · rintro ⟨evidence⟩
    cases evidence with
    | hole _ holeEvidence => exact ⟨holeEvidence⟩
  · rintro ⟨holeEvidence⟩
    exact ⟨.hole name holeEvidence⟩

@[simp] theorem contextSatisfies_extend_iff (model : Model.{u, v, w})
    (world : model.World) (formula : Pattern) (tail : ContextSchema) :
    ContextSatisfies model world (.extend formula tail) ↔
      Nonempty (model.FormulaEvidence world formula) ∧
        ContextSatisfies model world tail := by
  constructor
  · rintro ⟨evidence⟩
    cases evidence with
    | extend head rest => exact ⟨⟨head⟩, ⟨rest⟩⟩
  · rintro ⟨⟨head⟩, ⟨rest⟩⟩
    exact ⟨.extend head rest⟩

@[simp] theorem formulaRowSatisfies_nil (model : Model.{u, v, w})
    (world : model.World) :
    FormulaRowSatisfies model world [] :=
  ⟨.nil⟩

@[simp] theorem formulaRowSatisfies_cons_iff (model : Model.{u, v, w})
    (world : model.World) (formula : Pattern) (formulas : List Pattern) :
    FormulaRowSatisfies model world (formula :: formulas) ↔
      Nonempty (model.FormulaEvidence world formula) ∧
        FormulaRowSatisfies model world formulas := by
  constructor
  · rintro ⟨evidence⟩
    cases evidence with
    | cons head tail => exact ⟨⟨head⟩, ⟨tail⟩⟩
  · rintro ⟨⟨head⟩, ⟨tail⟩⟩
    exact ⟨.cons head tail⟩

/-- Prefix satisfaction factors into the exact ordered prefix evidence and
the retained tail evidence. -/
theorem contextSatisfies_prepend_iff (model : Model.{u, v, w})
    (world : model.World) (formulas : List Pattern) (tail : ContextSchema) :
    ContextSatisfies model world (ContextSchema.prepend formulas tail) ↔
      FormulaRowSatisfies model world formulas ∧
        ContextSatisfies model world tail := by
  induction formulas with
  | nil => simp
  | cons formula formulas inductionHypothesis =>
      rw [ContextSchema.prepend_cons, contextSatisfies_extend_iff,
        inductionHypothesis, formulaRowSatisfies_cons_iff]
      constructor
      · rintro ⟨head, row, tailEvidence⟩
        exact ⟨⟨head, row⟩, tailEvidence⟩
      · rintro ⟨⟨head, row⟩, tailEvidence⟩
        exact ⟨head, row, tailEvidence⟩

/-! ## Fail-closed wire interpretation -/

/-- A canonical context wire receives exactly the evidence of its decoded
authored context.  Malformed wires receive the empty type. -/
def ContextWireEvidence (model : Model.{u, v, w}) (world : model.World)
    (wire : Pattern) :
    Type (max u v w) :=
  match decodeContext? wire with
  | some context => ContextEvidence model world context
  | none => NoEvidence

/-- A canonical contextual judgment is interpreted as open-sequent validity.
Malformed or foreign judgments are false. -/
def JudgmentMeaning (model : Model.{u, v, w}) (wire : Pattern) : Prop :=
  match decodeSequent? wire with
  | some sequent => SequentValid model sequent
  | none => False

@[simp] theorem contextWireEvidence_encode (model : Model.{u, v, w})
    (world : model.World) (context : ContextSchema) :
    ContextWireEvidence model world (encodeContext context) =
      ContextEvidence model world context := by
  simp [ContextWireEvidence]

theorem not_contextWireEvidence_of_decode_none (model : Model.{u, v, w})
    (world : model.World)
    {wire : Pattern} (malformed : decodeContext? wire = none) :
    ¬ Nonempty (ContextWireEvidence model world wire) := by
  simp only [ContextWireEvidence, malformed]
  rintro ⟨evidence⟩
  nomatch evidence

@[simp] theorem judgmentMeaning_lowerSequent (model : Model.{u, v, w})
    (sequent : Sequent) :
    JudgmentMeaning model (lowerSequent sequent) ↔
      SequentValid model sequent := by
  simp [JudgmentMeaning]

theorem not_judgmentMeaning_of_decode_none (model : Model.{u, v, w})
    {wire : Pattern} (malformed : decodeSequent? wire = none) :
    ¬ JudgmentMeaning model wire := by
  simp [JudgmentMeaning, malformed]

/-! ## The discharged-guard countermodel -/

namespace Canary

private def guardFormula : Pattern :=
  .apply "$gslt:context-semantics:guard" []

private def targetFormula : Pattern :=
  .apply "$gslt:context-semantics:target" []

private def modalFormula : Pattern :=
  .apply "$gslt:context-semantics:modal" []

/-- Only the target formula has evidence.  In particular, the guard and modal
claims are independently false. -/
def vacuityModel : Model where
  World := Unit
  FormulaEvidence := fun _ formula =>
    if formula = targetFormula then Unit else Empty
  HoleEvidence := fun _ _ => Unit

private def guardedBody : Sequent where
  variableContext := .empty
  relationContext := .extend guardFormula .empty
  conclusion := targetFormula

private def dischargedConclusion : Sequent where
  variableContext := .empty
  relationContext := .empty
  conclusion := modalFormula

/-- A body under an impossible guard is valid vacuously, even though its
target formula is independently inhabited. -/
theorem guardedBody_valid : SequentValid vacuityModel guardedBody := by
  intro environment
  cases environment.relationEvidence with
  | extend guardEvidence _rest =>
      exact guardEvidence.elim

/-- Dropping the guard does not produce modal evidence. -/
theorem dischargedConclusion_invalid :
    ¬ SequentValid vacuityModel dischargedConclusion := by
  intro valid
  have result := valid
    { world := ()
      variableEvidence := .empty
      relationEvidence := .empty }
  simp [vacuityModel, dischargedConclusion, modalFormula, targetFormula]
    at result

/-- The implication represented by the guarded body cannot justify the
unguarded modal conclusion. -/
theorem body_valid_does_not_imply_discharged_conclusion :
    SequentValid vacuityModel guardedBody ∧
      ¬ SequentValid vacuityModel dischargedConclusion :=
  ⟨guardedBody_valid, dischargedConclusion_invalid⟩

/-! ### Canonical-context instantiation boundary -/

/-- A declared ground formula used to isolate context-code validity from
formula-code validity in the checker counterexample below. -/
private def checkerTruthTerm : GrammarRule where
  label := "$gslt:context-semantics:checker-truth"
  category := formulaType.name
  params := []
  syntaxPattern := []

/-- The smallest open contextual rule: it concludes an arbitrary declared
formula under an ambient variable context.  The schema itself is locally and
globally valid. -/
private def checkerOpenRule : RuleSchema where
  id := ⟨"$gslt:context-semantics:checker-open"⟩
  metavariables := [("Gamma", 0), ("Claim", 0)]
  premises := []
  conclusion := lowerSequent
    { variableContext := .hole "Gamma"
      relationContext := .empty
      conclusion := .fvar "Claim" }
  sideConditions := []

private def checkerDefinition : CalculusLanguageDef :=
  { ContextualInference.definition with
    terms := ContextualInference.definition.terms ++ [checkerTruthTerm]
    rules := [checkerOpenRule] }

private theorem checkerDefinition_valid : checkerDefinition.isValid = true := by
  decide +kernel

private def checkedDefinition : ValidatedCalculusLanguageDef :=
  ⟨checkerDefinition, checkerDefinition_valid⟩

/-- This ground term is deliberately not a canonical context code. -/
private def malformedContextCode : Pattern :=
  .apply "$gslt:context-semantics:not-a-context" []

private def checkerTruth : Pattern :=
  .apply checkerTruthTerm.label []

private def malformedContextRuleInstance : RuleInstance where
  ruleId := checkerOpenRule.id
  arguments := [malformedContextCode, checkerTruth]

private def malformedContextConclusion : Pattern :=
  .apply contextualJudgment.head
    [malformedContextCode, encodeContext .empty, checkerTruth]

/-- Ordinary ground-argument validity does not certify that an argument used
as an ambient context is a canonical context code. -/
theorem checker_accepts_malformed_context_instance :
    RuleApplication checkedDefinition malformedContextRuleInstance []
      malformedContextConclusion := by
  apply instantiateRule?_eq_some_iff_application.mp
  decide +kernel

/-- The independently defined contextual decoder correctly rejects the same
checker-produced conclusion. -/
theorem malformed_context_instance_rejected :
    decodeSequent? malformedContextConclusion = none := by
  rfl

/-- Consequently, raw rule application alone cannot imply fail-closed
contextual meaning.  A sound open calculus must additionally certify its
instantiated context arguments. -/
theorem checker_application_need_not_have_contextual_meaning :
    RuleApplication checkedDefinition malformedContextRuleInstance []
        malformedContextConclusion ∧
      ¬ JudgmentMeaning vacuityModel malformedContextConclusion := by
  refine ⟨checker_accepts_malformed_context_instance, ?_⟩
  simp [JudgmentMeaning, malformed_context_instance_rejected]

end Canary

#print axioms contextSatisfies_prepend_iff
#print axioms ContextEvidence.splitPrepend
#print axioms ContextEvidence.joinPrepend
#print axioms contextWireEvidence_encode
#print axioms not_contextWireEvidence_of_decode_none
#print axioms judgmentMeaning_lowerSequent
#print axioms not_judgmentMeaning_of_decode_none
#print axioms Canary.guardedBody_valid
#print axioms Canary.dischargedConclusion_invalid
#print axioms Canary.body_valid_does_not_imply_discharged_conclusion
#print axioms Canary.checker_accepts_malformed_context_instance
#print axioms Canary.malformed_context_instance_rejected
#print axioms Canary.checker_application_need_not_have_contextual_meaning

end Mettapedia.GSLT.LanguageDef.ContextualInferenceSemantics
