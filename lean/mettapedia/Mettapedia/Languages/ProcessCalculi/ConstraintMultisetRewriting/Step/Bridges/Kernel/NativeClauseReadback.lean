import Mettapedia.Languages.HOLLight.ExactFormulaReadback
import Mettapedia.Languages.HOLLight.SourceProfileModels
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Kernel.SourceDisjunction

/-!
# Reading finite native record clauses in their received source model

A case table consists of typed formulas, including their guards and all
existential row witnesses. The reader checks the whole case equation against
an existing cache entry. Its semantics is derived in the model constructed
from the accepted proof and definition history.

This module provides the reader used by the concrete native table. It does
not itself contain that table, a received native proof, or a byte-level
implementation theorem. In particular, a table length or a record name is
not an admission certificate.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Kernel.NativeClauseReadback

open Mettapedia.Logic Mettapedia.Languages.OpenTheory
open Mettapedia.Languages.HOLLight
open ProofExecution TypeFamilySemantics
open ReferenceBooleanSemantics

universe w

structure Signature where
  state : HOL.Ty AtomicTy
  record : HOL.Ty AtomicTy
  step : HOL.ClosedTerm Symbol (state.arr (record.arr (state.arr .prop)))
  disjunction : SourceDisjunction.Operator

namespace Signature

variable (signature : Signature)

abbrev Clause := HOL.Formula Symbol [signature.state, signature.record, signature.state]

def alternatives : List signature.Clause → signature.Clause
  | [] => .const StandardTheoryInterpretation.Interpretation.Symbols.falsity
  | [first] => first
  | first :: second :: later =>
      .app (.app (HOL.weakenCtx _ signature.disjunction) first) (alternatives (second :: later))

/-- The source equation is lowered using the existing proved logical
expansion. Every clause remains part of the comparison. -/
def equation (clauses : List signature.Clause) : HOL.ClosedFormula Symbol :=
  universal (universal (universal (.eq
    (.app (.app (.app (HOL.weakenCtx _ signature.step) (.var (.vs (.vs .vz))))
      (.var (.vs .vz))) (.var .vz))
    (signature.alternatives clauses))))

abbrev State (model : HOL.HenkinModel.{0,0,w+1} AtomicTy Symbol) :=
  HOL.Ty.denote.{0,w+1} model.Carrier signature.state

abbrev Record (model : HOL.HenkinModel.{0,0,w+1} AtomicTy Symbol) :=
  HOL.Ty.denote.{0,w+1} model.Carrier signature.record

def empty (model : HOL.HenkinModel.{0,0,w+1} AtomicTy Symbol) : model.Valuation [] :=
  fun index => nomatch index

theorem empty_unique (model : HOL.HenkinModel.{0,0,w+1} AtomicTy Symbol)
    (valuation : model.Valuation []) : @valuation = @empty model := by
  funext type index
  exact nomatch index

def values (model : HOL.HenkinModel.{0,0,w+1} AtomicTy Symbol)
    (source : signature.State model) (record : signature.Record model)
    (target : signature.State model) : model.Valuation [signature.state, signature.record, signature.state] :=
  model.extend (model.extend (model.extend (empty model) source) record) target

def stepValue (model : HOL.HenkinModel.{0,0,w+1} AtomicTy Symbol)
    (source : signature.State model) (record : signature.Record model)
    (target : signature.State model) : Prop :=
  (model.denote signature.step (empty model) source record target).down

def admitsClause (model : HOL.HenkinModel.{0,0,w+1} AtomicTy Symbol)
    (clause : signature.Clause) (source : signature.State model)
    (record : signature.Record model) (target : signature.State model) : Prop :=
  (model.denote clause (signature.values model source record target)).down

theorem alternatives_meaning (model : HOL.HenkinModel.{0,0,w+1} AtomicTy Symbol)
    (meanings : Meanings model)
    (disjunction : ∀ left right : ULift.{w+1} Prop,
      (model.denote signature.disjunction (empty model) left right).down ↔ left.down ∨ right.down)
    (clauses : List signature.Clause) (valuation : model.Valuation [signature.state, signature.record, signature.state]) :
    (model.denote (signature.alternatives clauses) valuation).down ↔
      ∃ clause ∈ clauses, (model.denote clause valuation).down := by
  induction clauses with
  | nil => simp [alternatives, HOL.HenkinModel.denote, meanings.falsity]
  | cons first later ih =>
      cases later with
      | nil => simp [alternatives]
      | cons second later =>
          simp only [alternatives, HOL.HenkinModel.denote, HOL.PreModel.denote,
            HOL.HenkinModel.denote_weakenCtx, empty_unique model, disjunction]
          simpa only [List.mem_cons, exists_eq_or_imp] using
            or_congr_right ih

theorem equation_meaning (model : HOL.HenkinModel.{0,0,w+1} AtomicTy Symbol)
    (full : model.FullDomains) (meanings : Meanings model)
    (disjunction : ∀ left right : ULift.{w+1} Prop,
      (model.denote signature.disjunction (empty model) left right).down ↔ left.down ∨ right.down)
    (clauses : List signature.Clause) :
    model.models (signature.equation clauses) ↔
      ∀ source record target, signature.stepValue model source record target ↔
        ∃ clause ∈ clauses, signature.admitsClause model clause source record target := by
  have admitted : ∀ type value, model.adm type value := full
  simp only [equation, HOL.HenkinModel.models, HOL.PreModel.models,
    denote_universal model meanings,
    HOL.HenkinModel.denote, HOL.PreModel.denote, HOL.HenkinModel.denote_weakenCtx,
    HOL.PreModel.extend, admitted, forall_true_left, model.eqv_iff_eq_of_fullDomains full]
  simp only [empty_unique model]
  constructor
  · intro holds source record target
    have cases := signature.alternatives_meaning model meanings disjunction clauses
      (signature.values model source record target)
    simpa [values, stepValue, admitsClause] using
      (Iff.of_eq (congrArg ULift.down (holds source record target))).trans cases
  · intro holds source record target
    apply ULift.ext
    apply propext
    simpa [values, stepValue, admitsClause] using (holds source record target).trans
      (signature.alternatives_meaning model meanings disjunction clauses
        (signature.values model source record target)).symm

end Signature

structure Reading (signature : Signature) (clauses : List signature.Clause) (state : Registered.State) where
  disjunction : ExactFormulaReadback.ReadFact state (SourceDisjunction.equation signature.disjunction)
  fact : ExactFormulaReadback.ReadFact state (signature.equation clauses)

def read? (signature : Signature) (clauses : List signature.Clause)
    (state : Registered.State) (disjunctionIndex index : Nat) : Option (Reading signature clauses state) := do
  return ⟨← ExactFormulaReadback.read? state disjunctionIndex
      (SourceDisjunction.equation signature.disjunction),
    ← ExactFormulaReadback.read? state index (signature.equation clauses)⟩

/-- A checked root is interpreted in its own constructed history model.
No case relation or semantic admission equivalence is supplied as a premise. -/
theorem received_cases (signature : Signature) (clauses : List signature.Clause)
    (commands : List Registered.Command) (state : Registered.State)
    (accepted : Registered.replayFrom SourceProfileModels.policy
      (Registered.empty SourceProfile.primitiveContext) commands = some state)
    (reading : Reading signature clauses state)
    (other : OperatorFamilies.{w}) (assignment : Assignment.{w}) :
    let model := (SourceProfileModels.sourceReplayFrame commands state accepted).frame.model other assignment
    ∀ source record target, signature.stepValue model source record target ↔
      ∃ clause ∈ clauses, signature.admitsClause model clause source record target := by
  let frame := (SourceProfileModels.sourceReplayFrame commands state accepted).frame
  have disjunction := SourceDisjunction.received_meaning signature.disjunction commands state
    accepted reading.disjunction other assignment
  exact (signature.equation_meaning (frame.model other assignment)
    (frame.model_fullDomains other assignment)
    (replay_meanings commands state accepted other assignment)
    (by simpa only [Signature.empty_unique (frame.model other assignment)] using disjunction) clauses).mp
      (ExactFormulaReadback.read_models frame other assignment _ reading.fact)

/-- A successful read cannot silently erase an additional case from the
comparison: the retained source conclusion is the complete expanded equation. -/
theorem read_retains_equation (signature : Signature) (clauses : List signature.Clause)
    (state : Registered.State) (reading : Reading signature clauses state) :
    ∃ fact ∈ state.cache, fact.sequent.hyp = ∅ ∧
      Translates [] fact.sequent.concl.term .prop (signature.equation clauses) :=
  ⟨reading.fact.fact, reading.fact.known, reading.fact.closed, reading.fact.translated⟩

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Kernel.NativeClauseReadback
