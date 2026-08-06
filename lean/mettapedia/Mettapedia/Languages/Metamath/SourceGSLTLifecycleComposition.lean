import Mettapedia.Languages.Metamath.SourceGSLTRawSourceComposition
import Mettapedia.Languages.Metamath.SourceGSLTNormalTheorem
import Mettapedia.Languages.Metamath.SourceGSLTCompressedTheorem

/-!
# Lifecycle composition: carried obligations against the theorem joints

Tranche step 4, statement-level joints, both lanes.  The raw-source
composition fold applies
each `$p` statement's declaration effect (`insertAssertion?`) and
carries a `TheoremObligation` — label, tagged formula, and the exact
located proof payload.  This module discharges those obligations into
`NormalTheoremStep`, the source GSLT's proof-relevant `$p` semantics,
in both directions against the shipped mm-lean4 execution:

* `applyStatement_provable_inv` — inversion: an accepted `$p` fold step
  is exactly a tagging success plus an `insertAssertion?` acceptance,
  emitting exactly one obligation.
* `mkNormalTheoremStep` — witness-form assembly: an obligation whose
  insertion was accepted, together with a validated presentation of the
  pre-insertion prefix and an exact proof-occurrence tree whose labels
  are the carried steps, **is** a `NormalTheoremStep`; the fold's own
  transition is the step's transition, and pre-state validity comes
  from the gate, not from an extra hypothesis.
* `obligation_normal_lifecycle_of_mmLean4` — **preservation**: if the
  shipped mm-lean4 normal fold (`RuntimeDB.stepNormal` over the carried
  labels, from an empty stack) accepts with the obligation's formula on
  the stack, the theorem step exists.  The execution weight is carried
  by the sealed `normalFold_accepts_iff_exactSourceTree`.
* `normalTheoremStep_mmLean4_accepts` — **reflection**: every normal
  theorem step forces the shipped fold to accept its label list with
  its formula as the result.

The compressed lane composes the same way: `CompressedWitness` bundles
the machine-level evidence, `mkCompressedTheoremStep` ties it to the
fold's insertion, and `applyStatement_compressed_lifecycle` composes;
the step's `explicitHeaderLabels`/`bodyWords` indices are exactly the
carried payload's `header.map (·.name)` and `words.map (·.bytes)`.
Downstream, `CompressedTheoremStep` already feeds the shipped-parser
preservation seam (`mmLean4ParserCorePreserved`).

`LifecycleRun` is the whole-run relation — the statement sequence with
every `$p` discharged by its proof-relevant theorem step over the
fold's own intermediate states — and `LifecycleRun.toFold` proves it
refines to the executable fold with the same final state.
`foldStatements_toLifecycleRun_of_discharges` proves the converse under
one proof-relevant discharge at each exact fold transition; declaration
success alone is never promoted to proof validity.  No new computational
claim is introduced: assemblies are definitional and the mm-lean4 iff is
sealed upstream, where its executable calibration lives.  The remaining
umbrella-level obligation is to discharge lexical leaf coverage from the
raw-byte classifier and compose that fact with the independently proved
segmented-statement / `sourceProductions` correspondence.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Metamath.SourceGSLTLifecycleComposition

open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.Languages.Metamath.InferenceEncoding
open Mettapedia.Languages.Metamath.MMLean4Bridge
open Mettapedia.Languages.Metamath.InferenceProjection
open Mettapedia.Languages.Metamath.SourceGSLTState
open Mettapedia.Languages.Metamath.SourceGSLTNormalTheorem
open Mettapedia.Languages.Metamath.SourceGSLTRawSourceComposition
open Mettapedia.Languages.Metamath.SourceInferenceExecution
open Mettapedia.Languages.Metamath.SourceInferenceProjection

/-- Inversion of the fold's `$p` case: acceptance is exactly tagging
success plus assertion insertion, with exactly one carried
obligation. -/
theorem applyStatement_provable_inv {state next : SourceState}
    {site : SourceGSLTRawByteLexical.LocatedByteSpan}
    {label typecode : LocatedName} {body : List LocatedName}
    {proof : ProofPayload}
    {separator terminator : SourceGSLTRawByteLexical.LocatedByteSpan}
    {obligations : List TheoremObligation}
    (h : applyStatement state
        (.provable site label typecode body proof separator terminator) =
      .ok (next, obligations)) :
    ∃ syms, tagBody state body = .ok syms ∧
      insertAssertion? state label.name ⟨typecode.name, syms⟩ =
        some next ∧
      obligations = [⟨site, label, ⟨typecode.name, syms⟩, proof⟩] := by
  cases htag : tagBody state body with
  | rejected r =>
      simp only [applyStatement, htag] at h
      exact nomatch h
  | ok syms =>
      simp only [applyStatement, htag] at h
      cases hins : insertAssertion? state label.name
          ⟨typecode.name, syms⟩ with
      | none =>
          simp only [hins] at h
          exact nomatch h
      | some s =>
          simp only [hins] at h
          cases h
          exact ⟨syms, rfl, hins, rfl⟩

/-- Witness-form assembly: an accepted insertion plus a presentation
and an exact tree with the carried labels is a normal theorem step.
Pre-state validity is the gate's own guarantee. -/
def mkNormalTheoremStep {state next : SourceState}
    {ob : TheoremObligation}
    (hins : insertAssertion? state ob.label.name ob.formula = some next)
    (target : ValidatedPresentation)
    (hpres : presentationOfSourcePrefix? state.toSourcePrefix =
      some target.1)
    (tree : SourceGeneratedProvesTree state.toSourcePrefix target
      ob.formula)
    {steps : List LocatedName}
    (hlabels : tree.labels = steps.map (·.name)) :
    NormalTheoremStep state next ob.label.name ob.formula
      (steps.map (·.name)) :=
  { sourceValid := insertAssertion?_valid_before hins
    target := target
    presentation_eq := hpres
    tree := tree
    labels_eq := hlabels
    inserted := hins }

/-- **Preservation against the shipped executor**: if mm-lean4's normal
step function accepts the carried label list from an empty stack with
the obligation's formula as the single result, the source GSLT's
theorem step exists, with the fold's own insertion as its
transition. -/
theorem obligation_normal_lifecycle_of_mmLean4 {state next : SourceState}
    {ob : TheoremObligation}
    (hins : insertAssertion? state ob.label.name ob.formula = some next)
    (target : ValidatedPresentation)
    (hpres : presentationOfSourcePrefix? state.toSourcePrefix =
      some target.1)
    (db : RuntimeDB)
    (hproject : projectPrefix? db =
      some state.toSourcePrefix.toProjection)
    (base : RuntimeProofState) (hbase : base.stack = #[])
    {steps : List LocatedName}
    (hrun : (steps.map (·.name)).foldlM
        (fun proofState label => db.stepNormal proofState label) base =
      .ok (base.push ob.formula.toRuntime)) :
    Nonempty (NormalTheoremStep state next ob.label.name ob.formula
      (steps.map (·.name))) := by
  obtain ⟨⟨tree, hlabels⟩⟩ :=
    (normalFold_accepts_iff_exactSourceTree db state.toSourcePrefix
      target base ob.formula (steps.map (·.name)) hpres hproject
      hbase).mp hrun
  exact ⟨mkNormalTheoremStep hins target hpres tree hlabels⟩

/-- **Reflection into the shipped executor**: every normal theorem step
forces mm-lean4's normal fold to accept its label list, producing
exactly its formula. -/
theorem normalTheoremStep_mmLean4_accepts
    {before after : SourceState} {label : String}
    {formula : ConstantHeadedFormula} {proofLabels : List String}
    (step : NormalTheoremStep before after label formula proofLabels)
    (db : RuntimeDB)
    (hproject : projectPrefix? db =
      some before.toSourcePrefix.toProjection)
    (base : RuntimeProofState) (hbase : base.stack = #[]) :
    proofLabels.foldlM
        (fun proofState stepLabel => db.stepNormal proofState stepLabel)
        base =
      .ok (base.push formula.toRuntime) := by
  exact (normalFold_accepts_iff_exactSourceTree db
    before.toSourcePrefix step.target base formula proofLabels
    step.presentation_eq hproject hbase).mpr
    ⟨⟨step.tree, step.labels_eq⟩⟩

/-- Fold-to-lifecycle composition, normal lane: an accepted `$p` fold
step whose payload is a normal proof, together with the presentation
and shipped-executor acceptance of the carried labels, yields the
theorem step over exactly the fold's transition. -/
theorem applyStatement_normal_lifecycle {state next : SourceState}
    {site : SourceGSLTRawByteLexical.LocatedByteSpan}
    {label typecode : LocatedName} {body steps : List LocatedName}
    {separator terminator : SourceGSLTRawByteLexical.LocatedByteSpan}
    {obligations : List TheoremObligation}
    (h : applyStatement state
        (.provable site label typecode body (.normal steps) separator
          terminator) =
      .ok (next, obligations))
    (target : ValidatedPresentation)
    (hpres : presentationOfSourcePrefix? state.toSourcePrefix =
      some target.1)
    (db : RuntimeDB)
    (hproject : projectPrefix? db =
      some state.toSourcePrefix.toProjection)
    (base : RuntimeProofState) (hbase : base.stack = #[])
    (hrun : ∀ syms, tagBody state body = .ok syms →
      (steps.map (·.name)).foldlM
          (fun proofState stepLabel =>
            db.stepNormal proofState stepLabel) base =
        .ok (base.push
          (ConstantHeadedFormula.toRuntime ⟨typecode.name, syms⟩))) :
    ∃ syms, tagBody state body = .ok syms ∧
      Nonempty (NormalTheoremStep state next label.name
        ⟨typecode.name, syms⟩ (steps.map (·.name))) := by
  obtain ⟨syms, htag, hins, hobs⟩ := applyStatement_provable_inv h
  refine ⟨syms, htag, ?_⟩
  exact obligation_normal_lifecycle_of_mmLean4
    (ob := ⟨site, label, ⟨typecode.name, syms⟩, .normal steps⟩)
    hins target hpres db hproject base hbase (hrun syms htag)

/-! ## The compressed lane -/

open Mettapedia.Languages.Metamath.SourceGSLTCompressedTheorem

/-- Machine-level witness bundle for one compressed occurrence over a
fixed pre-insertion state: everything `CompressedTheoremStep` needs
except the transition, which the fold supplies, and pre-state validity,
which the gate guarantees. -/
structure CompressedWitness (before : SourceState)
    (formula : ConstantHeadedFormula)
    (explicitHeaderLabels : List String)
    (bodyWords : List (List UInt8)) : Type where
  target : ValidatedPresentation
  presentation_eq :
    presentationOfSourcePrefix? before.toSourcePrefix = some target.1
  actions : List CompressedAction
  decoded : decodeProgram bodyWords = some actions
  initialState : MachineState before.toSourcePrefix target
  finalState : MachineState before.toSourcePrefix target
  header :
    HeaderBuild (headerItems before formula explicitHeaderLabels)
      (emptyMachine before.toSourcePrefix target) initialState
  execution : Execute initialState actions finalState
  rootId : Nat
  root : ProofNode before.toSourcePrefix target
  finalStack : finalState.stack = [rootId]
  rootLookup : finalState.nodes[rootId]? = some root
  rootFormula : root.formula = formula

/-- Witness-form assembly for the compressed lane: the carried
payload's header names and word bytes are exactly the step's indices,
and the fold's insertion is its transition. -/
def mkCompressedTheoremStep {state next : SourceState}
    {ob : TheoremObligation}
    (hins : insertAssertion? state ob.label.name ob.formula = some next)
    {header : List LocatedName} {words : List LocatedToken}
    (w : CompressedWitness state ob.formula (header.map (·.name))
      (words.map (·.bytes))) :
    CompressedTheoremStep state next ob.label.name ob.formula
      (header.map (·.name)) (words.map (·.bytes)) :=
  { sourceValid := insertAssertion?_valid_before hins
    target := w.target
    presentation_eq := w.presentation_eq
    actions := w.actions
    decoded := w.decoded
    initialState := w.initialState
    finalState := w.finalState
    header := w.header
    execution := w.execution
    rootId := w.rootId
    root := w.root
    finalStack := w.finalStack
    rootLookup := w.rootLookup
    rootFormula := w.rootFormula
    inserted := hins }

/-- Fold-to-lifecycle composition, compressed lane. -/
theorem applyStatement_compressed_lifecycle {state next : SourceState}
    {site : SourceGSLTRawByteLexical.LocatedByteSpan}
    {label typecode : LocatedName} {body : List LocatedName}
    {openParen closeParen : SourceGSLTRawByteLexical.LocatedByteSpan}
    {header : List LocatedName} {words : List LocatedToken}
    {separator terminator : SourceGSLTRawByteLexical.LocatedByteSpan}
    {obligations : List TheoremObligation}
    (h : applyStatement state
        (.provable site label typecode body
          (.compressed openParen header closeParen words) separator
          terminator) =
      .ok (next, obligations))
    (w : ∀ syms, tagBody state body = .ok syms →
      CompressedWitness state ⟨typecode.name, syms⟩
        (header.map (·.name)) (words.map (·.bytes))) :
    ∃ syms, tagBody state body = .ok syms ∧
      Nonempty (CompressedTheoremStep state next label.name
        ⟨typecode.name, syms⟩ (header.map (·.name))
        (words.map (·.bytes))) := by
  obtain ⟨syms, htag, hins, hobs⟩ := applyStatement_provable_inv h
  exact ⟨syms, htag,
    ⟨mkCompressedTheoremStep
      (ob := ⟨site, label, ⟨typecode.name, syms⟩,
        .compressed openParen header closeParen words⟩)
      hins (w syms htag)⟩⟩

/-! ## The whole-run lifecycle relation -/

/-- Forward computation of the fold's `$p` case from its components. -/
theorem applyStatement_provable_of {state next : SourceState}
    {site : SourceGSLTRawByteLexical.LocatedByteSpan}
    {label typecode : LocatedName} {body : List LocatedName}
    {proof : ProofPayload}
    {separator terminator : SourceGSLTRawByteLexical.LocatedByteSpan}
    {syms : List Metamath.Verify.Sym}
    (htag : tagBody state body = .ok syms)
    (hins : insertAssertion? state label.name ⟨typecode.name, syms⟩ =
      some next) :
    applyStatement state
        (.provable site label typecode body proof separator terminator) =
      .ok (next, [⟨site, label, ⟨typecode.name, syms⟩, proof⟩]) := by
  simp [applyStatement, htag, hins]

/-- Whole-run lifecycle: the statement sequence with every `$p`
discharged by its proof-relevant theorem step (normal or compressed)
over the fold's own intermediate states. -/
inductive LifecycleRun : SourceState → List RawStatement →
    SourceState → Type where
  | nil (state : SourceState) : LifecycleRun state [] state
  | localStep {state mid final : SourceState} {stmt : RawStatement}
      {rest : List RawStatement}
      (happly : applyStatement state stmt = .ok (mid, []))
      (tail : LifecycleRun mid rest final) :
      LifecycleRun state (stmt :: rest) final
  | normalStep {state mid final : SourceState}
      {site : SourceGSLTRawByteLexical.LocatedByteSpan}
      {label typecode : LocatedName} {body steps : List LocatedName}
      {separator terminator : SourceGSLTRawByteLexical.LocatedByteSpan}
      {rest : List RawStatement} {syms : List Metamath.Verify.Sym}
      (htag : tagBody state body = .ok syms)
      (step : NormalTheoremStep state mid label.name
        ⟨typecode.name, syms⟩ (steps.map (·.name)))
      (tail : LifecycleRun mid rest final) :
      LifecycleRun state
        (.provable site label typecode body (.normal steps) separator
          terminator :: rest) final
  | compressedStep {state mid final : SourceState}
      {site : SourceGSLTRawByteLexical.LocatedByteSpan}
      {label typecode : LocatedName} {body : List LocatedName}
      {openParen closeParen : SourceGSLTRawByteLexical.LocatedByteSpan}
      {header : List LocatedName} {words : List LocatedToken}
      {separator terminator : SourceGSLTRawByteLexical.LocatedByteSpan}
      {rest : List RawStatement} {syms : List Metamath.Verify.Sym}
      (htag : tagBody state body = .ok syms)
      (step : CompressedTheoremStep state mid label.name
        ⟨typecode.name, syms⟩ (header.map (·.name))
        (words.map (·.bytes)))
      (tail : LifecycleRun mid rest final) :
      LifecycleRun state
        (.provable site label typecode body
          (.compressed openParen header closeParen words) separator
          terminator :: rest) final

/-! ## Conditional reflection of the executable fold

The raw fold deliberately does not check proofs.  Its reverse direction is
therefore parameterized by a proof-relevant discharge for each statement at
the exact intermediate state reached by the fold. -/

/-- One statement's external proof obligation.  Local statements only need
their already computed empty-obligation transition.  A `$p` statement needs
the corresponding source theorem step; its insertion is thereby forced to be
the fold's exact transition. -/
inductive StatementDischarge :
    (state next : SourceState) → RawStatement → Type where
  | localStatement {state next : SourceState} {stmt : RawStatement}
      (happly : applyStatement state stmt = .ok (next, [])) :
      StatementDischarge state next stmt
  | normal {state next : SourceState}
      {site : SourceGSLTRawByteLexical.LocatedByteSpan}
      {label typecode : LocatedName} {body steps : List LocatedName}
      {separator terminator : SourceGSLTRawByteLexical.LocatedByteSpan}
      {syms : List Metamath.Verify.Sym}
      (htag : tagBody state body = .ok syms)
      (step : NormalTheoremStep state next label.name
        ⟨typecode.name, syms⟩ (steps.map (·.name))) :
      StatementDischarge state next
        (.provable site label typecode body (.normal steps) separator
          terminator)
  | compressed {state next : SourceState}
      {site : SourceGSLTRawByteLexical.LocatedByteSpan}
      {label typecode : LocatedName} {body : List LocatedName}
      {openParen closeParen : SourceGSLTRawByteLexical.LocatedByteSpan}
      {header : List LocatedName} {words : List LocatedToken}
      {separator terminator : SourceGSLTRawByteLexical.LocatedByteSpan}
      {syms : List Metamath.Verify.Sym}
      (htag : tagBody state body = .ok syms)
      (step : CompressedTheoremStep state next label.name
        ⟨typecode.name, syms⟩ (header.map (·.name))
        (words.map (·.bytes))) :
      StatementDischarge state next
        (.provable site label typecode body
          (.compressed openParen header closeParen words) separator
          terminator)

/-- A provider discharges any statement occurrence in this source list at
the exact state and transition selected by `applyStatement`.  It cannot
invent the fold trace or omit a theorem occurrence. -/
def DischargeProvider (statements : List RawStatement) : Type :=
  ∀ (state next : SourceState) (stmt : RawStatement)
    (obligations : List TheoremObligation),
    stmt ∈ statements →
    applyStatement state stmt = .ok (next, obligations) →
    StatementDischarge state next stmt

/-- **Conditional reverse direction**: executable declaration folding plus
one discharge for every encountered statement constructs the whole
proof-relevant lifecycle.  No proof validity is inferred from declaration
success. -/
def foldStatements_toLifecycleRun_of_discharges
    {state final : SourceState} {statements : List RawStatement}
    {obligations : List TheoremObligation}
    (hfold : foldStatements state statements = .ok (final, obligations))
    (discharges : DischargeProvider statements) :
    LifecycleRun state statements final := by
  induction statements generalizing state final obligations with
  | nil =>
      simp only [foldStatements] at hfold
      cases hfold
      exact .nil _
  | cons stmt rest ih =>
      simp only [foldStatements] at hfold
      cases happ : applyStatement state stmt with
      | rejected rejection =>
          simp only [happ] at hfold
          exact nomatch hfold
      | ok pair =>
          obtain ⟨next, stepObligations⟩ := pair
          simp only [happ] at hfold
          cases hrest : foldStatements next rest with
          | rejected rejection =>
              simp only [hrest] at hfold
              exact nomatch hfold
          | ok pair =>
              obtain ⟨tailFinal, tailObligations⟩ := pair
              simp only [hrest] at hfold
              have tailProvider : DischargeProvider rest := by
                intro before after candidate candidateObligations member
                  candidateApply
                exact discharges before after candidate candidateObligations
                  (List.Mem.tail stmt member) candidateApply
              have tailRun : LifecycleRun next rest tailFinal :=
                ih hrest tailProvider
              have discharge := discharges state next stmt stepObligations
                (List.Mem.head rest) happ
              cases discharge with
              | localStatement localApply =>
                  cases hfold
                  exact .localStep localApply tailRun
              | normal htag step =>
                  cases hfold
                  exact .normalStep htag step tailRun
              | compressed htag step =>
                  cases hfold
                  exact .compressedStep htag step tailRun

/-- **The lifecycle relation refines to the executable fold**: every
whole-run lifecycle derivation is realized by the fold, with the same
final state.  Each theorem step's own insertion is the fold's
transition at its position. -/
theorem LifecycleRun.toFold {state final : SourceState} :
    ∀ {statements : List RawStatement},
      LifecycleRun state statements final →
      ∃ obligations,
        foldStatements state statements = .ok (final, obligations) := by
  intro statements run
  induction run with
  | nil s => exact ⟨[], rfl⟩
  | localStep happly tail ih =>
      obtain ⟨obligations, hfold⟩ := ih
      exact ⟨obligations, by
        simp [foldStatements, happly, hfold]⟩
  | @normalStep state mid final site label typecode body steps
      separator terminator rest syms htag step tail ih =>
      obtain ⟨obligations, hfold⟩ := ih
      exact ⟨⟨site, label, ⟨typecode.name, syms⟩, .normal steps⟩ ::
          obligations, by
        simp [foldStatements,
          applyStatement_provable_of htag step.inserted, hfold]⟩
  | @compressedStep state mid final site label typecode body openParen
      closeParen header words separator terminator rest syms htag step
      tail ih =>
      obtain ⟨obligations, hfold⟩ := ih
      exact ⟨⟨site, label, ⟨typecode.name, syms⟩,
          .compressed openParen header closeParen words⟩ ::
          obligations, by
        simp [foldStatements,
          applyStatement_provable_of htag step.inserted, hfold]⟩

/-! ## Dependent discharge: the fold-to-lifecycle direction

A successful fold alone cannot yield a `LifecycleRun` — the fold
deliberately records `$p` obligations without checking proofs.  The
honest theorem threads a **discharge witness for every `$p` at the
fold's exact intermediate state**: the witness carries only what the
fold cannot provide (presentation and proof evidence); insertions and
pre-state validity come from the fold's own gates. -/

/-- Proof evidence for one normal `$p` occurrence over a fixed
pre-insertion state — everything `NormalTheoremStep` needs except the
transition and pre-state validity. -/
structure NormalDischarge (before : SourceState)
    (formula : ConstantHeadedFormula) (labels : List String) : Type where
  target : ValidatedPresentation
  presentation_eq :
    presentationOfSourcePrefix? before.toSourcePrefix = some target.1
  tree : SourceGeneratedProvesTree before.toSourcePrefix target formula
  labels_eq : tree.labels = labels

/-- The discharge a single statement demands at a given state: proof
evidence for a `$p` (normal or compressed, at the statement's own
tagged formula), nothing otherwise. -/
def StepWitness (state : SourceState) : RawStatement → Type
  | .provable _ _ typecode body (.normal steps) _ _ =>
      match tagBody state body with
      | .ok syms =>
          NormalDischarge state ⟨typecode.name, syms⟩
            (steps.map (·.name))
      | .rejected _ => PUnit
  | .provable _ _ typecode body
      (.compressed _ header _ words) _ _ =>
      match tagBody state body with
      | .ok syms =>
          CompressedWitness state ⟨typecode.name, syms⟩
            (header.map (·.name)) (words.map (·.bytes))
      | .rejected _ => PUnit
  | _ => PUnit

/-- Discharges threaded along the fold's own intermediate states. -/
def RunWitnesses : SourceState → List RawStatement → Type
  | _, [] => PUnit
  | state, stmt :: rest =>
      StepWitness state stmt ×
        (match applyStatement state stmt with
         | .ok (mid, _) => RunWitnesses mid rest
         | .rejected _ => PUnit)

/-- **Fold plus discharges is the whole-run lifecycle**: a successful
fold, together with a discharge for every `$p` at its exact
intermediate state, constructs the `LifecycleRun`.  Non-`$p` statements
need no witness; each `$p`'s theorem step is assembled from the fold's
own insertion and the supplied evidence. -/
def foldStatements_toLifecycle :
    ∀ {statements : List RawStatement} {state final : SourceState}
      {obligations : List TheoremObligation},
      foldStatements state statements = .ok (final, obligations) →
      RunWitnesses state statements →
      LifecycleRun state statements final
  | [], state, final, obligations, h, _ => by
      simp only [foldStatements] at h
      cases h
      exact .nil state
  | stmt :: rest, state, final, obligations, h, w => by
      obtain ⟨sw, wrest⟩ := w
      simp only [foldStatements] at h
      cases stmt with
      | provable site label typecode body proof separator terminator =>
          cases htag : tagBody state body with
          | rejected r =>
              simp only [applyStatement, htag] at h
              exact nomatch h
          | ok syms =>
              simp only [applyStatement, htag] at h
              cases hins : insertAssertion? state label.name
                  ⟨typecode.name, syms⟩ with
              | none =>
                  simp only [hins] at h
                  exact nomatch h
              | some mid =>
                  simp only [hins] at h
                  cases hrest : foldStatements mid rest with
                  | rejected r =>
                      simp only [hrest] at h
                      exact nomatch h
                  | ok finalPair =>
                      obtain ⟨final', restObs⟩ := finalPair
                      simp only [hrest] at h
                      cases h
                      rw [show applyStatement state
                          (.provable site label typecode body proof
                            separator terminator) =
                          .ok (mid, [⟨site, label,
                            ⟨typecode.name, syms⟩, proof⟩]) from
                        applyStatement_provable_of htag hins] at wrest
                      cases proof with
                      | normal steps =>
                          rw [show StepWitness state
                              (.provable site label typecode body
                                (.normal steps) separator terminator) =
                              (match tagBody state body with
                               | .ok syms =>
                                   NormalDischarge state
                                     ⟨typecode.name, syms⟩
                                     (steps.map (·.name))
                               | .rejected _ => PUnit) from rfl,
                            htag] at sw
                          exact .normalStep htag
                            { sourceValid :=
                                insertAssertion?_valid_before hins
                              target := sw.target
                              presentation_eq := sw.presentation_eq
                              tree := sw.tree
                              labels_eq := sw.labels_eq
                              inserted := hins }
                            (foldStatements_toLifecycle hrest wrest)
                      | compressed openParen header closeParen words =>
                          rw [show StepWitness state
                              (.provable site label typecode body
                                (.compressed openParen header closeParen
                                  words) separator terminator) =
                              (match tagBody state body with
                               | .ok syms =>
                                   CompressedWitness state
                                     ⟨typecode.name, syms⟩
                                     (header.map (·.name))
                                     (words.map (·.bytes))
                               | .rejected _ => PUnit) from rfl,
                            htag] at sw
                          exact .compressedStep htag
                            { sourceValid :=
                                insertAssertion?_valid_before hins
                              target := sw.target
                              presentation_eq := sw.presentation_eq
                              actions := sw.actions
                              decoded := sw.decoded
                              initialState := sw.initialState
                              finalState := sw.finalState
                              header := sw.header
                              execution := sw.execution
                              rootId := sw.rootId
                              root := sw.root
                              finalStack := sw.finalStack
                              rootLookup := sw.rootLookup
                              rootFormula := sw.rootFormula
                              inserted := hins }
                            (foldStatements_toLifecycle hrest wrest)
      | openScope site =>
          cases happ : applyLocalPayload? .openScope state with
          | none => simp only [applyStatement, happ] at h; exact nomatch h
          | some mid =>
              simp only [applyStatement, happ] at h
              cases hrest : foldStatements mid rest with
              | rejected r => simp only [hrest] at h; exact nomatch h
              | ok finalPair =>
                  obtain ⟨final', restObs⟩ := finalPair
                  simp only [hrest] at h
                  cases h
                  rw [show applyStatement state (.openScope site) =
                      .ok (mid, []) by
                    simp [applyStatement, happ]] at wrest
                  exact .localStep
                    (by simp [applyStatement, happ])
                    (foldStatements_toLifecycle hrest wrest)
      | closeScope site =>
          cases happ : applyLocalPayload? .closeScope state with
          | none => simp only [applyStatement, happ] at h; exact nomatch h
          | some middle =>
              simp only [applyStatement, happ] at h
              cases hcomp : applyLocalPayload? .completeBlock middle with
              | none => simp only [hcomp] at h; exact nomatch h
              | some mid =>
                  simp only [hcomp] at h
                  cases hrest : foldStatements mid rest with
                  | rejected r => simp only [hrest] at h; exact nomatch h
                  | ok finalPair =>
                      obtain ⟨final', restObs⟩ := finalPair
                      simp only [hrest] at h
                      cases h
                      rw [show applyStatement state (.closeScope site) =
                          .ok (mid, []) by
                        simp [applyStatement, happ, hcomp]] at wrest
                      exact .localStep
                        (by simp [applyStatement, happ, hcomp])
                        (foldStatements_toLifecycle hrest wrest)
      | constDecl site names terminator =>
          cases happ : applyLocalPayload?
              (.declareConstants (names.map (·.name))) state with
          | none => simp only [applyStatement, happ] at h; exact nomatch h
          | some mid =>
              simp only [applyStatement, happ] at h
              cases hrest : foldStatements mid rest with
              | rejected r => simp only [hrest] at h; exact nomatch h
              | ok finalPair =>
                  obtain ⟨final', restObs⟩ := finalPair
                  simp only [hrest] at h
                  cases h
                  rw [show applyStatement state
                      (.constDecl site names terminator) =
                      .ok (mid, []) by
                    simp [applyStatement, happ]] at wrest
                  exact .localStep
                    (by simp [applyStatement, happ])
                    (foldStatements_toLifecycle hrest wrest)
      | varDecl site names terminator =>
          cases happ : applyLocalPayload?
              (.declareVariables (names.map (·.name))) state with
          | none => simp only [applyStatement, happ] at h; exact nomatch h
          | some mid =>
              simp only [applyStatement, happ] at h
              cases hrest : foldStatements mid rest with
              | rejected r => simp only [hrest] at h; exact nomatch h
              | ok finalPair =>
                  obtain ⟨final', restObs⟩ := finalPair
                  simp only [hrest] at h
                  cases h
                  rw [show applyStatement state
                      (.varDecl site names terminator) =
                      .ok (mid, []) by
                    simp [applyStatement, happ]] at wrest
                  exact .localStep
                    (by simp [applyStatement, happ])
                    (foldStatements_toLifecycle hrest wrest)
      | djDecl site names terminator =>
          cases happ : applyLocalPayload?
              (.declareDisjoint (names.map (·.name))) state with
          | none => simp only [applyStatement, happ] at h; exact nomatch h
          | some mid =>
              simp only [applyStatement, happ] at h
              cases hrest : foldStatements mid rest with
              | rejected r => simp only [hrest] at h; exact nomatch h
              | ok finalPair =>
                  obtain ⟨final', restObs⟩ := finalPair
                  simp only [hrest] at h
                  cases h
                  rw [show applyStatement state
                      (.djDecl site names terminator) =
                      .ok (mid, []) by
                    simp [applyStatement, happ]] at wrest
                  exact .localStep
                    (by simp [applyStatement, happ])
                    (foldStatements_toLifecycle hrest wrest)
      | floating site label typecode variableName terminator =>
          cases happ : applyLocalPayload?
              (.declareFloating label.name typecode.name
                variableName.name) state with
          | none => simp only [applyStatement, happ] at h; exact nomatch h
          | some mid =>
              simp only [applyStatement, happ] at h
              cases hrest : foldStatements mid rest with
              | rejected r => simp only [hrest] at h; exact nomatch h
              | ok finalPair =>
                  obtain ⟨final', restObs⟩ := finalPair
                  simp only [hrest] at h
                  cases h
                  rw [show applyStatement state
                      (.floating site label typecode variableName
                        terminator) =
                      .ok (mid, []) by
                    simp [applyStatement, happ]] at wrest
                  exact .localStep
                    (by simp [applyStatement, happ])
                    (foldStatements_toLifecycle hrest wrest)
      | essential site label typecode body terminator =>
          cases htag : tagBody state body with
          | rejected r =>
              simp only [applyStatement, htag] at h
              exact nomatch h
          | ok syms =>
              simp only [applyStatement, htag] at h
              cases happ : applyLocalPayload?
                  (.declareEssential label.name ⟨typecode.name, syms⟩)
                  state with
              | none => simp only [happ] at h; exact nomatch h
              | some mid =>
                  simp only [happ] at h
                  cases hrest : foldStatements mid rest with
                  | rejected r => simp only [hrest] at h; exact nomatch h
                  | ok finalPair =>
                      obtain ⟨final', restObs⟩ := finalPair
                      simp only [hrest] at h
                      cases h
                      rw [show applyStatement state
                          (.essential site label typecode body
                            terminator) =
                          .ok (mid, []) by
                        simp [applyStatement, htag, happ]] at wrest
                      exact .localStep
                        (by simp [applyStatement, htag, happ])
                        (foldStatements_toLifecycle hrest wrest)
      | axiomatic site label typecode body terminator =>
          cases htag : tagBody state body with
          | rejected r =>
              simp only [applyStatement, htag] at h
              exact nomatch h
          | ok syms =>
              simp only [applyStatement, htag] at h
              cases happ : applyLocalPayload?
                  (.declareAxiom label.name ⟨typecode.name, syms⟩)
                  state with
              | none => simp only [happ] at h; exact nomatch h
              | some mid =>
                  simp only [happ] at h
                  cases hrest : foldStatements mid rest with
                  | rejected r => simp only [hrest] at h; exact nomatch h
                  | ok finalPair =>
                      obtain ⟨final', restObs⟩ := finalPair
                      simp only [hrest] at h
                      cases h
                      rw [show applyStatement state
                          (.axiomatic site label typecode body
                            terminator) =
                          .ok (mid, []) by
                        simp [applyStatement, htag, happ]] at wrest
                      exact .localStep
                        (by simp [applyStatement, htag, happ])
                        (foldStatements_toLifecycle hrest wrest)

/-- **The discharge family is recoverable**: every whole-run lifecycle
yields its own thread of witnesses (the reverse of
`foldStatements_toLifecycle`; together with `LifecycleRun.toFold` the
run recovers both the fold result and the discharges). -/
def LifecycleRun.witnesses :
    ∀ {state final : SourceState} {statements : List RawStatement},
      LifecycleRun state statements final →
      RunWitnesses state statements
  | _, _, _, .nil _ => PUnit.unit
  | state, final, stmt :: rest, run => by
      cases run with
      | localStep happly tail =>
          refine ⟨?_, ?_⟩
          · cases stmt with
            | provable site label typecode body proof separator
                terminator =>
                exact absurd happly (fun happly' => by
                  obtain ⟨syms, htag, hins, hobs⟩ :=
                    applyStatement_provable_inv happly'
                  simp at hobs)
            | openScope site => exact PUnit.unit
            | closeScope site => exact PUnit.unit
            | constDecl site names terminator => exact PUnit.unit
            | varDecl site names terminator => exact PUnit.unit
            | djDecl site names terminator => exact PUnit.unit
            | floating site label typecode variableName terminator =>
                exact PUnit.unit
            | essential site label typecode body terminator =>
                exact PUnit.unit
            | axiomatic site label typecode body terminator =>
                exact PUnit.unit
          · rw [show applyStatement state stmt = .ok (_, []) from happly]
            exact tail.witnesses
      | @normalStep _ mid _ site label typecode body steps separator
          terminator _ syms htag step tail =>
          refine ⟨?_, ?_⟩
          · rw [show StepWitness state
                (.provable site label typecode body (.normal steps)
                  separator terminator) =
                (match tagBody state body with
                 | .ok syms =>
                     NormalDischarge state ⟨typecode.name, syms⟩
                       (steps.map (·.name))
                 | .rejected _ => PUnit) from rfl, htag]
            exact ⟨step.target, step.presentation_eq, step.tree,
              step.labels_eq⟩
          · rw [applyStatement_provable_of htag step.inserted]
            exact tail.witnesses
      | @compressedStep _ mid _ site label typecode body openParen
          closeParen header words separator terminator _ syms htag step
          tail =>
          refine ⟨?_, ?_⟩
          · rw [show StepWitness state
                (.provable site label typecode body
                  (.compressed openParen header closeParen words)
                  separator terminator) =
                (match tagBody state body with
                 | .ok syms =>
                     CompressedWitness state ⟨typecode.name, syms⟩
                       (header.map (·.name)) (words.map (·.bytes))
                 | .rejected _ => PUnit) from rfl, htag]
            exact
              { target := step.target
                presentation_eq := step.presentation_eq
                actions := step.actions
                decoded := step.decoded
                initialState := step.initialState
                finalState := step.finalState
                header := step.header
                execution := step.execution
                rootId := step.rootId
                root := step.root
                finalStack := step.finalStack
                rootLookup := step.rootLookup
                rootFormula := step.rootFormula }
          · rw [applyStatement_provable_of htag step.inserted]
            exact tail.witnesses

end Mettapedia.Languages.Metamath.SourceGSLTLifecycleComposition
