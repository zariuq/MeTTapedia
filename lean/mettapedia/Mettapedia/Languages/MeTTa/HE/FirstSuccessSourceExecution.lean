import Mettapedia.Languages.MeTTa.HE.FirstSuccessContinuationPaths
import Mettapedia.Languages.MeTTa.HE.FirstSuccessLeafEvaluation
import Mettapedia.Languages.MeTTa.HE.FirstSuccessSourceScan
import Mettapedia.Languages.MeTTa.HE.NativeArgumentControlHistory
import Mettapedia.Languages.MeTTa.HE.Spec.Bindings.ScopeObservation
import Mettapedia.Languages.MeTTa.HE.Spec.Match.StructuralModel
import Mettapedia.Languages.MeTTa.HE.EquationFreshening
import Mettapedia.Languages.MeTTa.HE.RetainedArgumentSpecification
import Mettapedia.Languages.MeTTa.HE.QueryBindingProjection
import Mettapedia.Languages.MeTTa.HE.EvaluatorBindingExtension
import Mettapedia.Languages.MeTTa.HE.RecursiveExecution
import Mettapedia.Machines.OrderedProtocol
open Mettapedia.Languages.MeTTa.HE.FirstSuccessContinuationPaths (AppendFrames BranchPlan FramedPath rawOutput checkedOutput)
open Mettapedia.Languages.MeTTa.HE.Spec.Match.SolutionTheory
open Mettapedia.Languages.MeTTa.HE.BindingComposition
open Mettapedia.Languages.MeTTa.HE.MatchSizeTheory
open Mettapedia.Languages.MeTTa.HE.Spec.Bindings.ScopeObservation.ModelTransport

/-!
# Scoped recursive source derivations through retained first-success execution

The admitted grammar combines independently checked closed type casts and
argument domains with recursive equation calls. Its source witnesses carry
physical query occurrences, hygienic instantiation, local matching and merging,
and binding materialization. Local leaf coverage earns a completed checked run
and completion from each saved scheduler pause. Closed type checks have
structural coverage bounds; general recursive matching retains its explicit
local coverage obligation. No whole-run completion premise is required.

Actual matching constructs independent occurrence evidence for finite
first-order patterns, including open queries and repeated variables. The record
observer retains the historical reader's equality-free normal-caller admission.
The semantic observer keeps one independently certified finite table in the
source frame and agrees with every covered checkpoint read. It admits normal
store views with bare aliases. Matching and equation updates expose those
aliases as equalities at their local merge boundary; successful reconciliation
earns the next complete certificate. One table reads every present and future
operand, while stronger output shape facts are proved for the admitted operation.

Coverage of the actual equation frontier now constructs its source evidence
for every row, including open nonlinear inputs. Each physical occurrence earns
a selected renewal and one absorption law for the complete pending tuple.
Producer and return children remain independent source derivations.

Recursive bodies retain changed bindings, selected tables and live scope.
The independent evaluator join preserves every returned atom and physical
occurrence. Its two binding comparisons are relation-list permutation and
complete solution theory with exact freshness support. The latter transports
the actual binding-machine representative through the chosen checkpoint table.
It constructs selected-source witnesses; it does not assert that every other
certified source choice is made by Rust or C, nor that literal string observers
are invariant under a residual renaming. Closed total-cast failure contributes
one error per physical type occurrence.
Mixed argument continuation laws retain changed failures without running their
tails, and preserve actual binding endpoints through the independent success
and failure histories. The earlier equation-free, read-only grammar embeds
into this one. Exact occurrence lists describe this worker's delivery policy.

The same mutual admission family covers selected-frame minimal data, successful
or genuinely unmatched unify, cons/decons, and recursive function bodies. Each
successful unify constructs its next source frame from the actual match, exposed
merge and retained structural-cycle filter. The independent match, finite model
and complete output readout are proved from those operations. Body rows
retain their own bindings and are read before the next instruction is chosen.
The ordinary embedded-call branch composes that actual invocation with its
existing typed return receiver; raw refusal and ordinary restoration remain
distinct. Emitted and completed producer provenance is explicit.

Equation admission separates actual query occurrences and materialized inputs
from emitted producer execution and typed return. Function-producing equations
run their actual bodies before the ordinary receiver resumes at each reached
frame. The ordered composition retains candidate, input and producer occurrence
coordinates; ordinary nonfunction equations are its proved specialization.

Raw eval and structural chain now reuse the same raw invocation, emitted
producer and minimal continuations. Each query retains its physical equation
occurrence and actual merge/read coverage; each chain reads the reached child
frame, substitutes its explicit binder in saved syntax, then resumes under the
original live scope and caller. Internal Empty and NotReducible are retained.
No-match refusal requires independent query absence and covered actual reads.
The ordinary untyped tuple path uses an actual singleton Undefined lookup,
tuple-specific live scopes and stopping rules, and recursive call children.
Its ordered replies retain changed bindings and duplicate equation occurrences.
General failed-arrow fallback, polymorphic first-binding coverage, remaining
minimal host operations and host/world effects remain separate boundaries.
Operator coverage still requires an admitted call child; the tuple syntax does
not supply that evidence. Raw syntax demand holds programs as data. No effectful
host adequacy is claimed by this read-only-space worker.

-/

open Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation.BindingTheory (aliasConstraints)

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Spec.Type.Presentation Spec.Type.Presentation.Theory Spec.Type.RuntimeRefinement
open Spec.Type.Presentation.BindingTheory
open Spec.Bindings.ScopeObservation Spec.Match.ModelTheory

namespace BindingSourceAgreement


theorem queryVisible_iff {left right : Bindings} (related : BindingSourceAgreement left right)
    (live : List Atom) (query : Atom) (name : String) :
    Spec.Eval.Steps.QueryVisibleName live query left name ↔
      Spec.Eval.Steps.QueryVisibleName live query right name := by
  rw [EquationScope.queryVisible_support_iff,EquationScope.queryVisible_support_iff,related.support]

theorem alphaVariant_iff {incoming other : Bindings} (related : BindingSourceAgreement incoming other)
    (live : List Atom) (query left right freshLeft freshRight : Atom) :
    Spec.Eval.Steps.AlphaVariantRel live query incoming left right freshLeft freshRight ↔
      Spec.Eval.Steps.AlphaVariantRel live query other left right freshLeft freshRight := by
  simp only [Spec.Eval.Steps.AlphaVariantRel,related.queryVisible_iff]

theorem noMatch {incoming other : Bindings} (related : BindingSourceAgreement incoming other)
    (space : Space) (live : List Atom) (query : Atom)
    (absent : Spec.Eval.Steps.EquationQueryNoMatchRel space live query incoming) :
    Spec.Eval.Steps.EquationQueryNoMatchRel space live query other := by
  intro freshLeft freshRight matched rule
  obtain ⟨left,right,stored,alpha,matching⟩ := rule
  exact absent freshLeft freshRight matched
    ⟨left,right,stored,(related.alphaVariant_iff live query left right freshLeft freshRight).mpr alpha,matching⟩

/-- Failure of a satisfiable match-and-caller conjunction is independent of
the binding record's presentation. The same match and common valuation
construct the contradictory candidate in the other presentation. -/
theorem unifyNoMatch {incoming other : Bindings} (related : BindingSourceAgreement incoming other)
    {target pattern : Atom}
    (absent : Spec.Eval.Steps.UnifyNoMatchRel target pattern incoming) :
    Spec.Eval.Steps.UnifyNoMatchRel target pattern other := by
  rintro output ⟨matched,matching,merged⟩
  obtain ⟨valuation,matchedModel,callerModel⟩ := merged.common_model
  exact absent _ ⟨matched,matching,Spec.Bindings.ScopeObservation.LogicalMergeRel.append_of_common_model
    ⟨valuation,matchedModel,(related.solutions valuation).mpr callerModel⟩⟩

end BindingSourceAgreement

/-- Admission of an actual retained binding record for executable readout.
The invariant belongs to the runtime record; independent source presentations
need not have a canonical resolver. -/
structure PrincipalBindingFrame (bindings : Bindings) : Prop where
  loopFree : Spec.Match.Merge.SemanticLoopFree bindings
  nonvariable : AssignmentsNonVariable bindings
  coherent : CanonicalClassCoherent bindings loopFree nonvariable

theorem PrincipalBindingFrame.model {bindings : Bindings}
    (frame : PrincipalBindingFrame bindings) :
    ∃ valuation, TypeBindingSatisfied valuation bindings :=
  ⟨_, QueryBindingProjection.applyFull_typeBindingSatisfied
    frame.loopFree frame.nonvariable frame.coherent⟩

/-- The ordinary empty worker environment earns the invariant directly. -/
theorem PrincipalBindingFrame.empty : PrincipalBindingFrame Bindings.empty := by
  have loopFree : Spec.Match.Merge.SemanticLoopFree Bindings.empty :=
    (Spec.Match.Merge.hasLoop_eq_false_iff_semanticLoopFree _).mp (by decide)
  have nonvariable : AssignmentsNonVariable Bindings.empty := by
    intro key value present
    simp [Bindings.empty] at present
  refine ⟨loopFree,nonvariable,?_⟩
  apply Spec.Match.StructuralModel.canonicalClassCoherent_of_structurallySolved
  intro left right leftValue rightValue present
  simp [Bindings.empty] at present

/-- The independently certified table selected by the maintained binding
machine for this complete actual checkpoint. -/
def PrincipalBindingFrame.sourceFrame {bindings : Bindings}
    (principal : PrincipalBindingFrame bindings) : Spec.Eval.BindingFrame :=
  .selected bindings (QueryBindingProjection.nativeReadoutPresentation bindings)
    (QueryBindingProjection.nativeReadoutPresentation_certificate principal.loopFree
      principal.nonvariable principal.coherent (fun _ => Iff.rfl))

/-- The admission proof may retain the stronger record observer or use the
constructed full-theory observer. Both are comparisons of the same worker. -/
inductive SourceBindingComparison where
  | records
  | semantic

def SourceBindingComparison.Related : SourceBindingComparison → Bindings → Bindings → Prop
  | .records, left, right => BindingRecordPerm left right
  | .semantic, left, right => BindingSourceAgreement left right

theorem SourceBindingComparison.noMatch (comparison : SourceBindingComparison)
    {incoming other : Bindings} (related : comparison.Related incoming other)
    (space : Space) (live : List Atom) (query : Atom)
    (absent : Spec.Eval.Steps.EquationQueryNoMatchRel space live query incoming) :
    Spec.Eval.Steps.EquationQueryNoMatchRel space live query other := by
  cases comparison with
  | records => exact (BindingSourceAgreement.of_recordPerm related).noMatch space live query absent
  | semantic => exact related.noMatch space live query absent

/-- The historical mode keeps record permutation. The semantic mode keeps
complete constraint/support agreement, one independently certified table,
and its agreement with every covered read of the actual checkpoint.
Operation-specific matching or merging shape is not representation evidence. -/
inductive SourceBindingComparison.FrameRelated :
    SourceBindingComparison → Bindings → Spec.Eval.BindingFrame → Prop where
  | records {native source : Bindings} (related : BindingRecordPerm native source) :
      FrameRelated .records native (.historical source)
  | semantic {native source : Bindings} {table : TypeSubst}
      (agreement : BindingSourceAgreement native source)
      (certificate : ReadoutCertificate source table)
      (coveredRead : ∀ atom depth, native.applyFullCovered atom depth = true →
        native.applyFull atom depth = table.apply atom) :
      FrameRelated .semantic native (.selected source table certificate)

namespace SourceBindingComparison.FrameRelated

/-- Both admitted observers retain the whole independent binding theory. -/
theorem agreement {comparison : SourceBindingComparison} {native : Bindings}
    {frame : Spec.Eval.BindingFrame} (witness : comparison.FrameRelated native frame) :
    BindingSourceAgreement native frame.bindings := by
  cases witness with
  | records related => exact BindingSourceAgreement.of_recordPerm related
  | semantic agreement _ _ => exact agreement

theorem related {comparison : SourceBindingComparison} {native : Bindings}
    {frame : Spec.Eval.BindingFrame} (witness : comparison.FrameRelated native frame) :
    comparison.Related native frame.bindings := by
  cases witness with
  | records related => exact related
  | semantic agreement _ _ => exact agreement

/-- Renewal is used alongside a real source operation; representation alone
does not assert that the operation exists or preserves the previous theory. -/
theorem renew {comparison : SourceBindingComparison} {before after : Bindings}
    {input output : Spec.Eval.BindingFrame}
    (first : comparison.FrameRelated before input)
    (next : comparison.FrameRelated after output) :
    Spec.Eval.BindingFrame.Update .renew input output := by
  cases first <;> cases next
  · exact .historical _ _
  · exact .selected _ _

theorem historical {native source : Bindings}
    (related : BindingRecordPerm native source) :
    SourceBindingComparison.records.FrameRelated native source := .records related

theorem refl (bindings : Bindings) :
    SourceBindingComparison.records.FrameRelated bindings bindings := .records (.refl _)

theorem historical_eq {native : Bindings} {frame : Spec.Eval.BindingFrame}
    (related : SourceBindingComparison.records.FrameRelated native frame) :
    frame = Spec.Eval.BindingFrame.historical frame.bindings := by
  cases related
  rfl

theorem noMatch {comparison : SourceBindingComparison} {native : Bindings}
    {frame : Spec.Eval.BindingFrame} (related : comparison.FrameRelated native frame)
    (space : Space) (live : List Atom) (query : Atom)
    (absent : Spec.Eval.Steps.EquationQueryNoMatchRel space live query native) :
    Spec.Eval.Steps.EquationQueryNoMatchRel space live query frame.bindings :=
  comparison.noMatch related.related space live query absent

/-- Every covered operand is read through the checkpoint's same table. -/
theorem materialization {native : Bindings} {frame : Spec.Eval.BindingFrame}
    (related : SourceBindingComparison.semantic.FrameRelated native frame)
    (atom : Atom) (fuel : Nat) (covered : native.applyFullCovered atom fuel = true) :
    frame.Materialization atom (native.applyFull atom fuel) := by
  cases related with
  | semantic _ _ reads => exact reads atom fuel covered

theorem materialization_of_forced {native : Bindings} {frame : Spec.Eval.BindingFrame}
    (related : SourceBindingComparison.semantic.FrameRelated native frame)
    (atom value : Atom)
    (forced : ∀ valuation, TypeBindingSatisfied valuation frame.bindings →
      applyTypeValuation valuation atom = value) :
    frame.Materialization atom value := by
  cases related with
  | semantic _ certificate _ =>
    have model := (certificate.theory _).mp
      (normal_presentedValuation_satisfied certificate.normal)
    have read := forced _ model
    rw [applyTypeValuation_presented_eq_apply] at read
    exact read.symm

theorem selected_readout {native : Bindings} {frame : Spec.Eval.BindingFrame}
    (related : SourceBindingComparison.semantic.FrameRelated native frame) :
    ∃ table, ∃ certificate : ReadoutCertificate frame.bindings table,
      frame = .selected frame.bindings table certificate ∧
      ∀ atom depth, native.applyFullCovered atom depth = true →
        native.applyFull atom depth = table.apply atom := by
  cases related with
  | semantic _ certificate reads => exact ⟨_, certificate, rfl, reads⟩

theorem source_model {native : Bindings} {frame : Spec.Eval.BindingFrame}
    (related : SourceBindingComparison.semantic.FrameRelated native frame) :
    ∃ valuation, TypeBindingSatisfied valuation frame.bindings := by
  cases related with
  | semantic _ certificate _ => exact certificate.satisfiable

theorem model {native : Bindings} {frame : Spec.Eval.BindingFrame}
    (related : SourceBindingComparison.semantic.FrameRelated native frame) :
    ∃ valuation, TypeBindingSatisfied valuation native := by
  obtain ⟨valuation, satisfied⟩ := related.source_model
  exact ⟨valuation, (related.related.solutions valuation).mpr satisfied⟩

/-- The earlier native resolver invariant constructs this representation as
a sufficient instance. It is not required of every source presentation. -/
theorem of_principal {native source : Bindings}
    (principal : PrincipalBindingFrame native)
    (agreement : BindingSourceAgreement native source) :
    SourceBindingComparison.semantic.FrameRelated native (.selected source
      (QueryBindingProjection.nativeReadoutPresentation native)
      (QueryBindingProjection.nativeReadoutPresentation_certificate principal.loopFree
        principal.nonvariable principal.coherent agreement.solutions)) :=
  .semantic agreement
    (QueryBindingProjection.nativeReadoutPresentation_certificate principal.loopFree
      principal.nonvariable principal.coherent agreement.solutions)
    (fun atom depth covered => (QueryBindingProjection.nativeReadoutPresentation_apply
      principal.loopFree principal.nonvariable principal.coherent atom depth covered).symm)

/-- Unique actual equations and their actual finite-cycle check earn both
the normalized table and the complete selected-frame representation. -/
theorem normalized {entries : TypeSubst} (unique : entries.keys.Nodup)
    (checked : Bindings.hasLoop ⟨entries, []⟩ = false) :
    SourceBindingComparison.semantic.FrameRelated
      (FirstSuccessPreparedArguments.presentedBindings
        (BindingTheory.CurrentStore.normalize entries))
      (.selected ⟨entries, []⟩ (BindingTheory.CurrentStore.normalize entries)
        (BindingTheory.CurrentStore.normalize_certified_of_noLoop unique checked)) := by
  have certificate := BindingTheory.CurrentStore.normalize_certified_of_noLoop unique checked
  apply semantic (certificate := certificate)
  · refine ⟨?_, BindingTheory.CurrentStore.normalize_support unique⟩
    intro valuation
    simpa only [FirstSuccessPreparedArguments.presentedBindings, TypeBindingSatisfied,
      List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true, TypeSubstSatisfied] using
      certificate.theory valuation
  · exact FirstSuccessPreparedArguments.applyFull_presented_of_covered certificate.normal

/-- Scoped preparation reads the current generational store, then the actual
cycle check constructs its certificate. No expected table/model is an input. -/
theorem prepared {globals : List String}
    {image : MetavariableFrameStore.Shared.ImageOf BindingTheory.CurrentStore.ContextualOperand}
    {operands : List BindingTheory.CurrentStore.ContextualOperand}
    {snapshot : List BindingTheory.CurrentStore.Row} {qualified : List Atom}
    (prepared : BindingTheory.CurrentStore.prepareScoped? globals image operands =
      some (snapshot, qualified))
    (checked : Bindings.hasLoop ⟨BindingTheory.CurrentStore.assignments snapshot, []⟩ = false) :
    SourceBindingComparison.semantic.FrameRelated
      (FirstSuccessPreparedArguments.presentedBindings
        (BindingTheory.CurrentStore.normalize (BindingTheory.CurrentStore.assignments snapshot)))
      (.selected ⟨BindingTheory.CurrentStore.assignments snapshot, []⟩
        (BindingTheory.CurrentStore.normalize (BindingTheory.CurrentStore.assignments snapshot))
        (BindingTheory.CurrentStore.prepareScoped?_certified_of_noLoop prepared checked)) :=
  normalized
    (BindingTheory.CurrentStore.assignments_unique
      (BindingTheory.CurrentStore.contextualRows?_unique
        (BindingTheory.CurrentStore.prepare?_components
          (BindingTheory.CurrentStore.prepareScoped?_success prepared)).1)) checked

/-- One covered tuple read preserves repeated uses and held call syntax. -/
theorem pending {native source : Bindings} {table : TypeSubst}
    {certificate : ReadoutCertificate source table}
    (related : SourceBindingComparison.semantic.FrameRelated native
      (.selected source table certificate)) (pending : List Atom) (depth : Nat)
    (covered : native.applyFullCovered (.expression pending) depth = true) :
    native.applyFull (.expression pending) depth = .expression (pending.map table.apply) := by
  simpa only [Spec.Eval.BindingFrame.materialization_selected, TypeSubst.apply] using
    related.materialization (.expression pending) depth covered

/-- If an actual operation strengthens the complete source theory, its
later representation absorbs the old read of the entire pending tuple.
Each worker read uses its own actual coverage evidence. -/
theorem pending_absorbed {before after : Bindings} {input output : Spec.Eval.BindingFrame}
    (old : SourceBindingComparison.semantic.FrameRelated before input)
    (next : SourceBindingComparison.semantic.FrameRelated after output)
    (extension : ∀ valuation, TypeBindingSatisfied valuation output.bindings →
      TypeBindingSatisfied valuation input.bindings)
    (pending : List Atom) (firstDepth laterDepth directDepth : Nat)
    (firstCovered : before.applyFullCovered (.expression pending) firstDepth = true)
    (laterCovered : after.applyFullCovered
      (before.applyFull (.expression pending) firstDepth) laterDepth = true)
    (directCovered : after.applyFullCovered (.expression pending) directDepth = true) :
    after.applyFull (before.applyFull (.expression pending) firstDepth) laterDepth =
      after.applyFull (.expression pending) directDepth := by
  cases old with
  | semantic _ oldCertificate oldReads =>
    cases next with
    | semantic _ nextCertificate nextReads =>
      rw [nextReads _ _ laterCovered, nextReads _ _ directCovered,
        oldReads _ _ firstCovered]
      exact oldCertificate.absorbs nextCertificate extension _

/-- The selected certificate supplies one historical principal fold and
one inverse residual permutation, shared by all operands and all covered
depths. This does not assert literal agreement of representative names. -/
theorem historical_readout {native : Bindings} {frame : Spec.Eval.BindingFrame}
    (related : SourceBindingComparison.semantic.FrameRelated native frame) :
    ∃ folded : TypeSubst, ∃ permutation : Equiv.Perm String,
      EquationListPresentationRel (BindingTheory.bindingAtomEquations frame.bindings) [] folded ∧
      (∀ name, name ∉ specBindingVars frame.bindings → permutation name = name) ∧
      ∀ atom depth, native.applyFullCovered atom depth = true →
        folded.apply atom = renameTypeVars permutation (native.applyFull atom depth) := by
  cases related with
  | semantic _ certificate reads =>
    obtain ⟨folded, choice, fold, fixed, outside, allAtoms⟩ := certificate.representative
    refine ⟨folded, choice.symm, fold, ?_, ?_⟩
    · intro name absent
      apply choice.injective
      rw [choice.apply_symm_apply, outside name absent]
    · intro atom depth covered
      rw [reads atom depth covered, allAtoms atom,
        (fold.model_fixed_representative choice fixed).2.2 atom,
        renameTypeVars_perm_inverse]

/-- All pending operands have one historical source observation modulo the
same residual renaming, retaining shared variables between their positions. -/
theorem joint_observation {native : Bindings} {frame : Spec.Eval.BindingFrame}
    (related : SourceBindingComparison.semantic.FrameRelated native frame)
    (pending : List Atom) (depth : Nat)
    (covered : native.applyFullCovered (.expression pending) depth = true) :
    ∃ normalized : Atom, ∃ permutation : Equiv.Perm String,
      BindingTheory.BindingMaterializationRel frame.bindings (.expression pending) normalized ∧
      normalized = renameTypeVars permutation (native.applyFull (.expression pending) depth) := by
  obtain ⟨folded, permutation, fold, _outside, reads⟩ := related.historical_readout
  exact ⟨folded.apply (.expression pending), permutation, ⟨folded, fold, rfl⟩,
    reads _ depth covered⟩

end SourceBindingComparison.FrameRelated

end Mettapedia.Languages.MeTTa.HE

namespace Mettapedia.Languages.MeTTa.HE.FirstSuccessSourceExecution

open Mettapedia.Languages.MeTTa.OSLFCore (Atom GroundedValue)
open Spec.Eval Spec.Type Spec.Type.Presentation
open Spec.Bindings.ScopeObservation (BindingRecordPerm)
open RecursiveTasks FirstSuccessRecursiveExecution FirstSuccessRawExecution
open FirstSuccessLeafEvaluation FirstSuccessSourceApplicability FirstSuccessSourceScan
open Mettapedia.GSLT.Distinction.ProductiveBlocks

attribute [local simp] Atom.atomType Atom.undefinedType Atom.symbolType Atom.variableType
  Atom.groundedType Atom.expressionType

/-- This profile has no host operations. That restriction is independent of
whether a syntax value is executable in any other runtime profile. -/
def noHost : Spec.Eval.GroundedDispatch where
  executable := fun _ => False
  outcome := fun _ _ _ => False

/-- The space itself contains no equation declarations. -/
def EquationFree (space : Space) : Prop :=
  ∀ left right, .expression [.symbol "=", left, right] ∉ space.atoms

theorem no_source_equations (space : Space) (free : EquationFree space)
    (value : Atom) (fuel : Nat) : queryEquations space value fuel = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro result member
  obtain ⟨left, right, index, declared, _, _⟩ := queryEquations_matchAtoms_witness member
  exact free left right (List.fst_mem_of_mem_zipIdx declared)

theorem no_scoped_source_equations (space : Space) (free : EquationFree space)
    (avoid : List String) (value : Atom) (fuel : Nat) :
    queryEquationsAvoiding avoid space value fuel = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro result member
  obtain ⟨left, right, index, declared, _, _⟩ := queryEquationsAvoiding_matchAtoms_witness member
  exact free left right (List.fst_mem_of_mem_zipIdx declared)

theorem no_independent_equations (space : Space) (free : EquationFree space)
    (live : List Atom) (value : Atom) (bindings : Bindings) :
    Spec.Eval.Steps.EquationQueryNoMatchRel space live value bindings := by
  intro freshLeft freshRight matched rule
  obtain ⟨left, right, declared, _⟩ := rule
  exact free left right declared

/-- Ordered replies with one unchanged binding frame. The list retains
occurrences even when their values and bindings coincide. -/
def replies (bindings : Bindings) (values : List Atom) : ResultSet :=
  values.map fun value => (value, bindings)

def packets (bindings : Bindings) (values : List (List Atom)) : ResultSet :=
  replies bindings (values.map argumentPacket)

/-- The exact arrow supplied by a checked argument/return presentation. -/
def arrow (domains : List Atom) (returned : Atom) : Atom :=
  .expression (.symbol "->" :: (domains ++ [returned]))

def selectedPolicy (domains : List Atom) (returned : Atom) : SelectedTypePolicy :=
  ⟨arrow domains returned, domains, returned, rfl⟩

/-- One admitted source application. Every type-side field is syntax,
lookup or an independently checked rejection/fit condition. No machine
correspondence or evaluator result is assumed. -/
structure ApplicationTyping (space : Space) (name : String) (arguments : List Atom)
    (expected : Atom) (fuel : Nat) where
  domains : List Atom
  returned : Atom
  before : List Atom
  after : List Atom
  declined : List NativeSelectedTypeScan.Candidate
  sourceTypes : getAtomTypes space (.symbol name) = before ++ arrow domains returned :: after
  rejected : RejectedPrefix space fuel (.symbol name) expected arguments before declined
  argumentChecks : List.Forall₂ (fun argument domain =>
    ArgumentDomainEvidence space argument domain fuel) arguments domains
  argumentPaths : 0 < admittedPathCount space arguments domains
  expectedClosed : TypeSubst.typeVars expected = []
  returnedClosed : TypeSubst.typeVars returned = []
  returnedFits : ClosedTypeFits expected returned
  returnBudget : sizeOf expected + sizeOf returned + 2 ≤ fuel
  earlierClosed : ∀ candidate ∈ before, TypeSubst.typeVars candidate = []
  earlierHeadRejects : ∀ candidate ∈ before, ¬ClosedTypeFits (arrow domains returned) candidate
  headClosed : TypeSubst.typeVars (arrow domains returned) = []
  headBudget : sizeOf (arrow domains returned) + sizeOf (arrow domains returned) + 2 < fuel
  demandNotRaw : expected ≠ Atom.atomType
  demandNotExpression : expected ≠ Atom.expressionType
  nonemptyOperator : name ≠ "Empty"
  cleanOperator : name ≠ "Error"


/-- A singleton declared arrow supplies pure typing evidence. Invocation is
licensed separately by the actual call derivation at the selected demand. -/
def ApplicationTyping.single_arrow
    (space : Space) (name : String) (arguments domains : List Atom)
    (expected returned : Atom) (fuel : Nat)
    (types : getAtomTypes space (.symbol name) = [arrow domains returned])
    (checked : List.Forall₂ (fun argument domain =>
      ArgumentDomainEvidence space argument domain fuel) arguments domains)
    (positive : 0 < admittedPathCount space arguments domains)
    (expectedClosed : TypeSubst.typeVars expected = [])
    (returnedClosed : TypeSubst.typeVars returned = [])
    (fits : ClosedTypeFits expected returned)
    (returnBudget : sizeOf expected + sizeOf returned + 2 ≤ fuel)
    (headClosed : TypeSubst.typeVars (arrow domains returned) = [])
    (headBudget : sizeOf (arrow domains returned) + sizeOf (arrow domains returned) + 2 < fuel)
    (notRaw : expected ≠ Atom.atomType) (notExpression : expected ≠ Atom.expressionType)
    (notEmpty : name ≠ "Empty") (notError : name ≠ "Error") :
    ApplicationTyping space name arguments expected fuel where
  domains := domains
  returned := returned
  before := []
  after := []
  declined := []
  sourceTypes := types
  rejected := .nil
  argumentChecks := checked
  argumentPaths := positive
  expectedClosed := expectedClosed
  returnedClosed := returnedClosed
  returnedFits := fits
  returnBudget := returnBudget
  earlierClosed := by simp
  earlierHeadRejects := by simp
  headClosed := headClosed
  headBudget := headBudget
  demandNotRaw := notRaw
  demandNotExpression := notExpression
  nonemptyOperator := notEmpty
  cleanOperator := notError

mutual
/-- A derivation carries exact ordered occurrences in addition to the
published singular evaluator judgment. Recursive children are source
derivations; callers cannot supply an assumed worker realization. -/
inductive ReadOnlyAtomDerivation (space : Space) (bindings : Bindings) :
    Atom → Atom → Nat → List Atom → Prop where
  | leaf (value expected : Atom) (fuel : Nat) :
      LeafRel value expected → ReadOnlyAtomDerivation space bindings value expected (fuel + 1) [value]
  | symbolCast (name : String) (expected : Atom) (fuel : Nat)
      (before after : List Atom) (actual : Atom) :
      name ≠ "Empty" → expected ≠ Atom.atomType → expected ≠ Atom.symbolType →
      getAtomTypes space (.symbol name) = before ++ actual :: after →
      TypeSubst.typeVars expected = [] → TypeSubst.typeVars actual = [] →
      (∀ candidate ∈ before, TypeSubst.typeVars candidate = []) →
      (∀ candidate ∈ before, ¬ClosedTypeFits expected candidate) →
      ClosedTypeFits expected actual → sizeOf expected + sizeOf actual + 2 ≤ fuel →
      ReadOnlyAtomDerivation space bindings (.symbol name) expected (fuel + 1) [.symbol name]
  | application (name : String) (arguments : List Atom) (expected : Atom) (fuel : Nat)
      (typing : ApplicationTyping space name arguments expected fuel) (values : List (List Atom)) :
      name ≠ "unify" ∧ name ≠ "switch-minimal" →
      Spec.Eval.Minimal.embeddedInstruction (.expression [.symbol name]) = false →
      ReadOnlyArgsDerivation space bindings arguments typing.domains fuel values →
      ReadOnlyAtomDerivation space bindings (.expression (.symbol name :: arguments)) expected (fuel + 3)
        (values.map fun packet => .expression (.symbol name :: packet))

inductive ReadOnlyArgsDerivation (space : Space) (bindings : Bindings) :
    List Atom → List Atom → Nat → List (List Atom) → Prop where
  | nil (fuel : Nat) : ReadOnlyArgsDerivation space bindings [] [] (fuel + 1) [[]]
  | cons (value expected : Atom) (values types : List Atom) (fuel : Nat)
      (heads : List Atom) (tails : List (List Atom)) :
      ReadOnlyAtomDerivation space bindings value expected fuel heads →
      ReadOnlyArgsDerivation space bindings values types fuel tails →
      ReadOnlyArgsDerivation space bindings (value :: values) (expected :: types) (fuel + 1)
        (heads.flatMap fun head => tails.map fun tail => head :: tail)
end

abbrev Realizes (space : Space) (task : Task) (results : ResultSet) : Prop :=
  ∀ stack emitted, SilentPath HE.GroundedDispatch.none
    ⟨space, .work task, stack, emitted⟩ ⟨space, .returning results, stack, emitted⟩

private theorem appendFrames (space : Space) :
    AppendFrames (FirstSuccessRecursiveExecution.machine HE.GroundedDispatch.none).reading.silent space where
  resumeTail rest head := by
    intro stack emitted
    simpa only [RecursiveMachine.resume, List.cons_append, List.nil_append] using
      consume_continuation space HE.GroundedDispatch.none (.append rest) head stack emitted
  restoreHead head tail := by
    intro stack emitted
    simpa only [RecursiveMachine.resume, List.cons_append, List.nil_append] using
      consume_continuation space HE.GroundedDispatch.none (.prepend head) tail stack emitted

theorem append_results (space : Space) (remaining : Task) (first second : ResultSet)
    (tail : Realizes space remaining second) (stack : List Frame) (emitted : ResultSet) :
    SilentPath HE.GroundedDispatch.none
      ⟨space, .returning first, .append remaining :: stack, emitted⟩
      ⟨space, .returning (first ++ second), stack, emitted⟩ := by
  exact (appendFrames space).collect remaining first second tail stack emitted

/-- Each recursive body keeps its own input and output bindings. The actual
`atoms` task evaluates the requests under the saved caller stack and appends
their full occurrence lists, including equal requests and equal replies. -/
theorem atoms_realizes (space : Space) (expected : Atom) (fuel : Nat) (live : List Atom)
    {requests : ResultSet} {outputs : List ResultSet}
    (children : List.Forall₂ (fun request output =>
      Realizes space (.atom request.1 expected request.2 fuel live) output) requests outputs) :
    Realizes space (.atoms expected fuel requests live) outputs.flatten := by
  refine (appendFrames space).traverseTasks
    (fun requests => Task.atoms expected fuel requests live)
    (fun request => Task.atom request.1 expected request.2 fuel live) ?_ ?_ children
  · intro stack emitted
    exact enter_request space HE.GroundedDispatch.none (Task.atoms expected fuel [] live) stack emitted
  · rintro ⟨value, bindings⟩ rest stack emitted
    exact enter_request space HE.GroundedDispatch.none (Task.atoms expected fuel (⟨value, bindings⟩ :: rest) live)
      stack emitted

/-- Ordinary refusal restores the retained original call, even at zero
remaining evaluator depth. This administrative return does not re-evaluate it. -/
theorem returned_notReducible_realizes (space : Space) (original expected : Atom)
    (bindings : Bindings) (fuel : Nat) (live : List Atom) :
    Realizes space (.returned original Atom.notReducible expected bindings fuel live)
      [(original, bindings)] := by
  intro stack emitted
  simpa [FirstSuccessRecursiveStrategy.enter, RecursiveMachine.enter] using
    enter_request space HE.GroundedDispatch.none
      (.returned original Atom.notReducible expected bindings fuel live) stack emitted

theorem returned_stopped_realizes (space : Space) (original value expected : Atom)
    (bindings : Bindings) (fuel : Nat) (live : List Atom)
    (stopped : isEmptyOrError value = true) :
    Realizes space (.returned original value expected bindings fuel live) [(value, bindings)] := by
  have accepted : value ≠ Atom.notReducible := by
    rintro rfl
    simp [isEmptyOrError, isEmptyAtom, isErrorAtom, Atom.notReducible, Atom.empty] at stopped
  intro stack emitted
  simpa [FirstSuccessRecursiveStrategy.enter, RecursiveMachine.enter, accepted, stopped] using
    enter_request space HE.GroundedDispatch.none
      (.returned original value expected bindings fuel live) stack emitted

theorem returned_evaluate_realizes (space : Space) (original value expected : Atom)
    (bindings : Bindings) (fuel : Nat) (live : List Atom) (results : ResultSet)
    (accepted : value ≠ Atom.notReducible) (running : isEmptyOrError value = false)
    (child : Realizes space (.atom value expected bindings fuel live) results) :
    Realizes space (.returned original value expected bindings fuel live) results := by
  intro stack emitted
  have entered := enter_request space HE.GroundedDispatch.none
    (.returned original value expected bindings fuel live) stack emitted
  apply entered.trans
  simpa [FirstSuccessRecursiveStrategy.enter, RecursiveMachine.enter, accepted, running] using
    child stack emitted

theorem returns_realizes (space : Space) (original expected : Atom) (fuel : Nat) (live : List Atom)
    {requests : ResultSet} {outputs : List ResultSet}
    (children : List.Forall₂ (fun request output =>
      Realizes space (.returned original request.1 expected request.2 fuel live) output) requests outputs) :
    Realizes space (.returns original expected fuel requests live) outputs.flatten := by
  refine (appendFrames space).traverseTasks
    (fun requests => Task.returns original expected fuel requests live)
    (fun request => Task.returned original request.1 expected request.2 fuel live) ?_ ?_ children
  · intro stack emitted
    exact enter_request space HE.GroundedDispatch.none (Task.returns original expected fuel [] live) stack emitted
  · rintro ⟨value, bindings⟩ rest stack emitted
    exact enter_request space HE.GroundedDispatch.none (Task.returns original expected fuel (⟨value, bindings⟩ :: rest) live)
      stack emitted

/-- The retained equation instruction prepares actual merged binding states.
This is its input representation, not an independent equation semantics. -/
def equationInputs (incoming : Bindings) (fuel : Nat) (candidate : ResultPair) : ResultSet :=
  (mergeBindings candidate.2 (aliasConstraints incoming) fuel).filterMap fun merged =>
    if merged.hasLoop then none else some (merged.applyFull candidate.1 fuel, merged)

/-- Preparing one equality-matched query item preserves its unitary choice.
Loop rejection and materialization cannot duplicate that source occurrence. -/
theorem equationInputs_length_le_one (incoming : Bindings) (fuel : Nat) (candidate : ResultPair) :
    (equationInputs incoming fuel candidate).length ≤ 1 :=
  (List.length_filterMap_le _ _).trans (mergeBindings_length_le_one _ _ _)

/-- Query preparation retains every surviving merge before any producer or
typed return continuation is entered. -/
theorem equations_read_realizes (space : Space) (original expected : Atom)
    (incoming : Bindings) (fuel : Nat) (live : List Atom) (candidates : ResultSet) :
    Realizes space (.equations original expected incoming fuel candidates live)
      (candidates.flatMap (equationInputs incoming fuel)) := by
  refine (appendFrames space).traverseMap
    (fun rows => .equations original expected incoming fuel rows live)
    (equationInputs incoming fuel) ?_ candidates ?_
  · intro stack emitted
    exact enter_request space HE.GroundedDispatch.none
      (.equations original expected incoming fuel [] live) stack emitted
  · rintro ⟨value, bindings⟩ _ rest stack emitted
    exact enter_request space HE.GroundedDispatch.none
      (.equations original expected incoming fuel (⟨value, bindings⟩ :: rest) live) stack emitted

theorem produced_ordinary_realizes (space : Space) (value : Atom) (bindings : Bindings)
    (fuel : Nat) (live : List Atom) (caller : Option Atom)
    (ordinary : ¬Spec.Eval.Minimal.IsFunction value) :
    Realizes space (.produced value bindings (fuel + 1) live caller) [(value, bindings)] := by
  intro stack emitted
  have expanded : FirstSuccessRecursiveStrategy.enter space GroundedDispatch.none
      (.produced value bindings (fuel + 1) live caller) =
        (.returning [(value, bindings)], []) := by
    simp only [FirstSuccessRecursiveStrategy.enter, RecursiveMachine.enter,
      show (InvocationProvenance.emitted == InvocationProvenance.completed) = false from rfl,
      Bool.false_eq_true, if_false]
    split
    · exact (ordinary ⟨_, rfl⟩).elim
    · rfl
  simpa only [expanded, List.nil_append] using
    enter_request space GroundedDispatch.none
      (.produced value bindings (fuel + 1) live caller) stack emitted

/-- Every physical row passes through its producer gate. This identity law
uses positive depth and independently recognized nonfunction syntax. -/
theorem productions_ordinary_realizes (space : Space) (fuel : Nat)
    (live : List Atom) (caller : Option Atom) (results : ResultSet)
    (ordinary : ∀ result ∈ results, ¬Spec.Eval.Minimal.IsFunction result.1) :
    Realizes space (.productions (fuel + 1) results live caller) results := by
  have children : List.Forall₂
      (fun request output => Realizes space
        (.produced request.1 request.2 (fuel + 1) live caller) output)
      results (results.map fun row => [row]) := by
    apply List.forall₂_map_right_iff.mpr
    apply List.forall₂_same.mpr
    intro row member
    exact produced_ordinary_realizes space row.1 row.2 fuel live caller (ordinary row member)
  have run := (appendFrames space).traverseTasks
      (fun requests => Task.productions (fuel + 1) requests live caller)
      (fun request => Task.produced request.1 request.2 (fuel + 1) live caller)
      (fun stack emitted => enter_request space HE.GroundedDispatch.none
        (.productions (fuel + 1) [] live caller) stack emitted)
      (by
        rintro ⟨value, bindings⟩ rest stack emitted
        exact enter_request space HE.GroundedDispatch.none
          (.productions (fuel + 1) (⟨value, bindings⟩ :: rest) live caller) stack emitted)
      children
  rw [← List.flatMap_def, List.flatMap_singleton'] at run
  exact run

theorem producer_ordinary_realizes (space : Space) (original expected : Atom)
    (incoming : Bindings) (fuel : Nat) (live : List Atom) (raw results : ResultSet)
    (present : raw ≠ [])
    (ordinary : ∀ result ∈ raw, ¬Spec.Eval.Minimal.IsFunction result.1)
    (body : Realizes space (.returns original expected (fuel + 1) raw live) results) :
    Realizes space (.producerResults (.ordinary expected) original incoming (fuel + 1)
      live Atom.notReducible raw) results := by
  intro stack emitted
  let returned := Frame.invocationReturn (.ordinary expected) original (fuel + 1) live
  have begin := enter_request space GroundedDispatch.none
    (.producerResults (.ordinary expected) original incoming (fuel + 1) live Atom.notReducible raw)
    stack emitted
  have production := productions_ordinary_realizes space fuel (expected :: live)
    (some original) raw ordinary (returned :: stack) emitted
  have resumed := consume_continuation space GroundedDispatch.none returned raw stack emitted
  have finish := body stack emitted
  apply begin.trans
  have nonempty := List.isEmpty_eq_false_iff.mpr present
  simpa only [FirstSuccessRecursiveStrategy.enter, RecursiveMachine.enter, nonempty,
    Bool.false_eq_true, if_false, InvocationMode.pendingScope, List.cons_append, List.nil_append,
    returned] using production.trans (resumed.trans (by
      simpa only [RecursiveMachine.resume, List.nil_append, returned] using finish))

theorem producer_refused_realizes (space : Space) (original expected : Atom)
    (incoming : Bindings) (fuel : Nat) (live : List Atom) :
    Realizes space (.producerResults (.ordinary expected) original incoming fuel
      live Atom.notReducible []) [(original, incoming)] := by
  intro stack emitted
  let returned := Frame.invocationReturn (.ordinary expected) original fuel live
  have begin := enter_request space GroundedDispatch.none
    (.producerResults (.ordinary expected) original incoming fuel live Atom.notReducible []) stack emitted
  have resumed := consume_continuation space GroundedDispatch.none returned
    [(Atom.notReducible, incoming)] stack emitted
  have children : List.Forall₂ (fun request output =>
      Realizes space (.returned original request.1 expected request.2 fuel live) output)
      [(Atom.notReducible, incoming)] [[(original, incoming)]] :=
    .cons (returned_notReducible_realizes space original expected incoming fuel live) .nil
  have finish := returns_realizes space original expected fuel live children stack emitted
  exact begin.trans (by
    simpa only [FirstSuccessRecursiveStrategy.enter, RecursiveMachine.enter,
      List.isEmpty_nil, if_true, List.cons_append, List.nil_append, returned] using
      resumed.trans (by simpa only [RecursiveMachine.resume, returned, List.nil_append,
        List.flatten_cons, List.flatten_nil, List.append_nil] using finish))

theorem classifier_agrees (value : Atom) :
    minimalInstruction value = Spec.Eval.Minimal.embeddedInstruction value := by
  cases value with
  | symbol _ | var _ | grounded _ => rfl
  | expression parts => cases parts with
    | nil => rfl
    | cons head tail => cases head <;> rfl

/-- A complete nonhost equation invocation first prepares all raw rows, then
enters the producer and ordinary-return continuations on that exact list. -/
theorem call_query_realizes (space : Space) (name : String) (arguments : List Atom)
    (expected : Atom) (incoming : Bindings) (fuel : Nat) (live : List Atom)
    (nonembedded : Spec.Eval.Minimal.embeddedInstruction (.expression [.symbol name]) = false)
    (clean : name ≠ "Error") (results : ResultSet)
    (body : Realizes space (.producerResults (.ordinary expected)
      (.expression (.symbol name :: arguments)) incoming fuel live Atom.notReducible
      (rawQueryResults space (.expression (.symbol name :: arguments)) expected incoming fuel live)) results) :
    Realizes space (.call (.expression (.symbol name :: arguments)) expected incoming (fuel + 1) live)
      results := by
  intro stack emitted
  let query := Atom.expression (.symbol name :: arguments)
  let after := Frame.producerResults (.ordinary expected) query incoming fuel live Atom.notReducible
  have ordinary : minimalInstruction query = false := by
    rw [classifier_agrees]
    exact nonembedded
  have notError : isErrorAtom query = false := by simp [query, isErrorAtom, clean]
  have begin := enter_request space GroundedDispatch.none
    (.call query expected incoming (fuel + 1) live) stack emitted
  have invoked := enter_request space GroundedDispatch.none
    (.invocation (.ordinary expected) query incoming (fuel + 1) live) stack emitted
  have prepared := equations_read_realizes space query expected incoming fuel live
    (queryEquationsAvoiding (equationScope live query expected incoming) space query fuel)
    (after :: stack) emitted
  have resumed := consume_continuation space GroundedDispatch.none after
    (rawQueryResults space query expected incoming fuel live) stack emitted
  have finish := body stack emitted
  apply begin.trans
  apply invoked.trans
  simpa only [FirstSuccessRecursiveStrategy.enter, RecursiveMachine.enter,
    InvocationMode.errorPassthrough, notError, Bool.false_eq_true, if_false,
    GroundedDispatch.none, ordinary, InvocationMode.expected, List.nil_append,
    List.cons_append, query] using prepared.trans (resumed.trans (by
      simpa only [RecursiveMachine.resume, List.nil_append, after,
        rawQueryResults, equationInputs] using finish))


/-- Actual merge and loop rejection are performed before recursive RHS work.
Every surviving body is evaluated under its changed binding frame, while
later equation candidates and the caller's stack remain retained. -/
theorem equations_realizes (space : Space) (original expected : Atom) (incoming : Bindings)
    (fuel : Nat) (live : List Atom) {candidates : ResultSet} {outputs : List (List ResultSet)}
    (bodies : List.Forall₂ (fun candidate output =>
      List.Forall₂ (fun request results =>
        Realizes space (.returned original request.1 expected request.2 fuel live) results)
        (equationInputs incoming fuel candidate) output) candidates outputs) :
    Realizes space (.returns original expected fuel
      (candidates.flatMap (equationInputs incoming fuel)) live)
      (outputs.map List.flatten).flatten := by
  have grouped : List.Forall₂ (List.Forall₂ fun request results =>
      Realizes space (.returned original request.1 expected request.2 fuel live) results)
      (candidates.map (equationInputs incoming fuel)) outputs :=
    List.forall₂_map_left_iff.mpr bodies
  have joined := returns_realizes space original expected fuel live (List.rel_flatten grouped)
  simpa only [← List.flatMap_def, List.flatten_flatten] using joined

/-- Independent leaf evidence earns all instantiated body requests. The
space may contain equations and each body keeps its actual merged bindings. -/
theorem equations_leaf_realizes (space : Space) (original expected : Atom) (incoming : Bindings)
    (fuel : Nat) (candidates : ResultSet)
    (leaves : ∀ candidate ∈ candidates, ∀ request ∈ equationInputs incoming (fuel + 1) candidate,
      LeafRel request.1 expected) (notRefused : ∀ candidate ∈ candidates,
      ∀ request ∈ equationInputs incoming (fuel + 1) candidate, request.1 ≠ Atom.notReducible)
    (live : List Atom := []) :
    Realizes space (.returns original expected (fuel + 1)
      (candidates.flatMap (equationInputs incoming (fuel + 1))) live)
      (candidates.flatMap (equationInputs incoming (fuel + 1))) := by
  have body : ∀ candidate ∈ candidates,
      List.Forall₂ (fun request output =>
        Realizes space (.returned original request.1 expected request.2 (fuel + 1) live) output)
        (equationInputs incoming (fuel + 1) candidate)
        ((equationInputs incoming (fuel + 1) candidate).map fun request => [request]) := by
    intro candidate member
    apply List.forall₂_map_right_iff.mpr
    apply List.forall₂_same.mpr
    intro request present stack emitted
    by_cases stopped : isEmptyOrError request.1 = true
    · exact returned_stopped_realizes space original request.1 expected request.2 (fuel + 1)
        live stopped stack emitted
    · apply returned_evaluate_realizes space original request.1 expected request.2 (fuel + 1)
        live [request] (notRefused candidate member request present) (by simpa using stopped)
        (stack := stack) (emitted := emitted)
      exact retained_leaf space HE.GroundedDispatch.none request.1 expected request.2 fuel
        (leaves candidate member request present) live
  have children : List.Forall₂ (fun candidate output =>
      List.Forall₂ (fun request results =>
        Realizes space (.returned original request.1 expected request.2 (fuel + 1) live) results)
        (equationInputs incoming (fuel + 1) candidate) output)
      candidates (candidates.map fun candidate =>
        (equationInputs incoming (fuel + 1) candidate).map fun request => [request]) :=
    List.forall₂_map_right_iff.mpr (List.forall₂_same.mpr fun candidate member => body candidate member)
  have batch := equations_realizes space original expected incoming (fuel + 1) live children
  simpa only [List.map_map, Function.comp_def, ← List.flatMap_def,
    List.flatMap_singleton'] using batch

/-- Raw demand is earned for every instantiated body, with no equation-free
restriction on the space or unchanged-binding restriction on the outputs. -/
theorem equations_raw_realizes (space : Space) (original : Atom) (incoming : Bindings)
    (fuel : Nat) (candidates : ResultSet)
    (notRefused : ∀ candidate ∈ candidates,
      ∀ request ∈ equationInputs incoming (fuel + 1) candidate, request.1 ≠ Atom.notReducible) :
    Realizes space (.returns original Atom.atomType (fuel + 1)
      (candidates.flatMap (equationInputs incoming (fuel + 1))))
      (candidates.flatMap (equationInputs incoming (fuel + 1))) :=
  equations_leaf_realizes space original Atom.atomType incoming fuel candidates (fun _ _ request _ =>
    Or.inr ⟨getMetaType request.1,
      (Conformance.metaTypeRel_iff_getMetaType _ _).mpr rfl, Or.inl rfl⟩) notRefused

/-- Nonempty actual survivors license producer work; candidate existence alone
is insufficient because reconciliation can reject every candidate. -/
theorem call_equations_realizes (space : Space) (name : String) (arguments : List Atom)
    (expected : Atom) (incoming : Bindings) (fuel : Nat) (results : ResultSet)
    (nonembedded : Spec.Eval.Minimal.embeddedInstruction (.expression [.symbol name]) = false)
    (clean : name ≠ "Error") (live : List Atom)
    (selected : rawQueryResults space (.expression (.symbol name :: arguments)) expected incoming fuel live ≠ [])
    (ordinary : ∀ request ∈ rawQueryResults space (.expression (.symbol name :: arguments))
      expected incoming fuel live, ¬Spec.Eval.Minimal.IsFunction request.1)
    (bodies : Realizes space (.returns (.expression (.symbol name :: arguments)) expected fuel
      (rawQueryResults space (.expression (.symbol name :: arguments)) expected incoming fuel live) live) results) :
    Realizes space (.call (.expression (.symbol name :: arguments)) expected incoming (fuel + 1) live)
      results := by
  cases fuel with
  | zero => simp [rawQueryResults, queryEquationsAvoiding] at selected
  | succ fuel =>
      exact call_query_realizes space name arguments expected incoming (fuel + 1) live nonembedded clean
        results (producer_ordinary_realizes space _ _ _ fuel live _ _ selected ordinary bodies)

theorem call_empty_realizes (space : Space) (name : String) (arguments : List Atom)
    (expected : Atom) (incoming : Bindings) (fuel : Nat) (live : List Atom)
    (nonembedded : Spec.Eval.Minimal.embeddedInstruction (.expression [.symbol name]) = false)
    (clean : name ≠ "Error")
    (empty : queryEquationsAvoiding
      (equationScope live (.expression (.symbol name :: arguments)) expected incoming)
      space (.expression (.symbol name :: arguments)) fuel = []) :
    Realizes space (.call (.expression (.symbol name :: arguments)) expected incoming (fuel + 1) live)
      [(.expression (.symbol name :: arguments), incoming)] := by
  apply call_query_realizes space name arguments expected incoming fuel live nonembedded clean
  simpa only [rawQueryResults, empty, List.flatMap_nil] using
    producer_refused_realizes space (.expression (.symbol name :: arguments)) expected incoming fuel live


theorem call_unreduced (space : Space) (free : EquationFree space)
    (name : String)
    (nonembedded : Spec.Eval.Minimal.embeddedInstruction (.expression [.symbol name]) = false)
    (clean : name ≠ "Error") (arguments : List Atom) (expected : Atom)
    (bindings : Bindings) (fuel : Nat) (live : List Atom := []) :
    Realizes space (.call (.expression (.symbol name :: arguments)) expected bindings (fuel + 1) live)
      [(.expression (.symbol name :: arguments), bindings)] :=
  call_empty_realizes space name arguments expected bindings fuel live nonembedded clean
    (no_scoped_source_equations space free _ _ _)

/-- Each retained call keeps its own binding endpoints. The saved calls
continuation concatenates complete replies, including repeated equal values. -/
theorem calls_realizes (space : Space) (expected : Atom) (fuel : Nat) (live : List Atom)
    {requests : ResultSet} {outputs : List ResultSet}
    (children : List.Forall₂ (fun request output =>
      Realizes space (.call request.1 expected request.2 fuel live) output) requests outputs) :
    Realizes space (.calls expected fuel requests live) outputs.flatten := by
  refine (appendFrames space).traverseTasks
    (fun requests => Task.calls expected fuel requests live)
    (fun request => Task.call request.1 expected request.2 fuel live) ?_ ?_ children
  · intro stack emitted
    exact enter_request space HE.GroundedDispatch.none (Task.calls expected fuel [] live) stack emitted
  · rintro ⟨value, bindings⟩ rest stack emitted
    exact enter_request space HE.GroundedDispatch.none (Task.calls expected fuel (⟨value, bindings⟩ :: rest) live)
      stack emitted

theorem calls_unreduced (space : Space) (free : EquationFree space)
    (name : String)
    (nonembedded : Spec.Eval.Minimal.embeddedInstruction (.expression [.symbol name]) = false)
    (clean : name ≠ "Error") (values : List (List Atom)) (expected : Atom)
    (bindings : Bindings) (fuel : Nat) (live : List Atom) :
    Realizes space (.calls expected (fuel + 1)
      (replies bindings (values.map fun packet => .expression (.symbol name :: packet))) live)
      (replies bindings (values.map fun packet => .expression (.symbol name :: packet))) := by
  let requests := replies bindings (values.map fun packet => .expression (.symbol name :: packet))
  have children : List.Forall₂ (fun request output =>
      Realizes space (.call request.1 expected request.2 (fuel + 1) live) output)
      requests (requests.map fun request => [request]) := by
    apply List.forall₂_map_right_iff.mpr
    apply List.forall₂_same.mpr
    intro request member
    obtain ⟨value, valueMember, rfl⟩ := List.mem_map.mp member
    obtain ⟨packet, _, rfl⟩ := List.mem_map.mp valueMember
    exact call_unreduced space free name nonembedded clean packet expected bindings fuel live
  simpa only [← List.flatMap_def, List.flatMap_singleton'] using
    calls_realizes space expected (fuel + 1) live children

/-- Physical reply batches for the retained argument-head instruction. A changed
failure contributes its own occurrence without evaluating the pending arguments. -/
def argumentOutputs (original : Atom) (heads : ResultSet)
    (tails : ResultPair → ResultSet) : ResultSet :=
  heads.flatMap fun head =>
    if head.1 != original && isEmptyOrError head.1 then [head]
    else RecursiveTasks.argumentTail head.1 (tails head)

private def argumentBranchPlan (original : Atom) (remaining types : List Atom)
    (fuel : Nat) (live : List Atom) : BranchPlan where
  batch rows := .argumentHeads original remaining types fuel rows live
  stopped row := row.1 != original && isEmptyOrError row.1
  child row := .args remaining types row.2 fuel (row.1 :: live)
  receiver row := .argumentTail row.1
  readout row := RecursiveTasks.argumentTail row.1

/-- The retained branch instruction composes a physical list of replies,
including stopped branches and differently sized completed tail batches. -/
theorem argument_heads_branches_realizes (space : Space) (original : Atom)
    (remaining types : List Atom) (fuel : Nat) (live : List Atom)
    {heads : ResultSet} {outputs : List ResultSet}
    (branches : List.Forall₂ (fun head output =>
      if head.1 != original && isEmptyOrError head.1 then output = [head]
      else ∃ tails, Realizes space (.args remaining types head.2 fuel (head.1 :: live)) tails ∧
        output = RecursiveTasks.argumentTail head.1 tails) heads outputs) :
    Realizes space (.argumentHeads original remaining types fuel heads live) outputs.flatten := by
  let plan := argumentBranchPlan original remaining types fuel live
  refine (appendFrames space).traverseBranches plan ?_ ?_ ?_ ?_ branches
  · intro stack emitted
    exact enter_request space HE.GroundedDispatch.none (Task.argumentHeads original remaining types fuel [] live) stack emitted
  · rintro ⟨value, bindings⟩ rest stopped stack emitted
    simp only [plan, argumentBranchPlan] at stopped
    simpa only [plan, argumentBranchPlan, FirstSuccessRecursiveStrategy.enter, RecursiveMachine.enter,
      stopped, if_true, List.cons_append, List.nil_append] using
      enter_request space HE.GroundedDispatch.none (Task.argumentHeads original remaining types fuel (⟨value, bindings⟩ :: rest) live) stack emitted
  · rintro ⟨value, bindings⟩ rest running stack emitted
    simp only [plan, argumentBranchPlan] at running
    simpa only [plan, argumentBranchPlan, FirstSuccessRecursiveStrategy.enter, RecursiveMachine.enter,
      running, Bool.false_eq_true, if_false, List.cons_append, List.nil_append] using
      enter_request space HE.GroundedDispatch.none (Task.argumentHeads original remaining types fuel (⟨value, bindings⟩ :: rest) live) stack emitted
  · intro row replies stack emitted
    simpa only [plan, argumentBranchPlan, RecursiveMachine.resume, List.cons_append, List.nil_append] using
      consume_continuation space HE.GroundedDispatch.none (Frame.argumentTail row.1) replies stack emitted

/-- Both failed and selected occurrences pass through the existing controller.
Only selected occurrences require a residual argument execution. -/
theorem argument_heads_mixed_realizes (space : Space) (original : Atom)
    (remaining types : List Atom) (fuel : Nat) (live : List Atom)
    (heads : ResultSet) (tails : ResultPair → ResultSet)
    (children : ∀ head ∈ heads,
      (head.1 != original && isEmptyOrError head.1) = false →
      Realizes space (.args remaining types head.2 fuel (head.1 :: live)) (tails head)) :
    Realizes space (.argumentHeads original remaining types fuel heads live)
      (argumentOutputs original heads tails) := by
  have branches := (argumentBranchPlan original remaining types fuel live).rowResults_map
    (step := (FirstSuccessRecursiveExecution.machine HE.GroundedDispatch.none).reading.silent) (space := space) heads tails children
  have run := argument_heads_branches_realizes space original remaining types fuel live branches
  rw [← List.flatMap_def] at run
  exact run

theorem arguments_cons_mixed_realizes (space : Space) (original expected : Atom)
    (remaining types : List Atom) (incoming : Bindings) (fuel : Nat) (live : List Atom)
    (heads : ResultSet) (tails : ResultPair → ResultSet)
    (headRun : Realizes space (.atom original expected incoming fuel (remaining ++ types ++ live)) heads)
    (children : ∀ head ∈ heads,
      (head.1 != original && isEmptyOrError head.1) = false →
      Realizes space (.args remaining types head.2 fuel (head.1 :: live)) (tails head)) :
    Realizes space (.args (original :: remaining) (expected :: types) incoming (fuel + 1) live)
      (argumentOutputs original heads tails) := by
  refine FramedPath.trans (third := []) (FramedPath.receive (first := []) (last := []) (receiver := Frame.argumentHeads original remaining types fuel live) ?_ headRun ?_)
    (argument_heads_mixed_realizes space original remaining types fuel live heads tails children)
  · intro stack emitted
    exact enter_request space HE.GroundedDispatch.none (.args (original :: remaining) (expected :: types) incoming (fuel + 1) live) stack emitted
  · intro stack emitted
    exact consume_continuation space HE.GroundedDispatch.none (Frame.argumentHeads original remaining types fuel live) heads stack emitted

/-- Resume directly at the saved head-return frame. The selected head service
is not among the assumptions needed to execute this residual configuration. -/
theorem argument_checkpoint_realizes (space : Space) (original : Atom)
    (remaining types : List Atom) (fuel : Nat) (live : List Atom)
    (heads : ResultSet) (tails : ResultPair → ResultSet)
    (children : ∀ head ∈ heads,
      (head.1 != original && isEmptyOrError head.1) = false →
      Realizes space (.args remaining types head.2 fuel (head.1 :: live)) (tails head))
    (stack : List Frame) (emitted : ResultSet) :
    SilentPath HE.GroundedDispatch.none
      ⟨space, .returning heads, .argumentHeads original remaining types fuel live :: stack, emitted⟩
      ⟨space, .returning (argumentOutputs original heads tails), stack, emitted⟩ := by
  have resumed := consume_continuation space HE.GroundedDispatch.none
    (.argumentHeads original remaining types fuel live) heads stack emitted
  exact resumed.trans (by
    simpa only [RecursiveMachine.resume, List.nil_append] using
      argument_heads_mixed_realizes space original remaining types fuel live heads tails children stack emitted)


/-- Every accepted head resumes its own remaining argument computation under
that head's selected binding frame. Tail replies retain their actual output
frames; neither branching nor collecting argument packets restores the input
frame. This local composition law does not assume source/body adequacy. -/
theorem argument_heads_realizes (space : Space) (original : Atom) (remaining types : List Atom)
    (fuel : Nat) (live : List Atom) {heads : ResultSet} {outputs : List ResultSet}
    (safe : ∀ head ∈ heads, head.1 = original ∨ isEmptyOrError head.1 = false)
    (branches : List.Forall₂ (fun head output => ∃ tails,
      Realizes space (.args remaining types head.2 fuel (head.1 :: live)) tails ∧
        output = RecursiveTasks.argumentTail head.1 tails) heads outputs) :
    Realizes space (.argumentHeads original remaining types fuel heads live) outputs.flatten := by
  apply argument_heads_branches_realizes space original remaining types fuel live
  induction branches with
  | nil => exact .nil
  | @cons head output heads outputs branch branches ih =>
      have guard : (head.1 != original && isEmptyOrError head.1) = false := by
        rcases safe head List.mem_cons_self with same | clean
        · simp [same]
        · simp [clean]
      refine .cons ?_ (ih (fun next member => safe next (List.mem_cons_of_mem _ member)))
      simpa only [guard, Bool.false_eq_true, if_false] using branch

/-- The actual argument instruction composes a full head computation with
its branch-specific residual arguments, preserving the surrounding caller. -/
theorem arguments_cons_with_branches_realizes (space : Space) (original expected : Atom)
    (remaining types : List Atom) (incoming : Bindings) (fuel : Nat) (live : List Atom)
    {heads : ResultSet} {outputs : List ResultSet}
    (headRun : Realizes space (.atom original expected incoming fuel (remaining ++ types ++ live))
      heads)
    (safe : ∀ head ∈ heads, head.1 = original ∨ isEmptyOrError head.1 = false)
    (branches : List.Forall₂ (fun head output => ∃ tails,
      Realizes space (.args remaining types head.2 fuel (head.1 :: live)) tails ∧
        output = RecursiveTasks.argumentTail head.1 tails) heads outputs) :
    Realizes space (.args (original :: remaining) (expected :: types) incoming (fuel + 1) live)
      outputs.flatten := by
  refine FramedPath.trans (third := []) (FramedPath.receive (first := []) (last := []) (receiver := Frame.argumentHeads original remaining types fuel live) ?_ headRun ?_)
    (argument_heads_realizes space original remaining types fuel live safe branches)
  · intro stack emitted
    exact enter_request space HE.GroundedDispatch.none (.args (original :: remaining) (expected :: types) incoming (fuel + 1) live) stack emitted
  · intro stack emitted
    exact consume_continuation space HE.GroundedDispatch.none (Frame.argumentHeads original remaining types fuel live) heads stack emitted

theorem argument_heads (space : Space) (original : Atom) (remaining types : List Atom)
    (bindings : Bindings) (fuel : Nat) (live : List Atom) (heads : List Atom)
    (tails : List (List Atom))
    (safe : ∀ head ∈ heads, head = original ∨ isEmptyOrError head = false)
    (tail : ∀ live', Realizes space (.args remaining types bindings fuel live')
      (packets bindings tails)) :
    Realizes space (.argumentHeads original remaining types fuel (replies bindings heads) live)
      (packets bindings (heads.flatMap fun head => tails.map fun values => head :: values)) := by
  have safeHeads : ∀ head ∈ replies bindings heads,
      head.1 = original ∨ isEmptyOrError head.1 = false := by
    intro head member
    change head ∈ heads.map (fun value => (value, bindings)) at member
    obtain ⟨value, valueMember, same⟩ := List.mem_map.mp member
    simpa only [← same] using safe value valueMember
  have branches : List.Forall₂ (fun head output => ∃ results,
      Realizes space (.args remaining types head.2 fuel (head.1 :: live)) results ∧
        output = RecursiveTasks.argumentTail head.1 results)
      (replies bindings heads)
      (heads.map fun head => RecursiveTasks.argumentTail head (packets bindings tails)) := by
    clear safe safeHeads
    induction heads with
    | nil => exact .nil
    | cons head heads ih => exact .cons ⟨packets bindings tails, tail _, rfl⟩ ih
  have realized := argument_heads_realizes space original remaining types fuel live safeHeads
    branches
  simpa [packets, replies, RecursiveTasks.argumentTail, List.map_map, Function.comp_def,
    List.map_flatMap, List.flatMap_map, ← List.flatMap_def] using realized

theorem function_head (space : Space) (name : String) (domains : List Atom) (returned : Atom)
    (bindings : Bindings) (fuel : Nat) (live : List Atom) (values : List (List Atom))
    (arguments : List Atom) (clean : name ≠ "Empty")
    (tail : Realizes space (.args arguments domains bindings fuel (.symbol name :: live))
      (packets bindings values)) :
    Realizes space (.heads (arrow domains returned) arguments fuel [(.symbol name, bindings)] live)
      (replies bindings (values.map fun packet => .expression (.symbol name :: packet))) := by
  intro stack emitted
  let rest := Task.heads (arrow domains returned) arguments fuel [] live
  have begin := enter_request space HE.GroundedDispatch.none
    (.heads (arrow domains returned) arguments fuel [(.symbol name, bindings)] live) stack emitted
  have middle := tail (.functionTail (.symbol name) :: .append rest :: stack) emitted
  have collect := consume_continuation space HE.GroundedDispatch.none (.functionTail (.symbol name))
    (packets bindings values) (.append rest :: stack) emitted
  have mapped : RecursiveTasks.functionTail (.symbol name) (packets bindings values) =
      replies bindings (values.map fun packet => .expression (.symbol name :: packet)) := by
    simp [packets, replies, RecursiveTasks.functionTail, List.map_map, Function.comp_def]
  have emptyRest : Realizes space rest [] := by
    intro saved prior
    simpa [rest, FirstSuccessRecursiveStrategy.enter, RecursiveMachine.enter] using
      enter_request space HE.GroundedDispatch.none rest saved prior
  have finish := append_results space rest
    (replies bindings (values.map fun packet => .expression (.symbol name :: packet))) []
    emptyRest stack emitted
  have collected : SilentPath HE.GroundedDispatch.none
      ⟨space, .returning (packets bindings values), .functionTail (.symbol name) :: .append rest :: stack, emitted⟩
      ⟨space, .returning (replies bindings (values.map fun packet => .expression (.symbol name :: packet))),
        .append rest :: stack, emitted⟩ := by
    simpa only [RecursiveMachine.resume, mapped, List.nil_append] using collect
  exact begin.trans (by
    simpa [FirstSuccessRecursiveStrategy.enter, RecursiveMachine.enter, isEmptyOrError,
      isEmptyAtom, Atom.empty, isErrorAtom, clean, arrow, getFunctionArgTypes, rest] using
        middle.trans (collected.trans finish))


theorem symbol_cast_realizes (space : Space) (name : String) (expected : Atom)
    (bindings : Bindings) (fuel : Nat) (before after : List Atom) (actual : Atom)
    (notEmpty : name ≠ "Empty")
    (types : getAtomTypes space (.symbol name) = before ++ actual :: after)
    (expectedClosed : TypeSubst.typeVars expected = []) (actualClosed : TypeSubst.typeVars actual = [])
    (earlierClosed : ∀ candidate ∈ before, TypeSubst.typeVars candidate = [])
    (earlierRejects : ∀ candidate ∈ before, ¬ClosedTypeFits expected candidate)
    (fits : ClosedTypeFits expected actual) (enough : sizeOf expected + sizeOf actual + 2 ≤ fuel)
    (live : List Atom := []) :
    Realizes space (.atom (.symbol name) expected bindings (fuel + 1) live)
      [(.symbol name, bindings)] := by
  intro stack emitted
  have cast := (closed_cast_reply space (.symbol name) expected bindings fuel before actual after
    types expectedClosed earlierClosed earlierRejects actualClosed fits enough).1
  simpa [FirstSuccessRecursiveStrategy.enter, RecursiveMachine.enter, isEmptyOrError,
    isEmptyAtom, Atom.empty, isErrorAtom, getMetaType, notEmpty, cast] using
      enter_request space HE.GroundedDispatch.none
        (.atom (.symbol name) expected bindings (fuel + 1) live) stack emitted

theorem symbol_cast_spec (space : Space) (name : String) (expected : Atom)
    (bindings : BindingFrame) (fuel : Nat) (before after : List Atom) (actual : Atom)
    (notEmpty : name ≠ "Empty") (notRaw : expected ≠ Atom.atomType)
    (notMeta : expected ≠ Atom.symbolType)
    (types : getAtomTypes space (.symbol name) = before ++ actual :: after)
    (expectedClosed : TypeSubst.typeVars expected = []) (actualClosed : TypeSubst.typeVars actual = [])
    (earlierClosed : ∀ candidate ∈ before, TypeSubst.typeVars candidate = [])
    (earlierRejects : ∀ candidate ∈ before, ¬ClosedTypeFits expected candidate)
    (fits : ClosedTypeFits expected actual) (enough : sizeOf expected + sizeOf actual + 2 ≤ fuel)
    (live : List Atom) (scope : List String) :
    EvalAtomRawRel space noHost live (protectedScope := scope)
      (.symbol name) expected bindings (.symbol name, bindings) := by
  apply EvalAtomRawRel.cast (.symbol name) expected Atom.symbolType bindings (.symbol name, bindings)
  · simp [IsEmptyOrErrorRel, IsErrorRel, Atom.empty, notEmpty]
  · exact .symbol name
  · rintro (raw | intrinsic | impossible)
    · exact notRaw raw
    · exact notMeta intrinsic
    · simp at impossible
  · exact Or.inl ⟨name, rfl⟩
  · exact (closed_cast_reply space (.symbol name) expected bindings fuel before actual after
      types expectedClosed earlierClosed earlierRejects actualClosed fits enough).2
  · exact .same .renew _

theorem symbol_rejection_realizes (space : Space) (name : String) (expected : Atom)
    (incoming : Bindings) (fuel : Nat) (live : List Atom)
    (notEmpty : name ≠ "Empty") (notRaw : expected ≠ Atom.atomType)
    (notMeta : expected ≠ Atom.symbolType)
    (expectedClosed : TypeSubst.typeVars expected = [])
    (closed : ∀ actual ∈ getAtomTypes space (.symbol name), TypeSubst.typeVars actual = [])
    (rejected : ∀ actual ∈ getAtomTypes space (.symbol name), ¬ClosedTypeFits expected actual) :
    Realizes space (.atom (.symbol name) expected incoming (fuel + 1) live)
      ((getAtomTypes space (.symbol name)).map fun actual =>
        (mkError (.symbol name) (.badType expected actual), incoming)) := by
  intro stack emitted
  change expected ≠ .symbol "Symbol" at notMeta
  change expected ≠ .symbol "Atom" at notRaw
  have cast := (closed_cast_failure_reply space (.symbol name) expected incoming fuel
    expectedClosed closed rejected).1
  simpa [FirstSuccessRecursiveStrategy.enter, RecursiveMachine.enter, isEmptyOrError,
    isEmptyAtom, Atom.empty, isErrorAtom, getMetaType, notEmpty, notRaw, notMeta,
    Atom.variableType, Atom.symbolType, cast] using
      enter_request space HE.GroundedDispatch.none
        (.atom (.symbol name) expected incoming (fuel + 1) live) stack emitted

theorem symbol_rejection_spec (space : Space) (name : String) (expected : Atom)
    (incoming : BindingFrame) (live : List Atom) (scope : List String)
    (notEmpty : name ≠ "Empty") (notRaw : expected ≠ Atom.atomType)
    (notMeta : expected ≠ Atom.symbolType)
    (expectedClosed : TypeSubst.typeVars expected = [])
    (closed : ∀ actual ∈ getAtomTypes space (.symbol name), TypeSubst.typeVars actual = [])
    (rejected : ∀ actual ∈ getAtomTypes space (.symbol name), ¬ClosedTypeFits expected actual)
    (actual : Atom) (present : actual ∈ getAtomTypes space (.symbol name)) :
    EvalAtomRawRel space noHost live (protectedScope := scope)
      (.symbol name) expected incoming (mkError (.symbol name) (.badType expected actual), incoming) := by
  apply EvalAtomRawRel.cast (.symbol name) expected Atom.symbolType incoming _
  · simp [IsEmptyOrErrorRel, IsErrorRel, Atom.empty, notEmpty]
  · exact .symbol name
  · rintro (raw | intrinsic | impossible)
    · exact notRaw raw
    · exact notMeta intrinsic
    · simp [Atom.symbolType, Atom.variableType] at impossible
  · exact Or.inl ⟨name, rfl⟩
  · exact (closed_cast_failure_reply space (.symbol name) expected incoming 0
      expectedClosed closed rejected).2 actual present
  · exact .same .renew _

/-- Independent source reflection for the rejected symbol cast. This is the
published first-success type service, not the old implementation EvalSpec. -/
theorem symbol_rejection_raw_iff (space : Space) (name : String) (expected : Atom)
    (incoming : Bindings) (live : List Atom) (scope : List String)
    (notEmpty : name ≠ "Empty") (notRaw : expected ≠ Atom.atomType)
    (notMeta : expected ≠ Atom.symbolType)
    (expectedClosed : TypeSubst.typeVars expected = [])
    (closed : ∀ actual ∈ getAtomTypes space (.symbol name), TypeSubst.typeVars actual = [])
    (rejected : ∀ actual ∈ getAtomTypes space (.symbol name), ¬ClosedTypeFits expected actual)
    (result : ResultPair) :
    EvalAtomRawRel space noHost live (protectedScope := scope)
      (.symbol name) expected incoming result ↔
    result ∈ (getAtomTypes space (.symbol name)).map
      (fun actual => (mkError (.symbol name) (.badType expected actual), incoming)) := by
  rcases result with ⟨resultValue, resultBindings⟩
  constructor
  · intro source
    cases source with
    | emptyOrError _ _ _ failed =>
        simp [IsEmptyOrErrorRel, IsErrorRel, Atom.empty, notEmpty] at failed
    | typePass _ _ metaTy _ _ intrinsic passed =>
        have same := Conformance.metaTypeRel_iff_getMetaType _ _ |>.mp intrinsic
        simp only [getMetaType] at same
        subst metaTy
        rcases passed with raw | intrinsic | impossible
        · exact (notRaw raw).elim
        · exact (notMeta intrinsic).elim
        · simp [Atom.symbolType, Atom.variableType] at impossible
    | cast _ _ _ _ _ _ _ _ _ cast _renewed =>
        have member := (closed_cast_failure_iff space (.symbol name) expected incoming 0
          expectedClosed closed rejected (resultValue, resultBindings)).mpr cast
        rw [(closed_cast_failure_reply space (.symbol name) expected incoming 0
          expectedClosed closed rejected).1] at member
        exact member
    | interpretSuccess _ _ _ _ _ _ _ _ impossible _ _ =>
        obtain ⟨head, tail, impossible⟩ := impossible
        cases impossible
    | interpretError _ _ _ _ _ _ _ _ impossible _ _ =>
        obtain ⟨head, tail, impossible⟩ := impossible
        cases impossible
  · intro member
    obtain ⟨actual, present, same⟩ := List.mem_map.mp member
    obtain ⟨valueSame, bindingsSame⟩ := Prod.mk.inj same
    subst resultValue resultBindings
    exact symbol_rejection_spec space name expected incoming live scope notEmpty notRaw notMeta
      expectedClosed closed rejected actual present

/-- Total cast failure satisfies the public success-priority gate too: an
independent successful alternative has been excluded, not merely unobserved. -/
theorem symbol_rejection_published_iff (space : Space) (name : String) (expected : Atom)
    (incoming : Bindings) (live : List Atom)
    (notEmpty : name ≠ "Empty") (notRaw : expected ≠ Atom.atomType)
    (notMeta : expected ≠ Atom.symbolType)
    (expectedClosed : TypeSubst.typeVars expected = [])
    (closed : ∀ actual ∈ getAtomTypes space (.symbol name), TypeSubst.typeVars actual = [])
    (rejected : ∀ actual ∈ getAtomTypes space (.symbol name), ¬ClosedTypeFits expected actual)
    (result : ResultPair) :
    EvalRel space noHost live (.symbol name) expected incoming result ↔
      result ∈ (getAtomTypes space (.symbol name)).map
        (fun actual => (mkError (.symbol name) (.badType expected actual), incoming)) := by
  have exactRaw := symbol_rejection_raw_iff space name expected incoming live []
    notEmpty notRaw notMeta expectedClosed closed rejected
  constructor
  · intro source
    exact (exactRaw result).mp source.1
  · intro member
    refine ⟨(exactRaw result).mpr member, ?_⟩
    intro _ other source
    have historical := source.preserves_historical rfl
    rw [← historical.result] at source
    obtain ⟨actual, _, same⟩ := List.mem_map.mp
      ((exactRaw (BindingFrame.rawResult other)).mp source)
    have value := congrArg Prod.fst same
    change mkError (.symbol name) (.badType expected actual) = other.1 at value
    rw [← value]
    simp [IsErrorRel, mkError, Atom.error]


theorem application_selected {space : Space} {name : String} {arguments : List Atom}
    {expected : Atom} {fuel : Nat} (typing : ApplicationTyping space name arguments expected fuel)
    (bindings : Bindings) :
    FirstSuccessRecursiveStrategy.select space (.expression (.symbol name :: arguments)) expected bindings
      (fuel + 1) (getAtomTypes space (.symbol name)) =
        .selected (selectedPolicy typing.domains typing.returned) [bindings] ∧
    FunctionCandidateScanRel PublishedCandidateApplicabilityRel space
      (.expression (.symbol name :: arguments)) expected bindings
      (getAtomTypes space (.symbol name))
      (.success (selectedPolicy typing.domains typing.returned) bindings) := by
  obtain ⟨policy, domains, returned, selected, scan⟩ := checked_prefix_selected typing.rejected
    typing.returned typing.domains bindings typing.after typing.argumentChecks typing.argumentPaths
    typing.expectedClosed typing.returnedClosed typing.returnedFits typing.returnBudget
  have same : policy = selectedPolicy typing.domains typing.returned := by
    cases policy with
    | mk functionType argumentTypes returnType isFunction =>
        dsimp at domains returned
        subst argumentTypes; subst returnType
        change functionType = arrow typing.domains typing.returned at isFunction
        subst functionType
        rfl
  subst policy
  rw [typing.sourceTypes]
  exact ⟨selected, scan⟩

theorem application_function {space : Space} {name : String} {arguments : List Atom}
    {expected : Atom} {fuel : Nat} (typing : ApplicationTyping space name arguments expected fuel)
    (bindings : Bindings) (values : List (List Atom)) (live : List Atom)
    (argumentsRun : Realizes space
      (.args arguments typing.domains bindings fuel (.symbol name :: live)) (packets bindings values)) :
    Realizes space
      (.func (.expression (.symbol name :: arguments)) (arrow typing.domains typing.returned)
        bindings (fuel + 1) live)
      (replies bindings (values.map fun packet => .expression (.symbol name :: packet))) := by
  cases fuel with
  | zero => have := typing.headBudget; omega
  | succ fuel =>
      intro stack emitted
      have cast := symbol_cast_realizes space name (arrow typing.domains typing.returned)
        bindings fuel typing.before typing.after (arrow typing.domains typing.returned)
        typing.nonemptyOperator typing.sourceTypes
        typing.headClosed typing.headClosed typing.earlierClosed typing.earlierHeadRejects
        (Or.inr (Or.inr (Or.inr (Or.inr rfl)))) (by have := typing.headBudget; omega)
        (arrow typing.domains typing.returned :: arguments ++ live)
        (.heads (arrow typing.domains typing.returned) arguments (fuel + 1) live :: stack) emitted
      have resumed := consume_continuation space HE.GroundedDispatch.none
        (.heads (arrow typing.domains typing.returned) arguments (fuel + 1) live)
        [(.symbol name, bindings)] stack emitted
      have done := function_head space name typing.domains typing.returned bindings (fuel + 1) live
        values arguments typing.nonemptyOperator argumentsRun stack emitted
      have continuation := resumed.trans (by
        simpa only [RecursiveMachine.resume, List.nil_append] using done)
      have begin := enter_request space HE.GroundedDispatch.none
        (.func (.expression (.symbol name :: arguments)) (arrow typing.domains typing.returned)
          bindings (fuel + 1 + 1) live) stack emitted
      exact begin.trans (by
        simpa only [FirstSuccessRecursiveStrategy.enter, RecursiveMachine.enter,
          List.cons_append, List.nil_append] using cast.trans continuation)

/-- Typed argument alternatives enter the actual calls continuation. Its
outputs may change binding frames; all call occurrences and saved alternatives
are appended without replacing those outputs by their incoming bindings. -/
theorem binding_alternatives_with_calls {space : Space} {name : String} {arguments : List Atom}
    {expected : Atom} {fuel : Nat} (typing : ApplicationTyping space name arguments expected fuel)
    (bindings : Bindings) (values : List (List Atom)) (count : Nat) (results : ResultSet)
    (live : List Atom)
    (argumentsRun : Realizes space (.args arguments typing.domains bindings fuel
      (.symbol name ::
        (if typing.returned = Atom.expressionType then Atom.undefinedType else typing.returned) ::
          live))
      (packets bindings values))
    (callsRun : Realizes space
      (.calls (if typing.returned = Atom.expressionType then Atom.undefinedType else typing.returned)
        (fuel + 1) (replies bindings (values.map fun packet => .expression (.symbol name :: packet)))
        live)
      results) :
    Realizes space
      (.bindingAlternatives (.expression (.symbol name :: arguments)) (arrow typing.domains typing.returned)
        (if typing.returned = Atom.expressionType then Atom.undefinedType else typing.returned)
        (fuel + 1) (List.replicate count bindings) live)
      (List.replicate count results).flatten := by
  induction count with
  | zero =>
      intro stack emitted
      simpa [replies, FirstSuccessRecursiveStrategy.enter, RecursiveMachine.enter] using
        enter_request space HE.GroundedDispatch.none
          (.bindingAlternatives (.expression (.symbol name :: arguments))
            (arrow typing.domains typing.returned)
            (if typing.returned = Atom.expressionType then Atom.undefinedType else typing.returned)
            (fuel + 1) [] live) stack emitted
  | succ count ih =>
      intro stack emitted
      let callType := if typing.returned = Atom.expressionType then Atom.undefinedType else typing.returned
      let one := replies bindings (values.map fun packet => .expression (.symbol name :: packet))
      let rest := Task.bindingAlternatives (.expression (.symbol name :: arguments))
        (arrow typing.domains typing.returned) callType (fuel + 1) (List.replicate count bindings) live
      have begin := enter_request space HE.GroundedDispatch.none
        (.bindingAlternatives (.expression (.symbol name :: arguments))
          (arrow typing.domains typing.returned) callType (fuel + 1)
          (List.replicate (count + 1) bindings) live) stack emitted
      have function := application_function typing bindings values (callType :: live) argumentsRun
        (.calls callType (fuel + 1) live :: .append rest :: stack) emitted
      have transfer := consume_continuation space HE.GroundedDispatch.none
        (.calls callType (fuel + 1) live) one (.append rest :: stack) emitted
      have calls := callsRun (.append rest :: stack) emitted
      have remainder := append_results space rest results
        (List.replicate count results).flatten ih stack emitted
      have collected := transfer.trans (by
        simpa only [RecursiveMachine.resume, List.nil_append, one] using calls.trans remainder)
      exact begin.trans (by
        simpa [FirstSuccessRecursiveStrategy.enter, RecursiveMachine.enter, List.replicate_succ,
          callType, one, rest, replies, List.map_append] using function.trans collected)


theorem binding_alternatives {space : Space} {name : String} {arguments : List Atom}
    {expected : Atom} {fuel : Nat} (typing : ApplicationTyping space name arguments expected fuel)
    (nonembedded : Spec.Eval.Minimal.embeddedInstruction (.expression [.symbol name]) = false)
    (free : EquationFree space) (bindings : Bindings) (values : List (List Atom)) (count : Nat)
    (live : List Atom)
    (argumentsRun : ∀ live', Realizes space (.args arguments typing.domains bindings fuel live')
      (packets bindings values)) :
    Realizes space
      (.bindingAlternatives (.expression (.symbol name :: arguments)) (arrow typing.domains typing.returned)
        (if typing.returned = Atom.expressionType then Atom.undefinedType else typing.returned)
        (fuel + 1) (List.replicate count bindings) live)
      (replies bindings ((List.replicate count
        (values.map fun packet => .expression (.symbol name :: packet))).flatten)) := by
  have calls := calls_unreduced space free name nonembedded typing.cleanOperator values
    (if typing.returned = Atom.expressionType then Atom.undefinedType else typing.returned)
    bindings fuel live
  simpa only [replies, List.map_flatten, List.map_replicate] using
    binding_alternatives_with_calls typing bindings values count
      (replies bindings (values.map fun packet => .expression (.symbol name :: packet))) live
      (argumentsRun _) calls


theorem clean_application (name : String) (values : List Atom) (clean : name ≠ "Error") :
    ¬IsEmptyOrErrorRel (.expression (.symbol name :: values)) ∧
    isEmptyOrError (.expression (.symbol name :: values)) = false := by
  simp [IsEmptyOrErrorRel, IsErrorRel, isEmptyOrError, isEmptyAtom, isErrorAtom, Atom.empty, clean]

theorem application_spec {space : Space} {name : String} {arguments : List Atom}
    {expected : Atom} {fuel : Nat} (typing : ApplicationTyping space name arguments expected fuel)
    (nonembedded : Spec.Eval.Minimal.embeddedInstruction (.expression [.symbol name]) = false)
    (free : EquationFree space) (bindings : Bindings) (values : List Atom)
    (live : List Atom) (scope : List String)
    (argumentDerivation : InterpretArgsRel space noHost
      (.symbol name ::
        (if typing.returned = Atom.expressionType then Atom.undefinedType else typing.returned) :: live)
      (protectedScope := scope) arguments typing.domains bindings
      (argumentPacket values, bindings)) :
    EvalAtomRawRel space noHost live (protectedScope := scope)
      (.expression (.symbol name :: arguments)) expected bindings
      (.expression (.symbol name :: values), bindings) := by
  have cleanInput := (clean_application name arguments typing.cleanOperator).1
  have cleanOutput := (clean_application name values typing.cleanOperator).1
  have interpreted : InterpretExpressionRel space noHost live (protectedScope := scope)
      (.expression (.symbol name :: arguments)) expected bindings
      (.expression (.symbol name :: values), bindings) := by
    apply InterpretExpressionRel.functionPath _ _ (.symbol name) arguments
      (getAtomTypes space (.symbol name)) (getAtomTypes space (.symbol name))
      (selectedPolicy typing.domains typing.returned)
      (if typing.returned = Atom.expressionType then Atom.undefinedType else typing.returned)
      bindings bindings (.expression (.symbol name :: values), bindings)
      (.expression (.symbol name :: values), bindings) rfl (FirstSuccessSourceReplies.source_types space (.symbol name))
      rfl (application_selected typing bindings).2 (.same .renew _) rfl
    · have head : EvalAtomRawRel space noHost
          (arrow typing.domains typing.returned :: arguments ++
            (if typing.returned = Atom.expressionType then Atom.undefinedType else typing.returned) :: live)
          (protectedScope := scope ++ expectedApplicationScope (.expression (.symbol name :: arguments)) expected)
          (.symbol name) (arrow typing.domains typing.returned) bindings (.symbol name, bindings) :=
        symbol_cast_spec space name (arrow typing.domains typing.returned) bindings (fuel - 1)
          typing.before typing.after (arrow typing.domains typing.returned)
          typing.nonemptyOperator (by simp [arrow]) (by simp [arrow]) typing.sourceTypes
          typing.headClosed typing.headClosed typing.earlierClosed typing.earlierHeadRejects
          (Or.inr (Or.inr (Or.inr (Or.inr rfl)))) (by have := typing.headBudget; omega) _ _
      simpa only [selectedPolicy, argumentValues_packet] using (InterpretFunctionRel.success
        (.expression (.symbol name :: arguments)) (arrow typing.domains typing.returned) expected (.symbol name)
        typing.returned arguments typing.domains bindings (.symbol name, bindings)
        (argumentPacket values, bindings) rfl (show FunctionTypeRel (arrow typing.domains typing.returned)
          typing.domains typing.returned from rfl) head
        (by simp [IsEmptyOrErrorRel, IsErrorRel, Atom.empty, typing.nonemptyOperator]) argumentDerivation
        ⟨values, rfl⟩)
    · apply CallRel.noEquation
      · exact fun error => cleanOutput (Or.inr error)
      · exact ⟨by simp [Spec.Eval.Minimal.HostCall, noHost], nonembedded⟩
      · exact no_independent_equations space free _ _ bindings
  apply EvalAtomRawRel.interpretSuccess _ _ Atom.expressionType bindings _ cleanInput
    (.expression (.symbol name :: arguments)) _ ⟨.symbol name, arguments, rfl⟩ interpreted
    (fun error => cleanOutput (Or.inr error))
  rintro (raw | intrinsic | impossible)
  · exact typing.demandNotRaw raw
  · exact typing.demandNotExpression intrinsic
  · simp at impossible

theorem success_priority_clean (bindings : Bindings) (values : List Atom)
    (clean : ∀ value ∈ values, isErrorAtom value = false) :
    successPriority (replies bindings values) = replies bindings values := by
  have all : (replies bindings values).filter (fun result => !isErrorAtom result.1) =
      replies bindings values := by
    apply List.filter_eq_self.mpr
    intro result member
    obtain ⟨value, valueMember, rfl⟩ := List.mem_map.mp member
    simp [clean value valueMember]
  rw [successPriority, all]
  cases values with
  | nil => simp [replies]
  | cons value values => simp [replies]

/-- The ordinary typed expression path delegates to the existing calls
continuation and retains its complete changed output frames. The actual
success-priority filter is applied, including its error-only behavior. -/
theorem application_with_calls_realizes {space : Space} {name : String} {arguments : List Atom}
    {expected : Atom} {fuel : Nat} (typing : ApplicationTyping space name arguments expected fuel)
    (bindings : Bindings) (values : List (List Atom)) (results : ResultSet) (live : List Atom)
    (argumentsRun : Realizes space (.args arguments typing.domains bindings fuel
      (.symbol name ::
        (if typing.returned = Atom.expressionType then Atom.undefinedType else typing.returned) ::
          live))
      (packets bindings values))
    (callsRun : Realizes space
      (.calls (if typing.returned = Atom.expressionType then Atom.undefinedType else typing.returned)
        (fuel + 1) (replies bindings (values.map fun packet => .expression (.symbol name :: packet)))
        live)
      results) :
    Realizes space (.atom (.expression (.symbol name :: arguments)) expected bindings (fuel + 3) live)
      (successPriority results) := by
  intro stack emitted
  let resultValues := results
  have atom := enter_request space HE.GroundedDispatch.none
    (.atom (.expression (.symbol name :: arguments)) expected bindings (fuel + 3) live) stack emitted
  have expression := enter_request space HE.GroundedDispatch.none
    (.expression (.expression (.symbol name :: arguments)) expected bindings (fuel + 2) live)
    (.filter :: stack) emitted
  have selection := enter_request space HE.GroundedDispatch.none
    (.functions (.expression (.symbol name :: arguments)) expected bindings (fuel + 1)
      (getAtomTypes space (.symbol name)) live) (.filter :: stack) emitted
  have alternatives := binding_alternatives_with_calls typing bindings values
    1 results live argumentsRun callsRun
    (.filter :: stack) emitted
  have filtered := consume_continuation space HE.GroundedDispatch.none .filter resultValues
    stack emitted
  have selected := (application_selected typing bindings).1
  have done := alternatives.trans (by
    simpa only [RecursiveMachine.resume, List.nil_append, resultValues, List.replicate_one,
      List.flatten_cons, List.flatten_nil, List.append_nil] using filtered)
  have stepSelection := selection.trans (by
    simpa [FirstSuccessRecursiveStrategy.enter, selected, selectedPolicy] using done)
  have stepExpression := expression.trans (by
    simpa only [FirstSuccessRecursiveStrategy.enter, rawTypeLookup, List.nil_append] using
      stepSelection)
  have notRaw : expected ≠ .symbol "Atom" := typing.demandNotRaw
  have notExpression : expected ≠ .symbol "Expression" := typing.demandNotExpression
  exact atom.trans (by
    simpa [FirstSuccessRecursiveStrategy.enter, RecursiveMachine.enter, isEmptyOrError,
      isEmptyAtom, Atom.empty, Atom.unit, isErrorAtom, getMetaType, notRaw,
      notExpression, typing.cleanOperator, Nat.add_assoc] using stepExpression)


theorem application_realizes {space : Space} {name : String} {arguments : List Atom}
    {expected : Atom} {fuel : Nat} (typing : ApplicationTyping space name arguments expected fuel)
    (nonembedded : Spec.Eval.Minimal.embeddedInstruction (.expression [.symbol name]) = false)
    (free : EquationFree space) (bindings : Bindings) (values : List (List Atom)) (live : List Atom)
    (argumentsRun : ∀ live', Realizes space (.args arguments typing.domains bindings fuel live')
      (packets bindings values)) :
    Realizes space (.atom (.expression (.symbol name :: arguments)) expected bindings (fuel + 3) live)
      (replies bindings (values.map fun packet => .expression (.symbol name :: packet))) := by
  let resultValues := (values.map fun packet => Atom.expression (.symbol name :: packet))
  have priority : successPriority (replies bindings resultValues) = replies bindings resultValues := by
    apply success_priority_clean
    intro value member
    obtain ⟨packet, _, rfl⟩ := List.mem_map.mp member
    simp [isErrorAtom, typing.cleanOperator]
  have calls := calls_unreduced space free name nonembedded typing.cleanOperator values
    (if typing.returned = Atom.expressionType then Atom.undefinedType else typing.returned)
    bindings fuel live
  have realized := application_with_calls_realizes typing bindings values
    (replies bindings (values.map fun packet => .expression (.symbol name :: packet))) live
    (argumentsRun _) calls
  change successPriority (replies bindings (values.map fun packet => .expression (.symbol name :: packet))) = _ at priority
  simpa only [priority] using realized


/-- Argument packets retain the output frame chosen by that branch. -/
abbrev ArgumentResults := List (List Atom × Bindings)

def argumentReplies (rows : ArgumentResults) : ResultSet :=
  rows.map fun row => (argumentPacket row.1, row.2)

def applications (name : String) (rows : ArgumentResults) : ResultSet :=
  rows.map fun row => (.expression (.symbol name :: row.1), row.2)

theorem function_head_retained (space : Space) (name : String) (domains : List Atom) (returned : Atom)
    (bindings : Bindings) (fuel : Nat) (live : List Atom) (rows : ArgumentResults)
    (arguments : List Atom) (clean : name ≠ "Empty")
    (tail : Realizes space (.args arguments domains bindings fuel (.symbol name :: live))
      (argumentReplies rows)) :
    Realizes space (.heads (arrow domains returned) arguments fuel [(.symbol name, bindings)] live)
      (applications name rows) := by
  intro stack emitted
  let rest := Task.heads (arrow domains returned) arguments fuel [] live
  have begin := enter_request space HE.GroundedDispatch.none
    (.heads (arrow domains returned) arguments fuel [(.symbol name, bindings)] live) stack emitted
  have middle := tail (.functionTail (.symbol name) :: .append rest :: stack) emitted
  have collect := consume_continuation space HE.GroundedDispatch.none (.functionTail (.symbol name))
    (argumentReplies rows) (.append rest :: stack) emitted
  have mapped : RecursiveTasks.functionTail (.symbol name) (argumentReplies rows) =
      applications name rows := by
    simp [argumentReplies, applications, RecursiveTasks.functionTail, List.map_map, Function.comp_def, argumentValues_packet, argumentsSucceeded_packet]
  have emptyRest : Realizes space rest [] := by
    intro saved prior
    simpa [rest, FirstSuccessRecursiveStrategy.enter, RecursiveMachine.enter] using
      enter_request space HE.GroundedDispatch.none rest saved prior
  have finish := append_results space rest
    (applications name rows) []
    emptyRest stack emitted
  have collected : SilentPath HE.GroundedDispatch.none
      ⟨space, .returning (argumentReplies rows), .functionTail (.symbol name) :: .append rest :: stack, emitted⟩
      ⟨space, .returning (applications name rows),
        .append rest :: stack, emitted⟩ := by
    simpa only [RecursiveMachine.resume, mapped, List.nil_append] using collect
  exact begin.trans (by
    simpa [FirstSuccessRecursiveStrategy.enter, RecursiveMachine.enter, isEmptyOrError,
      isEmptyAtom, Atom.empty, isErrorAtom, clean, arrow, getFunctionArgTypes, rest] using
        middle.trans (collected.trans finish))

theorem application_function_retained {space : Space} {name : String} {arguments : List Atom}
    {expected : Atom} {fuel : Nat} (typing : ApplicationTyping space name arguments expected fuel)
    (bindings : Bindings) (rows : ArgumentResults) (live : List Atom)
    (argumentsRun : Realizes space
      (.args arguments typing.domains bindings fuel (.symbol name :: live)) (argumentReplies rows)) :
    Realizes space
      (.func (.expression (.symbol name :: arguments)) (arrow typing.domains typing.returned)
        bindings (fuel + 1) live)
      (applications name rows) := by
  cases fuel with
  | zero => have := typing.headBudget; omega
  | succ fuel =>
      intro stack emitted
      have cast := symbol_cast_realizes space name (arrow typing.domains typing.returned)
        bindings fuel typing.before typing.after (arrow typing.domains typing.returned)
        typing.nonemptyOperator typing.sourceTypes
        typing.headClosed typing.headClosed typing.earlierClosed typing.earlierHeadRejects
        (Or.inr (Or.inr (Or.inr (Or.inr rfl)))) (by have := typing.headBudget; omega)
        (arrow typing.domains typing.returned :: arguments ++ live)
        (.heads (arrow typing.domains typing.returned) arguments (fuel + 1) live :: stack) emitted
      have resumed := consume_continuation space HE.GroundedDispatch.none
        (.heads (arrow typing.domains typing.returned) arguments (fuel + 1) live)
        [(.symbol name, bindings)] stack emitted
      have done := function_head_retained space name typing.domains typing.returned bindings (fuel + 1) live
        rows arguments typing.nonemptyOperator argumentsRun stack emitted
      have continuation := resumed.trans (by
        simpa only [RecursiveMachine.resume, List.nil_append] using done)
      have begin := enter_request space HE.GroundedDispatch.none
        (.func (.expression (.symbol name :: arguments)) (arrow typing.domains typing.returned)
          bindings (fuel + 1 + 1) live) stack emitted
      exact begin.trans (by
        simpa only [FirstSuccessRecursiveStrategy.enter, RecursiveMachine.enter,
          List.cons_append, List.nil_append] using cast.trans continuation)

/-- Typed argument alternatives enter the actual calls continuation. Its
outputs may change binding frames; all call occurrences and saved alternatives
are appended without replacing those outputs by their incoming bindings. -/

theorem binding_alternatives_retained {space : Space} {name : String} {arguments : List Atom}
    {expected : Atom} {fuel : Nat} (typing : ApplicationTyping space name arguments expected fuel)
    (bindings : Bindings) (rows : ArgumentResults) (count : Nat) (results : ResultSet)
    (live : List Atom)
    (argumentsRun : Realizes space (.args arguments typing.domains bindings fuel
      (.symbol name ::
        (if typing.returned = Atom.expressionType then Atom.undefinedType else typing.returned) ::
          live))
      (argumentReplies rows))
    (callsRun : Realizes space
      (.calls (if typing.returned = Atom.expressionType then Atom.undefinedType else typing.returned)
        (fuel + 1) (applications name rows)
        live)
      results) :
    Realizes space
      (.bindingAlternatives (.expression (.symbol name :: arguments)) (arrow typing.domains typing.returned)
        (if typing.returned = Atom.expressionType then Atom.undefinedType else typing.returned)
        (fuel + 1) (List.replicate count bindings) live)
      (List.replicate count results).flatten := by
  induction count with
  | zero =>
      intro stack emitted
      simpa [replies, FirstSuccessRecursiveStrategy.enter, RecursiveMachine.enter] using
        enter_request space HE.GroundedDispatch.none
          (.bindingAlternatives (.expression (.symbol name :: arguments))
            (arrow typing.domains typing.returned)
            (if typing.returned = Atom.expressionType then Atom.undefinedType else typing.returned)
            (fuel + 1) [] live) stack emitted
  | succ count ih =>
      intro stack emitted
      let callType := if typing.returned = Atom.expressionType then Atom.undefinedType else typing.returned
      let one := applications name rows
      let rest := Task.bindingAlternatives (.expression (.symbol name :: arguments))
        (arrow typing.domains typing.returned) callType (fuel + 1) (List.replicate count bindings) live
      have begin := enter_request space HE.GroundedDispatch.none
        (.bindingAlternatives (.expression (.symbol name :: arguments))
          (arrow typing.domains typing.returned) callType (fuel + 1)
          (List.replicate (count + 1) bindings) live) stack emitted
      have function := application_function_retained typing bindings rows (callType :: live) argumentsRun
        (.calls callType (fuel + 1) live :: .append rest :: stack) emitted
      have transfer := consume_continuation space HE.GroundedDispatch.none
        (.calls callType (fuel + 1) live) one (.append rest :: stack) emitted
      have calls := callsRun (.append rest :: stack) emitted
      have remainder := append_results space rest results
        (List.replicate count results).flatten ih stack emitted
      have collected := transfer.trans (by
        simpa only [RecursiveMachine.resume, List.nil_append, one] using calls.trans remainder)
      exact begin.trans (by
        simpa [FirstSuccessRecursiveStrategy.enter, RecursiveMachine.enter, List.replicate_succ,
          callType, one, rest, replies, List.map_append] using function.trans collected)

theorem application_retained_realizes {space : Space} {name : String} {arguments : List Atom}
    {expected : Atom} {fuel : Nat} (typing : ApplicationTyping space name arguments expected fuel)
    (bindings : Bindings) (rows : ArgumentResults) (results : ResultSet) (live : List Atom)
    (argumentsRun : Realizes space (.args arguments typing.domains bindings fuel
      (.symbol name ::
        (if typing.returned = Atom.expressionType then Atom.undefinedType else typing.returned) ::
          live))
      (argumentReplies rows))
    (callsRun : Realizes space
      (.calls (if typing.returned = Atom.expressionType then Atom.undefinedType else typing.returned)
        (fuel + 1) (applications name rows)
        live)
      results) :
    Realizes space (.atom (.expression (.symbol name :: arguments)) expected bindings (fuel + 3) live)
      (successPriority results) := by
  intro stack emitted
  let resultValues := results
  have atom := enter_request space HE.GroundedDispatch.none
    (.atom (.expression (.symbol name :: arguments)) expected bindings (fuel + 3) live) stack emitted
  have expression := enter_request space HE.GroundedDispatch.none
    (.expression (.expression (.symbol name :: arguments)) expected bindings (fuel + 2) live)
    (.filter :: stack) emitted
  have selection := enter_request space HE.GroundedDispatch.none
    (.functions (.expression (.symbol name :: arguments)) expected bindings (fuel + 1)
      (getAtomTypes space (.symbol name)) live) (.filter :: stack) emitted
  have alternatives := binding_alternatives_retained typing bindings rows
    1 results live argumentsRun callsRun
    (.filter :: stack) emitted
  have filtered := consume_continuation space HE.GroundedDispatch.none .filter resultValues
    stack emitted
  have selected := (application_selected typing bindings).1
  have done := alternatives.trans (by
    simpa only [RecursiveMachine.resume, List.nil_append, resultValues, List.replicate_one,
      List.flatten_cons, List.flatten_nil, List.append_nil] using filtered)
  have stepSelection := selection.trans (by
    simpa [FirstSuccessRecursiveStrategy.enter, selected, selectedPolicy] using done)
  have stepExpression := expression.trans (by
    simpa only [FirstSuccessRecursiveStrategy.enter, rawTypeLookup, List.nil_append] using
      stepSelection)
  have notRaw : expected ≠ .symbol "Atom" := typing.demandNotRaw
  have notExpression : expected ≠ .symbol "Expression" := typing.demandNotExpression
  exact atom.trans (by
    simpa [FirstSuccessRecursiveStrategy.enter, RecursiveMachine.enter, isEmptyOrError,
      isEmptyAtom, Atom.empty, Atom.unit, isErrorAtom, getMetaType, notRaw,
      notExpression, typing.cleanOperator, Nat.add_assoc] using stepExpression)

/-- Permuting relation lists preserves the complete visible-name inventory. -/
theorem bindingRecordPerm_queryVisible_iff {incoming other : Bindings}
    (related : BindingRecordPerm incoming other) (live : List Atom) (query : Atom) (name : String) :
    Spec.Eval.Steps.QueryVisibleName live query incoming name ↔
      Spec.Eval.Steps.QueryVisibleName live query other name := by
  simp only [Spec.Eval.Steps.QueryVisibleName, related.assignments.mem_iff,
    related.equalities.mem_iff]

/-- The same concrete simultaneous freshener remains hygienic after a
permutation of the caller's binding relation lists. -/
theorem bindingRecordPerm_alphaVariant_iff {incoming other : Bindings}
    (related : BindingRecordPerm incoming other) (live : List Atom) (query : Atom)
    (left right freshLeft freshRight : Atom) :
    Spec.Eval.Steps.AlphaVariantRel live query incoming left right freshLeft freshRight ↔
      Spec.Eval.Steps.AlphaVariantRel live query other left right freshLeft freshRight := by
  simp only [Spec.Eval.Steps.AlphaVariantRel, bindingRecordPerm_queryVisible_iff related]

/-- Failure to find an independently admitted rule depends on visible names,
not on the order of the caller's stored relations. -/
theorem bindingRecordPerm_noMatch {incoming other : Bindings}
    (related : BindingRecordPerm incoming other) (space : Space) (live : List Atom) (query : Atom)
    (absent : Spec.Eval.Steps.EquationQueryNoMatchRel space live query incoming) :
    Spec.Eval.Steps.EquationQueryNoMatchRel space live query other := by
  intro freshLeft freshRight matched rule
  obtain ⟨left, right, stored, alpha, matching⟩ := rule
  exact absent freshLeft freshRight matched ⟨left, right, stored,
    (bindingRecordPerm_alphaVariant_iff related live query left right freshLeft freshRight).mpr alpha, matching⟩

/-- One actual query work item is licensed locally by its physical source
occurrence and independent materialization. The declared concrete binding
comparison is transported locally; recursive evaluation is not a field. -/
structure EquationBodyEvidence (space : Space) (live : List Atom) (query expected : Atom)
    (incoming : Bindings) (candidate request : ResultPair)
    (comparison : SourceBindingComparison := .records) : Prop where
  transport : ∀ independentIncoming, comparison.FrameRelated incoming independentIncoming →
    ∃ independentMerged, comparison.FrameRelated request.2 independentMerged ∧
      (∃ position left right matched,
        candidate.1 = (freshenEquationAvoiding
          (equationScope live query expected incoming) position left right).2 ∧
        Spec.Eval.Steps.EquationQueryOccurrenceRel space (expected :: live) query independentIncoming.bindings
          position left right
          (freshenEquationAvoiding (equationScope live query expected incoming) position left right).1
          candidate.1 matched candidate.1 independentMerged.bindings) ∧
      independentMerged.Materialization candidate.1 request.1

/-- Existing literal-record witnesses embed through the historical profile.
The occurrence, materialization and returned record are all retained. -/
theorem EquationBodyEvidence.of_records_transport
    {space : Space} {live : List Atom} {query expected : Atom} {incoming : Bindings}
    {candidate request : ResultPair}
    (transport : ∀ independentIncoming, BindingRecordPerm incoming independentIncoming →
      ∃ independentMerged, BindingRecordPerm request.2 independentMerged ∧
        (∃ position left right,
          candidate.1 = (freshenEquationAvoiding
            (equationScope live query expected incoming) position left right).2 ∧
          Spec.Eval.Steps.EquationQueryOccurrenceRel space (expected :: live) query independentIncoming
            position left right
            (freshenEquationAvoiding (equationScope live query expected incoming) position left right).1
            candidate.1 candidate.2 candidate.1 independentMerged) ∧
        Spec.Type.Presentation.BindingTheory.BindingMaterializationRel
          independentMerged candidate.1 request.1) :
    EquationBodyEvidence space live query expected incoming candidate request := by
  refine ⟨?_⟩
  intro independent related
  cases related with
  | records related =>
    obtain ⟨merged, output, ⟨position, left, right, rhs, occurrence⟩, materialized⟩ :=
      transport _ related
    exact ⟨BindingFrame.historical merged, .records output,
      ⟨position, left, right, candidate.2, rhs, occurrence⟩, materialized⟩

/-- The retained query policy at a fully scoped call. -/
abbrev equationCandidates (space : Space) (live : List Atom) (query expected : Atom)
    (incoming : Bindings) (fuel : Nat) : ResultSet :=
  queryEquationsAvoiding (equationScope live query expected incoming) space query fuel

section ClosedQueryAdmission

open Spec.Type.RuntimeRefinement Spec.Type.Presentation.Theory
open Spec.Bindings.ScopeObservation

/-- A finite record of distinct keys with closed values and no aliases. -/
structure ClosedBindingFrame (bindings : Bindings) : Prop where
  noEqualities : bindings.equalities = []
  keys : (bindings.assignments.map Prod.fst).Nodup
  closed : ∀ name value, (name, value) ∈ bindings.assignments → TypeSubst.typeVars value = []

namespace ClosedBindingFrame

theorem empty : ClosedBindingFrame Bindings.empty :=
  ⟨rfl, by simp [Bindings.empty], by simp [Bindings.empty]⟩

theorem normal {bindings : Bindings} (frame : ClosedBindingFrame bindings) :
    TypeSubst.Normal bindings.assignments := by
  refine ⟨frame.keys, ?_⟩
  intro name value member key occurs
  simp [frame.closed name value member] at occurs

theorem satisfies {bindings : Bindings} (frame : ClosedBindingFrame bindings) :
    TypeBindingSatisfied (presentedValuation bindings.assignments) bindings := by
  refine ⟨normal_presentedValuation_satisfied frame.normal, ?_⟩
  intro left right member
  simp [frame.noEqualities] at member

theorem acyclic {bindings : Bindings} (frame : ClosedBindingFrame bindings) :
    Spec.Match.Merge.SemanticLoopFree bindings := by
  apply MatchSizeTheory.heSemanticLoopFree_of_satisfied_nonvariable
    (Spec.Bindings.ScopeObservation.ModelTransport.heBindingSatisfied_of_specTypeBindingSatisfied frame.satisfies)
  intro name value member
  have closed := frame.closed name (.var value) member
  simp [TypeSubst.typeVars] at closed

theorem noLoop {bindings : Bindings} (frame : ClosedBindingFrame bindings) :
    bindings.hasLoop = false :=
  (Spec.Match.Merge.hasLoop_eq_false_iff_semanticLoopFree bindings).mpr frame.acyclic

theorem lookup_none {bindings : Bindings} {name : String}
    (absent : name ∉ bindings.assignments.map Prod.fst) : bindings.lookup name = none := by
  apply List.lookup_eq_none_iff.mpr
  intro entry member
  apply bne_iff_ne.mpr
  intro equal
  exact absent (equal ▸ List.mem_map.mpr ⟨entry, member, rfl⟩)

theorem fresh_assign {bindings : Bindings} (frame : ClosedBindingFrame bindings)
    (name : String) (value : Atom) (absent : bindings.lookup name = none)
    (closed : TypeSubst.typeVars value = []) : ClosedBindingFrame (bindings.assign name value) := by
  have fresh : name ∉ bindings.assignments.map Prod.fst := by
    intro member
    obtain ⟨entry, entryMember, same⟩ := List.mem_map.mp member
    have neq := (List.lookup_eq_none_iff.mp absent) entry entryMember
    simp [same] at neq
  have assignment : bindings.assign name value =
      ⟨bindings.assignments ++ [(name, value)], bindings.equalities⟩ := by
    simp [Bindings.assign, Bindings.isBound, absent]
  rw [assignment]
  refine ⟨frame.noEqualities, ?_, ?_⟩
  · simpa only [List.map_append, List.map_cons, List.map_nil, List.concat_eq_append] using frame.keys.concat fresh
  · intro key atom member
    rcases List.mem_append.mp member with member | member
    · exact frame.closed key atom member
    · obtain pair := List.mem_singleton.mp member
      cases pair
      exact closed

theorem single (name : String) (value : Atom) (closed : TypeSubst.typeVars value = []) :
    ClosedBindingFrame (Bindings.empty.assign name value) :=
  empty.fresh_assign name value rfl closed

theorem applyFull {bindings : Bindings} (frame : ClosedBindingFrame bindings)
    (atom : Atom) (fuel : Nat) (enough : BindingComposition.atomDepth atom + 2 ≤ fuel) :
    bindings.applyFull atom fuel = applyTypeValuation (presentedValuation bindings.assignments) atom := by
  have represented : bindings = FirstSuccessPreparedArguments.presentedBindings bindings.assignments := by
    cases bindings with
    | mk assignments equalities =>
      exact congrArg (Bindings.mk assignments) frame.noEqualities
  conv_lhs => rw [represented]
  rw [FirstSuccessPreparedArguments.applyFull_presented frame.normal fuel atom enough,
    applyTypeValuation_presented_eq_apply]

end ClosedBindingFrame

theorem closed_match_membership {left right : Atom} {output : Bindings} {fuel : Nat}
    (leftClosed : TypeSubst.typeVars left = []) (rightClosed : TypeSubst.typeVars right = [])
    (member : output ∈ matchAtoms left right fuel) :
    left = right ∧ output = Bindings.empty := by
  let larger := max fuel (sizeOf left + sizeOf right + 2)
  have preserved := DeclMatchSpec.matchAtoms_mono left right fuel (larger - fuel) member
  have total : fuel + (larger - fuel) = larger := Nat.add_sub_of_le (Nat.le_max_left _ _)
  rw [total, (closed_match_exact larger).1 left right leftClosed rightClosed (Nat.le_max_right _ _)] at preserved
  split at preserved
  · exact ⟨by assumption, List.mem_singleton.mp preserved⟩
  · exact (List.not_mem_nil preserved).elim

theorem closed_match_failure {left right : Atom}
    (leftClosed : TypeSubst.typeVars left = []) (rightClosed : TypeSubst.typeVars right = [])
    (different : left ≠ right) (fuel : Nat) : matchAtoms left right fuel = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro output member
  exact different (closed_match_membership leftClosed rightClosed member).1

namespace ClosedBindingFrame

theorem lookup_closed {bindings : Bindings} (frame : ClosedBindingFrame bindings)
    {name : String} {value : Atom} (found : bindings.lookup name = some value) :
    TypeSubst.typeVars value = [] := by
  apply frame.closed name value
  apply TypeSubst.lookup_eq_some_mem
  rw [← FirstSuccessPreparedArguments.lookup_presented]
  exact found

/-- A repeated pattern variable is checked against its existing closed value;
it does not add a second assignment row. -/
theorem addVarBinding_cases {bindings output : Bindings} (frame : ClosedBindingFrame bindings)
    {name : String} {value : Atom} {fuel : Nat} (closed : TypeSubst.typeVars value = [])
    (member : output ∈ addVarBinding bindings name value fuel) :
    (bindings.lookup name = none ∧ output = bindings.assign name value) ∨
      (bindings.lookup name = some value ∧ output = bindings) := by
  cases fuel with
  | zero => simp [addVarBinding] at member
  | succ fuel =>
    rw [addVarBinding, Bindings.classValues_no_equalities frame.noEqualities] at member
    cases found : bindings.lookup name with
    | none =>
      simp only [found, Option.toList_none, List.mem_singleton] at member
      exact Or.inl ⟨rfl, member⟩
    | some previous =>
      have previousClosed := frame.lookup_closed found
      simp only [found, Option.toList_some, Bindings.valuesConsistent,
        List.all_nil, ite_true] at member
      by_cases same : previous = value
      · subst previous
        simp only [BEq.rfl, ite_true, List.mem_singleton] at member
        exact Or.inr ⟨rfl, member⟩
      · rw [if_neg (by simpa using same), closed_match_failure previousClosed closed same fuel] at member
        simp at member

theorem addVarBinding_source {bindings output : Bindings} (frame : ClosedBindingFrame bindings)
    {name : String} {value : Atom} {fuel : Nat} (closed : TypeSubst.typeVars value = [])
    (member : output ∈ addVarBinding bindings name value fuel) :
    Spec.Match.Merge.AddVarBindingRel Spec.Match.Merge.equalityGroundedSemantic bindings name value output ∧
      ClosedBindingFrame output := by
  rcases frame.addVarBinding_cases closed member with ⟨missing, rfl⟩ | ⟨found, rfl⟩
  · exact ⟨.fresh (by rw [Bindings.classValues_no_equalities frame.noEqualities, missing]; rfl),
      frame.fresh_assign name value missing closed⟩
  · refine ⟨.same (by rw [Bindings.classValues_no_equalities frame.noEqualities, found]; rfl) ?_ rfl, frame⟩
    simp [Spec.Match.Merge.ValuesAgree]

theorem constraints_of_no_equalities (bindings : Bindings)
    (unique : (bindings.assignments.map Prod.fst).Nodup) (noEqualities : bindings.equalities = []) :
    Spec.Match.Merge.constraints bindings = bindings.assignments.map
      (fun entry => Spec.Match.Merge.Constraint.value entry.1 entry.2) := by
  have pairsNodup : bindings.assignments.Nodup := List.Nodup.of_map _ unique
  have distinct : (bindings.assignments.map
      (fun entry => Spec.Match.Merge.Constraint.value entry.1 entry.2)).Nodup := by
    exact pairsNodup.map (by intro left right same; simpa only [Spec.Match.Merge.Constraint.value.injEq,
      Prod.ext_iff] using same)
  simp only [Spec.Match.Merge.constraints, noEqualities, List.map_nil, List.append_nil]
  generalize bindings.assignments.map _ = rows at distinct ⊢
  induction rows with
  | nil => rfl
  | cons row rows ih =>
    have split := List.nodup_cons.mp distinct
    rw [List.eraseDups_cons]
    have filtered : rows.filter (fun other => !other == row) = rows := by
      apply List.filter_eq_self.mpr
      intro other member
      have different : other ≠ row := fun same => split.1 (same ▸ member)
      simp [different]
    rw [filtered, ih split.2]

theorem constraints (bindings : Bindings) (frame : ClosedBindingFrame bindings) :
    Spec.Match.Merge.constraints bindings = bindings.assignments.map
      (fun entry => Spec.Match.Merge.Constraint.value entry.1 entry.2) :=
  constraints_of_no_equalities bindings frame.keys frame.noEqualities

/-- Each actual assignment-fold step has an independent merge-constraint
derivation and preserves the closed finite-map invariant. -/
theorem assignment_fold_source (fuel : Nat) (rows : List (String × Atom))
    (closed : ∀ name value, (name, value) ∈ rows → TypeSubst.typeVars value = [])
    (frontier : List Bindings) (frames : ∀ bindings ∈ frontier, ClosedBindingFrame bindings)
    {output : Bindings}
    (member : output ∈ rows.foldl (fun acc entry => acc.flatMap
      (fun bindings => addVarBinding bindings entry.1 entry.2 fuel)) frontier) :
    ∃ input ∈ frontier,
      Spec.Match.Merge.MergeConstraintsRel Spec.Match.Merge.equalityGroundedSemantic
        input (rows.map (fun entry => Spec.Match.Merge.Constraint.value entry.1 entry.2)) output ∧
      ClosedBindingFrame output := by
  induction rows generalizing frontier with
  | nil => exact ⟨output, member, .nil, frames output member⟩
  | cons entry rows ih =>
    rcases entry with ⟨name, value⟩
    have nextFrames : ∀ bindings ∈ frontier.flatMap
        (fun input => addVarBinding input name value fuel), ClosedBindingFrame bindings := by
      intro bindings present
      obtain ⟨input, initial, added⟩ := List.mem_flatMap.mp present
      exact ((frames input initial).addVarBinding_source
        (closed name value (by simp)) added).2
    obtain ⟨next, nextMember, tail, outputFrame⟩ :=
      ih (fun key atom present => closed key atom (by simp [present])) _ nextFrames member
    obtain ⟨input, initial, added⟩ := List.mem_flatMap.mp nextMember
    exact ⟨input, initial, .value ((frames input initial).addVarBinding_source
      (closed name value (by simp)) added).1 tail, outputFrame⟩

theorem merge_source {left right output : Bindings} (leftFrame : ClosedBindingFrame left)
    (rightFrame : ClosedBindingFrame right) {fuel : Nat}
    (member : output ∈ mergeBindings left right fuel) :
    Spec.Match.Merge.MergeRel Spec.Match.Merge.equalityGroundedSemantic left right output ∧
      ClosedBindingFrame output := by
  cases fuel with
  | zero => simp [mergeBindings] at member
  | succ fuel =>
    simp only [mergeBindings, rightFrame.noEqualities, List.foldl_nil] at member
    obtain ⟨input, initial, fold, outputFrame⟩ := assignment_fold_source fuel right.assignments
      rightFrame.closed [left] (by intro bindings present; simpa using List.mem_singleton.mp present ▸ leftFrame) member
    obtain rfl := List.mem_singleton.mp initial
    exact ⟨.mk (by rw [rightFrame.constraints]) fold, outputFrame⟩

theorem addVarBinding_supported {bindings output : Bindings} (frame : ClosedBindingFrame bindings)
    {name : String} {value : Atom} {fuel : Nat} (closed : TypeSubst.typeVars value = [])
    (member : output ∈ addVarBinding bindings name value fuel) (allowed : String → Prop)
    (before : ∀ key atom, (key, atom) ∈ bindings.assignments → allowed key)
    (added : allowed name) : ∀ key atom, (key, atom) ∈ output.assignments → allowed key := by
  rcases frame.addVarBinding_cases closed member with ⟨missing, rfl⟩ | ⟨_, rfl⟩
  · intro key atom present
    simp only [Bindings.assign, Bindings.isBound, missing, Option.isSome_none,
      Bool.false_eq_true, ite_false, List.mem_append, List.mem_singleton, Prod.mk.injEq] at present
    rcases present with present | ⟨rfl, _⟩
    · exact before key atom present
    · exact added
  · exact before

theorem merge_supported {left right output : Bindings} (leftFrame : ClosedBindingFrame left)
    (rightFrame : ClosedBindingFrame right) {fuel : Nat}
    (member : output ∈ mergeBindings left right fuel) (allowed : String → Prop)
    (leftKeys : ∀ key atom, (key, atom) ∈ left.assignments → allowed key)
    (rightKeys : ∀ key atom, (key, atom) ∈ right.assignments → allowed key) :
    ∀ key atom, (key, atom) ∈ output.assignments → allowed key := by
  cases fuel with
  | zero => simp [mergeBindings] at member
  | succ fuel =>
    simp only [mergeBindings, rightFrame.noEqualities, List.foldl_nil] at member
    have fold : ∀ (rows : List (String × Atom)) (frontier : List Bindings),
        (∀ key atom, (key, atom) ∈ rows → TypeSubst.typeVars atom = [] ∧ allowed key) →
        (∀ input ∈ frontier, ClosedBindingFrame input ∧
          ∀ key atom, (key, atom) ∈ input.assignments → allowed key) →
        ∀ out ∈ rows.foldl (fun acc entry => acc.flatMap
          (fun input => addVarBinding input entry.1 entry.2 fuel)) frontier,
        ∀ key atom, (key, atom) ∈ out.assignments → allowed key := by
      intro rows
      induction rows with
      | nil => intro frontier _ initial out present; exact (initial out present).2
      | cons entry rows ih =>
        rcases entry with ⟨name, value⟩
        intro frontier rowFacts initial out present
        apply ih _ (fun key atom mem => rowFacts key atom (by simp [mem])) ?_ out present
        intro next nextMember
        obtain ⟨input, inputMember, step⟩ := List.mem_flatMap.mp nextMember
        have inputFacts := initial input inputMember
        have addedFacts := rowFacts name value (by simp)
        exact ⟨(inputFacts.1.addVarBinding_source addedFacts.1 step).2,
          inputFacts.1.addVarBinding_supported addedFacts.1 step allowed inputFacts.2 addedFacts.2⟩
    exact fold right.assignments [left] (fun key atom mem =>
      ⟨rightFrame.closed key atom mem, rightKeys key atom mem⟩)
      (by intro input mem; obtain rfl := List.mem_singleton.mp mem; exact ⟨leftFrame, leftKeys⟩)
      output member

end ClosedBindingFrame

/-- A successful match against a closed input constructs the independent
matcher derivation. Repeated pattern variables are reconciled by the actual
assignment fold and retain one consistent row. -/
theorem closed_target_match_source {target pattern : Atom} {output : Bindings}
    (matched : DeclMatchSpec.MatchRel target pattern output)
    (closed : TypeSubst.typeVars target = []) :
    Spec.Match.Merge.MatchRel Spec.Match.Merge.equalityGroundedSemantic target pattern output ∧
      ClosedBindingFrame output := by
  induction matched using DeclMatchSpec.MatchRel.rec
    (motive_2 := fun lefts rights input out _ =>
      TypeSubst.typeVarsList lefts = [] → ClosedBindingFrame input →
      Spec.Match.Merge.MatchListAccRel Spec.Match.Merge.equalityGroundedSemantic lefts rights input out ∧
        ClosedBindingFrame out) with
  | symSym name => exact ⟨.symSym name ClosedBindingFrame.empty.acyclic, .empty⟩
  | varVar left right => simp [TypeSubst.typeVars] at closed
  | varNonVar nonvariable occurs => simp [TypeSubst.typeVars] at closed
  | @nonVarVar value name nonvariable occurs =>
    have frame := ClosedBindingFrame.single name value closed
    exact ⟨.nonVarVar (by cases value <;> simp_all [DeclMatchSpec.Atom.isVarB,
      Spec.Match.Merge.isVariableB]) frame.acyclic, frame⟩
  | grounded value =>
    exact ⟨.groundedLeftCustom rfl (by trivial) ⟨rfl, rfl⟩ ClosedBindingFrame.empty.acyclic, .empty⟩
  | @expr lefts rights output list acyclic ih =>
    have derived := ih closed ClosedBindingFrame.empty
    exact ⟨.expression derived.1 acyclic, derived.2⟩
  | nil => exact ⟨.nil, by assumption⟩
  | @cons left right lefts rights input head next output fuel headMatch merged tailMatch ihHead ihTail =>
    rename_i closed frame
    have parts : TypeSubst.typeVars left = [] ∧ TypeSubst.typeVarsList lefts = [] := by
      simpa only [TypeSubst.typeVarsList, List.append_eq_nil_iff] using closed
    obtain ⟨sourceHead, headFrame⟩ := ihHead parts.1
    obtain ⟨sourceMerge, nextFrame⟩ := frame.merge_source headFrame merged
    obtain ⟨sourceTail, outputFrame⟩ := ihTail parts.2 nextFrame
    exact ⟨.cons sourceHead sourceMerge sourceTail, outputFrame⟩

theorem closed_target_runtime_match_source {target pattern : Atom} {output : Bindings} {fuel : Nat}
    (closed : TypeSubst.typeVars target = [])
    (matched : output ∈ matchAtoms target pattern fuel) :
    Spec.Match.Merge.MatchRel Spec.Match.Merge.equalityGroundedSemantic target pattern output ∧
      ClosedBindingFrame output :=
  closed_target_match_source (DeclMatchSpec.matchAtoms_sound matched) closed

/-- A closed-input match can assign only variables physically present in its
pattern. This support law is what transfers declaration hygiene to all rows. -/
theorem closed_target_match_keys {target pattern : Atom} {output : Bindings}
    (matched : DeclMatchSpec.MatchRel target pattern output)
    (closed : TypeSubst.typeVars target = []) :
    ∀ key atom, (key, atom) ∈ output.assignments → key ∈ TypeSubst.typeVars pattern := by
  induction matched using DeclMatchSpec.MatchRel.rec
    (motive_2 := fun lefts rights input out _ =>
      TypeSubst.typeVarsList lefts = [] → ClosedBindingFrame input →
      ∀ key atom, (key, atom) ∈ out.assignments →
        key ∈ input.assignments.map Prod.fst ∨ key ∈ TypeSubst.typeVarsList rights) with
  | symSym name => simp
  | varVar left right => simp [TypeSubst.typeVars] at closed
  | varNonVar nonvariable occurs => simp [TypeSubst.typeVars] at closed
  | @nonVarVar value name nonvariable occurs =>
    intro key atom member
    have same : key = name := (Prod.mk.inj (List.mem_singleton.mp member)).1
    simp [TypeSubst.typeVars, same]
  | grounded value => simp
  | @expr lefts rights output list acyclic ih =>
    intro key atom member
    have supported := ih closed ClosedBindingFrame.empty key atom member
    simpa only [Bindings.empty, List.map_nil, List.not_mem_nil, false_or, TypeSubst.typeVars] using supported
  | nil =>
    rename_i _ frame key atom member
    exact Or.inl (List.mem_map.mpr ⟨(key, atom), member, rfl⟩)
  | @cons left right lefts rights input head next output fuel headMatch merged tailMatch ihHead ihTail =>
    rename_i closed frame key atom member
    have parts : TypeSubst.typeVars left = [] ∧ TypeSubst.typeVarsList lefts = [] := by
      simpa only [TypeSubst.typeVarsList, List.append_eq_nil_iff] using closed
    have headFrame := (closed_target_match_source headMatch parts.1).2
    have nextFrame := (frame.merge_source headFrame merged).2
    rcases ihTail parts.2 nextFrame key atom member with nextKey | tailKey
    · obtain ⟨entry, entryMember, same⟩ := List.mem_map.mp nextKey
      have supported := frame.merge_supported headFrame merged
        (fun name => name ∈ input.assignments.map Prod.fst ∨ name ∈ TypeSubst.typeVars right)
        (fun name value mem => Or.inl (List.mem_map.mpr ⟨(name, value), mem, rfl⟩))
        (fun name value mem => Or.inr (ihHead parts.1 name value mem)) entry.1 entry.2 entryMember
      rw [same] at supported
      rcases supported with initial | headKey
      · exact Or.inl initial
      · exact Or.inr (by simp [TypeSubst.typeVarsList, headKey])
    · exact Or.inr (by simp [TypeSubst.typeVarsList, tailKey])

theorem normal_record_model {bindings : Bindings} (noEqualities : bindings.equalities = [])
    (normal : TypeSubst.Normal bindings.assignments) :
    TypeBindingSatisfied (presentedValuation bindings.assignments) bindings := by
  exact ⟨normal_presentedValuation_satisfied normal, by simp [noEqualities]⟩

theorem normal_record_acyclic {bindings : Bindings} (noEqualities : bindings.equalities = [])
    (normal : TypeSubst.Normal bindings.assignments) : Spec.Match.Merge.SemanticLoopFree bindings := by
  have endpoints : ∀ source target, Spec.Match.Merge.ClassDepends bindings source target →
      source ∈ TypeSubst.keys bindings.assignments ∧ target ∉ TypeSubst.keys bindings.assignments := by
    intro source target edge
    obtain ⟨key, value, dependency, member, sourceClass, occurs, targetClass, _⟩ := edge
    have sourceEq : source = key := by
      simpa [Bindings.eqClass, Bindings.eqClassAux, Bindings.eqStep, noEqualities] using sourceClass
    have targetEq : target = dependency := by
      simpa [Bindings.eqClass, Bindings.eqClassAux, Bindings.eqStep, noEqualities] using targetClass
    subst source
    subst target
    refine ⟨List.mem_map.mpr ⟨(key, value), member, rfl⟩, normal.2 key value member dependency ?_⟩
    rw [TypeSubst.typeVars_eq_vars]
    exact Spec.Match.Merge.mem_vars_iff_atomOccurs.mpr occurs
  have paths : ∀ source target, Relation.TransGen (Spec.Match.Merge.ClassDepends bindings) source target →
      source ∈ TypeSubst.keys bindings.assignments ∧ target ∉ TypeSubst.keys bindings.assignments := by
    intro source target path
    induction path with
    | single edge => exact endpoints _ _ edge
    | tail path edge ih => exact ⟨ih.1, (endpoints _ _ edge).2⟩
  intro name loop
  have impossible := paths name name loop
  exact impossible.2 impossible.1

theorem normal_record_perm {left right : Bindings} (related : BindingRecordPerm left right)
    (normal : TypeSubst.Normal left.assignments) : TypeSubst.Normal right.assignments := by
  refine ⟨(related.assignments.map Prod.fst).nodup_iff.mp normal.1, ?_⟩
  intro name value member key occurs found
  exact normal.2 name value (related.assignments.mem_iff.mpr member) key occurs
    ((related.assignments.map Prod.fst).mem_iff.mpr found)

theorem normal_append_closed {incoming matched : Bindings}
    (normal : TypeSubst.Normal incoming.assignments) (frame : ClosedBindingFrame matched)
    (fresh : ∀ key ∈ matched.assignments.map Prod.fst, key ∉ specBindingVars incoming) :
    TypeSubst.Normal (matched.assignments ++ incoming.assignments) := by
  have distinct : List.Disjoint (matched.assignments.map Prod.fst) (incoming.assignments.map Prod.fst) := by
    apply List.disjoint_left.mpr
    intro key inMatch inCaller
    obtain ⟨entry, member, same⟩ := List.mem_map.mp inCaller
    apply fresh key inMatch
    simp only [specBindingVars, List.mem_append, List.mem_flatMap]
    exact Or.inl ⟨entry, member, by simp [same]⟩
  refine ⟨?_, ?_⟩
  · simpa only [TypeSubst.keys, List.map_append] using
      List.nodup_append.mpr ⟨frame.keys, normal.1, by
        intro a ha b hb same
        subst b
        exact List.disjoint_left.mp distinct ha hb⟩
  · intro name value member key occurs
    rcases List.mem_append.mp member with matchedMember | incomingMember
    · simp [frame.closed name value matchedMember] at occurs
    · simp only [TypeSubst.keys, List.map_append, List.mem_append, not_or]
      refine ⟨?_, normal.2 name value incomingMember key occurs⟩
      intro matchedKey
      apply fresh key matchedKey
      simp only [specBindingVars, List.mem_append, List.mem_flatMap]
      exact Or.inl ⟨(name, value), incomingMember, by simp [occurs]⟩

/-- Fresh assignment rows are appended by the real merge fold, irrespective
of their values. Thus a caller's open values are retained without evaluation. -/
theorem fresh_assignment_fold_exact (fuel : Nat) (rows : List (String × Atom))
    (unique : (rows.map Prod.fst).Nodup) (initial : Bindings)
    (fresh : List.Disjoint (initial.assignments.map Prod.fst) (rows.map Prod.fst))
    {output : Bindings}
    (member : output ∈ rows.foldl (fun acc entry => acc.flatMap
      (fun bindings => addVarBinding bindings entry.1 entry.2 fuel)) [initial])
    (noEqualities : initial.equalities = []) :
    output = ⟨initial.assignments ++ rows, []⟩ := by
  induction rows generalizing initial with
  | nil =>
    obtain rfl := List.mem_singleton.mp member
    cases output with
    | mk assignments equalities => simpa using congrArg (Bindings.mk assignments) noEqualities
  | cons entry rows ih =>
    rcases entry with ⟨key, value⟩
    have parts := List.nodup_cons.mp unique
    have absent : initial.lookup key = none := ClosedBindingFrame.lookup_none (by
      intro present
      exact List.disjoint_left.mp fresh present (by simp))
    cases fuel with
    | zero =>
      have emptyFold : ∀ remaining : List (String × Atom),
          remaining.foldl (fun acc entry => acc.flatMap
            (fun bindings => addVarBinding bindings entry.1 entry.2 0)) [] = [] := by
        intro remaining
        induction remaining with
        | nil => rfl
        | cons entry remaining ih => simpa using ih
      simp only [List.foldl_cons, List.flatMap_cons, List.flatMap_nil, List.append_nil,
        addVarBinding] at member
      change output ∈ rows.foldl (fun acc entry => acc.flatMap
        (fun bindings => addVarBinding bindings entry.1 entry.2 0)) [] at member
      rw [emptyFold] at member
      exact (List.not_mem_nil member).elim
    | succ fuel =>
      have added : addVarBinding initial key value (fuel + 1) = [initial.assign key value] := by
        rw [addVarBinding, Bindings.classValues_no_equalities noEqualities, absent]
        rfl
      simp only [List.foldl_cons, List.flatMap_cons, List.flatMap_nil, List.append_nil, added] at member
      have assigned : initial.assign key value =
          (⟨initial.assignments ++ [(key, value)], []⟩ : Bindings) := by
        simp [Bindings.assign, Bindings.isBound, absent, noEqualities]
      have disjoint : List.Disjoint ((initial.assign key value).assignments.map Prod.fst)
          (rows.map Prod.fst) := by
        rw [assigned]
        simp only [List.map_append, List.map_cons, List.map_nil, List.disjoint_append_left]
        refine ⟨?_, List.disjoint_left.mpr (by
          intro name present found
          obtain rfl := List.mem_singleton.mp present
          exact parts.1 found)⟩
        exact List.disjoint_left.mpr (fun name present other =>
          List.disjoint_left.mp fresh present (by simp [other]))
      have result := ih parts.2 (initial.assign key value) disjoint member (by rw [assigned])
      simpa only [assigned, List.append_assoc, List.singleton_append] using result

theorem fresh_merge_exact {left right output : Bindings} {fuel : Nat}
    (leftNoEq : left.equalities = []) (rightNoEq : right.equalities = [])
    (rightUnique : (right.assignments.map Prod.fst).Nodup)
    (fresh : List.Disjoint (left.assignments.map Prod.fst) (right.assignments.map Prod.fst))
    (member : output ∈ mergeBindings left right fuel) :
    output = ⟨left.assignments ++ right.assignments, []⟩ := by
  cases fuel with
  | zero => simp [mergeBindings] at member
  | succ fuel =>
    simp only [mergeBindings, rightNoEq, List.foldl_nil] at member
    exact fresh_assignment_fold_exact fuel right.assignments rightUnique left fresh member leftNoEq

/-- Independent merging admits the same fresh assignment rows in their
physical order, without requiring the caller's stored values to be closed. -/
theorem fresh_constraints_source (rows : List (String × Atom))
    (unique : (rows.map Prod.fst).Nodup) (initial : Bindings)
    (fresh : List.Disjoint (initial.assignments.map Prod.fst) (rows.map Prod.fst))
    (noEqualities : initial.equalities = []) :
    Spec.Match.Merge.MergeConstraintsRel Spec.Match.Merge.equalityGroundedSemantic initial
      (rows.map (fun entry => Spec.Match.Merge.Constraint.value entry.1 entry.2))
      ⟨initial.assignments ++ rows, []⟩ := by
  induction rows generalizing initial with
  | nil =>
    have same : (⟨initial.assignments ++ [], []⟩ : Bindings) = initial := by
      cases initial
      simp_all
    rw [same]
    exact .nil
  | cons entry rows ih =>
    rcases entry with ⟨key, value⟩
    have parts := List.nodup_cons.mp unique
    have absent : initial.lookup key = none := ClosedBindingFrame.lookup_none (by
      intro present
      exact List.disjoint_left.mp fresh present (by simp))
    have assigned : initial.assign key value =
        (⟨initial.assignments ++ [(key, value)], []⟩ : Bindings) := by
      simp [Bindings.assign, Bindings.isBound, absent, noEqualities]
    have disjoint : List.Disjoint ((initial.assign key value).assignments.map Prod.fst)
        (rows.map Prod.fst) := by
      rw [assigned]
      simp only [List.map_append, List.map_cons, List.map_nil, List.disjoint_append_left]
      refine ⟨?_, List.disjoint_left.mpr (by
          intro name present found
          obtain rfl := List.mem_singleton.mp present
          exact parts.1 found)⟩
      exact List.disjoint_left.mpr (fun name present other =>
        List.disjoint_left.mp fresh present (by simp [other]))
    have tail := ih parts.2 (initial.assign key value) disjoint (by rw [assigned])
    have step : Spec.Match.Merge.AddVarBindingRel Spec.Match.Merge.equalityGroundedSemantic
        initial key value (initial.assign key value) :=
      .fresh (by rw [Bindings.classValues_no_equalities noEqualities, absent]; rfl)
    simpa only [List.map_cons, assigned, List.append_assoc, List.singleton_append] using
      Spec.Match.Merge.MergeConstraintsRel.value step tail

/-- A fresh one-variable rule extension has an independent query realization
under every layout of an equality-free caller frame. The matcher, hygiene,
model and materialization premises are local source facts, not body execution. -/
theorem EquationBodyEvidence.fresh_assignment
    {space : Space} {live : List Atom} {query expected : Atom} {incoming : Bindings}
    {candidate request : ResultPair} (position : Nat) (left right : Atom)
    (key : String) (value : Atom)
    (stored : space.atoms[position]? = some (.expression [.symbol "=", left, right]))
    (rhs : candidate.1 = (freshenEquationAvoiding
      (equationScope live query expected incoming) position left right).2)
    (alpha : Spec.Eval.Steps.AlphaVariantRel (expected :: live) query incoming left right
      (freshenEquationAvoiding (equationScope live query expected incoming) position left right).1
      candidate.1)
    (matching : Spec.Match.Merge.MatchRel Spec.Match.Merge.equalityGroundedSemantic query
      (freshenEquationAvoiding (equationScope live query expected incoming) position left right).1
      candidate.2)
    (matched : candidate.2 = Bindings.empty.assign key value)
    (noEqualities : incoming.equalities = [])
    (unique : (incoming.assignments.map Prod.fst).Nodup)
    (fresh : ∀ old, (key, old) ∉ incoming.assignments)
    (output : BindingRecordPerm request.2 ⟨(key, value) :: incoming.assignments, []⟩)
    (model : ∃ valuation, Spec.Type.RuntimeRefinement.TypeBindingSatisfied valuation request.2)
    (forced : ∀ valuation, Spec.Type.RuntimeRefinement.TypeBindingSatisfied valuation request.2 →
      Spec.Type.RuntimeRefinement.applyTypeValuation valuation candidate.1 = request.1) :
    EquationBodyEvidence space live query expected incoming candidate request := by
  refine EquationBodyEvidence.of_records_transport ?_
  intro independent related
  have noEqualities' : independent.equalities = [] := by
    have permutation := related.equalities
    rw [noEqualities] at permutation
    exact (List.Perm.nil_eq permutation).symm
  have fresh' : ∀ old, (key, old) ∉ independent.assignments := by
    intro old member
    exact fresh old (related.assignments.mem_iff.mpr member)
  let independentMerged : Bindings := ⟨(key,value)::independent.assignments,[]⟩
  have outputRelated : BindingRecordPerm request.2 independentMerged :=
    output.trans ⟨List.Perm.cons (key,value) related.assignments,.refl _⟩
  have independentUnique := (related.assignments.map Prod.fst).nodup_iff.mp unique
  have disjoint : List.Disjoint ((Bindings.empty.assign key value).assignments.map Prod.fst)
      (independent.assignments.map Prod.fst) := by
    apply List.disjoint_left.mpr
    intro name owned present
    have same : name=key := by simpa [Bindings.empty,Bindings.assign,Bindings.isBound,Bindings.lookup] using owned
    subst name
    obtain ⟨row,member,same⟩:=List.mem_map.mp present
    exact fresh' row.2 (same ▸ member)
  have sourceMerge : Spec.Match.Merge.MergeRel Spec.Match.Merge.equalityGroundedSemantic
      (Bindings.empty.assign key value) independent independentMerged := by
    apply Spec.Match.Merge.MergeRel.mk
      (order:=independent.assignments.map (fun row=>Spec.Match.Merge.Constraint.value row.1 row.2))
    · rw [ClosedBindingFrame.constraints_of_no_equalities independent independentUnique noEqualities']
    · simpa [independentMerged,Bindings.empty,Bindings.assign,Bindings.isBound,Bindings.lookup] using
        fresh_constraints_source independent.assignments independentUnique
          (Bindings.empty.assign key value) disjoint rfl
  have materialized : Spec.Type.Presentation.BindingTheory.BindingMaterializationRel
      independentMerged candidate.1 request.1 := by
    apply Spec.Type.Presentation.BindingTheory.BindingMaterializationRel.of_model_constant
    · obtain ⟨valuation, satisfied⟩ := model
      exact ⟨valuation, (outputRelated.satisfied_iff valuation).mp satisfied⟩
    · intro valuation satisfied
      exact forced valuation ((outputRelated.satisfied_iff valuation).mpr satisfied)
  refine ⟨independentMerged, outputRelated,
    ⟨position, left, right, rhs, ?_⟩, materialized⟩
  refine ⟨stored,
    ⟨(bindingRecordPerm_alphaVariant_iff related _ _ _ _ _ _).mp alpha, matching⟩,
    ?_⟩
  refine ⟨?_, fun _ _ => rfl⟩
  rw [matched]
  apply sourceMerge.logicalMerge
  obtain ⟨valuation, satisfied⟩ := model
  exact ⟨valuation, (outputRelated.satisfied_iff valuation).mp satisfied⟩

/-- An equation whose match adds no constraints preserves the caller's
binding theory under each relation-list layout. Its body readout is still
proved from the source model and is not assumed to have executed. -/
theorem EquationBodyEvidence.empty_match
    {space : Space} {live : List Atom} {query expected : Atom} {incoming : Bindings}
    {candidate request : ResultPair} (position : Nat) (left right : Atom)
    (stored : space.atoms[position]? = some (.expression [.symbol "=", left, right]))
    (rhs : candidate.1 = (freshenEquationAvoiding
      (equationScope live query expected incoming) position left right).2)
    (alpha : Spec.Eval.Steps.AlphaVariantRel (expected :: live) query incoming left right
      (freshenEquationAvoiding (equationScope live query expected incoming) position left right).1
      candidate.1)
    (matching : Spec.Match.Merge.MatchRel Spec.Match.Merge.equalityGroundedSemantic query
      (freshenEquationAvoiding (equationScope live query expected incoming) position left right).1 candidate.2)
    (matched : candidate.2 = Bindings.empty)
    (noEqualities : incoming.equalities = [])
    (unique : (incoming.assignments.map Prod.fst).Nodup)
    (output : BindingRecordPerm request.2 incoming)
    (model : ∃ valuation, Spec.Type.RuntimeRefinement.TypeBindingSatisfied valuation request.2)
    (forced : ∀ valuation, Spec.Type.RuntimeRefinement.TypeBindingSatisfied valuation request.2 →
      Spec.Type.RuntimeRefinement.applyTypeValuation valuation candidate.1 = request.1) :
    EquationBodyEvidence space live query expected incoming candidate request := by
  refine EquationBodyEvidence.of_records_transport ?_
  intro independent related
  have outputRelated := output.trans related
  have independentNoEq : independent.equalities=[] := by
    have permutation:=related.equalities
    rw [noEqualities] at permutation
    exact (List.Perm.nil_eq permutation).symm
  have independentUnique := (related.assignments.map Prod.fst).nodup_iff.mp unique
  have materialized : Spec.Type.Presentation.BindingTheory.BindingMaterializationRel
      independent candidate.1 request.1 := by
    apply Spec.Type.Presentation.BindingTheory.BindingMaterializationRel.of_model_constant
    · obtain ⟨valuation, satisfied⟩ := model
      exact ⟨valuation, (outputRelated.satisfied_iff valuation).mp satisfied⟩
    · intro valuation satisfied
      exact forced valuation ((outputRelated.satisfied_iff valuation).mpr satisfied)
  refine ⟨independent, outputRelated, ⟨position, left, right, rhs, ?_⟩, materialized⟩
  refine ⟨stored, ⟨(bindingRecordPerm_alphaVariant_iff related _ _ _ _ _ _).mp alpha, matching⟩,
    ?_⟩
  refine ⟨?_, fun _ _ => rfl⟩
  apply Spec.Match.Merge.MergeRel.logicalMerge
  · rw [matched]
    apply Spec.Match.Merge.MergeRel.mk
      (order:=independent.assignments.map (fun row=>Spec.Match.Merge.Constraint.value row.1 row.2))
    · rw [ClosedBindingFrame.constraints_of_no_equalities independent independentUnique independentNoEq]
    · have folded := fresh_constraints_source independent.assignments independentUnique Bindings.empty
        (by simp [Bindings.empty]) rfl
      have same : (⟨independent.assignments,[]⟩ : Bindings)=independent := by
        cases independent
        simp_all
      simpa only [Bindings.empty,List.nil_append,same] using folded
  · obtain ⟨valuation, satisfied⟩ := model
    exact ⟨valuation, (outputRelated.satisfied_iff valuation).mp satisfied⟩

theorem alphaVariant_pattern_fresh {live : List Atom} {query left right freshLeft freshRight : Atom}
    {incoming : Bindings}
    (alpha : Spec.Eval.Steps.AlphaVariantRel live query incoming left right freshLeft freshRight) :
    ∀ key ∈ TypeSubst.typeVars freshLeft, key ∉ specBindingVars incoming := by
  obtain ⟨rename, _, lhs, _, avoids⟩ := alpha
  rw [EquationFreshening.alphaRename_eq lhs,
    Spec.Type.Presentation.ScopeObservation.typeVars_renameTypeVars]
  intro key renamedMember bindingMember
  obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp renamedMember
  apply avoids original (Or.inl ?_) ?_
  · rw [TypeSubst.typeVars_eq_vars] at originalMember
    exact Spec.Match.Merge.mem_vars_iff_atomOccurs.mp originalMember
  · simp only [specBindingVars, List.mem_append, List.mem_flatMap] at bindingMember
    rcases bindingMember with ⟨entry, member, occurs⟩ | ⟨entry, member, endpoint⟩
    · rcases List.mem_cons.mp occurs with same | valueOccurs
      · exact Or.inr (Or.inr (Or.inl ⟨entry.2, same ▸ member⟩))
      · apply Or.inr ∘ Or.inr ∘ Or.inr ∘ Or.inl
        refine ⟨entry.1, entry.2, member, ?_⟩
        rw [TypeSubst.typeVars_eq_vars] at valueOccurs
        exact Spec.Match.Merge.mem_vars_iff_atomOccurs.mp valueOccurs
    · apply Or.inr ∘ Or.inr ∘ Or.inr ∘ Or.inr
      exact ⟨entry.1, entry.2, member, by simpa using endpoint⟩

theorem alphaVariant_covered {live : List Atom} {query left right freshLeft freshRight : Atom}
    {incoming : Bindings}
    (alpha : Spec.Eval.Steps.AlphaVariantRel live query incoming left right freshLeft freshRight)
    (covered : ∀ key ∈ TypeSubst.typeVars right, key ∈ TypeSubst.typeVars left) :
    ∀ key ∈ TypeSubst.typeVars freshRight, key ∈ TypeSubst.typeVars freshLeft := by
  obtain ⟨rename, _, lhs, rhs, _⟩ := alpha
  rw [EquationFreshening.alphaRename_eq lhs, EquationFreshening.alphaRename_eq rhs,
    Spec.Type.Presentation.ScopeObservation.typeVars_renameTypeVars,
    Spec.Type.Presentation.ScopeObservation.typeVars_renameTypeVars]
  intro key member
  obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp member
  exact List.mem_map.mpr ⟨original, covered original originalMember, rfl⟩

theorem closed_valuation (valuation : String → Atom) {atom : Atom}
    (closed : TypeSubst.typeVars atom = []) : applyTypeValuation valuation atom = atom := by
  calc
    applyTypeValuation valuation atom = applyTypeValuation (fun name => .var name) atom := by
      apply (applyTypeValuation_eq_iff_on_typeVars valuation (fun name => .var name) atom).mpr
      simp [closed]
    _ = atom := applyTypeValuation_var_identity atom

theorem runtime_match_type_solution {left right : Atom} {bindings : Bindings} {fuel : Nat}
    (matched : bindings ∈ matchAtoms left right fuel) (valuation : String → Atom)
    (satisfied : TypeBindingSatisfied valuation bindings) :
    applyTypeValuation valuation left = applyTypeValuation valuation right := by
  apply Spec.Match.SolutionTheory.encodeModelAtom_injective
  simp only [Spec.Bindings.ScopeObservation.ModelTransport.encodeModelAtom_applyTypeValuation]
  exact (BindingComposition.matchAtoms_solution_iff matched _).mp
    (Spec.Bindings.ScopeObservation.ModelTransport.heBindingSatisfied_of_specTypeBindingSatisfied satisfied)

theorem runtime_merge_type_solution {left right output : Bindings} {fuel : Nat}
    (merged : output ∈ mergeBindings left right fuel) (valuation : String → Atom)
    (satisfied : TypeBindingSatisfied valuation output) :
    TypeBindingSatisfied valuation left ∧ TypeBindingSatisfied valuation right := by
  have parts := (BindingComposition.mergeBindings_solution_iff merged _).mp
    (Spec.Bindings.ScopeObservation.ModelTransport.heBindingSatisfied_of_specTypeBindingSatisfied satisfied)
  constructor
  · simpa only [Spec.Match.SolutionTheory.decodeModelAtom_encodeModelAtom] using
      Spec.Bindings.ScopeObservation.ModelTransport.specTypeBindingSatisfied_of_heBindingSatisfied parts.1
  · simpa only [Spec.Match.SolutionTheory.decodeModelAtom_encodeModelAtom] using
      Spec.Bindings.ScopeObservation.ModelTransport.specTypeBindingSatisfied_of_heBindingSatisfied parts.2

end ClosedQueryAdmission
end Mettapedia.Languages.MeTTa.HE.FirstSuccessSourceExecution

/-! ## Protected private matches with alias-bearing callers -/

namespace Mettapedia.Languages.MeTTa.HE.FreshPrivateMerge

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.SubstitutionAlgebra (vars)

open Spec.Bindings.ScopeObservation FirstSuccessSourceExecution Spec.Type.Presentation

theorem ClosedBindingFrame.readFrame {bindings : Bindings}
    (frame : FirstSuccessSourceExecution.ClosedBindingFrame bindings)
    (keys : String → Prop) : ReadFrame keys bindings.lookup bindings := by
  refine ⟨?_, ?_, fun _ _ => rfl⟩
  · intro key value present name occurs
    have closed : vars value = [] := by
      rw [← TypeSubst.typeVars_eq_vars, frame.closed key value present]
    simp [closed] at occurs
  · intro left right present
    simp [frame.noEqualities] at present

/-- The actual candidate-first merge protects each private closed assignment
through all caller reconciliation, without imposing a caller layout or model. -/
theorem merge_closed_private {matched caller out : Bindings} {fuel : Nat}
    (frame : FirstSuccessSourceExecution.ClosedBindingFrame matched)
    (fresh : ∀ key ∈ matched.assignments.map Prod.fst, key ∉ specBindingVars caller)
    (member : out ∈ mergeBindings matched caller fuel) :
    ReadFrame (fun key => key ∈ matched.assignments.map Prod.fst) matched.lookup out :=
  (frame_family (fun key => key ∈ matched.assignments.map Prod.fst) fuel).2.2.1
    matched.lookup matched caller out (ClosedBindingFrame.readFrame frame _)
    (readFrame_of_fresh fresh) member

/-- Readout on the private component ignores arbitrary unrelated alias
reconciliation. This equality includes shallow and exhausted read budgets. -/
theorem ReadFrame.applyFull_eq {keys : String → Prop} {matched out : Bindings}
    (frame : FirstSuccessSourceExecution.ClosedBindingFrame matched)
    (output : ReadFrame keys matched.lookup out) (atom : Atom) (fuel : Nat)
    (supported : ∀ key ∈ TypeSubst.typeVars atom, keys key) :
    out.applyFull atom fuel = matched.applyFull atom fuel := by
  induction fuel generalizing atom with
  | zero => rfl
  | succ fuel ih =>
    cases atom with
    | symbol | grounded => rfl
    | var key =>
      have owned := supported key (by simp [TypeSubst.typeVars])
      simp only [Bindings.applyFull,
        resolveFull_eq_of_closed_singleton
          (Bindings.eqClassOrdered_no_equalities frame.noEqualities key)
          (output.orderedClass owned) (output.reads key owned)
          (fun value found => frame.lookup_closed found) fuel]
    | expression atoms =>
      simp only [Bindings.applyFull]
      congr 1
      apply List.map_congr_left
      intro atom member
      apply ih atom
      intro key occurs
      exact supported key
        (Freshness.typeVars_mem_typeVarsList_of_mem member key occurs)

/-- A scoped private region may include residual holes as well as the keys
actually assigned by matching. Caller operations cannot capture either. -/
theorem merge_closed_frame {matched caller out : Bindings} {fuel : Nat}
    (frame : FirstSuccessSourceExecution.ClosedBindingFrame matched)
    (keys : String → Prop)
    (fresh : ∀ key, keys key → key ∉ specBindingVars caller)
    (member : out ∈ mergeBindings matched caller fuel) :
    ReadFrame keys matched.lookup out :=
  (frame_family keys fuel).2.2.1 matched.lookup matched caller out
    (ClosedBindingFrame.readFrame frame keys) (readFrame_of_fresh fresh) member

/-- The actual candidate-first merge has the same private-body materialization
as the matched component, at every read budget. It does not rewrite the stored
caller or erase duplicate equality occurrences. -/
theorem merge_closed_materialization {matched caller out : Bindings} {fuel : Nat}
    (frame : FirstSuccessSourceExecution.ClosedBindingFrame matched)
    (atom : Atom) (fresh : ∀ key ∈ TypeSubst.typeVars atom, key ∉ specBindingVars caller)
    (member : out ∈ mergeBindings matched caller fuel) (readFuel : Nat) :
    out.applyFull atom readFuel = matched.applyFull atom readFuel :=
  (merge_closed_frame frame (fun key => key ∈ TypeSubst.typeVars atom) fresh member).applyFull_eq
    frame atom readFuel (fun _ member => member)

/-- Constructive source endpoint for the actual closed matched component.
Only the independent source append order is chosen; the native checkpoint
continues to retain its own exact record. -/
theorem closed_source_merge {matched caller : Bindings}
    (frame : FirstSuccessSourceExecution.ClosedBindingFrame matched)
    (fresh : ∀ key ∈ matched.assignments.map Prod.fst, key ∉ specBindingVars caller) :
    Spec.Match.Merge.MergeRel Spec.Match.Merge.equalityGroundedSemantic caller matched
      ⟨caller.assignments ++ matched.assignments, caller.equalities⟩ := by
  apply Spec.Match.Merge.MergeRel.mk
    (order := matched.assignments.map (fun entry => Spec.Match.Merge.Constraint.value entry.1 entry.2))
  · rw [frame.constraints]
  · exact closed_constraints_source matched.assignments frame.keys frame.closed caller fresh



end Mettapedia.Languages.MeTTa.HE.FreshPrivateMerge

namespace Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Spec.Type.Presentation Spec.Type.Presentation.Theory Spec.Type.RuntimeRefinement Spec.Bindings.ScopeObservation
open Spec.Match.ModelTheory FirstSuccessSourceExecution FreshPrivateMerge

namespace FreshPrivateMerge

theorem runtime_merge_type_solution_iff {left right output : Bindings} {fuel : Nat}
    (member : output∈mergeBindings left right fuel) (valuation : String→Atom) :
    TypeBindingSatisfied valuation output ↔
      TypeBindingSatisfied valuation left ∧ TypeBindingSatisfied valuation right := by
  simp only [Spec.Bindings.ScopeObservation.ModelTransport.specTypeBindingSatisfied_iff_heBindingSatisfied_translated]
  exact BindingComposition.mergeBindings_solution_iff member _

/-- Extend an actual caller model only on the fresh closed match keys. -/
theorem closed_private_common_model {matched caller : Bindings}
    (frame : ClosedBindingFrame matched)
    (fresh : ∀ key∈matched.assignments.map Prod.fst,key∉specBindingVars caller)
    {valuation : String→Atom} (model : TypeBindingSatisfied valuation caller) :
    ∃ extended,TypeBindingSatisfied extended matched ∧ TypeBindingSatisfied extended caller := by
  let extended := extendThroughPresentation valuation matched.assignments
  have incoming : TypeBindingSatisfied extended caller :=
    extendThroughPresentation_preserves_binding
      (fun key present owned=>fresh key owned present) model
  have privateModel := extendThroughPresentation_satisfied frame.normal valuation
  exact ⟨extended,⟨privateModel,by simp [frame.noEqualities]⟩,incoming⟩

/-- Successful reconciliation of a fresh closed matched component earns a
principal runtime checkpoint. A finite caller model and assignment shape
suffice; the incoming caller need not already have canonical coherence. -/
theorem closed_private_principal {matched caller out : Bindings} {fuel : Nat}
    (frame : ClosedBindingFrame matched)
    (fresh : ∀ key ∈ matched.assignments.map Prod.fst, key ∉ specBindingVars caller)
    (model : ∃ valuation, TypeBindingSatisfied valuation caller)
    (shape : AssignmentsNonVariable caller)
    (member : out ∈ mergeBindings matched caller fuel) : PrincipalBindingFrame out := by
  obtain ⟨valuation,satisfied⟩ := model
  obtain ⟨extended,matchedModel,callerModel⟩ := closed_private_common_model frame fresh satisfied
  have matchedShape : AssignmentsNonVariable matched := by
    intro key value stored
    have closed := frame.closed key value stored
    cases value <;> simp_all [TypeSubst.typeVars,Spec.Match.Merge.isVariableB]
  have leftModel := Spec.Bindings.ScopeObservation.ModelTransport.heBindingSatisfied_of_specTypeBindingSatisfied matchedModel
  have rightModel := Spec.Bindings.ScopeObservation.ModelTransport.heBindingSatisfied_of_specTypeBindingSatisfied callerModel
  exact ⟨QueryBindingProjection.mergeBindings_semanticLoopFree_of_common_model
      member matchedShape shape leftModel rightModel,
    QueryBindingProjection.mergeBindings_assignmentsNonVariable_model member matchedShape shape,
    QueryBindingProjection.mergeBindings_canonicalClassCoherent_of_common_model
      member frame.keys frame.noEqualities matchedShape shape leftModel rightModel⟩

/-- The actual candidate-first result agrees with the independent caller-first
closed extension as a complete theory and a freshness support, not as lists. -/
theorem closed_private_source_agreement {matched caller independent out : Bindings} {fuel : Nat}
    (frame : ClosedBindingFrame matched) (related : BindingSourceAgreement caller independent)
    (member : out∈mergeBindings matched caller fuel) :
    BindingSourceAgreement out
      ⟨independent.assignments++matched.assignments,independent.equalities⟩ := by
  constructor
  · intro valuation
    rw [runtime_merge_type_solution_iff member,appendPrivatePresentation_solutions,
      ←related.solutions]
    have privateFact : TypeBindingSatisfied valuation matched ↔
        Theory.TypeSubstSatisfied valuation matched.assignments := by
      simp [TypeBindingSatisfied,frame.noEqualities,Theory.TypeSubstSatisfied]
    rw [privateFact]
    exact and_comm
  · intro name
    rw [merge_support_iff member]
    simp only [specBindingVars,List.flatMap_append,List.mem_append] at *
    have privateFact : name∈matched.equalities.flatMap (fun edge=>[edge.1,edge.2]) ↔ False := by
      simp [frame.noEqualities]
    have callerSupport := related.support name
    simp only [specBindingVars,List.mem_append] at callerSupport
    rw [privateFact]
    tauto

/-- Independent source merge, output model and source loop freedom are earned
from the same selected fresh match and caller model. -/
theorem closed_private_source_endpoint {matched caller independent out : Bindings} {fuel : Nat}
    (frame : ClosedBindingFrame matched) (related : BindingSourceAgreement caller independent)
    (fresh : ∀ key∈matched.assignments.map Prod.fst,key∉specBindingVars caller)
    (model : ∃ valuation,TypeBindingSatisfied valuation caller)
    (shape : AssignmentsNonVariable independent)
    (member : out∈mergeBindings matched caller fuel) :
    ∃ source,
    Spec.Match.Merge.MergeRel Spec.Match.Merge.equalityGroundedSemantic matched independent source ∧
      BindingSourceAgreement out source ∧
      AssignmentsNonVariable source ∧ Spec.Match.Merge.SemanticLoopFree source ∧
      ∃ valuation,TypeBindingSatisfied valuation source := by
  have independentFresh : ∀ key∈matched.assignments.map Prod.fst,key∉specBindingVars independent := by
    intro key owned present
    exact fresh key owned ((related.support key).mpr present)
  have sourceMerge := closed_source_merge frame independentFresh
  have sourceShape : AssignmentsNonVariable
      ⟨independent.assignments++matched.assignments,independent.equalities⟩ := by
    intro key value stored
    rcases List.mem_append.mp stored with old | freshRow
    · exact shape key value old
    · have closed := frame.closed key value freshRow
      cases value <;> simp_all [TypeSubst.typeVars,Spec.Match.Merge.isVariableB]
  obtain ⟨valuation,satisfied⟩ := model
  obtain ⟨extended,privateModel,independentModel⟩ :=
    closed_private_common_model frame independentFresh ((related.solutions valuation).mp satisfied)
  have sourceModel : TypeBindingSatisfied extended
      ⟨independent.assignments++matched.assignments,independent.equalities⟩ :=
    (appendPrivatePresentation_solutions _ _ _).mpr ⟨independentModel,privateModel.1⟩
  have independentShape : Spec.Match.SolutionTheory.HEAssignmentsNonVariable independent := by
    intro key target present
    have impossible := shape key (.var target) present
    simp [Spec.Match.Merge.isVariableB] at impossible
  have matchedShape : Spec.Match.SolutionTheory.HEAssignmentsNonVariable matched := by
    intro key target present
    have impossible := frame.closed key (.var target) present
    simp [TypeSubst.typeVars] at impossible
  obtain ⟨source,swapped,swappedShape,_,sameModels⟩ :=
    Spec.Match.Completeness.exists_swapped_specMerge_of_satisfied sourceMerge
      independentShape matchedShape
      ⟨fun name=>Spec.Match.SolutionTheory.encodeModelAtom (extended name),
        Spec.Bindings.ScopeObservation.ModelTransport.heBindingSatisfied_of_specTypeBindingSatisfied sourceModel⟩
  have theory : ∀ observer,
      TypeBindingSatisfied observer
        ⟨independent.assignments++matched.assignments,independent.equalities⟩ ↔
      TypeBindingSatisfied observer source := by
    intro observer
    rw [Spec.Bindings.ScopeObservation.ModelTransport.specTypeBindingSatisfied_iff_heBindingSatisfied_translated,
      Spec.Bindings.ScopeObservation.ModelTransport.specTypeBindingSatisfied_iff_heBindingSatisfied_translated]
    exact sameModels _
  have outputRelated := closed_private_source_agreement frame related member
  have finalRelated : BindingSourceAgreement out source := by
    refine ⟨fun observer=>(outputRelated.solutions observer).trans (theory observer),?_⟩
    intro name
    rw [outputRelated.support name,
      QueryBindingProjection.SourceSupport.merge_support sourceMerge name,
      QueryBindingProjection.SourceSupport.merge_support swapped name]
    exact or_comm
  have finalShape : AssignmentsNonVariable source := by
    intro key value present
    cases value with
    | var name => exact (swappedShape key name present).elim
    | symbol | grounded | expression => rfl
  have finalModel := (theory extended).mp sourceModel
  exact ⟨source,swapped,finalRelated,finalShape,
    Spec.Match.ModelTheory.semanticLoopFree_of_satisfied_nonvariable
      (Spec.Bindings.ScopeObservation.ModelTransport.heBindingSatisfied_of_specTypeBindingSatisfied finalModel) finalShape,
    extended,finalModel⟩

/-- A private RHS supported by the closed match has the same literal
materialization under the actual reconciled frame and independent source
extension. No caller alias layout or canonical resolver is assumed. -/
theorem closed_private_readout_forced {matched caller source out : Bindings}
    {mergeFuel readFuel : Nat} (frame : ClosedBindingFrame matched)
    (related : BindingSourceAgreement out source)
    (fresh : ∀ key∈matched.assignments.map Prod.fst,key∉specBindingVars caller)
    (member : out∈mergeBindings matched caller mergeFuel)
    (atom : Atom)
    (supported : ∀ key∈TypeSubst.typeVars atom,key∈matched.assignments.map Prod.fst)
    (enough : BindingComposition.atomDepth atom+2≤readFuel) :
    ∀ observer, TypeBindingSatisfied observer source →
      applyTypeValuation observer atom = out.applyFull atom readFuel := by
  have readout : out.applyFull atom readFuel =
      applyTypeValuation (presentedValuation matched.assignments) atom := by
    rw [merge_closed_materialization frame atom
      (fun key occurs=>fresh key (supported key occurs)) member]
    have represented : matched=FirstSuccessPreparedArguments.presentedBindings matched.assignments := by
      rcases matched with ⟨assignments,equalities⟩
      exact congrArg (Bindings.mk assignments) frame.noEqualities
    conv_lhs => rw [represented]
    rw [FirstSuccessPreparedArguments.applyFull_presented frame.normal readFuel atom enough,
      applyTypeValuation_presented_eq_apply]
  rw [readout]
  intro observer observerModel
  have selected := (runtime_merge_type_solution member observer
    ((related.solutions observer).mpr observerModel)).1
  apply (applyTypeValuation_eq_iff_on_typeVars observer (presentedValuation matched.assignments) atom).mpr
  intro key occurs
  obtain ⟨⟨stored,value⟩,present,same⟩ := List.mem_map.mp (supported key occurs)
  simp only at same
  subst stored
  have observed := selected.1 key value present
  have canonical := frame.satisfies.1 key value present
  rw [closed_valuation observer (frame.closed key value present)] at observed
  rw [closed_valuation (presentedValuation matched.assignments) (frame.closed key value present)] at canonical
  exact observed.trans canonical.symm

/-- The historical reader is the exact specialization of the same forced
private-body value; no caller representation is discarded. -/
theorem closed_private_source_materialization {matched caller source out : Bindings}
    {mergeFuel readFuel : Nat} (frame : ClosedBindingFrame matched)
    (related : BindingSourceAgreement out source)
    (fresh : ∀ key∈matched.assignments.map Prod.fst,key∉specBindingVars caller)
    (model : ∃ valuation,TypeBindingSatisfied valuation source)
    (member : out∈mergeBindings matched caller mergeFuel)
    (atom : Atom)
    (supported : ∀ key∈TypeSubst.typeVars atom,key∈matched.assignments.map Prod.fst)
    (enough : BindingComposition.atomDepth atom+2≤readFuel) :
    Spec.Type.Presentation.BindingTheory.BindingMaterializationRel source atom
      (out.applyFull atom readFuel) :=
  BindingTheory.BindingMaterializationRel.of_model_constant model
    (closed_private_readout_forced frame related fresh member atom supported enough)

end FreshPrivateMerge
end Mettapedia.Languages.MeTTa.HE


namespace Mettapedia.Languages.MeTTa.HE.FirstSuccessSourceExecution
open Mettapedia.Languages.MeTTa.OSLFCore (Atom GroundedValue)
open Spec.Eval Spec.Type Spec.Type.Presentation
open Spec.Type.RuntimeRefinement Spec.Type.Presentation.Theory Spec.Bindings.ScopeObservation
open RecursiveTasks FirstSuccessRecursiveExecution FirstSuccessRawExecution
open FirstSuccessLeafEvaluation FirstSuccessSourceApplicability FirstSuccessSourceScan
open Mettapedia.GSLT.Distinction.ProductiveBlocks
attribute [local simp] Atom.atomType Atom.undefinedType Atom.symbolType Atom.variableType
  Atom.groundedType Atom.expressionType
section ClosedQueryAdmission

/-- Actual hygienic matching, actual caller merge, and a covered body construct
the independent occurrence and materialization evidence for a recursive rule.
The caller may be nonempty and may retain open values in its normal frame. -/
theorem EquationBodyEvidence.of_closed_match
    {space : Space} {live : List Atom} {query expected : Atom} {incoming : Bindings}
    {candidate request : ResultPair} (position : Nat) (left right : Atom)
    (stored : space.atoms[position]? = some (.expression [.symbol "=", left, right]))
    (rhs : candidate.1 = (freshenEquationAvoiding
      (equationScope live query expected incoming) position left right).2)
    (closed : TypeSubst.typeVars query = [])
    (covered : ∀ key ∈ TypeSubst.typeVars right, key ∈ TypeSubst.typeVars left)
    (noEqualities : incoming.equalities = []) (normal : TypeSubst.Normal incoming.assignments)
    (matchFuel mergeFuel readFuel : Nat)
    (matched : candidate.2 ∈ matchAtoms query
      (freshenEquationAvoiding (equationScope live query expected incoming) position left right).1 matchFuel)
    (merged : request.2 ∈ mergeBindings candidate.2 (aliasConstraints incoming) mergeFuel)
    (readout : request.1 = request.2.applyFull candidate.1 readFuel)
    (enough : BindingComposition.atomDepth candidate.1 + 2 ≤ readFuel) :
    EquationBodyEvidence space live query expected incoming candidate request := by
  let pattern := (freshenEquationAvoiding
    (equationScope live query expected incoming) position left right).1
  have alpha : Spec.Eval.Steps.AlphaVariantRel (expected :: live) query incoming
      left right pattern candidate.1 := by
    rw [rhs]
    exact EquationFreshening.freshenEquationAvoiding_alphaVariant
      (expected :: live) query left right incoming _ position (by
        intro name visible
        have captured := EquationFreshening.equationScope_visible (type_ := expected) visible
        simp only [equationScope, atomListVariables, List.mem_append] at captured ⊢
        tauto)
  obtain ⟨independentMatch, frame⟩ := closed_target_runtime_match_source closed matched
  have supported := closed_target_match_keys (DeclMatchSpec.matchAtoms_sound matched) closed
  have fresh : ∀ key ∈ candidate.2.assignments.map Prod.fst,
      key ∉ specBindingVars (aliasConstraints incoming) := by
    intro key member present
    obtain ⟨entry, entryMember, same⟩ := List.mem_map.mp member
    have patternMember := supported entry.1 entry.2 entryMember
    rw [same] at patternMember
    exact alphaVariant_pattern_fresh alpha key patternMember
      ((Spec.Type.Presentation.BindingTheory.aliasConstraints_support incoming key).mp present)
  have model : ∃ valuation, TypeBindingSatisfied valuation (aliasConstraints incoming) :=
    ⟨_, (Spec.Type.Presentation.BindingTheory.aliasConstraints_models incoming _).mpr
      (normal_record_model noEqualities normal)⟩
  have principal := FreshPrivateMerge.closed_private_principal frame fresh model
    (Spec.Type.Presentation.BindingTheory.aliasConstraints_nonvariable incoming) merged
  have selected : (request.2, QueryBindingProjection.nativeReadoutPresentation request.2) ∈
      QueryBindingProjection.AliasReadout.mergeReadouts candidate.2 incoming mergeFuel :=
    QueryBindingProjection.AliasReadout.mem_mergeReadouts.mpr
      ⟨merged, (Spec.Match.Merge.hasLoop_eq_false_iff_semanticLoopFree _).mpr principal.loopFree, rfl⟩
  obtain ⟨agreement, outputModel, _certificate, _reads⟩ :=
    QueryBindingProjection.AliasReadout.mergeReadouts_sound matched selected
  have bodySupported : ∀ key ∈ TypeSubst.typeVars candidate.1,
      key ∈ candidate.2.assignments.map Prod.fst := by
    intro key occurs
    have member := (FreshPrivateMerge.match_support_iff matched key).mpr
      (Or.inr (alphaVariant_covered alpha covered key occurs))
    simp only [specBindingVars, frame.noEqualities, List.flatMap_nil, List.append_nil,
      List.mem_flatMap] at member
    obtain ⟨⟨storedKey, value⟩, present, member⟩ := member
    rcases List.mem_cons.mp member with same | occursValue
    · exact List.mem_map.mpr ⟨(storedKey, value), present, same.symm⟩
    · simp [frame.closed storedKey value present] at occursValue
  refine EquationBodyEvidence.of_records_transport ?_
  intro independent related
  have logical : LogicalMergeRel candidate.2 independent request.2 :=
    (LogicalMergeRel.congr_inputs (.refl _) (.of_recordPerm related)).mp
      ⟨agreement, outputModel⟩
  have materialized : BindingTheory.BindingMaterializationRel request.2 candidate.1 request.1 := by
    rw [readout]
    exact FreshPrivateMerge.closed_private_source_materialization frame (.refl _) fresh
      outputModel merged candidate.1 bodySupported enough
  refine ⟨request.2, .refl _, ⟨position, left, right, rhs, ?_⟩, materialized⟩
  refine ⟨stored, ⟨(bindingRecordPerm_alphaVariant_iff related _ _ _ _ _ _).mp alpha,
    independentMatch⟩, logical, ?_⟩
  intro valuation satisfied
  rfl

/-- Query and input membership expose the actual declaration occurrence,
match, merge and readout; the portable evidence is then constructed uniformly. -/
theorem EquationBodyEvidence.of_closed_query_hit
    {space : Space} {live : List Atom} {query expected : Atom} {incoming : Bindings}
    {candidate request : ResultPair} {fuel : Nat}
    (closed : TypeSubst.typeVars query = [])
    (covered : ∀ (position : Nat) (left right : Atom),
      space.atoms[position]? = some (.expression [.symbol "=", left, right]) →
      ∀ key ∈ TypeSubst.typeVars right, key ∈ TypeSubst.typeVars left)
    (noEqualities : incoming.equalities = []) (normal : TypeSubst.Normal incoming.assignments)
    (hit : candidate ∈ equationCandidates space live query expected incoming fuel)
    (input : request ∈ equationInputs incoming fuel candidate)
    (enough : BindingComposition.atomDepth candidate.1 + 2 ≤ fuel) :
    EquationBodyEvidence space live query expected incoming candidate request := by
  obtain ⟨left, right, position, stored, rhs, matched, _⟩ :=
    queryEquationsAvoiding_matchAtoms_witness hit
  rw [List.mem_zipIdx_iff_getElem?] at stored
  obtain ⟨merged, mergeMember, selected⟩ := List.mem_filterMap.mp input
  split at selected
  · simp at selected
  · have pair : (merged.applyFull candidate.1 fuel, merged) = request := Option.some.inj selected
    cases pair
    exact EquationBodyEvidence.of_closed_match position left right stored rhs closed
      (covered position left right stored) noEqualities normal fuel fuel fuel matched mergeMember rfl enough

end ClosedQueryAdmission

/-- Chain uses one structural substitution in both presentations. -/
theorem chainSubstitute_eq_substituteName (name : String) (replacement template : Atom) :
    chainSubstitute name replacement template = Minimal.substituteName name replacement template := by
  induction template using Atom.rec with
  | symbol value => simp [chainSubstitute, SubstitutionAlgebra.subst, Minimal.substituteName]
  | var key => simp [chainSubstitute, SubstitutionAlgebra.subst, Minimal.substituteName]; split <;> rfl
  | grounded value => simp [chainSubstitute, SubstitutionAlgebra.subst, Minimal.substituteName]
  | expression values ih =>
      simp only [chainSubstitute, SubstitutionAlgebra.subst, Minimal.substituteName, Atom.expression.injEq]
      exact ih
  | nil => rfl
  | cons head tail ihHead ihTail =>
      simp only [List.map_cons]
      exact congrArg₂ List.cons ihHead ihTail

private theorem queryVisible_cons {live : List Atom} {query atom : Atom} {incoming : Bindings}
    {name : String} (visible : Spec.Eval.Steps.QueryVisibleName live query incoming name) :
    Spec.Eval.Steps.QueryVisibleName (atom :: live) query incoming name := by
  rcases visible with occurs | ⟨value, member, occurs⟩ | assigned | values | equalities
  · exact Or.inl occurs
  · exact Or.inr (Or.inl ⟨value, List.mem_cons_of_mem _ member, occurs⟩)
  · exact Or.inr (Or.inr (Or.inl assigned))
  · exact Or.inr (Or.inr (Or.inr (Or.inl values)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr equalities)))


/-- Tuple branches stop on every Empty/Error head. Other occurrences retain
their own tail reply list and its reached bindings. -/
def tupleOutputs (heads : ResultSet) (tails : ResultPair → ResultSet) : ResultSet :=
  heads.flatMap fun head =>
    if isEmptyOrError head.1 then [head]
    else RecursiveTasks.tupleTail head.1 (tails head)

mutual
/-- Recursive source derivations retain every answer and its reached binding
frame. Equation bodies and arguments are derivations in this same family. -/
inductive AtomDerivation (space : Space) (comparison : SourceBindingComparison := .records) :
    List Atom → Atom → Atom → Bindings → Nat → ResultSet → Prop where
  | leaf (live : List Atom) (value expected : Atom) (incoming : Bindings) (fuel : Nat) :
      LeafRel value expected →
      AtomDerivation (comparison := comparison) space live value expected incoming (fuel + 1) [(value, incoming)]
  | symbolCast (live : List Atom) (name : String) (expected : Atom) (incoming : Bindings)
      (fuel : Nat) (before after : List Atom) (actual : Atom) :
      name ≠ "Empty" → expected ≠ Atom.atomType → expected ≠ Atom.symbolType →
      getAtomTypes space (.symbol name) = before ++ actual :: after →
      TypeSubst.typeVars expected = [] → TypeSubst.typeVars actual = [] →
      (∀ candidate ∈ before, TypeSubst.typeVars candidate = []) →
      (∀ candidate ∈ before, ¬ClosedTypeFits expected candidate) →
      ClosedTypeFits expected actual → sizeOf expected + sizeOf actual + 2 ≤ fuel →
      AtomDerivation (comparison := comparison) space live (.symbol name) expected incoming (fuel + 1)
        [(.symbol name, incoming)]
  | symbolRejected (live : List Atom) (name : String) (expected : Atom)
      (incoming : Bindings) (fuel : Nat) :
      name ≠ "Empty" → expected ≠ Atom.atomType → expected ≠ Atom.symbolType →
      TypeSubst.typeVars expected = [] →
      (∀ actual ∈ getAtomTypes space (.symbol name), TypeSubst.typeVars actual = []) →
      (∀ actual ∈ getAtomTypes space (.symbol name), ¬ClosedTypeFits expected actual) →
      AtomDerivation (comparison := comparison) space live (.symbol name) expected incoming (fuel + 1)
        ((getAtomTypes space (.symbol name)).map fun actual =>
          (mkError (.symbol name) (.badType expected actual), incoming))
  | application (live : List Atom) (name : String) (arguments : List Atom) (expected : Atom)
      (incoming : Bindings) (fuel : Nat)
      (typing : ApplicationTyping space name arguments expected fuel)
      (rows : ArgumentResults) (outputs : ResultPair → ResultSet) :
      ArgsDerivation (comparison := comparison) space
        (.symbol name ::
          (if typing.returned = Atom.expressionType then Atom.undefinedType else typing.returned) :: live)
        arguments typing.domains incoming fuel rows →
      (∀ request ∈ applications name rows,
        CallDerivation (comparison := comparison) space live request.1
          (if typing.returned = Atom.expressionType then Atom.undefinedType else typing.returned)
          request.2 (fuel + 1) (outputs request)) →
      AtomDerivation (comparison := comparison) space live (.expression (.symbol name :: arguments)) expected incoming
        (fuel + 3) (successPriority (((applications name rows).flatMap outputs)))
  | untypedTuple (live : List Atom) (operator : Atom) (arguments : List Atom)
      (expected : Atom) (incoming : Bindings) (fuel : Nat)
      (rows : ResultSet) (outputs : ResultPair → ResultSet) :
      isEmptyOrError (.expression (operator :: arguments)) = false →
      expected ≠ Atom.atomType → expected ≠ Atom.expressionType →
      getAtomTypes space operator = [Atom.undefinedType] →
      TupleDerivation space comparison (expected :: live) (.expression (operator :: arguments))
        incoming (fuel + 1) rows →
      (∀ request ∈ rows, CallDerivation space comparison live request.1 expected request.2
        (fuel + 1) (outputs request)) →
      AtomDerivation space comparison live (.expression (operator :: arguments)) expected incoming
        (fuel + 3) (successPriority (rows.flatMap outputs))

/-- Tuple interpretation uses its own pending-tail scope and stopping rule.
Its child derivations are the same recursive atom family as ordinary calls. -/
inductive TupleDerivation (space : Space) (comparison : SourceBindingComparison := .records) :
    List Atom → Atom → Bindings → Nat → ResultSet → Prop where
  | nil (live : List Atom) (incoming : Bindings) (fuel : Nat) :
      TupleDerivation space comparison live Atom.unit incoming (fuel + 1) [(Atom.unit, incoming)]
  | singleton (live : List Atom) (value : Atom) (incoming : Bindings) (fuel : Nat)
      (heads : ResultSet) :
      AtomDerivation space comparison live value Atom.undefinedType incoming fuel heads →
      TupleDerivation space comparison live (.expression [value]) incoming (fuel + 1)
        (heads.map HE.tupleSingleton)
  | cons (live : List Atom) (head second : Atom) (remaining : List Atom)
      (incoming : Bindings) (fuel : Nat) (heads : ResultSet) (tails : ResultPair → ResultSet) :
      AtomDerivation space comparison (.expression (second :: remaining) :: live)
        head Atom.undefinedType incoming fuel heads →
      (∀ selected ∈ heads, isEmptyOrError selected.1 = false →
        TupleDerivation space comparison (selected.1 :: live) (.expression (second :: remaining))
          selected.2 fuel (tails selected)) →
      TupleDerivation space comparison live (.expression (head :: second :: remaining))
        incoming (fuel + 1) (tupleOutputs heads tails)

inductive ArgsDerivation (space : Space) (comparison : SourceBindingComparison := .records) :
    List Atom → List Atom → List Atom → Bindings → Nat → ArgumentResults → Prop where
  | nil (live : List Atom) (incoming : Bindings) (fuel : Nat) :
      ArgsDerivation (comparison := comparison) space live [] [] incoming (fuel + 1) [([], incoming)]
  | cons (live : List Atom) (value expected : Atom) (values types : List Atom)
      (incoming : Bindings) (fuel : Nat) (heads : ResultSet)
      (tails : ResultPair → ArgumentResults) :
      AtomDerivation (comparison := comparison) space (values ++ types ++ live) value expected incoming fuel heads →
      (∀ head ∈ heads, head.1 = value ∨ isEmptyOrError head.1 = false) →
      (∀ head ∈ heads, ArgsDerivation (comparison := comparison) space (head.1 :: live)
        values types head.2 fuel (tails head)) →
      ArgsDerivation (comparison := comparison) space live (value :: values) (expected :: types) incoming (fuel + 1)
        (heads.flatMap fun head => (tails head).map fun tail => (head.1 :: tail.1, tail.2))

inductive CallDerivation (space : Space) (comparison : SourceBindingComparison := .records) :
    List Atom → Atom → Atom → Bindings → Nat → ResultSet → Prop where
  | errorPassthrough (live : List Atom) (value expected : Atom)
      (incoming : Bindings) (fuel : Nat) :
      IsErrorRel value →
      CallDerivation space comparison live value expected incoming (fuel + 1) [(value, incoming)]
  | embedded (live : List Atom) (name : String) (arguments : List Atom) (expected : Atom)
      (incoming : Bindings) (fuel : Nat) (raw : ResultSet) (outputs : ResultPair → ResultSet) :
      comparison = .semantic → name ≠ "Error" →
      minimalInstruction (.expression (.symbol name :: arguments)) = true →
      MinimalDerivation (comparison := comparison) space (expected :: live) none
        (.expression (.symbol name :: arguments)) incoming fuel raw →
      (∀ result ∈ raw, ReturnDerivation (comparison := comparison) space live
        (.expression (.symbol name :: arguments)) expected result.1 result.2 fuel (outputs result)) →
      CallDerivation (comparison := comparison) space live (.expression (.symbol name :: arguments)) expected
        incoming (fuel + 1) (raw.flatMap outputs)
  | unreduced (live : List Atom) (name : String) (arguments : List Atom) (expected : Atom)
      (incoming : Bindings) (fuel : Nat) :
      name ≠ "unify" ∧ name ≠ "switch-minimal" →
      Spec.Eval.Minimal.embeddedInstruction (.expression [.symbol name]) = false →
      name ≠ "Error" →
      equationCandidates space live (.expression (.symbol name :: arguments)) expected incoming fuel = [] →
      Spec.Eval.Steps.EquationQueryNoMatchRel space (expected :: live)
        (.expression (.symbol name :: arguments)) incoming →
      CallDerivation (comparison := comparison) space live (.expression (.symbol name :: arguments)) expected incoming
        (fuel + 1) [(.expression (.symbol name :: arguments), incoming)]
  | equations (live : List Atom) (name : String) (arguments : List Atom) (expected : Atom)
      (incoming : Bindings) (fuel : Nat)
      (productions : ResultPair → ResultPair → ResultSet)
      (outputs : ResultPair → ResultPair → ResultPair → ResultSet) :
      name ≠ "unify" ∧ name ≠ "switch-minimal" →
      Spec.Eval.Minimal.embeddedInstruction (.expression [.symbol name]) = false →
      name ≠ "Error" →
      rawQueryResults space (.expression (.symbol name :: arguments)) expected incoming fuel live ≠ [] →
      (∀ candidate ∈ equationCandidates space live (.expression (.symbol name :: arguments))
          expected incoming fuel, ∀ request ∈ equationInputs incoming fuel candidate,
        EquationBodyEvidence (comparison := comparison) space live (.expression (.symbol name :: arguments))
          expected incoming candidate request) →
      (∀ candidate ∈ equationCandidates space live (.expression (.symbol name :: arguments))
          expected incoming fuel, ∀ request ∈ equationInputs incoming fuel candidate,
        ProducedDerivation space comparison (expected :: live)
          (some (.expression (.symbol name :: arguments))) request.1 request.2 fuel
          (productions candidate request)) →
      (∀ candidate ∈ equationCandidates space live (.expression (.symbol name :: arguments))
          expected incoming fuel, ∀ request ∈ equationInputs incoming fuel candidate,
        ∀ produced ∈ productions candidate request,
        ReturnDerivation (comparison := comparison) space live (.expression (.symbol name :: arguments))
          expected produced.1 produced.2 fuel (outputs candidate request produced)) →
      CallDerivation (comparison := comparison) space live (.expression (.symbol name :: arguments))
        expected incoming (fuel + 1)
        ((equationCandidates space live (.expression (.symbol name :: arguments))
          expected incoming fuel).flatMap fun candidate =>
            (equationInputs incoming fuel candidate).flatMap fun request =>
              (productions candidate request).flatMap (outputs candidate request))

/-- The ordinary call boundary distinguishes a raw refusal or stopped reply
from a body that still needs evaluation. Its caller frame and depth are exact. -/
inductive ReturnDerivation (space : Space) (comparison : SourceBindingComparison := .records) :
    List Atom → Atom → Atom → Atom → Bindings → Nat → ResultSet → Prop where
  | notReducible (live : List Atom) (original expected : Atom) (bindings : Bindings) (fuel : Nat) :
      ReturnDerivation (comparison := comparison) space live original expected Atom.notReducible bindings fuel [(original, bindings)]
  | stopped (live : List Atom) (original expected value : Atom) (bindings : Bindings) (fuel : Nat) :
      IsEmptyOrErrorRel value →
      ReturnDerivation (comparison := comparison) space live original expected value bindings fuel [(value, bindings)]
  | evaluate (live : List Atom) (original expected value : Atom) (bindings : Bindings)
      (fuel : Nat) (results : ResultSet) :
      value ≠ Atom.notReducible → ¬IsEmptyOrErrorRel value →
      AtomDerivation (comparison := comparison) space live value expected bindings fuel results →
      ReturnDerivation (comparison := comparison) space live original expected value bindings fuel results

/-- Emitted producer admission uses the existing function primitive. A
completed-native producer belongs to its separately tagged service boundary. -/
inductive ProducedDerivation (space : Space) (comparison : SourceBindingComparison := .records) :
    List Atom → Option Atom → Atom → Bindings → Nat → ResultSet → Prop where
  | raw (live : List Atom) (caller : Option Atom) (value : Atom) (incoming : Bindings) (fuel : Nat) :
      ¬Minimal.IsFunction value →
      ProducedDerivation space comparison live caller value incoming (fuel + 1) [(value, incoming)]
  | function (live : List Atom) (caller : Option Atom) (body : Atom) (incoming : Bindings)
      (fuel : Nat) (results : ResultSet) :
      comparison = .semantic →
      PrimitiveDerivation (comparison := comparison) space live caller
        (.expression [.symbol "function", body]) incoming fuel results →
      ProducedDerivation space comparison live caller
        (.expression [.symbol "function", body]) incoming (fuel + 1) results


/-- Raw invocation has its own receiver but reuses the same query and
emitted-producer admissions. Local coverage concerns only actual operations. -/
inductive RawInvocationDerivation (space : Space) (comparison : SourceBindingComparison := .records) :
    List Atom → Option Atom → Atom → Bindings → Nat → ResultSet → Prop where
  | embedded (live : List Atom) (caller : Option Atom) (name : String) (arguments : List Atom)
      (incoming : Bindings) (fuel : Nat) (results : ResultSet) :
      minimalInstruction (.expression (.symbol name :: arguments)) = true →
      MinimalDerivation space comparison live caller (.expression (.symbol name :: arguments))
        incoming fuel results →
      RawInvocationDerivation space comparison live caller (.expression (.symbol name :: arguments))
        incoming (fuel + 1) results
  | unreduced (live : List Atom) (caller : Option Atom) (name : String) (arguments : List Atom)
      (incoming : Bindings) (fuel : Nat) :
      minimalInstruction (.expression (.symbol name :: arguments)) = false →
      queryEquationsCovered (equationScope live (.expression (.symbol name :: arguments))
        Atom.undefinedType incoming) space (.expression (.symbol name :: arguments)) fuel = true →
      equationCandidates space live (.expression (.symbol name :: arguments)) Atom.undefinedType incoming fuel = [] →
      Spec.Eval.Steps.EquationQueryNoMatchRel space live (.expression (.symbol name :: arguments)) incoming →
      RawInvocationDerivation space comparison live caller (.expression (.symbol name :: arguments))
        incoming (fuel + 1) [(Atom.notReducible, incoming)]
  | equations (live : List Atom) (caller : Option Atom) (name : String) (arguments : List Atom)
      (incoming : Bindings) (fuel : Nat) (outputs : ResultPair → ResultPair → ResultSet) :
      minimalInstruction (.expression (.symbol name :: arguments)) = false →
      queryEquationsCovered (equationScope live (.expression (.symbol name :: arguments))
        Atom.undefinedType incoming) space (.expression (.symbol name :: arguments)) fuel = true →
      (∀ candidate ∈ equationCandidates space live (.expression (.symbol name :: arguments))
          Atom.undefinedType incoming fuel,
        matchCovered fuel (.merge candidate.2 (aliasConstraints incoming)) = true ∧
        ∀ merged ∈ mergeBindings candidate.2 (aliasConstraints incoming) fuel, merged.hasLoop = false →
          merged.applyFullCovered candidate.1 fuel = true) →
      rawQueryResults space (.expression (.symbol name :: arguments)) Atom.undefinedType incoming fuel live ≠ [] →
      (∀ candidate ∈ equationCandidates space live (.expression (.symbol name :: arguments))
          Atom.undefinedType incoming fuel, ∀ request ∈ equationInputs incoming fuel candidate,
        EquationBodyEvidence space live (.expression (.symbol name :: arguments))
          Atom.undefinedType incoming candidate request comparison) →
      (∀ candidate ∈ equationCandidates space live (.expression (.symbol name :: arguments))
          Atom.undefinedType incoming fuel, ∀ request ∈ equationInputs incoming fuel candidate,
        ProducedDerivation space comparison live (some (.expression (.symbol name :: arguments)))
          request.1 request.2 fuel (outputs candidate request)) →
      RawInvocationDerivation space comparison live caller (.expression (.symbol name :: arguments))
        incoming (fuel + 1)
        ((equationCandidates space live (.expression (.symbol name :: arguments))
          Atom.undefinedType incoming fuel).flatMap fun candidate =>
            (equationInputs incoming fuel candidate).flatMap (outputs candidate))

/-- Covered minimal instruction paths extend the same source admission family.
They retain physical result lists and caller data; no whole-run execution or
source-correspondence statement is an admission premise. -/
inductive MinimalDerivation (space : Space) (comparison : SourceBindingComparison := .records) :
    List Atom → Option Atom → Atom → Bindings → Nat → ResultSet → Prop where
  | data (live : List Atom) (caller : Option Atom) (value : Atom)
      (incoming : Bindings) (fuel : Nat) :
      minimalInstruction value = false →
      MinimalDerivation (comparison := comparison) space live caller value incoming (fuel + 1) [(value, incoming)]
  | instruction (live : List Atom) (caller : Option Atom) (value : Atom)
      (incoming : Bindings) (fuel : Nat) (results : ResultSet) :
      minimalInstruction value = true → ¬Spec.Eval.Minimal.IsChain value →
      PrimitiveDerivation (comparison := comparison) space live caller value incoming fuel results →
      MinimalDerivation (comparison := comparison) space live caller value incoming (fuel + 1) results

  | chain (live : List Atom) (caller : Option Atom) (atom : Atom) (name : String)
      (template : Atom) (incoming : Bindings) (fuel : Nat) (raw : ResultSet)
      (outputs : ResultPair → ResultSet) :
      PrimitiveDerivation space comparison live caller
        (.expression [.symbol "chain", atom, .var name, template]) incoming fuel raw →
      (∀ result ∈ raw, MinimalDerivation space comparison live caller result.1 result.2 fuel (outputs result)) →
      MinimalDerivation space comparison live caller
        (.expression [.symbol "chain", atom, .var name, template]) incoming (fuel + 1) (raw.flatMap outputs)

inductive PrimitiveDerivation (space : Space) (comparison : SourceBindingComparison := .records) :
    List Atom → Option Atom → Atom → Bindings → Nat → ResultSet → Prop where
  | eval (live : List Atom) (caller : Option Atom) (atom : Atom)
      (incoming : Bindings) (fuel : Nat) (results : ResultSet) :
      incoming.applyFullCovered atom fuel = true →
      RawInvocationDerivation space comparison live caller (incoming.applyFull atom fuel)
        incoming fuel results →
      PrimitiveDerivation space comparison live caller
        (.expression [.symbol "eval", atom]) incoming (fuel + 1) results
  | chain (live : List Atom) (caller : Option Atom) (atom : Atom) (name : String)
      (template : Atom) (incoming : Bindings) (fuel : Nat) (raw : ResultSet) :
      MinimalDerivation space comparison
        (.expression [.symbol "chain", atom, .var name, template] :: live)
        (some (.expression [.symbol "chain", atom, .var name, template])) atom incoming fuel raw →
      (∀ result ∈ raw, result.2.applyFullCovered result.1 fuel = true) →
      PrimitiveDerivation space comparison live caller
        (.expression [.symbol "chain", atom, .var name, template]) incoming (fuel + 1)
        (raw.map fun result => (chainSubstitute name (result.2.applyFull result.1 fuel) template, result.2))
  | unifySuccess (live : List Atom) (caller : Option Atom)
      (target pattern yes no : Atom) (incoming : Bindings) (fuel : Nat) :
      unifyMatchesCovered target pattern incoming fuel = true →
      unifySuccessResults target pattern yes incoming fuel ≠ [] →
      PrimitiveDerivation (comparison := comparison) space live caller
        (.expression [.symbol "unify", target, pattern, yes, no]) incoming (fuel + 1)
        (unifySuccessResults target pattern yes incoming fuel)
  | unifyNoMatch (live : List Atom) (caller : Option Atom)
      (target pattern yes no : Atom) (incoming : Bindings) (fuel : Nat) :
      unifyMatchesCovered target pattern incoming fuel = true →
      unifySuccessResults target pattern yes incoming fuel = [] →
      PrimitiveDerivation (comparison := comparison) space live caller
        (.expression [.symbol "unify", target, pattern, yes, no]) incoming (fuel + 1) [(no, incoming)]
  | consAtom (live : List Atom) (caller : Option Atom) (head : Atom) (tail : List Atom)
      (incoming : Bindings) (fuel : Nat) :
      PrimitiveDerivation (comparison := comparison) space live caller
        (.expression [.symbol "cons-atom", head, .expression tail]) incoming (fuel + 1)
        [(.expression (head :: tail), incoming)]
  | deconsAtom (live : List Atom) (caller : Option Atom) (head : Atom) (tail : List Atom)
      (incoming : Bindings) (fuel : Nat) :
      PrimitiveDerivation (comparison := comparison) space live caller
        (.expression [.symbol "decons-atom", .expression (head :: tail)]) incoming (fuel + 1)
        [(.expression [head, .expression tail], incoming)]
  | function (live : List Atom) (caller : Option Atom) (parts : List Atom)
      (incoming : Bindings) (fuel : Nat) (terminals : ResultSet) :
      FunctionBodyDerivation (comparison := comparison) space
        (.expression [.symbol "function", .expression parts] :: live)
        (some (.expression [.symbol "function", .expression parts]))
        (.expression parts) incoming fuel terminals →
      PrimitiveDerivation (comparison := comparison) space live caller
        (.expression [.symbol "function", .expression parts]) incoming (fuel + 1)
        (terminals.map fun result => (functionTerminal caller result.1, result.2))

inductive FunctionBodyDerivation (space : Space) (comparison : SourceBindingComparison := .records) :
    List Atom → Option Atom → Atom → Bindings → Nat → ResultSet → Prop where
  | run (live : List Atom) (caller : Option Atom) (value : Atom) (incoming : Bindings)
      (fuel : Nat) (raw : ResultSet) (outputs : ResultPair → ResultSet) :
      MinimalDerivation (comparison := comparison) space live caller value incoming fuel raw →
      (∀ result ∈ raw, result.2.applyFullCovered result.1 fuel = true) →
      (∀ result ∈ raw, minimalInstruction (result.2.applyFull result.1 fuel) = false →
        outputs result = [(result.2.applyFull result.1 fuel, result.2)]) →
      (∀ result ∈ raw, minimalInstruction (result.2.applyFull result.1 fuel) = true →
        FunctionBodyDerivation (comparison := comparison) space live caller (result.2.applyFull result.1 fuel)
          result.2 fuel (outputs result)) →
      FunctionBodyDerivation (comparison := comparison) space live caller value incoming (fuel + 1) (raw.flatMap outputs)

end

/-- The ordinary equation case is the singleton-producer specialization of
actual emitted-result completion, retaining all query/input occurrences. -/
theorem CallDerivation.ordinaryEquations {space : Space} {comparison : SourceBindingComparison}
    (live : List Atom) (name : String) (arguments : List Atom) (expected : Atom)
    (incoming : Bindings) (fuel : Nat) (outputs : ResultPair → ResultPair → ResultSet)
    (ordinary : name ≠ "unify" ∧ name ≠ "switch-minimal")
    (nonembedded : Minimal.embeddedInstruction (.expression [.symbol name]) = false)
    (clean : name ≠ "Error")
    (selected : rawQueryResults space (.expression (.symbol name :: arguments)) expected incoming fuel live ≠ [])
    (evidence : ∀ candidate ∈ equationCandidates space live (.expression (.symbol name :: arguments))
        expected incoming fuel, ∀ request ∈ equationInputs incoming fuel candidate,
      EquationBodyEvidence (comparison := comparison) space live (.expression (.symbol name :: arguments))
        expected incoming candidate request)
    (ordinaryBodies : ∀ candidate ∈ equationCandidates space live (.expression (.symbol name :: arguments))
        expected incoming fuel, ∀ request ∈ equationInputs incoming fuel candidate,
      ¬Spec.Eval.Minimal.IsFunction request.1)
    (bodies : ∀ candidate ∈ equationCandidates space live (.expression (.symbol name :: arguments))
        expected incoming fuel, ∀ request ∈ equationInputs incoming fuel candidate,
      ReturnDerivation (comparison := comparison) space live (.expression (.symbol name :: arguments))
        expected request.1 request.2 fuel (outputs candidate request)) :
    CallDerivation (comparison := comparison) space live (.expression (.symbol name :: arguments))
      expected incoming (fuel + 1)
      ((equationCandidates space live (.expression (.symbol name :: arguments)) expected incoming fuel).flatMap
        fun candidate => (equationInputs incoming fuel candidate).flatMap (outputs candidate)) := by
  cases fuel with
  | zero => simp [rawQueryResults, queryEquationsAvoiding] at selected
  | succ fuel =>
      simpa only [List.flatMap_cons, List.flatMap_nil, List.append_nil] using
        (CallDerivation.equations (space := space) (comparison := comparison)
        live name arguments expected incoming (fuel + 1)
        (fun _ request => [request]) (fun candidate request _ => outputs candidate request)
        ordinary nonembedded clean selected evidence
        (fun candidate member request present => .raw _ _ _ _ fuel
          (ordinaryBodies candidate member request present))
        (by
          intro candidate member request present produced appeared
          have same := List.mem_singleton.mp appeared
          subst produced
          exact bodies candidate member request present))

namespace Covered
abbrev SilentPath := Relation.ReflTransGen
  (Checked.machine HE.GroundedDispatch.none).reading.silent
abbrev Realizes (space : Space) (task : Task) (results : ResultSet) : Prop :=
  ∀ stack emitted, SilentPath ⟨space, .work task, stack, emitted⟩
    ⟨space, .returning results, stack, emitted⟩

theorem enter_request (space : Space) (task : Task)
    (stack : List Frame) (emitted : ResultSet)
    (ready : FirstSuccessRecursiveStrategy.taskReady space HE.GroundedDispatch.none task = true := by
      first | rfl | assumption | simp_all [FirstSuccessRecursiveStrategy.taskReady, RecursiveMachine.Checked.taskReady, getMetaType, Atom.unit]) :
    SilentPath ⟨space, .work task, stack, emitted⟩
      ⟨space, (FirstSuccessRecursiveStrategy.enter space HE.GroundedDispatch.none task).1,
        (FirstSuccessRecursiveStrategy.enter space HE.GroundedDispatch.none task).2 ++ stack, emitted⟩ := by
  apply Relation.ReflTransGen.single
  simp [Machine.reading, Checked.machine, RecursiveMachine.Checked.guardMachine,
    Checked.blocked, ready, FirstSuccessRecursiveExecution.machine, next, Transition.relabel]

theorem consume_continuation (space : Space) (frame : Frame) (results : ResultSet)
    (stack : List Frame) (emitted : ResultSet)
    (ready : RecursiveMachine.Checked.frameReady space results frame = true := by rfl) :
    SilentPath ⟨space, .returning results, frame :: stack, emitted⟩
      ⟨space, (RecursiveMachine.resume space frame results).1,
        (RecursiveMachine.resume space frame results).2 ++ stack, emitted⟩ := by
  apply Relation.ReflTransGen.single
  simp [Machine.reading, Checked.machine, RecursiveMachine.Checked.guardMachine,
    Checked.blocked, ready, FirstSuccessRecursiveExecution.machine, next, Transition.relabel]



private theorem appendFrames (space : Space) :
    AppendFrames (Checked.machine HE.GroundedDispatch.none).reading.silent space where
  resumeTail rest head := by
    intro stack emitted
    simpa only [RecursiveMachine.resume, List.cons_append, List.nil_append] using
      consume_continuation space (.append rest) head stack emitted
  restoreHead head tail := by
    intro stack emitted
    simpa only [RecursiveMachine.resume, List.cons_append, List.nil_append] using
      consume_continuation space (.prepend head) tail stack emitted

theorem append_results (space : Space) (remaining : Task) (first second : ResultSet)
    (tail : Realizes space remaining second) (stack : List Frame) (emitted : ResultSet) :
    SilentPath
      ⟨space, .returning first, .append remaining :: stack, emitted⟩
      ⟨space, .returning (first ++ second), stack, emitted⟩ := by
  exact (appendFrames space).collect remaining first second tail stack emitted


theorem atoms_realizes (space : Space) (expected : Atom) (fuel : Nat) (live : List Atom)
    {requests : ResultSet} {outputs : List ResultSet}
    (children : List.Forall₂ (fun request output =>
      Realizes space (.atom request.1 expected request.2 fuel live) output) requests outputs) :
    Realizes space (.atoms expected fuel requests live) outputs.flatten := by
  refine (appendFrames space).traverseTasks
    (fun requests => Task.atoms expected fuel requests live)
    (fun request => Task.atom request.1 expected request.2 fuel live) ?_ ?_ children
  · intro stack emitted
    exact enter_request space (Task.atoms expected fuel [] live) stack emitted
  · rintro ⟨value, bindings⟩ rest stack emitted
    exact enter_request space (Task.atoms expected fuel (⟨value, bindings⟩ :: rest) live)
      stack emitted


theorem returned_notReducible_realizes (space : Space) (original expected : Atom)
    (bindings : Bindings) (fuel : Nat) (live : List Atom) :
    Realizes space (.returned original Atom.notReducible expected bindings fuel live)
      [(original, bindings)] := by
  intro stack emitted
  simpa [FirstSuccessRecursiveStrategy.enter, RecursiveMachine.enter] using
    enter_request space
      (.returned original Atom.notReducible expected bindings fuel live) stack emitted

theorem returned_stopped_realizes (space : Space) (original value expected : Atom)
    (bindings : Bindings) (fuel : Nat) (live : List Atom)
    (stopped : isEmptyOrError value = true) :
    Realizes space (.returned original value expected bindings fuel live) [(value, bindings)] := by
  have accepted : value ≠ Atom.notReducible := by
    rintro rfl
    simp [isEmptyOrError, isEmptyAtom, isErrorAtom, Atom.notReducible, Atom.empty] at stopped
  intro stack emitted
  simpa [FirstSuccessRecursiveStrategy.enter, RecursiveMachine.enter, accepted, stopped] using
    enter_request space
      (.returned original value expected bindings fuel live) stack emitted

theorem returned_evaluate_realizes (space : Space) (original value expected : Atom)
    (bindings : Bindings) (fuel : Nat) (live : List Atom) (results : ResultSet)
    (accepted : value ≠ Atom.notReducible) (running : isEmptyOrError value = false)
    (child : Realizes space (.atom value expected bindings fuel live) results) :
    Realizes space (.returned original value expected bindings fuel live) results := by
  intro stack emitted
  have entered := enter_request space
    (.returned original value expected bindings fuel live) stack emitted
  apply entered.trans
  simpa [FirstSuccessRecursiveStrategy.enter, RecursiveMachine.enter, accepted, running] using
    child stack emitted

theorem returns_realizes (space : Space) (original expected : Atom) (fuel : Nat) (live : List Atom)
    {requests : ResultSet} {outputs : List ResultSet}
    (children : List.Forall₂ (fun request output =>
      Realizes space (.returned original request.1 expected request.2 fuel live) output) requests outputs) :
    Realizes space (.returns original expected fuel requests live) outputs.flatten := by
  refine (appendFrames space).traverseTasks
    (fun requests => Task.returns original expected fuel requests live)
    (fun request => Task.returned original request.1 expected request.2 fuel live) ?_ ?_ children
  · intro stack emitted
    exact enter_request space (Task.returns original expected fuel [] live) stack emitted
  · rintro ⟨value, bindings⟩ rest stack emitted
    exact enter_request space (Task.returns original expected fuel (⟨value, bindings⟩ :: rest) live)
      stack emitted

/-- Query preparation retains every surviving merge before any producer or
typed return continuation is entered. -/
theorem equations_read_realizes (space : Space) (original expected : Atom)
    (incoming : Bindings) (fuel : Nat) (live : List Atom) (candidates : ResultSet)
    (covered : ∀ candidate ∈ candidates,
      matchCovered fuel (.merge candidate.2 (aliasConstraints incoming)) = true ∧
      ∀ merged ∈ mergeBindings candidate.2 (aliasConstraints incoming) fuel, merged.hasLoop = false →
        merged.applyFullCovered candidate.1 fuel = true) :
    Realizes space (.equations original expected incoming fuel candidates live)
      (candidates.flatMap (equationInputs incoming fuel)) := by
  refine (appendFrames space).traverseMap
    (fun rows => .equations original expected incoming fuel rows live)
    (equationInputs incoming fuel) ?_ candidates ?_
  · intro stack emitted
    exact enter_request space (.equations original expected incoming fuel [] live) stack emitted
  · rintro ⟨value, bindings⟩ member rest stack emitted
    obtain ⟨mergeReady, readReady⟩ := covered ⟨value, bindings⟩ member
    have ready : FirstSuccessRecursiveStrategy.taskReady space GroundedDispatch.none
        (.equations original expected incoming fuel (⟨value, bindings⟩ :: rest) live) = true := by
      refine Bool.and_eq_true_iff.mpr ⟨mergeReady, List.all_eq_true.mpr ?_⟩
      intro merged present
      by_cases loop : merged.hasLoop = true
      · simp [loop]
      · have clean : merged.hasLoop = false := Bool.eq_false_of_not_eq_true loop
        simp [clean, readReady merged present clean]
    exact enter_request space
      (.equations original expected incoming fuel (⟨value, bindings⟩ :: rest) live) stack emitted ready

theorem produced_ordinary_realizes (space : Space) (value : Atom) (bindings : Bindings)
    (fuel : Nat) (live : List Atom) (caller : Option Atom)
    (ordinary : ¬Spec.Eval.Minimal.IsFunction value) :
    Realizes space (.produced value bindings (fuel + 1) live caller) [(value, bindings)] := by
  intro stack emitted
  have expanded : FirstSuccessRecursiveStrategy.enter space GroundedDispatch.none
      (.produced value bindings (fuel + 1) live caller) =
        (.returning [(value, bindings)], []) := by
    simp only [FirstSuccessRecursiveStrategy.enter, RecursiveMachine.enter,
      show (InvocationProvenance.emitted == InvocationProvenance.completed) = false from rfl,
      Bool.false_eq_true, if_false]
    split
    · exact (ordinary ⟨_, rfl⟩).elim
    · rfl
  simpa only [expanded, List.nil_append] using
    enter_request space
      (.produced value bindings (fuel + 1) live caller) stack emitted

/-- Every physical row passes through its producer gate. This identity law
uses positive depth and independently recognized nonfunction syntax. -/
theorem productions_ordinary_realizes (space : Space) (fuel : Nat)
    (live : List Atom) (caller : Option Atom) (results : ResultSet)
    (ordinary : ∀ result ∈ results, ¬Spec.Eval.Minimal.IsFunction result.1) :
    Realizes space (.productions (fuel + 1) results live caller) results := by
  have children : List.Forall₂
      (fun request output => Realizes space
        (.produced request.1 request.2 (fuel + 1) live caller) output)
      results (results.map fun row => [row]) := by
    apply List.forall₂_map_right_iff.mpr
    apply List.forall₂_same.mpr
    intro row member
    exact produced_ordinary_realizes space row.1 row.2 fuel live caller (ordinary row member)
  have run := (appendFrames space).traverseTasks
      (fun requests => Task.productions (fuel + 1) requests live caller)
      (fun request => Task.produced request.1 request.2 (fuel + 1) live caller)
      (fun stack emitted => enter_request space
        (.productions (fuel + 1) [] live caller) stack emitted)
      (by
        rintro ⟨value, bindings⟩ rest stack emitted
        exact enter_request space
          (.productions (fuel + 1) (⟨value, bindings⟩ :: rest) live caller) stack emitted)
      children
  rw [← List.flatMap_def, List.flatMap_singleton'] at run
  exact run

theorem producer_ordinary_realizes (space : Space) (original expected : Atom)
    (incoming : Bindings) (fuel : Nat) (live : List Atom) (raw results : ResultSet)
    (present : raw ≠ [])
    (ordinary : ∀ result ∈ raw, ¬Spec.Eval.Minimal.IsFunction result.1)
    (body : Realizes space (.returns original expected (fuel + 1) raw live) results) :
    Realizes space (.producerResults (.ordinary expected) original incoming (fuel + 1)
      live Atom.notReducible raw) results := by
  intro stack emitted
  let returned := Frame.invocationReturn (.ordinary expected) original (fuel + 1) live
  have begin := enter_request space
    (.producerResults (.ordinary expected) original incoming (fuel + 1) live Atom.notReducible raw)
    stack emitted
  have production := productions_ordinary_realizes space fuel (expected :: live)
    (some original) raw ordinary (returned :: stack) emitted
  have resumed := consume_continuation space returned raw stack emitted
  have finish := body stack emitted
  apply begin.trans
  have nonempty := List.isEmpty_eq_false_iff.mpr present
  simpa only [FirstSuccessRecursiveStrategy.enter, RecursiveMachine.enter, nonempty,
    Bool.false_eq_true, if_false, InvocationMode.pendingScope, List.cons_append, List.nil_append,
    returned] using production.trans (resumed.trans (by
      simpa only [RecursiveMachine.resume, List.nil_append, returned] using finish))

theorem producer_refused_realizes (space : Space) (original expected : Atom)
    (incoming : Bindings) (fuel : Nat) (live : List Atom) :
    Realizes space (.producerResults (.ordinary expected) original incoming fuel
      live Atom.notReducible []) [(original, incoming)] := by
  intro stack emitted
  let returned := Frame.invocationReturn (.ordinary expected) original fuel live
  have begin := enter_request space
    (.producerResults (.ordinary expected) original incoming fuel live Atom.notReducible []) stack emitted
  have resumed := consume_continuation space returned
    [(Atom.notReducible, incoming)] stack emitted
  have children : List.Forall₂ (fun request output =>
      Realizes space (.returned original request.1 expected request.2 fuel live) output)
      [(Atom.notReducible, incoming)] [[(original, incoming)]] :=
    .cons (returned_notReducible_realizes space original expected incoming fuel live) .nil
  have finish := returns_realizes space original expected fuel live children stack emitted
  exact begin.trans (by
    simpa only [FirstSuccessRecursiveStrategy.enter, RecursiveMachine.enter,
      List.isEmpty_nil, if_true, List.cons_append, List.nil_append, returned] using
      resumed.trans (by simpa only [RecursiveMachine.resume, returned, List.nil_append,
        List.flatten_cons, List.flatten_nil, List.append_nil] using finish))

/-- A complete nonhost equation invocation first prepares all raw rows, then
enters the producer and ordinary-return continuations on that exact list. -/
theorem call_query_realizes (space : Space) (name : String) (arguments : List Atom)
    (expected : Atom) (incoming : Bindings) (fuel : Nat) (live : List Atom)
    (nonembedded : Spec.Eval.Minimal.embeddedInstruction (.expression [.symbol name]) = false)
    (clean : name ≠ "Error") (results : ResultSet)
    (queryCovered : queryEquationsCovered
      (equationScope live (.expression (.symbol name :: arguments)) expected incoming)
      space (.expression (.symbol name :: arguments)) fuel = true)
    (inputsCovered : ∀ candidate ∈ queryEquationsAvoiding
      (equationScope live (.expression (.symbol name :: arguments)) expected incoming)
      space (.expression (.symbol name :: arguments)) fuel,
      matchCovered fuel (.merge candidate.2 (aliasConstraints incoming)) = true ∧
      ∀ merged ∈ mergeBindings candidate.2 (aliasConstraints incoming) fuel, merged.hasLoop = false →
        merged.applyFullCovered candidate.1 fuel = true)
    (body : Realizes space (.producerResults (.ordinary expected)
      (.expression (.symbol name :: arguments)) incoming fuel live Atom.notReducible
      (rawQueryResults space (.expression (.symbol name :: arguments)) expected incoming fuel live)) results) :
    Realizes space (.call (.expression (.symbol name :: arguments)) expected incoming (fuel + 1) live)
      results := by
  intro stack emitted
  let query := Atom.expression (.symbol name :: arguments)
  let after := Frame.producerResults (.ordinary expected) query incoming fuel live Atom.notReducible
  have ordinary : minimalInstruction query = false := by
    rw [classifier_agrees]
    exact nonembedded
  have notError : isErrorAtom query = false := by simp [query, isErrorAtom, clean]
  have begin := enter_request space
    (.call query expected incoming (fuel + 1) live) stack emitted
  have ready : FirstSuccessRecursiveStrategy.taskReady space GroundedDispatch.none
      (.invocation (.ordinary expected) query incoming (fuel + 1) live) = true := by
    simpa [FirstSuccessRecursiveStrategy.taskReady, RecursiveMachine.Checked.taskReady,
      InvocationMode.errorPassthrough, GroundedDispatch.none, notError, ordinary,
      InvocationMode.expected, query] using queryCovered
  have invoked := enter_request space
    (.invocation (.ordinary expected) query incoming (fuel + 1) live) stack emitted ready
  have prepared := equations_read_realizes space query expected incoming fuel live
    (queryEquationsAvoiding (equationScope live query expected incoming) space query fuel)
    inputsCovered (after :: stack) emitted
  have resumed := consume_continuation space after
    (rawQueryResults space query expected incoming fuel live) stack emitted
  have finish := body stack emitted
  apply begin.trans
  apply invoked.trans
  simpa only [FirstSuccessRecursiveStrategy.enter, RecursiveMachine.enter,
    InvocationMode.errorPassthrough, notError, Bool.false_eq_true, if_false,
    GroundedDispatch.none, ordinary, InvocationMode.expected, List.nil_append,
    List.cons_append, query] using prepared.trans (resumed.trans (by
      simpa only [RecursiveMachine.resume, List.nil_append, after,
        rawQueryResults, equationInputs] using finish))


theorem equations_realizes (space : Space) (original expected : Atom) (incoming : Bindings)
    (fuel : Nat) (live : List Atom) {candidates : ResultSet} {outputs : List (List ResultSet)}
    (bodies : List.Forall₂ (fun candidate output =>
      List.Forall₂ (fun request results =>
        Realizes space (.returned original request.1 expected request.2 fuel live) results)
        (equationInputs incoming fuel candidate) output) candidates outputs) :
    Realizes space (.returns original expected fuel
      (candidates.flatMap (equationInputs incoming fuel)) live)
      (outputs.map List.flatten).flatten := by
  have grouped : List.Forall₂ (List.Forall₂ fun request results =>
      Realizes space (.returned original request.1 expected request.2 fuel live) results)
      (candidates.map (equationInputs incoming fuel)) outputs :=
    List.forall₂_map_left_iff.mpr bodies
  have joined := returns_realizes space original expected fuel live (List.rel_flatten grouped)
  simpa only [← List.flatMap_def, List.flatten_flatten] using joined

/-- Nonempty actual survivors license producer work; candidate existence alone
is insufficient because reconciliation can reject every candidate. -/
theorem call_equations_realizes (space : Space) (name : String) (arguments : List Atom)
    (expected : Atom) (incoming : Bindings) (fuel : Nat) (results : ResultSet)
    (nonembedded : Spec.Eval.Minimal.embeddedInstruction (.expression [.symbol name]) = false)
    (clean : name ≠ "Error") (live : List Atom)
    (queryCovered : queryEquationsCovered
      (equationScope live (.expression (.symbol name :: arguments)) expected incoming)
      space (.expression (.symbol name :: arguments)) fuel = true)
    (inputsCovered : ∀ candidate ∈ queryEquationsAvoiding
      (equationScope live (.expression (.symbol name :: arguments)) expected incoming)
      space (.expression (.symbol name :: arguments)) fuel,
      matchCovered fuel (.merge candidate.2 (aliasConstraints incoming)) = true ∧
      ∀ merged ∈ mergeBindings candidate.2 (aliasConstraints incoming) fuel, merged.hasLoop = false →
        merged.applyFullCovered candidate.1 fuel = true)
    (selected : rawQueryResults space (.expression (.symbol name :: arguments)) expected incoming fuel live ≠ [])
    (ordinary : ∀ request ∈ rawQueryResults space (.expression (.symbol name :: arguments))
      expected incoming fuel live, ¬Spec.Eval.Minimal.IsFunction request.1)
    (bodies : Realizes space (.returns (.expression (.symbol name :: arguments)) expected fuel
      (rawQueryResults space (.expression (.symbol name :: arguments)) expected incoming fuel live) live) results) :
    Realizes space (.call (.expression (.symbol name :: arguments)) expected incoming (fuel + 1) live)
      results := by
  cases fuel with
  | zero => simp [rawQueryResults, queryEquationsAvoiding] at selected
  | succ fuel =>
      exact call_query_realizes space name arguments expected incoming (fuel + 1) live nonembedded clean
        results queryCovered inputsCovered (producer_ordinary_realizes space _ _ _ fuel live _ _ selected ordinary bodies)

theorem call_empty_realizes (space : Space) (name : String) (arguments : List Atom)
    (expected : Atom) (incoming : Bindings) (fuel : Nat) (live : List Atom)
    (nonembedded : Spec.Eval.Minimal.embeddedInstruction (.expression [.symbol name]) = false)
    (clean : name ≠ "Error")
    (queryCovered : queryEquationsCovered
      (equationScope live (.expression (.symbol name :: arguments)) expected incoming)
      space (.expression (.symbol name :: arguments)) fuel = true)
    (empty : queryEquationsAvoiding
      (equationScope live (.expression (.symbol name :: arguments)) expected incoming)
      space (.expression (.symbol name :: arguments)) fuel = []) :
    Realizes space (.call (.expression (.symbol name :: arguments)) expected incoming (fuel + 1) live)
      [(.expression (.symbol name :: arguments), incoming)] := by
  apply call_query_realizes space name arguments expected incoming fuel live nonembedded clean _ queryCovered
    (by intro candidate present; rw [empty] at present; exact (List.not_mem_nil present).elim)
  simpa only [rawQueryResults, empty, List.flatMap_nil] using
    producer_refused_realizes space (.expression (.symbol name :: arguments)) expected incoming fuel live



theorem calls_realizes (space : Space) (expected : Atom) (fuel : Nat) (live : List Atom)
    {requests : ResultSet} {outputs : List ResultSet}
    (children : List.Forall₂ (fun request output =>
      Realizes space (.call request.1 expected request.2 fuel live) output) requests outputs) :
    Realizes space (.calls expected fuel requests live) outputs.flatten := by
  refine (appendFrames space).traverseTasks
    (fun requests => Task.calls expected fuel requests live)
    (fun request => Task.call request.1 expected request.2 fuel live) ?_ ?_ children
  · intro stack emitted
    exact enter_request space (Task.calls expected fuel [] live) stack emitted
  · rintro ⟨value, bindings⟩ rest stack emitted
    exact enter_request space (Task.calls expected fuel (⟨value, bindings⟩ :: rest) live)
      stack emitted


theorem argument_heads_branches_realizes (space : Space) (original : Atom)
    (remaining types : List Atom) (fuel : Nat) (live : List Atom)
    {heads : ResultSet} {outputs : List ResultSet}
    (branches : List.Forall₂ (fun head output =>
      if head.1 != original && isEmptyOrError head.1 then output = [head]
      else ∃ tails, Realizes space (.args remaining types head.2 fuel (head.1 :: live)) tails ∧
        output = RecursiveTasks.argumentTail head.1 tails) heads outputs) :
    Realizes space (.argumentHeads original remaining types fuel heads live) outputs.flatten := by
  let plan := argumentBranchPlan original remaining types fuel live
  refine (appendFrames space).traverseBranches plan ?_ ?_ ?_ ?_ branches
  · intro stack emitted
    exact enter_request space (Task.argumentHeads original remaining types fuel [] live) stack emitted
  · rintro ⟨value, bindings⟩ rest stopped stack emitted
    simp only [plan, argumentBranchPlan] at stopped
    simpa only [plan, argumentBranchPlan, FirstSuccessRecursiveStrategy.enter, RecursiveMachine.enter,
      stopped, if_true, List.cons_append, List.nil_append] using
      enter_request space (Task.argumentHeads original remaining types fuel (⟨value, bindings⟩ :: rest) live) stack emitted
  · rintro ⟨value, bindings⟩ rest running stack emitted
    simp only [plan, argumentBranchPlan] at running
    simpa only [plan, argumentBranchPlan, FirstSuccessRecursiveStrategy.enter, RecursiveMachine.enter,
      running, Bool.false_eq_true, if_false, List.cons_append, List.nil_append] using
      enter_request space (Task.argumentHeads original remaining types fuel (⟨value, bindings⟩ :: rest) live) stack emitted
  · intro row replies stack emitted
    simpa only [plan, argumentBranchPlan, RecursiveMachine.resume, List.cons_append, List.nil_append] using
      consume_continuation space (Frame.argumentTail row.1) replies stack emitted


theorem argument_heads_realizes (space : Space) (original : Atom) (remaining types : List Atom)
    (fuel : Nat) (live : List Atom) {heads : ResultSet} {outputs : List ResultSet}
    (safe : ∀ head ∈ heads, head.1 = original ∨ isEmptyOrError head.1 = false)
    (branches : List.Forall₂ (fun head output => ∃ tails,
      Realizes space (.args remaining types head.2 fuel (head.1 :: live)) tails ∧
        output = RecursiveTasks.argumentTail head.1 tails) heads outputs) :
    Realizes space (.argumentHeads original remaining types fuel heads live) outputs.flatten := by
  apply argument_heads_branches_realizes space original remaining types fuel live
  induction branches with
  | nil => exact .nil
  | @cons head output heads outputs branch branches ih =>
      have guard : (head.1 != original && isEmptyOrError head.1) = false := by
        rcases safe head List.mem_cons_self with same | clean
        · simp [same]
        · simp [clean]
      refine .cons ?_ (ih (fun next member => safe next (List.mem_cons_of_mem _ member)))
      simpa only [guard, Bool.false_eq_true, if_false] using branch


theorem arguments_cons_with_branches_realizes (space : Space) (original expected : Atom)
    (remaining types : List Atom) (incoming : Bindings) (fuel : Nat) (live : List Atom)
    {heads : ResultSet} {outputs : List ResultSet}
    (headRun : Realizes space (.atom original expected incoming fuel (remaining ++ types ++ live))
      heads)
    (safe : ∀ head ∈ heads, head.1 = original ∨ isEmptyOrError head.1 = false)
    (branches : List.Forall₂ (fun head output => ∃ tails,
      Realizes space (.args remaining types head.2 fuel (head.1 :: live)) tails ∧
        output = RecursiveTasks.argumentTail head.1 tails) heads outputs) :
    Realizes space (.args (original :: remaining) (expected :: types) incoming (fuel + 1) live)
      outputs.flatten := by
  refine FramedPath.trans (third := []) (FramedPath.receive (first := []) (last := []) (receiver := Frame.argumentHeads original remaining types fuel live) ?_ headRun ?_)
    (argument_heads_realizes space original remaining types fuel live safe branches)
  · intro stack emitted
    exact enter_request space (.args (original :: remaining) (expected :: types) incoming (fuel + 1) live) stack emitted
  · intro stack emitted
    exact consume_continuation space (Frame.argumentHeads original remaining types fuel live) heads stack emitted


theorem function_head_retained (space : Space) (name : String) (domains : List Atom) (returned : Atom)
    (bindings : Bindings) (fuel : Nat) (live : List Atom) (rows : ArgumentResults)
    (arguments : List Atom) (clean : name ≠ "Empty")
    (tail : Realizes space (.args arguments domains bindings fuel (.symbol name :: live))
      (argumentReplies rows)) :
    Realizes space (.heads (arrow domains returned) arguments fuel [(.symbol name, bindings)] live)
      (applications name rows) := by
  intro stack emitted
  let rest := Task.heads (arrow domains returned) arguments fuel [] live
  have begin := enter_request space
    (.heads (arrow domains returned) arguments fuel [(.symbol name, bindings)] live) stack emitted
  have middle := tail (.functionTail (.symbol name) :: .append rest :: stack) emitted
  have collect := consume_continuation space (.functionTail (.symbol name))
    (argumentReplies rows) (.append rest :: stack) emitted
  have mapped : RecursiveTasks.functionTail (.symbol name) (argumentReplies rows) =
      applications name rows := by
    simp [argumentReplies, applications, RecursiveTasks.functionTail, List.map_map, Function.comp_def, argumentValues_packet, argumentsSucceeded_packet]
  have emptyRest : Realizes space rest [] := by
    intro saved prior
    simpa [rest, FirstSuccessRecursiveStrategy.enter, RecursiveMachine.enter] using
      enter_request space rest saved prior
  have finish := append_results space rest
    (applications name rows) []
    emptyRest stack emitted
  have collected : SilentPath
      ⟨space, .returning (argumentReplies rows), .functionTail (.symbol name) :: .append rest :: stack, emitted⟩
      ⟨space, .returning (applications name rows),
        .append rest :: stack, emitted⟩ := by
    simpa only [RecursiveMachine.resume, mapped, List.nil_append] using collect
  exact begin.trans (by
    simpa [FirstSuccessRecursiveStrategy.enter, RecursiveMachine.enter, isEmptyOrError,
      isEmptyAtom, Atom.empty, isErrorAtom, clean, arrow, getFunctionArgTypes, rest] using
        middle.trans (collected.trans finish))


theorem symbol_cast_realizes (space : Space) (name : String) (expected : Atom)
    (bindings : Bindings) (fuel : Nat) (before after : List Atom) (actual : Atom)
    (notEmpty : name ≠ "Empty")
    (types : getAtomTypes space (.symbol name) = before ++ actual :: after)
    (expectedClosed : TypeSubst.typeVars expected = []) (actualClosed : TypeSubst.typeVars actual = [])
    (earlierClosed : ∀ candidate ∈ before, TypeSubst.typeVars candidate = [])
    (earlierRejects : ∀ candidate ∈ before, ¬ClosedTypeFits expected candidate)
    (fits : ClosedTypeFits expected actual) (enough : sizeOf expected + sizeOf actual + 2 ≤ fuel)
    (live : List Atom := []) (covered : typeCastCovered (.symbol name) expected space bindings fuel = true) :
    Realizes space (.atom (.symbol name) expected bindings (fuel + 1) live)
      [(.symbol name, bindings)] := by
  intro stack emitted
  have cast := (closed_cast_reply space (.symbol name) expected bindings fuel before actual after
    types expectedClosed earlierClosed earlierRejects actualClosed fits enough).1
  simpa [FirstSuccessRecursiveStrategy.enter, RecursiveMachine.enter, isEmptyOrError,
    isEmptyAtom, Atom.empty, isErrorAtom, getMetaType, notEmpty, cast] using
      enter_request space
        (.atom (.symbol name) expected bindings (fuel + 1) live) stack emitted


theorem symbol_rejection_realizes (space : Space) (name : String) (expected : Atom)
    (incoming : Bindings) (fuel : Nat) (live : List Atom)
    (notEmpty : name ≠ "Empty") (notRaw : expected ≠ Atom.atomType)
    (notMeta : expected ≠ Atom.symbolType)
    (expectedClosed : TypeSubst.typeVars expected = [])
    (closed : ∀ actual ∈ getAtomTypes space (.symbol name), TypeSubst.typeVars actual = [])
    (rejected : ∀ actual ∈ getAtomTypes space (.symbol name), ¬ClosedTypeFits expected actual) (covered : typeCastCovered (.symbol name) expected space incoming fuel = true) :
    Realizes space (.atom (.symbol name) expected incoming (fuel + 1) live)
      ((getAtomTypes space (.symbol name)).map fun actual =>
        (mkError (.symbol name) (.badType expected actual), incoming)) := by
  intro stack emitted
  change expected ≠ .symbol "Symbol" at notMeta
  change expected ≠ .symbol "Atom" at notRaw
  have cast := (closed_cast_failure_reply space (.symbol name) expected incoming fuel
    expectedClosed closed rejected).1
  simpa [FirstSuccessRecursiveStrategy.enter, RecursiveMachine.enter, isEmptyOrError,
    isEmptyAtom, Atom.empty, isErrorAtom, getMetaType, notEmpty, notRaw, notMeta,
    Atom.variableType, Atom.symbolType, cast] using
      enter_request space
        (.atom (.symbol name) expected incoming (fuel + 1) live) stack emitted


theorem application_function_retained {space : Space} {name : String} {arguments : List Atom}
    {expected : Atom} {fuel : Nat} (typing : ApplicationTyping space name arguments expected fuel)
    (bindings : Bindings) (rows : ArgumentResults) (live : List Atom)
    (headCovered : typeCastCovered (.symbol name) (arrow typing.domains typing.returned)
      space bindings (fuel - 1) = true)
    (argumentsRun : Realizes space
      (.args arguments typing.domains bindings fuel (.symbol name :: live)) (argumentReplies rows)) :
    Realizes space
      (.func (.expression (.symbol name :: arguments)) (arrow typing.domains typing.returned)
        bindings (fuel + 1) live)
      (applications name rows) := by
  cases fuel with
  | zero => have := typing.headBudget; omega
  | succ fuel =>
      intro stack emitted
      have cast := symbol_cast_realizes space name (arrow typing.domains typing.returned)
        bindings fuel typing.before typing.after (arrow typing.domains typing.returned)
        typing.nonemptyOperator typing.sourceTypes
        typing.headClosed typing.headClosed typing.earlierClosed typing.earlierHeadRejects
        (Or.inr (Or.inr (Or.inr (Or.inr rfl)))) (by have := typing.headBudget; omega)
        (arrow typing.domains typing.returned :: arguments ++ live) (by simpa using headCovered)
        (.heads (arrow typing.domains typing.returned) arguments (fuel + 1) live :: stack) emitted
      have resumed := consume_continuation space
        (.heads (arrow typing.domains typing.returned) arguments (fuel + 1) live)
        [(.symbol name, bindings)] stack emitted
      have done := function_head_retained space name typing.domains typing.returned bindings (fuel + 1) live
        rows arguments typing.nonemptyOperator argumentsRun stack emitted
      have continuation := resumed.trans (by
        simpa only [RecursiveMachine.resume, List.nil_append] using done)
      have begin := enter_request space
        (.func (.expression (.symbol name :: arguments)) (arrow typing.domains typing.returned)
          bindings (fuel + 1 + 1) live) stack emitted
      exact begin.trans (by
        simpa only [FirstSuccessRecursiveStrategy.enter, RecursiveMachine.enter,
          List.cons_append, List.nil_append] using cast.trans continuation)


theorem binding_alternatives_retained {space : Space} {name : String} {arguments : List Atom}
    {expected : Atom} {fuel : Nat} (typing : ApplicationTyping space name arguments expected fuel)
    (bindings : Bindings) (rows : ArgumentResults) (count : Nat) (results : ResultSet)
    (live : List Atom)
    (headCovered : typeCastCovered (.symbol name) (arrow typing.domains typing.returned)
      space bindings (fuel - 1) = true)
    (argumentsRun : Realizes space (.args arguments typing.domains bindings fuel
      (.symbol name ::
        (if typing.returned = Atom.expressionType then Atom.undefinedType else typing.returned) ::
          live))
      (argumentReplies rows))
    (callsRun : Realizes space
      (.calls (if typing.returned = Atom.expressionType then Atom.undefinedType else typing.returned)
        (fuel + 1) (applications name rows)
        live)
      results) :
    Realizes space
      (.bindingAlternatives (.expression (.symbol name :: arguments)) (arrow typing.domains typing.returned)
        (if typing.returned = Atom.expressionType then Atom.undefinedType else typing.returned)
        (fuel + 1) (List.replicate count bindings) live)
      (List.replicate count results).flatten := by
  induction count with
  | zero =>
      intro stack emitted
      simpa [replies, FirstSuccessRecursiveStrategy.enter, RecursiveMachine.enter] using
        enter_request space
          (.bindingAlternatives (.expression (.symbol name :: arguments))
            (arrow typing.domains typing.returned)
            (if typing.returned = Atom.expressionType then Atom.undefinedType else typing.returned)
            (fuel + 1) [] live) stack emitted
  | succ count ih =>
      intro stack emitted
      let callType := if typing.returned = Atom.expressionType then Atom.undefinedType else typing.returned
      let one := applications name rows
      let rest := Task.bindingAlternatives (.expression (.symbol name :: arguments))
        (arrow typing.domains typing.returned) callType (fuel + 1) (List.replicate count bindings) live
      have begin := enter_request space
        (.bindingAlternatives (.expression (.symbol name :: arguments))
          (arrow typing.domains typing.returned) callType (fuel + 1)
          (List.replicate (count + 1) bindings) live) stack emitted
      have function := application_function_retained typing bindings rows (callType :: live) headCovered argumentsRun
        (.calls callType (fuel + 1) live :: .append rest :: stack) emitted
      have transfer := consume_continuation space
        (.calls callType (fuel + 1) live) one (.append rest :: stack) emitted
      have calls := callsRun (.append rest :: stack) emitted
      have remainder := append_results space rest results
        (List.replicate count results).flatten ih stack emitted
      have collected := transfer.trans (by
        simpa only [RecursiveMachine.resume, List.nil_append, one] using calls.trans remainder)
      exact begin.trans (by
        simpa [FirstSuccessRecursiveStrategy.enter, RecursiveMachine.enter, List.replicate_succ,
          callType, one, rest, replies, List.map_append] using function.trans collected)


theorem application_retained_realizes {space : Space} {name : String} {arguments : List Atom}
    {expected : Atom} {fuel : Nat} (typing : ApplicationTyping space name arguments expected fuel)
    (bindings : Bindings) (rows : ArgumentResults) (results : ResultSet) (live : List Atom)
    (selectionCovered : FirstSuccessRecursiveStrategy.selectionReady space
      (.expression (.symbol name :: arguments)) expected bindings (fuel + 1)
      (getAtomTypes space (.symbol name)) = true)
    (headCovered : typeCastCovered (.symbol name) (arrow typing.domains typing.returned)
      space bindings (fuel - 1) = true)
    (argumentsRun : Realizes space (.args arguments typing.domains bindings fuel
      (.symbol name ::
        (if typing.returned = Atom.expressionType then Atom.undefinedType else typing.returned) ::
          live))
      (argumentReplies rows))
    (callsRun : Realizes space
      (.calls (if typing.returned = Atom.expressionType then Atom.undefinedType else typing.returned)
        (fuel + 1) (applications name rows)
        live)
      results) :
    Realizes space (.atom (.expression (.symbol name :: arguments)) expected bindings (fuel + 3) live)
      (successPriority results) := by
  intro stack emitted
  let resultValues := results
  have atom := enter_request space
    (.atom (.expression (.symbol name :: arguments)) expected bindings (fuel + 3) live) stack emitted
  have expression := enter_request space
    (.expression (.expression (.symbol name :: arguments)) expected bindings (fuel + 2) live)
    (.filter :: stack) emitted
  have selection := enter_request space
    (.functions (.expression (.symbol name :: arguments)) expected bindings (fuel + 1)
      (getAtomTypes space (.symbol name)) live) (.filter :: stack) emitted
  have alternatives := binding_alternatives_retained typing bindings rows
    1 results live headCovered argumentsRun callsRun
    (.filter :: stack) emitted
  have filtered := consume_continuation space .filter resultValues
    stack emitted
  have selected := (application_selected typing bindings).1
  have done := alternatives.trans (by
    simpa only [RecursiveMachine.resume, List.nil_append, resultValues, List.replicate_one,
      List.flatten_cons, List.flatten_nil, List.append_nil] using filtered)
  have stepSelection := selection.trans (by
    simpa [FirstSuccessRecursiveStrategy.enter, selected, selectedPolicy] using done)
  have stepExpression := expression.trans (by
    simpa only [FirstSuccessRecursiveStrategy.enter, rawTypeLookup, List.nil_append] using
      stepSelection)
  have notRaw : expected ≠ .symbol "Atom" := typing.demandNotRaw
  have notExpression : expected ≠ .symbol "Expression" := typing.demandNotExpression
  exact atom.trans (by
    simpa [FirstSuccessRecursiveStrategy.enter, RecursiveMachine.enter, isEmptyOrError,
      isEmptyAtom, Atom.empty, Atom.unit, isErrorAtom, getMetaType, notRaw,
      notExpression, typing.cleanOperator, Nat.add_assoc] using stepExpression)


theorem calls_realizes_map (space : Space) (expected : Atom) (fuel : Nat) (live : List Atom)
    (requests : ResultSet) (outputs : ResultPair → ResultSet)
    (children : ∀ request ∈ requests,
      Realizes space (.call request.1 expected request.2 fuel live) (outputs request)) :
    Realizes space (.calls expected fuel requests live) (requests.flatMap outputs) := by
  have aligned : List.Forall₂ (fun request output =>
      Realizes space (.call request.1 expected request.2 fuel live) output)
      requests (requests.map outputs) :=
    List.forall₂_map_right_iff.mpr (List.forall₂_same.mpr children)
  simpa only [← List.flatMap_def] using calls_realizes space expected fuel live aligned


theorem equations_realizes_map (space : Space) (original expected : Atom) (incoming : Bindings)
    (fuel : Nat) (live : List Atom) (candidates : ResultSet)
    (outputs : ResultPair → ResultPair → ResultSet)
    (children : ∀ candidate ∈ candidates, ∀ request ∈ equationInputs incoming fuel candidate,
      Realizes space (.returned original request.1 expected request.2 fuel live) (outputs candidate request)) :
    Realizes space (.returns original expected fuel
      (candidates.flatMap (equationInputs incoming fuel)) live)
      (candidates.flatMap fun candidate =>
        (equationInputs incoming fuel candidate).flatMap (outputs candidate)) := by
  have aligned : List.Forall₂ (fun candidate output =>
      List.Forall₂ (fun request results =>
        Realizes space (.returned original request.1 expected request.2 fuel live) results)
        (equationInputs incoming fuel candidate) output)
      candidates (candidates.map fun candidate =>
        (equationInputs incoming fuel candidate).map (outputs candidate)) := by
    apply List.forall₂_map_right_iff.mpr
    apply List.forall₂_same.mpr
    intro candidate member
    exact List.forall₂_map_right_iff.mpr (List.forall₂_same.mpr (children candidate member))
  simpa only [List.map_map, Function.comp_def, ← List.flatMap_def] using
    equations_realizes space original expected incoming fuel live aligned

theorem retained_leaf (space : Space) (value expected : Atom) (incoming : Bindings)
    (fuel : Nat) (live : List Atom) (leaf : LeafRel value expected) :
    Covered.Realizes space (.atom value expected incoming (fuel + 1) live) [(value, incoming)] := by
  intro stack emitted
  have ready : FirstSuccessRecursiveStrategy.taskReady space HE.GroundedDispatch.none
      (.atom value expected incoming (fuel + 1) live) = true := by
    rcases (leaf_gate value expected).mp leaf with failed | passed
    · simp [FirstSuccessRecursiveStrategy.taskReady, RecursiveMachine.Checked.taskReady, failed]
    · simp only [Bool.or_eq_true, beq_iff_eq] at passed
      simp [FirstSuccessRecursiveStrategy.taskReady, RecursiveMachine.Checked.taskReady]
      exact Or.inr (Or.inl passed)
  have expanded : FirstSuccessRecursiveStrategy.enter space HE.GroundedDispatch.none
      (.atom value expected incoming (fuel + 1) live) = (.returning [(value, incoming)], []) := by
    rcases (leaf_gate value expected).mp leaf with failed | passed
    · simp only [FirstSuccessRecursiveStrategy.enter, RecursiveMachine.enter, failed, if_true]
    · simp only [FirstSuccessRecursiveStrategy.enter, RecursiveMachine.enter, passed, if_true, ite_self]
  simpa only [expanded, List.nil_append] using
    enter_request space (.atom value expected incoming (fuel + 1) live) stack emitted ready

end Covered

namespace Covered

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open RecursiveTasks FirstSuccessRecursiveExecution

/-- The retained body traversal reads every reached row with that row's own
binding record before deciding whether to resume an instruction. Child paths
are local premises for composition; this statement does not assume source
meaning or whole-evaluator correspondence. -/
theorem body_results_realizes (space : Space) (fuel : Nat) (live : List Atom)
    (caller : Option Atom) {requests : ResultSet} {outputs : List ResultSet}
    (children : List.Forall₂ (fun request output =>
      request.2.applyFullCovered request.1 fuel = true ∧
      if minimalInstruction (request.2.applyFull request.1 fuel) then
        Realizes space (.functionBody (request.2.applyFull request.1 fuel)
          request.2 fuel live caller) output
      else output = [(request.2.applyFull request.1 fuel, request.2)]) requests outputs) :
    Realizes space (.bodyResults fuel requests live caller) outputs.flatten := by
  refine (appendFrames space).traverse
    (fun requests => .bodyResults fuel requests live caller) ?_ (List.Forall₂.imp ?_ children)
  · intro stack emitted
    exact enter_request space (.bodyResults fuel [] live caller) stack emitted
  · rintro ⟨value, bindings⟩ output ⟨covered, continuation⟩ rest stack emitted
    have begin := enter_request space
      (.bodyResults fuel (⟨value, bindings⟩ :: rest) live caller) stack emitted covered
    cases running : minimalInstruction (bindings.applyFull value fuel) with
    | false =>
        simp only [running, Bool.false_eq_true, if_false] at continuation
        subst output
        simpa only [FirstSuccessRecursiveStrategy.enter, RecursiveMachine.enter, running,
          Bool.false_eq_true, if_false, List.cons_append, List.nil_append] using begin
    | true =>
        simp only [running, if_true] at continuation
        apply begin.trans
        simpa only [FirstSuccessRecursiveStrategy.enter, RecursiveMachine.enter, running,
          if_true, List.cons_append, List.nil_append] using
          continuation (.append (.bodyResults fuel rest live caller) :: stack) emitted

/-- Entering a function body retains its receiver while the actual minimal
run produces rows; the body traversal consumes that exact ordered list. -/
theorem function_body_realizes (space : Space) (value : Atom) (bindings : Bindings)
    (fuel : Nat) (live : List Atom) (caller : Option Atom) (raw results : ResultSet)
    (child : Realizes space (.minimal value bindings fuel live caller) raw)
    (continuation : Realizes space (.bodyResults fuel raw live caller) results) :
    Realizes space (.functionBody value bindings (fuel + 1) live caller) results := by
  refine FramedPath.trans (third := []) (FramedPath.receive (first := []) (last := []) (receiver := Frame.bodyResults fuel live caller) ?_ child ?_)
    (continuation)
  · intro stack emitted
    exact enter_request space (.functionBody value bindings (fuel + 1) live caller) stack emitted
  · intro stack emitted
    exact consume_continuation space (Frame.bodyResults fuel live caller) raw stack emitted

/-- The function return frame preserves every body's binding endpoint and
uses the original saved caller for each non-return terminal. -/
theorem function_primitive_realizes (space : Space) (parts : List Atom)
    (bindings : Bindings) (fuel : Nat) (live : List Atom) (caller : Option Atom)
    (terminals : ResultSet)
    (child : Realizes space (.functionBody (.expression parts) bindings fuel
      (.expression [.symbol "function", .expression parts] :: live)
      (some (.expression [.symbol "function", .expression parts]))) terminals) :
    Realizes space (.primitive (.expression [.symbol "function", .expression parts])
      bindings (fuel + 1) live caller)
      (terminals.map fun result => (functionTerminal caller result.1, result.2)) := by
  refine FramedPath.receive (first := []) (last := []) (receiver := Frame.functionTerminal caller) ?_ child ?_
  · intro stack emitted
    exact enter_request space (.primitive (.expression [.symbol "function", .expression parts]) bindings (fuel + 1) live caller) stack emitted
  · intro stack emitted
    exact consume_continuation space (Frame.functionTerminal caller) terminals stack emitted

/-- Emitted function syntax runs through the saved function receiver. This
rule does not infer completed-producer provenance from the syntax. -/
theorem produced_function_realizes (space : Space) (body : Atom) (bindings : Bindings)
    (fuel : Nat) (live : List Atom) (caller : Option Atom) (results : ResultSet)
    (child : Realizes space
      (.primitive (.expression [.symbol "function", body]) bindings fuel live caller) results) :
    Realizes space (.produced (.expression [.symbol "function", body])
      bindings (fuel + 1) live caller .emitted) results := by
  intro stack emitted
  have begin := enter_request space
    (.produced (.expression [.symbol "function", body]) bindings (fuel + 1) live caller .emitted)
    stack emitted
  apply begin.trans
  simpa only [FirstSuccessRecursiveStrategy.enter, RecursiveMachine.enter,
    show (InvocationProvenance.emitted == InvocationProvenance.completed) = false from rfl,
    Bool.false_eq_true, if_false, List.nil_append] using child stack emitted

/-- The already-completed lane keeps its explicit producer tag and exact
reply, even when the reply happens to have function syntax. -/
theorem produced_completed_realizes (space : Space) (value : Atom) (bindings : Bindings)
    (fuel : Nat) (live : List Atom) (caller : Option Atom) :
    Realizes space (.produced value bindings (fuel + 1) live caller .completed)
      [(value, bindings)] := by
  intro stack emitted
  simpa only [FirstSuccessRecursiveStrategy.enter, RecursiveMachine.enter,
    show (InvocationProvenance.completed == InvocationProvenance.completed) = true from rfl,
    if_true, List.nil_append] using
    enter_request space (.produced value bindings (fuel + 1) live caller .completed) stack emitted

/-- Producers are traversed by physical list occurrence. Equal replies are
not identified, and each child retains the exact reached binding record. -/
theorem productions_realizes (space : Space) (fuel : Nat) (live : List Atom)
    (caller : Option Atom) (provenance : InvocationProvenance)
    {requests : ResultSet} {outputs : List ResultSet}
    (children : List.Forall₂ (fun request output => Realizes space
      (.produced request.1 request.2 fuel live caller provenance) output) requests outputs) :
    Realizes space (.productions fuel requests live caller provenance) outputs.flatten := by
  refine (appendFrames space).traverseTasks
    (fun requests => Task.productions fuel requests live caller provenance)
    (fun request => Task.produced request.1 request.2 fuel live caller provenance) ?_ ?_ children
  · intro stack emitted
    exact enter_request space (Task.productions fuel [] live caller provenance) stack emitted
  · rintro ⟨value, bindings⟩ rest stack emitted
    exact enter_request space (Task.productions fuel (⟨value, bindings⟩ :: rest) live caller provenance)
      stack emitted

end Covered

section

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Spec.Eval Spec.Eval.Steps Spec.Match.Merge Spec.Match.ModelTheory
open Spec.Type.Presentation Spec.Type.RuntimeRefinement Spec.Bindings.ScopeObservation
open Mettapedia.Languages.MeTTa.HE.Spec.Match.SolutionTheory Mettapedia.Languages.MeTTa.HE.Spec.Bindings.ScopeObservation.ModelTransport

open Spec.Type Spec.Type.Presentation.BindingTheory

/-- Actual local reconciliation implements logical constraint conjunction
against an independently chosen, fully equivalent caller record. -/
theorem alias_unify_source_candidate
    {target pattern : Atom} {incoming independent output : Bindings}
    {table : TypeSubst} {depth : Nat}
    (input : BindingSourceAgreement incoming independent)
    (occurred : (output, table) ∈
      QueryBindingProjection.AliasReadout.unifyReadouts target pattern incoming depth) :
    UnifyCandidateRel target pattern independent output := by
  obtain ⟨matched, matching, agreement, model, _certificate, _reads⟩ :=
    QueryBindingProjection.AliasReadout.unifyReadouts_source input occurred
  exact ⟨matched, matching, agreement, model⟩

/-- A discovered operation earns its selected source frame, exact primitive
step and all-operand readout. The arbitrary old source table is absorbed on
the entire pending tuple, so later uses retain their shared residual identity. -/
theorem alias_unify_selected_source_step
    {target pattern thenBranch elseBranch : Atom}
    {incoming independent output : Bindings} {oldTable table : TypeSubst} {depth : Nat}
    (input : BindingSourceAgreement incoming independent)
    (old : ReadoutCertificate independent oldTable)
    (occurred : (output, table) ∈
      QueryBindingProjection.AliasReadout.unifyReadouts target pattern incoming depth)
    (space : Space) (dispatch : Spec.Eval.GroundedDispatch) (live : List Atom)
    (typing : EvalTypeService) (caller : Option Atom) :
    ∃ certificate : ReadoutCertificate output table,
      let before := BindingFrame.selected independent oldTable old
      let after := BindingFrame.selected output table certificate
      UnifyCandidateRel target pattern before after ∧
      BindingFrame.Update .renew before after ∧
      Minimal.CoreStepRel space dispatch live
        (.expression [.symbol "unify", target, pattern, thenBranch, elseBranch])
        before (table.apply thenBranch, after) (typing := typing) (caller := caller) ∧
      (∀ atom readDepth, output.applyFullCovered atom readDepth = true →
        after.Materialization atom (output.applyFull atom readDepth)) ∧
      (∀ pending : List Atom,
        (pending.map oldTable.apply).map table.apply = pending.map table.apply) := by
  obtain ⟨_matched, _matching, _agreement, _model, certificate, reads⟩ :=
    QueryBindingProjection.AliasReadout.unifyReadouts_source input occurred
  refine ⟨certificate, alias_unify_source_candidate input occurred, .selected old certificate,
    ?_, ?_, ?_⟩
  · exact .unifySuccess space target pattern thenBranch elseBranch (table.apply thenBranch)
      (BindingFrame.selected independent oldTable old)
      (BindingFrame.selected output table certificate)
      (alias_unify_source_candidate input occurred) (.selected old certificate) rfl
  · intro atom readDepth covered
    exact (reads atom readDepth covered).symm
  · exact QueryBindingProjection.AliasReadout.unifyReadouts_source_pending input old occurred

/-- Every actual ordered occurrence has its own source-step occurrence. The
same selected caller is used throughout; equal records are not deduplicated. -/
theorem alias_unify_source_occurrences
    (target pattern thenBranch elseBranch : Atom)
    {incoming independent : Bindings} {oldTable : TypeSubst} (depth : Nat)
    (input : BindingSourceAgreement incoming independent)
    (old : ReadoutCertificate independent oldTable)
    (space : Space) (dispatch : Spec.Eval.GroundedDispatch) (live : List Atom)
    (typing : EvalTypeService) (caller : Option Atom) :
    ∃ outputs : List FrameResult,
      outputs.map BindingFrame.rawResult =
        QueryBindingProjection.AliasReadout.results target pattern thenBranch incoming depth ∧
      List.Forall₂ (fun entry returned =>
        returned.1 = entry.2.apply thenBranch ∧ returned.2.bindings = entry.1 ∧
        Minimal.CoreStepRel space dispatch live
          (.expression [.symbol "unify", target, pattern, thenBranch, elseBranch])
          (BindingFrame.selected independent oldTable old) returned
          (typing := typing) (caller := caller) ∧
        ∀ pending : List Atom,
          (pending.map oldTable.apply).map entry.2.apply = pending.map entry.2.apply)
        (QueryBindingProjection.AliasReadout.unifyReadouts target pattern incoming depth) outputs := by
  have build : ∀ entries : List (Bindings × TypeSubst),
      (∀ entry ∈ entries, entry ∈
        QueryBindingProjection.AliasReadout.unifyReadouts target pattern incoming depth) →
      ∃ outputs : List FrameResult,
        outputs.map BindingFrame.rawResult =
          entries.map (fun entry => (entry.2.apply thenBranch, entry.1)) ∧
        List.Forall₂ (fun entry returned =>
          returned.1 = entry.2.apply thenBranch ∧ returned.2.bindings = entry.1 ∧
          Minimal.CoreStepRel space dispatch live
            (.expression [.symbol "unify", target, pattern, thenBranch, elseBranch])
            (BindingFrame.selected independent oldTable old) returned
            (typing := typing) (caller := caller) ∧
          ∀ pending : List Atom,
            (pending.map oldTable.apply).map entry.2.apply = pending.map entry.2.apply)
          entries outputs := by
    intro entries
    induction entries with
    | nil => exact fun _ => ⟨[], rfl, .nil⟩
    | cons entry entries ih =>
      intro members
      obtain ⟨certificate, _candidate, _updated, stepped, _reads, pending⟩ :=
        alias_unify_selected_source_step (thenBranch := thenBranch) (elseBranch := elseBranch)
          input old (members entry (by simp)) space dispatch live typing caller
      obtain ⟨outputs, rows, steps⟩ := ih (fun value present => members value (by simp [present]))
      refine ⟨(entry.2.apply thenBranch, BindingFrame.selected entry.1 entry.2 certificate) :: outputs,
        ?_, .cons ⟨rfl, rfl, stepped, pending⟩ steps⟩
      simp only [List.map_cons, BindingFrame.rawResult, BindingFrame.selected, rows]
  exact build _ (fun _ member => member)

/-- The ordered source occurrences project to the exact operation used by the
recursive worker, including repeated equal results. -/
theorem unifySuccessResults_source_occurrences
    (target pattern thenBranch elseBranch : Atom)
    {incoming independent : Bindings} {oldTable : TypeSubst} (depth : Nat)
    (input : BindingSourceAgreement incoming independent)
    (old : ReadoutCertificate independent oldTable)
    (space : Space) (dispatch : Spec.Eval.GroundedDispatch) (live : List Atom)
    (typing : EvalTypeService) (caller : Option Atom) :
    ∃ outputs : List FrameResult,
      outputs.map BindingFrame.rawResult =
        unifySuccessResults target pattern thenBranch incoming depth ∧
      List.Forall₂ (fun entry returned =>
        returned.1 = entry.2.apply thenBranch ∧ returned.2.bindings = entry.1 ∧
        Minimal.CoreStepRel space dispatch live
          (.expression [.symbol "unify", target, pattern, thenBranch, elseBranch])
          (BindingFrame.selected independent oldTable old) returned
          (typing := typing) (caller := caller) ∧
        ∀ pending : List Atom,
          (pending.map oldTable.apply).map entry.2.apply = pending.map entry.2.apply)
        (QueryBindingProjection.AliasReadout.unifyReadouts target pattern incoming depth) outputs := by
  obtain ⟨outputs, projection, occurrences⟩ := alias_unify_source_occurrences
    target pattern thenBranch elseBranch depth input old space dispatch live typing caller
  exact ⟨outputs, projection.trans
    (QueryBindingProjection.AliasReadout.results_eq_unifySuccessResults _ _ _ _ _), occurrences⟩

/-- One actual reconciliation earns a related selected source frame.
The actual matcher supplies the local match witness; the independent source
merge, frame certificate, renewal and all-operand readout are constructed. -/
theorem unify_selected_frame_of_actual_merge
    {target pattern : Atom} {incoming matched output : Bindings} {fuel : Nat}
    (matching : matched ∈ matchAtoms target pattern fuel)
    (physicalMerge : output ∈ mergeBindings matched (aliasConstraints incoming) fuel)
    (acyclic : output.hasLoop = false)
    (input : BindingFrame)
    (related : SourceBindingComparison.semantic.FrameRelated incoming input) :
    ∃ next, SourceBindingComparison.semantic.FrameRelated output next ∧
      UnifyCandidateRel target pattern input next ∧ BindingFrame.Update .renew input next ∧
      ∀ atom depth, output.applyFullCovered atom depth = true →
        next.Materialization atom (output.applyFull atom depth) := by
  have occurred : (output, QueryBindingProjection.nativeReadoutPresentation output) ∈
      QueryBindingProjection.AliasReadout.unifyReadouts target pattern incoming fuel :=
    QueryBindingProjection.AliasReadout.mem_unifyReadouts.mpr
      ⟨matched, matching, QueryBindingProjection.AliasReadout.mem_mergeReadouts.mpr
        ⟨physicalMerge, acyclic, rfl⟩⟩
  cases related with
  | semantic agreement old oldReads =>
      obtain ⟨certificate, candidate, renewal, _step, reads, _pending⟩ :=
        alias_unify_selected_source_step (thenBranch := target) (elseBranch := pattern)
          agreement old occurred Space.empty noHost [] storageTypeService none
      have next : SourceBindingComparison.semantic.FrameRelated output
          (.selected output _ certificate) :=
        .semantic (.refl _) certificate (fun atom depth covered => reads atom depth covered)
      exact ⟨_, next, candidate, renewal, reads⟩

end

namespace Covered
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open RecursiveTasks FirstSuccessRecursiveExecution

theorem minimal_data_realizes (space : Space) (value : Atom) (bindings : Bindings)
    (fuel : Nat) (live : List Atom) (caller : Option Atom)
    (data : minimalInstruction value = false) :
    Realizes space (.minimal value bindings (fuel + 1) live caller) [(value, bindings)] := by
  intro stack emitted
  simpa only [FirstSuccessRecursiveStrategy.enter, RecursiveMachine.enter, data,
    Bool.false_eq_true, if_false, List.nil_append] using
    enter_request space (.minimal value bindings (fuel + 1) live caller) stack emitted

theorem minimal_instruction_realizes (space : Space) (value : Atom) (bindings : Bindings)
    (fuel : Nat) (live : List Atom) (caller : Option Atom) (results : ResultSet)
    (instruction : minimalInstruction value = true) (notChain : ¬Spec.Eval.Minimal.IsChain value)
    (child : Realizes space (.primitive value bindings fuel live caller) results) :
    Realizes space (.minimal value bindings (fuel + 1) live caller) results := by
  intro stack emitted
  have expanded : FirstSuccessRecursiveStrategy.enter space GroundedDispatch.none
      (.minimal value bindings (fuel + 1) live caller) =
        (.work (.primitive value bindings fuel live caller), []) := by
    simp only [FirstSuccessRecursiveStrategy.enter, RecursiveMachine.enter, instruction, if_true]
    split
    · exact (notChain ⟨_, rfl⟩).elim
    · rfl
  have begin := enter_request space (.minimal value bindings (fuel + 1) live caller) stack emitted
  apply begin.trans
  simpa only [expanded, List.nil_append] using child stack emitted

theorem minimals_realizes (space : Space) (fuel : Nat) (live : List Atom)
    (caller : Option Atom) {requests : ResultSet} {outputs : List ResultSet}
    (children : List.Forall₂ (fun request output =>
      Realizes space (.minimal request.1 request.2 fuel live caller) output) requests outputs) :
    Realizes space (.minimals fuel requests live caller) outputs.flatten := by
  refine (appendFrames space).traverseTasks
    (fun requests => Task.minimals fuel requests live caller)
    (fun request => Task.minimal request.1 request.2 fuel live caller) ?_ ?_ children
  · intro stack emitted
    exact enter_request space (Task.minimals fuel [] live caller) stack emitted
  · rintro ⟨value, bindings⟩ rest stack emitted
    exact enter_request space (Task.minimals fuel (⟨value, bindings⟩ :: rest) live caller)
      stack emitted

theorem primitive_unify_realizes (space : Space) (target pattern yes no : Atom)
    (incoming : Bindings) (fuel : Nat) (live : List Atom) (caller : Option Atom)
    (covered : unifyMatchesCovered target pattern incoming fuel = true) :
    Realizes space (.primitive (.expression [.symbol "unify", target, pattern, yes, no])
      incoming (fuel + 1) live caller)
      (let results := unifySuccessResults target pattern yes incoming fuel
       if results.isEmpty then [(no, incoming)] else results) := by
  intro stack emitted
  have ready : FirstSuccessRecursiveStrategy.taskReady space GroundedDispatch.none
      (.primitive (.expression [.symbol "unify", target, pattern, yes, no])
        incoming (fuel + 1) live caller) = true := covered
  simpa only [FirstSuccessRecursiveStrategy.enter, RecursiveMachine.enter, List.nil_append] using
    enter_request space (.primitive (.expression [.symbol "unify", target, pattern, yes, no])
      incoming (fuel + 1) live caller) stack emitted ready

end Covered

namespace Covered
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open RecursiveTasks FirstSuccessRecursiveExecution
/-- Raw embedded invocation uses the same minimal worker and simply returns
its exact rows through the raw receiver. -/
theorem raw_embedded_realizes (space : Space) (name : String) (arguments : List Atom)
    (incoming : Bindings) (fuel : Nat) (live : List Atom) (caller : Option Atom)
    (results : ResultSet)
    (instruction : minimalInstruction (.expression (.symbol name :: arguments)) = true)
    (child : Realizes space (.minimal (.expression (.symbol name :: arguments)) incoming fuel
      live caller) results) :
    Realizes space (.invocation .raw (.expression (.symbol name :: arguments)) incoming
      (fuel + 1) live caller) results := by
  intro stack emitted
  let atom := Atom.expression (.symbol name :: arguments)
  let receiver := Frame.invocationReturn .raw atom fuel live
  have invocation := enter_request space
    (.invocation .raw atom incoming (fuel + 1) live caller) stack emitted (by
      simp [FirstSuccessRecursiveStrategy.taskReady, RecursiveMachine.Checked.taskReady, atom, instruction])
  have continued := consume_continuation space receiver results stack emitted
  exact invocation.trans (by
    simpa [atom, receiver, FirstSuccessRecursiveStrategy.enter, RecursiveMachine.enter,
      InvocationMode.errorPassthrough, InvocationMode.pendingScope, GroundedDispatch.none,
      instruction, RecursiveMachine.resume] using
      (child (receiver :: stack) emitted).trans continued)
/-- Nested flattening keeps the candidate and prepared-row occurrences while
executing the existing producer list worker. -/
theorem equation_productions_realizes (space : Space) (incoming : Bindings) (fuel : Nat)
    (live : List Atom) (caller : Option Atom) (candidates : ResultSet)
    (outputs : ResultPair → ResultPair → ResultSet)
    (children : ∀ candidate ∈ candidates, ∀ request ∈ equationInputs incoming fuel candidate,
      Realizes space (.produced request.1 request.2 fuel live caller .emitted) (outputs candidate request)) :
    Realizes space (.productions fuel (candidates.flatMap (equationInputs incoming fuel)) live caller .emitted)
      (candidates.flatMap fun candidate => (equationInputs incoming fuel candidate).flatMap (outputs candidate)) := by
  have grouped : List.Forall₂ (List.Forall₂ fun request output =>
      Realizes space (.produced request.1 request.2 fuel live caller .emitted) output)
      (candidates.map (equationInputs incoming fuel))
      (candidates.map fun candidate => (equationInputs incoming fuel candidate).map (outputs candidate)) := by
    apply List.forall₂_map_left_iff.mpr
    apply List.forall₂_map_right_iff.mpr
    apply List.forall₂_same.mpr
    intro candidate member
    exact List.forall₂_map_right_iff.mpr (List.forall₂_same.mpr (children candidate member))
  have joined := productions_realizes space fuel live caller .emitted (List.rel_flatten grouped)
  simpa only [List.flatten_eq_flatMap, List.flatMap_assoc, List.flatMap_map, id_eq] using joined

theorem raw_query_realizes (space : Space) (name : String) (arguments : List Atom)
    (incoming : Bindings) (fuel : Nat) (live : List Atom) (caller : Option Atom)
    (nonembedded : minimalInstruction (.expression (.symbol name :: arguments)) = false)
    (results : ResultSet)
    (queryCovered : queryEquationsCovered
      (equationScope live (.expression (.symbol name :: arguments)) Atom.undefinedType incoming)
      space (.expression (.symbol name :: arguments)) fuel = true)
    (inputsCovered : ∀ candidate ∈ equationCandidates space live
        (.expression (.symbol name :: arguments)) Atom.undefinedType incoming fuel,
      matchCovered fuel (.merge candidate.2 (aliasConstraints incoming)) = true ∧
      ∀ merged ∈ mergeBindings candidate.2 (aliasConstraints incoming) fuel, merged.hasLoop = false →
        merged.applyFullCovered candidate.1 fuel = true)
    (body : Realizes space (.producerResults .raw
      (.expression (.symbol name :: arguments)) incoming fuel live Atom.notReducible
      (rawQueryResults space (.expression (.symbol name :: arguments)) Atom.undefinedType incoming fuel live)) results) :
    Realizes space (.invocation .raw (.expression (.symbol name :: arguments)) incoming
      (fuel + 1) live caller) results := by
  intro stack emitted
  let query := Atom.expression (.symbol name :: arguments)
  let after := Frame.producerResults .raw query incoming fuel live Atom.notReducible
  have ready : FirstSuccessRecursiveStrategy.taskReady space GroundedDispatch.none
      (.invocation .raw query incoming (fuel + 1) live caller) = true := by
    simpa [FirstSuccessRecursiveStrategy.taskReady, RecursiveMachine.Checked.taskReady,
      InvocationMode.errorPassthrough, GroundedDispatch.none, nonembedded,
      InvocationMode.expected, query] using queryCovered
  have invoked := enter_request space
    (.invocation .raw query incoming (fuel + 1) live caller) stack emitted ready
  have prepared := equations_read_realizes space query Atom.undefinedType incoming fuel live
    (equationCandidates space live query Atom.undefinedType incoming fuel)
    inputsCovered (after :: stack) emitted
  have resumed := consume_continuation space after
    (rawQueryResults space query Atom.undefinedType incoming fuel live) stack emitted
  apply invoked.trans
  simpa only [FirstSuccessRecursiveStrategy.enter, RecursiveMachine.enter,
    InvocationMode.errorPassthrough, Bool.false_eq_true, if_false,
    GroundedDispatch.none, nonembedded, InvocationMode.expected, List.nil_append,
    List.cons_append, query] using prepared.trans (resumed.trans (by
      simpa only [RecursiveMachine.resume, List.nil_append, after,
        rawQueryResults, equationInputs] using body stack emitted))

theorem raw_producer_results_realizes (space : Space) (original : Atom)
    (incoming : Bindings) (fuel : Nat) (live : List Atom) (raw results : ResultSet)
    (present : raw ≠ [])
    (production : Realizes space (.productions fuel raw live (some original) .emitted) results) :
    Realizes space (.producerResults .raw original incoming fuel live Atom.notReducible raw) results := by
  intro stack emitted
  let receiver := Frame.invocationReturn .raw original fuel live
  have begin := enter_request space
    (.producerResults .raw original incoming fuel live Atom.notReducible raw) stack emitted
  have resumed := consume_continuation space receiver results stack emitted
  apply begin.trans
  have nonempty := List.isEmpty_eq_false_iff.mpr present
  simpa only [FirstSuccessRecursiveStrategy.enter, RecursiveMachine.enter, nonempty,
    Bool.false_eq_true, if_false, InvocationMode.pendingScope, List.cons_append, List.nil_append,
    receiver, RecursiveMachine.resume] using (production (receiver :: stack) emitted).trans resumed

theorem raw_producer_refused_realizes (space : Space) (original : Atom)
    (incoming : Bindings) (fuel : Nat) (live : List Atom) :
    Realizes space (.producerResults .raw original incoming fuel live Atom.notReducible [])
      [(Atom.notReducible, incoming)] := by
  intro stack emitted
  let receiver := Frame.invocationReturn .raw original fuel live
  have begin := enter_request space
    (.producerResults .raw original incoming fuel live Atom.notReducible []) stack emitted
  have resumed := consume_continuation space receiver [(Atom.notReducible, incoming)] stack emitted
  exact begin.trans (by
    simpa only [FirstSuccessRecursiveStrategy.enter, RecursiveMachine.enter, List.isEmpty_nil,
      if_true, List.cons_append, List.nil_append, receiver, RecursiveMachine.resume] using resumed)

theorem primitive_eval_realizes (space : Space) (atom : Atom) (incoming : Bindings)
    (fuel : Nat) (live : List Atom) (caller : Option Atom) (results : ResultSet)
    (covered : incoming.applyFullCovered atom fuel = true)
    (child : Realizes space (.invocation .raw (incoming.applyFull atom fuel) incoming fuel live caller) results) :
    Realizes space (.primitive (.expression [.symbol "eval", atom]) incoming (fuel + 1) live caller) results := by
  intro stack emitted
  have ready : FirstSuccessRecursiveStrategy.taskReady space GroundedDispatch.none
      (.primitive (.expression [.symbol "eval", atom]) incoming (fuel + 1) live caller) = true := covered
  have begin := enter_request space
    (.primitive (.expression [.symbol "eval", atom]) incoming (fuel + 1) live caller) stack emitted ready
  exact begin.trans (by
    simpa only [FirstSuccessRecursiveStrategy.enter, RecursiveMachine.enter, List.nil_append]
      using child stack emitted)

theorem chain_rows_realizes (space : Space) (name : String) (template : Atom) (fuel : Nat)
    (rows : ResultSet) (covered : ∀ result ∈ rows, result.2.applyFullCovered result.1 fuel = true) :
    Realizes space (.chainRows name template fuel rows)
      (rows.map fun result => (chainSubstitute name (result.2.applyFull result.1 fuel) template, result.2)) := by
  have run := (appendFrames space).traverseMap
      (fun requests => Task.chainRows name template fuel requests)
      (fun row => [(chainSubstitute name (row.2.applyFull row.1 fuel) template, row.2)])
      (fun stack emitted => enter_request space (.chainRows name template fuel []) stack emitted)
      rows (by
        rintro ⟨value, bindings⟩ member rest stack emitted
        exact enter_request space (.chainRows name template fuel (⟨value, bindings⟩ :: rest))
          stack emitted (covered ⟨value, bindings⟩ member))
  rw [← List.map_eq_flatMap] at run
  exact run

theorem primitive_chain_realizes (space : Space) (atom : Atom) (name : String) (template : Atom)
    (incoming : Bindings) (fuel : Nat) (live : List Atom) (caller : Option Atom) (raw : ResultSet)
    (child : Realizes space (.minimal atom incoming fuel
      (.expression [.symbol "chain", atom, .var name, template] :: live)
      (some (.expression [.symbol "chain", atom, .var name, template]))) raw)
    (covered : ∀ result ∈ raw, result.2.applyFullCovered result.1 fuel = true) :
    Realizes space (.primitive (.expression [.symbol "chain", atom, .var name, template])
      incoming (fuel + 1) live caller)
      (raw.map fun result => (chainSubstitute name (result.2.applyFull result.1 fuel) template, result.2)) := by
  refine FramedPath.trans (third := []) (FramedPath.receive (first := []) (last := []) (receiver := Frame.chainResults name template fuel) ?_ child ?_)
    (chain_rows_realizes space name template fuel raw covered)
  · intro stack emitted
    exact enter_request space (.primitive (.expression [.symbol "chain", atom, .var name, template]) incoming (fuel + 1) live caller) stack emitted
  · intro stack emitted
    exact consume_continuation space (Frame.chainResults name template fuel) raw stack emitted

theorem minimal_chain_realizes (space : Space) (atom : Atom) (name : String) (template : Atom)
    (incoming : Bindings) (fuel : Nat) (live : List Atom) (caller : Option Atom) (raw results : ResultSet)
    (child : Realizes space (.primitive (.expression [.symbol "chain", atom, .var name, template])
      incoming fuel live caller) raw)
    (continuation : Realizes space (.minimals fuel raw live caller) results) :
    Realizes space (.minimal (.expression [.symbol "chain", atom, .var name, template])
      incoming (fuel + 1) live caller) results := by
  refine FramedPath.trans (third := []) (FramedPath.receive (first := []) (last := []) (receiver := Frame.minimalResults fuel live caller) ?_ child ?_)
    (continuation)
  · intro stack emitted
    exact enter_request space (.minimal (.expression [.symbol "chain", atom, .var name, template]) incoming (fuel + 1) live caller) stack emitted
  · intro stack emitted
    exact consume_continuation space (Frame.minimalResults fuel live caller) raw stack emitted

end Covered

section
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open RecursiveTasks FirstSuccessRecursiveExecution
open Spec.Eval Spec.Eval.Steps Spec.Type.Presentation

mutual
/-- Producer meaning is independently constructed from the actual primitive
body derivation, retaining its reached selected frame. -/
theorem ProducedDerivation.sound {space : Space} {comparison : SourceBindingComparison}
    {live : List Atom} {caller : Option Atom} {value : Atom} {incoming : Bindings}
    {fuel : Nat} {results : ResultSet}
    (derived : ProducedDerivation space comparison live caller value incoming fuel results)
    (result : ResultPair) (member : result ∈ results) (input : BindingFrame)
    (related : comparison.FrameRelated incoming input) (scope : List String := []) :
    ∃ output, Minimal.CoreInvocationResultRel space noHost live (protectedScope := scope) (caller := caller)
      value input (result.1, output) ∧ comparison.FrameRelated result.2 output := by
  cases derived with
  | raw live caller value incoming fuel ordinary =>
      obtain rfl := List.mem_singleton.mp member
      exact ⟨input, .raw space value input ordinary, related⟩
  | function live caller body incoming fuel results semantic child =>
      cases semantic
      obtain ⟨output, invoked, next⟩ := child.sound result member input related scope
      exact ⟨output, .function space body input _ invoked, next⟩
termination_by fuel

theorem RawInvocationDerivation.sound {space : Space} {live : List Atom} {caller : Option Atom}
    {value : Atom} {incoming : Bindings} {fuel : Nat} {results : ResultSet}
    (derived : RawInvocationDerivation space .semantic live caller value incoming fuel results)
    (result : ResultPair) (member : result ∈ results) (input : BindingFrame)
    (related : SourceBindingComparison.semantic.FrameRelated incoming input) (scope : List String := []) :
    ∃ output, Minimal.CoreInvocationRel space noHost live (protectedScope := scope) (caller := caller)
      value input (result.1, output) ∧
      SourceBindingComparison.semantic.FrameRelated result.2 output := by
  cases derived with
  | embedded live caller name arguments incoming fuel results instruction child =>
      obtain ⟨output, source, next⟩ := child.sound result member input related scope
      exact ⟨output, .embedded space _ input _ (by simp [Minimal.HostCall, noHost])
        ((classifier_agrees _).symm.trans instruction) source, next⟩
  | unreduced live caller name arguments incoming fuel instruction covered empty absent =>
      obtain rfl := List.mem_singleton.mp member
      exact ⟨input, .noEquation space _ input (by simp [Minimal.HostCall, noHost])
        ((classifier_agrees _).symm.trans instruction) (related.noMatch space _ _ absent), related⟩
  | equations live caller name arguments incoming fuel outputs instruction covered inputs present evidence producers =>
      obtain ⟨candidate, candidateMember, produced⟩ := List.mem_flatMap.mp member
      obtain ⟨request, requestMember, produced⟩ := List.mem_flatMap.mp produced
      obtain ⟨middle, middleRelated, ⟨position, left, right, matched, rhs, occurrence⟩, materialized⟩ :=
        (evidence candidate candidateMember request requestMember).transport input related
      obtain ⟨output, completion, next⟩ :=
        (producers candidate candidateMember request requestMember).sound result produced middle middleRelated scope
      refine ⟨output, .equation space _ candidate.1 request.1 input middle _
        (by simp [Minimal.HostCall, noHost]) ((classifier_agrees _).symm.trans instruction)
        ?_ (related.renew middleRelated) materialized completion, next⟩
      have selected := occurrence.selected
      obtain ⟨⟨rename, injective, leftRenamed, rightRenamed, fresh⟩, matching⟩ := selected
      exact ⟨_, _, matched, ⟨left, right, List.mem_of_getElem? occurrence.stored,
        ⟨rename, injective, leftRenamed, rightRenamed, fun key occurs visible =>
          fresh key occurs (queryVisible_cons visible)⟩, matching⟩, occurrence.result⟩
termination_by fuel


/-- Actual minimal paths preserve an independently selected source frame. -/
theorem MinimalDerivation.sound {space : Space} {live : List Atom} {caller : Option Atom}
    {value : Atom} {incoming : Bindings} {fuel : Nat} {results : ResultSet}
    (derived : MinimalDerivation (comparison := .semantic) space live caller value incoming fuel results)
    (result : ResultPair) (member : result ∈ results) (input : BindingFrame)
    (related : SourceBindingComparison.semantic.FrameRelated incoming input) (scope : List String := []) :
    ∃ output, Minimal.CoreRunRel space noHost live (protectedScope := scope) (caller := caller)
      value input (result.1, output) ∧
      SourceBindingComparison.semantic.FrameRelated result.2 output := by
  cases derived with
  | data live caller value incoming fuel data =>
      obtain rfl := List.mem_singleton.mp member
      exact ⟨input, .data space value input ((classifier_agrees value).symm.trans data), related⟩
  | instruction live caller value incoming fuel results instruction notChain child =>
      obtain ⟨output, source, next⟩ := child.sound result member input related scope
      exact ⟨output, .instruction space value input (result.1, output)
        ((classifier_agrees value).symm.trans instruction) notChain source, next⟩
  | chain live caller atom name template incoming fuel raw outputs child continuations =>
      obtain ⟨middle, present, produced⟩ := List.mem_flatMap.mp member
      obtain ⟨middleFrame, source, middleRelated⟩ := child.sound middle present input related scope
      obtain ⟨output, resumed, next⟩ := (continuations middle present).sound result produced middleFrame middleRelated scope
      exact ⟨output, .chain space _ input (middle.1, middleFrame) (result.1, output)
        ⟨_, rfl⟩ source resumed, next⟩
termination_by fuel

/-- The primitive source witness uses the actual merge output's earned whole
readout table; successful return and NoReturn preserve that same frame. -/
theorem PrimitiveDerivation.sound {space : Space} {live : List Atom} {caller : Option Atom}
    {value : Atom} {incoming : Bindings} {fuel : Nat} {results : ResultSet}
    (derived : PrimitiveDerivation (comparison := .semantic) space live caller value incoming fuel results)
    (result : ResultPair) (member : result ∈ results) (input : BindingFrame)
    (related : SourceBindingComparison.semantic.FrameRelated incoming input) (scope : List String := []) :
    ∃ output, Minimal.CoreStepRel space noHost live (protectedScope := scope) (caller := caller)
      value input (result.1, output) ∧
      SourceBindingComparison.semantic.FrameRelated result.2 output := by
  cases derived with
  | eval live caller atom incoming fuel results covered child =>
      obtain ⟨output, source, next⟩ := child.sound result member input related scope
      exact ⟨output, .eval space atom _ input _ (related.materialization atom fuel covered) source, next⟩
  | chain live caller atom name template incoming fuel raw child covered =>
      obtain ⟨selected, present, rfl⟩ := List.mem_map.mp member
      obtain ⟨output, source, next⟩ := child.sound selected present input related scope
      refine ⟨output, ?_, next⟩
      simpa only [chainSubstitute_eq_substituteName] using
        Minimal.CoreStepRel.chain (dispatch := noHost) (live := live) (caller := caller)
          space atom name template input (selected.1, output) _ source
          (next.materialization selected.1 fuel (covered selected present))
  | unifySuccess live caller target pattern yes no incoming fuel covered nonempty =>
      obtain ⟨matched, matchedMember, mergedMember⟩ := List.mem_flatMap.mp member
      obtain ⟨merged, mergeMember, emitted⟩ := List.mem_filterMap.mp mergedMember
      cases loop : merged.hasLoop with
      | true => simp [loop] at emitted
      | false =>
          have pair : (merged.applyFull yes (merged.resolutionFuel yes), merged) = result := by
            simpa only [loop, Bool.false_eq_true, if_false, Option.some.injEq] using emitted
          cases pair
          obtain ⟨output, next, candidate, renewed, read⟩ :=
            unify_selected_frame_of_actual_merge matchedMember mergeMember loop input related
          exact ⟨output, .unifySuccess space target pattern yes no _ input output
            candidate renewed (read yes _ (merged.applyFullCovered_resolutionFuel yes)), next⟩
  | unifyNoMatch live caller target pattern yes no incoming fuel covered empty =>
      obtain rfl := List.mem_singleton.mp member
      exact ⟨input, .unifyNoMatch space target pattern yes no input
        (related.agreement.unifyNoMatch
          ((QueryBindingProjection.AliasReadout.covered_unify_empty_iff covered).mp empty)), related⟩
  | consAtom live caller head tail incoming fuel =>
      obtain rfl := List.mem_singleton.mp member
      exact ⟨input, .consAtom space head tail input, related⟩
  | deconsAtom live caller head tail incoming fuel =>
      obtain rfl := List.mem_singleton.mp member
      exact ⟨input, .deconsAtom space head tail input, related⟩
  | function live caller parts incoming fuel terminals child =>
      obtain ⟨terminal, present, rfl⟩ := List.mem_map.mp member
      obtain ⟨output, source, next⟩ := child.sound terminal present input related scope
      by_cases returns : ∃ returned, terminal.1 = .expression [.symbol "return", returned]
      · obtain ⟨returned, same⟩ := returns
        refine ⟨output, ?_, next⟩
        simpa only [same, functionTerminal] using
          Minimal.CoreStepRel.functionReturn (dispatch := noHost) (live := live) (caller := caller)
            space (.expression parts) returned input output ⟨parts, rfl⟩ (same ▸ source)
      · refine ⟨output, ?_, next⟩
        exact Minimal.CoreStepRel.functionNoReturn space (.expression parts) terminal.1 input output
          ⟨parts, rfl⟩ source (by simpa only [not_exists] using returns)
termination_by fuel

/-- Every body resumption reads the reached child frame, preserving shared
pending variables and their exact source materialization. -/
theorem FunctionBodyDerivation.sound {space : Space} {live : List Atom} {caller : Option Atom}
    {value : Atom} {incoming : Bindings} {fuel : Nat} {results : ResultSet}
    (derived : FunctionBodyDerivation (comparison := .semantic) space live caller value incoming fuel results)
    (result : ResultPair) (member : result ∈ results) (input : BindingFrame)
    (related : SourceBindingComparison.semantic.FrameRelated incoming input) (scope : List String := []) :
    ∃ output, Minimal.CoreFunctionBodyRel space noHost live (protectedScope := scope) (caller := caller)
      value input (result.1, output) ∧
      SourceBindingComparison.semantic.FrameRelated result.2 output := by
  cases derived with
  | run live caller value incoming fuel raw outputs child covered terminal resumed =>
      obtain ⟨selected, present, produced⟩ := List.mem_flatMap.mp member
      obtain ⟨middle, source, middleRelated⟩ := child.sound selected present input related scope
      have read := middleRelated.materialization selected.1 fuel (covered selected present)
      cases instruction : minimalInstruction (selected.2.applyFull selected.1 fuel) with
      | false =>
          rw [terminal selected present instruction] at produced
          obtain rfl := List.mem_singleton.mp produced
          exact ⟨middle, .terminal space value input (selected.1, middle) _ source read
            ((classifier_agrees _).symm.trans instruction), middleRelated⟩
      | true =>
          obtain ⟨output, continuation, next⟩ :=
            (resumed selected present instruction).sound result produced middle middleRelated scope
          exact ⟨output, .resume space value input (selected.1, middle) _ (result.1, output)
            source read ((classifier_agrees _).symm.trans instruction) continuation, next⟩
termination_by fuel
end

mutual
theorem ProducedDerivation.covered_realizes {space : Space} {comparison : SourceBindingComparison}
    {live : List Atom} {caller : Option Atom} {value : Atom} {incoming : Bindings}
    {fuel : Nat} {results : ResultSet}
    (derived : ProducedDerivation space comparison live caller value incoming fuel results) :
    Covered.Realizes space (.produced value incoming fuel live caller .emitted) results := by
  cases derived with
  | raw live caller value incoming fuel ordinary =>
      exact Covered.produced_ordinary_realizes space value incoming fuel live caller ordinary
  | function live caller body incoming fuel results semantic child =>
      cases semantic
      exact Covered.produced_function_realizes space body incoming fuel live caller results child.covered_realizes
termination_by fuel

theorem RawInvocationDerivation.covered_realizes {space : Space} {live : List Atom} {caller : Option Atom}
    {value : Atom} {incoming : Bindings} {fuel : Nat} {results : ResultSet}
    (derived : RawInvocationDerivation space .semantic live caller value incoming fuel results) :
    Covered.Realizes space (.invocation .raw value incoming fuel live caller) results := by
  cases derived with
  | embedded live caller name arguments incoming fuel results instruction child =>
      exact Covered.raw_embedded_realizes space name arguments incoming fuel live caller results
        instruction child.covered_realizes
  | unreduced live caller name arguments incoming fuel instruction covered empty absent =>
      apply Covered.raw_query_realizes space name arguments incoming fuel live caller instruction _ covered
        (by intro candidate present; rw [empty] at present; exact (List.not_mem_nil present).elim)
      simpa only [rawQueryResults, empty, List.flatMap_nil] using
        Covered.raw_producer_refused_realizes space (.expression (.symbol name :: arguments)) incoming fuel live
  | equations live caller name arguments incoming fuel outputs instruction covered inputs present evidence producers =>
      apply Covered.raw_query_realizes space name arguments incoming fuel live caller instruction _ covered inputs
      apply Covered.raw_producer_results_realizes space _ incoming fuel live _ _ present
      exact Covered.equation_productions_realizes space incoming fuel live
        (some (.expression (.symbol name :: arguments))) _ outputs
        (fun candidate member request selected => (producers candidate member request selected).covered_realizes)
termination_by fuel


/-- Source admission earns the actual guarded minimal path. -/
theorem MinimalDerivation.covered_realizes {space : Space} {live : List Atom} {caller : Option Atom}
    {value : Atom} {incoming : Bindings} {fuel : Nat} {results : ResultSet}
    (derived : MinimalDerivation (comparison := .semantic) space live caller value incoming fuel results) :
    Covered.Realizes space (.minimal value incoming fuel live caller) results := by
  cases derived with
  | data live caller value incoming fuel data =>
      exact Covered.minimal_data_realizes space value incoming fuel live caller data
  | instruction live caller value incoming fuel results instruction notChain child =>
      exact Covered.minimal_instruction_realizes space value incoming fuel live caller results
        instruction notChain child.covered_realizes
  | chain live caller atom name template incoming fuel raw outputs child continuations =>
      apply Covered.minimal_chain_realizes space atom name template incoming fuel live caller raw _ child.covered_realizes
      have children : List.Forall₂ (fun request output =>
          Covered.Realizes space (.minimal request.1 request.2 fuel live caller) output)
          raw (raw.map outputs) :=
        List.forall₂_map_right_iff.mpr (List.forall₂_same.mpr fun request present =>
          (continuations request present).covered_realizes)
      simpa only [← List.flatMap_def] using Covered.minimals_realizes space fuel live caller children
termination_by fuel

theorem PrimitiveDerivation.covered_realizes {space : Space} {live : List Atom} {caller : Option Atom}
    {value : Atom} {incoming : Bindings} {fuel : Nat} {results : ResultSet}
    (derived : PrimitiveDerivation (comparison := .semantic) space live caller value incoming fuel results) :
    Covered.Realizes space (.primitive value incoming fuel live caller) results := by
  cases derived with
  | eval live caller atom incoming fuel results covered child =>
      exact Covered.primitive_eval_realizes space atom incoming fuel live caller results covered child.covered_realizes
  | chain live caller atom name template incoming fuel raw child covered =>
      exact Covered.primitive_chain_realizes space atom name template incoming fuel live caller raw
        child.covered_realizes covered
  | unifySuccess live caller target pattern yes no incoming fuel covered nonempty =>
      simpa only [List.isEmpty_eq_false_iff.mpr nonempty, Bool.false_eq_true, if_false] using
        Covered.primitive_unify_realizes space target pattern yes no incoming fuel live caller covered
  | unifyNoMatch live caller target pattern yes no incoming fuel covered empty =>
      simpa only [empty, List.isEmpty_nil, if_true] using
        Covered.primitive_unify_realizes space target pattern yes no incoming fuel live caller covered
  | consAtom live caller head tail incoming fuel =>
      intro stack emitted
      simpa only [FirstSuccessRecursiveStrategy.enter, RecursiveMachine.enter, List.nil_append] using
        Covered.enter_request space
          (.primitive (.expression [.symbol "cons-atom", head, .expression tail])
            incoming (fuel + 1) live caller) stack emitted
  | deconsAtom live caller head tail incoming fuel =>
      intro stack emitted
      simpa only [FirstSuccessRecursiveStrategy.enter, RecursiveMachine.enter, List.nil_append] using
        Covered.enter_request space
          (.primitive (.expression [.symbol "decons-atom", .expression (head :: tail)])
            incoming (fuel + 1) live caller) stack emitted
  | function live caller parts incoming fuel terminals child =>
      exact Covered.function_primitive_realizes space parts incoming fuel live caller terminals
        child.covered_realizes
termination_by fuel

theorem FunctionBodyDerivation.covered_realizes {space : Space} {live : List Atom} {caller : Option Atom}
    {value : Atom} {incoming : Bindings} {fuel : Nat} {results : ResultSet}
    (derived : FunctionBodyDerivation (comparison := .semantic) space live caller value incoming fuel results) :
    Covered.Realizes space (.functionBody value incoming fuel live caller) results := by
  cases derived with
  | run live caller value incoming fuel raw outputs child covered terminal resumed =>
      apply Covered.function_body_realizes space value incoming fuel live caller raw _ child.covered_realizes
      have children : List.Forall₂ (fun request output =>
          request.2.applyFullCovered request.1 fuel = true ∧
          if minimalInstruction (request.2.applyFull request.1 fuel) then
            Covered.Realizes space (.functionBody (request.2.applyFull request.1 fuel)
              request.2 fuel live caller) output
          else output = [(request.2.applyFull request.1 fuel, request.2)]) raw (raw.map outputs) := by
        apply List.forall₂_map_right_iff.mpr
        apply List.forall₂_same.mpr
        intro request present
        refine ⟨covered request present, ?_⟩
        cases instruction : minimalInstruction (request.2.applyFull request.1 fuel) with
        | false => simpa only [instruction, Bool.false_eq_true, if_false] using terminal request present instruction
        | true => simpa only [instruction, if_true] using (resumed request present instruction).covered_realizes
      simpa only [← List.flatMap_def] using
        Covered.body_results_realizes space fuel live caller children
termination_by fuel
end

end

namespace Covered
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open RecursiveTasks FirstSuccessRecursiveExecution

/-- Removing a local readiness guard from an already guarded silent path
preserves the exact configurations; it does not assert service coverage. -/
theorem unchecked {space : Space} {task : Task} {results : ResultSet}
    (path : Realizes space task results) :
    FirstSuccessSourceExecution.Realizes space task results := by
  intro stack emitted
  refine Relation.ReflTransGen.mono ?_ _ _ (path stack emitted)
  intro before after advanced
  change (Checked.machine GroundedDispatch.none).step before = some (.silent after) at advanced
  change (FirstSuccessRecursiveExecution.machine GroundedDispatch.none).step before = some (.silent after)
  simp only [Checked.machine, RecursiveMachine.Checked.guardMachine] at advanced
  split at advanced
  · simp at advanced
  · cases stepped : (FirstSuccessRecursiveExecution.machine GroundedDispatch.none).step before with
    | none => simp [stepped] at advanced
    | some action =>
        cases action <;> simp_all [Mettapedia.GSLT.Distinction.ProductiveBlocks.Transition.relabel]

/-- The ordinary invocation receiver consumes the actual raw row list before
running the typed return continuations. No function syntax is reclassified. -/
theorem ordinary_embedded_realizes (space : Space) (name : String) (arguments : List Atom)
    (expected : Atom) (incoming : Bindings) (fuel : Nat) (live : List Atom)
    (raw results : ResultSet)
    (clean : name ≠ "Error")
    (instruction : minimalInstruction (.expression (.symbol name :: arguments)) = true)
    (child : Realizes space (.minimal (.expression (.symbol name :: arguments)) incoming fuel
      (expected :: live) none) raw)
    (returned : Realizes space
      (.returns (.expression (.symbol name :: arguments)) expected fuel raw live) results) :
    Realizes space (.call (.expression (.symbol name :: arguments)) expected incoming (fuel + 1) live) results := by
  intro stack emitted
  let atom := Atom.expression (.symbol name :: arguments)
  let receiver := Frame.invocationReturn (.ordinary expected) atom fuel live
  have call := enter_request space (.call atom expected incoming (fuel + 1) live) stack emitted
  have invocation := enter_request space
    (.invocation (.ordinary expected) atom incoming (fuel + 1) live none) stack emitted (by
      simp [FirstSuccessRecursiveStrategy.taskReady, RecursiveMachine.Checked.taskReady, atom, instruction])
  have continued := consume_continuation space receiver raw stack emitted
  have tail := continued.trans (by
    simpa only [receiver, RecursiveMachine.resume, List.nil_append] using returned stack emitted)
  have run := invocation.trans (by
    simpa [atom, receiver, FirstSuccessRecursiveStrategy.enter, RecursiveMachine.enter,
      InvocationMode.errorPassthrough, InvocationMode.pendingScope, GroundedDispatch.none,
      isErrorAtom, clean, instruction] using
      (child (receiver :: stack) emitted).trans tail)
  exact call.trans (by
    simpa only [FirstSuccessRecursiveStrategy.enter, RecursiveMachine.enter, List.nil_append] using run)

end Covered

section
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open RecursiveTasks FirstSuccessRecursiveExecution FirstSuccessRawExecution

/-- The ordinary invocation receiver consumes the actual raw row list before
running the typed return continuations. No function syntax is reclassified. -/
theorem ordinary_embedded_realizes (space : Space) (name : String) (arguments : List Atom)
    (expected : Atom) (incoming : Bindings) (fuel : Nat) (live : List Atom)
    (raw results : ResultSet)
    (clean : name ≠ "Error")
    (instruction : minimalInstruction (.expression (.symbol name :: arguments)) = true)
    (child : Realizes space (.minimal (.expression (.symbol name :: arguments)) incoming fuel
      (expected :: live) none) raw)
    (returned : Realizes space
      (.returns (.expression (.symbol name :: arguments)) expected fuel raw live) results) :
    Realizes space (.call (.expression (.symbol name :: arguments)) expected incoming (fuel + 1) live) results := by
  intro stack emitted
  let atom := Atom.expression (.symbol name :: arguments)
  let receiver := Frame.invocationReturn (.ordinary expected) atom fuel live
  have call := enter_request space GroundedDispatch.none (.call atom expected incoming (fuel + 1) live) stack emitted
  have invocation := enter_request space GroundedDispatch.none
    (.invocation (.ordinary expected) atom incoming (fuel + 1) live none) stack emitted
  have continued := consume_continuation space GroundedDispatch.none receiver raw stack emitted
  have tail := continued.trans (by
    simpa only [receiver, RecursiveMachine.resume, List.nil_append] using returned stack emitted)
  have run := invocation.trans (by
    simpa [atom, receiver, FirstSuccessRecursiveStrategy.enter, RecursiveMachine.enter,
      InvocationMode.errorPassthrough, InvocationMode.pendingScope, GroundedDispatch.none,
      isErrorAtom, clean, instruction] using
      (child (receiver :: stack) emitted).trans tail)
  exact call.trans (by
    simpa only [FirstSuccessRecursiveStrategy.enter, RecursiveMachine.enter, List.nil_append] using run)


end

/-- The historical record comparison retains the equation-only admission.
Selected-frame minimal paths use their actual instruction and return witnesses. -/
theorem CallDerivation.nonembedded {space : Space} {comparison : SourceBindingComparison}
    {live : List Atom} {query expected : Atom} {incoming : Bindings}
    {fuel : Nat} {results : ResultSet}
    (derived : CallDerivation (comparison := comparison) space live query expected incoming fuel results)
    (historical : comparison = .records) :
    Spec.Eval.Minimal.embeddedInstruction query = false := by
  cases derived with
  | errorPassthrough _ value _ _ _ error =>
      rcases error with ⟨tail, rfl⟩
      rfl
  | embedded _ _ _ _ _ _ _ _ semantic _ _ _ _ => cases historical.symm.trans semantic
  | unreduced => assumption
  | equations => assumption

/-- A recognized instruction cannot enter the historical equation-only lane. -/
theorem CallDerivation.not_of_embedded {space : Space} {comparison : SourceBindingComparison}
    {live : List Atom} {query expected : Atom} {incoming : Bindings}
    {fuel : Nat} {results : ResultSet}
    (historical : comparison = .records)
    (embedded : Spec.Eval.Minimal.embeddedInstruction query = true) :
    ¬CallDerivation (comparison := comparison) space live query expected incoming fuel results := by
  intro derived
  have ordinary := derived.nonembedded historical
  rw [embedded] at ordinary
  contradiction

/-- The real function annotation cannot license the former wrong fallback. -/
theorem function_equation_admission_refused (space : Space)
    (comparison : SourceBindingComparison) (live : List Atom) (body expected : Atom)
    (incoming : Bindings) (fuel : Nat) (results : ResultSet)
    (historical : comparison = .records) :
    ¬CallDerivation (comparison := comparison) space live
      (.expression [.symbol "function", body]) expected incoming fuel results :=
  CallDerivation.not_of_embedded historical rfl

/-- Explicit raw evaluation also requires its actual instruction path. -/
theorem eval_equation_admission_refused (space : Space)
    (comparison : SourceBindingComparison) (live : List Atom) (body expected : Atom)
    (incoming : Bindings) (fuel : Nat) (results : ResultSet)
    (historical : comparison = .records) :
    ¬CallDerivation (comparison := comparison) space live
      (.expression [.symbol "eval", body]) expected incoming fuel results :=
  CallDerivation.not_of_embedded historical rfl

/-- Pointwise child paths are assembled by the existing calls instruction. -/
theorem calls_realizes_map (space : Space) (expected : Atom) (fuel : Nat) (live : List Atom)
    (requests : ResultSet) (outputs : ResultPair → ResultSet)
    (children : ∀ request ∈ requests,
      Realizes space (.call request.1 expected request.2 fuel live) (outputs request)) :
    Realizes space (.calls expected fuel requests live) (requests.flatMap outputs) := by
  have aligned : List.Forall₂ (fun request output =>
      Realizes space (.call request.1 expected request.2 fuel live) output)
      requests (requests.map outputs) :=
    List.forall₂_map_right_iff.mpr (List.forall₂_same.mpr children)
  simpa only [← List.flatMap_def] using calls_realizes space expected fuel live aligned

/-- Recursive equation bodies compose at their actual materialized request
and reached binding state. This law handles every candidate and occurrence. -/
theorem equations_realizes_map (space : Space) (original expected : Atom) (incoming : Bindings)
    (fuel : Nat) (live : List Atom) (candidates : ResultSet)
    (outputs : ResultPair → ResultPair → ResultSet)
    (children : ∀ candidate ∈ candidates, ∀ request ∈ equationInputs incoming fuel candidate,
      Realizes space (.returned original request.1 expected request.2 fuel live) (outputs candidate request)) :
    Realizes space (.returns original expected fuel
      (candidates.flatMap (equationInputs incoming fuel)) live)
      (candidates.flatMap fun candidate =>
        (equationInputs incoming fuel candidate).flatMap (outputs candidate)) := by
  have aligned : List.Forall₂ (fun candidate output =>
      List.Forall₂ (fun request results =>
        Realizes space (.returned original request.1 expected request.2 fuel live) results)
        (equationInputs incoming fuel candidate) output)
      candidates (candidates.map fun candidate =>
        (equationInputs incoming fuel candidate).map (outputs candidate)) := by
    apply List.forall₂_map_right_iff.mpr
    apply List.forall₂_same.mpr
    intro candidate member
    exact List.forall₂_map_right_iff.mpr (List.forall₂_same.mpr (children candidate member))
  simpa only [List.map_map, Function.comp_def, ← List.flatMap_def] using
    equations_realizes space original expected incoming fuel live aligned

namespace Covered

/-- The producer receiver runs the entire ordered physical row list before
entering the ordinary typed return receiver on its exact completed list. -/
theorem producer_results_realizes (space : Space) (original expected : Atom)
    (incoming : Bindings) (fuel : Nat) (live : List Atom) (raw completed results : ResultSet)
    (present : raw ≠ [])
    (production : Realizes space (.productions fuel raw (expected :: live) (some original) .emitted) completed)
    (returned : Realizes space (.returns original expected fuel completed live) results) :
    Realizes space (.producerResults (.ordinary expected) original incoming fuel
      live Atom.notReducible raw) results := by
  intro stack emitted
  let receiver := Frame.invocationReturn (.ordinary expected) original fuel live
  have begin := enter_request space
    (.producerResults (.ordinary expected) original incoming fuel live Atom.notReducible raw) stack emitted
  have resumed := consume_continuation space receiver completed stack emitted
  apply begin.trans
  have nonempty := List.isEmpty_eq_false_iff.mpr present
  simpa only [FirstSuccessRecursiveStrategy.enter, RecursiveMachine.enter, nonempty,
    Bool.false_eq_true, if_false, InvocationMode.pendingScope, List.cons_append, List.nil_append,
    receiver] using (production (receiver :: stack) emitted).trans (resumed.trans (by
      simpa only [RecursiveMachine.resume, List.nil_append, receiver] using returned stack emitted))

/-- Return traversal retains all three occurrence coordinates: candidate,
prepared input and completed producer result. -/
theorem equation_produced_returns_realizes (space : Space) (original expected : Atom)
    (incoming : Bindings) (fuel : Nat) (live : List Atom) (candidates : ResultSet)
    (productions : ResultPair → ResultPair → ResultSet)
    (outputs : ResultPair → ResultPair → ResultPair → ResultSet)
    (children : ∀ candidate ∈ candidates, ∀ request ∈ equationInputs incoming fuel candidate,
      ∀ completed ∈ productions candidate request,
        Realizes space (.returned original completed.1 expected completed.2 fuel live)
          (outputs candidate request completed)) :
    Realizes space (.returns original expected fuel
      (candidates.flatMap fun candidate => (equationInputs incoming fuel candidate).flatMap (productions candidate)) live)
      (candidates.flatMap fun candidate => (equationInputs incoming fuel candidate).flatMap fun request =>
        (productions candidate request).flatMap (outputs candidate request)) := by
  have grouped : List.Forall₂ (List.Forall₂ (List.Forall₂ fun completed output =>
      Realizes space (.returned original completed.1 expected completed.2 fuel live) output))
      (candidates.map fun candidate => (equationInputs incoming fuel candidate).map (productions candidate))
      (candidates.map fun candidate => (equationInputs incoming fuel candidate).map fun request =>
        (productions candidate request).map (outputs candidate request)) := by
    apply List.forall₂_map_right_iff.mpr
    apply List.forall₂_map_left_iff.mpr
    apply List.forall₂_same.mpr
    intro candidate member
    apply List.forall₂_map_right_iff.mpr
    apply List.forall₂_map_left_iff.mpr
    apply List.forall₂_same.mpr
    intro request present
    exact List.forall₂_map_right_iff.mpr
      (List.forall₂_same.mpr (children candidate member request present))
  have joined := returns_realizes space original expected fuel live (List.rel_flatten (List.rel_flatten grouped))
  simpa only [List.flatten_eq_flatMap, List.flatMap_assoc, List.flatMap_map, id_eq] using joined

end Covered

/-- The producer receiver runs the entire ordered physical row list before
entering the ordinary typed return receiver on its exact completed list. -/
theorem producer_results_realizes (space : Space) (original expected : Atom)
    (incoming : Bindings) (fuel : Nat) (live : List Atom) (raw completed results : ResultSet)
    (present : raw ≠ [])
    (production : Realizes space (.productions fuel raw (expected :: live) (some original) .emitted) completed)
    (returned : Realizes space (.returns original expected fuel completed live) results) :
    Realizes space (.producerResults (.ordinary expected) original incoming fuel
      live Atom.notReducible raw) results := by
  intro stack emitted
  let receiver := Frame.invocationReturn (.ordinary expected) original fuel live
  have begin := enter_request space HE.GroundedDispatch.none
    (.producerResults (.ordinary expected) original incoming fuel live Atom.notReducible raw) stack emitted
  have resumed := consume_continuation space HE.GroundedDispatch.none receiver completed stack emitted
  apply begin.trans
  have nonempty := List.isEmpty_eq_false_iff.mpr present
  simpa only [FirstSuccessRecursiveStrategy.enter, RecursiveMachine.enter, nonempty,
    Bool.false_eq_true, if_false, InvocationMode.pendingScope, List.cons_append, List.nil_append,
    receiver] using (production (receiver :: stack) emitted).trans (resumed.trans (by
      simpa only [RecursiveMachine.resume, List.nil_append, receiver] using returned stack emitted))

/-- Return traversal retains all three occurrence coordinates: candidate,
prepared input and completed producer result. -/
theorem equation_produced_returns_realizes (space : Space) (original expected : Atom)
    (incoming : Bindings) (fuel : Nat) (live : List Atom) (candidates : ResultSet)
    (productions : ResultPair → ResultPair → ResultSet)
    (outputs : ResultPair → ResultPair → ResultPair → ResultSet)
    (children : ∀ candidate ∈ candidates, ∀ request ∈ equationInputs incoming fuel candidate,
      ∀ completed ∈ productions candidate request,
        Realizes space (.returned original completed.1 expected completed.2 fuel live)
          (outputs candidate request completed)) :
    Realizes space (.returns original expected fuel
      (candidates.flatMap fun candidate => (equationInputs incoming fuel candidate).flatMap (productions candidate)) live)
      (candidates.flatMap fun candidate => (equationInputs incoming fuel candidate).flatMap fun request =>
        (productions candidate request).flatMap (outputs candidate request)) := by
  have grouped : List.Forall₂ (List.Forall₂ (List.Forall₂ fun completed output =>
      Realizes space (.returned original completed.1 expected completed.2 fuel live) output))
      (candidates.map fun candidate => (equationInputs incoming fuel candidate).map (productions candidate))
      (candidates.map fun candidate => (equationInputs incoming fuel candidate).map fun request =>
        (productions candidate request).map (outputs candidate request)) := by
    apply List.forall₂_map_right_iff.mpr
    apply List.forall₂_map_left_iff.mpr
    apply List.forall₂_same.mpr
    intro candidate member
    apply List.forall₂_map_right_iff.mpr
    apply List.forall₂_map_left_iff.mpr
    apply List.forall₂_same.mpr
    intro request present
    exact List.forall₂_map_right_iff.mpr
      (List.forall₂_same.mpr (children candidate member request present))
  have joined := returns_realizes space original expected fuel live (List.rel_flatten (List.rel_flatten grouped))
  simpa only [List.flatten_eq_flatMap, List.flatMap_assoc, List.flatMap_map, id_eq] using joined



/-- The singleton receiver wraps ordinary values and propagates stopped rows. -/
theorem tuple_singleton_realizes (space : Space) (value : Atom) (incoming : Bindings)
    (fuel : Nat) (live : List Atom) (heads : ResultSet)
    (child : Realizes space (.atom value Atom.undefinedType incoming fuel live) heads) :
    Realizes space (.tuple (.expression [value]) incoming (fuel + 1) live)
      (heads.map HE.tupleSingleton) := by
  refine FramedPath.receive (first := []) (last := []) (receiver := Frame.tupleSingleton) ?_ child ?_
  · intro stack emitted
    exact enter_request space HE.GroundedDispatch.none (.tuple (.expression [value]) incoming (fuel + 1) live) stack emitted
  · intro stack emitted
    exact consume_continuation space HE.GroundedDispatch.none (Frame.tupleSingleton) heads stack emitted

private def tupleBranchPlan (tail : Atom) (fuel : Nat) (live : List Atom) : BranchPlan where
  batch rows := .tupleHeads tail fuel rows live
  stopped row := isEmptyOrError row.1
  child row := .tuple tail row.2 fuel (row.1 :: live)
  receiver row := .tupleTail row.1
  readout row := RecursiveTasks.tupleTail row.1

/-- Each nonstopped physical head enters its own retained tuple tail. -/
theorem tuple_heads_realizes (space : Space) (tail : Atom) (fuel : Nat) (live : List Atom)
    (heads : ResultSet) (tails : ResultPair → ResultSet)
    (children : ∀ head ∈ heads, isEmptyOrError head.1 = false →
      Realizes space (.tuple tail head.2 fuel (head.1 :: live)) (tails head)) :
    Realizes space (.tupleHeads tail fuel heads live) (tupleOutputs heads tails) := by
  let plan := tupleBranchPlan tail fuel live
  have branches := plan.rowResults_map (step := (FirstSuccessRecursiveExecution.machine HE.GroundedDispatch.none).reading.silent)
    (space := space) heads tails children
  change Realizes space (.tupleHeads tail fuel heads live) (tupleOutputs heads tails)
  rw [tupleOutputs, List.flatMap_def]
  refine (appendFrames space).traverseBranches plan ?_ ?_ ?_ ?_ branches
  · intro stack emitted
    exact enter_request space HE.GroundedDispatch.none (Task.tupleHeads tail fuel [] live) stack emitted
  · rintro ⟨value, bindings⟩ rest stopped stack emitted
    simp only [plan, tupleBranchPlan] at stopped
    simpa only [plan, tupleBranchPlan, FirstSuccessRecursiveStrategy.enter, RecursiveMachine.enter,
      stopped, if_true, List.cons_append, List.nil_append] using
      enter_request space HE.GroundedDispatch.none (Task.tupleHeads tail fuel (⟨value, bindings⟩ :: rest) live) stack emitted
  · rintro ⟨value, bindings⟩ rest running stack emitted
    simp only [plan, tupleBranchPlan] at running
    simpa only [plan, tupleBranchPlan, FirstSuccessRecursiveStrategy.enter, RecursiveMachine.enter,
      running, Bool.false_eq_true, if_false, List.cons_append, List.nil_append] using
      enter_request space HE.GroundedDispatch.none (Task.tupleHeads tail fuel (⟨value, bindings⟩ :: rest) live) stack emitted
  · intro row replies stack emitted
    simpa only [plan, tupleBranchPlan, RecursiveMachine.resume, List.cons_append, List.nil_append] using
      consume_continuation space HE.GroundedDispatch.none (Frame.tupleTail row.1) replies stack emitted

/-- Tuple head evaluation carries the whole pending tuple in its live scope. -/
theorem tuple_cons_realizes (space : Space) (head second : Atom) (remaining : List Atom)
    (incoming : Bindings) (fuel : Nat) (live : List Atom)
    (heads : ResultSet) (tails : ResultPair → ResultSet)
    (first : Realizes space (.atom head Atom.undefinedType incoming fuel
      (.expression (second :: remaining) :: live)) heads)
    (children : ∀ selected ∈ heads, isEmptyOrError selected.1 = false →
      Realizes space (.tuple (.expression (second :: remaining)) selected.2 fuel
        (selected.1 :: live)) (tails selected)) :
    Realizes space (.tuple (.expression (head :: second :: remaining)) incoming (fuel + 1) live)
      (tupleOutputs heads tails) := by
  refine FramedPath.trans (third := []) (FramedPath.receive (first := []) (last := []) (receiver := Frame.tupleHeads (.expression (second :: remaining)) fuel live) ?_ first ?_)
    (tuple_heads_realizes space (.expression (second :: remaining)) fuel live heads tails children)
  · intro stack emitted
    exact enter_request space HE.GroundedDispatch.none (.tuple (.expression (head :: second :: remaining)) incoming (fuel + 1) live) stack emitted
  · intro stack emitted
    exact consume_continuation space HE.GroundedDispatch.none (Frame.tupleHeads (.expression (second :: remaining)) fuel live) heads stack emitted

/-- The actual Undefined operator lookup selects tuple interpretation before
the existing ordinary call receiver and success-priority collection. -/
theorem untyped_tuple_realizes (space : Space) (operator : Atom) (arguments : List Atom)
    (expected : Atom) (incoming : Bindings) (fuel : Nat) (live : List Atom)
    (rows results : ResultSet)
    (clean : isEmptyOrError (.expression (operator :: arguments)) = false)
    (notRaw : expected ≠ Atom.atomType) (notExpression : expected ≠ Atom.expressionType)
    (types : getAtomTypes space operator = [Atom.undefinedType])
    (tuple : Realizes space (.tuple (.expression (operator :: arguments)) incoming
      (fuel + 1) (expected :: live)) rows)
    (calls : Realizes space (.calls expected (fuel + 1) rows live) results) :
    Realizes space (.atom (.expression (operator :: arguments)) expected incoming (fuel + 3) live)
      (successPriority results) := by
  change expected ≠ .symbol "Atom" at notRaw
  change expected ≠ .symbol "Expression" at notExpression
  intro stack emitted
  let value := Atom.expression (operator :: arguments)
  let saved := Frame.prepend [] :: .filter :: stack
  have first := enter_request space HE.GroundedDispatch.none
    (.atom value expected incoming (fuel + 3) live) stack emitted
  have expression := enter_request space HE.GroundedDispatch.none
    (.expression value expected incoming (fuel + 2) live) (.filter :: stack) emitted
  have selected := enter_request space HE.GroundedDispatch.none
    (.functions value expected incoming (fuel + 1) [Atom.undefinedType] live)
    (.filter :: stack) emitted
  have entered := enter_request space HE.GroundedDispatch.none
    (.tupleCalls value expected incoming (fuel + 1) live) saved emitted
  have resumed := consume_continuation space HE.GroundedDispatch.none
    (.calls expected (fuel + 1) live) rows saved emitted
  have prepended := consume_continuation space HE.GroundedDispatch.none (.prepend []) results (.filter :: stack) emitted
  have filtered := consume_continuation space HE.GroundedDispatch.none .filter results stack emitted
  have finish := prepended.trans (by
    simpa only [RecursiveMachine.resume, List.nil_append] using filtered)
  have callRun := calls saved emitted
  have tupleRun := tuple (.calls expected (fuel + 1) live :: saved) emitted
  have completed := tupleRun.trans (resumed.trans (by
    simpa only [RecursiveMachine.resume, List.nil_append] using callRun.trans finish))
  have tupleEntered := entered.trans (by
    simpa only [FirstSuccessRecursiveStrategy.enter, RecursiveMachine.enter,
      List.cons_append, List.nil_append, value] using completed)
  have selection := selected.trans (by
    simpa only [FirstSuccessRecursiveStrategy.enter, FirstSuccessRecursiveStrategy.select,
      FirstSuccessRecursiveStrategy.readPolicy, FirstSuccessRecursiveStrategy.noteNonFunction,
      Atom.undefinedType, if_true, List.map_nil, List.cons_append, List.nil_append, saved] using tupleEntered)
  have interpreted := expression.trans (by
    simpa only [FirstSuccessRecursiveStrategy.enter, rawTypeLookup, types, value,
      List.nil_append] using selection)
  exact first.trans (by
    simpa [FirstSuccessRecursiveStrategy.enter, RecursiveMachine.enter, value, clean,
      getMetaType, notRaw, notExpression, Atom.unit, Nat.add_assoc] using interpreted)

/-- Error-shaped tuple results use the existing ordinary invocation guard. -/
theorem error_call_realizes (space : Space) (value expected : Atom) (incoming : Bindings)
    (fuel : Nat) (live : List Atom) (error : IsErrorRel value) :
    Realizes space (.call value expected incoming (fuel + 1) live) [(value, incoming)] := by
  have nativeError := (Conformance.isErrorRel_iff_isErrorAtom value).mp error
  intro stack emitted
  have first := enter_request space HE.GroundedDispatch.none (.call value expected incoming (fuel + 1) live)
    stack emitted
  have invoked := enter_request space HE.GroundedDispatch.none
    (.invocation (.ordinary expected) value incoming (fuel + 1) live none) stack emitted
  exact first.trans (by
    simpa only [FirstSuccessRecursiveStrategy.enter, RecursiveMachine.enter,
      InvocationMode.errorPassthrough, nativeError, if_true, List.nil_append] using invoked)

namespace Covered


/-- The singleton receiver wraps ordinary values and propagates stopped rows. -/
theorem tuple_singleton_realizes (space : Space) (value : Atom) (incoming : Bindings)
    (fuel : Nat) (live : List Atom) (heads : ResultSet)
    (child : Realizes space (.atom value Atom.undefinedType incoming fuel live) heads) :
    Realizes space (.tuple (.expression [value]) incoming (fuel + 1) live)
      (heads.map HE.tupleSingleton) := by
  refine FramedPath.receive (first := []) (last := []) (receiver := Frame.tupleSingleton) ?_ child ?_
  · intro stack emitted
    exact enter_request space (.tuple (.expression [value]) incoming (fuel + 1) live) stack emitted
  · intro stack emitted
    exact consume_continuation space (Frame.tupleSingleton) heads stack emitted

/-- Each nonstopped physical head enters its own retained tuple tail. -/
theorem tuple_heads_realizes (space : Space) (tail : Atom) (fuel : Nat) (live : List Atom)
    (heads : ResultSet) (tails : ResultPair → ResultSet)
    (children : ∀ head ∈ heads, isEmptyOrError head.1 = false →
      Realizes space (.tuple tail head.2 fuel (head.1 :: live)) (tails head)) :
    Realizes space (.tupleHeads tail fuel heads live) (tupleOutputs heads tails) := by
  let plan := tupleBranchPlan tail fuel live
  have branches := plan.rowResults_map (step := (Checked.machine HE.GroundedDispatch.none).reading.silent)
    (space := space) heads tails children
  change Realizes space (.tupleHeads tail fuel heads live) (tupleOutputs heads tails)
  rw [tupleOutputs, List.flatMap_def]
  refine (appendFrames space).traverseBranches plan ?_ ?_ ?_ ?_ branches
  · intro stack emitted
    exact enter_request space (Task.tupleHeads tail fuel [] live) stack emitted
  · rintro ⟨value, bindings⟩ rest stopped stack emitted
    simp only [plan, tupleBranchPlan] at stopped
    simpa only [plan, tupleBranchPlan, FirstSuccessRecursiveStrategy.enter, RecursiveMachine.enter,
      stopped, if_true, List.cons_append, List.nil_append] using
      enter_request space (Task.tupleHeads tail fuel (⟨value, bindings⟩ :: rest) live) stack emitted
  · rintro ⟨value, bindings⟩ rest running stack emitted
    simp only [plan, tupleBranchPlan] at running
    simpa only [plan, tupleBranchPlan, FirstSuccessRecursiveStrategy.enter, RecursiveMachine.enter,
      running, Bool.false_eq_true, if_false, List.cons_append, List.nil_append] using
      enter_request space (Task.tupleHeads tail fuel (⟨value, bindings⟩ :: rest) live) stack emitted
  · intro row replies stack emitted
    simpa only [plan, tupleBranchPlan, RecursiveMachine.resume, List.cons_append, List.nil_append] using
      consume_continuation space (Frame.tupleTail row.1) replies stack emitted

/-- Tuple head evaluation carries the whole pending tuple in its live scope. -/
theorem tuple_cons_realizes (space : Space) (head second : Atom) (remaining : List Atom)
    (incoming : Bindings) (fuel : Nat) (live : List Atom)
    (heads : ResultSet) (tails : ResultPair → ResultSet)
    (first : Realizes space (.atom head Atom.undefinedType incoming fuel
      (.expression (second :: remaining) :: live)) heads)
    (children : ∀ selected ∈ heads, isEmptyOrError selected.1 = false →
      Realizes space (.tuple (.expression (second :: remaining)) selected.2 fuel
        (selected.1 :: live)) (tails selected)) :
    Realizes space (.tuple (.expression (head :: second :: remaining)) incoming (fuel + 1) live)
      (tupleOutputs heads tails) := by
  refine FramedPath.trans (third := []) (FramedPath.receive (first := []) (last := []) (receiver := Frame.tupleHeads (.expression (second :: remaining)) fuel live) ?_ first ?_)
    (tuple_heads_realizes space (.expression (second :: remaining)) fuel live heads tails children)
  · intro stack emitted
    exact enter_request space (.tuple (.expression (head :: second :: remaining)) incoming (fuel + 1) live) stack emitted
  · intro stack emitted
    exact consume_continuation space (Frame.tupleHeads (.expression (second :: remaining)) fuel live) heads stack emitted

/-- The actual Undefined operator lookup selects tuple interpretation before
the existing ordinary call receiver and success-priority collection. -/
theorem untyped_tuple_realizes (space : Space) (operator : Atom) (arguments : List Atom)
    (expected : Atom) (incoming : Bindings) (fuel : Nat) (live : List Atom)
    (rows results : ResultSet)
    (clean : isEmptyOrError (.expression (operator :: arguments)) = false)
    (notRaw : expected ≠ Atom.atomType) (notExpression : expected ≠ Atom.expressionType)
    (types : getAtomTypes space operator = [Atom.undefinedType])
    (tuple : Realizes space (.tuple (.expression (operator :: arguments)) incoming
      (fuel + 1) (expected :: live)) rows)
    (calls : Realizes space (.calls expected (fuel + 1) rows live) results) :
    Realizes space (.atom (.expression (operator :: arguments)) expected incoming (fuel + 3) live)
      (successPriority results) := by
  change expected ≠ .symbol "Atom" at notRaw
  change expected ≠ .symbol "Expression" at notExpression
  intro stack emitted
  let value := Atom.expression (operator :: arguments)
  let saved := Frame.prepend [] :: .filter :: stack
  have first := enter_request space
    (.atom value expected incoming (fuel + 3) live) stack emitted (by
      simp [FirstSuccessRecursiveStrategy.taskReady, RecursiveMachine.Checked.taskReady,
        value, getMetaType, Atom.unit])
  have expression := enter_request space
    (.expression value expected incoming (fuel + 2) live) (.filter :: stack) emitted
  have selected := enter_request space
    (.functions value expected incoming (fuel + 1) [Atom.undefinedType] live)
    (.filter :: stack) emitted (by
      simp [FirstSuccessRecursiveStrategy.taskReady,
        FirstSuccessRecursiveStrategy.selectionReady, FirstSuccessRecursiveStrategy.readPolicy,
        Atom.undefinedType])
  have entered := enter_request space
    (.tupleCalls value expected incoming (fuel + 1) live) saved emitted
  have resumed := consume_continuation space
    (.calls expected (fuel + 1) live) rows saved emitted
  have prepended := consume_continuation space (.prepend []) results (.filter :: stack) emitted
  have filtered := consume_continuation space .filter results stack emitted
  have finish := prepended.trans (by
    simpa only [RecursiveMachine.resume, List.nil_append] using filtered)
  have callRun := calls saved emitted
  have tupleRun := tuple (.calls expected (fuel + 1) live :: saved) emitted
  have completed := tupleRun.trans (resumed.trans (by
    simpa only [RecursiveMachine.resume, List.nil_append] using callRun.trans finish))
  have tupleEntered := entered.trans (by
    simpa only [FirstSuccessRecursiveStrategy.enter, RecursiveMachine.enter,
      List.cons_append, List.nil_append, value] using completed)
  have selection := selected.trans (by
    simpa only [FirstSuccessRecursiveStrategy.enter, FirstSuccessRecursiveStrategy.select,
      FirstSuccessRecursiveStrategy.readPolicy, FirstSuccessRecursiveStrategy.noteNonFunction,
      Atom.undefinedType, if_true, List.map_nil, List.cons_append, List.nil_append, saved] using tupleEntered)
  have interpreted := expression.trans (by
    simpa only [FirstSuccessRecursiveStrategy.enter, rawTypeLookup, types, value,
      List.nil_append] using selection)
  exact first.trans (by
    simpa [FirstSuccessRecursiveStrategy.enter, RecursiveMachine.enter, value, clean,
      getMetaType, notRaw, notExpression, Atom.unit, Nat.add_assoc] using interpreted)

/-- Error-shaped tuple results use the existing ordinary invocation guard. -/
theorem error_call_realizes (space : Space) (value expected : Atom) (incoming : Bindings)
    (fuel : Nat) (live : List Atom) (error : IsErrorRel value) :
    Realizes space (.call value expected incoming (fuel + 1) live) [(value, incoming)] := by
  have nativeError := (Conformance.isErrorRel_iff_isErrorAtom value).mp error
  intro stack emitted
  have first := enter_request space (.call value expected incoming (fuel + 1) live)
    stack emitted
  have invoked := enter_request space
    (.invocation (.ordinary expected) value incoming (fuel + 1) live none) stack emitted (by
      simp [FirstSuccessRecursiveStrategy.taskReady, RecursiveMachine.Checked.taskReady,
        InvocationMode.errorPassthrough, nativeError])
  exact first.trans (by
    simpa only [FirstSuccessRecursiveStrategy.enter, RecursiveMachine.enter,
      InvocationMode.errorPassthrough, nativeError, if_true, List.nil_append] using invoked)

end Covered

mutual
/-- A recursive source derivation constructs the actual first-success worker
path, under every saved caller and already published occurrence list. -/
theorem AtomDerivation.realizes {space : Space} {comparison : SourceBindingComparison} {live : List Atom} {value expected : Atom}
    {incoming : Bindings} {fuel : Nat} {results : ResultSet}
    (derivation : AtomDerivation (comparison := comparison) space live value expected incoming fuel results) :
    Realizes space (.atom value expected incoming fuel live) results := by
  cases derivation with
  | leaf live value expected incoming fuel leaf =>
      exact retained_leaf space HE.GroundedDispatch.none value expected incoming fuel leaf live
  | symbolCast live name expected incoming fuel before after actual notEmpty _ _ types
      expectedClosed actualClosed earlierClosed earlierRejects fits enough =>
      exact symbol_cast_realizes space name expected incoming fuel before after actual notEmpty types
        expectedClosed actualClosed earlierClosed earlierRejects fits enough live
  | symbolRejected live name expected incoming fuel notEmpty notRaw notMeta expectedClosed closed rejected =>
      exact symbol_rejection_realizes space name expected incoming fuel live
        notEmpty notRaw notMeta expectedClosed closed rejected
  | application live name arguments expected incoming fuel typing rows outputs args calls =>
      apply application_retained_realizes typing incoming rows _ live
      · exact args.realizes
      · apply calls_realizes_map
        intro request member
        exact (calls request member).realizes
  | untypedTuple live operator arguments expected incoming fuel rows outputs clean notRaw notExpr
      types tuple calls =>
      apply untyped_tuple_realizes space operator arguments expected incoming fuel live rows _
        clean notRaw notExpr types tuple.realizes
      exact calls_realizes_map space expected (fuel + 1) live rows outputs
        (fun request member => (calls request member).realizes)
termination_by 2 * fuel

/-- Tuple paths preserve stopped heads and the actual selected tail bindings. -/
theorem TupleDerivation.realizes {space : Space} {comparison : SourceBindingComparison}
    {live : List Atom} {value : Atom} {incoming : Bindings} {fuel : Nat} {results : ResultSet}
    (derivation : TupleDerivation space comparison live value incoming fuel results) :
    Realizes space (.tuple value incoming fuel live) results := by
  cases derivation with
  | nil live incoming fuel =>
      intro stack emitted
      simpa only [FirstSuccessRecursiveStrategy.enter, RecursiveMachine.enter, Atom.unit,
        List.nil_append] using enter_request space HE.GroundedDispatch.none
          (.tuple Atom.unit incoming (fuel + 1) live) stack emitted
  | singleton live value incoming fuel heads child =>
      exact tuple_singleton_realizes space value incoming fuel live heads child.realizes
  | cons live head second remaining incoming fuel heads tails first children =>
      exact tuple_cons_realizes space head second remaining incoming fuel live heads tails
        first.realizes (fun selected member clean => (children selected member clean).realizes)
termination_by 2 * fuel

/-- Each argument branch continues with its own bindings and the exact live
syntax of the pending tail. -/
theorem ArgsDerivation.realizes {space : Space} {comparison : SourceBindingComparison} {live : List Atom} {values types : List Atom}
    {incoming : Bindings} {fuel : Nat} {results : ArgumentResults}
    (derivation : ArgsDerivation (comparison := comparison) space live values types incoming fuel results) :
    Realizes space (.args values types incoming fuel live) (argumentReplies results) := by
  cases derivation with
  | nil live incoming fuel =>
      intro stack emitted
      simpa [FirstSuccessRecursiveStrategy.enter, RecursiveMachine.enter, argumentReplies] using
        enter_request space HE.GroundedDispatch.none (.args [] [] incoming (fuel + 1) live) stack emitted
  | cons live value expected values types incoming fuel heads tails head safe tail =>
      have branches : List.Forall₂ (fun selected output => ∃ rests,
          Realizes space (.args values types selected.2 fuel (selected.1 :: live)) rests ∧
            output = RecursiveTasks.argumentTail selected.1 rests)
          heads (heads.map fun selected =>
            RecursiveTasks.argumentTail selected.1 (argumentReplies (tails selected))) := by
        apply List.forall₂_map_right_iff.mpr
        apply List.forall₂_same.mpr
        intro selected member
        exact ⟨argumentReplies (tails selected), (tail selected member).realizes, rfl⟩
      have path := arguments_cons_with_branches_realizes space value expected values types incoming
        fuel live head.realizes safe branches
      simpa [argumentReplies, RecursiveTasks.argumentTail, List.map_map, List.map_flatMap,
        Function.comp_def, argumentValues_packet, argumentsSucceeded_packet,
        ← List.flatMap_def] using path
termination_by 2 * fuel

/-- Source equations enter the existing query/body continuation; recursively
changing bindings remain part of every returned occurrence. -/
theorem CallDerivation.realizes {space : Space} {comparison : SourceBindingComparison} {live : List Atom} {query expected : Atom}
    {incoming : Bindings} {fuel : Nat} {results : ResultSet}
    (derivation : CallDerivation (comparison := comparison) space live query expected incoming fuel results) :
    Realizes space (.call query expected incoming fuel live) results := by
  cases derivation with
  | errorPassthrough live value expected incoming fuel error =>
      exact error_call_realizes space _ expected incoming fuel live error
  | unreduced live name arguments expected incoming fuel _ nonembedded clean empty _ =>
      exact call_empty_realizes space name arguments expected incoming fuel live nonembedded clean empty
  | equations live name arguments expected incoming fuel productions outputs _ nonembedded clean selected evidence producers bodies =>
      apply call_query_realizes space name arguments expected incoming fuel live nonembedded clean
      apply producer_results_realizes space _ _ incoming fuel live _ _ _ selected
      · exact Covered.unchecked (Covered.equation_productions_realizes space incoming fuel
          (expected :: live) (some (.expression (.symbol name :: arguments))) _ productions
          (fun candidate member request present =>
            (producers candidate member request present).covered_realizes))
      · apply equation_produced_returns_realizes
        intro candidate member request present produced selected
        exact (bodies candidate member request present produced selected).realizes

  | embedded live name arguments expected incoming fuel raw outputs semantic clean instruction child returns =>
      cases semantic
      apply ordinary_embedded_realizes space name arguments expected incoming fuel live raw _ clean instruction
        (Covered.unchecked child.covered_realizes)
      have paths : List.Forall₂ (fun request output =>
          Realizes space (.returned (.expression (.symbol name :: arguments)) request.1 expected
            request.2 fuel live) output) raw (raw.map outputs) :=
        List.forall₂_map_right_iff.mpr (List.forall₂_same.mpr (fun result member =>
          (returns result member).realizes))
      simpa only [← List.flatMap_def] using returns_realizes space
        (.expression (.symbol name :: arguments)) expected fuel live paths

termination_by 2 * fuel

theorem ReturnDerivation.realizes {space : Space} {comparison : SourceBindingComparison} {live : List Atom}
    {original expected value : Atom} {bindings : Bindings} {fuel : Nat} {results : ResultSet}
    (derivation : ReturnDerivation (comparison := comparison) space live original expected value bindings fuel results) :
    Realizes space (.returned original value expected bindings fuel live) results := by
  cases derivation with
  | notReducible live original expected bindings fuel =>
      exact returned_notReducible_realizes space original expected bindings fuel live
  | stopped live original expected value bindings fuel stopped =>
      exact returned_stopped_realizes space original value expected bindings fuel live
        ((Conformance.isEmptyOrErrorRel_iff_isEmptyOrError value).mp stopped)
  | evaluate live original expected value bindings fuel results accepted running child =>
      exact returned_evaluate_realizes space original value expected bindings fuel live results accepted
        (by simpa [Conformance.isEmptyOrErrorRel_iff_isEmptyOrError] using running) child.realizes
termination_by 2 * fuel + 1

end

/-- Success priority removes occurrences; it does not invent an occurrence. -/
theorem mem_of_mem_successPriority {result : ResultPair} {results : ResultSet}
    (member : result ∈ successPriority results) : result ∈ results := by
  simp only [successPriority] at member
  split at member <;> exact (List.mem_filter.mp member).1

/-- The actual worker's completed filter implements the independent phase
judgment, including repeated all-error occurrences. -/
theorem successPriority_source (results : ResultSet) :
    Mettapedia.Machines.OrderedProtocol.Completion.SuccessPriorityRel
      (fun row : ResultPair => isErrorAtom row.1) results (successPriority results) := by
  classical
  by_cases succeeds : ∃ row ∈ results, isErrorAtom row.1 = false
  · have nonempty : (results.filter fun row => !isErrorAtom row.1) ≠ [] := by
      obtain ⟨row, member, clean⟩ := succeeds
      intro empty
      have present : row ∈ results.filter (fun row => !isErrorAtom row.1) :=
        List.mem_filter.mpr ⟨member, by simp [clean]⟩
      rw [empty] at present
      exact List.not_mem_nil present
    have selected : successPriority results = results.filter (fun row => !isErrorAtom row.1) := by
      simp [successPriority, List.isEmpty_eq_false_iff.mpr nonempty]
    rw [selected]
    exact .successes succeeds
  · have failed : ∀ row ∈ results, isErrorAtom row.1 = true := by
      intro row member
      cases classified : isErrorAtom row.1 with
      | true => rfl
      | false => exact False.elim (succeeds ⟨row, member, classified⟩)
    have empty : (results.filter fun row => !isErrorAtom row.1) = [] := by
      apply List.filter_eq_nil_iff.mpr
      intro row member
      simp [failed row member]
    have kept : (results.filter fun row => isErrorAtom row.1) = results :=
      List.filter_eq_self.mpr failed
    simp only [successPriority, empty, List.isEmpty_nil, Bool.not_true, Bool.false_eq_true,
      ↓reduceIte, kept]
    exact .allErrors failed

/-- The publication judgment determines the worker's complete occurrence
list, not just its support. -/
theorem successPriority_source_iff (raw published : ResultSet) :
    Mettapedia.Machines.OrderedProtocol.Completion.SuccessPriorityRel
      (fun row : ResultPair => isErrorAtom row.1) raw published ↔
      successPriority raw = published := by
  constructor
  · intro completed
    exact (successPriority_source raw).functional completed
  · rintro rfl
    exact successPriority_source raw

/-- A completed source phase consumes the actual retained filter frame.
The reached space, caller stack and earlier publications are preserved. -/
theorem completed_priority_retained_filter (space : Space) (raw published : ResultSet)
    (stack : List Frame) (emitted : ResultSet)
    (completed : Mettapedia.Machines.OrderedProtocol.Completion.SuccessPriorityRel
      (fun row : ResultPair => isErrorAtom row.1) raw published) :
    Covered.SilentPath ⟨space,.returning raw,.filter::stack,emitted⟩
      ⟨space,.returning published,stack,emitted⟩ := by
  have selected := (successPriority_source_iff raw published).mp completed
  simpa only [RecursiveMachine.resume, List.nil_append, selected] using
    Covered.consume_continuation space .filter raw stack emitted

section ScopedPolymorphicInvocation

open Spec.Type.Presentation.Exact
open Spec.Type.Presentation.BindingTheory Spec.Type.Presentation.Theory
open Spec.Type.RuntimeRefinement
open Spec.Match.Merge

open private atomVariables_eq_typeVars atomListVariables_eq_typeVarsList
  from Mettapedia.Languages.MeTTa.HE.EquationFreshening

/-- A fresh type alias extends the checkpoint's single certified table. The
same extension reads every pending operand; the left type is already fixed
by the reached constraints. -/
theorem scoped_type_alias_certificate {bindings : Bindings} {table : TypeSubst}
    (certificate : ReadoutCertificate bindings table) (left right actual : String)
    (fresh : right ∉ specBindingVars bindings)
    (forced : ∀ valuation, TypeBindingSatisfied valuation bindings →
      valuation left = .symbol actual) :
    ReadoutCertificate (bindings.addEquality left right)
      (table.bind right (.symbol actual)) := by
  apply ReadoutCertificate.of_normal_theory
  · exact certificate.normal.bind (by simp [TypeSubst.apply, TypeSubst.typeVars])
  · intro valuation
    rw [TypeSubstSatisfied.bind_iff (certificate.lookup_none_of_outside fresh),
      certificate.theory]
    simp only [applyTypeValuation]
    constructor
    · rintro ⟨model, assigned⟩
      refine ⟨model.1, ?_⟩
      intro first second stored
      rcases List.mem_append.mp stored with old | added
      · exact model.2 first second old
      · cases List.mem_singleton.mp added
        exact (forced valuation model).trans assigned.symm
    · intro model
      have old : TypeBindingSatisfied valuation bindings :=
        ⟨model.1, fun first second stored =>
          model.2 first second (List.mem_append_left _ stored)⟩
      refine ⟨old, ?_⟩
      exact (model.2 left right (by simp [Bindings.addEquality])).symm.trans
        (forced valuation old)

private theorem equality_only_classValues (edges : List (String × String)) (name : String) :
    (⟨[], edges⟩ : Bindings).classValues name = [] := by
  simp [Bindings.classValues, Bindings.lookup]

/-- Repeated positions of one whole arrow produce two physical equality
occurrences in the executable matcher, even though their constraint is shared. -/
theorem repeated_arrow_match (left right : String) (depth : Nat) :
    matchAtoms (.expression [.symbol "->", .var left, .var left])
      (.expression [.symbol "->", .var right, .var right]) (depth + 7) =
      [((Bindings.empty.addEquality left right).addEquality left right)] := by
  have noLoop (edges : List (String × String)) :
      (⟨[], edges⟩ : Bindings).hasLoop = false :=
    Bindings.hasLoop_false_of_assignments_nil _ rfl
  simp [matchAtoms, matchAtomsList, mergeBindings, addVarEquality, getMetaType,
    Bindings.empty, Bindings.addEquality, equality_only_classValues, noLoop,
    Bindings.valuesConsistent]

private theorem source_single_equality_merge (bindings : Bindings) (left right : String)
    {values : List Atom} (selected : (bindings.addEquality left right).classValues left = values)
    (agree : ValuesAgree values) :
    MergeRel equalityGroundedSemantic bindings (Bindings.empty.addEquality left right)
      (bindings.addEquality left right) := by
  refine .mk (order := [.equality left right]) ?_ (.equality (.consistent selected agree) .nil)
  exact List.Perm.refl _

/-- The independent structural matcher also records both variable positions.
Its enclosing merge folds the unique constraint only once. -/
theorem independent_repeated_arrow_match (left right : String) :
    MatchRel equalityGroundedSemantic
      (.expression [.symbol "->", .var left, .var left])
      (.expression [.symbol "->", .var right, .var right])
      ((Bindings.empty.addEquality left right).addEquality left right) := by
  apply MatchRel.expression
  · apply MatchListAccRel.cons (.symSym "->" semanticLoopFree_empty)
      (MergeRel.mk (List.Perm.refl []) .nil)
    apply MatchListAccRel.cons (.varVar left right (semanticLoopFree_of_assignments_nil rfl))
      (source_single_equality_merge Bindings.empty left right
        (equality_only_classValues _ _) trivial)
    exact MatchListAccRel.cons
      (.varVar left right (semanticLoopFree_of_assignments_nil rfl))
      (source_single_equality_merge (Bindings.empty.addEquality left right) left right
        (equality_only_classValues _ _) trivial) .nil
  · exact semanticLoopFree_of_assignments_nil rfl

/-- The head cast genuinely changes the applicability binding: its fresh
second signature is linked to the already valued first signature. -/
theorem independent_fresh_arrow_type_match (bindings : Bindings) (left right : String)
    (value : Atom) (leftFresh : left ∉ bindings.names)
    (rightFresh : right ∉ bindings.names) (different : left ≠ right) :
    TypeMatchRel (.expression [.symbol "->", .var left, .var left])
      (.expression [.symbol "->", .var right, .var right]) (bindings.assign left value)
      ((bindings.assign left value).addEquality left right) := by
  apply TypeMatchRel.structural (by intro same; cases same) (by intro same; cases same)
    (by intro same; cases same) (by intro same; cases same)
    (independent_repeated_arrow_match left right)
  refine .mk (order := [.equality left right]) ?_
    (.equality (.consistent
      (fresh_instance_alias_values bindings left right value leftFresh rightFresh different)
      (by simp [ValuesAgree])) .nil)
  simp [constraints, Bindings.empty, Bindings.addEquality, List.eraseDups_cons]

/-- Native merging preserves both physical repeated-arrow edges. This exact
record is intentionally distinct from the source's unique-constraint fold. -/
theorem fresh_arrow_type_match (bindings : Bindings) (left right : String)
    (value : Atom) (depth : Nat) (leftFresh : left ∉ bindings.names)
    (rightFresh : right ∉ bindings.names) (different : left ≠ right) :
    matchTypes (.expression [.symbol "->", .var left, .var left])
      (.expression [.symbol "->", .var right, .var right])
      (bindings.assign left value) (depth + 7) =
      [(((bindings.assign left value).addEquality left right).addEquality left right)] := by
  have first := fresh_instance_alias_values bindings left right value leftFresh rightFresh different
  have second : (((bindings.assign left value).addEquality left right).addEquality left right).classValues
      left = [value] := by
    rw [EqualityClosure.classValues_addEquality_of_mem (by simp [Bindings.addEquality])]
    exact first
  have firstAdded : addVarEquality (bindings.assign left value) left right (depth + 6) =
      [(bindings.assign left value).addEquality left right] := by
    rw [show depth + 6 = (depth + 5) + 1 by omega, addVarEquality]
    simp only [first, Bindings.valuesConsistent, List.all_nil, ↓reduceIte]
  have secondAdded : addVarEquality ((bindings.assign left value).addEquality left right)
      left right (depth + 6) =
      [((bindings.assign left value).addEquality left right).addEquality left right] := by
    rw [show depth + 6 = (depth + 5) + 1 by omega, addVarEquality]
    simp only [second, Bindings.valuesConsistent, List.all_nil, ↓reduceIte]
  change (matchAtoms (.expression [.symbol "->", .var left, .var left])
    (.expression [.symbol "->", .var right, .var right]) (depth + 7)).flatMap
      (fun matched => mergeBindings (bindings.assign left value) matched (depth + 7)) = _
  rw [repeated_arrow_match]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
  change mergeBindings (bindings.assign left value) ⟨[], [(left, right), (left, right)]⟩
    (depth + 7) = _
  rw [show depth + 7 = (depth + 6) + 1 by omega, mergeBindings]
  simp only [List.foldl_cons, List.foldl_nil, List.flatMap_cons, List.flatMap_nil,
    List.append_nil, firstAdded, secondAdded]

/-- The distinct row multiplicities retain exactly the same complete models
and name support. This does not identify their physical records. -/
theorem repeated_type_edge_agreement (bindings : Bindings) (left right : String) :
    BindingSourceAgreement ((bindings.addEquality left right).addEquality left right)
      (bindings.addEquality left right) := by
  constructor
  · intro valuation
    constructor
    · intro model
      refine ⟨model.1, ?_⟩
      intro first second stored
      exact model.2 first second (List.mem_append_left _ stored)
    · intro model
      refine ⟨model.1, ?_⟩
      intro first second stored
      rcases List.mem_append.mp stored with old | added
      · exact model.2 first second old
      · exact model.2 first second (List.mem_append_right _ added)
  · intro name
    simp only [specBindingVars, Bindings.addEquality, List.flatMap_append,
      List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_append,
      List.mem_cons, List.not_mem_nil, or_false]
    tauto

/-- The source cast and its renewed table are constructed from the selected
type occurrence and the reached certificate. No evaluator result is assumed. -/
theorem scoped_fresh_arrow_cast (space : Space) (scope : List String) (operator : Atom)
    (bindings : Bindings) (left right actual : String) (table : TypeSubst)
    (certificate : ReadoutCertificate (bindings.assign left (.symbol actual)) table)
    (leftFresh : left ∉ bindings.names) (rightFresh : right ∉ bindings.names)
    (different : left ≠ right)
    (freshReached : right ∉ specBindingVars (bindings.assign left (.symbol actual)))
    (lookup : scopedTypeLookup scope space (bindings.assign left (.symbol actual)) operator
      (.expression [.symbol "->", .var left, .var left])
      [.expression [.symbol "->", .var right, .var right]]) :
    ∃ nextCertificate : ReadoutCertificate
        ((bindings.assign left (.symbol actual)).addEquality left right)
        (table.bind right (.symbol actual)),
      scopedStorageTypeService.typeCast scope space operator
        (.expression [.symbol "->", .var left, .var left])
        (bindings.assign left (.symbol actual))
        (operator, (bindings.assign left (.symbol actual)).addEquality left right) ∧
      BindingFrame.Update .renew
        (.selected (bindings.assign left (.symbol actual)) table certificate)
        (.selected ((bindings.assign left (.symbol actual)).addEquality left right)
          (table.bind right (.symbol actual)) nextCertificate) ∧
      ∀ pending : List Atom, (pending.map table.apply).map
        (table.bind right (.symbol actual)).apply =
          pending.map (table.bind right (.symbol actual)).apply := by
  have unbound : bindings.lookup left = none := by
    apply List.lookup_eq_none_iff.mpr
    intro entry stored
    apply bne_iff_ne.mpr
    intro same
    apply leftFresh
    apply List.mem_append_left
    exact List.mem_flatMap.mpr ⟨entry, stored, by simp [same]⟩
  have bound : (left, Atom.symbol actual) ∈ (bindings.assign left (.symbol actual)).assignments := by
    simp [Bindings.assign, isBound_false_of_lookup_none unbound]
  have forced (valuation : String → Atom)
      (model : TypeBindingSatisfied valuation (bindings.assign left (.symbol actual))) :
      valuation left = .symbol actual := by
    simpa only [applyTypeValuation] using model.1 left (.symbol actual) bound
  let nextCertificate := scoped_type_alias_certificate certificate left right actual freshReached forced
  refine ⟨nextCertificate, ?_, .selected certificate nextCertificate, ?_⟩
  · exact TypeCastRel.success (earlierTypes := []) (laterTypes := []) lookup rfl
      (by simp) (independent_fresh_arrow_type_match bindings left right (.symbol actual)
        leftFresh rightFresh different)
  · intro pending
    apply certificate.pending_absorbed nextCertificate _ pending
    intro valuation model
    refine ⟨model.1, ?_⟩
    intro first second stored
    exact model.2 first second (List.mem_append_left _ stored)

open private reachable_ne_endpoints_mem_edgeNodes
  from Mettapedia.Languages.MeTTa.HE.EqualityClosure

private theorem scoped_type_class_fresh {bindings : Bindings} {name : String}
    (fresh : name ∉ bindings.eqVarsInOrder) : bindings.eqClassOrdered name = [name] := by
  have empty : bindings.eqVarsInOrder.filter
      (fun other => (bindings.eqClass name).contains other) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro other stored connected
    by_cases same : name = other
    · exact fresh (same.symm ▸ stored)
    · exact fresh (EqualityClosure.mem_eqVarsInOrder_iff.mpr
        (reachable_ne_endpoints_mem_edgeNodes same
          (EqualityClosure.mem_eqClass_iff_reachable.mp
            (List.contains_iff_mem.mp connected))).1)
  simp only [Bindings.eqClassOrdered, empty]

private theorem scoped_type_class_avoids {bindings : Bindings} {root name : String}
    (fresh : name ∉ bindings.eqVarsInOrder) (different : root ≠ name) :
    name ∉ bindings.eqClassOrdered root := by
  intro member
  exact fresh (EqualityClosure.mem_eqVarsInOrder_iff.mpr
    (reachable_ne_endpoints_mem_edgeNodes different
      (EqualityClosure.mem_eqClass_iff_reachable.mp
        (EqualityClosure.mem_eqClassOrdered_iff.mp member))).2)

private theorem scoped_type_fresh_edges {bindings : Bindings} {name : String}
    (fresh : name ∉ specBindingVars bindings) : name ∉ bindings.eqVarsInOrder := by
  intro member
  apply fresh
  exact List.mem_append_right _ (EqualityClosure.mem_eqVarsInOrder_iff.mp member)

private theorem scoped_type_lookup_avoids {bindings : Bindings} {name key : String}
    {value : Atom} (fresh : name ∉ specBindingVars bindings)
    (found : bindings.lookup key = some value) : name ∉ TypeSubst.typeVars value := by
  obtain ⟨before, after, entries, _⟩ := List.lookup_eq_some_iff.mp found
  intro occurs
  apply fresh
  apply List.mem_append_left
  apply List.mem_flatMap.mpr
  exact ⟨(key, value), by simp [entries], by simp [occurs]⟩

private theorem scoped_type_alias_guard {bindings : Bindings} {left right actual : String}
    (leftFresh : left ∉ bindings.eqVarsInOrder)
    (rightFresh : right ∉ bindings.eqVarsInOrder) (different : left ≠ right)
    (assigned : bindings.lookup left = some (.symbol actual)) :
    ∀ fuel atom, right ∉ TypeSubst.typeVars atom →
      (bindings.addEquality left right).hasResolvableVarAux fuel atom =
        bindings.hasResolvableVarAux fuel atom := by
  intro fuel
  induction fuel with
  | zero => intro atom absent; rfl
  | succ fuel ih =>
      intro atom absent
      cases atom with
      | symbol name => rfl
      | grounded value => rfl
      | var name =>
          have outside : name ≠ right := by simpa [TypeSubst.typeVars, eq_comm] using absent
          by_cases same : name = left
          · subst name
            simp [Bindings.hasResolvableVarAux, scoped_type_class_fresh leftFresh,
              EqualityClosure.eqClassOrdered_addEquality_of_fresh leftFresh rightFresh different,
              Bindings.isBound, assigned]
          · simp only [Bindings.hasResolvableVarAux,
              EqualityClosure.eqClassOrdered_addEquality_of_outside_fresh
                leftFresh rightFresh different same outside]
            rfl
      | expression atoms =>
          have children : ∀ atom ∈ atoms,
              (bindings.addEquality left right).hasResolvableVarAux fuel atom =
                bindings.hasResolvableVarAux fuel atom := by
            intro atom member
            exact ih atom (fun occurs => absent
              (Freshness.typeVars_mem_typeVarsList_of_mem member right occurs))
          simp only [Bindings.hasResolvableVarAux]
          clear absent
          induction atoms with
          | nil => rfl
          | cons atom rest tail =>
              simp only [List.any_cons, children atom (by simp)]
              rw [tail (fun child member => children child (by simp [member]))]

private theorem scoped_type_alias_resolveAux {bindings : Bindings} {left right actual : String}
    (leftFresh : left ∉ bindings.eqVarsInOrder)
    (rightFresh : right ∉ specBindingVars bindings) (different : left ≠ right)
    (assigned : bindings.lookup left = some (.symbol actual)) :
    ∀ fuel visited atom, right ∉ visited → right ∉ TypeSubst.typeVars atom →
      (bindings.addEquality left right).resolveAtomFullAux fuel visited atom =
        bindings.resolveAtomFullAux fuel visited atom := by
  have rightEdges := scoped_type_fresh_edges rightFresh
  have lookups : (bindings.addEquality left right).lookup = bindings.lookup := rfl
  intro fuel
  induction fuel with
  | zero => intro visited atom avoided absent; rfl
  | succ fuel ih =>
      intro visited atom avoided absent
      cases atom with
      | symbol name => rfl
      | grounded value => rfl
      | expression atoms =>
          have children : ∀ atom ∈ atoms,
              (bindings.addEquality left right).resolveAtomFullAux fuel visited atom =
                bindings.resolveAtomFullAux fuel visited atom := by
            intro atom member
            exact ih visited atom avoided (fun occurs => absent
              (Freshness.typeVars_mem_typeVarsList_of_mem member right occurs))
          simp only [Bindings.resolveAtomFullAux]
          have mapped : atoms.mapM
                ((bindings.addEquality left right).resolveAtomFullAux fuel visited) =
              atoms.mapM (bindings.resolveAtomFullAux fuel visited) := by
            clear absent
            induction atoms with
            | nil => rfl
            | cons atom rest tail =>
                simp only [List.mapM_cons, children atom (by simp)]
                rw [tail (fun child member => children child (by simp [member]))]
          rw [mapped]
      | var root =>
          have outside : root ≠ right := by simpa [TypeSubst.typeVars, eq_comm] using absent
          by_cases same : root = left
          · subst root
            simp [Bindings.resolveAtomFullAux, scoped_type_class_fresh leftFresh,
              EqualityClosure.eqClassOrdered_addEquality_of_fresh leftFresh rightEdges different,
              lookups, assigned, avoided, Bindings.hasResolvableVar,
              Bindings.hasResolvableVarAux, Bindings.atomScanFuel]
          · have classes := EqualityClosure.eqClassOrdered_addEquality_of_outside_fresh
              leftFresh rightEdges different same outside
            have nextAvoided : right ∉ bindings.eqClassOrdered root ++ visited := by
              simp only [List.mem_append, not_or]
              exact ⟨scoped_type_class_avoids rightEdges outside, avoided⟩
            simp only [Bindings.resolveAtomFullAux, classes, lookups]
            split
            · rfl
            · cases found : (bindings.eqClassOrdered root).findSome? bindings.lookup with
              | none => simp only [Bindings.eqRepresentative, classes]
              | some value =>
                  obtain ⟨key, _member, lookup⟩ := List.exists_of_findSome?_eq_some found
                  have valueAbsent := scoped_type_lookup_avoids rightFresh lookup
                  have scanned : (bindings.addEquality left right).hasResolvableVar value =
                      bindings.hasResolvableVar value :=
                    scoped_type_alias_guard leftFresh rightEdges different assigned _ value valueAbsent
                  have continued := ih (bindings.eqClassOrdered root ++ visited) value
                    nextAvoided valueAbsent
                  cases value <;> simp only [scanned, continued, Bindings.eqRepresentative, classes]

private theorem scoped_type_alias_resolve {bindings : Bindings} {left right actual root : String}
    (leftFresh : left ∉ bindings.eqVarsInOrder)
    (rightFresh : right ∉ specBindingVars bindings) (different : left ≠ right)
    (assigned : bindings.lookup left = some (.symbol actual)) (outside : root ≠ right)
    (fuel : Nat) :
    (bindings.addEquality left right).resolveFull root fuel = bindings.resolveFull root fuel := by
  have rightEdges := scoped_type_fresh_edges rightFresh
  have lookups : (bindings.addEquality left right).lookup = bindings.lookup := rfl
  have read := scoped_type_alias_resolveAux leftFresh rightFresh different assigned
    fuel [] (.var root) (by simp) (by simpa [TypeSubst.typeVars, eq_comm] using outside)
  by_cases same : root = left
  · subst root
    simp only [Bindings.resolveFull, scoped_type_class_fresh leftFresh,
      EqualityClosure.eqClassOrdered_addEquality_of_fresh leftFresh rightEdges different,
      lookups, List.findSome?_cons, assigned, Option.isNone_some, Bool.and_false,
      Bool.false_eq_true, if_false, read]
  · simp only [Bindings.resolveFull,
      EqualityClosure.eqClassOrdered_addEquality_of_outside_fresh
        leftFresh rightEdges different same outside, lookups, read]

private theorem scoped_type_alias_fresh_read {bindings : Bindings} {left right actual : String}
    (leftFresh : left ∉ bindings.eqVarsInOrder)
    (rightFresh : right ∉ specBindingVars bindings) (different : left ≠ right)
    (assigned : bindings.lookup left = some (.symbol actual)) (fuel : Nat) :
    (bindings.addEquality left right).applyFull (.var right) (fuel + 2) = .symbol actual := by
  have connected : (EqualityClosure.edgeGraph
      (bindings.addEquality left right).equalities).Reachable left right :=
    ⟨.cons ⟨different, Or.inl (by simp [Bindings.addEquality])⟩ .nil⟩
  have classRight : (bindings.addEquality left right).eqClassOrdered right = [left, right] :=
    (EqualityClosure.eqClassOrdered_eq_of_reachable connected).symm.trans
      (EqualityClosure.eqClassOrdered_addEquality_of_fresh leftFresh
        (scoped_type_fresh_edges rightFresh) different)
  have lookups : (bindings.addEquality left right).lookup = bindings.lookup := rfl
  simp [Bindings.applyFull, Bindings.resolveFull, Bindings.resolveAtomFullAux, classRight,
    lookups, assigned, Bindings.hasResolvableVar, Bindings.hasResolvableVarAux, Bindings.atomScanFuel]



private theorem scoped_type_bind_unchanged {bindings : Bindings} {table : TypeSubst}
    (certificate : ReadoutCertificate bindings table) {name actual : String}
    (fresh : name ∉ specBindingVars bindings) (atom : Atom)
    (absent : name ∉ TypeSubst.typeVars atom) :
    (table.bind name (.symbol actual)).apply atom = table.apply atom := by
  rw [TypeSubst.bind_apply_eq_applyAssignment_apply _ _ _ _
    (certificate.lookup_none_of_outside fresh)]
  apply TypeSubst.apply_eq_self_of_variables_not_keys
  intro other occurs stored
  have same : other = name := by simpa [TypeSubst.keys] using stored
  exact certificate.avoids_outside fresh atom absent (same ▸ occurs)

/-- A fresh applicability assignment renews the actual saved frame and its
single independent readout table. Older alias classes remain intact, and
all covered pending operands share the same extended interpretation. -/
theorem scoped_type_assignment_frame {native source : Bindings} {table : TypeSubst}
    (certificate : ReadoutCertificate source table)
    (related : SourceBindingComparison.semantic.FrameRelated native
      (.selected source table certificate)) (name actual : String)
    (fresh : name ∉ specBindingVars native) :
    ∃ nextCertificate : ReadoutCertificate (source.assign name (.symbol actual))
        (table.bind name (.symbol actual)),
      SourceBindingComparison.semantic.FrameRelated
        (native.assign name (.symbol actual))
        (.selected (source.assign name (.symbol actual)) (table.bind name (.symbol actual))
          nextCertificate) ∧
      BindingFrame.Update .renew (.selected source table certificate)
        (.selected (source.assign name (.symbol actual)) (table.bind name (.symbol actual))
          nextCertificate) ∧
      ∀ pending : List Atom, (pending.map table.apply).map
        (table.bind name (.symbol actual)).apply =
          pending.map (table.bind name (.symbol actual)).apply := by
  have agreement : BindingSourceAgreement native source := related.related
  have sourceFresh : name ∉ specBindingVars source :=
    fun member => fresh ((agreement.support name).mpr member)
  let nextCertificate := certificate.fresh_assignment name (.symbol actual) sourceFresh (by simp [TypeSubst.typeVars])
  have freshFrame := FreshPrivateMerge.readFrame_of_fresh
    (keys := fun key => key = name) (bindings := native) (by
      intro key same
      subst key
      exact fresh)
  have nativeUnbound : native.lookup name = none := freshFrame.reads name rfl
  have sourceUnbound : source.lookup name = none :=
    (FreshPrivateMerge.readFrame_of_fresh (keys := fun key => key = name)
      (by intro key same; subst key; exact sourceFresh)).reads name rfl
  have nativeAssigned : native.assign name (.symbol actual) =
      ⟨native.assignments ++ [(name, .symbol actual)], native.equalities⟩ := by
    simp [Bindings.assign, Bindings.isBound, nativeUnbound]
  have sourceAssigned : source.assign name (.symbol actual) =
      ⟨source.assignments ++ [(name, .symbol actual)], source.equalities⟩ := by
    simp [Bindings.assign, Bindings.isBound, sourceUnbound]
  have nextAgreement : BindingSourceAgreement (native.assign name (.symbol actual))
      (source.assign name (.symbol actual)) := by
    rw [nativeAssigned, sourceAssigned]
    constructor
    · intro valuation
      simpa only [List.append_nil] using
        solution_iff_append agreement.solutions ⟨[(name, .symbol actual)], []⟩ valuation
    · intro key
      simpa only [List.append_nil] using
        support_iff_append agreement.support ⟨[(name, .symbol actual)], []⟩ key
  have classes : ∀ root, root ≠ name → name ∉ native.eqClassOrdered root :=
    fun _ different => scoped_type_class_avoids (scoped_type_fresh_edges fresh) different
  have values : ∀ key value, native.lookup key = some value →
      name ∉ Mettapedia.Languages.MeTTa.SubstitutionAlgebra.vars value := by
    intro key value found
    simpa only [← TypeSubst.typeVars_eq_vars] using scoped_type_lookup_avoids fresh found
  have complete : ∀ atom,
      (native.assign name (.symbol actual)).applyFull atom
          ((native.assign name (.symbol actual)).resolutionFuel atom) =
        (table.bind name (.symbol actual)).apply atom := by
    intro atom
    induction atom using Atom.rec
        (motive_2 := fun atoms =>
          atoms.map (fun child => (native.assign name (.symbol actual)).applyFull child
              ((native.assign name (.symbol actual)).resolutionFuel child)) =
            atoms.map (table.bind name (.symbol actual)).apply) with
    | symbol key => simp [Bindings.resolutionFuel, Bindings.applyFull, TypeSubst.apply]
    | grounded value => simp [Bindings.resolutionFuel, Bindings.applyFull, TypeSubst.apply]
    | var root =>
        by_cases same : root = name
        · subst root
          have singleton : (native.assign name (.symbol actual)).eqClassOrdered name = [name] :=
            freshFrame.orderedClass rfl
          have assigned := lookup_assign_of_lookup_none native name (.symbol actual) nativeUnbound
          simp [Bindings.resolutionFuel, Bindings.applyFull, Bindings.resolveFull,
            Bindings.resolveAtomFullAux, singleton, assigned, Bindings.hasResolvableVar,
            Bindings.hasResolvableVarAux, Bindings.atomScanFuel, TypeSubst.apply,
            TypeSubst.lookup_bind]
        · have unchanged : ∀ fuel,
              (native.assign name (.symbol actual)).applyFull (.var root) fuel =
                native.applyFull (.var root) fuel := by
            intro fuel
            apply BindingResolutionReadSupport.applyFull_assign_unrelated
            cases fuel with
            | zero => simp [BindingResolutionReadSupport.applySupport]
            | succ fuel =>
                simp only [BindingResolutionReadSupport.applySupport,
                  BindingResolutionReadSupport.support, List.mem_append, not_or]
                exact ⟨classes root same,
                  BindingResolutionReadSupport.atomSupport_avoids native name classes values
                    fuel [] (.var root) (by simpa [SubstitutionAlgebra.vars, eq_comm] using same)⟩
          have oldRead : native.applyFull (.var root) (native.resolutionFuel (.var root)) =
              table.apply (.var root) :=
            related.materialization (.var root) _ (native.applyFullCovered_resolutionFuel _)
          have oldStable := native.applyFullCovered_stable (.var root)
            (native.resolutionFuel (.var root))
            ((native.assign name (.symbol actual)).resolutionFuel (.var root))
            (native.applyFullCovered_resolutionFuel _)
          have nextStable := (native.assign name (.symbol actual)).applyFullCovered_stable
            (.var root) ((native.assign name (.symbol actual)).resolutionFuel (.var root))
            (native.resolutionFuel (.var root))
            ((native.assign name (.symbol actual)).applyFullCovered_resolutionFuel _)
          rw [Nat.add_comm ((native.assign name (.symbol actual)).resolutionFuel (.var root))]
            at nextStable
          exact (nextStable.symm.trans ((unchanged _).trans oldStable)).trans (oldRead.trans
            (scoped_type_bind_unchanged certificate sourceFresh (.var root)
              (by simpa [TypeSubst.typeVars, eq_comm] using same)).symm)
    | expression atoms children =>
        rw [Bindings.applyFull_resolutionFuel_expression]
        simpa only [TypeSubst.apply] using congrArg Atom.expression children
    | nil => rfl
    | cons atom atoms head tail => exact congrArg₂ List.cons head tail
  refine ⟨nextCertificate, .semantic nextAgreement nextCertificate ?_,
    .selected certificate nextCertificate, ?_⟩
  · intro atom depth covered
    rw [← Bindings.applyFull_resolutionFuel_eq_of_covered _ atom depth covered]
    exact complete atom
  · intro pending
    apply certificate.pending_absorbed nextCertificate _ pending
    intro valuation model
    rw [sourceAssigned] at model
    exact ((appendPrivatePresentation_solutions valuation source [(name, .symbol actual)]).mp
      model).1

/-- A reached scoped type checkpoint renews one joint readout after its fresh
head instance is linked to the already assigned applicability instance. The
worker retains both equality occurrences; the source retains their one fold.
All covered operands agree, including saved syntax and repeated variables. -/
theorem scoped_type_alias_frame {native source : Bindings} {table : TypeSubst}
    (certificate : ReadoutCertificate source table)
    (related : SourceBindingComparison.semantic.FrameRelated native
      (.selected source table certificate)) (left right actual : String)
    (leftFresh : left ∉ native.eqVarsInOrder)
    (rightFresh : right ∉ specBindingVars native) (different : left ≠ right)
    (assigned : native.lookup left = some (.symbol actual)) :
    ∃ nextCertificate : ReadoutCertificate (source.addEquality left right)
        (table.bind right (.symbol actual)),
      SourceBindingComparison.semantic.FrameRelated
        ((native.addEquality left right).addEquality left right)
        (.selected (source.addEquality left right) (table.bind right (.symbol actual))
          nextCertificate) ∧
      BindingFrame.Update .renew (.selected source table certificate)
        (.selected (source.addEquality left right) (table.bind right (.symbol actual))
          nextCertificate) ∧
      ∀ pending : List Atom, (pending.map table.apply).map
        (table.bind right (.symbol actual)).apply =
          pending.map (table.bind right (.symbol actual)).apply := by
  have agreement : BindingSourceAgreement native source := related.related
  have sourceFresh : right ∉ specBindingVars source :=
    fun member => rightFresh ((agreement.support right).mpr member)
  have forced (valuation : String → Atom) (model : TypeBindingSatisfied valuation source) :
      valuation left = .symbol actual := by
    have nativeModel := (agreement.solutions valuation).mpr model
    obtain ⟨before, after, entries, _⟩ := List.lookup_eq_some_iff.mp assigned
    simpa only [applyTypeValuation] using
      nativeModel.1 left (.symbol actual) (by simp [entries])
  let nextCertificate := scoped_type_alias_certificate certificate left right actual sourceFresh forced
  have nextAgreement : BindingSourceAgreement (native.addEquality left right)
      (source.addEquality left right) := by
    constructor
    · intro valuation
      simpa only [Bindings.addEquality, List.append_nil] using
        solution_iff_append agreement.solutions ⟨[], [(left, right)]⟩ valuation
    · intro name
      simpa only [Bindings.addEquality, List.append_nil] using
        support_iff_append agreement.support ⟨[], [(left, right)]⟩ name
  have complete : ∀ atom,
      (native.addEquality left right).applyFull atom
          ((native.addEquality left right).resolutionFuel atom) =
        (table.bind right (.symbol actual)).apply atom := by
    intro atom
    induction atom using Atom.rec
        (motive_2 := fun atoms =>
          atoms.map (fun child => (native.addEquality left right).applyFull child
              ((native.addEquality left right).resolutionFuel child)) =
            atoms.map (table.bind right (.symbol actual)).apply) with
    | symbol name => simp [Bindings.resolutionFuel, Bindings.applyFull, TypeSubst.apply]
    | grounded value => simp [Bindings.resolutionFuel, Bindings.applyFull, TypeSubst.apply]
    | var name =>
        by_cases same : name = right
        · subst name
          have read := scoped_type_alias_fresh_read leftFresh rightFresh different assigned
            (native.boundVars.toFinset.card * (native.resolutionValueDepth + 1) + 2)
          simpa only [Bindings.resolutionFuel, Bindings.boundVars, Bindings.resolutionValueDepth,
            Bindings.addEquality, Bindings.atomScanFuel, TypeSubst.apply, TypeSubst.lookup_bind,
            if_pos rfl, ite_true, Option.getD_some, Nat.add_assoc] using read
        · have sameAt : ∀ fuel, (native.addEquality left right).applyFull (.var name) fuel =
              native.applyFull (.var name) fuel := by
            intro fuel
            cases fuel with
            | zero => rfl
            | succ fuel =>
                simp only [Bindings.applyFull,
                  scoped_type_alias_resolve leftFresh rightFresh different assigned same fuel]
          have oldRead : native.applyFull (.var name) (native.resolutionFuel (.var name)) =
              table.apply (.var name) := by
            exact related.materialization (.var name) _ (native.applyFullCovered_resolutionFuel _)
          exact (sameAt _).trans (oldRead.trans
            (scoped_type_bind_unchanged certificate sourceFresh (.var name)
              (by simpa [TypeSubst.typeVars, eq_comm] using same)).symm)
    | expression atoms children =>
        rw [Bindings.applyFull_resolutionFuel_expression]
        simpa only [TypeSubst.apply] using congrArg Atom.expression children
    | nil => rfl
    | cons atom atoms head tail => exact congrArg₂ List.cons head tail
  refine ⟨nextCertificate, .semantic
    ((repeated_type_edge_agreement native left right).trans nextAgreement)
    nextCertificate ?_, .selected certificate nextCertificate, ?_⟩
  · intro atom depth covered
    rw [← Bindings.applyFull_resolutionFuel_eq_of_covered _ atom depth covered,
      BindingResolutionReadSupport.applyFull_addEquality_of_mem
        (by simp [Bindings.addEquality]) atom]
    exact complete atom
  · intro pending
    apply certificate.pending_absorbed nextCertificate _ pending
    intro valuation model
    refine ⟨model.1, ?_⟩
    intro first second stored
    exact model.2 first second (List.mem_append_left _ stored)

/-- The expression request retains every name required by the source's typed
use, in addition to the older receivers and already emitted occurrences. -/
private theorem expression_invocation_scope_retained (state : Configuration)
    (expression expected : Atom) (bindings : Bindings) (fuel : Nat) (live : List Atom)
    (pending : state.control = .work (.expression expression expected bindings fuel live)) :
    ∀ name ∈ invocationTypeScope (RecursiveScope.configurationNames state)
        live expression expected bindings,
      name ∈ RecursiveScope.configurationNames state ++ bindings.names := by
  intro name member
  simp only [invocationTypeScope, List.mem_append] at member ⊢
  rcases member with (kept | used) | bound
  · exact Or.inl kept
  · left
    rw [← atomListVariables_eq_typeVarsList] at used
    simp only [atomListVariables_append, atomListVariables, List.append_nil,
      List.mem_append] at used
    simp only [RecursiveScope.configurationNames, RecursiveScope.liveAtoms, pending,
      RecursiveScope.controlAtoms, RecursiveScope.taskAtoms, atomListVariables_append,
      atomListVariables, List.append_nil, List.mem_append]
    tauto
  · exact Or.inr (by rwa [EquationFreshening.bindings_names_eq_specBindingVars])

/-- A literal operator annotation earns its fresh whole-arrow instance and
the first applicable binding at the actual saved configuration. The two
checked transitions retain the chosen instance, changed binding, stack and
emitted prefix. The final equation resumes precisely that checkpoint; it does
not assert completion of the later operator, argument or call work. -/
theorem scoped_polymorphic_annotation_prefix (state : Configuration)
    (dispatch : HE.GroundedDispatch) (operator parameter actual : String)
    (argument : Atom) (bindings : Bindings) (depth : Nat) (live : List Atom)
    (pending : state.control = .work (.expression
      (.expression [.symbol operator, argument]) Atom.undefinedType bindings (depth + 4) live))
    (declared : getAtomTypes state.space (.symbol operator) =
      [.expression [.symbol "->", .var parameter, .var parameter]])
    (argumentTypes : getAtomTypes state.space argument = [.symbol actual])
    (notUndefined : actual ≠ "%Undefined%") (notAtom : actual ≠ "Atom") :
    let name := instanceName (RecursiveScope.configurationNames state ++ bindings.names)
      [parameter] 0 parameter
    let signature := Atom.expression [.symbol "->", .var name, .var name]
    let call := Atom.expression [.symbol operator, argument]
    let scope := invocationTypeScope (RecursiveScope.configurationNames state)
      live call Atom.undefinedType bindings
    let selected := {state with control := .work (.functions
      call Atom.undefinedType bindings (depth + 3) [signature] live)}
    let reached := {state with control := .work (.bindingAlternatives
      call signature (.var name) (depth + 3)
        [bindings.assign name (.symbol actual)] live)}
    StorageTypesRel state.space (.symbol operator)
        [.expression [.symbol "->", .var parameter, .var parameter]] ∧
    ArgumentAlphaVariantsRel scope
        [.expression [.symbol "->", .var parameter, .var parameter]] [signature] ∧
    name ∉ RecursiveScope.configurationNames state ∧ name ∉ bindings.names ∧
    scopedStorageTypeService.candidateScan scope state.space call Atom.undefinedType bindings
        [signature] (.success (freshPolymorphicPolicy name)
          (bindings.assign name (.symbol actual))) ∧
    (Checked.machine dispatch scopedTypes).step state = some (.silent selected) ∧
    (Checked.machine dispatch scopedTypes).step selected = some (.silent reached) ∧
    ∀ budget, (Checked.machine dispatch scopedTypes).run (2 + budget) state =
      (Checked.machine dispatch scopedTypes).run budget reached := by
  dsimp only
  let name := instanceName (RecursiveScope.configurationNames state ++ bindings.names)
    [parameter] 0 parameter
  let signature := Atom.expression [.symbol "->", .var name, .var name]
  let call := Atom.expression [.symbol operator, argument]
  let scope := invocationTypeScope (RecursiveScope.configurationNames state)
    live call Atom.undefinedType bindings
  let selected := {state with control := .work (.functions
    call Atom.undefinedType bindings (depth + 3) [signature] live)}
  let reached := {state with control := .work (.bindingAlternatives
    call signature (.var name) (depth + 3)
      [bindings.assign name (.symbol actual)] live)}
  have queried : invocationTypes state bindings (.symbol operator) Atom.undefinedType =
      [signature] := by
    simp [invocationTypes, getAtomTypesScoped, declared, instantiateTypeSignatures,
      instantiateTypeSignature, atomVariables, atomListVariables, renameAtom, renameAtomList,
      List.eraseDups_cons, signature, name]
  have fresh : name ∉ RecursiveScope.configurationNames state ++ bindings.names :=
    instanceName_not_mem _ _ _ _
  have freshClass : bindings.classValues name = [] := by
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro value member
    exact fresh (List.mem_append_right _ (by
      rw [EquationFreshening.bindings_names_eq_specBindingVars]
      exact FreshPrivateMerge.class_key_support member))
  have variants : ArgumentAlphaVariantsRel scope
      [.expression [.symbol "->", .var parameter, .var parameter]] [signature] := by
    have instances := EquationFreshening.getAtomTypesScoped_variants
      (RecursiveScope.configurationNames state) state.space bindings
      (.symbol operator) Atom.undefinedType (avoid := scope) (fun candidate member => by
        have retained := expression_invocation_scope_retained state call Atom.undefinedType
          bindings (depth + 4) live pending candidate member
        simpa only [EquationFreshening.bindings_names_eq_specBindingVars,
          TypeSubst.typeVars, List.append_nil, Atom.undefinedType] using retained)
    change ArgumentAlphaVariantsRel scope (getAtomTypes state.space (.symbol operator))
      (invocationTypes state bindings (.symbol operator) Atom.undefinedType) at instances
    simpa only [declared, queried] using instances
  have first : (Checked.machine dispatch scopedTypes).step state =
      some (.silent selected) := by
    have ready : Checked.blocked dispatch state scopedTypes = none := by
      simp only [Checked.blocked, pending, FirstSuccessRecursiveStrategy.taskReady,
        RecursiveMachine.Checked.taskReady]
      rfl
    simp only [Checked.machine, RecursiveMachine.Checked.guardMachine]
    rw [ready]
    simp only [FirstSuccessRecursiveExecution.machine, next, pending, scopedTypes,
      FirstSuccessRecursiveStrategy.enter, queried, List.nil_append]
    rfl
  have second : (Checked.machine dispatch scopedTypes).step selected =
      some (.silent reached) := by
    exact fresh_polymorphic_scoped_step selected dispatch (.symbol operator) argument name actual
      bindings depth [] live rfl argumentTypes notUndefined notAtom freshClass
  have source := (fresh_polymorphic_scoped_selection selected (.symbol operator) argument
    name actual bindings depth [] scope argumentTypes notUndefined notAtom freshClass).2.2
  refine ⟨?_, variants, ?_, ?_, source, first, second, ?_⟩
  · rw [← declared]
    exact FirstSuccessSourceReplies.source_types _ _
  · exact fun member => fresh (List.mem_append_left _ member)
  · exact fun member => fresh (List.mem_append_right _ member)
  · intro budget
    rw [show 2 + budget = (budget + 1) + 1 by omega,
      (Checked.machine dispatch scopedTypes).run_succ_silent first,
      (Checked.machine dispatch scopedTypes).run_succ_silent second]

/-- The actual scoped annotation prefix also constructs the independent
frame after its first applicability assignment. It starts with the saved
configuration, retains that configuration's stack and emitted prefix, and
makes one extended table available to every later operand. This is a prefix
and frame correspondence, not completion of the later function work. -/
theorem scoped_polymorphic_annotation_frame (state : Configuration)
    (dispatch : HE.GroundedDispatch) (operator parameter actual : String)
    (argument : Atom) (native source : Bindings) (table : TypeSubst)
    (certificate : ReadoutCertificate source table)
    (related : SourceBindingComparison.semantic.FrameRelated native
      (.selected source table certificate)) (depth : Nat) (live : List Atom)
    (pending : state.control = .work (.expression
      (.expression [.symbol operator, argument]) Atom.undefinedType native (depth + 4) live))
    (declared : getAtomTypes state.space (.symbol operator) =
      [.expression [.symbol "->", .var parameter, .var parameter]])
    (argumentTypes : getAtomTypes state.space argument = [.symbol actual])
    (notUndefined : actual ≠ "%Undefined%") (notAtom : actual ≠ "Atom") :
    let name := instanceName (RecursiveScope.configurationNames state ++ native.names)
      [parameter] 0 parameter
    let signature := Atom.expression [.symbol "->", .var name, .var name]
    let reached := {state with control := .work (.bindingAlternatives
      (.expression [.symbol operator, argument]) signature (.var name) (depth + 3)
        [native.assign name (.symbol actual)] live)}
    ∃ nextCertificate : ReadoutCertificate (source.assign name (.symbol actual))
        (table.bind name (.symbol actual)),
      SourceBindingComparison.semantic.FrameRelated (native.assign name (.symbol actual))
        (.selected (source.assign name (.symbol actual)) (table.bind name (.symbol actual))
          nextCertificate) ∧
      BindingFrame.Update .renew (.selected source table certificate)
        (.selected (source.assign name (.symbol actual)) (table.bind name (.symbol actual))
          nextCertificate) ∧
      (∀ operands : List Atom, (operands.map table.apply).map
        (table.bind name (.symbol actual)).apply =
          operands.map (table.bind name (.symbol actual)).apply) ∧
      ∀ budget, (Checked.machine dispatch scopedTypes).run (2 + budget) state =
        (Checked.machine dispatch scopedTypes).run budget reached := by
  have selectedPrefix := scoped_polymorphic_annotation_prefix state dispatch operator parameter actual
    argument native depth live pending declared argumentTypes notUndefined notAtom
  have fresh : instanceName (RecursiveScope.configurationNames state ++ native.names)
      [parameter] 0 parameter ∉ specBindingVars native := by
    intro member
    exact selectedPrefix.2.2.2.1
      ((EquationFreshening.bindings_names_eq_specBindingVars native).symm ▸ member)
  obtain ⟨next, nextRelated, renewal, absorbed⟩ := scoped_type_assignment_frame
    certificate related _ actual fresh
  exact ⟨next, nextRelated, renewal, absorbed, selectedPrefix.2.2.2.2.2.2.2⟩

namespace ScopedAnnotationControls

private def space : Space := Space.ofList
  [.expression [.symbol ":", .symbol "ident",
    .expression [.symbol "->", .var "t", .var "t"]]]
private def incoming : Bindings := Bindings.empty.assign "t" (.symbol "Number")
private def argument : Atom := .grounded (.bool true)
private def call : Atom := .expression [.symbol "ident", argument]
private def live : List Atom := [.var "held"]
private def loaded : Configuration :=
  {Configuration.initial space (.atom call Atom.undefinedType incoming 12 live) with
    stack := [.functionTerminal (some (.expression [.symbol "caller", .var "t#0"]))]
    emitted := [(.var "t#1", incoming)]}
private def entered : Configuration :=
  {loaded with
    control := .work (.expression call Atom.undefinedType incoming 11 live)
    stack := .filter :: loaded.stack}
private def reached : Configuration :=
  {entered with control := .work (.bindingAlternatives call
    (.expression [.symbol "->", .var "t#2", .var "t#2"])
    (.var "t#2") 10 [incoming.assign "t#2" (.symbol "Bool")] live)}

/-- The initial atom request reaches expression interpretation using the
actual loader and retains its enclosing caller and emitted prefix. -/
theorem loader_enters_the_annotated_call :
    (Checked.machine HE.GroundedDispatch.none scopedTypes).step loaded =
      some (.silent entered) := by
  rfl

/-- Names held by both an older caller and an emitted occurrence are skipped.
The checked prefix reaches the real applicability assignment, preserving the
caller's independent assignment to the raw declaration name. -/
theorem annotated_call_reaches_changed_binding :
    (Checked.machine HE.GroundedDispatch.none scopedTypes).run 3 loaded =
      ([], .exhausted reached) := by
  have selected := scoped_polymorphic_annotation_prefix entered HE.GroundedDispatch.none
    "ident" "t" "Bool" argument incoming 7 live rfl rfl rfl (by decide) (by decide)
  rw [(Checked.machine HE.GroundedDispatch.none scopedTypes).run_succ_silent
    loader_enters_the_annotated_call]
  exact selected.2.2.2.2.2.2.2 0

/-- The source witness starts with the actual annotation; its selected fresh
signature and changed applicability binding are constructed by the prefix law. -/
theorem annotated_call_has_scoped_source_selection :
    StorageTypesRel space (.symbol "ident")
        [.expression [.symbol "->", .var "t", .var "t"]] ∧
    ArgumentAlphaVariantsRel
      (invocationTypeScope (RecursiveScope.configurationNames entered)
        live call Atom.undefinedType incoming)
      [.expression [.symbol "->", .var "t", .var "t"]]
      [.expression [.symbol "->", .var "t#2", .var "t#2"]] ∧
    scopedStorageTypeService.candidateScan
      (invocationTypeScope (RecursiveScope.configurationNames entered)
        live call Atom.undefinedType incoming)
      space call Atom.undefinedType incoming
      [.expression [.symbol "->", .var "t#2", .var "t#2"]]
      (.success (freshPolymorphicPolicy "t#2") (incoming.assign "t#2" (.symbol "Bool"))) := by
  have selected := scoped_polymorphic_annotation_prefix entered HE.GroundedDispatch.none
    "ident" "t" "Bool" argument incoming 7 live rfl rfl rfl (by decide) (by decide)
  exact ⟨selected.1, selected.2.1, selected.2.2.2.2.1⟩

/-- Resumption consumes the retained chosen signature rather than repeating
the annotation lookup or the changed-binding applicability operation. -/
theorem annotated_checkpoint_resumes (budget : Nat) :
    (Checked.machine HE.GroundedDispatch.none scopedTypes).run (3 + budget) loaded =
      (Checked.machine HE.GroundedDispatch.none scopedTypes).run budget reached := by
  have selected := scoped_polymorphic_annotation_prefix entered HE.GroundedDispatch.none
    "ident" "t" "Bool" argument incoming 7 live rfl rfl rfl (by decide) (by decide)
  rw [show 3 + budget = (2 + budget) + 1 by omega,
    (Checked.machine HE.GroundedDispatch.none scopedTypes).run_succ_silent
      loader_enters_the_annotated_call]
  exact selected.2.2.2.2.2.2.2 budget

/-- The same loaded expression without its annotation has only Undefined
at the candidate frontier; it cannot fabricate a polymorphic signature. -/
theorem absent_annotation_does_not_invent_an_arrow :
    (Checked.machine HE.GroundedDispatch.none scopedTypes).run 2
        {loaded with space := Space.empty} =
      ([], .exhausted {entered with
        space := Space.empty
        control := .work (.functions call Atom.undefinedType incoming 10 [Atom.undefinedType] live)}) := by
  rfl

/-- Literal declaration-name reuse is refused by the contrasting raw lookup
profile, while the annotated scoped prefix above succeeds. -/
theorem raw_annotation_reuses_the_caller_name :
    (Checked.machine HE.GroundedDispatch.none rawTypes).run 3 loaded =
      ([], .exhausted {entered with control := .returning [(mkError call
        (.badArgType 1 (.var "t") (.symbol "Bool")), incoming)]}) := by
  rfl

private def applicabilityBindings : Bindings := incoming.assign "t#2" (.symbol "Bool")
private def applicabilityTable : TypeSubst :=
  [("t#2", .symbol "Bool"), ("t", .symbol "Number")]
private def operatorType : Atom := .expression [.symbol "->", .var "t#2", .var "t#2"]
private def headLive : List Atom := operatorType :: argument :: .var "t#2" :: live
private def functionRequest : Configuration :=
  {reached with
    control := .work (.func call operatorType applicabilityBindings 10 (.var "t#2" :: live))
    stack := .calls (.var "t#2") 10 live ::
      .append (.bindingAlternatives call operatorType (.var "t#2") 10 [] live) :: reached.stack}
private def headRequest : Configuration :=
  {functionRequest with
    control := .work (.atom (.symbol "ident") operatorType applicabilityBindings 9 headLive)
    stack := .heads operatorType [argument] 9 (.var "t#2" :: live) :: functionRequest.stack}
private def nativeHeadBindings : Bindings :=
  (applicabilityBindings.addEquality "t#2" "t#3").addEquality "t#2" "t#3"
private def sourceHeadBindings : Bindings := applicabilityBindings.addEquality "t#2" "t#3"
private def headTable : TypeSubst := applicabilityTable.bind "t#3" (.symbol "Bool")
private def afterHead : Configuration :=
  {headRequest with control := .returning [(.symbol "ident", nativeHeadBindings)]}
private def exhaustedHead : Configuration :=
  {headRequest with control := .work (.atom (.symbol "ident") operatorType
    applicabilityBindings 0 headLive)}
private def headScope : List String := invocationTypeScope
  (RecursiveScope.configurationNames headRequest) headLive (.symbol "ident")
  operatorType applicabilityBindings

private theorem incomingFold : EquationListPresentationRel
    (bindingAtomEquations incoming) [] incoming.assignments := by
  change EquationListPresentationRel [(.var "t", .symbol "Number")] [] [("t", .symbol "Number")]
  have folded : EquationListPresentationRel [(.var "t", .symbol "Number")] []
      (TypeSubst.bind [] "t" (.symbol "Number")) :=
    .cons (.ordinary (resolvedLeft := .var "t") (resolvedRight := .symbol "Number")
      (by simp only [TypeSubst.apply_empty]) (by simp only [TypeSubst.apply_empty])
      (.bindLeft (by simp [TypeSubst.typeVars]))) (.nil _)
  simpa [TypeSubst.bind, TypeSubst.apply, TypeSubst.erase] using folded

private theorem incomingCertificate : ReadoutCertificate incoming incoming.assignments :=
  .of_fold incomingFold

private theorem incomingRelated : SourceBindingComparison.semantic.FrameRelated incoming
    (.selected incoming incoming.assignments incomingCertificate) := by
  apply SourceBindingComparison.FrameRelated.semantic (.refl _) incomingCertificate
  exact FirstSuccessPreparedArguments.applyFull_presented_of_covered incomingFold.bindingTheory.1

private theorem applicabilityCertificate : ReadoutCertificate
    applicabilityBindings applicabilityTable := by
  have next := incomingCertificate.fresh_assignment "t#2" (.symbol "Bool") (by decide +kernel)
    (by simp [TypeSubst.typeVars])
  simpa [applicabilityBindings, applicabilityTable, incoming, Bindings.assign,
    Bindings.isBound, Bindings.lookup, Bindings.empty, TypeSubst.bind, TypeSubst.apply,
    TypeSubst.erase, TypeSubst.applyAssignment] using next

private theorem applicabilityRelated : SourceBindingComparison.semantic.FrameRelated
    applicabilityBindings
    (.selected applicabilityBindings applicabilityTable applicabilityCertificate) := by
  obtain ⟨_certificate, next, _renewal, _absorbed⟩ := scoped_type_assignment_frame
    incomingCertificate incomingRelated "t#2" "Bool" (by decide +kernel)
  simpa [applicabilityBindings, applicabilityTable, incoming, Bindings.assign,
    Bindings.isBound, Bindings.lookup, Bindings.empty, TypeSubst.bind, TypeSubst.apply,
    TypeSubst.erase, TypeSubst.applyAssignment] using next

private theorem alternatives_enter_function :
    (Checked.machine HE.GroundedDispatch.none scopedTypes).step reached =
      some (.silent functionRequest) := by rfl

private theorem function_enters_head :
    (Checked.machine HE.GroundedDispatch.none scopedTypes).step functionRequest =
      some (.silent headRequest) := by rfl

/-- The head query instantiates the complete annotation a second time, apart
from the first instance and every older retained name. The actual cast stores
both matching occurrences and keeps the old caller and emitted prefix. -/
theorem annotated_head_uses_second_fresh_instance :
    invocationTypes headRequest applicabilityBindings (.symbol "ident") operatorType =
        [.expression [.symbol "->", .var "t#3", .var "t#3"]] ∧
    (Checked.machine HE.GroundedDispatch.none scopedTypes).step headRequest =
      some (.silent afterHead) := by
  exact ⟨rfl, rfl⟩

/-- Starting at the real loader reaches the head's changed-binding reply;
resumption retains its already selected two signature instances. -/
theorem annotated_head_checkpoint_resumes (budget : Nat) :
    (Checked.machine HE.GroundedDispatch.none scopedTypes).run (6 + budget) loaded =
      (Checked.machine HE.GroundedDispatch.none scopedTypes).run budget afterHead := by
  rw [show 6 + budget = 3 + (3 + budget) by omega, annotated_checkpoint_resumes,
    show 3 + budget = ((budget + 1) + 1) + 1 by omega,
    (Checked.machine HE.GroundedDispatch.none scopedTypes).run_succ_silent alternatives_enter_function,
    (Checked.machine HE.GroundedDispatch.none scopedTypes).run_succ_silent function_enters_head,
    (Checked.machine HE.GroundedDispatch.none scopedTypes).run_succ_silent
      annotated_head_uses_second_fresh_instance.2]

/-- The reached native reply has an independent scoped atom derivation and
one renewed source table. The source lookup is earned from the same authored
annotation and actual retained configuration, rather than supplied as a cast. -/
theorem annotated_head_has_source_and_joint_readout :
    ∃ certificate : ReadoutCertificate sourceHeadBindings headTable,
      EvalAtomRawRel space noHost headLive
        (protectedScope := RecursiveScope.configurationNames headRequest)
        (typing := scopedStorageTypeService) (.symbol "ident") operatorType
        (.selected applicabilityBindings applicabilityTable applicabilityCertificate)
        (.symbol "ident", .selected sourceHeadBindings headTable certificate) ∧
      SourceBindingComparison.semantic.FrameRelated nativeHeadBindings
        (.selected sourceHeadBindings headTable certificate) ∧
      ∀ pending : List Atom, (pending.map applicabilityTable.apply).map headTable.apply =
        pending.map headTable.apply := by
  have lookup := FirstSuccessSourceReplies.scoped_source_types headRequest headScope
    applicabilityBindings (.symbol "ident") operatorType (by
      change headScope ⊆ RecursiveScope.configurationNames headRequest
      decide +kernel)
  change scopedTypeLookup headScope space applicabilityBindings (.symbol "ident") operatorType
    [.expression [.symbol "->", .var "t#3", .var "t#3"]] at lookup
  obtain ⟨_, cast, _renewal, _absorbed⟩ := scoped_fresh_arrow_cast space headScope
    (.symbol "ident") incoming "t#2" "t#3" "Bool" applicabilityTable applicabilityCertificate
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lookup
  obtain ⟨certificate, next, renewal, absorbed⟩ := scoped_type_alias_frame
    applicabilityCertificate applicabilityRelated "t#2" "t#3" "Bool"
    (by decide +kernel) (by decide +kernel) (by decide +kernel) rfl
  refine ⟨certificate, ?_, next, absorbed⟩
  exact EvalAtomRawRel.cast (.symbol "ident") operatorType Atom.symbolType
    (.selected applicabilityBindings applicabilityTable applicabilityCertificate)
    (.symbol "ident", .selected sourceHeadBindings headTable certificate)
    (by simp [IsEmptyOrErrorRel, IsErrorRel, Atom.empty]) (.symbol "ident")
    (by simp [operatorType, Atom.atomType, Atom.symbolType, Atom.variableType])
    (Or.inl ⟨"ident", rfl⟩) cast renewal

/-- The general fresh-assignment join also applies after the two native
head-alias occurrences, without normalizing away either stored occurrence. -/
theorem fresh_assignment_preserves_repeated_head_aliases :
    ∃ certificate : ReadoutCertificate (sourceHeadBindings.assign "t#4" (.symbol "String"))
        (headTable.bind "t#4" (.symbol "String")),
      SourceBindingComparison.semantic.FrameRelated
        (nativeHeadBindings.assign "t#4" (.symbol "String"))
        (.selected (sourceHeadBindings.assign "t#4" (.symbol "String"))
          (headTable.bind "t#4" (.symbol "String")) certificate) ∧
      ∀ pending : List Atom, (pending.map headTable.apply).map
        (headTable.bind "t#4" (.symbol "String")).apply =
          pending.map (headTable.bind "t#4" (.symbol "String")).apply := by
  obtain ⟨certificate, _source, related, _absorbed⟩ := annotated_head_has_source_and_joint_readout
  obtain ⟨next, reached, _renewal, pending⟩ := scoped_type_assignment_frame
    certificate related "t#4" "String" (by decide +kernel)
  exact ⟨next, reached, pending⟩

/-- Replacing an already assigned name is not a monotone constraint extension:
materializing before the replacement cannot be undone by the new table. -/
theorem assigned_name_cannot_use_fresh_extension_law :
    let before : TypeSubst := [("t", .symbol "Number")]
    let after := before.bind "t" (.symbol "Bool")
    after.apply (before.apply (.var "t")) ≠ after.apply (.var "t") := by
  simp [TypeSubst.bind, TypeSubst.apply, TypeSubst.lookup, TypeSubst.erase,
    TypeSubst.applyAssignment]

/-- Native and source physical records differ, and the old table cannot read
the newly assigned type variable. Both repeated positions use the new table. -/
theorem annotated_head_requires_renewal :
    nativeHeadBindings ≠ sourceHeadBindings ∧
      applicabilityTable.apply (.var "t#3") = .var "t#3" ∧
      headTable.apply (.var "t#3") = .symbol "Bool" ∧
      headTable.apply (.expression [.var "t#2", .var "t#3", .var "t#2"]) =
        .expression [.symbol "Bool", .symbol "Bool", .symbol "Bool"] := by
  refine ⟨by decide +kernel, ?_, ?_, ?_⟩
  · simp [applicabilityTable, TypeSubst.apply, TypeSubst.lookup]
  · simp [headTable, TypeSubst.apply, TypeSubst.lookup_bind]
  · simp [headTable, applicabilityTable, TypeSubst.apply, TypeSubst.lookup_bind,
      TypeSubst.lookup, TypeSubst.applyAssignment]

/-- An exhausted head request is retained; it cannot claim that the checked
cast ran or erase the caller continuation. -/
theorem exhausted_head_does_not_publish_a_reply :
    (Checked.machine HE.GroundedDispatch.none scopedTypes).step exhaustedHead =
      some (.call .evaluationDepth exhaustedHead) := by rfl

/-- Raw head lookup reuses the caller's fixed declaration variable and
therefore refuses the same head that the independently fresh instance accepts. -/
theorem raw_head_conflicts_with_the_caller_type :
    (Checked.machine HE.GroundedDispatch.none rawTypes).step headRequest =
      some (.silent {headRequest with control := .returning [(mkError (.symbol "ident")
        (.badType operatorType (.expression [.symbol "->", .var "t", .var "t"])),
          applicabilityBindings)]}) := by rfl

end ScopedAnnotationControls

#print axioms scoped_type_alias_certificate
#print axioms fresh_arrow_type_match
#print axioms scoped_fresh_arrow_cast
#print axioms scoped_type_alias_frame
#print axioms ScopedAnnotationControls.annotated_head_has_source_and_joint_readout
#print axioms ScopedAnnotationControls.annotated_head_checkpoint_resumes
#print axioms ScopedAnnotationControls.annotated_head_requires_renewal
#print axioms ScopedAnnotationControls.exhausted_head_does_not_publish_a_reply
#print axioms ScopedAnnotationControls.raw_head_conflicts_with_the_caller_type

end ScopedPolymorphicInvocation

/-- The independent typed application rule composes an argument endpoint
with its own call derivation, including changed argument and result bindings. -/
theorem application_retained_spec {space : Space} {name : String} {arguments : List Atom}
    {expected : Atom} {fuel : Nat} (typing : ApplicationTyping space name arguments expected fuel)
    (incoming reached : BindingFrame) (values : List Atom) (live : List Atom) (result : FrameResult)
    (scope : List String)
    (argumentDerivation : InterpretArgsRel space noHost
      (.symbol name ::
        (if typing.returned = Atom.expressionType then Atom.undefinedType else typing.returned) :: live)
      (protectedScope := scope) arguments typing.domains incoming (argumentPacket values, reached))
    (callDerivation : CallRel space noHost live (protectedScope := scope)
      (.expression (.symbol name :: values))
      (if typing.returned = Atom.expressionType then Atom.undefinedType else typing.returned)
      reached result) :
    EvalAtomRawRel space noHost live (protectedScope := scope)
      (.expression (.symbol name :: arguments)) expected incoming result := by
  have interpreted : InterpretExpressionRel space noHost live (protectedScope := scope)
      (.expression (.symbol name :: arguments)) expected incoming result := by
    apply InterpretExpressionRel.functionPath _ _ (.symbol name) arguments
      (getAtomTypes space (.symbol name)) (getAtomTypes space (.symbol name))
      (selectedPolicy typing.domains typing.returned)
      (if typing.returned = Atom.expressionType then Atom.undefinedType else typing.returned)
      incoming incoming (.expression (.symbol name :: values), reached) result rfl
      (FirstSuccessSourceReplies.source_types space (.symbol name))
      rfl (application_selected typing incoming).2 (.same .renew _) rfl
    · have head : EvalAtomRawRel space noHost
          (arrow typing.domains typing.returned :: arguments ++
            (if typing.returned = Atom.expressionType then Atom.undefinedType else typing.returned) :: live)
          (protectedScope := scope ++ expectedApplicationScope (.expression (.symbol name :: arguments)) expected)
          (.symbol name) (arrow typing.domains typing.returned) incoming (.symbol name, incoming) :=
        symbol_cast_spec space name (arrow typing.domains typing.returned) incoming (fuel - 1)
          typing.before typing.after (arrow typing.domains typing.returned)
          typing.nonemptyOperator (by simp [arrow]) (by simp [arrow]) typing.sourceTypes
          typing.headClosed typing.headClosed typing.earlierClosed typing.earlierHeadRejects
          (Or.inr (Or.inr (Or.inr (Or.inr rfl)))) (by have := typing.headBudget; omega) _ _
      simpa only [selectedPolicy, argumentValues_packet] using (InterpretFunctionRel.success
        (.expression (.symbol name :: arguments)) (arrow typing.domains typing.returned) expected
        (.symbol name) typing.returned arguments typing.domains incoming (.symbol name, incoming)
        (argumentPacket values, reached) rfl (show FunctionTypeRel (arrow typing.domains typing.returned)
          typing.domains typing.returned from rfl) head
        (by simp [IsEmptyOrErrorRel, IsErrorRel, Atom.empty, typing.nonemptyOperator]) argumentDerivation
        ⟨values, rfl⟩)
    · exact callDerivation
  have notPass : ¬(expected = Atom.atomType ∨ expected = Atom.expressionType ∨
      Atom.expressionType = Atom.variableType) := by
    rintro (raw | intrinsic | impossible)
    · exact typing.demandNotRaw raw
    · exact typing.demandNotExpression intrinsic
    · simp at impossible
  by_cases error : IsErrorRel result.1
  · exact EvalAtomRawRel.interpretError _ _ Atom.expressionType incoming result
      (clean_application name arguments typing.cleanOperator).1
      (.expression (.symbol name :: arguments)) notPass ⟨.symbol name, arguments, rfl⟩ interpreted error
  · exact EvalAtomRawRel.interpretSuccess _ _ Atom.expressionType incoming result
      (clean_application name arguments typing.cleanOperator).1
      (.expression (.symbol name :: arguments)) notPass ⟨.symbol name, arguments, rfl⟩ interpreted error

/-- An actual Undefined lookup independently licenses the tuple path. No
failed-arrow applicability or expected-output premise is used. -/
theorem untyped_tuple_spec (space : Space) (operator : Atom) (arguments : List Atom)
    (expected : Atom) (incoming : BindingFrame) (tupleResult result : FrameResult)
    (live : List Atom) (scope : List String)
    (clean : isEmptyOrError (.expression (operator :: arguments)) = false)
    (notRaw : expected ≠ Atom.atomType) (notExpression : expected ≠ Atom.expressionType)
    (types : getAtomTypes space operator = [Atom.undefinedType])
    (tuple : InterpretTupleRel space noHost (expected :: live) (protectedScope := scope)
      (.expression (operator :: arguments)) incoming tupleResult)
    (called : CallRel space noHost live (protectedScope := scope)
      tupleResult.1 expected tupleResult.2 result) :
    EvalAtomRawRel space noHost live (protectedScope := scope)
      (.expression (operator :: arguments)) expected incoming result := by
  have sourceTypes : StorageTypesRel space operator [Atom.undefinedType] := by
    rw [← types]
    exact FirstSuccessSourceReplies.source_types space operator
  have scan : storageTypeService.candidateScan
      (invocationTypeScope scope live (.expression (operator :: arguments)) expected incoming)
      space (.expression (operator :: arguments)) expected incoming [Atom.undefinedType]
      (.exhausted [] true) :=
    .nonFunctionExhausted (by simp [FunctionTypeRel, Atom.undefinedType]) .nil
  have interpreted := InterpretExpressionRel.tuplePath
    (.expression (operator :: arguments)) expected operator arguments
    [Atom.undefinedType] [Atom.undefinedType] [] incoming tupleResult result
    rfl sourceTypes rfl scan tuple called
  have running : ¬IsEmptyOrErrorRel (.expression (operator :: arguments)) := by
    intro stopped
    have := (Conformance.isEmptyOrErrorRel_iff_isEmptyOrError _).mp stopped
    simp [clean] at this
  have notPass : ¬(expected = Atom.atomType ∨ expected = Atom.expressionType ∨
      Atom.expressionType = Atom.variableType) := by
    rintro (raw | intrinsic | impossible)
    · exact notRaw raw
    · exact notExpression intrinsic
    · simp at impossible
  by_cases error : IsErrorRel result.1
  · exact EvalAtomRawRel.interpretError _ _ Atom.expressionType incoming result running
      (.expression (operator :: arguments)) notPass ⟨operator, arguments, rfl⟩
      interpreted error
  · exact EvalAtomRawRel.interpretSuccess _ _ Atom.expressionType incoming result running
      (.expression (operator :: arguments)) notPass ⟨operator, arguments, rfl⟩
      interpreted error

mutual
/-- Every delivered occurrence has an independent scoped evaluator derivation
from each related input representation. Both endpoints use the declared
binding comparison; the observed atom and every physical occurrence are unchanged. -/
theorem AtomDerivation.sound {space : Space} {comparison : SourceBindingComparison} {live : List Atom} {value expected : Atom}
    {incoming : Bindings} {fuel : Nat} {results : ResultSet}
    (derivation : AtomDerivation (comparison := comparison) space live value expected incoming fuel results)
    (result : ResultPair) (member : result ∈ results) (scope : List String)
    (independentIncoming : BindingFrame) (related : comparison.FrameRelated incoming independentIncoming) :
    ∃ independentOutput,
      EvalAtomRawRel space noHost live (protectedScope := scope) value expected
        independentIncoming (result.1, independentOutput) ∧
      comparison.FrameRelated result.2 independentOutput := by
  cases derivation with
  | leaf live value expected incoming fuel leaf =>
      obtain rfl := List.mem_singleton.mp member
      exact ⟨independentIncoming,
        leaf_evidence space noHost live storageTypeService scope value expected independentIncoming leaf,
        related⟩
  | symbolCast live name expected incoming fuel before after actual notEmpty notRaw notMeta types
      expectedClosed actualClosed earlierClosed earlierRejects fits enough =>
      obtain rfl := List.mem_singleton.mp member
      exact ⟨independentIncoming,
        symbol_cast_spec space name expected independentIncoming fuel before after actual notEmpty notRaw
          notMeta types expectedClosed actualClosed earlierClosed earlierRejects fits enough live scope,
        related⟩
  | symbolRejected live name expected incoming fuel notEmpty notRaw notMeta expectedClosed closed rejected =>
      obtain ⟨actual, present, rfl⟩ := List.mem_map.mp member
      exact ⟨independentIncoming,
        symbol_rejection_spec space name expected independentIncoming live scope
          notEmpty notRaw notMeta expectedClosed closed rejected actual present, related⟩
  | application live name arguments expected incoming fuel typing rows outputs args calls =>
      obtain ⟨request, present, produced⟩ :=
        List.mem_flatMap.mp (mem_of_mem_successPriority member)
      obtain ⟨row, rowMember, same⟩ := List.mem_map.mp present
      obtain ⟨argumentOutput, argumentSound, argumentRelated⟩ :=
        args.sound row rowMember independentIncoming related scope
      obtain ⟨output, called, outputRelated⟩ := (calls request present).sound result produced
        argumentOutput (same ▸ argumentRelated) scope
      refine ⟨output, ?_, outputRelated⟩
      exact application_retained_spec typing independentIncoming argumentOutput row.1 live
        (result.1, output) scope argumentSound (by simpa only [← same] using called)
  | untypedTuple live operator arguments expected incoming fuel rows outputs clean notRaw notExpr
      types tuple calls =>
      obtain ⟨request, present, produced⟩ := List.mem_flatMap.mp (mem_of_mem_successPriority member)
      obtain ⟨middle, tupleSound, middleRelated⟩ :=
        tuple.sound request present independentIncoming related scope
      obtain ⟨output, called, outputRelated⟩ :=
        (calls request present).sound result produced middle middleRelated scope
      exact ⟨output, untyped_tuple_spec space operator arguments expected independentIncoming
        (request.1, middle) (result.1, output) live scope clean notRaw notExpr types tupleSound called,
        outputRelated⟩
termination_by 2 * fuel

/-- Tuple source meaning follows the actual stopped/singleton/tail receivers,
with the selected source frame transported at each child occurrence. -/
theorem TupleDerivation.sound {space : Space} {comparison : SourceBindingComparison}
    {live : List Atom} {value : Atom} {incoming : Bindings} {fuel : Nat} {results : ResultSet}
    (derivation : TupleDerivation space comparison live value incoming fuel results)
    (result : ResultPair) (member : result ∈ results)
    (independentIncoming : BindingFrame) (related : comparison.FrameRelated incoming independentIncoming)
    (scope : List String := []) :
    ∃ independentOutput,
      InterpretTupleRel space noHost live (protectedScope := scope) value independentIncoming
        (result.1, independentOutput) ∧ comparison.FrameRelated result.2 independentOutput := by
  cases derivation with
  | nil live incoming fuel =>
      obtain rfl := List.mem_singleton.mp member
      exact ⟨independentIncoming, .nil independentIncoming, related⟩
  | singleton live value incoming fuel heads child =>
      obtain ⟨head, present, rfl⟩ := List.mem_map.mp member
      obtain ⟨output, source, outputRelated⟩ := child.sound head present scope independentIncoming related
      cases stopped : isEmptyOrError head.1 with
      | true =>
          simpa only [HE.tupleSingleton_failure head stopped] using
            (show ∃ output, InterpretTupleRel space noHost live (protectedScope := scope)
                (.expression [value]) independentIncoming (head.1, output) ∧
                comparison.FrameRelated head.2 output from
              ⟨output, .singletonError value independentIncoming (head.1, output) source
                ((Conformance.isEmptyOrErrorRel_iff_isEmptyOrError _).mpr stopped), outputRelated⟩)
      | false =>
          have clean : ¬IsEmptyOrErrorRel head.1 := by
            simp only [Conformance.isEmptyOrErrorRel_iff_isEmptyOrError, stopped,
              Bool.false_eq_true, not_false_eq_true]
          simpa only [HE.tupleSingleton_success head stopped] using
            (show ∃ output, InterpretTupleRel space noHost live (protectedScope := scope)
                (.expression [value]) independentIncoming (.expression [head.1], output) ∧
                comparison.FrameRelated head.2 output from
              ⟨output, .singleton value independentIncoming (head.1, output) source clean, outputRelated⟩)
  | cons live head second remaining incoming fuel heads tails first children =>
      obtain ⟨selected, present, outputMember⟩ := List.mem_flatMap.mp member
      obtain ⟨middle, source, middleRelated⟩ := first.sound selected present scope independentIncoming related
      cases stopped : isEmptyOrError selected.1 with
      | true =>
          simp only [stopped, if_true, List.mem_singleton] at outputMember
          subst result
          exact ⟨middle, .headError head (second :: remaining) independentIncoming
            (selected.1, middle) (by simp) source
            ((Conformance.isEmptyOrErrorRel_iff_isEmptyOrError _).mpr stopped), middleRelated⟩
      | false =>
          simp only [stopped, Bool.false_eq_true, if_false, RecursiveTasks.tupleTail] at outputMember
          obtain ⟨rest, restMember, rfl⟩ := List.mem_map.mp outputMember
          obtain ⟨output, tailSource, outputRelated⟩ :=
            (children selected present stopped).sound rest restMember middle middleRelated scope
          have clean : ¬IsEmptyOrErrorRel selected.1 := by
            simp only [Conformance.isEmptyOrErrorRel_iff_isEmptyOrError, stopped,
              Bool.false_eq_true, not_false_eq_true]
          cases tailStopped : isEmptyOrError rest.1 with
          | true =>
              simp only [if_true]
              exact ⟨output, .tailError head (second :: remaining) independentIncoming
                (selected.1, middle) (rest.1, output) (by simp) source clean tailSource
                ((Conformance.isEmptyOrErrorRel_iff_isEmptyOrError _).mpr tailStopped), outputRelated⟩
          | false =>
              simp only [Bool.false_eq_true, if_false]
              have tailClean : ¬IsEmptyOrErrorRel rest.1 := by
                simp only [Conformance.isEmptyOrErrorRel_iff_isEmptyOrError, tailStopped,
                  Bool.false_eq_true, not_false_eq_true]
              refine ⟨output, ?_, outputRelated⟩
              have combined := InterpretTupleRel.success head (second :: remaining)
                independentIncoming (selected.1, middle) (rest.1, output) (by simp)
                source clean tailSource tailClean
              cases shape : rest.1 <;> simpa only [shape, atomElements] using combined
termination_by 2 * fuel

/-- Independent argument interpretation transports both selected head frames
and reached tail frames through their relation-list representations. -/
theorem ArgsDerivation.sound {space : Space} {comparison : SourceBindingComparison} {live : List Atom} {values types : List Atom}
    {incoming : Bindings} {fuel : Nat} {results : ArgumentResults}
    (derivation : ArgsDerivation (comparison := comparison) space live values types incoming fuel results)
    (result : List Atom × Bindings) (member : result ∈ results)
    (independentIncoming : BindingFrame) (related : comparison.FrameRelated incoming independentIncoming) (scope : List String := []) :
    ∃ independentOutput,
      InterpretArgsRel space noHost live (protectedScope := scope) values types independentIncoming
        (argumentPacket result.1, independentOutput) ∧
      comparison.FrameRelated result.2 independentOutput := by
  cases derivation with
  | nil live incoming fuel =>
      obtain rfl := List.mem_singleton.mp member
      exact ⟨independentIncoming, .nil independentIncoming, related⟩
  | cons live value expected values types incoming fuel heads tails head safe tail =>
      obtain ⟨selected, selectedMember, restMember⟩ := List.mem_flatMap.mp member
      obtain ⟨rest, present, rfl⟩ := List.mem_map.mp restMember
      obtain ⟨headOutput, headSound, headRelated⟩ :=
        head.sound selected selectedMember scope independentIncoming related
      obtain ⟨tailOutput, tailSound, tailRelated⟩ :=
        (tail selected selectedMember).sound rest present headOutput headRelated scope
      have guard : ¬IsEmptyOrErrorRel selected.1 ∨ selected.1 = value := by
        rcases safe selected selectedMember with same | clean
        · exact Or.inr same
        · exact Or.inl (by
            intro error
            have failed := (Spec.Type.Conformance.isEmptyOrErrorRel_iff_isEmptyOrError selected.1).mp error
            simp [clean] at failed)
      refine ⟨tailOutput, ?_, tailRelated⟩
      simpa only [argumentValues_packet] using InterpretArgsRel.success value values expected types
        independentIncoming (selected.1, headOutput) (argumentPacket rest.1, tailOutput)
        headSound guard tailSound ⟨rest.1, rfl⟩
termination_by 2 * fuel

/-- Every actual equation branch constructs the existing independent call
judgment. Its representation map transports the query and both binding endpoints. -/
theorem CallDerivation.sound {space : Space} {comparison : SourceBindingComparison} {live : List Atom} {query expected : Atom}
    {incoming : Bindings} {fuel : Nat} {results : ResultSet}
    (derivation : CallDerivation (comparison := comparison) space live query expected incoming fuel results)
    (result : ResultPair) (member : result ∈ results)
    (independentIncoming : BindingFrame) (related : comparison.FrameRelated incoming independentIncoming) (scope : List String := []) :
    ∃ independentOutput,
      CallRel space noHost live (protectedScope := scope) query expected independentIncoming (result.1, independentOutput) ∧
      comparison.FrameRelated result.2 independentOutput := by
  cases derivation with
  | errorPassthrough live value expected incoming fuel error =>
      obtain rfl := List.mem_singleton.mp member
      exact ⟨independentIncoming, .errorPassthrough _ expected independentIncoming error, related⟩
  | unreduced live name arguments expected incoming fuel ordinary nonembedded clean _ absent =>
      obtain rfl := List.mem_singleton.mp member
      refine ⟨independentIncoming, ?_, related⟩
      apply CallRel.noEquation
      · simp [IsErrorRel, clean]
      · exact ⟨by simp [Spec.Eval.Minimal.HostCall, noHost], nonembedded⟩
      · exact related.noMatch space _ _ absent
  | equations live name arguments expected incoming fuel productions outputs ordinary nonembedded clean selected evidence producers bodies =>
      obtain ⟨candidate, candidateMember, produced⟩ := List.mem_flatMap.mp member
      obtain ⟨request, requestMember, produced⟩ := List.mem_flatMap.mp produced
      obtain ⟨completed, completedMember, produced⟩ := List.mem_flatMap.mp produced
      have localEvidence := evidence candidate candidateMember request requestMember
      obtain ⟨merged, mergeRelated, ⟨position, left, right, _, _, occurrence⟩, materialized⟩ :=
        localEvidence.transport independentIncoming related
      obtain ⟨completedFrame, completion, completedRelated⟩ :=
        (producers candidate candidateMember request requestMember).sound
          completed completedMember merged mergeRelated scope
      obtain ⟨output, body, outputRelated⟩ :=
        (bodies candidate candidateMember request requestMember completed completedMember).sound
          result produced completedFrame completedRelated scope
      refine ⟨output, ?_, outputRelated⟩
      apply CallRel.equation _ _ candidate.1 request.1 independentIncoming merged
        (result.1, output) (completed.1, completedFrame)
      · simp [IsErrorRel, clean]
      · exact ⟨by simp [Spec.Eval.Minimal.HostCall, noHost], nonembedded⟩
      · exact occurrence.candidate
      · exact related.renew mergeRelated
      · exact materialized
      · exact completion
      · exact body

  | embedded live name arguments expected incoming fuel raw outputs semantic clean instruction child returns =>
      cases semantic
      obtain ⟨selected, present, produced⟩ := List.mem_flatMap.mp member
      obtain ⟨middle, invoked, middleRelated⟩ := child.sound selected present independentIncoming related scope
      obtain ⟨output, returned, outputRelated⟩ :=
        (returns selected present).sound result produced middle middleRelated scope
      refine ⟨output, ?_, outputRelated⟩
      apply CallRel.embedded (.expression (.symbol name :: arguments)) expected independentIncoming
        (selected.1, middle) (result.1, output)
      · simp [IsErrorRel, clean]
      · simp [Minimal.HostCall, noHost]
      · exact (classifier_agrees _).symm.trans instruction
      · exact .embedded space _ independentIncoming _ (by simp [Minimal.HostCall, noHost])
          ((classifier_agrees _).symm.trans instruction) invoked
      · exact returned

termination_by 2 * fuel

theorem ReturnDerivation.sound {space : Space} {comparison : SourceBindingComparison} {live : List Atom}
    {original expected value : Atom} {bindings : Bindings} {fuel : Nat} {results : ResultSet}
    (derivation : ReturnDerivation (comparison := comparison) space live original expected value bindings fuel results)
    (result : ResultPair) (member : result ∈ results)
    (independentIncoming : BindingFrame) (related : comparison.FrameRelated bindings independentIncoming) (scope : List String := []) :
    ∃ independentOutput,
      CallReturnRel space noHost live (protectedScope := scope) original expected value independentIncoming
        (result.1, independentOutput) ∧ comparison.FrameRelated result.2 independentOutput := by
  cases derivation with
  | notReducible live original expected bindings fuel =>
      obtain rfl := List.mem_singleton.mp member
      exact ⟨independentIncoming, .notReducible original expected independentIncoming, related⟩
  | stopped live original expected value bindings fuel stopped =>
      obtain rfl := List.mem_singleton.mp member
      exact ⟨independentIncoming, .stopped original expected value independentIncoming stopped, related⟩
  | evaluate live original expected value bindings fuel results accepted running child =>
      obtain ⟨output, evaluated, outputRelated⟩ := child.sound result member scope independentIncoming related
      exact ⟨output, .evaluate original expected value independentIncoming _ accepted running evaluated,
        outputRelated⟩
termination_by 2 * fuel + 1

end

/-- The historical record comparison recovers the former raw result interface.
The complete output frame is proved historical before its raw rows are exposed. -/
theorem AtomDerivation.sound_records {space : Space} {live : List Atom} {value expected : Atom}
    {incoming : Bindings} {fuel : Nat} {results : ResultSet}
    (derivation : AtomDerivation (comparison := .records) space live value expected incoming fuel results)
    (result : ResultPair) (member : result ∈ results) (scope : List String)
    (independentIncoming : Bindings) (related : BindingRecordPerm incoming independentIncoming) :
    ∃ independentOutput : Bindings,
      EvalAtomRawRel space noHost live (protectedScope := scope) value expected
        independentIncoming (result.1, independentOutput) ∧
      BindingRecordPerm result.2 independentOutput := by
  obtain ⟨output, evaluated, framed⟩ := derivation.sound result member scope
    independentIncoming (.records related)
  cases framed with
  | records relation => exact ⟨_, evaluated, relation⟩

theorem ArgsDerivation.sound_records {space : Space} {live : List Atom} {values types : List Atom}
    {incoming : Bindings} {fuel : Nat} {results : ArgumentResults}
    (derivation : ArgsDerivation (comparison := .records) space live values types incoming fuel results)
    (result : List Atom × Bindings) (member : result ∈ results)
    (independentIncoming : Bindings) (related : BindingRecordPerm incoming independentIncoming) :
    ∃ independentOutput : Bindings,
      InterpretArgsRel space noHost live values types independentIncoming
        (argumentPacket result.1, independentOutput) ∧
      BindingRecordPerm result.2 independentOutput := by
  obtain ⟨output, evaluated, framed⟩ := derivation.sound result member
    independentIncoming (.records related)
  cases framed with
  | records relation => exact ⟨_, evaluated, relation⟩

/-! ## Checked completion constructed from local source coverage -/

mutual
/-- Additional local service evidence for the existing source derivation.
The index is the original derivation; no execution or eventual-stability
statement is a constructor premise. Raw leaves have no bounded leaf calls. -/
 inductive AtomDerivation.Covered {space : Space} {comparison : SourceBindingComparison} : {live : List Atom} →
    {value expected : Atom} → {incoming : Bindings} → {fuel : Nat} →
    {results : ResultSet} → AtomDerivation (comparison := comparison) space live value expected incoming fuel results → Prop where
  | leaf {live value expected incoming fuel leaf} :
      AtomDerivation.Covered (@AtomDerivation.leaf space comparison live value expected incoming fuel leaf)
  | symbolCast {live name expected incoming fuel before after actual notEmpty notRaw notMeta
      types expectedClosed actualClosed earlierClosed earlierRejected fits enough}
      (covered : typeCastCovered (.symbol name) expected space incoming fuel = true) :
      AtomDerivation.Covered (@AtomDerivation.symbolCast space comparison live name expected incoming fuel before after actual
        notEmpty notRaw notMeta types expectedClosed actualClosed earlierClosed earlierRejected fits enough)
  | symbolRejected {live name expected incoming fuel notEmpty notRaw notMeta expectedClosed closed rejected}
      (covered : typeCastCovered (.symbol name) expected space incoming fuel = true) :
      AtomDerivation.Covered (@AtomDerivation.symbolRejected space comparison live name expected incoming fuel
        notEmpty notRaw notMeta expectedClosed closed rejected)
  | application {live name arguments expected incoming fuel typing rows outputs args calls}
      (selection : FirstSuccessRecursiveStrategy.selectionReady space
        (.expression (.symbol name :: arguments)) expected incoming (fuel + 1)
        (getAtomTypes space (.symbol name)) = true)
      (head : typeCastCovered (.symbol name) (arrow typing.domains typing.returned) space incoming
        (fuel - 1) = true)
      (argumentsCovered : ArgsDerivation.Covered args)
      (callsCovered : ∀ request member, CallDerivation.Covered (calls request member)) :
      AtomDerivation.Covered (@AtomDerivation.application space comparison live name arguments expected incoming fuel typing
        rows outputs args calls)
  | untypedTuple {live operator arguments expected incoming fuel rows outputs clean notRaw notExpr types tuple calls}
      (tupleCovered : TupleDerivation.Covered tuple)
      (callsCovered : ∀ request member, CallDerivation.Covered (calls request member)) :
      AtomDerivation.Covered (@AtomDerivation.untypedTuple space comparison live operator arguments
        expected incoming fuel rows outputs clean notRaw notExpr types tuple calls)
 inductive TupleDerivation.Covered {space : Space} {comparison : SourceBindingComparison} :
    {live : List Atom} → {value : Atom} → {incoming : Bindings} → {fuel : Nat} → {results : ResultSet} →
    TupleDerivation space comparison live value incoming fuel results → Prop where
  | nil {live incoming fuel} : TupleDerivation.Covered (@TupleDerivation.nil space comparison live incoming fuel)
  | singleton {live value incoming fuel heads child}
      (covered : AtomDerivation.Covered child) :
      TupleDerivation.Covered (@TupleDerivation.singleton space comparison live value incoming fuel heads child)
  | cons {live head second remaining incoming fuel heads tails first children}
      (headCovered : AtomDerivation.Covered first)
      (tailCovered : ∀ selected member clean, TupleDerivation.Covered (children selected member clean)) :
      TupleDerivation.Covered (@TupleDerivation.cons space comparison live head second remaining incoming
        fuel heads tails first children)
 inductive ArgsDerivation.Covered {space : Space} {comparison : SourceBindingComparison} : {live values types : List Atom} →
    {incoming : Bindings} → {fuel : Nat} → {results : ArgumentResults} →
    ArgsDerivation (comparison := comparison) space live values types incoming fuel results → Prop where
  | nil {live incoming fuel} : ArgsDerivation.Covered (@ArgsDerivation.nil space comparison live incoming fuel)
  | cons {live value expected values types incoming fuel heads tails head safe tail}
      (headCovered : AtomDerivation.Covered head)
      (tailCovered : ∀ selected member, ArgsDerivation.Covered (tail selected member)) :
      ArgsDerivation.Covered (@ArgsDerivation.cons space comparison live value expected values types incoming fuel
        heads tails head safe tail)
 inductive CallDerivation.Covered {space : Space} {comparison : SourceBindingComparison} : {live : List Atom} →
    {value expected : Atom} → {incoming : Bindings} → {fuel : Nat} → {results : ResultSet} →
    CallDerivation (comparison := comparison) space live value expected incoming fuel results → Prop where
  | errorPassthrough {live value expected incoming fuel error} :
      CallDerivation.Covered (@CallDerivation.errorPassthrough space comparison live value expected
        incoming fuel error)
  | embedded {live name arguments expected incoming fuel raw outputs semantic clean instruction child returns}
      (returnsCovered : ∀ result member, ReturnDerivation.Covered (returns result member)) :
      CallDerivation.Covered (@CallDerivation.embedded space comparison live name arguments expected incoming
        fuel raw outputs semantic clean instruction child returns)
  | unreduced {live name arguments expected incoming fuel ordinary nonembedded clean empty absent}
      (query : queryEquationsCovered
        (equationScope live (.expression (.symbol name :: arguments)) expected incoming)
        space (.expression (.symbol name :: arguments)) fuel = true) :
      CallDerivation.Covered (@CallDerivation.unreduced space comparison live name arguments expected incoming fuel
        ordinary nonembedded clean empty absent)
  | equations {live name arguments expected incoming fuel productions outputs ordinary nonembedded clean selected evidence producers bodies}
      (query : queryEquationsCovered
        (equationScope live (.expression (.symbol name :: arguments)) expected incoming)
        space (.expression (.symbol name :: arguments)) fuel = true)
      (inputs : ∀ candidate ∈ equationCandidates space live
          (.expression (.symbol name :: arguments)) expected incoming fuel,
        matchCovered fuel (.merge candidate.2 (aliasConstraints incoming)) = true ∧
        ∀ merged ∈ mergeBindings candidate.2 (aliasConstraints incoming) fuel, merged.hasLoop = false →
          merged.applyFullCovered candidate.1 fuel = true)
      (bodiesCovered : ∀ candidate member request present produced selected,
        ReturnDerivation.Covered (bodies candidate member request present produced selected)) :
      CallDerivation.Covered (@CallDerivation.equations space comparison live name arguments expected incoming fuel
        productions outputs ordinary nonembedded clean selected evidence producers bodies)

 inductive ReturnDerivation.Covered {space : Space} {comparison : SourceBindingComparison} : {live : List Atom} →
    {original expected value : Atom} → {bindings : Bindings} → {fuel : Nat} → {results : ResultSet} →
    ReturnDerivation (comparison := comparison) space live original expected value bindings fuel results → Prop where
  | notReducible {live original expected bindings fuel} :
      ReturnDerivation.Covered (@ReturnDerivation.notReducible space comparison live original expected bindings fuel)
  | stopped {live original expected value bindings fuel stopped} :
      ReturnDerivation.Covered (@ReturnDerivation.stopped space comparison live original expected value bindings fuel stopped)
  | evaluate {live original expected value bindings fuel results accepted running child}
      (covered : AtomDerivation.Covered child) :
      ReturnDerivation.Covered (@ReturnDerivation.evaluate space comparison live original expected value bindings fuel results
        accepted running child)

end

/-- Local coverage for the ordinary singleton-producer specialization. -/
theorem CallDerivation.Covered.ordinaryEquations {space : Space} {comparison : SourceBindingComparison}
    {live : List Atom} {name : String} {arguments : List Atom} {expected : Atom}
    {incoming : Bindings} {fuel : Nat} {outputs : ResultPair → ResultPair → ResultSet}
    {ordinary : name ≠ "unify" ∧ name ≠ "switch-minimal"}
    {nonembedded : Minimal.embeddedInstruction (.expression [.symbol name]) = false}
    {clean : name ≠ "Error"}
    {selected : rawQueryResults space (.expression (.symbol name :: arguments)) expected incoming fuel live ≠ []}
    {evidence : ∀ candidate ∈ equationCandidates space live (.expression (.symbol name :: arguments))
        expected incoming fuel, ∀ request ∈ equationInputs incoming fuel candidate,
      EquationBodyEvidence (comparison := comparison) space live (.expression (.symbol name :: arguments))
        expected incoming candidate request}
    {ordinaryBodies : ∀ candidate ∈ equationCandidates space live (.expression (.symbol name :: arguments))
        expected incoming fuel, ∀ request ∈ equationInputs incoming fuel candidate,
      ¬Spec.Eval.Minimal.IsFunction request.1}
    {bodies : ∀ candidate ∈ equationCandidates space live (.expression (.symbol name :: arguments))
        expected incoming fuel, ∀ request ∈ equationInputs incoming fuel candidate,
      ReturnDerivation (comparison := comparison) space live (.expression (.symbol name :: arguments))
        expected request.1 request.2 fuel (outputs candidate request)}
    (query : queryEquationsCovered
      (equationScope live (.expression (.symbol name :: arguments)) expected incoming)
      space (.expression (.symbol name :: arguments)) fuel = true)
    (inputs : ∀ candidate ∈ equationCandidates space live (.expression (.symbol name :: arguments))
        expected incoming fuel,
      matchCovered fuel (.merge candidate.2 (aliasConstraints incoming)) = true ∧
      ∀ merged ∈ mergeBindings candidate.2 (aliasConstraints incoming) fuel, merged.hasLoop = false →
        merged.applyFullCovered candidate.1 fuel = true)
    (covered : ∀ candidate member request present, (bodies candidate member request present).Covered) :
    (CallDerivation.ordinaryEquations live name arguments expected incoming fuel outputs
      ordinary nonembedded clean selected evidence ordinaryBodies bodies).Covered := by
  cases fuel with
  | zero => simp [rawQueryResults, queryEquationsAvoiding] at selected
  | succ fuel =>
      simpa only [List.flatMap_cons, List.flatMap_nil, List.append_nil] using
        (CallDerivation.Covered.equations (space := space) (comparison := comparison)
        (ordinary := ordinary) (nonembedded := nonembedded) (clean := clean)
        (selected := selected) (evidence := evidence)
        (productions := fun _ request => [request])
        (outputs := fun candidate request _ => outputs candidate request)
        (producers := fun candidate member request present =>
        .raw _ _ _ _ fuel (ordinaryBodies candidate member request present))
        (bodies := by
          intro candidate member request present produced appeared
          have same := List.mem_singleton.mp appeared
          subst produced
          exact bodies candidate member request present)
        query inputs (by
          intro candidate member request present produced appeared
          have same := List.mem_singleton.mp appeared
          subst produced
          exact covered candidate member request present))

mutual
/-- Local bounded-service checks turn the source derivation into an actual
covered path under every retained caller and established publication. -/
theorem AtomDerivation.covered_realizes {space : Space} {comparison : SourceBindingComparison} {live : List Atom}
    {value expected : Atom} {incoming : Bindings} {fuel : Nat} {results : ResultSet}
    (derivation : AtomDerivation (comparison := comparison) space live value expected incoming fuel results)
    (covered : derivation.Covered) :
    Covered.Realizes space (.atom value expected incoming fuel live) results := by
  cases covered with
  | @leaf live value expected incoming fuel leaf =>
      exact Covered.retained_leaf space value expected incoming fuel live leaf
  | @symbolCast live name expected incoming fuel before after actual notEmpty notRaw notMeta
      types expectedClosed actualClosed earlierClosed earlierRejected fits enough ready =>
      exact Covered.symbol_cast_realizes space name expected incoming fuel before after actual
        notEmpty types expectedClosed actualClosed earlierClosed earlierRejected fits enough live ready
  | @symbolRejected live name expected incoming fuel notEmpty notRaw notMeta expectedClosed
      closed rejected ready =>
      exact Covered.symbol_rejection_realizes space name expected incoming fuel live
        notEmpty notRaw notMeta expectedClosed closed rejected ready
  | @application live name arguments expected incoming fuel typing rows outputs args calls
      selection head argumentsCovered callsCovered =>
      apply Covered.application_retained_realizes typing incoming rows _ live selection head
      · exact args.covered_realizes argumentsCovered
      · apply Covered.calls_realizes_map
        intro request member
        exact (calls request member).covered_realizes (callsCovered request member)
  | @untypedTuple live operator arguments expected incoming fuel rows outputs clean notRaw notExpr
      types tuple calls tupleCovered callsCovered =>
      apply Covered.untyped_tuple_realizes space operator arguments expected incoming fuel live rows _
        clean notRaw notExpr types (tuple.covered_realizes tupleCovered)
      exact Covered.calls_realizes_map space expected (fuel + 1) live rows outputs
        (fun request member => (calls request member).covered_realizes (callsCovered request member))
termination_by 2 * fuel

/-- Local child coverage suffices for the existing tuple task and receivers;
stopped heads introduce no obligation to execute their abandoned tails. -/
theorem TupleDerivation.covered_realizes {space : Space} {comparison : SourceBindingComparison}
    {live : List Atom} {value : Atom} {incoming : Bindings} {fuel : Nat} {results : ResultSet}
    (derivation : TupleDerivation space comparison live value incoming fuel results)
    (covered : derivation.Covered) : Covered.Realizes space (.tuple value incoming fuel live) results := by
  cases covered with
  | @nil live incoming fuel =>
      intro stack emitted
      simpa only [FirstSuccessRecursiveStrategy.enter, RecursiveMachine.enter, Atom.unit,
        List.nil_append] using Covered.enter_request space
          (.tuple Atom.unit incoming (fuel + 1) live) stack emitted
  | @singleton live value incoming fuel heads child childCovered =>
      exact Covered.tuple_singleton_realizes space value incoming fuel live heads
        (child.covered_realizes childCovered)
  | @cons live head second remaining incoming fuel heads tails first children headCovered tailCovered =>
      exact Covered.tuple_cons_realizes space head second remaining incoming fuel live heads tails
        (first.covered_realizes headCovered) (fun selected member clean =>
          (children selected member clean).covered_realizes (tailCovered selected member clean))
termination_by 2 * fuel

theorem ArgsDerivation.covered_realizes {space : Space} {comparison : SourceBindingComparison} {live values types : List Atom}
    {incoming : Bindings} {fuel : Nat} {results : ArgumentResults}
    (derivation : ArgsDerivation (comparison := comparison) space live values types incoming fuel results)
    (covered : derivation.Covered) :
    Covered.Realizes space (.args values types incoming fuel live) (argumentReplies results) := by
  cases covered with
  | @nil live incoming fuel =>
      intro stack emitted
      simpa [FirstSuccessRecursiveStrategy.enter, RecursiveMachine.enter, argumentReplies] using
        Covered.enter_request space (.args [] [] incoming (fuel + 1) live) stack emitted
  | @cons live value expected values types incoming fuel heads tails head safe tail
      headCovered tailCovered =>
      have branches : List.Forall₂ (fun selected output => ∃ rests,
          Covered.Realizes space (.args values types selected.2 fuel (selected.1 :: live)) rests ∧
            output = RecursiveTasks.argumentTail selected.1 rests)
          heads (heads.map fun selected =>
            RecursiveTasks.argumentTail selected.1 (argumentReplies (tails selected))) := by
        apply List.forall₂_map_right_iff.mpr
        apply List.forall₂_same.mpr
        intro selected member
        exact ⟨argumentReplies (tails selected),
          (tail selected member).covered_realizes (tailCovered selected member), rfl⟩
      have path := Covered.arguments_cons_with_branches_realizes space value expected values types incoming
        fuel live (head.covered_realizes headCovered) safe branches
      simpa [argumentReplies, RecursiveTasks.argumentTail, List.map_map, List.map_flatMap,
        Function.comp_def, argumentValues_packet, argumentsSucceeded_packet,
        ← List.flatMap_def] using path
termination_by 2 * fuel

theorem CallDerivation.covered_realizes {space : Space} {comparison : SourceBindingComparison} {live : List Atom}
    {query expected : Atom} {incoming : Bindings} {fuel : Nat} {results : ResultSet}
    (derivation : CallDerivation (comparison := comparison) space live query expected incoming fuel results)
    (covered : derivation.Covered) :
    Covered.Realizes space (.call query expected incoming fuel live) results := by
  cases covered with
  | @errorPassthrough live value expected incoming fuel error =>
      exact Covered.error_call_realizes space _ expected incoming fuel live error
  | @unreduced live name arguments expected incoming fuel _ nonembedded clean empty _ ready =>
      exact Covered.call_empty_realizes space name arguments expected incoming fuel live
        nonembedded clean ready empty
  | @equations live name arguments expected incoming fuel productions outputs _ nonembedded clean selected evidence
      producers bodies queryCovered inputs bodiesCovered =>
      apply Covered.call_query_realizes space name arguments expected incoming fuel live nonembedded clean
        _ queryCovered inputs
      apply Covered.producer_results_realizes space _ _ incoming fuel live _ _ _ selected
      · exact Covered.equation_productions_realizes space incoming fuel
          (expected :: live) (some (.expression (.symbol name :: arguments))) _ productions
          (fun candidate member request present =>
            (producers candidate member request present).covered_realizes)
      · apply Covered.equation_produced_returns_realizes
        intro candidate member request present produced selected
        exact (bodies candidate member request present produced selected).covered_realizes
          (bodiesCovered candidate member request present produced selected)

  | @embedded live name arguments expected incoming fuel raw outputs semantic clean instruction child returns ready =>
      cases semantic
      apply Covered.ordinary_embedded_realizes space name arguments expected incoming fuel live raw _
        clean instruction child.covered_realizes
      have paths : List.Forall₂ (fun request output =>
          Covered.Realizes space (.returned (.expression (.symbol name :: arguments)) request.1 expected
            request.2 fuel live) output) raw (raw.map outputs) :=
        List.forall₂_map_right_iff.mpr (List.forall₂_same.mpr (fun result member =>
          (returns result member).covered_realizes (ready result member)))
      simpa only [← List.flatMap_def] using Covered.returns_realizes space
        (.expression (.symbol name :: arguments)) expected fuel live paths

termination_by 2 * fuel

theorem ReturnDerivation.covered_realizes {space : Space} {comparison : SourceBindingComparison} {live : List Atom}
    {original expected value : Atom} {bindings : Bindings} {fuel : Nat} {results : ResultSet}
    (derivation : ReturnDerivation (comparison := comparison) space live original expected value bindings fuel results)
    (covered : derivation.Covered) :
    Covered.Realizes space (.returned original value expected bindings fuel live) results := by
  cases covered with
  | @notReducible live original expected bindings fuel =>
      exact Covered.returned_notReducible_realizes space original expected bindings fuel live
  | @stopped live original expected value bindings fuel stopped =>
      exact Covered.returned_stopped_realizes space original value expected bindings fuel live
        ((Conformance.isEmptyOrErrorRel_iff_isEmptyOrError value).mp stopped)
  | @evaluate live original expected value bindings fuel results accepted running child ready =>
      exact Covered.returned_evaluate_realizes space original value expected bindings fuel live results
        accepted (by simpa [Conformance.isEmptyOrErrorRel_iff_isEmptyOrError] using running)
        (child.covered_realizes ready)
termination_by 2 * fuel + 1

end


namespace Covered
theorem drain_returning (space : Space) (results emitted : ResultSet) (later : Nat) :
    (Checked.machine HE.GroundedDispatch.none).run (results.length + 1 + later)
      ⟨space, .returning results, [], emitted⟩ =
      (results, .finished ⟨space, .returning [], [], emitted ++ results⟩) := by
  exact (checkedOutput space HE.GroundedDispatch.none rawTypes).drain results emitted later

/-- A constructed finite task path earns completion with all changed binding
frames and occurrences intact. This law does not require an equation-free
space; nontermination is excluded only for the supplied finite realization. -/
theorem realizes_completed {space : Space} {task : Task} {results : ResultSet}
    (realized : Realizes space task results) (earned : ResultSet) :
    ∃ budget, ∀ later, (Checked.machine HE.GroundedDispatch.none).run (budget + later)
      ⟨space, .work task, [], earned⟩ =
      (results, .finished ⟨space, .returning [], [], earned ++ results⟩) := by
  exact (checkedOutput space HE.GroundedDispatch.none rawTypes).complete (realized [] earned)

/-- A scheduler pause retains enough work to finish using the bound already
constructed from the source proof. No completed suffix is assumed. -/
theorem completes_saved {space : Space} {task : Task} {results : ResultSet}
    (realized : Realizes space task results) (earned : ResultSet)
    (first : Nat) (before : ResultSet) (saved : Configuration)
    (paused : (Checked.machine HE.GroundedDispatch.none).run first
      ⟨space, .work task, [], earned⟩ = (before, .exhausted saved)) :
    ∃ budget after,
      (Checked.machine HE.GroundedDispatch.none).run budget saved =
        (after, .finished ⟨space, .returning [], [], earned ++ results⟩) ∧
      before ++ after = results := by
  obtain ⟨budget, complete⟩ := realizes_completed realized earned
  obtain ⟨after, resumed, events⟩ := Machine.finished_suffix paused complete
  exact ⟨budget, after, resumed, events⟩

end Covered

/-- Finite source evidence plus local leaf coverage constructs a completed
checked execution. Its scheduler bound is earned by the source derivation. -/
theorem AtomDerivation.checked_completed {space : Space} {comparison : SourceBindingComparison} {live : List Atom}
    {value expected : Atom} {incoming : Bindings} {fuel : Nat} {results : ResultSet}
    (derivation : AtomDerivation (comparison := comparison) space live value expected incoming fuel results)
    (covered : derivation.Covered) (earned : ResultSet) :
    ∃ budget, ∀ later, (Checked.machine HE.GroundedDispatch.none).run (budget + later)
      ⟨space, .work (.atom value expected incoming fuel live), [], earned⟩ =
      (results, .finished ⟨space, .returning [], [], earned ++ results⟩) :=
  Covered.realizes_completed (derivation.covered_realizes covered) earned

theorem ArgsDerivation.checked_completed {space : Space} {comparison : SourceBindingComparison} {live values types : List Atom}
    {incoming : Bindings} {fuel : Nat} {results : ArgumentResults}
    (derivation : ArgsDerivation (comparison := comparison) space live values types incoming fuel results)
    (covered : derivation.Covered) (earned : ResultSet) :
    ∃ budget, ∀ later, (Checked.machine HE.GroundedDispatch.none).run (budget + later)
      ⟨space, .work (.args values types incoming fuel live), [], earned⟩ =
      (argumentReplies results,
        .finished ⟨space, .returning [], [], earned ++ argumentReplies results⟩) :=
  Covered.realizes_completed (derivation.covered_realizes covered) earned

theorem CallDerivation.checked_completed {space : Space} {comparison : SourceBindingComparison} {live : List Atom}
    {value expected : Atom} {incoming : Bindings} {fuel : Nat} {results : ResultSet}
    (derivation : CallDerivation (comparison := comparison) space live value expected incoming fuel results)
    (covered : derivation.Covered) (earned : ResultSet) :
    ∃ budget, ∀ later, (Checked.machine HE.GroundedDispatch.none).run (budget + later)
      ⟨space, .work (.call value expected incoming fuel live), [], earned⟩ =
      (results, .finished ⟨space, .returning [], [], earned ++ results⟩) :=
  Covered.realizes_completed (derivation.covered_realizes covered) earned

theorem ReturnDerivation.checked_completed {space : Space} {comparison : SourceBindingComparison} {live : List Atom}
    {original expected value : Atom} {bindings : Bindings} {fuel : Nat} {results : ResultSet}
    (derivation : ReturnDerivation (comparison := comparison) space live original expected value bindings fuel results)
    (covered : derivation.Covered) (earned : ResultSet) :
    ∃ budget, ∀ later, (Checked.machine HE.GroundedDispatch.none).run (budget + later)
      ⟨space, .work (.returned original value expected bindings fuel live), [], earned⟩ =
      (results, .finished ⟨space, .returning [], [], earned ++ results⟩) :=
  Covered.realizes_completed (derivation.covered_realizes covered) earned

/-- Actual pauses of an admitted source computation complete from their
saved continuation, preserving every already emitted occurrence. -/
theorem AtomDerivation.checked_resume_completed {space : Space} {comparison : SourceBindingComparison} {live : List Atom}
    {value expected : Atom} {incoming : Bindings} {fuel : Nat} {results : ResultSet}
    (derivation : AtomDerivation (comparison := comparison) space live value expected incoming fuel results)
    (covered : derivation.Covered) (earned : ResultSet)
    (first : Nat) (before : ResultSet) (saved : Configuration)
    (paused : (Checked.machine HE.GroundedDispatch.none).run first
      ⟨space, .work (.atom value expected incoming fuel live), [], earned⟩ =
        (before, .exhausted saved)) :
    ∃ budget after,
      (Checked.machine HE.GroundedDispatch.none).run budget saved =
        (after, .finished ⟨space, .returning [], [], earned ++ results⟩) ∧
      before ++ after = results :=
  Covered.completes_saved (derivation.covered_realizes covered) earned first before saved paused


/-- The same admitted source evidence constructs both a completed checked run
and the independent source judgment for every returned occurrence. -/
theorem AtomDerivation.checked_completion_and_source {space : Space} {live : List Atom}
    {value expected : Atom} {incoming : Bindings} {fuel : Nat} {results : ResultSet}
    (derivation : AtomDerivation (comparison := .records) space live value expected incoming fuel results)
    (covered : derivation.Covered) (earned : ResultSet) :
    (∃ budget, ∀ later, (Checked.machine HE.GroundedDispatch.none).run (budget + later)
      ⟨space, .work (.atom value expected incoming fuel live), [], earned⟩ =
      (results, .finished ⟨space, .returning [], [], earned ++ results⟩)) ∧
    ∀ result ∈ results, ∃ output : Bindings,
      EvalAtomRawRel space noHost live value expected incoming (result.1, output) ∧
      BindingRecordPerm result.2 output := by
  refine ⟨derivation.checked_completed covered earned, ?_⟩
  intro result member
  exact derivation.sound_records result member [] incoming (.refl _)

private abbrev AtomLaw (space : Space) (bindings : Bindings) (value expected : Atom)
    (fuel : Nat) (heads : List Atom) : Prop :=
  (∀ live, Realizes space (.atom value expected bindings fuel live) (replies bindings heads)) ∧
    (∀ head ∈ heads, ∀ (live : List Atom) (scope : List String), EvalAtomRawRel space noHost live
      (protectedScope := scope) value expected bindings (head, bindings)) ∧
    (∀ head ∈ heads, head = value ∨ isEmptyOrError head = false)

private abbrev ArgsLaw (space : Space) (bindings : Bindings) (values types : List Atom)
    (fuel : Nat) (results : List (List Atom)) : Prop :=
  (∀ live, Realizes space (.args values types bindings fuel live) (packets bindings results)) ∧
    ∀ result ∈ results, ∀ live scope, InterpretArgsRel space noHost live (protectedScope := scope)
      values types bindings (argumentPacket result, bindings)

private theorem leaf_law (space : Space) (bindings : Bindings) (value expected : Atom)
    (fuel : Nat) (leaf : LeafRel value expected) :
    AtomLaw space bindings value expected (fuel + 1) [value] := by
  refine ⟨?_, ?_, ?_⟩
  · intro live
    simpa only [replies, List.map_cons, List.map_nil] using
      retained_leaf space HE.GroundedDispatch.none value expected bindings fuel leaf live
  · intro head member live scope
    have same := List.mem_singleton.mp member
    subst head
    exact leaf_evidence space noHost live storageTypeService scope value expected bindings leaf
  · intro head member
    exact Or.inl (List.mem_singleton.mp member)

private theorem cast_law (space : Space) (bindings : Bindings) (name : String)
    (expected : Atom) (fuel : Nat) (before after : List Atom) (actual : Atom)
    (notEmpty : name ≠ "Empty") (notRaw : expected ≠ Atom.atomType) (notMeta : expected ≠ Atom.symbolType)
    (types : getAtomTypes space (.symbol name) = before ++ actual :: after)
    (expectedClosed : TypeSubst.typeVars expected = []) (actualClosed : TypeSubst.typeVars actual = [])
    (earlierClosed : ∀ candidate ∈ before, TypeSubst.typeVars candidate = [])
    (earlierRejects : ∀ candidate ∈ before, ¬ClosedTypeFits expected candidate)
    (fits : ClosedTypeFits expected actual) (enough : sizeOf expected + sizeOf actual + 2 ≤ fuel) :
    AtomLaw space bindings (.symbol name) expected (fuel + 1) [.symbol name] := by
  refine ⟨?_, ?_, ?_⟩
  · intro live
    simpa only [replies, List.map_cons, List.map_nil] using
      symbol_cast_realizes space name expected bindings fuel before after actual notEmpty types
        expectedClosed actualClosed earlierClosed earlierRejects fits enough live
  · intro head member live scope
    obtain rfl := List.mem_singleton.mp member
    exact symbol_cast_spec space name expected bindings fuel before after actual notEmpty notRaw notMeta types
      expectedClosed actualClosed earlierClosed earlierRejects fits enough live scope
  · intro head member
    exact Or.inl (List.mem_singleton.mp member)

private theorem application_law (space : Space) (free : EquationFree space) (bindings : Bindings)
    (name : String) (arguments : List Atom) (expected : Atom) (fuel : Nat)
    (typing : ApplicationTyping space name arguments expected fuel) (values : List (List Atom))
    (nonembedded : Spec.Eval.Minimal.embeddedInstruction (.expression [.symbol name]) = false)
    (tail : ArgsLaw space bindings arguments typing.domains fuel values) :
    AtomLaw space bindings (.expression (.symbol name :: arguments)) expected (fuel + 3)
      (values.map fun packet => .expression (.symbol name :: packet)) := by
  refine ⟨fun live => application_realizes typing nonembedded free bindings values live tail.1, ?_, ?_⟩
  · intro result member live scope
    obtain ⟨packet, packetMember, rfl⟩ := List.mem_map.mp member
    exact application_spec typing nonembedded free bindings packet live scope (tail.2 packet packetMember _ scope)
  · intro result member
    obtain ⟨packet, _, rfl⟩ := List.mem_map.mp member
    exact Or.inr (clean_application name packet typing.cleanOperator).2

private theorem arguments_nil_law (space : Space) (bindings : Bindings) (fuel : Nat) :
    ArgsLaw space bindings [] [] (fuel + 1) [[]] := by
  refine ⟨?_, ?_⟩
  · intro live stack emitted
    simpa [FirstSuccessRecursiveStrategy.enter, RecursiveMachine.enter, packets, replies] using
      enter_request space HE.GroundedDispatch.none (.args [] [] bindings (fuel + 1) live) stack emitted
  · intro result member live scope
    obtain rfl := List.mem_singleton.mp member
    exact .nil bindings

private theorem arguments_cons_law (space : Space) (bindings : Bindings) (value expected : Atom)
    (values types : List Atom) (fuel : Nat) (heads : List Atom) (tails : List (List Atom))
    (headLaw : AtomLaw space bindings value expected fuel heads)
    (tailLaw : ArgsLaw space bindings values types fuel tails) :
    ArgsLaw space bindings (value :: values) (expected :: types) (fuel + 1)
      (heads.flatMap fun head => tails.map fun tail => head :: tail) := by
  refine ⟨?_, ?_⟩
  · intro live stack emitted
    have begin := enter_request space HE.GroundedDispatch.none
      (.args (value :: values) (expected :: types) bindings (fuel + 1) live) stack emitted
    have head := headLaw.1 (values ++ types ++ live) (.argumentHeads value values types fuel live :: stack)
      emitted
    have transfer := consume_continuation space HE.GroundedDispatch.none
      (.argumentHeads value values types fuel live) (replies bindings heads) stack emitted
    have tail := argument_heads space value values types bindings fuel live heads tails headLaw.2.2
      tailLaw.1 stack emitted
    have combined := head.trans (transfer.trans (by
      simpa only [RecursiveMachine.resume, List.nil_append] using tail))
    exact begin.trans (by
      simpa only [FirstSuccessRecursiveStrategy.enter, RecursiveMachine.enter,
        List.cons_append, List.nil_append] using combined)
  · intro result member live scope
    obtain ⟨head, headMember, resultMember⟩ := List.mem_flatMap.mp member
    obtain ⟨tail, tailMember, rfl⟩ := List.mem_map.mp resultMember
    have safe : ¬IsEmptyOrErrorRel head ∨ head = value := by
      rcases headLaw.2.2 head headMember with equal | clean
      · exact Or.inr equal
      · exact Or.inl (by
          intro error
          have failed := (Spec.Type.Conformance.isEmptyOrErrorRel_iff_isEmptyOrError head).mp error
          simp [clean] at failed)
    simpa only [argumentValues_packet] using InterpretArgsRel.success value values expected types bindings
      (head, bindings) (argumentPacket tail, bindings) (headLaw.2.1 head headMember _ scope) safe
      (tailLaw.2 tail tailMember _ scope) ⟨tail, rfl⟩

private theorem atom_law {space : Space} (free : EquationFree space) {bindings : Bindings}
    {value expected : Atom} {fuel : Nat} {heads : List Atom}
    (derivation : ReadOnlyAtomDerivation space bindings value expected fuel heads) :
    AtomLaw space bindings value expected fuel heads := by
  exact ReadOnlyAtomDerivation.rec
    (motive_1 := fun value expected fuel heads _ => AtomLaw space bindings value expected fuel heads)
    (motive_2 := fun values types fuel results _ => ArgsLaw space bindings values types fuel results)
    (leaf_law space bindings) (cast_law space bindings)
    (fun name arguments expected fuel typing values _ordinary nonembedded _ tail =>
      application_law space free bindings name arguments expected fuel typing values nonembedded tail)
    (arguments_nil_law space bindings)
    (fun value expected values types fuel heads tails _ _ headLaw tailLaw =>
      arguments_cons_law space bindings value expected values types fuel heads tails headLaw tailLaw) derivation

private theorem args_law {space : Space} (free : EquationFree space) {bindings : Bindings}
    {values types : List Atom} {fuel : Nat} {results : List (List Atom)}
    (derivation : ReadOnlyArgsDerivation space bindings values types fuel results) :
    ArgsLaw space bindings values types fuel results := by
  exact ReadOnlyArgsDerivation.rec
    (motive_1 := fun value expected fuel heads _ => AtomLaw space bindings value expected fuel heads)
    (motive_2 := fun values types fuel results _ => ArgsLaw space bindings values types fuel results)
    (leaf_law space bindings) (cast_law space bindings)
    (fun name arguments expected fuel typing values _ordinary nonembedded _ tail =>
      application_law space free bindings name arguments expected fuel typing values nonembedded tail)
    (arguments_nil_law space bindings)
    (fun value expected values types fuel heads tails _ _ headLaw tailLaw =>
      arguments_cons_law space bindings value expected values types fuel heads tails headLaw tailLaw) derivation

mutual
/-- The earlier equation-free derivation is a genuine specialization of the
scoped recursive family, with unchanged bindings at every endpoint. -/
theorem ReadOnlyAtomDerivation.toScoped {space : Space} (free : EquationFree space)
    {incoming : Bindings} {value expected : Atom} {fuel : Nat} {results : List Atom}
    (derivation : ReadOnlyAtomDerivation space incoming value expected fuel results)
    (live : List Atom) :
    AtomDerivation (comparison := .records) space live value expected incoming fuel (replies incoming results) := by
  cases derivation with
  | leaf value expected fuel leaf =>
      exact .leaf live value expected incoming fuel leaf
  | symbolCast name expected fuel before after actual notEmpty notRaw notMeta types
      expectedClosed actualClosed earlierClosed earlierRejects fits enough =>
      exact .symbolCast live name expected incoming fuel before after actual notEmpty notRaw notMeta
        types expectedClosed actualClosed earlierClosed earlierRejects fits enough
  | application name arguments expected fuel typing values ordinary nonembedded argumentsDerivation =>
      have args := argumentsDerivation.toScoped free
        (.symbol name ::
          (if typing.returned = Atom.expressionType then Atom.undefinedType else typing.returned) :: live)
      have calls : ∀ request ∈ applications name (values.map fun packet => (packet, incoming)),
          CallDerivation (comparison := .records) space live request.1
            (if typing.returned = Atom.expressionType then Atom.undefinedType else typing.returned)
            request.2 (fuel + 1) [request] := by
        intro request member
        obtain ⟨row, present, rfl⟩ := List.mem_map.mp member
        obtain ⟨packet, _, rfl⟩ := List.mem_map.mp present
        exact .unreduced live name packet _ incoming fuel ordinary nonembedded typing.cleanOperator
          (no_scoped_source_equations space free _ _ _) (no_independent_equations space free _ _ _)
      have constructed := AtomDerivation.application live name arguments expected incoming fuel typing
        (values.map fun packet => (packet, incoming)) (fun request => [request]) args calls
      have clean : ∀ value ∈ (values.map fun packet => Atom.expression (.symbol name :: packet)),
          isErrorAtom value = false := by
        intro result member
        obtain ⟨packet, _, rfl⟩ := List.mem_map.mp member
        simp [isErrorAtom, typing.cleanOperator]
      have equal : successPriority (((applications name (values.map fun packet => (packet, incoming))).flatMap
            (fun request => [request]))) =
          replies incoming ((values.map fun packet => .expression (.symbol name :: packet))) := by
        rw [List.flatMap_singleton']
        have mapped : ((applications name (values.map fun packet => (packet, incoming)))) =
            replies incoming ((values.map fun packet => .expression (.symbol name :: packet))) := by
          simp [applications, replies, List.map_map, Function.comp_def]
        rw [mapped]
        exact success_priority_clean incoming _ clean
      exact equal ▸ constructed
termination_by fuel

/-- Read-only argument rows embed with the same physical multiplicity and
scope; the general argument machine owns no extra restoration operation. -/
theorem ReadOnlyArgsDerivation.toScoped {space : Space} (free : EquationFree space)
    {incoming : Bindings} {values types : List Atom} {fuel : Nat} {results : List (List Atom)}
    (derivation : ReadOnlyArgsDerivation space incoming values types fuel results)
    (live : List Atom) :
    ArgsDerivation (comparison := .records) space live values types incoming fuel
      (results.map fun result => (result, incoming)) := by
  cases derivation with
  | nil fuel => exact .nil live incoming fuel
  | cons value expected values types fuel heads tails head tail =>
      have headRun := head.toScoped free (values ++ types ++ live)
      have tailRun : ∀ selected ∈ replies incoming heads,
          ArgsDerivation (comparison := .records) space (selected.1 :: live) values types selected.2 fuel
            (tails.map fun result => (result, incoming)) := by
        intro selected member
        obtain ⟨value, _, rfl⟩ := List.mem_map.mp member
        exact tail.toScoped free (value :: live)
      have safe : ∀ selected ∈ replies incoming heads,
          selected.1 = value ∨ isEmptyOrError selected.1 = false := by
        intro selected member
        obtain ⟨headValue, present, rfl⟩ := List.mem_map.mp member
        exact (atom_law free head).2.2 headValue present
      have constructed := ArgsDerivation.cons live value expected values types incoming fuel
        (replies incoming heads) (fun _ => tails.map fun result => (result, incoming))
        headRun safe tailRun
      simpa [replies, List.flatMap_map, List.map_flatMap, List.map_map, Function.comp_def] using constructed
termination_by fuel
end

/-- Every admitted recursive source derivation realizes its full ordered
reply under arbitrary retained caller continuations and prior observations. -/
theorem ReadOnlyAtomDerivation.realizes {space : Space} (free : EquationFree space) {bindings : Bindings}
    {value expected : Atom} {fuel : Nat} {heads : List Atom}
    (derivation : ReadOnlyAtomDerivation space bindings value expected fuel heads) :
    Realizes space (.atom value expected bindings fuel) (replies bindings heads) :=
  (derivation.toScoped free []).realizes

/-- Each occurrence in the constructed ordered reply is earned by the
independent, fuel-free first-success evaluator rules. -/
theorem ReadOnlyAtomDerivation.sound {space : Space} (free : EquationFree space) {bindings : Bindings}
    {value expected : Atom} {fuel : Nat} {heads : List Atom}
    (derivation : ReadOnlyAtomDerivation space bindings value expected fuel heads)
    (head : Atom) (member : head ∈ heads) (scope : List String) :
    EvalAtomRawRel space noHost [] (protectedScope := scope) value expected bindings (head, bindings) :=
  (atom_law free derivation).2.1 head member [] scope

theorem ReadOnlyArgsDerivation.realizes {space : Space} (free : EquationFree space) {bindings : Bindings}
    {values types : List Atom} {fuel : Nat} {results : List (List Atom)}
    (derivation : ReadOnlyArgsDerivation space bindings values types fuel results) :
    Realizes space (.args values types bindings fuel) (packets bindings results) :=
  by simpa [argumentReplies, packets, replies, List.map_map, Function.comp_def] using
    (derivation.toScoped free []).realizes

theorem ReadOnlyArgsDerivation.sound {space : Space} (free : EquationFree space) {bindings : Bindings}
    {values types : List Atom} {fuel : Nat} {results : List (List Atom)}
    (derivation : ReadOnlyArgsDerivation space bindings values types fuel results)
    (result : List Atom) (member : result ∈ results) :
    InterpretArgsRel space noHost [] values types bindings (argumentPacket result, bindings) :=
  (args_law free derivation).2 result member [] []


/-- The existing worker drains every ordered occurrence and retains the
whole history; padding the budget after completion produces no new results. -/
theorem drain_returning (space : Space) (results emitted : ResultSet) (later : Nat) :
    (machine HE.GroundedDispatch.none).run (results.length + 1 + later)
      ⟨space, .returning results, [], emitted⟩ =
      (results, .finished ⟨space, .returning [], [], emitted ++ results⟩) := by
  exact (rawOutput space HE.GroundedDispatch.none rawTypes).drain results emitted later

/-- A constructed finite task path earns completion with all changed binding
frames and occurrences intact. This law does not require an equation-free
space; nontermination is excluded only for the supplied finite realization. -/
theorem realizes_completed {space : Space} {task : Task} {results : ResultSet}
    (realized : Realizes space task results) (earned : ResultSet) :
    ∃ budget, ∀ later, (machine HE.GroundedDispatch.none).run (budget + later)
      ⟨space, .work task, [], earned⟩ =
      (results, .finished ⟨space, .returning [], [], earned ++ results⟩) := by
  exact (rawOutput space HE.GroundedDispatch.none rawTypes).complete (realized [] earned)

/-- Every admitted recursive source derivation completes with its actual
binding-changing result occurrences and retained publication history. -/
theorem AtomDerivation.completed {space : Space} {comparison : SourceBindingComparison} {live : List Atom} {bindings : Bindings}
    {value expected : Atom} {fuel : Nat} {results : ResultSet}
    (derivation : AtomDerivation (comparison := comparison) space live value expected bindings fuel results) (earned : ResultSet) :
    ∃ budget, ∀ later, (machine HE.GroundedDispatch.none).run (budget + later)
      ⟨space, .work (.atom value expected bindings fuel live), [], earned⟩ =
      (results, .finished ⟨space, .returning [], [], earned ++ results⟩) :=
  realizes_completed derivation.realizes earned

/-- Completion is derived from the actual source continuations. The bound
is per derivation; it is not a uniform latency claim for arbitrary programs. -/
theorem ReadOnlyAtomDerivation.completed {space : Space} (free : EquationFree space) {bindings : Bindings}
    {value expected : Atom} {fuel : Nat} {heads : List Atom}
    (derivation : ReadOnlyAtomDerivation space bindings value expected fuel heads) (earned : ResultSet) :
    ∃ budget, ∀ later, (machine HE.GroundedDispatch.none).run (budget + later)
      ⟨space, .work (.atom value expected bindings fuel), [], earned⟩ =
      (replies bindings heads, .finished
        ⟨space, .returning [], [], earned ++ replies bindings heads⟩) :=
  (derivation.toScoped free []).completed earned

/-- Representation transports a constructed task realization, including its
full final binding states, rather than recomputing only a value observer. -/
theorem realizes_encoded_completed {space : Space} {task : Task} {results : ResultSet}
    (realized : Realizes space task results) (earned : ResultSet) :
    ∃ budget, ∀ later, (dataMachine HE.GroundedDispatch.none).run (budget + later)
      (RecursiveEncoding.configurationData ⟨space, .work task, [], earned⟩) =
      (results, .finished ⟨space, .returning [], [], earned ++ results⟩) := by
  obtain ⟨budget, complete⟩ := realizes_completed realized earned
  refine ⟨budget, fun later => ?_⟩
  rw [run_representation, complete later]
  rfl

/-- Source completion survives the existing configuration representation,
including live scope and every changed binding frame. -/
theorem AtomDerivation.encoded_completed {space : Space} {comparison : SourceBindingComparison} {live : List Atom} {bindings : Bindings}
    {value expected : Atom} {fuel : Nat} {results : ResultSet}
    (derivation : AtomDerivation (comparison := comparison) space live value expected bindings fuel results) (earned : ResultSet) :
    ∃ budget, ∀ later, (dataMachine HE.GroundedDispatch.none).run (budget + later)
      (RecursiveEncoding.configurationData
        ⟨space, .work (.atom value expected bindings fuel live), [], earned⟩) =
      (results, .finished ⟨space, .returning [], [], earned ++ results⟩) :=
  realizes_encoded_completed derivation.realizes earned

theorem ReadOnlyAtomDerivation.encoded_completed {space : Space} (free : EquationFree space) {bindings : Bindings}
    {value expected : Atom} {fuel : Nat} {heads : List Atom}
    (derivation : ReadOnlyAtomDerivation space bindings value expected fuel heads) (earned : ResultSet) :
    ∃ budget, ∀ later, (dataMachine HE.GroundedDispatch.none).run (budget + later)
      (RecursiveEncoding.configurationData
        ⟨space, .work (.atom value expected bindings fuel), [], earned⟩) =
      (replies bindings heads, .finished
        ⟨space, .returning [], [], earned ++ replies bindings heads⟩) :=
  (derivation.toScoped free []).encoded_completed earned

/-- Once a realized task finishes, every finished run has its complete
occurrence list and accumulated history. -/
theorem realizes_completed_unique {space : Space} {task : Task} {results : ResultSet}
    (realized : Realizes space task results)
    (earned actual : ResultSet) (budget : Nat) (finished : RecursiveTasks.Configuration)
    (ran : (machine HE.GroundedDispatch.none).run budget
      ⟨space, .work task, [], earned⟩ = (actual, .finished finished)) :
    actual = results ∧ finished = ⟨space, .returning [], [], earned ++ results⟩ := by
  obtain ⟨_, complete⟩ := realizes_completed realized earned
  exact Machine.finished_run_eq ran complete

/-- An actual finished run of the admitted source has exactly the derived
occurrences; finishing does not authorize dropping retained bindings. -/
theorem AtomDerivation.completed_unique {space : Space} {comparison : SourceBindingComparison} {live : List Atom} {bindings : Bindings}
    {value expected : Atom} {fuel : Nat} {results : ResultSet}
    (derivation : AtomDerivation (comparison := comparison) space live value expected bindings fuel results)
    (earned actual : ResultSet) (budget : Nat) (finished : RecursiveTasks.Configuration)
    (ran : (machine HE.GroundedDispatch.none).run budget
      ⟨space, .work (.atom value expected bindings fuel live), [], earned⟩ = (actual, .finished finished)) :
    actual = results ∧ finished = ⟨space, .returning [], [], earned ++ results⟩ :=
  realizes_completed_unique derivation.realizes earned actual budget finished ran

/-- Any finished run from the admitted request has the whole ordered reply
and the same complete final history, regardless of its supplied work budget. -/
theorem ReadOnlyAtomDerivation.completed_unique {space : Space} (free : EquationFree space) {bindings : Bindings}
    {value expected : Atom} {fuel : Nat} {heads : List Atom}
    (derivation : ReadOnlyAtomDerivation space bindings value expected fuel heads)
    (earned actual : ResultSet) (budget : Nat) (finished : RecursiveTasks.Configuration)
    (ran : (machine HE.GroundedDispatch.none).run budget
      ⟨space, .work (.atom value expected bindings fuel), [], earned⟩ = (actual, .finished finished)) :
    actual = replies bindings heads ∧
      finished = ⟨space, .returning [], [], earned ++ replies bindings heads⟩ :=
  (derivation.toScoped free []).completed_unique earned actual budget finished ran

/-- A realized task resumes its saved residual rather than restarting the
request. The accumulated history and all undelivered occurrences are fixed
by its constructed execution, even when their binding endpoints differ. -/
theorem realizes_resumed {space : Space} {task : Task} {results : ResultSet}
    (realized : Realizes space task results)
    (earned observedPrefix : ResultSet) (first : Nat) (saved : RecursiveTasks.Configuration)
    (paused : (machine HE.GroundedDispatch.none).run first
      ⟨space, .work task, [], earned⟩ = (observedPrefix, .exhausted saved)) :
    ∃ remainingBudget remaining,
      (machine HE.GroundedDispatch.none).run remainingBudget saved =
        (remaining, .finished ⟨space, .returning [], [], earned ++ results⟩) ∧
      observedPrefix ++ remaining = results := by
  obtain ⟨budget, completed⟩ := realizes_completed realized earned
  have resume := (machine HE.GroundedDispatch.none).established_and_pending first budget
    ⟨space, .work task, [], earned⟩ saved observedPrefix paused
  have finished := completed first
  rw [Nat.add_comm budget first, resume] at finished
  have pieces := Prod.mk.inj finished
  refine ⟨budget, ((machine HE.GroundedDispatch.none).run budget saved).1, ?_, pieces.1⟩
  exact Prod.ext rfl pieces.2

/-- A recursive source derivation licenses the continuation from every
reached pause, preserving the entire unconsumed occurrence suffix. -/
theorem AtomDerivation.resumed {space : Space} {comparison : SourceBindingComparison} {live : List Atom} {bindings : Bindings}
    {value expected : Atom} {fuel : Nat} {results : ResultSet}
    (derivation : AtomDerivation (comparison := comparison) space live value expected bindings fuel results)
    (earned observedPrefix : ResultSet) (first : Nat) (saved : RecursiveTasks.Configuration)
    (paused : (machine HE.GroundedDispatch.none).run first
      ⟨space, .work (.atom value expected bindings fuel live), [], earned⟩ = (observedPrefix, .exhausted saved)) :
    ∃ remainingBudget remaining,
      (machine HE.GroundedDispatch.none).run remainingBudget saved =
        (remaining, .finished ⟨space, .returning [], [], earned ++ results⟩) ∧
      observedPrefix ++ remaining = results :=
  realizes_resumed derivation.realizes earned observedPrefix first saved paused

/-- A previously observed prefix and the complete saved worker determine the
remaining occurrence list. Its continuation reuses the saved work and never
restarts evaluation of the original expression. -/
theorem ReadOnlyAtomDerivation.resumed {space : Space} (free : EquationFree space) {bindings : Bindings}
    {value expected : Atom} {fuel : Nat} {heads : List Atom}
    (derivation : ReadOnlyAtomDerivation space bindings value expected fuel heads)
    (earned observedPrefix : ResultSet) (first : Nat) (saved : RecursiveTasks.Configuration)
    (paused : (machine HE.GroundedDispatch.none).run first
      ⟨space, .work (.atom value expected bindings fuel), [], earned⟩ = (observedPrefix, .exhausted saved)) :
    ∃ remainingBudget remaining,
      (machine HE.GroundedDispatch.none).run remainingBudget saved =
        (remaining, .finished ⟨space, .returning [], [], earned ++ replies bindings heads⟩) ∧
      observedPrefix ++ remaining = replies bindings heads :=
  (derivation.toScoped free []).resumed earned observedPrefix first saved paused

/-- Executable source-service collection observes only a finished worker.
Exhaustion remains pending and cannot be converted into an earned empty reply. -/
def collectReply (space : Space) (value expected : Atom) (bindings : Bindings)
    (evaluatorFuel workBudget : Nat) (live : List Atom := []) : Option ResultSet :=
  let result := (machine HE.GroundedDispatch.none).run workBudget
    ⟨space, .work (.atom value expected bindings evaluatorFuel live), [], []⟩
  match result.2 with
  | .finished _ => some result.1
  | _ => none

/-- Collection is earned by source completion, not by exhausting the work
budget. Equation bodies can retain bindings introduced by nested calls. -/
theorem AtomDerivation.collect {space : Space} {comparison : SourceBindingComparison} {live : List Atom} {bindings : Bindings}
    {value expected : Atom} {fuel : Nat} {results : ResultSet}
    (derivation : AtomDerivation (comparison := comparison) space live value expected bindings fuel results) :
    ∃ budget, ∀ later, collectReply space value expected bindings fuel (budget + later) live = some results := by
  obtain ⟨budget, complete⟩ := derivation.completed []
  exact ⟨budget, fun later => by simp only [collectReply, complete later]⟩

/-- Successful collection is exact for this worker's delivery policy. The
cross-presentation source judgment preserves atoms and binding theory. -/
theorem AtomDerivation.collect_exact {space : Space} {comparison : SourceBindingComparison} {live : List Atom} {bindings : Bindings}
    {value expected : Atom} {fuel : Nat} {results : ResultSet}
    (derivation : AtomDerivation (comparison := comparison) space live value expected bindings fuel results)
    (budget : Nat) (actual : ResultSet)
    (collected : collectReply space value expected bindings fuel budget live = some actual) :
    actual = results := by
  cases ran : (machine HE.GroundedDispatch.none).run budget
      ⟨space, .work (.atom value expected bindings fuel live), [], []⟩ with
  | mk events outcome =>
      cases outcome with
      | finished finished =>
          have equal : events = actual := by
            simpa only [collectReply, ran, Option.some.injEq] using collected
          exact equal.symm.trans (derivation.completed_unique [] events budget finished ran).1
      | exhausted saved => simp only [collectReply, ran, reduceCtorEq] at collected
      | faulted => simp only [collectReply, ran, reduceCtorEq] at collected
      | suspended request saved => simp only [collectReply, ran, reduceCtorEq] at collected
      | stuck saved => simp only [collectReply, ran, reduceCtorEq] at collected

/-- A completed collection earns the independent evaluator judgment with
related output bindings. The relation changes representation, not the atom
or the hypotheses available in any selected observation scope. -/
theorem AtomDerivation.collect_sound {space : Space} {live : List Atom} {bindings : Bindings}
    {value expected : Atom} {fuel : Nat} {results : ResultSet}
    (derivation : AtomDerivation (comparison := .records) space live value expected bindings fuel results)
    (budget : Nat) (actual : ResultSet)
    (collected : collectReply space value expected bindings fuel budget live = some actual)
    (result : ResultPair) (member : result ∈ actual) (scope : List String)
    (independentIncoming : Bindings) (related : BindingRecordPerm bindings independentIncoming) :
    ∃ independentOutput : Bindings,
      EvalAtomRawRel space noHost live (protectedScope := scope)
        value expected independentIncoming (result.1, independentOutput) ∧
      BindingRecordPerm result.2 independentOutput ∧
      Spec.Bindings.ScopeObservation.BindingTheoryEquivAt scope result.2 independentOutput := by
  rw [derivation.collect_exact budget actual collected] at member
  obtain ⟨output, evaluated, equivalent⟩ := derivation.sound_records result member scope independentIncoming related
  exact ⟨output, evaluated, equivalent, equivalent.theoryEquivAt scope⟩

theorem ReadOnlyAtomDerivation.collect {space : Space} (free : EquationFree space) {bindings : Bindings}
    {value expected : Atom} {fuel : Nat} {heads : List Atom}
    (derivation : ReadOnlyAtomDerivation space bindings value expected fuel heads) :
    ∃ budget, ∀ later, collectReply space value expected bindings fuel (budget + later) =
      some (replies bindings heads) :=
  (derivation.toScoped free []).collect

/-- A collector cannot return a shorter support-only list or a different
history once the admitted source request has completed. -/
theorem ReadOnlyAtomDerivation.collect_exact {space : Space} (free : EquationFree space) {bindings : Bindings}
    {value expected : Atom} {fuel : Nat} {heads : List Atom}
    (derivation : ReadOnlyAtomDerivation space bindings value expected fuel heads)
    (budget : Nat) (actual : ResultSet)
    (collected : collectReply space value expected bindings fuel budget = some actual) :
    actual = replies bindings heads :=
  (derivation.toScoped free []).collect_exact budget actual collected

/-- Actual finite binding preparation and recursive evaluation compose at
the resolved endpoint. Neither an original variable nor its unresolved type
is silently substituted for the checked prepared request. -/
theorem prepared_nonleaf_collect {space : Space} (free : EquationFree space)
    {substitution : TypeSubst} (normal : substitution.Normal)
    (argument : TypedApplyState) (policy : NativeArgumentControlPolicy.Policy) (preparationFuel : Nat)
    (imported : argument.env = FirstSuccessPreparedArguments.presentedBindings substitution)
    (domainBudget : BindingComposition.atomDepth (NativeArgumentControl.originalDomain argument) + 2 ≤ preparationFuel)
    (argumentBudget : BindingComposition.atomDepth (NativeArgumentControl.original argument) + 2 ≤ preparationFuel)
    (fuel : Nat) (heads : List Atom)
    (derivation : ReadOnlyAtomDerivation space argument.env
      (FirstSuccessPreparedArguments.prepareSource argument policy preparationFuel).bound
      (FirstSuccessPreparedArguments.prepareSource argument policy preparationFuel).domain fuel heads) :
    FirstSuccessPreparedArguments.PreparationRel substitution argument policy
      (FirstSuccessPreparedArguments.prepareSource argument policy preparationFuel) ∧
    ∃ budget, ∀ later, collectReply space
      (FirstSuccessPreparedArguments.prepareSource argument policy preparationFuel).bound
      (FirstSuccessPreparedArguments.prepareSource argument policy preparationFuel).domain
      argument.env fuel (budget + later) = some (replies argument.env heads) :=
  ⟨FirstSuccessPreparedArguments.preparation_sound normal argument policy preparationFuel
    imported domainBudget argumentBudget, derivation.collect free⟩

/-- The actual finite source result, the independent delivery relation and
history preservation agree at the complete saved evaluation endpoint. -/
theorem deliver_nonleaf {space : Space} (free : EquationFree space)
    (configuration : NativeArgumentControl.Configuration)
    (history : NativeArgumentControlHistory.HistoryInv configuration)
    (argument : TypedApplyState) (prepared : NativeArgumentControl.Prepared)
    (ticket : Nat) (rest : List NativeArgumentControl.Frame)
    (pending : configuration.frames = .waiting (.evaluate argument prepared) ticket :: rest)
    (fuel charge : Nat) (heads : List Atom)
    (derivation : ReadOnlyAtomDerivation space argument.env prepared.bound prepared.domain fuel heads) :
    ∃ budget after,
      collectReply space prepared.bound prepared.domain argument.env fuel budget = some (replies argument.env heads) ∧
      NativeArgumentControl.DeliveryRel configuration
        ⟨(NativeArgumentControl.request configuration (.evaluate argument prepared) ticket).endpoint,
          .evaluated (replies argument.env heads), charge⟩ after ∧
      NativeArgumentControlHistory.HistoryInv after ∧
      NativeArgumentControlEncoding.resumeInteractionData
        (NativeArgumentControlMachine.interactionData (.active configuration))
        (.returned (NativeArgumentControlEncoding.replyData
          ⟨(NativeArgumentControl.request configuration (.evaluate argument prepared) ticket).endpoint,
            .evaluated (replies argument.env heads), charge⟩)) =
          NativeArgumentControlMachine.interactionData (.active after) ∧
      (∀ result ∈ replies argument.env heads,
        EvalAtomRawRel space noHost [] prepared.bound prepared.domain argument.env result) := by
  obtain ⟨budget, collected⟩ := derivation.collect free
  let reply : NativeArgumentControl.Reply :=
    ⟨(NativeArgumentControl.request configuration (.evaluate argument prepared) ticket).endpoint,
      .evaluated (replies argument.env heads), charge⟩
  let after := NativeArgumentControl.replied configuration rest reply
    [.iterate (NativeArgumentControl.selectedSnapshot argument prepared (replies argument.env heads)) prepared]
  have accepted : NativeArgumentControl.deliver configuration reply = .accepted after :=
    NativeArgumentControl.evaluated_reply configuration argument prepared ticket rest
      (replies argument.env heads) charge pending
  have delivery := (NativeArgumentControl.deliver_iff configuration reply after).mp accepted
  refine ⟨budget, after, by simpa using collected 0, delivery,
    NativeArgumentControlHistory.delivery_preserves_history history accepted,
    (NativeArgumentControlEncoding.represented_reply_accepted_iff configuration after reply).mpr delivery, ?_⟩
  intro result member
  obtain ⟨value, valueMember, rfl⟩ := List.mem_map.mp member
  exact derivation.sound free value valueMember []


section OwnedReplies

open Mettapedia.Machines
open NativeArgumentControlHistory.OwnedReplyBoundary

/-- An independently earned nonleaf source reply crosses the issued boundary
only in the source world it actually consulted. The dependency retains the
complete source atoms, including order and duplicate declarations. This is
the admitted read-only source profile, not a native callback correspondence. -/
theorem deliver_nonleaf_owned {Key : Type} [DecidableEq Key]
    {space : Space} (free : EquationFree space)
    (registry : Registry) (capture : Capture Key (List Atom)) (handle : Handle)
    (world : RevisionEnvironment Key (List Atom)) (sourceKey : Key)
    (sourceRead : capture.view.captured.current sourceKey = space.atoms)
    (consulted : sourceKey ∈ capture.view.consulted)
    (matchesOwner : Matches capture handle) (current : capture.view.CanPublish world)
    (authorized : Mettapedia.Machines.Cursor.OwnedLifecycle.IssuedReturn.Authenticated registry handle)
    (history : NativeArgumentControlHistory.HistoryInv capture.capture)
    (argument : TypedApplyState) (prepared : NativeArgumentControl.Prepared)
    (ticket : Nat) (rest : List NativeArgumentControl.Frame)
    (pending : capture.capture.frames = .waiting (.evaluate argument prepared) ticket :: rest)
    (fuel charge : Nat) (heads : List Atom)
    (derivation : ReadOnlyAtomDerivation space argument.env prepared.bound prepared.domain fuel heads) :
    ∃ budget after next,
      world.current sourceKey = space.atoms ∧
      collectReply space prepared.bound prepared.domain argument.env fuel budget = some (replies argument.env heads) ∧
      (deliverChecked registry world capture handle
        ⟨(NativeArgumentControl.request capture.capture (.evaluate argument prepared) ticket).endpoint,
          .evaluated (replies argument.env heads), charge⟩).1 = .ok (after, next) ∧
      NativeArgumentControlHistory.HistoryInv after ∧
      (∀ result ∈ replies argument.env heads,
        EvalAtomRawRel space noHost [] prepared.bound prepared.domain argument.env result) := by
  obtain ⟨budget, after, collected, delivered, retained, _, sound⟩ :=
    deliver_nonleaf free capture.capture history argument prepared ticket rest pending fuel charge heads derivation
  obtain ⟨next, cleared, released⟩ :=
    (Mettapedia.Machines.Cursor.OwnedLifecycle.IssuedReturn.releaseIssued_exists_iff registry handle).mpr authorized
  have sameSource := (CapturedReadView.valid_dependencies_iff capture.view world).mp current.2.2
    sourceKey (List.mem_toFinset.mpr consulted)
  exact ⟨budget, after, next, sameSource.trans sourceRead, collected,
    (deliverChecked_iff _ _ _ _ _ _ _).mpr ⟨matchesOwner, current, delivered, cleared, released⟩,
    retained, sound⟩

end OwnedReplies

/-- Operational child occurrences, including their exact bindings. These
receipts are not committed external effects or native ownership authority. -/
def sourceEvent (result : ResultPair) : Atom :=
  .expression [.symbol "he-source-result", result.1, TypedApplyEncoding.bindingsData result.2]

/-- Read the exact value and binding frame of an operational child receipt. -/
def readSourceEvent : Atom → Option ResultPair
  | .expression [.symbol "he-source-result", value, bindings] => do
      return (value, ← TypedApplyEncoding.readBindings bindings)
  | _ => none

@[simp] theorem readSourceEvent_sourceEvent (result : ResultPair) :
    readSourceEvent (sourceEvent result) = some result := by
  rcases result with ⟨value, bindings⟩
  simp [sourceEvent, readSourceEvent]

theorem sourceEvent_injective : Function.Injective sourceEvent := by
  intro left right equal
  have decoded := congrArg readSourceEvent equal
  simpa only [readSourceEvent_sourceEvent, Option.some.injEq] using decoded

/-- Decoding the ordered service log recovers every original occurrence,
including duplicates and every binding equality. -/
theorem read_sourceEvents (results : ResultSet) :
    (results.map sourceEvent).mapM readSourceEvent = some results := by
  induction results with
  | nil => rfl
  | cons result results ih => simp [ih]

def evaluationReply (endpoint : Atom) (charge : Nat) (finished : RecursiveTasks.Configuration) :
    Mettapedia.GSLT.Distinction.ProductiveBlocks.Reply Atom Atom :=
  .returned (NativeArgumentControlEncoding.replyData
    ⟨endpoint, .evaluated finished.emitted, charge⟩)

/-- The service is the existing worker with event/verdict labels adapted to
the callback protocol. Its state and every transition kind remain unchanged. -/
def evaluationService (endpoint : Atom) (charge : Nat) :
    Machine RecursiveTasks.Configuration Atom
      (Mettapedia.GSLT.Distinction.ProductiveBlocks.Reply Atom Atom) Empty :=
  (machine HE.GroundedDispatch.none).relabel sourceEvent (evaluationReply endpoint charge) id

/-- Event adaptation changes neither the saved worker nor its transition
charges. It does not account for internal native or external service work. -/
theorem evaluationService_spent (endpoint : Atom) (charge : Nat)
    (price : RecursiveTasks.Configuration → Nat) (budget : Nat) (initial : RecursiveTasks.Configuration) :
    (evaluationService endpoint charge).spent price budget initial =
      (machine HE.GroundedDispatch.none).spent price budget initial :=
  (machine HE.GroundedDispatch.none).spent_relabel sourceEvent (evaluationReply endpoint charge) id
    price budget initial

/-- The service protocol uses the already constructed lossless worker codec.
Both simulations retain actual represented residuals; the verdict adaptation
does not install an assumed source/native correspondence. -/
theorem evaluationService_forward (endpoint : Atom) (charge : Nat) :
    CostSimulation (evaluationService endpoint charge)
      ((dataMachine HE.GroundedDispatch.none).relabel sourceEvent (evaluationReply endpoint charge) id)
      Represents 1 :=
  (forwardSimulation HE.GroundedDispatch.none).relabel sourceEvent (evaluationReply endpoint charge) id

theorem evaluationService_backward (endpoint : Atom) (charge : Nat) :
    CostSimulation
      ((dataMachine HE.GroundedDispatch.none).relabel sourceEvent (evaluationReply endpoint charge) id)
      (evaluationService endpoint charge) (fun represented actual => Represents actual represented) 1 :=
  (backwardSimulation HE.GroundedDispatch.none).relabel sourceEvent (evaluationReply endpoint charge) id

/-- A constructed task completion earns the actual service verdict and every
published value/binding receipt. Equation continuations may change bindings;
the protocol does not replace them with the original input frame. -/
theorem realizes_service_completed {space : Space} {task : Task} {results : ResultSet}
    (realized : Realizes space task results) (endpoint : Atom) (charge : Nat) :
    ∃ budget, ∀ later, (evaluationService endpoint charge).run (budget + later)
      ⟨space, .work task, [], []⟩ =
      (results.map sourceEvent,
        .finished (.returned (NativeArgumentControlEncoding.replyData
          ⟨endpoint, .evaluated results, charge⟩))) := by
  obtain ⟨budget, complete⟩ := realizes_completed realized []
  refine ⟨budget, fun later => ?_⟩
  rw [evaluationService, Machine.run_relabel, complete later]
  rfl

/-- A service verdict carries the results derived from the recursive
source, including bindings introduced by its equation continuations. -/
theorem AtomDerivation.service_completed {space : Space} {comparison : SourceBindingComparison} {live : List Atom} {bindings : Bindings}
    {value expected : Atom} {fuel : Nat} {results : ResultSet}
    (derivation : AtomDerivation (comparison := comparison) space live value expected bindings fuel results) (endpoint : Atom) (charge : Nat) :
    ∃ budget, ∀ later, (evaluationService endpoint charge).run (budget + later)
      ⟨space, .work (.atom value expected bindings fuel live), [], []⟩ =
      (results.map sourceEvent,
        .finished (.returned (NativeArgumentControlEncoding.replyData
          ⟨endpoint, .evaluated results, charge⟩))) :=
  realizes_service_completed derivation.realizes endpoint charge

theorem ReadOnlyAtomDerivation.service_completed {space : Space} (free : EquationFree space) {bindings : Bindings}
    {value expected : Atom} {fuel : Nat} {heads : List Atom}
    (derivation : ReadOnlyAtomDerivation space bindings value expected fuel heads) (endpoint : Atom) (charge : Nat) :
    ∃ budget, ∀ later, (evaluationService endpoint charge).run (budget + later)
      ⟨space, .work (.atom value expected bindings fuel), [], []⟩ =
      ((replies bindings heads).map sourceEvent,
        .finished (.returned (NativeArgumentControlEncoding.replyData
          ⟨endpoint, .evaluated (replies bindings heads), charge⟩))) :=
  (derivation.toScoped free []).service_completed endpoint charge

/-- The same actual task, represented through the existing worker codec,
produces the same full service verdict and occurrence receipts. -/
theorem realizes_encoded_service_completed {space : Space} {task : Task} {results : ResultSet}
    (realized : Realizes space task results) (endpoint : Atom) (charge : Nat) :
    ∃ budget, ∀ later,
      ((dataMachine HE.GroundedDispatch.none).relabel sourceEvent (evaluationReply endpoint charge) id).run
        (budget + later) (RecursiveEncoding.configurationData ⟨space, .work task, [], []⟩) =
      (results.map sourceEvent,
        .finished (.returned (NativeArgumentControlEncoding.replyData
          ⟨endpoint, .evaluated results, charge⟩))) := by
  obtain ⟨budget, complete⟩ := realizes_encoded_completed realized []
  refine ⟨budget, fun later => ?_⟩
  rw [Machine.run_relabel, complete later]
  rfl

/-- The same earned service reply is delivered through the checked data
representation of the saved worker. -/
theorem AtomDerivation.encoded_service_completed {space : Space} {comparison : SourceBindingComparison} {live : List Atom} {bindings : Bindings}
    {value expected : Atom} {fuel : Nat} {results : ResultSet}
    (derivation : AtomDerivation (comparison := comparison) space live value expected bindings fuel results) (endpoint : Atom) (charge : Nat) :
    ∃ budget, ∀ later,
      ((dataMachine HE.GroundedDispatch.none).relabel sourceEvent (evaluationReply endpoint charge) id).run
        (budget + later) (RecursiveEncoding.configurationData
          ⟨space, .work (.atom value expected bindings fuel live), [], []⟩) =
      (results.map sourceEvent,
        .finished (.returned (NativeArgumentControlEncoding.replyData
          ⟨endpoint, .evaluated results, charge⟩))) :=
  realizes_encoded_service_completed derivation.realizes endpoint charge

theorem ReadOnlyAtomDerivation.encoded_service_completed {space : Space} (free : EquationFree space) {bindings : Bindings}
    {value expected : Atom} {fuel : Nat} {heads : List Atom}
    (derivation : ReadOnlyAtomDerivation space bindings value expected fuel heads) (endpoint : Atom) (charge : Nat) :
    ∃ budget, ∀ later,
      ((dataMachine HE.GroundedDispatch.none).relabel sourceEvent (evaluationReply endpoint charge) id).run
        (budget + later) (RecursiveEncoding.configurationData
          ⟨space, .work (.atom value expected bindings fuel), [], []⟩) =
      ((replies bindings heads).map sourceEvent,
        .finished (.returned (NativeArgumentControlEncoding.replyData
          ⟨endpoint, .evaluated (replies bindings heads), charge⟩))) :=
  (derivation.toScoped free []).encoded_service_completed endpoint charge

/-- An earned nonleaf evaluation composes with the existing retained caller
through the common resumable handler. The bound is derived for this input,
and includes call, worker occurrences and reply. The caller returns at the
accepted endpoint with its actual saved continuation intact. -/
theorem handled_evaluation {space : Space} {live : List Atom}
    (operations : NativeArgumentControl.Operations) (policy : NativeArgumentControlMachine.RefusalPolicy)
    (configuration : NativeArgumentControl.Configuration)
    (argument : TypedApplyState) (prepared : NativeArgumentControl.Prepared)
    (ticket : Nat) (rest : List NativeArgumentControl.Frame)
    (pending : configuration.frames = .waiting (.evaluate argument prepared) ticket :: rest)
    (fuel charge : Nat) (results : ResultSet)
    (realized : Realizes space (.atom prepared.bound prepared.domain argument.env fuel live) results) :
    let endpoint := (NativeArgumentControl.request configuration (.evaluate argument prepared) ticket).endpoint
    let reply : NativeArgumentControl.Reply := ⟨endpoint, .evaluated results, charge⟩
    let after := NativeArgumentControl.replied configuration rest reply
      [.iterate (NativeArgumentControl.selectedSnapshot argument prepared results) prepared]
    let initial : RecursiveTasks.Configuration :=
      ⟨space, .work (.atom prepared.bound prepared.domain argument.env fuel live), [], []⟩
    ∃ budget, ((NativeArgumentControlMachine.interactionMachine operations policy).handle
      NativeArgumentControlEncoding.interactionCallback (evaluationService endpoint charge) (fun _ => initial)).run
        budget (.running (.active configuration)) =
      (NativeArgumentControlEncoding.callEventData endpoint ::
        results.map sourceEvent ++
        [NativeArgumentControlEncoding.replyEventData (.returned (NativeArgumentControlEncoding.replyData reply))],
        .exhausted (.running (.active after))) := by
  dsimp only
  let endpoint := (NativeArgumentControl.request configuration (.evaluate argument prepared) ticket).endpoint
  let reply : NativeArgumentControl.Reply := ⟨endpoint, .evaluated results, charge⟩
  let after := NativeArgumentControl.replied configuration rest reply
    [.iterate (NativeArgumentControl.selectedSnapshot argument prepared results) prepared]
  let initial : RecursiveTasks.Configuration :=
    ⟨space, .work (.atom prepared.bound prepared.domain argument.env fuel live), [], []⟩
  have call : (NativeArgumentControlMachine.interactionMachine operations policy).step (.active configuration) =
      some (.call endpoint (.active configuration)) := by
    simp only [NativeArgumentControlMachine.interactionMachine,
      NativeArgumentControlMachine.inspectInteraction,
      NativeArgumentControlMachine.awaiting_preserves operations configuration (.evaluate argument prepared)
        ticket rest pending, NativeArgumentControlMachine.interactionAdvance, endpoint]
  obtain ⟨bound, completed⟩ := realizes_service_completed realized endpoint charge
  have answered : (evaluationService endpoint charge).run bound initial =
      (results.map sourceEvent,
        .finished (.returned (NativeArgumentControlEncoding.replyData reply))) := by
    simpa only [Nat.add_zero, initial, reply] using completed 0
  obtain ⟨used, _, ran⟩ := (NativeArgumentControlMachine.interactionMachine operations policy).handle_call_run
    NativeArgumentControlEncoding.interactionCallback (evaluationService endpoint charge) (fun _ => initial)
    (.active configuration) (.active configuration) endpoint call bound
    (results.map sourceEvent) (.returned (NativeArgumentControlEncoding.replyData reply)) answered
  have accepted : NativeArgumentControl.deliver configuration reply = .accepted after :=
    NativeArgumentControl.evaluated_reply configuration argument prepared ticket rest
      results charge pending
  exact ⟨used, by simpa only [NativeArgumentControlEncoding.interactionCallback,
    NativeArgumentControlEncoding.resumeInteraction, NativeArgumentControlEncoding.readReply_replyData,
    accepted] using ran⟩

/-- The admitted recursive source supplies the actual worker to the retained
caller; the service cannot restore the caller's old binding frame. -/
theorem AtomDerivation.handled {space : Space} {comparison : SourceBindingComparison} {live : List Atom}
    (operations : NativeArgumentControl.Operations) (policy : NativeArgumentControlMachine.RefusalPolicy)
    (configuration : NativeArgumentControl.Configuration)
    (argument : TypedApplyState) (prepared : NativeArgumentControl.Prepared)
    (ticket : Nat) (rest : List NativeArgumentControl.Frame)
    (pending : configuration.frames = .waiting (.evaluate argument prepared) ticket :: rest)
    (fuel charge : Nat) (results : ResultSet)
    (derivation : AtomDerivation (comparison := comparison) space live prepared.bound prepared.domain argument.env fuel results) :
    let endpoint := (NativeArgumentControl.request configuration (.evaluate argument prepared) ticket).endpoint
    let reply : NativeArgumentControl.Reply := ⟨endpoint, .evaluated results, charge⟩
    let after := NativeArgumentControl.replied configuration rest reply
      [.iterate (NativeArgumentControl.selectedSnapshot argument prepared results) prepared]
    let initial : RecursiveTasks.Configuration :=
      ⟨space, .work (.atom prepared.bound prepared.domain argument.env fuel live), [], []⟩
    ∃ budget, ((NativeArgumentControlMachine.interactionMachine operations policy).handle
      NativeArgumentControlEncoding.interactionCallback (evaluationService endpoint charge) (fun _ => initial)).run
        budget (.running (.active configuration)) =
      (NativeArgumentControlEncoding.callEventData endpoint ::
        results.map sourceEvent ++
        [NativeArgumentControlEncoding.replyEventData (.returned (NativeArgumentControlEncoding.replyData reply))],
        .exhausted (.running (.active after))) :=
  handled_evaluation operations policy configuration argument prepared ticket rest pending fuel charge
    results derivation.realizes

/-- Independent source derivations specialize the full-result interaction law. -/
theorem handled_nonleaf {space : Space} (free : EquationFree space)
    (operations : NativeArgumentControl.Operations) (policy : NativeArgumentControlMachine.RefusalPolicy)
    (configuration : NativeArgumentControl.Configuration)
    (argument : TypedApplyState) (prepared : NativeArgumentControl.Prepared)
    (ticket : Nat) (rest : List NativeArgumentControl.Frame)
    (pending : configuration.frames = .waiting (.evaluate argument prepared) ticket :: rest)
    (fuel charge : Nat) (heads : List Atom)
    (derivation : ReadOnlyAtomDerivation space argument.env prepared.bound prepared.domain fuel heads) :
    let endpoint := (NativeArgumentControl.request configuration (.evaluate argument prepared) ticket).endpoint
    let reply : NativeArgumentControl.Reply := ⟨endpoint, .evaluated (replies argument.env heads), charge⟩
    let after := NativeArgumentControl.replied configuration rest reply
      [.iterate (NativeArgumentControl.selectedSnapshot argument prepared (replies argument.env heads)) prepared]
    let initial : RecursiveTasks.Configuration :=
      ⟨space, .work (.atom prepared.bound prepared.domain argument.env fuel), [], []⟩
    ∃ budget, ((NativeArgumentControlMachine.interactionMachine operations policy).handle
      NativeArgumentControlEncoding.interactionCallback (evaluationService endpoint charge) (fun _ => initial)).run
        budget (.running (.active configuration)) =
      (NativeArgumentControlEncoding.callEventData endpoint ::
        (replies argument.env heads).map sourceEvent ++
        [NativeArgumentControlEncoding.replyEventData (.returned (NativeArgumentControlEncoding.replyData reply))],
        .exhausted (.running (.active after))) :=
  handled_evaluation operations policy configuration argument prepared ticket rest pending fuel charge
    (replies argument.env heads) (derivation.realizes free)


/-- Both sides of the actual interaction are represented here: the saved
caller uses its checked packet interface, and the service uses the existing
recursive configuration codec. The full reply comes from the constructed
worker execution, including every changed binding endpoint. -/
theorem handled_evaluation_encoded {space : Space} {live : List Atom}
    (operations : NativeArgumentControl.Operations) (policy : NativeArgumentControlMachine.RefusalPolicy)
    (configuration : NativeArgumentControl.Configuration)
    (argument : TypedApplyState) (prepared : NativeArgumentControl.Prepared)
    (ticket : Nat) (rest : List NativeArgumentControl.Frame)
    (pending : configuration.frames = .waiting (.evaluate argument prepared) ticket :: rest)
    (fuel charge : Nat) (results : ResultSet)
    (realized : Realizes space (.atom prepared.bound prepared.domain argument.env fuel live) results) :
    let endpoint := (NativeArgumentControl.request configuration (.evaluate argument prepared) ticket).endpoint
    let reply : NativeArgumentControl.Reply := ⟨endpoint, .evaluated results, charge⟩
    let after := NativeArgumentControl.replied configuration rest reply
      [.iterate (NativeArgumentControl.selectedSnapshot argument prepared results) prepared]
    let initial : RecursiveTasks.Configuration :=
      ⟨space, .work (.atom prepared.bound prepared.domain argument.env fuel live), [], []⟩
    ∃ budget, ((NativeArgumentControlEncoding.interactionDataMachine operations policy).handle
      NativeArgumentControlEncoding.representedCallback
      ((dataMachine HE.GroundedDispatch.none).relabel sourceEvent (evaluationReply endpoint charge) id)
      (fun _ => RecursiveEncoding.configurationData initial)).run budget
        (.running (NativeArgumentControlMachine.interactionData (.active configuration))) =
      (NativeArgumentControlEncoding.callEventData endpoint ::
        results.map sourceEvent ++
        [NativeArgumentControlEncoding.replyEventData (.returned (NativeArgumentControlEncoding.replyData reply))],
        .exhausted (.running (NativeArgumentControlMachine.interactionData (.active after)))) := by
  dsimp only
  let endpoint := (NativeArgumentControl.request configuration (.evaluate argument prepared) ticket).endpoint
  let reply : NativeArgumentControl.Reply := ⟨endpoint, .evaluated results, charge⟩
  let after := NativeArgumentControl.replied configuration rest reply
    [.iterate (NativeArgumentControl.selectedSnapshot argument prepared results) prepared]
  let initial : RecursiveTasks.Configuration :=
    ⟨space, .work (.atom prepared.bound prepared.domain argument.env fuel live), [], []⟩
  have call : (NativeArgumentControlMachine.interactionMachine operations policy).step (.active configuration) =
      some (.call endpoint (.active configuration)) := by
    simp only [NativeArgumentControlMachine.interactionMachine,
      NativeArgumentControlMachine.inspectInteraction,
      NativeArgumentControlMachine.awaiting_preserves operations configuration (.evaluate argument prepared)
        ticket rest pending, NativeArgumentControlMachine.interactionAdvance, endpoint]
  have encodedCall : (NativeArgumentControlEncoding.interactionDataMachine operations policy).step
      (NativeArgumentControlMachine.interactionData (.active configuration)) =
      some (.call endpoint (NativeArgumentControlMachine.interactionData (.active configuration))) := by
    rw [NativeArgumentControlEncoding.interaction_step_encoded, call]
    rfl
  obtain ⟨bound, completed⟩ := realizes_encoded_service_completed realized endpoint charge
  have answered :
      ((dataMachine HE.GroundedDispatch.none).relabel sourceEvent (evaluationReply endpoint charge) id).run
        bound (RecursiveEncoding.configurationData initial) =
      (results.map sourceEvent,
        .finished (.returned (NativeArgumentControlEncoding.replyData reply))) := by
    simpa only [Nat.add_zero, initial, reply] using completed 0
  obtain ⟨used, _, ran⟩ := (NativeArgumentControlEncoding.interactionDataMachine operations policy).handle_call_run
    NativeArgumentControlEncoding.representedCallback
    ((dataMachine HE.GroundedDispatch.none).relabel sourceEvent (evaluationReply endpoint charge) id)
    (fun _ => RecursiveEncoding.configurationData initial)
    (NativeArgumentControlMachine.interactionData (.active configuration))
    (NativeArgumentControlMachine.interactionData (.active configuration)) endpoint encodedCall bound
    (results.map sourceEvent) (.returned (NativeArgumentControlEncoding.replyData reply)) answered
  have accepted : NativeArgumentControl.deliver configuration reply = .accepted after :=
    NativeArgumentControl.evaluated_reply configuration argument prepared ticket rest
      results charge pending
  have represented := (NativeArgumentControlEncoding.represented_reply_accepted_iff configuration after reply).mpr
    ((NativeArgumentControl.deliver_iff configuration reply after).mp accepted)
  exact ⟨used, by simpa only [NativeArgumentControlEncoding.representedCallback, represented] using ran⟩

/-- The admitted recursive source supplies the actual worker to the retained
caller; the service cannot restore the caller's old binding frame. -/
theorem AtomDerivation.handled_encoded {space : Space} {comparison : SourceBindingComparison} {live : List Atom}
    (operations : NativeArgumentControl.Operations) (policy : NativeArgumentControlMachine.RefusalPolicy)
    (configuration : NativeArgumentControl.Configuration)
    (argument : TypedApplyState) (prepared : NativeArgumentControl.Prepared)
    (ticket : Nat) (rest : List NativeArgumentControl.Frame)
    (pending : configuration.frames = .waiting (.evaluate argument prepared) ticket :: rest)
    (fuel charge : Nat) (results : ResultSet)
    (derivation : AtomDerivation (comparison := comparison) space live prepared.bound prepared.domain argument.env fuel results) :
    let endpoint := (NativeArgumentControl.request configuration (.evaluate argument prepared) ticket).endpoint
    let reply : NativeArgumentControl.Reply := ⟨endpoint, .evaluated results, charge⟩
    let after := NativeArgumentControl.replied configuration rest reply
      [.iterate (NativeArgumentControl.selectedSnapshot argument prepared results) prepared]
    let initial : RecursiveTasks.Configuration :=
      ⟨space, .work (.atom prepared.bound prepared.domain argument.env fuel live), [], []⟩
    ∃ budget, ((NativeArgumentControlEncoding.interactionDataMachine operations policy).handle
      NativeArgumentControlEncoding.representedCallback
      ((dataMachine HE.GroundedDispatch.none).relabel sourceEvent (evaluationReply endpoint charge) id)
      (fun _ => RecursiveEncoding.configurationData initial)).run budget
        (.running (NativeArgumentControlMachine.interactionData (.active configuration))) =
      (NativeArgumentControlEncoding.callEventData endpoint ::
        results.map sourceEvent ++
        [NativeArgumentControlEncoding.replyEventData (.returned (NativeArgumentControlEncoding.replyData reply))],
        .exhausted (.running (NativeArgumentControlMachine.interactionData (.active after)))) :=
  handled_evaluation_encoded operations policy configuration argument prepared ticket rest pending fuel charge
    results derivation.realizes

/-- Independent source derivations specialize the full-result interaction law. -/
theorem handled_nonleaf_encoded {space : Space} (free : EquationFree space)
    (operations : NativeArgumentControl.Operations) (policy : NativeArgumentControlMachine.RefusalPolicy)
    (configuration : NativeArgumentControl.Configuration)
    (argument : TypedApplyState) (prepared : NativeArgumentControl.Prepared)
    (ticket : Nat) (rest : List NativeArgumentControl.Frame)
    (pending : configuration.frames = .waiting (.evaluate argument prepared) ticket :: rest)
    (fuel charge : Nat) (heads : List Atom)
    (derivation : ReadOnlyAtomDerivation space argument.env prepared.bound prepared.domain fuel heads) :
    let endpoint := (NativeArgumentControl.request configuration (.evaluate argument prepared) ticket).endpoint
    let reply : NativeArgumentControl.Reply := ⟨endpoint, .evaluated (replies argument.env heads), charge⟩
    let after := NativeArgumentControl.replied configuration rest reply
      [.iterate (NativeArgumentControl.selectedSnapshot argument prepared (replies argument.env heads)) prepared]
    let initial : RecursiveTasks.Configuration :=
      ⟨space, .work (.atom prepared.bound prepared.domain argument.env fuel), [], []⟩
    ∃ budget, ((NativeArgumentControlEncoding.interactionDataMachine operations policy).handle
      NativeArgumentControlEncoding.representedCallback
      ((dataMachine HE.GroundedDispatch.none).relabel sourceEvent (evaluationReply endpoint charge) id)
      (fun _ => RecursiveEncoding.configurationData initial)).run budget
        (.running (NativeArgumentControlMachine.interactionData (.active configuration))) =
      (NativeArgumentControlEncoding.callEventData endpoint ::
        (replies argument.env heads).map sourceEvent ++
        [NativeArgumentControlEncoding.replyEventData (.returned (NativeArgumentControlEncoding.replyData reply))],
        .exhausted (.running (NativeArgumentControlMachine.interactionData (.active after)))) :=
  handled_evaluation_encoded operations policy configuration argument prepared ticket rest pending fuel charge
    (replies argument.env heads) (derivation.realizes free)



/-- Every finished checked ordinary invocation of the admitted source has
exactly its ordered producer/return occurrences and retained endpoint. -/
theorem CallDerivation.checked_completed_unique {space : Space} {comparison : SourceBindingComparison}
    {live : List Atom} {value expected : Atom} {bindings : Bindings} {fuel : Nat} {results : ResultSet}
    (derived : CallDerivation (comparison := comparison) space live value expected bindings fuel results)
    (earned actual : ResultSet) (budget : Nat) (finished : Configuration)
    (ran : (FirstSuccessRecursiveExecution.Checked.machine HE.GroundedDispatch.none).run budget
      ⟨space, .work (.call value expected bindings fuel live), [], earned⟩ = (actual, .finished finished)) :
    actual = results ∧ finished = ⟨space, .returning [], [], earned ++ results⟩ :=
  realizes_completed_unique derived.realizes earned actual budget finished
    (FirstSuccessRecursiveExecution.Checked.finished_refines HE.GroundedDispatch.none budget _ actual finished ran)

/-- Ordinary completion delivers the independently derived call meaning at
its actual selected frame. This concerns the locally admitted grammar. -/
theorem CallDerivation.checked_completed_sound {space : Space} {comparison : SourceBindingComparison}
    {live : List Atom} {value expected : Atom} {bindings : Bindings} {fuel : Nat} {results : ResultSet}
    (derived : CallDerivation (comparison := comparison) space live value expected bindings fuel results)
    (earned actual : ResultSet) (budget : Nat) (finished : Configuration)
    (ran : (FirstSuccessRecursiveExecution.Checked.machine HE.GroundedDispatch.none).run budget
      ⟨space, .work (.call value expected bindings fuel live), [], earned⟩ = (actual, .finished finished))
    (independent : BindingFrame) (related : comparison.FrameRelated bindings independent) :
    ∀ result ∈ actual, ∃ output, CallRel space noHost live value expected independent (result.1, output) ∧
      comparison.FrameRelated result.2 output := by
  have same := (derived.checked_completed_unique earned actual budget finished ran).1
  intro result member
  exact derived.sound result (same ▸ member) independent related

/-- A checked completion supplies actual resource coverage. The existing
source realization then identifies every delivered occurrence and the full
retained endpoint; no finite empty approximation licenses completion. -/
theorem AtomDerivation.checked_completed_unique {space : Space} {comparison : SourceBindingComparison} {live : List Atom}
    {bindings : Bindings} {value expected : Atom} {fuel : Nat} {results : ResultSet}
    (derivation : AtomDerivation (comparison := comparison) space live value expected bindings fuel results)
    (earned actual : ResultSet) (budget : Nat) (finished : Configuration)
    (ran : (Checked.machine HE.GroundedDispatch.none).run budget
      ⟨space, .work (.atom value expected bindings fuel live), [], earned⟩ = (actual, .finished finished)) :
    actual = results ∧ finished = ⟨space, .returning [], [], earned ++ results⟩ :=
  derivation.completed_unique earned actual budget finished
    (Checked.finished_refines HE.GroundedDispatch.none budget _ actual finished ran)

/-- Every checked delivery has the independent scoped source judgment.
The declared comparison relates both binding endpoints; the returned atom
remains exact. -/
theorem AtomDerivation.checked_completed_sound {space : Space} {comparison : SourceBindingComparison} {live : List Atom}
    {bindings : Bindings} {value expected : Atom} {fuel : Nat} {results : ResultSet}
    (derivation : AtomDerivation (comparison := comparison) space live value expected bindings fuel results)
    (earned actual : ResultSet) (budget : Nat) (finished : Configuration)
    (ran : (Checked.machine HE.GroundedDispatch.none).run budget
      ⟨space, .work (.atom value expected bindings fuel live), [], earned⟩ = (actual, .finished finished))
    (scope : List String) (independentIncoming : BindingFrame)
    (related : comparison.FrameRelated bindings independentIncoming) :
    ∀ result ∈ actual, ∃ independentOutput,
      EvalAtomRawRel space noHost live (protectedScope := scope) value expected
        independentIncoming (result.1, independentOutput) ∧
      comparison.FrameRelated result.2 independentOutput := by
  have same := (derivation.checked_completed_unique earned actual budget finished ran).1
  intro result member
  exact derivation.sound result (same ▸ member) scope independentIncoming related

/-- Checked completion and independent source realization jointly fix the
answer at every larger initial evaluation depth. This is earned by actual
coverage along the run, rather than equality of bounded approximations. -/
theorem AtomDerivation.checked_completed_deepen {space : Space} {comparison : SourceBindingComparison} {live : List Atom}
    {bindings : Bindings} {value expected : Atom} {fuel : Nat} {results : ResultSet}
    (derivation : AtomDerivation (comparison := comparison) space live value expected bindings fuel results)
    (earned actual : ResultSet) (budget extra : Nat) (finished : Configuration)
    (ran : (Checked.machine HE.GroundedDispatch.none).run budget
      ⟨space, .work (.atom value expected bindings fuel live), [], earned⟩ = (actual, .finished finished)) :
    (machine HE.GroundedDispatch.none).run budget
      ⟨space, .work (.atom value expected bindings (fuel + extra) live), [], earned⟩ =
      (results, .finished ⟨space, .returning [], [], earned ++ results⟩) := by
  obtain ⟨rfl, rfl⟩ := derivation.checked_completed_unique earned actual budget finished ran
  simpa only [Configuration.deepen, Control.deepen, Task.replenish, List.map_nil] using
    Checked.completed_deepen HE.GroundedDispatch.none extra budget _ _ _ ran

/-- A complete checked continuation after a scheduler pause preserves the
source's entire occurrence list. It cannot replay the established prefix. -/
theorem AtomDerivation.checked_resumed_unique {space : Space} {comparison : SourceBindingComparison} {live : List Atom}
    {bindings : Bindings} {value expected : Atom} {fuel : Nat} {results : ResultSet}
    (derivation : AtomDerivation (comparison := comparison) space live value expected bindings fuel results)
    (earned before after : ResultSet) (first second : Nat) (saved finished : Configuration)
    (paused : (Checked.machine HE.GroundedDispatch.none).run first
      ⟨space, .work (.atom value expected bindings fuel live), [], earned⟩ = (before, .exhausted saved))
    (completed : (Checked.machine HE.GroundedDispatch.none).run second saved = (after, .finished finished)) :
    before ++ after = results ∧ finished = ⟨space, .returning [], [], earned ++ results⟩ := by
  apply derivation.checked_completed_unique earned (before ++ after) (first + second) finished
  rw [Checked.resume_prefix HE.GroundedDispatch.none _ saved first second before paused, completed]

/-- The actual resource-aware worker provides the existing evaluation protocol.
Resource calls retain the worker; they are not converted to replies. -/
def checkedEvaluationService (endpoint : Atom) (charge : Nat) :
    Machine Configuration Atom (Reply Atom Atom) Checked.ResourceRequest :=
  (Checked.machine HE.GroundedDispatch.none).relabel sourceEvent (evaluationReply endpoint charge) id

theorem AtomDerivation.checked_service_completed {space : Space} {comparison : SourceBindingComparison} {live : List Atom}
    {bindings : Bindings} {value expected : Atom} {fuel : Nat} {results : ResultSet}
    (derivation : AtomDerivation (comparison := comparison) space live value expected bindings fuel results)
    (actual : ResultSet) (budget : Nat) (finished : Configuration)
    (ran : (Checked.machine HE.GroundedDispatch.none).run budget
      ⟨space, .work (.atom value expected bindings fuel live), [], []⟩ = (actual, .finished finished))
    (endpoint : Atom) (charge : Nat) :
    (checkedEvaluationService endpoint charge).run budget
      ⟨space, .work (.atom value expected bindings fuel live), [], []⟩ =
      (results.map sourceEvent, .finished (.returned (NativeArgumentControlEncoding.replyData
        ⟨endpoint, .evaluated results, charge⟩))) := by
  obtain ⟨rfl, rfl⟩ := derivation.checked_completed_unique [] actual budget finished ran
  rw [checkedEvaluationService, Machine.run_relabel, ran]
  simp [Outcome.relabel, evaluationReply]

/-- Suspension exposes the depth request and exact worker state, without
inventing an evaluation reply or repeating earlier publication. -/
theorem checked_service_blocked (endpoint : Atom) (charge budget : Nat)
    (state : Configuration) (request : Checked.ResourceRequest)
    (pending : Checked.blocked HE.GroundedDispatch.none state = some request) :
    (checkedEvaluationService endpoint charge).run (budget + 1) state =
      ([], .suspended request state) := by
  rw [checkedEvaluationService, Machine.run_relabel,
    Checked.blocked_run HE.GroundedDispatch.none state request budget pending]
  rfl

/-- A checked resource request retains both levels of continuation. The
service's suspended depth cannot be mistaken for a reply to its native caller. -/
theorem checked_service_resource_retains_caller
    (operations : NativeArgumentControl.Operations) (policy : NativeArgumentControlMachine.RefusalPolicy)
    (endpoint : Atom) (charge : Nat) (caller : NativeArgumentControlMachine.Interaction)
    (state : Configuration) (request : Checked.ResourceRequest)
    (load : Atom → Configuration)
    (pending : Checked.blocked HE.GroundedDispatch.none state = some request) :
    ((NativeArgumentControlMachine.interactionMachine operations policy).handle
      NativeArgumentControlEncoding.interactionCallback (checkedEvaluationService endpoint charge) load).step
        (.handling endpoint caller state) =
      some (.call request (.handling endpoint caller state)) := by
  apply (Machine.handle_call_iff _ _ _ _ _ _ _).mpr
  refine ⟨endpoint, caller, state, state, rfl, ?_, rfl⟩
  simp [checkedEvaluationService, Machine.relabel, Checked.machine,
    RecursiveMachine.Checked.guardMachine, pending, Transition.relabel]

/-- Actual checked source completion answers the existing retained caller.
The bound counts the worker's steps and the call/reply boundary; depth requests
remain external interactions rather than empty replies. -/
theorem AtomDerivation.checked_handled {space : Space} {comparison : SourceBindingComparison} {live : List Atom}
    (operations : NativeArgumentControl.Operations) (policy : NativeArgumentControlMachine.RefusalPolicy)
    (configuration : NativeArgumentControl.Configuration)
    (argument : TypedApplyState) (prepared : NativeArgumentControl.Prepared)
    (ticket : Nat) (rest : List NativeArgumentControl.Frame)
    (pending : configuration.frames = .waiting (.evaluate argument prepared) ticket :: rest)
    (fuel charge : Nat) (results : ResultSet)
    (derivation : AtomDerivation (comparison := comparison) space live prepared.bound prepared.domain argument.env fuel results)
    (budget : Nat) (actual : ResultSet) (finished : Configuration)
    (completed : (Checked.machine HE.GroundedDispatch.none).run budget
      ⟨space, .work (.atom prepared.bound prepared.domain argument.env fuel live), [], []⟩ =
        (actual, .finished finished)) :
    let endpoint := (NativeArgumentControl.request configuration (.evaluate argument prepared) ticket).endpoint
    let reply : NativeArgumentControl.Reply := ⟨endpoint, .evaluated results, charge⟩
    let after := NativeArgumentControl.replied configuration rest reply
      [.iterate (NativeArgumentControl.selectedSnapshot argument prepared results) prepared]
    let initial : Configuration :=
      ⟨space, .work (.atom prepared.bound prepared.domain argument.env fuel live), [], []⟩
    ∃ used ≤ budget + 1,
      ((NativeArgumentControlMachine.interactionMachine operations policy).handle
        NativeArgumentControlEncoding.interactionCallback
        (checkedEvaluationService endpoint charge) (fun _ => initial)).run used (.running (.active configuration)) =
      (NativeArgumentControlEncoding.callEventData endpoint :: results.map sourceEvent ++
        [NativeArgumentControlEncoding.replyEventData (.returned (NativeArgumentControlEncoding.replyData reply))],
        .exhausted (.running (.active after))) := by
  dsimp only
  let endpoint := (NativeArgumentControl.request configuration (.evaluate argument prepared) ticket).endpoint
  let reply : NativeArgumentControl.Reply := ⟨endpoint, .evaluated results, charge⟩
  let after := NativeArgumentControl.replied configuration rest reply
    [.iterate (NativeArgumentControl.selectedSnapshot argument prepared results) prepared]
  let initial : Configuration :=
    ⟨space, .work (.atom prepared.bound prepared.domain argument.env fuel live), [], []⟩
  have call : (NativeArgumentControlMachine.interactionMachine operations policy).step (.active configuration) =
      some (.call endpoint (.active configuration)) := by
    simp only [NativeArgumentControlMachine.interactionMachine,
      NativeArgumentControlMachine.inspectInteraction,
      NativeArgumentControlMachine.awaiting_preserves operations configuration (.evaluate argument prepared)
        ticket rest pending, NativeArgumentControlMachine.interactionAdvance, endpoint]
  have answered : (checkedEvaluationService endpoint charge).run budget initial =
      (results.map sourceEvent, .finished (.returned (NativeArgumentControlEncoding.replyData reply))) :=
    derivation.checked_service_completed actual budget finished completed endpoint charge
  obtain ⟨used, bound, ran⟩ :=
    (NativeArgumentControlMachine.interactionMachine operations policy).handle_call_run
      NativeArgumentControlEncoding.interactionCallback
      (checkedEvaluationService endpoint charge) (fun _ => initial)
      (.active configuration) (.active configuration) endpoint call budget
      (results.map sourceEvent) (.returned (NativeArgumentControlEncoding.replyData reply)) answered
  have accepted : NativeArgumentControl.deliver configuration reply = .accepted after :=
    NativeArgumentControl.evaluated_reply configuration argument prepared ticket rest results charge pending
  refine ⟨used, bound, ?_⟩
  simpa only [NativeArgumentControlEncoding.interactionCallback,
    NativeArgumentControlEncoding.resumeInteraction, NativeArgumentControlEncoding.readReply_replyData,
    accepted] using ran


/-- The source meaning of the actual tail-attachment instruction. The caller
of the tail is the selected head's binding state, not the original input. -/
theorem argument_tail_spec {space : Space} {dispatch : Spec.Eval.GroundedDispatch}
    {live : List Atom} {typing : EvalTypeService} {original expected : Atom}
    {remaining types : List Atom} {incoming : BindingFrame} {head tail : FrameResult}
    (evaluated : EvalAtomRawRel space dispatch (remaining ++ types ++ live) (typing := typing)
      original expected incoming head)
    (safe : ¬IsEmptyOrErrorRel head.1 ∨ head.1 = original)
    (continued : InterpretArgsRel space dispatch (head.1 :: live) (typing := typing)
      remaining types head.2 tail) :
    InterpretArgsRel space dispatch live (typing := typing)
      (original :: remaining) (expected :: types) incoming
      (if argumentsSucceeded tail.1 = false then tail
        else (argumentPacket (head.1 :: argumentValues tail.1), tail.2)) := by
  cases packet : argumentsSucceeded tail.1 with
  | false =>
      simp only [if_true]
      apply InterpretArgsRel.tailError _ _ _ _ _ _ _ evaluated safe continued
      intro values same
      rw [same, argumentsSucceeded_packet] at packet
      cases packet
  | true =>
      simp only [Bool.true_eq_false, if_false]
      exact InterpretArgsRel.success _ _ _ _ _ _ _ evaluated safe continued
        (argumentsSucceeded_iff.mp packet)

/-- Local source judgments compose across every physical head and tail reply.
The service hypotheses concern the two actual child requests only. -/
theorem argument_outputs_sound {space : Space} {dispatch : Spec.Eval.GroundedDispatch}
    {live : List Atom} {typing : EvalTypeService} {original expected : Atom}
    {remaining types : List Atom} {incoming : Bindings}
    {heads : ResultSet} {tails : ResultPair → ResultSet}
    (headSound : ∀ head ∈ heads, ∀ (independentIncoming : Bindings),
      BindingRecordPerm incoming independentIncoming → ∃ independentHead : Bindings,
      EvalAtomRawRel space dispatch (remaining ++ types ++ live) (typing := typing)
        original expected independentIncoming (head.1, independentHead) ∧
      BindingRecordPerm head.2 independentHead)
    (tailSound : ∀ head ∈ heads,
      (head.1 != original && isEmptyOrError head.1) = false →
      ∀ tail ∈ tails head, ∀ (independentHead : Bindings), BindingRecordPerm head.2 independentHead →
      ∃ independentTail : Bindings,
        InterpretArgsRel space dispatch (head.1 :: live) (typing := typing)
          remaining types independentHead (tail.1, independentTail) ∧
        BindingRecordPerm tail.2 independentTail)
    (result : ResultPair) (member : result ∈ argumentOutputs original heads tails)
    (independentIncoming : Bindings) (related : BindingRecordPerm incoming independentIncoming) :
    ∃ independentOutput : Bindings,
      InterpretArgsRel space dispatch live (typing := typing)
        (original :: remaining) (expected :: types) independentIncoming (result.1, independentOutput) ∧
      BindingRecordPerm result.2 independentOutput := by
  obtain ⟨head, present, produced⟩ := List.mem_flatMap.mp member
  obtain ⟨independentHead, evaluated, headRelated⟩ := headSound head present independentIncoming related
  cases guard : head.1 != original && isEmptyOrError head.1 with
  | true =>
      simp only [guard, if_true, List.mem_singleton] at produced
      subst result
      have parts : head.1 ≠ original ∧ isEmptyOrError head.1 = true := by
        simpa only [Bool.and_eq_true, bne_iff_ne] using guard
      exact ⟨independentHead,
        InterpretArgsRel.headChangedError _ _ _ _ _ _ evaluated
          ((Spec.Type.Conformance.isEmptyOrErrorRel_iff_isEmptyOrError _).mpr parts.2) parts.1,
        headRelated⟩
  | false =>
      simp only [guard, Bool.false_eq_true, if_false, RecursiveTasks.argumentTail] at produced
      obtain ⟨tail, inTail, same⟩ := List.mem_map.mp produced
      obtain ⟨independentTail, continued, tailRelated⟩ :=
        tailSound head present guard tail inTail independentHead headRelated
      have safe : ¬IsEmptyOrErrorRel head.1 ∨ head.1 = original := by
        by_cases same : head.1 = original
        · exact Or.inr same
        · apply Or.inl
          intro bad
          have failed := (Spec.Type.Conformance.isEmptyOrErrorRel_iff_isEmptyOrError _).mp bad
          simp [same, failed] at guard
      have combined := argument_tail_spec evaluated safe continued
      cases packet : argumentsSucceeded tail.1 with
      | false =>
          simp only [packet, if_true] at same combined
          subst result
          exact ⟨independentTail, combined, tailRelated⟩
      | true =>
          simp only [packet, Bool.true_eq_false, if_false] at same combined
          subst result
          exact ⟨independentTail, combined, tailRelated⟩


/-- A checked head derivation supplies its exact local source service. Its
returned values and binding presentations are retained for the following stage. -/
theorem AtomDerivation.argument_head_source {space : Space} {live : List Atom}
    {original expected : Atom} {remaining types : List Atom} {incoming : Bindings}
    {fuel : Nat} {heads : ResultSet}
    (derivation : AtomDerivation (comparison := .records) space (remaining ++ types ++ live)
      original expected incoming fuel heads) :
    Realizes space (.atom original expected incoming fuel (remaining ++ types ++ live)) heads ∧
    ∀ head ∈ heads, ∀ (independentIncoming : Bindings), BindingRecordPerm incoming independentIncoming →
      ∃ independentHead : Bindings,
        EvalAtomRawRel space noHost (remaining ++ types ++ live)
          original expected independentIncoming (head.1, independentHead) ∧
        BindingRecordPerm head.2 independentHead := by
  exact ⟨derivation.realizes, fun head member incoming related =>
    derivation.sound_records head member [] incoming related⟩

/-- Existing successful source argument derivations are one implementation of
the local continuation boundary. The more general control law also permits
failure replies proved by the independent argument rules. -/
theorem ArgsDerivation.argument_tail_source {space : Space} {live : List Atom}
    {values types : List Atom} {incoming : Bindings} {fuel : Nat} {rows : ArgumentResults}
    (derivation : ArgsDerivation (comparison := .records) space live values types incoming fuel rows) :
    Realizes space (.args values types incoming fuel live) (argumentReplies rows) ∧
    ∀ result ∈ argumentReplies rows, ∀ (independentIncoming : Bindings),
      BindingRecordPerm incoming independentIncoming → ∃ independentOutput : Bindings,
      InterpretArgsRel space noHost live values types independentIncoming (result.1, independentOutput) ∧
      BindingRecordPerm result.2 independentOutput := by
  refine ⟨derivation.realizes, ?_⟩
  intro result member independent related
  obtain ⟨row, present, rfl⟩ := List.mem_map.mp member
  exact derivation.sound_records row present independent related

/-- Construct the argument computation from two local child interfaces.
Neither a whole argument-run result nor its source correspondence is an input.
Changed failures have no tail interface obligation. -/
theorem arguments_cons_source_join {space : Space} {live : List Atom}
    {original expected : Atom} {remaining types : List Atom} {incoming : Bindings}
    {fuel : Nat} {heads : ResultSet} {tails : ResultPair → ResultSet}
    (head : Realizes space (.atom original expected incoming fuel (remaining ++ types ++ live)) heads ∧
      ∀ selected ∈ heads, ∀ (independentIncoming : Bindings), BindingRecordPerm incoming independentIncoming →
        ∃ independentHead : Bindings,
          EvalAtomRawRel space noHost (remaining ++ types ++ live)
            original expected independentIncoming (selected.1, independentHead) ∧
          BindingRecordPerm selected.2 independentHead)
    (children : ∀ selected ∈ heads,
      (selected.1 != original && isEmptyOrError selected.1) = false →
      Realizes space (.args remaining types selected.2 fuel (selected.1 :: live)) (tails selected) ∧
      ∀ result ∈ tails selected, ∀ (independentHead : Bindings), BindingRecordPerm selected.2 independentHead →
        ∃ independentOutput : Bindings,
          InterpretArgsRel space noHost (selected.1 :: live)
            remaining types independentHead (result.1, independentOutput) ∧
          BindingRecordPerm result.2 independentOutput) :
    Realizes space (.args (original :: remaining) (expected :: types) incoming (fuel + 1) live)
      (argumentOutputs original heads tails) ∧
    ∀ result ∈ argumentOutputs original heads tails, ∀ (independentIncoming : Bindings),
      BindingRecordPerm incoming independentIncoming → ∃ independentOutput : Bindings,
        InterpretArgsRel space noHost live (original :: remaining) (expected :: types)
          independentIncoming (result.1, independentOutput) ∧
        BindingRecordPerm result.2 independentOutput := by
  refine ⟨arguments_cons_mixed_realizes space original expected remaining types incoming fuel live
    heads tails head.1 (fun selected member safe => (children selected member safe).1), ?_⟩
  exact argument_outputs_sound head.2
    (fun selected member safe => (children selected member safe).2)

/-- Every returned result constructs the corresponding independent chronological
history: either a completed packet, or the first changed failure and its
unexecuted suffix. This uses the source rules, not the old executable EvalSpec. -/
theorem independent_argument_history {space : Space} {dispatch : Spec.Eval.GroundedDispatch}
    {live : List Atom} {typing : EvalTypeService} {arguments types : List Atom}
    {incoming : BindingFrame} {result : FrameResult}
    (source : InterpretArgsRel space dispatch live (typing := typing)
      arguments types incoming result) :
    (∃ selected,
      RetainedArgumentSpecification.HistoryRel space dispatch live typing
        arguments types incoming selected result.2 ∧
      result.1 = argumentPacket (selected.map Prod.fst)) ∨
    (∃ selected,
      RetainedArgumentSpecification.FailureHistoryRel space dispatch live typing
        arguments types incoming selected result) := by
  by_cases packet : ∃ values, result.1 = argumentPacket values
  · obtain ⟨values, value⟩ := packet
    obtain ⟨selected, history, same⟩ := RetainedArgumentSpecification.arguments_to_history
      (show InterpretArgsRel space dispatch live (typing := typing) arguments types incoming
        (argumentPacket values, result.2) from by simpa only [← value] using source)
    exact Or.inl ⟨selected, history, by rw [same]; exact value⟩
  · exact Or.inr (RetainedArgumentSpecification.arguments_to_failure_history source
      (fun values same => packet ⟨values, same⟩))

/-- Checked completion of a realized argument task joins its complete occurrence
list and retained final state to independently proved histories. Matching,
typing and host effects must have been earned in the local child interfaces. -/
theorem checked_argument_completion_source {space : Space} {live : List Atom}
    {arguments types : List Atom} {incoming : Bindings} {fuel : Nat} {results : ResultSet}
    (realized : Realizes space (.args arguments types incoming fuel live) results)
    (source : ∀ result ∈ results, ∀ (independentIncoming : Bindings), BindingRecordPerm incoming independentIncoming →
      ∃ independentOutput : Bindings, InterpretArgsRel space noHost live arguments types independentIncoming
        (result.1, independentOutput) ∧ BindingRecordPerm result.2 independentOutput)
    (earned actual : ResultSet) (budget : Nat) (finished : Configuration)
    (ran : (Checked.machine HE.GroundedDispatch.none).run budget
      ⟨space, .work (.args arguments types incoming fuel live), [], earned⟩ = (actual, .finished finished)) :
    actual = results ∧ finished = ⟨space, .returning [], [], earned ++ results⟩ ∧
    ∀ result ∈ actual, ∀ (independentIncoming : Bindings), BindingRecordPerm incoming independentIncoming →
      ∃ independentOutput : Bindings, BindingRecordPerm result.2 independentOutput ∧
        ((∃ selected,
          RetainedArgumentSpecification.HistoryRel space noHost live storageTypeService
            arguments types independentIncoming selected independentOutput ∧
          result.1 = argumentPacket (selected.map Prod.fst)) ∨
        (∃ selected,
          RetainedArgumentSpecification.FailureHistoryRel space noHost live storageTypeService
            arguments types independentIncoming selected (result.1, independentOutput))) := by
  obtain ⟨same, endpoint⟩ := realizes_completed_unique realized earned actual budget finished
    (Checked.finished_refines HE.GroundedDispatch.none budget _ actual finished ran)
  refine ⟨same, endpoint, ?_⟩
  intro result member independent related
  obtain ⟨output, derived, corresponding⟩ := source result (same ▸ member) independent related
  exact ⟨output, corresponding, independent_argument_history derived⟩

/-- A scheduler cut leaves the actual remaining control in place. Completing
from that saved configuration yields the same source occurrence list; the
already published prefix is neither replayed nor replaced. -/
theorem checked_argument_resume_source {space : Space} {live : List Atom}
    {arguments types : List Atom} {incoming : Bindings} {fuel : Nat} {results : ResultSet}
    (realized : Realizes space (.args arguments types incoming fuel live) results)
    (source : ∀ result ∈ results, ∀ (independentIncoming : Bindings), BindingRecordPerm incoming independentIncoming →
      ∃ independentOutput : Bindings, InterpretArgsRel space noHost live arguments types independentIncoming
        (result.1, independentOutput) ∧ BindingRecordPerm result.2 independentOutput)
    (earned before after : ResultSet) (first second : Nat) (saved finished : Configuration)
    (paused : (Checked.machine HE.GroundedDispatch.none).run first
      ⟨space, .work (.args arguments types incoming fuel live), [], earned⟩ = (before, .exhausted saved))
    (completed : (Checked.machine HE.GroundedDispatch.none).run second saved = (after, .finished finished)) :
    before ++ after = results ∧ finished = ⟨space, .returning [], [], earned ++ results⟩ ∧
    ∀ result ∈ before ++ after, ∀ (independentIncoming : Bindings), BindingRecordPerm incoming independentIncoming →
      ∃ independentOutput : Bindings, BindingRecordPerm result.2 independentOutput ∧
        ((∃ selected,
          RetainedArgumentSpecification.HistoryRel space noHost live storageTypeService
            arguments types independentIncoming selected independentOutput ∧
          result.1 = argumentPacket (selected.map Prod.fst)) ∨
        (∃ selected,
          RetainedArgumentSpecification.FailureHistoryRel space noHost live storageTypeService
            arguments types independentIncoming selected (result.1, independentOutput))) := by
  apply checked_argument_completion_source realized source earned (before ++ after) (first + second) finished
  rw [Checked.resume_prefix HE.GroundedDispatch.none _ saved first second before paused, completed]


section Controls

private def heldSyntax : Atom :=
  .expression [.symbol "quote", .expression [.symbol "Pair", .var "shared", .var "shared"]]
private def innerSyntax : Atom := .expression [.symbol "inner", heldSyntax]
private def outerSyntax : Atom := .expression [.symbol "outer", innerSyntax]
private def numberType : Atom := .symbol "Number"
private def booleanType : Atom := .symbol "Bool"
private def textType : Atom := .symbol "Text"
private def sourceSpace : Space := ⟨[
  .expression [.symbol ":", .symbol "inner", arrow [Atom.atomType] numberType],
  .expression [.symbol ":", .symbol "outer", arrow [textType] numberType],
  .expression [.symbol ":", .symbol "outer", arrow [numberType] booleanType],
  .expression [.symbol ":", .symbol "outer", arrow [numberType] numberType],
  .expression [.symbol ":", heldSyntax, numberType],
  .expression [.symbol ":", heldSyntax, booleanType],
  .expression [.symbol ":", innerSyntax, numberType],
  .expression [.symbol ":", innerSyntax, numberType],
  .expression [.symbol ":", innerSyntax, booleanType]]⟩

private theorem source_free : EquationFree sourceSpace := by
  intro left right
  simp [sourceSpace]

private def controlFuel : Nat := 4096

private theorem inner_type_occurrences :
    getAtomTypes sourceSpace innerSyntax = [numberType, numberType, booleanType] := by decide

private theorem control_argument_checked (domain : Atom)
    (closed : TypeSubst.typeVars domain = [])
    (numberBudget : sizeOf domain + sizeOf numberType + 2 ≤ controlFuel + 6)
    (booleanBudget : sizeOf domain + sizeOf booleanType + 2 ≤ controlFuel + 6) :
    ArgumentDomainEvidence sourceSpace innerSyntax domain (controlFuel + 6) := by
  refine .closed closed ?_ ?_
  · intro actual member
    rw [inner_type_occurrences] at member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl <;> rfl
  · intro actual member
    rw [inner_type_occurrences] at member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl
    · exact numberBudget
    · exact numberBudget
    · exact booleanBudget

private def innerTyping : ApplicationTyping sourceSpace "inner" [heldSyntax] numberType (controlFuel + 2) where
  domains := [Atom.atomType]
  returned := numberType
  before := []
  after := []
  declined := []
  sourceTypes := by decide
  rejected := .nil
  argumentChecks := .cons (.wildcard (Or.inl rfl)) .nil
  argumentPaths := by decide
  expectedClosed := rfl
  returnedClosed := rfl
  returnedFits := Or.inr (Or.inr (Or.inr (Or.inr rfl)))
  returnBudget := by decide
  earlierClosed := by simp
  earlierHeadRejects := by simp
  headClosed := rfl
  headBudget := by decide
  demandNotRaw := by decide
  demandNotExpression := by decide
  nonemptyOperator := by decide
  cleanOperator := by decide

private def outerTyping : ApplicationTyping sourceSpace "outer" [innerSyntax] numberType (controlFuel + 6) where
  domains := [numberType]
  returned := numberType
  before := [arrow [textType] numberType, arrow [numberType] booleanType]
  after := []
  declined := [⟨arrow [textType] numberType,
    .error [mkError outerSyntax (.badArgType 1 textType numberType)]⟩,
    ⟨arrow [numberType] booleanType,
    .error [mkError outerSyntax (.badType numberType booleanType)]⟩]
  sourceTypes := by decide
  rejected := .badArguments (.cons (control_argument_checked textType rfl (by decide) (by decide)) .nil)
    (by decide) (by decide)
    (.badReturn (.cons (control_argument_checked numberType rfl (by decide) (by decide)) .nil)
      (by decide) rfl rfl (by decide) .nil)
  argumentChecks := .cons (control_argument_checked numberType rfl (by decide) (by decide)) .nil
  argumentPaths := by decide
  expectedClosed := rfl
  returnedClosed := rfl
  returnedFits := Or.inr (Or.inr (Or.inr (Or.inr rfl)))
  returnBudget := by decide
  earlierClosed := by
    intro candidate member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> rfl
  earlierHeadRejects := by
    intro candidate member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> decide
  headClosed := rfl
  headBudget := by decide
  demandNotRaw := by decide
  demandNotExpression := by decide
  nonemptyOperator := by decide
  cleanOperator := by decide

/-- The two repeated quote variables remain raw syntax under Atom demand,
for any retained binding frame. -/
theorem source_quote_is_held (bindings : Bindings) :
    ReadOnlyAtomDerivation sourceSpace bindings heldSyntax Atom.atomType (controlFuel + 1) [heldSyntax] :=
  .leaf heldSyntax Atom.atomType controlFuel (Or.inr ⟨Atom.expressionType, .expression _, Or.inl rfl⟩)

private theorem inner_derivation (bindings : Bindings) :
    ReadOnlyAtomDerivation sourceSpace bindings innerSyntax numberType (controlFuel + 5) [innerSyntax] := by
  have arguments : ReadOnlyArgsDerivation sourceSpace bindings [heldSyntax] [Atom.atomType] (controlFuel + 2) [[heldSyntax]] := by
    simpa using ReadOnlyArgsDerivation.cons heldSyntax Atom.atomType [] [] (controlFuel + 1) [heldSyntax] [[]]
      (source_quote_is_held bindings) (.nil controlFuel)
  have derived := ReadOnlyAtomDerivation.application "inner" [heldSyntax] numberType (controlFuel + 2) innerTyping
    [[heldSyntax]] (by decide) (by decide) arguments
  simpa only [List.map_cons, List.map_nil, Nat.add_assoc, innerSyntax] using derived

/-- Each nested call selects its first successful type-binding path. Earlier
Text-domain and Bool-return candidates are independently declined. The later
successful type paths do not duplicate execution, and quoted fields remain raw. -/
theorem nested_nonleaf_derivation (bindings : Bindings) :
    ReadOnlyAtomDerivation sourceSpace bindings outerSyntax numberType (controlFuel + 9)
      [outerSyntax] := by
  have arguments : ReadOnlyArgsDerivation sourceSpace bindings [innerSyntax] [numberType] (controlFuel + 6)
      [[innerSyntax]] := by
    simpa using ReadOnlyArgsDerivation.cons innerSyntax numberType [] [] (controlFuel + 5)
      [innerSyntax] [[]] (inner_derivation bindings) (.nil (controlFuel + 4))
  have derived := ReadOnlyAtomDerivation.application "outer" [innerSyntax] numberType (controlFuel + 6) outerTyping
    [[innerSyntax]] (by decide) (by decide) arguments
  simpa only [List.map_cons, List.map_nil, Nat.add_assoc, outerSyntax] using derived

theorem earlier_typed_candidate_rejected (bindings output : Bindings) :
    ¬ApplicationSuccessRel sourceSpace outerSyntax (arrow [numberType] booleanType)
      numberType bindings output :=
  closed_return_excludes_success sourceSpace (.symbol "outer") numberType booleanType [innerSyntax]
    [numberType] bindings output rfl rfl (by decide)

theorem earlier_argument_candidate_rejected (bindings output : Bindings) :
    ¬ApplicationSuccessRel sourceSpace outerSyntax (arrow [textType] numberType)
      numberType bindings output :=
  checked_arguments_exclude_success sourceSpace (.symbol "outer") numberType numberType [innerSyntax]
    [textType] bindings output (controlFuel + 6)
    (.cons (control_argument_checked textType rfl (by decide) (by decide)) .nil) (by decide)

theorem checked_duplicate_paths_are_retained (bindings : Bindings) :
    getAtomTypes sourceSpace innerSyntax = [numberType, numberType, booleanType] ∧
    acceptedTypes sourceSpace innerSyntax numberType = [numberType, numberType] ∧
    checkIfFunctionTypeIsApplicable outerSyntax (arrow [numberType] numberType) numberType
      sourceSpace bindings (controlFuel + 7) = .inr [bindings, bindings] := by
  refine ⟨inner_type_occurrences, by decide, ?_⟩
  have checked := checked_applicability_success sourceSpace (.symbol "outer") numberType numberType
    [innerSyntax] [numberType] bindings (controlFuel + 6)
    (.cons (control_argument_checked numberType rfl (by decide) (by decide)) .nil)
    (by decide) rfl rfl (by decide) (by decide)
  have count : admittedPathCount sourceSpace [innerSyntax] [numberType] = 2 := by decide
  simpa only [count, List.replicate_succ, List.replicate_zero, outerSyntax, arrow, Nat.add_assoc] using checked

theorem rejected_argument_errors_keep_duplicates (bindings : Bindings) :
    checkIfFunctionTypeIsApplicable outerSyntax (arrow [textType] numberType) numberType
      sourceSpace bindings (controlFuel + 7) = .inl [
        mkError outerSyntax (.badArgType 1 textType numberType),
        mkError outerSyntax (.badArgType 1 textType numberType),
        mkError outerSyntax (.badArgType 1 textType booleanType)] := by
  have checked := checked_applicability_argument_failure sourceSpace (.symbol "outer") numberType numberType
    [innerSyntax] [textType] bindings (controlFuel + 6)
    (.cons (control_argument_checked textType rfl (by decide) (by decide)) .nil) (by decide)
  have errors : argumentErrorBlocks sourceSpace outerSyntax [innerSyntax] [textType] 1 1 = [
      mkError outerSyntax (.badArgType 1 textType numberType),
      mkError outerSyntax (.badArgType 1 textType numberType),
      mkError outerSyntax (.badArgType 1 textType booleanType)] := by decide
  change checkIfFunctionTypeIsApplicable outerSyntax (arrow [textType] numberType) numberType
    sourceSpace bindings (controlFuel + 6 + 1) =
      .inl (argumentErrorBlocks sourceSpace outerSyntax [innerSyntax] [textType] 1 1) at checked
  rw [errors] at checked
  simpa only [Nat.add_assoc] using checked

/-- Errors from an earlier mixed argument precede the later argument's
errors. The two surviving Number paths repeat the second argument's whole
error block, with its original one-based position. Each occurrence has an
independent rejection derivation. -/
theorem argument_errors_follow_surviving_paths (bindings : Bindings) :
    let expression : Atom := .expression [.symbol "outer", innerSyntax, heldSyntax]
    let errors := [mkError expression (.badArgType 1 numberType booleanType),
      mkError expression (.badArgType 2 textType numberType),
      mkError expression (.badArgType 2 textType booleanType),
      mkError expression (.badArgType 2 textType numberType),
      mkError expression (.badArgType 2 textType booleanType)]
    checkIfFunctionTypeIsApplicable expression (arrow [numberType, textType] numberType) numberType
      sourceSpace bindings (controlFuel + 7) = .inl errors ∧
    ∀ error ∈ errors, ApplicabilityRel sourceSpace expression (arrow [numberType, textType] numberType)
      numberType bindings (.error error) := by
  let expression : Atom := .expression [.symbol "outer", innerSyntax, heldSyntax]
  let errors := [mkError expression (.badArgType 1 numberType booleanType),
    mkError expression (.badArgType 2 textType numberType),
    mkError expression (.badArgType 2 textType booleanType),
    mkError expression (.badArgType 2 textType numberType),
    mkError expression (.badArgType 2 textType booleanType)]
  have heldTypes : getAtomTypes sourceSpace heldSyntax = [numberType, booleanType] := by decide
  have heldChecked : ArgumentDomainEvidence sourceSpace heldSyntax textType (controlFuel + 6) := by
    refine .closed rfl ?_ ?_
    · intro actual member
      rw [heldTypes] at member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl <;> rfl
    · intro actual member
      rw [heldTypes] at member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl <;> decide
  have checked : List.Forall₂ (fun argument domain =>
      ArgumentDomainEvidence sourceSpace argument domain (controlFuel + 6))
      [innerSyntax, heldSyntax] [numberType, textType] :=
    .cons (control_argument_checked numberType rfl (by decide) (by decide)) (.cons heldChecked .nil)
  have exhausted : admittedPathCount sourceSpace [innerSyntax, heldSyntax] [numberType, textType] = 0 := by decide
  have orderedErrors : argumentErrorBlocks sourceSpace expression [innerSyntax, heldSyntax]
      [numberType, textType] 1 1 = errors := by decide
  constructor
  · have result := checked_applicability_argument_failure sourceSpace (.symbol "outer") numberType numberType
      [innerSyntax, heldSyntax] [numberType, textType] bindings (controlFuel + 6) checked exhausted
    change checkIfFunctionTypeIsApplicable expression (arrow [numberType, textType] numberType) numberType
      sourceSpace bindings (controlFuel + 6 + 1) =
        .inl (argumentErrorBlocks sourceSpace expression [innerSyntax, heldSyntax] [numberType, textType] 1 1) at result
    rw [orderedErrors] at result
    simpa only [Nat.add_assoc] using result
  · intro error member
    have noSuccess : ∀ output, ¬ApplicationSuccessRel sourceSpace expression
        (arrow [numberType, textType] numberType) numberType bindings output :=
      fun output => checked_arguments_exclude_success sourceSpace (.symbol "outer") numberType numberType
        [innerSyntax, heldSyntax] [numberType, textType] bindings output (controlFuel + 6) checked exhausted
    exact checked_argument_errors_sound sourceSpace (.symbol "outer") numberType numberType
      [innerSyntax, heldSyntax] [numberType, textType] bindings (controlFuel + 6) checked noSuccess error
      (orderedErrors ▸ member)

theorem nested_source_collects_one (bindings : Bindings) :
    ∃ budget, collectReply sourceSpace outerSyntax numberType bindings (controlFuel + 9) budget =
      some [(outerSyntax, bindings)] := by
  obtain ⟨budget, complete⟩ := (nested_nonleaf_derivation bindings).collect source_free
  exact ⟨budget, by simpa only [Nat.add_zero, replies, List.map_cons, List.map_nil] using complete 0⟩

theorem nested_independent_result (bindings : Bindings) :
    EvalAtomRawRel sourceSpace noHost [] outerSyntax numberType bindings (outerSyntax, bindings) :=
  (nested_nonleaf_derivation bindings).sound source_free outerSyntax (by simp) []

private def requestSubstitution : TypeSubst := [("request", outerSyntax)]
private def unresolvedArgument : TypedApplyState :=
  ⟨.symbol "caller", [.var "request"], [numberType], 0, [],
    FirstSuccessPreparedArguments.presentedBindings requestSubstitution⟩
private def resolvedArgument : NativeArgumentControl.Prepared :=
  ⟨numberType, outerSyntax, {dialect := .he}⟩

/-- A stored nested argument is resolved from an actual normal substitution
before interpretation. Its still-unassigned raw quote variables and original
source argument remain in the retained state. -/
theorem stored_nested_argument_is_prepared :
    FirstSuccessPreparedArguments.prepareSource unresolvedArgument {dialect := .he} 8 = resolvedArgument ∧
    FirstSuccessPreparedArguments.PreparationRel requestSubstitution unresolvedArgument {dialect := .he}
      resolvedArgument ∧
    ∃ budget, collectReply sourceSpace outerSyntax numberType unresolvedArgument.env
      (controlFuel + 9) budget =
        some (replies unresolvedArgument.env [outerSyntax]) := by
  have normal : requestSubstitution.Normal := by
    simp [requestSubstitution, TypeSubst.Normal, TypeSubst.keys, TypeSubst.typeVars,
      TypeSubst.typeVarsList, outerSyntax, innerSyntax, heldSyntax]
  have prepared : FirstSuccessPreparedArguments.prepareSource unresolvedArgument {dialect := .he} 8 =
      resolvedArgument := rfl
  have independent := FirstSuccessPreparedArguments.preparation_sound normal unresolvedArgument {dialect := .he}
    8 rfl (by decide) (by decide)
  rw [prepared] at independent
  obtain ⟨budget, collected⟩ := (nested_nonleaf_derivation unresolvedArgument.env).collect source_free
  exact ⟨prepared, independent, budget, by simpa only [Nat.add_zero] using collected 0⟩

/-- Successful type-check alternatives do not create answer occurrences. -/
theorem unselected_type_paths_are_not_results (bindings : Bindings) (budget : Nat) :
    collectReply sourceSpace outerSyntax numberType bindings (controlFuel + 9) budget ≠
      some (replies bindings [outerSyntax, outerSyntax, outerSyntax, outerSyntax]) := by
  intro duplicated
  have same := (nested_nonleaf_derivation bindings).collect_exact source_free budget
    (replies bindings [outerSyntax, outerSyntax, outerSyntax, outerSyntax]) duplicated
  have lengths := congrArg List.length same
  simp [replies] at lengths

/-- Atom demand holds the complete syntax before the selector is visited. -/
theorem raw_demand_retains_syntax (bindings : Bindings) :
    ReadOnlyAtomDerivation sourceSpace bindings outerSyntax Atom.atomType (controlFuel + 9) [outerSyntax] :=
  .leaf outerSyntax Atom.atomType (controlFuel + 8) (Or.inr
    ⟨Atom.expressionType, .expression _, Or.inl rfl⟩)

/-- Budget exhaustion is retained, not an earned empty or singleton reply. -/
theorem zero_budget_is_pending (bindings : Bindings) :
    collectReply sourceSpace outerSyntax numberType bindings (controlFuel + 9) 0 = none := rfl

/-- A pause after publishing the selected result resumes with no extra type
alternative. The saved worker retains its already published occurrence. -/
theorem selected_reply_prefix_resumes (bindings : Bindings) :
    ∃ firstBudget saved,
      (machine HE.GroundedDispatch.none).run firstBudget
        ⟨sourceSpace, .work (.atom outerSyntax numberType bindings (controlFuel + 9)), [], []⟩ =
        ([(outerSyntax, bindings)], .exhausted saved) ∧
      (machine HE.GroundedDispatch.none).run 1 saved =
        ([], .finished ⟨sourceSpace, .returning [], [], [(outerSyntax, bindings)]⟩) := by
  obtain ⟨administrative, realized⟩ := (machine HE.GroundedDispatch.none).silent_run
    ((nested_nonleaf_derivation bindings).realizes source_free [] [])
  refine ⟨administrative + 1,
    ⟨sourceSpace, .returning [], [], [(outerSyntax, bindings)]⟩, ?_, rfl⟩
  rw [realized 1]
  rfl


private def callerArgument (bindings : Bindings) : TypedApplyState :=
  ⟨.symbol "caller", [outerSyntax], [numberType], 0, [], bindings⟩
private def callerPrepared : NativeArgumentControl.Prepared :=
  ⟨numberType, outerSyntax, {dialect := .he}⟩
private def callerWaiting (bindings : Bindings) : NativeArgumentControl.Configuration :=
  NativeArgumentControl.issue ⟨[], [], 17, 0, [], 0⟩ []
    (.evaluate (callerArgument bindings) callerPrepared)

private theorem caller_history (bindings : Bindings) :
    NativeArgumentControlHistory.HistoryInv (callerWaiting bindings) :=
  NativeArgumentControlHistory.issue_history
    (NativeArgumentControlHistory.history_empty [] (by simp [NativeArgumentControlHistory.PlainFrames]) 17)
    [] (by simp [NativeArgumentControlHistory.PlainFrames]) _

/-- The complete nonleaf reply is earned by source rules before the endpoint
checker accepts it. Acceptance retains the selected occurrence in the original
argument snapshot and preserves the serial/history invariant. -/
theorem earned_nonleaf_callback (bindings : Bindings) :
    ∃ budget after,
      collectReply sourceSpace outerSyntax numberType bindings (controlFuel + 9) budget =
        some (replies bindings [outerSyntax]) ∧
      NativeArgumentControl.DeliveryRel (callerWaiting bindings)
        ⟨(NativeArgumentControl.request (callerWaiting bindings)
          (.evaluate (callerArgument bindings) callerPrepared) 0).endpoint,
          .evaluated (replies bindings [outerSyntax]), 0⟩ after ∧
      NativeArgumentControlHistory.HistoryInv after := by
  obtain ⟨budget, after, collected, delivered, history, _, _⟩ :=
    deliver_nonleaf source_free (callerWaiting bindings) (caller_history bindings)
      (callerArgument bindings) callerPrepared 0 [] rfl (controlFuel + 9) 0
      [outerSyntax] (nested_nonleaf_derivation bindings)
  exact ⟨budget, after, collected, delivered, history⟩

/-- The shared handler executes the real nested worker and resumes the exact
parent after its actual one-occurrence service log. No fixture provider is
used to produce the reply. -/
theorem earned_nonleaf_handler (bindings : Bindings)
    (operations : NativeArgumentControl.Operations) :
    let endpoint := (NativeArgumentControl.request (callerWaiting bindings)
      (.evaluate (callerArgument bindings) callerPrepared) 0).endpoint
    let reply : NativeArgumentControl.Reply :=
      ⟨endpoint, .evaluated (replies bindings [outerSyntax]), 0⟩
    let after := NativeArgumentControl.replied (callerWaiting bindings) [] reply
      [.iterate (NativeArgumentControl.selectedSnapshot (callerArgument bindings) callerPrepared
        (replies bindings [outerSyntax])) callerPrepared]
    ∃ budget, ((NativeArgumentControlMachine.interactionMachine operations .stop).handle
      NativeArgumentControlEncoding.interactionCallback (evaluationService endpoint 0)
      (fun _ => (⟨sourceSpace, .work (.atom outerSyntax numberType bindings (controlFuel + 9)), [], []⟩ :
        RecursiveTasks.Configuration))).run budget (.running (.active (callerWaiting bindings))) =
      (NativeArgumentControlEncoding.callEventData endpoint ::
        (replies bindings [outerSyntax]).map sourceEvent ++
        [NativeArgumentControlEncoding.replyEventData (.returned (NativeArgumentControlEncoding.replyData reply))],
        .exhausted (.running (.active after))) :=
  handled_nonleaf source_free operations .stop (callerWaiting bindings) (callerArgument bindings)
    callerPrepared 0 [] rfl (controlFuel + 9) 0
    [outerSyntax] (nested_nonleaf_derivation bindings)

private def capturedSourceWorld : Mettapedia.Machines.RevisionEnvironment Nat (List Atom) :=
  ⟨fun _ => sourceSpace.atoms⟩
private def capturedCaller (bindings : Bindings) :
    NativeArgumentControlHistory.OwnedReplyBoundary.Capture Nat (List Atom) :=
  ⟨5, (Mettapedia.Machines.CapturedReadView.admit capturedSourceWorld).consult capturedSourceWorld 0,
    callerWaiting bindings⟩
private def issuedCaller (bindings : Bindings) : NativeArgumentControlHistory.OwnedReplyBoundary.Handle :=
  ⟨19, 17, ⟨1, 11, NativeArgumentControl.configurationData (callerWaiting bindings), 5⟩⟩
private def callerRegistry (bindings : Bindings) : NativeArgumentControlHistory.OwnedReplyBoundary.Registry :=
  ⟨19, [(issuedCaller bindings).row]⟩

/-- The existing nested worker earns the selected occurrence before the issued
reply boundary checks its complete source dependency and consumes its token. -/
theorem earned_nonleaf_owned_reply (bindings : Bindings) :
    ∃ budget after next,
      collectReply sourceSpace outerSyntax numberType bindings (controlFuel + 9) budget =
        some (replies bindings [outerSyntax]) ∧
      (NativeArgumentControlHistory.OwnedReplyBoundary.deliverChecked (callerRegistry bindings)
        capturedSourceWorld (capturedCaller bindings) (issuedCaller bindings)
        ⟨(NativeArgumentControl.request (callerWaiting bindings)
          (.evaluate (callerArgument bindings) callerPrepared) 0).endpoint,
          .evaluated (replies bindings [outerSyntax]), 0⟩).1 =
          .ok (after, next) ∧ NativeArgumentControlHistory.HistoryInv after := by
  have current : (capturedCaller bindings).view.CanPublish capturedSourceWorld := by
    refine ⟨rfl, rfl, ?_⟩
    apply (Mettapedia.Machines.CapturedReadView.valid_dependencies_iff _ _).mpr
    intro key _
    rfl
  have authority : Mettapedia.Machines.Cursor.OwnedLifecycle.IssuedReturn.Authenticated
      (callerRegistry bindings) (issuedCaller bindings) := by
    simp [Mettapedia.Machines.Cursor.OwnedLifecycle.IssuedReturn.Authenticated,
      callerRegistry, issuedCaller]
  obtain ⟨budget, after, next, _, collected, accepted, history, _⟩ :=
    deliver_nonleaf_owned source_free (callerRegistry bindings) (capturedCaller bindings)
      (issuedCaller bindings) capturedSourceWorld 0 rfl (by simp [capturedCaller,
        Mettapedia.Machines.CapturedReadView.consult, Mettapedia.Machines.CapturedReadView.admit])
      ⟨rfl, rfl, rfl⟩ current authority (caller_history bindings)
      (callerArgument bindings) callerPrepared 0 [] rfl (controlFuel + 9) 0
      [outerSyntax] (nested_nonleaf_derivation bindings)
  exact ⟨budget, after, next, collected, accepted, history⟩

/-- An edited source cannot authorize the reply earned from the old admitted
source, even though that old reply remains a valid source derivation. -/
theorem edited_source_refuses_issued_nonleaf_reply (bindings : Bindings) :
    let changed : Mettapedia.Machines.RevisionEnvironment Nat (List Atom) :=
      ⟨fun _ => sourceSpace.atoms ++ [.symbol "added-declaration"]⟩
    (NativeArgumentControlHistory.OwnedReplyBoundary.deliverChecked (callerRegistry bindings)
      changed (capturedCaller bindings) (issuedCaller bindings)
      ⟨(NativeArgumentControl.request (callerWaiting bindings)
        (.evaluate (callerArgument bindings) callerPrepared) 0).endpoint,
        .evaluated (replies bindings [outerSyntax]), 0⟩).1 =
          .error .staleDependencies := by
  apply NativeArgumentControlHistory.OwnedReplyBoundary.stale_refused
  · exact ⟨rfl, rfl, rfl⟩
  · intro allowed
    have reads := (Mettapedia.Machines.CapturedReadView.valid_dependencies_iff _ _).mp allowed.2.2
      0 (by simp [capturedCaller, Mettapedia.Machines.CapturedReadView.consult,
        Mettapedia.Machines.CapturedReadView.admit])
    have impossible := congrArg List.length reads
    simp [capturedCaller, capturedSourceWorld, Mettapedia.Machines.CapturedReadView.consult,
      Mettapedia.Machines.CapturedReadView.admit] at impossible

private def mismatchedPrepared : NativeArgumentControl.Prepared :=
  ⟨booleanType, outerSyntax, {dialect := .he}⟩
private def mismatchedReply (bindings : Bindings) : NativeArgumentControl.Reply :=
  ⟨(NativeArgumentControl.request (callerWaiting bindings)
      (.evaluate (callerArgument bindings) mismatchedPrepared) 0).endpoint,
    .evaluated (replies bindings [outerSyntax]), 7⟩

/-- Results earned at a different resolved demand cannot be spliced into the
saved request, even though their represented values coincide. -/
theorem mismatched_domain_refused (bindings : Bindings) :
    NativeArgumentControl.deliver (callerWaiting bindings) (mismatchedReply bindings) =
      .rejected .endpointMismatch := by
  have different : (mismatchedReply bindings).endpoint ≠
      (NativeArgumentControl.request (callerWaiting bindings)
        (.evaluate (callerArgument bindings) callerPrepared) 0).endpoint := by
    intro same
    simp [mismatchedReply, NativeArgumentControl.request, NativeArgumentControl.waitingData,
      NativeArgumentControl.preparedData, callerPrepared, mismatchedPrepared, numberType, booleanType] at same
  simp only [NativeArgumentControl.deliver,
    show (callerWaiting bindings).frames =
      .waiting (.evaluate (callerArgument bindings) callerPrepared) 0 :: [] from rfl]
  rw [if_pos different]

/-- Refusal retains the entire controller and does not consume the forged
charge, fresh serial or reply history. -/
theorem mismatched_callback_retains_state (bindings : Bindings) :
    NativeArgumentControlEncoding.resumeInteraction
      (.active (callerWaiting bindings))
      (.returned (NativeArgumentControlEncoding.replyData (mismatchedReply bindings))) =
      .refused .endpointMismatch (callerWaiting bindings)
        (NativeArgumentControlEncoding.replyData (mismatchedReply bindings)) :=
  (NativeArgumentControlEncoding.rejected_reply_retains_saved
    (callerWaiting bindings) (mismatchedReply bindings) .endpointMismatch
    (mismatched_domain_refused bindings)).1

private def identityEquation : Atom :=
  .expression [.symbol "=", .expression [.symbol "identity", .var "x"], .var "x"]

private def equationSpace : Space := Space.ofList [identityEquation, identityEquation,
  .expression [.symbol ":", .symbol "identity", arrow [Atom.atomType] Atom.symbolType]]
private def equationQuery : Atom := .expression [.symbol "identity", .symbol "answer"]
private def equationCaller : Bindings := Bindings.empty.assign "caller" (.symbol "kept")
private def equationBinding (index : Nat) : Bindings :=
  ⟨[("x#" ++ Nat.repr index, .symbol "answer"), ("caller", .symbol "kept")], []⟩
private def equationAnswers : ResultSet :=
  [(.symbol "answer", equationBinding 0), (.symbol "answer", equationBinding 1)]

private theorem equation_inputs_exact :
    (queryEquations equationSpace equationQuery 12).flatMap (equationInputs equationCaller 12) =
      equationAnswers := by decide +kernel

private theorem equation_body_leaves (fuel : Nat)
    (inputs : (queryEquations equationSpace equationQuery fuel).flatMap
      (equationInputs equationCaller fuel) = equationAnswers) :
    ∀ candidate ∈ queryEquations equationSpace equationQuery fuel,
      ∀ request ∈ equationInputs equationCaller fuel candidate,
        LeafRel request.1 Atom.symbolType := by
  intro candidate member request present
  have inAnswers : request ∈ equationAnswers := by
    rw [← inputs]
    exact List.mem_flatMap.mpr ⟨candidate, member, present⟩
  simp only [equationAnswers, List.mem_cons, List.not_mem_nil, or_false] at inAnswers
  rcases inAnswers with rfl | rfl <;>
    exact Or.inr ⟨Atom.symbolType, .symbol "answer", Or.inr (Or.inl rfl)⟩

private theorem equation_body_notRefused (fuel : Nat)
    (inputs : (queryEquations equationSpace equationQuery fuel).flatMap
      (equationInputs equationCaller fuel) = equationAnswers) :
    ∀ candidate ∈ queryEquations equationSpace equationQuery fuel,
      ∀ request ∈ equationInputs equationCaller fuel candidate,
        request.1 ≠ Atom.notReducible := by
  intro candidate member request present
  have inAnswers : request ∈ equationAnswers := by
    rw [← inputs]
    exact List.mem_flatMap.mpr ⟨candidate, member, present⟩
  simp only [equationAnswers, List.mem_cons, List.not_mem_nil, or_false] at inAnswers
  rcases inAnswers with rfl | rfl <;> decide

/-- Duplicate physical equations retain separate changed binding states.
The caller's binding survives; the fresh rule binding is not replaced by it. -/
theorem equation_results_retain_changed_bindings :
    equationAnswers.map Prod.fst = [.symbol "answer", .symbol "answer"] ∧
      equationAnswers.length = 2 ∧
      (equationBinding 0).lookup "caller" = some (.symbol "kept") ∧
      (equationBinding 1).lookup "caller" = some (.symbol "kept") ∧
      (equationBinding 0).lookup "x#0" = some (.symbol "answer") ∧
      (equationBinding 1).lookup "x#1" = some (.symbol "answer") ∧
      equationBinding 0 ≠ equationCaller ∧ equationBinding 1 ≠ equationCaller := by decide +kernel

/-- The actual call queries the nonempty equation space, merges the incoming
frame and recursively evaluates both RHS requests under any saved caller. -/
theorem equation_call_realizes_changed_bindings :
    Realizes equationSpace (.call equationQuery Atom.symbolType equationCaller 13) equationAnswers := by
  have bodies := equations_leaf_realizes equationSpace equationQuery Atom.symbolType equationCaller 11
    (queryEquations equationSpace equationQuery 12) (equation_body_leaves 12 equation_inputs_exact)
    (equation_body_notRefused 12 equation_inputs_exact)
  rw [equation_inputs_exact] at bodies
  exact call_equations_realizes equationSpace "identity" [.symbol "answer"]
    Atom.symbolType equationCaller 12 equationAnswers (by decide) (by decide) [] (by decide +kernel)
    (by intro request member; change request ∈ equationAnswers at member;
        simp only [equationAnswers, List.mem_cons, List.not_mem_nil, or_false] at member;
        rcases member with rfl | rfl <;> simp [Minimal.IsFunction]) bodies

private def equationTyping :
    ApplicationTyping equationSpace "identity" [.symbol "answer"] Atom.symbolType controlFuel where
  domains := [Atom.atomType]
  returned := Atom.symbolType
  before := []
  after := []
  declined := []
  sourceTypes := by decide
  rejected := .nil
  argumentChecks := .cons (.wildcard (Or.inl rfl)) .nil
  argumentPaths := by decide
  expectedClosed := rfl
  returnedClosed := rfl
  returnedFits := Or.inr (Or.inr (Or.inr (Or.inr rfl)))
  returnBudget := by decide
  earlierClosed := by simp
  earlierHeadRejects := by simp
  headClosed := rfl
  headBudget := by decide
  demandNotRaw := by decide
  demandNotExpression := by decide
  nonemptyOperator := by decide
  cleanOperator := by decide

/-- A full typed expression, rather than a preselected call task, traverses
argument checking and both equation bodies. The replies keep their changed
frames through the existing typed return and success-priority continuation. -/
theorem typed_equation_expression_retains_bindings_under (live : List Atom)
    (closed : atomListVariables live = []) :
    Realizes equationSpace
      (.atom equationQuery Atom.symbolType equationCaller (controlFuel + 3) live) equationAnswers := by
  have scope : equationScope live equationQuery Atom.symbolType equationCaller =
      equationScope [] equationQuery Atom.symbolType equationCaller := by
    simp [equationScope, closed, atomListVariables]
  have inputs : (queryEquationsAvoiding (equationScope [] equationQuery Atom.symbolType equationCaller)
      equationSpace equationQuery controlFuel).flatMap
      (equationInputs equationCaller controlFuel) = equationAnswers := by decide +kernel
  have bodies := equations_leaf_realizes equationSpace equationQuery Atom.symbolType equationCaller (controlFuel - 1)
    (queryEquationsAvoiding (equationScope [] equationQuery Atom.symbolType equationCaller)
      equationSpace equationQuery controlFuel) (equation_body_leaves controlFuel inputs) (equation_body_notRefused controlFuel inputs) live
  simp only [show controlFuel - 1 + 1 = controlFuel from rfl] at bodies
  change Realizes equationSpace (.returns equationQuery Atom.symbolType controlFuel
    ((queryEquationsAvoiding (equationScope [] equationQuery Atom.symbolType equationCaller)
      equationSpace equationQuery controlFuel).flatMap
      (equationInputs equationCaller controlFuel)) live) _ at bodies
  rw [inputs] at bodies
  have raw : rawQueryResults equationSpace equationQuery Atom.symbolType equationCaller controlFuel live =
      equationAnswers := by
    change (queryEquationsAvoiding (equationScope live equationQuery Atom.symbolType equationCaller)
      equationSpace equationQuery controlFuel).flatMap (equationInputs equationCaller controlFuel) = _
    rw [scope]
    exact inputs
  have call := call_equations_realizes equationSpace "identity" [.symbol "answer"]
    Atom.symbolType equationCaller controlFuel equationAnswers (by decide) (by decide) live
    (by rw [show (.expression [.symbol "identity", .symbol "answer"]) = equationQuery from rfl, raw]; decide)
    (by intro request member; rw [show (.expression [.symbol "identity", .symbol "answer"]) = equationQuery from rfl, raw] at member
        simp only [equationAnswers, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl <;> simp [Minimal.IsFunction])
    (by simpa only [show (.expression [.symbol "identity", .symbol "answer"]) = equationQuery from rfl, raw] using bodies)
  have calls := calls_realizes equationSpace Atom.symbolType (controlFuel + 1) live
    (requests := [(equationQuery, equationCaller)]) (outputs := [equationAnswers])
    (List.Forall₂.cons call (.nil : List.Forall₂ _ [] []))
  have leaf : LeafRel (.symbol "answer") Atom.atomType :=
    Or.inr ⟨Atom.symbolType, .symbol "answer", Or.inl rfl⟩
  have arguments := arguments_cons_law equationSpace equationCaller (.symbol "answer") Atom.atomType
    [] [] (controlFuel - 1) [.symbol "answer"] [[]]
    (leaf_law equationSpace equationCaller (.symbol "answer") Atom.atomType (controlFuel - 2) leaf)
    (arguments_nil_law equationSpace equationCaller (controlFuel - 2))
  have realized := application_with_calls_realizes equationTyping equationCaller [[.symbol "answer"]]
    equationAnswers live (arguments.1 _) calls
  have filtered : successPriority equationAnswers = equationAnswers := by decide +kernel
  simpa only [filtered, equationQuery] using realized

theorem typed_equation_expression_retains_bindings :
    Realizes equationSpace
      (.atom equationQuery Atom.symbolType equationCaller (controlFuel + 3)) equationAnswers :=
  typed_equation_expression_retains_bindings_under [] rfl

/-- A typed equation computation in the first argument creates two binding
endpoints. The actual second argument runs under each endpoint and the
collected packet keeps that endpoint, together with arbitrary saved callers. -/
theorem equation_argument_branches_retain_bindings :
    Realizes equationSpace
      (.args [equationQuery, .symbol "tail"] [Atom.symbolType, Atom.atomType]
        equationCaller (controlFuel + 4))
      (equationAnswers.map fun result =>
        (argumentPacket [result.1, .symbol "tail"], result.2)) := by
  have safe : ∀ head ∈ equationAnswers,
      head.1 = equationQuery ∨ isEmptyOrError head.1 = false := by
    intro head member
    simp only [equationAnswers, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> exact Or.inr rfl
  have branches : List.Forall₂ (fun head output => ∃ tails,
      Realizes equationSpace (.args [.symbol "tail"] [Atom.atomType] head.2 (controlFuel + 3)
        [head.1]) tails ∧
        output = RecursiveTasks.argumentTail head.1 tails)
      equationAnswers
      (equationAnswers.map fun head =>
        RecursiveTasks.argumentTail head.1 [(argumentPacket [.symbol "tail"], head.2)]) := by
    apply List.forall₂_map_right_iff.mpr
    apply List.forall₂_same.mpr
    intro head _
    refine ⟨[(argumentPacket [.symbol "tail"], head.2)], ?_, rfl⟩
    intro stack emitted
    exact raw_arguments equationSpace HE.GroundedDispatch.none [.symbol "tail"]
      head.2 (controlFuel + 3) (by simp) _ stack emitted
  have realized := arguments_cons_with_branches_realizes equationSpace equationQuery Atom.symbolType
    [.symbol "tail"] [Atom.atomType] equationCaller (controlFuel + 3) []
    (typed_equation_expression_retains_bindings_under _ rfl) safe branches
  simpa only [RecursiveTasks.argumentTail, List.map_cons, List.map_nil, argumentsSucceeded_packet,
    Bool.true_eq_false, if_false, argumentValues_packet, ← List.flatMap_def,
    List.flatMap_singleton', equationAnswers, List.flatMap_cons, List.flatMap_nil,
    List.append_nil, List.nil_append, List.cons_append, Nat.add_assoc, List.flatten_cons,
    List.flatten_nil] using realized

/-- Replacing the branch endpoints by the original caller preserves the two
packet values and changes the actual argument results. -/
theorem restoring_argument_input_loses_bindings :
    (equationAnswers.map fun result =>
      (argumentPacket [result.1, .symbol "tail"], result.2)).map Prod.fst =
      [argumentPacket [.symbol "answer", .symbol "tail"],
       argumentPacket [.symbol "answer", .symbol "tail"]] ∧
    equationAnswers.map (fun result =>
      (argumentPacket [result.1, .symbol "tail"], result.2)) ≠
      replies equationCaller [argumentPacket [.symbol "answer", .symbol "tail"],
        argumentPacket [.symbol "answer", .symbol "tail"]] := by
  decide +kernel

private def equationArgument : TypedApplyState :=
  ⟨.symbol "caller", [equationQuery], [Atom.symbolType], 0, [], equationCaller⟩
private def equationPrepared : NativeArgumentControl.Prepared :=
  ⟨Atom.symbolType, equationQuery, {dialect := .he}⟩
private def equationWaiting : NativeArgumentControl.Configuration :=
  NativeArgumentControl.issue ⟨[], [], 17, 0, [], 0⟩ []
    (.evaluate equationArgument equationPrepared)

/-- The typed equation child actually returns to its retained caller through
call, worker and reply transitions. Both new equation frames reach the caller's
selected snapshot; an unchanged-input-frame callback cannot substitute for it. -/
theorem typed_equation_returns_changed_bindings_to_caller
    (operations : NativeArgumentControl.Operations) (policy : NativeArgumentControlMachine.RefusalPolicy)
    (charge : Nat) :
    let endpoint := (NativeArgumentControl.request equationWaiting
      (.evaluate equationArgument equationPrepared) 0).endpoint
    let reply : NativeArgumentControl.Reply := ⟨endpoint, .evaluated equationAnswers, charge⟩
    let after := NativeArgumentControl.replied equationWaiting [] reply
      [.iterate (NativeArgumentControl.selectedSnapshot equationArgument equationPrepared equationAnswers)
        equationPrepared]
    let initial : RecursiveTasks.Configuration :=
      ⟨equationSpace, .work (.atom equationQuery Atom.symbolType equationCaller (controlFuel + 3)), [], []⟩
    ∃ budget, ((NativeArgumentControlMachine.interactionMachine operations policy).handle
      NativeArgumentControlEncoding.interactionCallback (evaluationService endpoint charge) (fun _ => initial)).run
      budget (.running (.active equationWaiting)) =
      (NativeArgumentControlEncoding.callEventData endpoint :: equationAnswers.map sourceEvent ++
        [NativeArgumentControlEncoding.replyEventData (.returned (NativeArgumentControlEncoding.replyData reply))],
        .exhausted (.running (.active after))) :=
  handled_evaluation operations policy equationWaiting equationArgument equationPrepared 0 [] rfl
    (controlFuel + 3) charge equationAnswers typed_equation_expression_retains_bindings

/-- Both service representations publish the two complete changed binding
frames, and the endpoint verdict carries that same full occurrence list. -/
theorem equation_call_service_retains_bindings (endpoint : Atom) (charge : Nat) :
    (∃ budget, ∀ later, (evaluationService endpoint charge).run (budget + later)
      ⟨equationSpace, .work (.call equationQuery Atom.symbolType equationCaller 13), [], []⟩ =
        (equationAnswers.map sourceEvent,
          .finished (.returned (NativeArgumentControlEncoding.replyData
            ⟨endpoint, .evaluated equationAnswers, charge⟩)))) ∧
    (∃ budget, ∀ later,
      ((dataMachine HE.GroundedDispatch.none).relabel sourceEvent
        (evaluationReply endpoint charge) id).run (budget + later)
        (RecursiveEncoding.configurationData
          ⟨equationSpace, .work (.call equationQuery Atom.symbolType equationCaller 13), [], []⟩) =
        (equationAnswers.map sourceEvent,
          .finished (.returned (NativeArgumentControlEncoding.replyData
            ⟨endpoint, .evaluated equationAnswers, charge⟩)))) :=
  ⟨realizes_service_completed equation_call_realizes_changed_bindings endpoint charge,
    realizes_encoded_service_completed equation_call_realizes_changed_bindings endpoint charge⟩

/-- The source task earns finite completion and exact saved-residual
resumption. Existing observations are appended once, including equal values. -/
theorem equation_call_completes_and_resumes (earned observed : ResultSet)
    (first : Nat) (saved : RecursiveTasks.Configuration)
    (paused : (machine HE.GroundedDispatch.none).run first
      ⟨equationSpace, .work (.call equationQuery Atom.symbolType equationCaller 13), [], earned⟩ =
        (observed, .exhausted saved)) :
    (∃ budget, ∀ later, (machine HE.GroundedDispatch.none).run (budget + later)
      ⟨equationSpace, .work (.call equationQuery Atom.symbolType equationCaller 13), [], earned⟩ =
        (equationAnswers, .finished ⟨equationSpace, .returning [], [], earned ++ equationAnswers⟩)) ∧
    (∃ remainingBudget remaining, (machine HE.GroundedDispatch.none).run remainingBudget saved =
      (remaining, .finished ⟨equationSpace, .returning [], [], earned ++ equationAnswers⟩) ∧
      observed ++ remaining = equationAnswers) :=
  ⟨realizes_completed equation_call_realizes_changed_bindings earned,
    realizes_resumed equation_call_realizes_changed_bindings earned observed first saved paused⟩

/-- A nonvacuous suspension after the first physical answer. Resuming the
actual saved worker emits only the second, with both changed frames retained. -/
theorem equation_call_published_cut (earned : ResultSet) :
    ∃ first saved,
      (machine HE.GroundedDispatch.none).run first
        ⟨equationSpace, .work (.call equationQuery Atom.symbolType equationCaller 13), [], earned⟩ =
          ([((.symbol "answer" : Atom), equationBinding 0)], .exhausted saved) ∧
      (machine HE.GroundedDispatch.none).run 2 saved =
        ([((.symbol "answer" : Atom), equationBinding 1)],
          .finished ⟨equationSpace, .returning [], [], earned ++ equationAnswers⟩) := by
  obtain ⟨administrative, realized⟩ := (machine HE.GroundedDispatch.none).silent_run
    (equation_call_realizes_changed_bindings [] earned)
  refine ⟨administrative + 1,
    ⟨equationSpace, .returning [(.symbol "answer", equationBinding 1)], [],
      earned ++ [(.symbol "answer", equationBinding 0)]⟩, ?_, ?_⟩
  · rw [realized 1]
    rfl
  · have drained := drain_returning equationSpace [(.symbol "answer", equationBinding 1)]
      (earned ++ [(.symbol "answer", equationBinding 0)]) 0
    rw [List.append_assoc] at drained
    exact drained

/-- Returning the pre-call frame for either answer would lose the equation
binding, even though both value-only observations would still agree. -/
theorem unchanged_binding_observer_is_insufficient :
    equationAnswers ≠ [(.symbol "answer", equationCaller), (.symbol "answer", equationCaller)] ∧
      equationAnswers.map Prod.fst =
        [(.symbol "answer", equationCaller), (.symbol "answer", equationCaller)].map Prod.fst := by
  decide +kernel

private def recursiveSpace : Space := Space.ofList [identityEquation,
  .expression [.symbol ":", .symbol "identity", arrow [Atom.atomType] Atom.symbolType]]

private def captureLive : List Atom := [.var "x#0"]
private def recursiveQuery : Atom := .expression [.symbol "identity", equationQuery]
private def outerRecursiveBindings : Bindings :=
  ⟨[("x#1", equationQuery), ("caller", .symbol "kept")], []⟩
private def innerRecursiveBindings : Bindings :=
  ⟨[("x#2", .symbol "answer"), ("x#1", equationQuery), ("caller", .symbol "kept")], []⟩

private def unaryRawSymbolTyping (space : Space) (name : String) (argument : Atom)
    (fuel : Nat) (enough : controlFuel ≤ fuel)
    (types : getAtomTypes space (.symbol name) = [arrow [Atom.atomType] Atom.symbolType])
    (nonempty : name ≠ "Empty") (clean : name ≠ "Error") :
    ApplicationTyping space name [argument] Atom.symbolType fuel where
  domains := [Atom.atomType]
  returned := Atom.symbolType
  before := []
  after := []
  declined := []
  sourceTypes := types
  rejected := .nil
  argumentChecks := .cons (.wildcard (Or.inl rfl)) .nil
  argumentPaths := by
    simpa [admittedPathCount, acceptedTypes, ClosedTypeFits] using
      List.length_pos_iff.mpr (FirstSuccessSourceReplies.getAtomTypes_nonempty space argument)
  expectedClosed := rfl
  returnedClosed := rfl
  returnedFits := Or.inr (Or.inr (Or.inr (Or.inr rfl)))
  returnBudget := by have bound : sizeOf Atom.symbolType + sizeOf Atom.symbolType + 2 ≤ controlFuel := by decide
                     omega
  earlierClosed := by simp
  earlierHeadRejects := by simp
  headClosed := rfl
  headBudget := by
    have bound : sizeOf (arrow [Atom.atomType] Atom.symbolType) +
        sizeOf (arrow [Atom.atomType] Atom.symbolType) + 2 < controlFuel := by decide
    omega
  demandNotRaw := by decide
  demandNotExpression := by decide
  nonemptyOperator := nonempty
  cleanOperator := clean

private def recursiveTyping (argument : Atom) (fuel : Nat) (enough : controlFuel ≤ fuel) :
    ApplicationTyping recursiveSpace "identity" [argument] Atom.symbolType fuel :=
  unaryRawSymbolTyping recursiveSpace "identity" argument fuel enough (by decide) (by decide) (by decide)

private theorem normal_assignments_model (bindings : Bindings) (noEqualities : bindings.equalities = [])
    (normal : TypeSubst.Normal bindings.assignments) :
    ∃ valuation, Spec.Type.RuntimeRefinement.TypeBindingSatisfied valuation bindings := by
  exact ⟨Spec.Type.Presentation.Theory.presentedValuation bindings.assignments,
    normal_record_model noEqualities normal⟩

private theorem unary_assignment_source_match (name : String) (left right value : Atom) (key : String)
    (acyclic : Spec.Match.Merge.SemanticLoopFree (Bindings.empty.assign key value))
    (argument : Spec.Match.Merge.MatchRel Spec.Match.Merge.equalityGroundedSemantic
      left right (Bindings.empty.assign key value)) :
    Spec.Match.Merge.MatchRel Spec.Match.Merge.equalityGroundedSemantic
      (.expression [.symbol name, left]) (.expression [.symbol name, right])
      (Bindings.empty.assign key value) := by
  apply Spec.Match.Merge.MatchRel.expression
  · refine .cons (next := Bindings.empty) (.symSym name Spec.Match.Merge.semanticLoopFree_empty) ?_ ?_
    · exact .mk (.refl _) .nil
    · refine .cons argument ?_ .nil
      apply Spec.Match.Merge.MergeRel.mk (order := [.value key value])
      · simp [Spec.Match.Merge.constraints, Bindings.assign, Bindings.empty,
          Bindings.isBound, Bindings.lookup, List.eraseDups_cons]
      · exact .value (.fresh rfl) .nil
  · exact acyclic

private theorem identity_source_match (argument : Atom) (key : String)
    (nonvariable : Spec.Match.Merge.isVariableB argument = false)
    (acyclic : Spec.Match.Merge.SemanticLoopFree (Bindings.empty.assign key argument)) :
    Spec.Match.Merge.MatchRel Spec.Match.Merge.equalityGroundedSemantic
      (.expression [.symbol "identity", argument]) (.expression [.symbol "identity", .var key])
      (Bindings.empty.assign key argument) :=
  unary_assignment_source_match "identity" argument (.var key) argument key acyclic (.nonVarVar nonvariable acyclic)

private theorem scoped_identity_evidence (space : Space) (position : Nat)
    (stored : space.atoms[position]? = some identityEquation) (live : List Atom) (argument : Atom) (incoming : Bindings)
    (key : String)
    (freshened : freshenEquationAvoiding
        (equationScope live (.expression [.symbol "identity", argument]) Atom.symbolType incoming)
        position (.expression [.symbol "identity", .var "x"]) (.var "x") =
      (.expression [.symbol "identity", .var key], .var key))
    (noEqualities : incoming.equalities = [])
    (fresh : ∀ old, (key, old) ∉ incoming.assignments)
    (nonvariable : Spec.Match.Merge.isVariableB argument = false)
    (singleAcyclic : Spec.Match.Merge.SemanticLoopFree (Bindings.empty.assign key argument))
    (normal : TypeSubst.Normal ((key, argument) :: incoming.assignments))
    (closed : ∀ valuation, Spec.Type.RuntimeRefinement.applyTypeValuation valuation argument = argument) :
    EquationBodyEvidence space live (.expression [.symbol "identity", argument])
      Atom.symbolType incoming (.var key, Bindings.empty.assign key argument)
      (argument, ⟨(key, argument) :: incoming.assignments, []⟩) := by
  apply EquationBodyEvidence.fresh_assignment position
    (.expression [.symbol "identity", .var "x"]) (.var "x") key argument
  · exact stored
  · simp only [freshened]
  · have alpha := EquationFreshening.freshenEquationAvoiding_alphaVariant
      (Atom.symbolType :: live) (.expression [.symbol "identity", argument])
      (.expression [.symbol "identity", .var "x"]) (.var "x") incoming
      (equationScope live (.expression [.symbol "identity", argument]) Atom.symbolType incoming) position
      (by
        intro name visible
        have covered := EquationFreshening.equationScope_visible (type_ := Atom.symbolType) visible
        simpa [equationScope, atomListVariables, atomVariables] using covered)
    simpa only [freshened] using alpha
  · simpa only [freshened] using identity_source_match argument key nonvariable singleAcyclic
  · rfl
  · exact noEqualities
  · exact (List.nodup_cons.mp normal.1).2
  · exact fresh
  · exact .refl _
  · exact normal_assignments_model _ rfl normal
  · intro valuation satisfied
    have assigned := satisfied.1 key argument (by simp)
    simpa only [Spec.Type.RuntimeRefinement.applyTypeValuation, closed valuation] using assigned

private theorem single_raw_args_derivation {comparison : SourceBindingComparison} (space : Space) (live : List Atom) (argument : Atom)
    (incoming : Bindings) (fuel : Nat) :
    ArgsDerivation (comparison := comparison) space live [argument] [Atom.atomType] incoming (fuel + 2) [([argument], incoming)] := by
  have leaf : LeafRel argument Atom.atomType :=
    Or.inr ⟨getMetaType argument, (Conformance.metaTypeRel_iff_getMetaType _ _).mpr rfl, Or.inl rfl⟩
  have head := AtomDerivation.leaf (comparison := comparison) (space := space) ([] ++ [] ++ live) argument Atom.atomType incoming fuel leaf
  have tail : ∀ selected ∈ [(argument, incoming)],
      ArgsDerivation (comparison := comparison) space (selected.1 :: live) [] [] selected.2 (fuel + 1) [([], incoming)] := by
    intro selected member
    obtain rfl := List.mem_singleton.mp member
    exact .nil _ _ fuel
  simpa using ArgsDerivation.cons live argument Atom.atomType [] [] incoming (fuel + 1)
    [(argument, incoming)] (fun _ => [([], incoming)]) head
    (by intro selected member; obtain rfl := List.mem_singleton.mp member; exact Or.inl rfl) tail

private theorem unary_raw_application_derivation {comparison : SourceBindingComparison} {space : Space} {name : String}
    (live : List Atom) (argument : Atom) (incoming : Bindings) (fuel : Nat)
    (typing : ApplicationTyping space name [argument] Atom.symbolType fuel)
    (domains : typing.domains = [Atom.atomType]) (returned : typing.returned = Atom.symbolType)
    (positive : 2 ≤ fuel) (results : ResultSet)
    (call : CallDerivation (comparison := comparison) space live (.expression [.symbol name, argument])
      Atom.symbolType incoming (fuel + 1) results)
    (filtered : successPriority results = results) :
    AtomDerivation (comparison := comparison) space live (.expression [.symbol name, argument])
      Atom.symbolType incoming (fuel + 3) results := by
  have args : ArgsDerivation (comparison := comparison) space (.symbol name :: Atom.symbolType :: live)
      [argument] [Atom.atomType] incoming fuel [([argument], incoming)] := by
    convert single_raw_args_derivation (comparison := comparison) space
      (.symbol name :: Atom.symbolType :: live) argument incoming (fuel - 2) using 1
    omega
  have calls : ∀ request ∈ applications name [([argument], incoming)],
      CallDerivation (comparison := comparison) space live request.1 Atom.symbolType request.2 (fuel + 1) results := by
    intro request member
    obtain rfl := List.mem_singleton.mp member
    exact call
  have rawType : (if typing.returned = Atom.expressionType then Atom.undefinedType else typing.returned) =
      Atom.symbolType := by rw [returned]; rfl
  have constructed := AtomDerivation.application live name [argument] Atom.symbolType incoming
    fuel typing [([argument], incoming)] (fun _ => results)
    (by simpa only [domains, rawType] using args) (by simpa only [rawType] using calls)
  simpa only [domains, applications, List.map_cons, List.map_nil, List.flatMap_cons,
    List.flatMap_nil, List.append_nil, filtered] using constructed

private theorem single_identity_application_derivation (live : List Atom) (argument : Atom)
    (incoming : Bindings) (fuel : Nat) (enough : controlFuel ≤ fuel) (results : ResultSet)
    (call : CallDerivation (comparison := .records) recursiveSpace live (.expression [.symbol "identity", argument])
      Atom.symbolType incoming (fuel + 1) results)
    (filtered : successPriority results = results) :
    AtomDerivation (comparison := .records) recursiveSpace live (.expression [.symbol "identity", argument])
      Atom.symbolType incoming (fuel + 3) results :=
  unary_raw_application_derivation live argument incoming fuel (recursiveTyping argument fuel enough)
    rfl rfl (by
      have : 2 ≤ controlFuel := by decide
      omega) results call filtered


private theorem singleton_prepared_rows {Input Output : Type}
    {source : List Input} {prepare : Input → List Output} {chosen : Input} {result : Output}
    (oneSource : source = [chosen]) (oneOutput : prepare chosen = [result])
    {property : Input → Output → Prop} (holds : property chosen result) :
    ∀ input ∈ source, ∀ output ∈ prepare input, property input output := by
  intro input member output present
  rw [oneSource] at member
  obtain rfl := List.mem_singleton.mp member
  rw [oneOutput] at present
  obtain rfl := List.mem_singleton.mp present
  exact holds

private structure OrdinaryEquationPlan (comparison : SourceBindingComparison) (space : Space)
    (live : List Atom) (invocation expected : Atom) (incoming : Bindings) (fuel : Nat)
    (results : ResultSet) : Prop where
  selected : rawQueryResults space invocation expected incoming fuel live ≠ []
  evidence : ∀ candidate ∈ equationCandidates space live invocation expected incoming fuel,
    ∀ request ∈ equationInputs incoming fuel candidate,
      EquationBodyEvidence (comparison := comparison) space live invocation expected incoming candidate request
  ordinary : ∀ candidate ∈ equationCandidates space live invocation expected incoming fuel,
    ∀ request ∈ equationInputs incoming fuel candidate, ¬Spec.Eval.Minimal.IsFunction request.1
  returns : ∀ candidate ∈ equationCandidates space live invocation expected incoming fuel,
    ∀ request ∈ equationInputs incoming fuel candidate,
      ReturnDerivation (comparison := comparison) space live invocation expected request.1 request.2 fuel results

/-- The same source selections supply both the ordinary proof and its
coverage proof. Each dependent premise is transported through the two
actual singleton observations. -/
private theorem singleEquationPlan {comparison : SourceBindingComparison} {space : Space}
    {live : List Atom} {invocation expected : Atom} {incoming : Bindings} {fuel : Nat}
    {candidate request : ResultPair} {results : ResultSet}
    (query : equationCandidates space live invocation expected incoming fuel = [candidate])
    (inputs : equationInputs incoming fuel candidate = [request])
    (evidence : EquationBodyEvidence (comparison := comparison) space live invocation expected
      incoming candidate request)
    (nonfunction : ¬Spec.Eval.Minimal.IsFunction request.1)
    (accepted : request.1 ≠ Atom.notReducible) (running : isEmptyOrError request.1 = false)
    (body : AtomDerivation (comparison := comparison) space live request.1 expected request.2 fuel results) :
    OrdinaryEquationPlan comparison space live invocation expected incoming fuel results := by
  refine ⟨?_, singleton_prepared_rows query inputs evidence,
    singleton_prepared_rows query inputs (property := fun _ row => ¬Spec.Eval.Minimal.IsFunction row.1)
      nonfunction, singleton_prepared_rows query inputs ?_⟩
  · change List.flatMap (equationInputs incoming fuel)
      (equationCandidates space live invocation expected incoming fuel) ≠ []
    rw [query]
    simp [inputs]
  · exact .evaluate live invocation expected request.1 request.2 fuel results accepted
      (by simpa [Conformance.isEmptyOrErrorRel_iff_isEmptyOrError] using running) body

private theorem single_equation_call_derivation {comparison : SourceBindingComparison} (space : Space) (name : String)
    (ordinary : name ≠ "unify" ∧ name ≠ "switch-minimal")
    (nonembedded : Spec.Eval.Minimal.embeddedInstruction (.expression [.symbol name]) = false)
    (clean : name ≠ "Error")
    (live : List Atom) (argument : Atom)
    (incoming : Bindings) (fuel : Nat) (candidate request : ResultPair) (results : ResultSet)
    (query : equationCandidates space live (.expression [.symbol name, argument])
      Atom.symbolType incoming fuel = [candidate])
    (inputs : equationInputs incoming fuel candidate = [request])
    (evidence : EquationBodyEvidence (comparison := comparison) space live (.expression [.symbol name, argument])
      Atom.symbolType incoming candidate request)
    (body : AtomDerivation (comparison := comparison) space live request.1 Atom.symbolType request.2 fuel results)
    (normal : request.1 ≠ Atom.notReducible ∧ isEmptyOrError request.1 = false := by
      simp only [Prod.fst]
      decide +kernel)
    (nonfunction : ¬Spec.Eval.Minimal.IsFunction request.1 := by
      rintro ⟨body, impossible⟩
      have heads := congrArg (fun value : Atom => match value with
        | .expression (.symbol head :: _) => head | _ => "") impossible
      simp only at heads
      revert heads
      decide) :
    CallDerivation (comparison := comparison) space live (.expression [.symbol name, argument])
      Atom.symbolType incoming (fuel + 1) results := by
  have plan := singleEquationPlan query inputs evidence nonfunction normal.1 normal.2 body
  have constructed := CallDerivation.ordinaryEquations live name [argument] Atom.symbolType incoming fuel
    (fun _ _ => results) ordinary nonembedded clean plan.selected plan.evidence plan.ordinary plan.returns
  simpa only [query, inputs, List.flatMap_cons, List.flatMap_nil, List.append_nil] using constructed

private theorem single_raw_args_covered {comparison : SourceBindingComparison} (space : Space) (live : List Atom) (argument : Atom)
    (incoming : Bindings) (fuel : Nat) :
    (single_raw_args_derivation (comparison := comparison) space live argument incoming fuel).Covered := by
  have leaf : LeafRel argument Atom.atomType :=
    Or.inr ⟨getMetaType argument, (Conformance.metaTypeRel_iff_getMetaType _ _).mpr rfl, Or.inl rfl⟩
  have head := AtomDerivation.leaf (comparison := comparison) (space := space) ([] ++ [] ++ live) argument Atom.atomType incoming fuel leaf
  have tail : ∀ selected ∈ [(argument, incoming)],
      ArgsDerivation (comparison := comparison) space (selected.1 :: live) [] [] selected.2 (fuel + 1) [([], incoming)] := by
    intro selected member
    obtain rfl := List.mem_singleton.mp member
    exact .nil _ _ fuel
  have derived := ArgsDerivation.cons live argument Atom.atomType [] [] incoming (fuel + 1)
    [(argument, incoming)] (fun _ => [([], incoming)]) head
    (by intro selected member; obtain rfl := List.mem_singleton.mp member; exact Or.inl rfl) tail
  have covered : derived.Covered := by
    apply ArgsDerivation.Covered.cons (head := head) (tail := tail)
      (safe := by intro selected member; obtain rfl := List.mem_singleton.mp member; exact Or.inl rfl)
    · exact AtomDerivation.Covered.leaf (leaf := leaf)
    · intro selected member
      obtain rfl := List.mem_singleton.mp member
      exact .nil
  simpa using covered

private theorem unary_raw_application_covered {comparison : SourceBindingComparison} {space : Space} {name : String}
    (live : List Atom) (argument : Atom) (incoming : Bindings) (fuel : Nat)
    (typing : ApplicationTyping space name [argument] Atom.symbolType fuel)
    (domains : typing.domains = [Atom.atomType]) (returned : typing.returned = Atom.symbolType)
    (positive : 2 ≤ fuel) (results : ResultSet)
    (call : CallDerivation (comparison := comparison) space live (.expression [.symbol name, argument])
      Atom.symbolType incoming (fuel + 1) results)
    (filtered : successPriority results = results)
    (selection : FirstSuccessRecursiveStrategy.selectionReady space
      (.expression [.symbol name, argument]) Atom.symbolType incoming (fuel + 1)
      (getAtomTypes space (.symbol name)) = true)
    (headCovered : typeCastCovered (.symbol name) (arrow typing.domains typing.returned)
      space incoming (fuel - 1) = true)
    (callCovered : call.Covered) :
    (unary_raw_application_derivation (comparison := comparison) live argument incoming fuel typing domains returned positive
      results call filtered).Covered := by
  have args : ArgsDerivation (comparison := comparison) space (.symbol name :: Atom.symbolType :: live)
      [argument] [Atom.atomType] incoming fuel [([argument], incoming)] := by
    convert single_raw_args_derivation (comparison := comparison) space
      (.symbol name :: Atom.symbolType :: live) argument incoming (fuel - 2) using 1
    omega
  have argsCovered : args.Covered := by
    convert single_raw_args_covered (comparison := comparison) space (.symbol name :: Atom.symbolType :: live)
      argument incoming (fuel - 2) using 1
    omega
  have calls : ∀ request ∈ applications name [([argument], incoming)],
      CallDerivation (comparison := comparison) space live request.1 Atom.symbolType request.2 (fuel + 1) results := by
    intro request member
    obtain rfl := List.mem_singleton.mp member
    exact call
  have rawType : (if typing.returned = Atom.expressionType then Atom.undefinedType else typing.returned) =
      Atom.symbolType := by rw [returned]; rfl
  have constructed := AtomDerivation.application live name [argument] Atom.symbolType incoming
    fuel typing [([argument], incoming)] (fun _ => results)
    (by simpa only [domains, rawType] using args) (by simpa only [rawType] using calls)
  have covered : constructed.Covered := by
    apply AtomDerivation.Covered.application (args := by simpa only [domains, rawType] using args)
      (calls := by simpa only [rawType] using calls) selection headCovered
    · simpa only [domains, rawType] using argsCovered
    · intro request member
      obtain rfl := List.mem_singleton.mp member
      simpa only [rawType] using callCovered
  simpa only [domains, applications, List.map_cons, List.map_nil, List.flatMap_cons,
    List.flatMap_nil, List.append_nil, filtered] using covered

private theorem single_equation_call_covered {comparison : SourceBindingComparison} (space : Space) (name : String)
    (ordinary : name ≠ "unify" ∧ name ≠ "switch-minimal")
    (nonembedded : Spec.Eval.Minimal.embeddedInstruction (.expression [.symbol name]) = false)
    (clean : name ≠ "Error")
    (live : List Atom) (argument : Atom) (incoming : Bindings) (fuel : Nat)
    (candidate request : ResultPair) (results : ResultSet)
    (query : equationCandidates space live (.expression [.symbol name, argument])
      Atom.symbolType incoming fuel = [candidate])
    (inputs : equationInputs incoming fuel candidate = [request])
    (evidence : EquationBodyEvidence (comparison := comparison) space live (.expression [.symbol name, argument])
      Atom.symbolType incoming candidate request)
    (body : AtomDerivation (comparison := comparison) space live request.1 Atom.symbolType request.2 fuel results)
    (normal : request.1 ≠ Atom.notReducible ∧ isEmptyOrError request.1 = false)
    (queryCovered : queryEquationsCovered
      (equationScope live (.expression [.symbol name, argument]) Atom.symbolType incoming)
      space (.expression [.symbol name, argument]) fuel = true)
    (mergeCovered : matchCovered fuel (.merge candidate.2 (aliasConstraints incoming)) = true)
    (readCovered : ∀ merged ∈ mergeBindings candidate.2 (aliasConstraints incoming) fuel, merged.hasLoop = false →
      merged.applyFullCovered candidate.1 fuel = true)
    (bodyCovered : body.Covered)
    (nonfunction : ¬Spec.Eval.Minimal.IsFunction request.1 := by
      rintro ⟨body, impossible⟩
      have heads := congrArg (fun value : Atom => match value with
        | .expression (.symbol head :: _) => head | _ => "") impossible
      simp only at heads
      revert heads
      decide) :
    (single_equation_call_derivation (comparison := comparison) space name ordinary nonembedded clean live argument incoming fuel
      candidate request results query inputs evidence body normal nonfunction).Covered := by
  have plan := singleEquationPlan query inputs evidence nonfunction normal.1 normal.2 body
  have constructed := CallDerivation.ordinaryEquations live name [argument] Atom.symbolType incoming fuel
    (fun _ _ => results) ordinary nonembedded clean plan.selected plan.evidence plan.ordinary plan.returns
  have covered : constructed.Covered := by
    apply CallDerivation.Covered.ordinaryEquations (ordinary := ordinary) (nonembedded := nonembedded)
      (clean := clean) (selected := plan.selected) (evidence := plan.evidence)
      (ordinaryBodies := plan.ordinary) (bodies := plan.returns) queryCovered
    · intro selected member
      rw [query] at member
      obtain rfl := List.mem_singleton.mp member
      exact ⟨mergeCovered, readCovered⟩
    · intro selected member prepared present
      rw [query] at member
      obtain rfl := List.mem_singleton.mp member
      rw [inputs] at present
      obtain rfl := List.mem_singleton.mp present
      exact ReturnDerivation.Covered.evaluate (accepted := normal.1)
        (running := by simpa [Conformance.isEmptyOrErrorRel_iff_isEmptyOrError] using normal.2) bodyCovered
  simpa only [query, inputs, List.flatMap_cons, List.flatMap_nil, List.append_nil] using covered



private theorem inner_recursive_source :
    AtomDerivation (comparison := .records) recursiveSpace captureLive equationQuery Atom.symbolType outerRecursiveBindings
      (controlFuel + 8) [(.symbol "answer", innerRecursiveBindings)] := by
  apply single_identity_application_derivation captureLive (.symbol "answer") outerRecursiveBindings
    (controlFuel + 5) (by omega) _
  · apply single_equation_call_derivation recursiveSpace "identity" (by decide) (by decide) (by decide) captureLive (.symbol "answer") outerRecursiveBindings
      (controlFuel + 5) (.var "x#2", Bindings.empty.assign "x#2" (.symbol "answer"))
      (.symbol "answer", innerRecursiveBindings)
    · decide +kernel
    · decide +kernel
    · exact scoped_identity_evidence recursiveSpace 0 (by decide) captureLive (.symbol "answer") outerRecursiveBindings "x#2"
        (by decide +kernel) rfl (by simp [outerRecursiveBindings]) rfl
        ((Spec.Match.Merge.hasLoop_eq_false_iff_semanticLoopFree _).mp (by decide +kernel))
        (by
          constructor
          · decide
          · intro name value member candidate occurrence
            simp only [outerRecursiveBindings, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at member
            rcases member with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
              simp [equationQuery, TypeSubst.typeVars, TypeSubst.typeVarsList] at occurrence)
        (fun _ => by simp [Spec.Type.RuntimeRefinement.applyTypeValuation])
    · exact .leaf captureLive (.symbol "answer") Atom.symbolType innerRecursiveBindings
        (controlFuel + 4) (Or.inr ⟨Atom.symbolType, .symbol "answer", Or.inr (Or.inl rfl)⟩)
  · rfl

/-- The same variable-bearing equation is entered twice recursively. Both
new rule bindings and the old caller survive, while the pending x#0 remains
untouched. This is a source derivation, before invoking any machine theorem. -/
theorem nested_equation_source_derivation :
    AtomDerivation (comparison := .records) recursiveSpace captureLive recursiveQuery Atom.symbolType equationCaller
      (controlFuel + 11) [(.symbol "answer", innerRecursiveBindings)] := by
  apply single_identity_application_derivation captureLive equationQuery equationCaller
    (controlFuel + 8) (by omega) _
  · apply single_equation_call_derivation recursiveSpace "identity" (by decide) (by decide) (by decide) captureLive equationQuery equationCaller
      (controlFuel + 8) (.var "x#1", Bindings.empty.assign "x#1" equationQuery)
      (equationQuery, outerRecursiveBindings)
    · decide +kernel
    · decide +kernel
    · exact scoped_identity_evidence recursiveSpace 0 (by decide) captureLive equationQuery equationCaller "x#1"
        (by decide +kernel) rfl (by simp [equationCaller, Bindings.assign, Bindings.empty,
          Bindings.isBound, Bindings.lookup]) rfl
        ((Spec.Match.Merge.hasLoop_eq_false_iff_semanticLoopFree _).mp (by decide +kernel))
        (by
          constructor
          · decide
          · intro name value member candidate occurrence
            change (name, value) ∈ [("x#1", equationQuery), ("caller", .symbol "kept")] at member
            simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at member
            rcases member with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
              simp [equationQuery, TypeSubst.typeVars, TypeSubst.typeVarsList] at occurrence)
        (fun _ => by simp [equationQuery, Spec.Type.RuntimeRefinement.applyTypeValuation])
    · exact inner_recursive_source
  · rfl

/-- Nested calls reach the retained worker with every saved caller and prior
publication intact; the conclusion is constructed from the source derivation. -/
theorem nested_equation_realizes :
    Realizes recursiveSpace
      (.atom recursiveQuery Atom.symbolType equationCaller (controlFuel + 11) captureLive)
      [(.symbol "answer", innerRecursiveBindings)] :=
  nested_equation_source_derivation.realizes

/-- The independent evaluator agrees on the returned atom and complete
binding theory. Private relation-list layouts are related explicitly. -/
theorem nested_equation_independent_sound :
    ∃ output : Bindings,
      EvalAtomRawRel recursiveSpace noHost captureLive recursiveQuery Atom.symbolType equationCaller
        (.symbol "answer", output) ∧
      BindingRecordPerm innerRecursiveBindings output ∧
      Spec.Bindings.ScopeObservation.BindingTheoryEquivAt
        ["caller", "x#0", "x#1", "x#2"] innerRecursiveBindings output := by
  obtain ⟨output, derived, related⟩ := nested_equation_source_derivation.sound_records
    (.symbol "answer", innerRecursiveBindings) (by simp) [] equationCaller (.refl _)
  exact ⟨output, derived, related, related.theoryEquivAt _⟩

/-- Protecting a name changes the actual source instance; restoring the
caller would erase two different rule bindings. -/
theorem nested_equation_freshness_and_retention :
    innerRecursiveBindings.lookup "caller" = some (.symbol "kept") ∧
    innerRecursiveBindings.lookup "x#0" = none ∧
    innerRecursiveBindings.lookup "x#1" = some equationQuery ∧
    innerRecursiveBindings.lookup "x#2" = some (.symbol "answer") ∧
    innerRecursiveBindings ≠ equationCaller ∧
    freshenEquationAvoiding
      (equationScope captureLive recursiveQuery Atom.symbolType equationCaller) 0
      (.expression [.symbol "identity", .var "x"]) (.var "x") ≠
      (.expression [.symbol "identity", .var "x#0"], .var "x#0") := by decide +kernel

/-- Quotation/raw demand holds the recursive program as data instead of
executing its two equations or introducing their fresh bindings. -/
theorem nested_equation_raw_is_data :
    Realizes recursiveSpace
      (.atom recursiveQuery Atom.atomType equationCaller (controlFuel + 11) captureLive)
      [(recursiveQuery, equationCaller)] :=
  retained_leaf recursiveSpace HE.GroundedDispatch.none recursiveQuery Atom.atomType equationCaller
    (controlFuel + 10) (Or.inr ⟨Atom.expressionType, .expression _, Or.inl rfl⟩) captureLive


private theorem normal_closed_assignment_list (assignments : List (String × Atom))
    (unique : (TypeSubst.keys assignments).Nodup)
    (closed : ∀ entry ∈ assignments, TypeSubst.typeVars entry.2 = []) :
    TypeSubst.Normal assignments := by
  refine ⟨unique, ?_⟩
  intro name value present candidate occurrence
  rw [closed (name, value) present] at occurrence
  exact (List.not_mem_nil occurrence).elim

private theorem duplicate_identity_evidence (index : Nat) (position : index = 0 ∨ index = 1) :
    EquationBodyEvidence equationSpace [] equationQuery Atom.symbolType equationCaller
      (.var ("x#" ++ Nat.repr index), Bindings.empty.assign ("x#" ++ Nat.repr index) (.symbol "answer"))
      (.symbol "answer", equationBinding index) := by
  apply scoped_identity_evidence equationSpace index
    (by rcases position with rfl | rfl <;> decide) [] (.symbol "answer") equationCaller
  · rcases position with rfl | rfl <;> decide +kernel
  · rfl
  · have different : "x#" ++ Nat.repr index ≠ "caller" := by
      rcases position with rfl | rfl <;> decide
    intro old member
    exact different (Prod.mk.inj (List.mem_singleton.mp member)).1
  · rfl
  · apply (Spec.Match.Merge.hasLoop_eq_false_iff_semanticLoopFree _).mp
    rcases position with rfl | rfl <;> decide +kernel
  · apply normal_closed_assignment_list _ (by rcases position with rfl | rfl <;> decide)
    intro entry present
    change entry ∈ [(_, .symbol "answer"), ("caller", .symbol "kept")] at present
    simp only [List.mem_cons, List.not_mem_nil, or_false] at present
    rcases present with rfl | rfl <;> rfl
  · intro valuation
    simp [Spec.Type.RuntimeRefinement.applyTypeValuation]

private theorem duplicate_equation_source_call :
    CallDerivation (comparison := .records) equationSpace [] equationQuery Atom.symbolType equationCaller
      (controlFuel + 1) equationAnswers := by
  let candidates : ResultSet :=
    [(.var "x#0", Bindings.empty.assign "x#0" (.symbol "answer")),
     (.var "x#1", Bindings.empty.assign "x#1" (.symbol "answer"))]
  have queried : equationCandidates equationSpace [] equationQuery Atom.symbolType equationCaller
      controlFuel = candidates := by decide +kernel
  have inputZero : equationInputs equationCaller controlFuel candidates[0]! =
      [(.symbol "answer", equationBinding 0)] := by decide +kernel
  have inputOne : equationInputs equationCaller controlFuel candidates[1]! =
      [(.symbol "answer", equationBinding 1)] := by decide +kernel
  have evidence : ∀ candidate ∈ equationCandidates equationSpace [] equationQuery Atom.symbolType
      equationCaller controlFuel, ∀ request ∈ equationInputs equationCaller controlFuel candidate,
      EquationBodyEvidence equationSpace [] equationQuery Atom.symbolType equationCaller candidate request := by
    intro candidate member request present
    rw [queried] at member
    simp only [candidates, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · rw [show equationInputs equationCaller controlFuel
          (.var "x#0", Bindings.empty.assign "x#0" (.symbol "answer")) =
            [(.symbol "answer", equationBinding 0)] from inputZero] at present
      obtain rfl := List.mem_singleton.mp present
      exact duplicate_identity_evidence 0 (Or.inl rfl)
    · rw [show equationInputs equationCaller controlFuel
          (.var "x#1", Bindings.empty.assign "x#1" (.symbol "answer")) =
            [(.symbol "answer", equationBinding 1)] from inputOne] at present
      obtain rfl := List.mem_singleton.mp present
      exact duplicate_identity_evidence 1 (Or.inr rfl)
  have bodies : ∀ candidate ∈ equationCandidates equationSpace [] equationQuery Atom.symbolType
      equationCaller controlFuel, ∀ request ∈ equationInputs equationCaller controlFuel candidate,
      ReturnDerivation (comparison := .records) equationSpace [] equationQuery Atom.symbolType request.1 request.2 controlFuel [request] := by
    intro candidate member request present
    have allInputs : (equationCandidates equationSpace [] equationQuery Atom.symbolType equationCaller
        controlFuel).flatMap (equationInputs equationCaller controlFuel) = equationAnswers := by decide +kernel
    have inAnswers : request ∈ equationAnswers := by
      rw [← allInputs]
      exact List.mem_flatMap.mpr ⟨candidate, member, present⟩
    simp only [equationAnswers, List.mem_cons, List.not_mem_nil, or_false] at inAnswers
    rcases inAnswers with rfl | rfl
    all_goals
      exact .evaluate [] equationQuery Atom.symbolType (.symbol "answer") _ controlFuel _
        (by decide) (by simp [IsEmptyOrErrorRel, IsErrorRel, Atom.empty])
        (.leaf [] (.symbol "answer") Atom.symbolType _ (controlFuel - 1)
          (Or.inr ⟨Atom.symbolType, .symbol "answer", Or.inr (Or.inl rfl)⟩))
  have ordinaryBodies : ∀ candidate ∈ equationCandidates equationSpace [] equationQuery Atom.symbolType
      equationCaller controlFuel, ∀ request ∈ equationInputs equationCaller controlFuel candidate,
      ¬Spec.Eval.Minimal.IsFunction request.1 := by
    intro candidate member request present
    have allInputs : (equationCandidates equationSpace [] equationQuery Atom.symbolType equationCaller
        controlFuel).flatMap (equationInputs equationCaller controlFuel) = equationAnswers := by decide +kernel
    have inAnswers : request ∈ equationAnswers := by
      rw [← allInputs]
      exact List.mem_flatMap.mpr ⟨candidate, member, present⟩
    simp only [equationAnswers, List.mem_cons, List.not_mem_nil, or_false] at inAnswers
    rcases inAnswers with rfl | rfl <;> simp [Spec.Eval.Minimal.IsFunction]
  have constructed := CallDerivation.ordinaryEquations [] "identity" [.symbol "answer"] Atom.symbolType
    equationCaller controlFuel (fun _ request => [request]) (by decide) (by decide) (by decide)
    (by change rawQueryResults equationSpace equationQuery Atom.symbolType equationCaller controlFuel [] ≠ [];
        decide +kernel) evidence ordinaryBodies bodies
  convert constructed using 1 <;> rfl

/-- Two physical declarations of the same equation give two source
occurrences. They reach distinct retained binding frames even though their
values agree. -/
theorem duplicate_equation_source_derivation :
    AtomDerivation (comparison := .records) equationSpace [] equationQuery Atom.symbolType equationCaller
      (controlFuel + 3) equationAnswers := by
  have args : ArgsDerivation (comparison := .records) equationSpace [.symbol "identity", Atom.symbolType]
      [.symbol "answer"] [Atom.atomType] equationCaller controlFuel
      [([.symbol "answer"], equationCaller)] :=
    single_raw_args_derivation equationSpace _ _ _ (controlFuel - 2)
  have calls : ∀ request ∈ applications "identity" [([.symbol "answer"], equationCaller)],
      CallDerivation (comparison := .records) equationSpace [] request.1 Atom.symbolType request.2 (controlFuel + 1) equationAnswers := by
    intro request member
    obtain rfl := List.mem_singleton.mp member
    exact duplicate_equation_source_call
  have constructed := AtomDerivation.application [] "identity" [.symbol "answer"] Atom.symbolType
    equationCaller controlFuel equationTyping [([.symbol "answer"], equationCaller)]
    (fun _ => equationAnswers) args calls
  convert constructed using 1 <;> rfl

/-- Every delivered duplicate has an independent source derivation; the
underlying source-derivation list still has two occurrences, not one value. -/
theorem duplicate_equation_independent_sound :
    equationAnswers.length = 2 ∧
      ∀ result ∈ equationAnswers, ∃ output : Bindings,
        EvalAtomRawRel equationSpace noHost [] equationQuery Atom.symbolType equationCaller
          (result.1, output) ∧ BindingRecordPerm result.2 output :=
  ⟨rfl, fun result member => duplicate_equation_source_derivation.sound_records result member []
    equationCaller (.refl _)⟩

/-- The full nested source request completes through the collector and its
actual encoded worker. The old caller remains in both results. -/
theorem nested_equation_complete_and_collect (earned : ResultSet) :
    (∃ budget, ∀ later, collectReply recursiveSpace recursiveQuery Atom.symbolType equationCaller
      (controlFuel + 11) (budget + later) captureLive = some [(.symbol "answer", innerRecursiveBindings)]) ∧
    (∃ budget, ∀ later, (dataMachine HE.GroundedDispatch.none).run (budget + later)
      (RecursiveEncoding.configurationData
        ⟨recursiveSpace, .work (.atom recursiveQuery Atom.symbolType equationCaller
          (controlFuel + 11) captureLive), [], earned⟩) =
      ([((.symbol "answer" : Atom), innerRecursiveBindings)], .finished
        ⟨recursiveSpace, .returning [], [], earned ++ [(.symbol "answer", innerRecursiveBindings)]⟩)) :=
  ⟨nested_equation_source_derivation.collect, nested_equation_source_derivation.encoded_completed earned⟩

/-- A reached pause keeps its exact nested equation residual. Resumption
cannot silently repeat the freshening or discard the saved outer binding. -/
theorem nested_equation_resumed (earned observed : ResultSet) (first : Nat)
    (saved : RecursiveTasks.Configuration)
    (paused : (machine HE.GroundedDispatch.none).run first
      ⟨recursiveSpace, .work (.atom recursiveQuery Atom.symbolType equationCaller
        (controlFuel + 11) captureLive), [], earned⟩ = (observed, .exhausted saved)) :
    ∃ remainingBudget remaining,
      (machine HE.GroundedDispatch.none).run remainingBudget saved =
        (remaining, .finished
          ⟨recursiveSpace, .returning [], [], earned ++ [(.symbol "answer", innerRecursiveBindings)]⟩) ∧
      observed ++ remaining = [(.symbol "answer", innerRecursiveBindings)] :=
  nested_equation_source_derivation.resumed earned observed first saved paused

private def recursiveCallerArgument : TypedApplyState :=
  ⟨.symbol "caller", [recursiveQuery], [Atom.symbolType], 0, [], equationCaller⟩
private def recursiveCallerPrepared : NativeArgumentControl.Prepared :=
  ⟨Atom.symbolType, recursiveQuery, {dialect := .he}⟩
private def recursiveCallerWaiting : NativeArgumentControl.Configuration :=
  NativeArgumentControl.issue ⟨[], [], 19, 0, [], 0⟩ []
    (.evaluate recursiveCallerArgument recursiveCallerPrepared)

/-- A retained native caller invokes the actual nested source worker and
receives its changed bindings through the represented callback boundary. -/
theorem nested_equation_retained_handler (operations : NativeArgumentControl.Operations) :
    let endpoint := (NativeArgumentControl.request recursiveCallerWaiting
      (.evaluate recursiveCallerArgument recursiveCallerPrepared) 0).endpoint
    let reply : NativeArgumentControl.Reply :=
      ⟨endpoint, .evaluated [(.symbol "answer", innerRecursiveBindings)], 0⟩
    let after := NativeArgumentControl.replied recursiveCallerWaiting [] reply
      [.iterate (NativeArgumentControl.selectedSnapshot recursiveCallerArgument recursiveCallerPrepared
        [(.symbol "answer", innerRecursiveBindings)]) recursiveCallerPrepared]
    let initial : RecursiveTasks.Configuration :=
      ⟨recursiveSpace, .work (.atom recursiveQuery Atom.symbolType equationCaller
        (controlFuel + 11) captureLive), [], []⟩
    ∃ budget, ((NativeArgumentControlEncoding.interactionDataMachine operations .stop).handle
      NativeArgumentControlEncoding.representedCallback
      ((dataMachine HE.GroundedDispatch.none).relabel sourceEvent (evaluationReply endpoint 0) id)
      (fun _ => RecursiveEncoding.configurationData initial)).run budget
        (.running (NativeArgumentControlMachine.interactionData (.active recursiveCallerWaiting))) =
      (NativeArgumentControlEncoding.callEventData endpoint ::
        [sourceEvent (.symbol "answer", innerRecursiveBindings)] ++
        [NativeArgumentControlEncoding.replyEventData (.returned (NativeArgumentControlEncoding.replyData reply))],
        .exhausted (.running (NativeArgumentControlMachine.interactionData (.active after)))) :=
  AtomDerivation.handled_encoded operations .stop recursiveCallerWaiting recursiveCallerArgument
    recursiveCallerPrepared 0 [] rfl (controlFuel + 11) 0 [(.symbol "answer", innerRecursiveBindings)]
    nested_equation_source_derivation

/-- A completed empty reply and an unstarted nested worker are different
observations. No evaluator equation is licensed by a zero work budget. -/
theorem nested_zero_budget_is_pending :
    collectReply recursiveSpace recursiveQuery Atom.symbolType equationCaller
      (controlFuel + 11) 0 captureLive = none := rfl

/-- An emitted function wrapper requires the function-production branch;
query evidence alone cannot complete it as ordinary data. -/
theorem function_wrapper_producer_requires_execution {space : Space}
    {comparison : SourceBindingComparison} {live : List Atom} {caller : Option Atom}
    {body : Atom} {bindings : Bindings} {fuel : Nat} {results : ResultSet}
    (derived : ProducedDerivation (comparison := comparison) space live caller
      (.expression [.symbol "function", body]) bindings fuel results) :
    comparison = .semantic ∧ ∃ predecessor, fuel = predecessor + 1 ∧
      PrimitiveDerivation (comparison := comparison) space live caller
        (.expression [.symbol "function", body]) bindings predecessor results := by
  cases derived with
  | raw _ _ _ _ _ ordinary => exact (ordinary ⟨body, rfl⟩).elim
  | function _ _ _ _ predecessor _ semantic child =>
      exact ⟨semantic, predecessor, rfl, child⟩

private def successor (value : Atom) : Atom := .expression [.symbol "S", value]
private def peel (value : Atom) : Atom := .expression [.symbol "peel", value]
private def peelSpace : Space := Space.ofList
  [.expression [.symbol "=", peel (successor (.var "x")), peel (.var "x")],
   .expression [.symbol "=", peel (.symbol "Z"), .symbol "done"],
   .expression [.symbol ":", .symbol "peel", arrow [Atom.atomType] Atom.symbolType]]
private def peelOuterBindings : Bindings :=
  ⟨[("x#1", successor (.symbol "Z")), ("caller", .symbol "kept")], []⟩
private def peelInnerBindings : Bindings :=
  ⟨[("x#2", .symbol "Z"), ("x#1", successor (.symbol "Z")), ("caller", .symbol "kept")], []⟩

private def peelTyping (argument : Atom) (fuel : Nat) (enough : controlFuel ≤ fuel) :
    ApplicationTyping peelSpace "peel" [argument] Atom.symbolType fuel :=
  unaryRawSymbolTyping peelSpace "peel" argument fuel enough (by decide) (by decide) (by decide)

private theorem peel_recursive_evidence (tail : Atom) (incoming : Bindings) (key : String)
    (freshened : freshenEquationAvoiding
      (equationScope captureLive (peel (successor tail)) Atom.symbolType incoming)
      0 (peel (successor (.var "x"))) (peel (.var "x")) =
        (peel (successor (.var key)), peel (.var key)))
    (noEqualities : incoming.equalities = [])
    (fresh : ∀ old, (key, old) ∉ incoming.assignments)
    (nonvariable : Spec.Match.Merge.isVariableB tail = false)
    (singleAcyclic : Spec.Match.Merge.SemanticLoopFree (Bindings.empty.assign key tail))
    (normal : TypeSubst.Normal ((key, tail) :: incoming.assignments))
    (closed : ∀ valuation, Spec.Type.RuntimeRefinement.applyTypeValuation valuation tail = tail) :
    EquationBodyEvidence peelSpace captureLive (peel (successor tail)) Atom.symbolType incoming
      (peel (.var key), Bindings.empty.assign key tail)
      (peel tail, ⟨(key, tail) :: incoming.assignments, []⟩) := by
  apply EquationBodyEvidence.fresh_assignment 0 (peel (successor (.var "x"))) (peel (.var "x")) key tail
  · rfl
  · simp only [freshened]
  · have alpha := EquationFreshening.freshenEquationAvoiding_alphaVariant
      (Atom.symbolType :: captureLive) (peel (successor tail))
      (peel (successor (.var "x"))) (peel (.var "x")) incoming
      (equationScope captureLive (peel (successor tail)) Atom.symbolType incoming) 0
      (by
        intro name visible
        have covered := EquationFreshening.equationScope_visible (type_ := Atom.symbolType) visible
        simpa [equationScope, atomListVariables, atomVariables] using covered)
    simpa only [freshened] using alpha
  · rw [freshened]
    exact unary_assignment_source_match "peel" (successor tail) (successor (.var key)) tail key singleAcyclic
        (unary_assignment_source_match "S" tail (.var key) tail key singleAcyclic
          (.nonVarVar nonvariable singleAcyclic))
  · rfl
  · exact noEqualities
  · exact (List.nodup_cons.mp normal.1).2
  · exact fresh
  · exact .refl _
  · exact normal_assignments_model _ rfl normal
  · intro valuation satisfied
    have assigned := satisfied.1 key tail (by simp)
    simp only [closed valuation] at assigned
    simp only [peel, Spec.Type.RuntimeRefinement.applyTypeValuation, List.map_cons, List.map_nil, assigned]

private theorem peel_base_evidence :
    EquationBodyEvidence peelSpace captureLive (peel (.symbol "Z")) Atom.symbolType peelInnerBindings
      (.symbol "done", Bindings.empty) (.symbol "done", peelInnerBindings) := by
  apply EquationBodyEvidence.empty_match 1 (peel (.symbol "Z")) (.symbol "done")
  · rfl
  · decide +kernel
  · have alpha := EquationFreshening.freshenEquationAvoiding_alphaVariant
      (Atom.symbolType :: captureLive) (peel (.symbol "Z"))
      (peel (.symbol "Z")) (.symbol "done") peelInnerBindings
      (equationScope captureLive (peel (.symbol "Z")) Atom.symbolType peelInnerBindings) 1
      (by
        intro name visible
        have covered := EquationFreshening.equationScope_visible (type_ := Atom.symbolType) visible
        simpa [equationScope, atomListVariables, atomVariables] using covered)
    exact alpha
  · apply Spec.Match.Merge.MatchRel.expression
    · refine .cons (next := Bindings.empty) (.symSym "peel" Spec.Match.Merge.semanticLoopFree_empty) ?_ ?_
      · exact .mk (.refl _) .nil
      · refine .cons (next := Bindings.empty) (.symSym "Z" Spec.Match.Merge.semanticLoopFree_empty) ?_ .nil
        exact .mk (.refl _) .nil
    · exact Spec.Match.Merge.semanticLoopFree_empty
  · rfl
  · rfl
  · decide +kernel
  · exact .refl _
  · apply normal_assignments_model _ rfl
    apply normal_closed_assignment_list _ (by decide)
    intro entry present
    simp only [peelInnerBindings, List.mem_cons, List.not_mem_nil, or_false] at present
    rcases present with rfl | rfl | rfl <;>
      simp [successor, TypeSubst.typeVars, TypeSubst.typeVarsList]
  · intro valuation satisfied
    simp [Spec.Type.RuntimeRefinement.applyTypeValuation]

private theorem peel_one_evidence :
    EquationBodyEvidence peelSpace captureLive (peel (successor (.symbol "Z"))) Atom.symbolType
      peelOuterBindings (peel (.var "x#2"), Bindings.empty.assign "x#2" (.symbol "Z"))
      (peel (.symbol "Z"), peelInnerBindings) := by
  apply peel_recursive_evidence (.symbol "Z") peelOuterBindings "x#2"
  · decide +kernel
  · rfl
  · simp [peelOuterBindings]
  · rfl
  · exact (Spec.Match.Merge.hasLoop_eq_false_iff_semanticLoopFree _).mp (by decide +kernel)
  · apply normal_closed_assignment_list _ (by decide)
    intro entry present
    simp only [peelOuterBindings, List.mem_cons, List.not_mem_nil, or_false] at present
    rcases present with rfl | rfl | rfl <;>
      simp [successor, TypeSubst.typeVars, TypeSubst.typeVarsList]
  · intro valuation
    simp [Spec.Type.RuntimeRefinement.applyTypeValuation]

private theorem peel_two_evidence :
    EquationBodyEvidence peelSpace captureLive (peel (successor (successor (.symbol "Z")))) Atom.symbolType
      equationCaller (peel (.var "x#1"), Bindings.empty.assign "x#1" (successor (.symbol "Z")))
      (peel (successor (.symbol "Z")), peelOuterBindings) := by
  apply peel_recursive_evidence (successor (.symbol "Z")) equationCaller "x#1"
  · decide +kernel
  · rfl
  · simp [equationCaller, Bindings.assign, Bindings.empty, Bindings.isBound, Bindings.lookup]
  · rfl
  · exact (Spec.Match.Merge.hasLoop_eq_false_iff_semanticLoopFree _).mp (by decide +kernel)
  · apply normal_closed_assignment_list _ (by decide)
    intro entry present
    change entry ∈ [("x#1", successor (.symbol "Z")), ("caller", .symbol "kept")] at present
    simp only [List.mem_cons, List.not_mem_nil, or_false] at present
    rcases present with rfl | rfl <;> simp [successor, TypeSubst.typeVars, TypeSubst.typeVarsList]
  · intro valuation
    simp [successor, Spec.Type.RuntimeRefinement.applyTypeValuation]


private theorem peel_base_source :
    AtomDerivation (comparison := .records) peelSpace captureLive (peel (.symbol "Z")) Atom.symbolType peelInnerBindings
      (controlFuel + 3) [(.symbol "done", peelInnerBindings)] := by
  apply unary_raw_application_derivation captureLive (.symbol "Z") peelInnerBindings controlFuel
    (peelTyping (.symbol "Z") controlFuel (by omega)) rfl rfl (by decide) _
  · apply single_equation_call_derivation peelSpace "peel" (by decide) (by decide) (by decide)
      captureLive (.symbol "Z") peelInnerBindings controlFuel
      (.symbol "done", Bindings.empty) (.symbol "done", peelInnerBindings)
    · decide +kernel
    · decide +kernel
    · exact peel_base_evidence
    · exact .leaf captureLive (.symbol "done") Atom.symbolType peelInnerBindings (controlFuel - 1)
        (Or.inr ⟨Atom.symbolType, .symbol "done", Or.inr (Or.inl rfl)⟩)
  · rfl

private theorem peel_one_source :
    AtomDerivation (comparison := .records) peelSpace captureLive (peel (successor (.symbol "Z"))) Atom.symbolType peelOuterBindings
      (controlFuel + 6) [(.symbol "done", peelInnerBindings)] := by
  apply unary_raw_application_derivation captureLive (successor (.symbol "Z")) peelOuterBindings
    (controlFuel + 3) (peelTyping _ _ (by omega)) rfl rfl (by decide) _
  · apply single_equation_call_derivation peelSpace "peel" (by decide) (by decide) (by decide)
      captureLive (successor (.symbol "Z")) peelOuterBindings (controlFuel + 3)
      (peel (.var "x#2"), Bindings.empty.assign "x#2" (.symbol "Z"))
      (peel (.symbol "Z"), peelInnerBindings)
    · decide +kernel
    · decide +kernel
    · exact peel_one_evidence
    · exact peel_base_source
  · rfl

/-- A recursive rule, peel(S x) = peel(x), calls itself twice before its
base rule peel(Z) = done fires. The proof uses the same recursive source
family as arbitrary admitted bodies and retains both fresh rule frames. -/
theorem recursive_rule_source_derivation :
    AtomDerivation (comparison := .records) peelSpace captureLive (peel (successor (successor (.symbol "Z"))))
      Atom.symbolType equationCaller (controlFuel + 9) [(.symbol "done", peelInnerBindings)] := by
  apply unary_raw_application_derivation captureLive (successor (successor (.symbol "Z"))) equationCaller
    (controlFuel + 6) (peelTyping _ _ (by omega)) rfl rfl (by decide) _
  · apply single_equation_call_derivation peelSpace "peel" (by decide) (by decide) (by decide)
      captureLive (successor (successor (.symbol "Z"))) equationCaller (controlFuel + 6)
      (peel (.var "x#1"), Bindings.empty.assign "x#1" (successor (.symbol "Z")))
      (peel (successor (.symbol "Z")), peelOuterBindings)
    · decide +kernel
    · decide +kernel
    · exact peel_two_evidence
    · exact peel_one_source
  · rfl

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem peel_base_covered : peel_base_source.Covered := by
  have body := AtomDerivation.leaf (comparison := .records) (space := peelSpace) captureLive (.symbol "done") Atom.symbolType
    peelInnerBindings (controlFuel - 1)
    (Or.inr ⟨Atom.symbolType, .symbol "done", Or.inr (Or.inl rfl)⟩)
  have bodyCovered : body.Covered := AtomDerivation.Covered.leaf
    (leaf := Or.inr ⟨Atom.symbolType, .symbol "done", Or.inr (Or.inl rfl)⟩)
  have call := single_equation_call_derivation peelSpace "peel" (by decide) (by decide) (by decide)
    captureLive (.symbol "Z") peelInnerBindings controlFuel
    (.symbol "done", Bindings.empty) (.symbol "done", peelInnerBindings) _
    (by decide +kernel) (by decide +kernel) peel_base_evidence body
  have callCovered : call.Covered := single_equation_call_covered peelSpace "peel" (by decide) (by decide) (by decide)
    captureLive (.symbol "Z") peelInnerBindings controlFuel
    (.symbol "done", Bindings.empty) (.symbol "done", peelInnerBindings) _
    (by decide +kernel) (by decide +kernel) peel_base_evidence body (by decide)
    (by decide +kernel) (by decide +kernel) (by
      intro merged member clean
      have same : merged = peelInnerBindings := by
        exact List.mem_singleton.mp member
      subst merged
      decide +kernel) bodyCovered
  exact unary_raw_application_covered captureLive (.symbol "Z") peelInnerBindings controlFuel
    (peelTyping _ _ (by omega)) rfl rfl (by decide) _ call rfl
    (by decide +kernel) (by decide +kernel) callCovered

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem peel_one_covered : peel_one_source.Covered := by
  have call := single_equation_call_derivation peelSpace "peel" (by decide) (by decide) (by decide)
    captureLive (successor (.symbol "Z")) peelOuterBindings (controlFuel + 3)
    (peel (.var "x#2"), Bindings.empty.assign "x#2" (.symbol "Z")) (peel (.symbol "Z"), peelInnerBindings) _
    (by decide +kernel) (by decide +kernel) peel_one_evidence peel_base_source
  have callCovered : call.Covered := single_equation_call_covered peelSpace "peel" (by decide) (by decide) (by decide)
    captureLive (successor (.symbol "Z")) peelOuterBindings (controlFuel + 3)
    (peel (.var "x#2"), Bindings.empty.assign "x#2" (.symbol "Z")) (peel (.symbol "Z"), peelInnerBindings) _
    (by decide +kernel) (by decide +kernel) peel_one_evidence peel_base_source (by decide)
    (by decide +kernel) (by decide +kernel) (by
      intro merged member clean
      have same : merged = peelInnerBindings := by
        exact List.mem_singleton.mp member
      subst merged
      decide +kernel) peel_base_covered
  exact unary_raw_application_covered captureLive (successor (.symbol "Z")) peelOuterBindings (controlFuel + 3)
    (peelTyping _ _ (by omega)) rfl rfl (by decide) _ call rfl
    (by decide +kernel) (by decide +kernel) callCovered

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem recursive_rule_source_covered : recursive_rule_source_derivation.Covered := by
  have call := single_equation_call_derivation peelSpace "peel" (by decide) (by decide) (by decide)
    captureLive (successor (successor (.symbol "Z"))) equationCaller (controlFuel + 6)
    (peel (.var "x#1"), Bindings.empty.assign "x#1" (successor (.symbol "Z"))) (peel (successor (.symbol "Z")), peelOuterBindings) _
    (by decide +kernel) (by decide +kernel) peel_two_evidence peel_one_source
  have callCovered : call.Covered := single_equation_call_covered peelSpace "peel" (by decide) (by decide) (by decide)
    captureLive (successor (successor (.symbol "Z"))) equationCaller (controlFuel + 6)
    (peel (.var "x#1"), Bindings.empty.assign "x#1" (successor (.symbol "Z"))) (peel (successor (.symbol "Z")), peelOuterBindings) _
    (by decide +kernel) (by decide +kernel) peel_two_evidence peel_one_source (by decide)
    (by decide +kernel) (by decide +kernel) (by
      intro merged member clean
      have same : merged = peelOuterBindings := by
        exact List.mem_singleton.mp member
      subst merged
      decide +kernel) peel_one_covered
  exact unary_raw_application_covered captureLive (successor (successor (.symbol "Z"))) equationCaller (controlFuel + 6)
    (peelTyping _ _ (by omega)) rfl rfl (by decide) _ call rfl
    (by decide +kernel) (by decide +kernel) callCovered

/-- Local coverage of the recursive source earns a completion bound; no run
bound or previously completed machine execution is an assumption. -/
theorem recursive_rule_source_constructs_checked_completion (earned : ResultSet) :
    ∃ budget, ∀ extra, (Checked.machine HE.GroundedDispatch.none).run (budget + extra)
      ⟨peelSpace, .work (.atom (peel (successor (successor (.symbol "Z")))) Atom.symbolType
        equationCaller (controlFuel + 9) captureLive), [], earned⟩ =
      ([(.symbol "done", peelInnerBindings)], .finished
        ⟨peelSpace, .returning [], [], earned ++ [(.symbol "done", peelInnerBindings)]⟩) :=
  recursive_rule_source_derivation.checked_completed recursive_rule_source_covered earned


/-- A genuine recursive definition has an independent evaluation and an
executable completed collector with the same value and related full bindings. -/
theorem recursive_rule_independent_and_collected :
    (∃ output : Bindings, EvalAtomRawRel peelSpace noHost captureLive
      (peel (successor (successor (.symbol "Z")))) Atom.symbolType equationCaller (.symbol "done", output) ∧
      BindingRecordPerm peelInnerBindings output) ∧
    (∃ budget, ∀ later, collectReply peelSpace (peel (successor (successor (.symbol "Z"))))
      Atom.symbolType equationCaller (controlFuel + 9) (budget + later) captureLive =
        some [(.symbol "done", peelInnerBindings)]) :=
  ⟨recursive_rule_source_derivation.sound_records (.symbol "done", peelInnerBindings) (by simp) [] equationCaller (.refl _),
    recursive_rule_source_derivation.collect⟩

/-- The rule-space is genuinely recursive and equation-bearing. The
source admission neither erases the old caller nor reuses its protected name. -/
theorem recursive_rule_retains_scopes :
    ¬EquationFree peelSpace ∧
      peelInnerBindings.lookup "caller" = some (.symbol "kept") ∧
      peelInnerBindings.lookup "x#0" = none ∧
      peelInnerBindings.lookup "x#1" = some (successor (.symbol "Z")) ∧
      peelInnerBindings.lookup "x#2" = some (.symbol "Z") ∧
      peelInnerBindings ≠ equationCaller := by
  refine ⟨?_, by decide +kernel⟩
  intro free
  exact free (peel (successor (.var "x"))) (peel (.var "x")) (by simp [peelSpace, Space.ofList])

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
/-- The nested equation example passes every actual resource guard and keeps
both fresh frames as well as the original caller. -/
theorem checked_nested_equation_completed :
    (Checked.machine HE.GroundedDispatch.none).run 600
      ⟨recursiveSpace, .work (.atom recursiveQuery Atom.symbolType equationCaller
        (controlFuel + 11) captureLive), [], []⟩ =
      ([(.symbol "answer", innerRecursiveBindings)], .finished
        ⟨recursiveSpace, .returning [], [], [(.symbol "answer", innerRecursiveBindings)]⟩) := by rfl

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
/-- A recursive rule invokes itself twice before its base case. Completion
comes from the checked worker, not from two equal finite approximations. -/
theorem checked_recursive_rule_completed :
    (Checked.machine HE.GroundedDispatch.none).run 600
      ⟨peelSpace, .work (.atom (peel (successor (successor (.symbol "Z")))) Atom.symbolType
        equationCaller (controlFuel + 9) captureLive), [], []⟩ =
      ([(.symbol "done", peelInnerBindings)], .finished
        ⟨peelSpace, .returning [], [], [(.symbol "done", peelInnerBindings)]⟩) := by rfl

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
/-- Distinct declarations with equal returned atoms still deliver both full
occurrences, with their separate fresh binding endpoints. -/
theorem checked_duplicate_equations_completed :
    (Checked.machine HE.GroundedDispatch.none).run 600
      ⟨equationSpace, .work (.atom equationQuery Atom.symbolType equationCaller
        (controlFuel + 7) []), [], []⟩ =
      (equationAnswers, .finished ⟨equationSpace, .returning [], [], equationAnswers⟩) := by rfl

/-- The recursively computed answer is stable at every larger depth, justified
by the actual completed coverage above. -/
theorem checked_recursive_rule_all_depths (extra : Nat) :
    (machine HE.GroundedDispatch.none).run 600
      ⟨peelSpace, .work (.atom (peel (successor (successor (.symbol "Z")))) Atom.symbolType
        equationCaller (controlFuel + 9 + extra) captureLive), [], []⟩ =
      ([(.symbol "done", peelInnerBindings)], .finished
        ⟨peelSpace, .returning [], [], [(.symbol "done", peelInnerBindings)]⟩) := by
  simpa only [List.nil_append] using
    recursive_rule_source_derivation.checked_completed_deepen [] _ 600 extra _ checked_recursive_rule_completed

/-- Zero evaluator depth remains a resource request, even if enough scheduler
steps were supplied to finish a genuinely empty result. -/
theorem checked_depth_exhaustion_is_not_failure (value expected : Atom) (incoming : Bindings)
    (live : List Atom) :
    (Checked.machine HE.GroundedDispatch.none).run 3
      ⟨Space.empty, .work (.atom value expected incoming 0 live), [], []⟩ =
      ([], .suspended .evaluationDepth
        ⟨Space.empty, .work (.atom value expected incoming 0 live), [], []⟩) := rfl

theorem checked_empty_result_completes :
    (Checked.machine HE.GroundedDispatch.none).run 3
      ⟨Space.empty, .work (.args [.symbol "a"] [] Bindings.empty 1 []), [], []⟩ =
      ([], .finished ⟨Space.empty, .returning [], [], []⟩) := rfl

/-- A positive evaluator depth is insufficient when its equation-search leaf
has no depth. The exact operation is retained for a grant. -/
theorem checked_leaf_exhaustion_is_retained :
    (Checked.machine HE.GroundedDispatch.none).run 2
      ⟨Space.empty, .work (.call (.expression [.symbol "unknown"]) Atom.undefinedType Bindings.empty 1 []), [], []⟩ =
      ([], .suspended .leafDepth
        ⟨Space.empty, .work (.invocation (.ordinary Atom.undefinedType)
          (.expression [.symbol "unknown"]) Bindings.empty 1 []), [], []⟩) := rfl

/-- Taking one observation leaves the second equal occurrence in the saved
state. Resuming publishes it once without replaying the first. -/
theorem checked_duplicate_once_prefix (result : ResultPair) (earned : ResultSet) :
    (Checked.machine HE.GroundedDispatch.none).run 1
        ⟨Space.empty, .returning [result, result], [], earned⟩ =
      ([result], .exhausted ⟨Space.empty, .returning [result], [], earned ++ [result]⟩) ∧
    (Checked.machine HE.GroundedDispatch.none).run 2
        ⟨Space.empty, .returning [result], [], earned ++ [result]⟩ =
      ([result], .finished ⟨Space.empty, .returning [], [], (earned ++ [result]) ++ [result]⟩) := ⟨rfl, rfl⟩

/-- The request codec rejects malformed resource tags. A malformed saved
configuration also cannot become a completed reply after a depth grant. -/
theorem checked_malformed_resources_refused (events : ResultSet) :
    RecursiveDataExecution.Checked.readRequest (.expression [.symbol "he-eval-evaluation-depth-v1", .symbol "extra"]) = none ∧
    Checked.continueDataRun HE.GroundedDispatch.none 20 4
        (events, .suspended .evaluationDepth (.symbol "not-a-configuration")) =
      (events, .stuck (.symbol "not-a-configuration")) := ⟨rfl, rfl⟩

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
/-- The real duplicate-producing source can pause after its first delivered
occurrence. The unreported declaration and its fresh binding remain retained. -/
theorem checked_duplicate_equation_prefix :
    (Checked.machine HE.GroundedDispatch.none).run 63
      ⟨equationSpace, .work (.atom equationQuery Atom.symbolType equationCaller
        (controlFuel + 7) []), [], []⟩ =
      ([(.symbol "answer", equationBinding 0)], .exhausted
        ⟨equationSpace, .returning [(.symbol "answer", equationBinding 1)], [],
          [(.symbol "answer", equationBinding 0)]⟩) := by rfl

/-- Resuming the exact reached source checkpoint publishes only the second
occurrence and preserves both original declaration identities. -/
theorem checked_duplicate_equation_resume :
    (Checked.machine HE.GroundedDispatch.none).run 2
      ⟨equationSpace, .returning [(.symbol "answer", equationBinding 1)], [],
        [(.symbol "answer", equationBinding 0)]⟩ =
      ([(.symbol "answer", equationBinding 1)], .finished
        ⟨equationSpace, .returning [], [], equationAnswers⟩) := rfl

/-- A grant to the initially exhausted recursive computation enables its
actual covered run. The suspended request was not a completed empty answer. -/
theorem checked_recursive_grant_completes :
    Checked.continueRun HE.GroundedDispatch.none 600 (controlFuel + 9)
      ([], .suspended .evaluationDepth
        ⟨peelSpace, .work (.atom (peel (successor (successor (.symbol "Z")))) Atom.symbolType
          equationCaller 0 captureLive), [], []⟩) =
      ([(.symbol "done", peelInnerBindings)], .finished
        ⟨peelSpace, .returning [], [], [(.symbol "done", peelInnerBindings)]⟩) := by
  simpa only [Checked.continueRun, RecursiveMachine.Checked.replenish, Task.replenish,
    Nat.zero_add, List.nil_append] using checked_recursive_rule_completed

/-- The same real depth grant and completed recursive reply survive the
configuration codec, including every changed binding and protected scope. -/
theorem checked_recursive_data_grant_completes :
    Checked.continueDataRun HE.GroundedDispatch.none 600 (controlFuel + 9)
      ([], .suspended .evaluationDepth (RecursiveEncoding.configurationData
        ⟨peelSpace, .work (.atom (peel (successor (successor (.symbol "Z")))) Atom.symbolType
          equationCaller 0 captureLive), [], []⟩)) =
      ([(.symbol "done", peelInnerBindings)], .finished (RecursiveEncoding.configurationData
        ⟨peelSpace, .returning [], [], [(.symbol "done", peelInnerBindings)]⟩)) := by
  have represented := Checked.continueRun_representation HE.GroundedDispatch.none 600 (controlFuel + 9)
    ([], .suspended .evaluationDepth
      ⟨peelSpace, .work (.atom (peel (successor (successor (.symbol "Z")))) Atom.symbolType
        equationCaller 0 captureLive), [], []⟩)
  simpa only [checked_recursive_grant_completes, RecursiveDataExecution.representedOutcome] using represented

/-- The actual checked nested computation resumes the original native caller,
with the independently derived reply rather than a supplied host answer. -/
theorem checked_nested_equation_retained_handler (operations : NativeArgumentControl.Operations) :
    let endpoint := (NativeArgumentControl.request recursiveCallerWaiting
      (.evaluate recursiveCallerArgument recursiveCallerPrepared) 0).endpoint
    let reply : NativeArgumentControl.Reply :=
      ⟨endpoint, .evaluated [(.symbol "answer", innerRecursiveBindings)], 0⟩
    let after := NativeArgumentControl.replied recursiveCallerWaiting [] reply
      [.iterate (NativeArgumentControl.selectedSnapshot recursiveCallerArgument recursiveCallerPrepared
        [(.symbol "answer", innerRecursiveBindings)]) recursiveCallerPrepared]
    let initial : Configuration :=
      ⟨recursiveSpace, .work (.atom recursiveQuery Atom.symbolType equationCaller
        (controlFuel + 11) captureLive), [], []⟩
    ∃ used ≤ 601,
      ((NativeArgumentControlMachine.interactionMachine operations .stop).handle
        NativeArgumentControlEncoding.interactionCallback
        (checkedEvaluationService endpoint 0) (fun _ => initial)).run used
        (.running (.active recursiveCallerWaiting)) =
      (NativeArgumentControlEncoding.callEventData endpoint ::
        [(.symbol "answer", innerRecursiveBindings)].map sourceEvent ++
        [NativeArgumentControlEncoding.replyEventData (.returned (NativeArgumentControlEncoding.replyData reply))],
        .exhausted (.running (.active after))) :=
  nested_equation_source_derivation.checked_handled operations .stop recursiveCallerWaiting
    recursiveCallerArgument recursiveCallerPrepared 0 [] rfl (controlFuel + 11) 0
    [(.symbol "answer", innerRecursiveBindings)] 600 _ _ checked_nested_equation_completed

private def coverageNestedType : Nat → Atom
  | 0 => .symbol "Base"
  | depth + 1 => .expression [.symbol "Box", coverageNestedType depth]

/-- The rejected prefix is checked and the first applicable type is selected,
even though a later type lacks matching coverage. Requiring the whole list
would impose work which this first-success strategy never performs. -/
theorem checked_selection_ignores_uncovered_suffix :
    let value : Atom := .expression [.symbol "f"]
    let expected := coverageNestedType 40
    let rejected : Atom := .expression [.symbol "->", Atom.atomType, Atom.undefinedType]
    let selected : Atom := .expression [.symbol "->", Atom.undefinedType]
    let uncovered : Atom := .expression [.symbol "->", expected]
    functionTypeCovered value uncovered expected Space.empty Bindings.empty 8 = false ∧
      FirstSuccessRecursiveStrategy.selectionReady Space.empty value expected Bindings.empty 8
        [rejected, selected, uncovered] = true ∧
      Checked.blocked HE.GroundedDispatch.none
        ⟨Space.empty, .work (.functions value expected Bindings.empty 8
          [rejected, selected, uncovered] []), [], []⟩ = none := by decide +kernel

open Spec.Type.RuntimeRefinement

private def pairTerm (left right : Atom) : Atom := .expression [.symbol "Pair", left, right]
private def successorTerm (value : Atom) : Atom := .expression [.symbol "S", value]
private def pairedCall (argument : Atom) : Atom := .expression [.symbol "paired", argument]
private def pairedRule : Atom := .expression [.symbol "=",
  pairedCall (pairTerm (successorTerm (.var "x")) (successorTerm (.var "y"))),
  pairedCall (pairTerm (.var "x") (.var "y"))]
private def pairedBase : Atom := pairedCall (pairTerm (.symbol "Z") (.symbol "Z"))
private def pairedSpace : Space := Space.ofList [pairedRule, pairedRule,
  .expression [.symbol "=", pairedBase, .symbol "done"],
  .expression [.symbol ":", .symbol "paired", arrow [Atom.atomType] Atom.symbolType]]
private def pairedLive : List Atom := [.var "protected"]
private def pairedCaller : Bindings := ⟨[("caller", .expression [.symbol "held", .var "external"])], []⟩
private def pairedMatched (index : Fin 2) : Bindings :=
  ⟨[("x#" ++ toString index.val, .symbol "Z"), ("y#" ++ toString (index.val + 1), .symbol "Z")], []⟩
private def pairedBindings (index : Fin 2) : Bindings :=
  ⟨(pairedMatched index).assignments ++ pairedCaller.assignments, []⟩
private def pairedCandidate (index : Fin 2) : ResultPair :=
  (pairedCall (pairTerm (.var ("x#" ++ toString index.val)) (.var ("y#" ++ toString (index.val + 1)))),
    pairedMatched index)
private def pairedQuery : Atom := pairedCall
  (pairTerm (successorTerm (.symbol "Z")) (successorTerm (.symbol "Z")))
private def pairedResults : ResultSet :=
  [(.symbol "done", pairedBindings 0), (.symbol "done", pairedBindings 1)]

private theorem paired_covered : ∀ (position : Nat) (left right : Atom),
    pairedSpace.atoms[position]? = some (.expression [.symbol "=", left, right]) →
    ∀ key ∈ TypeSubst.typeVars right, key ∈ TypeSubst.typeVars left := by
  intro position left right stored key member
  have declared : (.expression [.symbol "=", left, right] : Atom) ∈ pairedSpace.atoms :=
    List.mem_of_getElem? stored
  simp only [pairedSpace, Space.ofList, List.mem_cons, List.not_mem_nil, or_false,
    pairedRule, pairedBase, pairedCall, pairTerm, successorTerm, Atom.expression.injEq,
    List.cons.injEq, Atom.symbol.injEq, and_true] at declared
  rcases declared with recursive | recursive | base | impossible
  · rcases recursive with ⟨_, rfl, rfl⟩
    simpa [TypeSubst.typeVars, TypeSubst.typeVarsList] using member
  · rcases recursive with ⟨_, rfl, rfl⟩
    simpa [TypeSubst.typeVars, TypeSubst.typeVarsList] using member
  · obtain ⟨_, rfl, rfl⟩ := base
    simp [TypeSubst.typeVars] at member
  · simp at impossible

private theorem paired_caller_normal : TypeSubst.Normal pairedCaller.assignments := by
  simp [pairedCaller, TypeSubst.Normal, TypeSubst.keys, TypeSubst.typeVars, TypeSubst.typeVarsList]

private theorem paired_bindings_normal (index : Fin 2) :
    TypeSubst.Normal (pairedBindings index).assignments := by
  fin_cases index <;> constructor
  all_goals try decide
  all_goals
    intro name value member key occurs
    simp only [pairedBindings, pairedMatched, pairedCaller, List.mem_append,
      List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at member
    rcases member with (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) | ⟨rfl, rfl⟩
    · simp [TypeSubst.typeVars] at occurs
    · simp [TypeSubst.typeVars] at occurs
    · have same : key = "external" := by
        simpa [TypeSubst.typeVars, TypeSubst.typeVarsList] using occurs
      subst key
      decide

private def pairedTyping (argument : Atom) (fuel : Nat) (enough : controlFuel ≤ fuel) :
    ApplicationTyping pairedSpace "paired" [argument] Atom.symbolType fuel :=
  unaryRawSymbolTyping pairedSpace "paired" argument fuel enough (by decide +kernel)
    (by decide) (by decide)

private theorem paired_base_source (index : Fin 2) :
    AtomDerivation (comparison := .records) pairedSpace pairedLive pairedBase Atom.symbolType (pairedBindings index)
      (controlFuel + 3) [(.symbol "done", pairedBindings index)] := by
  apply unary_raw_application_derivation pairedLive (pairTerm (.symbol "Z") (.symbol "Z"))
    (pairedBindings index) controlFuel (pairedTyping _ _ (by omega)) rfl rfl (by decide)
    _
  · apply single_equation_call_derivation pairedSpace "paired" (by decide) (by decide) (by decide)
      pairedLive (pairTerm (.symbol "Z") (.symbol "Z")) (pairedBindings index) controlFuel
      (.symbol "done", Bindings.empty) (.symbol "done", pairedBindings index)
    · fin_cases index <;> decide +kernel
    · fin_cases index <;> decide +kernel
    · apply EquationBodyEvidence.of_closed_query_hit (fuel := controlFuel)
        (by decide) paired_covered rfl (paired_bindings_normal index)
      · fin_cases index <;> decide +kernel
      · fin_cases index <;> decide +kernel
      · decide
    · exact .leaf pairedLive (.symbol "done") Atom.symbolType (pairedBindings index) (controlFuel - 1)
        (Or.inr ⟨Atom.symbolType, .symbol "done", Or.inr (Or.inl rfl)⟩)
  · rfl

private theorem paired_inputs (index : Fin 2) :
    equationInputs pairedCaller (controlFuel + 3) (pairedCandidate index) =
      [(pairedBase, pairedBindings index)] := by
  fin_cases index <;> decide +kernel

private theorem paired_candidates :
    equationCandidates pairedSpace pairedLive pairedQuery Atom.symbolType pairedCaller (controlFuel + 3) =
      [pairedCandidate 0, pairedCandidate 1] := by decide +kernel

/-- The recursive rule binds two variables at once. Its two physical
declarations recurse independently and retain the caller's open value. -/
theorem multivariable_recursive_source_derivation :
    AtomDerivation (comparison := .records) pairedSpace pairedLive pairedQuery Atom.symbolType pairedCaller
      (controlFuel + 6) pairedResults := by
  apply unary_raw_application_derivation pairedLive
    (pairTerm (successorTerm (.symbol "Z")) (successorTerm (.symbol "Z"))) pairedCaller
    (controlFuel + 3) (pairedTyping _ _ (by omega)) rfl rfl (by decide) _
  · have call := CallDerivation.ordinaryEquations (comparison := .records) pairedLive "paired"
      [pairTerm (successorTerm (.symbol "Z")) (successorTerm (.symbol "Z"))]
      Atom.symbolType pairedCaller (controlFuel + 3)
      (fun _ request => [(.symbol "done", request.2)]) (by decide) (by decide) (by decide)
      (by change rawQueryResults pairedSpace pairedQuery Atom.symbolType pairedCaller
            (controlFuel + 3) pairedLive ≠ []; decide +kernel) ?_ ?_ ?_
    · convert call using 1; rfl
    · intro candidate hit request input
      apply EquationBodyEvidence.of_closed_query_hit (by decide) paired_covered rfl paired_caller_normal hit input
      · change candidate ∈ equationCandidates pairedSpace pairedLive pairedQuery Atom.symbolType pairedCaller (controlFuel + 3) at hit
        rw [paired_candidates] at hit
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hit
        rcases hit with rfl | rfl <;> decide
    · intro candidate hit request input
      change candidate ∈ equationCandidates pairedSpace pairedLive pairedQuery Atom.symbolType pairedCaller (controlFuel + 3) at hit
      rw [paired_candidates] at hit
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hit
      rcases hit with rfl | rfl
      all_goals
        rw [paired_inputs] at input
        obtain rfl := List.mem_singleton.mp input
        simp [pairedBase, pairedCall, Spec.Eval.Minimal.IsFunction]
    · intro candidate hit request input
      change candidate ∈ equationCandidates pairedSpace pairedLive pairedQuery Atom.symbolType pairedCaller (controlFuel + 3) at hit
      rw [paired_candidates] at hit
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hit
      rcases hit with rfl | rfl
      all_goals
        rw [paired_inputs] at input
        obtain rfl := List.mem_singleton.mp input
      · exact .evaluate pairedLive pairedQuery Atom.symbolType pairedBase _ (controlFuel + 3) _
          (by decide) (by simp [IsEmptyOrErrorRel, IsErrorRel, Atom.empty, pairedBase, pairedCall])
          (paired_base_source 0)
      · exact .evaluate pairedLive pairedQuery Atom.symbolType pairedBase _ (controlFuel + 3) _
          (by decide) (by simp [IsEmptyOrErrorRel, IsErrorRel, Atom.empty, pairedBase, pairedCall])
          (paired_base_source 1)
  · rfl


set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
/-- Actual resource guards accept the recursive, two-variable workload.
Both physical declarations retain independent bindings and the open caller. -/
theorem checked_multivariable_recursive_completed :
    (Checked.machine HE.GroundedDispatch.none).run 600
      ⟨pairedSpace, .work (.atom pairedQuery Atom.symbolType pairedCaller
        (controlFuel + 6) pairedLive), [], []⟩ =
      (pairedResults, .finished ⟨pairedSpace, .returning [], [], pairedResults⟩) := by rfl

/-- The completed multi-variable worker delivers independently justified
occurrences, with both binding endpoints compared by the same observer. -/
theorem checked_multivariable_recursive_source_sound (scope : List String)
    (incoming : Bindings) (related : BindingRecordPerm pairedCaller incoming) :
    ∀ result ∈ pairedResults, ∃ output,
      EvalAtomRawRel pairedSpace noHost pairedLive (protectedScope := scope)
        pairedQuery Atom.symbolType incoming (result.1, output) ∧
      BindingRecordPerm result.2 output := by
  intro result member
  obtain ⟨output, source, framed⟩ :=
    multivariable_recursive_source_derivation.checked_completed_sound [] pairedResults 600 _
      checked_multivariable_recursive_completed scope incoming (.records related) result member
  exact ⟨output, source, framed.related⟩

/-- Depth stability follows from real completion coverage, including both
recursive branches. It is not inferred from matching finite approximations. -/
theorem checked_multivariable_recursive_all_depths (extra : Nat) :
    (machine HE.GroundedDispatch.none).run 600
      ⟨pairedSpace, .work (.atom pairedQuery Atom.symbolType pairedCaller
        (controlFuel + 6 + extra) pairedLive), [], []⟩ =
      (pairedResults, .finished ⟨pairedSpace, .returning [], [], pairedResults⟩) := by
  simpa only [List.nil_append] using
    multivariable_recursive_source_derivation.checked_completed_deepen [] pairedResults 600 extra _
      checked_multivariable_recursive_completed

/-- Shared values do not merge physical declarations. The two bindings still
retain the caller's open payload, without capturing either free name. -/
theorem multivariable_recursive_occurrences_and_caller :
    pairedResults.length = 2 ∧
    pairedResults.map Prod.fst = [.symbol "done", .symbol "done"] ∧
    pairedBindings 0 ≠ pairedBindings 1 ∧
    ∀ index : Fin 2,
      (pairedBindings index).lookup "caller" = some (.expression [.symbol "held", .var "external"]) ∧
      (pairedBindings index).lookup "external" = none ∧
      (pairedBindings index).lookup "protected" = none := by decide +kernel

/-- Repeated pattern variables impose equality; an equal second occurrence
checks the first assignment instead of creating another assignment row. -/
theorem nonlinear_closed_match_reuses_assignment :
    matchAtoms (pairTerm (.symbol "Z") (.symbol "Z")) (pairTerm (.var "x") (.var "x")) 32 =
      [Bindings.empty.assign "x" (.symbol "Z")] ∧
    Spec.Match.Merge.MatchRel Spec.Match.Merge.equalityGroundedSemantic
      (pairTerm (.symbol "Z") (.symbol "Z")) (pairTerm (.var "x") (.var "x"))
      (Bindings.empty.assign "x" (.symbol "Z")) := by
  have matched : matchAtoms (pairTerm (.symbol "Z") (.symbol "Z"))
      (pairTerm (.var "x") (.var "x")) 32 = [Bindings.empty.assign "x" (.symbol "Z")] := by decide +kernel
  refine ⟨matched, ?_⟩
  apply (closed_target_runtime_match_source (by decide) (fuel := 32) ?_).1
  rw [matched]
  simp

/-- A nonlinear pattern rejects unequal closed components at every matcher
depth, not merely at a chosen insufficient budget. -/
theorem nonlinear_distinct_closed_refused (left right : Atom) (name : String)
    (leftClosed : TypeSubst.typeVars left = []) (rightClosed : TypeSubst.typeVars right = [])
    (different : left ≠ right) (fuel : Nat) :
    matchAtoms (pairTerm left right) (pairTerm (.var name) (.var name)) fuel = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro output member
  have targetClosed : TypeSubst.typeVars (pairTerm left right) = [] := by
    simp [pairTerm, TypeSubst.typeVars, TypeSubst.typeVarsList, leftClosed, rightClosed]
  have frame := (closed_target_runtime_match_source targetClosed member).2
  have equation := runtime_match_type_solution member _ frame.satisfies
  simp only [pairTerm, applyTypeValuation, List.map_cons, List.map_nil, Atom.expression.injEq,
    List.cons.injEq, true_and, and_true] at equation
  have leftFixed := closed_valuation (Theory.presentedValuation output.assignments) leftClosed
  have rightFixed := closed_valuation (Theory.presentedValuation output.assignments) rightClosed
  exact different (leftFixed.symm.trans (equation.1.trans (equation.2.symm.trans rightFixed)))

/-- Raw demand retains the entire recursive source term. Source equations do
not override the caller's request to treat it as an atom. -/
theorem multivariable_raw_demand_preserves_term :
    AtomDerivation (comparison := .records) pairedSpace pairedLive pairedQuery Atom.atomType pairedCaller
      (controlFuel + 6) [(pairedQuery, pairedCaller)] :=
  .leaf pairedLive pairedQuery Atom.atomType pairedCaller (controlFuel + 5)
    (Or.inr ⟨Atom.expressionType, .expression _, Or.inl rfl⟩)


private def nonlinearSpace : Space := Space.ofList [
  .expression [.symbol "=", .expression [.symbol "same", pairTerm (.var "x") (.var "x")], .var "x"]]

/-- The general source-admission constructor also handles a nonlinear rule.
The second occurrence constrains the first binding; it creates no extra row. -/
theorem nonlinear_equation_body_admitted :
    EquationBodyEvidence nonlinearSpace pairedLive
      (.expression [.symbol "same", pairTerm (.symbol "Z") (.symbol "Z")])
      Atom.symbolType pairedCaller
      (.var "x#0", Bindings.empty.assign "x#0" (.symbol "Z"))
      (.symbol "Z", ⟨[("x#0", .symbol "Z")] ++ pairedCaller.assignments, []⟩) := by
  refine EquationBodyEvidence.of_closed_query_hit (fuel := 32) (by decide) ?_ rfl paired_caller_normal ?_ ?_ ?_
  · intro position left right stored name member
    have declared := List.mem_of_getElem? stored
    simp only [nonlinearSpace, Space.ofList, List.mem_singleton, Atom.expression.injEq,
      List.cons.injEq, true_and, and_true] at declared
    obtain ⟨rfl, rfl⟩ := declared
    simpa [pairTerm, TypeSubst.typeVars, TypeSubst.typeVarsList] using member
  · decide +kernel
  · decide +kernel
  · decide

/-- A body variable not determined by the pattern can vary while the complete
matched pattern and all stored constraints stay fixed. This is why variable
coverage is required by the generic materialization construction. -/
theorem uncovered_body_variable_not_determined :
    ∃ left right : String → Atom,
      TypeBindingSatisfied left (Bindings.empty.assign "bound" (.symbol "Z")) ∧
      TypeBindingSatisfied right (Bindings.empty.assign "bound" (.symbol "Z")) ∧
      applyTypeValuation left (pairTerm (.var "bound") (.var "bound")) =
        applyTypeValuation right (pairTerm (.var "bound") (.var "bound")) ∧
      applyTypeValuation left (.var "uncovered") ≠
        applyTypeValuation right (.var "uncovered") := by
  let left : String → Atom := fun name => if name = "bound" then .symbol "Z" else .symbol "A"
  let right : String → Atom := fun name => if name = "bound" then .symbol "Z" else .symbol "B"
  refine ⟨left, right, ?_, ?_, ?_, ?_⟩
  · simp [TypeBindingSatisfied, Bindings.assign, Bindings.empty, Bindings.isBound, Bindings.lookup, left, applyTypeValuation]
  · simp [TypeBindingSatisfied, Bindings.assign, Bindings.empty, Bindings.isBound, Bindings.lookup, right, applyTypeValuation]
  · simp [pairTerm, applyTypeValuation, left, right]
  · simp [applyTypeValuation, left, right]


set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
/-- This worker's actual delivery policy can pause after the first recursive
occurrence. Its saved state retains the second occurrence and its full frame. -/
theorem checked_multivariable_recursive_prefix :
    (Checked.machine HE.GroundedDispatch.none).run 161
      ⟨pairedSpace, .work (.atom pairedQuery Atom.symbolType pairedCaller
        (controlFuel + 6) pairedLive), [], []⟩ =
      ([(.symbol "done", pairedBindings 0)], .exhausted
        ⟨pairedSpace, .returning [(.symbol "done", pairedBindings 1)], [],
          [(.symbol "done", pairedBindings 0)]⟩) := by rfl

/-- Resuming the reached checkpoint publishes only its remaining occurrence;
it does not re-run either recursive source branch. -/
theorem checked_multivariable_recursive_resume :
    (Checked.machine HE.GroundedDispatch.none).run 2
      ⟨pairedSpace, .returning [(.symbol "done", pairedBindings 1)], [],
        [(.symbol "done", pairedBindings 0)]⟩ =
      ([(.symbol "done", pairedBindings 1)], .finished
        ⟨pairedSpace, .returning [], [], pairedResults⟩) := rfl

/-- The existing service protocol carries the same independently justified
multi-variable result and retained bindings. -/
theorem checked_multivariable_recursive_service (endpoint : Atom) (charge : Nat) :
    (checkedEvaluationService endpoint charge).run 600
      ⟨pairedSpace, .work (.atom pairedQuery Atom.symbolType pairedCaller
        (controlFuel + 6) pairedLive), [], []⟩ =
      (pairedResults.map sourceEvent, .finished (.returned
        (NativeArgumentControlEncoding.replyData ⟨endpoint, .evaluated pairedResults, charge⟩))) :=
  multivariable_recursive_source_derivation.checked_service_completed pairedResults 600 _
    checked_multivariable_recursive_completed endpoint charge


end Controls

namespace ArgumentContinuationControls


open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Spec.Eval Spec.Type Spec.Type.Presentation
open Spec.Bindings.ScopeObservation (BindingRecordPerm)
open RecursiveTasks FirstSuccessRecursiveExecution FirstSuccessRawExecution
open FirstSuccessSourceApplicability FirstSuccessLeafEvaluation
open Mettapedia.GSLT.Distinction.ProductiveBlocks

private def rejectedSpace : Space := ⟨[
  .expression [.symbol ":", .symbol "bad", .symbol "Wrong"],
  .expression [.symbol ":", .symbol "bad", .symbol "Wrong"]]⟩
private def wanted : Atom := .symbol "Wanted"
private def bad : Atom := .symbol "bad"
private def failure : Atom := mkError bad (.badType wanted (.symbol "Wrong"))
private def failures (caller : Bindings) : ResultSet := [(failure, caller), (failure, caller)]
private def untouched : Atom := .expression [.symbol "external-effect", .var "pending"]
private def caller : Bindings := ⟨[("old", .symbol "kept")], []⟩
private def live : List Atom := [.var "pending"]

/-- Duplicate declarations produce duplicate changed failures, under any caller
bindings and any live pending syntax. -/
theorem rejected_head_derivation (incoming : Bindings) (fuel : Nat) (scope : List Atom) :
    AtomDerivation (comparison := .records) rejectedSpace scope bad wanted incoming (fuel + 1) (failures incoming) := by
  have types : getAtomTypes rejectedSpace (.symbol "bad") = [.symbol "Wrong", .symbol "Wrong"] := by decide
  have derived := AtomDerivation.symbolRejected (comparison := .records) (space := rejectedSpace) scope "bad" wanted incoming fuel
    (by decide) (by decide) (by decide) rfl
    (by intro actual member; rw [types] at member; simp only [List.mem_cons, List.not_mem_nil, or_false, or_self] at member; subst actual; rfl)
    (by intro actual member; rw [types] at member; simp only [List.mem_cons, List.not_mem_nil, or_false, or_self] at member; subst actual; simp [ClosedTypeFits, wanted, Atom.undefinedType, Atom.atomType])
  simpa only [bad, types, List.map_cons, List.map_nil, wanted, failure, failures] using derived

/-- The unexecuted suffix may contain arbitrary syntax and expected types.
The failed head requires no service or source theorem for that suffix. -/
theorem rejected_argument_source (incoming : Bindings) (fuel : Nat)
    (remaining types scope : List Atom) :
    Realizes rejectedSpace (.args (bad :: remaining) (wanted :: types) incoming (fuel + 2) scope)
      (failures incoming) ∧
    ∀ result ∈ failures incoming, ∀ independentIncoming, BindingRecordPerm incoming independentIncoming →
      ∃ independentOutput : Bindings,
        InterpretArgsRel rejectedSpace noHost scope (bad :: remaining) (wanted :: types)
          independentIncoming (result.1, independentOutput) ∧
        BindingRecordPerm result.2 independentOutput := by
  have head := (rejected_head_derivation incoming fuel (remaining ++ types ++ scope)).argument_head_source
  have children : ∀ selected ∈ failures incoming,
      (selected.1 != bad && isEmptyOrError selected.1) = false →
      Realizes rejectedSpace (.args remaining types selected.2 (fuel + 1) (selected.1 :: scope)) [] ∧
      ∀ result ∈ ([] : ResultSet), ∀ independentHead, BindingRecordPerm selected.2 independentHead →
        ∃ independentOutput : Bindings, InterpretArgsRel rejectedSpace noHost (selected.1 :: scope)
          remaining types independentHead (result.1, independentOutput) ∧
          BindingRecordPerm result.2 independentOutput := by
    intro selected member guard
    simp only [failures, List.mem_cons, List.not_mem_nil, or_false, or_self] at member
    subst selected
    have failed : (failure != bad && isEmptyOrError failure) = true := by decide
    rw [failed] at guard
    cases guard
  have joined := arguments_cons_source_join (tails := fun _ => []) head children
  have exactReplies : argumentOutputs bad (failures incoming) (fun _ => []) = failures incoming := by
    have failed : (failure != bad && isEmptyOrError failure) = true := by decide
    simp only [argumentOutputs, failures, List.flatMap_cons, List.flatMap_nil, failed,
      if_true, List.append_nil, List.singleton_append]
  simpa only [exactReplies, Nat.add_assoc] using joined

/-- A preceding selected argument remains in the independent history when a
later argument fails. The failure is propagated, rather than wrapped as data. -/
theorem retained_prefix_failure_source (incoming : Bindings) (fuel : Nat)
    (remaining types scope : List Atom) :
    Realizes rejectedSpace
      (.args (.symbol "prefix" :: bad :: remaining) (Atom.atomType :: wanted :: types)
        incoming (fuel + 3) scope) (failures incoming) ∧
    ∀ result ∈ failures incoming, ∀ independentIncoming, BindingRecordPerm incoming independentIncoming →
      ∃ independentOutput : Bindings,
        InterpretArgsRel rejectedSpace noHost scope
          (.symbol "prefix" :: bad :: remaining) (Atom.atomType :: wanted :: types)
          independentIncoming (result.1, independentOutput) ∧
        BindingRecordPerm result.2 independentOutput := by
  have leaf : LeafRel (.symbol "prefix") Atom.atomType :=
    Or.inr ⟨Atom.symbolType, .symbol "prefix", Or.inl rfl⟩
  have head := (AtomDerivation.leaf (space := rejectedSpace)
    ((bad :: remaining) ++ (wanted :: types) ++ scope) (.symbol "prefix") Atom.atomType
    incoming (fuel + 1) leaf).argument_head_source
  have children : ∀ selected ∈ [(.symbol "prefix", incoming)],
      (selected.1 != .symbol "prefix" && isEmptyOrError selected.1) = false →
      Realizes rejectedSpace (.args (bad :: remaining) (wanted :: types) selected.2
        (fuel + 1 + 1) (selected.1 :: scope)) (failures incoming) ∧
      ∀ result ∈ failures incoming, ∀ independentHead, BindingRecordPerm selected.2 independentHead →
        ∃ independentOutput : Bindings,
          InterpretArgsRel rejectedSpace noHost (selected.1 :: scope)
            (bad :: remaining) (wanted :: types) independentHead (result.1, independentOutput) ∧
          BindingRecordPerm result.2 independentOutput := by
    intro selected member _
    obtain rfl := List.mem_singleton.mp member
    simpa only [Nat.add_assoc] using rejected_argument_source incoming fuel remaining types
      (.symbol "prefix" :: scope)
  have joined := arguments_cons_source_join (tails := fun _ => failures incoming) head children
  have exactReplies : argumentOutputs (.symbol "prefix") [(.symbol "prefix", incoming)]
      (fun _ => failures incoming) = failures incoming := by
    have failed : argumentsSucceeded failure = false := by decide
    simp [argumentOutputs, RecursiveTasks.argumentTail, failures, failed]
  simpa only [exactReplies, Nat.add_assoc] using joined

/-- These are native-independent HE machine checks with explicit pending scope.
The effect-shaped suffix is not entered. -/
theorem checked_failure_occurrences :
    (Checked.machine HE.GroundedDispatch.none).run 100
      ⟨rejectedSpace, .work (.args [.symbol "prefix", bad, untouched]
        [Atom.atomType, wanted, Atom.undefinedType] caller 10 live), [], []⟩ =
      (failures caller, .finished ⟨rejectedSpace, .returning [], [], failures caller⟩) := by rfl

/-- A cut after the first error occurrence retains the second occurrence and
the caller record. Equal error values do not license duplicate elimination. -/
theorem checked_failure_prefix :
    (Checked.machine HE.GroundedDispatch.none).run 19
      ⟨rejectedSpace, .work (.args [.symbol "prefix", bad, untouched]
        [Atom.atomType, wanted, Atom.undefinedType] caller 10 live), [], []⟩ =
      ([(failure, caller)], .exhausted
        ⟨rejectedSpace, .returning [(failure, caller)], [], [(failure, caller)]⟩) := rfl

theorem checked_failure_resume :
    (Checked.machine HE.GroundedDispatch.none).run 2
      ⟨rejectedSpace, .returning [(failure, caller)], [], [(failure, caller)]⟩ =
      ([(failure, caller)], .finished ⟨rejectedSpace, .returning [], [], failures caller⟩) := rfl

/-- Actual checked pause/resume constructs independent success/failure
histories for all final occurrences, without erasing the input environment. -/
theorem checked_failure_resumed_source :
    ∀ result ∈ failures caller, ∃ independentOutput : Bindings,
      BindingRecordPerm result.2 independentOutput ∧
      ((∃ selected,
        RetainedArgumentSpecification.HistoryRel rejectedSpace noHost live storageTypeService
          [.symbol "prefix", bad, untouched] [Atom.atomType, wanted, Atom.undefinedType]
          caller selected independentOutput ∧
        result.1 = argumentPacket (selected.map Prod.fst)) ∨
      (∃ selected,
        RetainedArgumentSpecification.FailureHistoryRel rejectedSpace noHost live storageTypeService
          [.symbol "prefix", bad, untouched] [Atom.atomType, wanted, Atom.undefinedType]
          caller selected (result.1, independentOutput))) := by
  have joined := retained_prefix_failure_source caller 7 [untouched] [Atom.undefinedType] live
  have checked := checked_argument_resume_source joined.1 joined.2 [] [(failure, caller)]
    [(failure, caller)] 19 2 _ _ checked_failure_prefix checked_failure_resume
  intro result member
  exact checked.2.2 result member caller (.refl _)

/-- A completed semantic type rejection is distinct from the resource guard
refusing an uncovered lower-level match. The latter retains the whole task. -/
theorem shallow_cast_is_pending :
    (Checked.machine HE.GroundedDispatch.none).run 1
      ⟨rejectedSpace, .work (.atom bad wanted caller 1 live), [], []⟩ =
      ([], .suspended .leafDepth
        ⟨rejectedSpace, .work (.atom bad wanted caller 1 live), [], []⟩) := rfl

/-- A finite independent rejection proof is not itself a resource
certificate: its zero-depth matcher has not checked either type occurrence. -/
theorem shallow_source_has_no_coverage :
    ¬(rejected_head_derivation caller 0 live).Covered := by
  intro covered
  obtain ⟨budget, finished⟩ :=
    (rejected_head_derivation caller 0 live).checked_completed covered []
  have stopped : (Checked.machine HE.GroundedDispatch.none).run (budget + 1)
      ⟨rejectedSpace, .work (.atom bad wanted caller 1 live), [], []⟩ =
      ([], .suspended .leafDepth
        ⟨rejectedSpace, .work (.atom bad wanted caller 1 live), [], []⟩) := rfl
  have contradiction := finished 1
  rw [stopped] at contradiction
  cases contradiction

/-- Error-shaped input under Atom demand is data, so the tail does run and the
returned packet contains that original atom. -/
theorem raw_error_argument_is_data :
    (Checked.machine HE.GroundedDispatch.none).run 50
      ⟨rejectedSpace, .work (.args [failure, .symbol "kept"]
        [Atom.atomType, Atom.atomType] caller 5 live), [], []⟩ =
      ([(argumentPacket [failure, .symbol "kept"], caller)], .finished
        ⟨rejectedSpace, .returning [], [], [(argumentPacket [failure, .symbol "kept"], caller)]⟩) := rfl

theorem raw_error_argument_source :
    RetainedArgumentSpecification.HistoryRel rejectedSpace noHost live storageTypeService
      [failure, .symbol "kept"] [Atom.atomType, Atom.atomType] caller
      [(failure, caller), (.symbol "kept", caller)] caller :=
  RetainedArgumentSpecification.raw_history rejectedSpace noHost live storageTypeService
    [failure, .symbol "kept"] caller

theorem failure_occurrences_are_not_one_packet :
    (failures caller).length = 2 ∧
      failures caller ≠ [(argumentPacket [failure, failure], caller)] := by decide


end ArgumentContinuationControls

/-! ## Alias-bearing caller representation boundary

The independently coherent caller below is satisfiable and loop-free. Replaying
its relations through the candidate-first executable merge adds a redundant
equality occurrence. The independent caller-first merge only inserts the fresh
assignment, so relation-list permutation cannot be a general source boundary.
No result occurrence or execution checkpoint is normalized by these controls.
-/

namespace AliasMergeControls

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Spec.Match.Merge
open Spec.Bindings.ScopeObservation
open Spec.Type.RuntimeRefinement
open Spec.Match.ModelTheory
open Spec.Match.StructuralModel
def caller : Bindings := ⟨[("x", .expression [.symbol "F", .var "z"]),
  ("y", .expression [.symbol "F", .var "w"]), ("z", .symbol "A"), ("w", .symbol "A")], [("x", "y")]⟩
def fresh : Bindings := ⟨[("private", .symbol "B")], []⟩
def reconciled : Bindings := {caller with equalities := [("x", "y"), ("z", "w")]}

def actual : Bindings :=
  ⟨fresh.assignments ++ reconciled.assignments,
    [("x", "y"), ("z", "w"), ("z", "w")]⟩

set_option maxRecDepth 12000 in
/-- Exact result of the Lean merge algorithm. This is not a claim about the
internal binding representation of a Rust or C implementation. -/
theorem lean_merge_result : mergeBindings fresh reconciled 50 = [actual] := by
  decide

theorem reconciled_acyclic : reconciled.hasLoop = false := by decide

def model (name : String) : Atom :=
  if name = "x" ∨ name = "y" then .expression [.symbol "F", .symbol "A"]
  else if name = "z" ∨ name = "w" then .symbol "A"
  else if name = "private" then .symbol "B" else .var name

theorem reconciled_satisfiable : TypeBindingSatisfied model reconciled := by
  constructor
  · intro key value member
    simp only [reconciled, caller, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at member
    rcases member with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      simp [model, applyTypeValuation]
  · intro key value member
    simp only [reconciled, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at member
    rcases member with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp [model]

private theorem add_fresh_forced {p : Parameters} {seed out : Bindings} {key : String} {value : Atom}
    (empty : seed.classValues key = []) (insert : AddVarBindingRel p seed key value out) :
    out = seed.assign key value := by
  cases insert with
  | fresh => rfl
  | same order _ _ => simpa [empty] using order.length_eq
  | conflict order _ _ _ _ => simpa [empty] using order.length_eq
  | reconcile order _ _ _ => simpa [empty] using order.length_eq

private theorem singleton_fresh_merge_forced {p : Parameters} {seed out : Bindings}
    {key : String} {value : Atom} (empty : seed.classValues key = [])
    (merge : MergeRel p seed (Bindings.empty.assign key value) out) :
    out = seed.assign key value := by
  rcases merge with ⟨order, steps⟩
  have singleton := List.perm_singleton.mp order
  cases singleton
  cases steps with
  | value inserted rest =>
    cases rest
    exact add_fresh_forced empty inserted

theorem independent_fresh_merge_forced {p : Parameters} {out : Bindings}
    (merge : MergeRel p reconciled fresh out) :
    out = reconciled.assign "private" (.symbol "B") := by
  exact singleton_fresh_merge_forced (by decide) merge

/-- A source merge of the fresh right-hand assignment cannot reproduce the
extra equality occurrence introduced by the Lean candidate-first merger. -/
theorem no_source_record_permutation {p : Parameters} :
    ¬∃ out, MergeRel p reconciled fresh out ∧ BindingRecordPerm actual out := by
  rintro ⟨out, merge, related⟩
  have forced := independent_fresh_merge_forced merge
  subst out
  have lengths := related.equalities.length_eq
  norm_num [actual, reconciled, Bindings.assign] at lengths

theorem source_merge_exists (p : Parameters) :
    MergeRel p reconciled fresh (reconciled.assign "private" (.symbol "B")) := by
  exact .mk (.refl _) (.value (.fresh (by decide)) .nil)

theorem closed_fresh_match :
    matchAtoms (.symbol "B") (.var "private") 50 = [fresh] := by decide

theorem outside_caller : "private" ∉ specBindingVars reconciled := by decide

set_option maxRecDepth 12000 in
theorem reconciled_readout_coherent :
    ∀ key value, (key, value) ∈ reconciled.assignments →
      reconciled.applyFull (.var key) 50 = reconciled.applyFull value 50 := by
  intro key value member
  simp only [reconciled, caller, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at member
  rcases member with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide

theorem reconciled_structurally_solved : ClassAssignmentsStructurallySolved reconciled := by
  intro left right leftValue rightValue leftStored rightStored sameClass
  simp only [reconciled, caller, List.mem_cons, List.not_mem_nil, or_false,
    Prod.mk.injEq] at leftStored rightStored
  rcases leftStored with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    rcases rightStored with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  all_goals first
    | exact AtomSolved.refl _ _
    | exact .expression (.cons (.symbol "F") (.cons (.varVar (by decide)) .nil))
    | exfalso; revert sameClass; decide

theorem reconciled_nonvariable : AssignmentsNonVariable reconciled := by
  intro key value member
  simp only [reconciled, caller, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at member
  rcases member with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rfl

theorem reconciled_source_coherent :
    CanonicalClassCoherent reconciled
      ((hasLoop_eq_false_iff_semanticLoopFree _).mp reconciled_acyclic)
      reconciled_nonvariable :=
  canonicalClassCoherent_of_structurallySolved _ _ reconciled_structurally_solved

theorem independent_closed_match :
    MatchRel equalityGroundedSemantic (.symbol "B") (.var "private") fresh := by
  exact .nonVarVar rfl ((hasLoop_eq_false_iff_semanticLoopFree _).mp (by decide))

/-- Different explicit edge multiplicities preserve the whole binding theory. -/
theorem same_complete_solution_theory (valuation : String → Atom) :
    TypeBindingSatisfied valuation actual ↔
      TypeBindingSatisfied valuation (reconciled.assign "private" (.symbol "B")) := by
  have assignments : actual.assignments.Perm
      (reconciled.assign "private" (.symbol "B")).assignments := by
    change (fresh.assignments ++ reconciled.assignments).Perm
      (reconciled.assignments ++ fresh.assignments)
    exact List.perm_append_comm
  have equalities : ∀ edge, edge ∈ actual.equalities ↔
      edge ∈ (reconciled.assign "private" (.symbol "B")).equalities := by
    intro edge
    simp [actual, reconciled, Bindings.assign]
  constructor
  · intro satisfied
    exact ⟨fun key value member => satisfied.1 key value (assignments.mem_iff.mpr member),
      fun left right member => satisfied.2 left right ((equalities _).mpr member)⟩
  · intro satisfied
    exact ⟨fun key value member => satisfied.1 key value (assignments.mem_iff.mp member),
      fun left right member => satisfied.2 left right ((equalities _).mp member)⟩

set_option maxRecDepth 12000 in
/-- All selected readouts agree together, including two occurrences of one
open residual variable. This is stronger than independent per-value alpha. -/
theorem public_readouts_agree :
    let observations := .expression [Atom.var "x", .var "y", .var "z", .var "w", .var "private",
      .expression [.symbol "pair", .var "residual", .var "residual"]]
    actual.applyFull observations 50 =
      (reconciled.assign "private" (.symbol "B")).applyFull observations 50 := by decide


end AliasMergeControls

end Mettapedia.Languages.MeTTa.HE.FirstSuccessSourceExecution



namespace Mettapedia.Languages.MeTTa.HE.FirstSuccessSourceExecution
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Spec.Type.Presentation Spec.Type.Presentation.Theory Spec.Type.RuntimeRefinement
open Spec.Bindings.ScopeObservation Spec.Match.ModelTheory FreshPrivateMerge
open RecursiveTasks FirstSuccessRecursiveExecution
open Mettapedia.GSLT.Distinction.ProductiveBlocks

/-- For a closed matched frame, its complete variable support is exactly its
assigned keys. Closed values introduce no hidden names. -/
theorem ClosedBindingFrame.support_iff_keys {bindings : Bindings}
    (frame : ClosedBindingFrame bindings) (name : String) :
    name ∈ specBindingVars bindings ↔ name ∈ bindings.assignments.map Prod.fst := by
  simp only [specBindingVars, frame.noEqualities, List.flatMap_nil, List.append_nil,
    List.mem_flatMap, List.mem_map, List.mem_cons]
  constructor
  · rintro ⟨⟨key,value⟩,stored,same | occurs⟩
    · exact ⟨(key,value),stored,same.symm⟩
    · simp [frame.closed key value stored] at occurs
  · rintro ⟨⟨key,value⟩,stored,same⟩
    exact ⟨(key,value),stored,Or.inl same.symm⟩

/-- Hygienic closed-query admission retains alias-bearing runtime frames.
Transport consumes their principal invariant and constructs the next one.
The actual candidate-first checkpoint and independent candidate-first source
endpoint agree on their whole theory and freshness support; the source record
needs no canonical resolver or equality-free layout. -/
theorem EquationBodyEvidence.of_alias_closed_match
    {space : Space} {live : List Atom} {query expected : Atom} {incoming : Bindings}
    {candidate request : ResultPair} (position : Nat) (left right : Atom)
    (stored : space.atoms[position]? = some (.expression [.symbol "=", left, right]))
    (rhs : candidate.1 = (freshenEquationAvoiding
      (equationScope live query expected incoming) position left right).2)
    (closed : TypeSubst.typeVars query = [])
    (covered : ∀ key ∈ TypeSubst.typeVars right, key ∈ TypeSubst.typeVars left)
    (matchFuel mergeFuel readFuel : Nat)
    (matched : candidate.2 ∈ matchAtoms query
      (freshenEquationAvoiding (equationScope live query expected incoming) position left right).1 matchFuel)
    (merged : request.2 ∈ mergeBindings candidate.2 (aliasConstraints incoming) mergeFuel)
    (readout : request.1 = request.2.applyFull candidate.1 readFuel)
    (enough : BindingComposition.atomDepth candidate.1 + 2 ≤ readFuel) :
    EquationBodyEvidence space live query expected incoming candidate request .semantic := by
  let pattern := (freshenEquationAvoiding
    (equationScope live query expected incoming) position left right).1
  have alpha : Spec.Eval.Steps.AlphaVariantRel (expected :: live) query incoming
      left right pattern candidate.1 := by
    rw [rhs]
    exact EquationFreshening.freshenEquationAvoiding_alphaVariant
      (expected :: live) query left right incoming _ position (by
        intro name visible
        have captured := EquationFreshening.equationScope_visible (type_ := expected) visible
        simp only [equationScope, atomListVariables, List.mem_append] at captured ⊢
        tauto)
  obtain ⟨independentMatch, frame⟩ := closed_target_runtime_match_source closed matched
  have supported := closed_target_match_keys (DeclMatchSpec.matchAtoms_sound matched) closed
  have fresh : ∀ key ∈ candidate.2.assignments.map Prod.fst, key ∉ specBindingVars incoming := by
    intro key member
    obtain ⟨entry, entryMember, same⟩ := List.mem_map.mp member
    have patternMember := supported entry.1 entry.2 entryMember
    rw [same] at patternMember
    exact alphaVariant_pattern_fresh alpha key patternMember
  have bodySupported : ∀ key ∈ TypeSubst.typeVars candidate.1,
      key ∈ candidate.2.assignments.map Prod.fst := by
    intro key occurs
    apply (frame.support_iff_keys key).mp
    apply (FreshPrivateMerge.match_support_iff matched key).mpr
    exact Or.inr (alphaVariant_covered alpha covered key occurs)
  refine ⟨?_⟩
  intro independent sourceRelated
  have freshAlias : ∀ key ∈ candidate.2.assignments.map Prod.fst,
      key ∉ specBindingVars (aliasConstraints incoming) := by
    intro key owned present
    exact fresh key owned
      ((Spec.Type.Presentation.BindingTheory.aliasConstraints_support incoming key).mp present)
  obtain ⟨valuation, callerModel⟩ := sourceRelated.model
  have principal := closed_private_principal frame freshAlias
    ⟨valuation, (Spec.Type.Presentation.BindingTheory.aliasConstraints_models incoming valuation).mpr callerModel⟩
    (Spec.Type.Presentation.BindingTheory.aliasConstraints_nonvariable incoming) merged
  have selected : (request.2, QueryBindingProjection.nativeReadoutPresentation request.2) ∈
      QueryBindingProjection.AliasReadout.mergeReadouts candidate.2 incoming mergeFuel :=
    QueryBindingProjection.AliasReadout.mem_mergeReadouts.mpr
      ⟨merged, (Spec.Match.Merge.hasLoop_eq_false_iff_semanticLoopFree _).mpr principal.loopFree, rfl⟩
  obtain ⟨sourceMatched, sourceMatch, sourceAgreement, model, certificate, reads⟩ :=
    QueryBindingProjection.AliasReadout.mergeReadouts_source sourceRelated.related matched selected
  let sourceFrame : Spec.Eval.BindingFrame := .selected request.2 _ certificate
  have framed : SourceBindingComparison.semantic.FrameRelated request.2 sourceFrame :=
    .semantic (.refl _) certificate (fun atom depth covered => (reads atom depth covered).symm)
  refine ⟨sourceFrame, framed, ⟨position, left, right, sourceMatched, rhs, ?_⟩, ?_⟩
  · refine ⟨stored, ⟨(sourceRelated.related.alphaVariant_iff _ _ _ _ _ _).mp alpha, sourceMatch⟩,
      ⟨sourceAgreement, model⟩, ?_⟩
    intro observer satisfied
    rfl
  · apply framed.materialization_of_forced
    rw [readout]
    exact closed_private_readout_forced frame (.refl _) freshAlias merged
      candidate.1 bodySupported enough

/-- Actual scoped query/input occurrences construct the alias-aware local
source evidence. The retained selected certificate supplies its finite model;
no output comparison, source coherence or whole evaluation theorem is assumed. -/
theorem EquationBodyEvidence.of_alias_closed_query_hit
    {space : Space} {live : List Atom} {query expected : Atom} {incoming : Bindings}
    {candidate request : ResultPair} {fuel : Nat}
    (closed : TypeSubst.typeVars query = [])
    (covered : ∀ (position : Nat) (left right : Atom),
      space.atoms[position]? = some (.expression [.symbol "=", left, right]) →
      ∀ key ∈ TypeSubst.typeVars right, key ∈ TypeSubst.typeVars left)
    (hit : candidate ∈ equationCandidates space live query expected incoming fuel)
    (input : request ∈ equationInputs incoming fuel candidate)
    (enough : BindingComposition.atomDepth candidate.1 + 2 ≤ fuel) :
    EquationBodyEvidence space live query expected incoming candidate request .semantic := by
  obtain ⟨left, right, position, stored, rhs, matched, _⟩ :=
    queryEquationsAvoiding_matchAtoms_witness hit
  rw [List.mem_zipIdx_iff_getElem?] at stored
  obtain ⟨merged, mergeMember, selected⟩ := List.mem_filterMap.mp input
  split at selected
  · simp at selected
  · have pair : (merged.applyFull candidate.1 fuel, merged) = request := Option.some.inj selected
    cases pair
    exact EquationBodyEvidence.of_alias_closed_match position left right stored rhs closed
      (covered position left right stored) fuel fuel fuel matched mergeMember rfl enough

/-- The same recursive derivation constructs checked completion and source
meaning under either declared binding observer. Its source input is explicit. -/
theorem AtomDerivation.checked_completion_and_related_source
    {space : Space} {comparison : SourceBindingComparison} {live : List Atom}
    {value expected : Atom} {incoming : Bindings} {fuel : Nat} {results : ResultSet}
    (derivation : AtomDerivation (comparison := comparison) space live value expected incoming fuel results)
    (covered : derivation.Covered) (earned : ResultSet)
    (independent : Spec.Eval.BindingFrame)
    (related : comparison.FrameRelated incoming independent) :
    (∃ budget, ∀ later, (Checked.machine HE.GroundedDispatch.none).run (budget + later)
      ⟨space, .work (.atom value expected incoming fuel live), [], earned⟩ =
      (results, .finished ⟨space, .returning [], [], earned ++ results⟩)) ∧
    ∀ result ∈ results, ∃ output,
      Spec.Eval.EvalAtomRawRel space noHost live value expected independent (result.1,output) ∧
      comparison.FrameRelated result.2 output := by
  refine ⟨derivation.checked_completed covered earned,?_⟩
  intro result member
  exact derivation.sound result member [] independent related

end Mettapedia.Languages.MeTTa.HE.FirstSuccessSourceExecution

namespace Mettapedia.Languages.MeTTa.HE.FirstSuccessSourceExecution
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Spec.Type.Presentation Spec.Type.RuntimeRefinement
open Spec.Type.Presentation.BindingTheory

/-- Every returned occurrence preserves the chosen source constraint theory.
The independent observer materializes all requested observations together, so
one residual renaming preserves aliases and repeated uses across the tuple. -/
theorem AtomDerivation.semantic_source_observer
    {space : Space} {live : List Atom} {value expected : Atom}
    {incoming : Bindings} {fuel : Nat} {results : ResultSet}
    (derivation : AtomDerivation (comparison := .semantic) space live value expected incoming fuel results)
    (input : Spec.Eval.BindingFrame)
    (initial : SourceBindingComparison.semantic.FrameRelated incoming input)
    (result : ResultPair) (member : result ∈ results) (observations : List Atom) :
    ∃ independentOutput normalized,
      Spec.Eval.EvalAtomRawRel space noHost live value expected input
        (result.1, independentOutput) ∧
      BindingSourceAgreement result.2 independentOutput ∧
      BindingMaterializationRel independentOutput (.expression (result.1 :: observations)) normalized ∧
      ∃ permutation : Equiv.Perm String,
        normalized = renameTypeVars permutation
          (result.2.applyFull (.expression (result.1 :: observations))
            (result.2.resolutionFuel (.expression (result.1 :: observations)))) := by
  obtain ⟨output, evaluated, related⟩ := derivation.sound result member [] input initial
  obtain ⟨normalized, permutation, materialized, readout⟩ :=
    related.joint_observation (result.1 :: observations)
      (result.2.resolutionFuel (.expression (result.1 :: observations)))
      (Bindings.applyFullCovered_resolutionFuel _ _)
  exact ⟨output, normalized, evaluated, related.related, materialized, permutation, readout⟩

end Mettapedia.Languages.MeTTa.HE.FirstSuccessSourceExecution

/-! ## Recursive alias-bearing checkpoints and independent observations -/

namespace Mettapedia.Languages.MeTTa.HE.FirstSuccessSourceExecution
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open RecursiveTasks FirstSuccessRecursiveExecution FirstSuccessSourceApplicability FirstSuccessLeafEvaluation
open Spec.Type Spec.Type.Presentation Spec.Type.RuntimeRefinement
open Spec.Bindings.ScopeObservation
set_option maxRecDepth 12000
set_option maxHeartbeats 4000000
namespace AliasRecursiveControls
abbrev initial := AliasMergeControls.reconciled
abbrev outerCandidate : ResultPair := (.var "x#1",Bindings.empty.assign "x#1" equationQuery)
def outerBindings : Bindings :=
  ⟨[("x#1",equationQuery)]++initial.assignments,[("x","y"),("z","w"),("z","w")]⟩
abbrev innerCandidate : ResultPair := (.var "x#2",Bindings.empty.assign "x#2" (.symbol "answer"))
def finalBindings : Bindings :=
  ⟨[("x#2",.symbol "answer")]++outerBindings.assignments,[("x","y"),("z","w"),("z","w"),("z","w")]⟩
def results : ResultSet := [(.symbol "answer",finalBindings)]

theorem initial_principal : PrincipalBindingFrame initial :=
  ⟨(Spec.Match.Merge.hasLoop_eq_false_iff_semanticLoopFree _).mp AliasMergeControls.reconciled_acyclic,
    AliasMergeControls.reconciled_nonvariable,AliasMergeControls.reconciled_source_coherent⟩

private theorem bodyCoverage (position : Nat) (left right : Atom)
    (stored : recursiveSpace.atoms[position]? = some (.expression [.symbol "=",left,right])) :
    ∀ key ∈ TypeSubst.typeVars right,key ∈ TypeSubst.typeVars left := by
  have present := List.mem_of_getElem? stored
  simp only [recursiveSpace,Space.ofList,List.mem_cons,List.not_mem_nil,or_false] at present
  rcases present with first | second
  · simp only [identityEquation,Atom.expression.injEq,List.cons.injEq,true_and,and_true] at first
    obtain ⟨rfl,rfl⟩ := first
    intro key occurs
    simpa [TypeSubst.typeVars,TypeSubst.typeVarsList] using occurs
  · simp at second

theorem outer_candidates :
    equationCandidates recursiveSpace captureLive recursiveQuery Atom.symbolType initial
      (controlFuel+8) = [outerCandidate] := by decide +kernel

theorem outer_inputs : equationInputs initial (controlFuel+8) outerCandidate =
    [(equationQuery,outerBindings)] := by decide +kernel

theorem inner_candidates :
    equationCandidates recursiveSpace captureLive equationQuery Atom.symbolType outerBindings
      (controlFuel+5) = [innerCandidate] := by decide +kernel

theorem inner_inputs : equationInputs outerBindings (controlFuel+5) innerCandidate =
    [(.symbol "answer",finalBindings)] := by decide +kernel

private theorem outerEvidence :
    EquationBodyEvidence recursiveSpace captureLive recursiveQuery Atom.symbolType initial
      outerCandidate (equationQuery,outerBindings) .semantic := by
  apply EquationBodyEvidence.of_alias_closed_query_hit (fuel:=controlFuel+8)
    (by rfl) bodyCoverage
  · rw [outer_candidates]; simp
  · rw [outer_inputs]; simp
  · decide

private theorem innerEvidence :
    EquationBodyEvidence recursiveSpace captureLive equationQuery Atom.symbolType outerBindings
      innerCandidate (.symbol "answer",finalBindings) .semantic := by
  apply EquationBodyEvidence.of_alias_closed_query_hit (fuel:=controlFuel+5)
    (by rfl) bodyCoverage
  · rw [inner_candidates]; simp
  · rw [inner_inputs]; simp
  · decide

private theorem innerSource :
    AtomDerivation (comparison:=.semantic) recursiveSpace captureLive equationQuery Atom.symbolType
      outerBindings (controlFuel+8) results := by
  apply unary_raw_application_derivation captureLive (.symbol "answer") outerBindings
    (controlFuel+5) (recursiveTyping _ _ (by omega)) rfl rfl (by decide) results
  · apply single_equation_call_derivation recursiveSpace "identity" (by decide) (by decide) (by decide)
      captureLive (.symbol "answer") outerBindings (controlFuel+5)
      innerCandidate (.symbol "answer",finalBindings) results inner_candidates inner_inputs innerEvidence
    exact .leaf captureLive (.symbol "answer") Atom.symbolType finalBindings (controlFuel+4)
      (Or.inr ⟨Atom.symbolType,.symbol "answer",Or.inr (Or.inl rfl)⟩)
  · rfl

/-- Two nested calls reconcile the same alias-bearing caller at both actual
checkpoints. The source derivation retains those records rather than silently
replacing them by a normal or equality-free environment. -/
theorem source :
    AtomDerivation (comparison:=.semantic) recursiveSpace captureLive recursiveQuery Atom.symbolType
      initial (controlFuel+11) results := by
  apply unary_raw_application_derivation captureLive equationQuery initial
    (controlFuel+8) (recursiveTyping _ _ (by omega)) rfl rfl (by decide) results
  · exact single_equation_call_derivation recursiveSpace "identity" (by decide) (by decide) (by decide)
      captureLive equationQuery initial (controlFuel+8) outerCandidate (equationQuery,outerBindings)
      results outer_candidates outer_inputs outerEvidence innerSource
  · rfl

private theorem innerCovered : innerSource.Covered := by
  have body := AtomDerivation.leaf (comparison:=.semantic) (space:=recursiveSpace)
    captureLive (.symbol "answer") Atom.symbolType finalBindings (controlFuel+4)
    (Or.inr ⟨Atom.symbolType,.symbol "answer",Or.inr (Or.inl rfl)⟩)
  have call := single_equation_call_derivation recursiveSpace "identity" (by decide) (by decide) (by decide)
    captureLive (.symbol "answer") outerBindings (controlFuel+5) innerCandidate
    (.symbol "answer",finalBindings) results inner_candidates inner_inputs innerEvidence body
  have callCovered : call.Covered := by
    apply single_equation_call_covered recursiveSpace "identity" (by decide) (by decide) (by decide)
      captureLive (.symbol "answer") outerBindings (controlFuel+5) innerCandidate
      (.symbol "answer",finalBindings) results inner_candidates inner_inputs innerEvidence body
      (by decide +kernel)
    · decide +kernel
    · decide +kernel
    · intro merged member safe
      have only : mergeBindings innerCandidate.2 (aliasConstraints outerBindings) (controlFuel+5) = [finalBindings] := by decide +kernel
      rw [only] at member
      obtain rfl := List.mem_singleton.mp member
      decide +kernel
    · exact AtomDerivation.Covered.leaf
        (leaf := Or.inr ⟨Atom.symbolType,.symbol "answer",Or.inr (Or.inl rfl)⟩)
  exact unary_raw_application_covered captureLive (.symbol "answer") outerBindings
    (controlFuel+5) (recursiveTyping _ _ (by omega)) rfl rfl (by decide) results
    call rfl (by decide +kernel) (by decide +kernel) callCovered

/-- All local matching/readout bounds are checked on the actual changed
records; this proves finite completion without assuming any whole-run answer. -/
theorem covered : source.Covered := by
  have call := single_equation_call_derivation recursiveSpace "identity" (by decide) (by decide) (by decide)
    captureLive equationQuery initial (controlFuel+8) outerCandidate (equationQuery,outerBindings)
    results outer_candidates outer_inputs outerEvidence innerSource
  have callCovered : call.Covered := by
    apply single_equation_call_covered recursiveSpace "identity" (by decide) (by decide) (by decide)
      captureLive equationQuery initial (controlFuel+8) outerCandidate (equationQuery,outerBindings)
      results outer_candidates outer_inputs outerEvidence innerSource (by decide +kernel)
    · decide +kernel
    · decide +kernel
    · intro merged member safe
      have only : mergeBindings outerCandidate.2 (aliasConstraints initial) (controlFuel+8) = [outerBindings] := by decide +kernel
      rw [only] at member
      obtain rfl := List.mem_singleton.mp member
      decide +kernel
    · exact innerCovered
  exact unary_raw_application_covered captureLive equationQuery initial
    (controlFuel+8) (recursiveTyping _ _ (by omega)) rfl rfl (by decide) results
    call rfl (by decide +kernel) (by decide +kernel) callCovered

/-- The complete saved-worker bound is constructed from the recursive source
and its local coverage. It includes both alias-changing calls. -/
theorem source_earns_completion (earned : ResultSet) :
    ∃ budget, ∀ later, (Checked.machine HE.GroundedDispatch.none).run (budget+later)
      ⟨recursiveSpace,.work (.atom recursiveQuery Atom.symbolType initial
        (controlFuel+11) captureLive),[],earned⟩ =
      (results,.finished ⟨recursiveSpace,.returning [],[],earned++results⟩) :=
  source.checked_completed covered earned

/-- A concrete resource-aware run agrees with the constructed source result. -/
theorem checked_run :
    (Checked.machine HE.GroundedDispatch.none).run 1000
      ⟨recursiveSpace,.work (.atom recursiveQuery Atom.symbolType initial
        (controlFuel+11) captureLive),[],[]⟩ =
      (results,.finished ⟨recursiveSpace,.returning [],[],results⟩) := by rfl

/-- Reconciliation preserves constraints while retaining repeated equality
occurrences in the worker record. Equality-list permutation would reject it. -/
theorem checkpoint_is_not_caller_layout :
    ¬BindingRecordPerm finalBindings
      ⟨initial.assignments++[("x#1",equationQuery),("x#2",.symbol "answer")],initial.equalities⟩ := by
  intro related
  have lengths := related.equalities.length_eq
  norm_num [finalBindings,initial,AliasMergeControls.reconciled] at lengths

/-- The pause is after the outer equation has changed its caller record and
before its recursive body runs. The complete surrounding stack is retained. -/
theorem retained_outer_checkpoint :
    ∃ saved : Configuration,
      (Checked.machine HE.GroundedDispatch.none).run 38
        ⟨recursiveSpace,.work (.atom recursiveQuery Atom.symbolType initial
          (controlFuel+11) captureLive),[],[]⟩ = ([],.exhausted saved) ∧
      saved.control = .work (.returned recursiveQuery equationQuery Atom.symbolType outerBindings
        (controlFuel+8) captureLive) ∧ saved.stack ≠ [] ∧
      (Checked.machine HE.GroundedDispatch.none).run 1000 saved =
        (results,.finished ⟨recursiveSpace,.returning [],[],results⟩) := by
  exact ⟨_,rfl,rfl,by decide,rfl⟩

/-- Insufficient evaluation depth is retained as a resource request. The
absence of emitted answers is not evidence of a completed empty computation. -/
theorem shallow_is_pending :
    (Checked.machine HE.GroundedDispatch.none).run 1
      ⟨recursiveSpace,.work (.atom recursiveQuery Atom.symbolType initial 0 captureLive),[],[]⟩ =
      ([],.suspended .evaluationDepth
        ⟨recursiveSpace,.work (.atom recursiveQuery Atom.symbolType initial 0 captureLive),[],[]⟩) := rfl

/-- The existing service carries the complete reconciled record and reply;
no alternate caller protocol or normalized checkpoint is introduced. -/
theorem checked_service (endpoint : Atom) (charge : Nat) :
    (checkedEvaluationService endpoint charge).run 1000
      ⟨recursiveSpace,.work (.atom recursiveQuery Atom.symbolType initial
        (controlFuel+11) captureLive),[],[]⟩ =
      (results.map sourceEvent,.finished (.returned
        (NativeArgumentControlEncoding.replyData ⟨endpoint,.evaluated results,charge⟩))) :=
  source.checked_service_completed results 1000 _ checked_run endpoint charge

/-- The source judgment and joint residual observer follow from the same
recursive source proof that constructs the actual checked run. -/
theorem independent_meaning_and_joint_observation (observations : List Atom) :
    ∃ independent normalized,
      Spec.Eval.EvalAtomRawRel recursiveSpace noHost captureLive recursiveQuery Atom.symbolType
        initial_principal.sourceFrame (.symbol "answer",independent) ∧
      BindingSourceAgreement finalBindings independent ∧
      Spec.Type.Presentation.BindingTheory.BindingMaterializationRel independent
        (.expression (.symbol "answer" :: observations)) normalized ∧
      ∃ permutation : Equiv.Perm String,
        normalized = renameTypeVars permutation
          (finalBindings.applyFull (.expression (.symbol "answer" :: observations))
            (finalBindings.resolutionFuel (.expression (.symbol "answer" :: observations)))) := by
  obtain ⟨independent,normalized,evaluated,agreement,materialized,permutation,readout⟩ :=
    source.semantic_source_observer initial_principal.sourceFrame
      (.of_principal initial_principal (.refl _)) (.symbol "answer",finalBindings)
      (by simp [results]) observations
  exact ⟨independent,normalized,evaluated,agreement,materialized,permutation,readout⟩

end AliasRecursiveControls
end Mettapedia.Languages.MeTTa.HE.FirstSuccessSourceExecution


namespace Mettapedia.Languages.MeTTa.HE.FirstSuccessSourceExecution.DuplicateSeedControl
open Spec.Match.Merge Spec.Bindings.ScopeObservation

private def duplicate : Bindings := ⟨[("x",.symbol "A"),("x",.symbol "A")],[]⟩
private def single : Bindings := ⟨[("x",.symbol "A")],[]⟩

/-- Replaying a raw duplicated caller from the empty selected match removes
its repeated logical constraint. Literal relation multiplicity is not a source
merge invariant. -/
theorem selected_empty_replay {out : Bindings}
    (derived : MergeRel equalityGroundedSemantic Bindings.empty duplicate out) : out=single := by
  cases derived with
  | @mk _ _ _ order listed folded =>
    have orderEq : order=[.value "x" (.symbol "A")] := by
      have exactly : constraints duplicate=[.value "x" (.symbol "A")] := by decide +kernel
      rw [exactly] at listed
      exact List.perm_singleton.mp listed
    subst order
    cases folded with
    | value added tail =>
      cases tail
      cases added with
      | fresh => rfl
      | same values _ _ | conflict values _ _ _ _ | reconcile values _ _ _ =>
        have emptyValues : Bindings.empty.classValues "x"=[] := rfl
        rw [emptyValues] at values
        have impossible := values.length_eq
        simp at impossible

theorem duplicate_admitted : SemanticLoopFree duplicate ∧
    ∃ valuation,Spec.Match.SolutionTheory.HEBindingSatisfied valuation duplicate := by
  constructor
  · exact (hasLoop_eq_false_iff_semanticLoopFree _).mp (by decide +kernel)
  · exact ⟨fun _=>.sym "A",by simp [Spec.Match.SolutionTheory.HEBindingSatisfied,duplicate,
      Spec.Match.SolutionTheory.applyClassSolution,Spec.Match.SolutionTheory.encodeModelAtom]⟩

theorem selected_empty_constructed :
    MergeRel equalityGroundedSemantic Bindings.empty duplicate single := by
  refine .mk (order:=[.value "x" (.symbol "A")]) ?_ (.value (.fresh rfl) .nil)
  decide +kernel

/-- The old unrestricted empty-match permutation interface is false even
for a satisfiable, acyclic caller with only closed assignments. -/
theorem selected_empty_replay_not_recordPerm {out : Bindings}
    (derived : MergeRel equalityGroundedSemantic Bindings.empty duplicate out) :
    ¬BindingRecordPerm duplicate out := by
  rw [selected_empty_replay derived]
  intro related
  have impossible:=related.assignments.length_eq
  simp [duplicate,single] at impossible

end Mettapedia.Languages.MeTTa.HE.FirstSuccessSourceExecution.DuplicateSeedControl


namespace Mettapedia.Languages.MeTTa.HE.FirstSuccessSourceExecution
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Spec.Type.Presentation Spec.Type.Presentation.Theory Spec.Type.RuntimeRefinement Spec.Bindings.ScopeObservation
open Spec.Type.Presentation.BindingTheory
open Spec.Match.Merge Spec.Match.ModelTheory
open QueryBindingProjection

/-- Every surviving open-query work item of the maintained Lean binding machine
has an independent source occurrence
at the same physical position and one executable finite presentation of its
entire actual binding record. The presentation preserves the complete source
theory and every covered future operand; it is not chosen for one RHS.

The certificate does not assert that the historical source fold selects this
representation, or that unchanged name-inspecting services ignore its spelling.
Rust query narrowing and actual C materialization require separate adapters. -/
theorem equationInput_open_source_at
    {space : Space} {live : List Atom} {query expected : Atom} {incoming independent : Bindings}
    {candidate request : ResultPair} {fuel : Nat}
    (related : BindingSourceAgreement incoming independent)
    (position : Nat) (left right : Atom)
    (stored : space.atoms[position]? = some (.expression [.symbol "=", left, right]))
    (rhs : candidate.1 = (freshenEquationAvoiding
      (equationScope live query expected incoming) position left right).2)
    (matching : candidate.2 ∈ matchAtoms query (freshenEquationAvoiding
      (equationScope live query expected incoming) position left right).1 fuel)
    (input : request ∈ equationInputs incoming fuel candidate)
    (readCovered : request.2.applyFullCovered candidate.1 fuel = true) :
    ∃ (matched merged : Bindings),
      Spec.Eval.Steps.EquationQueryOccurrenceRel space (expected :: live) query independent
        position left right
        (freshenEquationAvoiding (equationScope live query expected incoming) position left right).1
        candidate.1 matched candidate.1 merged ∧
      BindingSourceAgreement request.2 merged ∧ PrincipalBindingFrame request.2 ∧
      AssignmentsNonVariable merged ∧
      (nativeReadoutPresentation request.2).Normal ∧
      (∀ valuation, TypeSubstSatisfied valuation (nativeReadoutPresentation request.2) ↔
        TypeBindingSatisfied valuation merged) ∧
      (nativeReadoutPresentation request.2).apply candidate.1 = request.1 ∧
      (∀ atom depth, request.2.applyFullCovered atom depth = true →
        (nativeReadoutPresentation request.2).apply atom = request.2.applyFull atom depth) := by
  obtain ⟨out, mergeMember, selected⟩ := List.mem_filterMap.mp input
  split at selected
  · simp at selected
  · rename_i admitted
    have admitted : out.hasLoop = false := by simpa using admitted
    have pair : (out.applyFull candidate.1 fuel, out) = request := Option.some.inj selected
    cases pair
    let pattern := (freshenEquationAvoiding
      (equationScope live query expected incoming) position left right).1
    have alpha : Spec.Eval.Steps.AlphaVariantRel (expected :: live) query incoming
        left right pattern candidate.1 := by
      rw [rhs]
      exact EquationFreshening.freshenEquationAvoiding_alphaVariant
        (expected :: live) query left right incoming _ position (by
          intro name visible
          have captured := EquationFreshening.equationScope_visible (type_ := expected) visible
          simp only [equationScope, atomListVariables, List.mem_append] at captured ⊢
          tauto)
    have selected : (out, nativeReadoutPresentation out) ∈
        AliasReadout.mergeReadouts candidate.2 incoming fuel :=
      AliasReadout.mem_mergeReadouts.mpr ⟨mergeMember, admitted, rfl⟩
    obtain ⟨sourceMatched, sourceMatch, agreement, model, certificate, readout⟩ :=
      AliasReadout.mergeReadouts_source related matching selected
    have shape := mergeBindings_assignmentsNonVariable_model mergeMember
      (matchAtoms_assignmentsNonVariable_model matching) (aliasConstraints_nonvariable incoming)
    have loopFree := (hasLoop_eq_false_iff_semanticLoopFree out).mp admitted
    have coherent := declMerge_canonicalClassCoherent_of_match (DeclMatchSpec.matchAtoms_sound matching)
      (DeclMergeSpec.mergeBindings_sound mergeMember) loopFree shape
    refine ⟨sourceMatched, out, ?_, .refl _,
      ⟨loopFree, shape, coherent⟩, shape, certificate.normal, certificate.theory,
      readout candidate.1 fuel readCovered, readout⟩
    refine ⟨stored, ⟨(related.alphaVariant_iff _ _ _ _ _ _).mp alpha, sourceMatch⟩,
      ⟨agreement, model⟩, ?_⟩
    intro _ _
    rfl

/-- A viable independent source occurrence cannot disappear from a fully
covered query and caller reconciliation. Its private names are first
transported to the actual retained fresh instance. No restriction on incoming
aliases or closedness of the query is imposed. This concerns raw RHS work. -/
theorem source_occurrence_reaches_covered_query
    {space : Space} {live : List Atom} {query expected left right pattern body emitted : Atom}
    {incoming matched independent : Bindings} {position fuel : Nat}
    (source : Spec.Eval.Steps.EquationQueryOccurrenceRel space (expected :: live) query incoming
      position left right pattern body matched emitted independent)
    (queryCovered : queryEquationsCovered (equationScope live query expected incoming)
      space query fuel = true)
    (inputsCovered : ∀ candidate ∈ equationCandidates space live query expected incoming fuel,
      matchCovered fuel (.merge candidate.2 (aliasConstraints incoming)) = true) :
    ∃ request, request ∈ rawQueryResults space query expected incoming fuel live := by
  let avoid := equationScope live query expected incoming
  let chosen := freshenEquationAvoiding avoid position left right
  have variant : Spec.Eval.Steps.AlphaVariantRel (expected :: live) query incoming
      left right chosen.1 chosen.2 := by
    apply EquationFreshening.freshenEquationAvoiding_alphaVariant
    intro name visible
    have captured := EquationFreshening.equationScope_visible (type_ := expected) visible
    simp only [avoid,equationScope,atomListVariables,List.mem_append] at captured ⊢
    tauto
  obtain ⟨_,_,_,_,_,_,selected,_,_⟩ :=
    EquationFreshening.occurrence_alpha_transport_logical source variant
  obtain ⟨valuation,sourceModel,callerModel⟩ := selected.result.1.common_model
  let observer : String → Metta.Atom := fun name => Spec.Match.SolutionTheory.encodeModelAtom (valuation name)
  have equation : Spec.Match.SolutionTheory.HEAtomEquationSatisfied observer query chosen.1 :=
    (Spec.Match.SolutionTheory.matchRel_solution_iff selected.selected.2 observer).mp
      (Spec.Bindings.ScopeObservation.ModelTransport.heBindingSatisfied_of_specTypeBindingSatisfied sourceModel)
  obtain ⟨actual,witnessDepth,matching⟩ :=
    MatchSizeTheory.exists_matchAtoms_of_solution_solutionSize equation
  have actualModel := (BindingComposition.matchAtoms_solution_iff matching observer).mpr equation
  have actualShape := matchAtoms_assignmentsNonVariable_model matching
  have actualAcyclic : actual.hasLoop = false :=
    (hasLoop_eq_false_iff_semanticLoopFree actual).mpr
      (semanticLoopFree_of_satisfied_nonvariable actualModel actualShape)
  have foundLarge : (chosen.2,actual) ∈
      queryEquationsAvoiding avoid space query (fuel + (witnessDepth + 1)) := by
    simp only [Nat.add_succ,queryEquationsAvoiding]
    apply List.mem_flatMap.mpr
    refine ⟨(.expression [.symbol "=",left,right],position),
      List.mem_zipIdx_iff_getElem?.mpr source.stored,?_⟩
    dsimp only
    apply List.mem_flatMap.mpr
    refine ⟨actual,?_,?_⟩
    · simpa only [chosen,Nat.succ_eq_add_one,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using
        DeclMatchSpec.matchAtoms_mono query chosen.1 witnessDepth (fuel + 1) matching
    · simp [chosen,mergeBindings,Bindings.empty,actualAcyclic]
  have found : (chosen.2,actual) ∈ equationCandidates space live query expected incoming fuel := by
    change (chosen.2,actual) ∈ queryEquationsAvoiding avoid space query fuel
    rw [← queryEquationsCovered_stable avoid space query fuel (witnessDepth + 1) queryCovered]
    exact foundLarge
  have callerModel' : Spec.Match.SolutionTheory.HEBindingSatisfied observer (aliasConstraints incoming) :=
    Spec.Bindings.ScopeObservation.ModelTransport.heBindingSatisfied_of_specTypeBindingSatisfied
      ((aliasConstraints_models incoming valuation).mpr callerModel)
  have callerShape : Spec.Match.SolutionTheory.HEAssignmentsNonVariable (aliasConstraints incoming) := by
    intro key name present
    have impossible := aliasConstraints_nonvariable incoming key (.var name) present
    simp [isVariableB] at impossible
  obtain ⟨output,mergeDepth,occurred⟩ := MatchSizeTheory.exists_mergeBindings_of_common_model
    actualModel (MatchSizeTheory.heAssignmentsNonVariable_of_matchAtoms matching) callerModel' callerShape
  have later := DeclMatchSpec.mergeBindings_mono actual (aliasConstraints incoming) mergeDepth fuel occurred
  have stable := matchCovered_stable fuel mergeDepth (.merge actual (aliasConstraints incoming))
    (inputsCovered _ found)
  change mergeBindings actual (aliasConstraints incoming) (fuel + mergeDepth) =
    mergeBindings actual (aliasConstraints incoming) fuel at stable
  rw [Nat.add_comm mergeDepth fuel,stable] at later
  have acyclic : output.hasLoop = false :=
    (hasLoop_eq_false_iff_semanticLoopFree output).mpr
      (mergeBindings_semanticLoopFree_of_common_model later actualShape
        (aliasConstraints_nonvariable incoming) actualModel callerModel')
  change ∃ request, request ∈ (equationCandidates space live query expected incoming fuel).flatMap
    (equationInputs incoming fuel)
  refine ⟨(output.applyFull chosen.2 fuel,output),List.mem_flatMap.mpr ⟨(chosen.2,actual),found,?_⟩⟩
  exact List.mem_filterMap.mpr ⟨output,later,by simp [acyclic]⟩

/-- Completed query emptiness is exactly an independently covered empty
physical source frontier. Local coverage includes the actual reached merge
and readout operations; it is not a whole-evaluator correctness premise. -/
theorem covered_query_empty_iff_source_frontier
    {space : Space} {live : List Atom} {query expected : Atom} {incoming : Bindings} {fuel : Nat}
    (queryCovered : queryEquationsCovered (equationScope live query expected incoming)
      space query fuel = true)
    (inputsCovered : ∀ candidate ∈ equationCandidates space live query expected incoming fuel,
      matchCovered fuel (.merge candidate.2 (aliasConstraints incoming)) = true ∧
      ∀ merged ∈ mergeBindings candidate.2 (aliasConstraints incoming) fuel, merged.hasLoop = false →
        merged.applyFullCovered candidate.1 fuel = true) :
    rawQueryResults space query expected incoming fuel live = [] ↔
      Spec.Eval.Steps.EquationFrontierRel space (expected :: live) query incoming [] := by
  constructor
  · intro empty
    obtain ⟨works,completed⟩ := EquationFreshening.equationFrontier_exists space (expected :: live) query incoming
    have absent : ∀ emitted output,
        ¬Spec.Eval.Steps.EquationQueryCandidateRel space (expected :: live) query incoming emitted output := by
      intro emitted output candidate
      obtain ⟨position,left,right,pattern,body,matched,source⟩ :=
        (Spec.Eval.Steps.equationQueryCandidateRel_iff_occurrence _ _ _ _ _ _).mp candidate
      obtain ⟨request,present⟩ := source_occurrence_reaches_covered_query source queryCovered
        (fun item member => (inputsCovered item member).1)
      rw [empty] at present
      exact List.not_mem_nil present
    have none := completed.empty_iff_no_candidate.mpr absent
    simpa only [none] using completed
  · intro completed
    have absent := completed.empty_iff_no_candidate.mp rfl
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro request present
    change request ∈ (equationCandidates space live query expected incoming fuel).flatMap
      (equationInputs incoming fuel) at present
    obtain ⟨candidate,selected,input⟩ := List.mem_flatMap.mp present
    obtain ⟨merged,mergeMember,result⟩ := List.mem_filterMap.mp input
    split at result
    · simp at result
    · rename_i admitted
      have acyclic : merged.hasLoop = false := by simpa using admitted
      have pair : (merged.applyFull candidate.1 fuel,merged) = request := Option.some.inj result
      cases pair
      obtain ⟨left,right,position,stored,rhs,matching,_⟩ := queryEquationsAvoiding_matchAtoms_witness selected
      rw [List.mem_zipIdx_iff_getElem?] at stored
      obtain ⟨_,_,source,_⟩ := equationInput_open_source_at (.refl incoming)
        position left right stored rhs matching input
        ((inputsCovered candidate selected).2 merged mergeMember acyclic)
      exact absent _ _ source.candidate

/-- An actual open-query work item constructs the retained source frame.
Freshening, matching, reconciliation, principality and the one finite table
are all earned from this physical rule occurrence. -/
theorem EquationBodyEvidence.of_open_query_at
    {space : Space} {live : List Atom} {query expected : Atom} {incoming : Bindings}
    {candidate request : ResultPair} {fuel : Nat}
    (position : Nat) (left right : Atom)
    (stored : space.atoms[position]? = some (.expression [.symbol "=", left, right]))
    (rhs : candidate.1 = (freshenEquationAvoiding
      (equationScope live query expected incoming) position left right).2)
    (matching : candidate.2 ∈ matchAtoms query (freshenEquationAvoiding
      (equationScope live query expected incoming) position left right).1 fuel)
    (input : request ∈ equationInputs incoming fuel candidate)
    (readCovered : request.2.applyFullCovered candidate.1 fuel = true) :
    EquationBodyEvidence space live query expected incoming candidate request .semantic := by
  refine ⟨?_⟩
  intro independent framedInput
  have inputAgreement := framedInput.related
  obtain ⟨matched, merged, occurrence, agreement, principal, shape, _normal, _theory,
      observed, _future⟩ := equationInput_open_source_at inputAgreement position left right stored rhs matching input readCovered
  let frame := Spec.Eval.BindingFrame.selected merged (nativeReadoutPresentation request.2)
    (nativeReadoutPresentation_certificate principal.loopFree principal.nonvariable
      principal.coherent agreement.solutions)
  exact ⟨frame, .of_principal principal agreement,
    ⟨position, left, right, matched, rhs, occurrence⟩, observed.symm⟩

/-- Ordered worker traversal can apply the explicit-position constructor at
its retained row. Ordinary membership also yields a compatible source witness. -/
theorem EquationBodyEvidence.of_open_query_hit
    {space : Space} {live : List Atom} {query expected : Atom} {incoming : Bindings}
    {candidate request : ResultPair} {fuel : Nat}
    (hit : candidate ∈ equationCandidates space live query expected incoming fuel)
    (input : request ∈ equationInputs incoming fuel candidate)
    (readCovered : request.2.applyFullCovered candidate.1 fuel = true) :
    EquationBodyEvidence space live query expected incoming candidate request .semantic := by
  obtain ⟨left, right, position, stored, rhs, matching, _⟩ :=
    queryEquationsAvoiding_matchAtoms_witness hit
  rw [List.mem_zipIdx_iff_getElem?] at stored
  exact .of_open_query_at position left right stored rhs matching input readCovered

/-- The selected table is supported by one genuine independent equation fold
and one model-fixed residual choice. The same choice applies to every future
operand; this statement does not insert a new source evaluation rule. -/
theorem equationInput_open_source_presentation_choice
    {space : Space} {live : List Atom} {query expected : Atom} {incoming independent : Bindings}
    {candidate request : ResultPair} {fuel : Nat}
    (related : BindingSourceAgreement incoming independent)
    (position : Nat) (left right : Atom)
    (stored : space.atoms[position]? = some (.expression [.symbol "=", left, right]))
    (rhs : candidate.1 = (freshenEquationAvoiding
      (equationScope live query expected incoming) position left right).2)
    (matching : candidate.2 ∈ matchAtoms query (freshenEquationAvoiding
      (equationScope live query expected incoming) position left right).1 fuel)
    (input : request ∈ equationInputs incoming fuel candidate)
    (readCovered : request.2.applyFullCovered candidate.1 fuel = true) :
    ∃ (matched merged : Bindings) (folded : TypeSubst) (choice : Equiv.Perm String),
      Spec.Eval.Steps.EquationQueryOccurrenceRel space (expected :: live) query independent
        position left right
        (freshenEquationAvoiding (equationScope live query expected incoming) position left right).1
        candidate.1 matched candidate.1 merged ∧
      BindingSourceAgreement request.2 merged ∧ PrincipalBindingFrame request.2 ∧
      EquationListPresentationRel (bindingAtomEquations merged) [] folded ∧
      (∀ valuation, TypeBindingSatisfied valuation merged →
        ∀ name, valuation (choice name) = valuation name) ∧
      (∀ name, name ∉ specBindingVars merged → choice name = name) ∧
      (∀ atom, (nativeReadoutPresentation request.2).apply atom =
        (folded.renameVars choice).apply atom) ∧
      (folded.renameVars choice).apply candidate.1 = request.1 := by
  obtain ⟨matched, merged, occurrence, agreement, principal, _shape, _normal, _theory,
      observed, _future⟩ := equationInput_open_source_at related
        position left right stored rhs matching input readCovered
  obtain ⟨folded, choice, fold, _normal, _theory, reads, fixed, outside⟩ :=
    exists_uniform_exact_native_presentation principal.loopFree principal.nonvariable
      principal.coherent agreement.solutions
  have allAtoms (atom : Atom) : (nativeReadoutPresentation request.2).apply atom =
      (folded.renameVars choice).apply atom := by
    have covered := request.2.applyFullCovered_resolutionFuel atom
    exact (nativeReadoutPresentation_apply principal.loopFree principal.nonvariable
      principal.coherent atom _ covered).trans (reads atom _ covered).symm
  exact ⟨matched, merged, folded, choice, occurrence, agreement, principal, fold,
    fixed, outside, allAtoms, (allAtoms candidate.1).symm.trans observed⟩

/-- Membership yields a compatible physical source witness. Equal-valued
hits can come from distinct rows, so this corollary does not identify the
runtime slot of a duplicate. Ordered traversal proofs use the explicit-position
endpoint above. -/
theorem equationInput_open_source_occurrence
    {space : Space} {live : List Atom} {query expected : Atom} {incoming independent : Bindings}
    {candidate request : ResultPair} {fuel : Nat}
    (related : BindingSourceAgreement incoming independent)
    (hit : candidate ∈ equationCandidates space live query expected incoming fuel)
    (input : request ∈ equationInputs incoming fuel candidate)
    (readCovered : request.2.applyFullCovered candidate.1 fuel = true) :
    ∃ (position : Nat) (left right : Atom) (matched merged : Bindings),
      Spec.Eval.Steps.EquationQueryOccurrenceRel space (expected :: live) query independent
        position left right
        (freshenEquationAvoiding (equationScope live query expected incoming) position left right).1
        candidate.1 matched candidate.1 merged ∧
      BindingSourceAgreement request.2 merged ∧ PrincipalBindingFrame request.2 ∧
      AssignmentsNonVariable merged ∧
      (nativeReadoutPresentation request.2).Normal ∧
      (∀ valuation, TypeSubstSatisfied valuation (nativeReadoutPresentation request.2) ↔
        TypeBindingSatisfied valuation merged) ∧
      (nativeReadoutPresentation request.2).apply candidate.1 = request.1 ∧
      (∀ atom depth, request.2.applyFullCovered atom depth = true →
        (nativeReadoutPresentation request.2).apply atom = request.2.applyFull atom depth) := by
  obtain ⟨left, right, position, stored, rhs, matching, _⟩ :=
    queryEquationsAvoiding_matchAtoms_witness hit
  rw [List.mem_zipIdx_iff_getElem?] at stored
  obtain ⟨matched, merged, witness⟩ := equationInput_open_source_at
    related position left right stored rhs matching input readCovered
  exact ⟨position, left, right, matched, merged, witness⟩

namespace OpenOccurrenceControls

/-- Full theory, exact support and even raw relation-list permutation do not
fix the spelling returned by a class-first presentation selector. This is a
representation-law counterexample, not a claim about either native executable. -/
theorem semantic_agreement_does_not_fix_joint_spelling :
    let first : Bindings := ⟨[], [("a", "b"), ("c", "b")]⟩
    let second : Bindings := ⟨[], [("c", "b"), ("a", "b")]⟩
    BindingSourceAgreement first second ∧
      (nativeReadoutPresentation first).apply (.expression [.var "b", .var "b"]) ≠
        (nativeReadoutPresentation second).apply (.expression [.var "b", .var "b"]) := by
  constructor
  · exact BindingSourceAgreement.of_recordPerm ⟨List.Perm.refl [], List.Perm.swap _ _ []⟩
  · have expression (presentation : TypeSubst) (atom : Atom) :
        presentation.apply (.expression [atom, atom]) =
          .expression [presentation.apply atom, presentation.apply atom] := by
      rw [TypeSubst.apply]
      rfl
    rw [expression, expression]
    rw [nativeReadoutPresentation_apply_var, nativeReadoutPresentation_apply_var]
    decide +kernel

def sharedRuleLeft : Atom := .expression [.symbol "share-open", .var "x"]
def sharedRuleRight : Atom := .expression [.symbol "Pair", .var "x", .var "x"]
def sharedRule : Atom := .expression [.symbol "=", sharedRuleLeft, sharedRuleRight]
def duplicateSpace : Space := ⟨[sharedRule, sharedRule]⟩
def openQuery : Atom := .expression [.symbol "share-open", .var "public"]
def aliasCaller : Bindings := ⟨[], [("public", "legacy")]⟩
def candidateAt (position : Nat) : ResultPair :=
  let name := suffixName "x" position
  (.expression [.symbol "Pair", .var name, .var name], ⟨[], [("public", name)]⟩)
def requestAt (position : Nat) : ResultPair :=
  (.expression [.symbol "Pair", .var "public", .var "public"],
    ⟨[], [("public", suffixName "x" position), ("public", "legacy")]⟩)

/-- The actual query traversal retains two stored rule occurrences. Their
fresh records differ, although the eventual open result atoms coincide. -/
theorem duplicate_query_inputs :
    equationCandidates duplicateSpace [] openQuery Atom.undefinedType aliasCaller 32 =
      [candidateAt 0, candidateAt 1] ∧
    equationInputs aliasCaller 32 (candidateAt 0) = [requestAt 0] ∧
    equationInputs aliasCaller 32 (candidateAt 1) = [requestAt 1] ∧
    (requestAt 0).1 = (requestAt 1).1 ∧
    (requestAt 0).2 ≠ (requestAt 1).2 := by
  decide +kernel

/-- A fixed physical row keeps its own independent source occurrence and
its shared residual-variable readout. Neither row is justified by the other. -/
theorem each_duplicate_has_source_at (position : Nat) (selected : position = 0 ∨ position = 1) :
    ∃ matched merged,
      Spec.Eval.Steps.EquationQueryOccurrenceRel duplicateSpace [Atom.undefinedType] openQuery
        aliasCaller position sharedRuleLeft sharedRuleRight
        (freshenEquationAvoiding (equationScope [] openQuery Atom.undefinedType aliasCaller)
          position sharedRuleLeft sharedRuleRight).1
        (candidateAt position).1 matched (candidateAt position).1 merged ∧
      BindingSourceAgreement (requestAt position).2 merged ∧
      PrincipalBindingFrame (requestAt position).2 ∧
      (nativeReadoutPresentation (requestAt position).2).apply (candidateAt position).1 =
        (requestAt position).1 := by
  obtain ⟨matched, merged, occurrence, agreement, principal, _shape, _normal, _theory,
      readout, _future⟩ := equationInput_open_source_at
    (space := duplicateSpace) (live := []) (query := openQuery) (expected := Atom.undefinedType)
    (incoming := aliasCaller) (independent := aliasCaller)
    (candidate := candidateAt position) (request := requestAt position) (fuel := 32)
    (BindingSourceAgreement.refl _) position sharedRuleLeft sharedRuleRight
    (by rcases selected with rfl | rfl <;> decide +kernel)
    (by rcases selected with rfl | rfl <;> decide +kernel)
    (by rcases selected with rfl | rfl <;> decide +kernel)
    (by rcases selected with rfl | rfl <;> decide +kernel)
    (by rcases selected with rfl | rfl <;> decide +kernel)
  exact ⟨matched, merged, occurrence, agreement, principal, readout⟩

/-- A missing row cannot acquire provenance merely because another row emits
an equal atom. -/
theorem absent_row_rejected :
    ¬∃ matched merged,
      Spec.Eval.Steps.EquationQueryOccurrenceRel duplicateSpace [Atom.undefinedType] openQuery
        aliasCaller 2 sharedRuleLeft sharedRuleRight sharedRuleLeft sharedRuleRight
        matched sharedRuleRight merged := by
  rintro ⟨matched, merged, occurrence⟩
  have absent := occurrence.stored
  simp [duplicateSpace] at absent

end OpenOccurrenceControls

end Mettapedia.Languages.MeTTa.HE.FirstSuccessSourceExecution

namespace Mettapedia.Languages.MeTTa.HE.FirstSuccessSourceExecution
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Spec.Type.Presentation Spec.Type.Presentation.Theory Spec.Type.RuntimeRefinement
open Spec.Eval QueryBindingProjection EvaluatorBindingExtension

/-- Actual open matching and caller reconciliation earn the stronger frame and
therefore the readout absorption law; no equality of raw merge records is used. -/
theorem mergeBindings_readout_absorbs_caller
    {left right : Atom} {matched caller out : Bindings} {matchFuel mergeFuel : Nat}
    (matching : matched ∈ matchAtoms left right matchFuel)
    (merged : out ∈ mergeBindings matched caller mergeFuel)
    (callerFrame : PrincipalBindingFrame caller)
    (admitted : out.hasLoop = false) :
    PrincipalBindingFrame out ∧ ∀ atom,
      (nativeReadoutPresentation out).apply ((nativeReadoutPresentation caller).apply atom) =
        (nativeReadoutPresentation out).apply atom := by
  have shape := mergeBindings_assignmentsNonVariable_model merged
    (matchAtoms_assignmentsNonVariable_model matching) callerFrame.nonvariable
  have loopFree := (Spec.Match.Merge.hasLoop_eq_false_iff_semanticLoopFree out).mp admitted
  have coherent := declMerge_canonicalClassCoherent_of_match
    (DeclMatchSpec.matchAtoms_sound matching) (DeclMergeSpec.mergeBindings_sound merged)
    loopFree shape
  refine ⟨⟨loopFree, shape, coherent⟩, ?_⟩
  apply nativeReadoutPresentation_absorbs_of_models callerFrame.loopFree callerFrame.nonvariable
    callerFrame.coherent loopFree shape coherent
  intro valuation model
  exact ((FreshPrivateMerge.runtime_merge_type_solution_iff merged valuation).mp model).2

/-- At the existing proved structural bounds, actual resolver composition
inherits the actual match/merge refinement without an extra coverage premise. -/
theorem mergeBindings_applyFull_absorbs_caller
    {left right : Atom} {matched caller out : Bindings} {matchFuel mergeFuel : Nat}
    (matching : matched ∈ matchAtoms left right matchFuel)
    (merged : out ∈ mergeBindings matched caller mergeFuel)
    (callerFrame : PrincipalBindingFrame caller)
    (admitted : out.hasLoop = false) (atom : Atom) :
    out.applyFull (caller.applyFull atom (caller.resolutionFuel atom))
        (out.resolutionFuel (caller.applyFull atom (caller.resolutionFuel atom))) =
      out.applyFull atom (out.resolutionFuel atom) := by
  have next := (mergeBindings_readout_absorbs_caller matching merged callerFrame admitted).1
  apply applyFull_absorbs_of_models callerFrame.loopFree callerFrame.nonvariable
    callerFrame.coherent next.loopFree next.nonvariable next.coherent
    (fun valuation model => ((FreshPrivateMerge.runtime_merge_type_solution_iff merged valuation).mp model).2)
  · exact caller.applyFullCovered_resolutionFuel atom
  · exact out.applyFullCovered_resolutionFuel _
  · exact out.applyFullCovered_resolutionFuel atom

/-- An actual independent evaluation that preserves its input constraints
licenses joint rematerialization of the same frame's complete pending tuple.
This neither evaluates those atoms early nor changes already-rendered data. -/
theorem source_eval_pending_readout_absorbs
    {space : Space} {dispatch : Spec.Eval.GroundedDispatch} {typing : EvalTypeService}
    {live : List Atom} {protectedScope : List String} {atom expected : Atom} {sourceBefore : BindingFrame} {result : FrameResult}
    {nativeBefore nativeAfter : Bindings}
    (laws : EvalTypeServiceBindingLaws typing)
    (derived : EvalAtomRawRel space dispatch live atom expected sourceBefore result
      (protectedScope := protectedScope) (typing := typing))
    (before : BindingSourceAgreement nativeBefore sourceBefore)
    (after : BindingSourceAgreement nativeAfter result.2)
    (beforePrincipal : PrincipalBindingFrame nativeBefore)
    (afterPrincipal : PrincipalBindingFrame nativeAfter) (pending : List Atom) :
    (pending.map (nativeReadoutPresentation nativeBefore).apply).map
        (nativeReadoutPresentation nativeAfter).apply =
      pending.map (nativeReadoutPresentation nativeAfter).apply := by
  have extension := evalAtomRawRel_bindingTheoryExtends laws derived
  simp only [List.map_map]
  apply List.map_congr_left
  intro value _
  apply nativeReadoutPresentation_absorbs_of_models beforePrincipal.loopFree
    beforePrincipal.nonvariable beforePrincipal.coherent afterPrincipal.loopFree
    afterPrincipal.nonvariable afterPrincipal.coherent
  intro valuation model
  exact (before.solutions valuation).mpr (extension valuation ((after.solutions valuation).mp model))

/-- Published independent evaluation obtains the extension premise without an
external typing-service law. The paired native endpoint invariants remain
explicit; this theorem does not construct an evaluator correspondence. -/
theorem published_source_eval_pending_readout_absorbs
    {space : Space} {dispatch : Spec.Eval.GroundedDispatch}
    {live : List Atom} {protectedScope : List String} {atom expected : Atom} {sourceBefore : BindingFrame} {result : FrameResult}
    {nativeBefore nativeAfter : Bindings}
    (derived : EvalAtomRawRel space dispatch live atom expected sourceBefore result
      (protectedScope := protectedScope))
    (before : BindingSourceAgreement nativeBefore sourceBefore)
    (after : BindingSourceAgreement nativeAfter result.2)
    (beforePrincipal : PrincipalBindingFrame nativeBefore)
    (afterPrincipal : PrincipalBindingFrame nativeAfter) (pending : List Atom) :
    (pending.map (nativeReadoutPresentation nativeBefore).apply).map
        (nativeReadoutPresentation nativeAfter).apply =
      pending.map (nativeReadoutPresentation nativeAfter).apply :=
  source_eval_pending_readout_absorbs publishedTypeService_bindingLaws derived before after
    beforePrincipal afterPrincipal pending

/-- The ordinary return protocol preserves the same rematerialization law
when it restores an invocation, stops, or resumes independent evaluation. -/
theorem source_callReturn_pending_readout_absorbs
    {space : Space} {dispatch : Spec.Eval.GroundedDispatch} {typing : EvalTypeService}
    {live : List Atom} {original expected value : Atom}
    {sourceBefore : BindingFrame} {result : FrameResult} {nativeBefore nativeAfter : Bindings}
    (laws : EvalTypeServiceBindingLaws typing)
    (returned : CallReturnRel space dispatch live original expected value sourceBefore result
      (typing := typing))
    (before : BindingSourceAgreement nativeBefore sourceBefore)
    (after : BindingSourceAgreement nativeAfter result.2)
    (beforePrincipal : PrincipalBindingFrame nativeBefore)
    (afterPrincipal : PrincipalBindingFrame nativeAfter) (pending : List Atom) :
    (pending.map (nativeReadoutPresentation nativeBefore).apply).map
        (nativeReadoutPresentation nativeAfter).apply =
      pending.map (nativeReadoutPresentation nativeAfter).apply := by
  have extension := callReturnRel_bindingTheoryExtends laws returned
  simp only [List.map_map]
  apply List.map_congr_left
  intro atom _
  apply nativeReadoutPresentation_absorbs_of_models beforePrincipal.loopFree
    beforePrincipal.nonvariable beforePrincipal.coherent afterPrincipal.loopFree
    afterPrincipal.nonvariable afterPrincipal.coherent
  intro valuation model
  exact (before.solutions valuation).mpr (extension valuation ((after.solutions valuation).mp model))

namespace RetainedPresentationControls

def caller : Bindings := ⟨[], [("a", "b")]⟩
def matched : Bindings := ⟨[("a", .symbol "A")], []⟩
def selected : Bindings := ⟨[("a", .symbol "A")], [("a", "b")]⟩
def pending : List Atom := [.expression [.symbol "Pair", .var "a", .var "b"], .var "b", .var "b"]

theorem caller_principal : PrincipalBindingFrame caller := by
  have loopFree : Spec.Match.Merge.SemanticLoopFree caller :=
    (Spec.Match.Merge.hasLoop_eq_false_iff_semanticLoopFree _).mp (by decide +kernel)
  have shape : Spec.Match.ModelTheory.AssignmentsNonVariable caller := by
    intro _ _ member
    cases member
  refine ⟨loopFree, shape, ?_⟩
  apply Spec.Match.StructuralModel.canonicalClassCoherent_of_structurallySolved
  intro _ _ _ _ member
  cases member

/-- The refinement is an actual matcher/merge result, not a supplied abstract
constraint implication. -/
theorem actual_match_merge :
    matched ∈ matchAtoms (.var "a") (.symbol "A") 32 ∧
      selected ∈ mergeBindings matched caller 32 ∧ selected.hasLoop = false := by
  decide +kernel

theorem actual_pending_tuple_absorbed :
    (pending.map (nativeReadoutPresentation caller).apply).map
        (nativeReadoutPresentation selected).apply =
      pending.map (nativeReadoutPresentation selected).apply := by
  have absorbs := (mergeBindings_readout_absorbs_caller actual_match_merge.1
    actual_match_merge.2.1 caller_principal actual_match_merge.2.2).2
  simp only [List.map_map]
  exact List.map_congr_left (fun atom _ => absorbs atom)

/-- Repeated positions and two distinct names in the old shared class are all
retained in the observed tuple. -/
theorem actual_pending_values :
    pending.map (nativeReadoutPresentation selected).apply =
      [.expression [.symbol "Pair", .symbol "A", .symbol "A"], .symbol "A", .symbol "A"] := by
  have readA : (nativeReadoutPresentation selected).apply (.var "a") = .symbol "A" := by
    rw [nativeReadoutPresentation_apply_var]
    decide +kernel
  have readB : (nativeReadoutPresentation selected).apply (.var "b") = .symbol "A" := by
    rw [nativeReadoutPresentation_apply_var]
    decide +kernel
  have expression (values : List Atom) :
      (nativeReadoutPresentation selected).apply (.expression values) =
        .expression (values.map (nativeReadoutPresentation selected).apply) := by
    rw [TypeSubst.apply]
  have symbol : (nativeReadoutPresentation selected).apply (.symbol "Pair") = .symbol "Pair" := by
    rw [TypeSubst.apply]
  simp only [pending, List.map_cons, List.map_nil, expression, symbol, readA, readB]

/-- Forgetting the old alias theory breaks absorption, even though both
records have valid finite principal presentations. -/
theorem forgetting_alias_breaks_absorption :
    (nativeReadoutPresentation Bindings.empty).apply
        ((nativeReadoutPresentation caller).apply (.var "b")) ≠
      (nativeReadoutPresentation Bindings.empty).apply (.var "b") := by
  have old : (nativeReadoutPresentation caller).apply (.var "b") = .var "a" := by
    rw [nativeReadoutPresentation_apply_var]
    decide +kernel
  rw [old, nativeReadoutPresentation_apply_var, nativeReadoutPresentation_apply_var]
  decide +kernel

/-- A rendered string is ordinary data: later constraint propagation cannot
turn a previously printed variable name into the printed new value. -/
theorem rendered_string_is_not_rematerialized :
    (nativeReadoutPresentation selected).apply (.grounded (.string "$b")) =
      .grounded (.string "$b") ∧
    (nativeReadoutPresentation selected).apply (.grounded (.string "$b")) ≠
      .grounded (.string "A") := by
  simp only [TypeSubst.apply]
  decide +kernel

end RetainedPresentationControls

end Mettapedia.Languages.MeTTa.HE.FirstSuccessSourceExecution

namespace Mettapedia.Languages.MeTTa.HE.FirstSuccessSourceExecution.OpenContinuationControls
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Spec.Type.Presentation Spec.Type.RuntimeRefinement Spec.Type.Presentation.BindingTheory
open Spec.Bindings.ScopeObservation Spec.Match.ModelTheory
open QueryBindingProjection

def rule : Atom := .expression [.symbol "=",
  .expression [.symbol "share", .var "x"], .var "x"]
def context : Space := ⟨[rule]⟩
def call : Atom := .expression [.symbol "share", .var "public"]
def selectedBindings : Bindings := ⟨[], [("public", suffixName "x" 0)]⟩
def selectedCandidate : ResultPair := (.var (suffixName "x" 0), selectedBindings)
def selectedRequest : ResultPair := (.var "public", selectedBindings)

/-- The obstruction is reached by the maintained query and ordinary caller
merge, from an empty caller. No arbitrary incoherent caller is involved. -/
theorem actual_empty_caller_work_item :
    equationCandidates context [] call Atom.undefinedType Bindings.empty 24 = [selectedCandidate] ∧
      equationInputs Bindings.empty 24 selectedCandidate = [selectedRequest] := by
  decide +kernel

/-- The historical chronological fold cannot emit the selected public alias
from this actual merged record. This is a source-model representative
obstruction, not rejection or failure of the executable query. -/
theorem historical_materialization_rejects_selected :
    ¬BindingMaterializationRel selectedBindings selectedCandidate.1 selectedRequest.1 := by
  intro materialized
  have suffix : suffixName "x" 0 = "x#0" := by decide +kernel
  let p : Equiv.Perm String := Equiv.swap "private" (suffixName "x" 0)
  have renamed := materialized.rename p
  have record : renameBindings p selectedBindings = QueryBindingProjection.Controls.publicAlias := by
    simp [renameBindings, selectedBindings, QueryBindingProjection.Controls.publicAlias,
      p, suffix, Equiv.swap_apply_def]
  rw [record] at renamed
  have rejected := QueryBindingProjection.Controls.publicAlias_source_excludes_public renamed
  simp [selectedRequest, TypeSubst.typeVars, p, suffix,
    Equiv.swap_apply_def] at rejected

/-- The selected whole-frame reader admits this actual open body from the
empty caller, where the historical chronological representative was excluded. -/
theorem selected_frame_admits_open_body :
    EquationBodyEvidence context [] call Atom.undefinedType Bindings.empty
      selectedCandidate selectedRequest .semantic := by
  apply EquationBodyEvidence.of_open_query_hit
  · rw [actual_empty_caller_work_item.1]
    exact List.mem_singleton_self _
  · rw [actual_empty_caller_work_item.2]
    exact List.mem_singleton_self _
  · decide +kernel

end Mettapedia.Languages.MeTTa.HE.FirstSuccessSourceExecution.OpenContinuationControls

/-! ## Selected-frame source continuation controls -/

namespace Mettapedia.Languages.MeTTa.HE.FirstSuccessSourceExecution.SelectedFrameControls
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Spec.Eval Spec.Type Spec.Type.Presentation Spec.Type.Presentation.Theory
open Spec.Type.RuntimeRefinement Spec.Type.Presentation.BindingTheory
open Spec.Bindings.ScopeObservation Spec.Match.ModelTheory QueryBindingProjection
open FirstSuccessSourceExecution


open FirstSuccessSourceExecution.OpenContinuationControls

theorem emptyCertificate : ReadoutCertificate Bindings.empty [] :=
  ReadoutCertificate.of_fold (.nil [])
def initial : BindingFrame := .selected Bindings.empty [] emptyCertificate

def pending : Atom := .expression [.symbol "Pair", .var "public", .var "public"]
def live : List Atom := [pending, Atom.atomType]

private theorem actual_candidate :
    equationCandidates context live call Atom.undefinedType Bindings.empty 24 = [selectedCandidate] ∧
      equationInputs Bindings.empty 24 selectedCandidate = [selectedRequest] := by
  decide +kernel

/-- The real scoped occurrence constructs one selected frame. No whole
source/evaluator correspondence appears in the table's certificate. -/
theorem selected_occurrence :
    ∃ frame : BindingFrame,
      Spec.Eval.Steps.EquationQueryCandidateRel context (Atom.undefinedType :: live)
        call Bindings.empty selectedCandidate.1 frame.bindings ∧
      BindingFrame.Update .renew initial frame ∧
      frame.Materialization selectedCandidate.1 (.var "public") ∧
      frame.Materialization pending pending := by
  have matching : selectedCandidate.2 ∈ matchAtoms call
      (freshenEquationAvoiding (equationScope live call Atom.undefinedType Bindings.empty) 0
        (.expression [.symbol "share", .var "x"]) (.var "x")).1 24 := by
    decide +kernel
  have input : selectedRequest ∈ equationInputs Bindings.empty 24 selectedCandidate := by
    rw [actual_candidate.2]
    simp
  obtain ⟨matched, merged, folded, choice, occurrence, agreement, principal, fold,
      fixed, outside, allAtoms, observed⟩ :=
    equationInput_open_source_presentation_choice (space := context) (live := live)
      (BindingSourceAgreement.refl _)
      0 (.expression [.symbol "share", .var "x"]) (.var "x")
      (by rfl) (by decide +kernel) matching input (by decide +kernel)
  have certificate : ReadoutCertificate merged (nativeReadoutPresentation selectedRequest.2) :=
    ⟨(nativeReadoutPresentation_principal principal.loopFree principal.nonvariable
      principal.coherent agreement.solutions).1, folded, choice, fold, fixed, outside, allAtoms⟩
  let frame := BindingFrame.selected merged (nativeReadoutPresentation selectedRequest.2) certificate
  refine ⟨frame, occurrence.candidate, .selected emptyCertificate certificate, ?_, ?_⟩
  · exact (allAtoms selectedCandidate.1).trans observed |>.symm
  · change pending = (nativeReadoutPresentation selectedRequest.2).apply pending
    have read : (nativeReadoutPresentation selectedRequest.2).apply (.var "public") =
        .var "public" := by
      rw [nativeReadoutPresentation_apply_var]
      decide +kernel
    unfold pending
    rw [TypeSubst.apply]
    simp only [List.map_cons, List.map_nil, read, TypeSubst.apply]

private theorem no_annotations (atom : Atom) : AnnotationTypesRel atom context.atoms [] := by
  apply AnnotationTypesRel.skip
  · intro type
    simp [rule]
  · exact .nil

private theorem raw_share (scope : List Atom) (frame : BindingFrame) :
    EvalAtomRawRel context noHost scope (.symbol "share") Atom.undefinedType frame
      (.symbol "share", frame) := by
  apply EvalAtomRawRel.cast _ _ Atom.symbolType
  · simp [IsEmptyOrErrorRel, IsErrorRel, Atom.empty]
  · exact .symbol _
  · simp [Atom.undefinedType, Atom.atomType, Atom.symbolType, Atom.variableType]
  · exact Or.inl ⟨"share", rfl⟩
  · apply TypeCastRel.success (types := [Atom.undefinedType]) (earlierTypes := [])
      (laterTypes := []) (actualType := Atom.undefinedType)
    · exact .symbolUndefined (no_annotations _)
    · rfl
    · simp
    · exact .undefinedLeft _ _
  · exact .same .renew frame

private theorem raw_variable (scope : List Atom) (name : String) (expected : Atom)
    (frame : BindingFrame) :
    EvalAtomRawRel context noHost scope (.var name) expected frame (.var name, frame) := by
  exact .typePass _ _ Atom.variableType _
    (by simp [IsEmptyOrErrorRel, IsErrorRel, Atom.empty]) (.variable _) (Or.inr (Or.inr rfl))

/-- Ordinary source completion uses the selected reached frame, retaining
both pending uses of the public residual. The renderer and host stay unchanged. -/
private theorem full_share_from_candidate (frame : BindingFrame)
    (candidate : Spec.Eval.Steps.EquationQueryCandidateRel context (Atom.undefinedType :: live)
      call Bindings.empty selectedCandidate.1 frame.bindings)
    (updated : BindingFrame.Update .renew initial frame)
    (materialized : frame.Materialization selectedCandidate.1 (.var "public")) :
    EvalAtomRawRel context noHost live call Atom.undefinedType initial
      (.var "public", frame) := by
  have called : CallRel context noHost live call Atom.undefinedType initial
      (.var "public", frame) := by
    refine .equation call Atom.undefinedType selectedCandidate.1 (.var "public") initial frame
      (.var "public", frame) (.var "public", frame) ?_ ?_ candidate updated materialized ?_ ?_
    · simp [IsErrorRel, call]
    · simp [NonGroundedCallRel, Spec.Eval.Minimal.HostCall, Spec.Eval.Minimal.embeddedInstruction, call, noHost]
    · exact .raw _ _ _ (by simp [Minimal.IsFunction])
    · exact .evaluate _ _ _ _ _ (by simp [Atom.notReducible])
        (by simp [IsEmptyOrErrorRel, IsErrorRel, Atom.empty]) (raw_variable _ _ _ frame)
  have tuple : InterpretTupleRel context noHost (Atom.undefinedType :: live) call initial
      (call, initial) := by
    apply InterpretTupleRel.success (.symbol "share") [.var "public"] initial
      (.symbol "share", initial) (.expression [.var "public"], initial)
    · simp
    · exact raw_share _ _
    · simp [IsEmptyOrErrorRel, IsErrorRel, Atom.empty]
    · apply InterpretTupleRel.singleton (.var "public") initial (.var "public", initial)
      · exact raw_variable _ _ _ _
      · simp [IsEmptyOrErrorRel, IsErrorRel, Atom.empty]
    · simp [IsEmptyOrErrorRel, IsErrorRel, Atom.empty]
  apply EvalAtomRawRel.interpretSuccess _ _ Atom.expressionType
  · simp [call, IsEmptyOrErrorRel, IsErrorRel, Atom.empty]
  · exact .expression _
  · simp [Atom.undefinedType, Atom.atomType, Atom.expressionType, Atom.variableType]
  · exact ⟨.symbol "share", [.var "public"], rfl⟩
  · exact .tuplePath call Atom.undefinedType (.symbol "share") [.var "public"]
      [Atom.undefinedType] [Atom.undefinedType] [] initial (call, initial) (.var "public", frame) rfl
      (.symbolUndefined (no_annotations _)) rfl
      (.nonFunctionExhausted (by simp [FunctionTypeRel, Atom.undefinedType]) .nil) tuple called
  · simp [IsErrorRel]

theorem full_open_share :
    ∃ frame : BindingFrame,
      EvalAtomRawRel context noHost live call Atom.undefinedType initial
        (.var "public", frame) ∧ frame.Materialization pending pending := by
  obtain ⟨frame, candidate, updated, materialized, shared⟩ := selected_occurrence
  exact ⟨frame, full_share_from_candidate frame candidate updated materialized, shared⟩

/-- The actual argument continuation keeps both occurrences in its pending
syntax and passes the same selected frame to its next argument. -/
theorem pending_aliases_share_frame :
    ∃ frame : BindingFrame,
      InterpretArgsRel context noHost [] [call, pending]
        [Atom.undefinedType, Atom.atomType] initial
        (argumentPacket [.var "public", pending], frame) ∧
      frame.Materialization pending pending := by
  obtain ⟨frame, evaluated, shared⟩ := full_open_share
  refine ⟨frame, ?_, shared⟩
  refine .success call [pending] Atom.undefinedType [Atom.atomType] initial
    (.var "public", frame) (argumentPacket [pending], frame) evaluated ?_ ?_ ⟨[pending], rfl⟩
  · left
    simp [IsEmptyOrErrorRel, IsErrorRel, Atom.empty]
  · refine .success pending [] Atom.atomType [] frame (pending, frame)
      (argumentPacket [], frame) ?_ ?_ (.nil frame) ⟨[], rfl⟩
    · exact .typePass _ _ Atom.expressionType _
        (by simp [pending, IsEmptyOrErrorRel, IsErrorRel, Atom.empty]) (.expression _) (Or.inl rfl)
    · exact Or.inr rfl

end Mettapedia.Languages.MeTTa.HE.FirstSuccessSourceExecution.SelectedFrameControls

namespace Mettapedia.Languages.MeTTa.HE.FirstSuccessSourceExecution.SelectedFrameControls
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Spec.Eval
open Spec.Type Spec.Type.Presentation Spec.Type.Presentation.Theory
open Spec.Type.RuntimeRefinement Spec.Type.Presentation.BindingTheory
open Spec.Bindings.ScopeObservation Spec.Match.ModelTheory Spec.Match.Merge
open QueryBindingProjection FirstSuccessSourceExecution
open FirstSuccessSourceExecution.OpenContinuationControls

private theorem aliasPrincipal : PrincipalBindingFrame selectedBindings := by
  have loop : SemanticLoopFree selectedBindings := semanticLoopFree_of_assignments_nil rfl
  have shape : AssignmentsNonVariable selectedBindings := by
    intro key value member
    cases member
  refine ⟨loop, shape, ?_⟩
  apply Spec.Match.StructuralModel.canonicalClassCoherent_of_structurallySolved
  intro _ _ _ _ member
  cases member

private theorem aliasCertificate :
    ReadoutCertificate selectedBindings (nativeReadoutPresentation selectedBindings) :=
  nativeReadoutPresentation_certificate aliasPrincipal.loopFree
    aliasPrincipal.nonvariable aliasPrincipal.coherent (fun _ => Iff.rfl)

def aliasFrame : BindingFrame := .selected selectedBindings
  (nativeReadoutPresentation selectedBindings) aliasCertificate

private theorem exact_alias_source :
    Spec.Eval.Steps.EquationQueryCandidateRel context (Atom.undefinedType :: live)
      call Bindings.empty selectedCandidate.1 selectedBindings := by
  have admissible : SemanticLoopFree selectedBindings := semanticLoopFree_of_assignments_nil rfl
  have emptyAdmissible : SemanticLoopFree Bindings.empty := semanticLoopFree_of_assignments_nil rfl
  have emptyMerge : MergeRel equalityGroundedSemantic Bindings.empty Bindings.empty Bindings.empty :=
    .mk (List.Perm.refl []) .nil
  have aliasMerge : MergeRel equalityGroundedSemantic Bindings.empty selectedBindings selectedBindings := by
    refine .mk (order := [.equality "public" (suffixName "x" 0)]) ?_ ?_
    · decide +kernel
    · exact .equality (.consistent (values := []) rfl trivial) .nil
  have matched : MatchRel equalityGroundedSemantic call
      (.expression [.symbol "share", .var (suffixName "x" 0)]) selectedBindings :=
    .expression (.cons (.symSym "share" emptyAdmissible) emptyMerge
      (.cons (.varVar "public" (suffixName "x" 0) admissible) aliasMerge .nil)) admissible
  have fresh := EquationFreshening.freshenEquationAvoiding_alphaVariant
    (Atom.undefinedType :: live) call (.expression [.symbol "share", .var "x"]) (.var "x")
    Bindings.empty (equationScope live call Atom.undefinedType Bindings.empty) 0 (by
      intro name visible
      have present := EquationFreshening.equationScope_visible
        (type_ := Atom.undefinedType) visible
      simpa [equationScope, atomListVariables, Atom.undefinedType, atomVariables] using present)
  have actualFresh : freshenEquationAvoiding
      (equationScope live call Atom.undefinedType Bindings.empty) 0
      (.expression [.symbol "share", .var "x"]) (.var "x") =
      (.expression [.symbol "share", .var (suffixName "x" 0)], .var (suffixName "x" 0)) := by
    decide +kernel
  rw [actualFresh] at fresh
  refine ⟨.expression [.symbol "share", .var (suffixName "x" 0)], selectedCandidate.1,
    selectedBindings, ?_,
    (Spec.Match.Merge.MergeRel.mk (List.Perm.refl []) .nil).logicalMerge ?_, ?_⟩
  · exact ⟨.expression [.symbol "share", .var "x"], .var "x", by simp [context, rule],
      fresh, matched⟩
  · exact ⟨fun _ => .symbol "A", by simp [TypeBindingSatisfied, selectedBindings]⟩
  · intros
    rfl

/-- This fixed source checkpoint is also the actual successful empty-caller
share frame. Its selected table will be reused by the later-constraint control. -/
theorem exact_open_share_frame :
    EvalAtomRawRel context noHost live call Atom.undefinedType initial
      (.var "public", aliasFrame) := by
  apply full_share_from_candidate aliasFrame exact_alias_source
  · exact .selected emptyCertificate aliasCertificate
  · change .var "public" = (nativeReadoutPresentation selectedBindings).apply
      (.var (suffixName "x" 0))
    rw [nativeReadoutPresentation_apply_var]
    decide +kernel

def valueMatch : Bindings := ⟨[("public", .symbol "A")], []⟩
def valueBindings : Bindings := ⟨[("public", .symbol "A")], selectedBindings.equalities⟩

theorem real_later_constraint :
    valueMatch ∈ matchAtoms (.var "public") (.symbol "A") 32 ∧
      valueBindings ∈ mergeBindings valueMatch selectedBindings 32 ∧
      valueBindings.hasLoop = false := by
  decide +kernel

private theorem valuePrincipal : PrincipalBindingFrame valueBindings :=
  (mergeBindings_readout_absorbs_caller real_later_constraint.1
    real_later_constraint.2.1 aliasPrincipal real_later_constraint.2.2).1

private theorem valueCertificate :
    ReadoutCertificate valueBindings (nativeReadoutPresentation valueBindings) :=
  nativeReadoutPresentation_certificate valuePrincipal.loopFree
    valuePrincipal.nonvariable valuePrincipal.coherent (fun _ => Iff.rfl)

def valueFrame : BindingFrame := .selected valueBindings
  (nativeReadoutPresentation valueBindings) valueCertificate

/-- The actual later merge changes the selected frame once, and the earned
refinement rematerializes both pending occurrences through that one table. -/
theorem later_constraint_updates_both_pending_uses :
    BindingFrame.Update .renew aliasFrame valueFrame ∧
      (nativeReadoutPresentation valueBindings).apply
        ((nativeReadoutPresentation selectedBindings).apply pending) =
        .expression [.symbol "Pair", .symbol "A", .symbol "A"] := by
  constructor
  · exact .selected aliasCertificate valueCertificate
  · rw [aliasCertificate.absorbs valueCertificate
      (fun valuation model => ((FreshPrivateMerge.runtime_merge_type_solution_iff
        real_later_constraint.2.1 valuation).mp model).2)]
    have read : (nativeReadoutPresentation valueBindings).apply (.var "public") = .symbol "A" := by
      rw [nativeReadoutPresentation_apply_var]
      decide +kernel
    unfold pending
    rw [TypeSubst.apply]
    simp only [List.map_cons, List.map_nil, read, TypeSubst.apply]

private theorem historicalAliasFold :
    EquationListPresentationRel (bindingAtomEquations selectedBindings) []
      [("public", .var (suffixName "x" 0))] := by
  change EquationListPresentationRel [(.var "public", .var (suffixName "x" 0))] [] _
  refine .cons (.ordinary rfl rfl ?_) (.nil _)
  simpa [TypeSubst.bind, TypeSubst.erase] using
    (AppliedReducedTypeMatchRel.bindLeft (substitution := []) (name := "public")
      (right := .var (suffixName "x" 0)) (by decide +kernel))

/-- Both alternatives are valid principal readouts, but an unchanged frame
cannot switch from one to the other between two operand reads. -/
theorem unchanged_frame_refuses_different_valid_table :
    ¬BindingFrame.Update .retain aliasFrame
      (.selected selectedBindings [("public", .var (suffixName "x" 0))]
        (ReadoutCertificate.of_fold historicalAliasFold)) := by
  apply BindingFrame.Update.no_reselect aliasCertificate
    (ReadoutCertificate.of_fold historicalAliasFold)
  intro same
  have sameRead := congrArg (fun table : TypeSubst => table.apply (.var "public")) same
  rw [nativeReadoutPresentation_apply_var] at sameRead
  have actual : selectedBindings.applyFull (.var "public")
      (selectedBindings.resolutionFuel (.var "public")) = .var "public" := by
    decide +kernel
  rw [actual] at sameRead
  have expected : TypeSubst.apply [("public", .var (suffixName "x" 0))] (.var "public") =
      .var (suffixName "x" 0) := by simp [TypeSubst.apply, TypeSubst.lookup]
  rw [expected] at sameRead
  exact (by decide +kernel : (Atom.var "public") ≠ .var (suffixName "x" 0)) sameRead

/-- A printed residual is data: the later constraint changes syntax variable
occurrences but does not rewrite a previously rendered string. -/
theorem printed_string_stays_opaque :
    valueFrame.Materialization (.grounded (.string "$public"))
      (.grounded (.string "$public")) ∧
    ¬valueFrame.Materialization (.grounded (.string "$public")) (.grounded (.string "A")) := by
  change _ = TypeSubst.apply _ _ ∧ ¬(_ = TypeSubst.apply _ _)
  simp only [TypeSubst.apply]
  decide +kernel

end Mettapedia.Languages.MeTTa.HE.FirstSuccessSourceExecution.SelectedFrameControls

namespace Mettapedia.Languages.MeTTa.HE.FirstSuccessSourceExecution.SelectedFrameControls
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Spec.Eval
open Spec.Type Spec.Type.Presentation Spec.Match.Merge Spec.Eval.Steps
open FirstSuccessSourceExecution FirstSuccessSourceExecution.OpenContinuationControls
open QueryBindingProjection

def refineInstruction : Atom := .expression
  [.symbol "unify", .var "public", .symbol "A", .symbol "ok", .symbol "failed"]
def pendingReturn : Atom := .expression [.symbol "return", pending]
def refineBody : Atom := .expression
  [.symbol "chain", refineInstruction, .var "ignored", pendingReturn]
def refineFunction : Atom := .expression [.symbol "function", refineBody]
def resolvedPending : Atom := .expression [.symbol "Pair", .symbol "A", .symbol "A"]

private theorem source_value_merge :
    MergeRel equalityGroundedSemantic valueMatch selectedBindings valueBindings := by
  refine .mk (order := [.equality "public" (suffixName "x" 0)]) ?_ ?_
  · decide +kernel
  · exact .equality (.consistent (values := [.symbol "A"]) (by decide +kernel)
      (by intro value present; cases present)) .nil

private theorem source_unify_candidate :
    UnifyCandidateRel (.var "public") (.symbol "A") selectedBindings valueBindings := by
  refine ⟨valueMatch, .varNonVar rfl ?_, source_value_merge.logicalMerge
    ⟨fun _ => .symbol "A", ?_⟩⟩
  · exact (hasLoop_eq_false_iff_semanticLoopFree _).mp (by decide +kernel)
  · simp [Spec.Type.RuntimeRefinement.TypeBindingSatisfied, valueBindings, selectedBindings,
      Spec.Type.RuntimeRefinement.applyTypeValuation]

private theorem pending_return_materialized :
    valueFrame.Materialization pendingReturn (.expression [.symbol "return", resolvedPending]) := by
  change .expression [.symbol "return", resolvedPending] =
    (nativeReadoutPresentation valueBindings).apply pendingReturn
  have read : (nativeReadoutPresentation valueBindings).apply (.var "public") = .symbol "A" := by
    rw [nativeReadoutPresentation_apply_var]
    decide +kernel
  unfold pendingReturn pending resolvedPending
  rw [TypeSubst.apply]
  simp only [List.map_cons, List.map_nil, TypeSubst.apply, read]

/-- The reached share frame feeds the actual minimal chain/function rules.
The later source unification refines it once; both occurrences in the saved
return template are read through the new certified table on completion. -/
theorem actual_continuation_refines_both_uses :
    Minimal.CoreStepRel context noHost [] refineFunction aliasFrame
      (resolvedPending, valueFrame) := by
  apply Minimal.CoreStepRel.functionReturn context refineBody resolvedPending aliasFrame valueFrame
  · exact ⟨_, rfl⟩
  apply Minimal.CoreFunctionBodyRel.terminal context refineBody aliasFrame
    (pendingReturn, valueFrame) (.expression [.symbol "return", resolvedPending])
  · apply Minimal.CoreRunRel.chain context refineBody aliasFrame
      (pendingReturn, valueFrame) (pendingReturn, valueFrame)
    · exact ⟨[refineInstruction, .var "ignored", pendingReturn], rfl⟩
    · have substituted : Minimal.substituteName "ignored" (.symbol "ok") pendingReturn =
          pendingReturn := by simp [pendingReturn, pending, Minimal.substituteName]
      rw [← substituted]
      apply Minimal.CoreStepRel.chain context refineInstruction "ignored" pendingReturn aliasFrame
        (.symbol "ok", valueFrame) (.symbol "ok")
      · exact Minimal.CoreRunRel.instruction context refineInstruction aliasFrame
          (.symbol "ok", valueFrame) rfl (by simp [Minimal.IsChain, refineInstruction])
          (Minimal.CoreStepRel.unifySuccess context (.var "public") (.symbol "A")
            (.symbol "ok") (.symbol "failed") (.symbol "ok") aliasFrame valueFrame
            source_unify_candidate (.selected aliasCertificate valueCertificate)
            (by
              change .symbol "ok" = TypeSubst.apply _ (.symbol "ok")
              rw [TypeSubst.apply]))
      · change .symbol "ok" = TypeSubst.apply _ (.symbol "ok")
        rw [TypeSubst.apply]
    · exact .data _ _ _ rfl
  · exact pending_return_materialized
  · rfl

/-- Both phases use one actual retained frame, rather than independently
renaming the two public occurrences at each observation. -/
theorem open_share_then_real_refinement :
    EvalAtomRawRel context noHost live call Atom.undefinedType initial
        (.var "public", aliasFrame) ∧
      Minimal.CoreStepRel context noHost [] refineFunction aliasFrame
        (resolvedPending, valueFrame) :=
  ⟨exact_open_share_frame, actual_continuation_refines_both_uses⟩

end Mettapedia.Languages.MeTTa.HE.FirstSuccessSourceExecution.SelectedFrameControls

namespace Mettapedia.Languages.MeTTa.HE.FirstSuccessSourceExecution.SelectedFrameControls
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Spec.Eval Spec.Type Spec.Type.Presentation RecursiveTasks FirstSuccessRecursiveExecution
open FirstSuccessLeafEvaluation OpenContinuationControls

private theorem open_call_query :
    equationCandidates context live call Atom.symbolType Bindings.empty 24 = [selectedCandidate] := by
  decide +kernel

private theorem open_call_input :
    equationInputs Bindings.empty 24 selectedCandidate = [selectedRequest] := by
  decide +kernel

private theorem open_call_evidence :
    EquationBodyEvidence context live call Atom.symbolType Bindings.empty
      selectedCandidate selectedRequest .semantic := by
  apply EquationBodyEvidence.of_open_query_hit
  · rw [open_call_query]
    exact List.mem_singleton_self _
  · rw [open_call_input]
    exact List.mem_singleton_self _
  · decide +kernel

private theorem open_call_body :
    AtomDerivation (comparison := .semantic) context live selectedRequest.1
      Atom.symbolType selectedRequest.2 24 [selectedRequest] :=
  .leaf live (.var "public") Atom.symbolType selectedBindings 23
    (Or.inr ⟨Atom.variableType, .variable _, Or.inr (Or.inr rfl)⟩)

/-- Automatic open-query admission supplies the ordinary worker's existing
recursive evidence, with its actual live tuple and reached alias record. -/
theorem open_call_source :
    CallDerivation (comparison := .semantic) context live call Atom.symbolType
      Bindings.empty 25 [selectedRequest] :=
  single_equation_call_derivation context "share" (by decide) (by decide) (by decide) live
    (.var "public") Bindings.empty 24 selectedCandidate selectedRequest [selectedRequest]
    open_call_query open_call_input open_call_evidence open_call_body (by decide +kernel)

private theorem open_call_covered : open_call_source.Covered := by
  apply single_equation_call_covered context "share" (by decide) (by decide) (by decide) live
    (.var "public") Bindings.empty 24 selectedCandidate selectedRequest [selectedRequest]
    open_call_query open_call_input open_call_evidence open_call_body
    (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · intro merged member _
    have exactMerge : mergeBindings selectedCandidate.2 (aliasConstraints Bindings.empty) 24 = [selectedBindings] := by
      decide +kernel
    rw [exactMerge] at member
    obtain rfl := List.mem_singleton.mp member
    decide +kernel
  · exact .leaf (leaf := Or.inr ⟨Atom.variableType, .variable _, Or.inr (Or.inr rfl)⟩)

/-- The same source evidence constructs actual checked completion; extra
scheduler budget cannot alter the returned occurrence or its full bindings. -/
theorem open_call_checked_completion (earned : ResultSet) :
    ∃ budget, ∀ later, (Checked.machine HE.GroundedDispatch.none).run (budget + later)
      ⟨context, .work (.call call Atom.symbolType Bindings.empty 25 live), [], earned⟩ =
      ([selectedRequest], .finished ⟨context, .returning [], [], earned ++ [selectedRequest]⟩) :=
  open_call_source.checked_completed open_call_covered earned

/-- The actual completed occurrence has a selected source frame and a single
readout for both still-pending public occurrences. -/
theorem open_call_independent_selected_continuation :
    ∃ frame : BindingFrame,
      CallRel context noHost live call Atom.symbolType PrincipalBindingFrame.empty.sourceFrame
        (.var "public", frame) ∧
      SourceBindingComparison.semantic.FrameRelated selectedBindings frame ∧
      frame.Materialization pending pending := by
  obtain ⟨frame, source, related⟩ := open_call_source.sound selectedRequest (by simp)
    PrincipalBindingFrame.empty.sourceFrame
    (.of_principal PrincipalBindingFrame.empty (.refl _))
  refine ⟨frame, source, related, ?_⟩
  have observed := related.materialization pending 32 (by decide +kernel)
  have actual : selectedBindings.applyFull pending 32 = pending := by decide +kernel
  change frame.Materialization pending (selectedBindings.applyFull pending 32) at observed
  simpa only [actual] using observed

/-- An unfinished open call remains a saved call; it is not a completed empty
answer and may be supplied additional depth through the existing machine API. -/
theorem open_call_zero_depth_suspends :
    (Checked.machine HE.GroundedDispatch.none).run 2
      ⟨context, .work (.call call Atom.symbolType Bindings.empty 0 live), [], []⟩ =
      ([], .suspended .evaluationDepth
        ⟨context, .work (.invocation (.ordinary Atom.symbolType) call Bindings.empty 0 live), [], []⟩) := rfl

end Mettapedia.Languages.MeTTa.HE.FirstSuccessSourceExecution.SelectedFrameControls


namespace Mettapedia.Languages.MeTTa.HE.FirstSuccessSourceExecution.FunctionBodyControls
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Spec.Eval Spec.Eval.Steps Spec.Type.RuntimeRefinement
open RecursiveTasks FirstSuccessRecursiveExecution

private def value : Atom := .symbol "Value"
private def pending : Atom := .expression [.symbol "Pair", .var "public", .var "public"]
private def answer : Atom := .expression [.symbol "Pair", value, value]
private def template : Atom := .expression [.symbol "return", pending]
private def returned : Atom := .expression [.symbol "return", answer]
private def body : Atom := .expression [.symbol "unify", value, .var "public", template, .symbol "Miss"]
private def block : Atom := .expression [.symbol "function", body]
private def outer : Atom := .expression [.symbol "outer", .var "public"]
private def bindings : Bindings := Bindings.empty.assign "public" value
private def raw : ResultSet := [(returned, bindings)]

private theorem raw_success :
    unifySuccessResults value (.var "public") template Bindings.empty 9 = raw := by decide +kernel

private theorem matched_source :
    Spec.Match.Merge.MatchRel Spec.Match.Merge.equalityGroundedSemantic
      value (.var "public") bindings := by
  apply Spec.Match.Merge.MatchRel.nonVarVar
  · rfl
  · exact (Spec.Match.Merge.hasLoop_eq_false_iff_semanticLoopFree _).mp (by decide +kernel)

private theorem primitive (live : List Atom) (caller : Option Atom) :
    PrimitiveDerivation (comparison := .semantic) Space.empty live caller body Bindings.empty 10 raw := by
  have derived := PrimitiveDerivation.unifySuccess (space := Space.empty) (comparison := .semantic)
    live caller value (.var "public") template (.symbol "Miss") Bindings.empty 9
    (by decide +kernel) (by rw [raw_success]; simp [raw])
  simpa only [body, raw_success] using derived

/-- The body performs an actual binding-changing primitive, then reads its
returned syntax through that reached frame. Both pending uses are retained. -/
theorem function_body_admitted (live : List Atom) (caller : Option Atom) :
    FunctionBodyDerivation (comparison := .semantic) Space.empty live caller body Bindings.empty 12 raw := by
  have child : MinimalDerivation (comparison := .semantic) Space.empty live caller body Bindings.empty 11 raw :=
    .instruction live caller body Bindings.empty 10 raw rfl
      (by simp [Minimal.IsChain, body]) (primitive live caller)
  have derived := FunctionBodyDerivation.run (space := Space.empty) (comparison := .semantic) live caller body
    Bindings.empty 11 raw (fun result => [result]) child
    (by intro result member; obtain rfl := List.mem_singleton.mp member; decide +kernel)
    (by intro result member instruction; obtain rfl := List.mem_singleton.mp member; rfl)
    (by intro result member instruction; obtain rfl := List.mem_singleton.mp member; contradiction)
  simpa only [raw, List.flatMap_cons, List.flatMap_nil, List.singleton_append] using derived

/-- Function completion unwraps the return while retaining the new binding. -/
theorem function_admitted :
    PrimitiveDerivation (comparison := .semantic) Space.empty [] (some outer) block Bindings.empty 13
      [(answer, bindings)] := by
  exact PrimitiveDerivation.function [] (some outer)
    [.symbol "unify", value, .var "public", template, .symbol "Miss"] Bindings.empty 12 raw
    (function_body_admitted [block] (some block))

theorem function_independent_source :
    ∃ output, Minimal.CoreStepRel Space.empty noHost [] (caller := some outer)
      block PrincipalBindingFrame.empty.sourceFrame (answer, output) ∧
      SourceBindingComparison.semantic.FrameRelated bindings output := by
  exact function_admitted.sound (answer, bindings) (by simp)
    PrincipalBindingFrame.empty.sourceFrame
    (.of_principal PrincipalBindingFrame.empty (.refl _))

theorem function_actual_worker :
    Covered.Realizes Space.empty (.primitive block Bindings.empty 13 [] (some outer))
      [(answer, bindings)] := function_admitted.covered_realizes

private def initial : Configuration :=
  ⟨Space.empty, .work (.primitive block Bindings.empty 13 [] (some outer)), [], []⟩
private def afterWrite : Configuration :=
  ⟨Space.empty, .returning raw,
    [.bodyResults 11 [block] (some block), .functionTerminal (some outer)], []⟩

/-- The paused machine has already changed its binding record; its saved
continuations still contain the raw original caller and function body. -/
theorem checkpoint_after_actual_write :
    (Checked.machine HE.GroundedDispatch.none).run 4 initial = ([], .exhausted afterWrite) := by
  rfl

theorem checkpoint_keeps_nonzero_binding :
    afterWrite.control = .returning [(returned, bindings)] ∧
    bindings.lookup "public" = some value ∧ bindings ≠ Bindings.empty := by
  decide +kernel

theorem checkpoint_resumes_exactly :
    ∃ budget remaining,
      (Checked.machine HE.GroundedDispatch.none).run budget afterWrite =
        (remaining, .finished ⟨Space.empty, .returning [], [], [(answer, bindings)]⟩) ∧
      remaining = [(answer, bindings)] := by
  simpa only [List.nil_append] using
    Covered.completes_saved function_actual_worker [] 4 [] afterWrite checkpoint_after_actual_write

private def noReturnBody : Atom := .expression [.symbol "Value"]
private def noReturnBlock : Atom := .expression [.symbol "function", noReturnBody]

private theorem no_return_body :
    FunctionBodyDerivation (comparison := .semantic) Space.empty [noReturnBlock]
      (some noReturnBlock) noReturnBody Bindings.empty 5 [(noReturnBody, Bindings.empty)] := by
  exact .run [noReturnBlock] (some noReturnBlock) noReturnBody Bindings.empty 4
    [(noReturnBody, Bindings.empty)] (fun result => [result])
    (.data _ _ _ _ 3 rfl)
    (by intro result member; obtain rfl := List.mem_singleton.mp member; decide +kernel)
    (by intro result member instruction; obtain rfl := List.mem_singleton.mp member; rfl)
    (by intro result member instruction; obtain rfl := List.mem_singleton.mp member; contradiction)

theorem no_return_uses_original_caller :
    PrimitiveDerivation (comparison := .semantic) Space.empty [] (some outer)
      noReturnBlock Bindings.empty 6 [(Atom.error outer (.symbol "NoReturn"), Bindings.empty)] := by
  exact .function [] (some outer) [.symbol "Value"] Bindings.empty 5 _ no_return_body

theorem no_return_cannot_report_terminal :
    Atom.error outer (.symbol "NoReturn") ≠ Atom.error noReturnBody (.symbol "NoReturn") := by
  decide +kernel

/-- Ready provenance is supplied by the producer, never guessed from a
function-looking atom. A completed wrapper remains ordinary result data. -/
theorem completed_function_is_not_executed :
    Covered.Realizes Space.empty (.produced block Bindings.empty 14 [] (some outer) .completed)
      [(block, Bindings.empty)] :=
  Covered.produced_completed_realizes Space.empty block Bindings.empty 13 [] (some outer)

private theorem function_at_call :
    MinimalDerivation (comparison := .semantic) Space.empty [Atom.atomType] none
      block Bindings.empty 14 [(answer, bindings)] := by
  apply MinimalDerivation.instruction _ _ _ _ 13 _ rfl
    (by simp [Minimal.IsChain, block])
  exact PrimitiveDerivation.function [Atom.atomType] none
    [.symbol "unify", value, .var "public", template, .symbol "Miss"] Bindings.empty 12 raw
    (function_body_admitted [block, Atom.atomType] (some block))

private theorem answer_return :
    ReturnDerivation (comparison := .semantic) Space.empty [] block Atom.atomType answer bindings 14
      [(answer, bindings)] :=
  .evaluate [] block Atom.atomType answer bindings 14 _
    (by simp [answer, Atom.notReducible])
    (by simp [answer, IsEmptyOrErrorRel, IsErrorRel, Atom.empty])
    (.leaf [] answer Atom.atomType bindings 13 (Or.inr ⟨Atom.expressionType, .expression _, Or.inl rfl⟩))

private theorem answer_return_covered : answer_return.Covered := by
  exact .evaluate
    (accepted := by simp [answer, Atom.notReducible])
    (running := by simp [answer, IsEmptyOrErrorRel, IsErrorRel, Atom.empty])
    (child := .leaf [] answer Atom.atomType bindings 13
      (Or.inr ⟨Atom.expressionType, .expression _, Or.inl rfl⟩))
    (.leaf (leaf := Or.inr ⟨Atom.expressionType, .expression _, Or.inl rfl⟩))

private theorem ordinary_call_admitted :
    CallDerivation (comparison := .semantic) Space.empty [] block Atom.atomType Bindings.empty 15
      [(answer, bindings)] :=
  .embedded [] "function" [body] Atom.atomType Bindings.empty 14 [(answer, bindings)] (fun result => [result])
    rfl (by decide) rfl function_at_call
    (by intro result member; obtain rfl := List.mem_singleton.mp member; exact answer_return)

private theorem ordinary_call_covered : ordinary_call_admitted.Covered := by
  apply CallDerivation.Covered.embedded
    (semantic := rfl) (clean := by decide) (instruction := rfl) (child := function_at_call)
    (outputs := fun result => [result])
    (returns := by intro result member; obtain rfl := List.mem_singleton.mp member; exact answer_return)
  intro result member
  obtain rfl := List.mem_singleton.mp member
  exact answer_return_covered

/-- The same mutual family now constructs ordinary call meaning through its
actual minimal body, changed selected frame and typed return receiver. -/
theorem ordinary_function_independent_source :
    ∃ output, CallRel Space.empty noHost [] block Atom.atomType
      PrincipalBindingFrame.empty.sourceFrame (answer, output) ∧
      SourceBindingComparison.semantic.FrameRelated bindings output :=
  ordinary_call_admitted.sound (answer, bindings) (by simp)
    PrincipalBindingFrame.empty.sourceFrame
    (.of_principal PrincipalBindingFrame.empty (.refl _))

theorem ordinary_function_checked_completion (earned : ResultSet) :
    ∃ budget, ∀ later, (Checked.machine HE.GroundedDispatch.none).run (budget + later)
      ⟨Space.empty, .work (.call block Atom.atomType Bindings.empty 15 []), [], earned⟩ =
      ([(answer, bindings)], .finished ⟨Space.empty, .returning [], [], earned ++ [(answer, bindings)]⟩) :=
  ordinary_call_admitted.checked_completed ordinary_call_covered earned

/-- Raw invocation has the same body behavior but keeps its raw receiver;
ordinary interpretation's additional typed return is separately proved. -/
theorem raw_function_checked_path :
    Covered.Realizes Space.empty (.invocation .raw block Bindings.empty 15 [Atom.atomType] none)
      [(answer, bindings)] :=
  Covered.raw_embedded_realizes Space.empty "function" [body] Bindings.empty 14 [Atom.atomType]
    none [(answer, bindings)] rfl function_at_call.covered_realizes

private def refusal : Atom :=
  .expression [.symbol "unify", value, value, Atom.notReducible, .symbol "Else"]

private theorem refusal_primitive :
    PrimitiveDerivation (comparison := .semantic) Space.empty [Atom.atomType] none
      refusal Bindings.empty 10 [(Atom.notReducible, Bindings.empty)] := by
  apply PrimitiveDerivation.unifySuccess _ _ value value Atom.notReducible (.symbol "Else")
    Bindings.empty 9 (by decide +kernel) (by decide +kernel)

private theorem refusal_minimal :
    MinimalDerivation (comparison := .semantic) Space.empty [Atom.atomType] none
      refusal Bindings.empty 11 [(Atom.notReducible, Bindings.empty)] :=
  .instruction _ _ _ _ 10 _ rfl (by simp [Minimal.IsChain, refusal]) refusal_primitive

private theorem refusal_call :
    CallDerivation (comparison := .semantic) Space.empty [] refusal Atom.atomType
      Bindings.empty 12 [(refusal, Bindings.empty)] := by
  exact .embedded [] "unify" [value, value, Atom.notReducible, .symbol "Else"]
    Atom.atomType Bindings.empty 11 [(Atom.notReducible, Bindings.empty)]
    (fun _ => [(refusal, Bindings.empty)]) rfl (by decide) rfl refusal_minimal
    (by intro result member; obtain rfl := List.mem_singleton.mp member; exact .notReducible ..)

private theorem refusal_call_covered : refusal_call.Covered := by
  apply CallDerivation.Covered.embedded
    (semantic := rfl) (clean := by decide) (instruction := rfl) (child := refusal_minimal)
    (outputs := fun _ => [(refusal, Bindings.empty)])
    (returns := by
      intro result member
      obtain rfl := List.mem_singleton.mp member
      exact .notReducible ..)
  intro result member
  obtain rfl := List.mem_singleton.mp member
  exact .notReducible

/-- A raw invocation exposes its refusal value. The ordinary receiver restores
the original invocation through the actual typed return task. -/
theorem raw_and_ordinary_refusal_differ :
    Covered.Realizes Space.empty (.invocation .raw refusal Bindings.empty 12 [Atom.atomType] none)
      [(Atom.notReducible, Bindings.empty)] ∧
    Covered.Realizes Space.empty (.call refusal Atom.atomType Bindings.empty 12 [])
      [(refusal, Bindings.empty)] ∧
    [(Atom.notReducible, Bindings.empty)] ≠ [(refusal, Bindings.empty)] := by
  refine ⟨?_, refusal_call.covered_realizes refusal_call_covered, ?_⟩
  · exact Covered.raw_embedded_realizes Space.empty "unify"
      [value, value, Atom.notReducible, .symbol "Else"] Bindings.empty 11 [Atom.atomType]
      none [(Atom.notReducible, Bindings.empty)] rfl refusal_minimal.covered_realizes
  · decide +kernel

theorem ordinary_refusal_independent_source :
    ∃ output, CallRel Space.empty noHost [] refusal Atom.atomType
      PrincipalBindingFrame.empty.sourceFrame (refusal, output) ∧
      SourceBindingComparison.semantic.FrameRelated Bindings.empty output :=
  refusal_call.sound (refusal, Bindings.empty) (by simp)
    PrincipalBindingFrame.empty.sourceFrame
    (.of_principal PrincipalBindingFrame.empty (.refl _))

private def closedReturn : Atom := .expression [.symbol "return", value]
private def closedBlock : Atom := .expression [.symbol "function", closedReturn]
private def duplicateQuery : Atom := .expression [.symbol "duplicate-function"]
private def duplicateRule : Atom := .expression [.symbol "=", duplicateQuery, closedBlock]
private def duplicateSpace : Space := Space.ofList [duplicateRule, duplicateRule]
private def duplicateRows : ResultSet := [(closedBlock, Bindings.empty), (closedBlock, Bindings.empty)]

/-- The two equal results come from distinct stored equation positions. -/
theorem duplicate_function_query_occurrences :
    duplicateSpace.atoms[0]? = some duplicateRule ∧
    duplicateSpace.atoms[1]? = some duplicateRule ∧
    equationCandidates duplicateSpace [] duplicateQuery Atom.atomType Bindings.empty 9 = duplicateRows ∧
    rawQueryResults duplicateSpace duplicateQuery Atom.atomType Bindings.empty 9 [] = duplicateRows := by
  decide +kernel

private theorem closed_function_body :
    FunctionBodyDerivation (comparison := .semantic) duplicateSpace [closedBlock]
      (some closedBlock) closedReturn Bindings.empty 5 [(closedReturn, Bindings.empty)] := by
  exact .run [closedBlock] (some closedBlock) closedReturn Bindings.empty 4
    [(closedReturn, Bindings.empty)] (fun result => [result])
    (.data _ _ _ _ 3 rfl)
    (by intro result member; obtain rfl := List.mem_singleton.mp member; decide +kernel)
    (by intro result member instruction; obtain rfl := List.mem_singleton.mp member; rfl)
    (by intro result member instruction; obtain rfl := List.mem_singleton.mp member; contradiction)

private theorem closed_function :
    PrimitiveDerivation (comparison := .semantic) duplicateSpace [] (some duplicateQuery)
      closedBlock Bindings.empty 6 [(value, Bindings.empty)] :=
  .function [] (some duplicateQuery) [.symbol "return", value] Bindings.empty 5 _ closed_function_body

/-- Actual ordered producer traversal executes both physical replies. This
local composition does not assume a function-producing equation admission. -/
theorem duplicate_function_producers_retained :
    Covered.Realizes duplicateSpace
      (.productions 7 duplicateRows [] (some duplicateQuery) .emitted)
      [(value, Bindings.empty), (value, Bindings.empty)] := by
  have child := Covered.produced_function_realizes duplicateSpace closedReturn Bindings.empty 6 []
    (some duplicateQuery) [(value, Bindings.empty)] closed_function.covered_realizes
  exact Covered.productions_realizes duplicateSpace 7 [] (some duplicateQuery) .emitted
    (requests := duplicateRows)
    (outputs := [[(value, Bindings.empty)], [(value, Bindings.empty)]])
    (.cons child (.cons child .nil))

theorem duplicate_function_results_not_deduplicated :
    [(value, Bindings.empty), (value, Bindings.empty)] ≠ [(value, Bindings.empty)] := by
  decide +kernel

end Mettapedia.Languages.MeTTa.HE.FirstSuccessSourceExecution.FunctionBodyControls


/-! ## Function-producing equation occurrences -/

namespace Mettapedia.Languages.MeTTa.HE.FirstSuccessSourceExecution.EquationProducerControls
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
open RecursiveTasks RecursiveMachine FirstSuccessRecursiveExecution
open Spec.Eval Spec.Type Spec.Type.Presentation Spec.Type.Presentation.Theory
open Spec.Bindings.ScopeObservation

private def value : Atom := .symbol "Value"
private def query : Atom := .expression [.symbol "producer", value]
private def pattern : Atom := .expression [.symbol "producer", .var "x"]
private def sourceBody : Atom := .expression [.symbol "function", .expression [.symbol "return", .var "x"]]
private def rule : Atom := .expression [.symbol "=", pattern, sourceBody]
private def context : Space := Space.ofList [rule, rule]
private def returned : Atom := .expression [.symbol "return", value]
private def block : Atom := .expression [.symbol "function", returned]
private def key (index : Fin 2) : String := "x#" ++ Nat.repr index.val
private def bindings (index : Fin 2) : Bindings := Bindings.empty.assign (key index) value
private def candidate (index : Fin 2) : ResultPair :=
  (.expression [.symbol "function", .expression [.symbol "return", .var (key index)]], bindings index)
private def request (index : Fin 2) : ResultPair := (block, bindings index)
private def answers : ResultSet := [(value, bindings 0), (value, bindings 1)]

private theorem queried :
    equationCandidates context [] query Atom.symbolType Bindings.empty 12 = [candidate 0, candidate 1] := by
  decide +kernel

private theorem prepared (index : Fin 2) :
    equationInputs Bindings.empty 12 (candidate index) = [request index] := by
  fin_cases index <;> decide +kernel

private theorem occurrence_evidence (index : Fin 2) :
    EquationBodyEvidence context [] query Atom.symbolType Bindings.empty
      (candidate index) (request index) .semantic := by
  apply EquationBodyEvidence.of_open_query_at (fuel := 12) index.val pattern sourceBody
  · fin_cases index <;> decide +kernel
  · fin_cases index <;> decide +kernel
  · fin_cases index <;> decide +kernel
  · rw [prepared]; exact List.mem_singleton_self _
  · fin_cases index <;> decide +kernel

private theorem completed_body (index : Fin 2) :
    FunctionBodyDerivation (comparison := .semantic) context [block, Atom.symbolType]
      (some block) returned (bindings index) 10 [(returned, bindings index)] := by
  exact .run [block, Atom.symbolType] (some block) returned (bindings index) 9
    [(returned, bindings index)] (fun result => [result])
    (.data _ _ _ _ 8 rfl)
    (by intro result member; obtain rfl := List.mem_singleton.mp member
        fin_cases index <;> decide +kernel)
    (by intro result member instruction; obtain rfl := List.mem_singleton.mp member
        fin_cases index <;> decide +kernel)
    (by intro result member instruction; obtain rfl := List.mem_singleton.mp member
        fin_cases index <;> contradiction)

private theorem completed_producer (index : Fin 2) :
    ProducedDerivation (comparison := .semantic) context [Atom.symbolType] (some query)
      block (bindings index) 12 [(value, bindings index)] := by
  exact .function [Atom.symbolType] (some query) returned (bindings index) 11 _ rfl
    (.function [Atom.symbolType] (some query) [.symbol "return", value] (bindings index) 10 _
      (completed_body index))

private theorem evidence : ∀ selected ∈ equationCandidates context [] query Atom.symbolType Bindings.empty 12,
    ∀ input ∈ equationInputs Bindings.empty 12 selected,
      EquationBodyEvidence context [] query Atom.symbolType Bindings.empty selected input .semantic := by
  intro selected member input present
  rw [queried] at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  all_goals
    rw [prepared] at present
    obtain rfl := List.mem_singleton.mp present
    exact occurrence_evidence _

private theorem producers : ∀ selected ∈ equationCandidates context [] query Atom.symbolType Bindings.empty 12,
    ∀ input ∈ equationInputs Bindings.empty 12 selected,
      ProducedDerivation (comparison := .semantic) context [Atom.symbolType] (some query)
        input.1 input.2 12 [(value, input.2)] := by
  intro selected member input present
  rw [queried] at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  all_goals
    rw [prepared] at present
    obtain rfl := List.mem_singleton.mp present
    exact completed_producer _

private theorem returns : ∀ selected ∈ equationCandidates context [] query Atom.symbolType Bindings.empty 12,
    ∀ input ∈ equationInputs Bindings.empty 12 selected, ∀ completed ∈ [(value, input.2)],
      ReturnDerivation (comparison := .semantic) context [] query Atom.symbolType
        completed.1 completed.2 12 [completed] := by
  intro selected member input present completed appeared
  obtain rfl := List.mem_singleton.mp appeared
  exact .evaluate [] query Atom.symbolType value input.2 12 _
    (by decide) (by simp [value, IsEmptyOrErrorRel, IsErrorRel, Atom.empty])
    (.leaf [] value Atom.symbolType input.2 11 (Or.inr ⟨Atom.symbolType, .symbol _, Or.inr (Or.inl rfl)⟩))

private theorem selected : rawQueryResults context query Atom.symbolType Bindings.empty 12 [] ≠ [] := by
  decide +kernel

/-- Both physical equations execute their function body, then the ordinary
return receiver retains the distinct fresh binding of that occurrence. -/
theorem call_admitted :
    CallDerivation (comparison := .semantic) context [] query Atom.symbolType Bindings.empty 13 answers := by
  have derived := CallDerivation.equations [] "producer" [value] Atom.symbolType Bindings.empty 12
    (fun _ input => [(value, input.2)]) (fun _ _ completed => [completed])
    (by decide) (by decide) (by decide) selected evidence producers returns
  have queryRows := queried
  dsimp only [query] at queryRows
  simpa only [query, queryRows, prepared, request, answers, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.nil_append, List.cons_append] using derived

private theorem inputs_covered (index : Fin 2) :
    matchCovered 12 (.merge (candidate index).2 Bindings.empty) = true ∧
      ∀ merged ∈ mergeBindings (candidate index).2 Bindings.empty 12, merged.hasLoop = false →
        merged.applyFullCovered (candidate index).1 12 = true := by
  constructor
  · fin_cases index <;> decide +kernel
  · intro merged occurs acyclic
    have actual : mergeBindings (candidate index).2 Bindings.empty 12 = [bindings index] := by
      fin_cases index <;> decide +kernel
    rw [actual] at occurs
    obtain rfl := List.mem_singleton.mp occurs
    fin_cases index <;> decide +kernel

private theorem call_covered : call_admitted.Covered := by
  have covered := CallDerivation.Covered.equations
    (space := context) (comparison := .semantic)
    (ordinary := by decide) (nonembedded := by decide) (clean := by decide)
    (selected := selected) (evidence := evidence) (producers := producers) (bodies := returns)
    (productions := fun _ input => [(value, input.2)]) (outputs := fun _ _ completed => [completed])
    (by decide +kernel) (by
      intro selected member
      change selected ∈ equationCandidates context [] query Atom.symbolType Bindings.empty 12 at member
      rw [queried] at member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact inputs_covered 0
      · exact inputs_covered 1)
    (by
      intro selected member input present completed appeared
      obtain rfl := List.mem_singleton.mp appeared
      exact ReturnDerivation.Covered.evaluate
        (accepted := by decide) (running := by simp [value, IsEmptyOrErrorRel, IsErrorRel, Atom.empty])
        (child := .leaf [] value Atom.symbolType input.2 11
          (Or.inr ⟨Atom.symbolType, .symbol _, Or.inr (Or.inl rfl)⟩))
        (.leaf (leaf := Or.inr ⟨Atom.symbolType, .symbol _, Or.inr (Or.inl rfl)⟩)))
  have queryRows := queried
  dsimp only [query] at queryRows
  simpa only [query, queryRows, prepared, request, answers, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.nil_append, List.cons_append] using covered

/-- Candidate occurrence, matched input and completed producer occurrences
remain separate coordinates; repeated values do not collapse either rule. -/
theorem physical_occurrences_and_changed_bindings :
    context.atoms[0]? = some rule ∧ context.atoms[1]? = some rule ∧
    answers.length = 2 ∧ bindings 0 ≠ bindings 1 ∧
    (bindings 0).lookup "x#0" = some value ∧ (bindings 1).lookup "x#1" = some value ∧
    bindings 0 ≠ Bindings.empty ∧ bindings 1 ≠ Bindings.empty := by
  decide +kernel

theorem independent_function_equation_result (index : Fin 2) :
    ∃ output, CallRel context noHost [] query Atom.symbolType PrincipalBindingFrame.empty.sourceFrame
      (value, output) ∧ SourceBindingComparison.semantic.FrameRelated (bindings index) output := by
  exact call_admitted.sound (value, bindings index)
    (by fin_cases index <;> simp [answers]) PrincipalBindingFrame.empty.sourceFrame
    (.of_principal PrincipalBindingFrame.empty (.refl _))

theorem checked_function_equation_completion (earned : ResultSet) :
    ∃ budget, ∀ later, (FirstSuccessRecursiveExecution.Checked.machine HE.GroundedDispatch.none).run (budget + later)
      ⟨context, .work (.call query Atom.symbolType Bindings.empty 13 []), [], earned⟩ =
      (answers, .finished ⟨context, .returning [], [], earned ++ answers⟩) :=
  call_admitted.checked_completed call_covered earned

private def initial : Configuration :=
  ⟨context, .work (.call query Atom.symbolType Bindings.empty 13 []), [], []⟩
private def saved : Configuration :=
  ⟨context, .work (.primitive block (bindings 0) 11 [Atom.symbolType] (some query)),
    [.append (.productions 12 [request 1] [Atom.symbolType] (some query) .emitted),
      .invocationReturn (.ordinary Atom.symbolType) query 12 []], []⟩

/-- This exact paused configuration keeps the first reached binding, the
second physical producer occurrence and the ordinary return receiver. -/
theorem saved_after_query_before_body :
    (FirstSuccessRecursiveExecution.Checked.machine HE.GroundedDispatch.none).run 13 initial = ([], .exhausted saved) := by
  rfl

theorem saved_producer_resumes :
    ∃ budget remaining,
      (FirstSuccessRecursiveExecution.Checked.machine HE.GroundedDispatch.none).run budget saved =
        (remaining, .finished ⟨context, .returning [], [], answers⟩) ∧ remaining = answers := by
  simpa only [List.nil_append] using
    Covered.completes_saved (call_admitted.covered_realizes call_covered)
      [] 13 [] saved saved_after_query_before_body

end Mettapedia.Languages.MeTTa.HE.FirstSuccessSourceExecution.EquationProducerControls


namespace Mettapedia.Languages.MeTTa.HE.FirstSuccessSourceExecution.EquationNoReturnControls
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
open RecursiveTasks RecursiveMachine FirstSuccessRecursiveExecution
open Spec.Eval Spec.Type Spec.Type.Presentation Spec.Type.Presentation.Theory

private def query : Atom := .expression [.symbol "no-return"]
private def terminal : Atom := .expression [.symbol "Value"]
private def block : Atom := .expression [.symbol "function", terminal]
private def context : Space := Space.ofList [.expression [.symbol "=", query, block]]
private def error : Atom := Atom.error query (.symbol "NoReturn")
private def raw : ResultPair := (block, Bindings.empty)
private def replies : ResultSet := [(error, Bindings.empty)]

private theorem queried :
    equationCandidates context [] query Atom.symbolType Bindings.empty 12 = [raw] := by
  decide +kernel
private theorem prepared : equationInputs Bindings.empty 12 raw = [raw] := by decide +kernel

private theorem evidence :
    EquationBodyEvidence context [] query Atom.symbolType Bindings.empty raw raw .semantic := by
  apply EquationBodyEvidence.of_open_query_at (fuel := 12) 0 query block
  · rfl
  · decide +kernel
  · decide +kernel
  · rw [prepared]; exact List.mem_singleton_self _
  · decide +kernel

private theorem body :
    FunctionBodyDerivation (comparison := .semantic) context [block, Atom.symbolType]
      (some block) terminal Bindings.empty 10 [(terminal, Bindings.empty)] := by
  exact .run [block, Atom.symbolType] (some block) terminal Bindings.empty 9
    [(terminal, Bindings.empty)] (fun result => [result])
    (.data _ _ _ _ 8 rfl)
    (by intro result member; obtain rfl := List.mem_singleton.mp member; decide +kernel)
    (by intro result member instruction; obtain rfl := List.mem_singleton.mp member; rfl)
    (by intro result member instruction; obtain rfl := List.mem_singleton.mp member; contradiction)

private theorem produced :
    ProducedDerivation (comparison := .semantic) context [Atom.symbolType] (some query)
      block Bindings.empty 12 replies := by
  exact .function [Atom.symbolType] (some query) terminal Bindings.empty 11 _ rfl
    (.function [Atom.symbolType] (some query) [.symbol "Value"] Bindings.empty 10 _ body)

private theorem evidence_all : ∀ selected ∈ equationCandidates context [] query Atom.symbolType Bindings.empty 12,
    ∀ input ∈ equationInputs Bindings.empty 12 selected,
      EquationBodyEvidence context [] query Atom.symbolType Bindings.empty selected input .semantic := by
  intro selected member input present
  rw [queried] at member
  obtain rfl := List.mem_singleton.mp member
  rw [prepared] at present
  obtain rfl := List.mem_singleton.mp present
  exact evidence

private theorem producers : ∀ selected ∈ equationCandidates context [] query Atom.symbolType Bindings.empty 12,
    ∀ input ∈ equationInputs Bindings.empty 12 selected,
      ProducedDerivation (comparison := .semantic) context [Atom.symbolType] (some query)
        input.1 input.2 12 replies := by
  intro selected member input present
  rw [queried] at member
  obtain rfl := List.mem_singleton.mp member
  rw [prepared] at present
  obtain rfl := List.mem_singleton.mp present
  exact produced

private theorem stopped : IsEmptyOrErrorRel error := by
  simp [error, Atom.error, IsEmptyOrErrorRel, IsErrorRel]

private theorem returns : ∀ selected ∈ equationCandidates context [] query Atom.symbolType Bindings.empty 12,
    ∀ input ∈ equationInputs Bindings.empty 12 selected, ∀ completed ∈ replies,
      ReturnDerivation (comparison := .semantic) context [] query Atom.symbolType
        completed.1 completed.2 12 [completed] := by
  intro selected member input present completed appeared
  obtain rfl := List.mem_singleton.mp appeared
  exact .stopped [] query Atom.symbolType error Bindings.empty 12 stopped

/-- A function produced by an equation reports NoReturn at the invocation
that selected the equation, rather than at its wrapper or terminal body. -/
theorem call_admitted :
    CallDerivation (comparison := .semantic) context [] query Atom.symbolType Bindings.empty 13 replies := by
  have derived := CallDerivation.equations [] "no-return" [] Atom.symbolType Bindings.empty 12
    (fun _ _ => replies) (fun _ _ completed => [completed])
    (by decide) (by decide) (by decide)
    (by change rawQueryResults context query Atom.symbolType Bindings.empty 12 [] ≠ []; decide +kernel)
    evidence_all producers returns
  have queryRows := queried
  dsimp only [query] at queryRows
  simpa only [query, queryRows, prepared, replies, List.flatMap_cons, List.flatMap_nil, List.append_nil] using derived

private theorem call_covered : call_admitted.Covered := by
  have covered := CallDerivation.Covered.equations
    (space := context) (comparison := .semantic)
    (ordinary := by decide) (nonembedded := by decide) (clean := by decide)
    (selected := by change rawQueryResults context query Atom.symbolType Bindings.empty 12 [] ≠ []; decide +kernel)
    (evidence := evidence_all) (producers := producers) (bodies := returns)
    (productions := fun _ _ => replies) (outputs := fun _ _ completed => [completed])
    (by decide +kernel) (by
      intro selected member
      change selected ∈ equationCandidates context [] query Atom.symbolType Bindings.empty 12 at member
      rw [queried] at member
      obtain rfl := List.mem_singleton.mp member
      constructor
      · decide +kernel
      · intro merged present acyclic
        have same : merged = Bindings.empty := by
          simpa only [show mergeBindings raw.2 (aliasConstraints Bindings.empty) 12 = [Bindings.empty] from rfl,
            List.mem_singleton] using present
        subst merged
        decide +kernel)
    (by
      intro selected member input present completed appeared
      obtain rfl := List.mem_singleton.mp appeared
      exact ReturnDerivation.Covered.stopped (stopped := stopped))
  have queryRows := queried
  dsimp only [query] at queryRows
  simpa only [query, queryRows, prepared, replies, List.flatMap_cons, List.flatMap_nil, List.append_nil] using covered

theorem independent_original_caller :
    ∃ output, CallRel context noHost [] query Atom.symbolType PrincipalBindingFrame.empty.sourceFrame
      (error, output) ∧ SourceBindingComparison.semantic.FrameRelated Bindings.empty output :=
  call_admitted.sound (error, Bindings.empty) (by simp [replies])
    PrincipalBindingFrame.empty.sourceFrame
    (.of_principal PrincipalBindingFrame.empty (.refl _))

theorem checked_original_caller (earned : ResultSet) :
    ∃ budget, ∀ later, (FirstSuccessRecursiveExecution.Checked.machine HE.GroundedDispatch.none).run (budget + later)
      ⟨context, .work (.call query Atom.symbolType Bindings.empty 13 []), [], earned⟩ =
      (replies, .finished ⟨context, .returning [], [], earned ++ replies⟩) :=
  call_admitted.checked_completed call_covered earned

theorem neither_wrapper_nor_terminal_is_error_subject :
    error ≠ Atom.error block (.symbol "NoReturn") ∧
    error ≠ Atom.error terminal (.symbol "NoReturn") := by decide +kernel

end Mettapedia.Languages.MeTTa.HE.FirstSuccessSourceExecution.EquationNoReturnControls


namespace Mettapedia.Languages.MeTTa.HE.FirstSuccessSourceExecution
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open RecursiveTasks RecursiveMachine FirstSuccessRecursiveExecution
open Spec.Eval

/-- Local raw-invocation admissions earn a completed checked run, including
the complete occurrence list and the already published caller prefix. -/
theorem RawInvocationDerivation.checked_completed {space : Space} {live : List Atom}
    {caller : Option Atom} {value : Atom} {incoming : Bindings} {fuel : Nat} {results : ResultSet}
    (derived : RawInvocationDerivation space .semantic live caller value incoming fuel results)
    (earned : ResultSet) :
    ∃ budget, ∀ later, (FirstSuccessRecursiveExecution.Checked.machine HE.GroundedDispatch.none).run (budget + later)
      ⟨space, .work (.invocation .raw value incoming fuel live caller), [], earned⟩ =
      (results, .finished ⟨space, .returning [], [], earned ++ results⟩) :=
  Covered.realizes_completed derived.covered_realizes earned

/-- Any completed budget has the same raw rows and final retained history.
This is reflection for the admitted request, not a completeness assertion for
all possible independent representative choices. -/
theorem RawInvocationDerivation.checked_completed_unique {space : Space} {live : List Atom}
    {caller : Option Atom} {value : Atom} {incoming : Bindings} {fuel : Nat} {results : ResultSet}
    (derived : RawInvocationDerivation space .semantic live caller value incoming fuel results)
    (earned actual : ResultSet) (budget : Nat) (finished : Configuration)
    (ran : (FirstSuccessRecursiveExecution.Checked.machine HE.GroundedDispatch.none).run budget
      ⟨space, .work (.invocation .raw value incoming fuel live caller), [], earned⟩ =
      (actual, .finished finished)) :
    actual = results ∧ finished = ⟨space, .returning [], [], earned ++ results⟩ :=
  realizes_completed_unique (Covered.unchecked derived.covered_realizes) earned actual budget finished
    (FirstSuccessRecursiveExecution.Checked.finished_refines HE.GroundedDispatch.none budget _ actual finished ran)

/-- Every completed physical raw result carries its independent invocation
witness at the same caller, live scope and reached selected binding frame. -/
theorem RawInvocationDerivation.checked_completed_sound {space : Space} {live : List Atom}
    {caller : Option Atom} {value : Atom} {incoming : Bindings} {fuel : Nat} {results : ResultSet}
    (derived : RawInvocationDerivation space .semantic live caller value incoming fuel results)
    (earned actual : ResultSet) (budget : Nat) (finished : Configuration)
    (ran : (FirstSuccessRecursiveExecution.Checked.machine HE.GroundedDispatch.none).run budget
      ⟨space, .work (.invocation .raw value incoming fuel live caller), [], earned⟩ =
      (actual, .finished finished))
    (input : BindingFrame) (related : SourceBindingComparison.semantic.FrameRelated incoming input) :
    ∀ result ∈ actual, ∃ output,
      Minimal.CoreInvocationRel space noHost live (caller := caller) value input (result.1, output) ∧
      SourceBindingComparison.semantic.FrameRelated result.2 output := by
  have same := (derived.checked_completed_unique earned actual budget finished ran).1
  intro result member
  exact derived.sound result (same ▸ member) input related

/-- The complete retained stack, child work and already delivered occurrence
prefix survive an actual scheduler pause; the suffix bound is constructed. -/
theorem RawInvocationDerivation.checked_resumes {space : Space} {live : List Atom}
    {caller : Option Atom} {value : Atom} {incoming : Bindings} {fuel : Nat} {results : ResultSet}
    (derived : RawInvocationDerivation space .semantic live caller value incoming fuel results)
    (earned : ResultSet) (first : Nat) (before : ResultSet) (saved : Configuration)
    (paused : (FirstSuccessRecursiveExecution.Checked.machine HE.GroundedDispatch.none).run first
      ⟨space, .work (.invocation .raw value incoming fuel live caller), [], earned⟩ =
      (before, .exhausted saved)) :
    ∃ budget after, (FirstSuccessRecursiveExecution.Checked.machine HE.GroundedDispatch.none).run budget saved =
      (after, .finished ⟨space, .returning [], [], earned ++ results⟩) ∧ before ++ after = results :=
  Covered.completes_saved derived.covered_realizes earned first before saved paused

theorem MinimalDerivation.checked_completed {space : Space} {live : List Atom}
    {caller : Option Atom} {value : Atom} {incoming : Bindings} {fuel : Nat} {results : ResultSet}
    (derived : MinimalDerivation space .semantic live caller value incoming fuel results)
    (earned : ResultSet) :
    ∃ budget, ∀ later, (FirstSuccessRecursiveExecution.Checked.machine HE.GroundedDispatch.none).run (budget + later)
      ⟨space, .work (.minimal value incoming fuel live caller), [], earned⟩ =
      (results, .finished ⟨space, .returning [], [], earned ++ results⟩) :=
  Covered.realizes_completed derived.covered_realizes earned

end Mettapedia.Languages.MeTTa.HE.FirstSuccessSourceExecution


namespace Mettapedia.Languages.MeTTa.HE.FirstSuccessSourceExecution.RawChainControls
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open RecursiveTasks RecursiveMachine FirstSuccessRecursiveExecution
open Spec.Eval Spec.Eval.Steps Spec.Type Spec.Type.Presentation Spec.Type.Presentation.Theory
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

def value : Atom := .symbol "Value"
def query : Atom := .expression [.symbol "supply", value]
def pattern : Atom := .expression [.symbol "supply", .var "x"]
def sourceBody : Atom := .expression [.symbol "function", .expression [.symbol "return", .var "x"]]
def rule : Atom := .expression [.symbol "=", pattern, sourceBody]
def context : Space := Space.ofList [rule, rule]
def returned : Atom := .expression [.symbol "return", value]
def block : Atom := .expression [.symbol "function", returned]
def key (index : Fin 2) : String := "x#" ++ Nat.repr index.val
def bindings (index : Fin 2) : Bindings := Bindings.empty.assign (key index) value
def candidate (index : Fin 2) : ResultPair :=
  (.expression [.symbol "function", .expression [.symbol "return", .var (key index)]], bindings index)
def request (index : Fin 2) : ResultPair := (block, bindings index)
def headRows : ResultSet := [(value, bindings 0), (value, bindings 1)]
def evalQuery : Atom := .expression [.symbol "eval", query]
def template : Atom := .expression [.symbol "return", .expression [.symbol "Pair", .var "r", .var "r"]]
def chain : Atom := .expression [.symbol "chain", evalQuery, .var "r", template]
def outer : Atom := .expression [.symbol "function", chain]
def liveScope : List Atom := [chain, outer]
def pair : Atom := .expression [.symbol "Pair", value, value]
def terminal : Atom := .expression [.symbol "return", pair]
def terminals : ResultSet := [(terminal, bindings 0), (terminal, bindings 1)]
def answers : ResultSet := [(pair, bindings 0), (pair, bindings 1)]

theorem queried : equationCandidates context liveScope query Atom.undefinedType Bindings.empty 12 =
    [candidate 0, candidate 1] := by decide +kernel
theorem prepared (index : Fin 2) : equationInputs Bindings.empty 12 (candidate index) =
    [request index] := by fin_cases index <;> decide +kernel

theorem occurrence_evidence (index : Fin 2) :
    EquationBodyEvidence context liveScope query Atom.undefinedType Bindings.empty
      (candidate index) (request index) .semantic := by
  apply EquationBodyEvidence.of_open_query_at (fuel := 12) index.val pattern sourceBody
  · fin_cases index <;> decide +kernel
  · fin_cases index <;> decide +kernel
  · fin_cases index <;> decide +kernel
  · rw [prepared]; exact List.mem_singleton_self _
  · fin_cases index <;> decide +kernel

theorem producer (index : Fin 2) :
    ProducedDerivation context .semantic liveScope (some query) block (bindings index) 12
      [(value, bindings index)] := by
  apply ProducedDerivation.function liveScope (some query) returned (bindings index) 11 _ rfl
  apply PrimitiveDerivation.function liveScope (some query) [.symbol "return", value] (bindings index) 10
    [(returned, bindings index)]
  exact .run (block :: liveScope) (some block) returned (bindings index) 9
    [(returned, bindings index)] (fun result => [result])
    (.data _ _ _ _ 8 rfl)
    (by intro result member; obtain rfl := List.mem_singleton.mp member
        fin_cases index <;> decide +kernel)
    (by intro result member instruction; obtain rfl := List.mem_singleton.mp member
        fin_cases index <;> decide +kernel)
    (by intro result member instruction; obtain rfl := List.mem_singleton.mp member
        fin_cases index <;> contradiction)

theorem input_covered (index : Fin 2) :
    matchCovered 12 (.merge (candidate index).2 Bindings.empty) = true ∧
      ∀ merged ∈ mergeBindings (candidate index).2 Bindings.empty 12, merged.hasLoop = false →
        merged.applyFullCovered (candidate index).1 12 = true := by
  constructor
  · fin_cases index <;> decide +kernel
  · intro merged present acyclic
    have actual : mergeBindings (candidate index).2 Bindings.empty 12 = [bindings index] := by
      fin_cases index <;> decide +kernel
    rw [actual] at present
    obtain rfl := List.mem_singleton.mp present
    fin_cases index <;> decide +kernel

theorem raw_query_admitted : RawInvocationDerivation context .semantic liveScope (some chain)
    query Bindings.empty 13 headRows := by
  have derived := RawInvocationDerivation.equations (space := context) (comparison := .semantic)
    liveScope (some chain) "supply" [value] Bindings.empty 12
    (fun _ input => [(value, input.2)])
    (by decide +kernel) (by decide +kernel) (by
      intro selected member
      change selected ∈ equationCandidates context liveScope query Atom.undefinedType Bindings.empty 12 at member
      rw [queried] at member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact input_covered 0
      · exact input_covered 1)
    (by change rawQueryResults context query Atom.undefinedType Bindings.empty 12 liveScope ≠ []; decide +kernel)
    (by
      intro selected member input present
      change selected ∈ equationCandidates context liveScope query Atom.undefinedType Bindings.empty 12 at member
      rw [queried] at member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      all_goals
        rw [prepared] at present
        obtain rfl := List.mem_singleton.mp present
        exact occurrence_evidence _)
    (by
      intro selected member input present
      change selected ∈ equationCandidates context liveScope query Atom.undefinedType Bindings.empty 12 at member
      rw [queried] at member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      all_goals
        rw [prepared] at present
        obtain rfl := List.mem_singleton.mp present
        exact producer _)
  have rows := queried
  dsimp only [query] at rows
  simpa only [query, rows, prepared, request, headRows,
    List.flatMap_cons, List.flatMap_nil, List.append_nil, List.nil_append, List.cons_append] using derived

theorem eval_query_admitted : MinimalDerivation context .semantic liveScope (some chain)
    evalQuery Bindings.empty 15 headRows :=
  .instruction liveScope (some chain) evalQuery Bindings.empty 14 headRows rfl
    (by simp [Minimal.IsChain, evalQuery])
    (.eval liveScope (some chain) query Bindings.empty 13 headRows (by decide +kernel) raw_query_admitted)

theorem chain_step : PrimitiveDerivation context .semantic [outer] (some outer)
    chain Bindings.empty 16 terminals := by
  have child := PrimitiveDerivation.chain [outer] (some outer) evalQuery "r" template Bindings.empty 15
    headRows eval_query_admitted (by
      intro result member
      simp only [headRows, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl <;> decide +kernel)
  have rows : (headRows.map fun result =>
      (chainSubstitute "r" (result.2.applyFull result.1 15) template, result.2)) = terminals := by decide +kernel
  exact rows ▸ child

theorem chain_admitted : MinimalDerivation context .semantic [outer] (some outer)
    chain Bindings.empty 17 terminals := by
  have continued := MinimalDerivation.chain [outer] (some outer) evalQuery "r" template Bindings.empty 16
    terminals (fun result => [result]) chain_step (by
      intro result member
      simp only [terminals, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      all_goals exact .data _ _ _ _ 15 rfl)
  simpa only [chain, terminals, List.flatMap_cons, List.flatMap_nil, List.singleton_append] using continued

theorem outer_body : FunctionBodyDerivation context .semantic [outer] (some outer)
    chain Bindings.empty 18 terminals := by
  have body := FunctionBodyDerivation.run [outer] (some outer) chain Bindings.empty 17
    terminals (fun result => [result]) chain_admitted (by
      intro result member
      simp only [terminals, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl <;> decide +kernel) (by
      intro result member instruction
      simp only [terminals, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl <;> decide +kernel) (by
      intro result member instruction
      simp only [terminals, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl <;> contradiction)
  simpa only [terminals, List.flatMap_cons, List.flatMap_nil, List.singleton_append] using body

theorem outer_primitive : PrimitiveDerivation context .semantic [] none outer Bindings.empty 19 answers := by
  have body := PrimitiveDerivation.function [] none [.symbol "chain", evalQuery, .var "r", template]
    Bindings.empty 18 terminals outer_body
  exact (show (terminals.map fun result => (functionTerminal none result.1, result.2)) = answers by rfl) ▸ body

theorem outer_raw : RawInvocationDerivation context .semantic [] none outer Bindings.empty 21 answers :=
  .embedded [] none "function" [chain] Bindings.empty 20 answers rfl
    (.instruction [] none outer Bindings.empty 19 answers rfl (by simp [Minimal.IsChain, outer]) outer_primitive)

theorem actual_nested_source (index : Fin 2) :
    ∃ output, Minimal.CoreInvocationRel context noHost [] outer PrincipalBindingFrame.empty.sourceFrame
      (pair, output) ∧ SourceBindingComparison.semantic.FrameRelated (bindings index) output :=
  outer_raw.sound (pair, bindings index) (by fin_cases index <;> simp [answers])
    PrincipalBindingFrame.empty.sourceFrame
    (.of_principal PrincipalBindingFrame.empty (.refl _))

theorem actual_nested_completion (earned : ResultSet) :
    ∃ budget, ∀ later, (FirstSuccessRecursiveExecution.Checked.machine HE.GroundedDispatch.none).run (budget + later)
      ⟨context, .work (.invocation .raw outer Bindings.empty 21 [] none), [], earned⟩ =
      (answers, .finished ⟨context, .returning [], [], earned ++ answers⟩) :=
  Covered.realizes_completed outer_raw.covered_realizes earned

theorem duplicates_and_bindings : answers.length = 2 ∧ bindings 0 ≠ bindings 1 ∧
    (bindings 0).lookup "x#0" = some value ∧ (bindings 1).lookup "x#1" = some value ∧
    answers ≠ [(pair, Bindings.empty)] := by decide +kernel

def initial : Configuration := ⟨context, .work (.invocation .raw outer Bindings.empty 21 [] none), [], []⟩

theorem no_depth_is_suspension :
    (FirstSuccessRecursiveExecution.Checked.machine HE.GroundedDispatch.none).run 2
      ⟨context, .work (.invocation .raw outer Bindings.empty 0 [] none), [], []⟩ =
      ([], .suspended .evaluationDepth
        ⟨context, .work (.invocation .raw outer Bindings.empty 0 [] none), [], []⟩) := rfl

def saved : Configuration :=
  ⟨context, .work (.primitive block (bindings 0) 11 liveScope (some query)),
    [.append (.productions 12 [request 1] liveScope (some query) .emitted),
      .invocationReturn .raw query 12 liveScope,
      .chainResults "r" template 15,
      .minimalResults 16 [outer] (some outer),
      .bodyResults 17 [outer] (some outer),
      .functionTerminal none,
      .invocationReturn .raw outer 20 []], []⟩

/-- The first equation body is active while the second physical equation,
raw receiver, repeated-variable chain template and enclosing function wait. -/
theorem actual_saved_checkpoint :
    (FirstSuccessRecursiveExecution.Checked.machine HE.GroundedDispatch.none).run 20 initial =
      ([], .exhausted saved) := by rfl

theorem saved_retains_both_uses :
    Frame.chainResults "r" template 15 ∈ saved.stack ∧
      template = .expression [.symbol "return", .expression [.symbol "Pair", .var "r", .var "r"]] ∧
      saved.control = .work (.primitive block (bindings 0) 11 liveScope (some query)) ∧
      Frame.append (.productions 12 [request 1] liveScope (some query) .emitted) ∈ saved.stack := by
  decide +kernel

theorem saved_resumes :
    ∃ budget remaining,
      (FirstSuccessRecursiveExecution.Checked.machine HE.GroundedDispatch.none).run budget saved =
        (remaining, .finished ⟨context, .returning [], [], answers⟩) ∧ remaining = answers := by
  simpa only [List.nil_append] using
    Covered.completes_saved outer_raw.covered_realizes [] 20 [] saved actual_saved_checkpoint

theorem shallow_does_not_finish_empty :
    (FirstSuccessRecursiveExecution.Checked.machine HE.GroundedDispatch.none).run 20 initial ≠
      ([], .finished saved) := by rw [actual_saved_checkpoint]; intro equal; cases equal

end Mettapedia.Languages.MeTTa.HE.FirstSuccessSourceExecution.RawChainControls


namespace Mettapedia.Languages.MeTTa.HE.FirstSuccessSourceExecution.RawChainBoundaryControls
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open RecursiveTasks RecursiveMachine FirstSuccessRecursiveExecution
open Spec.Eval Spec.Eval.Steps Spec.Type Spec.Type.Presentation
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

def query : Atom := .expression [.symbol "missing"]
def evalQuery : Atom := .expression [.symbol "eval", query]
def template : Atom := .expression [.symbol "Seen", .var "r"]
def chain : Atom := .expression [.symbol "chain", evalQuery, .var "r", template]
def refusal : Atom := .expression [.symbol "Seen", Atom.notReducible]

theorem absent (live : List Atom) : EquationQueryNoMatchRel Space.empty live query Bindings.empty := by
  rintro left right matched ⟨rawLeft, rawRight, stored, _⟩
  simp [Space.empty] at stored

theorem refused (live : List Atom) (caller : Option Atom) :
    RawInvocationDerivation Space.empty .semantic live caller query Bindings.empty 5
      [(Atom.notReducible, Bindings.empty)] :=
  .unreduced live caller "missing" [] Bindings.empty 4 rfl
    (by rfl)
    (by simp [equationCandidates, queryEquationsAvoiding, Space.empty]) (absent live)

theorem raw_refusal_source :
    ∃ output, Minimal.CoreInvocationRel Space.empty noHost [] query PrincipalBindingFrame.empty.sourceFrame
      (Atom.notReducible, output) ∧ SourceBindingComparison.semantic.FrameRelated Bindings.empty output :=
  (refused [] none).sound (Atom.notReducible, Bindings.empty) (by simp)
    PrincipalBindingFrame.empty.sourceFrame
    (.of_principal PrincipalBindingFrame.empty (.refl _))

theorem ordinary_restores : CallDerivation Space.empty .semantic [] query Atom.atomType Bindings.empty 5
    [(query, Bindings.empty)] :=
  .unreduced [] "missing" [] Atom.atomType Bindings.empty 4 (by decide) rfl (by decide)
    (by simp [equationCandidates, queryEquationsAvoiding, Space.empty]) (absent _)

theorem raw_refusal_is_not_ordinary_return :
    [(Atom.notReducible, Bindings.empty)] ≠ [(query, Bindings.empty)] := by decide +kernel

theorem eval_refusal : MinimalDerivation Space.empty .semantic [chain] (some chain)
    evalQuery Bindings.empty 7 [(Atom.notReducible, Bindings.empty)] :=
  .instruction [chain] (some chain) evalQuery Bindings.empty 6 _ rfl
    (by simp [Minimal.IsChain, evalQuery])
    (.eval [chain] (some chain) query Bindings.empty 5 _ (by decide +kernel) (refused _ _))

theorem refusal_chain : MinimalDerivation Space.empty .semantic [] none chain Bindings.empty 9
    [(refusal, Bindings.empty)] := by
  have child := PrimitiveDerivation.chain [] none evalQuery "r" template Bindings.empty 7
    [(Atom.notReducible, Bindings.empty)] eval_refusal
    (by intro result member; obtain rfl := List.mem_singleton.mp member; decide +kernel)
  have actual : ([(Atom.notReducible, Bindings.empty)].map fun result =>
      (chainSubstitute "r" (result.2.applyFull result.1 7) template, result.2)) =
      [(refusal, Bindings.empty)] := by decide +kernel
  have run := MinimalDerivation.chain [] none evalQuery "r" template Bindings.empty 8
    [(refusal, Bindings.empty)] (fun result => [result]) (actual ▸ child)
    (by intro result member; obtain rfl := List.mem_singleton.mp member; exact .data _ _ _ _ 7 rfl)
  simpa only [chain, List.flatMap_cons, List.flatMap_nil, List.singleton_append] using run

def mismatch : Atom := .expression [.symbol "unify", .symbol "A", .symbol "B", .symbol "Yes", Atom.empty]
def emptyChain : Atom := .expression [.symbol "chain", mismatch, .var "r", template]
def seenEmpty : Atom := .expression [.symbol "Seen", Atom.empty]

theorem unmatched : MinimalDerivation Space.empty .semantic [emptyChain] (some emptyChain)
    mismatch Bindings.empty 7 [(Atom.empty, Bindings.empty)] :=
  .instruction [emptyChain] (some emptyChain) mismatch Bindings.empty 6 _ rfl
    (by simp [Minimal.IsChain, mismatch])
    (.unifyNoMatch [emptyChain] (some emptyChain) (.symbol "A") (.symbol "B") (.symbol "Yes") Atom.empty
      Bindings.empty 5 (by decide +kernel) (by decide +kernel))

theorem internal_empty_chain : MinimalDerivation Space.empty .semantic [] none emptyChain Bindings.empty 9
    [(seenEmpty, Bindings.empty)] := by
  have child := PrimitiveDerivation.chain [] none mismatch "r" template Bindings.empty 7
    [(Atom.empty, Bindings.empty)] unmatched
    (by intro result member; obtain rfl := List.mem_singleton.mp member; decide +kernel)
  have actual : ([(Atom.empty, Bindings.empty)].map fun result =>
      (chainSubstitute "r" (result.2.applyFull result.1 7) template, result.2)) =
      [(seenEmpty, Bindings.empty)] := by decide +kernel
  have run := MinimalDerivation.chain [] none mismatch "r" template Bindings.empty 8
    [(seenEmpty, Bindings.empty)] (fun result => [result]) (actual ▸ child)
    (by intro result member; obtain rfl := List.mem_singleton.mp member; exact .data _ _ _ _ 7 rfl)
  simpa only [emptyChain, List.flatMap_cons, List.flatMap_nil, List.singleton_append] using run

theorem sentinel_continuations_are_not_empty_answers :
    [(refusal, Bindings.empty)] ≠ ([] : ResultSet) ∧
    [(seenEmpty, Bindings.empty)] ≠ ([] : ResultSet) := by decide +kernel

theorem source_keeps_internal_empty :
    ∃ output, Minimal.CoreRunRel Space.empty noHost [] emptyChain PrincipalBindingFrame.empty.sourceFrame
      (seenEmpty, output) ∧ SourceBindingComparison.semantic.FrameRelated Bindings.empty output :=
  internal_empty_chain.sound (seenEmpty, Bindings.empty) (by simp)
    PrincipalBindingFrame.empty.sourceFrame
    (.of_principal PrincipalBindingFrame.empty (.refl _))

theorem checked_empty_continuation :
    Covered.Realizes Space.empty (.minimal emptyChain Bindings.empty 9 [] none) [(seenEmpty, Bindings.empty)] :=
  internal_empty_chain.covered_realizes

end Mettapedia.Languages.MeTTa.HE.FirstSuccessSourceExecution.RawChainBoundaryControls


namespace Mettapedia.Languages.MeTTa.HE.FirstSuccessSourceExecution.ChangedChainControls
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open RecursiveTasks FirstSuccessRecursiveExecution
open Spec.Eval Spec.Type.RuntimeRefinement
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

def value : Atom := .symbol "Value"
def bindings : Bindings := Bindings.empty.assign "public" value
def pending : Atom := .expression [.symbol "return", .expression [.symbol "Pair", .var "public", .var "public"]]
def answer : Atom := .expression [.symbol "Pair", value, value]
def returned : Atom := .expression [.symbol "return", answer]
def written : Atom := .expression [.symbol "unify", value, .var "public", .symbol "ok", .symbol "Miss"]
def chain : Atom := .expression [.symbol "chain", written, .var "ignored", pending]
def block : Atom := .expression [.symbol "function", chain]
def original : Atom := .expression [.symbol "outer", .var "public"]

theorem write_admitted : PrimitiveDerivation Space.empty .semantic [chain, block] (some chain)
    written Bindings.empty 10 [(.symbol "ok", bindings)] := by
  have selected : unifySuccessResults value (.var "public") (.symbol "ok") Bindings.empty 9 =
      [(.symbol "ok", bindings)] := by decide +kernel
  have derived := PrimitiveDerivation.unifySuccess (space := Space.empty) (comparison := .semantic)
    [chain, block] (some chain) value (.var "public") (.symbol "ok") (.symbol "Miss") Bindings.empty 9
    (by decide +kernel) (by rw [selected]; simp)
  simpa only [written, selected] using derived

theorem chain_step : PrimitiveDerivation Space.empty .semantic [block] (some block)
    chain Bindings.empty 12 [(pending, bindings)] := by
  have write : MinimalDerivation Space.empty .semantic [chain, block] (some chain)
      written Bindings.empty 11 [(.symbol "ok", bindings)] :=
    .instruction [chain, block] (some chain) written Bindings.empty 10 _ rfl
      (by simp [Minimal.IsChain, written]) write_admitted
  have result := PrimitiveDerivation.chain [block] (some block) written "ignored" pending Bindings.empty 11
    [(.symbol "ok", bindings)] write
    (by intro result member; obtain rfl := List.mem_singleton.mp member; decide +kernel)
  exact (show ([((.symbol "ok" : Atom), bindings)].map fun result =>
    (chainSubstitute "ignored" (result.2.applyFull result.1 11) pending, result.2)) =
      [(pending, bindings)] by decide +kernel) ▸ result

theorem chain_run : MinimalDerivation Space.empty .semantic [block] (some block)
    chain Bindings.empty 13 [(pending, bindings)] := by
  have result := MinimalDerivation.chain [block] (some block) written "ignored" pending Bindings.empty 12
    [(pending, bindings)] (fun result => [result]) chain_step
    (by intro result member; obtain rfl := List.mem_singleton.mp member; exact .data _ _ _ _ 11 rfl)
  simpa only [chain, List.flatMap_cons, List.flatMap_nil, List.singleton_append] using result

theorem body_admitted : FunctionBodyDerivation Space.empty .semantic [block] (some block)
    chain Bindings.empty 14 [(returned, bindings)] := by
  have result := FunctionBodyDerivation.run [block] (some block) chain Bindings.empty 13
    [(pending, bindings)] (fun result => [(returned, result.2)]) chain_run
    (by intro result member; obtain rfl := List.mem_singleton.mp member; decide +kernel)
    (by intro result member instruction; obtain rfl := List.mem_singleton.mp member; decide +kernel)
    (by intro result member instruction; obtain rfl := List.mem_singleton.mp member; contradiction)
  simpa only [List.flatMap_cons, List.flatMap_nil, List.singleton_append] using result

theorem function_admitted : PrimitiveDerivation Space.empty .semantic [] (some original)
    block Bindings.empty 15 [(answer, bindings)] :=
  .function [] (some original) [.symbol "chain", written, .var "ignored", pending] Bindings.empty 14
    [(returned, bindings)] body_admitted

theorem source_reads_both_pending_uses :
    ∃ output, Minimal.CoreStepRel Space.empty noHost [] (caller := some original)
      block PrincipalBindingFrame.empty.sourceFrame (answer, output) ∧
      SourceBindingComparison.semantic.FrameRelated bindings output ∧
      BindingFrame.Materialization output pending returned := by
  obtain ⟨output, source, related⟩ := function_admitted.sound (answer, bindings) (by simp)
    PrincipalBindingFrame.empty.sourceFrame
    (.of_principal PrincipalBindingFrame.empty (.refl _))
  exact ⟨output, source, related, related.materialization pending 13 (by decide +kernel)⟩

theorem actual_write_keeps_chain_destination_structural :
    bindings.lookup "public" = some value ∧ bindings.lookup "ignored" = none ∧
    bindings ≠ Bindings.empty ∧ pending ≠ returned := by decide +kernel

theorem checked_changed_frame :
    Covered.Realizes Space.empty (.primitive block Bindings.empty 15 [] (some original)) [(answer, bindings)] :=
  function_admitted.covered_realizes

end Mettapedia.Languages.MeTTa.HE.FirstSuccessSourceExecution.ChangedChainControls


namespace Mettapedia.Languages.MeTTa.HE.FirstSuccessSourceExecution

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Spec.Eval Spec.Eval.Steps Spec.Bindings.ScopeObservation
open Spec.Type Spec.Type.Presentation Spec.Type.Presentation.BindingTheory
open Spec.Type.RuntimeRefinement

namespace AliasUnifyControls

open QueryBindingProjection.AliasReadout
open QueryBindingProjection.AliasReadout.Controls

/-- The repaired local operation and the independent primitive both accept
the certified crossed-alias caller that the former worker rejects. -/
theorem crossed_aliases_have_source_step
    (space : Space) (dispatch : Spec.Eval.GroundedDispatch) (live : List Atom)
    (typing : EvalTypeService) (caller : Option Atom) :
    ∃ certificate : ReadoutCertificate output (QueryBindingProjection.nativeReadoutPresentation output),
      Minimal.CoreStepRel space dispatch live
        (.expression [.symbol "unify", target, pattern, pending, .symbol "No"])
        (BindingFrame.selected incoming oldTable input_certificate)
        ((QueryBindingProjection.nativeReadoutPresentation output).apply pending,
          BindingFrame.selected output (QueryBindingProjection.nativeReadoutPresentation output)
            certificate) (typing := typing) (caller := caller) := by
  obtain ⟨certificate, _candidate, _updated, stepped, _reads, _pending⟩ :=
    alias_unify_selected_source_step (thenBranch := pending) (elseBranch := .symbol "No")
      (BindingSourceAgreement.refl _) input_certificate actual_occurrence
      space dispatch live typing caller
  exact ⟨certificate, stepped⟩

/-- An empty budget-limited discovery is not evidence of logical refusal. -/
theorem zero_depth_is_not_completed_refusal :
    unifyReadouts target pattern incoming 0 = [] ∧
      ¬UnifyNoMatchRel target pattern incoming := by
  refine ⟨by decide +kernel, ?_⟩
  intro absent
  exact absent output (alias_unify_source_candidate
    (BindingSourceAgreement.refl _) actual_occurrence)

end AliasUnifyControls

end Mettapedia.Languages.MeTTa.HE.FirstSuccessSourceExecution


namespace Mettapedia.Languages.MeTTa.HE.FreshPrivateMerge
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Spec.Type.Presentation Spec.Type.Presentation.Theory Spec.Type.RuntimeRefinement
open Spec.Bindings.ScopeObservation FirstSuccessSourceExecution
namespace Controls
open FirstSuccessSourceExecution.AliasMergeControls

theorem freshFrame : FirstSuccessSourceExecution.ClosedBindingFrame fresh :=
  (closed_target_runtime_match_source (target := .symbol "B")
    (pattern := .var "private") (fuel := 50) (by rfl)
    (by rw [closed_fresh_match]; simp)).2

/-- Duplicate caller edges may be added by real reconciliation, while all
private readouts—including a repeated residual hole—remain exact together. -/
theorem private_readout_all_budgets (fuel : Nat) :
    let body := Atom.expression [.symbol "pair", .var "private", .var "hole", .var "hole"]
    actual.applyFull body fuel = fresh.applyFull body fuel := by
  apply merge_closed_materialization freshFrame _ ?_
    (by rw [lean_merge_result]; simp) fuel
  intro key present
  simp [TypeSubst.typeVars,TypeSubst.typeVarsList] at present
  rcases present with rfl | rfl <;> decide

theorem source_alias_endpoint :
    Spec.Match.Merge.MergeRel Spec.Match.Merge.equalityGroundedSemantic reconciled fresh
      ⟨reconciled.assignments ++ fresh.assignments,reconciled.equalities⟩ :=
  closed_source_merge freshFrame (by intro key present; simp only [fresh,List.map_cons,
    List.map_nil,List.mem_singleton] at present; subst key; exact outside_caller)

/-- Omitting a residual hole from the protected scope really permits capture. -/
example :
    let matched := Bindings.empty.assign "private" (.symbol "B")
    let caller := Bindings.empty.assign "hole" (.symbol "A")
    let body := Atom.expression [.var "private", .var "hole", .var "hole"]
    let output := (mergeBindings matched caller 20).head!
    output.applyFull body 20 ≠ matched.applyFull body 20 := by decide

/-- Reconciliation does not grant a conflicting caller assignment ownership
of a protected private key: the actual merge has no successful branch. -/
example : mergeBindings fresh (Bindings.empty.assign "private" (.symbol "A")) 20 = [] := by
  decide
end Controls
end Mettapedia.Languages.MeTTa.HE.FreshPrivateMerge


/-! ## Constructed open-query admission and selected renewal -/

namespace Mettapedia.Languages.MeTTa.HE.FirstSuccessSourceExecution
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open RecursiveTasks RecursiveMachine
open Spec.Eval Spec.Eval.Steps Spec.Type.Presentation Spec.Type.Presentation.Theory
open Spec.Type.Presentation.BindingTheory Spec.Type.RuntimeRefinement
open Spec.Bindings.ScopeObservation Spec.Match.ModelTheory QueryBindingProjection

/-- A covered query input earns its RHS read from the actual surviving merge.
The caller need not supply an expected body value or a source correspondence. -/
theorem equationInputs_readCovered {incoming : Bindings} {candidate request : ResultPair}
    {fuel : Nat}
    (covered : ∀ merged ∈ mergeBindings candidate.2 (aliasConstraints incoming) fuel,
      merged.hasLoop = false → merged.applyFullCovered candidate.1 fuel = true)
    (present : request ∈ equationInputs incoming fuel candidate) :
    request.2.applyFullCovered candidate.1 fuel = true := by
  obtain ⟨merged, member, selected⟩ := List.mem_filterMap.mp present
  split at selected
  · simp at selected
  · rename_i acyclic
    have pair : (merged.applyFull candidate.1 fuel, merged) = request := Option.some.inj selected
    cases pair
    exact covered merged member (by simpa using acyclic)

/-- Local readiness constructs independent equation evidence for an actual
open query row. Every caller constraint is reconciled before the RHS is read. -/
theorem EquationBodyEvidence.of_covered_query_hit
    {space : Space} {live : List Atom} {query expected : Atom} {incoming : Bindings}
    {candidate request : ResultPair} {fuel : Nat}
    (hit : candidate ∈ equationCandidates space live query expected incoming fuel)
    (covered : ∀ merged ∈ mergeBindings candidate.2 (aliasConstraints incoming) fuel,
      merged.hasLoop = false → merged.applyFullCovered candidate.1 fuel = true)
    (present : request ∈ equationInputs incoming fuel candidate) :
    EquationBodyEvidence space live query expected incoming candidate request .semantic :=
  .of_open_query_hit hit present (equationInputs_readCovered covered present)

/-- One physical query occurrence earns a selected frame and renewal of the
chosen source input. Its computed table absorbs the old table simultaneously
on the entire pending tuple; no residual representative is chosen per operand. -/
theorem equationInput_selected_source_at
    {space : Space} {live : List Atom} {query expected : Atom}
    {incoming independent : Bindings} {oldTable : TypeSubst}
    {candidate request : ResultPair} {fuel : Nat}
    (related : BindingSourceAgreement incoming independent)
    (old : ReadoutCertificate independent oldTable)
    (position : Nat) (left right : Atom)
    (stored : space.atoms[position]? = some (.expression [.symbol "=", left, right]))
    (rhs : candidate.1 = (freshenEquationAvoiding
      (equationScope live query expected incoming) position left right).2)
    (matching : candidate.2 ∈ matchAtoms query (freshenEquationAvoiding
      (equationScope live query expected incoming) position left right).1 fuel)
    (input : request ∈ equationInputs incoming fuel candidate)
    (covered : ∀ merged ∈ mergeBindings candidate.2 (aliasConstraints incoming) fuel,
      merged.hasLoop = false → merged.applyFullCovered candidate.1 fuel = true) :
    ∃ matched merged, ∃ certificate : ReadoutCertificate merged (nativeReadoutPresentation request.2),
      let before := BindingFrame.selected independent oldTable old
      let after := BindingFrame.selected merged (nativeReadoutPresentation request.2) certificate
      SourceBindingComparison.semantic.FrameRelated request.2 after ∧
      BindingFrame.Update .renew before after ∧
      EquationQueryOccurrenceRel space (expected :: live) query independent
        position left right
        (freshenEquationAvoiding (equationScope live query expected incoming) position left right).1
        candidate.1 matched candidate.1 merged ∧
      after.Materialization candidate.1 request.1 ∧
      (∀ atom depth, request.2.applyFullCovered atom depth = true →
        after.Materialization atom (request.2.applyFull atom depth)) ∧
      (∀ pending : List Atom,
        (pending.map oldTable.apply).map (nativeReadoutPresentation request.2).apply =
          pending.map (nativeReadoutPresentation request.2).apply) := by
  obtain ⟨matched, merged, occurrence, agreement, principal, _shape, _normal, _theory,
      observed, reads⟩ := equationInput_open_source_at related position left right stored rhs matching input
        (equationInputs_readCovered covered input)
  let certificate := nativeReadoutPresentation_certificate principal.loopFree principal.nonvariable
    principal.coherent agreement.solutions
  refine ⟨matched, merged, certificate, .semantic agreement certificate
    (fun atom depth enough => (reads atom depth enough).symm), .selected old certificate,
    occurrence, observed.symm, ?_, ?_⟩
  · intro atom depth enough
    exact (reads atom depth enough).symm
  · intro pending
    apply old.pending_absorbed certificate _ pending
    intro valuation model
    exact ((bindingSatisfied_append_iff valuation matched independent).mp
      ((occurrence.result.1.1.solutions valuation).mp model)).2

/-- The complete surviving frontier of one physical rule carries ordered
source occurrences. Equal work items remain separate list occurrences and
all of them renew the same chosen caller frame. -/
theorem equationInputs_selected_source_occurrences_at
    {space : Space} {live : List Atom} {query expected : Atom}
    {incoming independent : Bindings} {oldTable : TypeSubst}
    {candidate : ResultPair} {fuel : Nat}
    (related : BindingSourceAgreement incoming independent)
    (old : ReadoutCertificate independent oldTable)
    (position : Nat) (left right : Atom)
    (stored : space.atoms[position]? = some (.expression [.symbol "=",left,right]))
    (rhs : candidate.1 = (freshenEquationAvoiding
      (equationScope live query expected incoming) position left right).2)
    (matching : candidate.2 ∈ matchAtoms query (freshenEquationAvoiding
      (equationScope live query expected incoming) position left right).1 fuel)
    (covered : ∀ merged ∈ mergeBindings candidate.2 (aliasConstraints incoming) fuel,
      merged.hasLoop = false → merged.applyFullCovered candidate.1 fuel = true) :
    ∃ outputs : List (ResultPair × BindingFrame),
      outputs.map Prod.fst = equationInputs incoming fuel candidate ∧
      ∀ output ∈ outputs,
        SourceBindingComparison.semantic.FrameRelated output.1.2 output.2 ∧
        BindingFrame.Update .renew (.selected independent oldTable old) output.2 ∧
        (∃ matched, EquationQueryOccurrenceRel space (expected::live) query independent
          position left right
          (freshenEquationAvoiding (equationScope live query expected incoming) position left right).1
          candidate.1 matched candidate.1 output.2.bindings) ∧
        output.2.Materialization candidate.1 output.1.1 ∧
        (∀ atom depth, output.1.2.applyFullCovered atom depth = true →
          output.2.Materialization atom (output.1.2.applyFull atom depth)) ∧
        (∀ pending : List Atom,
          (pending.map oldTable.apply).map (nativeReadoutPresentation output.1.2).apply =
          pending.map (nativeReadoutPresentation output.1.2).apply) := by
  have each (request : ResultPair) (present : request ∈ equationInputs incoming fuel candidate) :=
    equationInput_selected_source_at related old position left right stored rhs matching present covered
  let property : ResultPair × BindingFrame → Prop := fun output =>
    SourceBindingComparison.semantic.FrameRelated output.1.2 output.2 ∧
    BindingFrame.Update .renew (.selected independent oldTable old) output.2 ∧
    (∃ matched, EquationQueryOccurrenceRel space (expected::live) query independent
      position left right
      (freshenEquationAvoiding (equationScope live query expected incoming) position left right).1
      candidate.1 matched candidate.1 output.2.bindings) ∧
    output.2.Materialization candidate.1 output.1.1 ∧
    (∀ atom depth, output.1.2.applyFullCovered atom depth = true →
      output.2.Materialization atom (output.1.2.applyFull atom depth)) ∧
    (∀ pending : List Atom,
      (pending.map oldTable.apply).map (nativeReadoutPresentation output.1.2).apply =
      pending.map (nativeReadoutPresentation output.1.2).apply)
  have traverse : ∀ rows : ResultSet,
      (∀ row ∈ rows, row ∈ equationInputs incoming fuel candidate) →
      ∃ outputs : List (ResultPair × BindingFrame), outputs.map Prod.fst = rows ∧
        ∀ output ∈ outputs, property output := by
    intro rows
    induction rows with
    | nil => exact fun _ => ⟨[],rfl,by simp⟩
    | cons row rows ih =>
      intro present
      obtain ⟨matched,merged,certificate,frame,renewed,occurrence,read,reads,pending⟩ :=
        each row (present row List.mem_cons_self)
      obtain ⟨rest,projection,restProperties⟩ := ih (fun item member =>
        present item (List.mem_cons_of_mem _ member))
      let output : BindingFrame := .selected merged (nativeReadoutPresentation row.2) certificate
      refine ⟨(row,output)::rest,by simp only [List.map_cons,projection],?_⟩
      intro item member
      rcases List.mem_cons.mp member with same | member
      · subst item
        exact ⟨frame,renewed,⟨matched,occurrence⟩,read,reads,pending⟩
      · exact restProperties item member
  exact traverse _ (fun _ member => member)

/-- Actual readiness and recursive producer/return admissions construct an
ordinary equation call. Open and nonlinear inputs use the same query path;
source evidence is earned here for every surviving physical work item. -/
theorem CallDerivation.coveredEquations {space : Space}
    (live : List Atom) (name : String) (arguments : List Atom) (expected : Atom)
    (incoming : Bindings) (fuel : Nat)
    (productions : ResultPair → ResultPair → ResultSet)
    (outputs : ResultPair → ResultPair → ResultPair → ResultSet)
    (ordinary : name ≠ "unify" ∧ name ≠ "switch-minimal")
    (nonembedded : Minimal.embeddedInstruction (.expression [.symbol name]) = false)
    (clean : name ≠ "Error")
    (query : queryEquationsCovered
      (equationScope live (.expression (.symbol name :: arguments)) expected incoming)
      space (.expression (.symbol name :: arguments)) fuel = true)
    (inputs : ∀ candidate ∈ equationCandidates space live
        (.expression (.symbol name :: arguments)) expected incoming fuel,
      matchCovered fuel (.merge candidate.2 (aliasConstraints incoming)) = true ∧
      ∀ merged ∈ mergeBindings candidate.2 (aliasConstraints incoming) fuel, merged.hasLoop = false →
        merged.applyFullCovered candidate.1 fuel = true)
    (present : rawQueryResults space (.expression (.symbol name :: arguments)) expected incoming fuel live ≠ [])
    (producers : ∀ candidate ∈ equationCandidates space live
        (.expression (.symbol name :: arguments)) expected incoming fuel,
      ∀ request ∈ equationInputs incoming fuel candidate,
      ProducedDerivation space .semantic (expected :: live)
        (some (.expression (.symbol name :: arguments))) request.1 request.2 fuel
        (productions candidate request))
    (returns : ∀ candidate ∈ equationCandidates space live
        (.expression (.symbol name :: arguments)) expected incoming fuel,
      ∀ request ∈ equationInputs incoming fuel candidate, ∀ produced ∈ productions candidate request,
      ReturnDerivation space .semantic live (.expression (.symbol name :: arguments)) expected
        produced.1 produced.2 fuel (outputs candidate request produced))
    (returnCoverage : ∀ candidate hit request selected produced occurred,
      ReturnDerivation.Covered (returns candidate hit request selected produced occurred)) :
    ∃ derived : CallDerivation space .semantic live (.expression (.symbol name :: arguments))
      expected incoming (fuel + 1)
      ((equationCandidates space live (.expression (.symbol name :: arguments)) expected incoming fuel).flatMap
        fun candidate => (equationInputs incoming fuel candidate).flatMap fun request =>
          (productions candidate request).flatMap (outputs candidate request)),
      derived.Covered := by
  let evidence : ∀ candidate ∈ equationCandidates space live
      (.expression (.symbol name :: arguments)) expected incoming fuel,
      ∀ request ∈ equationInputs incoming fuel candidate,
      EquationBodyEvidence space live (.expression (.symbol name :: arguments)) expected
        incoming candidate request .semantic := fun candidate hit request selected =>
    EquationBodyEvidence.of_covered_query_hit (request := request) hit (inputs candidate hit).2 selected
  refine ⟨.equations live name arguments expected incoming fuel productions outputs ordinary
    nonembedded clean present evidence producers returns, ?_⟩
  exact .equations (ordinary := ordinary) (nonembedded := nonembedded) (clean := clean)
    (selected := present) (evidence := evidence) (producers := producers) query inputs returnCoverage

/-- Raw invocation shares the same automatic open-query evidence and retains
its own caller and return protocol. -/
theorem RawInvocationDerivation.coveredEquations {space : Space}
    (live : List Atom) (caller : Option Atom) (name : String) (arguments : List Atom)
    (incoming : Bindings) (fuel : Nat) (outputs : ResultPair → ResultPair → ResultSet)
    (ordinary : minimalInstruction (.expression (.symbol name :: arguments)) = false)
    (query : queryEquationsCovered
      (equationScope live (.expression (.symbol name :: arguments)) Atom.undefinedType incoming)
      space (.expression (.symbol name :: arguments)) fuel = true)
    (inputs : ∀ candidate ∈ equationCandidates space live
        (.expression (.symbol name :: arguments)) Atom.undefinedType incoming fuel,
      matchCovered fuel (.merge candidate.2 (aliasConstraints incoming)) = true ∧
      ∀ merged ∈ mergeBindings candidate.2 (aliasConstraints incoming) fuel, merged.hasLoop = false →
        merged.applyFullCovered candidate.1 fuel = true)
    (present : rawQueryResults space (.expression (.symbol name :: arguments)) Atom.undefinedType incoming fuel live ≠ [])
    (producers : ∀ candidate ∈ equationCandidates space live
        (.expression (.symbol name :: arguments)) Atom.undefinedType incoming fuel,
      ∀ request ∈ equationInputs incoming fuel candidate,
      ProducedDerivation space .semantic live (some (.expression (.symbol name :: arguments)))
        request.1 request.2 fuel (outputs candidate request)) :
    RawInvocationDerivation space .semantic live caller (.expression (.symbol name :: arguments))
      incoming (fuel + 1)
      ((equationCandidates space live (.expression (.symbol name :: arguments)) Atom.undefinedType incoming fuel).flatMap
        fun candidate => (equationInputs incoming fuel candidate).flatMap (outputs candidate)) :=
  .equations live caller name arguments incoming fuel outputs ordinary query inputs present
    (fun candidate hit request selected =>
      .of_covered_query_hit (request := request) hit (inputs candidate hit).2 selected) producers

end Mettapedia.Languages.MeTTa.HE.FirstSuccessSourceExecution

section

set_option autoImplicit false
set_option maxRecDepth 12000
set_option maxHeartbeats 4000000
namespace Mettapedia.Languages.MeTTa.HE.FirstSuccessSourceExecution.OpenNonlinearControls
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open RecursiveTasks RecursiveMachine FirstSuccessRecursiveExecution
open Spec.Eval Spec.Eval.Steps Spec.Type.Presentation Spec.Type.Presentation.Theory
open Spec.Type.Presentation.BindingTheory Spec.Type.RuntimeRefinement QueryBindingProjection

def value : Atom := .symbol "Value"
def kept : Atom := .symbol "Kept"
def entries : TypeSubst := [("u", .var "v"), ("keep", kept), ("outer", .var "anchor")]
def incoming : Bindings := ⟨[("outer",.var "anchor"),("keep",kept),("u",.var "v")],[]⟩
def query : Atom := .expression [.symbol "link",.var "u",.var "u"]
def pattern : Atom := .expression [.symbol "link",.var "x",.var "x"]
def pair (key : String) : Atom := .expression [.symbol "Pair",.var key,.var key]
def answer : Atom := .expression [.symbol "Pair",value,value]
def template (key : String) : Atom := .expression [.symbol "return",pair key]
def returned : Atom := .expression [.symbol "return",answer]
def parts (key : String) : List Atom := [.symbol "unify",value,.var key,template key,.symbol "No"]
def body (key : String) : Atom := .expression (parts key)
def block (key : String) : Atom := .expression [.symbol "function",body key]
def rule : Atom := .expression [.symbol "=",pattern,block "x"]
def context : Space := Space.ofList [rule,rule]
def live : List Atom := [.expression [.symbol "Pending",.var "u",.var "v",.var "outer",.var "keep"]]
def depth : Nat := 64
def key (index : Fin 2) : String := "x#" ++ Nat.repr index.val
def matched (index : Fin 2) : Bindings := ⟨[],[("u",key index),("u",key index)]⟩
def candidate (index : Fin 2) : ResultPair := (block (key index),matched index)
def merged (index : Fin 2) : Bindings :=
  ⟨[("keep",kept)],[("u",key index),("u",key index),("outer","anchor"),("u","v")]⟩
def request (index : Fin 2) : ResultPair := (block "u",merged index)
def final (index : Fin 2) : Bindings :=
  ⟨[("u",value),("keep",kept)],(merged index).equalities⟩
def raw (index : Fin 2) : ResultSet := [(returned,final index)]
def answers : ResultSet := [(answer,final 0),(answer,final 1)]
def outputs (row : ResultPair) : ResultSet :=
  if row = request 0 then [(answer,final 0)] else [(answer,final 1)]

theorem normalized : CurrentStore.normalize entries = incoming.assignments := by
  simp [CurrentStore.normalize,CurrentStore.normalizeFrom,entries,incoming,kept,
    TypeSubst.bind,TypeSubst.apply,TypeSubst.lookup,TypeSubst.erase,TypeSubst.applyAssignment]

theorem initialCertificate : ReadoutCertificate ⟨entries,[]⟩ (CurrentStore.normalize entries) :=
  CurrentStore.normalize_certified_of_noLoop (by decide +kernel) (by decide +kernel)

def initialFrame : BindingFrame := .selected ⟨entries,[]⟩ (CurrentStore.normalize entries) initialCertificate

theorem initialRelated : SourceBindingComparison.semantic.FrameRelated incoming initialFrame := by
  have actual := SourceBindingComparison.FrameRelated.normalized
    (entries := entries) (by decide +kernel) (by decide +kernel)
  simpa only [normalized, FirstSuccessPreparedArguments.presentedBindings, incoming, initialFrame] using actual

theorem queried : equationCandidates context live query Atom.atomType incoming depth =
    [candidate 0,candidate 1] := by decide +kernel

theorem prepared (index : Fin 2) : equationInputs incoming depth (candidate index) = [request index] := by
  fin_cases index <;> decide +kernel

theorem input_covered (index : Fin 2) :
    matchCovered depth (.merge (candidate index).2 (aliasConstraints incoming)) = true ∧
      ∀ out ∈ mergeBindings (candidate index).2 (aliasConstraints incoming) depth,
        out.hasLoop = false → out.applyFullCovered (candidate index).1 depth = true := by
  constructor
  · fin_cases index <;> decide +kernel
  · intro out present _
    have actual : mergeBindings (candidate index).2 (aliasConstraints incoming) depth = [merged index] := by
      fin_cases index <;> decide +kernel
    rw [actual] at present
    obtain rfl := List.mem_singleton.mp present
    fin_cases index <;> decide +kernel

theorem selected_request {selected input : ResultPair}
    (member : selected ∈ equationCandidates context live query Atom.atomType incoming depth)
    (present : input ∈ equationInputs incoming depth selected) :
    ∃ index : Fin 2, selected = candidate index ∧ input = request index := by
  rw [queried] at member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with same | same
  · subst selected
    rw [prepared] at present
    exact ⟨0,rfl,List.mem_singleton.mp present⟩
  · subst selected
    rw [prepared] at present
    exact ⟨1,rfl,List.mem_singleton.mp present⟩

theorem output_index (index : Fin 2) : outputs (request index) = [(answer,final index)] := by
  fin_cases index <;> decide +kernel

theorem body_admitted (index : Fin 2) (scope : List Atom) (caller : Option Atom) :
    FunctionBodyDerivation context .semantic scope caller (body "u") (merged index) (depth - 2) (raw index) := by
  have success : unifySuccessResults value (.var "u") (template "u") (merged index) (depth - 5) = raw index := by
    fin_cases index <;> decide +kernel
  have primitive : PrimitiveDerivation context .semantic scope caller (body "u") (merged index) (depth - 4) (raw index) := by
    have derived := PrimitiveDerivation.unifySuccess (space := context) (comparison := .semantic)
      scope caller value (.var "u") (template "u") (.symbol "No") (merged index) (depth - 5)
      (by fin_cases index <;> decide +kernel) (by rw [success]; simp [raw])
    rw [success] at derived
    simpa only [body,parts,depth] using derived
  have child : MinimalDerivation context .semantic scope caller (body "u") (merged index) (depth - 3) (raw index) :=
    .instruction scope caller (body "u") (merged index) (depth - 4) _ rfl
      (by simp [Minimal.IsChain,body,parts]) primitive
  have terminal : ∀ row ∈ raw index,
      minimalInstruction (row.2.applyFull row.1 (depth - 3)) = false := by
    intro row member
    obtain rfl := List.mem_singleton.mp member
    fin_cases index <;> decide +kernel
  have derived := FunctionBodyDerivation.run (space := context) (comparison := .semantic) scope caller
    (body "u") (merged index) (depth - 3) (raw index) (fun row => [row]) child
    (by intro row member; obtain rfl := List.mem_singleton.mp member
        fin_cases index <;> decide +kernel)
    (by intro row member _; obtain rfl := List.mem_singleton.mp member
        fin_cases index <;> decide +kernel)
    (fun row member instruction => False.elim
      (Bool.noConfusion ((terminal row member).symm.trans instruction)))
  simpa only [raw,List.flatMap_cons,List.flatMap_nil,List.singleton_append,depth] using derived

theorem producer (index : Fin 2) :
    ProducedDerivation context .semantic (Atom.atomType :: live) (some query)
      (request index).1 (request index).2 depth (outputs (request index)) := by
  rw [output_index]
  have body := body_admitted index (block "u" :: Atom.atomType :: live) (some (block "u"))
  have primitive := PrimitiveDerivation.function (space := context) (comparison := .semantic)
    (Atom.atomType :: live) (some query) (parts "u") (merged index) (depth - 2) (raw index) body
  have finished : ((raw index).map fun row => (functionTerminal (some query) row.1,row.2)) =
      [(answer,final index)] := by rfl
  rw [finished] at primitive
  exact .function _ _ _ _ (depth - 1) _ rfl primitive


theorem receiver (index : Fin 2) :
    ReturnDerivation context .semantic live query Atom.atomType answer (final index) depth [(answer,final index)] :=
  .evaluate live query Atom.atomType answer (final index) depth _
    (by simp [answer,Atom.notReducible])
    (by simp [answer,IsEmptyOrErrorRel,IsErrorRel,Atom.empty])
    (.leaf live answer Atom.atomType (final index) (depth - 1)
      (Or.inr ⟨Atom.expressionType,.expression _,Or.inl rfl⟩))

theorem receiver_covered (index : Fin 2) : (receiver index).Covered :=
  .evaluate
    (accepted := by simp [answer,Atom.notReducible])
    (running := by simp [answer,IsEmptyOrErrorRel,IsErrorRel,Atom.empty])
    (child := .leaf live answer Atom.atomType (final index) (depth - 1)
      (Or.inr ⟨Atom.expressionType,.expression _,Or.inl rfl⟩))
    (.leaf (leaf := Or.inr ⟨Atom.expressionType,.expression _,Or.inl rfl⟩))

/-- Neither the query nor its selected body is closed. Automatic admission
runs each duplicated physical rule, then the producer binds the shared open
class and the ordinary receiver reads the resulting pair. -/
theorem call_admitted :
    ∃ derived : CallDerivation context .semantic live query Atom.atomType incoming (depth + 1) answers,
      derived.Covered := by
  have produced : ∀ selected ∈ equationCandidates context live query Atom.atomType incoming depth,
      ∀ input ∈ equationInputs incoming depth selected,
      ProducedDerivation context .semantic (Atom.atomType :: live) (some query)
        input.1 input.2 depth (outputs input) := by
    intro selected hit input present
    obtain ⟨index,rfl,rfl⟩ := selected_request hit present
    exact producer index
  have returns : ∀ selected ∈ equationCandidates context live query Atom.atomType incoming depth,
      ∀ input ∈ equationInputs incoming depth selected, ∀ row ∈ outputs input,
      ReturnDerivation context .semantic live query Atom.atomType row.1 row.2 depth [row] := by
    intro selected hit input present row occurred
    obtain ⟨index,rfl,rfl⟩ := selected_request hit present
    rw [output_index] at occurred
    obtain rfl := List.mem_singleton.mp occurred
    exact receiver index
  have covered : ∀ selected hit input present row occurred,
      ReturnDerivation.Covered (returns selected hit input present row occurred) := by
    intro selected hit input present row occurred
    obtain ⟨index,rfl,rfl⟩ := selected_request hit present
    rw [output_index] at occurred
    obtain rfl := List.mem_singleton.mp occurred
    exact receiver_covered index
  obtain ⟨derived, ready⟩ := CallDerivation.coveredEquations (space := context)
    live "link" [.var "u",.var "u"] Atom.atomType incoming depth
    (fun _ input => outputs input) (fun _ _ row => [row])
    (by decide) (by decide) (by decide) (by decide +kernel)
    (by
      intro selected hit
      change selected ∈ equationCandidates context live query Atom.atomType incoming depth at hit
      rw [queried] at hit
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hit
      rcases hit with rfl | rfl
      · exact input_covered 0
      · exact input_covered 1)
    (by decide +kernel) produced returns covered
  have joined : ((equationCandidates context live query Atom.atomType incoming depth).flatMap
      fun selected => (equationInputs incoming depth selected).flatMap fun input =>
        (outputs input).flatMap fun row => [row]) = answers := by
    rw [queried]
    simp only [List.flatMap_cons,List.flatMap_nil,prepared,List.append_nil,List.singleton_append,
      output_index,answers]
  change ∃ derived : CallDerivation context .semantic live query Atom.atomType incoming (depth + 1) answers,
    derived.Covered
  change CallDerivation context .semantic live query Atom.atomType incoming (depth + 1) _ at derived
  rw [← joined]
  exact ⟨derived,ready⟩

/-- Chosen independent inputs remain universal; the nonempty alias-bearing
fixture supplies one concrete instance of that representation relation. -/
theorem source_call (input : BindingFrame)
    (related : SourceBindingComparison.semantic.FrameRelated incoming input) (index : Fin 2) :
    ∃ output,
      CallRel context noHost live query Atom.atomType input (answer,output) ∧
      SourceBindingComparison.semantic.FrameRelated (final index) output := by
  obtain ⟨derived,_⟩ := call_admitted
  exact derived.sound (answer,final index) (by fin_cases index <;> simp [answers]) input related

theorem source_from_actual_alias_input (index : Fin 2) :
    ∃ output, CallRel context noHost live query Atom.atomType initialFrame (answer,output) ∧
      SourceBindingComparison.semantic.FrameRelated (final index) output :=
  source_call initialFrame initialRelated index

/-- Saved callers and prior publications remain untouched by the actual
covered local path. The two output occurrences retain their complete records. -/
theorem retained_path (stack : List Frame) (earned : ResultSet) :
    Covered.SilentPath
      ⟨context,.work (.call query Atom.atomType incoming (depth+1) live),stack,earned⟩
      ⟨context,.returning answers,stack,earned⟩ := by
  obtain ⟨derived,covered⟩ := call_admitted
  exact derived.covered_realizes covered stack earned

theorem checked_completion (earned : ResultSet) :
    ∃ budget, ∀ later,
      (FirstSuccessRecursiveExecution.Checked.machine HE.GroundedDispatch.none).run (budget+later)
        ⟨context,.work (.call query Atom.atomType incoming (depth+1) live),[],earned⟩ =
      (answers,.finished ⟨context,.returning [],[],earned++answers⟩) := by
  obtain ⟨derived,covered⟩ := call_admitted
  exact derived.checked_completed covered earned

/-- Every physical rule owns its own fresh variable even when the resulting
function bodies have the same public residual spelling. -/
theorem physical_renewal (index : Fin 2) :
    ∃ matched source, ∃ certificate : ReadoutCertificate source (nativeReadoutPresentation (merged index)),
      let after := BindingFrame.selected source (nativeReadoutPresentation (merged index)) certificate
      SourceBindingComparison.semantic.FrameRelated (merged index) after ∧
      BindingFrame.Update .renew initialFrame after ∧
      EquationQueryOccurrenceRel context (Atom.atomType::live) query initialFrame.bindings
        index.val pattern (block "x")
        (freshenEquationAvoiding (equationScope live query Atom.atomType incoming) index.val pattern (block "x")).1
        (candidate index).1 matched (candidate index).1 source ∧
      after.Materialization (candidate index).1 (block "u") ∧
      (∀ atom fuel, (merged index).applyFullCovered atom fuel = true →
        after.Materialization atom ((merged index).applyFull atom fuel)) ∧
      (∀ pending : List Atom,
        (pending.map (CurrentStore.normalize entries).apply).map (nativeReadoutPresentation (merged index)).apply =
        pending.map (nativeReadoutPresentation (merged index)).apply) := by
  have stored : context.atoms[index.val]? = some (.expression [.symbol "=",pattern,block "x"]) := by
    fin_cases index <;> rfl
  have rhs : (candidate index).1 = (freshenEquationAvoiding
      (equationScope live query Atom.atomType incoming) index.val pattern (block "x")).2 := by
    fin_cases index <;> decide +kernel
  have matching : (candidate index).2 ∈ matchAtoms query (freshenEquationAvoiding
      (equationScope live query Atom.atomType incoming) index.val pattern (block "x")).1 depth := by
    fin_cases index <;> decide +kernel
  have present : request index ∈ equationInputs incoming depth (candidate index) := by
    rw [prepared]; exact List.mem_singleton_self _
  have earned := equationInput_selected_source_at (space := context) (live := live)
    (query := query) (expected := Atom.atomType) (incoming := incoming)
    (independent := ⟨entries,[]⟩) (oldTable := CurrentStore.normalize entries)
    (candidate := candidate index) (request := request index) (fuel := depth)
    initialRelated.related initialCertificate index.val pattern (block "x")
    stored rhs matching present (input_covered index).2
  simpa only [request,initialFrame,BindingFrame.selected] using earned

/-- One actual read of the pending tuple observes every alias use after the
body changes bindings, while unrelated caller information is preserved. -/
theorem all_pending_uses_and_caller_constraints (index : Fin 2) :
    (final index).applyFull (.expression [.var "u",.var "v",.var (key index),
      .var "u",.var "keep",.var "outer",.var "anchor"]) depth =
      .expression [value,value,value,value,kept,.var "outer",.var "outer"] ∧
      ("outer","anchor") ∈ (final index).equalities ∧
      (final index).lookup "keep" = some kept ∧
      (final index).lookup "u" = some value := by
  fin_cases index <;> decide +kernel

theorem genuinely_open_and_binding_changing (index : Fin 2) :
    TypeSubst.typeVars query ≠ [] ∧ TypeSubst.typeVars (request index).1 ≠ [] ∧
      (merged index).lookup "u" = none ∧ (final index).lookup "u" = some value ∧
      merged index ≠ final index := by fin_cases index <;> decide +kernel

theorem duplicates_are_occurrences : answers.length = 2 ∧ final 0 ≠ final 1 ∧
    answers.map Prod.fst = [answer,answer] ∧ answers ≠ [(answer,final 0)] := by decide +kernel

/-- Nonlinear matching refuses incompatible instances before a body starts. -/
theorem nonlinear_conflict : equationCandidates context live
    (.expression [.symbol "link",.symbol "A",.symbol "B"]) Atom.atomType incoming depth = [] := by
  decide +kernel

theorem structural_occurs_failure : equationCandidates context live
    (.expression [.symbol "link",.var "z",.expression [.symbol "f",.var "z"]])
    Atom.atomType incoming depth = [] := by decide +kernel

/-- Existing caller constraints cannot be dropped merely to accept a body. -/
theorem incompatible_caller_has_no_unify_branch (index : Fin 2) :
    unifySuccessResults value (.var "u") (template "u")
      ⟨[("u",.symbol "Different"),("keep",kept)],(merged index).equalities⟩ (depth-5) = [] := by
  fin_cases index <;> decide +kernel

theorem depth_exhaustion_is_not_refusal :
    (FirstSuccessRecursiveExecution.Checked.machine HE.GroundedDispatch.none).run 2
      ⟨context,.work (.call query Atom.atomType incoming 0 live),[],[]⟩ =
      ([],.suspended .evaluationDepth
        ⟨context,.work (.invocation (.ordinary Atom.atomType) query incoming 0 live none),[],[]⟩) := rfl


/-- The raw invocation uses the same constructed evidence without the
ordinary return receiver; it still executes the actual function producer. -/
theorem raw_admitted (caller : Option Atom) :
    RawInvocationDerivation context .semantic live caller query incoming (depth+1) answers := by
  have rawQuery : equationCandidates context live query Atom.undefinedType incoming depth =
      [candidate 0,candidate 1] := by decide +kernel
  have rawSelected {selected input : ResultPair}
      (hit : selected ∈ equationCandidates context live query Atom.undefinedType incoming depth)
      (present : input ∈ equationInputs incoming depth selected) :
      ∃ index : Fin 2, selected = candidate index ∧ input = request index := by
    apply selected_request
    · rw [queried,← rawQuery]; exact hit
    · exact present
  have producerRaw (index : Fin 2) :
      ProducedDerivation context .semantic live (some query) (block "u") (merged index) depth
        (outputs (request index)) := by
    rw [output_index]
    have body := body_admitted index (block "u" :: live) (some (block "u"))
    have primitive := PrimitiveDerivation.function (space := context) (comparison := .semantic)
      live (some query) (parts "u") (merged index) (depth-2) (raw index) body
    have finished : ((raw index).map fun row => (functionTerminal (some query) row.1,row.2)) =
        [(answer,final index)] := by rfl
    rw [finished] at primitive
    exact .function _ _ _ _ (depth-1) _ rfl primitive
  have derived := RawInvocationDerivation.coveredEquations (space := context)
    live caller "link" [.var "u",.var "u"] incoming depth (fun _ input => outputs input)
    (by decide) (by decide +kernel)
    (by
      intro selected hit
      change selected ∈ equationCandidates context live query Atom.undefinedType incoming depth at hit
      rw [rawQuery] at hit
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hit
      rcases hit with rfl | rfl
      · exact input_covered 0
      · exact input_covered 1)
    (by decide +kernel)
    (by
      intro selected hit input present
      obtain ⟨index,rfl,rfl⟩ := rawSelected hit present
      exact producerRaw index)
  have joined : ((equationCandidates context live query Atom.undefinedType incoming depth).flatMap
      fun selected => (equationInputs incoming depth selected).flatMap outputs) = answers := by
    rw [rawQuery]
    simp only [List.flatMap_cons,List.flatMap_nil,prepared,List.append_nil,List.singleton_append,
      output_index,answers]
  rw [← joined]
  exact derived

theorem raw_checked_completion (caller : Option Atom) (earned : ResultSet) :
    ∃ budget, ∀ later,
      (FirstSuccessRecursiveExecution.Checked.machine HE.GroundedDispatch.none).run (budget+later)
        ⟨context,.work (.invocation .raw query incoming (depth+1) live caller),[],earned⟩ =
      (answers,.finished ⟨context,.returning [],[],earned++answers⟩) :=
  (raw_admitted caller).checked_completed earned

/-- A name present only in the retained live tuple is protected by actual
freshening. Reusing the unguarded candidate is therefore rejected. -/
theorem pending_name_avoids_capture :
    let guardedLive := Atom.var "x#0" :: live
    (freshenEquationAvoiding (equationScope guardedLive query Atom.atomType incoming)
      0 pattern (block "x")).2 ≠ (candidate 0).1 ∧
    (equationCandidates context guardedLive query Atom.atomType incoming depth).length = 2 := by
  decide +kernel


def initial (earned : ResultSet) : Configuration :=
  ⟨context,.work (.call query Atom.atomType incoming (depth+1) live),[],earned⟩

def saved (earned : ResultSet) : Configuration :=
  ⟨context,.work (.bodyResults (depth-3) [] (block "u" :: Atom.atomType :: live) (some (block "u"))),
    [.prepend (raw 0),.functionTerminal (some query),
      .append (.productions depth [request 1] (Atom.atomType :: live) (some query) .emitted),
      .invocationReturn (.ordinary Atom.atomType) query depth live],earned⟩

/-- A real scheduler prefix stops after the first binding change while the
second physical rule and the ordinary receiver are still retained. -/
theorem actual_saved_checkpoint (earned : ResultSet) :
    (FirstSuccessRecursiveExecution.Checked.machine HE.GroundedDispatch.none).run 20 (initial earned) =
      ([],.exhausted (saved earned)) := rfl

theorem saved_has_changed_binding_and_pending_occurrence (earned : ResultSet) :
    .prepend (raw 0) ∈ (saved earned).stack ∧
      .append (.productions depth [request 1] (Atom.atomType::live) (some query) .emitted)
        ∈ (saved earned).stack ∧
      .invocationReturn (.ordinary Atom.atomType) query depth live ∈ (saved earned).stack ∧
      (final 0).lookup "u" = some value ∧ (merged 1).lookup "u" = none ∧
      (saved earned).emitted = earned := by
  simp [saved,raw,final,merged,value,Bindings.lookup]

theorem saved_resumes (earned : ResultSet) :
    ∃ budget remaining,
      (FirstSuccessRecursiveExecution.Checked.machine HE.GroundedDispatch.none).run budget (saved earned) =
        (remaining,.finished ⟨context,.returning [],[],earned++answers⟩) ∧ remaining = answers := by
  obtain ⟨derived,covered⟩ := call_admitted
  simpa only [List.nil_append] using
    Covered.completes_saved (derived.covered_realizes covered) earned 20 [] (saved earned)
      (actual_saved_checkpoint earned)

theorem saved_is_not_completed_empty (earned : ResultSet) :
    (FirstSuccessRecursiveExecution.Checked.machine HE.GroundedDispatch.none).run 20 (initial earned) ≠
      ([],.finished (saved earned)) := by
  rw [actual_saved_checkpoint]
  intro same
  cases same

/-- The independent return observes all residual aliases through its earned
single table, including the still-free unrelated caller class. -/
theorem source_pending_tuple (input : BindingFrame)
    (related : SourceBindingComparison.semantic.FrameRelated incoming input) (index : Fin 2) :
    ∃ output, CallRel context noHost live query Atom.atomType input (answer,output) ∧
      SourceBindingComparison.semantic.FrameRelated (final index) output ∧
      output.Materialization
        (.expression [.var "u",.var "v",.var (key index),.var "u",.var "keep",.var "outer",.var "anchor"])
        (.expression [value,value,value,value,kept,.var "outer",.var "outer"]) := by
  obtain ⟨output,source,frame⟩ := source_call input related index
  refine ⟨output,source,frame,?_⟩
  have actual := frame.materialization
    (.expression [.var "u",.var "v",.var (key index),.var "u",.var "keep",.var "outer",.var "anchor"])
    depth (by fin_cases index <;> decide +kernel)
  simpa only [(all_pending_uses_and_caller_constraints index).1] using actual

end Mettapedia.Languages.MeTTa.HE.FirstSuccessSourceExecution.OpenNonlinearControls

end

section
set_option autoImplicit false
set_option maxRecDepth 12000
set_option maxHeartbeats 4000000

namespace Mettapedia.Languages.MeTTa.HE.FirstSuccessSourceExecution.UntypedTupleControls
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open RecursiveTasks RecursiveMachine FirstSuccessRecursiveExecution
open Spec.Eval Spec.Eval.Steps Spec.Type.Presentation Spec.Type.Presentation.Theory
open Spec.Type.Presentation.BindingTheory Spec.Type.RuntimeRefinement QueryBindingProjection

def a : Atom := .symbol "A"
def done : Atom := .symbol "Done"
def kept : Atom := .symbol "Kept"
def incoming : Bindings := ⟨[("keep",kept)],[]⟩
def pattern : Atom := .expression [.symbol "pick",.var "x",.var "x"]
def rule : Atom := .expression [.symbol "=",pattern,done]
def context : Space := Space.ofList [rule,rule]
def query : Atom := .expression [.symbol "pick",a,a]
def term : Atom := .expression [.symbol "Box",query]
def answer : Atom := .expression [.symbol "Box",done]
def live : List Atom := [.var "held"]
def innerLive : List Atom := .symbol "Box" :: Atom.undefinedType :: live
def key (index : Fin 2) : String := "x#" ++ Nat.repr index.val
def matched (index : Fin 2) : Bindings := ⟨[(key index,a)],[]⟩
def bindings (index : Fin 2) : Bindings := ⟨[(key index,a),("keep",kept)],[]⟩
def candidate (index : Fin 2) : ResultPair := (done,matched index)
def request (index : Fin 2) : ResultPair := (done,bindings index)
def innerAnswers : ResultSet := [request 0,request 1]
def answers : ResultSet := [(answer,bindings 0),(answer,bindings 1)]

theorem symbol_lookup (name : String) : getAtomTypes context (.symbol name) = [Atom.undefinedType] := rfl

private theorem symbol_admitted (scope : List Atom) (name : String) (state : Bindings)
    (fuel : Nat) (clean : name ≠ "Empty") (enough : sizeOf Atom.undefinedType + sizeOf [Atom.undefinedType] + 2 ≤ fuel) :
    ∃ derived : AtomDerivation context .semantic scope (.symbol name) Atom.undefinedType
        state (fuel+1) [(.symbol name,state)], derived.Covered := by
  have sizeBound : sizeOf Atom.undefinedType + sizeOf Atom.undefinedType + 2 ≤ fuel :=
    Nat.le_trans (by decide) enough
  let derived := AtomDerivation.symbolCast (space := context) (comparison := .semantic)
    scope name Atom.undefinedType state fuel [] [] Atom.undefinedType clean
    (by decide) (by decide) (symbol_lookup name) rfl rfl (by simp) (by simp)
    (Or.inl rfl) sizeBound
  have covered : derived.Covered := .symbolCast (before := []) (after := [])
    (actual := Atom.undefinedType) (notEmpty := clean) (notRaw := by decide) (notMeta := by decide)
    (types := symbol_lookup name) (expectedClosed := rfl) (actualClosed := rfl)
    (earlierClosed := by simp) (earlierRejected := by simp) (fits := Or.inl rfl) (enough := sizeBound) (by
    apply FirstSuccessSourceApplicability.closed_typeCast_covered
      context (.symbol name) Atom.undefinedType state fuel rfl
    · intro actual member
      rw [symbol_lookup] at member
      obtain rfl := List.mem_singleton.mp member
      rfl
    · rw [symbol_lookup]
      exact enough)
  exact ⟨derived,covered⟩

private theorem tuple_single (scope : List Atom) (value : Atom) (state : Bindings)
    (fuel : Nat) (rows : ResultSet)
    (child : ∃ derived : AtomDerivation context .semantic scope value Atom.undefinedType
      state fuel rows, derived.Covered) :
    ∃ derived : TupleDerivation context .semantic scope (.expression [value])
      state (fuel+1) (rows.map HE.tupleSingleton), derived.Covered := by
  obtain ⟨derived,covered⟩ := child
  exact ⟨.singleton scope value state fuel rows derived, .singleton covered⟩

private theorem tuple_cons (scope : List Atom) (head second : Atom) (tail : List Atom)
    (state next : Bindings) (fuel : Nat) (value : Atom) (rows : ResultSet)
    (clean : isEmptyOrError value = false)
    (first : ∃ derived : AtomDerivation context .semantic
      (.expression (second::tail)::scope) head Atom.undefinedType state fuel [(value,next)],
      derived.Covered)
    (rest : ∃ derived : TupleDerivation context .semantic (value::scope)
      (.expression (second::tail)) next fuel rows, derived.Covered) :
    ∃ derived : TupleDerivation context .semantic scope (.expression (head::second::tail))
      state (fuel+1) (RecursiveTasks.tupleTail value rows), derived.Covered := by
  obtain ⟨first,firstCovered⟩ := first
  obtain ⟨rest,restCovered⟩ := rest
  have children : ∀ selected ∈ [(value,next)], isEmptyOrError selected.1 = false →
      TupleDerivation context .semantic (selected.1::scope) (.expression (second::tail))
        selected.2 fuel rows := by
    intro selected member _
    obtain rfl := List.mem_singleton.mp member
    exact rest
  have childrenCovered : ∀ selected member safe, (children selected member safe).Covered := by
    intro selected member _
    obtain rfl := List.mem_singleton.mp member
    exact restCovered
  have derived := TupleDerivation.cons (space := context) (comparison := .semantic)
    scope head second tail state fuel [(value,next)] (fun _ => rows) first children
  have covered := TupleDerivation.Covered.cons firstCovered childrenCovered
  simpa only [tupleOutputs,List.flatMap_cons,List.flatMap_nil,List.append_nil,clean,
    Bool.false_eq_true,if_false] using (⟨derived,covered⟩ : ∃ d, d.Covered)

theorem queried : equationCandidates context innerLive query Atom.undefinedType incoming 4099 =
    [candidate 0,candidate 1] := by decide +kernel

theorem prepared (index : Fin 2) : equationInputs incoming 4099 (candidate index) = [request index] := by
  fin_cases index <;> decide +kernel

theorem inputs_covered (index : Fin 2) :
    matchCovered 4099 (.merge (candidate index).2 (aliasConstraints incoming)) = true ∧
    ∀ out ∈ mergeBindings (candidate index).2 (aliasConstraints incoming) 4099,
      out.hasLoop = false → out.applyFullCovered (candidate index).1 4099 = true := by
  constructor
  · fin_cases index <;> decide +kernel
  · intro out member _
    have actual : mergeBindings (candidate index).2 (aliasConstraints incoming) 4099 = [bindings index] := by
      fin_cases index <;> decide +kernel
    rw [actual] at member
    obtain rfl := List.mem_singleton.mp member
    fin_cases index <;> decide +kernel

theorem selected_request {selected input : ResultPair}
    (member : selected ∈ equationCandidates context innerLive query Atom.undefinedType incoming 4099)
    (present : input ∈ equationInputs incoming 4099 selected) :
    ∃ index : Fin 2, selected = candidate index ∧ input = request index := by
  rw [queried] at member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · rw [prepared] at present
    exact ⟨0,rfl,List.mem_singleton.mp present⟩
  · rw [prepared] at present
    exact ⟨1,rfl,List.mem_singleton.mp present⟩

theorem inner_call_admitted :
    ∃ derived : CallDerivation context .semantic innerLive query Atom.undefinedType incoming 4100
      innerAnswers, derived.Covered := by
  have producers : ∀ selected ∈ equationCandidates context innerLive query Atom.undefinedType incoming 4099,
      ∀ input ∈ equationInputs incoming 4099 selected,
      ProducedDerivation context .semantic (Atom.undefinedType::innerLive) (some query)
        input.1 input.2 4099 [input] := by
    intro selected member input present
    obtain ⟨index,rfl,rfl⟩ := selected_request member present
    exact .raw _ _ done (bindings index) 4098 (by simp [Minimal.IsFunction,done])
  have receiver (index : Fin 2) : ∃ derived : ReturnDerivation context .semantic innerLive query
      Atom.undefinedType done (bindings index) 4099 [request index], derived.Covered := by
    obtain ⟨child,covered⟩ := symbol_admitted innerLive "Done" (bindings index) 4098 (by decide) (by decide)
    let derived := ReturnDerivation.evaluate (space := context) (comparison := .semantic)
      innerLive query Atom.undefinedType done (bindings index) 4099 [request index]
      (by decide) (by simp [IsEmptyOrErrorRel,IsErrorRel,done,Atom.empty]) child
    have ready : derived.Covered := .evaluate (accepted := by decide)
      (running := by simp [IsEmptyOrErrorRel,IsErrorRel,done,Atom.empty]) covered
    exact ⟨derived,ready⟩
  have returns : ∀ selected ∈ equationCandidates context innerLive query Atom.undefinedType incoming 4099,
      ∀ input ∈ equationInputs incoming 4099 selected, ∀ row ∈ [input],
      ∃ derived : ReturnDerivation context .semantic innerLive query Atom.undefinedType
        row.1 row.2 4099 [row], derived.Covered := by
    intro selected member input present row occurred
    obtain ⟨index,rfl,rfl⟩ := selected_request member present
    obtain rfl := List.mem_singleton.mp occurred
    exact receiver index
  choose returns covered using returns
  obtain ⟨derived,ready⟩ := CallDerivation.coveredEquations (space := context)
    innerLive "pick" [a,a] Atom.undefinedType incoming 4099 (fun _ input => [input])
    (fun _ _ row => [row]) (by decide) (by decide) (by decide) (by decide +kernel)
    (by
      intro selected member
      change selected ∈ equationCandidates context innerLive query Atom.undefinedType incoming 4099 at member
      rw [queried] at member
      simp only [List.mem_cons,List.not_mem_nil,or_false] at member
      rcases member with rfl | rfl
      · exact inputs_covered 0
      · exact inputs_covered 1)
    (by decide +kernel) producers returns covered
  have joined : ((equationCandidates context innerLive query Atom.undefinedType incoming 4099).flatMap
      fun selected => (equationInputs incoming 4099 selected).flatMap fun input =>
        [input].flatMap fun row => [row]) = innerAnswers := by
    rw [queried]
    simp only [List.flatMap_cons,List.flatMap_nil,prepared,List.append_nil,List.singleton_append,innerAnswers]
  rw [← joined]
  exact ⟨derived,ready⟩

theorem inner_tuple_admitted :
    ∃ derived : TupleDerivation context .semantic (Atom.undefinedType::innerLive) query incoming 4100
      [(query,incoming)], derived.Covered := by
  have last := tuple_single (a::.symbol "pick"::Atom.undefinedType::innerLive) a incoming 4097
    [(a,incoming)] (symbol_admitted _ "A" incoming 4096 (by decide) (by decide))
  have rest := tuple_cons (.symbol "pick"::Atom.undefinedType::innerLive) a a [] incoming incoming
    4098 a [(.expression [a],incoming)] rfl
    (symbol_admitted _ "A" incoming 4097 (by decide) (by decide)) (by simpa [HE.tupleSingleton,isEmptyOrError,isEmptyAtom,isErrorAtom,a,Atom.empty] using last)
  have whole := tuple_cons (Atom.undefinedType::innerLive) (.symbol "pick") a [a] incoming incoming
    4099 (.symbol "pick") [(.expression [a,a],incoming)] rfl
    (symbol_admitted _ "pick" incoming 4098 (by decide) (by decide))
    (by simpa [RecursiveTasks.tupleTail,atomElements,isEmptyOrError,isEmptyAtom,isErrorAtom,a,Atom.empty] using rest)
  simpa [RecursiveTasks.tupleTail,atomElements,query,isEmptyOrError,isEmptyAtom,isErrorAtom,a,Atom.empty] using whole

theorem inner_admitted :
    ∃ derived : AtomDerivation context .semantic innerLive query Atom.undefinedType incoming 4102
      innerAnswers, derived.Covered := by
  obtain ⟨tuple,tupleCovered⟩ := inner_tuple_admitted
  obtain ⟨call,callCovered⟩ := inner_call_admitted
  have calls : ∀ row ∈ [(query,incoming)], CallDerivation context .semantic innerLive row.1
      Atom.undefinedType row.2 4100 innerAnswers := by
    intro row member
    obtain rfl := List.mem_singleton.mp member
    exact call
  have ready : ∀ row member, (calls row member).Covered := by
    intro row member
    obtain rfl := List.mem_singleton.mp member
    exact callCovered
  have derived := AtomDerivation.untypedTuple (space := context) (comparison := .semantic)
    innerLive (.symbol "pick") [a,a] Atom.undefinedType incoming 4099 [(query,incoming)]
    (fun _ => innerAnswers) rfl (by decide) (by decide) (symbol_lookup "pick") tuple calls
  have covered : derived.Covered := AtomDerivation.Covered.untypedTuple
    (clean := rfl) (notRaw := by decide) (notExpr := by decide)
    (types := symbol_lookup "pick") tupleCovered ready
  have aggregation : successPriority ([(query,incoming)].flatMap fun _ => innerAnswers) = innerAnswers := by
    decide +kernel
  rw [← aggregation]
  exact ⟨derived,covered⟩

/-- A constructor head remains absent independently of the fresh spellings
chosen for either stored nonlinear rule. -/
theorem box_absent (scope : List Atom) (state : Bindings) :
    EquationQueryNoMatchRel context scope answer state := by
  rintro freshLeft freshRight matched ⟨rawLeft,rawRight,stored,renamed,matchedRule⟩
  have storedShape : rawLeft = pattern ∧ rawRight = done := by
    simpa only [context,Space.ofList,rule,List.mem_cons,List.not_mem_nil,or_false,or_self,
      Atom.expression.injEq,List.cons.injEq,and_true,true_and] using stored
  rcases storedShape with ⟨rfl,rfl⟩
  obtain ⟨rename,_,leftRenamed,_,_⟩ := renamed
  have shape := EquationFreshening.alphaRename_eq leftRenamed
  simp only [pattern,renameTypeVars,List.map_cons,List.map_nil] at shape
  subst freshLeft
  cases matchedRule with
  | expression children =>
    cases children with
    | cons first _ _ =>
      exact Spec.Match.Merge.symbol_mismatch_not_match (by decide) _ first

theorem outer_call_admitted (index : Fin 2) :
    ∃ derived : CallDerivation context .semantic live answer Atom.undefinedType (bindings index) 4104
      [(answer,bindings index)], derived.Covered := by
  have empty : equationCandidates context live answer Atom.undefinedType (bindings index) 4103 = [] := by
    fin_cases index <;> decide +kernel
  let derived := CallDerivation.unreduced (space := context) (comparison := .semantic)
    live "Box" [done] Atom.undefinedType (bindings index) 4103 (by decide) rfl (by decide) empty (box_absent _ _)
  have covered : derived.Covered := .unreduced (ordinary := by decide)
    (nonembedded := rfl) (clean := by decide) (empty := empty) (absent := box_absent _ _)
    (by fin_cases index <;> decide +kernel)
  exact ⟨derived,covered⟩

theorem outer_tuple_admitted :
    ∃ derived : TupleDerivation context .semantic (Atom.undefinedType::live) term incoming 4104 answers,
      derived.Covered := by
  have singleton := tuple_single innerLive query incoming 4102 innerAnswers inner_admitted
  have whole := tuple_cons (Atom.undefinedType::live) (.symbol "Box") query [] incoming incoming
    4103 (.symbol "Box") (innerAnswers.map HE.tupleSingleton) rfl
    (symbol_admitted _ "Box" incoming 4102 (by decide) (by decide)) singleton
  simpa [RecursiveTasks.tupleTail,innerAnswers,request,HE.tupleSingleton,done,
    isEmptyOrError,isEmptyAtom,isErrorAtom,Atom.empty,atomElements,term,answer,answers] using whole

/-- Ordinary evaluation traverses an untyped tuple, executes both physical
nonlinear equations, and rebuilds the enclosing constructor at each reached frame. -/
theorem admitted : ∃ derived : AtomDerivation context .semantic live term Atom.undefinedType
    incoming 4106 answers, derived.Covered := by
  obtain ⟨tuple,tupleCovered⟩ := outer_tuple_admitted
  have calls : ∀ row ∈ answers, ∃ derived : CallDerivation context .semantic live row.1
      Atom.undefinedType row.2 4104 [row], derived.Covered := by
    intro row member
    simp only [answers,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl
    · exact outer_call_admitted 0
    · exact outer_call_admitted 1
  choose calls ready using calls
  have derived := AtomDerivation.untypedTuple (space := context) (comparison := .semantic)
    live (.symbol "Box") [query] Atom.undefinedType incoming 4103 answers (fun row => [row])
    rfl (by decide) (by decide) (symbol_lookup "Box") tuple calls
  have covered : derived.Covered := AtomDerivation.Covered.untypedTuple
    (clean := rfl) (notRaw := by decide) (notExpr := by decide)
    (types := symbol_lookup "Box") tupleCovered ready
  have aggregation : successPriority (answers.flatMap fun row => [row]) = answers := by decide +kernel
  rw [← aggregation]
  exact ⟨derived,covered⟩

theorem checked_completion (earned : ResultSet) :
    ∃ budget, ∀ later, (FirstSuccessRecursiveExecution.Checked.machine HE.GroundedDispatch.none).run
      (budget+later) ⟨context,.work (.atom term Atom.undefinedType incoming 4106 live),[],earned⟩ =
      (answers,.finished ⟨context,.returning [],[],earned++answers⟩) := by
  obtain ⟨derived,covered⟩ := admitted
  exact derived.checked_completed covered earned

theorem source_occurrence (input : BindingFrame)
    (related : SourceBindingComparison.semantic.FrameRelated incoming input) (index : Fin 2) :
    ∃ output, EvalAtomRawRel context noHost live term Atom.undefinedType input (answer,output) ∧
      SourceBindingComparison.semantic.FrameRelated (bindings index) output := by
  obtain ⟨derived,_⟩ := admitted
  exact derived.sound (answer,bindings index) (by fin_cases index <;> simp [answers]) [] input related

theorem multiplicity_and_changed_bindings : answers.length = 2 ∧ bindings 0 ≠ bindings 1 ∧
    (bindings 0).lookup "x#0" = some a ∧ (bindings 1).lookup "x#1" = some a ∧
    (bindings 0).lookup "keep" = some kept ∧ (bindings 1).lookup "keep" = some kept := by
  decide +kernel

theorem initial_certificate : ReadoutCertificate incoming (CurrentStore.normalize incoming.assignments) :=
  CurrentStore.normalize_certified_of_noLoop (by decide +kernel) (by decide +kernel)

def initialFrame : BindingFrame := .selected incoming (CurrentStore.normalize incoming.assignments)
  initial_certificate

theorem initial_related : SourceBindingComparison.semantic.FrameRelated incoming initialFrame := by
  have actual := SourceBindingComparison.FrameRelated.normalized
    (entries := incoming.assignments) (by decide +kernel) (by decide +kernel)
  have normalized : CurrentStore.normalize incoming.assignments = incoming.assignments := by
    simp [CurrentStore.normalize,CurrentStore.normalizeFrom,incoming,kept,
      TypeSubst.bind,TypeSubst.erase,TypeSubst.applyAssignment]
  have native : FirstSuccessPreparedArguments.presentedBindings
      (CurrentStore.normalize incoming.assignments) = incoming := by
    rw [normalized]
    rfl
  rw [native] at actual
  exact actual

theorem source_from_actual_nonempty_caller (index : Fin 2) :
    ∃ output, EvalAtomRawRel context noHost live term Atom.undefinedType initialFrame (answer,output) ∧
      SourceBindingComparison.semantic.FrameRelated (bindings index) output :=
  source_occurrence initialFrame initial_related index

def initial : Configuration :=
  ⟨context,.work (.atom term Atom.undefinedType incoming 4106 live),[],[]⟩

def saved : Configuration :=
  ⟨context,.work (.atom (.symbol "Box") Atom.undefinedType incoming 4103
      (.expression [query]::Atom.undefinedType::live)),
    [.tupleHeads (.expression [query]) 4103 (Atom.undefinedType::live),
      .calls Atom.undefinedType 4104 live,.prepend [],.filter],[]⟩

/-- The pending nonlinear query, ordinary demand and tuple receiver are
actual retained state, before the first child publishes anything. -/
theorem actual_saved_checkpoint :
    (FirstSuccessRecursiveExecution.Checked.machine HE.GroundedDispatch.none).run 5 initial =
      ([],.exhausted saved) := rfl

theorem saved_pending_scope :
    saved.control = .work (.atom (.symbol "Box") Atom.undefinedType incoming 4103
      (.expression [query]::Atom.undefinedType::live)) ∧
    .tupleHeads (.expression [query]) 4103 (Atom.undefinedType::live) ∈ saved.stack ∧
    .calls Atom.undefinedType 4104 live ∈ saved.stack := by decide +kernel

theorem saved_resumes : ∃ budget remaining,
    (FirstSuccessRecursiveExecution.Checked.machine HE.GroundedDispatch.none).run budget saved =
      (remaining,.finished ⟨context,.returning [],[],answers⟩) ∧ remaining = answers := by
  obtain ⟨derived,covered⟩ := admitted
  simpa only [List.nil_append] using
    derived.checked_resume_completed covered [] 5 [] saved actual_saved_checkpoint

theorem shallow_is_not_finished :
    (FirstSuccessRecursiveExecution.Checked.machine HE.GroundedDispatch.none).run 5 initial ≠
      ([],.finished saved) := by
  rw [actual_saved_checkpoint]
  intro impossible
  cases impossible

theorem zero_tuple_depth_suspends :
    (FirstSuccessRecursiveExecution.Checked.machine HE.GroundedDispatch.none).run 1
      ⟨context,.work (.tuple term incoming 0 live),[],[]⟩ =
      ([],.suspended .evaluationDepth ⟨context,.work (.tuple term incoming 0 live),[],[]⟩) := rfl

theorem held_atom_demand :
    ∃ derived : AtomDerivation context .semantic live term Atom.atomType incoming 1 [(term,incoming)],
      derived.Covered :=
  ⟨.leaf live term Atom.atomType incoming 0
    (Or.inr ⟨Atom.expressionType,.expression _,Or.inl rfl⟩),
    .leaf (leaf := Or.inr ⟨Atom.expressionType,.expression _,Or.inl rfl⟩)⟩

/-- A missing constructor equation is established by source head mismatch,
while a nonlinear mismatch is independently covered by the real query service. -/
theorem genuine_absence :
    EquationQueryNoMatchRel context (Atom.undefinedType::live) answer incoming ∧
    equationCandidates context live answer Atom.undefinedType incoming 4099 = [] ∧
    queryEquationsCovered (equationScope live (.expression [.symbol "pick",a,.symbol "B"])
      Atom.undefinedType incoming) context (.expression [.symbol "pick",a,.symbol "B"]) 4099 = true ∧
    equationCandidates context live (.expression [.symbol "pick",a,.symbol "B"])
      Atom.undefinedType incoming 4099 = [] := by
  exact ⟨box_absent _ _,by decide +kernel,by decide +kernel,by decide +kernel⟩

theorem annotation_refuses_untyped_guard :
    getAtomTypes (context.add (.expression [.symbol ":",.symbol "Box",
      arrow [Atom.atomType] Atom.atomType])) (.symbol "Box") ≠ [Atom.undefinedType] := by
  decide +kernel

def failed : Atom := .expression [.symbol "Error",.symbol "Stopped"]
def failedTail : Atom := .expression [.symbol "Box",failed]

theorem stopped_head_admitted (value : Atom) (stopped : IsEmptyOrErrorRel value) :
    ∃ derived : TupleDerivation context .semantic live (.expression [value,query]) incoming 4
      [(value,incoming)], derived.Covered := by
  let first := AtomDerivation.leaf (space := context) (comparison := .semantic)
    (.expression [query]::live) value Atom.undefinedType incoming 2 (Or.inl stopped)
  have stop : isEmptyOrError value = true :=
    (Spec.Type.Conformance.isEmptyOrErrorRel_iff_isEmptyOrError _).mp stopped
  have children : ∀ selected ∈ [(value,incoming)], isEmptyOrError selected.1 = false →
      TupleDerivation context .semantic (selected.1::live) (.expression [query]) selected.2 3 [] := by
    intro selected member clean
    obtain rfl := List.mem_singleton.mp member
    simp [stop] at clean
  have ready : ∀ selected member clean, (children selected member clean).Covered := by
    intro selected member clean
    obtain rfl := List.mem_singleton.mp member
    simp [stop] at clean
  have derived := TupleDerivation.cons (space := context) (comparison := .semantic)
    live value query [] incoming 3 [(value,incoming)] (fun _ => []) first children
  have covered : derived.Covered := .cons (.leaf (leaf := Or.inl stopped)) ready
  have aggregation : tupleOutputs [(value,incoming)] (fun _ => []) = [(value,incoming)] := by
    simp [tupleOutputs,stop]
  rw [← aggregation]
  exact ⟨derived,covered⟩

theorem empty_head_does_not_run_tail :
    ∃ derived : TupleDerivation context .semantic live (.expression [Atom.empty,query]) incoming 4
      [(Atom.empty,incoming)], derived.Covered :=
  stopped_head_admitted Atom.empty (Or.inl rfl)

theorem error_head_does_not_run_tail :
    ∃ derived : TupleDerivation context .semantic live (.expression [failed,query]) incoming 4
      [(failed,incoming)], derived.Covered :=
  stopped_head_admitted failed (Or.inr ⟨[.symbol "Stopped"],rfl⟩)

theorem error_tail_admitted :
    ∃ derived : AtomDerivation context .semantic live failedTail Atom.undefinedType incoming 4106
      [(failed,incoming)], derived.Covered := by
  have stopped : IsEmptyOrErrorRel failed := Or.inr ⟨[.symbol "Stopped"],rfl⟩
  have leaf : ∃ derived : AtomDerivation context .semantic innerLive failed Atom.undefinedType incoming 4102
      [(failed,incoming)], derived.Covered :=
    ⟨.leaf _ _ _ _ 4101 (Or.inl stopped),.leaf (leaf := Or.inl stopped)⟩
  have singleton := tuple_single innerLive failed incoming 4102 [(failed,incoming)] leaf
  have whole := tuple_cons (Atom.undefinedType::live) (.symbol "Box") failed [] incoming incoming
    4103 (.symbol "Box") [(failed,incoming)] rfl
    (symbol_admitted _ "Box" incoming 4102 (by decide) (by decide))
    (by simpa [innerLive,HE.tupleSingleton,failed,isEmptyOrError,isErrorAtom] using singleton)
  have tupleAdmission : ∃ derived : TupleDerivation context .semantic (Atom.undefinedType::live)
      failedTail incoming 4104 [(failed,incoming)], derived.Covered := by
    simpa [RecursiveTasks.tupleTail,failed,failedTail,isEmptyOrError,isErrorAtom] using whole
  obtain ⟨tuple,tupleCovered⟩ := tupleAdmission
  have calls : ∀ row ∈ [(failed,incoming)], CallDerivation context .semantic live row.1
      Atom.undefinedType row.2 4104 [row] := by
    intro row member
    obtain rfl := List.mem_singleton.mp member
    exact .errorPassthrough live failed Atom.undefinedType incoming 4103 ⟨[.symbol "Stopped"],rfl⟩
  have ready : ∀ row member, (calls row member).Covered := by
    intro row member
    obtain rfl := List.mem_singleton.mp member
    exact .errorPassthrough (error := ⟨[.symbol "Stopped"],rfl⟩)
  have derived := AtomDerivation.untypedTuple (space := context) (comparison := .semantic)
    live (.symbol "Box") [failed] Atom.undefinedType incoming 4103 [(failed,incoming)] (fun row => [row])
    rfl (by decide) (by decide) (symbol_lookup "Box") tuple calls
  have covered : derived.Covered := .untypedTuple (clean := rfl) (notRaw := by decide)
    (notExpr := by decide) (types := symbol_lookup "Box") tupleCovered ready
  have aggregation : successPriority ([(failed,incoming)].flatMap fun row => [row]) = [(failed,incoming)] := rfl
  rw [← aggregation]
  exact ⟨derived,covered⟩

theorem stopped_tail_source :
    ∃ output, EvalAtomRawRel context noHost live failedTail Atom.undefinedType initialFrame (failed,output) ∧
      SourceBindingComparison.semantic.FrameRelated incoming output := by
  obtain ⟨derived,_⟩ := error_tail_admitted
  exact derived.sound (failed,incoming) (by simp) [] initialFrame initial_related

theorem error_is_not_wrapped :
    [(failed,incoming)] ≠ [(failedTail,incoming)] := by decide +kernel

#print axioms TupleDerivation.realizes
#print axioms TupleDerivation.sound
#print axioms TupleDerivation.covered_realizes
#print axioms AtomDerivation.checked_completed
#print axioms AtomDerivation.checked_resume_completed
#print axioms source_from_actual_nonempty_caller
#print axioms checked_completion
#print axioms saved_resumes
#print axioms stopped_tail_source
#print axioms genuine_absence
#print axioms annotation_refuses_untyped_guard

end Mettapedia.Languages.MeTTa.HE.FirstSuccessSourceExecution.UntypedTupleControls
end


section
set_option autoImplicit false
set_option maxRecDepth 14000
set_option maxHeartbeats 4000000

namespace Mettapedia.Languages.MeTTa.HE.FirstSuccessSourceExecution.NestedPriorityControls
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Spec.Eval Spec.Eval.Steps Spec.Type Spec.Type.Presentation
open RecursiveTasks RecursiveMachine FirstSuccessRecursiveExecution

/-- One child has a success and an error; a later child has only an error.
The standalone MeTTa discriminator uses these same three equations. -/
def mixed : Atom := .expression [.symbol "mixed"]
def later : Atom := .expression [.symbol "later"]
def earlyError : Atom := .expression [.symbol "Error",.symbol "Early",.symbol "Failed"]
def lateError : Atom := .expression [.symbol "Error",.symbol "Later",.symbol "Failed"]
def context : Space := Space.ofList [
  .expression [.symbol "=",mixed,.symbol "Good"],
  .expression [.symbol "=",mixed,earlyError],
  .expression [.symbol "=",later,lateError]]
def query : Atom := .expression [.symbol "Box",mixed,later]

private theorem symbol_lookup (name : String) :
    getAtomTypes context (.symbol name) = [Atom.undefinedType] := rfl

private theorem symbol_raw (live : List Atom) (name : String) (clean : name ≠ "Empty") :
    EvalAtomRawRel context noHost live (.symbol name) Atom.undefinedType Bindings.empty
      (.symbol name,Bindings.empty) := by
  exact symbol_cast_spec context name Atom.undefinedType Bindings.empty 4100 [] []
    Atom.undefinedType clean (by decide) (by decide) (symbol_lookup name)
    rfl rfl (by simp) (by simp) (Or.inl rfl) (by decide) live []

private theorem mixed_equation (live : List Atom) :
    EquationQueryCandidateRel context (Atom.undefinedType::live) mixed Bindings.empty
      earlyError Bindings.empty ∧
      BindingFrame.Materialization (BindingFrame.historical Bindings.empty) earlyError earlyError := by
  have evidence : EquationBodyEvidence context live mixed Atom.undefinedType Bindings.empty
      (earlyError,Bindings.empty) (earlyError,Bindings.empty) := by
    apply EquationBodyEvidence.of_closed_match 1 mixed earlyError rfl rfl rfl
      (by simp [earlyError,TypeSubst.typeVars,TypeSubst.typeVarsList]) rfl
      (by simp [TypeSubst.Normal,TypeSubst.keys,Bindings.empty]) 12 12 12
    · change Bindings.empty ∈ matchAtoms mixed mixed 12
      decide +kernel
    · decide +kernel
    · rfl
    · decide +kernel
  obtain ⟨output,related,⟨position,left,right,matched,_rhs,occurrence⟩,materialized⟩ :=
    evidence.transport (BindingFrame.historical Bindings.empty) (.refl _)
  have outputEmpty : output = BindingFrame.historical Bindings.empty := by
    have assignments := List.perm_nil.mp related.related.assignments.symm
    have equalities := List.perm_nil.mp related.related.equalities.symm
    have bindingsEmpty : output.bindings = Bindings.empty :=
      show (⟨output.bindings.assignments,output.bindings.equalities⟩ : Bindings) = Bindings.empty by
        rw [assignments,equalities]
        rfl
    exact related.historical_eq.trans (congrArg BindingFrame.historical bindingsEmpty)
  subst output
  exact ⟨occurrence.candidate,materialized⟩

private theorem untyped_error_raw (live : List Atom) (name : String) (arguments : List Atom)
    (clean : name ≠ "Error")
    (tuple : InterpretTupleRel context noHost (Atom.undefinedType::live)
      (.expression (.symbol name::arguments)) Bindings.empty (earlyError,Bindings.empty)) :
    EvalAtomRawRel context noHost live (.expression (.symbol name::arguments))
      Atom.undefinedType Bindings.empty (earlyError,Bindings.empty) := by
  apply EvalAtomRawRel.interpretError _ _ Atom.expressionType _ _
  · simp [IsEmptyOrErrorRel,IsErrorRel,Atom.empty,clean]
  · exact .expression _
  · decide
  · exact ⟨_,_,rfl⟩
  · apply InterpretExpressionRel.tuplePath _ _ (.symbol name) arguments
      [Atom.undefinedType] [Atom.undefinedType] [] _ _ _ rfl
    · exact FirstSuccessSourceReplies.source_types context (.symbol name)
    · rfl
    · exact .nonFunctionExhausted (by rintro ⟨_,_,impossible⟩; cases impossible) .nil
    · exact tuple
    · exact .errorPassthrough _ _ _ ⟨[.symbol "Early",.symbol "Failed"],rfl⟩
  · exact ⟨[.symbol "Early",.symbol "Failed"],rfl⟩

/-- The historical raw child judgment admits the early error. Its tuple
parent consumes that raw result before applying success priority. -/
theorem raw_child_early (live : List Atom) :
    EvalAtomRawRel context noHost live mixed Atom.undefinedType Bindings.empty
      (earlyError,Bindings.empty) := by
  apply EvalAtomRawRel.interpretError _ _ Atom.expressionType _ _
  · simp [mixed,IsEmptyOrErrorRel,IsErrorRel,Atom.empty]
  · exact .expression _
  · decide
  · exact ⟨_,_,rfl⟩
  · apply InterpretExpressionRel.tuplePath _ _ (.symbol "mixed") []
      [Atom.undefinedType] [Atom.undefinedType] [] _ (mixed,Bindings.empty) _ rfl
    · exact FirstSuccessSourceReplies.source_types context (.symbol "mixed")
    · rfl
    · exact .nonFunctionExhausted (by rintro ⟨_,_,impossible⟩; cases impossible) .nil
    · exact .singleton _ _ _ (symbol_raw _ "mixed" (by decide))
        (by simp [IsEmptyOrErrorRel,IsErrorRel,Atom.empty])
    · obtain ⟨selected,materialized⟩ := mixed_equation live
      apply CallRel.equation mixed Atom.undefinedType earlyError earlyError
        (BindingFrame.historical Bindings.empty) (BindingFrame.historical Bindings.empty)
        (earlyError,BindingFrame.historical Bindings.empty)
        (earlyError,BindingFrame.historical Bindings.empty)
      · simp [mixed,IsErrorRel]
      · exact ⟨by rintro ⟨_,_,_,impossible⟩; exact impossible,rfl⟩
      · exact selected
      · exact .same .renew _
      · exact materialized
      · exact .raw _ _ _ (by simp [Minimal.IsFunction,earlyError])
      · exact .stopped _ _ _ _ (Or.inr ⟨[.symbol "Early",.symbol "Failed"],rfl⟩)
  · exact ⟨[.symbol "Early",.symbol "Failed"],rfl⟩

/-- The old outer-only judgment consequently has a raw parent derivation
that propagates Early without evaluating the later child. -/
theorem raw_parent_early :
    EvalAtomRawRel context noHost [] query Atom.undefinedType Bindings.empty
      (earlyError,Bindings.empty) := by
  apply untyped_error_raw [] "Box" [mixed,later] (by decide)
  apply InterpretTupleRel.tailError _ _ _ (.symbol "Box",Bindings.empty)
    (earlyError,Bindings.empty) (by simp)
  · exact symbol_raw _ "Box" (by decide)
  · simp [IsEmptyOrErrorRel,IsErrorRel,Atom.empty]
  · apply InterpretTupleRel.headError _ _ _ _ (by simp)
    · exact raw_child_early _
    · exact Or.inr ⟨[.symbol "Early",.symbol "Failed"],rfl⟩
  · exact Or.inr ⟨[.symbol "Early",.symbol "Failed"],rfl⟩

def initial : Configuration :=
  Configuration.initial context (.atom query Atom.undefinedType Bindings.empty 64 [])

private def completedView
    (result : ResultSet × Mettapedia.GSLT.Distinction.ProductiveBlocks.Outcome
      Configuration Configuration RecursiveMachine.Checked.ResourceRequest) :
    Option (ResultSet × Configuration) :=
  match result with
  | (events,.finished final) => some (events,final)
  | _ => none

private theorem completedView_exact (result) (events : ResultSet) (final : Configuration) :
    completedView result = some (events,final) ↔ result = (events,.finished final) := by
  rcases result with ⟨actual,outcome⟩
  cases outcome <;> simp [completedView,Prod.mk.injEq]

/-- Every child publishes before its caller resumes. The checked retained
machine finishes with Later only, matching the reference engines. -/
theorem checked_late_only :
    (FirstSuccessRecursiveExecution.Checked.machine HE.GroundedDispatch.none).run 200 initial =
      ([(lateError,Bindings.empty)],
        .finished ⟨context,.returning [],[],[(lateError,Bindings.empty)]⟩) := by
  apply (completedView_exact _ _ _).mp
  decide +kernel

/-- The same completed observation holds under HE's scoped invocation-type
policy; this discriminator does not rely on the literal-annotation profile. -/
theorem checked_scoped_late_only :
    (FirstSuccessRecursiveExecution.Checked.machine HE.GroundedDispatch.none scopedTypes).run 200 initial =
      ([(lateError,Bindings.empty)],
        .finished ⟨context,.returning [],[],[(lateError,Bindings.empty)]⟩) := by
  apply (completedView_exact _ _ _).mp
  decide +kernel

/-- Atom-support completeness against the historical outer-only source
judgment is impossible for this completed run. No representation or choice
of binding representatives can repair the missing publication boundary. -/
theorem outer_only_source_cannot_cover_checked_run :
    ¬(∀ result, EvalRel context noHost [] query Atom.undefinedType Bindings.empty result →
      result.1 ∈ ((FirstSuccessRecursiveExecution.Checked.machine
        HE.GroundedDispatch.none scopedTypes).run 200 initial).1.map Prod.fst) := by
  rw [checked_scoped_late_only]
  change ¬(∀ result, EvalRel context noHost [] query Atom.undefinedType Bindings.empty result →
    result.1 ∈ [lateError])
  apply EvalRel.not_covered_by_errors raw_parent_early
  · intro value member
    obtain rfl := List.mem_singleton.mp member
    exact ⟨[.symbol "Later",.symbol "Failed"],rfl⟩
  · decide

end Mettapedia.Languages.MeTTa.HE.FirstSuccessSourceExecution.NestedPriorityControls

namespace Mettapedia.Languages.MeTTa.HE.BindingSourceAgreement

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Spec.Type Spec.Type.RuntimeRefinement Spec.Bindings.ScopeObservation
open Spec.Type.Presentation.Exact
open Spec.Eval.Completed (TypeMatchingPolicy)
open Mettapedia.Languages.MeTTa.HE.Spec.Match.SolutionTheory

/-- The complete ordered family of fresh type instances survives a change of
binding presentation. The target may protect fewer enclosing names; every
candidate still avoids all earlier instances and the complete input support. -/
theorem scopedTypeLookup {native independent : Bindings}
    (input : BindingSourceAgreement native independent)
    {outer inner : List String} (included : ∀ name ∈ inner, name ∈ outer)
    {space : Space} {subject expected : Atom} {candidates : List Atom}
    (queried : Spec.Eval.scopedTypeLookup outer space native subject expected candidates) :
    Spec.Eval.scopedTypeLookup inner space independent subject expected candidates := by
  obtain ⟨raw, types, variants⟩ := queried
  refine ⟨raw, types, variants.restrict ?_⟩
  intro name member
  simp only [Spec.Eval.invocationTypeScope, List.mem_append, or_assoc] at member ⊢
  rcases member with inherited | syntaxNames | bound
  · exact Or.inl (included name inherited)
  · exact Or.inr (Or.inl syntaxNames)
  · exact Or.inr (Or.inr ((input.support name).mpr bound))

theorem scopedTypeLookup_iff {native independent : Bindings}
    (input : BindingSourceAgreement native independent)
    (scope : List String) (space : Space) (subject expected : Atom) (candidates : List Atom) :
    Spec.Eval.scopedTypeLookup scope space native subject expected candidates ↔
      Spec.Eval.scopedTypeLookup scope space independent subject expected candidates :=
  ⟨input.scopedTypeLookup (fun _ member => member),
    input.symm.scopedTypeLookup (fun _ member => member)⟩

/-- A complete finite cast changes binding representation without changing
the first successful type occurrence or any failure occurrence. The query
law concerns the one actual ordered lookup, not evaluator correctness.
Reached binding theories and their complete freshening support are paired
occurrence by occurrence; materializer equality remains a separate law. -/
theorem typeCastBatch_finite {native independent : Bindings}
    (input : BindingSourceAgreement native independent)
    (nativeShape : HEAssignmentsNonVariable native)
    (sourceShape : HEAssignmentsNonVariable independent)
    {space : Space} {atom expected : Atom} {results : ResultSet}
    {nativeLookup sourceLookup : TypeLookupRel}
    (completed : TypeCastBatchRel space atom expected native results
      (lookup := nativeLookup) (matching := TypeMatchingPolicy.Rel .finite))
    (query : ∀ types, nativeLookup native atom expected types →
      sourceLookup independent atom expected types) :
    ∃ sourceResults,
      TypeCastBatchRel space atom expected independent sourceResults
        (lookup := sourceLookup) (matching := TypeMatchingPolicy.Rel .finite) ∧
      List.Forall₂ (fun left right : ResultPair =>
        left.1 = right.1 ∧ BindingSourceAgreement left.2 right.2) results sourceResults ∧
      ∀ result ∈ sourceResults, HEAssignmentsNonVariable result.2 := by
  cases completed with
  | @success _ _ types earlier later actual output queried selected rejected matched =>
      obtain ⟨sourceOutput, sourceMatch, related, shape, model⟩ :=
        input.typeMatch_finite sourceShape matched.1 matched.2
      refine ⟨[(atom, sourceOutput)],
        .success (query types queried) selected ?_ ⟨sourceMatch, model⟩,
        .cons ⟨rfl, related⟩ .nil, ?_⟩
      · intro prior member candidate accepted
        obtain ⟨nativeOutput, nativeMatch, _, _, nativeModel⟩ :=
          input.symm.typeMatch_finite nativeShape accepted.1 accepted.2
        exact rejected prior member nativeOutput ⟨nativeMatch, nativeModel⟩
      · intro result member
        obtain rfl := List.mem_singleton.mp member
        exact shape
  | @failure _ _ types queried rejected =>
      refine ⟨types.map (fun actual => (mkError atom (.badType expected actual), independent)),
        .failure (query types queried) ?_, ?_, ?_⟩
      · intro actual member candidate accepted
        obtain ⟨nativeOutput, nativeMatch, _, _, nativeModel⟩ :=
          input.symm.typeMatch_finite nativeShape accepted.1 accepted.2
        exact rejected actual member nativeOutput ⟨nativeMatch, nativeModel⟩
      · clear queried rejected
        induction types with
        | nil => exact .nil
        | cons actual types ih => exact .cons ⟨rfl, input⟩ ih
      · intro result member
        obtain ⟨actual, _, rfl⟩ := List.mem_map.mp member
        exact sourceShape

/-- The concrete scoped source service discharges the local query law. This
preserves its complete mutually fresh candidate family, first success and
duplicate failures under a changed constraint representation. -/
theorem typeCastBatch_scoped_finite {native independent : Bindings}
    (input : BindingSourceAgreement native independent)
    (nativeShape : HEAssignmentsNonVariable native)
    (sourceShape : HEAssignmentsNonVariable independent)
    {outer inner : List String} (included : ∀ name ∈ inner, name ∈ outer)
    {space : Space} {atom expected : Atom} {results : ResultSet}
    (completed : TypeCastBatchRel space atom expected native results
      (lookup := Spec.Eval.scopedTypeLookup outer space)
      (matching := TypeMatchingPolicy.Rel .finite)) :
    ∃ sourceResults,
      TypeCastBatchRel space atom expected independent sourceResults
        (lookup := Spec.Eval.scopedTypeLookup inner space)
        (matching := TypeMatchingPolicy.Rel .finite) ∧
      List.Forall₂ (fun left right : ResultPair =>
        left.1 = right.1 ∧ BindingSourceAgreement left.2 right.2) results sourceResults ∧
      ∀ result ∈ sourceResults, HEAssignmentsNonVariable result.2 :=
  input.typeCastBatch_finite nativeShape sourceShape completed
    (fun _ queried => input.scopedTypeLookup included queried)

end Mettapedia.Languages.MeTTa.HE.BindingSourceAgreement

namespace Mettapedia.Languages.MeTTa.HE.FirstSuccessSourceExecution.TypeMatchTransportControls

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Spec.Eval Spec.Eval.Completed
open Spec.Type Spec.Type.RuntimeRefinement Spec.Bindings.ScopeObservation
open Spec.Type.Presentation Spec.Type.Presentation.Theory Spec.Type.Presentation.BindingTheory
open QueryBindingProjection.AliasReadout.Controls

private def leftTable : TypeSubst := [("a", .var "b")]

private theorem leftPresentation :
    AppliedTypePresentationMatchRel [] (.var "a") (.var "b") leftTable := by
  apply AppliedTypePresentationMatchRel.ordinary
    (TypeSubst.apply_empty (.var "a")) (TypeSubst.apply_empty (.var "b"))
  simpa [leftTable, TypeSubst.bind, TypeSubst.apply, TypeSubst.lookup, TypeSubst.erase] using
    (AppliedReducedTypeMatchRel.bindLeft
      (substitution := []) (name := "a") (right := .var "b") (by decide))

private theorem leftCertificate : ReadoutCertificate forwardAlias leftTable := by
  apply ReadoutCertificate.of_fold
  change EquationListPresentationRel [(.var "a", .var "b")] [] leftTable
  exact .cons leftPresentation (.nil _)

private def leftFrame : Frame := by
  refine ⟨forwardAlias, [("a", .var "b")], ?_⟩
  simpa only [Entry.Value.eraseEnvironment, List.map_cons, List.map_nil, Entry.Value.erase,
    leftTable] using leftCertificate

/-- The maintained matcher really returns this alias class and its literal
materializer keeps the first representative. The read is locally covered. -/
theorem actual_variable_match_and_materialization :
    matchTypes (.var "a") (.var "b") Bindings.empty 8 = [forwardAlias] ∧
      forwardAlias.applyFull (.var "a") 8 = .var "a" ∧
      forwardAlias.applyFullCovered (.var "a") 8 = true := by
  decide +kernel

/-- The independently certified contextual unifier is a real finite state.
Its left-binding representative is different from the maintained alias read. -/
theorem contextual_variable_match (policy : Entry.RebuildPolicy) :
    Entry.Value.UnifyRel policy [] (.var "a") (.var "b") leftFrame.environment := by
  apply Entry.Value.UnifyRel.ordinary
  simpa [leftFrame, Entry.Value.substitute, Entry.Value.resolve, Entry.Value.bind,
    List.lookup] using
    (Entry.Value.AppliedUnifyRel.bindLeft (policy := policy) (environment := []) (name := "a")
      (right := .var "b") (by simp [Entry.Value.erase, TypeSubst.typeVars]))

/-- Literal covered-read agreement is too strong for this actual alias
operation. This refutes a candidate representation relation, not the equality
of the underlying binding theories or a language implementation. -/
theorem variable_match_has_no_literal_frame_transport (policy : Entry.RebuildPolicy)
    (after : Frame)
    (unified : Entry.Value.UnifyRel policy [] (.var "a") (.var "b") after.environment) :
    ¬ SourceBindingComparison.semantic.FrameRelated forwardAlias after.source := by
  have erased : AppliedTypePresentationMatchRel [] (.var "a") (.var "b")
      (Entry.Value.eraseEnvironment after.environment) := by
    simpa only [Entry.Value.eraseEnvironment, List.map_nil, Entry.Value.erase] using unified.erases
  have table := erased.output_eq leftPresentation
  rcases after with ⟨bindings, environment, certificate⟩
  intro related
  cases related with
  | semantic _ _ reads =>
      have same := reads (.var "a") 8 actual_variable_match_and_materialization.2.2
      rw [table, actual_variable_match_and_materialization.2.1] at same
      simp [leftTable, TypeSubst.apply, TypeSubst.lookup] at same

/-- The actual alias materializer and certified source table have the same
joint public constraint observation, including the repeated returned variable.
The representative counterexample does not refute this semantic observer. -/
theorem variable_match_joint_public_readout :
    observedTuples forwardAlias
        ([Atom.var "a", .var "b", .var "a"].map fun atom => forwardAlias.applyFull atom 8) =
      observedTuples forwardAlias
        ([Atom.var "a", .var "b", .var "a"].map leftTable.apply) := by
  have actual :
      ([Atom.var "a", .var "b", .var "a"].map fun atom => forwardAlias.applyFull atom 8) =
        [.var "a", .var "a", .var "a"] := by decide +kernel
  rw [actual]
  have joint : observedTuples forwardAlias [Atom.var "a", .var "a", .var "a"] =
      observedTuples forwardAlias [Atom.var "b", .var "b", .var "b"] := by
    apply observedTuples_congr_models
    intro model satisfied
    have aliasEquality := satisfied.2 "a" "b" (by simp [forwardAlias])
    simp only [List.map_cons, List.map_nil, applyTypeValuation]
    rw [aliasEquality]
  simpa [leftTable, TypeSubst.apply, TypeSubst.lookup] using joint

/-- Wildcard matching alone does not certify a finite completed cast: an
inconsistent caller must not be admitted through the wildcard branch. -/
theorem wildcard_without_model_is_not_finite :
    TypeMatchRel Atom.undefinedType (.symbol "A") inconsistent inconsistent ∧
      ¬ TypeMatchingPolicy.Rel .finite Atom.undefinedType (.symbol "A")
        inconsistent inconsistent := by
  refine ⟨.undefinedLeft _ _, ?_⟩
  rintro ⟨_, model⟩
  exact inconsistent_has_no_model model

end Mettapedia.Languages.MeTTa.HE.FirstSuccessSourceExecution.TypeMatchTransportControls
end


namespace Mettapedia.Languages.MeTTa.HE.FirstSuccessSourceExecution.CompletedQueryControls
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Spec.Eval.Steps RecursiveTasks FirstSuccessRecursiveExecution

/-- Independently covered source copies agree with the actual whole query
and keep their distinct physical origins. -/
theorem complete_source_and_native_frontier :
    ∃ works, EquationFrontierRel FrontierControls.context [] (.symbol "a") Bindings.empty works ∧
      rawQueryResults FrontierControls.context (.symbol "a") Atom.undefinedType Bindings.empty 12 [] =
        works.map (fun work => (work.body,work.bindings)) ∧
      works.map EquationWork.position = [0,3] := by
  refine ⟨[FrontierControls.work 0,FrontierControls.work 3],FrontierControls.complete,?_,rfl⟩
  decide +kernel

/-- An empty depth-truncated helper result cannot certify source absence.
The source proof still accounts for both viable stored copies. -/
theorem truncated_empty_is_not_source_completion :
    rawQueryResults FrontierControls.context (.symbol "a") Atom.undefinedType Bindings.empty 0 [] = [] ∧
      ¬EquationFrontierRel FrontierControls.context [] (.symbol "a") Bindings.empty [] :=
  ⟨by decide +kernel,FrontierControls.live_copy_prevents_empty_completion⟩

/-- The actual checked machine retains the unstarted query as a resource
request. It does not publish the helper's empty list as completed failure. -/
theorem checked_query_remains_pending :
    let initial := Configuration.initial FrontierControls.context
      (.invocation .raw (.symbol "a") Bindings.empty 0 [] none)
    (Checked.machine HE.GroundedDispatch.none).run 1 initial =
      ([],.suspended .evaluationDepth initial) := by
  dsimp only
  exact Checked.blocked_run HE.GroundedDispatch.none _ .evaluationDepth 0 rfl

/-- A structural hit rejected by the caller's constraints takes the else
branch through the actual retained worker, preserving any surrounding
callers and earlier emissions. Its source absence is earned by coverage. -/
theorem post_merge_failure_retains_callers (space : Space) (live : List Atom) (caller : Option Atom) :
    Covered.Realizes space
      (.primitive (.expression [.symbol "unify",.var "x",.symbol "B",.symbol "yes",.symbol "no"])
        QueryBindingProjection.AliasReadout.Controls.groundCaller 13 live caller)
      [(.symbol "no",QueryBindingProjection.AliasReadout.Controls.groundCaller)] := by
  have derived : PrimitiveDerivation (comparison := .semantic) space live caller
      (.expression [.symbol "unify",.var "x",.symbol "B",.symbol "yes",.symbol "no"])
      QueryBindingProjection.AliasReadout.Controls.groundCaller 13
      [(.symbol "no",QueryBindingProjection.AliasReadout.Controls.groundCaller)] :=
    .unifyNoMatch live caller (.var "x") (.symbol "B") (.symbol "yes") (.symbol "no")
      QueryBindingProjection.AliasReadout.Controls.groundCaller 12 (by decide +kernel) (by decide +kernel)
  exact derived.covered_realizes

def conflictingQuery : Atom := .expression [.symbol "pick",.var "x"]
def conflictingSpace : Space := Space.ofList
  [.expression [.symbol "=",.expression [.symbol "pick",.symbol "B"],.symbol "Value"]]

/-- A whole query can have a structural candidate while its caller rejects
every prepared input. Complete source absence is earned after reconciliation. -/
theorem post_merge_query_has_complete_empty_frontier :
    equationCandidates conflictingSpace [] conflictingQuery Atom.undefinedType
        QueryBindingProjection.AliasReadout.Controls.groundCaller 12 ≠ [] ∧
      rawQueryResults conflictingSpace conflictingQuery Atom.undefinedType
        QueryBindingProjection.AliasReadout.Controls.groundCaller 12 [] = [] ∧
      EquationFrontierRel conflictingSpace [Atom.undefinedType] conflictingQuery
        QueryBindingProjection.AliasReadout.Controls.groundCaller [] := by
  let incoming := QueryBindingProjection.AliasReadout.Controls.groundCaller
  have empty : rawQueryResults conflictingSpace conflictingQuery Atom.undefinedType incoming 12 [] = [] := by
    decide +kernel
  refine ⟨by decide +kernel,empty,(covered_query_empty_iff_source_frontier (by decide +kernel) ?_).mp empty⟩
  have candidates : equationCandidates conflictingSpace [] conflictingQuery Atom.undefinedType incoming 12 =
      [(.symbol "Value",⟨[("x",.symbol "B")],[]⟩)] := by decide +kernel
  intro candidate member
  rw [candidates] at member
  obtain rfl := List.mem_singleton.mp member
  refine ⟨by decide +kernel,?_⟩
  intro merged present
  have rejected : mergeBindings ⟨[("x",.symbol "B")],[]⟩ (aliasConstraints incoming) 12 = [] := by
    decide +kernel
  rw [rejected] at present
  exact (List.not_mem_nil present).elim

end Mettapedia.Languages.MeTTa.HE.FirstSuccessSourceExecution.CompletedQueryControls

namespace Mettapedia.Languages.MeTTa.HE.FirstSuccessSourceExecution.NestedPriorityControls

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Spec.Eval Spec.Eval.Steps Spec.Type Spec.Type.Presentation
open Spec.Match.Merge
open Spec.Bindings.ScopeObservation FirstSuccessRecursiveExecution

private def frame : BindingFrame := .historical Bindings.empty

private theorem symbol_has_no_variable (symbol : String) (name : String) :
    ¬AtomOccurs (.symbol symbol) name := by intro occurs; cases occurs

private theorem symbol_list_has_no_variable (symbols : List String) (name : String) :
    ¬AtomOccurs (.expression (symbols.map Atom.symbol)) name := by
  intro occurs
  cases occurs with
  | expression member child =>
      obtain ⟨symbol,_,rfl⟩ := List.mem_map.mp member
      cases child

private theorem closed_instance (live : List Atom) (subject : Atom) (name : String) (rhs : Atom)
    (closed : ∀ key, ¬AtomOccurs rhs key) :
    AlphaVariantRel live subject Bindings.empty
      (.expression [.symbol name]) rhs (.expression [.symbol name]) rhs := by
  refine ⟨id,Function.injective_id,?_,?_,?_⟩
  · simpa only [Spec.Type.Presentation.ScopeObservation.renameTypeVars_id] using
      EquationFreshening.rename_alpha id (.expression [.symbol name])
  · simpa only [Spec.Type.Presentation.ScopeObservation.renameTypeVars_id] using
      EquationFreshening.rename_alpha id rhs
  · intro key occurs
    rcases occurs with occurs | occurs
    · exact (symbol_list_has_no_variable [name] key occurs).elim
    · exact (closed key occurs).elim

private theorem empty_logical_merge : LogicalMergeRel Bindings.empty Bindings.empty Bindings.empty := by
  refine ⟨BindingSourceAgreement.refl _,fun name => .var name,?_⟩
  simp [Spec.Type.RuntimeRefinement.TypeBindingSatisfied,Bindings.empty]

private def work (position : Nat) (name : String) (rhs : Atom) : EquationWork :=
  ⟨position,.expression [.symbol name],rhs,.expression [.symbol name],rhs,Bindings.empty⟩

private theorem row_hit (live : List Atom) (position : Nat) (name : String) (rhs : Atom)
    (closed : ∀ key, ¬AtomOccurs rhs key) :
    EquationRowResultsRel live (.expression [.symbol name]) Bindings.empty position
      (.expression [.symbol "=",.expression [.symbol name],rhs]) [work position name rhs] := by
  apply EquationRowResultsRel.hit position _ _ _ _ Bindings.empty Bindings.empty
    (closed_instance _ _ name rhs closed) _ empty_logical_merge
  exact .expression (.cons (.symSym name semanticLoopFree_empty) (.mk (.refl []) .nil) .nil)
    semanticLoopFree_empty

private theorem row_miss (live : List Atom) (position : Nat) (subject name : String) (rhs : Atom)
    (closed : ∀ key, ¬AtomOccurs rhs key) (distinct : subject ≠ name) :
    EquationRowResultsRel live (.expression [.symbol subject]) Bindings.empty position
      (.expression [.symbol "=",.expression [.symbol name],rhs]) [] := by
  apply EquationRowResultsRel.miss position _ _ _ _ (closed_instance _ _ name rhs closed)
  intro pattern body renamed matched output viable
  obtain ⟨_,_,patternRenamed,_,_⟩ := renamed
  have same : pattern = .expression [.symbol name] := by
    simpa only [Spec.Type.RuntimeRefinement.renameTypeVars,List.map_cons,List.map_nil] using
      EquationFreshening.alphaRename_eq patternRenamed
  subst pattern
  cases viable.1 with
  | expression children _ =>
      cases children with
      | cons first _ _ => exact symbol_mismatch_not_match distinct _ first

/-- Both physical clauses are covered independently before either RHS is
evaluated. The later clause is a certified miss. -/
theorem mixed_source_frontier (live : List Atom) :
    EquationFrontierRel context live mixed Bindings.empty
      [work 0 "mixed" (.symbol "Good"),work 1 "mixed" earlyError] := by
  apply EquationFrontierRel.completed (blocks :=
    [[work 0 "mixed" (.symbol "Good")],[work 1 "mixed" earlyError],[]])
  exact .cons (row_hit live 0 "mixed" (.symbol "Good") (symbol_has_no_variable "Good"))
    (.cons (row_hit live 1 "mixed" earlyError (symbol_list_has_no_variable ["Error","Early","Failed"]))
      (.cons (row_miss live 2 "mixed" "later" lateError
        (symbol_list_has_no_variable ["Error","Later","Failed"]) (by decide)) .nil))

theorem later_source_frontier (live : List Atom) :
    EquationFrontierRel context live later Bindings.empty [work 2 "later" lateError] := by
  apply EquationFrontierRel.completed (blocks := [[],[],[work 2 "later" lateError]])
  exact .cons (row_miss live 0 "later" "mixed" (.symbol "Good")
      (symbol_has_no_variable "Good") (by decide))
    (.cons (row_miss live 1 "later" "mixed" earlyError
      (symbol_list_has_no_variable ["Error","Early","Failed"]) (by decide))
      (.cons (row_hit live 2 "later" lateError
        (symbol_list_has_no_variable ["Error","Later","Failed"])) .nil))

private def SymbolQueries (lookup : Completed.CastLookup) : Prop :=
  ∀ scope name, lookup scope context Bindings.empty (.symbol name) Atom.undefinedType [Atom.undefinedType]

private theorem raw_symbol_queries : SymbolQueries Completed.rawLookup := by
  intro scope name
  exact FirstSuccessSourceReplies.source_types context (.symbol name)

private theorem scoped_symbol_queries : SymbolQueries Completed.scopedLookup := by
  intro scope name
  refine ⟨[Atom.undefinedType],FirstSuccessSourceReplies.source_types context (.symbol name),?_⟩
  exact .cons ⟨id,Function.injective_id,
    by simp [Atom.undefinedType],
    by simp [Atom.undefinedType,TypeSubst.typeVars]⟩ (.nil _)

private def completedFrame : Completed.Frame := .empty

private theorem completed_symbol (lookup : Completed.CastLookup) (queries : SymbolQueries lookup)
    (live : List Atom) (scope : List String) (name : String) (clean : name ≠ "Empty") :
    Completed.AtomRel context noHost lookup live scope (.symbol name) Atom.undefinedType completedFrame
      [(.symbol name,completedFrame)] := by
  apply Completed.AtomRel.cast (raw := [(.symbol name,Bindings.empty)])
  · simpa only [completedFrame,Completed.Frame.read_empty,Completed.Policy.unmarked,
      Spec.Eval.Entry.Value.erase,Spec.Eval.Entry.Value.status] using
      (Spec.Eval.Entry.Rel.cast (policy := .reinterpret) (status := .active)
        (by simpa [IsEmptyOrErrorRel,IsErrorRel,Atom.empty] using clean)
        (.symbol name) (by decide) (Or.inl ⟨name,rfl⟩)
        (by intro impossible; cases impossible))
  · simp only [completedFrame,Completed.Frame.read_empty,Spec.Eval.Entry.Value.erase]
    exact TypeCastBatchRel.success (space := context)
      (earlierTypes := []) (laterTypes := []) (actualType := Atom.undefinedType)
      (queries _ name) rfl (by simp) (.undefinedLeft _ _)
  · refine .cons ⟨?_,Completed.Frame.CastRenewRel.same _,?_⟩ .nil
    · simp [Completed.rawResult,Spec.Eval.Entry.Value.erase,completedFrame,Completed.Frame.empty]
    · simp [completedFrame,Spec.Eval.Entry.Value.erase]

private theorem ordinary (name : String)
    (notEmbedded : Minimal.embeddedInstruction (.expression [.symbol name]) = false) :
    NonGroundedCallRel noHost (.expression [.symbol name]) := by
  refine ⟨?_,notEmbedded⟩
  rintro ⟨_,_,_,impossible⟩
  exact impossible

private theorem unmarked_publication (original : Atom) (results : List Completed.Result)
    (active : ∀ result ∈ results, result.1.status = .active) :
    results.map (Completed.publishResult .unmarked original) = results := by
  calc
    _ = results.map id := by
      apply List.map_congr_left
      intro result present
      exact congrArg (fun value => (value,result.2))
        (Spec.Eval.Entry.Value.publish_none_active original result.2.source result.1
          (active result present))
    _ = results := List.map_id _

private theorem empty_contextual_match (left right : Spec.Eval.Entry.Value)
    (same : left.erase = right.erase) :
    Spec.Eval.Entry.Value.UnifyRel .preserve [] left right [] := by
  apply Spec.Eval.Entry.Value.UnifyRel.ordinary
  apply Spec.Eval.Entry.Value.AppliedUnifyRel.identical
  simpa only [Spec.Eval.Entry.Value.erase_substitute_environment,
    Spec.Eval.Entry.Value.eraseEnvironment,List.map_nil,TypeSubst.apply_empty] using same

private theorem nullary_completed (lookup : Completed.CastLookup) (queries : SymbolQueries lookup)
    (live : List Atom) (scope : List String) (name : String)
    (clean : name ≠ "Empty") (notError : name ≠ "Error")
    {raw published : List Completed.Result}
    (call : Completed.CallRel context noHost lookup live scope (.expression .active [.symbol name])
      Atom.undefinedType completedFrame raw)
    (priority : Mettapedia.Machines.OrderedProtocol.Completion.SuccessPriorityRel
      (fun result : Completed.Result => isErrorAtom result.1.erase)
      (raw.map (Completed.readResult .unmarked)) published)
    (active : ∀ result ∈ published, result.1.status = .active)
    (readiness : Spec.Eval.Entry.Status := .active) :
    Completed.AtomRel context noHost lookup live scope (.expression readiness [.symbol name])
      Atom.undefinedType completedFrame published := by
  have built : Completed.AtomRel context noHost lookup live scope
      (.expression readiness [.symbol name]) Atom.undefinedType completedFrame
      (published.map (Completed.publishResult .unmarked
        (completedFrame.read .unmarked (.expression readiness [.symbol name])).erase)) := by
    apply Completed.AtomRel.tuple (readiness := readiness) (operator := .symbol name) (arguments := [])
      (rows := [(.expression .active [.symbol name],completedFrame)]) (raw := raw)
    · simpa only [completedFrame,Completed.Frame.read_empty,Completed.Policy.unmarked,
        Spec.Eval.Entry.Value.erase,Spec.Eval.Entry.Value.status,List.map_cons,List.map_nil] using
        (Spec.Eval.Entry.Rel.expression (policy := .reinterpret) (status := readiness)
          (head := .symbol name) (tail := []) (expected := Atom.undefinedType)
          (by simp [IsEmptyOrErrorRel,IsErrorRel,Atom.empty,notError])
          (by decide) (Or.inl rfl))
    · simp [completedFrame]
    · simpa only [Spec.Eval.Entry.Value.erase,symbol_lookup,Multiset.coe_singleton] using
        (FirstSuccessSourceReplies.source_types context (.symbol name)).occurrences
    · simpa [Completed.tupleSingleton,isEmptyOrError,isEmptyAtom,isErrorAtom,Atom.empty,
        Spec.Eval.Entry.Value.erase,clean] using
        Completed.TupleRel.singleton (completed_symbol lookup queries (Atom.undefinedType::live) scope name clean)
    · simpa using Completed.CallsRel.cons call (.nil)
    · exact priority
  simpa only [completedFrame,Completed.Frame.read_empty,Spec.Eval.Entry.Value.erase,
    List.map_cons,List.map_nil,unmarked_publication _ _ active] using built

private theorem mixed_completed (lookup : Completed.CastLookup) (queries : SymbolQueries lookup)
    (live : List Atom) (scope : List String) (readiness : Spec.Eval.Entry.Status := .active) :
    Completed.AtomRel context noHost lookup live scope (.expression readiness [.symbol "mixed"])
      Atom.undefinedType completedFrame [(.symbol "Good",completedFrame)] := by
  apply nullary_completed lookup queries live scope "mixed" (by decide) (by decide)
    (readiness := readiness)
    (raw := [(.symbol "Good",completedFrame),(Spec.Eval.Entry.Value.ofAtom earlyError,completedFrame)])
  · apply Completed.CallRel.equations (works :=
      [work 0 "mixed" (.symbol "Good"),work 1 "mixed" earlyError])
    · simp [IsErrorRel,Spec.Eval.Entry.Value.erase]
    · simpa only [Spec.Eval.Entry.Value.erase,List.map_cons,List.map_nil] using ordinary "mixed" rfl
    · simpa only [Spec.Eval.Entry.Value.erase,List.map_cons,List.map_nil,completedFrame,
        Completed.Frame.empty,mixed] using mixed_source_frontier (Atom.undefinedType :: live)
    · simp
    · apply Completed.EquationBodiesRel.ordinary_cons (output := completedFrame)
        (children := [(.symbol "Good",completedFrame)]) rfl
      · exact empty_contextual_match _ _ (by simp [work,Spec.Eval.Entry.Value.erase])
      · simp [completedFrame,work,Spec.Eval.Entry.Value.ofAtom,Spec.Eval.Entry.Value.erase,Completed.FunctionPending,Minimal.IsFunction]
      · apply Completed.ReturnRel.evaluate
        · simp [completedFrame,work,Spec.Eval.Entry.Value.ofAtom,Spec.Eval.Entry.Value.erase,Atom.notReducible]
        · simp [completedFrame,work,Spec.Eval.Entry.Value.ofAtom,Spec.Eval.Entry.Value.erase,
            IsEmptyOrErrorRel,IsErrorRel,Atom.empty]
        · simpa only [work,completedFrame,Completed.Frame.read_empty,Spec.Eval.Entry.Value.ofAtom] using
            completed_symbol lookup queries live scope "Good" (by decide)
      · apply Completed.EquationBodiesRel.ordinary_cons (output := completedFrame)
          (children := [(Spec.Eval.Entry.Value.ofAtom earlyError,completedFrame)]) rfl
        · exact empty_contextual_match _ _ (by simp [work,Spec.Eval.Entry.Value.erase])
        · simp [completedFrame,work,Spec.Eval.Entry.Value.ofAtom,Spec.Eval.Entry.Value.erase,
            Completed.FunctionPending,Minimal.IsFunction,earlyError]
        · simp only [work,completedFrame,Completed.Frame.read_empty]
          apply Completed.ReturnRel.stopped
          simp [Spec.Eval.Entry.Value.erase_ofAtom,IsEmptyOrErrorRel,IsErrorRel,earlyError]
        · exact .nil
  · simpa [Completed.readResult,completedFrame,earlyError,isErrorAtom,
      Spec.Eval.Entry.Value.erase_ofAtom,Spec.Eval.Entry.Value.erase] using
      (Mettapedia.Machines.OrderedProtocol.Completion.SuccessPriorityRel.successes
        (isError := fun result : Completed.Result => isErrorAtom result.1.erase)
        (raw := [(.symbol "Good",completedFrame),(Spec.Eval.Entry.Value.ofAtom earlyError,completedFrame)])
        ⟨(.symbol "Good",completedFrame),by simp,by simp [Spec.Eval.Entry.Value.erase,isErrorAtom]⟩)
  · intro result present
    obtain rfl := List.mem_singleton.mp present
    rfl

private theorem later_completed (lookup : Completed.CastLookup) (queries : SymbolQueries lookup)
    (live : List Atom) (scope : List String) :
    Completed.AtomRel context noHost lookup live scope (Spec.Eval.Entry.Value.ofAtom later)
      Atom.undefinedType completedFrame [(Spec.Eval.Entry.Value.ofAtom lateError,completedFrame)] := by
  simp only [later,Spec.Eval.Entry.Value.ofAtom,List.map_cons,List.map_nil]
  apply nullary_completed lookup queries live scope "later" (by decide) (by decide)
  · apply Completed.CallRel.equations (works := [work 2 "later" lateError])
    · simp [IsErrorRel,Spec.Eval.Entry.Value.erase]
    · simpa only [Spec.Eval.Entry.Value.erase,List.map_cons,List.map_nil] using ordinary "later" rfl
    · simpa only [Spec.Eval.Entry.Value.erase,List.map_cons,List.map_nil,completedFrame,
        Completed.Frame.empty,later] using later_source_frontier (Atom.undefinedType :: live)
    · simp
    · apply Completed.EquationBodiesRel.ordinary_cons (output := completedFrame)
        (children := [(Spec.Eval.Entry.Value.ofAtom lateError,completedFrame)]) rfl
      · exact empty_contextual_match _ _ (by simp [work,Spec.Eval.Entry.Value.erase])
      · simp [completedFrame,work,Spec.Eval.Entry.Value.ofAtom,Spec.Eval.Entry.Value.erase,
          Completed.FunctionPending,Minimal.IsFunction,lateError]
      · simp only [work,completedFrame,Completed.Frame.read_empty]
        apply Completed.ReturnRel.stopped
        simp [Spec.Eval.Entry.Value.erase_ofAtom,IsEmptyOrErrorRel,IsErrorRel,lateError]
      · exact .nil
  · simp only [List.append_nil,List.map_cons,List.map_nil,Completed.readResult,
      completedFrame,Completed.Frame.read_empty]
    apply Mettapedia.Machines.OrderedProtocol.Completion.SuccessPriorityRel.allErrors
    intro result member
    simp only [List.mem_singleton] at member
    subst result
    simp [Spec.Eval.Entry.Value.erase_ofAtom,lateError,isErrorAtom]
  · intro result present
    obtain rfl := List.mem_singleton.mp present
    simp [Spec.Eval.Entry.Value.ofAtom,lateError,Spec.Eval.Entry.Value.status]

private theorem parent_completed (lookup : Completed.CastLookup) (queries : SymbolQueries lookup)
    (live : List Atom) (scope : List String) :
    Completed.AtomRel context noHost lookup live scope (Spec.Eval.Entry.Value.ofAtom query)
      Atom.undefinedType completedFrame [(Spec.Eval.Entry.Value.ofAtom lateError,completedFrame)] := by
  have active : ∀ result ∈ [(Spec.Eval.Entry.Value.ofAtom lateError,completedFrame)], result.1.status = .active := by
    intro result present
    obtain rfl := List.mem_singleton.mp present
    simp [Spec.Eval.Entry.Value.ofAtom,lateError,Spec.Eval.Entry.Value.status]
  rw [←unmarked_publication
    (completedFrame.read .unmarked (Spec.Eval.Entry.Value.ofAtom query)).erase _ active]
  apply Completed.AtomRel.tuple (readiness := .active) (operator := .symbol "Box")
    (arguments := [Spec.Eval.Entry.Value.ofAtom mixed,Spec.Eval.Entry.Value.ofAtom later])
    (rows := [(Spec.Eval.Entry.Value.ofAtom lateError,completedFrame)])
    (raw := [(Spec.Eval.Entry.Value.ofAtom lateError,completedFrame)])
  · simp only [completedFrame,Completed.Frame.read_empty,Spec.Eval.Entry.Value.ofAtom,
      Spec.Eval.Entry.Value.erase_ofAtom,Spec.Eval.Entry.Value.erase,Spec.Eval.Entry.Value.status,
      Completed.Policy.unmarked,query,List.map_cons,List.map_nil]
    apply Spec.Eval.Entry.Rel.expression
    · simp [IsEmptyOrErrorRel,IsErrorRel,Atom.empty]
    · decide
    · exact Or.inl rfl
  · simp [completedFrame,Spec.Eval.Entry.Value.ofAtom,query]
  · simpa only [Spec.Eval.Entry.Value.erase,symbol_lookup,Multiset.coe_singleton] using
      (FirstSuccessSourceReplies.source_types context (.symbol "Box")).occurrences
  · apply Completed.TupleRel.cons (head := .symbol "Box")
      (second := Spec.Eval.Entry.Value.ofAtom mixed) (remaining := [Spec.Eval.Entry.Value.ofAtom later])
      (heads := [(.symbol "Box",completedFrame)])
      (completed_symbol lookup queries _ scope "Box" (by decide))
    have laterPart := Completed.TupleRel.singleton (later_completed lookup queries
      (.symbol "Good" :: .symbol "Box" :: Atom.undefinedType :: live) scope)
    have laterOne : Completed.TupleRel context noHost lookup
        (.symbol "Good" :: .symbol "Box" :: Atom.undefinedType :: live) scope
        [Spec.Eval.Entry.Value.ofAtom later] completedFrame
        [(Spec.Eval.Entry.Value.ofAtom lateError,completedFrame)] := by
      simpa [Completed.tupleSingleton,isEmptyOrError,isErrorAtom,lateError,
        Spec.Eval.Entry.Value.erase_ofAtom] using laterPart
    have mixedTail : Completed.TupleBranchesRel context noHost lookup
        (.symbol "Box" :: Atom.undefinedType :: live) scope [Spec.Eval.Entry.Value.ofAtom later]
        [(.symbol "Good",completedFrame)] [(Spec.Eval.Entry.Value.ofAtom lateError,completedFrame)] := by
      have continued := Completed.TupleBranchesRel.continuing
        (space := context) (dispatch := noHost) (lookup := lookup)
        (live := .symbol "Box" :: Atom.undefinedType :: live) (scope := scope)
        (tail := [Spec.Eval.Entry.Value.ofAtom later])
        (head := ((.symbol "Good" : Spec.Eval.Entry.Value),completedFrame)) (heads := [])
        (children := [(Spec.Eval.Entry.Value.ofAtom lateError,completedFrame)]) (rest := [])
        (by simp [IsEmptyOrErrorRel,IsErrorRel,Atom.empty,Spec.Eval.Entry.Value.erase])
        (by simpa only [Spec.Eval.Entry.Value.erase] using laterOne)
        (Completed.TupleBranchesRel.nil)
      simpa [Completed.tuplePrepend,isEmptyOrError,isErrorAtom,lateError,
        Spec.Eval.Entry.Value.erase_ofAtom] using continued
    have mixedPart : Completed.AtomRel context noHost lookup
        (.expression [(Spec.Eval.Entry.Value.ofAtom later).erase] ::
          .symbol "Box" :: Atom.undefinedType :: live) scope
        (Spec.Eval.Entry.Value.ofAtom mixed) Atom.undefinedType completedFrame
        [(.symbol "Good",completedFrame)] := by
      simpa only [mixed,Spec.Eval.Entry.Value.ofAtom,List.map_cons,List.map_nil] using
        mixed_completed lookup queries _ scope
    have argsPart := Completed.TupleRel.cons mixedPart mixedTail
    have continued := Completed.TupleBranchesRel.continuing
      (space := context) (dispatch := noHost) (lookup := lookup)
      (live := Atom.undefinedType :: live) (scope := scope)
      (tail := [Spec.Eval.Entry.Value.ofAtom mixed,Spec.Eval.Entry.Value.ofAtom later])
      (head := ((.symbol "Box" : Spec.Eval.Entry.Value),completedFrame)) (heads := [])
      (children := [(Spec.Eval.Entry.Value.ofAtom lateError,completedFrame)]) (rest := [])
      (by simp [IsEmptyOrErrorRel,IsErrorRel,Atom.empty,Spec.Eval.Entry.Value.erase])
      (by simpa only [Spec.Eval.Entry.Value.erase] using argsPart)
      (Completed.TupleBranchesRel.nil)
    simpa [Completed.tuplePrepend,isEmptyOrError,isErrorAtom,lateError,
      Spec.Eval.Entry.Value.erase_ofAtom] using continued
  · simpa using Completed.CallsRel.cons (Completed.CallRel.error (by
      simpa only [Spec.Eval.Entry.Value.erase_ofAtom] using (show IsErrorRel lateError from ⟨_,rfl⟩))) (.nil)
  · simp only [List.map_cons,List.map_nil,Completed.readResult,
      completedFrame,Completed.Frame.read_empty]
    apply Mettapedia.Machines.OrderedProtocol.Completion.SuccessPriorityRel.allErrors
    intro result member
    simp only [List.mem_singleton] at member
    subst result
    simp [Spec.Eval.Entry.Value.erase_ofAtom,lateError,isErrorAtom]

/-- The independent contextual source completion supplies a small-step
machine run and preserves the actual scoped worker's atom observation on
the permanent nested-priority discriminator. -/
theorem completed_scoped_source_matches_run :
    ∃ results, Completed.AtomRel context noHost Completed.scopedLookup [] []
        (Spec.Eval.Entry.Value.ofAtom query) Atom.undefinedType completedFrame results ∧
      RecursiveMachine.Contextual.Steps noHost Completed.scopedLookup .unmarked
        (RecursiveMachine.Contextual.load context query Atom.undefinedType)
        ⟨context,.returning [],[],results⟩ ∧
      results.map (fun result => result.1.erase) =
        ((FirstSuccessRecursiveExecution.Checked.machine HE.GroundedDispatch.none scopedTypes).run 200 initial).1.map Prod.fst ∧
      earlyError ∉ results.map (fun result => result.1.erase) := by
  refine ⟨[(Spec.Eval.Entry.Value.ofAtom lateError,completedFrame)],
    parent_completed _ scoped_symbol_queries [] [],?_,?_,?_⟩
  · exact (RecursiveExecution.Contextual.task_source_iff_finished context _ _).mp
      (parent_completed _ scoped_symbol_queries [] [])
  · rw [checked_scoped_late_only]
    simp only [List.map_cons,List.map_nil,Spec.Eval.Entry.Value.erase_ofAtom]
  · simp [Spec.Eval.Entry.Value.erase_ofAtom,earlyError,lateError]

theorem completed_raw_source :
    Completed.AtomRel context noHost Completed.rawLookup [] []
      (Spec.Eval.Entry.Value.ofAtom query) Atom.undefinedType completedFrame
      [(Spec.Eval.Entry.Value.ofAtom lateError,completedFrame)] :=
  parent_completed _ raw_symbol_queries [] []

/-- One reentry choice separates both the completed source phases and their
actual contextual machine runs. Equations and recursive rules are shared. -/
theorem held_call_profile_separation :
    let heldCall : Spec.Eval.Entry.Value := .expression .held [.symbol "mixed"]
    let reusePolicy : Completed.Policy := { Completed.Policy.unmarked with reentry := .reuse }
    Completed.AtomRel context noHost Completed.rawLookup [] [] heldCall Atom.undefinedType completedFrame
      [(heldCall,completedFrame)] (policy := reusePolicy) ∧
    Completed.AtomRel context noHost Completed.rawLookup [] [] heldCall Atom.undefinedType completedFrame
      [(.symbol "Good",completedFrame)] ∧
    RecursiveMachine.Contextual.Steps noHost Completed.rawLookup reusePolicy
      (RecursiveTasks.Contextual.Configuration.initial context
        (.atom [] [] heldCall Atom.undefinedType completedFrame))
      ⟨context,.returning [],[],[(heldCall,completedFrame)]⟩ ∧
    RecursiveMachine.Contextual.Steps noHost Completed.rawLookup .unmarked
      (RecursiveTasks.Contextual.Configuration.initial context
        (.atom [] [] heldCall Atom.undefinedType completedFrame))
      ⟨context,.returning [],[],[(.symbol "Good",completedFrame)]⟩ ∧
    heldCall.erase ≠ (.symbol "Good" : Atom) := by
  dsimp only
  have reused : Completed.AtomRel context noHost Completed.rawLookup [] []
      (.expression .held [.symbol "mixed"]) Atom.undefinedType completedFrame
      [(.expression .held [.symbol "mixed"],completedFrame)]
      (policy := { Completed.Policy.unmarked with reentry := .reuse }) := by
    have read : completedFrame.read { Completed.Policy.unmarked with reentry := .reuse }
        (.expression .held [.symbol "mixed"]) = .expression .held [.symbol "mixed"] := by
      simp [completedFrame]
    have completed := Completed.AtomRel.reuse_expression
      (space := context) (dispatch := noHost) (lookup := Completed.rawLookup)
      (live := []) (scope := []) (value := .expression .held [.symbol "mixed"])
      (expected := Atom.undefinedType) (frame := completedFrame)
      (policy := { Completed.Policy.unmarked with reentry := .reuse })
      (children := [.symbol "mixed"]) read rfl
    simpa only [read] using completed
  have interpreted := mixed_completed _ raw_symbol_queries [] [] .held
  refine ⟨reused,interpreted,?_,?_,?_⟩
  · exact (RecursiveExecution.Contextual.task_source_iff_finished context _ _).mp reused
  · exact (RecursiveExecution.Contextual.task_source_iff_finished context _ _).mp interpreted
  · simp [Spec.Eval.Entry.Value.erase]

end Mettapedia.Languages.MeTTa.HE.FirstSuccessSourceExecution.NestedPriorityControls
