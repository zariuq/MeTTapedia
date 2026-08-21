import Mettapedia.Languages.MeTTa.Prime.NativeGradualQuotation
import Mettapedia.Languages.MeTTa.PeTTa.TypecheckV3Core

/-!
# Program-level gradual elaboration for MeTTa Native

Expression quotation and native elaboration are deliberately partial.  This
module lifts them to complete authored programs without turning partial typing
into a program gate.  Every source command is retained.  Each embedded pattern
is independently prepared in one of three modes:

* `raw`: preserve the ordinary MeTTa path without asking for evidence;
* `eager`: keep exact typing evidence on success and fall back to raw on a
  structured, source-located rejection;
* `checked`: suspend the source-indexed obligation under a complete cache key.

Ordinary execution erases all three modes to the exact parsed program.  Thus a
native island may earn an accelerator, but failure to elaborate one island
cannot reject its declaration or unrelated declarations.
-/

namespace Mettapedia.Languages.MeTTa.Prime.NativeProgramElaboration

open Mettapedia.OSLF.MeTTaIL.MeTTaSyntaxQuotation
open Mettapedia.Languages.MeTTa.Prime.GradualExecutionPlan
open Mettapedia.Languages.MeTTa.Prime.NativeGradualQuotation
open Mettapedia.Languages.MeTTa.Prime.NativeTypedQuotation
open Mettapedia.Languages.MeTTa.PeTTa.TypecheckV3Core
open scoped Mettapedia.OSLF.MeTTaIL.MeTTaSyntaxQuotation

abbrev SourceCommand := ProgramCommand RuntimePattern
abbrev SourceProgram := Program RuntimePattern

/-! ## Declaration-order stance -/

/-- Nominal declarations are admitted in source order by the same selector as
PeTTa typecheck-v3.  This is intentionally distinct from `equationBag`. -/
def nominalAdmission (declarations : List (Nat × ProviderDecl))
    (name : Nat) : Option ProviderDecl :=
  firstProviderDecl declarations name

/-- The first declaration for a nominal name is authoritative. -/
@[simp] theorem nominalAdmission_head (name : Nat)
    (declaration : ProviderDecl)
    (rest : List (Nat × ProviderDecl)) :
    nominalAdmission ((name, declaration) :: rest) name = some declaration :=
  firstProviderDecl_head name declaration rest

/-- Negative control: a later incompatible declaration cannot replace the
first admitted meaning. -/
theorem nominalAdmission_later_conflict_is_ignored :
    nominalAdmission
        [(8, .alias (.prim .num)), (8, .newtype (.prim .str))] 8 =
      some (.alias (.prim .num)) := by
  rfl

/-! ## Preparation policy and exact locations -/

inductive PreparationMode where
  | raw
  | eager
  | checked
deriving Repr, DecidableEq

/-- A policy can select preparation per declaration and per embedded-pattern
coordinate.  Revision, dialect, and authority are retained in every suspended
key rather than supplied later by the runner. -/
structure PreparationPolicy where
  choose : Nat → Nat → RuntimePattern → PreparationMode
  /-- The native candidate is produced out-of-band.  The default keeps direct
  native quotations unchanged; curriculum policies can instead compile an
  ordinary source shape without modifying the authored program. -/
  encode : Nat → Nat → RuntimePattern → RuntimePattern :=
    fun _ _ source => source
  revision : Nat
  dialect : String
  authority : String

structure SourceLocation where
  declaration : Nat
  line : Nat
  child : Nat
deriving Repr, DecidableEq

structure LocatedFailure where
  location : SourceLocation
  failure : Failure
deriving Repr, DecidableEq

/-! ## Planned patterns -/

/-- A program island retains its ordinary source independently of an optional
native compilation artifact.  The typed branch carries intrinsic evidence
about `evidence.source`, which may be an out-of-band encoding of `source`.
The checked branch similarly keys the encoded candidate while raw execution
continues to erase to `source`. -/
inductive IslandPlan where
  | raw (source : RuntimePattern)
  | typed (source : RuntimePattern) (evidence : TypingEvidence)
  | checked (source : RuntimePattern) (typingKey : TypingKey)

namespace IslandPlan

def erase : IslandPlan → RuntimePattern
  | .raw source | .typed source _ | .checked source _ => source

def kind : IslandPlan → PreparationMode
  | .raw _ => .raw
  | .typed _ _ => .eager
  | .checked _ _ => .checked

def nativeCandidate : IslandPlan → RuntimePattern
  | .raw source => source
  | .typed _ evidence => evidence.source
  | .checked _ typingKey => typingKey.occurrence.2

/-- A plan classified as eager contains an actual proof-producing native
elaboration result for its compiled candidate. -/
theorem eager_has_intrinsic_typing (plan : IslandPlan)
    (eager : plan.kind = .eager) :
    ∃ result, elaborate plan.nativeCandidate = .ok result := by
  cases plan with
  | raw source => cases eager
  | typed source evidence => exact ⟨evidence.result, evidence.elaborated⟩
  | checked source typingKey => cases eager

end IslandPlan

/-- One planned source occurrence.  The optional failure is retained only when
eager elaboration was requested and refused; the plan itself is then raw. -/
structure PlannedPattern where
  location : SourceLocation
  source : RuntimePattern
  plan : IslandPlan
  failure? : Option LocatedFailure

namespace PlannedPattern

def kind (planned : PlannedPattern) : PreparationMode :=
  planned.plan.kind

/-- Ordinary execution sees exactly the authored source pattern. -/
def erase (planned : PlannedPattern) : RuntimePattern :=
  planned.plan.erase

end PlannedPattern

/-- Prepare one pattern.  Eager rejection is explicitly fail-open: it returns
a raw plan and a retained structured diagnostic. -/
def preparePattern (policy : PreparationPolicy) (location : SourceLocation)
    (source : RuntimePattern) : PlannedPattern :=
  let candidate := policy.encode location.declaration location.child source
  match policy.choose location.declaration location.child source with
  | .raw =>
      ⟨location, source, .raw source, none⟩
  | .checked =>
      let typingKey := key (Nat.pair location.declaration location.child)
        policy.revision policy.dialect policy.authority candidate
      ⟨location, source, .checked source typingKey, none⟩
  | .eager =>
      match equation : elaborate candidate with
      | .ok result =>
          let evidence : TypingEvidence := ⟨candidate, result, equation⟩
          ⟨location, source, .typed source evidence, none⟩
      | .error failure =>
          ⟨location, source, .raw source,
            some ⟨location, failure⟩⟩

@[simp] theorem preparePattern_erases (policy : PreparationPolicy)
    (location : SourceLocation) (source : RuntimePattern) :
    (preparePattern policy location source).erase = source := by
  simp only [preparePattern, PlannedPattern.erase]
  split
  · rfl
  · rfl
  · split <;> rfl

/-! ## Command and program planning -/

abbrev PlannedCommand := ProgramCommand PlannedPattern
abbrev PlannedRows := List (Nat × PlannedCommand)

def prepareCommand (policy : PreparationPolicy) (declaration line : Nat)
    (command : SourceCommand) : PlannedCommand :=
  command.mapIdx fun child source =>
    preparePattern policy ⟨declaration, line, child⟩ source

def eraseCommand (command : PlannedCommand) : SourceCommand :=
  command.map PlannedPattern.erase

theorem erase_prepareCommand (policy : PreparationPolicy)
    (declaration line : Nat) (command : SourceCommand) :
    eraseCommand (prepareCommand policy declaration line command) = command := by
  unfold eraseCommand prepareCommand
  exact ProgramCommand.map_mapIdx_of_leftInverse _ _
    (fun child source => preparePattern_erases policy
      ⟨declaration, line, child⟩ source) command

def prepareRowsFrom (policy : PreparationPolicy) :
    Nat → SourceProgram → PlannedRows
  | _, [] => []
  | declaration, row :: rows =>
      (row.1, prepareCommand policy declaration row.1 row.2) ::
        prepareRowsFrom policy (declaration + 1) rows

def prepareRows (policy : PreparationPolicy) (source : SourceProgram) :
    PlannedRows :=
  prepareRowsFrom policy 0 source

def eraseRows (rows : PlannedRows) : SourceProgram :=
  rows.map fun row => (row.1, eraseCommand row.2)

theorem erase_prepareRowsFrom (policy : PreparationPolicy)
    (declaration : Nat) (source : SourceProgram) :
    eraseRows (prepareRowsFrom policy declaration source) = source := by
  induction source generalizing declaration with
  | nil => rfl
  | cons row rows inductionHypothesis =>
      rcases row with ⟨line, command⟩
      simp only [prepareRowsFrom, eraseRows, List.map_cons]
      rw [erase_prepareCommand]
      exact congrArg (List.cons (line, command))
        (inductionHypothesis (declaration + 1))

theorem erase_prepareRows (policy : PreparationPolicy)
    (source : SourceProgram) :
    eraseRows (prepareRows policy source) = source := by
  exact erase_prepareRowsFrom policy 0 source

/-- The proof-carrying program package.  `erases` prevents a planner from
dropping, reordering, or rewriting an authored declaration while assigning
optional evidence. -/
structure ProgramPlan where
  source : SourceProgram
  planned : PlannedRows
  erases : eraseRows planned = source

def prepareProgram (policy : PreparationPolicy)
    (source : SourceProgram) : ProgramPlan :=
  ⟨source, prepareRows policy source, erase_prepareRows policy source⟩

/-! ## Diagnostics -/

def commandFailures : ProgramCommand PlannedPattern → List LocatedFailure
  | .empty => []
  | .eval term | .fact term => term.failure?.toList
  | .defineEq left right | .defineType left right |
      .import left right | .addAtom left right | .removeAtom left right =>
      left.failure?.toList ++ right.failure?.toList
  | .defineRule left right premises =>
      left.failure?.toList ++ right.failure?.toList ++
        premises.flatMap fun premise => premise.failure?.toList
  | .relationFact _ arguments | .builtinFact _ arguments |
      .directive _ arguments =>
      arguments.flatMap fun argument => argument.failure?.toList
  | .setFuel _ | .newSpace _ => []

def ProgramPlan.failures (program : ProgramPlan) : List LocatedFailure :=
  program.planned.flatMap fun row => commandFailures row.2

/-! ## Policy constructors and laws -/

def rawPolicy : PreparationPolicy where
  choose := fun _ _ _ => .raw
  revision := 0
  dialect := "raw"
  authority := "none"

def checkedPolicy (revision : Nat) (dialect authority : String) :
    PreparationPolicy where
  choose := fun _ _ _ => .checked
  revision := revision
  dialect := dialect
  authority := authority

def eagerPolicy (revision : Nat) (dialect authority : String) :
    PreparationPolicy where
  choose := fun _ _ _ => .eager
  revision := revision
  dialect := dialect
  authority := authority

theorem rawPolicy_has_no_failures (source : SourceProgram) :
    (prepareProgram rawPolicy source).failures = [] := by
  suffices rowsHaveNoFailures : ∀ declaration,
      (prepareRowsFrom rawPolicy declaration source).flatMap
          (fun row => commandFailures row.2) = [] by
    exact rowsHaveNoFailures 0
  intro declaration
  induction source generalizing declaration with
  | nil => rfl
  | cons row rows inductionHypothesis =>
      rcases row with ⟨line, command⟩
      have patternHasNoFailure : ∀ child term,
          (preparePattern rawPolicy ⟨declaration, line, child⟩ term).failure? =
            none := by
        intro child term
        rfl
      have listHasNoFailures : ∀ start terms,
          (ProgramCommand.mapIdxFrom start
              (fun child term =>
                preparePattern rawPolicy ⟨declaration, line, child⟩ term)
              terms).flatMap (fun term => term.failure?.toList) = [] := by
        intro start terms
        induction terms generalizing start with
        | nil => rfl
        | cons term terms listInduction =>
            simp [ProgramCommand.mapIdxFrom, patternHasNoFailure,
              listInduction]
      have commandHasNoFailures :
          commandFailures
              (prepareCommand rawPolicy declaration line command) = [] := by
        cases command <;>
          simp [commandFailures, prepareCommand, ProgramCommand.mapIdx,
            patternHasNoFailure, listHasNoFailures]
      simp [prepareRowsFrom, commandHasNoFailures, inductionHypothesis]

/-! ## Positive and negative controls -/

def mixedSource : SourceProgram :=
  metta_program% petta
    "(native:u0)
     (native:app (native:pattern request) (native:pattern datum))
     (ordinary datum)"

def mixedEager : ProgramPlan :=
  prepareProgram (eagerPolicy 7 "petta" "prime-native-v1") mixedSource

/-- The complete three-declaration source survives eager preparation exactly,
including the rejected native application and the ordinary equation. -/
theorem mixedEager_erases : eraseRows mixedEager.planned = mixedSource :=
  mixedEager.erases

/-- The invalid native application and the ordinary expression produce two
located diagnostics, while the complete surrounding program remains
executable through raw erasure. -/
theorem mixedEager_failure_count : mixedEager.failures.length = 2 := by
  decide

def mixedChecked : ProgramPlan :=
  prepareProgram (checkedPolicy 7 "petta" "prime-native-v1") mixedSource

/-- Suspending all checks produces no eager diagnostics and retains the same
source program. -/
theorem mixedChecked_has_no_failures : mixedChecked.failures = [] := by
  decide

theorem mixedChecked_erases : eraseRows mixedChecked.planned = mixedSource :=
  mixedChecked.erases

#print axioms erase_prepareRows
#print axioms mixedEager_erases
#print axioms mixedEager_failure_count
#print axioms mixedChecked_has_no_failures

end Mettapedia.Languages.MeTTa.Prime.NativeProgramElaboration
