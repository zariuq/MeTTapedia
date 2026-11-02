import Batteries.Data.List.Lemmas
import Mettapedia.Languages.MeTTa.PeTTa.BridgeKit
import Mettapedia.Languages.MeTTa.PeTTa.BridgeTransport
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.GeneralPremiseMachineExecution.Core

/-!
# The complete machine's MeTTa sources

The scheduled descent and complete-machine artifacts are quoted and pinned.
Their operations use the single checked interpreted runtime. Scoped, typed,
descent and complete views retain that program; proof transport of lower
operations uses their explicit closed fragments.
-/

set_option autoImplicit false
set_option Elab.async false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution

open SpaceSemantics (Program)
open Eval (codeWithin)
open scoped ProgramQuotation

def descentSource : ProgramQuotation.QuotedProgram :=
  petta_source_file%
    "../../../../../../../../../metta/gslt/lib/gslt_descent_execution.metta"
    sha256 "ac6898f665cc26f9e7cc3190f110adb1e1cbf773a0fe114bb78501d62a502bf9"

def completeSource : ProgramQuotation.QuotedProgram :=
  petta_source_file%
    "../../../../../../../../../metta/gslt/lib/gslt_complete.metta"
    sha256 "86918154a2bd3259288bbe0e7bfc8c1881ec6ccaa0359904c045b87d5ea394a9"

/-- The common runtime is selected from the checked shared source. The view
names keep the machine operations on that same runtime. -/
def scopedLibrary : BridgeKit.Library := RetainedMatchingWire.interpretedLibrary

def typedLibrary : BridgeKit.Library := RetainedMatchingWire.interpretedLibrary

def descentLibrary : BridgeKit.Library := RetainedMatchingWire.interpretedLibrary

def completeLibrary : BridgeKit.Library := RetainedMatchingWire.interpretedLibrary

abbrev runtime : Program := RuleExecutionProgram.interpretedPremiseProgram

theorem scoped_checked : scopedLibrary.check = true := RetainedMatchingWire.interpreted_checked

theorem typed_checked : typedLibrary.check = true := RetainedMatchingWire.interpreted_checked

theorem descent_checked : descentLibrary.check = true := RetainedMatchingWire.interpreted_checked

theorem complete_checked : completeLibrary.check = true := RetainedMatchingWire.interpreted_checked

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution

section

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution.PhysicalSourceAgreement

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open SpaceSemantics (Program Equation)
open Eval

private def matching (head : String) : Bool := head.startsWith "gslt:premise:matching-"

private def supportEquations : List Equation :=
  RuleExecutionProgram.interpretedPremiseSupportSources.flatMap (fun source => source.program.equations)

private def supportDeclarations : List Atom :=
  RuleExecutionProgram.interpretedPremiseSupportSources.flatMap (fun source => source.program.declarations)

private theorem support_equations_fresh :
    supportEquations.all (fun row => !matching row.head) = true := by decide +kernel

private theorem support_declarations_fresh :
    supportDeclarations.all (fun row => !retainedCallDeclaration matching row) = true := by decide +kernel

private theorem filtered_constant {α : Type} (rows : List α) (first second : α → Bool)
    (value : Bool) (same : ∀ row, second row = true → first row = value) :
    (rows.filter first).filter second = if value then rows.filter second else [] := by
  induction rows with
  | nil => cases value <;> rfl
  | cons row rows ih =>
      cases selected : second row with
      | false =>
          cases kept : first row <;> simp [selected, kept, ih]
      | true =>
          have kept := same row selected
          cases value <;> simp [selected, kept, ih]

private theorem declaration_constant (owns : String → Bool) (head : String) (declaration : Atom)
    (selected : retainedCallDeclaration (fun name => name == head) declaration = true) :
    retainedCallDeclaration owns declaration = owns head := by
  unfold retainedCallDeclaration at selected ⊢
  split at selected
  · rename_i name _
    have same : name = head := by simpa using selected
    simp_all
  · simp_all

theorem fold_equations (sources : List ProgramQuotation.QuotedProgram) (base : Program) :
    (sources.foldl (fun loaded source => loaded.append source.program) base).equations =
      base.equations ++ sources.flatMap (fun source => source.program.equations) := by
  induction sources generalizing base with
  | nil => simp
  | cons source sources ih =>
      simpa only [List.foldl_cons, Program.append, List.flatMap_cons, List.append_assoc] using
        ih (base.append source.program)

theorem fold_declarations (sources : List ProgramQuotation.QuotedProgram) (base : Program) :
    (sources.foldl (fun loaded source => loaded.append source.program) base).declarations =
      base.declarations ++ sources.flatMap (fun source => source.program.declarations) := by
  induction sources generalizing base with
  | nil => simp
  | cons source sources ih =>
      simpa only [List.foldl_cons, Program.append, List.flatMap_cons, List.append_assoc] using
        ih (base.append source.program)

private theorem support_equations_absent (head : String) (owned : matching head = true) :
    supportEquations.filter (fun row => row.head == head) = [] := by
  apply List.filter_eq_nil_iff.mpr
  intro row member selected
  have same : row.head = head := by simpa using selected
  have fresh := List.all_eq_true.mp support_equations_fresh row member
  simp [same, owned] at fresh

private theorem support_declarations_absent (head : String) (owned : matching head = true) :
    supportDeclarations.filter (retainedCallDeclaration (fun name => name == head)) = [] := by
  apply List.filter_eq_nil_iff.mpr
  intro row member selected
  have same := declaration_constant matching head row selected
  have fresh := List.all_eq_true.mp support_declarations_fresh row member
  simp [same, owned] at fresh

private theorem append_equations (first second : Program) :
    (first.append second).equations = first.equations ++ second.equations := rfl

private theorem append_declarations (first second : Program) :
    (first.append second).declarations = first.declarations ++ second.declarations := rfl

theorem named_equations (head : String) :
    (RuleExecutionProgram.interpretedPremiseSupportSources.foldl
      (fun loaded source => loaded.append source.program) RuleExecutionProgram.scopedProgram).equations.filter
        (fun row => row.head == head) =
      RuleExecutionProgram.interpretedPremiseProgram.equations.filter (fun row => row.head == head) := by
  have yes := filtered_constant RuleExecutionProgram.scopedProgram.equations
    (fun row => matching row.head) (fun row => row.head == head) (matching head)
    (fun row selected => by
      have same : row.head = head := by simpa using selected
      exact congrArg matching same)
  have no := filtered_constant RuleExecutionProgram.scopedProgram.equations
    (fun row => !matching row.head) (fun row => row.head == head) (!matching head)
    (fun row selected => by
      have same : row.head = head := by simpa using selected
      exact congrArg (fun name => !matching name) same)
  simp only [RuleExecutionProgram.interpretedPremiseProgram, append_equations, fold_equations,
    RuleExecutionProgram.callFragmentWhere, List.filter_append]
  change _ ++ supportEquations.filter _ = (_ ++ supportEquations.filter _) ++ _
  rw [show (fun row : Equation => row.head.startsWith "gslt:premise:matching-") =
      (fun row => matching row.head) from rfl]
  rw [show (fun row : Equation => !row.head.startsWith "gslt:premise:matching-") =
      (fun row => !matching row.head) from rfl]
  rw [yes, no]
  cases owned : matching head with
  | false => simp
  | true => simp [support_equations_absent head owned]

theorem named_declarations (head : String) :
    (RuleExecutionProgram.interpretedPremiseSupportSources.foldl
      (fun loaded source => loaded.append source.program) RuleExecutionProgram.scopedProgram).declarations.filter
        (retainedCallDeclaration (fun name => name == head)) =
      RuleExecutionProgram.interpretedPremiseProgram.declarations.filter
        (retainedCallDeclaration (fun name => name == head)) := by
  have yes := filtered_constant RuleExecutionProgram.scopedProgram.declarations
    (retainedCallDeclaration matching) (retainedCallDeclaration (fun name => name == head)) (matching head)
    (fun row selected => declaration_constant matching head row selected)
  have no := filtered_constant RuleExecutionProgram.scopedProgram.declarations
    (retainedCallDeclaration (fun name => !matching name)) (retainedCallDeclaration (fun name => name == head))
    (!matching head) (fun row selected => declaration_constant (fun name => !matching name) head row selected)
  simp only [RuleExecutionProgram.interpretedPremiseProgram, append_declarations, fold_declarations,
    RuleExecutionProgram.callFragmentWhere, List.filter_append]
  change _ ++ supportDeclarations.filter _ = (_ ++ supportDeclarations.filter _) ++ _
  rw [show (fun name => name.startsWith "gslt:premise:matching-") = matching from rfl]
  rw [show (fun name => !name.startsWith "gslt:premise:matching-") = (fun name => !matching name) from rfl]
  rw [yes, no]
  cases owned : matching head with
  | false => simp
  | true => simp [support_declarations_absent head owned]

theorem physical_interpreted_agreement :
    ProgramAgreementOn (fun _ => true)
      (RuleExecutionProgram.interpretedPremiseSupportSources.foldl
        (fun loaded source => loaded.append source.program) RuleExecutionProgram.scopedProgram)
      RuleExecutionProgram.interpretedPremiseProgram := by
  have named (head : String) : ProgramAgreementOn (fun name => name == head)
      (RuleExecutionProgram.interpretedPremiseSupportSources.foldl
        (fun loaded source => loaded.append source.program) RuleExecutionProgram.scopedProgram)
      RuleExecutionProgram.interpretedPremiseProgram :=
    programAgreementOn_of_retained_rows _ _ _ (named_equations head) (named_declarations head)
  exact ⟨fun head _ => (named head).dispatch head (by simp),
    fun head index _ => (named head).demand head index (by simp),
    fun head values _ => (named head).bodies head values (by simp)⟩

#print axioms named_equations
#print axioms named_declarations
#print axioms physical_interpreted_agreement

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution.PhysicalSourceAgreement

end


section CompleteProofView

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open SpaceSemantics (Program Equation)
open Eval BridgeKit

mutual
  def sourceLiteralHeads : Atom → List String
    | .expression items =>
        match items with
        | .symbol head :: _ => head :: sourceLiteralListHeads items
        | _ => sourceLiteralListHeads items
    | _ => []

  def sourceLiteralListHeads : List Atom → List String
    | [] => []
    | first :: rest => sourceLiteralHeads first ++ sourceLiteralListHeads rest
end

private def completeProofSource : Program :=
  (RuleExecutionProgram.interpretedPremiseSupportSources[2]'(by decide +kernel)).program

private def completeMetadataDescentSource : Program :=
  (RuleExecutionProgram.interpretedPremiseSupportSources[1]'(by decide +kernel)).program

/-- Direct outward calls, derived from the actual complete artifact's body syntax. -/
private def completeObservedInheritedHeads : List String :=
  ((completeProofSource.equations.flatMap (fun row => sourceLiteralHeads row.body)).filter
    (fun head => head.startsWith "gslt:" && !(completeProofSource.equations.map (·.head)).contains head)).eraseDups

/-- The source-derived direct outward calls, materialized once for bounded metadata checks. -/
def completeProofInheritedHeads : List String := [
    "gslt:descent:start",
    "gslt:automata:member",
    "gslt:descent:payloads",
    "gslt:automata:append",
    "gslt:descent:cut",
    "gslt:descent:tick",
    "gslt:sites:jobs",
    "gslt:rule:job-finish-root",
    "gslt:automata:length",
    "gslt:rule:scope-matcher-complete",
    "gslt:rule:scope-matcher-tick",
    "gslt:rule:scope-matcher-start",
    "gslt:premise:check-assignment",
    "gslt:premise:open-well-sorted",
    "gslt:sites:generate",
    "gslt:rule:scope-reduct",
    "gslt:rule:site-replacement-represented",
    "gslt:rule:scope-fill",
    "gslt:rule:scope-instantiate-at"
  ]

theorem completeProofInheritedHeads_derived :
    completeObservedInheritedHeads = completeProofInheritedHeads := by decide +kernel

theorem completeSource_equation_count : completeSource.program.equations.length = 85 := by decide +kernel

theorem completeProofInheritedHeads_count : completeObservedInheritedHeads.length = 19 := by
  rw [completeProofInheritedHeads_derived]
  decide +kernel

private def completeMetadataTypedSource : Program :=
  (RuleExecutionProgram.interpretedPremiseSupportSources[0]'(by decide +kernel)).program

private def completeScopedMetadataEquations : List Equation := [
    RuleExecutionProgram.scopedProgram.equations[0]'(by decide +kernel),
    RuleExecutionProgram.scopedProgram.equations[1]'(by decide +kernel),
    RuleExecutionProgram.scopedProgram.equations[2]'(by decide +kernel),
    RuleExecutionProgram.scopedProgram.equations[118]'(by decide +kernel),
    RuleExecutionProgram.scopedProgram.equations[146]'(by decide +kernel),
    RuleExecutionProgram.scopedProgram.equations[148]'(by decide +kernel),
    RuleExecutionProgram.scopedProgram.equations[173]'(by decide +kernel),
    RuleExecutionProgram.scopedProgram.equations[174]'(by decide +kernel),
    RuleExecutionProgram.scopedProgram.equations[179]'(by decide +kernel),
    RuleExecutionProgram.scopedProgram.equations[196]'(by decide +kernel),
    RuleExecutionProgram.scopedProgram.equations[198]'(by decide +kernel),
    RuleExecutionProgram.scopedProgram.equations[218]'(by decide +kernel),
    RuleExecutionProgram.scopedProgram.equations[219]'(by decide +kernel)
  ]

private def completeTypedMetadataEquations : List Equation := [
    completeMetadataTypedSource.equations[7]'(by decide +kernel),
    completeMetadataTypedSource.equations[18]'(by decide +kernel)
  ]

private def completeDescentMetadataEquations : List Equation := [
    completeMetadataDescentSource.equations[9]'(by decide +kernel),
    completeMetadataDescentSource.equations[10]'(by decide +kernel),
    completeMetadataDescentSource.equations[12]'(by decide +kernel),
    completeMetadataDescentSource.equations[13]'(by decide +kernel)
  ]

private def completeScopedMetadataDeclarations : List Atom := [
    RuleExecutionProgram.scopedProgram.declarations[0]'(by decide +kernel),
    RuleExecutionProgram.scopedProgram.declarations[1]'(by decide +kernel),
    RuleExecutionProgram.scopedProgram.declarations[2]'(by decide +kernel),
    RuleExecutionProgram.scopedProgram.declarations[118]'(by decide +kernel),
    RuleExecutionProgram.scopedProgram.declarations[146]'(by decide +kernel),
    RuleExecutionProgram.scopedProgram.declarations[148]'(by decide +kernel),
    RuleExecutionProgram.scopedProgram.declarations[173]'(by decide +kernel),
    RuleExecutionProgram.scopedProgram.declarations[174]'(by decide +kernel),
    RuleExecutionProgram.scopedProgram.declarations[179]'(by decide +kernel),
    RuleExecutionProgram.scopedProgram.declarations[196]'(by decide +kernel),
    RuleExecutionProgram.scopedProgram.declarations[198]'(by decide +kernel),
    RuleExecutionProgram.scopedProgram.declarations[218]'(by decide +kernel),
    RuleExecutionProgram.scopedProgram.declarations[219]'(by decide +kernel)
  ]

private def completeTypedMetadataDeclarations : List Atom := [
    completeMetadataTypedSource.declarations[7]'(by decide +kernel),
    completeMetadataTypedSource.declarations[18]'(by decide +kernel)
  ]

private def completeDescentMetadataDeclarations : List Atom := [
    completeMetadataDescentSource.declarations[9]'(by decide +kernel),
    completeMetadataDescentSource.declarations[10]'(by decide +kernel),
    completeMetadataDescentSource.declarations[12]'(by decide +kernel),
    completeMetadataDescentSource.declarations[13]'(by decide +kernel)
  ]

/-- Actual source rows for the direct outward calls, in their original artifact order. -/
private def completeMetadataBase : Program where
  equations := completeScopedMetadataEquations ++ completeTypedMetadataEquations ++ completeDescentMetadataEquations
  declarations := completeScopedMetadataDeclarations ++ completeTypedMetadataDeclarations ++ completeDescentMetadataDeclarations
  layout := List.replicate 19 .equation ++ List.replicate 19 .declaration

/-- Body and ABI metadata for complete-family proofs. Operational conclusions still use runtime. -/
def completeProofLibrary : BridgeKit.Library :=
  ⟨completeMetadataBase, completeProofSource,
    ["gslt:deep:", "gslt:step:", "gslt:complete:", "gslt:equations:", "gslt:classes:"]⟩

/-- Metadata also agrees for literal data constructors and the direct outward operation heads. -/
def completeProofHeads (head : String) : Bool :=
  !head.startsWith "gslt:" || completeProofLibrary.owns head || completeProofInheritedHeads.contains head

theorem completeProof_owned_supported {head : String} (owned : completeProofLibrary.owns head = true) :
    completeProofHeads head = true := by simp [completeProofHeads, owned]

theorem completeProof_constructor_supported {head : String} (constructor : head.startsWith "gslt:" = false) :
    completeProofHeads head = true := by simp [completeProofHeads, constructor]

theorem completeProof_inherited_supported {head : String} (member : head ∈ completeProofInheritedHeads) :
    completeProofHeads head = true := by
  have contained := List.contains_iff_mem.mpr member
  simp only [completeProofHeads, contained, Bool.or_true]

theorem completeProof_inherited_rows :
    completeMetadataBase.equations.all (fun row => completeProofInheritedHeads.contains row.head) = true ∧
      completeProofInheritedHeads.all (fun head => completeMetadataBase.equations.any (fun row => row.head == head)) = true := by
  constructor <;> decide +kernel

theorem completeProof_inherited_declaration_heads :
    (completeMetadataBase.declarations.filterMap BridgeKit.arrowHead).all completeProofInheritedHeads.contains = true ∧
      completeProofInheritedHeads.all (completeMetadataBase.declarations.filterMap BridgeKit.arrowHead).contains = true := by
  constructor <;> decide +kernel

theorem completeProof_base_count : completeMetadataBase.equations.length = 19 := by decide +kernel

theorem completeProof_equation_count : completeProofLibrary.runtime.equations.length = 104 := by decide +kernel

theorem completeProof_source_supported :
    completeProofSource.equations.all (fun row => codeWithin completeProofHeads row.body) = true := by
  decide +kernel

theorem completeProof_checked : completeProofLibrary.check = true := by decide +kernel

private def completePhysicalProgram : Program :=
  RuleExecutionProgram.interpretedPremiseSupportSources.foldl
    (fun loaded source => loaded.append source.program) RuleExecutionProgram.scopedProgram

private def completeLateSources : List ProgramQuotation.QuotedProgram :=
  RuleExecutionProgram.interpretedPremiseSupportSources.drop 3

private theorem completeSupport_equations :
    (RuleExecutionProgram.interpretedPremiseSupportSources.flatMap (fun source => source.program.equations)) =
      completeMetadataTypedSource.equations ++ completeMetadataDescentSource.equations ++
        completeProofSource.equations ++ completeLateSources.flatMap (fun source => source.program.equations) := by
  have split : RuleExecutionProgram.interpretedPremiseSupportSources =
      RuleExecutionProgram.interpretedPremiseSupportSources[0]'(by decide +kernel) ::
      RuleExecutionProgram.interpretedPremiseSupportSources[1]'(by decide +kernel) ::
      RuleExecutionProgram.interpretedPremiseSupportSources[2]'(by decide +kernel) :: completeLateSources := rfl
  conv_lhs => rw [split, List.flatMap_cons, List.flatMap_cons, List.flatMap_cons]
  rfl

private theorem completeSupport_declarations :
    (RuleExecutionProgram.interpretedPremiseSupportSources.flatMap (fun source => source.program.declarations)) =
      completeMetadataTypedSource.declarations ++ completeMetadataDescentSource.declarations ++
        completeProofSource.declarations ++ completeLateSources.flatMap (fun source => source.program.declarations) := by
  have split : RuleExecutionProgram.interpretedPremiseSupportSources =
      RuleExecutionProgram.interpretedPremiseSupportSources[0]'(by decide +kernel) ::
      RuleExecutionProgram.interpretedPremiseSupportSources[1]'(by decide +kernel) ::
      RuleExecutionProgram.interpretedPremiseSupportSources[2]'(by decide +kernel) :: completeLateSources := rfl
  conv_lhs => rw [split, List.flatMap_cons, List.flatMap_cons, List.flatMap_cons]
  rfl

theorem source_filter_indices {α : Type} (rows : List α) (keep : α → Bool) :
    rows.filter keep = ((List.finRange rows.length).filter (fun index => keep (rows.get index))).map rows.get := by
  conv_lhs => rw [← List.map_get_finRange rows]
  rw [List.filter_map]
  rfl

private theorem completeScoped_equations_indices :
    (List.finRange RuleExecutionProgram.scopedProgram.equations.length).filter (fun index => (fun row => completeProofHeads row.head) (RuleExecutionProgram.scopedProgram.equations.get index)) =
      [⟨0, by decide +kernel⟩, ⟨1, by decide +kernel⟩, ⟨2, by decide +kernel⟩, ⟨118, by decide +kernel⟩, ⟨146, by decide +kernel⟩, ⟨148, by decide +kernel⟩, ⟨173, by decide +kernel⟩, ⟨174, by decide +kernel⟩, ⟨179, by decide +kernel⟩, ⟨196, by decide +kernel⟩, ⟨198, by decide +kernel⟩, ⟨218, by decide +kernel⟩, ⟨219, by decide +kernel⟩] := by decide +kernel

private theorem completeScoped_equations :
    RuleExecutionProgram.scopedProgram.equations.filter (fun row => completeProofHeads row.head) = completeScopedMetadataEquations := by
  rw [source_filter_indices, completeScoped_equations_indices]
  rfl

private theorem completeScoped_declarations_indices :
    (List.finRange RuleExecutionProgram.scopedProgram.declarations.length).filter (fun index => (retainedCallDeclaration completeProofHeads) (RuleExecutionProgram.scopedProgram.declarations.get index)) =
      [⟨0, by decide +kernel⟩, ⟨1, by decide +kernel⟩, ⟨2, by decide +kernel⟩, ⟨118, by decide +kernel⟩, ⟨146, by decide +kernel⟩, ⟨148, by decide +kernel⟩, ⟨173, by decide +kernel⟩, ⟨174, by decide +kernel⟩, ⟨179, by decide +kernel⟩, ⟨196, by decide +kernel⟩, ⟨198, by decide +kernel⟩, ⟨218, by decide +kernel⟩, ⟨219, by decide +kernel⟩] := by decide +kernel

private theorem completeScoped_declarations :
    RuleExecutionProgram.scopedProgram.declarations.filter (retainedCallDeclaration completeProofHeads) = completeScopedMetadataDeclarations := by
  rw [source_filter_indices, completeScoped_declarations_indices]
  rfl

private theorem completeTyped_equations_indices :
    (List.finRange completeMetadataTypedSource.equations.length).filter (fun index => (fun row => completeProofHeads row.head) (completeMetadataTypedSource.equations.get index)) =
      [⟨7, by decide +kernel⟩, ⟨18, by decide +kernel⟩] := by decide +kernel

private theorem completeTyped_equations :
    completeMetadataTypedSource.equations.filter (fun row => completeProofHeads row.head) = completeTypedMetadataEquations := by
  rw [source_filter_indices, completeTyped_equations_indices]
  rfl

private theorem completeTyped_declarations_indices :
    (List.finRange completeMetadataTypedSource.declarations.length).filter (fun index => (retainedCallDeclaration completeProofHeads) (completeMetadataTypedSource.declarations.get index)) =
      [⟨7, by decide +kernel⟩, ⟨18, by decide +kernel⟩] := by decide +kernel

private theorem completeTyped_declarations :
    completeMetadataTypedSource.declarations.filter (retainedCallDeclaration completeProofHeads) = completeTypedMetadataDeclarations := by
  rw [source_filter_indices, completeTyped_declarations_indices]
  rfl

private theorem completeDescent_equations_indices :
    (List.finRange completeMetadataDescentSource.equations.length).filter (fun index => (fun row => completeProofHeads row.head) (completeMetadataDescentSource.equations.get index)) =
      [⟨9, by decide +kernel⟩, ⟨10, by decide +kernel⟩, ⟨12, by decide +kernel⟩, ⟨13, by decide +kernel⟩] := by decide +kernel

private theorem completeDescent_equations :
    completeMetadataDescentSource.equations.filter (fun row => completeProofHeads row.head) = completeDescentMetadataEquations := by
  rw [source_filter_indices, completeDescent_equations_indices]
  rfl

private theorem completeDescent_declarations_indices :
    (List.finRange completeMetadataDescentSource.declarations.length).filter (fun index => (retainedCallDeclaration completeProofHeads) (completeMetadataDescentSource.declarations.get index)) =
      [⟨9, by decide +kernel⟩, ⟨10, by decide +kernel⟩, ⟨12, by decide +kernel⟩, ⟨13, by decide +kernel⟩] := by decide +kernel

private theorem completeDescent_declarations :
    completeMetadataDescentSource.declarations.filter (retainedCallDeclaration completeProofHeads) = completeDescentMetadataDeclarations := by
  rw [source_filter_indices, completeDescent_declarations_indices]
  rfl

private theorem completeOwned_equations :
    completeProofSource.equations.filter (fun row => completeProofHeads row.head) = completeProofSource.equations := by
  apply List.filter_eq_self.mpr
  exact List.all_eq_true.mp (by decide +kernel)

private theorem completeOwned_declarations :
    completeProofSource.declarations.filter (retainedCallDeclaration completeProofHeads) = completeProofSource.declarations := by
  apply List.filter_eq_self.mpr
  exact List.all_eq_true.mp (by decide +kernel)

private theorem completeLate_equations :
    (completeLateSources.flatMap (fun source => source.program.equations)).filter
      (fun row => completeProofHeads row.head) = [] := by
  have rejected : (completeLateSources.flatMap (fun source => source.program.equations)).all
      (fun row => !completeProofHeads row.head) = true := by decide +kernel
  apply List.filter_eq_nil_iff.mpr
  intro row member kept
  have no := List.all_eq_true.mp rejected row member
  simp [kept] at no

private theorem completeLate_declarations :
    (completeLateSources.flatMap (fun source => source.program.declarations)).filter
      (retainedCallDeclaration completeProofHeads) = [] := by
  have rejected : (completeLateSources.flatMap (fun source => source.program.declarations)).all
      (fun row => !retainedCallDeclaration completeProofHeads row) = true := by decide +kernel
  apply List.filter_eq_nil_iff.mpr
  intro row member kept
  have no := List.all_eq_true.mp rejected row member
  simp [kept] at no

/-- Retention is proved from physical composition; bodies of selected source rows stay opaque. -/
theorem completeProof_physical_equations : completeProofLibrary.runtime.equations =
    completePhysicalProgram.equations.filter (fun row => completeProofHeads row.head) := by
  rw [completePhysicalProgram, PhysicalSourceAgreement.fold_equations, completeSupport_equations]
  simp only [List.filter_append, completeScoped_equations, completeTyped_equations,
    completeDescent_equations, completeOwned_equations, completeLate_equations, List.append_nil]
  change (completeScopedMetadataEquations ++ completeTypedMetadataEquations ++
    completeDescentMetadataEquations) ++ completeProofSource.equations = _
  simp only [List.append_assoc]

theorem completeProof_physical_declarations : completeProofLibrary.runtime.declarations =
    completePhysicalProgram.declarations.filter (retainedCallDeclaration completeProofHeads) := by
  rw [completePhysicalProgram, PhysicalSourceAgreement.fold_declarations, completeSupport_declarations]
  simp only [List.filter_append, completeScoped_declarations, completeTyped_declarations,
    completeDescent_declarations, completeOwned_declarations, completeLate_declarations, List.append_nil]
  change (completeScopedMetadataDeclarations ++ completeTypedMetadataDeclarations ++
    completeDescentMetadataDeclarations) ++ completeProofSource.declarations = _
  simp only [List.append_assoc]

/-- The small source metadata agrees with the physical artifacts and hence with the one Raw runtime. -/
theorem completeProof_agreement : ProgramAgreementOn completeProofHeads completeProofLibrary.runtime runtime := by
  have physical : ProgramAgreementOn completeProofHeads completeProofLibrary.runtime completePhysicalProgram :=
    fragment_agreement _ _ completeProof_physical_equations completeProof_physical_declarations
      (fun _ supported => supported)
  exact agreement_trans physical
    (agreement_mono (fun _ _ => rfl) PhysicalSourceAgreement.physical_interpreted_agreement)

theorem completeProof_owned_agreement :
    ProgramAgreementOn completeProofLibrary.owns completeProofLibrary.runtime runtime :=
  agreement_mono (fun _ owned => completeProof_owned_supported owned) completeProof_agreement

theorem completeProof_constructor_agreement :
    ProgramAgreementOn (fun head => !head.startsWith "gslt:") completeProofLibrary.runtime runtime := by
  apply agreement_mono _ completeProof_agreement
  intro head constructor
  simp only [Bool.not_eq_true'] at constructor
  exact completeProof_constructor_supported constructor

theorem completeProof_inherited_agreement :
    ProgramAgreementOn completeProofInheritedHeads.contains completeProofLibrary.runtime runtime := by
  apply agreement_mono _ completeProof_agreement
  intro head member
  exact completeProof_inherited_supported (List.contains_iff_mem.mp member)

/-- The metadata view deliberately need not contain the implementations called by inherited bodies. -/
theorem completeProof_not_closed : ¬ ProgramClosed completeProofHeads completeProofLibrary.runtime := by
  intro closed
  let row := completeMetadataBase.equations[16]'(by decide +kernel)
  have member : row ∈ completeProofLibrary.runtime.equations := by
    apply List.mem_append_left
    exact List.getElem_mem _
  have supported : completeProofHeads row.head = true := by decide +kernel
  have outside : codeWithin completeProofHeads row.body = false := by decide +kernel
  have inside := closed.bodies row member supported
  rw [outside] at inside
  cases inside

#print axioms completeProofInheritedHeads_derived
#print axioms completeSource_equation_count
#print axioms completeProofInheritedHeads_count
#print axioms completeProof_owned_supported
#print axioms completeProof_constructor_supported
#print axioms completeProof_inherited_supported
#print axioms completeProof_inherited_rows
#print axioms completeProof_inherited_declaration_heads
#print axioms completeProof_equation_count
#print axioms completeProof_source_supported
#print axioms completeProof_checked
#print axioms completeProof_physical_equations
#print axioms completeProof_physical_declarations
#print axioms completeProof_agreement
#print axioms completeProof_owned_agreement
#print axioms completeProof_constructor_agreement
#print axioms completeProof_inherited_agreement
#print axioms completeProof_not_closed

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution

end CompleteProofView

section DescentProofView

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open SpaceSemantics (Program Equation)
open Eval BridgeKit

private def descentProofSource : Program :=
  (RuleExecutionProgram.interpretedPremiseSupportSources[1]'(by decide +kernel)).program

private def descentObservedInheritedHeads : List String :=
  ((descentProofSource.equations.flatMap (fun row => sourceLiteralHeads row.body)).filter
    (fun head => head.startsWith "gslt:" && !(descentProofSource.equations.map (·.head)).contains head)).eraseDups

/-- Direct outward calls, materialized from the pinned descent artifact's body syntax. -/
def descentProofInheritedHeads : List String := [
    "gslt:premise:context-next",
    "gslt:premise:matching-environment",
    "gslt:premise:substitution-presentation",
    "gslt:automata:length",
    "gslt:rule:scope-reduct",
    "gslt:premise:open-well-sorted",
    "gslt:premise:matching-start",
    "gslt:automata:binding",
    "gslt:rule:scope-instantiate-value",
    "gslt:rule:scope-instantiate-at",
    "gslt:premise:fresh",
    "gslt:premise:scope-collection",
    "gslt:premise:source-type",
    "gslt:automata:append",
    "gslt:premise:scope-local-value",
    "gslt:premise:scope-bind",
    "gslt:premise:context-quantified",
    "gslt:premise:check-assignment",
    "gslt:rule:row-at",
    "gslt:premise:specification",
    "gslt:premise:binding-admitted",
    "gslt:premise:matching-answer-at",
    "gslt:premise:matching-complete",
    "gslt:premise:matching-tick",
    "gslt:premise:query-obligations",
    "gslt:premise:query-expand-in",
    "gslt:premise:machine-commit"
  ]

theorem descentProofInheritedHeads_derived :
    descentObservedInheritedHeads = descentProofInheritedHeads := by decide +kernel

theorem descentProofSource_count : descentProofSource.equations.length = 15 := by decide +kernel

theorem descentProofInheritedHeads_count : descentObservedInheritedHeads.length = 27 := by
  rw [descentProofInheritedHeads_derived]
  decide +kernel

private def descentScopedMetadataEquations : List Equation := [
    RuleExecutionProgram.scopedProgram.equations[0]'(by decide +kernel),
    RuleExecutionProgram.scopedProgram.equations[1]'(by decide +kernel),
    RuleExecutionProgram.scopedProgram.equations[32]'(by decide +kernel),
    RuleExecutionProgram.scopedProgram.equations[65]'(by decide +kernel),
    RuleExecutionProgram.scopedProgram.equations[92]'(by decide +kernel),
    RuleExecutionProgram.scopedProgram.equations[126]'(by decide +kernel),
    RuleExecutionProgram.scopedProgram.equations[130]'(by decide +kernel),
    RuleExecutionProgram.scopedProgram.equations[132]'(by decide +kernel),
    RuleExecutionProgram.scopedProgram.equations[133]'(by decide +kernel),
    RuleExecutionProgram.scopedProgram.equations[146]'(by decide +kernel),
    RuleExecutionProgram.scopedProgram.equations[148]'(by decide +kernel),
    RuleExecutionProgram.scopedProgram.equations[149]'(by decide +kernel),
    RuleExecutionProgram.scopedProgram.equations[150]'(by decide +kernel),
    RuleExecutionProgram.scopedProgram.equations[155]'(by decide +kernel),
    RuleExecutionProgram.scopedProgram.equations[156]'(by decide +kernel),
    RuleExecutionProgram.scopedProgram.equations[166]'(by decide +kernel),
    RuleExecutionProgram.scopedProgram.equations[169]'(by decide +kernel),
    RuleExecutionProgram.scopedProgram.equations[196]'(by decide +kernel),
    RuleExecutionProgram.scopedProgram.equations[198]'(by decide +kernel),
    RuleExecutionProgram.scopedProgram.equations[203]'(by decide +kernel),
    RuleExecutionProgram.scopedProgram.equations[213]'(by decide +kernel),
    RuleExecutionProgram.scopedProgram.equations[214]'(by decide +kernel),
    RuleExecutionProgram.scopedProgram.equations[220]'(by decide +kernel),
    RuleExecutionProgram.scopedProgram.equations[221]'(by decide +kernel),
    RuleExecutionProgram.scopedProgram.equations[222]'(by decide +kernel),
    RuleExecutionProgram.scopedProgram.equations[223]'(by decide +kernel),
    RuleExecutionProgram.scopedProgram.equations[224]'(by decide +kernel)
  ]

private def descentScopedMetadataDeclarations : List Atom := [
    RuleExecutionProgram.scopedProgram.declarations[0]'(by decide +kernel),
    RuleExecutionProgram.scopedProgram.declarations[1]'(by decide +kernel),
    RuleExecutionProgram.scopedProgram.declarations[32]'(by decide +kernel),
    RuleExecutionProgram.scopedProgram.declarations[65]'(by decide +kernel),
    RuleExecutionProgram.scopedProgram.declarations[92]'(by decide +kernel),
    RuleExecutionProgram.scopedProgram.declarations[126]'(by decide +kernel),
    RuleExecutionProgram.scopedProgram.declarations[130]'(by decide +kernel),
    RuleExecutionProgram.scopedProgram.declarations[132]'(by decide +kernel),
    RuleExecutionProgram.scopedProgram.declarations[133]'(by decide +kernel),
    RuleExecutionProgram.scopedProgram.declarations[146]'(by decide +kernel),
    RuleExecutionProgram.scopedProgram.declarations[148]'(by decide +kernel),
    RuleExecutionProgram.scopedProgram.declarations[149]'(by decide +kernel),
    RuleExecutionProgram.scopedProgram.declarations[150]'(by decide +kernel),
    RuleExecutionProgram.scopedProgram.declarations[155]'(by decide +kernel),
    RuleExecutionProgram.scopedProgram.declarations[156]'(by decide +kernel),
    RuleExecutionProgram.scopedProgram.declarations[166]'(by decide +kernel),
    RuleExecutionProgram.scopedProgram.declarations[169]'(by decide +kernel),
    RuleExecutionProgram.scopedProgram.declarations[196]'(by decide +kernel),
    RuleExecutionProgram.scopedProgram.declarations[198]'(by decide +kernel),
    RuleExecutionProgram.scopedProgram.declarations[203]'(by decide +kernel),
    RuleExecutionProgram.scopedProgram.declarations[213]'(by decide +kernel),
    RuleExecutionProgram.scopedProgram.declarations[214]'(by decide +kernel),
    RuleExecutionProgram.scopedProgram.declarations[220]'(by decide +kernel),
    RuleExecutionProgram.scopedProgram.declarations[221]'(by decide +kernel),
    RuleExecutionProgram.scopedProgram.declarations[222]'(by decide +kernel),
    RuleExecutionProgram.scopedProgram.declarations[223]'(by decide +kernel),
    RuleExecutionProgram.scopedProgram.declarations[224]'(by decide +kernel)
  ]

private def descentMetadataBase : Program where
  equations := descentScopedMetadataEquations
  declarations := descentScopedMetadataDeclarations
  layout := List.replicate 27 .equation ++ List.replicate 27 .declaration

/-- Bounded body and ABI metadata; operational conclusions still execute in runtime. -/
def descentProofLibrary : BridgeKit.Library :=
  ⟨descentMetadataBase, descentProofSource, ["gslt:descent:"]⟩

def descentProofHeads (head : String) : Bool :=
  !head.startsWith "gslt:" || descentProofLibrary.owns head || descentProofInheritedHeads.contains head

theorem descentProof_owned_supported {head : String} (owned : descentProofLibrary.owns head = true) :
    descentProofHeads head = true := by simp [descentProofHeads, owned]

theorem descentProof_constructor_supported {head : String} (constructor : head.startsWith "gslt:" = false) :
    descentProofHeads head = true := by simp [descentProofHeads, constructor]

theorem descentProof_inherited_supported {head : String} (member : head ∈ descentProofInheritedHeads) :
    descentProofHeads head = true := by
  have contained := List.contains_iff_mem.mpr member
  simp only [descentProofHeads, contained, Bool.or_true]

theorem descentProof_inherited_rows :
    descentMetadataBase.equations.all (fun row => descentProofInheritedHeads.contains row.head) = true ∧
      descentProofInheritedHeads.all (fun head => descentMetadataBase.equations.any (fun row => row.head == head)) = true := by
  constructor <;> decide +kernel

theorem descentProof_inherited_declaration_heads :
    (descentMetadataBase.declarations.filterMap BridgeKit.arrowHead).all descentProofInheritedHeads.contains = true ∧
      descentProofInheritedHeads.all (descentMetadataBase.declarations.filterMap BridgeKit.arrowHead).contains = true := by
  constructor <;> decide +kernel

theorem descentProof_base_count : descentMetadataBase.equations.length = 27 := by decide +kernel

theorem descentProof_equation_count : descentProofLibrary.runtime.equations.length = 42 := by decide +kernel

theorem descentProof_source_supported :
    descentProofSource.equations.all (fun row => codeWithin descentProofHeads row.body) = true := by decide +kernel

theorem descentProof_checked : descentProofLibrary.check = true := by decide +kernel

private def descentPhysicalProgram : Program :=
  RuleExecutionProgram.interpretedPremiseSupportSources.foldl
    (fun loaded source => loaded.append source.program) RuleExecutionProgram.scopedProgram

private def descentMetadataTypedSource : Program :=
  (RuleExecutionProgram.interpretedPremiseSupportSources[0]'(by decide +kernel)).program

private def descentLateSources : List ProgramQuotation.QuotedProgram :=
  RuleExecutionProgram.interpretedPremiseSupportSources.drop 2

private theorem descentScoped_equations_indices :
    (List.finRange RuleExecutionProgram.scopedProgram.equations.length).filter (fun index => (fun row => descentProofHeads row.head) (RuleExecutionProgram.scopedProgram.equations.get index)) =
      [⟨0, by decide +kernel⟩, ⟨1, by decide +kernel⟩, ⟨32, by decide +kernel⟩, ⟨65, by decide +kernel⟩, ⟨92, by decide +kernel⟩, ⟨126, by decide +kernel⟩, ⟨130, by decide +kernel⟩, ⟨132, by decide +kernel⟩, ⟨133, by decide +kernel⟩, ⟨146, by decide +kernel⟩, ⟨148, by decide +kernel⟩, ⟨149, by decide +kernel⟩, ⟨150, by decide +kernel⟩, ⟨155, by decide +kernel⟩, ⟨156, by decide +kernel⟩, ⟨166, by decide +kernel⟩, ⟨169, by decide +kernel⟩, ⟨196, by decide +kernel⟩, ⟨198, by decide +kernel⟩, ⟨203, by decide +kernel⟩, ⟨213, by decide +kernel⟩, ⟨214, by decide +kernel⟩, ⟨220, by decide +kernel⟩, ⟨221, by decide +kernel⟩, ⟨222, by decide +kernel⟩, ⟨223, by decide +kernel⟩, ⟨224, by decide +kernel⟩] := by decide +kernel

private theorem descentScoped_equations :
    RuleExecutionProgram.scopedProgram.equations.filter (fun row => descentProofHeads row.head) = descentScopedMetadataEquations := by
  rw [source_filter_indices, descentScoped_equations_indices]
  rfl

private theorem descentSupport_equations :
    RuleExecutionProgram.interpretedPremiseSupportSources.flatMap (fun source => source.program.equations) =
      descentMetadataTypedSource.equations ++ descentProofSource.equations ++
        descentLateSources.flatMap (fun source => source.program.equations) := by
  have split : RuleExecutionProgram.interpretedPremiseSupportSources =
      RuleExecutionProgram.interpretedPremiseSupportSources[0]'(by decide +kernel) ::
      RuleExecutionProgram.interpretedPremiseSupportSources[1]'(by decide +kernel) :: descentLateSources := rfl
  conv_lhs => rw [split, List.flatMap_cons, List.flatMap_cons]
  rfl

private theorem descentTyped_equations :
    descentMetadataTypedSource.equations.filter (fun row => descentProofHeads row.head) = [] := by
  have rejected : descentMetadataTypedSource.equations.all (fun row => !(fun row => descentProofHeads row.head) row) = true := by decide +kernel
  apply List.filter_eq_nil_iff.mpr
  intro row member kept
  have no := List.all_eq_true.mp rejected row member
  simp [kept] at no

private theorem descentLate_equations :
    (descentLateSources.flatMap (fun source => source.program.equations)).filter (fun row => descentProofHeads row.head) = [] := by
  have rejected : (descentLateSources.flatMap (fun source => source.program.equations)).all (fun row => !(fun row => descentProofHeads row.head) row) = true := by decide +kernel
  apply List.filter_eq_nil_iff.mpr
  intro row member kept
  have no := List.all_eq_true.mp rejected row member
  simp [kept] at no

private theorem descentOwned_equations :
    descentProofSource.equations.filter (fun row => descentProofHeads row.head) = descentProofSource.equations := by
  apply List.filter_eq_self.mpr
  exact List.all_eq_true.mp (by decide +kernel)

theorem descentProof_physical_equations : descentProofLibrary.runtime.equations =
    descentPhysicalProgram.equations.filter (fun row => descentProofHeads row.head) := by
  rw [descentPhysicalProgram, PhysicalSourceAgreement.fold_equations, descentSupport_equations]
  simp only [List.filter_append, descentScoped_equations, descentTyped_equations,
    descentOwned_equations, descentLate_equations, List.nil_append, List.append_nil]
  rfl

private theorem descentScoped_declarations_indices :
    (List.finRange RuleExecutionProgram.scopedProgram.declarations.length).filter (fun index => (retainedCallDeclaration descentProofHeads) (RuleExecutionProgram.scopedProgram.declarations.get index)) =
      [⟨0, by decide +kernel⟩, ⟨1, by decide +kernel⟩, ⟨32, by decide +kernel⟩, ⟨65, by decide +kernel⟩, ⟨92, by decide +kernel⟩, ⟨126, by decide +kernel⟩, ⟨130, by decide +kernel⟩, ⟨132, by decide +kernel⟩, ⟨133, by decide +kernel⟩, ⟨146, by decide +kernel⟩, ⟨148, by decide +kernel⟩, ⟨149, by decide +kernel⟩, ⟨150, by decide +kernel⟩, ⟨155, by decide +kernel⟩, ⟨156, by decide +kernel⟩, ⟨166, by decide +kernel⟩, ⟨169, by decide +kernel⟩, ⟨196, by decide +kernel⟩, ⟨198, by decide +kernel⟩, ⟨203, by decide +kernel⟩, ⟨213, by decide +kernel⟩, ⟨214, by decide +kernel⟩, ⟨220, by decide +kernel⟩, ⟨221, by decide +kernel⟩, ⟨222, by decide +kernel⟩, ⟨223, by decide +kernel⟩, ⟨224, by decide +kernel⟩] := by decide +kernel

private theorem descentScoped_declarations :
    RuleExecutionProgram.scopedProgram.declarations.filter (retainedCallDeclaration descentProofHeads) = descentScopedMetadataDeclarations := by
  rw [source_filter_indices, descentScoped_declarations_indices]
  rfl

private theorem descentSupport_declarations :
    RuleExecutionProgram.interpretedPremiseSupportSources.flatMap (fun source => source.program.declarations) =
      descentMetadataTypedSource.declarations ++ descentProofSource.declarations ++
        descentLateSources.flatMap (fun source => source.program.declarations) := by
  have split : RuleExecutionProgram.interpretedPremiseSupportSources =
      RuleExecutionProgram.interpretedPremiseSupportSources[0]'(by decide +kernel) ::
      RuleExecutionProgram.interpretedPremiseSupportSources[1]'(by decide +kernel) :: descentLateSources := rfl
  conv_lhs => rw [split, List.flatMap_cons, List.flatMap_cons]
  rfl

private theorem descentTyped_declarations :
    descentMetadataTypedSource.declarations.filter (retainedCallDeclaration descentProofHeads) = [] := by
  have rejected : descentMetadataTypedSource.declarations.all (fun row => !(retainedCallDeclaration descentProofHeads) row) = true := by decide +kernel
  apply List.filter_eq_nil_iff.mpr
  intro row member kept
  have no := List.all_eq_true.mp rejected row member
  simp [kept] at no

private theorem descentLate_declarations :
    (descentLateSources.flatMap (fun source => source.program.declarations)).filter (retainedCallDeclaration descentProofHeads) = [] := by
  have rejected : (descentLateSources.flatMap (fun source => source.program.declarations)).all (fun row => !(retainedCallDeclaration descentProofHeads) row) = true := by decide +kernel
  apply List.filter_eq_nil_iff.mpr
  intro row member kept
  have no := List.all_eq_true.mp rejected row member
  simp [kept] at no

private theorem descentOwned_declarations :
    descentProofSource.declarations.filter (retainedCallDeclaration descentProofHeads) = descentProofSource.declarations := by
  apply List.filter_eq_self.mpr
  exact List.all_eq_true.mp (by decide +kernel)

theorem descentProof_physical_declarations : descentProofLibrary.runtime.declarations =
    descentPhysicalProgram.declarations.filter (retainedCallDeclaration descentProofHeads) := by
  rw [descentPhysicalProgram, PhysicalSourceAgreement.fold_declarations, descentSupport_declarations]
  simp only [List.filter_append, descentScoped_declarations, descentTyped_declarations,
    descentOwned_declarations, descentLate_declarations, List.nil_append, List.append_nil]
  rfl

/-- Agreement checks owned calls, inherited raw calls and literal constructor templates. -/
theorem descentProof_agreement : ProgramAgreementOn descentProofHeads descentProofLibrary.runtime runtime := by
  have physical : ProgramAgreementOn descentProofHeads descentProofLibrary.runtime descentPhysicalProgram :=
    fragment_agreement _ _ descentProof_physical_equations descentProof_physical_declarations
      (fun _ supported => supported)
  exact agreement_trans physical
    (agreement_mono (fun _ _ => rfl) PhysicalSourceAgreement.physical_interpreted_agreement)

theorem descentProof_owned_agreement :
    ProgramAgreementOn descentProofLibrary.owns descentProofLibrary.runtime runtime :=
  agreement_mono (fun _ owned => descentProof_owned_supported owned) descentProof_agreement

theorem descentProof_constructor_agreement :
    ProgramAgreementOn (fun head => !head.startsWith "gslt:") descentProofLibrary.runtime runtime := by
  apply agreement_mono _ descentProof_agreement
  intro head constructor
  simp only [Bool.not_eq_true'] at constructor
  exact descentProof_constructor_supported constructor

theorem descentProof_inherited_agreement :
    ProgramAgreementOn descentProofInheritedHeads.contains descentProofLibrary.runtime runtime := by
  apply agreement_mono _ descentProof_agreement
  intro head member
  exact descentProof_inherited_supported (List.contains_iff_mem.mp member)

/-- Inherited bodies are metadata; they need not close inside the bounded view. -/
theorem descentProof_not_closed : ¬ ProgramClosed descentProofHeads descentProofLibrary.runtime := by
  intro closed
  let row := descentMetadataBase.equations[16]'(by decide +kernel)
  have member : row ∈ descentProofLibrary.runtime.equations := by
    apply List.mem_append_left
    exact List.getElem_mem _
  have supported : descentProofHeads row.head = true := by decide +kernel
  have outside : codeWithin descentProofHeads row.body = false := by decide +kernel
  have inside := closed.bodies row member supported
  rw [outside] at inside
  cases inside

#print axioms descentProofInheritedHeads_derived
#print axioms descentProofSource_count
#print axioms descentProofInheritedHeads_count
#print axioms descentProof_owned_supported
#print axioms descentProof_constructor_supported
#print axioms descentProof_inherited_supported
#print axioms descentProof_inherited_rows
#print axioms descentProof_inherited_declaration_heads
#print axioms descentProof_base_count
#print axioms descentProof_equation_count
#print axioms descentProof_source_supported
#print axioms descentProof_checked
#print axioms descentProof_physical_equations
#print axioms descentProof_physical_declarations
#print axioms descentProof_agreement
#print axioms descentProof_owned_agreement
#print axioms descentProof_constructor_agreement
#print axioms descentProof_inherited_agreement
#print axioms descentProof_not_closed

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution

end DescentProofView


section SelectedNativeSourceView

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CollectionOccurrenceSearchExecution.SelectedNativeSource
open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open SpaceSemantics Eval BridgeKit
open scoped ProgramQuotation

def continuationSource : ProgramQuotation.QuotedProgram :=
  petta_source_file%
    "../../../../../../../../../metta/gslt/lib/gslt_collection_continuation.metta"
    sha256 "d0712043381250e511d655826644a6751904c49c6536beb058cd9abe11596892"
def occurrenceSource : ProgramQuotation.QuotedProgram :=
  petta_source_file% "../../../../../../../../../metta/gslt/lib/gslt_collection_occurrence_search.metta"
    sha256 "001f4aae5597a31df16243635be54671b09475c463e6c13646502aee78e30f44"
def collectorSource : ProgramQuotation.QuotedProgram :=
  petta_source_file% "../../../../../../../../../metta/gslt/lib/gslt_collection_collector.metta"
    sha256 "b4f55a7bd581963f8a91f35b3b70bbbb383151b5096799fb1341ee8ac6e1ae40"
def oldSources := RuleExecutionProgram.interpretedPremiseSupportSources
def oldContinuation : ProgramQuotation.QuotedProgram := oldSources[13]'(by decide +kernel)
def oldCollector : ProgramQuotation.QuotedProgram := oldSources[17]'(by decide +kernel)
def oldOccurrence : ProgramQuotation.QuotedProgram := oldSources[20]'(by decide +kernel)
def sources : List ProgramQuotation.QuotedProgram :=
  oldSources.take 13 ++ [continuationSource] ++ (oldSources.drop 14).take 3 ++
    [collectorSource] ++ (oldSources.drop 18).take 2 ++ [occurrenceSource] ++ oldSources.drop 21
def runtime : Program :=
  let base := RuleExecutionProgram.callFragmentWhere
    (fun head => !head.startsWith "gslt:premise:matching-") RuleExecutionProgram.scopedProgram
  let support := sources.foldl (fun loaded part => loaded.append part.program) base
  support.append (RuleExecutionProgram.callFragmentWhere
    (fun head => head.startsWith "gslt:premise:matching-") RuleExecutionProgram.scopedProgram)
def excluded : List String := ["gslt:collection-continuation:begin", "gslt:collection-continuation:publication", "gslt:collection-continuation:results", "gslt:collection-continuation:run", "gslt:explore:begin", "gslt:explore:children", "gslt:explore:edges", "gslt:explore:expand", "gslt:explore:expand-all", "gslt:explore:node-edges", "gslt:explore:receipt-edges", "gslt:explore:rounds", "gslt:explore:settled", "gslt:explore:step", "gslt:occurrence-batch:advance-frames", "gslt:occurrence-batch:frame-begin", "gslt:occurrence-batch:frame-publication", "gslt:occurrence-batch:frame-run", "gslt:occurrence-batch:resume", "gslt:occurrence-batch:run", "gslt:occurrence-collector:advance-lane", "gslt:occurrence-collector:advance-lanes", "gslt:occurrence-collector:allocate", "gslt:occurrence-collector:collect", "gslt:occurrence-machine:round", "gslt:occurrence-machine:run", "gslt:occurrence-search:finish", "gslt:occurrence-search:frames-idle", "gslt:occurrence-search:frames-resolved", "gslt:occurrence-search:lanes-complete", "gslt:occurrence-search:publication", "gslt:occurrence-search:read-committed", "gslt:occurrence-search:read-log", "gslt:occurrence-search:resume", "gslt:occurrence-search:run", "gslt:occurrence-search:status", "gslt:occurrence-search:target", "gslt:occurrence-search:with-state", "gslt:runner:advance", "gslt:runner:begin", "gslt:runner:target", "gslt:runner:tick", "gslt:search:publication", "gslt:search:resume", "gslt:search:run", "gslt:search:status", "gslt:search:target", "gslt:occurrence-search:key-event", "gslt:occurrence-search:key-history", "gslt:occurrence-search:key-elements", "gslt:occurrence-search:key-binding", "gslt:occurrence-search:key-values", "gslt:occurrence-search:key-extract", "gslt:occurrence-search:key-project", "gslt:occurrence-search:key-unique", "gslt:occurrence-search:key-binary", "gslt:occurrence-search:key-conclusions", "gslt:occurrence-search:key-bag", "gslt:occurrence-search:key-facts"]
def lowerHeads (head : String) : Bool := !excluded.contains head && !head.startsWith "native-probe:"

private theorem oldSources_shape : oldSources = oldSources.take 13 ++ [oldContinuation] ++
    (oldSources.drop 14).take 3 ++ [oldCollector] ++ (oldSources.drop 18).take 2 ++
    [oldOccurrence] ++ oldSources.drop 21 := by rfl
private theorem append_equations (first second : Program) :
    (first.append second).equations = first.equations ++ second.equations := rfl
private theorem append_declarations (first second : Program) :
    (first.append second).declarations = first.declarations ++ second.declarations := rfl
private theorem oldContinuation_equations_erased :
    oldContinuation.program.equations.filter (fun row => lowerHeads row.head) = [] := by decide +kernel
private theorem oldContinuation_declarations_erased :
    oldContinuation.program.declarations.filter (retainedCallDeclaration lowerHeads) = [] := by decide +kernel
private theorem continuationSource_equations_erased :
    continuationSource.program.equations.filter (fun row => lowerHeads row.head) = [] := by decide +kernel
private theorem continuationSource_declarations_erased :
    continuationSource.program.declarations.filter (retainedCallDeclaration lowerHeads) = [] := by decide +kernel
private theorem oldOccurrence_equations_erased :
    oldOccurrence.program.equations.filter (fun row => lowerHeads row.head) = [] := by decide +kernel
private theorem oldOccurrence_declarations_erased :
    oldOccurrence.program.declarations.filter (retainedCallDeclaration lowerHeads) = [] := by decide +kernel
private theorem occurrenceSource_equations_erased :
    occurrenceSource.program.equations.filter (fun row => lowerHeads row.head) = [] := by decide +kernel
private theorem occurrenceSource_declarations_erased :
    occurrenceSource.program.declarations.filter (retainedCallDeclaration lowerHeads) = [] := by decide +kernel

private theorem oldCollector_equations_erased :
    oldCollector.program.equations.filter (fun row => lowerHeads row.head) = [] := by decide +kernel
private theorem oldCollector_declarations_erased :
    oldCollector.program.declarations.filter (retainedCallDeclaration lowerHeads) = [] := by decide +kernel
private theorem collectorSource_equations_erased :
    collectorSource.program.equations.filter (fun row => lowerHeads row.head) = [] := by decide +kernel
private theorem collectorSource_declarations_erased :
    collectorSource.program.declarations.filter (retainedCallDeclaration lowerHeads) = [] := by decide +kernel

private theorem support_equations_agree :
    (oldSources.flatMap (fun part => part.program.equations)).filter (fun row => lowerHeads row.head) =
    (sources.flatMap (fun part => part.program.equations)).filter (fun row => lowerHeads row.head) := by
  conv_lhs => rw [oldSources_shape]
  simp only [sources, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
    List.filter_append, oldContinuation_equations_erased, continuationSource_equations_erased,
    oldOccurrence_equations_erased, occurrenceSource_equations_erased,
    oldCollector_equations_erased, collectorSource_equations_erased, List.append_nil]

private theorem support_declarations_agree :
    (oldSources.flatMap (fun part => part.program.declarations)).filter (retainedCallDeclaration lowerHeads) =
    (sources.flatMap (fun part => part.program.declarations)).filter (retainedCallDeclaration lowerHeads) := by
  conv_lhs => rw [oldSources_shape]
  simp only [sources, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
    List.filter_append, oldContinuation_declarations_erased, continuationSource_declarations_erased,
    oldOccurrence_declarations_erased, occurrenceSource_declarations_erased,
    oldCollector_declarations_erased, collectorSource_declarations_erased, List.append_nil]

theorem lower_agreement : ProgramAgreementOn lowerHeads RuleExecutionProgram.interpretedPremiseProgram runtime := by
  apply programAgreementOn_of_retained_rows
  · have same := support_equations_agree
    unfold oldSources at same
    simp only [RuleExecutionProgram.interpretedPremiseProgram, runtime, append_equations,
      CompleteExecution.PhysicalSourceAgreement.fold_equations, List.filter_append]
    rw [same]
  · have same := support_declarations_agree
    unfold oldSources at same
    simp only [RuleExecutionProgram.interpretedPremiseProgram, runtime, append_declarations,
      CompleteExecution.PhysicalSourceAgreement.fold_declarations, List.filter_append]
    rw [same]

private def closedRow (row : Equation) : Bool := !lowerHeads row.head || codeWithin lowerHeads row.body

private theorem all_split {α : Type} (items : List α) (test : α → Bool) (count : Nat)
    (front : (items.take count).all test = true) (back : (items.drop count).all test = true) :
    items.all test = true := by
  have together : (items.take count ++ items.drop count).all test = true := by
    rw [List.all_append, front, back]
    rfl
  simpa only [List.take_append_drop] using together

private theorem closed_block_0 :
    ((RuleExecutionProgram.interpretedPremiseProgram.equations.drop 0).take 20).all closedRow = true := by
  decide +kernel
private theorem closed_block_20 :
    ((RuleExecutionProgram.interpretedPremiseProgram.equations.drop 20).take 20).all closedRow = true := by
  decide +kernel
private theorem closed_block_40 :
    ((RuleExecutionProgram.interpretedPremiseProgram.equations.drop 40).take 20).all closedRow = true := by
  decide +kernel
private theorem closed_block_60 :
    ((RuleExecutionProgram.interpretedPremiseProgram.equations.drop 60).take 20).all closedRow = true := by
  decide +kernel
private theorem closed_block_80 :
    ((RuleExecutionProgram.interpretedPremiseProgram.equations.drop 80).take 20).all closedRow = true := by
  decide +kernel
private theorem closed_block_100 :
    ((RuleExecutionProgram.interpretedPremiseProgram.equations.drop 100).take 20).all closedRow = true := by
  decide +kernel
private theorem closed_block_120 :
    ((RuleExecutionProgram.interpretedPremiseProgram.equations.drop 120).take 20).all closedRow = true := by
  decide +kernel
private theorem closed_block_140 :
    ((RuleExecutionProgram.interpretedPremiseProgram.equations.drop 140).take 20).all closedRow = true := by
  decide +kernel
private theorem closed_block_160 :
    ((RuleExecutionProgram.interpretedPremiseProgram.equations.drop 160).take 20).all closedRow = true := by
  decide +kernel
private theorem closed_block_180 :
    ((RuleExecutionProgram.interpretedPremiseProgram.equations.drop 180).take 20).all closedRow = true := by
  decide +kernel
private theorem closed_block_200 :
    ((RuleExecutionProgram.interpretedPremiseProgram.equations.drop 200).take 20).all closedRow = true := by
  decide +kernel
private theorem closed_block_220 :
    ((RuleExecutionProgram.interpretedPremiseProgram.equations.drop 220).take 20).all closedRow = true := by
  decide +kernel
private theorem closed_block_240 :
    ((RuleExecutionProgram.interpretedPremiseProgram.equations.drop 240).take 20).all closedRow = true := by
  decide +kernel
private theorem closed_block_260 :
    ((RuleExecutionProgram.interpretedPremiseProgram.equations.drop 260).take 20).all closedRow = true := by
  decide +kernel
private theorem closed_block_280 :
    ((RuleExecutionProgram.interpretedPremiseProgram.equations.drop 280).take 20).all closedRow = true := by
  decide +kernel
private theorem closed_block_300 :
    ((RuleExecutionProgram.interpretedPremiseProgram.equations.drop 300).take 20).all closedRow = true := by
  decide +kernel
private theorem closed_block_320 :
    ((RuleExecutionProgram.interpretedPremiseProgram.equations.drop 320).take 20).all closedRow = true := by
  decide +kernel
private theorem closed_block_340 :
    ((RuleExecutionProgram.interpretedPremiseProgram.equations.drop 340).take 20).all closedRow = true := by
  decide +kernel
private theorem closed_block_360 :
    ((RuleExecutionProgram.interpretedPremiseProgram.equations.drop 360).take 20).all closedRow = true := by
  decide +kernel
private theorem closed_block_380 :
    ((RuleExecutionProgram.interpretedPremiseProgram.equations.drop 380).take 20).all closedRow = true := by
  decide +kernel
private theorem closed_block_400 :
    ((RuleExecutionProgram.interpretedPremiseProgram.equations.drop 400).take 20).all closedRow = true := by
  decide +kernel
private theorem closed_block_420 :
    ((RuleExecutionProgram.interpretedPremiseProgram.equations.drop 420).take 20).all closedRow = true := by
  decide +kernel
private theorem closed_block_440 :
    ((RuleExecutionProgram.interpretedPremiseProgram.equations.drop 440).take 20).all closedRow = true := by
  decide +kernel
private theorem closed_block_460 :
    ((RuleExecutionProgram.interpretedPremiseProgram.equations.drop 460).take 20).all closedRow = true := by
  decide +kernel
private theorem closed_block_480 :
    ((RuleExecutionProgram.interpretedPremiseProgram.equations.drop 480).take 20).all closedRow = true := by
  decide +kernel
private theorem closed_block_500 :
    ((RuleExecutionProgram.interpretedPremiseProgram.equations.drop 500).take 20).all closedRow = true := by
  decide +kernel
private theorem closed_block_520 :
    ((RuleExecutionProgram.interpretedPremiseProgram.equations.drop 520).take 20).all closedRow = true := by
  decide +kernel
private theorem closed_block_540 :
    ((RuleExecutionProgram.interpretedPremiseProgram.equations.drop 540).take 20).all closedRow = true := by
  decide +kernel
private theorem closed_suffix_560 :
    (RuleExecutionProgram.interpretedPremiseProgram.equations.drop 560).all closedRow = true := by
  decide +kernel
private theorem closed_suffix_540 :
    (RuleExecutionProgram.interpretedPremiseProgram.equations.drop 540).all closedRow = true := by
  apply all_split _ _ 20 closed_block_540
  simpa only [List.drop_drop] using closed_suffix_560
private theorem closed_suffix_520 :
    (RuleExecutionProgram.interpretedPremiseProgram.equations.drop 520).all closedRow = true := by
  apply all_split _ _ 20 closed_block_520
  simpa only [List.drop_drop] using closed_suffix_540
private theorem closed_suffix_500 :
    (RuleExecutionProgram.interpretedPremiseProgram.equations.drop 500).all closedRow = true := by
  apply all_split _ _ 20 closed_block_500
  simpa only [List.drop_drop] using closed_suffix_520
private theorem closed_suffix_480 :
    (RuleExecutionProgram.interpretedPremiseProgram.equations.drop 480).all closedRow = true := by
  apply all_split _ _ 20 closed_block_480
  simpa only [List.drop_drop] using closed_suffix_500
private theorem closed_suffix_460 :
    (RuleExecutionProgram.interpretedPremiseProgram.equations.drop 460).all closedRow = true := by
  apply all_split _ _ 20 closed_block_460
  simpa only [List.drop_drop] using closed_suffix_480
private theorem closed_suffix_440 :
    (RuleExecutionProgram.interpretedPremiseProgram.equations.drop 440).all closedRow = true := by
  apply all_split _ _ 20 closed_block_440
  simpa only [List.drop_drop] using closed_suffix_460
private theorem closed_suffix_420 :
    (RuleExecutionProgram.interpretedPremiseProgram.equations.drop 420).all closedRow = true := by
  apply all_split _ _ 20 closed_block_420
  simpa only [List.drop_drop] using closed_suffix_440
private theorem closed_suffix_400 :
    (RuleExecutionProgram.interpretedPremiseProgram.equations.drop 400).all closedRow = true := by
  apply all_split _ _ 20 closed_block_400
  simpa only [List.drop_drop] using closed_suffix_420
private theorem closed_suffix_380 :
    (RuleExecutionProgram.interpretedPremiseProgram.equations.drop 380).all closedRow = true := by
  apply all_split _ _ 20 closed_block_380
  simpa only [List.drop_drop] using closed_suffix_400
private theorem closed_suffix_360 :
    (RuleExecutionProgram.interpretedPremiseProgram.equations.drop 360).all closedRow = true := by
  apply all_split _ _ 20 closed_block_360
  simpa only [List.drop_drop] using closed_suffix_380
private theorem closed_suffix_340 :
    (RuleExecutionProgram.interpretedPremiseProgram.equations.drop 340).all closedRow = true := by
  apply all_split _ _ 20 closed_block_340
  simpa only [List.drop_drop] using closed_suffix_360
private theorem closed_suffix_320 :
    (RuleExecutionProgram.interpretedPremiseProgram.equations.drop 320).all closedRow = true := by
  apply all_split _ _ 20 closed_block_320
  simpa only [List.drop_drop] using closed_suffix_340
private theorem closed_suffix_300 :
    (RuleExecutionProgram.interpretedPremiseProgram.equations.drop 300).all closedRow = true := by
  apply all_split _ _ 20 closed_block_300
  simpa only [List.drop_drop] using closed_suffix_320
private theorem closed_suffix_280 :
    (RuleExecutionProgram.interpretedPremiseProgram.equations.drop 280).all closedRow = true := by
  apply all_split _ _ 20 closed_block_280
  simpa only [List.drop_drop] using closed_suffix_300
private theorem closed_suffix_260 :
    (RuleExecutionProgram.interpretedPremiseProgram.equations.drop 260).all closedRow = true := by
  apply all_split _ _ 20 closed_block_260
  simpa only [List.drop_drop] using closed_suffix_280
private theorem closed_suffix_240 :
    (RuleExecutionProgram.interpretedPremiseProgram.equations.drop 240).all closedRow = true := by
  apply all_split _ _ 20 closed_block_240
  simpa only [List.drop_drop] using closed_suffix_260
private theorem closed_suffix_220 :
    (RuleExecutionProgram.interpretedPremiseProgram.equations.drop 220).all closedRow = true := by
  apply all_split _ _ 20 closed_block_220
  simpa only [List.drop_drop] using closed_suffix_240
private theorem closed_suffix_200 :
    (RuleExecutionProgram.interpretedPremiseProgram.equations.drop 200).all closedRow = true := by
  apply all_split _ _ 20 closed_block_200
  simpa only [List.drop_drop] using closed_suffix_220
private theorem closed_suffix_180 :
    (RuleExecutionProgram.interpretedPremiseProgram.equations.drop 180).all closedRow = true := by
  apply all_split _ _ 20 closed_block_180
  simpa only [List.drop_drop] using closed_suffix_200
private theorem closed_suffix_160 :
    (RuleExecutionProgram.interpretedPremiseProgram.equations.drop 160).all closedRow = true := by
  apply all_split _ _ 20 closed_block_160
  simpa only [List.drop_drop] using closed_suffix_180
private theorem closed_suffix_140 :
    (RuleExecutionProgram.interpretedPremiseProgram.equations.drop 140).all closedRow = true := by
  apply all_split _ _ 20 closed_block_140
  simpa only [List.drop_drop] using closed_suffix_160
private theorem closed_suffix_120 :
    (RuleExecutionProgram.interpretedPremiseProgram.equations.drop 120).all closedRow = true := by
  apply all_split _ _ 20 closed_block_120
  simpa only [List.drop_drop] using closed_suffix_140
private theorem closed_suffix_100 :
    (RuleExecutionProgram.interpretedPremiseProgram.equations.drop 100).all closedRow = true := by
  apply all_split _ _ 20 closed_block_100
  simpa only [List.drop_drop] using closed_suffix_120
private theorem closed_suffix_80 :
    (RuleExecutionProgram.interpretedPremiseProgram.equations.drop 80).all closedRow = true := by
  apply all_split _ _ 20 closed_block_80
  simpa only [List.drop_drop] using closed_suffix_100
private theorem closed_suffix_60 :
    (RuleExecutionProgram.interpretedPremiseProgram.equations.drop 60).all closedRow = true := by
  apply all_split _ _ 20 closed_block_60
  simpa only [List.drop_drop] using closed_suffix_80
private theorem closed_suffix_40 :
    (RuleExecutionProgram.interpretedPremiseProgram.equations.drop 40).all closedRow = true := by
  apply all_split _ _ 20 closed_block_40
  simpa only [List.drop_drop] using closed_suffix_60
private theorem closed_suffix_20 :
    (RuleExecutionProgram.interpretedPremiseProgram.equations.drop 20).all closedRow = true := by
  apply all_split _ _ 20 closed_block_20
  simpa only [List.drop_drop] using closed_suffix_40
private theorem closed_suffix_0 :
    (RuleExecutionProgram.interpretedPremiseProgram.equations.drop 0).all closedRow = true := by
  apply all_split _ _ 20 closed_block_0
  simpa only [List.drop_drop] using closed_suffix_20

theorem lower_closed : ProgramClosed lowerHeads RuleExecutionProgram.interpretedPremiseProgram := by
  apply closed_of_all _ _ (by decide +kernel)
  exact closed_suffix_0

theorem transport_lower {caller : Mettapedia.Languages.ProcessCalculi.MORK.Subst}
    {before after : Effects.State} {code answer : Atom}
    (within : codeWithin lowerHeads code = true)
    (returned : PureReturns RuleExecutionProgram.interpretedPremiseProgram caller before code after answer) :
    PureReturns runtime caller before code after answer :=
  transport lower_closed lower_agreement within returned


theorem runtime_equation_count : runtime.equations.length = 579 := by decide +kernel

theorem runtime_declaration_count : runtime.declarations.length = 579 := by decide +kernel

theorem observer_heads_not_lower :
    (occurrenceSource.program.equations.drop 12).all (fun row => !lowerHeads row.head) = true := by
  decide +kernel

theorem no_initializers : runtime.initializers = [] := by decide +kernel

theorem continuation_not_lower : lowerHeads "gslt:collection-continuation:begin" = false := by decide +kernel
theorem finish_not_lower : lowerHeads "gslt:occurrence-search:finish" = false := by decide +kernel
theorem primitive_finisher_lower : lowerHeads "gslt:rule:job-finish-root" = true := by decide +kernel
theorem root_continuation_lower : lowerHeads "gslt:descent:continue-root-answer" = true := by decide +kernel

#print axioms runtime_equation_count
#print axioms runtime_declaration_count
#print axioms observer_heads_not_lower
#print axioms no_initializers
#print axioms lower_agreement
#print axioms lower_closed
#print axioms transport_lower
#print axioms continuation_not_lower
#print axioms finish_not_lower
#print axioms primitive_finisher_lower
#print axioms root_continuation_lower
end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CollectionOccurrenceSearchExecution.SelectedNativeSource

end SelectedNativeSourceView


section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CollectionOccurrenceSearchExecution.Interpreted
open SpaceSemantics Eval BridgeKit
def metadataLibrary : Library :=
  ⟨{equations := [], declarations := []},
    (((RuleExecutionProgram.callFragment ["gslt:rule:scope-fill"] RuleExecutionProgram.program).append
      RuleExecutionProgram.ruleJobReadoutProgram).append
      (RuleExecutionProgram.callFragment ["gslt:occurrence-search:finish",
        "gslt:occurrence-search:read-log", "gslt:occurrence-search:read-committed"]
        SelectedNativeSource.occurrenceSource.program)).append
      (RuleExecutionProgram.callFragment ["gslt:premise:matching-environment"] RuleExecutionProgram.scopedProgram),
    ["gslt:occurrence-search:finish", "gslt:occurrence-search:read-log", "gslt:occurrence-search:read-committed",
      "gslt:premise:matching-environment", "gslt:rule:scope-fill",
      "gslt:rule:site-replacement-represented", "gslt:rule:job-finish-root",
      "OccurrenceFinishInput", "CompletePlan", "RecursiveOccurrencePublication", "RecursiveCollectionOrigin",
      "RuleJob", "CollectionSiteVariant", "RecursiveCollectionContinued", "PreparedCollectionMatch",
      "ScopedMatcherAnswer", "RootAnswer", "InterpretedPremiseEnvironment", "RecursiveCollectionAnswer",
      "PremiseResult", "RootGoal", "CommittedOccurrence", "LCons", "LNil", "Some", "None"]⟩

def metadataHeads := metadataLibrary.owns

theorem metadata_checked : metadataLibrary.check = true := by decide +kernel


end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CollectionOccurrenceSearchExecution.Interpreted

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CollectionOccurrenceSearchExecution.SelectedNativeSource
open SpaceSemantics Eval BridgeKit
private local instance equationEq : DecidableEq SpaceSemantics.Equation := by
  intro left right
  apply decidable_of_iff (left.head = right.head ∧ left.arguments = right.arguments ∧ left.body = right.body)
  constructor
  · rintro ⟨head, arguments, body⟩
    cases left
    cases right
    cases head
    cases arguments
    cases body
    rfl
  · intro same
    cases same
    exact ⟨rfl, rfl, rfl⟩

theorem metadata_agreement :
    ProgramAgreementOn CollectionOccurrenceSearchExecution.Interpreted.metadataHeads
      CollectionOccurrenceSearchExecution.Interpreted.metadataLibrary.runtime runtime := by
  apply programAgreementOn_of_retained_rows
  · decide +kernel
  · decide +kernel

#print axioms metadata_agreement


end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CollectionOccurrenceSearchExecution.SelectedNativeSource

end


section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CollectionOccurrenceSearchExecution.Declared
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open SpaceSemantics Eval BridgeKit
def keyLibrary : Library :=
  ⟨{equations := [], declarations := []},
    {equations := SelectedNativeSource.occurrenceSource.program.equations.drop (SelectedNativeSource.occurrenceSource.program.equations.length - 12) ++
        [MatchAutomataProgram.program.equations[2]'(by decide +kernel),
         MatchAutomataProgram.program.equations[3]'(by decide +kernel),
         MatchAutomataProgram.program.equations[4]'(by decide +kernel),
         MatchAutomataProgram.program.equations[32]'(by decide +kernel),
         (RuleExecutionProgram.interpretedPremiseSupportSources[4]'(by decide +kernel)).program.equations[17]'(by decide +kernel)],
     declarations := SelectedNativeSource.occurrenceSource.program.declarations.drop (SelectedNativeSource.occurrenceSource.program.declarations.length - 12) ++
        [MatchAutomataProgram.program.declarations[2]'(by decide +kernel),
         MatchAutomataProgram.program.declarations[3]'(by decide +kernel),
         MatchAutomataProgram.program.declarations[4]'(by decide +kernel),
         MatchAutomataProgram.program.declarations[32]'(by decide +kernel),
         (RuleExecutionProgram.interpretedPremiseSupportSources[4]'(by decide +kernel)).program.declarations[17]'(by decide +kernel)]},
    ["gslt:occurrence-search:key-", "gslt:automata:binding", "gslt:automata:member",
      "gslt:automata:unique", "gslt:automata:unique-acc", "gslt:canon:canon"]⟩

private def keyNamedHeads : List String := ["gslt:occurrence-search:key-event", "gslt:occurrence-search:key-history", "gslt:occurrence-search:key-elements", "gslt:occurrence-search:key-binding", "gslt:occurrence-search:key-values", "gslt:occurrence-search:key-extract", "gslt:occurrence-search:key-project", "gslt:occurrence-search:key-unique", "gslt:occurrence-search:key-binary", "gslt:occurrence-search:key-conclusions", "gslt:occurrence-search:key-bag", "gslt:occurrence-search:key-facts", "gslt:automata:member", "gslt:automata:unique", "gslt:automata:unique-acc", "gslt:automata:binding", "gslt:canon:canon"]

def keyHeads (head : String) : Bool := !head.startsWith "gslt:" || keyNamedHeads.contains head

theorem key_checked : keyLibrary.check = true := by decide +kernel

theorem key_body_count : keyLibrary.source.equations.length = 17 := by decide +kernel



private theorem key_view_equations_named :
    keyLibrary.runtime.equations.all (fun row => !keyHeads row.head || keyNamedHeads.contains row.head) = true := by
  decide +kernel

private theorem key_selected_equations_named :
    SelectedNativeSource.runtime.equations.all (fun row => !keyHeads row.head || keyNamedHeads.contains row.head) = true := by
  decide +kernel

private def keyNamedDeclaration (row : Atom) : Bool :=
  match row with
  | .expression [.symbol ":", .symbol head, .expression (.symbol "->" :: _)] =>
      !keyHeads head || keyNamedHeads.contains head
  | _ => true

private theorem key_view_declarations_named : keyLibrary.runtime.declarations.all keyNamedDeclaration = true := by
  decide +kernel

private theorem key_selected_declarations_named : SelectedNativeSource.runtime.declarations.all keyNamedDeclaration = true := by
  decide +kernel

private theorem key_equations_absent (program : Program)
    (checked : program.equations.all (fun row => !keyHeads row.head || keyNamedHeads.contains row.head) = true)
    (head : String) (supported : keyHeads head = true) (absent : head ∉ keyNamedHeads) :
    program.equations.filter (fun row => row.head == head) = [] := by
  apply List.filter_eq_nil_iff.mpr
  intro row member selected
  have same : row.head = head := by simpa using selected
  have known := List.all_eq_true.mp checked row member
  rw [same, supported, Bool.not_true, Bool.false_or] at known
  exact absent (List.contains_iff_mem.mp known)

private theorem key_declarations_absent (program : Program)
    (checked : program.declarations.all keyNamedDeclaration = true)
    (head : String) (supported : keyHeads head = true) (absent : head ∉ keyNamedHeads) :
    program.declarations.filter (retainedCallDeclaration (fun name => name == head)) = [] := by
  apply List.filter_eq_nil_iff.mpr
  intro row member selected
  have known := List.all_eq_true.mp checked row member
  have same : keyNamedDeclaration row = (!keyHeads head || keyNamedHeads.contains head) := by
    unfold retainedCallDeclaration at selected
    split at selected <;> simp_all [keyNamedDeclaration]
  rw [same, supported, Bool.not_true, Bool.false_or] at known
  exact absent (List.contains_iff_mem.mp known)


private local instance keyEquationEq : DecidableEq SpaceSemantics.Equation := by
  intro left right
  apply decidable_of_iff (left.head = right.head ∧ left.arguments = right.arguments ∧ left.body = right.body)
  constructor
  · rintro ⟨head, arguments, body⟩
    cases left
    cases right
    cases head
    cases arguments
    cases body
    rfl
  · intro same
    cases same
    exact ⟨rfl, rfl, rfl⟩

private theorem key_named_0 : ProgramAgreementOn (fun name => name == "gslt:occurrence-search:key-event")
    keyLibrary.runtime SelectedNativeSource.runtime := by
  apply programAgreementOn_of_retained_rows
  · decide +kernel
  · decide +kernel

private theorem key_named_1 : ProgramAgreementOn (fun name => name == "gslt:occurrence-search:key-history")
    keyLibrary.runtime SelectedNativeSource.runtime := by
  apply programAgreementOn_of_retained_rows
  · decide +kernel
  · decide +kernel

private theorem key_named_2 : ProgramAgreementOn (fun name => name == "gslt:occurrence-search:key-elements")
    keyLibrary.runtime SelectedNativeSource.runtime := by
  apply programAgreementOn_of_retained_rows
  · decide +kernel
  · decide +kernel

private theorem key_named_3 : ProgramAgreementOn (fun name => name == "gslt:occurrence-search:key-binding")
    keyLibrary.runtime SelectedNativeSource.runtime := by
  apply programAgreementOn_of_retained_rows
  · decide +kernel
  · decide +kernel

private theorem key_named_4 : ProgramAgreementOn (fun name => name == "gslt:occurrence-search:key-values")
    keyLibrary.runtime SelectedNativeSource.runtime := by
  apply programAgreementOn_of_retained_rows
  · decide +kernel
  · decide +kernel

private theorem key_named_5 : ProgramAgreementOn (fun name => name == "gslt:occurrence-search:key-extract")
    keyLibrary.runtime SelectedNativeSource.runtime := by
  apply programAgreementOn_of_retained_rows
  · decide +kernel
  · decide +kernel

private theorem key_named_6 : ProgramAgreementOn (fun name => name == "gslt:occurrence-search:key-project")
    keyLibrary.runtime SelectedNativeSource.runtime := by
  apply programAgreementOn_of_retained_rows
  · decide +kernel
  · decide +kernel

private theorem key_named_7 : ProgramAgreementOn (fun name => name == "gslt:occurrence-search:key-unique")
    keyLibrary.runtime SelectedNativeSource.runtime := by
  apply programAgreementOn_of_retained_rows
  · decide +kernel
  · decide +kernel

private theorem key_named_8 : ProgramAgreementOn (fun name => name == "gslt:occurrence-search:key-binary")
    keyLibrary.runtime SelectedNativeSource.runtime := by
  apply programAgreementOn_of_retained_rows
  · decide +kernel
  · decide +kernel

private theorem key_named_9 : ProgramAgreementOn (fun name => name == "gslt:occurrence-search:key-conclusions")
    keyLibrary.runtime SelectedNativeSource.runtime := by
  apply programAgreementOn_of_retained_rows
  · decide +kernel
  · decide +kernel

private theorem key_named_10 : ProgramAgreementOn (fun name => name == "gslt:occurrence-search:key-bag")
    keyLibrary.runtime SelectedNativeSource.runtime := by
  apply programAgreementOn_of_retained_rows
  · decide +kernel
  · decide +kernel

private theorem key_named_11 : ProgramAgreementOn (fun name => name == "gslt:occurrence-search:key-facts")
    keyLibrary.runtime SelectedNativeSource.runtime := by
  apply programAgreementOn_of_retained_rows
  · decide +kernel
  · decide +kernel

private theorem key_named_12 : ProgramAgreementOn (fun name => name == "gslt:automata:member")
    keyLibrary.runtime SelectedNativeSource.runtime := by
  apply programAgreementOn_of_retained_rows
  · decide +kernel
  · decide +kernel

private theorem key_named_13 : ProgramAgreementOn (fun name => name == "gslt:automata:unique")
    keyLibrary.runtime SelectedNativeSource.runtime := by
  apply programAgreementOn_of_retained_rows
  · decide +kernel
  · decide +kernel

private theorem key_named_14 : ProgramAgreementOn (fun name => name == "gslt:automata:unique-acc")
    keyLibrary.runtime SelectedNativeSource.runtime := by
  apply programAgreementOn_of_retained_rows
  · decide +kernel
  · decide +kernel

private theorem key_named_15 : ProgramAgreementOn (fun name => name == "gslt:automata:binding")
    keyLibrary.runtime SelectedNativeSource.runtime := by
  apply programAgreementOn_of_retained_rows
  · decide +kernel
  · decide +kernel

private theorem key_named_16 : ProgramAgreementOn (fun name => name == "gslt:canon:canon")
    keyLibrary.runtime SelectedNativeSource.runtime := by
  apply programAgreementOn_of_retained_rows
  · decide +kernel
  · decide +kernel

/-- Same-head row order, call demand and constructor templates agree; cross-head ordering is immaterial. -/
theorem key_metadata_agreement : ProgramAgreementOn keyHeads keyLibrary.runtime SelectedNativeSource.runtime := by
  have named (head : String) (supported : keyHeads head = true) :
      ProgramAgreementOn (fun name => name == head) keyLibrary.runtime SelectedNativeSource.runtime := by
    by_cases present : head ∈ keyNamedHeads
    · simp only [keyNamedHeads, List.mem_cons, List.not_mem_nil, or_false] at present
      rcases present with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact key_named_0
      · exact key_named_1
      · exact key_named_2
      · exact key_named_3
      · exact key_named_4
      · exact key_named_5
      · exact key_named_6
      · exact key_named_7
      · exact key_named_8
      · exact key_named_9
      · exact key_named_10
      · exact key_named_11
      · exact key_named_12
      · exact key_named_13
      · exact key_named_14
      · exact key_named_15
      · exact key_named_16
    · apply programAgreementOn_of_retained_rows
      · rw [key_equations_absent keyLibrary.runtime key_view_equations_named head supported present,
          key_equations_absent SelectedNativeSource.runtime key_selected_equations_named head supported present]
      · rw [key_declarations_absent keyLibrary.runtime key_view_declarations_named head supported present,
          key_declarations_absent SelectedNativeSource.runtime key_selected_declarations_named head supported present]
  exact ⟨fun head supported => (named head supported).dispatch head (by simp),
    fun head index supported => (named head supported).demand head index (by simp),
    fun head values supported => (named head supported).bodies head values (by simp)⟩

#print axioms key_checked
#print axioms key_body_count
#print axioms key_metadata_agreement

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CollectionOccurrenceSearchExecution.Declared

end


section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CollectionOccurrenceSearchExecution.SelectedNativeSource.PhysicalAgreement

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open SpaceSemantics (Program Equation)
open Eval

private def matching (head : String) : Bool := head.startsWith "gslt:premise:matching-"

private def supportEquations : List Equation :=
  SelectedNativeSource.sources.flatMap (fun source => source.program.equations)

private def supportDeclarations : List Atom :=
  SelectedNativeSource.sources.flatMap (fun source => source.program.declarations)

private theorem support_equations_fresh :
    supportEquations.all (fun row => !matching row.head) = true := by decide +kernel

private theorem support_declarations_fresh :
    supportDeclarations.all (fun row => !retainedCallDeclaration matching row) = true := by decide +kernel

private theorem filtered_constant {α : Type} (rows : List α) (first second : α → Bool)
    (value : Bool) (same : ∀ row, second row = true → first row = value) :
    (rows.filter first).filter second = if value then rows.filter second else [] := by
  induction rows with
  | nil => cases value <;> rfl
  | cons row rows ih =>
      cases selected : second row with
      | false =>
          cases kept : first row <;> simp [selected, kept, ih]
      | true =>
          have kept := same row selected
          cases value <;> simp [selected, kept, ih]

private theorem declaration_constant (owns : String → Bool) (head : String) (declaration : Atom)
    (selected : retainedCallDeclaration (fun name => name == head) declaration = true) :
    retainedCallDeclaration owns declaration = owns head := by
  unfold retainedCallDeclaration at selected ⊢
  split at selected
  · rename_i name _
    have same : name = head := by simpa using selected
    simp_all
  · simp_all

private theorem fold_equations (sources : List ProgramQuotation.QuotedProgram) (base : Program) :
    (sources.foldl (fun loaded source => loaded.append source.program) base).equations =
      base.equations ++ sources.flatMap (fun source => source.program.equations) := by
  induction sources generalizing base with
  | nil => simp
  | cons source sources ih =>
      simpa only [List.foldl_cons, Program.append, List.flatMap_cons, List.append_assoc] using
        ih (base.append source.program)

private theorem fold_declarations (sources : List ProgramQuotation.QuotedProgram) (base : Program) :
    (sources.foldl (fun loaded source => loaded.append source.program) base).declarations =
      base.declarations ++ sources.flatMap (fun source => source.program.declarations) := by
  induction sources generalizing base with
  | nil => simp
  | cons source sources ih =>
      simpa only [List.foldl_cons, Program.append, List.flatMap_cons, List.append_assoc] using
        ih (base.append source.program)

private theorem support_equations_absent (head : String) (owned : matching head = true) :
    supportEquations.filter (fun row => row.head == head) = [] := by
  apply List.filter_eq_nil_iff.mpr
  intro row member selected
  have same : row.head = head := by simpa using selected
  have fresh := List.all_eq_true.mp support_equations_fresh row member
  simp [same, owned] at fresh

private theorem support_declarations_absent (head : String) (owned : matching head = true) :
    supportDeclarations.filter (retainedCallDeclaration (fun name => name == head)) = [] := by
  apply List.filter_eq_nil_iff.mpr
  intro row member selected
  have same := declaration_constant matching head row selected
  have fresh := List.all_eq_true.mp support_declarations_fresh row member
  simp [same, owned] at fresh

private theorem append_equations (first second : Program) :
    (first.append second).equations = first.equations ++ second.equations := rfl

private theorem append_declarations (first second : Program) :
    (first.append second).declarations = first.declarations ++ second.declarations := rfl

theorem named_equations (head : String) :
    (SelectedNativeSource.sources.foldl
      (fun loaded source => loaded.append source.program) RuleExecutionProgram.scopedProgram).equations.filter
        (fun row => row.head == head) =
      SelectedNativeSource.runtime.equations.filter (fun row => row.head == head) := by
  have yes := filtered_constant RuleExecutionProgram.scopedProgram.equations
    (fun row => matching row.head) (fun row => row.head == head) (matching head)
    (fun row selected => by
      have same : row.head = head := by simpa using selected
      exact congrArg matching same)
  have no := filtered_constant RuleExecutionProgram.scopedProgram.equations
    (fun row => !matching row.head) (fun row => row.head == head) (!matching head)
    (fun row selected => by
      have same : row.head = head := by simpa using selected
      exact congrArg (fun name => !matching name) same)
  simp only [SelectedNativeSource.runtime, append_equations, fold_equations,
    RuleExecutionProgram.callFragmentWhere, List.filter_append]
  change _ ++ supportEquations.filter _ = (_ ++ supportEquations.filter _) ++ _
  rw [show (fun row : Equation => row.head.startsWith "gslt:premise:matching-") =
      (fun row => matching row.head) from rfl]
  rw [show (fun row : Equation => !row.head.startsWith "gslt:premise:matching-") =
      (fun row => !matching row.head) from rfl]
  rw [yes, no]
  cases owned : matching head with
  | false => simp
  | true => simp [support_equations_absent head owned]

theorem named_declarations (head : String) :
    (SelectedNativeSource.sources.foldl
      (fun loaded source => loaded.append source.program) RuleExecutionProgram.scopedProgram).declarations.filter
        (retainedCallDeclaration (fun name => name == head)) =
      SelectedNativeSource.runtime.declarations.filter
        (retainedCallDeclaration (fun name => name == head)) := by
  have yes := filtered_constant RuleExecutionProgram.scopedProgram.declarations
    (retainedCallDeclaration matching) (retainedCallDeclaration (fun name => name == head)) (matching head)
    (fun row selected => declaration_constant matching head row selected)
  have no := filtered_constant RuleExecutionProgram.scopedProgram.declarations
    (retainedCallDeclaration (fun name => !matching name)) (retainedCallDeclaration (fun name => name == head))
    (!matching head) (fun row selected => declaration_constant (fun name => !matching name) head row selected)
  simp only [SelectedNativeSource.runtime, append_declarations, fold_declarations,
    RuleExecutionProgram.callFragmentWhere, List.filter_append]
  change _ ++ supportDeclarations.filter _ = (_ ++ supportDeclarations.filter _) ++ _
  rw [show (fun name => name.startsWith "gslt:premise:matching-") = matching from rfl]
  rw [show (fun name => !name.startsWith "gslt:premise:matching-") = (fun name => !matching name) from rfl]
  rw [yes, no]
  cases owned : matching head with
  | false => simp
  | true => simp [support_declarations_absent head owned]

theorem physical_selected_agreement :
    ProgramAgreementOn (fun _ => true)
      (SelectedNativeSource.sources.foldl
        (fun loaded source => loaded.append source.program) RuleExecutionProgram.scopedProgram)
      SelectedNativeSource.runtime := by
  have named (head : String) : ProgramAgreementOn (fun name => name == head)
      (SelectedNativeSource.sources.foldl
        (fun loaded source => loaded.append source.program) RuleExecutionProgram.scopedProgram)
      SelectedNativeSource.runtime :=
    programAgreementOn_of_retained_rows _ _ _ (named_equations head) (named_declarations head)
  exact ⟨fun head _ => (named head).dispatch head (by simp),
    fun head index _ => (named head).demand head index (by simp),
    fun head values _ => (named head).bodies head values (by simp)⟩

#print axioms named_equations
#print axioms named_declarations
#print axioms physical_selected_agreement

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CollectionOccurrenceSearchExecution.SelectedNativeSource.PhysicalAgreement

end


section
section SelectedNativeLibrary
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CollectionOccurrenceSearchExecution.SelectedNativeSource
open SpaceSemantics Eval BridgeKit

/-- The selected artifacts supply one target runtime. Bounded views supply proof metadata only. -/
def library : Library := ⟨{equations := [], declarations := []}, runtime, ["gslt:"]⟩

theorem checked : library.check = true := by decide +kernel

theorem runtime_same : library.runtime = runtime := rfl

#print axioms checked
#print axioms runtime_same
end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CollectionOccurrenceSearchExecution.SelectedNativeSource
end SelectedNativeLibrary

end
