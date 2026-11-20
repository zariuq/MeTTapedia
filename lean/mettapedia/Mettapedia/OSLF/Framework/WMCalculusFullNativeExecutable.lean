import Mettapedia.OSLF.Framework.WMCalculusNativeExecutable

/-!
# Typed executable presentation of the full WM calculus

The full authored rule inventory has constructors beyond the core grammar.
This presentation supplies their declarations and the relation input/output
modes needed by the current native compiler. It retains every original rule,
including every premise and the authored congruences. Relation rows still
require model-specific semantic certification.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Framework.WMCalculusFullNativeExecutable

open Mettapedia.OSLF.MeTTaIL Syntax GeneralExecutionAdmission
open Mettapedia.OSLF.Framework.WMCalculusLanguageDef
open Mettapedia.OSLF.Framework.WMCalculusContextClosure
open Mettapedia.OSLF.NativeTypes.Executable.Explored.Compiled
open Mettapedia.OSLF.NativeTypes.Semantics.ModalFormula
open Mettapedia.Logic.ModalMuCalculus

private def decl (label result : String) (arguments : List String) : GrammarRule where
  label := label
  category := result
  params := arguments.zipIdx.map fun (sort, index) => .simple s!"arg{index}" (.base sort)
  syntaxPattern := []

def extensionTerms : List GrammarRule := [
  decl "SourceCompatible" "Proposition" ["State", "State"],
  decl "PartialRevision" "State" ["State", "State"],
  decl "FallbackRevision" "State" ["State", "State"],
  decl "TrustedGate" "State" ["Policy", "State"],
  decl "TrustedAll" "Policy" [],
  decl "EvidenceOne" "BinaryEvidence" [],
  decl "EvidenceOneNegative" "BinaryEvidence" [],
  decl "ImmediateStep" "QuerySet" ["RuleSet", "State", "QuerySet", "QuerySet"],
  decl "LeastClosure" "QuerySet" ["RuleSet", "State", "QuerySet"],
  decl "ImmediateIter" "QuerySet" ["RuleSet", "State", "QuerySet", "Nat"],
  decl "Succ" "Nat" ["Nat"],
  decl "Card" "Nat" ["QuerySpace"],
  decl "PolicyRevisedState" "State" ["Policy", "State", "State"],
  decl "SwapAnomaly" "Cost" ["State", "State", "Query"],
  decl "ScheduleError" "Cost" ["State", "Schedule", "Schedule", "Query"],
  decl "CostZero" "Cost" [],
  decl "ExperimentEvidence" "BinaryEvidence" ["State", "Query"],
  decl "BlackwellPullback" "Query" ["Channel", "Channel", "Query"],
  decl "ChannelComp" "Channel" ["Channel", "Channel"],
  decl "ChannelId" "Channel" [],
  decl "StochEvidence" "BinaryEvidence" ["State", "Query"],
  decl "ExpectedUtility" "Cost" ["Prior", "Channel", "Policy", "Utility"],
  decl "LiftPolicy" "Policy" ["Channel", "Policy"],
  decl "StochId" "Channel" [],
  decl "KripkeEvidence" "BinaryEvidence" ["State", "ModalQuery"],
  decl "Singleton" "State" ["PointedKripke"],
  decl "GenericEvidence" "BinaryEvidence" ["State", "Query"]]

def language : LanguageDef :=
  {wmFullVertexLanguageDefWithCong wmFullVertexMaximal with
    types := ((wmFullTypes wmFullVertexMaximal) ++ ["Proposition", "QuerySpace", "Cost"]).eraseDups
    terms := (wmFullVertexLanguageDef wmFullVertexMaximal).terms ++ extensionTerms}

private def inputs (relation : String) (arguments : List String) : GeneralPremise.Signature :=
  ⟨relation, arguments.map TypeExpr.base, arguments.map fun _ => .input⟩

def signatures : List GeneralPremise.Signature := [
  inputs "outsideScope" ["Scope", "Query"],
  inputs "supportedInScope" ["Scope", "State"],
  inputs "cleanForScope" ["Scope", "State"],
  inputs "sourceCompatible" ["State", "State"],
  inputs "notSourceCompatible" ["State", "State"],
  inputs "querySpaceOf" ["RuleSet", "QuerySpace"],
  inputs "equalCounts" ["State", "State", "Query"],
  ⟨"erasesInScope", [.base "Scope", .base "State"], [.output, .input]⟩,
  inputs "blackwellQueryFactors" ["Query", "Channel", "Channel"],
  ⟨"blackwellFactors", [.base "Channel", .base "Channel", .base "Channel"],
    [.input, .output, .output]⟩,
  inputs "kripkeSat" ["PointedKripke", "ModalQuery"],
  inputs "kripkeNotSat" ["PointedKripke", "ModalQuery"],
  ⟨"queryEquiv", [.base "Query", .base "Query"], [.input, .output]⟩]

def snapshot (handles : List (String × TypeExpr)) (rows : List GeneralPremise.ProviderRow) : Snapshot :=
  ⟨language, handles, {signatures := signatures, rows := rows}⟩

def compile (handles : List (String × TypeExpr)) (rows : List GeneralPremise.ProviderRow) : Plan :=
  StructuralDescent.Plan.compile (snapshot handles rows) WMCalculusNativeExecutable.permissions

theorem compile_equations (handles : List (String × TypeExpr))
    (rows : List GeneralPremise.ProviderRow) : (compile handles rows).equations = [] := by
  unfold compile StructuralDescent.Plan.compile
  rw [StructuralDescent.Plan.equations_preserved]
  rfl

def ask (handles : List (String × TypeExpr)) (rows : List GeneralPremise.ProviderRow)
    (sort : TypeExpr) (source : Pattern) {n : Nat} (atoms : Fin n → Pattern → Bool)
    (formula : Formula Traversal n) (work budget : Nat) : Except WMCalculusNativeExecutable.Issue Verdict :=
  let plan := compile handles rows
  if plan.complete then
    if Mettapedia.GSLT.LanguageDef.WellSorted.checkHasType
        plan.snapshot.language plan.snapshot.free [] source sort then
      .ok (verdict plan [] sort id source work formula
        (equationFreeAtoms (bound := []) (expected := sort) (compile_equations handles rows) atoms) budget)
    else .error .sourceSort
  else .error (.admission plan.obligations)

private theorem ask_ok {handles : List (String × TypeExpr)} {rows : List GeneralPremise.ProviderRow}
    {sort : TypeExpr} {source : Pattern} {n : Nat} {atoms : Fin n → Pattern → Bool}
    {formula : Formula Traversal n} {work budget : Nat} {result : Verdict}
    (answer : ask handles rows sort source atoms formula work budget = .ok result) :
    verdict (compile handles rows) [] sort id source work formula
      (equationFreeAtoms (bound := []) (expected := sort) (compile_equations handles rows) atoms) budget = result := by
  unfold ask at answer
  dsimp only at answer
  split at answer
  · split at answer
    · exact Except.ok.inj answer
    · cases answer
  · cases answer

theorem ask_proved {handles : List (String × TypeExpr)} {rows : List GeneralPremise.ProviderRow}
    {sort : TypeExpr} {source : Pattern} {n : Nat} {atoms : Fin n → Pattern → Bool}
    {formula : Formula Traversal n} {work budget : Nat}
    (answer : ask handles rows sort source atoms formula work budget = .ok .proved) :
    satisfies (transitionSystem (GSLTTypeSynthesis.gsltSpan (theory (compile handles rows) [] sort)))
      (equationFreeAtoms (bound := []) (expected := sort) (compile_equations handles rows) atoms).meaning
      formula source :=
  verdict_proved (plan := compile handles rows) (bound := []) (expected := sort)
    (by rw [Complete.Predecessors.equationsChecked, compile_equations]; rfl)
    (Abstraction.plain _ _ _) trivial (ask_ok answer)

theorem ask_refuted {handles : List (String × TypeExpr)} {rows : List GeneralPremise.ProviderRow}
    {sort : TypeExpr} {source : Pattern} {n : Nat} {atoms : Fin n → Pattern → Bool}
    {formula : Formula Traversal n} {work budget : Nat}
    (answer : ask handles rows sort source atoms formula work budget = .ok .refuted) :
    ¬ satisfies (transitionSystem (GSLTTypeSynthesis.gsltSpan (theory (compile handles rows) [] sort)))
      (equationFreeAtoms (bound := []) (expected := sort) (compile_equations handles rows) atoms).meaning
      formula source :=
  verdict_refuted (plan := compile handles rows) (bound := []) (expected := sort)
    (by rw [Complete.Predecessors.equationsChecked, compile_equations]; rfl)
    (Abstraction.plain _ _ _) trivial (ask_ok answer)

#guard language.validate.isEmpty
#guard (compile [] []).complete
#guard (compile [] []).rules.length == 51
#guard ((compile [] []).rules.map fun rule => (rule.declarationIndex, rule.authored.name)) ==
  (language.rewrites.zipIdx.map fun (rule, index) => (index, rule.name))

end Mettapedia.OSLF.Framework.WMCalculusFullNativeExecutable
