import Mettapedia.Languages.MeTTa.SpaceTheory.LiteralRealization
import Mettapedia.GSLT.LanguageDef.ModuleSource.Commands
import Mettapedia.GSLT.LanguageDef.DefinitionalKeySize
import Mettapedia.GSLT.LanguageDef.LiveModuleSteps

/-! A single authored .module as the base for ground space insertions.
The worked instance starts with an equation and three rules, not an empty
fallback language. No evaluation of a foreign binary is a proof premise. -/
set_option autoImplicit false
open Mettapedia.GSLT.LanguageDef.ModuleSource.Commands
#module_file "../../../../../../metta/gslt/module/controls/LiveAliasSpace.module"

namespace Mettapedia.Languages.MeTTa.SpaceTheory.LiteralExamples

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef
open LiveModuleEdits LiteralRealization
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.GSLT.Contracts.LiveAliasRepair

private def parsed := (ModuleSource.elaborateAuthored LiveAliasSpace.library LiveAliasSpace.module).toOption
def base : LanguageDef := parsed.get (by decide +kernel)

private def leaf (h : String) : Pattern := .apply h []
private def probe (h : String) : Pattern := .apply "Probe" [leaf h]

private def fact : Atom := .expression [.symbol "sample", .symbol "Cold"]
private def rule : Atom := .expression [.symbol "=", .expression [.symbol "Probe", .symbol "Cold"],
  .symbol "NewHit"]
private def aliasEquation : Atom := .expression [.symbol "=e", .symbol "Warm", .symbol "Chill"]
private def atoms := [fact, rule, rule, aliasEquation]

private def observed (o : Order) (events : List Atom) (query : Pattern) : Option (List Pattern) := do
  let es ← readEvents 0 events
  let table ← run? o base (build base) es
  return (answers (resulting o base es) table query).map (·.right)

theorem authored_base :
    admitted base = true ∧ base.equations.length = 1 ∧ base.rewrites.length = 3 ∧
    observed .back [] (probe "Chill") = some [leaf "BaseHit"] := by decide +kernel

/-- The ordinary syntax has no rule headed by Probe(Chill). The existing
GSLT step modulo the authored equation has BaseHit, but not Other. -/
theorem authored_alias_step (premises : Mettapedia.OSLF.MeTTaIL.ContextualStep.BasePremiseEvaluator) :
    EquationSemantics.StepModuloEquations premises base (probe "Chill") (leaf "BaseHit") ∧
    ¬ EquationSemantics.StepModuloEquations premises base (probe "Chill") (leaf "Other") := by
  have faithful := LiveModuleSteps.updated_successors_iff (D := Atom) premises .back base
    authored_base.1 [] (out := build base) rfl (probe "Chill")
  refine ⟨(faithful (leaf "BaseHit")).1 (by decide +kernel), ?_⟩
  have absent : DefinitionalEquations.expand (DefinitionalEquations.definitions base) (leaf "Other") ∉
      (answers base (build base) (probe "Chill")).map
        (fun r => DefinitionalEquations.expand (DefinitionalEquations.definitions base) r.right) := by
    decide +kernel
  exact fun step => absent ((faithful (leaf "Other")).2 step)

theorem fact_rule_equation :
    observed .back [fact] (probe "Cold") = some [leaf "BaseHit"] ∧
    observed .back [fact, rule, rule] (probe "Cold") =
      some [leaf "BaseHit", leaf "NewHit", leaf "NewHit"] ∧
    observed .back atoms (probe "Cold") =
      some [leaf "OldHit", leaf "BaseHit", leaf "NewHit", leaf "NewHit"] ∧
    observed .front atoms (probe "Cold") =
      some [leaf "NewHit", leaf "NewHit", leaf "OldHit", leaf "BaseHit"] ∧
    observed .front atoms (probe "Solo") = some [leaf "Other"] := by decide +kernel

/-- One of five literal LHS keys needs reconsideration; the new alias is
nested under Probe. A head-only index on the outer symbol would miss it. -/
theorem one_of_five :
    (view? .back base [fact, rule, rule]).map
      (fun l => (l.rewrites.length, (posting l "Warm").map Fin.val)) = some (5, [0]) := by
  decide +kernel

private def cyclic : Atom := .expression [.symbol "=e", .symbol "Cold", .symbol "Warm"]
private def openRule : Atom := .expression [.symbol "=", .expression [.symbol "Probe", .var "x"],
  .symbol "NewHit"]
private def wrongSort : Atom := .expression [.symbol "=", .symbol "Cold", .symbol "NewHit"]

theorem declines_outside_slice :
    observed .back (atoms ++ [cyclic]) (probe "Cold") = none ∧
    observed .front [openRule] (probe "Cold") = none ∧
    observed .back [wrongSort] (probe "Cold") = none ∧
    ConstructorSyntax.term? .literal (.expression [.symbol "Cold"]) = none := by decide +kernel

def oldWarmKey := DefinitionalEquations.expand (DefinitionalEquations.definitions base) (probe "Warm")
def newWarmKey := DefinitionalEquations.expand (DefinitionalEquations.definitions base ++
  [⟨"Warm", [], leaf "Chill"⟩]) (probe "Warm")

/-- The same legal edit has a dense worst case. For N separately materialized
old keys of this shape, no point-write repair can change fewer than N slots. -/
theorem dense_is_unavoidable (n : Nat) (writes : List (Fin n))
    (kept : ∀ i ∉ writes, oldWarmKey = newWarmKey) : n ≤ writes.length := by
  have diff : oldWarmKey ≠ newWarmKey := by decide +kernel
  have all : changed (fun _ : Fin n => oldWarmKey) (fun _ => newWarmKey) = Finset.univ := by
    ext i
    simp [changed, diff]
  simpa only [all, Finset.card_univ, Fintype.card_fin] using
    minimum_writes (fun _ : Fin n => oldWarmKey) (fun _ => newWarmKey) writes kept

private def treeSource := (ModuleSource.elaborateTheoryAuthored LiveAliasSpace.library
  LiveAliasSpace.module ["TreeKeys"]).toOption
def treeLanguage : LanguageDef := treeSource.get (by decide +kernel)

theorem duplicating_theory_is_admitted :
    admitted treeLanguage = true ∧ DefinitionalEquations.definitions treeLanguage =
      [DefinitionalKeySize.duplicate] := by decide +kernel

open DefinitionalKeySize Mettapedia.Machines in
/-- Admission is not a profitability theorem. This well-sorted acyclic
theory doubles tree occurrences at every nested use of its one definition.
A shared construction yields the same normal form with only linearly many
node combinations. -/
theorem admitted_but_expansive (n : Nat) :
    let key := DefinitionalEquations.expand (DefinitionalEquations.definitions treeLanguage) (input n)
    let shared := DemandSummary.demand graph Pattern.apply n (fun _ => none)
    nodes (input n) = n+1 ∧ nodes key + 1 = 2^(n+1) ∧
      shared.value = key ∧ shared.computed.length ≤ n+1 := by
  rw [duplicating_theory_is_admitted.2]
  obtain ⟨same, bound, outputSize⟩ := shared_normal_form n
  exact ⟨input_size n, same ▸ outputSize, same, bound⟩

end Mettapedia.Languages.MeTTa.SpaceTheory.LiteralExamples
