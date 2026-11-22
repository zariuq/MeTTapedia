import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Presentation.Schematic.EqualityControl

/-!
# A made unknown determined by a tell: range restriction is sufficient, not necessary

`RangeRestricted` asks every unknown of a tell, a guard and a made row to occur in a take or read pattern. The
guard and made-row clauses are needed (`Controls.freeGuard_refused`, `Boundary.survivor_unread`). The tell clause
is not needed in this instance: the rule `tellMade` tells `x = 5` and makes `x`, with `x` in no take or read
pattern (`tellMade_not_restricted`). Its made row is not ground after the match, yet it is determined by the
tell: `RuleSyntax.step` fires at the empty store and its result reads as the store `{5}`
(`tellMade_fires`, `tellMade_reads`), and the presented language steps from the empty store to `{5}`
(`tellMade_steps`), its premise `x = 5` binding `x` as the tell determines it.

So a made row is ground modulo the knowledge when every unknown it holds is bound by a match **or determined by a
tell** from bound terms; "exactly when every unknown of a made row occurs in a take or read pattern" is false.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Presentation.Schematic.TellDetermined

open Mettapedia.Logic.LP
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.MatchSpec
open Mettapedia.OSLF.MeTTaIL.Engine (RelationEnv premiseStepWithEnv matchRelationArgument)
open Mettapedia.OSLF.MeTTaIL.ContextualStep (engineBasePremises PremiseAt PremisesAt StepAt)
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical (matchPatternForRule matchPatternForRule_eq_syntactic)
open MeTTaCalculus.OccurrenceCommits (Enabled fire)
open Interface (Frames)
open NamesOnTheStep (Expr)
open Presentation.Schematic.Examples (x sym)
open Presentation.Schematic.Controls (emptyState)
open Presentation.Schematic.Boundary (emptyState_ground)

/-- **Tell `x = 5`, make `x`**, with `x` in no take or read pattern. -/
def tellMade : SRule := ⟨PUnit.unit, ⟨[], [], [(x, sym 5)], [], [x]⟩, []⟩

/-- The program of that rule. -/
def tellMadeProgram : List SRule := [tellMade]

theorem tellMade_not_restricted : ¬ RangeRestricted tellMade := by
  intro restricted
  obtain ⟨t, member, -⟩ := restricted x (by simp [written, tellMade]) 0 (mem_vars_var.mpr rfl)
  simp [tellMade] at member

/-- Make identity `0`, opening `x` beyond the knowledge. -/
def tellMadeFiring : Firing ℕ E {r | r ∈ tellMadeProgram} emptyState.frame :=
  ⟨tellMade, List.mem_singleton_self _, PUnit.unit, shift (knowledgeBound emptyState.knowledge), ⟨[], [], [0]⟩, []⟩

theorem tellMade_information :
    tellMadeFiring.information X emptyState = [(.var 1, sym 5)] := rfl

/-- **The rule fires at the empty store** on `RuleSyntax.step`. -/
theorem tellMade_fires : (schematicStep ℕ tellMadeProgram).Admits (s := emptyState) tellMadeFiring := by
  refine (admits_iff tellMadeFiring).mpr ⟨shift_fresh emptyState_ground tellMadeFiring rfl,
    ⟨List.nodup_nil, List.nodup_singleton 0, rfl, rfl, rfl, rfl⟩, ?_, ?_, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp [tellMadeFiring, emptyState, Selection.commit]
  · refine (Frames.ofSubstitution_solvable_iff A _).mpr ⟨fun _ => sym 5, fun e inside => ?_⟩
    rw [tellMade_information, List.mem_singleton] at inside
    subst inside
    rfl
  · intro c inside
    simp [tellMadeFiring, tellMade, Firing.opened, RuleInstance.map] at inside
  · intro q inside
    simp [tellMadeFiring, tellMade, Firing.collectOpened] at inside

/-- **Its result reads as the store `{5}`**: every solution of its knowledge sends the made unknown to `5`. -/
theorem tellMade_reads :
    ReadsAs ((schematicStep ℕ tellMadeProgram).result tellMadeFiring tellMade_fires) {.sym 5} := by
  intro σ solved
  have known : ((schematicStep ℕ tellMadeProgram).result tellMadeFiring tellMade_fires).knowledge =
      [(.var 1, sym 5)] := by
    rw [result_eq]
    exact tellMade_information
  rw [known] at solved
  have five : σ 1 = sym 5 := solved (.var 1, sym 5) (List.mem_singleton_self _)
  have present : fire emptyState.present (Selection.commit ⟨[], [], [0]⟩ (T := Unit)) = {0} := by
    simp [fire, emptyState, Selection.commit]
  show (fire emptyState.present (Selection.commit ⟨[], [], [0]⟩ (T := Unit))).val.map _ = _
  rw [present, Finset.singleton_val, Multiset.map_singleton, Multiset.map_singleton]
  exact congrArg (fun t : Tm => ({t} : Multiset Tm)) five

/-- **The presented language steps from the empty store to `{5}`**: the premise `x = 5` binds `x`. -/
theorem tellMade_steps {relEnv : RelationEnv} (noEq : ∀ args, relEnv.tuples "eq" args = []) :
    Mettapedia.OSLF.MeTTaIL.ContextualStep.Step (engineBasePremises relEnv) (presentSchematic tellMadeProgram)
      (storeCode []) (storeCode [.sym 5]) := by
  let initial : Bindings := [("rest", .collection .hashBag [] none)]
  have matched : initial ∈ matchPatternForRule (presentSchematic tellMadeProgram) (schematicRewrite 0 tellMade)
      (storeCode []) := by
    rw [matchPatternForRule_eq_syntactic, matchPattern_iff_matchRel]
    exact .collection (by decide) .nilRest
  have absent : initial.find? (·.1 == unknownName 0) = none := by
    simp [initial, beq_iff_eq, Ne.symm (unknownName_ne_rest 0)]
  let final : Bindings := (unknownName 0, rowCode (.sym 5)) :: initial
  have h1Member : [(unknownName 0, rowCode (.sym 5))] ∈ matchRelationArgument initial (termCode x)
      (rowCode (.sym 5)) := by
    show [(unknownName 0, rowCode (.sym 5))] ∈ matchRelationArgument initial (.fvar (unknownName 0))
      (rowCode (.sym 5))
    rw [matchRelationArgument_fvar_free _ absent]
    exact List.mem_singleton_self _
  have extMerged : mergeBindings initial [(unknownName 0, rowCode (.sym 5))] = some final := by
    rw [mergeBindings_cons_none [] absent]
    rfl
  have h2Member : [] ∈ matchRelationArgument final (termCode (sym 5)) (rowCode (.sym 5)) := by
    rw [matchRelationArgument_other final _ (fun _ different => by simp [termCode, sym] at different),
      matchPattern_iff_matchRel]
    exact matchRel_self_rowCode (.sym 5)
  have premise : final ∈ premiseStepWithEnv relEnv (presentSchematic tellMadeProgram) initial
      (equationPremise (x, sym 5)) := by
    refine (relationQuery_eq_iff noEq _ initial _ _ final).mpr ⟨rowCode (.sym 5),
      Or.inr (applyBindings_rowCode initial (.sym 5)).symm, [(unknownName 0, rowCode (.sym 5))], ?_, extMerged⟩
    exact mem_matchRelationArgs_cons.mpr ⟨_, h1Member, final, extMerged, [],
      mem_matchRelationArgs_one.mpr ⟨h2Member, final, mergeBindings_nil final⟩, mergeBindings_nil _⟩
  have premises : PremisesAt (engineBasePremises relEnv) (presentSchematic tellMadeProgram) 0 initial
      (schematicRewrite 0 tellMade).premises final :=
    .cons (premiseAt_engine_iff.mpr premise) (.nil final)
  refine ⟨1, .rule (List.mem_singleton_self _) matched premises ?_⟩
  rw [applyBindingsForRule_schematic]
  have restFound :
      final.find? (·.1 == "rest") = some ("rest", .collection .hashBag (([] : List Expr).map rowCode) none) := by
    simp [final, initial, beq_iff_eq, unknownName_ne_rest 0]
  have xFound : final.find? (·.1 == unknownName 0) = some (unknownName 0, rowCode (.sym 5)) := by
    simp [final]
  exact right_instantiated final (fun _ => .sym 5) [x] [] restFound fun p inProduce z vars => by
    rw [List.mem_singleton.mp inProduce] at vars
    rw [mem_vars_var.mp vars]
    exact xFound

#print axioms tellMade_not_restricted
#print axioms tellMade_fires
#print axioms tellMade_reads
#print axioms tellMade_steps

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Presentation.Schematic.TellDetermined
