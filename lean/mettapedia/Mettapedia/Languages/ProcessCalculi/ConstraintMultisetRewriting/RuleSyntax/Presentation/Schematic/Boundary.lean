import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Presentation.Schematic.Controls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Presentation.Boundary

/-!
# Where the presentation with unknowns stops

## The class of premises

The rewrites of `presentSchematic` ask only the framework's builtin equality, of two kinds of arguments: the
rest against an **open** bag, `rest = {q, ...qⱼ}` (a read), and codes of matched terms, `l = r` (a tell or a
guard); the relation environment is asked to add nothing to the equality (`noEq`). No premise reads the store
beyond what the rule matches, and none is an oracle (`Presentation.Oracle`).

* For that class the step is closed under parallel composition (`schematic_parClosed`, from
  `Matching.semanticStep_beside`), so it is never the none step (`schematic_not_none`, the corollary of
  `NullsOnTheStep.Composition.parClosed_not_noneReduces`).
* **Open bags are needed** (`closedBag_steps`, `closedBag_refuses`, `closedBag_not_parClosed`): the builtin
  equality alone, comparing the rest with a bag that has no rest variable, `rest = {}`, presents "make `12` where
  the store is empty", and that step is not closed under parallel composition.

## An unknown that survives a firing needs the knowledge in the term

The rule `makeFresh` makes the row `(7 x)` with `x` bound by nothing (`makeFresh_not_restricted`).
* On `RuleSyntax.step` it fires at the empty store (`makeFresh_fires`), and the result of every firing reads as
  **no** bag of rows (`survivor_unread`): two solutions of its knowledge send the fresh unknown to `0` and to `1`.
  The made row is ground only modulo a knowledge that does not bind it.
* The presented language steps from the empty store to a term that holds the metavariable code of `x`
  (`survivor_framework_steps`), which is the store of no rows (`survivorTerm_not_store`): the framework
  instantiates an unbound metavariable as itself, the same metavariable at every firing.

## A tell that binds a caller's unknown needs the knowledge in the term

The rule `tellRule` reads a row `y`, tells `y = 5`, and makes `9`; it is in the fragment (`tellRule_fragment`).
* At a row labelled by the caller's unknown `x`, with no knowledge, it fires (`tellFiring_admitted`); beside the
  knowledge `x = 6`, with the same rows and labels, it does not (`toldSix_refused`).
* So **no presentation whose terms record only the present rows and their labels**, whatever its rewrites and
  premises (oracles included), has the step's firing possibility at both states (`knowledge_needed`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Presentation.Schematic.Boundary

open Mettapedia.Logic.LP
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.MatchSpec
open Mettapedia.OSLF.MeTTaIL.Engine (RelationEnv premiseStepWithEnv matchRelationArgument)
open Mettapedia.OSLF.MeTTaIL.ContextualStep (engineBasePremises PremiseAt PremisesAt StepAt)
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical (matchPatternForRule matchPatternForRule_eq_syntactic)
open Mettapedia.OSLF.Framework.TypeSynthesis (langSemanticReducesUsing langDiamondUsing langGSLTUsing)
open Mettapedia.OSLF.Framework.GSLTTypeSynthesis (EquationPredicate)
open Mettapedia.GSLT.LanguageDef.EquationSemantics (EquationEquiv StepModuloEquations)
open NullsOnTheStep.Composition (ParClosed NoneReduces parClosed_not_noneReduces)
open MeTTaCalculus.OccurrenceCommits (Enabled fire)
open Interface (Frames)
open NamesOnTheStep (Expr)
open Presentation.Schematic.Examples (x sym app)
open Presentation.Schematic.Controls (emptyState)

variable {relEnv : RelationEnv}

/-! ## The class of premises, and the context rule -/

/-- **The presented step of a program with unknowns is closed under parallel composition**, read on composition
terms through their leaves. -/
theorem schematic_parClosed {rules : List SRule} (noEq : ∀ args, relEnv.tuples "eq" args = [])
    (fragment : ∀ r ∈ rules, RangeRestrictedPositive r) : ParClosed (onTerms relEnv (presentSchematic rules)) :=
  fun _ _ u step => semanticStep_beside noEq fragment u.leaves step

/-- **So it is never the none step.** -/
theorem schematic_not_none {rules : List SRule} (noEq : ∀ args, relEnv.tuples "eq" args = [])
    (fragment : ∀ r ∈ rules, RangeRestrictedPositive r) (missing made : Expr) :
    ¬ ∀ t t', onTerms relEnv (presentSchematic rules) t t' ↔ NoneReduces missing made t t' :=
  parClosed_not_noneReduces (schematic_parClosed noEq fragment) missing made

/-- The empty bag. -/
def emptyBag : Pattern := .collection .hashBag [] none

/-- **"The rest is empty"**: a premise of the builtin equality against a bag with no rest variable. -/
def closedBagRewrite : RewriteRule where
  name := "MakeWhereEmpty"
  typeContext := [("rest", .bag (.base "Row"))]
  premises := [.relationQuery "eq" [.fvar "rest", emptyBag]]
  left := .collection .hashBag [] (some "rest")
  right := .collection .hashBag [termCode (sym 12)] (some "rest")

/-- The language of that rewrite. -/
def closedBagLanguage : LanguageDef where
  name := "MakeWhereTheStoreIsEmpty"
  types := ["Nat", "Row", "Store"]
  terms := rowFormers ++ [storeFormer]
  equations := []
  rewrites := [closedBagRewrite]

theorem closedBag_aligned : ruleDepthAligned closedBagRewrite = true :=
  ruleDepthAligned_of_binderFree _ rfl (binderFreeList_termCode [sym 12])

/-- **The closed-bag premise steps at the empty store.** -/
theorem closedBag_steps (noEq : ∀ args, relEnv.tuples "eq" args = []) :
    Mettapedia.OSLF.MeTTaIL.ContextualStep.Step (engineBasePremises relEnv) closedBagLanguage (storeCode [])
      (storeCode [.sym 12]) := by
  let initial : Bindings := [("rest", emptyBag)]
  have found : initial.find? (·.1 == "rest") = some ("rest", emptyBag) := by simp [initial]
  have matched : initial ∈ matchPatternForRule closedBagLanguage closedBagRewrite (storeCode []) := by
    rw [matchPatternForRule_eq_syntactic, matchPattern_iff_matchRel]
    exact .collection (by decide) .nilRest
  have h1 : [] ∈ matchRelationArgument initial (.fvar "rest") emptyBag := by
    rw [matchRelationArgument_fvar_bound _ found, if_pos rfl]
    exact List.mem_singleton_self _
  have h2 : [] ∈ matchRelationArgument initial emptyBag emptyBag := by
    rw [matchRelationArgument_other initial _ (fun _ different => by cases different), matchPattern_iff_matchRel]
    exact .collection (by decide) .nilNoRest
  have premise : initial ∈ premiseStepWithEnv relEnv closedBagLanguage initial
      (.relationQuery "eq" [.fvar "rest", emptyBag]) :=
    (relationQuery_eq_iff noEq _ initial _ _ initial).mpr ⟨emptyBag, Or.inl (applyBindings_fvar_some found).symm,
      [], mem_matchRelationArgs_cons.mpr ⟨[], h1, initial, mergeBindings_nil initial, [],
        mem_matchRelationArgs_one.mpr ⟨h2, initial, mergeBindings_nil initial⟩, mergeBindings_nil []⟩,
      mergeBindings_nil initial⟩
  refine ⟨1, .rule (List.mem_singleton_self _) matched (.cons (premiseAt_engine_iff.mpr premise) (.nil initial)) ?_⟩
  rw [Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.applyBindingsForRule_eq_syntactic,
    applyRuleBindings_eq_applyBindings _ _ closedBag_aligned]
  exact right_instantiated initial (fun _ => .sym 0) [sym 12] [] found fun p inProduce z vars => by
    rw [List.mem_singleton.mp inProduce] at vars
    exact absurd vars not_mem_vars_const

/-- **The closed-bag premise refuses beside a row `11`.** -/
theorem closedBag_refuses (noEq : ∀ args, relEnv.tuples "eq" args = []) (target : Pattern) :
    ¬ Mettapedia.OSLF.MeTTaIL.ContextualStep.Step (engineBasePremises relEnv) closedBagLanguage
      (storeCode [.sym 11]) target := by
  rintro ⟨fuel, stepAt⟩
  cases stepAt with
  | @rule fuel' source' target' rule initial final ruleMember matched premises targetEq =>
    obtain rfl := List.mem_singleton.mp ruleMember
    rw [matchPatternForRule_eq_syntactic, matchPattern_iff_matchRel] at matched
    change MatchRel (.collection .hashBag [] (some "rest")) (.collection .hashBag [rowCode (.sym 11)] none) initial
      at matched
    cases matched with
    | collection _ bagMatch =>
    cases bagMatch
    cases premises with
    | cons first _ =>
    have member := premiseAt_engine_iff.mp first
    obtain ⟨v, -, bPrem, prem, -⟩ := (relationQuery_eq_iff noEq _ _ _ _ _).mp member
    obtain ⟨h1, h1Member, ext, -, t, tMember, -⟩ := mem_matchRelationArgs_cons.mp prem
    obtain ⟨h2Member, -, -⟩ := mem_matchRelationArgs_one.mp tMember
    have found : [("rest", Pattern.collection .hashBag [rowCode (.sym 11)] none)].find? (·.1 == "rest") =
        some ("rest", .collection .hashBag [rowCode (.sym 11)] none) := by simp
    rw [matchRelationArgument_fvar_bound _ found] at h1Member
    split_ifs at h1Member with same
    · subst same
      rw [matchRelationArgument_other ext _ (fun _ different => by cases different), matchPattern_iff_matchRel]
        at h2Member
      cases h2Member with
      | collection _ emptyMatch => cases emptyMatch
    · exact absurd h1Member List.not_mem_nil

theorem closedBag_equations : closedBagLanguage.equations = [] := rfl

theorem closedBag_noAlgebra : closedBagLanguage.hasAlgebraDeclarations = false := rfl

/-- **The builtin equality against a closed bag breaks the context rule**: the step of `closedBagLanguage`, read on
composition terms, is not closed under parallel composition. So the class of premises must keep bags open. -/
theorem closedBag_not_parClosed (noEq : ∀ args, relEnv.tuples "eq" args = []) :
    ¬ ParClosed (onTerms relEnv closedBagLanguage) := by
  intro closed
  have here : onTerms relEnv closedBagLanguage .unit (.atom (.sym 12)) :=
    ⟨storeCode [], storeCode [.sym 12], Relation.EqvGen.refl _, closedBag_steps noEq, Relation.EqvGen.refl _⟩
  obtain ⟨redex, contractum, before, step, -⟩ := closed _ _ (.atom (.sym 11)) here
  obtain ⟨arranged, rfl, perm⟩ := storeCode_of_equationEquiv closedBag_equations closedBag_noAlgebra before
  have single : arranged = [.sym 11] := List.perm_singleton.mp perm.symm
  subst single
  exact closedBag_refuses noEq _ step

/-! ## An unknown that survives a firing -/

/-- **Make `(7 x)`**, with `x` bound by nothing. -/
def makeFresh : SRule := ⟨PUnit.unit, ⟨[], [], [], [], [app (sym 7) x]⟩, []⟩

/-- The program of that rule. -/
def freshProgram : List SRule := [makeFresh]

theorem makeFresh_not_restricted : ¬ RangeRestricted makeFresh := by
  intro restricted
  obtain ⟨t, member, -⟩ := restricted (app (sym 7) x) (by simp [written, makeFresh]) 0
    (mem_vars_tail (mem_vars_var.mpr rfl))
  simp [makeFresh] at member

theorem emptyState_ground : GroundLabels emptyState (fun _ => .sym 0) := fun _ inside =>
  absurd inside (Finset.notMem_empty _)

/-- Make identity `0`, opening `x` beyond the knowledge. -/
def freshFiring : Firing ℕ E {r | r ∈ freshProgram} emptyState.frame :=
  ⟨makeFresh, List.mem_singleton_self _, PUnit.unit, shift (knowledgeBound emptyState.knowledge), ⟨[], [], [0]⟩,
    []⟩

/-- **The rule fires at the empty store** on `RuleSyntax.step`. -/
theorem makeFresh_fires : (schematicStep ℕ freshProgram).Admits (s := emptyState) freshFiring := by
  refine (admits_iff freshFiring).mpr ⟨shift_fresh emptyState_ground freshFiring rfl,
    ⟨List.nodup_nil, List.nodup_singleton 0, rfl, rfl, rfl, rfl⟩, ?_, ?_, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp [freshFiring, emptyState, Selection.commit]
  · refine (Frames.ofSubstitution_solvable_iff A _).mpr ⟨Subst.id rowSig, fun e inside => ?_⟩
    simp [Firing.information, Firing.matching, Firing.opened, RuleInstance.map, freshFiring, makeFresh, emptyState,
      Frames.applyStore] at inside
  · intro c inside
    simp [freshFiring, makeFresh, Firing.opened, RuleInstance.map] at inside
  · intro q inside
    simp [freshFiring, makeFresh, Firing.collectOpened] at inside

/-- **The result of every firing of `makeFresh` at the empty store reads as no bag of rows**: two solutions of its
knowledge send the fresh unknown to `0` and to `1`. -/
theorem survivor_unread (g : Firing ℕ E {r | r ∈ freshProgram} emptyState.frame)
    (admitted : (schematicStep ℕ freshProgram).Admits (s := emptyState) g) :
    ¬ ∃ bag, ReadsAs ((schematicStep ℕ freshProgram).result g admitted) bag := by
  rintro ⟨bag, reads⟩
  obtain ⟨fresh, ⟨_, _, takeLength, readLength, produceLength, _⟩, -, -⟩ := (admits_iff g).mp admitted
  have isRule : g.rule = makeFresh := List.mem_singleton.mp g.member
  have reading : ∀ k : ℕ, ∃ u : Subst rowSig,
      A.Models u ((schematicStep ℕ freshProgram).result g admitted).knowledge ∧
      ((schematicStep ℕ freshProgram).result g admitted).present.val.map
          (fun o => u.applyTerm (((schematicStep ℕ freshProgram).result g admitted).label o)) =
        {toTerm (.app (.sym 7) (.sym k))} := by
    intro k
    let h : Subst rowSig := fun _ => sym k
    obtain ⟨u, -, ruleTerms⟩ := fresh PUnit.unit (Subst.id rowSig) h
    obtain ⟨rule, member, ext, opening, ⟨taken, read, made⟩, seen⟩ := g
    obtain rfl : rule = makeFresh := isRule
    have takenEmpty : taken = [] := List.length_eq_zero_iff.mp takeLength.symm
    have readEmpty : read = [] := List.length_eq_zero_iff.mp readLength.symm
    obtain ⟨m, rfl⟩ : ∃ m, made = [m] := List.length_eq_one_iff.mp produceLength.symm
    subst takenEmpty
    subst readEmpty
    have madeRow : u.applyTerm (opening.applyTerm (app (sym 7) x)) = toTerm (.app (.sym 7) (.sym k)) := by
      have holds : u.applyTerm (opening.applyTerm (app (sym 7) x)) = h.applyTerm (app (sym 7) x) :=
        ruleTerms (app (sym 7) x) (by simp [Rule.terms, makeFresh])
      refine holds.trans ?_
      rw [show app (sym 7) x = Term.app RowFunction.app (args2 (sym 7) x) from rfl, Subst.applyTerm_app]
      refine congrArg (Term.app (σ := rowSig) RowFunction.app) (funext fun i => ?_)
      rcases fin_app i with rfl | rfl <;> rfl
    refine ⟨u, fun e inside => ?_, ?_⟩
    · have empty : ((schematicStep ℕ freshProgram).result ⟨makeFresh, member, ext, opening, ⟨[], [], [m]⟩, seen⟩
          admitted).knowledge = [] := by
        rw [result_eq]
        simp [Firing.result, Firing.information, Firing.matching, Firing.opened, RuleInstance.map, makeFresh,
          emptyState, Frames.applyStore]
      rw [empty] at inside
      exact absurd inside List.not_mem_nil
    · show (fire emptyState.present (Selection.commit ⟨[], [], [m]⟩ (T := Unit))).val.map _ = _
      have present : fire emptyState.present (Selection.commit ⟨[], [], [m]⟩ (T := Unit)) = {m} := by
        simp [fire, emptyState, Selection.commit]
      rw [present, Finset.singleton_val, Multiset.map_singleton]
      congr 1
      show u.applyTerm (relabel _ [m] [opening.applyTerm (app (sym 7) x)] m) = _
      simp only [relabel]
      exact madeRow
  obtain ⟨u0, solved0, read0⟩ := reading 0
  obtain ⟨u1, solved1, read1⟩ := reading 1
  have same : ({toTerm (.app (.sym 7) (.sym 0))} : Multiset Tm) = {toTerm (.app (.sym 7) (.sym 1))} :=
    read0.symm.trans ((reads u0 solved0).trans ((reads u1 solved1).symm.trans read1))
  have rows := toTerm_injective (Multiset.singleton_inj.mp same)
  exact absurd (Expr.sym.inj (Expr.app.inj rows).2) (by decide)

/-- The term the presented language reaches from the empty store: the made row with the metavariable code of
`x`. -/
def survivorTerm : Pattern := .collection .hashBag [.apply "App" [rowCode (.sym 7), .fvar (unknownName 0)]] none

/-- **The presented language steps from the empty store to the term holding the metavariable code of `x`.** -/
theorem survivor_framework_steps :
    Mettapedia.OSLF.MeTTaIL.ContextualStep.Step (engineBasePremises relEnv) (presentSchematic freshProgram)
      (storeCode []) survivorTerm := by
  let initial : Bindings := [("rest", .collection .hashBag [] none)]
  have matched : initial ∈ matchPatternForRule (presentSchematic freshProgram) (schematicRewrite 0 makeFresh)
      (storeCode []) := by
    rw [matchPatternForRule_eq_syntactic, matchPattern_iff_matchRel]
    exact .collection (by decide) .nilRest
  have found : initial.find? (·.1 == "rest") = some ("rest", .collection .hashBag [] none) := by simp [initial]
  have missing : initial.find? (·.1 == unknownName 0) = none := by
    simp [initial, beq_iff_eq, Ne.symm (unknownName_ne_rest 0)]
  refine ⟨1, .rule (List.mem_singleton_self _) matched (.nil initial) ?_⟩
  rw [applyBindingsForRule_schematic, applyBindings_collection, restResolution_bound found]
  show Pattern.collection .hashBag ([applyBindings initial (termCode (app (sym 7) x))] ++ []) none = survivorTerm
  rw [List.append_nil, show app (sym 7) x = Term.app RowFunction.app (args2 (sym 7) x) from rfl, applyBindings_app]
  show Pattern.collection .hashBag [.apply "App" [applyBindings initial (rowCode (.sym 7)),
    applyBindings initial (.fvar (unknownName 0))]] none = survivorTerm
  rw [applyBindings_rowCode, applyBindings_fvar_none missing]
  rfl

/-- **That term is the store of no rows**: no row's code is a metavariable. -/
theorem survivorTerm_not_store : ¬ ∃ rows : List Expr, survivorTerm = storeCode rows := by
  rintro ⟨rows, same⟩
  have elements := (Pattern.collection.inj same).2.1
  cases rows with
  | nil => simp at elements
  | cons e rest =>
      simp only [List.map_cons, List.cons.injEq] at elements
      cases e with
      | app f a =>
          have arguments := (Pattern.apply.inj elements.1).2
          have second := (List.cons.inj (List.cons.inj arguments).2).1
          cases a <;> cases second
      | sym _ => exact absurd (Pattern.apply.inj elements.1).1 (by decide)
      | name _ => exact absurd (Pattern.apply.inj elements.1).1 (by decide)
      | code _ => exact absurd (Pattern.apply.inj elements.1).1 (by decide)

/-! ## A tell that binds a caller's unknown -/

/-- **Read a row `y`, tell `y = 5`, make `9`.** -/
def tellRule : SRule := ⟨PUnit.unit, ⟨[], [x], [(x, sym 5)], [], [sym 9]⟩, []⟩

/-- The program of that rule. -/
def tellProgram : List SRule := [tellRule]

theorem tellRule_fragment : RangeRestrictedPositive tellRule := by
  refine ⟨rfl, rfl, fun t inWritten z vars => ?_⟩
  simp only [written, tellRule, List.map_cons, List.map_nil, List.flatMap_nil, List.nil_append, List.cons_append,
    List.append_nil, List.mem_cons, List.not_mem_nil, or_false] at inWritten
  rcases inWritten with rfl | rfl | rfl
  · rw [mem_vars_var.mp vars]
    exact ⟨x, by simp [tellRule], mem_vars_var.mpr rfl⟩
  · exact absurd vars not_mem_vars_const
  · exact absurd vars not_mem_vars_const

/-- **A row labelled by the caller's unknown `x`**, with no knowledge. -/
def openCaller : SState ℕ := ⟨PUnit.unit, [], {0}, fun _ => x⟩

/-- **The same row**, beside the knowledge `x = 6`. -/
def toldSix : SState ℕ := ⟨PUnit.unit, [(x, sym 6)], {0}, fun _ => x⟩

/-- The opening that renames the rule's `y` to `x₁`. -/
def shiftOne : Subst rowSig := fun v => .var (v + 1)

/-- Read the row `0`, make identity `1`. -/
def tellFiring : Firing ℕ E {r | r ∈ tellProgram} openCaller.frame :=
  ⟨tellRule, List.mem_singleton_self _, PUnit.unit, shiftOne, ⟨[], [0], [1]⟩, []⟩

theorem tellFiring_information : tellFiring.information X openCaller = [(.var 1, x), (.var 1, sym 5)] := rfl

theorem tellFiring_fresh : tellFiring.Fresh X openCaller := by
  intro b (g' : Subst rowSig) (h : Subst rowSig)
  let u : Subst rowSig := fun v => if v = 1 then h 0 else g' v
  refine ⟨u, ?_, ?_⟩
  · rintro t (inside | inside | ⟨o, -, rfl⟩)
    · simp [openCaller] at inside
    · simp [openCaller] at inside
    · rfl
  · intro t member
    simp only [tellFiring, tellRule, Rule.terms, List.map_cons, List.map_nil, List.flatMap_nil,
      List.nil_append, List.append_nil, List.cons_append, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl <;> rfl

/-- **At the row of the caller's unknown, with no knowledge, the tell fires.** -/
theorem tellFiring_admitted : (schematicStep ℕ tellProgram).Admits (s := openCaller) tellFiring := by
  refine (admits_iff tellFiring).mpr ⟨tellFiring_fresh, ⟨List.nodup_nil, List.nodup_singleton 1, rfl, rfl, rfl,
    rfl⟩, ?_, ?_, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp [tellFiring, openCaller, Selection.commit]
  · refine (Frames.ofSubstitution_solvable_iff A _).mpr ⟨fun _ => sym 5, fun e inside => ?_⟩
    rw [tellFiring_information] at inside
    simp only [List.mem_cons, List.not_mem_nil, or_false] at inside
    rcases inside with rfl | rfl <;> rfl
  · intro c inside
    simp [tellFiring, tellRule, Firing.opened, RuleInstance.map] at inside
  · intro q inside
    simp [tellFiring, tellRule, Firing.collectOpened] at inside

/-- **Beside the knowledge `x = 6`, with the same rows and labels, no firing of the tell is admitted**: its
information would equate `5` and `6`. -/
theorem toldSix_refused :
    ¬ ∃ g : Firing ℕ E {r | r ∈ tellProgram} toldSix.frame, (schematicStep ℕ tellProgram).Admits (s := toldSix) g := by
  rintro ⟨g, admitted⟩
  obtain ⟨-, ⟨_, _, _, readLength, _, _⟩, enabled, solvable, -, -⟩ := (admits_iff g).mp admitted
  obtain ⟨σ, solved⟩ := (Frames.ofSubstitution_solvable_iff A _).mp solvable
  have isRule : g.rule = tellRule := List.mem_singleton.mp g.member
  obtain ⟨rule, member, ext, opening, ⟨taken, read, made⟩, seen⟩ := g
  obtain rfl : rule = tellRule := isRule
  obtain ⟨o, rfl⟩ : ∃ o, read = [o] := List.length_eq_one_iff.mp readLength.symm
  have present : o ∈ toldSix.present := enabled.kept_subset (by simp [Selection.commit])
  have isZero : o = 0 := by simpa [toldSix] using present
  subst isZero
  have known := Firing.knowledge_solved (b := PUnit.unit)
    (⟨tellRule, member, ext, opening, ⟨taken, [0], made⟩, seen⟩ : Firing ℕ E {r | r ∈ tellProgram} toldSix.frame)
    solved (x, sym 6) (List.mem_singleton_self _)
  have six : σ.applyTerm x = sym 6 := by
    have composed : Subst.applyTerm (σ.comp (Subst.id rowSig)) x = Subst.applyTerm (σ.comp (Subst.id rowSig)) (sym 6) :=
      known
    rw [Subst.comp_id_right] at composed
    exact composed
  have read := Firing.read_solved (b := PUnit.unit)
    (⟨tellRule, member, ext, opening, ⟨taken, [0], made⟩, seen⟩ : Firing ℕ E {r | r ∈ tellProgram} toldSix.frame)
    solved (p := opening.applyTerm x) (o := 0) (List.mem_singleton_self _)
  have told := Firing.tell_solved (b := PUnit.unit)
    (⟨tellRule, member, ext, opening, ⟨taken, [0], made⟩, seen⟩ : Firing ℕ E {r | r ∈ tellProgram} toldSix.frame)
    solved (e := (opening.applyTerm x, opening.applyTerm (sym 5))) (List.mem_singleton_self _)
  have readEq : σ.applyTerm (opening.applyTerm x) = σ.applyTerm (Subst.applyTerm (Subst.id rowSig) x) := read
  have toldEq : σ.applyTerm (opening.applyTerm x) = σ.applyTerm (opening.applyTerm (sym 5)) := told
  rw [Subst.applyTerm_id, six] at readEq
  have five : (sym 6 : Tm) = sym 5 := readEq.symm.trans toldEq
  exact absurd (RowConstant.sym.inj (Term.const.inj five)) (by decide)

/-- **A tell that binds a caller's unknown needs the knowledge in the term**: for every store map that reads only
the present rows and their labels, every language definition, relation environment and property, the generated
possibility at the two states cannot be the step's firing possibility at both. -/
theorem knowledge_needed (storeOf : Finset ℕ → (ℕ → Tm) → Pattern) (L : LanguageDef)
    (φ : EquationPredicate (langGSLTUsing relEnv L)) :
    ¬ (((langDiamondUsing relEnv L φ).1 (storeOf openCaller.present openCaller.label) ↔
          ∃ g : Firing ℕ E {r | r ∈ tellProgram} openCaller.frame,
            (schematicStep ℕ tellProgram).Admits (s := openCaller) g) ∧
        ((langDiamondUsing relEnv L φ).1 (storeOf toldSix.present toldSix.label) ↔
          ∃ g : Firing ℕ E {r | r ∈ tellProgram} toldSix.frame,
            (schematicStep ℕ tellProgram).Admits (s := toldSix) g)) := by
  rintro ⟨atOpen, atTold⟩
  exact toldSix_refused (atTold.mp (atOpen.mpr ⟨tellFiring, tellFiring_admitted⟩))

#print axioms schematic_parClosed
#print axioms schematic_not_none
#print axioms closedBag_steps
#print axioms closedBag_refuses
#print axioms closedBag_not_parClosed
#print axioms makeFresh_not_restricted
#print axioms makeFresh_fires
#print axioms survivor_unread
#print axioms survivor_framework_steps
#print axioms survivorTerm_not_store
#print axioms tellRule_fragment
#print axioms tellFiring_admitted
#print axioms toldSix_refused
#print axioms knowledge_needed

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Presentation.Schematic.Boundary
