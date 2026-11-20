import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Presentation.Schematic.Possibility

/-!
# Controls: where each hypothesis of the presentation with unknowns is needed

* **Two reads may read one row** (`reads_share`, `consumeReproduce_refuses`): the rule `twoReads` reads
  `(5 x)` and `(5 y)` and makes `(x y)`. At the store holding the one row `(5 1)` both reads read it, with
  `x = y = 1`: `RuleSyntax.step` admits a firing, and the presentation's read premises step there. The ground
  presentation's encoding of reads (consume the distinct read patterns and make them again) needs two rows for
  the two distinct patterns, and the language of that rewrite has no step there. Deduplicating reads is exact on
  ground rows only; with unknowns the read premises are needed.
* **A guard over an unknown no match binds is not presented** (`freeGuard_steps`, `freeGuard_refused`): the
  rule `freeGuard` guards `x = 5` with `x` bound by nothing (it is not range-restricted:
  `freeGuard_not_restricted`). The presentation's premise `x = 5` binds `x` and steps; the step asks the guard
  at every solution of the information, where `x` may be `6`, and refuses. A premise is existential, a guard
  is an ask; they agree on unknowns the match binds.
* **Matching modulo the knowledge is two-way** (`unknownRow_fires`, `unknownRow_no_step`): at a state whose row
  is the caller's unknown `x`, the rule `takeFive` (take `5`, make `9`) fires: the take equation `5 = x` is
  solved by binding the caller's `x`. The framework's matcher treats the row's code as data: the pattern `5`
  does not match the metavariable code of `x`, and the presented language has no step there. So the
  presentation is exact on ground rows only (`Possibility.generated_possibility` asks `GroundLabels`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Presentation.Schematic.Controls

open Mettapedia.Logic.LP
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.MatchSpec
open Mettapedia.OSLF.MeTTaIL.Engine (RelationEnv premiseStepWithEnv)
open Mettapedia.OSLF.MeTTaIL.ContextualStep (engineBasePremises PremiseAt PremisesAt StepAt)
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical (matchPatternForRule matchPatternForRule_eq_syntactic)
open Mettapedia.OSLF.Framework.TypeSynthesis (langDiamondUsing langGSLTUsing)
open Mettapedia.OSLF.Framework.GSLTTypeSynthesis (EquationPredicate)
open Interface (Frames)
open NamesOnTheStep (Expr)
open Presentation.Schematic.Examples (x sym app single single_ground single_trivial single_store)

/-- The unknown `y`. -/
def y : Tm := .var 1

/-- Every term. -/
def everything (relEnv : RelationEnv) (L : LanguageDef) : EquationPredicate (langGSLTUsing relEnv L) :=
  ⟨fun _ => True, fun _ _ _ => Iff.rfl⟩

/-- **A bag pattern matches at most as many elements as there are.** -/
theorem length_le_of_matchBag : ∀ {ps : List Pattern} {rest : Option String} {kind : CollType} {terms : List Pattern}
    {bs : Bindings}, MatchBagRel ps rest kind terms bs → ps.length ≤ terms.length
  | [], _, _, _, _, _ => Nat.zero_le _
  | _ :: _, _, _, _, _, matched => by
      cases matched with
      | cons index bound _ tail _ =>
          have shorter := length_le_of_matchBag tail
          rw [List.length_eraseIdx_of_lt bound] at shorter
          simp only [List.length_cons]
          omega

/-! ## Two reads may read one row -/

/-- **Read `(5 x)` and `(5 y)`, make `(x y)`.** -/
def twoReads : SRule := ⟨PUnit.unit, ⟨[], [app (sym 5) x, app (sym 5) y], [], [], [app x y]⟩, []⟩

/-- The program of that rule. -/
def readsProgram : List SRule := [twoReads]

theorem twoReads_fragment : ∀ r ∈ readsProgram, RangeRestrictedPositive r := by
  intro r member
  rw [List.mem_singleton.mp member]
  refine ⟨rfl, rfl, fun t inWritten z vars => ?_⟩
  have isMade : t = app x y := by simpa [written, twoReads] using inWritten
  subst isMade
  rcases mem_vars_app_cases vars with inX | inY
  · rw [mem_vars_var.mp inX]
    exact ⟨app (sym 5) x, by simp [twoReads], mem_vars_tail (mem_vars_var.mpr rfl)⟩
  · rw [mem_vars_var.mp inY]
    exact ⟨app (sym 5) y, by simp [twoReads], mem_vars_tail (mem_vars_var.mpr rfl)⟩

/-- The row `(5 1)`. -/
def fiveOne : Expr := .app (.sym 5) (.sym 1)

/-- **Both reads read the one row `(5 1)`**: the presentation's read premises step there, and `RuleSyntax.step`
admits a firing there. -/
theorem reads_share {relEnv : RelationEnv} (noEq : ∀ args, relEnv.tuples "eq" args = []) :
    (langDiamondUsing relEnv (presentSchematic readsProgram) (everything relEnv _)).1 (storeCode [fiveOne]) ∧
      ∃ g : Firing ℕ E {r | r ∈ readsProgram} (single fiveOne).frame,
        (schematicStep ℕ readsProgram).Admits (s := single fiveOne) g := by
  have holds : (langDiamondUsing relEnv (presentSchematic readsProgram) (everything relEnv _)).1
      (storeCode [fiveOne]) :=
    (diamond_storeCode_iff noEq twoReads_fragment _ _).mpr ⟨twoReads, List.mem_singleton_self _, fun _ => .sym 1,
      [fiveOne], ⟨List.Perm.refl _, fun q member => by
        simp only [twoReads, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl <;> exact List.mem_singleton_self _,
        fun _ member => absurd member List.not_mem_nil⟩, trivial⟩
  refine ⟨holds, ?_⟩
  have atState := holds
  rw [← single_store fiveOne] at atState
  obtain ⟨g, admitted, -⟩ := (generated_possibility noEq twoReads_fragment (single_ground fiveOne)
    (single_trivial fiveOne) _).mp atState
  exact ⟨g, admitted⟩

/-- **The ground presentation's encoding of the reads, with unknowns**: consume the two distinct read patterns
beside the rest and make them again with the made row. -/
def consumeReproduceRewrite : RewriteRule where
  name := "Fire0"
  typeContext := [("rest", .bag (.base "Row"))]
  premises := []
  left := .collection .hashBag [termCode (app (sym 5) x), termCode (app (sym 5) y)] (some "rest")
  right := .collection .hashBag [termCode (app x y), termCode (app (sym 5) x), termCode (app (sym 5) y)]
    (some "rest")

/-- The language of that rewrite. -/
def consumeReproduce : LanguageDef where
  name := "ReadsConsumedAndRemade"
  types := ["Nat", "Row", "Store"]
  terms := rowFormers ++ [storeFormer]
  equations := []
  rewrites := [consumeReproduceRewrite]

/-- **The encoding by consuming and remaking reads has no step at the one row `(5 1)`**: its left side needs two
rows. -/
theorem consumeReproduce_refuses (relEnv : RelationEnv) (target : Pattern) :
    ¬ Mettapedia.OSLF.MeTTaIL.ContextualStep.Step (engineBasePremises relEnv) consumeReproduce
      (storeCode [fiveOne]) target := by
  rintro ⟨fuel, stepAt⟩
  cases stepAt with
  | @rule fuel' source' target' rule initial final ruleMember matched premises targetEq =>
    obtain rfl := List.mem_singleton.mp ruleMember
    rw [matchPatternForRule_eq_syntactic, matchPattern_iff_matchRel] at matched
    change MatchRel (.collection .hashBag [termCode (app (sym 5) x), termCode (app (sym 5) y)] (some "rest"))
      (.collection .hashBag [rowCode fiveOne] none) initial at matched
    cases matched with
    | collection _ bagMatch =>
        have lengths := length_le_of_matchBag bagMatch
        simp at lengths

/-! ## A guard over an unknown no match binds -/

/-- **Guard `x = 5`, make `9`**, with `x` bound by nothing. -/
def freeGuard : SRule := ⟨PUnit.unit, ⟨[], [], [], [.equal x (sym 5)], [sym 9]⟩, []⟩

/-- The program of that rule. -/
def guardProgram : List SRule := [freeGuard]

theorem freeGuard_not_restricted : ¬ RangeRestricted freeGuard := by
  intro restricted
  obtain ⟨t, member, -⟩ := restricted x (by simp [written, freeGuard, checkTerms]) 0 (mem_vars_var.mpr rfl)
  simp [freeGuard] at member

/-- The empty store. -/
def emptyState : SState ℕ := ⟨PUnit.unit, [], ∅, fun _ => toTerm (.sym 0)⟩

/-- **The premise `x = 5` binds `x`, and the presented language steps from the empty store to `{9}`.** -/
theorem freeGuard_steps {relEnv : RelationEnv} (noEq : ∀ args, relEnv.tuples "eq" args = []) :
    Mettapedia.OSLF.MeTTaIL.ContextualStep.Step (engineBasePremises relEnv) (presentSchematic guardProgram)
      (storeCode []) (storeCode [.sym 9]) := by
  have member : schematicRewrite 0 freeGuard ∈ (presentSchematic guardProgram).rewrites := List.mem_singleton_self _
  let initial : Bindings := [("rest", .collection .hashBag [] none)]
  have matched : initial ∈ matchPatternForRule (presentSchematic guardProgram) (schematicRewrite 0 freeGuard)
      (storeCode []) := by
    rw [matchPatternForRule_eq_syntactic, matchPattern_iff_matchRel]
    exact .collection (by decide) .nilRest
  have missing : initial.find? (·.1 == unknownName 0) = none := by
    simp [initial, beq_iff_eq, Ne.symm (unknownName_ne_rest 0)]
  let final : Bindings := (unknownName 0, rowCode (.sym 5)) :: initial
  have h1Member : [(unknownName 0, rowCode (.sym 5))] ∈
      Mettapedia.OSLF.MeTTaIL.Engine.matchRelationArgument initial (termCode x) (rowCode (.sym 5)) := by
    show [(unknownName 0, rowCode (.sym 5))] ∈
      Mettapedia.OSLF.MeTTaIL.Engine.matchRelationArgument initial (.fvar (unknownName 0)) (rowCode (.sym 5))
    rw [matchRelationArgument_fvar_free _ missing]
    exact List.mem_singleton_self _
  have extMerged : mergeBindings initial [(unknownName 0, rowCode (.sym 5))] = some final := by
    rw [mergeBindings_cons_none [] missing]
    rfl
  have h2Member : [] ∈ Mettapedia.OSLF.MeTTaIL.Engine.matchRelationArgument final (termCode (sym 5))
      (rowCode (.sym 5)) := by
    rw [matchRelationArgument_other final _ (fun _ different => by simp [termCode, sym] at different),
      matchPattern_iff_matchRel]
    exact matchRel_self_rowCode (.sym 5)
  have premise : final ∈ premiseStepWithEnv relEnv (presentSchematic guardProgram) initial
      (equationPremise (x, sym 5)) := by
    refine (relationQuery_eq_iff noEq _ initial _ _ final).mpr ⟨rowCode (.sym 5),
      Or.inr (applyBindings_rowCode initial (.sym 5)).symm, [(unknownName 0, rowCode (.sym 5))], ?_, extMerged⟩
    exact mem_matchRelationArgs_cons.mpr ⟨_, h1Member, final, extMerged, [],
      mem_matchRelationArgs_one.mpr ⟨h2Member, final, mergeBindings_nil final⟩, mergeBindings_nil _⟩
  have premises : PremisesAt (engineBasePremises relEnv) (presentSchematic guardProgram) 0 initial
      (schematicRewrite 0 freeGuard).premises final :=
    .cons (premiseAt_engine_iff.mpr premise) (.nil final)
  refine ⟨1, .rule member matched premises ?_⟩
  rw [applyBindingsForRule_schematic]
  have restFound :
      final.find? (·.1 == "rest") = some ("rest", .collection .hashBag (([] : List Expr).map rowCode) none) := by
    simp [final, initial, beq_iff_eq, unknownName_ne_rest 0]
  exact right_instantiated final (fun _ => .sym 0) [sym 9] [] restFound fun p inProduce z vars => by
    rw [List.mem_singleton.mp inProduce] at vars
    exact absurd vars not_mem_vars_const

/-- **The step refuses the guard over an unbound unknown**: at the empty store no firing of `freeGuard` is
admitted, since a solution of the (empty) information may send the opened `x` to `6`. -/
theorem freeGuard_refused :
    ¬ ∃ g : Firing ℕ E {r | r ∈ guardProgram} emptyState.frame,
      (schematicStep ℕ guardProgram).Admits (s := emptyState) g := by
  rintro ⟨⟨rule, member, ext, opening, selection, seen⟩, admitted⟩
  obtain rfl : rule = freeGuard := List.mem_singleton.mp member
  obtain ⟨fresh, -, -, -, checks, -⟩ := (admits_iff _).mp admitted
  obtain ⟨u, -, ruleTerms⟩ := fresh PUnit.unit (Subst.id rowSig) (fun _ => sym 6)
  have six : u.applyTerm (opening.applyTerm x) = sym 6 :=
    ruleTerms x (by simp [Rule.terms, freeGuard, checkTerms])
  have solved : X.Models (a := PUnit.unit) (b := PUnit.unit) u
      (Firing.information X emptyState ⟨freeGuard, member, ext, opening, selection, seen⟩) := by
    intro e inside
    simp [Firing.information, Firing.matching, Firing.opened, RuleInstance.map, freeGuard, emptyState,
      Frames.applyStore] at inside
  have holds := checks (Check.map opening.applyTerm (.equal x (sym 5))) (List.mem_singleton_self _) PUnit.unit u
    solved
  have equal : u.applyTerm (opening.applyTerm x) = u.applyTerm (opening.applyTerm (sym 5)) := holds
  rw [six] at equal
  exact absurd (RowConstant.sym.inj (Term.const.inj equal)) (by decide)

/-! ## A row that is an unknown -/

/-- **Take `5`, make `9`.** -/
def takeFive : SRule := ⟨PUnit.unit, ⟨[sym 5], [], [], [], [sym 9]⟩, []⟩

/-- The program of that rule. -/
def fiveProgram : List SRule := [takeFive]

/-- **A row that is the caller's unknown `x`**, which nothing binds. -/
def unknownRow : SState ℕ := ⟨PUnit.unit, [], {0}, fun _ => x⟩

/-- Take the row `0`, make identity `1`. -/
def fiveFiring : Firing ℕ E {r | r ∈ fiveProgram} unknownRow.frame :=
  ⟨takeFive, List.mem_singleton_self _, PUnit.unit, Subst.id rowSig, ⟨[0], [], [1]⟩, []⟩

theorem fiveFiring_information : fiveFiring.information X unknownRow = [(sym 5, x)] := rfl

/-- **The step solves `5 = x` by binding the caller's `x`**: the firing is admitted. -/
theorem unknownRow_fires : (schematicStep ℕ fiveProgram).Admits (s := unknownRow) fiveFiring := by
  refine (admits_iff fiveFiring).mpr ⟨?_, ⟨List.nodup_singleton 0, List.nodup_singleton 1, rfl, rfl, rfl, rfl⟩,
    ?_, ?_, ?_, ?_⟩
  · apply RuleSyntax.Examples.fresh_of_ground A unknownRow fiveFiring
    intro t member σ
    simp only [fiveFiring, takeFive, Rule.terms, List.map_nil, List.flatMap_nil, List.nil_append,
      List.append_nil, List.cons_append, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> rfl
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp [fiveFiring, unknownRow, Selection.commit]
  · refine (Frames.ofSubstitution_solvable_iff A _).mpr ⟨fun _ => sym 5, fun e inside => ?_⟩
    rw [fiveFiring_information, List.mem_singleton] at inside
    subst inside
    rfl
  · intro c inside
    simp [fiveFiring, takeFive, Firing.opened, RuleInstance.map] at inside
  · intro q inside
    simp [fiveFiring, takeFive, Firing.collectOpened] at inside

/-- **The presented language has no step at the store of that row**: the pattern `5` does not match the
metavariable code of `x`. -/
theorem unknownRow_no_step (relEnv : RelationEnv) (target : Pattern) :
    ¬ Mettapedia.OSLF.MeTTaIL.ContextualStep.Step (engineBasePremises relEnv) (presentSchematic fiveProgram)
      (.collection .hashBag [termCode x] none) target := by
  rintro ⟨fuel, stepAt⟩
  cases stepAt with
  | @rule fuel' source' target' rule initial final ruleMember matched premises targetEq =>
    obtain ⟨r, inRules, index, rfl⟩ := of_mem_rewrites ruleMember
    obtain rfl : r = takeFive := List.mem_singleton.mp inRules
    rw [matchPatternForRule_eq_syntactic, matchPattern_iff_matchRel] at matched
    change MatchRel (.collection .hashBag [termCode (sym 5)] (some "rest"))
      (.collection .hashBag [termCode x] none) initial at matched
    cases matched with
    | collection _ bagMatch =>
        cases bagMatch with
        | cons index bound head _ _ =>
            have zero : index = 0 := by simpa using bound
            subst zero
            cases head

#print axioms length_le_of_matchBag
#print axioms twoReads_fragment
#print axioms reads_share
#print axioms consumeReproduce_refuses
#print axioms freeGuard_not_restricted
#print axioms freeGuard_steps
#print axioms freeGuard_refused
#print axioms unknownRow_fires
#print axioms unknownRow_no_step

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Presentation.Schematic.Controls
