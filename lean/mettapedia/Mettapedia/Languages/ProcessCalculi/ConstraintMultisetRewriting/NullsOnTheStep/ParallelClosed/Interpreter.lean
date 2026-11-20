import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NullsOnTheStep.ParallelClosed.Monotone
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Presentation.Boundary

/-!
# A translation of the none-guarded step into a presentation that tests rows

`RuleSyntax.Presentation.wholeStore` is a presentation in the tree's format with one rewrite, which
makes the row `12` where no row of the store is `11`: its premise asks a relation environment
(`noneRelation`) that decides this of the bag, a test of rows. As a calculus with a parallel
composition (`wholeCalculus`, the tree's `presentationCalculus` of that presentation) its composition is
the presentation's juxtaposition `beside`, two terms side by side in a bag `{p, q}`; its success is that
the row `12` is a component, modulo the equations; its static equivalence is the equations.

* `wholeCalculus_succeeds_iff`: from a store of rows, success is reachable exactly when `12` is a row or
  `11` is not.
* `source_succeeds_iff`: reachable success of the none-guarded step is exactly: `T` is present, or the
  knowledge has identical sides and no `U` is present.
* `interpret`: a configuration goes to the store of its rows, each renamed by `rename` (`T` to the
  presentation's made row `12`, `W` to `10`, every other row to itself); when its knowledge has an
  equation with distinct sides, the row `11` is added. It is defined from the rows and a check of the
  knowledge, not from success. The target is the same one-rule program, "make the row where the
  blocker is not present", with its none test as a whole-store premise: `interpret` is a renaming of
  one program into its own presentation together with a check of the knowledge, not an interpreter of
  the step.
* **It preserves and reflects reachable success** (`interpret_succeeds_iff`).
* **It is not homomorphic on parallel composition** (`interpret_not_homomorphic`): two stores side by
  side are a bag of two bags, at which the rewrite fires whatever the inner stores hold
  (`beside_stores_succeed`), while the union of the empty store and the store holding `U` goes to the
  store holding `11`, at which nothing fires.
* **The check of the knowledge is needed** (`rows_only_not_reflecting`): a configuration whose
  knowledge has no solution fires nothing, while the store of its rows may fire.

The presentation is not persistent either: its step is not closed under parallel composition
(`RuleSyntax.Presentation.whole_not_parClosed`, read on composition terms).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NullsOnTheStep.ParallelClosed.Interpreter

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.MatchSpec
open Mettapedia.OSLF.MeTTaIL.ContextualStep (BasePremiseEvaluator engineBasePremises
  step_iff_rootStep_of_noncontextualRules)
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical (matchPatternForRule_eq_syntactic)
open Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution (applyBindingsForRule_eq_syntactic)
open Mettapedia.GSLT.LanguageDef.EquationSemantics (EquationEquiv)
open NamesOnTheStep NamesOnTheStep.IssuingControls
open MeTTaCalculus.OccurrenceCommits (Enabled fire mem_fire)
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NullsOnTheStep.Composition
  (unionOf)
open RuleSyntax.Presentation (wholeStore noneRelation spawnWhole storeCode rowCode rowCode_injective
  besideRest binderFree_besideRest applyBindings_besideRest premises_whole whole_noncontextual
  whole_semanticStep_iff whole_equations whole_noAlgebra storeCode_of_equationEquiv)

/-! ## The presentation as a calculus -/

/-- **The whole-store presentation as a calculus with a parallel composition**: composition is
juxtaposition (`beside`), success "the row `12` is a component modulo the equations". -/
abbrev wholeCalculus : ParallelCalculus :=
  presentationCalculus (engineBasePremises noneRelation) wholeStore .hashBag (rowCode (.sym 12))

/-- Reachable success of a presentation is read up to its equations. -/
theorem presentation_respects {base : BasePremiseEvaluator} {language : LanguageDef} {kind : CollType}
    {ω t t' : Pattern} (same : EquationEquiv base language t t')
    (succeeds : (presentationCalculus base language kind ω).Succeeds t') :
    (presentationCalculus base language kind ω).Succeeds t := by
  obtain ⟨t'', run, shows⟩ := succeeds
  rcases Relation.ReflTransGen.cases_head run with rfl | ⟨middle, first, rest⟩
  · obtain ⟨t''', equivalent, component⟩ := shows
    exact ⟨t, .refl, t''',
      (Mettapedia.GSLT.LanguageDef.EquationSemantics.equationSetoid base language).iseqv.trans same
        equivalent, component⟩
  · exact ⟨t'', Relation.ReflTransGen.head
      (Mettapedia.GSLT.LanguageDef.EquationSemantics.stepModuloEquations_change_source
        ((Mettapedia.GSLT.LanguageDef.EquationSemantics.equationSetoid base language).iseqv.symm same)
        first) rest, shows⟩

theorem rowCode_ne_collection (e : Expr) (kind : CollType) (elements : List Pattern)
    (rest : Option String) : rowCode e ≠ .collection kind elements rest := by
  cases e <;> exact fun same => by cases same

/-- A component of a row's code is the code itself. -/
theorem component_rowCode {c : Pattern} {e : Expr} (component : Component .hashBag c (rowCode e)) :
    c = rowCode e := by
  generalize code : rowCode e = p at component ⊢
  cases component with
  | here => rfl
  | inside _ _ => exact absurd code (rowCode_ne_collection _ _ _ _)

/-- **A row's code is a component of a store exactly when the row is in it.** -/
theorem component_storeCode {rows : List Expr} {e : Expr} :
    Component .hashBag (rowCode e) (storeCode rows) ↔ e ∈ rows := by
  constructor
  · intro component
    generalize store : storeCode rows = p at component
    cases component with
    | here => exact absurd store.symm (rowCode_ne_collection _ _ _ _)
    | inside member inner =>
        simp only [storeCode, Pattern.collection.injEq] at store
        obtain ⟨-, elements, -⟩ := store
        rw [← elements] at member
        obtain ⟨e', inRows, rfl⟩ := List.mem_map.mp member
        rw [rowCode_injective (component_rowCode inner)]
        exact inRows
  · intro member
    exact .inside (List.mem_map_of_mem member) .here

/-- **From a store of rows, success is reachable exactly when `12` is a row or `11` is not.** -/
theorem wholeCalculus_succeeds_iff (rows : List Expr) :
    wholeCalculus.Succeeds (storeCode rows) ↔ Expr.sym 12 ∈ rows ∨ Expr.sym 11 ∉ rows := by
  constructor
  · rintro ⟨t, run, shows⟩
    rcases Relation.ReflTransGen.cases_head run with rfl | ⟨middle, first, -⟩
    · obtain ⟨t', equivalent, component⟩ := shows
      obtain ⟨others, rfl, perm⟩ := storeCode_of_equationEquiv whole_equations whole_noAlgebra equivalent
      exact Or.inl (perm.symm.subset (component_storeCode.mp component))
    · exact Or.inr (whole_semanticStep_iff.mp first).1
  · rintro (made | missing)
    · exact ParallelCalculus.succeeds_of_success _
        ⟨storeCode rows, Relation.EqvGen.refl _, component_storeCode.mpr made⟩
    · exact ⟨storeCode (.sym 12 :: rows),
        .single (whole_semanticStep_iff.mpr ⟨missing, Relation.EqvGen.refl _⟩),
        storeCode (.sym 12 :: rows), Relation.EqvGen.refl _,
        component_storeCode.mpr List.mem_cons_self⟩

/-- **At any bag with no row `11`, the rewrite makes `12`**, whatever else the bag holds. -/
theorem whole_step_bag {elements : List Pattern} (missing : rowCode (.sym 11) ∉ elements) :
    Mettapedia.OSLF.MeTTaIL.ContextualStep.Step (engineBasePremises noneRelation) wholeStore
      (.collection .hashBag elements none) (.collection .hashBag (rowCode (.sym 12) :: elements) none) := by
  rw [step_iff_rootStep_of_noncontextualRules whole_noncontextual]
  refine ⟨spawnWhole, List.mem_singleton_self _, [("rest", .collection .hashBag elements none)], ?_,
    [("rest", .collection .hashBag elements none)], ?_, ?_⟩
  · rw [matchPatternForRule_eq_syntactic, matchPattern_iff_matchRel]
    exact .collection (by decide) .nilRest
  · rw [premises_whole, if_neg missing]
    exact List.mem_singleton_self _
  · rw [applyBindingsForRule_eq_syntactic, applyRuleBindings_eq_applyBindings _ _
      (ruleDepthAligned_of_binderFree _ (binderFree_besideRest _) (binderFree_besideRest _))]
    change applyBindings _ (besideRest [.sym 12]) = _
    rw [applyBindings_besideRest]
    rfl

/-- **Two stores side by side succeed**: a bag of two bags has no row `11`, so the rewrite fires. -/
theorem beside_stores_succeed (rows rows' : List Expr) :
    wholeCalculus.Succeeds (wholeCalculus.par (storeCode rows) (storeCode rows')) := by
  have missing : rowCode (.sym 11) ∉ [storeCode rows, storeCode rows'] := by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
    exact ⟨rowCode_ne_collection _ _ _ _, rowCode_ne_collection _ _ _ _⟩
  exact ⟨_, .single ⟨_, _, Relation.EqvGen.refl _, whole_step_bag missing, Relation.EqvGen.refl _⟩, _,
    Relation.EqvGen.refl _, .inside List.mem_cons_self .here⟩

/-! ## The source's reachable success -/

/-- `spawn`, making `T` with a copy number above every present one. -/
def spawnAbove (C : Conf) : Fir := ⟨Separations.spawn, [], ⟨[], [], [(factT, Monotone.bound C.present)]⟩⟩

/-- **The reachable success of the none-guarded step**: `T` is present, or the knowledge has
identical sides and no `U` is present. -/
theorem source_succeeds_iff (C : Conf) :
    source.Succeeds C ↔ (∃ o ∈ C.present, o.1 = factT) ∨
      ((∀ e ∈ C.equations, e.1 = e.2) ∧ ∀ o ∈ C.present, o.1 ≠ factU) := by
  constructor
  · intro succeeds
    by_cases presentT : ∃ o ∈ C.present, o.1 = factT
    · exact Or.inl presentT
    · have clearT : ∀ o ∈ C.present, o.1 ≠ factT := fun o member isT => presentT ⟨o, member, isT⟩
      by_cases presentU : ∃ o ∈ C.present, o.1 = factU
      · exact absurd succeeds (never_succeeds_of_blocker program_keeps program_guards presentU clearT)
      · refine Or.inr ⟨?_, fun o member isU => presentU ⟨o, member, isU⟩⟩
        obtain ⟨C', run, shows⟩ := succeeds
        rcases Relation.ReflTransGen.cases_head run with rfl | ⟨_, ⟨f, -, admitted, -⟩, -⟩
        · obtain ⟨o, member, isT⟩ := shows
          exact absurd isT (clearT o member)
        · have problem := Monotone.consistent_iff.mp
            (show f.Valid ground Prod.fst C from admitted).firing.consistent
          exact fun e member => problem e (by simp [Selection.problem, member])
  · rintro (now | ⟨knowledge, clearU⟩)
    · exact ParallelCalculus.succeeds_of_success _ now
    · have fresh : ((factT, Monotone.bound C.present) : Occ) ∉ C.present := fun member =>
        absurd (Monotone.lt_bound member) (Nat.lt_irrefl _)
      have enabled : Enabled Prod.fst C.present ((spawnAbove C).selection.commit (T := Expr)) := by
        refine ⟨?_, ?_, ?_, ?_, ?_⟩
        · intro p member
          simp [spawnAbove, Selection.commit] at member
        · intro p member
          simp [spawnAbove, Selection.commit] at member
        · simp [spawnAbove, Selection.commit]
        · simpa [spawnAbove, Selection.commit] using fresh
        · intro query member
          simp [Selection.commit] at member
      have admitted : base.Admits (s := C) (spawnAbove C) := by
        refine (admits_of (D := fun _ _ _ _ => True) (σ := (C, ∅)) (fresh := []) List.nodup_nil
          (List.nodup_singleton _) rfl rfl rfl enabled knowledge rfl ?_ trivial).1
        intro c member
        simp only [Separations.spawn, rule, List.mem_singleton] at member
        subst member
        exact none_holds clearU
      refine ⟨_, .single ⟨spawnAbove C, Or.inl rfl, admitted, rfl⟩, (factT, Monotone.bound C.present),
        ?_, rfl⟩
      change (factT, Monotone.bound C.present) ∈ fire C.present ((spawnAbove C).selection.commit (T := Expr))
      rw [mem_fire]
      exact Or.inr (by simp [spawnAbove, Selection.commit])

/-! ## The translation -/

/-- **The rows of the step read in the presentation**: `T` as the presentation's made row `12`, `W` as
`10`, every other row as itself. -/
def rename (e : Expr) : Expr := if e = factT then .sym 12 else if e = .sym 12 then factT else e

theorem rename_eq_twelve {e : Expr} : rename e = .sym 12 ↔ e = factT := by
  unfold rename
  split_ifs with isT isW
  · exact ⟨fun _ => isT, fun _ => rfl⟩
  · exact ⟨fun same => absurd same (by decide), fun same => absurd (isW.symm.trans same) (by decide)⟩
  · exact ⟨fun same => absurd same isW, fun same => absurd same isT⟩

theorem rename_eq_eleven {e : Expr} : rename e = .sym 11 ↔ e = factU := by
  unfold rename
  split_ifs with isT isW
  · exact ⟨fun same => absurd same (by decide), fun same => absurd (isT.symm.trans same) (by decide)⟩
  · exact ⟨fun same => absurd same (by decide), fun same => absurd (isW.symm.trans same) (by decide)⟩
  · exact ⟨fun same => same, fun same => same⟩

/-- The renamed rows of a configuration, in the order of its occurrences. -/
noncomputable def rowsOf (C : Conf) : List Expr := C.present.toList.map (rename ∘ Prod.fst)

theorem mem_rowsOf {C : Conf} {e : Expr} : e ∈ rowsOf C ↔ ∃ o ∈ C.present, rename o.1 = e := by
  simp [rowsOf]

/-- **The translation**: the store of the renamed rows, with the row `11` added when the knowledge
has an equation with distinct sides. It renames the one none-guarded program into its own
presentation (`wholeStore` is the same rule, "make `12` where no `11`") and checks the knowledge; it
interprets no other program. -/
noncomputable def interpret (C : Conf) : Pattern :=
  if ∀ e ∈ C.equations, e.1 = e.2 then storeCode (rowsOf C) else storeCode (rowsOf C ++ [.sym 11])

theorem interpret_storeCode (C : Conf) : ∃ rows, interpret C = storeCode rows := by
  unfold interpret
  split_ifs
  · exact ⟨_, rfl⟩
  · exact ⟨_, rfl⟩

/-- **The translation preserves and reflects reachable success.** -/
theorem interpret_succeeds_iff (C : Conf) : wholeCalculus.Succeeds (interpret C) ↔ source.Succeeds C := by
  rw [source_succeeds_iff]
  have twelve : Expr.sym 12 ∈ rowsOf C ↔ ∃ o ∈ C.present, o.1 = factT := by
    rw [mem_rowsOf]
    exact exists_congr fun o => and_congr_right fun _ => rename_eq_twelve
  have eleven : Expr.sym 11 ∈ rowsOf C ↔ ∃ o ∈ C.present, o.1 = factU := by
    rw [mem_rowsOf]
    exact exists_congr fun o => and_congr_right fun _ => rename_eq_eleven
  unfold interpret
  split_ifs with knowledge
  · rw [wholeCalculus_succeeds_iff, twelve, eleven]
    constructor
    · rintro (now | missing)
      · exact Or.inl now
      · exact Or.inr ⟨knowledge, fun o member isU => missing ⟨o, member, isU⟩⟩
    · rintro (now | ⟨-, clearU⟩)
      · exact Or.inl now
      · exact Or.inr fun ⟨o, member, isU⟩ => clearU o member isU
  · rw [wholeCalculus_succeeds_iff]
    have blocked : Expr.sym 11 ∈ rowsOf C ++ [.sym 11] := List.mem_append_right _ (List.mem_singleton_self _)
    have made : Expr.sym 12 ∈ rowsOf C ++ [.sym 11] ↔ ∃ o ∈ C.present, o.1 = factT := by
      rw [List.mem_append, List.mem_singleton, twelve]
      exact ⟨fun inside => inside.resolve_right (by decide), Or.inl⟩
    rw [made]
    constructor
    · rintro (now | missing)
      · exact Or.inl now
      · exact absurd blocked missing
    · rintro (now | ⟨solvable, -⟩)
      · exact Or.inl now
      · exact absurd solvable knowledge

/-- **The translation is not homomorphic on parallel composition**: the union of the empty store and the
store holding `U` goes to a store at which success is unreachable, while the two images side by side
succeed. -/
theorem interpret_not_homomorphic :
    ¬ ∀ s s', source.composable s s' →
      wholeCalculus.same (interpret (source.par s s')) (wholeCalculus.par (interpret s) (interpret s')) := by
  intro homomorphic
  have same := homomorphic alone blocker alone_blocker_composable
  obtain ⟨rows, first⟩ := interpret_storeCode alone
  obtain ⟨rows', second⟩ := interpret_storeCode blocker
  have composite : wholeCalculus.Succeeds (wholeCalculus.par (interpret alone) (interpret blocker)) := by
    rw [first, second]
    exact beside_stores_succeed rows rows'
  have union := presentation_respects same composite
  exact beside_blocked ((interpret_succeeds_iff _).mp union)

/-! ## The check of the knowledge is needed -/

/-- No rows, and knowledge equating `T` and `U`, which has no solution. -/
def unsolvable : Conf := ⟨[(factT, factU)], ∅⟩

/-- **Without the check of the knowledge the store of the rows does not reflect success**: at the
configuration with no rows and unsolvable knowledge the store of its rows (the empty store) succeeds,
and the configuration does not. -/
theorem rows_only_not_reflecting :
    wholeCalculus.Succeeds (storeCode (rowsOf unsolvable)) ∧ ¬ source.Succeeds unsolvable := by
  have empty : rowsOf unsolvable = [] := by simp [rowsOf, unsolvable]
  refine ⟨?_, fun succeeds => ?_⟩
  · rw [empty, wholeCalculus_succeeds_iff]
    exact Or.inr List.not_mem_nil
  · rcases (source_succeeds_iff unsolvable).mp succeeds with ⟨o, member, -⟩ | ⟨knowledge, -⟩
    · exact absurd member (Finset.notMem_empty o)
    · exact absurd (knowledge (factT, factU) (List.mem_singleton_self _)) (by decide)

#print axioms presentation_respects
#print axioms component_storeCode
#print axioms wholeCalculus_succeeds_iff
#print axioms whole_step_bag
#print axioms beside_stores_succeed
#print axioms source_succeeds_iff
#print axioms interpret_succeeds_iff
#print axioms interpret_not_homomorphic
#print axioms rows_only_not_reflecting

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NullsOnTheStep.ParallelClosed.Interpreter
