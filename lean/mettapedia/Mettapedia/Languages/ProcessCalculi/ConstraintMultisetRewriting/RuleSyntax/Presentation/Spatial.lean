import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Presentation.Possibility
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NullsOnTheStep.NoneNotCompositional
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.Invariance
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.Generated
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.BagCanonicalForms

/-!
# The spatial type the union of stores generates

The framework's generated logic of a language (the tree's module `GeneratedLogic`: the structure
`referenceStructure` of the language and its formulas) has a collection former for each collection kind the language's
constructors use: `split kind A B` holds at a term equal, modulo the equations, to a collection whose elements
divide into a part of type `A` and a part of type `B`. For the presented program the union of stores declares
a bag, so `split .hashBag A B` is generated (`split_generated`): **"A beside B"**.

* `sat_split_iff`, **the split law**: a store has type "A beside B" exactly when its rows divide into a store
  of type `A` and a store of type `B`.
* `sat_possibly_iff`: the generated logic's own possibility at a store, read through the reference relation
  of the presented language (equal to the least contextual relation on this language: `referenceProfile`),
  is a rule whose consumed rows are part of the store; at the stores of configurations it is the firing
  possibility of the step on the positive fragment (`Substitutability.sat_possibly_storeOf_iff`).
* `split_possibly`, **a firing of a part is a firing of the whole**, in the generated types:
  "(possibly A) beside B" implies "possibly (A beside B)", for every presented program.
* On the instance-set step (the step of a program as a set of ground rule instances,
  `ProgramAdequacy.program`; not `RuleSyntax.step`) the same law is `succ_beside`, by
  `NullsOnTheStep.Composition.positive_admission_monotone`: for rules whose checks are equations, a firing of a
  configuration is a firing of the configuration beside another one with trivial knowledge and fresh
  identities. On `RuleSyntax.step` itself the law is `StepBeside.admitted_beside`.
* **Control**: a none-guarded rule breaks the law on the instance-set step (`spawn_fires_alone`,
  `spawn_refused_beside`): `Examples.spawn` fires on the empty store and does not fire beside the row `11`;
  so the presentation of its rule, whose possibility obeys the law, has possibility the step does not have
  (`spawn_presentation_control`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Presentation

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine (RelationEnv)
open Mettapedia.OSLF.MeTTaIL.ContextualStep (engineBasePremises)
open Mettapedia.OSLF.NativeTypes.GeneratedLogic
  (Formula Env referenceStructure IsState IsObject ObjectEquivalent sat_respects_equivalent GeneratedBy)
open Mettapedia.GSLT.LanguageDef.WellSorted (isObjectPattern isObjectPatternList)
open Mettapedia.GSLT.LanguageDef.EquationSemantics (DerivedInstance)
open Mettapedia.OSLF.Framework.TypeSynthesis (langDiamondUsing)
open NamesOnTheStep (Expr)
open NamesOnTheStep.IssuingControls (ground Occ Conf)
open LogicOverTheStep.ProgramAdequacy (program program_succ_iff)
open LogicOverTheStep.StepSpan (Succ)
open MeTTaCalculus.OccurrenceCommits (Enabled fire mem_fire)
open NullsOnTheStep.Composition (unionOf positive_admission_monotone)
open OneFrame (bodies)

universe uO

/-! ## Stores are closed object terms -/

theorem object_numeral : ∀ k : ℕ, isObjectPattern (Pattern.unary "Zero" "Succ" k) = true
  | 0 => rfl
  | k + 1 => by simp [isObjectPattern, isObjectPatternList, object_numeral k]

theorem object_rowCode : ∀ e : Expr, isObjectPattern (rowCode e) = true
  | .sym k => by simp [rowCode, isObjectPattern, isObjectPatternList, object_numeral k]
  | .app f a => by simp [rowCode, isObjectPattern, isObjectPatternList, object_rowCode f, object_rowCode a]
  | .name n => by simp [rowCode, isObjectPattern, isObjectPatternList, object_numeral n]
  | .code e => by simp [rowCode, isObjectPattern, isObjectPatternList, object_rowCode e]

theorem scoped_numeral : ∀ k : ℕ, (Pattern.unary "Zero" "Succ" k).isWellScopedAt 0 = true
  | 0 => rfl
  | k + 1 => by simp [Pattern.isWellScopedAt, Pattern.isWellScopedListAt, scoped_numeral k]

theorem scoped_rowCode : ∀ e : Expr, (rowCode e).isWellScopedAt 0 = true
  | .sym k => by simp [rowCode, Pattern.isWellScopedAt, Pattern.isWellScopedListAt, scoped_numeral k]
  | .app f a => by simp [rowCode, Pattern.isWellScopedAt, Pattern.isWellScopedListAt, scoped_rowCode f,
      scoped_rowCode a]
  | .name n => by simp [rowCode, Pattern.isWellScopedAt, Pattern.isWellScopedListAt, scoped_numeral n]
  | .code e => by simp [rowCode, Pattern.isWellScopedAt, Pattern.isWellScopedListAt, scoped_rowCode e]

theorem objectList_rows : ∀ rows : List Expr, isObjectPatternList (rows.map rowCode) = true
  | [] => rfl
  | e :: rows => by simp only [List.map_cons, isObjectPatternList, object_rowCode e, objectList_rows rows,
      Bool.and_self]

theorem scopedList_rows : ∀ rows : List Expr, Pattern.isWellScopedListAt 0 (rows.map rowCode) = true
  | [] => rfl
  | e :: rows => by simp only [List.map_cons, Pattern.isWellScopedListAt, scoped_rowCode e, scopedList_rows rows,
      Bool.and_self]

/-- **A store is a state**: a closed object term. -/
theorem isState_storeCode (rows : List Expr) : IsState (storeCode rows) :=
  ⟨scopedList_rows rows, by
    show ((none : Option String).isNone && isObjectPatternList (rows.map rowCode)) = true
    rw [objectList_rows rows]
    rfl⟩

/-! ## In every language of rows and stores without authored equations

The equivalence, the split former and the step of the generated logic at stores depend only on the language's
constructors and equations, and on its step from stores. They are stated here for every language that declares
the row formers and the union of stores, with no authored equation and no collection algebra; the presentations
of ground programs (below) and of programs with unknowns (`Schematic.Spatial`) are instances. -/

section InEveryLanguage

variable {L : LanguageDef} {relEnv : RelationEnv}

/-- **A term equal to a store in the generated logic is the store of a permutation of its rows**, in every
language with no authored equation and no collection algebra. -/
theorem storeCode_of_objectEquivalent_in (noEquations : L.equations = []) (noAlgebra : L.hasAlgebraDeclarations = false)
    {rows : List Expr} {q : Pattern} (equivalent : ObjectEquivalent relEnv L .syntax (storeCode rows) q) :
    ∃ others : List Expr, q = storeCode others ∧ rows.Perm others :=
  storeCode_of_same
    (Mettapedia.OSLF.NativeTypes.GeneratedLogic.BagForms.canon_eq_of_equivalent noEquations noAlgebra equivalent)

/-- **A permutation of a store's rows is an equation of the generated logic**, in every language that declares the
row formers and the union of stores. -/
theorem objectEquivalent_of_perm_in (formersIn : rowFormers ⊆ L.terms) (storeIn : storeFormer ∈ L.terms)
    {rows others : List Expr} (perm : rows.Perm others) :
    ObjectEquivalent relEnv L .syntax (storeCode rows) (storeCode others) :=
  Relation.EqvGen.rel _ _ ⟨(isState_storeCode rows).2, (isState_storeCode others).2,
    Mettapedia.OSLF.MeTTaIL.ReferenceStep.EquationStep.inContext .hole
      (Or.inr (DerivedInstance.bagPerm storeIn (collectionTyped formersIn rows) (perm.map rowCode)))⟩

/-- **The generated logic's step from a store**, in every aligned language of this kind whose steps from stores
reach stores: a step of the language from an arrangement of the rows, to a store equal to the target. -/
theorem refStep_storeCode_iff_in (noEquations : L.equations = []) (noAlgebra : L.hasAlgebraDeclarations = false)
    (formersIn : rowFormers ⊆ L.terms) (storeIn : storeFormer ∈ L.terms)
    (profile : Mettapedia.OSLF.MeTTaIL.ReferenceStep.ReferenceProfile L)
    (storesToStores : ∀ {rows : List Expr} {next : Pattern},
      Mettapedia.OSLF.MeTTaIL.ContextualStep.Step (engineBasePremises relEnv) L (storeCode rows) next →
        ∃ others : List Expr, next = storeCode others)
    {rows : List Expr} {target : Pattern} :
    (referenceStructure relEnv L).step (storeCode rows) .any target ↔
      IsState target ∧ ∃ arranged next : List Expr, rows.Perm arranged ∧
        Mettapedia.OSLF.MeTTaIL.ContextualStep.Step (engineBasePremises relEnv) L (storeCode arranged)
          (storeCode next) ∧
        ObjectEquivalent relEnv L .syntax (storeCode next) target := by
  constructor
  · rintro ⟨-, targetState, redex, contractum, witness, placed, -, valid, -, toTarget, -⟩
    have placed : ObjectEquivalent relEnv L .syntax (storeCode rows) redex := placed
    obtain ⟨arranged, rfl, perm⟩ := storeCode_of_objectEquivalent_in noEquations noAlgebra placed
    have step := (Mettapedia.OSLF.MeTTaIL.ReferenceStep.contextualStep_iff_step relEnv L profile).mpr
      ⟨witness, valid⟩
    obtain ⟨next, rfl⟩ := storesToStores step
    exact ⟨targetState, arranged, next, perm, step, toTarget⟩
  · rintro ⟨targetState, arranged, next, perm, step, toTarget⟩
    obtain ⟨witness, valid⟩ := (Mettapedia.OSLF.MeTTaIL.ReferenceStep.contextualStep_iff_step relEnv L
      profile).mp step
    exact ⟨isState_storeCode rows, targetState, storeCode arranged, storeCode next, witness,
      objectEquivalent_of_perm_in formersIn storeIn perm, isState_storeCode _, valid, isState_storeCode _, toTarget,
      rfl⟩

/-- **The union of stores generates the spatial former** in every language whose constructors use a bag. -/
theorem split_generated_in (uses : L.usesCollection .hashBag = true) (A B : Formula 0) :
    GeneratedBy L (.split .hashBag A B) ↔ GeneratedBy L A ∧ GeneratedBy L B := by
  simp only [GeneratedBy, uses, true_and]

/-- **The split law** in every language of this kind: a store has type "A beside B" exactly when its rows divide
into a store of type `A` and a store of type `B`. -/
theorem sat_split_iff_in (noEquations : L.equations = []) (noAlgebra : L.hasAlgebraDeclarations = false)
    (formersIn : rowFormers ⊆ L.terms) (storeIn : storeFormer ∈ L.terms) (A B : Formula 0) (rows : List Expr) :
    (referenceStructure relEnv L).sat Env.closed (.split .hashBag A B) (storeCode rows) ↔
      ∃ left right : List Expr, (left ++ right).Perm rows ∧
        (referenceStructure relEnv L).sat Env.closed A (storeCode left) ∧
        (referenceStructure relEnv L).sat Env.closed B (storeCode right) := by
  change (∃ first second, (IsObject (storeCode rows) ∧ ∃ l r,
      ObjectEquivalent relEnv L .syntax (storeCode rows) (.collection .hashBag (l ++ r) none) ∧
        first = .collection .hashBag l none ∧ second = .collection .hashBag r none) ∧
      (referenceStructure relEnv L).sat Env.closed A first ∧
      (referenceStructure relEnv L).sat Env.closed B second) ↔ _
  constructor
  · rintro ⟨_, _, ⟨-, l, r, equivalent, rfl, rfl⟩, holdsA, holdsB⟩
    obtain ⟨others, same, perm⟩ := storeCode_of_objectEquivalent_in noEquations noAlgebra equivalent
    have codes : l ++ r = others.map rowCode := (Pattern.collection.inj same).2.1
    obtain ⟨left, right, rfl, rfl, rfl⟩ := List.append_eq_map_iff.mp codes
    exact ⟨left, right, perm.symm, holdsA, holdsB⟩
  · rintro ⟨left, right, perm, holdsA, holdsB⟩
    refine ⟨storeCode left, storeCode right, ⟨(isState_storeCode rows).2, left.map rowCode, right.map rowCode, ?_,
      rfl, rfl⟩, holdsA, holdsB⟩
    rw [← List.map_append]
    exact objectEquivalent_of_perm_in formersIn storeIn perm.symm

end InEveryLanguage

/-! ## The generated logic's equivalence and step on stores -/

variable {R : Reading} {rules : List (Rule Rows)} {relEnv : RelationEnv}

/-- **A term equal to a store in the generated logic is the store of a permutation of its rows.** -/
theorem storeCode_of_objectEquivalent {rows : List Expr} {q : Pattern}
    (equivalent : ObjectEquivalent relEnv (presentWith R rules) .syntax (storeCode rows) q) :
    ∃ others : List Expr, q = storeCode others ∧ rows.Perm others :=
  storeCode_of_objectEquivalent_in presentWith_equations presentWith_noAlgebra equivalent

/-- **A permutation of a store's rows is an equation of the generated logic.** -/
theorem objectEquivalent_of_perm {rows others : List Expr} (perm : rows.Perm others) :
    ObjectEquivalent relEnv (presentWith R rules) .syntax (storeCode rows) (storeCode others) :=
  objectEquivalent_of_perm_in presentWith_formers presentWith_store perm

theorem extraNotDeeper_numeral (lhs : Pattern) (d : ℕ) : ∀ k : ℕ,
    Mettapedia.OSLF.MeTTaIL.ReferenceStep.extraNotDeeper lhs [] d (Pattern.unary "Zero" "Succ" k) = true
  | 0 => by simp [Mettapedia.OSLF.MeTTaIL.ReferenceStep.extraNotDeeper,
      Mettapedia.OSLF.MeTTaIL.ReferenceStep.extraNotDeeperList]
  | k + 1 => by simp [Mettapedia.OSLF.MeTTaIL.ReferenceStep.extraNotDeeper,
      Mettapedia.OSLF.MeTTaIL.ReferenceStep.extraNotDeeperList, extraNotDeeper_numeral lhs d k]

theorem extraNotDeeper_rowCode (lhs : Pattern) (d : ℕ) : ∀ e : Expr,
    Mettapedia.OSLF.MeTTaIL.ReferenceStep.extraNotDeeper lhs [] d (rowCode e) = true
  | .sym k => by simp [rowCode, Mettapedia.OSLF.MeTTaIL.ReferenceStep.extraNotDeeper,
      Mettapedia.OSLF.MeTTaIL.ReferenceStep.extraNotDeeperList, extraNotDeeper_numeral lhs d k]
  | .app f a => by simp [rowCode, Mettapedia.OSLF.MeTTaIL.ReferenceStep.extraNotDeeper,
      Mettapedia.OSLF.MeTTaIL.ReferenceStep.extraNotDeeperList, extraNotDeeper_rowCode lhs d f,
      extraNotDeeper_rowCode lhs d a]
  | .name n => by simp [rowCode, Mettapedia.OSLF.MeTTaIL.ReferenceStep.extraNotDeeper,
      Mettapedia.OSLF.MeTTaIL.ReferenceStep.extraNotDeeperList, extraNotDeeper_numeral lhs d n]
  | .code e => by simp [rowCode, Mettapedia.OSLF.MeTTaIL.ReferenceStep.extraNotDeeper,
      Mettapedia.OSLF.MeTTaIL.ReferenceStep.extraNotDeeperList, extraNotDeeper_rowCode lhs d e]

theorem extraNotDeeperList_rows (lhs : Pattern) (d : ℕ) : ∀ rows : List Expr,
    Mettapedia.OSLF.MeTTaIL.ReferenceStep.extraNotDeeperList lhs [] d (rows.map rowCode) = true
  | [] => rfl
  | e :: rows => by simp only [List.map_cons, Mettapedia.OSLF.MeTTaIL.ReferenceStep.extraNotDeeperList,
      extraNotDeeper_rowCode lhs d e, extraNotDeeperList_rows lhs d rows, Bool.and_self]

/-- **The presented language is aligned**: its reference relation and its least contextual relation agree. -/
theorem referenceProfile : Mettapedia.OSLF.MeTTaIL.ReferenceStep.ReferenceProfile (presentWith R rules) := by
  intro rule member
  obtain ⟨r, -, -, index, rfl⟩ := of_mem_rewrites member
  show (([] : List Premise).all _ &&
    Mettapedia.OSLF.MeTTaIL.ReferenceStep.extraNotDeeper (besideRest (R.consumed r)) [] 0
      (besideRest (R.yielded r))) = true
  simp only [List.all_nil, Bool.true_and, besideRest, Mettapedia.OSLF.MeTTaIL.ReferenceStep.extraNotDeeper,
    extraNotDeeperList_rows]
  split <;> rfl

/-- **The generated logic's step from a store**: a rule whose consumed rows are part of the store, to a state
equal to the store with them replaced by its yielded rows. -/
theorem refStep_storeCode_iff {rows : List Expr} {target : Pattern} :
    (referenceStructure relEnv (presentWith R rules)).step (storeCode rows) .any target ↔
      IsState target ∧ ∃ r ∈ rules, guardsHold r = true ∧ ∃ rest : List Expr, (R.consumed r ++ rest).Perm rows ∧
        ObjectEquivalent relEnv (presentWith R rules) .syntax (storeCode (R.yielded r ++ rest)) target := by
  constructor
  · rintro ⟨-, targetState, redex, contractum, witness, placed, -, valid, -, toTarget, -⟩
    have placed : ObjectEquivalent relEnv (presentWith R rules) .syntax (storeCode rows) redex := placed
    obtain ⟨arranged, rfl, perm⟩ := storeCode_of_objectEquivalent placed
    have step := (Mettapedia.OSLF.MeTTaIL.ReferenceStep.contextualStep_iff_step relEnv (presentWith R rules)
      referenceProfile).mpr ⟨witness, valid⟩
    obtain ⟨r, member, holds, rest, split, rfl⟩ := step_storeCode step
    exact ⟨targetState, r, member, holds, rest, split.trans perm.symm, toTarget⟩
  · rintro ⟨targetState, r, member, holds, rest, split, toTarget⟩
    obtain ⟨witness, valid⟩ := (Mettapedia.OSLF.MeTTaIL.ReferenceStep.contextualStep_iff_step relEnv
      (presentWith R rules) referenceProfile).mp (step_prefix member holds rest)
    exact ⟨isState_storeCode rows, targetState, storeCode (R.consumed r ++ rest), storeCode (R.yielded r ++ rest),
      witness, objectEquivalent_of_perm split.symm, isState_storeCode _, valid, isState_storeCode _, toTarget, rfl⟩

/-- **The generated logic's possibility at a store**: some rule whose consumed rows are part of the store leads
to the store of its yielded rows beside the rest, of the type. -/
theorem sat_possibly_iff (A : Formula 0) (rows : List Expr) :
    (referenceStructure relEnv (presentWith R rules)).sat Env.closed (.possibly .any A) (storeCode rows) ↔
      ∃ r ∈ rules, guardsHold r = true ∧ ∃ rest : List Expr, (R.consumed r ++ rest).Perm rows ∧
        (referenceStructure relEnv (presentWith R rules)).sat Env.closed A (storeCode (R.yielded r ++ rest)) := by
  change (∃ next, (referenceStructure relEnv (presentWith R rules)).step (storeCode rows) .any next ∧
    (referenceStructure relEnv (presentWith R rules)).sat Env.closed A next) ↔ _
  constructor
  · rintro ⟨next, step, holds⟩
    obtain ⟨nextState, r, member, guards, rest, split, toNext⟩ := refStep_storeCode_iff.mp step
    exact ⟨r, member, guards, rest, split,
      (sat_respects_equivalent relEnv _ A (isState_storeCode _) nextState toNext).mpr holds⟩
  · rintro ⟨r, member, guards, rest, split, holds⟩
    exact ⟨_, refStep_storeCode_iff.mpr ⟨isState_storeCode _, r, member, guards, rest, split,
      Relation.EqvGen.refl _⟩, holds⟩

/-! ## The split law -/

/-- **The union of stores generates the spatial former**: "A beside B" is a formula of the presented
language whenever `A` and `B` are. -/
theorem split_generated (A B : Formula 0) :
    GeneratedBy (presentWith R rules) (.split .hashBag A B) ↔
      GeneratedBy (presentWith R rules) A ∧ GeneratedBy (presentWith R rules) B :=
  split_generated_in rfl A B

/-- **The split law**: a store has type "A beside B" exactly when its rows divide into a store of type `A` and a
store of type `B`. -/
theorem sat_split_iff (A B : Formula 0) (rows : List Expr) :
    (referenceStructure relEnv (presentWith R rules)).sat Env.closed (.split .hashBag A B) (storeCode rows) ↔
      ∃ left right : List Expr, (left ++ right).Perm rows ∧
        (referenceStructure relEnv (presentWith R rules)).sat Env.closed A (storeCode left) ∧
        (referenceStructure relEnv (presentWith R rules)).sat Env.closed B (storeCode right) :=
  sat_split_iff_in presentWith_equations presentWith_noAlgebra presentWith_formers presentWith_store A B rows

/-- **A firing of a part is a firing of the whole**, in the generated types: "(possibly A) beside B" implies
"possibly (A beside B)" at every store, for every presented program. -/
theorem split_possibly (A B : Formula 0) (rows : List Expr)
    (holds : (referenceStructure relEnv (presentWith R rules)).sat Env.closed
      (.split .hashBag (.possibly .any A) B) (storeCode rows)) :
    (referenceStructure relEnv (presentWith R rules)).sat Env.closed
      (.possibly .any (.split .hashBag A B)) (storeCode rows) := by
  obtain ⟨left, right, perm, possible, holdsB⟩ := (sat_split_iff _ _ rows).mp holds
  obtain ⟨r, member, guards, rest, split, holdsA⟩ := (sat_possibly_iff A left).mp possible
  refine (sat_possibly_iff _ rows).mpr ⟨r, member, guards, rest ++ right, ?_, ?_⟩
  · rw [← List.append_assoc]
    exact (split.append_right right).trans perm
  · refine (sat_split_iff A B _).mpr ⟨R.yielded r ++ rest, right, ?_, holdsA, holdsB⟩
    rw [List.append_assoc]

/-! ## The same law on the instance-set step, and where the none query breaks it -/

section Step

variable {O : Type uO} [DecidableEq O] (label : O → Expr)

theorem fire_union {store D : Finset O} {c : MeTTaCalculus.OccurrenceCommits.Commit O Expr}
    (takenIn : c.taken ⊆ store) (apart : Disjoint store D) : fire (store ∪ D) c = fire store c ∪ D := by
  ext o
  have notTaken : o ∈ D → o ∉ c.taken := fun inD taken => Finset.disjoint_left.mp apart (takenIn taken) inD
  simp only [fire, Finset.mem_union, Finset.mem_sdiff]
  tauto

/-- **A firing of a part is a firing of the whole, on the instance-set step** (`ProgramAdequacy.program`, the
step of a program as a set of ground rule instances, not `RuleSyntax.step`): for rules whose checks are
equations or `any` queries, a successor of a configuration gives a successor of the configuration beside another one with trivial
knowledge and fresh identities, whose bag is the successor's bag beside the other's. The proof is
`NullsOnTheStep.Composition.positive_admission_monotone`. The same law on `RuleSyntax.step` is
`StepBeside.admitted_beside`. -/
theorem succ_beside {R : Set (RuleInstance Expr)}
    (monotone : ∀ i ∈ R, ∀ c ∈ i.checks, (∃ l r, c = Check.equal l r) ∨ ∃ p, c = Check.predicate .any p)
    {C C' D : Configuration Expr O} (step : Succ (program ground label R) C C')
    (apart : Disjoint C.present D.present) (resultApart : Disjoint C'.present D.present)
    (knowledgeD : Trivial D.equations) :
    ∃ C'', Succ (program ground label R) (unionOf C D) C'' ∧ bagOf label C'' = bagOf label C' + bagOf label D := by
  obtain ⟨rule, sel, member, valid, rfl⟩ := (program_succ_iff ground label R C C').mp step
  have admitted : (AnnotatedRuns.firstOrder ground label).toStep.Admits (s := C)
      (⟨rule, [], sel⟩ : AnnotatedRuns.Firing Expr Unit O) :=
    PredicateQueryAdmission.regionValid_nil_iff.mpr valid
  have madeFresh : ∀ o ∈ sel.made, o ∉ D.present := fun o made inD =>
    Finset.disjoint_left.mp resultApart (mem_fire.mpr (Or.inr (List.mem_toFinset.mpr made))) inD
  obtain ⟨σ, solved⟩ := valid.consistent
  have beside := positive_admission_monotone (monotone rule member) rfl admitted madeFresh ⟨σ, solved, knowledgeD⟩
  have validBeside : sel.Valid ground label rule (unionOf C D) := beside.firing
  refine ⟨_, (program_succ_iff ground label R _ _).mpr ⟨rule, sel, member, validBeside, rfl⟩, ?_⟩
  show (fire (C.present ∪ D.present) (sel.commit (T := Expr))).val.map label =
    (fire C.present (sel.commit (T := Expr))).val.map label + D.present.val.map label
  rw [fire_union valid.occurrences.taken_subset apart,
    val_union_of_disjoint (s := fire C.present (sel.commit (T := Expr))) resultApart, Multiset.map_add]

end Step

/-- One copy of the row `11`. -/
def elevenConf : Conf := ⟨[], {(.sym 11, 0)}⟩

/-- **The none query fires alone**: `spawn` (make `12` where `11` is not present) fires on the empty store. -/
theorem spawn_fires_alone :
    ∃ C', Succ (program ground Prod.fst (bodies {r | r ∈ [Examples.spawn]})) Examples.emptyConf C' := by
  refine ⟨_, (program_succ_iff ground Prod.fst _ _ _).mpr ⟨Examples.spawn.body, ⟨[], [], [(.sym 12, 0)]⟩,
    ⟨Examples.spawn, List.mem_cons_self, rfl⟩, ?_, rfl⟩⟩
  exact {
    take_distinct := List.nodup_nil
    output_distinct := List.nodup_singleton _
    take_length := rfl
    read_length := rfl
    outputs := rfl
    occurrences := ⟨by simp [Selection.commit], by simp [Selection.commit], by simp [Selection.commit],
      by simp [Selection.commit, Examples.emptyConf], fun _ member => by simp [Selection.commit] at member⟩
    consistent := ⟨(), fun _ member => by simp [Selection.problem, Selection.equations, Examples.spawn,
      Examples.rule, Examples.emptyConf] at member⟩
    checks := by
      intro check member σ _
      rw [show Examples.spawn.body.checks = [.predicate .none (.sym 11)] from rfl, List.mem_singleton] at member
      subst member
      intro o present
      exact absurd present (Finset.notMem_empty o) }

/-- **The none query is refused beside the row `11`**: no firing of `spawn` from the empty store beside `11`. -/
theorem spawn_refused_beside :
    ¬ ∃ C', Succ (program ground Prod.fst (bodies {r | r ∈ [Examples.spawn]}))
      (unionOf Examples.emptyConf elevenConf) C' := by
  rintro ⟨C', step⟩
  obtain ⟨_, sel, ⟨r, inRules, rfl⟩, valid, -⟩ := (program_succ_iff ground Prod.fst _ _ _).mp step
  obtain rfl : r = Examples.spawn := List.mem_singleton.mp inRules
  obtain ⟨σ, solved⟩ := valid.consistent
  have missing := valid.checks (.predicate .none (.sym 11)) List.mem_cons_self σ solved
  exact missing (.sym 11, 0) (by simp [unionOf, Examples.emptyConf, elevenConf]) rfl

theorem storeOf_union_eleven : storeOf Prod.fst (unionOf Examples.emptyConf elevenConf) = storeCode [.sym 11] := by
  simp [storeOf, unionOf, Examples.emptyConf, elevenConf, Finset.toList_singleton]

/-- **Control: a none-guarded rule is outside the fragment for a reason.** Its rule, presented (the
none check is not a rewrite), steps at the store `{11}`, where the step of the program fires nothing. -/
theorem spawn_presentation_control :
    (langDiamondUsing relEnv (present [Examples.spawn]) (Examples.everything relEnv _)).1
        (storeOf Prod.fst (unionOf Examples.emptyConf elevenConf)) ∧
      ¬ ∃ C', Succ (program ground Prod.fst (bodies {r | r ∈ [Examples.spawn]}))
        (unionOf Examples.emptyConf elevenConf) C' := by
  refine ⟨?_, spawn_refused_beside⟩
  rw [storeOf_union_eleven]
  exact (diamond_storeCode_iff _ _).mpr ⟨Examples.spawn, List.mem_cons_self, by decide, [.sym 11], by decide,
    trivial⟩

#print axioms isState_storeCode
#print axioms storeCode_of_objectEquivalent_in
#print axioms objectEquivalent_of_perm_in
#print axioms refStep_storeCode_iff_in
#print axioms split_generated_in
#print axioms sat_split_iff_in
#print axioms storeCode_of_objectEquivalent
#print axioms objectEquivalent_of_perm
#print axioms referenceProfile
#print axioms refStep_storeCode_iff
#print axioms sat_possibly_iff
#print axioms split_generated
#print axioms sat_split_iff
#print axioms split_possibly
#print axioms succ_beside
#print axioms spawn_fires_alone
#print axioms spawn_refused_beside
#print axioms spawn_presentation_control

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Presentation
