import Mettapedia.GSLT.Compilation.Uniform.QueryRulesOnTheStep

/-!
# The demand transformation of clauses on rows

Clauses on rows define relations: a clause `relation(input, output) :- body` holds at each of its
instances whose goals hold, where a goal is a condition on given relations or a question to a defined
relation. The defined relations are the least model of the clauses (`Derives`, by derivation depth).

The demand transformation of the clauses (the magic-sets transformation of deductive databases:
Bancilhon, Maier, Sagiv and Ullman 1986; Beeri and Ramakrishnan 1991) gives rules that only read rows
and make rows. Its rows are:

* `demand r x`: the outputs of relation `r` at the input `x` are asked for;
* `answer r x y`: relation `r` holds at input `x` and output `y`;
* `supplementary i j v`: an instance of the `i`-th clause has passed its first `j` goals, with the values
  `v` of the unknowns bound so far.

Each clause gives an entry rule (a demand that its input matches starts an instance), one rule per
condition (which checks it), two rules per question (one asks it, one reads its answer), and an exit rule
(an instance that passed every goal answers). Every answer row holds in the least model, and every
supplementary row is an instance whose goals so far hold (`fired_sound`). From a demand, the rules reach
an answer for every output the least model gives (`answers_reachable`).

A run adds one row, `current x`. A seed asks a chosen relation at the current row, and a commit replaces
the current row by an answer of a chosen relation (`runRules`). Every firing keeps the run at its row or
moves it along one chosen relation (`readStep`), and every such move is a run of firings (`forward`). On
moded clauses every rule is range-restricted (`runRules_restricted`), so this holds on the transform
step too (`stepCorrespondence`).
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Compilation.Uniform.DemandTransformation

open Mettapedia.GSLT
open Mettapedia.GSLT.IndexedOperational
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
open NamesOnTheStep (Expr)
open RuleSyntax
open RuleSyntax.Presentation.Schematic
open RuleSyntax.Machines
open RuleSyntax.ComputedConditions (RuleWithCondition Condition Relations RelationStep relationEvaluation relationGraph
  programSystem specialized rows relationCorrespondence)
open RootRewritesOnTheStep (symTerm appTerm unknowns_appTerm unknowns_symTerm)
open Mettapedia.OSLF.Framework.GSLTTypeSynthesis (equalityGSLT)

/-! ## Clauses and their least model -/

/-- A goal of a clause: a condition on the given relations, or a question to a defined relation. -/
inductive Goal where
  | query (condition : Condition ℕ Tm)
  | ask (relation : ℕ) (input output : Tm)

/-- **A clause**: the defined relation holds at the clause's input and output at each instance whose
goals hold. -/
structure Clause where
  relation : ℕ
  input : Tm
  output : Tm
  body : List Goal

variable (R : Relations) (program : List Clause)

/-- A goal at an instance, given where the defined relations hold. -/
def goalHolds (derived : ℕ → Expr → Expr → Prop) (θ : ℕ → Expr) : Goal → Prop
  | .query condition => R condition.name (condition.arguments.map (inst θ)) (inst θ condition.value)
  | .ask relation input output => derived relation (inst θ input) (inst θ output)

/-- Where the defined relations hold by derivations at most `depth` clauses deep. -/
def DerivesAt : ℕ → ℕ → Expr → Expr → Prop
  | 0, _, _, _ => False
  | depth + 1, relation, x, y => ∃ c ∈ program, c.relation = relation ∧ ∃ θ : ℕ → Expr,
      inst θ c.input = x ∧ inst θ c.output = y ∧ ∀ g ∈ c.body, goalHolds R (DerivesAt depth) θ g

/-- **The least model of the clauses**: a defined relation holds where some derivation shows it. -/
def Derives (relation : ℕ) (x y : Expr) : Prop := ∃ depth, DerivesAt R program depth relation x y

variable {R program}

@[simp] theorem inst_unknown (θ : ℕ → Expr) (x : ℕ) : inst θ (Mettapedia.Logic.LP.Term.var x : Tm) = θ x := rfl

theorem goalHolds_mono {derived derived' : ℕ → Expr → Expr → Prop}
    (le : ∀ relation x y, derived relation x y → derived' relation x y) {θ : ℕ → Expr} :
    ∀ {g : Goal}, goalHolds R derived θ g → goalHolds R derived' θ g
  | .query _, holds => holds
  | .ask _ _ _, holds => le _ _ _ holds

theorem DerivesAt.mono : ∀ {depth more : ℕ}, depth ≤ more → ∀ {relation : ℕ} {x y : Expr},
    DerivesAt R program depth relation x y → DerivesAt R program more relation x y
  | 0, _, _, _, _, _, derived => derived.elim
  | _ + 1, 0, le, _, _, _, _ => absurd le (by omega)
  | depth + 1, more + 1, le, _, _, _, derived => by
      obtain ⟨c, member, relationIs, θ, inputIs, outputIs, goals⟩ := derived
      exact ⟨c, member, relationIs, θ, inputIs, outputIs, fun g inside =>
        goalHolds_mono (fun _ _ _ below => DerivesAt.mono (Nat.le_of_succ_le_succ le) below) (goals g inside)⟩

/-- The unknowns of a goal. -/
def goalUnknowns : Goal → List ℕ
  | .query condition => condition.arguments.flatMap unknowns ++ unknowns condition.value
  | .ask _ input output => unknowns input ++ unknowns output

theorem inst_agree {θ θ' : ℕ → Expr} (t : Tm) (agree : ∀ x ∈ unknowns t, θ x = θ' x) : inst θ t = inst θ' t :=
  inst_congr t fun x inside => agree x (mem_unknowns t inside)

/-- A goal depends only on the values of its unknowns. -/
theorem goalHolds_congr {derived : ℕ → Expr → Expr → Prop} {θ θ' : ℕ → Expr} :
    ∀ (g : Goal), (∀ x ∈ goalUnknowns g, θ x = θ' x) → goalHolds R derived θ g → goalHolds R derived θ' g
  | .query condition, agree, holds => by
      have arguments : condition.arguments.map (inst θ) = condition.arguments.map (inst θ') :=
        List.map_congr_left fun t inside => inst_agree t fun x inX =>
          agree x (List.mem_append_left _ (List.mem_flatMap.mpr ⟨t, inside, inX⟩))
      have value : inst θ condition.value = inst θ' condition.value :=
        inst_agree _ fun x inX => agree x (List.mem_append_right _ inX)
      simp only [goalHolds] at holds ⊢
      rw [← arguments, ← value]
      exact holds
  | .ask relation input output, agree, holds => by
      simp only [goalHolds] at holds ⊢
      rw [← inst_agree input fun x inX => agree x (List.mem_append_left _ inX),
        ← inst_agree output fun x inX => agree x (List.mem_append_right _ inX)]
      exact holds

/-- Goals that hold in the least model hold at one depth. -/
theorem derivesAt_of_goals {θ : ℕ → Expr} : ∀ (goals : List Goal),
    (∀ g ∈ goals, goalHolds R (Derives R program) θ g) →
      ∃ depth, ∀ g ∈ goals, goalHolds R (DerivesAt R program depth) θ g
  | [], _ => ⟨0, fun _ inside => absurd inside List.not_mem_nil⟩
  | g :: goals, holds => by
      obtain ⟨depth, later⟩ := derivesAt_of_goals goals fun g' inside => holds g' (List.mem_cons_of_mem _ inside)
      have here : ∃ d, goalHolds R (DerivesAt R program d) θ g := by
        have held := holds g List.mem_cons_self
        cases g with
        | query condition => exact ⟨0, held⟩
        | ask relation input output => exact held
      obtain ⟨d, hereAt⟩ := here
      refine ⟨max depth d, fun g' inside => ?_⟩
      rcases List.mem_cons.mp inside with rfl | inLater
      · exact goalHolds_mono (fun _ _ _ derived => DerivesAt.mono (le_max_right _ _) derived) hereAt
      · exact goalHolds_mono (fun _ _ _ derived => DerivesAt.mono (le_max_left _ _) derived) (later g' inLater)

/-- **An instance of a clause whose goals hold is in the least model.** -/
theorem derives_of_clause {c : Clause} (member : c ∈ program) (θ : ℕ → Expr)
    (goals : ∀ g ∈ c.body, goalHolds R (Derives R program) θ g) :
    Derives R program c.relation (inst θ c.input) (inst θ c.output) := by
  obtain ⟨depth, uniform⟩ := derivesAt_of_goals c.body goals
  exact ⟨depth + 1, c, member, rfl, θ, rfl, rfl, uniform⟩

/-- A derivation is an instance of a clause whose goals hold. -/
theorem derives_cases {relation : ℕ} {x y : Expr} (derived : Derives R program relation x y) :
    ∃ c ∈ program, c.relation = relation ∧ ∃ θ : ℕ → Expr, inst θ c.input = x ∧ inst θ c.output = y ∧
      ∀ g ∈ c.body, goalHolds R (Derives R program) θ g := by
  obtain ⟨depth, derivedAt⟩ := derived
  cases depth with
  | zero => exact derivedAt.elim
  | succ depth =>
      obtain ⟨c, member, relationIs, θ, inputIs, outputIs, goals⟩ := derivedAt
      exact ⟨c, member, relationIs, θ, inputIs, outputIs, fun g inside =>
        goalHolds_mono (fun _ _ _ below => ⟨depth, below⟩) (goals g inside)⟩

/-- More clauses derive more. -/
theorem DerivesAt.mono_program {larger : List Clause} (included : ∀ c ∈ program, c ∈ larger) :
    ∀ {depth relation : ℕ} {x y : Expr}, DerivesAt R program depth relation x y → DerivesAt R larger depth relation x y
  | 0, _, _, _, derived => derived.elim
  | _ + 1, _, _, _, derived => by
      obtain ⟨c, member, relationIs, θ, inputIs, outputIs, goals⟩ := derived
      exact ⟨c, included c member, relationIs, θ, inputIs, outputIs, fun g inside =>
        goalHolds_mono (fun _ _ _ below => DerivesAt.mono_program included below) (goals g inside)⟩

/-! ## Rows -/

/-- The row of the current term. -/
def currentRow (term : Tm) : Tm := appTerm (symTerm 7) term

/-- The row asking for the outputs of a relation at an input. -/
def demandRow (relation : ℕ) (input : Tm) : Tm := appTerm (symTerm 8) (appTerm (symTerm relation) input)

/-- The row of one output of a relation at an input. -/
def answerRow (relation : ℕ) (input output : Tm) : Tm :=
  appTerm (symTerm 9) (appTerm (symTerm relation) (appTerm input output))

/-- The row of an instance of the `clause`-th clause that has passed `passed` goals, with its values. -/
def supplementaryRow (clause passed : ℕ) (values : Tm) : Tm :=
  appTerm (symTerm 10) (appTerm (symTerm (Nat.pair clause passed)) values)

/-- Some unknowns as one row. -/
def valuesTerm : List ℕ → Tm
  | [] => symTerm 0
  | x :: xs => appTerm (.var x) (valuesTerm xs)

/-- The current row. -/
def current (x : Expr) : Expr := .app (.sym 7) x

/-- A demand row. -/
def demand (relation : ℕ) (x : Expr) : Expr := .app (.sym 8) (.app (.sym relation) x)

/-- An answer row. -/
def answer (relation : ℕ) (x y : Expr) : Expr := .app (.sym 9) (.app (.sym relation) (.app x y))

/-- A supplementary row. -/
def supplementary (key : ℕ) (values : Expr) : Expr := .app (.sym 10) (.app (.sym key) values)

@[simp] theorem inst_currentRow (θ : ℕ → Expr) (term : Tm) : inst θ (currentRow term) = current (inst θ term) := rfl

@[simp] theorem inst_demandRow (θ : ℕ → Expr) (relation : ℕ) (input : Tm) :
    inst θ (demandRow relation input) = demand relation (inst θ input) := rfl

@[simp] theorem inst_answerRow (θ : ℕ → Expr) (relation : ℕ) (input output : Tm) :
    inst θ (answerRow relation input output) = answer relation (inst θ input) (inst θ output) := rfl

@[simp] theorem inst_supplementaryRow (θ : ℕ → Expr) (clause passed : ℕ) (values : Tm) :
    inst θ (supplementaryRow clause passed values) = supplementary (Nat.pair clause passed) (inst θ values) := rfl

@[simp] theorem current_inj {x y : Expr} : current x = current y ↔ x = y := by simp [current]

@[simp] theorem answer_inj {relation relation' : ℕ} {x x' y y' : Expr} :
    answer relation x y = answer relation' x' y' ↔ relation = relation' ∧ x = x' ∧ y = y' := by simp [answer]

@[simp] theorem supplementary_inj {key key' : ℕ} {values values' : Expr} :
    supplementary key values = supplementary key' values' ↔ key = key' ∧ values = values' := by simp [supplementary]

@[simp] theorem demand_ne_current (relation : ℕ) (x y : Expr) : demand relation x ≠ current y := by
  simp [demand, current]

@[simp] theorem answer_ne_current (relation : ℕ) (x y z : Expr) : answer relation x y ≠ current z := by
  simp [answer, current]

@[simp] theorem supplementary_ne_current (key : ℕ) (values x : Expr) : supplementary key values ≠ current x := by
  simp [supplementary, current]

theorem values_agree {θ θ' : ℕ → Expr} : ∀ {xs : List ℕ},
    inst θ (valuesTerm xs) = inst θ' (valuesTerm xs) → ∀ x ∈ xs, θ x = θ' x
  | [], _, _, inside => absurd inside List.not_mem_nil
  | y :: ys, same, x, inside => by
      simp only [valuesTerm, RootRewritesOnTheStep.inst_appTerm, inst_unknown, Expr.app.injEq] at same
      rcases List.mem_cons.mp inside with rfl | later
      · exact same.1
      · exact values_agree same.2 x later

@[simp] theorem unknowns_unknown (x : ℕ) : unknowns (Mettapedia.Logic.LP.Term.var x : Tm) = [x] := rfl

theorem unknowns_valuesTerm : ∀ xs : List ℕ, unknowns (valuesTerm xs) = xs
  | [] => rfl
  | x :: xs => by simp [valuesTerm, unknowns_valuesTerm xs]

/-! ## The rules of the clauses -/

/-- The unknowns bound after a clause's input and its first `passed` goals. -/
def boundAt (c : Clause) (passed : ℕ) : List ℕ := unknowns c.input ++ (c.body.take passed).flatMap goalUnknowns

theorem boundAt_succ {c : Clause} {passed : ℕ} {g : Goal} (found : c.body[passed]? = some g) :
    boundAt c (passed + 1) = boundAt c passed ++ goalUnknowns g := by
  simp [boundAt, List.take_add_one, found]

theorem goal_bound {c : Clause} {passed : ℕ} {g : Goal} (inside : g ∈ c.body.take passed) :
    ∀ x ∈ goalUnknowns g, x ∈ boundAt c passed :=
  fun _ inX => List.mem_append_right _ (List.mem_flatMap.mpr ⟨g, inside, inX⟩)

theorem input_bound (c : Clause) (passed : ℕ) : ∀ x ∈ unknowns c.input, x ∈ boundAt c passed :=
  fun _ inside => List.mem_append_left _ inside

/-- A rule that reads rows and makes rows, under conditions. -/
def readRule (read produce : List Tm) (conditions : List (Condition ℕ Tm)) : RuleWithCondition ℕ Tm :=
  { rule := ⟨PUnit.unit, ⟨[], read, [], [], produce⟩, []⟩, conditions }

/-- A demand that the input matches starts an instance of the `index`-th clause. -/
def entryRule (index : ℕ) (c : Clause) : RuleWithCondition ℕ Tm :=
  readRule [demandRow c.relation c.input] [supplementaryRow index 0 (valuesTerm (boundAt c 0))] []

/-- An instance that passed every goal answers. -/
def exitRule (index : ℕ) (c : Clause) : RuleWithCondition ℕ Tm :=
  readRule [supplementaryRow index c.body.length (valuesTerm (boundAt c c.body.length))]
    [answerRow c.relation c.input c.output] []

/-- The rules that pass the `passed`-th goal: a condition is checked; a question is asked, then its answer read. -/
def goalRules (index : ℕ) (c : Clause) (passed : ℕ) : Goal → List (RuleWithCondition ℕ Tm)
  | .query condition =>
      [readRule [supplementaryRow index passed (valuesTerm (boundAt c passed))]
        [supplementaryRow index (passed + 1) (valuesTerm (boundAt c (passed + 1)))] [condition]]
  | .ask relation input output =>
      [readRule [supplementaryRow index passed (valuesTerm (boundAt c passed))] [demandRow relation input] [],
       readRule [supplementaryRow index passed (valuesTerm (boundAt c passed)), answerRow relation input output]
        [supplementaryRow index (passed + 1) (valuesTerm (boundAt c (passed + 1)))] []]

/-- The rules of the `index`-th clause. -/
def clauseRules (index : ℕ) (c : Clause) : List (RuleWithCondition ℕ Tm) :=
  entryRule index c :: ((List.range c.body.length).flatMap fun passed =>
    (c.body[passed]?.map (goalRules index c passed)).getD []) ++ [exitRule index c]

variable (program) in
/-- **The demand transformation of the clauses.** -/
def demandRules : List (RuleWithCondition ℕ Tm) :=
  (List.range program.length).flatMap fun index => (program[index]?.map (clauseRules index)).getD []

theorem mem_demandRules {ρ : RuleWithCondition ℕ Tm} (inside : ρ ∈ demandRules program) :
    ∃ index c, program[index]? = some c ∧ (ρ = entryRule index c ∨ ρ = exitRule index c ∨
      ∃ passed g, c.body[passed]? = some g ∧ ρ ∈ goalRules index c passed g) := by
  simp only [demandRules, List.mem_flatMap, List.mem_range] at inside
  obtain ⟨index, -, inClause⟩ := inside
  cases found : program[index]? with
  | none => simp [found] at inClause
  | some c =>
      rw [found, Option.map_some, Option.getD_some, clauseRules] at inClause
      refine ⟨index, c, found, ?_⟩
      rcases List.mem_cons.mp inClause with rfl | inRest
      · exact .inl rfl
      rcases List.mem_append.mp inRest with inGoals | inExit
      · obtain ⟨passed, -, inGoal⟩ := List.mem_flatMap.mp inGoals
        cases goalFound : c.body[passed]? with
        | none => rw [goalFound] at inGoal; exact absurd inGoal List.not_mem_nil
        | some g =>
            rw [goalFound, Option.map_some, Option.getD_some] at inGoal
            exact .inr (.inr ⟨passed, g, goalFound, inGoal⟩)
      · exact .inr (.inl (List.mem_singleton.mp inExit))

theorem clauseRules_mem {index : ℕ} {c : Clause} (found : program[index]? = some c) {ρ : RuleWithCondition ℕ Tm}
    (inside : ρ ∈ clauseRules index c) : ρ ∈ demandRules program := by
  simp only [demandRules, List.mem_flatMap, List.mem_range]
  exact ⟨index, (List.getElem?_eq_some_iff.mp found).1, by simpa [found] using inside⟩

theorem entryRule_mem {index : ℕ} {c : Clause} (found : program[index]? = some c) :
    entryRule index c ∈ demandRules program :=
  clauseRules_mem found List.mem_cons_self

theorem exitRule_mem {index : ℕ} {c : Clause} (found : program[index]? = some c) :
    exitRule index c ∈ demandRules program :=
  clauseRules_mem found (List.mem_cons_of_mem _ (List.mem_append_right _ (List.mem_singleton_self _)))

theorem goalRules_mem {index : ℕ} {c : Clause} (found : program[index]? = some c) {passed : ℕ} {g : Goal}
    (goalFound : c.body[passed]? = some g) {ρ : RuleWithCondition ℕ Tm} (inside : ρ ∈ goalRules index c passed g) :
    ρ ∈ demandRules program := by
  refine clauseRules_mem found (List.mem_cons_of_mem _ (List.mem_append_left _ (List.mem_flatMap.mpr
    ⟨passed, List.mem_range.mpr (List.getElem?_eq_some_iff.mp goalFound).1, ?_⟩)))
  rw [goalFound, Option.map_some, Option.getD_some]
  exact inside

/-- Every demand rule only reads and makes rows. -/
theorem demandRules_read {ρ : RuleWithCondition ℕ Tm} (inside : ρ ∈ demandRules program) :
    ∃ read produce conditions, ρ = readRule read produce conditions := by
  obtain ⟨index, c, -, rfl | rfl | ⟨passed, g, -, inGoal⟩⟩ := mem_demandRules inside
  · exact ⟨_, _, _, rfl⟩
  · exact ⟨_, _, _, rfl⟩
  · cases g with
    | query condition =>
        rw [goalRules, List.mem_singleton] at inGoal
        exact ⟨_, _, _, inGoal⟩
    | ask relation input output =>
        simp only [goalRules, List.mem_cons, List.not_mem_nil, or_false] at inGoal
        rcases inGoal with rfl | rfl
        · exact ⟨_, _, _, rfl⟩
        · exact ⟨_, _, _, rfl⟩

/-! ## Firings -/

theorem readRule_fires {read produce : List Tm} {conditions : List (Condition ℕ Tm)} {θ : ℕ → Expr}
    {bag : Multiset Expr} (reads : ∀ q ∈ read, inst θ q ∈ bag)
    (holds : ∀ c ∈ conditions, R c.name (c.arguments.map (inst θ)) (inst θ c.value)) :
    RelationStep R (readRule read produce conditions) bag ((produce.map (inst θ) : Multiset Expr) + bag) :=
  ⟨θ, bag, by simp [readRule], reads, by simp [readRule, equationsOf], holds, rfl⟩

theorem readRule_fired {read produce : List Tm} {conditions : List (Condition ℕ Tm)} {bag after : Multiset Expr}
    (fired : RelationStep R (readRule read produce conditions) bag after) :
    ∃ θ : ℕ → Expr, (∀ q ∈ read, inst θ q ∈ bag) ∧
      (∀ c ∈ conditions, R c.name (c.arguments.map (inst θ)) (inst θ c.value)) ∧
      after = (produce.map (inst θ) : Multiset Expr) + bag := by
  obtain ⟨θ, rest, split, reads, _, holds, rfl⟩ := fired
  have same : rest = bag := by simpa [readRule] using split
  subst same
  exact ⟨θ, reads, holds, rfl⟩

/-! ## What the rows state -/

variable (R program) in
/-- **What a supplementary row states**: an instance of a clause whose goals so far hold, with the values of the
unknowns bound so far. -/
def SupplementarySound (key : ℕ) (values : Expr) : Prop :=
  ∃ index passed c, key = Nat.pair index passed ∧ program[index]? = some c ∧ passed ≤ c.body.length ∧
    ∃ θ : ℕ → Expr, values = inst θ (valuesTerm (boundAt c passed)) ∧
      ∀ g ∈ c.body.take passed, goalHolds R (Derives R program) θ g

variable (R program) in
/-- **What a row states**: an answer holds in the least model, and a supplementary row is an instance whose
goals so far hold. -/
def RowSound (row : Expr) : Prop :=
  (∀ relation x y, row = answer relation x y → Derives R program relation x y) ∧
    ∀ key values, row = supplementary key values → SupplementarySound R program key values

theorem rowSound_demand (relation : ℕ) (x : Expr) : RowSound R program (demand relation x) :=
  ⟨fun _ _ _ same => by simp [demand, answer] at same, fun _ _ same => by simp [demand, supplementary] at same⟩

theorem rowSound_current (x : Expr) : RowSound R program (current x) :=
  ⟨fun _ _ _ same => by simp [current, answer] at same, fun _ _ same => by simp [current, supplementary] at same⟩

theorem rowSound_answer {relation : ℕ} {x y : Expr} (derived : Derives R program relation x y) :
    RowSound R program (answer relation x y) := by
  refine ⟨fun _ _ _ same => ?_, fun _ _ same => by simp [answer, supplementary] at same⟩
  obtain ⟨rfl, rfl, rfl⟩ := answer_inj.mp same
  exact derived

theorem rowSound_supplementary {key : ℕ} {values : Expr} (holds : SupplementarySound R program key values) :
    RowSound R program (supplementary key values) := by
  refine ⟨fun _ _ _ same => by simp [answer, supplementary] at same, fun _ _ same => ?_⟩
  obtain ⟨rfl, rfl⟩ := supplementary_inj.mp same
  exact holds

/-- A supplementary row of a run gives the goals so far at its own instance. -/
theorem supplementary_read {bag : Multiset Expr} (sound : ∀ row ∈ bag, RowSound R program row)
    {index passed : ℕ} {c : Clause} (found : program[index]? = some c) {θ : ℕ → Expr}
    (present : supplementary (Nat.pair index passed) (inst θ (valuesTerm (boundAt c passed))) ∈ bag) :
    passed ≤ c.body.length ∧ ∀ g ∈ c.body.take passed, goalHolds R (Derives R program) θ g := by
  obtain ⟨index', passed', c', key, found', within, θ', values, goals⟩ := (sound _ present).2 _ _ rfl
  obtain ⟨rfl, rfl⟩ := Nat.pair_eq_pair.mp key
  rw [found] at found'
  cases found'
  exact ⟨within, fun g inside => goalHolds_congr g
    (fun x inX => (values_agree values x (goal_bound inside x inX)).symm) (goals g inside)⟩

theorem take_succ_goals {c : Clause} {passed : ℕ} {g : Goal} (found : c.body[passed]? = some g) :
    c.body.take (passed + 1) = c.body.take passed ++ [g] := by
  rw [List.take_add_one, found, Option.toList_some]

/-- A supplementary row after one more goal, at an instance where the goals so far and this goal hold. -/
theorem supplementary_next {index passed : ℕ} {c : Clause} (found : program[index]? = some c) {g : Goal}
    (goalFound : c.body[passed]? = some g) {θ : ℕ → Expr}
    (before : ∀ g' ∈ c.body.take passed, goalHolds R (Derives R program) θ g')
    (here : goalHolds R (Derives R program) θ g) :
    RowSound R program (supplementary (Nat.pair index (passed + 1)) (inst θ (valuesTerm (boundAt c (passed + 1))))) :=
  rowSound_supplementary ⟨index, passed + 1, c, rfl, found, (List.getElem?_eq_some_iff.mp goalFound).1, θ, rfl,
    fun g' inside => by
      rw [take_succ_goals goalFound] at inside
      rcases List.mem_append.mp inside with earlier | now
      · exact before g' earlier
      · rw [List.mem_singleton.mp now]
        exact here⟩

theorem added_single {θ : ℕ → Expr} {t : Tm} {row : Expr}
    (inside : row ∈ ((([t] : List Tm).map (inst θ) : List Expr) : Multiset Expr)) : row = inst θ t := by
  simpa using inside

/-- **Every demand rule adds rows that state what they say, and no current row.** -/
theorem fired_sound {ρ : RuleWithCondition ℕ Tm} (inProgram : ρ ∈ demandRules program) {bag after : Multiset Expr}
    (sound : ∀ row ∈ bag, RowSound R program row) (fired : RelationStep R ρ bag after) :
    ∃ added : Multiset Expr, after = added + bag ∧ ∀ row ∈ added, RowSound R program row ∧ ∀ x, row ≠ current x := by
  obtain ⟨index, c, found, origin⟩ := mem_demandRules inProgram
  rcases origin with rfl | rfl | ⟨passed, g, goalFound, inGoal⟩
  · obtain ⟨θ, -, -, rfl⟩ := readRule_fired fired
    refine ⟨_, rfl, fun row inside => ?_⟩
    rw [added_single inside, inst_supplementaryRow]
    exact ⟨rowSound_supplementary ⟨index, 0, c, rfl, found, Nat.zero_le _, θ, rfl, by simp⟩,
      fun _ => supplementary_ne_current _ _ _⟩
  · obtain ⟨θ, reads, -, rfl⟩ := readRule_fired fired
    obtain ⟨-, goals⟩ := supplementary_read sound found (by simpa using reads _ List.mem_cons_self)
    rw [List.take_length] at goals
    refine ⟨_, rfl, fun row inside => ?_⟩
    rw [added_single inside, inst_answerRow]
    exact ⟨rowSound_answer (derives_of_clause (List.mem_of_getElem? found) θ goals), fun _ => answer_ne_current _ _ _ _⟩
  · cases g with
    | query condition =>
        rw [goalRules, List.mem_singleton] at inGoal
        subst inGoal
        obtain ⟨θ, reads, conditions, rfl⟩ := readRule_fired fired
        obtain ⟨-, goals⟩ := supplementary_read sound found (by simpa using reads _ List.mem_cons_self)
        refine ⟨_, rfl, fun row inside => ?_⟩
        rw [added_single inside, inst_supplementaryRow]
        exact ⟨supplementary_next found goalFound goals (conditions _ List.mem_cons_self),
          fun _ => supplementary_ne_current _ _ _⟩
    | ask relation input output =>
        simp only [goalRules, List.mem_cons, List.not_mem_nil, or_false] at inGoal
        rcases inGoal with rfl | rfl
        · obtain ⟨θ, -, -, rfl⟩ := readRule_fired fired
          refine ⟨_, rfl, fun row inside => ?_⟩
          rw [added_single inside, inst_demandRow]
          exact ⟨rowSound_demand _ _, fun _ => demand_ne_current _ _ _⟩
        · obtain ⟨θ, reads, -, rfl⟩ := readRule_fired fired
          obtain ⟨-, goals⟩ := supplementary_read sound found (by simpa using reads _ List.mem_cons_self)
          have answered := (sound _ (reads _ (List.mem_cons_of_mem _ List.mem_cons_self))).1 relation
            (inst θ input) (inst θ output) rfl
          refine ⟨_, rfl, fun row inside => ?_⟩
          rw [added_single inside, inst_supplementaryRow]
          exact ⟨supplementary_next found goalFound goals answered, fun _ => supplementary_ne_current _ _ _⟩

/-! ## Every derived answer is reached -/

variable (R) in
/-- The firings of some rules on bags, under the relations. -/
abbrev bagSystem (rules : List (RuleWithCondition ℕ Tm)) : GSLT := relationEvaluation R {ρ | ρ ∈ rules}

theorem multiStep_trans {S : GSLT} {first second third : S.Term} (one : S.MultiStep first second)
    (two : S.MultiStep second third) : S.MultiStep first third := by
  induction one with
  | refl => exact two
  | step head _ ih => exact .step head (ih two)

/-- Induction along a run. -/
theorem multiStep_rec {S : GSLT} (P : S.Term → S.Term → Prop) (refl : ∀ t, P t t)
    (step : ∀ {t u v : S.Term}, S.Step t u → S.MultiStep u v → P u v → P t v) {t v : S.Term}
    (steps : S.MultiStep t v) : P t v := by
  induction steps with
  | refl t => exact refl t
  | step head rest ih => exact step head rest ih

theorem multiStep_mono {rules larger : List (RuleWithCondition ℕ Tm)} (included : ∀ ρ ∈ rules, ρ ∈ larger)
    {bag later : Multiset Expr} (steps : (bagSystem R rules).MultiStep bag later) :
    (bagSystem R larger).MultiStep bag later :=
  multiStep_rec (S := bagSystem R rules) (fun (bag later : Multiset Expr) => (bagSystem R larger).MultiStep bag later)
    (fun _ => .refl _) (fun head _ ih => by
      obtain ⟨ρ, inRules, fired⟩ := head
      exact .step ⟨ρ, included ρ inRules, fired⟩ ih) steps

theorem fire {ρ : RuleWithCondition ℕ Tm} {rules : List (RuleWithCondition ℕ Tm)} (inRules : ρ ∈ rules)
    {bag next : Multiset Expr} (fired : RelationStep R ρ bag next) : (bagSystem R rules).MultiStep bag next :=
  .step ⟨ρ, inRules, fired⟩ (.refl _)

/-- Firings of the demand rules only add rows, which state what they say and are not current. -/
theorem multiStep_adds {bag later : Multiset Expr} (steps : (bagSystem R (demandRules program)).MultiStep bag later)
    (sound : ∀ row ∈ bag, RowSound R program row) :
    ∃ added : Multiset Expr, later = added + bag ∧ ∀ row ∈ added, RowSound R program row ∧ ∀ x, row ≠ current x := by
  revert sound
  refine multiStep_rec (S := bagSystem R (demandRules program)) (fun (bag later : Multiset Expr) =>
    (∀ row ∈ bag, RowSound R program row) → ∃ added : Multiset Expr, later = added + bag ∧
      ∀ row ∈ added, RowSound R program row ∧ ∀ x, row ≠ current x)
    (fun _ _ => ⟨0, (zero_add _).symm, fun _ inside => absurd inside (Multiset.notMem_zero _)⟩) ?_ steps
  intro bag middle later head _ ih sound
  obtain ⟨ρ, inRules, fired⟩ := head
  obtain ⟨first, middleIs, firstSound⟩ := fired_sound inRules sound fired
  obtain ⟨second, laterIs, secondSound⟩ := ih fun row inside => by
    rw [middleIs] at inside
    exact (Multiset.mem_add.mp inside).elim (fun inFirst => (firstSound row inFirst).1) (sound row)
  refine ⟨second + first, by rw [laterIs, middleIs]; exact (add_assoc _ _ _).symm, fun row inside => ?_⟩
  rcases Multiset.mem_add.mp inside with inSecond | inFirst
  · exact secondSound row inSecond
  · exact firstSound row inFirst

theorem multiStep_keeps {bag later : Multiset Expr} (steps : (bagSystem R (demandRules program)).MultiStep bag later)
    {row : Expr} (inside : row ∈ bag) : row ∈ later := by
  revert inside
  refine multiStep_rec (S := bagSystem R (demandRules program))
    (fun (bag later : Multiset Expr) => row ∈ bag → row ∈ later) (fun _ inside => inside) ?_ steps
  intro bag middle later head _ ih inside
  obtain ⟨ρ, inRules, fired⟩ := head
  obtain ⟨read, produce, conditions, rfl⟩ := demandRules_read inRules
  obtain ⟨θ, -, -, middleIs⟩ := readRule_fired fired
  exact ih (by rw [middleIs]; exact Multiset.mem_add.mpr (.inr inside))

/-- **From a demand, the demand rules reach an answer for every output the least model gives.** -/
theorem answers_reachable : ∀ (depth : ℕ) {relation : ℕ} {x y : Expr}, DerivesAt R program depth relation x y →
    ∀ {bag : Multiset Expr}, demand relation x ∈ bag →
      ∃ later : Multiset Expr, (bagSystem R (demandRules program)).MultiStep bag later ∧ answer relation x y ∈ later := by
  intro depth
  induction depth with
  | zero => intro _ _ _ derived; exact derived.elim
  | succ depth ih =>
    intro relation x y derived bag demanded
    obtain ⟨c, member, rfl, θ, rfl, rfl, goals⟩ := derived
    obtain ⟨index, within, cIs⟩ := List.getElem_of_mem member
    have found : program[index]? = some c := by rw [List.getElem?_eq_getElem within, cIs]
    have entered := fire (entryRule_mem found) (readRule_fires (R := R) (θ := θ) (produce :=
      [supplementaryRow index 0 (valuesTerm (boundAt c 0))]) (conditions := [])
      (fun q inside => by rw [List.mem_singleton.mp inside, inst_demandRow]; exact demanded)
      (fun _ inside => absurd inside List.not_mem_nil))
    have passes : ∀ passed ≤ c.body.length, ∃ later : Multiset Expr,
        (bagSystem R (demandRules program)).MultiStep bag later ∧
        supplementary (Nat.pair index passed) (inst θ (valuesTerm (boundAt c passed))) ∈ later := by
      intro passed
      induction passed with
      | zero => exact fun _ => ⟨_, entered, by simp⟩
      | succ passed inner =>
        intro within
        obtain ⟨later, steps, present⟩ := inner (by omega)
        obtain ⟨g, goalFound⟩ : ∃ g, c.body[passed]? = some g :=
          ⟨c.body[passed], List.getElem?_eq_getElem (by omega)⟩
        have held := goals g (List.mem_of_getElem? goalFound)
        cases g with
        | query condition =>
            have checked := fire (goalRules_mem found goalFound List.mem_cons_self) (readRule_fires (R := R)
              (θ := θ) (bag := later) (produce := [supplementaryRow index (passed + 1)
                (valuesTerm (boundAt c (passed + 1)))])
              (fun q inside => by rw [List.mem_singleton.mp inside, inst_supplementaryRow]; exact present)
              (fun c' inside => by rw [List.mem_singleton.mp inside]; exact held))
            exact ⟨_, multiStep_trans steps checked, by simp⟩
        | ask relation input output =>
            have asked := fire (goalRules_mem found goalFound List.mem_cons_self) (readRule_fires (R := R)
              (θ := θ) (bag := later) (produce := [demandRow relation input])
              (fun q inside => by rw [List.mem_singleton.mp inside, inst_supplementaryRow]; exact present)
              (fun _ inside => absurd inside List.not_mem_nil))
            have demanded' : demand relation (inst θ input) ∈
                (([demandRow relation input].map (inst θ) : List Expr) : Multiset Expr) + later :=
              Multiset.mem_add.mpr (.inl (by simp))
            obtain ⟨answered, answering, answerIn⟩ := ih held demanded'
            have read := fire (goalRules_mem found goalFound (List.mem_cons_of_mem _ List.mem_cons_self))
              (readRule_fires (R := R) (θ := θ) (bag := answered) (produce := [supplementaryRow index (passed + 1)
                (valuesTerm (boundAt c (passed + 1)))]) (conditions := [])
              (fun q inside => by
                simp only [List.mem_cons, List.not_mem_nil, or_false] at inside
                rcases inside with rfl | rfl
                · rw [inst_supplementaryRow]
                  exact multiStep_keeps answering (Multiset.mem_add.mpr (.inr present))
                · rw [inst_answerRow]
                  exact answerIn)
              (fun _ inside => absurd inside List.not_mem_nil))
            exact ⟨_, multiStep_trans steps (multiStep_trans asked (multiStep_trans answering read)), by simp⟩
    obtain ⟨later, steps, present⟩ := passes c.body.length le_rfl
    have exited := fire (exitRule_mem found) (readRule_fires (R := R) (θ := θ) (bag := later)
      (produce := [answerRow c.relation c.input c.output]) (conditions := [])
      (fun q inside => by rw [List.mem_singleton.mp inside, inst_supplementaryRow]; exact present)
      (fun _ inside => absurd inside List.not_mem_nil))
    exact ⟨_, multiStep_trans steps exited, by simp⟩

/-! ## Runs at a row -/

/-- **The seed**: ask a relation at the current row. -/
def seedRule (relation : ℕ) : RuleWithCondition ℕ Tm := readRule [currentRow (.var 0)] [demandRow relation (.var 0)] []

/-- **The commit**: replace the current row by an answer of a relation at it. -/
def commitRule (relation : ℕ) : RuleWithCondition ℕ Tm :=
  { rule := ⟨PUnit.unit, ⟨[currentRow (.var 0)], [answerRow relation (.var 0) (.var 1)], [], [],
      [currentRow (.var 1)]⟩, []⟩,
    conditions := [] }

variable (program) in
/-- **The rules of a run** that moves along the relations `moves`. -/
def runRules (moves : List ℕ) : List (RuleWithCondition ℕ Tm) :=
  moves.map seedRule ++ moves.map commitRule ++ demandRules program

variable (R program) in
/-- **A run at a row**: the row is the one current row, and every row states what it says. -/
def AtRow (x : Expr) (bag : Multiset Expr) : Prop :=
  ∃ rest, bag = current x ::ₘ rest ∧ (∀ row ∈ rest, ∀ y, row ≠ current y) ∧ ∀ row ∈ bag, RowSound R program row

variable (R program) in
/-- One move along one of the relations `moves`. -/
def Moves (moves : List ℕ) (x y : Expr) : Prop := ∃ relation ∈ moves, Derives R program relation x y

theorem commitRule_fired {relation : ℕ} {bag after : Multiset Expr} (fired : RelationStep R (commitRule relation) bag after) :
    ∃ (θ : ℕ → Expr) (rest : Multiset Expr), bag = current (θ 0) ::ₘ rest ∧
      answer relation (θ 0) (θ 1) ∈ rest ∧ after = current (θ 1) ::ₘ rest := by
  obtain ⟨θ, rest, split, reads, _, _, rfl⟩ := fired
  refine ⟨θ, rest, ?_, by simpa [commitRule] using reads, ?_⟩
  · simpa [commitRule] using split.symm
  · simp [commitRule]

theorem commitRule_fires {relation : ℕ} {θ : ℕ → Expr} {rest : Multiset Expr}
    (answered : answer relation (θ 0) (θ 1) ∈ rest) :
    RelationStep R (commitRule relation) (current (θ 0) ::ₘ rest) (current (θ 1) ::ₘ rest) :=
  ⟨θ, rest, by simp [commitRule], by simpa [commitRule] using answered, by simp [commitRule, equationsOf],
    by simp [commitRule], by simp [commitRule]⟩

/-- **Every firing from a run at a row keeps the run at the row, or moves it along one of the relations.** -/
theorem readStep {moves : List ℕ} {x : Expr} {bag next : Multiset Expr} (at_ : AtRow R program x bag)
    (fired : ∃ ρ ∈ runRules program moves, RelationStep R ρ bag next) :
    AtRow R program x next ∨ ∃ y, Moves R program moves x y ∧ AtRow R program y next := by
  obtain ⟨rest, bagIs, restQuiet, sound⟩ := at_
  obtain ⟨ρ, inRules, fired⟩ := fired
  simp only [runRules, List.mem_append, List.mem_map] at inRules
  rcases inRules with (⟨relation, -, rfl⟩ | ⟨relation, member, rfl⟩) | inDemand
  · obtain ⟨θ, -, -, rfl⟩ := readRule_fired fired
    refine .inl ⟨_, by rw [bagIs, Multiset.add_cons], fun row inside y => ?_, fun row inside => ?_⟩
    · rcases Multiset.mem_add.mp inside with inAdded | inRest
      · rw [added_single inAdded, inst_demandRow]
        exact demand_ne_current _ _ _
      · exact restQuiet row inRest y
    · rcases Multiset.mem_add.mp inside with inAdded | inBag
      · rw [added_single inAdded, inst_demandRow]
        exact rowSound_demand _ _
      · exact sound row inBag
  · obtain ⟨θ, rest', bagIs', answered, rfl⟩ := commitRule_fired fired
    have currentIn : current (θ 0) ∈ bag := by rw [bagIs']; exact Multiset.mem_cons_self _ _
    rw [bagIs] at currentIn
    rcases Multiset.mem_cons.mp currentIn with same | inRest
    · have firstIs : θ 0 = x := current_inj.mp same
      have restIs : rest' = rest := by
        have both := bagIs'.symm.trans bagIs
        rw [firstIs] at both
        exact (Multiset.cons_inj_right _).mp both
      subst restIs
      have derived := (sound _ (by rw [bagIs']; exact Multiset.mem_cons_of_mem answered)).1 relation (θ 0) (θ 1) rfl
      rw [firstIs] at derived
      refine .inr ⟨θ 1, ⟨relation, member, derived⟩, rest', rfl, restQuiet, fun row inside => ?_⟩
      rcases Multiset.mem_cons.mp inside with rfl | inRest'
      · exact rowSound_current _
      · exact sound row (by rw [bagIs']; exact Multiset.mem_cons_of_mem inRest')
    · exact absurd rfl (restQuiet _ inRest (θ 0))
  · obtain ⟨added, rfl, addedSound⟩ := fired_sound inDemand sound fired
    refine .inl ⟨added + rest, by rw [bagIs, Multiset.add_cons], fun row inside y => ?_, fun row inside => ?_⟩
    · rcases Multiset.mem_add.mp inside with inAdded | inRest
      · exact (addedSound row inAdded).2 y
      · exact restQuiet row inRest y
    · rcases Multiset.mem_add.mp inside with inAdded | inBag
      · exact (addedSound row inAdded).1
      · exact sound row inBag

/-- **Every move along one of the relations is a run of firings.** -/
theorem forward {moves : List ℕ} {x y : Expr} {bag : Multiset Expr} (at_ : AtRow R program x bag)
    (moved : Moves R program moves x y) :
    ∃ next : Multiset Expr, (bagSystem R (runRules program moves)).MultiStep bag next ∧ AtRow R program y next := by
  obtain ⟨rest, bagIs, restQuiet, sound⟩ := at_
  obtain ⟨relation, member, depth, derived⟩ := moved
  have inDemand : ∀ ρ ∈ demandRules program, ρ ∈ runRules program moves :=
    fun ρ inside => List.mem_append_right _ inside
  have seeded := readRule_fires (R := R) (θ := fun _ => x) (bag := bag) (read := [currentRow (.var 0)])
    (produce := [demandRow relation (.var 0)]) (conditions := [])
    (fun q inside => by rw [List.mem_singleton.mp inside, bagIs]; simp)
    (fun _ inside => absurd inside List.not_mem_nil)
  have seedIn : seedRule relation ∈ runRules program moves :=
    List.mem_append_left _ (List.mem_append_left _ (List.mem_map.mpr ⟨relation, member, rfl⟩))
  have seedSound : ∀ row ∈ (([demandRow relation (.var 0)].map (inst fun _ => x) : List Expr) : Multiset Expr) + bag,
      RowSound R program row := fun row inside => (Multiset.mem_add.mp inside).elim
    (fun inAdded => by rw [added_single inAdded, inst_demandRow]; exact rowSound_demand _ _)
    (sound row)
  have demanded : demand relation x ∈
      (([demandRow relation (.var 0)].map (inst fun _ => x) : List Expr) : Multiset Expr) + bag :=
    Multiset.mem_add.mpr (.inl (by simp))
  obtain ⟨answered, answering, answerIn⟩ := answers_reachable depth derived demanded
  obtain ⟨added, answeredIs, addedSound⟩ := multiStep_adds answering seedSound
  have reshaped : answered = current x ::ₘ (added + (demand relation x ::ₘ rest)) := by
    rw [answeredIs, bagIs]
    simp [Multiset.add_cons]
  have answerInRest : answer relation x y ∈ added + (demand relation x ::ₘ rest) := by
    rw [reshaped] at answerIn
    rcases Multiset.mem_cons.mp answerIn with same | inside
    · simp [answer, current] at same
    · exact inside
  have committed := commitRule_fires (R := R) (relation := relation)
    (θ := fun n => if n = 0 then x else y) (rest := added + (demand relation x ::ₘ rest)) (by simpa using answerInRest)
  simp only [one_ne_zero, if_false, if_true] at committed
  have commitIn : commitRule relation ∈ runRules program moves :=
    List.mem_append_left _ (List.mem_append_right _ (List.mem_map.mpr ⟨relation, member, rfl⟩))
  refine ⟨_, multiStep_trans (fire seedIn seeded) (multiStep_trans (multiStep_mono inDemand answering)
    (fire commitIn (by rw [reshaped]; exact committed))), added + (demand relation x ::ₘ rest), rfl,
    fun row inside z => ?_, fun row inside => ?_⟩
  · rcases Multiset.mem_add.mp inside with inAdded | inRest
    · exact (addedSound row inAdded).2 z
    · rcases Multiset.mem_cons.mp inRest with rfl | inRest'
      · exact demand_ne_current _ _ _
      · exact restQuiet row inRest' z
  · rcases Multiset.mem_cons.mp inside with rfl | inRest
    · exact rowSound_current _
    · rcases Multiset.mem_add.mp inRest with inAdded | inRest'
      · exact (addedSound row inAdded).1
      · rcases Multiset.mem_cons.mp inRest' with rfl | inRest''
        · exact rowSound_demand _ _
        · exact sound row (by rw [bagIs]; exact Multiset.mem_cons_of_mem inRest'')

variable (R program) in
/-- **The relations on rows and the runs of their rules, on bags.** -/
def bagCorrespondence (moves : List ℕ) :
    OperationalCorrespondence (equalityGSLT Expr (Moves R program moves)) (bagSystem R (runRules program moves)) where
  related := AtRow R program
  readStep := fun at_ fired => readStep at_ fired
  forward := fun at_ moved => by
    obtain ⟨next, steps, atNext⟩ := forward at_ moved
    exact ⟨next, (executionPath_nonempty_iff_multiStep _ _ _).mpr steps, atNext⟩

/-! ## On the transform step -/

/-- The unknowns a goal needs when it is reached: a condition's arguments, a question's input. -/
def goalInputs : Goal → List ℕ
  | .query condition => condition.arguments.flatMap unknowns
  | .ask _ input _ => unknowns input

/-- **A moded clause**: what each goal needs is bound when it is reached, and the output is bound at the end. -/
def Moded (c : Clause) : Prop :=
  (∀ passed g, c.body[passed]? = some g → ∀ x ∈ goalInputs g, x ∈ boundAt c passed) ∧
    ∀ x ∈ unknowns c.output, x ∈ boundAt c c.body.length

/-- Whether a clause is moded, by computation. -/
def modedCheck (c : Clause) : Bool :=
  (List.range c.body.length).all (fun passed => match c.body[passed]? with
    | some g => (goalInputs g).all fun x => (boundAt c passed).contains x
    | none => true) &&
    (unknowns c.output).all fun x => (boundAt c c.body.length).contains x

theorem moded_of_check {c : Clause} (checked : modedCheck c = true) : Moded c := by
  simp only [modedCheck, Bool.and_eq_true, List.all_eq_true, List.mem_range, List.contains_iff_mem] at checked
  refine ⟨fun passed g found x inside => ?_, checked.2⟩
  have here := checked.1 passed (List.getElem?_eq_some_iff.mp found).1
  rw [found] at here
  simp only [List.all_eq_true, List.contains_iff_mem] at here
  exact here x inside

/-- The instantiation of the first unknowns by some rows. -/
def pick (values : List Expr) (n : ℕ) : Expr := values.getD n (.sym 0)

/-! ## Goals in order -/

/-- **The goals' inputs are bound in order**: what each goal needs is bound before it, or by an earlier goal. -/
inductive InputsBound : List ℕ → List Goal → Prop
  | nil (bound : List ℕ) : InputsBound bound []
  | cons {bound : List ℕ} {g : Goal} {goals : List Goal} : (∀ x ∈ goalInputs g, x ∈ bound) →
      InputsBound (bound ++ goalUnknowns g) goals → InputsBound bound (g :: goals)

theorem InputsBound.mono : ∀ {bound bound' : List ℕ} {goals : List Goal}, (∀ x ∈ bound, x ∈ bound') →
    InputsBound bound goals → InputsBound bound' goals
  | _, _, _, _, .nil _ => .nil _
  | _, _, _, more, .cons first later => .cons (fun x inside => more x (first x inside))
      (InputsBound.mono (fun x inside => (List.mem_append.mp inside).elim
        (fun inBound => List.mem_append_left _ (more x inBound)) (List.mem_append_right _)) later)

theorem InputsBound.append : ∀ {bound : List ℕ} {first second : List Goal}, InputsBound bound first →
    InputsBound (bound ++ first.flatMap goalUnknowns) second → InputsBound bound (first ++ second)
  | _, [], _, _, two => by simpa using two
  | _, _ :: _, _, .cons head later, two =>
      .cons head (InputsBound.append later (by simpa [List.flatMap_cons, List.append_assoc] using two))

theorem inputsBound_iff : ∀ {bound : List ℕ} {goals : List Goal}, InputsBound bound goals ↔
    ∀ passed g, goals[passed]? = some g → ∀ x ∈ goalInputs g, x ∈ bound ++ (goals.take passed).flatMap goalUnknowns
  | bound, [] => ⟨fun _ _ _ found => by simp at found, fun _ => .nil bound⟩
  | bound, g :: goals => by
      constructor
      · intro flows passed g' found x inside
        cases flows with
        | cons first later =>
          cases passed with
          | zero =>
              simp only [List.getElem?_cons_zero, Option.some.injEq] at found
              subst found
              exact List.mem_append_left _ (first x inside)
          | succ passed =>
              have here := inputsBound_iff.mp later passed g' (by simpa using found) x inside
              simpa [List.take_succ_cons, List.flatMap_cons, List.append_assoc] using here
      · intro flows
        refine .cons (fun x inside => by simpa using flows 0 g rfl x inside) (inputsBound_iff.mpr ?_)
        intro passed g' found x inside
        have here := flows (passed + 1) g' (by simpa using found) x inside
        simpa [List.take_succ_cons, List.flatMap_cons, List.append_assoc] using here

/-- **A clause whose goals' inputs are bound in order from its input, and whose output is bound at the end, is
moded.** -/
theorem moded_of_inputsBound {c : Clause} (flows : InputsBound (unknowns c.input) c.body)
    (output : ∀ x ∈ unknowns c.output, x ∈ unknowns c.input ++ c.body.flatMap goalUnknowns) : Moded c :=
  ⟨fun passed g found x inside => inputsBound_iff.mp flows passed g found x inside,
    fun x inside => by simpa [boundAt] using output x inside⟩

theorem readRule_restricted {read produce : List Tm} {conditions : List (Condition ℕ Tm)}
    (bound : ∀ t ∈ produce, ∀ x ∈ unknowns t, (∃ q ∈ read, x ∈ unknowns q) ∨ ∃ c ∈ conditions, x ∈ unknowns c.value) :
    (readRule read produce conditions).RangeRestrictedWith := by
  intro t inWritten x inVars
  have made : t ∈ produce := by simpa [written, readRule] using inWritten
  rcases bound t made x (mem_unknowns t inVars) with ⟨q, inRead, inQ⟩ | ⟨c, inConditions, inValue⟩
  · exact .inl ⟨q, by simpa [readRule] using inRead, vars_of_mem_unknowns q inQ⟩
  · exact .inr ⟨c, inConditions, vars_of_mem_unknowns c.value inValue⟩

/-- A rule whose single made row has only unknowns of its first read row. -/
theorem readRule_restricted_one {first : Tm} {read : List Tm} {made : Tm} {conditions : List (Condition ℕ Tm)}
    (bound : ∀ x ∈ unknowns made, x ∈ unknowns first) :
    (readRule (first :: read) [made] conditions).RangeRestrictedWith :=
  readRule_restricted fun t inside x inX => by
    rw [List.mem_singleton.mp inside] at inX
    exact .inl ⟨first, List.mem_cons_self, bound x inX⟩

theorem commitRule_restricted (relation : ℕ) : (commitRule relation).RangeRestrictedWith := by
  intro t inWritten x inVars
  have made : t = currentRow (.var 1) := by simpa [written, commitRule] using inWritten
  subst made
  have one : x = 1 := by simpa [currentRow] using mem_unknowns _ inVars
  subst one
  exact .inl ⟨answerRow relation (.var 0) (.var 1), by simp [commitRule],
    vars_of_mem_unknowns _ (by simp [answerRow])⟩

theorem unknowns_supplementaryRow (index passed : ℕ) (xs : List ℕ) :
    unknowns (supplementaryRow index passed (valuesTerm xs)) = xs := by
  simp [supplementaryRow, unknowns_valuesTerm]

/-- **Every demand rule of moded clauses is range-restricted.** -/
theorem demandRules_restricted (moded : ∀ c ∈ program, Moded c) :
    ∀ ρ ∈ demandRules program, ρ.RangeRestrictedWith := by
  intro ρ inside
  obtain ⟨index, c, found, origin⟩ := mem_demandRules inside
  have shape := moded c (List.mem_of_getElem? found)
  rcases origin with rfl | rfl | ⟨passed, g, goalFound, inGoal⟩
  · refine readRule_restricted_one fun x inX => ?_
    simpa [unknowns_supplementaryRow, boundAt, demandRow] using inX
  · refine readRule_restricted_one fun x inX => ?_
    rw [unknowns_supplementaryRow]
    simp only [answerRow, unknowns_appTerm, unknowns_symTerm, List.nil_append, List.mem_append] at inX
    rcases inX with inInput | inOutput
    · exact input_bound c _ x inInput
    · exact shape.2 x inOutput
  · have inputs := shape.1 passed g goalFound
    cases g with
    | query condition =>
        rw [goalRules, List.mem_singleton] at inGoal
        subst inGoal
        refine readRule_restricted fun t inside x inX => ?_
        rw [List.mem_singleton.mp inside, unknowns_supplementaryRow, boundAt_succ goalFound] at inX
        simp only [goalUnknowns, List.mem_append] at inX
        rcases inX with inBound | inArguments | inValue
        · exact .inl ⟨_, List.mem_cons_self, by rw [unknowns_supplementaryRow]; exact inBound⟩
        · exact .inl ⟨_, List.mem_cons_self, by rw [unknowns_supplementaryRow]; exact inputs x inArguments⟩
        · exact .inr ⟨condition, List.mem_cons_self, inValue⟩
    | ask relation input output =>
        simp only [goalRules, List.mem_cons, List.not_mem_nil, or_false] at inGoal
        rcases inGoal with rfl | rfl
        · refine readRule_restricted_one fun x inX => ?_
          rw [unknowns_supplementaryRow]
          simp only [demandRow, unknowns_appTerm, unknowns_symTerm, List.nil_append] at inX
          exact inputs x inX
        · refine readRule_restricted fun t inside x inX => ?_
          rw [List.mem_singleton.mp inside, unknowns_supplementaryRow, boundAt_succ goalFound] at inX
          simp only [goalUnknowns, List.mem_append] at inX
          rcases inX with inBound | inInput | inOutput
          · exact .inl ⟨_, List.mem_cons_self, by rw [unknowns_supplementaryRow]; exact inBound⟩
          · exact .inl ⟨answerRow relation input output, List.mem_cons_of_mem _ List.mem_cons_self, by
              simp [answerRow, inInput]⟩
          · exact .inl ⟨answerRow relation input output, List.mem_cons_of_mem _ List.mem_cons_self, by
              simp [answerRow, inOutput]⟩

/-- **Every rule of a run of moded clauses is range-restricted.** -/
theorem runRules_restricted (moded : ∀ c ∈ program, Moded c) (moves : List ℕ) :
    ∀ ρ ∈ runRules program moves, ρ.RangeRestrictedWith := by
  intro ρ inside
  simp only [runRules, List.mem_append, List.mem_map] at inside
  rcases inside with (⟨relation, -, rfl⟩ | ⟨relation, -, rfl⟩) | inDemand
  · exact readRule_restricted_one fun x inX => by simpa [demandRow, currentRow] using inX
  · exact commitRule_restricted relation
  · exact demandRules_restricted moded ρ inDemand

theorem runRules_plain (moves : List ℕ) :
    ∀ ρ ∈ runRules program moves, ρ.rule.collect = [] ∧ ρ.rule.body.checks = [] := by
  intro ρ inside
  simp only [runRules, List.mem_append, List.mem_map] at inside
  rcases inside with (⟨relation, -, rfl⟩ | ⟨relation, -, rfl⟩) | inDemand
  · exact ⟨rfl, rfl⟩
  · exact ⟨rfl, rfl⟩
  · obtain ⟨read, produce, conditions, rfl⟩ := demandRules_read inDemand
    exact ⟨rfl, rfl⟩

variable (R program) in
/-- **The relations on rows and the runs of their rules, on the transform step.** -/
def stepCorrespondence {O : Type} [DecidableEq O] [Infinite O] (moded : ∀ c ∈ program, Moded c) (moves : List ℕ) :
    OperationalCorrespondence (equalityGSLT Expr (Moves R program moves))
      (programSystem O (specialized rows (relationGraph R) {ρ | ρ ∈ runRules program moves})) :=
  (bagCorrespondence R program moves).comp (relationCorrespondence
    (fun ρ inside => (runRules_plain moves ρ inside).1)
    (fun ρ inside => by rw [(runRules_plain moves ρ inside).2]; rfl)
    (runRules_restricted moded moves))

end Mettapedia.GSLT.Compilation.Uniform.DemandTransformation

#print axioms Mettapedia.GSLT.Compilation.Uniform.DemandTransformation.answers_reachable
#print axioms Mettapedia.GSLT.Compilation.Uniform.DemandTransformation.fired_sound
#print axioms Mettapedia.GSLT.Compilation.Uniform.DemandTransformation.stepCorrespondence
