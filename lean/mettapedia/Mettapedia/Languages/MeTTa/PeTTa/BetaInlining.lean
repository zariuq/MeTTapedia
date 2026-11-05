import Mettapedia.Languages.MeTTa.PeTTa.Eval
import Mettapedia.Languages.MeTTa.TypeSchemeActivation

/-!
# Beta inlining of one-equation calls

A call `(f $a1 .. $an)` of a function with exactly one equation
`(= (f $x1 .. $xn) body)` runs, in the machine of `Eval`, by evaluating its
arguments, matching the equation's head against their values and running `body`
under the parameters' bindings, above one empty sequencing frame per argument and
one for the selected equation (`call_reaches_body`).

**Beta inlining.** Replace each parameter of `body` by its argument variable and run
the result in the caller's environment and continuation. The two runs complete with
the same store, the same answers in the same order and multiplicity, and the same
remaining input and output (`beta_complete`). They fault together, for the same
reason, with the same store and input/output at the fault (`beta_fault`). The
premises are `Inlinable`:

* `f` has exactly one equation; its head arguments are distinct variables, and the
  body mentions no other variable;
* the call supplies one variable per parameter, each bound in the caller's
  environment;
* `f` is not a primitive, an I/O operation or control syntax.

Recursion is allowed: one unfolding leaves an inner call of `f` a call. A
declaration of `f` is allowed: in this machine a declaration selects only literal
`Atom` demand, and a variable argument has the same value either way. The machine
fixes the equations when the program is loaded, so no run can add a second one.

**How.** One step of the callee's body under its bindings is one step of the renamed
body under the caller's (`simulation`), for configurations related by `Rel`: the
controls of the body and of its renaming (`RelControl`, `RelFrame`), with nested
calls, answers and faults shared. Binders in the body only test parameters, bound on
both sides (`matchBinding_rename`, `selectCase_rename`), and renaming preserves the
recognition of control syntax (`controlForm_rename`). A run beneath caller frames is
the run of the computation followed by the run of its callers
(`runs_split_frames`, `runs_join_frames`), and empty sequencing frames pass answers
through (`runs_pop_empty_sequences`).

Companion modules: `BetaInliningControls` (positive and negative controls, and the
premises met by a search round's function), `BetaInliningSuperpose` (several equations as
an ordered superposition; an argument expression through a binding), `BetaInliningGuard`
(a head pattern as a case), `BetaInliningTyped` (a typed call is a guarded protocol, not
its body) and `BetaInliningRound` (the round's call, solution by solution and over a
whole round, against `NestedQueryEffects`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.BetaInlining

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst matchAtom)
open SpaceSemantics (Program Cases)
open Effects (State Fault)
open Eval
open DeclarativeSpec (Transition Runs controlForm)
open Mettapedia.Languages.MeTTa.TypeSchemeActivation (rename freeVars)

/-! ## Renaming the variables of code -/

/-- The variables of `e` are among `vars`. -/
def Within (vars : List String) (e : Atom) : Prop := ∀ x ∈ freeVars e, x ∈ vars

theorem within_expression {vars : List String} {items : List Atom} :
    Within vars (.expression items) ↔ ∀ item ∈ items, Within vars item := by
  simp only [Within, freeVars, List.mem_flatMap]
  constructor
  · intro h item member x hx
    exact h x ⟨item, member, hx⟩
  · rintro h x ⟨item, member, hx⟩
    exact h item member x hx

/-- The callee's environment and the caller's give each variable of `vars` the same
bound value, the caller reading it under its renamed name. -/
def Agree (callee caller : Subst) (names : String → String) (vars : List String) : Prop :=
  ∀ x ∈ vars, ∃ w, callee.lookup x = some w ∧ caller.lookup (names x) = some w

@[simp] theorem rename_expression (names : String → String) (items : List Atom) :
    rename names (.expression items) = .expression (items.map (rename names)) := by
  simp [rename]

@[simp] theorem rename_symbol (names : String → String) (name : String) :
    rename names (.symbol name) = .symbol name := by simp [rename]

@[simp] theorem rename_var (names : String → String) (name : String) :
    rename names (.var name) = .var (names name) := by simp [rename]

@[simp] theorem rename_grounded (names : String → String)
    (value : Mettapedia.Languages.MeTTa.OSLFCore.GroundedValue) :
    rename names (.grounded value) = .grounded value := by simp [rename]

theorem applySubstList_eq_map (bindings : Subst) (items : List Atom) :
    applySubst.applySubstList bindings items = items.map (applySubst bindings) := by
  induction items with
  | nil => rfl
  | cons head tail ih => simp [applySubst.applySubstList, ih]

/-- Instantiating renamed code in the caller's environment instantiates the original
code in the callee's. -/
theorem applySubst_rename {callee caller : Subst} {names : String → String}
    {vars : List String} (agree : Agree callee caller names vars) :
    ∀ (e : Atom), Within vars e → applySubst caller (rename names e) = applySubst callee e := by
  intro e
  induction e using Atom.rec (motive_2 := fun items =>
    (∀ item ∈ items, Within vars item) →
      items.map (fun item => applySubst caller (rename names item)) =
        items.map (applySubst callee)) with
  | symbol _ => intro _; simp [applySubst]
  | grounded _ => intro _; simp [applySubst]
  | var x =>
      intro within
      obtain ⟨w, calleeValue, callerValue⟩ := agree x (within x (by simp [freeVars]))
      simp [applySubst, calleeValue, callerValue]
  | expression items ih =>
      intro within
      have each := ih (within_expression.mp within)
      simp only [rename_expression, applySubst, applySubstList_eq_map, List.map_map]
      exact congrArg Atom.expression each
  | nil => rfl
  | cons head tail ihHead ihTail =>
      rename_i within
      simp only [List.map_cons]
      rw [ihHead (within head List.mem_cons_self),
        ihTail (fun item member => within item (List.mem_cons_of_mem _ member))]

/-! ## Matching renamed patterns whose variables are all bound -/

/-- Two match outcomes with the same verdict: both succeed and add no binding, or
both fail. -/
def SameVerdict (callee caller : Subst) (one two : Option Subst) : Prop :=
  (one = some callee ∧ two = some caller) ∨ (one = none ∧ two = none)

theorem sameVerdict_ite {callee caller : Subst} (condition : Prop) [Decidable condition] :
    SameVerdict callee caller (if condition then some callee else none)
      (if condition then some caller else none) := by
  by_cases holds : condition <;> simp [SameVerdict, holds]

theorem matchAtom_rename {callee caller : Subst} {names : String → String}
    {vars : List String} (agree : Agree callee caller names vars) :
    ∀ (p : Atom), Within vars p → ∀ (v : Atom),
      SameVerdict callee caller (matchAtom callee p v) (matchAtom caller (rename names p) v) := by
  intro p
  induction p using Atom.rec (motive_2 := fun items =>
    (∀ item ∈ items, Within vars item) → ∀ values,
      SameVerdict callee caller (matchAtom.matchAtomList callee items values)
        (matchAtom.matchAtomList caller (items.map (rename names)) values)) with
  | symbol s =>
      intro _ v
      cases v with
      | symbol t => simp only [rename_symbol, matchAtom]; exact sameVerdict_ite _
      | var _ | grounded _ | expression _ => simp [matchAtom, SameVerdict]
  | grounded g =>
      intro _ v
      cases v with
      | grounded h => simp only [rename_grounded, matchAtom]; exact sameVerdict_ite _
      | var _ | symbol _ | expression _ => simp [matchAtom, SameVerdict]
  | var x =>
      intro within v
      obtain ⟨w, calleeValue, callerValue⟩ := agree x (within x (by simp [freeVars]))
      simp only [rename_var, matchAtom, calleeValue, callerValue]
      exact sameVerdict_ite _
  | expression items ih =>
      intro within v
      have each := ih (within_expression.mp within)
      cases v with
      | expression values =>
          simp only [rename_expression, matchAtom]
          exact each values
      | var _ | symbol _ | grounded _ => simp [matchAtom, SameVerdict]
  | nil =>
      rename_i _ values
      cases values <;> simp [matchAtom.matchAtomList, SameVerdict]
  | cons head tail ihHead ihTail =>
      rename_i within values
      cases values with
      | nil => simp [matchAtom.matchAtomList, SameVerdict]
      | cons value rest =>
          simp only [List.map_cons, matchAtom.matchAtomList]
          rcases ihHead (within head List.mem_cons_self) value with ⟨one, two⟩ | ⟨one, two⟩
          · rw [one, two]
            exact ihTail (fun item member => within item (List.mem_cons_of_mem _ member)) rest
          · rw [one, two]
            simp [SameVerdict]

theorem rename_eq_symbol (names : String → String) (a : Atom) (s : String) :
    rename names a = .symbol s ↔ a = .symbol s := by
  cases a <;> simp

theorem not_cons_rename (names : String → String) {items : List Atom}
    (notCons : ∀ first rest, items ≠ [.symbol "cons", first, rest]) :
    ∀ first rest, items.map (rename names) ≠ [.symbol "cons", first, rest] := by
  intro first rest same
  rcases items with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, tail⟩⟩⟩⟩ <;> simp at same
  exact notCons b c (by rw [(rename_eq_symbol names a "cons").mp same.1])

theorem matchValue_atomic (bindings : Subst) (p v : Atom)
    (notExpression : ∀ items, p ≠ .expression items) :
    SpaceSemantics.matchValue bindings p v = matchAtom bindings p v := by
  cases p with
  | expression items => exact absurd rfl (notExpression items)
  | var _ | symbol _ | grounded _ => rw [SpaceSemantics.matchValue.eq_def]

theorem matchValue_cons_cons (bindings : Subst) (first rest head : Atom) (tail : List Atom) :
    SpaceSemantics.matchValue bindings (.expression [.symbol "cons", first, rest])
        (.expression (head :: tail)) =
      (SpaceSemantics.matchValue bindings first head).bind
        (fun bound => SpaceSemantics.matchValue bound rest (.expression tail)) := by
  rw [SpaceSemantics.matchValue.eq_def]
  rfl

theorem matchValue_cons_other (bindings : Subst) (first rest v : Atom)
    (other : ∀ head tail, v ≠ .expression (head :: tail)) :
    SpaceSemantics.matchValue bindings (.expression [.symbol "cons", first, rest]) v = none := by
  rw [SpaceSemantics.matchValue.eq_def]
  cases v with
  | expression values =>
      cases values with
      | nil => rfl
      | cons head tail => exact absurd rfl (other head tail)
  | var _ | symbol _ | grounded _ => rfl

theorem matchValue_expression_nonexpression (bindings : Subst) (items : List Atom) (v : Atom)
    (notExpression : ∀ values, v ≠ .expression values)
    (notCons : ∀ first rest, items ≠ [.symbol "cons", first, rest]) :
    SpaceSemantics.matchValue bindings (.expression items) v = none := by
  rw [SpaceSemantics.matchValue.eq_def]
  cases v with
  | expression values => exact absurd rfl (notExpression values)
  | var _ | symbol _ | grounded _ =>
      split <;> simp_all

theorem matchValue_rename {callee caller : Subst} {names : String → String}
    {vars : List String} (agree : Agree callee caller names vars) :
    ∀ (p : Atom), Within vars p → ∀ (v : Atom),
      SameVerdict callee caller (SpaceSemantics.matchValue callee p v)
        (SpaceSemantics.matchValue caller (rename names p) v) := by
  intro p
  induction p using Atom.rec (motive_2 := fun items =>
    (∀ item ∈ items, Within vars item) →
      (∀ item ∈ items, ∀ v, SameVerdict callee caller (SpaceSemantics.matchValue callee item v)
          (SpaceSemantics.matchValue caller (rename names item) v)) ∧
      ∀ values, SameVerdict callee caller
        (SpaceSemantics.matchValue.matchValues callee items values)
        (SpaceSemantics.matchValue.matchValues caller (items.map (rename names)) values)) with
  | symbol s =>
      intro within v
      rw [matchValue_atomic _ _ _ (by simp), rename_symbol,
        matchValue_atomic _ _ _ (by simp)]
      simpa only [rename_symbol] using matchAtom_rename agree (.symbol s) within v
  | grounded g =>
      intro within v
      rw [matchValue_atomic _ _ _ (by simp), rename_grounded,
        matchValue_atomic _ _ _ (by simp)]
      simpa only [rename_grounded] using matchAtom_rename agree (.grounded g) within v
  | var x =>
      intro within v
      rw [matchValue_atomic _ _ _ (by simp), rename_var,
        matchValue_atomic _ _ _ (by simp)]
      simpa only [rename_var] using matchAtom_rename agree (.var x) within v
  | expression items ih =>
      intro within v
      obtain ⟨eachItem, eachList⟩ := ih (within_expression.mp within)
      by_cases isCons : ∃ first rest, items = [.symbol "cons", first, rest]
      · obtain ⟨first, rest, rfl⟩ := isCons
        have firstVerdict := eachItem first (by simp)
        have restVerdict := eachItem rest (by simp)
        simp only [rename_expression, List.map_cons, List.map_nil, rename_symbol]
        by_cases shape : ∃ head tail, v = .expression (head :: tail)
        · obtain ⟨head, tail, rfl⟩ := shape
          rw [matchValue_cons_cons, matchValue_cons_cons]
          rcases firstVerdict head with ⟨one, two⟩ | ⟨one, two⟩
          · rw [one, two]
            exact restVerdict (.expression tail)
          · rw [one, two]
            simp [SameVerdict]
        · have other : ∀ head tail, v ≠ .expression (head :: tail) :=
            fun head tail same => shape ⟨head, tail, same⟩
          rw [matchValue_cons_other _ _ _ _ other, matchValue_cons_other _ _ _ _ other]
          simp [SameVerdict]
      · have notCons : ∀ first rest, items ≠ [.symbol "cons", first, rest] := by
          intro first rest same
          exact isCons ⟨first, rest, same⟩
        have renamedNotCons := not_cons_rename names notCons
        simp only [rename_expression]
        cases v with
        | expression values =>
            rw [SpaceSemantics.matchValue_expression_of_not_cons _ _ _ notCons,
              SpaceSemantics.matchValue_expression_of_not_cons _ _ _ renamedNotCons]
            exact eachList values
        | var _ | symbol _ | grounded _ =>
            rw [matchValue_expression_nonexpression _ _ _ (by simp) notCons,
              matchValue_expression_nonexpression _ _ _ (by simp) renamedNotCons]
            simp [SameVerdict]
  | nil =>
      refine ⟨by simp, fun values => ?_⟩
      cases values <;> simp [SpaceSemantics.matchValue.matchValues, SameVerdict]
  | cons head tail ihHead ihTail =>
      rename_i within
      have headWithin := within head List.mem_cons_self
      have tailWithin : ∀ item ∈ tail, Within vars item :=
        fun item member => within item (List.mem_cons_of_mem _ member)
      obtain ⟨tailItems, tailList⟩ := ihTail tailWithin
      refine ⟨?_, fun values => ?_⟩
      · intro item member v
        rcases List.mem_cons.mp member with rfl | member
        · exact ihHead headWithin v
        · exact tailItems item member v
      · cases values with
        | nil => simp [SpaceSemantics.matchValue.matchValues, SameVerdict]
        | cons value rest =>
            simp only [List.map_cons, SpaceSemantics.matchValue.matchValues, bind, Option.bind]
            rcases ihHead headWithin value with ⟨one, two⟩ | ⟨one, two⟩
            · rw [one, two]
              exact tailList rest
            · rw [one, two]
              simp [SameVerdict]

theorem not_quote_rename (names : String → String) {p : Atom}
    (notQuote : ∀ literal, p ≠ .expression [.symbol "quote", literal]) :
    ∀ literal, rename names p ≠ .expression [.symbol "quote", literal] := by
  intro literal same
  cases p with
  | var _ | symbol _ | grounded _ => simp at same
  | expression items =>
      simp only [rename_expression, Atom.expression.injEq] at same
      rcases items with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩ <;> simp at same
      exact notQuote b (by rw [(rename_eq_symbol names a "quote").mp same.1])

theorem matchBinding_rename {callee caller : Subst} {names : String → String}
    {vars : List String} (agree : Agree callee caller names vars)
    (p : Atom) (within : Within vars p) (v : Atom) :
    SameVerdict callee caller (SpaceSemantics.matchBinding callee p v)
      (SpaceSemantics.matchBinding caller (rename names p) v) := by
  by_cases isQuote : ∃ literal, p = .expression [.symbol "quote", literal]
  · obtain ⟨literal, rfl⟩ := isQuote
    simp only [rename_expression, List.map_cons, List.map_nil, rename_symbol,
      SpaceSemantics.matchBinding_quote]
    exact matchAtom_rename agree literal
      ((within_expression.mp within) literal (by simp)) v
  · have notQuote : ∀ literal, p ≠ .expression [.symbol "quote", literal] :=
      fun literal same => isQuote ⟨literal, same⟩
    rw [SpaceSemantics.matchBinding_ordinary _ _ _ notQuote,
      SpaceSemantics.matchBinding_ordinary _ _ _ (not_quote_rename names notQuote)]
    exact matchValue_rename agree p within v

/-- Case rows with both pattern and body renamed. -/
def renameCases (names : String → String) (cases : Cases) : Cases :=
  cases.map fun row => (rename names row.1, rename names row.2)

theorem selectCase_rename {callee caller : Subst} {names : String → String}
    {vars : List String} (agree : Agree callee caller names vars) (v : Atom) :
    ∀ (cases : Cases), (∀ row ∈ cases, Within vars row.1 ∧ Within vars row.2) →
      (SpaceSemantics.selectCase callee v cases = none ∧
          SpaceSemantics.selectCase caller v (renameCases names cases) = none) ∨
        ∃ body, Within vars body ∧
          SpaceSemantics.selectCase callee v cases = some (callee, body) ∧
          SpaceSemantics.selectCase caller v (renameCases names cases) =
            some (caller, rename names body)
  | [], _ => .inl ⟨rfl, rfl⟩
  | (pattern, body) :: rest, within => by
      have rowWithin := within (pattern, body) List.mem_cons_self
      simp only [renameCases, List.map_cons, SpaceSemantics.selectCase]
      rcases matchValue_rename agree pattern rowWithin.1 v with ⟨one, two⟩ | ⟨one, two⟩
      · rw [one, two]
        exact .inr ⟨body, rowWithin.2, rfl, rfl⟩
      · rw [one, two]
        exact selectCase_rename agree v rest
          (fun row member => within row (List.mem_cons_of_mem _ member))

theorem readCases_rename (names : String → String) :
    ∀ (rows : List Atom),
      Eval.readCases (rows.map (rename names)) = (Eval.readCases rows).map (renameCases names)
  | [] => rfl
  | row :: rest => by
      have ih := readCases_rename names rest
      cases row with
      | var _ | symbol _ | grounded _ => simp [Eval.readCases]
      | expression items =>
          rcases items with _ | ⟨a, _ | ⟨b, _ | ⟨c, more⟩⟩⟩
          · simp [Eval.readCases]
          · simp [Eval.readCases]
          · simp only [List.map_cons, rename_expression, List.map_nil, Eval.readCases, ih]
            cases Eval.readCases rest <;> simp [renameCases]
          · simp [Eval.readCases]

theorem readCases_within {vars : List String} :
    ∀ {rows : List Atom} {cases : Cases}, Eval.readCases rows = some cases →
      (∀ row ∈ rows, Within vars row) → ∀ row ∈ cases, Within vars row.1 ∧ Within vars row.2
  | [], cases, parsed, _ => by
      simp only [Eval.readCases, Option.some.injEq] at parsed
      subst parsed
      simp
  | row :: rest, cases, parsed, within => by
      cases row with
      | var _ | symbol _ | grounded _ => simp [Eval.readCases] at parsed
      | expression items =>
          rcases items with _ | ⟨a, _ | ⟨b, _ | ⟨c, more⟩⟩⟩
          · simp [Eval.readCases] at parsed
          · simp [Eval.readCases] at parsed
          · simp only [Eval.readCases] at parsed
            cases restParsed : Eval.readCases rest with
            | none => simp [restParsed] at parsed
            | some restCases =>
                simp only [restParsed, Option.map_eq_map, Option.map_some,
                  Option.some.injEq] at parsed
                subst parsed
                have rowWithin := within_expression.mp (within _ List.mem_cons_self)
                intro case member
                rcases List.mem_cons.mp member with rfl | member
                · exact ⟨rowWithin a (by simp), rowWithin b (by simp)⟩
                · exact readCases_within restParsed
                    (fun row member => within row (List.mem_cons_of_mem _ member)) case member
          · simp [Eval.readCases] at parsed

theorem nestedLets_rename (names : String → String) :
    ∀ (pairs : List Atom) (body : Atom),
      Eval.nestedLets (pairs.map (rename names)) (rename names body) =
        (Eval.nestedLets pairs body).map (rename names)
  | [], body => rfl
  | pair :: rest, body => by
      have ih := nestedLets_rename names rest body
      cases pair with
      | var _ | symbol _ | grounded _ => simp [Eval.nestedLets]
      | expression items =>
          rcases items with _ | ⟨a, _ | ⟨b, _ | ⟨c, more⟩⟩⟩
          · simp [Eval.nestedLets]
          · simp [Eval.nestedLets]
          · simp only [List.map_cons, rename_expression, List.map_nil, Eval.nestedLets, ih]
            cases Eval.nestedLets rest body <;> simp
          · simp [Eval.nestedLets]

theorem nestedLets_within {vars : List String} :
    ∀ {pairs : List Atom} {body nested : Atom}, Eval.nestedLets pairs body = some nested →
      (∀ pair ∈ pairs, Within vars pair) → Within vars body → Within vars nested
  | [], body, nested, expanded, _, bodyWithin => by
      simp only [Eval.nestedLets, Option.some.injEq] at expanded
      subst expanded
      exact bodyWithin
  | pair :: rest, body, nested, expanded, within, bodyWithin => by
      cases pair with
      | var _ | symbol _ | grounded _ => simp [Eval.nestedLets] at expanded
      | expression items =>
          rcases items with _ | ⟨a, _ | ⟨b, _ | ⟨c, more⟩⟩⟩
          · simp [Eval.nestedLets] at expanded
          · simp [Eval.nestedLets] at expanded
          · simp only [Eval.nestedLets] at expanded
            cases restExpanded : Eval.nestedLets rest body with
            | none => simp [restExpanded] at expanded
            | some inner =>
                simp only [restExpanded, Option.map_eq_map, Option.map_some,
                  Option.some.injEq] at expanded
                subst expanded
                have pairWithin := within_expression.mp (within _ List.mem_cons_self)
                have innerWithin := nestedLets_within restExpanded
                  (fun pair member => within pair (List.mem_cons_of_mem _ member)) bodyWithin
                apply within_expression.mpr
                intro item member
                simp only [List.mem_cons, List.not_mem_nil, or_false] at member
                rcases member with rfl | rfl | rfl | rfl
                · intro x hx; simp [freeVars] at hx
                · exact pairWithin _ (by simp)
                · exact pairWithin _ (by simp)
                · exact innerWithin
          · simp [Eval.nestedLets] at expanded

/-! ## Control syntax is recognized on the shape of code -/

def isExpr : Atom → Bool
  | .expression _ => true
  | _ => false

def shape : Atom → Bool
  | .expression [.symbol s, _, _, _] => s == "let" || s == "if" || s == "match"
  | .expression [.symbol s, a, b] => (s == "let*" && isExpr a) || (s == "case" && isExpr b)
  | .expression [.symbol s, a] => s == "collapse" || (s == "superpose" && isExpr a) || s == "quote"
  | .expression [.symbol s] => s == "empty"
  | _ => false

set_option maxHeartbeats 1000000 in
theorem controlForm_eq_shape (e : Atom) : controlForm e = shape e := by
  cases e with
  | var _ | symbol _ | grounded _ => rfl
  | expression items =>
      rcases items with _ | ⟨h, _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, rest⟩⟩⟩⟩⟩
      · rfl
      · cases h with
        | symbol s =>
            unfold controlForm shape
            split <;> simp_all
        | _ => rfl
      · cases h with
        | symbol s =>
            unfold controlForm shape
            cases a <;> split <;> simp_all [isExpr]
        | _ => rfl
      · cases h with
        | symbol s =>
            unfold controlForm shape
            cases a <;> cases b <;> split <;> simp_all [isExpr]
        | _ => rfl
      · cases h with
        | symbol s =>
            unfold controlForm shape
            split
            all_goals (try simp_all)
            all_goals
              rename_i notLet notIf notMatch
              exact ⟨⟨fun same => notLet a b c same rfl rfl rfl, fun same => notIf a b c same rfl rfl rfl⟩,
                fun same => notMatch a b c same rfl rfl rfl⟩
        | _ => rfl
      · cases h with
        | symbol s =>
            unfold controlForm shape
            split <;> simp_all
        | _ => rfl

theorem isExpr_rename (names : String → String) (a : Atom) : isExpr (rename names a) = isExpr a := by
  cases a <;> simp [isExpr]

theorem shape_rename (names : String → String) (e : Atom) : shape (rename names e) = shape e := by
  cases e with
  | var _ | symbol _ | grounded _ => simp [shape]
  | expression items =>
      rcases items with _ | ⟨h, _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, rest⟩⟩⟩⟩⟩
      · simp [shape]
      all_goals (cases h <;> simp [shape, isExpr_rename])

theorem controlForm_rename (names : String → String) (e : Atom) :
    controlForm (rename names e) = controlForm e := by
  rw [controlForm_eq_shape, controlForm_eq_shape, shape_rename]

theorem unheaded_rename (names : String → String) {items : List Atom}
    (unheaded : ∀ head arguments, items ≠ .symbol head :: arguments) :
    ∀ head arguments, items.map (rename names) ≠ .symbol head :: arguments := by
  intro head arguments same
  cases items with
  | nil => simp at same
  | cons first rest =>
      simp only [List.map_cons, List.cons.injEq] at same
      exact unheaded head rest (by rw [(rename_eq_symbol names first head).mp same.1])

/-! ## The two runs, step by step

`RelControl` relates a control of the callee's body, under the callee's environment, to
the same control of the renamed body under the caller's environment. Controls of nested
calls, answers and faults are shared by both runs (`same`). -/

section Simulation

variable (callee caller : Subst) (names : String → String) (vars : List String)

mutual
inductive RelControl : Control → Control → Prop
  | same (control : Control) : RelControl control control
  | evaluate (e : Atom) (within : Within vars e) :
      RelControl (.evaluate callee e) (.evaluate caller (rename names e))
  | arguments (target : Target) (remaining values : List Atom) (index : Nat)
      (within : ∀ a ∈ remaining, Within vars a) :
      RelControl (.arguments callee target remaining values index)
        (.arguments caller target (remaining.map (rename names)) values index)
  | sequence {first second : List Control} (answers : List Atom)
      (related : RelControls first second) :
      RelControl (.sequence first answers) (.sequence second answers)

inductive RelControls : List Control → List Control → Prop
  | nil : RelControls [] []
  | cons {one two : Control} {first second : List Control} :
      RelControl one two → RelControls first second → RelControls (one :: first) (two :: second)
end

inductive RelFrame : Frame → Frame → Prop
  | same (frame : Frame) : RelFrame frame frame
  | bind (pattern body : Atom) (patternWithin : Within vars pattern)
      (bodyWithin : Within vars body) :
      RelFrame (.bind callee pattern body) (.bind caller (rename names pattern) (rename names body))
  | select (cases : Cases) (within : ∀ row ∈ cases, Within vars row.1 ∧ Within vars row.2) :
      RelFrame (.select callee cases) (.select caller (renameCases names cases))
  | branch (yes no : Atom) (yesWithin : Within vars yes) (noWithin : Within vars no) :
      RelFrame (.branch callee yes no) (.branch caller (rename names yes) (rename names no))
  | argument (target : Target) (remaining values : List Atom) (index : Nat)
      (within : ∀ a ∈ remaining, Within vars a) :
      RelFrame (.argument callee target remaining values index)
        (.argument caller target (remaining.map (rename names)) values index)
  | sequence {first second : List Control} (answers : List Atom)
      (related : RelControls callee caller names vars first second) :
      RelFrame (.sequence first answers) (.sequence second answers)
  | query (pattern body : Atom) (patternWithin : Within vars pattern)
      (bodyWithin : Within vars body) :
      RelFrame (.query callee pattern body) (.query caller (rename names pattern) (rename names body))

/-- Two configurations that share the store and input/output and whose controls and
frames are related. -/
structure Rel (one two : Configuration) : Prop where
  state : one.state = two.state
  input : one.input = two.input
  output : one.output = two.output
  control : RelControl callee caller names vars one.control two.control
  frames : List.Forall₂ (RelFrame callee caller names vars) one.frames two.frames

theorem relControls_refl : ∀ (controls : List Control),
    RelControls callee caller names vars controls controls
  | [] => .nil
  | control :: rest => .cons (.same control) (relControls_refl rest)

theorem relControls_evaluate : ∀ (items : List Atom), (∀ item ∈ items, Within vars item) →
    RelControls callee caller names vars (items.map (.evaluate callee))
      ((items.map (rename names)).map (.evaluate caller))
  | [], _ => .nil
  | item :: rest, within =>
      .cons (.evaluate item (within item List.mem_cons_self))
        (relControls_evaluate rest (fun other member => within other (List.mem_cons_of_mem _ member)))

theorem relControls_arguments (target : Target) (pending values : List Atom) (index : Nat)
    (within : ∀ a ∈ pending, Within vars a) : ∀ (answers : List Atom),
    RelControls callee caller names vars
      (answers.map fun value => .arguments callee target pending (values ++ [value]) (index + 1))
      (answers.map fun value =>
        .arguments caller target (pending.map (rename names)) (values ++ [value]) (index + 1))
  | [] => .nil
  | value :: rest =>
      .cons (.arguments target pending (values ++ [value]) (index + 1) within)
        (relControls_arguments target pending values index within rest)

theorem relControls_branch (yes no : Atom) (yesWithin : Within vars yes)
    (noWithin : Within vars no) : ∀ (answers : List Atom),
    RelControls callee caller names vars
      (answers.map fun value =>
        .evaluate callee (if value == Effects.boolean true then yes else no))
      (answers.map fun value =>
        .evaluate caller (if value == Effects.boolean true then rename names yes else rename names no))
  | [] => .nil
  | value :: rest => by
      refine .cons ?_ (relControls_branch yes no yesWithin noWithin rest)
      by_cases chosen : (value == Effects.boolean true) = true
      · simp only [chosen, ↓reduceIte]
        exact .evaluate yes yesWithin
      · simp only [chosen, Bool.false_eq_true, ↓reduceIte]
        exact .evaluate no noWithin

variable {callee caller names vars}

theorem relControls_bind (agree : Agree callee caller names vars) (pattern body : Atom)
    (patternWithin : Within vars pattern) (bodyWithin : Within vars body) :
    ∀ (answers : List Atom),
    RelControls callee caller names vars
      (answers.filterMap fun value =>
        (SpaceSemantics.matchBinding callee pattern value).map fun bound => .evaluate bound body)
      (answers.filterMap fun value =>
        (SpaceSemantics.matchBinding caller (rename names pattern) value).map
          fun bound => .evaluate bound (rename names body))
  | [] => .nil
  | value :: rest => by
      have tail := relControls_bind agree pattern body patternWithin bodyWithin rest
      rcases matchBinding_rename agree pattern patternWithin value with ⟨one, two⟩ | ⟨one, two⟩
      · simp only [List.filterMap_cons, one, two, Option.map_some]
        exact .cons (.evaluate body bodyWithin) tail
      · simp only [List.filterMap_cons, one, two, Option.map_none]
        exact tail

theorem relControls_select (agree : Agree callee caller names vars) (cases : Cases)
    (within : ∀ row ∈ cases, Within vars row.1 ∧ Within vars row.2) :
    ∀ (answers : List Atom),
    RelControls callee caller names vars
      (answers.filterMap fun value =>
        (SpaceSemantics.selectCase callee value cases).map fun (bound, body) => .evaluate bound body)
      (answers.filterMap fun value =>
        (SpaceSemantics.selectCase caller value (renameCases names cases)).map
          fun (bound, body) => .evaluate bound body)
  | [] => .nil
  | value :: rest => by
      have tail := relControls_select agree cases within rest
      rcases selectCase_rename agree value cases within with ⟨one, two⟩ | ⟨body, bodyWithin, one, two⟩
      · simp only [List.filterMap_cons, one, two, Option.map_none]
        exact tail
      · simp only [List.filterMap_cons, one, two, Option.map_some]
        exact .cons (.evaluate body bodyWithin) tail

theorem relControls_append : {first second : List Control} → {third fourth : List Control} →
    RelControls callee caller names vars first second →
    RelControls callee caller names vars third fourth →
    RelControls callee caller names vars (first ++ third) (second ++ fourth)
  | _, _, _, _, .nil, rest => rest
  | _, _, _, _, .cons head tail, rest => .cons head (relControls_append tail rest)

theorem relControls_queryBodies (agree : Agree callee caller names vars) (pattern body : Atom)
    (patternWithin : Within vars pattern) (bodyWithin : Within vars body) :
    ∀ (rows : List Atom),
    RelControls callee caller names vars (queryBodies callee rows pattern body)
      (queryBodies caller rows (rename names pattern) (rename names body))
  | [] => .nil
  | row :: rest => by
      have tail := relControls_queryBodies agree pattern body patternWithin bodyWithin rest
      rcases matchValue_rename agree pattern patternWithin row with ⟨one, two⟩ | ⟨one, two⟩
      · simp only [queryBodies, List.filterMap_cons, one, two, Option.map_some] at tail ⊢
        exact .cons (.evaluate body bodyWithin) tail
      · simp only [queryBodies, List.filterMap_cons, one, two, Option.map_none] at tail ⊢
        exact tail

/-- The alternatives of a query in the callee's body and in the renamed body read
the same rows and run related bodies. -/
theorem relControls_query (agree : Agree callee caller names vars) (state : State)
    (pattern body : Atom) (patternWithin : Within vars pattern) (bodyWithin : Within vars body) :
    ∀ (answers : List Atom),
    RelControls callee caller names vars
      (answers.flatMap fun space => queryAlternatives state callee space pattern body)
      (answers.flatMap fun space =>
        queryAlternatives state caller space (rename names pattern) (rename names body))
  | [] => .nil
  | space :: rest => by
      have tail := relControls_query agree state pattern body patternWithin bodyWithin rest
      simp only [List.flatMap_cons]
      apply relControls_append _ tail
      unfold queryAlternatives
      split
      · exact relControls_queryBodies agree pattern body patternWithin bodyWithin _
      · exact .cons (.same _) .nil

/-- **One step of the callee's body is one step of the renamed body.** -/
theorem simulation (agree : Agree callee caller names vars) {program : Program}
    {one target two : Configuration} (transition : Transition program one target)
    (related : Rel callee caller names vars one two) :
    ∃ next, Transition program two next ∧ Rel callee caller names vars target next := by
  obtain ⟨st2, k2, fs2, in2, out2⟩ := two
  obtain ⟨hs, hi, ho, hc, hf⟩ := related
  simp only at hs hi ho hc hf
  cases transition with
  | sequence_done control =>
      rw [control] at hc
      cases hc with
      | same => exact ⟨_, .sequence_done rfl, ⟨hs, hi, ho, .same _, hf⟩⟩
      | sequence _ related =>
          cases related
          exact ⟨_, .sequence_done rfl, ⟨hs, hi, ho, .same _, hf⟩⟩
  | sequence_enter control =>
      rw [control] at hc
      cases hc with
      | same => exact ⟨_, .sequence_enter rfl, ⟨hs, hi, ho, .same _, .cons (.same _) hf⟩⟩
      | sequence _ related =>
          cases related with
          | cons head tail =>
              exact ⟨_, .sequence_enter rfl, ⟨hs, hi, ho, head, .cons (.sequence _ tail) hf⟩⟩
  | construct control =>
      rw [control] at hc
      cases hc with
      | same => exact ⟨_, .construct rfl, ⟨hs, hi, ho, .same _, hf⟩⟩
      | arguments _ _ _ _ _ => exact ⟨_, .construct rfl, ⟨hs, hi, ho, .same _, hf⟩⟩
  | read_end control input =>
      rw [control] at hc
      cases hc with
      | same => exact ⟨_, .read_end rfl (hi ▸ input), ⟨hs, hi, ho, .same _, hf⟩⟩
      | arguments _ _ _ _ _ => exact ⟨_, .read_end rfl (hi ▸ input), ⟨hs, hi, ho, .same _, hf⟩⟩
  | read_line control input =>
      rw [control] at hc
      have input2 : in2 = _ := hi ▸ input
      cases hc with
      | same => exact ⟨_, .read_line rfl input2, ⟨hs, rfl, ho, .same _, hf⟩⟩
      | arguments _ _ _ _ _ => exact ⟨_, .read_line rfl input2, ⟨hs, rfl, ho, .same _, hf⟩⟩
  | print control =>
      rw [control] at hc
      cases hc with
      | same => exact ⟨_, .print rfl, ⟨hs, hi, by simp [ho], .same _, hf⟩⟩
      | arguments _ _ _ _ _ => exact ⟨_, .print rfl, ⟨hs, hi, by simp [ho], .same _, hf⟩⟩
  | evaluate_code control =>
      rw [control] at hc
      cases hc with
      | same => exact ⟨_, .evaluate_code rfl, ⟨hs, hi, ho, .same _, hf⟩⟩
      | arguments _ _ _ _ _ => exact ⟨_, .evaluate_code rfl, ⟨hs, hi, ho, .same _, hf⟩⟩
  | read_bad control invalid =>
      rw [control] at hc
      cases hc with
      | same => exact ⟨_, .read_bad rfl invalid, ⟨hs, hi, ho, .same _, hf⟩⟩
      | arguments _ _ _ _ _ => exact ⟨_, .read_bad rfl invalid, ⟨hs, hi, ho, .same _, hf⟩⟩
  | print_bad control invalid =>
      rw [control] at hc
      cases hc with
      | same => exact ⟨_, .print_bad rfl invalid, ⟨hs, hi, ho, .same _, hf⟩⟩
      | arguments _ _ _ _ _ => exact ⟨_, .print_bad rfl invalid, ⟨hs, hi, ho, .same _, hf⟩⟩
  | eval_bad control invalid =>
      rw [control] at hc
      cases hc with
      | same => exact ⟨_, .eval_bad rfl invalid, ⟨hs, hi, ho, .same _, hf⟩⟩
      | arguments _ _ _ _ _ => exact ⟨_, .eval_bad rfl invalid, ⟨hs, hi, ho, .same _, hf⟩⟩
  | primitive control ordinary native result =>
      rw [control] at hc
      have result2 := hs ▸ result
      cases hc with
      | same => exact ⟨_, .primitive rfl ordinary native result2, ⟨rfl, hi, ho, .same _, hf⟩⟩
      | arguments _ _ _ _ _ =>
          exact ⟨_, .primitive rfl ordinary native result2, ⟨rfl, hi, ho, .same _, hf⟩⟩
  | primitive_fault control ordinary native result =>
      rw [control] at hc
      have result2 := hs ▸ result
      cases hc with
      | same => exact ⟨_, .primitive_fault rfl ordinary native result2, ⟨hs, hi, ho, .same _, hf⟩⟩
      | arguments _ _ _ _ _ =>
          exact ⟨_, .primitive_fault rfl ordinary native result2, ⟨hs, hi, ho, .same _, hf⟩⟩
  | equations control ordinary notNative =>
      rw [control] at hc
      cases hc with
      | same => exact ⟨_, .equations rfl ordinary notNative, ⟨hs, hi, ho, .same _, hf⟩⟩
      | arguments _ _ _ _ _ =>
          exact ⟨_, .equations rfl ordinary notNative, ⟨hs, hi, ho, .same _, hf⟩⟩
  | raw_argument control raw =>
      rename_i bindings target first rest values index
      have rawPosition : (match target with
          | .function head => argumentIsRaw program head index
          | .data => false) = true := by
        cases target <;> simp_all
      rw [control] at hc
      cases hc with
      | same =>
          exact ⟨_, .raw_argument rfl (by cases target <;> simp_all),
            ⟨hs, hi, ho, .same _, .cons (.same _) hf⟩⟩
      | arguments _ _ _ _ within =>
          have firstWithin := within first List.mem_cons_self
          have restWithin : ∀ a ∈ rest, Within vars a :=
            fun a member => within a (List.mem_cons_of_mem _ member)
          refine ⟨_, .raw_argument (bindings := caller) (first := rename names first) (rest := rest.map (rename names))
            (by simp) (by cases target <;> simp_all),
            ⟨hs, hi, ho, ?_, .cons (.argument _ _ _ _ restWithin) hf⟩⟩
          simp only
          rw [applySubst_rename agree first firstWithin]
          exact .same _
  | evaluated_argument control demanded =>
      rename_i bindings target first rest values index
      have evaluatedPosition : (match target with
          | .function head => argumentIsRaw program head index
          | .data => false) = false := by
        cases target <;> simp_all
      rw [control] at hc
      cases hc with
      | same =>
          exact ⟨_, .evaluated_argument rfl (by cases target <;> simp_all),
            ⟨hs, hi, ho, .same _, .cons (.same _) hf⟩⟩
      | arguments _ _ _ _ within =>
          have firstWithin := within first List.mem_cons_self
          have restWithin : ∀ a ∈ rest, Within vars a :=
            fun a member => within a (List.mem_cons_of_mem _ member)
          exact ⟨_, .evaluated_argument (bindings := caller) (first := rename names first)
            (rest := rest.map (rename names)) (by simp)
            (by cases target <;> simp_all),
            ⟨hs, hi, ho, .evaluate first firstWithin, .cons (.argument _ _ _ _ restWithin) hf⟩⟩
  | value_variable control =>
      rw [control] at hc
      cases hc with
      | same => exact ⟨_, .value_variable rfl, ⟨hs, hi, ho, .same _, hf⟩⟩
      | evaluate e within =>
          rename_i name
          refine ⟨_, .value_variable (bindings := caller) (name := names name) (by simp), ⟨hs, hi, ho, ?_, hf⟩⟩
          simp only
          have equal := applySubst_rename agree (.var name) within
          simp only [rename_var] at equal
          rw [equal]
          exact .same _
  | symbol control =>
      rw [control] at hc
      cases hc with
      | same => exact ⟨_, .symbol rfl, ⟨hs, hi, ho, .same _, hf⟩⟩
      | evaluate e within => exact ⟨_, .symbol (bindings := caller) (by simp), ⟨hs, hi, ho, .same _, hf⟩⟩
  | grounded control =>
      rw [control] at hc
      cases hc with
      | same => exact ⟨_, .grounded rfl, ⟨hs, hi, ho, .same _, hf⟩⟩
      | evaluate e within => exact ⟨_, .grounded (bindings := caller) (by simp), ⟨hs, hi, ho, .same _, hf⟩⟩
  | let_enter control =>
      rw [control] at hc
      cases hc with
      | same => exact ⟨_, .let_enter rfl, ⟨hs, hi, ho, .same _, .cons (.same _) hf⟩⟩
      | evaluate e within =>
          rename_i pattern value body
          have items := within_expression.mp within
          exact ⟨_, .let_enter (bindings := caller) (by simp),
            ⟨hs, hi, ho, .evaluate value (items value (by simp)),
              .cons (.bind pattern body (items pattern (by simp)) (items body (by simp))) hf⟩⟩
  | let_star control expanded =>
      rw [control] at hc
      cases hc with
      | same => exact ⟨_, .let_star rfl expanded, ⟨hs, hi, ho, .same _, hf⟩⟩
      | evaluate e within =>
          rename_i pairs body nested
          have items := within_expression.mp within
          have pairsWithin := within_expression.mp (items (.expression pairs) (by simp))
          have nestedWithin := nestedLets_within expanded pairsWithin (items body (by simp))
          have renamed : Eval.nestedLets (pairs.map (rename names)) (rename names body) =
              some (rename names nested) := by
            rw [nestedLets_rename, expanded]
            rfl
          exact ⟨_, .let_star (bindings := caller) (by simp) renamed,
            ⟨hs, hi, ho, .evaluate nested nestedWithin, hf⟩⟩
  | let_star_bad control invalid =>
      rw [control] at hc
      cases hc with
      | same => exact ⟨_, .let_star_bad rfl invalid, ⟨hs, hi, ho, .same _, hf⟩⟩
      | evaluate e within =>
          rename_i pairs body
          have renamed : Eval.nestedLets (pairs.map (rename names)) (rename names body) = none := by
            rw [nestedLets_rename, invalid]
            rfl
          exact ⟨_, .let_star_bad (bindings := caller) (by simp) renamed, ⟨hs, hi, ho, .same _, hf⟩⟩
  | case_enter control parsed =>
      rw [control] at hc
      cases hc with
      | same => exact ⟨_, .case_enter rfl parsed, ⟨hs, hi, ho, .same _, .cons (.same _) hf⟩⟩
      | evaluate e within =>
          rename_i value rows cases
          have items := within_expression.mp within
          have rowsWithin := within_expression.mp (items (.expression rows) (by simp))
          have casesWithin := readCases_within parsed rowsWithin
          have renamed : Eval.readCases (rows.map (rename names)) =
              some (renameCases names cases) := by
            rw [readCases_rename, parsed]
            rfl
          exact ⟨_, .case_enter (bindings := caller) (by simp) renamed,
            ⟨hs, hi, ho, .evaluate value (items value (by simp)),
              .cons (.select cases casesWithin) hf⟩⟩
  | case_bad control invalid =>
      rw [control] at hc
      cases hc with
      | same => exact ⟨_, .case_bad rfl invalid, ⟨hs, hi, ho, .same _, hf⟩⟩
      | evaluate e within =>
          rename_i value rows
          have renamed : Eval.readCases (rows.map (rename names)) = none := by
            rw [readCases_rename, invalid]
            rfl
          exact ⟨_, .case_bad (bindings := caller) (value := rename names value) (by simp) renamed, ⟨hs, hi, ho, .same _, hf⟩⟩
  | if_enter control =>
      rw [control] at hc
      cases hc with
      | same => exact ⟨_, .if_enter rfl, ⟨hs, hi, ho, .same _, .cons (.same _) hf⟩⟩
      | evaluate e within =>
          rename_i condition yes no
          have items := within_expression.mp within
          exact ⟨_, .if_enter (bindings := caller) (by simp),
            ⟨hs, hi, ho, .evaluate condition (items condition (by simp)),
              .cons (.branch yes no (items yes (by simp)) (items no (by simp))) hf⟩⟩
  | collapse_enter control =>
      rw [control] at hc
      cases hc with
      | same => exact ⟨_, .collapse_enter rfl, ⟨hs, hi, ho, .same _, .cons (.same _) hf⟩⟩
      | evaluate e within =>
          rename_i expression
          have items := within_expression.mp within
          exact ⟨_, .collapse_enter (bindings := caller) (by simp),
            ⟨hs, hi, ho, .evaluate expression (items expression (by simp)), .cons (.same _) hf⟩⟩
  | superpose_enter control =>
      rw [control] at hc
      cases hc with
      | same => exact ⟨_, .superpose_enter rfl, ⟨hs, hi, ho, .same _, hf⟩⟩
      | evaluate e within =>
          rename_i alternatives
          have items := within_expression.mp within
          have alternativesWithin := within_expression.mp (items (.expression alternatives) (by simp))
          exact ⟨_, .superpose_enter (bindings := caller) (by simp),
            ⟨hs, hi, ho, .sequence _ (relControls_evaluate callee caller names vars alternatives
              alternativesWithin), hf⟩⟩
  | empty_enter control =>
      rw [control] at hc
      cases hc with
      | same => exact ⟨_, .empty_enter rfl, ⟨hs, hi, ho, .same _, hf⟩⟩
      | evaluate e within => exact ⟨_, .empty_enter (bindings := caller) (by simp), ⟨hs, hi, ho, .same _, hf⟩⟩
  | quote_enter control =>
      rw [control] at hc
      cases hc with
      | same => exact ⟨_, .quote_enter rfl, ⟨hs, hi, ho, .same _, hf⟩⟩
      | evaluate e within =>
          rename_i expression
          have items := within_expression.mp within
          refine ⟨_, .quote_enter (bindings := caller) (expression := rename names expression) (by simp),
            ⟨hs, hi, ho, ?_, hf⟩⟩
          simp only
          rw [applySubst_rename agree expression (items expression (by simp))]
          exact .same _
  | call_enter control notControl callable =>
      rw [control] at hc
      cases hc with
      | same => exact ⟨_, .call_enter rfl notControl callable, ⟨hs, hi, ho, .same _, hf⟩⟩
      | evaluate e within =>
          rename_i head arguments
          have items := within_expression.mp within
          have renamedNotControl :
              controlForm (.expression (.symbol head :: arguments.map (rename names))) = false := by
            have := controlForm_rename names (.expression (.symbol head :: arguments))
            simp only [rename_expression, List.map_cons, rename_symbol] at this
            rw [this]
            exact notControl
          exact ⟨_, .call_enter (bindings := caller) (arguments := arguments.map (rename names)) (by simp)
            renamedNotControl callable,
            ⟨hs, hi, ho, .arguments _ arguments [] 0
              (fun a member => items a (List.mem_cons_of_mem _ member)), hf⟩⟩
  | data_enter control notControl notCallable =>
      rw [control] at hc
      cases hc with
      | same => exact ⟨_, .data_enter rfl notControl notCallable, ⟨hs, hi, ho, .same _, hf⟩⟩
      | evaluate e within =>
          rename_i head arguments
          have items := within_expression.mp within
          have renamedNotControl :
              controlForm (.expression (.symbol head :: arguments.map (rename names))) = false := by
            have := controlForm_rename names (.expression (.symbol head :: arguments))
            simp only [rename_expression, List.map_cons, rename_symbol] at this
            rw [this]
            exact notControl
          refine ⟨_, .data_enter (bindings := caller) (arguments := arguments.map (rename names)) (by simp)
            renamedNotControl notCallable, ⟨hs, hi, ho, ?_, hf⟩⟩
          have related : RelControl callee caller names vars _ _ :=
            RelControl.arguments .data (.symbol head :: arguments) [] 0 items
          simpa only [List.map_cons, rename_symbol] using related
  | expression_enter control unheaded =>
      rw [control] at hc
      cases hc with
      | same => exact ⟨_, .expression_enter rfl unheaded, ⟨hs, hi, ho, .same _, hf⟩⟩
      | evaluate e within =>
          rename_i items
          exact ⟨_, .expression_enter (bindings := caller) (items := items.map (rename names)) (by simp)
            (unheaded_rename names unheaded),
            ⟨hs, hi, ho, .arguments .data items [] 0 (within_expression.mp within), hf⟩⟩
  | collapse_return control frames =>
      rw [control] at hc
      rw [frames] at hf
      cases hc with
      | same =>
          cases hf with
          | cons head tail =>
              cases head with
              | same => exact ⟨_, .collapse_return rfl rfl, ⟨hs, hi, ho, .same _, tail⟩⟩
  | sequence_return control frames =>
      rw [control] at hc
      rw [frames] at hf
      cases hc with
      | same =>
          cases hf with
          | cons head tail =>
              cases head with
              | same => exact ⟨_, .sequence_return rfl rfl, ⟨hs, hi, ho, .same _, tail⟩⟩
              | sequence _ related =>
                  exact ⟨_, .sequence_return rfl rfl, ⟨hs, hi, ho, .sequence _ related, tail⟩⟩
  | argument_return control frames =>
      rw [control] at hc
      rw [frames] at hf
      cases hc with
      | same =>
          cases hf with
          | cons head tail =>
              cases head with
              | same => exact ⟨_, .argument_return rfl rfl, ⟨hs, hi, ho, .same _, tail⟩⟩
              | argument target pending values index within =>
                  exact ⟨_, .argument_return rfl rfl, ⟨hs, hi, ho,
                    .sequence _ (relControls_arguments callee caller names vars _ _
                      _ _ within _), tail⟩⟩
  | binding_return control frames =>
      rw [control] at hc
      rw [frames] at hf
      cases hc with
      | same =>
          cases hf with
          | cons head tail =>
              cases head with
              | same => exact ⟨_, .binding_return rfl rfl, ⟨hs, hi, ho, .same _, tail⟩⟩
              | bind pattern body patternWithin bodyWithin =>
                  exact ⟨_, .binding_return rfl rfl, ⟨hs, hi, ho,
                    .sequence _ (relControls_bind agree _ _ patternWithin bodyWithin _),
                    tail⟩⟩
  | case_return control frames =>
      rw [control] at hc
      rw [frames] at hf
      cases hc with
      | same =>
          cases hf with
          | cons head tail =>
              cases head with
              | same => exact ⟨_, .case_return rfl rfl, ⟨hs, hi, ho, .same _, tail⟩⟩
              | select cases within =>
                  exact ⟨_, .case_return rfl rfl, ⟨hs, hi, ho,
                    .sequence _ (relControls_select agree _ within _), tail⟩⟩
  | if_return control frames =>
      rw [control] at hc
      rw [frames] at hf
      cases hc with
      | same =>
          cases hf with
          | cons head tail =>
              cases head with
              | same => exact ⟨_, .if_return rfl rfl, ⟨hs, hi, ho, .same _, tail⟩⟩
              | branch yes no yesWithin noWithin =>
                  exact ⟨_, .if_return rfl rfl, ⟨hs, hi, ho,
                    .sequence _ (relControls_branch callee caller names vars _ _ yesWithin
                      noWithin _), tail⟩⟩
  | query_enter control =>
      rw [control] at hc
      cases hc with
      | same => exact ⟨_, .query_enter rfl, ⟨hs, hi, ho, .same _, .cons (.same _) hf⟩⟩
      | evaluate e within =>
          rename_i space pattern body
          have items := within_expression.mp within
          exact ⟨_, .query_enter (bindings := caller) (by simp),
            ⟨hs, hi, ho, .evaluate space (items space (by simp)),
              .cons (.query pattern body (items pattern (by simp)) (items body (by simp))) hf⟩⟩
  | query_return control frames =>
      rw [control] at hc
      rw [frames] at hf
      cases hc with
      | same =>
          cases hf with
          | cons head tail =>
              cases head with
              | same =>
                  refine ⟨_, .query_return rfl rfl, ⟨hs, hi, ho, ?_, tail⟩⟩
                  simp only
                  rw [hs]
                  exact .same _
              | query pattern body patternWithin bodyWithin =>
                  refine ⟨_, .query_return rfl rfl, ⟨hs, hi, ho, ?_, tail⟩⟩
                  simp only
                  rw [hs]
                  exact .sequence _ (relControls_query agree _ _ _ patternWithin bodyWithin _)

theorem rel_control_returned {one two : Configuration}
    (related : Rel callee caller names vars one two) (answers : List Atom) :
    one.control = .returned answers ↔ two.control = .returned answers := by
  have hc := related.control
  generalize one.control = k1 at hc ⊢
  generalize two.control = k2 at hc ⊢
  cases hc <;> simp

theorem rel_control_fault {one two : Configuration}
    (related : Rel callee caller names vars one two) (reason : Fault) :
    one.control = .fault reason ↔ two.control = .fault reason := by
  have hc := related.control
  generalize one.control = k1 at hc ⊢
  generalize two.control = k2 at hc ⊢
  cases hc <;> simp

theorem rel_frames_nil {one two : Configuration}
    (related : Rel callee caller names vars one two) : one.frames = [] ↔ two.frames = [] := by
  have hf := related.frames
  generalize one.frames = f1 at hf ⊢
  generalize two.frames = f2 at hf ⊢
  cases hf <;> simp

end Simulation

/-! ## Finished, faulted and moving configurations -/

/-- A configuration the machine has finished with: a fault, or answers with no frame
left. -/
def Terminal (c : Configuration) : Prop :=
  (∃ reason, c.control = .fault reason) ∨ (∃ answers, c.control = .returned answers ∧ c.frames = [])

theorem step_some_of_not_terminal (program : Program) (c : Configuration)
    (moving : ¬ Terminal c) : ∃ d, step program c = some d := by
  obtain ⟨state, control, frames, input, output⟩ := c
  cases control with
  | fault reason => exact absurd (.inl ⟨reason, rfl⟩) moving
  | returned answers =>
      cases frames with
      | nil => exact absurd (.inr ⟨answers, rfl, rfl⟩) moving
      | cons frame rest => cases frame <;> simp [step]
  | sequence remaining answers => cases remaining <;> simp [step]
  | arguments bindings target remaining values index =>
      cases remaining with
      | nil =>
          cases target with
          | data => simp [step]
          | function head =>
              simp only [step]
              split
              · split
                · split <;> simp
                · simp
                · simp
                · simp
              · split
                · split <;> simp
                · simp
      | cons first rest =>
          simp only [step]
          split <;> (try split) <;> exact ⟨_, rfl⟩
  | evaluate bindings expression =>
      simp only [step]
      split <;> (try split) <;> simp

theorem not_terminal_of_transition {program : Program} {c d : Configuration}
    (transition : Transition program c d) : ¬ Terminal c := by
  rintro (⟨reason, faulted⟩ | ⟨answers, returned, finished⟩)
  · cases transition <;> simp_all
  · cases transition <;> simp_all

theorem rel_terminal {callee caller : Subst} {names : String → String} {vars : List String}
    {one two : Configuration} (related : Rel callee caller names vars one two) :
    Terminal one ↔ Terminal two := by
  unfold Terminal
  simp only [rel_control_fault related, rel_control_returned related, rel_frames_nil related]

/-! ## Whole runs of the two bodies -/

section Runs

variable {callee caller : Subst} {names : String → String} {vars : List String}

theorem runs_complete_forward (agree : Agree callee caller names vars) {program : Program}
    {one : Configuration} {result : Outcome} (running : Runs program one result) :
    ∀ {two : Configuration} {state : State} {answers input output : List Atom},
      result = .complete state answers input output →
      Rel callee caller names vars one two → Runs program two (.complete state answers input output) := by
  induction running with
  | completed control frames =>
      intro two state answers input output same related
      cases same
      rename_i source answers'
      have control2 := (rel_control_returned related answers').mp control
      have frames2 := (rel_frames_nil related).mp frames
      have outcome := Runs.completed (program := program) control2 frames2
      rw [← related.state, ← related.input, ← related.output] at outcome
      exact outcome
  | fault control =>
      intro two state answers input output same
      cases same
  | next transition rest ih =>
      intro two state answers input output same related
      obtain ⟨next, transition2, related2⟩ := simulation agree transition related
      exact .next transition2 (ih same related2)

theorem runs_fault_forward (agree : Agree callee caller names vars) {program : Program}
    {one : Configuration} {result : Outcome} (running : Runs program one result) :
    ∀ {two : Configuration} {reason : Fault} {faulted : Configuration},
      result = .fault reason faulted →
      Rel callee caller names vars one two →
        ∃ faulted', Runs program two (.fault reason faulted') ∧
          Rel callee caller names vars faulted faulted' := by
  induction running with
  | completed control frames =>
      intro two reason faulted same
      cases same
  | fault control =>
      intro two reason faulted same related
      cases same
      rename_i source reason'
      exact ⟨two, .fault ((rel_control_fault related reason').mp control), related⟩
  | next transition rest ih =>
      intro two reason faulted same related
      obtain ⟨next, transition2, related2⟩ := simulation agree transition related
      obtain ⟨faulted', running', related'⟩ := ih same related2
      exact ⟨faulted', .next transition2 running', related'⟩

theorem runs_complete_backward (agree : Agree callee caller names vars) {program : Program}
    {two : Configuration} {result : Outcome} (running : Runs program two result) :
    ∀ {one : Configuration} {state : State} {answers input output : List Atom},
      result = .complete state answers input output →
      Rel callee caller names vars one two → Runs program one (.complete state answers input output) := by
  induction running with
  | completed control frames =>
      intro one state answers input output same related
      cases same
      rename_i source answers'
      have control1 := (rel_control_returned related answers').mpr control
      have frames1 := (rel_frames_nil related).mpr frames
      have outcome := Runs.completed (program := program) control1 frames1
      rw [related.state, related.input, related.output] at outcome
      exact outcome
  | fault control =>
      intro one state answers input output same
      cases same
  | next transition rest ih =>
      rename_i source target result
      intro one state answers input output same related
      have moving : ¬ Terminal one :=
        fun terminal => not_terminal_of_transition transition ((rel_terminal related).mp terminal)
      obtain ⟨next, computed⟩ := step_some_of_not_terminal program one moving
      have transition1 := step_transition computed
      obtain ⟨next2, transition2, related2⟩ := simulation agree transition1 related
      have same2 : next2 = target :=
        Option.some.inj ((transition_step transition2).symm.trans (transition_step transition))
      subst same2
      exact .next transition1 (ih same related2)

theorem runs_fault_backward (agree : Agree callee caller names vars) {program : Program}
    {two : Configuration} {result : Outcome} (running : Runs program two result) :
    ∀ {one : Configuration} {reason : Fault} {faulted' : Configuration},
      result = .fault reason faulted' →
      Rel callee caller names vars one two →
        ∃ faulted, Runs program one (.fault reason faulted) ∧
          Rel callee caller names vars faulted faulted' := by
  induction running with
  | completed control frames =>
      intro one reason faulted' same
      cases same
  | fault control =>
      intro one reason faulted' same related
      cases same
      rename_i source reason'
      exact ⟨one, .fault ((rel_control_fault related reason').mpr control), related⟩
  | next transition rest ih =>
      rename_i source target result
      intro one reason faulted' same related
      have moving : ¬ Terminal one :=
        fun terminal => not_terminal_of_transition transition ((rel_terminal related).mp terminal)
      obtain ⟨next, computed⟩ := step_some_of_not_terminal program one moving
      have transition1 := step_transition computed
      obtain ⟨next2, transition2, related2⟩ := simulation agree transition1 related
      have same2 : next2 = target :=
        Option.some.inj ((transition_step transition2).symm.trans (transition_step transition))
      subst same2
      obtain ⟨faulted, running1, relatedFault⟩ := ih same related2
      exact ⟨faulted, .next transition1 running1, relatedFault⟩

end Runs

/-! ## Runs along a deterministic path, and caller frames -/

theorem runs_step_iff {program : Program} {a b : Configuration} {o : Outcome}
    (transition : Transition program a b) : Runs program a o ↔ Runs program b o := by
  constructor
  · intro running
    cases running with
    | completed control frames =>
        exact absurd (.inr ⟨_, control, frames⟩) (not_terminal_of_transition transition)
    | fault control =>
        exact absurd (.inl ⟨_, control⟩) (not_terminal_of_transition transition)
    | next transition' rest =>
        have same : b = _ :=
          Option.some.inj ((transition_step transition).symm.trans (transition_step transition'))
        exact same ▸ rest
  · exact fun running => .next transition running

theorem runs_path_iff {program : Program} {o : Outcome} :
    {a b : Configuration} → (theory program).MultiStep a b → (Runs program a o ↔ Runs program b o)
  | _, _, .refl _ => Iff.rfl
  | _, _, .step transition rest => (runs_step_iff transition).trans (runs_path_iff rest)

/-- A run beneath caller frames is a run of the computation, then of the callers with
its answers; or a fault of the computation, its frames above the callers'. -/
theorem runs_split_frames {program : Program} (caller : List Frame) {d : Configuration}
    {o : Outcome} (running : Runs program d o) :
    ∀ (c : Configuration), d = withFrames c caller →
      (∃ state answers input output, Runs program c (.complete state answers input output) ∧
        Runs program { state, control := .returned answers, frames := caller, input, output } o) ∨
      (∃ reason faulted, Runs program c (.fault reason faulted) ∧
        o = .fault reason (withFrames faulted caller)) := by
  induction running with
  | completed control frames =>
      rename_i source answers
      intro c same
      subst same
      simp only [withFrames, List.append_eq_nil_iff] at control frames
      obtain ⟨own, callers⟩ := frames
      subst callers
      refine .inl ⟨c.state, answers, c.input, c.output, .completed control own, ?_⟩
      exact .completed rfl rfl
  | fault control =>
      rename_i source reason
      intro c same
      subst same
      exact .inr ⟨reason, c, .fault control, rfl⟩
  | next transition rest ih =>
      rename_i source target result
      intro c same
      subst same
      by_cases terminal : Terminal c
      · rcases terminal with ⟨reason, faulted⟩ | ⟨answers, returned, finished⟩
        · exact absurd (.inl ⟨reason, faulted⟩) (not_terminal_of_transition transition)
        · refine .inl ⟨c.state, answers, c.input, c.output, .completed returned finished, ?_⟩
          have shape : withFrames c caller =
              { state := c.state, control := .returned answers, frames := caller,
                input := c.input, output := c.output } := by
            obtain ⟨st, k, fs, i, o⟩ := c
            simp only at returned finished
            subst returned finished
            rfl
          rw [← shape]
          exact .next transition rest
      · obtain ⟨next, computed⟩ := step_some_of_not_terminal program c terminal
        have lifted := step_with_caller_frames program c next caller computed
        have same : target = withFrames next caller :=
          Option.some.inj ((transition_step transition).symm.trans lifted)
        rcases ih next same with ⟨st, answers, i, o, inner, outer⟩ | ⟨reason, faulted, inner, eq⟩
        · exact .inl ⟨st, answers, i, o, .next (step_transition computed) inner, outer⟩
        · exact .inr ⟨reason, faulted, .next (step_transition computed) inner, eq⟩

theorem runs_of_path {program : Program} {a b : Configuration} {o : Outcome}
    (path : (theory program).MultiStep a b) (running : Runs program b o) : Runs program a o :=
  (runs_path_iff path).mpr running

theorem runs_join_frames {program : Program} (caller : List Frame) (c : Configuration)
    {state : State} {answers input output : List Atom} {o : Outcome}
    (inner : Runs program c (.complete state answers input output))
    (outer : Runs program { state, control := .returned answers, frames := caller, input, output } o) :
    Runs program (withFrames c caller) o := by
  have path := (completed_derivation_iff_path program c state answers input output).mp inner
  have lifted := path_with_caller_frames program caller path
  apply runs_of_path lifted
  simpa [withFrames, finished] using outer

theorem runs_join_fault {program : Program} (caller : List Frame) {c : Configuration}
    {reason : Fault} {faulted : Configuration} (inner : Runs program c (.fault reason faulted)) :
    Runs program (withFrames c caller) (.fault reason (withFrames faulted caller)) := by
  generalize resultEq : Outcome.fault reason faulted = result at inner
  induction inner with
  | completed control frames => cases resultEq
  | fault control =>
      cases resultEq
      exact .fault control
  | next transition rest ih =>
      exact .next (step_transition (step_with_caller_frames program _ _ caller
        (transition_step transition))) (ih resultEq)

/-- Answers returned to the given frames. -/
def returnedTo (state : State) (answers : List Atom) (frames : List Frame)
    (input output : List Atom) : Configuration :=
  { state := state, control := .returned answers, frames := frames, input := input,
    output := output }

/-- Empty sequencing frames pass answers through. -/
theorem runs_pop_empty_sequences (program : Program) (caller : List Frame) (state : State)
    (answers input output : List Atom) (o : Outcome) :
    ∀ (count : Nat),
      Runs program (returnedTo state answers (List.replicate count (.sequence [] []) ++ caller)
        input output) o ↔ Runs program (returnedTo state answers caller input output) o
  | 0 => by simp
  | count + 1 => by
      rw [runs_step_iff (.sequence_return rfl rfl), runs_step_iff (.sequence_done rfl)]
      simpa [returnedTo] using runs_pop_empty_sequences program caller state answers input output o count

/-! ## The call reaches its equation's body -/

theorem path_trans {program : Program} :
    {a b c : Configuration} → (theory program).MultiStep a b → (theory program).MultiStep b c →
      (theory program).MultiStep a c
  | _, _, _, .refl _, second => second
  | _, _, _, .step transition rest, second => .step transition (path_trans rest second)

theorem lookup_cons (name other : String) (value : Atom) (rest : Subst) :
    Subst.lookup ((name, value) :: rest) other =
      if name = other then some value else Subst.lookup rest other := by
  by_cases same : name = other
  · subst same
    simp [Subst.lookup, List.find?]
  · have different : (name == other) = false := by simp [same]
    simp [Subst.lookup, List.find?, different, same]

/-- Matching distinct parameter variables binds each to its value. -/
theorem matchValues_parameters :
    ∀ (params : List String) (values : List Atom) (acc : Subst),
      params.Nodup → values.length = params.length → (∀ x ∈ params, Subst.lookup acc x = none) →
      ∃ bound, SpaceSemantics.matchValue.matchValues acc (params.map .var) values = some bound ∧
        (∀ i (h₁ : i < params.length) (h₂ : i < values.length),
          Subst.lookup bound params[i] = some values[i]) ∧
        (∀ y, y ∉ params → Subst.lookup bound y = Subst.lookup acc y)
  | [], values, acc, _, lengths, _ => by
      cases values with
      | nil =>
          exact ⟨acc, by simp [SpaceSemantics.matchValue.matchValues],
            fun i h₁ => absurd h₁ (Nat.not_lt_zero i), fun _ _ => rfl⟩
      | cons _ _ => simp at lengths
  | x :: xs, values, acc, distinct, lengths, fresh => by
      cases values with
      | nil => simp at lengths
      | cons v vs =>
          have xNotIn : x ∉ xs := (List.nodup_cons.mp distinct).1
          have xsDistinct : xs.Nodup := (List.nodup_cons.mp distinct).2
          have accFresh : Subst.lookup acc x = none := fresh x List.mem_cons_self
          have freshTail : ∀ y ∈ xs, Subst.lookup ((x, v) :: acc) y = none := by
            intro y member
            have different : x ≠ y := fun same => xNotIn (same ▸ member)
            rw [lookup_cons, if_neg different]
            exact fresh y (List.mem_cons_of_mem _ member)
          obtain ⟨bound, matched, values', others⟩ :=
            matchValues_parameters xs vs ((x, v) :: acc) xsDistinct
              (by simpa using lengths) freshTail
          refine ⟨bound, ?_, ?_, ?_⟩
          · simp only [List.map_cons, SpaceSemantics.matchValue.matchValues, bind, Option.bind]
            rw [matchValue_atomic _ _ _ (by simp)]
            simp only [matchAtom, accFresh]
            exact matched
          · intro i h₁ h₂
            cases i with
            | zero =>
                simp only [List.getElem_cons_zero]
                rw [others x xNotIn, lookup_cons, if_pos rfl]
            | succ i =>
                simp only [List.getElem_cons_succ]
                exact values' i (by simpa using h₁) (by simpa using h₂)
          · intro y notIn
            have notTail : y ∉ xs := fun member => notIn (List.mem_cons_of_mem _ member)
            have different : x ≠ y := fun same => notIn (same ▸ List.mem_cons_self)
            rw [others y notTail, lookup_cons, if_neg different]

theorem filterMap_ite_eq_filter {α β : Type} (p : α → Prop) [DecidablePred p]
    (g : α → Option β) : ∀ (items : List α),
      items.filterMap (fun item => if p item then g item else none) =
        (items.filter (fun item => decide (p item))).filterMap g
  | [] => rfl
  | item :: rest => by
      have tail := filterMap_ite_eq_filter p g rest
      by_cases holds : p item
      · rw [List.filter_cons_of_pos (by simpa using holds)]
        simp only [List.filterMap_cons, holds, ↓reduceIte]
        cases g item <;> simp [tail]
      · rw [List.filter_cons_of_neg (by simpa using holds)]
        simp only [List.filterMap_cons, holds, ↓reduceIte]
        exact tail

/-- With one equation for `f`, the clauses of a call are that equation's match. -/
theorem clauses_single (program : Program) (f : String) (params : List String) (body : Atom)
    (single : program.equations.filter (fun equation => equation.head == f) =
      [⟨f, params.map .var, body⟩]) (values : List Atom) :
    clauses program f values =
      ((SpaceSemantics.matchValue.matchValues [] (params.map .var) values).map
        fun bound => Control.evaluate bound body).toList := by
  unfold clauses
  have rewritten := filterMap_ite_eq_filter (fun equation : SpaceSemantics.Equation =>
      equation.head = f)
    (fun equation => (SpaceSemantics.matchValue.matchValues [] equation.arguments values).map
      fun bindings => Control.evaluate bindings equation.body)
    program.equations
  rw [rewritten]
  have sameFilter : (fun equation : SpaceSemantics.Equation => decide (equation.head = f)) =
      (fun equation => equation.head == f) := by
    funext equation
    by_cases same : equation.head = f <;> simp [same]
  rw [sameFilter, single]
  simp only [List.filterMap_cons, List.filterMap_nil]
  cases (SpaceSemantics.matchValue.matchValues [] (params.map .var) values) <;> rfl

theorem arguments_path (program : Program) (caller : Subst) (head : String) (state : State)
    (input output : List Atom) :
    ∀ (remaining : List String) (values : List Atom) (index : Nat) (frames : List Frame),
      (theory program).MultiStep
        ⟨state, .arguments caller (.function head) (remaining.map .var) values index, frames,
          input, output⟩
        ⟨state, .arguments caller (.function head) []
            (values ++ remaining.map fun a => applySubst caller (.var a))
            (index + remaining.length),
          List.replicate remaining.length (.sequence [] []) ++ frames, input, output⟩
  | [], values, index, frames => by
      simp only [List.map_nil, List.append_nil, List.length_nil, Nat.add_zero,
        List.replicate_zero, List.nil_append]
      exact .refl _
  | a :: rest, values, index, frames => by
      have tail := arguments_path program caller head state input output rest
        (values ++ [applySubst caller (.var a)]) (index + 1) (.sequence [] [] :: frames)
      have first : (theory program).MultiStep
          ⟨state, .arguments caller (.function head) ((a :: rest).map .var) values index, frames,
            input, output⟩
          ⟨state, .arguments caller (.function head) (rest.map .var)
            (values ++ [applySubst caller (.var a)]) (index + 1), .sequence [] [] :: frames,
            input, output⟩ := by
        cases raw : argumentIsRaw program head index with
        | true =>
            exact .step (Transition.raw_argument rfl (by simpa using raw))
              (.step (Transition.argument_return rfl rfl)
                (.step (Transition.sequence_enter rfl) (.refl _)))
        | false =>
            exact .step (Transition.evaluated_argument rfl (by simpa using raw))
              (.step (Transition.value_variable rfl)
                (.step (Transition.argument_return rfl rfl)
                  (.step (Transition.sequence_enter rfl) (.refl _))))
      have shape :
          List.replicate rest.length (Frame.sequence [] []) ++ Frame.sequence [] [] :: frames =
            List.replicate (a :: rest).length (Frame.sequence [] []) ++ frames := by
        simp [List.replicate_succ', List.append_assoc]
      refine path_trans first ?_
      simpa [shape, List.append_assoc, Nat.add_assoc, Nat.add_comm 1] using tail

theorem ordinary_not_control (f : String) (items : List Atom)
    (ordinary : f ∉ ["let", "let*", "case", "if", "collapse", "superpose", "empty", "quote", "unique"])
    (notMatch : f ≠ "match") :
    controlForm (.expression (.symbol f :: items)) = false := by
  rw [controlForm_eq_shape]
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at ordinary
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := ordinary
  rcases items with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, rest⟩⟩⟩⟩ <;> simp [shape, *]

/-- **The call reaches its body.** A saturated call of a one-equation function whose
arguments are variables evaluates its arguments, selects the equation, and runs the
body under the parameters' bindings, above one empty sequencing frame per argument and
one for the selected equation. -/
theorem call_reaches_body (program : Program) (f : String) (params args : List String)
    (body : Atom)
    (single : program.equations.filter (fun equation => equation.head == f) =
      [⟨f, params.map .var, body⟩])
    (distinct : params.Nodup) (lengths : args.length = params.length)
    (notPrimitive : StdLib.known f = false) (notIO : ioHead f = false)
    (ordinary : f ∉ ["let", "let*", "case", "if", "collapse", "superpose", "empty", "quote", "unique"])
    (caller : Subst) (state : State) (frames : List Frame) (input output : List Atom) :
    ∃ callee : Subst,
      (∀ i (h₁ : i < params.length) (h₂ : i < args.length),
        Subst.lookup callee params[i] = some (applySubst caller (.var args[i]))) ∧
      (theory program).MultiStep
        ⟨state, .evaluate caller (.expression (.symbol f :: args.map .var)), frames, input, output⟩
        ⟨state, .evaluate callee body,
          List.replicate (args.length + 1) (.sequence [] []) ++ frames, input, output⟩ := by
  obtain ⟨callee, matched, lookups, _⟩ := matchValues_parameters params
    (args.map fun a => applySubst caller (.var a)) [] distinct (by simp [lengths])
    (by simp [Subst.lookup])
  refine ⟨callee, fun i h₁ h₂ => ?_, ?_⟩
  · have found := lookups i h₁ (by simpa using h₂)
    rw [List.getElem_map] at found
    exact found
  · have callable : (ioHead f || StdLib.known f || program.equations.any (·.head == f)) = true := by
      have member : (⟨f, params.map .var, body⟩ : SpaceSemantics.Equation) ∈
          program.equations.filter (fun equation => equation.head == f) := by
        rw [single]; simp
      have found := List.mem_filter.mp member
      simp only [List.any_eq_true, Bool.or_eq_true]
      exact .inr ⟨_, found.1, found.2⟩
    have enter : Transition program
        ⟨state, .evaluate caller (.expression (.symbol f :: args.map .var)), frames, input, output⟩
        ⟨state, .arguments caller (.function f) (args.map .var) [] 0, frames, input, output⟩ :=
      .call_enter rfl (ordinary_not_control f _ ordinary (ne_match_of_not_known notPrimitive)) callable
    have argumentsPath := arguments_path program caller f state input output args [] 0 frames
    simp only [List.nil_append, Nat.zero_add] at argumentsPath
    have dispatch : Transition program
        ⟨state, .arguments caller (.function f) [] (args.map fun a => applySubst caller (.var a))
          args.length, List.replicate args.length (.sequence [] []) ++ frames, input, output⟩
        ⟨state, .sequence [.evaluate callee body] [],
          List.replicate args.length (.sequence [] []) ++ frames, input, output⟩ := by
      have equations := Transition.equations (program := program)
        (source := ⟨state, .arguments caller (.function f) []
          (args.map fun a => applySubst caller (.var a)) args.length,
          List.replicate args.length (.sequence [] []) ++ frames, input, output⟩) rfl notIO
        notPrimitive
      have chosen : clauses program f (args.map fun a => applySubst caller (.var a)) =
          [.evaluate callee body] := by
        simp [clauses_single program f params body single, matched]
      rw [application_of_selected chosen] at equations
      exact equations
    have selected : Transition program
        ⟨state, .sequence [.evaluate callee body] [],
          List.replicate args.length (.sequence [] []) ++ frames, input, output⟩
        ⟨state, .evaluate callee body,
          List.replicate (args.length + 1) (.sequence [] []) ++ frames, input, output⟩ :=
      .sequence_enter rfl
    exact .step enter (path_trans argumentsPath (.step dispatch (.step selected (.refl _))))

/-! ## Beta inlining -/

section Beta

variable (program : Program) (f : String) (params args : List String) (body : Atom)
  (names : String → String) (caller : Subst) (state : State) (frames : List Frame)
  (input output : List Atom)

/-- The premises under which a call is its body with the arguments substituted. -/
structure Inlinable : Prop where
  /-- `f` has exactly one equation, whose head arguments are the parameters. -/
  single : program.equations.filter (fun equation => equation.head == f) =
    [⟨f, params.map .var, body⟩]
  /-- The parameters are distinct variables. -/
  distinct : params.Nodup
  /-- The body uses no variable other than the parameters. -/
  closed : Within params body
  /-- The call supplies one argument per parameter. -/
  saturated : args.length = params.length
  /-- `names` sends each parameter to its argument variable. -/
  renamed : ∀ i (h₁ : i < params.length) (h₂ : i < args.length), names params[i] = args[i]
  /-- `f` is an authored function, not a primitive, an I/O operation or control syntax. -/
  notPrimitive : StdLib.known f = false
  notIO : ioHead f = false
  ordinary : f ∉ ["let", "let*", "case", "if", "collapse", "superpose", "empty", "quote", "unique"]
  /-- Every argument variable is bound in the caller's environment. -/
  bound : ∀ a ∈ args, ∃ value, Subst.lookup caller a = some value

/-- The configuration evaluating the call. -/
def callConfiguration : Configuration :=
  ⟨state, .evaluate caller (.expression (.symbol f :: args.map .var)), frames, input, output⟩

/-- The configuration evaluating the body with the arguments substituted, in the
caller's environment and continuation. -/
def inlinedConfiguration : Configuration :=
  ⟨state, .evaluate caller (rename names body), frames, input, output⟩

variable {program f params args body names caller}

theorem inlinable_agree (premises : Inlinable program f params args body names caller)
    {callee : Subst}
    (lookups : ∀ i (h₁ : i < params.length) (h₂ : i < args.length),
      Subst.lookup callee params[i] = some (applySubst caller (.var args[i]))) :
    Agree callee caller names params := by
  intro x member
  obtain ⟨i, h₁, rfl⟩ := List.getElem_of_mem member
  have h₂ : i < args.length := by rw [premises.saturated]; exact h₁
  obtain ⟨value, found⟩ := premises.bound args[i] (List.getElem_mem h₂)
  refine ⟨value, ?_, ?_⟩
  · rw [lookups i h₁ h₂]
    simp [applySubst, found]
  · rw [premises.renamed i h₁ h₂]
    exact found

/-- **Beta inlining, completed runs.** The call and its inlined body complete with the
same store, the same answers in the same order and multiplicity, and the same remaining
input and output, in every continuation. -/
theorem beta_complete (premises : Inlinable program f params args body names caller)
    (after : State) (answers input' output' : List Atom) :
    Runs program (callConfiguration f args caller state frames input output)
        (.complete after answers input' output') ↔
      Runs program (inlinedConfiguration body names caller state frames input output)
        (.complete after answers input' output') := by
  obtain ⟨callee, lookups, path⟩ := call_reaches_body program f params args body premises.single
    premises.distinct premises.saturated premises.notPrimitive premises.notIO premises.ordinary
    caller state frames input output
  have agree := inlinable_agree premises lookups
  have related : Rel callee caller names params ⟨state, .evaluate callee body, [], input, output⟩
      ⟨state, .evaluate caller (rename names body), [], input, output⟩ :=
    ⟨rfl, rfl, rfl, .evaluate body premises.closed, .nil⟩
  unfold callConfiguration inlinedConfiguration
  rw [runs_path_iff path]
  constructor
  · intro running
    rcases runs_split_frames (List.replicate (args.length + 1) (.sequence [] []) ++ frames) running
        ⟨state, .evaluate callee body, [], input, output⟩ rfl with
      ⟨st, returned, i, o, inner, outer⟩ | ⟨reason, faulted, inner, same⟩
    · have outer' := (runs_pop_empty_sequences program frames st returned i o _
        (args.length + 1)).mp outer
      exact runs_join_frames frames _ (runs_complete_forward agree inner rfl related) outer'
    · cases same
  · intro running
    rcases runs_split_frames frames running
        ⟨state, .evaluate caller (rename names body), [], input, output⟩ rfl with
      ⟨st, returned, i, o, inner, outer⟩ | ⟨reason, faulted, inner, same⟩
    · have outer' := (runs_pop_empty_sequences program frames st returned i o _
        (args.length + 1)).mpr outer
      exact runs_join_frames _ _ (runs_complete_backward agree inner rfl related) outer'
    · cases same

/-- **Beta inlining, faults.** The call faults exactly when the inlined body does, for
the same reason and with the same store and input/output at the fault. -/
theorem beta_fault (premises : Inlinable program f params args body names caller)
    (reason : Fault) (after : State) (input' output' : List Atom) :
    (∃ faulted, Runs program (callConfiguration f args caller state frames input output)
        (.fault reason faulted) ∧
        faulted.state = after ∧ faulted.input = input' ∧ faulted.output = output') ↔
      (∃ faulted, Runs program (inlinedConfiguration body names caller state frames input output)
        (.fault reason faulted) ∧
        faulted.state = after ∧ faulted.input = input' ∧ faulted.output = output') := by
  obtain ⟨callee, lookups, path⟩ := call_reaches_body program f params args body premises.single
    premises.distinct premises.saturated premises.notPrimitive premises.notIO premises.ordinary
    caller state frames input output
  have agree := inlinable_agree premises lookups
  have related : Rel callee caller names params ⟨state, .evaluate callee body, [], input, output⟩
      ⟨state, .evaluate caller (rename names body), [], input, output⟩ :=
    ⟨rfl, rfl, rfl, .evaluate body premises.closed, .nil⟩
  unfold callConfiguration inlinedConfiguration
  constructor
  · rintro ⟨faulted, running, hs, hi, ho⟩
    rw [runs_path_iff path] at running
    rcases runs_split_frames (List.replicate (args.length + 1) (.sequence [] []) ++ frames) running
        ⟨state, .evaluate callee body, [], input, output⟩ rfl with
      ⟨st, returned, i, o, inner, outer⟩ | ⟨reason', faulted', inner, same⟩
    · have outer' := (runs_pop_empty_sequences program frames st returned i o _
        (args.length + 1)).mp outer
      exact ⟨faulted, runs_join_frames frames _ (runs_complete_forward agree inner rfl related)
        outer', hs, hi, ho⟩
    · cases same
      obtain ⟨faulted'', running'', related''⟩ := runs_fault_forward agree inner rfl related
      refine ⟨withFrames faulted'' frames, runs_join_fault frames running'', ?_, ?_, ?_⟩
      · rw [← hs]; exact related''.state.symm
      · rw [← hi]; exact related''.input.symm
      · rw [← ho]; exact related''.output.symm
  · rintro ⟨faulted, running, hs, hi, ho⟩
    rcases runs_split_frames frames running
        ⟨state, .evaluate caller (rename names body), [], input, output⟩ rfl with
      ⟨st, returned, i, o, inner, outer⟩ | ⟨reason', faulted', inner, same⟩
    · have outer' := (runs_pop_empty_sequences program frames st returned i o _
        (args.length + 1)).mpr outer
      exact ⟨faulted, (runs_path_iff path).mpr (runs_join_frames _ _
        (runs_complete_backward agree inner rfl related) outer'), hs, hi, ho⟩
    · cases same
      obtain ⟨faulted'', running'', related''⟩ := runs_fault_backward agree inner rfl related
      refine ⟨withFrames faulted''
          (List.replicate (args.length + 1) (Frame.sequence [] []) ++ frames),
        (runs_path_iff path).mpr (runs_join_fault
          (List.replicate (args.length + 1) (Frame.sequence [] []) ++ frames) running''),
        ?_, ?_, ?_⟩
      · rw [← hs]; exact related''.state
      · rw [← hi]; exact related''.input
      · rw [← ho]; exact related''.output

end Beta

end Mettapedia.Languages.MeTTa.PeTTa.BetaInlining
