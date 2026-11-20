import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.EvaluationModes.Typed

/-!
# Nested occurrences and heads without a definition

A head with no definition (`wrap`, `pair`) either evaluates its arguments (`constructorsRun`, what
Hyperon Experimental, PeTTa and the Prime draft all do for written code: `!(wrap (f a))` is
`(wrap 5)` in each) or holds them. Crossed with the two held rules that keep the four laws, this
gives four designs: `byName`, `byNameHold`, `codeValue`, `codeValueHold`.

**Two laws for undeclared heads.**

* `KeepsConstructorValues`: a written `(wrap M)` prints `(wrap v)` for each value `v` of `M`
  (constructors are applied to values). Kept wherever arguments are evaluated
  (`constructorValues_of`), broken by both designs that hold them (`constructorValues_hold_breaks`).
* `KeepsFieldReading`, the plain reading at a field: `(= (g $x) (wrap $x))` with `$x` held,
  `(g M)` prints what the written `(wrap M)` prints, for every `M`. It holds exactly when undeclared
  heads hold their arguments, or a held parameter runs at every computation position under every
  computation type (`fieldReading_iff`, all 96 designs): by-name under both defaults, Hyperon
  Experimental, and code value only with held arguments; not the Prime draft or the hybrid.
* `four_combinations`: with evaluated arguments, code value must give up the field reading to keep
  constructors taking values; by-name keeps both; with held arguments both keep the field reading
  and give up constructors taking values.

**What `(pair $x $x)` costs** (`pair_costs`), counted on the core's traces as calls of `f`: two runs
under by-name with evaluated arguments (as in Hyperon Experimental), none in the other three. With
held code that has two answers, `(= (two) 1) (= (two) 2)`, by-name with evaluated arguments runs it
twice independently and gives four pairs, mixed ones included; a `let`-bound value is chosen once
and gives two (`pair_choice_rows`). By-name duplicates work and choice; sharing it would be by need,
which this core does not model (the tree's branch-local Need calculus does).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.EvaluationModes

open Mettapedia.Languages.MeTTa.OSLFCore (Atom GroundedValue)
open Core CoreLaws Acceptance Weakening Laws

namespace Nested

/-- By-name, with the arguments of undeclared heads held. -/
def byNameHold : Design := { byName with constructorsRun := false }

/-- Code value, with the arguments of undeclared heads held. -/
def codeValueHold : Design := { codeValue with constructorsRun := false }

/-- `(: g (-> Atom %Undefined%)) (= (g $x) B)`. -/
def heldBody (B : Atom) : SProg := [fA, ⟨"g", some ([.atom], .undef), [([V "x"], B)]⟩]

/-- `(= (two) 1) (= (two) 2)`. -/
def twoFn : Fn := ⟨"two", none, [([], N 1), ([], N 2)]⟩

/-- How many times `f` ran on each answer's branch. -/
def runsOf (h : String) (L : List Ans) : List Nat := L.map fun a => a.2.count h

/-! ## The four designs on the measured nested rows -/

/-- `(g (f a))` with body `(wrap $x)`, and the written `(wrap (f a))`. -/
theorem nested_plain_reading_rows :
    answers byName (heldBody (E [S "wrap", V "x"])) F qRange = some [E [S "wrap", N 5]] ∧
    answers byName (heldBody (E [S "wrap", V "x"])) F (E [S "wrap", callFA]) =
      some [E [S "wrap", N 5]] ∧
    answers byNameHold (heldBody (E [S "wrap", V "x"])) F qRange = some [E [S "wrap", callFA]] ∧
    answers byNameHold (heldBody (E [S "wrap", V "x"])) F (E [S "wrap", callFA]) =
      some [E [S "wrap", callFA]] ∧
    answers codeValue (heldBody (E [S "wrap", V "x"])) F qRange = some [E [S "wrap", callFA]] ∧
    answers codeValue (heldBody (E [S "wrap", V "x"])) F (E [S "wrap", callFA]) =
      some [E [S "wrap", N 5]] ∧
    answers codeValueHold (heldBody (E [S "wrap", V "x"])) F qRange =
      some [E [S "wrap", callFA]] ∧
    answers codeValueHold (heldBody (E [S "wrap", V "x"])) F (E [S "wrap", callFA]) =
      some [E [S "wrap", callFA]] := by
  decide +kernel

/-- **What `(pair $x $x)` costs**: the answers and, per answer, the runs of `f`. -/
theorem pair_costs :
    (runQ byName (heldBody (E [S "pair", V "x", V "x"])) F qRange).map
        (fun L => (observe true L, runsOf "f" L)) =
      some ([E [S "pair", N 5, N 5]], [2]) ∧
    (runQ byNameHold (heldBody (E [S "pair", V "x", V "x"])) F qRange).map
        (fun L => (observe true L, runsOf "f" L)) =
      some ([E [S "pair", callFA, callFA]], [0]) ∧
    (runQ codeValue (heldBody (E [S "pair", V "x", V "x"])) F qRange).map
        (fun L => (observe false L, runsOf "f" L)) =
      some ([E [S "pair", callFA, callFA]], [0]) ∧
    (runQ codeValueHold (heldBody (E [S "pair", V "x", V "x"])) F qRange).map
        (fun L => (observe false L, runsOf "f" L)) =
      some ([E [S "pair", callFA, callFA]], [0]) ∧
    (runQ he (heldBody (E [S "pair", V "x", V "x"])) F qRange).map
        (fun L => (observe true L, runsOf "f" L)) =
      some ([E [S "pair", N 5, N 5]], [2]) ∧
    (runQ primeToday (heldBody (E [S "pair", V "x", V "x"])) F qRange).map
        (fun L => (observe true L, runsOf "f" L)) =
      some ([E [S "pair", callFA, callFA]], [0]) := by
  decide +kernel

/-- Held code with two answers, duplicated by `(pair $x $x)`: by-name with evaluated arguments
gives four pairs, mixed ones included; a `let`-bound value is chosen once. Measured: Hyperon
Experimental prints the four pairs in this order, and the `let` row as the same bag in the other
order; PeTTa and the Prime draft print `(pair (two) (two))` and the two equal pairs. -/
theorem pair_choice_rows :
    answers byName (twoFn :: heldBody (E [S "pair", V "x", V "x"])) F (E [S "g", E [S "two"]]) =
      some [E [S "pair", N 1, N 1], E [S "pair", N 1, N 2], E [S "pair", N 2, N 1],
        E [S "pair", N 2, N 2]] ∧
    answers he (twoFn :: heldBody (E [S "pair", V "x", V "x"])) F (E [S "g", E [S "two"]]) =
      some [E [S "pair", N 1, N 1], E [S "pair", N 1, N 2], E [S "pair", N 2, N 1],
        E [S "pair", N 2, N 2]] ∧
    answers codeValue (twoFn :: heldBody (E [S "pair", V "x", V "x"])) F
        (E [S "g", E [S "two"]]) =
      some [E [S "pair", E [S "two"], E [S "two"]]] ∧
    answers primeToday (twoFn :: heldBody (E [S "pair", V "x", V "x"])) F
        (E [S "g", E [S "two"]]) =
      some [E [S "pair", E [S "two"], E [S "two"]]] ∧
    answers byName [twoFn] F (E [S "let", V "y", E [S "two"], E [S "pair", V "y", V "y"]]) =
      some [E [S "pair", N 1, N 1], E [S "pair", N 2, N 2]] ∧
    answers he [twoFn] F (E [S "let", V "y", E [S "two"], E [S "pair", V "y", V "y"]]) =
      some [E [S "pair", N 1, N 1], E [S "pair", N 2, N 2]] ∧
    answers codeValue [twoFn] F (E [S "let", V "y", E [S "two"], E [S "pair", V "y", V "y"]]) =
      some [E [S "pair", N 1, N 1], E [S "pair", N 2, N 2]] := by
  decide +kernel

/-! ## Constructors applied to values -/

/-- A written `(wrap M)`, `wrap` undeclared. -/
def wrapQ (M : Atom) : Atom := E [S "wrap", M]

/-- **Constructors take values**: when `M` finishes refusing nothing, a written `(wrap M)` prints
`wrap` around each value `M` prints. -/
def KeepsConstructorValues (D : Design) : Prop :=
  ∀ (P : SProg) (M : Atom), modesOf P "wrap" 1 = none → ∀ (n : Nat) (A : List Ans),
    runQ D P n M = some A → allVal A = true →
      Prints D P (wrapQ M) ((observe D.reportsRefusal A).map fun v => E [S "wrap", v])

theorem continueEach_wrap (L : List Ans) :
    continueEach (fun v => some [(.val (E [S "wrap", v]), [])]) L =
      some (L.map fun a => match a with
        | (.val v, tr) => (.val (E [S "wrap", v]), tr)
        | (.refused d k, tr) => (.refused d k, tr)) := by
  induction L with
  | nil => rfl
  | cons a rest ih =>
      obtain ⟨o, tr⟩ := a
      cases o with
      | val v => simp [continueEach, ih]
      | refused d k => simp [continueEach, ih]

theorem observe_wrap (b : Bool) (L : List Ans) (hL : allVal L = true) :
    observe b (L.map fun a => match a with
        | (.val v, tr) => (.val (E [S "wrap", v]), tr)
        | (.refused d k, tr) => (.refused d k, tr)) =
      (observe b L).map fun v => E [S "wrap", v] := by
  induction L with
  | nil => rfl
  | cons a rest ih =>
      obtain ⟨o, tr⟩ := a
      cases o with
      | val v =>
          simp only [allVal_cons, Out.isVal, Bool.true_and] at hL
          simp [observe, ih hL]
      | refused d k => simp [allVal, Out.isVal] at hL

theorem runQ_wrap (D : Design) (hc : D.constructorsRun = true) (P : SProg) (M : Atom)
    (hw : modesOf P "wrap" 1 = none) (n : Nat) :
    runQ D P (n + 2) (wrapQ M) =
      (runQ D P (n + 1) M).map fun L => L.map fun a => match a with
        | (.val v, tr) => (.val (E [S "wrap", v]), tr)
        | (.refused d k, tr) => (.refused d k, tr) := by
  have hq : elabQuery D (modesOf P) (wrapQ M) =
      .bind (elabQuery D (modesOf P) M) (slot 0)
        (.ret (.expression [.symbol "wrap", .var (slot 0)])) := by
    have h1 : elabQuery D (modesOf P) (wrapQ M) =
        (match modesOf P "wrap" 1 with
          | some ps => elabArgs D (modesOf P) [] (fun _ => false) ps [M] 0 [] (.call "wrap")
          | none =>
              if D.constructorsRun then
                elabArgs D (modesOf P) [] (fun _ => false) (List.replicate 1 .undef) [M] 0 []
                  fun items => .ret (.expression (.symbol "wrap" :: items))
              else .ret (.expression [.symbol "wrap", M])) := rfl
    rw [h1, hw]
    simp only [hc, if_true]
    rfl
  unfold runQ
  rw [hq, exec_bind]
  have hk : (fun v => exec (elabProg D P) (n + 1)
      (.comp ((slot 0, v) :: []) (.ret (.expression [.symbol "wrap", .var (slot 0)])))) =
      fun v => some [(.val (E [S "wrap", v]), [])] := by
    funext v
    rw [exec_ret]
    rfl
  rw [hk]
  cases exec (elabProg D P) (n + 1) (.comp [] (elabQuery D (modesOf P) M)) with
  | none => rfl
  | some L => exact continueEach_wrap L

/-- Where undeclared heads evaluate their arguments, constructors take values, for every program
and every term. -/
theorem constructorValues_of (D : Design) (hc : D.constructorsRun = true) :
    KeepsConstructorValues D := by
  intro P M hw n A hA hval
  have hA' : runQ D P (n + 1) M = some A := runQ_mono (by omega) hA
  refine ⟨n + 2, ?_⟩
  rw [answers_eq, runQ_wrap D hc P M hw n, hA']
  simp only [Option.map_some]
  rw [observe_wrap _ A hval]

/-- With held arguments, the written `(wrap (f a))` prints as written: constructors do not take
values. -/
theorem constructorValues_hold_breaks :
    ¬ KeepsConstructorValues byNameHold ∧ ¬ KeepsConstructorValues codeValueHold := by
  have key : ∀ D : Design, runQ D [fA] F callFA = some [(.val (N 5), ["f"])] →
      observe D.reportsRefusal [(.val (N 5), ["f"])] = [N 5] →
      Prints D [fA] (wrapQ callFA) [E [S "wrap", callFA]] → ¬ KeepsConstructorValues D := by
    intro D hM hobs hw hk
    have := hk [fA] callFA rfl F _ hM rfl
    rw [hobs] at this
    exact absurd (Prints.det this hw) (by decide)
  exact ⟨key _ (by decide +kernel) rfl ⟨F, by decide +kernel⟩,
    key _ (by decide +kernel) rfl ⟨F, by decide +kernel⟩⟩

/-- The four designs of this module: the two with evaluated arguments keep the constructor law. -/
theorem constructorValues_evaluating :
    KeepsConstructorValues byName ∧ KeepsConstructorValues codeValue :=
  ⟨constructorValues_of byName rfl, constructorValues_of codeValue rfl⟩

/-! ## The plain reading at a field -/

/-- `(: g (-> Atom R)) (= (g $x) (wrap $x))`. -/
def wrapFn (R : Ty) : Fn := ⟨"g", some ([.atom], R), [([V "x"], E [S "wrap", V "x"])]⟩

theorem wrapFn_clauses (D : Design) (ms : Modes) (R : Ty) (hR : Unchecked R)
    (hw : ms "wrap" 1 = none) :
    (elabFn D ms (wrapFn R)).clauses =
      [([.var "x"], if D.constructorsRun then
          .bind (if heldRunsAt D (D.heldUnder R) false then .run (.var "x") else .ret (.var "x"))
            (slot 0) (.ret (.expression [.symbol "wrap", .var (slot 0)]))
        else .ret (.expression [.symbol "wrap", .var "x"]))] := by
  have hb : elabBody D ms (heldVars [.atom] [.var "x"]) R (E [S "wrap", V "x"]) =
      elabC D ms ["x"] (heldRunsAt D (D.heldUnder R)) true
        (.expression [.symbol "wrap", .var "x"]) := by
    rcases hR with rfl | rfl | rfl <;> rfl
  show [([Atom.var "x"], elabBody D ms (heldVars [.atom] [.var "x"]) R (E [S "wrap", V "x"]))] = _
  rw [hb, elabC.eq_5 _ _ _ _ _ _ _ (by simp) (by simp) (by simp)]
  simp only [List.length_singleton, hw]
  cases hc : D.constructorsRun
  · simp
  · simp only [if_true]
    rw [show List.replicate 1 Ty.undef = [Ty.undef] from rfl, elabArgs.eq_1, if_neg (by decide),
      elabC.eq_1, elabVar_held D (heldRunsAt D (D.heldUnder R)) false (by decide)]
    rfl

theorem runQ_wrapFn (D : Design) (R : Ty) (hR : Unchecked R) (P0 : SProg)
    (hw : modesOf (wrapFn R :: P0) "wrap" 1 = none) (M : Atom) (m : Nat) :
    (runQ D (wrapFn R :: P0) (m + 5) (gQ M)).map (observe D.reportsRefusal) =
      if D.constructorsRun then
        (if heldRunsAt D (D.heldUnder R) false then
          (runQ D (wrapFn R :: P0) (m + 1) M).map fun L =>
            observe D.reportsRefusal (L.map fun a => match a with
              | (.val v, tr) => (.val (E [S "wrap", v]), tr)
              | (.refused d k, tr) => (.refused d k, tr))
        else some [E [S "wrap", M]])
      else some [E [S "wrap", M]] := by
  have hq : elabQuery D (modesOf (wrapFn R :: P0)) (gQ M) = .call "g" [M] := rfl
  have hres : (elabFn D (modesOf (wrapFn R :: P0)) (wrapFn R)).resultCheck = none := by
    rcases hR with rfl | rfl | rfl <;> rfl
  unfold runQ
  rw [hq, exec_call]
  simp only [List.map, inst_nil]
  rw [exec_enter_first _ "g" [M] _ [.var "x"] _ [] [("x", M)] (m + 3) rfl rfl hres
    (wrapFn_clauses D _ R hR hw) rfl fun _ => rfl]
  cases hc : D.constructorsRun
  · simp only [Bool.false_eq_true, if_false]
    rfl
  · simp only [if_true]
    by_cases hr : heldRunsAt D (D.heldUnder R) false
    · rw [if_pos hr, if_pos hr, exec_bind, exec_run, inst_var_head]
      have hk : (fun v => exec (elabProg D (wrapFn R :: P0)) (m + 2)
          (.comp ((slot 0, v) :: [("x", M)])
            (.ret (.expression [.symbol "wrap", .var (slot 0)])))) =
          fun v => some [(.val (E [S "wrap", v]), [])] := by
        funext v
        rw [exec_ret]
        rfl
      rw [hk, show (elabProg D (wrapFn R :: P0)).code M =
        elabQuery D (modesOf (wrapFn R :: P0)) M from rfl]
      cases exec (elabProg D (wrapFn R :: P0)) (m + 1)
          (.comp [] (elabQuery D (modesOf (wrapFn R :: P0)) M)) with
      | none => rfl
      | some L =>
          simp only [Option.bind_some, Option.map_some, continueEach_wrap]
          congr 1
          rw [observe_prefix]
    · rw [if_neg hr, if_neg hr, exec_bind_ret_val, exec_ret]
      simp only [inst_var_head, Option.map_some, List.map, prefixTrace]
      rfl

theorem runQ_wrap_held (D : Design) (hc : D.constructorsRun = false) (P : SProg) (M : Atom)
    (hw : modesOf P "wrap" 1 = none) (n : Nat) :
    runQ D P (n + 1) (wrapQ M) = some [(.val (E [S "wrap", M]), [])] := by
  have hq : elabQuery D (modesOf P) (wrapQ M) = .ret (.expression [.symbol "wrap", M]) := by
    have h1 : elabQuery D (modesOf P) (wrapQ M) =
        (match modesOf P "wrap" 1 with
          | some ps => elabArgs D (modesOf P) [] (fun _ => false) ps [M] 0 [] (.call "wrap")
          | none =>
              if D.constructorsRun then
                elabArgs D (modesOf P) [] (fun _ => false) (List.replicate 1 .undef) [M] 0 []
                  fun items => .ret (.expression (.symbol "wrap" :: items))
              else .ret (.expression [.symbol "wrap", M])) := rfl
    rw [h1, hw]
    simp [hc]
  unfold runQ
  rw [hq, exec_ret, inst_nil]
  rfl

/-- **The plain reading at a field**: `(g M)` with body `(wrap $x)` prints what the written
`(wrap M)` prints. -/
def KeepsFieldReading (D : Design) : Prop :=
  ∀ (P0 : SProg) (R : Ty) (M : Atom) (L : List Atom), Unchecked R →
    modesOf (wrapFn R :: P0) "wrap" 1 = none →
    (Prints D (wrapFn R :: P0) (gQ M) L ↔ Prints D (wrapFn R :: P0) (wrapQ M) L)

theorem keepsFieldReading_of_hold (D : Design) (hc : D.constructorsRun = false) :
    KeepsFieldReading D := by
  intro P0 R M L hR hw
  apply prints_iff_of_shift 5 1
  intro n
  rw [runQ_wrapFn D R hR P0 hw M n, hc, runQ_wrap_held D hc _ M hw n]
  simp [observe]

theorem keepsFieldReading_of_run (D : Design) (hc : D.constructorsRun = true)
    (h : ∀ R, Unchecked R → heldRunsAt D (D.heldUnder R) false = true) :
    KeepsFieldReading D := by
  intro P0 R M L hR hw
  apply prints_iff_of_shift 5 2
  intro n
  rw [runQ_wrapFn D R hR P0 hw M n, hc, if_pos rfl, if_pos (h R hR), runQ_wrap D hc _ M hw n]
  cases runQ D (wrapFn R :: P0) (n + 1) M with
  | none => rfl
  | some A => rfl

/-- The field counterexample under result type `R`: `(g (f a))` prints `(wrap (f a))`, the
written `(wrap (f a))` prints `(wrap 5)`. -/
def FieldSplit (D : Design) (R : Ty) : Prop :=
  answers D (wrapFn R :: [fA]) F (gQ callFA) = some [E [S "wrap", callFA]] ∧
    answers D (wrapFn R :: [fA]) F (wrapQ callFA) = some [E [S "wrap", N 5]]

theorem not_keepsField_of_split {D : Design} {R : Ty} (hR : Unchecked R) (h : FieldSplit D R) :
    ¬ KeepsFieldReading D := fun hk =>
  not_iff_of_prints ⟨F, h.1⟩ ⟨F, h.2⟩ (by decide) (hk [fA] R callFA [E [S "wrap", N 5]] hR rfl)

theorem fieldSplit_undef : ∀ D : Design, D.constructorsRun = true → D.held ≠ .everywhere →
    FieldSplit D .undef := by
  intro D
  rcases D with ⟨held, p, r, a, c, rep⟩
  unfold FieldSplit
  cases held <;> cases p <;> cases r <;> cases a <;> cases c <;> cases rep <;> decide +kernel

theorem fieldSplit_proc : ∀ D : Design, D.constructorsRun = true → D.holdsUnderProc = true →
    FieldSplit D .proc := by
  intro D
  rcases D with ⟨held, p, r, a, c, rep⟩
  unfold FieldSplit
  cases held <;> cases p <;> cases r <;> cases a <;> cases c <;> cases rep <;> decide +kernel

/-- **The plain reading at a field holds exactly when undeclared heads hold their arguments, or a
held parameter runs at every computation position under every computation type.** -/
theorem fieldReading_iff (D : Design) :
    KeepsFieldReading D ↔
      (D.constructorsRun = false ∨ (D.held = .everywhere ∧ D.holdsUnderProc = false)) := by
  constructor
  · intro hk
    cases hc : D.constructorsRun
    · exact .inl rfl
    · refine .inr ⟨?_, ?_⟩
      · by_contra hne
        exact not_keepsField_of_split (.inr (.inl rfl)) (fieldSplit_undef D hc hne) hk
      · cases hp : D.holdsUnderProc
        · rfl
        · exact absurd hk (not_keepsField_of_split (.inl rfl) (fieldSplit_proc D hc hp))
  · rintro (hc | ⟨he, hp⟩)
    · exact keepsFieldReading_of_hold D hc
    · cases hc : D.constructorsRun
      · exact keepsFieldReading_of_hold D hc
      · apply keepsFieldReading_of_run D hc
        rintro R (rfl | rfl | rfl) <;> simp [heldRunsAt, he, Design.heldUnder, hp]

/-- The four combinations: by-name keeps the field reading under both defaults; code value only
when undeclared heads hold their arguments. With evaluated arguments, code value must choose
between the field reading and constructors taking values; by-name keeps both. -/
theorem four_combinations :
    (KeepsFieldReading byName ∧ KeepsConstructorValues byName) ∧
      (KeepsFieldReading byNameHold ∧ ¬ KeepsConstructorValues byNameHold) ∧
      (¬ KeepsFieldReading codeValue ∧ KeepsConstructorValues codeValue) ∧
      (KeepsFieldReading codeValueHold ∧ ¬ KeepsConstructorValues codeValueHold) :=
  ⟨⟨(fieldReading_iff _).mpr (.inr ⟨rfl, rfl⟩), constructorValues_of byName rfl⟩,
    ⟨(fieldReading_iff _).mpr (.inl rfl), constructorValues_hold_breaks.1⟩,
    ⟨fun h => by
        rcases (fieldReading_iff _).mp h with h | ⟨h, _⟩
        · exact absurd h (by decide)
        · exact absurd h (by decide),
      constructorValues_of codeValue rfl⟩,
    ⟨(fieldReading_iff _).mpr (.inl rfl), constructorValues_hold_breaks.2⟩⟩

end Nested

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.EvaluationModes
