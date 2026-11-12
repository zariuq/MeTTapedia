import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.TriangleFootprints.LetEveryRun

/-!
# PeTTa's `let` under tracked incoming bindings: structured patterns and computed values

`AnswerBags.PeTTaEvaluates` and `BoundVariables.PeTTaOpen` quantify over every incoming substitution.
That is right for ground terms, and wrong for an open term past the entry: whether
`(let (pair $a $y) (pair 1 2) b)` binds depends on what the incoming bindings hold for `$y`
(`Controls.incoming_bindings_decide`). This module gives the interface with the bindings fixed.

* `PeTTaUnder atoms w σ u L`: **PeTTa's streaming machine runs the open term `u` under exactly the
  incoming bindings `σ` to the answers `L`**, from every world whose use counter is at least `w`
  (so the names of `σ` and `u`, renamed at earlier uses, stay apart from later ones).
  `under_of_evaluates`, `under_of_open`, `under_of_openN` embed the earlier interfaces;
  `under_variable` runs a bound variable.
* `PeTTaReturns atoms σ u d`: the value term `u` returns `d` with the bindings `σ` unchanged;
  `returns_value` gives it for every value tree (constructors over items, nested), a computed value.
* `petta_let_under`: **`(let p v b)` under `σ`, for any pattern `p`**: when `v` returns `d` and PeTTa's
  binding of `p` with `d` over `σ` gives `σ'`, the answers are those of `b` under `σ'`.
  `petta_let_clash`: when the binding clashes there is no answer.
* `values_of_under`, `petta_let_entry`: from PeTTa's entry.

## Controls

On HE's `let` and `if` programs (`LetEveryRun.Controls.letIfRows`):
* `Controls.swap_values` (positive, a structured pattern): `(let (pair $a $b) (pair 1 2) (pair $b $a))`
  yields `[(pair 2 1)]`; HE's `metta-repl` answers `[(pair 2 1)]`.
* `Controls.computed_value` (positive, a computed value read back): `(let $x (pair 1 2) $x)` yields
  `[(pair 1 2)]`; HE's `metta-repl` answers `[(pair 1 2)]`.
* `Controls.nonlinear_none` (negative, a clash): `(let (pair $a $a) (pair 1 2) yes)` yields `[]`; HE's
  `metta-repl` answers `[]`.
* `Controls.incoming_bindings_decide` (negative, the bindings matter): the same `let` has the answer
  `(pair 1 2)` under the empty bindings and none under bindings holding `$y := 7`; no statement over
  all incoming bindings is true of it.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.TriangleFootprints

namespace LetPeTTaBindings

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.HE.Spec.Eval
open Mettapedia.Languages.MeTTa.PeTTa
open Mettapedia.Languages.ProcessCalculi.MORK (Subst isGroundAtom applySubst)
open ServiceFootprints EntryToQuery AnswerBags EveryRun BoundVariables NestedValues

variable {dispatch : GroundedDispatch}

/-! ## The interface -/

/-- **PeTTa's streaming machine runs the open term `u` under the incoming bindings `σ` to the answers
`L`**, under any frames that deliver each of them, from every world over the translation's store
whose use counter is at least `w`. -/
def PeTTaUnder (atoms : List Atom) (w : Nat) (σ : Subst) (u : Atom) (L : List Atom) : Prop :=
  ∀ (frames : List Streaming.Frame) (K : Atom → List Atom), (∀ v ∈ L, Delivers atoms frames K v) →
  ∀ (world : Streaming.World), world.state = store atoms → world.privateCode = [] →
    w ≤ world.uses →
    ∀ (older : List Streaming.Job) (answers : List Unifying.Answer) (next : Nat),
      ∃ (uses : Nat) (out : List Unifying.Answer), world.uses ≤ uses ∧
        out.map (fun answer => Unifying.resolve answer.bindings answer.value) = L.flatMap K ∧
        PeTTaRuns.PSteps (translate atoms)
          ⟨world, .execute ⟨.evaluate σ u, frames⟩ :: older, answers, next⟩
          ⟨{world with uses := uses}, older, answers ++ out, next⟩

/-- The bindings are ground and leave every use from `w` on fresh. -/
structure Tracked (w : Nat) (σ : Subst) : Prop where
  range : Unifying.GroundRange σ
  fresh : ∀ k, Unifying.FreshFor (w + k) σ

theorem Tracked.at {w : Nat} {σ : Subst} (tracked : Tracked w σ) {uses : Nat} (atLeast : w ≤ uses) :
    ∀ k, Unifying.FreshFor (uses + k) σ := by
  intro k
  have same : uses + k = w + (uses - w + k) := by omega
  rw [same]
  exact tracked.fresh _

/-- A ground term evaluated under every bindings is evaluated under these. -/
theorem under_of_evaluates {atoms : List Atom} {w : Nat} {σ : Subst} (tracked : Tracked w σ)
    {t : Atom} {L : List Atom} (evaluates : PeTTaEvaluates atoms t L) : PeTTaUnder atoms w σ t L :=
  fun frames K deliver world state privateCode atLeast older answers next =>
    evaluates frames K deliver world σ state privateCode tracked.range (tracked.at atLeast) older
      answers next

/-- An open presentation of `t` under `σ` runs to the answers of `t`. -/
theorem under_of_open {atoms : List Atom} {w : Nat} {σ : Subst} (tracked : Tracked w σ) {t b : Atom}
    {L : List Atom} (evaluates : PeTTaOpen atoms t L) (presented : Presents σ b t) :
    PeTTaUnder atoms w σ b L :=
  fun frames K deliver world state privateCode atLeast older answers next =>
    evaluates frames K deliver world σ state privateCode tracked.range (tracked.at atLeast) b
      presented older answers next

/-- A flat or value presentation of `t` under `σ` runs to the answers of `t`. -/
theorem under_of_openN {atoms : List Atom} {w : Nat} {σ : Subst} (tracked : Tracked w σ) {t b : Atom}
    {L : List Atom} (evaluates : PeTTaOpenN dispatch atoms t L)
    (presented : PresentsN dispatch atoms σ b t) : PeTTaUnder atoms w σ b L :=
  fun frames K deliver world state privateCode atLeast older answers next =>
    evaluates frames K deliver world σ state privateCode tracked.range (tracked.at atLeast) b
      presented older answers next

/-- **A variable runs to the value the bindings hold for it.** -/
theorem under_variable {atoms : List Atom} {w : Nat} {σ : Subst} (tracked : Tracked w σ) {x : String}
    {v : Atom} (bound : Unifying.resolve σ (.var x) = v) : PeTTaUnder atoms w σ (.var x) [v] := by
  intro frames K deliver world state privateCode atLeast older answers next
  obtain ⟨uses, out, grown, valuesOut, path⟩ := deliver v List.mem_cons_self world σ state
    privateCode tracked.range (tracked.at atLeast) older answers next
  have step : Streaming.Transition (translate atoms)
      ⟨world, .execute ⟨.evaluate σ (.var x), frames⟩ :: older, answers, next⟩
      ⟨world, .execute ⟨.returned [⟨Unifying.resolve σ (.var x), σ⟩], frames⟩ :: older, answers,
        next⟩ := .phase rfl rfl (.value_variable rfl) (.plain rfl)
  rw [bound] at step
  exact ⟨uses, out, grown, by simp [valuesOut], .head step path⟩

/-- **PeTTa returns the value `d` for the term `u` under `σ`, with the bindings unchanged.** -/
def PeTTaReturns (atoms : List Atom) (σ : Subst) (u d : Atom) : Prop :=
  ∀ (world : Streaming.World) (frames : List Streaming.Frame) (older : List Streaming.Job)
    (answers : List Unifying.Answer) (next : Nat), world.privateCode = [] →
    PeTTaRuns.PSteps (translate atoms)
      ⟨world, .execute ⟨.evaluate σ u, frames⟩ :: older, answers, next⟩
      ⟨world, .execute ⟨.returned [⟨d, σ⟩], frames⟩ :: older, answers, next⟩

/-- **A value tree returns its value** (`NestedValues.value_run`): constructors over items, at any
depth, each variable resolved when reached. -/
theorem returns_value {atoms : List Atom} {σ : Subst} (range : Unifying.GroundRange σ) {u d : Atom}
    (presented : ValuePresents dispatch atoms σ u d) : PeTTaReturns atoms σ u d := by
  intro world frames older answers next privateCode
  have run := value_run world privateCode σ range presented.tree presented.bound frames older
    answers next
  rw [presented.instantiates] at run
  exact run

/-! ## `let` under tracked bindings -/

/-- **PeTTa's `let` with any pattern, under the incoming bindings `σ`.** When the value term returns
`d` with `σ` unchanged and PeTTa's binding of the pattern with `d` over `σ` succeeds with `σ'`, the
`let` runs to the answers of its body under `σ'`. -/
theorem petta_let_under {atoms : List Atom} {w : Nat} {σ σ' : Subst} {p v b d : Atom}
    {L : List Atom} (returns : PeTTaReturns atoms σ v d)
    (bound : Unifying.unifyBinding σ p d = .ok σ') (body : PeTTaUnder atoms w σ' b L) :
    PeTTaUnder atoms w σ (.expression [.symbol "let", p, v, b]) L := by
  intro frames K deliver world state privateCode atLeast older answers next
  obtain ⟨uses, out, grown, valuesOut, path⟩ := body frames K deliver world state privateCode
    atLeast older answers next
  have continued : Unifying.bindAnswers p b [⟨d, σ⟩] = some [.evaluate σ' b] := by
    simp [Unifying.bindAnswers, bound]
  refine ⟨uses, out, grown, valuesOut, ?_⟩
  refine .head (LetPeTTa.let_enter_step world σ p v b frames older answers next) ?_
  refine (returns world (.source (.bind p b) :: frames) older answers next privateCode).trans ?_
  refine .head (LetPeTTa.binding_return_step world ⟨d, σ⟩ p b continued frames older answers
    next) ?_
  refine .head (PeTTaRuns.alternatives world _ frames older answers next) ?_
  exact path

/-- **A `let` whose pattern clashes with its value has no answer.** -/
theorem petta_let_clash {atoms : List Atom} {w : Nat} {σ : Subst} {p v b d : Atom}
    (returns : PeTTaReturns atoms σ v d) (clash : Unifying.unifyBinding σ p d = .clash) :
    PeTTaUnder atoms w σ (.expression [.symbol "let", p, v, b]) [] := by
  intro frames K _ world _ privateCode _ older answers next
  have continued : Unifying.bindAnswers p b [⟨d, σ⟩] = some [] := by
    simp [Unifying.bindAnswers, clash]
  refine ⟨world.uses, [], le_rfl, rfl, ?_⟩
  rw [List.append_nil]
  refine .head (LetPeTTa.let_enter_step world σ p v b frames older answers next) ?_
  refine (returns world (.source (.bind p b) :: frames) older answers next privateCode).trans ?_
  refine .head (LetPeTTa.binding_return_step world ⟨d, σ⟩ p b continued frames older answers
    next) ?_
  exact .single (PeTTaRuns.alternatives world [] frames older answers next)

/-- **From PeTTa's entry**: a term whose renamed form runs under the empty bindings to `L` yields `L`
from some fuel on. -/
theorem values_of_under {atoms : List Atom} {c : Atom} {L : List Atom}
    (clean : ∀ a ∈ L, Answerable a) (under : PeTTaUnder atoms 1 [] (Unifying.rename 0 c) L) :
    ∃ N, ∀ n, N ≤ n → Streaming.values (Streaming.advance (translate atoms) n
      (Streaming.enter { state := store atoms } c)) = L := by
  obtain ⟨uses, out, _, valuesOut, path⟩ := under [] (fun v => [v])
    (fun v member => PeTTaRuns.delivers_root atoms (clean v member))
    { state := store atoms, uses := 1 } rfl rfl le_rfl [] [] 0
  obtain ⟨N, reached⟩ := (Streaming.path_iff_advance _ _ _).mp path
  refine ⟨N, fun n bigger => ?_⟩
  have entered : Streaming.enter { state := store atoms } c =
      ⟨{ state := store atoms, uses := 1 }, [.execute ⟨.evaluate [] (Unifying.rename 0 c), []⟩], [],
        0⟩ := rfl
  rw [entered, show n = N + (n - N) by omega, Streaming.advance_add, reached, advance_finished]
  simpa [Streaming.values, flatMap_root] using valuesOut

/-- **PeTTa's `let` with any pattern, from its entry.** -/
theorem petta_let_entry {atoms : List Atom} {p v b d : Atom} {σ' : Subst} {L : List Atom}
    (clean : ∀ a ∈ L, Answerable a)
    (returns : PeTTaReturns atoms [] (Unifying.rename 0 v) d)
    (bound : Unifying.unifyBinding [] (Unifying.rename 0 p) d = .ok σ')
    (body : PeTTaUnder atoms 1 σ' (Unifying.rename 0 b) L) :
    ∃ N, ∀ n, N ≤ n → Streaming.values (Streaming.advance (translate atoms) n
      (Streaming.enter { state := store atoms } (.expression [.symbol "let", p, v, b]))) = L := by
  apply values_of_under clean
  have renamed : Unifying.rename 0 (.expression [.symbol "let", p, v, b]) =
      .expression [.symbol "let", Unifying.rename 0 p, Unifying.rename 0 v, Unifying.rename 0 b] := by
    simp [Unifying.rename, Unifying.rename.renameList]
  rw [renamed]
  exact petta_let_under returns bound body

/-! ## Controls -/

namespace Controls

open WholeRunWords.Double (noHost)
open AnswerBags.Controls (sym app)
open LetEveryRun.Controls (letIfRows)

abbrev one : Atom := .grounded (.int 1)
abbrev two : Atom := .grounded (.int 2)

theorem pair_constructor : ConstructorHead noHost letIfRows "pair" :=
  ⟨.symbol (by decide) (by decide), by decide +kernel, fun impossible => impossible, by decide,
    by decide, by decide, by decide, by decide +kernel⟩

/-- `(pair 1 2)` is a value tree that presents itself under any bindings. -/
theorem pair_presents (σ : Subst) : ValuePresents noHost letIfRows σ (app "pair" [one, two])
    (app "pair" [one, two]) where
  tree := .node pair_constructor fun u member => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> exact .item (.grounded _)
  bound := fun x member => by
    simp [Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation.TypeSubst.typeVars,
      Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation.TypeSubst.typeVarsList] at member
  instantiates := by
    simp [applySubst, applySubst.applySubstList]

theorem pair_ordinary : Ordinary noHost letIfRows "pair" [two, one] :=
  ⟨.symbol (by decide) (by decide), (fun a member => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl <;> exact .grounded _), (by decide +kernel),
    (fun impossible => impossible), (by decide), (by decide), (by decide), (by decide), (by decide),
    (by decide)⟩

/-- The bindings PeTTa's binding frame computes for `(pair $a $b)` against `(pair 1 2)`. -/
abbrev swapBindings : Subst := [("b#0", two), ("a#0", one)]

theorem swap_tracked : Tracked 1 swapBindings :=
  ⟨fun binding member => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl <;> rfl,
    PeTTaRuns.freshFor_renamed (use := 0) (next := 1) (bound := [("b", two), ("a", one)]) (σ := [])
      (by decide) (fun _ _ => rfl)⟩

/-- **Positive control, a structured pattern**: PeTTa on
`(let (pair $a $b) (pair 1 2) (pair $b $a))` yields `[(pair 2 1)]` from some fuel on; HE's
`metta-repl` answers `[(pair 2 1)]`. -/
theorem swap_values : ∃ N, ∀ n, N ≤ n → Streaming.values (Streaming.advance (translate letIfRows) n
    (Streaming.enter { state := store letIfRows }
      (.expression [.symbol "let", app "pair" [.var "a", .var "b"], app "pair" [one, two],
        app "pair" [.var "b", .var "a"]]))) = [app "pair" [two, one]] := by
  refine petta_let_entry (d := app "pair" [one, two]) (σ' := swapBindings) (fun a member => ?_)
    (returns_value (dispatch := noHost) (fun _ member => by cases member) (pair_presents [])) rfl
    (under_of_open swap_tracked
      (petta_open_constructor pair_ordinary (by decide +kernel))
      (.call "pair" rfl (.cons ⟨.grounded _, Or.inr ⟨"b#0", rfl, rfl⟩⟩
        (.cons ⟨.grounded _, Or.inr ⟨"a#0", rfl, rfl⟩⟩ .nil))))
  rw [List.mem_singleton] at member
  subst member
  exact app_answerable (.symbol (by decide) (by decide)) (fun a member => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> exact answerable_of_data (.grounded _))

theorem value_tracked : Tracked 1 [("x#0", app "pair" [one, two])] :=
  ⟨fun binding member => by
      rw [List.mem_singleton] at member
      subst member
      rfl,
    PeTTaRuns.freshFor_renamed (use := 0) (next := 1) (bound := [("x", app "pair" [one, two])])
      (σ := []) (by decide) (fun _ _ => rfl)⟩

/-- **Positive control, a computed value read back**: PeTTa on `(let $x (pair 1 2) $x)` yields
`[(pair 1 2)]`: the value is built by the machine, bound whole, and read through the bindings. -/
theorem computed_value : ∃ N, ∀ n, N ≤ n → Streaming.values (Streaming.advance (translate letIfRows) n
    (Streaming.enter { state := store letIfRows }
      (.expression [.symbol "let", .var "x", app "pair" [one, two], .var "x"]))) =
        [app "pair" [one, two]] := by
  refine petta_let_entry (d := app "pair" [one, two]) (σ' := [("x#0", app "pair" [one, two])])
    (fun a member => ?_)
    (returns_value (dispatch := noHost) (fun _ member => by cases member) (pair_presents [])) rfl
    (under_variable value_tracked rfl)
  rw [List.mem_singleton] at member
  subst member
  exact app_answerable (.symbol (by decide) (by decide)) (fun a member => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> exact answerable_of_data (.grounded _))

/-- **Negative control, a clash**: PeTTa on `(let (pair $a $a) (pair 1 2) yes)` yields nothing; HE's
`metta-repl` answers `[]`. -/
theorem nonlinear_none : ∃ N, ∀ n, N ≤ n → Streaming.values (Streaming.advance (translate letIfRows) n
    (Streaming.enter { state := store letIfRows }
      (.expression [.symbol "let", app "pair" [.var "a", .var "a"], app "pair" [one, two],
        sym "yes"]))) = [] := by
  apply values_of_under (fun a member => by cases member)
  have renamed : Unifying.rename 0 (.expression [.symbol "let", app "pair" [.var "a", .var "a"],
      app "pair" [one, two], sym "yes"]) =
      .expression [.symbol "let", app "pair" [.var "a#0", .var "a#0"], app "pair" [one, two],
        sym "yes"] := by decide
  rw [renamed]
  exact petta_let_clash (d := app "pair" [one, two])
    (returns_value (dispatch := noHost) (fun _ member => by cases member) (pair_presents [])) rfl

/-- **Negative control, the incoming bindings decide**: the binding of `(pair $a $y)` with
`(pair 1 2)` succeeds over the empty bindings and clashes over bindings holding `$y := 7`. So the
`let` below has one answer under the first and none under the second (`petta_let_under`,
`petta_let_clash`); a statement over all incoming bindings is false for it. -/
theorem incoming_bindings_decide :
    (∃ σ', Unifying.unifyBinding [] (app "pair" [.var "a#0", .var "y#0"]) (app "pair" [one, two]) =
      .ok σ') ∧
    Unifying.unifyBinding [("y#0", .grounded (.int 7))] (app "pair" [.var "a#0", .var "y#0"])
      (app "pair" [one, two]) = .clash :=
  ⟨⟨_, rfl⟩, rfl⟩

/-- Under the bindings holding `$y := 7`, the `let` has no answer. -/
theorem bound_incoming_none (w : Nat) (b : Atom) :
    PeTTaUnder letIfRows w [("y#0", .grounded (.int 7))]
      (.expression [.symbol "let", app "pair" [.var "a#0", .var "y#0"], app "pair" [one, two], b])
      [] :=
  petta_let_clash (d := app "pair" [one, two])
    (returns_value (dispatch := noHost) (fun binding member => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      subst member
      rfl) (pair_presents _)) incoming_bindings_decide.2

/-- The bindings PeTTa's binding frame computes for `$x` against `yes`. -/
abbrev yesBindings : Subst := [("x#0", sym "yes")]

theorem yes_tracked : Tracked 1 yesBindings :=
  ⟨fun binding member => by
      rw [List.mem_singleton] at member
      subst member
      rfl,
    PeTTaRuns.freshFor_renamed (use := 0) (next := 1) (bound := [("x", sym "yes")]) (σ := [])
      (by decide) (fun _ _ => rfl)⟩

theorem yes_presents : ValuePresents noHost letIfRows [] (sym "yes") (sym "yes") where
  tree := .item (.symbol _)
  bound := fun x member => by
    simp [Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation.TypeSubst.typeVars] at member
  instantiates := by decide

/-- The nested template presents its instance as a value tree under PeTTa's binding of `$x`. -/
theorem nested_presents : ValuePresents noHost letIfRows yesBindings
    (app "pair" [.var "x#0", app "pair" [.var "x#0", sym "no"]])
    (app "pair" [sym "yes", app "pair" [sym "yes", sym "no"]]) where
  tree := .node pair_constructor fun u member => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact .item (.var _)
    · exact .node pair_constructor fun u' member' => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at member'
        rcases member' with rfl | rfl
        · exact .item (.var _)
        · exact .item (.symbol _)
  bound := fun x member => by
    have isX : x = "x#0" := by
      simpa [Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation.TypeSubst.typeVars,
        Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation.TypeSubst.typeVarsList] using member
    subst isX
    exact .symbol "yes"
  instantiates := by decide

/-- **Positive control, both dialects, a nested template**: on `(let $x yes (pair $x (pair $x no)))`
a complete HE run exists, every complete HE run publishes `(pair yes (pair yes no))`, every HE run
finishes (`LetEveryRun.Controls.nested_template_every_run`), and PeTTa yields the same answer from
some fuel on, through the tracked interface. -/
theorem nested_agree (policy : Completed.Policy) :
    (ScopedTransfer.Publishes noHost Completed.scopedLookup policy
        (Mettapedia.Languages.MeTTa.HE.Space.ofList letIfRows)
        (LetSource.letCall "x" (sym "yes") (app "pair" [.var "x", app "pair" [.var "x", sym "no"]]))
        [app "pair" [sym "yes", app "pair" [sym "yes", sym "no"]]] ∧
      ScopedTransfer.Finishes noHost Completed.scopedLookup policy
        (Mettapedia.Languages.MeTTa.HE.Space.ofList letIfRows)
        (LetSource.letCall "x" (sym "yes") (app "pair" [.var "x", app "pair" [.var "x", sym "no"]]))
        [app "pair" [sym "yes", app "pair" [sym "yes", sym "no"]]]) ∧
    ∃ N, ∀ n, N ≤ n → Streaming.values (Streaming.advance (translate letIfRows) n
      (Streaming.enter { state := store letIfRows }
        (LetSource.letCall "x" (sym "yes") (app "pair" [.var "x", app "pair" [.var "x", sym "no"]])))) =
          [app "pair" [sym "yes", app "pair" [sym "yes", sym "no"]]] := by
  refine ⟨LetEveryRun.Controls.nested_template_every_run policy, ?_⟩
  refine petta_let_entry (d := sym "yes") (σ' := yesBindings) (fun a member => ?_)
    (returns_value (dispatch := noHost) (fun _ member => by cases member) yes_presents) rfl
    (under_of_openN yes_tracked (petta_openN_value (dispatch := noHost) pair_constructor)
      (Or.inr nested_presents))
  rw [List.mem_singleton] at member
  subst member
  exact app_answerable (.symbol (by decide) (by decide)) (fun a member => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact answerable_of_data (.symbol (by decide) (by decide))
    · exact app_answerable (.symbol (by decide) (by decide)) (fun a member => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl <;>
          exact answerable_of_data (.symbol (by decide) (by decide))))

end Controls

#print axioms Controls.nested_agree
#print axioms under_of_open
#print axioms under_variable
#print axioms returns_value
#print axioms petta_let_under
#print axioms petta_let_clash
#print axioms values_of_under
#print axioms petta_let_entry
#print axioms Controls.swap_values
#print axioms Controls.computed_value
#print axioms Controls.nonlinear_none
#print axioms Controls.incoming_bindings_decide
#print axioms Controls.bound_incoming_none

end LetPeTTaBindings

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.TriangleFootprints
