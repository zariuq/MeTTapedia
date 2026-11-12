import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.TriangleFootprints.LetPeTTaTemplates

/-!
# Computed values that are calls: PeTTa's `let` and `if` on a call that binds no name

`LetPeTTaBindings.PeTTaReturns` describes a value term that returns its value with the bindings and
the world unchanged: an item or a value tree. A call of a defined function is not such a term: PeTTa
renames the clause apart, which uses up a use number, and binds the clause's names in front of the
incoming bindings. This module covers the calls whose matching clause binds no name (a nullary
function, or a clause whose parameters are literals): the bindings come back unchanged and only the
use counter has grown.

* `PeTTaReturnsLater atoms w σ u d`: `u` returns `d` under `σ` with the bindings unchanged, at a use
  counter that may have grown; `later_of_returns` embeds `PeTTaReturns`.
* `returns_call`: **a call on data whose one matching clause binds no name and has a data body
  returns that body**, with the bindings unchanged, one use per candidate clause later.
* `petta_let_later`, `petta_if_later`: PeTTa's `let` (any pattern) and `if` under tracked bindings,
  with a value or a condition that returns later.

A clause that binds names returns with those names, renamed, in front of the incoming bindings; the
frames then receive extended bindings. That case needs the interface to be monotone over such
extensions and is not covered here.

## Controls

On HE's `let` and `if` programs with `(= (isTrue) True)`:
* `Controls.call_value` (positive): `(let $x (isTrue) (if $x yes no))` yields `[yes]`: the value is a
  call, the pattern binds its answer, and the template reads it in `if`'s condition. HE's
  `metta-repl` answers `[yes]`.
* `Controls.call_condition` (positive): `(if (isTrue) yes no)` yields `[yes]` through
  `petta_if_later`.
* `Controls.call_value_not_no` (negative): PeTTa does not yield `[no]` on the first.
* `Controls.binding_clause_outside` (negative, the boundary): for `(= (same $a) $a)` the clause of
  `(same 5)` is renamed with a binding in front of the incoming ones, so `returns_call`'s premise
  fails for it.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.TriangleFootprints

namespace LetPeTTaCalls

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.HE.Spec.Eval
open Mettapedia.Languages.MeTTa.PeTTa
open Mettapedia.Languages.ProcessCalculi.MORK (Subst isGroundAtom applySubst)
open ServiceFootprints EntryToQuery AnswerBags EveryRun BoundVariables NestedValues LetPeTTaBindings
  LetPeTTaTemplates

variable {dispatch : GroundedDispatch}

/-! ## Returning at a later use -/

/-- **PeTTa returns the value `d` for the term `u` under `σ` with the bindings unchanged, at a use
counter that may have grown**, from every world over the translation's store whose use counter is at
least `w`. -/
def PeTTaReturnsLater (atoms : List Atom) (w : Nat) (σ : Subst) (u d : Atom) : Prop :=
  ∀ (world : Streaming.World) (frames : List Streaming.Frame) (older : List Streaming.Job)
    (answers : List Unifying.Answer) (next : Nat), world.state = store atoms →
    world.privateCode = [] → w ≤ world.uses →
    ∃ uses : Nat, world.uses ≤ uses ∧
      PeTTaRuns.PSteps (translate atoms)
        ⟨world, .execute ⟨.evaluate σ u, frames⟩ :: older, answers, next⟩
        ⟨{world with uses := uses}, .execute ⟨.returned [⟨d, σ⟩], frames⟩ :: older, answers, next⟩

/-- A term that returns with the world unchanged returns later. -/
theorem later_of_returns {atoms : List Atom} {w : Nat} {σ : Subst} {u d : Atom}
    (returns : PeTTaReturns atoms σ u d) : PeTTaReturnsLater atoms w σ u d :=
  fun world frames older answers next _ privateCode _ =>
    ⟨world.uses, le_rfl, returns world frames older answers next privateCode⟩

/-- **A call on data whose one matching clause binds no name and has a data body returns that
body**: PeTTa enters the call, holds its arguments, selects the clauses of the head (one use each),
and the one that matches evaluates its body under the incoming bindings. -/
theorem returns_call {atoms : List Atom} {f : String} {args : List Atom}
    (ordinary : Ordinary dispatch atoms f args)
    (defined : ∃ e ∈ atoms.filterMap LiveEquations.equationOfRow, e.head = f ∧
      e.arguments.length = args.length)
    {d : Atom} (data : DataAtom d)
    (single : ∀ (σ : Subst) (use : Nat), Unifying.renamedClauses σ args use
      (Unifying.candidates (atoms.filterMap LiveEquations.equationOfRow) f args.length) =
        [.evaluate σ d])
    {w : Nat} {σ : Subst} (tracked : Tracked w σ) :
    PeTTaReturnsLater atoms w σ (.expression (.symbol f :: args)) d := by
  intro world frames older answers next state privateCode atLeast
  have fresh := tracked.at atLeast
  have groundArgs : ∀ v ∈ args, isGroundAtom v = true :=
    fun v member => (answerable_of_data (ordinary.arguments v member)).ground
  have callable : (Mettapedia.Languages.MeTTa.PeTTa.Eval.ioHead f || StdLib.known f ||
      (Unifying.codeRegistry (translate atoms) world.privateCode).equations.any (·.head == f)) =
      true := by
    obtain ⟨e, live, head, _⟩ := defined
    rw [privateCode, ordinary.notIO, ordinary.notNative]
    simp only [Unifying.codeRegistry, List.nil_append, translate_equations, Bool.false_or]
    exact List.any_eq_true.mpr ⟨e, live, by simp [head]⟩
  obtain ⟨e, live, head, arity⟩ := defined
  have liveEquations : Unifying.codeEquations world.state world.privateCode =
      atoms.filterMap LiveEquations.equationOfRow := by
    rw [state, privateCode]
    simp only [Unifying.codeEquations, List.nil_append, LiveEquations.liveEquations, store_core]
  have arityKnown : args.length ∈ Mettapedia.Languages.MeTTa.PeTTa.Eval.arities
      (Unifying.codeRegistry (translate atoms) world.privateCode) f := by
    rw [privateCode]
    simp only [Mettapedia.Languages.MeTTa.PeTTa.Eval.arities, Unifying.codeRegistry, List.nil_append,
      translate_equations]
    exact List.mem_map.mpr ⟨e, List.mem_filter.mpr ⟨live, by simp [head]⟩, arity⟩
  have applied : Unifying.application (Unifying.codeRegistry (translate atoms) world.privateCode)
      (Unifying.codeEquations world.state world.privateCode) f
      (args.map (Unifying.resolve σ)) σ world.uses =
      some (.sequence (Unifying.renamedClauses σ args world.uses
        (Unifying.candidates (atoms.filterMap LiveEquations.equationOfRow) f args.length)) [],
        (Unifying.candidates (atoms.filterMap LiveEquations.equationOfRow) f args.length).length) := by
    rw [PeTTaRuns.map_resolve_ground σ groundArgs, liveEquations]
    unfold Unifying.application
    rw [if_pos arityKnown]
    simp only
    rw [Unifying.selections_eq_renamedClauses tracked.range groundArgs world.uses _ fresh]
    rfl
  refine ⟨world.uses + (Unifying.candidates (atoms.filterMap LiveEquations.equationOfRow) f
    args.length).length, Nat.le_add_right _ _, ?_⟩
  refine .head (PeTTaRuns.call_enter world σ ordinary.notCollapse ordinary.notOnce
    ordinary.notControl callable frames older answers next) ?_
  have entered := PeTTaRuns.arguments_data (registry := translate atoms) world σ (.function f)
    (fun index => argumentIsRaw_false ordinary.notNative ordinary.untyped index) frames older
    answers next args [] 0 ordinary.arguments
  rw [List.nil_append] at entered
  refine entered.trans ?_
  refine .head (PeTTaRuns.apply_equations world σ args (0 + args.length) ordinary.notIO
    ordinary.notNative applied frames older answers next) ?_
  refine .head (PeTTaRuns.alternatives _ _ frames older answers next) ?_
  rw [single σ world.uses]
  simp only [List.map_cons, List.map_nil, List.singleton_append]
  exact .single (PeTTaRuns.evaluate_data _ σ data frames older answers next)

/-! ## `let` and `if` on a term that returns later -/

/-- **PeTTa's `let` with any pattern, under the incoming bindings `σ`, on a value that returns
later.** -/
theorem petta_let_later {atoms : List Atom} {w : Nat} {σ σ' : Subst} {p v b d : Atom}
    {L : List Atom} (returns : PeTTaReturnsLater atoms w σ v d)
    (bound : Unifying.unifyBinding σ p d = .ok σ') (body : PeTTaUnder atoms w σ' b L) :
    PeTTaUnder atoms w σ (.expression [.symbol "let", p, v, b]) L := by
  intro frames K deliver world state privateCode atLeast older answers next
  obtain ⟨uses, grown, run⟩ := returns world (.source (.bind p b) :: frames) older answers next
    state privateCode atLeast
  obtain ⟨uses', out, grown', valuesOut, path⟩ := body frames K deliver {world with uses := uses}
    state privateCode (atLeast.trans grown) older answers next
  have continued : Unifying.bindAnswers p b [⟨d, σ⟩] = some [.evaluate σ' b] := by
    simp [Unifying.bindAnswers, bound]
  refine ⟨uses', out, grown.trans grown', valuesOut, ?_⟩
  refine .head (LetPeTTa.let_enter_step world σ p v b frames older answers next) ?_
  refine run.trans ?_
  refine .head (LetPeTTa.binding_return_step {world with uses := uses} ⟨d, σ⟩ p b continued frames
    older answers next) ?_
  refine .head (PeTTaRuns.alternatives {world with uses := uses} _ frames older answers next) ?_
  exact path

/-- **PeTTa's `if` under the incoming bindings `σ`, on a condition that returns a Boolean later.** -/
theorem petta_if_later {atoms : List Atom} {w : Nat} {σ : Subst} {c y n : Atom} {b : Bool}
    {L : List Atom} (returns : PeTTaReturnsLater atoms w σ c (.grounded (.bool b)))
    (taken : PeTTaUnder atoms w σ (IfBranches.pick b y n) L) :
    PeTTaUnder atoms w σ (IfComputed.callC c y n) L := by
  intro frames K deliver world state privateCode atLeast older answers next
  obtain ⟨uses, grown, run⟩ := returns world (.source (.branch y n) :: frames) older answers next
    state privateCode atLeast
  obtain ⟨uses', out, grown', valuesOut, path⟩ := taken frames K deliver {world with uses := uses}
    state privateCode (atLeast.trans grown) older answers next
  have chosen : (if Atom.grounded (.bool b) == Effects.boolean true then y else n) =
      IfBranches.pick b y n := by
    cases b <;> rfl
  refine ⟨uses', out, grown.trans grown', valuesOut, ?_⟩
  refine .head (IfComputed.if_enter_step world σ c y n frames older answers next) ?_
  refine run.trans ?_
  refine .head (IfComputed.branch_return_step {world with uses := uses} ⟨.grounded (.bool b), σ⟩
    y n frames older answers next) ?_
  refine .head (PeTTaRuns.alternatives {world with uses := uses} _ frames older answers next) ?_
  simp only [chosen, List.map_cons, List.map_nil, List.singleton_append]
  exact path

/-! ## Controls -/

namespace Controls

open WholeRunWords.Double (noHost)
open AnswerBags.Controls (sym app rule)
open LetEveryRun.Controls (letIfRows)
open LetPeTTaTemplates.Controls (boolBindings bool_tracked if_template_under template_renamed)

/-- HE's `let` and `if` programs with `(= (isTrue) True)`. -/
abbrev callRows : List Atom := letIfRows ++ [rule (app "isTrue" []) (.grounded (.bool true))]

theorem isTrue_ordinary : Ordinary noHost callRows "isTrue" [] :=
  ⟨.symbol (by decide) (by decide), (fun _ member => by cases member), (by decide +kernel),
    (fun impossible => impossible), (by decide), (by decide), (by decide), (by decide),
    (by decide), (by decide)⟩

theorem isTrue_defined : ∃ e ∈ callRows.filterMap LiveEquations.equationOfRow,
    e.head = "isTrue" ∧ e.arguments.length = ([] : List Atom).length :=
  ⟨⟨"isTrue", [], .grounded (.bool true)⟩,
    List.mem_filterMap.mpr ⟨rule (app "isTrue" []) (.grounded (.bool true)),
      List.mem_append_right _ (List.mem_singleton_self _), rfl⟩, rfl, rfl⟩

theorem isTrue_single (σ : Subst) (use : Nat) : Unifying.renamedClauses σ [] use
    (Unifying.candidates (callRows.filterMap LiveEquations.equationOfRow) "isTrue"
      ([] : List Atom).length) = [.evaluate σ (.grounded (.bool true))] := by
  have chosen : Unifying.candidates (callRows.filterMap LiveEquations.equationOfRow) "isTrue"
      ([] : List Atom).length = [⟨"isTrue", [], .grounded (.bool true)⟩] := rfl
  rw [chosen]
  simp [Unifying.renamedClauses, SpaceSemantics.matchValue.matchValues, Unifying.renameKeys,
    Unifying.rename]

/-- `(isTrue)` returns `True` with the bindings unchanged, one use later. -/
theorem isTrue_returns {w : Nat} {σ : Subst} (tracked : Tracked w σ) :
    PeTTaReturnsLater callRows w σ (app "isTrue" []) (.grounded (.bool true)) :=
  returns_call isTrue_ordinary isTrue_defined (.grounded _) isTrue_single tracked

theorem empty_tracked : Tracked 1 ([] : Subst) where
  range := fun _ member => by cases member
  fresh := fun _ _ => rfl

theorem yes_answerable : ∀ a ∈ [sym "yes"], Answerable a := by
  intro a member
  rw [List.mem_singleton] at member
  subst member
  exact answerable_of_data (.symbol (by decide) (by decide))

/-- The renamed template under PeTTa's binding of `$x` to `True`, on this program. -/
theorem template_under : PeTTaUnder callRows 1 (boolBindings true)
    (IfComputed.callC (.var "x#0") (sym "yes") (sym "no")) [sym "yes"] :=
  petta_if_under (b := true) (returns_item ⟨.grounded _, Or.inr ⟨"x#0", rfl, rfl⟩⟩)
    (under_of_evaluates (bool_tracked true)
      (PeTTaRuns.petta_data callRows (.symbol (by decide) (by decide))))

/-- **Positive control, a value that is a call**: PeTTa on `(let $x (isTrue) (if $x yes no))` yields
`[yes]` from some fuel on: the call returns `True` one use later, the pattern binds it, and the
template reads it in `if`'s condition. HE's `metta-repl` answers `[yes]`. -/
theorem call_value : ∃ N, ∀ n, N ≤ n →
    Streaming.values (Streaming.advance (translate callRows) n
      (Streaming.enter { state := store callRows }
        (.expression [.symbol "let", .var "x", app "isTrue" [],
          app "if" [.var "x", sym "yes", sym "no"]]))) = [sym "yes"] := by
  apply values_of_under yes_answerable
  have renamed : Unifying.rename 0 (.expression [.symbol "let", .var "x", app "isTrue" [],
      app "if" [.var "x", sym "yes", sym "no"]]) =
      .expression [.symbol "let", .var "x#0", app "isTrue" [],
        IfComputed.callC (.var "x#0") (sym "yes") (sym "no")] := by decide
  rw [renamed]
  exact petta_let_later (d := .grounded (.bool true)) (isTrue_returns empty_tracked) rfl
    template_under

/-- **Positive control, a condition that is a call**: PeTTa on `(if (isTrue) yes no)` yields
`[yes]`. -/
theorem call_condition : ∃ N, ∀ n, N ≤ n →
    Streaming.values (Streaming.advance (translate callRows) n
      (Streaming.enter { state := store callRows }
        (app "if" [app "isTrue" [], sym "yes", sym "no"]))) = [sym "yes"] := by
  apply values_of_under yes_answerable
  have renamed : Unifying.rename 0 (app "if" [app "isTrue" [], sym "yes", sym "no"]) =
      IfComputed.callC (app "isTrue" []) (sym "yes") (sym "no") := by decide
  rw [renamed]
  exact petta_if_later (b := true) (isTrue_returns empty_tracked)
    (under_of_evaluates empty_tracked
      (PeTTaRuns.petta_data callRows (.symbol (by decide) (by decide))))

/-- **Negative control**: PeTTa does not yield `[no]` on `(let $x (isTrue) (if $x yes no))`. -/
theorem call_value_not_no : ¬ ∃ N, ∀ n, N ≤ n →
    Streaming.values (Streaming.advance (translate callRows) n
      (Streaming.enter { state := store callRows }
        (.expression [.symbol "let", .var "x", app "isTrue" [],
          app "if" [.var "x", sym "yes", sym "no"]]))) = [sym "no"] := by
  rintro ⟨M, wrong⟩
  obtain ⟨N, right⟩ := call_value
  have atMax := wrong (max M N) (le_max_left M N)
  rw [right (max M N) (le_max_right M N)] at atMax
  simp at atMax

/-- **Negative control, the boundary**: a clause that binds a name is renamed with that binding in
front of the incoming bindings: for `(= (same $a) $a)` and the call `(same 5)`, the clause's match
binds `a`, so the bindings its body runs under are not the incoming (here empty) ones. -/
theorem binding_clause_outside :
    (SpaceSemantics.matchValue.matchValues [] [.var "a"] [.grounded (.int 5)]).map
      (fun bound => Unifying.renameKeys 1 bound ++ ([] : Subst)) ≠ some [] := by
  decide +kernel

end Controls

#print axioms later_of_returns
#print axioms returns_call
#print axioms petta_let_later
#print axioms petta_if_later
#print axioms Controls.isTrue_returns
#print axioms Controls.call_value
#print axioms Controls.call_condition
#print axioms Controls.call_value_not_no
#print axioms Controls.binding_clause_outside

end LetPeTTaCalls

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.TriangleFootprints
