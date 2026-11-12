import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.TriangleFootprints.LetPeTTaBindings

/-!
# Templates that use the bound names in a special form: PeTTa's `if` under tracked bindings

`LetEveryRun.let_every_run` compares HE and PeTTa on `(let $x d b)` for a template `b` that presents
its instance flatly (a literal, or one call whose arguments are items). A template such as
`(if $x yes no)` is PeTTa's special form on an open condition: it is no flat presentation, and what
it does depends on the bindings. This module runs it through the tracked interface of
`LetPeTTaBindings` and states the comparison with that interface.

* `returns_item`: an item (a literal, or a name the bindings hold a literal for) returns its value
  with the bindings unchanged.
* `petta_if_under`: **PeTTa's `if` under the incoming bindings `σ`**: when the condition returns the
  Boolean `b` with `σ` unchanged, the answers are those of the taken branch under `σ`.
* `let_agree_under`: **HE and PeTTa agree on `(let $x d b)` on every run**, HE as in
  `LetEveryRun.let_every_run_he` (any instance meeting the source and finishing contracts), PeTTa
  whenever the renamed template runs under PeTTa's binding of the renamed `$x`.
  `let_settles_agree_under`: with the instance in `IfInBodies.SettlesIf`.

## Controls

On HE's `let` and `if` programs (`LetEveryRun.Controls.letIfRows`):
* `Controls.if_template_agree` (positive, both dialects): `(let $x True (if $x yes no))` gives `[yes]`
  on every HE run and on PeTTa; HE's `metta-repl` answers `[yes]`.
* `Controls.if_template_false` (positive, the other branch, PeTTa): `(let $x False (if $x yes no))`
  yields `[no]`; HE's `metta-repl` answers `[no]`.
* `Controls.structured_if` (positive, a structured pattern feeding the condition and the branch,
  PeTTa): `(let (pair $c $v) (pair True 5) (if $c $v 0))` yields `[5]`; HE's `metta-repl` answers
  `[5]`.
* `Controls.if_template_not_no` (negative): PeTTa does not yield `[no]` on the first.
* `Controls.condition_must_be_bound` (negative): under bindings that hold nothing for the condition's
  name, the condition is no item: `petta_if_under`'s premise is about the bindings.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.TriangleFootprints

namespace LetPeTTaTemplates

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.HE (Space)
open Mettapedia.Languages.MeTTa.HE.Spec.Eval
open Mettapedia.Languages.MeTTa.PeTTa
open Mettapedia.Languages.ProcessCalculi.MORK (Subst isGroundAtom applySubst)
open ServiceFootprints EntryToQuery AnswerBags EveryRun BoundVariables NestedValues ScopedTransfer
  LetPeTTaBindings

variable {dispatch : GroundedDispatch}

/-! ## Items and `if` under tracked bindings -/

/-- **An item returns its value with the bindings unchanged**: a literal, or a name the bindings
hold a literal for. -/
theorem returns_item {atoms : List Atom} {σ : Subst} {u a : Atom} (presented : PresentsItem σ u a) :
    PeTTaReturns atoms σ u a :=
  fun world frames older answers next _ =>
    .single (PeTTaOpenRuns.evaluate_item world σ presented frames older answers next)

/-- **PeTTa's `if` under the incoming bindings `σ`.** When the condition returns the Boolean `b`
with `σ` unchanged, the branch frame takes the branch of `b`, and the answers are those of that
branch under `σ`. -/
theorem petta_if_under {atoms : List Atom} {w : Nat} {σ : Subst} {c y n : Atom} {b : Bool}
    {L : List Atom} (returns : PeTTaReturns atoms σ c (.grounded (.bool b)))
    (taken : PeTTaUnder atoms w σ (IfBranches.pick b y n) L) :
    PeTTaUnder atoms w σ (IfComputed.callC c y n) L := by
  intro frames K deliver world state privateCode atLeast older answers next
  obtain ⟨uses, out, grown, valuesOut, path⟩ := taken frames K deliver world state privateCode
    atLeast older answers next
  have chosen : (if Atom.grounded (.bool b) == Effects.boolean true then y else n) =
      IfBranches.pick b y n := by
    cases b <;> rfl
  refine ⟨uses, out, grown, valuesOut, ?_⟩
  refine .head (IfComputed.if_enter_step world σ c y n frames older answers next) ?_
  refine (returns world (.source (.branch y n) :: frames) older answers next privateCode).trans ?_
  refine .head (IfComputed.branch_return_step world ⟨.grounded (.bool b), σ⟩ y n frames older
    answers next) ?_
  refine .head (PeTTaRuns.alternatives world _ frames older answers next) ?_
  simp only [chosen, List.map_cons, List.map_nil, List.singleton_append]
  exact path

/-! ## `let` with a variable pattern, both dialects, PeTTa through the tracked interface -/

/-- **HE and PeTTa agree on `(let $x d b)` on every run.** HE: for a data value `d` with one closed
stored type and a template `b` whose instance meets the source and finishing contracts, a complete
run exists, every complete run publishes `L`, and every run finishes. PeTTa: when its binding of the
renamed `$x` with `d` gives `σ'` and the renamed template runs under `σ'` to `L`, its streaming run
yields `L` from some fuel on. -/
theorem let_agree_under (notLet : ¬ dispatch.executable (.symbol "let"))
    (notUnify : ¬ dispatch.executable (.symbol "unify")) (policy : Completed.Policy)
    {atoms : List Atom} (program : LetSource.LetProgram atoms) {x : String} {d b : Atom}
    (call : LetSource.LetCall atoms x d b) {L : List Atom}
    (source : LetSource.InstanceSource dispatch policy atoms (LetSource.inst x d b) L)
    (finishing : LetFine.InstanceFine dispatch policy atoms (LetSource.inst x d b) L)
    {σ' : Subst} (bound : Unifying.unifyBinding [] (Unifying.rename 0 (.var x)) d = .ok σ')
    (body : PeTTaUnder atoms 1 σ' (Unifying.rename 0 b) L) :
    Publishes dispatch Completed.scopedLookup policy (Space.ofList atoms)
        (LetSource.letCall x d b) L ∧
      Finishes dispatch Completed.scopedLookup policy (Space.ofList atoms)
        (LetSource.letCall x d b) L ∧
      ∃ N : Nat, ∀ n, N ≤ n → Streaming.values (Streaming.advance (translate atoms) n
        (Streaming.enter { state := store atoms } (LetSource.letCall x d b))) = L := by
  obtain ⟨publishes, finishes⟩ :=
    LetEveryRun.let_every_run_he notLet notUnify policy program call source finishing
  refine ⟨publishes, finishes, ?_⟩
  have ground : isGroundAtom d = true := (answerable_of_data call.data).ground
  have returns : PeTTaReturns atoms [] (Unifying.rename 0 d) d := by
    rw [Unifying.rename_ground 0 d ground]
    exact returns_item ⟨lit_of_data call.data, Or.inl rfl⟩
  exact petta_let_entry source.clean returns bound body

/-- **The same over the settling class with `if` nodes**: the instance of the template is in
`IfInBodies.SettlesIf`. -/
theorem let_settles_agree_under (notHost : ¬ dispatch.executable (.symbol "if"))
    (notLet : ¬ dispatch.executable (.symbol "let"))
    (notUnify : ¬ dispatch.executable (.symbol "unify")) (policy : Completed.Policy)
    {atoms : List Atom} (letProgram : LetSource.LetProgram atoms)
    (ifProgram : IfBranches.IfProgram atoms) {x : String} {d b : Atom}
    (call : LetSource.LetCall atoms x d b) {L : List Atom}
    (settles : IfInBodies.SettlesIf dispatch atoms (LetSource.inst x d b) L)
    {σ' : Subst} (bound : Unifying.unifyBinding [] (Unifying.rename 0 (.var x)) d = .ok σ')
    (body : PeTTaUnder atoms 1 σ' (Unifying.rename 0 b) L) :
    Publishes dispatch Completed.scopedLookup policy (Space.ofList atoms)
        (LetSource.letCall x d b) L ∧
      Finishes dispatch Completed.scopedLookup policy (Space.ofList atoms)
        (LetSource.letCall x d b) L ∧
      ∃ N : Nat, ∀ n, N ≤ n → Streaming.values (Streaming.advance (translate atoms) n
        (Streaming.enter { state := store atoms } (LetSource.letCall x d b))) = L :=
  let_agree_under notLet notUnify policy letProgram call
    (LetEveryRun.instance_source_of_settles ifProgram settles)
    (LetEveryRun.instance_fine_of_settles notHost ifProgram settles) bound body

/-! ## Controls -/

namespace Controls

open WholeRunWords.Double (noHost)
open AnswerBags.Controls (sym app)
open LetEveryRun.Controls (letIfRows)

/-- The bindings PeTTa's binding frame computes for `$x` against a Boolean. -/
abbrev boolBindings (b : Bool) : Subst := [("x#0", .grounded (.bool b))]

theorem bool_tracked (b : Bool) : Tracked 1 (boolBindings b) :=
  ⟨fun binding member => by
      rw [List.mem_singleton] at member
      subst member
      rfl,
    PeTTaRuns.freshFor_renamed (use := 0) (next := 1) (bound := [("x", .grounded (.bool b))])
      (σ := []) (by decide) (fun _ _ => rfl)⟩

/-- The renamed template `(if $x yes no)` under PeTTa's binding of `$x` to the Boolean `b` runs to
the branch of `b`. -/
theorem if_template_under (b : Bool) :
    PeTTaUnder letIfRows 1 (boolBindings b) (IfComputed.callC (.var "x#0") (sym "yes") (sym "no"))
      [IfBranches.pick b (sym "yes") (sym "no")] :=
  petta_if_under (returns_item ⟨.grounded _, Or.inr ⟨"x#0", rfl, rfl⟩⟩)
    (under_of_evaluates (bool_tracked b)
      (PeTTaRuns.petta_data letIfRows (by cases b <;> exact .symbol (by decide) (by decide))))

theorem template_renamed : Unifying.rename 0 (app "if" [.var "x", sym "yes", sym "no"]) =
    IfComputed.callC (.var "x#0") (sym "yes") (sym "no") := by
  decide

/-- PeTTa on `(let $x b (if $x yes no))` for a Boolean literal `b`. -/
theorem if_template_values (b : Bool) : ∃ N, ∀ n, N ≤ n →
    Streaming.values (Streaming.advance (translate letIfRows) n
      (Streaming.enter { state := store letIfRows }
        (LetSource.letCall "x" (.grounded (.bool b)) (app "if" [.var "x", sym "yes", sym "no"])))) =
      [IfBranches.pick b (sym "yes") (sym "no")] := by
  refine petta_let_entry (d := .grounded (.bool b)) (σ' := boolBindings b) (fun a member => ?_)
    (returns_item ⟨.grounded _, Or.inl rfl⟩) rfl ?_
  · rw [List.mem_singleton] at member
    subst member
    cases b <;> exact answerable_of_data (.symbol (by decide) (by decide))
  · rw [template_renamed]
    exact if_template_under b

/-- **Positive control, both dialects, `let` binding the condition of `if`**: on
`(let $x True (if $x yes no))` a complete HE run exists, every complete HE run publishes `[yes]`,
every HE run finishes (`LetEveryRun.Controls.if_template_every_run`), and PeTTa yields `[yes]` from
some fuel on, through `petta_if_under`. HE's `metta-repl` answers `[yes]`. -/
theorem if_template_agree (policy : Completed.Policy) :
    (Publishes noHost Completed.scopedLookup policy (Space.ofList letIfRows)
        (LetSource.letCall "x" (.grounded (.bool true)) (app "if" [.var "x", sym "yes", sym "no"]))
        [sym "yes"] ∧
      Finishes noHost Completed.scopedLookup policy (Space.ofList letIfRows)
        (LetSource.letCall "x" (.grounded (.bool true)) (app "if" [.var "x", sym "yes", sym "no"]))
        [sym "yes"]) ∧
    ∃ N, ∀ n, N ≤ n → Streaming.values (Streaming.advance (translate letIfRows) n
      (Streaming.enter { state := store letIfRows }
        (LetSource.letCall "x" (.grounded (.bool true))
          (app "if" [.var "x", sym "yes", sym "no"])))) = [sym "yes"] :=
  ⟨LetEveryRun.Controls.if_template_every_run policy, if_template_values true⟩

/-- **Positive control, the other branch**: PeTTa on `(let $x False (if $x yes no))` yields `[no]`;
HE's `metta-repl` answers `[no]`. -/
theorem if_template_false : ∃ N, ∀ n, N ≤ n →
    Streaming.values (Streaming.advance (translate letIfRows) n
      (Streaming.enter { state := store letIfRows }
        (LetSource.letCall "x" (.grounded (.bool false))
          (app "if" [.var "x", sym "yes", sym "no"])))) = [sym "no"] :=
  if_template_values false

/-- **Negative control**: PeTTa does not yield `[no]` on `(let $x True (if $x yes no))`. -/
theorem if_template_not_no : ¬ ∃ N, ∀ n, N ≤ n →
    Streaming.values (Streaming.advance (translate letIfRows) n
      (Streaming.enter { state := store letIfRows }
        (LetSource.letCall "x" (.grounded (.bool true))
          (app "if" [.var "x", sym "yes", sym "no"])))) = [sym "no"] := by
  rintro ⟨M, wrong⟩
  obtain ⟨N, right⟩ := if_template_values true
  have atMax := wrong (max M N) (le_max_left M N)
  rw [right (max M N) (le_max_right M N)] at atMax
  simp [IfBranches.pick] at atMax

abbrev five : Atom := .grounded (.int 5)
abbrev zero : Atom := .grounded (.int 0)
abbrev tru : Atom := .grounded (.bool true)

/-- `(pair True 5)` is a value tree that presents itself under any bindings. -/
theorem pair_presents (σ : Subst) : ValuePresents noHost letIfRows σ (app "pair" [tru, five])
    (app "pair" [tru, five]) where
  tree := .node LetPeTTaBindings.Controls.pair_constructor fun u member => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> exact .item (.grounded _)
  bound := fun x member => by
    simp [Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation.TypeSubst.typeVars,
      Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation.TypeSubst.typeVarsList] at member
  instantiates := by
    simp [applySubst, applySubst.applySubstList]

/-- The bindings PeTTa's binding frame computes for `(pair $c $v)` against `(pair True 5)`. -/
abbrev pairBindings : Subst := [("v#0", five), ("c#0", tru)]

theorem pair_tracked : Tracked 1 pairBindings :=
  ⟨fun binding member => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl <;> rfl,
    PeTTaRuns.freshFor_renamed (use := 0) (next := 1) (bound := [("v", five), ("c", tru)]) (σ := [])
      (by decide) (fun _ _ => rfl)⟩

/-- **Positive control, a structured pattern feeding the condition and the branch of `if`**: PeTTa
on `(let (pair $c $v) (pair True 5) (if $c $v 0))` yields `[5]`: the pattern binds both names, the
condition reads one and the taken branch reads the other. HE's `metta-repl` answers `[5]`. -/
theorem structured_if : ∃ N, ∀ n, N ≤ n →
    Streaming.values (Streaming.advance (translate letIfRows) n
      (Streaming.enter { state := store letIfRows }
        (.expression [.symbol "let", app "pair" [.var "c", .var "v"], app "pair" [tru, five],
          app "if" [.var "c", .var "v", zero]]))) = [five] := by
  refine petta_let_entry (d := app "pair" [tru, five]) (σ' := pairBindings) (fun a member => ?_)
    (returns_value (dispatch := noHost) (fun _ member => by cases member) (pair_presents [])) rfl ?_
  · rw [List.mem_singleton] at member
    subst member
    exact answerable_of_data (.grounded _)
  · have renamed : Unifying.rename 0 (app "if" [.var "c", .var "v", zero]) =
        IfComputed.callC (.var "c#0") (.var "v#0") zero := by decide
    rw [renamed]
    exact petta_if_under (b := true) (returns_item ⟨.grounded _, Or.inr ⟨"c#0", rfl, rfl⟩⟩)
      (under_variable pair_tracked rfl)

/-- **Negative control**: under bindings that hold nothing for the condition's name, the condition
is no item: it does not present a Boolean. -/
theorem condition_must_be_bound (b : Bool) :
    ¬ PresentsItem ([] : Subst) (.var "c#0") (.grounded (.bool b)) := by
  rintro ⟨_, same | ⟨x, same, bound⟩⟩
  · cases same
  · cases same
    revert bound
    cases b <;> decide

end Controls

#print axioms returns_item
#print axioms petta_if_under
#print axioms let_agree_under
#print axioms let_settles_agree_under
#print axioms Controls.if_template_under
#print axioms Controls.if_template_agree
#print axioms Controls.if_template_false
#print axioms Controls.if_template_not_no
#print axioms Controls.structured_if
#print axioms Controls.condition_must_be_bound

end LetPeTTaTemplates

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.TriangleFootprints
