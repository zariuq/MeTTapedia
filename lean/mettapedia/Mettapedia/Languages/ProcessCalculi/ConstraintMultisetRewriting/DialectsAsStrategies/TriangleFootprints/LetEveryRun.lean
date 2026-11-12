import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.TriangleFootprints.LetFine

/-!
# HE and PeTTa agree on `let` with a variable pattern, on every run

`LetSource` proves that every derivation of HE's completed relation for `(let $x d b)` publishes the
answers of the instance `b[x := d]`; `LetFine` that every run of HE's machine finishes. Here they are
assembled, with PeTTa's side (`LetPeTTa.petta_let_root`), and instantiated with the settling class
with `if` nodes (`IfInBodies.SettlesIf`).

* `let_every_run_he`: **on the scoped lookup, a complete HE run of `(let $x d b)` exists, every
  complete run publishes the instance's answers, no run is infinite and every reachable
  configuration steps or is final with those answers**, for any instance meeting the source and
  finishing contracts.
* `let_settles_every_run`: the same when the instance is in the settling class `SettlesIf` (data,
  `if` nodes, constructors, calls whose region's bodies settle), on a program carrying `let` and
  `if`.
* `let_every_run`: with PeTTa: from some fuel on, PeTTa's streaming run of `(let $x d b)` yields the
  same answers, when `b` presents the instance under PeTTa's binding of `$x` (one level of items).

## Controls

On `letIfRows`, HE's `let` and `if` programs together:
* `Controls.five_every_run` (positive, both dialects): `(let $x 5 (pair $x $x))` gives
  `[(pair 5 5)]` on every HE run and in PeTTa; HE's `metta-repl` answers `[(pair 5 5)]`.
* `Controls.if_template_every_run` (positive, HE): `(let $x True (if $x yes no))` gives `[yes]` on every
  run: `let` binds the condition of HE's polymorphic `if`; `metta-repl` answers `[yes]`.
* `Controls.nested_template_every_run` (positive, HE): `(let $x yes (pair $x (pair $x no)))` gives
  `[(pair yes (pair yes no))]`; `metta-repl` agrees.
* `Controls.free_template_outside` (negative, the class's boundary): `(pair $x $y)` has the variable
  `y` besides the pattern's, so its instance is open and not the body of a contract.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.TriangleFootprints

namespace LetEveryRun

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.HE (Space Bindings)
open Mettapedia.Languages.MeTTa.HE.Spec.Eval
open Mettapedia.Languages.MeTTa.HE.Spec.Eval.Completed (Policy Result Frame)
open Mettapedia.Languages.MeTTa.HE.Spec.Type (StorageTypesRel AnnotationTypesRel)
open Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation (TypeSubst)
open Mettapedia.Languages.MeTTa.HE.RecursiveMachine.Contextual (load)
open Mettapedia.Languages.MeTTa.PeTTa
open ServiceFootprints EntryToQuery AnswerBags EveryRun EveryRunFinishes ScopedTransfer
  BoundVariables NestedArguments IfBranches IfConditions IfInBodies
open LetSource (letCall inst LetProgram LetCall InstanceSource)
open LetFine (InstanceFine)

variable {dispatch : GroundedDispatch}

/-! ## The contracts from the settling class with `if` nodes -/

theorem instance_source_of_settles {policy : Policy} {atoms : List Atom} (program : IfProgram atoms)
    {t : Atom} {L : List Atom} (settles : SettlesIf dispatch atoms t L) :
    InstanceSource dispatch policy atoms t L :=
  ⟨(settlesIf_shape settles).2, (settlesIf_shape settles).1, settlesIf_determined program settles⟩

theorem instance_fine_of_settles {policy : Policy} (notHost : ¬ dispatch.executable (.symbol "if"))
    {atoms : List Atom} (program : IfProgram atoms) {t : Atom} {L : List Atom}
    (settles : SettlesIf dispatch atoms t L) : InstanceFine dispatch policy atoms t L :=
  ⟨(settlesIf_shape settles).2, (settlesIf_shape settles).1, settlesIf_fine notHost program settles⟩

/-! ## Every run -/

/-- **HE's `let` with a variable pattern on every run**: on the scoped lookup, for a dispatch that
executes neither `let` nor `unify` and any policy, a complete run of `(let $x d b)` exists, every
complete run publishes `L`, no run is infinite, and every reachable configuration steps or is final
with `L`, where `L` is the instance's answers by its source and finishing contracts. -/
theorem let_every_run_he (notLet : ¬ dispatch.executable (.symbol "let"))
    (notUnify : ¬ dispatch.executable (.symbol "unify")) (policy : Policy) {atoms : List Atom}
    (program : LetProgram atoms) {x : String} {d b : Atom} (call : LetCall atoms x d b)
    {L : List Atom} (source : InstanceSource dispatch policy atoms (inst x d b) L)
    (finishing : InstanceFine dispatch policy atoms (inst x d b) L) :
    Publishes dispatch Completed.scopedLookup policy (Space.ofList atoms) (letCall x d b) L ∧
      Finishes dispatch Completed.scopedLookup policy (Space.ofList atoms) (letCall x d b) L := by
  have fine := LetFine.let_entry_fine notLet notUnify program call finishing
  have every : ∀ emitted : List Result,
      Relation.ReflTransGen (HEStep dispatch Completed.scopedLookup policy)
        (load (Space.ofList atoms) (letCall x d b) Atom.undefinedType)
        (final (Space.ofList atoms) emitted) →
      emitted.map (fun r => r.1.erase) = L :=
    fun emitted run => LetSource.let_entry_source program call source (complete_source run)
  refine ⟨⟨?_, every⟩, ⟨fine.acc, fun y path => ?_⟩⟩
  · obtain ⟨space, emitted, path⟩ := IfAtFrames.Fine.exists_final fine
    have same : space = Space.ofList atoms := space_fixed path
    subst same
    exact ⟨emitted, path⟩
  · rcases (fine.reaches path).progress with moves | ⟨space, emitted, rfl⟩
    · exact Or.inl moves
    · have same : space = Space.ofList atoms := space_fixed path
      subst same
      exact Or.inr ⟨emitted, rfl, every emitted path⟩

/-- **`let` over the settling class**: when the instance `b[x := d]` settles (`SettlesIf`), on a
program carrying both `let` and `if`, every HE run of `(let $x d b)` publishes the instance's answers
and finishes. -/
theorem let_settles_every_run (notHost : ¬ dispatch.executable (.symbol "if"))
    (notLet : ¬ dispatch.executable (.symbol "let"))
    (notUnify : ¬ dispatch.executable (.symbol "unify")) (policy : Policy) {atoms : List Atom}
    (letProgram : LetProgram atoms) (ifProgram : IfProgram atoms) {x : String} {d b : Atom}
    (call : LetCall atoms x d b) {L : List Atom} (settles : SettlesIf dispatch atoms (inst x d b) L) :
    Publishes dispatch Completed.scopedLookup policy (Space.ofList atoms) (letCall x d b) L ∧
      Finishes dispatch Completed.scopedLookup policy (Space.ofList atoms) (letCall x d b) L :=
  let_every_run_he notLet notUnify policy letProgram call
    (instance_source_of_settles ifProgram settles) (instance_fine_of_settles notHost ifProgram settles)

/-- **HE and PeTTa agree on `(let $x d b)` on every run**: HE as in `let_settles_every_run`, and
PeTTa's streaming run yields the same answers from some fuel on, when PeTTa evaluates every open
presentation of the instance to them and `b` presents it under PeTTa's binding of the renamed `$x`. -/
theorem let_every_run (notHost : ¬ dispatch.executable (.symbol "if"))
    (notLet : ¬ dispatch.executable (.symbol "let"))
    (notUnify : ¬ dispatch.executable (.symbol "unify")) (policy : Policy) {atoms : List Atom}
    (letProgram : LetProgram atoms) (ifProgram : IfProgram atoms) {x : String} {d b : Atom}
    (call : LetCall atoms x d b) {L : List Atom} (settles : SettlesIf dispatch atoms (inst x d b) L)
    (bound : Unifying.bindAnswers (.var (Unifying.freshName 0 x)) (Unifying.rename 0 b) [⟨d, []⟩] =
      some [.evaluate [(Unifying.freshName 0 x, d)] (Unifying.rename 0 b)])
    (petta : PeTTaOpen atoms (inst x d b) L)
    (presented : Presents [(Unifying.freshName 0 x, d)] (Unifying.rename 0 b) (inst x d b)) :
    Publishes dispatch Completed.scopedLookup policy (Space.ofList atoms) (letCall x d b) L ∧
      Finishes dispatch Completed.scopedLookup policy (Space.ofList atoms) (letCall x d b) L ∧
      ∃ N : Nat, ∀ n, N ≤ n → Streaming.values (Streaming.advance (translate atoms) n
        (Streaming.enter { state := store atoms } (letCall x d b))) = L := by
  obtain ⟨publishes, finishes⟩ :=
    let_settles_every_run notHost notLet notUnify policy letProgram ifProgram call settles
  exact ⟨publishes, finishes, LetPeTTa.petta_let_root (atoms := atoms) (x := x) call.data
    (settlesIf_shape settles).1 bound petta presented⟩

/-! ## Controls -/

namespace Controls

open WholeRunWords.Double (noHost)
open AnswerBags.Controls (sym app rule rule_consFree)
open IfEveryRun (ifProgram ifArrow if_program)
open IfInBodies.Controls (undeclared_of)

/-- HE's `let` and `if` programs together. -/
abbrev letIfRows : List Atom := LetFrontier.letRows ++ ifProgram

theorem annotations_none {target : Atom} :
    ∀ rows : List Atom, (∀ row ∈ rows, ∀ T, row ≠ .expression [.symbol ":", target, T]) →
      AnnotationTypesRel target rows []
  | [], _ => .nil
  | row :: rows, absent => .skip (absent row List.mem_cons_self)
      (annotations_none rows fun r member => absent r (List.mem_cons_of_mem _ member))

theorem let_types : StorageTypesRel (Space.ofList letIfRows) (.symbol "let") [LetPlain.letArrow] := by
  have extracted := Mettapedia.Languages.MeTTa.HE.Spec.Type.AnnotationTypesRel.complete
    (.symbol "let") letIfRows
  have computed : letIfRows.filterMap
      (Mettapedia.Languages.MeTTa.HE.Spec.Type.annotationType? (.symbol "let")) =
        [LetPlain.letArrow] := by decide
  rw [computed] at extracted
  exact .symbolKnown extracted (by simp)

theorem unify_types :
    StorageTypesRel (Space.ofList letIfRows) (.symbol "unify") [LetPlain.unifyArrow] := by
  have extracted := Mettapedia.Languages.MeTTa.HE.Spec.Type.AnnotationTypesRel.complete
    (.symbol "unify") letIfRows
  have computed : letIfRows.filterMap
      (Mettapedia.Languages.MeTTa.HE.Spec.Type.annotationType? (.symbol "unify")) =
        [LetPlain.unifyArrow] := by decide
  rw [computed] at extracted
  exact .symbolKnown extracted (by simp)

theorem if_types : StorageTypesRel (Space.ofList letIfRows) (.symbol "if") [ifArrow] := by
  have extracted := Mettapedia.Languages.MeTTa.HE.Spec.Type.AnnotationTypesRel.complete
    (.symbol "if") letIfRows
  have computed : letIfRows.filterMap
      (Mettapedia.Languages.MeTTa.HE.Spec.Type.annotationType? (.symbol "if")) = [ifArrow] := by
    decide
  rw [computed] at extracted
  exact .symbolKnown extracted (by simp)

theorem expr_types (head : Atom) (tail : List Atom) :
    StorageTypesRel (Space.ofList letIfRows) (.expression (head :: tail)) [Atom.undefinedType] :=
  .expressionUndefined (annotations_none letIfRows fun row member T same => by
    simp only [letIfRows, LetFrontier.letRows, ifProgram, List.cons_append, List.nil_append,
      List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [LetFrontier.letDecl, LetFrontier.unifyDecl] at same)

theorem let_program : LetProgram letIfRows where
  rows := ⟨ifProgram, rfl, fun row member => by
    simp only [ifProgram, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl
    · exact Or.inl fun l r same => by simp at same
    · exact Or.inr ⟨_, _, "if", _, rfl, rfl, Or.inl (by decide)⟩
    · exact Or.inr ⟨_, _, "if", _, rfl, rfl, Or.inl (by decide)⟩⟩
  letTypes := let_types
  unifyTypes := unify_types
  emptyTypes := undeclared_of (by decide)
  exprTypes := expr_types

theorem if_program_let : IfProgram letIfRows := by
  refine ⟨if_types, ?_⟩
  intro row member
  rcases List.mem_append.mp member with inLet | inIf
  · simp only [LetFrontier.letRows, List.mem_cons, List.not_mem_nil, or_false] at inLet
    rcases inLet with rfl | rfl | rfl
    · exact ⟨fun lhs rhs same => by simp [LetFrontier.letDecl] at same,
        fun lhs rhs same => by simp [LetFrontier.letDecl] at same⟩
    · exact ⟨fun lhs rhs same => by simp [LetFrontier.unifyDecl] at same,
        fun lhs rhs same => by simp [LetFrontier.unifyDecl] at same⟩
    · refine ⟨rule_consFree (f := "let") (args := [.var "pattern", .var "atom", .var "template"])
        (rhs := LetFrontier.letRight) fun a inside => ?_, fun lhs rhs same => ?_⟩
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at inside
        rcases inside with rfl | rfl | rfl <;> exact .var _
      · cases same
        decide
  · exact if_program row inIf

/-- `(let $x 5 (pair $x $x))`. -/
abbrev fiveCall : Atom := LetFrontier.Controls.fiveCall

theorem five_call : LetCall letIfRows "x" (.grounded (.int 5)) (app "pair" [.var "x", .var "x"]) where
  data := .grounded _
  typed := ⟨_, .groundedKnown (.int 5) (by simp [Atom.undefinedType]), rfl⟩
  onlyX := by decide
  expression := ⟨_, _, rfl⟩

theorem pair_head : NestedCalls.NodeHead noHost letIfRows "pair" :=
  ⟨.symbol (by decide) (by decide), by decide +kernel, fun impossible => impossible, by decide,
    by decide, by decide, by decide⟩

theorem five_settles : SettlesIf noHost letIfRows
    (inst "x" (.grounded (.int 5)) (app "pair" [.var "x", .var "x"]))
    [app "pair" [.grounded (.int 5), .grounded (.int 5)]] := by
  rw [LetSource.Controls.instance_five]
  have built := SettlesIf.build (dispatch := noHost) (atoms := letIfRows) pair_head
    (by decide +kernel) (ts := [.grounded (.int 5), .grounded (.int 5)])
    (Ls := [[.grounded (.int 5)], [.grounded (.int 5)]]) rfl (fun p member => by
      simp only [List.zip_cons_cons, List.zip_nil_right, List.mem_cons, List.not_mem_nil,
        or_false] at member
      rcases member with rfl | rfl <;> exact .data (.grounded _) (by simp [Atom.notReducible]))
  simpa [combos] using built

theorem pair_ordinary : Ordinary noHost letIfRows "pair" [.grounded (.int 5), .grounded (.int 5)] :=
  ⟨.symbol (by decide) (by decide), (fun a member => by
      simp only [List.mem_cons, List.not_mem_nil, or_false, or_self] at member
      subst member
      exact .grounded _), (by decide +kernel), (fun impossible => impossible), (by decide),
    (by decide), (by decide), (by decide), (by decide), (by decide)⟩

/-- **Positive control, both dialects**: `(let $x 5 (pair $x $x))` on HE's `let` and `if` programs:
a complete HE run exists, every complete run publishes `(pair 5 5)`, every run finishes, and PeTTa
yields `(pair 5 5)` from some fuel on. HE's `metta-repl` answers `[(pair 5 5)]`. -/
theorem five_every_run (policy : Policy) :
    Publishes noHost Completed.scopedLookup policy (Space.ofList letIfRows) fiveCall
        [app "pair" [.grounded (.int 5), .grounded (.int 5)]] ∧
      Finishes noHost Completed.scopedLookup policy (Space.ofList letIfRows) fiveCall
        [app "pair" [.grounded (.int 5), .grounded (.int 5)]] ∧
      ∃ N : Nat, ∀ n, N ≤ n → Streaming.values (Streaming.advance (translate letIfRows) n
        (Streaming.enter { state := store letIfRows } fiveCall)) =
          [app "pair" [.grounded (.int 5), .grounded (.int 5)]] :=
  let_every_run (fun impossible => impossible) (fun impossible => impossible)
    (fun impossible => impossible) policy let_program if_program_let five_call five_settles rfl
    (by
      rw [LetSource.Controls.instance_five]
      exact petta_open_constructor pair_ordinary (by decide +kernel))
    (by
      rw [LetSource.Controls.instance_five]
      exact .call "pair" rfl (.cons LetPeTTa.Controls.five_item (.cons LetPeTTa.Controls.five_item .nil)))

theorem if_template_call :
    LetCall letIfRows "x" (.grounded (.bool true)) (app "if" [.var "x", sym "yes", sym "no"]) where
  data := .grounded _
  typed := ⟨_, bool_types_in _ true, rfl⟩
  onlyX := by decide
  expression := ⟨_, _, rfl⟩

theorem if_template_instance :
    inst "x" (.grounded (.bool true)) (app "if" [.var "x", sym "yes", sym "no"]) =
      IfComputed.callC (.grounded (.bool true)) (sym "yes") (sym "no") := by
  simp [inst, Mettapedia.Languages.MeTTa.HE.Spec.Type.RuntimeRefinement.applyTypeValuation, app,
    IfComputed.callC]

theorem if_node : IfNode noHost letIfRows (.grounded (.bool true)) true (sym "yes") (sym "no") where
  condition := fun _ => literal_condition letIfRows true
  branches :=
    { branches :=
        { takenData := .symbol (by decide) (by decide)
          takenNotRefused := by simp [pick, Atom.notReducible]
          takenUndeclared := undeclared_of (by decide)
          closedYes := data_closed (.symbol (by decide) (by decide))
          closedNo := data_closed (.symbol (by decide) (by decide))
          groundYes := rfl
          groundNo := rfl
          typedYes := ⟨_, undeclared_of (by decide)⟩
          typedNo := ⟨_, undeclared_of (by decide)⟩
          region := by decide +kernel }
      typedYes := ⟨_, undeclared_of (by decide), rfl⟩
      typedNo := ⟨_, undeclared_of (by decide), rfl⟩ }
  dataYes := .symbol (by decide) (by decide)
  dataNo := .symbol (by decide) (by decide)

/-- **Positive control, `let` binding the condition of HE's polymorphic `if`**:
`(let $x True (if $x yes no))` gives `yes` on every HE run, and every run finishes; HE's
`metta-repl` answers `[yes]`. -/
theorem if_template_every_run (policy : Policy) :
    Publishes noHost Completed.scopedLookup policy (Space.ofList letIfRows)
        (letCall "x" (.grounded (.bool true)) (app "if" [.var "x", sym "yes", sym "no"])) [sym "yes"] ∧
      Finishes noHost Completed.scopedLookup policy (Space.ofList letIfRows)
        (letCall "x" (.grounded (.bool true)) (app "if" [.var "x", sym "yes", sym "no"]))
        [sym "yes"] := by
  have settles : SettlesIf noHost letIfRows
      (inst "x" (.grounded (.bool true)) (app "if" [.var "x", sym "yes", sym "no"])) [sym "yes"] := by
    rw [if_template_instance]
    exact .ifNode if_node
  exact let_settles_every_run (fun impossible => impossible) (fun impossible => impossible)
    (fun impossible => impossible) policy let_program if_program_let if_template_call settles

theorem nested_call : LetCall letIfRows "x" (sym "yes")
    (app "pair" [.var "x", app "pair" [.var "x", sym "no"]]) where
  data := .symbol (by decide) (by decide)
  typed := ⟨_, undeclared_of (by decide), rfl⟩
  onlyX := by decide
  expression := ⟨_, _, rfl⟩

/-- **Positive control, a nested template**: `(let $x yes (pair $x (pair $x no)))` gives
`(pair yes (pair yes no))` on every HE run, and every run finishes; HE's `metta-repl` agrees. -/
theorem nested_template_every_run (policy : Policy) :
    Publishes noHost Completed.scopedLookup policy (Space.ofList letIfRows)
        (letCall "x" (sym "yes") (app "pair" [.var "x", app "pair" [.var "x", sym "no"]]))
        [app "pair" [sym "yes", app "pair" [sym "yes", sym "no"]]] ∧
      Finishes noHost Completed.scopedLookup policy (Space.ofList letIfRows)
        (letCall "x" (sym "yes") (app "pair" [.var "x", app "pair" [.var "x", sym "no"]]))
        [app "pair" [sym "yes", app "pair" [sym "yes", sym "no"]]] := by
  have instanceEq : inst "x" (sym "yes") (app "pair" [.var "x", app "pair" [.var "x", sym "no"]]) =
      app "pair" [sym "yes", app "pair" [sym "yes", sym "no"]] := by
    simp [inst, Mettapedia.Languages.MeTTa.HE.Spec.Type.RuntimeRefinement.applyTypeValuation, app]
  have yesData : DataAtom (sym "yes") := .symbol (by decide) (by decide)
  have inner : SettlesIf noHost letIfRows (app "pair" [sym "yes", sym "no"])
      [app "pair" [sym "yes", sym "no"]] := by
    have built := SettlesIf.build (dispatch := noHost) (atoms := letIfRows) pair_head
      (by decide +kernel) (ts := [sym "yes", sym "no"]) (Ls := [[sym "yes"], [sym "no"]]) rfl
      (fun p member => by
        simp only [List.zip_cons_cons, List.zip_nil_right, List.mem_cons, List.not_mem_nil,
          or_false] at member
        rcases member with rfl | rfl
        · exact .data yesData (by simp [Atom.notReducible])
        · exact .data (.symbol (by decide) (by decide)) (by simp [Atom.notReducible]))
    simpa [combos] using built
  have settles : SettlesIf noHost letIfRows
      (inst "x" (sym "yes") (app "pair" [.var "x", app "pair" [.var "x", sym "no"]]))
      [app "pair" [sym "yes", app "pair" [sym "yes", sym "no"]]] := by
    rw [instanceEq]
    have built := SettlesIf.build (dispatch := noHost) (atoms := letIfRows) pair_head
      (by decide +kernel) (ts := [sym "yes", app "pair" [sym "yes", sym "no"]])
      (Ls := [[sym "yes"], [app "pair" [sym "yes", sym "no"]]]) rfl (fun p member => by
        simp only [List.zip_cons_cons, List.zip_nil_right, List.mem_cons, List.not_mem_nil,
          or_false] at member
        rcases member with rfl | rfl
        · exact .data yesData (by simp [Atom.notReducible])
        · exact inner)
    simpa [combos] using built
  exact let_settles_every_run (fun impossible => impossible) (fun impossible => impossible)
    (fun impossible => impossible) policy let_program if_program_let nested_call settles

/-- **Negative control, the class's boundary**: in `(let $x 5 (pair $x $y))` the template has the
variable `y` besides the pattern's, so its instance is open: it has no body facts and is outside the
contracts (HE answers it with the variable left free). -/
theorem free_template_outside :
    ¬ BodyFacts (inst "x" (.grounded (.int 5)) (app "pair" [.var "x", .var "y"])) := by
  intro facts
  apply facts.closed "y"
  have same : inst "x" (.grounded (.int 5)) (app "pair" [.var "x", .var "y"]) =
      app "pair" [.grounded (.int 5), .var "y"] := by
    simp [inst, Mettapedia.Languages.MeTTa.HE.Spec.Type.RuntimeRefinement.applyTypeValuation, app]
  rw [same]
  exact .expression (by simp) (.var "y")

end Controls

#print axioms instance_source_of_settles
#print axioms instance_fine_of_settles
#print axioms let_every_run_he
#print axioms let_settles_every_run
#print axioms let_every_run
#print axioms Controls.five_every_run
#print axioms Controls.if_template_every_run
#print axioms Controls.nested_template_every_run
#print axioms Controls.free_template_outside

end LetEveryRun

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.TriangleFootprints
