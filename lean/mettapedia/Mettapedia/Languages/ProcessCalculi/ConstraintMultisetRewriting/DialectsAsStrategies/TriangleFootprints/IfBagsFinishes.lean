import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.TriangleFootprints.IfCallFinishes

/-!
# Every run of `(if c y n)` on a nondeterministic condition finishes

`IfBags.bag_every_run` shows that, for a condition with several Boolean answers `Lc`, a complete HE run
of `(if c y n)` exists and every complete run publishes `answersOf Lc Ly Ln` (per condition answer in
order, the selected branch's answers). Here **every run finishes**: HE's machine has no infinite run
from the entry, every reachable configuration steps or is final, and a final one publishes those
answers, so the bags agree on every run, with multiplicity.

* `fine_condition_branches`: the argument branches over the condition's answers, one packet each.
* `fine_bag_calls`: the calls over the assembled call values, each by `IfCallFinishes.fine_call_query`.
* `fine_bag_function`, `bag_fine`, `bag_every_run_finishes`.

## Controls

* `Controls.coin_pair_finishes` (`(if (coin) (half 4) (pair a b))`): every run finishes, publishing
  `[two, (pair a b)]`.
* `Controls.coin_twice_finishes` (`(if (coin2) yes no)`, two `True` rows): every run finishes,
  publishing `yes` twice.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.TriangleFootprints

namespace IfBagsFinishes

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.HE (Space Bindings isErrorAtom)
open Mettapedia.Languages.MeTTa.HE.Spec.Eval
open Mettapedia.Languages.MeTTa.HE.Spec.Eval.Steps (EquationWork EquationFrontierRel)
open Mettapedia.Languages.MeTTa.HE.Spec.Eval.Completed (Policy Result CastLookup Frame)
open Mettapedia.Languages.MeTTa.HE.Spec.Type (TypeMatchRel StorageTypesRel)
open Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation (TypeSubst)
open Mettapedia.Languages.MeTTa.HE.Spec.Match.Merge (AtomOccurs)
open Mettapedia.Languages.MeTTa.HE.RecursiveMachine.Contextual (LocalStepWith load)
open Mettapedia.Languages.MeTTa.HE.RecursiveTasks.Contextual (Control Continuation)
open HEOnTheStep (HEConfig)
open Mettapedia.Languages.MeTTa.PeTTa
open ServiceFootprints EntryToQuery AnswerBags EveryRun BoundVariables NestedArguments
  NestedEveryRun NestedValues NestedCalls MarkedValues CompoundBindings DeclaredHeads
  DeclaredEveryRun TypedEveryRun AtomDemands IfEveryRun IfBranches DemandSpine IfComputed
  IfCallBranches IfBags EveryRunFinishes IfFinishes DemandSpineFinishes IfCallFinishes
open AnswerBags.Controls (sym app rule rule_consFree)

variable {dispatch : GroundedDispatch} {policy : Policy}

/-! ## The argument branches over the condition's answers -/

/-- **Every run of the argument branches over the condition's answers finishes**, with one packet
per answer, in order. -/
theorem fine_condition_branches {atoms : List Atom} {live : List Atom} {scope : List String}
    {c y n : Atom} (closedY : ∀ name, ¬ AtomOccurs y name)
    (closedN : ∀ name, ¬ AtomOccurs n name) :
    ∀ (R : List Result), (∀ r ∈ R, ∃ b : Bool, r.1 = Entry.Value.ofAtom (.grounded (.bool b))) →
      ∀ (stack : List Continuation) (emitted : List Result),
        (∀ out : List Result, out.map (fun r => r.1) = R.map (fun r =>
            Entry.Value.argumentPacket [r.1, Entry.Value.ofAtom y, Entry.Value.ofAtom n]) →
          Fine dispatch Completed.rawLookup policy ⟨Space.ofList atoms, .returning out, stack,
            emitted⟩) →
        Fine dispatch Completed.rawLookup policy ⟨Space.ofList atoms,
          .work (.argumentBranches live scope (Entry.Value.ofAtom c)
            [(Entry.Value.ofAtom y, Atom.atomType), (Entry.Value.ofAtom n, Atom.atomType)] R),
          stack, emitted⟩
  | [], _, stack, emitted, cont => fine_argumentBranches_nil (cont [] rfl)
  | r :: rs, booleans, stack, emitted, cont => by
      obtain ⟨b, rValue⟩ := booleans r List.mem_cons_self
      obtain ⟨rv, fr⟩ := r
      simp only at rValue
      subst rValue
      refine fine_argumentBranches_continue ?_ ?_
      · rintro ⟨stopped, _⟩
        exact (DataAtom.grounded (.bool b)).not_stopped (by simpa using stopped)
      apply fine_argumentsCons
      refine fine_deliver_closed closedY ?_
      apply fine_arguments_frame
      refine fine_argumentBranches_continue ?_ ?_
      · rintro ⟨_, different⟩
        exact different rfl
      apply fine_argumentsCons
      refine fine_deliver_closed closedN ?_
      apply fine_arguments_frame
      refine fine_argumentBranches_continue ?_ ?_
      · rintro ⟨_, different⟩
        exact different rfl
      apply fine_argumentsNil
      apply fine_argumentTail
      apply fine_append
      apply fine_argumentBranches_nil
      apply fine_prepend
      apply fine_argumentTail
      apply fine_append
      apply fine_argumentBranches_nil
      apply fine_prepend
      apply fine_argumentTail
      apply fine_append
      apply fine_condition_branches closedY closedN rs
        (fun x member => booleans x (List.mem_cons_of_mem _ member)) _ emitted
      intro out outEq
      apply fine_prepend
      apply cont
      simp [outEq, Completed.argumentPrepend_packet]

/-! ## The calls over the assembled values -/

/-- **Every run of the calls over the assembled call values finishes**, per answer with the selected
branch's answers. -/
theorem fine_bag_calls (notHost : ¬ dispatch.executable (.symbol "if")) {atoms : List Atom}
    (program : IfCallProgram atoms) {c y n : Atom} {Lc Ly Ln : List Atom}
    (bag : BagIf dispatch atoms c y n Lc Ly Ln) {live : List Atom} {scope : List String} :
    ∀ (rows : List Result) (as : List Atom), as ⊆ Lc →
      rows.map (fun r => r.1) = as.map (fun a => callValueOf (truth a) y n) →
      (∀ a ∈ as, ∃ b : Bool, a = .grounded (.bool b)) →
      ∀ (stack : List Continuation) (emitted : List Result),
        (∀ R : List Result, R.map (fun r => r.1.erase) = answersOf as Ly Ln →
          Fine dispatch Completed.rawLookup policy ⟨Space.ofList atoms, .returning R, stack,
            emitted⟩) →
        Fine dispatch Completed.rawLookup policy ⟨Space.ofList atoms,
          .work (.calls live scope (.var "t") rows), stack, emitted⟩
  | [], as, _, shaped, _, stack, emitted, cont => by
      cases as with
      | nil => exact fine_calls_nil (cont [] rfl)
      | cons _ _ => simp at shaped
  | r :: rs, as, within, shaped, booleans, stack, emitted, cont => by
      obtain ⟨a, as', rfl⟩ : ∃ a as', as = a :: as' := by
        cases as with
        | nil => simp at shaped
        | cons a as' => exact ⟨a, as', rfl⟩
      simp only [List.map_cons, List.cons.injEq] at shaped
      obtain ⟨headValue, restValues⟩ := shaped
      have inLc : a ∈ Lc := within List.mem_cons_self
      obtain ⟨b, rfl⟩ := booleans a List.mem_cons_self
      rw [truth_bool] at headValue
      obtain ⟨rv, fr⟩ := r
      simp only at headValue
      subst headValue
      apply fine_calls_cons
      refine fine_call_query notHost program (bag.branches b inLc) fr _ _ ?_
      intro Q eraseQ
      apply fine_append
      apply fine_bag_calls notHost program bag rs as'
        (fun x member => within (List.mem_cons_of_mem _ member)) restValues
        (fun x member => booleans x (List.mem_cons_of_mem _ member)) _ emitted
      intro Rs eraseRs
      apply fine_prepend
      apply cont
      rw [List.map_append, eraseQ, eraseRs]
      cases b <;> simp [answersOf, truth_bool]

/-! ## The function application -/

/-- **Every run of the function application of `(if c y n)` on a condition with several answers
finishes**, with one call value per answer, in order. -/
theorem fine_bag_function {atoms : List Atom} (program : IfCallProgram atoms) {c y n : Atom}
    {Lc Ly Ln : List Atom} (bag : BagIf dispatch atoms c y n Lc Ly Ln) {live : List Atom}
    {scope : List String} {expected : Atom} {signature : SelectedTypePolicy}
    (functionType : signature.functionType = ifArrow) {activation : Frame}
    (empty : activation.bindings = Bindings.empty) (stack : List Continuation)
    (emitted : List Result)
    (cont : ∀ R : List Result, R.map (fun r => r.1) = Lc.map (fun a => callValueOf (truth a) y n) →
      Fine dispatch Completed.rawLookup policy ⟨Space.ofList atoms, .returning R, stack, emitted⟩) :
    Fine dispatch Completed.rawLookup policy ⟨Space.ofList atoms,
      .work (.function live scope expected signature (Entry.Value.ofAtom (.symbol "if"))
        [Entry.Value.ofAtom c, Entry.Value.ofAtom y, Entry.Value.ofAtom n] activation), stack,
      emitted⟩ := by
  have projections := if_projections functionType
  refine fine_functionStart (by simp [projections.1]) ?_
  rw [projections.1, functionType]
  simp only [List.zip_cons_cons, List.zip_nil_right]
  refine fine_data_cast if_data (symbol_cast_entry (by decide) (by decide) (by decide +kernel))
    program.types (if_renewal_at policy empty) (ifArrow_accepts empty) ?_
  intro frF
  apply fine_functionHeads_frame
  refine fine_functionBranches_continue ?_ ?_
  · simpa using if_data.not_stopped
  apply fine_argumentsCons
  refine fine_settlesK_at program.rows bool_transparent bag.conditionSettles bag.conditionCasts
    (Entry.Value.ofAtom c) (Entry.Value.erase_ofAtom c) (marked_ofAtom c) _ _ _ _ _ ?_
  intro R eraseR
  have booleans : ∀ r ∈ R, ∃ b : Bool, r.1 = Entry.Value.ofAtom (.grounded (.bool b)) := by
    intro r member
    have inLc : r.1.erase ∈ Lc := by
      rw [← eraseR]
      exact List.mem_map.mpr ⟨r, member, rfl⟩
    obtain ⟨b, same⟩ := bag.booleans _ inLc
    exact ⟨b, value_of_data (.grounded _) same⟩
  apply fine_arguments_frame
  refine fine_condition_branches bag.closedYes bag.closedNo R booleans _ _ ?_
  intro out outEq
  apply fine_functionAssemble
  apply fine_append
  apply fine_functionBranches_nil
  apply fine_prepend
  apply cont
  rw [List.append_nil, List.map_map]
  have viaFst : ((fun r => r.1) ∘ Completed.functionAssemble
      (Entry.Value.ofAtom (.symbol "if"))) =
      (fun r : Result => (Completed.functionAssemble
        (Entry.Value.ofAtom (.symbol "if")) (r.1, Completed.Frame.empty)).1) := by
    funext r
    exact assemble_fst _ r _
  rw [viaFst]
  have mapped := congrArg (List.map fun v : Entry.Value =>
    (Completed.functionAssemble (Entry.Value.ofAtom (.symbol "if"))
      (v, Completed.Frame.empty)).1) outEq
  simp only [List.map_map, Function.comp_def] at mapped
  rw [mapped, assembled_rows R booleans, eraseR]

/-! ## Every run of `(if c y n)` -/

/-- **Every run of `(if c y n)` on a nondeterministic condition from HE's entry finishes.** -/
theorem bag_fine (notHost : ¬ dispatch.executable (.symbol "if")) (policy : Policy)
    {atoms : List Atom} (program : IfCallProgram atoms) {c y n : Atom} {Lc Ly Ln : List Atom}
    (bag : BagIf dispatch atoms c y n Lc Ly Ln) :
    Fine dispatch Completed.rawLookup policy
      (load (Space.ofList atoms) (callC c y n) Atom.undefinedType) := by
  obtain ⟨Tc, typesC, acceptsC, keepsC⟩ := bag.conditionTyped
  obtain ⟨Ty, typesY⟩ := bag.typedYes
  obtain ⟨Tn, typesN⟩ := bag.typedNo
  have entry := call_entry policy if_data [c, y, n]
  have shape : Completed.Frame.empty.read policy (Entry.Value.ofAtom (callC c y n)) =
      .expression .active (Entry.Value.ofAtom (.symbol "if") ::
        [c, y, n].map Entry.Value.ofAtom) := by
    rw [Completed.Frame.read_empty]
    simp only [callC, app, Entry.Value.ofAtom, List.map_cons, List.map_nil]
  have selection : Completed.ArgumentService.historical.selection (Space.ofList atoms)
      Completed.rawLookup policy [] []
      (Completed.Frame.empty.read policy (Entry.Value.ofAtom (callC c y n))).erase
      (Entry.Value.ofAtom (.symbol "if")).erase Atom.undefinedType Completed.Frame.empty
      (.selected ifPolicy [Completed.Frame.empty]) := by
    rw [Completed.Frame.read_empty, Entry.Value.erase_ofAtom, Entry.Value.erase_ofAtom]
    exact cond_selection_succeeds policy program typesC acceptsC typesY typesN
  have cleanL := answersOf_answerable (Lc := Lc) (settlesK_shape bag.yesSettles).1.answers
    (settlesK_shape bag.noSettles).1.answers
  show Fine dispatch Completed.rawLookup policy ⟨Space.ofList atoms,
    .work (.atom [] [] (Entry.Value.ofAtom (callC c y n)) Atom.undefinedType Completed.Frame.empty),
    [], []⟩
  refine .step ⟨_, .internal (LocalStepWith.atomFunction (admission := .historical) entry shape
    selection)⟩ ?_
  intro z moved
  cases moved with
  | internal l =>
      cases l with
      | delivered entered => cases Entry.functional entered entry
      | cast entered => cases Entry.functional entered entry
      | atomTuple _ shaped occurs =>
          rw [shape] at shaped
          simp only [Entry.Value.expression.injEq, List.cons.injEq] at shaped
          obtain ⟨_, rfl, _⟩ := shaped
          rw [Entry.Value.erase_ofAtom] at occurs
          have same := Mettapedia.Languages.MeTTa.HE.Spec.Type.TypeOccurrencesRel.unique occurs
            program.types.occurrences
          simp [Atom.undefinedType] at same
      | atomFallback _ shaped chosen =>
          rw [shape] at shaped
          simp only [Entry.Value.expression.injEq, List.cons.injEq] at shaped
          obtain ⟨_, rfl, _⟩ := shaped
          rw [Completed.Frame.read_empty, Entry.Value.erase_ofAtom, Entry.Value.erase_ofAtom]
            at chosen
          obtain ⟨_, _, _, _, impossible⟩ := cond_selection program typesC acceptsC keepsC typesY
            typesN chosen
          cases impossible
      | atomSelectionFailed _ shaped chosen =>
          rw [shape] at shaped
          simp only [Entry.Value.expression.injEq, List.cons.injEq] at shaped
          obtain ⟨_, rfl, _⟩ := shaped
          rw [Completed.Frame.read_empty, Entry.Value.erase_ofAtom, Entry.Value.erase_ofAtom]
            at chosen
          obtain ⟨_, _, _, _, impossible⟩ := cond_selection program typesC acceptsC keepsC typesY
            typesN chosen
          cases impossible
      | atomFunction _ shaped chosen =>
          rw [shape] at shaped
          simp only [Entry.Value.expression.injEq, List.cons.injEq] at shaped
          obtain ⟨_, rfl, rfl⟩ := shaped
          rw [Completed.Frame.read_empty, Entry.Value.erase_ofAtom, Entry.Value.erase_ofAtom]
            at chosen
          obtain ⟨signature, after, functionType, afterBindings, selected⟩ :=
            cond_selection program typesC acceptsC keepsC typesY typesN chosen
          simp only [Completed.InvocationSelection.selected.injEq] at selected
          obtain ⟨rfl, rfl⟩ := selected
          have returnTypeOf : ∀ {s : SelectedTypePolicy}, s.returnType = .var "t" →
              Completed.invocationReturnType s = .var "t" := by
            intro s same
            simp [Completed.invocationReturnType, same, Atom.expressionType]
          apply fine_invocations_cons
          rw [returnTypeOf (if_projections functionType).2]
          simp only [List.map_cons, List.map_nil]
          refine fine_bag_function program bag functionType afterBindings _ _ ?_
          intro R shapeR
          apply fine_calls_frame
          refine fine_bag_calls notHost program bag R Lc (fun _ member => member) shapeR
            bag.booleans _ _ ?_
          intro Q eraseQ
          apply fine_append
          apply fine_invocations_nil
          apply fine_prepend
          refine fine_publish (HENested.clean_of_erase (by simpa using eraseQ) cleanL) ?_
          exact fine_top _ _

/-- **Every run of `(if c y n)` on a nondeterministic condition finishes, and every finished run
publishes `answersOf Lc Ly Ln`.** Under the hypotheses of `IfBags.bag_every_run`: HE's step relation
is well founded from the entry, every reachable configuration steps or is final, a final one
publishes exactly `answersOf Lc Ly Ln`, and PeTTa yields the same list from some fuel on. -/
theorem bag_every_run_finishes (dispatch : GroundedDispatch)
    (notHost : ¬ dispatch.executable (.symbol "if")) (policy : Policy) {atoms : List Atom}
    (program : IfCallProgram atoms) {c y n : Atom} {Lc Ly Ln : List Atom}
    (bag : BagIf dispatch atoms c y n Lc Ly Ln) :
    Acc (fun later earlier => HEStep dispatch Completed.rawLookup policy earlier later)
        (load (Space.ofList atoms) (callC c y n) Atom.undefinedType) ∧
      (∀ x, Relation.ReflTransGen (HEStep dispatch Completed.rawLookup policy)
          (load (Space.ofList atoms) (callC c y n) Atom.undefinedType) x →
        (∃ z, HEStep dispatch Completed.rawLookup policy x z) ∨
          ∃ emitted : List Result, x = ⟨Space.ofList atoms, .returning [], [], emitted⟩ ∧
            emitted.map (fun r => r.1.erase) = answersOf Lc Ly Ln) ∧
      ∃ N : Nat, ∀ k, N ≤ k → Streaming.values (Streaming.advance (translate atoms) k
        (Streaming.enter { state := store atoms } (callC c y n))) = answersOf Lc Ly Ln := by
  have fine := bag_fine notHost policy program bag
  refine ⟨fine.acc, fun x path => ?_, (bag_every_run dispatch notHost policy program bag).2.2⟩
  rcases (fine.reaches path).progress with moves | ⟨space, emitted, rfl⟩
  · exact Or.inl moves
  · have sameSpace := space_fixed path
    simp only [load, Mettapedia.Languages.MeTTa.HE.RecursiveTasks.Contextual.Configuration.initial]
      at sameSpace
    subst sameSpace
    exact Or.inr ⟨emitted, rfl, bag_source program bag (complete_source path)⟩

/-! ## Controls -/

namespace Controls

open WholeRunWords.Double (noHost)
open IfComputed.Controls (num)
open IfBags.Controls (coinRows coin_program coin_bag coin2_bag)

/-- **`(if (coin) (half 4) (pair a b))`, every run**: no infinite run from the entry, and every final
configuration publishes `[two, (pair a b)]`. -/
theorem coin_pair_finishes (policy : Policy) :
    Acc (fun later earlier => HEStep noHost Completed.rawLookup policy earlier later)
        (load (Space.ofList coinRows)
          (callC (app "coin" []) (app "half" [num 4]) (app "pair" [sym "a", sym "b"]))
          Atom.undefinedType) ∧
      ∀ x, Relation.ReflTransGen (HEStep noHost Completed.rawLookup policy)
          (load (Space.ofList coinRows)
            (callC (app "coin" []) (app "half" [num 4]) (app "pair" [sym "a", sym "b"]))
            Atom.undefinedType) x →
        (∃ z, HEStep noHost Completed.rawLookup policy x z) ∨
          ∃ emitted : List Result, x = ⟨Space.ofList coinRows, .returning [], [], emitted⟩ ∧
            emitted.map (fun r => r.1.erase) = [sym "two", app "pair" [sym "a", sym "b"]] := by
  obtain ⟨acc, every, -⟩ := bag_every_run_finishes noHost (fun impossible => impossible) policy
    coin_program coin_bag
  have answers : answersOf [.grounded (.bool true), .grounded (.bool false)] [sym "two"]
      [app "pair" [sym "a", sym "b"]] = [sym "two", app "pair" [sym "a", sym "b"]] := by
    decide +kernel
  rw [answers] at every
  exact ⟨acc, every⟩

/-- **`(if (coin2) yes no)`, every run**: no infinite run, and every final configuration publishes
`yes` twice. -/
theorem coin_twice_finishes (policy : Policy) :
    Acc (fun later earlier => HEStep noHost Completed.rawLookup policy earlier later)
        (load (Space.ofList coinRows) (callC (app "coin2" []) (sym "yes") (sym "no"))
          Atom.undefinedType) ∧
      ∀ x, Relation.ReflTransGen (HEStep noHost Completed.rawLookup policy)
          (load (Space.ofList coinRows) (callC (app "coin2" []) (sym "yes") (sym "no"))
            Atom.undefinedType) x →
        (∃ z, HEStep noHost Completed.rawLookup policy x z) ∨
          ∃ emitted : List Result, x = ⟨Space.ofList coinRows, .returning [], [], emitted⟩ ∧
            emitted.map (fun r => r.1.erase) = [sym "yes", sym "yes"] := by
  obtain ⟨acc, every, -⟩ := bag_every_run_finishes noHost (fun impossible => impossible) policy
    coin_program coin2_bag
  have answers : answersOf [.grounded (.bool true), .grounded (.bool true)] [sym "yes"]
      [sym "no"] = [sym "yes", sym "yes"] := by
    decide +kernel
  rw [answers] at every
  exact ⟨acc, every⟩

end Controls

#print axioms fine_condition_branches
#print axioms fine_bag_calls
#print axioms fine_bag_function
#print axioms bag_fine
#print axioms bag_every_run_finishes
#print axioms Controls.coin_pair_finishes
#print axioms Controls.coin_twice_finishes

end IfBagsFinishes

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.TriangleFootprints
