import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.TriangleFootprints.IfCallBranches

/-!
# HE's `if` on a nondeterministic condition: the answers as a bag, on every run

`IfCallBranches` takes a condition with one Boolean answer. A condition may have several, for
instance a call with two matching rows. HE evaluates the condition under `Bool` to all its answers,
delivers both branches once per answer, and queries `if` once per answer; PeTTa's branch frame takes,
for each answer in turn, the branch it selects. Both publish, for each condition answer in order, the
answers of the branch it selects:

  `answersOf Lc Ly Ln = Lc.flatMap (fun a => if a = True then Ly else Ln)`.

The two lists are equal, so in particular equal as bags (multisets): order is not an observation in
either dialect, multiplicity is, and equal lists agree on both.

* `condition_packets`: every derivation of the argument branches over the condition's answers
  yields one argument packet per answer, in order.
* `bag_calls`: every derivation of the calls continuation over the assembled calls returns, per
  answer, the answers of the branch it selects.
* `bag_source`, `bag_run`: every derivation from the entry publishes `answersOf`; a complete run
  exists.
* `petta_if_bag`: PeTTa's special form gives the same list.
* `bag_every_run`: the three together, with the conclusion also stated as equal multisets.

## Controls

* `Controls.coin_pair` (`(if (coin) (half 4) (pair a b))` with `(= (coin) True)`,
  `(= (coin) False)`): every complete HE run publishes `[two, (pair a b)]`, as PeTTa does; the bag
  has one copy of each.
* `Controls.coin_twice` (multiplicity): `(if (coin2) yes no)` with two rows answering `True` publishes
  `yes` twice on every run, in both dialects; a set reading would lose a copy.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.TriangleFootprints

namespace IfBags

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.HE (Space Bindings isErrorAtom)
open Mettapedia.Languages.MeTTa.HE.Spec.Eval
open Mettapedia.Languages.MeTTa.HE.Spec.Eval.Steps (EquationWork EquationFrontierRel)
open Mettapedia.Languages.MeTTa.HE.Spec.Eval.Completed (Policy Result CastLookup Frame)
open Mettapedia.Languages.MeTTa.HE.Spec.Type (TypeMatchRel StorageTypesRel rawTypeLookupRel
  FunctionTypeRel)
open Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation (TypeSubst)
open Mettapedia.Languages.MeTTa.HE.Spec.Match.Merge (AtomOccurs)
open Mettapedia.Languages.MeTTa.HE.RecursiveMachine.Contextual (LocalStepWith load)
open Mettapedia.Languages.MeTTa.HE.RecursiveTasks.Contextual (Control Continuation)
open Mettapedia.Languages.MeTTa.PeTTa
open Mettapedia.Languages.ProcessCalculi.MORK (Subst isGroundAtom)
open ServiceFootprints EntryToQuery AnswerBags EveryRun BoundVariables NestedArguments
  NestedEveryRun NestedValues NestedCalls MarkedValues CompoundBindings DeclaredHeads
  DeclaredEveryRun TypedEveryRun AtomDemands IfEveryRun IfBranches DemandSpine IfComputed
  IfCallBranches
open AnswerBags.Controls (sym app rule rule_consFree)

variable {dispatch : GroundedDispatch} {policy : Policy}

/-! ## The answers -/

/-- The Boolean an answer stands for (`True` or anything else). -/
def truth (a : Atom) : Bool := a == .grounded (.bool true)

/-- **The answers of `(if c y n)`**: for each answer of the condition in order, the answers of the
branch it selects. -/
def answersOf (Lc Ly Ln : List Atom) : List Atom :=
  Lc.flatMap fun a => if truth a then Ly else Ln

theorem truth_bool (b : Bool) : truth (.grounded (.bool b)) = b := by
  cases b <;> rfl

/-- **The program, the condition and the branches.** The condition settles with Boolean answers
`Lc`, its one stored type meets `Bool`; both branches settle (each may be taken) with answers whose
data form `$t` casts as they are; both are closed with one stored type; and for every Boolean the
condition answers, the region of `if` is HE's row of that Boolean. -/
structure BagIf (dispatch : GroundedDispatch) (atoms : List Atom) (c y n : Atom)
    (Lc Ly Ln : List Atom) : Prop where
  conditionSettles : SettlesK dispatch atoms c Lc
  booleans : ∀ a ∈ Lc, ∃ b : Bool, a = .grounded (.bool b)
  conditionTyped : ∃ T, StorageTypesRel (Space.ofList atoms) c [T] ∧
    (∀ bnd : Bindings, TypeMatchRel (sym "Bool") T bnd bnd) ∧
    (∀ bnd out : Bindings, TypeMatchRel (sym "Bool") T bnd out → out = bnd)
  yesSettles : SettlesK dispatch atoms y Ly
  noSettles : SettlesK dispatch atoms n Ln
  yesCasts : ∀ a ∈ Ly, DataAtom a → CastsAt atoms (.var "t") a
  noCasts : ∀ a ∈ Ln, DataAtom a → CastsAt atoms (.var "t") a
  typedYes : ∃ T, StorageTypesRel (Space.ofList atoms) y [T]
  typedNo : ∃ T, StorageTypesRel (Space.ofList atoms) n [T]
  regions : ∀ b : Bool, Atom.grounded (.bool b) ∈ Lc → IfRegion atoms b y n

theorem BagIf.closedYes {atoms : List Atom} {c y n : Atom} {Lc Ly Ln : List Atom}
    (bag : BagIf dispatch atoms c y n Lc Ly Ln) : ∀ name, ¬ AtomOccurs y name :=
  (settlesK_shape bag.yesSettles).1.answerable.closed

theorem BagIf.closedNo {atoms : List Atom} {c y n : Atom} {Lc Ly Ln : List Atom}
    (bag : BagIf dispatch atoms c y n Lc Ly Ln) : ∀ name, ¬ AtomOccurs n name :=
  (settlesK_shape bag.noSettles).1.answerable.closed

/-- The branches of one Boolean answer, as `IfCallBranches` asks them. -/
theorem BagIf.branches {atoms : List Atom} {c y n : Atom} {Lc Ly Ln : List Atom}
    (bag : BagIf dispatch atoms c y n Lc Ly Ln) (b : Bool) (inLc : Atom.grounded (.bool b) ∈ Lc) :
    CallBranches dispatch atoms b y n (if b then Ly else Ln) := by
  cases b with
  | true =>
      exact ⟨bag.yesSettles, bag.yesCasts, bag.closedYes, bag.closedNo,
        (settlesK_shape bag.yesSettles).1.answerable.ground,
        (settlesK_shape bag.noSettles).1.answerable.ground, bag.typedYes, bag.typedNo,
        bag.regions true inLc⟩
  | false =>
      exact ⟨bag.noSettles, bag.noCasts, bag.closedYes, bag.closedNo,
        (settlesK_shape bag.yesSettles).1.answerable.ground,
        (settlesK_shape bag.noSettles).1.answerable.ground, bag.typedYes, bag.typedNo,
        bag.regions false inLc⟩

theorem BagIf.conditionCasts {atoms : List Atom} {c y n : Atom} {Lc Ly Ln : List Atom}
    (bag : BagIf dispatch atoms c y n Lc Ly Ln) :
    ∀ a ∈ Lc, DataAtom a → CastsAt atoms (sym "Bool") a := by
  intro a member _
  obtain ⟨b, rfl⟩ := bag.booleans a member
  exact bool_casts atoms b

/-! ## Every derivation -/

/-- **The argument branches over the condition's answers yield one packet per answer, in order.** -/
theorem condition_packets {space : Space} {lookup : CastLookup} {live : List Atom}
    {scope : List String} {c y n : Atom}
    (readY : ∀ frame : Frame, frame.read policy (Entry.Value.ofAtom y) = Entry.Value.ofAtom y)
    (readN : ∀ frame : Frame, frame.read policy (Entry.Value.ofAtom n) = Entry.Value.ofAtom n) :
    ∀ (heads : List Result) (Lc : List Atom), heads.map (fun r => r.1.erase) = Lc →
      (∀ a ∈ Lc, ∃ b : Bool, a = .grounded (.bool b)) → ∀ {results : List Result},
      Completed.ArgumentBranchesRel space dispatch lookup live scope (Entry.Value.ofAtom c)
        [(Entry.Value.ofAtom y, Atom.atomType), (Entry.Value.ofAtom n, Atom.atomType)] heads results
        (policy := policy) →
      results.map (fun r => r.1) = Lc.map fun a =>
        Entry.Value.argumentPacket [Entry.Value.ofAtom a, Entry.Value.ofAtom y, Entry.Value.ofAtom n]
  | [], Lc, erased, _, _, derived => by
      cases derived
      simp at erased
      subst erased
      rfl
  | h :: hs, Lc, erased, booleans, _, derived => by
      obtain ⟨a, Lc', rfl⟩ : ∃ a Lc', Lc = a :: Lc' := by
        cases Lc with
        | nil => simp at erased
        | cons a Lc' => exact ⟨a, Lc', rfl⟩
      simp only [List.map_cons, List.cons.injEq] at erased
      obtain ⟨headErase, restErase⟩ := erased
      obtain ⟨b, rfl⟩ := booleans _ List.mem_cons_self
      have hValue := value_of_data (.grounded (.bool b)) headErase
      obtain ⟨hv, fr⟩ := h
      simp only at hValue
      subst hValue
      cases derived with
      | stopped stopped _ =>
          obtain ⟨stoppedCondition, _⟩ := stopped
          rw [Entry.Value.erase_ofAtom] at stoppedCondition
          exact absurd stoppedCondition (DataAtom.grounded (.bool b)).not_stopped
      | continuing _ yesArguments later =>
          have rest := condition_packets readY readN hs Lc' restErase
            (fun a member => booleans a (List.mem_cons_of_mem _ member)) later
          cases yesArguments with
          | cons yesRel yesBranches =>
              have yesDelivered := atom_demand_source yesRel
              subst yesDelivered
              rw [readY] at yesBranches
              cases yesBranches with
              | stopped stopped _ =>
                  obtain ⟨_, different⟩ := stopped
                  exact absurd rfl different
              | continuing _ noArguments restYes =>
                  cases restYes
                  cases noArguments with
                  | cons noRel noBranches =>
                      have noDelivered := atom_demand_source noRel
                      subst noDelivered
                      rw [readN] at noBranches
                      cases noBranches with
                      | stopped stopped _ =>
                          obtain ⟨_, different⟩ := stopped
                          exact absurd rfl different
                      | continuing _ packets restNo =>
                          cases restNo
                          cases packets
                          simp only [List.map_cons, List.map_nil, List.append_nil,
                            Completed.argumentPrepend_packet, List.cons_append, List.nil_append]
                          rw [rest]

/-- **The calls over the assembled values return, per answer, the selected branch's answers.** -/
theorem bag_calls {atoms : List Atom} (program : IfCallProgram atoms) {c y n : Atom}
    {Lc Ly Ln : List Atom} (bag : BagIf dispatch atoms c y n Lc Ly Ln) {live : List Atom}
    {scope : List String} :
    ∀ (rows : List Result) (as : List Atom), as ⊆ Lc →
      rows.map (fun r => r.1) = as.map (fun a =>
        (Completed.functionAssemble (Entry.Value.ofAtom (.symbol "if"))
          (Entry.Value.argumentPacket [Entry.Value.ofAtom a, Entry.Value.ofAtom y,
            Entry.Value.ofAtom n], Completed.Frame.empty)).1) →
      ∀ {raw : List Result},
        Completed.CallsRel (Space.ofList atoms) dispatch Completed.rawLookup live scope (.var "t")
          rows raw (policy := policy) →
        raw.map (fun r => r.1.erase) = answersOf as Ly Ln
  | [], as, _, shaped, _, derived => by
      cases derived
      cases as with
      | nil => rfl
      | cons _ _ => simp at shaped
  | r :: rs, as, within, shaped, _, derived => by
      obtain ⟨a, as', rfl⟩ : ∃ a as', as = a :: as' := by
        cases as with
        | nil => simp at shaped
        | cons a as' => exact ⟨a, as', rfl⟩
      simp only [List.map_cons, List.cons.injEq] at shaped
      obtain ⟨headValue, restValues⟩ := shaped
      have inLc : a ∈ Lc := within List.mem_cons_self
      obtain ⟨b, rfl⟩ := bag.booleans a inLc
      cases derived with
      | cons called later =>
          have valueEq : r.1 = callValueOf b y n := by
            rw [headValue, assembled_eq]
          obtain ⟨rv, fr⟩ := r
          simp only at valueEq
          subst valueEq
          have here := call_query_source (policy := policy) program (bag.branches b inLc) called
          have rest := bag_calls program bag rs as' (fun x member => within (List.mem_cons_of_mem _ member))
            restValues later
          rw [List.map_append, here, rest]
          cases b <;> simp [answersOf, truth_bool]

/-- The assembled value depends only on the packet, not on its frame. -/
theorem assemble_fst (head : Entry.Value) (r : Result) (frame : Frame) :
    (Completed.functionAssemble head r).1 = (Completed.functionAssemble head (r.1, frame)).1 := by
  simp only [Completed.functionAssemble]
  split <;> rfl

theorem answersOf_answerable {Lc Ly Ln : List Atom} (yes : ∀ a ∈ Ly, Answerable a)
    (no : ∀ a ∈ Ln, Answerable a) : ∀ a ∈ answersOf Lc Ly Ln, Answerable a := by
  intro a member
  obtain ⟨c, _, inner⟩ := List.mem_flatMap.mp member
  split at inner
  · exact yes a inner
  · exact no a inner

/-- **Every derivation of HE's completed relation for `(if c y n)` publishes `answersOf`.** -/
theorem bag_source {atoms : List Atom} (program : IfCallProgram atoms) {c y n : Atom}
    {Lc Ly Ln : List Atom} (bag : BagIf dispatch atoms c y n Lc Ly Ln) {results : List Result}
    (derived : Completed.AtomRel (Space.ofList atoms) dispatch Completed.rawLookup [] []
      (Entry.Value.ofAtom (callC c y n)) Atom.undefinedType Completed.Frame.empty results
      (policy := policy)) :
    results.map (fun r => r.1.erase) = answersOf Lc Ly Ln := by
  obtain ⟨Tc, typesC, acceptsC, keepsC⟩ := bag.conditionTyped
  obtain ⟨Ty, typesY⟩ := bag.typedYes
  obtain ⟨Tn, typesN⟩ := bag.typedNo
  have conditionDetermined := (settlesK_at (policy := policy) program.rows bool_transparent
    bag.conditionSettles bag.conditionCasts).2
  have clean := answersOf_answerable (Lc := Lc) (settlesK_shape bag.yesSettles).1.answers
    (settlesK_shape bag.noSettles).1.answers
  have entry := call_entry policy if_data [c, y, n]
  have shape : Completed.Frame.empty.read policy (Entry.Value.ofAtom (callC c y n)) =
      .expression .active (Entry.Value.ofAtom (.symbol "if") ::
        [c, y, n].map Entry.Value.ofAtom) := by
    rw [Completed.Frame.read_empty]
    simp only [callC, app, Entry.Value.ofAtom, List.map_cons, List.map_nil]
  have outcome : ∀ {result : Completed.InvocationSelection},
      Completed.InvocationSelectionRel (Space.ofList atoms) Completed.rawLookup policy [] []
        (Completed.Frame.empty.read policy (Entry.Value.ofAtom (callC c y n))).erase
        (Entry.Value.ofAtom (.symbol "if")).erase Atom.undefinedType Completed.Frame.empty result →
      ∃ (signature : SelectedTypePolicy) (after : Frame), signature.functionType = ifArrow ∧
        after.bindings = Bindings.empty ∧ result = .selected signature [after] := by
    intro result chosenRel
    rw [Completed.Frame.read_empty, Entry.Value.erase_ofAtom, Entry.Value.erase_ofAtom] at chosenRel
    exact cond_selection program typesC acceptsC keepsC typesY typesN chosenRel
  have readY : ∀ frame : Frame, frame.read policy (Entry.Value.ofAtom y) = Entry.Value.ofAtom y :=
    fun frame => HERuns.read_closed policy frame bag.closedYes
  have readN : ∀ frame : Frame, frame.read policy (Entry.Value.ofAtom n) = Entry.Value.ofAtom n :=
    fun frame => HERuns.read_closed policy frame bag.closedNo
  cases derived with
  | delivered entered => cases Entry.functional entered entry
  | cast entered => cases Entry.functional entered entry
  | tuple _ shaped occurs _ _ _ =>
      rw [shape] at shaped
      simp only [Entry.Value.expression.injEq, List.cons.injEq] at shaped
      obtain ⟨_, rfl, _⟩ := shaped
      rw [Entry.Value.erase_ofAtom] at occurs
      have same := Mettapedia.Languages.MeTTa.HE.Spec.Type.TypeOccurrencesRel.unique occurs
        program.types.occurrences
      simp [Atom.undefinedType] at same
  | fallback _ shaped chosenRel _ _ _ =>
      rw [shape] at shaped
      simp only [Entry.Value.expression.injEq, List.cons.injEq] at shaped
      obtain ⟨_, rfl, _⟩ := shaped
      obtain ⟨_, _, _, _, impossible⟩ := outcome chosenRel
      cases impossible
  | selectionFailed _ shaped chosenRel _ =>
      rw [shape] at shaped
      simp only [Entry.Value.expression.injEq, List.cons.injEq] at shaped
      obtain ⟨_, rfl, _⟩ := shaped
      obtain ⟨_, _, _, _, impossible⟩ := outcome chosenRel
      cases impossible
  | function _ shaped chosenRel invoked priority =>
      rw [shape] at shaped
      simp only [Entry.Value.expression.injEq, List.cons.injEq] at shaped
      obtain ⟨_, rfl, rfl⟩ := shaped
      obtain ⟨signature, after, functionType, afterBindings, selected⟩ := outcome chosenRel
      simp only [Completed.InvocationSelection.selected.injEq] at selected
      obtain ⟨rfl, rfl⟩ := selected
      have projections := if_projections functionType
      have returnTypeOf : ∀ {s : SelectedTypePolicy}, s.returnType = .var "t" →
          Completed.invocationReturnType s = .var "t" := by
        intro s same
        simp [Completed.invocationReturnType, same, Atom.expressionType]
      have returnType := returnTypeOf projections.2
      cases invoked with
      | cons function calls rest =>
          cases rest
          cases function with
          | evaluated _ operatorRel branchesRel =>
              rw [functionType] at operatorRel
              obtain ⟨frF, rfl⟩ := typed_cast_source_at if_data
                (symbol_cast_entry (by decide) (by decide) (by decide +kernel)) program.types
                (ifArrow_accepts afterBindings) operatorRel
              rw [projections.1] at branchesRel
              simp only [List.map_cons, List.map_nil, List.zip_cons_cons, List.zip_nil_right]
                at branchesRel
              cases branchesRel with
              | stopped stopped _ =>
                  rw [Entry.Value.erase_ofAtom] at stopped
                  exact absurd stopped if_data.not_stopped
              | continuing _ arguments restBranches =>
                  cases restBranches
                  cases arguments with
                  | cons conditionRel conditionBranches =>
                      have conditionErase := conditionDetermined (Entry.Value.ofAtom c)
                        (Entry.Value.erase_ofAtom c) (marked_ofAtom c) _ _ _ _ conditionRel
                      have packetsEq := condition_packets readY readN _ Lc conditionErase
                        bag.booleans conditionBranches
                      rw [returnType] at calls
                      simp only [List.append_nil] at calls
                      have answered := bag_calls program bag _ Lc (fun _ member => member)
                        (by
                          rw [List.map_map]
                          have viaFst : ((fun r => r.1) ∘ Completed.functionAssemble
                              (Entry.Value.ofAtom (.symbol "if"))) =
                              (fun r : Result => (Completed.functionAssemble
                                (Entry.Value.ofAtom (.symbol "if")) (r.1, Completed.Frame.empty)).1) := by
                            funext r
                            exact assemble_fst _ r _
                          rw [viaFst]
                          have mapped := congrArg (List.map fun v : Entry.Value =>
                            (Completed.functionAssemble (Entry.Value.ofAtom (.symbol "if"))
                              (v, Completed.Frame.empty)).1) packetsEq
                          simpa only [List.map_map, Function.comp_def] using mapped)
                        calls
                      exact publish_answers (by simp only [List.append_nil]; exact answered)
                        clean priority

/-! ## A complete run -/

/-- **HE's machine delivers both branches once per condition answer**, building one packet each. -/
theorem branches_path (dispatch : GroundedDispatch) (policy : Policy) (space : Space)
    {live : List Atom} {c y n : Atom}
    (readY : ∀ frame : Frame, frame.read policy (Entry.Value.ofAtom y) = Entry.Value.ofAtom y)
    (readN : ∀ frame : Frame, frame.read policy (Entry.Value.ofAtom n) = Entry.Value.ofAtom n) :
    ∀ (R : List Result), (∀ r ∈ R, ∃ b : Bool, r.1 = Entry.Value.ofAtom (.grounded (.bool b))) →
      ∀ (stack : List Continuation), ∃ out : List Result,
        out.map (fun r => r.1) = R.map (fun r =>
          Entry.Value.argumentPacket [r.1, Entry.Value.ofAtom y, Entry.Value.ofAtom n]) ∧
        HERuns.HESteps dispatch Completed.rawLookup policy
          ⟨space, .work (.argumentBranches live [] (Entry.Value.ofAtom c)
            [(Entry.Value.ofAtom y, Atom.atomType), (Entry.Value.ofAtom n, Atom.atomType)] R),
            stack, []⟩
          ⟨space, .returning out, stack, []⟩
  | [], _, stack => ⟨[], rfl, .single (.internal .argumentBranchesNil)⟩
  | r :: rs, booleans, stack => by
      obtain ⟨b, rValue⟩ := booleans r List.mem_cons_self
      obtain ⟨rv, fr⟩ := r
      simp only at rValue
      subst rValue
      obtain ⟨out, outEq, path⟩ := branches_path dispatch policy space readY readN rs
        (fun x member => booleans x (List.mem_cons_of_mem _ member))
        (.prepend [(Entry.Value.argumentPacket [Entry.Value.ofAtom (.grounded (.bool b)),
          Entry.Value.ofAtom y, Entry.Value.ofAtom n], fr)] :: stack)
      refine ⟨[(Entry.Value.argumentPacket [Entry.Value.ofAtom (.grounded (.bool b)),
        Entry.Value.ofAtom y, Entry.Value.ofAtom n], fr)] ++ out, ?_, ?_⟩
      · simp [outEq]
      · refine .head (.internal (.argumentBranchesContinue ?_)) ?_
        · rintro ⟨stopped, _⟩
          exact (DataAtom.grounded (.bool b)).not_stopped (by simpa using stopped)
        refine .head (.internal .argumentsCons) ?_
        refine .head (.internal (.delivered (atom_demand_deliver _))) ?_
        refine .head (.internal .arguments) ?_
        refine .head (.internal (.argumentBranchesContinue ?_)) ?_
        · rintro ⟨_, different⟩
          simp only [readY] at different
          exact different rfl
        refine .head (.internal .argumentsCons) ?_
        refine .head (.internal (.delivered (atom_demand_deliver _))) ?_
        refine .head (.internal .arguments) ?_
        refine .head (.internal (.argumentBranchesContinue ?_)) ?_
        · rintro ⟨_, different⟩
          simp only [readN] at different
          exact different rfl
        refine .head (.internal .argumentsNil) ?_
        refine .head (.internal .argumentTail) ?_
        refine .head (.internal .append) ?_
        refine .head (.internal .argumentBranchesNil) ?_
        refine .head (.internal .prepend) ?_
        refine .head (.internal .argumentTail) ?_
        refine .head (.internal .append) ?_
        refine .head (.internal .argumentBranchesNil) ?_
        refine .head (.internal .prepend) ?_
        refine .head (.internal .argumentTail) ?_
        simp only [readY, readN, List.map_cons, List.map_nil, List.append_nil,
          Completed.argumentPrepend_packet]
        refine .head (.internal .append) ?_
        refine .trans path ?_
        exact .single (.internal .prepend)

/-- **The calls over the assembled values run, per answer, to the selected branch's answers.** -/
theorem bag_calls_path (dispatch : GroundedDispatch) (notHost : ¬ dispatch.executable (.symbol "if"))
    (policy : Policy) {atoms : List Atom} (program : IfCallProgram atoms) {c y n : Atom}
    {Lc Ly Ln : List Atom} (bag : BagIf dispatch atoms c y n Lc Ly Ln) :
    ∀ (rows : List Result) (as : List Atom), as ⊆ Lc →
      rows.map (fun r => r.1) = as.map (fun a => callValueOf (truth a) y n) →
      (∀ a ∈ as, ∃ b : Bool, a = .grounded (.bool b)) →
      ∀ (stack : List Continuation), ∃ R : List Result,
        R.map (fun r => r.1.erase) = answersOf as Ly Ln ∧
        HERuns.HESteps dispatch Completed.rawLookup policy
          ⟨Space.ofList atoms, .work (.calls [] [] (.var "t") rows), stack, []⟩
          ⟨Space.ofList atoms, .returning R, stack, []⟩
  | [], as, _, shaped, _, stack => by
      cases as with
      | nil => exact ⟨[], rfl, .single (.internal .callsNil)⟩
      | cons _ _ => simp at shaped
  | r :: rs, as, within, shaped, booleans, stack => by
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
      obtain ⟨Q, pathQ, eraseQ⟩ := call_query dispatch notHost policy program (bag.branches b inLc) fr
        (.append (.calls [] [] (.var "t") rs) :: stack)
      obtain ⟨Rs, eraseRs, pathRs⟩ := bag_calls_path dispatch notHost policy program bag rs as'
        (fun x member => within (List.mem_cons_of_mem _ member)) restValues
        (fun x member => booleans x (List.mem_cons_of_mem _ member)) (.prepend Q :: stack)
      refine ⟨Q ++ Rs, ?_, ?_⟩
      · rw [List.map_append, eraseQ, eraseRs]
        cases b <;> simp [answersOf, truth_bool]
      · refine .head (.internal .callsCons) ?_
        refine .trans pathQ ?_
        refine .head (.internal .append) ?_
        refine .trans pathRs ?_
        exact .single (.internal .prepend)

theorem assembled_rows {y n : Atom} :
    ∀ (R : List Result), (∀ r ∈ R, ∃ b : Bool, r.1 = Entry.Value.ofAtom (.grounded (.bool b))) →
      R.map (fun r => (Completed.functionAssemble (Entry.Value.ofAtom (.symbol "if"))
        (Entry.Value.argumentPacket [r.1, Entry.Value.ofAtom y, Entry.Value.ofAtom n],
          Completed.Frame.empty)).1) =
        (R.map fun r => r.1.erase).map (fun a => callValueOf (truth a) y n)
  | [], _ => rfl
  | r :: rs, booleans => by
      obtain ⟨b, rValue⟩ := booleans r List.mem_cons_self
      simp only [List.map_cons]
      rw [assembled_rows rs (fun x member => booleans x (List.mem_cons_of_mem _ member)), rValue,
        assembled_eq, Entry.Value.erase_ofAtom, truth_bool]

/-- **The function application of `(if c y n)` on a condition with several answers**: one call value
per answer, in order. -/
theorem bag_function_segment (dispatch : GroundedDispatch) (policy : Policy)
    {atoms : List Atom} (program : IfCallProgram atoms) {c y n : Atom} {Lc Ly Ln : List Atom}
    (bag : BagIf dispatch atoms c y n Lc Ly Ln) (stack : List Continuation) :
    ∃ results : List Result,
      HERuns.HESteps dispatch Completed.rawLookup policy
        ⟨Space.ofList atoms, .work (.function [Completed.invocationReturnType ifPolicy] []
          Atom.undefinedType ifPolicy (Entry.Value.ofAtom (.symbol "if"))
          [Entry.Value.ofAtom c, Entry.Value.ofAtom y, Entry.Value.ofAtom n]
          Completed.Frame.empty), stack, []⟩
        ⟨Space.ofList atoms, .returning results, stack, []⟩ ∧
      results.map (fun r => r.1) = Lc.map (fun a => callValueOf (truth a) y n) := by
  obtain ⟨frF, renewal⟩ := if_operator_renewal policy
  have readY : ∀ frame : Frame, frame.read policy (Entry.Value.ofAtom y) = Entry.Value.ofAtom y :=
    fun frame => HERuns.read_closed policy frame bag.closedYes
  have readN : ∀ frame : Frame, frame.read policy (Entry.Value.ofAtom n) = Entry.Value.ofAtom n :=
    fun frame => HERuns.read_closed policy frame bag.closedNo
  have ifCast := renewed_cast_step dispatch policy (atom := .symbol "if") (closed_symbol "if")
    (symbol_cast_entry (by decide) (by decide) (by decide +kernel)) program.types
    Completed.Frame.empty frF renewal
  have conditionRuns := (settlesK_at (policy := policy) program.rows bool_transparent
    bag.conditionSettles bag.conditionCasts).1 (Entry.Value.ofAtom c) (Entry.Value.erase_ofAtom c)
    (marked_ofAtom c)
  obtain ⟨R, eraseR, conditionRun⟩ := conditionRuns
    (Completed.argumentScope (requestsOf c y n).tail ++
      [(Entry.Value.ofAtom (.symbol "if")).erase, Completed.invocationReturnType ifPolicy])
    [] frF
    (.arguments [(Entry.Value.ofAtom (.symbol "if")).erase, Completed.invocationReturnType ifPolicy]
        [] (Entry.Value.ofAtom c) (requestsOf c y n).tail ::
      .functionAssemble (Entry.Value.ofAtom (.symbol "if")) ::
      .append (.functionBranches [Completed.invocationReturnType ifPolicy] [] (requestsOf c y n) []) ::
      stack) []
  have booleans : ∀ r ∈ R, ∃ b : Bool, r.1 = Entry.Value.ofAtom (.grounded (.bool b)) := by
    intro r member
    have inLc : r.1.erase ∈ Lc := by
      rw [← eraseR]
      exact List.mem_map.mpr ⟨r, member, rfl⟩
    obtain ⟨b, same⟩ := bag.booleans _ inLc
    exact ⟨b, value_of_data (.grounded _) same⟩
  obtain ⟨out, outEq, branchesRun⟩ := branches_path dispatch policy (Space.ofList atoms)
    (live := [(Entry.Value.ofAtom (.symbol "if")).erase, Completed.invocationReturnType ifPolicy])
    (c := c) readY readN R booleans
    (.functionAssemble (Entry.Value.ofAtom (.symbol "if")) ::
      .append (.functionBranches [Completed.invocationReturnType ifPolicy] [] (requestsOf c y n) []) ::
      stack)
  refine ⟨out.map (Completed.functionAssemble (Entry.Value.ofAtom (.symbol "if"))) ++ [], ?_, ?_⟩
  · refine .head (.internal (.functionStart rfl)) ?_
    refine .head (ifCast _ _ _ _) ?_
    refine .head (.internal .functionHeads) ?_
    refine .head (.internal (.functionBranchesContinue ?_)) ?_
    · simpa using if_data.not_stopped
    refine .head (.internal .argumentsCons) ?_
    refine .trans conditionRun ?_
    refine .head (.internal .arguments) ?_
    refine .trans branchesRun ?_
    refine .head (.internal .functionAssemble) ?_
    refine .head (.internal .append) ?_
    refine .head (.internal .functionBranchesNil) ?_
    exact .single (.internal .prepend)
  · rw [List.append_nil, List.map_map]
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

/-- **A complete run of `(if c y n)` on HE's machine, publishing `answersOf`.** -/
theorem bag_run (dispatch : GroundedDispatch) (notHost : ¬ dispatch.executable (.symbol "if"))
    (policy : Policy) {atoms : List Atom} (program : IfCallProgram atoms) {c y n : Atom}
    {Lc Ly Ln : List Atom} (bag : BagIf dispatch atoms c y n Lc Ly Ln) :
    ∃ heAnswers : List Result,
      Relation.ReflTransGen (HEStep dispatch Completed.rawLookup policy)
          (load (Space.ofList atoms) (callC c y n) Atom.undefinedType)
          ⟨Space.ofList atoms, .returning [], [], heAnswers⟩ ∧
        heAnswers.map (fun r => r.1.erase) = answersOf Lc Ly Ln := by
  obtain ⟨Tc, typesC, acceptsC, _⟩ := bag.conditionTyped
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
  have step := LocalStepWith.atomFunction (admission := .historical)
    (space := Space.ofList atoms) (dispatch := dispatch) (lookup := Completed.rawLookup)
    (live := []) (scope := []) (stack := []) entry shape selection
  have published : (Completed.Frame.empty.read policy (Entry.Value.ofAtom (callC c y n))).erase =
      callC c y n := by
    rw [Completed.Frame.read_empty, Entry.Value.erase_ofAtom]
  rw [published] at step
  have returned : Completed.invocationReturnType ifPolicy = .var "t" := by
    simp [Completed.invocationReturnType, ifPolicy, Atom.expressionType]
  have booleans := bag.booleans
  obtain ⟨F, pathF, shapeF⟩ := bag_function_segment dispatch policy program bag
    (.calls [] [] (Completed.invocationReturnType ifPolicy) ::
      .append (.invocations [] [] Atom.undefinedType ifPolicy (Entry.Value.ofAtom (.symbol "if"))
        [Entry.Value.ofAtom c, Entry.Value.ofAtom y, Entry.Value.ofAtom n] []) ::
        [.publish (callC c y n)])
  obtain ⟨Q, eraseQ, pathQ⟩ := bag_calls_path dispatch notHost policy program bag F Lc
    (fun _ member => member) shapeF booleans
    (.append (.invocations [] [] Atom.undefinedType ifPolicy (Entry.Value.ofAtom (.symbol "if"))
        [Entry.Value.ofAtom c, Entry.Value.ofAtom y, Entry.Value.ofAtom n] []) ::
        [.publish (callC c y n)])
  have cleanL := answersOf_answerable (Lc := Lc) (settlesK_shape bag.yesSettles).1.answers
    (settlesK_shape bag.noSettles).1.answers
  have clean : ∀ r ∈ Q ++ [], Answerable r.1.erase := by
    intro r member
    simp only [List.append_nil] at member
    apply cleanL
    rw [← eraseQ]
    exact List.mem_map.mpr ⟨r, member, rfl⟩
  obtain ⟨publishedAnswers, eraseP, pathP⟩ := NestedArguments.HENested.publish_step
    (dispatch := dispatch) (lookup := Completed.rawLookup) (policy := policy) (atoms := atoms)
    (callC c y n) (Q ++ []) clean [] []
  refine ⟨publishedAnswers, ?_, by rw [eraseP]; simpa using eraseQ⟩
  refine .head (.internal step) ?_
  refine .head (.internal .invocationsCons) ?_
  refine .trans pathF ?_
  refine .head (.internal .calls) ?_
  rw [returned]
  refine .trans pathQ ?_
  refine .head (.internal .append) ?_
  refine .head (.internal .invocationsNil) ?_
  refine .head (.internal .prepend) ?_
  exact pathP.trans (HERuns.publish_all _ publishedAnswers [])

/-! ## PeTTa -/

/-- **PeTTa's special form on a condition with several Boolean answers**: the branch frame takes,
for each answer in turn, the branch it selects. -/
theorem petta_if_bag {atoms : List Atom} {c y n : Atom} {Lc Ly Ln : List Atom}
    (booleans : ∀ a ∈ Lc, ∃ b : Bool, a = .grounded (.bool b))
    (evalC : PeTTaEvaluates atoms c Lc) (evalY : PeTTaEvaluates atoms y Ly)
    (evalN : PeTTaEvaluates atoms n Ln) :
    PeTTaEvaluates atoms (callC c y n) (answersOf Lc Ly Ln) := by
  intro frames K deliver world σ state privateCode range fresh older answers next
  have branchDelivers : ∀ v ∈ Lc, Delivers atoms (.source (.branch y n) :: frames)
      (fun v => (if truth v then Ly else Ln).flatMap K) v := by
    intro v member
    obtain ⟨b, rfl⟩ := booleans v member
    intro world' σ' state' privateCode' range' fresh' older' answers' next'
    have deliverTaken : ∀ u ∈ (if b then Ly else Ln), Delivers atoms frames K u := by
      intro u inside
      apply deliver
      exact List.mem_flatMap.mpr ⟨_, member, by rw [truth_bool]; exact inside⟩
    have chosen : (if Atom.grounded (.bool b) == Effects.boolean true then y else n) =
        (if b then y else n) := by
      cases b <;> rfl
    have evalTaken : PeTTaEvaluates atoms (if b then y else n) (if b then Ly else Ln) := by
      cases b
      · exact evalN
      · exact evalY
    obtain ⟨uses, out, grown, valuesOut, path⟩ := evalTaken frames K deliverTaken world' σ' state'
      privateCode' range' fresh' older' answers' next'
    refine ⟨uses, out, grown, by rw [valuesOut]; simp [truth_bool], ?_⟩
    refine .head (branch_return_step world' ⟨.grounded (.bool b), σ'⟩ y n frames older' answers'
      next') ?_
    refine .head (PeTTaRuns.alternatives world' _ frames older' answers' next') ?_
    simp only [chosen, List.map_cons, List.map_nil, List.singleton_append]
    exact path
  obtain ⟨uses, out, grown, valuesOut, path⟩ := evalC (.source (.branch y n) :: frames)
    (fun v => (if truth v then Ly else Ln).flatMap K) branchDelivers world σ state privateCode range
    fresh older answers next
  refine ⟨uses, out, grown, ?_, .head (if_enter_step world σ c y n frames older answers next) path⟩
  rw [valuesOut, answersOf, List.flatMap_assoc]

/-! ## Every run -/

/-- **HE's `if` on a nondeterministic condition, on every run.** On a program carrying HE's
standard-library `if`, historical lookup, any policy and any dispatch that does not execute `if`,
for `(if c y n)` meeting `BagIf` (the condition settles with Boolean answers `Lc`, each branch settles
with answers whose data form `$t` casts as they are): a complete HE run exists, every complete run
publishes `answersOf Lc Ly Ln`, and PeTTa yields the same list from some fuel on. -/
theorem bag_every_run (dispatch : GroundedDispatch)
    (notHost : ¬ dispatch.executable (.symbol "if")) (policy : Policy) {atoms : List Atom}
    (program : IfCallProgram atoms) {c y n : Atom} {Lc Ly Ln : List Atom}
    (bag : BagIf dispatch atoms c y n Lc Ly Ln) :
    (∃ heAnswers : List Result,
      Relation.ReflTransGen (HEStep dispatch Completed.rawLookup policy)
          (load (Space.ofList atoms) (callC c y n) Atom.undefinedType)
          ⟨Space.ofList atoms, .returning [], [], heAnswers⟩) ∧
      (∀ emitted : List Result,
        Relation.ReflTransGen (HEStep dispatch Completed.rawLookup policy)
            (load (Space.ofList atoms) (callC c y n) Atom.undefinedType)
            ⟨Space.ofList atoms, .returning [], [], emitted⟩ →
          emitted.map (fun r => r.1.erase) = answersOf Lc Ly Ln) ∧
      ∃ N : Nat, ∀ k, N ≤ k → Streaming.values (Streaming.advance (translate atoms) k
        (Streaming.enter { state := store atoms } (callC c y n))) = answersOf Lc Ly Ln := by
  obtain ⟨heAnswers, path, _⟩ := bag_run dispatch notHost policy program bag
  have cShape := (settlesK_shape bag.conditionSettles).1
  have ground : isGroundAtom (callC c y n) = true := by
    simp [isGroundAtom, isGroundAtom.isGroundList, cShape.answerable.ground,
      (settlesK_shape bag.yesSettles).1.answerable.ground,
      (settlesK_shape bag.noSettles).1.answerable.ground]
  exact ⟨⟨heAnswers, path⟩,
    fun emitted run => bag_source program bag (complete_source run),
    petta_complete ground (answersOf_answerable (settlesK_shape bag.yesSettles).1.answers
        (settlesK_shape bag.noSettles).1.answers)
      (petta_if_bag bag.booleans (petta_settles program.rows bag.conditionSettles)
        (petta_settles program.rows bag.yesSettles) (petta_settles program.rows bag.noSettles))⟩

/-- **The same as bags**: every complete HE run and PeTTa's run from some fuel on publish equal
multisets of answers (order is not an observation, multiplicity is). -/
theorem bag_every_run_multiset (dispatch : GroundedDispatch)
    (notHost : ¬ dispatch.executable (.symbol "if")) (policy : Policy) {atoms : List Atom}
    (program : IfCallProgram atoms) {c y n : Atom} {Lc Ly Ln : List Atom}
    (bag : BagIf dispatch atoms c y n Lc Ly Ln) :
    ∃ N : Nat, ∀ k, N ≤ k → ∀ emitted : List Result,
      Relation.ReflTransGen (HEStep dispatch Completed.rawLookup policy)
          (load (Space.ofList atoms) (callC c y n) Atom.undefinedType)
          ⟨Space.ofList atoms, .returning [], [], emitted⟩ →
        ((emitted.map (fun r => r.1.erase) : List Atom) : Multiset Atom) =
          ((Streaming.values (Streaming.advance (translate atoms) k
            (Streaming.enter { state := store atoms } (callC c y n))) : List Atom) : Multiset Atom) := by
  obtain ⟨_, every, N, petta⟩ := bag_every_run dispatch notHost policy program bag
  exact ⟨N, fun k bigger emitted run => by rw [every emitted run, petta k bigger]⟩

/-! ## Controls -/

namespace Controls

open WholeRunWords.Double (noHost)
open CompoundBindings.Controls (call_single build_values)
open IfComputed.Controls (num)

/-- HE's `if` with `coin` (answers `True` and `False`), `coin2` (answers `True` twice),
`(= (half 4) two)`. -/
abbrev coinRows : List Atom :=
  ifProgram ++ [rule (app "coin" []) (.grounded (.bool true)),
    rule (app "coin" []) (.grounded (.bool false)), rule (app "coin2" []) (.grounded (.bool true)),
    rule (app "coin2" []) (.grounded (.bool true)), rule (app "half" [num 4]) (sym "two")]

theorem coin_types_if : StorageTypesRel (Space.ofList coinRows) (.symbol "if") [ifArrow] :=
  .symbolKnown (.hit (.skip (fun _ same => by simp at same) (.skip (fun _ same => by simp at same)
    (.skip (fun _ same => by simp at same) (.skip (fun _ same => by simp at same)
      (.skip (fun _ same => by simp at same) (.skip (fun _ same => by simp at same)
        (.skip (fun _ same => by simp at same) .nil)))))))) (by simp)

theorem constant_row (f : String) (body : Atom) (item : FlatItem body)
    (closed : TypeSubst.typeVars body = []) :
    RegionsWithVariables.ConsFreeHeads (rule (app f []) body) ∧ CallRow (rule (app f []) body) :=
  ⟨rule_consFree fun a inside => (by cases inside), fun lhs rhs same => by
    cases same
    exact ⟨by simp [closed], .item item⟩⟩

theorem coin_rows : CallProgram coinRows := by
  intro row member
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with ((rfl | rfl | rfl) | rfl | rfl | rfl | rfl | rfl)
  · exact ⟨fun lhs rhs same => by simp at same, fun lhs rhs same => by simp at same⟩
  · refine ⟨rule_consFree fun a inside => ?_, fun lhs rhs same => ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at inside
      rcases inside with rfl | rfl | rfl
      · exact .grounded _
      · exact .var _
      · exact .var _
    · cases same
      exact ⟨by decide, .item (.var _)⟩
  · refine ⟨rule_consFree fun a inside => ?_, fun lhs rhs same => ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at inside
      rcases inside with rfl | rfl | rfl
      · exact .grounded _
      · exact .var _
      · exact .var _
    · cases same
      exact ⟨by decide, .item (.var _)⟩
  · exact constant_row "coin" _ (.grounded _) rfl
  · exact constant_row "coin" _ (.grounded _) rfl
  · exact constant_row "coin2" _ (.grounded _) rfl
  · exact constant_row "coin2" _ (.grounded _) rfl
  · refine ⟨rule_consFree fun a inside => ?_, fun lhs rhs same => ?_⟩
    · simp only [List.mem_singleton] at inside
      subst inside
      exact .grounded _
    · cases same
      exact ⟨by decide, .item (.symbol _)⟩

theorem coin_program : IfCallProgram coinRows := ⟨coin_types_if, coin_rows⟩

theorem coin_head (f : String) (untyped : (Space.ofList coinRows).atoms.filter
      (typeRegion (.symbol f)) = [])
    (notInstruction : Minimal.embeddedInstruction (.expression [.symbol f]) = false)
    (notIO : Mettapedia.Languages.MeTTa.PeTTa.Eval.ioHead f = false)
    (notNative : StdLib.known f = false) (notControl : controlHead f = false)
    (notEmpty : f ≠ "Empty") (notError : f ≠ "Error") : NodeHead noHost coinRows f :=
  ⟨.symbol notEmpty notError, untyped, fun impossible => impossible, notInstruction, notIO,
    notNative, notControl⟩

/-- A call without arguments whose region's instances are data atoms settles with them, in row
order. -/
theorem constant_settles {f : String} (head : NodeHead noHost coinRows f)
    (defined : ∃ e ∈ coinRows.filterMap LiveEquations.equationOfRow, e.head = f)
    {bodies : List Atom} (instances : regionInstances coinRows f [] = bodies) (nonempty : bodies ≠ [])
    (each : ∀ b ∈ bodies, DataAtom b ∧ b ≠ Atom.notReducible) :
    SettlesK noHost coinRows (app f []) bodies := by
  have built := SettlesK.call (dispatch := noHost) (atoms := coinRows) (ts := []) (Ls := [])
    (fun _ => bodies.map fun b => [b]) head defined rfl (fun p member => by cases member)
    (fun vals member => by
      simp only [combos, List.mem_singleton] at member
      subst member
      rw [instances]
      exact nonempty)
    (fun vals member => by
      simp only [combos, List.mem_singleton] at member
      subst member
      rw [instances]
      simp)
    (fun vals member p inside => by
      simp only [combos, List.mem_singleton] at member
      subst member
      rw [instances] at inside
      have shaped : ∀ (l : List Atom) (q : Atom × List Atom), q ∈ l.zip (l.map fun b => [b]) →
          q.2 = [q.1] ∧ q.1 ∈ l := by
        intro l
        induction l with
        | nil => intro q member; cases member
        | cons x xs ih =>
            intro q member
            simp only [List.map_cons, List.zip_cons_cons, List.mem_cons] at member
            rcases member with rfl | inner
            · exact ⟨rfl, List.mem_cons_self⟩
            · obtain ⟨same, inXs⟩ := ih q inner
              exact ⟨same, List.mem_cons_of_mem _ inXs⟩
      obtain ⟨same, inBodies⟩ := shaped bodies p inside
      rw [same]
      exact .data (each p.1 inBodies).1 (each p.1 inBodies).2)
  have flat : ∀ l : List Atom, (l.map fun b => [b]).flatten = l := by
    intro l
    induction l with
    | nil => rfl
    | cons x xs ih => simp [ih]
  exact SettlesK.of_eq built (by simp [combos, flat])

theorem coin_settles :
    SettlesK noHost coinRows (app "coin" []) [.grounded (.bool true), .grounded (.bool false)] :=
  constant_settles (coin_head "coin" (by decide +kernel) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)) (by decide +kernel) (by decide +kernel)
    (List.cons_ne_nil _ _) (fun b member => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl <;> exact ⟨.grounded _, fun same => by cases same⟩)

theorem coin2_settles :
    SettlesK noHost coinRows (app "coin2" []) [.grounded (.bool true), .grounded (.bool true)] :=
  constant_settles (coin_head "coin2" (by decide +kernel) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)) (by decide +kernel) (by decide +kernel)
    (List.cons_ne_nil _ _) (fun b member => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl <;> exact ⟨.grounded _, fun same => by cases same⟩)

theorem expression_undeclared (items : List Atom) (notIf : ∀ T,
    Atom.expression [.symbol ":", .symbol "if", ifArrow] ≠ .expression [.symbol ":", .expression items, T]) :
    StorageTypesRel (Space.ofList coinRows) (.expression items) [Atom.undefinedType] := by
  cases items with
  | nil => exact .unit _
  | cons head tail =>
      exact .expressionUndefined (.skip notIf (.skip (fun _ same => by simp at same)
        (.skip (fun _ same => by simp at same) (.skip (fun _ same => by simp at same)
          (.skip (fun _ same => by simp at same) (.skip (fun _ same => by simp at same)
            (.skip (fun _ same => by simp at same) (.skip (fun _ same => by simp at same) .nil))))))))

theorem symbol_undeclared (name : String) (notIf : name ≠ "if") :
    StorageTypesRel (Space.ofList coinRows) (sym name) [Atom.undefinedType] :=
  .symbolUndefined (.skip (fun _ same => by cases same; exact notIf rfl)
    (.skip (fun _ same => by simp at same) (.skip (fun _ same => by simp at same)
      (.skip (fun _ same => by simp at same) (.skip (fun _ same => by simp at same)
        (.skip (fun _ same => by simp at same) (.skip (fun _ same => by simp at same)
          (.skip (fun _ same => by simp at same) .nil))))))))

theorem undeclared_condition (f : String) :
    ∃ T, StorageTypesRel (Space.ofList coinRows) (app f []) [T] ∧
      (∀ bnd : Bindings, TypeMatchRel (sym "Bool") T bnd bnd) ∧
      (∀ bnd out : Bindings, TypeMatchRel (sym "Bool") T bnd out → out = bnd) :=
  ⟨Atom.undefinedType, expression_undeclared _ (fun _ same => by simp at same),
    fun _ => .undefinedRight _ _,
    fun _ _ matched => Mettapedia.Languages.MeTTa.HE.Spec.Type.TypeMatchRel.wildcard_output matched
      (Or.inr (Or.inr (Or.inl rfl)))⟩

theorem half_settles : SettlesK noHost coinRows (app "half" [num 4]) [sym "two"] :=
  call_single (coin_head "half" (by decide +kernel) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)) (by decide +kernel)
    (.cons (.data (.grounded _) (fun same => by cases same)) .nil) rfl (by decide +kernel)
    (.data (.symbol (by decide) (by decide)) (by decide))

theorem pair_head : NodeHead noHost coinRows "pair" :=
  coin_head "pair" (by decide +kernel) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide)

theorem pair_settles :
    SettlesK noHost coinRows (app "pair" [sym "a", sym "b"]) [app "pair" [sym "a", sym "b"]] :=
  build_values pair_head (by decide +kernel)
    (.cons (.data (.symbol (by decide) (by decide)) (by decide))
      (.cons (.data (.symbol (by decide) (by decide)) (by decide)) .nil))

/-- `(if (coin) (half 4) (pair a b))`: one answer of each branch. -/
theorem coin_bag : BagIf noHost coinRows (app "coin" []) (app "half" [num 4])
    (app "pair" [sym "a", sym "b"]) [.grounded (.bool true), .grounded (.bool false)] [sym "two"]
    [app "pair" [sym "a", sym "b"]] where
  conditionSettles := coin_settles
  booleans := fun a member => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact ⟨true, rfl⟩
    · exact ⟨false, rfl⟩
  conditionTyped := undeclared_condition "coin"
  yesSettles := half_settles
  noSettles := pair_settles
  yesCasts := fun a member data => by
    rw [List.mem_singleton] at member
    subst member
    exact undeclared_casts data (symbol_undeclared "two" (by decide)) "t"
  noCasts := fun a member data => by
    rw [List.mem_singleton] at member
    subst member
    cases data
  typedYes := ⟨_, expression_undeclared _ (fun _ same => by simp at same)⟩
  typedNo := ⟨_, expression_undeclared _ (fun _ same => by simp at same)⟩
  regions := fun b _ => by
    unfold IfRegion
    cases b <;> decide +kernel

/-- **A nondeterministic condition, both branches taken**: `(if (coin) (half 4) (pair a b))`
publishes `[two, (pair a b)]` on every complete HE run, a complete run exists, and PeTTa yields the
same list, hence the same bag. -/
theorem coin_pair (policy : Policy) :
    (∃ heAnswers : List Result,
      Relation.ReflTransGen (HEStep noHost Completed.rawLookup policy)
          (load (Space.ofList coinRows)
            (callC (app "coin" []) (app "half" [num 4]) (app "pair" [sym "a", sym "b"]))
            Atom.undefinedType)
          ⟨Space.ofList coinRows, .returning [], [], heAnswers⟩) ∧
      (∀ emitted : List Result,
        Relation.ReflTransGen (HEStep noHost Completed.rawLookup policy)
            (load (Space.ofList coinRows)
              (callC (app "coin" []) (app "half" [num 4]) (app "pair" [sym "a", sym "b"]))
              Atom.undefinedType)
            ⟨Space.ofList coinRows, .returning [], [], emitted⟩ →
          emitted.map (fun r => r.1.erase) = [sym "two", app "pair" [sym "a", sym "b"]]) ∧
      ∃ N : Nat, ∀ k, N ≤ k → Streaming.values (Streaming.advance (translate coinRows) k
        (Streaming.enter { state := store coinRows }
          (callC (app "coin" []) (app "half" [num 4]) (app "pair" [sym "a", sym "b"])))) =
          [sym "two", app "pair" [sym "a", sym "b"]] := by
  have every := bag_every_run noHost (fun impossible => impossible) policy coin_program coin_bag
  have answers : answersOf [.grounded (.bool true), .grounded (.bool false)] [sym "two"]
      [app "pair" [sym "a", sym "b"]] = [sym "two", app "pair" [sym "a", sym "b"]] := by
    decide +kernel
  rw [answers] at every
  exact every

/-- `(if (coin2) yes no)`: the condition answers `True` twice. -/
theorem coin2_bag : BagIf noHost coinRows (app "coin2" []) (sym "yes") (sym "no")
    [.grounded (.bool true), .grounded (.bool true)] [sym "yes"] [sym "no"] where
  conditionSettles := coin2_settles
  booleans := fun a member => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> exact ⟨true, rfl⟩
  conditionTyped := undeclared_condition "coin2"
  yesSettles := .data (.symbol (by decide) (by decide)) (by decide)
  noSettles := .data (.symbol (by decide) (by decide)) (by decide)
  yesCasts := fun a member data => by
    rw [List.mem_singleton] at member
    subst member
    exact undeclared_casts data (symbol_undeclared "yes" (by decide)) "t"
  noCasts := fun a member data => by
    rw [List.mem_singleton] at member
    subst member
    exact undeclared_casts data (symbol_undeclared "no" (by decide)) "t"
  typedYes := ⟨_, symbol_undeclared "yes" (by decide)⟩
  typedNo := ⟨_, symbol_undeclared "no" (by decide)⟩
  regions := fun b member => by
    unfold IfRegion
    cases b
    · simp at member
    · decide +kernel

/-- **Multiplicity is an observation**: `(if (coin2) yes no)` publishes `yes` twice on every complete
HE run, as PeTTa does; the bags agree with multiplicity two, so a set reading would lose a copy. -/
theorem coin_twice (policy : Policy) :
    (∀ emitted : List Result,
        Relation.ReflTransGen (HEStep noHost Completed.rawLookup policy)
            (load (Space.ofList coinRows) (callC (app "coin2" []) (sym "yes") (sym "no"))
              Atom.undefinedType)
            ⟨Space.ofList coinRows, .returning [], [], emitted⟩ →
          emitted.map (fun r => r.1.erase) = [sym "yes", sym "yes"]) ∧
      ∃ N : Nat, ∀ k, N ≤ k → Streaming.values (Streaming.advance (translate coinRows) k
        (Streaming.enter { state := store coinRows }
          (callC (app "coin2" []) (sym "yes") (sym "no")))) = [sym "yes", sym "yes"] := by
  have every := bag_every_run noHost (fun impossible => impossible) policy coin_program coin2_bag
  have answers : answersOf [.grounded (.bool true), .grounded (.bool true)] [sym "yes"]
      [sym "no"] = [sym "yes", sym "yes"] := by
    decide +kernel
  rw [answers] at every
  exact ⟨every.2.1, every.2.2⟩

end Controls

#print axioms condition_packets
#print axioms bag_calls
#print axioms bag_source
#print axioms branches_path
#print axioms bag_calls_path
#print axioms bag_function_segment
#print axioms bag_run
#print axioms petta_if_bag
#print axioms bag_every_run
#print axioms bag_every_run_multiset
#print axioms Controls.coin_pair
#print axioms Controls.coin_twice

end IfBags

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.TriangleFootprints
