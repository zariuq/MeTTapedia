import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.TriangleFootprints.GroundedDifferences
import Mettapedia.Languages.MeTTa.PeTTa.DeclaredTypesAtACall

/-!
# Three named differences of HE and PeTTa, on the models and on the hosts

Each difference is a small program family. It is measured on the hosts (HE: hyperon-experimental
0.2.10 with three later fixes, one call per file; PeTTa: CeTTa's PeTTa lane) and evaluated by the
kernel on the tree's two models: HE's executable evaluator (`HE.evalAtom`, with HE's `+`) and PeTTa's
streaming machine. Where a model answers as its host, its side of the difference is a theorem on
the model with existence; where it does not, the model's gap is a theorem about the model, stated
beside the measured row. Every sentence here about HE or a PeTTa host is a measured row; every
theorem is about a model.

## (a) Two declared rows

`(: g2 (-> Number Number))`, `(: g2 (-> $t $t))`, `(= (g2 $x) (+ $x 1))`: HE answers `(g2 1)` with
`[2]`; the PeTTa lane with `2 2`. `(: q2 (-> Atom Atom))`, `(: q2 (-> Number Number))`,
`(= (q2 $x) $x)`: HE answers `(q2 (+ 1 2))` with `[(+ 1 2)]`; the PeTTa lane with `(+ 1 2) 3`.

On the models (`two_rows_models`) each answers as the other dialect's host. HE's evaluator runs the
call once for every applicable row (`[2, 2]`, `[(+ 1 2), 3]`), where HE answers once. PeTTa's
machine runs the call once, holding the argument as written for the whole call because one row has
`Atom` there (`DeclaredTypesAtACall.the_model_holds_the_argument_for_every_row`), and answers `[2]`
and `[(+ 1 2)]`, where the PeTTa hosts deliver by each row (`DeclaredTypesAtACall`:
`rows_can_repeat_an_answer`, `each_row_delivers_by_its_own_demand`). Both are gaps of the models.
The PeTTa model's delivery is each row's exactly where a name's rows agree on their `Atom` positions
(`DeclaredTypesAtACall.the_model_delivers_as_each_row_where_rows_agree`), which `q2`'s rows do not
(`DeclaredTypesAtACall.rows_that_disagree_are_delivered_otherwise`); `g2`'s rows agree, and the gap
there is the one run against one run per row.

## (b) Partial application, and the equation that removes an answer

`(= (co7-base 1 2) old)`, `(= (co7-wrap $x) (co7-base $x))`: HE answers `(co7-wrap 1)` with
`[(co7-base 1)]` and `(co7-wrap 1 2)` with `[(co7-wrap 1 2)]`; the PeTTa lane answers
`(partial co7-base (1))` and `old`. With `(= (co7-wrap 1 2) added)` added, HE answers `[added]`, and
the PeTTa lane answers `added` only: on PeTTa the new equation removes the answer `old`.

* HE's side, on HE's contextual machine (`partial_application_he`): every complete run of
  `(co7-wrap 1 2)` publishes the call itself, and with the new equation `added`; each run exists.
  HE's evaluator answers all three calls as HE does (`partial_application_models`); the
  contextual machine's every-run statement for `(co7-wrap 1)`, whose body binds `$x` and calls a
  name with no row of its arity, is not built here.
* PeTTa's machine answers `(co7-wrap 1)` with its partial value and, with the new equation,
  `(co7-wrap 1 2)` with `added`, as the host does (`partial_application_petta`, every fuel from some
  fuel on). On `(co7-wrap 1 2)` without it, the model stops at the `overApplication` fault with no
  value, where the PeTTa lane answers `old`: a gap of the model (its `PeTTa.Eval.application`
  faults a call longer than every arity instead of applying the shorter call's partial value).

## (c) An `Atom` parameter used twice, with a choice as argument

`(= (two) a)`, `(= (two) b)`, `(: pairA (-> Atom %Undefined%))`, `(= (pairA $x) (pair $x $x))`: HE
answers `(pairA (two))` with the four pairs `(pair a a)`, `(pair a b)`, `(pair b a)`, `(pair b b)`;
the PeTTa lane with `(pair (two) (two))`. With the parameter `%Undefined%` (`pair2`) both answer the
two pairs `(pair a a)` and `(pair b b)` (HE in the order `b`, `a`).

On the models (`atom_parameter_models`) each answers as its host: HE's evaluator the four pairs in
HE's order, PeTTa's machine `(pair (two) (two))` from some fuel on; with the value parameter both the
two pairs (HE's evaluator in another order than HE's: the bag is HE's).
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.TriangleFootprints

namespace ThreeDifferences

open Mettapedia.Languages.MeTTa.OSLFCore (Atom GroundedValue)
open Mettapedia.Languages.MeTTa.HE (Space Bindings evalAtom isErrorAtom)
open Mettapedia.Languages.MeTTa.HE.Spec.Eval
open Mettapedia.Languages.MeTTa.HE.Spec.Eval.Completed (Policy Result CastLookup Frame)
open Mettapedia.Languages.MeTTa.HE.RecursiveMachine.Contextual (load)
open Mettapedia.Languages.MeTTa.PeTTa
open ServiceFootprints EntryToQuery AnswerBags EveryRun
open AnswerBags.Controls (sym app rule rule_consFree)
open WholeRunWords.Double (noHost)

/-! ## The two models -/

/-- An integer. -/
abbrev num (n : Int) : Atom := .grounded (.int n)

/-- A declaration row `(: name type)`. -/
abbrev decl (name : String) (type : Atom) : Atom := .expression [.symbol ":", .symbol name, type]

/-- A function type. -/
abbrev arrow (types : List Atom) : Atom := .expression (.symbol "->" :: types)

/-- **HE's executable evaluator** on a program, from `%Undefined%` demand, with HE's `+`. -/
def heEval (rows : List Atom) (t : Atom) (fuel : Nat) : List Atom :=
  (evalAtom (Space.ofList rows) HEOnTheStep.NamedDifferences.plus t Atom.undefinedType Bindings.empty
    fuel).map Prod.fst

/-- **PeTTa's streaming machine** on a program, from the entry of `t`, with `fuel`. -/
def pettaRun (rows : List Atom) (t : Atom) (fuel : Nat) : Streaming.State :=
  Streaming.advance (translate rows) fuel (Streaming.enter { state := store rows } t)

/-- **PeTTa's run finishes with the values `L`**: from some fuel on, its agenda is empty and its
values are `L`. The machine is deterministic, so this is its every run. -/
def PeTTaFinishes (rows : List Atom) (t : Atom) (L : List Atom) : Prop :=
  ∃ N, ∀ n, N ≤ n → (pettaRun rows t n).agenda = [] ∧ Streaming.values (pettaRun rows t n) = L

theorem petta_finishes_of {rows : List Atom} {t : Atom} {L : List Atom} (N : Nat)
    (done : (pettaRun rows t N).agenda = []) (values : Streaming.values (pettaRun rows t N) = L) :
    PeTTaFinishes rows t L := by
  refine ⟨N, fun n bigger => ?_⟩
  have stable := advance_stable done n bigger
  simp only [pettaRun] at done values ⊢
  rw [stable]
  exact ⟨done, values⟩

/-- The fault a stopped PeTTa run holds: its one remaining job is a fault at the root. -/
def stoppedAt : List Streaming.Job → Option Effects.Fault
  | [.execute ⟨.fault reason, []⟩] => some reason
  | _ => none

/-! ## (a) Two declared rows -/

/-- `(: g2 (-> Number Number))`, `(: g2 (-> $t $t))`, `(= (g2 $x) (+ $x 1))`. -/
def g2Rows : List Atom :=
  [decl "g2" (arrow [sym "Number", sym "Number"]), decl "g2" (arrow [.var "t", .var "t"]),
   rule (app "g2" [.var "x"]) (app "+" [.var "x", num 1])]

/-- `(: q2 (-> Atom Atom))`, `(: q2 (-> Number Number))`, `(= (q2 $x) $x)`. -/
def q2Rows : List Atom :=
  [decl "q2" (arrow [sym "Atom", sym "Atom"]), decl "q2" (arrow [sym "Number", sym "Number"]),
   rule (app "q2" [.var "x"]) (.var "x")]

/-- `(+ 1 2)`. -/
abbrev onePlusTwo : Atom := app "+" [num 1, num 2]

/-- **Two declared rows, on the models: each model answers as the other dialect's host.** HE's
evaluator answers `(g2 1)` with `[2, 2]` and `(q2 (+ 1 2))` with `[(+ 1 2), 3]`, one answer for each
row; HE answers `[2]` and `[(+ 1 2)]` (measured). PeTTa's machine finishes with `[2]` and
`[(+ 1 2)]`, running the call once; the PeTTa lane answers `2 2` and `(+ 1 2) 3` (measured). The
PeTTa model holds `q2`'s argument because one of its rows has `Atom` there; it would deliver as each
row only where the rows agree on their `Atom` positions. -/
theorem two_rows_models :
    heEval g2Rows (app "g2" [num 1]) 40 = [num 2, num 2] ∧
      heEval q2Rows (app "q2" [onePlusTwo]) 40 = [onePlusTwo, num 3] ∧
      PeTTaFinishes g2Rows (app "g2" [num 1]) [num 2] ∧
      PeTTaFinishes q2Rows (app "q2" [onePlusTwo]) [onePlusTwo] ∧
      Eval.argumentIsRaw (translate q2Rows) "q2" 0 = true ∧
      Eval.argumentIsRaw DeclaredTypesAtACall.twoRows "h" 0 = true := by
  refine ⟨by decide +kernel, by decide +kernel, petta_finishes_of 80 (by decide +kernel)
    (by decide +kernel), petta_finishes_of 80 (by decide +kernel) (by decide +kernel),
    by decide +kernel, DeclaredTypesAtACall.the_model_holds_the_argument_for_every_row⟩

/-! ## (b) Partial application, and the equation that removes an answer -/

/-- `(= (co7-base 1 2) old)`, `(= (co7-wrap $x) (co7-base $x))`. -/
def co7Rows : List Atom :=
  [rule (app "co7-base" [num 1, num 2]) (sym "old"),
   rule (app "co7-wrap" [.var "x"]) (app "co7-base" [.var "x"])]

/-- The program with `(= (co7-wrap 1 2) added)` added. -/
def co7AddedRows : List Atom := co7Rows ++ [rule (app "co7-wrap" [num 1, num 2]) (sym "added")]

/-- PeTTa's partial value `(partial co7-base (1))`, as the PeTTa model writes it. -/
abbrev partialBase : Atom :=
  .expression [.grounded (.custom "PeTTa.Partial" ""), .symbol "co7-base", .expression [num 1]]

theorem co7_program : ∀ row ∈ co7Rows, RegionsWithVariables.ConsFreeHeads row := by
  intro row member
  simp only [co7Rows, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact rule_consFree fun a inside => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at inside
      rcases inside with rfl | rfl <;> exact .grounded _
  · exact rule_consFree fun a inside => by
      rw [List.mem_singleton] at inside
      subst inside
      exact .var _

theorem co7Added_program : ∀ row ∈ co7AddedRows, RegionsWithVariables.ConsFreeHeads row := by
  intro row member
  rcases List.mem_append.mp member with old | added
  · exact co7_program row old
  · rw [List.mem_singleton] at added
    subst added
    exact rule_consFree fun a inside => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at inside
      rcases inside with rfl | rfl <;> exact .grounded _

theorem ints_data (values : List Int) : ∀ a ∈ values.map num, DataAtom a := by
  intro a member
  obtain ⟨n, _, rfl⟩ := List.mem_map.mp member
  exact .grounded _

theorem ordinary_wrap (atoms : List Atom) (args : List Int)
    (untyped : (Space.ofList atoms).atoms.filter (typeRegion (.symbol "co7-wrap")) = []) :
    Ordinary noHost atoms "co7-wrap" (args.map num) :=
  ⟨.symbol (by decide) (by decide), ints_data args, untyped, fun impossible => impossible,
    by cases args <;> rfl, by decide, by decide +kernel, by cases args <;> rfl, by decide, by decide⟩

/-- **HE's side of the difference, on HE's contextual machine** (any policy, HE's raw lookup):
`(co7-wrap 1 2)` publishes itself, no row having its arity; with `(= (co7-wrap 1 2) added)` it
publishes `added`. For each a complete run exists, and every complete run publishes that list. HE
answers the same (measured); the PeTTa lane answers `old`, and `added` only. The third call,
`(co7-wrap 1)`, whose body `(co7-base 1)` binds `$x` and has no row of its arity, is outside the
contextual machine's classes here; HE's evaluator answers it as HE does
(`partial_application_models`). -/
theorem partial_application_he (policy : Policy) :
    ((∃ heAnswers : List Result,
        Relation.ReflTransGen (HEStep noHost Completed.rawLookup policy)
          (load (Space.ofList co7Rows) (app "co7-wrap" [num 1, num 2]) Atom.undefinedType)
          ⟨Space.ofList co7Rows, .returning [], [], heAnswers⟩) ∧
      ∀ emitted : List Result,
        Relation.ReflTransGen (HEStep noHost Completed.rawLookup policy)
          (load (Space.ofList co7Rows) (app "co7-wrap" [num 1, num 2]) Atom.undefinedType)
          ⟨Space.ofList co7Rows, .returning [], [], emitted⟩ →
        emitted.map (fun r => r.1.erase) = [app "co7-wrap" [num 1, num 2]]) ∧
    ((∃ heAnswers : List Result,
        Relation.ReflTransGen (HEStep noHost Completed.rawLookup policy)
          (load (Space.ofList co7AddedRows) (app "co7-wrap" [num 1, num 2]) Atom.undefinedType)
          ⟨Space.ofList co7AddedRows, .returning [], [], heAnswers⟩) ∧
      ∀ emitted : List Result,
        Relation.ReflTransGen (HEStep noHost Completed.rawLookup policy)
          (load (Space.ofList co7AddedRows) (app "co7-wrap" [num 1, num 2]) Atom.undefinedType)
          ⟨Space.ofList co7AddedRows, .returning [], [], emitted⟩ →
        emitted.map (fun r => r.1.erase) = [sym "added"]) := by
  have wrapTwo : Ordinary noHost co7Rows "co7-wrap" [num 1, num 2] :=
    ordinary_wrap co7Rows [1, 2] (by decide +kernel)
  have wrapAdded : Ordinary noHost co7AddedRows "co7-wrap" [num 1, num 2] :=
    ordinary_wrap co7AddedRows [1, 2] (by decide +kernel)
  have twoEmpty : regionBodies co7Rows "co7-wrap" [num 1, num 2] = [] := by decide +kernel
  have addedBodies : regionBodies co7AddedRows "co7-wrap" [num 1, num 2] = [sym "added"] := by
    decide +kernel
  have addedData : DataAtom (sym "added") := .symbol (by decide) (by decide)
  have addedNotRefused : sym "added" ≠ Atom.notReducible := by decide
  refine ⟨⟨?_, fun emitted run => ?_⟩, ⟨?_, fun emitted run => ?_⟩⟩
  · obtain ⟨R, _, path, _⟩ := he_complete (HERuns.he_absent (dispatch := noHost)
      (lookup := Completed.rawLookup) (policy := policy) raw_answers co7_program wrapTwo twoEmpty)
    exact ⟨R, path⟩
  · exact empty_region_determined raw_contract co7_program wrapTwo twoEmpty [] [] _ _
      (complete_source run)
  · have bodies : List.Forall₂ (fun b L =>
        HEEvaluates noHost Completed.rawLookup policy co7AddedRows b L ∧ BodyFacts b ∧
          ∀ a ∈ L, Answerable a) (regionBodies co7AddedRows "co7-wrap" [num 1, num 2])
        [[sym "added"]] := by
      rw [addedBodies]
      exact .cons ⟨HERuns.he_data raw_answers co7AddedRows addedData,
        settles_facts (Settles.data (dispatch := noHost) (atoms := co7AddedRows) addedData
          addedNotRefused),
        fun a member => by
          rw [List.mem_singleton] at member
          subst member
          exact answerable_of_data addedData⟩ .nil
    obtain ⟨R, _, path, _⟩ := he_complete (HERuns.he_call raw_answers co7Added_program wrapAdded
      (by rw [addedBodies]; simp) bodies)
    exact ⟨R, path⟩
  · have settles : Settles noHost co7AddedRows (app "co7-wrap" [num 1, num 2]) :=
      .call wrapAdded (by rw [addedBodies]; simp) (by
        rw [addedBodies]
        intro b member
        rw [List.mem_singleton] at member
        subst member
        exact .data addedData addedNotRefused)
    obtain ⟨L, _, determined⟩ := settles_determined (policy := policy) co7Added_program settles
    have bodies : List.Forall₂ (fun b L =>
        HEEvaluates noHost Completed.rawLookup policy co7AddedRows b L ∧ BodyFacts b ∧
          ∀ a ∈ L, Answerable a) (regionBodies co7AddedRows "co7-wrap" [num 1, num 2])
        [[sym "added"]] := by
      rw [addedBodies]
      exact .cons ⟨HERuns.he_data raw_answers co7AddedRows addedData,
        settles_facts (Settles.data (dispatch := noHost) (atoms := co7AddedRows) addedData
          addedNotRefused),
        fun a member => by
          rw [List.mem_singleton] at member
          subst member
          exact answerable_of_data addedData⟩ .nil
    obtain ⟨R, erasedR, path, _⟩ := he_complete (HERuns.he_call raw_answers co7Added_program
      wrapAdded (by rw [addedBodies]; simp) bodies)
    rw [determined _ _ _ _ (complete_source run), ← determined _ _ _ _ (complete_source path)]
    exact erasedR

/-- **PeTTa's side, on the PeTTa model.** `(co7-wrap 1)` finishes with the partial value
`(partial co7-base (1))`, and with `(= (co7-wrap 1 2) added)` `(co7-wrap 1 2)` finishes with
`added` only, as on the PeTTa lane (measured). On `(co7-wrap 1 2)` without that equation the model
stops at the `overApplication` fault with no value, where the PeTTa lane answers `old` (measured):
a gap of the model. -/
theorem partial_application_petta :
    PeTTaFinishes co7Rows (app "co7-wrap" [num 1]) [partialBase] ∧
      PeTTaFinishes co7AddedRows (app "co7-wrap" [num 1, num 2]) [sym "added"] ∧
      stoppedAt (pettaRun co7Rows (app "co7-wrap" [num 1, num 2]) 80).agenda =
        some (.overApplication "co7-wrap" [1] 2) ∧
      Streaming.values (pettaRun co7Rows (app "co7-wrap" [num 1, num 2]) 80) = [] :=
  ⟨petta_finishes_of 80 (by decide +kernel) (by decide +kernel),
    petta_finishes_of 80 (by decide +kernel) (by decide +kernel), by decide +kernel,
    by decide +kernel⟩

/-- **HE's evaluator on the three calls** answers as HE: `[(co7-base 1)]`, `[(co7-wrap 1 2)]`,
`[added]`. -/
theorem partial_application_models :
    heEval co7Rows (app "co7-wrap" [num 1]) 40 = [app "co7-base" [num 1]] ∧
      heEval co7Rows (app "co7-wrap" [num 1, num 2]) 40 = [app "co7-wrap" [num 1, num 2]] ∧
      heEval co7AddedRows (app "co7-wrap" [num 1, num 2]) 40 = [sym "added"] := by
  refine ⟨?_, ?_, ?_⟩ <;> decide +kernel

/-! ## (c) An `Atom` parameter used twice, with a choice as argument -/

/-- `(= (two) a)`, `(= (two) b)`, `(: pairA (-> Atom %Undefined%))`, `(= (pairA $x) (pair $x $x))`. -/
def dupAtomRows : List Atom :=
  [rule (app "two" []) (sym "a"), rule (app "two" []) (sym "b"),
   decl "pairA" (arrow [sym "Atom", sym "%Undefined%"]),
   rule (app "pairA" [.var "x"]) (app "pair" [.var "x", .var "x"])]

/-- The same with the parameter `%Undefined%`: `(: pair2 (-> %Undefined% %Undefined%))`. -/
def dupValueRows : List Atom :=
  [rule (app "two" []) (sym "a"), rule (app "two" []) (sym "b"),
   decl "pair2" (arrow [sym "%Undefined%", sym "%Undefined%"]),
   rule (app "pair2" [.var "x"]) (app "pair" [.var "x", .var "x"])]

/-- `(pair x y)`. -/
abbrev pairOf (x y : String) : Atom := app "pair" [sym x, sym y]

/-- **An `Atom` parameter used twice, on the models: each answers as its host.** HE's evaluator
answers `(pairA (two))` with the four pairs in HE's order; PeTTa's machine finishes with
`(pair (two) (two))`, as the PeTTa lane does. With the value parameter HE's evaluator answers the two
pairs `(pair a a)`, `(pair b b)` (HE: the same bag, in the order `b`, `a`), and PeTTa's machine
finishes with them in the PeTTa lane's order. -/
theorem atom_parameter_models :
    heEval dupAtomRows (app "pairA" [app "two" []]) 40 =
        [pairOf "a" "a", pairOf "a" "b", pairOf "b" "a", pairOf "b" "b"] ∧
      PeTTaFinishes dupAtomRows (app "pairA" [app "two" []]) [app "pair" [app "two" [], app "two" []]] ∧
      heEval dupValueRows (app "pair2" [app "two" []]) 40 = [pairOf "a" "a", pairOf "b" "b"] ∧
      ((heEval dupValueRows (app "pair2" [app "two" []]) 40 : List Atom) : Multiset Atom) =
        (([pairOf "b" "b", pairOf "a" "a"] : List Atom) : Multiset Atom) ∧
      PeTTaFinishes dupValueRows (app "pair2" [app "two" []]) [pairOf "a" "a", pairOf "b" "b"] := by
  have values : heEval dupValueRows (app "pair2" [app "two" []]) 40 =
      [pairOf "a" "a", pairOf "b" "b"] := by
    decide +kernel
  refine ⟨by decide +kernel, petta_finishes_of 80 (by decide +kernel) (by decide +kernel), values,
    ?_, petta_finishes_of 80 (by decide +kernel) (by decide +kernel)⟩
  rw [values]
  exact Multiset.coe_eq_coe.mpr (List.Perm.swap _ _ [])

#print axioms petta_finishes_of
#print axioms two_rows_models
#print axioms partial_application_he
#print axioms partial_application_petta
#print axioms partial_application_models
#print axioms atom_parameter_models

end ThreeDifferences

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.TriangleFootprints
