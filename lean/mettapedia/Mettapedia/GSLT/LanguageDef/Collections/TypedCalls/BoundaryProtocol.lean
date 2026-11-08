import Mettapedia.Machines.TypedBoundary
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.Protocol
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEReturns

/-!
# Typed-call boundary instances

PeTTa's complete row protocol threads its actual guard stores through entry,
body and result guards. HE's return boundary evaluates each raw reply at the
declared range, then selects successes over errors for the whole batch.
`he_typed_call_boundary` connects this factorization to the HE interpreter
under the existing typed-call theorem's explicit applicability hypotheses.

The common observation is a finite answer multiset. HE's ordered list is
converted only in this observation theorem; the interpreter and its first
success choices are not replaced by unordered execution.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.BoundaryProtocol

open Mettapedia.Machines.TypedBoundary
open Mettapedia.Languages.MeTTa.OSLFCore (Atom GroundedValue)

abbrev PettaFrame := List Atom × List (Eqn CallVar)

/-- Arguments have already been delivered according to the row's demand.
Every successful argument-guard store remains a distinct continuation. -/
noncomputable def pettaRow (decls : Decls) (kind : Atom → String)
    (params : List (Ty String)) (range : Ty String) :
    Boundary (List Atom) PettaFrame Atom Atom where
  early := fun _ => 0
  enter := fun args => (guards decls kind 0 params args []).map fun store => (args, store)
  leave := fun frame answer => resultGuard decls kind params.length range frame.2 answer
  select := id

theorem petta_row_run (decls : Decls) (kind : Atom → String)
    (params : List (Ty String)) (range : Ty String)
    (body : List Atom → Multiset Atom) (args : List Atom) :
    (pettaRow decls kind params range).run (fun frame => body frame.1) args =
      chainCall decls kind body (arrow params range) args := by
  simp [Boundary.run, pettaRow, chainCall, arrowSplit_arrow, Multiset.bind_map]

/-- A declaration alternative retains its own shared store and return type. -/
structure PettaCallFrame where
  arguments : List Atom
  store : List (Eqn CallVar)
  parameterCount : Nat
  range : Ty String

noncomputable def pettaRows (decls : Decls) (kind : Atom → String)
    (rows : List (Ty String)) : Boundary (List Atom) PettaCallFrame Atom Atom where
  early := fun _ => 0
  enter := fun args => ((dedupAlpha rows : List (Ty String)) : Multiset _).bind fun row =>
    match arrowSplit row with
    | none => 0
    | some (params, range) =>
        (guards decls kind 0 params args []).map fun store =>
          ⟨args, store, params.length, range⟩
  leave := fun frame answer =>
    resultGuard decls kind frame.parameterCount frame.range frame.store answer
  select := id

/-- All declaration alternatives factor through the same boundary algebra.
Alpha-deduplication belongs to entry; distinct rows keep every continuation. -/
theorem petta_rows_run (decls : Decls) (kind : Atom → String)
    (rows : List (Ty String)) (body : List Atom → Multiset Atom) (args : List Atom) :
    (pettaRows decls kind rows).run (fun frame => body frame.arguments) args =
      typedCall decls kind body rows args := by
  simp only [Boundary.run, pettaRows, id_eq, Multiset.zero_add, Multiset.bind_assoc, typedCall]
  apply Multiset.bind_congr
  intro row _
  unfold chainCall
  cases h : arrowSplit row with
  | none => simp
  | some pair =>
      rcases pair with ⟨params, range⟩
      simp [Multiset.bind_map]

theorem petta_rows_repeat (decls : Decls) (kind : Atom → String)
    (rows : List (Ty String)) (row : Ty String)
    (repeated : ∃ old ∈ rows, AlphaEq old row)
    (body : List Atom → Multiset Atom) (args : List Atom) :
    (pettaRows decls kind (rows ++ [row])).run (fun frame => body frame.arguments) args =
      (pettaRows decls kind rows).run (fun frame => body frame.arguments) args := by
  rw [petta_rows_run, petta_rows_run]
  exact typedCall_repeat decls kind body rows row repeated args

/-- Boundary specialization derives the existing multiplicity factors rather
than replacing successful guards by Boolean tests. -/
theorem petta_closed_factors (decls : Decls) (kind : Atom → String)
    (params : List (Ty Empty)) (range : Ty Empty)
    (body : List Atom → Multiset Atom) (args : List Atom) :
    (pettaRow decls kind (params.map Ty.lift) range.lift).run
        (fun frame => body frame.1) args =
      argCount decls kind params args • (body args).bind fun answer =>
        if ResultGuarded range.lift then
          guardCount (info decls answer) range (kind answer) • {answer}
        else {answer} := by
  rw [petta_row_run, chainCall_closed]

/-- Skipping both boundary checks is justified by exact one-continuation
facts, not by the existence of some typing derivation. -/
theorem petta_closed_elision (decls : Decls) (kind : Atom → String)
    (params : List (Ty Empty)) (range : Ty Empty)
    (body : List Atom → Multiset Atom) (args : List Atom)
    (entryOnce : argCount decls kind params args = 1)
    (returnOnce : ∀ answer ∈ body args, ResultGuarded range.lift →
      guardCount (info decls answer) range (kind answer) = 1) :
    (pettaRow decls kind (params.map Ty.lift) range.lift).run
      (fun frame => body frame.1) args = body args := by
  rw [petta_closed_factors, entryOnce, one_nsmul]
  have each : ∀ answer ∈ body args,
      (if ResultGuarded range.lift then
        guardCount (info decls answer) range (kind answer) • {answer}
      else {answer}) = ({answer} : Multiset Atom) := by
    intro answer member
    split_ifs with guarded
    · rw [returnOnce answer member guarded, one_nsmul]
    · rfl
  calc
    _ = (body args).bind (fun answer => ({answer} : Multiset Atom)) :=
      Multiset.bind_congr each
    _ = body args := by
      rw [Multiset.bind_singleton]
      exact Multiset.map_id' (body args)

open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.HE.CompletedDelivery

/-- The bag observation of HE's genuine complete-batch selection. -/
theorem he_selection (answers : ResultSet) :
    preferSuccess (fun answer : Atom × Bindings => !isErrorAtom answer.1)
      (answers : Multiset (Atom × Bindings)) = (HEReturns.keep answers : Multiset _) := by
  rw [preferSuccess_list]
  unfold HEReturns.keep
  cases (answers.filter fun answer => !isErrorAtom answer.1).isEmpty <;> simp

/-- Return processing on actual HE reply records. The input is the raw
equation/native reply batch, before ordinary return processing and selection. -/
def heReturns (space : Space) (dispatch_ : GroundedDispatch) (original range : Atom)
    (fuel : Nat) (live : List Atom) :
    Boundary ResultSet (Atom × Bindings) Atom (Atom × Bindings) where
  early := fun _ => 0
  enter := fun replies => replies
  leave := fun reply value =>
    ordinaryCallReturn original value reply.2 fun value bindings =>
      evalAtom space dispatch_ value (callReturnType range) bindings fuel live
  select := preferSuccess fun reply => !isErrorAtom reply.1

def rawReply (reply : Atom × Bindings) : Multiset Atom := {reply.1}

theorem he_return_run (space : Space) (dispatch_ : GroundedDispatch) (original range : Atom)
    (fuel : Nat) (live : List Atom) (replies : ResultSet) :
    (heReturns space dispatch_ original range fuel live).run rawReply replies =
      (HEReturns.keep (replies.flatMap fun reply =>
        ordinaryCallReturn original reply.1 reply.2 fun value bindings =>
          evalAtom space dispatch_ value (callReturnType range) bindings fuel live) : Multiset _) := by
  simp only [Boundary.run, heReturns, rawReply, Multiset.zero_add, Multiset.singleton_bind]
  rw [Multiset.coe_bind, he_selection]

/-- The boundary is connected to the interpreter, not defined to be its
whole call. Entry applicability remains exactly that of typed_call_once. -/
theorem he_typed_call_boundary {space : Space} {dispatch_ : GroundedDispatch} {head : String}
    {params args : List Atom} {range expected : Atom}
    (declared : getAtomTypes space (.symbol head) = [arrowType params range])
    (ground : atomVariables (arrowType params range) = [])
    (notEmpty : head ≠ "Empty") (notError : head ≠ "Error")
    (notExecutable : dispatch_.isExecutable (.symbol head) = false)
    (notInstruction : minimalInstruction (.expression (.symbol head :: args)) = false)
    (checked : List.Forall₂ (CompletedDelivery.ArgumentChecked space) params args)
    (returns : CompletedDelivery.accepts expected range = true)
    (notAtom : expected ≠ Atom.atomType) (notExpression : expected ≠ Atom.expressionType)
    (bindings : Bindings) {fuel : Nat} (enough : matchFuel (arrowType params range) ≤ fuel)
    (arguments : ∀ live, interpretArgs space dispatch_ args params bindings (fuel + 1) live =
      [(argumentPacket args, bindings)])
    {live : List Atom} {replies : ResultSet}
    (queried : rawQueryResults space (.expression (.symbol head :: args)) (callReturnType range)
      bindings (fuel + 1) live = replies)
    (nonempty : replies ≠ [])
    (plain : ∀ reply ∈ replies, ∀ body, reply.1 ≠ .expression [.symbol "function", body]) :
    (heReturns space dispatch_ (.expression (.symbol head :: args)) range (fuel + 1) live).run
        rawReply replies =
      (evalAtom space dispatch_ (.expression (.symbol head :: args)) expected bindings
        (fuel + 4) live : Multiset _) := by
  rw [he_return_run,
    HEReturns.typed_call_once declared ground notEmpty notError notExecutable notInstruction
      checked returns notAtom notExpression bindings enough arguments queried nonempty plain]

namespace Controls

theorem petta_number_once :
    (pettaRow TypedCalls.Controls.decls TypedCalls.Controls.probeKind
      [.sym "Number"] (.sym "Number")).run
      (fun _ => {TypedCalls.Controls.num 2}) [TypedCalls.Controls.num 1] =
        {TypedCalls.Controls.num 2} := by
  exact (petta_row_run TypedCalls.Controls.decls TypedCalls.Controls.probeKind
    [.sym "Number"] (.sym "Number") (fun _ => {TypedCalls.Controls.num 2})
    [TypedCalls.Controls.num 1]).trans TypedCalls.Controls.number_row_once

/-- Distinct declaration alternatives remain separate even when their answer
payloads are equal. -/
theorem petta_distinct_rows_keep_two :
    (pettaRows TypedCalls.Controls.decls TypedCalls.Controls.probeKind
      [TypedCalls.Controls.numberRow, TypedCalls.Controls.identityRow]).run
      (fun _ => {TypedCalls.Controls.num 2}) [TypedCalls.Controls.num 1] =
        {TypedCalls.Controls.num 2, TypedCalls.Controls.num 2} := by
  exact (petta_rows_run TypedCalls.Controls.decls TypedCalls.Controls.probeKind
    [TypedCalls.Controls.numberRow, TypedCalls.Controls.identityRow]
    (fun _ => {TypedCalls.Controls.num 2}) [TypedCalls.Controls.num 1]).trans
      TypedCalls.Controls.distinct_rows_two_answers

/-- Having another row is not permission to forget the correlation of a
shared type variable between an argument and its result. -/
theorem petta_shared_range_rejects :
    (pettaRows TypedCalls.Controls.decls TypedCalls.Controls.probeKind
      [TypedCalls.Controls.identityRow]).run
      (fun _ => {TypedCalls.Controls.str "a"}) [TypedCalls.Controls.num 1] = 0 := by
  calc
    _ = typedCall TypedCalls.Controls.decls TypedCalls.Controls.probeKind
        (fun _ => {TypedCalls.Controls.str "a"}) [TypedCalls.Controls.identityRow]
        [TypedCalls.Controls.num 1] :=
      petta_rows_run _ _ _ (fun _ => {TypedCalls.Controls.str "a"}) _
    _ = 0 := by
      rw [typedCall_single]
      exact TypedCalls.Controls.shared_variable_checks_result

def failed : Atom := .expression [.symbol "Error", .symbol "bad", .symbol "BadType"]
def value : Atom := .grounded (.int 3)

/-- HE keeps two identical successful occurrences and removes the failed
alternative; moving selection before combining alternatives changes this. -/
theorem he_batch_keeps_occurrences :
    HEReturns.keep [(failed, Bindings.empty), (value, Bindings.empty), (value, Bindings.empty)] =
      [(value, Bindings.empty), (value, Bindings.empty)] := by
  rfl

theorem he_selection_not_local :
    HEReturns.keep [(failed, Bindings.empty), (value, Bindings.empty)] ≠
      HEReturns.keep [(failed, Bindings.empty)] ++ HEReturns.keep [(value, Bindings.empty)] := by
  decide

end Controls

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.BoundaryProtocol
