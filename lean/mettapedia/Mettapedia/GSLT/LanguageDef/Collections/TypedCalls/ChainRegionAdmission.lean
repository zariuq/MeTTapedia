import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.ChainPrograms

/-!
# Checked activation boundaries for independently typed call chains

The existing equation evaluator and canonical protocol are retained. A new
activation dispatcher checks its delivered arguments, computes its own range
obligation, and combines it with the incoming tail obligation only when the
two are compatible. A refusal runs the canonical protocol at that same
activation boundary. Non-tail calls start a fresh obligation.

This pure finite-run model allows untyped calls in arbitrary non-tail
positions and separate chains with different ranges. It does not implement
shown-range elision. The boundary-local fallback is an explicit realization;
it is not a claim that the native machine currently retains this boundary
when its preflight or dynamic checks refuse a call.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.ChainRegion

open Mettapedia.Languages.MeTTa.OSLFCore (Atom GroundedValue)

/-- A cheap value-formal check: unchecked positions ask nothing; checked
positions accept a literal of the named class, not merely some type witness. -/
def ValueFormal (A : Ty Empty) (v : Atom) : Prop :=
  demand A.lift ≠ .guarded ∨ match A with
  | .sym c => Literal c v
  | .var x => x.elim
  | .app _ => False

instance (A : Ty Empty) (v : Atom) : Decidable (ValueFormal A v) := by
  unfold ValueFormal
  cases A with
  | var x => exact x.elim
  | sym _ => infer_instance
  | app _ => infer_instance

def ValueArguments (As : List (Ty Empty)) (vs : List Atom) : Prop :=
  List.Forall₂ ValueFormal As vs

instance (As : List (Ty Empty)) (vs : List Atom) : Decidable (ValueArguments As vs) :=
  inferInstanceAs (Decidable (List.Forall₂ ValueFormal As vs))

theorem ValueFormal.entryFact (Γ : Decls) (grounded : String → Bool)
    {A : Ty Empty} {v : Atom} (h : ValueFormal A v) :
    demand A.lift = .guarded → Holds Γ grounded v A := by
  intro hg
  rcases h with hn | hl
  · exact (hn hg).elim
  · cases A with
    | var x => exact x.elim
    | sym c => exact holds_literal hl
    | app _ => exact hl.elim

theorem ValueArguments.entryFacts (Γ : Decls) (grounded : String → Bool)
    {As : List (Ty Empty)} {vs : List Atom} (h : ValueArguments As vs) :
    EntryFacts Γ grounded As vs :=
  h.imp fun _ _ hv => ValueFormal.entryFact Γ grounded hv

/-- No pending range for unguarded ranges; otherwise one check at return. -/
def rowOwe (R : Ty Empty) : Option (Ty Empty) :=
  if ResultGuarded R.lift then some R else none

/-- The check is decided from the signature and delivered values. `none`
refuses this activation; `some none` admits it without a range obligation. -/
def entryAdmission (rows : String → Option (List (Ty Empty) × Ty Empty))
    (h : String) (vs : List Atom) : Option (Option (Ty Empty)) :=
  match rows h with
  | none => some none
  | some (As, R) => if ValueArguments As vs then some (rowOwe R) else none

def Compatible : Option (Ty Empty) → Option (Ty Empty) → Prop
  | some A, some B => A = B
  | _, _ => True

instance (o q : Option (Ty Empty)) : Decidable (Compatible o q) := by
  cases o <;> cases q <;> unfold Compatible <;> infer_instance

theorem owedCheck_compatible (Γ : Decls) (grounded : String → Bool)
    (functional : Functional Γ) {o q : Option (Ty Empty)} (h : Compatible o q)
    (answers : Multiset Atom) :
    owedCheck Γ grounded (o.or q) answers =
      owedCheck Γ grounded o (owedCheck Γ grounded q answers) := by
  cases o with
  | none => rfl
  | some A =>
      cases q with
      | none => rfl
      | some B =>
          change A = B at h
          subst B
          exact (rangeCheck_idem grounded functional A answers).symm

/-- Accepted literal checks derive the entry factor one. No whole-program
entry invariant or oracle typing hypothesis is assumed. -/
theorem row_call (Γ : Decls) (grounded : String → Bool)
    (As : List (Ty Empty)) (R : Ty Empty) (vs : List Atom)
    (checked : ValueArguments As vs) (body : List Atom → Multiset Atom) :
    chainCall Γ (metatype grounded) body (arrow (As.map Ty.lift) R.lift) vs =
      owedCheck Γ grounded (rowOwe R) (body vs) := by
  rw [chainCall_closed, argCount_of_entryFacts (checked.entryFacts Γ grounded), one_nsmul]
  unfold rowOwe
  split_ifs
  · rfl
  · change ((body vs).bind fun r => ({r} : Multiset Atom)) = body vs
    rw [Multiset.bind_singleton, Multiset.map_id']

abbrev Steps := String → (String → List Atom → Multiset Atom) → List Atom →
  Multiset (Atom ⊕ (String × List Atom))

theorem protocol_step (Γ : Decls) (grounded : String → Bool)
    (rows : String → Option (List (Ty Empty) × Ty Empty)) (steps : Steps)
    (n : Nat) (h : String) (vs : List Atom) {q : Option (Ty Empty)}
    (accepted : entryAdmission rows h vs = some q) :
    protocolRunS Γ grounded (sigOf rows) steps (n + 1) h vs =
      owedCheck Γ grounded q
        ((steps h (protocolRunS Γ grounded (sigOf rows) steps n) vs).bind
          (outcomeAnswers (protocolRunS Γ grounded (sigOf rows) steps n))) := by
  cases hr : rows h with
  | none =>
      simp only [entryAdmission, hr, Option.some.injEq] at accepted
      subst q
      simp only [protocolRunS, sigOf, hr, Option.map_none, owedCheck]
  | some pair =>
      rcases pair with ⟨As, R⟩
      simp only [entryAdmission, hr] at accepted
      split_ifs at accepted with checked
      · cases accepted
        simp only [protocolRunS, sigOf, hr, Option.map_some]
        exact row_call Γ grounded As R vs checked _

/-- A checked region dispatcher. A refused entry has not executed the body.
Tail re-entry carries the merged debt; non-tail calls open their own chain. -/
noncomputable def run (Γ : Decls) (grounded : String → Bool)
    (rows : String → Option (List (Ty Empty) × Ty Empty)) (steps : Steps) :
    Nat → Option (Ty Empty) → String → List Atom → Multiset Atom
  | 0, _, _, _ => 0
  | n + 1, o, h, vs =>
      match entryAdmission rows h vs with
      | none => owedCheck Γ grounded o (protocolRunS Γ grounded (sigOf rows) steps (n + 1) h vs)
      | some q =>
          if Compatible o q then
            (steps h (fun g ws => run Γ grounded rows steps n none g ws) vs).bind fun
              | .inl r => owedCheck Γ grounded (o.or q) {r}
              | .inr (g, ws) => run Γ grounded rows steps n (o.or q) g ws
          else owedCheck Γ grounded o (protocolRunS Γ grounded (sigOf rows) steps (n + 1) h vs)

theorem run_accepted (Γ : Decls) (grounded : String → Bool)
    (rows : String → Option (List (Ty Empty) × Ty Empty)) (steps : Steps)
    (n : Nat) (o : Option (Ty Empty)) (h : String) (vs : List Atom)
    {q : Option (Ty Empty)} (accepted : entryAdmission rows h vs = some q)
    (compatible : Compatible o q) :
    run Γ grounded rows steps (n + 1) o h vs =
      (steps h (fun g ws => run Γ grounded rows steps n none g ws) vs).bind (fun
        | .inl r => owedCheck Γ grounded (o.or q) {r}
        | .inr (g, ws) => run Γ grounded rows steps n (o.or q) g ws) := by
  rw [run, accepted]
  exact if_pos compatible

/-- Exact observation at every fuel, with no global common range and no
restriction that calls to untyped heads occur only in tail positions. -/
theorem run_eq_protocol (Γ : Decls) (grounded : String → Bool)
    (functional : Functional Γ) (rows : String → Option (List (Ty Empty) × Ty Empty))
    (steps : Steps) : ∀ n o h vs,
    run Γ grounded rows steps n o h vs =
      owedCheck Γ grounded o (protocolRunS Γ grounded (sigOf rows) steps n h vs)
  | 0, o, _, _ => by cases o <;> simp [run, protocolRunS, owedCheck, rangeCheck]
  | n + 1, o, h, vs => by
      simp only [run]
      cases ha : entryAdmission rows h vs with
      | none => rfl
      | some q =>
          simp only
          split_ifs with compatible
          · have same : (fun g ws => run Γ grounded rows steps n none g ws) =
                protocolRunS Γ grounded (sigOf rows) steps n := by
              funext g ws
              exact run_eq_protocol Γ grounded functional rows steps n none g ws
            rw [same, protocol_step Γ grounded rows steps n h vs ha,
              ← owedCheck_compatible Γ grounded functional compatible, owedCheck_bind]
            exact Multiset.bind_congr fun c _ => by
              cases c with
              | inl r => rfl
              | inr pair => exact run_eq_protocol Γ grounded functional rows steps n (o.or q) pair.1 pair.2
          · rfl

/-- The source instance uses the existing outcome evaluator of the authored
equations, not a separate relation chosen to agree with the machine. -/
theorem program_run_eq_protocol (Γ : Decls) (grounded : String → Bool)
    (functional : Functional Γ) (rows : String → Option (List (Ty Empty) × Ty Empty))
    (E : Env) (eqs : String → List Equation) (n : Nat) (h : String) (vs : List Atom) :
    run Γ grounded rows (stepsOf E eqs) n none h vs =
      protocolRunS Γ grounded (sigOf rows) (stepsOf E eqs) n h vs :=
  run_eq_protocol Γ grounded functional rows (stepsOf E eqs) n none h vs

namespace Controls

open Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.Controls
  (decls decls_functional env num str rangeCheck_value)

theorem number_return (grounded : String → Bool) (n : Int) :
    owedCheck decls grounded (some (.sym "Number")) {num n} = {num n} := by
  simpa [owedCheck, num] using
    rangeCheck_value grounded (g := .int n) (c := "Number") (c' := "Number") rfl (by decide)

theorem string_return (grounded : String → Bool) (s : String) :
    owedCheck decls grounded (some (.sym "String")) {str s} = {str s} := by
  simpa [owedCheck, str] using
    rangeCheck_value grounded (g := .string s) (c := "String") (c' := "String") rfl (by decide)

theorem number_rejects_string (grounded : String → Bool) (s : String) :
    owedCheck decls grounded (some (.sym "Number")) {str s} = 0 := by
  simpa only [owedCheck, str, if_neg (by decide : ("Number" : String) ≠ "String")] using
    rangeCheck_value grounded (g := .string s) (c := "String") (c' := "Number") rfl (by decide)

theorem string_rejects_number (grounded : String → Bool) (n : Int) :
    owedCheck decls grounded (some (.sym "String")) {num n} = 0 := by
  simpa only [owedCheck, num, if_neg (by decide : ("String" : String) ≠ "Number")] using
    rangeCheck_value grounded (g := .int n) (c := "Number") (c' := "String") rfl (by decide)

/-- The caller and its tail callee owe Number. The untyped non-tail helper
opens a separate chain whose typed callee owes String. -/
def separateRows : String → Option (List (Ty Empty) × Ty Empty)
  | "main" | "number" => some ([], .sym "Number")
  | "string" => some ([], .sym "String")
  | _ => none

def separateEqs : String → List Equation
  | "main" => [⟨[], .letE (.var "ignored") (.enter "helper" []) (.enter "number" [])⟩]
  | "helper" => [⟨[], .enter "string" []⟩]
  | "number" => [⟨[], .const (num 7)⟩]
  | "string" => [⟨[], .const (str "s")⟩]
  | _ => []

theorem separate_string (grounded : String → Bool) (n : Nat) :
    run decls grounded separateRows (stepsOf env separateEqs) (n + 1) none "string" [] = {str "s"} := by
  rw [run_accepted decls grounded separateRows _ n none "string" []
    (q := some (.sym "String")) (by decide) (by decide)]
  simpa [stepsOf, separateEqs, Pat.matchAll, Expr.evalOut, Expr.eval] using string_return grounded "s"

theorem separate_number (grounded : String → Bool) (n : Nat) :
    run decls grounded separateRows (stepsOf env separateEqs) (n + 1) (some (.sym "Number"))
      "number" [] = {num 7} := by
  rw [run_accepted decls grounded separateRows _ n (some (.sym "Number")) "number" []
    (q := some (.sym "Number")) (by decide) (by decide)]
  simpa [stepsOf, separateEqs, Pat.matchAll, Expr.evalOut, Expr.eval] using number_return grounded 7

theorem separate_helper (grounded : String → Bool) (n : Nat) :
    run decls grounded separateRows (stepsOf env separateEqs) (n + 2) none "helper" [] = {str "s"} := by
  rw [run_accepted decls grounded separateRows _ (n + 1) none "helper" []
    (q := none) (by decide) (by decide)]
  simpa [stepsOf, separateEqs, Pat.matchAll, Expr.evalOut, Expr.evalAll] using separate_string grounded n

theorem separate_main_step (P : String → List Atom → Multiset Atom) :
    stepsOf env separateEqs "main" P [] =
      (P "helper" []).bind (fun _ => ({.inr ("number", [])} : Multiset (Atom ⊕ (String × List Atom)))) := by
  simp [stepsOf, separateEqs, Pat.matchAll, Expr.evalOut, Expr.eval, Expr.evalAll, oracleOf,
    Pat.matchUnder, Pat.match, Pat.extend]

/-- Authored source with a non-tail call to an untyped helper, and with two
different owed classes in separate activation chains, evaluates exactly. -/
theorem separate_chains (grounded : String → Bool) (n : Nat) :
    run decls grounded separateRows (stepsOf env separateEqs) (n + 3) none "main" [] = {num 7} := by
  rw [run_accepted decls grounded separateRows _ (n + 2) none "main" []
    (q := some (.sym "Number")) (by decide) (by decide), separate_main_step]
  rw [separate_helper grounded n]
  simpa using separate_number grounded (n + 1)

theorem separate_chains_protocol (grounded : String → Bool) (n : Nat) :
    protocolRunS decls grounded (sigOf separateRows) (stepsOf env separateEqs)
      (n + 3) "main" [] = {num 7} := by
  rw [← program_run_eq_protocol decls grounded decls_functional]
  exact separate_chains grounded n

/-- The earlier whole-program syntactic restriction rejects this same
program solely because the untyped helper occurs outside a tail position. -/
theorem earlier_tail_restriction_rejects :
    ¬ TailOut (typedHead separateRows) true
      (.letE (.var "ignored") (.enter "helper" []) (.enter "number" [])) := by
  intro h
  cases h with
  | plain hc => simp [CallsTyped, typedHead, separateRows] at hc
  | letE hc _ => simp [CallsTyped, typedHead, separateRows] at hc

/-- Carrying the caller's range into the helper would discard its valid
String answer, whereas the separate String activation returns it once. -/
theorem inherited_nonTail_range_breaks (grounded : String → Bool) :
    owedCheck decls grounded (some (.sym "Number"))
      (owedCheck decls grounded (some (.sym "String")) {str "s"}) = 0 ∧
    owedCheck decls grounded (some (.sym "String")) {str "s"} = {str "s"} := by
  rw [string_return, number_rejects_string]
  exact ⟨rfl, rfl⟩

/-- The earlier counterexample's invalid typed entry is refused by an
actual value check, even though its untyped producer is allowed to run. -/
theorem untyped_bad_argument_refused :
    entryAdmission Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.Controls.argRows
      "g" [str "s"] = none := by decide

def conflictingRows : String → Option (List (Ty Empty) × Ty Empty)
  | "outer" => some ([], .sym "Number")
  | "badString" => some ([], .sym "String")
  | _ => none

def conflictingEqs : String → List Equation
  | "outer" => [⟨[], .enter "badString" []⟩]
  | "badString" => [⟨[], .const (num 7)⟩]
  | _ => []

theorem conflicting_debts_refused :
    ¬ Compatible (some (.sym "Number")) (some (.sym "String")) := by decide

theorem conflicting_callee_protocol (grounded : String → Bool) (n : Nat) :
    protocolRunS decls grounded (sigOf conflictingRows) (stepsOf env conflictingEqs)
      (n + 1) "badString" [] = 0 := by
  rw [protocol_step decls grounded conflictingRows _ n "badString" []
    (q := some (.sym "String")) (by decide)]
  simpa [stepsOf, conflictingEqs, Pat.matchAll, Expr.evalOut, Expr.eval, outcomeAnswers] using
    string_rejects_number grounded 7

theorem conflicting_callee_run (grounded : String → Bool) (n : Nat) :
    run decls grounded conflictingRows (stepsOf env conflictingEqs)
      (n + 1) (some (.sym "Number")) "badString" [] = 0 := by
  rw [run_eq_protocol _ _ decls_functional, conflicting_callee_protocol]
  simp [owedCheck, rangeCheck]

theorem conflicting_chain_keeps_both_checks (grounded : String → Bool) (n : Nat) :
    run decls grounded conflictingRows (stepsOf env conflictingEqs)
      (n + 2) none "outer" [] = 0 := by
  rw [run_accepted decls grounded conflictingRows _ (n + 1) none "outer" []
    (q := some (.sym "Number")) (by decide) (by decide)]
  simpa [stepsOf, conflictingEqs, Pat.matchAll, Expr.evalOut, Expr.evalAll] using
    conflicting_callee_run grounded n

/-- Without the compatibility check, the old unchecked transfer keeps only
Number and lets a Number returned by a String head escape. The checked
dispatcher preserves the canonical rejection instead. -/
theorem unchecked_conflict_invents_answer (grounded : String → Bool) (n : Nat) :
    machineRunS decls grounded (oweOf conflictingRows (fun _ => false))
      (stepsOf env conflictingEqs) (n + 2) (some (.sym "Number")) "outer" [] = {num 7} ∧
    run decls grounded conflictingRows (stepsOf env conflictingEqs)
      (n + 2) none "outer" [] = 0 := by
  refine ⟨?_, conflicting_chain_keeps_both_checks grounded n⟩
  rw [machineRunS]
  simp only [stepsOf, conflictingEqs, Multiset.coe_singleton, Multiset.singleton_bind,
    Pat.matchAll, Expr.evalOut, Expr.evalAll, Multiset.map_singleton]
  change machineRunS decls grounded (oweOf conflictingRows (fun _ => false))
    (stepsOf env conflictingEqs) (n + 1) (some (.sym "Number")) "badString" [] = {num 7}
  rw [machineRunS]
  simpa [stepsOf, conflictingEqs, Pat.matchAll, Expr.evalOut, Expr.eval] using number_return grounded 7

end Controls

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.ChainRegion
