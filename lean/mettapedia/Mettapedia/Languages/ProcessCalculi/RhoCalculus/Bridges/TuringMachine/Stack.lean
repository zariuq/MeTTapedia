import Mettapedia.Languages.ProcessCalculi.RhoCalculus.MultiStep
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.ReflectiveReplication
import Mettapedia.OSLF.MeTTaIL.ScopedPattern

/-!
# Unbounded half-tapes as finite rho code

A Scott-encoded list receives its empty and nonempty continuations on two
different ports. Both arguments are consumed; exactly the selected code is
activated by COMM. Nonempty code also sends the head and the complete tail.
An empty-pop continuation sends a blank and the empty list, so crossing an
allocated tape boundary needs no preallocated cells or fresh-name primitive.

`pop` takes two actual canonical COMM steps. `push` takes one. These are tape
operations, not a table interpreter: control lookup and the invariant for
repeated complete-machine executions are separate obligations.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.Bridges.TuringMachine.Stack

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ScopedPattern
open Mettapedia.Languages.ProcessCalculi.RhoCalculus
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.Reduction

abbrev parallel (processes : List Pattern) : Pattern := .collection .hashBag processes none
abbrev zero : Pattern := .apply "PZero" []
abbrev send (channel payload : Pattern) : Pattern := .apply "POutput" [channel, payload]
abbrev receive (channel body : Pattern) : Pattern := .apply "PInput" [channel, .lambda none body]
abbrev drop (index : Nat) : Pattern := .apply "PDrop" [.bvar index]

/-- The closed name `@0` used inside inert numeral code. -/
abbrev symbolPort : Pattern := .apply "NQuote" [zero]

/-- Numeral code uses only input prefixes. Its quotes are genuine rho names. -/
def symbolCode : Nat → Pattern
  | 0 => zero
  | n + 1 => receive symbolPort (symbolCode n)

theorem normalize_symbolCode (n : Nat) :
    semanticNormalizeProc (symbolCode n) = symbolCode n := by
  induction n with
  | zero => rfl
  | succ n ih => simpa [symbolCode, receive, semanticNormalizeProc,
      semanticNormalizeName] using congrArg (receive symbolPort) ih

theorem subst_symbolCode (n k : Nat) (replacement : Pattern) :
    semanticSubstProc k replacement (symbolCode n) = symbolCode n := by
  induction n generalizing k with
  | zero => rfl
  | succ n ih => simp [symbolCode, receive, semanticSubstProc,
      semanticSubstName, semanticSubstNameMark, semanticNormalizeName,
      semanticNormalizeProc, ih]

theorem symbolCode_ioCount (n : Nat) : ioCount (symbolCode n) = n := by
  induction n with
  | zero => simp [symbolCode, zero, ioCount]
  | succ n ih => simp [symbolCode, receive, ioCount, ih, Nat.add_comm]

/-- Structural equivalence cannot collapse two distinct tape symbols. -/
theorem symbolCode_sc_iff (first second : Nat) :
    StructuralCongruence (symbolCode first) (symbolCode second) ↔ first = second := by
  constructor
  · intro same
    simpa only [symbolCode_ioCount] using ioCount_SC same
  · rintro rfl
    exact .refl _

/-- Protocol ports are closed quoted code, rather than an assumed supply of
atomic names. The code's input-prefix count separates their names. -/
def port (index : Nat) : Pattern := .apply "NQuote" [symbolCode index]

@[simp] theorem normalize_port (index : Nat) : semanticNormalizeName (port index) = port index := by
  unfold port
  rw [semanticNormalizeName.eq_4 _ (by
    intro name same
    cases index <;> simp [symbolCode, receive, zero] at same), normalize_symbolCode]

@[simp] theorem subst_port_mark (index k : Nat) (replacement : Pattern) :
    semanticSubstNameMark k replacement (port index) = (port index, false) := by
  rw [semanticSubstNameMark, normalize_port]
  rfl

@[simp] theorem subst_bound_mark (index k : Nat) (replacement : Pattern) :
    semanticSubstNameMark k replacement (.bvar index) =
      if index = k then (replacement, true) else (.bvar index, false) := by
  simp [semanticSubstNameMark, semanticNormalizeName]

@[simp] theorem subst_port (index k : Nat) (replacement : Pattern) :
    semanticSubstName k replacement (port index) = port index := by
  simp [semanticSubstName]

theorem port_sc_iff (first second : Nat) :
    StructuralCongruence (port first) (port second) ↔ first = second := by
  constructor
  · intro same
    simpa [port, ioCount, symbolCode_ioCount] using ioCount_SC same
  · rintro rfl
    exact .refl _

theorem symbolCode_coreShape (index : Nat) : rhoProcCoreShape (symbolCode index) = true := by
  induction index with
  | zero => rfl
  | succ index ih =>
      simpa [symbolCode, receive, rhoProcCoreShape, rhoNameCoreShape] using ih

@[simp] theorem port_coreShape (index : Nat) : rhoNameCoreShape (port index) = true := by
  simpa [port, rhoNameCoreShape] using symbolCode_coreShape index

theorem symbolCode_binderSafe (index depth : Nat) :
    binderSafeAt "NQuote" depth (symbolCode index) = true := by
  induction index generalizing depth with
  | zero => rfl
  | succ index ih => simp [symbolCode, receive, binderSafeAt, binderSafeListAt, ih]

@[simp] theorem port_binderSafe (index depth : Nat) :
    binderSafeAt "NQuote" depth (port index) = true := by
  simpa [port, binderSafeAt] using symbolCode_binderSafe index 0

abbrev nilPort : Pattern := port 1
abbrev consPort : Pattern := port 2
abbrev headPort : Pattern := port 3
abbrev tailPort : Pattern := port 4
abbrev pushPort : Pattern := port 5
abbrev resultPort : Pattern := port 6

/-- A nonempty-case body retains the encoded tail as output data. -/
def consBody (head : Nat) (tail : Pattern) : Pattern :=
  parallel [drop 0, send headPort (symbolCode head), send tailPort tail]

/-- The first received continuation has index one under the second binder. -/
def encode : List Nat → Pattern
  | [] => receive nilPort (receive consPort (drop 1))
  | head :: tail => receive nilPort (receive consPort (consBody head (encode tail)))

theorem normalize_encode (cells : List Nat) :
    semanticNormalizeProc (encode cells) = encode cells := by
  induction cells with
  | nil => rfl
  | cons head tail ih =>
      simp [encode, receive, consBody, parallel, drop, send, semanticNormalizeProc,
        semanticNormalizeProcList, semanticNormalizeName, normalize_symbolCode, ih]

/-- Surrounding communications do not capture a half-tape's own binders. -/
theorem subst_encode (cells : List Nat) (k : Nat) (replacement : Pattern) :
    semanticSubstProc k replacement (encode cells) = encode cells := by
  induction cells generalizing k with
  | nil =>
      simp [encode, receive, drop, semanticSubstProc, semanticSubstName,
        subst_bound_mark]
  | cons head tail ih =>
      simp [encode, receive, consBody, parallel, drop, send, semanticSubstProc,
        semanticSubstProcList, semanticSubstName, subst_symbolCode, ih]

theorem encode_coreShape (cells : List Nat) : rhoProcCoreShape (encode cells) = true := by
  induction cells with
  | nil => rfl
  | cons head tail ih =>
      simp [encode, receive, consBody, parallel, drop, send, rhoProcCoreShape,
        rhoProcCoreShapeList, rhoNameCoreShape, symbolCode_coreShape, ih]

theorem encode_binderSafe (cells : List Nat) : binderSafeAt "NQuote" 0 (encode cells) = true := by
  have all_depths : ∀ depth, binderSafeAt "NQuote" depth (encode cells) = true := by
    induction cells with
    | nil => intro depth; simp [encode, receive, drop, binderSafeAt, binderSafeListAt]
    | cons head tail ih =>
        intro depth
        simp [encode, receive, consBody, parallel, drop, send, binderSafeAt,
          binderSafeListAt, symbolCode_binderSafe, ih]
  exact all_depths 0

def reply (head : Nat) (tail : List Nat) : Pattern :=
  parallel [send headPort (symbolCode head), send tailPort (encode tail)]

def emptyCase : Pattern := reply 0 []

theorem normalize_emptyCase : semanticNormalizeProc emptyCase = emptyCase := rfl

theorem subst_emptyCase (k : Nat) (replacement : Pattern) :
    semanticSubstProc k replacement emptyCase = emptyCase := by
  simp [emptyCase, reply, parallel, send, semanticSubstProc, semanticSubstProcList,
    semanticSubstName, symbolCode, subst_encode]

/-- Both continuations are consumed even when the list is empty. -/
def pop (cells : List Nat) : Pattern :=
  parallel [send nilPort emptyCase, encode cells, send consPort zero]

private theorem singleton_step {channel payload body target : Pattern}
    (computed : semanticCommSubst body payload = target) :
    Nonempty (Reduces (parallel [send channel payload, receive channel body]) target) := by
  exact ⟨Reduces.equiv (.refl _) (Reduces.comm (rest := []))
    (computed ▸ StructuralCongruence.par_singleton _)⟩

private theorem cons_reply_sc (head : Nat) (tail : List Nat) :
    parallel [zero, send headPort (symbolCode head), send tailPort (encode tail)] ≡
      reply head tail := by
  have grouped : parallel [zero, reply head tail] ≡
      parallel [zero, send headPort (symbolCode head), send tailPort (encode tail)] :=
    StructuralCongruence.par_flatten [zero]
      [send headPort (symbolCode head), send tailPort (encode tail)]
  exact .trans _ _ _ (.symm _ _ grouped) (StructuralCongruence.par_nil_left _)

/-- Empty pop supplies a blank forever; nonempty pop preserves the whole
tail. The bound is two communications for every list length. -/
theorem pop_reduces (cells : List Nat) :
    Nonempty (ReducesN 2 (pop cells) (reply (cells.headD 0) cells.tail)) := by
  cases cells with
  | nil =>
      have first : semanticCommSubst (receive consPort (drop 1)) emptyCase =
          receive consPort emptyCase := by
        simp [semanticCommSubst, receive, drop,
          semanticSubstProc, semanticSubstName, normalize_emptyCase]
      have firstStep : Reduces (pop [])
          (parallel [receive consPort emptyCase, send consPort zero]) := by
        change Reduces (parallel ([send nilPort emptyCase,
          receive nilPort (receive consPort (drop 1))] ++ [send consPort zero])) _
        simpa only [first, List.singleton_append] using
          (Reduces.comm (n := nilPort) (q := emptyCase)
            (p := receive consPort (drop 1)) (rest := [send consPort zero]))
      obtain ⟨secondStep⟩ := singleton_step (channel := consPort) (payload := zero)
        (body := emptyCase) (by simpa [semanticCommSubst, semanticCommRepresentative,
          semanticNormalizeProc] using subst_emptyCase 0 (.apply "NQuote" [zero]))
      have second : Reduces (parallel [receive consPort emptyCase, send consPort zero]) emptyCase :=
        .equiv (StructuralCongruence.par_comm _ _) secondStep (.refl _)
      exact ⟨.succ firstStep (.succ second (.zero _))⟩
  | cons head tail =>
      have first : semanticCommSubst (receive consPort (consBody head (encode tail))) emptyCase =
          receive consPort (consBody head (encode tail)) := by
        simp [semanticCommSubst, receive, consBody,
          parallel, send, drop, semanticSubstProc, semanticSubstProcList,
          semanticSubstName,
          subst_symbolCode, subst_encode]
      have firstStep : Reduces (pop (head :: tail))
          (parallel [receive consPort (consBody head (encode tail)), send consPort zero]) := by
        change Reduces (parallel ([send nilPort emptyCase,
          receive nilPort (receive consPort (consBody head (encode tail)))] ++
          [send consPort zero])) _
        simpa only [first, List.singleton_append] using
          (Reduces.comm (n := nilPort) (q := emptyCase)
            (p := receive consPort (consBody head (encode tail))) (rest := [send consPort zero]))
      have secondResult : semanticCommSubst (consBody head (encode tail)) zero =
          parallel [zero, send headPort (symbolCode head), send tailPort (encode tail)] := by
        simp [semanticCommSubst, consBody, parallel,
          send, drop, semanticSubstProc, semanticSubstProcList, semanticSubstName,
          semanticNormalizeProc,
          subst_symbolCode, subst_encode]
      obtain ⟨secondStep⟩ := singleton_step (channel := consPort) secondResult
      have second : Reduces
          (parallel [receive consPort (consBody head (encode tail)), send consPort zero])
          (reply head tail) :=
        .equiv (StructuralCongruence.par_comm _ _) secondStep (cons_reply_sc head tail)
      exact ⟨.succ firstStep (.succ second (.zero _))⟩

/-- A pushed cell is assembled through substitution in an output payload,
where quote opacity does not freeze the received tail. -/
def pushBody (head : Nat) : Pattern :=
  send resultPort (receive nilPort (receive consPort (consBody head (drop 2))))

def push (head : Nat) (tail : List Nat) : Pattern :=
  parallel [send pushPort (encode tail), receive pushPort (pushBody head)]

theorem push_reduces (head : Nat) (tail : List Nat) :
    Nonempty (Reduces (push head tail) (send resultPort (encode (head :: tail)))) := by
  apply singleton_step
  simp [pushBody, semanticCommSubst, send, receive,
    consBody, parallel, drop, semanticSubstProc, semanticSubstProcList,
    semanticSubstName,
    normalize_encode, subst_symbolCode, encode]

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.Bridges.TuringMachine.Stack
