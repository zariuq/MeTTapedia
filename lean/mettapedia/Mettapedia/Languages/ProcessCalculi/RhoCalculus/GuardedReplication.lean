import Mettapedia.Languages.ProcessCalculi.RhoCalculus.ParallelContextPaths
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.ChannelSeparation
import Mettapedia.OSLF.MeTTaIL.ScopedPattern

/-!
# Request-guarded replication through reflection

A self-reproducing server waits for a request before rearming and executing
its handler. Initialization takes one COMM step. Each request takes two
communications to restore the same waiting server beside one handler.
The idle server has no reduction, unlike unguarded reflective replication.

The normalization and substitution hypotheses state the exact requirements
on the two closed channels and the closed handler; clients must prove them
for their concrete programs. No replication or restriction primitive is used.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.GuardedReplication

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.Languages.ProcessCalculi.RhoCalculus
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.Reduction

private abbrev par (processes : List Pattern) : Pattern := .collection .hashBag processes none
private abbrev send (channel payload : Pattern) : Pattern := .apply "POutput" [channel, payload]
private abbrev receive (channel body : Pattern) : Pattern := .apply "PInput" [channel, .lambda none body]
private abbrev drop (index : Nat) : Pattern := .apply "PDrop" [.bvar index]

def body (self request handler : Pattern) : Pattern :=
  receive request (par [send self (drop 1), drop 1, handler])

def code (self request handler : Pattern) : Pattern :=
  receive self (body self request handler)

def start (self request handler : Pattern) : Pattern :=
  par [send self (code self request handler), code self request handler]

def idle (self request handler : Pattern) : Pattern :=
  receive request (par [send self (code self request handler), code self request handler, handler])

private theorem subst_drop_eq (index : Nat) (process : Pattern) :
    semanticSubstProc index (.apply "NQuote" [process]) (drop index) = process := by
  simp [drop, semanticSubstProc, semanticSubstNameMark, semanticNormalizeName]

private theorem subst_drop_ne (index target : Nat) (replacement : Pattern) (different : index ≠ target) :
    semanticSubstProc target replacement (drop index) = drop index := by
  simp [drop, semanticSubstProc, semanticSubstNameMark, semanticNormalizeName, different]

section Laws

variable {self request handler : Pattern}
variable (selfNormalized : semanticNormalizeName self = self)
variable (requestNormalized : semanticNormalizeName request = request)
variable (handlerNormalized : semanticNormalizeProc handler = handler)
variable (selfClosed : ∀ k replacement, semanticSubstName k replacement self = self)
variable (requestClosed : ∀ k replacement, semanticSubstName k replacement request = request)
variable (handlerClosed : ∀ k replacement, semanticSubstProc k replacement handler = handler)

include selfNormalized requestNormalized handlerNormalized in
theorem normalize_code :
    semanticNormalizeProc (code self request handler) = code self request handler := by
  simp [code, body, receive, par, send, drop, semanticNormalizeProc,
    semanticNormalizeProcList, semanticNormalizeName, selfNormalized, requestNormalized,
    handlerNormalized]

include selfClosed requestClosed handlerClosed in
theorem subst_code (k : Nat) (replacement : Pattern) :
    semanticSubstProc k replacement (code self request handler) = code self request handler := by
  simp [code, body, receive, par, send, semanticSubstProc, semanticSubstProcList,
    selfClosed, requestClosed, handlerClosed,
    subst_drop_ne 1 (k + 1 + 1) replacement (by omega)]

include selfNormalized requestNormalized handlerNormalized selfClosed requestClosed handlerClosed in
theorem body_received :
    semanticCommSubst (body self request handler) (code self request handler) =
      idle self request handler := by
  simp only [semanticCommSubst,
    normalize_code selfNormalized requestNormalized handlerNormalized,
    body, receive, semanticSubstProc, requestClosed, par, semanticSubstProcList,
    send, selfClosed, subst_drop_eq, handlerClosed, idle]

include selfNormalized requestNormalized handlerNormalized selfClosed requestClosed handlerClosed in
theorem start_reduces :
    Nonempty (Reduces (start self request handler) (idle self request handler)) := by
  have raw := Reduces.comm (n := self) (q := code self request handler)
    (p := body self request handler) (rest := [])
  rw [body_received selfNormalized requestNormalized handlerNormalized selfClosed
    requestClosed handlerClosed] at raw
  exact ⟨.equiv (.refl _) raw (StructuralCongruence.par_singleton _)⟩

include selfClosed requestClosed handlerClosed in
theorem request_received (payload : Pattern) :
    semanticCommSubst
        (par [send self (code self request handler), code self request handler, handler]) payload =
      par [send self (code self request handler), code self request handler, handler] := by
  simp [semanticCommSubst, par, send, semanticSubstProc, semanticSubstProcList,
    selfClosed, subst_code selfClosed requestClosed handlerClosed, handlerClosed]

include selfNormalized requestNormalized handlerNormalized selfClosed requestClosed handlerClosed in
/-- One request activates one handler and restores the same blocked server. -/
theorem request_reduces (payload : Pattern) :
    Nonempty (ReducesN 2 (par [send request payload, idle self request handler])
      (par [idle self request handler, handler])) := by
  have raw := Reduces.comm (n := request) (q := payload)
    (p := par [send self (code self request handler), code self request handler, handler]) (rest := [])
  rw [request_received selfClosed requestClosed handlerClosed] at raw
  have first : Reduces (par [send request payload, idle self request handler])
      (par [start self request handler, handler]) := by
    refine .equiv (.refl _) raw ?_
    refine .trans _ _ _ (StructuralCongruence.par_singleton _) ?_
    exact .symm _ _ (Context.par_flatten_head _ _)
  obtain ⟨second⟩ := start_reduces selfNormalized requestNormalized handlerNormalized
    selfClosed requestClosed handlerClosed
  exact ⟨.succ first (.succ (.par second) (.zero _))⟩

end Laws

/-- The guard prevents autonomous unfolding, for every handler. -/
theorem idle_normal (self request handler : Pattern) (names : List String)
    (unmentioned : nameCount names request = 0) : NormalForm (idle self request handler) := by
  rintro ⟨target, ⟨step⟩⟩
  have separated : separation names (idle self request handler) = 0 := by
    simp [idle, receive, separation, separationHead, unmentioned]
  exact (not_reduces_of_separation_eq_zero names separated target).false step

theorem idle_coreShape (self request handler : Pattern)
    (selfShape : rhoNameCoreShape self = true) (requestShape : rhoNameCoreShape request = true)
    (handlerShape : rhoProcCoreShape handler = true) :
    rhoProcCoreShape (idle self request handler) = true := by
  simp [idle, code, body, receive, par, send, drop, rhoProcCoreShape,
    rhoProcCoreShapeList, rhoNameCoreShape, selfShape, requestShape, handlerShape]

theorem idle_binderSafe (self request handler : Pattern) (depth : Nat)
    (selfSafe : ∀ d, Mettapedia.OSLF.MeTTaIL.ScopedPattern.binderSafeAt "NQuote" d self = true)
    (requestSafe : ∀ d, Mettapedia.OSLF.MeTTaIL.ScopedPattern.binderSafeAt "NQuote" d request = true)
    (handlerSafe : ∀ d, Mettapedia.OSLF.MeTTaIL.ScopedPattern.binderSafeAt "NQuote" d handler = true) :
    Mettapedia.OSLF.MeTTaIL.ScopedPattern.binderSafeAt "NQuote" depth
      (idle self request handler) = true := by
  simp [idle, code, body, receive, par, send, drop,
    Mettapedia.OSLF.MeTTaIL.ScopedPattern.binderSafeAt,
    Mettapedia.OSLF.MeTTaIL.ScopedPattern.binderSafeListAt, selfSafe, requestSafe, handlerSafe]

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.GuardedReplication
