import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.RhoUnaryCompiler

/-!
# Closing allocated names in the scoped rho compiler

A generated source name is represented by the quote of its seed process.
Closing the outermost target binder leaves all inner binders in place and
replaces precisely the corresponding bound-name value. The accompanying
payload law is essential: a received generated name is forwarded by sending
its seed process rather than an inert literal drop of its quotation.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.RhoUnaryClosing

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.DerivedPresentationSyntax
open Mettapedia.OSLF.MeTTaIL.ScopedPattern
open Mettapedia.OSLF.Binding
open Mettapedia.Languages.ProcessCalculi.PolyadicPi
open Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.RhoUnaryCode
open Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.RhoUnaryCompiler
open Mettapedia.Languages.ProcessCalculi.PiCalculus.Bridges.RhoEncodingTyping
open Mettapedia.Languages.ProcessCalculi.PiCalculus.Bridges.RhoScopedAllocation
open Mettapedia.Languages.ProcessCalculi.RhoCalculus
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.ScopedSubstitutionInert

/-- Close the outermost binder by an allocated name. Inner binders retain
exactly their original indices. -/
def closeSeed {depth : Nat} (seed : Nat) : NameValue (depth + 1) → NameValue depth
  | .bound index => if hit : index.val = depth then .allocated seed
      else .bound ⟨index, by omega⟩
  | .atom label => .atom label
  | .allocated index => .allocated index
  | .reserved channel => .reserved channel

@[simp] theorem closeSeed_weaken {depth : Nat} (seed : Nat) (name : NameValue (depth + 1)) :
    closeSeed seed name.weaken = (closeSeed seed name).weaken := by
  cases name with
  | bound index =>
      by_cases hit : index.val = depth
      · simp [closeSeed, NameValue.weaken, hit]
      · simp [closeSeed, NameValue.weaken, hit]
  | atom label | allocated index | reserved channel => rfl

/-- The exact semantic name substitution agrees with the name-value map. -/
theorem closeSeed_term {depth : Nat} (seed : Nat) (name : NameValue (depth + 1)) :
    semanticSubstName depth (allocatedName seed) name.term = (closeSeed seed name).term := by
  cases name with
  | bound index =>
      by_cases hit : index.val = depth
      · simp [semanticSubstName, semanticSubstNameMark, semanticNormalizeName,
          NameValue.term, closeSeed, hit]
      · simp [semanticSubstName, semanticSubstNameMark, semanticNormalizeName,
          NameValue.term, closeSeed, hit]
  | atom label | reserved channel => rfl
  | allocated index =>
      simpa [NameValue.term, closeSeed] using
        (closed_name_inert ((NameValue.allocated index : NameValue 0).typed)
          ((NameValue.allocated index : NameValue 0).safe)
          ((NameValue.allocated index : NameValue 0).normalized) depth (allocatedName seed))

/-- A bound name's process payload turns into the very seed code that names
the received value. Unrelated closed payloads remain unchanged. -/
theorem closeSeed_payload {depth : Nat} (seed : Nat) (name : NameValue (depth + 1)) :
    semanticSubstProc depth (allocatedName seed) name.payload = (closeSeed seed name).payload := by
  cases name with
  | bound index =>
      by_cases hit : index.val = depth
      · simp [NameValue.payload, NameValue.term, closeSeed, semanticSubstProc,
          semanticSubstNameMark, semanticNormalizeName, hit, allocatedName]
      · simp [NameValue.payload, NameValue.term, closeSeed, semanticSubstProc,
          semanticSubstNameMark, semanticNormalizeName, hit]
  | atom label | reserved channel => rfl
  | allocated index =>
      simpa [NameValue.payload, closeSeed] using
        ((proc_above_scope (seedCode_typed rhoAtomicNameContext index)
          (seedCode_safe index 0) (Nat.zero_le depth)).trans (seedCode_normalized index))

/-- Applying this map to the environment closes the same target binder in
every source-name occurrence. -/
def closeWorld {Γ : Ctx sig} {depth : Nat} (seed : Nat) (world : World Γ (depth + 1)) :
    World Γ depth := fun name => closeSeed seed (world name)

@[simp] theorem closeWorld_lift {Γ : Ctx sig} {depth : Nat} (seed : Nat)
    (world : World Γ (depth + 1)) :
    closeWorld seed (liftWorld world) = liftWorld (closeWorld seed world) := by
  funext name
  cases name with
  | zero => simp [closeWorld, liftWorld, closeSeed]
  | succ old => simp [closeWorld, liftWorld]

@[simp] theorem closeWorld_serverHandler {Γ : Ctx sig} {depth : Nat} (seed : Nat)
    (world : World Γ (depth + 1)) :
    closeWorld seed (serverHandlerWorld world) = serverHandlerWorld (closeWorld seed world) := by
  funext name
  cases name with
  | zero => simp [closeWorld, serverHandlerWorld, closeSeed]
  | succ old => simp [closeWorld, serverHandlerWorld]

@[simp] theorem closeWorld_storedHandler {Γ : Ctx sig} {depth : Nat} (seed : Nat)
    (world : World Γ (depth + 1)) :
    closeWorld seed (storedHandlerWorld world) = storedHandlerWorld (closeWorld seed world) := by
  funext name
  cases name with
  | zero => simp [closeWorld, storedHandlerWorld, closeSeed]
  | succ old => simp [closeWorld, storedHandlerWorld]

@[simp] theorem evalName_close {Γ : Ctx sig} {depth : Nat} (seed : Nat)
    (world : World Γ (depth + 1)) (name : Name Γ) :
    evalName (closeWorld seed world) name = closeSeed seed (evalName world name) := by
  cases name with
  | var name => rfl
  | op op args => cases op

/-- Stored-code binders are retained while an ambient name is closed. -/
theorem storedCode_close {depth : Nat} (seed : Nat) (channel : NameValue (depth + 1))
    (body : Code (depth + 5)) (closedBody : Code (depth + 4))
    (bodyEq : semanticSubstProc (depth + 4) (allocatedName seed) body.term = closedBody.term) :
    semanticSubstProc (depth + 2) (allocatedName seed) (storedCode channel body).term =
      (storedCode (closeSeed seed channel) closedBody).term := by
  have selfMiss : 3 ≠ depth + 4 := by omega
  have codeMiss : 1 ≠ depth + 4 := by omega
  have inputMiss : 1 ≠ depth + 2 := by omega
  have channelEq := closeSeed_term seed channel.weaken.weaken.weaken
  simp only [closeSeed_weaken] at channelEq
  simp only [storedCode, Code.listen, Code.triple, Code.sendName, Code.emit, Code.datum,
    semanticSubstProc, semanticSubstProcList, bodyEq]
  rw [channelEq]
  simp only [NameValue.term, NameValue.payload, semanticSubstProc, semanticSubstName,
    semanticSubstNameMark, semanticNormalizeName, beq_iff_eq, selfMiss, codeMiss, inputMiss, ↓reduceIte]

/-- Server installation accounts for both the retained code template and the
request-dependent continuation at their different target scopes. -/
theorem waitingServer_close {depth : Nat} (seed : Nat) (channel : NameValue (depth + 1))
    (handler : Code (depth + 3)) (closedHandler : Code (depth + 2))
    (storedHandler : Code (depth + 5)) (closedStored : Code (depth + 4))
    (handlerEq : semanticSubstProc (depth + 2) (allocatedName seed) handler.term = closedHandler.term)
    (storedEq : semanticSubstProc (depth + 4) (allocatedName seed) storedHandler.term = closedStored.term) :
    semanticSubstProc (depth + 1) (allocatedName seed)
        (waitingServer channel handler storedHandler).term =
      (waitingServer (closeSeed seed channel) closedHandler closedStored).term := by
  have selfMiss : 1 ≠ depth + 2 := by omega
  have channelEq := closeSeed_term seed channel.weaken
  simp only [closeSeed_weaken] at channelEq
  simp only [waitingServer, Code.listen, Code.triple, Code.emit,
    semanticSubstProc, semanticSubstProcList, handlerEq,
    storedCode_close seed channel storedHandler closedStored storedEq]
  rw [channelEq]
  simp only [NameValue.term, semanticSubstName, semanticSubstNameMark,
    semanticNormalizeName, beq_iff_eq, selfMiss, ↓reduceIte]

/-- Compiling after an allocated-name closing gives the actual semantic
substitution endpoint, for every process in the scoped guarded fragment. -/
theorem compile_closeSeed {Γ : Ctx sig} {process : Proc Γ} (guarded : GuardedUnary process) :
    ∀ {depth : Nat} (world : World Γ (depth + 1)) (seed : Nat) (code : Code (depth + 1)),
      compile world process = some code →
      ∃ closedCode : Code depth,
        compile (closeWorld seed world) process = some closedCode ∧
        semanticSubstProc depth (allocatedName seed) code.term = closedCode.term := by
  induction guarded with
  | nil =>
      intro depth world seed code compiled
      have same : Code.zero (depth + 1) = code := by simpa [compile, nil] using compiled
      subst code
      exact ⟨Code.zero depth, by simp [compile, nil], rfl⟩
  | par firstGuarded secondGuarded firstIH secondIH =>
      intro depth world seed code compiled
      obtain ⟨first, firstEq⟩ := compile_guarded firstGuarded world
      obtain ⟨second, secondEq⟩ := compile_guarded secondGuarded world
      have same : Code.par first second = code := by simpa [compile, par, firstEq, secondEq] using compiled
      subst code
      obtain ⟨closedFirst, closedFirstEq, firstClosed⟩ := firstIH world seed first firstEq
      obtain ⟨closedSecond, closedSecondEq, secondClosed⟩ := secondIH world seed second secondEq
      exact ⟨Code.par closedFirst closedSecond,
        by simp [compile, par, closedFirstEq, closedSecondEq],
        by simp only [Code.par, semanticSubstProc, semanticSubstProcList, firstClosed, secondClosed]⟩
  | inp1 channel bodyGuarded ih =>
      intro depth world seed code compiled
      obtain ⟨body, bodyEq⟩ := compile_guarded bodyGuarded (liftWorld world)
      have same : Code.listen (evalName world channel) body = code := by
        simpa [compile, inp1, bodyEq] using compiled
      subst code
      obtain ⟨closedBody, closedEq, closedTerm⟩ := ih (liftWorld world) seed body bodyEq
      exact ⟨Code.listen (evalName (closeWorld seed world) channel) closedBody,
        by
          rw [closeWorld_lift] at closedEq
          simp [compile, inp1, closedEq],
        by simp only [Code.listen, semanticSubstProc, closeSeed_term, evalName_close, closedTerm]⟩
  | out1 channel datum =>
      intro depth world seed code compiled
      have same : Code.sendName (evalName world channel) (evalName world datum) = code := by
        simpa [compile, out1] using compiled
      subst code
      exact ⟨Code.sendName (evalName (closeWorld seed world) channel) (evalName (closeWorld seed world) datum),
        by simp [compile, out1],
        by simp only [Code.sendName, Code.emit, Code.datum, semanticSubstProc,
          closeSeed_term, closeSeed_payload, evalName_close]⟩
  | nu bodyGuarded ih =>
      intro depth world seed code compiled
      obtain ⟨body, bodyEq⟩ := compile_guarded bodyGuarded (liftWorld world)
      have same : Code.reserve body = code := by simpa [compile, nu, bodyEq] using compiled
      subst code
      obtain ⟨closedBody, closedEq, closedTerm⟩ := ih (liftWorld world) seed body bodyEq
      exact ⟨Code.reserve closedBody,
        by
          rw [closeWorld_lift] at closedEq
          simp [compile, nu, closedEq],
        by simp only [Code.reserve, Code.par, Code.sendName, Code.emit, Code.datum,
          Code.listen, semanticSubstProc, semanticSubstProcList, NameValue.term,
          NameValue.payload, semanticSubstName, semanticSubstNameMark,
          semanticNormalizeName, closedTerm]⟩
  | server channel bodyGuarded ih =>
      intro depth world seed code compiled
      obtain ⟨handler, handlerEq⟩ := compile_guarded bodyGuarded (serverHandlerWorld world)
      obtain ⟨storedHandler, storedEq⟩ := compile_guarded bodyGuarded (storedHandlerWorld world)
      have same : Code.reserve (waitingServer (evalName world channel) handler storedHandler) = code := by
        simpa [compile, rep, inp1, handlerEq, storedEq] using compiled
      subst code
      obtain ⟨closedHandler, closedHandlerEq, handlerClosed⟩ :=
        ih (serverHandlerWorld world) seed handler handlerEq
      obtain ⟨closedStored, closedStoredEq, storedClosed⟩ :=
        ih (storedHandlerWorld world) seed storedHandler storedEq
      refine ⟨Code.reserve
        (waitingServer (evalName (closeWorld seed world) channel) closedHandler closedStored), ?_, ?_⟩
      · rw [closeWorld_serverHandler] at closedHandlerEq
        rw [closeWorld_storedHandler] at closedStoredEq
        simp [compile, rep, inp1, closedHandlerEq, closedStoredEq]
      · simp only [Code.reserve, Code.par, Code.sendName, Code.emit, Code.datum,
          Code.listen, semanticSubstProc, semanticSubstProcList, NameValue.term,
          NameValue.payload, semanticSubstName, semanticSubstNameMark,
          semanticNormalizeName]
        simp only [waitingServer_close seed _ handler closedHandler storedHandler closedStored
          handlerClosed storedClosed, evalName_close]

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.RhoUnaryClosing
