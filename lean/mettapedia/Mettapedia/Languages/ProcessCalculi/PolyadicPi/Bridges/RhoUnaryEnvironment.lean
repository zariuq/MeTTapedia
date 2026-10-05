import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.RhoUnaryNaturality

/-!
# Target binder padding does not change the compiled handler

Persistent-server implementation introduces stored-code binders that have no
source counterpart. In a closed source-name environment, padding those
unused target binders preserves the emitted process. The statement is proved
for the concrete compiler, including all recursive source scopes and servers.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.RhoUnaryEnvironment

open Mettapedia.OSLF.Binding
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.Languages.ProcessCalculi.PolyadicPi
open Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.RhoUnaryCode
open Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.RhoUnaryCompiler
open Mettapedia.Languages.ProcessCalculi.PiCalculus.Bridges.RhoScopedAllocation

private def namePayload (name : Pattern) : Pattern :=
  match name with
  | .apply "NQuote" [process] => process
  | name => .apply "PDrop" [name]

private theorem payload_from_term {depth : Nat} (name : NameValue depth) :
    name.payload = namePayload name.term := by
  cases name <;> rfl

/-- Equal name representations also have equal forwarding payloads. -/
theorem payload_eq {firstDepth secondDepth : Nat}
    {first : NameValue firstDepth} {second : NameValue secondDepth}
    (same : first.term = second.term) : first.payload = second.payload := by
  rw [payload_from_term, payload_from_term, same]

private def raiseName : Pattern → Pattern
  | .bvar index => .bvar (index + 1)
  | name => name

private theorem weaken_from_term {depth : Nat} (name : NameValue depth) :
    name.weaken.term = raiseName name.term := by
  cases name <;> rfl

/-- Padding one implementation binder respects actual name representations. -/
theorem weaken_eq {firstDepth secondDepth : Nat}
    {first : NameValue firstDepth} {second : NameValue secondDepth}
    (same : first.term = second.term) : first.weaken.term = second.weaken.term := by
  rw [weaken_from_term, weaken_from_term, same]

/-- Environments at different target depths denote the same source names. -/
def WorldSame {Γ : Ctx sig} {firstDepth secondDepth : Nat}
    (first : World Γ firstDepth) (second : World Γ secondDepth) : Prop :=
  ∀ name, (first name).term = (second name).term

theorem WorldSame.lift {Γ : Ctx sig} {firstDepth secondDepth : Nat}
    {first : World Γ firstDepth} {second : World Γ secondDepth} (same : WorldSame first second) :
    WorldSame (liftWorld first) (liftWorld second) := by
  intro name
  cases name with
  | zero => rfl
  | succ old => exact weaken_eq (same old)

theorem WorldSame.serverHandler {Γ : Ctx sig} {firstDepth secondDepth : Nat}
    {first : World Γ firstDepth} {second : World Γ secondDepth} (same : WorldSame first second) :
    WorldSame (serverHandlerWorld first) (serverHandlerWorld second) := by
  intro name
  cases name with
  | zero => rfl
  | succ old => exact weaken_eq (weaken_eq (same old))

theorem WorldSame.storedHandler {Γ : Ctx sig} {firstDepth secondDepth : Nat}
    {first : World Γ firstDepth} {second : World Γ secondDepth} (same : WorldSame first second) :
    WorldSame (storedHandlerWorld first) (storedHandlerWorld second) := by
  intro name
  cases name with
  | zero => rfl
  | succ old => exact weaken_eq (weaken_eq (weaken_eq (weaken_eq (same old))))

theorem WorldSame.eval {Γ : Ctx sig} {firstDepth secondDepth : Nat}
    {first : World Γ firstDepth} {second : World Γ secondDepth} (same : WorldSame first second)
    (name : Name Γ) : (evalName first name).term = (evalName second name).term := by
  cases name with
  | var name => exact same name
  | op op args => cases op

private theorem storedCode_same {firstDepth secondDepth : Nat}
    {firstChannel : NameValue firstDepth} {secondChannel : NameValue secondDepth}
    {firstBody : Code (firstDepth + 4)} {secondBody : Code (secondDepth + 4)}
    (channelEq : firstChannel.term = secondChannel.term) (bodyEq : firstBody.term = secondBody.term) :
    (storedCode firstChannel firstBody).term = (storedCode secondChannel secondBody).term := by
  simp only [storedCode, Code.listen, Code.triple, Code.sendName, Code.emit, Code.datum,
    bodyEq, weaken_eq (weaken_eq (weaken_eq channelEq))]
  rfl

private theorem waitingServer_same {firstDepth secondDepth : Nat}
    {firstChannel : NameValue firstDepth} {secondChannel : NameValue secondDepth}
    {firstHandler : Code (firstDepth + 2)} {secondHandler : Code (secondDepth + 2)}
    {firstStored : Code (firstDepth + 4)} {secondStored : Code (secondDepth + 4)}
    (channelEq : firstChannel.term = secondChannel.term)
    (handlerEq : firstHandler.term = secondHandler.term)
    (storedEq : firstStored.term = secondStored.term) :
    (waitingServer firstChannel firstHandler firstStored).term =
      (waitingServer secondChannel secondHandler secondStored).term := by
  simp only [waitingServer, Code.listen, Code.triple, Code.emit,
    weaken_eq channelEq, storedCode_same channelEq storedEq, handlerEq]
  rfl

/-- Target binder padding preserves the concrete compiler's emitted term,
not merely its typing judgment. -/
theorem compile_same {Γ : Ctx sig} {process : Proc Γ} (guarded : GuardedUnary process) :
    ∀ {firstDepth secondDepth : Nat} (firstWorld : World Γ firstDepth) (secondWorld : World Γ secondDepth),
      WorldSame firstWorld secondWorld →
      ∀ (firstCode : Code firstDepth) (secondCode : Code secondDepth),
        compile firstWorld process = some firstCode → compile secondWorld process = some secondCode →
        firstCode.term = secondCode.term := by
  induction guarded with
  | nil =>
      intro firstDepth secondDepth firstWorld secondWorld same firstCode secondCode firstEq secondEq
      have firstSame : Code.zero firstDepth = firstCode := by simpa [compile, nil] using firstEq
      have secondSame : Code.zero secondDepth = secondCode := by simpa [compile, nil] using secondEq
      subst firstCode; subst secondCode; rfl
  | par firstGuarded secondGuarded firstIH secondIH =>
      intro firstDepth secondDepth firstWorld secondWorld same firstCode secondCode firstEq secondEq
      obtain ⟨firstA, firstAEq⟩ := compile_guarded firstGuarded firstWorld
      obtain ⟨secondA, secondAEq⟩ := compile_guarded secondGuarded firstWorld
      obtain ⟨firstB, firstBEq⟩ := compile_guarded firstGuarded secondWorld
      obtain ⟨secondB, secondBEq⟩ := compile_guarded secondGuarded secondWorld
      have firstSame : Code.par firstA secondA = firstCode := by simpa [compile, par, firstAEq, secondAEq] using firstEq
      have secondSame : Code.par firstB secondB = secondCode := by simpa [compile, par, firstBEq, secondBEq] using secondEq
      subst firstCode; subst secondCode
      simp only [Code.par, firstIH firstWorld secondWorld same firstA firstB firstAEq firstBEq,
        secondIH firstWorld secondWorld same secondA secondB secondAEq secondBEq]
  | inp1 channel bodyGuarded ih =>
      intro firstDepth secondDepth firstWorld secondWorld same firstCode secondCode firstEq secondEq
      obtain ⟨bodyA, bodyAEq⟩ := compile_guarded bodyGuarded (liftWorld firstWorld)
      obtain ⟨bodyB, bodyBEq⟩ := compile_guarded bodyGuarded (liftWorld secondWorld)
      have firstSame : Code.listen (evalName firstWorld channel) bodyA = firstCode := by simpa [compile, inp1, bodyAEq] using firstEq
      have secondSame : Code.listen (evalName secondWorld channel) bodyB = secondCode := by simpa [compile, inp1, bodyBEq] using secondEq
      subst firstCode; subst secondCode
      simp only [Code.listen, same.eval channel,
        ih (liftWorld firstWorld) (liftWorld secondWorld) same.lift bodyA bodyB bodyAEq bodyBEq]
  | out1 channel datum =>
      intro firstDepth secondDepth firstWorld secondWorld same firstCode secondCode firstEq secondEq
      have firstSame : Code.sendName (evalName firstWorld channel) (evalName firstWorld datum) = firstCode := by
        simpa [compile, out1] using firstEq
      have secondSame : Code.sendName (evalName secondWorld channel) (evalName secondWorld datum) = secondCode := by
        simpa [compile, out1] using secondEq
      subst firstCode; subst secondCode
      simp only [Code.sendName, Code.emit, Code.datum, same.eval channel, payload_eq (same.eval datum)]
  | nu bodyGuarded ih =>
      intro firstDepth secondDepth firstWorld secondWorld same firstCode secondCode firstEq secondEq
      obtain ⟨bodyA, bodyAEq⟩ := compile_guarded bodyGuarded (liftWorld firstWorld)
      obtain ⟨bodyB, bodyBEq⟩ := compile_guarded bodyGuarded (liftWorld secondWorld)
      have firstSame : Code.reserve bodyA = firstCode := by simpa [compile, nu, bodyAEq] using firstEq
      have secondSame : Code.reserve bodyB = secondCode := by simpa [compile, nu, bodyBEq] using secondEq
      subst firstCode; subst secondCode
      simp only [Code.reserve, Code.par, Code.listen,
        ih (liftWorld firstWorld) (liftWorld secondWorld) same.lift bodyA bodyB bodyAEq bodyBEq]
      rfl
  | server channel bodyGuarded ih =>
      intro firstDepth secondDepth firstWorld secondWorld same firstCode secondCode firstEq secondEq
      obtain ⟨handlerA, handlerAEq⟩ := compile_guarded bodyGuarded (serverHandlerWorld firstWorld)
      obtain ⟨handlerB, handlerBEq⟩ := compile_guarded bodyGuarded (serverHandlerWorld secondWorld)
      obtain ⟨storedA, storedAEq⟩ := compile_guarded bodyGuarded (storedHandlerWorld firstWorld)
      obtain ⟨storedB, storedBEq⟩ := compile_guarded bodyGuarded (storedHandlerWorld secondWorld)
      have firstSame : Code.reserve (waitingServer (evalName firstWorld channel) handlerA storedA) = firstCode := by
        simpa [compile, rep, inp1, handlerAEq, storedAEq] using firstEq
      have secondSame : Code.reserve (waitingServer (evalName secondWorld channel) handlerB storedB) = secondCode := by
        simpa [compile, rep, inp1, handlerBEq, storedBEq] using secondEq
      subst firstCode; subst secondCode
      have handlerSame := ih _ _ same.serverHandler handlerA handlerB handlerAEq handlerBEq
      have storedSame := ih _ _ same.storedHandler storedA storedB storedAEq storedBEq
      simp only [Code.reserve, Code.par, Code.listen,
        waitingServer_same (same.eval channel) handlerSame storedSame]
      rfl

/-- A closed name is unchanged by target binder padding. -/
theorem weaken_ground (name : NameValue 0) : name.weaken.term = name.term := by
  cases name with
  | bound index => exact Fin.elim0 index
  | atom label | allocated index | reserved channel => rfl

/-- The compiled request handler has the same body before and after adding
the server's unused self-code binder. -/
theorem serverHandler_same {Γ : Ctx sig} {body : Proc (.nm :: Γ)}
    (guarded : GuardedUnary body) (world : World Γ 0)
    (ordinary : Code 1) (handler : Code 2) (stored : Code 4)
    (ordinaryEq : compile (liftWorld world) body = some ordinary)
    (handlerEq : compile (serverHandlerWorld world) body = some handler)
    (storedEq : compile (storedHandlerWorld world) body = some stored) :
    handler.term = ordinary.term ∧ stored.term = ordinary.term := by
  have handlerWorld : WorldSame (serverHandlerWorld world) (liftWorld world) := by
    intro name
    cases name with
    | zero => rfl
    | succ old =>
        change (world old).weaken.weaken.term = (world old).weaken.term
        exact weaken_eq (weaken_ground (world old))
  have storedWorld : WorldSame (storedHandlerWorld world) (liftWorld world) := by
    intro name
    cases name with
    | zero => rfl
    | succ old =>
        change (world old).weaken.weaken.weaken.weaken.term = (world old).weaken.term
        exact (weaken_eq (weaken_eq (weaken_eq (weaken_ground (world old))))).trans
          ((weaken_eq (weaken_eq (weaken_ground (world old)))).trans
            (weaken_eq (weaken_ground (world old))))
  exact ⟨compile_same guarded _ _ handlerWorld _ _ handlerEq ordinaryEq,
    compile_same guarded _ _ storedWorld _ _ storedEq ordinaryEq⟩

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.RhoUnaryEnvironment
