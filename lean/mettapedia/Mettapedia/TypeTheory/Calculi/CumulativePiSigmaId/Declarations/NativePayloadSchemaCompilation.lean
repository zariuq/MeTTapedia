import Mettapedia.Data.List.FiniteLookup
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Checking.NativeRecoveredArguments

/-!
# Compiled argument recovery for native declaration schemas

Given a checked right-hand side, its open source pattern and a constructor
payload position, compilation locates every telescope variable together with
its dependent type in the declared argument pool. Source/result types and
payload exposure are checked, and missing variables reject compilation.

One general execution theorem transports the compiled plan to every ambient
substitution and accepted source certificate. Selected positions are retained:
recompiling after substitution could merge distinct schema variables. This is
certificate construction for a schema; the caller still needs the declaration's
separate license for the selected computation rule.
-/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

set_option autoImplicit false


namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeJudgmentReplay.PayloadSchemaCompilation

open Presentation NativeIndexedFamilies NativeCheckedSubstitution DeclarationSpineReplay

def compilePositions {k : Nat} (context : Tower.Ctx k) (source payload : Tower.Tm k) :
    Option (Fin k → Nat) := do
  let pool ← combinedArguments source payload
  pool.findPositions (fun index => (.var index, Ctx.lookup context index))

theorem compilePositions_sound {k : Nat} {context : Tower.Ctx k} {source payload : Tower.Tm k}
    {positions : Fin k → Nat} (compiled : compilePositions context source payload = some positions)
    (index : Fin k) :
    (combinedArguments source payload).bind (fun entries => entries[positions index]?) =
      some (.var index, Ctx.lookup context index) := by
  cases described : combinedArguments source payload with
  | none => simp [compilePositions, described] at compiled
  | some entries =>
      simp only [compilePositions, described, bind, Option.bind] at compiled
      simpa only [described, Option.bind_some] using List.findPositions_getElem? compiled index

theorem compilePositions_domain {k : Nat} (context : Tower.Ctx k) (source payload : Tower.Tm k) :
    (compilePositions context source payload).isSome = true ↔
      ∃ entries, combinedArguments source payload = some entries ∧
        ∀ index, (.var index, Ctx.lookup context index) ∈ entries := by
  cases described : combinedArguments source payload with
  | none => simp [compilePositions, described]
  | some entries => simp [compilePositions, described, List.findPositions_isSome_iff]

structure Plan {context : Context} (result : JudgmentReceipt context) where
  source : Tower.Tm context.arity
  payloadPosition : Nat
  payload : Tower.Tm context.arity
  payloadType : Tower.Tm context.arity
  payloadExpected : Tower.Tm context.arity
  positions : Fin context.arity → Nat
  sourceType : declaredType source = some result.type
  selected : (declaredArguments source).bind (fun entries => entries[payloadPosition]?) =
    some (payload, payloadType)
  payloadTypeKnown : declaredType payload = some payloadExpected
  rows : ∀ index, (combinedArguments source payload).bind (fun entries => entries[positions index]?) =
    some (.var index, Ctx.lookup context.raw index)

/-- Compile all recovery obligations from finite declaration data; none of
the plan's proof fields are supplied by the caller. -/
def compile {context : Context} (result : JudgmentReceipt context)
    (source : Tower.Tm context.arity) (payloadPosition : Nat) : Option (Plan result) :=
  if sourceType : declaredType source = some result.type then
    match selected : (declaredArguments source).bind (fun entries => entries[payloadPosition]?) with
    | none => none
    | some (payload, payloadType) =>
        match known : declaredType payload with
        | none => none
        | some payloadExpected =>
            match compiled : compilePositions context.raw source payload with
            | none => none
            | some positions => some ⟨source, payloadPosition, payload, payloadType, payloadExpected,
                positions, sourceType, selected, known, compilePositions_sound compiled⟩
  else none

/-- The compiler accepts exactly when the source has the schema's declared
result type, exposes a typed payload, and covers every schema variable/type
pair. This is a characterization of this recovery fragment, not arbitrary
dependent inference. -/
theorem compile_domain {context : Context} (result : JudgmentReceipt context)
    (source : Tower.Tm context.arity) (payloadPosition : Nat) :
    (compile result source payloadPosition).isSome = true ↔
      declaredType source = some result.type ∧
      ∃ payload payloadType,
        (declaredArguments source).bind (fun entries => entries[payloadPosition]?) =
          some (payload, payloadType) ∧
        (declaredType payload).isSome = true ∧
        (compilePositions context.raw source payload).isSome = true := by
  unfold compile
  split
  · split
    · rename_i missing
      simp only [Option.isSome_none, Bool.false_eq_true, false_iff]
      rintro ⟨_, payload, payloadType, selected, _⟩
      rw [missing] at selected
      contradiction
    · split
      · simp_all
      · split <;> simp_all
  · simp_all

theorem compile_retains_source {context : Context} {result : JudgmentReceipt context}
    {source : Tower.Tm context.arity} {payloadPosition : Nat} {plan : Plan result}
    (compiled : compile result source payloadPosition = some plan) :
    plan.source = source ∧ plan.payloadPosition = payloadPosition := by
  unfold compile at compiled
  split at compiled
  · split at compiled
    · contradiction
    · split at compiled
      · contradiction
      · split at compiled
        · contradiction
        · cases Option.some.inj compiled
          exact ⟨rfl, rfl⟩
  · contradiction

def Plan.execute {schemaContext : Context} {schema : JudgmentReceipt schemaContext}
    (plan : Plan schema) {n : Nat} (contextCode : ContextCode n)
    (displayed : Tower.Tm n) (sourceCode : Code n)
    (sigma : Sub Tower.Head schemaContext.arity n) : Option (Code n) :=
  instantiateFromPayload schema contextCode (subst sigma plan.source) displayed sourceCode
    plan.payloadPosition sigma plan.positions

/-- A successfully compiled schema computes accepted result evidence for
every accepted instance, including conversions on the displayed result.
There is no target-typing premise at the execution boundary. -/
theorem Plan.execute_checked {schemaContext : Context} {schema : JudgmentReceipt schemaContext}
    (plan : Plan schema) {n : Nat} {context : Tower.Ctx n} {contextCode : ContextCode n}
    {displayed : Tower.Tm n} {sourceCode : Code n}
    (sigma : Sub Tower.Head schemaContext.arity n)
    (accepted : check context (subst sigma plan.source) displayed contextCode sourceCode = true) :
    ∃ output, plan.execute contextCode displayed sourceCode sigma = some output ∧
      check context (subst sigma schema.subject) displayed contextCode output = true := by
  apply instantiateFromPayload_checked schema plan.payloadPosition sigma plan.positions accepted
  · exact declaredType_subst plan.source sigma plan.sourceType
  · exact selectedArgument_subst sigma plan.payloadPosition plan.selected
  · exact declaredType_subst plan.payload sigma plan.payloadTypeKnown
  · intro index
    exact selectedCombinedArgument_subst sigma (plan.positions index) (plan.rows index)

#print axioms compilePositions_sound
#print axioms compilePositions_domain
#print axioms compile_domain
#print axioms compile_retains_source
#print axioms Plan.execute_checked

end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeJudgmentReplay.PayloadSchemaCompilation
