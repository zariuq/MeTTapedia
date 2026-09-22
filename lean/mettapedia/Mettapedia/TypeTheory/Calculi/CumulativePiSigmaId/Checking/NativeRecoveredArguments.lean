import Mettapedia.Data.Fin.OptionSequence
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeDeclarationSpineSubstitution
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Contextual.NativeCheckedJudgmentPresheaf

/-!
# Checked assignments assembled from recovered argument certificates

An explicit finite position map selects certificates from a recovered pool.
The argument/domain description is compared with the instantiated lookup of
the existing schema context. This earns the original dependent-argument
checker, retaining exactly the selected certificates and their positions.
-/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

set_option autoImplicit false


namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeJudgmentReplay.DeclarationSpineReplay

open Presentation NativeIndexedFamilies

def selectCodes {k n : Nat} (entries : List (Argument n)) (positions : Fin k → Nat) :
    Option (Fin k → Code n) :=
  Fin.sequenceOption k (fun index => (entries[positions index]?).map Argument.code)

theorem selectCodes_checked {k n : Nat} {context : Tower.Ctx n} {contextCode : ContextCode n}
    (schema : Tower.Ctx k) (sigma : Sub Tower.Head k n)
    (entries : List (Argument n)) (positions : Fin k → Nat)
    (checked : ∀ entry ∈ entries, check context entry.subject entry.type contextCode entry.code = true)
    (described : ∀ index, (entries[positions index]?).map (fun entry => (entry.subject, entry.type)) =
      some (sigma index, subst sigma (Ctx.lookup schema index))) :
    ∃ codes, selectCodes entries positions = some codes ∧
      TelescopeArgumentChecking.checkArguments
        (StructuralTypingReplay.check IntrinsicRelator.rules NativeRelatorConversionChecking.check context)
        schema sigma codes = true := by
  have present : ∀ index, ∃ code, (entries[positions index]?).map Argument.code = some code := by
    intro index
    obtain ⟨entry, found, _⟩ := Option.map_eq_some_iff.mp (described index)
    exact ⟨entry.code, by simp only [found, Option.map_some]⟩
  obtain ⟨codes, computed⟩ := Fin.sequenceOption_complete k _ present
  refine ⟨codes, computed, ?_⟩
  apply (TelescopeArgumentChecking.checkArguments_eq_true_iff _ _ _ _).mpr
  intro index
  obtain ⟨entry, found, same⟩ := Option.map_eq_some_iff.mp (described index)
  have selected := Fin.sequenceOption_sound k computed index
  simp only [found, Option.map_some, Option.some.injEq] at selected
  obtain ⟨subjectEq, typeEq⟩ := Prod.mk.inj same
  have accepted := checked entry (List.mem_of_getElem? found)
  simp only [check, StructuralTypingReplay.checkJudgment, Bool.and_eq_true] at accepted
  simpa only [subjectEq, typeEq, selected] using accepted.2

def combinedArguments {n : Nat} (source payload : Tower.Tm n) :
    Option (List (Tower.Tm n × Tower.Tm n)) := do
  let first ← declaredArguments source
  let second ← declaredArguments payload
  return first ++ second

theorem combinedArguments_subst {n m : Nat} (sigma : Sub Tower.Head n m)
    {source payload : Tower.Tm n} {entries : List (Tower.Tm n × Tower.Tm n)}
    (described : combinedArguments source payload = some entries) :
    combinedArguments (subst sigma source) (subst sigma payload) =
      some (entries.map fun entry => (subst sigma entry.1, subst sigma entry.2)) := by
  unfold combinedArguments at described ⊢
  cases first : declaredArguments source with
  | none => simp [first] at described
  | some firstEntries =>
      cases second : declaredArguments payload with
      | none => simp [first, second] at described
      | some secondEntries =>
          simp only [first, second, bind, Option.bind, pure, Option.some.injEq] at described
          subst entries
          simp [declaredArguments_subst source sigma first, declaredArguments_subst payload sigma second]

theorem selectedCombinedArgument_subst {n m : Nat} (sigma : Sub Tower.Head n m)
    {source payload argument type : Tower.Tm n} (position : Nat)
    (selected : (combinedArguments source payload).bind (fun entries => entries[position]?) =
      some (argument, type)) :
    (combinedArguments (subst sigma source) (subst sigma payload)).bind
        (fun entries => entries[position]?) = some (subst sigma argument, subst sigma type) := by
  cases described : combinedArguments source payload with
  | none => simp [described] at selected
  | some entries =>
      simp only [described, Option.bind_some] at selected
      simp only [combinedArguments_subst sigma described, Option.bind_some,
        List.getElem?_map, selected, Option.map_some]

theorem Valid.selectCombined_checked {k n : Nat}
    {context : Tower.Ctx n} {contextCode : ContextCode n}
    {source payload displayed payloadType : Tower.Tm n} {outer inner : Result n}
    (outerValid : Valid context contextCode source displayed outer)
    (innerValid : Valid context contextCode payload payloadType inner)
    (schema : Tower.Ctx k) (sigma : Sub Tower.Head k n) (positions : Fin k → Nat)
    (described : ∀ index, (combinedArguments source payload).bind
        (fun entries => entries[positions index]?) =
      some (sigma index, subst sigma (Ctx.lookup schema index))) :
    ∃ codes, selectCodes (outer.arguments ++ inner.arguments) positions = some codes ∧
      TelescopeArgumentChecking.checkArguments
        (StructuralTypingReplay.check IntrinsicRelator.rules NativeRelatorConversionChecking.check context)
        schema sigma codes = true := by
  apply selectCodes_checked schema sigma (outer.arguments ++ inner.arguments) positions
  · intro entry member
    rcases List.mem_append.mp member with prior | payloadMember
    · exact outerValid.arguments_checked entry prior
    · exact innerValid.arguments_checked entry payloadMember
  · intro index
    have row := described index
    simpa only [combinedArguments, outerValid.arguments_declared, innerValid.arguments_declared,
      bind, Option.bind, pure, ← List.map_append, List.getElem?_map] using row

#print axioms selectCodes_checked
#print axioms combinedArguments_subst
#print axioms selectedCombinedArgument_subst
#print axioms Valid.selectCombined_checked

def instantiateFromPayload {n : Nat} {schemaContext : NativeCheckedSubstitution.Context}
    (schema : NativeCheckedSubstitution.JudgmentReceipt schemaContext)
    (contextCode : ContextCode n) (source displayed : Tower.Tm n) (sourceCode : Code n)
    (payloadPosition : Nat) (sigma : Sub Tower.Head schemaContext.arity n)
    (positions : Fin schemaContext.arity → Nat) : Option (Code n) := do
  let outer ← recover contextCode source displayed sourceCode
  let payload ← outer.arguments[payloadPosition]?
  let inner ← recover contextCode payload.subject payload.type payload.code
  let codes ← selectCodes (outer.arguments ++ inner.arguments) positions
  return outer.tail.fill (NativeJudgmentReplay.substitute sigma codes schema.subject schema.type schema.code)

/-- Complete source recovery earns the schema's dependent argument contract,
then the existing checked substitution algorithm constructs the recursive
result certificate and the original result wrapper is replayed. -/
theorem instantiateFromPayload_checked {n : Nat} {schemaContext : NativeCheckedSubstitution.Context}
    (schema : NativeCheckedSubstitution.JudgmentReceipt schemaContext)
    {context : Tower.Ctx n} {contextCode : ContextCode n}
    {source displayed payload payloadType payloadExpected : Tower.Tm n} {sourceCode : Code n}
    (payloadPosition : Nat) (sigma : Sub Tower.Head schemaContext.arity n)
    (positions : Fin schemaContext.arity → Nat)
    (accepted : check context source displayed contextCode sourceCode = true)
    (predicted : declaredType source = some (subst sigma schema.type))
    (payloadSelected : (declaredArguments source).bind (fun entries => entries[payloadPosition]?) =
      some (payload, payloadType))
    (payloadPredicted : declaredType payload = some payloadExpected)
    (rows : ∀ index, (combinedArguments source payload).bind
        (fun entries => entries[positions index]?) =
      some (sigma index, subst sigma (Ctx.lookup schemaContext.raw index))) :
    ∃ output, instantiateFromPayload schema contextCode source displayed sourceCode
        payloadPosition sigma positions = some output ∧
      check context (subst sigma schema.subject) displayed contextCode output = true := by
  obtain ⟨outer, recovered, typeEq, outerValid⟩ :=
    recover_checked sourceCode context contextCode source displayed _ accepted predicted
  obtain ⟨payloadEntry, found, subjectEq, payloadTypeEq, payloadChecked⟩ :=
    outerValid.argumentAt payloadPosition payloadSelected
  obtain ⟨inner, recoveredPayload, _, innerValid⟩ :=
    recover_checked payloadEntry.code context contextCode payload payloadType payloadExpected
      payloadChecked payloadPredicted
  obtain ⟨codes, selected, imagesChecked⟩ := outerValid.selectCombined_checked innerValid
    schemaContext.raw sigma positions rows
  let output := outer.tail.fill
    (NativeJudgmentReplay.substitute sigma codes schema.subject schema.type schema.code)
  refine ⟨output, ?_, ?_⟩
  · simp [instantiateFromPayload, recovered, found, subjectEq, payloadTypeEq,
      recoveredPayload, selected, output]
  · apply outerValid.replayReplacement
    rw [typeEq]
    have contextAccepted := accepted
    simp only [check, StructuralTypingReplay.checkJudgment, Bool.and_eq_true] at contextAccepted
    exact NativeJudgmentReplay.check_substitute schema.accepted contextCode contextAccepted.1
      sigma codes imagesChecked

#print axioms instantiateFromPayload_checked

end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeJudgmentReplay.DeclarationSpineReplay
