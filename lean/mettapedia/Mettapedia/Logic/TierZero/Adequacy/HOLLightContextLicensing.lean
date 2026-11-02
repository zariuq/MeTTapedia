import Mettapedia.Logic.TierZero.Adequacy.HOLLightSelectedAdmission
import Mathlib.Logic.Relation

/-!
# Minimal rooted context licensing from original selected source admissions

Context licensing observes the original local registered command admission
and the independent source proofs of its selected premises. Public cache data
outside those selected addresses is irrelevant. This is a projection onto
declaration contexts, not an assertion of exact cache/history correspondence.
The latter is a separate observation of original registered-state traces.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.TierZero.Adequacy.HOLLightContextLicensing

open Mettapedia.Languages.OpenTheory
open Mettapedia.Languages.OpenTheory.SignatureFormation
open Mettapedia.Languages.HOLLight.DefinitionAdapters
open Mettapedia.Languages.HOLLight.ProofExecution.Registered

def Admitted (policy : AxiomPolicy) [DecidablePred policy]
    (before after : TheoryContext) : Prop :=
  ∃ (command : Command) (cache : Array Theorem) (output : Output), command.check policy before cache = some output ∧
    output.context = after ∧
    ∀ index ∈ command.parents, ∀ fact,
      cache[index]? = some fact → TheoryDerives policy before fact

def Path (policy : AxiomPolicy) [DecidablePred policy] : TheoryContext → TheoryContext → Prop :=
  Relation.ReflTransGen (Admitted policy)

def Licensed (initial : TheoryContext) (policy : AxiomPolicy) [DecidablePred policy]
    (context : TheoryContext) : Prop := Path policy initial context

theorem admitted_includes (policy : AxiomPolicy) [DecidablePred policy]
    {before after : TheoryContext} (step : Admitted policy before after) :
    before.signature.Includes after.signature := by
  obtain ⟨command, cache, output, checked, rfl, selected⟩ := step
  exact (HOLLightSelectedAdmission.check_sound_selected policy before cache command selected checked).1

theorem path_includes (policy : AxiomPolicy) [DecidablePred policy]
    {before after : TheoryContext} (path : Path policy before after) :
    before.signature.Includes after.signature := by
  induction path with
  | refl => exact .refl _
  | tail prior step earlier => exact earlier.trans (admitted_includes policy step)

theorem initial_licensed (initial : TheoryContext) (policy : AxiomPolicy) [DecidablePred policy] :
    Licensed initial policy initial := .refl

theorem admission_licenses_context (initial : TheoryContext) (policy : AxiomPolicy) [DecidablePred policy]
    {before after : TheoryContext} (prior : Licensed initial policy before)
    (step : Admitted policy before after) : Licensed initial policy after := prior.tail step

theorem path_trans (policy : AxiomPolicy) [DecidablePred policy]
    {first middle last : TheoryContext} (left : Path policy first middle) (right : Path policy middle last) :
    Path policy first last := left.trans right

/-- Weakening follows an actual source-licensed inclusion path, rather than
equality or relabelling of printed context identities. -/
theorem transport_theorem (policy : AxiomPolicy) [DecidablePred policy]
    {before after : TheoryContext} (path : Path policy before after) {fact : Theorem}
    (proof : TheoryDerives policy before fact) : TheoryDerives policy after fact :=
  .weaken (path_includes policy path) proof

theorem checked_command_licenses_output (initial : TheoryContext) (policy : AxiomPolicy) [DecidablePred policy]
    {before : TheoryContext} (prior : Licensed initial policy before) (command : Command) (cache : Array Theorem)
    {output : Output} (checked : command.check policy before cache = some output)
    (selected : ∀ index ∈ command.parents, ∀ fact, cache[index]? = some fact → TheoryDerives policy before fact) :
    Licensed initial policy output.context ∧
      Path policy before output.context ∧
      ∀ fact ∈ output.theorems, TheoryDerives policy output.context fact := by
  have step : Admitted policy before output.context := ⟨command, cache, output, checked, rfl, selected⟩
  exact ⟨prior.tail step, Relation.ReflTransGen.single step,
    (HOLLightSelectedAdmission.check_sound_selected policy before cache command selected checked).2⟩

end Mettapedia.Logic.TierZero.Adequacy.HOLLightContextLicensing
