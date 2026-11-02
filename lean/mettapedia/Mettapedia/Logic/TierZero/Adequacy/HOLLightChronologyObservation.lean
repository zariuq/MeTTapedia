import Mettapedia.Logic.TierZero.Adequacy.HOLLightContextLicensing
import Mettapedia.Languages.HOLLight.RegisteredReplayModels

/-!
# Exact registered histories refine the minimal context-license observation

The original state/cache/receipt trace is stronger than logical context
licensing. Each accepted original history projects to the latter while also
retaining exact cache addresses and its independently constructed model frame.
Neither observation grants authority to arbitrary unused public cache rows.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.TierZero.Adequacy.HOLLightChronologyObservation

open Mettapedia.Languages.OpenTheory
open Mettapedia.Languages.HOLLight
open Mettapedia.Languages.HOLLight.DefinitionAdapters
open Mettapedia.Languages.HOLLight.DefinitionModelFamily
open Mettapedia.Languages.HOLLight.ModelInterpretation
open Mettapedia.Languages.HOLLight.ProofExecution.Registered
open Mettapedia.Logic
open HOLLightContextLicensing

theorem apply_projects (policy : AxiomPolicy) [DecidablePred policy]
    {before after : State} {command : Command} (valid : Valid policy before)
    (accepted : apply policy before command = some after) :
    Admitted policy before.context after.context := by
  obtain ⟨output, checked, contextSame, _, _⟩ := apply_result policy accepted
  refine ⟨command, before.cache, output, checked, contextSame.symm, ?_⟩
  intro index _ fact found
  exact valid fact (Array.mem_of_getElem? found)

theorem path_projects (initial : TheoryContext) (policy : AxiomPolicy) [DecidablePred policy]
    : ∀ {before after : State}, (gslt policy).MultiStep before after →
      Valid policy before → Licensed initial policy before.context → Licensed initial policy after.context
  | _, _, .refl _, _, licensed => licensed
  | _, _, .step first rest, valid, licensed => by
      obtain ⟨command, checked⟩ := first
      exact path_projects initial policy rest (apply_preserves_derivations policy valid checked)
        (licensed.tail (apply_projects policy valid checked))

theorem reachable_licensed (initial : TheoryContext) (policy : AxiomPolicy) [DecidablePred policy]
    {after : State} (path : (gslt policy).MultiStep (empty initial) after) :
    Licensed initial policy after.context :=
  path_projects initial policy path (empty_valid policy initial) (initial_licensed initial policy)

theorem reachable_includes_initial (initial : TheoryContext) (policy : AxiomPolicy) [DecidablePred policy]
    {after : State} (path : (gslt policy).MultiStep (empty initial) after) :
    initial.signature.Includes after.context.signature :=
  path_includes policy (reachable_licensed initial policy path)

universe w

/-- The stronger exact-history observation carries the original independent
model family, rather than inferring semantic validity from an axiom list. -/
theorem reachable_frame {initial : TheoryContext} {policy : AxiomPolicy} [DecidablePred policy]
    (primitives : Primitives initial)
    (root : RegisteredReplayModels.Frame.{w} initial policy initial #[])
    {after : State} (path : (gslt policy).MultiStep (empty initial) after) :
    Nonempty (RegisteredReplayModels.Frame.{w} initial policy after.context after.cache) :=
  RegisteredReplayModels.Frame.reachable primitives root path

/-- A later type declaration can use the exact earlier cached existence
proof in the original licensed semantic frame. -/
theorem reachable_existence_provable {initial : TheoryContext} {policy : AxiomPolicy} [DecidablePred policy]
    (primitives : Primitives initial)
    (root : RegisteredReplayModels.Frame.{w} initial policy initial #[])
    {before : State} (path : (gslt policy).MultiStep (empty initial) before)
    {instances : SignatureFormation.InstanceWitnesses} {request : TypeOperatorDefinitionRequest}
    {result : SourceTypeDefinitionResult}
    (admitted : admitSourceTypeInTheory before.context instances request = some result)
    (known : request.existence ∈ before.cache) :
    ∃ frame : RegisteredReplayModels.Frame.{w} initial policy before.context before.cache,
      HOL.ClosedTheorySet.Provable
        (UniversalDefinitionHistory.schemaBackground frame.schemas)
        (TypeAdmission.admittedImage admitted).formula := by
  obtain ⟨frame⟩ := reachable_frame primitives root path
  exact ⟨frame, frame.existence_provable admitted known⟩

end Mettapedia.Logic.TierZero.Adequacy.HOLLightChronologyObservation
