import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.TypedPublicationRealization

/-!
# Typed readouts, repeated refinement and solution coverage

Publication preserves typed values under agreement and literal source code
under explicit substitution. These are different observations. The coverage
theorem keeps each observer's context, including the empty context; symbolic
solvability is not substituted for closed realization.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.TypedPublication

open _root_.CategoryTheory
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta DependentFull

variable {Head : Type} {rules : Rules Head}

namespace Output

variable {Γ Δ Θ : Context rules} (output : Output Γ)

def readout (substitution : Δ ⟶ Γ) (licensed : output.At substitution) : TotalTerm Δ :=
  ⟨output.expected.reindex substitution, output.realize substitution licensed⟩

theorem readout_code (substitution : Δ ⟶ Γ) (licensed : output.At substitution) :
    (output.readout substitution licensed).2.code = subst substitution.substitution output.value.2.code := rfl

theorem readout_type (substitution : Δ ⟶ Γ) (licensed : output.At substitution) :
    (output.readout substitution licensed).1 = output.expected.reindex substitution := rfl

/-- Repeated refinement keeps the same type and substituted code, not just
an equal observation after erasing the source syntax. -/
theorem readout_precompose (first : Δ ⟶ Γ) (second : Θ ⟶ Δ) (licensed : output.At first) :
    (output.readout first licensed).reindex second =
      output.readout (second ≫ first) (Output.At.precompose output licensed second) :=
  totalTerm_ext (output.expected.reindex_comp second first).symm
    (subst_subComp second.substitution first.substitution output.value.2.code)

theorem readout_reindex (first : Δ ⟶ Γ) (second : Θ ⟶ Δ)
    (licensed : (output.reindex first).At second) :
    (output.reindex first).readout second licensed =
      output.readout (second ≫ first) ((output.at_reindex_iff first second).mp licensed) :=
  totalTerm_ext (output.expected.reindex_comp second first).symm
    (subst_subComp second.substitution first.substitution output.value.2.code)

variable {L : Type} [UniverseLevel.LevelOrder L] (levels : LevelModel rules L)

theorem readout_agree {first second : Δ ⟶ Γ}
    (agree : UnificationWithLevels.Agree (frames levels) first second)
    (firstLicense : output.At first) (secondLicense : output.At second) :
    (frames levels).E (output.readout first firstLicense) (output.readout second secondLicense) :=
  output.realized_values_agree levels agree firstLicense secondLicense

/-- An actual helper isomorphism transports the readout by its actual map.
This does not identify raw substitutions or license illegal dependent swaps. -/
theorem helper_iso_readout (iso : Γ ≅ Δ) (substitution : Θ ⟶ Δ)
    (licensed : (output.reindex iso.inv).At substitution) :
    (output.reindex iso.inv).readout substitution licensed =
      output.readout (substitution ≫ iso.inv)
        ((output.at_reindex_iff iso.inv substitution).mp licensed) :=
  output.readout_reindex iso.inv substitution licensed

end Output

variable {L : Type} [UniverseLevel.LevelOrder L] {levels : LevelModel rules L} {O : Type}
  {state : State rules O} {schema : Schema levels O state.frame} {pick : Pick schema}
  {target : Context rules} {answer : target ⟶ schema.helpers.frame}

/-- Coverage preserves existence at each fixed context, including the closed
one. It does not turn a variable in a nonempty context into a closed inhabitant. -/
theorem Basis.realization_exists_iff (basis : Basis levels O schema pick answer) (observer : Context rules) :
    (∃ solution : observer ⟶ schema.helpers.frame,
      (frames levels).Models solution (schema.compile pick).information) ↔
    ∃ further : observer ⟶ target, (frames levels).Models further basis.knowledge := by
  constructor
  · rintro ⟨solution, solved⟩
    obtain ⟨further, valid, _⟩ := basis.covers solution solved
    exact ⟨further, valid⟩
  · rintro ⟨further, valid⟩
    exact ⟨further ≫ answer, basis.sound further valid⟩

/-- The representative carries every licensed typed source readout, for
every original solution, after the appropriate residual interpretation. -/
theorem Basis.covers_typed_outputs (basis : Basis levels O schema pick answer)
    (licensed : ∀ output ∈ schema.outputs, output.At answer)
    {observer : Context rules} (solution : observer ⟶ schema.helpers.frame)
    (solved : (frames levels).Models solution (schema.compile pick).information) :
    ∃ (further : observer ⟶ target) (_valid : (frames levels).Models further basis.knowledge),
      ∀ (output : Code schema.helpers.frame) (member : output ∈ schema.outputs),
        ∃ sourceLicense : output.At solution,
          (frames levels).E (output.readout solution sourceLicense)
            ((output.readout answer (licensed output member)).reindex further) := by
  obtain ⟨further, valid, agree⟩ := basis.covers solution solved
  refine ⟨further, valid, fun output member => ?_⟩
  have residualLicense := output.at_precompose (licensed output member) further
  have sourceLicense := (output.at_agree levels agree).mpr residualLicense
  refine ⟨sourceLicense, ?_⟩
  rw [output.readout_precompose]
  exact output.readout_agree levels agree sourceLicense residualLicense

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.TypedPublication

#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.TypedPublication.Output.readout_precompose
#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.TypedPublication.Basis.realization_exists_iff
#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.TypedPublication.Basis.covers_typed_outputs
