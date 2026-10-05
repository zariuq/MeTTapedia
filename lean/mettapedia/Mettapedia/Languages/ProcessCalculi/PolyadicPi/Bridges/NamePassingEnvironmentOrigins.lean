import Mettapedia.Languages.LambdaCalculus.NamePassingEnvironmentEvents
import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingEnvironmentNative
import Mettapedia.GSLT.Causality.OccurrenceRealization

/-!
# Retained environment origins and compiled execution accounts

Source occurrences carry their actual constructor certificates, firing owner
and serviced reference. Their complete presentation erases to precisely the
independent environment theory. Compilation checks their endpoints using the
existing compiler and sends their erased execution into its path functor.

Source history remains available in the occurrence path; the target execution
retains compiled states and primitive steps. Its account agrees with the
number of supplied source occurrences. This does not reconstruct a unique
target occurrence from an erased target step or endpoint.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingEnvironmentOrigins

open Mettapedia.OSLF.Binding
open Mettapedia.GSLT
open Mettapedia.GSLT.IndexedOperational
open Mettapedia.GSLT.Core.InteractionEvent
open Mettapedia.GSLT.Causality.OccurrenceHistory
open Mettapedia.GSLT.Ultrainfinite
open Mettapedia.Languages.LambdaCalculus
open Mettapedia.Languages.ProcessCalculi.PolyadicPi
open Mettapedia.Languages.ProcessCalculi.PolyadicPi.NativeTypes
open Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingLambda
open Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingEnvironmentNative

/-- An origin is accepted only when the real selected derivation has that origin. -/
def events (Γ : Ctx sig) : InteractionPresentation (environmentTheory Γ) where
  Site := NamePassing.Environment.EventOrigin
  Event origin source target :=
    { certificate : NamePassing.Environment.EventCertificate origin.action source target //
      certificate.origin = origin }
  sound {site _source _target} event := ⟨site.action, event.val.sound⟩

theorem events_complete (Γ : Ctx sig) : (events Γ).Complete := by
  rintro source target ⟨action, step⟩
  obtain ⟨certificate⟩ := NamePassing.Environment.EventCertificate.nonempty_iff.mpr step
  exact ⟨⟨certificate.origin, certificate, rfl⟩⟩

/-- The labelled source history erases into the existing execution category.
The occurrence path itself still contains the origin and its selected evidence. -/
def erasePath {Γ : Ctx sig} :
    {source target : (environmentTheory Γ).Term} →
      OccurrencePath (events Γ) source target →
        ExecutionPath (environmentTheory Γ) source target
  | _, _, .refl term => .refl term
  | _, _, .cons event rest => .cons ⟨event.step⟩ (erasePath rest)

theorem erasePath_length {Γ : Ctx sig} {source target : (environmentTheory Γ).Term}
    (path : OccurrencePath (events Γ) source target) :
    (erasePath path).length = path.sites.length := by
  induction path with
  | refl => rfl
  | cons event rest ih =>
      simp only [erasePath, Route.length, OccurrencePath.sites, List.length_cons, ih]

/-- The compiled execution has the actual supplied endpoints and every
translated source intermediate state. Source origin evidence remains in `path`. -/
def compileHistory {Γ Δ : Ctx sig} (environment : Ren sig Γ Δ) (result : Var Δ .nm)
    {source target : (environmentTheory Γ).Term}
    (path : OccurrencePath (events Γ) source target) :
    ExecutionPath (operationalTheory Δ) (compile source environment result)
      (compile target environment result) :=
  (compiler environment result).mapRoute (erasePath path)

theorem compileHistory_length {Γ Δ : Ctx sig} (environment : Ren sig Γ Δ)
    (result : Var Δ .nm) {source target : (environmentTheory Γ).Term}
    (path : OccurrencePath (events Γ) source target) :
    (compileHistory environment result path).length = path.sites.length :=
  (OperationalTranslation.mapRoute_length _ (erasePath path)).trans (erasePath_length path)

/-- Target accounting charges every supplied event, including repeated
equal-endpoint events whose retained source origins are different. -/
theorem compileHistory_account {Γ Δ : Ctx sig} (environment : Ren sig Γ Δ)
    (result : Var Δ .nm) {source target : (environmentTheory Γ).Term}
    (path : OccurrencePath (events Γ) source target) :
    (transitionAccount (operationalTheory Δ)).of (compileHistory environment result path) =
      Multiplicative.ofAdd path.sites.length :=
  congrArg Multiplicative.ofAdd (compileHistory_length environment result path)

/-- Later stages charge the entire translated history according to their
actual per-transition block lengths. These hypotheses describe the later stage,
not an assumed end-to-end correctness result. -/
theorem staged_history_bounds {Γ Δ : Ctx sig} {targetTheory : GSLT}
    (environment : Ren sig Γ Δ) (result : Var Δ .nm)
    (later : OperationalRealization (operationalTheory Δ) targetTheory)
    (lower upper : Nat)
    (perStep : ∀ {first last} (step : (operationalTheory Δ).Step first last),
      lower ≤ (later.mapStep step).length ∧ (later.mapStep step).length ≤ upper)
    {source target : (environmentTheory Γ).Term}
    (path : OccurrencePath (events Γ) source target) :
    lower * path.sites.length ≤ (later.mapRoute (compileHistory environment result path)).length ∧
      (later.mapRoute (compileHistory environment result path)).length ≤ upper * path.sites.length := by
  have bounds := later.mapRoute_length_bounds lower upper perStep
    (compileHistory environment result path)
  rw [compileHistory_length] at bounds
  exact bounds

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingEnvironmentOrigins
