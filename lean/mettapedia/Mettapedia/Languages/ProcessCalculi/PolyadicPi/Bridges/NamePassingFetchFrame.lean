import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingFetchMarking
import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingFetchResidual
import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.ScopedOpening

/-!
# The exposed source fetch frame is guarded and excludes its selected actors

All active source scopes are collected in the physical envelope. Its untouched
frame contains pending binary outputs and guarded unary declarations, including
persistent servers. Constructor addresses distinguish those declarations from
the selected receiver, while lookup actors occur only at the active head.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingFetchFrame

open Mettapedia.OSLF.Binding
open Mettapedia.Languages.LambdaCalculus.NamePassing
open Mettapedia.Languages.ProcessCalculi.PolyadicPi
open Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges
open NamePassingLambda NamePassingActiveOrigins NamePassingFetchEnvelope NamePassingFetchSelected
open NamePassingFetchMarking NamePassingFetchResidual ActiveOriginErasure

private theorem vacuous_par {Γ : Ctx sig} (first second : Proc Γ)
    (left : ScopedOpening.Vacuous first) (right : ScopedOpening.Vacuous second) :
    ScopedOpening.Vacuous (par first second) := by
  simpa only [par, ScopedOpening.Vacuous] using And.intro left right

theorem lookup_frame_vacuous {Γ Δ : Ctx sig} {name : Var Γ Srt.nm}
    {value source target : Expr Srt.nm Γ}
    (selected : Environment.FetchCertificate name value source target)
    (ρ : Ren sig Γ Δ) (result : Var Δ .nm) :
    ScopedOpening.Vacuous (lookupEnvelope selected ρ result).frame := by
  induction selected generalizing Δ with
  | here => simp only [lookupEnvelope, nil, ScopedOpening.Vacuous]
  | app argument selected ih =>
      change ScopedOpening.Vacuous (par (lookupEnvelope selected (push ρ) .zero).frame _)
      apply vacuous_par
      · exact ih _ _
      · apply (ScopedOpening.vacuous_rename _ _).mpr
        simp only [out2, ScopedOpening.Vacuous]
  | defn stored selected ih =>
      change ScopedOpening.Vacuous (par (lookupEnvelope selected (liftRen ρ [Srt.nm]) (.succ result)).frame _)
      apply vacuous_par
      · exact ih _ _
      · apply (ScopedOpening.vacuous_rename _ _).mpr
        simp only [rep, inp1, ScopedOpening.Vacuous]
  | carrier name value selected ih =>
      change ScopedOpening.Vacuous (par (lookupEnvelope selected ρ result).frame _)
      apply vacuous_par
      · exact ih _ _
      · apply (ScopedOpening.vacuous_rename _ _).mpr
        simp only [inp1, ScopedOpening.Vacuous]

theorem event_frame_vacuous {Γ Δ : Ctx sig} {kind : Environment.Action}
    {source target : Expr Srt.nm Γ} (event : Environment.EventCertificate kind source target)
    (nonBeta : kind ≠ .beta) (ρ : Ren sig Γ Δ) (result : Var Δ .nm) :
    ScopedOpening.Vacuous (eventEnvelope event nonBeta ρ result).frame := by
  induction event generalizing Δ with
  | beta => exact False.elim (nonBeta rfl)
  | carrierFetch name value selected => exact lookup_frame_vacuous selected ρ result
  | environmentFetch value selected => exact lookup_frame_vacuous selected (liftRen ρ [Srt.nm]) (.succ result)
  | app argument event ih =>
      change ScopedOpening.Vacuous (par (eventEnvelope event nonBeta (push ρ) .zero).frame _)
      apply vacuous_par
      · exact ih _ _ _
      · apply (ScopedOpening.vacuous_rename _ _).mpr
        simp only [out2, ScopedOpening.Vacuous]
  | defn value event ih =>
      change ScopedOpening.Vacuous (par (eventEnvelope event nonBeta (liftRen ρ [Srt.nm]) (.succ result)).frame _)
      apply vacuous_par
      · exact ih _ _ _
      · apply (ScopedOpening.vacuous_rename _ _).mpr
        simp only [rep, inp1, ScopedOpening.Vacuous]
  | carrier name value event ih =>
      change ScopedOpening.Vacuous (par (eventEnvelope event nonBeta ρ result).frame _)
      apply vacuous_par
      · exact ih _ _ _
      · apply (ScopedOpening.vacuous_rename _ _).mpr
        simp only [inp1, ScopedOpening.Vacuous]

theorem lookup_kind {Γ : Ctx sig} {name : Var Γ Srt.nm} {value source target : Expr Srt.nm Γ}
    (selected : Environment.FetchCertificate name value source target) (address : List Edge) :
    (lookupOrigin selected address).kind = .lookup := by
  induction selected generalizing address with
  | here => rfl
  | app _ _ ih => exact ih _
  | defn _ _ ih => exact ih _
  | carrier _ _ _ ih => exact ih _

theorem input_depth {Γ : Ctx sig} {kind : Environment.Action} {source target : Expr Srt.nm Γ}
    (event : Environment.EventCertificate kind source target) (address : List Edge) :
    address.length ≤ (inputOrigin event address).address.length := by
  induction event generalizing address with
  | beta => simp only [inputOrigin, List.length_cons]; omega
  | carrierFetch | environmentFetch => exact Nat.le_refl _
  | app _ _ ih =>
      have deeper := ih (.function :: address)
      simp only [List.length_cons] at deeper
      simpa only [inputOrigin] using Nat.le_of_succ_le deeper
  | defn _ _ ih =>
      have deeper := ih (.definitionBody :: address)
      simp only [List.length_cons] at deeper
      simpa only [inputOrigin] using Nat.le_of_succ_le deeper
  | carrier _ _ _ ih =>
      have deeper := ih (.carrierBody :: address)
      simp only [List.length_cons] at deeper
      simpa only [inputOrigin] using Nat.le_of_succ_le deeper

theorem output_kind {Γ : Ctx sig} {kind : Environment.Action} {source target : Expr Srt.nm Γ}
    (event : Environment.EventCertificate kind source target) (nonBeta : kind ≠ .beta)
    (address : List Edge) : (outputOrigin event address).kind = .lookup := by
  induction event generalizing address with
  | beta => exact False.elim (nonBeta rfl)
  | carrierFetch _ _ selected | environmentFetch _ selected => exact lookup_kind selected _
  | app _ _ ih | defn _ _ ih | carrier _ _ _ ih => exact ih nonBeta _

private theorem frame_label_ne (origin : Origin) (kind : Kind) (address : List Edge)
    (notLookup : kind ≠ .lookup)
    (outside : origin.kind = .lookup ∨ origin.address.length < address.length) :
    Origin.mk kind address ≠ origin := by
  intro equal
  rcases outside with lookup | shallower
  · exact notLookup ((congrArg Origin.kind equal).trans lookup)
  · have lengths := congrArg (fun selected : Origin => selected.address.length) equal
    simp only at lengths
    omega

/-- No lookup actor is in the untouched frame; an actor above this selected
request also cannot be one of the frame's deeper declaration occurrences. -/
theorem lookup_frame_count_zero {Γ Δ : Ctx sig} {name : Var Γ Srt.nm}
    {value source target : Expr Srt.nm Γ}
    (selected : Environment.FetchCertificate name value source target)
    (address : List Edge) (ρ : Ren sig Γ Δ) (result : Var Δ .nm) (origin : Origin)
    (outside : origin.kind = .lookup ∨ origin.address.length < address.length) :
    originCount (one origin) (lookupMarks selected address ρ result).frame = 0 := by
  induction selected generalizing Δ address with
  | here => rfl
  | app argument selected ih =>
      change originCount (one origin) (.par (lookupMarks selected (.function :: address) (push ρ) .zero).frame
        (.out2 ⟨.application, address⟩)) = 0
      simp only [originCount]
      rw [ih _ _ _ (outside.imp_right (fun deeper => by simpa only [List.length_cons] using Nat.lt_succ_of_lt deeper))]
      simp [one, frame_label_ne origin .application address (by decide) outside]
  | defn stored selected ih =>
      change originCount (one origin) (.par (lookupMarks selected (.definitionBody :: address)
          (liftRen ρ [Srt.nm]) (.succ result)).frame
        (.rep (.inp1 ⟨.definition, address⟩ (mark stored (.definitionValue :: address))))) = 0
      simp only [originCount]
      rw [ih _ _ _ (outside.imp_right (fun deeper => by simpa only [List.length_cons] using Nat.lt_succ_of_lt deeper))]
      simp [one, frame_label_ne origin .definition address (by decide) outside]
  | carrier name value selected ih =>
      change originCount (one origin) (.par (lookupMarks selected (.carrierBody :: address) ρ result).frame
        (.inp1 ⟨.carrier, address⟩ (mark value (.carrierValue :: address)))) = 0
      simp only [originCount]
      rw [ih _ _ _ (outside.imp_right (fun deeper => by simpa only [List.length_cons] using Nat.lt_succ_of_lt deeper))]
      simp [one, frame_label_ne origin .carrier address (by decide) outside]

theorem input_not_lookup {Γ : Ctx sig} {kind : Environment.Action} {source target : Expr Srt.nm Γ}
    (event : Environment.EventCertificate kind source target) (address : List Edge) :
    (inputOrigin event address).kind ≠ .lookup := by
  induction event generalizing address with
  | beta | carrierFetch | environmentFetch => simp only [inputOrigin]; decide
  | app _ _ ih | defn _ _ ih | carrier _ _ _ ih => exact ih _

private theorem older_context_different {Γ : Ctx sig} {kind : Environment.Action}
    {source target : Expr Srt.nm Γ} (event : Environment.EventCertificate kind source target)
    (edge : Edge) (address : List Edge) (olderKind : Kind) :
    Origin.mk olderKind address ≠ inputOrigin event (edge :: address) := by
  intro equal
  have bound := input_depth event (edge :: address)
  have lengths := congrArg (fun origin : Origin => origin.address.length) equal
  simp only [List.length_cons] at bound
  simp only at lengths
  omega

/-- The selected declaration is not one of the original untouched frame's
actors, including declarations at the same reference channel. -/
theorem event_input_frame_zero {Γ Δ : Ctx sig} {kind : Environment.Action}
    {source target : Expr Srt.nm Γ} (event : Environment.EventCertificate kind source target)
    (nonBeta : kind ≠ .beta) (address : List Edge) (ρ : Ren sig Γ Δ) (result : Var Δ .nm) :
    originCount (one (inputOrigin event address)) (eventMarks event nonBeta address ρ result).frame = 0 := by
  induction event generalizing Δ address with
  | beta => exact False.elim (nonBeta rfl)
  | carrierFetch name value selected =>
      exact lookup_frame_count_zero selected (.carrierBody :: address) ρ result ⟨.carrier, address⟩
        (Or.inr (by simp only [List.length_cons]; omega))
  | environmentFetch value selected =>
      exact lookup_frame_count_zero selected (.definitionBody :: address) (liftRen ρ [Srt.nm]) (.succ result)
        ⟨.definition, address⟩ (Or.inr (by simp only [List.length_cons]; omega))
  | app argument event ih =>
      change originCount (one (inputOrigin event (.function :: address)))
        (.par (eventMarks event nonBeta (.function :: address) (push ρ) .zero).frame (.out2 ⟨.application, address⟩)) = 0
      simp only [originCount]
      rw [ih _ _ _ _]
      simp [one, older_context_different event .function address .application]
  | defn value event ih =>
      change originCount (one (inputOrigin event (.definitionBody :: address)))
        (.par (eventMarks event nonBeta (.definitionBody :: address) (liftRen ρ [Srt.nm]) (.succ result)).frame
          (.rep (.inp1 ⟨.definition, address⟩ (mark value (.definitionValue :: address))))) = 0
      simp only [originCount]
      rw [ih _ _ _ _]
      simp [one, older_context_different event .definitionBody address .definition]
  | carrier name value event ih =>
      change originCount (one (inputOrigin event (.carrierBody :: address)))
        (.par (eventMarks event nonBeta (.carrierBody :: address) ρ result).frame
          (.inp1 ⟨.carrier, address⟩ (mark value (.carrierValue :: address)))) = 0
      simp only [originCount]
      rw [ih _ _ _ _]
      simp [one, older_context_different event .carrierBody address .carrier]

theorem event_output_frame_zero {Γ Δ : Ctx sig} {kind : Environment.Action}
    {source target : Expr Srt.nm Γ} (event : Environment.EventCertificate kind source target)
    (nonBeta : kind ≠ .beta) (address : List Edge) (ρ : Ren sig Γ Δ) (result : Var Δ .nm) :
    originCount (one (outputOrigin event address)) (eventMarks event nonBeta address ρ result).frame = 0 := by
  induction event generalizing Δ address with
  | beta => exact False.elim (nonBeta rfl)
  | carrierFetch name value selected =>
      exact lookup_frame_count_zero selected (.carrierBody :: address) ρ result _ (Or.inl (lookup_kind selected _))
  | environmentFetch value selected =>
      exact lookup_frame_count_zero selected (.definitionBody :: address) (liftRen ρ [Srt.nm]) (.succ result)
        _ (Or.inl (lookup_kind selected _))
  | app argument event ih =>
      change originCount (one (outputOrigin event (.function :: address)))
        (.par (eventMarks event nonBeta (.function :: address) (push ρ) .zero).frame (.out2 ⟨.application, address⟩)) = 0
      simp only [originCount]
      rw [ih _ _ _ _]
      simp [one, frame_label_ne _ .application address (by decide) (Or.inl (output_kind event nonBeta _))]
  | defn value event ih =>
      change originCount (one (outputOrigin event (.definitionBody :: address)))
        (.par (eventMarks event nonBeta (.definitionBody :: address) (liftRen ρ [Srt.nm]) (.succ result)).frame
          (.rep (.inp1 ⟨.definition, address⟩ (mark value (.definitionValue :: address))))) = 0
      simp only [originCount]
      rw [ih _ _ _ _]
      simp [one, frame_label_ne _ .definition address (by decide) (Or.inl (output_kind event nonBeta _))]
  | carrier name value event ih =>
      change originCount (one (outputOrigin event (.carrierBody :: address)))
        (.par (eventMarks event nonBeta (.carrierBody :: address) ρ result).frame
          (.inp1 ⟨.carrier, address⟩ (mark value (.carrierValue :: address)))) = 0
      simp only [originCount]
      rw [ih _ _ _ _]
      simp [one, frame_label_ne _ .carrier address (by decide) (Or.inl (output_kind event nonBeta _))]

theorem event_pair_frame_zero {Γ Δ : Ctx sig} {kind : Environment.Action}
    {source target : Expr Srt.nm Γ} (event : Environment.EventCertificate kind source target)
    (nonBeta : kind ≠ .beta) (address : List Edge) (ρ : Ren sig Γ Δ) (result : Var Δ .nm) :
    originCount (pair (inputOrigin event address) (outputOrigin event address))
      (eventMarks event nonBeta address ρ result).frame = 0 := by
  have different : inputOrigin event address ≠ outputOrigin event address := by
    intro equal
    exact input_not_lookup event address ((congrArg Origin.kind equal).trans (output_kind event nonBeta address))
  rw [pair_count _ _ different, event_input_frame_zero, event_output_frame_zero]

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingFetchFrame
