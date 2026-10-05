import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingFetchEnvelope
import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingFetchSelected
import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.ActiveScopeTransport

/-!
# A source fetch exposes the same marked request and scope telescope

The physical lookup envelope moves each authored private binder and each
pending context frame together with its original actor mark. Both directions
use only the actual parallel and scope equations. Thus selected origins can
be followed through this normalization without assigning labels after the
target has chosen a communication.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingFetchMarking

open Mettapedia.OSLF.Binding
open Mettapedia.Languages.LambdaCalculus.NamePassing
open Mettapedia.Languages.ProcessCalculi.PolyadicPi
open Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges
open NamePassingLambda NamePassingActiveOrigins NamePassingFetchEnvelope NamePassingFetchSelected
open ActiveMarking ScopedActiveFrontier

private theorem frame_forward {Γ Δ : Ctx sig} {scope : Scope Γ Δ}
    (binders : ScopeMarks Origin scope) (body frame : Proc Δ) (extra : Proc Γ)
    (bodyMarks frameMarks extraMarks : ActiveMarking.Tree Origin) :
    Transport (.par (binders.close (.par bodyMarks frameMarks)) extraMarks)
      (par (scope.close (par body frame)) extra)
      (binders.close (.par bodyMarks (.par frameMarks extraMarks)))
      (scope.close (par body (par frame (rename scope.inclusion extra)))) :=
  .trans (ActiveScopeTransport.par_forward binders _ extra _ extraMarks)
    (ActiveScopeTransport.congr binders (.parAssoc _ _ _ _ _ _))

private theorem frame_backward {Γ Δ : Ctx sig} {scope : Scope Γ Δ}
    (binders : ScopeMarks Origin scope) (body frame : Proc Δ) (extra : Proc Γ)
    (bodyMarks frameMarks extraMarks : ActiveMarking.Tree Origin) :
    Transport (binders.close (.par bodyMarks (.par frameMarks extraMarks)))
      (scope.close (par body (par frame (rename scope.inclusion extra))))
      (.par (binders.close (.par bodyMarks frameMarks)) extraMarks)
      (par (scope.close (par body frame)) extra) :=
  .trans (ActiveScopeTransport.congr binders (.parAssocBack _ _ _ _ _ _))
    (ActiveScopeTransport.par_backward binders _ extra _ extraMarks)

structure LookupMarks {Γ Δ : Ctx sig} {name : Var Γ Srt.nm}
    {value source target : Expr Srt.nm Γ}
    (selected : Environment.FetchCertificate name value source target)
    (address : List Edge) (ρ : Ren sig Γ Δ) (result : Var Δ .nm) where
  binders : ScopeMarks Origin (lookupEnvelope selected ρ result).scope
  frame : ActiveMarking.Tree Origin
  forward : Transport (mark source address) (compile source ρ result)
    (binders.close (.par (.out1 (lookupOrigin selected address)) frame))
    ((lookupEnvelope selected ρ result).scope.close
      (par (out1 (.var ((lookupEnvelope selected ρ result).scope.inclusion .nm (ρ .nm name)))
        (.var (lookupEnvelope selected ρ result).returnName)) (lookupEnvelope selected ρ result).frame))
  backward : Transport
    (binders.close (.par (.out1 (lookupOrigin selected address)) frame))
    ((lookupEnvelope selected ρ result).scope.close
      (par (out1 (.var ((lookupEnvelope selected ρ result).scope.inclusion .nm (ρ .nm name)))
        (.var (lookupEnvelope selected ρ result).returnName)) (lookupEnvelope selected ρ result).frame))
    (mark source address) (compile source ρ result)

/-- The two transports are built from the source certificate's active
constructor recursion, including every pending call and stored declaration. -/
noncomputable def lookupMarks {Γ Δ : Ctx sig} {name : Var Γ Srt.nm}
    {value source target : Expr Srt.nm Γ}
    (selected : Environment.FetchCertificate name value source target)
    (address : List Edge) (ρ : Ren sig Γ Δ) (result : Var Δ .nm) :
    LookupMarks selected address ρ result := by
  induction selected generalizing Δ address with
  | here name value =>
      exact ⟨.nil, .nil, .parUnitBack _ _, .parUnit _ _⟩
  | app argument selected ih =>
      let inner := ih (.function :: address) (push ρ) .zero
      let boundary := lookupEnvelope selected (push ρ) .zero
      let extra := out2 (.var .zero) (.var (.succ (ρ .nm argument))) (.var (.succ result))
      let extraMarks : ActiveMarking.Tree Origin := .out2 ⟨.application, address⟩
      refine
        { binders := .bind ⟨.privateCall, address⟩ inner.binders
          frame := .par inner.frame extraMarks
          forward := ?_
          backward := ?_ }
      · exact .nu ⟨.privateCall, address⟩ (.trans (.par inner.forward (.refl extraMarks extra))
          (frame_forward inner.binders _ boundary.frame extra _ inner.frame extraMarks))
      · exact .nu ⟨.privateCall, address⟩ (.trans
          (frame_backward inner.binders _ boundary.frame extra _ inner.frame extraMarks)
          (.par inner.backward (.refl extraMarks extra)))
  | @defn Γ name value stored body body' selected ih =>
      let inner := ih (.definitionBody :: address) (liftRen ρ [Srt.nm]) (.succ result)
      let boundary := lookupEnvelope selected (liftRen ρ [Srt.nm]) (.succ result)
      let extra := rep (inp1 (.var .zero) (compile stored (push (push ρ)) .zero))
      let extraMarks : ActiveMarking.Tree Origin :=
        .rep (.inp1 ⟨.definition, address⟩ (mark stored (.definitionValue :: address)))
      refine
        { binders := .bind ⟨.privateReference, address⟩ inner.binders
          frame := .par inner.frame extraMarks
          forward := ?_
          backward := ?_ }
      · exact .nu ⟨.privateReference, address⟩ (.trans (.par inner.forward (.refl extraMarks extra))
          (frame_forward inner.binders _ boundary.frame extra _ inner.frame extraMarks))
      · exact .nu ⟨.privateReference, address⟩ (.trans
          (frame_backward inner.binders _ boundary.frame extra _ inner.frame extraMarks)
          (.par inner.backward (.refl extraMarks extra)))
  | carrier name value selected ih =>
      let inner := ih (.carrierBody :: address) ρ result
      let boundary := lookupEnvelope selected ρ result
      let extra := inp1 (.var (ρ .nm name)) (compile value (push ρ) .zero)
      let extraMarks : ActiveMarking.Tree Origin :=
        .inp1 ⟨.carrier, address⟩ (mark value (.carrierValue :: address))
      refine
        { binders := inner.binders
          frame := .par inner.frame extraMarks
          forward := ?_
          backward := ?_ }
      · exact .trans (.par inner.forward (.refl extraMarks extra))
          (frame_forward inner.binders _ boundary.frame extra _ inner.frame extraMarks)
      · exact .trans (frame_backward inner.binders _ boundary.frame extra _ inner.frame extraMarks)
          (.par inner.backward (.refl extraMarks extra))

def receiverMark (persistent : Bool) (origin : Origin) (guard : ActiveMarking.Tree Origin) :
    ActiveMarking.Tree Origin := if persistent then .rep (.inp1 origin guard) else .inp1 origin guard

structure UnaryMarks {Γ : Ctx sig} {source target : Proc Γ}
    (boundary : UnaryEnvelope source target) (sourceMarks : ActiveMarking.Tree Origin)
    (input output : Origin) where
  binders : ScopeMarks Origin boundary.scope
  guard : ActiveMarking.Tree Origin
  frame : ActiveMarking.Tree Origin
  forward : Transport sourceMarks source
    (binders.close (.par (.out1 output) (.par (receiverMark boundary.persistent input guard) frame)))
    (boundary.scope.close (par (out1 (.var boundary.channel) (.var boundary.datum))
      (par (if boundary.persistent then rep (inp1 (.var boundary.channel) boundary.guard)
        else inp1 (.var boundary.channel) boundary.guard) boundary.frame)))
  backward : Transport
    (binders.close (.par (.out1 output) (.par (receiverMark boundary.persistent input guard) frame)))
    (boundary.scope.close (par (out1 (.var boundary.channel) (.var boundary.datum))
      (par (if boundary.persistent then rep (inp1 (.var boundary.channel) boundary.guard)
        else inp1 (.var boundary.channel) boundary.guard) boundary.frame))) sourceMarks source

def UnaryMarks.parLeft {Γ : Ctx sig} {source target : Proc Γ}
    {boundary : UnaryEnvelope source target} {sourceMarks : ActiveMarking.Tree Origin} {input output : Origin}
    (marked : UnaryMarks boundary sourceMarks input output) (extra : Proc Γ)
    (extraMarks : ActiveMarking.Tree Origin) (noOutput : ActiveHeaderInvariant.visible .output1 extra = false) :
    UnaryMarks (boundary.parLeft extra noOutput) (.par sourceMarks extraMarks) input output where
  binders := marked.binders
  guard := marked.guard
  frame := .par marked.frame extraMarks
  forward := .trans (.par marked.forward (.refl extraMarks extra))
    (.trans (ActiveScopeTransport.par_forward marked.binders _ extra _ extraMarks)
      (ActiveScopeTransport.congr marked.binders (.trans (.parAssoc _ _ _ _ _ _)
        (.par (.refl _ _) (.parAssoc _ _ _ _ _ _)))))
  backward := .trans
    (ActiveScopeTransport.congr marked.binders (.trans
      (.par (.refl _ _) (.parAssocBack _ _ _ _ _ _)) (.parAssocBack _ _ _ _ _ _)))
    (.trans (ActiveScopeTransport.par_backward marked.binders _ extra _ extraMarks)
      (.par marked.backward (.refl extraMarks extra)))

def UnaryMarks.restrict {Γ : Ctx sig} {source target : Proc (Srt.nm :: Γ)}
    {boundary : UnaryEnvelope source target} {sourceMarks : ActiveMarking.Tree Origin} {input output : Origin}
    (marked : UnaryMarks boundary sourceMarks input output) (binder : Origin) :
    UnaryMarks boundary.restrict (.nu binder sourceMarks) input output where
  binders := .bind binder marked.binders
  guard := marked.guard
  frame := marked.frame
  forward := .nu binder marked.forward
  backward := .nu binder marked.backward

/-- The selected declaration's receiver mark and the request mark are moved
into the physical source envelope together with every pending context. -/
noncomputable def eventMarks {Γ Δ : Ctx sig} {kind : Environment.Action}
    {source target : Expr Srt.nm Γ} (event : Environment.EventCertificate kind source target)
    (nonBeta : kind ≠ .beta) (address : List Edge) (ρ : Ren sig Γ Δ) (result : Var Δ .nm) :
    UnaryMarks (eventEnvelope event nonBeta ρ result) (mark source address)
      (inputOrigin event address) (outputOrigin event address) := by
  induction event generalizing Δ address with
  | beta => exact False.elim (nonBeta rfl)
  | @carrierFetch Γ name value body body' selected =>
      let request := lookupEnvelope selected ρ result
      let selectedMarks := lookupMarks selected (.carrierBody :: address) ρ result
      let declaration := NamePassingEnvironment.listener value ρ (ρ .nm name)
      let declarationMarks : ActiveMarking.Tree Origin :=
        .inp1 ⟨.carrier, address⟩ (mark value (.carrierValue :: address))
      let environment : Ren sig Γ request.world := fun sort name => request.scope.inclusion sort (ρ sort name)
      have moved : rename request.scope.inclusion declaration =
          inp1 (.var (environment .nm name)) (compile value (push environment) .zero) :=
        NamePassingEnvironment.listener_target_rename value ρ request.scope.inclusion (ρ .nm name)
      refine
        { binders := selectedMarks.binders
          guard := mark value (.carrierValue :: address)
          frame := selectedMarks.frame
          forward := ?_
          backward := ?_ }
      · change Transport (.par (mark body (.carrierBody :: address)) declarationMarks)
          (par (compile body ρ result) declaration) _ _
        apply Transport.trans (.par selectedMarks.forward (.refl declarationMarks declaration))
        apply Transport.trans (ActiveScopeTransport.par_forward selectedMarks.binders _ declaration _ declarationMarks)
        rw [moved]
        exact ActiveScopeTransport.congr selectedMarks.binders (.trans (.parAssoc _ _ _ _ _ _)
          (.par (.refl _ _) (.parComm _ _ _ _)))
      · change Transport _ _ (.par (mark body (.carrierBody :: address)) declarationMarks)
          (par (compile body ρ result) declaration)
        change Transport (selectedMarks.binders.close
            (.par (.out1 (lookupOrigin selected (.carrierBody :: address)))
              (.par declarationMarks selectedMarks.frame)))
          (request.scope.close (par (out1 (.var (environment .nm name)) (.var request.returnName))
            (par (inp1 (.var (environment .nm name)) (compile value (push environment) .zero)) request.frame)))
          (.par (mark body (.carrierBody :: address)) declarationMarks) (par (compile body ρ result) declaration)
        rw [← moved]
        exact .trans (ActiveScopeTransport.congr selectedMarks.binders (.trans
          (.par (.refl _ _) (.parComm _ _ _ _)) (.parAssocBack _ _ _ _ _ _)))
          (.trans (ActiveScopeTransport.par_backward selectedMarks.binders _ declaration _ declarationMarks)
            (.par selectedMarks.backward (.refl declarationMarks declaration)))
  | @environmentFetch Γ value body body' selected =>
      let names : Ren sig (Srt.nm :: Γ) (Srt.nm :: Δ) := liftRen ρ [Srt.nm]
      let request := lookupEnvelope selected names (.succ result)
      let selectedMarks := lookupMarks selected (.definitionBody :: address) names (.succ result)
      let value' : Expr Srt.nm (Srt.nm :: Γ) := Mettapedia.Languages.LambdaCalculus.NamePassing.weaken value
      let server := NamePassingEnvironment.server value' names .zero
      let serverMarks : ActiveMarking.Tree Origin :=
        .rep (.inp1 ⟨.definition, address⟩ (mark value (.definitionValue :: address)))
      let environment : Ren sig (Srt.nm :: Γ) request.world :=
        fun sort name => request.scope.inclusion sort (names sort name)
      have actualServer : server = rep (inp1 (.var .zero) (compile value (push (push ρ)) .zero)) := by
        simp only [server, NamePassingEnvironment.server, NamePassingEnvironment.listener, value',
          Mettapedia.Languages.LambdaCalculus.NamePassing.weaken]
        rw [compile_source_rename]
        rfl
      have moved : rename request.scope.inclusion server =
          rep (inp1 (.var (environment .nm .zero)) (compile value' (push environment) .zero)) :=
        NamePassingEnvironment.server_target_rename value' names request.scope.inclusion .zero
      refine
        { binders := .bind ⟨.privateReference, address⟩ selectedMarks.binders
          guard := mark value (.definitionValue :: address)
          frame := selectedMarks.frame
          forward := ?_
          backward := ?_ }
      · change Transport (.nu ⟨.privateReference, address⟩
          (.par (mark body (.definitionBody :: address)) serverMarks))
          (nu (par (compile body names (.succ result)) _)) _ _
        rw [← actualServer]
        apply Transport.nu
        apply Transport.trans (.par selectedMarks.forward (.refl serverMarks server))
        apply Transport.trans (ActiveScopeTransport.par_forward selectedMarks.binders _ server _ serverMarks)
        rw [moved]
        exact ActiveScopeTransport.congr selectedMarks.binders (.trans (.parAssoc _ _ _ _ _ _)
          (.par (.refl _ _) (.parComm _ _ _ _)))
      · change Transport _ _ (.nu ⟨.privateReference, address⟩
          (.par (mark body (.definitionBody :: address)) serverMarks))
          (nu (par (compile body names (.succ result)) _))
        rw [← actualServer]
        apply Transport.nu
        change Transport (selectedMarks.binders.close
            (.par (.out1 (lookupOrigin selected (.definitionBody :: address)))
              (.par serverMarks selectedMarks.frame)))
          (request.scope.close (par (out1 (.var (environment .nm .zero)) (.var request.returnName))
            (par (rep (inp1 (.var (environment .nm .zero)) (compile value' (push environment) .zero))) request.frame)))
          (.par (mark body (.definitionBody :: address)) serverMarks)
          (par (compile body names (.succ result)) server)
        rw [← moved]
        exact .trans (ActiveScopeTransport.congr selectedMarks.binders (.trans
          (.par (.refl _ _) (.parComm _ _ _ _)) (.parAssocBack _ _ _ _ _ _)))
          (.trans (ActiveScopeTransport.par_backward selectedMarks.binders _ server _ serverMarks)
            (.par selectedMarks.backward (.refl serverMarks server)))
  | app argument event ih =>
      exact ((ih nonBeta (.function :: address) (push ρ) .zero).parLeft
        (out2 (.var .zero) (.var (.succ (ρ .nm argument))) (.var (.succ result)))
        (.out2 ⟨.application, address⟩) (by simp [out2, ActiveHeaderInvariant.visible])).restrict
        ⟨.privateCall, address⟩
  | defn value event ih =>
      exact ((ih nonBeta (.definitionBody :: address) (liftRen ρ [Srt.nm]) (.succ result)).parLeft
        (rep (inp1 (.var .zero) (compile value (push (push ρ)) .zero)))
        (.rep (.inp1 ⟨.definition, address⟩ (mark value (.definitionValue :: address))))
        (by simp [rep, inp1, ActiveHeaderInvariant.visible])).restrict ⟨.privateReference, address⟩
  | carrier name value event ih =>
      exact (ih nonBeta (.carrierBody :: address) ρ result).parLeft
        (inp1 (.var (ρ .nm name)) (compile value (push ρ) .zero))
        (.inp1 ⟨.carrier, address⟩ (mark value (.carrierValue :: address)))
        (by simp [inp1, ActiveHeaderInvariant.visible])

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingFetchMarking
