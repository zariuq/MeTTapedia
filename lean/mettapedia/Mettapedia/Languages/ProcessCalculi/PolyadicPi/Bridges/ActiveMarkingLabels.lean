import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.ActiveMarking

/-!
# Relabeling actual active-prefix derivations

Constructor labels may carry several independent observations. Relabeling
preserves the supplied syntax, equations, prefix addresses and scopes; it
does not add or remove an active occurrence.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.ActiveMarkingLabels

open Mettapedia.OSLF.Binding
open Mettapedia.Languages.ProcessCalculi.PolyadicPi
open Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.ActiveMarking
open Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.ScopedActiveFrontier

universe u v w

def labels {Label : Type u} {Other : Type v} (map : Label → Other) : ActiveMarking.Tree Label → ActiveMarking.Tree Other
  | .var => .var
  | .nil => .nil
  | .par first second => .par (labels map first) (labels map second)
  | .inp1 origin body => .inp1 (map origin) (labels map body)
  | .inp2 origin body => .inp2 (map origin) (labels map body)
  | .out1 origin => .out1 (map origin)
  | .out2 origin => .out2 (map origin)
  | .nu origin body => .nu (map origin) (labels map body)
  | .rep body => .rep (labels map body)

theorem labels_comp {Label : Type u} {Other : Type v} {Final : Type w}
    (first : Label → Other) (second : Other → Final) (marked : ActiveMarking.Tree Label) :
    labels second (labels first marked) = labels (second ∘ first) marked := by
  induction marked <;> simp only [labels, Function.comp_apply, *]

theorem labels_id {Label : Type u} (marked : ActiveMarking.Tree Label) : labels id marked = marked := by
  induction marked <;> simp only [labels, id_eq, *]

theorem fits_labels {Label : Type u} {Other : Type v} (map : Label → Other)
    {Γ : Ctx sig} {marked : ActiveMarking.Tree Label} {process : Proc Γ} (fits : Fits marked process) :
    Fits (labels map marked) process := by
  induction fits with
  | var => exact .var _
  | nil => exact .nil
  | par _ _ leftIH rightIH => exact .par leftIH rightIH
  | inp1 origin channel _ ih => exact .inp1 (map origin) channel ih
  | inp2 origin channel _ ih => exact .inp2 (map origin) channel ih
  | out1 origin channel datum => exact .out1 (map origin) channel datum
  | out2 origin channel first second => exact .out2 (map origin) channel first second
  | nu origin _ ih => exact .nu (map origin) ih
  | rep _ ih => exact .rep ih

theorem fits_of_labels {Label : Type u} {Other : Type v} (map : Label → Other)
    {Γ : Ctx sig} (marked : ActiveMarking.Tree Label) {process : Proc Γ}
    (fits : Fits (labels map marked) process) : Fits marked process := by
  induction marked generalizing Γ with
  | var => cases fits with | var name => exact .var name
  | nil => cases fits with | nil => exact .nil
  | par first second leftIH rightIH => cases fits with
    | par firstFits secondFits => exact .par (leftIH firstFits) (rightIH secondFits)
  | inp1 origin body ih => cases fits with
    | inp1 _ channel bodyFits => exact .inp1 origin channel (ih bodyFits)
  | inp2 origin body ih => cases fits with
    | inp2 _ channel bodyFits => exact .inp2 origin channel (ih bodyFits)
  | out1 origin => cases fits with
    | out1 _ channel datum => exact .out1 origin channel datum
  | out2 origin => cases fits with
    | out2 _ channel first second => exact .out2 origin channel first second
  | nu origin body ih => cases fits with
    | nu _ bodyFits => exact .nu origin (ih bodyFits)
  | rep body ih => cases fits with
    | rep bodyFits => exact .rep (ih bodyFits)

theorem transport_labels {Label : Type u} {Other : Type v} (map : Label → Other)
    {Γ : Ctx sig} {before after : ActiveMarking.Tree Label} {source target : Proc Γ}
    (transport : Transport before source after target) :
    Transport (labels map before) source (labels map after) target := by
  induction transport with
  | refl => exact .refl _ _
  | trans _ _ leftIH rightIH => exact .trans leftIH rightIH
  | parComm => exact .parComm _ _ _ _
  | parAssoc => exact .parAssoc _ _ _ _ _ _
  | parAssocBack => exact .parAssocBack _ _ _ _ _ _
  | parUnit => exact .parUnit _ _
  | parUnitBack => exact .parUnitBack _ _
  | nuUnused => exact .nuUnused _ _ _
  | nuUnusedBack => exact .nuUnusedBack _ _ _
  | nuPar => exact .nuPar _ _ _ _ _
  | nuParBack => exact .nuParBack _ _ _ _ _
  | nuSwap => exact .nuSwap _ _ _ _
  | nuSwapBack => exact .nuSwapBack _ _ _ _
  | repUnfold => exact .repUnfold _ _
  | repFold => exact .repFold _ _ _
  | par _ _ leftIH rightIH => exact .par leftIH rightIH
  | nu origin _ ih => exact .nu (map origin) ih
  | inp1 origin channel _ ih => exact .inp1 (map origin) channel ih
  | inp2 origin channel _ ih => exact .inp2 (map origin) channel ih
  | rep _ ih => exact .rep ih

theorem transport_rename {Label : Type u} {Γ Δ : Ctx sig} (environment : Ren sig Γ Δ)
    {before after : ActiveMarking.Tree Label} {source target : Proc Γ}
    (transport : Transport before source after target) :
    Transport before (rename environment source) after (rename environment target) := by
  induction transport generalizing Δ with
  | refl => exact .refl _ _
  | trans _ _ leftIH rightIH => exact .trans (leftIH environment) (rightIH environment)
  | parComm => simpa only [rename_par] using Transport.parComm _ _ _ _
  | parAssoc => simpa only [rename_par] using Transport.parAssoc _ _ _ _ _ _
  | parAssocBack => simpa only [rename_par] using Transport.parAssocBack _ _ _ _ _ _
  | parUnit => simpa only [rename_par, nil, rename, renameArgs] using Transport.parUnit _ _
  | parUnitBack => simpa only [rename_par, nil, rename, renameArgs] using Transport.parUnitBack _ _
  | nuUnused origin marked process =>
      simp only [rename_nu]
      rw [rename_weaken (S := sig) (fresh := Srt.nm) environment process]
      exact .nuUnused origin marked _
  | nuUnusedBack origin marked process =>
      simp only [rename_nu]
      rw [rename_weaken (S := sig) (fresh := Srt.nm) environment process]
      exact .nuUnusedBack origin marked _
  | nuPar origin first second process frame =>
      simp only [rename_par, rename_nu]
      rw [rename_weaken (S := sig) (fresh := Srt.nm) environment frame]
      exact .nuPar origin first second _ _
  | nuParBack origin first second process frame =>
      simp only [rename_par, rename_nu]
      rw [rename_weaken (S := sig) (fresh := Srt.nm) environment frame]
      exact .nuParBack origin first second _ _
  | nuSwap outer inner marked process =>
      simp only [rename_nu, liftRen_two]
      rw [rename_exchange_lift environment Srt.nm Srt.nm process]
      exact .nuSwap outer inner marked _
  | nuSwapBack outer inner marked process =>
      simp only [rename_nu, liftRen_two]
      rw [rename_exchange_lift environment Srt.nm Srt.nm process]
      exact .nuSwapBack outer inner marked _
  | repUnfold => simpa only [rename_rep, rename_par] using Transport.repUnfold _ _
  | repFold => simpa only [rename_rep, rename_par] using Transport.repFold _ _ _
  | par _ _ leftIH rightIH => simpa only [rename_par] using Transport.par (leftIH environment) (rightIH environment)
  | nu origin _ ih => simpa only [rename_nu] using Transport.nu origin (ih (liftRen environment [.nm]))
  | inp1 origin channel _ ih =>
      simpa only [rename_inp1] using Transport.inp1 origin (rename environment channel) (ih (liftRen environment [.nm]))
  | inp2 origin channel _ ih =>
      simpa only [rename_inp2] using Transport.inp2 origin (rename environment channel) (ih (liftRen environment [.nm, .nm]))
  | rep _ ih => simpa only [rename_rep] using Transport.rep (ih environment)

def scopeLabels {Label : Type u} {Other : Type v} (map : Label → Other) :
    {Γ Δ : Ctx sig} → {scope : Scope Γ Δ} → ScopeMarks Label scope → ScopeMarks Other scope
  | _, _, _, .nil => .nil
  | _, _, _, .bind origin rest => .bind (map origin) (scopeLabels map rest)

theorem labels_scope {Label : Type u} {Other : Type v} (map : Label → Other)
    {Γ Δ : Ctx sig} {scope : Scope Γ Δ} (binders : ScopeMarks Label scope) (body : ActiveMarking.Tree Label) :
    labels map (binders.close body) = (scopeLabels map binders).close (labels map body) := by
  induction binders with
  | nil => rfl
  | bind origin rest ih => simpa only [ScopeMarks.close, labels, scopeLabels] using congrArg (ActiveMarking.Tree.nu (map origin)) ih

def communicationLabels {Label : Type u} {Other : Type v} (map : Label → Other) :
    {Γ : Ctx sig} → {redex reduct : Proc Γ} → {selected : ScopedCommunicationInversion.Communication redex reduct} →
    {marked : ActiveMarking.Tree Label} → MarkedCommunication selected marked → MarkedCommunication selected (labels map marked)
  | _, _, _, _, _, .unary channel datum body output input continuation fits =>
      .unary channel datum body (map output) (map input) (labels map continuation) (fits_labels map fits)
  | _, _, _, _, _, .binary channel first second body output input continuation fits =>
      .binary channel first second body (map output) (map input) (labels map continuation) (fits_labels map fits)

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.ActiveMarkingLabels
