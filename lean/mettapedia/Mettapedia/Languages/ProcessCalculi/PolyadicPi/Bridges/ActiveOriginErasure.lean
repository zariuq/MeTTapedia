import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.ActiveMarking

/-!
# Origin-selective erasure through guarded structural equations

Erasure follows actual marked prefix constructors and keeps replicated bodies
opaque. A copied single active prefix erases either to inaction or to its
original body, so the existing unfolding equation absorbs its erased copy.
The guard condition is invariant under the complete existing static relation,
including unused scope, extrusion, exchange and congruence under inputs.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.ActiveOriginErasure

open Mettapedia.OSLF.Binding
open Mettapedia.Languages.ProcessCalculi.PolyadicPi
open Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.ActiveMarking

universe u

def NoActiveRep : {Γ : Ctx sig} → Proc Γ → Prop
  | _, .var _ | _, .op .nil .nil => True
  | _, .op .par (.cons first (.cons second .nil)) => NoActiveRep first ∧ NoActiveRep second
  | _, .op .inp1 (.cons _ (.cons _ .nil)) | _, .op .inp2 (.cons _ (.cons _ .nil)) => True
  | _, .op .out1 (.cons _ (.cons _ .nil)) | _, .op .out2 (.cons _ (.cons _ (.cons _ .nil))) => True
  | _, .op .nu (.cons body .nil) => NoActiveRep body
  | _, .op .rep (.cons _ .nil) => False
termination_by _ process => termSize process
decreasing_by all_goals simp only [termSize, argsSize]; omega

/-- Input bodies are suspended. Variables, inputs and outputs each count as
one active leaf; restrictions retain their body's leaves. -/
def width : {Γ : Ctx sig} → Proc Γ → Nat
  | _, .var _ => 1
  | _, .op .nil .nil => 0
  | _, .op .par (.cons first (.cons second .nil)) => width first + width second
  | _, .op .inp1 (.cons _ (.cons _ .nil)) | _, .op .inp2 (.cons _ (.cons _ .nil)) => 1
  | _, .op .out1 (.cons _ (.cons _ .nil)) | _, .op .out2 (.cons _ (.cons _ (.cons _ .nil))) => 1
  | _, .op .nu (.cons body .nil) | _, .op .rep (.cons body .nil) => width body
termination_by _ process => termSize process
decreasing_by all_goals simp only [termSize, argsSize]; omega

theorem noActiveRep_rename : ∀ {Γ Δ : Ctx sig} (environment : Ren sig Γ Δ) (process : Proc Γ),
    NoActiveRep (rename environment process) ↔ NoActiveRep process
  | _, _, _, .var _ => by simp only [rename, NoActiveRep]
  | _, _, _, .op .nil .nil => by simp only [rename, renameArgs, NoActiveRep]
  | _, _, environment, .op .par (.cons first (.cons second .nil)) => by
      simp only [rename, renameArgs, liftRen, NoActiveRep]
      exact and_congr (noActiveRep_rename environment first) (noActiveRep_rename environment second)
  | _, _, _, .op .inp1 (.cons _ (.cons _ .nil)) => by simp only [rename, renameArgs, NoActiveRep]
  | _, _, _, .op .inp2 (.cons _ (.cons _ .nil)) => by simp only [rename, renameArgs, NoActiveRep]
  | _, _, _, .op .out1 (.cons _ (.cons _ .nil)) => by simp only [rename, renameArgs, NoActiveRep]
  | _, _, _, .op .out2 (.cons _ (.cons _ (.cons _ .nil))) => by simp only [rename, renameArgs, NoActiveRep]
  | _, _, environment, .op .nu (.cons body .nil) => by
      simp only [rename, renameArgs, NoActiveRep]
      exact noActiveRep_rename (liftRen environment [.nm]) body
  | _, _, _, .op .rep (.cons _ .nil) => by simp only [rename, renameArgs, NoActiveRep]
termination_by _ _ _ process => termSize process
decreasing_by all_goals simp only [termSize, argsSize]; omega

theorem width_rename : ∀ {Γ Δ : Ctx sig} (environment : Ren sig Γ Δ) (process : Proc Γ),
    width (rename environment process) = width process
  | _, _, _, .var _ => by simp only [rename, width]
  | _, _, _, .op .nil .nil => by simp only [rename, renameArgs, width]
  | _, _, environment, .op .par (.cons first (.cons second .nil)) => by
      simp only [rename, renameArgs, liftRen, width]
      rw [width_rename environment first, width_rename environment second]
  | _, _, _, .op .inp1 (.cons _ (.cons _ .nil)) => by simp only [rename, renameArgs, width]
  | _, _, _, .op .inp2 (.cons _ (.cons _ .nil)) => by simp only [rename, renameArgs, width]
  | _, _, _, .op .out1 (.cons _ (.cons _ .nil)) => by simp only [rename, renameArgs, width]
  | _, _, _, .op .out2 (.cons _ (.cons _ (.cons _ .nil))) => by simp only [rename, renameArgs, width]
  | _, _, environment, .op .nu (.cons body .nil) => by
      simp only [rename, renameArgs, width]
      exact width_rename (liftRen environment [.nm]) body
  | _, _, environment, .op .rep (.cons body .nil) => by
      simp only [rename, renameArgs, liftRen, width]
      exact width_rename environment body
termination_by _ _ _ process => termSize process
decreasing_by all_goals simp only [termSize, argsSize]; omega

theorem noActiveRep_structural {Γ : Ctx sig} {first second : Proc Γ}
    (equal : StructuralEq first second) : NoActiveRep first ↔ NoActiveRep second := by
  induction equal with
  | refl => rfl
  | symm _ ih => exact ih.symm
  | trans _ _ firstIH secondIH => exact firstIH.trans secondIH
  | parComm => simp only [par, NoActiveRep, and_comm]
  | parAssoc => simp only [par, NoActiveRep, and_assoc]
  | parUnit => simp only [par, nil, NoActiveRep, and_true]
  | nuUnused => simp only [nu, NoActiveRep, weaken, noActiveRep_rename]
  | nuPar => simp only [nu, par, NoActiveRep, weaken, noActiveRep_rename]
  | nuSwap => simp only [nu, NoActiveRep, noActiveRep_rename]
  | repUnfold => simp only [rep, par, NoActiveRep, and_false]
  | par _ _ firstIH secondIH => simpa only [par, NoActiveRep] using and_congr firstIH secondIH
  | nu _ ih => simpa only [nu, NoActiveRep] using ih
  | inp1 => simp only [inp1, NoActiveRep]
  | inp2 => simp only [inp2, NoActiveRep]
  | rep => simp only [rep, NoActiveRep]

theorem width_structural {Γ : Ctx sig} {first second : Proc Γ}
    (equal : StructuralEq first second) : NoActiveRep first → width first = width second := by
  induction equal with
  | refl => intro _; rfl
  | symm equal ih => intro safe; exact (ih ((noActiveRep_structural equal).mpr safe)).symm
  | trans first _ firstIH secondIH =>
      intro safe
      exact (firstIH safe).trans (secondIH ((noActiveRep_structural first).mp safe))
  | parComm => intro _; simp only [par, width, Nat.add_comm]
  | parAssoc => intro _; simp only [par, width, Nat.add_assoc]
  | parUnit => intro _; simp only [par, nil, width, Nat.add_zero]
  | nuUnused => intro _; simp only [nu, width, weaken, width_rename]
  | nuPar => intro _; simp only [nu, par, width, weaken, width_rename]
  | nuSwap => intro _; simp only [nu, width, width_rename]
  | repUnfold => intro impossible; simp only [rep, NoActiveRep] at impossible
  | par _ _ firstIH secondIH =>
      intro safe
      simp only [par, NoActiveRep] at safe
      simp only [par, width]
      rw [firstIH safe.1, secondIH safe.2]
  | nu _ ih =>
      intro safe
      simp only [nu, NoActiveRep] at safe
      simpa only [nu, width] using ih safe
  | inp1 => intro _; simp only [inp1, width]
  | inp2 => intro _; simp only [inp2, width]
  | rep => intro impossible; simp only [rep, NoActiveRep] at impossible

/-- Replicated active bodies are single leaves without active nested
replication. Guarded input continuations may contain arbitrary private scopes
and further persistent servers; they are not counted here. -/
def SingleBodies : {Γ : Ctx sig} → Proc Γ → Prop
  | _, .var _ | _, .op .nil .nil => True
  | _, .op .par (.cons first (.cons second .nil)) => SingleBodies first ∧ SingleBodies second
  | _, .op .inp1 (.cons _ (.cons _ .nil)) | _, .op .inp2 (.cons _ (.cons _ .nil)) => True
  | _, .op .out1 (.cons _ (.cons _ .nil)) | _, .op .out2 (.cons _ (.cons _ (.cons _ .nil))) => True
  | _, .op .nu (.cons body .nil) => SingleBodies body
  | _, .op .rep (.cons body .nil) => NoActiveRep body ∧ width body = 1
termination_by _ process => termSize process
decreasing_by all_goals simp only [termSize, argsSize]; omega

theorem singleBodies_of_noActiveRep : ∀ {Γ : Ctx sig} (process : Proc Γ),
    NoActiveRep process → SingleBodies process
  | _, .var _, _ => by simp only [SingleBodies]
  | _, .op .nil .nil, _ => by simp only [SingleBodies]
  | _, .op .par (.cons first (.cons second .nil)), safe => by
      simp only [NoActiveRep] at safe
      simp only [SingleBodies]
      exact ⟨singleBodies_of_noActiveRep first safe.1, singleBodies_of_noActiveRep second safe.2⟩
  | _, .op .inp1 (.cons _ (.cons _ .nil)), _ => by simp only [SingleBodies]
  | _, .op .inp2 (.cons _ (.cons _ .nil)), _ => by simp only [SingleBodies]
  | _, .op .out1 (.cons _ (.cons _ .nil)), _ => by simp only [SingleBodies]
  | _, .op .out2 (.cons _ (.cons _ (.cons _ .nil))), _ => by simp only [SingleBodies]
  | _, .op .nu (.cons body .nil), safe => by
      simp only [NoActiveRep] at safe
      simp only [SingleBodies]
      exact singleBodies_of_noActiveRep body safe
  | _, .op .rep (.cons _ .nil), impossible => by simp only [NoActiveRep] at impossible
termination_by _ process _ => termSize process
decreasing_by all_goals simp only [termSize, argsSize]; omega

theorem singleBodies_rename : ∀ {Γ Δ : Ctx sig} (environment : Ren sig Γ Δ) (process : Proc Γ),
    SingleBodies (rename environment process) ↔ SingleBodies process
  | _, _, _, .var _ => by simp only [rename, SingleBodies]
  | _, _, _, .op .nil .nil => by simp only [rename, renameArgs, SingleBodies]
  | _, _, environment, .op .par (.cons first (.cons second .nil)) => by
      simp only [rename, renameArgs, liftRen, SingleBodies]
      exact and_congr (singleBodies_rename environment first) (singleBodies_rename environment second)
  | _, _, _, .op .inp1 (.cons _ (.cons _ .nil)) => by simp only [rename, renameArgs, SingleBodies]
  | _, _, _, .op .inp2 (.cons _ (.cons _ .nil)) => by simp only [rename, renameArgs, SingleBodies]
  | _, _, _, .op .out1 (.cons _ (.cons _ .nil)) => by simp only [rename, renameArgs, SingleBodies]
  | _, _, _, .op .out2 (.cons _ (.cons _ (.cons _ .nil))) => by simp only [rename, renameArgs, SingleBodies]
  | _, _, environment, .op .nu (.cons body .nil) => by
      simp only [rename, renameArgs, SingleBodies]
      exact singleBodies_rename (liftRen environment [.nm]) body
  | _, _, environment, .op .rep (.cons body .nil) => by
      simp only [rename, renameArgs, liftRen, SingleBodies, noActiveRep_rename, width_rename]
termination_by _ _ _ process => termSize process
decreasing_by all_goals simp only [termSize, argsSize]; omega

theorem singleBodies_structural {Γ : Ctx sig} {first second : Proc Γ}
    (equal : StructuralEq first second) : SingleBodies first ↔ SingleBodies second := by
  induction equal with
  | refl => rfl
  | symm _ ih => exact ih.symm
  | trans _ _ firstIH secondIH => exact firstIH.trans secondIH
  | parComm => simp only [par, SingleBodies, and_comm]
  | parAssoc => simp only [par, SingleBodies, and_assoc]
  | parUnit => simp only [par, nil, SingleBodies, and_true]
  | nuUnused => simp only [nu, SingleBodies, weaken, singleBodies_rename]
  | nuPar => simp only [nu, par, SingleBodies, weaken, singleBodies_rename]
  | nuSwap => simp only [nu, SingleBodies, singleBodies_rename]
  | repUnfold process =>
      simp only [rep, par, SingleBodies]
      exact ⟨fun safe => ⟨singleBodies_of_noActiveRep process safe.1, safe⟩, And.right⟩
  | par _ _ firstIH secondIH => simpa only [par, SingleBodies] using and_congr firstIH secondIH
  | nu _ ih => simpa only [nu, SingleBodies] using ih
  | inp1 => simp only [inp1, SingleBodies]
  | inp2 => simp only [inp2, SingleBodies]
  | rep equal _ =>
      simp only [rep, SingleBodies]
      constructor
      · rintro ⟨safe, one⟩
        exact ⟨(noActiveRep_structural equal).mp safe, (width_structural equal safe).symm.trans one⟩
      · rintro ⟨safe, one⟩
        exact ⟨(noActiveRep_structural equal).mpr safe, (width_structural (.symm equal) safe).symm.trans one⟩

/-- Only active marked leaves are erased. In particular, erasure never
descends into a replicated body or a suspended input continuation. -/
def erase {Label : Type u} (selected : Label → Bool) :
    {Γ : Ctx sig} → ActiveMarking.Tree Label → Proc Γ → Proc Γ
  | _, _, .var name => .var name
  | _, _, .op .nil .nil => nil
  | _, marked, .op .par (.cons first (.cons second .nil)) => match marked with
      | .par left right => par (erase selected left first) (erase selected right second)
      | _ => par first second
  | _, marked, .op .inp1 (.cons channel (.cons body .nil)) => match marked with
      | .inp1 origin _ => if selected origin then nil else inp1 channel body
      | _ => inp1 channel body
  | _, marked, .op .inp2 (.cons channel (.cons body .nil)) => match marked with
      | .inp2 origin _ => if selected origin then nil else inp2 channel body
      | _ => inp2 channel body
  | _, marked, .op .out1 (.cons channel (.cons datum .nil)) => match marked with
      | .out1 origin => if selected origin then nil else out1 channel datum
      | _ => out1 channel datum
  | _, marked, .op .out2 (.cons channel (.cons first (.cons second .nil))) => match marked with
      | .out2 origin => if selected origin then nil else out2 channel first second
      | _ => out2 channel first second
  | _, marked, .op .nu (.cons body .nil) => match marked with
      | .nu _ inner => nu (erase selected inner body)
      | _ => nu body
  | _, _, .op .rep (.cons body .nil) => rep body
termination_by _ _ process => termSize process
decreasing_by all_goals simp only [termSize, argsSize]; omega

theorem erase_rename {Label : Type u} (selected : Label → Bool) :
    ∀ {Γ Δ : Ctx sig} (environment : Ren sig Γ Δ) (process : Proc Γ) (marked : ActiveMarking.Tree Label),
      erase selected marked (rename environment process) = rename environment (erase selected marked process)
  | _, _, _, .var _, _ => by simp only [rename, erase]
  | _, _, _, .op .nil .nil, _ => by simp only [rename, renameArgs, erase, nil]
  | _, _, environment, .op .par (.cons first (.cons second .nil)), marked => by
      cases marked <;> simp only [rename, renameArgs, liftRen, erase, par]
      rename_i left right
      rw [erase_rename selected environment first left, erase_rename selected environment second right]
  | _, _, environment, .op .inp1 (.cons channel (.cons body .nil)), marked => by
      cases marked <;> simp only [rename, renameArgs, erase, inp1]
      split <;> rfl
  | _, _, environment, .op .inp2 (.cons channel (.cons body .nil)), marked => by
      cases marked <;> simp only [rename, renameArgs, erase, inp2]
      split <;> rfl
  | _, _, environment, .op .out1 (.cons channel (.cons datum .nil)), marked => by
      cases marked <;> simp only [rename, renameArgs, erase, out1]
      split <;> rfl
  | _, _, environment, .op .out2 (.cons channel (.cons first (.cons second .nil))), marked => by
      cases marked <;> simp only [rename, renameArgs, erase, out2]
      split <;> rfl
  | _, _, environment, .op .nu (.cons body .nil), marked => by
      cases marked <;> simp only [rename, renameArgs, erase, nu]
      rename_i origin inner
      rw [erase_rename selected (liftRen environment [.nm]) body inner]
  | _, _, _, .op .rep (.cons _ .nil), _ => by simp only [rename, renameArgs, erase, rep]
termination_by _ _ _ process _ => termSize process
decreasing_by all_goals simp only [termSize, argsSize]; omega

private theorem zero_inactive : ∀ {Γ : Ctx sig} (process : Proc Γ),
    NoActiveRep process → width process = 0 → StructuralEq process nil
  | _, .var _, _, impossible => by simp only [width] at impossible; omega
  | _, .op .nil .nil, _, _ => .refl _
  | _, .op .par (.cons first (.cons second .nil)), safe, zero => by
      simp only [NoActiveRep] at safe
      simp only [width, Nat.add_eq_zero_iff] at zero
      exact .trans (.par (zero_inactive first safe.1 zero.1) (zero_inactive second safe.2 zero.2)) (.parUnit _)
  | _, .op .inp1 (.cons _ (.cons _ .nil)), _, impossible => by simp only [width] at impossible; omega
  | _, .op .inp2 (.cons _ (.cons _ .nil)), _, impossible => by simp only [width] at impossible; omega
  | _, .op .out1 (.cons _ (.cons _ .nil)), _, impossible => by simp only [width] at impossible; omega
  | _, .op .out2 (.cons _ (.cons _ (.cons _ .nil))), _, impossible => by simp only [width] at impossible; omega
  | _, .op .nu (.cons body .nil), safe, zero => by
      simp only [NoActiveRep] at safe
      simp only [width] at zero
      exact .trans (.nu (zero_inactive body safe zero)) (.nuUnused nil)
  | _, .op .rep (.cons _ .nil), impossible, _ => by simp only [NoActiveRep] at impossible
termination_by _ process _ _ => termSize process
decreasing_by all_goals simp only [termSize, argsSize]; omega

theorem erase_zero {Label : Type u} (selected : Label → Bool) {Γ : Ctx sig}
    {marked : ActiveMarking.Tree Label} {process : Proc Γ} (fitted : Fits marked process) :
    NoActiveRep process → width process = 0 → erase selected marked process = process := by
  induction fitted with
  | var => intro _ impossible; simp only [width] at impossible; omega
  | nil => intro _ _; simp only [nil, erase]
  | par _ _ firstIH secondIH =>
      intro safe zero
      simp only [par, NoActiveRep] at safe
      simp only [par, width, Nat.add_eq_zero_iff] at zero
      simp only [par, erase, firstIH safe.1 zero.1, secondIH safe.2 zero.2]
  | inp1 | inp2 | out1 | out2 => intro _ impossible; simp only [inp1, inp2, out1, out2, width] at impossible; omega
  | nu _ _ ih =>
      intro safe zero
      simp only [nu, NoActiveRep] at safe
      simp only [nu, width] at zero
      simpa only [nu, erase] using congrArg nu (ih safe zero)
  | rep => intro impossible _; simp only [rep, NoActiveRep] at impossible

theorem erase_single {Label : Type u} (selected : Label → Bool) {Γ : Ctx sig}
    {marked : ActiveMarking.Tree Label} {process : Proc Γ} (fitted : Fits marked process) :
    NoActiveRep process → width process = 1 →
      StructuralEq (erase selected marked process) nil ∨
        StructuralEq (erase selected marked process) process := by
  induction fitted with
  | var => intro _ _; simp only [erase]; exact .inr (.refl _)
  | nil => intro _ impossible; simp only [nil, width] at impossible; omega
  | @par Γ first second left right firstFits secondFits firstIH secondIH =>
      intro safe one
      simp only [par, NoActiveRep] at safe
      simp only [par, width] at one
      simp only [par, erase]
      by_cases empty : width first = 0
      · rw [erase_zero selected firstFits safe.1 empty]
        rcases secondIH safe.2 (by omega) with gone | kept
        · exact .inl (.trans (.par (zero_inactive first safe.1 empty) gone) (.parUnit _))
        · exact .inr (.par (.refl _) kept)
      · have otherEmpty : width second = 0 := by omega
        rw [erase_zero selected secondFits safe.2 otherEmpty]
        rcases firstIH safe.1 (by omega) with gone | kept
        · exact .inl (.trans (.par gone (zero_inactive second safe.2 otherEmpty)) (.parUnit _))
        · exact .inr (.par kept (.refl _))
  | inp1 | inp2 | out1 | out2 =>
      intro _ _
      simp only [inp1, inp2, out1, out2, erase]
      split
      · exact .inl (.refl _)
      · exact .inr (.refl _)
  | nu origin _ ih =>
      intro safe one
      simp only [nu, NoActiveRep] at safe
      simp only [nu, width] at one
      simp only [nu, erase]
      rcases ih safe one with gone | kept
      · exact .inl (.trans (.nu gone) (.nuUnused nil))
      · exact .inr (.nu kept)
  | rep => intro impossible _; simp only [rep, NoActiveRep] at impossible

/-- Static transport retains a valid marking at its supplied endpoint. -/
theorem fitted_target {Label : Type u} {Γ : Ctx sig}
    {before after : ActiveMarking.Tree Label} {first second : Proc Γ}
    (tracked : Transport before first after second) : Fits before first → Fits after second := by
  induction tracked with
  | refl => exact id
  | trans _ _ firstIH secondIH => exact fun fitted => secondIH (firstIH fitted)
  | parComm => intro fitted; cases fitted with | par first second => exact .par second first
  | parAssoc =>
      intro fitted; cases fitted with | par first third => cases first with
      | par first second => exact .par first (.par second third)
  | parAssocBack =>
      intro fitted; cases fitted with | par first later => cases later with
      | par second third => exact .par (.par first second) third
  | parUnit => intro fitted; cases fitted with | par first empty => exact first
  | parUnitBack => intro fitted; exact .par fitted .nil
  | nuUnused origin marked process =>
      intro fitted; cases fitted with
      | nu _ body => exact Fits.ofRename (fun _ name => .succ name) process marked body
  | nuUnusedBack origin marked process => intro fitted; exact .nu origin (fitted.rename _)
  | nuPar origin left right process frame =>
      intro fitted
      cases fitted with
      | par privateFits frameFits =>
          cases privateFits with
          | nu _ body =>
              have changed : Fits right (weaken (t := Srt.nm) frame) := frameFits.rename _
              exact .nu origin (.par body changed)
  | nuParBack origin first second process frame =>
      intro fitted; cases fitted with | nu _ inside => cases inside with
      | par body outer => exact .par (.nu origin body) (Fits.ofRename _ frame second outer)
  | nuSwap outer inner marked process =>
      intro fitted; cases fitted with | nu _ inside => cases inside with
      | nu _ body => exact .nu inner (.nu outer (body.rename _))
  | nuSwapBack outer inner marked process =>
      intro fitted; cases fitted with | nu _ inside => cases inside with
      | nu _ body => exact .nu outer (.nu inner (Fits.ofRename _ process marked body))
  | repUnfold => intro fitted; cases fitted with | rep body => exact .par body (.rep body)
  | repFold => intro fitted; cases fitted with | par copy server => exact server
  | par _ _ firstIH secondIH =>
      intro fitted; cases fitted with | par first second => exact .par (firstIH first) (secondIH second)
  | nu origin _ ih => intro fitted; cases fitted with | nu _ body => exact .nu origin (ih body)
  | inp1 origin channel _ ih => intro fitted; cases fitted with | inp1 _ _ body => exact .inp1 origin channel (ih body)
  | inp2 origin channel _ ih => intro fitted; cases fitted with | inp2 _ _ body => exact .inp2 origin channel (ih body)
  | rep _ ih => intro fitted; cases fitted with | rep body => exact .rep (ih body)

private theorem erased_copy_absorbed {Label : Type u} (selected : Label → Bool)
    {Γ : Ctx sig} {marked : ActiveMarking.Tree Label} {body : Proc Γ}
    (fitted : Fits marked body) (single : NoActiveRep body ∧ width body = 1) :
    StructuralEq (par (erase selected marked body) (rep body)) (rep body) := by
  rcases erase_single selected fitted single.1 single.2 with gone | kept
  · exact .trans (.par gone (.refl _)) (.trans (.parComm _ _) (.parUnit _))
  · exact .trans (.par kept (.refl _)) (.symm (.repUnfold _))

/-- Exact marked erasure respects every static generator. Replicated
copies are absorbed by their retained server rather than counted as consumed
server occurrences. No bijection of repeated input copies is assumed. -/
theorem erased_structural {Label : Type u} (selected : Label → Bool) {Γ : Ctx sig}
    {before after : ActiveMarking.Tree Label} {first second : Proc Γ}
    (tracked : Transport before first after second) :
    Fits before first → SingleBodies first →
      StructuralEq (erase selected before first) (erase selected after second) := by
  induction tracked with
  | refl => intro _ _; exact .refl _
  | trans first _ firstIH secondIH =>
      intro fitted good
      exact .trans (firstIH fitted good)
        (secondIH (fitted_target first fitted) ((singleBodies_structural first.erase).mp good))
  | parComm => intro _ _; simp only [par, erase]; exact .parComm _ _
  | parAssoc => intro _ _; simp only [par, erase]; exact .parAssoc _ _ _
  | parAssocBack => intro _ _; simp only [par, erase]; exact .symm (.parAssoc _ _ _)
  | parUnit => intro _ _; simp only [par, nil, erase]; exact .parUnit _
  | parUnitBack => intro _ _; simp only [par, nil, erase]; exact .symm (.parUnit _)
  | nuUnused => intro _ _; simp only [nu, erase, weaken, erase_rename]; exact .nuUnused _
  | nuUnusedBack => intro _ _; simp only [nu, erase, weaken, erase_rename]; exact .symm (.nuUnused _)
  | nuPar => intro _ _; simp only [par, nu, erase, weaken, erase_rename]; exact .nuPar _ _
  | nuParBack => intro _ _; simp only [par, nu, erase, weaken, erase_rename]; exact .symm (.nuPar _ _)
  | nuSwap => intro _ _; simp only [nu, erase, erase_rename]; exact .nuSwap _
  | nuSwapBack => intro _ _; simp only [nu, erase, erase_rename]; exact .symm (.nuSwap _)
  | repUnfold marked body =>
      intro fitted good
      cases fitted with
      | rep bodyFits =>
          simp only [rep, SingleBodies] at good
          simpa only [rep, par, erase] using (erased_copy_absorbed selected bodyFits good).symm
  | repFold copy server body =>
      intro fitted good
      cases fitted with
      | par copyFits serverFits =>
          simp only [par, rep, SingleBodies] at good
          simpa only [rep, par, erase] using erased_copy_absorbed selected copyFits good.2
  | par _ _ firstIH secondIH =>
      intro fitted good
      cases fitted with
      | par first second =>
          simp only [par, SingleBodies] at good
          simpa only [par, erase] using StructuralEq.par (firstIH first good.1) (secondIH second good.2)
  | nu origin _ ih =>
      intro fitted good
      cases fitted with
      | nu _ body =>
          simp only [nu, SingleBodies] at good
          simpa only [nu, erase] using StructuralEq.nu (ih body good)
  | inp1 origin channel inside _ =>
      intro _ _
      simp only [inp1, erase]
      split
      · exact .refl _
      · exact .inp1 channel inside.erase
  | inp2 origin channel inside _ =>
      intro _ _
      simp only [inp2, erase]
      split
      · exact .refl _
      · exact .inp2 channel inside.erase
  | rep inside _ => intro _ _; simp only [rep, erase]; exact .rep inside.erase

/-- Count the supplied active origins, retaining copied server marks. Input
continuations are suspended; only their enclosing active prefix contributes. -/
def originCount {Label : Type u} (selected : Label → Bool) : ActiveMarking.Tree Label → Nat
  | .var | .nil => 0
  | .par first second => originCount selected first + originCount selected second
  | .inp1 origin _ | .inp2 origin _ | .out1 origin | .out2 origin => if selected origin then 1 else 0
  | .nu _ body | .rep body => originCount selected body

/-- A genuine selected constructor contributes a counted active occurrence.
Suspended continuations do not supply such a witness. -/
theorem selection_positive {Label : Type u} (selected : Label → Bool)
    {header : ActiveHeaderInvariant.Header} {origin : Label} {marked : ActiveMarking.Tree Label}
    (chosen : ActiveMarking.Selection header origin marked) (active : selected origin = true) :
    0 < originCount selected marked := by
  induction chosen with
  | inp1 | inp2 | out1 | out2 => simp only [originCount, active, ite_true]; omega
  | left _ _ ih => have positive := ih active; simp only [originCount]; omega
  | right _ _ ih => have positive := ih active; simp only [originCount]; omega
  | nu _ _ ih | rep _ ih => simpa only [originCount] using ih active

/-- Selected origins have no active occurrence inside a replicated body. This
allows selected ordinary occurrences to be counted despite unrelated servers. -/
def RepFree {Label : Type u} (selected : Label → Bool) : ActiveMarking.Tree Label → Prop
  | .var | .nil | .inp1 _ _ | .inp2 _ _ | .out1 _ | .out2 _ => True
  | .par first second => RepFree selected first ∧ RepFree selected second
  | .nu _ body => RepFree selected body
  | .rep body => originCount selected body = 0

theorem originCount_zero_transport {Label : Type u} (selected : Label → Bool)
    {Γ : Ctx sig} {before after : ActiveMarking.Tree Label} {first second : Proc Γ}
    (tracked : Transport before first after second) :
    originCount selected before = 0 → originCount selected after = 0 := by
  induction tracked with
  | refl => exact id
  | trans _ _ firstIH secondIH => exact fun zero => secondIH (firstIH zero)
  | parComm => simp only [originCount, Nat.add_comm]; exact id
  | parAssoc => simp only [originCount, Nat.add_assoc]; exact id
  | parAssocBack => simp only [originCount, Nat.add_assoc]; exact id
  | parUnit => simp only [originCount, Nat.add_zero]; exact id
  | parUnitBack => simp only [originCount, Nat.add_zero]; exact id
  | nuUnused => simp only [originCount]; exact id
  | nuUnusedBack => simp only [originCount]; exact id
  | nuPar => simp only [originCount]; exact id
  | nuParBack => simp only [originCount]; exact id
  | nuSwap => simp only [originCount]; exact id
  | nuSwapBack => simp only [originCount]; exact id
  | repUnfold => simp only [originCount]; intro zero; omega
  | repFold => simp only [originCount]; intro zero; omega
  | par _ _ firstIH secondIH =>
      simp only [originCount]
      intro zero
      have firstZero := firstIH (by omega)
      have secondZero := secondIH (by omega)
      omega
  | nu _ _ ih => simpa only [originCount] using ih
  | inp1 => simp only [originCount]; exact id
  | inp2 => simp only [originCount]; exact id
  | rep _ ih => simpa only [originCount] using ih

theorem repFree_of_zero {Label : Type u} (selected : Label → Bool)
    (marked : ActiveMarking.Tree Label) : originCount selected marked = 0 → RepFree selected marked := by
  induction marked with
  | var | nil | inp1 | inp2 | out1 | out2 => intro _; trivial
  | par first second firstIH secondIH =>
      simp only [originCount, RepFree]
      intro zero
      exact ⟨firstIH (by omega), secondIH (by omega)⟩
  | nu _ _ ih => simpa only [originCount, RepFree] using ih
  | rep => simp only [originCount, RepFree]; exact id

theorem repFree_transport {Label : Type u} (selected : Label → Bool)
    {Γ : Ctx sig} {before after : ActiveMarking.Tree Label} {first second : Proc Γ}
    (tracked : Transport before first after second) : RepFree selected before → RepFree selected after := by
  induction tracked with
  | refl => exact id
  | trans _ _ firstIH secondIH => exact fun safe => secondIH (firstIH safe)
  | parComm => simp only [RepFree, and_comm]; exact id
  | parAssoc => simp only [RepFree, and_assoc]; exact id
  | parAssocBack => simp only [RepFree, and_assoc]; exact id
  | parUnit => simp only [RepFree, and_true]; exact id
  | parUnitBack => simp only [RepFree, and_true]; exact id
  | nuUnused => simp only [RepFree]; exact id
  | nuUnusedBack => simp only [RepFree]; exact id
  | nuPar => simp only [RepFree]; exact id
  | nuParBack => simp only [RepFree]; exact id
  | nuSwap => simp only [RepFree]; exact id
  | nuSwapBack => simp only [RepFree]; exact id
  | repUnfold marked _ =>
      simp only [RepFree]
      intro zero
      exact ⟨repFree_of_zero selected marked zero, zero⟩
  | repFold => simp only [RepFree]; exact And.right
  | par _ _ firstIH secondIH =>
      simp only [RepFree]
      exact fun safe => ⟨firstIH safe.1, secondIH safe.2⟩
  | nu _ _ ih => simpa only [RepFree] using ih
  | inp1 | inp2 => simp only [RepFree]; exact id
  | rep inside _ =>
      simpa only [RepFree] using originCount_zero_transport selected inside

/-- Static transport cannot create additional selected ordinary occurrences.
Contraction can discard an equal copy, so this is deliberately an inequality. -/
theorem originCount_le {Label : Type u} (selected : Label → Bool)
    {Γ : Ctx sig} {before after : ActiveMarking.Tree Label} {first second : Proc Γ}
    (tracked : Transport before first after second) :
    RepFree selected before → originCount selected after ≤ originCount selected before := by
  induction tracked with
  | refl => intro _; exact le_rfl
  | trans first _ firstIH secondIH =>
      intro safe
      exact (secondIH (repFree_transport selected first safe)).trans (firstIH safe)
  | parComm => intro _; simp only [originCount, Nat.add_comm, le_refl]
  | parAssoc => intro _; simp only [originCount, Nat.add_assoc, le_refl]
  | parAssocBack => intro _; simp only [originCount, Nat.add_assoc, le_refl]
  | parUnit => intro _; simp only [originCount, Nat.add_zero, le_refl]
  | parUnitBack => intro _; simp only [originCount, Nat.add_zero, le_refl]
  | nuUnused | nuUnusedBack | nuPar | nuParBack | nuSwap | nuSwapBack =>
      intro _; simp only [originCount, le_refl]
  | repUnfold => simp only [originCount, RepFree]; intro zero; omega
  | repFold => simp only [originCount]; intro _; omega
  | par _ _ firstIH secondIH =>
      simp only [originCount, RepFree]
      intro safe
      exact Nat.add_le_add (firstIH safe.1) (secondIH safe.2)
  | nu _ _ ih => simpa only [originCount, RepFree] using ih
  | inp1 | inp2 => intro _; simp only [originCount, le_refl]
  | rep inside _ =>
      simp only [originCount, RepFree]
      intro zero
      rw [originCount_zero_transport selected inside zero, zero]

/-- An origin-free frame is retained literally, including all suspended
bodies and servers. -/
theorem erase_of_originCount_zero {Label : Type u} (selected : Label → Bool)
    {Γ : Ctx sig} {marked : ActiveMarking.Tree Label} {process : Proc Γ}
    (fitted : Fits marked process) (zero : originCount selected marked = 0) :
    erase selected marked process = process := by
  induction fitted with
  | var => simp only [erase]
  | nil => simp only [nil, erase]
  | par _ _ firstIH secondIH =>
      simp only [originCount] at zero
      simp only [par, erase]
      rw [firstIH (by omega), secondIH (by omega)]
  | inp1 | inp2 | out1 | out2 =>
      simp only [originCount] at zero
      simp only [inp1, inp2, out1, out2, erase]
      split <;> simp_all
  | nu _ _ ih =>
      simp only [originCount] at zero
      simp only [nu, erase]
      rw [ih zero]
  | rep => simp only [rep, erase]

theorem originCount_scope {Label : Type u} (selected : Label → Bool) :
    ∀ {Γ Δ : Ctx sig} {scope : ScopedActiveFrontier.Scope Γ Δ}
      (binders : ScopeMarks Label scope) (marked : ActiveMarking.Tree Label),
      originCount selected (binders.close marked) = originCount selected marked
  | _, _, _, .nil, _ => rfl
  | _, _, _, .bind _ rest, marked => originCount_scope selected rest marked

theorem erase_scope {Label : Type u} (selected : Label → Bool) :
    ∀ {Γ Δ : Ctx sig} {scope : ScopedActiveFrontier.Scope Γ Δ}
      (binders : ScopeMarks Label scope) (marked : ActiveMarking.Tree Label) (body : Proc Δ),
      erase selected (binders.close marked) (scope.close body) =
        scope.close (erase selected marked body)
  | _, _, _, .nil, _, _ => rfl
  | _, _, _, .bind _ rest, marked, body => by
      simp only [ScopeMarks.close, ScopedActiveFrontier.Scope.close, nu, erase]
      rw [erase_scope selected rest marked body]

private theorem communication_erased {Label : Type u} (selected : Label → Bool)
    {Γ : Ctx sig} {redex reduct : Proc Γ}
    {communication : ScopedCommunicationInversion.Communication redex reduct}
    {marks : ActiveMarking.Tree Label} (chosen : MarkedCommunication communication marks)
    (input : selected chosen.inputOrigin = true) (output : selected chosen.outputOrigin = true) :
    erase selected marks redex = par nil nil := by
  cases chosen <;> simp_all only [MarkedCommunication.inputOrigin,
    MarkedCommunication.outputOrigin, par, out1, out2, inp1, inp2, erase, if_true]

private theorem communication_count {Label : Type u} (selected : Label → Bool)
    {Γ : Ctx sig} {redex reduct : Proc Γ}
    {communication : ScopedCommunicationInversion.Communication redex reduct}
    {marks : ActiveMarking.Tree Label} (chosen : MarkedCommunication communication marks)
    (input : selected chosen.inputOrigin = true) (output : selected chosen.outputOrigin = true) :
    originCount selected marks = 2 := by
  cases chosen <;> simp_all only [MarkedCommunication.inputOrigin,
    MarkedCommunication.outputOrigin, originCount, if_true]

/-- The actual pair's two selected origins contribute exactly their own
counts, independently of the continuation marking. -/
theorem marked_communication_count {Label : Type u} (selected : Label → Bool)
    {Γ : Ctx sig} {redex reduct : Proc Γ}
    {chosen : ScopedCommunicationInversion.Communication redex reduct}
    {marked : ActiveMarking.Tree Label} (communication : MarkedCommunication chosen marked) :
    originCount selected marked =
      (if selected communication.outputOrigin then 1 else 0) +
      (if selected communication.inputOrigin then 1 else 0) := by
  cases communication <;> rfl

/-- Erasing the selected communication in an arbitrary traced exposure
retains the exact erasure of its supplied residual and private telescope. -/
theorem erased_exposure_residual {Label : Type u} (selected : Label → Bool)
    {Γ : Ctx sig} {original : ActiveMarking.Tree Label} {source target : Proc Γ}
    {exposure : ScopedCommunicationInversion.Exposure source target}
    (fitted : Fits original source) (single : SingleBodies source)
    (traced : TracedExposure original exposure)
    (input : selected traced.continuation.inputOrigin = true)
    (output : selected traced.continuation.outputOrigin = true) :
    StructuralEq (erase selected original source)
      (exposure.scope.close (erase selected traced.frameMarks exposure.frame)) := by
  have transported := erased_structural selected traced.transport fitted single
  rw [erase_scope] at transported
  simp only [par, erase] at transported
  rw [communication_erased selected traced.continuation input output] at transported
  apply transported.trans
  apply exposure.scope.congr
  exact .trans (.par (.parUnit nil) (.refl _)) (.trans (.parComm _ _) (.parUnit _))

/-- Two selected ordinary origins exhaust the selected occurrences in the
actual redex. Thus its supplied residual contains none of them, even when
unrelated prefixes use the same channel or have identical syntax. -/
theorem ordinary_exposure_residual {Label : Type u} (selected : Label → Bool)
    {Γ : Ctx sig} {original : ActiveMarking.Tree Label} {source target : Proc Γ}
    {exposure : ScopedCommunicationInversion.Exposure source target}
    (fitted : Fits original source) (single : SingleBodies source)
    (traced : TracedExposure original exposure) (ordinary : RepFree selected original)
    (two : originCount selected original = 2)
    (input : selected traced.continuation.inputOrigin = true)
    (output : selected traced.continuation.outputOrigin = true) :
    originCount selected traced.frameMarks = 0 ∧
      StructuralEq (erase selected original source) (exposure.scope.close exposure.frame) := by
  have bound := originCount_le selected traced.transport ordinary
  rw [originCount_scope, originCount, communication_count selected traced.continuation input output,
    two] at bound
  have zero : originCount selected traced.frameMarks = 0 := by omega
  refine ⟨zero, ?_⟩
  have exactResidual := erased_exposure_residual selected fitted single traced input output
  rw [erase_of_originCount_zero selected traced.frameFits zero] at exactResidual
  exact exactResidual

/-- Each selected active leaf is an actual copy of the supplied retained
server body modulo the existing equations. Names under a private scope use
the ordinary weakening of that body; suspended continuations stay opaque. -/
def Absorbable {Label : Type u} (selected : Label → Bool) :
    {Γ : Ctx sig} → ActiveMarking.Tree Label → Proc Γ → Proc Γ → Prop
  | _, _, .var _, _ | _, _, .op .nil .nil, _ => True
  | _, marked, .op .par (.cons first (.cons second .nil)), body => match marked with
      | .par left right => Absorbable selected left first body ∧ Absorbable selected right second body
      | _ => True
  | _, marked, .op .inp1 (.cons channel (.cons continuation .nil)), body => match marked with
      | .inp1 origin _ => selected origin = true → StructuralEq (inp1 channel continuation) body
      | _ => True
  | _, marked, .op .inp2 (.cons channel (.cons continuation .nil)), body => match marked with
      | .inp2 origin _ => selected origin = true → StructuralEq (inp2 channel continuation) body
      | _ => True
  | _, marked, .op .out1 (.cons channel (.cons datum .nil)), body => match marked with
      | .out1 origin => selected origin = true → StructuralEq (out1 channel datum) body
      | _ => True
  | _, marked, .op .out2 (.cons channel (.cons first (.cons second .nil))), body => match marked with
      | .out2 origin => selected origin = true → StructuralEq (out2 channel first second) body
      | _ => True
  | Γ, marked, .op .nu (.cons process .nil), body => match marked with
      | .nu _ inner => Absorbable (Γ := Srt.nm :: Γ) selected inner process
          (Mettapedia.OSLF.Binding.weaken (S := sig) (Γ := Γ) (t := Srt.nm) body)
      | _ => True
  | _, _, .op .rep (.cons _ .nil), _ => True
termination_by _ _ process _ => termSize process
decreasing_by all_goals simp only [termSize, argsSize]; omega

private theorem exchange_frame {Γ : Ctx sig} (first second rest : Proc Γ) :
    StructuralEq (par first (par second rest)) (par second (par first rest)) :=
  .trans (.symm (.parAssoc _ _ _))
    (.trans (.par (.parComm _ _) (.refl _)) (.parAssoc _ _ _))

private theorem absorb_leaf {Γ : Ctx sig} {process body : Proc Γ}
    (copy : StructuralEq process body) :
    StructuralEq (par process (rep body)) (par nil (rep body)) :=
  .trans (.par copy (.refl _)) (.trans (.symm (.repUnfold _))
    (.symm (.trans (.parComm _ _) (.parUnit _))))

/-- Arbitrarily many erased copies are absorbed by one retained server.
The proof reuses that same occurrence; it never assumes that replication
itself is idempotent or duplicates the server. Private scopes are extruded by
the actual scope law, preserving their supplied binder indices. -/
theorem restore_with_server {Label : Type u} (selected : Label → Bool)
    {Γ : Ctx sig} {marked : ActiveMarking.Tree Label} {process : Proc Γ}
    (fitted : Fits marked process) : ∀ body : Proc Γ, Absorbable selected marked process body →
      StructuralEq (par process (rep body)) (par (erase selected marked process) (rep body)) := by
  induction fitted with
  | var => intro body _; simp only [erase]; exact .refl _
  | nil => intro body _; simp only [nil, erase]; exact .refl _
  | @par Γ first second left right _ _ firstIH secondIH =>
      intro body copied
      simp only [par, Absorbable] at copied
      simp only [par, erase]
      exact .trans (.parAssoc _ _ _)
        (.trans (.par (.refl _) (secondIH body copied.2))
          (.trans (exchange_frame _ _ _)
            (.trans (.par (.refl _) (firstIH body copied.1))
              (.trans (exchange_frame _ _ _) (.symm (.parAssoc _ _ _))))))
  | inp1 | inp2 | out1 | out2 =>
      intro body copied
      simp only [inp1, inp2, out1, out2, Absorbable] at copied
      simp only [inp1, inp2, out1, out2, erase]
      split
      · exact absorb_leaf (copied (by assumption))
      · exact .refl _
  | @nu Γ origin process inner _ ih =>
      intro body copied
      simp only [nu, Absorbable] at copied
      simp only [nu, erase]
      apply (StructuralEq.nuPar process (rep body)).trans
      apply StructuralEq.trans _ (.symm (StructuralEq.nuPar (erase selected inner process) (rep body)))
      have lifted : weaken (t := Srt.nm) (rep body) = rep (weaken (t := Srt.nm) body) := by
        simp only [weaken, rep, rename, renameArgs, liftRen]
        congr 2
      rw [lifted]
      exact StructuralEq.nu (ih (weaken (t := Srt.nm) body) copied)
  | rep => intro body _; simp only [rep, erase]; exact .refl _

/-- Finite copies formed with the existing parallel and inaction syntax. -/
def copies {Γ : Ctx sig} (body : Proc Γ) : Nat → Proc Γ
  | 0 => nil
  | count + 1 => par body (copies body count)

/-- Count actual erased prefixes, excluding the retained replicated body. -/
def removedCount {Label : Type u} (selected : Label → Bool) : ActiveMarking.Tree Label → Nat
  | .var | .nil | .rep _ => 0
  | .par first second => removedCount selected first + removedCount selected second
  | .inp1 origin _ | .inp2 origin _ | .out1 origin | .out2 origin => if selected origin then 1 else 0
  | .nu _ body => removedCount selected body

private theorem nil_left {Γ : Ctx sig} (process : Proc Γ) : StructuralEq (par nil process) process :=
  .trans (.parComm _ _) (.parUnit _)

theorem copies_add {Γ : Ctx sig} (body : Proc Γ) (first second : Nat) :
    StructuralEq (copies body (first + second)) (par (copies body first) (copies body second)) := by
  induction first with
  | zero => simpa only [Nat.zero_add, copies] using (nil_left (copies body second)).symm
  | succ first ih =>
      simp only [Nat.succ_add, copies]
      exact (StructuralEq.par (.refl _) ih).trans (.symm (.parAssoc _ _ _))

theorem copies_rename {Γ Δ : Ctx sig} (environment : Ren sig Γ Δ) (body : Proc Γ) (count : Nat) :
    rename environment (copies body count) = copies (rename environment body) count := by
  induction count with
  | zero => simp only [copies, nil, rename, renameArgs]
  | succ count ih => simp only [copies, rename_par, ih]

private theorem interchange {Γ : Ctx sig} (first second third fourth : Proc Γ) :
    StructuralEq (par (par first second) (par third fourth))
      (par (par first third) (par second fourth)) :=
  .trans (.parAssoc _ _ _) (.trans (.par (.refl _) (exchange_frame _ _ _)) (.symm (.parAssoc _ _ _)))

private theorem single_copy {Γ : Ctx sig} {process body : Proc Γ}
    (equal : StructuralEq process body) : StructuralEq process (par (copies body 1) nil) :=
  equal.trans (.symm ((StructuralEq.par (.parUnit _) (.refl _)).trans (.parUnit _)))

/-- The supplied process decomposes into its exact erased frame and a finite
number of actual copies. Copies under a scope are extruded with their
weakened body, so no used private name is collapsed. -/
theorem copies_decomposition {Label : Type u} (selected : Label → Bool)
    {Γ : Ctx sig} {marked : ActiveMarking.Tree Label} {process : Proc Γ}
    (fitted : Fits marked process) : ∀ body : Proc Γ, Absorbable selected marked process body →
      StructuralEq process (par (copies body (removedCount selected marked)) (erase selected marked process)) := by
  induction fitted with
  | var => intro body _; simp only [erase, removedCount, copies]; exact (nil_left _).symm
  | nil => intro body _; simp only [nil, erase, removedCount, copies]; exact (nil_left _).symm
  | @par Γ first second left right _ _ firstIH secondIH =>
      intro body copied
      simp only [par, Absorbable] at copied
      simp only [par, erase, removedCount]
      exact (StructuralEq.par (firstIH body copied.1) (secondIH body copied.2)).trans
        ((interchange _ _ _ _).trans (.par (copies_add body _ _).symm (.refl _)))
  | inp1 | inp2 | out1 | out2 =>
      intro body copied
      simp only [inp1, inp2, out1, out2, Absorbable] at copied
      simp only [inp1, inp2, out1, out2, erase, removedCount]
      split
      · exact single_copy (copied (by assumption))
      · simp only [copies]; exact (nil_left _).symm
  | @nu Γ origin process inner _ ih =>
      intro body copied
      simp only [nu, Absorbable] at copied
      simp only [nu, erase, removedCount]
      have first := StructuralEq.nu (ih (weaken (t := Srt.nm) body) copied)
      apply first.trans
      have reindexed : weaken (t := Srt.nm) (copies body (removedCount selected inner)) =
          copies (weaken (t := Srt.nm) body) (removedCount selected inner) :=
        copies_rename (fun _ name => (Var.succ name : Var (Srt.nm :: Γ) _)) body _
      rw [← reindexed]
      exact (StructuralEq.nu (.parComm _ _)).trans
        ((StructuralEq.nuPar (erase selected inner process) (copies body (removedCount selected inner))).symm.trans
          (.parComm _ _))
  | rep => intro body _; simp only [rep, erase, removedCount, copies]; exact (nil_left _).symm

theorem copies_server_absorbed {Γ : Ctx sig} (body : Proc Γ) (count : Nat) :
    StructuralEq (par (copies body count) (rep body)) (rep body) := by
  induction count with
  | zero => simpa only [copies] using nil_left (rep body)
  | succ count ih =>
      simp only [copies]
      exact (StructuralEq.parAssoc _ _ _).trans
        ((StructuralEq.par (.refl _) ih).trans (.symm (.repUnfold body)))

/-- A server already present in the erased residual absorbs every removed
copy. Unlike adding an extra server on both sides, this conclusion retains
exactly the supplied residual's existing server multiplicity. -/
theorem restore_in_existing_server_frame {Label : Type u} (selected : Label → Bool)
    {Γ : Ctx sig} {marked : ActiveMarking.Tree Label} {process : Proc Γ}
    (fitted : Fits marked process) (body : Proc Γ) (copied : Absorbable selected marked process body)
    (rest : Proc Γ) (server : StructuralEq (erase selected marked process) (par rest (rep body))) :
    StructuralEq process (erase selected marked process) := by
  exact (copies_decomposition selected fitted body copied).trans
    ((StructuralEq.par (.refl _) server).trans
      ((exchange_frame _ _ _).trans
        ((StructuralEq.par (.refl _) (copies_server_absorbed body _)).trans server.symm)))

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.ActiveOriginErasure
