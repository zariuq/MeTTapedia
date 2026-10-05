import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.MonadicProtocolSimulation
import Mettapedia.GSLT.Core.OperationalPathFibration

/-!
# The unary image is closed under actual execution

The unary subset is invariant under every stated structural equation and
every actual communication. Name-binder opening preserves this subset; no
substitution of arbitrary processes for free process variables is assumed.
Consequently all intermediate states of a supplied unary execution, including
changes of structural representative, remain unary.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.MonadicProtocol

open Mettapedia.OSLF.Binding
open Mettapedia.GSLT
open Mettapedia.GSLT.IndexedOperational
open Mettapedia.GSLT.Ultrainfinite
open Mettapedia.Languages.ProcessCalculi.PolyadicPi
open Mettapedia.Languages.ProcessCalculi.PolyadicPi.NativeTypes

/-- Reindexing names cannot conceal a binary constructor. -/
theorem unary_of_rename : ∀ {Γ Δ : Ctx sig} (ρ : Ren sig Γ Δ) (process : Proc Γ),
    Unary (rename ρ process) → Unary process
  | _, _, _, .var _ => fun _ => .var _
  | _, _, _, .op .nil .nil => fun _ => .nil
  | _, _, ρ, .op .par (.cons first (.cons second .nil)) => by
      intro unary
      change Unary (par (rename ρ first) (rename ρ second)) at unary
      cases unary with
      | par firstUnary secondUnary =>
          exact .par (unary_of_rename ρ first firstUnary)
            (unary_of_rename ρ second secondUnary)
  | _, _, ρ, .op .inp1 (.cons channel (.cons body .nil)) => by
      intro unary
      change Unary (inp1 (rename ρ channel) (rename (liftRen ρ [.nm]) body)) at unary
      cases unary with
      | inp1 channel unary => exact .inp1 _ (unary_of_rename (liftRen ρ [.nm]) body unary)
  | _, _, ρ, .op .inp2 (.cons channel (.cons body .nil)) => by
      intro unary
      change Unary (inp2 (rename ρ channel) (rename (liftRen ρ [.nm, .nm]) body)) at unary
      cases unary
  | _, _, _, .op .out1 (.cons _ (.cons _ .nil)) => fun _ => .out1 _ _
  | _, _, ρ, .op .out2 (.cons channel (.cons first (.cons second .nil))) => by
      intro unary
      change Unary (out2 (rename ρ channel) (rename ρ first) (rename ρ second)) at unary
      cases unary
  | _, _, ρ, .op .nu (.cons body .nil) => by
      intro unary
      change Unary (nu (rename (liftRen ρ [.nm]) body)) at unary
      cases unary with
      | nu unary => exact .nu (unary_of_rename (liftRen ρ [.nm]) body unary)
  | _, _, ρ, .op .rep (.cons process .nil) => by
      intro unary
      change Unary (rep (rename ρ process)) at unary
      cases unary with
      | rep unary => exact .rep (unary_of_rename ρ process unary)
termination_by _ _ _ process => termSize process
decreasing_by all_goals simp only [termSize, argsSize]; omega

theorem unary_rename_iff {Γ Δ : Ctx sig} (ρ : Ren sig Γ Δ) (process : Proc Γ) :
    Unary (rename ρ process) ↔ Unary process :=
  ⟨unary_of_rename ρ process, fun unary => unary.rename ρ⟩

theorem unary_weaken_iff {Γ : Ctx sig} {fresh : Srt} (process : Proc Γ) :
    Unary (weaken (t := fresh) process) ↔ Unary process :=
  unary_rename_iff (fun _ name => .succ name) process

theorem unary_par_iff {Γ : Ctx sig} (first second : Proc Γ) :
    Unary (par first second) ↔ Unary first ∧ Unary second := by
  constructor
  · intro unary
    cases unary with
    | par first second => exact ⟨first, second⟩
  · rintro ⟨first, second⟩
    exact .par first second

theorem unary_nu_iff {Γ : Ctx sig} (body : Proc (.nm :: Γ)) :
    Unary (nu body) ↔ Unary body := by
  constructor
  · intro unary
    cases unary with
    | nu unary => exact unary
  · exact Unary.nu

theorem unary_rep_iff {Γ : Ctx sig} (body : Proc Γ) :
    Unary (rep body) ↔ Unary body := by
  constructor
  · intro unary
    cases unary with
    | rep unary => exact unary
  · exact Unary.rep

theorem unary_inp1_iff {Γ : Ctx sig} (channel : Name Γ) (body : Proc (.nm :: Γ)) :
    Unary (inp1 channel body) ↔ Unary body := by
  constructor
  · intro unary
    cases unary with
    | inp1 channel unary => exact unary
  · exact Unary.inp1 channel

/-- In particular, scope extrusion and replication unfolding do not leave
the unary subset or hide a binary process within it. -/
theorem unary_structural_iff {Γ : Ctx sig} {first second : Proc Γ}
    (equal : StructuralEq first second) : Unary first ↔ Unary second := by
  induction equal with
  | refl => rfl
  | symm _ ih => exact ih.symm
  | trans _ _ firstIH secondIH => exact firstIH.trans secondIH
  | parComm => simp only [unary_par_iff]; exact and_comm
  | parAssoc => simp only [unary_par_iff]; exact and_assoc
  | parUnit =>
      simp only [unary_par_iff]
      exact ⟨fun both => both.1, fun unary => ⟨unary, .nil⟩⟩
  | nuUnused => exact (unary_nu_iff _).trans (unary_weaken_iff _)
  | nuPar =>
      simp only [unary_par_iff, unary_nu_iff, unary_weaken_iff]
  | nuSwap => simp only [unary_nu_iff, unary_rename_iff]
  | repUnfold =>
      simp only [unary_rep_iff, unary_par_iff]
      exact ⟨fun unary => ⟨unary, unary⟩, fun both => both.1⟩
  | par _ _ firstIH secondIH =>
      simp only [unary_par_iff]
      exact and_congr firstIH secondIH
  | nu _ ih => simpa only [unary_nu_iff] using ih
  | inp1 channel _ ih => simpa only [unary_inp1_iff] using ih
  | inp2 channel _ ih => constructor <;> intro unary <;> cases unary
  | rep _ ih => simpa only [unary_rep_iff] using ih

/-- Opening a name binder is reindexing by a name variable, so it preserves
all process constructors in the unary subset. -/
theorem unary_inst {Γ : Ctx sig} {body : Proc (.nm :: Γ)} (unary : Unary body)
    (datum : Name Γ) : Unary (inst body datum) := by
  cases datum with
  | op op args => cases op
  | var datum =>
      have opening : inst body (.var datum) = rename (nameRen datum) body := by
        unfold inst
        have environment : extend (Term.var datum) =
            (fun sort name => Term.var (nameRen datum sort name)) := by
          funext sort name
          cases name <;> rfl
        rw [environment, bind_var_eq_rename]
      rw [opening]
      exact unary.rename _

theorem unary_openPair {Γ : Ctx sig} {body : Proc (.nm :: .nm :: Γ)}
    (unary : Unary body) (first second : Name Γ) : Unary (openPair body first second) := by
  cases first with
  | op op args => cases op
  | var first =>
      cases second with
      | op op args => cases op
      | var second =>
          rw [openPair_variables]
          exact unary.rename _

/-- Actual steps from unary syntax cannot select the binary rule. -/
theorem unary_step {Γ : Ctx sig} {source target : Proc Γ}
    (step : Step source target) (unary : Unary source) : Unary target := by
  induction step with
  | comm1 channel datum body =>
      obtain ⟨_, input⟩ := (unary_par_iff _ _).mp unary
      exact unary_inst ((unary_inp1_iff _ _).mp input) datum
  | comm2 channel first second body =>
      obtain ⟨output, _⟩ := (unary_par_iff _ _).mp unary
      cases output
  | parL frame _ ih =>
      obtain ⟨active, frameUnary⟩ := (unary_par_iff _ _).mp unary
      exact .par (ih active) frameUnary
  | parR frame _ ih =>
      obtain ⟨frameUnary, active⟩ := (unary_par_iff _ _).mp unary
      exact .par frameUnary (ih active)
  | nu _ ih => exact .nu (ih ((unary_nu_iff _).mp unary))

/-- The invariant includes both structural changes around the actual firing. -/
theorem unary_stepModulo {Γ : Ctx sig} {source target : Proc Γ}
    (step : StepModulo source target) (unary : Unary source) : Unary target := by
  obtain ⟨redex, contractum, before, firing, after⟩ := step
  exact (unary_structural_iff after).mp
    (unary_step firing ((unary_structural_iff before).mp unary))

/-- Readout of every visited state of an existing retained rewrite path. -/
def rewritePathUnary {Γ : Ctx sig} : {source target : (operationalTheory Γ).Term} →
    (operationalTheory Γ).RewritePath source target → Prop
  | _, _, .nil state => Unary state
  | source, _, .cons _ rest => Unary source ∧ rewritePathUnary rest

theorem rewritePath_unary {Γ : Ctx sig} {source target : (operationalTheory Γ).Term}
    (path : (operationalTheory Γ).RewritePath source target) (unary : Unary source) :
    rewritePathUnary path := by
  induction path with
  | nil _ => exact unary
  | cons step rest ih => exact ⟨unary, ih (unary_stepModulo step unary)⟩

theorem rewritePath_unary_endpoint {Γ : Ctx sig} {source target : (operationalTheory Γ).Term}
    (path : (operationalTheory Γ).RewritePath source target) (unary : Unary source) :
    Unary target := by
  induction path with
  | nil _ => exact unary
  | cons step rest ih => exact ih (unary_stepModulo step unary)

/-- Readout of all states in the existing free execution category. -/
def executionPathUnary {Γ : Ctx sig} :
    {source target : (operationalTheory Γ).Term} →
    ExecutionPath (operationalTheory Γ) source target → Prop
  | _, _, .refl state => Unary state
  | source, _, .cons _ rest => Unary source ∧ executionPathUnary rest

theorem executionPath_unary {Γ : Ctx sig} {source target : (operationalTheory Γ).Term}
    (path : ExecutionPath (operationalTheory Γ) source target) (unary : Unary source) :
    executionPathUnary path := by
  induction path with
  | refl _ => exact unary
  | cons step rest ih => exact ⟨unary, ih (unary_stepModulo step.down unary)⟩

theorem executionPath_unary_endpoint {Γ : Ctx sig}
    {source target : (operationalTheory Γ).Term}
    (path : ExecutionPath (operationalTheory Γ) source target) (unary : Unary source) :
    Unary target := by
  induction path with
  | refl _ => exact unary
  | cons step rest ih => exact ih (unary_stepModulo step.down unary)

/-- This applies to every actual path from a lowered process, not merely to
the one selected for its forward simulation. -/
theorem lowered_executionPath_unary {Γ : Ctx sig} (process : Proc Γ)
    {target : (operationalTheory Γ).Term}
    (path : ExecutionPath (operationalTheory Γ) (lower process) target) :
    executionPathUnary path := executionPath_unary path (lower_unary process)

/-- A binary source call's actual four-phase protocol stays unary at every
intermediate state, with no condition on whether its two fields alias. -/
theorem lowerCallPath_unary {Γ : Ctx sig} (channel first second : Name Γ)
    (body : Proc (.nm :: .nm :: Γ)) :
    rewritePathUnary (lowerCallPath channel first second body) :=
  rewritePath_unary _ (lower_unary _)

/-- No actual execution from a unary process can reach a binary receiver,
even after arbitrary stated structural rearrangements. -/
theorem unary_cannot_reach_binary_input {Γ : Ctx sig} (source : Proc Γ)
    (unary : Unary source) (channel : Name Γ) (body : Proc (.nm :: .nm :: Γ)) :
    ¬ Nonempty (ExecutionPath (operationalTheory Γ) source (inp2 channel body)) := by
  rintro ⟨path⟩
  have impossible := executionPath_unary_endpoint path unary
  cases impossible

theorem unary_cannot_reach_binary_output {Γ : Ctx sig} (source : Proc Γ)
    (unary : Unary source) (channel first second : Name Γ) :
    ¬ Nonempty (ExecutionPath (operationalTheory Γ) source (out2 channel first second)) := by
  rintro ⟨path⟩
  have impossible := executionPath_unary_endpoint path unary
  cases impossible

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.MonadicProtocol
