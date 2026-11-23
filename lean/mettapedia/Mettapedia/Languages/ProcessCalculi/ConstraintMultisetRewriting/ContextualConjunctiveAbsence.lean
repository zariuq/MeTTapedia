import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualConjunctiveQueries
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualFrameWorklist
import Mathlib.Data.Finset.Pi
import Mathlib.Data.Fintype.Basic

/-!
# Certified absence of a conjunction over every physical candidate tuple

The candidate product is constructed from the occupied occurrences, with
repetition allowed for read ports. Acceptance requires a certified worklist
refutation of every joint problem. Residual equations and exhausted fuel
never stand for a refutation. The check returns no query or caller binding.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualConjunctiveAbsence

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualConjunctiveQueries

universe u
variable {S : Signature} {Query Local Shared : Type} {O : Type u}
  (queries : Query → MetaArity S) (locals : Local → MetaArity S) (captures : Shared → MetaArity S)

def releaseUniv {count : Nat} (chosen : ∀ port ∈ (Finset.univ : Finset (Fin count)), O) : Fin count → O :=
  fun port => chosen port (Finset.mem_univ port)

theorem releaseUniv_injective {count : Nat} : Function.Injective (releaseUniv (O := O) (count := count)) := by
  intro first second same
  funext port member
  exact congrFun same port

def candidates [DecidableEq O] (world : Finset O) (count : Nat) : Finset (Fin count → O) :=
  ((Finset.univ : Finset (Fin count)).pi fun _ => world).map ⟨releaseUniv, releaseUniv_injective⟩

theorem mem_candidates [DecidableEq O] (world : Finset O) {count : Nat} (chosen : Fin count → O) :
    chosen ∈ candidates world count ↔ ∀ port, chosen port ∈ world := by
  rw [candidates, Finset.mem_map]
  constructor
  · rintro ⟨tuple, member, rfl⟩ port
    exact (Finset.mem_pi.mp member) port (Finset.mem_univ port)
  · intro member
    exact ⟨fun port _ => chosen port, Finset.mem_pi.mpr (fun port _ => member port), rfl⟩

def Holds {Next : Type} {next : Next → MetaArity S} (candidate : Assignment captures next)
    {Γ : Ctx S} {sort : S.Srt}
    (patterns : List (Term (signature S (queryFamily queries captures)) Γ sort))
    (rows : O → ContextualStoredRows.Row locals captures Γ sort) (world : Finset O) : Prop :=
  ∀ chosen : Fin patterns.length → O, (∀ port, chosen port ∈ world) →
    ¬ ContextualConjunctiveQueries.Matches queries locals captures candidate patterns rows chosen

def Ask {Γ : Ctx S} {sort : S.Srt}
    (problem : EquationStore (Term (signature S captures) Γ sort))
    (patterns : List (Term (signature S (queryFamily queries captures)) Γ sort))
    (rows : O → ContextualStoredRows.Row locals captures Γ sort) (world : Finset O) : Prop :=
  ∀ (Next : Type) (next : Next → MetaArity S) (candidate : Assignment captures next),
    ContextualFrameUnifier.Models candidate problem → Holds queries locals captures candidate patterns rows world

variable [DecidableEq Query] [DecidableEq Local] [DecidableEq Shared] [DecidableEq S.Srt]
  [∀ sort, DecidableEq (S.Op sort)]

def certifiesTuple (fuel : Nat) {Γ : Ctx S} {sort : S.Srt}
    (problem : EquationStore (Term (signature S captures) Γ sort))
    (patterns : List (Term (signature S (queryFamily queries captures)) Γ sort))
    (rows : O → ContextualStoredRows.Row locals captures Γ sort) (chosen : Fin patterns.length → O) : Bool :=
  match ContextualFrameWorklist.run fuel (family queries locals captures)
      (ContextualResidual.observeProblem (joint queries locals captures problem patterns rows chosen)) with
  | .refuted _ => true
  | .residual _ => false

theorem certifiesTuple_sound (fuel : Nat) {Next : Type} (next : Next → MetaArity S)
    (candidate : Assignment captures next) {Γ : Ctx S} {sort : S.Srt}
    (problem : EquationStore (Term (signature S captures) Γ sort))
    (patterns : List (Term (signature S (queryFamily queries captures)) Γ sort))
    (rows : O → ContextualStoredRows.Row locals captures Γ sort) (chosen : Fin patterns.length → O)
    (accepted : certifiesTuple queries locals captures fuel problem patterns rows chosen = true)
    (solved : ContextualFrameUnifier.Models candidate problem) :
    ¬ ContextualConjunctiveQueries.Matches queries locals captures candidate patterns rows chosen := by
  intro matched
  cases computed : ContextualFrameWorklist.run fuel (family queries locals captures)
      (ContextualResidual.observeProblem (joint queries locals captures problem patterns rows chosen)) with
  | residual update => simp only [certifiesTuple, computed, Bool.false_eq_true] at accepted
  | refuted impossible =>
      obtain ⟨Later, later, combined, models⟩ :=
        match_gives_joint_model queries locals captures candidate problem patterns rows chosen solved matched
      exact impossible later combined ((ContextualResidual.models_observeProblem combined _).mpr models)

def certifies [DecidableEq O] (fuel : Nat) {Γ : Ctx S} {sort : S.Srt}
    (problem : EquationStore (Term (signature S captures) Γ sort))
    (patterns : List (Term (signature S (queryFamily queries captures)) Γ sort))
    (rows : O → ContextualStoredRows.Row locals captures Γ sort) (world : Finset O) : Bool :=
  decide (∀ chosen ∈ candidates world patterns.length,
    certifiesTuple queries locals captures fuel problem patterns rows chosen = true)

theorem certifies_sound [DecidableEq O] (fuel : Nat) {Γ : Ctx S} {sort : S.Srt}
    (problem : EquationStore (Term (signature S captures) Γ sort))
    (patterns : List (Term (signature S (queryFamily queries captures)) Γ sort))
    (rows : O → ContextualStoredRows.Row locals captures Γ sort) (world : Finset O)
    (accepted : certifies queries locals captures fuel problem patterns rows world = true) :
    Ask queries locals captures problem patterns rows world := by
  intro Next next candidate solved chosen present
  have each := of_decide_eq_true accepted
  exact certifiesTuple_sound queries locals captures fuel next candidate problem patterns rows chosen
    (each chosen ((mem_candidates world chosen).mpr present)) solved

theorem zero_fuel_is_not_a_tuple_refutation {Γ : Ctx S} {sort : S.Srt}
    (problem : EquationStore (Term (signature S captures) Γ sort))
    (patterns : List (Term (signature S (queryFamily queries captures)) Γ sort))
    (rows : O → ContextualStoredRows.Row locals captures Γ sort) (chosen : Fin patterns.length → O) :
    certifiesTuple queries locals captures 0 problem patterns rows chosen = false := rfl

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualConjunctiveAbsence
