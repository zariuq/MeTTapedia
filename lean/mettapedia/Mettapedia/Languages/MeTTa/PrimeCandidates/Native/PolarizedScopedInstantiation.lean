import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Computation.PolarizedNeedParameterTransport
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ScopedEquationInstantiation
import Mettapedia.Languages.MeTTa.PrimeCandidates.Native.PolarizedConstraintExecution

/-!
# Per-use logical identities in actual polarized execution

The existing fresh-local/shared-capture map acts on symbolic heads and equation
effects before execution, including captured code, values and Need heaps.
Both raw and consistency-checked successors commute with this instantiation.
The caller supplies a distinct scope for each private activation; this is not
an allocation algorithm or an elaborator for dynamic equation expressions.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.Native.PolarizedScopedInstantiation

open Mettapedia.Machines.BranchLocalNeed NeedReference
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open PolarizedNeedMachine
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
open Mettapedia.Logic.LP

variable {signature : LPSignature.{0, 0, 0, 0}} {Private Shared O F N : Type} {m : Nat}

abbrev SourceTerm := ScopedEquationInstantiation.Source
  (signature := signature) (Private := Private) (Shared := Shared)
abbrev ActiveTerm := ScopedEquationInstantiation.Active
  (signature := signature) (Private := Private) (Shared := Shared)

def representation (scope : Nat) :=
  PolarizedNeedParameterMap.mapping (O := O) (F := F) (N := N) (m := m)
    (ScopedVariables.termAt (signature := signature) (Local := Private) (Shared := Shared) scope)
    (ScopedEquationInstantiation.equationAt (signature := signature) (Private := Private) (Shared := Shared) scope)

theorem store_map (scope : Nat) (initial : EquationStore (SourceTerm (signature := signature) (Private := Private) (Shared := Shared)))
    (machine : NeedMachine (SourceTerm (signature := signature) (Private := Private) (Shared := Shared)) O (Equation (SourceTerm (signature := signature) (Private := Private) (Shared := Shared))) F N m) :
    NeedConstraintEffects.equations (ScopedEquationInstantiation.storeAt scope initial)
      ((representation scope).mapMachine machine) =
      ScopedEquationInstantiation.storeAt scope (NeedConstraintEffects.equations initial machine) := by
  change ScopedEquationInstantiation.storeAt scope initial ++
      ((representation scope).mapWorld machine.world).receipts.effects =
    ScopedEquationInstantiation.storeAt scope (initial ++ machine.world.receipts.effects)
  rw [NeedRepresentation.Mapping.effects_map]
  simp only [ScopedEquationInstantiation.storeAt, List.map_append,
    representation, PolarizedNeedParameterMap.mapping]

theorem consistency_transport (scope : Nat) (initial : EquationStore (SourceTerm (signature := signature) (Private := Private) (Shared := Shared)))
    (machine : NeedMachine (SourceTerm (signature := signature) (Private := Private) (Shared := Shared)) O (Equation (SourceTerm (signature := signature) (Private := Private) (Shared := Shared))) F N m) :
    (FirstOrder.action (signature.withVars (ScopedVar Private ⊕ Shared))).Consistent
      (NeedConstraintEffects.equations (ScopedEquationInstantiation.storeAt scope initial)
        ((representation scope).mapMachine machine)) ↔
    (FirstOrder.action (signature.withVars (Private ⊕ Shared))).Consistent
      (NeedConstraintEffects.equations initial machine) := by
  rw [store_map, ScopedEquationInstantiation.consistent_iff]

theorem check_transport (scope : Nat) (initial : EquationStore (SourceTerm (signature := signature) (Private := Private) (Shared := Shared)))
    (checkSource : EquationStore (SourceTerm (signature := signature) (Private := Private) (Shared := Shared)) → Bool)
    (checkTarget : EquationStore (ActiveTerm (signature := signature) (Private := Private) (Shared := Shared)) → Bool)
    (sourceLaw : ∀ store, checkSource store = true ↔
      (FirstOrder.action (signature.withVars (Private ⊕ Shared))).Consistent store)
    (targetLaw : ∀ store, checkTarget store = true ↔
      (FirstOrder.action (signature.withVars (ScopedVar Private ⊕ Shared))).Consistent store)
    (machine : NeedMachine (SourceTerm (signature := signature) (Private := Private) (Shared := Shared)) O (Equation (SourceTerm (signature := signature) (Private := Private) (Shared := Shared))) F N m) :
    checkTarget (NeedConstraintEffects.equations (ScopedEquationInstantiation.storeAt scope initial)
      ((representation scope).mapMachine machine)) =
      checkSource (NeedConstraintEffects.equations initial machine) := by
  apply Bool.eq_iff_iff.mpr
  rw [targetLaw, sourceLaw, consistency_transport]

/-- Consistency admission commutes with actual fresh instantiation before
every source transition, including demand and cached-answer transitions. -/
theorem checked_step_map (scope : Nat) (initial : EquationStore (SourceTerm (signature := signature) (Private := Private) (Shared := Shared)))
    (source : O → Tm (SourceTerm (signature := signature) (Private := Private) (Shared := Shared)) m →
      Produced (Tm (SourceTerm (signature := signature) (Private := Private) (Shared := Shared)) m) F N)
    (target : O → Tm (ActiveTerm (signature := signature) (Private := Private) (Shared := Shared)) m →
      Produced (Tm (ActiveTerm (signature := signature) (Private := Private) (Shared := Shared)) m) F N)
    (primitives : ∀ operation argument, target operation (argument.mapHead (ScopedVariables.termAt scope)) =
      PolarizedNeedParameterMap.nativeOutcome (ScopedVariables.termAt scope) (source operation argument))
    (checkSource : EquationStore (SourceTerm (signature := signature) (Private := Private) (Shared := Shared)) → Bool)
    (checkTarget : EquationStore (ActiveTerm (signature := signature) (Private := Private) (Shared := Shared)) → Bool)
    (sourceLaw : ∀ store, checkSource store = true ↔
      (FirstOrder.action (signature.withVars (Private ⊕ Shared))).Consistent store)
    (targetLaw : ∀ store, checkTarget store = true ↔
      (FirstOrder.action (signature.withVars (ScopedVar Private ⊕ Shared))).Consistent store)
    (machine : NeedMachine (SourceTerm (signature := signature) (Private := Private) (Shared := Shared)) O (Equation (SourceTerm (signature := signature) (Private := Private) (Shared := Shared))) F N m) :
    ((PolarizedConstraintExecution.machine source initial checkSource).next machine).map
      (representation scope).mapMachine =
    (PolarizedConstraintExecution.machine target (ScopedEquationInstantiation.storeAt scope initial) checkTarget).next
      ((representation scope).mapMachine machine) := by
  change ((NeedLocalSteps.step (extension source) machine).filter
      (fun state => checkSource (NeedConstraintEffects.equations initial state))).map
        (representation scope).mapMachine =
    (NeedLocalSteps.step (extension target) ((representation scope).mapMachine machine)).filter
      (fun state => checkTarget (NeedConstraintEffects.equations (ScopedEquationInstantiation.storeAt scope initial) state))
  have steps := PolarizedNeedParameterMap.step_map (ScopedVariables.termAt scope)
    (ScopedEquationInstantiation.equationAt scope) source target primitives machine
  change (NeedLocalSteps.step (extension source) machine).map (representation scope).mapMachine =
    NeedLocalSteps.step (extension target) ((representation scope).mapMachine machine) at steps
  rw [← steps]
  rw [List.filter_map]
  congr 1
  apply List.filter_congr
  intro state member
  exact (check_transport scope initial checkSource checkTarget sourceLaw targetLaw state).symm

/-- Finite accepted executions retain exactly the same successor positions. -/
theorem checked_replay_map (scope : Nat) (initial : EquationStore (SourceTerm (signature := signature) (Private := Private) (Shared := Shared)))
    (source : O → Tm (SourceTerm (signature := signature) (Private := Private) (Shared := Shared)) m →
      Produced (Tm (SourceTerm (signature := signature) (Private := Private) (Shared := Shared)) m) F N)
    (target : O → Tm (ActiveTerm (signature := signature) (Private := Private) (Shared := Shared)) m →
      Produced (Tm (ActiveTerm (signature := signature) (Private := Private) (Shared := Shared)) m) F N)
    (primitives : ∀ operation argument, target operation (argument.mapHead (ScopedVariables.termAt scope)) =
      PolarizedNeedParameterMap.nativeOutcome (ScopedVariables.termAt scope) (source operation argument))
    (checkSource : EquationStore (SourceTerm (signature := signature) (Private := Private) (Shared := Shared)) → Bool)
    (checkTarget : EquationStore (ActiveTerm (signature := signature) (Private := Private) (Shared := Shared)) → Bool)
    (sourceLaw : ∀ store, checkSource store = true ↔
      (FirstOrder.action (signature.withVars (Private ⊕ Shared))).Consistent store)
    (targetLaw : ∀ store, checkTarget store = true ↔
      (FirstOrder.action (signature.withVars (ScopedVar Private ⊕ Shared))).Consistent store)
    (machine : NeedMachine (SourceTerm (signature := signature) (Private := Private) (Shared := Shared)) O
      (Equation (SourceTerm (signature := signature) (Private := Private) (Shared := Shared))) F N m)
    (trace : List Nat) :
    (PolarizedConstraintExecution.machine target (ScopedEquationInstantiation.storeAt scope initial) checkTarget).follow
      ((representation scope).mapMachine machine) trace =
    ((PolarizedConstraintExecution.machine source initial checkSource).follow machine trace).map
      (representation scope).mapMachine :=
  Mettapedia.GSLT.Causality.OccurrenceMachineHistory.follow_map _ _ _
    (fun state => (checked_step_map scope initial source target primitives checkSource checkTarget
      sourceLaw targetLaw state).symm) machine trace

/-- A checked instantiated execution also has an original checked execution. -/
theorem checked_replay_reflects (scope : Nat) (initial : EquationStore (SourceTerm (signature := signature) (Private := Private) (Shared := Shared)))
    (source : O → Tm (SourceTerm (signature := signature) (Private := Private) (Shared := Shared)) m →
      Produced (Tm (SourceTerm (signature := signature) (Private := Private) (Shared := Shared)) m) F N)
    (target : O → Tm (ActiveTerm (signature := signature) (Private := Private) (Shared := Shared)) m →
      Produced (Tm (ActiveTerm (signature := signature) (Private := Private) (Shared := Shared)) m) F N)
    (primitives : ∀ operation argument, target operation (argument.mapHead (ScopedVariables.termAt scope)) =
      PolarizedNeedParameterMap.nativeOutcome (ScopedVariables.termAt scope) (source operation argument))
    (checkSource : EquationStore (SourceTerm (signature := signature) (Private := Private) (Shared := Shared)) → Bool)
    (checkTarget : EquationStore (ActiveTerm (signature := signature) (Private := Private) (Shared := Shared)) → Bool)
    (sourceLaw : ∀ store, checkSource store = true ↔
      (FirstOrder.action (signature.withVars (Private ⊕ Shared))).Consistent store)
    (targetLaw : ∀ store, checkTarget store = true ↔
      (FirstOrder.action (signature.withVars (ScopedVar Private ⊕ Shared))).Consistent store)
    (machine : NeedMachine (SourceTerm (signature := signature) (Private := Private) (Shared := Shared)) O
      (Equation (SourceTerm (signature := signature) (Private := Private) (Shared := Shared))) F N m)
    (trace : List Nat)
    (endpoint : NeedMachine (ActiveTerm (signature := signature) (Private := Private) (Shared := Shared)) O
      (Equation (ActiveTerm (signature := signature) (Private := Private) (Shared := Shared))) F N m)
    (ran : (PolarizedConstraintExecution.machine target (ScopedEquationInstantiation.storeAt scope initial) checkTarget).follow
      ((representation scope).mapMachine machine) trace = some endpoint) :
    ∃ original, (PolarizedConstraintExecution.machine source initial checkSource).follow machine trace = some original ∧
      (representation scope).mapMachine original = endpoint :=
  Mettapedia.GSLT.Causality.OccurrenceMachineHistory.replay_reflects _ _ _
    (fun state => (checked_step_map scope initial source target primitives checkSource checkTarget
      sourceLaw targetLaw state).symm) ran

/-- Actual mapped effect histories use exactly the existing captured-variable
agreement condition when separately instantiated activations are combined. -/
theorem executed_family_consistent_iff [DecidableEq Private] [DecidableEq Shared]
    {n : Nat} (scopeOf : Fin n → Nat) (fresh : Function.Injective scopeOf)
    (worlds : Fin n → NeedWorld (SourceTerm (signature := signature) (Private := Private) (Shared := Shared)) O
      (Equation (SourceTerm (signature := signature) (Private := Private) (Shared := Shared))) F N m) :
    (FirstOrder.action (signature.withVars (ScopedVar Private ⊕ Shared))).Consistent
      ((List.finRange n).flatMap fun i => ((representation (O := O) (m := m) (scopeOf i)).mapWorld
        (worlds i)).receipts.effects) ↔
      ∃ family : Fin n → Subst (signature.withVars (ScopedVar Private ⊕ Shared)),
        (∀ i, ScopedSolutionGluing.Solves (family i) (scopeOf i) (worlds i).receipts.effects) ∧
        ∀ i j shared, family i (.inr shared) = family j (.inr shared) := by
  simp only [NeedRepresentation.Mapping.effects_map, representation, PolarizedNeedParameterMap.mapping]
  exact ScopedEquationInstantiation.family_consistent_iff scopeOf fresh (fun i => (worlds i).receipts.effects)

end Mettapedia.Languages.MeTTa.PrimeCandidates.Native.PolarizedScopedInstantiation
