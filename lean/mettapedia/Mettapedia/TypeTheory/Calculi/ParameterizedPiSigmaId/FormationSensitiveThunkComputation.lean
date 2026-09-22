import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.FormationSensitiveDependentComputation
import Mettapedia.TypeTheory.ContextualKleisliAdjunction
import Mettapedia.TypeTheory.ContextualThunkStrategy

/-!
# Suspended native dependent computations

A selected native index and its suspended continuation are first-class data
in the existing contextual effect semantics. The raw packet has no proof
fields. Forcing runs its body in the consumer's current world and pairs the
answer with the retained index. Independent qualification of the selected
index and every body result supplies native Sigma admission.

This is a semantic interface for delayed mathematical services, not an
object-language CBPV grammar or a classification of raw native terms as
normalized values. A program-valued suspension is not a memoized need cell.
The source, heap and machine contracts for such cells remain separate.
Substitution here reindexes native answers of semantic programs; it is not
substitution through a newly reified object-language thunk syntax.
-/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace FormationSensitive.ThunkComputation

open Mettapedia.GSLT.Dynamics.ContextualEffectHandlers
open Mettapedia.TypeTheory.ContextualDependentSequencing
open Mettapedia.TypeTheory.ContextualComputationKleisli.Program (bind_assoc)
open FormationSensitive.DependentComputation

open Mettapedia.TypeTheory

variable {Head State Intent : Type} {R : Rules Head} {n m : Nat}
variable {Γ : Ctx Head n} {Δ : Ctx Head m} {A : Tm Head n} {B : Tm Head (n + 1)}

/-- Executable suspended data: no native admission is stored in the packet. -/
structure RawThunk (Head State Intent : Type) (n : Nat) where
  index : Tm Head n
  body : Program State (Tm Head n) Intent

/-- Delay a continuation without running it. Effects in the index selection
still run when this outer program is observed. -/
def select (indices : Program State (Tm Head n) Intent)
    (next : Tm Head n → Program State (Tm Head n) Intent) :
    Program State (RawThunk Head State Intent n) Intent :=
  Program.map (fun index => ⟨index, next index⟩) indices

/-- Force the selected body and retain its actual native index in the result. -/
def force (packets : Program State (RawThunk Head State Intent n) Intent) :
    Program State (Tm Head n) Intent :=
  packets.bind fun packet => Program.map (Tm.pair packet.index) packet.body

/-- Delaying a selected continuation and then forcing it agrees with the
original indexed sequencing; the continuation is not run during packaging. -/
theorem force_select (indices : Program State (Tm Head n) Intent)
    (next : Tm Head n → Program State (Tm Head n) Intent) :
    force (select indices next) =
      indices.bind (fun index => Program.map (Tm.pair index) (next index)) := by
  unfold force select Program.map
  rw [bind_assoc]
  rfl

/-- Forcing preserves the selected world's state and branch, and appends the
body's deferred intents after the selection's intents. -/
theorem runWorldsAt_force (packets : Program State (RawThunk Head State Intent n) Intent)
    (state : State) (branch : BranchTrace) :
    runWorldsAt (force packets) state branch =
      (runWorldsAt packets state branch).flatMap fun prior =>
        (runWorldsAt prior.answer.body prior.state prior.branch).map fun suffix =>
          { branch := suffix.branch, answer := .pair prior.answer.index suffix.answer,
            state := suffix.state, intents := prior.intents ++ suffix.intents } := by
  rw [force, runWorldsAt_bind]
  simp only [runWorldsAt_map, List.map_map, Function.comp_def,
    WorldResult.prependIntents, WorldResult.mapAnswer]

/-- Qualification is separate from the executable packet. It retains the
actual selected native index in every continuation's result family. -/
structure Qualified (R : Rules Head) (Γ : Ctx Head n)
    (A : Tm Head n) (B : Tm Head (n + 1))
    (packet : RawThunk Head State Intent n) : Prop where
  indexTyping : Typing R Γ packet.index A
  bodyTyping : ∀ (state : State) (branch : BranchTrace)
    (output : WorldResult State (Tm Head n) Intent),
    output ∈ runWorldsAt packet.body state branch →
      Typing R Γ output.answer (inst0 packet.index B)

/-- Native pair admission is derived from independently formed Sigma data,
the selected packet's index, and its actual continuation result. -/
theorem force_result_judgment {u : Head}
    (formed : Judgment R Γ (.sigma A B) (.head u)) (universeWitness : R.isUniverse u)
    (packets : Program State (RawThunk Head State Intent n) Intent)
    (state : State) (branch : BranchTrace)
    (qualified : ∀ prior ∈ runWorldsAt packets state branch, Qualified R Γ A B prior.answer)
    (output : WorldResult State (Tm Head n) Intent)
    (retained : output ∈ runWorldsAt (force packets) state branch) :
    Judgment R Γ output.answer (.sigma A B) := by
  rw [runWorldsAt_force] at retained
  obtain ⟨prior, priorMember, bodyMember⟩ := List.mem_flatMap.mp retained
  obtain ⟨suffix, suffixMember, equality⟩ := List.mem_map.mp bodyMember
  subst output
  exact ⟨formed.context, .pairIntro formed.typing universeWitness
    (qualified prior priorMember).indexTyping
    ((qualified prior priorMember).bodyTyping _ _ suffix suffixMember)⟩

namespace RawThunk

/-- Substitution changes the stored native index and each future native
answer, not the computation's state, choices or deferred intents. -/
def substitute (σ : Sub Head n m) (packet : RawThunk Head State Intent n) :
    RawThunk Head State Intent m :=
  ⟨subst σ packet.index, Program.map (subst σ) packet.body⟩

end RawThunk

/-- Capture-avoiding substitution commutes with delayed native pair use. -/
theorem substitute_force (σ : Sub Head n m)
    (packets : Program State (RawThunk Head State Intent n) Intent) :
    Program.map (subst σ) (force packets) =
      force (Program.map (RawThunk.substitute σ) packets) := by
  unfold force RawThunk.substitute Program.map
  simp only [bind_assoc, Program.pure_bind]
  rfl

/-- A typed native substitution transports both the stored index and the
future answer family. No equality of raw index tags substitutes for this law. -/
theorem Qualified.substitute {σ : Sub Head n m} (typed : CtxMor R Γ Δ σ)
    {packet : RawThunk Head State Intent n} (qualified : Qualified R Γ A B packet) :
    Qualified R Δ (subst σ A) (subst (liftSub σ) B) (packet.substitute σ) := by
  refine ⟨qualified.indexTyping.substitute typed, ?_⟩
  intro state branch output member
  rw [RawThunk.substitute, runWorldsAt_map] at member
  obtain ⟨prior, priorMember, equality⟩ := List.mem_map.mp member
  subst output
  have result := (qualified.bodyTyping state branch prior priorMember).substitute typed
  rw [subst_inst0] at result
  exact result

/-- Raw native forcing is the same sequencing operation induced by the
value/computation adjunction, instantiated at executable packet data. -/
theorem force_is_induced_sequencing
    (packets : Program State (RawThunk Head State Intent n) Intent) :
    (ContextualKleisliAdjunction.inducedMonad State Intent).μ.app (Tm Head n)
      ((ContextualKleisliAdjunction.inducedMonad State Intent).map
        (_root_.TypeCat.ofHom fun packet : RawThunk Head State Intent n =>
          Program.map (Tm.pair packet.index) packet.body) packets) = force packets :=
  ContextualKleisliAdjunction.inducedMonad_bind State Intent packets _

/-! ## Erasure from admitted mathematical services -/

/-- A suspended service whose answer type retains its selected native index. -/
abbrev AdmittedThunk (R : Rules Head) (Γ : Ctx Head n)
    (A : Tm Head n) (B : Tm Head (n + 1)) (State Intent : Type) :=
  (first : TypedValue R Γ A) × Program State (TypedValue R Γ (inst0 first.val B)) Intent

/-- Forget the service's logical witnesses without changing executable data. -/
def erase (packet : AdmittedThunk R Γ A B State Intent) :
    RawThunk Head State Intent n :=
  ⟨packet.1.val, Program.map Subtype.val packet.2⟩

/-- Use the existing dependent force interface and the native pair rule. -/
def forceAdmitted {u : Head}
    (formed : Judgment R Γ (.sigma A B) (.head u)) (universeWitness : R.isUniverse u)
    (packets : Program State (AdmittedThunk R Γ A B State Intent) Intent) :
    Program State (TypedValue R Γ (.sigma A B)) Intent :=
  Program.map (fun value => sigmaPair formed universeWitness value.1 value.2)
    (ContextualThunkStrategy.forceSelected packets)

/-- The native and contextual dependent interfaces agree on delayed services. -/
theorem forceAdmitted_delaySelected {u : Head}
    (formed : Judgment R Γ (.sigma A B) (.head u)) (universeWitness : R.isUniverse u)
    (indices : Program State (TypedValue R Γ A) Intent)
    (next : (first : TypedValue R Γ A) →
      Program State (TypedValue R Γ (inst0 first.val B)) Intent) :
    forceAdmitted formed universeWitness (ContextualThunkStrategy.delaySelected indices next) =
      sigmaProgram formed universeWitness indices next := by
  rw [forceAdmitted, ContextualThunkStrategy.forceSelected_delaySelected]
  rfl

/-- Erasing the native evidence before execution produces exactly the same
raw program as erasing the admitted result afterwards. -/
theorem erase_forceAdmitted {u : Head}
    (formed : Judgment R Γ (.sigma A B) (.head u)) (universeWitness : R.isUniverse u)
    (packets : Program State (AdmittedThunk R Γ A B State Intent) Intent) :
    Program.map Subtype.val (forceAdmitted formed universeWitness packets) =
      force (Program.map erase packets) := by
  unfold forceAdmitted ContextualThunkStrategy.forceSelected force erase Program.map
  simp only [bind_assoc, Program.pure_bind]
  rfl

/-- Independently admitted service answers qualify the raw delayed body. -/
theorem erase_qualified (packet : AdmittedThunk R Γ A B State Intent) :
    Qualified R Γ A B (erase packet) := by
  refine ⟨packet.1.property.typing, ?_⟩
  intro state branch output member
  change output ∈ runWorldsAt (Program.map Subtype.val packet.2) state branch at member
  rw [runWorldsAt_map] at member
  obtain ⟨prior, _, equality⟩ := List.mem_map.mp member
  subst output
  exact prior.answer.property.typing

/-- The raw data returned by a program of admitted delayed services inherits
qualification without making the raw packet itself proof-carrying. -/
theorem erased_packets_qualified
    (packets : Program State (AdmittedThunk R Γ A B State Intent) Intent)
    (state : State) (branch : BranchTrace)
    (output : WorldResult State (RawThunk Head State Intent n) Intent)
    (member : output ∈ runWorldsAt (Program.map erase packets) state branch) :
    Qualified R Γ A B output.answer := by
  rw [runWorldsAt_map] at member
  obtain ⟨prior, _, equality⟩ := List.mem_map.mp member
  subst output
  exact erase_qualified prior.answer

/-! ## A native dependent proof, delayed across a state change -/


#print axioms force_select
#print axioms runWorldsAt_force
#print axioms force_result_judgment
#print axioms substitute_force
#print axioms Qualified.substitute
#print axioms force_is_induced_sequencing
#print axioms forceAdmitted_delaySelected
#print axioms erase_forceAdmitted
#print axioms erase_qualified
#print axioms erased_packets_qualified

end FormationSensitive.ThunkComputation
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
