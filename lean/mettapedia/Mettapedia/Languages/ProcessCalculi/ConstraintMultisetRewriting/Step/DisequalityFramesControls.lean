import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.DisequalityFramesInstances
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.DependentFullIndependenceControls

/-!
# Disequations at dependent frames and at declaration frames: controls

## The dependent full step (`DependentTell`)

At `triple` (`X : U0, x : X, g : Ground`), with no knowledge and no rows:
* telling `X ≠ Ground → Ground` is admitted (`tellApart_admitted`): `X ↦ Ground` separates it;
* **after it, telling `X ≐ Ground → Ground` is refused** (`identify_refused`), although the same tell is
  admitted at the state without the disequation (`identify_admitted_without`);
* **after it, telling `X ≐ Ground` is admitted** (`compatible_admitted`).

## The helper step at declaration frames (`ContextualTell`)

From the empty frame, the helper firing that makes the helper `H` valued `7` is admitted; its result
lives at the frame with `H`. A helper firing tells only the value of its own fresh helper, so it never
constrains an older name (`ContextualDiamond`); the identifying firing therefore comes first here:
* **after `H ≐ 7`, a firing that tells `H ≠ 7` is refused** (`apartSeven_refused`);
* **a firing that tells `H ≠ 8` is admitted** (`apartEight_admitted`), with a solution into the empty
  frame that values `H` by `7`.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DisequalityFrames

open Interface (Frames)

/-! ## The dependent full step -/

namespace DependentTell

open _root_.CategoryTheory
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open TypedEquality TypedEquality.Normalization TypedContextual
open Interface.DependentFull
open Interface.DependentFull.Controls
open Interface.DependentFull.IndependenceControls
open MeTTaCalculus.OccurrenceCommits (Enabled fire)

abbrev X := ContextualDependentEta.frames setting.levels
abbrev Q := (Dependent.prestep setting.levels Nat).step
abbrev P := Dependent.withDisequations setting.levels Nat

/-- The state at `triple` with no knowledge, no rows and no disequations. -/
def start : Q.DState := Q.plain (stateAt [] ∅)

/-- The firing that takes, reads, makes and tells nothing. -/
def quiet : Plain setting.levels Nat triple := ⟨[], [], [], [], [], [], [], []⟩

/-- The disequation `X ≠ Ground → Ground`. -/
def apart : Equation (TotalTerm triple) := (xUniverse, arrowUniverse)

/-- `X ↦ Ground` separates it. -/
theorem toGround_separates : Separates X (a := triple) (b := point) toGround [apart] := by
  intro d member equated
  obtain rfl := List.mem_singleton.mp member
  exact ground_apart toGround equated ((X.equivalence point).symm toGround_solves)

/-- **Tell `X ≠ Ground → Ground`.** -/
def tellApart : Q.DFiring start :=
  ⟨Plain.toFiring (s := stateAt [] ∅) quiet, [apart],
    (separates_id_iff _).mpr ⟨point, toGround, toGround_separates⟩⟩

/-- A firing without helpers that takes, reads and makes nothing is enabled at every state. -/
theorem enabled_empty {s : State Tower.rules Nat} (f : Plain setting.levels Nat s.frame)
    (taken : ∀ o, o ∉ f.taken) (read : ∀ o, o ∉ f.read) (made : ∀ o, o ∉ f.made) :
    Enabled (fun _ : Nat => ()) s.present ((Plain.toFiring f).selection.commit (T := Unit)) :=
  (enabled_iff (Plain.toFiring f)).mpr
    ⟨fun o member => absurd member (taken o), fun o member => absurd member (read o),
      fun o member => absurd member (taken o), fun o member => absurd member (made o)⟩

theorem tellApart_admitted : P.Admits tellApart := by
  refine (Interface.Step.admits_iff_separating _ tellApart).mpr
    ⟨⟨List.nodup_nil, List.nodup_nil, rfl, rfl, fun _ member => absurd member List.not_mem_nil⟩,
      enabled_empty (s := stateAt [] ∅) quiet (fun _ => List.not_mem_nil) (fun _ => List.not_mem_nil)
        (fun _ => List.not_mem_nil), ⟨point, toGround, ?_, toGround_separates⟩, ?_⟩
  · intro e member
    have empty : Q.information tellApart.base = [] := rfl
    rw [empty] at member
    exact absurd member List.not_mem_nil
  · intro _ _ _ _
    exact ⟨Frames.models_nil _, fun _ member => absurd member List.not_mem_nil⟩

/-- The state after the disequation. -/
def told : Q.DState := P.result tellApart tellApart_admitted

/-- **Tell `X ≐ Ground → Ground` after the disequation.** -/
def identify : Q.DFiring told :=
  Interface.Step.DFiring.silent told (Plain.toFiring (s := told.state) tellArrow)
    (Dependent.toFiring_reflects (s := told.state) tellArrow)

/-- **The disequation refuses the identifying tell.** -/
theorem identify_refused : ¬ P.Admits identify := by
  intro admitted
  obtain ⟨-, -, ⟨b, g, solved, separated⟩, -⟩ := (Interface.Step.admits_iff_separating _ identify).mp admitted
  have equated : X.E (X.act g xUniverse) (X.act g arrowUniverse) :=
    solved (xUniverse, arrowUniverse) (List.mem_append_right _ (List.mem_singleton_self _))
  apply separated _ (List.mem_append_left _ (List.mem_singleton_self _))
  show X.E (X.act g (X.act _ (X.act _ xUniverse))) (X.act g (X.act _ (X.act _ arrowUniverse)))
  erw [X.act_id, X.act_id, X.act_id, X.act_id]
  exact equated

/-- **Without the disequation, the same tell is admitted.** -/
def identifyWithout : Q.DFiring start :=
  Interface.Step.DFiring.silent start (Plain.toFiring (s := stateAt [] ∅) tellArrow)
    (Dependent.toFiring_reflects (s := stateAt [] ∅) tellArrow)

theorem identify_admitted_without : P.Admits identifyWithout := by
  refine (Interface.Step.admits_iff_separating _ identifyWithout).mpr
    ⟨⟨List.nodup_nil, List.nodup_nil, rfl, rfl, fun _ member => absurd member List.not_mem_nil⟩,
      enabled_empty (s := stateAt [] ∅) tellArrow (fun _ => List.not_mem_nil) (fun _ => List.not_mem_nil)
        (fun _ => List.not_mem_nil), ⟨point, toArrow, ?_, ?_⟩, ?_⟩
  · intro e member
    have single : Q.information identifyWithout.base = [(xUniverse, arrowUniverse)] := rfl
    rw [single] at member
    obtain rfl := List.mem_singleton.mp member
    exact toArrow_solves
  · intro d member
    have empty : Q.carried start identifyWithout.base ++ identifyWithout.tells = [] := rfl
    rw [empty] at member
    exact absurd member List.not_mem_nil
  · intro _ _ _ _
    exact ⟨Frames.models_nil _, fun _ member => absurd member List.not_mem_nil⟩

/-- **Tell `X ≐ Ground` after the disequation.** -/
def compatible : Q.DFiring told :=
  Interface.Step.DFiring.silent told (Plain.toFiring (s := told.state) tellGround)
    (Dependent.toFiring_reflects (s := told.state) tellGround)

/-- **A compatible tell is admitted**: `X ↦ Ground` solves it and keeps `X` apart from
`Ground → Ground`. -/
theorem compatible_admitted : P.Admits compatible := by
  refine (Interface.Step.admits_iff_separating _ compatible).mpr
    ⟨⟨List.nodup_nil, List.nodup_nil, rfl, rfl, fun _ member => absurd member List.not_mem_nil⟩,
      enabled_empty (s := told.state) tellGround (fun _ => List.not_mem_nil) (fun _ => List.not_mem_nil)
        (fun _ => List.not_mem_nil), ⟨point, toGround, ?_, ?_⟩, ?_⟩
  · intro e member
    have single : Q.information compatible.base = [(xUniverse, groundUniverse)] := rfl
    rw [single] at member
    obtain rfl := List.mem_singleton.mp member
    exact toGround_solves
  · intro d member equated
    rcases List.mem_append.mp member with carried | none
    · obtain rfl := List.mem_singleton.mp carried
      change X.E (X.act toGround (X.act _ (X.act _ xUniverse)))
        (X.act toGround (X.act _ (X.act _ arrowUniverse))) at equated
      erw [X.act_id, X.act_id, X.act_id, X.act_id] at equated
      exact toGround_separates _ (List.mem_singleton_self _) equated
    · exact absurd none List.not_mem_nil
  · intro _ _ _ _
    exact ⟨Frames.models_nil _, fun _ member => absurd member List.not_mem_nil⟩

/-- **The dependent control**: a told disequation refuses a later identifying firing, which it alone
refuses, and admits a compatible one. -/
theorem control :
    P.Admits tellApart ∧ ¬ P.Admits identify ∧ P.Admits identifyWithout ∧ P.Admits compatible :=
  ⟨tellApart_admitted, identify_refused, identify_admitted_without, compatible_admitted⟩

end DependentTell

/-! ## The helper step at declaration frames -/

namespace ContextualTell

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open Interface.Helpers (helperStep extend incl fresh)
open Interface.Helpers.Consumer (tiny constant empty start first)

abbrev X := Frames.contextual tiny
abbrev Q := (Contextual.prestep tiny Nat).step
abbrev P := Contextual.withDisequations tiny Nat

/-- The empty frame, with no disequations. -/
def start' : Q.DState := Q.plain start

/-- The helper firing that makes occurrence `1` and the helper `H` valued `7`. -/
def makeHelper : Q.DFiring start' := Interface.Step.DFiring.ofBase start' first rfl

theorem first_admitted : helperStep.Admits first := by
  obtain ⟨admitted, -⟩ := Interface.Helpers.Consumer.independent
  exact admitted

theorem makeHelper_admitted : P.Admits makeHelper :=
  (Interface.Step.conservative _ makeHelper rfl rfl).mpr first_admitted

/-- The state after it: the frame with `H`, and the knowledge `H ≐ 7`. -/
def valued : Q.DState := P.result makeHelper makeHelper_admitted

/-- A helper firing at that state: occurrence `2` and a helper `K` valued `0`. -/
def next : Interface.Helpers.Firing valued.state := ⟨2, ([], ()), constant 0, []⟩

/-- The two names of the frame after both helpers. -/
abbrev both := extend (extend empty ([], ())) ([], ())

/-- `H` read at that frame. -/
def helperH : Observation tiny both.arity := observe (generator both.arity (.inl (.inr ())))

/-- An observation of a constant. -/
def constantAt (n : Nat) : Observation tiny both.arity := observe (constant (Γ := []) n)

/-- The constant an observation is headed by, if any. -/
def head {V : Type} {declaration : V → MetaArity tiny} : Observation tiny declaration → Option Nat
  | ⟨_, _, .op (.inl n) _⟩ => some n
  | _ => none

theorem helperH_head : head helperH = none := rfl

theorem constantAt_head (n : Nat) : head (constantAt n) = some n := rfl

theorem helperH_ne (n : Nat) : helperH ≠ constantAt n := by
  intro same
  have heads := congrArg head same
  rw [helperH_head, constantAt_head] at heads
  exact absurd heads (by simp)

/-- **The helper's tell `H ≐ 7`, read at the frame after both helpers.** -/
theorem tell_read :
    ((Frames.contextual tiny).act (a := extend empty ([], ())) (b := both)
        (incl (extend empty ([], ())) ([], ())) first.tell.1,
      (Frames.contextual tiny).act (a := extend empty ([], ())) (b := both)
        (incl (extend empty ([], ())) ([], ())) first.tell.2) =
      (helperH, constantAt 7) := by
  refine Prod.ext ?_ rfl
  show observe (instantiate (incl (extend empty ([], ())) ([], ()))
    (generator (extend empty ([], ())).arity (.inr ()))) = helperH
  rw [instantiate_generator]
  rfl

/-- `H ≠ n`, at the frame after both helpers. -/
def apartFrom (n : Nat) : Q.DFiring valued :=
  ⟨next, [(helperH, constantAt n)], by
    refine (separates_id_iff_apart _).mpr fun d member => ?_
    have only : d = (helperH, constantAt n) := List.mem_singleton.mp member
    rw [only]
    exact helperH_ne n⟩

/-- `H ≐ 7` read at the frame after both helpers is in the second firing's information. -/
theorem seven_known : (helperH, constantAt 7) ∈ Q.information (apartFrom 7).base := by
  refine List.mem_append_left _ (List.mem_map.mpr ⟨first.tell, ?_, tell_read⟩)
  exact List.mem_append_right _ (List.mem_singleton_self _)

/-- **After `H ≐ 7`, telling `H ≠ 7` is refused.** -/
theorem apartSeven_refused : ¬ P.Admits (apartFrom 7) :=
  Interface.Step.refused_of_identified _ (apartFrom 7) (d := (helperH, constantAt 7))
    (List.mem_append_right _ (List.mem_singleton_self _))
    fun _ _ solved => solved _ seven_known

/-- The solution into the empty frame: `H ↦ 7`, `K ↦ 0`. -/
def close : Assignment both.arity empty.arity
  | .inl (.inl impossible) => impossible.elim
  | .inl (.inr ()) => constant 7
  | .inr () => constant 0

theorem close_helperH :
    (Frames.contextual tiny).act (a := both) (b := empty) close helperH = observe (constant (Γ := []) 7) := by
  show observe (instantiate close (generator both.arity (.inl (.inr ())))) = _
  rw [instantiate_generator]
  rfl

theorem close_constant (n : Nat) :
    (Frames.contextual tiny).act (a := both) (b := empty) close (constantAt n) = observe (constant (Γ := []) n) :=
  rfl

theorem close_fresh :
    (Frames.contextual tiny).act (a := both) (b := empty) close
      (observe (Interface.Helpers.fresh (extend empty ([], ())) ([], ()))) = observe (constant (Γ := []) 0) := by
  show observe (instantiate close (generator both.arity (.inr ()))) = _
  rw [instantiate_generator]
  rfl

/-- **Telling `H ≠ 8` is admitted.** -/
theorem apartEight_admitted : P.Admits (apartFrom 8) := by
  refine (Interface.Step.admits_iff_separating _ (apartFrom 8)).mpr
    ⟨List.nodup_singleton _, (Interface.Helpers.enabled_iff next).mpr (by decide),
      ⟨empty, close, ?_, ?_⟩, ?_⟩
  · intro e member
    rcases List.mem_append.mp member with old | told
    · obtain ⟨original, inside, rfl⟩ := List.mem_map.mp old
      rcases List.mem_append.mp inside with none | seven
      · exact absurd none List.not_mem_nil
      · obtain rfl := List.mem_singleton.mp seven
        obtain ⟨first_read, second_read⟩ := Prod.mk.inj tell_read
        show (Frames.contextual tiny).act (a := both) (b := empty) close
            ((Frames.contextual tiny).act (a := extend empty ([], ())) (b := both)
              (incl (extend empty ([], ())) ([], ())) first.tell.1) =
          (Frames.contextual tiny).act (a := both) (b := empty) close
            ((Frames.contextual tiny).act (a := extend empty ([], ())) (b := both)
              (incl (extend empty ([], ())) ([], ())) first.tell.2)
        rw [first_read, second_read, close_helperH, close_constant]
    · obtain rfl := List.mem_singleton.mp told
      show (Frames.contextual tiny).act (a := both) (b := empty) close
          (observe (Interface.Helpers.fresh (extend empty ([], ())) ([], ()))) =
        (Frames.contextual tiny).act (a := both) (b := empty) close (constantAt 0)
      rw [close_fresh, close_constant]
  · refine separates_append.mpr ⟨fun d member => absurd member List.not_mem_nil, ?_⟩
    intro d member equated
    obtain rfl := List.mem_singleton.mp member
    change (Frames.contextual tiny).act (a := both) (b := empty) close helperH =
      (Frames.contextual tiny).act (a := both) (b := empty) close (constantAt 8) at equated
    rw [close_helperH, close_constant] at equated
    exact absurd (congrArg head equated) (by decide)
  · intro _ _ _ _
    show (Frames.contextual tiny).Models _ []
    exact Frames.models_nil _

/-- **The contextual control**: a told disequation is refused after the firing that identifies it,
and a compatible one is admitted. -/
theorem control : P.Admits makeHelper ∧ ¬ P.Admits (apartFrom 7) ∧ P.Admits (apartFrom 8) :=
  ⟨makeHelper_admitted, apartSeven_refused, apartEight_admitted⟩

end ContextualTell

#print axioms DependentTell.tellApart_admitted
#print axioms DependentTell.identify_refused
#print axioms DependentTell.identify_admitted_without
#print axioms DependentTell.compatible_admitted
#print axioms DependentTell.control
#print axioms ContextualTell.apartSeven_refused
#print axioms ContextualTell.apartEight_admitted
#print axioms ContextualTell.control

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DisequalityFrames
