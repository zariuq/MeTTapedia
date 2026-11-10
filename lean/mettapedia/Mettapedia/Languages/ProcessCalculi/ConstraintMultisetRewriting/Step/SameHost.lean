import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.PreparedNative

/-!
# One host: guards, disequations, fresh helpers and settlement on one carrier

The carrier is the category of declaration frames, `Frames.contextual S`, and its disequation
frames: the carrier of the helper step and of the native step. One step here has every feature at
once, and the controls of preparation and of exhaustive versus committing settlement run on it.

## The step (`settledBy`, `host`, `hostWith`)

A state is a helper state: a frame, its knowledge and its present occurrences. A firing
(`Firing`) makes one occurrence and one **fresh helper**, tells the helper's value, a term over the
frame it fires at, and is **guarded** by authored atoms at the frame with the helper: equations and
disequations of observations (`Atom`, `Atom.Holds`). Its preparation is its shapes; its result is the
frame with the helper and the information read along its **settlement**. `host` settles by the
identity, and `hostWith` is `host` with told **disequations**
(`Interface.Step.withDisequations`).

* **Coverage** (`host_coversAnswers`, `hostWith_coversAnswers`): both are exhaustive; they cover
  their answers.
* **The helper step is inside the host** (`ofHelper`, `ofHelper_holds`, `ofHelper_admits_iff`,
  `ofHelper_result`): a helper firing's equation guards become equation atoms, with the same
  admission and the same result.

## The controls on this carrier (`Controls`, natural numbers as constants)

At the frame with one name `x`, the firing `guarded` makes the helper `h` valued `x`, guarded by
`h ≠ 0`:
* **Preparation** (`guarded_refused`, `apart_admitted`, `guard_not_everywhere`): the step without
  disequations refuses it, since `x ↦ 0` fails the guard; with `h ≠ 0` told, `hostWith` admits it and
  prepares its result; the guard does not hold at every solution, so no result obtained from the
  base admission exists for it.
* **A committing settlement** (`closing_control`, `closing_sound_not_covering`): the same states and
  firings, settled by closing every old name to `0`, admit the firing `quiet` without guards, keep its
  result solvable and are sound; they commit `x` to `0`, so the answer `x ↦ 1` is not recovered after
  any extension of its frame: a committing step, not an answer-covering one. `host` covers.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SameHost

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits (Enabled fire)
open Interface (Frames)
open Interface.Frames (Frame)
open Interface.Helpers (State extend incl fresh)
open PreparedStep (Prepared)
open SettlementCoverage (CoversAnswers Extends extends_of_retraction Sound sound)

variable {S : Signature}

/-- **An authored guard atom** at a frame: two observations asked equal, or asked apart. -/
inductive Atom (F : Frame S) where
  | same (left right : Observation S F.arity)
  | apart (left right : Observation S F.arity)

/-- **The interpretation of an atom** at a solution. -/
def Atom.Holds {F b : Frame S} (σ : Assignment F.arity b.arity) : Atom F → Prop
  | .same left right => instantiateObservation σ left = instantiateObservation σ right
  | .apart left right => instantiateObservation σ left ≠ instantiateObservation σ right

variable (S) (O : Type) [DecidableEq O]

/-- **A same-host firing**: it makes one occurrence and one fresh helper, tells the helper's value,
a term over the frame it fires at, and is guarded by authored atoms at the frame with the helper. -/
structure Firing (s : State S O) where
  made : O
  helper : MetaArity S
  value : Term (signature S s.frame.arity) helper.1 helper.2
  guards : List (Atom (extend s.frame helper))

variable {S O}

namespace Firing

variable {s : State S O} (f : Firing S O s)

/-- The occurrence it makes. -/
def selection : Selection O := ⟨[], [], [f.made]⟩

/-- The helper's equation, at the frame with the helper. -/
def tell : Equation (Observation S (extend s.frame f.helper).arity) :=
  (observe (fresh s.frame f.helper), observe (instantiate (incl s.frame f.helper) f.value))

/-- Its information: the knowledge, read at the frame with the helper, and the helper's equation. -/
def information : EquationStore (Observation S (extend s.frame f.helper).arity) :=
  (Frames.contextual S).applyStore (incl s.frame f.helper) s.knowledge ++ [f.tell]

end Firing

variable (S O) in
/-- **The same-host prepared step, settled by `settleBy`**: its result is the frame with the helper
and the information read along the settlement. -/
def settledBy (settleBy : ∀ {s : State S O} (f : Firing S O s),
      Assignment (extend s.frame f.helper).arity (extend s.frame f.helper).arity) :
    Prepared.{_, _, _, _, _, _, 0} (Frames.contextual S) O (State S O) (Firing S O) where
  frame s := s.frame
  knowledge s := s.knowledge
  present s := s.present
  selection f := f.selection
  target f := extend _ f.helper
  extension f := incl _ f.helper
  information f := f.information
  transported := by
    intro s f e member
    exact List.mem_append_left _ (List.mem_map.mpr ⟨e, member, rfl⟩)
  Shapes f := f.selection.made.Nodup
  Holds f _ σ := ∀ atom ∈ f.guards, atom.Holds σ
  Prep f := f.selection.made.Nodup
  prepare _ shapes _ _ := shapes
  result {s} f _ := ⟨extend _ f.helper, (Frames.contextual S).applyStore (settleBy f) f.information,
    fire s.present (f.selection.commit (T := Unit))⟩
  present_result _ _ := rfl
  settle f _ := settleBy f
  knowledge_result _ _ := rfl

variable (S O) in
/-- **The host**: settled by the identity. -/
abbrev host := settledBy S O fun f => (Frames.contextual S).id (extend _ f.helper)

theorem host_reflects : (host S O).step.Reflects :=
  fun _ _ _ _ same => DisequalityFrames.id_reflects same

variable (S O) in
/-- **The host with disequations.** -/
abbrev hostWith := (host S O).step.withDisequations host_reflects

theorem host_extends {s : State S O} (f : Firing S O s) (p : (host S O).Prep f) :
    Extends (Frames.contextual S) ((host S O).settle f p) :=
  extends_of_retraction (X := Frames.contextual S) (e := (host S O).settle f p)
    ((Frames.contextual S).id _) fun t => EvidenceInterface.id_retraction (X := Frames.contextual S) t

/-- **The host covers its answers.** -/
theorem host_coversAnswers : CoversAnswers (host S O).step.toStep := by
  apply Prepared.step_coversAnswers
  intro _ f p
  exact host_extends f p

/-- **The host with disequations covers its answers.** -/
theorem hostWith_coversAnswers : CoversAnswers (hostWith S O) := by
  apply SettlementCoverage.withDisequations_coversAnswers
  intro _ f p
  exact host_extends f ((host S O).prepare f p.1 p.2.1 p.2.2)

/-! ## The helper step inside the host -/

/-- **A helper firing as a same-host firing**: its equation guards, read at the frame with the
helper, become `same` atoms. -/
def ofHelper {s : State S O} (f : Interface.Helpers.Firing s) : Firing S O s :=
  ⟨f.made, f.helper, f.value, f.guards.map fun e =>
    .same ((Frames.contextual S).act (incl s.frame f.helper) e.1)
      ((Frames.contextual S).act (incl s.frame f.helper) e.2)⟩

/-- **The guards agree.** -/
theorem ofHelper_holds {s : State S O} (f : Interface.Helpers.Firing s) {b : Frame S}
    (σ : Assignment (extend s.frame f.helper).arity b.arity) :
    (host S O).Holds (ofHelper f) b σ ↔ Interface.Helpers.helperStep.Holds f b σ := by
  constructor
  · intro holds e member
    have atom := holds _ (List.mem_map.mpr ⟨e, member, rfl⟩)
    show instantiateObservation (Assignment.compose σ (incl s.frame f.helper)) e.1 =
      instantiateObservation (Assignment.compose σ (incl s.frame f.helper)) e.2
    rw [← instantiateObservation_comp, ← instantiateObservation_comp]
    exact atom
  · intro holds atom member
    obtain ⟨e, inside, rfl⟩ := List.mem_map.mp member
    have solved := holds e inside
    show instantiateObservation σ (instantiateObservation (incl s.frame f.helper) e.1) =
      instantiateObservation σ (instantiateObservation (incl s.frame f.helper) e.2)
    rw [instantiateObservation_comp, instantiateObservation_comp]
    exact solved

/-- **The host admits a helper firing exactly when the helper step does.** -/
theorem ofHelper_admits_iff {s : State S O} (f : Interface.Helpers.Firing s) :
    (host S O).step.Admits (ofHelper f) ↔ Interface.Helpers.helperStep.Admits f := by
  constructor
  · rintro ⟨shapes, enabled, solvable, asked⟩
    exact ⟨shapes, enabled, solvable, fun b σ solved => (ofHelper_holds f σ).mp (asked b σ solved)⟩
  · rintro ⟨shapes, enabled, solvable, asked⟩
    exact ⟨shapes, enabled, solvable, fun b σ solved => (ofHelper_holds f σ).mpr (asked b σ solved)⟩

/-- **With the same result.** -/
theorem ofHelper_result {s : State S O} (f : Interface.Helpers.Firing s)
    (admitted : (host S O).step.Admits (ofHelper f)) (helperAdmitted : Interface.Helpers.helperStep.Admits f) :
    (host S O).step.result (ofHelper f) admitted = Interface.Helpers.helperStep.result f helperAdmitted := by
  show (⟨extend s.frame f.helper,
      (Frames.contextual S).applyStore ((Frames.contextual S).id (extend s.frame f.helper)) f.information,
      fire s.present (f.selection.commit (T := Unit))⟩ : State S O) =
    ⟨extend s.frame f.helper, f.information, fire s.present (f.selection.commit (T := Unit))⟩
  rw [Frames.applyStore_id]

/-! ## The controls on this carrier -/

namespace Controls

open Interface.Helpers.Consumer (tiny constant empty)

/-- The constant an observation is headed by, if any. -/
def head {V : Type} {declaration : V → MetaArity tiny} : Observation tiny declaration → Option Nat
  | ⟨_, _, .op (.inl n) _⟩ => some n
  | _ => none

/-- The frame with one parameterless name `x`. -/
abbrev one : Frame tiny := ⟨Unit, fun _ => ([], ())⟩

/-- The state at `one` with no knowledge and no occurrences. -/
abbrev start : State tiny Nat := ⟨one, [], ∅⟩

/-- The frame with `x` and the fresh helper `h`. -/
abbrev both : Frame tiny := extend one ([], ())

/-- `x`, as a term over `one`. -/
def x : Term (signature tiny one.arity) [] () := generator one.arity ()

/-- `x` at the frame with the helper. -/
def xAt : Observation tiny both.arity := observe (generator both.arity (.inl ()))

/-- `h` at the frame with the helper. -/
def hAt : Observation tiny both.arity := observe (generator both.arity (.inr ()))

/-- A constant at the frame with the helper. -/
def constantAt (n : Nat) : Observation tiny both.arity := observe (constant (Γ := []) n)

/-- **The guarded firing**: make occurrence `1` and the helper `h` valued `x`, guarded by `h ≠ 0`. -/
def guarded : Firing tiny Nat start := ⟨1, ([], ()), x, [.apart hAt (constantAt 0)]⟩

/-- The same firing without guards. -/
def quiet : Firing tiny Nat start := ⟨1, ([], ()), x, []⟩

/-- The solution closing `x` and `h` to `n`. -/
def closeAt (n : Nat) : Assignment both.arity empty.arity := fun _ => constant n

theorem closeAt_h (n : Nat) :
    instantiateObservation (closeAt n) hAt = observe (constant (Γ := []) n) := by
  show observe (instantiate (closeAt n) (generator both.arity (.inr ()))) = _
  rw [instantiate_generator]
  rfl

theorem closeAt_x (n : Nat) :
    instantiateObservation (closeAt n) xAt = observe (constant (Γ := []) n) := by
  show observe (instantiate (closeAt n) (generator both.arity (.inl ()))) = _
  rw [instantiate_generator]
  rfl

theorem closeAt_constant (n m : Nat) :
    instantiateObservation (closeAt n) (constantAt m) = observe (constant (Γ := []) m) :=
  rfl

/-- Instantiation fixes constants. -/
theorem constant_fixed {b c : Frame tiny} (σ : Assignment b.arity c.arity) (n : Nat) :
    instantiateObservation σ (observe (constant (declaration := b.arity) (Γ := []) n)) =
      observe (constant (Γ := []) n) :=
  rfl

theorem incl_x : instantiate (incl one ([], ())) x = generator both.arity (.inl ()) :=
  instantiate_generator (incl one ([], ())) ()

/-- **`closeAt n` solves the guarded firing's information.** -/
theorem guarded_solved (n : Nat) :
    (Frames.contextual tiny).Models (a := both) (b := empty) (closeAt n) guarded.information := by
  intro e member
  rcases List.mem_append.mp member with none | told
  · exact absurd none List.not_mem_nil
  · obtain rfl := List.mem_singleton.mp told
    have first : instantiate (closeAt n) (generator both.arity (.inr ())) = constant n :=
      instantiate_generator _ _
    have second : instantiate (closeAt n) (instantiate (incl one ([], ())) x) = constant n := by
      rw [incl_x]
      exact instantiate_generator _ _
    show observe (instantiate (closeAt n) (generator both.arity (.inr ()))) =
      observe (instantiate (closeAt n) (instantiate (incl one ([], ())) x))
    rw [first, second]
    rfl

/-- The unguarded firing has the same information. -/
theorem quiet_solved (n : Nat) :
    (Frames.contextual tiny).Models (a := both) (b := empty) (closeAt n) quiet.information :=
  guarded_solved n

theorem hAt_ne_constant (n : Nat) : hAt ≠ constantAt n := by
  intro same
  have heads : (none : Option Nat) = some n := congrArg head same
  cases heads

theorem enabled_one :
    Enabled (fun _ : Nat => ()) (∅ : Finset Nat) ((⟨[], [], [1]⟩ : Selection Nat).commit (T := Unit)) :=
  ⟨by simp [Selection.commit], by simp [Selection.commit], by simp [Selection.commit],
    by simp [Selection.commit], by simp [Selection.commit]⟩

/-! ### Preparation: a guard made valid by a told disequation -/

/-- **The step without disequations refuses the guarded firing**: `x ↦ 0` fails `h ≠ 0`. -/
theorem guarded_refused : ¬ (host tiny Nat).step.Admits guarded := by
  intro admitted
  have asked := admitted.2.2.2 empty (closeAt 0) (guarded_solved 0)
  exact asked (.apart hAt (constantAt 0)) (List.mem_singleton_self _)
    ((closeAt_h 0).trans (closeAt_constant 0 0).symm)

/-- The state without disequations. -/
def start' : (host tiny Nat).step.DState := ⟨start, [], DisequalityFrames.separates_nil _⟩

/-- **The guarded firing that tells `h ≠ 0`.** -/
def apart : (host tiny Nat).step.DFiring start' :=
  ⟨guarded, [(hAt, constantAt 0)], by
    refine (DisequalityFrames.separates_id_iff_apart _).mpr fun d member => ?_
    rcases List.mem_append.mp member with none | told
    · exact absurd none List.not_mem_nil
    · obtain rfl := List.mem_singleton.mp told
      exact hAt_ne_constant 0⟩

/-- **With `h ≠ 0` told, the host admits the guarded firing**, and prepares its result. -/
theorem apart_admitted : (hostWith tiny Nat).Admits apart := by
  refine (Interface.Step.admits_iff_separating host_reflects apart).mpr
    ⟨List.nodup_singleton _, enabled_one, ⟨empty, closeAt 1, guarded_solved 1, ?_⟩, ?_⟩
  · intro d member equated
    rcases List.mem_append.mp member with none | told
    · exact absurd none List.not_mem_nil
    · obtain rfl := List.mem_singleton.mp told
      change instantiateObservation (closeAt 1) hAt = instantiateObservation (closeAt 1) (constantAt 0)
        at equated
      rw [closeAt_h, closeAt_constant] at equated
      exact absurd (congrArg head equated) (by decide)
  · intro _ g _ separated atom member
    obtain rfl := List.mem_singleton.mp member
    exact separated (hAt, constantAt 0) (List.mem_append_right _ (List.mem_singleton_self _))

/-- **The guard does not hold at every solution**: `x ↦ 0` fails it. A result obtained from the
base admission needs the guard at every solution; preparation does not. -/
theorem guard_not_everywhere :
    ¬ ∀ (b : Frame tiny) (σ : Assignment both.arity b.arity), (host tiny Nat).Holds guarded b σ :=
  fun everywhere => everywhere empty (closeAt 0) (.apart hAt (constantAt 0)) (List.mem_singleton_self _)
    ((closeAt_h 0).trans (closeAt_constant 0 0).symm)

/-- **The preparation control on this carrier.** -/
theorem preparation_control :
    ¬ (host tiny Nat).step.Admits guarded ∧ (hostWith tiny Nat).Admits apart :=
  ⟨guarded_refused, apart_admitted⟩

/-! ### A committing settlement: closing old names is consistent and sound, and does not cover -/

/-- The settlement that closes every old name to `0` and keeps the helper. -/
def closeOld {s : State tiny Nat} (f : Firing tiny Nat s) :
    Assignment (extend s.frame f.helper).arity (extend s.frame f.helper).arity
  | .inl _ => constant 0
  | .inr () => fresh s.frame f.helper

/-- **The same states and firings, settled by closing old names.** -/
abbrev closing := settledBy tiny Nat closeOld

theorem quiet_admitted : (closing).step.Admits quiet :=
  ⟨List.nodup_singleton _, enabled_one, ⟨empty, closeAt 1, quiet_solved 1⟩,
    fun _ _ _ _ member => absurd member List.not_mem_nil⟩

theorem closeOld_x : instantiateObservation (closeOld quiet) xAt = observe (constant (Γ := []) 0) :=
  congrArg observe (instantiate_generator (closeOld quiet) (.inl ()))

/-- **The closed result is solvable.** -/
theorem closing_result_solvable :
    (Frames.contextual tiny).Solvable ((closing).step.knowledge ((closing).step.result quiet quiet_admitted)) := by
  refine ⟨empty, closeAt 0, ?_⟩
  intro e member
  obtain ⟨original, inside, rfl⟩ := List.mem_map.mp member
  rcases List.mem_append.mp inside with none | told
  · exact absurd none List.not_mem_nil
  · obtain rfl := List.mem_singleton.mp told
    have first : instantiate (closeOld quiet) (generator both.arity (.inr ())) =
        generator both.arity (.inr ()) :=
      instantiate_generator _ _
    have second : instantiate (closeOld quiet) (instantiate (incl one ([], ())) x) = constant 0 := by
      rw [incl_x]
      exact instantiate_generator _ _
    show instantiateObservation (closeAt 0) (observe (instantiate (closeOld quiet) (generator both.arity (.inr ())))) =
      instantiateObservation (closeAt 0) (observe (instantiate (closeOld quiet) (instantiate (incl one ([], ())) x)))
    rw [first, second]
    exact (closeAt_h 0).trans (closeAt_constant 0 0).symm

/-- **Closing old names loses the answer `x ↦ 1`**, after every extension of its frame. -/
theorem closing_not_coversAnswers : ¬ CoversAnswers (closing).step.toStep := by
  intro covers
  obtain ⟨c, j, τ, _, _, agree⟩ :=
    covers (s := start) quiet quiet_admitted (b := empty) (closeAt 1) (quiet_solved 1)
  have point := agree xAt
  change instantiateObservation (Assignment.compose j (closeAt 1)) xAt =
    instantiateObservation (Assignment.compose τ (closeOld quiet)) xAt at point
  have left : instantiateObservation (Assignment.compose j (closeAt 1)) xAt =
      observe (constant (Γ := []) 1) :=
    (instantiateObservation_comp (closeAt 1) j xAt).symm.trans
      ((congrArg (instantiateObservation j) (closeAt_x 1)).trans (constant_fixed j 1))
  have right : instantiateObservation (Assignment.compose τ (closeOld quiet)) xAt =
      observe (constant (Γ := []) 0) :=
    (instantiateObservation_comp (closeOld quiet) τ xAt).symm.trans
      ((congrArg (instantiateObservation τ) closeOld_x).trans (constant_fixed τ 0))
  have heads : some 1 = some 0 := congrArg head (left.symm.trans (point.trans right))
  exact absurd (Option.some.inj heads) (by decide)

/-- **The settlement control on this carrier**: closing old names admits the firing without guards,
keeps its result solvable, and does not cover; the host covers. -/
theorem closing_control :
    (closing).step.Admits quiet ∧
      (Frames.contextual tiny).Solvable ((closing).step.knowledge ((closing).step.result quiet quiet_admitted)) ∧
      ¬ CoversAnswers (closing).step.toStep ∧ CoversAnswers (host tiny Nat).step.toStep :=
  ⟨quiet_admitted, closing_result_solvable, closing_not_coversAnswers, host_coversAnswers⟩

/-- **Closing old names is sound**: the committing settlement satisfies the step's one law. -/
theorem closing_sound : Sound (closing).step.toStep :=
  sound (closing).step.toStep

/-- **Closing old names is a committing step**: sound, and not answer-covering. -/
theorem closing_sound_not_covering : Sound (closing).step.toStep ∧ ¬ CoversAnswers (closing).step.toStep :=
  ⟨closing_sound, closing_not_coversAnswers⟩

end Controls

#print axioms host_coversAnswers
#print axioms hostWith_coversAnswers
#print axioms ofHelper_admits_iff
#print axioms ofHelper_result
#print axioms Controls.guarded_refused
#print axioms Controls.apart_admitted
#print axioms Controls.guard_not_everywhere
#print axioms Controls.preparation_control
#print axioms Controls.closing_result_solvable
#print axioms Controls.closing_not_coversAnswers
#print axioms Controls.closing_control
#print axioms Controls.closing_sound
#print axioms Controls.closing_sound_not_covering

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SameHost
