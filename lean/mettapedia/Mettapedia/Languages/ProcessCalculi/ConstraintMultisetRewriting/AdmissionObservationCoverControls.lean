import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AdmissionObservationCover

/-!
# Correlated solution controls for guard-observation covers

The frame acts on Boolean observations by arbitrary substitutions of two-bit
worlds. A store equates the two coordinates, so its global solutions are
correlated. Each coordinate nevertheless has the exact cover {false,true}.
The cover suffices for universal local conjunctions without replacing the
correlated solution family by an independent product.
-/
set_option autoImplicit false
namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace AdmissionObservationCover.Controls
open Interface
abbrev World := Fin 2 → Bool

def frame : Frames (fun _ : Unit => World → Bool) (fun _ _ : Unit => World → World) where
  E := Eq
  equivalence _ := ⟨Eq.refl, Eq.symm, Eq.trans⟩
  act σ term := fun world => term (σ world)
  id _ := id
  comp later earlier := fun world => earlier (later world)
  act_id _ := rfl
  act_comp _ _ _ := rfl
  preserves := by intro a b σ s t same; subst t; rfl

def correlated : EquationStore (World → Bool) := [(fun w => w 0, fun w => w 1)]
def observe (index : Fin 2) (_ : Unit) (σ : World → World) : Bool := σ (fun _ => false) index

def cover : Cover frame (a := ()) correlated observe where
  values := fun _ => {false, true}
  upper := by intro b σ solved index; cases observe index b σ <;> simp

theorem cover_exact : cover.Exact := by
  intro index value member
  refine ⟨(), (fun _ _ => value), ?_, rfl⟩
  intro equation present
  obtain rfl := List.mem_singleton.mp present
  rfl

theorem correlated_solution_exists : frame.Solvable (a := ()) correlated := by
  refine ⟨(), (fun _ _ => false), ?_⟩
  intro equation member
  obtain rfl := List.mem_singleton.mp member
  rfl

theorem mixed_observation_impossible (b : Unit) (σ : World → World) (solved : frame.Models (a := ()) (b := b) σ correlated) :
    ¬ (observe 0 b σ = false ∧ observe 1 b σ = true) := by
  have equal := solved _ (List.mem_singleton_self _)
  have point := congrFun equal (fun _ => false)
  change observe 0 b σ = observe 1 b σ at point
  rintro ⟨zero, one⟩
  rw [zero, one] at point
  cases point

theorem universal_local_guards_exact (guard : Fin 2 → Bool → Prop) :
    frame.Entails (a := ()) correlated (fun b σ => ∀ index, guard index (observe index b σ)) ↔
      ∀ index, guard index false ∧ guard index true := by
  rw [cover.entails_iff cover_exact]
  simp [cover]

theorem observing_one_solution_is_not_a_cover :
    ¬ (∀ b (σ : World → World), frame.Models (a := ()) (b := b) σ correlated →
      ∀ index, observe index b σ ∈ ({false} : Finset Bool)) := by
  intro all
  have solved : frame.Models (a := ()) (b := ()) (fun _ _ => true) correlated := by
    intro equation member; obtain rfl := List.mem_singleton.mp member; rfl
  have impossible := all () (fun _ _ => true) solved 0
  simp only [observe, Finset.mem_singleton, Bool.true_eq_false] at impossible

def forceFalse : EquationStore (World → Bool) := [(fun w => w 0, fun _ => false)]

def strengthening_keeps_upper_cover : Cover frame (a := ()) (correlated ++ forceFalse) observe := cover.strengthen forceFalse

theorem strengthening_invalidates_old_reachability : ¬ (cover.strengthen forceFalse).Exact := by
  intro exact
  obtain ⟨b, σ, solved, observed⟩ := exact 0 true (by simp [Cover.strengthen, cover])
  have forced := ((Frames.models_append (X := frame) (a := ()) (b := b) σ correlated forceFalse).mp solved).2 _ (List.mem_singleton_self _)
  have point := congrFun forced (fun _ => false)
  change observe 0 b σ = false at point
  rw [observed] at point
  cases point

def impossible : EquationStore (World → Bool) := [(fun _ => false, fun _ => true)]

theorem impossible_not_solvable : ¬ frame.Solvable (a := ()) impossible := by
  rintro ⟨b, σ, solved⟩
  have eqn := solved _ (List.mem_singleton_self _)
  have point := congrFun eqn (fun _ => false)
  cases point

theorem vacuous_guards_do_not_give_solvability :
    frame.Entails (a := ()) impossible (fun _ _ => ∀ b : Bool, b = b) ∧ ¬ frame.Solvable (a := ()) impossible := by
  exact ⟨fun _ _ _ _ => rfl, impossible_not_solvable⟩

/-- Restriction and aggregation do not commute for arbitrary relational guards. -/
theorem coordinate_witnesses_need_not_glue :
    (∃ b σ, frame.Models (a := ()) (b := b) σ correlated ∧ observe 0 b σ = false) ∧
    (∃ b σ, frame.Models (a := ()) (b := b) σ correlated ∧ observe 1 b σ = true) ∧
    ¬ ∃ b σ, frame.Models (a := ()) (b := b) σ correlated ∧ observe 0 b σ = false ∧ observe 1 b σ = true := by
  refine ⟨?_, ?_, ?_⟩
  · exact cover_exact 0 false (by simp [cover])
  · exact cover_exact 1 true (by simp [cover])
  · rintro ⟨b, σ, solved, zero, one⟩
    exact mixed_observation_impossible b σ solved ⟨zero, one⟩
end AdmissionObservationCover.Controls
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AdmissionObservationCover.InfiniteControls
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface
abbrev World := Nat × Bool

def frame : Frames (fun _ : Unit => World → Bool) (fun _ _ : Unit => World → World) where
  E := Eq
  equivalence _ := ⟨Eq.refl, Eq.symm, Eq.trans⟩
  act σ term := fun w => term (σ w)
  id _ := id
  comp later earlier := fun w => earlier (later w)
  act_id _ := rfl
  act_comp _ _ _ := rfl
  preserves := by intro a b σ s t same; subst t; rfl

def observe (_ : Unit) (_ : Unit) (σ : World → World) : Bool := (σ (0,false)).2

def cover : Cover frame (a := ()) [] observe where
  values := fun _ => {false,true}
  upper := by intro b σ solved index; cases observe index b σ <;> simp

theorem exact_cover : cover.Exact := by
  intro index value member
  exact ⟨(), (fun _ => (0,value)), Frames.models_nil _, rfl⟩

def witness (n : Nat) : World → World := fun _ => (n,false)

theorem infinitely_many_distinct_solutions : Function.Injective witness := by
  intro n m same
  exact congrArg (fun σ => (σ (0,false)).1) same

theorem each_witness_solves (n : Nat) : frame.Models (a := ()) (b := ()) (witness n) [] := Frames.models_nil _
theorem same_observation_for_every_witness (n : Nat) : observe () () (witness n) = false := rfl

theorem exact_guard_reading (guard : Bool → Prop) :
    frame.Entails (a := ()) [] (fun b σ => guard (observe () b σ)) ↔ guard false ∧ guard true := by
  have exact := cover.entails_iff exact_cover (fun _ => guard)
  simpa [cover, Frames.Entails, observe] using exact
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AdmissionObservationCover.InfiniteControls
