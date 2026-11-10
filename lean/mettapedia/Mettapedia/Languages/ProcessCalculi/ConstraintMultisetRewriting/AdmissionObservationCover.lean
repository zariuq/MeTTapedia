import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Interface

/-!
# Admission from covers of individual guard observations

A universal conjunction depends on each guard's reachable observations, not
on an explicit Cartesian product of complete solutions. Upper covers certify
positive guards. Reachability of listed observations licenses counterexamples
and the converse. Correlations between observations need not be discarded or
assumed absent. A separate solvability witness prevents vacuous admission.
-/

set_option autoImplicit false
namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace AdmissionObservationCover
open Interface
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits (Enabled)
universe u v w i j
variable {Obj : Type u} {Tm : Obj → Type v} {Hom : Obj → Obj → Type w}
variable (X : Frames Tm Hom) {a : Obj} (K : EquationStore (Tm a))
variable {I : Type i} {Value : I → Type j}

structure Cover (observe : (index : I) → (b : Obj) → Hom a b → Value index) where
  values : (index : I) → Finset (Value index)
  upper : ∀ (b : Obj) (σ : Hom a b), X.Models σ K → ∀ index, observe index b σ ∈ values index

namespace Cover
variable {X K} {observe : (index : I) → (b : Obj) → Hom a b → Value index}

/-- Each listed local observation has its own global solution witness.
The witnesses for different indices need not be the same solution. -/
def Exact (cover : Cover X K observe) : Prop :=
  ∀ index value, value ∈ cover.values index →
    ∃ (b : Obj) (σ : Hom a b), X.Models σ K ∧ observe index b σ = value

theorem entails_of_all (cover : Cover X K observe) (guard : (index : I) → Value index → Prop)
    (checked : ∀ index value, value ∈ cover.values index → guard index value) :
    X.Entails K (fun b σ => ∀ index, guard index (observe index b σ)) := by
  intro b σ solved index
  exact checked index _ (cover.upper b σ solved index)

theorem entails_iff (cover : Cover X K observe) (exact : cover.Exact)
    (guard : (index : I) → Value index → Prop) :
    X.Entails K (fun b σ => ∀ index, guard index (observe index b σ)) ↔
      ∀ index value, value ∈ cover.values index → guard index value := by
  constructor
  · intro holds index value member
    obtain ⟨b, σ, solved, same⟩ := exact index value member
    exact same ▸ holds b σ solved index
  · exact cover.entails_of_all guard

theorem counterexample (cover : Cover X K observe) (exact : cover.Exact)
    (guard : (index : I) → Value index → Prop) (index : I) (value : Value index)
    (member : value ∈ cover.values index) (fails : ¬ guard index value) :
    ∃ (b : Obj) (σ : Hom a b), X.Models σ K ∧ ¬ (∀ index, guard index (observe index b σ)) := by
  obtain ⟨b, σ, solved, same⟩ := exact index value member
  exact ⟨b, σ, solved, fun all => fails (same ▸ all index)⟩

/-- Further equations may remove solutions. An upper cover remains sound;
its old reachability witnesses need not survive. -/
def strengthen (cover : Cover X K observe) (extra : EquationStore (Tm a)) :
    Cover X (K ++ extra) observe where
  values := cover.values
  upper := fun b σ solved => cover.upper b σ ((Frames.models_append σ K extra).mp solved).1

/-- A less discriminating observer reuses the cover by mapping observations,
without enumerating solutions again. -/
def project {Output : I → Type} [∀ index, DecidableEq (Output index)]
    (cover : Cover X K observe) (view : (index : I) → Value index → Output index) :
    Cover X K (fun index b σ => view index (observe index b σ)) where
  values := fun index => (cover.values index).image (view index)
  upper := fun b σ solved index => Finset.mem_image.mpr ⟨_, cover.upper b σ solved index, rfl⟩

theorem exact_project {Output : I → Type} [∀ index, DecidableEq (Output index)]
    (cover : Cover X K observe) (exact : cover.Exact) (view : (index : I) → Value index → Output index) :
    (cover.project view).Exact := by
  intro index value member
  obtain ⟨original, present, same⟩ := Finset.mem_image.mp member
  obtain ⟨b, σ, solved, observed⟩ := exact index original present
  exact ⟨b, σ, solved, (congrArg (view index) observed).trans same⟩

end Cover

section Step
variable {O : Type} [DecidableEq O] {State : Type} {Firing : State → Type}
variable (P : Interface.Step X O State Firing) {s : State} (f : Firing s)
variable [P.Guarded]
variable (observe : (index : I) → (b : Obj) → Hom (P.target f) b → Value index)
variable (guard : (index : I) → Value index → Prop)
variable (reads : ∀ b σ, P.Holds f b σ ↔ ∀ index, guard index (observe index b σ))
include reads

theorem admits_of_cover (cover : Cover X (P.information f) observe)
    (shapes : P.Shapes f)
    (enabled : Enabled (fun _ : O => ()) (P.present s) ((P.selection f).commit (T := Unit)))
    (witness : X.Solvable (P.information f))
    (checked : ∀ index value, value ∈ cover.values index → guard index value) : P.Admits f := by
  apply (P.admits_iff f).mpr
  refine ⟨shapes, enabled, witness, ?_⟩
  intro b σ solved
  exact (reads b σ).mpr (cover.entails_of_all guard checked b σ solved)

theorem admits_iff_cover (cover : Cover X (P.information f) observe) (exact : cover.Exact) :
    P.Admits f ↔ P.Shapes f ∧
      Enabled (fun _ : O => ()) (P.present s) ((P.selection f).commit (T := Unit)) ∧
      X.Solvable (P.information f) ∧ (∀ index value, value ∈ cover.values index → guard index value) := by
  constructor
  · intro admitted
    obtain ⟨shapes, enabled, solved, entails⟩ := (P.admits_iff f).mp admitted
    refine ⟨shapes, enabled, solved, (cover.entails_iff exact guard).mp ?_⟩
    exact fun b σ models => (reads b σ).mp (entails b σ models)
  · rintro ⟨shapes, enabled, solved, checked⟩
    exact admits_of_cover X P f observe guard reads cover shapes enabled solved checked
end Step
end AdmissionObservationCover
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
