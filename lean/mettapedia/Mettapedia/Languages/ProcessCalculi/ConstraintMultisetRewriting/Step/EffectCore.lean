import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Frames

/-!
# Prepared effects and semantic knowledge contracts

Effects describe candidate state changes independently of admission. Both
knowledge obligations are semantic: information refines the source along the
extension, and the result refines information along settlement. Exactness is
an additional property. The existing step supplies an interpretation into
this interface; migration of its consumers can therefore be checked locally.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface

open MeTTaCalculus.OccurrenceCommits (Enabled fire)

universe uO uT uH uOcc uS uF

theorem Frames.models_of_transport {Obj : Type uO} {Tm : Obj → Type uT}
    {Hom : Obj → Obj → Type uH} (X : Frames Tm Hom) {a m b : Obj}
    (old : EquationStore (Tm a)) (information : EquationStore (Tm m))
    (extension : Hom a m)
    (contains : ∀ e ∈ old, (X.act extension e.1, X.act extension e.2) ∈ information)
    (σ : Hom m b) (solved : X.Models σ information) :
    X.Models (X.comp σ extension) old := by
  apply (Frames.models_applyStore extension σ old).mp
  intro e member
  obtain ⟨original, present, rfl⟩ := List.mem_map.mp member
  exact solved _ (contains original present)

structure EffectCore {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}
    (X : Frames Tm Hom) (O : Type uOcc) [DecidableEq O]
    (State : Type uS) (Firing : State → Type uF) where
  frame : State → Obj
  knowledge : (s : State) → EquationStore (Tm (frame s))
  present : State → Finset O
  selection : {s : State} → Firing s → Selection O
  target : {s : State} → Firing s → Obj
  extension : {s : State} → (f : Firing s) → Hom (frame s) (target f)
  information : {s : State} → (f : Firing s) → EquationStore (Tm (target f))
  information_refines : ∀ {s : State} (f : Firing s) {b : Obj} (σ : Hom (target f) b),
    X.Models σ (information f) → X.Models (X.comp σ (extension f)) (knowledge s)
  Shapes : {s : State} → Firing s → Prop
  preparedResult : {s : State} → (f : Firing s) → Shapes f ∧
    Enabled (fun _ : O => ()) (present s) ((selection f).commit (T := Unit)) ∧
    X.Solvable (information f) → State
  present_preparedResult : ∀ {s : State} (f : Firing s) (p : Shapes f ∧
      Enabled (fun _ : O => ()) (present s) ((selection f).commit (T := Unit)) ∧
      X.Solvable (information f)),
    present (preparedResult f p) = fire (present s) ((selection f).commit (T := Unit))
  preparedSettle : {s : State} → (f : Firing s) → (p : Shapes f ∧
      Enabled (fun _ : O => ()) (present s) ((selection f).commit (T := Unit)) ∧
      X.Solvable (information f)) → Hom (target f) (frame (preparedResult f p))
  result_refines : ∀ {s : State} (f : Firing s) (p : Shapes f ∧
      Enabled (fun _ : O => ()) (present s) ((selection f).commit (T := Unit)) ∧
      X.Solvable (information f)) {b : Obj} (σ : Hom (frame (preparedResult f p)) b),
    X.Models σ (knowledge (preparedResult f p)) → X.Models (X.comp σ (preparedSettle f p)) (information f)

namespace EffectCore

variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}
  {X : Frames Tm Hom} {O : Type uOcc} [DecidableEq O]
  {State : Type uS} {Firing : State → Type uF}
  (E : EffectCore X O State Firing)

abbrev Prepares {s : State} (f : Firing s) : Prop :=
  E.Shapes f ∧ Enabled (fun _ : O => ()) (E.present s)
    ((E.selection f).commit (T := Unit)) ∧ X.Solvable (E.information f)

def along {s : State} (f : Firing s) (p : E.Prepares f) :
    Hom (E.frame s) (E.frame (E.preparedResult f p)) :=
  X.comp (E.preparedSettle f p) (E.extension f)

/-- The reverse implication is an optional exactness certificate. -/
def ExactKnowledge : Prop :=
  ∀ {s : State} (f : Firing s) (p : E.Prepares f) {b : Obj}
    (σ : Hom (E.frame (E.preparedResult f p)) b),
    X.Models (X.comp σ (E.preparedSettle f p)) (E.information f) →
      X.Models σ (E.knowledge (E.preparedResult f p))

theorem models_result_iff (exactness : E.ExactKnowledge) {s : State}
    (f : Firing s) (p : E.Prepares f) {b : Obj} (σ : Hom (E.frame (E.preparedResult f p)) b) :
    X.Models σ (E.knowledge (E.preparedResult f p)) ↔
      X.Models (X.comp σ (E.preparedSettle f p)) (E.information f) :=
  ⟨E.result_refines f p σ, exactness f p σ⟩

/-- Every prepared effect pulls result solutions back to the source. -/
theorem models_along {s : State} (f : Firing s) (p : E.Prepares f) {b : Obj}
    (σ : Hom (E.frame (E.preparedResult f p)) b)
    (solved : X.Models σ (E.knowledge (E.preparedResult f p))) :
    X.Models (X.comp σ (E.along f p)) (E.knowledge s) := by
  have back := E.information_refines f _ (E.result_refines f p σ solved)
  exact (Frames.models_congr
    (fun t => Frames.act_comp_assoc (E.extension f) (E.preparedSettle f p) σ t)
    (E.knowledge s)).mp back

/-- Permission is a predicate on prepared candidates, with no default. -/
abbrev Admission := ∀ {s : State} (f : Firing s), E.Prepares f → Prop

def guardAdmission (holds : ∀ {s : State} (f : Firing s) (b : Obj), Hom (E.target f) b → Prop) :
    E.Admission := fun f _ => X.Entails (E.information f) (holds f)

/-- Edges retain the complete candidate; certificates do not identify distinct firings. -/
structure Event (allow : E.Admission) (s t : State) where
  firing : Firing s
  prepared : E.Prepares firing
  permitted : allow firing prepared
  target_eq : E.preparedResult firing prepared = t

def eventAlong {allow : E.Admission} {s t : State} (e : E.Event allow s t) :
    Hom (E.frame s) (E.frame t) := e.target_eq ▸ E.along e.firing e.prepared

theorem event_models {allow : E.Admission} {s t : State} (e : E.Event allow s t)
    {b : Obj} (σ : Hom (E.frame t) b) (solved : X.Models σ (E.knowledge t)) :
    X.Models (X.comp σ (E.eventAlong e)) (E.knowledge s) := by
  rcases e with ⟨f, p, _, rfl⟩
  exact E.models_along f p σ solved

/-- Event restriction preserves the candidate, preparation and endpoint. -/
def Event.restrict {first second : E.Admission}
    (included : ∀ {s : State} (f : Firing s) (p : E.Prepares f), first f p → second f p)
    {s t : State} (e : E.Event first s t) : E.Event second s t :=
  ⟨e.firing, e.prepared, included _ _ e.permitted, e.target_eq⟩

end EffectCore

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface
