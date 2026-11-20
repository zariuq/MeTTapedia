import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.ContextualCoupling

/-!
# What a state mentions decides an admission only through the freshness of the opening

The step asks an opening to be fresh for what the state **mentions** (`Firing.Fresh`). So a state's
knowledge can decide an admission in two ways: by its solutions, and by the terms it happens to
write down. This module separates the two.

* `withTautology`: a state with one more equation `t = t`. It has the same solutions and mentions one
  more term.
* `models_tautology_iff`: every firing's information has the same solutions at the two states.
* `tautology_admits_iff`: **a firing whose opening is fresh at both states is admitted at one exactly
  when it is admitted at the other.** The one place where the added equation can matter is the
  freshness of the opening.
* `canonical_tautology_invariant`: at declaration frames, where a firing enters its rule's unknowns
  by extending the frame (`Contextual.canonical`), freshness holds at every state
  (`Contextual.canonical_fresh`), so **adding `t = t` changes the admission of no such firing**.
* `mention_matters_off_canonical`: on the two states of
  `Contextual.CouplingControls.tautology_flips_coupling`, every firing that enters its unknowns by
  extending the frame is admitted at one exactly when at the other, while the firing whose opening
  sends a rule's unknown to a name of the state is admitted at one and refused at the other.

So where unknowns enter only by extending a frame, adding an equation that says nothing changes no
admission; the condition "the two states mention the same unknowns" is asked for by openings into
names of the state, and by nothing else.
-/

set_option autoImplicit false

open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Contextual.CouplingControls
  (stateWith mentionsM coupling tautology_flips_coupling nameAt)
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Contextual.HelperControl
  (oneName)
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Helpers.Consumer (tiny)

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Worlds

open Interface (Frames)

universe uO uT uH uE uOcc

section General

variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH} {O : Type uOcc}
  {X : Frames Tm Hom} {E : Extensions.{uO, uH, uE} Hom} {P : Program Tm}

/-- **A state with one more equation that says nothing**: `t = t`. -/
def withTautology (s : State Tm O) (t : Tm s.frame) : State Tm O :=
  ⟨s.frame, (t, t) :: s.knowledge, s.present, s.label⟩

/-- The information of a firing at the state with the tautology: the tautology, carried along the
extension, and the information at the state. -/
theorem tautology_information (s : State Tm O) (t : Tm s.frame) (f : Firing O E P s.frame) :
    Firing.information X (withTautology s t) f =
      (X.act (E.weaken f.ext) t, X.act (E.weaken f.ext) t) :: Firing.information X s f :=
  rfl

/-- **The same solutions.** -/
theorem models_tautology_iff (s : State Tm O) (t : Tm s.frame) (f : Firing O E P s.frame) {b : Obj}
    (σ : Hom (E.target f.ext) b) :
    X.Models σ (Firing.information X (withTautology s t) f) ↔ X.Models σ (Firing.information X s f) := by
  rw [tautology_information]
  constructor
  · intro solved e member
    exact solved e (List.mem_cons_of_mem _ member)
  · intro solved e member
    rcases List.mem_cons.mp member with rfl | inside
    · exact (X.equivalence b).refl _
    · exact solved e inside

/-- **A firing whose opening is fresh at both states is admitted at one exactly when at the other.** -/
theorem tautology_admits_iff [DecidableEq O] (s : State Tm O) (t : Tm s.frame)
    (f : Firing O E P s.frame) (fresh : f.Fresh X s)
    (freshWith : Firing.Fresh X (withTautology s t) f) :
    Firing.Admits X (withTautology s t) f ↔ f.Admits X s := by
  constructor
  · rintro ⟨⟨-, shapes⟩, enabled, ⟨b, σ, solved⟩, entails⟩
    exact ⟨⟨fresh, shapes⟩, enabled, ⟨b, σ, (models_tautology_iff s t f σ).mp solved⟩,
      fun b σ solved => entails b σ ((models_tautology_iff s t f σ).mpr solved)⟩
  · rintro ⟨⟨-, shapes⟩, enabled, ⟨b, σ, solved⟩, entails⟩
    exact ⟨⟨freshWith, shapes⟩, enabled, ⟨b, σ, (models_tautology_iff s t f σ).mpr solved⟩,
      fun b σ solved => entails b σ ((models_tautology_iff s t f σ).mp solved)⟩

end General

/-! ## At declaration frames -/

section Declarations

variable {S : Mettapedia.OSLF.Binding.Signature} {O : Type} [DecidableEq O]
  {P : Program (Contextual.Terms S)}

/-- **Adding `t = t` changes the admission of no firing that enters its unknowns by extending the
frame.** -/
theorem canonical_tautology_invariant (s : State (Contextual.Terms S) O)
    (t : Contextual.Terms S s.frame) (r : Rule (Contextual.Terms S)) (member : r ∈ P)
    (selection : Selection O) (seen : List (Finset O)) :
    Firing.Admits (Frames.contextual S) (withTautology s t)
        (Contextual.canonical (F := s.frame) r member selection seen) ↔
      Firing.Admits (Frames.contextual S) s
        (Contextual.canonical (F := s.frame) r member selection seen) :=
  tautology_admits_iff s t _ (Contextual.canonical_fresh s r member selection seen)
    (Contextual.canonical_fresh (withTautology s t) r member selection seen)

end Declarations

/-- **Mention decides only off the canonical opening.** On the two states of
`Contextual.CouplingControls.tautology_flips_coupling` (no knowledge, and `m = m`): every firing that
enters its rule's unknowns by extending the frame is admitted at one exactly when at the other; the
firing that sends a rule's unknown to the name `m` of the state is admitted at the first and refused
at the second. -/
theorem mention_matters_off_canonical :
    (∀ (r : Rule (Contextual.Terms tiny)) (member : r ∈ Contextual.CouplingControls.program)
        (selection : Selection ℕ) (seen : List (Finset ℕ)),
        Firing.Admits (Frames.contextual tiny) (stateWith mentionsM)
            (Contextual.canonical (F := oneName) r member selection seen) ↔
          Firing.Admits (Frames.contextual tiny) (stateWith [])
            (Contextual.canonical (F := oneName) r member selection seen)) ∧
      (step (Frames.contextual tiny) ℕ (Contextual.declarations tiny)
        Contextual.CouplingControls.program).Admits (s := stateWith []) coupling ∧
      ¬ (step (Frames.contextual tiny) ℕ (Contextual.declarations tiny)
        Contextual.CouplingControls.program).Admits (s := stateWith mentionsM) coupling :=
  ⟨fun r member selection seen =>
      canonical_tautology_invariant (stateWith []) (nameAt oneName ()) r member selection seen,
    tautology_flips_coupling.2⟩

#print axioms tautology_information
#print axioms models_tautology_iff
#print axioms tautology_admits_iff
#print axioms canonical_tautology_invariant
#print axioms mention_matters_off_canonical

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Worlds
