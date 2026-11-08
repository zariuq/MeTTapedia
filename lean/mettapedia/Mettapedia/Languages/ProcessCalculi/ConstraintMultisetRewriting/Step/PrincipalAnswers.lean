import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Interface

/-!
# Asks decided at a principal answer

Two facts about the frames of the candidate step that need nothing beyond the interface.

* **Solutions are read through their action** (`Frames.models_congrE`): two morphisms that act
  alike on every term, up to the equivalence of terms, solve the same stores.
* **A stable ask is decided at a principal answer** (`Frames.Principal.entails_iff`): an
  observation that respects the action and survives further instantiation holds at every solution
  of the knowledge exactly when it holds at the answer. Equality guards are such observations
  (`Frames.Principal.entails_models_iff`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface

universe uO uT uH

namespace Frames

variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH} {X : Frames Tm Hom}

/-- Models depend on a morphism only through its action, up to the equivalence of terms. -/
theorem models_congrE {a b : Obj} {f g : Hom a b} (same : ∀ t : Tm a, X.E (X.act f t) (X.act g t))
    (store : EquationStore (Tm a)) : X.Models f store ↔ X.Models g store := by
  constructor
  · intro solved e member
    have h : X.E (X.act f e.1) (X.act f e.2) := solved e member
    show X.E (X.act g e.1) (X.act g e.2)
    exact (X.equivalence b).trans ((X.equivalence b).symm (same e.1))
      ((X.equivalence b).trans h (same e.2))
  · intro solved e member
    have h : X.E (X.act g e.1) (X.act g e.2) := solved e member
    show X.E (X.act f e.1) (X.act f e.2)
    exact (X.equivalence b).trans (same e.1)
      ((X.equivalence b).trans h ((X.equivalence b).symm (same e.2)))

/-- **A stable ask is decided at a principal answer**: when an observation respects the action
and survives further instantiation, it holds at every solution exactly when it holds at the
answer. -/
theorem Principal.entails_iff {a m : Obj} {store : EquationStore (Tm a)} {answer : Hom a m}
    (principal : X.Principal store answer) {observation : (b : Obj) → Hom a b → Prop}
    (respects : ∀ (b : Obj) (f g : Hom a b), (∀ t : Tm a, X.E (X.act f t) (X.act g t)) →
      (observation b f ↔ observation b g))
    (stable : ∀ (b : Obj) (residual : Hom m b), observation m answer →
      observation b (X.comp residual answer)) :
    X.Entails store observation ↔ observation m answer := by
  constructor
  · intro asked
    exact asked m answer principal.sound
  · intro holds b f solved
    obtain ⟨residual, through⟩ := principal.factors b f solved
    exact (respects b f (X.comp residual answer) through).mpr (stable b residual holds)

/-- **Equality guards are decided at a principal answer.** -/
theorem Principal.entails_models_iff {a m : Obj} {store : EquationStore (Tm a)} {answer : Hom a m}
    (principal : X.Principal store answer) (guards : EquationStore (Tm a)) :
    X.Entails store (fun _ f => X.Models f guards) ↔ X.Models answer guards :=
  principal.entails_iff (fun _ _ _ same => models_congrE same guards)
    (fun _ residual holds => models_comp holds residual)

end Frames

#print axioms Frames.models_congrE
#print axioms Frames.Principal.entails_iff
#print axioms Frames.Principal.entails_models_iff

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface
