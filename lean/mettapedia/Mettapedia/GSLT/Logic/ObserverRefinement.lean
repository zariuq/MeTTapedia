import Mettapedia.GSLT.Logic.HennessyMilnerTransport
import Mathlib.CategoryTheory.Opposites

/-!
# Observer refinement and behavioral refinement

An observer does not discover a single context-free identity relation.  It
selects atoms and interactions that states must agree on.  Refining an
observer may add distinctions; forgetting those distinctions maps the finer
behavioral quotient to the coarser one.

`ObserverRefinement coarse fine` records this direction explicitly.  Every
coarse atom and label is represented exactly by a fine one.  The fine system
may still contain additional atoms or labels.  Consequently:

* fine bisimilarity implies coarse bisimilarity;
* fine behavioral classes map canonically to coarse behavioral classes;
* refinements compose, and so do their quotient maps; and
* if the atom and label maps are surjective, the two observers induce the
  same identity relation.

This is an observer-indexed notion of refinement, not equality reflection.  It does
not turn behavioral identity into judgmental equality or an identity proof.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.HennessyMilner

open Mettapedia.GSLT
open scoped CategoryTheory

universe uS uAtomCoarse uLabelCoarse uAtomMiddle uLabelMiddle
  uAtomFine uLabelFine

variable {S : GSLT.{uS}}

namespace System

/-- Behavioral identity classes for one labeled observational system. -/
def behavioralSetoid (M : System.{uAtomCoarse, uLabelCoarse} S) : Setoid S.Term where
  r := M.Bisimilar
  iseqv :=
    ⟨M.bisimilar_refl,
      fun equivalent => M.bisimilar_symm equivalent,
      fun first second => M.bisimilar_trans first second⟩

/-- The quotient of states by one observer's behavioral identity. -/
def BehavioralClass (M : System.{uAtomCoarse, uLabelCoarse} S) : Type uS :=
  Quotient M.behavioralSetoid

/-- Send a state to its behavioral identity class. -/
def toBehavioralClass (M : System.{uAtomCoarse, uLabelCoarse} S)
    (term : S.Term) : M.BehavioralClass :=
  Quotient.mk M.behavioralSetoid term

theorem behavioralClass_eq_iff (M : System.{uAtomCoarse, uLabelCoarse} S)
    (left right : S.Term) :
    M.toBehavioralClass left = M.toBehavioralClass right ↔ M.Bisimilar left right :=
  Quotient.eq

end System

/-! ## Refining what can be observed -/

/-- A refinement of observation at fixed operational states.  Every coarse
atom and labeled transition has an exactly represented fine counterpart.
Additional fine atoms and labels may distinguish states that the coarse
observer identifies. -/
structure ObserverRefinement
    (coarse : System.{uAtomCoarse, uLabelCoarse} S)
    (fine : System.{uAtomFine, uLabelFine} S) where
  mapAtom : coarse.Atom → fine.Atom
  mapLabel : coarse.Label → fine.Label
  observes_iff : ∀ (atom : coarse.Atom) (term : S.Term),
    coarse.observes atom term ↔ fine.observes (mapAtom atom) term
  act_iff : ∀ (label : coarse.Label) (source target : S.Term),
    coarse.act label source target ↔ fine.act (mapLabel label) source target

namespace ObserverRefinement

variable
  {coarse : System.{uAtomCoarse, uLabelCoarse} S}
  {middle : System.{uAtomMiddle, uLabelMiddle} S}
  {fine : System.{uAtomFine, uLabelFine} S}

@[ext]
theorem ext {first second : ObserverRefinement coarse fine}
    (atoms : first.mapAtom = second.mapAtom)
    (labels : first.mapLabel = second.mapLabel) : first = second := by
  cases first
  cases second
  cases atoms
  cases labels
  rfl

/-- Refining by the same observer changes nothing. -/
def id (M : System.{uAtomCoarse, uLabelCoarse} S) : ObserverRefinement M M where
  mapAtom := _root_.id
  mapLabel := _root_.id
  observes_iff := fun _ _ => Iff.rfl
  act_iff := fun _ _ _ => Iff.rfl

/-- Observer refinements compose from coarse to fine. -/
def comp (first : ObserverRefinement coarse middle)
    (second : ObserverRefinement middle fine) : ObserverRefinement coarse fine where
  mapAtom := second.mapAtom ∘ first.mapAtom
  mapLabel := second.mapLabel ∘ first.mapLabel
  observes_iff := fun atom term =>
    (first.observes_iff atom term).trans
      (second.observes_iff (first.mapAtom atom) term)
  act_iff := fun label source target =>
    (first.act_iff label source target).trans
      (second.act_iff (first.mapLabel label) source target)

/-- An observer refinement is an exact labeled-system cover whose state map
is the identity. -/
def toSystemCover (refinement : ObserverRefinement coarse fine) :
    SystemCover coarse fine where
  mapTerm := _root_.id
  mapAtom := refinement.mapAtom
  mapLabel := refinement.mapLabel
  mapEquiv := fun equivalent => equivalent
  observes_iff := refinement.observes_iff
  mapAct := fun step => (refinement.act_iff _ _ _).mp step
  liftAct := by
    intro label source target step
    exact ⟨target, (refinement.act_iff label source target).mpr step,
      S.equations.iseqv.refl target⟩

/-- Every formula available to the coarse observer has exactly the same
truth value after it is translated to the finer observer.  Fine-only formulas
may still distinguish additional states. -/
theorem sat_refine (refinement : ObserverRefinement coarse fine)
    (formula : Formula coarse.Atom coarse.Label) (term : S.Term) :
    fine.sat (formula.map refinement.mapAtom refinement.mapLabel) term ↔
      coarse.sat formula term := by
  simpa [toSystemCover] using refinement.toSystemCover.sat_map formula term

/-- The same exact translation law for the negation-free fragment. -/
theorem psat_refine (refinement : ObserverRefinement coarse fine)
    (formula : PosFormula coarse.Atom coarse.Label) (term : S.Term) :
    fine.psat (formula.map refinement.mapAtom refinement.mapLabel) term ↔
      coarse.psat formula term := by
  simpa [toSystemCover] using refinement.toSystemCover.psat_map formula term

/-- Any identity visible to a finer observer remains an identity after
forgetting distinctions. -/
theorem bisimilar_forget (refinement : ObserverRefinement coarse fine)
    {left right : S.Term} (bisimilar : fine.Bisimilar left right) :
    coarse.Bisimilar left right := by
  simpa using refinement.toSystemCover.bisimilar_of_map bisimilar

/-- Forgetting observational distinctions induces a canonical map from fine
behavioral classes to coarse behavioral classes. -/
def classMap (refinement : ObserverRefinement coarse fine) :
    fine.BehavioralClass → coarse.BehavioralClass :=
  Quotient.map _root_.id fun _ _ equivalent =>
    refinement.bisimilar_forget equivalent

@[simp]
theorem classMap_toBehavioralClass (refinement : ObserverRefinement coarse fine)
    (term : S.Term) :
    refinement.classMap (fine.toBehavioralClass term) =
      coarse.toBehavioralClass term :=
  rfl

/-- Identity refinement has the identity quotient map. -/
theorem classMap_id (M : System.{uAtomCoarse, uLabelCoarse} S) :
    (ObserverRefinement.id M).classMap = _root_.id := by
  funext stateClass
  induction stateClass using Quotient.inductionOn with
  | _ term => rfl

/-- Refining through an intermediate observer agrees with direct refinement. -/
theorem classMap_comp (first : ObserverRefinement coarse middle)
    (second : ObserverRefinement middle fine) :
    (first.comp second).classMap = first.classMap ∘ second.classMap := by
  funext stateClass
  induction stateClass using Quotient.inductionOn with
  | _ term => rfl

/-- A refinement that reaches every fine atom and label changes notation but
not behavioral identity. -/
theorem bisimilar_iff_of_surjective
    (refinement : ObserverRefinement coarse fine)
    (atomSurjective : Function.Surjective refinement.mapAtom)
    (labelSurjective : Function.Surjective refinement.mapLabel)
    (left right : S.Term) :
    fine.Bisimilar left right ↔ coarse.Bisimilar left right := by
  constructor
  · exact refinement.bisimilar_forget
  · intro bisimilar
    change fine.Bisimilar
      (refinement.toSystemCover.mapTerm left)
      (refinement.toSystemCover.mapTerm right)
    exact refinement.toSystemCover.bisimilar_map
      atomSurjective labelSurjective bisimilar

/-- With no new atoms or labels, refinement is reversible on behavioral classes. -/
theorem classMap_injective_of_surjective
    (refinement : ObserverRefinement coarse fine)
    (atomSurjective : Function.Surjective refinement.mapAtom)
    (labelSurjective : Function.Surjective refinement.mapLabel) :
    Function.Injective refinement.classMap := by
  intro first second equalImages
  induction first using Quotient.inductionOn with
  | _ left =>
      induction second using Quotient.inductionOn with
      | _ right =>
          apply Quotient.sound
          apply (refinement.bisimilar_iff_of_surjective
            atomSurjective labelSurjective left right).2
          exact Quotient.exact equalImages

end ObserverRefinement

/-! ## The category of observers -/

/-- One observer of a fixed operational system.  Atom and label universes are
fixed only so these objects form an ordinary locally small category. -/
structure ObserverObject (S : GSLT.{uS}) where
  system : System.{uAtomCoarse, uLabelCoarse} S

namespace ObserverObject

instance : CategoryTheory.Category
    (ObserverObject.{uS, uAtomCoarse, uLabelCoarse} S) where
  Hom source target := ObserverRefinement source.system target.system
  id object := ObserverRefinement.id object.system
  comp earlier later := earlier.comp later
  id_comp refinement := by
    apply ObserverRefinement.ext <;> rfl
  comp_id refinement := by
    apply ObserverRefinement.ext <;> rfl
  assoc first second third := by
    apply ObserverRefinement.ext <;> rfl

/-- Behavioral identity is contravariant in observational precision: an
arrow from a coarse observer to a fine observer induces a function from fine
classes back to coarse classes. -/
def behavioralClasses :
    CategoryTheory.Functor (Opposite (ObserverObject S)) (Type uS) where
  obj observer := observer.unop.system.BehavioralClass
  map refinement := ↾ refinement.unop.classMap
  map_id observer := by
    ext stateClass
    induction stateClass using Quotient.inductionOn with
    | _ term => rfl
  map_comp first second := by
    ext stateClass
    induction stateClass using Quotient.inductionOn with
    | _ term => rfl

end ObserverObject

/-! ## A non-collapse canary -/

namespace ObserverRefinementCanary

/-- Two inert states: all distinctions in this specimen come from the
observer, not from transition structure. -/
def states : GSLT where
  Term := Bool
  equations := ⟨Eq, ⟨Eq.refl, Eq.symm, Eq.trans⟩⟩
  rewrites := fun _ _ => False
  rewrites_resp_left := fun _ impossible => impossible.elim
  rewrites_resp_right := fun impossible _ => impossible.elim

/-- The coarse observer asks only the always-true question. -/
def coarse : System.{0, 0} states where
  Atom := Unit
  observes := fun _ _ => True
  observes_resp := by
    intro _ _ _ _
    exact Iff.rfl
  Label := Unit
  act := fun _ _ _ => False
  act_resp_left := fun _ impossible => impossible.elim
  act_resp_right := fun impossible _ => impossible.elim

/-- The fine observer retains the coarse question and additionally asks for
the exact Boolean state. -/
def fine : System.{0, 0} states where
  Atom := Unit ⊕ Bool
  observes
    | .inl _, _ => True
    | .inr expected, actual => expected = actual
  observes_resp := by
    intro atom left right equal
    subst right
    exact Iff.rfl
  Label := Unit
  act := fun _ _ _ => False
  act_resp_left := fun _ impossible => impossible.elim
  act_resp_right := fun impossible _ => impossible.elim

/-- The coarse questions embed into the fine observer. -/
def refinement : ObserverRefinement coarse fine where
  mapAtom := Sum.inl
  mapLabel := _root_.id
  observes_iff := fun _ _ => Iff.rfl
  act_iff := fun _ _ _ => Iff.rfl

/-- At coarse resolution the two states are behaviorally identical. -/
theorem coarse_identifies : coarse.Bisimilar false true := by
  refine ⟨fun _ _ => True, ⟨?_, ?_, ?_⟩, trivial⟩
  · intro _ _ _ _ _ impossible
    exact impossible.elim
  · intro _ _ _ _ _ impossible
    exact impossible.elim
  · intro _ _ _ _
    exact Iff.rfl

/-- At fine resolution one atom separates the two states. -/
theorem fine_distinguishes : ¬ fine.Bisimilar false true := by
  rintro ⟨relation, ⟨_, _, atoms⟩, related⟩
  have impossible := (atoms related (Sum.inr false)).mp rfl
  exact Bool.false_ne_true impossible

/-- Coarsening genuinely loses information: its class map is not injective. -/
theorem refinement_not_injective : ¬ Function.Injective refinement.classMap := by
  intro injective
  apply fine_distinguishes
  apply (fine.behavioralClass_eq_iff false true).1
  apply injective
  exact (coarse.behavioralClass_eq_iff false true).2 coarse_identifies

end ObserverRefinementCanary

#print axioms ObserverRefinement.bisimilar_forget
#print axioms ObserverRefinement.sat_refine
#print axioms ObserverRefinement.psat_refine
#print axioms ObserverRefinement.bisimilar_iff_of_surjective
#print axioms ObserverRefinement.classMap_comp
#print axioms ObserverRefinement.classMap_injective_of_surjective
#print axioms ObserverObject.behavioralClasses
#print axioms ObserverRefinementCanary.coarse_identifies
#print axioms ObserverRefinementCanary.fine_distinguishes
#print axioms ObserverRefinementCanary.refinement_not_injective

end Mettapedia.GSLT.HennessyMilner
