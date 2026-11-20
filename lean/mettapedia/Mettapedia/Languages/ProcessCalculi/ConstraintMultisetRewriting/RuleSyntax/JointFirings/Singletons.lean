import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.JointFirings.Bags

/-!
# A bag of one match is a firing of the program

The step whose firing is a bag of matches (`bagStep`), restricted to bags of one member, is the step of the
program (`step`): the same admission and the same result. This holds over every frame action and every
family of extensions.

* For a bag of one member, the joint selection is the member's selection (`Bag.selection_single`), the
  joint information is the information of its firing (`Bag.information_single`), joint freshness is
  `Firing.Fresh` (`Bag.fresh_single`), the fit is `Firing.Shapes` (`Bag.fits_single`), and the joint guard
  predicate is `Firing.Holds` (`Bag.holds_single`).
* **Admission** (`Bag.admits_single`): the bag of one member is jointly admitted exactly when the member's
  firing is admitted by the step of the program. The two readings of the guards coincide on it
  (`Bag.admitsOwn_single`), and so does the member-by-member reading of enabling
  (`Bag.admitsSnapshot_single`).
* **Result** (`Bag.result_single`): the result of the bag is the result of the firing, as a state.
* **The steps** (`succ_iff_single`): a state is reached from another by the step of the program exactly
  when it is the result of an admitted bag of one member.

So the firing of `RuleSyntax.Core` is the restriction of the bag firing to one member, and nothing else.

A bag of two members is not a firing of the program in general: `Bag.single` has one member
(`Bag.single_members`), and `OneAfterAnother` and `Knowledge` say when a larger bag is a run of firings and
when it is not.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.JointFirings

open Interface (Frames)
open MeTTaCalculus.OccurrenceCommits (Enabled fire)
open LogicOverTheStep.StepSpan (Succ)

universe uO uT uH uE uOcc

variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}

namespace Bag

variable {O : Type uOcc} {E : Extensions.{uO, uH, uE} Hom} {P : Program Tm}

/-- **The bag of one firing.** -/
def single {a : Obj} (g : Firing O E P a) : Bag O E P a := ⟨g.ext, [Member.ofFiring g]⟩

theorem single_members {a : Obj} (g : Firing O E P a) : (single g).members.length = 1 := rfl

/-- The joint selection of one member is its selection. -/
theorem selection_single {a : Obj} {x : E.Ext a} (m : Member O E P x) :
    (⟨x, [m]⟩ : Bag O E P a).selection = m.selection := by
  have taken : [m].flatMap (fun m => m.selection.taken) = m.selection.taken :=
    List.flatMap_singleton _ m
  have read : [m].flatMap (fun m => m.selection.read) = m.selection.read :=
    List.flatMap_singleton _ m
  have made : [m].flatMap (fun m => m.selection.made) = m.selection.made :=
    List.flatMap_singleton _ m
  exact (by rw [taken, read, made] :
    (⟨[m].flatMap (fun m => m.selection.taken), [m].flatMap (fun m => m.selection.read),
      [m].flatMap (fun m => m.selection.made)⟩ : Selection O) =
      ⟨m.selection.taken, m.selection.read, m.selection.made⟩)

/-- The opened made rows of one member are those of its firing. -/
theorem produce_single (X : Frames Tm Hom) {a : Obj} {x : E.Ext a} (m : Member O E P x) :
    Bag.produce X (⟨x, [m]⟩ : Bag O E P a) = (m.firing.opened X).produce := by
  unfold Bag.produce
  exact List.flatMap_singleton _ m

section One

variable (X : Frames Tm Hom) (s : State Tm O) {x : E.Ext s.frame} (m : Member O E P x)

/-- **The joint information of one member is the information of its firing.** -/
theorem information_single :
    Bag.information X s (⟨x, [m]⟩ : Bag O E P s.frame) = m.firing.information X s := by
  show X.applyStore (E.weaken x) s.knowledge ++ [m].flatMap (fun m => m.own X s) = _
  rw [List.flatMap_singleton, Member.information_eq X s m]

/-- **Joint freshness of one member is the freshness of its opening.** -/
theorem fresh_single : Bag.Fresh X s (⟨x, [m]⟩ : Bag O E P s.frame) ↔ m.firing.Fresh X s := by
  constructor
  · intro fresh b g h
    exact (realized_nil X _).mp ((realized_cons X m [] _).mp (fresh b g) h)
  · intro fresh b g
    exact (realized_cons X m [] _).mpr fun h => (realized_nil X _).mpr (fresh b g h)

/-- **The fit of one member is the shapes of its firing.** -/
theorem fits_single : Bag.Fits X s (⟨x, [m]⟩ : Bag O E P s.frame) ↔ m.firing.Shapes X s := by
  unfold Bag.Fits Firing.Shapes
  rw [selection_single m, fresh_single X s m]
  constructor
  · rintro ⟨fresh, taken, made, lengths⟩
    exact ⟨fresh, taken, made, lengths m (List.mem_singleton_self m)⟩
  · rintro ⟨fresh, taken, made, lengths⟩
    refine ⟨fresh, taken, made, fun m' inside => ?_⟩
    rw [List.mem_singleton.mp inside]
    exact lengths

/-- **The joint guard predicate of one member is the guard predicate of its firing.** -/
theorem holds_single {b : Obj} (σ : Hom (E.target x) b) :
    Bag.Holds X s (⟨x, [m]⟩ : Bag O E P s.frame) σ ↔ m.firing.Holds X s σ := by
  constructor
  · intro holds
    exact holds m (List.mem_singleton_self m)
  · intro holds m' inside
    rw [List.mem_singleton.mp inside]
    exact holds

variable [DecidableEq O]

/-- **Admission of one member**: the bag of one member is jointly admitted exactly when its firing is
admitted by the step of the program. -/
theorem admits_single : Bag.Admits X s (⟨x, [m]⟩ : Bag O E P s.frame) ↔ m.firing.Admits X s := by
  have info := information_single X s m
  have sel := selection_single m
  constructor
  · rintro ⟨fits, enabled, solvable, asks⟩
    rw [sel] at enabled
    rw [info] at solvable asks
    exact ⟨(fits_single X s m).mp fits, enabled, solvable,
      fun b σ solved => (holds_single X s m σ).mp (asks b σ solved)⟩
  · rintro ⟨shapes, enabled, solvable, asks⟩
    refine ⟨(fits_single X s m).mpr shapes, ?_, ?_, ?_⟩
    · rw [sel]
      exact enabled
    · rw [info]
      exact solvable
    · rw [info]
      exact fun b σ solved => (holds_single X s m σ).mpr (asks b σ solved)

/-- **On one member the two readings of the guards coincide.** -/
theorem admitsOwn_single :
    Bag.AdmitsOwn X s (⟨x, [m]⟩ : Bag O E P s.frame) ↔ m.firing.Admits X s := by
  constructor
  · intro own
    exact (admits_single X s m).mp (admits_of_admitsOwn X own)
  · intro admitted
    obtain ⟨fits, enabled, solvable, -⟩ := (admits_single X s m).mpr admitted
    refine ⟨fits, enabled, solvable, fun m' inside => ?_⟩
    rw [List.mem_singleton.mp inside]
    exact admitted.2.2.2

/-- **On one member, enabling member by member is enabling.** -/
theorem admitsSnapshot_single :
    Bag.AdmitsSnapshot X s (⟨x, [m]⟩ : Bag O E P s.frame) ↔ m.firing.Admits X s := by
  constructor
  · rintro ⟨fits, enabled, solvable, asks⟩
    have one := enabled m (List.mem_singleton_self m)
    refine (admits_single X s m).mp ⟨fits, ?_, solvable, asks⟩
    rw [selection_single m]
    exact one
  · intro admitted
    exact admitsSnapshot_of_admits X ((admits_single X s m).mpr admitted)

/-- **The result of one member is the result of its firing.** -/
theorem result_single : Bag.result X s (⟨x, [m]⟩ : Bag O E P s.frame) = m.firing.result X s := by
  have info := information_single X s m
  have sel := selection_single m
  have made := produce_single X m
  show (⟨E.target x, Bag.information X s (⟨x, [m]⟩ : Bag O E P s.frame),
      fire s.present ((Bag.selection (⟨x, [m]⟩ : Bag O E P s.frame)).commit (T := Unit)),
      relabel (fun o => X.act (E.weaken x) (s.label o))
        (Bag.selection (⟨x, [m]⟩ : Bag O E P s.frame)).made
        (Bag.produce X (⟨x, [m]⟩ : Bag O E P s.frame))⟩ : State Tm O) =
    ⟨E.target x, m.firing.information X s, fire s.present (m.selection.commit (T := Unit)),
      relabel (fun o => X.act (E.weaken x) (s.label o)) m.selection.made (m.firing.opened X).produce⟩
  rw [info, sel, made]

end One

/-! ## The firing of the program is the bag of one member -/

section Firing

variable (X : Frames Tm Hom) [DecidableEq O] (s : State Tm O) (g : Firing O E P s.frame)

/-- **The bag of one firing is admitted exactly when the firing is.** -/
theorem single_admits_iff : (single g).Admits X s ↔ g.Admits X s :=
  admits_single X s (Member.ofFiring g)

/-- **The bag of one firing has the firing's result.** -/
theorem single_result : (single g).result X s = g.result X s :=
  result_single X s (Member.ofFiring g)

end Firing

end Bag

/-! ## The two steps -/

section Steps

variable (X : Frames Tm Hom) (O : Type uOcc) [DecidableEq O] (E : Extensions.{uO, uH, uE} Hom)
  (P : Program Tm)

/-- **The step of a program is the bag step restricted to bags of one member**: a state is reached by an
admitted firing exactly when it is the result of an admitted bag with one member. -/
theorem succ_iff_single (s s' : State Tm O) :
    Succ (step X O E P).toStep s s' ↔
      ∃ f : Bag O E P s.frame, f.members.length = 1 ∧ (bagStep X O E P).Admits f ∧ f.result X s = s' := by
  constructor
  · rintro ⟨g, admitted, rfl⟩
    exact ⟨Bag.single g, rfl, ⟨List.cons_ne_nil _ _, (Bag.single_admits_iff X s g).mpr admitted⟩,
      Bag.single_result X s g⟩
  · rintro ⟨⟨x, members⟩, one, ⟨-, admitted⟩, rfl⟩
    have one' : members.length = 1 := one
    obtain ⟨m, rfl⟩ := List.length_eq_one_iff.mp one'
    exact ⟨m.firing, (Bag.admits_single X s m).mp admitted, (Bag.result_single X s m).symm⟩

/-- **Every firing of the program is a firing of the bag step**, with the same result. -/
theorem succ_bagStep_of_succ {s s' : State Tm O} (reached : Succ (step X O E P).toStep s s') :
    Succ (bagStep X O E P).toStep s s' := by
  obtain ⟨f, -, admitted, rfl⟩ := (succ_iff_single X O E P s s').mp reached
  exact ⟨f, admitted, rfl⟩

end Steps

#print axioms Bag.selection_single
#print axioms Bag.information_single
#print axioms Bag.fresh_single
#print axioms Bag.fits_single
#print axioms Bag.holds_single
#print axioms Bag.admits_single
#print axioms Bag.admitsOwn_single
#print axioms Bag.admitsSnapshot_single
#print axioms Bag.result_single
#print axioms Bag.single_admits_iff
#print axioms Bag.single_result
#print axioms succ_iff_single
#print axioms succ_bagStep_of_succ

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.JointFirings
