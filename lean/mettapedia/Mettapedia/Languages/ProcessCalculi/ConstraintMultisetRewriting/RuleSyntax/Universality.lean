import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Interface
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.StepSpan
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FirstOrder

/-!
# What the interface of the step is: transition systems with refining knowledge

`Interface.Step` is an interface, not a calculus. This module says exactly what it is.

## The laws

Read a step as a transition system: `t` is reached from `s` when an admitted firing at `s` has
result `t` (the tree's successor relation `StepSpan.Succ`). Over states that carry a frame, knowledge and present occurrences, the
interface adds exactly these laws to a transition system (`Laws`):

* **solvable sources**: a state with an outgoing transition has solvable knowledge;
* **refinement along a frame morphism**: some morphism from the source's frame to the target's frame
  pulls every solution of the target's knowledge back to a solution of the source's;
* **commits**: the present occurrences change by an enabled commit.

Every instance obeys them (`admitted_laws`), and every relation that obeys them is the admitted
relation of an instance with exactly the given frames, knowledge and present occurrences, whose
firings at a state are its outgoing transitions (`ofLaws`, `ofLaws_admitted_iff`). Together:
`realizable_iff`. So a theorem proved once "at the interface" is a theorem about every transition
system with these three laws, and nothing more.

The third law excludes nothing: any two finite sets of occurrences are related by an enabled commit
(`commit_between`). At one frame the second law follows from the first (`oneFrame_laws_iff`): the
solution itself is a morphism. So at one frame the interface asks only that sources have solvable
knowledge, and with no knowledge it asks nothing: **every relation is an instance** (`ofLTS`,
`ofLTS_admitted_iff`), at one frame, with no occurrences and the empty store, even as a
`Step.Standard`.

Knowledge refines only up to the morphism a firing moves along, which may carry bindings. Where
firings move along the identity, as at the one-frame first-order step, knowledge genuinely only
refines (`refines_of_identity`).

## Controls

* Solvable sources: a transition out of a state whose knowledge is unsolvable is admitted by no
  instance with that knowledge (`Controls.unsolvable_source_excluded`); with solvable knowledge it is
  realized (`Controls.solvable_source_realized`).
* Refinement: knowledge that **shrinks** (from `x = 0` to nothing) is still an instance, because the
  firing's morphism may carry the binding (`Controls.shrinking_realized`); it is excluded when firings
  move along the identity (`Controls.shrinking_excluded_at_identity`). Across frames with no morphism
  between them, a transition with solvable source knowledge is excluded
  (`Controls.no_morphism_excluded`).
* Commits: a selection that takes a missing occurrence is not enabled
  (`Controls.missing_take_not_enabled`), although another commit relates the same two stores.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax

open Interface (Frames)
open MeTTaCalculus.OccurrenceCommits (Enabled fire)
open LogicOverTheStep.StepSpan (Succ)

universe uO uT uH uOcc uS uF

section Laws

variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH} (X : Frames Tm Hom)
  {O : Type uOcc} [DecidableEq O] {State : Type uS}

/-- **The laws the interface adds to a transition system** whose states carry frames, knowledge and
present occurrences, for one transition from `s` to `t`. -/
structure Laws (frame : State → Obj) (knowledge : (s : State) → EquationStore (Tm (frame s)))
    (present : State → Finset O) (s t : State) : Prop where
  solvable : X.Solvable (knowledge s)
  refines : ∃ m : Hom (frame s) (frame t), ∀ (b : Obj) (σ : Hom (frame t) b),
    X.Models σ (knowledge t) → X.Models (X.comp σ m) (knowledge s)
  commits : ∃ selection : Selection O,
    Enabled (fun _ : O => ()) (present s) (selection.commit (T := Unit)) ∧
      present t = fire (present s) (selection.commit (T := Unit))

/-- **Every instance obeys the laws.** -/
theorem admitted_laws {Firing : State → Type uF} (P : Interface.Step X O State Firing) {s t : State}
    (reached : Succ P s t) : Laws X P.frame P.knowledge P.present s t := by
  obtain ⟨f, admitted, rfl⟩ := reached
  exact ⟨P.solvable_knowledge admitted,
    ⟨P.along f admitted, fun _ σ solved => P.models_along admitted σ solved⟩,
    ⟨P.selection f, (P.prepares admitted).2.1, P.present_result f admitted⟩⟩

/-- **Every relation obeying the laws is an instance**, with the given frames, knowledge and present
occurrences. A firing at `s` is an outgoing transition; it moves along the identity, its information
is the source's knowledge, and it settles along the morphism the second law provides. -/
noncomputable def ofLaws (frame : State → Obj) (knowledge : (s : State) → EquationStore (Tm (frame s)))
    (present : State → Finset O) (R : State → State → Prop)
    (laws : ∀ s t, R s t → Laws X frame knowledge present s t) :
    Interface.Step X O State (fun s => {t : State // R s t}) where
  frame := frame
  knowledge := knowledge
  present := present
  selection f := Classical.choose (laws _ _ f.2).commits
  target {s} _ := frame s
  extension {s} _ := X.id (frame s)
  information {s} _ := knowledge s
  information_refines := by
    intro s _ b σ solved
    exact (Frames.models_congr (fun t => Frames.act_comp_id σ t) (knowledge s)).mp solved
  Shapes _ := True
  preparedResult f _ := f.1
  present_preparedResult f _ := (Classical.choose_spec (laws _ _ f.2).commits).2
  preparedSettle f _ := Classical.choose (laws _ _ f.2).refines
  result_refines := by
    intro _ f _ b σ solved
    exact Classical.choose_spec (laws _ _ f.2).refines b σ solved
  Admits _ := True
  admitted_prepares f _ :=
    ⟨trivial, (Classical.choose_spec (laws _ _ f.2).commits).1, (laws _ _ f.2).solvable⟩

variable (frame : State → Obj) (knowledge : (s : State) → EquationStore (Tm (frame s)))
  (present : State → Finset O) (R : State → State → Prop)

theorem ofLaws_frame (laws : ∀ s t, R s t → Laws X frame knowledge present s t) :
    (ofLaws X frame knowledge present R laws).frame = frame := rfl

theorem ofLaws_knowledge (laws : ∀ s t, R s t → Laws X frame knowledge present s t) :
    (ofLaws X frame knowledge present R laws).knowledge = knowledge := rfl

theorem ofLaws_present (laws : ∀ s t, R s t → Laws X frame knowledge present s t) :
    (ofLaws X frame knowledge present R laws).present = present := rfl

/-- **Its admitted relation is the given relation.** -/
theorem ofLaws_admitted_iff (laws : ∀ s t, R s t → Laws X frame knowledge present s t)
    (s t : State) : Succ (ofLaws X frame knowledge present R laws) s t ↔ R s t := by
  constructor
  · rintro ⟨f, -, rfl⟩
    exact f.2
  · intro related
    exact ⟨⟨t, related⟩, trivial, rfl⟩

/-- An instance has the given frames, knowledge and present occurrences. -/
def HasMaps {Firing : State → Type uF} (P : Interface.Step X O State Firing) : Prop :=
  (⟨P.frame, P.knowledge⟩ : Σ fr : State → Obj, (s : State) → EquationStore (Tm (fr s))) =
      ⟨frame, knowledge⟩ ∧ P.present = present

/-- **What the interface is.** A relation is the admitted relation of an instance with the given
frames, knowledge and present occurrences exactly when every transition obeys the three laws. -/
theorem realizable_iff :
    (∃ P : Interface.Step X O State (fun s => {t : State // R s t}),
        HasMaps X frame knowledge present P ∧ ∀ s t, Succ P s t ↔ R s t) ↔
      ∀ s t, R s t → Laws X frame knowledge present s t := by
  constructor
  · rintro ⟨P, ⟨maps, same⟩, admitted⟩ s t related
    have laws := admitted_laws X P ((admitted s t).mpr related)
    obtain ⟨frameEq, knowledgeEq⟩ := Sigma.mk.inj_iff.mp maps
    subst same
    subst frameEq
    have knowledgeSame : P.knowledge = knowledge := eq_of_heq knowledgeEq
    subst knowledgeSame
    exact laws
  · intro laws
    exact ⟨ofLaws X frame knowledge present R laws, ⟨rfl, rfl⟩,
      ofLaws_admitted_iff X frame knowledge present R laws⟩

end Laws

/-! ## The third law excludes nothing -/

section Commits

variable {O : Type uOcc} [DecidableEq O]

/-- **Any two finite sets of occurrences are related by an enabled commit**: take what disappears,
make what appears. -/
theorem commit_between (before after : Finset O) :
    ∃ selection : Selection O,
      Enabled (fun _ : O => ()) before (selection.commit (T := Unit)) ∧
        after = fire before (selection.commit (T := Unit)) := by
  refine ⟨⟨(before \ after).toList, [], (after \ before).toList⟩, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · intro o member
    simp only [Selection.commit, Finset.toList_toFinset, Finset.mem_sdiff] at member
    exact member.1
  · intro o member
    simp [Selection.commit] at member
  · simp [Selection.commit]
  · rw [Finset.disjoint_left]
    intro o member
    simp only [Selection.commit, Finset.toList_toFinset, Finset.mem_sdiff] at member
    exact member.2
  · intro query member
    simp [Selection.commit] at member
  · ext o
    simp only [fire, Selection.commit, Finset.toList_toFinset, Finset.mem_union, Finset.mem_sdiff]
    tauto

/-- The empty selection is enabled everywhere. -/
theorem enabled_nil (W : Finset O) :
    Enabled (fun _ : O => ()) W ((⟨[], [], []⟩ : Selection O).commit (T := Unit)) :=
  ⟨by simp [Selection.commit], by simp [Selection.commit], by simp [Selection.commit],
    by simp [Selection.commit], by simp [Selection.commit]⟩

end Commits

/-! ## One frame -/

section OneFrame

universe uA uB

variable {T : Type uA} {S : Type uB} (A : SubstitutionAction T S) {O : Type uOcc} [DecidableEq O]
  {State : Type uS}

/-- **At one frame the second law follows from the first**: a solution of the source's knowledge is
itself a morphism into the one frame, and every later solution composed with it still solves. So the
laws ask only for consistent source knowledge. -/
theorem oneFrame_laws_iff (knowledge : State → EquationStore T) (present : State → Finset O)
    (s t : State) :
    Laws (Frames.ofSubstitution A) (fun _ => PUnit.unit) knowledge present s t ↔
      A.Consistent (knowledge s) := by
  constructor
  · intro laws
    exact (Frames.ofSubstitution_solvable_iff A (knowledge s)).mp laws.solvable
  · intro consistent
    obtain ⟨θ, solved⟩ := consistent
    refine ⟨(Frames.ofSubstitution_solvable_iff A (knowledge s)).mpr ⟨θ, solved⟩, ⟨θ, ?_⟩,
      commit_between _ _⟩
    intro _ σ _
    exact Frames.models_comp (X := Frames.ofSubstitution A) (a := PUnit.unit) (b := PUnit.unit)
      (f := θ) solved σ

/-- **When firings move along the identity, knowledge genuinely only refines**: every solution of
the target's knowledge solves the source's. -/
theorem refines_of_identity {Firing : State → Type uF}
    (P : Interface.Step (Frames.ofSubstitution A) O State Firing)
    (identity : ∀ {s : State} (f : Firing s) (admitted : P.Admits f) (t : T),
      A.apply (P.along f admitted) t = t)
    {s t : State} (reached : Succ P s t) :
    A.Refines (P.knowledge t) (P.knowledge s) := by
  obtain ⟨f, admitted, rfl⟩ := reached
  intro σ solved e member
  have back : A.E (A.apply (A.compose σ (P.along f admitted)) e.1)
      (A.apply (A.compose σ (P.along f admitted)) e.2) :=
    P.models_along admitted (b := PUnit.unit) σ solved e member
  rw [A.apply_compose, A.apply_compose, identity, identity] at back
  exact back

/-- The point action: one term and one substitution. -/
def pointAction : SubstitutionAction PUnit.{1} PUnit.{1} where
  E := Eq
  equivalence := ⟨Eq.refl, Eq.symm, Eq.trans⟩
  apply _ t := t
  identity := PUnit.unit
  compose _ _ := PUnit.unit
  apply_identity _ := rfl
  apply_compose _ _ _ := rfl
  preserves := fun _ {_ _} same => same

/-- **Every relation is an instance**: one frame, the empty store, no occurrences; the firings at a
state are its outgoing transitions, and every one is admitted. -/
def ofLTS {S : Type uS} (R : S → S → Prop) (O : Type uOcc) [DecidableEq O] :
    Interface.Step.Standard (Frames.ofSubstitution pointAction) O S (fun s => {t : S // R s t}) where
  frame _ := PUnit.unit
  knowledge _ := []
  present _ := ∅
  selection _ := ⟨[], [], []⟩
  target _ := PUnit.unit
  extension _ := PUnit.unit
  information _ := []
  transported := by
    intro _ _ _ member
    cases member
  Shapes _ := True
  Holds _ _ _ := True
  Admits _ := True
  admits_iff := by
    intro _ _
    exact ⟨fun _ => ⟨trivial, enabled_nil ∅,
      ⟨PUnit.unit, PUnit.unit, Frames.models_nil (X := Frames.ofSubstitution pointAction) _⟩,
      fun _ _ _ => trivial⟩, fun _ => trivial⟩
  preparedResult f _ := f.1
  present_preparedResult _ _ := by simp [fire, Selection.commit]
  preparedSettle _ _ := PUnit.unit
  knowledge_preparedResult _ _ := rfl

/-- **The admitted relation of `ofLTS R` is `R`.** -/
theorem ofLTS_admitted_iff {S : Type uS} (R : S → S → Prop) (O : Type uOcc) [DecidableEq O]
    (s t : S) : Succ (ofLTS R O).toStep s t ↔ R s t := by
  constructor
  · rintro ⟨f, -, rfl⟩
    exact f.2
  · intro related
    exact ⟨⟨t, related⟩, trivial, rfl⟩

end OneFrame

/-! ## Controls -/

namespace Controls

open Mettapedia.Logic.LP

/-- Terms for the controls: numerals as constants and as variables, no function symbols. -/
abbrev atoms : LPSignature where
  constants := ℕ
  vars := ℕ
  relationSymbols := Empty
  relationArity := Empty.elim
  functionSymbols := Empty
  functionArity := Empty.elim

/-- The first-order action on these terms. -/
abbrev action : SubstitutionAction (Term atoms) (Subst atoms) := FirstOrder.action atoms

/-- Its one-frame frame action. -/
abbrev frames := Frames.ofSubstitution action

/-- Distinct constants are never equated. -/
theorem const_apart (σ : Subst atoms) {m n : ℕ} (different : m ≠ n) :
    ¬ action.Solves σ (Term.const m, Term.const n) := by
  intro same
  exact different (Term.const.inj same)

/-- The one transition `false → true`. -/
def forward : Bool → Bool → Prop := fun s t => s = false ∧ t = true

/-- Knowledge that equates two distinct constants at `false`. -/
def contradictory : Bool → EquationStore (Term atoms)
  | false => [(Term.const 0, Term.const 1)]
  | true => []

/-- **An unsolvable source is excluded**: no instance with this knowledge admits `false → true`. -/
theorem unsolvable_source_excluded {Firing : Bool → Type uF}
    (P : Interface.Step frames ℕ Bool Firing) (knows : ∀ s, P.knowledge s = contradictory s) :
    ¬ Succ P false true := by
  intro reached
  have solvable := (admitted_laws frames P reached).solvable
  rw [knows false] at solvable
  obtain ⟨θ, solved⟩ := (Frames.ofSubstitution_solvable_iff action _).mp solvable
  exact const_apart θ (by decide : (0 : ℕ) ≠ 1) (solved _ List.mem_cons_self)

/-- **With solvable knowledge the same transition is realized.** -/
theorem solvable_source_realized :
    ∃ P : Interface.Step frames ℕ Bool (fun s => {t : Bool // forward s t}),
      (∀ s, P.knowledge s = []) ∧ ∀ s t, Succ P s t ↔ forward s t := by
  have laws : ∀ s t, forward s t →
      Laws frames (fun _ => PUnit.unit) (fun _ => ([] : EquationStore (Term atoms)))
        (fun _ => (∅ : Finset ℕ)) s t := fun s t _ =>
    (oneFrame_laws_iff action _ _ s t).mpr ⟨Subst.id atoms, fun _ member => by cases member⟩
  exact ⟨ofLaws frames _ _ _ forward laws, fun _ => rfl, ofLaws_admitted_iff frames _ _ _ forward laws⟩

/-- Knowledge that **shrinks** along `false → true`: `x = 0`, then nothing. -/
def shrinking : Bool → EquationStore (Term atoms)
  | false => [(Term.var 0, Term.const 0)]
  | true => []

/-- **Shrinking knowledge is still an instance**: the firing's morphism carries the binding. -/
theorem shrinking_realized :
    ∃ P : Interface.Step frames ℕ Bool (fun s => {t : Bool // forward s t}),
      (∀ s, P.knowledge s = shrinking s) ∧ ∀ s t, Succ P s t ↔ forward s t := by
  have laws : ∀ s t, forward s t →
      Laws frames (fun _ => PUnit.unit) shrinking (fun _ => (∅ : Finset ℕ)) s t := by
    rintro s t ⟨rfl, rfl⟩
    refine (oneFrame_laws_iff action shrinking _ false true).mpr ⟨fun _ => Term.const 0, ?_⟩
    intro e member
    obtain rfl := List.mem_singleton.mp member
    rfl
  exact ⟨ofLaws frames _ _ _ forward laws, fun _ => rfl, ofLaws_admitted_iff frames _ _ _ forward laws⟩

/-- **Shrinking knowledge is excluded when firings move along the identity.** -/
theorem shrinking_excluded_at_identity {Firing : Bool → Type uF}
    (P : Interface.Step frames ℕ Bool Firing) (knows : ∀ s, P.knowledge s = shrinking s)
    (identity : ∀ {s : Bool} (f : Firing s) (admitted : P.Admits f) (t : Term atoms),
      action.apply (P.along f admitted) t = t) :
    ¬ Succ P false true := by
  intro reached
  have refines := refines_of_identity action P identity reached
  rw [knows false, knows true] at refines
  have solved := refines (fun _ => Term.const 1) (fun _ member => by cases member)
  have one := solved (Term.var 0, Term.const 0) (by simp [shrinking])
  exact const_apart (fun _ => Term.const 1) (by decide : (1 : ℕ) ≠ 0) one

/-- Two frames and no morphism between them. -/
def discrete : Frames (fun _ : Bool => PUnit.{1}) (fun a b : Bool => PLift (a = b)) where
  E := Eq
  equivalence _ := ⟨Eq.refl, Eq.symm, Eq.trans⟩
  act _ t := t
  id _ := ⟨rfl⟩
  comp g f := ⟨f.down.trans g.down⟩
  act_id _ := rfl
  act_comp _ _ _ := rfl
  preserves := by
    intro _ _ _ _ _ same
    exact same

/-- **Across frames with no morphism, a transition is excluded** although its source knowledge is
solvable. -/
theorem no_morphism_excluded {Firing : Bool → Type uF} (P : Interface.Step discrete ℕ Bool Firing)
    (frames : ∀ s, P.frame s = s) : ¬ Succ P false true := by
  intro reached
  obtain ⟨m, -⟩ := (admitted_laws discrete P reached).refines
  have same := m.down
  rw [frames false, frames true] at same
  exact Bool.false_ne_true same

/-- The empty knowledge is solvable at either frame, so the first law holds there. -/
theorem discrete_solvable (s : Bool) : discrete.Solvable (a := s) [] :=
  ⟨s, ⟨rfl⟩, fun _ member => by cases member⟩

/-- **A selection that takes a missing occurrence is not enabled.** -/
theorem missing_take_not_enabled :
    ¬ Enabled (fun _ : ℕ => ()) ∅ ((⟨[0], [], []⟩ : Selection ℕ).commit (T := Unit)) := by
  intro enabled
  have inside := enabled.taken_subset
    (show (0 : ℕ) ∈ ((⟨[0], [], []⟩ : Selection ℕ).commit (T := Unit)).taken by
      simp [Selection.commit])
  simp at inside

end Controls

#print axioms admitted_laws
#print axioms ofLaws_admitted_iff
#print axioms realizable_iff
#print axioms commit_between
#print axioms oneFrame_laws_iff
#print axioms refines_of_identity
#print axioms ofLTS_admitted_iff
#print axioms Controls.unsolvable_source_excluded
#print axioms Controls.solvable_source_realized
#print axioms Controls.shrinking_realized
#print axioms Controls.shrinking_excluded_at_identity
#print axioms Controls.no_morphism_excluded
#print axioms Controls.missing_take_not_enabled

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax
