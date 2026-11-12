import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Independence
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualPatternTermination

/-!
# The smallest contextual instance: firings that make fresh helpers

A **helper firing** makes one occurrence and one fresh helper metavariable, and tells the
helper's value, a term over the frame it fires at (`Helpers.helperStep`). Its result lives at the
frame with one more name (`Helpers.extend`), so a second firing lives in the frame the first made.
Its guards are equations on the names of the frame it fires at, asked at every solution; it has no
predicate queries. It is an instance of the candidate step over the canonical category of
declaration frames.

* **Transport** (`Helpers.helperTransport`): isomorphisms of states are the interface's (frames
  related by contextual assignments that are inverse on terms, knowledge with the same solutions,
  occurrences related by a renaming). A firing moves by instantiating its value and renaming the
  occurrence it makes (`Firing.carry`); its result moves along the isomorphism lifted to the extended
  frames (`Helpers.liftIso`), which fixes the fresh helper, with the same renaming. The
  residual of a firing after another is its value instantiated along the other's morphism of frames.
* **Admission** is solvable knowledge, a fresh occurrence, and guards asked by the knowledge
  (`admits_iff`): the helper is fresh, so its equation never constrains old names
  (`extendSolution_models`, `entails_information_iff`). Asks of guards are carried along
  isomorphisms (`Frames.Iso.entails_applyStore_iff`).
* **The diamond closes only up to renaming** (`helper_closes`): firing `f` then `g` and firing `g`
  then `f` reach frames whose two helpers sit in the two orders; swapping them (`Helpers.swapIso`) is
  an isomorphism of the results that fixes every old name (`swap_incl_incl`). Independence is exactly
  solvable knowledge, fresh and distinct occurrences, and the guards of both firings asked by the
  knowledge (`independent_iff`).
* **The consumer** (`Consumer`): two firings at the empty frame, helpers of different arities,
  independent, with their residuals computed; the composite states are different
  (`Consumer.composites_differ`) and isomorphic.
* **Deciding it.** In the pattern fibre, the structural-pattern driver decides solvability of
  the knowledge (`pattern_solvable_iff`, `pattern_unsolvable_iff`). `helperCheck` answers
  independent, dependent or unknown at a solver budget; it is sound at every budget, it answers at
  some budget on pattern knowledge for guard-free firings (`helperCheck_decides`), and off the
  pattern fragment it answers
  unknown (`helperCheck_unknown`). The control `NonPattern` has knowledge `M(c) = c`, outside the
  fragment and solvable: its pair is independent, and the check answers unknown at every budget.
  The definition of independence never chooses a solution: the knowledge stays a residual store.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits (Enabled fire)
open Interface.Frames (Frame)

namespace Frames

universe uO uT uH

variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH} {X : Frames Tm Hom}

theorem applyStore_append {a b : Obj} (f : Hom a b) (one two : EquationStore (Tm a)) :
    X.applyStore f (one ++ two) = X.applyStore f one ++ X.applyStore f two :=
  List.map_append ..

theorem applyStore_applyStore {a b c : Obj} (f : Hom a b) (g : Hom b c) (store : EquationStore (Tm a)) :
    X.applyStore g (X.applyStore f store) = X.applyStore (X.comp g f) store := by
  unfold applyStore
  rw [List.map_map]
  congr 1
  funext e
  simp only [Function.comp, X.act_comp]

theorem Equivalent.append_right {a : Obj} {one two : EquationStore (Tm a)} (same : X.Equivalent one two)
    (rest : EquationStore (Tm a)) : X.Equivalent (one ++ rest) (two ++ rest) := by
  intro b f
  rw [models_append, models_append, same b f]

/-- **Asks of guards are carried along an isomorphism**: a transported store asks the transported
guards exactly when the store asks the guards. -/
theorem Iso.entails_applyStore_iff {a b : Obj} (φ : X.Iso a b) (store guards : EquationStore (Tm a)) :
    X.Entails (X.applyStore φ.hom store) (fun _ σ => X.Models σ (X.applyStore φ.hom guards)) ↔
      X.Entails store (fun _ σ => X.Models σ guards) := by
  have back : ∀ {c : Obj} (τ : Hom a c) (t : Tm a), X.E (X.act (X.comp (X.comp τ φ.inv) φ.hom) t) (X.act τ t) :=
    fun τ t => by
      simp only [X.act_comp]
      exact X.preserves τ (φ.inv_hom t)
  constructor
  · intro asked c τ solved
    have moved : X.Models (X.comp τ φ.inv) (X.applyStore φ.hom store) :=
      (models_applyStore φ.hom (X.comp τ φ.inv) store).mpr ((models_congrE (back τ) store).mpr solved)
    have holds := (models_applyStore φ.hom (X.comp τ φ.inv) guards).mp (asked c (X.comp τ φ.inv) moved)
    exact (models_congrE (back τ) guards).mp holds
  · intro asked c σ solved
    exact (models_applyStore φ.hom σ guards).mpr
      (asked c (X.comp σ φ.hom) ((models_applyStore φ.hom σ store).mp solved))

end Frames

namespace Helpers

variable {S : Signature}

/-! ## Frames with one more helper -/

/-- The frame with one more name, the fresh helper. -/
abbrev extend (F : Frame S) (helper : MetaArity S) : Frame S :=
  ⟨F.Names ⊕ Unit, Sum.elim F.arity fun _ => helper⟩

/-- The old names inside the extended frame. -/
def incl (F : Frame S) (helper : MetaArity S) : Assignment F.arity (extend F helper).arity :=
  fun name => generator (extend F helper).arity (.inl name)

/-- The fresh helper. -/
def fresh (F : Frame S) (helper : MetaArity S) :
    Term (signature S (extend F helper).arity) helper.1 helper.2 :=
  generator (extend F helper).arity (.inr ())

/-- A morphism of frames lifted to the frames with one more helper; it fixes the helper. -/
def lift {F G : Frame S} (φ : Assignment F.arity G.arity) (helper : MetaArity S) :
    Assignment (extend F helper).arity (extend G helper).arity
  | .inl name => instantiate (incl G helper) (φ name)
  | .inr () => fresh G helper

theorem compose_lift_incl {F G : Frame S} (φ : Assignment F.arity G.arity) (helper : MetaArity S) :
    Assignment.compose (lift φ helper) (incl F helper) = Assignment.compose (incl G helper) φ := by
  funext name
  exact instantiate_generator (lift φ helper) (.inl name)

theorem instantiate_lift_fresh {F G : Frame S} (φ : Assignment F.arity G.arity) (helper : MetaArity S) :
    instantiate (lift φ helper) (fresh F helper) = fresh G helper :=
  instantiate_generator (lift φ helper) (.inr ())

theorem lift_compose {F G H : Frame S} (φ : Assignment F.arity G.arity)
    (ψ : Assignment G.arity H.arity) (helper : MetaArity S) :
    Assignment.compose (lift ψ helper) (lift φ helper) = lift (Assignment.compose ψ φ) helper := by
  funext name
  cases name with
  | inl name =>
      calc instantiate (lift ψ helper) (instantiate (incl G helper) (φ name))
          = instantiate (Assignment.compose (lift ψ helper) (incl G helper)) (φ name) :=
            (Assignment.instantiate_compose _ _ _).symm
        _ = instantiate (Assignment.compose (incl H helper) ψ) (φ name) := by rw [compose_lift_incl]
        _ = instantiate (incl H helper) (instantiate ψ (φ name)) := Assignment.instantiate_compose _ _ _
  | inr star =>
      cases star
      exact instantiate_lift_fresh ψ helper

theorem lift_generator (F : Frame S) (helper : MetaArity S) :
    lift (generator F.arity) helper = generator (extend F helper).arity := by
  funext name
  cases name with
  | inl name => exact instantiate_generator (incl F helper) name
  | inr star =>
      cases star
      rfl

/-- The inverse law of a contextual isomorphism, on assignments. -/
theorem compose_inv_hom {F G : Frame S} (φ : (Frames.contextual S).Iso F G) :
    Assignment.compose φ.inv φ.hom = generator F.arity := by
  funext name
  have law := φ.inv_hom (observe (generator F.arity name))
  change instantiateObservation φ.inv (instantiateObservation φ.hom (observe (generator F.arity name))) =
    observe (generator F.arity name) at law
  rw [instantiateObservation_observe, instantiateObservation_observe] at law
  have terms := observe_injective law
  rw [instantiate_generator] at terms
  exact terms

theorem compose_hom_inv {F G : Frame S} (φ : (Frames.contextual S).Iso F G) :
    Assignment.compose φ.hom φ.inv = generator G.arity :=
  compose_inv_hom φ.symm

/-- **An isomorphism of frames lifts to the frames with one more helper.** -/
def liftIso {F G : Frame S} (φ : (Frames.contextual S).Iso F G) (helper : MetaArity S) :
    (Frames.contextual S).Iso (extend F helper) (extend G helper) where
  hom := lift φ.hom helper
  inv := lift φ.inv helper
  inv_hom t := by
    show instantiateObservation (lift φ.inv helper) (instantiateObservation (lift φ.hom helper) t) = t
    rw [instantiateObservation_comp, lift_compose, compose_inv_hom, lift_generator,
      instantiateObservation_identity]
  hom_inv t := by
    show instantiateObservation (lift φ.hom helper) (instantiateObservation (lift φ.inv helper) t) = t
    rw [instantiateObservation_comp, lift_compose, compose_hom_inv, lift_generator,
      instantiateObservation_identity]

/-- Two helpers made in one order, read in the other. -/
def swap (F : Frame S) (first second : MetaArity S) :
    Assignment (extend (extend F first) second).arity (extend (extend F second) first).arity
  | .inl (.inl name) => generator (extend (extend F second) first).arity (.inl (.inl name))
  | .inl (.inr ()) => generator (extend (extend F second) first).arity (.inr ())
  | .inr () => generator (extend (extend F second) first).arity (.inl (.inr ()))

theorem swap_swap (F : Frame S) (first second : MetaArity S) :
    Assignment.compose (swap F second first) (swap F first second) =
      generator (extend (extend F first) second).arity := by
  funext name
  rcases name with (name | star) | star
  · exact instantiate_generator (swap F second first) (.inl (.inl name))
  · cases star
    exact instantiate_generator (swap F second first) (.inr ())
  · cases star
    exact instantiate_generator (swap F second first) (.inl (.inr ()))

/-- **Swapping two helpers is an isomorphism of frames.** -/
def swapIso (F : Frame S) (first second : MetaArity S) :
    (Frames.contextual S).Iso (extend (extend F first) second) (extend (extend F second) first) where
  hom := swap F first second
  inv := swap F second first
  inv_hom t := by
    show instantiateObservation (swap F second first) (instantiateObservation (swap F first second) t) = t
    rw [instantiateObservation_comp, swap_swap, instantiateObservation_identity]
  hom_inv t := by
    show instantiateObservation (swap F first second) (instantiateObservation (swap F second first) t) = t
    rw [instantiateObservation_comp, swap_swap, instantiateObservation_identity]

theorem swap_incl_incl (F : Frame S) (first second : MetaArity S) :
    Assignment.compose (swap F first second)
        (Assignment.compose (incl (extend F first) second) (incl F first)) =
      Assignment.compose (incl (extend F second) first) (incl F second) := by
  funext name
  show instantiate (swap F first second)
      (instantiate (incl (extend F first) second) (generator (extend F first).arity (.inl name))) =
    instantiate (incl (extend F second) first) (generator (extend F second).arity (.inl name))
  rw [instantiate_generator, instantiate_generator]
  exact instantiate_generator (swap F first second) (.inl (.inl name))

theorem swap_incl_fresh (F : Frame S) (first second : MetaArity S) :
    instantiate (swap F first second) (instantiate (incl (extend F first) second) (fresh F first)) =
      fresh (extend F second) first := by
  show instantiate (swap F first second)
      (instantiate (incl (extend F first) second) (generator (extend F first).arity (.inr ()))) = _
  rw [instantiate_generator]
  exact instantiate_generator (swap F first second) (.inl (.inr ()))

theorem swap_fresh (F : Frame S) (first second : MetaArity S) :
    instantiate (swap F first second) (fresh (extend F first) second) =
      instantiate (incl (extend F second) first) (fresh F second) := by
  show instantiate (swap F first second) (generator (extend (extend F first) second).arity (.inr ())) =
    instantiate (incl (extend F second) first) (generator (extend F second).arity (.inr ()))
  rw [instantiate_generator, instantiate_generator]
  rfl

/-- Values read through both inclusions, then swapped, are values read through the other two. -/
theorem swap_value (F : Frame S) (first second : MetaArity S) {Γ : Ctx S} {sort : S.Srt}
    (value : Term (signature S F.arity) Γ sort) :
    instantiate (swap F first second)
        (instantiate (incl (extend F first) second) (instantiate (incl F first) value)) =
      instantiate (incl (extend F second) first) (instantiate (incl F second) value) :=
  calc instantiate (swap F first second)
        (instantiate (incl (extend F first) second) (instantiate (incl F first) value))
      = instantiate (swap F first second)
          (instantiate (Assignment.compose (incl (extend F first) second) (incl F first)) value) :=
        congrArg (instantiate (swap F first second)) (Assignment.instantiate_compose _ _ _).symm
    _ = instantiate (Assignment.compose (swap F first second)
          (Assignment.compose (incl (extend F first) second) (incl F first))) value :=
        (Assignment.instantiate_compose _ _ _).symm
    _ = instantiate (Assignment.compose (incl (extend F second) first) (incl F second)) value := by
        rw [swap_incl_incl]
    _ = instantiate (incl (extend F second) first) (instantiate (incl F second) value) :=
        Assignment.instantiate_compose _ _ _

/-! ## The helper step -/

variable (S) (O : Type) [DecidableEq O]

/-- A state of the helper step: a frame, its knowledge and its present occurrences. -/
structure State where
  frame : Frame S
  knowledge : EquationStore (Observation S frame.arity)
  present : Finset O

variable {S O}

/-- **A helper firing**: it makes one occurrence and one fresh helper, and tells the helper's value,
a term over the frame it fires at. Its guards are equations on the names of that frame, asked at
every solution. -/
structure Firing (s : State S O) where
  made : O
  helper : MetaArity S
  value : Term (signature S s.frame.arity) helper.1 helper.2
  guards : EquationStore (Observation S s.frame.arity)

namespace Firing

variable {s : State S O} (f : Firing s)

/-- The occurrence it makes. -/
def selection : Selection O := ⟨[], [], [f.made]⟩

/-- The helper's equation, at the extended frame. -/
def tell : Equation (Observation S (extend s.frame f.helper).arity) :=
  (observe (fresh s.frame f.helper), observe (instantiate (incl s.frame f.helper) f.value))

/-- Its information: the knowledge, read in the extended frame, and the helper's equation. -/
def information : EquationStore (Observation S (extend s.frame f.helper).arity) :=
  (Frames.contextual S).applyStore (incl s.frame f.helper) s.knowledge ++ [f.tell]

/-- The state after it. -/
abbrev after : State S O :=
  ⟨extend s.frame f.helper, f.information, fire s.present (f.selection.commit (T := Unit))⟩

/-- The firing read at another state along a morphism of frames. -/
abbrev move {t : State S O} (φ : Assignment s.frame.arity t.frame.arity) : Firing t :=
  ⟨f.made, f.helper, instantiate φ f.value, (Frames.contextual S).applyStore φ f.guards⟩

/-- The firing read at another state along a morphism of frames, its occurrence renamed. -/
abbrev carry {t : State S O} (π : O ≃ O) (φ : Assignment s.frame.arity t.frame.arity) : Firing t :=
  ⟨π f.made, f.helper, instantiate φ f.value, (Frames.contextual S).applyStore φ f.guards⟩

end Firing

/-- **The helper step**: firings that make fresh helpers, guarded by equations on the old names; it has
no predicate queries. -/
abbrev helperStep : Step.Standard (Frames.contextual S) O (State S O) Firing where
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
  Holds {s} f _ σ := (Frames.contextual S).Models (Assignment.compose σ (incl s.frame f.helper)) f.guards
  Admits {s} f := f.selection.made.Nodup ∧
    Enabled (fun _ : O => ()) s.present (f.selection.commit (T := Unit)) ∧
    (Frames.contextual S).Solvable f.information ∧
    (Frames.contextual S).Entails f.information fun _ σ =>
      (Frames.contextual S).Models (Assignment.compose σ (incl s.frame f.helper)) f.guards
  admits_iff _ := Iff.rfl
  preparedResult f _ := f.after
  present_preparedResult _ _ := rfl
  preparedSettle f _ := (Frames.contextual S).id (extend _ f.helper)
  knowledge_preparedResult f _ := (Frames.applyStore_id (X := Frames.contextual S) f.information).symm

instance helperStep_guarded : (helperStep (S := S) (O := O)).toStep.Guarded :=
  Step.standard_guarded _

instance helperStep_exact : (helperStep (S := S) (O := O)).toStep.Exact :=
  Step.standard_exact _

/-- The morphism a helper firing moves along is the inclusion of the old names. -/
theorem along_eq {s : State S O} (f : Firing s) (admitted : helperStep.Admits f) :
    helperStep.along f admitted = incl s.frame f.helper :=
  Assignment.compose_identity_left _

/-- The extension of a solution by the helper's value. -/
def extendSolution {s : State S O} (f : Firing s) {b : Frame S} (σ : Assignment s.frame.arity b.arity) :
    Assignment (extend s.frame f.helper).arity b.arity
  | .inl name => σ name
  | .inr () => instantiate σ f.value

omit [DecidableEq O] in
/-- The extension restricts back to the solution on the old names. -/
theorem extendSolution_restrict {s : State S O} (f : Firing s) {b : Frame S}
    (σ : Assignment s.frame.arity b.arity) :
    Assignment.compose (extendSolution f σ) (incl s.frame f.helper) = σ := by
  funext name
  exact instantiate_generator (extendSolution f σ) (.inl name)

omit [DecidableEq O] in
/-- **The helper is fresh**: every solution of the knowledge extends to the information. -/
theorem extendSolution_models {s : State S O} (f : Firing s) {b : Frame S}
    (σ : Assignment s.frame.arity b.arity) (solved : (Frames.contextual S).Models σ s.knowledge) :
    (Frames.contextual S).Models (extendSolution f σ) f.information := by
  have restrict := extendSolution_restrict f σ
  intro e member
  rcases List.mem_append.mp member with old | told
  · obtain ⟨original, present, rfl⟩ := List.mem_map.mp old
    have solvedOriginal : instantiateObservation σ original.1 = instantiateObservation σ original.2 :=
      solved original present
    show instantiateObservation (extendSolution f σ) (instantiateObservation (incl s.frame f.helper) original.1) =
      instantiateObservation (extendSolution f σ) (instantiateObservation (incl s.frame f.helper) original.2)
    rw [instantiateObservation_comp, instantiateObservation_comp, restrict]
    exact solvedOriginal
  · obtain rfl := List.mem_singleton.mp told
    show observe (instantiate (extendSolution f σ) (fresh s.frame f.helper)) =
      observe (instantiate (extendSolution f σ) (instantiate (incl s.frame f.helper) f.value))
    rw [← Assignment.instantiate_compose, restrict]
    exact congrArg observe (instantiate_generator (extendSolution f σ) (.inr ()))

omit [DecidableEq O] in
theorem information_solvable {s : State S O} (f : Firing s)
    (solvable : (Frames.contextual S).Solvable s.knowledge) :
    (Frames.contextual S).Solvable f.information := by
  obtain ⟨b, σ, solved⟩ := solvable
  exact ⟨b, extendSolution f σ, extendSolution_models f σ solved⟩

omit [DecidableEq O] in
/-- Every solution of the information restricts to a solution of the knowledge. -/
theorem restrict_models {s : State S O} (f : Firing s) {b : Frame S}
    (σ : Assignment (extend s.frame f.helper).arity b.arity)
    (solved : (Frames.contextual S).Models σ f.information) :
    (Frames.contextual S).Models (Assignment.compose σ (incl s.frame f.helper)) s.knowledge :=
  (Frames.models_applyStore (X := Frames.contextual S) (incl s.frame f.helper) σ s.knowledge).mp
    (Frames.models_of_subset (fun _ member => List.mem_append_left _ member) solved)

omit [DecidableEq O] in
/-- **The information asks exactly what the knowledge asks about the old names.** -/
theorem entails_information_iff {s : State S O} (f : Firing s)
    (guards : EquationStore (Observation S s.frame.arity)) :
    (Frames.contextual S).Entails f.information
        (fun _ σ => (Frames.contextual S).Models (Assignment.compose σ (incl s.frame f.helper)) guards) ↔
      (Frames.contextual S).Entails s.knowledge (fun _ σ => (Frames.contextual S).Models σ guards) := by
  constructor
  · intro asked b σ solved
    have holds : (Frames.contextual S).Models
        (Assignment.compose (extendSolution f σ) (incl s.frame f.helper)) guards :=
      asked b (extendSolution f σ) (extendSolution_models f σ solved)
    rwa [extendSolution_restrict] at holds
  · intro asked b σ solved
    exact asked b _ (restrict_models f σ solved)

omit [DecidableEq O] in
theorem knowledge_solvable {s : State S O} (f : Firing s)
    (solvable : (Frames.contextual S).Solvable f.information) :
    (Frames.contextual S).Solvable s.knowledge :=
  Frames.solvable_of_applyStore (incl s.frame f.helper)
    (Frames.solvable_of_subset (fun _ member => List.mem_append_left _ member) solvable)

theorem enabled_iff {s : State S O} (f : Firing s) :
    Enabled (fun _ : O => ()) s.present (f.selection.commit (T := Unit)) ↔ f.made ∉ s.present := by
  constructor
  · intro enabled present
    exact Finset.disjoint_left.mp enabled.fresh (by simp [Firing.selection, Selection.commit]) present
  · intro absent
    refine ⟨by simp [Firing.selection, Selection.commit], by simp [Firing.selection, Selection.commit],
      by simp [Firing.selection, Selection.commit], ?_, by simp [Firing.selection, Selection.commit]⟩
    simpa [Firing.selection, Selection.commit] using absent

/-- **Admission of a helper firing**: solvable knowledge, a fresh occurrence, and guards that the
knowledge asks. -/
theorem admits_iff {s : State S O} (f : Firing s) :
    helperStep.Admits f ↔ (Frames.contextual S).Solvable s.knowledge ∧ f.made ∉ s.present ∧
      (Frames.contextual S).Entails s.knowledge (fun _ σ => (Frames.contextual S).Models σ f.guards) := by
  constructor
  · rintro ⟨-, enabled, solvable, asked⟩
    exact ⟨knowledge_solvable f solvable, (enabled_iff f).mp enabled,
      (entails_information_iff f f.guards).mp asked⟩
  · rintro ⟨solvable, absent, asked⟩
    exact ⟨List.nodup_singleton _, (enabled_iff f).mpr absent, information_solvable f solvable,
      (entails_information_iff f f.guards).mpr asked⟩

/-! ## Transport -/

omit [DecidableEq O] in
/-- Firings with the same occurrence and helper are equal when their values and guards are. -/
theorem Firing.mk_congr {t : State S O} (made : O) (helper : MetaArity S)
    {first second : Term (signature S t.frame.arity) helper.1 helper.2}
    {firstGuards secondGuards : EquationStore (Observation S t.frame.arity)}
    (same : first = second) (sameGuards : firstGuards = secondGuards) :
    (⟨made, helper, first, firstGuards⟩ : Firing t) = ⟨made, helper, second, secondGuards⟩ := by
  rw [same, sameGuards]

omit [DecidableEq O] in
theorem Firing.mk_congr_made {t : State S O} {made made' : O} (sameMade : made = made')
    (helper : MetaArity S) {first second : Term (signature S t.frame.arity) helper.1 helper.2}
    {firstGuards secondGuards : EquationStore (Observation S t.frame.arity)}
    (same : first = second) (sameGuards : firstGuards = secondGuards) :
    (⟨made, helper, first, firstGuards⟩ : Firing t) = ⟨made', helper, second, secondGuards⟩ := by
  rw [sameMade, same, sameGuards]

omit [DecidableEq O] in
theorem move_value {s t : State S O} (f : Firing s) (φ : Assignment s.frame.arity t.frame.arity) :
    (f.move φ).value = instantiate φ f.value := rfl

/-- The information of a moved firing is the information carried along the lifted isomorphism. -/
theorem information_move {s t : State S O} (i : helperStep.StateIso s t) (f : Firing s) :
    (Frames.contextual S).Equivalent
      ((Frames.contextual S).applyStore (liftIso i.frame f.helper).hom f.information)
      (f.move i.frame.hom).information := by
  dsimp only [helperStep] at i ⊢
  have carried : (Frames.contextual S).applyStore (liftIso i.frame f.helper).hom f.information =
      (Frames.contextual S).applyStore (incl t.frame f.helper)
          ((Frames.contextual S).applyStore i.frame.hom s.knowledge) ++
        [(observe (fresh t.frame f.helper),
          observe (instantiate (incl t.frame f.helper) (instantiate i.frame.hom f.value)))] := by
    unfold Firing.information
    rw [Frames.applyStore_append, Frames.applyStore_applyStore, Frames.applyStore_applyStore]
    congr 1
    · show (Frames.contextual S).applyStore (Assignment.compose (lift i.frame.hom f.helper) (incl s.frame f.helper))
          s.knowledge =
        (Frames.contextual S).applyStore (Assignment.compose (incl t.frame f.helper) i.frame.hom) s.knowledge
      rw [compose_lift_incl]
    · have value : instantiate (lift i.frame.hom f.helper) (instantiate (incl s.frame f.helper) f.value) =
          instantiate (incl t.frame f.helper) (instantiate i.frame.hom f.value) :=
        (Assignment.instantiate_compose _ _ _).symm.trans
          ((congrArg (fun assignment => instantiate assignment f.value) (compose_lift_incl i.frame.hom f.helper)).trans
            (Assignment.instantiate_compose _ _ _))
      show [(observe (instantiate (lift i.frame.hom f.helper) (fresh s.frame f.helper)),
          observe (instantiate (lift i.frame.hom f.helper) (instantiate (incl s.frame f.helper) f.value)))] =
        [(observe (fresh t.frame f.helper),
          observe (instantiate (incl t.frame f.helper) (instantiate i.frame.hom f.value)))]
      rw [instantiate_lift_fresh, value]
  rw [carried]
  exact Frames.Equivalent.append_right (Frames.Equivalent.applyStore _ i.knowledge) _

/-- **Transport of helper firings** along isomorphisms of states. -/
def helperTransport : Transport (helperStep (S := S) (O := O)).toStep where
  Iso s t := helperStep.StateIso s t
  toStateIso i := i
  refl s := Step.StateIso.refl s
  symm i := i.symm
  trans i j := i.trans j
  Alike f f' := f = f'
  alike_equivalence _ := ⟨Eq.refl, Eq.symm, Eq.trans⟩
  selection_alike same := congrArg _ same
  admits_alike same := same ▸ Iff.rfl
  result_alike {s} {f} _ same _ _ := by
    subst same
    exact Step.StateIso.refl _
  move i f := f.carry i.rename i.frame.hom
  move_alike _ _ _ same := by subst same; rfl
  move_refl f := Firing.mk_congr _ _ (instantiate_identity f.value)
    (Frames.applyStore_id (X := Frames.contextual S) f.guards)
  move_trans i j f := Firing.mk_congr _ _ (Assignment.instantiate_compose j.frame.hom i.frame.hom f.value)
    (Frames.applyStore_applyStore (X := Frames.contextual S) i.frame.hom j.frame.hom f.guards).symm
  move_symm i f := Firing.mk_congr_made (i.rename.symm_apply_apply f.made) _
    ((Assignment.instantiate_compose i.frame.inv i.frame.hom f.value).symm.trans
      ((congrArg (fun assignment => instantiate assignment f.value) (compose_inv_hom i.frame)).trans
        (instantiate_identity f.value)))
    ((Frames.applyStore_applyStore (X := Frames.contextual S) i.frame.hom i.frame.inv f.guards).trans
      ((congrArg (fun assignment => (Frames.contextual S).applyStore assignment f.guards)
        (compose_inv_hom i.frame)).trans (Frames.applyStore_id (X := Frames.contextual S) f.guards)))
  selection_move _ _ := rfl
  admits_move {s t} i f := by
    rw [admits_iff, admits_iff]
    exact and_congr i.solvable_iff.symm (and_congr (not_congr (i.mem_present_iff f.made))
      ((Frames.Equivalent.entails_iff i.knowledge _).symm.trans
        (Frames.Iso.entails_applyStore_iff i.frame s.knowledge f.guards)))
  result_move {s t} i f _ :=
    ⟨liftIso i.frame f.helper, information_move i f, i.rename, by
      show (fire s.present (f.selection.commit (T := Unit))).map i.rename.toEmbedding =
        fire t.present ((AnnotatedRuns.renameSelection i.rename f.selection).commit (T := Unit))
      have present : s.present.map i.rename.toEmbedding = t.present := i.present
      rw [← present]
      exact (AnnotatedRuns.fire_rename s.present f.selection).symm⟩
  residual g admitted f := f.move (helperStep.along g admitted)
  selection_residual _ _ _ := rfl
  move_residual {s t} i g admitted f := by
    have value : instantiate (lift i.frame.hom g.helper) (instantiate (incl s.frame g.helper) f.value) =
        instantiate (incl t.frame g.helper) (instantiate i.frame.hom f.value) :=
      (Assignment.instantiate_compose _ _ _).symm.trans
        ((congrArg (fun assignment => instantiate assignment f.value) (compose_lift_incl i.frame.hom g.helper)).trans
          (Assignment.instantiate_compose _ _ _))
    have first : instantiate (helperStep.along g admitted) f.value = instantiate (incl s.frame g.helper) f.value :=
      congrArg (fun assignment => instantiate assignment f.value) (along_eq g admitted)
    have second : ∀ moved, instantiate (helperStep.along (g.carry (t := t) i.rename i.frame.hom) moved)
        (instantiate i.frame.hom f.value) = instantiate (incl t.frame g.helper) (instantiate i.frame.hom f.value) :=
      fun moved => congrArg (fun assignment => instantiate assignment (instantiate i.frame.hom f.value))
        (along_eq (g.carry (t := t) i.rename i.frame.hom) moved)
    have guardsFirst : (Frames.contextual S).applyStore (helperStep.along g admitted) f.guards =
        (Frames.contextual S).applyStore (incl s.frame g.helper) f.guards :=
      congrArg (fun assignment => (Frames.contextual S).applyStore assignment f.guards) (along_eq g admitted)
    have guardsSecond : ∀ moved, (Frames.contextual S).applyStore
        (helperStep.along (g.carry (t := t) i.rename i.frame.hom) moved)
          ((Frames.contextual S).applyStore i.frame.hom f.guards) =
        (Frames.contextual S).applyStore (incl t.frame g.helper)
          ((Frames.contextual S).applyStore i.frame.hom f.guards) :=
      fun moved => congrArg (fun assignment =>
        (Frames.contextual S).applyStore assignment ((Frames.contextual S).applyStore i.frame.hom f.guards))
        (along_eq (g.carry (t := t) i.rename i.frame.hom) moved)
    have guardsValue : (Frames.contextual S).applyStore (lift i.frame.hom g.helper)
          ((Frames.contextual S).applyStore (incl s.frame g.helper) f.guards) =
        (Frames.contextual S).applyStore (incl t.frame g.helper)
          ((Frames.contextual S).applyStore i.frame.hom f.guards) :=
      (Frames.applyStore_applyStore (X := Frames.contextual S) _ _ f.guards).trans
        ((congrArg (fun assignment => (Frames.contextual S).applyStore assignment f.guards)
          (compose_lift_incl i.frame.hom g.helper)).trans
          (Frames.applyStore_applyStore (X := Frames.contextual S) _ _ f.guards).symm)
    exact Firing.mk_congr _ _
      ((congrArg (instantiate (lift i.frame.hom g.helper)) first).trans (value.trans (second _).symm))
      ((congrArg ((Frames.contextual S).applyStore (lift i.frame.hom g.helper)) guardsFirst).trans
        (guardsValue.trans (guardsSecond _).symm))


/-! ## The diamond closes up to renaming the helpers -/

/-- A residual reads the value through the inclusion of the old names. -/
theorem along_value {s : State S O} (g : Firing s) (admitted : helperStep.Admits g)
    {Γ : Ctx S} {sort : S.Srt} (term : Term (signature S s.frame.arity) Γ sort) :
    instantiate (helperStep.along g admitted) term = instantiate (incl s.frame g.helper) term :=
  congrArg (fun assignment => instantiate assignment term) (along_eq g admitted)

omit [DecidableEq O] in
/-- Observations read through both inclusions, then swapped, are read through the other two. -/
theorem swap_observation (F : Frame S) (first second : MetaArity S) (t : Observation S F.arity) :
    instantiateObservation (swap F first second)
        (instantiateObservation (incl (extend F first) second) (instantiateObservation (incl F first) t)) =
      instantiateObservation (incl (extend F second) first) (instantiateObservation (incl F second) t) :=
  calc instantiateObservation (swap F first second)
        (instantiateObservation (incl (extend F first) second) (instantiateObservation (incl F first) t))
      = instantiateObservation (swap F first second)
          (instantiateObservation (Assignment.compose (incl (extend F first) second) (incl F first)) t) :=
        congrArg (instantiateObservation (swap F first second)) (instantiateObservation_comp _ _ t)
    _ = instantiateObservation (Assignment.compose (swap F first second)
          (Assignment.compose (incl (extend F first) second) (incl F first))) t :=
        instantiateObservation_comp _ _ t
    _ = instantiateObservation (Assignment.compose (incl (extend F second) first) (incl F second)) t := by
        rw [swap_incl_incl]
    _ = instantiateObservation (incl (extend F second) first) (instantiateObservation (incl F second) t) :=
        (instantiateObservation_comp _ _ t).symm

/-- The canonical result isomorphism swaps the two fresh declaration blocks
and preserves physical occurrence identities. -/
def helperSquareIso {s : State S O} {f g : Firing s}
    (first : helperStep.Admits f) (second : helperStep.Admits g) :
    helperStep.StateIso
      (g.move (t := f.after) (helperStep.along f first)).after
      (f.move (t := g.after) (helperStep.along g second)).after := by
  refine ⟨swapIso s.frame f.helper g.helper, ?_, Equiv.refl O, ?_⟩
  · show (Frames.contextual S).Equivalent
        ((Frames.contextual S).applyStore (swap s.frame f.helper g.helper)
          (g.move (t := f.after) (helperStep.along f first)).information)
        (f.move (t := g.after) (helperStep.along g second)).information
    have kPart : (Frames.contextual S).applyStore (swap s.frame f.helper g.helper)
          ((Frames.contextual S).applyStore (incl (extend s.frame f.helper) g.helper)
            ((Frames.contextual S).applyStore (incl s.frame f.helper) s.knowledge)) =
        (Frames.contextual S).applyStore (incl (extend s.frame g.helper) f.helper)
          ((Frames.contextual S).applyStore (incl s.frame g.helper) s.knowledge) := by
      unfold Frames.applyStore
      simp only [List.map_map]
      congr 1
      funext e
      exact Prod.ext (swap_observation s.frame f.helper g.helper e.1)
        (swap_observation s.frame f.helper g.helper e.2)
    have tellF : (Frames.contextual S).applyStore (swap s.frame f.helper g.helper)
          ((Frames.contextual S).applyStore (incl (extend s.frame f.helper) g.helper) [f.tell]) =
        [(f.move (t := g.after) (helperStep.along g second)).tell] := by
      show [(observe (instantiate (swap s.frame f.helper g.helper)
              (instantiate (incl (extend s.frame f.helper) g.helper) (fresh s.frame f.helper))),
            observe (instantiate (swap s.frame f.helper g.helper)
              (instantiate (incl (extend s.frame f.helper) g.helper)
                (instantiate (incl s.frame f.helper) f.value))))] =
        [(observe (fresh (extend s.frame g.helper) f.helper),
            observe (instantiate (incl (extend s.frame g.helper) f.helper)
              (instantiate (helperStep.along g second) f.value)))]
      rw [swap_incl_fresh, swap_value, along_value]
    have tellG : (Frames.contextual S).applyStore (swap s.frame f.helper g.helper)
          [(g.move (t := f.after) (helperStep.along f first)).tell] =
        (Frames.contextual S).applyStore (incl (extend s.frame g.helper) f.helper) [g.tell] := by
      show [(observe (instantiate (swap s.frame f.helper g.helper) (fresh (extend s.frame f.helper) g.helper)),
            observe (instantiate (swap s.frame f.helper g.helper)
              (instantiate (incl (extend s.frame f.helper) g.helper)
                (instantiate (helperStep.along f first) g.value))))] =
        [(observe (instantiate (incl (extend s.frame g.helper) f.helper) (fresh s.frame g.helper)),
            observe (instantiate (incl (extend s.frame g.helper) f.helper)
              (instantiate (incl s.frame g.helper) g.value)))]
      rw [along_value, swap_fresh, swap_value]
    have left : (Frames.contextual S).applyStore (swap s.frame f.helper g.helper)
          (g.move (t := f.after) (helperStep.along f first)).information =
        (Frames.contextual S).applyStore (incl (extend s.frame g.helper) f.helper)
            ((Frames.contextual S).applyStore (incl s.frame g.helper) s.knowledge) ++
          [(f.move (t := g.after) (helperStep.along g second)).tell] ++
          (Frames.contextual S).applyStore (incl (extend s.frame g.helper) f.helper) [g.tell] := by
      show (Frames.contextual S).applyStore (swap s.frame f.helper g.helper)
          ((Frames.contextual S).applyStore (incl (extend s.frame f.helper) g.helper)
            ((Frames.contextual S).applyStore (incl s.frame f.helper) s.knowledge ++ [f.tell]) ++
            [(g.move (t := f.after) (helperStep.along f first)).tell]) = _
      simp only [Frames.applyStore_append]
      rw [kPart, tellF, tellG]
    have right : (f.move (t := g.after) (helperStep.along g second)).information =
        (Frames.contextual S).applyStore (incl (extend s.frame g.helper) f.helper)
            ((Frames.contextual S).applyStore (incl s.frame g.helper) s.knowledge) ++
          (Frames.contextual S).applyStore (incl (extend s.frame g.helper) f.helper) [g.tell] ++
          [(f.move (t := g.after) (helperStep.along g second)).tell] := by
      show (Frames.contextual S).applyStore (incl (extend s.frame g.helper) f.helper)
          ((Frames.contextual S).applyStore (incl s.frame g.helper) s.knowledge ++ [g.tell]) ++
          [(f.move (t := g.after) (helperStep.along g second)).tell] = _
      rw [Frames.applyStore_append]
    rw [left, right]
    exact Frames.equivalent_of_mem_iff fun e => by
      simp only [List.mem_append]
      tauto
  · show (fire (fire s.present (f.selection.commit (T := Unit))) (g.selection.commit (T := Unit))).map
        (Equiv.refl O).toEmbedding =
      fire (fire s.present (g.selection.commit (T := Unit))) (f.selection.commit (T := Unit))
    rw [Equiv.refl_toEmbedding, Finset.map_refl]
    ext o
    simp only [Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.mem_fire]
    simp [Firing.selection, Selection.commit]
    tauto

/-- Both admitted orders close through the canonical declaration swap. -/
theorem helper_closes : (helperTransport (S := S) (O := O)).Closes := by
  intro _s _f _g first second _afterFirst _afterSecond
  exact ⟨helperSquareIso first second⟩

/-- The residual's guards are asked after the other firing exactly when the knowledge asks them. -/
theorem residual_asks_iff {s : State S O} (f : Firing s) (first : helperStep.Admits f)
    (guards : EquationStore (Observation S s.frame.arity)) :
    (Frames.contextual S).Entails f.information (fun _ σ =>
        (Frames.contextual S).Models σ ((Frames.contextual S).applyStore (helperStep.along f first) guards)) ↔
      (Frames.contextual S).Entails s.knowledge (fun _ σ => (Frames.contextual S).Models σ guards) := by
  rw [along_eq]
  refine Iff.trans ?_ (entails_information_iff f guards)
  constructor
  · intro asked b σ solved
    exact (Frames.models_applyStore (X := Frames.contextual S) (incl s.frame f.helper) σ guards).mp
      (asked b σ solved)
  · intro asked b σ solved
    exact (Frames.models_applyStore (X := Frames.contextual S) (incl s.frame f.helper) σ guards).mpr
      (asked b σ solved)

/-- **Independence of helper firings**: solvable knowledge, fresh and distinct occurrences, and the
guards of both firings asked by the knowledge. -/
theorem independent_iff {s : State S O} {f g : Firing s} :
    (helperTransport (S := S) (O := O)).Independent s f g ↔
      (Frames.contextual S).Solvable s.knowledge ∧ f.made ∉ s.present ∧ g.made ∉ s.present ∧
        f.made ≠ g.made ∧
        (Frames.contextual S).Entails s.knowledge (fun _ σ => (Frames.contextual S).Models σ f.guards) ∧
        (Frames.contextual S).Entails s.knowledge (fun _ σ => (Frames.contextual S).Models σ g.guards) := by
  rw [Transport.independent_iff_admits helper_closes]
  constructor
  · rintro ⟨first, second, afterFirst, -⟩
    obtain ⟨solvable, fFresh, fAsked⟩ := (admits_iff f).mp first
    obtain ⟨-, gFresh, gAsked⟩ := (admits_iff g).mp second
    obtain ⟨-, gAfter, -⟩ := (admits_iff _).mp afterFirst
    refine ⟨solvable, fFresh, gFresh, fun same => gAfter ?_, fAsked, gAsked⟩
    show g.made ∈ fire s.present (f.selection.commit (T := Unit))
    rw [← same]
    simp [fire, Firing.selection, Selection.commit]
  · rintro ⟨solvable, fFresh, gFresh, distinct, fAsked, gAsked⟩
    have first := (admits_iff f).mpr ⟨solvable, fFresh, fAsked⟩
    have second := (admits_iff g).mpr ⟨solvable, gFresh, gAsked⟩
    refine ⟨first, second,
      (admits_iff _).mpr ⟨information_solvable f solvable, ?_, (residual_asks_iff f first g.guards).mpr gAsked⟩,
      (admits_iff _).mpr ⟨information_solvable g solvable, ?_, (residual_asks_iff g second f.guards).mpr fAsked⟩⟩
    · show g.made ∉ fire s.present (f.selection.commit (T := Unit))
      simp [fire, Firing.selection, Selection.commit, gFresh, Ne.symm distinct]
    · show f.made ∉ fire s.present (g.selection.commit (T := Unit))
      simp [fire, Firing.selection, Selection.commit, fFresh, distinct]

omit [DecidableEq O] in
/-- No guards are always asked. -/
theorem asks_nil {s : State S O} :
    (Frames.contextual S).Entails s.knowledge (fun _ σ => (Frames.contextual S).Models σ []) :=
  fun _ _ _ => Frames.models_nil _

omit [DecidableEq O] in
/-- Empty guards are always asked. -/
theorem asks_of_isEmpty {s : State S O} {guards : EquationStore (Observation S s.frame.arity)}
    (empty : guards.isEmpty = true) :
    (Frames.contextual S).Entails s.knowledge (fun _ σ => (Frames.contextual S).Models σ guards) := by
  rw [List.isEmpty_iff.mp empty]
  exact asks_nil

/-! ## The consumer: a concrete diamond -/

namespace Consumer

/-- One sort; the natural numbers are its constants. -/
abbrev tiny : Signature where
  Srt := Unit
  Op _ := Nat
  arity _ := []

/-- A constant. -/
def constant {V : Type} {declaration : V → MetaArity tiny} {Γ : Ctx tiny} (n : Nat) :
    Term (signature tiny declaration) Γ () :=
  .op (.inl n) .nil

/-- The empty frame. -/
abbrev empty : Frame tiny := ⟨Empty, fun impossible => impossible.elim⟩

/-- No names, no knowledge, no occurrences. -/
abbrev start : State tiny Nat := ⟨empty, [], ∅⟩

/-- Makes occurrence `1` and a parameterless helper, valued `7`. -/
def first : Firing start := ⟨1, ([], ()), constant 7, []⟩

/-- Makes occurrence `2` and a helper with one parameter, valued `8`. -/
def second : Firing start := ⟨2, ([()], ()), constant 8, []⟩

theorem start_solvable : (Frames.contextual tiny).Solvable start.knowledge :=
  ⟨empty, generator empty.arity, Frames.models_nil _⟩

/-- **The consumer diamond: the two firings are independent.** -/
theorem independent : (helperTransport (S := tiny) (O := Nat)).Independent start first second :=
  independent_iff.mpr ⟨start_solvable, by decide, by decide, by decide, asks_nil, asks_nil⟩

/-- **The transported results**: each residual keeps its occurrence, its helper and its constant
value, read in the frame the other firing made. -/
theorem residuals (a : helperStep.Admits first) (b : helperStep.Admits second) :
    (helperTransport.residual first a second).made = 2 ∧
      (helperTransport.residual first a second).helper = ([()], ()) ∧
      (helperTransport.residual first a second).value = constant 8 ∧
      (helperTransport.residual second b first).made = 1 ∧
      (helperTransport.residual second b first).helper = ([], ()) ∧
      (helperTransport.residual second b first).value = constant 7 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- **The diamond commutes only up to renaming**: the two composite states are different, and they
are isomorphic. -/
theorem composites_differ :
    ∃ (a : helperStep.Admits first) (b : helperStep.Admits second)
      (a₁ : helperStep.Admits (helperTransport.residual first a second))
      (b₁ : helperStep.Admits (helperTransport.residual second b first)),
      helperStep.result _ a₁ ≠ helperStep.result _ b₁ ∧
        helperTransport.Same (helperStep.result _ a₁) (helperStep.result _ b₁) := by
  obtain ⟨a, b, a₁, b₁, close⟩ := independent
  refine ⟨a, b, a₁, b₁, fun same => ?_, close⟩
  have frames : (⟨(Empty ⊕ Unit) ⊕ Unit,
        Sum.elim (Sum.elim empty.arity fun _ => (([], ()) : MetaArity tiny)) fun _ => ([()], ())⟩ : Frame tiny) =
      ⟨(Empty ⊕ Unit) ⊕ Unit,
        Sum.elim (Sum.elim empty.arity fun _ => (([()], ()) : MetaArity tiny)) fun _ => ([], ())⟩ :=
    congrArg State.frame same
  have arities := congrFun (eq_of_heq (Frame.mk.inj frames).2) (.inr ())
  simp at arities

end Consumer

/-! ## Deciding independence in the pattern fibre, and a sound check elsewhere -/

section Pattern

variable [DecidableEq S.Srt] [∀ sort, DecidableEq (S.Op sort)]

/-- **The pattern fibre decides solvability with the structural-pattern driver**: pattern knowledge is solvable exactly
when the driver returns an empty residual at some budget. -/
theorem pattern_solvable_iff {V : Type} [DecidableEq V] {source : V → MetaArity S}
    (problem : ContextualResidual.Problem source)
    (patterned : ContextualPatternFragment.ProblemPattern problem) :
    (Frames.contextual S).Solvable (a := ⟨V, source⟩) problem ↔
      ∃ fuel, ∃ update, ContextualFrameWorklist.run fuel source problem = .residual update ∧
        update.remaining = [] := by
  constructor
  · rintro ⟨b, σ, solved⟩
    obtain ⟨fuel, found | refused⟩ := ContextualPatternTermination.solves_or_refutes problem patterned
    · obtain ⟨update, computed, empty, -, -⟩ := found
      exact ⟨fuel, update, computed, empty⟩
    · obtain ⟨proof, -⟩ := refused
      exact (proof b.arity σ solved).elim
  · rintro ⟨fuel, update, -, empty⟩
    exact ⟨⟨update.Variables, update.declaration⟩, update.answer, update.completed empty⟩

/-- **The pattern fibre decides unsolvability with the structural-pattern driver**: it refutes at some budget. -/
theorem pattern_unsolvable_iff {V : Type} [DecidableEq V] {source : V → MetaArity S}
    (problem : ContextualResidual.Problem source)
    (patterned : ContextualPatternFragment.ProblemPattern problem) :
    ¬ (Frames.contextual S).Solvable (a := ⟨V, source⟩) problem ↔
      ∃ fuel, ∃ proof, ContextualFrameWorklist.run fuel source problem = .refuted proof := by
  constructor
  · intro unsolvable
    exact ContextualPatternTermination.refutes_of_no_model problem patterned
      fun next candidate model => unsolvable ⟨⟨_, next⟩, candidate, model⟩
  · rintro ⟨fuel, proof, -⟩ ⟨b, σ, solved⟩
    exact proof b.arity σ solved

/-- The driver solves the problem at this budget. -/
def solvedAt {V : Type} [DecidableEq V] {source : V → MetaArity S} (fuel : Nat)
    (problem : ContextualResidual.Problem source) : Bool :=
  match ContextualFrameWorklist.run fuel source problem with
  | .residual update => update.remaining.isEmpty
  | .refuted _ => false

/-- The driver refutes the problem at this budget. -/
def refutedAt {V : Type} [DecidableEq V] {source : V → MetaArity S} (fuel : Nat)
    (problem : ContextualResidual.Problem source) : Bool :=
  match ContextualFrameWorklist.run fuel source problem with
  | .residual _ => false
  | .refuted _ => true

theorem solvedAt_sound {V : Type} [DecidableEq V] {source : V → MetaArity S} (fuel : Nat)
    (problem : ContextualResidual.Problem source) (solved : solvedAt fuel problem = true) :
    (Frames.contextual S).Solvable (a := ⟨V, source⟩) problem := by
  unfold solvedAt at solved
  cases computed : ContextualFrameWorklist.run fuel source problem with
  | residual update =>
      simp only [computed] at solved
      exact ⟨⟨update.Variables, update.declaration⟩, update.answer,
        update.completed (List.isEmpty_iff.mp solved)⟩
  | refuted proof => simp [computed] at solved

theorem refutedAt_sound {V : Type} [DecidableEq V] {source : V → MetaArity S} (fuel : Nat)
    (problem : ContextualResidual.Problem source) (refuted : refutedAt fuel problem = true) :
    ¬ (Frames.contextual S).Solvable (a := ⟨V, source⟩) problem := by
  unfold refutedAt at refuted
  cases computed : ContextualFrameWorklist.run fuel source problem with
  | residual update => simp [computed] at refuted
  | refuted proof =>
      rintro ⟨b, σ, solved⟩
      exact proof b.arity σ solved

/-- **A sound three-valued check of helper independence, at a solver budget.** Fresh, distinct
occurrences with pattern knowledge that the driver solves answer independent; a reused occurrence or a
refutation answers dependent; anything else, in particular knowledge outside the pattern fragment,
answers unknown. -/
def helperCheck (s : State S O) [DecidableEq s.frame.Names] (fuel : Nat) :
    (helperTransport (S := S) (O := O)).Check s :=
  Transport.Check.ofTests helperTransport s
    (fun f g => f.made ∉ s.present ∧ g.made ∉ s.present ∧ f.made ≠ g.made ∧
      f.guards.isEmpty = true ∧ g.guards.isEmpty = true ∧
      ContextualPatternFragment.checkProblem s.knowledge = true ∧ solvedAt fuel s.knowledge = true)
    (fun f g => f.made ∈ s.present ∨ g.made ∈ s.present ∨ f.made = g.made ∨
      (ContextualPatternFragment.checkProblem s.knowledge = true ∧ refutedAt fuel s.knowledge = true))
    (fun _ _ holds => independent_iff.mpr
      ⟨solvedAt_sound fuel s.knowledge holds.2.2.2.2.2.2, holds.1, holds.2.1, holds.2.2.1,
        asks_of_isEmpty holds.2.2.2.1, asks_of_isEmpty holds.2.2.2.2.1⟩)
    (fun _ _ refutes independent => by
      obtain ⟨solvable, fFresh, gFresh, distinct, -, -⟩ := independent_iff.mp independent
      rcases refutes with present | present | same | ⟨-, refuted⟩
      · exact fFresh present
      · exact gFresh present
      · exact distinct same
      · exact refutedAt_sound fuel s.knowledge refuted solvable)

/-- **On pattern knowledge the check answers at some budget**, for guard-free firings. -/
theorem helperCheck_decides (s : State S O) [DecidableEq s.frame.Names]
    (patterned : ContextualPatternFragment.ProblemPattern s.knowledge) :
    ∃ fuel, ∀ f g : Firing s, f.guards = [] → g.guards = [] →
      (helperCheck s fuel).verdict f g ≠ .unknown := by
  obtain ⟨fuel, finished⟩ := ContextualPatternTermination.finishes s.knowledge patterned
  have checked : ContextualPatternFragment.checkProblem s.knowledge = true :=
    (ContextualPatternFragment.checkProblem_iff _).mpr patterned
  have answered : solvedAt fuel s.knowledge = true ∨ refutedAt fuel s.knowledge = true := by
    unfold solvedAt refutedAt
    generalize ContextualFrameWorklist.run fuel s.frame.arity s.knowledge = result at finished ⊢
    cases finished with
    | solved update empty =>
        left
        simp [empty]
    | refuted proof =>
        right
        rfl
  refine ⟨fuel, fun f g fNone gNone => ?_⟩
  have decided : (f.made ∉ s.present ∧ g.made ∉ s.present ∧ f.made ≠ g.made ∧
        f.guards.isEmpty = true ∧ g.guards.isEmpty = true ∧
        ContextualPatternFragment.checkProblem s.knowledge = true ∧ solvedAt fuel s.knowledge = true) ∨
      (f.made ∈ s.present ∨ g.made ∈ s.present ∨ f.made = g.made ∨
        (ContextualPatternFragment.checkProblem s.knowledge = true ∧ refutedAt fuel s.knowledge = true)) := by
    by_cases fUsed : f.made ∈ s.present
    · exact .inr (.inl fUsed)
    by_cases gUsed : g.made ∈ s.present
    · exact .inr (.inr (.inl gUsed))
    by_cases same : f.made = g.made
    · exact .inr (.inr (.inr (.inl same)))
    rcases answered with solved | refuted
    · exact .inl ⟨fUsed, gUsed, same, List.isEmpty_iff.mpr fNone, List.isEmpty_iff.mpr gNone, checked, solved⟩
    · exact .inr (.inr (.inr (.inr ⟨checked, refuted⟩)))
  simp only [helperCheck, Transport.Check.ofTests]
  split_ifs with holds refutes
  · simp
  · simp
  · exact (decided.elim holds refutes).elim

/-- **Off the pattern fragment the check answers unknown** for fresh, distinct occurrences, at every
budget. -/
theorem helperCheck_unknown (s : State S O) [DecidableEq s.frame.Names] (fuel : Nat) {f g : Firing s}
    (outside : ContextualPatternFragment.checkProblem s.knowledge = false)
    (fFresh : f.made ∉ s.present) (gFresh : g.made ∉ s.present) (distinct : f.made ≠ g.made) :
    (helperCheck s fuel).verdict f g = .unknown := by
  simp [helperCheck, Transport.Check.ofTests, outside, fFresh, gFresh, distinct]

end Pattern

/-! ## A non-pattern pair

Its knowledge `M(3) = 3` applies a metavariable to a constant, outside the pattern fragment, and is
solvable (`M ↦ λx. 3`). The pair is independent, and the check answers unknown at every budget. -/

namespace NonPattern

open Consumer (tiny constant)

/-- One metavariable `M` with one parameter. -/
abbrev frame : Frame tiny := ⟨Unit, fun _ => ([()], ())⟩

/-- `M(3)`. -/
def applied : Term (signature tiny frame.arity) [] () :=
  .op (.inr (.mk ())) (.cons (constant 3) .nil)

/-- The knowledge `M(3) = 3`, kept as a residual store. -/
abbrev state : State tiny Nat := ⟨frame, [(observe applied, observe (constant (Γ := []) 3))], ∅⟩

def first : Firing state := ⟨1, ([], ()), constant 0, []⟩

def second : Firing state := ⟨2, ([], ()), constant 0, []⟩

theorem solvable : (Frames.contextual tiny).Solvable state.knowledge := by
  refine ⟨frame, fun _ => constant 3, ?_⟩
  intro e member
  obtain rfl := List.mem_singleton.mp member
  rfl

theorem outside : ContextualPatternFragment.checkProblem state.knowledge = false := by
  decide

theorem independent : (helperTransport (S := tiny) (O := Nat)).Independent state first second :=
  independent_iff.mpr ⟨solvable, by decide, by decide, by decide, asks_nil, asks_nil⟩

theorem unknown (fuel : Nat) : (helperCheck state fuel).verdict first second = .unknown :=
  helperCheck_unknown state fuel outside (by decide) (by decide) (by decide)

end NonPattern

end Helpers

#print axioms Helpers.liftIso
#print axioms Helpers.information_move
#print axioms Helpers.admits_iff
#print axioms Helpers.helper_closes
#print axioms Helpers.independent_iff
#print axioms Helpers.Consumer.independent
#print axioms Helpers.Consumer.residuals
#print axioms Helpers.Consumer.composites_differ
#print axioms Helpers.pattern_solvable_iff
#print axioms Helpers.pattern_unsolvable_iff
#print axioms Helpers.helperCheck_decides
#print axioms Helpers.helperCheck_unknown
#print axioms Helpers.NonPattern.independent
#print axioms Helpers.NonPattern.unknown

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface
