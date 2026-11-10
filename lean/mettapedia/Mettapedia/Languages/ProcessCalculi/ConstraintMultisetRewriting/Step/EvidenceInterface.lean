import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Evidence
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.DisequalityFramesInstances

/-!
# Runs never enter an inconsistent store, at the interface

`Evidence.not_admits_of_not_solvable` holds for every instance: knowledge without a solution admits
nothing. Its converse direction, that a run from solvable knowledge ends in solvable knowledge, is
`Evidence.firstOrder_run_consistent` for the first-order step. This module states it once.

* **The restriction** (`SettlesConservatively`, `run_solvable`): with exact result knowledge, a
  settlement keeping solvable information solvable never enters an inconsistent store. Exactness
  is needed to transfer that solution to the actual result; semantic refinement alone need not
  preserve consistency.
* **A checkable sufficient condition** (`RetractsSettlement`, `conservative_of_retracts`): the
  settlement has a retraction up to the equivalence. An identity settlement has one.
* **The bridge: it holds for every main instance** (`firstOrder_retracts`, `dependent_retracts`,
  `helper_retracts`), and it passes to disequations (`withDisequations_retracts`): every step with
  disequations over a prestep whose settlement retracts keeps it. `firstOrder_run_consistent` is a
  corollary (`old_firstOrder_run_consistent`).
* **The separating control** (`Controls.guess_enters_inconsistency`): an instance that settles by a
  guessed value instead of a solution admits a firing from solvable knowledge and enters knowledge
  without a solution.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.EvidenceInterface

open Interface (Frames)
open DisequalityFrames (Prestep Separates separates_applyStore)
open MeTTaCalculus.OccurrenceCommits (Enabled fire)

universe uO uT uH uOcc uS uF

section Generic

variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}
  {X : Frames Tm Hom} {O : Type uOcc} [DecidableEq O] {State : Type uS} {Firing : State → Type uF}
  (P : Interface.Step X O State Firing)

/-- **Settlement keeps solvable information solvable.** -/
def SettlesConservatively : Prop :=
  ∀ {s : State} (f : Firing s) (admitted : P.Admits f), X.Solvable (P.information f) →
    X.Solvable (X.applyStore (P.settle f admitted) (P.information f))

/-- **Settlement has a retraction**, up to the equivalence. -/
def RetractsSettlement : Prop :=
  ∀ {s : State} (f : Firing s) (admitted : P.Admits f),
    ∃ back : Hom (P.frame (P.result f admitted)) (P.target f),
      ∀ t : Tm (P.target f), X.E (X.act (X.comp back (P.settle f admitted)) t) t

variable {P}

/-- **A retraction makes settlement conservative.** -/
theorem conservative_of_retracts (retracts : RetractsSettlement P) : SettlesConservatively P := by
  intro s f admitted solvable
  obtain ⟨b, g, solved⟩ := solvable
  obtain ⟨back, retraction⟩ := retracts f admitted
  refine ⟨b, X.comp g back, (Frames.models_applyStore _ _ _).mpr fun e member => ?_⟩
  have kept : X.E (X.act g e.1) (X.act g e.2) := solved e member
  have first : X.E (X.act (X.comp (X.comp g back) (P.settle f admitted)) e.1) (X.act g e.1) := by
    rw [Frames.act_comp_assoc, X.act_comp]
    exact X.preserves g (retraction e.1)
  have second : X.E (X.act (X.comp (X.comp g back) (P.settle f admitted)) e.2) (X.act g e.2) := by
    rw [Frames.act_comp_assoc, X.act_comp]
    exact X.preserves g (retraction e.2)
  exact (X.equivalence b).trans first ((X.equivalence b).trans kept ((X.equivalence b).symm second))

/-- An admitted firing of a conservatively settling instance ends in solvable knowledge. -/
theorem solvable_result [P.Exact] (conservative : SettlesConservatively P) {s : State} {f : Firing s}
    (admitted : P.Admits f) : X.Solvable (P.knowledge (P.result f admitted)) := by
  obtain ⟨b, σ, solved⟩ := conservative f admitted (P.solvable_information admitted)
  exact ⟨b, σ, Interface.Step.Exact.exactness f (P.prepares admitted) σ
    ((Frames.models_applyStore _ _ _).mp solved)⟩

/-- **A conservatively settling instance never enters an inconsistent store**: every run from
solvable knowledge ends in solvable knowledge. -/
theorem run_solvable [P.Exact] (conservative : SettlesConservatively P) :
    ∀ {s : State} (r : P.Run s), X.Solvable (P.knowledge s) → X.Solvable (P.knowledge r.last)
  | _, .nil _, solvable => solvable
  | _, .cons _ admitted rest, _ => run_solvable conservative rest (solvable_result conservative admitted)

/-- An identity settlement retracts, by the identity. -/
theorem id_retraction {a : Obj} (t : Tm a) : X.E (X.act (X.comp (X.id a) (X.id a)) t) t := by
  rw [X.act_comp, X.act_id, X.act_id]
  exact (X.equivalence a).refl t

/-- Separation is invariant under pointwise equivalent actions. -/
theorem separates_of_equivalent {a b : Obj} {f g : Hom a b} (same : ∀ t, X.E (X.act f t) (X.act g t))
    {store : Disequality.DisequationStore (Tm a)} (separated : Separates X g store) : Separates X f store := by
  intro d member equated
  exact separated d member ((X.equivalence b).trans ((X.equivalence b).symm (same d.1))
    ((X.equivalence b).trans equated (same d.2)))

end Generic

/-! ## Disequations keep a retracting settlement -/

section Disequations

variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}
  {X : Frames Tm Hom} {O : Type uOcc} [DecidableEq O] {State : Type uS} {Firing : State → Type uF}
  {Q : Prestep X O State Firing}

variable (Q) in
/-- **A prestep's settlement retracts** at every firing with its shapes. -/
def PrestepRetracts : Prop :=
  ∀ {s : State} (f : Firing s) (shapes : Q.Shapes f),
    ∃ back : Hom (Q.frame (Q.result f shapes)) (Q.target f),
      ∀ t : Tm (Q.target f), X.E (X.act (X.comp back (Q.settle f shapes)) t) t

/-- Its step's settlement retracts. -/
theorem step_retracts (retracts : PrestepRetracts Q) : RetractsSettlement Q.step.toStep :=
  fun f admitted => retracts f admitted.1

/-- **The step with disequations over a prestep whose settlement retracts also retracts.** -/
theorem withDisequations_retracts (reflects : Q.step.Reflects) (retracts : PrestepRetracts Q) :
    RetractsSettlement (Q.step.withDisequations reflects) := by
  intro s f admitted
  obtain ⟨back, retraction⟩ := retracts f.base admitted.1
  refine ⟨⟨back, fun c τ separated => ?_⟩, retraction⟩
  refine (separates_applyStore _ _ _).mpr (separates_of_equivalent (fun t => ?_) separated)
  have same : X.act (X.comp (X.comp τ back) (Q.settle f.base admitted.1)) t =
      X.act τ (X.act (X.comp back (Q.settle f.base admitted.1)) t) :=
    (X.act_comp _ _ t).trans ((X.act_comp τ back _).trans (congrArg (X.act τ) (X.act_comp back _ t).symm))
  exact (congrArg (fun z => X.E z (X.act τ t)) same).mpr (X.preserves τ (retraction t))

end Disequations

/-! ## The main instances -/

section Instances

universe uA uB uC

variable {T : Type uA} {S : Type uB} {O : Type uC} [DecidableEq O] (A : SubstitutionAction T S)
  (label : O → T)

/-- **The first-order step's settlement retracts.** -/
theorem firstOrder_retracts : RetractsSettlement (AnnotatedRuns.firstOrder A label).toStep :=
  fun _ _ => ⟨A.identity, id_retraction (X := Frames.ofSubstitution A) (a := PUnit.unit)⟩

/-- The first-order prestep's settlement retracts. -/
theorem firstOrderPrestep_retracts : PrestepRetracts (DisequalityFrames.firstOrderPrestep A label) :=
  fun _ _ => ⟨A.identity, id_retraction (X := Frames.ofSubstitution A) (a := PUnit.unit)⟩

/-- **`Evidence.firstOrder_run_consistent` is a corollary.** -/
theorem old_firstOrder_run_consistent {C : Configuration T O} (r : (AnnotatedRuns.firstOrder A label).Run C)
    (consistent : A.Consistent C.equations) : A.Consistent r.last.equations := by
  have solvable := run_solvable (conservative_of_retracts (firstOrder_retracts A label)) r
    ((Frames.ofSubstitution_solvable_iff A _).mpr consistent)
  exact (Frames.ofSubstitution_solvable_iff A _).mp solvable

/-- The first-order step with disequations never enters an inconsistent store. -/
theorem firstOrderWith_run_solvable {s : (DisequalityFrames.firstOrderPrestep A label).step.DState}
    (r : (DisequalityFrames.firstOrderWith A label).Run s)
    (solvable : (DisequalityFrames.frames (Frames.ofSubstitution A)).Solvable
      (a := (DisequalityFrames.firstOrderWith A label).frame s)
      ((DisequalityFrames.firstOrderWith A label).knowledge s)) :
    (DisequalityFrames.frames (Frames.ofSubstitution A)).Solvable
      (a := (DisequalityFrames.firstOrderWith A label).frame r.last)
      ((DisequalityFrames.firstOrderWith A label).knowledge r.last) :=
  run_solvable (conservative_of_retracts (withDisequations_retracts _ (firstOrderPrestep_retracts A label)))
    r solvable

end Instances

section DependentInstance

open _root_.CategoryTheory
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open TypedEquality TypedEquality.Normalization TypedContextual
open Interface.DependentFull

variable {Head L : Type} [UniverseLevel.LevelOrder L] {rules : Rules Head}
  (levels : LevelModel rules L) (O : Type) [DecidableEq O]

/-- **The dependent full step's settlement retracts.** -/
theorem dependent_retracts : RetractsSettlement (step levels O).toStep :=
  fun f _ => ⟨(ContextualDependentEta.frames levels).id f.helpers.frame,
    id_retraction (X := ContextualDependentEta.frames levels)⟩

theorem dependentPrestep_retracts : PrestepRetracts (DisequalityFrames.Dependent.prestep levels O) :=
  fun f _ => ⟨(ContextualDependentEta.frames levels).id f.helpers.frame,
    id_retraction (X := ContextualDependentEta.frames levels)⟩

/-- **The dependent full step never enters an inconsistent store**, with or without disequations. -/
theorem dependent_run_solvable {s : State rules O} (r : (step levels O).Run s)
    (solvable : (ContextualDependentEta.frames levels).Solvable s.knowledge) :
    (ContextualDependentEta.frames levels).Solvable r.last.knowledge :=
  run_solvable (conservative_of_retracts (dependent_retracts levels O)) r solvable

theorem dependentWith_retracts : RetractsSettlement (DisequalityFrames.Dependent.withDisequations levels O) :=
  withDisequations_retracts _ (dependentPrestep_retracts levels O)

end DependentInstance

section HelperInstance

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily

variable {S : Signature} {O : Type} [DecidableEq O]

/-- **The helper step's settlement retracts.** -/
theorem helper_retracts : RetractsSettlement (Interface.Helpers.helperStep (S := S) (O := O)).toStep :=
  fun f _ => ⟨(Frames.contextual S).id (Interface.Helpers.extend _ f.helper),
    id_retraction (X := Frames.contextual S)⟩

variable (S O) in
theorem helperWith_retracts : RetractsSettlement (DisequalityFrames.Contextual.withDisequations S O) :=
  withDisequations_retracts _ fun f _ => ⟨(Frames.contextual S).id (Interface.Helpers.extend _ f.helper),
    id_retraction (X := Frames.contextual S)⟩

end HelperInstance

/-! ## The separating control: settling by a guess -/

namespace Controls

open Mettapedia.Logic.LP
open Disequality.Controls (signature A X bind)

/-- An instance whose one firing tells `X ≐ 1` and settles by the guess `X ↦ 0`. -/
def guess : Prestep (Frames.ofSubstitution A) Nat (EquationStore (Term signature)) (fun _ => Unit) where
  frame _ := PUnit.unit
  knowledge s := s
  present _ := ∅
  selection _ := ⟨[], [], []⟩
  target _ := PUnit.unit
  extension _ := A.identity
  information {s} _ := (Frames.ofSubstitution A).applyStore (a := PUnit.unit) (b := PUnit.unit) A.identity s ++
    [(X, .const 1)]
  transported _ e member := List.mem_append_left _ (List.mem_map.mpr ⟨e, member, rfl⟩)
  Shapes {s} _ := s = []
  Holds _ _ σ := (Frames.ofSubstitution A).Models (a := PUnit.unit) (b := PUnit.unit) σ []
  result {s} _ _ := (Frames.ofSubstitution A).applyStore (a := PUnit.unit) (b := PUnit.unit) (bind (.const 0))
    ((Frames.ofSubstitution A).applyStore (a := PUnit.unit) (b := PUnit.unit) A.identity s ++ [(X, .const 1)])
  present_result _ _ := by
    ext o
    simp [MeTTaCalculus.OccurrenceCommits.fire, Selection.commit]
  settle _ _ := bind (.const 0)
  knowledge_result _ _ := rfl

abbrev P := guess.step

/-- The empty selection is enabled at every store. -/
theorem enabled_nothing (store : Finset Nat) :
    Enabled (fun _ : Nat => ()) store ((⟨[], [], []⟩ : Selection Nat).commit (T := Unit)) :=
  ⟨by simp [Selection.commit], by simp [Selection.commit], by simp [Selection.commit],
    by simp [Selection.commit], by simp [Selection.commit]⟩

theorem guess_admitted : P.Admits (s := []) () := by
  refine ⟨rfl, enabled_nothing ∅, ⟨PUnit.unit, bind (.const 1), fun e member => ?_⟩,
    fun _ _ _ => show (Frames.ofSubstitution A).Models _ [] from Frames.models_nil _⟩
  rcases List.mem_append.mp member with none | told
  · exact absurd none List.not_mem_nil
  · obtain rfl := List.mem_singleton.mp told
    show A.E (A.apply (bind (.const 1)) X) (A.apply (bind (.const 1)) (.const 1))
    simp [Disequality.Controls.bind_zero]

/-- **Settling by a guess enters an inconsistent store**: from the empty knowledge, the firing is
admitted, and the knowledge after it, `0 ≐ 1`, has no solution. -/
theorem guess_enters_inconsistency :
    (Frames.ofSubstitution A).Solvable (a := PUnit.unit) (P.knowledge []) ∧
      ¬ (Frames.ofSubstitution A).Solvable (a := PUnit.unit) (P.knowledge (P.result () guess_admitted)) := by
  refine ⟨⟨PUnit.unit, A.identity, Frames.models_nil _⟩, ?_⟩
  rintro ⟨_, σ, solved⟩
  have clash := solved (A.apply (bind (.const 0)) X, A.apply (bind (.const 0)) (.const 1))
    (List.mem_map.mpr ⟨(X, .const 1), List.mem_append_right _ (List.mem_singleton_self _), rfl⟩)
  change A.E (A.apply σ (A.apply (bind (.const 0)) X)) (A.apply σ (A.apply (bind (.const 0)) (.const 1))) at clash
  simp [Disequality.Controls.bind_zero] at clash

/-- So its settlement does not retract. -/
theorem guess_not_retracts : ¬ RetractsSettlement P.toStep := fun retracts =>
  guess_enters_inconsistency.2 (solvable_result (conservative_of_retracts retracts) guess_admitted)

end Controls

#print axioms conservative_of_retracts
#print axioms run_solvable
#print axioms withDisequations_retracts
#print axioms firstOrder_retracts
#print axioms old_firstOrder_run_consistent
#print axioms firstOrderWith_run_solvable
#print axioms dependent_retracts
#print axioms dependent_run_solvable
#print axioms dependentWith_retracts
#print axioms helper_retracts
#print axioms helperWith_retracts
#print axioms Controls.guess_enters_inconsistency
#print axioms Controls.guess_not_retracts

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.EvidenceInterface
