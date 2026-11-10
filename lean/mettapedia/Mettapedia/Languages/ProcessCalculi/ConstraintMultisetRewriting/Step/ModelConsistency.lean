import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.ModelControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.ModelDerivation
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.DependentClosed

/-!
# Models of the step's rules, and consistency of the proof logic

**An independent set model of the first-order step** (`AnnotatedRuns.firstOrder_set_model`). For
every universe `u` and every first-order structure `Model : Type u` with an element: every admitted
firing has a point of its information; at every point satisfying a firing's result, the knowledge
before it holds and the present values change by the firing's taken and made values; and along every
run the values are conserved. The closed-empty-obligation controls are in `ModelControls`
(`emptySort_separates`, `constructorFree_separates`) and, for contextual frames, `ModelContextual`
(`SwapControl.separates`).

**Consistency of the proof logic** (`AnnotatedRuns.certainChecks_consistent`). The proof logic is the
certain-check calculus of `ModelDerivation` (`CertainChecks.Derives`) and derivable admission
(`CertainChecks.AdmitsDerivably`), which is admission for query-free firings. For distinct constants
`c ≠ d`, the judgment `c = d` is derivable from no store, and the admission of the firing that tells
`c = d` is not derivable. The proof is by soundness in the free term algebra. Hypotheses: two distinct
constants. Axioms: `propext`, `Quot.sound`, `Classical.choice`. Universe: that of the signature's
terms. No universe tower and no inaccessible cardinal is used.

**Realization** (soundness of the rules in models, not consistency):
* every step whose guards are in the guard syntax is realized in the generic model, with no
  hypothesis (`Step.generic_model`); a store has a generic point exactly when it is solvable;
* closed admission is admission read in the closed stage (`Step.closedAdmits_iff_stage`), and
  follows from admission at a weakly terminal closed frame (`Step.closedAdmits_of_admits`);
* in the first-order run layer every admitted firing is realized in the free term algebra with its
  full `Holds`, predicate queries included (`firstOrder_termModel_realizes`), and at a ground point
  of the Herbrand model as soon as one ground term exists (`firstOrder_herbrand_realizes`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface

open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits (Enabled)

universe uO uT uH uOcc uS uF

namespace Frames

variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH} {X : Frames Tm Hom}

/-- The generic model has a point at every frame: its identity. -/
theorem generic_inhabited (X : Frames Tm Hom) (a : Obj) : Nonempty (Σ b : Obj, Hom a b) :=
  ⟨⟨a, X.id a⟩⟩

/-- Closed asks at every closed solution are the closed entailment of `DependentClosed`. -/
theorem asks_closedEvery_iff {O : Type uOcc} (point : Obj) {a : Obj} (store : EquationStore (Tm a))
    (φ : GuardFormula (Tm a) O) :
    X.Asks point store (.closedEvery φ) ↔ X.ClosedEntails point store fun f => X.Satisfies f φ :=
  Iff.rfl

/-- Closed solvability is the closed ask `closedSome ⊤`. -/
theorem closedSolvable_iff_closedSome_top {O : Type uOcc} (point : Obj) {a : Obj}
    (store : EquationStore (Tm a)) :
    X.ClosedSolvable point store ↔ X.Asks (O := O) point store (.closedSome .top) :=
  ⟨fun ⟨f, solved⟩ => ⟨f, solved, trivial⟩, fun ⟨f, solved, _⟩ => ⟨f, solved⟩⟩

/-- **A free model realizes no unsolvable store.** -/
theorem HenkinModel.no_point_of_unsolvable {Val : Type*} {Pt : Obj → Type*}
    {M : X.HenkinModel Val Pt} (free : M.Free) {a : Obj} {store : EquationStore (Tm a)}
    (unsolvable : ¬ X.Solvable store) (q : Pt a) : ¬ M.Models q store := fun known => by
  obtain ⟨b, f, realized⟩ := free a q
  exact unsolvable ⟨b, f, (HenkinModel.models_iff_of_realizes realized store).mp known⟩

end Frames

namespace Step

variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}
  {X : Frames Tm Hom} {O : Type uOcc} [DecidableEq O] {State : Type uS} {Firing : State → Type uF}
  (P : Step X O State Firing)
  [P.Guarded]

/-- **Every step whose guards are written in the guard syntax has a model of its rules, with no
hypothesis**: in the generic model, every admitted firing has a point of its information that
satisfies its guards. -/
theorem generic_model {guard : ∀ {s : State} (f : Firing s), GuardFormula (Tm (P.target f)) O}
    (guarded : P.GuardedBy guard) {s : State} {f : Firing s} (admitted : P.Admits f) :
    ∃ q : Σ b : Obj, Hom (P.target f) b,
      (Frames.generic X).Models q (P.information f) ∧ (Frames.generic X).Satisfies q (guard f) :=
  P.realized_guards (Frames.generic X) (Frames.generic_inhabited X) Frames.generic_free guarded admitted

/-- **Closed admission is admission read in the closed stage.** -/
theorem closedAdmits_iff_stage {guard : ∀ {s : State} (f : Firing s), GuardFormula (Tm (P.target f)) O}
    (guarded : P.GuardedBy guard) (point : Obj) {s : State} (f : Firing s) :
    P.ClosedAdmits point f ↔ P.Shapes f ∧
      Enabled (fun _ : O => ()) (P.present s) ((P.selection f).commit (T := Unit)) ∧
      (∃ q : Hom (P.target f) point, (Frames.stage X point).Models q (P.information f)) ∧
      ∀ q : Hom (P.target f) point, (Frames.stage X point).Models q (P.information f) →
        (Frames.stage X point).Satisfies q (guard f) := by
  refine and_congr Iff.rfl (and_congr Iff.rfl (and_congr ?_ ?_))
  · exact exists_congr fun q =>
      (Frames.HenkinModel.models_iff_of_realizes (Frames.stage_kernel q) (P.information f)).symm
  · exact forall_congr' fun q => imp_congr
      (Frames.HenkinModel.models_iff_of_realizes (Frames.stage_kernel q) (P.information f)).symm
      ((guarded f point q).trans
        (Frames.HenkinModel.satisfies_iff_of_realizes (Frames.stage_kernel q) (guard f)).symm)

/-- **At a weakly terminal closed frame, admission implies closed admission.** -/
theorem closedAdmits_of_admits {point : Obj} (terminal : Frames.WeaklyTerminal Hom point)
    {s : State} {f : Firing s} (admitted : P.Admits f) : P.ClosedAdmits point f := by
  obtain ⟨shapes, enabled, solvable, asked⟩ := (P.admits_iff f).mp admitted
  exact ⟨shapes, enabled, (Frames.closedSolvable_iff_of_weaklyTerminal terminal _).mpr solvable,
    Frames.Entails.closed asked⟩

end Step

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRuns

open Interface (Frames)
open Mettapedia.Logic.LP

universe uO

variable {σ : LPSignature} {O : Type uO} [DecidableEq O] (label : O → Term σ)

/-- **In the free term algebra, every admitted firing is realized with its full `Holds`**, predicate
queries included, for every signature. -/
theorem firstOrder_termModel_realizes {C : Configuration (Term σ) O} {f : Firing (Term σ) (Subst σ) O}
    (valid : f.Valid (FirstOrder.action σ) label C) :
    ∃ θ : σ.vars → Term σ, (termModel σ).Models (a := PUnit.unit) θ (f.result label C).equations ∧
      (firstOrder (FirstOrder.action σ) label).Holds (s := C) f PUnit.unit θ := by
  obtain ⟨_, _, ⟨_, θ, solved⟩, asked⟩ := (firstOrder (FirstOrder.action σ) label).admits_iff (s := C) f |>.mp valid
  exact ⟨θ, (Frames.HenkinModel.models_iff_of_realizes (termModel_realizes θ) _).mpr solved,
    asked PUnit.unit θ solved⟩

/-- **In the Herbrand model, every admitted firing is realized at a ground point with its full
`Holds`**, as soon as one ground term exists. -/
theorem firstOrder_herbrand_realizes (ground : GroundTerm σ) {C : Configuration (Term σ) O}
    {f : Firing (Term σ) (Subst σ) O} (valid : f.Valid (FirstOrder.action σ) label C) :
    ∃ g : σ.vars → GroundTerm σ, (herbrandModel σ).Models (a := PUnit.unit) g (f.result label C).equations ∧
      (firstOrder (FirstOrder.action σ) label).Holds (s := C) f PUnit.unit (Grounding.toSubst g) := by
  obtain ⟨_, _, ⟨_, θ, solved⟩, asked⟩ := (firstOrder (FirstOrder.action σ) label).admits_iff (s := C) f |>.mp valid
  let base : Grounding σ := fun _ => ground
  let g : σ.vars → GroundTerm σ := fun v => Grounding.groundTerm base (θ v)
  have through : Grounding.toSubst g = Subst.comp (Grounding.toSubst base) θ :=
    funext fun v => Grounding.groundTerm_toTerm base (θ v)
  have models : (FirstOrder.action σ).Models (Grounding.toSubst g) (f.result label C).equations := by
    rw [through]
    exact (FirstOrder.action σ).models_compose solved _
  exact ⟨g, (Frames.HenkinModel.models_iff_of_realizes (herbrandModel_realizes g) _).mpr models,
    asked PUnit.unit _ models⟩

/-- The firing that tells `c = d` is not admitted, at any configuration (an operational fact; the
consistency statement is about derivability, `certainChecks_consistent`). -/
theorem tellClash_refused {c d : σ.constants} (distinct : c ≠ d) (C : Configuration (Term σ) O) :
    ¬ (tellClash (O := O) c d).Valid (FirstOrder.action σ) label C := by
  intro valid
  obtain ⟨θ, solved⟩ := valid.firing.consistent
  have told : (FirstOrder.action σ).Solves θ (.const c, .const d) :=
    solved _ (by simp [Selection.problem, tellClash])
  exact distinct (Term.const.inj told)

/-- **Distinct constants are not unified**, so no free model has a point where they are equal; in
particular neither the free term algebra nor the Herbrand model. -/
theorem clash_unsolvable {c d : σ.constants} (distinct : c ≠ d) :
    ¬ (Frames.ofSubstitution (FirstOrder.action σ)).Solvable (a := PUnit.unit)
      [((.const c : Term σ), (.const d : Term σ))] := by
  rintro ⟨_, θ, solved⟩
  exact distinct (Term.const.inj (solved _ (List.mem_singleton_self _)))

theorem clash_no_herbrand_point {c d : σ.constants} (distinct : c ≠ d) (g : σ.vars → GroundTerm σ) :
    ¬ (herbrandModel σ).Models (a := PUnit.unit) g [((.const c : Term σ), (.const d : Term σ))] :=
  Frames.HenkinModel.no_point_of_unsolvable herbrandModel_free (clash_unsolvable distinct) g

/-- **Consistency of the certain-check calculus.** For distinct constants `c ≠ d`, the judgment
`c = d` is derivable from no store, and the admission of the firing that tells `c = d` is not
derivable, at any configuration. -/
theorem certainChecks_consistent {σ : LPSignature} [DecidableEq σ.vars] [DecidableEq σ.constants]
    [DecidableEq σ.functionSymbols] {O : Type} [DecidableEq O] (label : O → Term σ) {c d : σ.constants}
    (distinct : c ≠ d) :
    (∀ (problem : EquationStore (Term σ)) (world : Finset O),
      ¬ CertainChecks.Derives problem label world (.equal (.const c) (.const d))) ∧
      ∀ C : Configuration (Term σ) O, ¬ CertainChecks.AdmitsDerivably label C (tellClash (O := O) c d) :=
  ⟨fun problem world => CertainChecks.not_derives_clash distinct problem world,
    fun C => CertainChecks.not_admitsDerivably_clash distinct C⟩

universe u

/-- **An independent set model of the first-order step**, in any universe `u`. For a first-order
structure with an element: every admitted firing has a point of its information; at a point of a
firing's result the knowledge before it holds and the present values lose the taken and gain the made
values; and along every run the present values are conserved against the run's flow. -/
theorem firstOrder_set_model (Model : Type u) [FirstOrderBridge.language σ |>.Structure Model]
    [Nonempty Model] [DecidableEq Model] :
    (∀ (C : Configuration (Term σ) O) (f : Firing (Term σ) (Subst σ) O), f.Valid (FirstOrder.action σ) label C →
      ∃ ρ : σ.vars → Model, (setModel Model).Models (a := PUnit.unit) ρ (f.result label C).equations) ∧
    (∀ (C : Configuration (Term σ) O) (f : Firing (Term σ) (Subst σ) O), f.Valid (FirstOrder.action σ) label C →
      ∀ ρ : σ.vars → Model, (setModel Model).Models (a := PUnit.unit) ρ (f.result label C).equations →
        (setModel Model).Models (a := PUnit.unit) ρ C.equations ∧
        (f.result label C).present.val.map (fun o => (setModel Model).eval (a := PUnit.unit) (label o) ρ) =
          C.present.val.map (fun o => (setModel Model).eval (a := PUnit.unit) (label o) ρ) -
            (f.selection.taken : Multiset O).map (fun o => (setModel Model).eval (a := PUnit.unit) (label o) ρ) +
            (f.selection.made : Multiset O).map (fun o => (setModel Model).eval (a := PUnit.unit) (label o) ρ)) ∧
    ∀ (C : Configuration (Term σ) O) (r : (firstOrder (FirstOrder.action σ) label).Run C) (ρ : σ.vars → Model),
      r.last.present.val.map (fun o => (setModel Model).eval (a := PUnit.unit) (label o) ρ) +
          (Multiplicative.toAdd (r.account fun _ f => flow (setModel Model) label ρ f)).1 =
        C.present.val.map (fun o => (setModel Model).eval (a := PUnit.unit) (label o) ρ) +
          (Multiplicative.toAdd (r.account fun _ f => flow (setModel Model) label ρ f)).2 :=
  ⟨fun _ _ valid => setModel_realized Model label valid,
    fun _ _ valid ρ known =>
      let t := firstOrder_model_transition (setModel Model) label valid ρ known
      ⟨t.1, t.2.2.2.2⟩,
    fun _ r ρ => run_conservation (setModel Model) label ρ r⟩

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRuns

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting

#print axioms Interface.Frames.generic_inhabited
#print axioms Interface.Frames.asks_closedEvery_iff
#print axioms Interface.Frames.closedSolvable_iff_closedSome_top
#print axioms Interface.Frames.HenkinModel.no_point_of_unsolvable
#print axioms Interface.Step.generic_model
#print axioms Interface.Step.closedAdmits_iff_stage
#print axioms Interface.Step.closedAdmits_of_admits
#print axioms AnnotatedRuns.firstOrder_termModel_realizes
#print axioms AnnotatedRuns.firstOrder_herbrand_realizes
#print axioms AnnotatedRuns.tellClash_refused
#print axioms AnnotatedRuns.clash_unsolvable
#print axioms AnnotatedRuns.clash_no_herbrand_point
#print axioms AnnotatedRuns.certainChecks_consistent
#print axioms AnnotatedRuns.firstOrder_set_model

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
