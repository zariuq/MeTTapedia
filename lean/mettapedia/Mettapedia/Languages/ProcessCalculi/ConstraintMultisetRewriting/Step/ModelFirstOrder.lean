import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.ModelHenkin
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FirstOrder
import Mettapedia.Logic.LP.FirstOrderBridge
import Mettapedia.Logic.LP.Matching

/-!
# The first-order run layer in set models

The run layer is the one-frame instance `firstOrder A label` of the step. This module reads it in
Henkin models of its one frame, and for first-order terms in set models: first-order structures,
whose points are assignments of their elements to the variables.

**Every Henkin model, every admitted firing** (`firstOrder_model_transition`). At a point satisfying
the firing's result, the knowledge before it holds; the taken and read patterns evaluate to the
values of the occurrences they select; the produced terms evaluate to the values of the made
occurrences; and **the present occurrences, read as a finite multiset of model elements, lose the
taken values and gain the made ones** (`fire_val_map`). With a point at all, every admitted firing
has one satisfying its information (`firstOrder_realized`).

**Set models of first-order terms** (`setModel`): a structure of mathlib's first-order model theory
for the language of the signature. Evaluation is `FirstOrderBridge.realizeTerm`, naturality is the
substitution lemma.
* **The free term algebra** (`termModel`): terms as elements, substitutions as points. It is free
  (`termModel_free`), and **the asks of the run layer are exactly validity in it**
  (`entails_iff_termModel`): one set model, with inhabited sorts, is sound and complete.
* **The Herbrand model** (`herbrandModel`): ground terms as elements, groundings as points. It is free
  (`herbrandModel_free`), so every ask holds at its points (`herbrand_sound`). It is not complete:
  the case split in `ModelControls`.
* Set models in general realize every admitted firing (`setModel_realized`); they are not sound for
  asks, and a store can have a set point without being solvable (`ModelControls`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRuns

open Interface (Frames GuardFormula)
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits (Enabled fire)

universe uT uS uO uV uP

section OneFrame

variable {T : Type uT} {S : Type uS} {O : Type uO} [DecidableEq O]
  {A : SubstitutionAction T S} {Val : Type uV} {Pt : PUnit.{1} → Type uP}
  (M : (Frames.ofSubstitution A).HenkinModel Val Pt)

omit [DecidableEq O] in
/-- A point satisfying the equations between patterns and selected labels evaluates the patterns to
the selected values. -/
theorem models_equations_values (label : O → T) (ρ : Pt PUnit.unit) :
    ∀ {patterns : List T} {selected : List O}, patterns.length = selected.length →
      M.Models ρ (Selection.equations label patterns selected) →
        patterns.map (fun p => M.eval p ρ) = selected.map (fun o => M.eval (label o) ρ)
  | [], [], _, _ => rfl
  | [], _ :: _, lengths, _ => by simp at lengths
  | _ :: _, [], lengths, _ => by simp at lengths
  | p :: patterns, o :: selected, lengths, known => by
      have head : M.kernel ρ p (label o) :=
        known (p, label o) (by simp [Selection.equations])
      have rest : M.Models ρ (Selection.equations label patterns selected) := fun e member =>
        known e (by simp only [Selection.equations, List.zipWith_cons_cons, List.mem_cons]; exact Or.inr member)
      simp only [List.map_cons]
      rw [models_equations_values label ρ (Nat.succ.inj lengths) rest]
      exact congrArg (· :: _) head

/-- **Firing on present occurrences, as multisets of values**: the taken values leave and the made
values arrive. -/
theorem fire_val_map {W : Finset O} {taken made : List O} (takenNodup : taken.Nodup)
    (madeNodup : made.Nodup) (inside : taken.toFinset ⊆ W) (fresh : Disjoint made.toFinset W) [DecidableEq Val]
    (v : O → Val) :
    ((W \ taken.toFinset) ∪ made.toFinset).val.map v =
      W.val.map v - (taken : Multiset O).map v + (made : Multiset O).map v := by
  have disjoint : Disjoint (W \ taken.toFinset) made.toFinset :=
    fresh.symm.mono_left Finset.sdiff_subset
  have le : (taken : Multiset O) ≤ W.val := by
    have := Finset.val_le_iff.mpr inside
    rwa [List.toFinset_val, takenNodup.dedup] at this
  rw [← Finset.disjUnion_eq_union _ _ disjoint, Finset.disjUnion_val, Finset.sdiff_val,
    List.toFinset_val, List.toFinset_val, takenNodup.dedup, madeNodup.dedup, Multiset.map_add]
  congr 1
  have split : W.val = W.val - (taken : Multiset O) + (taken : Multiset O) := (tsub_add_cancel_of_le le).symm
  conv_rhs => rw [split, Multiset.map_add]
  rw [add_tsub_cancel_right]

variable (label : O → T)

/-- **An admitted first-order firing in a Henkin model.** At a point satisfying its result, the
knowledge before it holds, the taken and read patterns evaluate to the selected values, the produced
terms to the made values, and the present values lose the taken and gain the made ones. -/
theorem firstOrder_model_transition {C : Configuration T O} {f : Firing T S O}
    (valid : f.Valid A label C) (ρ : Pt PUnit.unit) [DecidableEq Val]
    (known : M.Models ρ (f.result label C).equations) :
    M.Models ρ C.equations ∧
      f.rule.take.map (fun p => M.eval p ρ) = f.selection.taken.map (fun o => M.eval (label o) ρ) ∧
      f.rule.read.map (fun p => M.eval p ρ) = f.selection.read.map (fun o => M.eval (label o) ρ) ∧
      f.rule.produce.map (fun p => M.eval p ρ) = f.selection.made.map (fun o => M.eval (label o) ρ) ∧
      (f.result label C).present.val.map (fun o => M.eval (label o) ρ) =
        C.present.val.map (fun o => M.eval (label o) ρ) -
          (f.selection.taken : Multiset O).map (fun o => M.eval (label o) ρ) +
          (f.selection.made : Multiset O).map (fun o => M.eval (label o) ρ) := by
  have firing := valid.firing
  have problem : M.Models ρ (f.selection.problem label f.rule C) := known
  unfold Selection.problem at problem
  refine ⟨fun e member => problem e (by simp [member]), ?_, ?_, ?_, ?_⟩
  · exact models_equations_values M label ρ firing.take_length
      (fun e member => problem e (by simp [member]))
  · exact models_equations_values M label ρ firing.read_length
      (fun e member => problem e (by simp [member]))
  · rw [← firing.outputs, List.map_map]
    rfl
  · exact fire_val_map firing.take_distinct firing.output_distinct firing.occurrences.taken_subset
      firing.occurrences.fresh _

/-- **Every admitted first-order firing is realized** in a Henkin model with a point. -/
theorem firstOrder_realized (inhabited : Nonempty (Pt PUnit.unit)) {C : Configuration T O}
    {f : Firing T S O} (valid : f.Valid A label C) :
    ∃ ρ : Pt PUnit.unit, M.Models ρ (f.result label C).equations :=
  M.exists_point_of_solvable (fun _ => inhabited)
    ((Frames.ofSubstitution_solvable_iff A _).mpr valid.firing.consistent)

/-- **The flow of a firing at a point**: the values it takes and the values it makes, in the
commutative monoid of pairs of multisets. -/
def flow (ρ : Pt PUnit.unit) (f : Firing T S O) : Multiplicative (Multiset Val × Multiset Val) :=
  Multiplicative.ofAdd ((f.selection.taken : Multiset O).map (fun o => M.eval (label o) ρ),
    (f.selection.made : Multiset O).map (fun o => M.eval (label o) ρ))

/-- **Values are conserved along runs**: at every point, the present values at the end of a run
together with everything it took are the present values at its start together with everything it
made. The flow is an account, so it is a functor out of the free category of runs
(`Step.Run.account_append`). -/
theorem run_conservation [DecidableEq Val] (ρ : Pt PUnit.unit) :
    ∀ {C : Configuration T O} (r : (firstOrder A label).Run C),
      r.last.present.val.map (fun o => M.eval (label o) ρ) +
          (Multiplicative.toAdd (r.account fun _ f => flow M label ρ f)).1 =
        C.present.val.map (fun o => M.eval (label o) ρ) +
          (Multiplicative.toAdd (r.account fun _ f => flow M label ρ f)).2
  | _, .nil _ => by
      show _ + (Multiplicative.toAdd (1 : Multiplicative (Multiset Val × Multiset Val))).1 =
        _ + (Multiplicative.toAdd (1 : Multiplicative (Multiset Val × Multiset Val))).2
      simp only [toAdd_one, Prod.fst_zero, Prod.snd_zero, add_zero]
      rfl
  | C, .cons f admitted rest => by
      have later := run_conservation ρ rest
      have firing := (show f.Valid A label C from admitted).firing
      have law := fire_val_map (Val := Val) firing.take_distinct firing.output_distinct
        firing.occurrences.taken_subset firing.occurrences.fresh (fun o => M.eval (label o) ρ)
      have le : (f.selection.taken : Multiset O).map (fun o => M.eval (label o) ρ) ≤
          C.present.val.map (fun o => M.eval (label o) ρ) := by
        apply Multiset.map_le_map
        have sub : f.selection.taken.toFinset ⊆ C.present := firing.occurrences.taken_subset
        have := Finset.val_le_iff.mpr sub
        rwa [List.toFinset_val, firing.take_distinct.dedup] at this
      set taken := (f.selection.taken : Multiset O).map (fun o => M.eval (label o) ρ)
      set made := (f.selection.made : Multiset O).map (fun o => M.eval (label o) ρ)
      set before := C.present.val.map (fun o => M.eval (label o) ρ)
      set restFlow := Multiplicative.toAdd (rest.account fun _ f => flow M label ρ f)
      have result : (f.result label C).present.val.map (fun o => M.eval (label o) ρ) =
          before - taken + made := law
      have split : before = before - taken + taken := (tsub_add_cancel_of_le le).symm
      show rest.last.present.val.map (fun o => M.eval (label o) ρ) + (taken + restFlow.1) =
        before + (made + restFlow.2)
      have later' : rest.last.present.val.map (fun o => M.eval (label o) ρ) + restFlow.1 =
          before - taken + made + restFlow.2 := by
        rw [← result]
        exact later
      calc rest.last.present.val.map (fun o => M.eval (label o) ρ) + (taken + restFlow.1)
          = (rest.last.present.val.map (fun o => M.eval (label o) ρ) + restFlow.1) + taken := by abel
        _ = before - taken + made + restFlow.2 + taken := by rw [later']
        _ = (before - taken + taken) + (made + restFlow.2) := by ac_rfl
        _ = before + (made + restFlow.2) := by rw [← split]

end OneFrame

/-! ## Set models of first-order terms -/

section SetModels

open Mettapedia.Logic.LP
open Mettapedia.Logic.LP.FirstOrderBridge (language realizeTerm realizeTerm_applyTerm herbrandStructure
  realizeTerm_herbrand)

variable {σ : LPSignature}

/-- **The set model of a first-order structure**: points are assignments of its elements to the
variables, and evaluation is realization. -/
def setModel (Model : Type*) [(language σ).Structure Model] :
    (Frames.ofSubstitution (FirstOrder.action σ)).HenkinModel Model (fun _ => σ.vars → Model) where
  eval t ρ := realizeTerm ρ t
  pull θ ρ := fun v => realizeTerm ρ (θ v)
  eval_act θ t ρ := realizeTerm_applyTerm ρ θ t
  eval_E same ρ := congrArg (realizeTerm ρ) same

/-- **Set models realize admitted firings**: in a nonempty structure, every admitted firing of the
run layer has a point satisfying its information. -/
theorem setModel_realized (Model : Type*) [(language σ).Structure Model] [Nonempty Model]
    {O : Type uO} [DecidableEq O] (label : O → Term σ) {C : Configuration (Term σ) O}
    {f : Firing (Term σ) (Subst σ) O} (valid : f.Valid (FirstOrder.action σ) label C) :
    ∃ ρ : σ.vars → Model, (setModel Model).Models (a := PUnit.unit) ρ (f.result label C).equations :=
  firstOrder_realized (setModel Model) label ⟨fun _ => Classical.arbitrary Model⟩ valid

/-- The free term algebra as a first-order structure: symbols build terms. -/
@[instance_reducible] def termStructure : (language σ).Structure (Term σ) where
  funMap
    | .constant symbol, _ => .const symbol
    | .function symbol, arguments => .app symbol arguments
  RelMap _ _ := False

theorem realizeTerm_termStructure (θ : Subst σ) (t : Term σ) :
    @realizeTerm σ (Term σ) termStructure θ t = θ.applyTerm t := by
  let _ := termStructure (σ := σ)
  induction t with
  | var => rfl
  | const => rfl
  | app symbol arguments ih =>
    change Term.app symbol (fun position => realizeTerm θ (arguments position)) = _
    simp only [Subst.applyTerm, ih]

/-- **The free term algebra as a set model**: its points are the substitutions. -/
abbrev termModel (σ : LPSignature) :
    (Frames.ofSubstitution (FirstOrder.action σ)).HenkinModel (Term σ) (fun _ => σ.vars → Term σ) :=
  @setModel σ (Term σ) termStructure

theorem termModel_realizes (θ : Subst σ) :
    (termModel σ).Realizes (a := PUnit.unit) (b := PUnit.unit) θ θ := fun s t => by
  show @realizeTerm σ (Term σ) termStructure θ s = @realizeTerm σ (Term σ) termStructure θ t ↔
    θ.applyTerm s = θ.applyTerm t
  rw [realizeTerm_termStructure, realizeTerm_termStructure]

/-- **The free term algebra is a free model.** -/
theorem termModel_free : (termModel σ).Free := fun _ θ => ⟨PUnit.unit, θ, termModel_realizes θ⟩

/-- **The asks of the run layer are exactly validity in the free term algebra.** -/
theorem entails_iff_termModel {O : Type uO} (store : EquationStore (Term σ))
    (φ : GuardFormula (Term σ) O) :
    (Frames.ofSubstitution (FirstOrder.action σ)).Entails (a := PUnit.unit) store
        (fun b θ => (Frames.ofSubstitution (FirstOrder.action σ)).Satisfies (a := PUnit.unit) (b := b) θ φ) ↔
      ∀ ρ : σ.vars → Term σ, (termModel σ).Models (a := PUnit.unit) ρ store →
        (termModel σ).Satisfies (a := PUnit.unit) ρ φ := by
  constructor
  · exact fun asked ρ known => Frames.HenkinModel.sound termModel_free asked ρ known
  · intro valid _ θ solved
    exact (Frames.HenkinModel.satisfies_iff_of_realizes (termModel_realizes θ) φ).mp
      (valid θ ((Frames.HenkinModel.models_iff_of_realizes (termModel_realizes θ) store).mpr solved))

/-- **The Herbrand model**: ground terms, with groundings as points. -/
abbrev herbrandModel (σ : LPSignature) :
    (Frames.ofSubstitution (FirstOrder.action σ)).HenkinModel (GroundTerm σ)
      (fun _ => σ.vars → GroundTerm σ) :=
  @setModel σ (GroundTerm σ) (herbrandStructure ∅)

theorem herbrandModel_realizes (g : σ.vars → GroundTerm σ) :
    (herbrandModel σ).Realizes (a := PUnit.unit) (b := PUnit.unit) g (Grounding.toSubst g) :=
  fun s t => by
    show @realizeTerm σ (GroundTerm σ) (herbrandStructure ∅) g s =
        @realizeTerm σ (GroundTerm σ) (herbrandStructure ∅) g t ↔
      (Grounding.toSubst g).applyTerm s = (Grounding.toSubst g).applyTerm t
    have hs : @realizeTerm σ (GroundTerm σ) (herbrandStructure ∅) g s = Grounding.groundTerm g s :=
      realizeTerm_herbrand ∅ g s
    have ht : @realizeTerm σ (GroundTerm σ) (herbrandStructure ∅) g t = Grounding.groundTerm g t :=
      realizeTerm_herbrand ∅ g t
    have hs' : (Grounding.groundTerm g s).toTerm = (Grounding.toSubst g).applyTerm s :=
      Grounding.groundTerm_toTerm g s
    have ht' : (Grounding.groundTerm g t).toTerm = (Grounding.toSubst g).applyTerm t :=
      Grounding.groundTerm_toTerm g t
    rw [hs, ht, ← hs', ← ht']
    exact ⟨congrArg GroundTerm.toTerm, fun same => GroundTerm.toTerm_injective same⟩

/-- **The Herbrand model is free.** -/
theorem herbrandModel_free : (herbrandModel σ).Free :=
  fun _ g => ⟨PUnit.unit, Grounding.toSubst g, herbrandModel_realizes g⟩

/-- **Every ask holds at the Herbrand points.** -/
theorem herbrand_sound {O : Type uO} {store : EquationStore (Term σ)} {φ : GuardFormula (Term σ) O}
    (asked : (Frames.ofSubstitution (FirstOrder.action σ)).Entails (a := PUnit.unit) store
      (fun b θ => (Frames.ofSubstitution (FirstOrder.action σ)).Satisfies (a := PUnit.unit) (b := b) θ φ))
    (g : σ.vars → GroundTerm σ) (known : (herbrandModel σ).Models (a := PUnit.unit) g store) :
    (herbrandModel σ).Satisfies (a := PUnit.unit) g φ :=
  Frames.HenkinModel.sound herbrandModel_free asked g known

end SetModels

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRuns

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting

#print axioms AnnotatedRuns.models_equations_values
#print axioms AnnotatedRuns.fire_val_map
#print axioms AnnotatedRuns.firstOrder_model_transition
#print axioms AnnotatedRuns.firstOrder_realized
#print axioms AnnotatedRuns.run_conservation
#print axioms AnnotatedRuns.setModel
#print axioms AnnotatedRuns.setModel_realized
#print axioms AnnotatedRuns.realizeTerm_termStructure
#print axioms AnnotatedRuns.termModel_free
#print axioms AnnotatedRuns.entails_iff_termModel
#print axioms AnnotatedRuns.herbrandModel_free
#print axioms AnnotatedRuns.herbrand_sound

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
