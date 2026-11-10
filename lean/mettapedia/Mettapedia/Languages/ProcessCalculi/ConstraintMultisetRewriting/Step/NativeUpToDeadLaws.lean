import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.NativeUpToDead
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.NativeResidualSeparation

/-!
# Lawful and coherent transport up to dead names

`Transport.Coherent` and `Transport.Lawful` (`Step/LawfulTransport`) are the laws under which
independence is a property of the step. Natively they fail as stated: the residual's frame is not
separated by its two restrictions (`NativeResidualSeparation.residual_not_separated`, R83), because it
keeps dead names. This module weakens exactly what dead names break and shows the native step meets
the weakened laws.

## The laws up to dead names (`DeadTransport.Coherent`, `DeadTransport.Lawful`)

* **Coherence up to dead names**: a carrying of the firing's information frame into the residual's,
  squaring with the step's morphism (`square`); **amalgamation after a morphism out of the solutions'
  frame** (`amalgamate`), where the strict law asks for one into the same frame; the information law
  (`information`); the shapes law (`shapes`). **Separation is not asked.**
* **Admission of a residual, solvability part, mentions no residual** (`Coherent.solvable_iff`): the
  residual's information is solvable exactly when the firing's information and the step's result
  knowledge have solutions agreeing on the state's frame. Two solutions with the same restrictions
  solve the residual's information together (`Coherent.models_congr`): separation holds on what the
  information sees.
* **Conservative settlement up to dead names** (`ConservativeUpToDead`): every solution of an
  admitted firing's information extends through the settling morphism after a morphism out of its
  frame. Under it the result's knowledge is solvable exactly when the information is
  (`solvable_result_iff`): settlement chooses no solution.

## The native step meets them

On the live step, for residuals of firings that take and read nothing the step makes
(`residualsUnmade`, the residuals that independence uses):

* `coherent`: the carrying is R83's `carry`, the square is `carry_captured`, amalgamation goes to the
  first-order frame (`amalgamOf`), the information law is `information_residualAt` up to membership,
  and the shapes law uses the injectivity of the carrying (`carryExtension`);
* `conservative`: the solver's helper names go to the first-order frame;
* `lawful`: both.

The strict separation law fails (`strict_separation_fails`), so the strict `Lawful` does not hold.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface

universe uOb uTm uHm uO uSt uF uI

/-! ## The laws up to dead names -/

namespace DeadTransport

variable {Obj : Type uOb} {Tm : Obj → Type uTm} {Hom : Obj → Obj → Type uHm}
  {X : Frames Tm Hom} {O : Type uO} [DecidableEq O] {State : Type uSt} {Fir : State → Type uF}
  {P : Step X O State Fir} {T : DeadTransport.{uOb, uTm, uHm, uO, uSt, uF, uI} P}

/-- **Coherent residuals up to dead names.** Separation is not asked, and amalgamation goes through a
morphism out of the solutions' frame. -/
structure Coherent (R : T.Residuals) where
  carry : ∀ {s : State} {g : Fir s} {admitted : P.Admits g} {f : Fir s} {r : Fir (P.result g admitted)},
    R.Residual g admitted f r → Hom (P.target f) (P.target r)
  square : ∀ {s : State} {g : Fir s} {admitted : P.Admits g} {f : Fir s} {r : Fir (P.result g admitted)}
    (residual : R.Residual g admitted f r),
    X.Agree (X.comp (carry residual) (P.extension f)) (X.comp (P.extension r) (P.along g admitted))
  amalgamate : ∀ {s : State} {g : Fir s} {admitted : P.Admits g} {f : Fir s} {r : Fir (P.result g admitted)}
    (residual : R.Residual g admitted f r) (b : Obj) (σ : Hom (P.target f) b)
    (τ : Hom (P.frame (P.result g admitted)) b),
    X.Agree (X.comp σ (P.extension f)) (X.comp τ (P.along g admitted)) →
      ∃ (c : Obj) (ι : Hom b c) (ρ : Hom (P.target r) c),
        X.Agree (X.comp ρ (carry residual)) (X.comp ι σ) ∧ X.Agree (X.comp ρ (P.extension r)) (X.comp ι τ)
  information : ∀ {s : State} {g : Fir s} {admitted : P.Admits g} {f : Fir s} {r : Fir (P.result g admitted)}
    (residual : R.Residual g admitted f r),
    X.Equivalent (P.information r)
      (X.applyStore (carry residual) (P.information f) ++
        X.applyStore (P.extension r) (P.knowledge (P.result g admitted)))
  shapes : ∀ {s : State} {g : Fir s} {admitted : P.Admits g} {f : Fir s} {r : Fir (P.result g admitted)},
    R.Residual g admitted f r → (P.Shapes r ↔ P.Shapes f)

variable {R : T.Residuals}

/-- A solution of a residual's information is a solution of the firing's information and of the
step's result knowledge, read through the two restrictions. -/
theorem Coherent.models_iff (C : Coherent R) {s : State} {g : Fir s} {admitted : P.Admits g} {f : Fir s}
    {r : Fir (P.result g admitted)} (residual : R.Residual g admitted f r) {b : Obj} (ρ : Hom (P.target r) b) :
    X.Models ρ (P.information r) ↔
      X.Models (X.comp ρ (C.carry residual)) (P.information f) ∧
        X.Models (X.comp ρ (P.extension r)) (P.knowledge (P.result g admitted)) := by
  rw [C.information residual b ρ, Frames.models_append, Frames.models_applyStore, Frames.models_applyStore]

/-- **Separation on what the information sees**: two solutions with the same restrictions solve the
residual's information together. -/
theorem Coherent.models_congr (C : Coherent R) {s : State} {g : Fir s} {admitted : P.Admits g} {f : Fir s}
    {r : Fir (P.result g admitted)} (residual : R.Residual g admitted f r) {b : Obj} {ρ ρ' : Hom (P.target r) b}
    (throughCarry : X.Agree (X.comp ρ (C.carry residual)) (X.comp ρ' (C.carry residual)))
    (throughExtension : X.Agree (X.comp ρ (P.extension r)) (X.comp ρ' (P.extension r))) :
    X.Models ρ (P.information r) ↔ X.Models ρ' (P.information r) := by
  rw [C.models_iff residual ρ, C.models_iff residual ρ', throughCarry.models_iff, throughExtension.models_iff]

/-- **The solvability part of a residual's admission mentions no residual**: the residual's information
is solvable exactly when the firing's information and the step's result knowledge have solutions
that agree on the state's frame. -/
theorem Coherent.solvable_iff (C : Coherent R) {s : State} {g : Fir s} {admitted : P.Admits g} {f : Fir s}
    {r : Fir (P.result g admitted)} (residual : R.Residual g admitted f r) :
    X.Solvable (P.information r) ↔
      ∃ (b : Obj) (σ : Hom (P.target f) b) (τ : Hom (P.frame (P.result g admitted)) b),
        X.Models σ (P.information f) ∧ X.Models τ (P.knowledge (P.result g admitted)) ∧
          X.Agree (X.comp σ (P.extension f)) (X.comp τ (P.along g admitted)) := by
  constructor
  · rintro ⟨b, ρ, solved⟩
    obtain ⟨first, second⟩ := (C.models_iff residual ρ).mp solved
    exact ⟨b, _, _, first, second, (Frames.agree_assoc _ _ ρ).trans
      ((Frames.Agree.comp_left ρ (C.square residual)).trans (Frames.agree_assoc _ _ ρ).symm)⟩
  · rintro ⟨b, σ, τ, first, second, agree⟩
    obtain ⟨c, ι, ρ, throughCarry, throughExtension⟩ := C.amalgamate residual b σ τ agree
    exact ⟨c, ρ, (C.models_iff residual ρ).mpr
      ⟨(throughCarry.models_iff _).mpr (Frames.models_comp first ι),
        (throughExtension.models_iff _).mpr (Frames.models_comp second ι)⟩⟩

variable (P) in
/-- **Conservative settlement up to dead names**: every solution of an admitted firing's information
extends through the settling morphism after a morphism out of its frame. -/
def ConservativeUpToDead : Prop :=
  ∀ {s : State} (f : Fir s) (admitted : P.Admits f) (b : Obj) (σ : Hom (P.target f) b),
    X.Models σ (P.information f) →
      ∃ (c : Obj) (ι : Hom b c) (ρ : Hom (P.frame (P.result f admitted)) c),
        X.Agree (X.comp ι σ) (X.comp ρ (P.settle f admitted))

/-- **Settlement chooses no solution, up to dead names**: the result's knowledge is solvable exactly
when the information is. -/
theorem solvable_result_iff [P.Exact] (conservative : ConservativeUpToDead P) {s : State} (f : Fir s)
    (admitted : P.Admits f) :
    X.Solvable (P.knowledge (P.result f admitted)) ↔ X.Solvable (P.information f) := by
  constructor
  · rintro ⟨b, ρ, solved⟩
    exact ⟨b, _, P.result_refines f (P.prepares admitted) ρ solved⟩
  · rintro ⟨b, σ, solved⟩
    obtain ⟨c, ι, ρ, agree⟩ := conservative f admitted b σ solved
    refine ⟨c, ρ, ?_⟩
    exact Step.Exact.exactness (P := P) f (P.prepares admitted) ρ
      ((agree.models_iff _).mp (Frames.models_comp solved ι))

/-- **Lawful transport up to dead names**: coherent residuals and conservative settlement, both up to
dead names. -/
structure Lawful (R : T.Residuals) where
  coherent : Coherent R
  conservative : ConservativeUpToDead P

end DeadTransport

/-! ## The native step meets the laws -/

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open Mettapedia.Logic.LP (ScopedVar)
open NativeResidual NativeDead NativeIterated NativeUpToDead

variable {S : Signature} {O : Type} [DecidableEq O] {Γ : Ctx S} {sort : S.Srt}
  [DecidableEq S.Srt] [∀ result, DecidableEq (S.Op result)]

namespace NativeUpToDeadLaws

/-- **Residuals of firings that take and read nothing the step makes**: the residuals independence
uses. -/
noncomputable def residualsUnmade :
    (deadTransport (S := S) (O := O) (Γ := Γ) (sort := sort)).Residuals where
  Residual g admitted f r := (∀ o ∈ f.selection.taken ++ f.selection.read, o ∉ g.selection.made) ∧
    r = residualAfter admitted f
  selection_residual residual := by
    rw [residual.2]
    rfl

variable {s : NativeState S O Γ sort}

omit [DecidableEq O] [DecidableEq S.Srt] [∀ result, DecidableEq (S.Op result)] in
/-- Two assignments that agree on observations are equal. -/
theorem eq_of_agree {F G : Frames.Frame S} {α β : Assignment F.arity G.arity}
    (agree : (Frames.contextual S).Agree α β) : α = β := by
  funext name
  have same := agree (observe (generator F.arity name))
  change observe (instantiate α (generator F.arity name)) = observe (instantiate β (generator F.arity name)) at same
  have terms := observe_injective same
  rw [instantiate_generator, instantiate_generator] at terms
  exact terms

section Native

variable (G : ContextualConditionalExecution.Firing s.locals s.state)

/-- The names the carrying moves to. -/
def carryName : ScopedVar s.Local ⊕ s.state.Names → ScopedVar (s.Local ⊕ G.update.Variables) ⊕ G.target.Names
  | .inl name => .inl ⟨name.scope + shift G, .inl name.name⟩
  | .inr name => .inr (.inl (.inr name))

theorem carryName_injective : Function.Injective (carryName G) := by
  rintro (⟨scope, name⟩ | name) (⟨scope', name'⟩ | name') same <;> simp [carryName] at same
  · obtain ⟨rfl, rfl⟩ := same
    rfl
  · rw [same]

/-- **The carrying is an extension**: injective on names. -/
def carryExtension : ContextualGuardMatching.Extension (ContextualActivatedStep.target s.locals s.state.declarations) :=
  ⟨_, laterTarget G, carryName G, carryName_injective G, fun name => by cases name <;> rfl⟩

theorem carry_eq_extension : carry G = (carryExtension G).assignment := by
  funext name
  cases name <;> rfl

/-- **A residual has the firing's shapes.** -/
theorem shapes_residual (f : LiveFiring s) :
    native.Shapes (f.residualAt G).toNative ↔ native.Shapes f.toNative := by
  show (f.selection.taken.Nodup ∧ f.selection.made.Nodup ∧
        (f.rule.map (instantiate (sourceCarry G))).take.length = f.selection.taken.length ∧
        (f.rule.map (instantiate (sourceCarry G))).read.length = f.selection.read.length ∧
        f.selection.made.map (fun o => instantiate (carry G) (f.outputs o)) = (f.residualAt G).toNative.prepared.rule.produce) ↔
      (f.selection.taken.Nodup ∧ f.selection.made.Nodup ∧ f.rule.take.length = f.selection.taken.length ∧
        f.rule.read.length = f.selection.read.length ∧ f.selection.made.map f.outputs = f.toNative.prepared.rule.produce)
  rw [residual_prepared G f]
  have outputs : f.selection.made.map (fun o => instantiate (carry G) (f.outputs o)) =
      (f.selection.made.map f.outputs).map (instantiate (carry G)) := (List.map_map ..).symm
  rw [outputs]
  show _ ↔ (_ ∧ _ ∧ _ ∧ _ ∧ _)
  show (_ ∧ _ ∧ (f.rule.take.map _).length = _ ∧ (f.rule.read.map _).length = _ ∧
    _ = f.toNative.prepared.rule.produce.map _) ↔ _
  rw [List.length_map, List.length_map]
  have injective : Function.Injective (List.map (instantiate (carry G) (Γ := Γ) (sort := sort))) := by
    rw [carry_eq_extension]
    exact List.map_injective_iff.mpr (carryExtension G).instantiate_injective
  exact and_congr Iff.rfl (and_congr Iff.rfl (and_congr Iff.rfl (and_congr Iff.rfl injective.eq_iff)))

/-- **The information law**, up to membership. -/
theorem information_law (f : LiveFiring s)
    (unmade : ∀ o ∈ f.selection.taken ++ f.selection.read, o ∉ G.selection.made) :
    (Frames.contextual S).Equivalent (a := (rawTarget G).infoFrame) (f.residualAt G).toNative.information
      (ContextualResidual.mapProblem (carry G) f.toNative.information ++
        ContextualResidual.mapProblem (laterCaptured G) G.target.equations) := by
  apply Frames.equivalent_of_mem_iff
  intro x
  have knowledge : ∀ y ∈ ContextualResidual.mapProblem (carry G)
      (ContextualResidual.mapProblem (ContextualSelectionViews.capturedTarget s.locals s.state.declarations)
        s.state.equations), y ∈ ContextualResidual.mapProblem (laterCaptured G) G.target.equations := by
    intro y member
    rw [ContextualConditionalNaturality.map_problem_compose, carry_captured,
      ← ContextualConditionalNaturality.map_problem_compose] at member
    refine List.map_subset _ (fun z inChange => ?_) member
    unfold NativeResidual.change at inChange
    rw [← ContextualConditionalNaturality.map_problem_compose] at inChange
    obtain ⟨e, inCaptured, rfl⟩ := List.mem_map.mp inChange
    have inInformation : e ∈ ContextualConditionalExecution.information s.locals s.state.declarations
        s.state.occupied G.selection G.rule s.state.rows s.state.equations := by
      rw [information_eq]
      exact List.mem_append_left _ inCaptured
    exact List.mem_map_of_mem (f := fun equation =>
      (instantiateObservation (ContextualComputedFreshFrame.includeSource G.update) equation.1,
        instantiateObservation (ContextualComputedFreshFrame.includeSource G.update) equation.2)) inInformation
  have split : f.toNative.information =
      ContextualResidual.mapProblem (ContextualSelectionViews.capturedTarget s.locals s.state.declarations)
        s.state.equations ++ ownPart s f.selection f.rule :=
    information_eq s.locals s.state.declarations s.state.occupied f.selection f.rule s.state.rows s.state.equations
  have carried : ContextualResidual.mapProblem (carry G) f.toNative.information =
      ContextualResidual.mapProblem (carry G)
        (ContextualResidual.mapProblem (ContextualSelectionViews.capturedTarget s.locals s.state.declarations)
          s.state.equations) ++ ContextualResidual.mapProblem (carry G) (ownPart s f.selection f.rule) := by
    rw [split, mapProblem_append]
  rw [information_residualAt G f unmade, carried]
  constructor
  · intro member
    rcases List.mem_append.mp member with inKnowledge | inOwn
    · exact List.mem_append_right _ inKnowledge
    · exact List.mem_append_left _ (List.mem_append_right _ inOwn)
  · intro member
    rcases List.mem_append.mp member with inCarried | inKnowledge
    · rcases List.mem_append.mp inCarried with inCaptured | inOwn
      · exact List.mem_append_left _ (knowledge x inCaptured)
      · exact List.mem_append_right _ inOwn
    · exact List.mem_append_left _ inKnowledge

/-- **Amalgamation into the first-order frame**: the carried rule locals read the first solution, the
published frame the second, and the scoped private helpers go to the first-order frame. -/
def amalgamOf {b : Frames.Frame S} (σ : Assignment (ContextualActivatedStep.target s.locals s.state.declarations) b.arity)
    (τ : Assignment G.target.declarations b.arity) : Assignment (laterTarget G) (Frames.firstOrderFrame S).arity
  | .inl ⟨scope, .inl name⟩ => instantiate (Frames.toFirstOrder b) (σ (.inl ⟨scope - shift G, name⟩))
  | .inl ⟨scope, .inr helper⟩ => Frames.toFirstOrder ⟨_, laterTarget G⟩ (.inl ⟨scope, .inr helper⟩)
  | .inr name => instantiate (Frames.toFirstOrder b) (τ name)

theorem amalgamOf_carry {b : Frames.Frame S}
    (σ : Assignment (ContextualActivatedStep.target s.locals s.state.declarations) b.arity)
    (τ : Assignment G.target.declarations b.arity)
    (agree : Assignment.compose σ (ContextualSelectionViews.capturedTarget s.locals s.state.declarations) =
      Assignment.compose τ (change G)) :
    Assignment.compose (amalgamOf G σ τ) (carry G) = Assignment.compose (Frames.toFirstOrder b) σ := by
  funext name
  cases name with
  | inl name =>
      refine (instantiate_generator (amalgamOf G σ τ) (.inl (ScopedVar.at (name.scope + shift G) (.inl name.name)))).trans ?_
      show instantiate (Frames.toFirstOrder b) (σ (.inl ⟨name.scope + shift G - shift G, name.name⟩)) =
        instantiate (Frames.toFirstOrder b) (σ (.inl name))
      rw [Nat.add_sub_cancel]
  | inr name =>
      have atName : τ (.inl (.inr name)) = σ (.inr name) :=
        ((instantiate_generator τ (.inl (.inr name))).symm.trans
          ((congrArg (instantiate τ) (change_apply G name)).symm.trans (congrFun agree name).symm)).trans
          (instantiate_generator σ (.inr name))
      exact (instantiate_generator (amalgamOf G σ τ) (.inr (.inl (.inr name)))).trans
        (congrArg (instantiate (Frames.toFirstOrder b)) atName)

theorem amalgamOf_captured {b : Frames.Frame S}
    (σ : Assignment (ContextualActivatedStep.target s.locals s.state.declarations) b.arity)
    (τ : Assignment G.target.declarations b.arity) :
    Assignment.compose (amalgamOf G σ τ) (laterCaptured G) = Assignment.compose (Frames.toFirstOrder b) τ := by
  funext name
  exact instantiate_generator (amalgamOf G σ τ) (.inr name)

/-- **A solution of an execution's information, lifted through its settlement**: the solver's helpers
go to the first-order frame. -/
def settleLift {b : Frames.Frame S} (σ : Assignment (ContextualActivatedStep.target s.locals s.state.declarations) b.arity) :
    Assignment G.target.declarations (Frames.firstOrderFrame S).arity
  | .inl name => instantiate (Frames.toFirstOrder b) (σ name)
  | .inr helper => Frames.toFirstOrder ⟨_, G.target.declarations⟩ (.inr helper)

theorem settleLift_settle {b : Frames.Frame S}
    (σ : Assignment (ContextualActivatedStep.target s.locals s.state.declarations) b.arity) :
    Assignment.compose (Frames.toFirstOrder b) σ =
      Assignment.compose (settleLift G σ) (ContextualComputedFreshFrame.includeSource G.update) := by
  funext name
  exact ((congrArg (instantiate (settleLift G σ)) (includeSource_apply G name)).trans
    (instantiate_generator (settleLift G σ) (.inl name))).symm

end Native

/-- **The native residuals are coherent up to dead names.** -/
noncomputable def coherent : DeadTransport.Coherent (residualsUnmade (S := S) (O := O) (Γ := Γ) (sort := sort)) where
  carry {_ _ admitted _ _} _ := carryAt (LiveFiring.execution admitted)
  square {_ _ admitted _ _} _ := Frames.Agree.of_eq (carry_captured (LiveFiring.execution admitted))
  amalgamate {_ _ admitted _ _} _ b σ τ agree :=
    ⟨Frames.firstOrderFrame S, Frames.toFirstOrder b, amalgamOf (LiveFiring.execution admitted) σ τ,
      Frames.Agree.of_eq (amalgamOf_carry (LiveFiring.execution admitted) σ τ (eq_of_agree agree)),
      Frames.Agree.of_eq (amalgamOf_captured (LiveFiring.execution admitted) σ τ)⟩
  information {_ _ admitted f _} residual := by
    obtain ⟨unmade, rfl⟩ := residual
    have selection := (LiveFiring.execution_data admitted).2.1
    exact information_law (LiveFiring.execution admitted) f fun o member => by
      rw [selection]
      exact unmade o member
  shapes {_ _ admitted f _} residual := by
    obtain ⟨_, rfl⟩ := residual
    exact shapes_residual (LiveFiring.execution admitted) f

/-- **Native settlement is conservative up to dead names**: the solver's helper names go to the
first-order frame. -/
theorem conservative : DeadTransport.ConservativeUpToDead
    (live (S := S) (O := O) (Γ := Γ) (sort := sort)).toStep :=
  fun _ admitted b σ _ => ⟨Frames.firstOrderFrame S, Frames.toFirstOrder b,
    settleLift (LiveFiring.execution admitted) σ,
    Frames.Agree.of_eq (settleLift_settle (LiveFiring.execution admitted) σ)⟩

/-- **The native transport up to dead names is lawful up to dead names.** -/
noncomputable def lawful : DeadTransport.Lawful (residualsUnmade (S := S) (O := O) (Γ := Γ) (sort := sort)) :=
  ⟨coherent, conservative⟩

/-- **The strict separation law fails**: for every execution and every private local, two solutions of
the residual's frame with the same two restrictions differ on an observation (R83). So the strict
`Transport.Coherent`, and with it the strict `Transport.Lawful`, does not hold for native residuals. -/
theorem strict_separation_fails (G : ContextualConditionalExecution.Firing s.locals s.state) (name : s.Local) :
    ∃ (b : Frames.Frame S) (ρ ρ' : Assignment (laterTarget G) b.arity),
      Assignment.compose ρ (carry G) = Assignment.compose ρ' (carry G) ∧
        Assignment.compose ρ (laterCaptured G) = Assignment.compose ρ' (laterCaptured G) ∧
        ¬ (Frames.contextual S).Agree (a := ⟨_, laterTarget G⟩) (b := b) ρ ρ' :=
  NativeResidualSeparation.residual_not_separated G name

/-- **The laws are not vacuous**: the residual of the first maker of `Step/NativeResidualExample` after
the second is a residual of the law, and it is admitted. -/
theorem makers_residual :
    residualsUnmade.Residual (NativeResidualExample.maker 1 none) (NativeResidualExample.maker_realized 1 none)
        (NativeResidualExample.maker 0 none)
        (residualAfter (NativeResidualExample.maker_realized 1 none) (NativeResidualExample.maker 0 none)) ∧
      (residualAfter (NativeResidualExample.maker_realized 1 none) (NativeResidualExample.maker 0 none)).toNative.Realized :=
  ⟨⟨fun _ member => absurd member List.not_mem_nil, rfl⟩, NativeResidualExample.makers_each_after.1⟩

end NativeUpToDeadLaws

#print axioms DeadTransport.Coherent.models_iff
#print axioms DeadTransport.Coherent.models_congr
#print axioms DeadTransport.Coherent.solvable_iff
#print axioms DeadTransport.solvable_result_iff
#print axioms NativeUpToDeadLaws.eq_of_agree
#print axioms NativeUpToDeadLaws.shapes_residual
#print axioms NativeUpToDeadLaws.information_law
#print axioms NativeUpToDeadLaws.amalgamOf_carry
#print axioms NativeUpToDeadLaws.coherent
#print axioms NativeUpToDeadLaws.conservative
#print axioms NativeUpToDeadLaws.lawful
#print axioms NativeUpToDeadLaws.strict_separation_fails
#print axioms NativeUpToDeadLaws.makers_residual

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface
