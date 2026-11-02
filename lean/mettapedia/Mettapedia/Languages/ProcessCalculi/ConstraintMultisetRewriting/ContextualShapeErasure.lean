import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualPatternProblems
import Mettapedia.OSLF.Syntax.BindingArgumentSlotPositions
import Mettapedia.OSLF.Syntax.SignatureMorphismMetas
import Mettapedia.Logic.LP.TotalUnification

/-!
# First-order shapes of contextual pattern equations

The interpretation uses the existing first-order LP terms. A contextual
hole is a first-order variable, every object variable is the same nullary
leaf, and a rigid constructor retains its ordered field arity. Sort and
scope information is deliberately forgotten. Renaming therefore leaves
the interpretation unchanged.

On structural pattern inputs, interpretation commutes with contextual
instantiation, even when the supplied images are arbitrary terms. Every
higher-order model consequently supplies a first-order shape model. The
pattern premise is essential for using shape failure as a refutation.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualShapeErasure

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualResidual
open ContextualPatternFragment

namespace FO
abbrev Term := Mettapedia.Logic.LP.Term
abbrev Subst := Mettapedia.Logic.LP.Subst
end FO

def shapeSignature (S : Signature) (Names : Type) : Mettapedia.Logic.LP.LPSignature where
  constants := Unit
  vars := Names
  relationSymbols := Empty
  relationArity := fun impossible => nomatch impossible
  functionSymbols := (sort : S.Srt) × S.Op sort
  functionArity := fun operator => (S.arity operator.2).length

abbrev ShapeTerm (S : Signature) (Names : Type) := FO.Term (shapeSignature S Names)
abbrev ShapeAssignment (S : Signature) (Names Next : Type) := Names → ShapeTerm S Next

variable {S : Signature} {V W Next : Type} {source : V → MetaArity S} {target : W → MetaArity S}

mutual
def evaluate (images : ShapeAssignment S V Next) :
    {Γ : Ctx S} → {sort : S.Srt} → Term (signature S source) Γ sort → ShapeTerm S Next
  | _, _, .var _ => .const ()
  | _, sort, .op (.inl operator) fields => .app ⟨sort, operator⟩ (evaluateArgs images fields)
  | _, _, .op (.inr (.mk identity)) _ => images identity

def evaluateArgs (images : ShapeAssignment S V Next) :
    {arities : List (MetaArity S)} → {Γ : Ctx S} → Args (signature S source) arities Γ →
      Fin arities.length → ShapeTerm S Next
  | _, _, .nil, position => Fin.elim0 position
  | _, _, .cons head tail, position => Fin.cases (evaluate images head) (evaluateArgs images tail) position
end

def erase {Γ : Ctx S} {sort : S.Srt} (term : Term (signature S source) Γ sort) : ShapeTerm S V :=
  evaluate (fun identity => .var identity) term

def equations (problem : Problem source) : List (ShapeTerm S V × ShapeTerm S V) :=
  problem.map fun equation => (erase equation.1.2.2, erase equation.2.2.2)

def ShapeModels (images : ShapeAssignment S V Next) (problem : Problem source) : Prop :=
  ∀ equation ∈ problem, evaluate images equation.1.2.2 = evaluate images equation.2.2.2

def evaluateObservation (images : ShapeAssignment S V Next) (observation : Observation S source) : ShapeTerm S Next :=
  evaluate images observation.2.2

@[simp] theorem evaluate_generator (images : ShapeAssignment S V Next) (identity : V) :
    evaluate (source := source) images (generator source identity) = images identity := rfl

theorem evaluate_cast_body (images : ShapeAssignment S V Next) {first second : MetaArity S} (same : first = second)
    (body : Term (signature S source) first.1 first.2) :
    evaluate images (castMetaBody (V := signature S source) same body) = evaluate images body := by
  cases same
  rfl

mutual
theorem evaluate_rename (images : ShapeAssignment S V Next) :
    ∀ {Γ Δ : Ctx S} {sort : S.Srt} (rho : Ren S Γ Δ) (term : Term (signature S source) Γ sort),
      evaluate images (rename (S := signature S source) rho term) = evaluate images term
  | _, _, _, _, .var _ => rfl
  | _, _, sort, rho, .op (.inl operator) fields => by
      change Mettapedia.Logic.LP.Term.app (σ := shapeSignature S Next) ⟨sort, operator⟩
        (evaluateArgs images (renameArgs (S := signature S source) rho fields)) = _
      exact congrArg (Mettapedia.Logic.LP.Term.app (σ := shapeSignature S Next) ⟨sort, operator⟩)
        (funext fun position => evaluateArgs_rename images rho fields position)
  | _, _, _, _, .op (.inr (.mk _)) _ => rfl

theorem evaluateArgs_rename (images : ShapeAssignment S V Next) :
    ∀ {arities : List (MetaArity S)} {Γ Δ : Ctx S} (rho : Ren S Γ Δ)
      (fields : Args (signature S source) arities Γ) (position : Fin arities.length),
      evaluateArgs images (renameArgs (S := signature S source) rho fields) position = evaluateArgs images fields position
  | _, _, _, _, .nil, position => Fin.elim0 position
  | _, _, _, rho, .cons (bs := binders) head tail, position => by
      refine Fin.cases ?_ (fun index => ?_) position
      · exact evaluate_rename images (liftRen rho binders) head
      · exact evaluateArgs_rename images rho tail index
end

theorem evaluateArgs_at_slot (images : ShapeAssignment S V Next) :
    ∀ {arities : List (MetaArity S)} {Γ : Ctx S} (fields : Args (signature S source) arities Γ)
      (slot : ArgumentSlots.Slot arities),
      evaluateArgs images fields (ArgumentSlots.toIndex slot) =
        evaluate images (ArgumentSlots.get fields slot.1 slot.2)
  | _, _, .nil, ⟨_, impossible⟩ => nomatch impossible
  | _, _, .cons _ _, ⟨_, .zero⟩ => rfl
  | _, _, .cons _ tail, ⟨field, .succ position⟩ => evaluateArgs_at_slot images tail ⟨field, position⟩

mutual
theorem evaluate_apply (images : FO.Subst (shapeSignature S V)) :
    ∀ {Γ : Ctx S} {sort : S.Srt} (term : Term (signature S source) Γ sort),
      images.applyTerm (erase term) = evaluate images term
  | _, _, .var _ => rfl
  | _, _, .op (.inr (.mk _)) _ => rfl
  | _, sort, .op (.inl operator) fields => by
      change Mettapedia.Logic.LP.Term.app (σ := shapeSignature S V) ⟨sort, operator⟩
        (fun position => images.applyTerm (evaluateArgs (fun identity => Mettapedia.Logic.LP.Term.var identity) fields position)) = _
      exact congrArg (Mettapedia.Logic.LP.Term.app (σ := shapeSignature S V) ⟨sort, operator⟩)
        (funext fun position => evaluateArgs_apply images fields position)

theorem evaluateArgs_apply (images : FO.Subst (shapeSignature S V)) :
    ∀ {arities : List (MetaArity S)} {Γ : Ctx S} (fields : Args (signature S source) arities Γ)
      (position : Fin arities.length),
      images.applyTerm (evaluateArgs (fun identity => Mettapedia.Logic.LP.Term.var identity) fields position) = evaluateArgs images fields position
  | _, _, .nil, position => Fin.elim0 position
  | _, _, .cons head tail, position => by
      refine Fin.cases ?_ (fun index => ?_) position
      · exact evaluate_apply images head
      · exact evaluateArgs_apply images tail index
end

theorem unifies_equations_iff (images : FO.Subst (shapeSignature S V)) (problem : Problem source) :
    Mettapedia.Logic.LP.Unifies images (equations problem) ↔ ShapeModels images problem := by
  constructor
  · intro unifies equation member
    have same := unifies _ (List.mem_map.mpr ⟨equation, member, rfl⟩)
    simpa only [evaluate_apply] using same
  · intro models pair member
    obtain ⟨equation, selected, rfl⟩ := List.mem_map.mp member
    simpa only [evaluate_apply] using models equation selected

theorem evaluate_instantiate (candidate : Assignment source target) (images : ShapeAssignment S W Next)
    {Γ : Ctx S} {sort : S.Srt} (term : Term (signature S source) Γ sort) (patterned : Pattern S source term) :
    evaluate images (instantiate candidate term) = evaluate (fun identity => evaluate images (candidate identity)) term := by
  refine Pattern.rec
    (motive_1 := fun value _ => evaluate images (instantiate candidate value) =
      evaluate (fun identity => evaluate images (candidate identity)) value)
    (motive_2 := fun fields _ => evaluateArgs images (instantiateArgs candidate fields) =
      evaluateArgs (fun identity => evaluate images (candidate identity)) fields)
    ?_ ?_ ?_ ?_ ?_ patterned
  · intro context result position
    rfl
  · intro context result operator fields _ checked
    exact congrArg (Mettapedia.Logic.LP.Term.app (σ := shapeSignature S Next) ⟨result, operator⟩) checked
  · intro context identity arguments rho spine _
    rw [instantiate_spine candidate identity arguments rho spine]
    exact evaluate_rename images rho (candidate identity)
  · intro context
    funext position
    exact Fin.elim0 position
  · intro arities context binders result head tail _ _ checkedHead checkedTail
    funext position
    refine Fin.cases ?_ (fun index => ?_) position
    · exact checkedHead
    · exact congrFun checkedTail index

theorem evaluate_instantiate_observation (candidate : Assignment source target) (images : ShapeAssignment S W Next)
    (observation : Observation S source) (patterned : Pattern S source observation.2.2) :
    evaluateObservation images (instantiateObservation candidate observation) =
      evaluateObservation (fun identity => evaluate images (candidate identity)) observation := by
  rcases observation with ⟨Γ, sort, term⟩
  exact evaluate_instantiate candidate images term patterned

theorem shape_model_of_model (candidate : Assignment source target) (images : ShapeAssignment S W Next)
    (problem : Problem source) (patterned : ProblemPattern problem) (solved : ContextualResidual.Models candidate problem) :
    ShapeModels (fun identity => evaluate images (candidate identity)) problem := by
  intro equation member
  have same := congrArg (evaluateObservation images) (solved equation member)
  rw [evaluate_instantiate_observation candidate images equation.1 (patterned equation member).1,
    evaluate_instantiate_observation candidate images equation.2 (patterned equation member).2] at same
  exact same

theorem necessary_model (candidate : Assignment source target) (problem : Problem source)
    (patterned : ProblemPattern problem) (solved : ContextualResidual.Models candidate problem) :
    ∃ images : FO.Subst (shapeSignature S V), Mettapedia.Logic.LP.Unifies images (equations problem) := by
  let ground : ShapeAssignment S W V := fun _ => .const ()
  let images : FO.Subst (shapeSignature S V) := fun identity => evaluate ground (candidate identity)
  exact ⟨images, (unifies_equations_iff images problem).mpr
    (shape_model_of_model candidate ground problem patterned solved)⟩

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualShapeErasure
