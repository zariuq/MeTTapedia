import Mettapedia.Logic.HOL.CurriedPredicateProofs
import Mettapedia.Logic.HOL.PredicateFixedPoint

/-!
# Retained existential queries over original field arguments

Existential abstraction commutes with typed substitution. Its beta and
introduction programs retain the supplied witness and original field order.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Logic.HOL.CurriedPredicates

open FiniteConstructorEncoding
universe u v
variable {Base : Type u} {Const : Ty Base → Type v} {Γ Ξ : Ctx Base} {bound : Ty Base}

def existsBody (fields : List (Ty Base)) (predicate : Term Const Γ (bound ⇒ handlerType fields)) :
    ArgumentBody Const Γ fields := fun images arguments =>
  .ex (applyArguments fields (.app (weaken (HOL.subst images predicate)) (.var .vz))
    (weakenArguments bound fields arguments))

theorem existsValue_natural (fields : List (Ty Base))
    (predicate : Term Const Γ (bound ⇒ handlerType fields)) :
    NaturalBody (@existsBody (Base := Base) (Const := Const) (Γ := Γ) (bound := bound) fields predicate) := by
  intro Δ Ω earlier later arguments
  simp only [existsBody, HOL.subst, applyArguments_subst, subst_weaken, HOL.subst_comp,
    substituteArguments_weaken, Subst.lift]
  rfl

theorem existsValue_subst (images : Subst Const Γ Ξ) (fields : List (Ty Base))
    (predicate : Term Const Γ (bound ⇒ handlerType fields)) :
    HOL.subst images (existsValue fields predicate) = existsValue fields (HOL.subst images predicate) := by
  unfold existsValue
  change HOL.subst images (abstractArguments fields (@existsBody (Base := Base) (Const := Const) (Γ := Γ) (bound := bound) fields predicate)) =
    abstractArguments fields (@existsBody (Base := Base) (Const := Const) (Γ := Ξ) (bound := bound) fields (HOL.subst images predicate))
  rw [abstractArguments_subst images fields _ (existsValue_natural fields predicate)]
  apply congrArg (abstractArguments fields)
  funext laterContext later arguments
  simp only [existsBody, HOL.subst_comp]
  rfl

def existsValue_beta {assumptions : List (Formula Const Γ)} (fields : List (Ty Base))
    (predicate : Term Const Γ (bound ⇒ handlerType fields)) (arguments : Arguments Const Γ fields) :
    ProofSyntax Const assumptions (.eq (applyArguments fields (existsValue fields predicate) arguments)
      (.ex (applyArguments fields (.app (weaken predicate) (.var .vz))
        (weakenArguments bound fields arguments)))) := by
  apply ProofSyntax.castIndices rfl ?_
    (abstractArguments_beta fields (@existsBody (Base := Base) (Const := Const) (Γ := Γ) (bound := bound) fields predicate) (existsValue_natural fields predicate) arguments)
  have identityTerm {type : Ty Base} (term : Term Const Γ type) :
      HOL.subst (fun index => .var index) term = term :=
    ProofSyntax.term_subst_of_identity (fun _ => rfl) term
  simp only [existsBody, identityTerm]
  rfl

theorem existsValue_beta_free {assumptions : List (Formula Const Γ)} (fields : List (Ty Base))
    (predicate : Term Const Γ (bound ⇒ handlerType fields)) (arguments : Arguments Const Γ fields) :
    (existsValue_beta (assumptions := assumptions) fields predicate arguments).FunctionExtensionalityFree := by
  unfold existsValue_beta
  apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
  exact abstractArguments_beta_free _ _ _ _

private theorem arguments_cancel (fields : List (Ty Base)) (arguments : Arguments Const Γ fields)
    (witness : Term Const Γ bound) :
    substituteArguments (Subst.single witness) fields (weakenArguments bound fields arguments) = arguments := by
  induction fields with
  | nil => cases arguments; rfl
  | cons type rest previous =>
      exact congrArg₂ Prod.mk (PredicateFixedPoint.subst_single_weaken witness arguments.1) (previous arguments.2)

def existsValue_intro {assumptions : List (Formula Const Γ)} (fields : List (Ty Base))
    (predicate : Term Const Γ (bound ⇒ handlerType fields)) (arguments : Arguments Const Γ fields)
    (witness : Term Const Γ bound)
    (present : ProofSyntax Const assumptions (applyArguments fields (.app predicate witness) arguments)) :
    ProofSyntax Const assumptions (applyArguments fields (existsValue fields predicate) arguments) := by
  apply ProofSyntax.impE (ProofSyntax.eqPropER (existsValue_beta fields predicate arguments))
  apply ProofSyntax.exI witness
  apply ProofSyntax.castIndices rfl ?_ present
  simp only [instantiate, applyArguments_subst, HOL.subst, Subst.single,
    PredicateFixedPoint.subst_single_weaken]
  rw [arguments_cancel fields arguments witness]

theorem existsValue_intro_free {assumptions : List (Formula Const Γ)} (fields : List (Ty Base))
    (predicate : Term Const Γ (bound ⇒ handlerType fields)) (arguments : Arguments Const Γ fields)
    (witness : Term Const Γ bound)
    (present : ProofSyntax Const assumptions (applyArguments fields (.app predicate witness) arguments))
    (free : present.FunctionExtensionalityFree) :
    (existsValue_intro fields predicate arguments witness present).FunctionExtensionalityFree := by
  unfold existsValue_intro
  refine ⟨existsValue_beta_free _ _ _, ?_⟩
  apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
  exact free

#print axioms existsValue_subst
#print axioms existsValue_intro_free

end Mettapedia.Logic.HOL.CurriedPredicates
