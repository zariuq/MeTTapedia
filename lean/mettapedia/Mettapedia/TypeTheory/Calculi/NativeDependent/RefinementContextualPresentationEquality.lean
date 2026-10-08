import Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementSyntacticScopes
import Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementJudgmentRegularity

/-!
# Generated equations determine the chosen mixed presentation

Raw contexts remain objects with their original data and predicate syntax.
Their chosen presentations agree under generated context equations: a data
extension compares its actual type class, and an assumption compares its
actual predicate class. Both comparisons first transport to the shared
preceding presentation. The complete mixed scopes then agree in the earned
source model, including all assumption restrictions.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.Contextual.PresentationEquality

open Presentation
open Mettapedia.TypeTheory.ContextualPredicateModelScopes

universe u
variable {S : Symbols.{u}} {D : Signature S}

noncomputable def annotation {n : Nat} {context : ContextExpr S n}
    (previous : Data (D := D) context) (type : TypeExpr S n)
    (typed : Holds D (.type context type)) : TypeOver previous.context :=
  QuotientCwf.typeRepresentative (QType.mk
    ⟨type, conclude (.transportType context previous.selected type)
      ⟨contextEquality_symm previous.equivalent, typed, trivial⟩⟩)

noncomputable def predicateAnnotation {n : Nat} {context : ContextExpr S n}
    (previous : Data (D := D) context) (predicate : PropExpr S n)
    (formed : Holds D (.predicate context predicate)) : PredicateOver previous.context :=
  AssumptionModel.chosen (QPredicate.mk
    ⟨predicate, conclude (.transportPredicate context previous.selected predicate)
      ⟨contextEquality_symm previous.equivalent, formed, trivial⟩⟩)

theorem annotation_code {n : Nat} {first second : ContextExpr S n}
    (firstData : Data (D := D) first) (secondData : Data (D := D) second)
    (firstType secondType : TypeExpr S n)
    (firstTyped : Holds D (.type first firstType))
    (secondTyped : Holds D (.type second secondType))
    (earlier : firstData.selected = secondData.selected)
    (sameType : Holds D (.typeEq first firstType secondType)) :
    (annotation firstData firstType firstTyped).code =
      (annotation secondData secondType secondTyped).code := by
  cases firstData with
  | mk firstSelected firstSelectedFormed firstChosen firstEquivalent firstScope =>
    cases secondData with
    | mk secondSelected secondSelectedFormed secondChosen secondEquivalent secondScope =>
      dsimp only at earlier
      cases earlier
      unfold annotation
      apply congrArg (fun type : QType (contextOf firstSelected firstSelectedFormed) =>
        (QuotientCwf.typeRepresentative type).code)
      apply (QType.mk_eq_iff _ _).mpr
      exact conclude (.transportTypeEquality first firstSelected firstType secondType)
        ⟨contextEquality_symm firstEquivalent, sameType, trivial⟩

theorem predicateAnnotation_code {n : Nat} {first second : ContextExpr S n}
    (firstData : Data (D := D) first) (secondData : Data (D := D) second)
    (firstPredicate secondPredicate : PropExpr S n)
    (firstFormed : Holds D (.predicate first firstPredicate))
    (secondFormed : Holds D (.predicate second secondPredicate))
    (earlier : firstData.selected = secondData.selected)
    (samePredicate : Holds D (.predicateEq first firstPredicate secondPredicate)) :
    (predicateAnnotation firstData firstPredicate firstFormed).code =
      (predicateAnnotation secondData secondPredicate secondFormed).code := by
  cases firstData with
  | mk firstSelected firstSelectedFormed firstChosen firstEquivalent firstScope =>
    cases secondData with
    | mk secondSelected secondSelectedFormed secondChosen secondEquivalent secondScope =>
      dsimp only at earlier
      cases earlier
      unfold predicateAnnotation
      apply congrArg (fun predicate : QPredicate (contextOf firstSelected firstSelectedFormed) =>
        (AssumptionModel.chosen predicate).code)
      apply (QPredicate.mk_eq_iff _ _).mpr
      have transported := conclude
        (.substitutePredicateEquality firstSelected first TermExpr.var firstPredicate secondPredicate)
        ⟨(contextArrow firstSelected first firstSelectedFormed
          (JudgmentRegularity.predicateContext firstFormed) firstEquivalent).admitted,
          samePredicate, trivial⟩
      change Holds D (.predicateEq firstSelected
        (firstPredicate.substitute TermExpr.var) (secondPredicate.substitute TermExpr.var)) at transported
      rw [PropExpr.substitute_identity, PropExpr.substitute_identity] at transported
      exact transported

theorem selected_extension {n : Nat} {first second : ContextExpr S n}
    {firstType secondType : TypeExpr S n}
    (firstFormed : Formed D (.snoc first firstType))
    (secondFormed : Formed D (.snoc second secondType))
    (earlier : (Presentation.select first (formed_previous firstFormed)).selected =
      (Presentation.select second (formed_previous secondFormed)).selected)
    (sameType : Holds D (.typeEq first firstType secondType)) :
    (Presentation.select (.snoc first firstType) firstFormed).selected =
      (Presentation.select (.snoc second secondType) secondFormed).selected := by
  change ContextExpr.snoc (Presentation.select first (formed_previous firstFormed)).selected
      (annotation (Presentation.select first (formed_previous firstFormed)) firstType (formed_last firstFormed)).code =
    ContextExpr.snoc (Presentation.select second (formed_previous secondFormed)).selected
      (annotation (Presentation.select second (formed_previous secondFormed)) secondType (formed_last secondFormed)).code
  exact congrArg₂ ContextExpr.snoc earlier (annotation_code _ _ _ _
    (formed_last firstFormed) (formed_last secondFormed) earlier sameType)

theorem selected_assumption {n : Nat} {first second : ContextExpr S n}
    {firstPredicate secondPredicate : PropExpr S n}
    (firstFormed : Formed D (.assume first firstPredicate))
    (secondFormed : Formed D (.assume second secondPredicate))
    (earlier : (Presentation.select first (assumed_previous firstFormed)).selected =
      (Presentation.select second (assumed_previous secondFormed)).selected)
    (samePredicate : Holds D (.predicateEq first firstPredicate secondPredicate)) :
    (Presentation.select (.assume first firstPredicate) firstFormed).selected =
      (Presentation.select (.assume second secondPredicate) secondFormed).selected := by
  change ContextExpr.assume (Presentation.select first (assumed_previous firstFormed)).selected
      (predicateAnnotation (Presentation.select first (assumed_previous firstFormed)) firstPredicate
        (assumed_last firstFormed)).code =
    ContextExpr.assume (Presentation.select second (assumed_previous secondFormed)).selected
      (predicateAnnotation (Presentation.select second (assumed_previous secondFormed)) secondPredicate
        (assumed_last secondFormed)).code
  exact congrArg₂ ContextExpr.assume earlier (predicateAnnotation_code _ _ _ _
    (assumed_last firstFormed) (assumed_last secondFormed) earlier samePredicate)

def Result (D : Signature S) : Judgment S → Prop
  | .contextEq first second => ∀ (firstFormed : Formed D first) (secondFormed : Formed D second),
      (Presentation.select first firstFormed).selected = (Presentation.select second secondFormed).selected
  | _ => True

theorem derivation {judgment : Judgment S} (tree : Derivation D judgment) : Result D judgment := by
  refine JudgmentDerivation.Derivation.rec (S := judgmentSignature D)
    (motive := fun judgment _ => Result D judgment) (fun rule premises regular => ?_) tree
  rcases rule with ⟨code, rfl⟩
  cases code <;> dsimp only [RuleCode.conclusion, Result] <;> try exact trivial
  case contextReflexivity context =>
    intro firstFormed secondFormed
    rfl
  case contextSymmetry first second =>
    intro firstFormed secondFormed
    exact (regular ⟨⟨0, by change 0 < 1; decide⟩⟩ secondFormed firstFormed).symm
  case contextTransitivity first middle last =>
    intro firstFormed lastFormed
    have same : Holds D (.contextEq first middle) :=
      ⟨premises ⟨⟨0, by change 0 < 2; decide⟩⟩⟩
    have middleFormed := (JudgmentRegularity.contextEquality same).2
    exact (regular ⟨⟨0, by change 0 < 2; decide⟩⟩ firstFormed middleFormed).trans
      (regular ⟨⟨1, by change 1 < 2; decide⟩⟩ middleFormed lastFormed)
  case contextExtendEquality first second firstType secondType =>
    intro firstFormed secondFormed
    have same : Holds D (.typeEq first firstType secondType) :=
      ⟨premises ⟨⟨1, by change 1 < 3; decide⟩⟩⟩
    exact selected_extension firstFormed secondFormed
      (regular ⟨⟨0, by change 0 < 3; decide⟩⟩
        (formed_previous firstFormed) (formed_previous secondFormed)) same
  case contextAssumeEquality first second firstPredicate secondPredicate =>
    intro firstFormed secondFormed
    have same : Holds D (.predicateEq first firstPredicate secondPredicate) :=
      ⟨premises ⟨⟨1, by change 1 < 3; decide⟩⟩⟩
    exact selected_assumption firstFormed secondFormed
      (regular ⟨⟨0, by change 0 < 3; decide⟩⟩
        (assumed_previous firstFormed) (assumed_previous secondFormed)) same

theorem selected_raw {n : Nat} {first second : ContextExpr S n}
    (same : Holds D (.contextEq first second))
    (firstFormed : Formed D first) (secondFormed : Formed D second) :
    (Presentation.select first firstFormed).selected = (Presentation.select second secondFormed).selected := by
  rcases same with ⟨tree⟩
  exact derivation tree firstFormed secondFormed

theorem selected_context {n : Nat} {first second : ContextExpr S n}
    (same : Holds D (.contextEq first second))
    (firstFormed : Formed D first) (secondFormed : Formed D second) :
    selectedContext (contextOf first firstFormed) = selectedContext (contextOf second secondFormed) :=
  SyntacticScopes.raw_context_ext rfl (heq_of_eq (selected_raw same firstFormed secondFormed))

theorem selected_scope {n : Nat} {first second : ContextExpr S n}
    (same : Holds D (.contextEq first second))
    (firstFormed : Formed D first) (secondFormed : Formed D second) :
    selectedScope (contextOf first firstFormed) = selectedScope (contextOf second secondFormed) :=
  SyntacticScopes.semantic_scope_ext _ _
    (congrArg (quotientProjection D).obj (selected_context same firstFormed secondFormed))

end Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.Contextual.PresentationEquality
