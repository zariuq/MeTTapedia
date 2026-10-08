import Mettapedia.TypeTheory.Calculi.NativeDependent.ExternalContextualPresentation
import Mettapedia.TypeTheory.Calculi.NativeDependent.ExternalSyntacticTelescopes
import Mettapedia.TypeTheory.Calculi.NativeDependent.ExternalJudgmentRegularity

/-!
# Equality of chosen presentations under generated context equations

Raw context objects remain distinct. Their recursively chosen comprehension
presentations coincide when the generated context equation identifies their
dependent annotations. The extension case transports the actual type equation
to the common preceding presentation before comparing selected representatives.
The finite native telescopes then agree in the constructed source model.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.NativeDependent.External.Contextual.PresentationEquality

open Presentation

universe u
variable {S : Symbols.{u}} {D : Signature S}

noncomputable def annotation {n : Nat} {context : ContextExpr S n}
    (previous : Data (D := D) context) (type : TypeExpr S n)
    (typed : Holds D (.type context type)) : TypeOver previous.context :=
  QuotientCwf.typeRepresentative (QType.mk
    ⟨type, conclude (.transportType context previous.selected type)
      ⟨contextEquality_symm previous.equivalent, typed, trivial⟩⟩)

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
  | mk firstSelected firstSelectedFormed firstChosen firstEquivalent =>
    cases secondData with
    | mk secondSelected secondSelectedFormed secondChosen secondEquivalent =>
      dsimp only at earlier
      cases earlier
      unfold annotation
      apply congrArg (fun type : QType (contextOf firstSelected firstSelectedFormed) =>
        (QuotientCwf.typeRepresentative type).code)
      apply (QType.mk_eq_iff _ _).mpr
      exact conclude (.transportTypeEquality first firstSelected firstType secondType)
        ⟨contextEquality_symm firstEquivalent, sameType, trivial⟩

theorem selected_extension {n : Nat} {first second : ContextExpr S n}
    {firstType secondType : TypeExpr S n}
    (firstFormed : Formed D (.snoc first firstType))
    (secondFormed : Formed D (.snoc second secondType))
    (earlier : (select first (formed_previous firstFormed)).selected =
      (select second (formed_previous secondFormed)).selected)
    (sameType : Holds D (.typeEq first firstType secondType)) :
    (select (.snoc first firstType) firstFormed).selected =
      (select (.snoc second secondType) secondFormed).selected := by
  change (ContextExpr.snoc (select first (formed_previous firstFormed)).selected
      (annotation (select first (formed_previous firstFormed)) firstType (formed_last firstFormed)).code) =
    ContextExpr.snoc (select second (formed_previous secondFormed)).selected
      (annotation (select second (formed_previous secondFormed)) secondType (formed_last secondFormed)).code
  exact congrArg₂ ContextExpr.snoc earlier (annotation_code _ _ _ _
    (formed_last firstFormed) (formed_last secondFormed) earlier sameType)

def Result (D : Signature S) : Judgment S → Prop
  | .contextEq first second => ∀ (firstFormed : Formed D first) (secondFormed : Formed D second),
      (select first firstFormed).selected = (select second secondFormed).selected
  | _ => True

theorem derivation {judgment : Judgment S} (tree : Derivation D judgment) : Result D judgment := by
  refine JudgmentDerivation.Derivation.rec (S := judgmentSignature D)
    (motive := fun judgment _ => Result D judgment) (fun rule premises regular => ?_) tree
  rcases rule with ⟨code, rfl⟩
  cases code <;> try exact trivial
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

theorem selected_raw {n : Nat} {first second : ContextExpr S n}
    (same : Holds D (.contextEq first second))
    (firstFormed : Formed D first) (secondFormed : Formed D second) :
    (select first firstFormed).selected = (select second secondFormed).selected := by
  rcases same with ⟨tree⟩
  exact derivation tree firstFormed secondFormed

theorem selected_context {n : Nat} {first second : ContextExpr S n}
    (same : Holds D (.contextEq first second))
    (firstFormed : Formed D first) (secondFormed : Formed D second) :
    selectedContext (contextOf first firstFormed) = selectedContext (contextOf second secondFormed) := by
  exact SyntacticTelescopes.raw_context_ext rfl
    (heq_of_eq (selected_raw same firstFormed secondFormed))

theorem selected_telescope {n : Nat} {first second : ContextExpr S n}
    (same : Holds D (.contextEq first second))
    (firstFormed : Formed D first) (secondFormed : Formed D second) :
    HEq (selectedTelescope (contextOf first firstFormed))
      (selectedTelescope (contextOf second secondFormed)) :=
  SyntacticTelescopes.telescope_heq _ _
    (congrArg (quotientProjection D).obj (selected_context same firstFormed secondFormed))

theorem selected_parameter_context {n : Nat} {first second : ContextExpr S n}
    (same : Holds D (.contextEq first second))
    (firstFormed : Formed D first) (secondFormed : Formed D second) :
    (⟨(quotientProjection D).obj (selectedContext (contextOf first firstFormed)),
        selectedTelescope (contextOf first firstFormed)⟩ :
      Mettapedia.TypeTheory.ContextualModelTelescopes.Context (QuotientCwf.withTerminal D) n) =
    ⟨(quotientProjection D).obj (selectedContext (contextOf second secondFormed)),
      selectedTelescope (contextOf second secondFormed)⟩ :=
  Sigma.ext (congrArg (quotientProjection D).obj (selected_context same firstFormed secondFormed))
    (selected_telescope same firstFormed secondFormed)

end Mettapedia.TypeTheory.Calculi.NativeDependent.External.Contextual.PresentationEquality
