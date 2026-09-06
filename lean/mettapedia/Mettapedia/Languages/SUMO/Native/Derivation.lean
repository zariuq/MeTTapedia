import Mettapedia.Languages.SUMO.Native.SemanticSubstitution

/-!
# Native derivations for SUMO's logical core

This is a classical natural-deduction calculus over the intrinsically scoped
SUMO syntax. Ordinary and row quantifiers have separate rules, and equality
elimination is the full Leibniz rule over a formula with one ordinary hole.

No rule is attached to `Term.kappa`, belief, knowledge, time, or any other
ontology relation here. Such rules require a separately declared doctrine and
a soundness proof for its models.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.SUMO.Native

universe uSymbol uLiteral

/-- Weaken every assumption beneath one fresh ordinary binder. -/
def weakenObjectHypotheses
    {Symbol : Type uSymbol} {Literal : Type uLiteral}
    {ordinary rows : Nat}
    (assumptions : List (Formula Symbol Literal ordinary rows)) :
    List (Formula Symbol Literal (ordinary + 1) rows) :=
  assumptions.map Renaming.weakenObjectFormula

/-- Weaken every assumption beneath one fresh row binder. -/
def weakenRowHypotheses
    {Symbol : Type uSymbol} {Literal : Type uLiteral}
    {ordinary rows : Nat}
    (assumptions : List (Formula Symbol Literal ordinary rows)) :
    List (Formula Symbol Literal ordinary (rows + 1)) :=
  assumptions.map Renaming.weakenRowFormula

set_option autoImplicit true in
/-- Native proof judgments for the classical SUO-KIF logical core.  Constructor
indices are inferred locally from their fully explicit premise and conclusion
types; `autoImplicit` remains disabled everywhere else in the module. -/
inductive Derivation (Symbol : Type uSymbol) (Literal : Type uLiteral) :
    {ordinary rows : Nat} ->
    List (Formula Symbol Literal ordinary rows) ->
    Formula Symbol Literal ordinary rows -> Prop where
  | hypothesis {assumptions : List (Formula Symbol Literal ordinary rows)} :
      body ∈ assumptions -> Derivation Symbol Literal assumptions body
  | topIntroduction {assumptions : List (Formula Symbol Literal ordinary rows)} :
      Derivation Symbol Literal assumptions .top
  | bottomElimination
      {assumptions : List (Formula Symbol Literal ordinary rows)} :
      Derivation Symbol Literal assumptions .bottom ->
      Derivation Symbol Literal assumptions body
  | andIntroduction
      {assumptions : List (Formula Symbol Literal ordinary rows)} :
      Derivation Symbol Literal assumptions left ->
      Derivation Symbol Literal assumptions right ->
      Derivation Symbol Literal assumptions (.and left right)
  | andEliminationLeft
      {assumptions : List (Formula Symbol Literal ordinary rows)} :
      Derivation Symbol Literal assumptions (.and left right) ->
      Derivation Symbol Literal assumptions left
  | andEliminationRight
      {assumptions : List (Formula Symbol Literal ordinary rows)} :
      Derivation Symbol Literal assumptions (.and left right) ->
      Derivation Symbol Literal assumptions right
  | orIntroductionLeft
      {assumptions : List (Formula Symbol Literal ordinary rows)} :
      Derivation Symbol Literal assumptions left ->
      Derivation Symbol Literal assumptions (.or left right)
  | orIntroductionRight
      {assumptions : List (Formula Symbol Literal ordinary rows)} :
      Derivation Symbol Literal assumptions right ->
      Derivation Symbol Literal assumptions (.or left right)
  | orElimination
      {assumptions : List (Formula Symbol Literal ordinary rows)} :
      Derivation Symbol Literal assumptions (.or left right) ->
      Derivation Symbol Literal (left :: assumptions) result ->
      Derivation Symbol Literal (right :: assumptions) result ->
      Derivation Symbol Literal assumptions result
  | implicationIntroduction
      {assumptions : List (Formula Symbol Literal ordinary rows)} :
      Derivation Symbol Literal (antecedent :: assumptions) consequent ->
      Derivation Symbol Literal assumptions (.implies antecedent consequent)
  | implicationElimination
      {assumptions : List (Formula Symbol Literal ordinary rows)} :
      Derivation Symbol Literal assumptions (.implies antecedent consequent) ->
      Derivation Symbol Literal assumptions antecedent ->
      Derivation Symbol Literal assumptions consequent
  | negationIntroduction
      {assumptions : List (Formula Symbol Literal ordinary rows)} :
      Derivation Symbol Literal (body :: assumptions) .bottom ->
      Derivation Symbol Literal assumptions (.not body)
  | negationElimination
      {assumptions : List (Formula Symbol Literal ordinary rows)} :
      Derivation Symbol Literal assumptions (.not body) ->
      Derivation Symbol Literal assumptions body ->
      Derivation Symbol Literal assumptions .bottom
  | iffIntroduction
      {assumptions : List (Formula Symbol Literal ordinary rows)} :
      Derivation Symbol Literal assumptions (.implies left right) ->
      Derivation Symbol Literal assumptions (.implies right left) ->
      Derivation Symbol Literal assumptions (.iff left right)
  | iffEliminationLeft
      {assumptions : List (Formula Symbol Literal ordinary rows)} :
      Derivation Symbol Literal assumptions (.iff left right) ->
      Derivation Symbol Literal assumptions (.implies left right)
  | iffEliminationRight
      {assumptions : List (Formula Symbol Literal ordinary rows)} :
      Derivation Symbol Literal assumptions (.iff left right) ->
      Derivation Symbol Literal assumptions (.implies right left)
  | allInSpineFromAllObject
      {assumptions : List (Formula Symbol Literal ordinary rows)}
      (arguments : Spine Symbol Literal ordinary rows) :
      Derivation Symbol Literal assumptions (.allObject body) ->
      Derivation Symbol Literal assumptions (.allInSpine arguments body)
  | allInSpineNilIntroduction
      {assumptions : List (Formula Symbol Literal ordinary rows)}
      (body : Formula Symbol Literal (ordinary + 1) rows) :
      Derivation Symbol Literal assumptions (.allInSpine .nil body)
  | allInSpineTermIntroduction
      {assumptions : List (Formula Symbol Literal ordinary rows)}
      (value : Term Symbol Literal ordinary rows)
      (rest : Spine Symbol Literal ordinary rows) :
      Derivation Symbol Literal assumptions
        (Substitution.instantiateObjectFormula value body) ->
      Derivation Symbol Literal assumptions (.allInSpine rest body) ->
      Derivation Symbol Literal assumptions
        (.allInSpine (.term value rest) body)
  | allInSpineHeadElimination
      {assumptions : List (Formula Symbol Literal ordinary rows)} :
      Derivation Symbol Literal assumptions
        (.allInSpine (.term value rest) body) ->
      Derivation Symbol Literal assumptions
        (Substitution.instantiateObjectFormula value body)
  | allInSpineTermTailElimination
      {assumptions : List (Formula Symbol Literal ordinary rows)} :
      Derivation Symbol Literal assumptions
        (.allInSpine (.term value rest) body) ->
      Derivation Symbol Literal assumptions (.allInSpine rest body)
  | allInSpineRowTailElimination
      {assumptions : List (Formula Symbol Literal ordinary rows)} :
      Derivation Symbol Literal assumptions
        (.allInSpine (.row rowIndex rest) body) ->
      Derivation Symbol Literal assumptions (.allInSpine rest body)
  | allObjectIntroduction
      {assumptions : List (Formula Symbol Literal ordinary rows)} :
      Derivation Symbol Literal (weakenObjectHypotheses assumptions) body ->
      Derivation Symbol Literal assumptions (.allObject body)
  | allObjectElimination
      {assumptions : List (Formula Symbol Literal ordinary rows)}
      (value : Term Symbol Literal ordinary rows) :
      Derivation Symbol Literal assumptions (.allObject body) ->
      Derivation Symbol Literal assumptions
        (Substitution.instantiateObjectFormula value body)
  | someObjectIntroduction
      {assumptions : List (Formula Symbol Literal ordinary rows)}
      (value : Term Symbol Literal ordinary rows) :
      Derivation Symbol Literal assumptions
        (Substitution.instantiateObjectFormula value body) ->
      Derivation Symbol Literal assumptions (.someObject body)
  | someObjectElimination
      {assumptions : List (Formula Symbol Literal ordinary rows)} :
      Derivation Symbol Literal assumptions (.someObject body) ->
      Derivation Symbol Literal
        (body :: weakenObjectHypotheses assumptions)
        (Renaming.weakenObjectFormula result) ->
      Derivation Symbol Literal assumptions result
  | allRowIntroduction
      {assumptions : List (Formula Symbol Literal ordinary rows)} :
      Derivation Symbol Literal (weakenRowHypotheses assumptions) body ->
      Derivation Symbol Literal assumptions (.allRow body)
  | allRowElimination
      {assumptions : List (Formula Symbol Literal ordinary rows)}
      (arguments : Spine Symbol Literal ordinary rows) :
      Derivation Symbol Literal assumptions (.allRow body) ->
      Derivation Symbol Literal assumptions
        (Substitution.instantiateRowFormula arguments body)
  | someRowIntroduction
      {assumptions : List (Formula Symbol Literal ordinary rows)}
      (arguments : Spine Symbol Literal ordinary rows) :
      Derivation Symbol Literal assumptions
        (Substitution.instantiateRowFormula arguments body) ->
      Derivation Symbol Literal assumptions (.someRow body)
  | someRowElimination
      {assumptions : List (Formula Symbol Literal ordinary rows)} :
      Derivation Symbol Literal assumptions (.someRow body) ->
      Derivation Symbol Literal
        (body :: weakenRowHypotheses assumptions)
        (Renaming.weakenRowFormula result) ->
      Derivation Symbol Literal assumptions result
  | equalityReflexivity
      {assumptions : List (Formula Symbol Literal ordinary rows)}
      (value : Term Symbol Literal ordinary rows) :
      Derivation Symbol Literal assumptions (.equal value value)
  | equalitySubstitution
      {assumptions : List (Formula Symbol Literal ordinary rows)}
      (context : Formula Symbol Literal (ordinary + 1) rows) :
      Derivation Symbol Literal assumptions (.equal left right) ->
      Derivation Symbol Literal assumptions
        (Substitution.instantiateObjectFormula left context) ->
      Derivation Symbol Literal assumptions
        (Substitution.instantiateObjectFormula right context)
  | classicalContradiction
      {assumptions : List (Formula Symbol Literal ordinary rows)} :
      Derivation Symbol Literal ((.not body) :: assumptions) .bottom ->
      Derivation Symbol Literal assumptions body

namespace Derivation

variable {Symbol : Type uSymbol} {Literal : Type uLiteral}

/-- A closed theorem is a derivation from no assumptions. -/
abbrev Theorem (body : Sentence Symbol Literal) : Prop :=
  Derivation Symbol Literal [] body

/-- Native implication reflexivity, valid for formula arguments and
self-application just as for ordinary atoms. -/
theorem implication_reflexivity
    {ordinary rows : Nat}
    (body : Formula Symbol Literal ordinary rows) :
    Derivation Symbol Literal [] (.implies body body) :=
  .implicationIntroduction (.hypothesis (by simp))

/-- The exact row universal over truth. -/
def everyRowTop :
    Derivation String Unit ([] : List (Formula String Unit 0 0))
      (.allRow (.top : Formula String Unit 0 1)) :=
  .allRowIntroduction .topIntroduction

private def eightArguments : Spine String Unit 0 0 :=
  Spine.ofTerms
    [(.constant "a"), (.constant "b"), (.constant "c"), (.constant "d"),
      (.constant "e"), (.constant "f"), (.constant "g"), (.constant "h")]

/-- Row elimination uses an exact eight-argument spine without an arity
expansion table. -/
def eightArgumentTop :
    Derivation String Unit []
      (Substitution.instantiateRowFormula eightArguments (.top : Formula String Unit 0 1)) :=
  .allRowElimination eightArguments everyRowTop

example :
    Substitution.instantiateRowFormula eightArguments
      (.top : Formula String Unit 0 1) = .top := rfl

end Derivation

end Mettapedia.Languages.SUMO.Native
