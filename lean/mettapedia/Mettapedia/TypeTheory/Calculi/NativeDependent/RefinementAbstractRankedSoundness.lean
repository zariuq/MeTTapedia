import Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementAbstractSoundness
import Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementHeaderFormation

/-!
# Generated soundness below a declaration rank

A supplied proof tree uses only symbols below its bound. Only those local
primitive header and result meanings need to be realized. All dependent,
logical and guarded-assumption rules construct their interpretations from
actual local premises, including the full pair-context sum motive. This is
used to realize independently formed declarations successively; it assumes
neither a complete source interpreter nor a global source roundtrip.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.Abstract

open Mettapedia.TypeTheory.ContextualPredicateModel
open Mettapedia.GSLT.Core.ContextualLadder
open Mettapedia.TypeTheory.ContextualTypeOperations
open Mettapedia.TypeTheory.ContextualPiEta

universe a c s t m p
variable {S : Symbols.{a}} {C : CwfWithTerminal.{c, s, t, m}}
  {localModel : LocalModel.{c, s, t, m, p} C} {D : Signature S}

structure BoundedRealization (model : ModelData S C localModel) (D : Signature S)
    (bound : Nat) : Prop where
  typeHeader : ∀ symbol, D.typeRank symbol < bound →
    model.evaluateContext (D.typeParameters symbol) = some (model.typeParameters symbol)
  termHeader : ∀ symbol, D.termRank symbol < bound →
    model.evaluateContext (D.termParameters symbol) = some (model.termParameters symbol)
  predicateHeader : ∀ symbol, D.predicateRank symbol < bound →
    model.evaluateContext (D.predicateParameters symbol) = some (model.predicateParameters symbol)
  termResult : ∀ symbol, D.termRank symbol < bound →
    model.evaluateType (model.termParameters symbol) (D.termResult symbol) = some (model.termType symbol)

namespace ModelData

variable (model : ModelData S C localModel) {n : Nat}

theorem family_sound_before (symbol : S.TypeSymbol)
    (headerRead : model.evaluateContext (D.typeParameters symbol) = some (model.typeParameters symbol))
    (context : ContextExpr S n)
    (arguments : Substitution S (S.typeArity symbol) n)
    (contextInterpreted : Interprets model (.context context))
    (argumentsInterpreted : Interprets model (.substitution context (D.typeParameters symbol) arguments)) :
    Interprets model (.type context (.family symbol arguments)) := by
  exact model.family_sound_of_header symbol headerRead context arguments contextInterpreted argumentsInterpreted

theorem primitive_sound_before (symbol : S.TermSymbol)
    (header : model.evaluateContext (D.termParameters symbol) = some (model.termParameters symbol))
    (result : model.evaluateType (model.termParameters symbol) (D.termResult symbol) = some (model.termType symbol))
    (stable : StrictPiSubstitution localModel.products) (context : ContextExpr S n)
    (arguments : Substitution S (S.termArity symbol) n)
    (argumentsInterpreted : Interprets model
      (.substitution context (D.termParameters symbol) arguments)) :
    Interprets model (.term context (.primitive symbol arguments)
      ((D.termResult symbol).substitute arguments)) := by
  exact model.primitive_sound_of_header symbol header result stable context arguments argumentsInterpreted

theorem familyCongruence_sound_before (context : ContextExpr S n) (symbol : S.TypeSymbol)
    (header : model.evaluateContext (D.typeParameters symbol) = some (model.typeParameters symbol))
    (first second : Substitution S (S.typeArity symbol) n)
    (argumentsInterpreted : Interprets model (.substitutionEq context (D.typeParameters symbol) first second)) :
    Interprets model (.typeEq context (.family symbol first) (.family symbol second)) := by
  exact model.familyCongruence_sound_of_header context symbol header first second argumentsInterpreted

theorem primitiveCongruence_sound_before (stable : StrictPiSubstitution localModel.products)
    (context : ContextExpr S n) (symbol : S.TermSymbol)
    (header : model.evaluateContext (D.termParameters symbol) = some (model.termParameters symbol))
    (result : model.evaluateType (model.termParameters symbol) (D.termResult symbol) = some (model.termType symbol))
    (first second : Substitution S (S.termArity symbol) n)
    (argumentsInterpreted : Interprets model (.substitutionEq context (D.termParameters symbol) first second)) :
    Interprets model (.termEq context (.primitive symbol first) (.primitive symbol second)
      ((D.termResult symbol).substitute first)) := by
  exact model.primitiveCongruence_sound_of_header stable context symbol header result first second argumentsInterpreted

theorem predicatePrimitive_sound_before (symbol : S.PredicateSymbol)
    (header : model.evaluateContext (D.predicateParameters symbol) = some (model.predicateParameters symbol))
    (context : ContextExpr S n)
    (arguments : Substitution S (S.predicateArity symbol) n)
    (contextInterpreted : Interprets model (.context context))
    (argumentsInterpreted : Interprets model (.substitution context (D.predicateParameters symbol) arguments)) :
    Interprets model (.predicate context (.atom symbol arguments)) := by
  exact model.predicatePrimitive_sound_of_header symbol header context arguments contextInterpreted argumentsInterpreted

theorem predicatePrimitiveCongruence_sound_before (context : ContextExpr S n) (symbol : S.PredicateSymbol)
    (header : model.evaluateContext (D.predicateParameters symbol) = some (model.predicateParameters symbol))
    (first second : Substitution S (S.predicateArity symbol) n)
    (argumentsInterpreted : Interprets model
      (.substitutionEq context (D.predicateParameters symbol) first second)) :
    Interprets model (.predicateEq context (.atom symbol first) (.atom symbol second)) := by
  exact model.predicatePrimitiveCongruence_sound_of_header context symbol header first second argumentsInterpreted

private def primitiveDeclarationRank (D : Signature S) : PrimitiveDeclaration S → Nat
  | .family symbol => D.typeRank symbol
  | .term symbol => D.termRank symbol
  | .predicate symbol => D.predicateRank symbol

private theorem declaredHead_before {rule : RuleCode D} {bound : Nat}
    (ordered : rule.conclusion.before D bound) {declaration : PrimitiveDeclaration S}
    (head : RuleDeclaration rule declaration) :
    primitiveDeclarationRank D declaration < bound := by
  cases head <;> first | exact ordered.2.1 | exact ordered.2.1.1

/-- Assumption binders cannot request a primitive declaration of their own. -/
example {n : Nat} (context : ContextExpr S n) (predicate : PropExpr S n)
    {declaration : PrimitiveDeclaration S} :
    ¬ RuleDeclaration (RuleCode.contextAssume (D := D) context predicate) declaration :=
  fun witness => nomatch witness

/-- A family's rule cannot be dispatched at the family's own declaration rank. -/
example {n : Nat} (context : ContextExpr S n) (symbol : S.TypeSymbol)
    (arguments : Substitution S (S.typeArity symbol) n) :
    ¬ (RuleCode.typeFamily (D := D) context symbol arguments).conclusion.before D
        (D.typeRank symbol) :=
  fun ordered => Nat.lt_irrefl _ (declaredHead_before ordered (.family context symbol arguments))

theorem rule_sound_before (model : ModelData S C localModel) {bound : Nat}
    (realization : BoundedRealization model D bound)
    (stable : StrictPiSubstitution localModel.products) (beta : PiBeta localModel.products)
    (eta : PiEta localModel.products stable.1) (rule : RuleCode D)
    (ordered : rule.conclusion.before D bound)
    (premises : (position : Fin rule.premises.length) → Interprets model (rule.premises.get position)) :
    Interprets model rule.conclusion := by
  apply model.rule_sound_with_declaration stable beta eta rule ?_ premises
  intro declaration head
  have earlier := declaredHead_before ordered head
  cases declaration with
  | family symbol => exact realization.typeHeader symbol earlier
  | term symbol => exact ⟨realization.termHeader symbol earlier, realization.termResult symbol earlier⟩
  | predicate symbol => exact realization.predicateHeader symbol earlier

end ModelData

namespace Derivation

theorem sound_before (model : ModelData S C localModel) {bound : Nat}
    (realization : BoundedRealization model D bound)
    (stable : StrictPiSubstitution localModel.products) (beta : PiBeta localModel.products)
    (eta : PiEta localModel.products stable.1) {judgment : Judgment S}
    (derivation : Derivation D judgment) (ordered : derivation.before bound) :
    Interprets model judgment := by
  refine JudgmentDerivation.Derivation.rec (S := judgmentSignature D)
    (motive := fun judgment tree => Derivation.before (D := D) bound tree → Interprets model judgment)
    (fun rule premises ih => ?_) derivation ordered
  rcases rule with ⟨rule, rfl⟩
  intro bounded
  exact model.rule_sound_before realization stable beta eta rule bounded.1
    (fun position => ih ⟨position⟩ (bounded.2 ⟨position⟩))

theorem qualified_sound_before (model : ModelData S C localModel) {bound : Nat}
    (realization : BoundedRealization model D bound) (qualified : Qualification localModel)
    {judgment : Judgment S} (derivation : Derivation D judgment)
    (ordered : derivation.before bound) : Interprets model judgment :=
  sound_before model realization qualified.stableProducts qualified.productBeta
    qualified.productEta derivation ordered

end Derivation

end Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.Abstract
