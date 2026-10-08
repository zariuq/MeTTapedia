import Mettapedia.TypeTheory.Calculi.NativeDependent.ExternalHeaderFormation
import Mathlib.Data.Fintype.Fin

/-!
# Deciding bounds on supplied declaration derivations

The structural decision procedures inspect every annotation and every actual
premise occurrence of a supplied finite derivation. They decide declaration
rank bounds, without deciding formation or assuming a semantic interpreter.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.NativeDependent.External

universe u

variable {S : Symbols.{u}}
variable (typeRank : S.TypeSymbol → Nat) (termRank : S.TermSymbol → Nat) (bound : Nat)

mutual

def TypeExpr.decidableBefore : ∀ {n : Nat} (value : TypeExpr S n),
    Decidable (value.before typeRank termRank bound)
  | _, .family symbol arguments => by
      letI : ∀ position, Decidable ((arguments position).before typeRank termRank bound) :=
        fun position => TermExpr.decidableBefore (arguments position)
      change Decidable (typeRank symbol < bound ∧ ∀ position,
        (arguments position).before typeRank termRank bound)
      infer_instance
  | _, .pi domain body => by
      letI := TypeExpr.decidableBefore domain
      letI := TypeExpr.decidableBefore body
      change Decidable (domain.before typeRank termRank bound ∧ body.before typeRank termRank bound)
      infer_instance
  | _, .sigma domain body => by
      letI := TypeExpr.decidableBefore domain
      letI := TypeExpr.decidableBefore body
      change Decidable (domain.before typeRank termRank bound ∧ body.before typeRank termRank bound)
      infer_instance

def TermExpr.decidableBefore : ∀ {n : Nat} (value : TermExpr S n),
    Decidable (value.before typeRank termRank bound)
  | _, .var _ => isTrue trivial
  | _, .primitive symbol arguments => by
      letI : ∀ position, Decidable ((arguments position).before typeRank termRank bound) :=
        fun position => TermExpr.decidableBefore (arguments position)
      change Decidable (termRank symbol < bound ∧ ∀ position,
        (arguments position).before typeRank termRank bound)
      infer_instance
  | _, .lam domain codomain body => by
      letI := TypeExpr.decidableBefore domain
      letI := TypeExpr.decidableBefore codomain
      letI := TermExpr.decidableBefore body
      change Decidable (domain.before typeRank termRank bound ∧
        codomain.before typeRank termRank bound ∧ body.before typeRank termRank bound)
      infer_instance
  | _, .app domain body function argument => by
      letI := TypeExpr.decidableBefore domain
      letI := TypeExpr.decidableBefore body
      letI := TermExpr.decidableBefore function
      letI := TermExpr.decidableBefore argument
      change Decidable (domain.before typeRank termRank bound ∧ body.before typeRank termRank bound ∧
        function.before typeRank termRank bound ∧ argument.before typeRank termRank bound)
      infer_instance
  | _, .pair domain body first second => by
      letI := TypeExpr.decidableBefore domain
      letI := TypeExpr.decidableBefore body
      letI := TermExpr.decidableBefore first
      letI := TermExpr.decidableBefore second
      change Decidable (domain.before typeRank termRank bound ∧ body.before typeRank termRank bound ∧
        first.before typeRank termRank bound ∧ second.before typeRank termRank bound)
      infer_instance
  | _, .fst domain body pair => by
      letI := TypeExpr.decidableBefore domain
      letI := TypeExpr.decidableBefore body
      letI := TermExpr.decidableBefore pair
      change Decidable (domain.before typeRank termRank bound ∧ body.before typeRank termRank bound ∧
        pair.before typeRank termRank bound)
      infer_instance
  | _, .snd domain body pair => by
      letI := TypeExpr.decidableBefore domain
      letI := TypeExpr.decidableBefore body
      letI := TermExpr.decidableBefore pair
      change Decidable (domain.before typeRank termRank bound ∧ body.before typeRank termRank bound ∧
        pair.before typeRank termRank bound)
      infer_instance
  | _, .sigmaElim domain body motive branch pair => by
      letI := TypeExpr.decidableBefore domain
      letI := TypeExpr.decidableBefore body
      letI := TypeExpr.decidableBefore motive
      letI := TermExpr.decidableBefore branch
      letI := TermExpr.decidableBefore pair
      change Decidable (domain.before typeRank termRank bound ∧ body.before typeRank termRank bound ∧
        motive.before typeRank termRank bound ∧ branch.before typeRank termRank bound ∧
        pair.before typeRank termRank bound)
      infer_instance

end

instance {n : Nat} (value : TypeExpr S n) : Decidable (value.before typeRank termRank bound) :=
  value.decidableBefore typeRank termRank bound

instance {n : Nat} (value : TermExpr S n) : Decidable (value.before typeRank termRank bound) :=
  value.decidableBefore typeRank termRank bound

def ContextExpr.decidableBefore : ∀ {n : Nat} (context : ContextExpr S n),
    Decidable (context.before typeRank termRank bound)
  | _, .nil => isTrue trivial
  | _, .snoc context type => by
      letI := ContextExpr.decidableBefore context
      change Decidable (context.before typeRank termRank bound ∧ type.before typeRank termRank bound)
      infer_instance

instance {n : Nat} (context : ContextExpr S n) : Decidable (context.before typeRank termRank bound) :=
  context.decidableBefore typeRank termRank bound

def Judgment.decidableBefore (D : Signature S) : (judgment : Judgment S) →
    Decidable (judgment.before D bound)
  | .context _ => by dsimp only [Judgment.before]; infer_instance
  | .type _ _ => by dsimp only [Judgment.before]; infer_instance
  | .term _ _ _ => by dsimp only [Judgment.before]; infer_instance
  | .substitution _ _ _ => by dsimp only [Judgment.before]; infer_instance
  | .contextEq _ _ => by dsimp only [Judgment.before]; infer_instance
  | .typeEq _ _ _ => by dsimp only [Judgment.before]; infer_instance
  | .termEq _ _ _ _ => by dsimp only [Judgment.before]; infer_instance
  | .substitutionEq _ _ _ _ => by dsimp only [Judgment.before]; infer_instance

instance (D : Signature S) (judgment : Judgment S) : Decidable (judgment.before D bound) :=
  judgment.decidableBefore bound D

def Derivation.decidableBefore {D : Signature S} : ∀ {judgment : Judgment S}
    (tree : Derivation D judgment), Decidable (tree.before bound)
  | _, .node rule premises => by
      letI : Fintype ((judgmentSignature D).Premise rule) := by
        change Fintype (ULift (Fin rule.val.premises.length))
        infer_instance
      letI : ∀ position, Decidable (Derivation.before bound (premises position)) :=
        fun position => Derivation.decidableBefore (premises position)
      change Decidable (rule.val.conclusion.before D bound ∧
        ∀ position, Derivation.before bound (premises position))
      infer_instance

instance {D : Signature S} {judgment : Judgment S} (tree : Derivation D judgment) :
    Decidable (tree.before bound) := tree.decidableBefore bound

end Mettapedia.TypeTheory.Calculi.NativeDependent.External
