import Mettapedia.OSLF.Syntax.IntrinsicScopedConditionalSubstitution
import Mathlib.CategoryTheory.Category.Basic

/-!
# The category of contextual reduction judgments at a fixed sort

Objects are pairs of program endpoints in a typed variable context. An arrow
is an ordinary-variable substitution that sends both endpoints to the target
pair. Thus substitution of individual firing evidence can be represented by
an arrow independently of any authored rule constructor.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.IntrinsicScopedConditionalJudgmentCategory

open _root_.CategoryTheory
open Mettapedia.OSLF.Binding
open Mettapedia.OSLF.Binding.BindingSubstitutionAlgebra
open Mettapedia.OSLF.Binding.AuthoredPositionedRulePolynomial (Judgment)
open Mettapedia.OSLF.Binding.IntrinsicScopedConditionalSubstitution

variable {S : Signature}
variable (A : BindingCloneAlgebra.Algebra.{0} S)

/-- Endpoint pairs at one fixed sort, with their ordinary-variable context. -/
structure State (sort : S.Srt) where
  context : Ctx S
  source : A.substitution.Carrier context sort
  target : A.substitution.Carrier context sort

/-- A substitution arrow carries its environment and verifies both
endpoint equations. It does not quotient firing witnesses. -/
structure Map {sort : S.Srt} (first second : State A sort) where
  environment : Environment S A.substitution.Carrier first.context second.context
  sourceEq : A.substitution.substitute environment first.source = second.source
  targetEq : A.substitution.substitute environment first.target = second.target

@[ext] theorem Map.ext {sort : S.Srt} {first second : State A sort}
    {f g : Map A first second} (same : f.environment = g.environment) :
    f = g := by
  cases f
  cases g
  cases same
  rfl

/-- Composition is semantic substitution of the environment components. -/
def Map.comp {sort : S.Srt} {first middle last : State A sort}
    (f : Map A first middle) (g : Map A middle last) : Map A first last where
  environment := fun s v => A.substitution.substitute g.environment (f.environment s v)
  sourceEq := by
    calc
      A.substitution.substitute
          (fun s v => A.substitution.substitute g.environment (f.environment s v))
          first.source =
        A.substitution.substitute g.environment
          (A.substitution.substitute f.environment first.source) :=
            (A.substitution.substitute_comp f.environment g.environment
              first.source).symm
      _ = A.substitution.substitute g.environment middle.source :=
        congrArg (A.substitution.substitute g.environment) f.sourceEq
      _ = last.source := g.sourceEq
  targetEq := by
    calc
      A.substitution.substitute
          (fun s v => A.substitution.substitute g.environment (f.environment s v))
          first.target =
        A.substitution.substitute g.environment
          (A.substitution.substitute f.environment first.target) :=
            (A.substitution.substitute_comp f.environment g.environment
              first.target).symm
      _ = A.substitution.substitute g.environment middle.target :=
        congrArg (A.substitution.substitute g.environment) f.targetEq
      _ = last.target := g.targetEq

noncomputable instance (sort : S.Srt) : Category (State A sort) where
  Hom := Map A
  id first := {
    environment := fun _ var => A.substitution.injectVar var
    sourceEq := A.substitution.substitute_identity first.source
    targetEq := A.substitution.substitute_identity first.target }
  comp := Map.comp A
  id_comp := by
    intro first second f
    apply Map.ext A
    funext s v
    exact A.substitution.substitute_var f.environment v
  comp_id := by
    intro first second f
    apply Map.ext A
    funext s v
    exact A.substitution.substitute_identity (f.environment s v)
  assoc := by
    intro first middle third last f g h
    apply Map.ext A
    funext s v
    exact A.substitution.substitute_comp g.environment h.environment
      (f.environment s v)

/-- View a general sorted judgment in its fixed-sort fiber. -/
def ofJudgment (judgment : Judgment A) : State A judgment.2.1 :=
  ⟨judgment.1, judgment.2.2.1, judgment.2.2.2⟩

/-- Forget the fixed-sort packaging without changing endpoints. -/
def State.asJudgment {sort : S.Srt} (state : State A sort) : Judgment A :=
  ⟨state.context, sort, state.source, state.target⟩

theorem State.as_of (judgment : Judgment A) :
    (ofJudgment A judgment).asJudgment A = judgment := by
  cases judgment with
  | mk Γ rest =>
    cases rest with
    | mk sort endpoints => rfl

theorem State.of_as {sort : S.Srt} (state : State A sort) :
    ofJudgment A (state.asJudgment A) = state := by
  cases state
  rfl

/-- The indexed judgment substitution is a genuine arrow of this category. -/
def substitutionArrow (judgment : Judgment A) {Δ : Ctx S}
    (σ : Environment S A.substitution.Carrier judgment.1 Δ) :
    ofJudgment A judgment ⟶ ofJudgment A (substJudgment judgment σ) where
  environment := σ
  sourceEq := rfl
  targetEq := rfl

/-- Every arrow of the fixed-sort category is exactly a substitution of
both endpoints of its source judgment. -/
theorem Map.as_substitution {sort : S.Srt}
    {first second : State A sort} (f : first ⟶ second) :
    substJudgment (first.asJudgment A) f.environment =
      second.asJudgment A := by
  change (⟨second.context, sort,
      A.substitution.substitute f.environment first.source,
      A.substitution.substitute f.environment first.target⟩ : Judgment A) =
    ⟨second.context, sort, second.source, second.target⟩
  rw [f.sourceEq, f.targetEq]

end Mettapedia.OSLF.Binding.IntrinsicScopedConditionalJudgmentCategory
