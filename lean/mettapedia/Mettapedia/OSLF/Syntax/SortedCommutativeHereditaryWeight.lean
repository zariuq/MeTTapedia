import Mettapedia.OSLF.Syntax.SortedCommutativeContextCategory
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!+# Hereditary weights of actual sorted AC1 terms and contexts

A supplied constructor weight is summed over every complete child and stored
sibling. The actual generated term and context equations preserve this sum.
Filling and composition add the complete weights, so a zero-weight composite
has zero-weight factors. These are properties of the independently formed
equation/context category, including unit and cross-root representatives.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.OSLF.SortedCommutative.HereditaryWeight

open _root_.CategoryTheory
open scoped BigOperators

universe u v

variable {signature : Mettapedia.OSLF.SortedConstructors.Signature.{u,v}}
  {Parallel : signature.Srt → Prop} (weight : signature.Constructor → Nat)

def term {sort : signature.Srt} (supplied : Term signature Parallel sort) : Nat :=
  @Term.rec signature Parallel (fun _ _ => Nat)
    (fun _ => 0) (fun _ _ _ first second => first + second)
    (fun constructor _ children => weight constructor + ∑ position, children position) sort supplied

@[simp] theorem term_zero {sort : signature.Srt} (parallel : Parallel sort) :
    term weight (.zero parallel : Term signature Parallel sort) = 0 := rfl

@[simp] theorem term_cut {sort : signature.Srt} (parallel : Parallel sort)
    (first second : Term signature Parallel sort) :
    term weight (.cut parallel first second) = term weight first + term weight second := rfl

@[simp] theorem term_node (constructor : signature.Constructor)
    (arguments : (position : Fin (signature.arity constructor)) → Term signature Parallel (signature.input constructor position)) :
    term weight (.node (signature := signature) (Parallel := Parallel) constructor arguments) =
      weight constructor + ∑ position, term weight (arguments position) := rfl

theorem term_equation {sort : signature.Srt} {first second : Term signature Parallel sort}
    (equation : Equation first second) : term weight first = term weight second := by
  apply @Equation.rec signature Parallel
    (fun {_sort} {first second} _ => term weight first = term weight second) (t := equation)
  · intro sort supplied
    rfl
  · intro sort first second equation inductionHypothesis
    exact inductionHypothesis.symm
  · intro sort first second third before after firstRead secondRead
    exact firstRead.trans secondRead
  · intro constructor first second equations inductionHypothesis
    exact congrArg (fun total => weight constructor + total)
      (Finset.sum_congr rfl (fun position _ => inductionHypothesis position))
  · intro sort parallel first first' second second' before after firstRead secondRead
    exact congrArg₂ (· + ·) firstRead secondRead
  · intro sort parallel first second third
    exact Nat.add_assoc _ _ _
  · intro sort parallel first second
    exact Nat.add_comm _ _
  · intro sort parallel supplied
    exact Nat.add_zero _

def classTerm {sort : signature.Srt} : Class signature Parallel sort → Nat :=
  Quotient.lift (term weight) (fun _ _ equation => term_equation weight equation)

def siblings (constructor : signature.Constructor) (position : Fin (signature.arity constructor))
    (supplied : (other : Fin (signature.arity constructor)) → other ≠ position →
      Term signature Parallel (signature.input constructor other)) : Nat :=
  ∑ other, if different : other ≠ position then term weight (supplied other different) else 0

theorem siblings_zero {constructor : signature.Constructor} {position : Fin (signature.arity constructor)}
    (supplied : (other : Fin (signature.arity constructor)) → other ≠ position →
      Term signature Parallel (signature.input constructor other))
    (zero : siblings weight constructor position supplied = 0)
    (other : Fin (signature.arity constructor)) (different : other ≠ position) :
    term weight (supplied other different) = 0 := by
  classical
  have bounded := Finset.single_le_sum
    (fun index _ => Nat.zero_le (if absent : index ≠ position then term weight (supplied index absent) else 0))
    (Finset.mem_univ other)
  simp only [dif_pos different] at bounded
  change _ ≤ siblings weight constructor position supplied at bounded
  omega

def context {first second : signature.Srt} (supplied : RawContext signature Parallel first second) : Nat :=
  @RawContext.rec signature Parallel first (fun _ _ => Nat) 0
    (fun constructor position supplied _ inner => weight constructor + siblings weight constructor position supplied + inner)
    (fun _ _ sibling inner => inner + term weight sibling)
    (fun _ sibling _ inner => term weight sibling + inner) second supplied

theorem context_equation {first second : signature.Srt} {before after : RawContext signature Parallel first second}
    (equation : ContextEquation before after) : context weight before = context weight after := by
  apply @ContextEquation.rec signature Parallel first
    (fun {_target} {before after} _ => context weight before = context weight after) (t := equation)
  · intro target supplied
    rfl
  · intro target before after equation inductionHypothesis
    exact inductionHypothesis.symm
  · intro target before middle after firstEq secondEq firstRead secondRead
    exact firstRead.trans secondRead
  · intro constructor position firstSiblings secondSiblings before after siblingEquations equation inductionHypothesis
    have siblingRead : siblings weight constructor position firstSiblings = siblings weight constructor position secondSiblings := by
      apply Finset.sum_congr rfl
      intro other _
      by_cases different : other ≠ position
      · simpa only [dif_pos different] using term_equation weight (siblingEquations other different)
      · simp only [dif_neg different]
    exact congrArg₂ (fun total inner => weight constructor + total + inner) siblingRead inductionHypothesis
  · intro target parallel before after first second inner sibling inductionHypothesis
    exact congrArg₂ (· + ·) inductionHypothesis (term_equation weight sibling)
  · intro target parallel first second before after sibling inner inductionHypothesis
    exact congrArg₂ (· + ·) (term_equation weight sibling) inductionHypothesis
  · intro target parallel inner sibling
    exact Nat.add_comm _ _
  · intro target parallel inner first second
    exact Nat.add_assoc _ _ _
  · intro target parallel inner
    exact Nat.add_zero _

def classContext {first second : signature.Srt} : ContextClass signature Parallel first second → Nat :=
  Quotient.lift (context weight) (fun _ _ equation => context_equation weight equation)

theorem insert_weight (constructor : signature.Constructor) (position : Fin (signature.arity constructor))
    (suppliedSiblings : (other : Fin (signature.arity constructor)) → other ≠ position →
      Term signature Parallel (signature.input constructor other))
    (supplied : Term signature Parallel (signature.input constructor position)) :
    (∑ other, term weight (RawContext.insert constructor position suppliedSiblings supplied other)) =
      term weight supplied + siblings weight constructor position suppliedSiblings := by
  classical
  calc
    _ = ∑ other, ((if other = position then term weight supplied else 0) +
        (if different : other ≠ position then term weight (suppliedSiblings other different) else 0)) := by
      apply Finset.sum_congr rfl
      intro other _
      by_cases same : other = position
      · subst other
        simp only [RawContext.insert, dite_true, if_true, ne_eq, not_true_eq_false, dite_false, Nat.add_zero]
      · simp only [RawContext.insert, dif_neg same, if_neg same, dif_pos same, Nat.zero_add]
    _ = term weight supplied + siblings weight constructor position suppliedSiblings := by
      rw [Finset.sum_add_distrib]
      simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true, siblings]

theorem context_fill {first second : signature.Srt} (suppliedContext : RawContext signature Parallel first second)
    (supplied : Term signature Parallel first) :
    term weight (suppliedContext.fill supplied) = context weight suppliedContext + term weight supplied := by
  apply @RawContext.rec signature Parallel first
    (fun _ suppliedContext => term weight (suppliedContext.fill supplied) = context weight suppliedContext + term weight supplied)
    (t := suppliedContext)
  · exact (Nat.zero_add _).symm
  · intro constructor position suppliedSiblings inner inductionHypothesis
    change weight constructor +
      (∑ other, term weight (RawContext.insert constructor position suppliedSiblings (inner.fill supplied) other)) = _
    rw [insert_weight, inductionHypothesis]
    change _ = (weight constructor + siblings weight constructor position suppliedSiblings + context weight inner) + term weight supplied
    omega
  · intro target parallel inner sibling inductionHypothesis
    change term weight (inner.fill supplied) + term weight sibling = _
    rw [inductionHypothesis]
    change _ = (context weight inner + term weight sibling) + term weight supplied
    omega
  · intro target parallel sibling inner inductionHypothesis
    change term weight sibling + term weight (inner.fill supplied) = _
    rw [inductionHypothesis]
    change _ = (term weight sibling + context weight inner) + term weight supplied
    omega

theorem context_comp {first second third : signature.Srt} (before : RawContext signature Parallel first second)
    (after : RawContext signature Parallel second third) :
    context weight (before.comp after) = context weight before + context weight after := by
  apply @RawContext.rec signature Parallel second
    (fun _ after => context weight (before.comp after) = context weight before + context weight after) (t := after)
  · exact (Nat.add_zero _).symm
  · intro constructor position suppliedSiblings outer inductionHypothesis
    change weight constructor + siblings weight constructor position suppliedSiblings + context weight (before.comp outer) = _
    rw [inductionHypothesis]
    change _ = context weight before + (weight constructor + siblings weight constructor position suppliedSiblings + context weight outer)
    omega
  · intro target parallel outer sibling inductionHypothesis
    change context weight (before.comp outer) + term weight sibling = _
    rw [inductionHypothesis]
    exact Nat.add_assoc _ _ _
  · intro target parallel sibling outer inductionHypothesis
    change term weight sibling + context weight (before.comp outer) = _
    rw [inductionHypothesis]
    change _ = context weight before + (term weight sibling + context weight outer)
    omega

theorem class_fill {first second : signature.Srt} (suppliedContext : ContextClass signature Parallel first second)
    (supplied : Class signature Parallel first) :
    classTerm weight (suppliedContext.fill supplied) = classContext weight suppliedContext + classTerm weight supplied :=
  Quotient.inductionOn₂ suppliedContext supplied (context_fill weight)

theorem class_comp {first second third : signature.Srt} (before : ContextClass signature Parallel first second)
    (after : ContextClass signature Parallel second third) :
    classContext weight (before.comp after) = classContext weight before + classContext weight after :=
  Quotient.inductionOn₂ before after (context_comp weight)

def arrow : {first second : RawObject signature Parallel} → (first ⟶ second) → Nat
  | _, _, .identity => 0
  | _, _, .value supplied => classTerm weight supplied
  | _, _, .context supplied => classContext weight supplied

@[simp] theorem arrow_id (object : RawObject signature Parallel) : arrow weight (𝟙 object) = 0 := by
  cases object <;> rfl

theorem arrow_comp {first second third : RawObject signature Parallel} (before : first ⟶ second) (after : second ⟶ third) :
    arrow weight (before ≫ after) = arrow weight before + arrow weight after := by
  cases before with
  | identity => exact (Nat.zero_add _).symm
  | value supplied =>
    cases after with
    | context suppliedContext => exact (class_fill weight suppliedContext supplied).trans (Nat.add_comm _ _)
  | context before =>
    cases after with
    | context after => exact class_comp weight before after

theorem composite_zero_iff {first second third : RawObject signature Parallel}
    (before : first ⟶ second) (after : second ⟶ third) :
    arrow weight (before ≫ after) = 0 ↔ arrow weight before = 0 ∧ arrow weight after = 0 := by
  rw [arrow_comp]
  exact Nat.add_eq_zero_iff

end Mettapedia.OSLF.SortedCommutative.HereditaryWeight
