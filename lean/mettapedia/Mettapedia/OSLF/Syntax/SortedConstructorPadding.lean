import Mettapedia.OSLF.Syntax.SortedConstructorContexts

/-!
# A genuine unary-unit equation and its sorted term quotient

A unary padding constructor is adjoined at one declared sort. The authored
equation removes precisely this padding, and its actual symmetric transitive
constructor congruence is proved equivalent to independently computed
normalization. The quotient is compared bijectively with the original sorted
constructor terms; an original binary cut remains an original constructor.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.OSLF.SortedConstructors.Padding

universe u v

variable (signature : Signature.{u,v}) (paddingSort : signature.Srt)

abbrev extended : Signature.{u,v} where
  Srt := signature.Srt
  Constructor := signature.Constructor ⊕ PUnit
  arity
    | .inl constructor => signature.arity constructor
    | .inr _ => 1
  input
    | .inl constructor => signature.input constructor
    | .inr _ => fun _ => paddingSort
  output
    | .inl constructor => signature.output constructor
    | .inr _ => paddingSort

abbrev RawTerm (sort : signature.Srt) := Term (extended signature paddingSort) sort

def pad (term : RawTerm signature paddingSort paddingSort) : RawTerm signature paddingSort paddingSort :=
  Term.node (signature := extended signature paddingSort) (Sum.inr PUnit.unit) (fun _ => term)

def embed {sort : signature.Srt} (term : Term signature sort) : RawTerm signature paddingSort sort :=
  @Term.rec signature (fun sort _ => RawTerm signature paddingSort sort)
    (fun constructor _ inductionHypothesis =>
      Term.node (signature := extended signature paddingSort) (Sum.inl constructor) inductionHypothesis) sort term

def normalize {sort : signature.Srt} (term : RawTerm signature paddingSort sort) : Term signature sort :=
  @Term.rec (extended signature paddingSort) (fun sort _ => Term signature sort)
    (fun constructor _ inductionHypothesis => by
      cases constructor with
      | inl original => exact Term.node (signature := signature) original inductionHypothesis
      | inr _ => exact inductionHypothesis 0) sort term

@[simp]
theorem normalize_pad (term : RawTerm signature paddingSort paddingSort) :
    normalize signature paddingSort (pad signature paddingSort term) =
      normalize signature paddingSort term := rfl

@[simp]
theorem normalize_embed {sort : signature.Srt} (term : Term signature sort) :
    normalize signature paddingSort (embed signature paddingSort term) = term := by
  induction term with
  | node constructor arguments inductionHypothesis =>
    change Term.node constructor
      (fun position => normalize signature paddingSort (embed signature paddingSort (arguments position))) =
      Term.node constructor arguments
    exact congrArg (Term.node constructor) (funext inductionHypothesis)

/-- Actual authored unit equations, with sorted congruence closure. -/
inductive Equation : {sort : signature.Srt} → RawTerm signature paddingSort sort →
    RawTerm signature paddingSort sort → Prop where
  | refl {sort : signature.Srt} (term : RawTerm signature paddingSort sort) : Equation term term
  | unit (term : RawTerm signature paddingSort paddingSort) :
      Equation (pad signature paddingSort term) term
  | symm {sort : signature.Srt} {first second : RawTerm signature paddingSort sort} :
      Equation first second → Equation second first
  | trans {sort : signature.Srt} {first second third : RawTerm signature paddingSort sort} :
      Equation first second → Equation second third → Equation first third
  | congruence (constructor : (extended signature paddingSort).Constructor)
      (first second : (position : Fin ((extended signature paddingSort).arity constructor)) →
        RawTerm signature paddingSort ((extended signature paddingSort).input constructor position))
      (arguments : ∀ position, Equation (first position) (second position)) :
      Equation (Term.node (signature := extended signature paddingSort) constructor first)
        (Term.node (signature := extended signature paddingSort) constructor second)

variable {signature paddingSort}

theorem equation_normalizes {sort : signature.Srt}
    {first second : RawTerm signature paddingSort sort}
    (equation : Equation signature paddingSort first second) :
    normalize signature paddingSort first = normalize signature paddingSort second := by
  induction equation with
  | refl => rfl
  | unit => rfl
  | symm _ inductionHypothesis => exact inductionHypothesis.symm
  | trans _ _ firstIH secondIH => exact firstIH.trans secondIH
  | congruence constructor first second _ inductionHypothesis =>
    cases constructor with
    | inl original => exact congrArg (Term.node original) (funext inductionHypothesis)
    | inr _ => exact inductionHypothesis 0

theorem normalization_equation {sort : signature.Srt} (term : RawTerm signature paddingSort sort) :
    Equation signature paddingSort term
      (embed signature paddingSort (normalize signature paddingSort term)) := by
  refine @Term.rec (extended signature paddingSort)
    (fun sort term => Equation signature paddingSort term
      (embed signature paddingSort (normalize signature paddingSort term))) ?_ sort term
  intro constructor arguments inductionHypothesis
  cases constructor with
  | inl original =>
      exact Equation.congruence (Sum.inl original) arguments
        (fun position => embed signature paddingSort (normalize signature paddingSort (arguments position)))
        inductionHypothesis
  | inr padding =>
      cases padding
      have supplied : arguments = fun _ => arguments 0 := by
        funext position
        have same : position = 0 := Subsingleton.elim position 0
        subst position
        rfl
      rw [supplied]
      exact Equation.trans (.unit (arguments 0)) (inductionHypothesis 0)

theorem equation_iff_normalizes {sort : signature.Srt}
    (first second : RawTerm signature paddingSort sort) :
    Equation signature paddingSort first second ↔
      normalize signature paddingSort first = normalize signature paddingSort second := by
  refine ⟨equation_normalizes, fun same => ?_⟩
  have firstEquation := normalization_equation first
  have secondEquation := normalization_equation second
  rw [same] at firstEquation
  exact Equation.trans firstEquation secondEquation.symm

def termSetoid (signature : Signature.{u,v}) (paddingSort sort : signature.Srt) :
    Setoid (RawTerm signature paddingSort sort) where
  r := Equation signature paddingSort
  iseqv := ⟨Equation.refl, Equation.symm, Equation.trans⟩

abbrev Class (signature : Signature.{u,v}) (paddingSort sort : signature.Srt) :=
  Quotient (termSetoid signature paddingSort sort)

def classOf {sort : signature.Srt} (term : RawTerm signature paddingSort sort) :
    Class signature paddingSort sort := Quotient.mk _ term

def value (signature : Signature.{u,v}) (paddingSort : signature.Srt) {sort : signature.Srt} :
    Class signature paddingSort sort → Term signature sort :=
  Quotient.lift (normalize signature paddingSort) (fun _ _ equation => equation_normalizes equation)

def termEquiv (signature : Signature.{u,v}) (paddingSort sort : signature.Srt) :
    Class signature paddingSort sort ≃ Term signature sort where
  toFun := value signature paddingSort
  invFun := fun term => classOf (embed signature paddingSort term)
  left_inv := by
    intro termClass
    induction termClass using Quotient.inductionOn with
    | _ term => exact Quotient.sound (normalization_equation term).symm
  right_inv := normalize_embed signature paddingSort

theorem classOf_eq_iff {sort : signature.Srt} (first second : RawTerm signature paddingSort sort) :
    classOf first = classOf second ↔ Equation signature paddingSort first second :=
  ⟨fun same => Quotient.exact same, fun equation =>
    Quotient.sound (s := termSetoid signature paddingSort sort) equation⟩

end Mettapedia.OSLF.SortedConstructors.Padding
