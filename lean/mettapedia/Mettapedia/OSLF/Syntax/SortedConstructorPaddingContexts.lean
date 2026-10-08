import Mettapedia.OSLF.Syntax.SortedConstructorPadding
import Mettapedia.OSLF.Syntax.SortedConstructorContextFaithfulness

/-!
# Authored padding equations on actual typed context paths

Padding frames become identity paths, while every original frame retains its
constructor and position and normalizes its actual sibling terms. The local
context equations independently allow padding removal, sibling equations and
composition. Their generated closure is proved equivalent to normalization,
including the full term-filling square.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.OSLF.SortedConstructors.Padding

open Mettapedia.CategoryTheory.GroundPath

universe u v

def framePath (signature : Signature.{u,v}) {source target : signature.Srt}
    (frame : Frame signature source target) : Context signature source target :=
  @Quiver.Hom.toPath signature.Srt (frameQuiver signature) source target frame

variable (signature : Signature.{u,v}) (paddingSort : signature.Srt)

def embedFrame {source target : signature.Srt} (frame : Frame signature source target) :
    Frame (extended signature paddingSort) source target := by
  cases frame with
  | slot constructor position siblings =>
    exact Frame.slot (signature := extended signature paddingSort) (Sum.inl constructor) position (fun other absent => embed signature paddingSort (siblings other absent))

def normalizeFrame {source target : signature.Srt}
    (frame : Frame (extended signature paddingSort) source target) : Context signature source target := by
  cases frame using @Frame.casesOn (extended signature paddingSort) with
  | slot constructor position siblings =>
    cases constructor with
    | inl original =>
      exact framePath signature (Frame.slot (signature := signature) original position
        (fun other absent => normalize signature paddingSort (siblings other absent)))
    | inr _ => exact .nil

def embedContext {source target : signature.Srt} (context : Context signature source target) :
    Context (extended signature paddingSort) source target :=
  @Quiver.Path.rec signature.Srt (frameQuiver signature) source
    (fun target _ => Context (extended signature paddingSort) source target) .nil
    (fun _ frame inductionHypothesis => inductionHypothesis.cons (embedFrame signature paddingSort frame))
    target context

def normalizeContext {source target : signature.Srt}
    (context : Context (extended signature paddingSort) source target) : Context signature source target :=
  @Quiver.Path.rec signature.Srt (frameQuiver (extended signature paddingSort)) source
    (fun target _ => Context signature source target) .nil
    (fun _ frame inductionHypothesis => inductionHypothesis.comp (normalizeFrame signature paddingSort frame))
    target context

theorem embedContext_comp {first middle target : signature.Srt}
    (left : Context signature first middle) (right : Context signature middle target) :
    embedContext signature paddingSort (left.comp right) =
      (embedContext signature paddingSort left).comp (embedContext signature paddingSort right) := by
  induction right with
  | nil => rfl
  | cons previous frame inductionHypothesis =>
    exact congrArg (fun context => context.cons (embedFrame signature paddingSort frame)) inductionHypothesis

theorem normalizeContext_comp {first middle target : signature.Srt}
    (left : Context (extended signature paddingSort) first middle)
    (right : Context (extended signature paddingSort) middle target) :
    normalizeContext signature paddingSort (left.comp right) =
      (normalizeContext signature paddingSort left).comp (normalizeContext signature paddingSort right) := by
  induction right with
  | nil => rfl
  | cons previous frame inductionHypothesis =>
    change (normalizeContext signature paddingSort (left.comp previous)).comp
        (normalizeFrame signature paddingSort frame) =
      (normalizeContext signature paddingSort left).comp
        ((normalizeContext signature paddingSort previous).comp (normalizeFrame signature paddingSort frame))
    rw [inductionHypothesis, Quiver.Path.comp_assoc]

theorem normalize_embedFrame {source target : signature.Srt} (frame : Frame signature source target) :
    normalizeFrame signature paddingSort (embedFrame signature paddingSort frame) = framePath signature frame := by
  cases frame with
  | slot constructor position siblings =>
    apply congrArg (fun supplied => framePath signature (Frame.slot (signature := signature) constructor position supplied))
    funext other absent
    exact normalize_embed signature paddingSort (siblings other absent)

theorem normalize_embedContext {source target : signature.Srt} (context : Context signature source target) :
    normalizeContext signature paddingSort (embedContext signature paddingSort context) = context := by
  induction context with
  | nil => rfl
  | cons previous frame inductionHypothesis =>
    change (normalizeContext signature paddingSort (embedContext signature paddingSort previous)).comp
      (normalizeFrame signature paddingSort (embedFrame signature paddingSort frame)) = previous.cons frame
    rw [inductionHypothesis, normalize_embedFrame]
    rfl

theorem normalize_fillFrame {source target : signature.Srt}
    (frame : Frame (extended signature paddingSort) source target)
    (supplied : RawTerm signature paddingSort source) :
    normalize signature paddingSort (Frame.fill frame supplied) =
      (action signature).path (normalizeFrame signature paddingSort frame)
        (normalize signature paddingSort supplied) := by
  classical
  cases frame using @Frame.casesOn (extended signature paddingSort) with
  | slot constructor position siblings =>
    cases constructor with
    | inl original =>
      change Term.node original (fun other => normalize signature paddingSort
          (if same : other = position then same.symm ▸ supplied else siblings other same)) =
        Frame.fill (Frame.slot original position
          (fun other absent => normalize signature paddingSort (siblings other absent)))
          (normalize signature paddingSort supplied)
      rw [Frame.fill_slot]
      apply congrArg (Term.node original)
      funext other
      split_ifs with same
      · subst other; rfl
      · rfl
    | inr _ =>
      have zero : position = 0 := Subsingleton.elim position 0
      subst position
      rfl

theorem normalize_fillContext {source target : signature.Srt}
    (context : Context (extended signature paddingSort) source target)
    (supplied : RawTerm signature paddingSort source) :
    normalize signature paddingSort ((action (extended signature paddingSort)).path context supplied) =
      (action signature).path (normalizeContext signature paddingSort context)
        (normalize signature paddingSort supplied) := by
  induction context with
  | nil => rfl
  | cons previous frame inductionHypothesis =>
    change normalize signature paddingSort
        (Frame.fill frame ((action (extended signature paddingSort)).path previous supplied)) =
      (action signature).path ((normalizeContext signature paddingSort previous).comp
        (normalizeFrame signature paddingSort frame)) (normalize signature paddingSort supplied)
    exact (normalize_fillFrame signature paddingSort frame
      ((action (extended signature paddingSort)).path previous supplied)).trans
      ((congrArg ((action signature).path (normalizeFrame signature paddingSort frame))
        inductionHypothesis).trans
        ((action signature).path_comp (normalizeContext signature paddingSort previous)
          (normalizeFrame signature paddingSort frame) (normalize signature paddingSort supplied)).symm)

inductive ContextEquation : {source target : signature.Srt} →
    Context (extended signature paddingSort) source target →
    Context (extended signature paddingSort) source target → Prop where
  | refl {source target : signature.Srt} (context : Context (extended signature paddingSort) source target) :
      ContextEquation context context
  | padding (position : Fin 1)
      (siblings : (other : Fin 1) → other ≠ position → RawTerm signature paddingSort paddingSort) :
      ContextEquation (framePath (extended signature paddingSort) (Frame.slot (signature := extended signature paddingSort)
        (Sum.inr PUnit.unit) position siblings)) .nil
  | siblings (constructor : signature.Constructor) (position : Fin (signature.arity constructor))
      (first second : (other : Fin (signature.arity constructor)) → other ≠ position →
        RawTerm signature paddingSort (signature.input constructor other))
      (equations : ∀ other absent, Equation signature paddingSort (first other absent) (second other absent)) :
      ContextEquation
        (framePath (extended signature paddingSort) (Frame.slot (signature := extended signature paddingSort) (Sum.inl constructor) position first))
        (framePath (extended signature paddingSort) (Frame.slot (signature := extended signature paddingSort) (Sum.inl constructor) position second))
  | symm {source target : signature.Srt}
      {first second : Context (extended signature paddingSort) source target} :
      ContextEquation first second → ContextEquation second first
  | trans {source target : signature.Srt}
      {first second third : Context (extended signature paddingSort) source target} :
      ContextEquation first second → ContextEquation second third → ContextEquation first third
  | comp {source middle target : signature.Srt}
      {first first' : Context (extended signature paddingSort) source middle}
      {second second' : Context (extended signature paddingSort) middle target} :
      ContextEquation first first' → ContextEquation second second' →
        ContextEquation (first.comp second) (first'.comp second')

variable {signature paddingSort}

theorem contextEquation_normalizes {source target : signature.Srt}
    {first second : Context (extended signature paddingSort) source target}
    (equation : ContextEquation signature paddingSort first second) :
    normalizeContext signature paddingSort first = normalizeContext signature paddingSort second := by
  induction equation with
  | refl => rfl
  | padding => rfl
  | siblings constructor position first second equations =>
    apply congrArg (fun supplied => framePath signature (Frame.slot (signature := signature) constructor position supplied))
    funext other absent
    exact equation_normalizes (equations other absent)
  | symm _ inductionHypothesis => exact inductionHypothesis.symm
  | trans _ _ firstIH secondIH => exact firstIH.trans secondIH
  | comp _ _ firstIH secondIH =>
    rw [normalizeContext_comp, normalizeContext_comp, firstIH, secondIH]

theorem normalization_frame_equation {source target : signature.Srt}
    (frame : Frame (extended signature paddingSort) source target) :
    ContextEquation signature paddingSort (framePath (extended signature paddingSort) frame)
      (embedContext signature paddingSort (normalizeFrame signature paddingSort frame)) := by
  cases frame using @Frame.casesOn (extended signature paddingSort) with
  | slot constructor position siblings =>
    cases constructor with
    | inl original =>
      exact ContextEquation.siblings original position siblings
        (fun other absent => embed signature paddingSort (normalize signature paddingSort (siblings other absent)))
        (fun other absent => normalization_equation (siblings other absent))
    | inr padding =>
      cases padding
      exact ContextEquation.padding position siblings

theorem normalization_context_equation {source target : signature.Srt}
    (context : Context (extended signature paddingSort) source target) :
    ContextEquation signature paddingSort context
      (embedContext signature paddingSort (normalizeContext signature paddingSort context)) := by
  induction context with
  | nil => exact ContextEquation.refl .nil
  | cons previous frame inductionHypothesis =>
    change ContextEquation signature paddingSort (@Quiver.Path.comp signature.Srt (frameQuiver (extended signature paddingSort)) _ _ _
      previous (framePath (extended signature paddingSort) frame))
      (embedContext signature paddingSort ((normalizeContext signature paddingSort previous).comp
        (normalizeFrame signature paddingSort frame)))
    rw [embedContext_comp]
    exact ContextEquation.comp inductionHypothesis (normalization_frame_equation frame)

theorem contextEquation_iff_normalizes {source target : signature.Srt}
    (first second : Context (extended signature paddingSort) source target) :
    ContextEquation signature paddingSort first second ↔
      normalizeContext signature paddingSort first = normalizeContext signature paddingSort second := by
  refine ⟨contextEquation_normalizes, fun same => ?_⟩
  have firstEquation := normalization_context_equation first
  rw [same] at firstEquation
  exact ContextEquation.trans firstEquation (normalization_context_equation second).symm

def contextSetoid (signature : Signature.{u,v}) (paddingSort source target : signature.Srt) :
    Setoid (Context (extended signature paddingSort) source target) where
  r := ContextEquation signature paddingSort
  iseqv := ⟨ContextEquation.refl, ContextEquation.symm, ContextEquation.trans⟩

abbrev ContextClass (signature : Signature.{u,v}) (paddingSort source target : signature.Srt) :=
  Quotient (contextSetoid signature paddingSort source target)

def contextClassOf {source target : signature.Srt}
    (context : Context (extended signature paddingSort) source target) :
    ContextClass signature paddingSort source target := Quotient.mk _ context

def contextValue (signature : Signature.{u,v}) (paddingSort : signature.Srt)
    {source target : signature.Srt} : ContextClass signature paddingSort source target →
    Context signature source target :=
  Quotient.lift (normalizeContext signature paddingSort) (fun _ _ equation => contextEquation_normalizes equation)

def contextEquiv (signature : Signature.{u,v}) (paddingSort source target : signature.Srt) :
    ContextClass signature paddingSort source target ≃ Context signature source target where
  toFun := contextValue signature paddingSort
  invFun := fun context => contextClassOf (embedContext signature paddingSort context)
  left_inv := by
    intro contextClass
    induction contextClass using Quotient.inductionOn with
    | _ context => exact Quotient.sound (normalization_context_equation context).symm
  right_inv := normalize_embedContext signature paddingSort

end Mettapedia.OSLF.SortedConstructors.Padding
