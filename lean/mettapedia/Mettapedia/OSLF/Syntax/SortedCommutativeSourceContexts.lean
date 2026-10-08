import Mettapedia.OSLF.Syntax.SortedCommutativeSourceValues

/-!
# Unchanged source context equations in the observer extension

Source contexts retain their exact original constructor position, sibling
terms and AC1 residues. A separately defined context erasure removes every
auxiliary observer frame and erases its siblings. This erasure reflects
source-image equations; it is not claimed to preserve arbitrary extended
closed-value filling. Actual source filling and composition are preserved.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.OSLF.Framework.SortedCommutativeInstruments.Source

open Mettapedia.OSLF.SortedCommutative

universe u

variable {Symbols : Type u} {arity : Symbols → Nat}

abbrev Context := RawContext (signature arity) (Parallel arity) (ULift.up ()) (ULift.up ())

def embedContext {source target : (signature arity).Srt} :
    RawContext (signature arity) (Parallel arity) source target →
      RawContext (SortedCommutativeInstruments.signature arity) (SortedCommutativeInstruments.Parallel arity) .base .base
  | .hole => .hole
  | .frame constructor position siblings inner =>
      .frame (signature := SortedCommutativeInstruments.signature arity)
        (Parallel := SortedCommutativeInstruments.Parallel arity)
        (SortedCommutativeInstruments.Constructor.original constructor) position
        (fun other absent => embed (siblings other absent)) (embedContext inner)
  | .left _ inner sibling => .left rfl (embedContext inner) (embed sibling)
  | .right _ sibling inner => .right rfl (embed sibling) (embedContext inner)

def eraseContext {source target : SortedCommutativeInstruments.Srt arity}
    (supplied : RawContext (SortedCommutativeInstruments.signature arity)
      (SortedCommutativeInstruments.Parallel arity) source target) : Context (arity := arity) :=
  @RawContext.rec (SortedCommutativeInstruments.signature arity) (SortedCommutativeInstruments.Parallel arity) source
    (fun _ _ => Context (arity := arity)) .hole
    (fun constructor position siblings _ inner => match constructor with
      | .original symbol => .frame (signature := signature arity) (Parallel := Parallel arity) symbol position (fun other absent => erase (siblings other absent)) inner
      | .arguments _ => inner
      | .probe _ => inner
      | .cut _ => inner)
    (fun _ _ sibling inner => .left rfl inner (erase sibling))
    (fun _ sibling _ inner => .right rfl (erase sibling) inner) target supplied

theorem embedContext_equation {source target : (signature arity).Srt}
    {first second : RawContext (signature arity) (Parallel arity) source target}
    (equation : ContextEquation (signature := signature arity) (Parallel := Parallel arity) first second) :
    ContextEquation (signature := SortedCommutativeInstruments.signature arity)
      (Parallel := SortedCommutativeInstruments.Parallel arity) (embedContext first) (embedContext second) := by
  induction equation with
  | refl => exact .refl _
  | symm _ inductionHypothesis => exact inductionHypothesis.symm
  | trans _ _ before after => exact before.trans after
  | frame constructor position siblings _ inductionHypothesis =>
    exact .frame (signature := SortedCommutativeInstruments.signature arity)
      (Parallel := SortedCommutativeInstruments.Parallel arity)
      (SortedCommutativeInstruments.Constructor.original constructor) position (fun other absent => embed_equation (siblings other absent)) inductionHypothesis
  | left _ _ sibling inner => exact ContextEquation.left _ inner (embed_equation sibling)
  | right _ sibling _ inner => exact ContextEquation.right _ (embed_equation sibling) inner
  | comm =>
    exact ContextEquation.comm (signature := SortedCommutativeInstruments.signature arity)
      (Parallel := SortedCommutativeInstruments.Parallel arity) rfl _ _
  | assoc =>
    exact ContextEquation.assoc (signature := SortedCommutativeInstruments.signature arity)
      (Parallel := SortedCommutativeInstruments.Parallel arity) rfl _ _ _
  | unit =>
    exact ContextEquation.unit (signature := SortedCommutativeInstruments.signature arity)
      (Parallel := SortedCommutativeInstruments.Parallel arity) rfl _

theorem eraseContext_equation {source target : SortedCommutativeInstruments.Srt arity}
    {first second : RawContext (SortedCommutativeInstruments.signature arity)
      (SortedCommutativeInstruments.Parallel arity) source target}
    (equation : ContextEquation (signature := SortedCommutativeInstruments.signature arity)
      (Parallel := SortedCommutativeInstruments.Parallel arity) first second) :
    ContextEquation (signature := signature arity) (Parallel := Parallel arity) (eraseContext first) (eraseContext second) := by
  apply @ContextEquation.rec (SortedCommutativeInstruments.signature arity)
    (SortedCommutativeInstruments.Parallel arity) source
    (fun {_target} {first second} _ => ContextEquation (signature := signature arity)
      (Parallel := Parallel arity) (eraseContext first) (eraseContext second)) (t := equation)
  · intro target context
    exact .refl _
  · intro target first second equation inductionHypothesis
    exact inductionHypothesis.symm
  · intro target first second third before after firstRead secondRead
    exact firstRead.trans secondRead
  · intro constructor position firstSiblings secondSiblings first second siblings equation inductionHypothesis
    cases constructor with
    | original symbol =>
      exact .frame symbol position (fun other absent => erase_equation (siblings other absent)) inductionHypothesis
    | arguments => exact inductionHypothesis
    | probe => exact inductionHypothesis
    | cut => exact inductionHypothesis
  · intro target parallel first second before after inner sibling inductionHypothesis
    exact .left rfl inductionHypothesis (erase_equation sibling)
  · intro target parallel before after first second sibling inner inductionHypothesis
    exact .right rfl (erase_equation sibling) inductionHypothesis
  · intro target parallel inner sibling
    exact .comm rfl _ _
  · intro target parallel inner first second
    exact .assoc rfl _ _ _
  · intro target parallel inner
    exact .unit rfl _

private theorem eraseContext_embed_heq {target : (signature arity).Srt}
    (supplied : RawContext (signature arity) (Parallel arity) (ULift.up ()) target) :
    HEq (eraseContext (embedContext supplied)) supplied := by
  apply @RawContext.rec (signature arity) (Parallel arity) (ULift.up ())
    (fun _ context => HEq (eraseContext (embedContext context)) context) (t := supplied)
  · rfl
  · intro constructor position siblings inner inductionHypothesis
    exact heq_of_eq (congrArg₂ (RawContext.frame constructor position)
      (funext (fun other => funext (fun absent => erase_embed (siblings other absent))))
      (eq_of_heq inductionHypothesis))
  · intro target parallel inner sibling inductionHypothesis
    cases target with
    | up target =>
      cases target
      exact heq_of_eq (congrArg₂ (RawContext.left rfl) (eq_of_heq inductionHypothesis) (erase_embed sibling))
  · intro target parallel sibling inner inductionHypothesis
    cases target with
    | up target =>
      cases target
      exact heq_of_eq (congrArg₂ (RawContext.right rfl) (erase_embed sibling) (eq_of_heq inductionHypothesis))

theorem eraseContext_embed (supplied : Context (arity := arity)) :
    eraseContext (embedContext supplied) = supplied := eq_of_heq (eraseContext_embed_heq supplied)

theorem contextEquation_iff_embedded (first second : Context (arity := arity)) :
    ContextEquation first second ↔ ContextEquation (embedContext first) (embedContext second) := by
  refine ⟨embedContext_equation, fun equation => ?_⟩
  simpa only [eraseContext_embed] using eraseContext_equation equation

theorem embedContext_fill {source target : (signature arity).Srt}
    (context : RawContext (signature arity) (Parallel arity) source target)
    (supplied : Term (signature arity) (Parallel arity) source) :
    (embedContext context).fill (embed supplied) = embed (context.fill supplied) := by
  induction context with
  | hole => rfl
  | frame constructor position siblings inner inductionHypothesis =>
    apply congrArg (Term.node (signature := SortedCommutativeInstruments.signature arity) (.original constructor))
    funext other
    by_cases same : other = position
    · subst other
      simpa only [RawContext.insert, dite_true] using inductionHypothesis
    · simp only [RawContext.insert, dif_neg same]
  | left _ inner sibling inductionHypothesis => exact congrArg (fun term => Term.cut (signature := SortedCommutativeInstruments.signature arity)
    (Parallel := SortedCommutativeInstruments.Parallel arity) rfl term (embed sibling)) inductionHypothesis
  | right _ sibling inner inductionHypothesis => exact congrArg (Term.cut (signature := SortedCommutativeInstruments.signature arity)
    (Parallel := SortedCommutativeInstruments.Parallel arity) rfl (embed sibling)) inductionHypothesis

theorem embedContext_comp {source middle target : (signature arity).Srt}
    (inner : RawContext (signature arity) (Parallel arity) source middle)
    (outer : RawContext (signature arity) (Parallel arity) middle target) :
    (embedContext inner).comp (embedContext outer) = embedContext (inner.comp outer) := by
  induction outer with
  | hole => rfl
  | frame constructor position siblings outer inductionHypothesis =>
    exact congrArg (RawContext.frame (signature := SortedCommutativeInstruments.signature arity)
      (Parallel := SortedCommutativeInstruments.Parallel arity)
      (SortedCommutativeInstruments.Constructor.original constructor) position (fun other absent => embed (siblings other absent))) inductionHypothesis
  | left _ outer sibling inductionHypothesis => exact congrArg (fun context => RawContext.left (signature := SortedCommutativeInstruments.signature arity)
    (Parallel := SortedCommutativeInstruments.Parallel arity) rfl context (embed sibling)) inductionHypothesis
  | right _ sibling outer inductionHypothesis => exact congrArg (RawContext.right (signature := SortedCommutativeInstruments.signature arity)
    (Parallel := SortedCommutativeInstruments.Parallel arity) rfl (embed sibling)) inductionHypothesis

def contextEmbedding : ContextClass (signature arity) (Parallel arity) (ULift.up ()) (ULift.up ()) →
    ContextClass (SortedCommutativeInstruments.signature arity) (SortedCommutativeInstruments.Parallel arity) .base .base :=
  Quotient.map embedContext (fun _ _ equation => embedContext_equation equation)

def contextRetraction {source target : SortedCommutativeInstruments.Srt arity} :
    ContextClass (SortedCommutativeInstruments.signature arity) (SortedCommutativeInstruments.Parallel arity) source target →
      ContextClass (signature arity) (Parallel arity) (ULift.up ()) (ULift.up ()) :=
  Quotient.map eraseContext (fun _ _ equation => eraseContext_equation equation)

theorem context_retraction_embedding
    (supplied : ContextClass (signature arity) (Parallel arity) (ULift.up ()) (ULift.up ())) :
    contextRetraction (contextEmbedding supplied) = supplied :=
  Quotient.inductionOn supplied (fun raw => congrArg contextClassOf (eraseContext_embed raw))

theorem contextEmbedding_injective : Function.Injective (contextEmbedding (arity := arity)) := by
  intro first second same
  exact (context_retraction_embedding first).symm.trans
    ((congrArg contextRetraction same).trans (context_retraction_embedding second))

end Mettapedia.OSLF.Framework.SortedCommutativeInstruments.Source
