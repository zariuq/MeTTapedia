import Mettapedia.OSLF.Framework.InstrumentCutSourceReactions
import Mettapedia.CategoryTheory.OneVertexPathEmbedding

/-!
# The independent source context category and its faithful typed inclusion

Source frames retain actual source trees at every unselected position. Their
lists act by constructor filling; they do not identify contexts merely because
their ground actions agree. The origin has source trees as arrows. The typed
inclusion traverses all frames and siblings into the original constructors of
the extended signature, including its selected original binary cut.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.OSLF.Framework.InstrumentCutContexts

open _root_.CategoryTheory
open Mettapedia.OSLF.SortedConstructors
open Mettapedia.CategoryTheory.GroundPath

universe u

variable {Symbols : Type u} (arity : Symbols → Nat)

local instance instrumentSourceContextCategoryQuiver : Quiver (Srt Symbols arity) := frameQuiver (signature arity)

structure SourceFrame where
  constructor : Symbols
  position : Fin (arity constructor)
  siblings : (other : Fin (arity constructor)) → other ≠ position → InstrumentObservations.Tree Symbols arity

def SourceFrame.fill (frame : SourceFrame arity) (supplied : InstrumentObservations.Tree Symbols arity) :
    InstrumentObservations.Tree Symbols arity := by
  classical
  exact .node frame.constructor (fun other => if same : other = frame.position then supplied else frame.siblings other same)

def sourceFrameImage (frame : SourceFrame arity) : Frame (signature arity) (.base : Srt Symbols arity) .base :=
  Frame.slot (signature := signature arity) (Constructor.original frame.constructor) frame.position
    (fun other absent => embedSource arity (frame.siblings other absent))

theorem sourceFrame_fill_readout (frame : SourceFrame arity) (supplied : InstrumentObservations.Tree Symbols arity) :
    embedSource arity (frame.fill arity supplied) = Frame.fill (sourceFrameImage arity frame) (embedSource arity supplied) := by
  classical
  apply congrArg (Term.node (signature := signature arity) (Constructor.original frame.constructor))
  funext other
  split_ifs with same
  · subst other; simp; rfl
  · simp [same]; rfl

theorem sourceFrameImage_injective : Function.Injective (sourceFrameImage arity) := by
  intro first second same
  rcases first with ⟨firstConstructor, firstPosition, firstSiblings⟩
  rcases second with ⟨secondConstructor, secondPosition, secondSiblings⟩
  have heads := congrArg (fun frame => Frame.constructor frame) same
  have headEq : firstConstructor = secondConstructor := Constructor.original.inj heads
  subst secondConstructor
  have positions := congrArg (fun frame : Frame (signature arity) (.base : Srt Symbols arity) .base => frame.position.val) same
  have positionEq : firstPosition = secondPosition := Fin.ext positions
  subst secondPosition
  have siblings := Frame.slot.inj same
  apply congrArg (SourceFrame.mk firstConstructor firstPosition)
  funext other absent
  exact embedSource_injective arity (congrFun (congrFun siblings other) absent)

abbrev SourceContext := List (SourceFrame arity)

def SourceContext.fill : SourceContext arity → InstrumentObservations.Tree Symbols arity →
    InstrumentObservations.Tree Symbols arity
  | [], supplied => supplied
  | frame :: previous, supplied => frame.fill arity (fill previous supplied)

def sourceContextImage : SourceContext arity → Context (signature arity) (.base : Srt Symbols arity) .base :=
  Mettapedia.CategoryTheory.OneVertexPathEmbedding.path (sourceFrameImage arity)

theorem sourceContext_fill_readout (context : SourceContext arity) (supplied : InstrumentObservations.Tree Symbols arity) :
    embedSource arity (SourceContext.fill arity context supplied) =
      (action (signature arity)).path (sourceContextImage arity context) (embedSource arity supplied) := by
  induction context with
  | nil => rfl
  | cons frame previous inductionHypothesis =>
    exact (sourceFrame_fill_readout arity frame (SourceContext.fill arity previous supplied)).trans
      (congrArg (Frame.fill (sourceFrameImage arity frame)) inductionHypothesis)

theorem sourceContextImage_injective : Function.Injective (sourceContextImage arity) :=
  @Mettapedia.CategoryTheory.OneVertexPathEmbedding.path_injective
    (Srt Symbols arity) (frameQuiver (signature arity)) (SourceFrame arity) .base
    (sourceFrameImage arity) (sourceFrameImage_injective arity)

theorem sourceContext_fill_append (outer inner : SourceContext arity)
    (supplied : InstrumentObservations.Tree Symbols arity) :
    SourceContext.fill arity (outer ++ inner) supplied =
      SourceContext.fill arity outer (SourceContext.fill arity inner supplied) := by
  induction outer with
  | nil => rfl
  | cons frame previous inductionHypothesis => exact congrArg (frame.fill arity) inductionHypothesis

inductive SourceObject (Symbols : Type u) (arity : Symbols → Nat) where
  | origin
  | base

inductive SourceArrow : SourceObject Symbols arity → SourceObject Symbols arity → Type u where
  | identity : SourceArrow .origin .origin
  | value (supplied : InstrumentObservations.Tree Symbols arity) : SourceArrow .origin .base
  | context (supplied : SourceContext arity) : SourceArrow .base .base

namespace SourceArrow

def id : (object : SourceObject Symbols arity) → SourceArrow arity object object
  | .origin => .identity
  | .base => .context []

def comp : {first middle target : SourceObject Symbols arity} → SourceArrow arity first middle →
    SourceArrow arity middle target → SourceArrow arity first target
  | _, _, _, .identity, second => second
  | _, _, _, .value supplied, .context suppliedContext => .value (SourceContext.fill arity suppliedContext supplied)
  | _, _, _, .context first, .context second => .context (second ++ first)

theorem id_comp {source target : SourceObject Symbols arity} (arrow : SourceArrow arity source target) :
    comp arity (id arity source) arrow = arrow := by
  cases arrow with
  | identity => rfl
  | value => rfl
  | context supplied => exact congrArg SourceArrow.context (List.append_nil supplied)

theorem comp_id {source target : SourceObject Symbols arity} (arrow : SourceArrow arity source target) :
    comp arity arrow (id arity target) = arrow := by cases arrow <;> rfl

theorem assoc {first second third fourth : SourceObject Symbols arity}
    (f : SourceArrow arity first second) (g : SourceArrow arity second third)
    (h : SourceArrow arity third fourth) : comp arity (comp arity f g) h = comp arity f (comp arity g h) := by
  cases f with
  | identity => rfl
  | value supplied =>
    cases g with
    | context first =>
      cases h with
      | context second => exact congrArg SourceArrow.value (sourceContext_fill_append arity second first supplied).symm
  | context first =>
    cases g with
    | context second =>
      cases h with
      | context third => exact congrArg SourceArrow.context (List.append_assoc third second first).symm

end SourceArrow

instance sourceCategory : Category.{u} (SourceObject Symbols arity) where
  Hom := SourceArrow arity
  id := SourceArrow.id arity
  comp := SourceArrow.comp arity
  id_comp := SourceArrow.id_comp arity
  comp_id := SourceArrow.comp_id arity
  assoc := SourceArrow.assoc arity

def sourceObjectImage : SourceObject Symbols arity → ContextObject (signature arity)
  | .origin => .origin
  | .base => .interface .base

def sourceArrowImage {source target : SourceObject Symbols arity} (arrow : source ⟶ target) :
    sourceObjectImage arity source ⟶ sourceObjectImage arity target :=
  match arrow with
  | .identity => .identity
  | .value supplied => .value (embedSource arity supplied)
  | .context supplied => .context (sourceContextImage arity supplied)

def sourceFunctor : SourceObject Symbols arity ⥤ ContextObject (signature arity) where
  obj := sourceObjectImage arity
  map := sourceArrowImage arity
  map_id object := by cases object <;> rfl
  map_comp first second := by
    cases first with
    | identity => rfl
    | value supplied =>
      cases second with
      | context suppliedContext => exact congrArg Arrow.value (sourceContext_fill_readout arity suppliedContext supplied)
    | context left =>
      cases second with
      | context right =>
        exact congrArg Arrow.context
          (@Mettapedia.CategoryTheory.OneVertexPathEmbedding.path_append
            (Srt Symbols arity) (frameQuiver (signature arity)) (SourceFrame arity) .base
            (sourceFrameImage arity) right left)

instance sourceFunctor_faithful : (sourceFunctor arity).Faithful where
  map_injective := by
    intro source target first second same
    cases first with
    | identity => cases second; rfl
    | value supplied =>
      cases second with
      | value other => exact congrArg SourceArrow.value (embedSource_injective arity (Arrow.value.inj same))
    | context supplied =>
      cases second with
      | context other =>
        exact congrArg SourceArrow.context
          (sourceContextImage_injective arity (Arrow.context.inj same))

end Mettapedia.OSLF.Framework.InstrumentCutContexts
