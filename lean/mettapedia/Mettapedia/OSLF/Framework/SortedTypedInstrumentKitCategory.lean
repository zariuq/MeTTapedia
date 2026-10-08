import Mettapedia.OSLF.Framework.SortedTypedInstrumentKitContextSupport

/-!
# The actual many-sorted context category selected by an instrument kit

Each arrow retains an actual equation/context class and its independently
earned hereditary support. Every original source term and context belongs
to every kit. Increasing a kit gives a genuine functor whose complete arrow
action is the unchanged supplied class; no ambient fullness is inferred.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.OSLF.Framework.SortedTypedInstruments.Kit

open _root_.CategoryTheory
open Mettapedia.OSLF.SortedCommutative

universe u v

variable {source : Mettapedia.OSLF.SortedConstructors.Signature.{u,v}}
  {Parallel : source.Srt → Prop}

theorem Allowed.monotone {first second : Policy source Parallel} (inclusion : ∀ head, first head → second head)
    {constructor : Constructor source Parallel} (allowed : Allowed first constructor) : Allowed second constructor := by
  cases allowed with
  | original constructor => exact .original constructor
  | arguments head permission => exact .arguments head (inclusion head permission)
  | probe instrument permission => exact .probe instrument (inclusion _ permission)
  | cut instrument permission => exact .cut instrument (inclusion _ permission)

theorem ContextSupported.monotone {first second : Policy source Parallel} (inclusion : ∀ head, first head → second head)
    {before after : Srt source Parallel} {supplied : RawContext (signature source Parallel) NativeParallel before after}
    (supported : ContextSupported first supplied) : ContextSupported second supplied := by
  induction supported with
  | hole => exact .hole _
  | frame allowed children previous inductionHypothesis =>
    exact .frame (allowed.monotone inclusion) (fun other different => (children other different).monotone inclusion)
      inductionHypothesis
  | left parallel previous stored inductionHypothesis => exact .left parallel inductionHypothesis (stored.monotone inclusion)
  | right parallel stored previous inductionHypothesis => exact .right parallel (stored.monotone inclusion) inductionHypothesis

theorem ClassContextSupported.monotone {first second : Policy source Parallel} (inclusion : ∀ head, first head → second head)
    {before after : Srt source Parallel} {supplied : ContextClass (signature source Parallel) NativeParallel before after}
    (supported : ClassContextSupported first supplied) : ClassContextSupported second supplied := by
  obtain ⟨raw, rawSupported, read⟩ := supported
  exact ⟨raw, rawSupported.monotone inclusion, read⟩

theorem ArrowSupported.monotone {first second : Policy source Parallel} (inclusion : ∀ head, first head → second head)
    {before after : ContextCategory source Parallel} {supplied : before ⟶ after}
    (supported : ArrowSupported first supplied) : ArrowSupported second supplied := by
  cases supported with
  | identity => exact .identity
  | value supported => exact .value (supported.monotone inclusion)
  | context supported => exact .context (supported.monotone inclusion)

structure Object (opened : Policy source Parallel) where
  base : ContextCategory source Parallel

instance category (opened : Policy source Parallel) : Category.{max u v} (Object opened) where
  Hom before after := {arrow : before.base ⟶ after.base // ArrowSupported opened arrow}
  id object := ⟨𝟙 object.base, ArrowSupported.id opened object.base⟩
  comp before after := ⟨before.val ≫ after.val, before.property.comp after.property⟩
  id_comp arrow := Subtype.ext (Category.id_comp arrow.val)
  comp_id arrow := Subtype.ext (Category.comp_id arrow.val)
  assoc before middle after := Subtype.ext (Category.assoc before.val middle.val after.val)

def origin (opened : Policy source Parallel) : Object opened := ⟨.origin⟩
def interface (opened : Policy source Parallel) (sort : Srt source Parallel) : Object opened := ⟨.interface sort⟩

def inclusion (opened : Policy source Parallel) : Object opened ⥤ ContextCategory source Parallel where
  obj object := object.base
  map arrow := arrow.val
  map_id _ := rfl
  map_comp _ _ := rfl

instance inclusion_faithful (opened : Policy source Parallel) : (inclusion opened).Faithful where
  map_injective := fun same => Subtype.ext same

theorem inclusion_surjective (opened : Policy source Parallel) : Function.Surjective (inclusion opened).obj :=
  fun object => ⟨⟨object⟩, rfl⟩

def value {opened : Policy source Parallel} {sort : Srt source Parallel}
    (supplied : ValueClass (source := source) (Parallel := Parallel) sort) (supported : ClassSupported opened supplied) :
    origin opened ⟶ interface opened sort := ⟨RawArrow.value supplied, .value supported⟩

def context {opened : Policy source Parallel} {first second : Srt source Parallel}
    (supplied : ContextClass (signature source Parallel) NativeParallel first second)
    (supported : ClassContextSupported opened supplied) :
    interface opened first ⟶ interface opened second := ⟨RawArrow.context supplied, .context supported⟩

def expand {first second : Policy source Parallel} (inclusion : ∀ head, first head → second head) :
    Object first ⥤ Object second where
  obj object := ⟨object.base⟩
  map arrow := ⟨arrow.val, arrow.property.monotone inclusion⟩
  map_id _ := rfl
  map_comp _ _ := rfl

instance expand_faithful {first second : Policy source Parallel} (inclusion : ∀ head, first head → second head) :
    (expand inclusion).Faithful where
  map_injective := by
    intro before after firstArrow secondArrow same
    apply Subtype.ext
    exact congrArg (fun arrow : (expand inclusion).obj before ⟶ (expand inclusion).obj after => arrow.val) same

theorem expand_inclusion {first second : Policy source Parallel} (subkit : ∀ head, first head → second head) :
    expand subkit ⋙ inclusion second = inclusion first := rfl

theorem expand_id (opened : Policy source Parallel) :
    expand (fun head (permission : opened head) => permission) = 𝟭 (Object opened) := rfl

theorem expand_comp {first second third : Policy source Parallel}
    (before : ∀ head, first head → second head) (after : ∀ head, second head → third head) :
    expand before ⋙ expand after = expand (fun head permission => after head (before head permission)) := rfl

theorem embedContext_supported (opened : Policy source Parallel) {first second : source.Srt}
    (supplied : RawContext source Parallel first second) : ContextSupported opened (embedContext supplied) := by
  induction supplied with
  | hole => exact .hole (.original first)
  | frame constructor position siblings inner inductionHypothesis =>
    exact .frame (.original constructor) (fun other different => embed_supported opened (siblings other different))
      inductionHypothesis
  | @left second parallel inner sibling inductionHypothesis =>
    exact .left (second := .original second) parallel inductionHypothesis (embed_supported opened sibling)
  | @right second parallel sibling inner inductionHypothesis =>
    exact .right (second := .original second) parallel (embed_supported opened sibling) inductionHypothesis

theorem source_arrow_supported (opened : Policy source Parallel) {first second : SourceCategory source Parallel}
    (supplied : first ⟶ second) : ArrowSupported opened ((SortedTypedInstruments.inclusion source Parallel).map supplied) := by
  cases supplied with
  | identity => exact .identity
  | value supplied => exact .value (classEmbedding_supported opened supplied)
  | context supplied =>
    refine .context ?_
    exact Quotient.inductionOn supplied (fun raw => ⟨embedContext raw, embedContext_supported opened raw, rfl⟩)

def sourceInclusion (opened : Policy source Parallel) : SourceCategory source Parallel ⥤ Object opened where
  obj object := ⟨(SortedTypedInstruments.inclusion source Parallel).obj object⟩
  map arrow := ⟨(SortedTypedInstruments.inclusion source Parallel).map arrow, source_arrow_supported opened arrow⟩
  map_id _ := Subtype.ext ((SortedTypedInstruments.inclusion source Parallel).map_id _)
  map_comp _ _ := Subtype.ext ((SortedTypedInstruments.inclusion source Parallel).map_comp _ _)

instance sourceInclusion_faithful (opened : Policy source Parallel) : (sourceInclusion opened).Faithful where
  map_injective := fun same => (SortedTypedInstruments.inclusion source Parallel).map_injective (congrArg Subtype.val same)

theorem sourceInclusion_inclusion (opened : Policy source Parallel) :
    sourceInclusion opened ⋙ inclusion opened = SortedTypedInstruments.inclusion source Parallel := rfl

theorem sourceInclusion_expand {first second : Policy source Parallel} (subkit : ∀ head, first head → second head) :
    sourceInclusion first ⋙ expand subkit = sourceInclusion second := rfl

end Mettapedia.OSLF.Framework.SortedTypedInstruments.Kit
