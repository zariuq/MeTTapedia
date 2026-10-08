import Mettapedia.OSLF.Framework.InstrumentCutKitSupport
import Mettapedia.GSLT.Logic.RelativePushoutFunctor

/-!
# The actual context category selected by an instrument kit

Objects retain their sorted interfaces. A morphism is an actual ambient arrow
with hereditary kit support, so unavailable argument formers cannot appear in
its stored siblings or outer frames. Factor closure reconstructs every RPO
candidate and mediator on a supported bound; the inclusion therefore preserves
and reflects the complete universal property without being full.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.OSLF.Framework.InstrumentCutContexts

open _root_.CategoryTheory
open Mettapedia.OSLF.SortedConstructors
open Mettapedia.CategoryTheory.GroundPath
open Mettapedia.GSLT.RelativePushout
open Mettapedia.GSLT.RedexRelativeCongruence

universe u

variable {Symbols : Type u} (arity : Symbols → Nat)

local instance instrumentCutKitCategoryQuiver : Quiver (Srt Symbols arity) :=
  frameQuiver (signature arity)

structure KitObject (opened : InstrumentObservations.Policy Symbols) where
  base : ContextObject (signature arity)

instance kitCategory (opened : InstrumentObservations.Policy Symbols) :
    Category.{u} (KitObject arity opened) where
  Hom first second := {arrow : first.base ⟶ second.base // KitArrow arity opened arrow}
  id object := ⟨𝟙 object.base, KitArrow.id arity opened object.base⟩
  comp first second := ⟨first.val ≫ second.val, first.property.comp arity second.property⟩
  id_comp arrow := Subtype.ext (Category.id_comp arrow.val)
  comp_id arrow := Subtype.ext (Category.comp_id arrow.val)
  assoc first second third := Subtype.ext (Category.assoc first.val second.val third.val)

def kitOrigin (opened : InstrumentObservations.Policy Symbols) : KitObject arity opened := ⟨.origin⟩

def kitInterface (opened : InstrumentObservations.Policy Symbols) (sort : Srt Symbols arity) :
    KitObject arity opened := ⟨.interface sort⟩

def kitInclusion (opened : InstrumentObservations.Policy Symbols) :
    KitObject arity opened ⥤ ContextObject (signature arity) where
  obj object := object.base
  map arrow := arrow.val
  map_id _ := rfl
  map_comp _ _ := rfl

instance kitInclusion_faithful (opened : InstrumentObservations.Policy Symbols) :
    (kitInclusion arity opened).Faithful where
  map_injective := fun same => Subtype.ext same

def kitValue {opened : InstrumentObservations.Policy Symbols} {sort : Srt Symbols arity}
    (value : Value arity sort) (supported : KitSupported arity opened value) :
    kitOrigin arity opened ⟶ kitInterface arity opened sort :=
  ⟨termArrow (signature arity) value, .value supported⟩

def kitContext {opened : InstrumentObservations.Policy Symbols} {source target : Srt Symbols arity}
    (context : Context (signature arity) source target) (supported : KitContext arity opened context) :
    kitInterface arity opened source ⟶ kitInterface arity opened target :=
  ⟨contextArrow (signature arity) context, .context supported⟩

variable {opened : InstrumentObservations.Policy Symbols}
variable {W X Y Z : KitObject arity opened}
variable {f : W ⟶ X} {g : W ⟶ Y} {h : X ⟶ Z} {i : Y ⟶ Z}

def kitLiftCandidate
    (candidate : Candidate ((kitInclusion arity opened).map f)
      ((kitInclusion arity opened).map g) ((kitInclusion arity opened).map h)
      ((kitInclusion arity opened).map i)) : Candidate f g h i where
  apex := ⟨candidate.apex⟩
  inl := ⟨candidate.inl, (kitArrow_comp_inv arity candidate.inl candidate.down
    (by rw [candidate.fac_left]; exact h.property)).1⟩
  inr := ⟨candidate.inr, (kitArrow_comp_inv arity candidate.inr candidate.down
    (by rw [candidate.fac_right]; exact i.property)).1⟩
  down := ⟨candidate.down, (kitArrow_comp_inv arity candidate.inl candidate.down
    (by rw [candidate.fac_left]; exact h.property)).2⟩
  comm := Subtype.ext candidate.comm
  fac_left := Subtype.ext candidate.fac_left
  fac_right := Subtype.ext candidate.fac_right

theorem kitLiftCandidate_readout
    (candidate : Candidate ((kitInclusion arity opened).map f)
      ((kitInclusion arity opened).map g) ((kitInclusion arity opened).map h)
      ((kitInclusion arity opened).map i)) :
    mapCandidate (kitInclusion arity opened) (kitLiftCandidate arity candidate) = candidate := by
  cases candidate
  rfl

theorem kit_map_mediates {from_ to_ : Candidate f g h i}
    (mediator : from_.apex ⟶ to_.apex) (equations : Candidate.Mediates from_ to_ mediator) :
    Candidate.Mediates (mapCandidate (kitInclusion arity opened) from_)
      (mapCandidate (kitInclusion arity opened) to_) ((kitInclusion arity opened).map mediator) :=
  ⟨congrArg Subtype.val equations.1, congrArg Subtype.val equations.2.1,
    congrArg Subtype.val equations.2.2⟩

theorem kit_reflects_mediates {from_ to_ : Candidate f g h i}
    (mediator : from_.apex ⟶ to_.apex)
    (equations : Candidate.Mediates (mapCandidate (kitInclusion arity opened) from_)
      (mapCandidate (kitInclusion arity opened) to_) ((kitInclusion arity opened).map mediator)) :
    Candidate.Mediates from_ to_ mediator :=
  ⟨Subtype.ext equations.1, Subtype.ext equations.2.1, Subtype.ext equations.2.2⟩

def kitLiftMediator {from_ to_ : Candidate f g h i}
    (mediator : (kitInclusion arity opened).obj from_.apex ⟶
      (kitInclusion arity opened).obj to_.apex)
    (equations : Candidate.Mediates (mapCandidate (kitInclusion arity opened) from_)
      (mapCandidate (kitInclusion arity opened) to_) mediator) : from_.apex ⟶ to_.apex :=
  ⟨mediator, (kitArrow_comp_inv arity from_.inl.val mediator
    (by
      have readout : from_.inl.val ≫ mediator = to_.inl.val := equations.1
      exact readout.symm ▸ to_.inl.property)).2⟩

theorem kit_relativePushout_iff (candidate : Candidate f g h i) :
    IsRelativePushout candidate ↔ IsRelativePushout (mapCandidate (kitInclusion arity opened) candidate) := by
  constructor
  · intro universal other
    let original := kitLiftCandidate arity other
    obtain ⟨mediator, equations, unique⟩ := universal original
    refine ⟨mediator.val, ?_, ?_⟩
    · exact kit_map_mediates arity mediator equations
    · intro alternative laws
      let lifted := kitLiftMediator arity (to_ := original) alternative laws
      have same := unique lifted (kit_reflects_mediates arity lifted laws)
      exact congrArg Subtype.val same
  · intro universal other
    obtain ⟨mediator, equations, unique⟩ := universal (mapCandidate (kitInclusion arity opened) other)
    let lifted := kitLiftMediator arity mediator equations
    refine ⟨lifted, kit_reflects_mediates arity lifted equations, ?_⟩
    intro alternative laws
    apply Subtype.ext
    exact unique alternative.val (kit_map_mediates arity alternative laws)

theorem kit_idemPushout_iff (square : f ≫ h = g ≫ i) :
    IsIdemPushout f g h i square ↔
      IsIdemPushout f.val g.val h.val i.val (congrArg Subtype.val square) :=
  kit_relativePushout_iff arity (Candidate.self f g h i square)

theorem kit_origin_hasRelativePushouts {first second : KitObject arity opened}
    (left : kitOrigin arity opened ⟶ first) (right : kitOrigin arity opened ⟶ second) :
    HasRelativePushouts left right := by
  intro target leftBound rightBound square
  obtain ⟨candidate, universal⟩ := origin_hasRelativePushouts (action (signature arity))
    left.val right.val target.base leftBound.val rightBound.val (congrArg Subtype.val square)
  refine ⟨kitLiftCandidate arity candidate, (kit_relativePushout_iff arity _).mpr ?_⟩
  exact (kitLiftCandidate_readout arity candidate).symm ▸ universal

theorem kit_category_context_congruence
    (rules : ReactionRule (kitOrigin arity opened) → Prop)
    {first second : KitObject arity opened} (left right : kitOrigin arity opened ⟶ first)
    (related : IPOBisimilar rules left right) (context : first ⟶ second) :
    IPOBisimilar rules (left ≫ context) (right ≫ context) :=
  ipoBisimilar_comp (fun _ agent rule _ => kit_origin_hasRelativePushouts arity agent rule.redex)
    related context

end Mettapedia.OSLF.Framework.InstrumentCutContexts
