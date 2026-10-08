import Mettapedia.OSLF.Framework.SortedTypedInstrumentKitCategory
import Mettapedia.GSLT.Logic.RelativePushoutFunctor

/-!
# Complete RPO and IPO comparison for supported typed kits

Every competing ambient candidate below a supported bound has supported
incoming arrows and descent, by actual factor closure. Its complete apex,
three arrows and every mediator therefore reconstruct in the kit category.
This earns RPO preservation and reflection, redex-RPO existence and context
congruence of actual all-label IPO bisimilarity. Increasing a kit preserves
the same complete minimality comparisons without ambient fullness.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.OSLF.Framework.SortedTypedInstruments.Kit

open _root_.CategoryTheory
open Mettapedia.OSLF.SortedCommutative
open Mettapedia.GSLT.RelativePushout Mettapedia.GSLT.RedexRelativeCongruence

universe u v u₁ v₁

variable {source : Mettapedia.OSLF.SortedConstructors.Signature.{u,v}}
  {Parallel : source.Srt → Prop} {opened : Policy source Parallel}
variable {W X Y Z : Object opened}
variable {f : W ⟶ X} {g : W ⟶ Y} {h : X ⟶ Z} {i : Y ⟶ Z}

private theorem candidate_eq_of_readouts {C : Type u₁} [Category.{v₁} C]
    {w x y z : C} {first : w ⟶ x} {second : w ⟶ y} {left : x ⟶ z} {right : y ⟶ z}
    (before after : Candidate first second left right) (apex : before.apex = after.apex)
    (inl : HEq before.inl after.inl) (inr : HEq before.inr after.inr) (down : HEq before.down after.down) :
    before = after := by
  cases before
  cases after
  cases apex
  cases eq_of_heq inl
  cases eq_of_heq inr
  cases eq_of_heq down
  rfl

private theorem factors_supported {first second third : ContextCategory source Parallel}
    (before : first ⟶ second) (after : second ⟶ third) (supported : ArrowSupported opened (before ≫ after)) :
    ArrowSupported opened before ∧ ArrowSupported opened after :=
  (arrow_supported_comp_iff opened before after).mp supported

def liftCandidate
    (candidate : Candidate ((inclusion opened).map f) ((inclusion opened).map g)
      ((inclusion opened).map h) ((inclusion opened).map i)) : Candidate f g h i where
  apex := ⟨candidate.apex⟩
  inl := ⟨candidate.inl, (factors_supported candidate.inl candidate.down
    (by rw [candidate.fac_left]; exact h.property)).1⟩
  inr := ⟨candidate.inr, (factors_supported candidate.inr candidate.down
    (by rw [candidate.fac_right]; exact i.property)).1⟩
  down := ⟨candidate.down, (factors_supported candidate.inl candidate.down
    (by rw [candidate.fac_left]; exact h.property)).2⟩
  comm := Subtype.ext candidate.comm
  fac_left := Subtype.ext candidate.fac_left
  fac_right := Subtype.ext candidate.fac_right

theorem liftCandidate_readout
    (candidate : Candidate ((inclusion opened).map f) ((inclusion opened).map g)
      ((inclusion opened).map h) ((inclusion opened).map i)) :
    mapCandidate (inclusion opened) (liftCandidate candidate) = candidate := by
  cases candidate
  rfl

theorem map_mediates {before after : Candidate f g h i}
    (mediator : before.apex ⟶ after.apex) (equations : Candidate.Mediates before after mediator) :
    Candidate.Mediates (mapCandidate (inclusion opened) before) (mapCandidate (inclusion opened) after)
      ((inclusion opened).map mediator) :=
  ⟨congrArg Subtype.val equations.1, congrArg Subtype.val equations.2.1, congrArg Subtype.val equations.2.2⟩

theorem reflects_mediates {before after : Candidate f g h i}
    (mediator : before.apex ⟶ after.apex)
    (equations : Candidate.Mediates (mapCandidate (inclusion opened) before)
      (mapCandidate (inclusion opened) after) ((inclusion opened).map mediator)) :
    Candidate.Mediates before after mediator :=
  ⟨Subtype.ext equations.1, Subtype.ext equations.2.1, Subtype.ext equations.2.2⟩

def liftMediator {before after : Candidate f g h i}
    (mediator : (inclusion opened).obj before.apex ⟶ (inclusion opened).obj after.apex)
    (equations : Candidate.Mediates (mapCandidate (inclusion opened) before)
      (mapCandidate (inclusion opened) after) mediator) : before.apex ⟶ after.apex :=
  ⟨mediator, (factors_supported before.inl.val mediator
    (by
      have readout : before.inl.val ≫ mediator = after.inl.val := equations.1
      exact readout.symm ▸ after.inl.property)).2⟩

theorem relativePushout_iff (candidate : Candidate f g h i) :
    IsRelativePushout candidate ↔ IsRelativePushout (mapCandidate (inclusion opened) candidate) := by
  constructor
  · intro universal other
    let original := liftCandidate other
    obtain ⟨mediator, equations, unique⟩ := universal original
    refine ⟨mediator.val, map_mediates mediator equations, ?_⟩
    intro alternative laws
    let lifted := liftMediator (after := original) alternative laws
    exact congrArg Subtype.val (unique lifted (reflects_mediates lifted laws))
  · intro universal other
    obtain ⟨mediator, equations, unique⟩ := universal (mapCandidate (inclusion opened) other)
    let lifted := liftMediator mediator equations
    refine ⟨lifted, reflects_mediates lifted equations, ?_⟩
    intro alternative laws
    exact Subtype.ext (unique alternative.val (map_mediates alternative laws))

theorem idemPushout_iff (square : f ≫ h = g ≫ i) :
    IsIdemPushout f g h i square ↔
      IsIdemPushout ((inclusion opened).map f) ((inclusion opened).map g)
        ((inclusion opened).map h) ((inclusion opened).map i) (congrArg Subtype.val square) := by
  have readout : mapCandidate (inclusion opened) (Candidate.self f g h i square) =
      Candidate.self ((inclusion opened).map f) ((inclusion opened).map g)
        ((inclusion opened).map h) ((inclusion opened).map i) (congrArg Subtype.val square) :=
    candidate_eq_of_readouts _ _ rfl HEq.rfl HEq.rfl (heq_of_eq ((inclusion opened).map_id Z))
  simpa only [IsIdemPushout, readout] using relativePushout_iff (Candidate.self f g h i square)

theorem redex_relativePushouts {first second : Object opened}
    (agent : origin opened ⟶ first) (redex : origin opened ⟶ second) : HasRelativePushouts agent redex := by
  intro apex left right square
  obtain ⟨ambient, universal⟩ := raw_redex_relativePushouts agent.val redex.val apex.base left.val right.val
    (congrArg Subtype.val square)
  refine ⟨liftCandidate ambient, (relativePushout_iff (liftCandidate ambient)).mpr ?_⟩
  simpa only [liftCandidate_readout] using universal

theorem bisimulation_context_congruence (rules : ReactionRule (origin opened) → Prop)
    {first second : Object opened} {before after : origin opened ⟶ first}
    (related : IPOBisimilar rules before after) (suppliedContext : first ⟶ second) :
    IPOBisimilar rules (before ≫ suppliedContext) (after ≫ suppliedContext) :=
  ipoBisimilar_comp (fun _ agent rule _ => redex_relativePushouts agent rule.redex) related suppliedContext

theorem expand_candidate_readout {second : Policy source Parallel} (subkit : ∀ head, opened head → second head)
    (candidate : Candidate f g h i) :
    mapCandidate (inclusion second) (mapCandidate (expand subkit) candidate) =
      mapCandidate (inclusion opened) candidate := by
  cases candidate
  rfl

theorem expanded_relativePushout_iff {second : Policy source Parallel} (subkit : ∀ head, opened head → second head)
    (candidate : Candidate f g h i) :
    IsRelativePushout candidate ↔ IsRelativePushout (mapCandidate (expand subkit) candidate) := by
  rw [relativePushout_iff candidate, relativePushout_iff (mapCandidate (expand subkit) candidate),
    expand_candidate_readout]

theorem expanded_idemPushout_iff {second : Policy source Parallel} (subkit : ∀ head, opened head → second head)
    (square : f ≫ h = g ≫ i) :
    IsIdemPushout f g h i square ↔
      IsIdemPushout ((expand subkit).map f) ((expand subkit).map g)
        ((expand subkit).map h) ((expand subkit).map i) (congrArg (expand subkit).map square) := by
  have readout : mapCandidate (expand subkit) (Candidate.self f g h i square) =
      Candidate.self ((expand subkit).map f) ((expand subkit).map g)
        ((expand subkit).map h) ((expand subkit).map i) (congrArg (expand subkit).map square) :=
    candidate_eq_of_readouts _ _ rfl HEq.rfl HEq.rfl (heq_of_eq ((expand subkit).map_id Z))
  simpa only [IsIdemPushout, readout] using expanded_relativePushout_iff subkit (Candidate.self f g h i square)

end Mettapedia.OSLF.Framework.SortedTypedInstruments.Kit
