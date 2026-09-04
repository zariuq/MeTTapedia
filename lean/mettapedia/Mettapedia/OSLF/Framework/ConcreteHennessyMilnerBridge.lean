import Mettapedia.OSLF.Formula
import Mettapedia.OSLF.Framework.HennessyMilnerNativeTypes

/-!
# The concrete OSLF formula syntax and the Hennessy--Milner fragment

`OSLFFormula` is the public, serializable modal syntax.  This module gives it
semantics over an arbitrary equation-aware GSLT system with string-valued
observations, embeds both Hennessy--Milner fragments into that syntax, and
proves preservation and reflection of satisfaction.  Consequently the
translated concrete formulas characterize bisimilarity (and simulation) under
the same image-finiteness hypothesis as the generic theorem.

The public `box` connective is the right adjoint of forward existential image:
it quantifies over predecessors.  It is therefore not part of the ordinary
forward Hennessy--Milner fragment.  A checked counterexample at the end shows
that quantifying over every concrete formula, including predecessor `box`, can
be strictly finer than forward bisimilarity.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Framework.ConcreteHennessyMilnerBridge

open Mettapedia.GSLT
open Mettapedia.GSLT.HennessyMilner
open Mettapedia.OSLF.Formula
open Mettapedia.OSLF.Framework.GSLTTypeSynthesis

universe uTerm

variable {S : GSLT.{uTerm}}

/-- The data selected by the concrete syntax: string-valued observations and
one unlabeled transition family. -/
structure ConcreteSystem (S : GSLT.{uTerm}) where
  observes : String → S.Term → Prop
  observes_resp : ∀ atom {left right},
    S.Equiv left right → (observes atom left ↔ observes atom right)
  act : S.Term → S.Term → Prop
  act_resp_left : ∀ {left right target},
    S.Equiv left right → act left target →
      ∃ target', act right target' ∧ S.Equiv target target'
  act_resp_right : ∀ {source target target'},
    act source target → S.Equiv target target' → act source target'

namespace ConcreteSystem

/-- The Hennessy--Milner system determined by the concrete observation and
transition interface. -/
def toHMLSystem (system : ConcreteSystem S) : System.{0, 0} S where
  Atom := String
  observes := system.observes
  observes_resp := system.observes_resp
  Label := Unit
  act := fun _ => system.act
  act_resp_left := system.act_resp_left
  act_resp_right := system.act_resp_right

end ConcreteSystem

variable (M : ConcreteSystem S)

/-! ## Concrete semantics on an arbitrary equation-aware system -/

/-- Interpret the public formula syntax using the labeled system's sole `Unit`
label.  Diamond follows forward transitions; box is the categorical
predecessor-universal right adjoint. -/
def satisfies : OSLFFormula → S.Term → Prop
  | .top, _ => True
  | .bot, _ => False
  | .atom atom, term => M.observes atom term
  | .and left right, term => satisfies left term ∧ satisfies right term
  | .or left right, term => satisfies left term ∨ satisfies right term
  | .imp left right, term => satisfies left term → satisfies right term
  | .dia body, source =>
      ∃ target, M.act source target ∧ satisfies body target
  | .box body, target =>
      ∀ source, M.act source target → satisfies body source

/-- Every concrete formula is invariant under the GSLT equations when its
atomic observations and labeled steps are invariant. -/
theorem satisfies_resp : ∀ (formula : OSLFFormula) {left right : S.Term},
    S.Equiv left right → (satisfies M formula left ↔ satisfies M formula right)
  | .top, _, _, _ => Iff.rfl
  | .bot, _, _, _ => Iff.rfl
  | .atom atom, _, _, equivalent => M.observes_resp atom equivalent
  | .and first second, _, _, equivalent =>
      and_congr (satisfies_resp first equivalent)
        (satisfies_resp second equivalent)
  | .or first second, _, _, equivalent =>
      or_congr (satisfies_resp first equivalent)
        (satisfies_resp second equivalent)
  | .imp first second, _, _, equivalent =>
      imp_congr (satisfies_resp first equivalent)
        (satisfies_resp second equivalent)
  | .dia body, _, _, equivalent => by
      constructor
      · rintro ⟨target, step, holds⟩
        obtain ⟨target', step', targetEquivalent⟩ :=
          M.act_resp_left equivalent step
        exact ⟨target', step',
          (satisfies_resp body targetEquivalent).mp holds⟩
      · rintro ⟨target, step, holds⟩
        obtain ⟨target', step', targetEquivalent⟩ := M.act_resp_left
          (S.equations.iseqv.symm equivalent) step
        exact ⟨target', step',
          (satisfies_resp body targetEquivalent).mp holds⟩
  | .box body, _, _, equivalent => by
      constructor
      · intro holds source step
        exact holds source
          (M.act_resp_right step (S.equations.iseqv.symm equivalent))
      · intro holds source step
        exact holds source (M.act_resp_right step equivalent)

/-- A concrete formula denotes an actual native type of the sole generated
GSLT OSLF. -/
def nativeType (formula : OSLFFormula) : GSLTNativeType S where
  sort := ()
  pred := invariantPredicate S (satisfies M formula)
    (by intro left right equivalent; exact satisfies_resp M formula equivalent)

@[simp]
theorem satisfies_nativeType_iff (formula : OSLFFormula) (term : S.Term) :
    (gsltOSLF S).satisfies (S := ()) term (nativeType M formula).pred ↔
      satisfies M formula term :=
  Iff.rfl

/-! ## Exact embedding of both Hennessy--Milner fragments -/

/-- Embed the full forward Hennessy--Milner fragment into the public syntax.
Negation is represented by implication into bottom. -/
def fromHML : Formula String Unit → OSLFFormula
  | .top => .top
  | .atom atom => .atom atom
  | .conj left right => .and (fromHML left) (fromHML right)
  | .neg body => .imp (fromHML body) .bot
  | .dia _ body => .dia (fromHML body)

/-- The embedding preserves and reflects satisfaction. -/
@[simp]
theorem satisfies_fromHML_iff
    (formula : Formula String Unit) (term : S.Term) :
    satisfies M (fromHML formula) term ↔
      M.toHMLSystem.sat formula term := by
  induction formula generalizing term with
  | top => rfl
  | atom atom => rfl
  | conj left right leftIH rightIH =>
      exact and_congr (leftIH term) (rightIH term)
  | neg body bodyIH =>
      exact not_congr (bodyIH term)
  | dia label body bodyIH =>
      cases label
      constructor
      · rintro ⟨target, step, holds⟩
        exact ⟨target, step, (bodyIH target).mp holds⟩
      · rintro ⟨target, step, holds⟩
        exact ⟨target, step, (bodyIH target).mpr holds⟩

/-- Embed the positive Hennessy--Milner fragment into the public syntax. -/
def fromPositiveHML : PosFormula String Unit → OSLFFormula
  | .top => .top
  | .bot => .bot
  | .atom atom => .atom atom
  | .conj left right => .and (fromPositiveHML left) (fromPositiveHML right)
  | .disj left right => .or (fromPositiveHML left) (fromPositiveHML right)
  | .dia _ body => .dia (fromPositiveHML body)

/-- The positive embedding preserves and reflects satisfaction. -/
@[simp]
theorem satisfies_fromPositiveHML_iff
    (formula : PosFormula String Unit) (term : S.Term) :
    satisfies M (fromPositiveHML formula) term ↔
      M.toHMLSystem.psat formula term := by
  induction formula generalizing term with
  | top => rfl
  | bot => rfl
  | atom atom => rfl
  | conj left right leftIH rightIH =>
      exact and_congr (leftIH term) (rightIH term)
  | disj left right leftIH rightIH =>
      exact or_congr (leftIH term) (rightIH term)
  | dia label body bodyIH =>
      cases label
      constructor
      · rintro ⟨target, step, holds⟩
        exact ⟨target, step, (bodyIH target).mp holds⟩
      · rintro ⟨target, step, holds⟩
        exact ⟨target, step, (bodyIH target).mpr holds⟩

/-- Concrete formulas in the translated full fragment characterize
bisimilarity. -/
theorem translated_equivalent_iff_bisimilar
    (finite : M.toHMLSystem.ImageFiniteModulo) (left right : S.Term) :
    (∀ formula : Formula String Unit,
      satisfies M (fromHML formula) left ↔
        satisfies M (fromHML formula) right) ↔
      M.toHMLSystem.Bisimilar left right := by
  constructor
  · intro same
    apply (M.toHMLSystem.logicallyEquivalent_iff_bisimilar finite left right).mp
    intro formula
    exact ((satisfies_fromHML_iff M formula left).symm.trans
      (same formula)).trans (satisfies_fromHML_iff M formula right)
  · intro bisimilar
    have same :=
      (M.toHMLSystem.logicallyEquivalent_iff_bisimilar finite left right).mpr
        bisimilar
    intro formula
    exact ((satisfies_fromHML_iff M formula left).trans
      (same formula)).trans (satisfies_fromHML_iff M formula right).symm

/-- The translated positive concrete fragment characterizes simulation. -/
theorem translated_preorder_iff_similar
    (finite : M.toHMLSystem.ImageFiniteModulo) (left right : S.Term) :
    (∀ formula : PosFormula String Unit,
      satisfies M (fromPositiveHML formula) left →
        satisfies M (fromPositiveHML formula) right) ↔
      M.toHMLSystem.Similar left right := by
  constructor
  · intro preserves
    apply (M.toHMLSystem.logicalPreorder_iff_similar finite left right).mp
    intro formula leftHolds
    exact (satisfies_fromPositiveHML_iff M formula right).mp
      (preserves formula
        ((satisfies_fromPositiveHML_iff M formula left).mpr leftHolds))
  · intro similar
    have preserves :=
      (M.toHMLSystem.logicalPreorder_iff_similar finite left right).mpr similar
    intro formula leftHolds
    exact (satisfies_fromPositiveHML_iff M formula right).mpr
      (preserves formula
        ((satisfies_fromPositiveHML_iff M formula left).mp leftHolds))

/-- The same adequacy result stated through actual generated native types. -/
theorem translated_nativeTypes_equivalent_iff_bisimilar
    (finite : M.toHMLSystem.ImageFiniteModulo) (left right : S.Term) :
    (∀ formula : Formula String Unit,
      (gsltOSLF S).satisfies (S := ()) left
          (nativeType M (fromHML formula)).pred ↔
        (gsltOSLF S).satisfies (S := ()) right
          (nativeType M (fromHML formula)).pred) ↔
      M.toHMLSystem.Bisimilar left right := by
  simpa only [satisfies_nativeType_iff] using
    translated_equivalent_iff_bisimilar M finite left right

/-! ## Negative boundary: predecessor box is additional structure -/

namespace PredecessorBoxCanary

inductive Term where
  | predecessor
  | left
  | right
  deriving DecidableEq

/-- One incoming edge reaches `left`; neither `left` nor `right` has an
outgoing edge. -/
abbrev theory : GSLT := equalityGSLT Term fun source target =>
  source = .predecessor ∧ target = .left

/-- No atomic observations: only forward behavior is visible to HML. -/
abbrev system : ConcreteSystem theory where
  observes := fun _ _ => False
  observes_resp := by
    intro atom leftTerm rightTerm equivalent
    cases equivalent
    rfl
  act := theory.Step
  act_resp_left := by
    intro leftTerm rightTerm target equivalent step
    cases equivalent
    exact ⟨target, step, rfl⟩
  act_resp_right := by
    intro source target target' step equivalent
    cases equivalent
    exact step

/-- The two deadlocked states are forward bisimilar. -/
theorem left_bisimilar_right : system.toHMLSystem.Bisimilar .left .right := by
  refine ⟨fun first second => first = .left ∧ second = .right,
    ⟨?_, ?_, ?_⟩, rfl, rfl⟩
  · rintro _ _ ⟨rfl, rfl⟩ _ target step
    change Term.left = Term.predecessor ∧ target = Term.left at step
    exact Term.noConfusion step.1
  · rintro _ _ ⟨rfl, rfl⟩ _ target step
    change Term.right = Term.predecessor ∧ target = Term.left at step
    exact Term.noConfusion step.1
  · rintro _ _ _ atom
    rfl

/-- The predecessor-universal box is false at `left`, because its predecessor
does not satisfy bottom. -/
theorem left_not_predecessor_box_bottom :
    ¬ satisfies system (.box .bot) .left := by
  intro holds
  exact holds .predecessor ⟨rfl, rfl⟩

/-- The same box is vacuously true at `right`, which has no predecessor. -/
theorem right_predecessor_box_bottom :
    satisfies system (.box .bot) .right := by
  intro source step
  change source = Term.predecessor ∧ Term.right = Term.left at step
  exact Term.noConfusion step.2

/-- Forward bisimilarity does not imply agreement on every concrete formula
when the predecessor modality is included. -/
theorem bisimilar_but_predecessor_box_distinguishes :
    system.toHMLSystem.Bisimilar .left .right ∧
      ¬ (satisfies system (.box .bot) .left ↔
        satisfies system (.box .bot) .right) := by
  refine ⟨left_bisimilar_right, ?_⟩
  intro agreement
  exact left_not_predecessor_box_bottom
    (agreement.mpr right_predecessor_box_bottom)

#print axioms left_bisimilar_right
#print axioms bisimilar_but_predecessor_box_distinguishes

end PredecessorBoxCanary

#print axioms satisfies_resp
#print axioms satisfies_fromHML_iff
#print axioms satisfies_fromPositiveHML_iff
#print axioms translated_equivalent_iff_bisimilar
#print axioms translated_preorder_iff_similar
#print axioms translated_nativeTypes_equivalent_iff_bisimilar

end Mettapedia.OSLF.Framework.ConcreteHennessyMilnerBridge
