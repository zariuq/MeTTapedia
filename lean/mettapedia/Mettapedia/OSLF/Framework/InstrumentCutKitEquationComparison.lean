import Mettapedia.OSLF.Framework.InstrumentCutKitEquationCategory
import Mettapedia.OSLF.Framework.InstrumentCutKitCategoryObservations
import Mettapedia.GSLT.Logic.ReactiveSystemFunctor

/-!
# All-label kit transitions and bisimulation on the unit quotient

The independently generated equation category has an earned based hom
equivalence. The actual transported proper-plus-kit reaction family therefore
has complete transition and all-interface bisimulation comparisons, actual
RPOs and contextual congruence. Partial structural tests and fully opened
source reconstruction apply to the complete retained normal source readings.
This is the admitted unary-unit equation language, not arbitrary equations.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.OSLF.Framework.InstrumentCutContexts

open _root_.CategoryTheory
open Mettapedia.OSLF.SortedConstructors
open Mettapedia.OSLF.SortedConstructors.Padding
open Mettapedia.CategoryTheory.GroundPath
open Mettapedia.GSLT.RelativePushout
open Mettapedia.GSLT.RedexRelativeCongruence

universe u w

variable {Symbols : Type u} (arity : Symbols → Nat)

local instance instrumentCutKitEquationComparisonQuiver : Quiver (Srt Symbols arity) :=
  frameQuiver (signature arity)

def equationKitRules (Origins : Type w) (opened : InstrumentObservations.Policy Symbols)
    (proper : SourceRule arity → Prop) : ReactionRule (equationKitOrigin arity opened) → Prop :=
  pullbackRules (kitNormalization arity opened) (kitCategoryRules arity Origins opened proper)

theorem equationKit_step_iff (Origins : Type w) (opened : InstrumentObservations.Policy Symbols)
    (proper : SourceRule arity → Prop) {sourceInterface targetInterface : EquationKitObject arity opened}
    (label : sourceInterface ⟶ targetInterface) (source : equationKitOrigin arity opened ⟶ sourceInterface)
    (target : equationKitOrigin arity opened ⟶ targetInterface) :
    ActIPO (equationKitRules arity Origins opened proper) label source target ↔
      ActIPO (kitCategoryRules arity Origins opened proper) ((kitNormalization arity opened).map label)
        ((kitNormalization arity opened).map source) ((kitNormalization arity opened).map target) :=
  pullback_step_iff (kitNormalization arity opened) (origin := equationKitOrigin arity opened)
    (kitNormalization_objects arity opened)
    (kitCategoryRules arity Origins opened proper) label source target

theorem equationKit_bisimilar_iff (Origins : Type w) (opened : InstrumentObservations.Policy Symbols)
    (proper : SourceRule arity → Prop) {interface : EquationKitObject arity opened}
    (first second : equationKitOrigin arity opened ⟶ interface) :
    IPOBisimilar (equationKitRules arity Origins opened proper) first second ↔
      IPOBisimilar (kitCategoryRules arity Origins opened proper)
        ((kitNormalization arity opened).map first) ((kitNormalization arity opened).map second) :=
  pullback_bisimilar_iff (kitNormalization arity opened) (origin := equationKitOrigin arity opened)
    (kitNormalization_objects arity opened)
    (kitCategoryRules arity Origins opened proper) first second

theorem equationKit_origin_hasRelativePushouts {opened : InstrumentObservations.Policy Symbols}
    {first second : EquationKitObject arity opened}
    (left : equationKitOrigin arity opened ⟶ first) (right : equationKitOrigin arity opened ⟶ second) :
    HasRelativePushouts left right :=
  reflects_hasRelativePushouts (kitNormalization arity opened) (kitNormalization_objects arity opened)
    (kit_origin_hasRelativePushouts arity ((kitNormalization arity opened).map left)
      ((kitNormalization arity opened).map right))

theorem equationKit_context_congruence (Origins : Type w) (opened : InstrumentObservations.Policy Symbols)
    (proper : SourceRule arity → Prop) {first second : EquationKitObject arity opened}
    (left right : equationKitOrigin arity opened ⟶ first)
    (related : IPOBisimilar (equationKitRules arity Origins opened proper) left right) (context : first ⟶ second) :
    IPOBisimilar (equationKitRules arity Origins opened proper) (left ≫ context) (right ≫ context) :=
  ipoBisimilar_comp (fun _ agent rule _ => equationKit_origin_hasRelativePushouts arity agent rule.redex)
    related context

theorem equationKit_partial_tests (Origins : Type w) [Nonempty Origins]
    (kit : List Symbols) (proper : SourceRule arity → Prop)
    (first second : equationKitOrigin arity (fun constructor => constructor ∈ kit) ⟶
      equationKitInterface arity (fun constructor => constructor ∈ kit) .base)
    (firstSource secondSource : InstrumentObservations.Tree Symbols arity)
    (firstReadout : (kitNormalization arity (fun constructor => constructor ∈ kit)).map first =
      kitSource arity (fun constructor => constructor ∈ kit) firstSource)
    (secondReadout : (kitNormalization arity (fun constructor => constructor ∈ kit)).map second =
      kitSource arity (fun constructor => constructor ∈ kit) secondSource)
    (related : IPOBisimilar (equationKitRules arity Origins (fun constructor => constructor ∈ kit) proper) first second) :
    InstrumentObservations.LogicallyEquivalent (fun constructor => constructor ∈ kit) firstSource secondSource := by
  have normalRelated := (equationKit_bisimilar_iff arity Origins _ proper first second).mp related
  rw [firstReadout, secondReadout] at normalRelated
  exact kit_category_interactive_partial_tests arity Origins kit proper firstSource secondSource normalRelated

/-- Complete normal source readouts are explicit, and may be obtained from
arbitrary independently supplied raw padding representatives. -/
theorem equationKit_fullyOpened_iff (Origins : Type w) [Nonempty Origins]
    (opened : InstrumentObservations.Policy Symbols) (proper : SourceRule arity → Prop)
    (first second : equationKitOrigin arity opened ⟶ equationKitInterface arity opened .base)
    (firstSource secondSource : InstrumentObservations.Tree Symbols arity)
    (firstReadout : (kitNormalization arity opened).map first = kitSource arity opened firstSource)
    (secondReadout : (kitNormalization arity opened).map second = kitSource arity opened secondSource)
    (complete : FullyOpened arity opened firstSource) :
    IPOBisimilar (equationKitRules arity Origins opened proper) first second ↔ firstSource = secondSource := by
  have comparison := equationKit_bisimilar_iff arity Origins opened proper first second
  rw [firstReadout, secondReadout] at comparison
  exact comparison.trans (kit_category_interactive_iff_equal arity Origins opened proper
    firstSource secondSource complete)

end Mettapedia.OSLF.Framework.InstrumentCutContexts
