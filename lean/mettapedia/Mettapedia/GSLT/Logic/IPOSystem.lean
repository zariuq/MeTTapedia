import Mettapedia.GSLT.Logic.RelativePushout

/-!
# Interface-indexed redex-relative transitions

Agents are arrows from a fixed origin. A transition retains its reaction
rule, reaction context and leastness witness. Bisimulation matches the same
literal context label in both directions at the target interface.

These are the foundational reactive-system declarations; contextual
congruence is derived separately from relative pushouts and local replay.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.RedexRelativeCongruence

open CategoryTheory
open Mettapedia.GSLT.RelativePushout

universe v u

variable {C : Type u} [Category.{v} C] {origin : C}

/-- A redex and its reactum at one interface, from the fixed origin. -/
structure ReactionRule (origin : C) where
  /-- The rule's result interface. -/
  codomain : C
  /-- What the rule consumes. -/
  redex : origin ⟶ codomain
  /-- And what it leaves, at the same interface. -/
  reactum : origin ⟶ codomain

/-- A redex-relative labelled transition. The label changes the agent's
interface, and an idem pushout makes it least for the exposed redex. -/
def ActIPO (rules : ReactionRule origin → Prop) {sourceInterface targetInterface : C}
    (label : sourceInterface ⟶ targetInterface)
    (agent : origin ⟶ sourceInterface) (target : origin ⟶ targetInterface) : Prop :=
  ∃ rule : ReactionRule origin, rules rule ∧
    ∃ reaction : rule.codomain ⟶ targetInterface,
    ∃ square : agent ≫ label = rule.redex ≫ reaction,
      IsIdemPushout agent rule.redex label reaction square ∧
        target = rule.reactum ≫ reaction

/-- A bisimulation family compares agents at the same interface and matches
transitions at their resulting interface. Labels are compared literally. -/
def IsIPOBisimulation (rules : ReactionRule origin → Prop)
    (relation : (interface : C) → (origin ⟶ interface) → (origin ⟶ interface) → Prop) :
    Prop :=
  ∀ {interface : C} (left right : origin ⟶ interface), relation interface left right →
    (∀ {nextInterface : C} (label : interface ⟶ nextInterface) next,
      ActIPO rules label left next →
        ∃ matched, ActIPO rules label right matched ∧ relation nextInterface next matched) ∧
    (∀ {nextInterface : C} (label : interface ⟶ nextInterface) next,
      ActIPO rules label right next →
        ∃ matched, ActIPO rules label left matched ∧ relation nextInterface matched next)

/-- Bisimilarity at one interface, witnessed by a family at every interface. -/
def IPOBisimilar (rules : ReactionRule origin → Prop) {interface : C}
    (left right : origin ⟶ interface) : Prop :=
  ∃ relation, IsIPOBisimulation rules relation ∧ relation interface left right

end Mettapedia.GSLT.RedexRelativeCongruence
