import Mettapedia.Logic.FinitaryRuleSystem.RuleHomomorphism

/-!
# Comparison preorders for finitary rule systems

There is no unqualified "weakest rule system."  This file packages three
different comparison relations, each induced by an explicitly named class of
translations:

* preservation of closed derivability;
* preservation and reflection of closed derivability;
* strict preservation of primitive rule instances.

The relations have the same direction convention: `host` simulates `guest`
when a translation runs from `guest` to `host`.  No relation is called
proof-theoretic interpretability; additional syntax and coding laws are needed
to earn that stronger name for arithmetic theories.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.FinitaryRuleSystem

universe u

/-- A finitary rule system bundled with its judgment carrier. -/
structure System : Type (u + 1) where
  Judgment : Type u
  rules : List Judgment → Judgment → Prop

/-- `host` simulates the closed derivability of `guest`. -/
def ClosedDerivabilitySimulates (host guest : System.{u}) : Prop :=
  Nonempty (DerivabilityTranslation guest.rules host.rules)

/-- `host` and `guest` agree on every translated closed theorem. -/
def ConservativelyDerivabilitySimulates (host guest : System.{u}) : Prop :=
  ∃ translation : DerivabilityTranslation guest.rules host.rules,
    translation.Conservative

/-- `host` simulates every primitive rule of `guest` strictly. -/
def StrictRuleSimulates (host guest : System.{u}) : Prop :=
  Nonempty (RuleHomomorphism guest.rules host.rules)

theorem closedDerivabilitySimulates_refl (system : System.{u}) :
    ClosedDerivabilitySimulates system system :=
  ⟨DerivabilityTranslation.id system.rules⟩

theorem closedDerivabilitySimulates_trans {first second third : System.{u}}
    (secondFirst : ClosedDerivabilitySimulates second first)
    (thirdSecond : ClosedDerivabilitySimulates third second) :
    ClosedDerivabilitySimulates third first := by
  rcases secondFirst with ⟨earlier⟩
  rcases thirdSecond with ⟨later⟩
  exact ⟨earlier.comp later⟩

theorem conservativelyDerivabilitySimulates_refl (system : System.{u}) :
    ConservativelyDerivabilitySimulates system system :=
  ⟨DerivabilityTranslation.id system.rules,
    DerivabilityTranslation.conservative_id system.rules⟩

theorem conservativelyDerivabilitySimulates_trans
    {first second third : System.{u}}
    (secondFirst : ConservativelyDerivabilitySimulates second first)
    (thirdSecond : ConservativelyDerivabilitySimulates third second) :
    ConservativelyDerivabilitySimulates third first := by
  rcases secondFirst with ⟨earlier, earlierConservative⟩
  rcases thirdSecond with ⟨later, laterConservative⟩
  exact ⟨earlier.comp later,
    earlierConservative.comp laterConservative⟩

theorem strictRuleSimulates_refl (system : System.{u}) :
    StrictRuleSimulates system system :=
  ⟨RuleHomomorphism.id system.rules⟩

theorem strictRuleSimulates_trans {first second third : System.{u}}
    (secondFirst : StrictRuleSimulates second first)
    (thirdSecond : StrictRuleSimulates third second) :
    StrictRuleSimulates third first := by
  rcases secondFirst with ⟨earlier⟩
  rcases thirdSecond with ⟨later⟩
  exact ⟨earlier.comp later⟩

/-- Primitive-rule simulation implies closed-derivability simulation. -/
theorem StrictRuleSimulates.toClosedDerivability
    {host guest : System.{u}} :
    StrictRuleSimulates host guest → ClosedDerivabilitySimulates host guest := by
  rintro ⟨homomorphism⟩
  exact ⟨homomorphism.toDerivabilityTranslation⟩

/-- Conservative simulation forgets to one-way closed-derivability
simulation. -/
theorem ConservativelyDerivabilitySimulates.toClosedDerivability
    {host guest : System.{u}} :
    ConservativelyDerivabilitySimulates host guest →
      ClosedDerivabilitySimulates host guest := by
  rintro ⟨translation, _conservative⟩
  exact ⟨translation⟩

/-! ## Explicit preorder carriers -/

/-- Rule systems ordered only by preservation of closed theorems. -/
def ClosedDerivabilityOrder := System.{u}

namespace ClosedDerivabilityOrder

instance : Preorder (ClosedDerivabilityOrder.{u}) where
  le guest host := ClosedDerivabilitySimulates host guest
  le_refl := closedDerivabilitySimulates_refl
  le_trans _first _second _third := closedDerivabilitySimulates_trans

end ClosedDerivabilityOrder

/-- Rule systems ordered by preservation and reflection of translated closed
theorems. -/
def ConservativeDerivabilityOrder := System.{u}

namespace ConservativeDerivabilityOrder

instance : Preorder (ConservativeDerivabilityOrder.{u}) where
  le guest host := ConservativelyDerivabilitySimulates host guest
  le_refl := conservativelyDerivabilitySimulates_refl
  le_trans _first _second _third :=
    conservativelyDerivabilitySimulates_trans

end ConservativeDerivabilityOrder

/-- Rule systems ordered by strict primitive-rule homomorphisms. -/
def StrictRuleOrder := System.{u}

namespace StrictRuleOrder

instance : Preorder (StrictRuleOrder.{u}) where
  le guest host := StrictRuleSimulates host guest
  le_refl := strictRuleSimulates_refl
  le_trans _first _second _third := strictRuleSimulates_trans

end StrictRuleOrder

end Mettapedia.Logic.FinitaryRuleSystem
