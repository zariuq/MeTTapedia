import Mettapedia.TypeTheory.BubbleBetaTyping
import Mettapedia.TypeTheory.KnowledgePeeling

/-!
# What typing asks of a bubble

A bubble declares steps and uses them as its conversion. `TypingAdmission` collects what the
typing judgment, with the conversion rule at every node, needs from the declared steps:

* they are stable under substitution and under shifting;
* convertible products have convertible domains and convertible codomains;
* every rule keeps the type of its left side.

From these five facts the judgment has the properties gathered in the namespace
`TypingAdmission`: types are unique up to conversion (`unique`), every ask of a derivation is
answered by a run of the conversion step (`asks_are_runs`), weakening (`weaken`), substitution
(`subst`), subject reduction (`reduces`), the β step keeps types (`beta`), and a frame that knows
a definition has the conversion and the unique types of its instance (`definition_conversion`,
`definition_unique`).

`TypingAdmission.of_confluent` gives the two facts about products from confluence, for rules that
do not rewrite a product at the root. Confluence is used by typing for nothing else, and
termination of the rules is used by none of these properties: it is needed to decide conversion.

## Controls

* `Controls.arith_admitted`: the recursion equations of addition are admitted.
* `Controls.zeroToNat_not_admitted`: the rule `0 ↦ nat` is not.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.BubbleTypingAdmission

open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
open Mettapedia.TypeTheory.BubbleConversion
open Mettapedia.TypeTheory.BubbleTypingInside
open Mettapedia.TypeTheory.BubbleTypingAlgorithmic
open Mettapedia.TypeTheory.BubbleSubjectReduction
open Mettapedia.TypeTheory.BubbleBetaTyping
open Mettapedia.TypeTheory.KnowledgeFramesCore
open Mettapedia.TypeTheory.KnowledgeUnderBinders
open Mettapedia.TypeTheory.KnowledgeSubstitution
open Mettapedia.TypeTheory.KnowledgeSolvedForm
open Mettapedia.TypeTheory.KnowledgePeeling
open Mettapedia.Logic.HOL
open Mettapedia.Logic.HOL.Embedding.SimpleSliceOfDependent
open Mettapedia.Logic.Relation (Confluent)
open Expr

universe u v

section Core

variable {Base : Type u} {Const : Ty Base → Type v}

/-- What the typing judgment needs from the declared steps of a bubble. -/
structure TypingAdmission (rules : Expr Base Const → Expr Base Const → Prop) : Prop where
  /-- The rules are stable under substitution. -/
  substStable : SubstitutionStable rules
  /-- The rules are stable under shifting. -/
  shiftStable : ShiftStable rules
  /-- Convertible products have convertible codomains. -/
  codomains : PiCodomainInjective rules
  /-- Convertible products have convertible domains. -/
  domains : PiDomainInjective rules
  /-- Every rule keeps the type of its left side. -/
  preserves : PreservesTypes rules

/-- In a confluent bubble with no rule that rewrites a product at the root, convertible products
have convertible domains. -/
theorem piDomainInjective_of_confluent {rules : Expr Base Const → Expr Base Const → Prop}
    (confluent : Confluent (Rewrite rules))
    (noPiRule : ∀ A B right, ¬ rules (Expr.pi A B) right) : PiDomainInjective rules := by
  intro A B A' B' converted
  obtain ⟨common, fromLeft, fromRight⟩ := confluent.eqvGen_iff_join.mp converted
  obtain ⟨A₁, _, rfl, toA, _⟩ := reduct_of_pi noPiRule fromLeft
  obtain ⟨A₂, _, same, toA', _⟩ := reduct_of_pi noPiRule fromRight
  obtain ⟨rfl, _⟩ := Expr.pi.inj same
  exact Relation.EqvGen.trans _ _ _ (convertible_of_reduces toA)
    (Relation.EqvGen.symm _ _ (convertible_of_reduces toA'))

/-- **Confluence gives the two facts about products.** A confluent rule set that is stable under
substitution and shifting, does not rewrite a product at the root and keeps types is admitted. -/
theorem TypingAdmission.of_confluent {rules : Expr Base Const → Expr Base Const → Prop}
    (substStable : SubstitutionStable rules) (shiftStable : ShiftStable rules)
    (confluent : Confluent (Rewrite rules))
    (noPiRule : ∀ A B right, ¬ rules (Expr.pi A B) right) (preserves : PreservesTypes rules) :
    TypingAdmission rules where
  substStable := substStable
  shiftStable := shiftStable
  codomains := piCodomainInjective_of_confluent confluent noPiRule
  domains := piDomainInjective_of_confluent confluent noPiRule
  preserves := preserves

namespace TypingAdmission

variable {rules : Expr Base Const → Expr Base Const → Prop}

/-- The conversion of an admitted bubble is coherent. -/
theorem coherent (admitted : TypingAdmission rules) : Coherent (Convertible rules) :=
  coherent_convertible admitted.substStable admitted.codomains

/-- **Types are unique up to conversion.** -/
theorem unique (admitted : TypingAdmission rules) {Γ : List (Expr Base Const)}
    {e A B : Expr Base Const} (first : HasTypeInside rules Γ e A)
    (second : HasTypeInside rules Γ e B) : Convertible rules A B :=
  typed_unique admitted.coherent first second

/-- **Every ask of a typing is answered by a run of the conversion step.** -/
theorem asks_are_runs (admitted : TypingAdmission rules) {Γ : List (Expr Base Const)}
    {e T : Expr Base Const} :
    HasTypeInside rules Γ e T ↔ ∃ A, Synth (Reaches rules) Γ e A ∧ Reaches rules A T :=
  hasTypeInside_iff_synth_run admitted.coherent

/-- **Weakening.** -/
theorem weaken (admitted : TypingAdmission rules) (D : Expr Base Const)
    {Γ : List (Expr Base Const)} {e A : Expr Base Const} (typed : HasTypeInside rules Γ e A)
    (Δ Θ : List (Expr Base Const)) (split : Γ = Δ ++ Θ) :
    HasTypeInside rules (shiftCtx Δ ++ D :: Θ) (shiftAt Δ.length e) (shiftAt Δ.length A) :=
  typedKnowing_discharge admitted.shiftStable
    (typedKnowing_weaken admitted.shiftStable D (typedKnowing_of_inside typed []) Δ Θ split)
    (fun _ member => absurd member List.not_mem_nil)

/-- **Substitution.** -/
theorem subst (admitted : TypingAdmission rules) {Γ : List (Expr Base Const)}
    {s C e A : Expr Base Const} (typedS : HasTypeInside rules Γ s C)
    (typed : HasTypeInside rules (C :: Γ) e A) :
    HasTypeInside rules Γ (substAt 0 s e) (substAt 0 s A) :=
  hasTypeInside_subst admitted.substStable admitted.shiftStable typedS typed

/-- **Subject reduction**: a typed term keeps its type along any computation by the rules. -/
theorem reduces (admitted : TypingAdmission rules) {Γ : List (Expr Base Const)}
    {e e' A : Expr Base Const} (typed : HasTypeInside rules Γ e A)
    (reduced : Relation.ReflTransGen (Rewrite rules) e e') : HasTypeInside rules Γ e' A :=
  subject_reduction_star admitted.shiftStable admitted.preserves typed reduced

/-- **The β step keeps types.** -/
theorem beta (admitted : TypingAdmission rules) {Γ : List (Expr Base Const)}
    {A b a T : Expr Base Const} (typed : HasTypeInside rules Γ (Expr.app (Expr.lam A b) a) T) :
    HasTypeInside rules Γ (substAt 0 a b) T :=
  beta_keeps_type admitted.substStable admitted.shiftStable admitted.coherent admitted.domains
    typed

/-- **A definition in a frame is eliminated by instantiation**, whatever else the frame knows. -/
theorem definition_conversion (admitted : TypingAdmission rules) (k : Nat)
    (u : Expr Base Const) (K' : EquationStore (Expr Base Const)) {A B : Expr Base Const} :
    ConvertibleKnowing rules ((bvar k, shiftN (k + 1) u) :: K') A B ↔
      ConvertibleKnowing rules (substStore k u K') (substAt k u A) (substAt k u B) :=
  peel_definition_iff admitted.substStable admitted.shiftStable k u K'

/-- **At the frame of a definition, types are unique up to the frame's conversion.** -/
theorem definition_unique (admitted : TypingAdmission rules) {Θ : List (Expr Base Const)}
    {u C : Expr Base Const} (typedU : HasTypeInside rules Θ u C) (Δ : List (Expr Base Const))
    {Γ : List (Expr Base Const)} (split : Γ = Δ ++ C :: Θ) {e A B : Expr Base Const}
    (first : TypedKnowing rules [(bvar Δ.length, shiftN (Δ.length + 1) u)] Γ e A)
    (second : TypedKnowing rules [(bvar Δ.length, shiftN (Δ.length + 1) u)] Γ e B) :
    ConvertibleKnowing rules [(bvar Δ.length, shiftN (Δ.length + 1) u)] A B :=
  typedKnowing_unique_solved admitted.substStable admitted.shiftStable admitted.coherent typedU Δ
    split first second

end TypingAdmission

end Core

/-! ## Controls -/

namespace Controls

open Mettapedia.TypeTheory.BubbleConversion.Arith
open Mettapedia.TypeTheory.BubbleTypingAlgorithmic.Controls
open Mettapedia.TypeTheory.BubbleSubjectReduction.Controls
open Mettapedia.TypeTheory.KnowledgeUnderBinders.Controls

/-- **The recursion equations of addition are admitted.** -/
theorem arith_admitted : TypingAdmission Rule where
  substStable := rule_stable
  shiftStable := rule_shiftStable
  codomains := arith_piCodomainInjective false
  domains := fun _ _ _ _ converted => arith_piDomain converted
  preserves := rule_preservesTypes

/-- **The rule `0 ↦ nat` is not admitted**: it does not keep types. -/
theorem zeroToNat_not_admitted : ¬ TypingAdmission ZeroToNat :=
  fun admitted => zeroToNat_not_preserving admitted.preserves

end Controls

/-! ## Axiom audit -/

#print axioms TypingAdmission.of_confluent
#print axioms TypingAdmission.unique
#print axioms TypingAdmission.asks_are_runs
#print axioms TypingAdmission.weaken
#print axioms TypingAdmission.subst
#print axioms TypingAdmission.reduces
#print axioms TypingAdmission.beta
#print axioms TypingAdmission.definition_conversion
#print axioms TypingAdmission.definition_unique
#print axioms Controls.arith_admitted
#print axioms Controls.zeroToNat_not_admitted

end Mettapedia.TypeTheory.BubbleTypingAdmission
