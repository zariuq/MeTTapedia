import Mettapedia.Enactive.Razor
import Mathlib.Data.Set.Card

/-!
# Abstraction, semantic compression, and complexity confounding

This module audits Propositions 1--2 of Michael Timothy Bennett's *Is
Complexity an Illusion?* (2024) against the paper's literal definitions.

The 2024 paper requires a statement to contain at least one fact.  The abstract
`Aspect` order used elsewhere freely adjoins the empty aspect as a bottom; this
is necessary for exact recovery of Bennett's 2023 language, whose empty
hypothesis is explicit.  `Mature2024.Statement` records the exact nonempty
fragment rather than silently conflating the two presentations.

At the full vocabulary, every semantic behavior has a one-fact representative:
the fact is its own set of realizing worlds.  This proves the semantic core of
the subjectivity proposition.  It does not imply equality of principal
completion extensions.  Under the paper's literal `E_x = {y | x ⊆ y}`,
principal extensions are injective, and a two-fact aspect cannot have the same
extension as a singleton.  The negative theorem below makes this correction
explicit.

For finite abstraction layers, a concrete pair shows how lower syntactic size
and greater weakness can agree, which is the mathematical content needed for
the claimed confounding possibility.  The independent disagreement canary in
`Enactive.Razor` proves that the correlation is not universal.
-/

set_option autoImplicit false

namespace Mettapedia.Enactive.ComplexityIllusion

open Mettapedia.Enactive

universe uWorld

/-! ## The exact nonempty 2024 fragment -/

namespace Mature2024

variable {World : Type uWorld} {layer : AbstractionLayer World}

/-- Statements in the literal 2024 presentation are nonempty aspects.  The
ambient `Aspect` supplies their conservative order-completion with a bottom. -/
abbrev Statement (layer : AbstractionLayer World) :=
  {aspect : Aspect layer // aspect.facts.Nonempty}

/-- Forgetting nonemptiness embeds the paper's statements in the completed
aspect order without changing their facts or realizability. -/
def toAspect : Statement layer → Aspect layer := Subtype.val

@[simp]
theorem toAspect_injective : Function.Injective (@toAspect World layer) :=
  Subtype.val_injective

end Mature2024

/-! ## Proposition 1: valid semantic theorem and literal-extension boundary -/

namespace NoAbstraction

variable {World : Type uWorld}

/-- The canonical one-fact representative belongs to the exact nonempty 2024
fragment. -/
def semanticRepresentative
    (aspect : Aspect (AbstractionLayer.full World)) :
    Mature2024.Statement (AbstractionLayer.full World) :=
  ⟨Mettapedia.Enactive.NoAbstraction.semanticSingleton aspect, by
    simp [Mettapedia.Enactive.NoAbstraction.semanticSingleton]⟩

theorem semanticRepresentative_one_fact
    (aspect : Aspect (AbstractionLayer.full World)) :
    (semanticRepresentative aspect).val.facts = {aspect.semanticExtent} :=
  rfl

/-- Source-faithful semantic core of the subjectivity proposition: without a
vocabulary restriction, every behavior admits a one-fact description. -/
theorem semanticRepresentative_equivalent
    (aspect : Aspect (AbstractionLayer.full World)) :
    (semanticRepresentative aspect).val.SemanticallyEquivalent aspect :=
  Mettapedia.Enactive.NoAbstraction.semanticSingleton_equivalent aspect

theorem semanticRepresentative_ncard
    (aspect : Aspect (AbstractionLayer.full World)) :
    (semanticRepresentative aspect).val.facts.ncard = 1 := by
  rw [semanticRepresentative_one_fact]
  simp

/-- Any exact 2024 statement with finitely many facts has syntactic size at
least one, so the semantic representative attains the smallest possible
positive size. -/
theorem one_le_ncard_of_finite
    (statement : Mature2024.Statement (AbstractionLayer.full World))
    (finiteFacts : statement.val.facts.Finite) :
    1 ≤ statement.val.facts.ncard := by
  exact (Set.ncard_pos finiteFacts).mpr statement.property

theorem trueOnly_ne_redundantTop :
    Mettapedia.Enactive.NoAbstraction.trueOnly ≠
      Mettapedia.Enactive.NoAbstraction.redundantTop := by
  intro equal
  have falseMember : false ∈ Mettapedia.Enactive.NoAbstraction.trueOnly := by
    rw [equal]
    simp [Mettapedia.Enactive.NoAbstraction.redundantTop]
  simp [Mettapedia.Enactive.NoAbstraction.trueOnly] at falseMember

/-- Literal negative control for Proposition 1: the redundant two-fact aspect
has no singleton aspect with the same principal extension.  Thus semantic
equivalence, not syntactic `E_x` equality, is the valid collapse theorem. -/
theorem redundantTrueAspect_not_extensionEquivalent_singleton
    (candidate : Aspect (AbstractionLayer.full Bool))
    (fact : Fact Bool) (singletonFacts : candidate.facts = {fact}) :
    ¬ Completion.ExtensionEquivalent
      Mettapedia.Enactive.NoAbstraction.redundantTrueAspect candidate := by
  intro extensionEquivalent
  have aspectsEqual :
      Mettapedia.Enactive.NoAbstraction.redundantTrueAspect = candidate :=
    Completion.extensionEquivalent_iff_eq.mp extensionEquivalent
  have factsEqual := congrArg Aspect.facts aspectsEqual
  have trueMember :
      Mettapedia.Enactive.NoAbstraction.trueOnly ∈ candidate.facts := by
    rw [← factsEqual]
    simp [Mettapedia.Enactive.NoAbstraction.redundantTrueAspect]
  have topMember :
      Mettapedia.Enactive.NoAbstraction.redundantTop ∈ candidate.facts := by
    rw [← factsEqual]
    simp [Mettapedia.Enactive.NoAbstraction.redundantTrueAspect]
  have trueEquals : Mettapedia.Enactive.NoAbstraction.trueOnly = fact := by
    rw [singletonFacts] at trueMember
    exact Set.mem_singleton_iff.mp trueMember
  have topEquals : Mettapedia.Enactive.NoAbstraction.redundantTop = fact := by
    rw [singletonFacts] at topMember
    exact Set.mem_singleton_iff.mp topMember
  exact trueOnly_ne_redundantTop (trueEquals.trans topEquals.symm)

end NoAbstraction

/-! ## Proposition 2: finite abstraction can align the two rankings -/

namespace FiniteConfoundingCanary

open Mettapedia.Enactive.Finite
open Mettapedia.Enactive.Finite.Canary

/-- A realizable two-fact statement extending `trueStatement`. -/
def trueTopStatement : boolLayer.Statement :=
  ⟨{trueFact, topFact}, by decide⟩

theorem trueStatement_syntactically_simpler :
    trueStatement.val.card < trueTopStatement.val.card := by
  decide

theorem trueStatement_semantically_weaker :
    boolLayer.weakness trueTopStatement <
      boolLayer.weakness trueStatement := by
  decide

/-- Positive confounding witness: on this finite pair, the syntactically
simpler policy is also the one with more completions. -/
theorem simplicity_and_weakness_agree_on_pair :
    trueStatement.val.card < trueTopStatement.val.card ∧
      boolLayer.weakness trueTopStatement <
        boolLayer.weakness trueStatement :=
  ⟨trueStatement_syntactically_simpler,
    trueStatement_semantically_weaker⟩

/-- Negative control: finite abstraction only permits correlation; it does not
make completion weakness a function of code length. -/
theorem finite_abstraction_does_not_force_length_agreement :
    Razor.BennettOckhamCanary.weaknessRazor.atLeastAsGood
        .weakLong .strongShort ∧
      Razor.BennettOckhamCanary.codeLengthRazor.atLeastAsGood
        .strongShort .weakLong :=
  ⟨Razor.BennettOckhamCanary.weakness_prefers_weakLong.1,
    Razor.BennettOckhamCanary.codeLength_prefers_strongShort.1⟩

end FiniteConfoundingCanary

#print axioms NoAbstraction.semanticRepresentative_equivalent
#print axioms NoAbstraction.redundantTrueAspect_not_extensionEquivalent_singleton
#print axioms FiniteConfoundingCanary.simplicity_and_weakness_agree_on_pair
#print axioms FiniteConfoundingCanary.finite_abstraction_does_not_force_length_agreement

end Mettapedia.Enactive.ComplexityIllusion
