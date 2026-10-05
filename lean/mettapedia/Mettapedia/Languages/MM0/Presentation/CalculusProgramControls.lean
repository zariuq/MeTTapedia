import Mettapedia.Languages.MM0.Presentation.CalculusProgramContract
import Mettapedia.Languages.MM0.Presentation.CalculusControls

/-!
# Controls for the checker of the MM0 calculus

The theory with a provable sort, a constant and an axiom asserting it, and the
same theory without the axiom. The checker accepts the translated witness that
applies the axiom and a local hypothesis. It refuses the same witness claiming
another conclusion, the witness in the theory without the axiom, a certificate
whose instance leaf claims a hypothesis the axiom does not have, a node naming
no rule, a node whose arguments are metavariables, and a node with a child its
rule does not have.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MM0.Presentation.ComputationalCalculus.Controls

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.GSLT.LanguageDef.InferenceComputedLeaves
open Mettapedia.GSLT.LanguageDef.DeterministicEquations
open Mettapedia.Languages.MM0.Kernel
open Calculus
open Calculus.Controls (withAxiom withoutAxiom axiomDecl constant axiom_instance nothing_derivable)

local notation "P" => calculusProgram
local notation "H" => dataEqualityHost

/-- The witness applying the axiom. -/
def axiomWitness : ProofWitness := .theoremApp 0 [] []

/-- **Positive control**: the translated witness applying the axiom is
accepted, whatever fuel its leaves name. -/
theorem axiom_accepted (fuel : Nat) :
    Applies P H "mm0:certificate"
      (request withAxiom (derivesJ [] [] constant) (Witness.translate withAxiom fuel [] [] axiomWitness))
      (.sym "True") :=
  (witness_accepted_iff withAxiom fuel [] [] axiomWitness constant).mp
    (.theoremApp rfl axiom_instance .nil)

/-- **Positive control**: a local hypothesis is accepted. -/
theorem hypothesis_accepted (fuel : Nat) :
    Applies P H "mm0:certificate"
      (request withoutAxiom (derivesJ [] [constant] constant)
        (Witness.translate withoutAxiom fuel [] [constant] (.hyp 0)))
      (.sym "True") :=
  (witness_accepted_iff withoutAxiom fuel [] [constant] (.hyp 0) constant).mp (.hyp rfl)

/-- **Negative control**: the witness applying the axiom, claiming another
conclusion, is refused. -/
theorem wrong_conclusion_refused (fuel : Nat) :
    Applies P H "mm0:certificate"
      (request withAxiom (derivesJ [] [] (.term 1)) (Witness.translate withAxiom fuel [] [] axiomWitness))
      (.sym "False") :=
  (witness_refused_iff withAxiom fuel [] [] axiomWitness (.term 1)).mp fun checked =>
    absurd ((ProofWitness.proof_eq_some_iff _ _ _ _ _ _ _).mpr checked) (by decide +kernel)

/-- **Negative control**: without the axiom, the same witness is refused. -/
theorem missing_axiom_refused (fuel : Nat) :
    Applies P H "mm0:certificate"
      (request withoutAxiom (derivesJ [] [] constant)
        (Witness.translate withoutAxiom fuel [] [] axiomWitness))
      (.sym "False") :=
  (witness_refused_iff withoutAxiom fuel [] [] axiomWitness constant).mp fun checked =>
    nothing_derivable checked.derives

/-- The certificate applying the axiom whose instance leaf claims one
hypothesis the axiom does not have, proved by the axiom itself. -/
def wrongInstance (fuel : Nat) : Witness.Certificate withAxiom :=
  Witness.ruleNode withAxiom rTheorem
    [contextPattern [], expressionsPattern [], indexPattern 0, theoremPattern axiomDecl,
      expressionsPattern [], expressionsPattern [constant], expressionPattern constant]
    [.computed ⟨Operation.lookup, ⟨(0 : Nat), axiomDecl, fuel⟩⟩,
      .computed ⟨Operation.instantiate, ⟨(([] : Context), axiomDecl, ([] : List Preterm)),
        (⟨[constant], constant⟩ : TheoremInstance), fuel⟩⟩,
      Witness.translateAll withAxiom fuel [] [] [axiomWitness] [constant]]

/-- **Negative control**: a wrong instance leaf is refused, whatever its
fuel. -/
theorem wrong_instance_refused (fuel : Nat) :
    Applies P H "mm0:certificate" (request withAxiom (derivesJ [] [] constant) (wrongInstance fuel))
      (.sym "False") := by
  rw [certificate_returns_iff]
  cases accepted : check formMM0 (settledEvaluate withAxiom) (derivesJ [] [] constant) (wrongInstance fuel)
  · rfl
  · exfalso
    obtain ⟨-, -, -, children⟩ :=
      (Witness.check_node_iff _ (r := rTheorem) (by simp [rules]) _ _ _).mp accepted
    rw [(inst_rTheorem _ _ _ _ _ _ _).1] at children
    simp only [checkChildren, Bool.and_eq_true] at children
    have leaf := children.2.1
    rw [check_computed] at leaf
    simp only [settled, Bool.and_eq_true, decide_eq_true_eq] at leaf
    exact absurd leaf.1 (by decide)

/-- A node naming no rule of the calculus. -/
def unknownRuleNode : Witness.Certificate withAxiom := .node ⟨⟨"mm0-unknown"⟩, []⟩ []

/-- **Negative control**: a node naming no rule is refused, for every goal. -/
theorem unknown_rule_refused (goal : Pattern) :
    Applies P H "mm0:certificate" (request withAxiom goal unknownRuleNode) (.sym "False") := by
  rw [certificate_returns_iff, unknownRuleNode, check_node_verdict]
  rfl

/-- An empty list of derivations claimed with metavariables for the context
and the hypotheses. -/
def metavariableNode : Witness.Certificate withAxiom :=
  .node ⟨⟨rAllNil.id⟩, [.fvar "c", .fvar "h"]⟩ []

/-- **Negative control**: metavariables are not valid arguments, even where
the conclusion they give is the goal. -/
theorem metavariable_arguments_refused :
    Applies P H "mm0:certificate"
      (request withAxiom (jAll (.fvar "c") (.fvar "h") (listOf nilOf)) metavariableNode) (.sym "False") := by
  rw [certificate_returns_iff, metavariableNode, check_node_verdict]
  rfl

/-- An empty list of derivations with a child its rule does not have. -/
def extraChild : Witness.Certificate withAxiom :=
  Witness.ruleNode withAxiom rAllNil [contextPattern [], expressionsPattern []]
    [Witness.translate withAxiom 0 [] [] axiomWitness]

/-- **Negative control**: a child the rule does not have is refused. -/
theorem extra_child_refused :
    Applies P H "mm0:certificate" (request withAxiom (allJ [] [] []) extraChild) (.sym "False") := by
  rw [certificate_returns_iff]
  cases accepted : check formMM0 (settledEvaluate withAxiom) (allJ [] [] []) extraChild
  · rfl
  · exfalso
    obtain ⟨-, -, -, children⟩ :=
      (Witness.check_node_iff _ (r := rAllNil) (by simp [rules]) _ _ _).mp accepted
    rw [(inst_rAllNil _ _).1] at children
    simp [checkChildren] at children

end Mettapedia.Languages.MM0.Presentation.ComputationalCalculus.Controls
