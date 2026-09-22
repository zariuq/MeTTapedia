import Mettapedia.GSLT.LanguageDef.CertificateGSLTDisplayedDerivations
import Mettapedia.GSLT.LanguageDef.CertificateGSLTOpenSearchMachine

/-!
# The ordered occurrence ledger as a presheaf

An open proof uses an ordered list of context positions. A contextual proof
substitution sends each such position to the ordered uses of its image proof.
The list `flatMap` law makes this action functorial over the existing
classifying context category. Forgetting an actual proof to its usage list
is then a natural transformation, not a context-insensitive count.

This is the resource observation of the proof-relevant derivation presheaf.
It does not assert a linear Prime calculus or an isomorphism between proofs
and their ledgers.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.CertificateGSLT

open CategoryTheory
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.Computability.ComputationalTrinity
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open OpenSearchMachine

/-- Reindex an ordered source ledger by replacing each source premise use
with the ordered premise uses of its image derivation. -/
def mapLedger
    {definition : ValidatedCalculusLanguageDef}
    {sourceContext targetContext : List Pattern}
    (environment : OpenDerivationList definition targetContext sourceContext)
    (ledger : List (Fin sourceContext.length)) :
    List (Fin targetContext.length) :=
  ledger.flatMap fun index => holeOccurrences (environment.get index)

@[simp] theorem mapLedger_id
    (definition : ValidatedCalculusLanguageDef)
    (context : List Pattern)
    (ledger : List (Fin context.length)) :
    mapLedger (assumptionEnvironment definition context) ledger = ledger := by
  simp [mapLedger, assumptionEnvironment, OpenDerivationList.get_ofFn,
    holeOccurrences]

/-- Ledger reindexing composes in the same contravariant order as proof
substitution. -/
theorem mapLedger_comp
    {definition : ValidatedCalculusLanguageDef}
    {firstContext secondContext thirdContext : List Pattern}
    (first : OpenDerivationList definition secondContext firstContext)
    (second : OpenDerivationList definition thirdContext secondContext)
    (ledger : List (Fin firstContext.length)) :
    mapLedger (first.bind second) ledger =
      mapLedger second (mapLedger first ledger) := by
  simp only [mapLedger, OpenDerivationList.get_bind,
    holeOccurrences_bind]
  exact List.flatMap_assoc.symm

/-- The presheaf of exact ordered premise-use ledgers. Equal judgment labels
at different positions remain different elements of its fibres. -/
def ledgerFace (definition : ValidatedCalculusLanguageDef) :
    Face (ClassifyingContext definition) where
  obj context := List (Fin context.unop.judgments.length)
  map substitution := TypeCat.ofHom fun ledger =>
    mapLedger substitution.unop ledger
  map_id context := by
    apply ConcreteCategory.hom_ext
    intro ledger
    exact mapLedger_id definition context.unop.judgments ledger
  map_comp first second := by
    apply ConcreteCategory.hom_ext
    intro ledger
    exact mapLedger_comp first.unop second.unop ledger

/-- Forget a proof-bearing contextual answer to its ordered occurrence
ledger. Naturality is precisely the proved substitution/flatMap law. -/
def derivationToLedger (definition : ValidatedCalculusLanguageDef) :
    derivationTotalFace definition ⟶ ledgerFace definition where
  app _ := TypeCat.ofHom fun answer => holeOccurrences answer.2
  naturality := by
    intro source target substitution
    apply ConcreteCategory.hom_ext
    rintro ⟨goal, derivation⟩
    exact holeOccurrences_bind derivation substitution.unop

/-- The paired observation keeps both the unchanged goal and the reindexed
ordered ledger. It is the base for exact-ledger proof fibres. -/
def goalLedgerFace (definition : ValidatedCalculusLanguageDef) :
    Face (ClassifyingContext definition) where
  obj context := Pattern × List (Fin context.unop.judgments.length)
  map substitution := TypeCat.ofHom fun answer =>
    (answer.1, mapLedger substitution.unop answer.2)
  map_id context := by
    apply ConcreteCategory.hom_ext
    rintro ⟨goal, ledger⟩
    exact congrArg (fun uses => (goal, uses))
      (mapLedger_id definition context.unop.judgments ledger)
  map_comp first second := by
    apply ConcreteCategory.hom_ext
    rintro ⟨goal, ledger⟩
    exact congrArg (fun uses => (goal, uses))
      (mapLedger_comp first.unop second.unop ledger)

/-- A proof-bearing answer observes its goal and exact ordered use list
jointly. Naturality follows from real proof substitution, not re-search. -/
def derivationToGoalLedger
    (definition : ValidatedCalculusLanguageDef) :
    derivationTotalFace definition ⟶ goalLedgerFace definition where
  app _ := TypeCat.ofHom fun answer =>
    (answer.1, holeOccurrences answer.2)
  naturality := by
    intro source target substitution
    apply ConcreteCategory.hom_ext
    rintro ⟨goal, derivation⟩
    exact congrArg (fun uses => (goal, uses))
      (holeOccurrences_bind derivation substitution.unop)

@[simp] theorem derivationToLedger_apply
    (definition : ValidatedCalculusLanguageDef)
    (context : (ClassifyingContext definition)ᵒᵖ)
    (answer : (derivationTotalFace definition).obj context) :
    (derivationToLedger definition).app context answer =
      holeOccurrences answer.2 := rfl

private def leftDuplicateAnswer
    (definition : ValidatedCalculusLanguageDef) (goal : Pattern) :
    (derivationTotalFace definition).obj
      (Opposite.op (⟨[goal, goal]⟩ : ClassifyingContext definition)) :=
  ⟨goal, OpenDerivation.assumption (definition := definition)
    (context := [goal, goal]) (0 : Fin 2)⟩

private def rightDuplicateAnswer
    (definition : ValidatedCalculusLanguageDef) (goal : Pattern) :
    (derivationTotalFace definition).obj
      (Opposite.op (⟨[goal, goal]⟩ : ClassifyingContext definition)) :=
  ⟨goal, OpenDerivation.assumption (definition := definition)
    (context := [goal, goal]) (1 : Fin 2)⟩

/-- Two answers with the same observed goal remain distinct at the ledger
observation because they use different equal-labeled premise positions. -/
theorem duplicateAnswers_sameGoal_distinctLedger
    (definition : ValidatedCalculusLanguageDef) (goal : Pattern) :
    (derivationToGoal definition).app _
        (leftDuplicateAnswer definition goal) =
      (derivationToGoal definition).app _
        (rightDuplicateAnswer definition goal) ∧
    (derivationToLedger definition).app _
        (leftDuplicateAnswer definition goal) ≠
      (derivationToLedger definition).app _
        (rightDuplicateAnswer definition goal) := by
  constructor
  · rfl
  · intro same
    change [(0 : Fin 2)] = [(1 : Fin 2)] at same
    have positions := List.singleton_injective same
    exact Fin.zero_ne_one positions

/-- A contextual proof substitution may intentionally reuse one target
assumption for two source positions; the ledger records both uses. -/
private def duplicateEnvironment
    (definition : ValidatedCalculusLanguageDef) (goal : Pattern) :
    OpenDerivationList definition [goal] [goal, goal] :=
  .cons (OpenDerivation.assumption (definition := definition)
    (context := [goal]) (0 : Fin 1))
    (.cons (OpenDerivation.assumption (definition := definition)
      (context := [goal]) (0 : Fin 1)) .nil)

theorem duplicateEnvironment_ledger
    (definition : ValidatedCalculusLanguageDef) (goal : Pattern) :
    mapLedger (duplicateEnvironment definition goal)
        [(0 : Fin 2), (1 : Fin 2)] =
      [(0 : Fin 1), (0 : Fin 1)] := by
  rfl

end Mettapedia.GSLT.LanguageDef.CertificateGSLT

#print axioms Mettapedia.GSLT.LanguageDef.CertificateGSLT.mapLedger_comp
#print axioms Mettapedia.GSLT.LanguageDef.CertificateGSLT.ledgerFace
#print axioms Mettapedia.GSLT.LanguageDef.CertificateGSLT.derivationToLedger
#print axioms Mettapedia.GSLT.LanguageDef.CertificateGSLT.goalLedgerFace
#print axioms Mettapedia.GSLT.LanguageDef.CertificateGSLT.derivationToGoalLedger
#print axioms Mettapedia.GSLT.LanguageDef.CertificateGSLT.duplicateAnswers_sameGoal_distinctLedger
#print axioms Mettapedia.GSLT.LanguageDef.CertificateGSLT.duplicateEnvironment_ledger
