import Mettapedia.Enactive.Finite
import Mettapedia.Languages.MeTTa.PureKernel.Universe.RelationalEvidence
import Mathlib.Data.Finset.Card

/-!
# Bennett weakness at Prime's support quotient

Michael Timothy Bennett's weakness counts distinct admissible completions.
Prime's relational engine retains a strictly more informative object: a bag of
answer occurrences, each carrying its derivation.  This module places Bennett
weakness at the finite-support readout of that bag and proves the exact premise
under which it agrees with occurrence multiplicity.

The distinction is intentional.  Two derivations of one completion increase
Prime evidence multiplicity but do not create a second Bennett completion.
Thus weakness is a useful readout of Prime relations, never a replacement for
their proof-relevant fibres.
-/

set_option autoImplicit false

namespace Mettapedia.Enactive.PrimeSupport

open Mettapedia.Languages.MeTTa.PureKernel.Universe
open RelationalEvidence

universe u

/-- The finite set of distinct visible answers in a Prime occurrence bag. -/
def distinctSupport {Source Target : Type u}
    [DecidableEq Target]
    {relation : RelationalEvidence.ProofRel Source Target}
    {source : Source} (bag : AnswerBag relation source) : Finset Target :=
  bag.targets.toFinset

/-- Bennett-shaped support weakness: the number of distinct admissible
answers, after derivation occurrences have been quotiented to support. -/
def supportWeakness {Source Target : Type u}
    [DecidableEq Target]
    {relation : RelationalEvidence.ProofRel Source Target}
    {source : Source} (bag : AnswerBag relation source) : Nat :=
  (distinctSupport bag).card

@[simp]
theorem mem_distinctSupport_iff {Source Target : Type u}
    [DecidableEq Target]
    {relation : RelationalEvidence.ProofRel Source Target}
    {source : Source} {bag : AnswerBag relation source} {target : Target} :
    target ∈ distinctSupport bag ↔ target ∈ bag.support := by
  simp [distinctSupport, AnswerBag.targets, AnswerBag.support]

/-- Distinct-answer weakness cannot exceed the retained number of derivation
occurrences. -/
theorem supportWeakness_le_occurrenceCard {Source Target : Type u}
    [DecidableEq Target]
    {relation : RelationalEvidence.ProofRel Source Target}
    {source : Source} (bag : AnswerBag relation source) :
    supportWeakness bag ≤ bag.card := by
  calc
    supportWeakness bag = bag.targets.toFinset.card := rfl
    _ ≤ bag.targets.card := Multiset.toFinset_card_le bag.targets
    _ = bag.card := AnswerBag.card_targets bag

/-- Support weakness coincides with derivation multiplicity exactly under the
explicit no-duplicate-target premise. -/
theorem supportWeakness_eq_occurrenceCard_of_targetNodup
    {Source Target : Type u} [DecidableEq Target]
    {relation : RelationalEvidence.ProofRel Source Target}
    {source : Source} (bag : AnswerBag relation source)
    (uniqueTargets : bag.targets.Nodup) :
    supportWeakness bag = bag.card := by
  calc
    supportWeakness bag = bag.targets.toFinset.card := rfl
    _ = bag.targets.card :=
      Multiset.toFinset_card_of_nodup uniqueTargets
    _ = bag.card := AnswerBag.card_targets bag

/-! ## Bennett completion relations as Prime relations -/

namespace Completion

open Mettapedia.Enactive.Finite

universe uWorld

variable {World : Type uWorld} [Fintype World] [DecidableEq World]
variable {finiteLayer : Mettapedia.Enactive.Finite.Layer World}

/-- Evidence that one finite Bennett statement completes another. -/
structure Evidence (source target : finiteLayer.Statement) : Type uWorld where
  included : source.val ⊆ target.val

/-- Finite Bennett completion is a proof-relevant Prime relation. -/
def relation (finiteLayer : Mettapedia.Enactive.Finite.Layer World) :
    RelationalEvidence.ProofRel finiteLayer.Statement finiteLayer.Statement where
  evidence := Evidence

/-- The canonical complete occurrence bag contains one witnessed occurrence
for every distinct completion. -/
def bag (source : finiteLayer.Statement) :
    AnswerBag (relation finiteLayer) source :=
  (finiteLayer.extension source).val.attach.map fun target =>
    { target := target.val
      derivation :=
        ⟨(Finite.Layer.mem_extension («layer» := finiteLayer)).mp
          target.property⟩ }

@[simp]
theorem targets_bag (source : finiteLayer.Statement) :
    (bag source).targets = (finiteLayer.extension source).val := by
  simp only [bag, AnswerBag.targets, Multiset.map_map]
  exact Multiset.attach_map_val (finiteLayer.extension source).val

/-- The canonical occurrence bag has exactly the finite completion set as its
support. -/
theorem distinctSupport_bag (source : finiteLayer.Statement) :
    distinctSupport (bag source) = finiteLayer.extension source := by
  ext target
  simp [distinctSupport]

/-- Bennett's finite weakness is exactly Prime support weakness for the
completion relation's canonical complete bag. -/
theorem weakness_eq_supportWeakness (source : finiteLayer.Statement) :
    finiteLayer.weakness source = supportWeakness (bag source) := by
  rw [Finite.Layer.weakness, supportWeakness, distinctSupport_bag]

/-- There is exactly one canonical occurrence per completion, so this specific
bag also satisfies the uniqueness premise that equates support and occurrence
counts. -/
theorem targets_bag_nodup (source : finiteLayer.Statement) :
    (bag source).targets.Nodup := by
  rw [targets_bag]
  exact (finiteLayer.extension source).nodup

/-! ### Equipment representability has real premises -/

def singletonLayer : Mettapedia.Enactive.Finite.Layer Unit where
  vocabulary := ∅

def singletonStatement : singletonLayer.Statement :=
  ⟨∅, by decide⟩

theorem singletonLayer_statement_eq
    (statement : singletonLayer.Statement) :
    statement = singletonStatement := by
  apply Subtype.ext
  have subsetEmpty :=
    (Finite.Layer.mem_statements («layer» := singletonLayer)).mp
      statement.property |>.1
  exact Finset.subset_empty.mp subsetEmpty

/-- Positive representability control: with only one possible completion, the
completion relation is total and proof-relevantly deterministic, so it earns a
direct-map license from the relational equipment. -/
theorem singleton_completion_representable :
    Nonempty
      (RelationalInternalLanguage.Semantic.Rel.Representation
        (relation singletonLayer)) := by
  apply
    (RelationalInternalLanguage.Semantic.Rel.representable_iff_total_and_deterministic
      (relation singletonLayer)).2
  constructor
  · intro source
    exact ⟨⟨source, ⟨Finset.Subset.rfl⟩⟩⟩
  · intro source
    constructor
    rintro ⟨first, firstEvidence⟩ ⟨second, secondEvidence⟩
    have targetEqual : first = second :=
      (singletonLayer_statement_eq first).trans
        (singletonLayer_statement_eq second).symm
    cases targetEqual
    have evidenceEqual : firstEvidence = secondEvidence := by
      cases firstEvidence
      cases secondEvidence
      congr
    cases evidenceEqual
    rfl

/-- Negative representability control: the ordinary Boolean completion
relation branches from the empty statement to distinct completions, so it
remains a loose relation and must not be compiled to a function. -/
theorem bool_completion_not_representable :
    ¬ Nonempty
      (RelationalInternalLanguage.Semantic.Rel.Representation
        (relation Finite.Canary.boolLayer)) := by
  intro represented
  have totalAndDeterministic :=
    (RelationalInternalLanguage.Semantic.Rel.representable_iff_total_and_deterministic
      (relation Finite.Canary.boolLayer)).mp represented
  have deterministic := totalAndDeterministic.2
  let first : Sigma fun target =>
      (relation Finite.Canary.boolLayer).evidence
        Finite.Canary.emptyStatement target :=
    ⟨Finite.Canary.emptyStatement, ⟨Finset.Subset.rfl⟩⟩
  let second : Sigma fun target =>
      (relation Finite.Canary.boolLayer).evidence
        Finite.Canary.emptyStatement target :=
    ⟨Finite.Canary.trueStatement, ⟨Finset.empty_subset _⟩⟩
  have pairEqual : first = second :=
    (deterministic Finite.Canary.emptyStatement).allEq first second
  have targetEqual : Finite.Canary.emptyStatement =
      Finite.Canary.trueStatement := congrArg Sigma.fst pairEqual
  have targetUnequal : Finite.Canary.emptyStatement ≠
      Finite.Canary.trueStatement := by decide
  exact targetUnequal targetEqual

end Completion

/-! ## Multiplicity is strictly more informative -/

namespace MultiplicityCanary

def relation : RelationalEvidence.ProofRel Unit Bool where
  evidence := fun _ _ => Unit

def falseOccurrence : AnswerOccurrence relation () :=
  ⟨false, ()⟩

def one : AnswerBag relation () :=
  {falseOccurrence}

def two : AnswerBag relation () :=
  {falseOccurrence, falseOccurrence}

/-- Positive support example: both bags denote the same one-element support. -/
theorem equal_distinctSupport :
    distinctSupport one = distinctSupport two := by
  decide

/-- Negative control: equal Bennett support does not imply equal Prime
derivation multiplicity. -/
theorem different_occurrenceCard : one.card ≠ two.card := by
  decide

theorem equal_supportWeakness :
    supportWeakness one = supportWeakness two := by
  exact congrArg Finset.card equal_distinctSupport

end MultiplicityCanary

#print axioms mem_distinctSupport_iff
#print axioms supportWeakness_eq_occurrenceCard_of_targetNodup
#print axioms Completion.weakness_eq_supportWeakness
#print axioms Completion.singleton_completion_representable
#print axioms Completion.bool_completion_not_representable
#print axioms MultiplicityCanary.equal_distinctSupport
#print axioms MultiplicityCanary.different_occurrenceCard

end Mettapedia.Enactive.PrimeSupport
