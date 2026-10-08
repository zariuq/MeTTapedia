import Mettapedia.GSLT.Logic.ProgrammableSpaceEvidence
import Mathlib.Data.List.OfFn

/-!
# Actual proof production and the counted Horn reading

Each premise bag contains typed retained derivations. The product operation
constructs every typed tuple of premises, and every authored rule occurrence
wraps each tuple in a genuine derivation of its head. Counting those produced
receipts agrees with the existing `AnnotatedHorn.stepCount`. The source rule
position survives in the produced receipt even when two clauses are equal.

Fact support and input-origin support are different readings of the same
retained batch. Counts of derivations count proof choices, not independent
observations.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.ProgrammableSpaceEvidence

attribute [local instance] Finite.membership

open Core.AnnotatedHorn

universe u v
variable {Atom : Type u} {Origin : Type v} {source : Source Atom Origin}

abbrev PremiseTuple (source : Source Atom Origin) (body : List Atom) :=
  (position : Fin body.length) → Derivation source (body.get position)

def premiseChoices (assign : (atom : Atom) → Multiset (Derivation source atom)) :
    (body : List Atom) → Multiset (PremiseTuple source body)
  | [] => {fun position => Fin.elim0 position}
  | atom :: rest => (assign atom).bind fun first =>
      (premiseChoices assign rest).map fun others => Fin.cases first others

theorem card_premiseChoices
    (assign : (atom : Atom) → Multiset (Derivation source atom)) (body : List Atom) :
    (premiseChoices assign body).card = (body.map fun atom => (assign atom).card).prod := by
  induction body with
  | nil => rfl
  | cons atom rest inductionHypothesis =>
      simp [premiseChoices, Multiset.card_bind, Multiset.map_const',
        Multiset.sum_replicate, inductionHypothesis]

variable [DecidableEq Atom]

/-- Only listed input origins produce input derivations; the equality witness
transports each actual source fact to the requested atom. -/
def inputBag (source : Source Atom Origin) (origins : List Origin) (atom : Atom) :
    Multiset (Derivation source atom) :=
  (origins : Multiset Origin).bind fun origin =>
    if same : source.input origin = atom then {same ▸ Derivation.input origin} else 0

def matchingRules (source : Source Atom Origin) (atom : Atom) : List source.RuleIndex :=
  (List.finRange source.rules.length).filter fun index => decide ((source.rule index).head = atom)

theorem matchingRules_authored (source : Source Atom Origin) (atom : Atom) :
    (matchingRules source atom).map source.rule =
      source.rules.filter (fun rule => decide (rule.head = atom)) := by
  have filtered := congrArg
    (List.filter (fun rule : DefiniteRule Atom => decide (rule.head = atom)))
    (List.map_get_finRange source.rules)
  rw [List.filter_map] at filtered
  exact filtered

def producedReceipts (source : Source Atom Origin)
    (assign : (atom : Atom) → Multiset (Derivation source atom)) (atom : Atom) :
    Multiset (Receipt source) :=
  ((matchingRules source atom).map fun index =>
    (premiseChoices assign (source.rule index).body).map fun premises =>
      (⟨(source.rule index).head, Derivation.rule index premises⟩ : Receipt source)).sum

theorem produced_count (source : Source Atom Origin)
    (assign : (atom : Atom) → Multiset (Derivation source atom)) (atom : Atom) :
    (producedReceipts source assign atom).card =
      stepCount source.rules (fun atom => (assign atom).card) atom := by
  rw [producedReceipts, card_listSum]
  simp only [List.map_map, Function.comp_def]
  trans ((matchingRules source atom).map fun index =>
    ((source.rule index).body.map fun premise => (assign premise).card).prod).sum
  · apply congrArg List.sum
    apply List.map_congr_left
    intro index _
    exact (Multiset.card_map _ _).trans (card_premiseChoices assign _)
  · have same := congrArg
      (fun rules : List (DefiniteRule Atom) =>
        (rules.map fun rule => (rule.body.map fun atom => (assign atom).card).prod).sum)
      (matchingRules_authored source atom)
    simpa only [List.map_map, Function.comp_def, stepCount] using same

private theorem mem_list_sum {Value : Type u} (bags : List (Multiset Value)) (value : Value) :
    value ∈ bags.sum ↔ ∃ bag ∈ bags, value ∈ bag := by
  induction bags with
  | nil => simp
  | cons first rest inductionHypothesis => simp [inductionHypothesis]

/-- Production retains the actual authored rule occurrence and premise tuple. -/
theorem mem_producedReceipts (source : Source Atom Origin)
    (assign : (atom : Atom) → Multiset (Derivation source atom)) (atom : Atom)
    (receipt : Receipt source) :
    receipt ∈ producedReceipts source assign atom ↔
      ∃ index ∈ matchingRules source atom,
        ∃ premises ∈ premiseChoices assign (source.rule index).body,
          (⟨(source.rule index).head, Derivation.rule index premises⟩ : Receipt source) = receipt := by
  rw [producedReceipts, mem_list_sum]
  constructor
  · rintro ⟨bag, inList, produced⟩
    obtain ⟨index, present, rfl⟩ := List.mem_map.mp inList
    obtain ⟨premises, chosen, same⟩ := Multiset.mem_map.mp produced
    exact ⟨index, present, premises, chosen, same⟩
  · rintro ⟨index, present, premises, chosen, same⟩
    exact ⟨_, List.mem_map.mpr ⟨index, present, rfl⟩,
      Multiset.mem_map.mpr ⟨premises, chosen, same⟩⟩

theorem produced_fact (source : Source Atom Origin)
    (assign : (atom : Atom) → Multiset (Derivation source atom)) (atom : Atom)
    (receipt : Receipt source) (present : receipt ∈ producedReceipts source assign atom) :
    receipt.fact = atom := by
  obtain ⟨index, matching, premises, _, rfl⟩ :=
    (mem_producedReceipts source assign atom receipt).mp present
  exact of_decide_eq_true (List.mem_filter.mp matching).2

def batchSupport (batch : List (Receipt source)) : Finset Atom :=
  Finite.support (batch.map Receipt.fact)

theorem mem_batchSupport (batch : List (Receipt source)) (atom : Atom) :
    atom ∈ batchSupport batch ↔ ∃ receipt ∈ batch, receipt.fact = atom := by
  simp only [batchSupport, Finite.mem_support, List.mem_map]

def batchOriginSupport [DecidableEq Origin] (batch : List (Receipt source)) : Finset Origin :=
  Finite.support (batch.flatMap Receipt.origins)

omit [DecidableEq Atom] in
theorem mem_batchOriginSupport [DecidableEq Origin]
    (batch : List (Receipt source)) (origin : Origin) :
    origin ∈ batchOriginSupport batch ↔ ∃ receipt ∈ batch, origin ∈ receipt.origins := by
  simp only [batchOriginSupport, Finite.mem_support, List.mem_flatMap]

end Mettapedia.GSLT.ProgrammableSpaceEvidence
