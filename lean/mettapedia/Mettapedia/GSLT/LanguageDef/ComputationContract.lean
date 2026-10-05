import Mettapedia.GSLT.LanguageDef.AuthoredComputation
import Mettapedia.OSLF.Framework.DerivedModalities

/-!
# A preserved contract for reused computed evidence

A checker that reuses evidence keeps a memo of entries: a query, an answer and
the provenance of the answer, either a run of the authored program with a given
fuel or a replayed check. The contract says every entry answers its query
according to the authored relation, and every computed entry names a run that
returns its answer.

The steps that extend the memo are recording a computed leaf and recording a
replayed answer. Their reduction span gives the operators of
`DerivedModalities`. The contract is preserved by every step: it lies below the
forward box `∀_source ∘ target*`, which says every step from a state leads to a
state with the property. By change of base, preservation is the same as the
step image of the contract staying inside it.

Lookup by the whole query returns related answers. A lookup keyed by less than
the query — forgetting the theory, for instance — can return the answer of a
different query, and then the contract fails.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Authored.Contract

open Mettapedia.OSLF.Framework.DerivedModalities

/-! ## Memo states -/

/-- Where an answer came from. -/
inductive Provenance where
  | computed (fuel : Nat)
  | replayed

variable {Query Answer : Type} (C : AuthoredComputation Query Answer)

/-- One reusable piece of evidence. -/
structure Entry (Query Answer : Type) where
  query : Query
  answer : Answer
  provenance : Provenance

/-- **The contract**: every entry answers its query, and a computed entry names
a run of the authored program returning its answer. -/
def Holds (memo : List (Entry Query Answer)) : Prop :=
  ∀ entry ∈ memo, C.relation entry.query entry.answer ∧
    ∀ fuel, entry.provenance = .computed fuel →
      C.runs ⟨entry.query, entry.answer, fuel⟩ = true

/-- The steps that extend the memo. -/
inductive Step : Type where
  | record (memo : List (Entry Query Answer)) (leaf : Leaf Query Answer)
      (succeeded : C.runs leaf = true)
  | replay (memo : List (Entry Query Answer)) (query : Query) (answer : Answer)
      (checked : C.relation query answer)

/-- The reduction span of memo steps. -/
def span : ReductionSpan (List (Entry Query Answer)) where
  Edge := Step C
  source
    | .record memo _ _ => memo
    | .replay memo _ _ _ => memo
  target
    | .record memo leaf _ => ⟨leaf.query, leaf.answer, .computed leaf.fuel⟩ :: memo
    | .replay memo query answer _ => ⟨query, answer, .replayed⟩ :: memo

/-- **The contract is preserved by every step.** -/
theorem holds_preserved : Holds C ≤ derivedForwardBox (span C) (Holds C) := by
  intro memo holds step atSource
  cases step with
  | record before leaf succeeded =>
      change before = memo at atSource
      subst atSource
      intro entry member
      rcases List.mem_cons.mp member with rfl | inBefore
      · refine ⟨C.relation_of_runs succeeded, ?_⟩
        intro fuel same
        cases same
        exact succeeded
      · exact holds entry inBefore
  | replay before query answer checked =>
      change before = memo at atSource
      subst atSource
      intro entry member
      rcases List.mem_cons.mp member with rfl | inBefore
      · exact ⟨checked, fun _ impossible => by cases impossible⟩
      · exact holds entry inBefore

/-- The same, stated through change of base: every state reached from one with
the contract has it. -/
theorem image_holds : derivedImage (span C) (Holds C) ≤ Holds C :=
  (preserved_iff_derivedImage_le (span C) (Holds C)).mp (holds_preserved C)

/-- The empty memo satisfies the contract. -/
theorem holds_nil : Holds C [] := fun _ member => absurd member (List.not_mem_nil)

/-! ## Lookup -/

/-- Lookup keyed by a projection of the query: the first entry with the same key. -/
def lookupBy {Key : Type} [DecidableEq Key] (key : Query → Key) :
    List (Entry Query Answer) → Query → Option Answer
  | [], _ => none
  | entry :: rest, query =>
      if key entry.query = key query then some entry.answer else lookupBy key rest query

theorem lookupBy_mem {Key : Type} [DecidableEq Key] (key : Query → Key) :
    ∀ (memo : List (Entry Query Answer)) (query : Query) (answer : Answer),
      lookupBy key memo query = some answer →
        ∃ entry ∈ memo, key entry.query = key query ∧ entry.answer = answer
  | [], _, _, found => by cases found
  | entry :: rest, query, answer, found => by
      unfold lookupBy at found
      split at found
      next same =>
        cases found
        exact ⟨entry, List.mem_cons_self, same, rfl⟩
      next =>
        obtain ⟨other, member, same, answered⟩ := lookupBy_mem key rest query answer found
        exact ⟨other, List.mem_cons_of_mem _ member, same, answered⟩

/-- **Lookup by the whole query returns a related answer** when the memo
satisfies the contract. -/
theorem lookup_sound [DecidableEq Query] {memo : List (Entry Query Answer)}
    (holds : Holds C memo) {query : Query} {answer : Answer}
    (found : lookupBy id memo query = some answer) : C.relation query answer := by
  obtain ⟨entry, member, same, answered⟩ := lookupBy_mem id memo query answer found
  have related := (holds entry member).1
  simp only [id] at same
  rw [same, answered] at related
  exact related

/-- **A key that forgets part of the query breaks the contract**: when it
identifies a query with another whose answer does not answer it, lookup
returns that unrelated answer. -/
theorem coarse_key_unsound {Key : Type} [DecidableEq Key] (key : Query → Key)
    {asked recorded : Query} {answer : Answer} (sameKey : key recorded = key asked)
    (unrelated : ¬ C.relation asked answer) :
    lookupBy key [⟨recorded, answer, .replayed⟩] asked = some answer ∧
      ¬ C.relation asked answer := by
  refine ⟨?_, unrelated⟩
  simp [lookupBy, sameKey]

end Mettapedia.GSLT.LanguageDef.Authored.Contract
