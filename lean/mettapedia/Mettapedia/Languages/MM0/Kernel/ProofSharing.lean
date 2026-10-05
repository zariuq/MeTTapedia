import Mettapedia.Languages.MM0.Kernel.ProofExtension

/-!
# Reusing checked local MM0 conclusions

A saved proof may be referenced like a local hypothesis only after its
conclusion has been justified in the original theory, context and hypothesis
scope. This is cut for MM0's existing proof judgment, not another checker.

The runtime can retain one conclusion and references to it. The proofs below
do not reconstruct or expand a shared proof tree. They establish the logical
contract needed by scoped proof sharing; parsing, the supplied-witness map and
its concrete execution remain separate obligations.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MM0.Kernel

/-- Replacing local assumptions by justified conclusions preserves derivability.
The signatures and variable context stay fixed. -/
theorem Derives.replaceHypotheses {signature : TermSignature}
    {definitions : Definition.Signature} {theorems : TheoremSignature}
    {context : Context} {source target : List Preterm} {expression : Preterm}
    (replacements : ∀ hypothesis ∈ source,
      Derives signature definitions theorems context target hypothesis)
    (derived : Derives signature definitions theorems context source expression) :
    Derives signature definitions theorems context target expression := by
  induction derived using Derives.rec
      (motive_2 := fun expressions _ =>
        DerivesList signature definitions theorems context target expressions) with
  | hypothesis member => exact replacements _ member
  | theoremApp known instantiated _ ih => exact .theoremApp known instantiated ih
  | conversion converted _ ih => exact .conversion converted ih
  | nil => exact .nil
  | cons _ _ ihHead ihTail => exact .cons ihHead ihTail

theorem Derives.weakenHypotheses {signature : TermSignature}
    {definitions : Definition.Signature} {theorems : TheoremSignature}
    {context : Context} {source target : List Preterm} {expression : Preterm}
    (included : ∀ hypothesis ∈ source, hypothesis ∈ target)
    (derived : Derives signature definitions theorems context source expression) :
    Derives signature definitions theorems context target expression :=
  derived.replaceHypotheses (fun _ member => .hypothesis (included _ member))

/-- Checked saved conclusions add no judgments to the original local scope.
This is an equivalence of derivability, not of concrete proof representations. -/
theorem derives_with_checked_facts_iff {signature : TermSignature}
    {definitions : Definition.Signature} {theorems : TheoremSignature}
    {context : Context} {hypotheses saved : List Preterm} {expression : Preterm}
    (checked : ∀ fact ∈ saved,
      Derives signature definitions theorems context hypotheses fact) :
    Derives signature definitions theorems context (hypotheses ++ saved) expression ↔
      Derives signature definitions theorems context hypotheses expression := by
  constructor
  · intro derived
    apply derived.replaceHypotheses
    intro hypothesis member
    rcases List.mem_append.mp member with original | shared
    · exact .hypothesis original
    · exact checked _ shared
  · exact fun derived => derived.weakenHypotheses
      (fun _ member => List.mem_append_left _ member)

/-- A particular submitted witness checked using saved conclusions remains
logically justified in the original scope. Its acceptance alone never
justifies the saved entries. -/
theorem ProofWitness.Checks.reuse_checked {signature : TermSignature}
    {definitions : Definition.Signature} {theorems : TheoremSignature}
    {context : Context} {hypotheses saved : List Preterm}
    {witness : ProofWitness} {expression : Preterm}
    (savedChecked : ∀ fact ∈ saved,
      Derives signature definitions theorems context hypotheses fact)
    (checked : Checks signature definitions theorems context
      (hypotheses ++ saved) witness expression) :
    Derives signature definitions theorems context hypotheses expression :=
  (derives_with_checked_facts_iff savedChecked).mp checked.derives

/-- Each saved entry carries the initializer actually supplied by the caller.
Checking those initializers in the original scope makes their conclusions
conservative local proof references. No new theorem or axiom is inserted. -/
theorem saved_witnesses_conservative {signature : TermSignature}
    {definitions : Definition.Signature} {theorems : TheoremSignature}
    {context : Context} {hypotheses : List Preterm}
    {saved : List (Preterm × ProofWitness)} {expression : Preterm}
    (initializers : ∀ entry ∈ saved,
      ProofWitness.check signature definitions theorems context hypotheses
        entry.2 entry.1 = true) :
    Derives signature definitions theorems context (hypotheses ++ saved.map Prod.fst) expression ↔
      Derives signature definitions theorems context hypotheses expression := by
  apply derives_with_checked_facts_iff
  intro fact member
  obtain ⟨entry, stored, same⟩ := List.mem_map.mp member
  subst fact
  exact ProofWitness.check_sound (initializers entry stored)

/-- Checking a root with those saved conclusions is sound in the original
scope. This statement retains every supplied initializer and the submitted
root; it does not assert that their wire-format elaboration is established. -/
theorem check_with_saved_witnesses_sound {signature : TermSignature}
    {definitions : Definition.Signature} {theorems : TheoremSignature}
    {context : Context} {hypotheses : List Preterm}
    {saved : List (Preterm × ProofWitness)} {witness : ProofWitness} {expression : Preterm}
    (initializers : ∀ entry ∈ saved,
      ProofWitness.check signature definitions theorems context hypotheses
        entry.2 entry.1 = true)
    (root : ProofWitness.check signature definitions theorems context
      (hypotheses ++ saved.map Prod.fst) witness expression = true) :
    Derives signature definitions theorems context hypotheses expression :=
  (saved_witnesses_conservative initializers).mp (ProofWitness.check_sound root)

/-- Chronological saved proofs. An initializer may reference earlier checked
entries, but not itself or a later entry. The environment does not store an
expanded proof tree. -/
inductive SavedWitnessesChecked (signature : TermSignature)
    (definitions : Definition.Signature) (theorems : TheoremSignature)
    (context : Context) (hypotheses : List Preterm) : List (Preterm × ProofWitness) → Prop where
  | nil : SavedWitnessesChecked signature definitions theorems context hypotheses []
  | record {before : List (Preterm × ProofWitness)} {expression : Preterm} {witness : ProofWitness} :
      SavedWitnessesChecked signature definitions theorems context hypotheses before →
      ProofWitness.check signature definitions theorems context
        (hypotheses ++ before.map Prod.fst) witness expression = true →
      SavedWitnessesChecked signature definitions theorems context hypotheses
        (before ++ [(expression, witness)])

/-- Every saved result remains justified in the original hypothesis scope,
including initializers which reused earlier results. -/
theorem SavedWitnessesChecked.sound {signature : TermSignature}
    {definitions : Definition.Signature} {theorems : TheoremSignature}
    {context : Context} {hypotheses : List Preterm} {saved : List (Preterm × ProofWitness)}
    (checked : SavedWitnessesChecked signature definitions theorems context hypotheses saved) :
    ∀ fact ∈ saved.map Prod.fst,
      Derives signature definitions theorems context hypotheses fact := by
  induction checked with
  | nil => intro fact member; cases member
  | @record before expression witness _ accepted ih =>
      have justified : Derives signature definitions theorems context hypotheses expression :=
        (derives_with_checked_facts_iff ih).mp (ProofWitness.check_sound accepted)
      intro fact member
      simp only [List.map_append, List.map_cons, List.map_nil, List.mem_append,
        List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with original | rfl
      · exact ih _ original
      · exact justified

theorem SavedWitnessesChecked.conservative {signature : TermSignature}
    {definitions : Definition.Signature} {theorems : TheoremSignature}
    {context : Context} {hypotheses : List Preterm} {saved : List (Preterm × ProofWitness)}
    (checked : SavedWitnessesChecked signature definitions theorems context hypotheses saved)
    (expression : Preterm) :
    Derives signature definitions theorems context (hypotheses ++ saved.map Prod.fst) expression ↔
      Derives signature definitions theorems context hypotheses expression :=
  derives_with_checked_facts_iff checked.sound

theorem SavedWitnessesChecked.root_sound {signature : TermSignature}
    {definitions : Definition.Signature} {theorems : TheoremSignature}
    {context : Context} {hypotheses : List Preterm} {saved : List (Preterm × ProofWitness)}
    (checked : SavedWitnessesChecked signature definitions theorems context hypotheses saved)
    {witness : ProofWitness} {expression : Preterm}
    (root : ProofWitness.check signature definitions theorems context
      (hypotheses ++ saved.map Prod.fst) witness expression = true) :
    Derives signature definitions theorems context hypotheses expression :=
  (checked.conservative expression).mp (ProofWitness.check_sound root)

/-- Conversion cannot invent a proof when neither hypotheses nor theorems
provide a starting proof, regardless of the declared computations. -/
theorem no_derivation_without_hypotheses_or_theorems
    (signature : TermSignature) (definitions : Definition.Signature)
    (context : Context) (expression : Preterm) :
    ¬ Derives signature definitions (fun _ => none) context [] expression := by
  intro derived
  induction derived using Derives.rec
      (motive_2 := fun expressions _ => ∀ value ∈ expressions, False) with
  | hypothesis member => exact List.not_mem_nil member
  | theoremApp known _ _ _ => cases known
  | conversion _ _ ih => exact ih
  | nil => rename_i value member; cases member
  | cons _ _ ihHead ihTail =>
      rename_i value member
      rcases List.mem_cons.mp member with rfl | member
      · exact ihHead
      · exact ihTail _ member

namespace ProofSharingControls

private def terms : TermSignature
  | 0 => some ⟨[], 0, ∅⟩
  | _ => none

private def declarations : TheoremSignature
  | 0 => some ⟨[], [], .term 0⟩
  | 1 => some ⟨[], [.term 0, .term 0], .term 0⟩
  | _ => none

private def emptyDefinitions : Definition.Signature := fun _ => none

theorem initializer_checked_before_reuse :
    ProofWitness.check terms emptyDefinitions declarations [] []
      (.theoremApp 0 [] []) (.term 0) = true := by decide +kernel

theorem two_references_preserve_two_premises :
    ProofWitness.check terms emptyDefinitions declarations [] [.term 0]
      (.theoremApp 1 [] [.hyp 0, .hyp 0]) (.term 0) = true := by decide +kernel

theorem saved_conclusion_discharged :
    Derives terms emptyDefinitions declarations [] [] (.term 0) := by
  apply ProofWitness.Checks.reuse_checked (saved := [.term 0])
      (witness := .theoremApp 1 [] [.hyp 0, .hyp 0])
  · intro fact member
    have same : fact = .term 0 := by simpa using member
    subst fact
    exact ProofWitness.check_sound initializer_checked_before_reuse
  · exact (ProofWitness.check_iff _ _ _ _ _ _ _).mp two_references_preserve_two_premises

theorem dropping_repeated_premise_refused :
    ProofWitness.proof? terms emptyDefinitions declarations [] [.term 0]
      (.theoremApp 1 [] [.hyp 0]) = none := by decide +kernel

theorem later_initializer_can_reference_checked_predecessor :
    SavedWitnessesChecked terms emptyDefinitions declarations [] []
      [(.term 0, .theoremApp 0 [] []), (.term 0, .hyp 0)] := by
  apply SavedWitnessesChecked.record
    (before := [(.term 0, .theoremApp 0 [] [])])
  · apply SavedWitnessesChecked.record (before := []) SavedWitnessesChecked.nil
    exact initializer_checked_before_reuse
  · decide +kernel

theorem first_initializer_cannot_reference_itself :
    ProofWitness.proof? terms emptyDefinitions declarations [] [] (.hyp 0) = none := by
  simp [ProofWitness.proof?]

theorem unchecked_saved_conclusion_is_an_extra_assumption :
    Derives terms emptyDefinitions (fun _ => none) [] [.term 0] (.term 0) ∧
      ¬ Derives terms emptyDefinitions (fun _ => none) [] [] (.term 0) := by
  exact ⟨.hypothesis (by simp), no_derivation_without_hypotheses_or_theorems _ _ _ _⟩

theorem conclusion_cannot_be_reused_in_a_different_theory :
    ProofWitness.check terms emptyDefinitions declarations [] []
        (.theoremApp 0 [] []) (.term 0) = true ∧
      ¬ Derives terms emptyDefinitions (fun _ => none) [] [] (.term 0) :=
  ⟨initializer_checked_before_reuse, no_derivation_without_hypotheses_or_theorems _ _ _ _⟩

end ProofSharingControls

end Mettapedia.Languages.MM0.Kernel
