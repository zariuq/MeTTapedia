import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FragmentsOfTheStep.ReflectiveCalculus.ByInstantiation.ReactComparison

/-!
# The channel match is decided by canonical forms of names

For two rows of a represented state, the communication firing that takes them is admitted exactly
when the first row's value is an input, the second's an output, and their channels have the same
canonical read-back (`comm_admitted_iff`); for an input row and an output row this is a decision
built from the decidable equality of patterns (`commDecision`), and rows of other shapes do not
communicate (`comm_needs_shapes`). The knowledge's equality, name equivalence at closed names, is
decided by the source's canonical forms of names; canonical forms are a decision procedure here,
not the meaning of any term. Controls: channels that are not name equivalent do not communicate
(`inequivalent_channels_refused`); `@(*@0)` and `@0` do (`quote_drop_channels_admitted`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FragmentsOfTheStep.ReflectiveCalculus.ByInstantiation

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ScopedPattern
open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open Mettapedia.Languages.ProcessCalculi.RhoCalculus
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.Canonical (canonicalize)
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefGSLT
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.CanonicalReactionControls

/-- The canonical communication firing on two rows, making a third. -/
abbrev commFiring (s : State) (o₁ o₂ o₃ : ℕ) : Firing s :=
  RuleSyntax.Contextual.canonical (F := s.frame) commRule commRule_mem ⟨[o₁, o₂], [], [o₃]⟩ []

/-- **What an admitted communication says about the values of its rows.** -/
theorem comm_values {s : State} {P : RhoProcess} {value : ℕ → G [] .pr}
    (represented : RepresentsBy s P value) {o₁ o₂ o₃ : ℕ}
    (admitted : (commFiring s o₁ o₂ o₃).Admits knowledge s) :
    ∃ c₁ b₁ c₂ q₂, value o₁ = inputT c₁ b₁ ∧ value o₂ = outputT c₂ q₂ ∧ Similar c₁ c₂ := by
  obtain ⟨_, enabled, solvable, _⟩ := admitted
  have present₁ : o₁ ∈ s.present := enabled.taken_subset (by
    simp [Selection.commit, commFiring, RuleSyntax.Contextual.canonical])
  have present₂ : o₂ ∈ s.present := enabled.taken_subset (by
    simp [Selection.commit, commFiring, RuleSyntax.Contextual.canonical])
  obtain ⟨g', solved⟩ := (solvable_iff _).mp solvable
  let opening := RuleSyntax.Contextual.canonicalOpening sig s.frame commFrame
  have known := ground_knowledge (commFiring s o₁ o₂ o₃) solved
  obtain ⟨u₁, at₁, similar₁⟩ := represented.determined _ known o₁ present₁
  obtain ⟨u₂, at₂, similar₂⟩ := represented.determined _ known o₂ present₂
  have first := ground_take (commFiring s o₁ o₂ o₃) solved (p := obs commInput) (o := o₁) (by
    simp only [commFiring, RuleSyntax.Firing.opened, RuleInstance.map,
      RuleSyntax.Contextual.canonical, List.map_cons, List.map_nil, List.zip_cons_cons,
      List.zip_nil_right]
    exact .head _)
  have second := ground_take (commFiring s o₁ o₂ o₃) solved (p := obs commOutput) (o := o₂) (by
    simp only [commFiring, RuleSyntax.Firing.opened, RuleInstance.map,
      RuleSyntax.Contextual.canonical, List.map_cons, List.map_nil, List.zip_cons_cons,
      List.zip_nil_right]
    exact .tail _ (.head _))
  rw [at₁] at first
  rw [at₂] at second
  change ObsSimilar ⟨[], .pr, instantiate (Assignment.compose g' opening) commInput⟩ _ at first
  change ObsSimilar ⟨[], .pr, instantiate (Assignment.compose g' opening) commOutput⟩ _ at second
  rw [instantiate_commInput] at first
  rw [instantiate_commOutput] at second
  obtain ⟨c₁, b₁, shape₁, channel₁, _⟩ :=
    similar_input_inv (Γ := ([] : Ctx sig)) (obs_closed_similar first similar₁)
  obtain ⟨c₂, q₂, shape₂, channel₂, _⟩ :=
    similar_output_inv (Γ := ([] : Ctx sig)) (obs_closed_similar second similar₂)
  exact ⟨c₁, b₁, c₂, q₂, shape₁, shape₂, similar_trans (similar_symm channel₁) channel₂⟩

/-- **The communication on two rows is admitted** when their values are an input and an output on
similar channels. -/
theorem comm_admitted_of {s : State} {P : RhoProcess} {value : ℕ → G [] .pr}
    (represented : RepresentsBy s P value) {o₁ o₂ o₃ : ℕ} (present₁ : o₁ ∈ s.present)
    (present₂ : o₂ ∈ s.present) (distinct : o₁ ≠ o₂) (fresh₃ : o₃ ∉ s.present)
    {c₁ c₂ : G [] .nm} {b₁ : G [.nm, .pr] .pr} {q₂ : G [] .pr}
    (shape₁ : value o₁ = inputT c₁ b₁) (shape₂ : value o₂ = outputT c₂ q₂)
    (channels : Similar c₁ c₂) : (commFiring s o₁ o₂ o₃).Admits knowledge s := by
  classical
  obtain ⟨g₀, known⟩ := represented.solvable
  let h : Grounding commFrame := fun
    | .channel => c₁
    | .body => b₁
    | .payload => q₂
  exact canonical_admits (s := s) commRule commRule_mem ⟨[o₁, o₂], [], [o₃]⟩ rfl rfl rfl
    (by simp [distinct]) (by simp) rfl rfl rfl (by simp [present₁, present₂]) (by simp [fresh₃])
    ⟨_, copair_solves commRule commRule_mem ⟨[o₁, o₂], [], [o₃]⟩ rfl rfl g₀ known h (by
      intro p x inside
      simp only [commRule, List.zip_cons_cons, List.zip_nil_right, List.mem_cons,
        List.not_mem_nil, or_false, Prod.mk.injEq] at inside
      rcases inside with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · have instantiated : instantiate h commInput = inputT c₁ b₁ := instantiate_commInput h
        change ObsSimilar ⟨[], .pr, instantiate h commInput⟩ _
        rw [instantiated]
        exact row_similar represented known present₁ (by rw [shape₁]; exact similar_refl _)
      · have instantiated : instantiate h commOutput = outputT c₁ q₂ := instantiate_commOutput h
        change ObsSimilar ⟨[], .pr, instantiate h commOutput⟩ _
        rw [instantiated]
        exact row_similar represented known present₂
          (by rw [shape₂]; exact .output channels (similar_refl _)))⟩

/-- **The channel match is decided by canonical forms.** -/
theorem comm_admitted_iff {s : State} {P : RhoProcess} {value : ℕ → G [] .pr}
    (represented : RepresentsBy s P value) {o₁ o₂ o₃ : ℕ} (present₁ : o₁ ∈ s.present)
    (present₂ : o₂ ∈ s.present) (distinct : o₁ ≠ o₂) (fresh₃ : o₃ ∉ s.present) :
    (commFiring s o₁ o₂ o₃).Admits knowledge s ↔
      ∃ c₁ b₁ c₂ q₂, value o₁ = inputT c₁ b₁ ∧ value o₂ = outputT c₂ q₂ ∧
        canonicalize (read c₁) = canonicalize (read c₂) := by
  constructor
  · intro admitted
    obtain ⟨c₁, b₁, c₂, q₂, shape₁, shape₂, channels⟩ := comm_values represented admitted
    exact ⟨c₁, b₁, c₂, q₂, shape₁, shape₂, similar_canonical channels⟩
  · rintro ⟨c₁, b₁, c₂, q₂, shape₁, shape₂, canonicalChannels⟩
    have closed₁ := represented.closed o₁ present₁
    have closed₂ := represented.closed o₂ present₂
    rw [shape₁] at closed₁
    rw [shape₂] at closed₂
    have closedChannel₁ : Closed c₁ := by
      have unfolded : binderSafeAt "NQuote" 0
          (.apply "PInput" [read c₁, .lambda none (read b₁)]) = true := closed₁
      simp only [binderSafeAt, binderSafeListAt, Bool.and_eq_true] at unfolded
      exact unfolded.1
    have closedChannel₂ : Closed c₂ := by
      have unfolded : binderSafeAt "NQuote" 0 (.apply "POutput" [read c₂, read q₂]) = true := closed₂
      simp only [binderSafeAt, binderSafeListAt, Bool.and_eq_true] at unfolded
      exact unfolded.1
    exact comm_admitted_of represented present₁ present₂ distinct fresh₃ shape₁ shape₂
      (.name closedChannel₁ closedChannel₂
        (StructuralCongruence.trans _ _ _ (Canonical.canonicalize_sound _)
          (canonicalChannels ▸ StructuralCongruence.symm _ _ (Canonical.canonicalize_sound _))))

/-- **For an input row and an output row, admission is decided by the equality of the canonical
read-backs of their channels**: a decision built from the decidable equality of patterns. -/
def commDecision {s : State} {P : RhoProcess} {value : ℕ → G [] .pr}
    (represented : RepresentsBy s P value) {o₁ o₂ o₃ : ℕ} (present₁ : o₁ ∈ s.present)
    (present₂ : o₂ ∈ s.present) (distinct : o₁ ≠ o₂) (fresh₃ : o₃ ∉ s.present)
    {c₁ c₂ : G [] .nm} {b₁ : G [.nm, .pr] .pr} {q₂ : G [] .pr}
    (shape₁ : value o₁ = inputT c₁ b₁) (shape₂ : value o₂ = outputT c₂ q₂) :
    Decidable ((commFiring s o₁ o₂ o₃).Admits knowledge s) :=
  decidable_of_iff (canonicalize (read c₁) = canonicalize (read c₂)) (by
    rw [comm_admitted_iff represented present₁ present₂ distinct fresh₃]
    constructor
    · intro same
      exact ⟨c₁, b₁, c₂, q₂, shape₁, shape₂, same⟩
    · rintro ⟨c₁', b₁', c₂', q₂', at₁, at₂, same⟩
      rw [shape₁] at at₁
      rw [shape₂] at at₂
      cases at₁
      cases at₂
      exact same)

/-- Rows that are not an input and an output do not communicate: an admitted communication has an
input and an output value (`comm_values`). -/
theorem comm_needs_shapes {s : State} {P : RhoProcess} {value : ℕ → G [] .pr}
    (represented : RepresentsBy s P value) {o₁ o₂ o₃ : ℕ}
    (notInput : ∀ c b, value o₁ ≠ inputT c b) : ¬ (commFiring s o₁ o₂ o₃).Admits knowledge s := by
  intro admitted
  obtain ⟨c₁, b₁, _, _, shape₁, _, _⟩ := comm_values represented admitted
  exact notInput c₁ b₁ shape₁

/-- `for(y <- @(@0!(0))){*y}` as a value. -/
def mismatchInput : G [] .pr := inputT (quoteT outputZero) twinVar

/-- `@0!(@0!(0))` as a value. -/
def separatingOutput : G [] .pr := outputT nameZero outputZero

/-- **Negative control**: an input on `@(@0!(0))` and an output on `@0` are not name equivalent, so
no communication between them is admitted. -/
theorem inequivalent_channels_refused {s : State} {P : RhoProcess} {value : ℕ → G [] .pr}
    (represented : RepresentsBy s P value) {o₁ o₂ o₃ : ℕ} (present₁ : o₁ ∈ s.present)
    (present₂ : o₂ ∈ s.present) (distinct : o₁ ≠ o₂) (fresh₃ : o₃ ∉ s.present)
    (shape₁ : value o₁ = mismatchInput) (shape₂ : value o₂ = separatingOutput) :
    ¬ (commFiring s o₁ o₂ o₃).Admits knowledge s := by
  rw [comm_admitted_iff represented present₁ present₂ distinct fresh₃]
  rintro ⟨c₁, b₁, c₂, q₂, at₁, at₂, same⟩
  rw [shape₁] at at₁
  rw [shape₂] at at₂
  cases at₁
  cases at₂
  exact Source.names_not_equivalent same

/-- The positive companion: an input on `@(*@0)` and an output on `@0` do communicate. -/
theorem quote_drop_channels_admitted {s : State} {P : RhoProcess} {value : ℕ → G [] .pr}
    (represented : RepresentsBy s P value) {o₁ o₂ o₃ : ℕ} (present₁ : o₁ ∈ s.present)
    (present₂ : o₂ ∈ s.present) (distinct : o₁ ≠ o₂) (fresh₃ : o₃ ∉ s.present)
    (shape₁ : value o₁ = inputT nameDropZero twinVar) (shape₂ : value o₂ = separatingOutput) :
    (commFiring s o₁ o₂ o₃).Admits knowledge s :=
  comm_admitted_of represented present₁ present₂ distinct fresh₃ shape₁ shape₂
    received_name_needs_name_equivalence.2.2.1

/-- **A state represents one equivalence class**: two processes it represents are equal modulo the
equations of the source. -/
theorem represents_functional {s : State} {P Q : RhoProcess} (first : Represents s P)
    (second : Represents s Q) :
    Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefGSLT.rhoProcessEquations.r P Q := by
  obtain ⟨value, first⟩ := first
  obtain ⟨value', second⟩ := second
  obtain ⟨g, solved⟩ := first.solvable
  have same : inventoryOf s.present value = inventoryOf s.present value' := by
    unfold inventoryOf
    refine Finset.sum_congr rfl fun o member => ?_
    obtain ⟨u, at', similar⟩ := first.determined g solved o member
    obtain ⟨u', at'', similar'⟩ := second.determined g solved o member
    have equal : u = u' := observe_injective (at'.symm.trans at'')
    subst equal
    rw [← primes_canonicalize, ← primes_canonicalize (read (value' o)),
      similar_canonical (similar_trans (similar_symm similar) similar')]
  apply (CanonicalBag.fromProcess_eq_iff P Q).mp
  apply Subtype.ext
  rw [← first.inventory_eq, ← second.inventory_eq, same]

#print axioms represents_functional
#print axioms comm_admitted_iff
#print axioms commDecision
#print axioms comm_needs_shapes
#print axioms inequivalent_channels_refused
#print axioms quote_drop_channels_admitted

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FragmentsOfTheStep.ReflectiveCalculus.ByInstantiation
