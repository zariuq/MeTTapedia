import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FragmentsOfTheStep.ReflectiveCalculus.ByInstantiation.Rows

/-!
# What each admitted firing of the program does to a represented state

A state **represents** a closed process (`RepresentsBy`) through a value for each present row: its
knowledge is solvable, every grounding that solves it gives each row a closed process term similar
to the row's value, the values are closed, and the primes of their read-backs sum to the canonical
bag of the process.

* `comm_effect`: an admitted communication firing takes an input row and an output row whose
  values are an input and an output on name-equivalent channels; the made row's value is the
  continuation instantiated at the received name and process; the result represents every process
  whose primes are the calculus's contractum beside the other rows.
* `heat_effect`, `clearBag_effect`, `clearZero_effect`: the housekeeping firings keep the represented
  process and strictly decrease the spine weight.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FragmentsOfTheStep.ReflectiveCalculus.ByInstantiation

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ScopedPattern
open Mettapedia.OSLF.MeTTaIL.DerivedPresentationSyntax
open Mettapedia.OSLF.Framework.ConstructorCategory
open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open Mettapedia.Languages.ProcessCalculi.RhoCalculus
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.Canonical (canonicalize IsCanonical)
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefRewriteSystem
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefGSLT
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.CanonicalBag
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.CanonicalReaction
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits (Enabled fire)

/-! ## Representation -/

/-- The primes of the rows of a set of occurrences. -/
def inventoryOf (present : Finset ℕ) (value : ℕ → G [] .pr) : Multiset Pattern :=
  ∑ o ∈ present, primes (read (value o))

/-- The spine weight of the rows of a set of occurrences. -/
def weightOf (present : Finset ℕ) (value : ℕ → G [] .pr) : ℕ := ∑ o ∈ present, spine (value o)

/-- **A state represents a closed process**, through a value for each row. -/
structure RepresentsBy (s : State) (P : RhoProcess) (value : ℕ → G [] .pr) : Prop where
  solvable : ∃ g : Grounding s.frame, GroundSolves g s.knowledge
  determined : ∀ g : Grounding s.frame, GroundSolves g s.knowledge → ∀ o ∈ s.present,
    ∃ u : G [] .pr, instantiateObservation g (s.label o) = ⟨[], .pr, u⟩ ∧ Similar u (value o)
  closed : ∀ o ∈ s.present, Closed (value o)
  inventory_eq : inventoryOf s.present value = (fromProcess P).1

/-- A state represents a closed process. -/
def Represents (s : State) (P : RhoProcess) : Prop := ∃ value, RepresentsBy s P value

/-! ## Rows as closed processes -/

/-- A closed value read back is a closed process of the source. -/
def rowProcess (v : G [] .pr) (closed : Closed v) : RhoProcess :=
  ⟨read v, (rhoClosedTermWellSorted_process_iff _).mpr
    ⟨(read_sorted v 0 rfl : SortedAt 0 .pr (read v)).closed closed, closed⟩⟩

/-- The canonical form of a closed value is a closed canonical process. -/
theorem canonical_row (v : G [] .pr) (closed : Closed v) :
    RhoClosedTermWellSorted rhoProc (canonicalize (read v)) ∧ IsCanonical (canonicalize (read v)) :=
  ⟨(RhoClosedTerm.canonicalize (rowProcess v closed)).2, Canonical.canonicalize_isCanonical _⟩

theorem prime_input {v : G [] .pr} (closed : Closed v) {C B : Pattern}
    (shape : canonicalize (read v) = input C B) : IsPrime (input C B) := by
  obtain ⟨typed, canonical⟩ := canonical_row v closed
  rw [shape] at typed canonical
  exact ⟨typed, canonical, by simp [input], fun _ same => by simp [input] at same⟩

theorem prime_output {v : G [] .pr} (closed : Closed v) {C Q : Pattern}
    (shape : canonicalize (read v) = output C Q) : IsPrime (output C Q) := by
  obtain ⟨typed, canonical⟩ := canonical_row v closed
  rw [shape] at typed canonical
  exact ⟨typed, canonical, by simp [output], fun _ same => by simp [output] at same⟩

/-- The canonical form of the read-back of an input. -/
theorem canonical_inputT (c : G [] .nm) (b : G [.nm, .pr] .pr) :
    canonicalize (read (inputT c b)) = input (canonicalize (read c)) (canonicalize (read b)) := by
  show canonicalize (.apply "PInput" [read c, .lambda none (read b)]) = _
  rw [CanonicalStepperCompleteness.canonicalize_input]
  rfl

theorem canonical_outputT (c : G [] .nm) (p : G [] .pr) :
    canonicalize (read (outputT c p)) = output (canonicalize (read c)) (canonicalize (read p)) := by
  show canonicalize (.apply "POutput" [read c, read p]) = _
  rw [CanonicalStepperCompleteness.canonicalize_output]
  rfl

/-- Similar terms have the same canonical read-back. -/
theorem similar_canonical {Γ : Ctx sig} {s : Srt} {t t' : G Γ s} (similar : Similar t t') :
    canonicalize (read t) = canonicalize (read t') :=
  Canonical.canonicalize_eq_of_structuralCongruence (similar_sound similar)
    (read_hashSetFree t) (read_hashSetFree t')

theorem primes_of_canonical_prime {v : G [] .pr} {pattern : Pattern}
    (shape : canonicalize (read v) = pattern) (prime : IsPrime pattern) :
    primes (read v) = {pattern} := by
  rw [← primes_canonicalize, shape, primes_of_isPrime prime]

/-! ## Facts about every firing -/

/-- The frame a firing extends to. -/
abbrev target {s : State} (f : Firing s) : Interface.Frames.Frame sig :=
  (RuleSyntax.Contextual.declarations sig).target f.ext

/-- The weakening of the state's frame into the firing's frame. -/
abbrev weakening {s : State} (f : Firing s) : Assignment s.frame.arity (target f).arity :=
  (RuleSyntax.Contextual.declarations sig).weaken f.ext

section FiringFacts

variable {s : State} (f : Firing s)

/-- A grounding solving the information restricts to one solving the knowledge. -/
theorem ground_knowledge {g' : Grounding (target f)}
    (solved : GroundSolves g' (f.information knowledge s)) :
    GroundSolves (Assignment.compose g' (weakening f)) s.knowledge := by
  intro e member
  have inside : (knowledge.act (weakening f) e.1, knowledge.act (weakening f) e.2) ∈
      f.information knowledge s :=
    List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
      (List.mem_map.mpr ⟨e, member, rfl⟩)))
  have similar := solved _ inside
  change ObsSimilar (instantiateObservation g' (instantiateObservation (weakening f) e.1))
    (instantiateObservation g' (instantiateObservation (weakening f) e.2)) at similar
  rwa [instantiateObservation_comp, instantiateObservation_comp] at similar

/-- A grounding solving the information equates each opened take pattern with its row. -/
theorem ground_take {g' : Grounding (target f)}
    (solved : GroundSolves g' (f.information knowledge s)) {p : Observation sig f.rule.locals.arity}
    {o : ℕ} (inside : (knowledge.act f.opening p, o) ∈ (f.opened knowledge).take.zip f.selection.taken) :
    ObsSimilar (instantiateObservation (Assignment.compose g' f.opening) p)
      (instantiateObservation (Assignment.compose g' (weakening f)) (s.label o)) := by
  have member := f.matching_mem (X := knowledge) inside
  have similar := solved _ (List.mem_append_left _ (List.mem_append_left _
    (List.mem_append_right _ member)))
  change ObsSimilar (instantiateObservation g' (instantiateObservation f.opening p))
    (instantiateObservation g' (instantiateObservation (weakening f) (s.label o))) at similar
  rwa [instantiateObservation_comp, instantiateObservation_comp] at similar

/-- Under a grounding of the result, a kept row is its old row under the restricted grounding. -/
theorem ground_kept (g' : Grounding (target f)) {o : ℕ} (kept : o ∉ f.selection.made) :
    instantiateObservation g' ((f.result knowledge s).label o) =
      instantiateObservation (Assignment.compose g' (weakening f)) (s.label o) := by
  rw [RuleSyntax.Firing.result_label_other f kept]
  change instantiateObservation g' (instantiateObservation (weakening f) (s.label o)) = _
  rw [instantiateObservation_comp]

/-- Under a grounding of the result, a made row is its opened made pattern. -/
theorem ground_made (g' : Grounding (target f)) (shapes : f.Shapes knowledge s) {o : ℕ}
    {p : Observation sig f.rule.locals.arity}
    (inside : (o, knowledge.act f.opening p) ∈ f.selection.made.zip (f.opened knowledge).produce) :
    instantiateObservation g' ((f.result knowledge s).label o) =
      instantiateObservation (Assignment.compose g' f.opening) p := by
  rw [RuleSyntax.Firing.result_label_made f shapes inside]
  change instantiateObservation g' (instantiateObservation f.opening p) = _
  rw [instantiateObservation_comp]

theorem result_present_eq :
    (f.result knowledge s).present = (s.present \ f.selection.taken.toFinset) ∪
      f.selection.made.toFinset := rfl

end FiringFacts

/-- An observation of a closed process term, after grounding. -/
theorem obs_closed_similar {u v w : G [] .pr}
    (first : ObsSimilar ⟨[], .pr, u⟩ ⟨[], .pr, v⟩) (second : Similar v w) : Similar u w :=
  similar_trans (obsSimilar_closed.mp first) second

theorem similar_input_input {Γ : Ctx sig} {c c' : G Γ .nm} {b b' : G (.nm :: .pr :: Γ) .pr}
    (similar : Similar (inputT c b) (inputT c' b')) : Similar c c' ∧ Similar b b' := by
  cases similar with
  | input channel body => exact ⟨channel, body⟩

theorem similar_output_output {Γ : Ctx sig} {c c' : G Γ .nm} {p p' : G Γ .pr}
    (similar : Similar (outputT c p) (outputT c' p')) : Similar c c' ∧ Similar p p' := by
  cases similar with
  | output channel payload => exact ⟨channel, payload⟩

/-! ## Communication -/

/-- **What a communication firing does.** -/
theorem comm_effect {s : State} {P : RhoProcess} {value : ℕ → G [] .pr}
    (represented : RepresentsBy s P value) (f : Firing s) (isComm : f.rule = commRule)
    (admitted : f.Admits knowledge s) :
    ∃ (o₁ o₂ : ℕ) (rule : GroundComm) (value' : ℕ → G [] .pr),
      f.selection.taken = [o₁, o₂] ∧
      canonicalize (read (value o₁)) = input rule.inputChannel rule.body ∧
      canonicalize (read (value o₂)) = output rule.outputChannel rule.payload ∧
      (fromProcess P).1 = rule.redex.1 + inventoryOf (s.present \ {o₁, o₂}) value ∧
      ∀ Q : RhoProcess,
        (fromProcess Q).1 = rule.reactum.1 + inventoryOf (s.present \ {o₁, o₂}) value →
          RepresentsBy (f.result knowledge s) Q value' := by
  classical
  obtain ⟨rule, member, ext, opening, ⟨taken, readSel, made⟩, seen⟩ := f
  change rule = commRule at isComm
  subst isComm
  obtain ⟨⟨fresh, takenNodup, madeNodup, takeLen, readLen, produceLen, collectLen⟩, enabled, solvable,
    asks⟩ := admitted
  change 2 = taken.length at takeLen
  change 0 = readSel.length at readLen
  change 1 = made.length at produceLen
  obtain ⟨o₁, o₂, rfl⟩ := List.length_eq_two.mp takeLen.symm
  obtain rfl := List.eq_nil_of_length_eq_zero readLen.symm
  obtain ⟨o₃, rfl⟩ := List.length_eq_one_iff.mp produceLen.symm
  let fir : Firing s := ⟨commRule, member, ext, opening, ⟨[o₁, o₂], [], [o₃]⟩, seen⟩
  have shapes : fir.Shapes knowledge s :=
    ⟨fresh, takenNodup, madeNodup, takeLen, readLen, produceLen, collectLen⟩
  have distinct : o₁ ≠ o₂ := by simpa using takenNodup
  have present₁ : o₁ ∈ s.present := enabled.taken_subset (by simp [Selection.commit])
  have present₂ : o₂ ∈ s.present := enabled.taken_subset (by simp [Selection.commit])
  have fresh₃ : o₃ ∉ s.present := by
    have apart := enabled.fresh
    simp only [Selection.commit, List.toFinset_cons, List.toFinset_nil, insert_empty_eq] at apart
    exact Finset.disjoint_singleton_left.mp apart
  -- what every solution of the information says about the two taken rows
  have takes : ∀ g' : Grounding (target fir), GroundSolves g' (fir.information knowledge s) →
      Similar (inputT ((Assignment.compose g' opening) .channel) ((Assignment.compose g' opening) .body))
        (value o₁) ∧
      Similar (outputT ((Assignment.compose g' opening) .channel)
        ((Assignment.compose g' opening) .payload)) (value o₂) := by
    intro g' solved
    have known := ground_knowledge fir solved
    obtain ⟨u₁, at₁, similar₁⟩ := represented.determined _ known o₁ present₁
    obtain ⟨u₂, at₂, similar₂⟩ := represented.determined _ known o₂ present₂
    have first := ground_take fir solved (p := obs commInput) (o := o₁) (by
      simp [fir, RuleSyntax.Firing.opened, RuleInstance.map])
    have second := ground_take fir solved (p := obs commOutput) (o := o₂) (by
      simp [fir, RuleSyntax.Firing.opened, RuleInstance.map])
    rw [at₁] at first
    rw [at₂] at second
    change ObsSimilar ⟨[], .pr, instantiate (Assignment.compose g' opening) commInput⟩ _ at first
    change ObsSimilar ⟨[], .pr, instantiate (Assignment.compose g' opening) commOutput⟩ _ at second
    rw [instantiate_commInput] at first
    rw [instantiate_commOutput] at second
    exact ⟨obs_closed_similar first similar₁, obs_closed_similar second similar₂⟩
  obtain ⟨g₀, solved₀⟩ := (solvable_iff _).mp solvable
  obtain ⟨inputSimilar₀, outputSimilar₀⟩ := takes g₀ solved₀
  obtain ⟨c₁, b₁, shape₁, channel₁, _⟩ := similar_input_inv (Γ := ([] : Ctx sig)) inputSimilar₀
  obtain ⟨c₂, q₂, shape₂, channel₂, _⟩ := similar_output_inv (Γ := ([] : Ctx sig)) outputSimilar₀
  have closed₁ := represented.closed o₁ present₁
  have closed₂ := represented.closed o₂ present₂
  rw [shape₁] at closed₁
  rw [shape₂] at closed₂
  have parts₁ : binderSafeAt "NQuote" 0 (read c₁) = true ∧
      binderSafeAt "NQuote" 1 (read b₁) = true := by
    have unfolded : binderSafeAt "NQuote" 0
        (.apply "PInput" [read c₁, .lambda none (read b₁)]) = true := closed₁
    simpa [binderSafeAt, binderSafeListAt] using unfolded
  have parts₂ : binderSafeAt "NQuote" 0 (read c₂) = true ∧
      binderSafeAt "NQuote" 0 (read q₂) = true := by
    have unfolded : binderSafeAt "NQuote" 0 (.apply "POutput" [read c₂, read q₂]) = true := closed₂
    simpa [binderSafeAt, binderSafeListAt] using unfolded
  -- the ground communication of the source
  have meaning₁ : canonicalize (read (value o₁)) =
      input (canonicalize (read c₁)) (canonicalize (read b₁)) := by
    rw [shape₁, canonical_inputT]
  have meaning₂ : canonicalize (read (value o₂)) =
      output (canonicalize (read c₂)) (canonicalize (read q₂)) := by
    rw [shape₂, canonical_outputT]
  have channels : canonicalize (read c₁) = canonicalize (read c₂) :=
    similar_canonical (similar_trans (similar_symm channel₁) channel₂)
  let ground : GroundComm := ⟨canonicalize (read c₁), canonicalize (read c₂), canonicalize (read b₁),
    canonicalize (read q₂), prime_input (represented.closed o₁ present₁) meaning₁,
    prime_output (represented.closed o₂ present₂) meaning₂, by rw [channels]⟩
  let made₃ : G [] .pr := bind (received q₂) b₁
  let value' : ℕ → G [] .pr := fun o => if o = o₃ then made₃ else value o
  have keep : ∀ o ∈ s.present, value' o = value o := by
    intro o member
    have different : o ≠ o₃ := fun same => fresh₃ (same ▸ member)
    simp only [value', different, if_false]
  have takenSub : ({o₁, o₂} : Finset ℕ) ⊆ s.present := by
    intro o member
    simp only [Finset.mem_insert, Finset.mem_singleton] at member
    rcases member with rfl | rfl
    · exact present₁
    · exact present₂
  refine ⟨o₁, o₂, ground, value', rfl, meaning₁, meaning₂, ?_, ?_⟩
  · -- the redex and the other rows
    rw [← represented.inventory_eq]
    unfold inventoryOf
    rw [← Finset.sum_sdiff takenSub, Finset.sum_pair distinct,
      primes_of_canonical_prime meaning₁ ground.inputPrime,
      primes_of_canonical_prime meaning₂ ground.outputPrime, add_comm]
    rfl
  · intro Q readsQ
    have resultPresent : (fir.result knowledge s).present = (s.present \ {o₁, o₂}) ∪ {o₃} := by
      rw [result_present_eq]
      simp [fir]
    have madeCanonical : canonicalize (read made₃) = canonicalize ground.result.1 := by
      rw [contractum_by_instantiation_canonical b₁ q₂ parts₁.2 parts₂.2]
      rfl
    refine ⟨⟨g₀, solved₀⟩, ?_, ?_, ?_⟩
    · intro g' solved o member
      rw [resultPresent] at member
      rcases Finset.mem_union.mp member with kept | new
      · have keptOld := Finset.mem_sdiff.mp kept
        have different : o ≠ o₃ := fun same => fresh₃ (same ▸ keptOld.1)
        obtain ⟨u, at', similar⟩ :=
          represented.determined _ (ground_knowledge fir solved) o keptOld.1
        refine ⟨u, (ground_kept fir g' (by simpa [fir] using different)).trans at', ?_⟩
        rw [keep o keptOld.1]
        exact similar
      · rw [Finset.mem_singleton] at new
        subst new
        refine ⟨bind (received ((Assignment.compose g' opening) .payload))
          ((Assignment.compose g' opening) .body),
          (ground_made fir g' shapes (p := obs commMade) (by
            simp [fir, RuleSyntax.Firing.opened, RuleInstance.map])).trans ?_, ?_⟩
        · show (⟨[], .pr, instantiate (Assignment.compose g' opening) commMade⟩ :
            Observation sig noUnknowns) = _
          rw [made_instantiation_ground]
          rfl
        · obtain ⟨inputSimilar, outputSimilar⟩ := takes g' solved
          rw [shape₁] at inputSimilar
          rw [shape₂] at outputSimilar
          simp only [value', if_true]
          exact similar_made (similar_input_input inputSimilar).2
            (similar_output_output outputSimilar).2
    · intro o member
      rw [resultPresent] at member
      rcases Finset.mem_union.mp member with kept | new
      · rw [keep o (Finset.mem_sdiff.mp kept).1]
        exact represented.closed o (Finset.mem_sdiff.mp kept).1
      · rw [Finset.mem_singleton] at new
        subst new
        simp only [value', if_true]
        exact (instantiation_sealed b₁ q₂ parts₁.2 parts₂.2).2
    · rw [readsQ]
      unfold inventoryOf
      rw [resultPresent, Finset.sum_union (Finset.disjoint_singleton_right.mpr
        (fun inside => fresh₃ (Finset.mem_sdiff.mp inside).1)), Finset.sum_singleton]
      have rest : ∑ o ∈ s.present \ {o₁, o₂}, primes (read (value' o)) =
          ∑ o ∈ s.present \ {o₁, o₂}, primes (read (value o)) :=
        Finset.sum_congr rfl fun o member => by rw [keep o (Finset.mem_sdiff.mp member).1]
      rw [rest, add_comm]
      congr 1
      simp only [value', if_true]
      rw [← primes_canonicalize, madeCanonical, primes_canonicalize]
      rfl

#print axioms comm_effect

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FragmentsOfTheStep.ReflectiveCalculus.ByInstantiation
