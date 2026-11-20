import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Concurrency.HostedAnswerReadings

/-!
# Real answer occurrences, dead helpers and missing labels

An actual completed answer row remains readable after adding a genuinely new unused frame name.
The existing source observer can also inspect the label of a missing occurrence; the physical-row
invariant deliberately rejects that ghost. This distinguishes the presence premise of the adapter
law from the semantic equation for labels alone.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Concurrency.HostedAnswerReadingsControls

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open SourceLanguage SourceLanguage.Elaboration SourceLanguage.Toolkit Hosting
open RuleSyntax.StepWeb.HostedNative
open NativeClosedReadings HostedAnswerReadings

abbrev N := mettaNodes

def value : Term MSig [] () := csym "one"

def hosted (present : Finset Nat) : HostState MSig :=
  ⟨⟨Empty, closedArity MSig⟩, [], present,
    fun _ => observe (closedAt (closedArity MSig) (answerPattern N value))⟩

def presented (present : Finset Nat) : Presented [] () (hosted present) where
  term _ := closedAt (closedArity MSig) (answerPattern N value)
  label_eq _ := rfl

theorem source_reads_one (present : Finset Nat) (occurrence : Nat) :
    value ∈ stateAnswer N (hosted present) occurrence := by
  refine ⟨⟨Empty, closedArity MSig⟩, generator (closedArity MSig), ?_, ?_⟩
  · exact (Frames.contextual MSig).models_nil _
  · change instantiateObservation (generator (closedArity MSig))
      (observe (closedAt (closedArity MSig) (answerPattern N value))) = _
    rw [instantiateObservation_identity, closedAt_answerPattern]

theorem source_answer_exact (present : Finset Nat) (occurrence : Nat) :
    stateAnswer N (hosted present) occurrence = {value} := by
  ext result
  constructor
  · rintro ⟨target, candidate, _, same⟩
    change instantiateObservation candidate
      (observe (closedAt (closedArity MSig) (answerPattern N value))) = _ at same
    change observe (instantiate candidate
      (closedAt (closedArity MSig) (answerPattern N value))) = _ at same
    have output := (closedAt_natural candidate (answerPattern N value)).symm.trans
      (observe_injective same)
    have patterns := closedAt_injective target.arity
      (output.trans (closedAt_answerPattern N target.arity result).symm)
    exact Set.mem_singleton_iff.mpr ((answerPattern_injective N) patterns).symm
  · intro member
    have same := Set.mem_singleton_iff.mp member
    subst result
    exact source_reads_one present occurrence

theorem present_native_reading :
    Reads (state mkeys (hosted {0}) (presented {0}) ∅) 0 (answerPattern N value) :=
  (reading_iff_stateAnswer N _ _ _ _ (by simp [hosted]) value).mpr (source_reads_one {0} 0)

theorem different_answer_refused :
    ¬ Reads (state mkeys (hosted {0}) (presented {0}) ∅) 0 (answerPattern N (csym "two")) := by
  intro read
  have source := (reading_iff_stateAnswer N _ _ _ _ (by simp [hosted]) (csym "two")).mp read
  rw [source_answer_exact] at source
  have same := Set.mem_singleton_iff.mp source
  have different : (csym "two" : Term MSig [] ()) ≠ value := by decide
  exact different same

theorem ghost_not_native_reading :
    ¬ Reads (state mkeys (hosted ∅) (presented ∅) ∅) 0 (answerPattern N value) := by
  rintro ⟨present, _⟩
  change 0 ∈ (∅ : Finset Nat) at present
  exact Finset.notMem_empty 0 present

theorem presence_cannot_be_omitted :
    value ∈ stateAnswer N (hosted ∅) 0 ∧
      ¬ Reads (state mkeys (hosted ∅) (presented ∅) ∅) 0 (answerPattern N value) :=
  ⟨source_reads_one ∅ 0, ghost_not_native_reading⟩

def extraDeclarations : Unit → MetaArity MSig := fun _ => ([], ())

def grownHost (present : Finset Nat) : HostState MSig :=
  ⟨⟨Unit, extraDeclarations⟩, [], present,
    fun _ => observe (closedAt extraDeclarations (answerPattern N value))⟩

def grownPresented (present : Finset Nat) : Presented [] () (grownHost present) where
  term _ := closedAt extraDeclarations (answerPattern N value)
  label_eq _ := rfl

noncomputable def embedding (present : Finset Nat) :
    NativeDead.Inclusion (state mkeys (hosted present) (presented present) ∅)
      (state mkeys (grownHost present) (grownPresented present) ∅) where
  locals := id
  locals_injective := Function.injective_id
  locals_preserves _ := rfl
  names := Empty.elim
  names_injective := by
    intro name
    exact Empty.elim name
  names_preserves name := Empty.elim name

noncomputable def extension (present : Finset Nat) :
    NativeDead.DeadExtension (state mkeys (hosted present) (presented present) ∅)
      (state mkeys (grownHost present) (grownPresented present) ∅) where
  toInclusion := embedding present
  rows occurrence := by
    change ContextualConditionalRows.ofStored (ruleLocals [] () mkeys) extraDeclarations
      (.shared (closedAt extraDeclarations (answerPattern N value))) =
      ContextualConditionalRows.ofStored (ruleLocals [] () mkeys) extraDeclarations
        (.shared (instantiate (embedding present).frame
          (closedAt (closedArity MSig) (answerPattern N value))))
    exact congrArg
      (fun term : Term (signature MSig extraDeclarations) [] () =>
        ContextualConditionalRows.ofStored (ruleLocals [] () mkeys) extraDeclarations (.shared term))
      (closedAt_natural (source := closedArity MSig) (target := extraDeclarations)
        (embedding present).frame (answerPattern N value)).symm
  equations := List.Perm.nil
  present := rfl
  occupied := rfl

theorem extra_name_is_genuinely_new (present : Finset Nat) :
    ¬ Function.Surjective (embedding present).names := by
  intro onto
  obtain ⟨name, _⟩ := onto ()
  exact Empty.elim name

theorem present_native_reading_after_extension :
    Reads (state mkeys (grownHost {0}) (grownPresented {0}) ∅) 0 (answerPattern N value) :=
  (deadExtension_reads_iff (extension {0}) 0 (answerPattern N value)).mpr present_native_reading

theorem existing_answer_preserved :
    stateAnswer N (hosted {0}) 0 = stateAnswer N (grownHost {0}) 0 :=
  stateAnswer_deadEquiv N (NativeDead.DeadEquiv.of_extension (extension {0})) 0
    (by simp [hosted])

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Concurrency.HostedAnswerReadingsControls
