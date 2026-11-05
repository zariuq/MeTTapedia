import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualRuleCode
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualConditionalClauses

/-!
# A stored rule declaration constructs its own operative source clause

The declaration supplies its actual body, repetition profile and production
intents as syntax data. Its locals become the invocation's query variables;
the selected code read opens a separate private copy in the same firing.
The code occurrence is read, not consumed and republished.

This is the source entry for structurally quoted declarations. The indexed
events and scheduler transport its actual family-changing firings; a fixed
label per physical occurrence does not supply that transport.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualStandingEntry

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits
open ContextualRuleCode ContextualConjunctiveQueries

variable {S : Signature} {atom : S.Srt} {Local Shared O : Type}
    (locals : Local → MetaArity (codeSignature S atom)) (captures : Shared → MetaArity (codeSignature S atom))
    {Γ : Ctx S}

def activation (declaration : Declaration
    (Term (signature (codeSignature S atom) (ContextualSelectionViews.source locals captures)) Γ atom)) :
    ContextualPublication.Plan (Term (signature (codeSignature S atom) (queryFamily locals captures)) Γ atom) where
  rule := {declaration.plan.rule with read := encodeDeclaration declaration :: declaration.plan.rule.read}
  reusable := declaration.plan.reusable
  shape := declaration.plan.shape

def selected (installation : O) (picked : Selection O) : Selection O :=
  StandingRuleRows.selection installation picked

variable [DecidableEq O]
    (before : ContextualConditionalExecution.State locals O Γ atom)

structure Admitted (installation : O)
    (declaration : Declaration (Term (signature (codeSignature S atom) (ContextualSelectionViews.source locals before.declarations)) Γ atom))
    (picked : Selection O) : Prop where
  code_at : ContextualStoredRows.asTemplate locals before.declarations (before.rows installation).value = encodeDeclaration declaration
  body : ContextualConditionalSourceAdmission.Admitted locals locals before.declarations
    (selected installation picked) (activation locals before.declarations declaration).rule
    before.rows before.equations before.present

theorem admitted_decodes (installation : O)
    (declaration : Declaration (Term (signature (codeSignature S atom) (ContextualSelectionViews.source locals before.declarations)) Γ atom))
    (picked : Selection O) (admitted : Admitted locals before installation declaration picked) :
    decodeDeclaration (ContextualStoredRows.asTemplate locals before.declarations (before.rows installation).value) = some declaration := by
  rw [admitted.code_at, decode_encodeDeclaration]

variable [DecidableEq Local] [DecidableEq S.Srt] [∀ sort, DecidableEq (S.Op sort)]

structure Compiled (installation : O)
    (declaration : Declaration (Term (signature (codeSignature S atom) (ContextualSelectionViews.source locals before.declarations)) Γ atom))
    (picked : Selection O) where
  code_at : ContextualStoredRows.asTemplate locals before.declarations (before.rows installation).value = encodeDeclaration declaration
  actual : ContextualConditionalClauses.Compiled locals locals (before := before)
    (activation locals before.declarations declaration) (selected installation picked)

theorem realize (installation : O)
    (declaration : Declaration (Term (signature (codeSignature S atom) (ContextualSelectionViews.source locals before.declarations)) Γ atom))
    (picked : Selection O) (admitted : Admitted locals before installation declaration picked) (fuel : Nat) :
    ∃ compiled : Compiled locals before installation declaration picked, compiled.actual.firing.fuel = fuel := by
  obtain ⟨actual, budget⟩ := ContextualConditionalClauses.realize locals locals (before := before)
    (activation locals before.declarations declaration) (selected installation picked) admitted.body fuel
  exact ⟨⟨admitted.code_at, actual⟩, budget⟩

namespace Compiled

variable {locals before} {installation : O}
    {declaration : Declaration (Term (signature (codeSignature S atom) (ContextualSelectionViews.source locals before.declarations)) Γ atom)}
    {picked : Selection O}

theorem source_admitted (compiled : Compiled locals before installation declaration picked) :
    Admitted locals before installation declaration picked := ⟨compiled.code_at, compiled.actual.source_admitted⟩

theorem installation_kept (compiled : Compiled locals before installation declaration picked) :
    installation ∈ compiled.actual.firing.target.present := by
  have admitted := compiled.actual.source_admitted
  have present : installation ∈ before.present := admitted.read_present (by simp [selected, StandingRuleRows.selection])
  have notTaken : installation ∉ picked.taken := by
    intro member
    exact Finset.disjoint_left.mp admitted.apart (List.mem_toFinset.mpr member)
      (by simp [selected, StandingRuleRows.selection])
  rw [compiled.actual.physical_result]
  apply Finset.mem_union_left
  exact Finset.mem_sdiff.mpr ⟨present, by simpa only [selected, StandingRuleRows.selection, Selection.commit, List.mem_toFinset] using notTaken⟩

end Compiled

theorem source_iff_compiled (installation : O)
    (declaration : Declaration (Term (signature (codeSignature S atom) (ContextualSelectionViews.source locals before.declarations)) Γ atom))
    (picked : Selection O) (fuel : Nat) :
    Admitted locals before installation declaration picked ↔
      ∃ compiled : Compiled locals before installation declaration picked, compiled.actual.firing.fuel = fuel :=
  ⟨fun admitted => realize locals before installation declaration picked admitted fuel,
    fun ⟨compiled, _⟩ => compiled.source_admitted⟩

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualStandingEntry
