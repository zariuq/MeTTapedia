import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.PresentationIntrinsicBinding
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualABTPreparation

/-! # Stored-schema preparation through authored, typed readback

Physical opening uses the existing freshening interpreter and scope ports.
Its values have exact intrinsic readback through the authored scalar grammar.
The head presentation is a named interpretation parameter. Prepared values
alone do not record their opening origin, nor certify permission to execute.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Presentation.SchemaPreparation

open Mettapedia.OSLF
open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open Mettapedia.GSLT.LanguageDef
open Mettapedia.Logic.LP (ScopedVar)

universe u
variable {S : Signature} {Local Shared : Type} {O : Type u}
  (locals : Local → MetaArity S) (captures : Shared → MetaArity S)

abbrev TargetSignature := signature S (ContextualSelectionViews.target locals captures)

variable (code : Intrinsic.HeadPresentation (TargetSignature locals captures))

def encodePhysical := SignatureIndexedABT.mapHeads (code.view (sort := ()))

def openRow? (scope : Nat) {Γ : Ctx S} {sort : S.Srt}
    (row : ContextualStoredRows.Row locals captures Γ sort) : Option Payloads.Term :=
  (ContextualABTPreparation.openRowAt locals captures scope row).map (encodePhysical locals captures code)

theorem openRow_exact (scope : Nat) {Γ : Ctx S} {sort : S.Srt}
    (row : ContextualStoredRows.Row locals captures Γ sort) :
    openRow? locals captures code scope row =
      some (Intrinsic.lower code (ContextualStoredRows.viewAt locals captures scope row)) := by
  rw [openRow?, ContextualABTPreparation.openRow_exact]
  rfl

def openRule? (scope : Nat) {Γ : Ctx S} {sort : S.Srt}
    (rule : RuleInstance (Term (signature S (ContextualSelectionViews.source locals captures)) Γ sort)) :
    Option (RuleInstance Payloads.Term) :=
  (ContextualABTPreparation.openRuleAt locals captures scope rule).map
    (RuleInstance.map (encodePhysical locals captures code))

theorem openRule_exact (scope : Nat) {Γ : Ctx S} {sort : S.Srt}
    (rule : RuleInstance (Term (signature S (ContextualSelectionViews.source locals captures)) Γ sort)) :
    openRule? locals captures code scope rule =
      some ((ContextualFreshening.ruleAt locals captures scope rule).map (Intrinsic.lower code)) := by
  rw [openRule?, ContextualABTPreparation.openRule_exact]
  change some (((ContextualFreshening.ruleAt locals captures scope rule).map Binding.CommonABT.lower).map
    (encodePhysical locals captures code)) = _
  rw [OccurrenceRelabeling.rule_map_comp]
  rfl

section Readback

variable [DecidableEq S.Srt]

def readRule? (Γ : Ctx S) (sort : S.Srt) (rule : RuleInstance Payloads.Term) :
    Option (RuleInstance (Term (TargetSignature locals captures) Γ sort)) :=
  rule.traverse? (Intrinsic.read? code Γ sort)

theorem read_mapped_rule {Γ : Ctx S} {sort : S.Srt}
    (rule : RuleInstance (Term (TargetSignature locals captures) Γ sort)) :
    readRule? locals captures code Γ sort (rule.map (Intrinsic.lower code)) = some rule :=
  RuleInstance.traverse?_map _ _ (Intrinsic.read_lower code) rule

noncomputable def readRuleSource? (Γ : Ctx S) (sort : S.Srt) (input : List Nat) :
    Option (RuleInstance (Term (TargetSignature locals captures) Γ sort)) := do
  let tree ← Source.parseTree "TcRule" input
  let pattern ← Mettapedia.GSLT.Parsing.LanguageDefScalarStructural.tree? tree
  let rule ← Payloads.readRule pattern
  readRule? locals captures code Γ sort rule

theorem readRuleSource_print {Γ : Ctx S} {sort : S.Srt}
    (rule : RuleInstance (Term (TargetSignature locals captures) Γ sort)) :
    readRuleSource? locals captures code Γ sort (Source.ruleInput (rule.map (Intrinsic.lower code))) = some rule := by
  obtain ⟨tree, erased, ⟨parsed⟩⟩ := Source.canonical_rule_source (rule.map (Intrinsic.lower code))
  simp only [readRuleSource?, Source.parseTree_of_derivation parsed]
  change (do
    let pattern ← Mettapedia.GSLT.Parsing.LanguageDefScalarStructural.tree? tree
    let raw ← Payloads.readRule pattern
    readRule? locals captures code Γ sort raw) = some rule
  rw [erased]
  change (Payloads.readRule (Payloads.rulePattern (rule.map (Intrinsic.lower code)))).bind
    (readRule? locals captures code Γ sort) = some rule
  rw [Payloads.readRule_pattern]
  exact read_mapped_rule locals captures code rule

theorem opened_rule_source_readback (scope : Nat) {Γ : Ctx S} {sort : S.Srt}
    (rule : RuleInstance (Term (signature S (ContextualSelectionViews.source locals captures)) Γ sort))
    {physical : RuleInstance Payloads.Term}
    (computed : openRule? locals captures code scope rule = some physical) :
    readRuleSource? locals captures code Γ sort (Source.ruleInput physical) =
      some (ContextualFreshening.ruleAt locals captures scope rule) := by
  rw [openRule_exact] at computed
  have same := Option.some.inj computed
  rw [← same]
  exact readRuleSource_print locals captures code _

theorem opened_value_readback (scope : Nat) {Γ : Ctx S} {sort : S.Srt}
    (row : ContextualStoredRows.Row locals captures Γ sort) {physical : Payloads.Term}
    (computed : openRow? locals captures code scope row = some physical) :
    Intrinsic.read? code Γ sort physical = some (ContextualStoredRows.viewAt locals captures scope row) := by
  rw [openRow_exact] at computed
  have same := Option.some.inj computed
  rw [← same]
  exact Intrinsic.read_lower code _

/-- Parsing the actual computed physical value recovers the intrinsic view
chosen by opening this row, not merely an equally named constructor. -/
theorem opened_source_readback (scope : Nat) {Γ : Ctx S} {sort : S.Srt}
    (row : ContextualStoredRows.Row locals captures Γ sort) {physical : Payloads.Term}
    (computed : openRow? locals captures code scope row = some physical) :
    Intrinsic.readSource? code Γ sort (Source.termInput physical) =
      some (ContextualStoredRows.viewAt locals captures scope row) := by
  rw [openRow_exact] at computed
  have same := Option.some.inj computed
  rw [← same]
  exact Intrinsic.readSource_print code _

theorem selected_read_source (occupied : Finset Nat) (selection : Selection O)
    {Γ : Ctx S} {sort : S.Srt}
    (rule : RuleInstance (Term (signature S (ContextualSelectionViews.source locals captures)) Γ sort))
    (rows : O → ContextualStoredRows.Row locals captures Γ sort) (port : Fin selection.read.length)
    {physical : Payloads.Term}
    (computed : (ContextualABTPreparation.readAt locals captures occupied selection rows port).map
      (encodePhysical locals captures code) = some physical) :
    Intrinsic.readSource? code Γ sort (Source.termInput physical) =
      some ((ContextualActivatedStep.prepared locals captures occupied selection rule rows).read port) := by
  rw [ContextualABTPreparation.read_exact locals captures occupied selection rule rows port] at computed
  have same := Option.some.inj computed
  rw [← same]
  exact Intrinsic.readSource_print code _

end Readback

theorem shared_value_unchanged (first second : Nat) {Γ : Ctx S} {sort : S.Srt}
    (value : Term (signature S captures) Γ sort) :
    openRow? locals captures code first (.shared value) = openRow? locals captures code second (.shared value) := by
  rw [openRow_exact, openRow_exact]
  rfl

theorem private_local_separates_encoded_uses {firstScope secondScope : Nat}
    (different : firstScope ≠ secondScope) {Γ : Ctx S} {sort : S.Srt}
    (first second : Term (signature S (ContextualSelectionViews.source locals captures)) Γ sort)
    (localName : Local) (occurs : Sum.inl localName ∈ support first) :
    openRow? locals captures code firstScope (.schema first) ≠
      openRow? locals captures code secondScope (.schema second) := by
  intro same
  rw [openRow_exact, openRow_exact] at same
  have intrinsic := Intrinsic.lower_injective code (Option.some.inj same)
  apply ContextualABTPreparation.private_local_separates_uses locals captures different first second localName occurs
  rw [ContextualABTPreparation.openTerm_exact, ContextualABTPreparation.openTerm_exact]
  exact congrArg (fun term => some (Binding.CommonABT.lower term)) intrinsic

/-- Opening origin is receipt data. Even a perfectly decoded shared value
cannot determine which opening produced it. -/
theorem value_cannot_recover_scope {Γ : Ctx S} {sort : S.Srt}
    (value : Term (signature S captures) Γ sort) :
    ¬ ∃ recover : Option Payloads.Term → Nat,
      ∀ scope, recover (openRow? locals captures code scope (.shared value)) = scope := by
  rintro ⟨recover, law⟩
  have same := congrArg recover (shared_value_unchanged locals captures code 0 1 value)
  rw [law 0, law 1] at same
  exact Nat.zero_ne_one same

#print axioms openRule_exact
#print axioms opened_rule_source_readback
#print axioms opened_source_readback
#print axioms selected_read_source
#print axioms private_local_separates_encoded_uses
#print axioms value_cannot_recover_scope

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Presentation.SchemaPreparation
