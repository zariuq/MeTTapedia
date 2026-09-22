import Mettapedia.GSLT.Parsing.PlainBnfDeclarationEncoding
import Mettapedia.GSLT.Parsing.PlainBnfDeclarationSource

/-!
# Source paths realizing the complete typed BNF declaration pass

Each semantic constructor is realized by its authenticated source occurrence,
with explicit ground substitutions and ordered premise paths. Name canonicality
is required exactly where the source uses its canonicalizing disequality provider.
This is finite source-path existence, not native execution, answer enumeration,
or a reverse source-path theorem.
-/

namespace Mettapedia.GSLT.Parsing.PlainBnfDeclarationRealization

open HornCertificate HornIntegerProvider
open PlainBnfDeclarationEncoding
open PlainBnfDeclarationSemantics PlainBnfDeclarationSource

def CanonicalDefinitions (definitions : List (Definition GroundTerm GroundTerm GroundTerm)) : Prop :=
  ∀ definition ∈ definitions, AliasFree definition.name

inductive CanonicalEntry : Entry GroundTerm GroundTerm GroundTerm GroundTerm → Prop where
  | rule {name : GroundTerm} (expression span : GroundTerm) (nameCanonical : AliasFree name) :
      CanonicalEntry (.rule name expression span)
  | comment (text span : GroundTerm) : CanonicalEntry (.comment text span)
  | blank (span : GroundTerm) : CanonicalEntry (.blank span)

def CanonicalEntries (entries : List (Entry GroundTerm GroundTerm GroundTerm GroundTerm)) : Prop :=
  ∀ entry ∈ entries, CanonicalEntry entry

def differentGoal (left right : GroundTerm) : GroundAtom :=
  ⟨"different", GroundTerms.ofList [left, right]⟩

def DifferentRealizes (program : Program) : Prop :=
  ∀ left right, AliasFree left → AliasFree right → left ≠ right →
    Realizable program (differentGoal left right)

def lookupGoal (name : GroundTerm) (definitions : List (Definition GroundTerm GroundTerm GroundTerm))
    (result : LookupResult GroundTerm GroundTerm) : GroundAtom :=
  ⟨"BNFDefinitionLookupV1", GroundTerms.ofList
    [name, encodeDefinitions definitions, encodeLookupResult result]⟩

def appendDefinitionGoal (before : List (Definition GroundTerm GroundTerm GroundTerm)) (definition :
    Definition GroundTerm GroundTerm GroundTerm)
    (after : List (Definition GroundTerm GroundTerm GroundTerm)) : GroundAtom :=
  ⟨"BNFAppendDefinitionV1", GroundTerms.ofList
    [encodeDefinitions before, encodeDefinition definition, encodeDefinitions after]⟩

def appendDiagnosticsGoal (left right after : List (Diagnostic GroundTerm GroundTerm)) : GroundAtom :=
  ⟨"BNFAppendDiagnosticsV1", GroundTerms.ofList
    [encodeDiagnostics left, encodeDiagnostics right, encodeDiagnostics after]⟩

def definitionStepGoal (name span expression : GroundTerm) (result : LookupResult GroundTerm GroundTerm)
    (before after : List (Definition GroundTerm GroundTerm GroundTerm)) (diagnostics : List (Diagnostic
        GroundTerm GroundTerm)) : GroundAtom :=
  ⟨"BNFDefinitionStepV1", GroundTerms.ofList
    [name, span, expression, encodeLookupResult result, encodeDefinitions before,
      encodeDefinitions after, encodeDiagnostics diagnostics]⟩

def collectGoal (entries : List (Entry GroundTerm GroundTerm GroundTerm GroundTerm)) (before after : List
    (Definition GroundTerm GroundTerm GroundTerm))
    (diagnostics : List (Diagnostic GroundTerm GroundTerm)) : GroundAtom :=
  ⟨"BNFCollectDefinitionsV1", GroundTerms.ofList
    [encodeEntries entries, encodeDefinitions before, encodeDefinitions after,
      encodeDiagnostics diagnostics]⟩

theorem lookup_realizable {program : Program} {offset : Nat}
    (source : HasDeclarationRules program offset) (different : DifferentRealizes program)
    {name : GroundTerm} {definitions : List (Definition GroundTerm GroundTerm GroundTerm)} {result :
        LookupResult GroundTerm GroundTerm}
    (derivation : Lookup name definitions result) (canonicalName : AliasFree name)
    (canonicalDefinitions : CanonicalDefinitions definitions) :
    Realizable program (lookupGoal name definitions result) := by
  induction derivation with
  | missing =>
      apply Realizable.rule (source ⟨0, by decide⟩)
        (substitution := [(0, name)]) (premises := []) (by rfl) (by rfl) (by rfl)
      intro child member
      cases member
  | found head tail equal =>
      subst name
      apply Realizable.rule (source ⟨1, by decide⟩)
        (substitution := [(0, head.name), (1, head.expression), (2, head.span),
          (3, encodeDefinitions tail)]) (premises := []) (by rfl) (by rfl) (by rfl)
      intro child member
      cases member
  | tail head tail unequal rest ih =>
      have tailCanonical : CanonicalDefinitions tail :=
        fun definition member => canonicalDefinitions definition (by simp [member])
      apply Realizable.rule (source ⟨2, by decide⟩)
        (substitution := [(0, name), (1, head.name), (2, head.expression), (3, head.span),
          (4, encodeDefinitions tail), (5, encodeLookupResult _)])
        (premises := [differentGoal name head.name, lookupGoal name tail _])
        (by rfl) (by rfl) (by rfl)
      intro child member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact different name head.name canonicalName
          (canonicalDefinitions head (by simp)) unequal
      · exact ih tailCanonical

theorem appendDefinition_realizable {program : Program} {offset : Nat}
    (source : HasDeclarationRules program offset)
    {before after : List (Definition GroundTerm GroundTerm GroundTerm)} {definition : Definition GroundTerm
        GroundTerm GroundTerm}
    (derivation : AppendDefinition before definition after) :
    Realizable program (appendDefinitionGoal before definition after) := by
  induction derivation with
  | nil definition =>
      apply Realizable.rule (source ⟨3, by decide⟩)
        (substitution := [(0, encodeDefinition definition)]) (premises := [])
        (by rfl) (by rfl) (by rfl)
      intro child member
      cases member
  | @cons head tail definition after rest ih =>
      apply Realizable.rule (source ⟨4, by decide⟩)
        (substitution := [(0, encodeDefinition head), (1, encodeDefinitions tail),
          (2, encodeDefinition definition), (3, encodeDefinitions after)])
        (premises := [appendDefinitionGoal tail definition after])
        (by rfl) (by rfl) (by rfl)
      intro child member
      have equal := List.mem_singleton.mp member
      exact equal ▸ ih

theorem appendDiagnostics_realizable {program : Program} {offset : Nat}
    (source : HasDeclarationRules program offset)
    {left right after : List (Diagnostic GroundTerm GroundTerm)}
    (derivation : AppendDiagnostics left right after) :
    Realizable program (appendDiagnosticsGoal left right after) := by
  induction derivation with
  | nil right =>
      apply Realizable.rule (source ⟨5, by decide⟩)
        (substitution := [(0, encodeDiagnostics right)]) (premises := [])
        (by rfl) (by rfl) (by rfl)
      intro child member
      cases member
  | @cons head tail right after rest ih =>
      apply Realizable.rule (source ⟨6, by decide⟩)
        (substitution := [(0, encodeDiagnostic head), (1, encodeDiagnostics tail),
          (2, encodeDiagnostics right), (3, encodeDiagnostics after)])
        (premises := [appendDiagnosticsGoal tail right after])
        (by rfl) (by rfl) (by rfl)
      intro child member
      have equal := List.mem_singleton.mp member
      exact equal ▸ ih

theorem definitionStep_realizable {program : Program} {offset : Nat}
    (source : HasDeclarationRules program offset)
    {name span expression : GroundTerm} {result : LookupResult GroundTerm GroundTerm}
    {before after : List (Definition GroundTerm GroundTerm GroundTerm)} {diagnostics : List (Diagnostic
        GroundTerm GroundTerm)}
    (derivation : DefinitionStep name span expression result before after diagnostics) :
    Realizable program (definitionStepGoal name span expression result before after diagnostics) := by
  cases derivation with
  | fresh append =>
      apply Realizable.rule (source ⟨7, by decide⟩)
        (substitution := [(0, name), (1, span), (2, expression),
          (3, encodeDefinitions before), (4, encodeDefinitions after)])
        (premises := [appendDefinitionGoal before ⟨name, expression, span⟩ after])
        (by rfl) (by rfl) (by rfl)
      intro child member
      have equal := List.mem_singleton.mp member
      exact equal ▸ appendDefinition_realizable source append
  | duplicate firstExpression firstSpan before =>
      apply Realizable.rule (source ⟨8, by decide⟩)
        (substitution := [(0, name), (1, span), (2, expression),
          (3, firstExpression), (4, firstSpan), (5, encodeDefinitions before)])
        (premises := []) (by rfl) (by rfl) (by rfl)
      intro child member
      cases member

theorem definitionStep_preserves_canonical {name span expression : GroundTerm}
    {result : LookupResult GroundTerm GroundTerm} {before after : List (Definition GroundTerm GroundTerm
        GroundTerm)} {diagnostics : List (Diagnostic GroundTerm GroundTerm)}
    (derivation : DefinitionStep name span expression result before after diagnostics)
    (canonicalName : AliasFree name) (canonicalBefore : CanonicalDefinitions before) :
    CanonicalDefinitions after := by
  cases derivation with
  | fresh append =>
      rw [append.result_eq]
      intro definition member
      simp only [List.mem_append, List.mem_singleton] at member
      rcases member with member | rfl
      · exact canonicalBefore definition member
      · exact canonicalName
  | duplicate => exact canonicalBefore

theorem collect_preserves_canonical {entries : List (Entry GroundTerm GroundTerm GroundTerm GroundTerm)}
    {before after : List (Definition GroundTerm GroundTerm GroundTerm)} {diagnostics : List (Diagnostic
        GroundTerm GroundTerm)}
    (derivation : Collect entries before after diagnostics)
    (canonicalEntries : CanonicalEntries entries) (canonicalBefore : CanonicalDefinitions before) :
    CanonicalDefinitions after := by
  induction derivation with
  | nil => exact canonicalBefore
  | comment text span rest ih =>
      exact ih (fun entry member => canonicalEntries entry (by simp [member])) canonicalBefore
  | blank span rest ih =>
      exact ih (fun entry member => canonicalEntries entry (by simp [member])) canonicalBefore
  | rule name expression span lookup step rest append ih =>
      have canonicalName : AliasFree name := by
        cases canonicalEntries (.rule name expression span) (by simp) with
        | rule _ _ nameCanonical => exact nameCanonical
      exact ih (fun entry member => canonicalEntries entry (by simp [member]))
        (definitionStep_preserves_canonical step canonicalName canonicalBefore)

theorem collect_realizable {program : Program} {offset : Nat}
    (source : HasDeclarationRules program offset) (different : DifferentRealizes program)
    {entries : List (Entry GroundTerm GroundTerm GroundTerm GroundTerm)} {before after : List (Definition
        GroundTerm GroundTerm GroundTerm)} {diagnostics : List (Diagnostic GroundTerm GroundTerm)}
    (derivation : Collect entries before after diagnostics)
    (canonicalEntries : CanonicalEntries entries) (canonicalBefore : CanonicalDefinitions before) :
    Realizable program (collectGoal entries before after diagnostics) := by
  induction derivation with
  | nil before =>
      apply Realizable.rule (source ⟨9, by decide⟩)
        (substitution := [(0, encodeDefinitions before)]) (premises := [])
        (by rfl) (by rfl) (by rfl)
      intro child member
      cases member
  | @comment text span tail before after diagnostics rest ih =>
      apply Realizable.rule (source ⟨10, by decide⟩)
        (substitution := [(0, text), (1, span), (2, encodeEntries tail),
          (3, encodeDefinitions before), (4, encodeDefinitions after),
          (5, encodeDiagnostics diagnostics)])
        (premises := [collectGoal tail before after diagnostics])
        (by rfl) (by rfl) (by rfl)
      intro child member
      have equal := List.mem_singleton.mp member
      exact equal ▸ ih (fun entry member => canonicalEntries entry (by simp [member])) canonicalBefore
  | @blank span tail before after diagnostics rest ih =>
      apply Realizable.rule (source ⟨11, by decide⟩)
        (substitution := [(0, span), (1, encodeEntries tail),
          (2, encodeDefinitions before), (3, encodeDefinitions after),
          (4, encodeDiagnostics diagnostics)])
        (premises := [collectGoal tail before after diagnostics])
        (by rfl) (by rfl) (by rfl)
      intro child member
      have equal := List.mem_singleton.mp member
      exact equal ▸ ih (fun entry member => canonicalEntries entry (by simp [member])) canonicalBefore
  | @rule name expression span tail before next after result currentDiagnostics
      tailDiagnostics diagnostics lookup step rest append ih =>
      have canonicalName : AliasFree name := by
        cases canonicalEntries (.rule name expression span) (by simp) with
        | rule _ _ nameCanonical => exact nameCanonical
      have canonicalNext := definitionStep_preserves_canonical step canonicalName canonicalBefore
      apply Realizable.rule (source ⟨12, by decide⟩)
        (substitution := [(0, name), (1, expression), (2, span), (3, encodeEntries tail),
          (4, encodeDefinitions before), (5, encodeDefinitions after),
          (6, encodeDiagnostics diagnostics), (7, encodeLookupResult result),
          (8, encodeDefinitions next), (9, encodeDiagnostics currentDiagnostics),
          (10, encodeDiagnostics tailDiagnostics)])
        (premises := [lookupGoal name before result,
          definitionStepGoal name span expression result before next currentDiagnostics,
          collectGoal tail next after tailDiagnostics,
          appendDiagnosticsGoal currentDiagnostics tailDiagnostics diagnostics])
        (by rfl) (by rfl) (by rfl)
      intro child member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl
      · exact lookup_realizable source different lookup canonicalName canonicalBefore
      · exact definitionStep_realizable source step
      · exact ih (fun entry member => canonicalEntries entry (by simp [member])) canonicalNext
      · exact appendDiagnostics_realizable source append

/-- Every finite canonical input has a source path to exactly the independently
computed ordered definitions and diagnostics. -/
theorem collect_result_realizable {program : Program} {offset : Nat}
    (source : HasDeclarationRules program offset) (different : DifferentRealizes program)
    (entries : List (Entry GroundTerm GroundTerm GroundTerm GroundTerm)) (before : List (Definition GroundTerm
        GroundTerm GroundTerm))
    (canonicalEntries : CanonicalEntries entries) (canonicalBefore : CanonicalDefinitions before) :
    Realizable program (collectGoal entries before
      (collect entries before).1 (collect entries before).2) :=
  collect_realizable source different (collectDerivation entries before) canonicalEntries canonicalBefore

end Mettapedia.GSLT.Parsing.PlainBnfDeclarationRealization
