import Mettapedia.Languages.MeTTa.PureKernel.Universe.DeclarationHostedJudgments

/-!
# Source-faithful ingress for authored Prime constants

An authored declaration document and its extensional signature have different
information content.  The document retains every occurrence and its order;
the signature implements the nominal first-declaration-wins policy.  Raw
checker generation therefore needs an exact source witness for the declaration
that is active, rather than mere list membership.

`FirstConstant` is that proof-relevant witness.  It walks the authored source,
retaining skipped equations and differently named constants, and stops at the
first declaration of the requested name.  The main equivalence proves that
this source witness is exactly the fibre of extensional signature lookup.
Consequently an active authored occurrence constructs the existing
declaration-hosted Prime typing judgment directly.  No checker or parallel
typing calculus is introduced here; a generated raw-ingress presentation can
consume this exact interface later.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PureKernel.Universe
namespace AuthoredConstantIngress

open AuthoredDeclarationSignature
open DeclarationAwareFormedTyping
open DeclarationHostedJudgments
open Mettapedia.Languages.MeTTa.PureKernel.Universe.Presentation
open Mettapedia.Languages.MeTTa.PureKernel.Universe.Presentation.Declaration

/-! ## Exact first-occurrence evidence -/

/-- The first authored constant declaration with a requested name.  Equations
and differently named constants remain visible in the proof path; a constant
with the requested name cannot be skipped. -/
inductive FirstConstant :
    List SourceDeclaration -> DeclName -> Entry Tower.Head -> Type where
  | here (name : DeclName) (entry : Entry Tower.Head)
      (rest : List SourceDeclaration) :
      FirstConstant (.constant name entry :: rest) name entry
  | equation (schema : EquationSchema) {declarations : List SourceDeclaration}
      {name : DeclName} {entry : Entry Tower.Head}
      (later : FirstConstant declarations name entry) :
      FirstConstant (.equation schema :: declarations) name entry
  | other {otherName name : DeclName} (different : otherName ≠ name)
      (otherEntry : Entry Tower.Head) {declarations : List SourceDeclaration}
      {entry : Entry Tower.Head}
      (later : FirstConstant declarations name entry) :
      FirstConstant (.constant otherName otherEntry :: declarations) name entry

namespace FirstConstant

/-- The exact authored-source position selected by first-wins lookup. -/
def index : {declarations : List SourceDeclaration} ->
    {name : DeclName} -> {entry : Entry Tower.Head} ->
    FirstConstant declarations name entry -> Nat
  | _, _, _, .here _ _ _ => 0
  | _, _, _, .equation _ later => later.index + 1
  | _, _, _, .other _ _ later => later.index + 1

/-- The retained position is always in the authored declaration inventory. -/
theorem index_lt : {declarations : List SourceDeclaration} ->
    {name : DeclName} -> {entry : Entry Tower.Head} ->
    (occurrence : FirstConstant declarations name entry) ->
    occurrence.index < declarations.length
  | _, _, _, .here _ _ _ => by simp [index]
  | _, _, _, .equation _ later => by
      simpa [index] using Nat.succ_lt_succ later.index_lt
  | _, _, _, .other _ _ later => by
      simpa [index] using Nat.succ_lt_succ later.index_lt

/-- Reading the retained source position recovers the exact declaration,
including its complete entry rather than merely its displayed type. -/
theorem get_index : {declarations : List SourceDeclaration} ->
    {name : DeclName} -> {entry : Entry Tower.Head} ->
    (occurrence : FirstConstant declarations name entry) ->
    declarations[occurrence.index]'occurrence.index_lt =
      .constant name entry
  | _, _, _, .here _ _ _ => by simp [index]
  | _, _, _, .equation _ later => by
      simpa [index] using later.get_index
  | _, _, _, .other _ _ later => by
      simpa [index] using later.get_index

/-- A first-occurrence witness is sound for the extensional first-wins
signature interpretation. -/
theorem entries_lookup : {declarations : List SourceDeclaration} ->
    {name : DeclName} -> {entry : Entry Tower.Head} ->
    FirstConstant declarations name entry ->
      (semanticSignature declarations).entries name = some entry
  | _, _, _, .here name entry rest => by
      simp [semanticSignature, constantDeclarations, Signature.ofList,
        Signature.insert]
  | _, _, _, .equation _ later => by
      simpa [semanticSignature, constantDeclarations] using later.entries_lookup
  | _, _, _, .other different otherEntry later => by
      have reverse : _ := Ne.symm different
      simpa [semanticSignature, constantDeclarations, Signature.ofList,
        Signature.insert, reverse] using
        later.entries_lookup

/-- Extensional first-wins lookup reflects to one exact authored occurrence.
The result is `Nonempty` because proof identity is retained on the source side
but extensional lookup deliberately exposes only existence. -/
theorem of_entries_lookup :
    (declarations : List SourceDeclaration) ->
    (name : DeclName) -> (entry : Entry Tower.Head) ->
    (semanticSignature declarations).entries name = some entry ->
      Nonempty (FirstConstant declarations name entry)
  | [], name, entry, lookup => by
      simp [semanticSignature, constantDeclarations, Signature.ofList,
        Signature.empty] at lookup
  | .equation schema :: declarations, name, entry, lookup => by
      have tailLookup :
          (semanticSignature declarations).entries name = some entry := by
        simpa [semanticSignature, constantDeclarations] using lookup
      rcases of_entries_lookup declarations name entry tailLookup with
        ⟨later⟩
      exact ⟨.equation schema later⟩
  | .constant otherName otherEntry :: declarations, name, entry, lookup => by
      by_cases same : otherName = name
      · subst otherName
        have entryEquality : otherEntry = entry := by
          have lookup' : some otherEntry = some entry := by
            simpa [semanticSignature, constantDeclarations, Signature.ofList,
              Signature.insert] using lookup
          exact Option.some.inj lookup'
        subst entry
        exact ⟨.here name otherEntry declarations⟩
      · have tailLookup :
            (semanticSignature declarations).entries name = some entry := by
          have reverse : name ≠ otherName := Ne.symm same
          simpa [semanticSignature, constantDeclarations, Signature.ofList,
            Signature.insert, reverse] using lookup
        rcases of_entries_lookup declarations name entry tailLookup with
          ⟨later⟩
        exact ⟨.other same otherEntry later⟩

/-- Exact preservation and strongest true reflection for nominal declaration
lookup. -/
theorem entries_lookup_iff_nonempty
    (declarations : List SourceDeclaration) (name : DeclName)
    (entry : Entry Tower.Head) :
    (semanticSignature declarations).entries name = some entry <->
      Nonempty (FirstConstant declarations name entry) := by
  constructor
  · exact of_entries_lookup declarations name entry
  · rintro ⟨occurrence⟩
    exact occurrence.entries_lookup

/-- The corresponding type lookup is the declared entry's type. -/
theorem type_lookup {declarations : List SourceDeclaration}
    {name : DeclName} {entry : Entry Tower.Head}
    (occurrence : FirstConstant declarations name entry) :
    (semanticSignature declarations).typeOf? name = some entry.type := by
  simp [Signature.typeOf?, occurrence.entries_lookup]

end FirstConstant

/-! ## Authored documents and hosted native judgments -/

/-- Exact active occurrence in a possibly bundled authored document. -/
abbrev SourceOccurrence (source : SourceDocument) (name : DeclName)
    (entry : Entry Tower.Head) : Type :=
  FirstConstant (elaborate source) name entry

/-- A source occurrence reflects exactly to lookup in the interpreted
signature of the same byte-authored declaration document. -/
theorem interpret_entries_iff_occurrence (source : SourceDocument)
    (name : DeclName) (entry : Entry Tower.Head) :
    (interpret source).entries name = some entry <->
      Nonempty (SourceOccurrence source name entry) := by
  exact FirstConstant.entries_lookup_iff_nonempty
    (elaborate source) name entry

/-- An active source declaration constructs the established host-indexed
formed typing judgment directly.  Raw checking is not part of construction;
it is a possible boundary consumer of the same source occurrence later. -/
theorem occurrence_constructs_hosted_typing
    (host : FormationHost) {name : DeclName} {entry : Entry Tower.Head}
    (occurrence : SourceOccurrence host.source name entry) :
    exists level : LevelExpr,
      Nonempty (HostedFormedTyping host
        { arity := 0
          context := .nil
          levels := .nil
          subject := .const name
          type := entry.type
          level := level }) := by
  apply declared_constant_has_hosted_typing host
  change (interpret host.source).typeOf? name = some entry.type
  exact FirstConstant.type_lookup occurrence

/-- Conversely, an extensional declaration lookup identifies an active
authored occurrence; it never fabricates source provenance. -/
theorem hosted_lookup_reflects_source
    (host : FormationHost) {name : DeclName} {entry : Entry Tower.Head}
    (lookup : host.signature.entries name = some entry) :
    Nonempty (SourceOccurrence host.source name entry) := by
  apply (interpret_entries_iff_occurrence host.source name entry).mp
  exact lookup

/-! ## Positive and negative controls -/

private def exampleName : DeclName := `Prime.AuthoredIngress.A

private def firstEntry : Entry Tower.Head where
  type := .head (.sort Tower.zero)

private def shadowedEntry : Entry Tower.Head where
  type := .head (.sort (.succ Tower.zero))

private def equation : EquationSchema where
  label := `Prime.AuthoredIngress.eq
  arity := 0
  context := .nil
  left := .head .legacyGround
  right := .head .legacyGround
  type := .head (.sort Tower.zero)

private def sourceDeclarations : List SourceDeclaration :=
  [.equation equation,
   .constant exampleName firstEntry,
   .constant exampleName shadowedEntry]

/-- Equations before a declaration remain in the occurrence path and shift
its exact source index. -/
def firstOccurrence :
    FirstConstant sourceDeclarations exampleName firstEntry :=
  .equation equation (.here exampleName firstEntry
    [.constant exampleName shadowedEntry])

theorem first_occurrence_has_exact_index : firstOccurrence.index = 1 := rfl

theorem first_occurrence_reads_exact_source :
    sourceDeclarations[firstOccurrence.index]'firstOccurrence.index_lt =
      .constant exampleName firstEntry :=
  firstOccurrence.get_index

/-- The later declaration is present in the source but cannot become an
active nominal occurrence. -/
theorem shadowed_occurrence_is_not_active :
    ¬ Nonempty
      (FirstConstant sourceDeclarations exampleName shadowedEntry) := by
  rintro ⟨occurrence⟩
  have shadowedLookup := occurrence.entries_lookup
  have firstLookup := firstOccurrence.entries_lookup
  rw [firstLookup] at shadowedLookup
  have entryEquality : firstEntry = shadowedEntry :=
    Option.some.inj shadowedLookup
  have typeEquality := congrArg Entry.type entryEquality
  simp [firstEntry, shadowedEntry] at typeEquality
  cases typeEquality

/-- The active source occurrence survives the extensional readout. -/
theorem first_occurrence_interprets :
    (semanticSignature sourceDeclarations).entries exampleName =
      some firstEntry :=
  firstOccurrence.entries_lookup

#print axioms FirstConstant.entries_lookup_iff_nonempty
#print axioms interpret_entries_iff_occurrence
#print axioms occurrence_constructs_hosted_typing
#print axioms hosted_lookup_reflects_source
#print axioms first_occurrence_has_exact_index
#print axioms first_occurrence_reads_exact_source
#print axioms shadowed_occurrence_is_not_active
#print axioms first_occurrence_interprets

end AuthoredConstantIngress
end Mettapedia.Languages.MeTTa.PureKernel.Universe
