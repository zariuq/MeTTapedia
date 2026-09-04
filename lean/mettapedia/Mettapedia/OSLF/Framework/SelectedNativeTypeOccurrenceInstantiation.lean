import Mettapedia.OSLF.Framework.SelectedNativeTypeAuthoredOccurrenceSyntax
import Mettapedia.GSLT.LanguageDef.InferenceInstantiationBridge

/-!
# Occurrence-local instantiation for selected native types

Generated source-indexed rules rename the variables of each authored rewrite
occurrence into a private namespace.  This module connects that structural
renaming to the inference checker's positional argument vector without making
the checker layout part of the source semantics.

The public input is a source binding environment covering the complete
endpoint support of one selected occurrence.  A derived binding row changes
only the names.  On the admitted first-order fragment, applying the derived
row to renamed syntax is exactly the same operation as applying the original
row to the authored syntax.  The generic inference-instantiation bridge then
compiles that fact into the checker's ordinary ordered arguments.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Framework.SelectedNativeTypeOccurrenceInstantiation

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.GSLT.LanguageDef.InferenceInstantiationBridge
open Mettapedia.OSLF.Framework
open Mettapedia.OSLF.Framework.SelectedNativeTypeContextualCalculus
open Mettapedia.OSLF.Framework.SelectedNativeTypeAuthoredOccurrenceSyntax

/-- A source binding environment covering every endpoint variable of one
exact selected occurrence.  It contains values, not typing or relation
evidence. -/
structure EndpointInstantiation {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source)
    (slot : Occurrence demand) where
  bindings : Bindings
  covers : ∀ name ∈ endpointVariableNames demand slot,
    (Bindings.lookup bindings name).isSome

/-- Reindex only a declared finite name row.  Values are read from the source
binding environment; a missing value remains visibly unresolved. -/
def reindexBindings (names : List String) (rename : String → String)
    (bindings : Bindings) : Bindings :=
  names.map fun name =>
    (rename name, (Bindings.lookup bindings name).getD (.fvar name))

/-- Pull a binding row back along a finite name map.  Only the declared source
support is retained; ambient checker arguments are deliberately forgotten. -/
def restoreBindings (names : List String) (rename : String → String)
    (bindings : Bindings) : Bindings :=
  names.map fun name =>
    (name, (Bindings.lookup bindings (rename name)).getD (.fvar name))

private theorem lookup_cons_self (name : String) (value : Pattern)
    (rest : Bindings) :
    Bindings.lookup ((name, value) :: rest) name = some value := by
  unfold Bindings.lookup
  rw [List.find?_cons_of_pos (by simp)]
  rfl

private theorem lookup_cons_ne {headName name : String}
    (different : headName ≠ name) (value : Pattern) (rest : Bindings) :
    Bindings.lookup ((headName, value) :: rest) name =
      Bindings.lookup rest name := by
  unfold Bindings.lookup
  rw [List.find?_cons_of_neg (by simpa using different)]

/-- Reindexing preserves lookup on the declared source support whenever the
renaming is injective on that support. -/
theorem lookup_reindexBindings
    (names : List String) (rename : String → String) (bindings : Bindings)
    (injectiveOn : ∀ first ∈ names, ∀ second ∈ names,
      rename first = rename second → first = second)
    (covered : ∀ name ∈ names, (Bindings.lookup bindings name).isSome)
    {name : String} (member : name ∈ names) :
    Bindings.lookup (reindexBindings names rename bindings) (rename name) =
      Bindings.lookup bindings name := by
  induction names with
  | nil => simp at member
  | cons head tail inductionHypothesis =>
      simp only [reindexBindings, List.map_cons]
      by_cases same : head = name
      · subst name
        rw [lookup_cons_self]
        obtain ⟨value, valueEq⟩ := Option.isSome_iff_exists.mp
          (covered head (by simp))
        rw [valueEq, Option.getD_some]
      · have nameInTail : name ∈ tail := by
          rcases List.mem_cons.mp member with equal | member
          · exact (same equal.symm).elim
          · exact member
        have renamedDifferent : rename head ≠ rename name := by
          intro equal
          exact same (injectiveOn head (by simp) name
            (List.mem_cons_of_mem _ nameInTail) equal)
        rw [lookup_cons_ne renamedDifferent]
        exact inductionHypothesis
          (fun first firstMember second secondMember equal =>
            injectiveOn first (List.mem_cons_of_mem _ firstMember)
              second (List.mem_cons_of_mem _ secondMember) equal)
          (fun inner innerMember =>
            covered inner (List.mem_cons_of_mem _ innerMember))
          nameInTail

/-- Pullback lookup recovers the value of the renamed key on an exact,
duplicate-free source support. -/
theorem lookup_restoreBindings
    (names : List String) (rename : String → String) (bindings : Bindings)
    (nodup : names.Nodup)
    (covered : ∀ name ∈ names,
      (Bindings.lookup bindings (rename name)).isSome)
    {name : String} (member : name ∈ names) :
    Bindings.lookup (restoreBindings names rename bindings) name =
      Bindings.lookup bindings (rename name) := by
  induction names with
  | nil => simp at member
  | cons head tail inductionHypothesis =>
      simp only [restoreBindings, List.map_cons]
      have nodupParts := List.nodup_cons.mp nodup
      by_cases same : head = name
      · subst name
        rw [lookup_cons_self]
        obtain ⟨value, valueEq⟩ := Option.isSome_iff_exists.mp
          (covered head (by simp))
        rw [valueEq, Option.getD_some]
      · have nameInTail : name ∈ tail := by
          rcases List.mem_cons.mp member with equal | tailMember
          · exact (same equal.symm).elim
          · exact tailMember
        rw [lookup_cons_ne same]
        exact inductionHypothesis nodupParts.2
          (fun inner innerMember =>
            covered inner (List.mem_cons_of_mem _ innerMember)) nameInTail

/-- The occurrence-local name map is injective on the exact endpoint support.
Names outside that support are intentionally not covered by this theorem. -/
theorem renameVariable_injectiveOn {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source) (slot : Occurrence demand) :
    ∀ first ∈ endpointVariableNames demand slot,
      ∀ second ∈ endpointVariableNames demand slot,
        renameVariable demand slot first = renameVariable demand slot second →
          first = second := by
  intro first firstMember second secondMember equal
  unfold renameVariable at equal
  have indices :
      (endpointVariableNames demand slot).idxOf first =
        (endpointVariableNames demand slot).idxOf second :=
    (authoredVariableName_eq_iff _ _ _ _).mp equal |>.2
  exact (List.idxOf_inj firstMember).mp indices

/-- Binding row used for occurrence-local authored variables. -/
def EndpointInstantiation.renamedBindings {source : ValidatedLanguageDef}
    {demand : SelectedNativeTypeDemand source} {slot : Occurrence demand}
    (instantiation : EndpointInstantiation demand slot) : Bindings :=
  reindexBindings (endpointVariableNames demand slot)
    (renameVariable demand slot) instantiation.bindings

/-- Every source endpoint lookup is retained exactly under its private
occurrence-local name. -/
theorem EndpointInstantiation.lookup_renamedBindings
    {source : ValidatedLanguageDef}
    {demand : SelectedNativeTypeDemand source} {slot : Occurrence demand}
    (instantiation : EndpointInstantiation demand slot)
    {name : String} (member : name ∈ endpointVariableNames demand slot) :
    Bindings.lookup instantiation.renamedBindings
        (renameVariable demand slot name) =
      Bindings.lookup instantiation.bindings name := by
  exact lookup_reindexBindings _ _ _
    (renameVariable_injectiveOn demand slot) instantiation.covers member

/-- Source-side first-order formal row used to state the exact structural
fragment before occurrence-local renaming. -/
def endpointFormals {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source)
    (slot : Occurrence demand) : List (String × Nat) :=
  (endpointVariableNames demand slot).map fun name => (name, 0)

/-- An endpoint member maps to an actual formal of the occurrence-local
checker slice. -/
theorem renamed_formal_mem {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source) (slot : Occurrence demand)
    {name : String} (member : name ∈ endpointVariableNames demand slot) :
    (renameVariable demand slot name, 0) ∈ authoredMetavariables demand slot := by
  rw [authoredMetavariables]
  apply List.mem_ofFn.mpr
  let index : Fin (endpointVariableNames demand slot).length :=
    ⟨(endpointVariableNames demand slot).idxOf name,
      List.idxOf_lt_length_iff.mpr member⟩
  refine ⟨index, ?_⟩
  simp [index, renameVariable]

mutual

/-- Renaming an admitted first-order source pattern yields a checker fragment
over the occurrence-local formal row. -/
theorem authoredPattern_fragment {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source) (slot : Occurrence demand)
    {pattern : Pattern}
    (fragment : BindingSchemaFragment (endpointFormals demand slot) pattern) :
    BindingSchemaFragment (authoredMetavariables demand slot)
      (authoredPattern demand slot pattern) := by
  cases fragment with
  | bvar index =>
      simpa [authoredPattern, Pattern.renameFVars] using
        (BindingSchemaFragment.bvar
          (formals := authoredMetavariables demand slot) index)
  | @fvar name declared =>
      have renamedDeclared :
          (renameVariable demand slot name, 0) ∈
            authoredMetavariables demand slot := by
        apply renamed_formal_mem demand slot
        simpa [endpointFormals] using declared
      simpa [authoredPattern, Pattern.renameFVars] using
        (BindingSchemaFragment.fvar renamedDeclared)
  | apply items =>
      simpa [authoredPattern, Pattern.renameFVars] using
        (BindingSchemaFragment.apply
          (authoredPatterns_fragment demand slot items))
  | collection items =>
      simpa [authoredPattern, Pattern.renameFVars] using
        (BindingSchemaFragment.collection
          (authoredPatterns_fragment demand slot items))

theorem authoredPatterns_fragment {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source) (slot : Occurrence demand)
    {patterns : List Pattern}
    (fragment : BindingSchemasFragment (endpointFormals demand slot) patterns) :
    BindingSchemasFragment (authoredMetavariables demand slot)
      (patterns.map (Pattern.renameFVars (renameVariable demand slot))) := by
  cases fragment with
  | nil => exact .nil
  | cons head tail =>
      exact .cons (by
          simpa [authoredPattern] using
            authoredPattern_fragment demand slot head)
        (authoredPatterns_fragment demand slot tail)

end

mutual

/-- On the admitted endpoint fragment, occurrence-local binding application
commutes with the structural renaming. -/
theorem applyBindings_authoredPattern {source : ValidatedLanguageDef}
    {demand : SelectedNativeTypeDemand source} {slot : Occurrence demand}
    (instantiation : EndpointInstantiation demand slot) {pattern : Pattern}
    (fragment : BindingSchemaFragment (endpointFormals demand slot) pattern) :
    applyBindings instantiation.renamedBindings
        (authoredPattern demand slot pattern) =
      applyBindings instantiation.bindings pattern := by
  cases fragment with
  | bvar index =>
      simp [authoredPattern, Pattern.renameFVars, applyBindings]
  | @fvar name declared =>
      have member : name ∈ endpointVariableNames demand slot := by
        simpa [endpointFormals] using declared
      obtain ⟨value, sourceLookup⟩ := Option.isSome_iff_exists.mp
        (instantiation.covers name member)
      have renamedLookup :
          Bindings.lookup instantiation.renamedBindings
              (renameVariable demand slot name) = some value :=
        (instantiation.lookup_renamedBindings member).trans sourceLookup
      simpa [authoredPattern, Pattern.renameFVars] using
        (applyBindings_fvar_eq_of_lookup renamedLookup).trans
          (applyBindings_fvar_eq_of_lookup sourceLookup).symm
  | apply items =>
      simpa only [authoredPattern, Pattern.renameFVars, applyBindings] using
        congrArg (Pattern.apply _)
          (applyBindings_authoredPatterns instantiation items)
  | collection items =>
      simpa only [authoredPattern, Pattern.renameFVars, applyBindings,
          List.append_nil] using
        congrArg (fun elements => Pattern.collection _ elements none)
          (applyBindings_authoredPatterns instantiation items)

theorem applyBindings_authoredPatterns {source : ValidatedLanguageDef}
    {demand : SelectedNativeTypeDemand source} {slot : Occurrence demand}
    (instantiation : EndpointInstantiation demand slot)
    {patterns : List Pattern}
    (fragment : BindingSchemasFragment (endpointFormals demand slot) patterns) :
    (patterns.map (Pattern.renameFVars (renameVariable demand slot))).map
        (applyBindings instantiation.renamedBindings) =
      patterns.map (applyBindings instantiation.bindings) := by
  cases fragment with
  | nil => rfl
  | cons head tail =>
      simp only [List.map_cons]
      have headEquality :=
        applyBindings_authoredPattern instantiation head
      simp only [authoredPattern] at headEquality
      rw [headEquality,
        applyBindings_authoredPatterns instantiation tail]

end

private theorem eraseDups_nodup
    {α : Type*} [BEq α] [LawfulBEq α] :
    ∀ values : List α, values.eraseDups.Nodup
  | [] => by simp
  | value :: values => by
      rw [List.eraseDups_cons]
      refine List.nodup_cons.mpr
        ⟨?_, eraseDups_nodup
          (values.filter fun other => !other == value)⟩
      intro member
      rw [List.mem_eraseDups, List.mem_filter] at member
      simp at member
termination_by values => values.length
decreasing_by
  have shorter :=
    List.length_filter_le (fun other => !other == value) values
  simp only [List.length_cons]
  omega

theorem endpointVariableNames_nodup {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source) (slot : Occurrence demand) :
    (endpointVariableNames demand slot).Nodup := by
  unfold endpointVariableNames
  exact eraseDups_nodup _

/-- Recover an occurrence-local source environment from any larger checker
binding row that covers the occurrence's private renamed variables. -/
def EndpointInstantiation.ofRenamedBindings
    {source : ValidatedLanguageDef}
    {demand : SelectedNativeTypeDemand source} {slot : Occurrence demand}
    (bindings : Bindings)
    (covered : ∀ name ∈ endpointVariableNames demand slot,
      (Bindings.lookup bindings (renameVariable demand slot name)).isSome) :
    EndpointInstantiation demand slot where
  bindings := restoreBindings (endpointVariableNames demand slot)
    (renameVariable demand slot) bindings
  covers := by
    intro name member
    rw [lookup_restoreBindings _ _ _
      (endpointVariableNames_nodup demand slot) covered member]
    exact covered name member

@[simp] theorem EndpointInstantiation.ofRenamedBindings_lookup
    {source : ValidatedLanguageDef}
    {demand : SelectedNativeTypeDemand source} {slot : Occurrence demand}
    (bindings : Bindings)
    (covered : ∀ name ∈ endpointVariableNames demand slot,
      (Bindings.lookup bindings (renameVariable demand slot name)).isSome)
    {name : String} (member : name ∈ endpointVariableNames demand slot) :
    Bindings.lookup
        (EndpointInstantiation.ofRenamedBindings bindings covered).bindings name =
      Bindings.lookup bindings (renameVariable demand slot name) := by
  exact lookup_restoreBindings _ _ _
    (endpointVariableNames_nodup demand slot) covered member

/-- Reconstruct one occurrence-local source environment from a larger
checker instance.  The declaration hypothesis is structural: it says only
that the generated rule's formal row contains every private endpoint name. -/
def EndpointInstantiation.ofCheckerArguments
    {source : ValidatedLanguageDef}
    {demand : SelectedNativeTypeDemand source} {slot : Occurrence demand}
    (formals : List (String × Nat)) (arguments : List Pattern)
    (checkerBindings : Bindings)
    (namesNodup : (formals.map Prod.fst).Nodup)
    (decoded : bindingsOfArguments? formals arguments = some checkerBindings)
    (declared : ∀ name ∈ endpointVariableNames demand slot,
      (renameVariable demand slot name, 0) ∈ formals) :
    EndpointInstantiation demand slot :=
  EndpointInstantiation.ofRenamedBindings checkerBindings (by
    intro name member
    exact bindingsOfArguments?_lookup_isSome namesNodup decoded
      (renameVariable demand slot name, 0) (declared name member))

/-- The source value reconstructed from a checker instance is exactly the
value stored under the corresponding private occurrence-local formal. -/
@[simp] theorem EndpointInstantiation.ofCheckerArguments_lookup
    {source : ValidatedLanguageDef}
    {demand : SelectedNativeTypeDemand source} {slot : Occurrence demand}
    (formals : List (String × Nat)) (arguments : List Pattern)
    (checkerBindings : Bindings)
    (namesNodup : (formals.map Prod.fst).Nodup)
    (decoded : bindingsOfArguments? formals arguments = some checkerBindings)
    (declared : ∀ name ∈ endpointVariableNames demand slot,
      (renameVariable demand slot name, 0) ∈ formals)
    {name : String} (member : name ∈ endpointVariableNames demand slot) :
    Bindings.lookup
        (EndpointInstantiation.ofCheckerArguments formals arguments
          checkerBindings namesNodup decoded declared).bindings name =
      Bindings.lookup checkerBindings (renameVariable demand slot name) := by
  exact EndpointInstantiation.ofRenamedBindings_lookup checkerBindings _ member

/-- One proof-relevant bridge from a checker argument vector to an exact
source endpoint environment.  Keeping the checker binding row and pointwise
lookup equality in the same record prevents an arbitrary endpoint witness
from being substituted after decoding. -/
structure CheckerEndpointInstantiation
    {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source) (slot : Occurrence demand)
    (formals : List (String × Nat)) (arguments : List Pattern) where
  checkerBindings : Bindings
  decoded : bindingsOfArguments? formals arguments = some checkerBindings
  endpoint : EndpointInstantiation demand slot
  lookup : ∀ name ∈ endpointVariableNames demand slot,
    Bindings.lookup endpoint.bindings name =
      Bindings.lookup checkerBindings (renameVariable demand slot name)

/-- A checker-valid, name-unique instance whose formal row contains the
private endpoint support constructs one coherent checker/source bridge. -/
theorem CheckerEndpointInstantiation.exists_of_arguments
    {source : ValidatedLanguageDef}
    {demand : SelectedNativeTypeDemand source} {slot : Occurrence demand}
    (formals : List (String × Nat)) (arguments : List Pattern)
    (valid : argumentsValidAt formals arguments = true)
    (namesNodup : (formals.map Prod.fst).Nodup)
    (declared : ∀ name ∈ endpointVariableNames demand slot,
      (renameVariable demand slot name, 0) ∈ formals) :
    Nonempty (CheckerEndpointInstantiation demand slot formals arguments) := by
  obtain ⟨checkerBindings, decoded⟩ :=
    bindingsOfArguments?_exists_of_argumentsValidAt valid
  let endpoint := EndpointInstantiation.ofCheckerArguments formals arguments
    checkerBindings namesNodup decoded declared
  refine ⟨{ checkerBindings := checkerBindings
            decoded := decoded
            endpoint := endpoint
            lookup := ?_ }⟩
  intro name member
  exact EndpointInstantiation.ofCheckerArguments_lookup
    formals arguments checkerBindings namesNodup decoded declared member

/-- The source endpoint value reconstructed by one checker bridge is exactly
the argument selected by the checker's own depth-sensitive lookup.  This is
the pointwise equation used to interpret grounded variable-context claims. -/
theorem CheckerEndpointInstantiation.lookupArgument
    {source : ValidatedLanguageDef}
    {demand : SelectedNativeTypeDemand source} {slot : Occurrence demand}
    {formals : List (String × Nat)} {arguments : List Pattern}
    (instantiation :
      CheckerEndpointInstantiation demand slot formals arguments)
    (namesNodup : (formals.map Prod.fst).Nodup)
    (declared : ∀ name ∈ endpointVariableNames demand slot,
      (renameVariable demand slot name, 0) ∈ formals)
    {name : String} (member : name ∈ endpointVariableNames demand slot) :
    Bindings.lookup instantiation.endpoint.bindings name =
      lookupArgumentAt? formals arguments
        (renameVariable demand slot name) 0 := by
  calc
    Bindings.lookup instantiation.endpoint.bindings name =
        Bindings.lookup instantiation.checkerBindings
          (renameVariable demand slot name) :=
      instantiation.lookup name member
    _ = lookupArgumentAt? formals arguments
          (renameVariable demand slot name) 0 :=
      bindingsOfArguments?_lookup_eq_lookupArgumentAt?
        namesNodup instantiation.decoded
        (renameVariable demand slot name, 0) (declared name member)

mutual

/-- Any larger checker rule containing the private endpoint formals
instantiates occurrence-renamed source syntax exactly through the endpoint
environment reconstructed from that same rule application. -/
theorem CheckerEndpointInstantiation.instantiate_authoredPattern
    {source : ValidatedLanguageDef}
    {demand : SelectedNativeTypeDemand source} {slot : Occurrence demand}
    {formals : List (String × Nat)} {arguments : List Pattern}
    (instantiation :
      CheckerEndpointInstantiation demand slot formals arguments)
    (namesNodup : (formals.map Prod.fst).Nodup)
    (declared : ∀ name ∈ endpointVariableNames demand slot,
      (renameVariable demand slot name, 0) ∈ formals)
    {pattern : Pattern}
    (fragment : BindingSchemaFragment (endpointFormals demand slot) pattern) :
    instantiateSchema? formals arguments (authoredPattern demand slot pattern) =
      some (applyBindings instantiation.endpoint.bindings pattern) := by
  cases fragment with
  | bvar index =>
      simp [instantiateSchema?, instantiateSchemaAt?, authoredPattern,
        Pattern.renameFVars, applyBindings]
  | @fvar name sourceDeclared =>
      have member : name ∈ endpointVariableNames demand slot := by
        simpa [endpointFormals] using sourceDeclared
      obtain ⟨value, sourceLookup⟩ := Option.isSome_iff_exists.mp
        (instantiation.endpoint.covers name member)
      have checkerLookup :
          lookupArgumentAt? formals arguments
              (renameVariable demand slot name) 0 = some value :=
        (instantiation.lookupArgument namesNodup declared member).symm.trans
          sourceLookup
      simpa [instantiateSchema?, instantiateSchemaAt?, authoredPattern,
        Pattern.renameFVars,
        applyBindings_fvar_eq_of_lookup sourceLookup] using checkerLookup
  | @apply constructor schemas items =>
      have itemsExact :
          instantiateSchemasAt? formals arguments 0
              (schemas.map (authoredPattern demand slot)) =
            some (schemas.map
              (applyBindings instantiation.endpoint.bindings)) :=
        instantiation.instantiate_authoredPatterns
          namesNodup declared items
      have authoredEq :
          authoredPattern demand slot (Pattern.apply constructor schemas) =
            Pattern.apply constructor
              (schemas.map (authoredPattern demand slot)) := by
        simp [authoredPattern, Pattern.renameFVars]
      have appliedEq :
          applyBindings instantiation.endpoint.bindings
              (Pattern.apply constructor schemas) =
            Pattern.apply constructor
              (schemas.map
                (applyBindings instantiation.endpoint.bindings)) := by
        simp [applyBindings]
      rw [authoredEq, appliedEq]
      simp [instantiateSchema?, instantiateSchemaAt?, itemsExact]
  | @collection collectionType elements items =>
      have itemsExact :
          instantiateSchemasAt? formals arguments 0
              (elements.map (authoredPattern demand slot)) =
            some (elements.map
              (applyBindings instantiation.endpoint.bindings)) :=
        instantiation.instantiate_authoredPatterns
          namesNodup declared items
      have authoredEq :
          authoredPattern demand slot
              (Pattern.collection collectionType elements none) =
            Pattern.collection collectionType
              (elements.map (authoredPattern demand slot)) none := by
        simp [authoredPattern, Pattern.renameFVars]
      have appliedEq :
          applyBindings instantiation.endpoint.bindings
              (Pattern.collection collectionType elements none) =
            Pattern.collection collectionType
              (elements.map
                (applyBindings instantiation.endpoint.bindings)) none := by
        simp [applyBindings]
      rw [authoredEq, appliedEq]
      simp [instantiateSchema?, instantiateSchemaAt?, itemsExact]

/-- List-valued companion retaining exact source order and duplicate pattern
occurrences. -/
theorem CheckerEndpointInstantiation.instantiate_authoredPatterns
    {source : ValidatedLanguageDef}
    {demand : SelectedNativeTypeDemand source} {slot : Occurrence demand}
    {formals : List (String × Nat)} {arguments : List Pattern}
    (instantiation :
      CheckerEndpointInstantiation demand slot formals arguments)
    (namesNodup : (formals.map Prod.fst).Nodup)
    (declared : ∀ name ∈ endpointVariableNames demand slot,
      (renameVariable demand slot name, 0) ∈ formals)
    {patterns : List Pattern}
    (fragment : BindingSchemasFragment (endpointFormals demand slot) patterns) :
    instantiateSchemas? formals arguments
        (patterns.map (authoredPattern demand slot)) =
      some (patterns.map (applyBindings instantiation.endpoint.bindings)) := by
  cases fragment with
  | nil => simp [instantiateSchemas?, instantiateSchemasAt?]
  | @cons pattern patterns head tail =>
      have headExact :
          instantiateSchemaAt? formals arguments 0
              (authoredPattern demand slot pattern) =
            some (applyBindings instantiation.endpoint.bindings pattern) := by
        simpa only [instantiateSchema?] using
          instantiation.instantiate_authoredPattern
            namesNodup declared head
      have tailExact :
          instantiateSchemasAt? formals arguments 0
              (patterns.map (authoredPattern demand slot)) =
            some (patterns.map
              (applyBindings instantiation.endpoint.bindings)) := by
        simpa only [instantiateSchemas?] using
          instantiation.instantiate_authoredPatterns
            namesNodup declared tail
      simp [instantiateSchemas?, instantiateSchemasAt?, headExact, tailExact]

end

/-- Every occurrence-local checker formal has a value in the derived binding
row. -/
theorem EndpointInstantiation.renamedBindings_cover
    {source : ValidatedLanguageDef}
    {demand : SelectedNativeTypeDemand source} {slot : Occurrence demand}
    (instantiation : EndpointInstantiation demand slot) :
    ∀ formal ∈ authoredMetavariables demand slot,
      (Bindings.lookup instantiation.renamedBindings formal.1).isSome := by
  intro formal formalMember
  rw [authoredMetavariables] at formalMember
  obtain ⟨index, formalEq⟩ := List.mem_ofFn.mp formalMember
  subst formal
  let name := (endpointVariableNames demand slot).get index
  have member : name ∈ endpointVariableNames demand slot := List.get_mem _ index
  have indexEq :
      (endpointVariableNames demand slot).idxOf name = index.val := by
    simpa [name] using
      List.get_idxOf (endpointVariableNames_nodup demand slot) index
  have keyEq :
      renameVariable demand slot name =
        authoredVariableName slot.val index.val := by
    simp [renameVariable, indexEq]
  have lookup := instantiation.lookup_renamedBindings member
  rw [← keyEq, lookup]
  exact instantiation.covers name member

private theorem argumentsOfBindings?_exists_of_cover :
    ∀ (formals : List (String × Nat)) (bindings : Bindings),
      (∀ formal ∈ formals, formal.2 = 0) →
      (∀ formal ∈ formals,
        (Bindings.lookup bindings formal.1).isSome) →
      ∃ arguments, argumentsOfBindings? formals bindings = some arguments
  | [], _, _, _ => ⟨[], rfl⟩
  | (name, depth) :: rest, bindings, depths, covered => by
      have depthZero : depth = 0 :=
        depths (name, depth) (by simp)
      subst depth
      obtain ⟨value, lookup⟩ := Option.isSome_iff_exists.mp
        (covered (name, 0) (by simp))
      obtain ⟨arguments, argumentsEq⟩ :=
        argumentsOfBindings?_exists_of_cover rest bindings
          (fun formal member => depths formal (by simp [member]))
          (fun formal member => covered formal (by simp [member]))
      exact ⟨value :: arguments, by
        simp [argumentsOfBindings?, lookup, argumentsEq]⟩

theorem authoredMetavariables_depth_zero {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source) (slot : Occurrence demand) :
    ∀ formal ∈ authoredMetavariables demand slot, formal.2 = 0 := by
  intro formal member
  rw [authoredMetavariables] at member
  obtain ⟨index, equality⟩ := List.mem_ofFn.mp member
  simpa using congrArg Prod.snd equality.symm

/-- Covered occurrence-local bindings always compile to a complete ordered
checker argument vector. -/
theorem EndpointInstantiation.checkerArguments_exists
    {source : ValidatedLanguageDef}
    {demand : SelectedNativeTypeDemand source} {slot : Occurrence demand}
    (instantiation : EndpointInstantiation demand slot) :
    ∃ arguments,
      argumentsOfBindings? (authoredMetavariables demand slot)
        instantiation.renamedBindings = some arguments := by
  exact argumentsOfBindings?_exists_of_cover _ _
    (authoredMetavariables_depth_zero demand slot)
    instantiation.renamedBindings_cover

/-- With one fixed checker argument vector, checker instantiation of renamed
syntax computes exactly the authored source binding application.  Keeping the
argument equality explicit lets several endpoint patterns share one coherent
occurrence environment. -/
theorem EndpointInstantiation.instantiate_authoredPattern_of_arguments
    {source : ValidatedLanguageDef}
    {demand : SelectedNativeTypeDemand source} {slot : Occurrence demand}
    (instantiation : EndpointInstantiation demand slot)
    {arguments : List Pattern} {pattern : Pattern}
    (argumentsEq :
      argumentsOfBindings? (authoredMetavariables demand slot)
        instantiation.renamedBindings = some arguments)
    (fragment : BindingSchemaFragment (endpointFormals demand slot) pattern) :
    instantiateSchema? (authoredMetavariables demand slot) arguments
        (authoredPattern demand slot pattern) =
      some (applyBindings instantiation.bindings pattern) := by
  rw [instantiateSchema?_eq_applyBindings
    (authoredPattern_fragment demand slot fragment) argumentsEq]
  exact congrArg some (applyBindings_authoredPattern instantiation fragment)

/-- Crown representation theorem for the occurrence-variable slice: one
complete checker argument vector instantiates every admitted authored
endpoint pattern exactly as the source binding environment does. -/
theorem EndpointInstantiation.instantiate_authoredPattern
    {source : ValidatedLanguageDef}
    {demand : SelectedNativeTypeDemand source} {slot : Occurrence demand}
    (instantiation : EndpointInstantiation demand slot) {pattern : Pattern}
    (fragment : BindingSchemaFragment (endpointFormals demand slot) pattern) :
    ∃ arguments,
      argumentsOfBindings? (authoredMetavariables demand slot)
          instantiation.renamedBindings = some arguments ∧
        instantiateSchema? (authoredMetavariables demand slot) arguments
            (authoredPattern demand slot pattern) =
          some (applyBindings instantiation.bindings pattern) := by
  obtain ⟨arguments, argumentsEq⟩ := instantiation.checkerArguments_exists
  exact ⟨arguments, argumentsEq,
    instantiation.instantiate_authoredPattern_of_arguments argumentsEq fragment⟩

/-! ## Generic controls -/

private def controlNames : List String := ["x", "y"]
private def controlBindings : Bindings :=
  [("x", .apply "X" []), ("y", .apply "Y" [])]

#guard decide
  (reindexBindings controlNames ("private:" ++ ·) controlBindings =
    [("private:x", .apply "X" []), ("private:y", .apply "Y" [])])

#guard
  (reindexBindings controlNames ("private:" ++ ·)
      [("x", .apply "X" [])]).lookup "private:y" ==
    some (.fvar "y")

#print axioms lookup_reindexBindings
#print axioms lookup_restoreBindings
#print axioms renameVariable_injectiveOn
#print axioms renamed_formal_mem
#print axioms authoredPattern_fragment
#print axioms applyBindings_authoredPattern
#print axioms EndpointInstantiation.ofRenamedBindings_lookup
#print axioms EndpointInstantiation.ofCheckerArguments_lookup
#print axioms CheckerEndpointInstantiation.exists_of_arguments
#print axioms CheckerEndpointInstantiation.lookupArgument
#print axioms CheckerEndpointInstantiation.instantiate_authoredPattern
#print axioms EndpointInstantiation.renamedBindings_cover
#print axioms EndpointInstantiation.checkerArguments_exists
#print axioms EndpointInstantiation.instantiate_authoredPattern_of_arguments
#print axioms EndpointInstantiation.instantiate_authoredPattern

end Mettapedia.OSLF.Framework.SelectedNativeTypeOccurrenceInstantiation
