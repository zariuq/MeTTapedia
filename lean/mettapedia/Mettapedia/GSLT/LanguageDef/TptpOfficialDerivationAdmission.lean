import Mettapedia.GSLT.LanguageDef.TptpOfficialDerivationSyntax

/-!
# Calculus-neutral admission of official TSTP derivations

This module performs the structural pass shared by every TSTP calculus.  It
admits the actual all-family semantic carrier, decodes each annotated formula
without changing it, resolves every recursive named source exactly once from
left to right, and assigns dense node identifiers.

The pass establishes the graph facts that do not depend on a calculus:

* source occurrences belong to the declared document digest;
* formula names and occurrence identities are unique;
* every local named dependency denotes an earlier node;
* parent order and multiplicity are preserved; and
* therefore every compiled local edge points to a strictly smaller node id.

It does not interpret inference-rule names, `status(...)`, introduced symbols,
assumptions, or formula semantics.  Those obligations belong to separately
validated calculus services.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.TptpOfficialDerivationAdmission

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.CarrierWellSorted
open Mettapedia.GSLT.LanguageDef.TptpOfficialSemanticCarrier
open Mettapedia.GSLT.LanguageDef.TptpOfficialDerivationSyntax

private def a (label : String) (arguments : List Pattern := []) : Pattern :=
  .apply label arguments

structure OccurrenceView where
  sourceDigest : String
  index : Pattern
  deriving DecidableEq, Repr

def decodeSourceDigest? : Pattern -> Option String
  | .apply "tptp-semantic:source-digest" [.apply digest []] => some digest
  | _ => none

def decodeOccurrence? : Pattern -> Option OccurrenceView
  | .apply "tptp-semantic:occurrence-id" [source, index] => do
      let sourceDigest <- decodeSourceDigest? source
      some { sourceDigest, index }
  | _ => none

def occurrenceBelongsToSource (source : Pattern) (occurrence : Pattern) : Bool :=
  match decodeSourceDigest? source, decodeOccurrence? occurrence with
  | some expected, some actual => actual.sourceDigest == expected
  | _, _ => false

def decodeReferenceNames? : List Pattern -> Option (List String)
  | [] => some []
  | reference :: references => do
      let name <- decodeName? reference
      let rest <- decodeReferenceNames? references
      some (name :: rest)

inductive NodeOrigin where
  | unannotated
  | sourced (raw : Pattern) (head : SourceHead) (optionalInfo : Pattern)
  deriving DecidableEq, Repr

structure DecodedNode where
  termView : DerivationNodeView
  name : String
  role : String
  origin : NodeOrigin
  references : List String
  deriving DecidableEq, Repr

def decodeNode? (input : AnnotatedInputView) : Option DecodedNode := do
  let termView <- decodeDerivationNode? input
  let name <- decodeName? termView.name
  let role <- decodeRoleLexeme? termView.role
  match termView.annotation with
  | .absent =>
      some { termView, name, role, origin := .unannotated, references := [] }
  | .sourced source optionalInfo => do
      let head <- decodeSourceHead? source
      let referencePatterns <- sourceReferences? source
      let references <- decodeReferenceNames? referencePatterns
      some {
        termView
        name
        role
        origin := .sourced source head optionalInfo
        references
      }

def decodeNodeViews? : Pattern -> Option (List AnnotatedInputView)
  | .apply "tptp-semantic:derivation-nodes-nil" [] => some []
  | .apply "tptp-semantic:derivation-nodes-cons" [first, rest] => do
      let decodedFirst <- decodeAnnotatedInput? first
      let decodedRest <- decodeNodeViews? rest
      some (decodedFirst :: decodedRest)
  | _ => none

def decodeNodesForSource? (source : Pattern) :
    List AnnotatedInputView -> Option (List DecodedNode)
  | [] => some []
  | input :: inputs => do
      if !occurrenceBelongsToSource source input.occurrence then none else
      let decodedInput <- decodeNode? input
      let decodedRest <- decodeNodesForSource? source inputs
      some (decodedInput :: decodedRest)

structure DecodedDerivation where
  source : Pattern
  sourceDigest : String
  nodes : List DecodedNode
  deriving DecidableEq, Repr

def decodeDerivation? : Pattern -> Option DecodedDerivation
  | .apply "tptp-semantic:derivation" [source, nodes] => do
      let sourceDigest <- decodeSourceDigest? source
      let nodeViews <- decodeNodeViews? nodes
      let decodedNodes <- decodeNodesForSource? source nodeViews
      some { source, sourceDigest, nodes := decodedNodes }
  | _ => none

structure NameEntry where
  name : String
  id : Nat
  deriving DecidableEq, Repr

abbrev NameTable := List NameEntry

def lookupEntry? : NameTable -> String -> Option NameEntry
  | [], _ => none
  | entry :: entries, requested =>
      if entry.name = requested then some entry
      else lookupEntry? entries requested

def resolveNames? (entries : NameTable) :
    List String -> Option (List NameEntry)
  | [] => some []
  | name :: names => do
      let entry <- lookupEntry? entries name
      let resolved <- resolveNames? entries names
      some (entry :: resolved)

theorem lookupEntry?_mem {entries : NameTable} {requested : String}
    {entry : NameEntry} (found : lookupEntry? entries requested = some entry) :
    entry ∈ entries := by
  induction entries with
  | nil => simp [lookupEntry?] at found
  | cons first rest ih =>
      unfold lookupEntry? at found
      split at found
      · have equal : first = entry := Option.some.inj found
        simp [equal]
      · exact List.mem_cons_of_mem _ (ih found)

theorem lookupEntry?_name {entries : NameTable} {requested : String}
    {entry : NameEntry} (found : lookupEntry? entries requested = some entry) :
    entry.name = requested := by
  induction entries with
  | nil => simp [lookupEntry?] at found
  | cons first rest ih =>
      unfold lookupEntry? at found
      split at found <;> rename_i condition
      · have equal : first = entry := Option.some.inj found
        simpa [equal] using condition
      · exact ih found

theorem resolveNames?_mem {entries : NameTable} {requested : List String}
    {resolved : List NameEntry}
    (found : resolveNames? entries requested = some resolved) :
    ∀ entry ∈ resolved, entry ∈ entries := by
  induction requested generalizing resolved with
  | nil =>
      simp [resolveNames?] at found
      subst resolved
      simp
  | cons name names ih =>
      unfold resolveNames? at found
      generalize entryEq : lookupEntry? entries name = entryResult at found
      cases entryResult with
      | none => simp at found
      | some entry =>
          generalize restEq : resolveNames? entries names = restResult at found
          cases restResult with
          | none => simp at found
          | some rest =>
              simp at found
              subst resolved
              intro candidate member
              simp only [List.mem_cons] at member
              rcases member with rfl | member
              · exact lookupEntry?_mem entryEq
              · exact ih restEq candidate member

theorem resolveNames?_names {entries : NameTable} {requested : List String}
    {resolved : List NameEntry}
    (found : resolveNames? entries requested = some resolved) :
    resolved.map NameEntry.name = requested := by
  induction requested generalizing resolved with
  | nil =>
      simp [resolveNames?] at found
      subst resolved
      rfl
  | cons name names ih =>
      unfold resolveNames? at found
      generalize entryEq : lookupEntry? entries name = entryResult at found
      cases entryResult with
      | none => simp at found
      | some entry =>
          generalize restEq : resolveNames? entries names = restResult at found
          cases restResult with
          | none => simp at found
          | some rest =>
              simp at found
              subst resolved
              simp [lookupEntry?_name entryEq, ih restEq]

def NamesBelow (entries : NameTable) (bound : Nat) : Prop :=
  ∀ entry ∈ entries, entry.id < bound

theorem resolveNames?_below {entries : NameTable} {bound : Nat}
    (below : NamesBelow entries bound) {requested : List String}
    {resolved : List NameEntry}
    (found : resolveNames? entries requested = some resolved) :
    ∀ entry ∈ resolved, entry.id < bound := by
  intro entry member
  exact below entry (resolveNames?_mem found entry member)

structure AdmittedNode where
  id : Nat
  source : DecodedNode
  parents : List NameEntry
  parentNames_exact : parents.map NameEntry.name = source.references
  parents_lt : ∀ parent ∈ parents, parent.id < id

def AdmittedNode.parentIds (node : AdmittedNode) : List Nat :=
  node.parents.map NameEntry.id

theorem AdmittedNode.parentIds_lt (node : AdmittedNode) :
    ∀ parentId ∈ node.parentIds, parentId < node.id := by
  intro parentId member
  obtain ⟨parent, parentMember, equal⟩ := List.mem_map.mp member
  rw [← equal]
  exact node.parents_lt parent parentMember

structure BuildState where
  names : NameTable
  occurrences : List Pattern
  nextId : Nat
  nodesRev : List AdmittedNode
  namesBelow : NamesBelow names nextId
  namesNodup : (names.map NameEntry.name).Nodup
  occurrencesNodup : occurrences.Nodup

def initialState : BuildState := {
  names := []
  occurrences := []
  nextId := 0
  nodesRev := []
  namesBelow := by simp [NamesBelow]
  namesNodup := by simp
  occurrencesNodup := by simp
}

def compileNode (state : BuildState) (node : DecodedNode) :
    Option BuildState :=
  if duplicateName : (state.names.map NameEntry.name).contains node.name then
    none
  else if duplicateOccurrence : state.occurrences.contains node.termView.occurrence then
    none
  else
    match resolvedEq : resolveNames? state.names node.references with
    | none => none
    | some parents =>
        let id := state.nextId
        let admitted : AdmittedNode := {
          id
          source := node
          parents
          parentNames_exact := resolveNames?_names resolvedEq
          parents_lt := resolveNames?_below state.namesBelow resolvedEq
        }
        some {
          names := { name := node.name, id } :: state.names
          occurrences := node.termView.occurrence :: state.occurrences
          nextId := id + 1
          nodesRev := admitted :: state.nodesRev
          namesBelow := by
            intro entry member
            simp only [List.mem_cons] at member
            rcases member with rfl | member
            · exact Nat.lt_succ_self _
            · exact Nat.lt_trans (state.namesBelow entry member)
                (Nat.lt_succ_self _)
          namesNodup := by
            simp only [List.map_cons, List.nodup_cons]
            constructor
            · simpa using duplicateName
            · exact state.namesNodup
          occurrencesNodup := by
            simp only [List.nodup_cons]
            constructor
            · simpa using duplicateOccurrence
            · exact state.occurrencesNodup
        }

def compileNodes : BuildState -> List DecodedNode -> Option BuildState
  | state, [] => some state
  | state, node :: nodes => do
      let next <- compileNode state node
      compileNodes next nodes

structure CompiledDerivation where
  decoded : DecodedDerivation
  nodes : List AdmittedNode
  names : NameTable
  occurrences : List Pattern
  namesNodup : (names.map NameEntry.name).Nodup
  occurrencesNodup : occurrences.Nodup

def compileDecoded? (decoded : DecodedDerivation) :
    Option CompiledDerivation := do
  let final <- compileNodes initialState decoded.nodes
  some {
    decoded
    nodes := final.nodesRev.reverse
    names := final.names
    occurrences := final.occurrences
    namesNodup := final.namesNodup
    occurrencesNodup := final.occurrencesNodup
  }

structure AdmittedDerivation where
  source : Pattern
  carrierAdmitted :
    checkHasType language WellSorted.FreeTypeContext.empty [] source
      (.base "TptpSemantic:derivation") = true
  derivation : DecodedDerivation
  decoded : decodeDerivation? source = some derivation
  compiled : CompiledDerivation
  lowered : compileDecoded? derivation = some compiled

def admit? (source : Pattern) : Option AdmittedDerivation :=
  if carrierAdmitted :
      checkHasType language WellSorted.FreeTypeContext.empty [] source
        (.base "TptpSemantic:derivation") = true then
    match decodedEq : decodeDerivation? source with
    | none => none
    | some decoded =>
        match loweredEq : compileDecoded? decoded with
        | none => none
        | some compiled => some {
            source
            carrierAdmitted
            derivation := decoded
            decoded := decodedEq
            compiled
            lowered := loweredEq
          }
  else
    none

theorem admitted_edges_strictly_decrease (admitted : AdmittedDerivation) :
    ∀ node ∈ admitted.compiled.nodes,
      ∀ parentId ∈ node.parentIds, parentId < node.id := by
  intro node _ parentId member
  exact node.parentIds_lt parentId member

theorem admitted_parent_names_exact (admitted : AdmittedDerivation) :
    ∀ node ∈ admitted.compiled.nodes,
      node.parents.map NameEntry.name = node.source.references := by
  intro node _
  exact node.parentNames_exact

theorem admitted_names_unique (admitted : AdmittedDerivation) :
    (admitted.compiled.names.map NameEntry.name).Nodup :=
  admitted.compiled.namesNodup

theorem admitted_occurrences_unique (admitted : AdmittedDerivation) :
    admitted.compiled.occurrences.Nodup :=
  admitted.compiled.occurrencesNodup

def Edge (compiled : CompiledDerivation) (parent child : Nat) : Prop :=
  ∃ node ∈ compiled.nodes,
    node.id = child ∧ parent ∈ node.parentIds

theorem edge_strictly_increases {compiled : CompiledDerivation}
    {parent child : Nat} (edge : Edge compiled parent child) :
    parent < child := by
  rcases edge with ⟨node, nodeMember, rfl, parentMember⟩
  exact node.parentIds_lt parent parentMember

theorem dependency_path_strictly_increases {compiled : CompiledDerivation}
    {ancestor descendant : Nat}
    (path : Relation.TransGen (Edge compiled) ancestor descendant) :
    ancestor < descendant := by
  induction path using Relation.TransGen.trans_induction_on with
  | single edge => exact edge_strictly_increases edge
  | trans _ _ firstLt secondLt => exact Nat.lt_trans firstLt secondLt

theorem dependency_graph_acyclic (compiled : CompiledDerivation) (id : Nat) :
    ¬ Relation.TransGen (Edge compiled) id id := by
  intro cycle
  exact (Nat.lt_irrefl id) (dependency_path_strictly_increases cycle)

/-! ## Controls -/

namespace Canary

def source : Pattern :=
  a "tptp-semantic:source-digest" [a "admission-canary"]

def occurrence (index : Nat) : Pattern :=
  a "tptp-semantic:occurrence-id" [source, a (toString index)]

def span : Pattern := a "tptp92-ast:source-span" [a "0", a "1"]

def replaceFofHeader (formulaName annotations : Pattern) : Pattern -> Pattern
  | .apply "tptp92-ast:fof-annotated:alt-1" [_name, role, formula, _] =>
      a "tptp92-ast:fof-annotated:alt-1"
        [formulaName, role, formula, annotations]
  | pattern => pattern

def input (index : Nat) (formulaName : String) (annotations : Pattern) : Pattern :=
  encodeAnnotatedInput {
    occurrence := occurrence index
    payload := .fof
      (replaceFofHeader (TptpOfficialDerivationSyntax.Canary.name formulaName)
        annotations
        TptpOfficialAbstractSyntax.fofAnnotatedExample)
    span
  }

def absent : Pattern := a "tptp92-ast:annotations:alt-2"

def namedAnnotation (parent : String) : Pattern :=
  a "tptp92-ast:annotations:alt-1" [
    a "tptp92-ast:source:alt-1" [
      a "tptp92-ast:dag-source:alt-1" [
        TptpOfficialDerivationSyntax.Canary.name parent]],
    a "tptp92-ast:optional-info:alt-2"]

def nodes (first second : Pattern) : Pattern :=
  a "tptp-semantic:derivation-nodes-cons" [first,
    a "tptp-semantic:derivation-nodes-cons" [second,
      a "tptp-semantic:derivation-nodes-nil"]]

def chronological : Pattern :=
  a "tptp-semantic:derivation" [source,
    nodes (input 0 "initial" absent)
      (input 1 "derived" (namedAnnotation "initial"))]

theorem chronological_decodes : (decodeDerivation? chronological).isSome := by
  rfl

theorem chronological_compiles :
    match decodeDerivation? chronological with
    | none => False
    | some decoded => (compileDecoded? decoded).isSome := by
  rfl

def duplicateOccurrence : Pattern :=
  a "tptp-semantic:derivation" [source,
    nodes (input 0 "initial" absent)
      (encodeAnnotatedInput {
        occurrence := occurrence 0
        payload := .fof
          (replaceFofHeader (TptpOfficialDerivationSyntax.Canary.name "derived")
            (namedAnnotation "initial")
            TptpOfficialAbstractSyntax.fofAnnotatedExample)
        span
      })]

theorem duplicate_occurrence_fails_closed :
    match decodeDerivation? duplicateOccurrence with
    | none => False
    | some decoded => (compileDecoded? decoded).isNone := by
  rfl

def duplicateName : Pattern :=
  a "tptp-semantic:derivation" [source,
    nodes (input 0 "same" absent) (input 1 "same" absent)]

theorem duplicate_name_fails_closed :
    match decodeDerivation? duplicateName with
    | none => False
    | some decoded => (compileDecoded? decoded).isNone := by
  rfl

def foreignSource : Pattern :=
  a "tptp-semantic:source-digest" [a "foreign"]

def foreignOccurrence : Pattern :=
  a "tptp-semantic:occurrence-id" [foreignSource, a "1"]

def crossSourceOccurrence : Pattern :=
  a "tptp-semantic:derivation" [source,
    nodes (input 0 "initial" absent)
      (encodeAnnotatedInput {
        occurrence := foreignOccurrence
        payload := .fof
          (replaceFofHeader
            (TptpOfficialDerivationSyntax.Canary.name "foreign") absent
            TptpOfficialAbstractSyntax.fofAnnotatedExample)
        span
      })]

theorem cross_source_occurrence_fails_closed :
    decodeDerivation? crossSourceOccurrence = none := by
  rfl

def forwardReference : Pattern :=
  a "tptp-semantic:derivation" [source,
    nodes (input 0 "first" (namedAnnotation "later"))
      (input 1 "later" absent)]

theorem forward_reference_fails_closed :
    match decodeDerivation? forwardReference with
    | none => False
    | some decoded => (compileDecoded? decoded).isNone := by
  rfl

end Canary

#print axioms lookupEntry?_mem
#print axioms lookupEntry?_name
#print axioms resolveNames?_mem
#print axioms resolveNames?_names
#print axioms resolveNames?_below
#print axioms admitted_edges_strictly_decrease
#print axioms admitted_parent_names_exact
#print axioms admitted_names_unique
#print axioms admitted_occurrences_unique
#print axioms edge_strictly_increases
#print axioms dependency_path_strictly_increases
#print axioms dependency_graph_acyclic
#print axioms Canary.chronological_decodes
#print axioms Canary.chronological_compiles
#print axioms Canary.duplicate_occurrence_fails_closed
#print axioms Canary.duplicate_name_fails_closed
#print axioms Canary.cross_source_occurrence_fails_closed
#print axioms Canary.forward_reference_fails_closed

end Mettapedia.GSLT.LanguageDef.TptpOfficialDerivationAdmission
