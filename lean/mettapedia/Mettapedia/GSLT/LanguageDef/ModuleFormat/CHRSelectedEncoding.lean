import Mettapedia.GSLT.LanguageDef.ModuleFormat.CHRRuleSelection

/-! Source occurrence selections encode to the actual instantiated query
schemas. The law uses the retained head readout and literal pools; it does
not select a new set of equal constraints when constructing the output.
-/

set_option autoImplicit false
set_option maxHeartbeats 3000000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.CHRCompilation.SelectedEncoding

open Mettapedia.Languages.CHR
open Mettapedia.OSLF.MeTTaIL Syntax Match
open GeneralFirstOrderProjection

theorem occurrence_encoding (vocabulary : Vocabulary) (bindings : Bindings) (active : Nat)
    (entry : Head × Nat) (value : Occurrence) (schema : Pattern)
    (pools : RequestPools.Read vocabulary bindings)
    (compiled : OccurrenceEncoding.schema? vocabulary active entry = some schema)
    (read : BagMatchReadout.HeadReadout vocabulary bindings active entry value) :
    OccurrenceEncoding.encode? vocabulary value = some (applyBindings bindings schema) := by
  obtain ⟨head, headCompiled, rfl⟩ := OccurrenceEncoding.schema_readout vocabulary active entry schema compiled
  obtain ⟨environment, variableRead, _, _, total⟩ :=
    VariableCaptures.environment_exists vocabulary bindings entry.1.variables read.captured
  have instantiated := read.instantiate environment variableRead total
  have encoded := TermReading.head_instantiation vocabulary environment bindings pools variableRead
    entry.1 head value.constraint headCompiled instantiated
  simp only [OccurrenceEncoding.encode?, encoded]
  rw [occurrence, applyBindings]
  simp only [List.map_cons, List.map_nil]
  rw [apply_variable, read.identity]
  rfl

theorem selected_encoding (vocabulary : Vocabulary) (bindings : Bindings) (active : Nat)
    {entries : List (Head × Nat)} {schemas : List Pattern} {selected : List Occurrence}
    (pools : RequestPools.Read vocabulary bindings)
    (compiled : entries.mapM (OccurrenceEncoding.schema? vocabulary active) = some schemas)
    (read : List.Forall₂ (BagMatchReadout.HeadReadout vocabulary bindings active) entries selected) :
    selected.mapM (OccurrenceEncoding.encode? vocabulary) = some (schemas.map (applyBindings bindings)) := by
  cases read with
  | nil =>
    have empty : schemas = [] := by simpa using compiled.symm
    subst schemas
    rfl
  | cons first rest =>
    obtain ⟨schema, schemas, headCompiled, tailCompiled, rfl⟩ :=
      ValueInjectivity.traverse_cons (OccurrenceEncoding.schema? vocabulary active) _ _ schemas compiled
    have headRead := occurrence_encoding vocabulary bindings active _ _ schema pools headCompiled first
    have tailRead := selected_encoding vocabulary bindings active pools tailCompiled rest
    simp only [List.mapM_cons, List.map_cons, headRead, tailRead]
    rfl
termination_by entries.length

theorem environment_encoding (vocabulary : Vocabulary) (bindings : Bindings) (environment : Environment)
    (indices : List Nat) (variableRead : TermReading.VariablesRead vocabulary environment bindings)
    (total : ∀ index ∈ indices, ∃ value, Mettapedia.Languages.CHR.lookup environment index = some value) :
    indices.mapM (fun index => (Mettapedia.Languages.CHR.lookup environment index).bind (value? vocabulary)) =
      some (indices.map (fun index => applyBindings bindings (.fvar (variableSlot index)))) := by
  induction indices with
  | nil => rfl
  | cons index indices ih =>
    obtain ⟨value, found⟩ := total index List.mem_cons_self
    obtain ⟨code, encoded, stored⟩ := variableRead index value found
    have first : (Mettapedia.Languages.CHR.lookup environment index).bind (value? vocabulary) =
        some (applyBindings bindings (.fvar (variableSlot index))) := by
      rw [found, apply_variable, stored]
      simpa using encoded
    have rest := ih (fun queried member => total queried (List.mem_cons_of_mem index member))
    simp only [List.mapM_cons, List.map_cons, first, rest]
    rfl

#print axioms occurrence_encoding
#print axioms selected_encoding
#print axioms environment_encoding

end Mettapedia.GSLT.LanguageDef.ModuleFormat.CHRCompilation.SelectedEncoding
