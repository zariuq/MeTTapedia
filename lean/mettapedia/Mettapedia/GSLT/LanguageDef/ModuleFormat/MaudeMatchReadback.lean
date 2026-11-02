import Mettapedia.GSLT.LanguageDef.ModuleFormat.MaudeMatching
import Mettapedia.GSLT.LanguageDef.ModuleFormat.MaudeTermCodec
import Mettapedia.OSLF.MeTTaIL.GeneralFirstOrderMatchValues

/-! First-order captures decode to source valuations. A successful sorted
row match and its instantiated contractum therefore determine a typed source
instance. The valuation is read from the returned bindings, not supplied by
the producer being checked. -/

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 3000000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.MaudeCompilation

open Mettapedia.Languages
open Mettapedia.OSLF.MeTTaIL Syntax Match MatchSpec
open GeneralFirstOrderProjection
open Mettapedia.GSLT.LanguageDef.EquationSemantics

private theorem decode_arguments (patterns : List Pattern)
    (readable : ∀ pattern ∈ patterns, ∃ term, decode? pattern = some term ∧ encode term = pattern) :
    ∃ terms, patterns.mapM decode? = some terms ∧ terms.map encode = patterns := by
  induction patterns with
  | nil => exact ⟨[], rfl, rfl⟩
  | cons first rest ih =>
      obtain ⟨head, decodedHead, encodedHead⟩ := readable first (by simp)
      obtain ⟨tail, decodedTail, encodedTail⟩ := ih (fun pattern member => readable pattern (List.mem_cons_of_mem _ member))
      exact ⟨head :: tail, by simp [List.mapM_cons, decodedHead, decodedTail], by simp [encodedHead, encodedTail]⟩

theorem firstOrder_decodes {pattern : Pattern} (shape : FirstOrder pattern) :
    ∃ term, decode? pattern = some term ∧ encode term = pattern := by
  induction pattern using Pattern.inductionOn with
  | hfvar name => exact ⟨.var name, by rw [decode?], by rw [encode]⟩
  | happly label arguments ih =>
      cases shape with
      | constructor _ _ children =>
          obtain ⟨terms, decoded, encoded⟩ := decode_arguments arguments
            (fun child member => ih child member (children child member))
          refine ⟨.app label terms, ?_, ?_⟩
          · rw [decode?, decoded]
            rfl
          · rw [encode, encoded]
  | hbvar | hlambda | hmultiLambda | hsubst | hcollection => cases shape

def readAssignment (bindings : Bindings) : Maude.Valuation := fun name =>
  ((bindings.lookup name).bind decode?).getD (.var name)

theorem readAssignment_variable {bindings : Bindings}
    (values : ∀ entry ∈ bindings, FirstOrder entry.2) (name : String) :
    applyBindings bindings (.fvar name) = encode (readAssignment bindings name) := by
  rw [apply_variable]
  cases found : bindings.lookup name with
  | none => simp [readAssignment, found, encode]
  | some value =>
      obtain ⟨term, decoded, encoded⟩ := firstOrder_decodes (values (name, value) (raw_lookup_member found))
      simpa only [readAssignment, found, Option.bind_some, decoded, Option.getD_some] using encoded.symm

theorem readAssignment_substitution {bindings : Bindings}
    (values : ∀ entry ∈ bindings, FirstOrder entry.2) (term : Maude.Term) :
    applyBindings bindings (encode term) = encode (term.substitute (readAssignment bindings)) :=
  encode_substitute_of_variables bindings (readAssignment bindings) term
    (fun name _ => readAssignment_variable values name)

theorem matched_values_decode {left source : Maude.Term} {bindings : Bindings}
    (matched : bindings ∈ matchPattern (encode left) (encode source)) :
    ∀ entry ∈ bindings, FirstOrder entry.2 :=
  matched_values_firstOrder (encode_firstOrder left) (encode_firstOrder source) (matchPattern_sound matched)

theorem matching_source_readback {left source : Maude.Term} {bindings : Bindings}
    (matched : bindings ∈ matchPattern (encode left) (encode source)) :
    left.substitute (readAssignment bindings) = source := by
  have reconstructed := matching_reconstructs matched
  rw [readAssignment_substitution (matched_values_decode matched) left] at reconstructed
  exact encode_injective reconstructed

theorem readAssignment_typed (prepared : Prepared) (ambient declarations : Maude.VariableContext)
    {bindings : Bindings} (values : ∀ entry ∈ bindings, FirstOrder entry.2)
    (sorted : SortedBindingsIn prepared.language (freeContext ambient)
      (declarations.map fun entry => (entry.1, TypeExpr.base entry.2)) bindings) :
    Maude.TypedValuation prepared.source.signature ambient declarations (readAssignment bindings) := by
  intro name sort found
  obtain ⟨before, after, shape, _⟩ := List.lookup_eq_some_iff.mp found
  have member : (name, sort) ∈ declarations := by simp [shape]
  have typed := (sorted name (.base sort) (List.mem_map.mpr ⟨(name, sort), member, rfl⟩)).2
  rw [readAssignment_variable values name] at typed
  exact (prepared_typing_iff prepared ambient _ sort).mp typed

theorem sorted_row_instance_readback (prepared : Prepared) (ambient : Maude.VariableContext)
    (row : Maude.Row) (source target : Maude.Term) {bindings : Bindings}
    (matched : bindings ∈ matchPattern (encode row.left) (encode source))
    (applied : applyBindings bindings (encode row.right) = encode target)
    (sorted : SortedBindingsIn prepared.language (freeContext ambient) (context row) bindings) :
    ∃ assignment, Maude.TypedValuation prepared.source.signature ambient row.usedContext assignment ∧
      row.left.substitute assignment = source ∧ row.right.substitute assignment = target := by
  have values := matched_values_decode matched
  refine ⟨readAssignment bindings, readAssignment_typed prepared ambient row.usedContext values sorted,
    matching_source_readback matched, ?_⟩
  rw [readAssignment_substitution values row.right] at applied
  exact encode_injective applied

theorem sorted_row_matching_iff (prepared : Prepared) (ambient : Maude.VariableContext)
    (row : Maude.Row) (source target : Maude.Term)
    (checked : row.check prepared.source.signature = true) (inputs : row.inputsBound = true) :
    (∃ bindings, bindings ∈ matchPattern (encode row.left) (encode source) ∧
      applyBindings bindings (encode row.right) = encode target ∧
      SortedBindingsIn prepared.language (freeContext ambient) (context row) bindings) ↔
    ∃ assignment, Maude.TypedValuation prepared.source.signature ambient row.usedContext assignment ∧
      row.left.substitute assignment = source ∧ row.right.substitute assignment = target := by
  constructor
  · rintro ⟨bindings, matched, applied, sorted⟩
    exact sorted_row_instance_readback prepared ambient row source target matched applied sorted
  · rintro ⟨assignment, typed, sourceExact, targetExact⟩
    have bound : ∀ name ∈ row.right.variables, name ∈ row.left.variables := by
      have selected := inputs
      simp only [Maude.Row.inputsBound, List.all_eq_true, List.contains_iff_mem] at selected
      intro name member
      exact selected name (List.mem_append_left _ member)
    obtain ⟨bindings, matched, applied, compatible, _, domain⟩ :=
      match_instance_readout assignment row.left row.right bound
    have sorted := matching_bindings_sorted prepared ambient row.usedContext assignment row.left compatible domain
      (usedContext_distinct checked) (fun _ _ member => usedContext_bound inputs member) typed
    rw [sourceExact] at matched
    rw [targetExact] at applied
    exact ⟨bindings, matched, applied, sorted⟩

theorem source_equation_of_sorted_row_match (prepared : Prepared) (ambient : Maude.VariableContext)
    (row : Maude.Row) (source target : Maude.Term) (sort : String) {bindings : Bindings}
    (declared : row ∈ prepared.source.equations) (empty : row.conditions = [])
    (checked : row.check prepared.source.signature = true)
    (leftTyped : Maude.HasSort prepared.source.signature row.usedContext row.left sort)
    (rightTyped : Maude.HasSort prepared.source.signature row.usedContext row.right sort)
    (matched : bindings ∈ matchPattern (encode row.left) (encode source))
    (applied : applyBindings bindings (encode row.right) = encode target)
    (sorted : SortedBindingsIn prepared.language (freeContext ambient) (context row) bindings) :
    Maude.Equivalent prepared.source ambient sort source target := by
  obtain ⟨assignment, typed, sourceExact, targetExact⟩ :=
    sorted_row_instance_readback prepared ambient row source target matched applied sorted
  rw [← sourceExact, ← targetExact]
  exact .equation assignment declared checked leftTyped rightTyped typed (empty ▸ .nil assignment)

end Mettapedia.GSLT.LanguageDef.ModuleFormat.MaudeCompilation
