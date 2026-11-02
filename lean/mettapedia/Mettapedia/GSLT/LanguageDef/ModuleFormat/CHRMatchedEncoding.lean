import Mettapedia.GSLT.LanguageDef.ModuleFormat.CHRSelectedEncoding

/-! Encoding a source selection and its environment produces the compiled
query's instantiated right side. The environment vector follows the authored
variable order, and kept/removed occurrences retain their original IDs.
-/

set_option autoImplicit false
set_option maxHeartbeats 3000000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.CHRCompilation.MatchedEncoding

open Mettapedia.Languages.CHR
open Mettapedia.OSLF.MeTTaIL Syntax Match RuleBinding ScopedRuleMatching GeneralScopedMatch
open GeneralFirstOrderProjection

def result? (vocabulary : Vocabulary) (environment : Environment) (indices : List Nat)
    (selection : Selection) : Option Pattern := do
  let values ← indices.mapM fun index =>
    (Mettapedia.Languages.CHR.lookup environment index).bind (value? vocabulary)
  let kept ← selection.kept.mapM (OccurrenceEncoding.encode? vocabulary)
  let removed ← selection.removed.mapM (OccurrenceEncoding.encode? vocabulary)
  let residual ← selection.rest.mapM (OccurrenceEncoding.encode? vocabulary)
  pure (.apply "ChrMatched" [vector values, heads kept, heads removed, store residual])

private theorem vector_substitution (bindings : Bindings) (patterns : List Pattern) :
    applyBindings bindings (vector patterns) = vector (patterns.map (applyBindings bindings)) := by
  simp only [vector, applyBindings, List.append_nil]

private theorem heads_substitution (bindings : Bindings) (patterns : List Pattern) :
    applyBindings bindings (heads patterns) = heads (patterns.map (applyBindings bindings)) := by
  simp only [heads, applyBindings, List.map_cons, List.map_nil, vector_substitution]

theorem compiled_result (vocabulary : Vocabulary) (query active : Nat) (source : Rule) (rule : RewriteRule)
    (bindings : Bindings) (environment : Environment) (schemas : List Pattern)
    (selected residual : List Occurrence) (residualCodes : List Pattern)
    (compiled : compileRule? vocabulary query active source = some rule)
    (schemasCompiled : source.heads.zipIdx.mapM (OccurrenceEncoding.schema? vocabulary active) = some schemas)
    (pools : RequestPools.Read vocabulary bindings)
    (variableRead : TermReading.VariablesRead vocabulary environment bindings)
    (total : ∀ index ∈ source.variables, ∃ value, Mettapedia.Languages.CHR.lookup environment index = some value)
    (selectedRead : List.Forall₂ (BagMatchReadout.HeadReadout vocabulary bindings active) source.heads.zipIdx selected)
    (restEncoded : residual.mapM (OccurrenceEncoding.encode? vocabulary) = some residualCodes)
    (restRead : bindings.lookup "chr:rest" = some (.collection .hashBag residualCodes none)) :
    result? vocabulary environment source.variables.eraseDups
      ⟨selected.take source.kept.length, selected.drop source.kept.length, residual⟩ =
      some (applyBindings bindings rule.right) := by
  obtain ⟨actualSchemas, _, actualCompiled, _, right⟩ := RuleSelection.compiled_data vocabulary query active source rule compiled
  have same : actualSchemas = schemas := Option.some.inj (actualCompiled.symm.trans schemasCompiled)
  subst actualSchemas
  have values := SelectedEncoding.environment_encoding vocabulary bindings environment source.variables.eraseDups
    variableRead (fun index member => total index (List.mem_eraseDups.mp member))
  have allRows := SelectedEncoding.selected_encoding vocabulary bindings active pools schemasCompiled selectedRead
  have paired := OccurrenceEncoding.paired_of_mapM vocabulary selected _ allRows
  have kept := OccurrenceEncoding.paired_to_mapM vocabulary (List.forall₂_take source.kept.length paired)
  have removed := OccurrenceEncoding.paired_to_mapM vocabulary (List.forall₂_drop source.kept.length paired)
  simp only [← List.map_take] at kept
  simp only [← List.map_drop] at removed
  have environmentSub : applyBindings bindings
      (vector (source.variables.eraseDups.map (fun index => Pattern.fvar (variableSlot index)))) =
      vector (source.variables.eraseDups.map (fun index => applyBindings bindings (.fvar (variableSlot index)))) := by
    simp only [vector_substitution, List.map_map, Function.comp_def]
  have residualSub : applyBindings bindings (.apply "ChrStore" [.fvar "chr:rest"]) = store residualCodes := by
    rw [applyBindings]
    simp only [List.map_cons, List.map_nil]
    rw [apply_variable, restRead]
    rfl
  rw [right, applyBindings]
  simp only [List.map_cons, List.map_nil, environmentSub, heads_substitution, residualSub]
  simp only [result?, values, kept, removed, restEncoded]
  rfl

theorem source_result (vocabulary : Vocabulary) (query activeSlot activeId : Nat)
    (source : Rule) (rule : RewriteRule) (store : List Occurrence) (bindings : Bindings)
    (environment : Environment) (selection : Selection)
    (compiled : compileRule? vocabulary query activeSlot source = some rule)
    (read : RuleSelection.SourceReadout vocabulary bindings activeSlot activeId source store environment selection) :
    result? vocabulary environment source.variables.eraseDups selection = some (applyBindings bindings rule.right) := by
  obtain ⟨schemas, _, schemasCompiled, _, _⟩ := RuleSelection.compiled_data vocabulary query activeSlot source rule compiled
  obtain ⟨residualCodes, restEncoded, restRead⟩ := read.remainder
  have keptLength : source.kept.length = selection.kept.length := read.sourceMatch.2.2.1.length_eq
  have kept : selection.heads.take source.kept.length = selection.kept := by
    rw [keptLength]
    simp [Selection.heads]
  have removed : selection.heads.drop source.kept.length = selection.removed := by
    rw [keptLength]
    simp [Selection.heads]
  have encoded := compiled_result vocabulary query activeSlot source rule bindings environment schemas
    selection.heads selection.rest residualCodes compiled schemasCompiled read.pools read.variableRead
    read.total read.selected restEncoded restRead
  simpa only [kept, removed] using encoded

theorem request_result (vocabulary : Vocabulary) (query activeSlot activeId : Nat)
    (source : Rule) (rule : RewriteRule) (store : List Occurrence) (known : List Pattern)
    (compiled : compileRule? vocabulary query activeSlot source = some rule)
    (encoded : store.mapM (OccurrenceEncoding.encode? vocabulary) = some known)
    (distinct : (store.map Occurrence.id).Nodup)
    {ambient : Nat} {captured : Assignment}
    (matched : Matches rule (GeneralRuleBindingInference.inferredSpec rule) ambient .left [] 0 [] rule.left
      (request vocabulary query activeId known) captured) :
    ∃ (environment : Environment) (selection : Selection),
      RuleSelection.SourceReadout vocabulary (ordinary captured) activeSlot activeId source store environment selection ∧
      result? vocabulary environment source.variables.eraseDups selection = some (applyBindings (ordinary captured) rule.right) := by
  obtain ⟨environment, selection, read⟩ := RuleSelection.source_selection_inferred vocabulary query activeSlot activeId
    source rule store known compiled encoded distinct matched
  exact ⟨environment, selection, read,
    source_result vocabulary query activeSlot activeId source rule store (ordinary captured) environment selection compiled read⟩

private theorem elements_binderFree (patterns : List Pattern)
    (free : ∀ pattern ∈ patterns, binderFree pattern = true) : binderFreeList patterns = true := by
  induction patterns with
  | nil => rfl
  | cons first rest ih =>
    exact Bool.and_eq_true_iff.mpr ⟨free first List.mem_cons_self,
      ih (fun child member => free child (List.mem_cons_of_mem first member))⟩

private theorem vector_shape_binderFree {schema : Pattern} (shape : VectorFirstOrder schema) :
    binderFree schema = true := by
  induction shape with
  | metavariable => rfl
  | constructor label arguments children ih => exact elements_binderFree arguments ih
  | vector arguments children ih => exact elements_binderFree arguments ih

theorem compiled_right_binderFree (vocabulary : Vocabulary) (query active : Nat) (source : Rule)
    (rule : RewriteRule) (compiled : compileRule? vocabulary query active source = some rule) :
    binderFree rule.right = true := by
  obtain ⟨schemas, _, _, left, right⟩ := RuleSelection.compiled_data vocabulary query active source rule compiled
  obtain ⟨checked, checkedLeft, shapes⟩ := HeadShape.compiled_rule_heads vocabulary query active source rule compiled
  have same : checked = schemas := by
    have arguments := (Pattern.apply.inj (checkedLeft.symm.trans left)).2
    have tails := List.append_cancel_left arguments
    simpa using tails
  subst checked
  have selectedFree : ∀ pattern ∈ schemas, binderFree pattern = true :=
    fun pattern member => vector_shape_binderFree (shapes pattern member)
  have kept := elements_binderFree (schemas.take source.kept.length)
    (fun pattern member => selectedFree pattern (List.mem_of_mem_take member))
  have removed := elements_binderFree (schemas.drop source.kept.length)
    (fun pattern member => selectedFree pattern (List.mem_of_mem_drop member))
  have values := elements_binderFree (source.variables.eraseDups.map (fun index => Pattern.fvar (variableSlot index)))
    (by intro pattern member; obtain ⟨index, _, rfl⟩ := List.mem_map.mp member; rfl)
  rw [right]
  simp only [binderFree, binderFreeList, vector, heads, kept, removed, values, Bool.true_and]

theorem request_scoped_result (vocabulary : Vocabulary) (query activeSlot activeId : Nat)
    (source : Rule) (rule : RewriteRule) (store : List Occurrence) (known : List Pattern)
    (compiled : compileRule? vocabulary query activeSlot source = some rule)
    (encoded : store.mapM (OccurrenceEncoding.encode? vocabulary) = some known)
    (distinct : (store.map Occurrence.id).Nodup)
    {ambient : Nat} {captured : Assignment} {operation : Pattern → Pattern → Pattern} {target : Pattern}
    (matched : Matches rule (GeneralRuleBindingInference.inferredSpec rule) ambient .left [] 0 [] rule.left
      (request vocabulary query activeId known) captured)
    (reduct : reductWith? operation rule (GeneralRuleBindingInference.inferredSpec rule)
      ambient captured = some target) :
    ∃ (environment : Environment) (selection : Selection),
      RuleSelection.SourceReadout vocabulary (ordinary captured) activeSlot activeId source store environment selection ∧
      result? vocabulary environment source.variables.eraseDups selection = some target := by
  have zero : GeneralPremise.checkZeroDependencies (GeneralRuleBindingInference.inferredSpec rule) = true := by
    simp [GeneralPremise.checkZeroDependencies, GeneralRuleBindingInference.inferredSpec]
  have roots := GeneralPremise.matching_rootValues zero (by intro name value found; cases found) matched
  have rightRead := binderFree_instantiation_readout
    (compiled_right_binderFree vocabulary query activeSlot source rule compiled) roots reduct
  obtain ⟨environment, selection, read, result⟩ := request_result vocabulary query activeSlot activeId source rule store known
    compiled encoded distinct matched
  exact ⟨environment, selection, read, result.trans (congrArg some rightRead)⟩

#print axioms compiled_result
#print axioms source_result
#print axioms request_result
#print axioms compiled_right_binderFree
#print axioms request_scoped_result

end Mettapedia.GSLT.LanguageDef.ModuleFormat.CHRCompilation.MatchedEncoding
