import Mettapedia.GSLT.LanguageDef.ModuleFormat.CHRBagMatchReadout
import Mettapedia.OSLF.MeTTaIL.GeneralScopedMatchRuleFields

/-! The compiled query retains its authored head order. Reading an actual
request match through the bag certificate supplies a source occurrence
selection; kept and removed heads use one source variable environment.
-/

set_option autoImplicit false
set_option maxHeartbeats 3000000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.CHRCompilation.RuleSelection

open Mettapedia.Languages.CHR
open Mettapedia.OSLF.MeTTaIL Syntax RuleBinding GeneralScopedMatch Match
open GeneralFirstOrderProjection

theorem compiled_data (vocabulary : Vocabulary) (query active : Nat) (source : Rule)
    (rule : RewriteRule) (compiled : compileRule? vocabulary query active source = some rule) :
    ∃ selected,
      active < source.heads.length ∧
      source.heads.zipIdx.mapM (OccurrenceEncoding.schema? vocabulary active) = some selected ∧
      rule.left = .apply (queryLabel query) (poolPatterns vocabulary ++
        [.fvar "chr:active", .apply "ChrStore" [.collection .hashBag selected (some "chr:rest")]]) ∧
      rule.right = .apply "ChrMatched"
        [vector (source.variables.eraseDups.map (fun index => .fvar (variableSlot index))),
         heads (selected.take source.kept.length), heads (selected.drop source.kept.length),
         .apply "ChrStore" [.fvar "chr:rest"]] := by
  unfold compileRule? at compiled
  split at compiled
  · rename_i within
    cases selectedRead : source.heads.zipIdx.mapM (fun (head, index) => do
        pure (occurrence (.fvar (idSlot index active)) (← head? vocabulary head))) with
    | none => rw [selectedRead] at compiled; cases compiled
    | some selected =>
      rw [selectedRead] at compiled
      let built : RewriteRule := {
        name := "chr-query:" ++ toString query
        typeContext := variableContext vocabulary source active
        premises := []
        left := Pattern.apply (queryLabel query) (poolPatterns vocabulary ++
          [.fvar "chr:active", .apply "ChrStore" [.collection .hashBag selected (some "chr:rest")]])
        right := Pattern.apply "ChrMatched"
          [vector (source.variables.eraseDups.map (fun index => .fvar (variableSlot index))),
           heads (selected.take source.kept.length), heads (selected.drop source.kept.length),
           .apply "ChrStore" [.fvar "chr:rest"]] }
      have same : built = rule := Option.some.inj compiled
      subst rule
      refine ⟨selected, within, ?_, rfl, rfl⟩
      have sameCompiler : (OccurrenceEncoding.schema? vocabulary active) =
          (fun (head, index) => do pure (occurrence (.fvar (idSlot index active)) (← head? vocabulary head))) := by
        funext entry
        rcases entry with ⟨head, index⟩
        rfl
      rw [sameCompiler]
      exact selectedRead
  · cases compiled

theorem request_readout (vocabulary : Vocabulary) (query activeSlot activeId : Nat)
    (source : Rule) (rule : RewriteRule) (store : List Occurrence) (known : List Pattern)
    (compiled : compileRule? vocabulary query activeSlot source = some rule)
    (encoded : store.mapM (OccurrenceEncoding.encode? vocabulary) = some known)
    {spec : RuleBindingSpec} {ambient : Nat} {captured chosen : ScopedRuleMatching.Assignment}
    (matched : Matches rule spec ambient .left [] 0 [] rule.left (request vocabulary query activeId known) captured)
    (later : Extends captured chosen) (roots : GeneralPremise.RootValues ambient chosen) :
    ∃ selected residual residualCodes,
      activeSlot < source.heads.length ∧
      store.Perm (selected ++ residual) ∧
      List.Forall₂ (BagMatchReadout.HeadReadout vocabulary (ordinary chosen) activeSlot) source.heads.zipIdx selected ∧
      List.Forall₂ (fun source target => OccurrenceEncoding.encode? vocabulary source = some target) residual residualCodes ∧
      (ordinary chosen).lookup "chr:rest" = some (.collection .hashBag residualCodes none) ∧
      (ordinary chosen).lookup "chr:active" = some (occurrenceRef activeId) := by
  obtain ⟨pools, activeRead⟩ := RequestPools.request_prefix vocabulary query activeSlot activeId source rule known
    compiled matched later roots
  obtain ⟨schemas, within, sourceCompiled, left, _⟩ := compiled_data vocabulary query activeSlot source rule compiled
  rw [left] at matched
  simp only [poolPatterns, request, List.cons_append, List.nil_append] at matched
  cases matched with
  | constructor arguments =>
    cases arguments with
    | cons predicates afterPredicates =>
      cases afterPredicates with
      | cons scalars afterScalars =>
        cases afterScalars with
        | cons active afterActive =>
          cases afterActive with
          | cons storeMatch endArgs =>
            cases endArgs
            cases storeMatch with
            | constructor storeArguments =>
              cases storeArguments with
              | cons bagMatch endArgs =>
                cases endArgs
                cases bagMatch with
                | bag _ bag =>
                  obtain ⟨selected, residual, residualCodes, conserved, headsRead, residualRead, restRead⟩ :=
                    BagMatchReadout.bag_readout vocabulary activeSlot source.heads.zipIdx schemas store known
                      pools sourceCompiled (OccurrenceEncoding.paired_of_mapM vocabulary store known encoded) bag later roots
                  exact ⟨selected, residual, residualCodes, within, conserved, headsRead, residualRead, restRead, activeRead⟩

theorem zip_variables (source : Rule) :
    source.heads.zipIdx.flatMap (fun entry => entry.1.variables) = source.variables := by
  change source.heads.zipIdx.flatMap (fun entry => entry.1.variables) = source.heads.flatMap Head.variables
  rw [← List.flatMap_map]
  simp

structure SourceReadout (vocabulary : Vocabulary) (bindings : Bindings)
    (activeSlot activeId : Nat) (source : Rule) (store : List Occurrence)
    (environment : Environment) (selection : Selection) : Prop where
  variableRead : TermReading.VariablesRead vocabulary environment bindings
  total : ∀ index ∈ source.variables, ∃ value, Mettapedia.Languages.CHR.lookup environment index = some value
  sourceMatch : selection.Matches source environment store
  active : selection.ActiveAt activeId activeSlot
  selected : List.Forall₂ (BagMatchReadout.HeadReadout vocabulary bindings activeSlot)
    source.heads.zipIdx selection.heads
  pools : RequestPools.Read vocabulary bindings
  remainder : ∃ residualCodes,
    selection.rest.mapM (OccurrenceEncoding.encode? vocabulary) = some residualCodes ∧
    bindings.lookup "chr:rest" = some (.collection .hashBag residualCodes none)

theorem source_selection (vocabulary : Vocabulary) (query activeSlot activeId : Nat)
    (source : Rule) (rule : RewriteRule) (store : List Occurrence) (known : List Pattern)
    (compiled : compileRule? vocabulary query activeSlot source = some rule)
    (encoded : store.mapM (OccurrenceEncoding.encode? vocabulary) = some known)
    (distinct : (store.map Occurrence.id).Nodup)
    {spec : RuleBindingSpec} {ambient : Nat} {captured chosen : ScopedRuleMatching.Assignment}
    (matched : Matches rule spec ambient .left [] 0 [] rule.left (request vocabulary query activeId known) captured)
    (later : Extends captured chosen) (roots : GeneralPremise.RootValues ambient chosen) :
    ∃ (environment : Environment) (selection : Selection),
      SourceReadout vocabulary (ordinary chosen) activeSlot activeId source store environment selection := by
  obtain ⟨pools, _⟩ := RequestPools.request_prefix vocabulary query activeSlot activeId source rule known
    compiled matched later roots
  obtain ⟨picked, residual, residualCodes, within, conserved, read, residualRead, restRead, activeRead⟩ :=
    request_readout vocabulary query activeSlot activeId source rule store known compiled encoded matched later roots
  have captures := BagMatchReadout.selected_variables vocabulary (ordinary chosen) activeSlot read
  rw [zip_variables] at captures
  obtain ⟨environment, variableRead, envUnique, envDomain, total⟩ :=
    VariableCaptures.environment_exists vocabulary (ordinary chosen) source.variables captures
  have instances := BagMatchReadout.selected_instances vocabulary (ordinary chosen) activeSlot environment
    variableRead read (by rw [zip_variables]; exact total)
  have headInstances : List.Forall₂ (fun head value => head.instantiate environment = some value.constraint)
      source.heads picked := by
    have mapped : List.Forall₂ (fun head value => head.instantiate environment = some value.constraint)
        (source.heads.zipIdx.map Prod.fst) picked := List.forall₂_map_left_iff.mpr instances
    simpa using mapped
  let selection : Selection := ⟨picked.take source.kept.length, picked.drop source.kept.length, residual⟩
  have selectedHeads : selection.heads = picked := by simp [selection, Selection.heads]
  have pickedUnique : (picked.map Occurrence.id).Nodup := by
    have allUnique : (picked.map Occurrence.id ++ residual.map Occurrence.id).Nodup := by
      simpa only [List.map_append] using (conserved.map Occurrence.id).nodup_iff.mp distinct
    exact (List.nodup_append.mp allUnique).1
  have sourceMatch : selection.Matches source environment store := by
    refine ⟨?_, ?_, ?_, ?_, envUnique, envDomain⟩
    · change store.Perm (picked.take source.kept.length ++ picked.drop source.kept.length ++ residual)
      rw [List.take_append_drop]
      exact conserved
    · rw [selectedHeads]
      exact pickedUnique
    · simpa [selection, Rule.heads] using List.forall₂_take source.kept.length headInstances
    · simpa [selection, Rule.heads] using List.forall₂_drop source.kept.length headInstances
  have pickedWithin : activeSlot < picked.length := by
    rw [← headInstances.length_eq]
    exact within
  have rowRead := read.get (by simpa using within) pickedWithin
  have selectedActive : (ordinary chosen).lookup "chr:active" = some (occurrenceRef picked[activeSlot].id) := by
    simpa [idSlot] using rowRead.identity
  have activeSame : picked[activeSlot].id = activeId :=
    ScalarReading.occurrence_injective (Option.some.inj (selectedActive.symm.trans activeRead))
  have active : selection.ActiveAt activeId activeSlot := by
    refine ⟨picked[activeSlot], ?_, activeSame⟩
    rw [selectedHeads]
    exact List.getElem?_eq_getElem pickedWithin
  exact ⟨environment, selection, variableRead, total, sourceMatch, active,
    by rw [selectedHeads]; exact read,
    pools, residualCodes, OccurrenceEncoding.paired_to_mapM vocabulary residualRead, restRead⟩

theorem source_selection_inferred (vocabulary : Vocabulary) (query activeSlot activeId : Nat)
    (source : Rule) (rule : RewriteRule) (store : List Occurrence) (known : List Pattern)
    (compiled : compileRule? vocabulary query activeSlot source = some rule)
    (encoded : store.mapM (OccurrenceEncoding.encode? vocabulary) = some known)
    (distinct : (store.map Occurrence.id).Nodup)
    {ambient : Nat} {captured : ScopedRuleMatching.Assignment}
    (matched : Matches rule (GeneralRuleBindingInference.inferredSpec rule) ambient .left [] 0 [] rule.left
      (request vocabulary query activeId known) captured) :
    ∃ (environment : Environment) (selection : Selection),
      SourceReadout vocabulary (ordinary captured) activeSlot activeId source store environment selection := by
  have zero : GeneralPremise.checkZeroDependencies (GeneralRuleBindingInference.inferredSpec rule) = true := by
    simp [GeneralPremise.checkZeroDependencies, GeneralRuleBindingInference.inferredSpec]
  have roots := GeneralPremise.matching_rootValues zero (by intro name value found; cases found) matched
  exact source_selection vocabulary query activeSlot activeId source rule store known compiled encoded distinct
    matched (by intro name value found; exact found) roots

theorem source_selection_elaborated (vocabulary : Vocabulary) (query activeSlot activeId : Nat)
    (source : Rule) (rule : RewriteRule) (binding : GeneralRuleBindingInference.BindingPlan)
    (store : List Occurrence) (known : List Pattern)
    (compiled : compileRule? vocabulary query activeSlot source = some rule)
    (encoded : store.mapM (OccurrenceEncoding.encode? vocabulary) = some known)
    (distinct : (store.map Occurrence.id).Nodup)
    {ambient : Nat} {captured : ScopedRuleMatching.Assignment}
    (matched : Matches (binding.elaborate rule) (GeneralRuleBindingInference.inferredSpec rule) ambient .left [] 0 []
      (binding.elaborate rule).left (request vocabulary query activeId known) captured) :
    ∃ (environment : Environment) (selection : Selection),
      SourceReadout vocabulary (ordinary captured) activeSlot activeId source store environment selection := by
  have raw := matched.rule_fields
    (show (binding.elaborate rule).left = rule.left from rfl)
    (show (binding.elaborate rule).right = rule.right from rfl)
    (show (binding.elaborate rule).premises = rule.premises from rfl)
  exact source_selection_inferred vocabulary query activeSlot activeId source rule store known
    compiled encoded distinct raw

#print axioms compiled_data
#print axioms request_readout
#print axioms source_selection
#print axioms source_selection_inferred
#print axioms source_selection_elaborated

end Mettapedia.GSLT.LanguageDef.ModuleFormat.CHRCompilation.RuleSelection
