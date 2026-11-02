import Mettapedia.GSLT.LanguageDef.ModuleFormat.CHRVariableCaptures
import Mettapedia.GSLT.LanguageDef.ModuleFormat.CHROccurrenceEncoding

/-! Actual bag matches select source occurrences and preserve their residual.
Each selected head supplies variable readings, its occurrence identity, and
an instantiation law for every compatible source environment. These are
postconditions of the existing scoped relation, not a second matcher.
-/

set_option autoImplicit false
set_option maxHeartbeats 3000000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.CHRCompilation.BagMatchReadout

open Mettapedia.Languages.CHR
open Mettapedia.OSLF.MeTTaIL Syntax RuleBinding GeneralScopedMatch Match
open GeneralFirstOrderProjection

structure HeadReadout (vocabulary : Vocabulary) (bindings : Bindings) (active : Nat)
    (entry : Head × Nat) (value : Occurrence) : Prop where
  captured : VariableCaptures.Captured vocabulary bindings entry.1.variables
  identity : bindings.lookup (idSlot entry.2 active) = some (occurrenceRef value.id)
  instantiate : ∀ environment,
    TermReading.VariablesRead vocabulary environment bindings →
    (∀ index ∈ entry.1.variables, ∃ datum, Mettapedia.Languages.CHR.lookup environment index = some datum) →
    entry.1.instantiate environment = some value.constraint

theorem occurrence_readout (vocabulary : Vocabulary) (active : Nat) (entry : Head × Nat)
    (schema : Pattern) (value : Occurrence) (target : Pattern)
    {rule : RewriteRule} {spec : RuleBindingSpec} {ambient : Nat} {site : RulePatternSite} {path : List Nat}
    {initial captured chosen : ScopedRuleMatching.Assignment}
    (pools : RequestPools.Read vocabulary (ordinary chosen))
    (compiled : OccurrenceEncoding.schema? vocabulary active entry = some schema)
    (encoded : OccurrenceEncoding.encode? vocabulary value = some target)
    (matched : Matches rule spec ambient site path 0 initial schema target captured)
    (later : Extends captured chosen) (roots : GeneralPremise.RootValues ambient chosen) :
    HeadReadout vocabulary (ordinary chosen) active entry value := by
  obtain ⟨head, headCompiled, rfl⟩ := OccurrenceEncoding.schema_readout vocabulary active entry schema compiled
  obtain ⟨constraint, constraintEncoded, rfl⟩ := OccurrenceEncoding.readout vocabulary value target encoded
  cases matched with
  | constructor arguments =>
    cases arguments with
    | cons idMatch afterId =>
      have idRead : (ordinary chosen).lookup (idSlot entry.2 active) = some (occurrenceRef value.id) := by
        cases idMatch with
        | capture stored =>
          exact capture_ordinary_compatible stored (afterId.extends.trans later) roots
            (idSlot entry.2 active, occurrenceRef value.id) List.mem_cons_self
      cases afterId with
      | cons headMatch endArgs =>
        cases endArgs
        refine ⟨VariableCaptures.head_captures vocabulary entry.1 head value.constraint constraint
          headCompiled constraintEncoded headMatch later roots, idRead, ?_⟩
        intro environment variableRead total
        obtain ⟨sourceValue, instantiated⟩ := Head.instantiate_exists environment entry.1 total
        have same := HeadCorrespondence.matched_head_instance vocabulary environment entry.1 head constraint
          sourceValue value.constraint pools variableRead headCompiled instantiated constraintEncoded headMatch later roots
        exact same ▸ instantiated

theorem bag_readout (vocabulary : Vocabulary) (active : Nat) (entries : List (Head × Nat))
    (schemas : List Pattern) (sources : List Occurrence) (targets : List Pattern)
    {rule : RewriteRule} {spec : RuleBindingSpec} {ambient index : Nat} {site : RulePatternSite} {path : List Nat}
    {initial captured chosen : ScopedRuleMatching.Assignment}
    (pools : RequestPools.Read vocabulary (ordinary chosen))
    (compiled : entries.mapM (OccurrenceEncoding.schema? vocabulary active) = some schemas)
    (encoded : List.Forall₂ (fun source target => OccurrenceEncoding.encode? vocabulary source = some target) sources targets)
    (matched : Bag rule spec ambient site path 0 initial index schemas (some "chr:rest") .hashBag targets captured)
    (later : Extends captured chosen) (roots : GeneralPremise.RootValues ambient chosen) :
    ∃ selected residual residualCodes,
      sources.Perm (selected ++ residual) ∧
      List.Forall₂ (HeadReadout vocabulary (ordinary chosen) active) entries selected ∧
      List.Forall₂ (fun source target => OccurrenceEncoding.encode? vocabulary source = some target) residual residualCodes ∧
      (ordinary chosen).lookup "chr:rest" = some (.collection .hashBag residualCodes none) := by
  cases entries with
  | nil =>
    have empty : schemas = [] := by simpa using compiled.symm
    subst schemas
    cases matched with
    | rest stored =>
      have restRead := capture_ordinary_compatible stored later roots
        ("chr:rest", Pattern.collection .hashBag targets none) List.mem_cons_self
      exact ⟨[], sources, targets, by simp, .nil, encoded, restRead⟩
  | cons entry entries =>
    obtain ⟨schema, schemas, entryCompiled, restCompiled, rfl⟩ :=
      ValueInjectivity.traverse_cons (OccurrenceEncoding.schema? vocabulary active) entry entries schemas compiled
    cases matched with
    | cons selected within head tail =>
      obtain ⟨sourceWithin, sourceEncoded, residualEncoded⟩ := OccurrenceEncoding.selected vocabulary encoded selected within
      have headRead := occurrence_readout vocabulary active entry schema sources[selected] targets[selected]
        pools entryCompiled sourceEncoded head (tail.extends.trans later) roots
      obtain ⟨picked, residual, residualCodes, conserved, read, residualCode, restRead⟩ :=
        bag_readout vocabulary active entries schemas (sources.eraseIdx selected) (targets.eraseIdx selected)
          pools restCompiled residualEncoded tail later roots
      refine ⟨sources[selected] :: picked, residual, residualCodes, ?_, .cons headRead read, residualCode, restRead⟩
      simpa only [List.cons_append] using
        (List.getElem_cons_eraseIdx_perm sourceWithin).symm.trans (conserved.cons sources[selected])
termination_by entries.length

theorem selected_variables (vocabulary : Vocabulary) (bindings : Bindings) (active : Nat)
    {entries : List (Head × Nat)} {selected : List Occurrence}
    (read : List.Forall₂ (HeadReadout vocabulary bindings active) entries selected) :
    VariableCaptures.Captured vocabulary bindings (entries.flatMap (fun entry => entry.1.variables)) := by
  induction read with
  | nil => simp [VariableCaptures.Captured]
  | cons first tail ih =>
    intro index member
    rcases List.mem_append.mp (by simpa only [List.flatMap_cons] using member) with here | there
    · exact first.captured index here
    · exact ih index there

theorem selected_instances (vocabulary : Vocabulary) (bindings : Bindings) (active : Nat)
    (environment : Environment) (variableRead : TermReading.VariablesRead vocabulary environment bindings)
    {entries : List (Head × Nat)} {selected : List Occurrence}
    (read : List.Forall₂ (HeadReadout vocabulary bindings active) entries selected)
    (total : ∀ index ∈ entries.flatMap (fun entry => entry.1.variables),
      ∃ value, Mettapedia.Languages.CHR.lookup environment index = some value) :
    List.Forall₂ (fun entry value => entry.1.instantiate environment = some value.constraint) entries selected := by
  cases read with
  | nil => exact .nil
  | cons first rest =>
    refine .cons (first.instantiate environment variableRead ?_) ?_
    · intro index member
      exact total index (List.mem_append_left _ member)
    · exact selected_instances vocabulary bindings active environment variableRead rest
        (fun index member => total index (List.mem_append_right _ member))
termination_by entries.length

#print axioms occurrence_readout
#print axioms bag_readout
#print axioms selected_variables
#print axioms selected_instances

end Mettapedia.GSLT.LanguageDef.ModuleFormat.CHRCompilation.BagMatchReadout
