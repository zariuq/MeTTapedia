import Mettapedia.GSLT.LanguageDef.ModuleFormat.CHRHeadCorrespondence
import Mettapedia.Languages.CHR.Instantiation

/-! Every variable in a matched compiled term has an encoded source value in
the retained assignment. The value comes from the actual source input, not
from an assumed source environment. Repeated variables share that assignment.
-/

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 3000000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.CHRCompilation.VariableCaptures

open Mettapedia.Languages.CHR
open Mettapedia.OSLF.MeTTaIL Syntax RuleBinding GeneralScopedMatch Match
open GeneralFirstOrderProjection

def Captured (vocabulary : Vocabulary) (bindings : Bindings) (indices : List Nat) : Prop :=
  ∀ index ∈ indices, ∃ value code,
    value? vocabulary value = some code ∧ bindings.lookup (variableSlot index) = some code

private theorem constructor_label {rule : RewriteRule} {spec : RuleBindingSpec} {ambient : Nat}
    {site : RulePatternSite} {path : List Nat} {initial captured : ScopedRuleMatching.Assignment}
    {expected actual : String} {schemas targets : List Pattern}
    (matched : Matches rule spec ambient site path 0 initial (.apply expected schemas) (.apply actual targets) captured) :
    expected = actual := by
  cases matched
  rfl

mutual
  theorem term_captures (vocabulary : Vocabulary) (source : Mettapedia.Languages.CHR.Term)
      (schema : Pattern) (value : Value) (target : Pattern)
      {rule : RewriteRule} {spec : RuleBindingSpec} {ambient : Nat} {site : RulePatternSite} {path : List Nat}
      {initial captured chosen : ScopedRuleMatching.Assignment}
      (compiled : term? vocabulary source = some schema) (encoded : value? vocabulary value = some target)
      (matched : Matches rule spec ambient site path 0 initial schema target captured)
      (later : Extends captured chosen) (roots : GeneralPremise.RootValues ambient chosen) :
      Captured vocabulary (ordinary chosen) source.variables := by
    cases source with
    | value datum => simp [Term.variables, Captured]
    | var index =>
      have same : Pattern.fvar (variableSlot index) = schema := by
        simpa only [term?, Option.some.injEq] using compiled
      subst schema
      cases matched with
      | capture stored =>
        have read := capture_ordinary_compatible stored later roots (variableSlot index, target) List.mem_cons_self
        intro queried member
        have same : queried = index := by simpa only [Term.variables, List.mem_singleton] using member
        subst queried
        exact ⟨value, target, encoded, read⟩
    | tuple fields =>
      rw [term?] at compiled
      change ((fields.mapM (term? vocabulary)).bind fun values =>
        some (Pattern.apply "ChrTuple" [vector values])) = some schema at compiled
      simp only [Option.bind_eq_some_iff, Option.some.injEq] at compiled
      obtain ⟨schemas, fieldsCompiled, rfl⟩ := compiled
      cases value with
      | integer number =>
        have same : integer number = target := by simpa only [value?, Option.some.injEq] using encoded
        subst target
        unfold integer at matched
        have impossible := constructor_label matched
        simp at impossible
      | atom name =>
        cases atIndex : vocabulary.scalars.idxOf? (.atom name) with
        | none => simp [value?, atIndex] at encoded
        | some index =>
          have same : scalarRef index = target := by simpa [value?, atIndex] using encoded
          subst target
          unfold scalarRef at matched
          cases matched
      | tuple values =>
        obtain ⟨targets, valuesEncoded, rfl⟩ := ValueInjectivity.tuple_encoding vocabulary values target encoded
        cases matched with
        | constructor arguments =>
          cases arguments with
          | cons vectorMatch endArgs =>
            cases endArgs
            have children := fixed_vector_arguments (by simpa only [vector] using vectorMatch)
            simpa only [Term.variables] using arguments_captures vocabulary fields schemas values targets
              fieldsCompiled valuesEncoded children later roots
  termination_by sizeOf source

  theorem arguments_captures (vocabulary : Vocabulary) (sources : List Mettapedia.Languages.CHR.Term)
      (schemas : List Pattern) (values : List Value) (targets : List Pattern)
      {rule : RewriteRule} {spec : RuleBindingSpec} {ambient index : Nat}
      {site : RulePatternSite} {path : List Nat} {initial captured chosen : ScopedRuleMatching.Assignment}
      (compiled : sources.mapM (term? vocabulary) = some schemas)
      (encoded : values.mapM (value? vocabulary) = some targets)
      (matched : Arguments rule spec ambient site path 0 initial index schemas targets captured)
      (later : Extends captured chosen) (roots : GeneralPremise.RootValues ambient chosen) :
      Captured vocabulary (ordinary chosen) (sources.flatMap Term.variables) := by
    cases sources with
    | nil => simp [Captured]
    | cons source sources =>
      obtain ⟨schema, schemas, sourceCompiled, restCompiled, rfl⟩ :=
        ValueInjectivity.traverse_cons (term? vocabulary) source sources schemas compiled
      cases values with
      | nil =>
        have empty : targets = [] := by simpa using encoded.symm
        subst targets
        cases matched
      | cons value values =>
        obtain ⟨target, targets, valueEncoded, restEncoded, rfl⟩ :=
          ValueInjectivity.traverse_cons (value? vocabulary) value values targets encoded
        cases matched with
        | cons first rest =>
          have firstRead := term_captures vocabulary source schema value target sourceCompiled valueEncoded
            first (rest.extends.trans later) roots
          have restRead := arguments_captures vocabulary sources schemas values targets restCompiled restEncoded rest later roots
          intro queried member
          rcases List.mem_append.mp (by simpa only [List.flatMap_cons] using member) with here | there
          · exact firstRead queried here
          · exact restRead queried there
  termination_by sizeOf sources
end

theorem head_captures (vocabulary : Vocabulary) (source : Head) (schema : Pattern)
    (value : Constraint) (target : Pattern)
    {rule : RewriteRule} {spec : RuleBindingSpec} {ambient : Nat} {site : RulePatternSite} {path : List Nat}
    {initial captured chosen : ScopedRuleMatching.Assignment}
    (compiled : head? vocabulary source = some schema) (encoded : constraint? vocabulary value = some target)
    (matched : Matches rule spec ambient site path 0 initial schema target captured)
    (later : Extends captured chosen) (roots : GeneralPremise.RootValues ambient chosen) :
    Captured vocabulary (ordinary chosen) source.variables := by
  change ((vocabulary.predicates.idxOf? source.name).bind fun index =>
    (source.arguments.mapM (term? vocabulary)).bind fun fields =>
      some (Pattern.apply "ChrConstraint" [.fvar (predicateSlot index), vector fields])) = some schema at compiled
  change ((vocabulary.predicates.idxOf? value.name).bind fun index =>
    (value.arguments.mapM (value? vocabulary)).bind fun fields =>
      some (Pattern.apply "ChrConstraint" [predicateRef index, vector fields])) = some target at encoded
  simp only [Option.bind_eq_some_iff, Option.some.injEq] at compiled encoded
  obtain ⟨_, _, schemas, fieldsCompiled, rfl⟩ := compiled
  obtain ⟨_, _, targets, valuesEncoded, rfl⟩ := encoded
  cases matched with
  | constructor arguments =>
    cases arguments with
    | cons predicateMatch afterPredicate =>
      cases afterPredicate with
      | cons vectorMatch endArgs =>
        cases endArgs
        have children := fixed_vector_arguments (by simpa only [vector] using vectorMatch)
        exact arguments_captures vocabulary source.arguments schemas value.arguments targets
          fieldsCompiled valuesEncoded children later roots

theorem environment_exists (vocabulary : Vocabulary) (bindings : Bindings) (indices : List Nat)
    (captures : Captured vocabulary bindings indices) :
    ∃ environment,
      TermReading.VariablesRead vocabulary environment bindings ∧
      (environment.map Prod.fst).Nodup ∧
      (∀ binding ∈ environment, binding.1 ∈ indices) ∧
      ∀ index ∈ indices, ∃ value, Mettapedia.Languages.CHR.lookup environment index = some value := by
  induction indices with
  | nil =>
    refine ⟨[], ?_, List.nodup_nil, ?_, ?_⟩
    · intro index value found
      simp [Mettapedia.Languages.CHR.lookup] at found
    · intro binding member
      cases member
    · intro index member
      cases member
  | cons index indices ih =>
    have restCaptures : Captured vocabulary bindings indices :=
      fun queried member => captures queried (List.mem_cons_of_mem index member)
    obtain ⟨environment, read, unique, domain, total⟩ := ih restCaptures
    by_cases present : index ∈ indices
    · refine ⟨environment, read, unique, ?_, ?_⟩
      · intro binding member
        exact List.mem_cons_of_mem index (domain binding member)
      · intro queried member
        rcases List.mem_cons.mp member with rfl | member
        · exact total queried present
        · exact total queried member
    · obtain ⟨value, code, encoded, stored⟩ := captures index List.mem_cons_self
      let expanded : Environment := (index, value) :: environment
      refine ⟨expanded, ?_, ?_, ?_, ?_⟩
      · intro queried datum found
        change Mettapedia.Languages.CHR.lookup ((index, value) :: environment) queried = some datum at found
        by_cases same : index = queried
        · subst queried
          have valuesSame : value = datum := by simpa only [lookup_cons, beq_self_eq_true, if_true, Option.some.injEq] using found
          subst datum
          exact ⟨code, encoded, stored⟩
        · have skipped : (index == queried) = false := beq_eq_false_iff_ne.mpr same
          exact read queried datum (by simpa only [lookup_cons, skipped, Bool.false_eq_true, if_false] using found)
      · change (index :: environment.map Prod.fst).Nodup
        refine List.nodup_cons.mpr ⟨?_, unique⟩
        intro member
        obtain ⟨binding, inEnvironment, same⟩ := List.mem_map.mp member
        exact present (same ▸ domain binding inEnvironment)
      · intro binding member
        rcases List.mem_cons.mp member with rfl | member
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem index (domain binding member)
      · intro queried member
        rcases List.mem_cons.mp member with rfl | member
        · exact ⟨value, by simp [expanded, lookup_cons]⟩
        · obtain ⟨datum, found⟩ := total queried member
          have different : index ≠ queried := by
            intro same
            subst queried
            exact present member
          have skipped : (index == queried) = false := beq_eq_false_iff_ne.mpr different
          exact ⟨datum, by simpa only [expanded, lookup_cons, skipped, Bool.false_eq_true, if_false] using found⟩

theorem source_head_of_match (vocabulary : Vocabulary) (source : Head) (schema : Pattern)
    (value : Constraint) (target : Pattern)
    {rule : RewriteRule} {spec : RuleBindingSpec} {ambient : Nat} {site : RulePatternSite} {path : List Nat}
    {initial captured chosen : ScopedRuleMatching.Assignment}
    (pools : RequestPools.Read vocabulary (ordinary chosen))
    (compiled : head? vocabulary source = some schema) (encoded : constraint? vocabulary value = some target)
    (matched : Matches rule spec ambient site path 0 initial schema target captured)
    (later : Extends captured chosen) (roots : GeneralPremise.RootValues ambient chosen) :
    ∃ environment,
      source.instantiate environment = some value ∧
      (environment.map Prod.fst).Nodup ∧
      ∀ binding ∈ environment, binding.1 ∈ source.variables := by
  have captures := head_captures vocabulary source schema value target compiled encoded matched later roots
  obtain ⟨environment, read, unique, domain, total⟩ :=
    environment_exists vocabulary (ordinary chosen) source.variables captures
  obtain ⟨sourceValue, instantiated⟩ := Head.instantiate_exists environment source total
  have same := HeadCorrespondence.matched_head_instance vocabulary environment source schema target sourceValue value
    pools read compiled instantiated encoded matched later roots
  exact ⟨environment, same ▸ instantiated, unique, domain⟩

#print axioms term_captures
#print axioms arguments_captures
#print axioms head_captures
#print axioms environment_exists
#print axioms source_head_of_match

end Mettapedia.GSLT.LanguageDef.ModuleFormat.CHRCompilation.VariableCaptures
