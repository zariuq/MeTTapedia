import Mettapedia.Languages.VibeITP.Presentation.Theory
import Mettapedia.Languages.VibeITP.Presentation.Instances
import Std.Data.String.ToNat

/-!
# Vibe-ITP presentation: validation of concrete kernel packages

The fixed package and its admitted theory facts use the same declared data
constructors and judgments. Encodings are structurally valid independently of
the mathematical status of a theory's axioms. The allocated-symbol, axiom and
definition identifiers occupy separate namespaces and enumerate distinct
indices, so the extended package has exact rule lookup.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Mettapedia.Languages.VibeITP.Presentation

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Substitution
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.GSLT.LanguageDef.InferenceInstantiationBridge
open Mettapedia.Languages.VibeITP.Spec

mutual
theorem isData_fragment (formals : List (String × Nat)) :
    ∀ {p : Pattern}, IsData p → BindingSchemaFragment formals p
  | .apply _ args, .apply _ _ h => .apply (isDataList_fragment formals args h)
theorem isDataList_fragment (formals : List (String × Nat)) :
    ∀ (ps : List Pattern), (∀ p ∈ ps, IsData p) → BindingSchemasFragment formals ps
  | [], _ => .nil
  | p :: ps, h => .cons (isData_fragment formals (h p (by simp)))
      (isDataList_fragment formals ps (fun q hq => h q (by simp [hq])))
end

set_option maxRecDepth 100000 in
theorem kernelRules_foPackage : FOPackage kernelRules := by
  have hn : kernelRules.all (fun r => decide r.vars.Nodup) = true := by decide +kernel
  have hp : kernelRules.all
      (fun r => checkBindingSchemasFragment r.formals r.premises) = true := by decide +kernel
  have hc : kernelRules.all
      (fun r => checkBindingSchemaFragment r.formals r.conclusion) = true := by decide +kernel
  exact ⟨fun r hr => of_decide_eq_true ((List.all_eq_true.mp hn) r hr),
    fun r hr => bindingSchemasFragment_of_check ((List.all_eq_true.mp hp) r hr),
    fun r hr => bindingSchemaFragment_of_check ((List.all_eq_true.mp hc) r hr)⟩

theorem closedRule_foPackage (id : String) {p : Pattern} (hp : IsData p) :
    FOPackage [mkRule id [] [] p] := by
  constructor
  · intro r hr
    have : r = mkRule id [] [] p := by simpa using hr
    subst r
    exact List.nodup_nil
  · intro r hr
    have : r = mkRule id [] [] p := by simpa using hr
    subst r
    exact .nil
  · intro r hr
    have : r = mkRule id [] [] p := by simpa using hr
    subst r
    exact isData_fragment _ hp

theorem theoryRules_foPackage (T : Theory) (allocated : Nat) :
    FOPackage (theoryRules T allocated) := by
  have closed : ∀ r ∈ theoryRules T allocated,
      ∃ id p, r = mkRule id [] [] p ∧ IsData p := by
    intro r hr
    simp only [theoryRules, List.mem_append] at hr
    rcases hr with (hr | hr) | hr
    · obtain ⟨n, _, rfl⟩ := List.mem_map.mp hr
      exact ⟨_, _, rfl, IsData.app1 _ (isData_encSym T.sig _)⟩
    · obtain ⟨k, φ, _, rfl⟩ := mem_axiomRules hr
      exact ⟨_, _, rfl, IsData.app1 _ (isData_encTerm T.sig _)⟩
    · obtain ⟨k, d, _, rfl⟩ := mem_theoryDefinitionRules hr
      exact ⟨_, _, rfl, IsData.app1 _ (isData_encTerm T.sig _)⟩
  constructor
  · intro r hr
    obtain ⟨id, p, rfl, _⟩ := closed r hr
    exact List.nodup_nil
  · intro r hr
    obtain ⟨id, p, rfl, _⟩ := closed r hr
    exact .nil
  · intro r hr
    obtain ⟨id, p, rfl, hp⟩ := closed r hr
    exact isData_fragment _ hp

theorem FOPackage.append {first second : List FORule}
    (hf : FOPackage first) (hs : FOPackage second) : FOPackage (first ++ second) := by
  constructor
  · intro r hr
    exact (List.mem_append.mp hr).elim (hf.nodup r) (hs.nodup r)
  · intro r hr
    exact (List.mem_append.mp hr).elim (hf.premisesFragment r) (hs.premisesFragment r)
  · intro r hr
    exact (List.mem_append.mp hr).elim (hf.conclusionFragment r) (hs.conclusionFragment r)

def KernelDataValid (p : Pattern) : Prop :=
  fixedConstructorsValid kernelDefinition.toLanguageDef p = true

theorem kernelConstructorArity (head : String) (arity : Nat)
    (h : (head, arity) ∈ constructorArities) :
    languageHasConstructorArity kernelDefinition.toLanguageDef head arity = true := by
  have hall : constructorArities.all (fun entry =>
      languageHasConstructorArity kernelDefinition.toLanguageDef entry.1 entry.2) = true := by
    decide +kernel
  exact (List.all_eq_true.mp hall) (head, arity) h

theorem kernelDataList_valid : ∀ (ps : List Pattern),
    (∀ p ∈ ps, KernelDataValid p) →
      fixedConstructorListsValid kernelDefinition.toLanguageDef ps = true
  | [], _ => by simp [fixedConstructorListsValid]
  | p :: ps, h => by
      simp only [fixedConstructorListsValid, Bool.and_eq_true]
      exact ⟨h p (by simp), kernelDataList_valid ps (fun q hq => h q (by simp [hq]))⟩

theorem kernelData_app (head : String) (args : List Pattern)
    (hhead : (head, args.length) ∈ constructorArities)
    (hargs : ∀ p ∈ args, KernelDataValid p) : KernelDataValid (.apply head args) := by
  unfold KernelDataValid
  simp only [fixedConstructorsValid]
  exact Bool.and_eq_true_iff.mpr
    ⟨kernelConstructorArity head args.length hhead, kernelDataList_valid args hargs⟩

theorem kernelData_app0 (head : String) (hhead : (head, 0) ∈ constructorArities) :
    KernelDataValid (.apply head []) := kernelData_app head [] hhead (by simp)

theorem kernelData_app1 (head : String) {p : Pattern}
    (hhead : (head, 1) ∈ constructorArities) (hp : KernelDataValid p) :
    KernelDataValid (.apply head [p]) := kernelData_app head [p] hhead (by simpa using hp)

theorem kernelData_app2 (head : String) {p q : Pattern}
    (hhead : (head, 2) ∈ constructorArities) (hp : KernelDataValid p) (hq : KernelDataValid q) :
    KernelDataValid (.apply head [p, q]) := kernelData_app head [p, q] hhead (by simp [hp, hq])

theorem kernelData_app3 (head : String) {p q r : Pattern}
    (hhead : (head, 3) ∈ constructorArities)
    (hp : KernelDataValid p) (hq : KernelDataValid q) (hr : KernelDataValid r) :
    KernelDataValid (.apply head [p, q, r]) :=
  kernelData_app head [p, q, r] hhead (by simp [hp, hq, hr])

theorem kernelData_encPos : ∀ n : Nat, KernelDataValid (encPos n) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
      obtain ⟨k, hk | hk⟩ := nat_even_or_odd n
      · subst hk
        by_cases hk0 : k = 0
        · subst hk0; exact kernelData_app0 _ (by decide)
        · rw [encPos_even k (by omega)]
          exact kernelData_app1 _ (by decide) (ih k (by omega))
      · subst hk
        by_cases hk0 : k = 0
        · subst hk0; exact kernelData_app0 _ (by decide)
        · rw [encPos_odd k (by omega)]
          exact kernelData_app1 _ (by decide) (ih k (by omega))

theorem kernelData_encNat (n : Nat) : KernelDataValid (encNat n) := by
  unfold encNat
  split
  · exact kernelData_app0 _ (by decide)
  · exact kernelData_app1 _ (by decide) (kernelData_encPos n)

theorem kernelData_encBool (b : Bool) : KernelDataValid (encBool b) := by
  cases b <;> exact kernelData_app0 _ (by decide)

theorem kernelData_encKind (kind : SymKind) : KernelDataValid (encKind kind) := by
  cases kind <;> exact kernelData_app0 _ (by decide)

theorem kernelData_encList : ∀ (ps : List Pattern), (∀ p ∈ ps, KernelDataValid p) →
    KernelDataValid (encList ps)
  | [], _ => kernelData_app0 _ (by decide)
  | p :: ps, h => kernelData_app2 _ (by decide) (h p (by simp))
      (kernelData_encList ps (fun q hq => h q (by simp [hq])))

theorem kernelData_encNatList (ns : List Nat) : KernelDataValid (encNatList ns) :=
  kernelData_encList _ (by simp [kernelData_encNat])

theorem kernelData_encBytes (bytes : List UInt8) : KernelDataValid (encBytes bytes) :=
  kernelData_encList _ (by simp [kernelData_encNat])

theorem kernelData_encSym (sig : Sig) (s : SymId) : KernelDataValid (encSym sig s) := by
  unfold encSym
  split
  · exact kernelData_app3 _ (by decide) (kernelData_encNat _)
      (kernelData_encKind _) (kernelData_encNatList _)
  · exact kernelData_app3 _ (by decide) (kernelData_encNat _)
      (kernelData_app0 _ (by decide)) (kernelData_app0 _ (by decide))

mutual
theorem kernelData_encTerm (sig : Sig) : ∀ t : Term, KernelDataValid (encTerm sig t)
  | .bvar i => kernelData_app1 _ (by decide) (kernelData_encNat i)
  | .lit bytes => kernelData_app1 _ (by decide) (kernelData_encBytes bytes)
  | .app s args => kernelData_app3 _ (by decide) (kernelData_encSym sig s)
      (kernelData_encTermList sig args)
      (kernelData_app2 _ (by decide) (kernelData_encNat _) (kernelData_encBool _))
theorem kernelData_encTermList (sig : Sig) :
    ∀ ts : List Term, KernelDataValid (encTermList sig ts)
  | [] => kernelData_app0 _ (by decide)
  | t :: ts => kernelData_app2 _ (by decide) (kernelData_encTerm sig t)
      (kernelData_encTermList sig ts)
end

/-! ## Closed schemas and judgment declarations -/

mutual
theorem isData_noCollectionRest : ∀ {p : Pattern}, IsData p →
    patternHasNoCollectionRest p = true
  | .apply _ args, .apply _ _ h => by
      simp only [patternHasNoCollectionRest]
      exact isDataList_noCollectionRest args h
theorem isDataList_noCollectionRest : ∀ (ps : List Pattern), (∀ p ∈ ps, IsData p) →
    patternsHaveNoCollectionRest ps = true
  | [], _ => by simp [patternsHaveNoCollectionRest]
  | p :: ps, h => by
      simp only [patternsHaveNoCollectionRest, Bool.and_eq_true]
      exact ⟨isData_noCollectionRest (h p (by simp)),
        isDataList_noCollectionRest ps (fun q hq => h q (by simp [hq]))⟩
end

mutual
theorem isData_noOccurrences : ∀ {p : Pattern}, IsData p →
    patternMetavariableOccurrencesAt 0 p = []
  | .apply _ args, .apply _ _ h => by
      simp only [patternMetavariableOccurrencesAt]
      exact isDataList_noOccurrences args h
theorem isDataList_noOccurrences : ∀ (ps : List Pattern), (∀ p ∈ ps, IsData p) →
    patternsMetavariableOccurrencesAt 0 ps = []
  | [], _ => by simp [patternsMetavariableOccurrencesAt]
  | p :: ps, h => by
      simp only [patternsMetavariableOccurrencesAt]
      rw [isData_noOccurrences (h p (by simp)),
        isDataList_noOccurrences ps (fun q hq => h q (by simp [hq]))]
      rfl
end

theorem closedRule_locallyValid (id : String) (hid : id ≠ "") {p : Pattern}
    (hp : IsData p) : RuleSchema.isLocallyValid (mkRule id [] [] p).toSchema = true := by
  have hscope : p.isWellScoped = true := isWellScoped_of_isGround (isData_ground p hp)
  simp [RuleSchema.isLocallyValid, RuleSchema.metavariableNames, RuleSchema.patterns,
    RuleSchema.occurrences, FORule.toSchema, FORule.formals, mkRule, hid,
    patternsMetavariableOccurrencesAt, isData_noOccurrences hp, hscope,
    isData_noCollectionRest hp, isData_canonical p hp]

theorem kernelJudgmentArity (head : String) (arity : Nat)
    (h : (head, arity) ∈ judgmentArities) :
    (kernelDefinition.lookupJudgment? head arity).isSome = true := by
  have hall : judgmentArities.all (fun entry =>
      (kernelDefinition.lookupJudgment? entry.1 entry.2).isSome) = true := by decide +kernel
  exact (List.all_eq_true.mp hall) (head, arity) h

theorem kernelJudgment_valid (head : String) (args : List Pattern)
    (hhead : (head, args.length) ∈ judgmentArities)
    (hargs : ∀ p ∈ args, KernelDataValid p) :
    kernelDefinition.judgmentSchemaValid (.apply head args) = true := by
  simp only [CalculusLanguageDef.judgmentSchemaValid]
  exact Bool.and_eq_true_iff.mpr
    ⟨kernelJudgmentArity head args.length hhead, kernelDataList_valid args hargs⟩

theorem kernelDefinitionWith_judgmentSchemaValid (admitted : List FORule) (p : Pattern) :
    (kernelDefinitionWith admitted).judgmentSchemaValid p =
      kernelDefinition.judgmentSchemaValid p := rfl

theorem kernelDefinitionWith_ruleIsValidIn (admitted : List FORule) (r : RuleSchema) :
    RuleSchema.isValidIn (kernelDefinitionWith admitted) r =
      RuleSchema.isValidIn kernelDefinition r := rfl

theorem closedRule_validIn (id : String) (hid : id ≠ "") {p : Pattern}
    (hp : IsData p) (hshape : kernelDefinition.judgmentSchemaValid p = true) :
    RuleSchema.isValidIn kernelDefinition (mkRule id [] [] p).toSchema = true := by
  simp only [RuleSchema.isValidIn, closedRule_locallyValid id hid hp, Bool.true_and]
  simpa [FORule.toSchema, FORule.formals, mkRule, RuleSchema.patterns] using hshape

theorem theoryRule_validIn (T : Theory) (allocated : Nat) {r : FORule}
    (hr : r ∈ theoryRules T allocated) :
    RuleSchema.isValidIn kernelDefinition r.toSchema = true := by
  simp only [theoryRules, List.mem_append] at hr
  rcases hr with (hr | hr) | hr
  · obtain ⟨n, _, rfl⟩ := List.mem_map.mp hr
    apply closedRule_validIn _ (by simp [symbolRuleId])
      (IsData.app1 _ (isData_encSym T.sig _))
    exact kernelJudgment_valid _ [_]
      (by change ("VSymDecl", 1) ∈ judgmentArities; decide) (by simp [kernelData_encSym])
  · obtain ⟨k, φ, _, rfl⟩ := mem_axiomRules hr
    apply closedRule_validIn _ (by simp [axiomRuleId])
      (IsData.app1 _ (isData_encTerm T.sig _))
    exact kernelJudgment_valid _ [_]
      (by change ("VThm", 1) ∈ judgmentArities; decide) (by simp [kernelData_encTerm])
  · obtain ⟨k, d, _, rfl⟩ := mem_theoryDefinitionRules hr
    apply closedRule_validIn _ (by simp [definitionRuleId])
      (IsData.app1 _ (isData_encTerm T.sig _))
    exact kernelJudgment_valid _ [_]
      (by change ("VThm", 1) ∈ judgmentArities; decide) (by simp [kernelData_encTerm])

/-! ## Identifier namespaces and allocation order -/

theorem prefixedString_injective (stem : String) : Function.Injective (stem ++ ·) := by
  intro a b h
  apply String.toList_injective
  apply List.append_cancel_left (as := stem.toList)
  simpa using congrArg String.toList h

theorem symbolRuleId_injective : Function.Injective symbolRuleId := by
  intro a b h
  exact Nat.repr_injective (prefixedString_injective _ h)

theorem axiomRuleId_injective : Function.Injective axiomRuleId := by
  intro a b h
  exact Nat.repr_injective (prefixedString_injective _ h)

theorem definitionRuleId_injective : Function.Injective definitionRuleId := by
  intro a b h
  exact Nat.repr_injective (prefixedString_injective _ h)

theorem freshSymbolRuleId_injective :
    Function.Injective (fun n => symbolRuleId (symNumber (.fresh n))) := by
  intro a b h
  have hn := symbolRuleId_injective h
  simp only [symNumber] at hn
  omega

theorem prefixedStrings_ne (first second : String) (width : Nat)
    (hfirst : width ≤ first.toList.length) (hsecond : width ≤ second.toList.length)
    (hne : first.toList.take width ≠ second.toList.take width)
    (a b : String) : first ++ a ≠ second ++ b := by
  intro h
  have ht := congrArg (fun s : String => s.toList.take width) h
  simp only [String.toList_append, List.take_append_of_le_length hfirst,
    List.take_append_of_le_length hsecond] at ht
  exact hne ht

theorem symbolRuleId_ne_axiomRuleId (i j : Nat) : symbolRuleId i ≠ axiomRuleId j :=
  prefixedStrings_ne _ _ 6 (by decide) (by decide) (by decide) _ _

theorem symbolRuleId_ne_definitionRuleId (i j : Nat) :
    symbolRuleId i ≠ definitionRuleId j :=
  prefixedStrings_ne _ _ 6 (by decide) (by decide) (by decide) _ _

theorem axiomRuleId_ne_definitionRuleId (i j : Nat) : axiomRuleId i ≠ definitionRuleId j :=
  prefixedStrings_ne _ _ 6 (by decide) (by decide) (by decide) _ _

theorem axiomRules_ids (sig : Sig) (k : Nat) (φs : List Term) :
    (axiomRules sig k φs).map FORule.id = (List.range' k φs.length).map axiomRuleId := by
  induction φs generalizing k with
  | nil => rfl
  | cons φ φs ih => simp [axiomRules, axiomRule, mkRule, List.range'_succ, ih]

theorem theoryDefinitionRules_ids (sig : Sig) (k : Nat) (ds : List Definition) :
    (theoryDefinitionRules sig k ds).map FORule.id =
      (List.range' k ds.length).map definitionRuleId := by
  induction ds generalizing k with
  | nil => rfl
  | cons d ds ih => simp [theoryDefinitionRules, definitionRule, mkRule, List.range'_succ, ih]

theorem theoryRules_ids (T : Theory) (allocated : Nat) :
    (theoryRules T allocated).map FORule.id =
      (List.range allocated).map (fun n => symbolRuleId (symNumber (.fresh n))) ++
      (List.range' 1 T.axioms.length).map axiomRuleId ++
      (List.range' 1 T.definitions.length).map definitionRuleId := by
  simp only [theoryRules, List.map_append, List.map_map, axiomRules_ids,
    theoryDefinitionRules_ids]
  rfl

theorem theoryRules_ids_nodup (T : Theory) (allocated : Nat) :
    ((theoryRules T allocated).map FORule.id).Nodup := by
  rw [theoryRules_ids]
  apply List.nodup_append.mpr
  refine ⟨List.nodup_append.mpr ⟨List.nodup_range.map freshSymbolRuleId_injective,
    (List.nodup_range').map axiomRuleId_injective, ?_⟩,
    (List.nodup_range').map definitionRuleId_injective, ?_⟩
  · intro i hi j hj
    obtain ⟨n, _, rfl⟩ := List.mem_map.mp hi
    obtain ⟨k, _, rfl⟩ := List.mem_map.mp hj
    exact symbolRuleId_ne_axiomRuleId _ _
  · intro i hi j hj
    obtain ⟨k, _, rfl⟩ := List.mem_map.mp hj
    rcases List.mem_append.mp hi with hi | hi
    · obtain ⟨n, _, rfl⟩ := List.mem_map.mp hi
      exact symbolRuleId_ne_definitionRuleId _ _
    · obtain ⟨n, _, rfl⟩ := List.mem_map.mp hi
      exact axiomRuleId_ne_definitionRuleId _ _

theorem kernelRule_id_ne_prefixed (stem : String)
    (hcheck : kernelRules.all (fun r =>
      decide (r.id.toList.take stem.toList.length ≠ stem.toList)) = true)
    {r : FORule} (hr : r ∈ kernelRules) (suffix : String) : r.id ≠ stem ++ suffix := by
  intro h
  have ht := congrArg (fun s : String => s.toList.take stem.toList.length) h
  simp only [String.toList_append, List.take_left] at ht
  exact of_decide_eq_true ((List.all_eq_true.mp hcheck) r hr) ht

set_option maxRecDepth 100000 in
theorem kernelRule_id_ne_symbolRuleId {r : FORule} (hr : r ∈ kernelRules) (n : Nat) :
    r.id ≠ symbolRuleId n :=
  kernelRule_id_ne_prefixed "vibe-symbol-" (by decide +kernel) hr _

set_option maxRecDepth 100000 in
theorem kernelRule_id_ne_axiomRuleId {r : FORule} (hr : r ∈ kernelRules) (n : Nat) :
    r.id ≠ axiomRuleId n :=
  kernelRule_id_ne_prefixed "vibe-axiom-" (by decide +kernel) hr _

set_option maxRecDepth 100000 in
theorem kernelRule_id_ne_definitionRuleId {r : FORule} (hr : r ∈ kernelRules) (n : Nat) :
    r.id ≠ definitionRuleId n :=
  kernelRule_id_ne_prefixed "vibe-definition-" (by decide +kernel) hr _

set_option maxRecDepth 100000 in
theorem kernelRules_ids_nodup : (kernelRules.map FORule.id).Nodup := by decide +kernel

theorem kernelAndTheoryRules_ids_nodup (T : Theory) (allocated : Nat) :
    ((kernelRules ++ theoryRules T allocated).map FORule.id).Nodup := by
  rw [List.map_append]
  apply List.nodup_append.mpr
  refine ⟨kernelRules_ids_nodup, theoryRules_ids_nodup T allocated, ?_⟩
  intro id hid other hother
  obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hid
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hother
  simp only [theoryRules, List.mem_append] at hs
  rcases hs with (hs | hs) | hs
  · obtain ⟨n, _, rfl⟩ := List.mem_map.mp hs
    exact kernelRule_id_ne_symbolRuleId hr _
  · obtain ⟨k, φ, _, rfl⟩ := mem_axiomRules hs
    exact kernelRule_id_ne_axiomRuleId hr _
  · obtain ⟨k, d, _, rfl⟩ := mem_theoryDefinitionRules hs
    exact kernelRule_id_ne_definitionRuleId hr _

/-! ## The actual validated definitions -/

theorem kernelDefinitionWith_rules (admitted : List FORule) :
    (kernelDefinitionWith admitted).rules =
      (kernelRules ++ admitted).map FORule.toSchema := rfl

theorem kernelDefinitionWith_ruleIds (admitted : List FORule) :
    (kernelDefinitionWith admitted).ruleIds =
      ((kernelRules ++ admitted).map FORule.id).map (fun id => (⟨id⟩ : RuleId)) := by
  simp [CalculusLanguageDef.ruleIds, kernelDefinitionWith_rules, List.map_map,
    Function.comp_def, FORule.toSchema]

theorem theoryRule_locallyValid (T : Theory) (allocated : Nat) {r : FORule}
    (hr : r ∈ theoryRules T allocated) : RuleSchema.isLocallyValid r.toSchema = true := by
  have h := theoryRule_validIn T allocated hr
  simp only [RuleSchema.isValidIn, Bool.and_eq_true] at h
  exact h.1

theorem kernelDefinitionWith_theoryRules_valid (T : Theory) (allocated : Nat) :
    (kernelDefinitionWith (theoryRules T allocated)).isValid = true := by
  have fixed := kernelDefinition_valid
  simp only [CalculusLanguageDef.isValid, CalculusLanguageDef.hasValidLocalRules,
    Bool.and_eq_true] at fixed
  obtain ⟨⟨⟨⟨⟨hlang, hlocal⟩, _⟩, hsignature⟩, hrules⟩, hconversion⟩ := fixed
  have ids : (kernelDefinitionWith (theoryRules T allocated)).ruleIds.Nodup := by
    rw [kernelDefinitionWith_ruleIds]
    apply (kernelAndTheoryRules_ids_nodup T allocated).map
    intro a b h
    exact RuleId.mk.inj h
  have localAdmitted : (theoryRules T allocated).all
      (fun r => RuleSchema.isLocallyValid r.toSchema) = true :=
    List.all_eq_true.mpr (fun r hr => theoryRule_locallyValid T allocated hr)
  have validAdmitted : (theoryRules T allocated).all
      (fun r => RuleSchema.isValidIn kernelDefinition r.toSchema) = true :=
    List.all_eq_true.mpr (fun r hr => theoryRule_validIn T allocated hr)
  simp only [CalculusLanguageDef.isValid, CalculusLanguageDef.hasValidLocalRules,
    Bool.and_eq_true]
  refine ⟨⟨⟨⟨⟨hlang, ?_⟩, ?_⟩, hsignature⟩, ?_⟩, hconversion⟩
  · rw [kernelDefinitionWith_rules, List.map_append, List.all_append]
    simp only [List.all_map]
    exact Bool.and_eq_true_iff.mpr ⟨hlocal, localAdmitted⟩
  · exact (Mettapedia.Util.LinearHash.eraseDupsLength_eq_true_iff_nodup _).mpr ids
  · rw [kernelDefinitionWith_rules, List.map_append, List.all_append]
    simp only [List.all_map]
    exact Bool.and_eq_true_iff.mpr ⟨hrules, validAdmitted⟩

def kernelValidated (T : Theory) (allocated : Nat) : ValidatedCalculusLanguageDef :=
  ⟨kernelDefinitionWith (theoryRules T allocated),
    kernelDefinitionWith_theoryRules_valid T allocated⟩

theorem kernelValidated_presents (T : Theory) (allocated : Nat) :
    Presents (kernelValidated T allocated) (kernelRules ++ theoryRules T allocated) :=
  ⟨kernelRules_foPackage.append (theoryRules_foPackage T allocated), rfl⟩

def kernelFixedValidated : ValidatedCalculusLanguageDef :=
  ⟨kernelDefinition, kernelDefinition_valid⟩

theorem kernelFixedValidated_presents : Presents kernelFixedValidated kernelRules := by
  exact ⟨kernelRules_foPackage, by simp [kernelFixedValidated, kernelDefinition,
    kernelDefinitionWith_rules]⟩

theorem kernelValidated_lookup (T : Theory) (allocated : Nat) {r : FORule}
    (hr : r ∈ kernelRules ++ theoryRules T allocated) :
    (kernelValidated T allocated).1.lookupRule? ⟨r.id⟩ = some r.toSchema :=
  (kernelValidated_presents T allocated).lookup hr

namespace AdmissionControls

private def freshInfo (n : Nat) : Option SymInfo :=
  if n = 0 then some (.fvarOf 0)
  else if n = 1 then some { kind := .constant, binders := [] }
  else none

private def controlSig : Sig := sigOf freshInfo
private def atom : Term := .app (.fresh 0) []
private def defn : Definition := ⟨.fresh 1, [], .lit []⟩
private def theory : Theory := ⟨controlSig, [atom], [defn]⟩
private def leaf (id : String) : RawProof := .node ⟨⟨id⟩, []⟩ []

theorem controlTheory_hosted : Hosted theory 2 := by
  constructor
  · intro b; rfl
  · intro n
    by_cases h0 : n = 0
    · subst n; decide +kernel
    by_cases h1 : n = 1
    · subst n; decide +kernel
    simp [theory, controlSig, sigOf, freshInfo, h0, h1]
    omega
  · intro s info hs hk b hb
    cases s with
    | builtin sym =>
        have hi : info = sym.info := by simpa [theory, controlSig, sigOf] using hs.symm
        subst info
        simp [Builtin.info] at hk
    | fresh n =>
        by_cases h0 : n = 0
        · subst n
          simp [theory, controlSig, sigOf, freshInfo, SymInfo.fvarOf] at hs
          subst info
          simp at hb
        by_cases h1 : n = 1
        · subst n
          simp [theory, controlSig, sigOf, freshInfo] at hs
          subst info
          simp at hb
        simp [theory, controlSig, sigOf, freshInfo, h0, h1] at hs
  · intro φ hφ
    have h : φ = atom := by simpa [theory] using hφ
    subst φ
    decide +kernel
  · intro d hd
    have h : d = defn := by simpa [theory] using hd
    subst d
    exact ⟨by decide +kernel, by decide +kernel, [], by decide +kernel⟩

set_option maxRecDepth 100000 in
theorem symbol_leaf_accepts :
    checkRaw (kernelValidated theory 2) (jSymDecl (encSym theory.sig (.fresh 0)))
      (leaf (symbolRuleId 13)) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem axiom_leaf_accepts :
    checkRaw (kernelValidated theory 2) (jThm (encTerm theory.sig atom))
      (leaf (axiomRuleId 1)) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem definition_leaf_accepts :
    checkRaw (kernelValidated theory 2)
      (jThm (encTerm theory.sig (definitionStatement theory.sig defn.symbol defn.fvars defn.value)))
      (leaf (definitionRuleId 1)) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem harmless_duplicate_axiom_accepts :
    checkRaw (kernelValidated { theory with axioms := [atom, atom] } 2)
      (jThm (encTerm theory.sig atom)) (leaf (axiomRuleId 2)) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem wrong_symbol_goal_rejects :
    checkRaw (kernelValidated theory 2) (jSymDecl (encSym theory.sig (.fresh 1)))
      (leaf (symbolRuleId 13)) = false := by decide +kernel

set_option maxRecDepth 100000 in
theorem wrong_axiom_goal_rejects :
    checkRaw (kernelValidated theory 2) (jThm (encTerm theory.sig (.app (.fresh 1) [])))
      (leaf (axiomRuleId 1)) = false := by decide +kernel

set_option maxRecDepth 100000 in
theorem extra_leaf_child_rejects :
    checkRaw (kernelValidated theory 2) (jThm (encTerm theory.sig atom))
      (.node ⟨⟨axiomRuleId 1⟩, []⟩ [leaf (axiomRuleId 1)]) = false := by decide +kernel

set_option maxRecDepth 100000 in
theorem extra_leaf_argument_rejects :
    checkRaw (kernelValidated theory 2) (jThm (encTerm theory.sig atom))
      (.node ⟨⟨axiomRuleId 1⟩, [cN0]⟩ []) = false := by decide +kernel

set_option maxRecDepth 100000 in
theorem duplicate_rule_id_rejects :
    (kernelDefinitionWith [axiomRule controlSig 1 atom, axiomRule controlSig 1 atom]).isValid =
      false := by decide +kernel

set_option maxRecDepth 100000 in
theorem wrong_constructor_arity_rejects :
    (kernelDefinitionWith [mkRule "vibe-control-wrong-arity" [] []
      (jThm (.apply "VSym" []))]).isValid = false := by decide +kernel

end AdmissionControls

end Mettapedia.Languages.VibeITP.Presentation
