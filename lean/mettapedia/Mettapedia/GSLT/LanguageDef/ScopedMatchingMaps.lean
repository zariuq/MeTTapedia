import Mathlib.Data.List.GetD
import Mathlib.Data.List.InsertIdx
import Mettapedia.GSLT.LanguageDef.StructuralRenamingSemantics
import Mettapedia.GSLT.LanguageDef.StructuralPatternScope
import Mettapedia.OSLF.MeTTaIL.ScopedEquationExecution

/-!
# Declared equations along constructor maps

The scoped matcher and instantiator read a constructor only to compare it with
another one.  Everything they check about a captured value, its scope, its
variable spine and its recovery, ignores constructor names.  So a constructor
map carries every declared equation instance to an instance of the mapped
equation (`applyEquationAt_mapEquation`).

The transport goes one way.  A map that identifies two constructors creates
matches the source does not have (`identifying_map_creates_instance`).
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ScopedMatchingMaps

open Mettapedia.OSLF.MeTTaIL
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.RuleBinding
open Mettapedia.OSLF.MeTTaIL.ScopedRuleMatching
open Mettapedia.OSLF.MeTTaIL.ScopedEquationExecution
open Mettapedia.GSLT.LanguageDef

variable (symbols : LanguageDefSymbolMap)

/-! ## Substitution of context variables -/

theorem lift_map (arity : Nat) (assignment : ContextSubstitution.Assignment) :
    ContextSubstitution.lift arity (fun index => mapPattern symbols (assignment index)) =
      fun index => mapPattern symbols (ContextSubstitution.lift arity assignment index) := by
  funext index
  simp only [ContextSubstitution.lift]
  split
  · simp [mapPattern]
  · exact (StructuralRenamingSemantics.mapPattern_liftBVars symbols 0 arity _).symm

theorem mapPattern_substitute (pattern : Pattern) :
    ∀ assignment : ContextSubstitution.Assignment,
      mapPattern symbols (ContextSubstitution.substitute assignment pattern) =
        ContextSubstitution.substitute (fun index => mapPattern symbols (assignment index))
          (mapPattern symbols pattern) := by
  induction pattern using Pattern.inductionOn with
  | hbvar index => intro assignment; simp [ContextSubstitution.substitute, mapPattern]
  | hfvar name => intro assignment; simp [ContextSubstitution.substitute, mapPattern]
  | happly constructor arguments inductionHypothesis =>
      intro assignment
      simp only [ContextSubstitution.substitute, ContextSubstitution.substituteList_eq_map,
        mapPattern, mapPatternList_eq_map, List.map_map, Pattern.apply.injEq, true_and]
      exact List.map_congr_left (fun argument member => inductionHypothesis argument member assignment)
  | hlambda binder body inductionHypothesis =>
      intro assignment
      simp only [ContextSubstitution.substitute, mapPattern, lift_map]
      rw [inductionHypothesis]
  | hmultiLambda arity binders body inductionHypothesis =>
      intro assignment
      simp only [ContextSubstitution.substitute, mapPattern, lift_map]
      rw [inductionHypothesis]
  | hsubst body replacement bodyHypothesis replacementHypothesis =>
      intro assignment
      simp only [ContextSubstitution.substitute, mapPattern, lift_map]
      rw [bodyHypothesis, replacementHypothesis]
  | hcollection collectionType elements rest inductionHypothesis =>
      intro assignment
      simp only [ContextSubstitution.substitute, ContextSubstitution.substituteList_eq_map,
        mapPattern, mapPatternList_eq_map, List.map_map, Pattern.collection.injEq, true_and, and_true]
      exact List.map_congr_left (fun element member => inductionHypothesis element member assignment)

/-- The recovery substitution sends variables to variables. -/
theorem mapPattern_recover (depth dependencies ambient : Nat) (indices : List Nat) (target : Pattern) :
    mapPattern symbols (ContextSubstitution.substitute (recoveryAssignment depth dependencies ambient indices) target) =
      ContextSubstitution.substitute (recoveryAssignment depth dependencies ambient indices)
        (mapPattern symbols target) := by
  rw [mapPattern_substitute]
  congr 1
  funext index
  simp only [recoveryAssignment]
  split_ifs <;> simp [mapPattern]

theorem occurrenceAssignment_map (dependencies depth : Nat) (arguments : List Pattern) :
    occurrenceAssignment dependencies depth (arguments.map (mapPattern symbols)) =
      fun index => mapPattern symbols (occurrenceAssignment dependencies depth arguments index) := by
  funext index
  simp only [occurrenceAssignment]
  split
  · simpa [mapPattern] using List.getD_map (mapPattern symbols) (l := arguments) (n := index) (d := .bvar 0)
  · simp [mapPattern]

/-! ## Captured values -/

/-- A captured value read through the constructor map. -/
def mapValue (value : ContextualValue) : ContextualValue :=
  { dependencies := value.dependencies.map (mapTypeExpr symbols)
    ambient := value.ambient
    body := mapPattern symbols value.body }

/-- An assignment read through the constructor map. -/
def mapAssignment (assignment : Assignment) : Assignment :=
  assignment.map fun entry => (entry.1, mapValue symbols entry.2)

@[simp] theorem mapAssignment_nil : mapAssignment symbols [] = [] := rfl

theorem instantiateValue?_map (value : ContextualValue) (ambient depth : Nat) (arguments : List Pattern) :
    instantiateValue? (mapValue symbols value) ambient depth (arguments.map (mapPattern symbols)) =
      (instantiateValue? value ambient depth arguments).map (mapPattern symbols) := by
  simp only [instantiateValue?, mapValue, List.length_map, isWellScopedAt_mapPattern, List.all_map,
    Function.comp_def, occurrenceAssignment_map, ← mapPattern_substitute]
  split_ifs <;> simp_all

theorem variableSpine?_map (depth : Nat) (arguments : List Pattern) :
    variableSpine? depth (arguments.map (mapPattern symbols)) = variableSpine? depth arguments := by
  unfold variableSpine?
  rw [List.mapM_map]
  congr 2
  funext argument
  cases argument <;> simp [mapPattern]

theorem recoverValue?_map {dependencies : List TypeExpr} {ambient depth : Nat} {arguments : List Pattern}
    {target : Pattern} {value : ContextualValue}
    (recovered : recoverValue? dependencies ambient depth arguments target = some value) :
    recoverValue? (dependencies.map (mapTypeExpr symbols)) ambient depth (arguments.map (mapPattern symbols))
      (mapPattern symbols target) = some (mapValue symbols value) := by
  have forward := recoverValue?_forward dependencies ambient depth arguments target value recovered
  unfold recoverValue? at recovered ⊢
  rw [isWellScopedAt_mapPattern, variableSpine?_map]
  split at recovered
  · cases recovered
  rename_i wellScoped
  rw [if_neg wellScoped]
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at recovered ⊢
  obtain ⟨indices, spine, recovered⟩ := recovered
  refine ⟨indices, spine, ?_⟩
  split at recovered
  · cases recovered
  rename_i lengths
  rw [List.length_map, if_neg lengths]
  split at recovered
  · cases recovered
    have built : mapValue symbols ⟨dependencies, ambient,
        ContextSubstitution.substitute (recoveryAssignment depth dependencies.length ambient indices) target⟩ =
        ⟨dependencies.map (mapTypeExpr symbols), ambient,
          ContextSubstitution.substitute (recoveryAssignment depth dependencies.length ambient indices)
            (mapPattern symbols target)⟩ := by
      simp [mapValue, mapPattern_recover]
    rw [← built, instantiateValue?_map, forward]
    simp
  · cases recovered

/-! ## Assignments -/

theorem lookup_map (assignment : Assignment) (name : String) :
    lookup (mapAssignment symbols assignment) name = (lookup assignment name).map (mapValue symbols) := by
  simp [lookup, mapAssignment, List.find?_map, Function.comp_def, Option.map_map]

theorem assign_map {assignment result : Assignment} {name : String} {value : ContextualValue}
    (assigned : assign assignment name value = some result) :
    assign (mapAssignment symbols assignment) name (mapValue symbols value) =
      some (mapAssignment symbols result) := by
  unfold assign at assigned ⊢
  rw [lookup_map]
  cases stored : lookup assignment name with
  | none =>
      simp only [stored, Option.some.injEq] at assigned
      subst assigned
      simp [mapAssignment]
  | some prior =>
      simp only [stored] at assigned
      by_cases same : prior = value
      · subst same
        simp only [beq_self_eq_true, if_true, Option.some.injEq] at assigned
        subst assigned
        simp
      · simp [same] at assigned

/-! ## Rules read through the map -/

/-- `target` reads every site of `source` through the constructor map. -/
structure RuleMaps (source target : RewriteRule) : Prop where
  sites : ∀ site, sitePattern? target site = (sitePattern? source site).map (mapPattern symbols)
  binderDepths : ∀ site, siteBinderDepth? target site = siteBinderDepth? source site
  names : target.typeContext.map Prod.fst = source.typeContext.map Prod.fst

variable {symbols}

theorem RuleMaps.left {source target : RewriteRule} (maps : RuleMaps symbols source target) :
    target.left = mapPattern symbols source.left := by
  simpa [sitePattern?] using maps.sites .left

theorem RuleMaps.right {source target : RewriteRule} (maps : RuleMaps symbols source target) :
    target.right = mapPattern symbols source.right := by
  simpa [sitePattern?] using maps.sites .right

variable (symbols)

theorem occurrenceAt?_mapPattern (pattern : Pattern) :
    ∀ path, occurrenceAt? (mapPattern symbols pattern) path = occurrenceAt? pattern path := by
  induction pattern using Pattern.inductionOn with
  | hbvar index => intro path; simp [mapPattern]
  | hfvar name => intro path; simp [mapPattern]
  | happly constructor arguments inductionHypothesis =>
      intro path
      cases path with
      | nil => simp [mapPattern, occurrenceAt?]
      | cons index path =>
          simp only [mapPattern, mapPatternList_eq_map, occurrenceAt?, List.getElem?_map]
          cases found : arguments[index]? with
          | none => simp
          | some argument => simp [inductionHypothesis argument (List.mem_of_getElem? found) path]
  | hlambda binder body inductionHypothesis =>
      intro path
      rcases path with _ | ⟨_ | index, path⟩ <;> simp [mapPattern, occurrenceAt?, inductionHypothesis]
  | hmultiLambda arity binders body inductionHypothesis =>
      intro path
      rcases path with _ | ⟨_ | index, path⟩ <;> simp [mapPattern, occurrenceAt?, inductionHypothesis]
  | hsubst body replacement bodyHypothesis replacementHypothesis =>
      intro path
      rcases path with _ | ⟨_ | _ | index, path⟩ <;>
        simp [mapPattern, occurrenceAt?, bodyHypothesis, replacementHypothesis]
  | hcollection collectionType elements rest inductionHypothesis =>
      intro path
      cases path with
      | nil => simp [mapPattern, occurrenceAt?]
      | cons index path =>
          simp only [mapPattern, mapPatternList_eq_map, occurrenceAt?, List.getElem?_map, List.length_map]
          cases found : elements[index]? with
          | none => simp
          | some element => simp [inductionHypothesis element (List.mem_of_getElem? found) path]

theorem occurrenceDepthAt?_mapPattern (pattern : Pattern) :
    ∀ path depth, occurrenceDepthAt? (mapPattern symbols pattern) path depth =
      occurrenceDepthAt? pattern path depth := by
  induction pattern using Pattern.inductionOn with
  | hbvar index => intro path depth; simp [mapPattern]
  | hfvar name => intro path depth; simp [mapPattern]
  | happly constructor arguments inductionHypothesis =>
      intro path depth
      cases path with
      | nil => simp [mapPattern, occurrenceDepthAt?]
      | cons index path =>
          simp only [mapPattern, mapPatternList_eq_map, occurrenceDepthAt?, List.getElem?_map]
          cases found : arguments[index]? with
          | none => simp
          | some argument => simp [inductionHypothesis argument (List.mem_of_getElem? found) path]
  | hlambda binder body inductionHypothesis =>
      intro path depth
      rcases path with _ | ⟨_ | index, path⟩ <;> simp [mapPattern, occurrenceDepthAt?, inductionHypothesis]
  | hmultiLambda arity binders body inductionHypothesis =>
      intro path depth
      rcases path with _ | ⟨_ | index, path⟩ <;> simp [mapPattern, occurrenceDepthAt?, inductionHypothesis]
  | hsubst body replacement bodyHypothesis replacementHypothesis =>
      intro path depth
      rcases path with _ | ⟨_ | _ | index, path⟩ <;>
        simp [mapPattern, occurrenceDepthAt?, bodyHypothesis, replacementHypothesis]
  | hcollection collectionType elements rest inductionHypothesis =>
      intro path depth
      cases path with
      | nil => simp [mapPattern, occurrenceDepthAt?]
      | cons index path =>
          simp only [mapPattern, mapPatternList_eq_map, occurrenceDepthAt?, List.getElem?_map, List.length_map]
          cases found : elements[index]? with
          | none => simp
          | some element => simp [inductionHypothesis element (List.mem_of_getElem? found) path]

variable {symbols}

theorem occurrenceDeclared_map {source target : RewriteRule} (maps : RuleMaps symbols source target)
    (row : MetavariableOccurrence) :
    occurrenceDeclared target (mapMetavariableOccurrence symbols row) = occurrenceDeclared source row := by
  simp only [occurrenceDeclared, mapMetavariableOccurrence, maps.sites]
  cases sitePattern? source row.site <;> simp [occurrenceAt?_mapPattern]

/-- Declaring an occurrence reads its name, site and address, not its arguments. -/
theorem occurrenceDeclared_mapOccurrence (rule : RewriteRule) (row : MetavariableOccurrence) :
    occurrenceDeclared rule (mapMetavariableOccurrence symbols row) = occurrenceDeclared rule row := rfl

theorem occurrenceDeclared_rule {source target : RewriteRule} (maps : RuleMaps symbols source target)
    (row : MetavariableOccurrence) :
    occurrenceDeclared target row = occurrenceDeclared source row := by
  simp only [occurrenceDeclared, maps.sites]
  cases sitePattern? source row.site <;> simp [occurrenceAt?_mapPattern]

theorem occurrenceDepthAtSite?_map {source target : RewriteRule} (maps : RuleMaps symbols source target)
    (site : RulePatternSite) (path : List Nat) :
    occurrenceDepthAtSite? target site path = occurrenceDepthAtSite? source site path := by
  simp only [occurrenceDepthAtSite?, maps.sites, maps.binderDepths]
  cases sitePattern? source site <;> simp [occurrenceDepthAt?_mapPattern]

variable (symbols)

theorem dependencies?_map (spec : RuleBindingSpec) (name : String) :
    dependencies? (mapRuleBindingSpec symbols spec) name =
      (dependencies? spec name).map (List.map (mapTypeExpr symbols)) := by
  simp only [dependencies?, mapRuleBindingSpec, List.filter_map, Function.comp_def]
  generalize spec.dependencies.filter (fun entry => entry.1 == name) = rows
  rcases rows with _ | ⟨⟨_, _⟩, _ | ⟨_, _⟩⟩ <;> simp

variable {symbols}

theorem arguments?_map {source target : RewriteRule} (maps : RuleMaps symbols source target)
    (spec : RuleBindingSpec) (name : String) (site : RulePatternSite) (path : List Nat) :
    arguments? target (mapRuleBindingSpec symbols spec) name site path =
      (arguments? source spec name site path).map (List.map (mapPattern symbols)) := by
  unfold arguments?
  rw [dependencies?_map]
  cases dependencies? spec name with
  | none => rfl
  | some dependencies =>
      simp only [Option.map_some, Option.bind_eq_bind, Option.bind_some, occurrenceDeclared_rule maps]
      by_cases declared : occurrenceDeclared source { name, site, path, arguments := [] } = true
      · simp only [declared, guard, if_true, Option.pure_def, Option.bind_some]
        have rows : (mapRuleBindingSpec symbols spec).occurrences.filter
            (fun row => row.name == name && row.site == site && row.path == path) =
            (spec.occurrences.filter
              (fun row => row.name == name && row.site == site && row.path == path)).map
                (mapMetavariableOccurrence symbols) := by
          simp [mapRuleBindingSpec, List.filter_map, Function.comp_def, mapMetavariableOccurrence]
        rw [rows]
        generalize spec.occurrences.filter
          (fun row => row.name == name && row.site == site && row.path == path) = found
        rcases found with _ | ⟨row, _ | ⟨_, _⟩⟩
        · simp
        · simp only [List.map_cons, List.map_nil, occurrenceDeclared_mapOccurrence]
          have kept : (mapMetavariableOccurrence symbols row).arguments = row.arguments.map (mapPattern symbols) := rfl
          rw [kept, List.length_map, List.length_map]
          split_ifs <;> simp_all
        · simp
      · simp [declared]

variable (symbols)

theorem capture?_map {source target : RewriteRule} (maps : RuleMaps symbols source target)
    {spec : RuleBindingSpec} {ambient depth : Nat} {site : RulePatternSite} {path : List Nat}
    {assignment result : Assignment} {name : String} {term : Pattern}
    (captured : capture? source spec ambient depth site path assignment name term = some result) :
    capture? target (mapRuleBindingSpec symbols spec) ambient depth site path
      (mapAssignment symbols assignment) name (mapPattern symbols term) =
        some (mapAssignment symbols result) := by
  unfold capture? at captured ⊢
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at captured
  obtain ⟨dependencies, declared, arguments, supplied, value, recovered, assigned⟩ := captured
  simp only [dependencies?_map, declared, arguments?_map maps, supplied, Option.map_some,
    Option.bind_eq_bind, Option.bind_some, recoverValue?_map symbols recovered]
  exact assign_map symbols assigned

/-! ## Matching -/

theorem matchArgs_map {source target : RewriteRule}
    (spec : RuleBindingSpec) (ambient : Nat) (site : RulePatternSite) (path : List Nat) (depth : Nat)
    (patterns : List Pattern)
    (elementwise : ∀ pattern ∈ patterns, ∀ (path : List Nat) (depth : Nat) (assignment : Assignment)
      (term : Pattern) (found : Assignment),
      found ∈ matchAtWith literalBodyComparison source spec ambient site path depth assignment pattern term →
        mapAssignment symbols found ∈ matchAtWith literalBodyComparison target
          (mapRuleBindingSpec symbols spec) ambient site path depth (mapAssignment symbols assignment)
          (mapPattern symbols pattern) (mapPattern symbols term)) :
    ∀ (index : Nat) (assignment : Assignment) (terms : List Pattern) (found : Assignment),
      found ∈ matchArgsAtWith literalBodyComparison source spec ambient site path depth assignment index
          patterns terms →
        mapAssignment symbols found ∈ matchArgsAtWith literalBodyComparison target
          (mapRuleBindingSpec symbols spec) ambient site path depth (mapAssignment symbols assignment) index
          (patterns.map (mapPattern symbols)) (terms.map (mapPattern symbols)) := by
  induction patterns with
  | nil =>
      intro index assignment terms found matched
      cases terms with
      | nil => simp only [matchArgsAtWith, List.map_nil, List.mem_singleton] at matched ⊢; rw [matched]
      | cons _ _ => simp [matchArgsAtWith] at matched
  | cons pattern patterns tailHypothesis =>
      intro index assignment terms found matched
      cases terms with
      | nil => simp [matchArgsAtWith] at matched
      | cons term terms =>
          simp only [matchArgsAtWith, List.mem_flatMap, List.map_cons] at matched ⊢
          obtain ⟨middle, first, rest⟩ := matched
          exact ⟨mapAssignment symbols middle,
            elementwise pattern (by simp) _ _ _ _ _ first,
            tailHypothesis (fun item member => elementwise item (by simp [member])) _ _ _ _ rest⟩

theorem matchBag_map {source target : RewriteRule} (maps : RuleMaps symbols source target)
    (spec : RuleBindingSpec) (ambient : Nat) (site : RulePatternSite) (path : List Nat) (depth : Nat)
    (patterns : List Pattern)
    (elementwise : ∀ pattern ∈ patterns, ∀ (path : List Nat) (depth : Nat) (assignment : Assignment)
      (term : Pattern) (found : Assignment),
      found ∈ matchAtWith literalBodyComparison source spec ambient site path depth assignment pattern term →
        mapAssignment symbols found ∈ matchAtWith literalBodyComparison target
          (mapRuleBindingSpec symbols spec) ambient site path depth (mapAssignment symbols assignment)
          (mapPattern symbols pattern) (mapPattern symbols term)) :
    ∀ (index : Nat) (assignment : Assignment) (rest : Option String) (kind : CollType)
      (terms : List Pattern) (found : Assignment),
      found ∈ matchBagAtWith literalBodyComparison source spec ambient site path depth assignment index
          patterns rest kind terms →
        mapAssignment symbols found ∈ matchBagAtWith literalBodyComparison target
          (mapRuleBindingSpec symbols spec) ambient site path depth (mapAssignment symbols assignment) index
          (patterns.map (mapPattern symbols)) rest kind (terms.map (mapPattern symbols)) := by
  induction patterns with
  | nil =>
      intro index assignment rest kind terms found matched
      cases rest with
      | none =>
          simp only [matchBagAtWith, List.map_nil, List.isEmpty_map] at matched ⊢
          split at matched
          · rename_i empty
            simp only [empty, if_true, List.mem_singleton] at matched ⊢
            rw [matched]
          · cases matched
      | some name =>
          simp only [matchBagAtWith, List.map_nil, captureRestWith?_literal, captureRest?, Option.mem_toList] at matched ⊢
          have mapped := capture?_map symbols maps matched
          simpa [mapPattern, mapPatternList_eq_map] using mapped
  | cons pattern patterns tailHypothesis =>
      intro index assignment rest kind terms found matched
      simp only [matchBagAtWith, List.map_cons, List.mem_flatMap] at matched ⊢
      obtain ⟨⟨term, selected⟩, chosen, middle, first, remaining⟩ := matched
      refine ⟨(mapPattern symbols term, selected), ?_, mapAssignment symbols middle,
        elementwise pattern (by simp) _ _ _ _ _ first, ?_⟩
      · rw [List.zipIdx_map]
        exact List.mem_map.mpr ⟨(term, selected), chosen, rfl⟩
      · rw [List.eraseIdx_map]
        exact tailHypothesis (fun item member => elementwise item (by simp [member])) _ _ _ _ _ _ remaining

theorem matchAt_map {source target : RewriteRule} (maps : RuleMaps symbols source target)
    (spec : RuleBindingSpec) (ambient : Nat) (site : RulePatternSite) (pattern : Pattern) :
    ∀ (path : List Nat) (depth : Nat) (assignment : Assignment) (term : Pattern) (found : Assignment),
      found ∈ matchAtWith literalBodyComparison source spec ambient site path depth assignment pattern term →
        mapAssignment symbols found ∈ matchAtWith literalBodyComparison target
          (mapRuleBindingSpec symbols spec) ambient site path depth (mapAssignment symbols assignment)
          (mapPattern symbols pattern) (mapPattern symbols term) := by
  induction pattern using Pattern.inductionOn with
  | hbvar expected =>
      intro path depth assignment term found matched
      cases term <;> simp [matchAtWith, mapPattern] at matched ⊢
      obtain ⟨same, rfl⟩ := matched
      exact ⟨same, rfl⟩
  | hfvar name =>
      intro path depth assignment term found matched
      simp only [matchAtWith, captureWith?_literal, Option.mem_toList, mapPattern] at matched ⊢
      exact capture?_map symbols maps matched
  | happly constructor patterns inductionHypothesis =>
      intro path depth assignment term found matched
      cases term with
      | apply actual terms =>
          simp only [matchAtWith, mapPattern, mapPatternList_eq_map] at matched ⊢
          split at matched
          · rename_i same
            simp only [beq_iff_eq] at same
            subst same
            simp only [beq_self_eq_true, if_true]
            exact matchArgs_map symbols spec ambient site path depth patterns inductionHypothesis
              0 assignment terms found matched
          · cases matched
      | _ => simp [matchAtWith] at matched
  | hlambda binder body inductionHypothesis =>
      intro path depth assignment term found matched
      cases term with
      | lambda _ inner =>
          simp only [matchAtWith, mapPattern] at matched ⊢
          exact inductionHypothesis _ _ _ _ _ matched
      | _ => simp [matchAtWith] at matched
  | hmultiLambda arity binders body inductionHypothesis =>
      intro path depth assignment term found matched
      cases term with
      | multiLambda actual _ inner =>
          simp only [matchAtWith, mapPattern] at matched ⊢
          split at matched
          · rename_i same
            simp only [same, if_true]
            exact inductionHypothesis _ _ _ _ _ matched
          · cases matched
      | _ => simp [matchAtWith] at matched
  | hsubst body replacement bodyHypothesis replacementHypothesis =>
      intro path depth assignment term found matched
      cases term with
      | subst termBody termReplacement =>
          simp only [matchAtWith, mapPattern, List.mem_flatMap] at matched ⊢
          obtain ⟨middle, first, second⟩ := matched
          exact ⟨mapAssignment symbols middle, bodyHypothesis _ _ _ _ _ first,
            replacementHypothesis _ _ _ _ _ second⟩
      | _ => simp [matchAtWith] at matched
  | hcollection kind patterns rest inductionHypothesis =>
      intro path depth assignment term found matched
      cases term with
      | collection actualKind terms actualRest =>
          simp only [mapPattern, mapPatternList_eq_map]
          unfold matchAtWith at matched ⊢
          split at matched
          · rename_i admitted
            simp only [admitted, if_true]
            split at matched
            · rename_i isVector
              simp only [isVector, if_true]
              cases rest with
              | none =>
                  exact matchArgs_map symbols spec ambient site path depth patterns inductionHypothesis
                    0 assignment terms found matched
              | some name =>
                  simp only [List.mem_filterMap] at matched ⊢
                  obtain ⟨middle, first, captured⟩ := matched
                  refine ⟨mapAssignment symbols middle, ?_, ?_⟩
                  · rw [List.length_map, ← List.map_take]
                    exact matchArgs_map symbols spec ambient site path depth patterns inductionHypothesis
                      0 assignment _ middle first
                  · simp only [captureRestWith?_literal, captureRest?] at captured ⊢
                    rw [List.length_map, ← List.map_drop]
                    have mapped := capture?_map symbols maps captured
                    simpa [mapPattern, mapPatternList_eq_map] using mapped
            · rename_i notVector
              simp only [notVector]
              exact matchBag_map symbols maps spec ambient site path depth patterns inductionHypothesis
                0 assignment rest kind terms found matched
          · cases matched
      | _ => simp [matchAtWith] at matched

/-! ## Instantiation -/

theorem instantiateArgs_map {source target : RewriteRule}
    (spec : RuleBindingSpec) (ambient : Nat) (site : RulePatternSite) (path : List Nat) (depth : Nat)
    (assignment : Assignment) (patterns : List Pattern)
    (elementwise : ∀ pattern ∈ patterns, ∀ (path : List Nat) (result : Pattern),
      instantiateWith? Substitution.instantiateBVar source spec ambient site path depth assignment pattern =
          some result →
        instantiateWith? Substitution.instantiateBVar target (mapRuleBindingSpec symbols spec) ambient site
          path depth (mapAssignment symbols assignment) (mapPattern symbols pattern) =
            some (mapPattern symbols result)) :
    ∀ (index : Nat) (results : List Pattern),
      instantiateArgsWith? Substitution.instantiateBVar source spec ambient site path depth assignment index
          patterns = some results →
        instantiateArgsWith? Substitution.instantiateBVar target (mapRuleBindingSpec symbols spec) ambient
          site path depth (mapAssignment symbols assignment) index (patterns.map (mapPattern symbols)) =
            some (results.map (mapPattern symbols)) := by
  induction patterns with
  | nil =>
      intro index results built
      simp only [instantiateArgsWith?, Option.some.injEq] at built
      subst built
      simp [instantiateArgsWith?]
  | cons pattern patterns tailHypothesis =>
      intro index results built
      simp only [instantiateArgsWith?, Option.bind_eq_bind, Option.bind_eq_some_iff] at built
      obtain ⟨head, first, tail, rest, built⟩ := built
      simp only [Option.some.injEq] at built
      subst built
      simp only [List.map_cons, instantiateArgsWith?, Option.bind_eq_bind,
        elementwise pattern (by simp) _ _ first, Option.bind_some,
        tailHypothesis (fun item member => elementwise item (by simp [member])) _ _ rest]

theorem instantiate_map {source target : RewriteRule} (maps : RuleMaps symbols source target)
    (spec : RuleBindingSpec) (ambient : Nat) (site : RulePatternSite) (pattern : Pattern) :
    ∀ (path : List Nat) (depth : Nat) (assignment : Assignment) (result : Pattern),
      instantiateWith? Substitution.instantiateBVar source spec ambient site path depth assignment pattern =
          some result →
        instantiateWith? Substitution.instantiateBVar target (mapRuleBindingSpec symbols spec) ambient site
          path depth (mapAssignment symbols assignment) (mapPattern symbols pattern) =
            some (mapPattern symbols result) := by
  induction pattern using Pattern.inductionOn with
  | hbvar index =>
      intro path depth assignment result built
      simp only [instantiateWith?, Option.some.injEq] at built
      subst built
      simp [instantiateWith?, mapPattern]
  | hfvar name =>
      intro path depth assignment result built
      simp only [instantiateWith?, Option.bind_eq_bind, Option.bind_eq_some_iff] at built
      obtain ⟨value, stored, arguments, supplied, instantiated⟩ := built
      simp only [mapPattern, instantiateWith?, Option.bind_eq_bind, lookup_map, stored, Option.map_some,
        Option.bind_some, arguments?_map maps, supplied, instantiateValue?_map, instantiated]
  | happly constructor patterns inductionHypothesis =>
      intro path depth assignment result built
      simp only [instantiateWith?, Option.bind_eq_bind, Option.bind_eq_some_iff] at built
      obtain ⟨results, row, built⟩ := built
      simp only [Option.some.injEq] at built
      subst built
      simp only [mapPattern, mapPatternList_eq_map, instantiateWith?, Option.bind_eq_bind,
        instantiateArgs_map symbols spec ambient site path depth assignment patterns
          (fun item member path' => inductionHypothesis item member path' depth assignment) 0 results row,
        Option.bind_some]
  | hlambda binder body inductionHypothesis =>
      intro path depth assignment result built
      simp only [instantiateWith?, Option.bind_eq_bind, Option.bind_eq_some_iff] at built
      obtain ⟨inner, first, built⟩ := built
      simp only [Option.some.injEq] at built
      subst built
      simp only [mapPattern, instantiateWith?, Option.bind_eq_bind, inductionHypothesis _ _ _ _ first,
        Option.bind_some]
  | hmultiLambda arity binders body inductionHypothesis =>
      intro path depth assignment result built
      simp only [instantiateWith?, Option.bind_eq_bind, Option.bind_eq_some_iff] at built
      obtain ⟨inner, first, built⟩ := built
      simp only [Option.some.injEq] at built
      subst built
      simp only [mapPattern, instantiateWith?, Option.bind_eq_bind, inductionHypothesis _ _ _ _ first,
        Option.bind_some]
  | hsubst body replacement bodyHypothesis replacementHypothesis =>
      intro path depth assignment result built
      simp only [instantiateWith?, Option.bind_eq_bind, Option.bind_eq_some_iff] at built
      obtain ⟨body', first, replacement', second, built⟩ := built
      simp only [Option.some.injEq] at built
      subst built
      simp only [mapPattern, instantiateWith?, Option.bind_eq_bind, bodyHypothesis _ _ _ _ first,
        replacementHypothesis _ _ _ _ second, Option.bind_some,
        StructuralRenamingSemantics.mapPattern_instantiateBVar]
  | hcollection kind patterns rest inductionHypothesis =>
      intro path depth assignment result built
      simp only [instantiateWith?, Option.bind_eq_bind, Option.bind_eq_some_iff] at built
      obtain ⟨explicit, row, built⟩ := built
      have mappedRow := instantiateArgs_map symbols spec ambient site path depth assignment patterns
        (fun item member path' => inductionHypothesis item member path' depth assignment) 0 explicit row
      simp only [mapPattern, mapPatternList_eq_map, instantiateWith?, Option.bind_eq_bind, mappedRow,
        Option.bind_some, List.length_map]
      cases rest with
      | none =>
          simp only [Option.some.injEq] at built
          subst built
          simp [mapPattern, mapPatternList_eq_map]
      | some name =>
          simp only [Option.bind_eq_some_iff] at built
          obtain ⟨value, stored, arguments, supplied, residual, instantiated, built⟩ := built
          simp only [lookup_map, stored, Option.map_some, Option.bind_some, arguments?_map maps, supplied,
            instantiateValue?_map, instantiated]
          cases residual with
          | collection actualKind elements residualRest =>
              cases residualRest with
              | none =>
                  simp only at built
                  split_ifs at built with same
                  simp only [Option.some.injEq] at built
                  subst built
                  simp [same, mapPattern, mapPatternList_eq_map]
              | some _ => simp at built
          | _ => simp at built

/-! ## Declared equations -/

theorem quantifiedBody?_mapPremise : ∀ (count : Nat) (premise : Premise),
    quantifiedBody? count (mapPremise symbols premise) = (quantifiedBody? count premise).map (mapPremise symbols)
  | 0, _ => rfl
  | count + 1, premise => by
      cases premise with
      | forAll collection parameter body =>
          simpa [quantifiedBody?, mapPremise] using quantifiedBody?_mapPremise count body
      | _ => rfl

theorem orientedRule_premises_map (equation : Equation) (orientation : Orientation) :
    (orientedRule (mapEquation symbols equation) orientation).premises =
      (orientedRule equation orientation).premises.map (mapPremise symbols) := by
  cases orientation <;> rfl

theorem orientedRule_maps (equation : Equation) (orientation : Orientation) :
    RuleMaps symbols (orientedRule equation orientation) (orientedRule (mapEquation symbols equation) orientation) where
  sites site := by
    cases site with
    | left => cases orientation <;> rfl
    | right => cases orientation <;> rfl
    | premise index quantifiers argument =>
        simp only [sitePattern?, orientedRule_premises_map, List.getElem?_map]
        cases (orientedRule equation orientation).premises[index]? with
        | none => rfl
        | some premise =>
            simp only [Option.map_some, Option.bind_eq_bind, Option.bind_some, quantifiedBody?_mapPremise]
            cases quantifiedBody? quantifiers premise with
            | none => rfl
            | some body =>
                cases body <;> simp only [Option.map_some, Option.bind_some, mapPremise] <;>
                  (try split_ifs) <;> simp [List.getElem?_map]
  binderDepths site := by
    cases site with
    | left => cases orientation <;> rfl
    | right => cases orientation <;> rfl
    | premise index quantifiers argument =>
        simp only [siteBinderDepth?, orientedRule_premises_map, List.getElem?_map]
        cases (orientedRule equation orientation).premises[index]? with
        | none => rfl
        | some premise =>
            simp only [Option.map_some, Option.bind_eq_bind, Option.bind_some, quantifiedBody?_mapPremise]
            cases quantifiedBody? quantifiers premise with
            | none => rfl
            | some body => cases body <;> simp [mapPremise]
  names := by
    cases orientation <;> simp [orientedRule, mapEquation, mapTypeContext, Function.comp_def]

theorem orientedRule_bindings_map (equation : Equation) (orientation : Orientation) :
    (orientedRule (mapEquation symbols equation) orientation).bindings =
      (orientedRule equation orientation).bindings.map (mapRuleBindingSpec symbols) := by
  cases orientation
  · rfl
  · show (equation.bindings.map (mapRuleBindingSpec symbols)).map exchangeBindings =
        (equation.bindings.map exchangeBindings).map (mapRuleBindingSpec symbols)
    rw [Option.map_map, Option.map_map]
    congr 1
    funext spec
    simp [exchangeBindings, mapRuleBindingSpec, exchangeOccurrence, mapMetavariableOccurrence, Function.comp_def]

theorem admittedFor_map {source target : RewriteRule} (maps : RuleMaps symbols source target)
    (spec : RuleBindingSpec) (admitted : admittedFor source spec = true) :
    admittedFor target (mapRuleBindingSpec symbols spec) = true := by
  have lengths : target.typeContext.length = source.typeContext.length := by
    simpa using congrArg List.length maps.names
  have covered : ∀ entry ∈ target.typeContext, ∃ original ∈ source.typeContext, original.1 = entry.1 := by
    intro entry member
    have named : entry.1 ∈ source.typeContext.map Prod.fst := by
      rw [← maps.names]
      exact List.mem_map_of_mem member
    simpa using named
  simp only [admittedFor, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.any_eq_true,
    beq_iff_eq] at admitted ⊢
  obtain ⟨⟨⟨⟨⟨names, dependencyNames⟩, rows⟩, count⟩, contexts⟩, occurrences⟩ := admitted
  refine ⟨⟨⟨⟨⟨by rw [maps.names]; exact names, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · simpa [mapRuleBindingSpec, Function.comp_def] using dependencyNames
  · simpa [mapRuleBindingSpec, Function.comp_def, mapMetavariableOccurrence] using rows
  · simpa [mapRuleBindingSpec, lengths] using count
  · intro entry member
    obtain ⟨original, originalMember, same⟩ := covered entry member
    obtain ⟨declared, declaredMember, declaredName⟩ := contexts original originalMember
    exact ⟨(declared.1, declared.2.map (mapTypeExpr symbols)),
      by simp only [mapRuleBindingSpec]; exact List.mem_map.mpr ⟨declared, declaredMember, rfl⟩,
      by simp [declaredName, same]⟩
  · intro row member
    simp only [mapRuleBindingSpec, List.mem_map] at member
    obtain ⟨original, originalMember, rfl⟩ := member
    obtain ⟨declared, shape⟩ := occurrences original originalMember
    refine ⟨by rw [occurrenceDeclared_map maps]; exact declared, ?_⟩
    have dependencyName : (mapMetavariableOccurrence symbols original).name = original.name := rfl
    have siteName : (mapMetavariableOccurrence symbols original).site = original.site := rfl
    have pathName : (mapMetavariableOccurrence symbols original).path = original.path := rfl
    rw [dependencyName, siteName, pathName, occurrenceDepthAtSite?_map maps, dependencies?_map]
    revert shape
    cases dependencies? spec original.name <;> cases occurrenceDepthAtSite? source original.site original.path
    all_goals simp [mapMetavariableOccurrence, isGroundAt_mapPattern]

/-- **A constructor map carries every declared equation instance to an instance of the mapped equation**, in any
language: declared instances read no language rule. -/
theorem applyEquationAt_mapEquation {language language' : LanguageDef} {ambient : Nat} {equation : Equation}
    {orientation : Orientation} {source target : Pattern}
    (firing : target ∈ applyEquationAt language ambient equation orientation source) :
    mapPattern symbols target ∈
      applyEquationAt language' ambient (mapEquation symbols equation) orientation (mapPattern symbols source) := by
  obtain ⟨premiseFree, sourceScoped, targetScoped, spec, captured, declared, admitted, matched, applied⟩ :=
    (mem_applyEquationAt_iff language ambient equation orientation source target).mp firing
  have maps := orientedRule_maps symbols equation orientation
  refine (mem_applyEquationAt_iff language' ambient _ orientation _ _).mpr
    ⟨by simp [mapEquation, premiseFree], by rw [isWellScopedAt_mapPattern]; exact sourceScoped,
      by rw [isWellScopedAt_mapPattern]; exact targetScoped, mapRuleBindingSpec symbols spec,
      mapAssignment symbols captured, by rw [orientedRule_bindings_map, declared]; rfl,
      admittedFor_map symbols maps spec admitted, ?_, ?_⟩
  · simp only [matchRuleAt, matchRuleWithAt, maps.left] at matched ⊢
    exact matchAt_map symbols maps spec ambient .left _ [] 0 [] source captured matched
  · simp only [reduct?, instantiateAt?, maps.right] at applied ⊢
    exact instantiate_map symbols maps spec ambient .right _ [] 0 captured target applied

/-! ## The transport goes one way -/

/-- Sends `B` to `A` and fixes every other constructor. -/
def collapse : LanguageDefSymbolMap :=
  { LanguageDefSymbolMap.id with constructor := fun name => if name == "B" then "A" else name }

/-- `A(P) = P`, declared with no binder dependency. -/
def unwrap : Equation where
  name := "Unwrap"
  typeContext := [("P", .base "Proc")]
  premises := []
  left := .apply "A" [.fvar "P"]
  right := .fvar "P"
  bindings := some { dependencies := [("P", [])], occurrences := [] }

def inert : Pattern := .apply "Z" []

theorem unwrap_instance :
    inert ∈ applyEquationAt (LanguageDef.empty "Unwrap") 0 unwrap .forward (.apply "A" [inert]) := by
  decide +kernel

theorem unmapped_no_instance :
    applyEquationAt (LanguageDef.empty "Unwrap") 0 unwrap .forward (.apply "B" [inert]) = [] := by
  decide +kernel

/-- **A map that identifies constructors creates an instance the source lacks.** -/
theorem identifying_map_creates_instance :
    mapPattern collapse inert ∈ applyEquationAt (LanguageDef.empty "Unwrap") 0 (mapEquation collapse unwrap)
      .forward (mapPattern collapse (.apply "B" [inert])) := by
  decide +kernel

end Mettapedia.GSLT.LanguageDef.ScopedMatchingMaps
