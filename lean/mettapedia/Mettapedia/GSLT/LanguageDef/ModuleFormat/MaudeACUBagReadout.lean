import Mettapedia.GSLT.LanguageDef.ModuleFormat.MaudeMatching
import Mettapedia.GSLT.LanguageDef.ModuleFormat.MaudeTermCodec
import Mettapedia.GSLT.LanguageDef.ModuleFormat.MaudeACUBagCompilation
import Mettapedia.Languages.Maude.ACUFold
import Mathlib.Data.List.InsertIdx

/-! Read actual shared bag selections back to independent Maude terms.
Ground selected components match literally; the rest retains its source
multiplicity. This boundary uses the existing scoped matcher and binding
application, rather than defining another matching or execution algorithm.
-/

set_option autoImplicit false
set_option maxHeartbeats 3000000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.MaudeCompilation.ACUBagReadout

open Mettapedia.Languages
open Mettapedia.OSLF.MeTTaIL Syntax RuleBinding GeneralScopedMatch Match
open GeneralFirstOrderProjection

theorem ground_apply (bindings : Bindings) (term : Maude.Term) (ground : term.variables = []) :
    applyBindings bindings (encode term) = encode term := by
  have applied := encode_substitute_of_variables bindings Maude.Term.var term (by
    intro name member
    rw [ground] at member
    cases member)
  rw [Maude.Term.substitute_ground _ _ ground] at applied
  exact applied

theorem ground_match {rule : RewriteRule} {ambient : Nat} {site : RulePatternSite} {path : List Nat}
    {initial captured chosen : ScopedRuleMatching.Assignment}
    (source actual : Maude.Term) (ground : source.variables = [])
    (matched : Matches rule (GeneralRuleBindingInference.inferredSpec rule)
      ambient site path 0 initial (encode source) (encode actual) captured)
    (later : Extends captured chosen) (roots : GeneralPremise.RootValues ambient chosen) :
    source = actual := by
  have reconstructed := GeneralFirstOrderProjection.matching_reconstructs
    (encode_firstOrder source) matched later roots
  rw [ground_apply _ source ground] at reconstructed
  exact encode_injective reconstructed

theorem ground_scoped_match (rule : RewriteRule) (spec : RuleBindingSpec) (ambient : Nat)
    (site : RulePatternSite) (initial : ScopedRuleMatching.Assignment) (term : Maude.Term)
    (ground : term.variables = []) (path : List Nat) :
    Matches rule spec ambient site path 0 initial (encode term) (encode term) initial := by
  refine Maude.Term.rec
    (motive_1 := fun value => value.variables = [] → ∀ path,
      Matches rule spec ambient site path 0 initial (encode value) (encode value) initial)
    (motive_2 := fun values => values.flatMap Maude.Term.variables = [] → ∀ path index,
      Arguments rule spec ambient site path 0 initial index (values.map encode) (values.map encode) initial)
    ?_ ?_ ?_ ?_ term ground path
  · intro name impossible
    simp [Maude.Term.variables] at impossible
  · intro label values ih empty path
    simpa only [encode] using Matches.constructor (label := label)
      (ih (by simpa only [Maude.Term.variables] using empty) path 0)
  · intro _ path index
    exact .nil
  · intro first rest firstIH restIH empty path index
    have parts : first.variables = [] ∧ rest.flatMap Maude.Term.variables = [] := by
      simpa only [List.flatMap_cons, List.append_eq_nil_iff] using empty
    exact .cons (firstIH parts.1 (path ++ [index])) (restIH parts.2 path (index + 1))

theorem bag_covers (heads sources residual : List Maude.Term) (restName : String)
    {rule : RewriteRule} {spec : RuleBindingSpec} {ambient index : Nat} {site : RulePatternSite} {path : List Nat}
    {initial : ScopedRuleMatching.Assignment}
    (ground : ∀ head ∈ heads, head.variables = [])
    (partition : sources.Perm (heads ++ residual))
    (restCapturable : ∀ actual : List Maude.Term, actual.Perm residual → ∃ captured,
      ScopedRuleMatching.captureRest? rule spec ambient 0 site (path ++ [index + heads.length])
        initial restName .hashBag (actual.map encode) = some captured) :
    ∃ (actual : List Maude.Term) (captured : ScopedRuleMatching.Assignment), actual.Perm residual ∧
      Bag rule spec ambient site path 0 initial index (heads.map encode) (some restName) .hashBag
        (sources.map encode) captured := by
  cases heads with
  | nil =>
    have same : sources.Perm residual := by simpa only [List.nil_append] using partition
    obtain ⟨captured, stored⟩ := restCapturable sources same
    exact ⟨sources, captured, same, .rest (by simpa only [List.length_nil, Nat.add_zero] using stored)⟩
  | cons first heads =>
    have member : first ∈ sources := partition.mem_iff.mpr (List.mem_append_left residual List.mem_cons_self)
    obtain ⟨selected, within, selectedIs⟩ := List.mem_iff_getElem.mp member
    have presented : sources.Perm (first :: sources.eraseIdx selected) := by
      simpa only [selectedIs] using (List.getElem_cons_eraseIdx_perm within).symm
    have remaining : (sources.eraseIdx selected).Perm (heads ++ residual) :=
      List.Perm.cons_inv (presented.symm.trans partition)
    have endIndex : index + 1 + heads.length = index + (first :: heads).length := by
      simp only [List.length_cons]
      omega
    have restCapturable' : ∀ actual : List Maude.Term, actual.Perm residual → ∃ captured,
        ScopedRuleMatching.captureRest? rule spec ambient 0 site (path ++ [(index + 1) + heads.length])
          initial restName .hashBag (actual.map encode) = some captured := by
      rw [endIndex]
      exact restCapturable
    obtain ⟨actual, captured, same, tail⟩ := bag_covers heads (sources.eraseIdx selected) residual restName
      (fun term inside => ground term (List.mem_cons_of_mem first inside)) remaining restCapturable'
    refine ⟨actual, captured, same, Bag.cons (middle := initial) selected
      (by simpa only [List.length_map] using within) ?_ ?_⟩
    · simpa only [List.getElem_map, selectedIs] using ground_scoped_match rule spec ambient site initial
        first (ground first List.mem_cons_self) (path ++ [index])
    · simpa only [List.eraseIdx_map] using tail
termination_by heads.length

theorem bag_readout (heads sources : List Maude.Term) (restName : String)
    {rule : RewriteRule} {ambient index : Nat} {site : RulePatternSite} {path : List Nat}
    {initial captured chosen : ScopedRuleMatching.Assignment}
    (ground : ∀ head ∈ heads, head.variables = [])
    (matched : Bag rule (GeneralRuleBindingInference.inferredSpec rule) ambient site path 0 initial index
      (heads.map encode) (some restName) .hashBag (sources.map encode) captured)
    (later : Extends captured chosen) (roots : GeneralPremise.RootValues ambient chosen) :
    ∃ residual, sources.Perm (heads ++ residual) ∧
      (ordinary chosen).lookup restName = some (.collection .hashBag (residual.map encode) none) := by
  cases heads with
  | nil =>
    cases matched with
    | rest stored =>
      exact ⟨sources, by simp,
        capture_ordinary_compatible stored later roots
          (restName, Pattern.collection .hashBag (sources.map encode) none) List.mem_cons_self⟩
  | cons first heads =>
    cases matched with
    | cons selected within head tail =>
      rename_i middle
      have sourceWithin : selected < sources.length := by simpa only [List.length_map] using within
      have matchedHead : Matches rule (GeneralRuleBindingInference.inferredSpec rule)
          ambient site (path ++ [index]) 0 initial (encode first) (encode sources[selected]) middle := by
        simpa only [List.getElem_map] using head
      have same := ground_match first sources[selected] (ground first List.mem_cons_self)
        matchedHead (tail.extends.trans later) roots
      have matchedTail : Bag rule (GeneralRuleBindingInference.inferredSpec rule)
          ambient site path 0 middle (index + 1) (heads.map encode) (some restName) .hashBag
          ((sources.eraseIdx selected).map encode) captured := by
        simpa only [List.eraseIdx_map] using tail
      obtain ⟨residual, partition, read⟩ := bag_readout heads (sources.eraseIdx selected) restName
        (fun term member => ground term (List.mem_cons_of_mem first member)) matchedTail later roots
      refine ⟨residual, ?_, read⟩
      have conserved := (List.getElem_cons_eraseIdx_perm sourceWithin).symm.trans
        (partition.cons sources[selected])
      simpa only [same, List.cons_append] using conserved
termination_by heads.length

theorem apply_residual (bindings : Bindings) (body residual : List Maude.Term) (restName : String)
    (ground : ∀ term ∈ body, term.variables = [])
    (read : bindings.lookup restName = some (.collection .hashBag (residual.map encode) none)) :
    applyBindings bindings (.collection .hashBag (body.map encode) (some restName)) =
      .collection .hashBag ((body ++ residual).map encode) none := by
  have children : (body.map encode).map (applyBindings bindings) = body.map encode := by
    rw [List.map_map]
    apply List.map_congr_left
    intro term member
    exact ground_apply bindings term (ground term member)
  simp only [Bindings.lookup, Option.map_eq_some_iff] at read
  obtain ⟨⟨name, value⟩, found, same⟩ := read
  change value = .collection .hashBag (residual.map encode) none at same
  subst value
  simp only [applyBindings, children, found, beq_self_eq_true, if_true, List.map_append]

theorem encode_scoped (ambient : Nat) (term : Maude.Term) :
    (encode term).isWellScopedAt ambient = true := by
  refine Maude.Term.rec
    (motive_1 := fun value => (encode value).isWellScopedAt ambient = true)
    (motive_2 := fun values => Pattern.isWellScopedListAt ambient (values.map encode) = true)
    ?_ ?_ ?_ ?_ term
  · intro name
    simp only [encode, Pattern.isWellScopedAt]
  · intro label values ih
    simpa only [encode, Pattern.isWellScopedAt] using ih
  · rfl
  · intro first rest firstIH restIH
    simp only [List.map_cons, Pattern.isWellScopedListAt, firstIH, restIH, Bool.and_self]

theorem encoded_parts_scoped (ambient : Nat) (parts : List Maude.Term) :
    Pattern.isWellScopedListAt ambient (parts.map encode) = true := by
  induction parts with
  | nil => rfl
  | cons first rest ih =>
    simp only [List.map_cons, Pattern.isWellScopedListAt, encode_scoped, ih, Bool.and_self]

theorem compiled_rest_capturable {theory : Maude.Theory}
    (operation : Maude.ACUOperation theory []) (row : Maude.Row) (index ambient : Nat)
    (residual : List Maude.Term) :
    ∃ captured, ScopedRuleMatching.captureRest? (ACUBagCompilation.compileRule operation row index)
      (GeneralRuleBindingInference.inferredSpec (ACUBagCompilation.compileRule operation row index))
      ambient 0 .left ([0] ++ [(operation.flatten row.left).length]) []
      ACUBagCompilation.restName .hashBag (residual.map encode) = some captured := by
  let rule := ACUBagCompilation.compileRule operation row index
  let target := Pattern.collection .hashBag (residual.map encode) none
  let environment : Bindings := [(ACUBagCompilation.restName, target)]
  have dependency : dependencies? (GeneralRuleBindingInference.inferredSpec rule) ACUBagCompilation.restName = some [] := by
    apply inferred_dependencies_of_lookup rule
      (type := .collection .hashBag (.base (ACUBagCompilation.tokenSort operation.declaration)))
    · simp [rule, ACUBagCompilation.compileRule]
    · simp [rule, ACUBagCompilation.compileRule]
  have coherent : NameCoherent rule .left [0]
      (.collection .hashBag ((operation.flatten row.left).map encode) (some ACUBagCompilation.restName)) := by
    simpa only [rule, ACUBagCompilation.compileRule, ACUBagPresentation.pack, List.nil_append] using
      (NameCoherent.left rule).arguments.head
  have restCoherent : NameCoherent rule .left ([0] ++ [(operation.flatten row.left).length])
      (.fvar ACUBagCompilation.restName) := by
    simpa only [List.length_map] using coherent.collection_rest
  have scopeProof : target.isWellScopedAt ambient = true := by
    simpa only [target, Pattern.isWellScopedAt] using encoded_parts_scoped ambient residual
  obtain ⟨captured, stored, _⟩ := capture_instance
    (environment := environment) (initial := []) (by intro entry impossible; cases impossible)
    (by simp [environment, Bindings.lookup]) dependency restCoherent scopeProof
  exact ⟨captured, stored⟩

theorem compiled_match_covers {theory : Maude.Theory}
    (operation : Maude.ACUOperation theory []) (row : Maude.Row) (index ambient : Nat)
    (sources residual : List Maude.Term)
    (ground : ∀ head ∈ operation.flatten row.left, head.variables = [])
    (partition : sources.Perm (operation.flatten row.left ++ residual)) :
    ∃ captured, Matches (ACUBagCompilation.compileRule operation row index)
      (GeneralRuleBindingInference.inferredSpec (ACUBagCompilation.compileRule operation row index))
      ambient .left [] 0 [] (ACUBagCompilation.compileRule operation row index).left
      (ACUBagPresentation.pack (ACUBagCompilation.wrapperName operation.declaration) sources) captured := by
  obtain ⟨actual, captured, _, matched⟩ := bag_covers (operation.flatten row.left) sources residual
    ACUBagCompilation.restName (ambient := ambient) (index := 0) (site := .left) (path := [0])
    (initial := []) ground partition (fun actual _ => by
      simpa only [Nat.zero_add] using compiled_rest_capturable operation row index ambient actual)
  refine ⟨captured, ?_⟩
  exact Matches.constructor (.cons (.bag (by decide) matched) .nil)

theorem compiled_enumerator_covers {theory : Maude.Theory}
    (operation : Maude.ACUOperation theory []) (row : Maude.Row) (index ambient : Nat)
    (sources residual : List Maude.Term)
    (ground : ∀ head ∈ operation.flatten row.left, head.variables = [])
    (partition : sources.Perm (operation.flatten row.left ++ residual)) :
    ∃ captured, captured ∈ ScopedRuleMatching.matchAt (ACUBagCompilation.compileRule operation row index)
      (GeneralRuleBindingInference.inferredSpec (ACUBagCompilation.compileRule operation row index))
      ambient .left [] 0 [] (ACUBagCompilation.compileRule operation row index).left
      (ACUBagPresentation.pack (ACUBagCompilation.wrapperName operation.declaration) sources) := by
  obtain ⟨captured, matched⟩ := compiled_match_covers operation row index ambient sources residual ground partition
  exact ⟨captured, matched.complete⟩

theorem matched_source_step {theory : Maude.Theory} {context : Maude.VariableContext}
    (operation : Maude.ACUOperation theory context) (checked : theory.signature.check = true)
    {source left right : Maude.Term} (typed : Maude.HasSort theory.signature context source operation.declaration.result)
    (heads : List Maude.Term) (restName : String)
    {rule : RewriteRule} {ambient index : Nat} {site : RulePatternSite} {path : List Nat}
    {initial captured chosen : ScopedRuleMatching.Assignment}
    (ground : ∀ head ∈ heads, head.variables = [])
    (matched : Bag rule (GeneralRuleBindingInference.inferredSpec rule) ambient site path 0 initial index
      (heads.map encode) (some restName) .hashBag ((operation.flatten source).map encode) captured)
    (later : Extends captured chosen) (roots : GeneralPremise.RootValues ambient chosen)
    (redex : Maude.Equivalent theory context operation.declaration.result (operation.fold heads) left)
    (firing : Maude.RawStep theory context operation.declaration.result left right) :
    ∃ residual,
      Maude.Step theory context operation.declaration.result source (operation.fold (operation.flatten right ++ residual)) ∧
      (ordinary chosen).lookup restName = some (.collection .hashBag (residual.map encode) none) := by
  obtain ⟨residual, partition, read⟩ := bag_readout heads (operation.flatten source) restName ground matched later roots
  exact ⟨residual, operation.step_of_subbag checked typed heads residual partition redex firing, read⟩

theorem closed_sorted_ground {signature : Maude.Signature} {term : Maude.Term} {sort : String}
    (typed : Maude.HasSort signature [] term sort) : term.variables = [] := by
  cases shape : term.variables with
  | nil => rfl
  | cons name rest =>
    have impossible : name ∈ ([] : List String) := typed_variables typed name (by
      rw [shape]
      exact List.mem_cons_self)
    cases impossible

theorem ground_row_fires {theory : Maude.Theory} {row : Maude.Row} {sort : String}
    (member : row ∈ theory.rules) (checked : row.check theory.signature = true)
    (conditions : row.conditions = [])
    (leftTyped : Maude.HasSort theory.signature [] row.left sort)
    (rightTyped : Maude.HasSort theory.signature [] row.right sort) :
    Maude.RawStep theory [] sort row.left row.right := by
  have leftGround := closed_sorted_ground leftTyped
  have rightGround := closed_sorted_ground rightTyped
  have contextEmpty : row.usedContext = [] := by
    simp [Maude.Row.usedContext, leftGround, rightGround, conditions]
  have valuation : Maude.TypedValuation theory.signature [] row.usedContext Maude.Term.var := by
    intro name value found
    rw [contextEmpty] at found
    cases found
  have firing := Maude.RawStep.rule Maude.Term.var member checked
    (contextEmpty.symm ▸ leftTyped) (contextEmpty.symm ▸ rightTyped) valuation
    (conditions.symm ▸ Maude.Conditions.nil Maude.Term.var)
  simpa only [Maude.Term.substitute_ground _ _ leftGround,
    Maude.Term.substitute_ground _ _ rightGround] using firing

theorem compiled_match_source_step {theory : Maude.Theory}
    (operation : Maude.ACUOperation theory []) (checked : theory.signature.check = true)
    (row : Maude.Row) (index : Nat) (member : row ∈ theory.rules)
    (rowChecked : row.check theory.signature = true) (conditions : row.conditions = [])
    (leftTyped : Maude.HasSort theory.signature [] row.left operation.declaration.result)
    (rightTyped : Maude.HasSort theory.signature [] row.right operation.declaration.result)
    {source : Maude.Term} (sourceTyped : Maude.HasSort theory.signature [] source operation.declaration.result)
    {ambient : Nat} {site : RulePatternSite} {path : List Nat}
    {initial captured chosen : ScopedRuleMatching.Assignment}
    (matched : Matches (ACUBagCompilation.compileRule operation row index)
      (GeneralRuleBindingInference.inferredSpec (ACUBagCompilation.compileRule operation row index))
      ambient site path 0 initial (ACUBagCompilation.compileRule operation row index).left
      (ACUBagPresentation.encodeBag operation (ACUBagCompilation.wrapperName operation.declaration) source) captured)
    (later : Extends captured chosen) (roots : GeneralPremise.RootValues ambient chosen) :
    ∃ residual,
      Maude.Step theory [] operation.declaration.result source (operation.fold (operation.flatten row.right ++ residual)) ∧
      applyBindings (ordinary chosen) (ACUBagCompilation.compileRule operation row index).right =
        ACUBagPresentation.pack (ACUBagCompilation.wrapperName operation.declaration)
          (operation.flatten row.right ++ residual) := by
  cases matched with
  | constructor arguments =>
    cases arguments with
    | cons first tail =>
      cases tail
      cases first with
      | bag _ matchedBag =>
        have leftGround : ∀ term ∈ operation.flatten row.left, term.variables = [] := fun term inside =>
          closed_sorted_ground (operation.flatten_sorted checked leftTyped term inside)
        obtain ⟨residual, step, read⟩ := matched_source_step operation checked sourceTyped
          (operation.flatten row.left) ACUBagCompilation.restName leftGround matchedBag later roots
          (.symm (operation.equivalent_fold_flatten checked leftTyped))
          (ground_row_fires member rowChecked conditions leftTyped rightTyped)
        refine ⟨residual, step, ?_⟩
        have rightGround : ∀ term ∈ operation.flatten row.right, term.variables = [] := fun term inside =>
          closed_sorted_ground (operation.flatten_sorted checked rightTyped term inside)
        have spliced := apply_residual (ordinary chosen) (operation.flatten row.right) residual
          ACUBagCompilation.restName rightGround read
        simpa only [ACUBagCompilation.compileRule, ACUBagPresentation.pack, applyBindings,
          List.map_cons, List.map_nil] using congrArg
            (fun parts => Pattern.apply (ACUBagCompilation.wrapperName operation.declaration) [parts]) spliced

#print axioms ground_match
#print axioms bag_covers
#print axioms bag_readout
#print axioms apply_residual
#print axioms matched_source_step
#print axioms compiled_match_source_step
#print axioms compiled_enumerator_covers

end Mettapedia.GSLT.LanguageDef.ModuleFormat.MaudeCompilation.ACUBagReadout
