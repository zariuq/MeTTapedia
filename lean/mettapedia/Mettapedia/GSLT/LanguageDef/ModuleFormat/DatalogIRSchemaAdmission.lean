import Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIRCanonicalAdmission
import Mettapedia.OSLF.MeTTaIL.GeneralVectorPremiseAdmission

/-! The compiler's atom and guard schemas pass the existing schema type
checker in their actual generated declaration context. Body occurrence
positions supply anonymous variables; source range restriction supplies
the variables used in conclusions and comparison inputs. -/

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 3000000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIR.SchemaAdmission

open Mettapedia.Languages.Datalog
open Mettapedia.OSLF.MeTTaIL Syntax GeneralRuleBindingInference
open Mettapedia.GSLT.LanguageDef.WellSorted

theorem context_lookup (pools : Join.Pools) (ordinal : Nat) (clause : Clause) (rule : RewriteRule)
    (compiled : Query.compileClause? pools ordinal clause = some rule) (name : String) :
    GeneralPremise.lookupRuleType? rule name = (BindingContext.context pools clause).lookup name := by
  rw [GeneralPremise.lookupRuleType?_eq_lookup,BindingContext.compiled_context pools ordinal clause rule compiled]

private theorem argument_typed (language : LanguageDef) (pools : Join.Pools) (ordinal : Nat)
    (clause : Clause) (rule : RewriteRule) (compiledRule : Query.compileClause? pools ordinal clause = some rule)
    (position index : Nat) (argument : Argument) (code : Pattern)
    (compiled : Join.argument? pools position index argument = some code)
    (logical : ∀ name, argument = .var name → name ∈ clause.providedVariables)
    (anonymous : argument = .anonymous →
      GeneralPremise.lookupRuleType? rule (Join.anonymousVariable position index) = some (.base "DlValue")) :
    HasType language (GeneralPremise.lookupRuleType? rule) [] code (.base "DlValue") := by
  cases argument with
  | var name =>
    have same : Pattern.fvar (Join.logicalVariable name) = code := Option.some.inj compiled
    subst code
    apply HasType.fvar
    rw [context_lookup pools ordinal clause rule compiledRule]
    exact BindingContext.logical_declared pools clause name (logical name rfl)
  | anonymous =>
    have same : Pattern.fvar (Join.anonymousVariable position index) = code := Option.some.inj compiled
    subst code
    exact .fvar (anonymous rfl)
  | literal value =>
    obtain ⟨slot,selected,rfl⟩ := Option.map_eq_some_iff.mp compiled
    apply HasType.fvar
    rw [context_lookup pools ordinal clause rule compiledRule]
    exact BindingContext.literal_declared pools clause slot (List.idxOf?_eq_some_iff.mp selected).1

private theorem constructor_typed (language : LanguageDef) (terms : language.terms = Query.baseLanguage.terms)
    (free : FreeTypeContext) (index : Fin Query.baseLanguage.terms.length) (arguments : List Pattern)
    (ordinary : ¬ UsesBareCollection (Query.baseLanguage.terms.get index))
    (typed : ArgumentsHaveTypes language free [] arguments (Query.baseLanguage.terms.get index).params) :
    HasType language free [] (.apply (Query.baseLanguage.terms.get index).label arguments)
      (.base (Query.baseLanguage.terms.get index).category) := by
  apply HasType.constructor ?_ ordinary typed
  rw [terms]
  exact List.get_mem _ index

private theorem compiled_elements (language : LanguageDef) (free : FreeTypeContext)
    (compile : Argument × Nat → Option Pattern) (entries : List (Argument × Nat)) (codes : List Pattern)
    (related : List.Forall₂ (fun entry code => compile entry = some code) entries codes)
    (typed : ∀ entry ∈ entries, ∀ code, compile entry = some code → HasType language free [] code (.base "DlValue")) :
    ElementsHaveType language free [] codes (.base "DlValue") := by
  induction related with
  | nil => exact .nil _ _
  | @cons entry code entries codes first rest ih =>
    exact .cons (typed entry List.mem_cons_self code first)
      (ih (fun entry member => typed entry (List.mem_cons_of_mem _ member)))

private theorem named_elements (language : LanguageDef) (free : FreeTypeContext)
    (names : List String) (type : TypeExpr) (declared : ∀ name ∈ names, free name = some type) :
    ElementsHaveType language free [] (names.map Pattern.fvar) type := by
  induction names with
  | nil => exact .nil _ _
  | cons name names ih =>
    exact .cons (.fvar (declared name List.mem_cons_self))
      (ih (fun other member => declared other (List.mem_cons_of_mem _ member)))

theorem left_typed (language : LanguageDef) (terms : language.terms = Query.baseLanguage.terms)
    (pools : Join.Pools) (ordinal : Nat) (clause : Clause) (rule : RewriteRule)
    (compiled : Query.compileClause? pools ordinal clause = some rule) :
    HasType language (GeneralPremise.lookupRuleType? rule) [] rule.left (.base "DlStatement") := by
  rw [(FiringReading.compiled_fields pools ordinal clause rule compiled).1]
  have relations := named_elements language (GeneralPremise.lookupRuleType? rule)
    (Join.relationSlots pools) (.base "DlRelation") (by
      intro name member
      obtain ⟨index,inside,rfl⟩ := List.mem_map.mp member
      rw [context_lookup pools ordinal clause rule compiled]
      exact BindingContext.relation_declared pools clause index (List.mem_range.mp inside))
  have literals := named_elements language (GeneralPremise.lookupRuleType? rule)
    (Join.literalSlots pools) (.base "DlValue") (by
      intro name member
      obtain ⟨index,inside,rfl⟩ := List.mem_map.mp member
      rw [context_lookup pools ordinal clause rule compiled]
      exact BindingContext.literal_declared pools clause index (List.mem_range.mp inside))
  exact constructor_typed language terms _ ⟨33,by decide +kernel⟩ _
    (by rintro ⟨_,_,_,impossible⟩; have bad : (2 : Nat) = 1 := congrArg List.length impossible; cases bad)
    (.cons trivial rfl (HasType.collection (collectionType := .vec) (rest := none) relations)
      (.cons trivial rfl (HasType.collection (collectionType := .vec) (rest := none) literals) .nil))

theorem atom_typed (language : LanguageDef) (terms : language.terms = Query.baseLanguage.terms)
    (pools : Join.Pools) (ordinal : Nat) (clause : Clause) (rule : RewriteRule)
    (compiledRule : Query.compileClause? pools ordinal clause = some rule)
    (position : Nat) (source : Mettapedia.Languages.Datalog.Atom) (code : Pattern)
    (compiled : Join.atom? pools position source = some code)
    (logical : ∀ name ∈ source.variables, name ∈ clause.providedVariables)
    (anonymous : ∀ index, source.arguments[index]? = some .anonymous →
      GeneralPremise.lookupRuleType? rule (Join.anonymousVariable position index) = some (.base "DlValue")) :
    HasType language (GeneralPremise.lookupRuleType? rule) [] code (.base "DlStatement") := by
  change ((Join.relation? pools source.relation).bind fun relation =>
    (source.arguments.zipIdx.mapM fun entry => Join.argument? pools position entry.2 entry.1).bind fun arguments =>
      some (Pattern.apply "GroundFact" [relation,.apply "GroundTuple" [Join.vector arguments]])) = some code at compiled
  simp only [Option.bind_eq_some_iff,Option.some.injEq] at compiled
  obtain ⟨relation,named,arguments,argsCompiled,rfl⟩ := compiled
  obtain ⟨slot,selected,rfl⟩ := Option.map_eq_some_iff.mp named
  have relationTyped : HasType language (GeneralPremise.lookupRuleType? rule) []
      (.fvar (Join.relationSlot slot)) (.base "DlRelation") := by
    apply HasType.fvar
    rw [context_lookup pools ordinal clause rule compiledRule]
    exact BindingContext.relation_declared pools clause slot (List.idxOf?_eq_some_iff.mp selected).1
  have elements : ElementsHaveType language (GeneralPremise.lookupRuleType? rule) [] arguments (.base "DlValue") := by
    apply compiled_elements language _ _ _ _ (CompilationFlow.mapM_relation _ _ _ argsCompiled)
    intro entry member argumentCode formed
    apply argument_typed language pools ordinal clause rule compiledRule position entry.2 entry.1 argumentCode formed
    · intro name same
      apply logical name
      apply List.mem_flatMap.mpr
      exact ⟨entry.1,List.fst_mem_of_mem_zipIdx member,by simp [same,Argument.vars]⟩
    · intro same
      apply anonymous entry.2
      simpa only [same] using List.mk_mem_zipIdx_iff_getElem?.mp member
  have vectorTyped := HasType.collection (collectionType := .vec) (rest := none) elements
  have tupleTyped := constructor_typed language terms _ ⟨9,by decide +kernel⟩ [Join.vector arguments]
    (by rintro ⟨_,_,_,impossible⟩; have bad : (0 : Nat) = 1 := congrArg List.length impossible; cases bad)
    (.cons trivial rfl vectorTyped .nil)
  exact constructor_typed language terms _ ⟨28,by decide +kernel⟩ _
    (by rintro ⟨_,_,_,impossible⟩; have bad : (2 : Nat) = 1 := congrArg List.length impossible; cases bad)
    (.cons trivial rfl relationTyped (.cons trivial rfl tupleTyped .nil))

theorem body_atom_typed (language : LanguageDef) (terms : language.terms = Query.baseLanguage.terms)
    (pools : Join.Pools) (ordinal : Nat) (clause : Clause) (rule : RewriteRule)
    (compiledRule : Query.compileClause? pools ordinal clause = some rule)
    (position : Nat) (source : Mettapedia.Languages.Datalog.Atom) (code : Pattern)
    (atSource : (Join.orderedBody clause)[position]? = some (.atom source))
    (compiled : Join.atom? pools position source = some code) :
    HasType language (GeneralPremise.lookupRuleType? rule) [] code (.base "DlStatement") := by
  apply atom_typed language terms pools ordinal clause rule compiledRule position source code compiled
  · intro name member
    exact List.mem_flatMap.mpr ⟨source,(BodyCompilation.ordered_atom clause source).mp (List.mem_of_getElem? atSource),member⟩
  · intro index present
    rw [context_lookup pools ordinal clause rule compiledRule]
    exact BindingContext.anonymous_declared pools clause position index source atSource present

theorem head_typed (language : LanguageDef) (terms : language.terms = Query.baseLanguage.terms)
    (pools : Join.Pools) (ordinal : Nat) (clause : Clause) (rule : RewriteRule)
    (compiledRule : Query.compileClause? pools ordinal clause = some rule) :
    HasType language (GeneralPremise.lookupRuleType? rule) [] rule.right (.base "DlStatement") := by
  have restricted := (BodyCompilation.compiled_body pools ordinal clause rule compiledRule).1
  apply atom_typed language terms pools ordinal clause rule compiledRule clause.body.length clause.head rule.right
    (FiringReading.compiled_fields pools ordinal clause rule compiledRule).2
  · intro name member
    obtain ⟨argument,atArgument,used⟩ := List.mem_flatMap.mp member
    exact restricted.2 name (List.mem_flatMap.mpr ⟨argument,List.mem_append_left _ atArgument,used⟩)
  · intro index present
    exact (restricted.1 _ (List.mem_append_left _ (List.mem_of_getElem? present)) rfl).elim

theorem guard_argument_typed (language : LanguageDef) (pools : Join.Pools) (ordinal : Nat)
    (clause : Clause) (rule : RewriteRule) (compiledRule : Query.compileClause? pools ordinal clause = some rule)
    (guard : Comparison) (inClause : guard ∈ Comparisons.guards clause)
    (position index : Nat) (argument : Argument) (inside : argument ∈ guard.arguments)
    (code : Pattern) (compiled : Join.argument? pools position index argument = some code) :
    HasType language (GeneralPremise.lookupRuleType? rule) [] code (.base "DlValue") := by
  have restricted := (BodyCompilation.compiled_body pools ordinal clause rule compiledRule).1
  have required := Comparisons.guard_arguments_required inClause inside
  apply argument_typed language pools ordinal clause rule compiledRule position index argument code compiled
  · intro name same
    exact restricted.2 name (List.mem_flatMap.mpr ⟨argument,required,by simp [same,Argument.vars]⟩)
  · intro same
    exact (restricted.1 argument required same).elim

theorem head_projection (language : LanguageDef) (terms : language.terms = Query.baseLanguage.terms)
    (pools : Join.Pools) (ordinal : Nat) (clause : Clause) (rule : RewriteRule)
    (compiled : Query.compileClause? pools ordinal clause = some rule) :
    GeneralPremise.checkRootProjectionSchema rule (inferredSpec rule) .right [] rule.right = true := by
  exact GeneralPremise.Static.vector_projection_of_typed
    (BindingContext.compiled_context_nodup pools ordinal clause rule compiled)
    (InstanceMatching.atom_shape pools clause.body.length clause.head rule.right
      (FiringReading.compiled_fields pools ordinal clause rule compiled).2)
    (GeneralFirstOrderProjection.NameCoherent.right rule)
    (head_typed language terms pools ordinal clause rule compiled)

#print axioms body_atom_typed
#print axioms left_typed
#print axioms head_typed
#print axioms guard_argument_typed
#print axioms head_projection

end Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIR.SchemaAdmission
