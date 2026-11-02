import Mettapedia.GSLT.LanguageDef.RestrictionBlocks.ReplicationLawShapes
import Mettapedia.GSLT.LanguageDef.RestrictionBlocks.ReplicationObjects

/-!
# Extensions by constructors

A chain of laws is a chain in every language with more rules and more laws, none with premises (`sortedEquiv_mono`,
`objectChain_mono`). A language extends another by constructors (`TermExtension`) when it has the other's grammar and some rules more,
labelled apart from every label the other speaks of, none with a collection among its parameters, and the same laws,
none with premises.

- **Typing**: a term that applies none of the added constructors (`avoids`) has a type in the smaller language exactly
  when it has it in the larger one (`TermExtension.typed_restrict`, `HasType.of_terms_subset`), and a term typed in the
  smaller language applies none of them (`TermExtension.avoids_of_typed`).
- **Generators**: a generator of the larger language's static theory from a term that avoids the added constructors
  is one of the smaller language (`TermExtension.step_restrict`), and every generator of the smaller language is one
  of the larger (`TermExtension.step_extend`).
- **Conservativity**: when the larger language's laws keep the terms that avoid the added constructors
  (`KeepsAvoiding`), its chains of laws from a term of the smaller language are the smaller language's
  (`TermExtension.sortedEquiv_restrict`, `TermExtension.objectChain_restrict`): the larger static theory extends the
  smaller one conservatively.

The laws of the restriction-block theory with replication apply only the block's own constructors, so they keep every
other constructor out (`LawShape.avoids_iff`).
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.RestrictionBlocks

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Substitution (liftBVars)
open Mettapedia.OSLF.MeTTaIL.DerivedContexts (OneHoleContext)
open Mettapedia.OSLF.MeTTaIL.ContextualStep (BasePremiseEvaluator PremisesAt engineBasePremises)
open Mettapedia.OSLF.MeTTaIL.Engine (RelationEnv)
open Mettapedia.GSLT.LanguageDef.WellSorted (HasType ArgumentsHaveTypes ElementsHaveType FreeTypeContext
  CollectionTypedAt isObjectPattern)
open Mettapedia.GSLT.LanguageDef.EquationSemantics (EquationGenerator EquationInstanceAt DerivedInstance
  EquationContextStep SortedAt AlgebraRule)

/-! ## Terms that avoid some constructors -/

mutual
  /-- **A term avoids some labels**: it applies no constructor so labelled. -/
  def avoids (labels : List String) : Pattern → Bool
    | .bvar _ | .fvar _ => true
    | .apply label arguments => decide (label ∉ labels) && avoidsList labels arguments
    | .lambda _ body => avoids labels body
    | .multiLambda _ _ body => avoids labels body
    | .subst body replacement => avoids labels body && avoids labels replacement
    | .collection _ elements _ => avoidsList labels elements

  def avoidsList (labels : List String) : List Pattern → Bool
    | [] => true
    | pattern :: patterns => avoids labels pattern && avoidsList labels patterns
end

variable {labels : List String}

theorem avoidsList_iff : ∀ {patterns : List Pattern},
    avoidsList labels patterns = true ↔ ∀ pattern ∈ patterns, avoids labels pattern = true
  | [] => by simp [avoidsList]
  | pattern :: patterns => by simp [avoidsList, avoidsList_iff (patterns := patterns)]

@[simp] theorem avoids_bvar (index : Nat) : avoids labels (.bvar index) = true := by simp [avoids]

@[simp] theorem avoids_fvar (name : String) : avoids labels (.fvar name) = true := by simp [avoids]

@[simp] theorem avoids_apply {label : String} {arguments : List Pattern} :
    avoids labels (.apply label arguments) = true ↔ label ∉ labels ∧ ∀ argument ∈ arguments, avoids labels argument = true := by
  simp [avoids, avoidsList_iff]

@[simp] theorem avoids_lambda {binder : Option String} {body : Pattern} :
    avoids labels (.lambda binder body) = avoids labels body := by simp [avoids]

@[simp] theorem avoids_multiLambda {arity : Nat} {binders : List String} {body : Pattern} :
    avoids labels (.multiLambda arity binders body) = avoids labels body := by simp [avoids]

@[simp] theorem avoids_subst {body replacement : Pattern} :
    avoids labels (.subst body replacement) = true ↔ avoids labels body = true ∧ avoids labels replacement = true := by
  simp [avoids]

@[simp] theorem avoids_collection {kind : CollType} {elements : List Pattern} {rest : Option String} :
    avoids labels (.collection kind elements rest) = true ↔ ∀ element ∈ elements, avoids labels element = true := by
  simp [avoids, avoidsList_iff]

/-- **Renaming bound variables keeps the constructors a term applies.** -/
theorem avoids_rename (pattern : Pattern) : ∀ (relabel : Nat → Nat),
    avoids labels (rename relabel pattern) = avoids labels pattern := by
  induction pattern using Pattern.inductionOn with
  | hbvar index => intro _; simp [rename_bvar]
  | hfvar name => intro _; simp [rename_fvar]
  | happly label arguments recurse =>
      intro relabel
      rw [rename_apply, Bool.eq_iff_iff, avoids_apply, avoids_apply, List.forall_mem_map]
      refine and_congr_right fun _ => forall₂_congr fun argument member => ?_
      rw [recurse argument member relabel]
  | hlambda binder body recurse =>
      intro relabel
      rw [rename_lambda, avoids_lambda, avoids_lambda, recurse]
  | hmultiLambda arity binders body recurse =>
      intro relabel
      rw [rename_multiLambda, avoids_multiLambda, avoids_multiLambda, recurse]
  | hsubst body replacement bodyRecurse replacementRecurse =>
      intro relabel
      rw [rename_subst, Bool.eq_iff_iff, avoids_subst, avoids_subst, bodyRecurse, replacementRecurse]
  | hcollection kind elements rest recurse =>
      intro relabel
      rw [rename_collection, Bool.eq_iff_iff, avoids_collection, avoids_collection, List.forall_mem_map]
      refine forall₂_congr fun element member => ?_
      rw [recurse element member relabel]

@[simp] theorem avoids_lift (cutoff shift : Nat) (pattern : Pattern) :
    avoids labels (liftBVars cutoff shift pattern) = avoids labels pattern := by
  rw [liftBVars_eq_rename, avoids_rename]

/-- **A context keeps whether a term avoids some labels.** -/
theorem avoids_fill_iff (context : OneHoleContext) {first second : Pattern}
    (same : avoids labels first = true ↔ avoids labels second = true) :
    avoids labels (context.fill first) = true ↔ avoids labels (context.fill second) = true := by
  induction context with
  | hole => exact same
  | apply constructor before inner after recurse =>
      simp only [OneHoleContext.fill, avoids_apply, List.mem_append, List.mem_cons, or_imp, forall_and,
        forall_eq]
      rw [recurse]
  | lambda binder inner recurse =>
      simp only [OneHoleContext.fill, avoids_lambda]
      exact recurse
  | multiLambda arity binders inner recurse =>
      simp only [OneHoleContext.fill, avoids_multiLambda]
      exact recurse
  | substBody inner replacement recurse =>
      simp only [OneHoleContext.fill, avoids_subst]
      rw [recurse]
  | substReplacement body inner recurse =>
      simp only [OneHoleContext.fill, avoids_subst]
      rw [recurse]
  | collection kind before inner after rest recurse =>
      simp only [OneHoleContext.fill, avoids_collection, List.mem_append, List.mem_cons, or_imp, forall_and,
        forall_eq]
      rw [recurse]

/-- **A term that avoids some labels fills its context with one that avoids them.** -/
theorem avoids_of_fill (context : OneHoleContext) {pattern : Pattern}
    (avoiding : avoids labels (context.fill pattern) = true) : avoids labels pattern = true := by
  induction context with
  | hole => exact avoiding
  | apply constructor before inner after recurse =>
      simp only [OneHoleContext.fill, avoids_apply, List.mem_append, List.mem_cons, or_imp, forall_and,
        forall_eq] at avoiding
      exact recurse avoiding.2.2.1
  | lambda binder inner recurse =>
      simp only [OneHoleContext.fill, avoids_lambda] at avoiding
      exact recurse avoiding
  | multiLambda arity binders inner recurse =>
      simp only [OneHoleContext.fill, avoids_multiLambda] at avoiding
      exact recurse avoiding
  | substBody inner replacement recurse =>
      simp only [OneHoleContext.fill, avoids_subst] at avoiding
      exact recurse avoiding.1
  | substReplacement body inner recurse =>
      simp only [OneHoleContext.fill, avoids_subst] at avoiding
      exact recurse avoiding.2
  | collection kind before inner after rest recurse =>
      simp only [OneHoleContext.fill, avoids_collection, List.mem_append, List.mem_cons, or_imp, forall_and,
        forall_eq] at avoiding
      exact recurse avoiding.2.1

/-! ## The laws of restriction and replication move no other constructor -/

/-- **The two sides of a law of the restriction-block theory with replication apply the same constructors but the
block's own.** -/
theorem LawShape.avoids_iff {block : ReplicationBlock} (unitApart : block.unit ∉ labels)
    (restrictApart : block.restrict ∉ labels) (replicateApart : block.replicate ∉ labels)
    (emptyApart : ∀ label ∈ block.emptyUnits, label ∉ labels) {source target : Pattern}
    (shape : LawShape block source target) : avoids labels source = true ↔ avoids labels target = true := by
  cases shape with
  | restrictionNil binder => simp [unitApart, restrictApart]
  | exchange outerBinder innerBinder body => simp [avoids_rename, restrictApart]
  | @extrusion members selected inside binder body chosen =>
      have around := List.getElem_cons_eraseIdx_perm inside
      rw [avoids_collection, ← forall_congr' fun member => imp_congr_left around.mem_iff, List.forall_mem_cons,
        chosen]
      simp [restrictApart]
  | @extrusionReverse binder members selected inside originals erased =>
      have around := List.getElem_cons_eraseIdx_perm inside
      have liftedIff : (∀ member ∈ members.eraseIdx selected, avoids labels member = true) ↔
          ∀ original ∈ originals, avoids labels original = true := by
        rw [erased, List.forall_mem_map]
        simp
      simp only [avoids_apply, avoids_lambda, avoids_collection, List.mem_singleton, forall_eq,
        List.forall_mem_cons, restrictApart, not_false_eq_true, true_and]
      rw [← forall_congr' fun member => imp_congr_left around.mem_iff, List.forall_mem_cons, liftedIff]
  | emptyUnit listed binder => simp [emptyApart _ listed, unitApart, restrictApart]
  | unfold process rest => simp [replicateApart]
  | unfoldSwap process rest => simp [replicateApart]
  | replicationNil => simp [replicateApart, unitApart]
  | twice process => simp [replicateApart]
  | par first second rest swapped => cases swapped <;> simp [replicateApart, and_comm]
  | parReverse first second rest swapped => cases swapped <;> simp [replicateApart, and_comm]
  | idempotent process rest => simp [replicateApart]
  | bagPerm permutation =>
      rw [avoids_collection, avoids_collection]
      exact forall_congr' fun member => imp_congr_left permutation.mem_iff
  | flatten pre inner post => simp [or_imp, forall_and]
  | singleton notLambda => simp
  | unitElim pre post => simp [or_imp, forall_and, unitApart]
  | emptyBag => simp [unitApart]

/-! ## Extensions by constructors -/

/-- **`large` extends `small` by constructors labelled in `added`**: it has the grammar of `small` and rules more, each
labelled in `added` and with no collection among its parameters; no label `small` speaks of, a constructor's or a
declared unit's, is added; and the two have the same laws, none with premises. -/
structure TermExtension (small large : LanguageDef) (added : List String) : Prop where
  terms : small.terms ⊆ large.terms
  labelled : ∀ rule ∈ large.terms, rule ∉ small.terms → rule.label ∈ added
  noCollections : ∀ rule ∈ large.terms, rule ∉ small.terms → ∀ parameter ∈ rule.params, ∀ kind,
    parameter.typeExpr.mentionsCollection kind = false
  apart : ∀ rule ∈ small.terms, rule.label ∉ added ∧
    ∀ algebra, rule.algebra? = some algebra → ∀ unit, algebra.unit = some unit → unit ∉ added
  equations : small.equations = large.equations
  premises : ∀ equation ∈ large.equations, equation.premises = []

/-- **The laws of a language keep the terms that avoid some labels**: a generator relates a term that avoids them only
to one that does. -/
def KeepsAvoiding (base : BasePremiseEvaluator) (language : LanguageDef) (labels : List String) : Prop :=
  ∀ source target, EquationGenerator base language source target →
    (avoids labels source = true ↔ avoids labels target = true)

/-! ## Larger presentations keep the static theory -/

section Mono

variable {first second : LanguageDef}

/-- **An instance of a law is one in every language with the law**, when the law has no premises. -/
theorem equationInstanceAt_mono {base : BasePremiseEvaluator}
    (laws : ∀ equation ∈ first.equations, equation ∈ second.equations)
    (premises : ∀ equation ∈ first.equations, equation.premises = []) {fuel : Nat} {source target : Pattern}
    (equationInstance : EquationInstanceAt base first fuel source target) :
    EquationInstanceAt base second fuel source target := by
  cases equationInstance with
  | forward member raw matched premisesHold applied =>
      have none := premises _ member
      rw [none] at premisesHold
      cases premisesHold
      exact .forward (laws _ member) raw matched (by rw [none]; exact .nil _) applied
  | reverse member raw matched premisesHold applied =>
      have none := premises _ member
      rw [none] at premisesHold
      cases premisesHold
      exact .reverse (laws _ member) raw matched (by rw [none]; exact .nil _) applied
  | declared member notRaw declared =>
      obtain ⟨spec, captured, final, oriented, admitted, sourceScoped, matched, premisesHold, reduced,
        targetScoped⟩ := declared
      have none := premises _ member
      rw [none] at premisesHold
      cases premisesHold
      exact .declared (laws _ member) notRaw
        ⟨spec, captured, _, oriented, admitted, sourceScoped, matched, by rw [none]; exact .nil _, reduced,
          targetScoped⟩

theorem algebraRule_mono (included : first.terms ⊆ second.terms) {rule : GrammarRule} {kind : CollType}
    {algebra : CollectionAlgebra} (algebraRule : AlgebraRule first rule kind algebra) :
    AlgebraRule second rule kind algebra := by
  refine ⟨included algebraRule.authored, algebraRule.declared, algebraRule.selfSorted, fun unit unitIs => ?_⟩
  obtain ⟨unitRule, unitMember, rest⟩ := algebraRule.unitAuthored unit unitIs
  exact ⟨unitRule, included unitMember, rest⟩

/-- **A law of a language's bags is one of every language with its grammar.** -/
theorem derived_mono (included : first.terms ⊆ second.terms) {source target : Pattern}
    (derived : DerivedInstance first source target) : DerivedInstance second source target := by
  cases derived with
  | bagPerm member typed permutation =>
      exact .bagPerm (included member) (typed.of_terms_subset included) permutation
  | setPerm member typed permutation =>
      exact .setPerm (included member) (typed.of_terms_subset included) permutation
  | setDedup member typed => exact .setDedup (included member) (typed.of_terms_subset included)
  | flatten algebraRule flattens sorted =>
      obtain ⟨free, bound, typed⟩ := sorted
      exact .flatten (algebraRule_mono included algebraRule) flattens ⟨free, bound, typed.of_terms_subset included⟩
  | singleton algebraRule flattens sorted =>
      obtain ⟨free, bound, typed⟩ := sorted
      exact .singleton (algebraRule_mono included algebraRule) flattens ⟨free, bound, typed.of_terms_subset included⟩
  | unitElim algebraRule unitIs sorted =>
      obtain ⟨free, bound, typed⟩ := sorted
      exact .unitElim (algebraRule_mono included algebraRule) unitIs ⟨free, bound, typed.of_terms_subset included⟩
  | emptyUnit algebraRule unitIs sorted =>
      obtain ⟨free, bound, typed⟩ := sorted
      exact .emptyUnit (algebraRule_mono included algebraRule) unitIs ⟨free, bound, typed.of_terms_subset included⟩

/-- **A generator in a context is one of every language with the grammar and the laws**, the laws without
premises. -/
theorem step_mono (included : first.terms ⊆ second.terms)
    (laws : ∀ equation ∈ first.equations, equation ∈ second.equations)
    (premises : ∀ equation ∈ first.equations, equation.premises = []) {base : BasePremiseEvaluator}
    {source target : Pattern} (step : EquationContextStep base first source target) :
    EquationContextStep base second source target := by
  cases step with
  | inContext context generator =>
      refine .inContext context ?_
      rcases generator with ⟨fuel, equationInstance⟩ | derived
      · exact .inl ⟨fuel, equationInstanceAt_mono laws premises equationInstance⟩
      · exact .inr (derived_mono included derived)

variable {free : FreeTypeContext} {bound : List TypeExpr} {sort : TypeExpr}

/-- **A chain of laws is one of every language with the grammar and the laws.** -/
theorem sortedEquiv_mono (included : first.terms ⊆ second.terms)
    (laws : ∀ equation ∈ first.equations, equation ∈ second.equations)
    (premises : ∀ equation ∈ first.equations, equation.premises = []) {source target : Pattern}
    (equivalent : SortedEquiv first free bound sort source target) : SortedEquiv second free bound sort source target :=
  Relation.EqvGen.mono (fun _ _ step => ⟨step_mono included laws premises step.step,
    step.firstTyped.of_terms_subset included, step.secondTyped.of_terms_subset included⟩) _ _ equivalent

theorem objectChain_mono (included : first.terms ⊆ second.terms)
    (laws : ∀ equation ∈ first.equations, equation ∈ second.equations)
    (premises : ∀ equation ∈ first.equations, equation.premises = []) {source target : Pattern}
    (chain : ObjectChain first free bound sort source target) : ObjectChain second free bound sort source target :=
  Relation.EqvGen.mono (fun _ _ step => ⟨⟨step_mono included laws premises step.1.step,
    step.1.firstTyped.of_terms_subset included, step.1.secondTyped.of_terms_subset included⟩, step.2⟩) _ _ chain

end Mono

namespace TermExtension

variable {small large : LanguageDef} {added : List String}

theorem mem_of_label (extension : TermExtension small large added) {rule : GrammarRule}
    (member : rule ∈ large.terms) (notAdded : rule.label ∉ added) : rule ∈ small.terms := by
  by_contra outside
  exact notAdded (extension.labelled rule member outside)

theorem mem_of_mentions (extension : TermExtension small large added) {rule : GrammarRule}
    (member : rule ∈ large.terms) {parameter : TermParam} (present : parameter ∈ rule.params) {kind : CollType}
    (mentions : parameter.typeExpr.mentionsCollection kind = true) : rule ∈ small.terms := by
  by_contra outside
  rw [extension.noCollections rule member outside parameter present kind] at mentions
  cases mentions

theorem mem_of_collection (extension : TermExtension small large added) {rule : GrammarRule}
    (member : rule ∈ large.terms) {name : String} {kind : CollType} {elementType : TypeExpr}
    (present : TermParam.simple name (.collection kind elementType) ∈ rule.params) : rule ∈ small.terms :=
  extension.mem_of_mentions member present (kind := kind) (by simp [TermParam.typeExpr, TypeExpr.mentionsCollection])

theorem mem_of_bare (extension : TermExtension small large added) {rule : GrammarRule}
    (member : rule ∈ large.terms) {name : String} {kind : CollType} {elementType : TypeExpr}
    (shape : rule.bareParams = [.simple name (.collection kind elementType)]) : rule ∈ small.terms := by
  apply extension.mem_of_collection member (name := name) (kind := kind) (elementType := elementType)
  unfold GrammarRule.bareParams at shape
  split at shape
  · rw [shape]
    exact List.mem_singleton_self _
  · simp at shape

/-! ### Typing -/

mutual
/-- **A term of the larger language that avoids the added constructors is a term of the smaller language.** -/
theorem typed_restrict (extension : TermExtension small large added) {free : FreeTypeContext}
    {bound : List TypeExpr} {pattern : Pattern} {type : TypeExpr} (typed : HasType large free bound pattern type)
    (avoiding : avoids added pattern = true) : HasType small free bound pattern type := by
  cases typed with
  | bvar found => exact .bvar found
  | fvar found => exact .fvar found
  | constructor declared notBare arguments =>
      rw [avoids_apply] at avoiding
      exact .constructor (extension.mem_of_label declared avoiding.1) notBare
        (arguments_restrict extension arguments avoiding.2)
  | lambda body =>
      rw [avoids_lambda] at avoiding
      exact .lambda (typed_restrict extension body avoiding)
  | multiLambda body =>
      rw [avoids_multiLambda] at avoiding
      exact .multiLambda (typed_restrict extension body avoiding)
  | subst body replacement =>
      rw [avoids_subst] at avoiding
      exact .subst (typed_restrict extension body avoiding.1) (typed_restrict extension replacement avoiding.2)
  | collection elements =>
      rw [avoids_collection] at avoiding
      exact .collection (elements_restrict extension elements avoiding)
  | collectionConstructor declared shape elements =>
      rw [avoids_collection] at avoiding
      exact .collectionConstructor (extension.mem_of_bare declared shape) shape
        (elements_restrict extension elements avoiding)
termination_by sizeOf pattern

theorem arguments_restrict (extension : TermExtension small large added) {free : FreeTypeContext}
    {bound : List TypeExpr} {patterns : List Pattern} {parameters : List TermParam}
    (typed : ArgumentsHaveTypes large free bound patterns parameters)
    (avoiding : ∀ pattern ∈ patterns, avoids added pattern = true) :
    ArgumentsHaveTypes small free bound patterns parameters := by
  cases typed with
  | nil => exact .nil
  | cons representation expected head tail =>
      exact .cons representation expected (typed_restrict extension head (avoiding _ List.mem_cons_self))
        (arguments_restrict extension tail fun pattern member => avoiding pattern (List.mem_cons_of_mem _ member))
termination_by sizeOf patterns

theorem elements_restrict (extension : TermExtension small large added) {free : FreeTypeContext}
    {bound : List TypeExpr} {patterns : List Pattern} {type : TypeExpr}
    (typed : ElementsHaveType large free bound patterns type)
    (avoiding : ∀ pattern ∈ patterns, avoids added pattern = true) :
    ElementsHaveType small free bound patterns type := by
  cases typed with
  | nil => exact .nil _ _
  | cons head tail =>
      exact .cons (typed_restrict extension head (avoiding _ List.mem_cons_self))
        (elements_restrict extension tail fun pattern member => avoiding pattern (List.mem_cons_of_mem _ member))
termination_by sizeOf patterns
end

mutual
/-- **A term of the smaller language avoids the added constructors.** -/
theorem avoids_of_typed (extension : TermExtension small large added) {free : FreeTypeContext}
    {bound : List TypeExpr} {pattern : Pattern} {type : TypeExpr} (typed : HasType small free bound pattern type) :
    avoids added pattern = true := by
  cases typed with
  | bvar => exact avoids_bvar _
  | fvar => exact avoids_fvar _
  | constructor declared _ arguments =>
      exact avoids_apply.mpr ⟨(extension.apart _ declared).1, avoidsList_iff.mp (arguments_avoid extension arguments)⟩
  | lambda body =>
      rw [avoids_lambda]
      exact avoids_of_typed extension body
  | multiLambda body =>
      rw [avoids_multiLambda]
      exact avoids_of_typed extension body
  | subst body replacement => exact avoids_subst.mpr ⟨avoids_of_typed extension body, avoids_of_typed extension replacement⟩
  | collection elements => exact avoids_collection.mpr (avoidsList_iff.mp (elements_avoid extension elements))
  | collectionConstructor _ _ elements =>
      exact avoids_collection.mpr (avoidsList_iff.mp (elements_avoid extension elements))
termination_by sizeOf pattern

theorem arguments_avoid (extension : TermExtension small large added) {free : FreeTypeContext}
    {bound : List TypeExpr} {patterns : List Pattern} {parameters : List TermParam}
    (typed : ArgumentsHaveTypes small free bound patterns parameters) : avoidsList added patterns = true := by
  cases typed with
  | nil => simp [avoidsList]
  | cons _ _ head tail =>
      simp only [avoidsList, Bool.and_eq_true]
      exact ⟨avoids_of_typed extension head, arguments_avoid extension tail⟩
termination_by sizeOf patterns

theorem elements_avoid (extension : TermExtension small large added) {free : FreeTypeContext}
    {bound : List TypeExpr} {patterns : List Pattern} {type : TypeExpr}
    (typed : ElementsHaveType small free bound patterns type) : avoidsList added patterns = true := by
  cases typed with
  | nil => simp [avoidsList]
  | cons head tail =>
      simp only [avoidsList, Bool.and_eq_true]
      exact ⟨avoids_of_typed extension head, elements_avoid extension tail⟩
termination_by sizeOf patterns
end

/-- **Typed in the smaller language exactly when typed in the larger one and avoiding the added constructors.** -/
theorem typed_iff (extension : TermExtension small large added) {free : FreeTypeContext} {bound : List TypeExpr}
    {pattern : Pattern} {type : TypeExpr} :
    HasType small free bound pattern type ↔ HasType large free bound pattern type ∧ avoids added pattern = true :=
  ⟨fun typed => ⟨typed.of_terms_subset extension.terms, extension.avoids_of_typed typed⟩,
    fun ⟨typed, avoiding⟩ => extension.typed_restrict typed avoiding⟩

/-! ### Generators -/

theorem sortedAt_restrict (extension : TermExtension small large added) {pattern : Pattern} {category : String}
    (sorted : SortedAt large pattern category) (avoiding : avoids added pattern = true) :
    SortedAt small pattern category := by
  obtain ⟨free, bound, typed⟩ := sorted
  exact ⟨free, bound, extension.typed_restrict typed avoiding⟩

theorem collectionTypedAt_restrict (extension : TermExtension small large added) {rule : GrammarRule}
    {kind : CollType} {elements : List Pattern} (typed : CollectionTypedAt large rule kind elements)
    (avoiding : avoids added (.collection kind elements none) = true) : CollectionTypedAt small rule kind elements := by
  obtain ⟨parameter, present, elementType, occurs, free, bound, typed⟩ := typed
  exact ⟨parameter, present, elementType, occurs, free, bound, extension.typed_restrict typed avoiding⟩

theorem mem_of_collectionTypedAt (extension : TermExtension small large added) {rule : GrammarRule}
    (member : rule ∈ large.terms) {kind : CollType} {elements : List Pattern}
    (typed : CollectionTypedAt large rule kind elements) : rule ∈ small.terms := by
  obtain ⟨parameter, present, mentions⟩ := typed.mentions
  exact extension.mem_of_mentions member present mentions

theorem algebraRule_restrict (extension : TermExtension small large added) {rule : GrammarRule} {kind : CollType}
    {algebra : CollectionAlgebra} (algebraRule : AlgebraRule large rule kind algebra) :
    AlgebraRule small rule kind algebra := by
  obtain ⟨parameterName, shape⟩ := algebraRule.selfSorted
  have member : rule ∈ small.terms :=
    extension.mem_of_collection algebraRule.authored (name := parameterName) (by rw [shape]; exact List.mem_singleton_self _)
  refine ⟨member, algebraRule.declared, algebraRule.selfSorted, fun unit unitIs => ?_⟩
  obtain ⟨unitRule, unitMember, labelIs, categoryIs, noParameters⟩ := algebraRule.unitAuthored unit unitIs
  have notAdded : unitRule.label ∉ added := by
    rw [labelIs]
    exact (extension.apart rule member).2 algebra algebraRule.declared unit unitIs
  exact ⟨unitRule, extension.mem_of_label unitMember notAdded, labelIs, categoryIs, noParameters⟩

/-- **A law of the larger language's bags from a term that avoids the added constructors is one of the smaller.** -/
theorem derived_restrict (extension : TermExtension small large added) {source target : Pattern}
    (derived : DerivedInstance large source target) (avoiding : avoids added source = true) :
    DerivedInstance small source target := by
  cases derived with
  | bagPerm member typed permutation =>
      exact .bagPerm (extension.mem_of_collectionTypedAt member typed) (extension.collectionTypedAt_restrict typed avoiding)
        permutation
  | setPerm member typed permutation =>
      exact .setPerm (extension.mem_of_collectionTypedAt member typed) (extension.collectionTypedAt_restrict typed avoiding)
        permutation
  | setDedup member typed =>
      exact .setDedup (extension.mem_of_collectionTypedAt member typed) (extension.collectionTypedAt_restrict typed avoiding)
  | flatten algebraRule flattens sorted =>
      exact .flatten (extension.algebraRule_restrict algebraRule) flattens (extension.sortedAt_restrict sorted avoiding)
  | singleton algebraRule flattens sorted =>
      exact .singleton (extension.algebraRule_restrict algebraRule) flattens (extension.sortedAt_restrict sorted avoiding)
  | unitElim algebraRule unitIs sorted =>
      exact .unitElim (extension.algebraRule_restrict algebraRule) unitIs (extension.sortedAt_restrict sorted avoiding)
  | emptyUnit algebraRule unitIs sorted =>
      exact .emptyUnit (extension.algebraRule_restrict algebraRule) unitIs (extension.sortedAt_restrict sorted avoiding)

theorem smallPremises (extension : TermExtension small large added) :
    ∀ equation ∈ small.equations, equation.premises = [] := by
  rw [extension.equations]
  exact extension.premises

/-- **A generator of the larger language in a context, from a term that avoids the added constructors, is one of the
smaller.** -/
theorem step_restrict (extension : TermExtension small large added) {base : BasePremiseEvaluator}
    {first second : Pattern} (step : EquationContextStep base large first second)
    (avoiding : avoids added first = true) : EquationContextStep base small first second := by
  cases step with
  | inContext context generator =>
      refine .inContext context ?_
      rcases generator with ⟨fuel, equationInstance⟩ | derived
      · exact .inl ⟨fuel, equationInstanceAt_mono (fun _ member => extension.equations ▸ member) extension.premises
          equationInstance⟩
      · exact .inr (extension.derived_restrict derived (avoids_of_fill context avoiding))

/-- **A generator of the smaller language in a context is one of the larger.** -/
theorem step_extend (extension : TermExtension small large added) {base : BasePremiseEvaluator}
    {first second : Pattern} (step : EquationContextStep base small first second) :
    EquationContextStep base large first second :=
  step_mono extension.terms (fun _ member => extension.equations ▸ member) extension.smallPremises step

/-! ### Conservativity -/

variable {free : FreeTypeContext} {bound : List TypeExpr} {sort : TypeExpr}

/-- **Laws that keep the terms avoiding some labels keep them along a chain.** -/
theorem _root_.Mettapedia.GSLT.LanguageDef.RestrictionBlocks.SortedEquiv.avoids_iff {language : LanguageDef}
    (keeps : KeepsAvoiding (engineBasePremises RelationEnv.empty) language labels) {first second : Pattern}
    (equivalent : SortedEquiv language free bound sort first second) :
    avoids labels first = true ↔ avoids labels second = true := by
  induction equivalent with
  | rel _ _ step =>
      cases step.step with
      | inContext context generator => exact avoids_fill_iff context (keeps _ _ generator)
  | refl => exact Iff.rfl
  | symm _ _ _ same => exact same.symm
  | trans _ _ _ _ _ left right => exact left.trans right

/-- **The larger static theory extends the smaller one conservatively**: a chain of laws of the larger language from a
term that avoids the added constructors, when the laws keep such terms, is a chain of the smaller language. -/
theorem sortedEquiv_restrict (extension : TermExtension small large added)
    (keeps : KeepsAvoiding (engineBasePremises RelationEnv.empty) large added) {first second : Pattern}
    (equivalent : SortedEquiv large free bound sort first second) (avoiding : avoids added first = true) :
    SortedEquiv small free bound sort first second := by
  induction equivalent with
  | rel first second step =>
      have secondAvoiding := (SortedEquiv.avoids_iff keeps (.rel _ _ step)).mp avoiding
      exact .rel _ _ ⟨extension.step_restrict step.step avoiding, extension.typed_restrict step.firstTyped avoiding,
        extension.typed_restrict step.secondTyped secondAvoiding⟩
  | refl => exact .refl _
  | symm _ _ inner recurse => exact .symm _ _ (recurse ((SortedEquiv.avoids_iff keeps inner).mpr avoiding))
  | trans _ _ _ firstPart _ firstRecurse secondRecurse =>
      exact .trans _ _ _ (firstRecurse avoiding)
        (secondRecurse ((SortedEquiv.avoids_iff keeps firstPart).mp avoiding))

/-- **Every chain of laws of the smaller language is one of the larger.** -/
theorem sortedEquiv_extend (extension : TermExtension small large added) {first second : Pattern}
    (equivalent : SortedEquiv small free bound sort first second) : SortedEquiv large free bound sort first second :=
  sortedEquiv_mono extension.terms (fun _ member => extension.equations ▸ member) extension.smallPremises equivalent

/-- **Chains through object terms, conservatively**: as `sortedEquiv_restrict`, through object terms. -/
theorem objectChain_restrict (extension : TermExtension small large added)
    (keeps : KeepsAvoiding (engineBasePremises RelationEnv.empty) large added) {first second : Pattern}
    (chain : ObjectChain large free bound sort first second) (avoiding : avoids added first = true) :
    ObjectChain small free bound sort first second := by
  induction chain with
  | rel first second step =>
      have secondAvoiding := (SortedEquiv.avoids_iff keeps (.rel _ _ step.1)).mp avoiding
      exact .rel _ _ ⟨⟨extension.step_restrict step.1.step avoiding, extension.typed_restrict step.1.firstTyped avoiding,
        extension.typed_restrict step.1.secondTyped secondAvoiding⟩, step.2⟩
  | refl => exact .refl _
  | symm _ _ inner recurse =>
      exact .symm _ _ (recurse ((SortedEquiv.avoids_iff keeps (ObjectChain.toSortedEquiv inner)).mpr avoiding))
  | trans _ _ _ firstPart _ firstRecurse secondRecurse =>
      exact .trans _ _ _ (firstRecurse avoiding)
        (secondRecurse ((SortedEquiv.avoids_iff keeps (ObjectChain.toSortedEquiv firstPart)).mp avoiding))

theorem objectChain_extend (extension : TermExtension small large added) {first second : Pattern}
    (chain : ObjectChain small free bound sort first second) : ObjectChain large free bound sort first second :=
  objectChain_mono extension.terms (fun _ member => extension.equations ▸ member) extension.smallPremises chain

end TermExtension

end Mettapedia.GSLT.LanguageDef.RestrictionBlocks
