import Mettapedia.GSLT.LanguageDef.ModuleSource.Elaborate
import Mettapedia.Algebra.Collections.Folds
import Mettapedia.OSLF.MeTTaIL.CoreLanguageDef
import Mettapedia.OSLF.MeTTaIL.CanonicalBags

/-!
# Boundaries of collection-algebra extraction

Algebra extraction and normalization share the same constructor-uniqueness
test. When a collection kind has several constructors, the original equations
remain available; none is replaced by an unavailable normalizer law.

Binary associativity is not an unrestricted variadic flattening axiom. The
finite countermodel below distinguishes the two. Monoid folds do justify
variadic flattening, by the existing list-product laws. AlgebraInterpretation connects checked binary replacements to those models.
The lemmas below license deleted first-order equation instances against the
final collection-law relation through the extraction fold, under the finite
source signature conditions. They preserve the actual representation table.
They do not establish full source-theory reflection or firing coherence.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleSource

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.CollectionLaws

theorem uniqueCollectionKind_iff {language : LanguageDef} {rule : GrammarRule}
    {kind : CollType} (shape : bareKind rule = some kind) :
    uniqueCollectionKind language rule = true ↔
      (language.terms.filter fun other => bareKind other == some kind).length = 1 := by
  simp [uniqueCollectionKind, shape]

/-- Retaining source equations is structural: it holds for every language
whose collection kinds fail the executable uniqueness test, independently of
the equations' contents. -/
theorem declareAlgebras_eq_self_of_unavailable (language : LanguageDef) (binaryLabels : List String)
    (unavailable : ∀ rule ∈ language.terms,
      rule.algebra?.isSome = true ∨ uniqueCollectionKind language rule = false) :
    declareAlgebras language binaryLabels = language := by
  unfold declareAlgebras
  suffices ∀ (rules : List GrammarRule),
      (∀ rule ∈ rules, rule.algebra?.isSome = true ∨ uniqueCollectionKind language rule = false) →
      rules.foldl (extractAlgebra language binaryLabels) language = language by
    exact this language.terms unavailable
  intro rules
  induction rules with
  | nil => simp
  | cons rule rules ih =>
    intro unavailable
    have head := unavailable rule List.mem_cons_self
    have guard : (rule.algebra?.isSome || !uniqueCollectionKind language rule ||
        !binaryLabels.contains rule.label) = true := by
      rcases head with known | absent
      · simp [known]
      · simp [absent]
    simp only [List.foldl_cons, extractAlgebra, guard, ↓reduceIte]
    exact ih (fun other member => unavailable other (List.mem_cons_of_mem _ member))

/-- A literal variadic declaration keeps all equations. The recognizer does
not promote its binary associativity instances into unrestricted flattening. -/
theorem declareAlgebras_without_binary_origins (language : LanguageDef) :
    declareAlgebras language [] = language := by
  unfold declareAlgebras
  have unchanged (current : LanguageDef) (rules : List GrammarRule) :
      rules.foldl (extractAlgebra language []) current = current := by
    induction rules generalizing current with
    | nil => rfl
    | cons rule rules ih =>
      simpa only [List.foldl_cons, extractAlgebra, List.contains_nil, Bool.not_false,
        Bool.or_true, Bool.true_eq, ↓reduceIte] using ih current
  exact unchanged language language.terms

/-- The actual argument mapper for a binary-to-collection replacement. The
old argument order is retained; the collection's equality policy is separate. -/
theorem argumentMap_binary_collection (old new : GrammarRule)
    (first second elements sort : String) (kind : CollType)
    (before : old.params = [.simple first (.base sort), .simple second (.base sort)])
    (after : new.params = [.simple elements (.collection kind (.base sort))]) :
    argumentMap old new = some (fun arguments => [Pattern.collection kind arguments none]) := by
  simp [argumentMap, namedArguments?, before, after, paramName]

namespace AlgebraExtractionControls

def bagConstructor (label sort : String) : GrammarRule :=
  { label, category := sort,
    params := [.simple "elements" (.collection .hashBag (.base sort))], syntaxPattern := [] }

def bagApplication (label : String) (elements : List Pattern) : Pattern :=
  .apply label [.collection .hashBag elements none]

def associativity (label : String) : Equation :=
  { name := label ++ ":associativity", typeContext := [], premises := [],
    left := bagApplication label
      [bagApplication label [.fvar "x", .fvar "y"], .fvar "z"],
    right := bagApplication label
      [.fvar "x", bagApplication label [.fvar "y", .fvar "z"]] }

def twoBagSorts : LanguageDef :=
  { name := "TwoBagSorts", types := [TypeDecl.plain "A", TypeDecl.plain "B"],
    terms := [bagConstructor "First" "A", bagConstructor "Second" "B"],
    equations := [associativity "First", associativity "Second"], rewrites := [] }

theorem ambiguous_algebras_retained :
    declareAlgebras twoBagSorts ["First", "Second"] = twoBagSorts := by
  apply declareAlgebras_eq_self_of_unavailable
  intro rule member
  simp only [twoBagSorts, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl <;> exact .inr (by decide)

theorem ambiguous_equations_retained :
    (declareAlgebras twoBagSorts ["First", "Second"]).equations =
      [associativity "First", associativity "Second"] := by
  rw [ambiguous_algebras_retained]
  rfl

theorem ambiguous_normalizer_has_no_laws :
    declared (declareAlgebras twoBagSorts ["First", "Second"]) = [] := by
  rw [ambiguous_algebras_retained]
  decide

/-- A symmetric variadic operation whose binary operation is Boolean join.
Its ternary operation is independent of that binary operation. -/
def associativeBinaryOnly (elements : List Bool) : Bool :=
  if elements.length = 3 then true else elements.any id

theorem binary_associativity (x y z : Bool) :
    associativeBinaryOnly [associativeBinaryOnly [x, y], z] =
      associativeBinaryOnly [x, associativeBinaryOnly [y, z]] := by
  cases x <;> cases y <;> cases z <;> decide

theorem binary_commutativity (x y : Bool) :
    associativeBinaryOnly [x, y] = associativeBinaryOnly [y, x] := by
  cases x <;> cases y <;> decide

theorem variadic_flattening_not_entailed :
    associativeBinaryOnly [associativeBinaryOnly [false, false], false] ≠
      associativeBinaryOnly [false, false, false] := by decide

theorem recognized_binary_associativity :
    (statedAlgebra [associativity "First"] (bagConstructor "First" "A")).map
      (fun result => result.1) = some { flatten := true, unit := none } := by decide

/-- Genuine fold interpretations implement splicing at arbitrary arities. -/
theorem monoid_fold_splice {A : Type} [Monoid A]
    (before middle after : List A) :
    (before ++ middle.prod :: after).prod = (before ++ middle ++ after).prod := by
  simp [List.prod_append]

theorem monoid_fold_singleton {A : Type} [Monoid A] (value : A) :
    [value].prod = value := by simp

theorem monoid_fold_unit {A : Type} [Monoid A] (before after : List A) :
    (before ++ (1 : A) :: after).prod = (before ++ after).prod := by simp

end AlgebraExtractionControls
end Mettapedia.GSLT.LanguageDef.ModuleSource

namespace Mettapedia.GSLT.LanguageDef.ModuleSource.AlgebraExtractionSoundness

set_option maxHeartbeats 1600000

open Mettapedia.OSLF.MeTTaIL Syntax CoreReduction CanonicalBags CollectionLaws Match

theorem elementsUnder_shape {label : String} {pattern : Pattern} {elements : List Pattern}
    (found : elementsUnder label pattern = some elements) :
    ∃ kind, pattern = .apply label [.collection kind elements none] := by
  unfold elementsUnder at found
  split at found
  next head kind actual =>
    split at found
    next selected =>
      have same : head = label := beq_iff_eq.mp selected
      cases same
      cases Option.some.inj found
      exact ⟨kind, rfl⟩
    next => cases found
  next => cases found

theorem variableNames_shape {patterns : List Pattern} {names : List String}
    (found : variableNames patterns = some names) : patterns = names.map Pattern.fvar := by
  induction patterns generalizing names with
  | nil => simp only [variableNames, Option.some.injEq] at found; cases found; rfl
  | cons pattern patterns ih =>
      cases pattern <;> simp only [variableNames] at found
      all_goals try cases found
      rename_i name
      cases tail : variableNames patterns with
      | none => simp [tail] at found
      | some rest =>
          have same : name :: rest = names := by simpa only [tail, Option.map_some,
            Option.some.injEq] using found
          subst names
          rw [ih tail]
          rfl

theorem unwrap_elementsUnder {bare : List (String × CollType)} {label : String}
    {kind : CollType} {pattern : Pattern} {elements : List Pattern}
    (selected : bare.lookup label = some kind)
    (found : elementsUnder label pattern = some elements) :
    unwrap bare pattern = .collection kind (elements.map (unwrap bare)) none := by
  obtain ⟨actual, rfl⟩ := elementsUnder_shape found
  simp [unwrap, selected]

theorem elementsUnder_bound (bindings : Bindings) {label : String} {pattern : Pattern}
    {elements : List Pattern} (found : elementsUnder label pattern = some elements) :
    elementsUnder label (applyBindings bindings pattern) = some (elements.map (applyBindings bindings)) := by
  obtain ⟨kind, rfl⟩ := elementsUnder_shape found
  simp [applyBindings, elementsUnder]

theorem unwrap_bound_elementsUnder (bindings : Bindings)
    {bare : List (String × CollType)} {label : String} {kind : CollType}
    {pattern : Pattern} {elements : List Pattern}
    (selected : bare.lookup label = some kind)
    (found : elementsUnder label pattern = some elements) :
    unwrap bare (applyBindings bindings pattern) =
      .collection kind (elements.map (fun pattern => unwrap bare (applyBindings bindings pattern))) none := by
  rw [unwrap_elementsUnder selected (elementsUnder_bound bindings found)]
  simp only [List.map_map, Function.comp_def]

theorem normalize_named (laws : List Laws) (kind : CollType) (names : List String) :
    normalize laws (.collection kind (names.map Pattern.fvar) none) =
      .collection kind (names.map Pattern.fvar) none := by
  rw [normalize_collection]
  split
  · rename_i law found
    simp only [List.map_map, Function.comp_def, normalize]
    have spliced : (names.map Pattern.fvar).flatMap (splice law) = names.map Pattern.fvar := by
      induction names with
      | nil => rfl
      | cons name names ih => simp [splice, ih]
    exact congrArg (fun values => Pattern.collection kind values none) spliced
  · simp [List.map_map, normalize]

theorem threeShape_lawNormal (bindings : Bindings) {bare : List (String × CollType)} {label : String}
    {kind : CollType} {laws : List Laws} {law : Laws} {pattern : Pattern}
    {shape : Nat} {names : List String}
    (selected : bare.lookup label = some kind)
    (declared : lawFor laws kind = some law)
    (found : threeShape label pattern = some (shape, names)) :
    lawNormal laws (unwrap bare (applyBindings bindings pattern)) =
      lawNormal laws (.collection kind (names.map (fun name => unwrap bare (applyBindings bindings (.fvar name)))) none) := by
  unfold threeShape at found
  split at found
  next inner z outer =>
    split at found
    next x y innerFound =>
      obtain ⟨elements, innerParts, named⟩ := Option.bind_eq_some_iff.mp innerFound
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj found)
      rw [unwrap_bound_elementsUnder bindings selected outer]
      simp only [List.map_cons, List.map_nil]
      rw [unwrap_bound_elementsUnder bindings selected innerParts, variableNames_shape named]
      simpa only [List.map_cons, List.map_nil, List.nil_append, List.cons_append, List.append_nil] using
        (LawStep.flatten (law := law) (before := []) (inner := [unwrap bare (applyBindings bindings (.fvar x)), unwrap bare (applyBindings bindings (.fvar y))])
          (after := [unwrap bare (applyBindings bindings (.fvar z))]) (rest := none) declared).lawNormal_eq laws
    next => cases found
  next x inner notVariable outer =>
    split at found
    next y z innerFound =>
      obtain ⟨elements, innerParts, named⟩ := Option.bind_eq_some_iff.mp innerFound
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj found)
      rw [unwrap_bound_elementsUnder bindings selected outer]
      simp only [List.map_cons, List.map_nil]
      rw [unwrap_bound_elementsUnder bindings selected innerParts, variableNames_shape named]
      simpa only [List.map_cons, List.map_nil, List.nil_append, List.cons_append, List.append_nil] using
        (LawStep.flatten (law := law) (before := [unwrap bare (applyBindings bindings (.fvar x))]) (inner := [unwrap bare (applyBindings bindings (.fvar y)), unwrap bare (applyBindings bindings (.fvar z))])
          (after := []) (rest := none) declared).lawNormal_eq laws
    next => cases found
  next elements notLeft notRight outer =>
    split at found
    next x y z named =>
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj found)
      rw [unwrap_bound_elementsUnder bindings selected outer, variableNames_shape named]
      simp only [List.map_cons, List.map_nil]
    next => cases found
  next => cases found

theorem statesFlatten_lawNormal (bindings : Bindings) {bare : List (String × CollType)} {label : String}
    {kind : CollType} {laws : List Laws} {law : Laws} {left right : Pattern}
    (selected : bare.lookup label = some kind)
    (declared : lawFor laws kind = some law)
    (recognized : statesFlatten label left right = true) :
    lawNormal laws (unwrap bare (applyBindings bindings left)) =
      lawNormal laws (unwrap bare (applyBindings bindings right)) := by
  cases leftShape : threeShape label left with
  | none => simp [statesFlatten, leftShape] at recognized
  | some first =>
    cases rightShape : threeShape label right with
    | none => simp [statesFlatten, rightShape] at recognized
    | some second =>
      rcases first with ⟨first, names⟩
      rcases second with ⟨second, others⟩
      simp only [statesFlatten, leftShape, rightShape, Bool.and_eq_true,
        beq_iff_eq] at recognized
      have same : names = others := recognized.1.2
      have leftNormal := threeShape_lawNormal bindings selected declared leftShape
      have rightNormal := threeShape_lawNormal bindings selected declared rightShape
      rw [← same] at rightNormal
      exact leftNormal.trans rightNormal.symm

theorem statesCommuting_lawNormal (bindings : Bindings) {bare : List (String × CollType)} {label : String}
    {kind : CollType} {laws : List Laws} {left right : Pattern}
    (selected : bare.lookup label = some kind)
    (unordered : Unordered kind = true)
    (recognized : statesCommuting label left right = true) :
    lawNormal laws (unwrap bare (applyBindings bindings left)) =
      lawNormal laws (unwrap bare (applyBindings bindings right)) := by
  unfold statesCommuting at recognized
  split at recognized
  next x y otherY otherX leftParts rightParts =>
    simp only [Bool.and_eq_true, beq_iff_eq] at recognized
    obtain ⟨⟨_, rfl⟩, rfl⟩ := recognized
    rw [unwrap_bound_elementsUnder bindings selected leftParts, unwrap_bound_elementsUnder bindings selected rightParts]
    simpa only [List.map_cons, List.map_nil] using
      (LawStep.permute (laws := laws) (rest := none) unordered
        (List.Perm.swap (unwrap bare (applyBindings bindings (.fvar x))) (unwrap bare (applyBindings bindings (.fvar y))) [])).lawNormal_eq laws |>.symm
  next => contradiction

theorem statedAlgebra_replaced {equations : List Equation} {rule : GrammarRule}
    {kind : CollType} {algebra : CollectionAlgebra} {replaced : Equation → Bool}
    (shape : ownKind rule = some kind)
    (found : statedAlgebra equations rule = some (algebra, replaced)) (row : Equation) :
    replaced row = (row.premises.isEmpty &&
      (eitherWay (statesFlatten rule.label) row ||
        (Unordered kind && eitherWay (statesCommuting rule.label) row))) := by
  have projected := congrArg (fun result => result.map Prod.snd) found
  cases tested : (equations.filter (·.premises.isEmpty)).any
      (eitherWay (statesFlatten rule.label)) with
  | false =>
      simp [statedAlgebra, shape, tested, guard, Option.bind_eq_bind] at projected
  | true =>
      have predicates : (fun entry : Equation => entry.premises.isEmpty &&
          (eitherWay (statesFlatten rule.label) entry ||
            ((kind == .hashBag || kind == .hashSet) &&
              eitherWay (statesCommuting rule.label) entry))) = replaced := by
        simpa [statedAlgebra, shape, tested, guard, Option.bind_eq_bind] using projected
      rw [← predicates]
      cases kind <;> rfl

theorem extraction_deletion_readout (language current : LanguageDef)
    (binaryLabels : List String) (rule : GrammarRule) (row : Equation)
    (member : row ∈ current.equations)
    (deleted : row ∉ (extractAlgebra language binaryLabels current rule).equations) :
    ∃ algebra replaced,
      statedAlgebra current.equations rule = some (algebra, replaced) ∧
      algebra.unit.isSome = true ∧ replaced row = true := by
  unfold extractAlgebra at deleted
  split at deleted
  · exact False.elim (deleted member)
  · split at deleted
    next algebra replaced found =>
      split at deleted
      next unitPresent =>
        refine ⟨algebra, replaced, found, unitPresent, ?_⟩
        have absent : (!replaced row) ≠ true := by
          intro kept
          exact deleted (List.mem_filter.mpr ⟨member, kept⟩)
        cases selected : replaced row
        · exact False.elim (absent (by simp [selected]))
        · rfl
      next => exact False.elim (deleted member)
    next => exact False.elim (deleted member)

theorem replaced_lawNormal (bindings : Bindings) {equations : List Equation} {rule : GrammarRule}
    {kind : CollType} {algebra : CollectionAlgebra} {replaced : Equation → Bool}
    {bare : List (String × CollType)} {laws : List Laws} {law : Laws} {row : Equation}
    (shape : ownKind rule = some kind)
    (found : statedAlgebra equations rule = some (algebra, replaced))
    (selected : bare.lookup rule.label = some kind)
    (declared : lawFor laws kind = some law) (removed : replaced row = true) :
    lawNormal laws (unwrap bare (applyBindings bindings row.left)) =
      lawNormal laws (unwrap bare (applyBindings bindings row.right)) := by
  rw [statedAlgebra_replaced shape found row] at removed
  simp only [Bool.and_eq_true, Bool.or_eq_true] at removed
  rcases removed.2 with flatten | commuting
  · simp only [eitherWay, Bool.or_eq_true] at flatten
    rcases flatten with forward | backward
    · exact statesFlatten_lawNormal bindings selected declared forward
    · exact (statesFlatten_lawNormal bindings selected declared backward).symm
  · rcases commuting with ⟨unordered, recognized⟩
    simp only [eitherWay, Bool.or_eq_true] at recognized
    rcases recognized with forward | backward
    · exact statesCommuting_lawNormal bindings selected unordered forward
    · exact (statesCommuting_lawNormal bindings selected unordered backward).symm

theorem extractAlgebra_deleted_lawNormal (language current : LanguageDef)
    (binaryLabels : List String) (rule : GrammarRule) (row : Equation)
    (kind : CollType) (law : Laws) (bindings : Bindings)
    (shape : ownKind rule = some kind)
    (represented : (bareLabels (extractAlgebra language binaryLabels current rule)).lookup
      rule.label = some kind)
    (declared : lawFor (CollectionLaws.declared (extractAlgebra language binaryLabels current rule))
      kind = some law)
    (member : row ∈ current.equations)
    (deleted : row ∉ (extractAlgebra language binaryLabels current rule).equations) :
    Relation.EqvGen (LawStep (CollectionLaws.declared (extractAlgebra language binaryLabels current rule)))
      (unwrap (bareLabels (extractAlgebra language binaryLabels current rule)) (applyBindings bindings row.left))
      (unwrap (bareLabels (extractAlgebra language binaryLabels current rule)) (applyBindings bindings row.right)) := by
  obtain ⟨algebra, replaced, found, _, removed⟩ :=
    extraction_deletion_readout language current binaryLabels rule row member deleted
  exact (lawNormal_iff _ _ _).mp (replaced_lawNormal bindings shape found represented declared removed)

theorem lawNormal_collection_ne_variable (laws : List Laws) (kind : CollType)
    (elements : List Pattern) (rest : Option String) (name : String) :
    lawNormal laws (.collection kind elements rest) ≠ lawNormal laws (.fvar name) := by
  unfold lawNormal
  rw [normalize_collection]
  split <;> simp only [canon, normalize, ne_eq, reduceCtorEq, not_false_eq_true]

theorem lawNormal_distinguishes_named (laws : List Laws) (bare : List (String × CollType))
    (first second : String) (arguments others : List Pattern)
    (firstNamed : bare.lookup first = none) (secondNamed : bare.lookup second = none)
    (different : first ≠ second) :
    lawNormal laws (unwrap bare (.apply first arguments)) ≠
      lawNormal laws (unwrap bare (.apply second others)) := by
  simp only [unwrap, firstNamed, secondNamed, lawNormal, normalize, canon]
  intro same
  exact different (Pattern.apply.inj same).1

theorem extractAlgebra_bareLabels (language current : LanguageDef)
    (binaryLabels : List String) (rule : GrammarRule) :
    bareLabels (extractAlgebra language binaryLabels current rule) = bareLabels current := by
  unfold extractAlgebra
  split
  · rfl
  · split
    next algebra replaced found =>
      split
      · simp only [bareLabels, List.filterMap_map]
        apply List.filterMap_congr
        intro declaration _
        dsimp only [Function.comp_def]
        cases named : (declaration.label == rule.label) <;> rfl
      · rfl
    next => rfl

theorem declareAlgebras_bareLabels (language : LanguageDef) (binaryLabels : List String) :
    bareLabels (declareAlgebras language binaryLabels) = bareLabels language := by
  unfold declareAlgebras
  suffices ∀ (rules : List GrammarRule) (current : LanguageDef),
      bareLabels (rules.foldl (extractAlgebra language binaryLabels) current) = bareLabels current by
    exact this language.terms language
  intro rules
  induction rules with
  | nil => intro current; rfl
  | cons rule rules ih =>
      intro current
      rw [List.foldl_cons, ih, extractAlgebra_bareLabels]

theorem declareAlgebras_unwrap (language : LanguageDef) (binaryLabels : List String)
    (pattern : Pattern) :
    unwrap (bareLabels (declareAlgebras language binaryLabels)) pattern =
      unwrap (bareLabels language) pattern := by
  rw [declareAlgebras_bareLabels]

theorem declared_lookup {language : LanguageDef} {kind : CollType} {rule : GrammarRule}
    {unit : Option String}
    (single : language.terms.filter (fun other => bareKind other == some kind) = [rule])
    (algebra : rule.algebra? = some ⟨true, unit⟩) :
    lawFor (CollectionLaws.declared language) kind = some ⟨kind, unit⟩ := by
  cases kind <;>
    simp only [CollectionLaws.declared, List.filterMap_cons, List.filterMap_nil,
      single, algebra, ↓reduceIte, lawFor]
  all_goals try rfl
  all_goals repeat' first
    | (solve | simp_all [List.find?_cons])
    | split at *
  all_goals simp_all only [Option.some.injEq]
  all_goals subst_vars
  all_goals simp

theorem statedAlgebra_kind {equations : List Equation} {rule : GrammarRule}
    {algebra : CollectionAlgebra} {replaced : Equation → Bool}
    (found : statedAlgebra equations rule = some (algebra, replaced)) :
    ∃ kind, ownKind rule = some kind := by
  cases shape : ownKind rule with
  | none => simp [statedAlgebra, shape] at found
  | some kind => exact ⟨kind, rfl⟩

theorem extractAlgebra_conditional_retained (language current : LanguageDef)
    (binaryLabels : List String) (rule : GrammarRule) (row : Equation)
    (member : row ∈ current.equations) (conditional : row.premises ≠ []) :
    row ∈ (extractAlgebra language binaryLabels current rule).equations := by
  by_contra deleted
  obtain ⟨algebra, replaced, found, _, removed⟩ :=
    extraction_deletion_readout language current binaryLabels rule row member deleted
  obtain ⟨kind, shape⟩ := statedAlgebra_kind found
  rw [statedAlgebra_replaced shape found row] at removed
  have empty := (Bool.and_eq_true_iff.mp removed).1
  exact conditional (List.isEmpty_iff.mp empty)

theorem extractAlgebra_variable_endpoint_retained (language current : LanguageDef)
    (binaryLabels : List String) (rule : GrammarRule) (row : Equation)
    (member : row ∈ current.equations)
    (variableEndpoint : ∃ name, row.left = .fvar name ∨ row.right = .fvar name) :
    row ∈ (extractAlgebra language binaryLabels current rule).equations := by
  by_contra deleted
  obtain ⟨algebra, replaced, found, _, removed⟩ :=
    extraction_deletion_readout language current binaryLabels rule row member deleted
  obtain ⟨kind, shape⟩ := statedAlgebra_kind found
  rw [statedAlgebra_replaced shape found row] at removed
  obtain ⟨name, left | right⟩ := variableEndpoint
  · simp [left, eitherWay, statesFlatten, threeShape, elementsUnder, statesCommuting] at removed
  · simp [right, eitherWay, statesFlatten, threeShape, elementsUnder, statesCommuting] at removed

theorem declared_unit_control :
    lawNormal [⟨.vec, some "One"⟩]
      (.collection .vec [.fvar "x", .apply "One" []] none) =
      .collection .vec [.fvar "x"] none := by cbv

theorem wrong_unit_control :
    ¬ Relation.EqvGen (LawStep [⟨.vec, some "One"⟩])
      (.collection .vec [.fvar "x", .apply "Other" []] none)
      (.collection .vec [.fvar "x"] none) := by
  intro related
  have same := (lawNormal_iff _ _ _).mpr related
  have different : lawNormal [⟨.vec, some "One"⟩]
      (.collection .vec [.fvar "x", .apply "Other" []] none) ≠
      lawNormal [⟨.vec, some "One"⟩] (.collection .vec [.fvar "x"] none) := by
    have left : lawNormal [⟨.vec, some "One"⟩]
        (.collection .vec [.fvar "x", .apply "Other" []] none) =
        .collection .vec [.fvar "x", .apply "Other" []] none := by cbv
    have right : lawNormal [⟨.vec, some "One"⟩] (.collection .vec [.fvar "x"] none) =
        .collection .vec [.fvar "x"] none := by cbv
    rw [left, right]
    intro equal
    have lengths := congrArg (fun pattern => match pattern with
      | .collection _ elements _ => elements.length
      | _ => 0) equal
    cases lengths
  exact different same

theorem cross_constructor_not_equivalent (laws : List Laws) (bare : List (String × CollType))
    (first second : String) (arguments others : List Pattern)
    (firstNamed : bare.lookup first = none) (secondNamed : bare.lookup second = none)
    (different : first ≠ second) :
    ¬ Relation.EqvGen (LawStep laws) (unwrap bare (.apply first arguments))
      (unwrap bare (.apply second others)) := by
  intro related
  exact lawNormal_distinguishes_named laws bare first second arguments others
    firstNamed secondNamed different ((lawNormal_iff _ _ _).mpr related)

theorem ownKind_bare {rule : GrammarRule} {kind : CollType}
    (shape : ownKind rule = some kind) : bareKind rule = some kind := by
  unfold ownKind at shape
  split at shape
  next name actual element parameterShape =>
    split at shape
    · cases Option.some.inj shape
      simp [bareKind, parameterShape]
    · cases shape
  next => cases shape

theorem statedAlgebra_flatten {equations : List Equation} {rule : GrammarRule}
    {kind : CollType} {algebra : CollectionAlgebra} {replaced : Equation → Bool}
    (shape : ownKind rule = some kind)
    (found : statedAlgebra equations rule = some (algebra, replaced)) :
    algebra.flatten = true := by
  have projected := congrArg (fun result => result.map (fun pair => pair.1.flatten)) found
  cases tested : (equations.filter (·.premises.isEmpty)).any
      (eitherWay (statesFlatten rule.label)) <;>
    simpa [statedAlgebra, shape, tested, guard, Option.bind_eq_bind] using projected.symm

theorem filter_algebra_update (language : LanguageDef) (label : String)
    (algebra : CollectionAlgebra) (kind : CollType) :
    (language.terms.map (fun rule => if rule.label == label then {rule with algebra? := some algebra} else rule)).filter
        (fun rule => bareKind rule == some kind) =
      (language.terms.filter (fun rule => bareKind rule == some kind)).map
        (fun rule => if rule.label == label then {rule with algebra? := some algebra} else rule) := by
  rw [List.filter_map]
  apply congrArg (List.map (fun rule : GrammarRule => if rule.label == label then
    {rule with algebra? := some algebra} else rule))
  apply List.filter_congr
  intro rule _
  dsimp only [Function.comp_def]
  cases selected : (rule.label == label) <;> rfl

theorem extractAlgebra_deleted_declares (language : LanguageDef) (binaryLabels : List String)
    (rule : GrammarRule) (row : Equation) (kind : CollType)
    (ruleMember : rule ∈ language.terms) (shape : ownKind rule = some kind)
    (member : row ∈ language.equations)
    (deleted : row ∉ (extractAlgebra language binaryLabels language rule).equations) :
    ∃ law, lawFor (CollectionLaws.declared (extractAlgebra language binaryLabels language rule))
      kind = some law := by
  obtain ⟨algebra, replaced, found, unitPresent, _⟩ :=
    extraction_deletion_readout language language binaryLabels rule row member deleted
  cases guarded : (rule.algebra?.isSome || !uniqueCollectionKind language rule ||
      !binaryLabels.contains rule.label) with
  | true =>
      exact False.elim (deleted (by simpa only [extractAlgebra, guarded, ↓reduceIte] using member))
  | false =>
      have unique : uniqueCollectionKind language rule = true := by
        cases tested : uniqueCollectionKind language rule
        · simp [tested] at guarded
        · rfl
      have bare := ownKind_bare shape
      have length := (uniqueCollectionKind_iff bare).mp unique
      obtain ⟨only, single⟩ := List.length_eq_one_iff.mp length
      have selectedMember : rule ∈ language.terms.filter (fun other => bareKind other == some kind) :=
        List.mem_filter.mpr ⟨ruleMember, by simp only [bare, beq_self_eq_true]⟩
      have selected : only = rule := by
        symm
        simpa only [single, List.mem_singleton] using selectedMember
      subst only
      have targetTerms : (extractAlgebra language binaryLabels language rule).terms =
          language.terms.map (fun other => if other.label == rule.label then
            {other with algebra? := some algebra} else other) := by
        simp only [extractAlgebra, guarded, Bool.false_eq_true, ↓reduceIte, found, unitPresent]
      have targetFilter :
          (extractAlgebra language binaryLabels language rule).terms.filter
              (fun other => bareKind other == some kind) = [{rule with algebra? := some algebra}] := by
        rw [targetTerms, filter_algebra_update, single]
        simp
      have flatten := statedAlgebra_flatten shape found
      have algebraEq : algebra = ⟨true, algebra.unit⟩ := by
        cases algebra with
        | mk flatten unit => simp_all
      refine ⟨⟨kind, algebra.unit⟩, ?_⟩
      apply declared_lookup targetFilter
      exact congrArg some algebraEq

theorem extractAlgebra_deleted_instances (language : LanguageDef) (binaryLabels : List String)
    (rule : GrammarRule) (row : Equation) (kind : CollType) (bindings : Bindings)
    (ruleMember : rule ∈ language.terms) (shape : ownKind rule = some kind)
    (represented : (bareLabels language).lookup rule.label = some kind)
    (member : row ∈ language.equations)
    (deleted : row ∉ (extractAlgebra language binaryLabels language rule).equations) :
    Relation.EqvGen (LawStep (CollectionLaws.declared (extractAlgebra language binaryLabels language rule)))
      (unwrap (bareLabels language) (applyBindings bindings row.left))
      (unwrap (bareLabels language) (applyBindings bindings row.right)) := by
  obtain ⟨law, declared⟩ := extractAlgebra_deleted_declares language binaryLabels rule row kind
    ruleMember shape member deleted
  have targetRepresented : (bareLabels (extractAlgebra language binaryLabels language rule)).lookup
      rule.label = some kind := by rw [extractAlgebra_bareLabels]; exact represented
  simpa only [extractAlgebra_bareLabels] using
    extractAlgebra_deleted_lawNormal language language binaryLabels rule row kind law bindings
      shape targetRepresented declared member deleted

theorem declareAlgebras_conditional_retained (language : LanguageDef)
    (binaryLabels : List String) (row : Equation)
    (member : row ∈ language.equations) (conditional : row.premises ≠ []) :
    row ∈ (declareAlgebras language binaryLabels).equations := by
  unfold declareAlgebras
  suffices ∀ (rules : List GrammarRule) (current : LanguageDef), row ∈ current.equations →
      row ∈ (rules.foldl (extractAlgebra language binaryLabels) current).equations by
    exact this language.terms language member
  intro rules
  induction rules with
  | nil => intro current member; exact member
  | cons rule rules ih =>
      intro current member
      exact ih _ (extractAlgebra_conditional_retained language current binaryLabels rule row member conditional)

theorem declareAlgebras_variable_endpoint_retained (language : LanguageDef)
    (binaryLabels : List String) (row : Equation)
    (member : row ∈ language.equations)
    (variableEndpoint : ∃ name, row.left = .fvar name ∨ row.right = .fvar name) :
    row ∈ (declareAlgebras language binaryLabels).equations := by
  unfold declareAlgebras
  suffices ∀ (rules : List GrammarRule) (current : LanguageDef), row ∈ current.equations →
      row ∈ (rules.foldl (extractAlgebra language binaryLabels) current).equations by
    exact this language.terms language member
  intro rules
  induction rules with
  | nil => intro current member; exact member
  | cons rule rules ih =>
      intro current member
      exact ih _ (extractAlgebra_variable_endpoint_retained language current binaryLabels rule row member variableEndpoint)

theorem extractAlgebra_equations_sublist (language current : LanguageDef)
    (binaryLabels : List String) (rule : GrammarRule) :
    (extractAlgebra language binaryLabels current rule).equations.Sublist current.equations := by
  unfold extractAlgebra
  split
  · exact .refl _
  · split
    next algebra replaced found =>
      split
      · exact List.filter_sublist
      · exact .refl _
    next => exact .refl _

theorem declareAlgebras_equations_sublist (language : LanguageDef)
    (binaryLabels : List String) :
    (declareAlgebras language binaryLabels).equations.Sublist language.equations := by
  unfold declareAlgebras
  suffices ∀ (rules : List GrammarRule) (current : LanguageDef),
      (rules.foldl (extractAlgebra language binaryLabels) current).equations.Sublist current.equations by
    exact this language.terms language
  intro rules
  induction rules with
  | nil => intro current; exact .refl _
  | cons rule rules ih =>
      intro current
      exact (ih _).trans (extractAlgebra_equations_sublist language current binaryLabels rule)


#print axioms elementsUnder_shape
#print axioms variableNames_shape
#print axioms unwrap_elementsUnder
#print axioms elementsUnder_bound
#print axioms unwrap_bound_elementsUnder
#print axioms normalize_named
#print axioms threeShape_lawNormal
#print axioms statesFlatten_lawNormal
#print axioms statesCommuting_lawNormal
#print axioms statedAlgebra_replaced
#print axioms extraction_deletion_readout
#print axioms replaced_lawNormal
#print axioms extractAlgebra_deleted_lawNormal
#print axioms lawNormal_collection_ne_variable
#print axioms lawNormal_distinguishes_named
#print axioms extractAlgebra_bareLabels
#print axioms declareAlgebras_bareLabels
#print axioms declareAlgebras_unwrap
#print axioms declared_lookup
#print axioms statedAlgebra_kind
#print axioms extractAlgebra_conditional_retained
#print axioms extractAlgebra_variable_endpoint_retained
#print axioms declared_unit_control
#print axioms wrong_unit_control
#print axioms cross_constructor_not_equivalent
#print axioms ownKind_bare
#print axioms statedAlgebra_flatten
#print axioms filter_algebra_update
#print axioms extractAlgebra_deleted_declares
#print axioms extractAlgebra_deleted_instances
#print axioms declareAlgebras_conditional_retained
#print axioms declareAlgebras_variable_endpoint_retained
#print axioms extractAlgebra_equations_sublist
#print axioms declareAlgebras_equations_sublist

end Mettapedia.GSLT.LanguageDef.ModuleSource.AlgebraExtractionSoundness

namespace Mettapedia.GSLT.LanguageDef.ModuleSource.AlgebraExtractionSoundness

set_option maxHeartbeats 1600000

open Mettapedia.OSLF.MeTTaIL Syntax CoreReduction CanonicalBags CollectionLaws Match

/-- Extraction changes algebra metadata but preserves the ordered declaration
signature after erasing that metadata. -/
theorem extractAlgebra_erased_terms (language current : LanguageDef)
    (binaryLabels : List String) (rule : GrammarRule) :
    (extractAlgebra language binaryLabels current rule).terms.map
        (fun declaration => { declaration with algebra? := none }) =
      current.terms.map (fun declaration => { declaration with algebra? := none }) := by
  unfold extractAlgebra
  split
  · rfl
  · split
    next algebra replaced found =>
      split
      · simp only [List.map_map]
        apply List.map_congr_left
        intro declaration _
        dsimp only [Function.comp_def]
        split <;> rfl
      · rfl
    next => rfl

theorem foldAlgebras_erased_terms (language current : LanguageDef)
    (binaryLabels : List String) (rules : List GrammarRule) :
    (rules.foldl (extractAlgebra language binaryLabels) current).terms.map
        (fun declaration => { declaration with algebra? := none }) =
      current.terms.map (fun declaration => { declaration with algebra? := none }) := by
  induction rules generalizing current with
  | nil => rfl
  | cons rule rules ih =>
      rw [List.foldl_cons, ih, extractAlgebra_erased_terms]

theorem erased_terms_filter (language current : LanguageDef) (kind : CollType)
    (same : current.terms.map (fun declaration => { declaration with algebra? := none }) =
      language.terms.map (fun declaration => { declaration with algebra? := none })) :
    (current.terms.filter (fun rule => bareKind rule == some kind)).map
        (fun declaration => { declaration with algebra? := none }) =
      (language.terms.filter (fun rule => bareKind rule == some kind)).map
        (fun declaration => { declaration with algebra? := none }) := by
  have filtered := congrArg (List.filter (fun rule => bareKind rule == some kind)) same
  simpa only [List.filter_map, Function.comp_def, bareKind, GrammarRule.bareParams] using filtered

theorem uniqueCollectionKind_filter {language : LanguageDef} {rule : GrammarRule}
    {kind : CollType} (member : rule ∈ language.terms) (shape : ownKind rule = some kind)
    (unique : uniqueCollectionKind language rule = true) :
    language.terms.filter (fun other => bareKind other == some kind) = [rule] := by
  have bare := ownKind_bare shape
  obtain ⟨only, single⟩ := List.length_eq_one_iff.mp ((uniqueCollectionKind_iff bare).mp unique)
  have selected : rule ∈ language.terms.filter (fun other => bareKind other == some kind) :=
    List.mem_filter.mpr ⟨member, by simp only [bare, beq_self_eq_true]⟩
  rw [single] at selected
  simpa only [List.mem_singleton.mp selected] using single

theorem extraction_deletion_unique (language current : LanguageDef)
    (binaryLabels : List String) (rule : GrammarRule) (row : Equation)
    (member : row ∈ current.equations)
    (deleted : row ∉ (extractAlgebra language binaryLabels current rule).equations) :
    uniqueCollectionKind language rule = true := by
  cases unique : uniqueCollectionKind language rule
  · simp only [extractAlgebra, unique, Bool.not_false, Bool.or_true, Bool.true_or,
      ↓reduceIte] at deleted
    exact False.elim (deleted member)
  · rfl

theorem extraction_deletion_guard (language current : LanguageDef)
    (binaryLabels : List String) (rule : GrammarRule) (row : Equation)
    (member : row ∈ current.equations)
    (deleted : row ∉ (extractAlgebra language binaryLabels current rule).equations) :
    (rule.algebra?.isSome || !uniqueCollectionKind language rule ||
      !binaryLabels.contains rule.label) = false := by
  cases tested : (rule.algebra?.isSome || !uniqueCollectionKind language rule ||
      !binaryLabels.contains rule.label)
  · rfl
  · exact False.elim (deleted (by simpa only [extractAlgebra, tested, ↓reduceIte] using member))

theorem extractAlgebra_filter_other (language current : LanguageDef)
    (binaryLabels : List String) (rule selected : GrammarRule) (kind : CollType)
    (single : current.terms.filter (fun other => bareKind other == some kind) = [selected])
    (different : selected.label ≠ rule.label) :
    (extractAlgebra language binaryLabels current rule).terms.filter
        (fun other => bareKind other == some kind) = [selected] := by
  unfold extractAlgebra
  split
  · exact single
  · split
    next algebra replaced found =>
      split
      · rw [filter_algebra_update, single]
        simp [different]
      · exact single
    next => exact single

theorem foldAlgebras_filter_other (language current : LanguageDef)
    (binaryLabels : List String) (rules : List GrammarRule) (selected : GrammarRule) (kind : CollType)
    (single : current.terms.filter (fun other => bareKind other == some kind) = [selected])
    (different : ∀ rule ∈ rules, selected.label ≠ rule.label) :
    (rules.foldl (extractAlgebra language binaryLabels) current).terms.filter
        (fun other => bareKind other == some kind) = [selected] := by
  induction rules generalizing current with
  | nil => exact single
  | cons rule rules ih =>
      apply ih _ (extractAlgebra_filter_other language current binaryLabels rule selected kind single
        (different rule List.mem_cons_self))
      intro other member
      exact different other (List.mem_cons_of_mem _ member)

theorem foldAlgebras_deletion_stage (language current : LanguageDef)
    (binaryLabels : List String) (rules : List GrammarRule) (row : Equation)
    (member : row ∈ current.equations)
    (deleted : row ∉ (rules.foldl (extractAlgebra language binaryLabels) current).equations) :
    ∃ before rule after, rules = before ++ rule :: after ∧
      row ∈ (before.foldl (extractAlgebra language binaryLabels) current).equations ∧
      row ∉ (extractAlgebra language binaryLabels
        (before.foldl (extractAlgebra language binaryLabels) current) rule).equations := by
  induction rules generalizing current with
  | nil => exact False.elim (deleted member)
  | cons rule rules ih =>
      by_cases removed : row ∈ (extractAlgebra language binaryLabels current rule).equations
      · obtain ⟨before, selected, after, split, present, absent⟩ :=
          ih _ removed deleted
        refine ⟨rule :: before, selected, after, ?_, ?_, ?_⟩
        · simp only [split, List.cons_append]
        · simpa only [List.foldl_cons] using present
        · simpa only [List.foldl_cons] using absent
      · exact ⟨[], rule, rules, rfl, member, removed⟩

/-- The executable unique-kind condition and source label determinacy rule
out any later declaration that could overwrite the selected algebra. -/
theorem uniqueCollectionKind_later_labels {language : LanguageDef}
    {before after : List GrammarRule} {rule : GrammarRule} {kind : CollType}
    (split : language.terms = before ++ rule :: after)
    (labels : ∀ first ∈ language.terms, ∀ second ∈ language.terms,
      first.label = second.label → first = second)
    (shape : ownKind rule = some kind)
    (single : language.terms.filter (fun other => bareKind other == some kind) = [rule]) :
    ∀ later ∈ after, rule.label ≠ later.label := by
  intro later member same
  have selected : rule ∈ language.terms := by rw [split]; simp
  have laterMember : later ∈ language.terms := by rw [split]; simp [member]
  have equal := labels rule selected later laterMember same
  subst later
  have bare := ownKind_bare shape
  have laterFiltered : rule ∈ after.filter (fun other => bareKind other == some kind) :=
    List.mem_filter.mpr ⟨member, by simp only [bare, beq_self_eq_true]⟩
  have positive := List.length_pos_of_mem laterFiltered
  have sizes := congrArg List.length single
  rw [split, List.filter_append, List.filter_cons] at sizes
  simp only [bare, beq_self_eq_true, ↓reduceIte, List.length_append, List.length_cons,
    List.length_nil] at sizes
  omega

/-- A law justifying a deleted equation remains declared at the end of the
whole fold. Its availability follows from the finite source signature and the
executable deletion, rather than from a supplied normalizer certificate. -/
theorem deletion_stage_final_declares (language : LanguageDef) (binaryLabels : List String)
    (before : List GrammarRule) (rule : GrammarRule) (after : List GrammarRule)
    (row : Equation) (kind : CollType)
    (split : language.terms = before ++ rule :: after)
    (labels : ∀ first ∈ language.terms, ∀ second ∈ language.terms,
      first.label = second.label → first = second)
    (shape : ownKind rule = some kind)
    (member : row ∈ (before.foldl (extractAlgebra language binaryLabels) language).equations)
    (deleted : row ∉ (extractAlgebra language binaryLabels
      (before.foldl (extractAlgebra language binaryLabels) language) rule).equations) :
    ∃ law, lawFor (CollectionLaws.declared (declareAlgebras language binaryLabels)) kind = some law := by
  let current := before.foldl (extractAlgebra language binaryLabels) language
  have ruleMember : rule ∈ language.terms := by rw [split]; simp
  have unique := extraction_deletion_unique language current binaryLabels rule row member deleted
  have sourceSingle := uniqueCollectionKind_filter ruleMember shape unique
  have skeleton := foldAlgebras_erased_terms language language binaryLabels before
  have filtered := erased_terms_filter language current kind skeleton
  rw [sourceSingle, List.map_singleton] at filtered
  obtain ⟨selected, currentSingle, sameSkeleton⟩ := List.map_eq_singleton_iff.mp filtered
  have sameLabel : selected.label = rule.label := by
    have projected := congrArg (fun declaration : GrammarRule => declaration.label) sameSkeleton
    exact projected
  obtain ⟨algebra, replaced, found, unitPresent, _⟩ :=
    extraction_deletion_readout language current binaryLabels rule row member deleted
  have guarded := extraction_deletion_guard language current binaryLabels rule row member deleted
  have outputSingle :
      (extractAlgebra language binaryLabels current rule).terms.filter
          (fun other => bareKind other == some kind) = [{selected with algebra? := some algebra}] := by
    simp only [extractAlgebra, guarded, Bool.false_eq_true, ↓reduceIte, found, unitPresent]
    rw [filter_algebra_update, currentSingle]
    simp [sameLabel]
  have untouched := uniqueCollectionKind_later_labels split labels shape sourceSingle
  have finalSingle := foldAlgebras_filter_other language
    (extractAlgebra language binaryLabels current rule) binaryLabels after
      {selected with algebra? := some algebra} kind outputSingle
      (fun later member => sameLabel ▸ untouched later member)
  have finalFilter : (declareAlgebras language binaryLabels).terms.filter
      (fun other => bareKind other == some kind) = [{selected with algebra? := some algebra}] := by
    simpa only [declareAlgebras, split, List.foldl_append, List.foldl_cons, current] using finalSingle
  have flatten := statedAlgebra_flatten shape found
  have algebraEq : algebra = ⟨true, algebra.unit⟩ := by
    cases algebra with
    | mk flatten unit => simp_all
  refine ⟨⟨kind, algebra.unit⟩, ?_⟩
  apply declared_lookup finalFilter
  exact congrArg some algebraEq

theorem bareLabels_as_kinds (language : LanguageDef) :
    bareLabels language = language.terms.filterMap
      (fun rule => (bareKind rule).map (fun kind => (rule.label, kind))) := by
  unfold bareLabels
  apply List.filterMap_congr
  intro rule _
  unfold bareKind
  split <;> simp_all

theorem bareLabels_member_kind {language : LanguageDef} {label : String} {kind : CollType}
    (member : (label, kind) ∈ bareLabels language) :
    ∃ rule ∈ language.terms, rule.label = label ∧ bareKind rule = some kind := by
  rw [bareLabels_as_kinds] at member
  obtain ⟨rule, selected, produced⟩ := List.mem_filterMap.mp member
  cases shape : bareKind rule with
  | none => simp [shape] at produced
  | some actual =>
      have same : (rule.label, actual) = (label, kind) := by simpa only [shape, Option.map_some,
        Option.some.injEq] using produced
      exact ⟨rule, selected, (Prod.mk.inj same).1, (Prod.mk.inj same).2 ▸ shape⟩

/-- Source label determinacy makes the representation lookup agree with the
selected bare declaration. -/
theorem bareLabels_selected_lookup {language : LanguageDef} {rule : GrammarRule} {kind : CollType}
    (labels : ∀ first ∈ language.terms, ∀ second ∈ language.terms,
      first.label = second.label → first = second)
    (member : rule ∈ language.terms) (shape : ownKind rule = some kind) :
    (bareLabels language).lookup rule.label = some kind := by
  have bare := ownKind_bare shape
  have pairMember : (rule.label, kind) ∈ bareLabels language := by
    rw [bareLabels_as_kinds]
    exact List.mem_filterMap.mpr ⟨rule, member, by simp only [bare, Option.map_some]⟩
  cases found : (bareLabels language).lookup rule.label with
  | none =>
      have absent := List.lookup_eq_none_iff.mp found (rule.label, kind) pairMember
      simp only [bne_self_eq_false, Bool.false_eq_true] at absent
  | some actual =>
      obtain ⟨before, after, split, _⟩ := List.lookup_eq_some_iff.mp found
      have actualMember : (rule.label, actual) ∈ bareLabels language := by rw [split]; simp
      obtain ⟨other, otherMember, label, otherKind⟩ := bareLabels_member_kind actualMember
      have same := labels other otherMember rule member label
      subst other
      have equal := Option.some.inj (otherKind.symm.trans bare)
      simp only [equal]

/-- Every instantiated equation deleted anywhere in the extraction fold is
licensed by the final declared laws after representation lowering. This is
forward equation preservation; it asserts neither source-theory reflection
nor coherence of a rewrite relation. -/
theorem declareAlgebras_deleted_instances (language : LanguageDef) (binaryLabels : List String)
    (row : Equation) (bindings : Bindings)
    (labels : ∀ first ∈ language.terms, ∀ second ∈ language.terms,
      first.label = second.label → first = second)
    (member : row ∈ language.equations)
    (deleted : row ∉ (declareAlgebras language binaryLabels).equations) :
    Relation.EqvGen (LawStep (CollectionLaws.declared (declareAlgebras language binaryLabels)))
      (unwrap (bareLabels language) (applyBindings bindings row.left))
      (unwrap (bareLabels language) (applyBindings bindings row.right)) := by
  obtain ⟨before, rule, after, split, present, absent⟩ :=
    foldAlgebras_deletion_stage language language binaryLabels language.terms row member deleted
  obtain ⟨algebra, replaced, found, _, removed⟩ := extraction_deletion_readout language
    (before.foldl (extractAlgebra language binaryLabels) language) binaryLabels rule row present absent
  obtain ⟨kind, shape⟩ := statedAlgebra_kind found
  obtain ⟨law, declared⟩ := deletion_stage_final_declares language binaryLabels before rule after
    row kind split labels shape present absent
  have selected := bareLabels_selected_lookup labels
    (by rw [split]; exact List.mem_append_right _ List.mem_cons_self) shape
  exact (lawNormal_iff _ _ _).mp (replaced_lawNormal bindings shape found selected declared removed)

theorem recheck_input_valid {items checked : List Item}
    (accepted : recheck items = .ok checked) : ModuleAlgebra.Valid items.toFinset := by
  unfold recheck at accepted
  cases tested : ModuleAlgebra.orderedCheck? items with
  | none => simp [tested] at accepted
  | some result =>
      apply (ModuleAlgebra.orderedCheck_isSome_iff items).mp
      simp only [tested, Option.isSome_some]

theorem flattenRaw_labels_unique (sourceName : String) (value : Value)
    (coherent : ∀ item ∈ value.entries, ∀ rule,
      item.body = .term rule → item.label = (.term, rule.label))
    (valid : ModuleAlgebra.Valid value.entries.toFinset) :
    ∀ first ∈ (flattenRaw sourceName value).terms,
      ∀ second ∈ (flattenRaw sourceName value).terms,
        first.label = second.label → first = second := by
  have selected : ∀ rule ∈ (flattenRaw sourceName value).terms,
      ∃ item ∈ value.entries, item.body = .term rule := by
    intro rule member
    obtain ⟨item, itemMember, produced⟩ := List.mem_filterMap.mp member
    cases body : item.body <;> try { simp [body] at produced }
    rename_i actual
    have same : actual = rule := by simpa only [body, Option.some.injEq] using produced
    exact ⟨item, itemMember, same ▸ body⟩
  intro first firstMember second secondMember sameLabel
  obtain ⟨firstItem, firstItemMember, firstBody⟩ := selected first firstMember
  obtain ⟨secondItem, secondItemMember, secondBody⟩ := selected second secondMember
  have sameKey : firstItem.label = secondItem.label :=
    (coherent firstItem firstItemMember first firstBody).trans
      ((congrArg (fun label => (Kind.term, label)) sameLabel).trans
        (coherent secondItem secondItemMember second secondBody).symm)
  have sameItem := valid firstItem (List.mem_toFinset.mpr firstItemMember)
    secondItem (List.mem_toFinset.mpr secondItemMember) (.inr sameKey)
  have sameBody := congrArg (fun item : Item => item.body) sameItem
  rw [firstBody, secondBody] at sameBody
  exact Decl.term.inj sameBody

theorem retained_labels_unique (language : LanguageDef) (binaryLabels : List String)
    (labels : ∀ first ∈ language.terms, ∀ second ∈ language.terms,
      first.label = second.label → first = second) :
    ∀ first ∈ (retainSharedCollectionLabels language binaryLabels).terms,
      ∀ second ∈ (retainSharedCollectionLabels language binaryLabels).terms,
        first.label = second.label → first = second := by
  let retain := fun rule : GrammarRule => match collectionParameterKind rule with
    | none => rule
    | some kind =>
        if language.terms.any (fun other =>
            other.label != rule.label && collectionParameterKind other == some kind) ||
            (collectionAlgebraCandidate rule binaryLabels &&
              otherCollectionParameter language rule kind) then
          {rule with collectionRepresentation := .wrapped}
        else rule
  have keepLabel : ∀ rule, (retain rule).label = rule.label := by
    intro rule
    dsimp only [retain]
    split
    · rfl
    · split <;> rfl
  intro first firstMember second secondMember sameLabel
  obtain ⟨originalFirst, firstSelected, rfl⟩ := List.mem_map.mp firstMember
  obtain ⟨originalSecond, secondSelected, rfl⟩ := List.mem_map.mp secondMember
  have originals : originalFirst = originalSecond := labels originalFirst firstSelected
    originalSecond secondSelected ((keepLabel originalFirst).symm.trans
      (sameLabel.trans (keepLabel originalSecond)))
  exact congrArg retain originals

/-- Keeping declared-bare constructors bare changes no label. -/
theorem kept_labels_unique (declared : List String) (language : LanguageDef)
    (labels : ∀ first ∈ language.terms, ∀ second ∈ language.terms,
      first.label = second.label → first = second) :
    ∀ first ∈ (keepDeclaredBare declared language).terms,
      ∀ second ∈ (keepDeclaredBare declared language).terms,
        first.label = second.label → first = second := by
  let keep := fun rule : GrammarRule =>
    if declared.contains rule.label then { rule with collectionRepresentation := .bare } else rule
  have keepLabel : ∀ rule, (keep rule).label = rule.label := by
    intro rule
    dsimp only [keep]
    split <;> rfl
  intro first firstMember second secondMember sameLabel
  obtain ⟨originalFirst, firstSelected, rfl⟩ := List.mem_map.mp firstMember
  obtain ⟨originalSecond, secondSelected, rfl⟩ := List.mem_map.mp secondMember
  have originals : originalFirst = originalSecond := labels originalFirst firstSelected
    originalSecond secondSelected ((keepLabel originalFirst).symm.trans
      (sameLabel.trans (keepLabel originalSecond)))
  exact congrArg keep originals

/-- The authoring pipeline's shared-constructor protection, with declared-bare constructors kept bare, precedes
algebra extraction. Successful entry checking and entry/body label coherence provide
the finite signature condition for that exact pipeline. -/
theorem flatten_deleted_instances (sourceName : String) (value : Value)
    (checked : List Item) (row : Equation) (bindings : Bindings)
    (coherent : ∀ item ∈ value.entries, ∀ rule,
      item.body = .term rule → item.label = (.term, rule.label))
    (accepted : recheck value.entries = .ok checked)
    (member : row ∈ (flattenRaw sourceName value).equations)
    (deleted : row ∉ (flatten sourceName value).equations) :
    Relation.EqvGen (LawStep (CollectionLaws.declared (flatten sourceName value)))
      (unwrap (bareLabels (keepDeclaredBare value.declaredBare
          (retainSharedCollectionLabels (flattenRaw sourceName value) (binaryCollectionLabels value))))
        (applyBindings bindings row.left))
      (unwrap (bareLabels (keepDeclaredBare value.declaredBare
          (retainSharedCollectionLabels (flattenRaw sourceName value) (binaryCollectionLabels value))))
        (applyBindings bindings row.right)) := by
  have labels := kept_labels_unique value.declaredBare _
    (retained_labels_unique (flattenRaw sourceName value) (binaryCollectionLabels value)
      (flattenRaw_labels_unique sourceName value coherent (recheck_input_valid accepted)))
  exact declareAlgebras_deleted_instances
    (keepDeclaredBare value.declaredBare
      (retainSharedCollectionLabels (flattenRaw sourceName value) (binaryCollectionLabels value)))
    _ row bindings labels member deleted

theorem recheck_refuses_label_collision (first second : Item)
    (sameLabel : first.label = second.label) (different : first ≠ second) :
    ∀ checked, recheck [first, second] ≠ .ok checked := by
  intro checked accepted
  have valid := recheck_input_valid accepted
  exact different (valid first (by simp) second (by simp) (.inr sameLabel))

#print axioms extractAlgebra_erased_terms
#print axioms foldAlgebras_erased_terms
#print axioms erased_terms_filter
#print axioms uniqueCollectionKind_filter
#print axioms extraction_deletion_unique
#print axioms extraction_deletion_guard
#print axioms extractAlgebra_filter_other
#print axioms foldAlgebras_filter_other
#print axioms foldAlgebras_deletion_stage
#print axioms uniqueCollectionKind_later_labels
#print axioms deletion_stage_final_declares
#print axioms bareLabels_as_kinds
#print axioms bareLabels_member_kind
#print axioms bareLabels_selected_lookup
#print axioms declareAlgebras_deleted_instances
#print axioms recheck_input_valid
#print axioms flattenRaw_labels_unique
#print axioms retained_labels_unique
#print axioms kept_labels_unique
#print axioms flatten_deleted_instances
#print axioms recheck_refuses_label_collision

end Mettapedia.GSLT.LanguageDef.ModuleSource.AlgebraExtractionSoundness
