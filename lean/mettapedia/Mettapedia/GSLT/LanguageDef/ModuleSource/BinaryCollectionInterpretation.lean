import Mettapedia.GSLT.LanguageDef.ModuleSource.BinaryCollectionLowering
import Mettapedia.GSLT.LanguageDef.ModuleSource.AlgebraInterpretation
import Mettapedia.OSLF.MeTTaIL.CanonicalBags
import Mettapedia.GSLT.LanguageDef.BagEquationDecision

/-!
# Source binary algebras and their packed collection interpretation

The source equations earn the fold model. The actual replacement and
unwrapping traversals then preserve every defined first-order interpretation
of a typed source pattern. The same fold respects the existing collection
presentation relation and canonical arrangement; no new normalizer is used.

These theorems concern defined first-order carrier interpretations. They do
not identify independent collection-data observations, decide arbitrary extra
equation theories or establish firing coverage.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleSource.BinaryCollectionInterpretation

open Mettapedia.OSLF.MeTTaIL Syntax WellSorted ReplacementTransport
open CanonicalBags CollectionLaws
open BinaryCollectionLowering

universe u
variable {A : Type u}

/-- The selected constructor is the identity wrapper around its collection
argument; the collection itself is interpreted by the earned finite fold.
Other constructor labels retain their source operations. -/
def read? (operations : String → List A → A) (assignment : String → A)
    (label : String) (kind : CollType) (fold : Mettapedia.Algebra.Collections.Folds.Model A) :
    Pattern → Option A
  | .fvar name => some (assignment name)
  | .apply head arguments => do
      let values ← arguments.mapM (read? operations assignment label kind fold)
      if head = label then
        match values with
        | [value] => some value
        | _ => none
      else some (operations head values)
  | .collection actual elements none =>
      if actual = kind then
        (elements.mapM (read? operations assignment label kind fold)).map fold.fold
      else none
  | _ => none
termination_by pattern => sizeOf pattern
decreasing_by all_goals sizeOf_pattern_dec

def checkFreshLabel (source : LanguageDef) (old new : GrammarRule) : Bool :=
  source.terms.all fun rule => rule.label != new.label || rule.label == old.label

theorem freshLabel_of_check {source : LanguageDef} {old new : GrammarRule}
    (checked : checkFreshLabel source old new = true) {rule : GrammarRule}
    (member : rule ∈ source.terms) (different : rule.label ≠ old.label) :
    rule.label ≠ new.label := by
  have fresh := List.all_eq_true.mp checked rule member
  simp only [Bool.or_eq_true, bne_iff_ne, beq_iff_eq] at fresh
  exact fresh.resolve_right different

private theorem length_mapM {f : Pattern → Option A} {patterns : List Pattern} {values : List A}
    (computed : patterns.mapM f = some values) : values.length = patterns.length := by
  induction patterns generalizing values with
  | nil => simpa using (congrArg List.length (Option.some.inj computed)).symm
  | cons pattern patterns ih =>
    cases first : f pattern with
    | none => simp [List.mapM_cons, first] at computed
    | some value =>
      cases rest : patterns.mapM f with
      | none => simp [List.mapM_cons, first, rest] at computed
      | some tail =>
        have same : value :: tail = values := by simpa [List.mapM_cons, first, rest] using computed
        rw [← same]
        simpa using congrArg Nat.succ (ih rest)

variable {source target : LanguageDef} {old new : GrammarRule}
    {name sort : String} {kind : CollType}

mutual
  /-- The interpretation follows the actual lowered pattern, not a parallel
  packing implementation. Undefined source interpretations make no claim. -/
  theorem read_translated (signature : Signature source target old new)
      (representation : Representation source target old new kind)
      (checked : checkReplacementTyping old new = true)
      (named : namedArguments? old new = false)
      (shape : new.params = [.simple name (.collection kind (.base sort))])
      (fresh : checkFreshLabel source old new = true)
      (operations : String → List A → A) (assignment : String → A)
      (fold : Mettapedia.Algebra.Collections.Folds.Model A)
      (binary : ∀ first second, fold.fold [first, second] = operations old.label [first, second])
      (free : FreeTypeContext) (bound : List TypeExpr) {pattern : Pattern} {type : TypeExpr}
      (typed : HasType source free bound pattern type) {value : A}
      (computed : AlgebraInterpretation.read? operations assignment pattern = some value) :
      read? operations assignment new.label kind fold
        (translated target old new kind pattern) = some value := by
    cases typed with
    | fvar found => simpa only [AlgebraInterpretation.read?, translated, renameConstructor,
        CoreReduction.unwrap, read?] using computed
    | @constructor bound rule arguments member ordinary argumentsTyped =>
      cases values : arguments.mapM (AlgebraInterpretation.read? operations assignment) with
      | none => simp only [AlgebraInterpretation.read?, values, Option.map_none] at computed; cases computed
      | some result =>
        have valueEq : operations rule.label result = value := by
          simpa only [AlgebraInterpretation.read?, values, Option.map_some, Option.some.injEq] using computed
        have mapped := arguments_read signature representation checked named shape fresh
          operations assignment fold binary free bound argumentsTyped values
        by_cases selected : rule.label = old.label
        · have same := signature.unique rule member selected
          subst rule
          have arity : result.length = 2 :=
            (length_mapM values).trans (argumentsTyped.length_eq.trans
              (checkReplacementTyping_packed checked named shape).2.1)
          obtain ⟨first, second, rfl⟩ := List.length_eq_two.mp arity
          have folded : fold.fold [first, second] = value := (binary first second).trans valueEq
          cases mode : new.collectionRepresentation with
          | bare =>
            have lookup : (CoreReduction.bareLabels target).lookup new.label = some kind := by
              simpa [mode] using representation.selected
            simp only [translated, renameConstructor, ↓reduceIte, packing, List.map_cons,
              List.map_nil, CoreReduction.unwrap, lookup, List.map_map, Function.comp_def,
              read?, mapped, Option.map_some, folded, ↓reduceIte]
          | wrapped =>
            have lookup : (CoreReduction.bareLabels target).lookup new.label = none := by
              simpa [mode] using representation.selected
            simp only [translated, renameConstructor, ↓reduceIte, packing, List.map_cons,
              List.map_nil, CoreReduction.unwrap, lookup, List.map_map, Function.comp_def,
              read?, mapped, Option.map_some, folded, ↓reduceIte, List.mapM_cons, List.mapM_nil, bind, pure,
              Option.bind]
        · have different := freshLabel_of_check fresh member selected
          simp only [translated, renameConstructor, if_neg selected, CoreReduction.unwrap,
            representation.retained rule member selected ordinary, List.map_map, Function.comp_def,
            read?, mapped, if_neg different, valueEq, bind, Option.bind]
    | bvar | lambda | multiLambda | subst | collection | collectionConstructor =>
      simp only [AlgebraInterpretation.read?] at computed
      cases computed
  termination_by sizeOf pattern

  theorem arguments_read (signature : Signature source target old new)
      (representation : Representation source target old new kind)
      (checked : checkReplacementTyping old new = true)
      (named : namedArguments? old new = false)
      (shape : new.params = [.simple name (.collection kind (.base sort))])
      (fresh : checkFreshLabel source old new = true)
      (operations : String → List A → A) (assignment : String → A)
      (fold : Mettapedia.Algebra.Collections.Folds.Model A)
      (binary : ∀ first second, fold.fold [first, second] = operations old.label [first, second])
      (free : FreeTypeContext) (bound : List TypeExpr)
      {arguments : List Pattern} {parameters : List TermParam}
      (typed : ArgumentsHaveTypes source free bound arguments parameters) {values : List A}
      (computed : arguments.mapM (AlgebraInterpretation.read? operations assignment) = some values) :
      (arguments.map (translated target old new kind)).mapM
        (read? operations assignment new.label kind fold) = some values := by
    cases typed with
    | nil => exact computed
    | @cons bound argument arguments parameter parameters expected represented declared first rest =>
      cases head : AlgebraInterpretation.read? operations assignment argument with
      | none => simp [List.mapM_cons, head] at computed
      | some value =>
        cases tail : arguments.mapM (AlgebraInterpretation.read? operations assignment) with
        | none => simp [List.mapM_cons, head, tail] at computed
        | some remaining =>
          have headRead := read_translated signature representation checked named shape fresh
            operations assignment fold binary free bound first head
          have tailRead := arguments_read signature representation checked named shape fresh
            operations assignment fold binary free bound rest tail
          simpa only [List.mapM_cons, head, tail, List.map_cons, headRead, tailRead]
            using computed
  termination_by sizeOf arguments
end

/-- Arrangement by the existing canonicalizer is licensed by the same fold
that interprets packing: bags forget order, sets also forget repetition. -/
theorem fold_arrange (fold : Mettapedia.Algebra.Collections.Folds.Model A)
    (kind : CollType) (permutation : kind ≠ .vec → fold.PermutationInvariant)
    (membership : kind = .hashSet → fold.MembershipInvariant)
    (interpret : Pattern → A) (elements : List Pattern) :
    fold.fold ((CanonicalBags.arrange kind elements).map interpret) =
      fold.fold (elements.map interpret) := by
  cases kind with
  | vec => rfl
  | hashBag =>
    exact permutation (by decide) _ _ ((PatternLexOrder.sortLex_perm elements).map interpret)
  | hashSet =>
    apply membership rfl
    intro value
    simp only [List.mem_map]
    exact ⟨fun ⟨pattern, member, image⟩ =>
      ⟨pattern, (CanonicalBags.arrange_mem pattern).mp member, image⟩,
      fun ⟨pattern, member, image⟩ =>
        ⟨pattern, (CanonicalBags.arrange_mem pattern).mpr member, image⟩⟩

/-- Splicing uses the same earned fold as binary packing. This law says
nothing about an independent observation of the input list as vector data. -/
theorem fold_splice (fold : Mettapedia.Algebra.Collections.Folds.Model A)
    (before middle after : List A) :
    fold.fold (before ++ fold.fold middle :: after) =
      fold.fold (before ++ middle ++ after) := by
  calc
    _ = fold.fold [fold.fold before, fold.fold (fold.fold middle :: after)] :=
      fold.fold_append before _
    _ = fold.fold [fold.fold before, fold.fold [fold.fold middle, fold.fold after]] :=
      congrArg (fun value => fold.fold [fold.fold before, value])
        (fold.fold_cons (fold.fold middle) after)
    _ = fold.fold [fold.fold [fold.fold before, fold.fold middle], fold.fold after] :=
      (fold.fold_associative _ _ _).symm
    _ = _ := by
      simpa only [fold.fold_append before middle] using
        (fold.fold_append (before ++ middle) after).symm

theorem fold_remove_unit (fold : Mettapedia.Algebra.Collections.Folds.Model A)
    (before after : List A) :
    fold.fold (before ++ fold.fold [] :: after) = fold.fold (before ++ after) := by
  simpa using fold_splice fold before [] after

private theorem mapM_defined (read : Pattern → Option A) {elements : List Pattern} {values : List A}
    (computed : elements.mapM read = some values) :
    ∀ element ∈ elements, ∃ value, read element = some value := by
  induction elements generalizing values with
  | nil => simp
  | cons element elements ih =>
    cases first : read element with
    | none => simp [List.mapM_cons, first] at computed
    | some value =>
      cases remaining : elements.mapM read with
      | none => simp [List.mapM_cons, first, remaining] at computed
      | some rest =>
        intro item member
        rcases List.mem_cons.mp member with rfl | member
        · exact ⟨value, first⟩
        · exact ih remaining item member

private theorem mapM_getD (read : Pattern → Option A) (fallback : A) (elements : List Pattern)
    (defined : ∀ element ∈ elements, ∃ value, read element = some value) :
    elements.mapM read = some (elements.map fun element => (read element).getD fallback) := by
  induction elements with
  | nil => rfl
  | cons element elements ih =>
    obtain ⟨value, first⟩ := defined element List.mem_cons_self
    have remaining := ih (fun item member => defined item (List.mem_cons_of_mem _ member))
    simp only [List.mapM_cons, first, remaining, List.map_cons, Option.getD_some]
    rfl

mutual
  /-- Canonical arrangement preserves every defined interpretation, including nested collections. -/
  theorem read_canon (operations : String → List A → A) (assignment : String → A)
      (label : String) (kind : CollType) (fold : Mettapedia.Algebra.Collections.Folds.Model A)
      (arranged : ∀ (interpret : Pattern → A) (elements : List Pattern),
        fold.fold ((arrange kind elements).map interpret) = fold.fold (elements.map interpret))
      {pattern : Pattern} {value : A}
      (computed : read? operations assignment label kind fold pattern = some value) :
      read? operations assignment label kind fold (canon pattern) = some value := by
    cases pattern with
    | fvar atom => simpa only [canon] using computed
    | apply head arguments =>
      cases values : arguments.mapM (read? operations assignment label kind fold) with
      | none => simp only [read?, values] at computed; cases computed
      | some values' =>
        have normalized := arguments_canon operations assignment label kind fold arranged values
        simpa only [canon_apply, read?, values, normalized] using computed
    | collection actual elements rest =>
      cases rest with
      | some _ => simp only [read?] at computed; cases computed
      | none =>
        by_cases selected : actual = kind
        · subst actual
          cases values : elements.mapM (read? operations assignment label kind fold) with
          | none => simp only [read?, ↓reduceIte, values, Option.map_none] at computed; cases computed
          | some values' =>
            have normalized := arguments_canon operations assignment label kind fold arranged values
            let read := read? operations assignment label kind fold
            let interpret := fun element => (read element).getD value
            have defined := mapM_defined read normalized
            have kept := mapM_getD read value (elements.map canon) defined
            have sameValues : (elements.map canon).map interpret = values' :=
              Option.some.inj (kept.symm.trans normalized)
            have sorted := mapM_getD read value (arrange kind (elements.map canon))
              (fun element member => defined element ((arrange_mem element).mp member))
            have valueEq : fold.fold values' = value := by
              simpa only [read?, ↓reduceIte, values, Option.map_some, Option.some.injEq] using computed
            dsimp only [read] at sorted
            simp only [canon_collection, read?, ↓reduceIte]
            rw [sorted]
            simp only [Option.map_some]
            exact congrArg some ((arranged interpret _).trans ((congrArg fold.fold sameValues).trans valueEq))
        · simp only [read?, selected, ↓reduceIte] at computed; cases computed
    | bvar | lambda | multiLambda | subst => simp only [read?] at computed; cases computed
  termination_by sizeOf pattern
  decreasing_by all_goals sizeOf_pattern_dec

  theorem arguments_canon (operations : String → List A → A) (assignment : String → A)
      (label : String) (kind : CollType) (fold : Mettapedia.Algebra.Collections.Folds.Model A)
      (arranged : ∀ (interpret : Pattern → A) (elements : List Pattern),
        fold.fold ((arrange kind elements).map interpret) = fold.fold (elements.map interpret))
      {arguments : List Pattern} {values : List A}
      (computed : arguments.mapM (read? operations assignment label kind fold) = some values) :
      (arguments.map canon).mapM (read? operations assignment label kind fold) = some values := by
    cases arguments with
    | nil => exact computed
    | cons argument arguments =>
      cases first : read? operations assignment label kind fold argument with
      | none => simp [List.mapM_cons, first] at computed
      | some value =>
        cases remaining : arguments.mapM (read? operations assignment label kind fold) with
        | none => simp [List.mapM_cons, first, remaining] at computed
        | some rest =>
          have headRead := read_canon operations assignment label kind fold arranged first
          have tailRead := arguments_canon operations assignment label kind fold arranged remaining
          simpa only [List.mapM_cons, first, remaining, List.map_cons, headRead, tailRead] using computed
  termination_by sizeOf arguments
  decreasing_by all_goals sizeOf_pattern_dec
end


/-! ## Declared flattening and units in the same interpretation -/

private theorem read_splice (operations : String → List A → A) (assignment : String → A)
    (label : String) (kind : CollType) (fold : Mettapedia.Algebra.Collections.Folds.Model A)
    (law : Laws) (sameKind : law.kind = kind)
    (unitRead : ∀ unit, law.unit = some unit → unit ≠ label ∧ operations unit [] = fold.fold [])
    {pattern : Pattern} {value : A}
    (computed : read? operations assignment label kind fold pattern = some value) :
    ∃ values, (splice law pattern).mapM (read? operations assignment label kind fold) = some values ∧
      fold.fold values = value := by
  have singleton {pattern : Pattern} (computed : read? operations assignment label kind fold pattern = some value) :
      ∃ values, [pattern].mapM (read? operations assignment label kind fold) = some values ∧
        fold.fold values = value :=
    ⟨[value], by simp only [List.mapM_cons, computed, List.mapM_nil]; rfl, fold.singleton value⟩
  cases pattern with
  | apply head arguments =>
    cases arguments with
    | nil =>
      by_cases selected : law.unit = some head
      · obtain ⟨different, empty⟩ := unitRead head selected
        have same : fold.fold [] = value := by
          simpa only [read?, List.mapM_nil, bind, pure, Option.bind,
            if_neg different, empty, Option.some.injEq] using computed
        exact ⟨[], by simp only [splice, selected, if_true, List.mapM_nil]; rfl, same⟩
      · simpa only [splice, if_neg selected] using singleton computed
    | cons first rest => simpa only [splice] using singleton computed
  | collection actual elements rest =>
    cases rest with
    | none =>
      by_cases selected : actual = kind
      · subst actual
        cases values : elements.mapM (read? operations assignment label kind fold) with
        | none => simp only [read?, ↓reduceIte, values, Option.map_none] at computed; cases computed
        | some values' =>
          refine ⟨values', ?_, ?_⟩
          · simpa only [splice, sameKind, ↓reduceIte] using values
          · simpa only [read?, ↓reduceIte, values, Option.map_some, Option.some.injEq] using computed
      · simpa only [splice, sameKind, if_neg selected] using singleton computed
    | some rest => simpa only [splice] using singleton computed
  | _ => simpa only [splice] using singleton computed

private theorem read_spliced_list (operations : String → List A → A) (assignment : String → A)
    (label : String) (kind : CollType) (fold : Mettapedia.Algebra.Collections.Folds.Model A)
    (law : Laws) (sameKind : law.kind = kind)
    (unitRead : ∀ unit, law.unit = some unit → unit ≠ label ∧ operations unit [] = fold.fold [])
    {patterns : List Pattern} {values : List A}
    (computed : patterns.mapM (read? operations assignment label kind fold) = some values) :
    ∃ spliced, (patterns.flatMap (splice law)).mapM (read? operations assignment label kind fold) = some spliced ∧
      fold.fold spliced = fold.fold values := by
  induction patterns generalizing values with
  | nil =>
    have empty : values = [] := by simpa using (Option.some.inj computed).symm
    subst values
    exact ⟨[], rfl, rfl⟩
  | cons pattern patterns ih =>
    cases first : read? operations assignment label kind fold pattern with
    | none => simp [List.mapM_cons, first] at computed
    | some value =>
      cases remaining : patterns.mapM (read? operations assignment label kind fold) with
      | none => simp [List.mapM_cons, first, remaining] at computed
      | some rest =>
        have same : value :: rest = values := by
          simpa only [List.mapM_cons, first, remaining, bind, pure, Option.bind, Option.some.injEq] using computed
        subst values
        obtain ⟨pieces, pieceReads, pieceFold⟩ := read_splice operations assignment label kind fold law sameKind unitRead first
        obtain ⟨tail, tailReads, tailFold⟩ := ih remaining
        refine ⟨pieces ++ tail, ?_, ?_⟩
        · simp only [List.flatMap_cons, List.mapM_append, pieceReads, tailReads]
          rfl
        · rw [fold.fold_append, pieceFold, tailFold]
          exact (fold.fold_cons value rest).symm

mutual
  theorem read_normalize (operations : String → List A → A) (assignment : String → A)
      (label : String) (kind : CollType) (fold : Mettapedia.Algebra.Collections.Folds.Model A)
      (laws : List Laws)
      (units : ∀ law, lawFor laws kind = some law →
        ∀ unit, law.unit = some unit → unit ≠ label ∧ operations unit [] = fold.fold [])
      {pattern : Pattern} {value : A}
      (computed : read? operations assignment label kind fold pattern = some value) :
      read? operations assignment label kind fold (CollectionLaws.normalize laws pattern) = some value := by
    cases pattern with
    | fvar atom => simpa only [CollectionLaws.normalize] using computed
    | apply head arguments =>
      cases values : arguments.mapM (read? operations assignment label kind fold) with
      | none => simp only [read?, values] at computed; cases computed
      | some values' =>
        have normalized := arguments_normalize operations assignment label kind fold laws units values
        simpa only [CollectionLaws.normalize, read?, values, normalized] using computed
    | collection actual elements rest =>
      cases rest with
      | some _ => simp only [read?] at computed; cases computed
      | none =>
        by_cases selected : actual = kind
        · subst actual
          cases values : elements.mapM (read? operations assignment label kind fold) with
          | none => simp only [read?, ↓reduceIte, values, Option.map_none] at computed; cases computed
          | some values' =>
            have normalized := arguments_normalize operations assignment label kind fold laws units values
            cases chosen : lawFor laws kind with
            | none => simpa only [CollectionLaws.normalize, chosen, read?, ↓reduceIte, normalized, values] using computed
            | some law =>
              obtain ⟨spliced, splicedReads, splicedFold⟩ := read_spliced_list operations assignment label kind fold
                law (lawFor_kind chosen) (units law chosen) normalized
              simpa only [CollectionLaws.normalize, chosen, read?, ↓reduceIte, splicedReads, Option.map_some,
                values, splicedFold] using computed
        · simp only [read?, if_neg selected] at computed; cases computed
    | bvar | lambda | multiLambda | subst => simp only [read?] at computed; cases computed
  termination_by sizeOf pattern
  decreasing_by all_goals sizeOf_pattern_dec

  theorem arguments_normalize (operations : String → List A → A) (assignment : String → A)
      (label : String) (kind : CollType) (fold : Mettapedia.Algebra.Collections.Folds.Model A)
      (laws : List Laws)
      (units : ∀ law, lawFor laws kind = some law →
        ∀ unit, law.unit = some unit → unit ≠ label ∧ operations unit [] = fold.fold [])
      {arguments : List Pattern} {values : List A}
      (computed : arguments.mapM (read? operations assignment label kind fold) = some values) :
      (arguments.map (CollectionLaws.normalize laws)).mapM (read? operations assignment label kind fold) = some values := by
    cases arguments with
    | nil => exact computed
    | cons argument arguments =>
      cases first : read? operations assignment label kind fold argument with
      | none => simp [List.mapM_cons, first] at computed
      | some value =>
        cases remaining : arguments.mapM (read? operations assignment label kind fold) with
        | none => simp [List.mapM_cons, first, remaining] at computed
        | some rest =>
          have headRead := read_normalize operations assignment label kind fold laws units first
          have tailRead := arguments_normalize operations assignment label kind fold laws units remaining
          simpa only [List.mapM_cons, first, remaining, List.map_cons, headRead, tailRead] using computed
  termination_by sizeOf arguments
  decreasing_by all_goals sizeOf_pattern_dec
end

theorem read_lawNormal (operations : String → List A → A) (assignment : String → A)
    (label : String) (kind : CollType) (fold : Mettapedia.Algebra.Collections.Folds.Model A)
    (laws : List Laws)
    (units : ∀ law, lawFor laws kind = some law →
      ∀ unit, law.unit = some unit → unit ≠ label ∧ operations unit [] = fold.fold [])
    (arranged : ∀ (interpret : Pattern → A) (elements : List Pattern),
      fold.fold ((arrange kind elements).map interpret) = fold.fold (elements.map interpret))
    {pattern : Pattern} {value : A}
    (computed : read? operations assignment label kind fold pattern = some value) :
    read? operations assignment label kind fold (lawNormal laws pattern) = some value :=
  read_canon operations assignment label kind fold arranged
    (read_normalize operations assignment label kind fold laws units computed)


/-- Law-equivalent presentations have equal values wherever the selected
first-order interpretation is defined. Normalization witnesses are not
additional interpreted events. -/
theorem read_lawSame (operations : String → List A → A) (assignment : String → A)
    (label : String) (kind : CollType) (fold : Mettapedia.Algebra.Collections.Folds.Model A)
    (laws : List Laws)
    (units : ∀ law, lawFor laws kind = some law →
      ∀ unit, law.unit = some unit → unit ≠ label ∧ operations unit [] = fold.fold [])
    (arranged : ∀ (interpret : Pattern → A) (elements : List Pattern),
      fold.fold ((arrange kind elements).map interpret) = fold.fold (elements.map interpret))
    {left right : Pattern} {first second : A}
    (related : Relation.EqvGen (LawStep laws) left right)
    (leftRead : read? operations assignment label kind fold left = some first)
    (rightRead : read? operations assignment label kind fold right = some second) : first = second := by
  have leftNormal := read_lawNormal operations assignment label kind fold laws units arranged leftRead
  have rightNormal := read_lawNormal operations assignment label kind fold laws units arranged rightRead
  rw [(lawNormal_iff laws left right).mpr related] at leftNormal
  exact Option.some.inj (leftNormal.symm.trans rightNormal)

/-- Actual authoring success and the source equations construct one model
for packing and canonical arrangement. Only declaration-level table and
fresh-label checks are requested; no preservation conclusion is assumed. -/
theorem replacement_model {value result : Value} {row : Replacement} {item : Item}
    {old : GrammarRule} {name sort : String} {kind : CollType}
    (accepted : replaceRow value row = .ok result)
    (selected : value.entries.find? (·.label == (.term, row.old)) = some item)
    (body : item.body = .term old)
    (coherent : TermLabelsCoherent value) (valid : ModuleAlgebra.Valid value.entries.toFinset)
    (sourceName targetName : String)
    (notCollection : collectionParameterKind old = none)
    (named : namedArguments? old row.rule = false)
    (shape : row.rule.params = [.simple name (.collection kind (.base sort))])
    (representation : checkRepresentation (flattenRaw sourceName value) (flattenRaw targetName result)
      old row.rule kind = true)
    (fresh : checkFreshLabel (flattenRaw sourceName value) old row.rule = true)
    (operations : String → List A → A)
    (holds : AlgebraInterpretation.SourceEquationsHold operations value) :
    ∃ unit : String, ∃ fold : Mettapedia.Algebra.Collections.Folds.Model A,
      fold.fold [] = operations unit [] ∧
      (∀ first second, fold.fold [first, second] = operations old.label [first, second]) ∧
      (∀ (interpret : Pattern → A) (elements : List Pattern),
        fold.fold ((CanonicalBags.arrange kind elements).map interpret) =
          fold.fold (elements.map interpret)) ∧
      ∀ (assignment : String → A) (free : FreeTypeContext) (bound : List TypeExpr)
        (pattern : Pattern) (type : TypeExpr) (answer : A),
        HasType (flattenRaw sourceName value) free bound pattern type →
        AlgebraInterpretation.read? operations assignment pattern = some answer →
        read? operations assignment row.rule.label kind fold
          (translated (flattenRaw targetName result) old row.rule kind pattern) = some answer ∧
        read? operations assignment row.rule.label kind fold
          (canon (translated (flattenRaw targetName result) old row.rule kind pattern)) = some answer := by
  obtain ⟨actual, _, actualLabel, _, checked, signature⟩ :=
    signature_of_replaceRow value row accepted coherent valid sourceName targetName
  have member := List.mem_of_find?_eq_some selected
  have key : item.label = (.term, row.old) := by simpa using List.find?_some selected
  have oldLabel : old.label = row.old :=
    (Prod.mk.inj ((coherent item member old body).symm.trans key)).2
  have same := signature.unique old ((raw_term_member _ _ _).mpr ⟨item, member, body⟩)
    (oldLabel.trans actualLabel.symm)
  subst actual
  obtain ⟨unit, fold, empty, binary, permutation, membership⟩ :=
    AlgebraInterpretation.replacement_collection_fold_model accepted selected body notCollection shape holds
  refine ⟨unit, fold, empty, binary, fold_arrange fold kind permutation membership, ?_⟩
  intro assignment free bound pattern type answer typed computed
  have interpreted := read_translated signature ((checkRepresentation_iff _ _ _ _ _).mp representation)
    checked named shape fresh operations assignment fold binary free bound typed computed
  exact ⟨interpreted, read_canon operations assignment row.rule.label kind fold
    (fold_arrange fold kind permutation membership) interpreted⟩

/-- Every typed first-order source equation is transported in every source
equation model supplied to `replacement_model`, including equations enclosing
several nested occurrences of the selected operation. -/
theorem equation_read_translated (signature : Signature source target old new)
    (representation : Representation source target old new kind)
    (checked : checkReplacementTyping old new = true)
    (named : namedArguments? old new = false)
    (shape : new.params = [.simple name (.collection kind (.base sort))])
    (fresh : checkFreshLabel source old new = true)
    (operations : String → List A → A)
    (fold : Mettapedia.Algebra.Collections.Folds.Model A)
    (binary : ∀ first second, fold.fold [first, second] = operations old.label [first, second])
    (free : FreeTypeContext) (bound : List TypeExpr) {left right : Pattern} {type : TypeExpr}
    (leftTyped : HasType source free bound left type) (rightTyped : HasType source free bound right type)
    (holds : AlgebraInterpretation.EquationHolds operations left right) :
    ∀ assignment, ∃ value,
      read? operations assignment new.label kind fold (translated target old new kind left) = some value ∧
      read? operations assignment new.label kind fold (translated target old new kind right) = some value := by
  intro assignment
  obtain ⟨value, leftRead, rightRead⟩ := holds assignment
  exact ⟨value,
    read_translated signature representation checked named shape fresh operations assignment fold binary
      free bound leftTyped leftRead,
    read_translated signature representation checked named shape fresh operations assignment fold binary
      free bound rightTyped rightRead⟩

/-- Typed source equations retain their value after the actual replacement
traversal and the existing law normalizer. The unit and arrangement laws are
those of the selected carrier interpretation. -/
theorem equation_read_lawNormal (signature : Signature source target old new)
    (representation : Representation source target old new kind)
    (checked : checkReplacementTyping old new = true)
    (named : namedArguments? old new = false)
    (shape : new.params = [.simple name (.collection kind (.base sort))])
    (fresh : checkFreshLabel source old new = true)
    (operations : String → List A → A)
    (fold : Mettapedia.Algebra.Collections.Folds.Model A)
    (binary : ∀ first second, fold.fold [first, second] = operations old.label [first, second])
    (laws : List Laws)
    (units : ∀ law, lawFor laws kind = some law →
      ∀ unit, law.unit = some unit → unit ≠ new.label ∧ operations unit [] = fold.fold [])
    (arranged : ∀ (interpret : Pattern → A) (elements : List Pattern),
      fold.fold ((arrange kind elements).map interpret) = fold.fold (elements.map interpret))
    (free : FreeTypeContext) (bound : List TypeExpr) {left right : Pattern} {type : TypeExpr}
    (leftTyped : HasType source free bound left type) (rightTyped : HasType source free bound right type)
    (holds : AlgebraInterpretation.EquationHolds operations left right) :
    ∀ assignment, ∃ value,
      read? operations assignment new.label kind fold (lawNormal laws (translated target old new kind left)) = some value ∧
      read? operations assignment new.label kind fold (lawNormal laws (translated target old new kind right)) = some value := by
  intro assignment
  obtain ⟨value, leftRead, rightRead⟩ := equation_read_translated signature representation checked named shape fresh
    operations fold binary free bound leftTyped rightTyped holds assignment
  exact ⟨value, read_lawNormal operations assignment new.label kind fold laws units arranged leftRead,
    read_lawNormal operations assignment new.label kind fold laws units arranged rightRead⟩


/-! ## The full source-equational bag normal form in the earned model -/

private theorem read_filtered_units (operations : String → List A → A) (assignment : String → A)
    (label unit : String) (fold : Mettapedia.Algebra.Collections.Folds.Model A)
    (different : unit ≠ label) (empty : operations unit [] = fold.fold [])
    {patterns : List Pattern} {values : List A}
    (computed : patterns.mapM (read? operations assignment label .hashBag fold) = some values) :
    ∃ kept,
      (patterns.filter fun pattern => decide (pattern ≠ .apply unit [])).mapM
        (read? operations assignment label .hashBag fold) = some kept ∧
      fold.fold kept = fold.fold values := by
  induction patterns generalizing values with
  | nil =>
      have same : values = [] := (Option.some.inj computed).symm
      exact ⟨[], rfl, congrArg fold.fold same.symm⟩
  | cons pattern patterns ih =>
      cases first : read? operations assignment label .hashBag fold pattern with
      | none => simp [List.mapM_cons, first] at computed
      | some value =>
        cases remaining : patterns.mapM (read? operations assignment label .hashBag fold) with
        | none => simp [List.mapM_cons, first, remaining] at computed
        | some rest =>
          have same : value :: rest = values := by
            simpa only [List.mapM_cons, first, remaining, bind, pure, Option.bind, Option.some.injEq] using computed
          subst values
          obtain ⟨kept, reads, folded⟩ := ih remaining
          by_cases selected : pattern = .apply unit []
          · subst pattern
            have unitValue : value = fold.fold [] := by
              simpa only [read?, List.mapM_nil, bind, pure, Option.bind,
                if_neg different, empty, Option.some.injEq] using first.symm
            refine ⟨kept, ?_, ?_⟩
            · simpa only [List.filter_cons, ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true,
                ↓reduceIte] using reads
            · rw [folded, fold.fold_cons, unitValue, fold.fold_left_unit]
          · refine ⟨value :: kept, ?_, ?_⟩
            · have test : decide (pattern ≠ .apply unit []) = true := by simp [selected]
              simp only [List.filter_cons, test, ↓reduceIte, List.mapM_cons, first, reads]
              rfl
            · calc
                fold.fold (value :: kept) = fold.fold [value, fold.fold kept] := fold.fold_cons _ _
                _ = fold.fold [value, fold.fold rest] := by rw [folded]
                _ = fold.fold (value :: rest) := (fold.fold_cons _ _).symm

private theorem bag_splice_eq (pattern : Pattern) :
    BagNormalForm.splice pattern = CollectionLaws.splice ⟨.hashBag,none⟩ pattern := by
  cases pattern with
  | collection kind elements rest => cases kind <;> cases rest <;> simp [BagNormalForm.splice, CollectionLaws.splice]
  | apply label arguments => cases arguments <;> simp [BagNormalForm.splice, CollectionLaws.splice]
  | _ => rfl

private theorem read_bag_contents (operations : String → List A → A) (assignment : String → A)
    (label unit : String) (fold : Mettapedia.Algebra.Collections.Folds.Model A)
    (different : unit ≠ label) (empty : operations unit [] = fold.fold [])
    {patterns : List Pattern} {values : List A}
    (computed : patterns.mapM (read? operations assignment label .hashBag fold) = some values) :
    ∃ kept, (BagNormalForm.bagContents unit patterns).mapM
      (read? operations assignment label .hashBag fold) = some kept ∧
      fold.fold kept = fold.fold values := by
  obtain ⟨spliced, reads, folded⟩ := read_spliced_list operations assignment label .hashBag fold
    ⟨.hashBag,none⟩ rfl (by intro identifier impossible; cases impossible) computed
  obtain ⟨kept, keptReads, keptFold⟩ := read_filtered_units operations assignment label unit fold different empty reads
  refine ⟨kept, ?_, keptFold.trans folded⟩
  simpa only [BagNormalForm.bagContents, funext bag_splice_eq] using keptReads

private theorem read_sort (operations : String → List A → A) (assignment : String → A)
    (label : String) (fold : Mettapedia.Algebra.Collections.Folds.Model A)
    (permutation : fold.PermutationInvariant) {patterns : List Pattern} {values : List A}
    (computed : patterns.mapM (read? operations assignment label .hashBag fold) = some values) :
    ∃ sorted, (PatternCode.sortPatterns patterns).mapM
      (read? operations assignment label .hashBag fold) = some sorted ∧
      fold.fold sorted = fold.fold values := by
  let read := read? operations assignment label .hashBag fold
  let fallback := fold.fold []
  let interpret := fun pattern => (read pattern).getD fallback
  have defined := mapM_defined read computed
  have original := mapM_getD read fallback patterns defined
  have sameValues : patterns.map interpret = values := Option.some.inj (original.symm.trans computed)
  have sorted := mapM_getD read fallback (PatternCode.sortPatterns patterns)
    (fun pattern member => defined pattern ((BagNormalForm.sortPatterns_perm patterns).mem_iff.mp member))
  exact ⟨_, sorted, (permutation _ _ ((BagNormalForm.sortPatterns_perm patterns).map interpret)).trans
    (congrArg fold.fold sameValues)⟩

private theorem read_collapse (operations : String → List A → A) (assignment : String → A)
    (label unit : String) (fold : Mettapedia.Algebra.Collections.Folds.Model A)
    (different : unit ≠ label) (empty : operations unit [] = fold.fold [])
    {patterns : List Pattern} {values : List A}
    (computed : patterns.mapM (read? operations assignment label .hashBag fold) = some values) :
    read? operations assignment label .hashBag fold (BagNormalForm.collapse unit patterns) =
      some (fold.fold values) := by
  cases patterns with
  | nil =>
      have same : values = [] := (Option.some.inj computed).symm
      subst values
      simp only [BagNormalForm.collapse, read?, List.mapM_nil, bind, pure, Option.bind,
        if_neg different, empty]
  | cons pattern patterns =>
      cases patterns with
      | nil =>
          cases first : read? operations assignment label .hashBag fold pattern with
          | none => simp [List.mapM_cons,first] at computed
          | some value =>
              have same : values = [value] := by
                simpa only [List.mapM_cons, first, List.mapM_nil, bind, pure, Option.bind, Option.some.injEq] using computed.symm
              simpa only [BagNormalForm.collapse, same, fold.singleton] using first
      | cons second rest =>
          simpa only [BagNormalForm.collapse, read?, ↓reduceIte, Option.map_some] using congrArg (Option.map fold.fold) computed

private theorem read_normalizeBag (operations : String → List A → A) (assignment : String → A)
    (label unit : String) (fold : Mettapedia.Algebra.Collections.Folds.Model A)
    (different : unit ≠ label) (empty : operations unit [] = fold.fold [])
    (permutation : fold.PermutationInvariant) {patterns : List Pattern} {values : List A}
    (computed : patterns.mapM (read? operations assignment label .hashBag fold) = some values) :
    read? operations assignment label .hashBag fold (BagNormalForm.normalizeBag (some unit) patterns) =
      some (fold.fold values) := by
  obtain ⟨kept, keptReads, keptFold⟩ := read_bag_contents operations assignment label unit fold different empty computed
  obtain ⟨sorted, sortedReads, sortedFold⟩ := read_sort operations assignment label fold permutation keptReads
  simpa only [BagNormalForm.normalizeBag, sortedFold, keptFold] using
    read_collapse operations assignment label unit fold different empty sortedReads

mutual
  /-- The existing full bag normal form, including empty and singleton
  collapse, preserves every defined interpretation in the earned bag fold. -/
  theorem read_bagNormalForm (operations : String → List A → A) (assignment : String → A)
      (label unit : String) (fold : Mettapedia.Algebra.Collections.Folds.Model A)
      (different : unit ≠ label) (empty : operations unit [] = fold.fold [])
      (permutation : fold.PermutationInvariant) {pattern : Pattern} {value : A}
      (computed : read? operations assignment label .hashBag fold pattern = some value) :
      read? operations assignment label .hashBag fold
        (BagNormalForm.normalForm (some unit) pattern) = some value := by
    cases pattern with
    | fvar atom => simpa only [BagNormalForm.normalForm] using computed
    | apply head arguments =>
        cases values : arguments.mapM (read? operations assignment label .hashBag fold) with
        | none => simp only [read?, values] at computed; cases computed
        | some values' =>
            have normalized := arguments_bagNormalForm operations assignment label unit fold different empty permutation values
            simpa only [BagNormalForm.normalForm_apply, read?, values, normalized] using computed
    | collection actual elements rest =>
        cases rest with
        | some _ => simp only [read?] at computed; cases computed
        | none =>
            by_cases selected : actual = .hashBag
            · subst actual
              cases values : elements.mapM (read? operations assignment label .hashBag fold) with
              | none => simp only [read?, ↓reduceIte, values, Option.map_none] at computed; cases computed
              | some values' =>
                  have normalized := arguments_bagNormalForm operations assignment label unit fold different empty permutation values
                  have folded : fold.fold values' = value := by
                    simpa only [read?, ↓reduceIte, values, Option.map_some, Option.some.injEq] using computed
                  simpa only [BagNormalForm.normalForm_bag, folded] using
                    read_normalizeBag operations assignment label unit fold different empty permutation normalized
            · simp only [read?, if_neg selected] at computed; cases computed
    | bvar | lambda | multiLambda | subst => simp only [read?] at computed; cases computed
  termination_by sizeOf pattern
  decreasing_by all_goals sizeOf_pattern_dec

  theorem arguments_bagNormalForm (operations : String → List A → A) (assignment : String → A)
      (label unit : String) (fold : Mettapedia.Algebra.Collections.Folds.Model A)
      (different : unit ≠ label) (empty : operations unit [] = fold.fold [])
      (permutation : fold.PermutationInvariant) {arguments : List Pattern} {values : List A}
      (computed : arguments.mapM (read? operations assignment label .hashBag fold) = some values) :
      (arguments.map (BagNormalForm.normalForm (some unit))).mapM
        (read? operations assignment label .hashBag fold) = some values := by
    cases arguments with
    | nil => exact computed
    | cons argument arguments =>
        cases first : read? operations assignment label .hashBag fold argument with
        | none => simp [List.mapM_cons,first] at computed
        | some value =>
            cases remaining : arguments.mapM (read? operations assignment label .hashBag fold) with
            | none => simp [List.mapM_cons,first,remaining] at computed
            | some rest =>
                have headRead := read_bagNormalForm operations assignment label unit fold different empty permutation first
                have tailRead := arguments_bagNormalForm operations assignment label unit fold different empty permutation remaining
                simpa only [List.mapM_cons,first,remaining,List.map_cons,headRead,tailRead] using computed
  termination_by sizeOf arguments
  decreasing_by all_goals sizeOf_pattern_dec
end


/-- Equality after actual binary packing, unwrapping and full bag
normalization reflects the original source equation theory. The model is
constructed from that theory's actual quotient, rather than supplied as a
separation or preservation assumption. -/
theorem replacement_reflects_bagNormalForm {value result : Value} {row : Replacement} {item : Item}
    {old : GrammarRule} {parameter sort : String}
    (accepted : replaceRow value row = .ok result)
    (selected : value.entries.find? (·.label == (.term, row.old)) = some item)
    (body : item.body = .term old)
    (coherent : TermLabelsCoherent value) (valid : ModuleAlgebra.Valid value.entries.toFinset)
    (sourceName targetName : String)
    (notCollection : collectionParameterKind old = none)
    (named : namedArguments? old row.rule = false)
    (shape : row.rule.params = [.simple parameter (.collection .hashBag (.base sort))])
    (representation : checkRepresentation (flattenRaw sourceName value) (flattenRaw targetName result)
      old row.rule .hashBag = true)
    (fresh : checkFreshLabel (flattenRaw sourceName value) old row.rule = true)
    (base : ContextualStep.BasePremiseEvaluator)
    (sourceRows : ∀ equation ∈ (flattenRaw sourceName value).equations, equation.premises = [] →
      GeneralFirstOrderProjection.FirstOrder equation.left ∧
      GeneralFirstOrderProjection.FirstOrder equation.right ∧
        ∀ identifier ∈ equation.right.freeFvarNames, identifier ∈ equation.left.freeFvarNames)
    (unit : String) (onLeft : Bool) (unitMember : (unit,onLeft) ∈ binaryUnits value old.label)
    (unitDifferent : unit ≠ row.rule.label)
    (free : FreeTypeContext) (bound : List TypeExpr) {left right : Pattern} {type : TypeExpr}
    (leftTyped : HasType (flattenRaw sourceName value) free bound left type)
    (rightTyped : HasType (flattenRaw sourceName value) free bound right type)
    (leftShape : GeneralFirstOrderProjection.FirstOrder left)
    (rightShape : GeneralFirstOrderProjection.FirstOrder right)
    (equal : BagNormalForm.normalForm (some unit)
        (translated (flattenRaw targetName result) old row.rule .hashBag left) =
      BagNormalForm.normalForm (some unit)
        (translated (flattenRaw targetName result) old row.rule .hashBag right)) :
    EquationSemantics.EquationEquiv base (flattenRaw sourceName value) left right := by
  let operations := AlgebraInterpretation.SourceQuotient.operations base (flattenRaw sourceName value)
  let assignment := fun identifier =>
    AlgebraInterpretation.SourceQuotient.classOf base (flattenRaw sourceName value) (.fvar identifier)
  have holds : AlgebraInterpretation.SourceEquationsHold operations value :=
    AlgebraInterpretation.SourceQuotient.sourceEquationsHold base sourceName value sourceRows
  obtain ⟨_, fold, _, binary, _, interpreted⟩ := replacement_model accepted selected body coherent valid
    sourceName targetName notCollection named shape representation fresh operations holds
  have faithful : checkFaithful value old row.rule = .ok () := by
    obtain ⟨actualItem, actualRule, _, found, actualBody, _, _, admitted⟩ :=
      replaceRow_typing_readout value row accepted
    have sameItem : actualItem = item := Option.some.inj (found.symm.trans selected)
    subst actualItem
    have sameRule : actualRule = old := Decl.term.inj (actualBody.symm.trans body)
    subst actualRule
    exact admitted
  have basis := AlgebraInterpretation.checkFaithful_collection_basis notCollection shape faithful
  have permutation : fold.PermutationInvariant := by
    apply fold.permutationInvariant_iff.mpr
    obtain ⟨equationLeft, equationRight, checked, semantic⟩ :=
      AlgebraInterpretation.recognized_equation holds (basis.2.2.1 (by decide))
    intro first second
    rw [binary,binary]
    exact AlgebraInterpretation.binary_commutativity_sound operations checked semantic first second
  have empty : operations unit [] = fold.fold [] := by
    have unitLaw := AlgebraInterpretation.binaryUnits_sound holds unitMember (fold.fold [])
    cases onLeft with
    | false =>
        simpa only [Bool.false_eq_true, ↓reduceIte, ← binary, fold.fold_left_unit] using unitLaw
    | true =>
        simpa only [↓reduceIte, ← binary, fold.fold_right_unit] using unitLaw
  have leftRead := (interpreted assignment free bound left type _ leftTyped
    (AlgebraInterpretation.SourceQuotient.read_classOf base _ leftShape)).1
  have rightRead := (interpreted assignment free bound right type _ rightTyped
    (AlgebraInterpretation.SourceQuotient.read_classOf base _ rightShape)).1
  have leftNormal := read_bagNormalForm operations assignment row.rule.label unit fold
    unitDifferent empty permutation leftRead
  have rightNormal := read_bagNormalForm operations assignment row.rule.label unit fold
    unitDifferent empty permutation rightRead
  rw [equal] at leftNormal
  exact Quotient.exact (Option.some.inj (leftNormal.symm.trans rightNormal))


/-! ## Forward source-equation transport -/

/-- An internal source observer built from the existing packing and unwrap
operations. Every selected source constructor is packed before unwrapping;
no target constructor label is recognized in unrelated raw source syntax. -/
def projectBinary (label : String) (pattern : Pattern) : Pattern :=
  CoreReduction.unwrap [(label,.hashBag)]
    (renameConstructor label label (packing .hashBag) pattern)

@[simp] theorem projectBinary_fvar (label identifier : String) :
    projectBinary label (.fvar identifier) = .fvar identifier := by
  simp only [projectBinary,renameConstructor,CoreReduction.unwrap]

@[simp] theorem projectBinary_apply (label head : String) (arguments : List Pattern) :
    projectBinary label (.apply head arguments) =
      if head = label then .collection .hashBag (arguments.map (projectBinary label)) none
      else .apply head (arguments.map (projectBinary label)) := by
  by_cases selected : head = label
  · subst head
    simp [projectBinary,renameConstructor,packing,CoreReduction.unwrap,List.lookup]
  · have test : (head == label) = false := by simp [selected]
    simp [projectBinary,renameConstructor,selected,CoreReduction.unwrap,List.lookup,test,Function.comp_def]

@[simp] theorem projectBinary_lambda (label : String) (binder : Option String) (body : Pattern) :
    projectBinary label (.lambda binder body) = .lambda binder (projectBinary label body) := by
  simp only [projectBinary,renameConstructor,CoreReduction.unwrap]
@[simp] theorem projectBinary_multiLambda (label : String) (arity : Nat) (binders : List String) (body : Pattern) :
    projectBinary label (.multiLambda arity binders body) = .multiLambda arity binders (projectBinary label body) := by
  simp only [projectBinary,renameConstructor,CoreReduction.unwrap]
@[simp] theorem projectBinary_subst (label : String) (body replacement : Pattern) :
    projectBinary label (.subst body replacement) =
      .subst (projectBinary label body) (projectBinary label replacement) := by
  simp only [projectBinary,renameConstructor,CoreReduction.unwrap]
@[simp] theorem projectBinary_collection (label : String) (kind : CollType)
    (elements : List Pattern) (rest : Option String) :
    projectBinary label (.collection kind elements rest) =
      .collection kind (elements.map (projectBinary label)) rest := by
  simp only [projectBinary,renameConstructor,CoreReduction.unwrap,List.map_map,Function.comp_def]
  rfl

open DerivedContexts in
private def projectedContext (label : String) : OneHoleContext → OneHoleContext
  | .hole => .hole
  | .apply head before inner after =>
      if head = label then .collection .hashBag (before.map (projectBinary label))
        (projectedContext label inner) (after.map (projectBinary label)) none
      else .apply head (before.map (projectBinary label))
        (projectedContext label inner) (after.map (projectBinary label))
  | .lambda binder inner => .lambda binder (projectedContext label inner)
  | .multiLambda arity binders inner => .multiLambda arity binders (projectedContext label inner)
  | .substBody inner replacement => .substBody (projectedContext label inner) (projectBinary label replacement)
  | .substReplacement body inner => .substReplacement (projectBinary label body) (projectedContext label inner)
  | .collection kind before inner after rest => .collection kind (before.map (projectBinary label))
      (projectedContext label inner) (after.map (projectBinary label)) rest

open DerivedContexts in
private theorem projectBinary_fill (label : String) (context : OneHoleContext) (pattern : Pattern) :
    projectBinary label (context.fill pattern) = (projectedContext label context).fill (projectBinary label pattern) := by
  induction context with
  | hole => rfl
  | apply head before inner after ih =>
      by_cases selected : head = label <;>
        simp only [OneHoleContext.fill,projectBinary_apply,selected,↓reduceIte,
          projectedContext,List.map_append,List.map_cons,ih]
  | lambda binder inner ih => simp only [OneHoleContext.fill,projectBinary_lambda,projectedContext,ih]
  | multiLambda arity binders inner ih => simp only [OneHoleContext.fill,projectBinary_multiLambda,projectedContext,ih]
  | substBody inner replacement ih => simp only [OneHoleContext.fill,projectBinary_subst,projectedContext,ih]
  | substReplacement body inner ih => simp only [OneHoleContext.fill,projectBinary_subst,projectedContext,ih]
  | collection kind before inner after rest ih =>
      simp only [OneHoleContext.fill,projectBinary_collection,projectedContext,List.map_append,List.map_cons,ih]

/-- The internal observer respects every raw structural context. This is a
static equation fact, not permission to fire a rewrite under that context. -/
theorem projectBinary_normalForm_fill (label unit : String) (context : DerivedContexts.OneHoleContext)
    {first second : Pattern}
    (same : BagNormalForm.normalForm (some unit) (projectBinary label first) =
      BagNormalForm.normalForm (some unit) (projectBinary label second)) :
    BagNormalForm.normalForm (some unit) (projectBinary label (context.fill first)) =
      BagNormalForm.normalForm (some unit) (projectBinary label (context.fill second)) := by
  rw [projectBinary_fill,projectBinary_fill]
  exact BagNormalForm.normalForm_fill_congr _ _ same

mutual
  /-- On typed first-order source terms, the internal observer is exactly the
  actual target-label replacement and representation unwrapping. -/
  theorem translated_eq_projectBinary
      (representation : Representation source target old new .hashBag)
      (bare : new.collectionRepresentation = .bare)
      {free : FreeTypeContext} {bound : List TypeExpr} {pattern : Pattern} {type : TypeExpr}
      (typed : HasType source free bound pattern type)
      (shape : GeneralFirstOrderProjection.FirstOrder pattern) :
      translated target old new .hashBag pattern = projectBinary old.label pattern := by
    cases typed with
    | fvar lookup => simp only [translated,renameConstructor,CoreReduction.unwrap,projectBinary_fvar]
    | @constructor bound rule arguments member ordinary argumentsTyped =>
        cases shape with
        | constructor _ _ children =>
            have mapped := arguments_projectBinary representation bare argumentsTyped children
            by_cases selected : rule.label = old.label
            · have lookup : (CoreReduction.bareLabels target).lookup new.label = some .hashBag := by
                simpa only [bare,↓reduceIte] using representation.selected
              simpa only [translated,renameConstructor,selected,↓reduceIte,packing,CoreReduction.unwrap,
                lookup,List.map_cons,List.map_nil,List.map_map,Function.comp_def,projectBinary_apply,↓reduceIte] using
                congrArg (fun elements => Pattern.collection .hashBag elements none) mapped
            · have lookup := representation.retained rule member selected ordinary
              simpa only [translated,renameConstructor,if_neg selected,CoreReduction.unwrap,lookup,
                List.map_map,Function.comp_def,projectBinary_apply,if_neg selected] using
                congrArg (Pattern.apply rule.label) mapped
    | bvar | lambda | multiLambda | subst | collection | collectionConstructor => cases shape
  termination_by sizeOf pattern

  theorem arguments_projectBinary
      (representation : Representation source target old new .hashBag)
      (bare : new.collectionRepresentation = .bare)
      {free : FreeTypeContext} {bound : List TypeExpr} {arguments : List Pattern} {parameters : List TermParam}
      (typed : ArgumentsHaveTypes source free bound arguments parameters)
      (shapes : ∀ argument ∈ arguments, GeneralFirstOrderProjection.FirstOrder argument) :
      arguments.map (translated target old new .hashBag) = arguments.map (projectBinary old.label) := by
    cases typed with
    | nil => rfl
    | cons represented declared first rest =>
        simp only [List.map_cons]
        rw [translated_eq_projectBinary representation bare first (shapes _ (by simp)),
          arguments_projectBinary representation bare rest
            (fun argument member => shapes argument (List.mem_cons_of_mem _ member))]
  termination_by sizeOf arguments
end

/-- Local generator certificates lift through all raw equation contexts.
The source's actual absence of collection laws is checked separately from
its authored equation instances. -/
theorem projectBinary_equationEquiv (label unit : String)
    (base : ContextualStep.BasePremiseEvaluator) (language : LanguageDef)
    (plain : EquationSemantics.PlainEquations language)
    (noBags : language.usesCollection .hashBag = false)
    (noSets : language.usesCollection .hashSet = false)
    (noAlgebra : language.hasAlgebraDeclarations = false)
    (rows : ∀ equation ∈ language.equations, ∀ bindings : Match.Bindings,
      BagNormalForm.normalForm (some unit) (projectBinary label (Match.applyBindings bindings equation.left)) =
        BagNormalForm.normalForm (some unit) (projectBinary label (Match.applyBindings bindings equation.right)))
    {left right : Pattern} (equivalent : EquationSemantics.EquationEquiv base language left right) :
    BagNormalForm.normalForm (some unit) (projectBinary label left) =
      BagNormalForm.normalForm (some unit) (projectBinary label right) := by
  apply EquationSemantics.equationEquiv_invariant
    (fun pattern => BagNormalForm.normalForm (some unit) (projectBinary label pattern))
    (fun context _ _ same => projectBinary_normalForm_fill label unit context same) _ equivalent
  intro first second generator
  rcases generator with authored | derived
  · obtain ⟨equation,member,bindings,⟨rfl,rfl⟩|⟨rfl,rfl⟩⟩ :=
      EquationSemantics.equationInstance_sides plain authored
    · exact rows equation member bindings
    · exact (rows equation member bindings).symm
  · exact (EquationSemantics.no_derivedInstance_of_no_derived_laws noBags noSets noAlgebra _ _ derived).elim


private theorem normalForm_flatten_bag (unit : String) (before inner after : List Pattern) :
    BagNormalForm.normalForm (some unit)
      (.collection .hashBag (before ++ (.collection .hashBag inner none) :: after) none) =
      BagNormalForm.normalForm (some unit) (.collection .hashBag (before ++ inner ++ after) none) := by
  open BagNormalForm in
  rw [normalForm_bag,normalForm_bag]
  open BagNormalForm in
  apply normalizeBag_contents_perm
  open BagNormalForm in
  simp only [List.map_append,List.map_cons,bagContents_append,List.append_assoc]
  open BagNormalForm in
  rw [bagContents_cons unit (normalForm (some unit) (.collection .hashBag inner none))]
  refine List.Perm.append_left _ (List.Perm.append_right _ ?_)
  open BagNormalForm in
  rw [normalForm_bag]
  open BagNormalForm in
  simp only [normalizeBag]
  open BagNormalForm in
  rw [bagContents_collapse]
  · exact BagNormalForm.sortPatterns_perm _
  · intro component membership
    apply BagNormalForm.bagContents_spec (elements := inner.map (BagNormalForm.normalForm (some unit)))
    · intro element elementMember
      obtain ⟨original,_,rfl⟩ := List.mem_map.mp elementMember
      exact BagNormalForm.rootNormal_normalForm unit original
    · exact BagNormalForm.mem_sortPatterns.mp membership

/-- The source binary associativity schema preserves the existing full bag
normal form under arbitrary raw substitutions. -/
theorem projectBinary_associativity (label unit : String) (first second third : Pattern) :
    BagNormalForm.normalForm (some unit)
      (projectBinary label (.apply label [.apply label [first,second],third])) =
      BagNormalForm.normalForm (some unit)
        (projectBinary label (.apply label [first,.apply label [second,third]])) := by
  simp only [projectBinary_apply,↓reduceIte,List.map_cons,List.map_nil]
  exact (normalForm_flatten_bag unit [] [projectBinary label first,projectBinary label second]
      [projectBinary label third]).trans
    (normalForm_flatten_bag unit [projectBinary label first]
      [projectBinary label second,projectBinary label third] []).symm

theorem projectBinary_commutativity (label unit : String) (first second : Pattern) :
    BagNormalForm.normalForm (some unit) (projectBinary label (.apply label [first,second])) =
      BagNormalForm.normalForm (some unit) (projectBinary label (.apply label [second,first])) := by
  simp only [projectBinary_apply,↓reduceIte,List.map_cons,List.map_nil,BagNormalForm.normalForm_bag]
  exact BagNormalForm.normalizeBag_perm _ ((List.Perm.swap _ _ []).map _)

theorem projectBinary_unit (label unit : String) (different : unit ≠ label)
    (pattern : Pattern) (onLeft : Bool) :
    BagNormalForm.normalForm (some unit) (projectBinary label
      (.apply label (if onLeft then [.apply unit [],pattern] else [pattern,.apply unit []]))) =
      BagNormalForm.normalForm (some unit) (projectBinary label pattern) := by
  cases onLeft with
  | false =>
      simpa only [projectBinary_apply,Bool.false_eq_true,↓reduceIte,List.map_cons,List.map_nil,if_neg different,
        List.cons_append,List.nil_append] using
        (BagNormalForm.WithAuthoredEquations.normalForm_insert_unit unit [projectBinary label pattern] []).trans
          (BagNormalForm.WithAuthoredEquations.normalForm_singleton unit (projectBinary label pattern))
  | true =>
      simpa only [projectBinary_apply,Bool.false_eq_true,↓reduceIte,List.map_cons,List.map_nil,if_neg different,
        List.cons_append,List.nil_append] using
        (BagNormalForm.WithAuthoredEquations.normalForm_insert_unit unit [] [projectBinary label pattern]).trans
          (BagNormalForm.WithAuthoredEquations.normalForm_singleton unit (projectBinary label pattern))


/-- First-order source syntax produces closed collection boundaries and
canonical binder metadata under the existing packing observer. -/
theorem projectBinary_metadata (label : String) {pattern : Pattern}
    (shape : GeneralFirstOrderProjection.FirstOrder pattern) :
    (projectBinary label pattern).hasCanonicalBinderMetadata = true ∧
      isObjectPattern (projectBinary label pattern) = true := by
  induction pattern using Pattern.inductionOn with
  | hfvar identifier =>
      simp only [projectBinary_fvar,Pattern.hasCanonicalBinderMetadata,isObjectPattern,and_self]
  | happly head arguments ih =>
      cases shape with
      | constructor _ _ children =>
          have canonical : Pattern.hasCanonicalBinderMetadataList (arguments.map (projectBinary label)) = true := by
            apply BagNormalForm.hasCanonicalBinderMetadataList_iff.mpr
            intro image member
            obtain ⟨original,inside,rfl⟩ := List.mem_map.mp member
            exact (ih original inside (children original inside)).1
          have objects : isObjectPatternList (arguments.map (projectBinary label)) = true := by
            apply BagNormalForm.isObjectPatternList_iff.mpr
            intro image member
            obtain ⟨original,inside,rfl⟩ := List.mem_map.mp member
            exact (ih original inside (children original inside)).2
          by_cases selected : head = label <;>
            simp only [projectBinary_apply,selected,↓reduceIte,Pattern.hasCanonicalBinderMetadata,
              isObjectPattern,Option.isNone_none,Bool.true_and,canonical,objects,and_self]
  | hbvar | hlambda | hmultiLambda | hsubst | hcollection => cases shape

/-- Actual signature membership, representation and typing checks derive
lowered admissibility. Metadata and object shape are proved from the source
fragment; no endpoint admissibility conclusion is assumed. -/
theorem translated_admissible (signature : Signature source target old new)
    (representation : Representation source target old new .hashBag)
    (checked : checkReplacementTyping old new = true)
    (named : namedArguments? old new = false)
    (shape : new.params = [.simple name (.collection .hashBag (.base sort))])
    (bare : new.collectionRepresentation = .bare)
    {free : FreeTypeContext} {bound : List TypeExpr} {pattern : Pattern} {type : TypeExpr}
    (typed : HasType source free bound pattern type)
    (firstOrder : GeneralFirstOrderProjection.FirstOrder pattern) :
    BagNormalForm.Admissible target free bound type (translated target old new .hashBag pattern) := by
  have lowered := BinaryCollectionLowering.typed signature representation checked named shape free bound typed
  have metadata := projectBinary_metadata old.label firstOrder
  have same := translated_eq_projectBinary representation bare typed firstOrder
  exact ⟨lowered,same.symm ▸ metadata.1,same.symm ▸ metadata.2⟩

#print axioms projectBinary_metadata
#print axioms translated_admissible

#print axioms projectBinary_associativity
#print axioms projectBinary_commutativity
#print axioms projectBinary_unit
#print axioms projectBinary_normalForm_fill
#print axioms translated_eq_projectBinary
#print axioms projectBinary_equationEquiv

#print axioms replacement_reflects_bagNormalForm
#print axioms read_bagNormalForm
#print axioms arguments_bagNormalForm

#print axioms replacement_model
#print axioms read_canon
#print axioms read_normalize
#print axioms read_lawNormal
#print axioms read_lawSame
#print axioms equation_read_lawNormal

end Mettapedia.GSLT.LanguageDef.ModuleSource.BinaryCollectionInterpretation
