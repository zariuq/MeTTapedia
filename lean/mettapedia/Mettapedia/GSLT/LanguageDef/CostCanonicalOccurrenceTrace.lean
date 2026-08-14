import Mettapedia.GSLT.LanguageDef.CostSemanticAtom
import Mettapedia.OSLF.MeTTaIL.ReflectiveCanonicalKeyedSingleton

/-!
# Positional occurrences through keyed canonical phases

Keyed reflective canonicalization is bottom-up.  A selected free-variable
occurrence can therefore move when a parallel wrapper is flattened or
collapsed, and again when the surrounding Quote/Drop finisher fires.  Raw
pattern equality does not retain that movement, especially in the presence of
duplicates.

This module records one proof-relevant path between exact zipper occurrences.
The first constructors cover contextual lifting, singleton-parallel collapse,
and Quote/Drop finishing.  Later flatten/filter/sort constructors can extend the
same carrier without changing its consumers.
-/

namespace Mettapedia.GSLT.LanguageDef

open Mettapedia.OSLF.MeTTaIL.DerivedContexts
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.OSLF.MeTTaIL.Syntax

namespace Selects

/-- Lift one exact selected occurrence through an outer one-hole context. -/
theorem inContext {needle root : Pattern} {inner : OneHoleContext}
    (selected : Selects needle inner root) (outer : OneHoleContext) :
    Selects needle (outer.comp inner) (outer.fill root) := by
  induction outer with
  | hole =>
      change Selects needle inner root
      exact selected
  | apply constructor before outer after inductionHypothesis =>
      exact .apply inductionHypothesis
  | lambda binder outer inductionHypothesis =>
      exact .lambda inductionHypothesis
  | multiLambda arity binders outer inductionHypothesis =>
      exact .multiLambda inductionHypothesis
  | substBody outer replacement inductionHypothesis =>
      exact .substBody inductionHypothesis
  | substReplacement body outer inductionHypothesis =>
      exact .substReplacement inductionHypothesis
  | collection collectionType before outer after rest inductionHypothesis =>
      exact .collection inductionHypothesis

end Selects

namespace CostStaticFVarOccurrence

/-- Retain the exact positional occurrence while placing its root in an outer
one-hole context. -/
def inContext {root : Pattern} (occurrence : CostStaticFVarOccurrence root)
    (outer : OneHoleContext) :
    CostStaticFVarOccurrence (outer.fill root) where
  name := occurrence.name
  context := outer.comp occurrence.context
  selected := Selects.inContext occurrence.selected outer

@[simp]
theorem inContext_name {root : Pattern}
    (occurrence : CostStaticFVarOccurrence root) (outer : OneHoleContext) :
    (occurrence.inContext outer).name = occurrence.name :=
  rfl

/-- Transport an occurrence across root equality without changing its name or
zipper. -/
def castRoot {left right : Pattern} (equal : left = right)
    (occurrence : CostStaticFVarOccurrence left) :
    CostStaticFVarOccurrence right := by
  cases equal
  exact occurrence

@[simp]
theorem castRoot_name {left right : Pattern} (equal : left = right)
    (occurrence : CostStaticFVarOccurrence left) :
    (castRoot equal occurrence).name = occurrence.name := by
  cases equal
  rfl

end CostStaticFVarOccurrence

/-! ## Positional transport through list permutations -/

/-- A free-variable occurrence inside one exact member of a pattern list.
The finite position distinguishes repeated equal members, while the nested
occurrence distinguishes repeated variables inside that member. -/
structure CostStaticFVarListOccurrence (patterns : List Pattern) where
  position : Fin patterns.length
  occurrence : CostStaticFVarOccurrence (patterns.get position)

namespace CostStaticFVarListOccurrence

/-- Pull an exact occurrence in a permuted target list back to the source
position selected by `List.Perm.idxBij`.  This is proof-relevant even when
several list members are equal. -/
def pullbackPerm {source target : List Pattern}
    (permutation : target.Perm source)
    (targetOccurrence : CostStaticFVarListOccurrence target) :
    CostStaticFVarListOccurrence source where
  position := permutation.idxBij targetOccurrence.position
  occurrence := by
    have elementEquality :
        source.get (permutation.idxBij targetOccurrence.position) =
          target.get targetOccurrence.position :=
      permutation.getElem_idxBij_eq_getElem targetOccurrence.position
    exact elementEquality.symm ▸ targetOccurrence.occurrence

private theorem castRoot_name {left right : Pattern}
    (equal : left = right) (occurrence : CostStaticFVarOccurrence right) :
    (equal.symm ▸ occurrence).name = occurrence.name := by
  cases equal
  rfl

/-- Pullback through a permutation preserves the selected variable name. -/
theorem pullbackPerm_name {source target : List Pattern}
    (permutation : target.Perm source)
    (targetOccurrence : CostStaticFVarListOccurrence target) :
    (pullbackPerm permutation targetOccurrence).occurrence.name =
      targetOccurrence.occurrence.name := by
  unfold pullbackPerm
  apply castRoot_name
  exact permutation.getElem_idxBij_eq_getElem targetOccurrence.position

/-- Distinct target positions remain distinct after positional permutation
pullback.  Equal values and equal keys do not weaken this guarantee. -/
theorem pullbackPerm_position_injective {source target : List Pattern}
    (permutation : target.Perm source)
    {left right : CostStaticFVarListOccurrence target}
    (distinct : left.position ≠ right.position) :
    (pullbackPerm permutation left).position ≠
      (pullbackPerm permutation right).position := by
  intro equal
  exact distinct (permutation.idxBij_injective equal)

/-- A proof-relevant order-preserving list embedding.  Unlike `List.Sublist`,
this lives in `Type`, so its keep/skip decisions can compute exact positions. -/
inductive CostPositionalSublist : List Pattern → List Pattern → Type where
  | nil : CostPositionalSublist [] []
  | skip (head : Pattern) {source target : List Pattern}
      (rest : CostPositionalSublist target source) :
      CostPositionalSublist target (head :: source)
  | keep (head : Pattern) {source target : List Pattern}
      (rest : CostPositionalSublist target source) :
      CostPositionalSublist (head :: target) (head :: source)

namespace CostPositionalSublist

/-- The finite-index embedding computed by an explicit keep/skip trace. -/
def sourcePosition {source target : List Pattern}
    (embedding : CostPositionalSublist target source) :
    Fin target.length → Fin source.length :=
  match embedding with
  | .nil => Fin.elim0
  | .skip _ rest => fun position => Fin.succ (sourcePosition rest position)
  | .keep _ rest =>
      Fin.cases ⟨0, by simp⟩
        (fun position => Fin.succ (sourcePosition rest position))

/-- The explicit position embedding selects the same list member. -/
theorem sourcePosition_get {source target : List Pattern}
    (embedding : CostPositionalSublist target source)
    (position : Fin target.length) :
    source.get (sourcePosition embedding position) = target.get position := by
  induction embedding with
  | nil => exact Fin.elim0 position
  | skip head rest inductionHypothesis =>
      simpa [sourcePosition] using inductionHypothesis position
  | keep head rest inductionHypothesis =>
      refine Fin.cases ?_ (fun tailPosition => ?_) position
      · rfl
      · simpa [sourcePosition] using inductionHypothesis tailPosition

/-- The explicit position embedding never merges two retained positions. -/
theorem sourcePosition_injective {source target : List Pattern}
    (embedding : CostPositionalSublist target source) :
    Function.Injective (sourcePosition embedding) := by
  induction embedding with
  | nil =>
      intro position
      exact Fin.elim0 position
  | skip head rest inductionHypothesis =>
      intro left right equal
      apply inductionHypothesis
      exact Fin.succ_inj.mp equal
  | keep head rest inductionHypothesis =>
      intro left right equal
      cases left using Fin.cases with
      | zero =>
          cases right using Fin.cases with
          | zero => rfl
          | succ rightTail =>
              have impossible := congrArg Fin.val equal
              simp [sourcePosition] at impossible
      | succ leftTail =>
          cases right using Fin.cases with
          | zero => simp [sourcePosition] at equal
          | succ rightTail =>
              apply congrArg Fin.succ
              apply inductionHypothesis
              exact Fin.succ_inj.mp equal

/-- Pull an exact occurrence through an order-preserving embedding. -/
def pullback {source target : List Pattern}
    (embedding : CostPositionalSublist target source)
    (targetOccurrence : CostStaticFVarListOccurrence target) :
    CostStaticFVarListOccurrence source where
  position := sourcePosition embedding targetOccurrence.position
  occurrence := by
    have elementEquality :
        source.get (sourcePosition embedding targetOccurrence.position) =
          target.get targetOccurrence.position :=
      sourcePosition_get embedding targetOccurrence.position
    exact elementEquality.symm ▸ targetOccurrence.occurrence

/-- Order-preserving pullback retains the selected variable name. -/
theorem pullback_name {source target : List Pattern}
    (embedding : CostPositionalSublist target source)
    (targetOccurrence : CostStaticFVarListOccurrence target) :
    (pullback embedding targetOccurrence).occurrence.name =
      targetOccurrence.occurrence.name := by
  unfold pullback
  apply castRoot_name
  exact sourcePosition_get embedding targetOccurrence.position

/-- Order-preserving pullback cannot merge distinct positions. -/
theorem pullback_position_injective {source target : List Pattern}
    (embedding : CostPositionalSublist target source)
    {left right : CostStaticFVarListOccurrence target}
    (distinct : left.position ≠ right.position) :
    (pullback embedding left).position ≠
      (pullback embedding right).position := by
  intro equal
  exact distinct (sourcePosition_injective embedding equal)

end CostPositionalSublist

/-- The proof-relevant keep/skip trace computed by Boolean filtering. -/
def filterPositionalSublist (keep : Pattern → Bool) :
    (patterns : List Pattern) →
      CostPositionalSublist (patterns.filter keep) patterns
  | [] => .nil
  | head :: tail =>
      if kept : keep head then
        by
          simpa [List.filter, kept] using
            CostPositionalSublist.keep head (filterPositionalSublist keep tail)
      else
        by
          simpa [List.filter, kept] using
            CostPositionalSublist.skip head (filterPositionalSublist keep tail)

/-- The unique block and the exact within-block occurrence selected by one
position of a flattened list. -/
structure FlatMapOccurrenceSource (expand : Pattern → List Pattern)
    (patterns : List Pattern) where
  sourcePosition : Fin patterns.length
  expandedOccurrence :
    CostStaticFVarListOccurrence (expand (patterns.get sourcePosition))

/-- Decompose an exact flattened-list position into its source-list position
and its exact position inside that source's expansion.  This computes from
lengths, so duplicate values cannot make the result ambiguous. -/
def flatMapOccurrenceSource (expand : Pattern → List Pattern) :
    (patterns : List Pattern) →
      CostStaticFVarListOccurrence (patterns.flatMap expand) →
        FlatMapOccurrenceSource expand patterns
  | [], occurrence => Fin.elim0 occurrence.position
  | head :: tail, occurrence => by
      by_cases inHead : occurrence.position.val < (expand head).length
      · let innerPosition : Fin (expand head).length :=
          ⟨occurrence.position.val, inHead⟩
        have elementEquality :
            (expand head).get innerPosition =
              ((head :: tail).flatMap expand).get occurrence.position := by
          symm
          exact List.getElem_append_left inHead
        exact
          { sourcePosition := ⟨0, by simp⟩
            expandedOccurrence :=
              { position := innerPosition
                occurrence :=
                  elementEquality ▸ occurrence.occurrence } }
      · let tailPosition : Fin (tail.flatMap expand).length :=
          ⟨occurrence.position.val - (expand head).length, by
            have bound : occurrence.position.val <
                (expand head).length + (tail.flatMap expand).length := by
              simpa [List.flatMap] using occurrence.position.isLt
            exact Nat.sub_lt_left_of_lt_add (Nat.le_of_not_gt inHead) bound⟩
        have elementEquality :
            (tail.flatMap expand).get tailPosition =
              ((head :: tail).flatMap expand).get occurrence.position := by
          symm
          exact List.getElem_append_right (by simpa using Nat.le_of_not_gt inHead)
        let tailOccurrence :
            CostStaticFVarListOccurrence (tail.flatMap expand) :=
          { position := tailPosition
            occurrence := elementEquality ▸ occurrence.occurrence }
        let source := flatMapOccurrenceSource expand tail tailOccurrence
        exact
          { sourcePosition := Fin.succ source.sourcePosition
            expandedOccurrence := by
              simpa using source.expandedOccurrence }

/-- Flattened-list decomposition preserves the selected variable name. -/
theorem flatMapOccurrenceSource_name (expand : Pattern → List Pattern)
    (patterns : List Pattern)
    (occurrence : CostStaticFVarListOccurrence (patterns.flatMap expand)) :
    (flatMapOccurrenceSource expand patterns occurrence
      ).expandedOccurrence.occurrence.name = occurrence.occurrence.name := by
  induction patterns with
  | nil => exact Fin.elim0 occurrence.position
  | cons head tail inductionHypothesis =>
      rw [flatMapOccurrenceSource]
      by_cases inHead : occurrence.position.val < (expand head).length
      · rw [dif_pos inHead]
        apply castRoot_name
        exact (List.getElem_append_left inHead).symm
      · rw [dif_neg inHead]
        let tailPosition : Fin (tail.flatMap expand).length :=
          ⟨occurrence.position.val - (expand head).length, by
            have bound : occurrence.position.val <
                (expand head).length + (tail.flatMap expand).length := by
              simpa [List.flatMap] using occurrence.position.isLt
            exact Nat.sub_lt_left_of_lt_add (Nat.le_of_not_gt inHead) bound⟩
        have elementEquality :
            (tail.flatMap expand).get tailPosition =
              ((head :: tail).flatMap expand).get occurrence.position := by
          symm
          exact List.getElem_append_right
            (by simpa using Nat.le_of_not_gt inHead)
        let tailOccurrence :
            CostStaticFVarListOccurrence (tail.flatMap expand) :=
          { position := tailPosition
            occurrence := elementEquality ▸ occurrence.occurrence }
        have tailName : tailOccurrence.occurrence.name =
            occurrence.occurrence.name := by
          unfold tailOccurrence
          dsimp only
          apply castRoot_name
          exact elementEquality
        change (flatMapOccurrenceSource expand tail tailOccurrence
          ).expandedOccurrence.occurrence.name = occurrence.occurrence.name
        exact (inductionHypothesis tailOccurrence).trans tailName

private theorem take_get_drop (patterns : List Pattern)
    (position : Fin patterns.length) :
    patterns.take position ++ patterns.get position ::
        patterns.drop (position + 1) = patterns := by
  rw [List.cons_get_drop_succ]
  exact List.take_append_drop position patterns

/-- Place a list occurrence back into the surrounding collection while
retaining its exact before/after zipper decomposition. -/
def inCollection (collectionType : CollType) (rest : Option String)
    {patterns : List Pattern}
    (occurrence : CostStaticFVarListOccurrence patterns) :
    CostStaticFVarOccurrence (.collection collectionType patterns rest) where
  name := occurrence.occurrence.name
  context := .collection collectionType (patterns.take occurrence.position)
    occurrence.occurrence.context
    (patterns.drop (occurrence.position + 1)) rest
  selected := by
    have selected : Selects (.fvar occurrence.occurrence.name)
        (.collection collectionType (patterns.take occurrence.position)
          occurrence.occurrence.context
          (patterns.drop (occurrence.position + 1)) rest)
        (.collection collectionType
          (patterns.take occurrence.position ++
            patterns.get occurrence.position ::
              patterns.drop (occurrence.position + 1)) rest) :=
      Selects.collection occurrence.occurrence.selected
    rw [take_get_drop] at selected
    exact selected

@[simp]
theorem inCollection_name (collectionType : CollType) (rest : Option String)
    {patterns : List Pattern}
    (occurrence : CostStaticFVarListOccurrence patterns) :
    (occurrence.inCollection collectionType rest).name =
      occurrence.occurrence.name :=
  rfl

/-- Transport a positional occurrence across list equality while preserving
its name explicitly. -/
def castPatterns {left right : List Pattern} (equal : left = right)
    (occurrence : CostStaticFVarListOccurrence left) :
    CostStaticFVarListOccurrence right := by
  cases equal
  exact occurrence

@[simp]
theorem castPatterns_name {left right : List Pattern} (equal : left = right)
    (occurrence : CostStaticFVarListOccurrence left) :
    (castPatterns equal occurrence).occurrence.name =
      occurrence.occurrence.name := by
  cases equal
  rfl

end CostStaticFVarListOccurrence

/-- A selected occurrence in a singleton list is an occurrence of its sole
member.  The finite position has no alternative. -/
def singletonListOccurrenceRoot {root : Pattern}
    (occurrence : CostStaticFVarListOccurrence [root]) :
    CostStaticFVarOccurrence root := by
  rcases occurrence with ⟨position, nested⟩
  have positionValue : position.val = 0 := by
    have bound := position.isLt
    change position.val < 1 at bound
    omega
  have positionEquality : position = ⟨0, by simp⟩ :=
    Fin.ext positionValue
  subst position
  exact nested

@[simp]
theorem singletonListOccurrenceRoot_name {root : Pattern}
    (occurrence : CostStaticFVarListOccurrence [root]) :
    (singletonListOccurrenceRoot occurrence).name = occurrence.occurrence.name := by
  rcases occurrence with ⟨position, nested⟩
  have positionValue : position.val = 0 := by
    have bound := position.isLt
    change position.val < 1 at bound
    omega
  have positionEquality : position = ⟨0, by simp⟩ :=
    Fin.ext positionValue
  subst position
  rfl

/-- Pull an exact occurrence in a parallel splice back into the source
pattern.  A genuine nested parallel uses the member zipper; every other
pattern uses the singleton splice. -/
def parallelSpliceOccurrenceSource
    (declaration : ReflectivePresentationDecl) {pattern : Pattern}
    (occurrence : CostStaticFVarListOccurrence
      (parallelSplice declaration pattern)) :
    CostStaticFVarOccurrence pattern := by
  cases pattern with
  | collection collectionType elements rest =>
      cases rest with
      | some restName =>
          have spliceEquality :
              parallelSplice declaration
                  (.collection collectionType elements (some restName)) =
                [.collection collectionType elements (some restName)] := rfl
          exact singletonListOccurrenceRoot
            (occurrence.castPatterns spliceEquality)
      | none =>
          by_cases parallel :
              collectionType = declaration.parallelCollection
          · subst collectionType
            have spliceEquality :
                parallelSplice declaration
                    (.collection declaration.parallelCollection elements none) =
                  elements := by
              simp [parallelSplice]
            let nested := occurrence.castPatterns spliceEquality
            exact nested.inCollection declaration.parallelCollection none
          · have spliceEquality :
                parallelSplice declaration
                    (.collection collectionType elements none) =
                  [.collection collectionType elements none] := by
              simp [parallelSplice, parallel]
            exact singletonListOccurrenceRoot
              (occurrence.castPatterns spliceEquality)
  | bvar index =>
      exact singletonListOccurrenceRoot occurrence
  | fvar name =>
      exact singletonListOccurrenceRoot occurrence
  | apply constructor arguments =>
      exact singletonListOccurrenceRoot occurrence
  | lambda binder body =>
      exact singletonListOccurrenceRoot occurrence
  | multiLambda arity binders body =>
      exact singletonListOccurrenceRoot occurrence
  | subst body replacement =>
      exact singletonListOccurrenceRoot occurrence

theorem parallelSpliceOccurrenceSource_name
    (declaration : ReflectivePresentationDecl) {pattern : Pattern}
    (occurrence : CostStaticFVarListOccurrence
      (parallelSplice declaration pattern)) :
    (parallelSpliceOccurrenceSource declaration occurrence).name =
      occurrence.occurrence.name := by
  cases pattern with
  | collection collectionType elements rest =>
      cases rest with
      | some restName =>
          have spliceEquality :
              parallelSplice declaration
                  (.collection collectionType elements (some restName)) =
                [.collection collectionType elements (some restName)] := rfl
          exact (singletonListOccurrenceRoot_name
              (occurrence.castPatterns spliceEquality)).trans
            (CostStaticFVarListOccurrence.castPatterns_name
              spliceEquality occurrence)
      | none =>
          by_cases parallel :
              collectionType = declaration.parallelCollection
          · subst collectionType
            have spliceEquality :
                parallelSplice declaration
                    (.collection declaration.parallelCollection elements none) =
                  elements := by
              simp [parallelSplice]
            simp [parallelSpliceOccurrenceSource, parallelSplice]
          · have spliceEquality :
                parallelSplice declaration
                    (.collection collectionType elements none) =
                  [.collection collectionType elements none] := by
              simp [parallelSplice, parallel]
            simp [parallelSpliceOccurrenceSource, parallelSplice, parallel]
  | bvar index =>
      exact singletonListOccurrenceRoot_name occurrence
  | fvar name =>
      exact singletonListOccurrenceRoot_name occurrence
  | apply constructor arguments =>
      exact singletonListOccurrenceRoot_name occurrence
  | lambda binder body =>
      exact singletonListOccurrenceRoot_name occurrence
  | multiLambda arity binders body =>
      exact singletonListOccurrenceRoot_name occurrence
  | subst body replacement =>
      exact singletonListOccurrenceRoot_name occurrence

/-- Exact source occurrence for a selected position after parallel
flattening. -/
def parallelFlatMapOccurrenceSource
    (declaration : ReflectivePresentationDecl) (patterns : List Pattern)
    (occurrence : CostStaticFVarListOccurrence
      (patterns.flatMap (parallelSplice declaration))) :
    CostStaticFVarListOccurrence patterns :=
  let source := CostStaticFVarListOccurrence.flatMapOccurrenceSource
    (parallelSplice declaration) patterns occurrence
  { position := source.sourcePosition
    occurrence := parallelSpliceOccurrenceSource declaration
      source.expandedOccurrence }

theorem parallelFlatMapOccurrenceSource_name
    (declaration : ReflectivePresentationDecl) (patterns : List Pattern)
    (occurrence : CostStaticFVarListOccurrence
      (patterns.flatMap (parallelSplice declaration))) :
    (parallelFlatMapOccurrenceSource declaration patterns occurrence
      ).occurrence.name = occurrence.occurrence.name := by
  unfold parallelFlatMapOccurrenceSource
  exact (parallelSpliceOccurrenceSource_name declaration _).trans
    (CostStaticFVarListOccurrence.flatMapOccurrenceSource_name
      (parallelSplice declaration) patterns occurrence)

/-- Exact positional ancestry through a list filter.  Surviving duplicate
values retain their order and their distinct source positions. -/
def filterOccurrenceSource (keep : Pattern → Bool) (patterns : List Pattern)
    (targetOccurrence :
      CostStaticFVarListOccurrence (patterns.filter keep)) :
    CostStaticFVarListOccurrence patterns :=
  CostStaticFVarListOccurrence.CostPositionalSublist.pullback
    (CostStaticFVarListOccurrence.filterPositionalSublist keep patterns)
    targetOccurrence

theorem filterOccurrenceSource_name (keep : Pattern → Bool)
    (patterns : List Pattern)
    (targetOccurrence :
      CostStaticFVarListOccurrence (patterns.filter keep)) :
    (filterOccurrenceSource keep patterns targetOccurrence).occurrence.name =
      targetOccurrence.occurrence.name :=
  CostStaticFVarListOccurrence.CostPositionalSublist.pullback_name
    (CostStaticFVarListOccurrence.filterPositionalSublist keep patterns)
    targetOccurrence

theorem filterOccurrenceSource_position_injective (keep : Pattern → Bool)
    (patterns : List Pattern)
    {left right : CostStaticFVarListOccurrence (patterns.filter keep)}
    (distinct : left.position ≠ right.position) :
    (filterOccurrenceSource keep patterns left).position ≠
      (filterOccurrenceSource keep patterns right).position :=
  CostStaticFVarListOccurrence.CostPositionalSublist.pullback_position_injective
    (CostStaticFVarListOccurrence.filterPositionalSublist keep patterns) distinct

/-- Exact positional ancestry for one selected occurrence through stable key
sorting.  The target is the sorted list; the result points into the original
list via the canonical permutation bijection. -/
def sortPatternsByOccurrenceSource
    {Key : Type} [LinearOrder Key] (key : Pattern → Key)
    (patterns : List Pattern)
    (targetOccurrence :
      CostStaticFVarListOccurrence
        (Mettapedia.OSLF.MeTTaIL.PatternCode.sortPatternsBy key patterns)) :
    CostStaticFVarListOccurrence patterns :=
  targetOccurrence.pullbackPerm
    (Mettapedia.OSLF.MeTTaIL.PatternCode.sortPatternsBy_perm key patterns)

theorem sortPatternsByOccurrenceSource_name
    {Key : Type} [LinearOrder Key] (key : Pattern → Key)
    (patterns : List Pattern)
    (targetOccurrence :
      CostStaticFVarListOccurrence
        (Mettapedia.OSLF.MeTTaIL.PatternCode.sortPatternsBy key patterns)) :
    (sortPatternsByOccurrenceSource key patterns targetOccurrence
      ).occurrence.name = targetOccurrence.occurrence.name :=
  CostStaticFVarListOccurrence.pullbackPerm_name
    (Mettapedia.OSLF.MeTTaIL.PatternCode.sortPatternsBy_perm key patterns)
    targetOccurrence

/-- Stable sorting preserves distinct positions even for duplicate values or
tied keys. -/
theorem sortPatternsByOccurrenceSource_position_injective
    {Key : Type} [LinearOrder Key] (key : Pattern → Key)
    (patterns : List Pattern)
    {left right :
      CostStaticFVarListOccurrence
        (Mettapedia.OSLF.MeTTaIL.PatternCode.sortPatternsBy key patterns)}
    (distinct : left.position ≠ right.position) :
    (sortPatternsByOccurrenceSource key patterns left).position ≠
      (sortPatternsByOccurrenceSource key patterns right).position :=
  CostStaticFVarListOccurrence.pullbackPerm_position_injective
    (Mettapedia.OSLF.MeTTaIL.PatternCode.sortPatternsBy_perm key patterns)
    distinct

/-- Exact positional ancestry through the complete parallel-list phase:
stable sorting, unit filtering, and nested-parallel flattening. -/
def normalizeParallelElementsByOccurrenceSource
    {Key : Type} [LinearOrder Key] (key : Pattern → Key)
    (declaration : ReflectivePresentationDecl) (patterns : List Pattern)
    (occurrence : CostStaticFVarListOccurrence
      (normalizeParallelElementsBy key declaration patterns)) :
    CostStaticFVarListOccurrence patterns :=
  let flattened := patterns.flatMap (parallelSplice declaration)
  let retained := flattened.filter fun pattern =>
    pattern ≠ .apply declaration.parallelUnitConstructor []
  let phaseEquality : normalizeParallelElementsBy key declaration patterns =
      Mettapedia.OSLF.MeTTaIL.PatternCode.sortPatternsBy key retained := by
    rfl
  let sortedOccurrence : CostStaticFVarListOccurrence
      (Mettapedia.OSLF.MeTTaIL.PatternCode.sortPatternsBy key retained) :=
    occurrence.castPatterns phaseEquality
  let retainedOccurrence :=
    sortPatternsByOccurrenceSource key retained sortedOccurrence
  let flattenedOccurrence := filterOccurrenceSource
    (fun pattern => pattern ≠ .apply declaration.parallelUnitConstructor [])
    flattened retainedOccurrence
  parallelFlatMapOccurrenceSource declaration patterns flattenedOccurrence

theorem normalizeParallelElementsByOccurrenceSource_name
    {Key : Type} [LinearOrder Key] (key : Pattern → Key)
    (declaration : ReflectivePresentationDecl) (patterns : List Pattern)
    (occurrence : CostStaticFVarListOccurrence
      (normalizeParallelElementsBy key declaration patterns)) :
    (normalizeParallelElementsByOccurrenceSource key declaration patterns
      occurrence).occurrence.name = occurrence.occurrence.name := by
  unfold normalizeParallelElementsByOccurrenceSource
  let flattened := patterns.flatMap (parallelSplice declaration)
  let retained := flattened.filter fun pattern =>
    pattern ≠ .apply declaration.parallelUnitConstructor []
  let phaseEquality : normalizeParallelElementsBy key declaration patterns =
      Mettapedia.OSLF.MeTTaIL.PatternCode.sortPatternsBy key retained := by
    rfl
  let sortedOccurrence : CostStaticFVarListOccurrence
      (Mettapedia.OSLF.MeTTaIL.PatternCode.sortPatternsBy key retained) :=
    occurrence.castPatterns phaseEquality
  let retainedOccurrence :=
    sortPatternsByOccurrenceSource key retained sortedOccurrence
  let flattenedOccurrence := filterOccurrenceSource
    (fun pattern => pattern ≠ .apply declaration.parallelUnitConstructor [])
    flattened retainedOccurrence
  exact (parallelFlatMapOccurrenceSource_name declaration patterns
      flattenedOccurrence).trans
    ((filterOccurrenceSource_name
      (fun pattern => pattern ≠ .apply declaration.parallelUnitConstructor [])
      flattened retainedOccurrence).trans
    ((sortPatternsByOccurrenceSource_name key retained sortedOccurrence).trans
      (CostStaticFVarListOccurrence.castPatterns_name phaseEquality occurrence)))

/-- Computational data exposed by a selected occurrence of a collection. -/
structure CostCollectionOccurrenceView (collectionType : CollType)
    (patterns : List Pattern) (rest : Option String)
    (occurrence : CostStaticFVarOccurrence
      (.collection collectionType patterns rest)) where
  before : List Pattern
  member : Pattern
  after : List Pattern
  inner : OneHoleContext
  patterns_eq : patterns = before ++ member :: after
  context_eq : occurrence.context =
    .collection collectionType before inner after rest
  selected : Selects (.fvar occurrence.name) inner member

/-- Every selected occurrence of a collection has a positional member view. -/
theorem CostCollectionOccurrenceView.nonempty (collectionType : CollType)
    (patterns : List Pattern) (rest : Option String)
    (occurrence : CostStaticFVarOccurrence
      (.collection collectionType patterns rest)) :
    Nonempty (CostCollectionOccurrenceView collectionType patterns rest
      occurrence) := by
  rcases occurrence with ⟨name, context, selected⟩
  cases selected with
  | collection innerSelected =>
      exact ⟨
        { before := _
          member := _
          after := _
          inner := _
          patterns_eq := rfl
          context_eq := rfl
          selected := innerSelected }⟩

/-- Choose the unique zipper-shaped member view hidden behind proof-irrelevant
selection evidence. -/
noncomputable def collectionOccurrenceView (collectionType : CollType)
    (patterns : List Pattern) (rest : Option String)
    (occurrence : CostStaticFVarOccurrence
      (.collection collectionType patterns rest)) :
    CostCollectionOccurrenceView collectionType patterns rest occurrence :=
  Classical.choice
    (CostCollectionOccurrenceView.nonempty collectionType patterns rest
      occurrence)

/-- Invert an occurrence of a collection into the exact selected member and
the exact nested occurrence within that member. -/
noncomputable def collectionOccurrenceMember (collectionType : CollType)
    (patterns : List Pattern) (rest : Option String)
    (occurrence : CostStaticFVarOccurrence
      (.collection collectionType patterns rest)) :
    CostStaticFVarListOccurrence patterns :=
  let view := collectionOccurrenceView collectionType patterns rest occurrence
  let inBounds : view.before.length < patterns.length := by
      have lengthEquality := congrArg List.length view.patterns_eq
      simp only [List.length_append, List.length_cons] at lengthEquality
      omega
  let position : Fin patterns.length := ⟨view.before.length, inBounds⟩
  have memberEquality : patterns.get position = view.member := by
    exact List.getElem_of_append view.patterns_eq rfl
  { position := position
    occurrence :=
      { name := occurrence.name
        context := view.inner
        selected := memberEquality.symm ▸ view.selected } }

@[simp]
theorem collectionOccurrenceMember_name (collectionType : CollType)
    (patterns : List Pattern) (rest : Option String)
    (occurrence : CostStaticFVarOccurrence
      (.collection collectionType patterns rest)) :
    (collectionOccurrenceMember collectionType patterns rest occurrence
      ).occurrence.name = occurrence.name := by
  rfl

/-- Reflect a selected occurrence through the final empty/singleton/multiple
parallel collapse.  The empty case is impossible because the declared unit
contains no free-variable occurrence. -/
noncomputable def collapseParallelOccurrenceSource
    (declaration : ReflectivePresentationDecl) (patterns : List Pattern)
    (occurrence : CostStaticFVarOccurrence
      (collapseParallel declaration patterns)) :
    CostStaticFVarListOccurrence patterns := by
  cases patterns with
  | nil =>
      have impossible := occurrence.name_mem_freeFvarNames
      simp [collapseParallel, Pattern.freeFvarNames] at impossible
  | cons first rest =>
      cases rest with
      | nil =>
          exact
            { position := ⟨0, by simp⟩
              occurrence := occurrence }
      | cons second tail =>
          exact collectionOccurrenceMember declaration.parallelCollection
            (first :: second :: tail) none occurrence

@[simp]
theorem collapseParallelOccurrenceSource_name
    (declaration : ReflectivePresentationDecl) (patterns : List Pattern)
    (occurrence : CostStaticFVarOccurrence
      (collapseParallel declaration patterns)) :
    (collapseParallelOccurrenceSource declaration patterns occurrence
      ).occurrence.name = occurrence.name := by
  cases patterns with
  | nil =>
      have impossible := occurrence.name_mem_freeFvarNames
      simp [collapseParallel, Pattern.freeFvarNames] at impossible
  | cons first rest =>
      cases rest with
      | nil => rfl
      | cons second tail =>
          exact collectionOccurrenceMember_name
            declaration.parallelCollection (first :: second :: tail) none
              occurrence

/-- Reflect an occurrence through every outer parallel canonical phase after
the children have already been canonicalized. -/
noncomputable def keyedParallelPhaseOccurrenceSource
    {Key : Type} [LinearOrder Key] (key : Pattern → Key)
    (declaration : ReflectivePresentationDecl) (patterns : List Pattern)
    (occurrence : CostStaticFVarOccurrence
      (collapseParallel declaration
        (normalizeParallelElementsBy key declaration patterns))) :
    CostStaticFVarListOccurrence patterns :=
  let normalizedOccurrence := collapseParallelOccurrenceSource declaration
    (normalizeParallelElementsBy key declaration patterns) occurrence
  normalizeParallelElementsByOccurrenceSource key declaration patterns
    normalizedOccurrence

@[simp]
theorem keyedParallelPhaseOccurrenceSource_name
    {Key : Type} [LinearOrder Key] (key : Pattern → Key)
    (declaration : ReflectivePresentationDecl) (patterns : List Pattern)
    (occurrence : CostStaticFVarOccurrence
      (collapseParallel declaration
        (normalizeParallelElementsBy key declaration patterns))) :
    (keyedParallelPhaseOccurrenceSource key declaration patterns occurrence
      ).occurrence.name = occurrence.name := by
  unfold keyedParallelPhaseOccurrenceSource
  exact (normalizeParallelElementsByOccurrenceSource_name key declaration
      patterns _).trans
    (collapseParallelOccurrenceSource_name declaration _ occurrence)

/-- Negative canary for value-only ancestry: two equal list members can carry
the same variable name at distinct positions. -/
theorem duplicateFVarListOccurrences_distinctPositions (name : String) :
    ∃ left right : CostStaticFVarListOccurrence [.fvar name, .fvar name],
      left.occurrence.name = right.occurrence.name ∧
        left.position ≠ right.position := by
  let point : CostStaticFVarOccurrence (.fvar name) := ⟨name, .hole, .here⟩
  let left : CostStaticFVarListOccurrence [.fvar name, .fvar name] :=
    ⟨⟨0, by simp⟩, point⟩
  let right : CostStaticFVarListOccurrence [.fvar name, .fvar name] :=
    ⟨⟨1, by simp⟩, point⟩
  refine ⟨left, right, rfl, ?_⟩
  simp [left, right]

/-- The quote-visible depth selected at the hole of a structural context.
Quotation resets the depth; binders advance it. -/
def keyedCanonicalHoleDepth (declaration : ReflectivePresentationDecl) :
    Nat → OneHoleContext → Nat
  | depth, .hole => depth
  | depth, .apply constructor _ inner _ =>
      keyedCanonicalHoleDepth declaration
        (if constructor == declaration.quoteConstructor then 0 else depth)
        inner
  | depth, .lambda _ inner =>
      keyedCanonicalHoleDepth declaration (depth + 1) inner
  | depth, .multiLambda arity _ inner =>
      keyedCanonicalHoleDepth declaration (depth + arity) inner
  | depth, .substBody inner _ =>
      keyedCanonicalHoleDepth declaration (depth + 1) inner
  | depth, .substReplacement _ inner =>
      keyedCanonicalHoleDepth declaration depth inner
  | depth, .collection _ _ inner _ _ =>
      keyedCanonicalHoleDepth declaration depth inner

/-- Equality of keyed representatives at the exact quote-visible hole depth
lifts through the complete one-hole context. -/
theorem canonicalizeByAt_fill_congr
    {Key : Type} [LinearOrder Key] (key : Nat → Pattern → Key)
    (declaration : ReflectivePresentationDecl) (depth : Nat)
    (context : OneHoleContext) {left right : Pattern}
    (representatives :
      canonicalizeByAt key declaration
          (keyedCanonicalHoleDepth declaration depth context) left =
        canonicalizeByAt key declaration
          (keyedCanonicalHoleDepth declaration depth context) right) :
    canonicalizeByAt key declaration depth (context.fill left) =
      canonicalizeByAt key declaration depth (context.fill right) := by
  induction context generalizing depth with
  | hole => exact representatives
  | apply constructor before inner after inductionHypothesis =>
      simp only [keyedCanonicalHoleDepth] at representatives
      simp only [OneHoleContext.fill, canonicalizeByAt,
        canonicalizeListByAt_eq_map, List.map_append, List.map_cons,
        inductionHypothesis _ representatives]
  | lambda binder inner inductionHypothesis =>
      simp only [keyedCanonicalHoleDepth] at representatives
      simp only [OneHoleContext.fill, canonicalizeByAt,
        inductionHypothesis _ representatives]
  | multiLambda arity binders inner inductionHypothesis =>
      simp only [keyedCanonicalHoleDepth] at representatives
      simp only [OneHoleContext.fill, canonicalizeByAt,
        inductionHypothesis _ representatives]
  | substBody inner replacement inductionHypothesis =>
      simp only [keyedCanonicalHoleDepth] at representatives
      simp only [OneHoleContext.fill, canonicalizeByAt,
        inductionHypothesis _ representatives]
  | substReplacement body inner inductionHypothesis =>
      simp only [keyedCanonicalHoleDepth] at representatives
      simp only [OneHoleContext.fill, canonicalizeByAt,
        inductionHypothesis _ representatives]
  | collection collectionType before inner after rest inductionHypothesis =>
      simp only [keyedCanonicalHoleDepth] at representatives
      cases rest <;>
        simp only [OneHoleContext.fill, canonicalizeByAt,
          canonicalizeListByAt_eq_map, List.map_append, List.map_cons,
          inductionHypothesis _ representatives]

/-- A proof-relevant path between exact free-variable occurrences across
bottom-up keyed canonicalization phases.  Every constructor retains both
zippers.  Composition therefore keeps equal duplicate occurrences distinct
even though the public ancestry theorem may later erase their positions. -/
inductive KeyedCanonicalFVarTrace
    {Key : Type} [LinearOrder Key] (key : Nat → Pattern → Key)
    (declaration : ReflectivePresentationDecl) :
    (sourceDepth targetDepth : Nat) → {source target : Pattern} →
      CostStaticFVarOccurrence source →
      CostStaticFVarOccurrence target → Type where
  | refl (depth : Nat) {root : Pattern}
      (occurrence : CostStaticFVarOccurrence root) :
      KeyedCanonicalFVarTrace key declaration depth depth occurrence occurrence
  | trans {sourceDepth middleDepth targetDepth : Nat}
      {source middle target : Pattern}
      {sourceOccurrence : CostStaticFVarOccurrence source}
      {middleOccurrence : CostStaticFVarOccurrence middle}
      {targetOccurrence : CostStaticFVarOccurrence target}
      (first : KeyedCanonicalFVarTrace key declaration sourceDepth middleDepth
        sourceOccurrence middleOccurrence)
      (second : KeyedCanonicalFVarTrace key declaration middleDepth targetDepth
        middleOccurrence targetOccurrence) :
      KeyedCanonicalFVarTrace key declaration sourceDepth targetDepth
        sourceOccurrence targetOccurrence
  | contextual {depth : Nat} (context : OneHoleContext)
      {source target : Pattern}
      {sourceOccurrence : CostStaticFVarOccurrence source}
      {targetOccurrence : CostStaticFVarOccurrence target}
      (nested : KeyedCanonicalFVarTrace key declaration
        (keyedCanonicalHoleDepth declaration depth context)
        (keyedCanonicalHoleDepth declaration depth context)
        sourceOccurrence targetOccurrence) :
      KeyedCanonicalFVarTrace key declaration depth depth
        (sourceOccurrence.inContext context)
        (targetOccurrence.inContext context)
  | parallelSingleton (depth : Nat) {element : Pattern}
      (occurrence : CostStaticFVarOccurrence element)
      (notParallel : ∀ elements,
        canonicalizeByAt key declaration depth element ≠
          .collection declaration.parallelCollection elements none) :
      KeyedCanonicalFVarTrace key declaration depth depth
        (occurrence.inContext
          (.collection declaration.parallelCollection [] .hole [] none))
        occurrence
  | quoteDrop (depth : Nat) {namePattern : Pattern}
      (occurrence : CostStaticFVarOccurrence namePattern)
      (quoteNeDrop : declaration.quoteConstructor ≠
        declaration.dropConstructor) :
      KeyedCanonicalFVarTrace key declaration depth 0
        (occurrence.inContext
          (.apply declaration.quoteConstructor []
            (.apply declaration.dropConstructor [] .hole []) []))
        occurrence

namespace KeyedCanonicalFVarTrace

/-- A trace never changes the selected free-variable spelling.  Distinct
positions carrying the same spelling remain distinct carrier values. -/
theorem name_eq
    {Key : Type} [LinearOrder Key] {key : Nat → Pattern → Key}
    {declaration : ReflectivePresentationDecl}
    {sourceDepth targetDepth : Nat}
    {source target : Pattern}
    {sourceOccurrence : CostStaticFVarOccurrence source}
    {targetOccurrence : CostStaticFVarOccurrence target}
    (trace : KeyedCanonicalFVarTrace key declaration sourceDepth targetDepth
      sourceOccurrence targetOccurrence) :
    sourceOccurrence.name = targetOccurrence.name := by
  induction trace with
  | refl => rfl
  | trans first second firstIH secondIH => exact firstIH.trans secondIH
  | contextual context nested inductionHypothesis =>
      exact inductionHypothesis
  | parallelSingleton => rfl
  | quoteDrop => rfl

/-- Every phase trace certifies equality of the complete keyed canonical
representatives.  This projection forgets positions; `name_eq` and the trace
itself retain their proof-relevant ancestry. -/
theorem representatives_eq
    {Key : Type} [LinearOrder Key] {key : Nat → Pattern → Key}
    {declaration : ReflectivePresentationDecl}
    {sourceDepth targetDepth : Nat}
    {source target : Pattern}
    {sourceOccurrence : CostStaticFVarOccurrence source}
    {targetOccurrence : CostStaticFVarOccurrence target}
    (trace : KeyedCanonicalFVarTrace key declaration sourceDepth targetDepth
      sourceOccurrence targetOccurrence) :
    canonicalizeByAt key declaration sourceDepth source =
      canonicalizeByAt key declaration targetDepth target := by
  induction trace with
  | refl => rfl
  | trans first second firstIH secondIH => exact firstIH.trans secondIH
  | contextual context nested inductionHypothesis =>
      exact canonicalizeByAt_fill_congr key declaration _ context
        inductionHypothesis
  | parallelSingleton depth occurrence notParallel =>
      exact canonicalizeByAt_parallel_singleton_of_not_parallel key
        declaration depth _ notParallel
  | quoteDrop depth occurrence quoteNeDrop =>
      exact canonicalizeByAt_quote_drop key declaration quoteNeDrop depth _

end KeyedCanonicalFVarTrace

/-! ## Staged Quote/singleton-parallel/Drop exposure -/

private def canonicalTraceFVarPoint (name : String) :
    CostStaticFVarOccurrence (.fvar name) :=
  ⟨name, .hole, .here⟩

/-- A Drop around a free variable canonicalizes to an application, never to a
bare parallel collection. -/
theorem canonicalizeByAt_drop_fvar_not_parallel
    {Key : Type} [LinearOrder Key] (key : Nat → Pattern → Key)
    (declaration : ReflectivePresentationDecl)
    (quoteNeDrop : declaration.quoteConstructor ≠
      declaration.dropConstructor)
    (depth : Nat) (name : String) : ∀ elements,
    canonicalizeByAt key declaration depth
        (.apply declaration.dropConstructor [.fvar name]) ≠
      .collection declaration.parallelCollection elements none := by
  intro elements equality
  simp [canonicalizeByAt, canonicalizeListByAt,
    Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.finishNormalizeReflectiveApply,
    Ne.symm quoteNeDrop] at equality

/-- The decisive staged trace.  Bottom-up canonicalization first removes the
singleton parallel wrapper inside quotation, producing a literal Drop shell;
only then can the outer Quote/Drop finisher expose the selected free variable.
The two exact source positions are composed rather than inferred from final
pattern equality. -/
def quoteParallelDropFVarTrace
    {Key : Type} [LinearOrder Key] (key : Nat → Pattern → Key)
    (declaration : ReflectivePresentationDecl)
    (quoteNeDrop : declaration.quoteConstructor ≠
      declaration.dropConstructor)
    (depth : Nat) (name : String) :
    KeyedCanonicalFVarTrace key declaration depth 0
      ((canonicalTraceFVarPoint name).inContext
        (.apply declaration.quoteConstructor []
          (.collection declaration.parallelCollection []
            (.apply declaration.dropConstructor [] .hole []) [] none) []))
      (canonicalTraceFVarPoint name) := by
  let point := canonicalTraceFVarPoint name
  let dropContext : OneHoleContext :=
    .apply declaration.dropConstructor [] .hole []
  let quoteContext : OneHoleContext :=
    .apply declaration.quoteConstructor [] .hole []
  let dropPoint := point.inContext dropContext
  have singleton : KeyedCanonicalFVarTrace key declaration 0 0
      (dropPoint.inContext
        (.collection declaration.parallelCollection [] .hole [] none))
      dropPoint :=
    .parallelSingleton 0 dropPoint
      (canonicalizeByAt_drop_fvar_not_parallel key declaration quoteNeDrop 0
        name)
  have first : KeyedCanonicalFVarTrace key declaration depth depth
      ((dropPoint.inContext
        (.collection declaration.parallelCollection [] .hole [] none)
        ).inContext quoteContext)
      (dropPoint.inContext quoteContext) :=
    by
      have singletonAtHole : KeyedCanonicalFVarTrace key declaration
          (keyedCanonicalHoleDepth declaration depth
            (.apply declaration.quoteConstructor [] .hole []))
          (keyedCanonicalHoleDepth declaration depth
            (.apply declaration.quoteConstructor [] .hole []))
          (dropPoint.inContext
            (.collection declaration.parallelCollection [] .hole [] none))
          dropPoint := by
        simpa [keyedCanonicalHoleDepth] using singleton
      simpa [quoteContext, keyedCanonicalHoleDepth] using
        (KeyedCanonicalFVarTrace.contextual (depth := depth)
          (.apply declaration.quoteConstructor [] .hole []) singletonAtHole)
  have second : KeyedCanonicalFVarTrace key declaration depth 0
      (point.inContext
        (.apply declaration.quoteConstructor []
          (.apply declaration.dropConstructor [] .hole []) []))
      point :=
    .quoteDrop depth point quoteNeDrop
  exact .trans first second

/-- Positive canary: the staged trace reaches the same canonical result as the
selected free variable. -/
theorem quoteParallelDropFVar_representatives_eq
    {Key : Type} [LinearOrder Key] (key : Nat → Pattern → Key)
    (declaration : ReflectivePresentationDecl)
    (quoteNeDrop : declaration.quoteConstructor ≠
      declaration.dropConstructor)
    (depth : Nat) (name : String) :
    canonicalizeByAt key declaration depth
        (Pattern.apply declaration.quoteConstructor
          [Pattern.collection declaration.parallelCollection
            [Pattern.apply declaration.dropConstructor [Pattern.fvar name]]
              none]) =
      canonicalizeByAt key declaration depth (Pattern.fvar name) := by
  have traced := (quoteParallelDropFVarTrace key declaration quoteNeDrop depth
    name).representatives_eq
  calc
    canonicalizeByAt key declaration depth
        (Pattern.apply declaration.quoteConstructor
          [Pattern.collection declaration.parallelCollection
            [Pattern.apply declaration.dropConstructor [Pattern.fvar name]]
              none]) =
        canonicalizeByAt key declaration 0 (Pattern.fvar name) := by
          simpa [OneHoleContext.fill] using traced
    _ = canonicalizeByAt key declaration depth (Pattern.fvar name) := rfl

/-- Negative shape canary: before the singleton phase fires, the outer term is
not a literal Quote/Drop shell.  A direct stopped-shell inversion would
therefore discard one real canonical phase. -/
theorem quoteParallelDropFVar_ne_quoteDropFVar
    (declaration : ReflectivePresentationDecl) (name : String) :
    (Pattern.apply declaration.quoteConstructor
        [Pattern.collection declaration.parallelCollection
          [Pattern.apply declaration.dropConstructor [Pattern.fvar name]]
            none]) ≠
      Pattern.apply declaration.quoteConstructor
        [Pattern.apply declaration.dropConstructor [Pattern.fvar name]] := by
  intro equality
  have argumentsEquality := (Pattern.apply.inj equality).2
  simp at argumentsEquality

end Mettapedia.GSLT.LanguageDef
