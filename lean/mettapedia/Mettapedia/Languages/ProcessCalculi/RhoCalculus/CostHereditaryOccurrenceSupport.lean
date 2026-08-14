import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryCanonical
import Mettapedia.GSLT.LanguageDef.CostReflectiveSupportSubstitutionComposition
import Mettapedia.GSLT.LanguageDef.CostElaborationDecoration
import Mettapedia.GSLT.LanguageDef.CostWholeLanguageDeterminism

/-!
# Occurrence-indexed support for hereditary rho Cost normalization

Hereditary Cost normalization retains two distinct finite views of a static
frame: positional parameter occurrences and semantic atoms.  Several
occurrences may denote one atom, but each occurrence may sit below a different
reflective binder context.  This module records the coeffect needed to pass
from the occurrence view to the semantic-atom view without changing either
runtime carrier.

The support of a semantic atom is the greatest suffix common to all of its
occurrence contexts.  Merely choosing an arbitrary common suffix is too weak:
it can discard binders on which the atom depends.
-/

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus

open Mettapedia.GSLT.LanguageDef
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.DerivedContexts

/-! ## Occurrence-class support -/

/-- A selected suffix is greatest among the suffixes shared by every member
of an indexed family.  This is an order-theoretic interface: consumers need
not depend on a particular executable longest-suffix algorithm. -/
structure GreatestCommonSuffix {Occurrence Item : Type}
    (available : Occurrence → List Item) (selected : List Item) : Prop where
  common : ∀ occurrence, selected <:+ available occurrence
  greatest : ∀ candidate,
    (∀ occurrence, candidate <:+ available occurrence) →
      candidate <:+ selected

namespace GreatestCommonSuffix

/-- Every inhabited family of finite lists has a greatest common suffix.
Choose one representative list and take the least depth at which its suffix
is common to the whole family.  Finiteness of the occurrence index is
unnecessary because the possible depths are bounded by the representative's
finite length. -/
theorem exists_of_nonempty {Occurrence Item : Type} [Nonempty Occurrence]
    (available : Occurrence → List Item) :
    ∃ selected, GreatestCommonSuffix available selected := by
  classical
  let representative : Occurrence := Classical.choice inferInstance
  let root := available representative
  have deep : ∃ depth,
      ∀ occurrence, root.drop depth <:+ available occurrence := by
    refine ⟨root.length, ?_⟩
    intro occurrence
    simp [root]
  let depth := Nat.find deep
  have depthSat : ∀ occurrence,
      root.drop depth <:+ available occurrence := Nat.find_spec deep
  refine ⟨root.drop depth, depthSat, ?_⟩
  intro candidate common
  obtain ⟨front, frontEq⟩ := common representative
  have candidateDrop : root.drop front.length = candidate := by
    have rootEq : front ++ candidate = root := by
      simpa [root] using frontEq
    rw [← rootEq, List.drop_left]
  have frontSat : ∀ occurrence,
      root.drop front.length <:+ available occurrence := by
    intro occurrence
    rw [candidateDrop]
    exact common occurrence
  have depthLe : depth ≤ front.length := Nat.find_min' deep frontSat
  have split : root.drop front.length =
      (root.drop depth).drop (front.length - depth) := by
    rw [List.drop_drop]
    congr 1
    omega
  rw [← candidateDrop, split]
  exact List.drop_suffix _ _

/-- Left-prefixing does not preserve the suffix order.  What greatest-common
suffixes do provide is the exact weaker fact needed below a binder: every
suffix common to all prefixed contexts is bounded by the selected suffix with
the same prefix restored. -/
theorem commonSuffix_prefix_append {Occurrence Item : Type}
    {available : Occurrence → List Item} {selected : List Item}
    (greatest : GreatestCommonSuffix available selected)
    (binderPrefix candidate : List Item)
    (candidateCommon : ∀ occurrence,
      candidate <:+ binderPrefix ++ available occurrence) :
    candidate <:+ binderPrefix ++ selected := by
  induction binderPrefix with
  | nil =>
      apply greatest.greatest
      intro occurrence
      simpa using candidateCommon occurrence
  | cons head tail inductionHypothesis =>
      classical
      by_cases whole : ∃ occurrence,
          candidate = head :: (tail ++ available occurrence)
      · obtain ⟨representative, candidateEquality⟩ := whole
        have representativeCommon : ∀ occurrence,
            available representative <:+ available occurrence := by
          intro occurrence
          have candidateSuffix := candidateCommon occurrence
          have representativeSuffixCandidate :
              available representative <:+ candidate := by
            rw [candidateEquality]
            exact List.suffix_append (head :: tail)
              (available representative)
          have representativeSuffixTarget :=
            representativeSuffixCandidate.trans candidateSuffix
          have occurrenceSuffixTarget :
              available occurrence <:+
                head :: (tail ++ available occurrence) := by
            exact List.suffix_append (head :: tail) (available occurrence)
          have lengthLe :
              (available representative).length ≤
                (available occurrence).length := by
            have lengths := candidateSuffix.length_le
            rw [candidateEquality] at lengths
            simp only [List.length_cons, List.length_append] at lengths
            omega
          exact List.suffix_of_suffix_length_le representativeSuffixTarget
            occurrenceSuffixTarget lengthLe
        have representativeSuffixSelected :=
          greatest.greatest (available representative) representativeCommon
        have selectedSuffixRepresentative := greatest.common representative
        have lengthEquality :
            (available representative).length = selected.length :=
          Nat.le_antisymm representativeSuffixSelected.length_le
            selectedSuffixRepresentative.length_le
        have valueEquality : available representative = selected :=
          representativeSuffixSelected.eq_of_length lengthEquality
        rw [candidateEquality, valueEquality]
        exact List.suffix_rfl
      · have reducedCommon : ∀ occurrence,
            candidate <:+ tail ++ available occurrence := by
          intro occurrence
          have member := candidateCommon occurrence
          simp only [List.cons_append] at member
          rw [List.suffix_cons_iff] at member
          rcases member with equality | suffix
          · exact False.elim (whole ⟨occurrence, equality⟩)
          · exact suffix
        exact (inductionHypothesis reducedCommon).trans
          (List.suffix_cons head (tail ++ selected))

end GreatestCommonSuffix

/-- One proof-relevant quotient of occurrence contexts by semantic class.

`represented` rules out empty semantic classes.  `classCommon` and
`classGreatest` say that `classAvailable` is the greatest common suffix of
exactly the occurrences mapped to that class. -/
structure OccurrenceClassSupport {Occurrence Class Item : Type}
    (classOf : Occurrence → Class) where
  occurrenceAvailable : Occurrence → List Item
  classAvailable : Class → List Item
  represented : Function.Surjective classOf
  classCommon : ∀ occurrence,
    classAvailable (classOf occurrence) <:+ occurrenceAvailable occurrence
  classGreatest : ∀ semanticClass candidate,
    (∀ occurrence, classOf occurrence = semanticClass →
      candidate <:+ occurrenceAvailable occurrence) →
    candidate <:+ classAvailable semanticClass

namespace OccurrenceClassSupport

/-- Assemble exact class support from an occurrence availability and a
proof that every semantic class is represented.  Each class applies the
inhabited-family greatest-common-suffix theorem to its proof-relevant fiber;
no enumeration or equality decision on occurrences is required. -/
noncomputable def ofSurjective {Occurrence Class Item : Type}
    {classOf : Occurrence → Class}
    (occurrenceAvailable : Occurrence → List Item)
    (represented : Function.Surjective classOf) :
    OccurrenceClassSupport (Item := Item) classOf := by
  classical
  let fiberRepresentative : ∀ semanticClass,
      { occurrence // classOf occurrence = semanticClass } :=
    fun semanticClass =>
      ⟨Classical.choose (represented semanticClass),
        Classical.choose_spec (represented semanticClass)⟩
  let fiberNonempty : ∀ semanticClass,
      Nonempty { occurrence // classOf occurrence = semanticClass } :=
    fun semanticClass => ⟨fiberRepresentative semanticClass⟩
  let fiberAvailable (semanticClass : Class) :
      { occurrence // classOf occurrence = semanticClass } → List Item :=
    fun occurrence => occurrenceAvailable occurrence.1
  let existence (semanticClass : Class) :
      ∃ selected, GreatestCommonSuffix (fiberAvailable semanticClass)
        selected :=
    @GreatestCommonSuffix.exists_of_nonempty
      { occurrence // classOf occurrence = semanticClass } Item
        (fiberNonempty semanticClass) (fiberAvailable semanticClass)
  let classAvailable (semanticClass : Class) : List Item :=
    Classical.choose (existence semanticClass)
  have classAvailableSpec (semanticClass : Class) :
      GreatestCommonSuffix (fiberAvailable semanticClass)
        (classAvailable semanticClass) :=
    Classical.choose_spec (existence semanticClass)
  exact
    { occurrenceAvailable := occurrenceAvailable
      classAvailable := classAvailable
      represented := represented
      classCommon := by
        intro occurrence
        exact (classAvailableSpec (classOf occurrence)).common
          ⟨occurrence, rfl⟩
      classGreatest := by
        intro semanticClass candidate common
        apply (classAvailableSpec semanticClass).greatest
        intro occurrence
        exact common occurrence.1 occurrence.2 }

/-- A single semantic class whose occurrences all have the same context. -/
def constant {Occurrence Item : Type} (representative : Occurrence)
    (available : List Item) :
    OccurrenceClassSupport (Item := Item)
      (fun _ : Occurrence => PUnit.unit) where
  occurrenceAvailable := fun _ => available
  classAvailable := fun _ => available
  represented := by
    intro semanticClass
    cases semanticClass
    exact ⟨representative, rfl⟩
  classCommon := by
    intro occurrence
    exact List.suffix_rfl
  classGreatest := by
    intro semanticClass candidate common
    cases semanticClass
    exact common representative rfl

/-- The binder-prefix bound specialized to one semantic occurrence class.
This is the order-theoretic bridge from positional contexts to a class-level
support; it does not claim that the prefixed class support is itself common. -/
theorem commonSuffix_prefix_classAvailable
    {Occurrence Class Item : Type} {classOf : Occurrence → Class}
    (support : OccurrenceClassSupport (Item := Item) classOf)
    (semanticClass : Class) (binderPrefix candidate : List Item)
    (candidateCommon : ∀ occurrence, classOf occurrence = semanticClass →
      candidate <:+ binderPrefix ++ support.occurrenceAvailable occurrence) :
    candidate <:+ binderPrefix ++ support.classAvailable semanticClass := by
  let Fiber := { occurrence // classOf occurrence = semanticClass }
  let fiberAvailable : Fiber → List Item :=
    fun occurrence => support.occurrenceAvailable occurrence.1
  have fiberGreatest : GreatestCommonSuffix fiberAvailable
      (support.classAvailable semanticClass) := by
    constructor
    · intro occurrence
      simpa [fiberAvailable, occurrence.2] using
        support.classCommon occurrence.1
    · intro alternative common
      apply support.classGreatest semanticClass alternative
      intro occurrence classEquality
      exact common ⟨occurrence, classEquality⟩
  apply fiberGreatest.commonSuffix_prefix_append binderPrefix candidate
  intro occurrence
  exact candidateCommon occurrence.1 occurrence.2

end OccurrenceClassSupport

/-! ## Positive and negative suffix canaries -/

/-- Two semantic classes, each with two positional occurrences and a distinct
nonempty greatest common suffix. -/
private def twoClassAvailable : Bool × Bool → List Bool
  | (false, false) => [false, true]
  | (false, true) => [true]
  | (true, false) => [true, false]
  | (true, true) => [false]

private theorem twoClass_surjective :
    Function.Surjective (Prod.fst : Bool × Bool → Bool) := by
  intro semanticClass
  exact ⟨(semanticClass, false), rfl⟩

private noncomputable def twoClassSupport :
    OccurrenceClassSupport (Item := Bool)
      (Prod.fst : Bool × Bool → Bool) :=
  OccurrenceClassSupport.ofSurjective twoClassAvailable twoClass_surjective

/-- Positive class-construction canary: quotienting by the first coordinate
retains the exact, distinct greatest suffix of each positional fiber. -/
theorem twoClassSupport_retains_distinct_greatestSuffixes :
    twoClassSupport.classAvailable false = [true] ∧
      twoClassSupport.classAvailable true = [false] := by
  constructor
  · have selectedSuffix : twoClassSupport.classAvailable false <:+ [true] := by
      have common := twoClassSupport.classCommon (false, true)
      change twoClassSupport.classAvailable false <:+
        twoClassAvailable (false, true) at common
      simpa [twoClassAvailable] using common
    have expectedSuffix : [true] <:+
        twoClassSupport.classAvailable false := by
      apply twoClassSupport.classGreatest false [true]
      intro occurrence classEquality
      rcases occurrence with ⟨semanticClass, position⟩
      change semanticClass = false at classEquality
      subst semanticClass
      cases position with
      | false =>
          change [true] <:+ [false, true]
          exact List.suffix_cons false [true]
      | true =>
          change [true] <:+ [true]
          exact List.suffix_rfl
    exact selectedSuffix.eq_of_length_le expectedSuffix.length_le
  · have selectedSuffix : twoClassSupport.classAvailable true <:+ [false] := by
      have common := twoClassSupport.classCommon (true, true)
      change twoClassSupport.classAvailable true <:+
        twoClassAvailable (true, true) at common
      simpa [twoClassAvailable] using common
    have expectedSuffix : [false] <:+
        twoClassSupport.classAvailable true := by
      apply twoClassSupport.classGreatest true [false]
      intro occurrence classEquality
      rcases occurrence with ⟨semanticClass, position⟩
      change semanticClass = true at classEquality
      subst semanticClass
      cases position with
      | false =>
          change [false] <:+ [true, false]
          exact List.suffix_cons true [false]
      | true =>
          change [false] <:+ [false]
          exact List.suffix_rfl
    exact selectedSuffix.eq_of_length_le expectedSuffix.length_le

/-- Two occurrence contexts sharing a nonempty tail.  The second occurrence
is exactly that tail, so it witnesses maximality directly. -/
private def suffixCanaryAvailable {Item : Type} (head tail : Item) :
    Bool → List Item
  | false => [head, tail]
  | true => [tail]

/-- Positive canary: the retained tail is the greatest common suffix. -/
theorem suffixCanary_tail_isGreatestCommonSuffix {Item : Type}
    (head tail : Item) :
    GreatestCommonSuffix (suffixCanaryAvailable head tail) [tail] := by
  constructor
  · intro occurrence
    cases occurrence <;> simp [suffixCanaryAvailable]
  · intro candidate common
    exact common true

/-- Negative canary: the empty list is a common suffix of the same occurrence
contexts, but it is not greatest.  Thus a lower-bound-only interface would
lose genuine binder support. -/
theorem suffixCanary_nil_not_greatestCommonSuffix {Item : Type}
    (head tail : Item) :
    ¬ GreatestCommonSuffix (suffixCanaryAvailable head tail) [] := by
  intro alleged
  have retainedTail : [tail] <:+ ([] : List Item) :=
    alleged.greatest [tail] (by
      intro occurrence
      cases occurrence <;> simp [suffixCanaryAvailable])
  simp at retainedTail

/-- Sharp order canary: a suffix need not remain a suffix after adding the
same list on the left.  Binder reasoning must use
`GreatestCommonSuffix.commonSuffix_prefix_append`, not a nonexistent
left-prefix monotonicity law. -/
theorem suffixCanary_leftPrefix_not_monotone :
    [true] <:+ [true, true] ∧
      ¬ ([false, true] <:+ [false, true, true]) := by
  decide

/-- Negative canary for the family index: the empty family makes every list a
common suffix, so it has no greatest member.  Re-basing therefore requires an
inhabited occurrence class; semantic atom classes supply that witness through
`OccurrenceClassSupport.represented`. -/
theorem emptyFamily_has_no_greatestCommonSuffix {Item : Type} [Nonempty Item]
    (selected : List Item) :
    ¬ GreatestCommonSuffix (fun occurrence : Empty => nomatch occurrence)
      selected := by
  intro alleged
  let marker : Item := selected.getLastD (Classical.choice inferInstance)
  have impossible : marker :: selected <:+ selected :=
    alleged.greatest (marker :: selected) (by intro occurrence; cases occurrence)
  have lengths := impossible.length_le
  simp at lengths

/-- A merely common suffix cannot rebase reflective support.  The singleton
free-variable computation is safe at its one-binder availability, while the
empty list is also a common suffix of that availability and is too small to
justify the same dependency.  Greatestness, not just commonness, is therefore
the sharp hypothesis of the rebasing theorem below. -/
theorem fvarSafeAt_commonSuffix_not_enough
    {language : LanguageDef} {free : WellSorted.FreeTypeContext}
    {name : String} {type binder : TypeExpr}
    (lookup : free name = some type)
    (profile : Mettapedia.OSLF.MeTTaIL.Reflection.ReflectionProfile)
    (binderImage : TypeExpr → TypeExpr) :
    let support : ContextSupport.Support := fun _ => [binder]
    let typed := WellSorted.HasType.fvar
      (language := language) (bound := []) lookup
    typed.ReflectiveSupportSafeAt profile support [binder] binderImage ∧
      ([] : List TypeExpr) <:+ [binder] ∧
      ¬ typed.ReflectiveSupportSafeAt profile support [] binderImage := by
  dsimp
  refine ⟨WellSorted.HasType.ReflectiveSupportSafeAt.fvar lookup [binder]
      ⟨[], by simp⟩, by simp, ?_⟩
  intro alleged
  cases alleged with
  | fvar _ _ shape =>
      obtain ⟨inner, impossible⟩ := shape
      have lengths := congrArg List.length impossible
      simp at lengths

/-! ## Plan-indexed occurrence availability -/

/-- A free-variable occurrence in a static plan decoration, retaining the
exact reflective availability at the leaf selected by its skeleton zipper.

The relation is proof-only.  It supplements the existing compact occurrence
carrier without changing executable inventories or normalized terms. -/
inductive CostStaticPlanAbstractOccurrence (source : CIGSLT) :
    (name : String) → CostStaticPlanDecoration source → OneHoleContext →
      List TypeExpr → Type where
  | sourceFVar
      {sourceBound targetBound sourceAvailable : List TypeExpr}
      {outer : OneHoleContext} {pattern : Pattern} {sourceType : TypeExpr}
      {boundaries : List CostRegionBoundary} {name : String} :
      CostStaticPlanAbstractOccurrence source name
        (.mk sourceBound targetBound sourceAvailable outer pattern sourceType
          boundaries (.fvar name))
        .hole sourceAvailable
  | boundaryApplication
      {sourceBound targetBound sourceAvailable : List TypeExpr}
      {outer : OneHoleContext} {pattern : Pattern} {sourceType : TypeExpr}
      {boundaries : List CostRegionBoundary}
      {constructor : source.DeclaredCostConstructor}
      {boundary : CostRegionBoundary} :
      CostStaticPlanAbstractOccurrence source
        (costRegionBoundaryVariableName boundary)
        (.mk sourceBound targetBound sourceAvailable outer pattern sourceType
          boundaries (.boundaryApplication constructor boundary))
        .hole sourceAvailable
  | application
      {sourceBound targetBound sourceAvailable : List TypeExpr}
      {outer : OneHoleContext} {pattern : Pattern} {sourceType : TypeExpr}
      {boundaries : List CostRegionBoundary} {sourceLabel : String}
      {constructor : source.DeclaredCostConstructor}
      {before : List (CostStaticPlanDecoration source)}
      {child : CostStaticPlanDecoration source}
      {after : List (CostStaticPlanDecoration source)}
      {name : String} {inner : OneHoleContext} {available : List TypeExpr}
      (nested : CostStaticPlanAbstractOccurrence source name child inner
        available) :
      CostStaticPlanAbstractOccurrence source name
        (.mk sourceBound targetBound sourceAvailable outer pattern sourceType
          boundaries
          (.application sourceLabel constructor (before ++ child :: after)))
        (.apply sourceLabel
          (before.map CostStaticPlanDecoration.abstractPattern) inner
          (after.map CostStaticPlanDecoration.abstractPattern))
        available
  | lambda
      {sourceBound targetBound sourceAvailable : List TypeExpr}
      {outer : OneHoleContext} {pattern : Pattern} {sourceType : TypeExpr}
      {boundaries : List CostRegionBoundary} {binder : Option String}
      {body : CostStaticPlanDecoration source}
      {name : String} {inner : OneHoleContext} {available : List TypeExpr}
      (nested : CostStaticPlanAbstractOccurrence source name body inner
        available) :
      CostStaticPlanAbstractOccurrence source name
        (.mk sourceBound targetBound sourceAvailable outer pattern sourceType
          boundaries (.lambda binder body))
        (.lambda binder inner) available
  | multiLambda
      {sourceBound targetBound sourceAvailable : List TypeExpr}
      {outer : OneHoleContext} {pattern : Pattern} {sourceType : TypeExpr}
      {boundaries : List CostRegionBoundary} {arity : Nat}
      {binders : List String} {body : CostStaticPlanDecoration source}
      {name : String} {inner : OneHoleContext} {available : List TypeExpr}
      (nested : CostStaticPlanAbstractOccurrence source name body inner
        available) :
      CostStaticPlanAbstractOccurrence source name
        (.mk sourceBound targetBound sourceAvailable outer pattern sourceType
          boundaries (.multiLambda arity binders body))
        (.multiLambda arity binders inner) available
  | collection
      {sourceBound targetBound sourceAvailable : List TypeExpr}
      {outer : OneHoleContext} {pattern : Pattern} {sourceType : TypeExpr}
      {boundaries : List CostRegionBoundary} {collectionType : CollType}
      {sourceRest : Option String} {choice : CostCollectionTypingChoice}
      {before : List (CostStaticPlanDecoration source)}
      {child : CostStaticPlanDecoration source}
      {after : List (CostStaticPlanDecoration source)}
      {name : String} {inner : OneHoleContext} {available : List TypeExpr}
      (nested : CostStaticPlanAbstractOccurrence source name child inner
        available) :
      CostStaticPlanAbstractOccurrence source name
        (.mk sourceBound targetBound sourceAvailable outer pattern sourceType
          boundaries
          (.collection collectionType sourceRest choice
            (before ++ child :: after)))
        (.collection collectionType
          (before.map CostStaticPlanDecoration.abstractPattern) inner
          (after.map CostStaticPlanDecoration.abstractPattern) sourceRest)
        available
  | boundaryCollection
      {sourceBound targetBound sourceAvailable : List TypeExpr}
      {outer : OneHoleContext} {pattern : Pattern} {sourceType : TypeExpr}
      {boundaries : List CostRegionBoundary} {collectionType : CollType}
      {choice : CostCollectionTypingChoice} {boundary : CostRegionBoundary} :
      CostStaticPlanAbstractOccurrence source
        (costRegionBoundaryVariableName boundary)
        (.mk sourceBound targetBound sourceAvailable outer pattern sourceType
          boundaries (.boundaryCollection collectionType choice boundary))
        .hole sourceAvailable

namespace CostStaticPlanAbstractOccurrence

/-- Forgetting plan evidence recovers the exact structural occurrence in the
abstract source skeleton. -/
def fvarOccurrence {source : CIGSLT} {name : String}
    {decoration : CostStaticPlanDecoration source}
    {context : OneHoleContext} {available : List TypeExpr}
    (occurrence : CostStaticPlanAbstractOccurrence source name decoration
      context available) :
    CostStaticFVarOccurrence decoration.abstractPattern := by
  refine { name := name, context := context, selected := ?_ }
  induction occurrence with
  | sourceFVar =>
      simpa only [CostStaticPlanDecoration.abstractPattern,
        CostStaticPlanDecorationNode.abstractPattern] using
        (Selects.here : Selects _ .hole _)
  | boundaryApplication =>
      simpa only [CostStaticPlanDecoration.abstractPattern,
        CostStaticPlanDecorationNode.abstractPattern] using
        (Selects.here : Selects _ .hole _)
  | boundaryCollection =>
      simpa only [CostStaticPlanDecoration.abstractPattern,
        CostStaticPlanDecorationNode.abstractPattern] using
        (Selects.here : Selects _ .hole _)
  | application nested inductionHypothesis =>
      simpa [CostStaticPlanDecoration.abstractPattern,
        CostStaticPlanDecorationNode.abstractPattern] using
        Selects.apply inductionHypothesis
  | lambda nested inductionHypothesis =>
      simpa [CostStaticPlanDecoration.abstractPattern,
        CostStaticPlanDecorationNode.abstractPattern] using
        Selects.lambda inductionHypothesis
  | multiLambda nested inductionHypothesis =>
      simpa [CostStaticPlanDecoration.abstractPattern,
        CostStaticPlanDecorationNode.abstractPattern] using
        Selects.multiLambda inductionHypothesis
  | collection nested inductionHypothesis =>
      simpa [CostStaticPlanDecoration.abstractPattern,
        CostStaticPlanDecorationNode.abstractPattern] using
        Selects.collection inductionHypothesis

/-- Invert an occurrence below an application decoration without asking
dependent elimination to synthesize the list split. -/
theorem application_split
    {source : CIGSLT}
    {sourceBound targetBound sourceAvailable : List TypeExpr}
    {outer : OneHoleContext} {pattern : Pattern} {sourceType : TypeExpr}
    {boundaries : List CostRegionBoundary} {sourceLabel : String}
    {constructor : source.DeclaredCostConstructor}
    {children : List (CostStaticPlanDecoration source)}
    {name : String} {context : OneHoleContext} {available : List TypeExpr}
    (occurrence : CostStaticPlanAbstractOccurrence source name
      (.mk sourceBound targetBound sourceAvailable outer pattern sourceType
        boundaries (.application sourceLabel constructor children))
      context available) :
    ∃ before child after inner,
      children = before ++ child :: after ∧
        Nonempty (CostStaticPlanAbstractOccurrence source name child inner
          available) := by
  cases occurrence with
  | application nested => exact ⟨_, _, _, _, rfl, ⟨nested⟩⟩

/-- Collection counterpart of `application_split`, retaining the selected
child and its exact nested occurrence. -/
theorem collection_split
    {source : CIGSLT}
    {sourceBound targetBound sourceAvailable : List TypeExpr}
    {outer : OneHoleContext} {pattern : Pattern} {sourceType : TypeExpr}
    {boundaries : List CostRegionBoundary} {collectionType : CollType}
    {sourceRest : Option String} {choice : CostCollectionTypingChoice}
    {children : List (CostStaticPlanDecoration source)}
    {name : String} {context : OneHoleContext} {available : List TypeExpr}
    (occurrence : CostStaticPlanAbstractOccurrence source name
      (.mk sourceBound targetBound sourceAvailable outer pattern sourceType
        boundaries (.collection collectionType sourceRest choice children))
      context available) :
    ∃ before child after inner,
      children = before ++ child :: after ∧
        Nonempty (CostStaticPlanAbstractOccurrence source name child inner
          available) := by
  cases occurrence with
  | collection nested => exact ⟨_, _, _, _, rfl, ⟨nested⟩⟩

/-- Transport only the selected decoration index of a plan occurrence.  This
is the proof-relevant alternative to eliminating a list-split equality by
substituting a dependent child. -/
def reindexDecoration
    {source : CIGSLT} {name : String}
    {first second : CostStaticPlanDecoration source}
    {context : OneHoleContext} {available : List TypeExpr}
    (decorationEquality : first = second)
    (occurrence : CostStaticPlanAbstractOccurrence source name first context
      available) :
    CostStaticPlanAbstractOccurrence source name second context available := by
  cases decorationEquality
  exact occurrence

end CostStaticPlanAbstractOccurrence

/-- Transport a positional occurrence across equality of its complete root
pattern.  The proof-relevant name and zipper are unchanged. -/
def castCostStaticFVarOccurrenceRoot {sourceRoot targetRoot : Pattern}
    (equality : sourceRoot = targetRoot)
    (occurrence : CostStaticFVarOccurrence sourceRoot) :
    CostStaticFVarOccurrence targetRoot := by
  subst targetRoot
  exact occurrence

@[simp]
theorem castCostStaticFVarOccurrenceRoot_name
    {sourceRoot targetRoot : Pattern}
    (equality : sourceRoot = targetRoot)
    (occurrence : CostStaticFVarOccurrence sourceRoot) :
    (castCostStaticFVarOccurrenceRoot equality occurrence).name =
      occurrence.name := by
  subst targetRoot
  rfl

@[simp]
theorem castCostStaticFVarOccurrenceRoot_context
    {sourceRoot targetRoot : Pattern}
    (equality : sourceRoot = targetRoot)
    (occurrence : CostStaticFVarOccurrence sourceRoot) :
    (castCostStaticFVarOccurrenceRoot equality occurrence).context =
      occurrence.context := by
  subst targetRoot
  rfl

/-- Invert a split of a mapped list without inventing an element.  The
result retains the exact prefix, selected member, and suffix in the source
list. -/
private theorem exists_source_split_of_map_eq
    {Source Target : Type} (map : Source → Target) :
    ∀ (before : List Target) (sources : List Source)
      (middle : Target) (after : List Target),
      sources.map map = before ++ middle :: after →
      ∃ sourceBefore sourceMiddle sourceAfter,
        sources = sourceBefore ++ sourceMiddle :: sourceAfter ∧
        sourceBefore.map map = before ∧
        map sourceMiddle = middle ∧
        sourceAfter.map map = after
  | [], [], middle, after, equality => by
      simp at equality
  | [], source :: sources, middle, after, equality => by
      simp only [List.map_cons, List.nil_append, List.cons.injEq] at equality
      exact ⟨[], source, sources, rfl, rfl, equality.1, equality.2⟩
  | target :: before, [], middle, after, equality => by
      simp at equality
  | target :: before, source :: sources, middle, after, equality => by
      simp only [List.map_cons, List.cons_append, List.cons.injEq] at equality
      obtain ⟨sourceBefore, sourceMiddle, sourceAfter, sourcesEquality,
          beforeEquality, middleEquality, afterEquality⟩ :=
        exists_source_split_of_map_eq map before sources middle after equality.2
      refine ⟨source :: sourceBefore, sourceMiddle, sourceAfter, ?_, ?_,
        middleEquality, afterEquality⟩
      · simp [sourcesEquality]
      · simp [equality.1, beforeEquality]

/-- Every selected free-variable zipper in a decorated static skeleton has
a plan-indexed reflective availability.  The recursion follows the zipper,
while the decoration supplies binder domains and quote-reset choices erased
from `OneHoleContext`. -/
theorem CostStaticPlanDecoration.nonempty_abstractOccurrenceOfFill
    {source : CIGSLT} :
    ∀ (context : OneHoleContext) (decoration : CostStaticPlanDecoration source)
      (name : String),
      decoration.abstractPattern = context.fill (.fvar name) →
      Nonempty (Σ available,
        CostStaticPlanAbstractOccurrence source name decoration context
          available)
  | .hole, .mk sourceBound targetBound sourceAvailable outer pattern sourceType
      boundaries node, name, filled => by
      simp only [OneHoleContext.fill_hole] at filled
      cases node with
      | bvar sourceIndex => simp [CostStaticPlanDecoration.abstractPattern,
          CostStaticPlanDecorationNode.abstractPattern] at filled
      | fvar sourceName =>
          simp [CostStaticPlanDecoration.abstractPattern,
            CostStaticPlanDecorationNode.abstractPattern] at filled
          subst sourceName
          exact ⟨⟨sourceAvailable, .sourceFVar⟩⟩
      | boundaryApplication constructor boundary =>
          simp [CostStaticPlanDecoration.abstractPattern,
            CostStaticPlanDecorationNode.abstractPattern] at filled
          subst name
          exact ⟨⟨sourceAvailable, .boundaryApplication⟩⟩
      | application sourceLabel constructor children =>
          simp [CostStaticPlanDecoration.abstractPattern,
            CostStaticPlanDecorationNode.abstractPattern] at filled
      | lambda binder body =>
          simp [CostStaticPlanDecoration.abstractPattern,
            CostStaticPlanDecorationNode.abstractPattern] at filled
      | multiLambda arity binders body =>
          simp [CostStaticPlanDecoration.abstractPattern,
            CostStaticPlanDecorationNode.abstractPattern] at filled
      | collection collectionType sourceRest choice children =>
          simp [CostStaticPlanDecoration.abstractPattern,
            CostStaticPlanDecorationNode.abstractPattern] at filled
      | boundaryCollection collectionType choice boundary =>
          simp [CostStaticPlanDecoration.abstractPattern,
            CostStaticPlanDecorationNode.abstractPattern] at filled
          subst name
          exact ⟨⟨sourceAvailable, .boundaryCollection⟩⟩
  | .apply contextLabel before inner after,
      .mk sourceBound targetBound sourceAvailable outer pattern sourceType
        boundaries node,
      name, filled => by
      simp only [OneHoleContext.fill] at filled
      cases node with
      | application sourceLabel constructor children =>
          simp only [CostStaticPlanDecoration.abstractPattern,
            CostStaticPlanDecorationNode.abstractPattern] at filled
          obtain ⟨labelEquality, childrenEquality⟩ := Pattern.apply.inj filled
          subst sourceLabel
          obtain ⟨sourceBefore, child, sourceAfter, childrenSplit,
              beforeEquality, childEquality, afterEquality⟩ :=
            exists_source_split_of_map_eq
              CostStaticPlanDecoration.abstractPattern before children
                (inner.fill (.fvar name)) after childrenEquality
          subst children
          obtain ⟨nested⟩ :=
            CostStaticPlanDecoration.nonempty_abstractOccurrenceOfFill inner
              child name childEquality
          cases beforeEquality
          cases afterEquality
          exact ⟨⟨nested.1, .application nested.2⟩⟩
      | bvar | fvar | boundaryApplication | lambda | multiLambda |
          collection | boundaryCollection =>
          simp [CostStaticPlanDecoration.abstractPattern,
            CostStaticPlanDecorationNode.abstractPattern] at filled
  | .lambda contextBinder inner,
      .mk sourceBound targetBound sourceAvailable outer pattern sourceType
        boundaries node,
      name, filled => by
      simp only [OneHoleContext.fill] at filled
      cases node with
      | lambda binder body =>
          simp only [CostStaticPlanDecoration.abstractPattern,
            CostStaticPlanDecorationNode.abstractPattern] at filled
          obtain ⟨binderEquality, bodyEquality⟩ := Pattern.lambda.inj filled
          subst binder
          obtain ⟨nested⟩ :=
            CostStaticPlanDecoration.nonempty_abstractOccurrenceOfFill inner
              body name bodyEquality
          exact ⟨⟨nested.1, .lambda nested.2⟩⟩
      | bvar | fvar | boundaryApplication | application | multiLambda |
          collection | boundaryCollection =>
          simp [CostStaticPlanDecoration.abstractPattern,
            CostStaticPlanDecorationNode.abstractPattern] at filled
  | .multiLambda contextArity contextBinders inner,
      .mk sourceBound targetBound sourceAvailable outer pattern sourceType
        boundaries node,
      name, filled => by
      simp only [OneHoleContext.fill] at filled
      cases node with
      | multiLambda arity binders body =>
          simp only [CostStaticPlanDecoration.abstractPattern,
            CostStaticPlanDecorationNode.abstractPattern] at filled
          obtain ⟨arityEquality, bindersEquality, bodyEquality⟩ :=
            Pattern.multiLambda.inj filled
          subst arity
          subst binders
          obtain ⟨nested⟩ :=
            CostStaticPlanDecoration.nonempty_abstractOccurrenceOfFill inner
              body name bodyEquality
          exact ⟨⟨nested.1, .multiLambda nested.2⟩⟩
      | bvar | fvar | boundaryApplication | application | lambda |
          collection | boundaryCollection =>
          simp [CostStaticPlanDecoration.abstractPattern,
            CostStaticPlanDecorationNode.abstractPattern] at filled
  | .substBody inner replacement, decoration, name, filled => by
      cases decoration with
      | mk sourceBound targetBound sourceAvailable outer pattern sourceType
          boundaries node =>
          cases node <;>
            simp [CostStaticPlanDecoration.abstractPattern,
              CostStaticPlanDecorationNode.abstractPattern,
              OneHoleContext.fill] at filled
  | .substReplacement body inner, decoration, name, filled => by
      cases decoration with
      | mk sourceBound targetBound sourceAvailable outer pattern sourceType
          boundaries node =>
          cases node <;>
            simp [CostStaticPlanDecoration.abstractPattern,
              CostStaticPlanDecorationNode.abstractPattern,
              OneHoleContext.fill] at filled
  | .collection contextCollection before inner after contextRest,
      .mk sourceBound targetBound sourceAvailable outer pattern sourceType
        boundaries node,
      name, filled => by
      simp only [OneHoleContext.fill] at filled
      cases node with
      | collection collectionType sourceRest choice children =>
          simp only [CostStaticPlanDecoration.abstractPattern,
            CostStaticPlanDecorationNode.abstractPattern] at filled
          obtain ⟨collectionEquality, childrenEquality, restEquality⟩ :=
            Pattern.collection.inj filled
          subst collectionType
          subst sourceRest
          obtain ⟨sourceBefore, child, sourceAfter, childrenSplit,
              beforeEquality, childEquality, afterEquality⟩ :=
            exists_source_split_of_map_eq
              CostStaticPlanDecoration.abstractPattern before children
                (inner.fill (.fvar name)) after childrenEquality
          subst children
          obtain ⟨nested⟩ :=
            CostStaticPlanDecoration.nonempty_abstractOccurrenceOfFill inner
              child name childEquality
          cases beforeEquality
          cases afterEquality
          exact ⟨⟨nested.1, .collection nested.2⟩⟩
      | bvar | fvar | boundaryApplication | application | lambda |
          multiLambda | boundaryCollection =>
          simp [CostStaticPlanDecoration.abstractPattern,
            CostStaticPlanDecorationNode.abstractPattern] at filled
termination_by context => sizeOf context

/-- Total plan-side extraction for the existing positional occurrence
carrier.  The occurrence remains the identity; the plan supplies only the
coeffect erased by its raw zipper. -/
theorem CostStaticPlanDecoration.nonempty_abstractOccurrence
    {source : CIGSLT} (decoration : CostStaticPlanDecoration source)
    (occurrence : CostStaticFVarOccurrence decoration.abstractPattern) :
    Nonempty (Σ available,
      CostStaticPlanAbstractOccurrence source occurrence.name decoration
        occurrence.context available) := by
  apply CostStaticPlanDecoration.nonempty_abstractOccurrenceOfFill
    occurrence.context decoration occurrence.name
  exact occurrence.selected.fill_eq.symm

/-- Reindex one inventory position from the node's stored skeleton equality
to the exact decoration root used by the plan-side occurrence relation. -/
def planDecorationOccurrenceAt
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    (node : CostStaticRegionNode source color targetFree)
    {values : TypedCostRegionBoundaryTable.Values source color targetFree
      node.boundaryTable}
    (inventory : CostStaticParameterInventory source color targetFree
      node.boundaryTable values node.skeleton.1)
    (position : inventory.Occurrence) :
    CostStaticFVarOccurrence node.plan.decoration.abstractPattern :=
  castCostStaticFVarOccurrenceRoot
    (node.skeleton_pattern.trans
      node.plan.decoration_abstractPattern.symm)
    (inventory.occurrenceAt position).fvarOccurrence

@[simp]
theorem planDecorationOccurrenceAt_name
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    (node : CostStaticRegionNode source color targetFree)
    {values : TypedCostRegionBoundaryTable.Values source color targetFree
      node.boundaryTable}
    (inventory : CostStaticParameterInventory source color targetFree
      node.boundaryTable values node.skeleton.1)
    (position : inventory.Occurrence) :
    (planDecorationOccurrenceAt node inventory position).name =
      (inventory.occurrenceAt position).fvarOccurrence.name :=
  castCostStaticFVarOccurrenceRoot_name _ _

@[simp]
theorem planDecorationOccurrenceAt_context
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    (node : CostStaticRegionNode source color targetFree)
    {values : TypedCostRegionBoundaryTable.Values source color targetFree
      node.boundaryTable}
    (inventory : CostStaticParameterInventory source color targetFree
      node.boundaryTable values node.skeleton.1)
    (position : inventory.Occurrence) :
    (planDecorationOccurrenceAt node inventory position).context =
      (inventory.occurrenceAt position).fvarOccurrence.context :=
  castCostStaticFVarOccurrenceRoot_context _ _

/-- Every executable inventory position has a plan-side occurrence carrying
its exact reflective availability.  The final equality proves that plan
extraction neither changes nor merely name-matches the positional zipper. -/
theorem nonempty_planOccurrenceAt
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    (node : CostStaticRegionNode source color targetFree)
    {values : TypedCostRegionBoundaryTable.Values source color targetFree
      node.boundaryTable}
    (inventory : CostStaticParameterInventory source color targetFree
      node.boundaryTable values node.skeleton.1)
    (position : inventory.Occurrence) :
    let positional := planDecorationOccurrenceAt node inventory position
    Nonempty (Σ available,
      { planOccurrence : CostStaticPlanAbstractOccurrence source
          positional.name node.plan.decoration positional.context available //
        planOccurrence.fvarOccurrence = positional }) := by
  let positional := planDecorationOccurrenceAt node inventory position
  obtain ⟨extracted⟩ :=
    CostStaticPlanDecoration.nonempty_abstractOccurrence
      node.plan.decoration positional
  refine ⟨⟨extracted.1, ⟨extracted.2, ?_⟩⟩⟩
  apply CostStaticFVarOccurrence.ext <;> rfl

/-! ## Semantic leaf safety -/

/-- The two honest sources of arbitrary reflective-support evidence for one
classified semantic leaf.  Source variables inherit the caller's leaf proof;
boundary values inherit the recursive child's normalized proof. -/
inductive CostStaticSemanticLeafSafeAt
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {occurrences : List CostRegionOccurrence}
    {table : TypedCostRegionBoundaryTable source color targetFree occurrences}
    {values : TypedCostRegionBoundaryTable.Values source color targetFree table}
    {root : Pattern}
    (support : ContextSupport.Support) (available : List TypeExpr)
    (binderImage : TypeExpr → TypeExpr) :
    CostStaticParameterOccurrence source color targetFree table values root →
      Prop where
  | sourceFVar
      {sourceName : String} {sourceType targetType : TypeExpr}
      {occurrence : CostStaticFVarOccurrence root}
      {decodesName : decodeCostRegionSourceVariableName occurrence.name =
        some sourceName}
      {targetLookup : targetFree sourceName = some targetType}
      {decodesType : decodeCostStaticTypeExpr source color targetType =
        some sourceType}
      {bound : List TypeExpr}
      (safe : (WellSorted.HasType.fvar
        (language := source.costWholeLanguage) (bound := bound)
        targetLookup).ReflectiveSupportSafeAt
          source.costWholeReflectionProfile support available binderImage) :
      CostStaticSemanticLeafSafeAt support available
        binderImage
        (.sourceFVar occurrence decodesName targetLookup decodesType)
  | boundary
      {occurrence : CostStaticFVarOccurrence root}
      {notSource : decodeCostRegionSourceVariableName occurrence.name = none}
      {resolved : TypedCostRegionBoundaryTable.Values.Resolved
        source color targetFree}
      {resolves : values.resolve table occurrence.name = some resolved}
      (safe : resolved.2.2.1.1.ReflectiveSupportSafeAt
        source.costWholeReflectionProfile support available binderImage) :
      CostStaticSemanticLeafSafeAt support available
        binderImage (.boundary occurrence notSource resolved resolves)

namespace CostStaticSemanticLeafSafeAt

/-- Either legitimate leaf source yields the same arbitrary support proof on
the semantic atom actually consumed by hereditary frame normalization. -/
theorem atomSafe
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {occurrences : List CostRegionOccurrence}
    {table : TypedCostRegionBoundaryTable source color targetFree occurrences}
    {values : TypedCostRegionBoundaryTable.Values source color targetFree table}
    {root : Pattern} {support : ContextSupport.Support}
    {available : List TypeExpr} {binderImage : TypeExpr → TypeExpr}
    {parameter : CostStaticParameterOccurrence source color targetFree table
      values root}
    (safe : CostStaticSemanticLeafSafeAt support available binderImage
      parameter) :
    parameter.atom.normalTyped.ReflectiveSupportSafeAt
      source.costWholeReflectionProfile support available binderImage := by
  cases safe with
  | sourceFVar sourceSafe =>
      cases sourceSafe with
      | fvar lookup _ shape =>
          simpa [CostStaticParameterOccurrence.atom,
            TypedCostStaticAtom.normalTyped,
            TypedCostStaticAtom.ofSourceFVar] using
            (WellSorted.HasType.ReflectiveSupportSafeAt.fvar
              (bound := []) lookup available shape)
  | boundary boundarySafe =>
      simpa [CostStaticParameterOccurrence.atom,
        TypedCostStaticAtom.normalTyped,
        TypedCostStaticAtom.ofBoundaryValue] using boundarySafe

end CostStaticSemanticLeafSafeAt

/-! ## Synchronized plan and semantic support -/

/-- The exact induction hypothesis supplied by recursively normalized
boundary children.  It is indexed by successful lookup in the current value
vector and consumes support safety of that same boundary's original content
and target type.  The input typing context is quantified because quotation
may hide a lexically present suffix; the selected raw content and result fiber
remain fixed.  Thus this is neither an unindexed promise about all outputs nor
a second normalization authority. -/
def CostStaticBoundaryChildReflectiveSupportPreserving
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {occurrences : List CostRegionOccurrence}
    (table : TypedCostRegionBoundaryTable source color targetFree occurrences)
    (values : TypedCostRegionBoundaryTable.Values source color targetFree table)
    (support : ContextSupport.Support)
    (binderImage : TypeExpr → TypeExpr) : Prop :=
  ∀ {name : String}
    {resolved : TypedCostRegionBoundaryTable.Values.Resolved
      source color targetFree},
    values.resolve table name = some resolved →
    ∀ {inputBound available : List TypeExpr}
      {inputTyped : WellSorted.HasType source.costWholeLanguage targetFree
        inputBound resolved.1.boundary.content
          resolved.1.boundary.targetType},
      inputTyped.ReflectiveSupportSafeAt
          source.costWholeReflectionProfile support available binderImage →
        resolved.2.2.1.1.ReflectiveSupportSafeAt
          source.costWholeReflectionProfile support available binderImage

/-- Result of synchronizing one exact plan occurrence with one arbitrary
reflective-support derivation.  `planAvailable` is retained as the plan's
typing/coeffect index, while `reflectiveAvailable` is the independently
computed availability induced by the caller's `binderImage`. -/
def CostStaticPlanSemanticLeafWitness
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {occurrences : List CostRegionOccurrence}
    {table : TypedCostRegionBoundaryTable source color targetFree occurrences}
    {values : TypedCostRegionBoundaryTable.Values source color targetFree table}
    {root : Pattern}
    {name : String} {decoration : CostStaticPlanDecoration source}
    {context : OneHoleContext} {planAvailable : List TypeExpr}
    (_planOccurrence : CostStaticPlanAbstractOccurrence source name decoration
      context planAvailable)
    (parameter : CostStaticParameterOccurrence source color targetFree table
      values root)
    (support : ContextSupport.Support)
    (binderImage : TypeExpr → TypeExpr) : Prop :=
  parameter.fvarOccurrence.name = name ∧
    ∃ reflectiveAvailable,
      CostStaticSemanticLeafSafeAt support reflectiveAvailable binderImage
        parameter

/-- A selected authored source-variable leaf inherits the exact arbitrary
support evidence at the corresponding generated target variable. -/
theorem sourceLeafSemanticSafeAt
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {occurrences : List CostRegionOccurrence}
    {table : TypedCostRegionBoundaryTable source color targetFree occurrences}
    {values : TypedCostRegionBoundaryTable.Values source color targetFree table}
    {root : Pattern} {sourceName : String} {sourceType : TypeExpr}
    {targetBound : List TypeExpr}
    (targetLookup : targetFree sourceName =
      some (mapTypeExpr (color.symbols source) sourceType))
    {targetTyped : WellSorted.HasType source.costWholeLanguage targetFree
      targetBound (.fvar sourceName)
        (mapTypeExpr (color.symbols source) sourceType)}
    {support : ContextSupport.Support} {available : List TypeExpr}
    {binderImage : TypeExpr → TypeExpr}
    (targetSafe : targetTyped.ReflectiveSupportSafeAt
      source.costWholeReflectionProfile support available binderImage)
    (parameter : CostStaticParameterOccurrence source color targetFree table
      values root)
    (nameEquality : parameter.fvarOccurrence.name =
      costRegionSourceVariableName sourceName) :
    CostStaticSemanticLeafSafeAt support available binderImage parameter := by
  cases parameter with
  | @sourceFVar decodedSource sourceType' targetType occurrence decodedName
      parameterLookup decodedType =>
      change occurrence.name = costRegionSourceVariableName sourceName at nameEquality
      have sourceNameEquality : decodedSource = sourceName := by
        rw [nameEquality, decodeCostRegionSourceVariableName_encode] at decodedName
        exact (Option.some.inj decodedName).symm
      subst decodedSource
      have targetTypeEquality : targetType =
          mapTypeExpr (color.symbols source) sourceType := by
        exact Option.some.inj (parameterLookup.symm.trans targetLookup)
      subst targetType
      exact .sourceFVar targetSafe.castTyping
  | boundary occurrence notSource resolved resolves =>
      change occurrence.name = costRegionSourceVariableName sourceName at nameEquality
      rw [nameEquality, decodeCostRegionSourceVariableName_encode] at notSource
      contradiction

/-- A selected rigid boundary leaf receives only the recursively justified
support evidence for the exact value returned by its finite lookup. -/
theorem boundaryLeafSemanticSafeAt
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {occurrences : List CostRegionOccurrence}
    {table : TypedCostRegionBoundaryTable source color targetFree occurrences}
    {values : TypedCostRegionBoundaryTable.Values source color targetFree table}
    {root targetPattern : Pattern} {targetType : TypeExpr}
    (boundary : TypedCostRegionBoundary source color targetFree)
    (membership : boundary ∈ table.entries)
    (patternEquality : boundary.boundary.content = targetPattern)
    (typeEquality : boundary.boundary.targetType = targetType)
    {targetBound : List TypeExpr}
    {targetTyped : WellSorted.HasType source.costWholeLanguage targetFree
      targetBound targetPattern targetType}
    {support : ContextSupport.Support} {available : List TypeExpr}
    {binderImage : TypeExpr → TypeExpr}
    (targetSafe : targetTyped.ReflectiveSupportSafeAt
      source.costWholeReflectionProfile support available binderImage)
    (childrenPreserve : CostStaticBoundaryChildReflectiveSupportPreserving
      table values support binderImage)
    (parameter : CostStaticParameterOccurrence source color targetFree table
      values root)
    (nameEquality : parameter.fvarOccurrence.name =
      costRegionBoundaryVariableName boundary.boundary) :
      CostStaticSemanticLeafSafeAt support available binderImage parameter := by
  cases parameter with
  | sourceFVar occurrence decodedName targetLookup decodedType =>
      change occurrence.name =
        costRegionBoundaryVariableName boundary.boundary at nameEquality
      rw [nameEquality, decodeCostRegionSourceVariableName_boundary] at decodedName
      contradiction
  | boundary occurrence notSource resolved resolves =>
      change occurrence.name =
        costRegionBoundaryVariableName boundary.boundary at nameEquality
      have projected := values.resolve_boundary table occurrence.name
      rw [resolves, nameEquality,
        table.resolve_of_mem_entries boundary membership] at projected
      have boundaryEquality : resolved.1 = boundary := by
        simpa using Option.some.inj projected
      cases boundaryEquality
      cases patternEquality
      cases typeEquality
      exact .boundary (childrenPreserve resolves targetSafe)

/-! ### Indexed support-safety inversions -/

/-- Reindex a support-safe constructor spine along equality of its complete
parameter profile.  The argument syntax and bound context do not move. -/
private theorem reindexArgumentsSafeAtParameters
    {language : LanguageDef} {free : WellSorted.FreeTypeContext}
    {bound : List TypeExpr} {arguments : List Pattern}
    {firstParameters secondParameters : List TermParam}
    (parametersEquality : firstParameters = secondParameters)
    {typed : WellSorted.ArgumentsHaveTypes language free bound arguments
      firstParameters}
    {profile : Mettapedia.OSLF.MeTTaIL.Reflection.ReflectionProfile}
    {support : ContextSupport.Support} {available : List TypeExpr}
    {binderImage : TypeExpr → TypeExpr}
    (safe : typed.ReflectiveSupportSafeAt profile support available
      binderImage) :
    ∃ targetTyped : WellSorted.ArgumentsHaveTypes language free bound arguments
        secondParameters,
      targetTyped.ReflectiveSupportSafeAt profile support available
        binderImage := by
  cases parametersEquality
  exact ⟨typed, safe⟩

/-- Invert arbitrary support safety of a generated static application against
the exact plan-selected constructor declaration.  Validated wire-label
uniqueness supplies the parameter-profile equality; quote status determines
whether the child availability is reset. -/
theorem applicationArgumentsSafe
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {targetBound : List TypeExpr}
    {wireName : String} {arguments : List Pattern}
    (constructor : source.DeclaredCostConstructor)
    (rendered : source.renderDeclaredCostConstructor constructor = wireName)
    (preimage : CostStaticConstructorPreimage source color constructor)
    {targetTyped : WellSorted.HasType source.costWholeLanguage targetFree
      targetBound (.apply wireName arguments)
        (mapTypeExpr (color.symbols source)
          (.base preimage.sourceConstructor.1.category))}
    {support : ContextSupport.Support} {reflectiveAvailable : List TypeExpr}
    {binderImage : TypeExpr → TypeExpr}
    (targetSafe : targetTyped.ReflectiveSupportSafeAt
      source.costWholeReflectionProfile support reflectiveAvailable
        binderImage) :
    ∃ argumentsTyped : WellSorted.ArgumentsHaveTypes
        source.costWholeLanguage targetFree targetBound arguments
          (preimage.sourceConstructor.1.params.map
            (mapTermParam (color.symbols source))),
      argumentsTyped.ReflectiveSupportSafeAt
        source.costWholeReflectionProfile support
          (if ReflectiveContextSupport.isQuoteConstructor source.reflection.1
              preimage.sourceConstructor.1.label then []
            else reflectiveAvailable)
          binderImage := by
  generalize _resultTypeEquality :
      mapTypeExpr (color.symbols source)
        (.base preimage.sourceConstructor.1.category) = targetResult
    at targetTyped targetSafe
  cases targetSafe with
  | @constructorQuote _ rule _ membership notBare argumentsTyped available
      binderImage targetQuoted argumentsSafe =>
      have labelEquality :
          (source.materializeDeclaredCostConstructor constructor).label =
            rule.label := by
        rw [source.materializeDeclaredCostConstructor_label, rendered]
      have ruleEquality :
          source.materializeDeclaredCostConstructor constructor = rule :=
        source.materializeDeclaredCostConstructor_eq_of_mem_of_label rule
          membership constructor labelEquality
      subst rule
      have parametersEquality :
          (source.materializeDeclaredCostConstructor constructor).params =
            preimage.sourceConstructor.1.params.map
              (mapTermParam (color.symbols source)) := preimage.parametersMap
      obtain ⟨mappedArgumentsTyped, mappedArgumentsSafe⟩ :=
        reindexArgumentsSafeAtParameters parametersEquality argumentsSafe
      have sourceQuoted : ReflectiveContextSupport.isQuoteConstructor
          source.reflection.1 preimage.sourceConstructor.1.label = true := by
        rw [← reflectiveIsQuoteConstructor_mapCostStatic source color]
        rw [← preimage.labelMap]
        exact targetQuoted
      rw [sourceQuoted]
      exact ⟨mappedArgumentsTyped, mappedArgumentsSafe⟩
  | @constructorOrdinary _ rule _ membership notBare argumentsTyped available
      binderImage targetOrdinary argumentsSafe =>
      have labelEquality :
          (source.materializeDeclaredCostConstructor constructor).label =
            rule.label := by
        rw [source.materializeDeclaredCostConstructor_label, rendered]
      have ruleEquality :
          source.materializeDeclaredCostConstructor constructor = rule :=
        source.materializeDeclaredCostConstructor_eq_of_mem_of_label rule
          membership constructor labelEquality
      subst rule
      have parametersEquality :
          (source.materializeDeclaredCostConstructor constructor).params =
            preimage.sourceConstructor.1.params.map
              (mapTermParam (color.symbols source)) := preimage.parametersMap
      obtain ⟨mappedArgumentsTyped, mappedArgumentsSafe⟩ :=
        reindexArgumentsSafeAtParameters parametersEquality argumentsSafe
      have sourceOrdinary : ReflectiveContextSupport.isQuoteConstructor
          source.reflection.1 preimage.sourceConstructor.1.label = false := by
        rw [← reflectiveIsQuoteConstructor_mapCostStatic source color]
        rw [← preimage.labelMap]
        exact targetOrdinary
      rw [sourceOrdinary]
      exact ⟨mappedArgumentsTyped, mappedArgumentsSafe⟩

/-- Explicitly transport reflective-support evidence when only the result
type index changes.  The pattern, binder context, and support observation are
held fixed; after eliminating the type equality, proof irrelevance accounts
for the remaining choice of typing derivation. -/
private theorem reflectiveSupportSafeAt_castType
    {language : LanguageDef} {free : WellSorted.FreeTypeContext}
    {bound : List TypeExpr} {pattern : Pattern}
    {sourceType targetType : TypeExpr}
    {sourceTyped : WellSorted.HasType language free bound pattern sourceType}
    {targetTyped : WellSorted.HasType language free bound pattern targetType}
    {profile : Mettapedia.OSLF.MeTTaIL.Reflection.ReflectionProfile}
    {support : ContextSupport.Support} {available : List TypeExpr}
    {binderImage : TypeExpr → TypeExpr}
    (typeEquality : sourceType = targetType)
    (safe : sourceTyped.ReflectiveSupportSafeAt profile support available
      binderImage) :
    targetTyped.ReflectiveSupportSafeAt profile support available
      binderImage := by
  cases typeEquality
  exact safe.castTyping

/-- Constructor-specific inversion for a directly typed collection. -/
private theorem collectionSafeAt_elements
    {source : CIGSLT} {targetFree : WellSorted.FreeTypeContext}
    {targetBound : List TypeExpr} {collectionType : CollType}
    {elements : List Pattern} {rest : Option String} {elementType : TypeExpr}
    {elementsTyped : WellSorted.ElementsHaveType source.costWholeLanguage
      targetFree targetBound elements elementType}
    {support : ContextSupport.Support} {available : List TypeExpr}
    {binderImage : TypeExpr → TypeExpr}
    (safe : (WellSorted.HasType.collection (collectionType := collectionType)
      (rest := rest) elementsTyped).ReflectiveSupportSafeAt
        source.costWholeReflectionProfile support available binderImage) :
    elementsTyped.ReflectiveSupportSafeAt source.costWholeReflectionProfile
      support available binderImage := by
  cases safe with
  | collection elementsSafe => exact elementsSafe.castTyping

/-- Proof-relevant inversion of collection support safety.  The element
fiber is retained explicitly because the outer collection judgment alone
does not determine it until collection-choice determinism is applied. -/
private theorem reflectiveSupportSafeAt_collectionData
    {source : CIGSLT} {targetFree : WellSorted.FreeTypeContext}
    {targetBound : List TypeExpr} {collectionType : CollType}
    {elements : List Pattern} {rest : Option String} {type : TypeExpr}
    {targetTyped : WellSorted.HasType source.costWholeLanguage targetFree
      targetBound (.collection collectionType elements rest) type}
    {support : ContextSupport.Support} {available : List TypeExpr}
    {binderImage : TypeExpr → TypeExpr}
    (safe : targetTyped.ReflectiveSupportSafeAt
      source.costWholeReflectionProfile support available binderImage) :
    (∃ elementType,
        ∃ elementsTyped : WellSorted.ElementsHaveType
            source.costWholeLanguage targetFree targetBound elements elementType,
          type = .collection collectionType elementType ∧
            elementsTyped.ReflectiveSupportSafeAt
              source.costWholeReflectionProfile support available
                binderImage) ∨
      (∃ rule parameterName elementType,
        ∃ _membership : rule ∈ source.costWholeLanguage.terms,
          ∃ _parameterShape : rule.params =
              [.simple parameterName
                (.collection collectionType elementType)],
            ∃ elementsTyped : WellSorted.ElementsHaveType
                source.costWholeLanguage targetFree targetBound elements
                  elementType,
              type = .base rule.category ∧
                elementsTyped.ReflectiveSupportSafeAt
                  source.costWholeReflectionProfile support available
                    binderImage) := by
  cases safe with
  | collection elementsSafe =>
      exact Or.inl ⟨_, _, rfl, elementsSafe⟩
  | @collectionConstructor _ branchRule branchParameterName _ _ _
      branchElementType branchMembership branchParameterShape
      branchElementsTyped _ _ elementsSafe =>
      exact Or.inr ⟨branchRule, branchParameterName, branchElementType,
        branchMembership, branchParameterShape, branchElementsTyped, rfl,
          elementsSafe⟩

/-- Constructor-specific inversion for a bare collection declaration. -/
private theorem collectionConstructorSafeAt_elements
    {source : CIGSLT} {targetFree : WellSorted.FreeTypeContext}
    {targetBound : List TypeExpr} {rule : GrammarRule}
    {parameterName : String} {collectionType : CollType}
    {elements : List Pattern} {rest : Option String} {elementType : TypeExpr}
    {membership : rule ∈ source.costWholeLanguage.terms}
    {parameterShape : rule.params =
      [.simple parameterName (.collection collectionType elementType)]}
    {elementsTyped : WellSorted.ElementsHaveType source.costWholeLanguage
      targetFree targetBound elements elementType}
    {support : ContextSupport.Support} {available : List TypeExpr}
    {binderImage : TypeExpr → TypeExpr}
    (collectionDeterministic :
      WellSorted.CollectionChoiceDeterministic source.costWholeLanguage)
    (safe : (WellSorted.HasType.collectionConstructor (rest := rest)
      membership parameterShape elementsTyped).ReflectiveSupportSafeAt
        source.costWholeReflectionProfile support available binderImage) :
    elementsTyped.ReflectiveSupportSafeAt source.costWholeReflectionProfile
      support available binderImage := by
  rcases reflectiveSupportSafeAt_collectionData safe with
    ⟨_otherElementType, _otherElementsTyped, typeEquality, _elementsSafe⟩ |
      ⟨otherRule, _otherParameterName, otherElementType, otherMembership,
        otherParameterShape, _otherElementsTyped, typeEquality, elementsSafe⟩
  · simp at typeEquality
  · have categoryEquality : rule.category = otherRule.category :=
      TypeExpr.base.inj typeEquality
    have elementTypeEquality : elementType = otherElementType :=
      collectionDeterministic membership otherMembership parameterShape
        otherParameterShape categoryEquality
    subst otherElementType
    exact elementsSafe.castTyping

/-- Proof-relevant inversion of application support safety.  The authored
rule and quote status remain existential so dependent elimination never has
to identify two rule proofs before generated-label determinism is applied. -/
private theorem reflectiveSupportSafeAt_applicationData
    {source : CIGSLT} {targetFree : WellSorted.FreeTypeContext}
    {targetBound : List TypeExpr} {wireName : String}
    {arguments : List Pattern} {type : TypeExpr}
    {targetTyped : WellSorted.HasType source.costWholeLanguage targetFree
      targetBound (.apply wireName arguments) type}
    {support : ContextSupport.Support} {available : List TypeExpr}
    {binderImage : TypeExpr → TypeExpr}
    (safe : targetTyped.ReflectiveSupportSafeAt
      source.costWholeReflectionProfile support available binderImage) :
    ∃ rule : GrammarRule,
      ∃ _membership : rule ∈ source.costWholeLanguage.terms,
        ∃ _notBare : ¬ WellSorted.UsesBareCollection rule,
          ∃ argumentsTyped : WellSorted.ArgumentsHaveTypes
              source.costWholeLanguage targetFree targetBound arguments
                rule.params,
            rule.label = wireName ∧ type = .base rule.category ∧
              ((ReflectiveContextSupport.isQuoteConstructor
                    source.costWholeReflectionProfile rule.label = true ∧
                  argumentsTyped.ReflectiveSupportSafeAt
                    source.costWholeReflectionProfile support [] binderImage) ∨
                (ReflectiveContextSupport.isQuoteConstructor
                    source.costWholeReflectionProfile rule.label = false ∧
                  argumentsTyped.ReflectiveSupportSafeAt
                    source.costWholeReflectionProfile support available
                      binderImage)) := by
  cases safe with
  | @constructorQuote _ rule _ membership notBare argumentsTyped _ _ quoted
      argumentsSafe =>
      exact ⟨rule, membership, notBare, argumentsTyped, rfl, rfl,
        Or.inl ⟨quoted, argumentsSafe⟩⟩
  | @constructorOrdinary _ rule _ membership notBare argumentsTyped _ _
      ordinary argumentsSafe =>
      exact ⟨rule, membership, notBare, argumentsTyped, rfl, rfl,
        Or.inr ⟨ordinary, argumentsSafe⟩⟩

/-- An ordinary application support proof exposes the argument spine of the
exact authored rule selected by the outer typing derivation. -/
private theorem constructorOrdinarySafeAt_arguments
    {source : CIGSLT} {targetFree : WellSorted.FreeTypeContext}
    {targetBound : List TypeExpr} {rule : GrammarRule}
    {arguments : List Pattern}
    {membership : rule ∈ source.costWholeLanguage.terms}
    {notBare : ¬ WellSorted.UsesBareCollection rule}
    {argumentsTyped : WellSorted.ArgumentsHaveTypes source.costWholeLanguage
      targetFree targetBound arguments rule.params}
    {support : ContextSupport.Support} {available : List TypeExpr}
    {binderImage : TypeExpr → TypeExpr}
    (ordinary : ReflectiveContextSupport.isQuoteConstructor
      source.costWholeReflectionProfile rule.label = false)
    (safe : (WellSorted.HasType.constructor membership notBare
      argumentsTyped).ReflectiveSupportSafeAt
        source.costWholeReflectionProfile support available binderImage) :
    argumentsTyped.ReflectiveSupportSafeAt
      source.costWholeReflectionProfile support available binderImage := by
  obtain ⟨otherRule, otherMembership, _otherNotBare, otherArgumentsTyped,
      labelEquality, _typeEquality, status⟩ :=
    reflectiveSupportSafeAt_applicationData safe
  have ruleEquality : otherRule = rule :=
    source.costWholeLanguage_labelDeterministic otherMembership membership
      labelEquality
  subst otherRule
  rcases status with
    ⟨quoted, _otherArgumentsSafe⟩ | ⟨_otherOrdinary, otherArgumentsSafe⟩
  · simp [ordinary] at quoted
  · exact otherArgumentsSafe.castTyping

/-! ### Greatest-common-suffix rebasing of support proofs -/

mutual
  /-- Internal prefix-indexed form of GCS rebasing.  The original root GCS is
  retained throughout the recursion; `binderPrefix` records binders crossed
  since that root.  This distinction is essential because
  `binderPrefix ++ selected` need not itself be common to all
  `binderPrefix ++ available occurrence`. -/
  private theorem rebaseSafeAtFromRepresentative
      {Occurrence : Type} [Nonempty Occurrence]
      {source : CIGSLT} {targetFree : WellSorted.FreeTypeContext}
      {support : ContextSupport.Support}
      {available : Occurrence → List TypeExpr}
      {selected binderPrefix : List TypeExpr}
      (greatest : GreatestCommonSuffix available selected)
      (collectionDeterministic :
        WellSorted.CollectionChoiceDeterministic source.costWholeLanguage)
      {bound : List TypeExpr} {pattern : Pattern} {type : TypeExpr}
      {typed : WellSorted.HasType source.costWholeLanguage targetFree bound
        pattern type}
      {binderImage : TypeExpr → TypeExpr}
      (object : WellSorted.isObjectPattern pattern = true)
      (representative : Occurrence)
      (representativeSafe : typed.ReflectiveSupportSafeAt
        source.costWholeReflectionProfile support
          (binderPrefix ++ available representative) binderImage)
      (familySafe : ∀ occurrence,
        typed.ReflectiveSupportSafeAt source.costWholeReflectionProfile support
          (binderPrefix ++ available occurrence) binderImage) :
      typed.ReflectiveSupportSafeAt source.costWholeReflectionProfile support
        (binderPrefix ++ selected) binderImage := by
    cases representativeSafe with
    | bvar lookup _ =>
        exact .bvar lookup (binderPrefix ++ selected)
    | @fvar _ name _ lookup _ _ _ =>
        refine .fvar lookup (binderPrefix ++ selected) ?_
        obtain ⟨inner, supportSuffix⟩ :=
          greatest.commonSuffix_prefix_append binderPrefix (support name) (by
            intro occurrence
            have occurrenceSafe := familySafe occurrence
            cases occurrenceSafe with
            | fvar _ _ shape =>
                obtain ⟨occurrenceInner, occurrenceShape⟩ := shape
                exact ⟨occurrenceInner, occurrenceShape.symm⟩)
        exact ⟨inner, supportSuffix.symm⟩
    | @constructorQuote _ rule _ membership notBare argumentsTyped _ _ quoted
        argumentsSafe =>
        exact .constructorQuote (membership := membership)
          (notBare := notBare) (argumentsTyped := argumentsTyped) quoted
            argumentsSafe
    | @constructorOrdinary _ rule arguments membership notBare argumentsTyped _ _
        ordinary argumentsSafe =>
        refine .constructorOrdinary (membership := membership)
          (notBare := notBare) (argumentsTyped := argumentsTyped) ordinary ?_
        have argumentsObjects :
            WellSorted.isObjectPatternList arguments = true := by
          simpa [WellSorted.isObjectPattern] using object
        apply rebaseArgumentsSafeAtFromRepresentative
          (binderImage := binderImage) greatest collectionDeterministic
            argumentsObjects representative argumentsSafe
        intro occurrence
        exact constructorOrdinarySafeAt_arguments (membership := membership)
          (notBare := notBare) (argumentsTyped := argumentsTyped) ordinary
          (familySafe occurrence)
    | @lambda _ binder body domain _codomain bodyTyped _ _ bodySafe =>
        refine .lambda (binder := binder) (bodyTyped := bodyTyped) ?_
        have bodyObject : WellSorted.isObjectPattern body = true := by
          simpa [WellSorted.isObjectPattern] using object
        have representativeBodySafe :
            bodyTyped.ReflectiveSupportSafeAt
              source.costWholeReflectionProfile support
              ((binderImage domain :: binderPrefix) ++ available representative)
                binderImage := by
          simpa only [List.cons_append] using bodySafe
        apply rebaseSafeAtFromRepresentative (binderImage := binderImage)
          greatest collectionDeterministic bodyObject representative
            representativeBodySafe
        intro occurrence
        have occurrenceSafe := familySafe occurrence
        cases occurrenceSafe with
        | lambda otherBodySafe =>
            simpa only [List.cons_append] using otherBodySafe.castTyping
    | @multiLambda _ arity binders body domain _codomain bodyTyped _ _ bodySafe =>
        refine .multiLambda (binders := binders) (bodyTyped := bodyTyped) ?_
        have bodyObject : WellSorted.isObjectPattern body = true := by
          simpa [WellSorted.isObjectPattern] using object
        let extendedPrefix :=
          List.replicate arity (binderImage domain) ++ binderPrefix
        have representativeBodySafe :
            bodyTyped.ReflectiveSupportSafeAt
              source.costWholeReflectionProfile support
              (extendedPrefix ++ available representative) binderImage := by
          simpa only [extendedPrefix, List.append_assoc] using bodySafe
        have rebased := rebaseSafeAtFromRepresentative
          (binderImage := binderImage) greatest collectionDeterministic
            bodyObject representative representativeBodySafe (by
              intro occurrence
              have occurrenceSafe := familySafe occurrence
              cases occurrenceSafe with
              | multiLambda otherBodySafe =>
                  simpa only [extendedPrefix, List.append_assoc] using
                    otherBodySafe.castTyping)
        simpa only [extendedPrefix, List.append_assoc] using rebased
    | @subst _ _ _ domain _ bodyTyped replacementTyped _ _ bodySafe
        replacementSafe =>
        simp [WellSorted.isObjectPattern] at object
    | @collection _ collectionType elements rest elementType elementsTyped _ _
        elementsSafe =>
        refine .collection (collectionType := collectionType) (rest := rest)
          (elementsTyped := elementsTyped) ?_
        have objectParts : rest.isNone = true ∧
            WellSorted.isObjectPatternList elements = true := by
          simpa [WellSorted.isObjectPattern] using object
        apply rebaseElementsSafeAtFromRepresentative greatest
          (binderImage := binderImage) collectionDeterministic objectParts.2
            representative elementsSafe
        intro occurrence
        exact collectionSafeAt_elements (familySafe occurrence)
    | @collectionConstructor _ rule parameterName collectionType elements rest
        elementType membership parameterShape elementsTyped _ _ elementsSafe =>
        refine .collectionConstructor (membership := membership)
          (parameterShape := parameterShape) (elementsTyped := elementsTyped) ?_
        have objectParts : rest.isNone = true ∧
            WellSorted.isObjectPatternList elements = true := by
          simpa [WellSorted.isObjectPattern] using object
        apply rebaseElementsSafeAtFromRepresentative greatest
          (binderImage := binderImage) collectionDeterministic objectParts.2
            representative elementsSafe
        intro occurrence
        exact collectionConstructorSafeAt_elements
          (parameterName := parameterName) (membership := membership)
          (parameterShape := parameterShape) collectionDeterministic
            (familySafe occurrence)
  termination_by 3 * sizeOf pattern + 2

  /-- Constructor-spine companion to
  `rebaseSafeAtFromRepresentative`. -/
  private theorem rebaseArgumentsSafeAtFromRepresentative
      {Occurrence : Type} [Nonempty Occurrence]
      {source : CIGSLT} {targetFree : WellSorted.FreeTypeContext}
      {support : ContextSupport.Support}
      {available : Occurrence → List TypeExpr}
      {selected binderPrefix : List TypeExpr}
      (greatest : GreatestCommonSuffix available selected)
      (collectionDeterministic :
        WellSorted.CollectionChoiceDeterministic source.costWholeLanguage)
      {bound : List TypeExpr} {arguments : List Pattern}
      {parameters : List TermParam}
      {typed : WellSorted.ArgumentsHaveTypes source.costWholeLanguage
        targetFree bound arguments parameters}
      {binderImage : TypeExpr → TypeExpr}
      (objects : WellSorted.isObjectPatternList arguments = true)
      (representative : Occurrence)
      (representativeSafe : typed.ReflectiveSupportSafeAt
        source.costWholeReflectionProfile support
          (binderPrefix ++ available representative) binderImage)
      (familySafe : ∀ occurrence,
        typed.ReflectiveSupportSafeAt source.costWholeReflectionProfile support
          (binderPrefix ++ available occurrence) binderImage) :
      typed.ReflectiveSupportSafeAt source.costWholeReflectionProfile support
        (binderPrefix ++ selected) binderImage := by
    cases representativeSafe with
    | nil _ _ =>
        exact .nil _ _
    | @cons _ argument arguments _ _ _ representation parameterType argumentTyped
        argumentsTyped _ _ argumentSafe argumentsSafe =>
        have objectParts :
            WellSorted.isObjectPattern argument = true ∧
              WellSorted.isObjectPatternList arguments = true := by
          simpa [WellSorted.isObjectPatternList] using objects
        refine .cons (representation := representation)
          (parameterType := parameterType) (argumentTyped := argumentTyped)
            (argumentsTyped := argumentsTyped) ?_ ?_
        · apply rebaseSafeAtFromRepresentative (binderImage := binderImage)
            greatest collectionDeterministic objectParts.1 representative
              argumentSafe
          intro occurrence
          exact (familySafe occurrence).head
            (representation := representation)
            (parameterType := parameterType)
            (argumentTyped := argumentTyped)
            (argumentsTyped := argumentsTyped)
        · apply rebaseArgumentsSafeAtFromRepresentative
            (binderImage := binderImage) greatest collectionDeterministic
              objectParts.2 representative argumentsSafe
          intro occurrence
          have occurrenceSafe := familySafe occurrence
          cases occurrenceSafe with
          | cons _ otherArgumentsSafe =>
              exact otherArgumentsSafe.castTyping
  termination_by 3 * sizeOf arguments + 1

  /-- Homogeneous-collection companion to
  `rebaseSafeAtFromRepresentative`. -/
  private theorem rebaseElementsSafeAtFromRepresentative
      {Occurrence : Type} [Nonempty Occurrence]
      {source : CIGSLT} {targetFree : WellSorted.FreeTypeContext}
      {support : ContextSupport.Support}
      {available : Occurrence → List TypeExpr}
      {selected binderPrefix : List TypeExpr}
      (greatest : GreatestCommonSuffix available selected)
      (collectionDeterministic :
        WellSorted.CollectionChoiceDeterministic source.costWholeLanguage)
      {bound : List TypeExpr} {elements : List Pattern} {elementType : TypeExpr}
      {typed : WellSorted.ElementsHaveType source.costWholeLanguage targetFree
        bound elements elementType}
      {binderImage : TypeExpr → TypeExpr}
      (objects : WellSorted.isObjectPatternList elements = true)
      (representative : Occurrence)
      (representativeSafe : typed.ReflectiveSupportSafeAt
        source.costWholeReflectionProfile support
          (binderPrefix ++ available representative) binderImage)
      (familySafe : ∀ occurrence,
        typed.ReflectiveSupportSafeAt source.costWholeReflectionProfile support
          (binderPrefix ++ available occurrence) binderImage) :
      typed.ReflectiveSupportSafeAt source.costWholeReflectionProfile support
        (binderPrefix ++ selected) binderImage := by
    cases representativeSafe with
    | nil _ _ _ =>
        exact .nil _ _ _
    | @cons _ element elements _ elementTyped elementsTyped _ _ elementSafe
        elementsSafe =>
        have objectParts :
            WellSorted.isObjectPattern element = true ∧
              WellSorted.isObjectPatternList elements = true := by
          simpa [WellSorted.isObjectPatternList] using objects
        refine .cons (elementTyped := elementTyped)
          (elementsTyped := elementsTyped) ?_ ?_
        · apply rebaseSafeAtFromRepresentative (binderImage := binderImage)
            greatest collectionDeterministic objectParts.1 representative
              elementSafe
          intro occurrence
          have occurrenceSafe := familySafe occurrence
          cases occurrenceSafe with
          | cons otherElementSafe _ => exact otherElementSafe.castTyping
        · apply rebaseElementsSafeAtFromRepresentative
            (binderImage := binderImage) greatest collectionDeterministic
              objectParts.2 representative elementsSafe
          intro occurrence
          have occurrenceSafe := familySafe occurrence
          cases occurrenceSafe with
          | cons _ otherElementsSafe => exact otherElementsSafe.castTyping
  termination_by 3 * sizeOf elements + 1

  decreasing_by
    all_goals subst_vars
    all_goals simp <;> omega
end

/-- Reflective support safety descends from an inhabited family of root
availabilities to its greatest common suffix.  The theorem remains local to
the Cost occurrence module because `GreatestCommonSuffix` is currently a
rho-local proof-only abstraction. -/
theorem WellSorted.HasType.ReflectiveSupportSafeAt.of_greatestCommonSuffix_of_object
    {Occurrence : Type} [Nonempty Occurrence]
    {source : CIGSLT} {targetFree : WellSorted.FreeTypeContext}
    {support : ContextSupport.Support}
    {available : Occurrence → List TypeExpr} {selected : List TypeExpr}
    {bound : List TypeExpr} {pattern : Pattern} {type : TypeExpr}
    {typed : WellSorted.HasType source.costWholeLanguage targetFree bound
      pattern type}
    {binderImage : TypeExpr → TypeExpr}
    (greatest : GreatestCommonSuffix available selected)
    (collectionDeterministic :
      WellSorted.CollectionChoiceDeterministic source.costWholeLanguage)
    (object : WellSorted.isObjectPattern pattern = true)
    (familySafe : ∀ occurrence,
      typed.ReflectiveSupportSafeAt source.costWholeReflectionProfile support
        (available occurrence) binderImage) :
    typed.ReflectiveSupportSafeAt source.costWholeReflectionProfile support
      selected binderImage := by
  let representative : Occurrence := Classical.choice inferInstance
  simpa only [List.nil_append] using
    rebaseSafeAtFromRepresentative (binderPrefix := []) greatest
      collectionDeterministic object
      representative (familySafe representative) familySafe

/-- Invert arbitrary support safety of a collection at the exact element
fiber selected by the proof-relevant static plan.  Candidate soundness
provides an independently checked derivation in that fiber; its proof is
transported into the caller's support-safety certificate only after the
typing indices agree. -/
theorem collectionElementsSafe
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {targetBound : List TypeExpr} {collectionType : CollType}
    {elements : List Pattern} {rest : Option String} {sourceType : TypeExpr}
    (collectionDeterministic :
      WellSorted.CollectionChoiceDeterministic source.costWholeLanguage)
    (choice : CostCollectionTypingChoice)
    (selected : choice ∈ costStaticCollectionTypingChoices source color
      targetFree targetBound collectionType elements
        (mapTypeExpr (color.symbols source) sourceType))
    {targetTyped : WellSorted.HasType source.costWholeLanguage targetFree
      targetBound (.collection collectionType elements rest)
        (mapTypeExpr (color.symbols source) sourceType)}
    {support : ContextSupport.Support} {reflectiveAvailable : List TypeExpr}
    {binderImage : TypeExpr → TypeExpr}
    (targetSafe : targetTyped.ReflectiveSupportSafeAt
      source.costWholeReflectionProfile support reflectiveAvailable
        binderImage) :
    ∃ elementsTyped : WellSorted.ElementsHaveType source.costWholeLanguage
        targetFree targetBound elements (choice.targetElementType source color),
      elementsTyped.ReflectiveSupportSafeAt
        source.costWholeReflectionProfile support reflectiveAvailable
          binderImage := by
  rcases mem_costStaticCollectionTypingChoices_sound source color targetFree
      targetBound collectionType elements
        (mapTypeExpr (color.symbols source) sourceType) choice selected with
    direct | bare
  · rcases direct with
      ⟨sourceElementType, rfl, resultEquality, elementsChecked⟩
    have elementsTyped :=
      WellSorted.checkElementsHaveType_sound elementsChecked
    have selectedSafe :
        (WellSorted.HasType.collection (collectionType := collectionType)
          (rest := rest) elementsTyped).ReflectiveSupportSafeAt
            source.costWholeReflectionProfile support reflectiveAvailable
              binderImage :=
      reflectiveSupportSafeAt_castType resultEquality targetSafe
    exact ⟨elementsTyped, collectionSafeAt_elements selectedSafe⟩
  · rcases bare with
      ⟨rule, sourceElementType, rfl, ruleMembership, wrappedMembership,
        resultEquality, parameterName, parameterShape, elementsChecked⟩
    have elementsTyped :=
      WellSorted.checkElementsHaveType_sound elementsChecked
    cases color with
    | base =>
        have parameterEquality :=
          costBaseConstructor_params_eq_map_of_mem_wrappedLabels source rule
            ruleMembership wrappedMembership
        have targetShape : (costBaseConstructor source.cut rule).params =
            [.simple parameterName
              (.collection collectionType
                (mapTypeExpr (CostStaticColor.base.symbols source)
                  sourceElementType))] := by
          simp [parameterEquality, parameterShape,
            mapTermParam_costBaseStaticSymbols, CostStaticColor.symbols,
            mapParameterType, costBaseTypeExpr]
        have selectedSafe :
            (WellSorted.HasType.collectionConstructor (rest := rest)
              (source.costBaseConstructor_mem_costWhole rule ruleMembership)
              targetShape elementsTyped).ReflectiveSupportSafeAt
                source.costWholeReflectionProfile support reflectiveAvailable
                  binderImage :=
          reflectiveSupportSafeAt_castType resultEquality targetSafe
        exact ⟨elementsTyped,
          collectionConstructorSafeAt_elements
            (parameterName := parameterName)
            (elementType := mapTypeExpr
              (CostStaticColor.base.symbols source) sourceElementType)
            (membership :=
              source.costBaseConstructor_mem_costWhole rule ruleMembership)
            (parameterShape := targetShape) (elementsTyped := elementsTyped)
            collectionDeterministic selectedSafe⟩
    | wrapped =>
        let authored : StructuralMorphism.AuthoredConstructor
            source.theory.presentation.presentation := ⟨rule, ruleMembership⟩
        have wrappedConstructor : authored ∈
            source.continuationRetyping.wrappedConstructors :=
          (source.continuationRetyping.mem_wrappedLabels_iff authored).mp
            wrappedMembership
        have targetShape :
            (costWrappedConstructor (theory := source.theory) rule).params =
              [.simple parameterName
                (.collection collectionType
                  (mapTypeExpr (CostStaticColor.wrapped.symbols source)
                    sourceElementType))] := by
          simp [costWrappedConstructor, parameterShape,
            CostStaticColor.symbols, mapParameterType, costWrappedTypeExpr]
        have selectedSafe :
            (WellSorted.HasType.collectionConstructor (rest := rest)
              (source.costWrappedConstructor_mem_costWhole authored
                wrappedConstructor)
              targetShape elementsTyped).ReflectiveSupportSafeAt
                source.costWholeReflectionProfile support reflectiveAvailable
                  binderImage :=
          reflectiveSupportSafeAt_castType resultEquality targetSafe
        exact ⟨elementsTyped,
          collectionConstructorSafeAt_elements
            (parameterName := parameterName)
            (elementType := mapTypeExpr
              (CostStaticColor.wrapped.symbols source) sourceElementType)
            (membership := source.costWrappedConstructor_mem_costWhole authored
              wrappedConstructor)
            (parameterShape := targetShape) (elementsTyped := elementsTyped)
            collectionDeterministic selectedSafe⟩

/-- Exact inversion of a support-safe mapped argument spine.  The mapped
parameter type is recovered from the source parameter's successful type
check, rather than by asking dependent elimination to guess the preimage
type. -/
theorem argumentsSafeAt_cons_map
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext} {targetBound : List TypeExpr}
    {argument : Pattern} {arguments : List Pattern}
    {parameter : TermParam} {parameters : List TermParam}
    {sourceExpected : TypeExpr}
    (parameterType : WellSorted.parameterType? parameter = some sourceExpected)
    {typed : WellSorted.ArgumentsHaveTypes source.costWholeLanguage targetFree
      targetBound (argument :: arguments)
        ((parameter :: parameters).map (mapTermParam (color.symbols source)))}
    {support : ContextSupport.Support} {available : List TypeExpr}
    {binderImage : TypeExpr → TypeExpr}
    (safe : typed.ReflectiveSupportSafeAt
      source.costWholeReflectionProfile support available binderImage) :
    ∃ argumentTyped : WellSorted.HasType source.costWholeLanguage targetFree
        targetBound argument (mapTypeExpr (color.symbols source) sourceExpected),
      ∃ argumentsTyped : WellSorted.ArgumentsHaveTypes
          source.costWholeLanguage targetFree targetBound arguments
            (parameters.map (mapTermParam (color.symbols source))),
        argumentTyped.ReflectiveSupportSafeAt
            source.costWholeReflectionProfile support available binderImage ∧
          argumentsTyped.ReflectiveSupportSafeAt
            source.costWholeReflectionProfile support available binderImage := by
  cases safe with
  | @cons bound argument arguments mappedParameter mappedParameters expected
      representation mappedParameterType argumentTyped argumentsTyped available
      binderImage argumentSafe argumentsSafe =>
      have mappedExpected : WellSorted.parameterType?
          (mapTermParam (color.symbols source) parameter) =
            some (mapTypeExpr (color.symbols source) sourceExpected) := by
        simp [WellSorted.parameterType?_mapTermParam, parameterType]
      have expectedEquality : expected =
          mapTypeExpr (color.symbols source) sourceExpected :=
        Option.some.inj (mappedParameterType.symm.trans mappedExpected)
      cases expectedEquality
      exact ⟨argumentTyped, argumentsTyped, argumentSafe, argumentsSafe⟩

/-- Exact head/tail inversion for a support-safe homogeneous element spine. -/
theorem elementsSafeAt_cons
    {source : CIGSLT} {targetFree : WellSorted.FreeTypeContext}
    {targetBound : List TypeExpr} {element : Pattern}
    {elements : List Pattern} {elementType : TypeExpr}
    {typed : WellSorted.ElementsHaveType source.costWholeLanguage targetFree
      targetBound (element :: elements) elementType}
    {support : ContextSupport.Support} {available : List TypeExpr}
    {binderImage : TypeExpr → TypeExpr}
    (safe : typed.ReflectiveSupportSafeAt source.costWholeReflectionProfile
      support available binderImage) :
    ∃ elementTyped : WellSorted.HasType source.costWholeLanguage targetFree
        targetBound element elementType,
      ∃ elementsTyped : WellSorted.ElementsHaveType source.costWholeLanguage
          targetFree targetBound elements elementType,
        elementTyped.ReflectiveSupportSafeAt source.costWholeReflectionProfile
            support available binderImage ∧
          elementsTyped.ReflectiveSupportSafeAt
            source.costWholeReflectionProfile support available binderImage := by
  cases safe with
  | cons elementSafe elementsSafe =>
      exact ⟨_, _, elementSafe, elementsSafe⟩

mutual
  /-- Synchronize a genuine static-region plan, one exact occurrence in its
  decoration, and arbitrary support safety of the target term.  Structural
  cases recurse through the plan; boundary cases alone invoke the exact child
  induction hypothesis above. -/
  theorem CostStaticRegionPlan.semanticLeafWitness
      {source : CIGSLT} {color : CostStaticColor}
      {targetFree : WellSorted.FreeTypeContext}
      {sourceBound targetBound : List TypeExpr}
      {thinning : CostStaticBinderThinning source color sourceBound targetBound}
      {sourceAvailable : List TypeExpr} {outer : OneHoleContext}
      {pattern : Pattern} {sourceType : TypeExpr}
      (plan : CostStaticRegionPlan source color targetFree sourceBound
        targetBound thinning sourceAvailable outer pattern sourceType)
      (collectionDeterministic :
        WellSorted.CollectionChoiceDeterministic source.costWholeLanguage)
      {globalOccurrences : List CostRegionOccurrence}
      (globalTable : TypedCostRegionBoundaryTable source color targetFree
        globalOccurrences)
      (values : TypedCostRegionBoundaryTable.Values source color targetFree
        globalTable)
      (entriesSubset : plan.boundaryTable.entries ⊆ globalTable.entries)
      {targetTyped : WellSorted.HasType source.costWholeLanguage targetFree
        targetBound pattern (mapTypeExpr (color.symbols source) sourceType)}
      {support : ContextSupport.Support} {reflectiveAvailable : List TypeExpr}
      {binderImage : TypeExpr → TypeExpr}
      (targetSafe : targetTyped.ReflectiveSupportSafeAt
        source.costWholeReflectionProfile support reflectiveAvailable binderImage)
      {root : Pattern}
      (parameter : CostStaticParameterOccurrence source color targetFree
        globalTable values root)
      {name : String} {context : OneHoleContext}
      {planAvailable : List TypeExpr}
      (planOccurrence : CostStaticPlanAbstractOccurrence source name
        plan.decoration context planAvailable)
      (nameEquality : parameter.fvarOccurrence.name = name)
      (childrenPreserve : CostStaticBoundaryChildReflectiveSupportPreserving
        globalTable values support binderImage) :
      CostStaticPlanSemanticLeafWitness planOccurrence parameter support
        binderImage := by
    cases plan with
    | bvar sourceIndex lookup correspondence availableScope =>
        cases planOccurrence
    | @fvar sourceBound targetBound sourceAvailable thinning outer sourceName
        sourceType targetLookup =>
        cases planOccurrence with
        | sourceFVar =>
            exact ⟨nameEquality, reflectiveAvailable,
              sourceLeafSemanticSafeAt targetLookup targetSafe parameter
                nameEquality⟩
    | boundaryApplication constructor rendered outsideCurrent certified
        certifies =>
        cases planOccurrence with
        | boundaryApplication =>
            have localMembership : certified.typed ∈
                [certified.typed] := List.mem_cons_self
            have globalMembership : certified.typed ∈ globalTable.entries :=
              entriesSubset localMembership
            exact ⟨nameEquality, reflectiveAvailable,
              boundaryLeafSemanticSafeAt certified.typed globalMembership
                certified.content_eq certified.targetType_eq targetSafe
                  childrenPreserve parameter nameEquality⟩
    | application constructor rendered current preimage notBare children =>
        obtain ⟨before, child, after, inner, decomposition, ⟨nested⟩⟩ :=
          CostStaticPlanAbstractOccurrence.application_split planOccurrence
        obtain ⟨argumentsTyped, argumentsSafe⟩ :=
          applicationArgumentsSafe constructor rendered preimage targetSafe
        obtain ⟨leafAvailable, leafSafe⟩ :=
          CostStaticArgumentPlan.semanticLeafSafeAt
            (name := name) (planAvailable := planAvailable)
            children collectionDeterministic globalTable values entriesSubset
              argumentsSafe
              decomposition nested parameter nameEquality childrenPreserve
        exact ⟨nameEquality, leafAvailable, leafSafe⟩
    | lambda bodyPlan =>
        cases planOccurrence with
        | lambda nested =>
            cases targetSafe with
            | lambda bodySafe =>
                obtain ⟨_, nestedAvailable, nestedSafe⟩ :=
                  CostStaticRegionPlan.semanticLeafWitness
                    (name := name) (planAvailable := planAvailable)
                    bodyPlan collectionDeterministic globalTable values
                      entriesSubset bodySafe parameter nested nameEquality
                        childrenPreserve
                exact ⟨nameEquality, nestedAvailable, nestedSafe⟩
    | multiLambda bodyPlan =>
        cases planOccurrence with
        | multiLambda nested =>
            cases targetSafe with
            | multiLambda bodySafe =>
                obtain ⟨_, nestedAvailable, nestedSafe⟩ :=
                  CostStaticRegionPlan.semanticLeafWitness
                    (name := name) (planAvailable := planAvailable)
                    bodyPlan collectionDeterministic globalTable values
                      entriesSubset bodySafe parameter nested nameEquality
                        childrenPreserve
                exact ⟨nameEquality, nestedAvailable, nestedSafe⟩
    | collection choice selected children =>
        obtain ⟨before, child, after, inner, decomposition, ⟨nested⟩⟩ :=
          CostStaticPlanAbstractOccurrence.collection_split planOccurrence
        obtain ⟨elementsTyped, elementsSafe⟩ :=
          collectionElementsSafe collectionDeterministic choice selected
            targetSafe
        obtain ⟨leafAvailable, leafSafe⟩ :=
          CostStaticElementPlan.semanticLeafSafeAt
            (name := name) (planAvailable := planAvailable)
            children collectionDeterministic globalTable values entriesSubset
              elementsSafe
              decomposition nested parameter nameEquality childrenPreserve
        exact ⟨nameEquality, leafAvailable, leafSafe⟩
    | boundaryCollection currentRejected oppositeChoice oppositeSelected
        certified certifies =>
        cases planOccurrence with
        | boundaryCollection =>
            have localMembership : certified.typed ∈
                [certified.typed] := List.mem_cons_self
            have globalMembership : certified.typed ∈ globalTable.entries :=
              entriesSubset localMembership
            exact ⟨nameEquality, reflectiveAvailable,
              boundaryLeafSemanticSafeAt certified.typed globalMembership
                certified.content_eq certified.targetType_eq targetSafe
                  childrenPreserve parameter nameEquality⟩

  /-- Application-spine synchronization locates the selected child decoration
  without forgetting its position, then delegates exactly once to that child
  plan. -/
  theorem CostStaticArgumentPlan.semanticLeafSafeAt
      {source : CIGSLT} {color : CostStaticColor}
      {targetFree : WellSorted.FreeTypeContext}
      {sourceBound targetBound : List TypeExpr}
      {thinning : CostStaticBinderThinning source color sourceBound targetBound}
      {sourceAvailable : List TypeExpr} {outer : OneHoleContext}
      {wireName : String} {before arguments : List Pattern}
      {parameters : List TermParam}
      (plan : CostStaticArgumentPlan source color targetFree sourceBound
        targetBound thinning sourceAvailable outer wireName before arguments
          parameters)
      (collectionDeterministic :
        WellSorted.CollectionChoiceDeterministic source.costWholeLanguage)
      {globalOccurrences : List CostRegionOccurrence}
      (globalTable : TypedCostRegionBoundaryTable source color targetFree
        globalOccurrences)
      (values : TypedCostRegionBoundaryTable.Values source color targetFree
        globalTable)
      (entriesSubset : plan.boundaryTable.entries ⊆ globalTable.entries)
      {argumentsTyped : WellSorted.ArgumentsHaveTypes source.costWholeLanguage
        targetFree targetBound arguments
          (parameters.map (mapTermParam (color.symbols source)))}
      {support : ContextSupport.Support} {reflectiveAvailable : List TypeExpr}
      {binderImage : TypeExpr → TypeExpr}
      (argumentsSafe : argumentsTyped.ReflectiveSupportSafeAt
        source.costWholeReflectionProfile support reflectiveAvailable binderImage)
      {selectedBefore selectedAfter : List (CostStaticPlanDecoration source)}
      {selectedDecoration : CostStaticPlanDecoration source}
      {name : String} {inner : OneHoleContext}
      {planAvailable : List TypeExpr}
      (decomposition : plan.decorations =
        selectedBefore ++ selectedDecoration :: selectedAfter)
      (nested : CostStaticPlanAbstractOccurrence source name selectedDecoration
        inner planAvailable)
      {root : Pattern}
      (parameter : CostStaticParameterOccurrence source color targetFree
        globalTable values root)
      (nameEquality : parameter.fvarOccurrence.name = name)
      (childrenPreserve : CostStaticBoundaryChildReflectiveSupportPreserving
        globalTable values support binderImage) :
      ∃ leafAvailable,
        CostStaticSemanticLeafSafeAt support leafAvailable binderImage
          parameter := by
    cases plan with
    | nil => simp [CostStaticArgumentPlan.decorations] at decomposition
    | cons representation parameterType head tail =>
        obtain ⟨_, _, headSafe, tailSafe⟩ :=
          argumentsSafeAt_cons_map (source := source) (color := color)
            parameterType argumentsSafe
        cases selectedBefore with
        | nil =>
            simp only [CostStaticArgumentPlan.decorations,
              List.nil_append, List.cons.injEq] at decomposition
            let headOccurrence :=
              CostStaticPlanAbstractOccurrence.reindexDecoration
                decomposition.1.symm nested
            have headSubset : head.boundaryTable.entries ⊆
                globalTable.entries := by
              intro boundary membership
              apply entriesSubset
              change boundary ∈
                (TypedCostRegionBoundaryTable.append head.boundaryTable
                  tail.boundaryTable).entries
              rw [TypedCostRegionBoundaryTable.entries_append]
              exact List.mem_append_left _ membership
            obtain ⟨_, headAvailable, headSemanticSafe⟩ :=
              CostStaticRegionPlan.semanticLeafWitness
                (name := name) (planAvailable := planAvailable)
                head collectionDeterministic globalTable values headSubset
                  headSafe parameter headOccurrence nameEquality
                    childrenPreserve
            exact ⟨headAvailable, headSemanticSafe⟩
        | cons skipped selectedBefore =>
            simp only [CostStaticArgumentPlan.decorations,
              List.cons_append, List.cons.injEq] at decomposition
            have tailSubset : tail.boundaryTable.entries ⊆
                globalTable.entries := by
              intro boundary membership
              apply entriesSubset
              change boundary ∈
                (TypedCostRegionBoundaryTable.append head.boundaryTable
                  tail.boundaryTable).entries
              rw [TypedCostRegionBoundaryTable.entries_append]
              exact List.mem_append_right _ membership
            exact CostStaticArgumentPlan.semanticLeafSafeAt
              (name := name) (planAvailable := planAvailable)
              tail collectionDeterministic globalTable values tailSubset
                tailSafe decomposition.2 nested parameter nameEquality
                  childrenPreserve

  /-- Homogeneous-collection companion to application-spine support
  synchronization. -/
  theorem CostStaticElementPlan.semanticLeafSafeAt
      {source : CIGSLT} {color : CostStaticColor}
      {targetFree : WellSorted.FreeTypeContext}
      {sourceBound targetBound : List TypeExpr}
      {thinning : CostStaticBinderThinning source color sourceBound targetBound}
      {sourceAvailable : List TypeExpr} {outer : OneHoleContext}
      {collectionType : CollType} {before elements : List Pattern}
      {rest : Option String} {sourceElementType : TypeExpr}
      (plan : CostStaticElementPlan source color targetFree sourceBound
        targetBound thinning sourceAvailable outer collectionType before elements
          rest sourceElementType)
      (collectionDeterministic :
        WellSorted.CollectionChoiceDeterministic source.costWholeLanguage)
      {globalOccurrences : List CostRegionOccurrence}
      (globalTable : TypedCostRegionBoundaryTable source color targetFree
        globalOccurrences)
      (values : TypedCostRegionBoundaryTable.Values source color targetFree
        globalTable)
      (entriesSubset : plan.boundaryTable.entries ⊆ globalTable.entries)
      {elementsTyped : WellSorted.ElementsHaveType source.costWholeLanguage
        targetFree targetBound elements
          (mapTypeExpr (color.symbols source) sourceElementType)}
      {support : ContextSupport.Support} {reflectiveAvailable : List TypeExpr}
      {binderImage : TypeExpr → TypeExpr}
      (elementsSafe : elementsTyped.ReflectiveSupportSafeAt
        source.costWholeReflectionProfile support reflectiveAvailable binderImage)
      {selectedBefore selectedAfter : List (CostStaticPlanDecoration source)}
      {selectedDecoration : CostStaticPlanDecoration source}
      {name : String} {inner : OneHoleContext}
      {planAvailable : List TypeExpr}
      (decomposition : plan.decorations =
        selectedBefore ++ selectedDecoration :: selectedAfter)
      (nested : CostStaticPlanAbstractOccurrence source name selectedDecoration
        inner planAvailable)
      {root : Pattern}
      (parameter : CostStaticParameterOccurrence source color targetFree
        globalTable values root)
      (nameEquality : parameter.fvarOccurrence.name = name)
      (childrenPreserve : CostStaticBoundaryChildReflectiveSupportPreserving
        globalTable values support binderImage) :
      ∃ leafAvailable,
        CostStaticSemanticLeafSafeAt support leafAvailable binderImage
          parameter := by
    cases plan with
    | nil => simp [CostStaticElementPlan.decorations] at decomposition
    | cons head tail =>
        obtain ⟨_, _, headSafe, tailSafe⟩ :=
          elementsSafeAt_cons (source := source) elementsSafe
        cases selectedBefore with
        | nil =>
            simp only [CostStaticElementPlan.decorations,
              List.nil_append, List.cons.injEq] at decomposition
            let headOccurrence :=
              CostStaticPlanAbstractOccurrence.reindexDecoration
                decomposition.1.symm nested
            have headSubset : head.boundaryTable.entries ⊆
                globalTable.entries := by
              intro boundary membership
              apply entriesSubset
              change boundary ∈
                (TypedCostRegionBoundaryTable.append head.boundaryTable
                  tail.boundaryTable).entries
              rw [TypedCostRegionBoundaryTable.entries_append]
              exact List.mem_append_left _ membership
            obtain ⟨_, headAvailable, headSemanticSafe⟩ :=
              CostStaticRegionPlan.semanticLeafWitness
                (name := name) (planAvailable := planAvailable)
                head collectionDeterministic globalTable values headSubset
                  headSafe parameter headOccurrence nameEquality
                    childrenPreserve
            exact ⟨headAvailable, headSemanticSafe⟩
        | cons skipped selectedBefore =>
            simp only [CostStaticElementPlan.decorations,
              List.cons_append, List.cons.injEq] at decomposition
            have tailSubset : tail.boundaryTable.entries ⊆
                globalTable.entries := by
              intro boundary membership
              apply entriesSubset
              change boundary ∈
                (TypedCostRegionBoundaryTable.append head.boundaryTable
                  tail.boundaryTable).entries
              rw [TypedCostRegionBoundaryTable.entries_append]
              exact List.mem_append_right _ membership
            exact CostStaticElementPlan.semanticLeafSafeAt
              (name := name) (planAvailable := planAvailable)
              tail collectionDeterministic globalTable values tailSubset
                tailSafe decomposition.2 nested parameter nameEquality
                  childrenPreserve
end

/-! ### Carrier-erasure canary -/

private def planOccurrenceAvailabilityCanary (source : CIGSLT)
    (available : List TypeExpr) : CostStaticPlanDecoration source :=
  .mk [] [] available .hole (.fvar "target") (.base "Canary") []
    (.fvar "source")

@[simp]
private theorem planOccurrenceAvailabilityCanary_abstractPattern
    (source : CIGSLT) (available : List TypeExpr) :
    (planOccurrenceAvailabilityCanary source available).abstractPattern =
      .fvar "source" :=
  by simp [planOccurrenceAvailabilityCanary,
    CostStaticPlanDecoration.abstractPattern,
    CostStaticPlanDecorationNode.abstractPattern]

/-- Negative canary: identical raw occurrence carriers can arise at different
reflective availabilities.  Recovering the coeffect from the zipper alone is
therefore impossible; the plan-indexed relation is essential evidence. -/
theorem rawOccurrence_does_not_determine_planAvailability
    (source : CIGSLT) (left right : List TypeExpr) (different : left ≠ right) :
    (planOccurrenceAvailabilityCanary source left).abstractPattern =
        (planOccurrenceAvailabilityCanary source right).abstractPattern ∧
      Nonempty (CostStaticPlanAbstractOccurrence source "source"
        (planOccurrenceAvailabilityCanary source left) .hole left) ∧
      Nonempty (CostStaticPlanAbstractOccurrence source "source"
        (planOccurrenceAvailabilityCanary source right) .hole right) ∧
      left ≠ right := by
  refine ⟨?_, ⟨.sourceFVar⟩, ⟨.sourceFVar⟩, different⟩
  simp

/-! ## Cost semantic-atom specialization -/

/-- Arbitrary caller-relative support evidence for every parameter occurrence
of one static frame, together with its exact greatest-suffix quotient over
semantic atoms.

The normal value is certified at each positional occurrence before equal
values are coalesced.  The quotient records only the support coeffect; exact
occurrence identity and semantic values remain in the existing inventory and
environment. -/
structure CostStaticOccurrenceSupportProfile
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {occurrences : List CostRegionOccurrence}
    {table : TypedCostRegionBoundaryTable source color targetFree occurrences}
    {values : TypedCostRegionBoundaryTable.Values source color targetFree table}
    {root : Pattern}
    {inventory : CostStaticParameterInventory source color targetFree table
      values root}
    (environment : CostStaticAtomEnvironment source color targetFree inventory)
    (support : ContextSupport.Support)
    (binderImage : TypeExpr → TypeExpr := id) where
  classSupport : OccurrenceClassSupport environment.occurrenceSlot
  occurrenceSafe : ∀ position,
    (inventory.occurrenceAtom position).normalTyped.ReflectiveSupportSafeAt
      source.costWholeReflectionProfile support
      (classSupport.occurrenceAvailable position) binderImage

namespace CostStaticOccurrenceSupportProfile

/-- Class-level reflective availability, indexed by the generated semantic
atom names used by the static frame.  This is the `inputSupport` map expected
by proof-relevant substitution alignment; constructing an aligned assignment
still requires a separate plan-level leaf theorem. -/
def semanticInputSupport
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {occurrences : List CostRegionOccurrence}
    {table : TypedCostRegionBoundaryTable source color targetFree occurrences}
    {values : TypedCostRegionBoundaryTable.Values source color targetFree table}
    {root : Pattern}
    {inventory : CostStaticParameterInventory source color targetFree table
      values root}
    {environment : CostStaticAtomEnvironment source color targetFree inventory}
    {support : ContextSupport.Support}
    {binderImage : TypeExpr → TypeExpr}
    (profile : CostStaticOccurrenceSupportProfile environment support
      binderImage) : ContextSupport.Support := fun name =>
  match environment.lookupAtom? name with
  | some slot => profile.classSupport.classAvailable slot
  | none => []

@[simp]
theorem semanticInputSupport_atomName
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {occurrences : List CostRegionOccurrence}
    {table : TypedCostRegionBoundaryTable source color targetFree occurrences}
    {values : TypedCostRegionBoundaryTable.Values source color targetFree table}
    {root : Pattern}
    {inventory : CostStaticParameterInventory source color targetFree table
      values root}
    {environment : CostStaticAtomEnvironment source color targetFree inventory}
    {support : ContextSupport.Support}
    {binderImage : TypeExpr → TypeExpr}
    (profile : CostStaticOccurrenceSupportProfile environment support
      binderImage)
    (slot : Fin environment.atomCount) :
    profile.semanticInputSupport (environment.atomName slot) =
      profile.classSupport.classAvailable slot := by
  simp [semanticInputSupport]

/-- Every semantic atom class has a proof-relevant positional representative.
This is intentionally data supplied by the support quotient, rather than an
unstated surjectivity assumption about arbitrary atom environments. -/
theorem exists_representative
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {occurrences : List CostRegionOccurrence}
    {table : TypedCostRegionBoundaryTable source color targetFree occurrences}
    {values : TypedCostRegionBoundaryTable.Values source color targetFree table}
    {root : Pattern}
    {inventory : CostStaticParameterInventory source color targetFree table
      values root}
    {environment : CostStaticAtomEnvironment source color targetFree inventory}
    {support : ContextSupport.Support}
    {binderImage : TypeExpr → TypeExpr}
    (profile : CostStaticOccurrenceSupportProfile environment support
      binderImage)
    (slot : Fin environment.atomCount) :
    ∃ position, environment.occurrenceSlot position = slot :=
  profile.classSupport.represented slot

/-- The selected support of an atom class is a suffix of every positional
context represented by that class. -/
theorem atomAvailable_suffix_occurrenceAvailable
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {occurrences : List CostRegionOccurrence}
    {table : TypedCostRegionBoundaryTable source color targetFree occurrences}
    {values : TypedCostRegionBoundaryTable.Values source color targetFree table}
    {root : Pattern}
    {inventory : CostStaticParameterInventory source color targetFree table
      values root}
    {environment : CostStaticAtomEnvironment source color targetFree inventory}
    {support : ContextSupport.Support}
    {binderImage : TypeExpr → TypeExpr}
    (profile : CostStaticOccurrenceSupportProfile environment support
      binderImage)
    (position : inventory.Occurrence) :
    profile.classSupport.classAvailable
        (environment.occurrenceSlot position) <:+
      profile.classSupport.occurrenceAvailable position :=
  profile.classSupport.classCommon position

/-- Every support suffix common to the occurrences of one semantic atom below
the same binder prefix is bounded by that prefix followed by the atom's
selected input support.  This is the exact class-level fact needed by a future
plan-to-substitution-alignment extraction. -/
theorem commonSuffix_prefix_semanticInputSupport
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {occurrences : List CostRegionOccurrence}
    {table : TypedCostRegionBoundaryTable source color targetFree occurrences}
    {values : TypedCostRegionBoundaryTable.Values source color targetFree table}
    {root : Pattern}
    {inventory : CostStaticParameterInventory source color targetFree table
      values root}
    {environment : CostStaticAtomEnvironment source color targetFree inventory}
    {support : ContextSupport.Support}
    {binderImage : TypeExpr → TypeExpr}
    (profile : CostStaticOccurrenceSupportProfile environment support
      binderImage)
    (slot : Fin environment.atomCount)
    (binderPrefix candidate : List TypeExpr)
    (candidateCommon : ∀ position,
      environment.occurrenceSlot position = slot →
        candidate <:+ binderPrefix ++
          profile.classSupport.occurrenceAvailable position) :
    candidate <:+ binderPrefix ++
      profile.semanticInputSupport (environment.atomName slot) := by
  rw [profile.semanticInputSupport_atomName slot]
  exact profile.classSupport.commonSuffix_prefix_classAvailable
    slot binderPrefix candidate candidateCommon

/-- Every normalized semantic atom is support-safe at the greatest common
suffix of exactly its positional occurrence class.  Equal semantic atoms are
identified only after `environment.occurrenceValue` transports the original
proof-relevant occurrence certificate into the class slot. -/
theorem classValueSafeAt
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {occurrences : List CostRegionOccurrence}
    {table : TypedCostRegionBoundaryTable source color targetFree occurrences}
    {values : TypedCostRegionBoundaryTable.Values source color targetFree table}
    {root : Pattern}
    {inventory : CostStaticParameterInventory source color targetFree table
      values root}
    {environment : CostStaticAtomEnvironment source color targetFree inventory}
    {support : ContextSupport.Support}
    {binderImage : TypeExpr → TypeExpr}
    (profile : CostStaticOccurrenceSupportProfile environment support
      binderImage)
    (collectionDeterministic :
      WellSorted.CollectionChoiceDeterministic source.costWholeLanguage)
    (slot : Fin environment.atomCount) :
    (environment.atomValue slot).normalTyped.ReflectiveSupportSafeAt
      source.costWholeReflectionProfile support
      (profile.classSupport.classAvailable slot) binderImage := by
  let Fiber :=
    { position : inventory.Occurrence //
      environment.occurrenceSlot position = slot }
  let fiberAvailable : Fiber → List TypeExpr := fun position =>
    profile.classSupport.occurrenceAvailable position.1
  obtain ⟨representative, representativeClass⟩ :=
    profile.exists_representative slot
  letI : Nonempty Fiber := ⟨⟨representative, representativeClass⟩⟩
  have greatest : GreatestCommonSuffix fiberAvailable
      (profile.classSupport.classAvailable slot) := by
    constructor
    · intro position
      simpa [fiberAvailable, position.2] using
        profile.classSupport.classCommon position.1
    · intro candidate common
      apply profile.classSupport.classGreatest slot candidate
      intro position classEquality
      exact common ⟨position, classEquality⟩
  apply WellSorted.HasType.ReflectiveSupportSafeAt.of_greatestCommonSuffix_of_object
    greatest collectionDeterministic (environment.atomValue slot).normalObject
  intro position
  have atomEquality : environment.atomValue slot =
      inventory.occurrenceAtom position.1 := by
    exact (congrArg environment.atomValue position.2).symm.trans
      (environment.occurrenceValue position.1)
  simpa [atomEquality, fiberAvailable] using
    (profile.occurrenceSafe position.1).castTyping

/-! ## Semantic-atom assignment adapter -/

/-- The two class-level obligations needed to turn occurrence-indexed support
into a reflective supported assignment.  `valueSafe` says that each semantic
atom is safe at the selected greatest common suffix.  `outputSupportSuffix`
is deliberately separate: safety below an internal binder does not imply
that the caller's support is a suffix of the atom's root availability.

Both fields are finite, indexed by genuine semantic atom slots, and retain
the complete typed atom value. -/
structure ClassValueSupport
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {occurrences : List CostRegionOccurrence}
    {table : TypedCostRegionBoundaryTable source color targetFree occurrences}
    {values : TypedCostRegionBoundaryTable.Values source color targetFree table}
    {root : Pattern}
    {inventory : CostStaticParameterInventory source color targetFree table
      values root}
    {environment : CostStaticAtomEnvironment source color targetFree inventory}
    {support : ContextSupport.Support}
    {binderImage : TypeExpr → TypeExpr}
    (profile : CostStaticOccurrenceSupportProfile environment support
      binderImage) : Prop where
  valueSafe : ∀ slot,
    (environment.atomValue slot).normalTyped.ReflectiveSupportSafeAt
      source.costWholeReflectionProfile support
      (profile.classSupport.classAvailable slot) binderImage
  outputSupportSuffix : ∀ slot targetName,
    targetName ∈ (environment.atomValue slot).key.normal.freeFvarNames →
      ∃ inner,
        profile.classSupport.classAvailable slot = inner ++ support targetName

/-- Assemble complete class-value support from the proved GCS rebasing theorem
and the independent root-footprint obligation.  The latter is kept as an
explicit argument because support safety below an internal binder does not
entail a root-level suffix. -/
def classValueSupport
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {occurrences : List CostRegionOccurrence}
    {table : TypedCostRegionBoundaryTable source color targetFree occurrences}
    {values : TypedCostRegionBoundaryTable.Values source color targetFree table}
    {root : Pattern}
    {inventory : CostStaticParameterInventory source color targetFree table
      values root}
    {environment : CostStaticAtomEnvironment source color targetFree inventory}
    {support : ContextSupport.Support}
    {binderImage : TypeExpr → TypeExpr}
    (profile : CostStaticOccurrenceSupportProfile environment support
      binderImage)
    (collectionDeterministic :
      WellSorted.CollectionChoiceDeterministic source.costWholeLanguage)
    (outputSupportSuffix : ∀ slot targetName,
      targetName ∈ (environment.atomValue slot).key.normal.freeFvarNames →
        ∃ inner,
          profile.classSupport.classAvailable slot =
            inner ++ support targetName) :
    profile.ClassValueSupport where
  valueSafe := profile.classValueSafeAt collectionDeterministic
  outputSupportSuffix := outputSupportSuffix

/-- Class-level support evidence supplies exactly the safe assignment consumed
by proof-relevant reflective substitution.  The existing restoration
assignment remains the semantic authority; this adapter adds only its
independently proved caller-relative coeffect. -/
def reflectiveSupportSafeAssignment
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {occurrences : List CostRegionOccurrence}
    {table : TypedCostRegionBoundaryTable source color targetFree occurrences}
    {values : TypedCostRegionBoundaryTable.Values source color targetFree table}
    {root : Pattern}
    {inventory : CostStaticParameterInventory source color targetFree table
      values root}
    {environment : CostStaticAtomEnvironment source color targetFree inventory}
    {support : ContextSupport.Support}
    {binderImage : TypeExpr → TypeExpr}
    (profile : CostStaticOccurrenceSupportProfile environment support
      binderImage)
    (classValues : profile.ClassValueSupport) :
    WellSorted.ReflectiveSupportSafeAssignment
      source.costWholeReflectionProfile source.costWholeLanguage
      environment.atomFreeContext targetFree environment.restorationSupport
      profile.semanticInputSupport support binderImage where
  toSupportedAssignment :=
    environment.restorationSupportedOpenAssignment.toSupportedAssignment
  valueSafe := by
    intro name type lookup
    simp only [CostStaticAtomEnvironment.atomFreeContext] at lookup
    cases selected : environment.lookupAtom? name with
    | none => simp [selected] at lookup
    | some slot =>
        simp only [selected, Option.map_some] at lookup
        have typeEquality :
            (environment.atomValue slot).key.targetType = type :=
          Option.some.inj lookup
        subst type
        simpa [CostStaticAtomEnvironment.restorationSupportedOpenAssignment,
          CostStaticAtomEnvironment.restorationSupport,
          CostStaticAtomEnvironment.restorationAssignment,
          semanticInputSupport, selected] using
            (classValues.valueSafe slot).castTyping
  outputSupportSuffix := by
    intro name type lookup targetName membership
    simp only [CostStaticAtomEnvironment.atomFreeContext] at lookup
    cases selected : environment.lookupAtom? name with
    | none => simp [selected] at lookup
    | some slot =>
        have valueMembership :
            targetName ∈
              (environment.atomValue slot).key.normal.freeFvarNames := by
          simpa [CostStaticAtomEnvironment.restorationSupportedOpenAssignment,
            CostStaticAtomEnvironment.restorationAssignment, selected] using
              membership
        simpa [semanticInputSupport, selected] using
          classValues.outputSupportSuffix slot targetName valueMembership

/-- Substitute a semantic-atom frame while retaining arbitrary reflective
support.  The two remaining frame premises are exact and proof-relevant:
`frameSafe` records the selected GCS coeffect at every source occurrence,
and `frameAligned` relates those reflective occurrences to the restoration
typing supports.  No endpoint equality or global support promise is used.

This is the local algebraic endpoint between occurrence-class support and the
generic substitution-composition theorem.  Plan/tree extraction of the two
frame premises remains a separate structural theorem. -/
theorem substituteAtomizedFramePreservingReflectiveSupport
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {occurrences : List CostRegionOccurrence}
    {table : TypedCostRegionBoundaryTable source color targetFree occurrences}
    {values : TypedCostRegionBoundaryTable.Values source color targetFree table}
    {root : Pattern}
    {inventory : CostStaticParameterInventory source color targetFree table
      values root}
    {environment : CostStaticAtomEnvironment source color targetFree inventory}
    {support : ContextSupport.Support}
    {binderImage : TypeExpr → TypeExpr}
    (profile : CostStaticOccurrenceSupportProfile environment support
      binderImage)
    (classValues : profile.ClassValueSupport)
    {bound available : List TypeExpr} {pattern : Pattern} {type : TypeExpr}
    {typed : WellSorted.HasType source.costWholeLanguage
      environment.atomFreeContext bound pattern type}
    (frameSafe : typed.ReflectiveSupportSafeAt
      source.costWholeReflectionProfile profile.semanticInputSupport available
        binderImage)
    (frameAligned : WellSorted.ReflectiveSupportSubstitutionAlignedAt
      environment.restorationSupport frameSafe) :
    ∃ outputTyped : WellSorted.HasType source.costWholeLanguage targetFree bound
        (ReflectiveContextSupport.substituteAt
          source.costWholeReflectionProfile profile.semanticInputSupport
            environment.restorationAssignment available.length pattern) type,
      outputTyped.ReflectiveSupportSafeAt source.costWholeReflectionProfile
        support available binderImage :=
  frameSafe.substitutePreservingReflectiveSupport
    (profile.reflectiveSupportSafeAssignment classValues) frameAligned

end CostStaticOccurrenceSupportProfile

end Mettapedia.Languages.ProcessCalculi.RhoCalculus
