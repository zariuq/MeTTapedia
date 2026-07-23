import Mettapedia.GSLT.LanguageDef.ContextSupport
import Mettapedia.GSLT.LanguageDef.SemanticCategory

/-!
# Computable canonical sections of presented GSLTs

A canonical section is computational data on the semantic carrier derived
from one exact `LanguageDef`.  It chooses a representative by normalization,
proves that normalization stays in the original equation class, and proves
that equivalent terms normalize identically.  The quotient representative is
therefore compiled with `Quotient.lift`; no representative is selected by
classical choice.
-/

namespace Mettapedia.GSLT.LanguageDef

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Substitution
open Mettapedia.OSLF.Framework.ConstructorCategory
open EquationSemantics

universe u

/-! ## Sections of arbitrary setoid quotients

The semantic carrier of a generated syntax need not itself be the raw term
type of an `IGSLT`.  In particular, a proof-relevant elaboration retains data
that its checked compact representation erases.  The quotient-section laws
are independent of that choice of carrier, so they live first at the ordinary
`Setoid` abstraction supplied by Lean. -/

/-- A computable choice of one exact representative for every class of an
arbitrary setoid. -/
structure ComputableSetoidSection (carrier : Type u)
    (relation : Setoid carrier) where
  normalize : carrier → carrier
  equivalent : ∀ term, relation.r (normalize term) term
  complete : ∀ {left right}, relation.r left right →
    normalize left = normalize right

namespace ComputableSetoidSection

/-- Setoid sections are determined by their representative function. -/
@[ext]
theorem ext {carrier : Type u} {relation : Setoid carrier}
    {first second : ComputableSetoidSection carrier relation}
    (normalize : first.normalize = second.normalize) : first = second := by
  cases first
  cases second
  cases normalize
  rfl

/-- The underlying setoid relation is exactly equality of representatives. -/
theorem equivalent_iff_normalize_eq {carrier : Type u}
    {relation : Setoid carrier}
    (canonical : ComputableSetoidSection carrier relation)
    (left right : carrier) :
    relation.r left right ↔
      canonical.normalize left = canonical.normalize right := by
  constructor
  · exact canonical.complete
  · intro normalized
    exact relation.iseqv.trans
      (relation.iseqv.symm (canonical.equivalent left))
      (by simpa [normalized] using canonical.equivalent right)

/-- Computed representatives are fixed points. -/
theorem normalize_idempotent {carrier : Type u} {relation : Setoid carrier}
    (canonical : ComputableSetoidSection carrier relation) (term : carrier) :
    canonical.normalize (canonical.normalize term) = canonical.normalize term :=
  canonical.complete (canonical.equivalent term)

/-- Compute the selected representative of an arbitrary setoid class. -/
def representative {carrier : Type u} {relation : Setoid carrier}
    (canonical : ComputableSetoidSection carrier relation) :
    Quotient relation → carrier :=
  Quotient.lift canonical.normalize
    (fun _ _ equivalent => canonical.complete equivalent)

/-- The computed representative belongs to the represented class. -/
theorem representative_spec {carrier : Type u} {relation : Setoid carrier}
    (canonical : ComputableSetoidSection carrier relation)
    (equivalenceClass : Quotient relation) :
    Quotient.mk relation (canonical.representative equivalenceClass) =
      equivalenceClass := by
  refine Quotient.inductionOn equivalenceClass ?_
  intro term
  exact Quotient.sound (canonical.equivalent term)

@[simp]
theorem representative_mk {carrier : Type u} {relation : Setoid carrier}
    (canonical : ComputableSetoidSection carrier relation) (term : carrier) :
    canonical.representative (Quotient.mk relation term) =
      canonical.normalize term :=
  rfl

/-- Selected representatives are already normalized. -/
theorem representative_normal {carrier : Type u} {relation : Setoid carrier}
    (canonical : ComputableSetoidSection carrier relation)
    (equivalenceClass : Quotient relation) :
    canonical.normalize (canonical.representative equivalenceClass) =
      canonical.representative equivalenceClass := by
  refine Quotient.inductionOn equivalenceClass ?_
  exact canonical.normalize_idempotent

end ComputableSetoidSection

/-- A computable section of the equational quotient of one presented iGSLT. -/
structure ComputableCanonicalSection (theory : IGSLT) where
  normalize : theory.toGSLT.Term → theory.toGSLT.Term
  equivalent : ∀ term, theory.toGSLT.equations.r (normalize term) term
  complete : ∀ {left right},
    theory.toGSLT.equations.r left right → normalize left = normalize right

namespace ComputableCanonicalSection

/-- Forget the presentation-specific indexing and expose the canonical
section through the generic setoid-section interface. -/
def toComputableSetoidSection {theory : IGSLT}
    (canonical : ComputableCanonicalSection theory) :
    ComputableSetoidSection theory.toGSLT.Term theory.toGSLT.equations where
  normalize := canonical.normalize
  equivalent := canonical.equivalent
  complete := canonical.complete

/-- Canonical sections are determined by their computable representative
function; the remaining fields are propositions about that function. -/
@[ext]
theorem ext {theory : IGSLT}
    {first second : ComputableCanonicalSection theory}
    (normalize : first.normalize = second.normalize) : first = second := by
  cases first
  cases second
  cases normalize
  rfl

/-- The section characterizes the authored equation relation exactly. -/
theorem equivalent_iff_normalize_eq {theory : IGSLT}
    (canonical : ComputableCanonicalSection theory)
    (left right : theory.toGSLT.Term) :
    theory.toGSLT.equations.r left right ↔
      canonical.normalize left = canonical.normalize right := by
  constructor
  · exact canonical.complete
  · intro normalized
    exact theory.toGSLT.equations.iseqv.trans
      (theory.toGSLT.equations.iseqv.symm (canonical.equivalent left))
      (by simpa [normalized] using canonical.equivalent right)

/-- Normalization is idempotent, derived from section soundness and
completeness rather than required as a separate field. -/
theorem normalize_idempotent {theory : IGSLT}
    (canonical : ComputableCanonicalSection theory)
    (term : theory.toGSLT.Term) :
    canonical.normalize (canonical.normalize term) = canonical.normalize term :=
  canonical.complete (canonical.equivalent term)

/-- Compute the selected representative of an equation class. -/
def representative {theory : IGSLT}
    (canonical : ComputableCanonicalSection theory) :
    Quotient theory.toGSLT.equations → theory.toGSLT.Term :=
  Quotient.lift canonical.normalize
    (fun _ _ equivalent => canonical.complete equivalent)

/-- The computed representative belongs to the class it represents. -/
theorem representative_spec {theory : IGSLT}
    (canonical : ComputableCanonicalSection theory)
    (equivalenceClass : Quotient theory.toGSLT.equations) :
    Quotient.mk theory.toGSLT.equations
        (canonical.representative equivalenceClass) = equivalenceClass := by
  refine Quotient.inductionOn equivalenceClass ?_
  intro term
  exact Quotient.sound (canonical.equivalent term)

/-- Section evaluation on an explicit class computes by normalization. -/
@[simp]
theorem representative_mk {theory : IGSLT}
    (canonical : ComputableCanonicalSection theory)
    (term : theory.toGSLT.Term) :
    canonical.representative
        (Quotient.mk theory.toGSLT.equations term) = canonical.normalize term :=
  rfl

/-- Representatives are already normalized. -/
theorem representative_normal {theory : IGSLT}
    (canonical : ComputableCanonicalSection theory)
    (equivalenceClass : Quotient theory.toGSLT.equations) :
    canonical.normalize (canonical.representative equivalenceClass) =
      canonical.representative equivalenceClass := by
  refine Quotient.inductionOn equivalenceClass ?_
  exact canonical.normalize_idempotent

end ComputableCanonicalSection

/-! ## Open presented equation carriers

The raw `Pattern` relation is useful for compiler proofs, but it deliberately
forgets the expected sort.  That forgetfulness is too coarse for a syntax
transformation that has multiple sort-indexed representations of the same raw
node.  The following carrier retains the authored sort, the open typing
contexts, and the object-language boundary while continuing to use the sole
authored equation declarations.
-/

/-- An open presented term at one authored base sort. -/
abbrev OpenTerm (theory : IGSLT) (free : WellSorted.FreeTypeContext)
    (bound : List TypeExpr)
    (sort : LangSort theory.presentation.presentation.language) :=
  WellSorted.OpenTerm theory.presentation.presentation.language free bound sort

/-- Transport an open term between propositionally equal fibers.  Its raw
pattern is unchanged; only the proof-indexed view of its contexts and sort is
transported. -/
def reindexOpenTerm {theory : IGSLT}
    {sourceFree targetFree : WellSorted.FreeTypeContext}
    {sourceBound targetBound : List TypeExpr}
    {sourceSort targetSort : LangSort theory.presentation.presentation.language}
    (freeEquality : sourceFree = targetFree)
    (boundEquality : sourceBound = targetBound)
    (sortEquality : sourceSort = targetSort)
    (term : OpenTerm theory sourceFree sourceBound sourceSort) :
    OpenTerm theory targetFree targetBound targetSort :=
  WellSorted.OpenTerm.reindex freeEquality boundEquality sortEquality term

@[simp]
theorem reindexOpenTerm_pattern {theory : IGSLT}
    {sourceFree targetFree : WellSorted.FreeTypeContext}
    {sourceBound targetBound : List TypeExpr}
    {sourceSort targetSort : LangSort theory.presentation.presentation.language}
    (freeEquality : sourceFree = targetFree)
    (boundEquality : sourceBound = targetBound)
    (sortEquality : sourceSort = targetSort)
    (term : OpenTerm theory sourceFree sourceBound sourceSort) :
    (reindexOpenTerm freeEquality boundEquality sortEquality term).1 = term.1 :=
  WellSorted.OpenTerm.reindex_pattern freeEquality boundEquality sortEquality
    term

/-- One authored contextual equation edge whose endpoints remain in the same
arbitrary-type open fiber.  This carrier is needed for supported assignments,
whose values may have arrow or collection type rather than an authored base
sort. -/
def openPatternEquationGenerator (language : LanguageDef)
    (free : WellSorted.FreeTypeContext) (bound : List TypeExpr)
    (type : TypeExpr)
    (left right : WellSorted.OpenPattern language free bound type) : Prop :=
  EquationSemantics.EquationContextStep defaultBasePremises language
    left.1 right.1

/-- Least contextual equivalence internal to one exact arbitrary-type open
fiber.  Every intermediate vertex retains typing, binder metadata,
object-pattern admissibility, and reflective scope. -/
def openPatternEquationSetoid (language : LanguageDef)
    (free : WellSorted.FreeTypeContext) (bound : List TypeExpr)
    (type : TypeExpr) :
    Setoid (WellSorted.OpenPattern language free bound type) where
  r := Relation.EqvGen
    (openPatternEquationGenerator language free bound type)
  iseqv :=
    { refl := Relation.EqvGen.refl
      symm := fun relation => Relation.EqvGen.symm _ _ relation
      trans := fun first second => Relation.EqvGen.trans _ _ _ first second }

/-- Every authored contextual equation generator preserves one exact typed
open fiber in both directions.  Bidirectionality is load-bearing because the
semantic equation relation is the symmetric-transitive closure of the
authored generator, while the raw generator itself is oriented.

This is a proposition about the sole `LanguageDef` relation, not a second
typing or equation authority.  Presentations whose equations change a sort,
object boundary, binder metadata, or reflective scope do not satisfy it. -/
def OpenEquationFiberStable (language : LanguageDef) : Prop :=
  ∀ {free : WellSorted.FreeTypeContext} {bound : List TypeExpr}
    {type : TypeExpr} {left right : Pattern},
    EquationSemantics.EquationContextStep defaultBasePremises language
        left right →
      (WellSorted.OpenPatternWellSorted language free bound type left ↔
        WellSorted.OpenPatternWellSorted language free bound type right)

namespace OpenEquationFiberStable

/-- A raw contextual equation path preserves every exact open fiber once its
generators do.  The proof follows reflexivity, symmetry, and transitivity
without choosing any new representative. -/
theorem equationEquiv_iff {language : LanguageDef}
    (stable : OpenEquationFiberStable language)
    {free : WellSorted.FreeTypeContext} {bound : List TypeExpr}
    {type : TypeExpr} {left right : Pattern}
    (equivalent : EquationEquiv defaultBasePremises language left right) :
    WellSorted.OpenPatternWellSorted language free bound type left ↔
      WellSorted.OpenPatternWellSorted language free bound type right := by
  induction equivalent with
  | rel left right generator =>
      exact stable generator
  | refl term =>
      exact Iff.rfl
  | symm left right relation inductionHypothesis =>
      exact inductionHypothesis.symm
  | trans left middle right first second firstIH secondIH =>
      exact firstIH.trans secondIH

/-- Lift a raw equation path to an exact typed path, constructing the typing
certificate of every intermediate vertex from generator stability. -/
private theorem liftExists {language : LanguageDef}
    (stable : OpenEquationFiberStable language)
    {free : WellSorted.FreeTypeContext} {bound : List TypeExpr}
    {type : TypeExpr} {left right : Pattern}
    (equivalent : EquationEquiv defaultBasePremises language left right)
    (leftWellSorted :
      WellSorted.OpenPatternWellSorted language free bound type left) :
    ∃ rightWellSorted :
        WellSorted.OpenPatternWellSorted language free bound type right,
      (openPatternEquationSetoid language free bound type).r
        ⟨left, leftWellSorted⟩ ⟨right, rightWellSorted⟩ := by
  induction equivalent with
  | rel left right generator =>
      let rightWellSorted := (stable generator).mp leftWellSorted
      exact ⟨rightWellSorted, Relation.EqvGen.rel _ _ generator⟩
  | refl term =>
      exact ⟨leftWellSorted, Relation.EqvGen.refl _⟩
  | symm left right relation inductionHypothesis =>
      have originalLeftWellSorted :=
        (stable.equationEquiv_iff relation).mpr leftWellSorted
      obtain ⟨originalRightWellSorted, lifted⟩ :=
        inductionHypothesis originalLeftWellSorted
      exact ⟨originalLeftWellSorted,
        (openPatternEquationSetoid language free bound type).iseqv.symm
          (by simpa using lifted)⟩
  | trans left middle right first second firstIH secondIH =>
      obtain ⟨middleWellSorted, firstLifted⟩ := firstIH leftWellSorted
      obtain ⟨rightWellSorted, secondLifted⟩ := secondIH middleWellSorted
      exact ⟨rightWellSorted,
        (openPatternEquationSetoid language free bound type).iseqv.trans
          firstLifted secondLifted⟩

/-- Under fiber stability, raw contextual equivalence between two admitted
open objects is exactly realizable as a path whose every intermediate vertex
stays in that same typed fiber. -/
theorem toOpenPatternEquationSetoid {language : LanguageDef}
    (stable : OpenEquationFiberStable language)
    {free : WellSorted.FreeTypeContext} {bound : List TypeExpr}
    {type : TypeExpr}
    {left right : WellSorted.OpenPattern language free bound type}
    (equivalent : EquationEquiv defaultBasePremises language left.1 right.1) :
    (openPatternEquationSetoid language free bound type).r left right := by
  obtain ⟨rightWellSorted, lifted⟩ :=
    stable.liftExists equivalent left.2
  have rightEquality :
      (⟨right.1, rightWellSorted⟩ :
        WellSorted.OpenPattern language free bound type) = right :=
    Subtype.ext (by rfl)
  simpa only [rightEquality] using lifted

end OpenEquationFiberStable

/-- Forget a fiber-internal arbitrary-type equation derivation to the raw
contextual relation generated by the same authored `LanguageDef`. -/
theorem openPatternEquationSetoid_to_equationEquiv
    {language : LanguageDef} {free : WellSorted.FreeTypeContext}
    {bound : List TypeExpr} {type : TypeExpr}
    {left right : WellSorted.OpenPattern language free bound type}
    (equivalent :
      (openPatternEquationSetoid language free bound type).r left right) :
    EquationEquiv defaultBasePremises language left.1 right.1 := by
  induction equivalent with
  | rel left right generator =>
      exact Relation.EqvGen.rel _ _ generator
  | refl term =>
      exact Relation.EqvGen.refl term.1
  | symm left right relation inductionHypothesis =>
      exact Relation.EqvGen.symm _ _ inductionHypothesis
  | trans left middle right first second firstIH secondIH =>
      exact Relation.EqvGen.trans _ _ _ firstIH secondIH

/-- One authored contextual equation edge whose endpoints remain in the same
open sorted fiber.  Restricting the generator, rather than only the endpoints
of a raw equivalence chain, prevents ill-sorted intermediates from mediating
semantic equality. -/
def openEquationGenerator (theory : IGSLT)
    (free : WellSorted.FreeTypeContext) (bound : List TypeExpr)
    (sort : LangSort theory.presentation.presentation.language)
    (left right : OpenTerm theory free bound sort) : Prop :=
  EquationSemantics.EquationContextStep defaultBasePremises
    theory.presentation.presentation.language left.1 right.1

/-- Least static equivalence generated inside one exact open sorted fiber. -/
def openEquationSetoid (theory : IGSLT)
    (free : WellSorted.FreeTypeContext) (bound : List TypeExpr)
    (sort : LangSort theory.presentation.presentation.language) :
    Setoid (OpenTerm theory free bound sort) where
  r := Relation.EqvGen (openEquationGenerator theory free bound sort)
  iseqv :=
    { refl := Relation.EqvGen.refl
      symm := fun relation => Relation.EqvGen.symm _ _ relation
      trans := fun first second => Relation.EqvGen.trans _ _ _ first second }

/-- In a presentation with no static generators, every open sorted fiber has
only syntactic equality. -/
theorem openEquationSetoid_iff_eq_of_no_generators
    (theory : IGSLT)
    (equationsEmpty :
      theory.presentation.presentation.language.equations = [])
    (reflectiveEmpty :
      theory.presentation.presentation.language.reflectivePresentations = [])
    {free : WellSorted.FreeTypeContext} {bound : List TypeExpr}
    {sort : LangSort theory.presentation.presentation.language}
    (left right : OpenTerm theory free bound sort) :
    (openEquationSetoid theory free bound sort).r left right ↔
      left = right := by
  constructor
  · intro equivalent
    induction equivalent with
    | rel left right step =>
        apply Subtype.ext
        exact (EquationSemantics.equationEquiv_iff_eq_of_no_generators
          equationsEmpty reflectiveEmpty left.1 right.1).mp
            (Relation.EqvGen.rel _ _ step)
    | refl term => rfl
    | symm left right relation inductionHypothesis =>
        exact inductionHypothesis.symm
    | trans left middle right first second firstIH secondIH =>
        exact firstIH.trans secondIH
  · rintro rfl
    exact Relation.EqvGen.refl left

/-- Forget the extra closed-term conditions while retaining the interacting
sort and its typing derivation. -/
def closedTermToOpen {theory : IGSLT}
    (term : theory.toGSLT.Term) :
    OpenTerm theory WellSorted.FreeTypeContext.empty []
      theory.presentation.interactingLangSort :=
  ⟨term.1, term.2.1, term.2.2.2.1, term.2.2.2.2.1,
    term.2.2.2.2.2.2⟩

/-- At empty free and bound contexts, sorting supplies ordinary de Bruijn
scope and the open carrier's reflective condition supplies quotation scope.
Hence every open object term in that fiber is already a closed semantic
term; groundness is derived rather than stored twice. -/
def openTermEmptyToClosed {theory : IGSLT}
    {sort : LangSort theory.presentation.presentation.language}
    (term : OpenTerm theory WellSorted.FreeTypeContext.empty [] sort) :
    WellSorted.ClosedTerm
      theory.presentation.presentation.language sort := by
  have ordinaryScope : term.1.isWellScopedAt 0 = true := by
    simpa using term.2.1.isWellScopedAt
  have scopeSafe : WellSorted.ScopeSafe
      theory.presentation.presentation.language term.1 :=
    ⟨ordinaryScope, term.2.2.2.2⟩
  exact ⟨term.1, term.2.1,
    WellSorted.ground_of_closed_sorting term.2.1 term.2.2.2.1 scopeSafe,
    term.2.2.1, term.2.2.2.1, scopeSafe⟩

@[simp]
theorem openTermEmptyToClosed_pattern {theory : IGSLT}
    {sort : LangSort theory.presentation.presentation.language}
    (term : OpenTerm theory WellSorted.FreeTypeContext.empty [] sort) :
    (openTermEmptyToClosed term).1 = term.1 :=
  rfl

@[simp]
theorem openTermEmptyToClosed_closedTermToOpen {theory : IGSLT}
    (term : theory.toGSLT.Term) :
    openTermEmptyToClosed (closedTermToOpen term) = term := by
  apply Subtype.ext
  rfl

@[simp]
theorem closedTermToOpen_openTermEmptyToClosed {theory : IGSLT}
    (term : OpenTerm theory WellSorted.FreeTypeContext.empty []
      theory.presentation.interactingLangSort) :
    closedTermToOpen (openTermEmptyToClosed term) = term := by
  apply Subtype.ext
  rfl

/-- Every equation path that stays in the closed semantic carrier also stays
in the corresponding open sorted carrier. -/
theorem presentedEquationSetoid_to_openEquationSetoid
    {theory : IGSLT} {left right : theory.toGSLT.Term}
    (equivalent : theory.toGSLT.equations.r left right) :
    (openEquationSetoid theory WellSorted.FreeTypeContext.empty []
      theory.presentation.interactingLangSort).r
        (closedTermToOpen left) (closedTermToOpen right) := by
  induction equivalent with
  | rel left right generator =>
      exact Relation.EqvGen.rel _ _ generator
  | refl term =>
      exact Relation.EqvGen.refl (closedTermToOpen term)
  | symm left right relation inductionHypothesis =>
      exact Relation.EqvGen.symm _ _ inductionHypothesis
  | trans left middle right first second firstIH secondIH =>
      exact Relation.EqvGen.trans _ _ _ firstIH secondIH

/-- In the empty interacting fiber, the open and closed presented equation
relations coincide.  Every intermediate open vertex is sorted and therefore
ordinary-scope safe; the remaining closed-carrier conditions are already
fields of `OpenTerm`. -/
theorem openEquationSetoid_to_presentedEquationSetoid
    {theory : IGSLT}
    {left right : OpenTerm theory WellSorted.FreeTypeContext.empty []
      theory.presentation.interactingLangSort}
    (equivalent :
      (openEquationSetoid theory WellSorted.FreeTypeContext.empty []
        theory.presentation.interactingLangSort).r left right) :
    theory.toGSLT.equations.r
      (openTermEmptyToClosed left) (openTermEmptyToClosed right) := by
  induction equivalent with
  | rel left right generator =>
      exact Relation.EqvGen.rel _ _ generator
  | refl term =>
      exact Relation.EqvGen.refl (openTermEmptyToClosed term)
  | symm left right relation inductionHypothesis =>
      exact Relation.EqvGen.symm _ _ inductionHypothesis
  | trans left middle right first second firstIH secondIH =>
      exact Relation.EqvGen.trans _ _ _ firstIH secondIH

/-- Computable representatives for every open authored-sort fiber.  The
normalizer receives the sort through its dependent carrier, so two identical
raw patterns at different sorts may normalize differently. -/
structure ComputableOpenSection (theory : IGSLT) where
  normalize : ∀ {free bound sort},
    OpenTerm theory free bound sort →
      OpenTerm theory free bound sort
  equivalent : ∀ {free bound sort}
      (term : OpenTerm theory free bound sort),
    (openEquationSetoid theory free bound sort).r (normalize term) term
  complete : ∀ {free bound sort}
      {left right : OpenTerm theory free bound sort},
    (openEquationSetoid theory free bound sort).r left right →
      normalize left = normalize right

namespace ComputableOpenSection

/-- One typed open fiber of an open section is an ordinary computable setoid
section.  This is the bridge used by generated proof-relevant carriers. -/
def toComputableSetoidSection {theory : IGSLT}
    (canonical : ComputableOpenSection theory)
    (free : WellSorted.FreeTypeContext) (bound : List TypeExpr)
    (sort : LangSort theory.presentation.presentation.language) :
    ComputableSetoidSection (OpenTerm theory free bound sort)
      (openEquationSetoid theory free bound sort) where
  normalize := canonical.normalize
  equivalent := canonical.equivalent
  complete := canonical.complete

/-- Construct an exact open canonical section from a typed soundness proof
and exact invariance under each authored equation generator.  Symmetry and
transitivity are supplied by the least equivalence closure; the caller must
prove the only substantive local cases.

This constructor does not weaken exactness to equation equivalence and does
not introduce a second relation: `generatorInvariant` is stated directly on
`openEquationGenerator`, hence on the sole authored `LanguageDef`. -/
def ofGeneratorInvariant {theory : IGSLT}
    (normalize : ∀ {free bound sort},
      OpenTerm theory free bound sort → OpenTerm theory free bound sort)
    (equivalent : ∀ {free bound sort}
      (term : OpenTerm theory free bound sort),
      (openEquationSetoid theory free bound sort).r (normalize term) term)
    (generatorInvariant : ∀ {free bound sort}
      {left right : OpenTerm theory free bound sort},
      openEquationGenerator theory free bound sort left right →
        normalize left = normalize right) :
    ComputableOpenSection theory where
  normalize := normalize
  equivalent := equivalent
  complete := by
    intro free bound sort left right relation
    induction relation with
    | rel left right generator =>
        exact generatorInvariant generator
    | refl term =>
        rfl
    | symm left right relation inductionHypothesis =>
        exact inductionHypothesis.symm
    | trans left middle right first second firstIH secondIH =>
        exact firstIH.trans secondIH

/-- Normalization commutes with transport between propositionally equal open
fibers.  This is dependent-function congruence, not an extra semantic law. -/
theorem normalize_reindex {theory : IGSLT}
    (canonical : ComputableOpenSection theory)
    {sourceFree targetFree : WellSorted.FreeTypeContext}
    {sourceBound targetBound : List TypeExpr}
    {sourceSort targetSort : LangSort theory.presentation.presentation.language}
    (freeEquality : sourceFree = targetFree)
    (boundEquality : sourceBound = targetBound)
    (sortEquality : sourceSort = targetSort)
    (term : OpenTerm theory sourceFree sourceBound sourceSort) :
    canonical.normalize
        (reindexOpenTerm freeEquality boundEquality sortEquality term) =
      reindexOpenTerm freeEquality boundEquality sortEquality
        (canonical.normalize term) := by
  cases freeEquality
  cases boundEquality
  cases sortEquality
  rfl

/-- Restrict an open section to the closed interacting fiber.  Unlike the
older raw-pattern bridge, every representative and every intermediate
equation vertex remains inside the declaration-derived typed carrier. -/
def toComputableCanonicalSection {theory : IGSLT}
    (canonical : ComputableOpenSection theory) :
    ComputableCanonicalSection theory where
  normalize := fun term =>
    openTermEmptyToClosed (canonical.normalize (closedTermToOpen term))
  equivalent := by
    intro term
    simpa using openEquationSetoid_to_presentedEquationSetoid
      (canonical.equivalent (closedTermToOpen term))
  complete := by
    intro left right equivalent
    exact congrArg openTermEmptyToClosed
      (canonical.complete
        (presentedEquationSetoid_to_openEquationSetoid equivalent))

/-- Sort-indexed normalization is idempotent in every open fiber. -/
theorem normalize_idempotent {theory : IGSLT}
    (canonical : ComputableOpenSection theory)
    {free bound sort} (term : OpenTerm theory free bound sort) :
    canonical.normalize (canonical.normalize term) =
      canonical.normalize term :=
  canonical.complete (canonical.equivalent term)

/-- The sort-indexed section characterizes its fiber relation exactly. -/
theorem equivalent_iff_normalize_eq {theory : IGSLT}
    (canonical : ComputableOpenSection theory)
    {free bound sort}
    (left right : OpenTerm theory free bound sort) :
    (openEquationSetoid theory free bound sort).r left right ↔
      canonical.normalize left = canonical.normalize right := by
  constructor
  · exact canonical.complete
  · intro normalized
    exact (openEquationSetoid theory free bound sort).iseqv.trans
      ((openEquationSetoid theory free bound sort).iseqv.symm
        (canonical.equivalent left))
      (by simpa [normalized] using canonical.equivalent right)

end ComputableOpenSection

/-! ## Contextual sections

The closed interacting fiber is the semantic carrier of an `IGSLT`, but it
does not contain enough data to transport canonicalization through a syntax
construction that places source terms beneath new constructors or binders.
For that purpose the same computation must be meaningful on the shared raw
pattern carrier and must characterize the authored contextual equation
relation there.  The closed section remains a derived view; no second
equation theory is introduced.
-/

/-- Forget a typed equation derivation to the raw contextual equation
relation generated by the same authored `LanguageDef`. -/
theorem presentedEquationSetoid_to_equationEquiv
    {theory : IGSLT} {left right : theory.toGSLT.Term}
    (equivalent : theory.toGSLT.equations.r left right) :
    EquationEquiv defaultBasePremises
      theory.presentation.presentation.language left.1 right.1 := by
  induction equivalent with
  | rel left right generator =>
      exact Relation.EqvGen.rel _ _ generator
  | refl term =>
      exact Relation.EqvGen.refl term.1
  | symm left right relation inductionHypothesis =>
      exact Relation.EqvGen.symm _ _ inductionHypothesis
  | trans left middle right first second firstIH secondIH =>
      exact Relation.EqvGen.trans _ _ _ firstIH secondIH

/-- A computable canonical section stable on the full contextual pattern
relation of one authored presentation.

The raw component supplies the missing open-term data needed by syntax
transformers. `mapsClosed` and `equivalentClosed` retain the exact semantic
boundary: normalization maps the established closed interacting carrier to
itself, and its equivalence proof stays inside that carrier at every
intermediate step. -/
structure ComputableContextualSection (theory : IGSLT) where
  normalize : Pattern → Pattern
  mapsClosed : ∀ term : theory.toGSLT.Term,
    WellSorted.ClosedTermWellSorted
      theory.presentation.presentation.language
      theory.presentation.interactingLangSort (normalize term.1)
  equivalent : ∀ pattern,
    EquationEquiv defaultBasePremises
      theory.presentation.presentation.language (normalize pattern) pattern
  complete : ∀ {left right},
    EquationEquiv defaultBasePremises
      theory.presentation.presentation.language left right →
        normalize left = normalize right
  equivalentClosed : ∀ term : theory.toGSLT.Term,
    theory.toGSLT.equations.r
      ⟨normalize term.1, mapsClosed term⟩ term

namespace ComputableContextualSection

/-- Restrict contextual normalization to the closed interacting fiber. -/
def normalizeClosed {theory : IGSLT}
    (canonical : ComputableContextualSection theory) :
    theory.toGSLT.Term → theory.toGSLT.Term :=
  fun term => ⟨canonical.normalize term.1, canonical.mapsClosed term⟩

@[simp]
theorem normalizeClosed_pattern {theory : IGSLT}
    (canonical : ComputableContextualSection theory)
    (term : theory.toGSLT.Term) :
    (canonical.normalizeClosed term).1 = canonical.normalize term.1 :=
  rfl

/-- Every contextual section induces the paper-facing section on the closed
interacting quotient. -/
def toComputableCanonicalSection {theory : IGSLT}
    (canonical : ComputableContextualSection theory) :
    ComputableCanonicalSection theory where
  normalize := canonical.normalizeClosed
  equivalent := canonical.equivalentClosed
  complete := by
    intro left right equivalent
    apply Subtype.ext
    exact canonical.complete
      (presentedEquationSetoid_to_equationEquiv equivalent)

/-- Contextual normalization is idempotent on every raw pattern. -/
theorem normalize_idempotent {theory : IGSLT}
    (canonical : ComputableContextualSection theory) (pattern : Pattern) :
    canonical.normalize (canonical.normalize pattern) =
      canonical.normalize pattern :=
  canonical.complete (canonical.equivalent pattern)

/-- Replacing the contents of a structural hole by their canonical
representative does not change the canonical representative of the whole
term.  The law follows from contextual closure and section completeness, so
it is deliberately not stored as another field of the section. -/
theorem normalize_fill_normalize {theory : IGSLT}
    (canonical : ComputableContextualSection theory)
    (context : Mettapedia.OSLF.MeTTaIL.DerivedContexts.OneHoleContext)
    (pattern : Pattern) :
    canonical.normalize
        (context.fill (canonical.normalize pattern)) =
      canonical.normalize (context.fill pattern) := by
  apply canonical.complete
  exact EquationSemantics.equationEquiv_fill context
    (canonical.equivalent pattern)

/-- Raw contextual equivalence is characterized exactly by the computed
representative. -/
theorem equivalent_iff_normalize_eq {theory : IGSLT}
    (canonical : ComputableContextualSection theory)
    (left right : Pattern) :
    EquationEquiv defaultBasePremises
        theory.presentation.presentation.language left right ↔
      canonical.normalize left = canonical.normalize right := by
  constructor
  · exact canonical.complete
  · intro normalized
    apply Relation.EqvGen.trans _ (canonical.normalize left) _
      (Relation.EqvGen.symm _ _ (canonical.equivalent left))
    change EquationEquiv defaultBasePremises
      theory.presentation.presentation.language
        (canonical.normalize left) right
    rw [normalized]
    exact canonical.equivalent right

end ComputableContextualSection

/-! ## Contextual open sections -/

/-- A computable section on every typed open fiber that preserves exact
free-variable support across ordinary binders and reflective quotation
boundaries.

The open fiber is the load-bearing contextual interface: it retains the
authored sort, free context, and binder context that a syntax construction
needs in order to normalize rigid boundaries soundly.  Requiring this
computation also to be one context-free `Pattern → Pattern` function would be
too strong: the same raw de Bruijn pattern can inhabit distinct binder fibers.
A theory may separately expose a `ComputableContextualSection` when it has a
useful raw canonicalizer, but continued interaction and iterable syntax do not
discard their typing indices merely to demand one. -/
structure ComputableContextualOpenSection (theory : IGSLT)
    extends ComputableOpenSection theory where
  preservesFreeVariableSupport : ∀ {free bound sort}
      (term : OpenTerm theory free bound sort) {name : String},
    name ∈ (normalize term).1.freeFvarNames → name ∈ term.1.freeFvarNames
  /-- The indexed family of open sections is natural under changes to unused
  free-context entries.  This is exact raw representative equality, not only
  contextual equivalence: the same syntax in two agreeing contexts cannot be
  assigned two different canonical representatives. -/
  normalizeRecontextualizeFree :
    ∀ {sourceFree targetFree : WellSorted.FreeTypeContext}
      {bound : List TypeExpr}
      {sort : LangSort theory.presentation.presentation.language}
      (term : OpenTerm theory sourceFree bound sort)
      (preserves : ∀ {name freeType},
        name ∈ term.1.freeFvarNames →
        sourceFree name = some freeType →
          targetFree name = some freeType),
    (normalize (term.recontextualizeFree preserves)).1 =
      (normalize term).1
  preservesReflectiveSupport : ∀ {free bound sort}
      (term : OpenTerm theory free bound sort)
      (support : ContextSupport.Support) (available : List TypeExpr)
      (binderImage : TypeExpr → TypeExpr),
    term.2.1.ReflectiveSupportSafeAt support available binderImage →
      (normalize term).2.1.ReflectiveSupportSafeAt support available
        binderImage

namespace ComputableContextualOpenSection

/-- Forget the contextual and support theorems while retaining the exact
computable open section. -/
abbrev openSection {theory : IGSLT}
    (canonical : ComputableContextualOpenSection theory) :
    ComputableOpenSection theory :=
  canonical.toComputableOpenSection

/-- Restriction to the closed interacting fiber uses the same typed open
normalizer; agreement with the raw contextual normalizer is bundled above. -/
def toComputableCanonicalSection {theory : IGSLT}
    (canonical : ComputableContextualOpenSection theory) :
    ComputableCanonicalSection theory :=
  canonical.toComputableOpenSection.toComputableCanonicalSection

/-- Normalization in a typed open fiber cannot introduce a free name outside
that fiber's finite restricted context.  This is the support bound needed by
syntax constructions that restore a finite table of rigid region parameters
after normalization. -/
theorem normalize_mem_of_restrictTo
    {theory : IGSLT} (canonical : ComputableContextualOpenSection theory)
    {free : WellSorted.FreeTypeContext} {names : List String}
    {bound : List TypeExpr}
    {sort : LangSort theory.presentation.presentation.language}
    (term : OpenTerm theory (free.restrictTo names) bound sort)
    {name : String}
    (membership : name ∈ (canonical.normalize term).1.freeFvarNames) :
    name ∈ names := by
  exact (canonical.normalize term).mem_of_restrictTo_freeFvarNames
    membership

/-- Typed open normalization introduces no new free-variable name.  The proof
reindexes the input by its exact finite support, then uses the fact that the
section stays in that same fiber.  Equations may still delete unused support;
equality of occurrence lists is neither required nor claimed. -/
theorem normalize_freeFvarNames_subset
    {theory : IGSLT} (canonical : ComputableContextualOpenSection theory)
    {free : WellSorted.FreeTypeContext} {bound : List TypeExpr}
    {sort : LangSort theory.presentation.presentation.language}
    (term : OpenTerm theory free bound sort) {name : String}
    (membership : name ∈ (canonical.normalize term).1.freeFvarNames) :
    name ∈ term.1.freeFvarNames :=
  canonical.preservesFreeVariableSupport term membership

end ComputableContextualOpenSection

end Mettapedia.GSLT.LanguageDef
