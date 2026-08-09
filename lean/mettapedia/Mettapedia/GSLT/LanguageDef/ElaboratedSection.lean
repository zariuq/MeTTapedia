import Mettapedia.GSLT.LanguageDef.ReflectiveCanonicalSection

/-!
# Proof-relevant open carriers over authored GSLTs

An elaborated carrier retains checked semantic data that compact object syntax
may erase.  The authored `IGSLT` still supplies the unique syntax, typing, and
equation authority: erasure lands in its exact typed open carrier, and every
elaborated semantic equation must erase to an authored equation path.

This file deliberately stops short of prescribing the data retained by an
elaboration or the algebra carried by a decoration.  Those are construction-
specific.  It isolates only the split-epimorphism and support-erasure laws
needed before an exact section can be constructed on a richer carrier.
-/

namespace Mettapedia.GSLT.LanguageDef

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.Framework.ConstructorCategory

universe u

/-- A proof-relevant carrier above every exact typed open fiber of one
authored interactive presentation.

`compile` chooses checked elaboration evidence for compact execution, while
`erase` forgets that evidence.  The retraction law makes compact syntax a
faithful input interface without asserting that erasure is injective. -/
structure OpenElaborationCarrier (theory : IGSLT) where
  Carrier : (free : WellSorted.FreeTypeContext) →
    (bound : List TypeExpr) →
    (sort : LangSort theory.presentation.presentation.language) → Type u
  erase : ∀ {free bound sort}, Carrier free bound sort →
    OpenTerm theory free bound sort
  compile : ∀ {free bound sort}, OpenTerm theory free bound sort →
    Carrier free bound sort
  erase_compile : ∀ {free bound sort}
    (term : OpenTerm theory free bound sort), erase (compile term) = term

namespace OpenElaborationCarrier

/-- A checked compiler into a proof-relevant carrier is injective because
compact erasure is its left inverse. -/
theorem compile_injective {theory : IGSLT}
    (carrier : OpenElaborationCarrier theory) {free bound sort} :
    Function.Injective
      (carrier.compile : OpenTerm theory free bound sort →
        carrier.Carrier free bound sort) := by
  intro left right equality
  have erased := congrArg carrier.erase equality
  simpa only [carrier.erase_compile] using erased

/-- Every checked compact open term is the erasure of at least one
proof-relevant elaboration. -/
theorem erase_surjective {theory : IGSLT}
    (carrier : OpenElaborationCarrier theory) {free bound sort} :
    Function.Surjective
      (carrier.erase : carrier.Carrier free bound sort →
        OpenTerm theory free bound sort) := by
  intro term
  exact ⟨carrier.compile term, carrier.erase_compile term⟩

/-- The compact observation relation pulls the sole authored equation setoid
back along erasure.  It is intentionally observational: it need not preserve
proof-relevant elaboration identity. -/
def compactObservationSetoid {theory : IGSLT}
    (carrier : OpenElaborationCarrier theory)
    (free : WellSorted.FreeTypeContext) (bound : List TypeExpr)
    (sort : LangSort theory.presentation.presentation.language) :
    Setoid (carrier.Carrier free bound sort) where
  r left right :=
    (openEquationSetoid theory free bound sort).r
      (carrier.erase left) (carrier.erase right)
  iseqv := by
    constructor
    · intro term
      exact (openEquationSetoid theory free bound sort).iseqv.refl _
    · intro left right equivalent
      exact (openEquationSetoid theory free bound sort).iseqv.symm equivalent
    · intro left middle right first second
      exact (openEquationSetoid theory free bound sort).iseqv.trans first second

@[simp]
theorem compactObservationSetoid_r_iff {theory : IGSLT}
    (carrier : OpenElaborationCarrier theory)
    (free : WellSorted.FreeTypeContext) (bound : List TypeExpr)
    (sort : LangSort theory.presentation.presentation.language)
    (left right : carrier.Carrier free bound sort) :
    (carrier.compactObservationSetoid free bound sort).r left right ↔
      (openEquationSetoid theory free bound sort).r
        (carrier.erase left) (carrier.erase right) :=
  Iff.rfl

/-- Distinct elaborations of the same compact term are observationally equal
at the compact boundary.  A proof-relevant semantics may still distinguish
them. -/
theorem compactObservation_of_erase_eq {theory : IGSLT}
    (carrier : OpenElaborationCarrier theory)
    {free : WellSorted.FreeTypeContext} {bound : List TypeExpr}
    {sort : LangSort theory.presentation.presentation.language}
    {left right : carrier.Carrier free bound sort}
    (erases : carrier.erase left = carrier.erase right) :
    (carrier.compactObservationSetoid free bound sort).r left right := by
  rw [compactObservationSetoid_r_iff, erases]
  exact (openEquationSetoid theory free bound sort).iseqv.refl _

end OpenElaborationCarrier

/-! ## Carriers over an admitted reflective fibre -/

/-- A proof-relevant carrier above each quote-safe typed open fibre selected
by an admitted reflection profile.

Unlike `OpenElaborationCarrier`, erasure does not claim that every core-typed
term is reflectively admissible.  Both compilation and erasure stay inside the
certified fibre, so an elaborator whose algorithm inspects quotations need not
manufacture a quote-safety proof for arbitrary core syntax. -/
structure ReflectiveOpenElaborationCarrier (theory : IGSLT)
    (reflection : ReflectionExtension.AdmittedProfile
      theory.presentation.presentation.language) where
  Carrier : (free : WellSorted.FreeTypeContext) →
    (bound : List TypeExpr) →
    (sort : LangSort theory.presentation.presentation.language) → Type u
  erase : ∀ {free bound sort}, Carrier free bound sort →
    ReflectiveWellSorted.OpenTerm reflection.1
      theory.presentation.presentation.language free bound sort
  compile : ∀ {free bound sort},
    ReflectiveWellSorted.OpenTerm reflection.1
      theory.presentation.presentation.language free bound sort →
    Carrier free bound sort
  erase_compile : ∀ {free bound sort}
    (term : ReflectiveWellSorted.OpenTerm reflection.1
      theory.presentation.presentation.language free bound sort),
    erase (compile term) = term

namespace ReflectiveOpenElaborationCarrier

/-- Compilation into a proof-relevant reflective carrier is injective because
erasure is its left inverse. -/
theorem compile_injective {theory : IGSLT}
    {reflection : ReflectionExtension.AdmittedProfile
      theory.presentation.presentation.language}
    (carrier : ReflectiveOpenElaborationCarrier theory reflection)
    {free bound sort} :
    Function.Injective
      (carrier.compile : ReflectiveWellSorted.OpenTerm reflection.1
        theory.presentation.presentation.language free bound sort →
          carrier.Carrier free bound sort) := by
  intro left right equality
  have erased := congrArg carrier.erase equality
  simpa only [carrier.erase_compile] using erased

/-- Every reflection-certified compact term is the erasure of at least one
proof-relevant elaboration. -/
theorem erase_surjective {theory : IGSLT}
    {reflection : ReflectionExtension.AdmittedProfile
      theory.presentation.presentation.language}
    (carrier : ReflectiveOpenElaborationCarrier theory reflection)
    {free bound sort} :
    Function.Surjective
      (carrier.erase : carrier.Carrier free bound sort →
        ReflectiveWellSorted.OpenTerm reflection.1
          theory.presentation.presentation.language free bound sort) := by
  intro term
  exact ⟨carrier.compile term, carrier.erase_compile term⟩

/-- Pull the admitted reflective equation relation back along proof-relevant
erasure.  Every intermediate term in that relation remains in the same
quote-safe typed fibre. -/
def compactObservationSetoid {theory : IGSLT}
    {reflection : ReflectionExtension.AdmittedProfile
      theory.presentation.presentation.language}
    (carrier : ReflectiveOpenElaborationCarrier theory reflection)
    (free : WellSorted.FreeTypeContext) (bound : List TypeExpr)
    (sort : LangSort theory.presentation.presentation.language) :
    Setoid (carrier.Carrier free bound sort) where
  r left right :=
    (ReflectiveEquationSemantics.reflectiveOpenPatternEquationSetoid
      reflection.1 defaultBasePremises
        theory.presentation.presentation.language free bound
          (.base sort.1)).r (carrier.erase left) (carrier.erase right)
  iseqv := by
    constructor
    · intro term
      exact (ReflectiveEquationSemantics.reflectiveOpenPatternEquationSetoid
        reflection.1 defaultBasePremises
          theory.presentation.presentation.language free bound
            (.base sort.1)).iseqv.refl (carrier.erase term)
    · intro left right equivalent
      exact (ReflectiveEquationSemantics.reflectiveOpenPatternEquationSetoid
        reflection.1 defaultBasePremises
          theory.presentation.presentation.language free bound
            (.base sort.1)).iseqv.symm equivalent
    · intro left middle right first second
      exact (ReflectiveEquationSemantics.reflectiveOpenPatternEquationSetoid
        reflection.1 defaultBasePremises
          theory.presentation.presentation.language free bound
            (.base sort.1)).iseqv.trans first second

@[simp]
theorem compactObservationSetoid_r_iff {theory : IGSLT}
    {reflection : ReflectionExtension.AdmittedProfile
      theory.presentation.presentation.language}
    (carrier : ReflectiveOpenElaborationCarrier theory reflection)
    (free : WellSorted.FreeTypeContext) (bound : List TypeExpr)
    (sort : LangSort theory.presentation.presentation.language)
    (left right : carrier.Carrier free bound sort) :
    (carrier.compactObservationSetoid free bound sort).r left right ↔
      (ReflectiveEquationSemantics.reflectiveOpenPatternEquationSetoid
        reflection.1 defaultBasePremises
          theory.presentation.presentation.language free bound
            (.base sort.1)).r (carrier.erase left) (carrier.erase right) :=
  Iff.rfl

/-- Elaborations with equal reflective erasures are compactly
indistinguishable. -/
theorem compactObservation_of_erase_eq {theory : IGSLT}
    {reflection : ReflectionExtension.AdmittedProfile
      theory.presentation.presentation.language}
    (carrier : ReflectiveOpenElaborationCarrier theory reflection)
    {free : WellSorted.FreeTypeContext} {bound : List TypeExpr}
    {sort : LangSort theory.presentation.presentation.language}
    {left right : carrier.Carrier free bound sort}
    (erases : carrier.erase left = carrier.erase right) :
    (carrier.compactObservationSetoid free bound sort).r left right := by
  rw [compactObservationSetoid_r_iff, erases]
  exact (ReflectiveEquationSemantics.reflectiveOpenPatternEquationSetoid
    reflection.1 defaultBasePremises
      theory.presentation.presentation.language free bound
        (.base sort.1)).iseqv.refl _

end ReflectiveOpenElaborationCarrier

/-- A proof-relevant lift of authored equation generators.

This is the elementary transport datum behind the fibred picture: an edge in
an elaboration fiber is admissible only when it projects to one generator of
the sole authored `IGSLT`.  The lift may additionally preserve or transport
declaration identities, occurrences, resources, or provenance. -/
structure OpenElaborationGeneratorLift {theory : IGSLT}
    (carrier : OpenElaborationCarrier theory) where
  step : ∀ (free : WellSorted.FreeTypeContext) (bound : List TypeExpr)
    (sort : LangSort theory.presentation.presentation.language),
    carrier.Carrier free bound sort → carrier.Carrier free bound sort → Prop
  erasesToAuthoredGenerator : ∀ {free bound sort} {left right},
    step free bound sort left right →
      openEquationGenerator theory free bound sort
        (carrier.erase left) (carrier.erase right)

namespace OpenElaborationGeneratorLift

/-- The least equivalence generated by a proof-relevant lift of the authored
equation edges. -/
def setoid {theory : IGSLT} {carrier : OpenElaborationCarrier theory}
    (lift : OpenElaborationGeneratorLift carrier)
    (free : WellSorted.FreeTypeContext) (bound : List TypeExpr)
    (sort : LangSort theory.presentation.presentation.language) :
    Setoid (carrier.Carrier free bound sort) where
  r := Relation.EqvGen (lift.step free bound sort)
  iseqv :=
    { refl := Relation.EqvGen.refl
      symm := fun relation => Relation.EqvGen.symm _ _ relation
      trans := fun first second => Relation.EqvGen.trans _ _ _ first second }

/-- The generated elaborated relation is least among equivalence relations
containing every lifted edge. -/
theorem setoid_le {theory : IGSLT}
    {carrier : OpenElaborationCarrier theory}
    (lift : OpenElaborationGeneratorLift carrier)
    {free : WellSorted.FreeTypeContext} {bound : List TypeExpr}
    {sort : LangSort theory.presentation.presentation.language}
    (target : Setoid (carrier.Carrier free bound sort))
    (contains : ∀ {left right}, lift.step free bound sort left right →
      target.r left right)
    {left right : carrier.Carrier free bound sort}
    (equivalent : (lift.setoid free bound sort).r left right) :
    target.r left right := by
  induction equivalent with
  | rel left right generator => exact contains generator
  | refl term => exact target.iseqv.refl term
  | symm left right relation inductionHypothesis =>
      exact target.iseqv.symm inductionHypothesis
  | trans left middle right first second firstIH secondIH =>
      exact target.iseqv.trans firstIH secondIH

/-- Enlarging the admissible lifted-generator family enlarges the generated
elaborated equivalence. -/
theorem setoid_mono {theory : IGSLT}
    {carrier : OpenElaborationCarrier theory}
    {first second : OpenElaborationGeneratorLift carrier}
    {free : WellSorted.FreeTypeContext} {bound : List TypeExpr}
    {sort : LangSort theory.presentation.presentation.language}
    (includes : ∀ {left right}, first.step free bound sort left right →
      second.step free bound sort left right)
    {left right : carrier.Carrier free bound sort}
    (equivalent : (first.setoid free bound sort).r left right) :
    (second.setoid free bound sort).r left right :=
  first.setoid_le (second.setoid free bound sort)
    (fun generator => Relation.EqvGen.rel _ _ (includes generator)) equivalent

/-- A path of lifted generators projects to a path in the sole authored open
equation setoid. -/
theorem erasesToAuthored {theory : IGSLT}
    {carrier : OpenElaborationCarrier theory}
    (lift : OpenElaborationGeneratorLift carrier)
    {free : WellSorted.FreeTypeContext} {bound : List TypeExpr}
    {sort : LangSort theory.presentation.presentation.language}
    {left right : carrier.Carrier free bound sort}
    (equivalent : (lift.setoid free bound sort).r left right) :
    (openEquationSetoid theory free bound sort).r
      (carrier.erase left) (carrier.erase right) := by
  induction equivalent with
  | rel left right generator =>
      exact Relation.EqvGen.rel _ _
        (lift.erasesToAuthoredGenerator generator)
  | refl term => exact Relation.EqvGen.refl _
  | symm left right relation inductionHypothesis =>
      exact Relation.EqvGen.symm _ _ inductionHypothesis
  | trans left middle right first second firstIH secondIH =>
      exact Relation.EqvGen.trans _ _ _ firstIH secondIH

end OpenElaborationGeneratorLift

/-- A proof-relevant elementary relation whose erasure is an authored
equation path.

This is the appropriate lift when one structured step expands to several
authored generators after forgetting evidence.  For example, supported
substitution may turn one source occurrence into a contextual equation path
rather than one target generator.  The target path is still entirely inside
the sole authored `IGSLT`; only the granularity of elementary steps changes. -/
structure OpenElaborationPathLift {theory : IGSLT}
    (carrier : OpenElaborationCarrier theory) where
  step : ∀ (free : WellSorted.FreeTypeContext) (bound : List TypeExpr)
    (sort : LangSort theory.presentation.presentation.language),
    carrier.Carrier free bound sort → carrier.Carrier free bound sort → Prop
  erasesToAuthoredPath : ∀ {free bound sort} {left right},
    step free bound sort left right →
      (openEquationSetoid theory free bound sort).r
        (carrier.erase left) (carrier.erase right)

namespace OpenElaborationPathLift

/-- Every generator lift is a path lift by injecting its erased generator
into the authored least equivalence. -/
def ofGeneratorLift {theory : IGSLT}
    {carrier : OpenElaborationCarrier theory}
    (lift : OpenElaborationGeneratorLift carrier) :
    OpenElaborationPathLift carrier where
  step := lift.step
  erasesToAuthoredPath := fun generator =>
    Relation.EqvGen.rel _ _ (lift.erasesToAuthoredGenerator generator)

/-- Least equivalence generated by proof-relevant edges whose erasures are
authored paths. -/
def setoid {theory : IGSLT} {carrier : OpenElaborationCarrier theory}
    (lift : OpenElaborationPathLift carrier)
    (free : WellSorted.FreeTypeContext) (bound : List TypeExpr)
    (sort : LangSort theory.presentation.presentation.language) :
    Setoid (carrier.Carrier free bound sort) where
  r := Relation.EqvGen (lift.step free bound sort)
  iseqv :=
    { refl := Relation.EqvGen.refl
      symm := fun relation => Relation.EqvGen.symm _ _ relation
      trans := fun first second => Relation.EqvGen.trans _ _ _ first second }

/-- A path of proof-relevant edges erases to an authored equation path. -/
theorem erasesToAuthored {theory : IGSLT}
    {carrier : OpenElaborationCarrier theory}
    (lift : OpenElaborationPathLift carrier)
    {free : WellSorted.FreeTypeContext} {bound : List TypeExpr}
    {sort : LangSort theory.presentation.presentation.language}
    {left right : carrier.Carrier free bound sort}
    (equivalent : (lift.setoid free bound sort).r left right) :
    (openEquationSetoid theory free bound sort).r
      (carrier.erase left) (carrier.erase right) := by
  induction equivalent with
  | rel left right path => exact lift.erasesToAuthoredPath path
  | refl term => exact Relation.EqvGen.refl _
  | symm left right relation inductionHypothesis =>
      exact Relation.EqvGen.symm _ _ inductionHypothesis
  | trans left middle right first second firstIH secondIH =>
      exact Relation.EqvGen.trans _ _ _ firstIH secondIH

end OpenElaborationPathLift

/-- A semantic equation family on a proof-relevant carrier, together with
its required support-erasure map into the sole authored equation relation.

The relation may be strictly finer than compact observation.  In particular,
it may retain declaration, occurrence, colour, or causal identity that raw
syntax forgets. -/
structure OpenElaborationSemantics {theory : IGSLT}
    (carrier : OpenElaborationCarrier theory) where
  relation : ∀ (free : WellSorted.FreeTypeContext) (bound : List TypeExpr)
    (sort : LangSort theory.presentation.presentation.language),
    Setoid (carrier.Carrier free bound sort)
  erasesToAuthored : ∀ {free bound sort} {left right},
    (relation free bound sort).r left right →
      (openEquationSetoid theory free bound sort).r
        (carrier.erase left) (carrier.erase right)

namespace OpenElaborationSemantics

/-- A path lift supplies an authored-only elaborated semantic relation even
when one proof-relevant edge expands to several compact authored generators. -/
def ofPathLift {theory : IGSLT}
    {carrier : OpenElaborationCarrier theory}
    (lift : OpenElaborationPathLift carrier) :
    OpenElaborationSemantics carrier where
  relation := lift.setoid
  erasesToAuthored := lift.erasesToAuthored

/-- A lifted generator family supplies an authored-only elaborated semantic
relation. -/
def ofGeneratorLift {theory : IGSLT}
    {carrier : OpenElaborationCarrier theory}
    (lift : OpenElaborationGeneratorLift carrier) :
    OpenElaborationSemantics carrier where
  relation := lift.setoid
  erasesToAuthored := lift.erasesToAuthored

/-- A proof-relevant identity retained above compact syntax.

The identity is fiber-indexed: it may record declaration, occurrence, colour,
collection-choice, boundary, or provenance data, but it cannot silently move a
term to another authored typing fiber. -/
structure Identity {theory : IGSLT}
    (carrier : OpenElaborationCarrier theory) where
  Key : (free : WellSorted.FreeTypeContext) →
    (bound : List TypeExpr) →
    (sort : LangSort theory.presentation.presentation.language) → Type u
  key : ∀ {free bound sort}, carrier.Carrier free bound sort →
    Key free bound sort

namespace Identity

/-- One authored equation edge that preserves the proof-relevant identity.

The authored `openEquationGenerator` is the only source of semantic edges;
key equality merely rejects edges that would conflate distinct elaborations. -/
def preservingGenerator {theory : IGSLT}
    {carrier : OpenElaborationCarrier theory}
    (identity : Identity carrier)
    (free : WellSorted.FreeTypeContext) (bound : List TypeExpr)
    (sort : LangSort theory.presentation.presentation.language)
    (left right : carrier.Carrier free bound sort) : Prop :=
  identity.key left = identity.key right ∧
    openEquationGenerator theory free bound sort
      (carrier.erase left) (carrier.erase right)

/-- Least equivalence generated by authored edges that retain elaboration
identity.  It is generally finer than equality after compact erasure. -/
def preservingSetoid {theory : IGSLT}
    {carrier : OpenElaborationCarrier theory}
    (identity : Identity carrier)
    (free : WellSorted.FreeTypeContext) (bound : List TypeExpr)
    (sort : LangSort theory.presentation.presentation.language) :
    Setoid (carrier.Carrier free bound sort) where
  r := Relation.EqvGen (identity.preservingGenerator free bound sort)
  iseqv :=
    { refl := Relation.EqvGen.refl
      symm := fun relation => Relation.EqvGen.symm _ _ relation
      trans := fun first second => Relation.EqvGen.trans _ _ _ first second }

/-- Identity preservation is a special case of a proof-relevant generator
lift. -/
def generatorLift {theory : IGSLT}
    {carrier : OpenElaborationCarrier theory}
    (identity : Identity carrier) :
    OpenElaborationGeneratorLift carrier where
  step := identity.preservingGenerator
  erasesToAuthoredGenerator := fun generator => generator.2

/-- The special-case construction agrees definitionally with the generic
lifted-generator setoid. -/
theorem preservingSetoid_eq_generatorLift_setoid {theory : IGSLT}
    {carrier : OpenElaborationCarrier theory}
    (identity : Identity carrier)
    (free : WellSorted.FreeTypeContext) (bound : List TypeExpr)
    (sort : LangSort theory.presentation.presentation.language) :
    identity.preservingSetoid free bound sort =
      identity.generatorLift.setoid free bound sort :=
  rfl

/-- Every identity-preserving semantic path retains the same proof-relevant
key. -/
theorem key_eq_of_preserving {theory : IGSLT}
    {carrier : OpenElaborationCarrier theory}
    (identity : Identity carrier)
    {free : WellSorted.FreeTypeContext} {bound : List TypeExpr}
    {sort : LangSort theory.presentation.presentation.language}
    {left right : carrier.Carrier free bound sort}
    (equivalent : (identity.preservingSetoid free bound sort).r left right) :
    identity.key left = identity.key right := by
  induction equivalent with
  | rel left right generator => exact generator.1
  | refl term => rfl
  | symm left right relation inductionHypothesis =>
      exact inductionHypothesis.symm
  | trans left middle right first second firstIH secondIH =>
      exact firstIH.trans secondIH

/-- Unequal proof-relevant identities cannot be connected by the
identity-preserving elaborated semantics. -/
theorem not_preserving_of_key_ne {theory : IGSLT}
    {carrier : OpenElaborationCarrier theory}
    (identity : Identity carrier)
    {free : WellSorted.FreeTypeContext} {bound : List TypeExpr}
    {sort : LangSort theory.presentation.presentation.language}
    {left right : carrier.Carrier free bound sort}
    (different : identity.key left ≠ identity.key right) :
    ¬ (identity.preservingSetoid free bound sort).r left right := by
  intro equivalent
  exact different (identity.key_eq_of_preserving equivalent)

/-- Erasing an identity-preserving path yields a path generated solely by the
authored equations of the underlying `IGSLT`. -/
theorem erasesToAuthored {theory : IGSLT}
    {carrier : OpenElaborationCarrier theory}
    (identity : Identity carrier)
    {free : WellSorted.FreeTypeContext} {bound : List TypeExpr}
    {sort : LangSort theory.presentation.presentation.language}
    {left right : carrier.Carrier free bound sort}
    (equivalent : (identity.preservingSetoid free bound sort).r left right) :
    (openEquationSetoid theory free bound sort).r
      (carrier.erase left) (carrier.erase right) := by
  induction equivalent with
  | rel left right generator =>
      exact Relation.EqvGen.rel _ _ generator.2
  | refl term => exact Relation.EqvGen.refl _
  | symm left right relation inductionHypothesis =>
      exact Relation.EqvGen.symm _ _ inductionHypothesis
  | trans left middle right first second firstIH secondIH =>
      exact Relation.EqvGen.trans _ _ _ firstIH secondIH

/-- Package one proof-relevant identity as a semantic relation over the
elaborated carrier. -/
def semantics {theory : IGSLT}
    {carrier : OpenElaborationCarrier theory}
    (identity : Identity carrier) : OpenElaborationSemantics carrier :=
  OpenElaborationSemantics.ofGeneratorLift identity.generatorLift

/-- Identity-preserving semantics is contained in compact observation. -/
theorem preserving_implies_compactObservation {theory : IGSLT}
    {carrier : OpenElaborationCarrier theory}
    (identity : Identity carrier)
    {free : WellSorted.FreeTypeContext} {bound : List TypeExpr}
    {sort : LangSort theory.presentation.presentation.language}
    {left right : carrier.Carrier free bound sort}
    (equivalent : (identity.semantics.relation free bound sort).r left right) :
    (carrier.compactObservationSetoid free bound sort).r left right :=
  identity.erasesToAuthored equivalent

/-- A same-erasure/different-key pair is a concrete witness that compact
observation is strictly coarser at that fiber. -/
theorem compact_but_not_preserving {theory : IGSLT}
    {carrier : OpenElaborationCarrier theory}
    (identity : Identity carrier)
    {free : WellSorted.FreeTypeContext} {bound : List TypeExpr}
    {sort : LangSort theory.presentation.presentation.language}
    {left right : carrier.Carrier free bound sort}
    (sameErasure : carrier.erase left = carrier.erase right)
    (differentIdentity : identity.key left ≠ identity.key right) :
    (carrier.compactObservationSetoid free bound sort).r left right ∧
      ¬ (identity.semantics.relation free bound sort).r left right :=
  ⟨carrier.compactObservation_of_erase_eq sameErasure,
    identity.not_preserving_of_key_ne differentIdentity⟩

end Identity

/-- Pulling back authored equality is the coarsest observation semantics.
It is useful at compact interfaces but deliberately does not claim to be the
proof-relevant semantic relation of a particular elaboration. -/
def compactObservation {theory : IGSLT}
    (carrier : OpenElaborationCarrier theory) :
    OpenElaborationSemantics carrier where
  relation := carrier.compactObservationSetoid
  erasesToAuthored := fun equivalent => equivalent

/-- An exact computable section on a proof-relevant semantic carrier. -/
structure ComputableSection {theory : IGSLT}
    {carrier : OpenElaborationCarrier theory}
    (semantics : OpenElaborationSemantics carrier) where
  canonical : ∀ (free : WellSorted.FreeTypeContext) (bound : List TypeExpr)
    (sort : LangSort theory.presentation.presentation.language),
    ComputableSetoidSection (carrier.Carrier free bound sort)
      (semantics.relation free bound sort)

namespace ComputableSection

/-- Construct an exact elaborated section from invariance on each
proof-relevant edge of a path lift.

The proof is the same least-equivalence induction as for a generator lift;
the distinction is solely that support erasure of one edge may already be an
authored path. -/
def ofPathInvariant {theory : IGSLT}
    {carrier : OpenElaborationCarrier theory}
    (lift : OpenElaborationPathLift carrier)
    (normalize : ∀ {free bound sort},
      carrier.Carrier free bound sort → carrier.Carrier free bound sort)
    (equivalent : ∀ {free bound sort}
      (term : carrier.Carrier free bound sort),
      (lift.setoid free bound sort).r (normalize term) term)
    (pathInvariant : ∀ {free bound sort}
      {left right : carrier.Carrier free bound sort},
      lift.step free bound sort left right →
        normalize left = normalize right) :
    ComputableSection (OpenElaborationSemantics.ofPathLift lift) where
  canonical := fun free bound sort =>
    { normalize := normalize
      equivalent := equivalent
      complete := by
        intro left right relation
        induction relation with
        | rel left right path => exact pathInvariant path
        | refl term => rfl
        | symm left right relation inductionHypothesis =>
            exact inductionHypothesis.symm
        | trans left middle right first second firstIH secondIH =>
            exact firstIH.trans secondIH }

/-- Construct an exact elaborated section from a normalization path for each
term and exact invariance on every lifted authored generator.

The least-equivalence induction is generic.  A concrete elaboration therefore
has only two local proof obligations: its normal form remains related to the
input, and one admissible proof-relevant edge receives equal normal forms. -/
def ofGeneratorInvariant {theory : IGSLT}
    {carrier : OpenElaborationCarrier theory}
    (lift : OpenElaborationGeneratorLift carrier)
    (normalize : ∀ {free bound sort},
      carrier.Carrier free bound sort → carrier.Carrier free bound sort)
    (equivalent : ∀ {free bound sort}
      (term : carrier.Carrier free bound sort),
      (lift.setoid free bound sort).r (normalize term) term)
    (generatorInvariant : ∀ {free bound sort}
      {left right : carrier.Carrier free bound sort},
      lift.step free bound sort left right →
        normalize left = normalize right) :
    ComputableSection (OpenElaborationSemantics.ofGeneratorLift lift) where
  canonical := fun free bound sort =>
    { normalize := normalize
      equivalent := equivalent
      complete := by
        intro left right relation
        induction relation with
        | rel left right generator =>
            exact generatorInvariant generator
        | refl term => rfl
        | symm left right relation inductionHypothesis =>
            exact inductionHypothesis.symm
        | trans left middle right first second firstIH secondIH =>
            exact firstIH.trans secondIH }

/-- Semantic normalization erases to an authored equation path. -/
theorem normalize_erases_equivalent {theory : IGSLT}
    {carrier : OpenElaborationCarrier theory}
    {semantics : OpenElaborationSemantics carrier}
    (canonical : ComputableSection semantics)
    {free bound sort} (term : carrier.Carrier free bound sort) :
    (openEquationSetoid theory free bound sort).r
      (carrier.erase ((canonical.canonical free bound sort).normalize term))
      (carrier.erase term) :=
  semantics.erasesToAuthored
    ((canonical.canonical free bound sort).equivalent term)

/-- Elaborated semantic equivalence is exactly equality of the selected
proof-relevant representatives. -/
theorem equivalent_iff_normalize_eq {theory : IGSLT}
    {carrier : OpenElaborationCarrier theory}
    {semantics : OpenElaborationSemantics carrier}
    (canonical : ComputableSection semantics)
    {free bound sort} (left right : carrier.Carrier free bound sort) :
    (semantics.relation free bound sort).r left right ↔
      (canonical.canonical free bound sort).normalize left =
        (canonical.canonical free bound sort).normalize right :=
  (canonical.canonical free bound sort).equivalent_iff_normalize_eq left right

end ComputableSection

end OpenElaborationSemantics

/-- An exact open semantic theory carried above one authored `IGSLT`.

The underlying interactive presentation remains the sole syntax and rule
authority.  The carrier may retain proof-relevant data, its semantic relation
must erase to the authored equation relation, and its section chooses exact
representatives upstairs.  This is an object bundle only; categorical
transport is introduced only after carrier reindexing has been proved. -/
structure ElaboratedOpenTheory where
  theory : IGSLT
  carrier : OpenElaborationCarrier theory
  semantics : OpenElaborationSemantics carrier
  canonical : OpenElaborationSemantics.ComputableSection semantics

namespace ElaboratedOpenTheory

/-- Normalization in an elaborated theory always erases to an authored
equation path in its unique underlying presentation. -/
theorem normalize_erases_equivalent (elaborated : ElaboratedOpenTheory)
    {free : WellSorted.FreeTypeContext} {bound : List TypeExpr}
    {sort : LangSort elaborated.theory.presentation.presentation.language}
    (term : elaborated.carrier.Carrier free bound sort) :
    (openEquationSetoid elaborated.theory free bound sort).r
      (elaborated.carrier.erase
        ((elaborated.canonical.canonical free bound sort).normalize term))
      (elaborated.carrier.erase term) :=
  elaborated.canonical.normalize_erases_equivalent term

end ElaboratedOpenTheory

/-! ## Proof-relevant semantics over an admitted reflective fibre

The corresponding core-only structures above remain useful when ordinary
typing is the whole admission boundary.  These structures retain the same
split-epimorphic architecture while making quote safety part of the carrier
and using the admitted reflective equation relation as the erasure target. -/

/-- A proof-relevant elementary relation whose erasure is a path in one
admitted reflective equation theory. -/
structure ReflectiveOpenElaborationPathLift {theory : IGSLT}
    {reflection : ReflectionExtension.AdmittedProfile
      theory.presentation.presentation.language}
    (carrier : ReflectiveOpenElaborationCarrier theory reflection) where
  step : ∀ (free : WellSorted.FreeTypeContext) (bound : List TypeExpr)
    (sort : LangSort theory.presentation.presentation.language),
    carrier.Carrier free bound sort → carrier.Carrier free bound sort → Prop
  erasesToReflectivePath : ∀ {free bound sort} {left right},
    step free bound sort left right →
      (ReflectiveEquationSemantics.reflectiveOpenPatternEquationSetoid
        reflection.1 defaultBasePremises
          theory.presentation.presentation.language free bound
            (.base sort.1)).r (carrier.erase left) (carrier.erase right)

namespace ReflectiveOpenElaborationPathLift

/-- Least equivalence generated by proof-relevant reflective edges. -/
def setoid {theory : IGSLT}
    {reflection : ReflectionExtension.AdmittedProfile
      theory.presentation.presentation.language}
    {carrier : ReflectiveOpenElaborationCarrier theory reflection}
    (lift : ReflectiveOpenElaborationPathLift carrier)
    (free : WellSorted.FreeTypeContext) (bound : List TypeExpr)
    (sort : LangSort theory.presentation.presentation.language) :
    Setoid (carrier.Carrier free bound sort) where
  r := Relation.EqvGen (lift.step free bound sort)
  iseqv :=
    { refl := Relation.EqvGen.refl
      symm := fun relation => Relation.EqvGen.symm _ _ relation
      trans := fun first second => Relation.EqvGen.trans _ _ _ first second }

/-- A path of proof-relevant edges erases to a path in the admitted
reflective equation theory. -/
theorem erasesToReflective {theory : IGSLT}
    {reflection : ReflectionExtension.AdmittedProfile
      theory.presentation.presentation.language}
    {carrier : ReflectiveOpenElaborationCarrier theory reflection}
    (lift : ReflectiveOpenElaborationPathLift carrier)
    {free : WellSorted.FreeTypeContext} {bound : List TypeExpr}
    {sort : LangSort theory.presentation.presentation.language}
    {left right : carrier.Carrier free bound sort}
    (equivalent : (lift.setoid free bound sort).r left right) :
    (ReflectiveEquationSemantics.reflectiveOpenPatternEquationSetoid
      reflection.1 defaultBasePremises
        theory.presentation.presentation.language free bound
          (.base sort.1)).r (carrier.erase left) (carrier.erase right) := by
  induction equivalent with
  | rel left right path => exact lift.erasesToReflectivePath path
  | refl term => exact Relation.EqvGen.refl _
  | symm left right relation inductionHypothesis =>
      exact Relation.EqvGen.symm _ _ inductionHypothesis
  | trans left middle right first second firstIH secondIH =>
      exact Relation.EqvGen.trans _ _ _ firstIH secondIH

end ReflectiveOpenElaborationPathLift

/-- A semantic equation family on a proof-relevant reflective carrier,
together with its erasure into the admitted reflective equation theory. -/
structure ReflectiveOpenElaborationSemantics {theory : IGSLT}
    {reflection : ReflectionExtension.AdmittedProfile
      theory.presentation.presentation.language}
    (carrier : ReflectiveOpenElaborationCarrier theory reflection) where
  relation : ∀ (free : WellSorted.FreeTypeContext) (bound : List TypeExpr)
    (sort : LangSort theory.presentation.presentation.language),
    Setoid (carrier.Carrier free bound sort)
  erasesToReflective : ∀ {free bound sort} {left right},
    (relation free bound sort).r left right →
      (ReflectiveEquationSemantics.reflectiveOpenPatternEquationSetoid
        reflection.1 defaultBasePremises
          theory.presentation.presentation.language free bound
            (.base sort.1)).r (carrier.erase left) (carrier.erase right)

namespace ReflectiveOpenElaborationSemantics

/-- A reflective path lift supplies its generated semantic relation. -/
def ofPathLift {theory : IGSLT}
    {reflection : ReflectionExtension.AdmittedProfile
      theory.presentation.presentation.language}
    {carrier : ReflectiveOpenElaborationCarrier theory reflection}
    (lift : ReflectiveOpenElaborationPathLift carrier) :
    ReflectiveOpenElaborationSemantics carrier where
  relation := lift.setoid
  erasesToReflective := lift.erasesToReflective

/-- A proof-relevant identity retained above reflection-certified compact
syntax. -/
structure Identity {theory : IGSLT}
    {reflection : ReflectionExtension.AdmittedProfile
      theory.presentation.presentation.language}
    (carrier : ReflectiveOpenElaborationCarrier theory reflection) where
  Key : (free : WellSorted.FreeTypeContext) →
    (bound : List TypeExpr) →
    (sort : LangSort theory.presentation.presentation.language) → Type u
  key : ∀ {free bound sort}, carrier.Carrier free bound sort →
    Key free bound sort

namespace Identity

/-- One admitted reflective equation edge that preserves a proof-relevant
identity. -/
def preservingGenerator {theory : IGSLT}
    {reflection : ReflectionExtension.AdmittedProfile
      theory.presentation.presentation.language}
    {carrier : ReflectiveOpenElaborationCarrier theory reflection}
    (identity : Identity carrier)
    (free : WellSorted.FreeTypeContext) (bound : List TypeExpr)
    (sort : LangSort theory.presentation.presentation.language)
    (left right : carrier.Carrier free bound sort) : Prop :=
  identity.key left = identity.key right ∧
    ReflectiveEquationSemantics.reflectiveOpenPatternEquationGenerator
      reflection.1 defaultBasePremises
        theory.presentation.presentation.language free bound
          (.base sort.1) (carrier.erase left) (carrier.erase right)

/-- Least equivalence generated by identity-preserving reflective edges. -/
def preservingSetoid {theory : IGSLT}
    {reflection : ReflectionExtension.AdmittedProfile
      theory.presentation.presentation.language}
    {carrier : ReflectiveOpenElaborationCarrier theory reflection}
    (identity : Identity carrier)
    (free : WellSorted.FreeTypeContext) (bound : List TypeExpr)
    (sort : LangSort theory.presentation.presentation.language) :
    Setoid (carrier.Carrier free bound sort) where
  r := Relation.EqvGen (identity.preservingGenerator free bound sort)
  iseqv :=
    { refl := Relation.EqvGen.refl
      symm := fun relation => Relation.EqvGen.symm _ _ relation
      trans := fun first second => Relation.EqvGen.trans _ _ _ first second }

/-- Every identity-preserving path retains its proof-relevant key. -/
theorem key_eq_of_preserving {theory : IGSLT}
    {reflection : ReflectionExtension.AdmittedProfile
      theory.presentation.presentation.language}
    {carrier : ReflectiveOpenElaborationCarrier theory reflection}
    (identity : Identity carrier)
    {free : WellSorted.FreeTypeContext} {bound : List TypeExpr}
    {sort : LangSort theory.presentation.presentation.language}
    {left right : carrier.Carrier free bound sort}
    (equivalent : (identity.preservingSetoid free bound sort).r left right) :
    identity.key left = identity.key right := by
  induction equivalent with
  | rel left right generator => exact generator.1
  | refl term => rfl
  | symm left right relation inductionHypothesis =>
      exact inductionHypothesis.symm
  | trans left middle right first second firstIH secondIH =>
      exact firstIH.trans secondIH

/-- Unequal retained keys cannot be related by identity-preserving
semantics. -/
theorem not_preserving_of_key_ne {theory : IGSLT}
    {reflection : ReflectionExtension.AdmittedProfile
      theory.presentation.presentation.language}
    {carrier : ReflectiveOpenElaborationCarrier theory reflection}
    (identity : Identity carrier)
    {free : WellSorted.FreeTypeContext} {bound : List TypeExpr}
    {sort : LangSort theory.presentation.presentation.language}
    {left right : carrier.Carrier free bound sort}
    (different : identity.key left ≠ identity.key right) :
    ¬ (identity.preservingSetoid free bound sort).r left right := by
  intro equivalent
  exact different (identity.key_eq_of_preserving equivalent)

/-- Identity-preserving paths erase to admitted reflective equation paths. -/
theorem erasesToReflective {theory : IGSLT}
    {reflection : ReflectionExtension.AdmittedProfile
      theory.presentation.presentation.language}
    {carrier : ReflectiveOpenElaborationCarrier theory reflection}
    (identity : Identity carrier)
    {free : WellSorted.FreeTypeContext} {bound : List TypeExpr}
    {sort : LangSort theory.presentation.presentation.language}
    {left right : carrier.Carrier free bound sort}
    (equivalent : (identity.preservingSetoid free bound sort).r left right) :
    (ReflectiveEquationSemantics.reflectiveOpenPatternEquationSetoid
      reflection.1 defaultBasePremises
        theory.presentation.presentation.language free bound
          (.base sort.1)).r (carrier.erase left) (carrier.erase right) := by
  induction equivalent with
  | rel left right generator =>
      exact Relation.EqvGen.rel _ _ generator.2
  | refl term => exact Relation.EqvGen.refl _
  | symm left right relation inductionHypothesis =>
      exact Relation.EqvGen.symm _ _ inductionHypothesis
  | trans left middle right first second firstIH secondIH =>
      exact Relation.EqvGen.trans _ _ _ firstIH secondIH

/-- Package one retained identity as reflective elaboration semantics. -/
def semantics {theory : IGSLT}
    {reflection : ReflectionExtension.AdmittedProfile
      theory.presentation.presentation.language}
    {carrier : ReflectiveOpenElaborationCarrier theory reflection}
    (identity : Identity carrier) :
    ReflectiveOpenElaborationSemantics carrier where
  relation := identity.preservingSetoid
  erasesToReflective := identity.erasesToReflective

/-- A same-erasure/different-key pair is compactly equal but semantically
distinct. -/
theorem compact_but_not_preserving {theory : IGSLT}
    {reflection : ReflectionExtension.AdmittedProfile
      theory.presentation.presentation.language}
    {carrier : ReflectiveOpenElaborationCarrier theory reflection}
    (identity : Identity carrier)
    {free : WellSorted.FreeTypeContext} {bound : List TypeExpr}
    {sort : LangSort theory.presentation.presentation.language}
    {left right : carrier.Carrier free bound sort}
    (sameErasure : carrier.erase left = carrier.erase right)
    (differentIdentity : identity.key left ≠ identity.key right) :
    (carrier.compactObservationSetoid free bound sort).r left right ∧
      ¬ (identity.semantics.relation free bound sort).r left right :=
  ⟨carrier.compactObservation_of_erase_eq sameErasure,
    identity.not_preserving_of_key_ne differentIdentity⟩

end Identity

/-- Pulling back admitted reflective equivalence is the coarsest compact
observation semantics on the proof-relevant carrier. -/
def compactObservation {theory : IGSLT}
    {reflection : ReflectionExtension.AdmittedProfile
      theory.presentation.presentation.language}
    (carrier : ReflectiveOpenElaborationCarrier theory reflection) :
    ReflectiveOpenElaborationSemantics carrier where
  relation := carrier.compactObservationSetoid
  erasesToReflective := fun equivalent => equivalent

/-- An exact computable section on a proof-relevant reflective semantic
carrier. -/
structure ComputableSection {theory : IGSLT}
    {reflection : ReflectionExtension.AdmittedProfile
      theory.presentation.presentation.language}
    {carrier : ReflectiveOpenElaborationCarrier theory reflection}
    (semantics : ReflectiveOpenElaborationSemantics carrier) where
  canonical : ∀ (free : WellSorted.FreeTypeContext) (bound : List TypeExpr)
    (sort : LangSort theory.presentation.presentation.language),
    ComputableSetoidSection (carrier.Carrier free bound sort)
      (semantics.relation free bound sort)

namespace ComputableSection

/-- Construct an exact section from invariance on each proof-relevant path
generator. -/
def ofPathInvariant {theory : IGSLT}
    {reflection : ReflectionExtension.AdmittedProfile
      theory.presentation.presentation.language}
    {carrier : ReflectiveOpenElaborationCarrier theory reflection}
    (lift : ReflectiveOpenElaborationPathLift carrier)
    (normalize : ∀ {free bound sort},
      carrier.Carrier free bound sort → carrier.Carrier free bound sort)
    (equivalent : ∀ {free bound sort}
      (term : carrier.Carrier free bound sort),
      (lift.setoid free bound sort).r (normalize term) term)
    (pathInvariant : ∀ {free bound sort}
      {left right : carrier.Carrier free bound sort},
      lift.step free bound sort left right → normalize left = normalize right) :
    ComputableSection (ReflectiveOpenElaborationSemantics.ofPathLift lift) where
  canonical := fun free bound sort =>
    { normalize := normalize
      equivalent := equivalent
      complete := by
        intro left right relation
        induction relation with
        | rel left right path => exact pathInvariant path
        | refl term => rfl
        | symm left right relation inductionHypothesis =>
            exact inductionHypothesis.symm
        | trans left middle right first second firstIH secondIH =>
            exact firstIH.trans secondIH }

/-- Semantic normalization erases to an admitted reflective equation path. -/
theorem normalize_erases_equivalent {theory : IGSLT}
    {reflection : ReflectionExtension.AdmittedProfile
      theory.presentation.presentation.language}
    {carrier : ReflectiveOpenElaborationCarrier theory reflection}
    {semantics : ReflectiveOpenElaborationSemantics carrier}
    (canonical : ComputableSection semantics)
    {free bound sort} (term : carrier.Carrier free bound sort) :
    (ReflectiveEquationSemantics.reflectiveOpenPatternEquationSetoid
      reflection.1 defaultBasePremises
        theory.presentation.presentation.language free bound
          (.base sort.1)).r
      (carrier.erase ((canonical.canonical free bound sort).normalize term))
      (carrier.erase term) :=
  semantics.erasesToReflective
    ((canonical.canonical free bound sort).equivalent term)

/-- Reflective elaborated equivalence is equality of the selected
proof-relevant representatives. -/
theorem equivalent_iff_normalize_eq {theory : IGSLT}
    {reflection : ReflectionExtension.AdmittedProfile
      theory.presentation.presentation.language}
    {carrier : ReflectiveOpenElaborationCarrier theory reflection}
    {semantics : ReflectiveOpenElaborationSemantics carrier}
    (canonical : ComputableSection semantics)
    {free bound sort} (left right : carrier.Carrier free bound sort) :
    (semantics.relation free bound sort).r left right ↔
      (canonical.canonical free bound sort).normalize left =
        (canonical.canonical free bound sort).normalize right :=
  (canonical.canonical free bound sort).equivalent_iff_normalize_eq left right

end ComputableSection

end ReflectiveOpenElaborationSemantics

/-- An exact open semantic theory carried above one admitted reflective
extension of an authored `IGSLT`. -/
structure ReflectiveElaboratedOpenTheory where
  theory : IGSLT
  reflection : ReflectionExtension.AdmittedProfile
    theory.presentation.presentation.language
  carrier : ReflectiveOpenElaborationCarrier theory reflection
  semantics : ReflectiveOpenElaborationSemantics carrier
  canonical : ReflectiveOpenElaborationSemantics.ComputableSection semantics

namespace ReflectiveElaboratedOpenTheory

/-- Normalization in a reflective elaborated theory erases to its admitted
reflective equation relation. -/
theorem normalize_erases_equivalent
    (elaborated : ReflectiveElaboratedOpenTheory)
    {free : WellSorted.FreeTypeContext} {bound : List TypeExpr}
    {sort : LangSort elaborated.theory.presentation.presentation.language}
    (term : elaborated.carrier.Carrier free bound sort) :
    (ReflectiveEquationSemantics.reflectiveOpenPatternEquationSetoid
      elaborated.reflection.1 defaultBasePremises
        elaborated.theory.presentation.presentation.language free bound
          (.base sort.1)).r
      (elaborated.carrier.erase
        ((elaborated.canonical.canonical free bound sort).normalize term))
      (elaborated.carrier.erase term) :=
  elaborated.canonical.normalize_erases_equivalent term

end ReflectiveElaboratedOpenTheory

end Mettapedia.GSLT.LanguageDef
