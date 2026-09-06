import Mettapedia.OSLF.Framework.GSLTTypeSynthesis

/-!
# Equation-respecting proof-relevant path modalities

Finite execution is a change of operational granularity, not a second OSLF
algorithm. A semantic path retains an actual `GSLT.RewritePath` together with
equation witnesses at both endpoints. In particular, a zero-step semantic
path relates every two representatives of one equation class.

The path and graded-path theories are ordinary GSLTs with the original
equation setoid. Their modal type systems are obtained exclusively by the
canonical `gsltOSLF` construction, so every admitted predicate is invariant
under equations.
-/

namespace Mettapedia.OSLF.Framework.PathTypeSynthesis

open Mettapedia.GSLT
open Mettapedia.OSLF.Framework
open Mettapedia.OSLF.Framework.GSLTTypeSynthesis
open Mettapedia.OSLF.Framework.DerivedModalities

/-! ## Proof-relevant semantic paths -/

/-- A retained finite execution modulo the equation theory at both endpoints. -/
structure SemanticPath (theory : GSLT)
    (source target : theory.Term) where
  startRepresentative : theory.Term
  endRepresentative : theory.Term
  sourceEquation : theory.Equiv source startRepresentative
  path : theory.RewritePath startRepresentative endRepresentative
  targetEquation : theory.Equiv endRepresentative target

namespace SemanticPath

/-- Every concrete rewrite path embeds with reflexive endpoint equations. -/
def ofRewritePath {theory : GSLT} {source target : theory.Term}
    (path : theory.RewritePath source target) :
    SemanticPath theory source target where
  startRepresentative := source
  endRepresentative := target
  sourceEquation := theory.equations.iseqv.refl source
  path := path
  targetEquation := theory.equations.iseqv.refl target

/-- Static equivalence is the zero-step part of semantic path reachability. -/
def ofEquiv {theory : GSLT} {source target : theory.Term}
    (equivalent : theory.Equiv source target) :
    SemanticPath theory source target where
  startRepresentative := source
  endRepresentative := source
  sourceEquation := theory.equations.iseqv.refl source
  path := .nil source
  targetEquation := equivalent

/-- When the equation theory is equality, a semantic path contains an
ordinary rewrite path with the displayed endpoints. -/
def toRewritePathOfEquivIffEq
    {theory : GSLT} {source target : theory.Term}
    (equivIffEq : ∀ left right, theory.Equiv left right ↔ left = right)
    (semanticPath : SemanticPath theory source target) :
    theory.RewritePath source target := by
  cases semanticPath with
  | mk startRepresentative endRepresentative sourceEquation path
      targetEquation =>
      have sourceEq : source = startRepresentative :=
        (equivIffEq _ _).mp sourceEquation
      have targetEq : endRepresentative = target :=
        (equivIffEq _ _).mp targetEquation
      subst startRepresentative
      subst target
      exact path

end SemanticPath

/-- A proof-relevant semantic path packaged as an unindexed span edge. -/
structure PathEdge (theory : GSLT) where
  source : theory.Term
  target : theory.Term
  evidence : SemanticPath theory source target

/-- A retained semantic path of exactly `steps` authored rewrites. Endpoint
equations do not contribute rewrite length. -/
structure GradedSemanticPath (theory : GSLT) (steps : Nat)
    (source target : theory.Term) extends SemanticPath theory source target where
  length_eq : toSemanticPath.path.length = steps

namespace GradedSemanticPath

/-- A concrete rewrite path of the declared length embeds in the corresponding
semantic path layer. Endpoint equations are reflexive, so the retained work is
exactly the work performed by the concrete path. -/
def ofRewritePath {theory : GSLT} {steps : Nat}
    {source target : theory.Term} (path : theory.RewritePath source target)
    (length_eq : path.length = steps) :
    GradedSemanticPath theory steps source target where
  toSemanticPath := SemanticPath.ofRewritePath path
  length_eq := length_eq

end GradedSemanticPath

/-- An exact-length semantic path packaged as an unindexed span edge. -/
structure GradedPathEdge (theory : GSLT) (steps : Nat) where
  source : theory.Term
  target : theory.Term
  evidence : GradedSemanticPath theory steps source target

/-- The proof-relevant span of all finite semantic rewrite paths. -/
def pathSpan (theory : GSLT) : ReductionSpan theory.Term where
  Edge := PathEdge theory
  source := PathEdge.source
  target := PathEdge.target

/-- The proof-relevant span of semantic paths with one fixed rewrite length. -/
def gradedPathSpan (theory : GSLT) (steps : Nat) :
    ReductionSpan theory.Term where
  Edge := GradedPathEdge theory steps
  source := GradedPathEdge.source
  target := GradedPathEdge.target

/-! ## Path GSLTs -/

/-- Changing the source representative preserves a semantic path without
discarding its concrete rewrite receipt. -/
def SemanticPath.changeSource
    {theory : GSLT} {source source' target : theory.Term}
    (equivalent : theory.Equiv source source')
    (semanticPath : SemanticPath theory source target) :
    SemanticPath theory source' target where
  startRepresentative := semanticPath.startRepresentative
  endRepresentative := semanticPath.endRepresentative
  sourceEquation := theory.equations.iseqv.trans
    (theory.equations.iseqv.symm equivalent) semanticPath.sourceEquation
  path := semanticPath.path
  targetEquation := semanticPath.targetEquation

/-- Changing the target representative preserves a semantic path without
discarding its concrete rewrite receipt. -/
def SemanticPath.changeTarget
    {theory : GSLT} {source target target' : theory.Term}
    (semanticPath : SemanticPath theory source target)
    (equivalent : theory.Equiv target target') :
    SemanticPath theory source target' where
  startRepresentative := semanticPath.startRepresentative
  endRepresentative := semanticPath.endRepresentative
  sourceEquation := semanticPath.sourceEquation
  path := semanticPath.path
  targetEquation := theory.equations.iseqv.trans
    semanticPath.targetEquation equivalent

/-- The GSLT whose one step is one retained finite semantic path. It keeps
the original equation setoid. -/
def pathGSLT (theory : GSLT) : GSLT where
  Term := theory.Term
  equations := theory.equations
  rewrites := fun source target => Nonempty (SemanticPath theory source target)
  rewrites_resp_left := by
    intro source source' target equivalent ⟨semanticPath⟩
    exact ⟨target, ⟨semanticPath.changeSource equivalent⟩,
      theory.equations.iseqv.refl target⟩
  rewrites_resp_right := by
    intro source target target' ⟨semanticPath⟩ equivalent
    exact ⟨semanticPath.changeTarget equivalent⟩

/-- The GSLT whose one step is one retained semantic path with exactly the
declared number of authored rewrites. -/
def gradedPathGSLT (theory : GSLT) (steps : Nat) : GSLT where
  Term := theory.Term
  equations := theory.equations
  rewrites := fun source target =>
    Nonempty (GradedSemanticPath theory steps source target)
  rewrites_resp_left := by
    intro source source' target equivalent ⟨semanticPath⟩
    refine ⟨target, ⟨?_⟩, theory.equations.iseqv.refl target⟩
    exact
      { toSemanticPath := semanticPath.toSemanticPath.changeSource equivalent
        length_eq := semanticPath.length_eq }
  rewrites_resp_right := by
    intro source target target' ⟨semanticPath⟩ equivalent
    exact ⟨
      { toSemanticPath := semanticPath.toSemanticPath.changeTarget equivalent
        length_eq := semanticPath.length_eq }⟩

@[simp]
theorem pathGSLT_equiv (theory : GSLT) (left right : theory.Term) :
    (pathGSLT theory).Equiv left right ↔ theory.Equiv left right :=
  Iff.rfl

@[simp]
theorem pathGSLT_step (theory : GSLT) (source target : theory.Term) :
    (pathGSLT theory).Step source target ↔
      Nonempty (SemanticPath theory source target) :=
  Iff.rfl

@[simp]
theorem gradedPathGSLT_step (theory : GSLT) (steps : Nat)
    (source target : theory.Term) :
    (gradedPathGSLT theory steps).Step source target ↔
      Nonempty (GradedSemanticPath theory steps source target) :=
  Iff.rfl

/-- With equality as the original equation theory, semantic paths and raw
rewrite paths coincide exactly. -/
theorem nonempty_semanticPath_iff_rewritePath_of_equiv_iff_eq
    (theory : GSLT)
    (equivIffEq : ∀ left right, theory.Equiv left right ↔ left = right)
    (source target : theory.Term) :
    Nonempty (SemanticPath theory source target) ↔
      Nonempty (theory.RewritePath source target) := by
  constructor
  · rintro ⟨semanticPath⟩
    exact ⟨semanticPath.toRewritePathOfEquivIffEq equivIffEq⟩
  · rintro ⟨path⟩
    exact ⟨SemanticPath.ofRewritePath path⟩

/-! ## The canonical OSLF at path granularity -/

/-- Possibility along a finite semantic path. -/
def pathDiamond (theory : GSLT) :
    EquationPredicate (pathGSLT theory) →
      EquationPredicate (pathGSLT theory) :=
  semanticDiamond (pathGSLT theory)

/-- Necessity along the converse of finite semantic paths. -/
def pathBox (theory : GSLT) :
    EquationPredicate (pathGSLT theory) →
      EquationPredicate (pathGSLT theory) :=
  semanticBox (pathGSLT theory)

/-- Possibility along a semantic path of exactly `steps` rewrites. -/
def gradedPathDiamond (theory : GSLT) (steps : Nat) :
    EquationPredicate (gradedPathGSLT theory steps) →
      EquationPredicate (gradedPathGSLT theory steps) :=
  semanticDiamond (gradedPathGSLT theory steps)

/-- Necessity along the converse of semantic paths of exactly `steps`
rewrites. -/
def gradedPathBox (theory : GSLT) (steps : Nat) :
    EquationPredicate (gradedPathGSLT theory steps) →
      EquationPredicate (gradedPathGSLT theory steps) :=
  semanticBox (gradedPathGSLT theory steps)

/-- The finite-path modalities use the canonical OSLF adjunction. -/
theorem pathGalois (theory : GSLT) :
    GaloisConnection (pathDiamond theory) (pathBox theory) :=
  semanticGalois (pathGSLT theory)

/-- Each exact-length path layer uses the canonical OSLF adjunction. -/
theorem gradedPathGalois (theory : GSLT) (steps : Nat) :
    GaloisConnection (gradedPathDiamond theory steps)
      (gradedPathBox theory steps) :=
  semanticGalois (gradedPathGSLT theory steps)

/-- Concrete meaning of finite-path possibility. -/
theorem pathDiamond_spec (theory : GSLT)
    (predicate : EquationPredicate (pathGSLT theory))
    (source : theory.Term) :
    pathDiamond theory predicate source ↔
      ∃ target, Nonempty (SemanticPath theory source target) ∧
        predicate target := by
  change gsltDiamond (pathGSLT theory) predicate.1 source ↔ _
  constructor
  · intro possible
    obtain ⟨target, step, holds⟩ :=
      (gsltDiamond_spec (pathGSLT theory) predicate.1 source).mp possible
    exact ⟨target, step, holds⟩
  · rintro ⟨target, step, holds⟩
    exact (gsltDiamond_spec (pathGSLT theory) predicate.1 source).mpr
      ⟨target, step, holds⟩

/-- Concrete meaning of exact-length path possibility. -/
theorem gradedPathDiamond_spec (theory : GSLT) (steps : Nat)
    (predicate : EquationPredicate (gradedPathGSLT theory steps))
    (source : theory.Term) :
    gradedPathDiamond theory steps predicate source ↔
      ∃ target, Nonempty (GradedSemanticPath theory steps source target) ∧
        predicate target := by
  change gsltDiamond (gradedPathGSLT theory steps) predicate.1 source ↔ _
  constructor
  · intro possible
    obtain ⟨target, step, holds⟩ :=
      (gsltDiamond_spec (gradedPathGSLT theory steps) predicate.1 source).mp
        possible
    exact ⟨target, step, holds⟩
  · rintro ⟨target, step, holds⟩
    exact (gsltDiamond_spec (gradedPathGSLT theory steps) predicate.1 source).mpr
      ⟨target, step, holds⟩

/-- Concrete meaning of finite-path necessity. -/
theorem pathBox_spec (theory : GSLT)
    (predicate : EquationPredicate (pathGSLT theory))
    (target : theory.Term) :
    pathBox theory predicate target ↔
      ∀ source, Nonempty (SemanticPath theory source target) →
        predicate source := by
  change gsltBox (pathGSLT theory) predicate.1 target ↔ _
  constructor
  · intro necessary source step
    exact (gsltBox_spec (pathGSLT theory) predicate.1 target).mp
      necessary source step
  · intro necessary
    apply (gsltBox_spec (pathGSLT theory) predicate.1 target).mpr
    intro source step
    exact necessary source step

/-- The rewrite system at finite-path granularity is generated from its GSLT. -/
def pathRewriteSystem (theory : GSLT) : RewriteSystem :=
  gsltRewriteSystem (pathGSLT theory)

/-- The OSLF at finite-path granularity is the sole canonical construction. -/
def pathOSLF (theory : GSLT) :
    OSLFTypeSystem (pathRewriteSystem theory) :=
  gsltOSLF (pathGSLT theory)

/-- Native predicates generated from finite semantic executions. -/
abbrev PathNativeType (theory : GSLT) : Type _ :=
  NativeTypeOf (pathOSLF theory)

/-- The finite-execution native type of states reaching one semantic
predicate. -/
def reachingNativeType (theory : GSLT)
    (predicate : EquationPredicate (pathGSLT theory)) :
    PathNativeType theory where
  sort := ()
  pred := pathDiamond theory predicate

/-- Inhabitation of a reaching native type retains an modulo-equations
finite path to a state satisfying its target predicate. -/
theorem satisfies_reachingNativeType_iff (theory : GSLT)
    (predicate : EquationPredicate (pathGSLT theory))
    (source : theory.Term) :
    (pathOSLF theory).satisfies source
        (reachingNativeType theory predicate).pred ↔
      ∃ target, Nonempty (SemanticPath theory source target) ∧
        predicate target :=
  pathDiamond_spec theory predicate source

section AxiomAudit

#print axioms pathGalois
#print axioms gradedPathGalois
#print axioms pathDiamond_spec
#print axioms gradedPathDiamond_spec
#print axioms pathBox_spec
#print axioms nonempty_semanticPath_iff_rewritePath_of_equiv_iff_eq
#print axioms satisfies_reachingNativeType_iff

end AxiomAudit

end Mettapedia.OSLF.Framework.PathTypeSynthesis
