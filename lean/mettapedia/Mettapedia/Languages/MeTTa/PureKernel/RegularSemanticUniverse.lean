import Mettapedia.Languages.MeTTa.PureKernel.RegularStructural
import Mettapedia.Languages.MeTTa.PureKernel.RegularContextualIdentity

/-!
# A proof-relevant semantic universe for regular Pure

The regular fragment has a top sort `U1`, but `U1` is not itself typed and
therefore cannot occur as a type stored in a regular context.  We consequently
do not need an impredicative candidate containing itself.  Instead, this module
defines an inductive relation between each type code below `U1` and the
contextual candidate which that code denotes.

The candidate is an index of the relation rather than information recovered by
syntax inspection.  This matters when computation hides the head constructor:
guarded conversion transports the already-earned meaning while retaining
independent accessibility evidence for both code endpoints.

Semantic contexts retain the candidate selected for every telescope entry.
These are the proof-relevant objects needed by the simultaneous formation and
typing fundamental lemma; that lemma is deliberately not claimed here.
-/

namespace Mettapedia.Languages.MeTTa.PureKernel.PresentationBoundary

open Mettapedia.Languages.MeTTa.PureKernel.Syntax
open Mettapedia.Languages.MeTTa.PureKernel.Context
open Mettapedia.Languages.MeTTa.PureKernel.Renaming
open Mettapedia.Languages.MeTTa.PureKernel.Substitution
open Mettapedia.Languages.MeTTa.PureKernel.Reduction
open Mettapedia.Languages.MeTTa.PureKernel.Typing

/-! ## The predicative boundary

`RegularHasType.subject_ne_u1` and `no_regular_u1_term` already prove that the
top sort has no typing derivation.  Conversion can change a type but never a
subject.  This is why the semantic universe below need not contain itself. -/

/-! ## Semantic terms and type codes -/

/-- A term inhabits a contextual candidate in every realizing environment and
also remains inside the declaration-free presentation fragment.  Candidate
membership supplies normalization; the explicit syntax field supplies the
exact Pattern boundary required by the later presentation square. -/
structure SemanticTerm {n : Nat} {context : CoherentCandidateContext n}
    (type : ContextualCandidateType context) (term : PureTm n) : Prop where
  realizes : type.RealizesTerm term
  constantFree : ConstantFree term

namespace SemanticTerm

/-- Semantic membership entails accessibility at the identity environment. -/
theorem accessible {context : CoherentCandidateContext n}
    {type : ContextualCandidateType context} {term : PureTm n}
    (semantic : SemanticTerm type term) : ReductionAccessible term := by
  have covered := semantic.realizes (ids : Sub n n) context.identity_realizes
  simpa only [subst_ids] using type.cr1 context.identity_realizes covered

/-- Every universe constructor is a semantic term of the normalization
candidate. -/
def u0 (context : CoherentCandidateContext n) :
    SemanticTerm (ContextualCandidateType.normalizing context) (.u0 : PureTm n) where
  realizes := by
    intro m environment realized
    exact reductionAccessible_u0
  constantFree := .u0

end SemanticTerm

/-! ## Extensional equality and semantic substitution -/

namespace ContextualCandidateType

/-- Extensional equivalence is the right equality notion for semantic types:
law fields are irrelevant to clients, while membership is observable. -/
def Equivalent {context : CoherentCandidateContext n}
    (left right : ContextualCandidateType context) : Prop :=
  ∀ {m : Nat} (environment : Sub n m) (term : PureTm m),
    left.pred environment term ↔ right.pred environment term

namespace Equivalent

theorem refl (type : ContextualCandidateType context) : type.Equivalent type :=
  fun _ _ => Iff.rfl

theorem symm {left right : ContextualCandidateType context}
    (equivalent : left.Equivalent right) : right.Equivalent left :=
  fun environment term => (equivalent environment term).symm

theorem trans {first middle last : ContextualCandidateType context}
    (left : first.Equivalent middle) (right : middle.Equivalent last) :
    first.Equivalent last :=
  fun environment term =>
    (left environment term).trans (right environment term)

end Equivalent

/-- Reindexing normalization changes only its base context. -/
theorem reindex_normalizing_equivalent
    {source : CoherentCandidateContext n}
    {target : CoherentCandidateContext m} {substitution : Sub n m}
    (map : CandidateSubstitution source.toCandidateContext
      target.toCandidateContext substitution) :
    ((normalizing source).reindex map).Equivalent (normalizing target) :=
  fun _ _ => Iff.rfl

/-- Reindexing along identity is extensionally the original contextual type. -/
theorem reindex_id_equivalent
    {context : CoherentCandidateContext n}
    (type : ContextualCandidateType context) :
    (type.reindex (CandidateSubstitution.id context.toCandidateContext)).Equivalent
      type := by
  intro m environment term
  simp [ContextualCandidateType.reindex]

/-- Contextual realization is stable under every candidate-respecting
substitution. -/
theorem RealizesTerm.subst
    {source : CoherentCandidateContext n}
    {target : CoherentCandidateContext m} {substitution : Sub n m}
    {type : ContextualCandidateType source} {term : PureTm n}
    (realizes : type.RealizesTerm term)
    (map : CandidateSubstitution source.toCandidateContext
      target.toCandidateContext substitution) :
    (type.reindex map).RealizesTerm (subst substitution term) := by
  intro k environment targetRealized
  have sourceRealized := map.maps_realizers environment targetRealized
  have covered := realizes (compSub environment substitution) sourceRealized
  rw [subst_comp]
  exact covered

end ContextualCandidateType

/-- A semantic substitution carries both the candidate-context map and the
exact declaration-free boundary for every substituted variable. -/
structure SemanticSubstitution
    (source : CoherentCandidateContext n)
    (target : CoherentCandidateContext m) (substitution : Sub n m) : Prop where
  maps : CandidateSubstitution source.toCandidateContext
    target.toCandidateContext substitution
  constantFree : ∀ index, ConstantFree (substitution index)

namespace SemanticSubstitution

/-- The tail of a composed lifted substitution is composition through the
tail environment. -/
theorem tailSub_compSub_liftSub
    (environment : Sub (m + 1) k) (substitution : Sub n m) :
    tailSub (compSub environment (liftSub substitution)) =
      compSub (tailSub environment) substitution := by
  funext index
  change subst environment (rename wk (substitution index)) =
    subst (tailSub environment) (substitution index)
  calc
    subst environment (rename wk (substitution index)) =
        subst (fun i => environment (wk i)) (substitution index) :=
      subst_rename (σ := environment) (ρ := (wk : Ren m (m + 1)))
        (t := substitution index)
    _ = subst (tailSub environment) (substitution index) := by
      apply subst_ext
      intro i
      rfl

/-- Composing an extended environment with a lifted substitution preserves
the head and composes the tails. -/
theorem compSub_consSub_liftSub
    (head : PureTm k) (tail : Sub m k) (substitution : Sub n m) :
    compSub (consSub head tail) (liftSub substitution) =
      consSub head (compSub tail substitution) := by
  funext index
  refine Fin.cases ?_ ?_ index
  · rfl
  · intro preceding
    change subst (consSub head tail) (rename wk (substitution preceding)) =
      subst tail (substitution preceding)
    calc
      subst (consSub head tail) (rename wk (substitution preceding)) =
          subst (fun i => consSub head tail (wk i))
            (substitution preceding) :=
        subst_rename (σ := consSub head tail) (ρ := (wk : Ren m (m + 1)))
          (t := substitution preceding)
      _ = subst tail (substitution preceding) := by
        apply subst_ext
        intro i
        rfl

/-- Renaming every image after composition agrees with composing after
renaming every image. -/
theorem renameEnvironment_compSub
    (ρ : Ren k l) (environment : Sub m k) (substitution : Sub n m) :
    renameEnvironment ρ (compSub environment substitution) =
      compSub (renameEnvironment ρ environment) substitution := by
  funext index
  exact rename_subst ρ environment (substitution index)

/-- Identity is a semantic substitution. -/
def id (context : CoherentCandidateContext n) :
    SemanticSubstitution context context ids where
  maps := CandidateSubstitution.id context.toCandidateContext
  constantFree := fun index => .var index

/-- The projection from a contextual extension to its base is an internal
semantic substitution. -/
def projection
    {context : CoherentCandidateContext n}
    (domain : ContextualCandidateType context) :
    SemanticSubstitution context (context.extendContextual domain)
      (renToSub wk) where
  maps :=
    { maps_realizers := by
        intro m environment realized
        rw [compSub_renToSub_wk]
        exact realized.1 }
  constantFree := fun index => .var (wk index)

/-- Reindexing through contextual projection is extensionally the established
weakening construction. -/
theorem reindex_projection_equivalent
    {context : CoherentCandidateContext n}
    (type : ContextualCandidateType context) :
    (type.reindex (projection type).maps).Equivalent type.weaken := by
  intro m environment term
  change type.pred (compSub environment (renToSub wk)) term ↔
    type.pred (tailSub environment) term
  rw [compSub_renToSub_wk]

/-- Extensionally equivalent domain candidates induce a semantic identity map
between their contextual extensions.  The syntax substitution is literally
identity; only the proof-relevant realization boundary changes. -/
def extensionIdentity
    {context : CoherentCandidateContext n}
    (left right : ContextualCandidateType context)
    (equivalent : left.Equivalent right) :
    SemanticSubstitution (context.extendContextual right)
      (context.extendContextual left) ids where
  maps :=
    { maps_realizers := by
        intro m environment realized
        have composed : compSub environment ids = environment := by
          funext index
          rfl
        rw [composed]
        exact ⟨realized.1,
          (equivalent (tailSub environment) (environment 0)).1 realized.2⟩ }
  constantFree := fun index => .var index

/-- Lift a semantic substitution through corresponding contextual extensions.
The target domain need only be extensionally equivalent to the pullback of the
source domain; proof-record identity is neither required nor observed. -/
def lift
    {source : CoherentCandidateContext n}
    {target : CoherentCandidateContext m} {substitution : Sub n m}
    (domain : ContextualCandidateType source)
    (targetDomain : ContextualCandidateType target)
    (base : SemanticSubstitution source target substitution)
    (domainEquivalent : targetDomain.Equivalent
      (domain.reindex base.maps)) :
    SemanticSubstitution
      (source.extendContextual domain)
      (target.extendContextual targetDomain)
      (liftSub substitution) where
  maps :=
    { maps_realizers := by
        intro k environment targetRealized
        constructor
        · rw [tailSub_compSub_liftSub]
          exact base.maps.maps_realizers (tailSub environment) targetRealized.1
        · rw [tailSub_compSub_liftSub]
          exact (domainEquivalent (tailSub environment) (environment 0)).1
            targetRealized.2 }
  constantFree := by
    intro index
    refine Fin.cases ?_ ?_ index
    · exact .var 0
    · intro preceding
      exact (base.constantFree preceding).rename wk

/-- Reindexing a dependent function candidate is extensionally the dependent
function candidate assembled from the reindexed fibres. -/
theorem reindex_pi_equivalent
    {source : CoherentCandidateContext n}
    {target : CoherentCandidateContext m} {substitution : Sub n m}
    (domain : ContextualCandidateType source)
    (targetDomain : ContextualCandidateType target)
    (codomain : ContextualCandidateType (source.extendContextual domain))
    (targetCodomain :
      ContextualCandidateType (target.extendContextual targetDomain))
    (base : SemanticSubstitution source target substitution)
    (domainEquivalent : targetDomain.Equivalent
      (domain.reindex base.maps))
    (codomainEquivalent : targetCodomain.Equivalent
      (codomain.reindex (lift domain targetDomain base domainEquivalent).maps)) :
    (targetDomain.pi targetCodomain).Equivalent
      ((domain.pi codomain).reindex base.maps) := by
  intro k environment function
  constructor
  · intro targetCovered l ρ argument argumentAtSource
    have argumentAtPullback :
        (domain.reindex base.maps).pred
          (renameEnvironment ρ environment) argument := by
      change domain.pred
        (compSub (renameEnvironment ρ environment) substitution) argument
      rw [← renameEnvironment_compSub ρ environment substitution]
      exact argumentAtSource
    have argumentAtTarget :=
      (domainEquivalent (renameEnvironment ρ environment) argument).2
        argumentAtPullback
    have targetResult := targetCovered ρ argument argumentAtTarget
    have pullbackResult :=
      (codomainEquivalent
        (consSub argument (renameEnvironment ρ environment))
        (.app (rename ρ function) argument)).1 targetResult
    change codomain.pred
      (consSub argument
        (renameEnvironment ρ (compSub environment substitution)))
      (.app (rename ρ function) argument)
    change codomain.pred
      (compSub (consSub argument (renameEnvironment ρ environment))
        (liftSub substitution))
      (.app (rename ρ function) argument) at pullbackResult
    rw [compSub_consSub_liftSub] at pullbackResult
    rw [← renameEnvironment_compSub ρ environment substitution] at pullbackResult
    exact pullbackResult
  · intro sourceCovered l ρ argument argumentAtTarget
    have argumentAtPullback :=
      (domainEquivalent (renameEnvironment ρ environment) argument).1
        argumentAtTarget
    have argumentAtSource :
        domain.pred
          (renameEnvironment ρ (compSub environment substitution)) argument := by
      change domain.pred
        (compSub (renameEnvironment ρ environment) substitution) argument at argumentAtPullback
      rw [← renameEnvironment_compSub ρ environment substitution] at argumentAtPullback
      exact argumentAtPullback
    have sourceResult := sourceCovered ρ argument argumentAtSource
    have pullbackResult :
        (codomain.reindex
          (lift domain targetDomain base domainEquivalent).maps).pred
          (consSub argument (renameEnvironment ρ environment))
          (.app (rename ρ function) argument) := by
      change codomain.pred
        (compSub (consSub argument (renameEnvironment ρ environment))
          (liftSub substitution))
        (.app (rename ρ function) argument)
      rw [compSub_consSub_liftSub,
        ← renameEnvironment_compSub ρ environment substitution]
      exact sourceResult
    exact (codomainEquivalent
      (consSub argument (renameEnvironment ρ environment))
      (.app (rename ρ function) argument)).2 pullbackResult

/-- Reindexing a dependent pair candidate commutes with assembling its
reindexed fibres. -/
theorem reindex_sigma_equivalent
    {source : CoherentCandidateContext n}
    {target : CoherentCandidateContext m} {substitution : Sub n m}
    (domain : ContextualCandidateType source)
    (targetDomain : ContextualCandidateType target)
    (codomain : ContextualCandidateType (source.extendContextual domain))
    (targetCodomain :
      ContextualCandidateType (target.extendContextual targetDomain))
    (base : SemanticSubstitution source target substitution)
    (domainEquivalent : targetDomain.Equivalent
      (domain.reindex base.maps))
    (codomainEquivalent : targetCodomain.Equivalent
      (codomain.reindex (lift domain targetDomain base domainEquivalent).maps)) :
    (targetDomain.sigma targetCodomain).Equivalent
      ((domain.sigma codomain).reindex base.maps) := by
  intro k environment pair
  constructor
  · intro targetCovered
    constructor
    · exact (domainEquivalent environment (.fst pair)).1 targetCovered.1
    · have pullbackSecond :=
        (codomainEquivalent (consSub (.fst pair) environment) (.snd pair)).1
          targetCovered.2
      change codomain.pred
        (consSub (.fst pair) (compSub environment substitution)) (.snd pair)
      change codomain.pred
        (compSub (consSub (.fst pair) environment) (liftSub substitution))
        (.snd pair) at pullbackSecond
      rw [compSub_consSub_liftSub] at pullbackSecond
      exact pullbackSecond
  · intro sourceCovered
    constructor
    · exact (domainEquivalent environment (.fst pair)).2 sourceCovered.1
    · apply (codomainEquivalent
        (consSub (.fst pair) environment) (.snd pair)).2
      change codomain.pred
        (compSub (consSub (.fst pair) environment) (liftSub substitution))
        (.snd pair)
      rw [compSub_consSub_liftSub]
      exact sourceCovered.2

/-- Semantic comprehension: a base substitution and a term in the pulled-back
domain form a substitution into the corresponding contextual extension. -/
def pair
    {source : CoherentCandidateContext n}
    {target : CoherentCandidateContext m} {substitution : Sub n m}
    (domain : ContextualCandidateType source)
    (base : SemanticSubstitution source target substitution)
    {term : PureTm m}
    (head : SemanticTerm (domain.reindex base.maps) term) :
    SemanticSubstitution (source.extendContextual domain) target
      (consSub term substitution) where
  maps :=
    { maps_realizers := by
        intro k environment targetRealized
        have baseRealized := base.maps.maps_realizers environment targetRealized
        have headRealized := head.realizes environment targetRealized
        constructor
        · rw [tailSub_compSub_consSub]
          exact baseRealized
        · rw [tailSub_compSub_consSub]
          exact headRealized }
  constantFree := by
    intro index
    refine Fin.cases ?_ ?_ index
    · exact head.constantFree
    · intro preceding
      exact base.constantFree preceding

/-- Pairing with identity is the semantic singleton substitution used by
dependent application, pair introduction, and second projection. -/
def instantiate
    {context : CoherentCandidateContext n}
    (domain : ContextualCandidateType context)
    {term : PureTm n} (head : SemanticTerm domain term) :
    SemanticSubstitution (context.extendContextual domain) context
      (subst0 term) := by
  have reindexedHead :
      SemanticTerm
        (domain.reindex
          (CandidateSubstitution.id context.toCandidateContext)) term :=
    { realizes := by
        intro m environment realized
        exact (ContextualCandidateType.reindex_id_equivalent domain
          environment (Substitution.subst environment term)).2
            (head.realizes environment realized)
      constantFree := head.constantFree }
  simpa only [show consSub term ids = subst0 term from rfl] using
    pair domain (id context) reindexedHead

end SemanticSubstitution

namespace SemanticTerm

/-- Semantic terms transport across pointwise-equivalent candidate meanings. -/
theorem of_equivalent
    {context : CoherentCandidateContext n}
    {left right : ContextualCandidateType context} {term : PureTm n}
    (semantic : SemanticTerm left term)
    (equivalent : left.Equivalent right) : SemanticTerm right term where
  realizes := by
    intro m environment realized
    exact (equivalent environment (Substitution.subst environment term)).1
      (semantic.realizes environment realized)
  constantFree := semantic.constantFree

/-- Semantic terms substitute along semantic substitutions. -/
theorem subst
    {source : CoherentCandidateContext n}
    {target : CoherentCandidateContext m} {substitution : Sub n m}
    {type : ContextualCandidateType source} {term : PureTm n}
    (semantic : SemanticTerm type term)
    (map : SemanticSubstitution source target substitution) :
    SemanticTerm (type.reindex map.maps) (Substitution.subst substitution term) where
  realizes := ContextualCandidateType.RealizesTerm.subst
    semantic.realizes map.maps
  constantFree := semantic.constantFree.subst map.constantFree

end SemanticTerm

/-- Lifting a realizing environment through a contextual extension supplies a
fresh neutral head in the weakened domain fibre. -/
theorem CoherentCandidateContext.liftSub_realizes
    {context : CoherentCandidateContext n}
    (domain : ContextualCandidateType context)
    {environment : Sub n m} (realized : context.Realizes environment) :
    (context.extendContextual domain).Realizes (liftSub environment) := by
  constructor
  · change context.Realizes (renameEnvironment wk environment)
    exact context.rename_realizes environment wk realized
  · apply domain.cr3
      (context.rename_realizes environment wk realized) (neutral_var 0)
    intro target step
    cases step

namespace SemanticTerm

/-- Semantic normalization is closed under dependent function codes. -/
def piCode
    {context : CoherentCandidateContext n}
    {domainCode : PureTm n} {codomainCode : PureTm (n + 1)}
    (domain : ContextualCandidateType context)
    (domainNormalizes :
      SemanticTerm (ContextualCandidateType.normalizing context) domainCode)
    (codomainNormalizes : SemanticTerm
      (ContextualCandidateType.normalizing (context.extendContextual domain))
      codomainCode) :
    SemanticTerm (ContextualCandidateType.normalizing context)
      (.pi domainCode codomainCode) where
  realizes := by
    intro m environment realized
    change ReductionAccessible
      (.pi (Substitution.subst environment domainCode)
        (Substitution.subst (liftSub environment) codomainCode))
    exact reductionAccessible_pi
      (domainNormalizes.realizes environment realized)
      (codomainNormalizes.realizes (liftSub environment)
        (context.liftSub_realizes domain realized))
  constantFree := .pi domainNormalizes.constantFree
    codomainNormalizes.constantFree

/-- Semantic normalization is closed under dependent pair codes. -/
def sigmaCode
    {context : CoherentCandidateContext n}
    {domainCode : PureTm n} {codomainCode : PureTm (n + 1)}
    (domain : ContextualCandidateType context)
    (domainNormalizes :
      SemanticTerm (ContextualCandidateType.normalizing context) domainCode)
    (codomainNormalizes : SemanticTerm
      (ContextualCandidateType.normalizing (context.extendContextual domain))
      codomainCode) :
    SemanticTerm (ContextualCandidateType.normalizing context)
      (.sigma domainCode codomainCode) where
  realizes := by
    intro m environment realized
    change ReductionAccessible
      (.sigma (Substitution.subst environment domainCode)
        (Substitution.subst (liftSub environment) codomainCode))
    exact reductionAccessible_sigma
      (domainNormalizes.realizes environment realized)
      (codomainNormalizes.realizes (liftSub environment)
        (context.liftSub_realizes domain realized))
  constantFree := .sigma domainNormalizes.constantFree
    codomainNormalizes.constantFree

/-- Semantic normalization is closed under identity codes. -/
def identityCode
    {context : CoherentCandidateContext n}
    {typeCode left right : PureTm n}
    {type : ContextualCandidateType context}
    (typeNormalizes :
      SemanticTerm (ContextualCandidateType.normalizing context) typeCode)
    (leftSemantic : SemanticTerm type left)
    (rightSemantic : SemanticTerm type right) :
    SemanticTerm (ContextualCandidateType.normalizing context)
      (.id typeCode left right) where
  realizes := by
    intro m environment realized
    change ReductionAccessible
      (.id (Substitution.subst environment typeCode)
        (Substitution.subst environment left)
        (Substitution.subst environment right))
    exact reductionAccessible_id
      (typeNormalizes.realizes environment realized)
      (type.cr1 realized (leftSemantic.realizes environment realized))
      (type.cr1 realized (rightSemantic.realizes environment realized))
  constantFree := .id typeNormalizes.constantFree
    leftSemantic.constantFree rightSemantic.constantFree

end SemanticTerm

/-- A conversion recognized by the semantic universe is normalized in every
realizing environment at both endpoints.  This is strictly stronger than
identity-environment accessibility and is the guard stable under dependent
substitution. -/
structure SemanticConstantFreeConv
    (context : CoherentCandidateContext n) (source target : PureTm n) : Prop where
  converts : ConstantFreeConv source target
  sourceNormalizes :
    SemanticTerm (ContextualCandidateType.normalizing context) source
  targetNormalizes :
    SemanticTerm (ContextualCandidateType.normalizing context) target

namespace SemanticConstantFreeConv

def symm (conversion : SemanticConstantFreeConv context source target) :
    SemanticConstantFreeConv context target source where
  converts := .symm conversion.converts
  sourceNormalizes := conversion.targetNormalizes
  targetNormalizes := conversion.sourceNormalizes

def trans (first : SemanticConstantFreeConv context source middle)
    (second : SemanticConstantFreeConv context middle target) :
    SemanticConstantFreeConv context source target where
  converts := .trans first.converts second.converts
  sourceNormalizes := first.sourceNormalizes
  targetNormalizes := second.targetNormalizes

/-- Semantic conversion is stable under every semantic substitution. -/
def subst
    {sourceContext : CoherentCandidateContext n}
    {targetContext : CoherentCandidateContext m}
    {substitution : Sub n m} {source target : PureTm n}
    (conversion : SemanticConstantFreeConv sourceContext source target)
    (map : SemanticSubstitution sourceContext targetContext substitution) :
    SemanticConstantFreeConv targetContext
      (Substitution.subst substitution source)
      (Substitution.subst substitution target) where
  converts := conversion.converts.subst substitution map.constantFree
  sourceNormalizes :=
    (conversion.sourceNormalizes.subst map).of_equivalent
      (ContextualCandidateType.reindex_normalizing_equivalent map.maps)
  targetNormalizes :=
    (conversion.targetNormalizes.subst map).of_equivalent
      (ContextualCandidateType.reindex_normalizing_equivalent map.maps)

end SemanticConstantFreeConv

/-- The semantic universe relation.  `SemanticType context code meaning` says
that `code` is a type code below `U1` and denotes exactly `meaning` over the
given semantic context.

The relation is intentionally proof-relevant in its indices: clients retain
the candidate meaning instead of merely learning that some candidate exists. -/
inductive SemanticType : {n : Nat} →
    (context : CoherentCandidateContext n) →
    PureTm n → ContextualCandidateType context → Prop where
  /-- `U0` classifies terms only through normalization in this fragment; it has
  no eliminator capable of imposing a stronger observation. -/
  | u0 (context : CoherentCandidateContext n) :
      SemanticType context .u0 (ContextualCandidateType.normalizing context)
  /-- Dependent function codes retain both their domain meaning and the
  codomain meaning over the corresponding context extension. -/
  | pi {context : CoherentCandidateContext n}
      {domainCode : PureTm n} {codomainCode : PureTm (n + 1)}
      {domain : ContextualCandidateType context}
      {codomain : ContextualCandidateType
        (context.extendContextual domain)} :
      SemanticType context domainCode domain →
      SemanticType (context.extendContextual domain) codomainCode codomain →
      SemanticType context (.pi domainCode codomainCode)
        (domain.pi codomain)
  /-- Dependent pair codes retain the same genuinely dependent indexing. -/
  | sigma {context : CoherentCandidateContext n}
      {domainCode : PureTm n} {codomainCode : PureTm (n + 1)}
      {domain : ContextualCandidateType context}
      {codomain : ContextualCandidateType
        (context.extendContextual domain)} :
      SemanticType context domainCode domain →
      SemanticType (context.extendContextual domain) codomainCode codomain →
      SemanticType context (.sigma domainCode codomainCode)
        (domain.sigma codomain)
  /-- The present identity fragment has reflexivity but no eliminator.  Its
  semantic meaning is therefore the scoped normalization candidate, while the
  constructor retains the endpoint typing evidence and exact syntax boundary. -/
  | identity {context : CoherentCandidateContext n}
      {typeCode left right : PureTm n}
      {type : ContextualCandidateType context} :
      SemanticType context typeCode type →
      SemanticTerm type left →
      SemanticTerm type right →
      SemanticType context (.id typeCode left right)
        (ContextualCandidateType.normalizing context)
  /-- Type-level computation preserves an already-earned candidate meaning
  only when both code endpoints normalize in every realizing environment. -/
  | convert {context : CoherentCandidateContext n}
      {source target : PureTm n}
      {meaning : ContextualCandidateType context} :
      SemanticType context source meaning →
      SemanticConstantFreeConv context source target →
      SemanticType context target meaning

namespace SemanticType

/-- Every semantically interpreted type code normalizes after every environment
which realizes its semantic context.  This is the Kripke-strength invariant
needed by dependent substitution. -/
theorem normalizes {context : CoherentCandidateContext n}
    {code : PureTm n} {meaning : ContextualCandidateType context}
    (semantic : SemanticType context code meaning) :
    SemanticTerm (ContextualCandidateType.normalizing context) code := by
  induction semantic with
  | u0 => exact SemanticTerm.u0 _
  | pi _ _ ihDomain ihCodomain =>
      exact SemanticTerm.piCode _ ihDomain ihCodomain
  | sigma _ _ ihDomain ihCodomain =>
      exact SemanticTerm.sigmaCode _ ihDomain ihCodomain
  | identity _ left right ihType =>
      exact SemanticTerm.identityCode ihType left right
  | convert _ conversion ih =>
      exact conversion.targetNormalizes

/-- Every semantically interpreted type code is strongly normalizing. -/
theorem code_accessible {context : CoherentCandidateContext n}
    {code : PureTm n} {meaning : ContextualCandidateType context}
    (semantic : SemanticType context code meaning) :
    ReductionAccessible code :=
  semantic.normalizes.accessible

/-- Every semantically interpreted type code belongs to the exact common
declaration-free syntax. -/
theorem code_constantFree {context : CoherentCandidateContext n}
    {code : PureTm n} {meaning : ContextualCandidateType context}
    (semantic : SemanticType context code meaning) : ConstantFree code := by
  exact semantic.normalizes.constantFree

/-- Guarded conversion can be oriented in either direction without changing
the retained candidate meaning. -/
theorem of_semantic_conversion_iff
    {context : CoherentCandidateContext n}
    {source target : PureTm n}
    {meaning : ContextualCandidateType context}
    (conversion : SemanticConstantFreeConv context source target) :
    SemanticType context source meaning ↔
      SemanticType context target meaning := by
  constructor
  · intro sourceSemantic
    exact .convert sourceSemantic conversion
  · intro targetSemantic
    exact .convert targetSemantic conversion.symm

/-- Semantic type codes and their retained meanings pull back along every
semantic substitution.  The resulting candidate is extensionally the
reindexing of the source meaning; proof-record identity is not exposed. -/
theorem subst_exists
    {source : CoherentCandidateContext n}
    {code : PureTm n} {meaning : ContextualCandidateType source}
    (semantic : SemanticType source code meaning)
    {target : CoherentCandidateContext m} {substitution : Sub n m}
    (map : SemanticSubstitution source target substitution) :
    ∃ targetMeaning : ContextualCandidateType target,
      SemanticType target (Substitution.subst substitution code) targetMeaning ∧
      targetMeaning.Equivalent (meaning.reindex map.maps) := by
  induction semantic generalizing m with
  | u0 =>
      refine ⟨ContextualCandidateType.normalizing target, .u0 target, ?_⟩
      exact ContextualCandidateType.Equivalent.symm
        (ContextualCandidateType.reindex_normalizing_equivalent map.maps)
  | @pi n source domainCode codomainCode domain codomain
      domainSemantic codomainSemantic domainIH codomainIH =>
      rcases domainIH map with
        ⟨targetDomain, targetDomainSemantic, domainEquivalent⟩
      let lifted := SemanticSubstitution.lift domain targetDomain map
        domainEquivalent
      rcases codomainIH lifted with
        ⟨targetCodomain, targetCodomainSemantic, codomainEquivalent⟩
      refine ⟨targetDomain.pi targetCodomain, ?_, ?_⟩
      · exact .pi targetDomainSemantic targetCodomainSemantic
      · exact SemanticSubstitution.reindex_pi_equivalent domain targetDomain
          codomain targetCodomain map domainEquivalent codomainEquivalent
  | @sigma n source domainCode codomainCode domain codomain
      domainSemantic codomainSemantic domainIH codomainIH =>
      rcases domainIH map with
        ⟨targetDomain, targetDomainSemantic, domainEquivalent⟩
      let lifted := SemanticSubstitution.lift domain targetDomain map
        domainEquivalent
      rcases codomainIH lifted with
        ⟨targetCodomain, targetCodomainSemantic, codomainEquivalent⟩
      refine ⟨targetDomain.sigma targetCodomain, ?_, ?_⟩
      · exact .sigma targetDomainSemantic targetCodomainSemantic
      · exact SemanticSubstitution.reindex_sigma_equivalent domain targetDomain
          codomain targetCodomain map domainEquivalent codomainEquivalent
  | @identity n source typeCode left right type typeSemantic leftSemantic
      rightSemantic typeIH =>
      rcases typeIH map with
        ⟨targetType, targetTypeSemantic, typeEquivalent⟩
      have targetLeft : SemanticTerm targetType
          (Substitution.subst substitution left) :=
        (leftSemantic.subst map).of_equivalent typeEquivalent.symm
      have targetRight : SemanticTerm targetType
          (Substitution.subst substitution right) :=
        (rightSemantic.subst map).of_equivalent typeEquivalent.symm
      refine ⟨ContextualCandidateType.normalizing target, ?_, ?_⟩
      · exact .identity targetTypeSemantic targetLeft targetRight
      · exact
          ContextualCandidateType.Equivalent.symm
            (ContextualCandidateType.reindex_normalizing_equivalent map.maps)
  | @convert n source sourceCode targetCode meaning sourceSemantic conversion
      sourceIH =>
      rcases sourceIH map with
        ⟨targetMeaning, targetSemantic, meaningEquivalent⟩
      refine ⟨targetMeaning, ?_, meaningEquivalent⟩
      exact .convert targetSemantic (conversion.subst map)

end SemanticType

/-- A first-class witness that a code has a retained semantic meaning.  Unlike
an unindexed existence proposition, this package can be stored in later
semantic-context and internal-language structures. -/
structure SemanticTypeWitness {n : Nat}
    (context : CoherentCandidateContext n) (code : PureTm n) where
  meaning : ContextualCandidateType context
  semantic : SemanticType context code meaning

namespace SemanticTypeWitness

theorem code_accessible (witness : SemanticTypeWitness context code) :
    ReductionAccessible code :=
  witness.semantic.code_accessible

theorem code_constantFree (witness : SemanticTypeWitness context code) :
    ConstantFree code :=
  witness.semantic.code_constantFree

end SemanticTypeWitness

/-! ## Proof-relevant semantic contexts -/

/-- A raw telescope is interpreted by a coherent candidate context when every
extension code denotes the exact contextual candidate used to extend the
semantic context. -/
inductive SemanticContext : {n : Nat} → Ctx n →
    CoherentCandidateContext n → Prop where
  | nil : SemanticContext (.nil : Ctx 0) CoherentCandidateContext.empty
  | snoc {context : CoherentCandidateContext n} {syntaxContext : Ctx n}
      {code : PureTm n} {meaning : ContextualCandidateType context} :
      SemanticContext syntaxContext context →
      SemanticType context code meaning →
      SemanticContext (.snoc syntaxContext code)
        (context.extendContextual meaning)

namespace SemanticContext

/-- Semantic context formation entails the exact declaration-free context
boundary; no separate side condition is assumed. -/
theorem syntax_constantFree {syntaxContext : Ctx n}
    {context : CoherentCandidateContext n}
    (semantic : SemanticContext syntaxContext context) :
    ConstantFreeCtx syntaxContext := by
  induction semantic with
  | nil => trivial
  | snoc _ typeSemantic ih =>
      exact ⟨ih, typeSemantic.code_constantFree⟩

/-- Every variable in a semantic telescope has both a semantic type code and
membership in the exact retained meaning of that code. -/
theorem lookup_exists {syntaxContext : Ctx n}
    {context : CoherentCandidateContext n}
    (semantic : SemanticContext syntaxContext context) (index : Fin n) :
    ∃ meaning : ContextualCandidateType context,
      SemanticType context (lookup syntaxContext index) meaning ∧
      SemanticTerm meaning (.var index) := by
  induction semantic with
  | nil => exact Fin.elim0 index
  | @snoc n context syntaxContext code domain baseSemantic typeSemantic ih =>
      refine Fin.cases ?_ ?_ index
      · let project := SemanticSubstitution.projection domain
        rcases typeSemantic.subst_exists project with
          ⟨targetMeaning, targetSemantic, targetEquivalent⟩
        have weakenedHead : SemanticTerm domain.weaken (.var 0) :=
          ⟨ContextualCandidateType.head_realizes domain, .var 0⟩
        have weakenedEquivalent : domain.weaken.Equivalent targetMeaning :=
          ContextualCandidateType.Equivalent.trans
            (ContextualCandidateType.Equivalent.symm
              (SemanticSubstitution.reindex_projection_equivalent domain))
            (ContextualCandidateType.Equivalent.symm targetEquivalent)
        refine ⟨targetMeaning, ?_,
          weakenedHead.of_equivalent weakenedEquivalent⟩
        simpa only [lookup_snoc_zero, subst_renToSub] using targetSemantic
      · intro preceding
        rcases ih preceding with
          ⟨sourceMeaning, sourceSemantic, sourceVariable⟩
        let project := SemanticSubstitution.projection domain
        rcases sourceSemantic.subst_exists project with
          ⟨targetMeaning, targetSemantic, targetEquivalent⟩
        have targetVariable : SemanticTerm targetMeaning (.var preceding.succ) := by
          have pulled := sourceVariable.subst project
          have transported := pulled.of_equivalent
            (ContextualCandidateType.Equivalent.symm targetEquivalent)
          simpa only [subst_renToSub, Renaming.rename, wk] using transported
        refine ⟨targetMeaning, ?_, targetVariable⟩
        simpa only [lookup_snoc_succ, subst_renToSub] using targetSemantic

end SemanticContext

/-- A proof-relevant interpretation package for a raw context. -/
structure SemanticContextWitness {n : Nat} (syntaxContext : Ctx n) where
  context : CoherentCandidateContext n
  semantic : SemanticContext syntaxContext context

/-! ## Positive type constructors -/

def semanticEmptyU0 :
    ContextualCandidateType CoherentCandidateContext.empty :=
  ContextualCandidateType.normalizing CoherentCandidateContext.empty

def semanticU0Codomain :
    ContextualCandidateType
      (CoherentCandidateContext.empty.extendContextual semanticEmptyU0) :=
  ContextualCandidateType.normalizing _

def semanticU0Pi :
    ContextualCandidateType CoherentCandidateContext.empty :=
  semanticEmptyU0.pi semanticU0Codomain

def semanticU0Sigma :
    ContextualCandidateType CoherentCandidateContext.empty :=
  semanticEmptyU0.sigma semanticU0Codomain

theorem semantic_u0_pi :
    SemanticType CoherentCandidateContext.empty
      (.pi .u0 .u0 : PureTm 0) semanticU0Pi :=
  .pi (.u0 _) (.u0 _)

theorem semantic_u0_sigma :
    SemanticType CoherentCandidateContext.empty
      (.sigma .u0 .u0 : PureTm 0) semanticU0Sigma :=
  .sigma (.u0 _) (.u0 _)

theorem semantic_u0_identity :
    SemanticType CoherentCandidateContext.empty
      (.id .u0 .u0 .u0 : PureTm 0)
      (ContextualCandidateType.normalizing CoherentCandidateContext.empty) :=
  .identity (.u0 _) (SemanticTerm.u0 _) (SemanticTerm.u0 _)

def semanticOneU0Context : CoherentCandidateContext 1 :=
  CoherentCandidateContext.empty.extendContextual semanticEmptyU0

theorem semantic_one_u0_context :
    SemanticContext (.snoc .nil .u0 : Ctx 1) semanticOneU0Context :=
  .snoc .nil (.u0 _)

/-! ## A computed type code retains its meaning -/

/-- A type-level beta redex whose normal form is the dependent `U0` function
code. -/
def hiddenSemanticPi : PureTm 0 :=
  .app (.lam (.pi .u0 .u0)) .u0

theorem hiddenSemanticPi_reduces :
    Red hiddenSemanticPi (.pi .u0 .u0 : PureTm 0) := by
  simpa [hiddenSemanticPi, inst0, subst0, subst] using
    (Red.betaPi (.pi .u0 .u0 : PureTm 1) (.u0 : PureTm 0))

theorem hiddenSemanticPi_constantFree : ConstantFree hiddenSemanticPi :=
  .app (.lam (.pi .u0 .u0)) .u0

theorem hiddenSemanticPi_accessible : ReductionAccessible hiddenSemanticPi := by
  apply reductionAccessible_beta_expansion
  · exact reductionAccessible_pi reductionAccessible_u0 reductionAccessible_u0
  · exact reductionAccessible_u0
  · simpa [inst0, subst0, subst] using
      (reductionAccessible_pi reductionAccessible_u0 reductionAccessible_u0 :
        ReductionAccessible (.pi .u0 .u0 : PureTm 0))

/-- The hidden dependent function code normalizes uniformly after every
realizing environment, not merely at the identity substitution. -/
def hiddenSemanticPi_normalizes :
    SemanticTerm
      (ContextualCandidateType.normalizing CoherentCandidateContext.empty)
      hiddenSemanticPi where
  realizes := by
    intro m environment realized
    change ReductionAccessible (.app (.lam (.pi .u0 .u0)) .u0 : PureTm m)
    apply reductionAccessible_beta_expansion
    · exact reductionAccessible_pi reductionAccessible_u0 reductionAccessible_u0
    · exact reductionAccessible_u0
    · simpa [inst0, subst0, subst] using
        (reductionAccessible_pi reductionAccessible_u0 reductionAccessible_u0 :
          ReductionAccessible (.pi .u0 .u0 : PureTm m))
  constantFree := hiddenSemanticPi_constantFree

def hiddenSemanticPiConversion :
    SemanticConstantFreeConv CoherentCandidateContext.empty hiddenSemanticPi
      (.pi .u0 .u0 : PureTm 0) where
  converts := .rel ⟨hiddenSemanticPi_reduces,
    hiddenSemanticPi_constantFree, semantic_u0_pi.code_constantFree⟩
  sourceNormalizes := hiddenSemanticPi_normalizes
  targetNormalizes := semantic_u0_pi.normalizes

/-- The semantic universe does not inspect only the visible syntax head: the
beta-hidden dependent function code retains the same candidate meaning as its
computed form. -/
theorem hidden_semantic_pi_has_pi_meaning :
    SemanticType CoherentCandidateContext.empty hiddenSemanticPi semanticU0Pi :=
  .convert semantic_u0_pi hiddenSemanticPiConversion.symm

/-! ## Negative controls -/

/-- The looping term cannot masquerade as a semantic type code under any
candidate meaning. -/
theorem omega_has_no_semantic_type :
    ¬ ∃ meaning : ContextualCandidateType CoherentCandidateContext.empty,
      SemanticType CoherentCandidateContext.empty regularOmega meaning := by
  rintro ⟨meaning, semantic⟩
  exact omega_not_in_normalizing_candidate semantic.code_accessible

/-- Even a raw beta conversion to `U0` cannot install a hidden looping source
as a semantic type code.  The accessibility guard is therefore doing semantic
work rather than recording redundant metadata. -/
theorem erasing_omega_has_no_semantic_type :
    ¬ ∃ meaning : ContextualCandidateType CoherentCandidateContext.empty,
      SemanticType CoherentCandidateContext.empty regularErasingOmega meaning := by
  rintro ⟨meaning, semantic⟩
  exact regularErasingOmega_not_accessible semantic.code_accessible

/-! ## Axiom audit -/

#print axioms SemanticTerm.accessible
#print axioms ContextualCandidateType.reindex_normalizing_equivalent
#print axioms ContextualCandidateType.RealizesTerm.subst
#print axioms SemanticSubstitution.tailSub_compSub_liftSub
#print axioms SemanticSubstitution.compSub_consSub_liftSub
#print axioms SemanticSubstitution.renameEnvironment_compSub
#print axioms SemanticSubstitution.projection
#print axioms SemanticSubstitution.reindex_projection_equivalent
#print axioms SemanticSubstitution.lift
#print axioms SemanticSubstitution.reindex_pi_equivalent
#print axioms SemanticSubstitution.reindex_sigma_equivalent
#print axioms SemanticSubstitution.pair
#print axioms SemanticSubstitution.instantiate
#print axioms SemanticTerm.of_equivalent
#print axioms SemanticTerm.subst
#print axioms RegularHasType.subject_ne_u1
#print axioms no_regular_u1_term
#print axioms SemanticType.code_accessible
#print axioms SemanticType.code_constantFree
#print axioms SemanticType.of_semantic_conversion_iff
#print axioms SemanticType.subst_exists
#print axioms SemanticContext.syntax_constantFree
#print axioms SemanticContext.lookup_exists
#print axioms semantic_u0_pi
#print axioms semantic_u0_sigma
#print axioms semantic_u0_identity
#print axioms semantic_one_u0_context
#print axioms hidden_semantic_pi_has_pi_meaning
#print axioms omega_has_no_semantic_type
#print axioms erasing_omega_has_no_semantic_type

end Mettapedia.Languages.MeTTa.PureKernel.PresentationBoundary
