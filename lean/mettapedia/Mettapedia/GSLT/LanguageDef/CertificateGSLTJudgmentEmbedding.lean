import Mettapedia.GSLT.LanguageDef.CertificateGSLTInterpretation

/-!
# Proof-relevant embeddings between ground CertificateGSLT judgments

`CertificateGSLT.Interpretation` changes derivations while retaining one
common ground-judgment representation.  This module adds the next exact
layer: a source judgment may be embedded into a different target judgment.
Every primitive source rule application is implemented by a target open
derivation from the pointwise embedded, ordered premise occurrences.

The judgment map is required to be injective.  This is not a convenience:
the generated native checker retains a certificate conclusion and compares it
with the submitted claim.  A non-injective map could make that comparison
succeed after translation when it failed at the source, so exact authority
replay would be impossible.

This is deliberately the ground action of a future binding-signature
translation.  It does not claim that an arbitrary embedding of closed
`Pattern` judgments preserves ABT constructors or substitution.  Those laws
belong to the upstream presentation morphism that induces this layer.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.CertificateGSLT

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.InferenceChecker

/-- Preserve one ordered occurrence position under pointwise judgment
embedding. -/
def mapIndex (embedding : Pattern → Pattern) {judgments : List Pattern}
    (index : Fin judgments.length) :
    Fin (judgments.map embedding).length :=
  ⟨index.val, by simp only [List.length_map]; exact index.isLt⟩

@[simp] theorem mapIndex_val (embedding : Pattern → Pattern)
    {judgments : List Pattern} (index : Fin judgments.length) :
    (mapIndex embedding index).val = index.val :=
  rfl

@[simp] theorem get_mapIndex (embedding : Pattern → Pattern)
    {judgments : List Pattern} (index : Fin judgments.length) :
    (judgments.map embedding).get (mapIndex embedding index) =
      embedding (judgments.get index) := by
  simp [mapIndex]

/-- A proof-relevant embedding changes ground judgments without collapsing
them and maps each source rule to a target derivation with exactly the mapped
premise occurrences. -/
structure JudgmentEmbedding (source target : Object) where
  mapClaim : Pattern → Pattern
  mapClaim_injective : Function.Injective mapClaim
  onRule :
    ∀ (ruleInstance : RuleInstance) {premises : List Pattern}
      {conclusion : Pattern},
      RuleApplication source.definition ruleInstance premises conclusion →
        OpenDerivation target.definition (premises.map mapClaim)
          (mapClaim conclusion)

namespace JudgmentEmbedding

/-- Transport only the goal index of an open derivation. -/
def castGoal {definition : ValidatedCalculusLanguageDef}
    {context : List Pattern} {left right : Pattern}
    (equality : left = right)
    (derivation : OpenDerivation definition context left) :
    OpenDerivation definition context right :=
  equality ▸ derivation

@[simp] theorem castGoal_rfl
    {definition : ValidatedCalculusLanguageDef}
    {context : List Pattern} {goal : Pattern}
    (derivation : OpenDerivation definition context goal) :
    castGoal rfl derivation = derivation :=
  rfl

/-- Goal transport commutes with plugging proof holes. -/
theorem castGoal_bind
    {definition : ValidatedCalculusLanguageDef}
    {sourceContext targetContext : List Pattern}
    {left right : Pattern} (equality : left = right)
    (derivation : OpenDerivation definition sourceContext left)
    (environment :
      OpenDerivationList definition targetContext sourceContext) :
    (castGoal equality derivation).bind environment =
      castGoal equality (derivation.bind environment) := by
  cases equality
  rfl

mutual

/-- Recursively translate an open derivation.  Assumption positions are
retained, while rule nodes are replaced by their authored target templates. -/
def mapOpen {source target : Object}
    (embedding : JudgmentEmbedding source target)
    {context : List Pattern} {goal : Pattern} :
    OpenDerivation source.definition context goal →
      OpenDerivation target.definition (context.map embedding.mapClaim)
        (embedding.mapClaim goal)
  | .assumption index => by
      exact castGoal (get_mapIndex embedding.mapClaim index)
        (OpenDerivation.assumption
          (definition := target.definition)
          (mapIndex embedding.mapClaim index))
  | .byRule ruleInstance application children =>
      (embedding.onRule ruleInstance application).bind
        (mapOpenList embedding children)

/-- Translate an ordered vector of open derivations pointwise. -/
def mapOpenList {source target : Object}
    (embedding : JudgmentEmbedding source target)
    {context goals : List Pattern} :
    OpenDerivationList source.definition context goals →
      OpenDerivationList target.definition
        (context.map embedding.mapClaim) (goals.map embedding.mapClaim)
  | .nil => .nil
  | .cons head tail =>
      .cons (mapOpen embedding head) (mapOpenList embedding tail)

end

/-- Position lookup commutes with pointwise derivation translation. -/
theorem mapOpenList_get {source target : Object}
    (embedding : JudgmentEmbedding source target)
    {context goals : List Pattern}
    (derivations : OpenDerivationList source.definition context goals)
    (index : Fin goals.length) :
    castGoal (get_mapIndex embedding.mapClaim index)
        ((embedding.mapOpenList derivations).get
          (mapIndex embedding.mapClaim index)) =
      embedding.mapOpen (derivations.get index) := by
  cases derivations with
  | nil => exact Fin.elim0 index
  | cons head tail =>
      refine Fin.cases ?_ (fun tailIndex => ?_) index
      · rfl
      · exact mapOpenList_get embedding tail tailIndex

mutual

/-- Ground-judgment translation is natural with respect to plugging premise
derivations into proof holes. -/
theorem mapOpen_bind {source target : Object}
    (embedding : JudgmentEmbedding source target)
    {sourceContext targetContext : List Pattern} {goal : Pattern}
    (derivation :
      OpenDerivation source.definition sourceContext goal)
    (environment :
      OpenDerivationList source.definition targetContext sourceContext) :
    embedding.mapOpen (derivation.bind environment) =
      (embedding.mapOpen derivation).bind
        (embedding.mapOpenList environment) := by
  cases derivation with
  | assumption index =>
      simp only [OpenDerivation.bind, mapOpen, castGoal_bind]
      exact (mapOpenList_get embedding environment index).symm
  | byRule ruleInstance application children =>
      simp only [OpenDerivation.bind, mapOpen]
      rw [OpenDerivation.bind_assoc]
      congr 1
      exact mapOpenList_bind embedding children environment

/-- Naturality under proof-hole substitution holds pointwise for ordered
derivation vectors. -/
theorem mapOpenList_bind {source target : Object}
    (embedding : JudgmentEmbedding source target)
    {sourceContext targetContext goals : List Pattern}
    (derivations :
      OpenDerivationList source.definition sourceContext goals)
    (environment :
      OpenDerivationList source.definition targetContext sourceContext) :
    embedding.mapOpenList (derivations.bind environment) =
      (embedding.mapOpenList derivations).bind
        (embedding.mapOpenList environment) := by
  cases derivations with
  | nil => rfl
  | cons head tail =>
      simp only [OpenDerivationList.bind, mapOpenList]
      rw [mapOpen_bind embedding head environment,
        mapOpenList_bind embedding tail environment]

end


/-- Identity embeds every judgment and realizes each rule by one target rule
node with a distinct hole for every ordered premise occurrence. -/
def identity (object : Object) : JudgmentEmbedding object object where
  mapClaim := id
  mapClaim_injective := fun _ _ equality => equality
  onRule := by
    intro ruleInstance premises conclusion application
    simpa using
      (OpenDerivation.byRule ruleInstance application
        (assumptionEnvironment object.definition premises))

/-- Compose ground-judgment embeddings and recursively translate the earlier
rule implementation through the later one. -/
def comp {first middle last : Object}
    (earlier : JudgmentEmbedding first middle)
    (later : JudgmentEmbedding middle last) :
    JudgmentEmbedding first last where
  mapClaim := fun claim => later.mapClaim (earlier.mapClaim claim)
  mapClaim_injective :=
    later.mapClaim_injective.comp earlier.mapClaim_injective
  onRule := by
    intro ruleInstance premises conclusion application
    simpa only [List.map_map, Function.comp_def] using
      later.mapOpen (earlier.onRule ruleInstance application)

/-- A common-judgment interpretation is the identity-claim special case. -/
def ofInterpretation {source target : Object}
    (interpretation : Interpretation source target) :
    JudgmentEmbedding source target where
  mapClaim := id
  mapClaim_injective := fun _ _ equality => equality
  onRule := by
    intro ruleInstance premises conclusion application
    simpa using interpretation.onRule ruleInstance application

/-! ## Closed derivations -/

/-- Translate a closed derivation and its conclusion. -/
def mapDerivation {source target : Object}
    (embedding : JudgmentEmbedding source target) {goal : Pattern}
    (derivation : Derivation source.definition goal) :
    Derivation target.definition (embedding.mapClaim goal) :=
  (embedding.mapOpen
    (OpenDerivation.ofClosed (context := []) derivation)).close

/-! ## Positive and negative structural facts -/

/-- Exact claim equality is both preserved and reflected by a judgment
embedding. -/
theorem mapClaim_eq_iff {source target : Object}
    (embedding : JudgmentEmbedding source target)
    (left right : Pattern) :
    embedding.mapClaim left = embedding.mapClaim right ↔ left = right := by
  constructor
  · intro equality
    exact embedding.mapClaim_injective equality
  · intro equality
    exact congrArg embedding.mapClaim equality

/-- A constant claim map cannot underlie an exact judgment embedding when the
source has two distinguishable judgments. -/
theorem no_constant_embedding {source target : Object}
    (embedding : JudgmentEmbedding source target)
    {left right : Pattern} (different : left ≠ right)
    (constant : embedding.mapClaim left = embedding.mapClaim right) : False :=
  different (embedding.mapClaim_injective constant)

#print axioms mapOpen_bind
#print axioms mapOpenList_bind
#print axioms mapClaim_eq_iff
#print axioms no_constant_embedding

end JudgmentEmbedding

end Mettapedia.GSLT.LanguageDef.CertificateGSLT
