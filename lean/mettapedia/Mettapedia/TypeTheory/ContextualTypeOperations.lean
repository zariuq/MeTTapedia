import Mettapedia.TypeTheory.ContextualSumComparison
import Mettapedia.TypeTheory.ContextualIdentitySubstitution
import Mettapedia.GSLT.Core.ContextualTypeReindexing

/-!
# Raw dependent type operations and their separate contextual laws

The operation records contain no qualification proofs. Products, sums and
identity elimination retain the exact context and motive types of the
existing qualified interfaces. The identity-context reindex map is explicit
raw data; its endpoint, witness and reflexivity equations are separate laws.

The substitution predicates named `Strict` compare selected type objects by
equality and terms by heterogeneous equality. They describe that class of
representatives, not every possible interpretation up to equivalence.
No semantic eta, endpoint reflection, proof irrelevance, universe hierarchy,
native interpretation or evaluation strategy is required by these records.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.ContextualTypeOperations

open Mettapedia.GSLT.Core.ContextualLadder
open ContextualProductComparison (selfExtend)
open ContextualIdentityTypes (secondEndpointType endpointPairContext endpointType
  leftEndpoint rightEndpoint endpointDiagonal)

universe u v w w'

/-! ## Raw operation data -/

structure PiOperations (C : Cwf.{u, v, w, w'}) where
  pi : {context : C.Ctx} →
    (domain : C.Ty context) → C.Ty (C.ext context domain) → C.Ty context
  lam : {context : C.Ctx} → {domain : C.Ty context} →
    {codomain : C.Ty (C.ext context domain)} →
    C.Tm (C.ext context domain) codomain → C.Tm context (pi domain codomain)
  app : {context : C.Ctx} → {domain : C.Ty context} →
    {codomain : C.Ty (C.ext context domain)} → C.Tm context (pi domain codomain) →
    (argument : C.Tm context domain) →
    C.Tm context (C.tySub codomain (selfExtend C argument))

structure SigmaOperations (C : Cwf.{u, v, w, w'}) where
  sigma : {context : C.Ctx} →
    (domain : C.Ty context) → C.Ty (C.ext context domain) → C.Ty context
  pair : {context : C.Ctx} → {domain : C.Ty context} →
    {codomain : C.Ty (C.ext context domain)} → (first : C.Tm context domain) →
    C.Tm context (C.tySub codomain (selfExtend C first)) →
    C.Tm context (sigma domain codomain)
  fst : {context : C.Ctx} → {domain : C.Ty context} →
    {codomain : C.Ty (C.ext context domain)} →
    C.Tm context (sigma domain codomain) → C.Tm context domain
  snd : {context : C.Ctx} → {domain : C.Ty context} →
    {codomain : C.Ty (C.ext context domain)} →
    (value : C.Tm context (sigma domain codomain)) →
    C.Tm context (C.tySub codomain (selfExtend C (fst value)))

structure IdentityFormationOperations (C : Cwf.{u, v, w, w'}) where
  idTy : {context : C.Ctx} → (type : C.Ty context) →
    C.Tm context type → C.Tm context type → C.Ty context

variable {C : Cwf.{u, v, w, w'}}

namespace IdentityFormationOperations

def witnessType (identity : IdentityFormationOperations C)
    {context : C.Ctx} (type : C.Ty context) : C.Ty (endpointPairContext C type) :=
  identity.idTy (endpointType C type) (leftEndpoint C type) (rightEndpoint C type)

/-- The same two-endpoint-and-witness context, without a formation-law field. -/
def identityContext (identity : IdentityFormationOperations C)
    {context : C.Ctx} (type : C.Ty context) : C.Ctx :=
  C.ext (endpointPairContext C type) (identity.witnessType type)

def baseProjection (identity : IdentityFormationOperations C)
    {context : C.Ctx} (type : C.Ty context) : C.Sub (identity.identityContext type) context :=
  C.compS (C.wk type)
    (C.compS (C.wk (secondEndpointType C type)) (C.wk (identity.witnessType type)))

def leftAt (identity : IdentityFormationOperations C)
    {context : C.Ctx} (type : C.Ty context) :
    C.Tm (identity.identityContext type)
      (C.tySub (endpointType C type) (C.wk (identity.witnessType type))) :=
  C.tmSub (leftEndpoint C type) (C.wk (identity.witnessType type))

def rightAt (identity : IdentityFormationOperations C)
    {context : C.Ctx} (type : C.Ty context) :
    C.Tm (identity.identityContext type)
      (C.tySub (endpointType C type) (C.wk (identity.witnessType type))) :=
  C.tmSub (rightEndpoint C type) (C.wk (identity.witnessType type))

end IdentityFormationOperations

structure IdentityReflexivityOperations (identity : IdentityFormationOperations C) where
  refl : {context : C.Ctx} → {type : C.Ty context} → (term : C.Tm context type) →
    C.Tm context (identity.idTy type term term)

structure IdentityEliminationOperations (identity : IdentityFormationOperations C) where
  reflexivitySubstitution : {context : C.Ctx} → (type : C.Ty context) →
    C.Sub (C.ext context type) (identity.identityContext type)
  j : {context : C.Ctx} → {type : C.Ty context} →
    (motive : C.Ty (identity.identityContext type)) →
    C.Tm (C.ext context type) (C.tySub motive (reflexivitySubstitution type)) →
    C.Tm (identity.identityContext type) motive

/-- A scoped map, not a claim that it respects any retained field. -/
structure IdentityReindexing (identity : IdentityFormationOperations C) where
  map : {source target : C.Ctx} → (substitution : C.Sub source target) →
    (type : C.Ty target) →
    C.Sub (identity.identityContext (C.tySub type substitution)) (identity.identityContext type)

structure IdentityOperations (C : Cwf.{u, v, w, w'}) where
  formation : IdentityFormationOperations C
  reflexivity : IdentityReflexivityOperations formation
  elimination : IdentityEliminationOperations formation
  reindexing : IdentityReindexing formation

/-- All raw constructor data use one supplied contextual core. -/
structure Operations (C : Cwf.{u, v, w, w'}) where
  products : PiOperations C
  sums : SigmaOperations C
  identity : IdentityOperations C

/-! ## Beta and identity-boundary predicates -/

def PiBeta (products : PiOperations C) : Prop :=
  ∀ {context : C.Ctx} {domain : C.Ty context} {codomain : C.Ty (C.ext context domain)}
    (body : C.Tm (C.ext context domain) codomain) (argument : C.Tm context domain),
    products.app (products.lam body) argument = C.tmSub body (selfExtend C argument)

def SigmaBeta (sums : SigmaOperations C) : Prop :=
  (∀ {context : C.Ctx} {domain : C.Ty context} {codomain : C.Ty (C.ext context domain)}
    (first : C.Tm context domain) (second : C.Tm context (C.tySub codomain (selfExtend C first))),
    sums.fst (sums.pair first second) = first) ∧
  (∀ {context : C.Ctx} {domain : C.Ty context} {codomain : C.Ty (C.ext context domain)}
    (first : C.Tm context domain) (second : C.Tm context (C.tySub codomain (selfExtend C first))),
    HEq (sums.snd (sums.pair first second)) second)

def IdentityBoundary {identity : IdentityFormationOperations C}
    (reflexivity : IdentityReflexivityOperations identity)
    (elimination : IdentityEliminationOperations identity) : Prop :=
  (∀ {context : C.Ctx} (type : C.Ty context),
    C.compS (C.wk (identity.witnessType type)) (elimination.reflexivitySubstitution type) =
      endpointDiagonal C type) ∧
  (∀ {context : C.Ctx} (type : C.Ty context),
    HEq (C.tmSub (C.vz (identity.witnessType type)) (elimination.reflexivitySubstitution type))
      (reflexivity.refl (C.vz type)))

def IdentityBeta {identity : IdentityFormationOperations C}
    (elimination : IdentityEliminationOperations identity) : Prop :=
  ∀ {context : C.Ctx} {type : C.Ty context}
    (motive : C.Ty (identity.identityContext type))
    (base : C.Tm (C.ext context type)
      (C.tySub motive (elimination.reflexivitySubstitution type))),
    C.tmSub (elimination.j motive base) (elimination.reflexivitySubstitution type) = base

/-! ## Strict contextual substitution predicates -/

/-- The supplied representatives must agree as CwF type objects. A model
whose products commute with substitution only up to equivalence has a
different, weaker comparison interface. -/
def StrictPiFormationSubstitution (products : PiOperations C) : Prop :=
  ∀ {source target : C.Ctx} (substitution : C.Sub source target)
    (domain : C.Ty target) (codomain : C.Ty (C.ext target domain)),
    C.tySub (products.pi domain codomain) substitution =
      products.pi (C.tySub domain substitution)
        (C.tySub codomain (TypeOver.extensionSubstitution substitution domain))

def StrictPiSubstitution (products : PiOperations C) : Prop :=
  StrictPiFormationSubstitution products ∧
  (∀ {source target : C.Ctx} (substitution : C.Sub source target)
    {domain : C.Ty target} {codomain : C.Ty (C.ext target domain)}
    (body : C.Tm (C.ext target domain) codomain),
    HEq (C.tmSub (products.lam body) substitution)
      (products.lam (C.tmSub body (TypeOver.extensionSubstitution substitution domain)))) ∧
  (∀ {source target : C.Ctx} (substitution : C.Sub source target)
    {domain : C.Ty target} {codomain : C.Ty (C.ext target domain)}
    (function : C.Tm target (products.pi domain codomain)) (argument : C.Tm target domain)
    (reindexedFunction : C.Tm source (products.pi (C.tySub domain substitution)
      (C.tySub codomain (TypeOver.extensionSubstitution substitution domain)))),
    HEq (C.tmSub function substitution) reindexedFunction →
    HEq (C.tmSub (products.app function argument) substitution)
      (products.app reindexedFunction (C.tmSub argument substitution)))

def StrictSigmaFormationSubstitution (sums : SigmaOperations C) : Prop :=
  ∀ {source target : C.Ctx} (substitution : C.Sub source target)
    (domain : C.Ty target) (codomain : C.Ty (C.ext target domain)),
    C.tySub (sums.sigma domain codomain) substitution =
      sums.sigma (C.tySub domain substitution)
        (C.tySub codomain (TypeOver.extensionSubstitution substitution domain))

def StrictSigmaSubstitution (sums : SigmaOperations C) : Prop :=
  StrictSigmaFormationSubstitution sums ∧
  (∀ {source target : C.Ctx} (substitution : C.Sub source target)
    {domain : C.Ty target} {codomain : C.Ty (C.ext target domain)}
    (first : C.Tm target domain)
    (second : C.Tm target (C.tySub codomain (selfExtend C first)))
    (reindexedSecond : C.Tm source
      (C.tySub (C.tySub codomain (TypeOver.extensionSubstitution substitution domain))
        (selfExtend C (C.tmSub first substitution)))),
    HEq (C.tmSub second substitution) reindexedSecond →
    HEq (C.tmSub (sums.pair first second) substitution)
      (sums.pair (C.tmSub first substitution) reindexedSecond)) ∧
  (∀ {source target : C.Ctx} (substitution : C.Sub source target)
    {domain : C.Ty target} {codomain : C.Ty (C.ext target domain)}
    (value : C.Tm target (sums.sigma domain codomain))
    (reindexedValue : C.Tm source (sums.sigma (C.tySub domain substitution)
      (C.tySub codomain (TypeOver.extensionSubstitution substitution domain)))),
    HEq (C.tmSub value substitution) reindexedValue →
      HEq (C.tmSub (sums.fst value) substitution) (sums.fst reindexedValue) ∧
      HEq (C.tmSub (sums.snd value) substitution) (sums.snd reindexedValue))

def StrictIdentityFormationSubstitution (identity : IdentityFormationOperations C) : Prop :=
  ∀ {source target : C.Ctx} (substitution : C.Sub source target)
    (type : C.Ty target) (left right : C.Tm target type),
    C.tySub (identity.idTy type left right) substitution =
      identity.idTy (C.tySub type substitution)
        (C.tmSub left substitution) (C.tmSub right substitution)

def StrictReflexivitySubstitution {identity : IdentityFormationOperations C}
    (reflexivity : IdentityReflexivityOperations identity) : Prop :=
  ∀ {source target : C.Ctx} (substitution : C.Sub source target)
    {type : C.Ty target} (term : C.Tm target type),
    HEq (C.tmSub (reflexivity.refl term) substitution)
      (reflexivity.refl (C.tmSub term substitution))

def ReflexivityReindexSquare {identity : IdentityFormationOperations C}
    (elimination : IdentityEliminationOperations identity)
    (reindexing : IdentityReindexing identity) : Prop :=
  ∀ {source target : C.Ctx} (substitution : C.Sub source target) (type : C.Ty target),
    C.compS (reindexing.map substitution type)
        (elimination.reflexivitySubstitution (C.tySub type substitution)) =
      C.compS (elimination.reflexivitySubstitution type)
        (TypeOver.extensionSubstitution substitution type)

/-- Every retained field of the full identity context is constrained. The
last clause is the square needed to reindex an arbitrary J base section. -/
def StrictIdentityReindexing {identity : IdentityFormationOperations C}
    (elimination : IdentityEliminationOperations identity)
    (reindexing : IdentityReindexing identity) : Prop :=
  (∀ {source target : C.Ctx} (substitution : C.Sub source target) (type : C.Ty target),
    C.compS (identity.baseProjection type) (reindexing.map substitution type) =
      C.compS substitution (identity.baseProjection (C.tySub type substitution))) ∧
  (∀ {source target : C.Ctx} (substitution : C.Sub source target) (type : C.Ty target),
    HEq (C.tmSub (identity.leftAt type) (reindexing.map substitution type))
        (identity.leftAt (C.tySub type substitution)) ∧
      HEq (C.tmSub (identity.rightAt type) (reindexing.map substitution type))
        (identity.rightAt (C.tySub type substitution)) ∧
      HEq (C.tmSub (C.vz (identity.witnessType type)) (reindexing.map substitution type))
        (C.vz (identity.witnessType (C.tySub type substitution)))) ∧
  ReflexivityReindexSquare elimination reindexing

/-- Full motives range over both endpoints and their witness. The HEq
premise names only the necessary transport of the base section; its
existence follows from the separately stated reflexivity square below. -/
def StrictJSubstitution {identity : IdentityFormationOperations C}
    (elimination : IdentityEliminationOperations identity)
    (reindexing : IdentityReindexing identity) : Prop :=
  ∀ {source target : C.Ctx} (substitution : C.Sub source target) (type : C.Ty target)
    (motive : C.Ty (identity.identityContext type))
    (base : C.Tm (C.ext target type)
      (C.tySub motive (elimination.reflexivitySubstitution type)))
    (reindexedBase : C.Tm (C.ext source (C.tySub type substitution))
      (C.tySub (C.tySub motive (reindexing.map substitution type))
        (elimination.reflexivitySubstitution (C.tySub type substitution)))),
    HEq (C.tmSub base (TypeOver.extensionSubstitution substitution type)) reindexedBase →
    HEq (C.tmSub (elimination.j motive base) (reindexing.map substitution type))
      (elimination.j (C.tySub motive (reindexing.map substitution type)) reindexedBase)

/-! ## Erasure of existing qualified interfaces -/

def PiOperations.ofQualified (products : ContextualProductComparison.DependentProductBeta C) :
    PiOperations C where
  pi := products.pi
  lam := products.lam
  app := products.app

theorem PiOperations.ofQualified_beta (products : ContextualProductComparison.DependentProductBeta C) :
    PiBeta (PiOperations.ofQualified products) := products.beta

def SigmaOperations.ofQualified (sums : ContextualSumComparison.DependentSumBeta C) :
    SigmaOperations C where
  sigma := sums.sigma
  pair := sums.pair
  fst := sums.fst
  snd := sums.snd

theorem SigmaOperations.ofQualified_beta (sums : ContextualSumComparison.DependentSumBeta C) :
    SigmaBeta (SigmaOperations.ofQualified sums) := ⟨sums.fst_pair, sums.snd_pair⟩

def IdentityFormationOperations.ofQualified (identity : ContextualIdentityTypes.IdentityFormation C) :
    IdentityFormationOperations C where
  idTy := identity.idTy

theorem IdentityFormationOperations.ofQualified_substitution
    (identity : ContextualIdentityTypes.IdentityFormation C) :
    StrictIdentityFormationSubstitution (IdentityFormationOperations.ofQualified identity) :=
  identity.idTy_sub

def IdentityReflexivityOperations.ofQualified {identity : ContextualIdentityTypes.IdentityFormation C}
    (reflexivity : ContextualIdentityTypes.IdentityReflexivity C identity) :
    IdentityReflexivityOperations (IdentityFormationOperations.ofQualified identity) where
  refl := reflexivity.refl

theorem IdentityReflexivityOperations.ofQualified_substitution
    {identity : ContextualIdentityTypes.IdentityFormation C}
    (reflexivity : ContextualIdentityTypes.IdentityReflexivity C identity) :
    StrictReflexivitySubstitution (IdentityReflexivityOperations.ofQualified reflexivity) :=
  reflexivity.refl_sub

def IdentityEliminationOperations.ofQualified {identity : ContextualIdentityTypes.IdentityFormation C}
    {reflexivity : ContextualIdentityTypes.IdentityReflexivity C identity}
    (elimination : ContextualIdentityTypes.IdentityEliminationBeta C identity reflexivity) :
    IdentityEliminationOperations (IdentityFormationOperations.ofQualified identity) where
  reflexivitySubstitution := elimination.reflexivitySubstitution
  j := elimination.j

theorem IdentityEliminationOperations.ofQualified_boundary
    {identity : ContextualIdentityTypes.IdentityFormation C}
    {reflexivity : ContextualIdentityTypes.IdentityReflexivity C identity}
    (elimination : ContextualIdentityTypes.IdentityEliminationBeta C identity reflexivity) :
    IdentityBoundary (IdentityReflexivityOperations.ofQualified reflexivity)
      (IdentityEliminationOperations.ofQualified elimination) :=
  ⟨elimination.over_diagonal, elimination.witness_is_refl⟩

theorem IdentityEliminationOperations.ofQualified_beta
    {identity : ContextualIdentityTypes.IdentityFormation C}
    {reflexivity : ContextualIdentityTypes.IdentityReflexivity C identity}
    (elimination : ContextualIdentityTypes.IdentityEliminationBeta C identity reflexivity) :
    IdentityBeta (IdentityEliminationOperations.ofQualified elimination) := elimination.beta

/-! ## Transport and the full-motive substitution/beta consequence -/

private theorem transported_heq {index : Sort u} {family : index → Sort v}
    {first second : index} (equal : first = second) (value : family first) :
    HEq (equal ▸ value) value := by
  cases equal
  rfl

theorem wk_selfExtend {context : C.Ctx} {type : C.Ty context}
    (argument : C.Tm context type) :
    C.compS (C.wk type) (selfExtend C argument) = C.idS context :=
  C.wk_pair _ _ _

theorem vz_selfExtend {context : C.Ctx} {type : C.Ty context}
    (argument : C.Tm context type) :
    HEq (C.tmSub (C.vz type) (selfExtend C argument)) argument :=
  (heq_of_eq (C.vz_pair _ _ _)).trans
    ((cast_heq _ _).trans (transported_heq (C.tySub_id type).symm argument))

/-- The dependent argument/comprehension square follows from the CwF laws;
it is not an extra axiom for the selected Pi or Sigma operation. -/
theorem selfExtend_substitution {source target : C.Ctx}
    (substitution : C.Sub source target) {type : C.Ty target} (argument : C.Tm target type) :
    C.compS (TypeOver.extensionSubstitution substitution type)
        (selfExtend C (C.tmSub argument substitution)) =
      C.compS (selfExtend C argument) substitution := by
  apply TypeOver.substitution_ext
  · rw [← C.comp_assoc, TypeOver.wk_extensionSubstitution, C.comp_assoc,
      wk_selfExtend, C.comp_id, ← C.comp_assoc, wk_selfExtend, C.id_comp]
  · have extensionTypes :
        C.tySub (C.tySub type (C.wk type)) (TypeOver.extensionSubstitution substitution type) =
          C.tySub (C.tySub type substitution) (C.wk (C.tySub type substitution)) := by
      rw [← C.tySub_comp, TypeOver.wk_extensionSubstitution, C.tySub_comp]
    have argumentTypes : C.tySub (C.tySub type (C.wk type)) (selfExtend C argument) = type := by
      rw [← C.tySub_comp, wk_selfExtend, C.tySub_id]
    have left :=
      (TypeOver.tmSub_comp_heq (C.vz type) (TypeOver.extensionSubstitution substitution type)
        (selfExtend C (C.tmSub argument substitution))).trans
      ((TypeOver.tmSub_heq extensionTypes (TypeOver.vz_extensionSubstitution substitution type)
        (selfExtend C (C.tmSub argument substitution))).trans
        (vz_selfExtend (C.tmSub argument substitution)))
    have right := (TypeOver.tmSub_comp_heq (C.vz type) (selfExtend C argument) substitution).trans
      (TypeOver.tmSub_heq argumentTypes (vz_selfExtend argument) substitution)
    exact left.trans right.symm

/-- Strict formation supplies the function transport required by the
application clause; its HEq premise cannot lose admitted functions. -/
def reindexFunction (products : PiOperations C)
    (formed : StrictPiFormationSubstitution products)
    {source target : C.Ctx} (substitution : C.Sub source target)
    {domain : C.Ty target} {codomain : C.Ty (C.ext target domain)}
    (function : C.Tm target (products.pi domain codomain)) :
    C.Tm source (products.pi (C.tySub domain substitution)
      (C.tySub codomain (TypeOver.extensionSubstitution substitution domain))) :=
  cast (congrArg (C.Tm source) (formed substitution domain codomain))
    (C.tmSub function substitution)

theorem reindexFunction_heq (products : PiOperations C)
    (formed : StrictPiFormationSubstitution products)
    {source target : C.Ctx} (substitution : C.Sub source target)
    {domain : C.Ty target} {codomain : C.Ty (C.ext target domain)}
    (function : C.Tm target (products.pi domain codomain)) :
    HEq (reindexFunction products formed substitution function) (C.tmSub function substitution) :=
  cast_heq _ _

/-- The second member of a dependent pair has its required reindexed type
by the argument/comprehension square. No type-family collapse is used. -/
def reindexPairSecond {source target : C.Ctx} (substitution : C.Sub source target)
    {domain : C.Ty target} {codomain : C.Ty (C.ext target domain)}
    (first : C.Tm target domain) (second : C.Tm target (C.tySub codomain (selfExtend C first))) :
    C.Tm source (C.tySub (C.tySub codomain (TypeOver.extensionSubstitution substitution domain))
      (selfExtend C (C.tmSub first substitution))) :=
  cast (by rw [← C.tySub_comp, ← selfExtend_substitution substitution first, C.tySub_comp])
    (C.tmSub second substitution)

theorem reindexPairSecond_heq {source target : C.Ctx} (substitution : C.Sub source target)
    {domain : C.Ty target} {codomain : C.Ty (C.ext target domain)}
    (first : C.Tm target domain) (second : C.Tm target (C.tySub codomain (selfExtend C first))) :
    HEq (reindexPairSecond substitution first second) (C.tmSub second substitution) :=
  cast_heq _ _

/-- The reflexivity square and the CwF substitution law determine the type
transport of the base section. No new type-former coherence is assumed. -/
def reindexBase {identity : IdentityFormationOperations C}
    (elimination : IdentityEliminationOperations identity)
    (reindexing : IdentityReindexing identity)
    (square : ReflexivityReindexSquare elimination reindexing)
    {source target : C.Ctx} (substitution : C.Sub source target) (type : C.Ty target)
    (motive : C.Ty (identity.identityContext type))
    (base : C.Tm (C.ext target type)
      (C.tySub motive (elimination.reflexivitySubstitution type))) :
    C.Tm (C.ext source (C.tySub type substitution))
      (C.tySub (C.tySub motive (reindexing.map substitution type))
        (elimination.reflexivitySubstitution (C.tySub type substitution))) :=
  cast (by rw [← C.tySub_comp, ← square substitution type, C.tySub_comp])
    (C.tmSub base (TypeOver.extensionSubstitution substitution type))

theorem reindexBase_heq {identity : IdentityFormationOperations C}
    (elimination : IdentityEliminationOperations identity)
    (reindexing : IdentityReindexing identity)
    (square : ReflexivityReindexSquare elimination reindexing)
    {source target : C.Ctx} (substitution : C.Sub source target) (type : C.Ty target)
    (motive : C.Ty (identity.identityContext type))
    (base : C.Tm (C.ext target type)
      (C.tySub motive (elimination.reflexivitySubstitution type))) :
    HEq (reindexBase elimination reindexing square substitution type motive base)
      (C.tmSub base (TypeOver.extensionSubstitution substitution type)) := cast_heq _ _

/-- Reindex full J, then restrict to the reindexed reflexivity boundary.
This composed equality follows from the separate J-substitution and beta
laws, with the base transported by the already proved contextual square. -/
theorem j_beta_substitution {identity : IdentityFormationOperations C}
    (elimination : IdentityEliminationOperations identity)
    (reindexing : IdentityReindexing identity)
    (square : ReflexivityReindexSquare elimination reindexing)
    (stable : StrictJSubstitution elimination reindexing) (beta : IdentityBeta elimination)
    {source target : C.Ctx} (substitution : C.Sub source target) (type : C.Ty target)
    (motive : C.Ty (identity.identityContext type))
    (base : C.Tm (C.ext target type)
      (C.tySub motive (elimination.reflexivitySubstitution type))) :
    C.tmSub (C.tmSub (elimination.j motive base) (reindexing.map substitution type))
        (elimination.reflexivitySubstitution (C.tySub type substitution)) =
      reindexBase elimination reindexing square substitution type motive base := by
  have commute := eq_of_heq (stable substitution type motive base _
    (reindexBase_heq elimination reindexing square substitution type motive base).symm)
  rw [commute]
  exact beta _ _

/-! ## Actual set-family operations and their laws -/

def BetaLaws (operations : Operations C) : Prop :=
  PiBeta operations.products ∧ SigmaBeta operations.sums ∧
    IdentityBoundary operations.identity.reflexivity operations.identity.elimination ∧
    IdentityBeta operations.identity.elimination

def StrictSubstitutionLaws (operations : Operations C) : Prop :=
  StrictPiSubstitution operations.products ∧ StrictSigmaSubstitution operations.sums ∧
    StrictIdentityFormationSubstitution operations.identity.formation ∧
    StrictReflexivitySubstitution operations.identity.reflexivity ∧
    StrictIdentityReindexing operations.identity.elimination operations.identity.reindexing ∧
    StrictJSubstitution operations.identity.elimination operations.identity.reindexing

namespace Families

def products : PiOperations (familiesCwf.{w}) :=
  PiOperations.ofQualified ContextualProductComparison.familiesProducts

def sums : SigmaOperations (familiesCwf.{w}) :=
  SigmaOperations.ofQualified ContextualSumComparison.familiesSums

def formation : IdentityFormationOperations (familiesCwf.{w}) :=
  IdentityFormationOperations.ofQualified ContextualIdentityTypes.Families.identityFormation

def reflexivity : IdentityReflexivityOperations formation.{w} :=
  IdentityReflexivityOperations.ofQualified ContextualIdentityTypes.Families.identityReflexivity

def elimination : IdentityEliminationOperations formation.{w} :=
  IdentityEliminationOperations.ofQualified ContextualIdentityTypes.Families.identityElimination

def reindexing : IdentityReindexing formation.{w} where
  map := ContextualIdentitySubstitution.identityReindex

def identity : IdentityOperations (familiesCwf.{w}) where
  formation := formation
  reflexivity := reflexivity
  elimination := elimination
  reindexing := reindexing

def operations : Operations (familiesCwf.{w}) where
  products := products
  sums := sums
  identity := identity

theorem products_substitution : StrictPiSubstitution products.{w} := by
  refine ⟨?_, ?_, ?_⟩
  · intro source target substitution domain codomain
    rfl
  · intro source target substitution domain codomain body
    rfl
  · intro source target substitution domain codomain function argument reindexedFunction same
    have equal : (familiesCwf.{w}).tmSub function substitution = reindexedFunction := eq_of_heq same
    cases equal
    rfl

theorem sums_substitution : StrictSigmaSubstitution sums.{w} := by
  refine ⟨?_, ?_, ?_⟩
  · intro source target substitution domain codomain
    rfl
  · intro source target substitution domain codomain first second reindexedSecond same
    have equal : (familiesCwf.{w}).tmSub second substitution = reindexedSecond := eq_of_heq same
    cases equal
    rfl
  · intro source target substitution domain codomain value reindexedValue same
    have equal : (familiesCwf.{w}).tmSub value substitution = reindexedValue := eq_of_heq same
    cases equal
    exact ⟨HEq.rfl, HEq.rfl⟩

theorem identity_reindexing : StrictIdentityReindexing elimination.{w} reindexing := by
  refine ⟨?_, ?_, ?_⟩
  · intro source target substitution type
    rfl
  · intro source target substitution type
    exact ⟨HEq.rfl, HEq.rfl, HEq.rfl⟩
  · intro source target substitution type
    exact ContextualIdentitySubstitution.reflexivity_square substitution type

/-- This imports the proved full-motive equality-elimination naturality,
not merely the substitution laws for formation and reflexivity. -/
theorem j_substitution : StrictJSubstitution elimination.{w} reindexing := by
  intro source target substitution type motive base reindexedBase same
  have equal : (familiesCwf.{w}).tmSub base
      (TypeOver.extensionSubstitution substitution type) = reindexedBase := eq_of_heq same
  cases equal
  exact heq_of_eq (ContextualIdentitySubstitution.j_substitution substitution type motive base)

theorem beta_laws : BetaLaws operations.{w} :=
  ⟨PiOperations.ofQualified_beta ContextualProductComparison.familiesProducts,
    SigmaOperations.ofQualified_beta ContextualSumComparison.familiesSums,
    IdentityEliminationOperations.ofQualified_boundary
      ContextualIdentityTypes.Families.identityElimination,
    IdentityEliminationOperations.ofQualified_beta
      ContextualIdentityTypes.Families.identityElimination⟩

theorem substitution_laws : StrictSubstitutionLaws operations.{w} :=
  ⟨products_substitution, sums_substitution,
    IdentityFormationOperations.ofQualified_substitution
      ContextualIdentityTypes.Families.identityFormation,
    IdentityReflexivityOperations.ofQualified_substitution
      ContextualIdentityTypes.Families.identityReflexivity,
    identity_reindexing, j_substitution⟩

/-- The abstract composed law is inhabited for every full dependent motive
of the actual set-family construction, at any fixed host universe. -/
theorem full_motive_beta_square {source target : Type w}
    (substitution : source → target) (type : target → Type w)
    (motive : (familiesCwf.{w}).Ty (formation.identityContext type))
    (base : (familiesCwf.{w}).Tm ((familiesCwf.{w}).ext target type)
      ((familiesCwf.{w}).tySub motive (elimination.reflexivitySubstitution type))) :
    (familiesCwf.{w}).tmSub
        ((familiesCwf.{w}).tmSub (elimination.j motive base) (reindexing.map substitution type))
        (elimination.reflexivitySubstitution ((familiesCwf.{w}).tySub type substitution)) =
      reindexBase elimination reindexing identity_reindexing.2.2 substitution type motive base :=
  j_beta_substitution elimination reindexing identity_reindexing.2.2 j_substitution
    beta_laws.2.2.2 substitution type motive base

/-! ### A varying-fibre computation through the same operations -/

def varyingDomain : Nat → Type := fun context => Fin (context + 1)

def varyingCodomain : (familiesCwf.{0}).ext Nat varyingDomain → Type :=
  fun point => Fin (point.1 + point.2.val + 2)

def varyingBody : (familiesCwf.{0}).Tm ((familiesCwf.{0}).ext Nat varyingDomain) varyingCodomain :=
  fun point => ⟨point.2.val + 1, by omega⟩

def varyingArgument : (familiesCwf.{0}).Tm Nat varyingDomain :=
  fun context => ⟨context, Nat.lt_succ_self context⟩

def varyingFunction : (familiesCwf.{0}).Tm Nat (products.pi varyingDomain varyingCodomain) :=
  products.lam varyingBody

def varyingPair : (familiesCwf.{0}).Tm Nat (sums.sigma varyingDomain varyingCodomain) :=
  sums.pair varyingArgument (products.app varyingFunction varyingArgument)

/-- A nonidentity, noninjective context substitution. -/
def foldingContext (context : Nat) : Nat := context % 3 + 1

def dependentMotive :
    (familiesCwf.{0}).Ty (formation.identityContext varyingDomain) :=
  fun point => Fin (point.1.1.1 + point.1.1.2.val + point.1.2.val + 2)

def dependentBase : (familiesCwf.{0}).Tm ((familiesCwf.{0}).ext Nat varyingDomain)
    ((familiesCwf.{0}).tySub dependentMotive (elimination.reflexivitySubstitution varyingDomain)) :=
  fun point => ⟨2 * point.2.val + 1, by
    change 2 * point.2.val + 1 < point.1 + point.2.val + point.2.val + 2
    omega⟩

theorem varying_computation :
    (products.app varyingFunction varyingArgument 2).val = 3 ∧
      (sums.fst varyingPair 2).val = 2 ∧ (sums.snd varyingPair 2).val = 3 ∧
      (elimination.j dependentMotive dependentBase
        (elimination.reflexivitySubstitution varyingDomain ⟨2, ⟨1, by decide⟩⟩)).val = 3 :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- The general J square is exercised at a context-dependent motive and
base. Its finite endpoint fibres are retained by the actual reindex map. -/
theorem dependent_reindex_square :
    (familiesCwf.{0}).tmSub
        ((familiesCwf.{0}).tmSub (elimination.j dependentMotive dependentBase)
          (reindexing.map foldingContext varyingDomain))
        (elimination.reflexivitySubstitution
          ((familiesCwf.{0}).tySub varyingDomain foldingContext)) =
      reindexBase elimination reindexing identity_reindexing.2.2
        foldingContext varyingDomain dependentMotive dependentBase :=
  full_motive_beta_square foldingContext varyingDomain dependentMotive dependentBase

/-- Discarding the context substitution changes the retained dependent-pair
answer. This comparison observes values, not just the spelling of types. -/
theorem dropping_reindex_changes_answer :
    (((familiesCwf.{0}).tmSub (sums.snd varyingPair) foldingContext) 0).val = 2 ∧
      (sums.snd varyingPair 0).val = 1 ∧
      (((familiesCwf.{0}).tmSub (sums.snd varyingPair) foldingContext) 0).val ≠
        (sums.snd varyingPair 0).val :=
  ⟨rfl, rfl, by decide⟩

/-- Erasure to raw operations does not collapse the existing genuinely
varying dependent products and sums to constant families. -/
theorem products_and_sums_not_constant :
    (¬ ∃ Constant : Type, ∀ context : Bool,
      Nonempty ((products.pi (constantFamily PUnit)
        (fun point => DependencyExtensionalityOrthogonality.varyingBoolFamily point.1) context) ≃
          Constant)) ∧
    (¬ ∃ Constant : Type, ∀ context : Bool,
      Nonempty ((sums.sigma (constantFamily PUnit)
        (fun point => DependencyExtensionalityOrthogonality.varyingBoolFamily point.1) context) ≃
          Constant)) :=
  ⟨ContextualProductComparison.varying_product_not_constant,
    ContextualSumComparison.varying_sum_not_constant⟩

end Families

/-! ## Formation and reflexivity do not supply full dependent elimination -/

namespace IndiscreteBoundary

def formation : IdentityFormationOperations (familiesCwf.{0}) :=
  IdentityFormationOperations.ofQualified ContextualIdentityTypes.Families.indiscreteFormation

def reflexivity : IdentityReflexivityOperations formation :=
  IdentityReflexivityOperations.ofQualified ContextualIdentityTypes.Families.indiscreteReflexivity

theorem basic_substitution_laws :
    StrictIdentityFormationSubstitution formation ∧ StrictReflexivitySubstitution reflexivity :=
  ⟨IdentityFormationOperations.ofQualified_substitution
      ContextualIdentityTypes.Families.indiscreteFormation,
    IdentityReflexivityOperations.ofQualified_substitution
      ContextualIdentityTypes.Families.indiscreteReflexivity⟩

/-- The old full dependent diagonal-motive obstruction applies unchanged
to the raw split. Qualification cannot be manufactured by moving proof
fields out of the operation records. -/
theorem no_qualified_elimination :
    ¬ ∃ elimination : IdentityEliminationOperations formation,
      IdentityBoundary reflexivity elimination ∧ IdentityBeta elimination := by
  rintro ⟨elimination, boundary, beta⟩
  apply ContextualIdentityTypes.Families.no_indiscreteIdentityElimination
  exact ⟨{
    reflexivitySubstitution := elimination.reflexivitySubstitution
    over_diagonal := boundary.1
    witness_is_refl := boundary.2
    j := elimination.j
    beta := beta }⟩

end IndiscreteBoundary

/-- A common, nonconstant set-family positive instance and the incompatible
identity extension on that same contextual core. This is not a model of any
native declaration environment or an unbounded universe hierarchy. -/
theorem set_family_controls :
    BetaLaws Families.operations.{0} ∧
      StrictSubstitutionLaws Families.operations.{0} ∧
      (StrictIdentityFormationSubstitution IndiscreteBoundary.formation ∧
        StrictReflexivitySubstitution IndiscreteBoundary.reflexivity) ∧
      ¬ ∃ elimination : IdentityEliminationOperations IndiscreteBoundary.formation,
        IdentityBoundary IndiscreteBoundary.reflexivity elimination ∧ IdentityBeta elimination :=
  ⟨Families.beta_laws, Families.substitution_laws,
    IndiscreteBoundary.basic_substitution_laws, IndiscreteBoundary.no_qualified_elimination⟩

#print axioms j_beta_substitution
#print axioms Families.substitution_laws
#print axioms Families.full_motive_beta_square
#print axioms Families.varying_computation
#print axioms Families.dependent_reindex_square
#print axioms Families.dropping_reindex_changes_answer
#print axioms Families.products_and_sums_not_constant
#print axioms IndiscreteBoundary.no_qualified_elimination
#print axioms set_family_controls

end Mettapedia.TypeTheory.ContextualTypeOperations
