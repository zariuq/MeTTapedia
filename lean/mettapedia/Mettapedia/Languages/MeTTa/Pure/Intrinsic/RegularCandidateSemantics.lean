import Mettapedia.Languages.MeTTa.Pure.Intrinsic.RegularKripkeCandidates

/-!
# Candidate-respecting contexts and substitutions

This module supplies the semantic environment layer required by the regular
Pure fundamental lemma.  A candidate context says which simultaneous
substitutions realize it and proves that realization is stable under variable
renaming.  A candidate type assigns a reducibility candidate to every realized
environment.  Extending a context makes the new head variable inhabit the
candidate selected by the tail environment.

The resulting substitutions compose and candidate types reindex
contravariantly.  This is genuine dependent-context infrastructure, but it does
not yet interpret the syntactic type formers or prove the fundamental lemma.
-/

namespace Mettapedia.Languages.MeTTa.Pure.Intrinsic.PresentationBoundary

open Mettapedia.Languages.MeTTa.Pure.Intrinsic.Syntax
open Mettapedia.Languages.MeTTa.Pure.Intrinsic.Renaming
open Mettapedia.Languages.MeTTa.Pure.Intrinsic.Substitution
open Mettapedia.Languages.MeTTa.Pure.Intrinsic.Reduction
open Mettapedia.Languages.MeTTa.Pure.Intrinsic.Typing

/-! ## Semantic contexts -/

/-- A simultaneous substitution realizes a semantic context when each image
has the candidate membership required by the dependent telescope. -/
structure CandidateContext (n : Nat) where
  Realizes : {m : Nat} → Sub n m → Prop
  identity_realizes : Realizes ids
  rename_realizes : ∀ {m k : Nat} (σ : Sub n m) (ρ : Ren m k),
    Realizes σ → Realizes (fun index => rename ρ (σ index))

namespace CandidateContext

/-- The empty semantic context is realized by its unique substitution. -/
def empty : CandidateContext 0 where
  Realizes := fun _ => True
  identity_realizes := trivial
  rename_realizes := fun _ _ _ => trivial

end CandidateContext

/-! ## Types over semantic contexts -/

/-- A semantic type over a candidate context.  Its candidate may depend on the
whole realizing environment, and membership transports to every future scope. -/
structure CandidateType {n : Nat} (context : CandidateContext n) where
  candidate : {m : Nat} → Sub n m → ReductionCandidate m
  rename_mem : ∀ {m k : Nat} (σ : Sub n m) (ρ : Ren m k)
      {term : PureTm m},
    context.Realizes σ →
      (candidate σ).pred term →
        (candidate (fun index => rename ρ (σ index))).pred (rename ρ term)

namespace CandidateType

/-- Strong normalization as a constant semantic type over any context. -/
def normalizing (context : CandidateContext n) : CandidateType context where
  candidate := fun _ => ReductionCandidate.normalizing _
  rename_mem := by
    intro m k σ ρ term realized covered
    exact reductionAccessible_rename ρ covered

/-- The strict `U0`-avoiding candidate as another constant semantic type. -/
def avoidingU0 (context : CandidateContext n) : CandidateType context where
  candidate := fun _ => ReductionCandidate.RenamingStable.avoidingU0 _
  rename_mem := by
    intro m k σ ρ term realized covered
    exact ReductionCandidate.RenamingStable.avoidingU0Family.rename_mem ρ covered

end CandidateType

/-! ## Dependent context extension -/

/-- Remove the newest variable from a simultaneous substitution. -/
def tailSub (σ : Sub (n + 1) m) : Sub n m :=
  fun index => σ index.succ

@[simp] theorem tailSub_apply (σ : Sub (n + 1) m) (index : Fin n) :
    tailSub σ index = σ index.succ :=
  rfl

/-- The tail of the identity substitution is weakening of the preceding
identity substitution. -/
theorem tailSub_ids :
    tailSub (ids : Sub (n + 1) (n + 1)) =
      fun index => rename wk ((ids : Sub n n) index) := by
  funext index
  rfl

namespace CandidateContext

/-- Extend a semantic context by a dependent semantic type.  The head image is
checked in the candidate selected by the realized tail environment. -/
def extend (context : CandidateContext n) (type : CandidateType context) :
    CandidateContext (n + 1) where
  Realizes := fun σ =>
    context.Realizes (tailSub σ) ∧
      (type.candidate (tailSub σ)).pred (σ 0)
  identity_realizes := by
    constructor
    · rw [tailSub_ids]
      exact context.rename_realizes ids wk context.identity_realizes
    · apply (type.candidate (tailSub ids)).cr3 (neutral_var 0)
      intro target step
      cases step
  rename_realizes := by
    intro m k σ ρ realized
    constructor
    · exact context.rename_realizes (tailSub σ) ρ realized.1
    · exact type.rename_mem (tailSub σ) ρ realized.1 realized.2

end CandidateContext

namespace CandidateType

/-- Reuse a semantic type under the context extension it generated.  Its
candidate depends only on the tail environment. -/
def weaken {context : CandidateContext n} (type : CandidateType context) :
    CandidateType (context.extend type) where
  candidate := fun σ => type.candidate (tailSub σ)
  rename_mem := by
    intro m k σ ρ term realized covered
    exact type.rename_mem (tailSub σ) ρ realized.1 covered

/-- A term realizes a semantic type when every context-realizing substitution
maps it into the candidate selected by that environment. -/
def RealizesTerm {context : CandidateContext n} (type : CandidateType context)
    (term : PureTm n) : Prop :=
  ∀ {m : Nat} (σ : Sub n m), context.Realizes σ →
    (type.candidate σ).pred (subst σ term)

/-- The newest variable realizes the weakened type in an extended context. -/
theorem head_realizes {context : CandidateContext n}
    (type : CandidateType context) :
    type.weaken.RealizesTerm (.var 0) := by
  intro m σ realized
  exact realized.2

end CandidateType

/-! ## Candidate-respecting substitutions -/

/-- Composition of simultaneous substitutions.  The right substitution runs
first. -/
def compSub (later : Sub m k) (earlier : Sub n m) : Sub n k :=
  fun index => subst later (earlier index)

@[simp] theorem compSub_left_id (σ : Sub n m) :
    compSub ids σ = σ := by
  funext index
  exact subst_ids (t := σ index)

@[simp] theorem compSub_right_id (σ : Sub n m) :
    compSub σ ids = σ := by
  rfl

theorem compSub_assoc (last : Sub k l) (middle : Sub m k)
    (first : Sub n m) :
    compSub last (compSub middle first) =
      compSub (compSub last middle) first := by
  funext index
  exact subst_comp last middle (first index)

/-- Renaming after substitution agrees with renaming every image of the
environment before applying the source substitution. -/
theorem rename_compSub (ρ : Ren m k) (environment : Sub n m)
    (source : Sub l n) :
    (fun index => rename ρ (compSub environment source index)) =
      compSub (fun index => rename ρ (environment index)) source := by
  funext index
  exact rename_subst ρ environment (source index)

/-! ## Context comprehension at the substitution level -/

/-- Extend a substitution by one newest image.  The head supplies de Bruijn
index zero; the tail supplies all preceding indices. -/
def consSub (head : PureTm m) (tail : Sub n m) : Sub (n + 1) m :=
  Fin.cases head tail

@[simp] theorem consSub_zero (head : PureTm m) (tail : Sub n m) :
    consSub head tail 0 = head :=
  rfl

@[simp] theorem consSub_succ (head : PureTm m) (tail : Sub n m)
    (index : Fin n) :
    consSub head tail index.succ = tail index :=
  rfl

@[simp] theorem tailSub_consSub (head : PureTm m) (tail : Sub n m) :
    tailSub (consSub head tail) = tail := by
  funext index
  rfl

/-- Every nonempty substitution is recovered from its head and tail. -/
theorem consSub_head_tail (σ : Sub (n + 1) m) :
    consSub (σ 0) (tailSub σ) = σ := by
  funext index
  refine Fin.cases ?_ ?_ index
  · rfl
  · intro preceding
    rfl

/-- Substitution into a cons environment preserves its tail component. -/
theorem tailSub_compSub_consSub (environment : Sub m k)
    (head : PureTm m) (tail : Sub n m) :
    tailSub (compSub environment (consSub head tail)) =
      compSub environment tail := by
  funext index
  rfl

/-- Substitution into a cons environment evaluates its head component. -/
@[simp] theorem compSub_consSub_zero (environment : Sub m k)
    (head : PureTm m) (tail : Sub n m) :
    compSub environment (consSub head tail) 0 = subst environment head :=
  rfl

/-- Weakening projects the tail of a context extension. -/
theorem compSub_consSub_renToSub_wk (head : PureTm m) (tail : Sub n m) :
    compSub (consSub head tail) (renToSub wk) = tail := by
  funext index
  rfl

/-- Composing an environment with weakening selects its tail. -/
theorem compSub_renToSub_wk (environment : Sub (n + 1) m) :
    compSub environment (renToSub wk) = tailSub environment := by
  funext index
  rfl

/-- Pairing the newest variable with weakening is the identity substitution. -/
theorem consSub_var_zero_renToSub_wk :
    consSub (.var 0) (renToSub wk) = (ids : Sub (n + 1) (n + 1)) := by
  funext index
  refine Fin.cases ?_ ?_ index
  · rfl
  · intro preceding
    rfl

/-- A semantic substitution from `source` to `target` maps every environment
realizing the target context to one realizing the source context. -/
structure CandidateSubstitution (source : CandidateContext n)
    (target : CandidateContext m) (substitution : Sub n m) where
  maps_realizers : ∀ {k : Nat} (environment : Sub m k),
    target.Realizes environment →
      source.Realizes (compSub environment substitution)

namespace CandidateSubstitution

/-- Identity substitutions preserve every semantic context. -/
def id (context : CandidateContext n) :
    CandidateSubstitution context context ids where
  maps_realizers := by
    intro k environment realized
    simpa using realized

/-- Candidate-respecting substitutions compose. -/
def comp {source : CandidateContext n} {middle : CandidateContext m}
    {target : CandidateContext k} {first : Sub n m} {later : Sub m k}
    (sourceToMiddle : CandidateSubstitution source middle first)
    (middleToTarget : CandidateSubstitution middle target later) :
    CandidateSubstitution source target (compSub later first) where
  maps_realizers := by
    intro l environment realized
    rw [compSub_assoc]
    exact sourceToMiddle.maps_realizers
      (compSub environment later)
      (middleToTarget.maps_realizers environment realized)

/-- The weakening substitution is the semantic projection from a context
extension to its base. -/
def projection {context : CandidateContext n} (type : CandidateType context) :
    CandidateSubstitution context (context.extend type) (renToSub wk) where
  maps_realizers := by
    intro k environment realized
    have baseRealized := realized.1
    change context.Realizes (compSub environment (renToSub wk))
    rw [compSub_renToSub_wk]
    exact baseRealized

end CandidateSubstitution

/-! ## Contravariant reindexing of semantic types -/

namespace CandidateType

/-- Pull a semantic type back along a candidate-respecting substitution. -/
def reindex {source : CandidateContext n} {target : CandidateContext m}
    {σ : Sub n m} (type : CandidateType source)
    (map : CandidateSubstitution source target σ) : CandidateType target where
  candidate := fun environment => type.candidate (compSub environment σ)
  rename_mem := by
    intro k l environment ρ term realized covered
    have sourceRealized := map.maps_realizers environment realized
    have transported := type.rename_mem
      (compSub environment σ) ρ sourceRealized covered
    rw [rename_compSub] at transported
    exact transported

/-- Reindexing along identity preserves the selected candidate. -/
theorem reindex_id_candidate {context : CandidateContext n}
    (type : CandidateType context) (environment : Sub n m) :
    (type.reindex (CandidateSubstitution.id context)).candidate environment =
      type.candidate environment := by
  simp [reindex]

/-- Reindexing along a composite selects the same candidate as two successive
reindexings. -/
theorem reindex_comp_candidate
    {source : CandidateContext n} {middle : CandidateContext m}
    {target : CandidateContext k} {first : Sub n m} {later : Sub m k}
    (type : CandidateType source)
    (sourceToMiddle : CandidateSubstitution source middle first)
    (middleToTarget : CandidateSubstitution middle target later)
    (environment : Sub k l) :
    ((type.reindex sourceToMiddle).reindex middleToTarget).candidate environment =
      (type.reindex (sourceToMiddle.comp middleToTarget)).candidate environment := by
  simp only [reindex]
  rw [← compSub_assoc]

/-- Semantic term realization is stable under every candidate-respecting
substitution. -/
theorem RealizesTerm.subst
    {source : CandidateContext n} {target : CandidateContext m}
    {σ : Sub n m} {type : CandidateType source} {term : PureTm n}
    (realizes : type.RealizesTerm term)
    (map : CandidateSubstitution source target σ) :
    (type.reindex map).RealizesTerm (subst σ term) := by
  intro k environment targetRealized
  have sourceRealized := map.maps_realizers environment targetRealized
  have covered := realizes (compSub environment σ) sourceRealized
  rw [subst_comp]
  change (type.candidate (compSub environment σ)).pred
    (Substitution.subst
      (fun index => Substitution.subst environment (σ index)) term)
  rw [show (fun index => Substitution.subst environment (σ index)) =
      compSub environment σ from rfl]
  exact covered

end CandidateType

/-! ## Semantic comprehension -/

namespace CandidateSubstitution

/-- Semantic pairing: a substitution into the base together with a term in
the pulled-back fibre determines a substitution into the extension. -/
def pair {source : CandidateContext n} {target : CandidateContext m}
    {σ : Sub n m} (type : CandidateType source)
    (base : CandidateSubstitution source target σ)
    {term : PureTm m}
    (head : (type.reindex base).RealizesTerm term) :
    CandidateSubstitution (source.extend type) target (consSub term σ) where
  maps_realizers := by
    intro k environment targetRealized
    have baseRealized := base.maps_realizers environment targetRealized
    have headRealized := head environment targetRealized
    constructor
    · rw [tailSub_compSub_consSub]
      exact baseRealized
    · rw [tailSub_compSub_consSub]
      change (type.candidate (compSub environment σ)).pred
        (subst environment term)
      exact headRealized

/-- The base component of semantic pairing satisfies the first projection
law at the raw substitution level. -/
theorem pair_projection_beta
    {source : CandidateContext n} {target : CandidateContext m}
    {σ : Sub n m} (type : CandidateType source)
    (base : CandidateSubstitution source target σ)
    {term : PureTm m}
    (_head : (type.reindex base).RealizesTerm term) :
    compSub (consSub term σ) (renToSub wk) = σ := by
  exact compSub_consSub_renToSub_wk term σ

/-- The head component of semantic pairing satisfies the second projection
law definitionally. -/
theorem pair_head_beta
    {source : CandidateContext n} {target : CandidateContext m}
    {σ : Sub n m} (type : CandidateType source)
    (base : CandidateSubstitution source target σ)
    {term : PureTm m}
    (_head : (type.reindex base).RealizesTerm term) :
    subst (consSub term σ) (.var 0) = term := by
  rfl

end CandidateSubstitution

/-! ## Positive and negative canaries -/

def emptyNormalizingType : CandidateType CandidateContext.empty :=
  CandidateType.normalizing CandidateContext.empty

def oneVariableNormalizingContext : CandidateContext 1 :=
  CandidateContext.empty.extend emptyNormalizingType

/-- The head variable is semantically valid in the one-variable normalizing
context. -/
theorem oneVariable_head_realizes :
    emptyNormalizingType.weaken.RealizesTerm (.var 0) :=
  CandidateType.head_realizes emptyNormalizingType

/-- The empty-context normalizing semantics rejects the looping omega term. -/
theorem omega_not_realized_in_empty_normalizing :
    ¬ emptyNormalizingType.RealizesTerm regularOmega := by
  intro realized
  have covered := realized (ids : Sub 0 0) trivial
  change ReductionAccessible regularOmega at covered
  exact omega_not_in_normalizing_candidate covered

/-! ## Axiom audit -/

#print axioms tailSub_ids
#print axioms CandidateType.head_realizes
#print axioms compSub_assoc
#print axioms rename_compSub
#print axioms consSub_head_tail
#print axioms tailSub_compSub_consSub
#print axioms compSub_consSub_renToSub_wk
#print axioms compSub_renToSub_wk
#print axioms consSub_var_zero_renToSub_wk
#print axioms CandidateSubstitution.projection
#print axioms CandidateSubstitution.pair
#print axioms CandidateSubstitution.pair_projection_beta
#print axioms CandidateSubstitution.pair_head_beta
#print axioms CandidateType.reindex_id_candidate
#print axioms CandidateType.reindex_comp_candidate
#print axioms CandidateType.RealizesTerm.subst
#print axioms oneVariable_head_realizes
#print axioms omega_not_realized_in_empty_normalizing

end Mettapedia.Languages.MeTTa.Pure.Intrinsic.PresentationBoundary
