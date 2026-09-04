import Mettapedia.GSLT.Core.OperationalRealization
import Mettapedia.GSLT.Core.SemanticInvariant

/-!
# Semantic transport along operational realizations

An operational realization explains how source computation is implemented by
target paths.  It does not, by itself, identify the independently selected
meanings of source and target terms.  A `DenotationSquare` records that extra
comparison as a commuting square.

The construction is deliberately neutral about the chosen mathematical
domain.  Graph representations may use finite graphs, compilers may use source
and target observations, and logical languages may use model-theoretic
denotations.  The operational map and semantic comparison remain separate.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT

open Mettapedia.GSLT.IndexedOperational

universe uSource uMiddle uTarget uMeaning uMiddleMeaning uTargetMeaning

namespace IndexedOperational

/-! ## Discrete operational targets -/

/-- A path in a discrete GSLT can only be reflexive.  In particular, its
endpoints are equal. -/
theorem discreteExecutionPath_eq {Term : Type uMeaning}
    {source target : (GSLT.discrete Term).Term}
    (path : ExecutionPath (GSLT.discrete Term) source target) :
    source = target := by
  cases path with
  | refl => rfl
  | cons step _rest => exact step.down.elim

/-- A path in a discrete GSLT performs no primitive rewrites. -/
@[simp] theorem discreteExecutionPath_length {Term : Type uMeaning}
    {source target : (GSLT.discrete Term).Term}
    (path : ExecutionPath (GSLT.discrete Term) source target) :
    path.length = 0 := by
  cases path with
  | refl => rfl
  | cons step _rest => exact step.down.elim

/-- Equality of endpoints supplies the unique path in a discrete GSLT. -/
def discreteExecutionPath_of_eq {Term : Type uMeaning}
    {source target : (GSLT.discrete Term).Term}
    (equal : source = target) :
    ExecutionPath (GSLT.discrete Term) source target :=
  equal ▸ .refl source

/-- Proof-relevant paths become unique only after the target dynamics have
been explicitly selected to be discrete. -/
instance discreteExecutionPath_subsingleton {Term : Type uMeaning}
    {source target : (GSLT.discrete Term).Term} :
    Subsingleton (ExecutionPath (GSLT.discrete Term) source target) where
  allEq first second := by
    cases first with
    | refl =>
        cases second with
        | refl => rfl
        | cons step _rest => exact step.down.elim
    | cons step _rest => exact step.down.elim

namespace OperationalRealization

/-- Realizations into a discrete target are determined by their term map.
The target has no steps, so there is no hidden path choice in `mapStep`. -/
theorem ext_mapTerm
    {source : GSLT.{uSource}} {Meaning : Type uMeaning}
    {first second : OperationalRealization source (GSLT.discrete Meaning)}
    (equal : first.mapTerm = second.mapTerm) : first = second := by
  cases first with
  | mk firstMap firstEquiv firstStep =>
      cases second with
      | mk secondMap secondEquiv secondStep =>
          dsimp at equal
          subst secondMap
          have equivEqual : @firstEquiv = @secondEquiv := by
            apply Subsingleton.elim
          subst secondEquiv
          have stepEqual : @firstStep = @secondStep := by
            funext sourceTerm targetTerm step
            exact Subsingleton.elim _ _
          subst secondStep
          rfl

end OperationalRealization

end IndexedOperational

namespace SemanticInvariant

/-- Semantic invariants are determined by their denotation maps. -/
theorem ext_denote {system : GSLT.{uSource}} {Meaning : Type uMeaning}
    {first second : SemanticInvariant system Meaning}
    (equal : first.denote = second.denote) : first = second := by
  cases first
  cases second
  cases equal
  rfl

/-! ## Invariants as operational realizations -/

/-- A conserved denotation is an operational realization into the discrete
GSLT of semantic values.  Equations map to equality and every source step
maps to the reflexive target path licensed by conservation. -/
def toDiscreteRealization {system : GSLT.{uSource}}
    {Meaning : Type uMeaning}
    (invariant : SemanticInvariant system Meaning) :
    OperationalRealization system (GSLT.discrete Meaning) where
  mapTerm := invariant.denote
  mapEquiv := invariant.equation
  mapStep := fun step =>
    IndexedOperational.discreteExecutionPath_of_eq
      (invariant.rewrite step)

/-- Conversely, realizing computation into a discrete semantic GSLT says
exactly that the realization's term map is conserved. -/
def ofDiscreteRealization {system : GSLT.{uSource}}
    {Meaning : Type uMeaning}
    (realization : OperationalRealization system (GSLT.discrete Meaning)) :
    SemanticInvariant system Meaning where
  denote := realization.mapTerm
  equation := realization.mapEquiv
  rewrite := fun step =>
    IndexedOperational.discreteExecutionPath_eq (realization.mapStep step)

/-- Semantic invariants are exactly path-valued operational realizations into
a discrete semantic GSLT.  This characterizes, rather than merely suggests,
the boundary between evolving operational state and conserved meaning. -/
def discreteRealizationEquiv {system : GSLT.{uSource}}
    {Meaning : Type uMeaning} :
    SemanticInvariant system Meaning ≃
      OperationalRealization system (GSLT.discrete Meaning) where
  toFun := toDiscreteRealization
  invFun := ofDiscreteRealization
  left_inv := fun invariant => by
    apply ext_denote
    rfl
  right_inv := fun realization => by
    apply OperationalRealization.ext_mapTerm
    rfl

/-- Pull a target invariant back through a path-valued operational
realization.  Primitive source steps may expand to any finite target path. -/
def pullback {source : GSLT.{uSource}} {target : GSLT.{uTarget}}
    {Meaning : Type uMeaning}
    (targetInvariant : SemanticInvariant target Meaning)
    (realization : OperationalRealization source target) :
    SemanticInvariant source Meaning where
  denote := targetInvariant.denote ∘ realization.mapTerm
  equation := fun equivalent =>
    targetInvariant.equation (realization.mapEquiv equivalent)
  rewrite := fun step =>
    targetInvariant.executionPath_eq (realization.mapStep step)

@[simp] theorem pullback_denote
    {source : GSLT.{uSource}} {target : GSLT.{uTarget}}
    {Meaning : Type uMeaning}
    (targetInvariant : SemanticInvariant target Meaning)
    (realization : OperationalRealization source target)
    (term : source.Term) :
    (targetInvariant.pullback realization).denote term =
      targetInvariant.denote (realization.mapTerm term) :=
  rfl

/-- Pulling back along the identity realization changes no invariant. -/
@[simp] theorem pullback_id {system : GSLT.{uSource}}
    {Meaning : Type uMeaning}
    (invariant : SemanticInvariant system Meaning) :
    invariant.pullback (OperationalRealization.id system) = invariant := by
  apply ext_denote
  rfl

/-- Semantic pullback is contravariantly compositional. -/
@[simp] theorem pullback_comp
    {source : GSLT.{uSource}} {middle : GSLT.{uMiddle}}
    {target : GSLT.{uTarget}} {Meaning : Type uMeaning}
    (targetInvariant : SemanticInvariant target Meaning)
    (earlier : OperationalRealization source middle)
    (later : OperationalRealization middle target) :
    (targetInvariant.pullback later).pullback earlier =
      targetInvariant.pullback (earlier.comp later) := by
  apply ext_denote
  rfl

end SemanticInvariant

namespace IndexedOperational

/-- A semantic comparison for an operational realization.  The upper edge is
path-valued operational implementation; the lower edge is the independently
chosen map of meanings. -/
structure DenotationSquare
    {source : GSLT.{uSource}} {target : GSLT.{uTarget}}
    {SourceMeaning : Type uMeaning} {TargetMeaning : Type uTargetMeaning}
    (realization : OperationalRealization source target)
    (sourceDenotation : SemanticInvariant source SourceMeaning)
    (targetDenotation : SemanticInvariant target TargetMeaning)
    (mapMeaning : SourceMeaning → TargetMeaning) : Prop where
  commutes : ∀ term,
    targetDenotation.denote (realization.mapTerm term) =
      mapMeaning (sourceDenotation.denote term)

namespace DenotationSquare

/-- Identity computation and identity meaning form a semantic square. -/
def id {system : GSLT.{uSource}} {Meaning : Type uMeaning}
    (denotation : SemanticInvariant system Meaning) :
    DenotationSquare (OperationalRealization.id system)
      denotation denotation _root_.id where
  commutes := fun _term => rfl

/-- Semantic squares compose in the same order as their operational
realizations and meaning maps. -/
def comp
    {source : GSLT.{uSource}} {middle : GSLT.{uMiddle}}
    {target : GSLT.{uTarget}}
    {SourceMeaning : Type uMeaning}
    {MiddleMeaning : Type uMiddleMeaning}
    {TargetMeaning : Type uTargetMeaning}
    {earlier : OperationalRealization source middle}
    {later : OperationalRealization middle target}
    {sourceDenotation : SemanticInvariant source SourceMeaning}
    {middleDenotation : SemanticInvariant middle MiddleMeaning}
    {targetDenotation : SemanticInvariant target TargetMeaning}
    {mapEarlier : SourceMeaning → MiddleMeaning}
    {mapLater : MiddleMeaning → TargetMeaning}
    (earlierSquare : DenotationSquare earlier sourceDenotation
      middleDenotation mapEarlier)
    (laterSquare : DenotationSquare later middleDenotation
      targetDenotation mapLater) :
    DenotationSquare (earlier.comp later) sourceDenotation targetDenotation
      (mapLater ∘ mapEarlier) where
  commutes := by
    intro term
    change targetDenotation.denote
        (later.mapTerm (earlier.mapTerm term)) =
      mapLater (mapEarlier (sourceDenotation.denote term))
    rw [laterSquare.commutes, earlierSquare.commutes]

/-- Pullback is the canonical square whose meaning map is identity. -/
def ofPullback
    {source : GSLT.{uSource}} {target : GSLT.{uTarget}}
    {Meaning : Type uMeaning}
    (targetDenotation : SemanticInvariant target Meaning)
    (realization : OperationalRealization source target) :
    DenotationSquare realization (targetDenotation.pullback realization)
      targetDenotation _root_.id where
  commutes := fun _term => rfl

/-- The square and source invariance agree along every complete source path.
This is the path-level semantic commuting law used by realizations. -/
theorem path_commutes
    {source : GSLT.{uSource}} {target : GSLT.{uTarget}}
    {SourceMeaning : Type uMeaning} {TargetMeaning : Type uTargetMeaning}
    {realization : OperationalRealization source target}
    {sourceDenotation : SemanticInvariant source SourceMeaning}
    {targetDenotation : SemanticInvariant target TargetMeaning}
    {mapMeaning : SourceMeaning → TargetMeaning}
    (square : DenotationSquare realization sourceDenotation
      targetDenotation mapMeaning)
    {sourceTerm targetTerm : source.Term}
    (path : ExecutionPath source sourceTerm targetTerm) :
    targetDenotation.denote (realization.mapTerm sourceTerm) =
      mapMeaning (sourceDenotation.denote targetTerm) :=
  (square.commutes sourceTerm).trans
    (congrArg mapMeaning (sourceDenotation.executionPath_eq path))

end DenotationSquare

/-! ## Non-collapse canary -/

namespace DenotationSquareCanary

def booleanSystem : GSLT := GSLT.discrete Bool

/-- The selected denotation observes the Boolean term itself. -/
def booleanDenotation : SemanticInvariant booleanSystem Bool where
  denote := _root_.id
  equation := fun equal => equal
  rewrite := fun impossible => impossible.elim

/-- Boolean negation is an operational realization of the discrete system:
there are no source steps to constrain it. -/
def flip : OperationalRealization booleanSystem booleanSystem where
  mapTerm := Bool.not
  mapEquiv := fun equal => congrArg Bool.not equal
  mapStep := fun impossible => impossible.elim

/-- The flip has the correct semantic square when meanings are also negated. -/
def flipNegationSquare :
    DenotationSquare flip booleanDenotation booleanDenotation Bool.not where
  commutes := fun _term => rfl

/-- Operational validity alone does not license the identity semantic map. -/
theorem noFlipIdentitySquare :
    ¬ DenotationSquare flip booleanDenotation booleanDenotation _root_.id := by
  intro square
  have falseCommutes := square.commutes false
  change true = false at falseCommutes
  exact Bool.noConfusion falseCommutes

end DenotationSquareCanary

/-! ## Transition-sensitive canary for the discrete characterization -/

namespace DiscreteRealizationCanary

abbrev togglingSystem : GSLT := OperationalRealization.FusionCanary.source

/-- Forgetting the Boolean state is a genuine invariant of the transition. -/
def constantInvariant : SemanticInvariant togglingSystem Unit where
  denote := fun _ => ()
  equation := fun _ => rfl
  rewrite := fun _ => rfl

/-- The positive control: the constant invariant gives a realization into a
discrete semantic target. -/
def constantRealization :
    OperationalRealization togglingSystem (GSLT.discrete Unit) :=
  constantInvariant.toDiscreteRealization

/-- The transition from `false` to `true` prevents Boolean identity from
being a semantic invariant. -/
theorem noIdentityInvariant :
    ¬ ∃ invariant : SemanticInvariant togglingSystem Bool,
      invariant.denote = _root_.id := by
  rintro ⟨invariant, equal⟩
  have impossible :=
    invariant.rewrite OperationalRealization.FusionCanary.source_step
  change invariant.denote false = invariant.denote true at impossible
  rw [equal] at impossible
  exact Bool.noConfusion impossible

/-- Equivalently, no identity-on-terms realization can send the toggling
system into the discrete Boolean GSLT. -/
theorem noIdentityDiscreteRealization :
    ¬ ∃ realization :
        OperationalRealization togglingSystem (GSLT.discrete Bool),
      realization.mapTerm = _root_.id := by
  rintro ⟨realization, equal⟩
  exact noIdentityInvariant
    ⟨SemanticInvariant.ofDiscreteRealization realization, equal⟩

end DiscreteRealizationCanary

#print axioms SemanticInvariant.pullback
#print axioms SemanticInvariant.pullback_comp
#print axioms SemanticInvariant.discreteRealizationEquiv
#print axioms DenotationSquare.comp
#print axioms DenotationSquare.path_commutes
#print axioms DenotationSquareCanary.flipNegationSquare
#print axioms DenotationSquareCanary.noFlipIdentitySquare
#print axioms DiscreteRealizationCanary.constantRealization
#print axioms DiscreteRealizationCanary.noIdentityInvariant
#print axioms DiscreteRealizationCanary.noIdentityDiscreteRealization

end IndexedOperational

end Mettapedia.GSLT
