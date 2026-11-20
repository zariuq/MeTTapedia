import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.TypedPublicationRunTransport
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.CountingModalities

/-!
# Counting an origin-indexed family of actual publication offers

Each offer retains an explicit origin index and an actual certified source
application. The span contains exactly its admitted offers, with the real
publication result as target. Transport is a bijection on these edges: the
index is retained and admission is reflected as well as preserved.

These are counts of the declared offer family, not counts of all possible
helper presentations, and not merely counts of distinct successor states.
The theorem applies to arbitrary index types; finite program slices are a
direct instance. It supplies no predecessor-lifting or scheduler law.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.TypedPublication.OfferedCounts

open _root_.CategoryTheory
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta DependentFull
open LogicOverTheStep.CountingModalities
open Mettapedia.OSLF.Framework.DerivedModalities

variable {Head L : Type} [UniverseLevel.LevelOrder L] {rules : Rules Head}
  {levels : LevelModel rules L} {O : Type} [DecidableEq O]
  {Index : Type} {source target : State rules O}

def span (offers : Index → Application levels O source) : ReductionSpan (State rules O) where
  Edge := {index : Index // (realizationStep levels O).Admits (offers index)}
  source _ := source
  target edge := (realizationStep levels O).result (offers edge.val) edge.property

def move (comparison : PlainIso levels source target) (offers : Index → Application levels O source) :
    Index → Application levels O target := fun index => RunTransport.application comparison (offers index)

def edges (comparison : PlainIso levels source target) (offers : Index → Application levels O source) :
    (span offers).Edge ≃ (span (move comparison offers)).Edge where
  toFun edge := ⟨edge.val, (RunTransport.admits comparison (offers edge.val)).mpr edge.property⟩
  invFun edge := ⟨edge.val, (RunTransport.admits comparison (offers edge.val)).mp edge.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem origins_kept (comparison : PlainIso levels source target)
    (offers : Index → Application levels O source) (edge : (span offers).Edge) :
    (edges comparison offers edge).val = edge.val := rfl

def results (comparison : PlainIso levels source target)
    (offers : Index → Application levels O source) (edge : (span offers).Edge) :
    PlainIso levels ((span offers).target edge)
      ((span (move comparison offers)).target (edges comparison offers edge)) :=
  RunTransport.after comparison (offers edge.val) edge.property

theorem counts (comparison : PlainIso levels source target) (offers : Index → Application levels O source)
    (observation : State rules O → Prop)
    (invariant : ∀ {first second : State rules O}, PlainIso levels first second →
      (observation first ↔ observation second)) (number : Nat) :
    countingDiamond (span offers) number observation source ↔
      countingDiamond (span (move comparison offers)) number observation target := by
  classical
  constructor
  · rintro ⟨chosen, cardinality, checked⟩
    refine ⟨chosen.map (edges comparison offers).toEmbedding,
      (Finset.card_map _).trans cardinality, ?_⟩
    intro edge member
    obtain ⟨original, inside, rfl⟩ := Finset.mem_map.mp member
    exact ⟨rfl, (invariant (results comparison offers original)).mp (checked original inside).2⟩
  · rintro ⟨chosen, cardinality, checked⟩
    refine ⟨chosen.map (edges comparison offers).symm.toEmbedding,
      (Finset.card_map _).trans cardinality, ?_⟩
    intro edge member
    obtain ⟨original, inside, rfl⟩ := Finset.mem_map.mp member
    exact ⟨rfl, (invariant (RunTransport.after comparison (offers original.val)
      ((RunTransport.admits comparison (offers original.val)).mp original.property))).mpr
        (checked original inside).2⟩

theorem possibility (comparison : PlainIso levels source target) (offers : Index → Application levels O source)
    (observation : State rules O → Prop)
    (invariant : ∀ {first second : State rules O}, PlainIso levels first second →
      (observation first ↔ observation second)) :
    derivedDiamond (span offers) observation source ↔
      derivedDiamond (span (move comparison offers)) observation target := by
  rw [← countingDiamond_one, ← countingDiamond_one]
  exact counts comparison offers observation invariant 1

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.TypedPublication.OfferedCounts

#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.TypedPublication.OfferedCounts.edges
#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.TypedPublication.OfferedCounts.counts
