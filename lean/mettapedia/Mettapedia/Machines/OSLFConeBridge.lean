import Mettapedia.Machines.ConeDuality
import Mettapedia.OSLF.Framework.TypeSynthesis

/-!
# OSLF modalities and production/demand cones

This module pins the variance between the one-step OSLF modalities generated
from a `LanguageDef` and the reflexive-transitive cones of a production
relation.

For a reduction `p ⟶ q`, `langDiamond φ p` asks whether a successor `q`
satisfies `φ`. As a transformer on sets, this is the one-step image under the
*reversed* relation. Its reachability closure is therefore `backwardCone`, not
`forwardCone`. Dually, the reachability box is `onlyFrom`.

This distinction matters operationally: a multi-step demand cone can contain a
state that the one-step diamond does not. The examples at the end retain that
negative discriminator.
-/

namespace Mettapedia.Machines

open Set
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.Framework.TypeSynthesis

/-- The generated one-step diamond is the step image under the reversed
reduction relation. This is the variance-correct set-transformer view. -/
theorem langDiamondUsing_eq_stepImage_swap
    (relEnv : RelationEnv) (lang : LanguageDef) (φ : Pattern → Prop) :
    langDiamondUsing relEnv lang φ =
      stepImage (Function.swap (langReducesUsing relEnv lang)) φ := by
  ext p
  rw [langDiamondUsing_spec]
  change (∃ q, langReducesUsing relEnv lang p q ∧ φ q) ↔
    ∃ q, φ q ∧ langReducesUsing relEnv lang p q
  constructor
  · rintro ⟨q, hpq, hφ⟩
    exact ⟨q, hφ, hpq⟩
  · rintro ⟨q, hφ, hpq⟩
    exact ⟨q, hpq, hφ⟩

/-- The generated one-step box is universal quantification over immediate
predecessors. -/
theorem langBoxUsing_eq_immediateOnlyFrom
    (relEnv : RelationEnv) (lang : LanguageDef) (φ : Pattern → Prop) :
    langBoxUsing relEnv lang φ =
      {p | ∀ q, langReducesUsing relEnv lang q p → φ q} := by
  ext p
  exact langBoxUsing_spec relEnv lang φ p

/-- Reflexive-transitive demand modality for a `LanguageDef`: states that can
reach a demanded state satisfying `φ`. -/
def langDiamondStarUsing (relEnv : RelationEnv) (lang : LanguageDef) :
    (Pattern → Prop) → (Pattern → Prop) :=
  backwardCone (langReducesUsing relEnv lang)

/-- Reflexive-transitive provenance box for a `LanguageDef`: states all of
whose reachable predecessors satisfy `φ`. -/
def langBoxStarUsing (relEnv : RelationEnv) (lang : LanguageDef) :
    (Pattern → Prop) → (Pattern → Prop) :=
  onlyFrom (langReducesUsing relEnv lang)

/-- Default-environment reachability diamond. -/
def langDiamondStar (lang : LanguageDef) :
    (Pattern → Prop) → (Pattern → Prop) :=
  langDiamondStarUsing RelationEnv.empty lang

/-- Default-environment reachability box. -/
def langBoxStar (lang : LanguageDef) :
    (Pattern → Prop) → (Pattern → Prop) :=
  langBoxStarUsing RelationEnv.empty lang

@[simp] theorem langDiamondStarUsing_spec
    (relEnv : RelationEnv) (lang : LanguageDef)
    (φ : Pattern → Prop) (p : Pattern) :
    langDiamondStarUsing relEnv lang φ p ↔
      ∃ q, φ q ∧ Reaches (langReducesUsing relEnv lang) p q :=
  Iff.rfl

@[simp] theorem langBoxStarUsing_spec
    (relEnv : RelationEnv) (lang : LanguageDef)
    (φ : Pattern → Prop) (p : Pattern) :
    langBoxStarUsing relEnv lang φ p ↔
      ∀ q, Reaches (langReducesUsing relEnv lang) q p → φ q :=
  Iff.rfl

/-- Demand over reachability is forward production in the opposite
direction. -/
theorem langDiamondStarUsing_eq_forwardCone_swap
    (relEnv : RelationEnv) (lang : LanguageDef) (φ : Pattern → Prop) :
    langDiamondStarUsing relEnv lang φ =
      forwardCone (Function.swap (langReducesUsing relEnv lang)) φ :=
  backwardCone_eq_forwardCone_swap _ _

/-- The reachability diamond and provenance box retain the generic cone
Galois connection. -/
theorem langReachabilityGaloisUsing
    (relEnv : RelationEnv) (lang : LanguageDef) :
    GaloisConnection (langDiamondStarUsing relEnv lang)
      (langBoxStarUsing relEnv lang) :=
  gc_backward (langReducesUsing relEnv lang)

/-- Every immediate demand is a reachable demand. -/
theorem langDiamondUsing_le_langDiamondStarUsing
    (relEnv : RelationEnv) (lang : LanguageDef) (φ : Pattern → Prop) :
    langDiamondUsing relEnv lang φ ≤ langDiamondStarUsing relEnv lang φ := by
  intro p hp
  obtain ⟨q, hpq, hφ⟩ :=
    (langDiamondUsing_spec relEnv lang φ p).mp hp
  exact ⟨q, hφ, Relation.ReflTransGen.single hpq⟩

/-- Reachability provenance is stronger than immediate-predecessor
provenance. -/
theorem langBoxStarUsing_le_langBoxUsing
    (relEnv : RelationEnv) (lang : LanguageDef) (φ : Pattern → Prop) :
    langBoxStarUsing relEnv lang φ ≤ langBoxUsing relEnv lang φ := by
  intro p hp
  apply (langBoxUsing_spec relEnv lang φ p).mpr
  intro q hqp
  exact hp q (Relation.ReflTransGen.single hqp)

/-! ## Positive and negative orientation examples -/

namespace Examples

inductive Node where
  | a | b | c
deriving DecidableEq

def edge : Node → Node → Prop
  | .a, .b => True
  | .b, .c => True
  | _, _ => False

/-- Two production steps put `c` in the forward cone of `a`. -/
theorem c_mem_forwardCone_a :
    Node.c ∈ forwardCone edge ({Node.a} : Set Node) := by
  refine ⟨Node.a, by simp, ?_⟩
  have hab : edge Node.a Node.b := by simp [edge]
  have hbc : edge Node.b Node.c := by simp [edge]
  exact Relation.ReflTransGen.trans
    (Relation.ReflTransGen.single hab)
    (Relation.ReflTransGen.single hbc)

/-- The same path puts `a` in the demand cone of goal `c`. -/
theorem a_mem_backwardCone_c :
    Node.a ∈ backwardCone edge ({Node.c} : Set Node) := by
  refine ⟨Node.c, by simp, ?_⟩
  have hab : edge Node.a Node.b := by simp [edge]
  have hbc : edge Node.b Node.c := by simp [edge]
  exact Relation.ReflTransGen.trans
    (Relation.ReflTransGen.single hab)
    (Relation.ReflTransGen.single hbc)

/-- A one-step diamond cannot see the two-step demand. This prevents an
accidental identification of OSLF's one-step modality with a full cone. -/
theorem a_not_mem_one_step_demand_c :
    Node.a ∉ stepImage (Function.swap edge) ({Node.c} : Set Node) := by
  simp [stepImage, edge, Function.swap]

end Examples

end Mettapedia.Machines
