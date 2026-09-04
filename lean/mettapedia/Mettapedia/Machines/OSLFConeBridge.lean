import Mettapedia.Machines.ConeDuality
import Mettapedia.OSLF.Framework.TypeSynthesis
import Mettapedia.OSLF.Framework.GSLTQuotientCoherence

/-!
# OSLF modalities and production/demand cones

This module pins the variance between the one-step OSLF modalities generated
from a `LanguageDef` and the reflexive-transitive cones of its semantic
production relation on equation classes.

For a reduction `[p] ⟶ [q]`, `langDiamond φ p` asks whether a successor class
`[q]` satisfies `φ`. As a transformer on semantic predicates, this is the
one-step image under the *reversed* relation. Its reachability closure is
therefore `backwardCone`, not `forwardCone`. Dually, the reachability box is
`onlyFrom`.

This distinction matters operationally: a multi-step demand cone can contain a
state that the one-step diamond does not. The examples at the end retain that
negative discriminator.
-/

namespace Mettapedia.Machines

open Set
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.Framework.TypeSynthesis
open Mettapedia.GSLT
open Mettapedia.GSLT.IndexedOperational
open Mettapedia.OSLF.Framework.GSLTTypeSynthesis
open Mettapedia.OSLF.Framework.GSLTQuotientCoherence

/-- The semantic term carrier of a generated language is its authored pattern
carrier modulo the equations declared by the language. -/
abbrev LangSemanticTermUsing (relEnv : RelationEnv) (lang : LanguageDef) :=
  SemanticTerm (langGSLTUsing relEnv lang)

/-- The generated one-step diamond descends exactly to the step image under
the reversed semantic relation. This is the variance-correct set-transformer
view; no equation-blind OSLF is involved. -/
theorem langDiamondUsing_eq_stepImage_swap
    (relEnv : RelationEnv) (lang : LanguageDef)
    (φ : EquationPredicate (langGSLTUsing relEnv lang)) :
    descendPredicate (langGSLTUsing relEnv lang)
        (langDiamondUsing relEnv lang φ) =
      stepImage
        (Function.swap (SemanticStep (langGSLTUsing relEnv lang)))
        (descendPredicate (langGSLTUsing relEnv lang) φ) := by
  rw [show langDiamondUsing relEnv lang φ =
      semanticDiamond (langGSLTUsing relEnv lang) φ from rfl]
  rw [descend_semanticDiamond]
  ext source
  rw [equationQuotientDiamond, gsltDiamond_spec]
  change (∃ target,
      SemanticStep (langGSLTUsing relEnv lang) source target ∧
        descendPredicate (langGSLTUsing relEnv lang) φ target) ↔
    ∃ target,
      descendPredicate (langGSLTUsing relEnv lang) φ target ∧
        SemanticStep (langGSLTUsing relEnv lang) source target
  constructor
  · rintro ⟨target, step, holds⟩
    exact ⟨target, holds, step⟩
  · rintro ⟨target, holds, step⟩
    exact ⟨target, step, holds⟩

/-- The generated one-step box descends to universal quantification over
immediate predecessor classes. -/
theorem langBoxUsing_eq_immediateOnlyFrom
    (relEnv : RelationEnv) (lang : LanguageDef)
    (φ : EquationPredicate (langGSLTUsing relEnv lang)) :
    descendPredicate (langGSLTUsing relEnv lang)
        (langBoxUsing relEnv lang φ) =
      {target | ∀ source,
        SemanticStep (langGSLTUsing relEnv lang) source target →
          descendPredicate (langGSLTUsing relEnv lang) φ source} := by
  rw [show langBoxUsing relEnv lang φ =
      semanticBox (langGSLTUsing relEnv lang) φ from rfl]
  rw [descend_semanticBox]
  ext target
  exact gsltBox_spec (semanticTheory (langGSLTUsing relEnv lang))
    (descendPredicate (langGSLTUsing relEnv lang) φ) target

/-- Reflexive-transitive demand modality for a `LanguageDef`: states that can
reach a demanded semantic state satisfying `φ`. -/
def langDiamondStarUsing (relEnv : RelationEnv) (lang : LanguageDef) :
    (LangSemanticTermUsing relEnv lang → Prop) →
      (LangSemanticTermUsing relEnv lang → Prop) :=
  backwardCone (SemanticStep (langGSLTUsing relEnv lang))

/-- Reflexive-transitive provenance box for a `LanguageDef`: states all of
whose reachable semantic predecessors satisfy `φ`. -/
def langBoxStarUsing (relEnv : RelationEnv) (lang : LanguageDef) :
    (LangSemanticTermUsing relEnv lang → Prop) →
      (LangSemanticTermUsing relEnv lang → Prop) :=
  onlyFrom (SemanticStep (langGSLTUsing relEnv lang))

/-- Default-environment reachability diamond. -/
def langDiamondStar (lang : LanguageDef) :
    (LangSemanticTermUsing RelationEnv.empty lang → Prop) →
      (LangSemanticTermUsing RelationEnv.empty lang → Prop) :=
  langDiamondStarUsing RelationEnv.empty lang

/-- Default-environment reachability box. -/
def langBoxStar (lang : LanguageDef) :
    (LangSemanticTermUsing RelationEnv.empty lang → Prop) →
      (LangSemanticTermUsing RelationEnv.empty lang → Prop) :=
  langBoxStarUsing RelationEnv.empty lang

@[simp] theorem langDiamondStarUsing_spec
    (relEnv : RelationEnv) (lang : LanguageDef)
    (φ : LangSemanticTermUsing relEnv lang → Prop)
    (source : LangSemanticTermUsing relEnv lang) :
    langDiamondStarUsing relEnv lang φ source ↔
      ∃ target, φ target ∧
        Reaches (SemanticStep (langGSLTUsing relEnv lang)) source target :=
  Iff.rfl

@[simp] theorem langBoxStarUsing_spec
    (relEnv : RelationEnv) (lang : LanguageDef)
    (φ : LangSemanticTermUsing relEnv lang → Prop)
    (target : LangSemanticTermUsing relEnv lang) :
    langBoxStarUsing relEnv lang φ target ↔
      ∀ source,
        Reaches (SemanticStep (langGSLTUsing relEnv lang)) source target →
          φ source :=
  Iff.rfl

/-- Demand over reachability is forward production in the opposite
direction. -/
theorem langDiamondStarUsing_eq_forwardCone_swap
    (relEnv : RelationEnv) (lang : LanguageDef)
    (φ : LangSemanticTermUsing relEnv lang → Prop) :
    langDiamondStarUsing relEnv lang φ =
      forwardCone
        (Function.swap (SemanticStep (langGSLTUsing relEnv lang))) φ :=
  backwardCone_eq_forwardCone_swap _ _

/-- The reachability diamond and provenance box retain the generic cone
Galois connection. -/
theorem langReachabilityGaloisUsing
    (relEnv : RelationEnv) (lang : LanguageDef) :
    GaloisConnection (langDiamondStarUsing relEnv lang)
      (langBoxStarUsing relEnv lang) :=
  gc_backward (SemanticStep (langGSLTUsing relEnv lang))

/-- Every immediate demand is a reachable demand. -/
theorem langDiamondUsing_le_langDiamondStarUsing
    (relEnv : RelationEnv) (lang : LanguageDef)
    (φ : EquationPredicate (langGSLTUsing relEnv lang)) :
    descendPredicate (langGSLTUsing relEnv lang)
        (langDiamondUsing relEnv lang φ) ≤
      langDiamondStarUsing relEnv lang
        (descendPredicate (langGSLTUsing relEnv lang) φ) := by
  intro source holds
  rw [langDiamondUsing_eq_stepImage_swap] at holds
  obtain ⟨target, targetHolds, step⟩ := holds
  exact ⟨target, targetHolds, Relation.ReflTransGen.single step⟩

/-- Reachability provenance is stronger than immediate-predecessor
provenance. -/
theorem langBoxStarUsing_le_langBoxUsing
    (relEnv : RelationEnv) (lang : LanguageDef)
    (φ : EquationPredicate (langGSLTUsing relEnv lang)) :
    langBoxStarUsing relEnv lang
        (descendPredicate (langGSLTUsing relEnv lang) φ) ≤
      descendPredicate (langGSLTUsing relEnv lang)
        (langBoxUsing relEnv lang φ) := by
  intro target holds
  rw [langBoxUsing_eq_immediateOnlyFrom]
  intro source step
  exact holds source (Relation.ReflTransGen.single step)

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
