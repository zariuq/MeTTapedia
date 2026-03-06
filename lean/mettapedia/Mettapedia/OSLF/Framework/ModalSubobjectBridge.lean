import Mettapedia.OSLF.Framework.CategoryBridge
import Mettapedia.OSLF.Framework.BeckChevalleyOSLF
import Mettapedia.OSLF.Framework.ToposReduction
import Mettapedia.OSLF.Framework.MeTTaFullLegacyInstance
import Mettapedia.OSLF.Framework.ConstructorCategory
import Mettapedia.OSLF.Framework.TypeSynthesis
import Mettapedia.OSLF.Framework.OSLFNTTTheoryClosure

/-!
# Modal Subobject Bridge (Presheaf/Subobject Route)

Canonical theorem wrappers for modal objects built as representable-fiber
subobjects:

- membership iff characterization,
- naturality under reindexing,
- Beck-Chevalley endpoint over pullback squares,
- BC + reduction-graph witness endpoint.

This module intentionally reuses existing `CategoryBridge` and
`BeckChevalleyOSLF` primitives without introducing alternative semantics.
-/

namespace Mettapedia.OSLF.Framework.ModalSubobjectBridge

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.Framework.ConstructorCategory
open Mettapedia.OSLF.Framework.TypeSynthesis
open Mettapedia.OSLF.Framework.CategoryBridge
open Mettapedia.OSLF.Framework.BeckChevalleyOSLF
open Mettapedia.OSLF.Framework.OSLFNTTTheoryClosure
open Mettapedia.Logic.OSLFEvidenceSemantics

section Canonical

/-- Canonical modal object at the fiber level (predicate-induced representable
subfunctor). -/
noncomputable abbrev modalFiberOfPatternPred
    (lang : LanguageDef) (s : LangSort lang)
    (seed : Pattern) (φ : Pattern → Prop)
    (hNat : languageSortPredNaturality lang s seed φ) :
    languageSortFiber lang s :=
  languageSortFiber_ofPatternPred lang s seed φ hNat

/-- Canonical modal object at the subobject level. -/
noncomputable abbrev modalSubobjectOfPatternPred
    (lang : LanguageDef) (s : LangSort lang)
    (seed : Pattern) (φ : Pattern → Prop)
    (hNat : languageSortPredNaturality lang s seed φ) :
    CategoryTheory.Subobject (languageSortRepresentableObj lang s) :=
  languageSortFiber_ofPatternPred_subobject lang s seed φ hNat

/-- View the canonical modal subobject back as its representable fiber. -/
noncomputable abbrev modalSubobjectAsFiber
    (lang : LanguageDef) (s : LangSort lang)
    (seed : Pattern) (φ : Pattern → Prop)
    (hNat : languageSortPredNaturality lang s seed φ) :
    languageSortFiber lang s :=
  (CategoryTheory.Subfunctor.orderIsoSubobject
    (F := languageSortRepresentableObj lang s)).invFun
      (modalSubobjectOfPatternPred lang s seed φ hNat)

/-- Canonical equivalence: converting the modal subobject back to a fiber returns
the original predicate-induced representable fiber. -/
theorem modalSubobjectAsFiber_eq_modalFiber
    (lang : LanguageDef) (s : LangSort lang)
    (seed : Pattern) (φ : Pattern → Prop)
    (hNat : languageSortPredNaturality lang s seed φ) :
    modalSubobjectAsFiber lang s seed φ hNat =
      modalFiberOfPatternPred lang s seed φ hNat := by
  simpa [modalSubobjectAsFiber, modalSubobjectOfPatternPred, modalFiberOfPatternPred] using
    (CategoryTheory.Subfunctor.orderIsoSubobject
      (F := languageSortRepresentableObj lang s)).toEquiv.left_inv
      (languageSortFiber_ofPatternPred lang s seed φ hNat)

/-- Membership iff theorem package for the canonical modal object. -/
theorem modalFiber_mem_iff
    (lang : LanguageDef) (s : LangSort lang)
    (seed : Pattern) (φ : Pattern → Prop)
    (hNat : languageSortPredNaturality lang s seed φ)
    {X : Opposite (ConstructorObj lang)}
    (h : (languageSortRepresentableObj lang s).obj X) :
    h ∈ (modalFiberOfPatternPred lang s seed φ hNat).obj X
      ↔
    φ (pathSem lang h seed) := by
  simpa [modalFiberOfPatternPred] using
    (languageSortFiber_ofPatternPred_mem_iff lang s seed φ hNat h)

/-- Subobject-level membership iff theorem package for the canonical modal object.

Membership is stated on the subobject viewed as a representable fiber via
`Sub(y(s)) ≃ Subfunctor(y(s))`. -/
theorem modalSubobject_mem_iff
    (lang : LanguageDef) (s : LangSort lang)
    (seed : Pattern) (φ : Pattern → Prop)
    (hNat : languageSortPredNaturality lang s seed φ)
    {X : Opposite (ConstructorObj lang)}
    (h : (languageSortRepresentableObj lang s).obj X) :
    h ∈ (modalSubobjectAsFiber lang s seed φ hNat).obj X
      ↔
    φ (pathSem lang h seed) := by
  simpa [modalSubobjectAsFiber_eq_modalFiber (lang := lang) (s := s)
      (seed := seed) (φ := φ) (hNat := hNat)] using
    (modalFiber_mem_iff lang s seed φ hNat h)

/-- Naturality endpoint: representable reindexing preserves canonical modal-fiber
membership. -/
theorem modalFiber_map_mem
    (lang : LanguageDef) (s : LangSort lang)
    (seed : Pattern) (φ : Pattern → Prop)
    (hNat : languageSortPredNaturality lang s seed φ)
    {X Y : Opposite (ConstructorObj lang)}
    (f : X ⟶ Y)
    (h : (languageSortRepresentableObj lang s).obj X)
    (hh : h ∈ (modalFiberOfPatternPred lang s seed φ hNat).obj X) :
    ((languageSortRepresentableObj lang s).map f h) ∈
      (modalFiberOfPatternPred lang s seed φ hNat).obj Y := by
  simpa [modalFiberOfPatternPred] using
    (languageSortFiber_ofPatternPred_map_mem
      lang s seed φ hNat f h hh)

/-- Substitution/reindexing transport for canonical modal subobjects, stated on
the subobject viewed as a representable fiber. -/
theorem modalSubobject_subst_map_mem
    (lang : LanguageDef) (s : LangSort lang)
    (seed : Pattern) (φ : Pattern → Prop)
    (hNat : languageSortPredNaturality lang s seed φ)
    {X Y : Opposite (ConstructorObj lang)}
    (f : X ⟶ Y)
    (h : (languageSortRepresentableObj lang s).obj X)
    (hh : h ∈ (modalSubobjectAsFiber lang s seed φ hNat).obj X) :
    ((languageSortRepresentableObj lang s).map f h) ∈
      (modalSubobjectAsFiber lang s seed φ hNat).obj Y := by
  have hhFiber :
      h ∈ (modalFiberOfPatternPred lang s seed φ hNat).obj X := by
    simpa [modalSubobjectAsFiber_eq_modalFiber (lang := lang) (s := s)
      (seed := seed) (φ := φ) (hNat := hNat)] using hh
  have hMap :
      ((languageSortRepresentableObj lang s).map f h) ∈
        (modalFiberOfPatternPred lang s seed φ hNat).obj Y :=
    modalFiber_map_mem lang s seed φ hNat f h hhFiber
  simpa [modalSubobjectAsFiber_eq_modalFiber (lang := lang) (s := s)
    (seed := seed) (φ := φ) (hNat := hNat)] using hMap

/-- Policy object linking modal-subobject transport assumptions to the controlled
semE step policy contract. -/
structure ModalSubobjectControlledPolicy
    (lang : LanguageDef) (s : LangSort lang)
    (seed q : Pattern)
    (relEnv : RelationEnv)
    (I : Mettapedia.Logic.OSLFEvidenceSemantics.EvidenceAtomSem) where
  pathLiftPkg : CommDiPathSemLiftPkg lang s seed q
  semEPolicy : ControlledStepPolicy relEnv I

/-- Build a modal-subobject controlled policy directly from a real
substitution/path-order square and a controlled-step policy witness. -/
def ModalSubobjectControlledPolicy.of_pathOrder
    (lang : LanguageDef) (s : LangSort lang)
    (seed q : Pattern)
    (relEnv : RelationEnv)
    (I : Mettapedia.Logic.OSLFEvidenceSemantics.EvidenceAtomSem)
    (hPathOrder :
      ∀ {a b : LangSort lang}
        (g : SortPath lang a b) (h : SortPath lang b s),
          pathSem lang g (pathSem lang h seed) = pathSem lang (g.comp h) seed)
    (hSemE : ControlledStepPolicy relEnv I) :
    ModalSubobjectControlledPolicy lang s seed q relEnv I where
  pathLiftPkg :=
    commDiPathSemLiftPkg_of_pathSem_comm_subst_and_path_order
      lang s seed q hPathOrder
  semEPolicy := hSemE

/-- Reuse the same modal-subobject policy object to discharge semE one-step
monotonicity obligations for policy-indexed controlled fragments. -/
theorem modalSubobject_policy_semE_step_mono
    (lang : LanguageDef) (s : LangSort lang)
    (seed q : Pattern)
    (relEnv : RelationEnv)
    (I : Mettapedia.Logic.OSLFEvidenceSemantics.EvidenceAtomSem)
    (policy : ModalSubobjectControlledPolicy lang s seed q relEnv I)
    {φf : Mettapedia.OSLF.Formula.OSLFFormula}
    (hφf : StepEvidenceControlledByPolicy policy.semEPolicy φf)
    {p qStep : Pattern}
    (hstep : OSLFTheoryStep relEnv p qStep) :
    semE (OSLFTheoryStep relEnv) I φf p ≤
      semE (OSLFTheoryStep relEnv) I φf qStep := by
  exact semE_step_mono_of_policy
    (policy := policy.semEPolicy)
    (hφ := hφf)
    hstep

/-- Canonical COMM Beck-Chevalley endpoint over representables using the
path-semantics lift package. -/
theorem modalSubobject_commDi_beckChevalley_of_pathSemLiftPkg
    (lang : LanguageDef) (s : LangSort lang)
    (seed q : Pattern) (φ : Pattern → Prop)
    (hPkg : CommDiPathSemLiftPkg lang s seed q)
    {P B D : CategoryTheory.Functor (Opposite (ConstructorObj lang)) (Type _)}
    (pi1 : P ⟶ (languageSortRepresentableObj lang s))
    (pi2 : P ⟶ B)
    (f : (languageSortRepresentableObj lang s) ⟶ D)
    (g : B ⟶ D)
    (hpb : CategoryTheory.IsPullback pi1 pi2 f g)
    (hf : CategoryTheory.Mono f) (hpi2 : CategoryTheory.Mono pi2) :
    (CategoryTheory.Subobject.map pi2).obj
        ((CategoryTheory.Subobject.pullback pi1).obj
          (modalSubobjectOfPatternPred lang s seed
            (commDi q (PathSemClosedPred lang φ))
            (languageSortPredNaturality_commDi_pathSemClosed_of_pkg
              lang s seed q φ hPkg)))
      =
    (CategoryTheory.Subobject.pullback g).obj
        ((CategoryTheory.Subobject.map f).obj
          (modalSubobjectOfPatternPred lang s seed
            (commDi q (PathSemClosedPred lang φ))
            (languageSortPredNaturality_commDi_pathSemClosed_of_pkg
              lang s seed q φ hPkg))) := by
  simpa [modalSubobjectOfPatternPred] using
    (representable_commDi_patternPred_beckChevalley_of_pathSemLiftPkg
      (lang := lang) (s := s) (seed := seed) (q := q) (φ := φ)
      (hPkg := hPkg)
      (pi1 := pi1) (pi2 := pi2) (f := f) (g := g)
      (hpb := hpb) (hf := hf) (hpi2 := hpi2))

/-- Canonical COMM Beck-Chevalley endpoint over representables, with path-lift
package synthesized from the language path-order law. -/
theorem modalSubobject_commDi_beckChevalley_of_pathOrder
    (lang : LanguageDef) (s : LangSort lang)
    (seed q : Pattern) (φ : Pattern → Prop)
    (hPathOrder :
      ∀ {a b : LangSort lang}
        (g : SortPath lang a b) (h : SortPath lang b s),
          pathSem lang g (pathSem lang h seed) = pathSem lang (g.comp h) seed)
    {P B D : CategoryTheory.Functor (Opposite (ConstructorObj lang)) (Type _)}
    (pi1 : P ⟶ (languageSortRepresentableObj lang s))
    (pi2 : P ⟶ B)
    (f : (languageSortRepresentableObj lang s) ⟶ D)
    (g : B ⟶ D)
    (hpb : CategoryTheory.IsPullback pi1 pi2 f g)
    (hf : CategoryTheory.Mono f) (hpi2 : CategoryTheory.Mono pi2) :
    (CategoryTheory.Subobject.map pi2).obj
        ((CategoryTheory.Subobject.pullback pi1).obj
          (modalSubobjectOfPatternPred lang s seed
            (commDi q (PathSemClosedPred lang φ))
            (languageSortPredNaturality_commDi_pathSemClosed_of_pkg
              lang s seed q φ
              (commDiPathSemLiftPkg_of_pathSem_comm_subst_and_path_order
                lang s seed q hPathOrder))))
      =
    (CategoryTheory.Subobject.pullback g).obj
        ((CategoryTheory.Subobject.map f).obj
          (modalSubobjectOfPatternPred lang s seed
            (commDi q (PathSemClosedPred lang φ))
            (languageSortPredNaturality_commDi_pathSemClosed_of_pkg
              lang s seed q φ
              (commDiPathSemLiftPkg_of_pathSem_comm_subst_and_path_order
                lang s seed q hPathOrder)))) := by
  exact modalSubobject_commDi_beckChevalley_of_pathSemLiftPkg
    (lang := lang) (s := s) (seed := seed) (q := q) (φ := φ)
    (hPkg := commDiPathSemLiftPkg_of_pathSem_comm_subst_and_path_order
      lang s seed q hPathOrder)
    (pi1 := pi1) (pi2 := pi2) (f := f) (g := g)
    (hpb := hpb) (hf := hf) (hpi2 := hpi2)

/-- Unified canonical endpoint:
COMM Beck-Chevalley over representables plus explicit reduction-graph witness
transport for the induced `◇` side. -/
theorem modalSubobject_commDi_bc_graph_endpoint_of_pathSemLiftPkg
    (lang : LanguageDef) (s : LangSort lang)
    (seed q : Pattern) (φ : Pattern → Prop)
    (hPkg : CommDiPathSemLiftPkg lang s seed q)
    {P B D : CategoryTheory.Functor (Opposite (ConstructorObj lang)) (Type _)}
    (pi1 : P ⟶ (languageSortRepresentableObj lang s))
    (pi2 : P ⟶ B)
    (f : (languageSortRepresentableObj lang s) ⟶ D)
    (g : B ⟶ D)
    (hpb : CategoryTheory.IsPullback pi1 pi2 f g)
    (hf : CategoryTheory.Mono f) (hpi2 : CategoryTheory.Mono pi2)
    (relEnv : RelationEnv)
    {X : Opposite (ConstructorObj lang)} (p : Pattern) :
    ((CategoryTheory.Subobject.map pi2).obj
        ((CategoryTheory.Subobject.pullback pi1).obj
          (modalSubobjectOfPatternPred lang s seed
            (commDi q (PathSemClosedPred lang φ))
            (languageSortPredNaturality_commDi_pathSemClosed_of_pkg
              lang s seed q φ hPkg)))
      =
    (CategoryTheory.Subobject.pullback g).obj
        ((CategoryTheory.Subobject.map f).obj
          (modalSubobjectOfPatternPred lang s seed
            (commDi q (PathSemClosedPred lang φ))
            (languageSortPredNaturality_commDi_pathSemClosed_of_pkg
              lang s seed q φ hPkg))))
    ∧
    (langDiamondUsing relEnv lang
      (commDi q (PathSemClosedPred lang φ)) p ↔
      ∃ e : (Mettapedia.OSLF.Framework.ToposReduction.reductionGraphUsing
        (C := ConstructorObj lang) relEnv lang).Edge.obj X,
        ((Mettapedia.OSLF.Framework.ToposReduction.reductionGraphUsing
          (C := ConstructorObj lang) relEnv lang).source.app X e).down = p ∧
        ∃ u : Pattern,
          Mettapedia.OSLF.MeTTaIL.Substitution.commSubst u q =
            ((Mettapedia.OSLF.Framework.ToposReduction.reductionGraphUsing
              (C := ConstructorObj lang) relEnv lang).target.app X e).down ∧
          PathSemClosedPred lang φ u) := by
  simpa [modalSubobjectOfPatternPred] using
    (representable_commDi_bc_and_graphDiamond_of_pathSemLiftPkg
      (lang := lang) (s := s) (seed := seed) (q := q) (φ := φ)
      (hPkg := hPkg)
      (pi1 := pi1) (pi2 := pi2) (f := f) (g := g)
      (hpb := hpb) (hf := hf) (hpi2 := hpi2)
      (relEnv := relEnv) (X := X) (p := p))

/-- Unified canonical endpoint over real substitution squares:
COMM Beck-Chevalley plus reduction-graph witness transport, with path-lift
package synthesized from path-order. -/
theorem modalSubobject_commDi_bc_graph_endpoint_of_pathOrder
    (lang : LanguageDef) (s : LangSort lang)
    (seed q : Pattern) (φ : Pattern → Prop)
    (hPathOrder :
      ∀ {a b : LangSort lang}
        (g : SortPath lang a b) (h : SortPath lang b s),
          pathSem lang g (pathSem lang h seed) = pathSem lang (g.comp h) seed)
    {P B D : CategoryTheory.Functor (Opposite (ConstructorObj lang)) (Type _)}
    (pi1 : P ⟶ (languageSortRepresentableObj lang s))
    (pi2 : P ⟶ B)
    (f : (languageSortRepresentableObj lang s) ⟶ D)
    (g : B ⟶ D)
    (hpb : CategoryTheory.IsPullback pi1 pi2 f g)
    (hf : CategoryTheory.Mono f) (hpi2 : CategoryTheory.Mono pi2)
    (relEnv : RelationEnv)
    {X : Opposite (ConstructorObj lang)} (p : Pattern) :
    ((CategoryTheory.Subobject.map pi2).obj
        ((CategoryTheory.Subobject.pullback pi1).obj
          (modalSubobjectOfPatternPred lang s seed
            (commDi q (PathSemClosedPred lang φ))
            (languageSortPredNaturality_commDi_pathSemClosed_of_pkg
              lang s seed q φ
              (commDiPathSemLiftPkg_of_pathSem_comm_subst_and_path_order
                lang s seed q hPathOrder))))
      =
    (CategoryTheory.Subobject.pullback g).obj
        ((CategoryTheory.Subobject.map f).obj
          (modalSubobjectOfPatternPred lang s seed
            (commDi q (PathSemClosedPred lang φ))
            (languageSortPredNaturality_commDi_pathSemClosed_of_pkg
              lang s seed q φ
              (commDiPathSemLiftPkg_of_pathSem_comm_subst_and_path_order
                lang s seed q hPathOrder)))))
    ∧
    (langDiamondUsing relEnv lang
      (commDi q (PathSemClosedPred lang φ)) p ↔
      ∃ e : (Mettapedia.OSLF.Framework.ToposReduction.reductionGraphUsing
        (C := ConstructorObj lang) relEnv lang).Edge.obj X,
        ((Mettapedia.OSLF.Framework.ToposReduction.reductionGraphUsing
          (C := ConstructorObj lang) relEnv lang).source.app X e).down = p ∧
        ∃ u : Pattern,
          Mettapedia.OSLF.MeTTaIL.Substitution.commSubst u q =
            ((Mettapedia.OSLF.Framework.ToposReduction.reductionGraphUsing
              (C := ConstructorObj lang) relEnv lang).target.app X e).down ∧
          PathSemClosedPred lang φ u) := by
  exact modalSubobject_commDi_bc_graph_endpoint_of_pathSemLiftPkg
    (lang := lang) (s := s) (seed := seed) (q := q) (φ := φ)
    (hPkg := commDiPathSemLiftPkg_of_pathSem_comm_subst_and_path_order
      lang s seed q hPathOrder)
    (pi1 := pi1) (pi2 := pi2) (f := f) (g := g)
    (hpb := hpb) (hf := hf) (hpi2 := hpi2)
    (relEnv := relEnv) (X := X) (p := p)

/-- Modal-subobject BC+graph endpoint consumed through a unified policy object. -/
theorem modalSubobject_commDi_bc_graph_endpoint_of_policy
    (lang : LanguageDef) (s : LangSort lang)
    (seed q : Pattern) (φ : Pattern → Prop)
    (relEnv : RelationEnv)
    (I : Mettapedia.Logic.OSLFEvidenceSemantics.EvidenceAtomSem)
    (policy : ModalSubobjectControlledPolicy lang s seed q relEnv I)
    {P B D : CategoryTheory.Functor (Opposite (ConstructorObj lang)) (Type _)}
    (pi1 : P ⟶ (languageSortRepresentableObj lang s))
    (pi2 : P ⟶ B)
    (f : (languageSortRepresentableObj lang s) ⟶ D)
    (g : B ⟶ D)
    (hpb : CategoryTheory.IsPullback pi1 pi2 f g)
    (hf : CategoryTheory.Mono f) (hpi2 : CategoryTheory.Mono pi2)
    {X : Opposite (ConstructorObj lang)} (p : Pattern) :
    ((CategoryTheory.Subobject.map pi2).obj
        ((CategoryTheory.Subobject.pullback pi1).obj
          (modalSubobjectOfPatternPred lang s seed
            (commDi q (PathSemClosedPred lang φ))
            (languageSortPredNaturality_commDi_pathSemClosed_of_pkg
              lang s seed q φ policy.pathLiftPkg)))
      =
    (CategoryTheory.Subobject.pullback g).obj
        ((CategoryTheory.Subobject.map f).obj
          (modalSubobjectOfPatternPred lang s seed
            (commDi q (PathSemClosedPred lang φ))
            (languageSortPredNaturality_commDi_pathSemClosed_of_pkg
              lang s seed q φ policy.pathLiftPkg))))
    ∧
    (langDiamondUsing relEnv lang
      (commDi q (PathSemClosedPred lang φ)) p ↔
      ∃ e : (Mettapedia.OSLF.Framework.ToposReduction.reductionGraphUsing
        (C := ConstructorObj lang) relEnv lang).Edge.obj X,
        ((Mettapedia.OSLF.Framework.ToposReduction.reductionGraphUsing
          (C := ConstructorObj lang) relEnv lang).source.app X e).down = p ∧
        ∃ u : Pattern,
          Mettapedia.OSLF.MeTTaIL.Substitution.commSubst u q =
            ((Mettapedia.OSLF.Framework.ToposReduction.reductionGraphUsing
              (C := ConstructorObj lang) relEnv lang).target.app X e).down ∧
          PathSemClosedPred lang φ u) := by
  exact modalSubobject_commDi_bc_graph_endpoint_of_pathSemLiftPkg
    (lang := lang) (s := s) (seed := seed) (q := q) (φ := φ)
    (hPkg := policy.pathLiftPkg)
    (pi1 := pi1) (pi2 := pi2) (f := f) (g := g)
    (hpb := hpb) (hf := hf) (hpi2 := hpi2)
    (relEnv := relEnv) (X := X) (p := p)

end Canonical

section MeTTaFullConcrete

/-- Concrete MeTTaFull endpoint over real substitution/path-order squares:
canonical modal subobject BC + graph witness transport. -/
theorem mettaFull_modalSubobject_commDi_bc_graph_endpoint
    (seed q : Pattern) (φ : Pattern → Prop)
    {P B D : CategoryTheory.Functor (Opposite (ConstructorObj Mettapedia.OSLF.Framework.MeTTaFullInstance.mettaFull)) (Type _)}
    (pi1 : P ⟶
      (languageSortRepresentableObj Mettapedia.OSLF.Framework.MeTTaFullInstance.mettaFull
        Mettapedia.OSLF.Framework.MeTTaFullInstance.mettaState))
    (pi2 : P ⟶ B)
    (f :
      (languageSortRepresentableObj Mettapedia.OSLF.Framework.MeTTaFullInstance.mettaFull
        Mettapedia.OSLF.Framework.MeTTaFullInstance.mettaState) ⟶ D)
    (g : B ⟶ D)
    (hpb : CategoryTheory.IsPullback pi1 pi2 f g)
    (hf : CategoryTheory.Mono f) (hpi2 : CategoryTheory.Mono pi2)
    (relEnv : RelationEnv)
    {X : Opposite (ConstructorObj Mettapedia.OSLF.Framework.MeTTaFullInstance.mettaFull)}
    (p : Pattern) :
    ((CategoryTheory.Subobject.map pi2).obj
        ((CategoryTheory.Subobject.pullback pi1).obj
          (modalSubobjectOfPatternPred
            Mettapedia.OSLF.Framework.MeTTaFullInstance.mettaFull
            Mettapedia.OSLF.Framework.MeTTaFullInstance.mettaState
            seed
            (commDi q
              (PathSemClosedPred Mettapedia.OSLF.Framework.MeTTaFullInstance.mettaFull φ))
            (languageSortPredNaturality_commDi_pathSemClosed_of_pkg
              Mettapedia.OSLF.Framework.MeTTaFullInstance.mettaFull
              Mettapedia.OSLF.Framework.MeTTaFullInstance.mettaState
              seed q φ
              (commDiPathSemLiftPkg_of_pathSem_comm_subst_and_path_order
                Mettapedia.OSLF.Framework.MeTTaFullInstance.mettaFull
                Mettapedia.OSLF.Framework.MeTTaFullInstance.mettaState
                seed q
                (Mettapedia.OSLF.Framework.MeTTaFullInstance.mettaFull_pathOrder seed)))))
      =
    (CategoryTheory.Subobject.pullback g).obj
        ((CategoryTheory.Subobject.map f).obj
          (modalSubobjectOfPatternPred
            Mettapedia.OSLF.Framework.MeTTaFullInstance.mettaFull
            Mettapedia.OSLF.Framework.MeTTaFullInstance.mettaState
            seed
            (commDi q
              (PathSemClosedPred Mettapedia.OSLF.Framework.MeTTaFullInstance.mettaFull φ))
            (languageSortPredNaturality_commDi_pathSemClosed_of_pkg
              Mettapedia.OSLF.Framework.MeTTaFullInstance.mettaFull
              Mettapedia.OSLF.Framework.MeTTaFullInstance.mettaState
              seed q φ
              (commDiPathSemLiftPkg_of_pathSem_comm_subst_and_path_order
                Mettapedia.OSLF.Framework.MeTTaFullInstance.mettaFull
                Mettapedia.OSLF.Framework.MeTTaFullInstance.mettaState
                seed q
                (Mettapedia.OSLF.Framework.MeTTaFullInstance.mettaFull_pathOrder seed))))))
    ∧
    (langDiamondUsing relEnv Mettapedia.OSLF.Framework.MeTTaFullInstance.mettaFull
      (commDi q
        (PathSemClosedPred Mettapedia.OSLF.Framework.MeTTaFullInstance.mettaFull φ)) p ↔
      ∃ e : (Mettapedia.OSLF.Framework.ToposReduction.reductionGraphUsing
        (C := ConstructorObj Mettapedia.OSLF.Framework.MeTTaFullInstance.mettaFull)
        relEnv Mettapedia.OSLF.Framework.MeTTaFullInstance.mettaFull).Edge.obj X,
        ((Mettapedia.OSLF.Framework.ToposReduction.reductionGraphUsing
          (C := ConstructorObj Mettapedia.OSLF.Framework.MeTTaFullInstance.mettaFull)
          relEnv Mettapedia.OSLF.Framework.MeTTaFullInstance.mettaFull).source.app X e).down = p ∧
        ∃ u : Pattern,
          Mettapedia.OSLF.MeTTaIL.Substitution.commSubst u q =
            ((Mettapedia.OSLF.Framework.ToposReduction.reductionGraphUsing
              (C := ConstructorObj Mettapedia.OSLF.Framework.MeTTaFullInstance.mettaFull)
              relEnv Mettapedia.OSLF.Framework.MeTTaFullInstance.mettaFull).target.app X e).down ∧
          PathSemClosedPred Mettapedia.OSLF.Framework.MeTTaFullInstance.mettaFull φ u) := by
  exact modalSubobject_commDi_bc_graph_endpoint_of_pathSemLiftPkg
    (lang := Mettapedia.OSLF.Framework.MeTTaFullInstance.mettaFull)
    (s := Mettapedia.OSLF.Framework.MeTTaFullInstance.mettaState)
    (seed := seed) (q := q) (φ := φ)
    (hPkg :=
      commDiPathSemLiftPkg_of_pathSem_comm_subst_and_path_order
        Mettapedia.OSLF.Framework.MeTTaFullInstance.mettaFull
        Mettapedia.OSLF.Framework.MeTTaFullInstance.mettaState
        seed q
        (Mettapedia.OSLF.Framework.MeTTaFullInstance.mettaFull_pathOrder seed))
    (pi1 := pi1) (pi2 := pi2) (f := f) (g := g)
    (hpb := hpb) (hf := hf) (hpi2 := hpi2)
    (relEnv := relEnv) (X := X) (p := p)

/-- Legacy-canonical alias for the concrete MeTTaFull modal-subobject endpoint. -/
abbrev mettaFullLegacy_modalSubobject_commDi_bc_graph_endpoint :=
  mettaFull_modalSubobject_commDi_bc_graph_endpoint

end MeTTaFullConcrete

end Mettapedia.OSLF.Framework.ModalSubobjectBridge
