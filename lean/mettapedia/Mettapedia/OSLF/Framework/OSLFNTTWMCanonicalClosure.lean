import Mettapedia.OSLF.Framework.ModalSubobjectBridge
import Mettapedia.OSLF.Framework.OSLFNTTWMBridge
import Mettapedia.OSLF.Framework.OSLFNTTTheoryClosure
import Mettapedia.OSLF.Framework.BeckChevalleyOSLF
import Mettapedia.OSLF.Framework.TypeSynthesis
import Mettapedia.OSLF.Framework.ConstructorCategory
import Mettapedia.OSLF.Framework.ToposTOGLBridge
import Mettapedia.Logic.PLNWorldModelFixpointClosure

/-!
# OSLF -> NTT -> WM Canonical Closure Endpoints

Composed theorem endpoints over the canonical presheaf/subobject modal semantics:

- canonical modal-subobject Beck-Chevalley + reduction-graph witness transport,
- policy-driven OSLF -> NTT -> WM evidence closure (step/star),
- one endpoint surface tying both together.
-/

namespace Mettapedia.OSLF.Framework.OSLFNTTWMCanonicalClosure

open CategoryTheory
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.Formula
open Mettapedia.CategoryTheory.PLNInstance
open Mettapedia.Logic.OSLFEvidenceSemantics
open Mettapedia.Logic.PLNWorldModel
open Mettapedia.Logic.PLNWorldModelCategoricalBridge.WMHyperdoctrine
open Mettapedia.OSLF.Framework.ConstructorCategory
open Mettapedia.OSLF.Framework.TypeSynthesis
open Mettapedia.OSLF.Framework.CategoryBridge
open Mettapedia.OSLF.Framework.BeckChevalleyOSLF
open Mettapedia.OSLF.Framework.ModalSubobjectBridge
open Mettapedia.OSLF.Framework.OSLFNTTTheoryClosure

universe u v

/-- Compact reusable context for formula-level canonical closure endpoints. -/
structure CanonicalClosureContext where
  lang : LanguageDef
  s : LangSort lang
  seed : Pattern
  qComm : Pattern
  φpred : Pattern → Prop
  relEnv : RelationEnv
  I : EvidenceAtomSem
  hPathOrder :
    ∀ {a b : LangSort lang}
      (g : SortPath lang a b) (h : SortPath lang b s),
        pathSem lang g (pathSem lang h seed) = pathSem lang (g.comp h) seed
  hSemEPolicy : ControlledStepPolicy relEnv I

namespace CanonicalClosureContext

/-- Canonical modal-subobject policy synthesized from path-order + semE policy. -/
def policy (ctx : CanonicalClosureContext) :
    ModalSubobjectControlledPolicy
      ctx.lang ctx.s ctx.seed ctx.qComm ctx.relEnv ctx.I :=
  ModalSubobjectControlledPolicy.of_pathOrder
    ctx.lang ctx.s ctx.seed ctx.qComm ctx.relEnv ctx.I
    ctx.hPathOrder ctx.hSemEPolicy

@[simp] theorem policy_semEPolicy (ctx : CanonicalClosureContext) :
    ctx.policy.semEPolicy = ctx.hSemEPolicy := rfl

end CanonicalClosureContext

/-- Reusable modal/representable Beck-Chevalley argument bundle for canonical
formula-to-WM star endpoints. -/
structure CanonicalModalSquare (ctx : CanonicalClosureContext) where
  Pm : CategoryTheory.Functor (Opposite (ConstructorObj ctx.lang)) (Type _)
  Bm : CategoryTheory.Functor (Opposite (ConstructorObj ctx.lang)) (Type _)
  Dm : CategoryTheory.Functor (Opposite (ConstructorObj ctx.lang)) (Type _)
  pi1m : Pm ⟶ (languageSortRepresentableObj ctx.lang ctx.s)
  pi2m : Pm ⟶ Bm
  fm : (languageSortRepresentableObj ctx.lang ctx.s) ⟶ Dm
  gm : Bm ⟶ Dm
  hpbm : CategoryTheory.IsPullback pi1m pi2m fm gm
  hfm : CategoryTheory.Mono fm
  hpi2m : CategoryTheory.Mono pi2m
  Xmodal : Opposite (ConstructorObj ctx.lang)
  pmodal : Pattern

/-- Reusable WM-hyperdoctrine categorical square bundle for canonical
formula-to-WM star endpoints. -/
structure CanonicalHyperSquare (ctx : CanonicalClosureContext) where
  H : Mettapedia.Logic.PLNWorldModelHyperdoctrine.WMHyperdoctrine.{u, v, 0, 0} SemEState
  P : H.Obj
  Aobj : H.Obj
  Bobj : H.Obj
  D : H.Obj
  pi1 : P ⟶ Aobj
  pi2 : P ⟶ Bobj
  fcat : Aobj ⟶ D
  gcat : Bobj ⟶ D
  hpb : CategoryTheory.IsPullback pi1 pi2 fcat gcat
  hmfcat : CategoryTheory.Mono fcat
  hmpi2 : CategoryTheory.Mono pi2

/-- Reusable formula payload bundle for canonical formula-to-WM star endpoints. -/
structure CanonicalFormulaArgs (ctx : CanonicalClosureContext) where
  queryOfAtom : String → Pattern → Pattern
  φf : OSLFFormula
  hφ : StepEvidenceControlledByPolicy ctx.hSemEPolicy φf
  Xobj : PLNObj
  Xgr : Opposite (Mettapedia.OSLF.Framework.ConstructorCategory.ConstructorObj
    Mettapedia.OSLF.Framework.MeTTaToNTT.mettaFull)

/-- Reusable endpoint goal bundle for compact canonical closure consumers.
This collapses the recurring `(p,q,hstar,φcat,hStrengthFromEvidence)` tail. -/
structure CanonicalGoalArgs
    (ctx : CanonicalClosureContext)
    (cat : CanonicalHyperSquare ctx)
    (fa : CanonicalFormulaArgs ctx) where
  p : Pattern
  q : Pattern
  hstar : OSLFTheoryStepStar ctx.relEnv p q
  φcat : cat.H.query cat.Bobj
  hStrengthFromEvidence :
    WMEvidenceObligation SemEState SemEQuery
      (semEState ctx.relEnv ctx.I fa.φf) p q →
    WMStrengthObligation SemEState SemEQuery
      (semEState ctx.relEnv ctx.I fa.φf) p q

/-- Extended bundled endpoint arguments: naturality + Π/Σ transport witnesses +
goal payload, sharing one reusable object across transport/fixpoint endpoints. -/
structure CanonicalTransportGoalArgs
    (ctx : CanonicalClosureContext)
    (modal : CanonicalModalSquare ctx)
    (cat : CanonicalHyperSquare ctx)
    (fa : CanonicalFormulaArgs ctx) where
  hφTop : languageSortPredNaturality ctx.lang ctx.s ctx.seed ctx.φpred
  χ : CategoryTheory.Subfunctor modal.Dm
  ψ : CategoryTheory.Subfunctor modal.Dm
  goal : CanonicalGoalArgs ctx cat fa

/-- Full composed star endpoint over canonical modal-subobject semantics. -/
theorem oslf_ntt_wm_star_sound
    (lang : LanguageDef) (s : LangSort lang)
    (seed qComm : Pattern) (φpred : Pattern → Prop)
    (relEnv : RelationEnv)
    (I : EvidenceAtomSem)
    (policy : ModalSubobjectControlledPolicy lang s seed qComm relEnv I)
    {Pm Bm Dm : CategoryTheory.Functor (Opposite (ConstructorObj lang)) (Type _)}
    (pi1m : Pm ⟶ (languageSortRepresentableObj lang s))
    (pi2m : Pm ⟶ Bm)
    (fm : (languageSortRepresentableObj lang s) ⟶ Dm)
    (gm : Bm ⟶ Dm)
    (hpbm : CategoryTheory.IsPullback pi1m pi2m fm gm)
    (hfm : CategoryTheory.Mono fm) (hpi2m : CategoryTheory.Mono pi2m)
    {Xmodal : Opposite (ConstructorObj lang)}
    (pmodal : Pattern)
    (H : Mettapedia.Logic.PLNWorldModelHyperdoctrine.WMHyperdoctrine SemEState)
    {P Aobj Bobj D : H.Obj}
    (pi1 : P ⟶ Aobj) (pi2 : P ⟶ Bobj) (fcat : Aobj ⟶ D) (gcat : Bobj ⟶ D)
    (hpb : CategoryTheory.IsPullback pi1 pi2 fcat gcat)
    (hmfcat : CategoryTheory.Mono fcat) (hmpi2 : CategoryTheory.Mono pi2)
    (queryOfAtom : String → Pattern → Pattern)
    (φf : OSLFFormula)
    (hφ : StepEvidenceControlledByPolicy policy.semEPolicy φf)
    (Xobj : PLNObj)
    {Xgr : Opposite (Mettapedia.OSLF.Framework.ConstructorCategory.ConstructorObj
      Mettapedia.OSLF.Framework.MeTTaToNTT.mettaFull)}
    (p q : Pattern)
    (hstar : OSLFTheoryStepStar relEnv p q)
    (φcat : H.query Bobj) :
    ((CategoryTheory.Subobject.map pi2m).obj
        ((CategoryTheory.Subobject.pullback pi1m).obj
          (modalSubobjectOfPatternPred lang s seed
            (commDi qComm (PathSemClosedPred lang φpred))
            (languageSortPredNaturality_commDi_pathSemClosed_of_pkg
              lang s seed qComm φpred policy.pathLiftPkg)))
      =
    (CategoryTheory.Subobject.pullback gm).obj
        ((CategoryTheory.Subobject.map fm).obj
          (modalSubobjectOfPatternPred lang s seed
            (commDi qComm (PathSemClosedPred lang φpred))
            (languageSortPredNaturality_commDi_pathSemClosed_of_pkg
              lang s seed qComm φpred policy.pathLiftPkg))))
    ∧
    (langDiamondUsing relEnv lang
      (commDi qComm (PathSemClosedPred lang φpred)) pmodal ↔
      ∃ e : (Mettapedia.OSLF.Framework.ToposReduction.reductionGraphUsing
        (C := ConstructorObj lang) relEnv lang).Edge.obj Xmodal,
        ((Mettapedia.OSLF.Framework.ToposReduction.reductionGraphUsing
          (C := ConstructorObj lang) relEnv lang).source.app Xmodal e).down = pmodal ∧
        ∃ u : Pattern,
          Mettapedia.OSLF.MeTTaIL.Substitution.commSubst u qComm =
            ((Mettapedia.OSLF.Framework.ToposReduction.reductionGraphUsing
              (C := ConstructorObj lang) relEnv lang).target.app Xmodal e).down ∧
          PathSemClosedPred lang φpred u)
    ∧
    EndpointStatement (H := H) pi1 pi2 fcat gcat (semEState relEnv I φf) φcat
    ∧
    WMEvidenceObligation SemEState SemEQuery
      (semEState relEnv I φf) p q := by
  have hModal :
      ((CategoryTheory.Subobject.map pi2m).obj
          ((CategoryTheory.Subobject.pullback pi1m).obj
            (modalSubobjectOfPatternPred lang s seed
              (commDi qComm (PathSemClosedPred lang φpred))
              (languageSortPredNaturality_commDi_pathSemClosed_of_pkg
                lang s seed qComm φpred policy.pathLiftPkg)))
        =
      (CategoryTheory.Subobject.pullback gm).obj
          ((CategoryTheory.Subobject.map fm).obj
            (modalSubobjectOfPatternPred lang s seed
              (commDi qComm (PathSemClosedPred lang φpred))
              (languageSortPredNaturality_commDi_pathSemClosed_of_pkg
                lang s seed qComm φpred policy.pathLiftPkg))))
      ∧
      (langDiamondUsing relEnv lang
        (commDi qComm (PathSemClosedPred lang φpred)) pmodal ↔
        ∃ e : (Mettapedia.OSLF.Framework.ToposReduction.reductionGraphUsing
          (C := ConstructorObj lang) relEnv lang).Edge.obj Xmodal,
          ((Mettapedia.OSLF.Framework.ToposReduction.reductionGraphUsing
            (C := ConstructorObj lang) relEnv lang).source.app Xmodal e).down = pmodal ∧
          ∃ u : Pattern,
            Mettapedia.OSLF.MeTTaIL.Substitution.commSubst u qComm =
              ((Mettapedia.OSLF.Framework.ToposReduction.reductionGraphUsing
                (C := ConstructorObj lang) relEnv lang).target.app Xmodal e).down ∧
            PathSemClosedPred lang φpred u) :=
    modalSubobject_commDi_bc_graph_endpoint_of_policy
      (lang := lang) (s := s) (seed := seed) (q := qComm)
      (φ := φpred) (relEnv := relEnv) (I := I) (policy := policy)
      (pi1 := pi1m) (pi2 := pi2m) (f := fm) (g := gm)
      (hpb := hpbm) (hf := hfm) (hpi2 := hpi2m)
      (X := Xmodal) (p := pmodal)
  rcases semE_fragment_formulaCategoricalEndpoint_stepStar_of_policy
      (H := H)
      (pi1 := pi1) (pi2 := pi2) (fcat := fcat) (gcat := gcat)
      (hpb := hpb) (hmfcat := hmfcat) (hmpi2 := hmpi2)
      (relEnv := relEnv) (queryOfAtom := queryOfAtom)
      (I := I) (policy := policy.semEPolicy) (φ := φf) (hφ := hφ)
      (Xobj := Xobj) (X := Xgr) (p := p) (q := q)
      (hstar := hstar) (φcat := φcat)
    with ⟨hPack, hEv⟩
  exact ⟨hModal.1, hModal.2, (hPack p).2, hEv⟩

/-- Step endpoint specialization of `oslf_ntt_wm_star_sound`. -/
theorem oslf_ntt_wm_step_sound
    (lang : LanguageDef) (s : LangSort lang)
    (seed qComm : Pattern) (φpred : Pattern → Prop)
    (relEnv : RelationEnv)
    (I : EvidenceAtomSem)
    (policy : ModalSubobjectControlledPolicy lang s seed qComm relEnv I)
    {Pm Bm Dm : CategoryTheory.Functor (Opposite (ConstructorObj lang)) (Type _)}
    (pi1m : Pm ⟶ (languageSortRepresentableObj lang s))
    (pi2m : Pm ⟶ Bm)
    (fm : (languageSortRepresentableObj lang s) ⟶ Dm)
    (gm : Bm ⟶ Dm)
    (hpbm : CategoryTheory.IsPullback pi1m pi2m fm gm)
    (hfm : CategoryTheory.Mono fm) (hpi2m : CategoryTheory.Mono pi2m)
    {Xmodal : Opposite (ConstructorObj lang)}
    (pmodal : Pattern)
    (H : Mettapedia.Logic.PLNWorldModelHyperdoctrine.WMHyperdoctrine SemEState)
    {P Aobj Bobj D : H.Obj}
    (pi1 : P ⟶ Aobj) (pi2 : P ⟶ Bobj) (fcat : Aobj ⟶ D) (gcat : Bobj ⟶ D)
    (hpb : CategoryTheory.IsPullback pi1 pi2 fcat gcat)
    (hmfcat : CategoryTheory.Mono fcat) (hmpi2 : CategoryTheory.Mono pi2)
    (queryOfAtom : String → Pattern → Pattern)
    (φf : OSLFFormula)
    (hφ : StepEvidenceControlledByPolicy policy.semEPolicy φf)
    (Xobj : PLNObj)
    {Xgr : Opposite (Mettapedia.OSLF.Framework.ConstructorCategory.ConstructorObj
      Mettapedia.OSLF.Framework.MeTTaToNTT.mettaFull)}
    (p q : Pattern)
    (hstep : OSLFTheoryStep relEnv p q)
    (φcat : H.query Bobj) :
    ((CategoryTheory.Subobject.map pi2m).obj
        ((CategoryTheory.Subobject.pullback pi1m).obj
          (modalSubobjectOfPatternPred lang s seed
            (commDi qComm (PathSemClosedPred lang φpred))
            (languageSortPredNaturality_commDi_pathSemClosed_of_pkg
              lang s seed qComm φpred policy.pathLiftPkg)))
      =
    (CategoryTheory.Subobject.pullback gm).obj
        ((CategoryTheory.Subobject.map fm).obj
          (modalSubobjectOfPatternPred lang s seed
            (commDi qComm (PathSemClosedPred lang φpred))
            (languageSortPredNaturality_commDi_pathSemClosed_of_pkg
              lang s seed qComm φpred policy.pathLiftPkg))))
    ∧
    (langDiamondUsing relEnv lang
      (commDi qComm (PathSemClosedPred lang φpred)) pmodal ↔
      ∃ e : (Mettapedia.OSLF.Framework.ToposReduction.reductionGraphUsing
        (C := ConstructorObj lang) relEnv lang).Edge.obj Xmodal,
        ((Mettapedia.OSLF.Framework.ToposReduction.reductionGraphUsing
          (C := ConstructorObj lang) relEnv lang).source.app Xmodal e).down = pmodal ∧
        ∃ u : Pattern,
          Mettapedia.OSLF.MeTTaIL.Substitution.commSubst u qComm =
            ((Mettapedia.OSLF.Framework.ToposReduction.reductionGraphUsing
              (C := ConstructorObj lang) relEnv lang).target.app Xmodal e).down ∧
          PathSemClosedPred lang φpred u)
    ∧
    EndpointStatement (H := H) pi1 pi2 fcat gcat (semEState relEnv I φf) φcat
    ∧
    WMEvidenceObligation SemEState SemEQuery
      (semEState relEnv I φf) p q := by
  have hstar : OSLFTheoryStepStar relEnv p q := Relation.ReflTransGen.single hstep
  exact oslf_ntt_wm_star_sound
    (lang := lang) (s := s)
    (seed := seed) (qComm := qComm) (φpred := φpred)
    (relEnv := relEnv)
    (I := I)
    (policy := policy)
    (pi1m := pi1m) (pi2m := pi2m) (fm := fm) (gm := gm)
    (hpbm := hpbm) (hfm := hfm) (hpi2m := hpi2m)
    (Xmodal := Xmodal) (pmodal := pmodal)
    (H := H)
    (pi1 := pi1) (pi2 := pi2) (fcat := fcat) (gcat := gcat)
    (hpb := hpb) (hmfcat := hmfcat) (hmpi2 := hmpi2)
    (queryOfAtom := queryOfAtom)
    (φf := φf) (hφ := hφ)
    (Xobj := Xobj) (Xgr := Xgr)
    (p := p) (q := q) (hstar := hstar) (φcat := φcat)

/-- Star endpoint wrapper with policy synthesized from path-order and controlled
step-policy assumptions. -/
theorem oslf_ntt_wm_star_sound_of_pathOrder
    (lang : LanguageDef) (s : LangSort lang)
    (seed qComm : Pattern) (φpred : Pattern → Prop)
    (relEnv : RelationEnv)
    (I : EvidenceAtomSem)
    (hPathOrder :
      ∀ {a b : LangSort lang}
        (g : SortPath lang a b) (h : SortPath lang b s),
          pathSem lang g (pathSem lang h seed) = pathSem lang (g.comp h) seed)
    (hSemEPolicy : ControlledStepPolicy relEnv I)
    {Pm Bm Dm : CategoryTheory.Functor (Opposite (ConstructorObj lang)) (Type _)}
    (pi1m : Pm ⟶ (languageSortRepresentableObj lang s))
    (pi2m : Pm ⟶ Bm)
    (fm : (languageSortRepresentableObj lang s) ⟶ Dm)
    (gm : Bm ⟶ Dm)
    (hpbm : CategoryTheory.IsPullback pi1m pi2m fm gm)
    (hfm : CategoryTheory.Mono fm) (hpi2m : CategoryTheory.Mono pi2m)
    {Xmodal : Opposite (ConstructorObj lang)}
    (pmodal : Pattern)
    (H : Mettapedia.Logic.PLNWorldModelHyperdoctrine.WMHyperdoctrine SemEState)
    {P Aobj Bobj D : H.Obj}
    (pi1 : P ⟶ Aobj) (pi2 : P ⟶ Bobj) (fcat : Aobj ⟶ D) (gcat : Bobj ⟶ D)
    (hpb : CategoryTheory.IsPullback pi1 pi2 fcat gcat)
    (hmfcat : CategoryTheory.Mono fcat) (hmpi2 : CategoryTheory.Mono pi2)
    (queryOfAtom : String → Pattern → Pattern)
    (φf : OSLFFormula)
    (hφ : StepEvidenceControlledByPolicy hSemEPolicy φf)
    (Xobj : PLNObj)
    {Xgr : Opposite (Mettapedia.OSLF.Framework.ConstructorCategory.ConstructorObj
      Mettapedia.OSLF.Framework.MeTTaToNTT.mettaFull)}
    (p q : Pattern)
    (hstar : OSLFTheoryStepStar relEnv p q)
    (φcat : H.query Bobj) :
    ((CategoryTheory.Subobject.map pi2m).obj
        ((CategoryTheory.Subobject.pullback pi1m).obj
          (modalSubobjectOfPatternPred lang s seed
            (commDi qComm (PathSemClosedPred lang φpred))
            (languageSortPredNaturality_commDi_pathSemClosed_of_pkg
              lang s seed qComm φpred
              (commDiPathSemLiftPkg_of_pathSem_comm_subst_and_path_order
                lang s seed qComm hPathOrder))))
      =
    (CategoryTheory.Subobject.pullback gm).obj
        ((CategoryTheory.Subobject.map fm).obj
          (modalSubobjectOfPatternPred lang s seed
            (commDi qComm (PathSemClosedPred lang φpred))
            (languageSortPredNaturality_commDi_pathSemClosed_of_pkg
              lang s seed qComm φpred
              (commDiPathSemLiftPkg_of_pathSem_comm_subst_and_path_order
                lang s seed qComm hPathOrder)))))
    ∧
    (langDiamondUsing relEnv lang
      (commDi qComm (PathSemClosedPred lang φpred)) pmodal ↔
      ∃ e : (Mettapedia.OSLF.Framework.ToposReduction.reductionGraphUsing
        (C := ConstructorObj lang) relEnv lang).Edge.obj Xmodal,
        ((Mettapedia.OSLF.Framework.ToposReduction.reductionGraphUsing
          (C := ConstructorObj lang) relEnv lang).source.app Xmodal e).down = pmodal ∧
        ∃ u : Pattern,
          Mettapedia.OSLF.MeTTaIL.Substitution.commSubst u qComm =
            ((Mettapedia.OSLF.Framework.ToposReduction.reductionGraphUsing
              (C := ConstructorObj lang) relEnv lang).target.app Xmodal e).down ∧
          PathSemClosedPred lang φpred u)
    ∧
    EndpointStatement (H := H) pi1 pi2 fcat gcat (semEState relEnv I φf) φcat
    ∧
    WMEvidenceObligation SemEState SemEQuery
      (semEState relEnv I φf) p q := by
  let policy : ModalSubobjectControlledPolicy lang s seed qComm relEnv I :=
    ModalSubobjectControlledPolicy.of_pathOrder
      lang s seed qComm relEnv I hPathOrder hSemEPolicy
  exact oslf_ntt_wm_star_sound
    (lang := lang) (s := s)
    (seed := seed) (qComm := qComm) (φpred := φpred)
    (relEnv := relEnv)
    (I := I)
    (policy := policy)
    (pi1m := pi1m) (pi2m := pi2m) (fm := fm) (gm := gm)
    (hpbm := hpbm) (hfm := hfm) (hpi2m := hpi2m)
    (Xmodal := Xmodal) (pmodal := pmodal)
    (H := H)
    (pi1 := pi1) (pi2 := pi2) (fcat := fcat) (gcat := gcat)
    (hpb := hpb) (hmfcat := hmfcat) (hmpi2 := hmpi2)
    (queryOfAtom := queryOfAtom)
    (φf := φf) (hφ := by simpa [policy] using hφ)
    (Xobj := Xobj) (Xgr := Xgr)
    (p := p) (q := q) (hstar := hstar) (φcat := φcat)

/-- Step endpoint wrapper with policy synthesized from path-order and controlled
step-policy assumptions. -/
theorem oslf_ntt_wm_step_sound_of_pathOrder
    (lang : LanguageDef) (s : LangSort lang)
    (seed qComm : Pattern) (φpred : Pattern → Prop)
    (relEnv : RelationEnv)
    (I : EvidenceAtomSem)
    (hPathOrder :
      ∀ {a b : LangSort lang}
        (g : SortPath lang a b) (h : SortPath lang b s),
          pathSem lang g (pathSem lang h seed) = pathSem lang (g.comp h) seed)
    (hSemEPolicy : ControlledStepPolicy relEnv I)
    {Pm Bm Dm : CategoryTheory.Functor (Opposite (ConstructorObj lang)) (Type _)}
    (pi1m : Pm ⟶ (languageSortRepresentableObj lang s))
    (pi2m : Pm ⟶ Bm)
    (fm : (languageSortRepresentableObj lang s) ⟶ Dm)
    (gm : Bm ⟶ Dm)
    (hpbm : CategoryTheory.IsPullback pi1m pi2m fm gm)
    (hfm : CategoryTheory.Mono fm) (hpi2m : CategoryTheory.Mono pi2m)
    {Xmodal : Opposite (ConstructorObj lang)}
    (pmodal : Pattern)
    (H : Mettapedia.Logic.PLNWorldModelHyperdoctrine.WMHyperdoctrine SemEState)
    {P Aobj Bobj D : H.Obj}
    (pi1 : P ⟶ Aobj) (pi2 : P ⟶ Bobj) (fcat : Aobj ⟶ D) (gcat : Bobj ⟶ D)
    (hpb : CategoryTheory.IsPullback pi1 pi2 fcat gcat)
    (hmfcat : CategoryTheory.Mono fcat) (hmpi2 : CategoryTheory.Mono pi2)
    (queryOfAtom : String → Pattern → Pattern)
    (φf : OSLFFormula)
    (hφ : StepEvidenceControlledByPolicy hSemEPolicy φf)
    (Xobj : PLNObj)
    {Xgr : Opposite (Mettapedia.OSLF.Framework.ConstructorCategory.ConstructorObj
      Mettapedia.OSLF.Framework.MeTTaToNTT.mettaFull)}
    (p q : Pattern)
    (hstep : OSLFTheoryStep relEnv p q)
    (φcat : H.query Bobj) :
    ((CategoryTheory.Subobject.map pi2m).obj
        ((CategoryTheory.Subobject.pullback pi1m).obj
          (modalSubobjectOfPatternPred lang s seed
            (commDi qComm (PathSemClosedPred lang φpred))
            (languageSortPredNaturality_commDi_pathSemClosed_of_pkg
              lang s seed qComm φpred
              (commDiPathSemLiftPkg_of_pathSem_comm_subst_and_path_order
                lang s seed qComm hPathOrder))))
      =
    (CategoryTheory.Subobject.pullback gm).obj
        ((CategoryTheory.Subobject.map fm).obj
          (modalSubobjectOfPatternPred lang s seed
            (commDi qComm (PathSemClosedPred lang φpred))
            (languageSortPredNaturality_commDi_pathSemClosed_of_pkg
              lang s seed qComm φpred
              (commDiPathSemLiftPkg_of_pathSem_comm_subst_and_path_order
                lang s seed qComm hPathOrder)))))
    ∧
    (langDiamondUsing relEnv lang
      (commDi qComm (PathSemClosedPred lang φpred)) pmodal ↔
      ∃ e : (Mettapedia.OSLF.Framework.ToposReduction.reductionGraphUsing
        (C := ConstructorObj lang) relEnv lang).Edge.obj Xmodal,
        ((Mettapedia.OSLF.Framework.ToposReduction.reductionGraphUsing
          (C := ConstructorObj lang) relEnv lang).source.app Xmodal e).down = pmodal ∧
        ∃ u : Pattern,
          Mettapedia.OSLF.MeTTaIL.Substitution.commSubst u qComm =
            ((Mettapedia.OSLF.Framework.ToposReduction.reductionGraphUsing
              (C := ConstructorObj lang) relEnv lang).target.app Xmodal e).down ∧
          PathSemClosedPred lang φpred u)
    ∧
    EndpointStatement (H := H) pi1 pi2 fcat gcat (semEState relEnv I φf) φcat
    ∧
    WMEvidenceObligation SemEState SemEQuery
      (semEState relEnv I φf) p q := by
  let policy : ModalSubobjectControlledPolicy lang s seed qComm relEnv I :=
    ModalSubobjectControlledPolicy.of_pathOrder
      lang s seed qComm relEnv I hPathOrder hSemEPolicy
  exact oslf_ntt_wm_step_sound
    (lang := lang) (s := s)
    (seed := seed) (qComm := qComm) (φpred := φpred)
    (relEnv := relEnv)
    (I := I)
    (policy := policy)
    (pi1m := pi1m) (pi2m := pi2m) (fm := fm) (gm := gm)
    (hpbm := hpbm) (hfm := hfm) (hpi2m := hpi2m)
    (Xmodal := Xmodal) (pmodal := pmodal)
    (H := H)
    (pi1 := pi1) (pi2 := pi2) (fcat := fcat) (gcat := gcat)
    (hpb := hpb) (hmfcat := hmfcat) (hmpi2 := hmpi2)
    (queryOfAtom := queryOfAtom)
    (φf := φf) (hφ := by simpa [policy] using hφ)
    (Xobj := Xobj) (Xgr := Xgr)
    (p := p) (q := q) (hstep := hstep) (φcat := φcat)

/-- Formula-level star endpoint:
OSLF->NTT formula triangle plus canonical modal-subobject + WM star closure. -/
theorem oslf_formula_ntt_wm_star_sound
    (lang : LanguageDef) (s : LangSort lang)
    (seed qComm : Pattern) (φpred : Pattern → Prop)
    (relEnv : RelationEnv)
    (I : EvidenceAtomSem)
    (policy : ModalSubobjectControlledPolicy lang s seed qComm relEnv I)
    {Pm Bm Dm : CategoryTheory.Functor (Opposite (ConstructorObj lang)) (Type _)}
    (pi1m : Pm ⟶ (languageSortRepresentableObj lang s))
    (pi2m : Pm ⟶ Bm)
    (fm : (languageSortRepresentableObj lang s) ⟶ Dm)
    (gm : Bm ⟶ Dm)
    (hpbm : CategoryTheory.IsPullback pi1m pi2m fm gm)
    (hfm : CategoryTheory.Mono fm) (hpi2m : CategoryTheory.Mono pi2m)
    {Xmodal : Opposite (ConstructorObj lang)}
    (pmodal : Pattern)
    (H : Mettapedia.Logic.PLNWorldModelHyperdoctrine.WMHyperdoctrine SemEState)
    {P Aobj Bobj D : H.Obj}
    (pi1 : P ⟶ Aobj) (pi2 : P ⟶ Bobj) (fcat : Aobj ⟶ D) (gcat : Bobj ⟶ D)
    (hpb : CategoryTheory.IsPullback pi1 pi2 fcat gcat)
    (hmfcat : CategoryTheory.Mono fcat) (hmpi2 : CategoryTheory.Mono pi2)
    (queryOfAtom : String → Pattern → Pattern)
    (φf : OSLFFormula)
    (hφ : StepEvidenceControlledByPolicy policy.semEPolicy φf)
    (Xobj : PLNObj)
    {Xgr : Opposite (Mettapedia.OSLF.Framework.ConstructorCategory.ConstructorObj
      Mettapedia.OSLF.Framework.MeTTaToNTT.mettaFull)}
    (p q : Pattern)
    (hstar : OSLFTheoryStepStar relEnv p q)
    (φcat : H.query Bobj) :
    Mettapedia.OSLF.Framework.OSLFNTTWMBridge.FormulaGraphEndpoint
      (State := SemEState)
      (relEnv := relEnv)
      (W := semEState relEnv I φf)
      (queryOfAtom := queryOfAtom)
      (φf := φf) (Xobj := Xobj) (X := Xgr) (p := p)
    ∧
    (((CategoryTheory.Subobject.map pi2m).obj
        ((CategoryTheory.Subobject.pullback pi1m).obj
          (modalSubobjectOfPatternPred lang s seed
            (commDi qComm (PathSemClosedPred lang φpred))
            (languageSortPredNaturality_commDi_pathSemClosed_of_pkg
              lang s seed qComm φpred policy.pathLiftPkg)))
      =
    (CategoryTheory.Subobject.pullback gm).obj
        ((CategoryTheory.Subobject.map fm).obj
          (modalSubobjectOfPatternPred lang s seed
            (commDi qComm (PathSemClosedPred lang φpred))
            (languageSortPredNaturality_commDi_pathSemClosed_of_pkg
              lang s seed qComm φpred policy.pathLiftPkg))))
    ∧
    (langDiamondUsing relEnv lang
      (commDi qComm (PathSemClosedPred lang φpred)) pmodal ↔
      ∃ e : (Mettapedia.OSLF.Framework.ToposReduction.reductionGraphUsing
        (C := ConstructorObj lang) relEnv lang).Edge.obj Xmodal,
        ((Mettapedia.OSLF.Framework.ToposReduction.reductionGraphUsing
          (C := ConstructorObj lang) relEnv lang).source.app Xmodal e).down = pmodal ∧
        ∃ u : Pattern,
          Mettapedia.OSLF.MeTTaIL.Substitution.commSubst u qComm =
            ((Mettapedia.OSLF.Framework.ToposReduction.reductionGraphUsing
              (C := ConstructorObj lang) relEnv lang).target.app Xmodal e).down ∧
          PathSemClosedPred lang φpred u)
    ∧
    EndpointStatement (H := H) pi1 pi2 fcat gcat (semEState relEnv I φf) φcat
    ∧
    WMEvidenceObligation SemEState SemEQuery
      (semEState relEnv I φf) p q) := by
  have hFormula :
      Mettapedia.OSLF.Framework.OSLFNTTWMBridge.FormulaGraphEndpoint
        (State := SemEState)
        (relEnv := relEnv)
        (W := semEState relEnv I φf)
        (queryOfAtom := queryOfAtom)
        (φf := φf) (Xobj := Xobj) (X := Xgr) (p := p) :=
    Mettapedia.OSLF.Framework.OSLFNTTWMBridge.oslf_formula_ntt_graph_triangle
      (State := SemEState)
      (relEnv := relEnv)
      (W := semEState relEnv I φf)
      (queryOfAtom := queryOfAtom)
      (φf := φf) (Xobj := Xobj) (X := Xgr) (p := p)
  have hCore :=
    oslf_ntt_wm_star_sound
      (lang := lang) (s := s)
      (seed := seed) (qComm := qComm) (φpred := φpred)
      (relEnv := relEnv)
      (I := I)
      (policy := policy)
      (pi1m := pi1m) (pi2m := pi2m) (fm := fm) (gm := gm)
      (hpbm := hpbm) (hfm := hfm) (hpi2m := hpi2m)
      (Xmodal := Xmodal) (pmodal := pmodal)
      (H := H)
      (pi1 := pi1) (pi2 := pi2) (fcat := fcat) (gcat := gcat)
      (hpb := hpb) (hmfcat := hmfcat) (hmpi2 := hmpi2)
      (queryOfAtom := queryOfAtom)
      (φf := φf) (hφ := hφ)
      (Xobj := Xobj) (Xgr := Xgr)
      (p := p) (q := q) (hstar := hstar) (φcat := φcat)
  exact ⟨hFormula, hCore⟩

/-- Formula-level step endpoint:
OSLF->NTT formula triangle plus canonical modal-subobject + WM step closure. -/
theorem oslf_formula_ntt_wm_step_sound
    (lang : LanguageDef) (s : LangSort lang)
    (seed qComm : Pattern) (φpred : Pattern → Prop)
    (relEnv : RelationEnv)
    (I : EvidenceAtomSem)
    (policy : ModalSubobjectControlledPolicy lang s seed qComm relEnv I)
    {Pm Bm Dm : CategoryTheory.Functor (Opposite (ConstructorObj lang)) (Type _)}
    (pi1m : Pm ⟶ (languageSortRepresentableObj lang s))
    (pi2m : Pm ⟶ Bm)
    (fm : (languageSortRepresentableObj lang s) ⟶ Dm)
    (gm : Bm ⟶ Dm)
    (hpbm : CategoryTheory.IsPullback pi1m pi2m fm gm)
    (hfm : CategoryTheory.Mono fm) (hpi2m : CategoryTheory.Mono pi2m)
    {Xmodal : Opposite (ConstructorObj lang)}
    (pmodal : Pattern)
    (H : Mettapedia.Logic.PLNWorldModelHyperdoctrine.WMHyperdoctrine SemEState)
    {P Aobj Bobj D : H.Obj}
    (pi1 : P ⟶ Aobj) (pi2 : P ⟶ Bobj) (fcat : Aobj ⟶ D) (gcat : Bobj ⟶ D)
    (hpb : CategoryTheory.IsPullback pi1 pi2 fcat gcat)
    (hmfcat : CategoryTheory.Mono fcat) (hmpi2 : CategoryTheory.Mono pi2)
    (queryOfAtom : String → Pattern → Pattern)
    (φf : OSLFFormula)
    (hφ : StepEvidenceControlledByPolicy policy.semEPolicy φf)
    (Xobj : PLNObj)
    {Xgr : Opposite (Mettapedia.OSLF.Framework.ConstructorCategory.ConstructorObj
      Mettapedia.OSLF.Framework.MeTTaToNTT.mettaFull)}
    (p q : Pattern)
    (hstep : OSLFTheoryStep relEnv p q)
    (φcat : H.query Bobj) :
    Mettapedia.OSLF.Framework.OSLFNTTWMBridge.FormulaGraphEndpoint
      (State := SemEState)
      (relEnv := relEnv)
      (W := semEState relEnv I φf)
      (queryOfAtom := queryOfAtom)
      (φf := φf) (Xobj := Xobj) (X := Xgr) (p := p)
    ∧
    (((CategoryTheory.Subobject.map pi2m).obj
        ((CategoryTheory.Subobject.pullback pi1m).obj
          (modalSubobjectOfPatternPred lang s seed
            (commDi qComm (PathSemClosedPred lang φpred))
            (languageSortPredNaturality_commDi_pathSemClosed_of_pkg
              lang s seed qComm φpred policy.pathLiftPkg)))
      =
    (CategoryTheory.Subobject.pullback gm).obj
        ((CategoryTheory.Subobject.map fm).obj
          (modalSubobjectOfPatternPred lang s seed
            (commDi qComm (PathSemClosedPred lang φpred))
            (languageSortPredNaturality_commDi_pathSemClosed_of_pkg
              lang s seed qComm φpred policy.pathLiftPkg))))
    ∧
    (langDiamondUsing relEnv lang
      (commDi qComm (PathSemClosedPred lang φpred)) pmodal ↔
      ∃ e : (Mettapedia.OSLF.Framework.ToposReduction.reductionGraphUsing
        (C := ConstructorObj lang) relEnv lang).Edge.obj Xmodal,
        ((Mettapedia.OSLF.Framework.ToposReduction.reductionGraphUsing
          (C := ConstructorObj lang) relEnv lang).source.app Xmodal e).down = pmodal ∧
        ∃ u : Pattern,
          Mettapedia.OSLF.MeTTaIL.Substitution.commSubst u qComm =
            ((Mettapedia.OSLF.Framework.ToposReduction.reductionGraphUsing
              (C := ConstructorObj lang) relEnv lang).target.app Xmodal e).down ∧
          PathSemClosedPred lang φpred u)
    ∧
    EndpointStatement (H := H) pi1 pi2 fcat gcat (semEState relEnv I φf) φcat
    ∧
    WMEvidenceObligation SemEState SemEQuery
      (semEState relEnv I φf) p q) := by
  have hFormula :
      Mettapedia.OSLF.Framework.OSLFNTTWMBridge.FormulaGraphEndpoint
        (State := SemEState)
        (relEnv := relEnv)
        (W := semEState relEnv I φf)
        (queryOfAtom := queryOfAtom)
        (φf := φf) (Xobj := Xobj) (X := Xgr) (p := p) :=
    Mettapedia.OSLF.Framework.OSLFNTTWMBridge.oslf_formula_ntt_graph_triangle
      (State := SemEState)
      (relEnv := relEnv)
      (W := semEState relEnv I φf)
      (queryOfAtom := queryOfAtom)
      (φf := φf) (Xobj := Xobj) (X := Xgr) (p := p)
  have hCore :=
    oslf_ntt_wm_step_sound
      (lang := lang) (s := s)
      (seed := seed) (qComm := qComm) (φpred := φpred)
      (relEnv := relEnv)
      (I := I)
      (policy := policy)
      (pi1m := pi1m) (pi2m := pi2m) (fm := fm) (gm := gm)
      (hpbm := hpbm) (hfm := hfm) (hpi2m := hpi2m)
      (Xmodal := Xmodal) (pmodal := pmodal)
      (H := H)
      (pi1 := pi1) (pi2 := pi2) (fcat := fcat) (gcat := gcat)
      (hpb := hpb) (hmfcat := hmfcat) (hmpi2 := hmpi2)
      (queryOfAtom := queryOfAtom)
      (φf := φf) (hφ := hφ)
      (Xobj := Xobj) (Xgr := Xgr)
      (p := p) (q := q) (hstep := hstep) (φcat := φcat)
  exact ⟨hFormula, hCore⟩

/-- Formula-level star endpoint wrapper with policy synthesized from path-order
and controlled-step-policy assumptions. -/
theorem oslf_formula_ntt_wm_star_sound_of_pathOrder
    (lang : LanguageDef) (s : LangSort lang)
    (seed qComm : Pattern) (φpred : Pattern → Prop)
    (relEnv : RelationEnv)
    (I : EvidenceAtomSem)
    (hPathOrder :
      ∀ {a b : LangSort lang}
        (g : SortPath lang a b) (h : SortPath lang b s),
          pathSem lang g (pathSem lang h seed) = pathSem lang (g.comp h) seed)
    (hSemEPolicy : ControlledStepPolicy relEnv I)
    {Pm Bm Dm : CategoryTheory.Functor (Opposite (ConstructorObj lang)) (Type _)}
    (pi1m : Pm ⟶ (languageSortRepresentableObj lang s))
    (pi2m : Pm ⟶ Bm)
    (fm : (languageSortRepresentableObj lang s) ⟶ Dm)
    (gm : Bm ⟶ Dm)
    (hpbm : CategoryTheory.IsPullback pi1m pi2m fm gm)
    (hfm : CategoryTheory.Mono fm) (hpi2m : CategoryTheory.Mono pi2m)
    {Xmodal : Opposite (ConstructorObj lang)}
    (pmodal : Pattern)
    (H : Mettapedia.Logic.PLNWorldModelHyperdoctrine.WMHyperdoctrine SemEState)
    {P Aobj Bobj D : H.Obj}
    (pi1 : P ⟶ Aobj) (pi2 : P ⟶ Bobj) (fcat : Aobj ⟶ D) (gcat : Bobj ⟶ D)
    (hpb : CategoryTheory.IsPullback pi1 pi2 fcat gcat)
    (hmfcat : CategoryTheory.Mono fcat) (hmpi2 : CategoryTheory.Mono pi2)
    (queryOfAtom : String → Pattern → Pattern)
    (φf : OSLFFormula)
    (hφ : StepEvidenceControlledByPolicy hSemEPolicy φf)
    (Xobj : PLNObj)
    {Xgr : Opposite (Mettapedia.OSLF.Framework.ConstructorCategory.ConstructorObj
      Mettapedia.OSLF.Framework.MeTTaToNTT.mettaFull)}
    (p q : Pattern)
    (hstar : OSLFTheoryStepStar relEnv p q)
    (φcat : H.query Bobj) :
    Mettapedia.OSLF.Framework.OSLFNTTWMBridge.FormulaGraphEndpoint
      (State := SemEState)
      (relEnv := relEnv)
      (W := semEState relEnv I φf)
      (queryOfAtom := queryOfAtom)
      (φf := φf) (Xobj := Xobj) (X := Xgr) (p := p)
    ∧
    (((CategoryTheory.Subobject.map pi2m).obj
        ((CategoryTheory.Subobject.pullback pi1m).obj
          (modalSubobjectOfPatternPred lang s seed
            (commDi qComm (PathSemClosedPred lang φpred))
            (languageSortPredNaturality_commDi_pathSemClosed_of_pkg
              lang s seed qComm φpred
              (commDiPathSemLiftPkg_of_pathSem_comm_subst_and_path_order
                lang s seed qComm hPathOrder))))
      =
    (CategoryTheory.Subobject.pullback gm).obj
        ((CategoryTheory.Subobject.map fm).obj
          (modalSubobjectOfPatternPred lang s seed
            (commDi qComm (PathSemClosedPred lang φpred))
            (languageSortPredNaturality_commDi_pathSemClosed_of_pkg
              lang s seed qComm φpred
              (commDiPathSemLiftPkg_of_pathSem_comm_subst_and_path_order
                lang s seed qComm hPathOrder)))))
    ∧
    (langDiamondUsing relEnv lang
      (commDi qComm (PathSemClosedPred lang φpred)) pmodal ↔
      ∃ e : (Mettapedia.OSLF.Framework.ToposReduction.reductionGraphUsing
        (C := ConstructorObj lang) relEnv lang).Edge.obj Xmodal,
        ((Mettapedia.OSLF.Framework.ToposReduction.reductionGraphUsing
          (C := ConstructorObj lang) relEnv lang).source.app Xmodal e).down = pmodal ∧
        ∃ u : Pattern,
          Mettapedia.OSLF.MeTTaIL.Substitution.commSubst u qComm =
            ((Mettapedia.OSLF.Framework.ToposReduction.reductionGraphUsing
              (C := ConstructorObj lang) relEnv lang).target.app Xmodal e).down ∧
          PathSemClosedPred lang φpred u)
    ∧
    EndpointStatement (H := H) pi1 pi2 fcat gcat (semEState relEnv I φf) φcat
    ∧
    WMEvidenceObligation SemEState SemEQuery
      (semEState relEnv I φf) p q) := by
  let policy : ModalSubobjectControlledPolicy lang s seed qComm relEnv I :=
    ModalSubobjectControlledPolicy.of_pathOrder
      lang s seed qComm relEnv I hPathOrder hSemEPolicy
  exact oslf_formula_ntt_wm_star_sound
    (lang := lang) (s := s)
    (seed := seed) (qComm := qComm) (φpred := φpred)
    (relEnv := relEnv)
    (I := I)
    (policy := policy)
    (pi1m := pi1m) (pi2m := pi2m) (fm := fm) (gm := gm)
    (hpbm := hpbm) (hfm := hfm) (hpi2m := hpi2m)
    (Xmodal := Xmodal) (pmodal := pmodal)
    (H := H)
    (pi1 := pi1) (pi2 := pi2) (fcat := fcat) (gcat := gcat)
    (hpb := hpb) (hmfcat := hmfcat) (hmpi2 := hmpi2)
    (queryOfAtom := queryOfAtom)
    (φf := φf) (hφ := by simpa [policy] using hφ)
    (Xobj := Xobj) (Xgr := Xgr)
    (p := p) (q := q) (hstar := hstar) (φcat := φcat)

/-- Formula-level star endpoint with a reusable canonical-closure context. -/
theorem oslf_formula_ntt_wm_star_sound_ctx
    (ctx : CanonicalClosureContext)
    {Pm Bm Dm : CategoryTheory.Functor (Opposite (ConstructorObj ctx.lang)) (Type _)}
    (pi1m : Pm ⟶ (languageSortRepresentableObj ctx.lang ctx.s))
    (pi2m : Pm ⟶ Bm)
    (fm : (languageSortRepresentableObj ctx.lang ctx.s) ⟶ Dm)
    (gm : Bm ⟶ Dm)
    (hpbm : CategoryTheory.IsPullback pi1m pi2m fm gm)
    (hfm : CategoryTheory.Mono fm) (hpi2m : CategoryTheory.Mono pi2m)
    {Xmodal : Opposite (ConstructorObj ctx.lang)}
    (pmodal : Pattern)
    (H : Mettapedia.Logic.PLNWorldModelHyperdoctrine.WMHyperdoctrine SemEState)
    {P Aobj Bobj D : H.Obj}
    (pi1 : P ⟶ Aobj) (pi2 : P ⟶ Bobj) (fcat : Aobj ⟶ D) (gcat : Bobj ⟶ D)
    (hpb : CategoryTheory.IsPullback pi1 pi2 fcat gcat)
    (hmfcat : CategoryTheory.Mono fcat) (hmpi2 : CategoryTheory.Mono pi2)
    (queryOfAtom : String → Pattern → Pattern)
    (φf : OSLFFormula)
    (hφ : StepEvidenceControlledByPolicy ctx.hSemEPolicy φf)
    (Xobj : PLNObj)
    {Xgr : Opposite (Mettapedia.OSLF.Framework.ConstructorCategory.ConstructorObj
      Mettapedia.OSLF.Framework.MeTTaToNTT.mettaFull)}
    (p q : Pattern)
    (hstar : OSLFTheoryStepStar ctx.relEnv p q)
    (φcat : H.query Bobj) :
    Mettapedia.OSLF.Framework.OSLFNTTWMBridge.FormulaGraphEndpoint
      (State := SemEState)
      (relEnv := ctx.relEnv)
      (W := semEState ctx.relEnv ctx.I φf)
      (queryOfAtom := queryOfAtom)
      (φf := φf) (Xobj := Xobj) (X := Xgr) (p := p)
    ∧
    (((CategoryTheory.Subobject.map pi2m).obj
        ((CategoryTheory.Subobject.pullback pi1m).obj
          (modalSubobjectOfPatternPred ctx.lang ctx.s ctx.seed
            (commDi ctx.qComm (PathSemClosedPred ctx.lang ctx.φpred))
            (languageSortPredNaturality_commDi_pathSemClosed_of_pkg
              ctx.lang ctx.s ctx.seed ctx.qComm ctx.φpred
              ctx.policy.pathLiftPkg)))
      =
    (CategoryTheory.Subobject.pullback gm).obj
        ((CategoryTheory.Subobject.map fm).obj
          (modalSubobjectOfPatternPred ctx.lang ctx.s ctx.seed
            (commDi ctx.qComm (PathSemClosedPred ctx.lang ctx.φpred))
            (languageSortPredNaturality_commDi_pathSemClosed_of_pkg
              ctx.lang ctx.s ctx.seed ctx.qComm ctx.φpred
              ctx.policy.pathLiftPkg))))
    ∧
    (langDiamondUsing ctx.relEnv ctx.lang
      (commDi ctx.qComm (PathSemClosedPred ctx.lang ctx.φpred)) pmodal ↔
      ∃ e : (Mettapedia.OSLF.Framework.ToposReduction.reductionGraphUsing
        (C := ConstructorObj ctx.lang) ctx.relEnv ctx.lang).Edge.obj Xmodal,
        ((Mettapedia.OSLF.Framework.ToposReduction.reductionGraphUsing
          (C := ConstructorObj ctx.lang) ctx.relEnv ctx.lang).source.app Xmodal e).down = pmodal ∧
        ∃ u : Pattern,
          Mettapedia.OSLF.MeTTaIL.Substitution.commSubst u ctx.qComm =
            ((Mettapedia.OSLF.Framework.ToposReduction.reductionGraphUsing
              (C := ConstructorObj ctx.lang) ctx.relEnv ctx.lang).target.app Xmodal e).down ∧
          PathSemClosedPred ctx.lang ctx.φpred u)
    ∧
    EndpointStatement (H := H) pi1 pi2 fcat gcat (semEState ctx.relEnv ctx.I φf) φcat
    ∧
    WMEvidenceObligation SemEState SemEQuery
      (semEState ctx.relEnv ctx.I φf) p q) := by
  exact oslf_formula_ntt_wm_star_sound
    (lang := ctx.lang) (s := ctx.s)
    (seed := ctx.seed) (qComm := ctx.qComm) (φpred := ctx.φpred)
    (relEnv := ctx.relEnv)
    (I := ctx.I)
    (policy := ctx.policy)
    (pi1m := pi1m) (pi2m := pi2m) (fm := fm) (gm := gm)
    (hpbm := hpbm) (hfm := hfm) (hpi2m := hpi2m)
    (Xmodal := Xmodal) (pmodal := pmodal)
    (H := H)
    (pi1 := pi1) (pi2 := pi2) (fcat := fcat) (gcat := gcat)
    (hpb := hpb) (hmfcat := hmfcat) (hmpi2 := hmpi2)
    (queryOfAtom := queryOfAtom)
    (φf := φf) (hφ := by simpa [CanonicalClosureContext.policy] using hφ)
    (Xobj := Xobj) (Xgr := Xgr)
    (p := p) (q := q) (hstar := hstar) (φcat := φcat)

/-- Compact-form projection: derive the canonical WM evidence obligation directly
from reusable modal/categorical/formula bundles. -/
theorem canonicalEvidenceObligation_compact
    (ctx : CanonicalClosureContext)
    (modal : CanonicalModalSquare ctx)
    (cat : CanonicalHyperSquare ctx)
    (fa : CanonicalFormulaArgs ctx)
    (p q : Pattern)
    (hstar : OSLFTheoryStepStar ctx.relEnv p q)
    (φcat : cat.H.query cat.Bobj) :
    WMEvidenceObligation SemEState SemEQuery
      (semEState ctx.relEnv ctx.I fa.φf) p q := by
  letI : CategoryTheory.Mono modal.fm := modal.hfm
  letI : CategoryTheory.Mono modal.pi2m := modal.hpi2m
  have hCore :=
    oslf_formula_ntt_wm_star_sound_ctx
      (ctx := ctx)
      (pi1m := modal.pi1m) (pi2m := modal.pi2m) (fm := modal.fm) (gm := modal.gm)
      (hpbm := modal.hpbm) (hfm := modal.hfm) (hpi2m := modal.hpi2m)
      (Xmodal := modal.Xmodal) (pmodal := modal.pmodal)
      (H := cat.H)
      (pi1 := cat.pi1) (pi2 := cat.pi2) (fcat := cat.fcat) (gcat := cat.gcat)
      (hpb := cat.hpb) (hmfcat := cat.hmfcat) (hmpi2 := cat.hmpi2)
      (queryOfAtom := fa.queryOfAtom)
      (φf := fa.φf) (hφ := fa.hφ)
      (Xobj := fa.Xobj) (Xgr := fa.Xgr)
      (p := p) (q := q) (hstar := hstar) (φcat := φcat)
  exact hCore.2.2.2.2

/-- Compact-form canonical WM evidence-rule constructor from the bundled
formula-level star endpoint. -/
def canonicalEvidenceConsequenceRuleOn_compact
    (ctx : CanonicalClosureContext)
    (modal : CanonicalModalSquare ctx)
    (cat : CanonicalHyperSquare ctx)
    (fa : CanonicalFormulaArgs ctx)
    (p q : Pattern)
    (hstar : OSLFTheoryStepStar ctx.relEnv p q)
    (φcat : cat.H.query cat.Bobj) :
    WMEvidenceConsequenceRuleOn SemEState SemEQuery where
  side := fun W => W = semEState ctx.relEnv ctx.I fa.φf
  premise := p
  conclusion := q
  sound := by
    intro W hW
    subst hW
    exact canonicalEvidenceObligation_compact
      (ctx := ctx) (modal := modal) (cat := cat) (fa := fa)
      (p := p) (q := q) (hstar := hstar) (φcat := φcat)

/-- Goal-bundled wrapper around `canonicalEvidenceConsequenceRuleOn_compact` so
evidence-rule consumers can pass one reusable endpoint-goal object. -/
def canonicalEvidenceConsequenceRuleOn_compact_of_goal
    (ctx : CanonicalClosureContext)
    (modal : CanonicalModalSquare ctx)
    (cat : CanonicalHyperSquare ctx)
    (fa : CanonicalFormulaArgs ctx)
    (goal : CanonicalGoalArgs ctx cat fa) :
    WMEvidenceConsequenceRuleOn SemEState SemEQuery :=
  canonicalEvidenceConsequenceRuleOn_compact
    (ctx := ctx) (modal := modal) (cat := cat) (fa := fa)
    (p := goal.p) (q := goal.q) (hstar := goal.hstar) (φcat := goal.φcat)

/-- Goal-bundled evidence-rule canary:
the bundled canonical evidence consequence rule discharges the expected WM
evidence obligation at its side condition. -/
theorem canonicalEvidenceConsequenceRuleOn_compact_of_goal_canary
    (ctx : CanonicalClosureContext)
    (modal : CanonicalModalSquare ctx)
    (cat : CanonicalHyperSquare ctx)
    (fa : CanonicalFormulaArgs ctx)
    (goal : CanonicalGoalArgs ctx cat fa) :
    let r : WMEvidenceConsequenceRuleOn SemEState SemEQuery :=
      canonicalEvidenceConsequenceRuleOn_compact_of_goal
        (ctx := ctx) (modal := modal) (cat := cat) (fa := fa) (goal := goal)
    WMEvidenceObligation SemEState SemEQuery
      (semEState ctx.relEnv ctx.I fa.φf) r.premise r.conclusion := by
  intro r
  have hSide : r.side (semEState ctx.relEnv ctx.I fa.φf) := rfl
  exact r.sound hSide

/-- Compact-form canonical WM strength-rule constructor from the bundled
formula-level star endpoint, using an explicit evidence->strength bridge for the
target state/pair. -/
def canonicalConsequenceRuleOn_compact
    (ctx : CanonicalClosureContext)
    (modal : CanonicalModalSquare ctx)
    (cat : CanonicalHyperSquare ctx)
    (fa : CanonicalFormulaArgs ctx)
    (p q : Pattern)
    (hstar : OSLFTheoryStepStar ctx.relEnv p q)
    (φcat : cat.H.query cat.Bobj)
    (hStrengthFromEvidence :
      WMEvidenceObligation SemEState SemEQuery
        (semEState ctx.relEnv ctx.I fa.φf) p q →
      WMStrengthObligation SemEState SemEQuery
        (semEState ctx.relEnv ctx.I fa.φf) p q) :
    WMConsequenceRuleOn SemEState SemEQuery where
  side := fun W => W = semEState ctx.relEnv ctx.I fa.φf
  premise := p
  conclusion := q
  sound := by
    intro W hW
    subst hW
    exact hStrengthFromEvidence <|
      canonicalEvidenceObligation_compact
        (ctx := ctx) (modal := modal) (cat := cat) (fa := fa)
        (p := p) (q := q) (hstar := hstar) (φcat := φcat)

/-- Goal-bundled wrapper around `canonicalConsequenceRuleOn_compact` so callers
can pass a single reusable endpoint-goal object. -/
def canonicalConsequenceRuleOn_compact_of_goal
    (ctx : CanonicalClosureContext)
    (modal : CanonicalModalSquare ctx)
    (cat : CanonicalHyperSquare ctx)
    (fa : CanonicalFormulaArgs ctx)
    (goal : CanonicalGoalArgs ctx cat fa) :
    WMConsequenceRuleOn SemEState SemEQuery :=
  canonicalConsequenceRuleOn_compact
    (ctx := ctx) (modal := modal) (cat := cat) (fa := fa)
    (p := goal.p) (q := goal.q) (hstar := goal.hstar) (φcat := goal.φcat)
    (hStrengthFromEvidence := goal.hStrengthFromEvidence)

/-- Compact-form canonical fixpoint canary:
the bundled canonical consequence rule is consumable directly by
`immediateIter/leastRuleClosure` without manual endpoint unpacking. -/
theorem canonicalConsequenceRuleOn_compact_fixpoint
    (ctx : CanonicalClosureContext)
    (modal : CanonicalModalSquare ctx)
    (cat : CanonicalHyperSquare ctx)
    (fa : CanonicalFormulaArgs ctx)
    (p q : Pattern)
    (hstar : OSLFTheoryStepStar ctx.relEnv p q)
    (φcat : cat.H.query cat.Bobj)
    (hStrengthFromEvidence :
      WMEvidenceObligation SemEState SemEQuery
        (semEState ctx.relEnv ctx.I fa.φf) p q →
      WMStrengthObligation SemEState SemEQuery
        (semEState ctx.relEnv ctx.I fa.φf) p q) :
    let W0 : SemEState := semEState ctx.relEnv ctx.I fa.φf
    let r : WMConsequenceRuleOn SemEState SemEQuery :=
      canonicalConsequenceRuleOn_compact
        (ctx := ctx) (modal := modal) (cat := cat) (fa := fa)
        (p := p) (q := q) (hstar := hstar) (φcat := φcat)
        (hStrengthFromEvidence := hStrengthFromEvidence)
    let R : Mettapedia.Logic.PLNWorldModelFixpointClosure.RuleSet SemEState SemEQuery := ({r} : Set _)
    p ∈ Mettapedia.Logic.PLNWorldModelFixpointClosure.immediateIter R W0 ({p} : Set SemEQuery) 0
      ∧ q ∈ Mettapedia.Logic.PLNWorldModelFixpointClosure.immediateIter R W0 ({p} : Set SemEQuery) 1
      ∧ q ∈ Mettapedia.Logic.PLNWorldModelFixpointClosure.leastRuleClosure R W0 ({p} : Set SemEQuery) := by
  classical
  dsimp
  let W0 : SemEState := semEState ctx.relEnv ctx.I fa.φf
  let r : WMConsequenceRuleOn SemEState SemEQuery :=
    canonicalConsequenceRuleOn_compact
      (ctx := ctx) (modal := modal) (cat := cat) (fa := fa)
      (p := p) (q := q) (hstar := hstar) (φcat := φcat)
      (hStrengthFromEvidence := hStrengthFromEvidence)
  let R : Mettapedia.Logic.PLNWorldModelFixpointClosure.RuleSet SemEState SemEQuery := ({r} : Set _)
  have hp0 :
      p ∈ Mettapedia.Logic.PLNWorldModelFixpointClosure.immediateIter R W0 ({p} : Set SemEQuery) 0 := by
    simp [Mettapedia.Logic.PLNWorldModelFixpointClosure.immediateIter]
  have hq1 :
      q ∈ Mettapedia.Logic.PLNWorldModelFixpointClosure.immediateIter R W0 ({p} : Set SemEQuery) 1 := by
    change q ∈ Mettapedia.Logic.PLNWorldModelFixpointClosure.immediateStep R W0
      ({p} : Set SemEQuery) ({p} : Set SemEQuery)
    refine Or.inr ?_
    refine ⟨r, by simp [R], by simp [r, W0, canonicalConsequenceRuleOn_compact], ?_, by
      simp [r, canonicalConsequenceRuleOn_compact]⟩
    show p ∈ ({p} : Set SemEQuery)
    simp
  have hqLfp :
      q ∈ Mettapedia.Logic.PLNWorldModelFixpointClosure.leastRuleClosure R W0 ({p} : Set SemEQuery) :=
    Mettapedia.Logic.PLNWorldModelFixpointClosure.immediateIter_subset_leastRuleClosure
      (State := SemEState) (Query := SemEQuery) R W0 ({p} : Set SemEQuery) 1 hq1
  exact ⟨hp0, hq1, hqLfp⟩

/-- Goal-bundled compact fixpoint canary: same closure result as
`canonicalConsequenceRuleOn_compact_fixpoint`, but consuming a single reusable
`CanonicalGoalArgs` object. -/
theorem canonicalConsequenceRuleOn_compact_fixpoint_of_goal
    (ctx : CanonicalClosureContext)
    (modal : CanonicalModalSquare ctx)
    (cat : CanonicalHyperSquare ctx)
    (fa : CanonicalFormulaArgs ctx)
    (goal : CanonicalGoalArgs ctx cat fa) :
    let W0 : SemEState := semEState ctx.relEnv ctx.I fa.φf
    let r : WMConsequenceRuleOn SemEState SemEQuery :=
      canonicalConsequenceRuleOn_compact_of_goal
        (ctx := ctx) (modal := modal) (cat := cat) (fa := fa) (goal := goal)
    let R : Mettapedia.Logic.PLNWorldModelFixpointClosure.RuleSet SemEState SemEQuery := ({r} : Set _)
    goal.p ∈ Mettapedia.Logic.PLNWorldModelFixpointClosure.immediateIter R W0 ({goal.p} : Set SemEQuery) 0
      ∧ goal.q ∈ Mettapedia.Logic.PLNWorldModelFixpointClosure.immediateIter R W0 ({goal.p} : Set SemEQuery) 1
      ∧ goal.q ∈ Mettapedia.Logic.PLNWorldModelFixpointClosure.leastRuleClosure R W0 ({goal.p} : Set SemEQuery) := by
  simpa [canonicalConsequenceRuleOn_compact_of_goal] using
    (canonicalConsequenceRuleOn_compact_fixpoint
      (ctx := ctx) (modal := modal) (cat := cat) (fa := fa)
      (p := goal.p) (q := goal.q) (hstar := goal.hstar) (φcat := goal.φcat)
      (hStrengthFromEvidence := goal.hStrengthFromEvidence))

/-- Compact combined endpoint:
explicit ΠΣ rule-pack transport package together with canonical WM
star-to-fixpoint closure under bundled modal/categorical/formula arguments. -/
theorem canonical_rulePack_transport_pack_and_fixpoint_endpoint_compact
    (ctx : CanonicalClosureContext)
    (modal : CanonicalModalSquare ctx)
    (cat : CanonicalHyperSquare ctx)
    (fa : CanonicalFormulaArgs ctx)
    (hφTop :
      languageSortPredNaturality ctx.lang ctx.s ctx.seed ctx.φpred)
    (hPiSigmaPack :
      Mettapedia.OSLF.NativeType.PiSigmaPredicateRulePack
        (C := ConstructorObj ctx.lang))
    (p q : Pattern)
    (hstar : OSLFTheoryStepStar ctx.relEnv p q)
    (φcat : cat.H.query cat.Bobj)
    (hStrengthFromEvidence :
      WMEvidenceObligation SemEState SemEQuery
        (semEState ctx.relEnv ctx.I fa.φf) p q →
      WMStrengthObligation SemEState SemEQuery
        (semEState ctx.relEnv ctx.I fa.φf) p q) :
    Mettapedia.OSLF.Framework.BeckChevalleyOSLF.RepresentablePiSigmaTransportPack
      (lang := ctx.lang) (s := ctx.s) (seed := ctx.seed) (φ := ctx.φpred)
      (hNat := hφTop) (f := modal.fm)
    ∧
    (let W0 : SemEState := semEState ctx.relEnv ctx.I fa.φf
      let r : WMConsequenceRuleOn SemEState SemEQuery :=
        canonicalConsequenceRuleOn_compact
          (ctx := ctx) (modal := modal) (cat := cat) (fa := fa)
          (p := p) (q := q) (hstar := hstar) (φcat := φcat)
          (hStrengthFromEvidence := hStrengthFromEvidence)
      let R : Mettapedia.Logic.PLNWorldModelFixpointClosure.RuleSet SemEState SemEQuery := ({r} : Set _)
      p ∈ Mettapedia.Logic.PLNWorldModelFixpointClosure.immediateIter R W0 ({p} : Set SemEQuery) 0
        ∧ q ∈ Mettapedia.Logic.PLNWorldModelFixpointClosure.immediateIter R W0 ({p} : Set SemEQuery) 1
        ∧ q ∈ Mettapedia.Logic.PLNWorldModelFixpointClosure.leastRuleClosure R W0 ({p} : Set SemEQuery)) := by
  refine ⟨?_, ?_⟩
  · exact
      Mettapedia.OSLF.Framework.ToposTOGLBridge.topos_representable_patternPred_piSigma_transport_pack_via_rulePack
        (lang := ctx.lang) (s := ctx.s) (seed := ctx.seed) (φ := ctx.φpred) (hNat := hφTop)
        (hPiSigmaPack := hPiSigmaPack)
        (f := modal.fm)
  · simpa using canonicalConsequenceRuleOn_compact_fixpoint
      (ctx := ctx) (modal := modal) (cat := cat) (fa := fa)
      (p := p) (q := q) (hstar := hstar) (φcat := φcat)
      (hStrengthFromEvidence := hStrengthFromEvidence)

/-- Goal-bundled combined endpoint:
explicit ΠΣ rule-pack transport package + canonical WM fixpoint closure, routed
through a reusable `CanonicalGoalArgs` value. -/
theorem canonical_rulePack_transport_pack_and_fixpoint_endpoint_of_goal
    (ctx : CanonicalClosureContext)
    (modal : CanonicalModalSquare ctx)
    (cat : CanonicalHyperSquare ctx)
    (fa : CanonicalFormulaArgs ctx)
    (hφTop :
      languageSortPredNaturality ctx.lang ctx.s ctx.seed ctx.φpred)
    (hPiSigmaPack :
      Mettapedia.OSLF.NativeType.PiSigmaPredicateRulePack
        (C := ConstructorObj ctx.lang))
    (goal : CanonicalGoalArgs ctx cat fa) :
    Mettapedia.OSLF.Framework.BeckChevalleyOSLF.RepresentablePiSigmaTransportPack
      (lang := ctx.lang) (s := ctx.s) (seed := ctx.seed) (φ := ctx.φpred)
      (hNat := hφTop) (f := modal.fm)
    ∧
    (let W0 : SemEState := semEState ctx.relEnv ctx.I fa.φf
      let r : WMConsequenceRuleOn SemEState SemEQuery :=
        canonicalConsequenceRuleOn_compact_of_goal
          (ctx := ctx) (modal := modal) (cat := cat) (fa := fa) (goal := goal)
      let R : Mettapedia.Logic.PLNWorldModelFixpointClosure.RuleSet SemEState SemEQuery := ({r} : Set _)
      goal.p ∈ Mettapedia.Logic.PLNWorldModelFixpointClosure.immediateIter R W0 ({goal.p} : Set SemEQuery) 0
        ∧ goal.q ∈ Mettapedia.Logic.PLNWorldModelFixpointClosure.immediateIter R W0 ({goal.p} : Set SemEQuery) 1
        ∧ goal.q ∈ Mettapedia.Logic.PLNWorldModelFixpointClosure.leastRuleClosure R W0 ({goal.p} : Set SemEQuery)) := by
  refine ⟨?_, ?_⟩
  · exact
      Mettapedia.OSLF.Framework.ToposTOGLBridge.topos_representable_patternPred_piSigma_transport_pack_via_rulePack
        (lang := ctx.lang) (s := ctx.s) (seed := ctx.seed) (φ := ctx.φpred) (hNat := hφTop)
        (hPiSigmaPack := hPiSigmaPack)
        (f := modal.fm)
  · simpa [canonicalConsequenceRuleOn_compact_of_goal] using
      (canonicalConsequenceRuleOn_compact_fixpoint
        (ctx := ctx) (modal := modal) (cat := cat) (fa := fa)
        (p := goal.p) (q := goal.q) (hstar := goal.hstar) (φcat := goal.φcat)
        (hStrengthFromEvidence := goal.hStrengthFromEvidence))

/-- Compact combined endpoint via canonical Prop-12 ΠΣ-rule instantiation.
This keeps a compatibility route while preserving the rule-pack-first surface. -/
theorem canonical_prop12_transport_pack_and_fixpoint_endpoint_compact
    (ctx : CanonicalClosureContext)
    (modal : CanonicalModalSquare ctx)
    (cat : CanonicalHyperSquare ctx)
    (fa : CanonicalFormulaArgs ctx)
    (hφTop :
      languageSortPredNaturality ctx.lang ctx.s ctx.seed ctx.φpred)
    (p q : Pattern)
    (hstar : OSLFTheoryStepStar ctx.relEnv p q)
    (φcat : cat.H.query cat.Bobj)
    (hStrengthFromEvidence :
      WMEvidenceObligation SemEState SemEQuery
        (semEState ctx.relEnv ctx.I fa.φf) p q →
      WMStrengthObligation SemEState SemEQuery
        (semEState ctx.relEnv ctx.I fa.φf) p q) :
    Mettapedia.OSLF.Framework.BeckChevalleyOSLF.RepresentablePiSigmaTransportPack
      (lang := ctx.lang) (s := ctx.s) (seed := ctx.seed) (φ := ctx.φpred)
      (hNat := hφTop) (f := modal.fm)
    ∧
    (let W0 : SemEState := semEState ctx.relEnv ctx.I fa.φf
      let r : WMConsequenceRuleOn SemEState SemEQuery :=
        canonicalConsequenceRuleOn_compact
          (ctx := ctx) (modal := modal) (cat := cat) (fa := fa)
          (p := p) (q := q) (hstar := hstar) (φcat := φcat)
          (hStrengthFromEvidence := hStrengthFromEvidence)
      let R : Mettapedia.Logic.PLNWorldModelFixpointClosure.RuleSet SemEState SemEQuery := ({r} : Set _)
      p ∈ Mettapedia.Logic.PLNWorldModelFixpointClosure.immediateIter R W0 ({p} : Set SemEQuery) 0
        ∧ q ∈ Mettapedia.Logic.PLNWorldModelFixpointClosure.immediateIter R W0 ({p} : Set SemEQuery) 1
        ∧ q ∈ Mettapedia.Logic.PLNWorldModelFixpointClosure.leastRuleClosure R W0 ({p} : Set SemEQuery)) := by
  refine ⟨?_, ?_⟩
  · exact
      Mettapedia.OSLF.Framework.ToposTOGLBridge.topos_representable_patternPred_piSigma_transport_pack_via_prop12
        (lang := ctx.lang) (s := ctx.s) (seed := ctx.seed) (φ := ctx.φpred) (hNat := hφTop)
        (f := modal.fm)
  · simpa using canonicalConsequenceRuleOn_compact_fixpoint
      (ctx := ctx) (modal := modal) (cat := cat) (fa := fa)
      (p := p) (q := q) (hstar := hstar) (φcat := φcat)
      (hStrengthFromEvidence := hStrengthFromEvidence)

/-- Goal-bundled combined endpoint via canonical Prop-12 ΠΣ-rule
compatibility instantiation. -/
theorem canonical_prop12_transport_pack_and_fixpoint_endpoint_of_goal
    (ctx : CanonicalClosureContext)
    (modal : CanonicalModalSquare ctx)
    (cat : CanonicalHyperSquare ctx)
    (fa : CanonicalFormulaArgs ctx)
    (hφTop :
      languageSortPredNaturality ctx.lang ctx.s ctx.seed ctx.φpred)
    (goal : CanonicalGoalArgs ctx cat fa) :
    Mettapedia.OSLF.Framework.BeckChevalleyOSLF.RepresentablePiSigmaTransportPack
      (lang := ctx.lang) (s := ctx.s) (seed := ctx.seed) (φ := ctx.φpred)
      (hNat := hφTop) (f := modal.fm)
    ∧
    (let W0 : SemEState := semEState ctx.relEnv ctx.I fa.φf
      let r : WMConsequenceRuleOn SemEState SemEQuery :=
        canonicalConsequenceRuleOn_compact_of_goal
          (ctx := ctx) (modal := modal) (cat := cat) (fa := fa) (goal := goal)
      let R : Mettapedia.Logic.PLNWorldModelFixpointClosure.RuleSet SemEState SemEQuery := ({r} : Set _)
      goal.p ∈ Mettapedia.Logic.PLNWorldModelFixpointClosure.immediateIter R W0 ({goal.p} : Set SemEQuery) 0
        ∧ goal.q ∈ Mettapedia.Logic.PLNWorldModelFixpointClosure.immediateIter R W0 ({goal.p} : Set SemEQuery) 1
        ∧ goal.q ∈ Mettapedia.Logic.PLNWorldModelFixpointClosure.leastRuleClosure R W0 ({goal.p} : Set SemEQuery)) := by
  refine ⟨?_, ?_⟩
  · exact
      Mettapedia.OSLF.Framework.ToposTOGLBridge.topos_representable_patternPred_piSigma_transport_pack_via_prop12
        (lang := ctx.lang) (s := ctx.s) (seed := ctx.seed) (φ := ctx.φpred) (hNat := hφTop)
        (f := modal.fm)
  · simpa [canonicalConsequenceRuleOn_compact_of_goal] using
      (canonicalConsequenceRuleOn_compact_fixpoint
        (ctx := ctx) (modal := modal) (cat := cat) (fa := fa)
        (p := goal.p) (q := goal.q) (hstar := goal.hstar) (φcat := goal.φcat)
        (hStrengthFromEvidence := goal.hStrengthFromEvidence))

/-- Transport-goal bundled variant of the rule-pack-first compact endpoint. -/
theorem canonical_rulePack_transport_pack_and_fixpoint_endpoint_of_transportGoal
    (ctx : CanonicalClosureContext)
    (modal : CanonicalModalSquare ctx)
    (cat : CanonicalHyperSquare ctx)
    (fa : CanonicalFormulaArgs ctx)
    (hPiSigmaPack :
      Mettapedia.OSLF.NativeType.PiSigmaPredicateRulePack
        (C := ConstructorObj ctx.lang))
    (transportGoal : CanonicalTransportGoalArgs ctx modal cat fa) :
    Mettapedia.OSLF.Framework.BeckChevalleyOSLF.RepresentablePiSigmaTransportPack
      (lang := ctx.lang) (s := ctx.s) (seed := ctx.seed) (φ := ctx.φpred)
      (hNat := transportGoal.hφTop) (f := modal.fm)
    ∧
    (let W0 : SemEState := semEState ctx.relEnv ctx.I fa.φf
      let r : WMConsequenceRuleOn SemEState SemEQuery :=
        canonicalConsequenceRuleOn_compact_of_goal
          (ctx := ctx) (modal := modal) (cat := cat) (fa := fa)
          (goal := transportGoal.goal)
      let R : Mettapedia.Logic.PLNWorldModelFixpointClosure.RuleSet SemEState SemEQuery := ({r} : Set _)
      transportGoal.goal.p ∈ Mettapedia.Logic.PLNWorldModelFixpointClosure.immediateIter R W0 ({transportGoal.goal.p} : Set SemEQuery) 0
        ∧ transportGoal.goal.q ∈ Mettapedia.Logic.PLNWorldModelFixpointClosure.immediateIter R W0 ({transportGoal.goal.p} : Set SemEQuery) 1
        ∧ transportGoal.goal.q ∈ Mettapedia.Logic.PLNWorldModelFixpointClosure.leastRuleClosure R W0 ({transportGoal.goal.p} : Set SemEQuery)) := by
  simpa using canonical_rulePack_transport_pack_and_fixpoint_endpoint_of_goal
    (ctx := ctx) (modal := modal) (cat := cat) (fa := fa)
    (hφTop := transportGoal.hφTop) (hPiSigmaPack := hPiSigmaPack)
    (goal := transportGoal.goal)

/-- Transport-goal bundled Prop-12 compatibility endpoint. -/
theorem canonical_prop12_transport_pack_and_fixpoint_endpoint_of_transportGoal
    (ctx : CanonicalClosureContext)
    (modal : CanonicalModalSquare ctx)
    (cat : CanonicalHyperSquare ctx)
    (fa : CanonicalFormulaArgs ctx)
    (transportGoal : CanonicalTransportGoalArgs ctx modal cat fa) :
    Mettapedia.OSLF.Framework.BeckChevalleyOSLF.RepresentablePiSigmaTransportPack
      (lang := ctx.lang) (s := ctx.s) (seed := ctx.seed) (φ := ctx.φpred)
      (hNat := transportGoal.hφTop) (f := modal.fm)
    ∧
    (let W0 : SemEState := semEState ctx.relEnv ctx.I fa.φf
      let r : WMConsequenceRuleOn SemEState SemEQuery :=
        canonicalConsequenceRuleOn_compact_of_goal
          (ctx := ctx) (modal := modal) (cat := cat) (fa := fa)
          (goal := transportGoal.goal)
      let R : Mettapedia.Logic.PLNWorldModelFixpointClosure.RuleSet SemEState SemEQuery := ({r} : Set _)
      transportGoal.goal.p ∈ Mettapedia.Logic.PLNWorldModelFixpointClosure.immediateIter R W0 ({transportGoal.goal.p} : Set SemEQuery) 0
        ∧ transportGoal.goal.q ∈ Mettapedia.Logic.PLNWorldModelFixpointClosure.immediateIter R W0 ({transportGoal.goal.p} : Set SemEQuery) 1
        ∧ transportGoal.goal.q ∈ Mettapedia.Logic.PLNWorldModelFixpointClosure.leastRuleClosure R W0 ({transportGoal.goal.p} : Set SemEQuery)) := by
  simpa using canonical_prop12_transport_pack_and_fixpoint_endpoint_of_goal
    (ctx := ctx) (modal := modal) (cat := cat) (fa := fa)
    (hφTop := transportGoal.hφTop)
    (goal := transportGoal.goal)

/-- Transport-goal bundled endpoint exposing direct Σ/Π transport inequalities
plus WM fixpoint closure, while routing through the compact transport-pack API
with an explicit ΠΣ rule-pack parameter. -/
theorem canonical_rulePack_transport_piSigma_and_fixpoint_of_transportGoal
    (ctx : CanonicalClosureContext)
    (modal : CanonicalModalSquare ctx)
    (cat : CanonicalHyperSquare ctx)
    (fa : CanonicalFormulaArgs ctx)
    (hPiSigmaPack :
      Mettapedia.OSLF.NativeType.PiSigmaPredicateRulePack
        (C := ConstructorObj ctx.lang))
    (transportGoal : CanonicalTransportGoalArgs ctx modal cat fa) :
    ((((Mettapedia.GSLT.Topos.presheafChangeOfBase
        (C := ConstructorObj ctx.lang)).directImage modal.fm)
        ((languageSortFiber_ofPatternPred ctx.lang ctx.s ctx.seed ctx.φpred transportGoal.hφTop :
          CategoryTheory.Subfunctor (languageSortRepresentableObj ctx.lang ctx.s)))
      ≤ transportGoal.ψ)
      ↔
      ((show CategoryTheory.Subfunctor (languageSortRepresentableObj ctx.lang ctx.s)
          from languageSortFiber_ofPatternPred
            ctx.lang ctx.s ctx.seed ctx.φpred transportGoal.hφTop)
        ≤ ((Mettapedia.GSLT.Topos.presheafChangeOfBase
          (C := ConstructorObj ctx.lang)).pullback modal.fm) transportGoal.ψ))
    ∧
    ((((Mettapedia.GSLT.Topos.presheafChangeOfBase
        (C := ConstructorObj ctx.lang)).pullback modal.fm) transportGoal.χ
      ≤ languageSortFiber_ofPatternPred
          ctx.lang ctx.s ctx.seed ctx.φpred transportGoal.hφTop)
      ↔
      (transportGoal.χ ≤
        ((Mettapedia.GSLT.Topos.presheafChangeOfBase
          (C := ConstructorObj ctx.lang)).universalImage modal.fm)
          (languageSortFiber_ofPatternPred
            ctx.lang ctx.s ctx.seed ctx.φpred transportGoal.hφTop)))
    ∧
    (let W0 : SemEState := semEState ctx.relEnv ctx.I fa.φf
      let r : WMConsequenceRuleOn SemEState SemEQuery :=
        canonicalConsequenceRuleOn_compact_of_goal
          (ctx := ctx) (modal := modal) (cat := cat) (fa := fa)
          (goal := transportGoal.goal)
      let R : Mettapedia.Logic.PLNWorldModelFixpointClosure.RuleSet SemEState SemEQuery := ({r} : Set _)
      transportGoal.goal.p ∈ Mettapedia.Logic.PLNWorldModelFixpointClosure.immediateIter R W0 ({transportGoal.goal.p} : Set SemEQuery) 0
        ∧ transportGoal.goal.q ∈ Mettapedia.Logic.PLNWorldModelFixpointClosure.immediateIter R W0 ({transportGoal.goal.p} : Set SemEQuery) 1
        ∧ transportGoal.goal.q ∈ Mettapedia.Logic.PLNWorldModelFixpointClosure.leastRuleClosure R W0 ({transportGoal.goal.p} : Set SemEQuery)) := by
  have hPack :=
    canonical_rulePack_transport_pack_and_fixpoint_endpoint_of_transportGoal
      (ctx := ctx) (modal := modal) (cat := cat) (fa := fa)
      (hPiSigmaPack := hPiSigmaPack)
      (transportGoal := transportGoal)
  have hPiSigma : ((((Mettapedia.GSLT.Topos.presheafChangeOfBase
        (C := ConstructorObj ctx.lang)).directImage modal.fm)
        ((languageSortFiber_ofPatternPred ctx.lang ctx.s ctx.seed ctx.φpred transportGoal.hφTop :
          CategoryTheory.Subfunctor (languageSortRepresentableObj ctx.lang ctx.s)))
      ≤ transportGoal.ψ)
      ↔
      ((show CategoryTheory.Subfunctor (languageSortRepresentableObj ctx.lang ctx.s)
          from languageSortFiber_ofPatternPred
            ctx.lang ctx.s ctx.seed ctx.φpred transportGoal.hφTop)
        ≤ ((Mettapedia.GSLT.Topos.presheafChangeOfBase
          (C := ConstructorObj ctx.lang)).pullback modal.fm) transportGoal.ψ))
    ∧
    ((((Mettapedia.GSLT.Topos.presheafChangeOfBase
        (C := ConstructorObj ctx.lang)).pullback modal.fm) transportGoal.χ
      ≤ languageSortFiber_ofPatternPred
          ctx.lang ctx.s ctx.seed ctx.φpred transportGoal.hφTop)
      ↔
      (transportGoal.χ ≤
        ((Mettapedia.GSLT.Topos.presheafChangeOfBase
          (C := ConstructorObj ctx.lang)).universalImage modal.fm)
          (languageSortFiber_ofPatternPred
            ctx.lang ctx.s ctx.seed ctx.φpred transportGoal.hφTop))) :=
    hPack.1.piSigma_transport transportGoal.χ transportGoal.ψ
  exact ⟨hPiSigma.1, hPiSigma.2, hPack.2⟩

/-- Transport-goal bundled endpoint exposing direct Σ/Π transport inequalities
plus WM fixpoint closure, via the canonical Prop-12 ΠΣ rule-pack
compatibility instantiation. -/
theorem canonical_prop12_transport_piSigma_and_fixpoint_of_transportGoal
    (ctx : CanonicalClosureContext)
    (modal : CanonicalModalSquare ctx)
    (cat : CanonicalHyperSquare ctx)
    (fa : CanonicalFormulaArgs ctx)
    (transportGoal : CanonicalTransportGoalArgs ctx modal cat fa) :
    ((((Mettapedia.GSLT.Topos.presheafChangeOfBase
        (C := ConstructorObj ctx.lang)).directImage modal.fm)
        ((languageSortFiber_ofPatternPred ctx.lang ctx.s ctx.seed ctx.φpred transportGoal.hφTop :
          CategoryTheory.Subfunctor (languageSortRepresentableObj ctx.lang ctx.s)))
      ≤ transportGoal.ψ)
      ↔
      ((show CategoryTheory.Subfunctor (languageSortRepresentableObj ctx.lang ctx.s)
          from languageSortFiber_ofPatternPred
            ctx.lang ctx.s ctx.seed ctx.φpred transportGoal.hφTop)
        ≤ ((Mettapedia.GSLT.Topos.presheafChangeOfBase
          (C := ConstructorObj ctx.lang)).pullback modal.fm) transportGoal.ψ))
    ∧
    ((((Mettapedia.GSLT.Topos.presheafChangeOfBase
        (C := ConstructorObj ctx.lang)).pullback modal.fm) transportGoal.χ
      ≤ languageSortFiber_ofPatternPred
          ctx.lang ctx.s ctx.seed ctx.φpred transportGoal.hφTop)
      ↔
      (transportGoal.χ ≤
        ((Mettapedia.GSLT.Topos.presheafChangeOfBase
          (C := ConstructorObj ctx.lang)).universalImage modal.fm)
          (languageSortFiber_ofPatternPred
            ctx.lang ctx.s ctx.seed ctx.φpred transportGoal.hφTop)))
    ∧
    (let W0 : SemEState := semEState ctx.relEnv ctx.I fa.φf
      let r : WMConsequenceRuleOn SemEState SemEQuery :=
        canonicalConsequenceRuleOn_compact_of_goal
          (ctx := ctx) (modal := modal) (cat := cat) (fa := fa)
          (goal := transportGoal.goal)
      let R : Mettapedia.Logic.PLNWorldModelFixpointClosure.RuleSet SemEState SemEQuery := ({r} : Set _)
      transportGoal.goal.p ∈ Mettapedia.Logic.PLNWorldModelFixpointClosure.immediateIter R W0 ({transportGoal.goal.p} : Set SemEQuery) 0
        ∧ transportGoal.goal.q ∈ Mettapedia.Logic.PLNWorldModelFixpointClosure.immediateIter R W0 ({transportGoal.goal.p} : Set SemEQuery) 1
        ∧ transportGoal.goal.q ∈ Mettapedia.Logic.PLNWorldModelFixpointClosure.leastRuleClosure R W0 ({transportGoal.goal.p} : Set SemEQuery)) := by
  simpa using canonical_rulePack_transport_piSigma_and_fixpoint_of_transportGoal
    (ctx := ctx) (modal := modal) (cat := cat) (fa := fa)
    (hPiSigmaPack := Mettapedia.OSLF.NativeType.prop12_piSigmaPredicateRulePack
      (C := ConstructorObj ctx.lang))
    (transportGoal := transportGoal)

/-- Formula-level step endpoint wrapper with policy synthesized from path-order
and controlled-step-policy assumptions. -/
theorem oslf_formula_ntt_wm_step_sound_of_pathOrder
    (lang : LanguageDef) (s : LangSort lang)
    (seed qComm : Pattern) (φpred : Pattern → Prop)
    (relEnv : RelationEnv)
    (I : EvidenceAtomSem)
    (hPathOrder :
      ∀ {a b : LangSort lang}
        (g : SortPath lang a b) (h : SortPath lang b s),
          pathSem lang g (pathSem lang h seed) = pathSem lang (g.comp h) seed)
    (hSemEPolicy : ControlledStepPolicy relEnv I)
    {Pm Bm Dm : CategoryTheory.Functor (Opposite (ConstructorObj lang)) (Type _)}
    (pi1m : Pm ⟶ (languageSortRepresentableObj lang s))
    (pi2m : Pm ⟶ Bm)
    (fm : (languageSortRepresentableObj lang s) ⟶ Dm)
    (gm : Bm ⟶ Dm)
    (hpbm : CategoryTheory.IsPullback pi1m pi2m fm gm)
    (hfm : CategoryTheory.Mono fm) (hpi2m : CategoryTheory.Mono pi2m)
    {Xmodal : Opposite (ConstructorObj lang)}
    (pmodal : Pattern)
    (H : Mettapedia.Logic.PLNWorldModelHyperdoctrine.WMHyperdoctrine SemEState)
    {P Aobj Bobj D : H.Obj}
    (pi1 : P ⟶ Aobj) (pi2 : P ⟶ Bobj) (fcat : Aobj ⟶ D) (gcat : Bobj ⟶ D)
    (hpb : CategoryTheory.IsPullback pi1 pi2 fcat gcat)
    (hmfcat : CategoryTheory.Mono fcat) (hmpi2 : CategoryTheory.Mono pi2)
    (queryOfAtom : String → Pattern → Pattern)
    (φf : OSLFFormula)
    (hφ : StepEvidenceControlledByPolicy hSemEPolicy φf)
    (Xobj : PLNObj)
    {Xgr : Opposite (Mettapedia.OSLF.Framework.ConstructorCategory.ConstructorObj
      Mettapedia.OSLF.Framework.MeTTaToNTT.mettaFull)}
    (p q : Pattern)
    (hstep : OSLFTheoryStep relEnv p q)
    (φcat : H.query Bobj) :
    Mettapedia.OSLF.Framework.OSLFNTTWMBridge.FormulaGraphEndpoint
      (State := SemEState)
      (relEnv := relEnv)
      (W := semEState relEnv I φf)
      (queryOfAtom := queryOfAtom)
      (φf := φf) (Xobj := Xobj) (X := Xgr) (p := p)
    ∧
    (((CategoryTheory.Subobject.map pi2m).obj
        ((CategoryTheory.Subobject.pullback pi1m).obj
          (modalSubobjectOfPatternPred lang s seed
            (commDi qComm (PathSemClosedPred lang φpred))
            (languageSortPredNaturality_commDi_pathSemClosed_of_pkg
              lang s seed qComm φpred
              (commDiPathSemLiftPkg_of_pathSem_comm_subst_and_path_order
                lang s seed qComm hPathOrder))))
      =
    (CategoryTheory.Subobject.pullback gm).obj
        ((CategoryTheory.Subobject.map fm).obj
          (modalSubobjectOfPatternPred lang s seed
            (commDi qComm (PathSemClosedPred lang φpred))
            (languageSortPredNaturality_commDi_pathSemClosed_of_pkg
              lang s seed qComm φpred
              (commDiPathSemLiftPkg_of_pathSem_comm_subst_and_path_order
                lang s seed qComm hPathOrder)))))
    ∧
    (langDiamondUsing relEnv lang
      (commDi qComm (PathSemClosedPred lang φpred)) pmodal ↔
      ∃ e : (Mettapedia.OSLF.Framework.ToposReduction.reductionGraphUsing
        (C := ConstructorObj lang) relEnv lang).Edge.obj Xmodal,
        ((Mettapedia.OSLF.Framework.ToposReduction.reductionGraphUsing
          (C := ConstructorObj lang) relEnv lang).source.app Xmodal e).down = pmodal ∧
        ∃ u : Pattern,
          Mettapedia.OSLF.MeTTaIL.Substitution.commSubst u qComm =
            ((Mettapedia.OSLF.Framework.ToposReduction.reductionGraphUsing
              (C := ConstructorObj lang) relEnv lang).target.app Xmodal e).down ∧
          PathSemClosedPred lang φpred u)
    ∧
    EndpointStatement (H := H) pi1 pi2 fcat gcat (semEState relEnv I φf) φcat
    ∧
    WMEvidenceObligation SemEState SemEQuery
      (semEState relEnv I φf) p q) := by
  let policy : ModalSubobjectControlledPolicy lang s seed qComm relEnv I :=
    ModalSubobjectControlledPolicy.of_pathOrder
      lang s seed qComm relEnv I hPathOrder hSemEPolicy
  exact oslf_formula_ntt_wm_step_sound
    (lang := lang) (s := s)
    (seed := seed) (qComm := qComm) (φpred := φpred)
    (relEnv := relEnv)
    (I := I)
    (policy := policy)
    (pi1m := pi1m) (pi2m := pi2m) (fm := fm) (gm := gm)
    (hpbm := hpbm) (hfm := hfm) (hpi2m := hpi2m)
    (Xmodal := Xmodal) (pmodal := pmodal)
    (H := H)
    (pi1 := pi1) (pi2 := pi2) (fcat := fcat) (gcat := gcat)
    (hpb := hpb) (hmfcat := hmfcat) (hmpi2 := hmpi2)
    (queryOfAtom := queryOfAtom)
    (φf := φf) (hφ := by simpa [policy] using hφ)
    (Xobj := Xobj) (Xgr := Xgr)
    (p := p) (q := q) (hstep := hstep) (φcat := φcat)

/-- Unified endpoint: consume the Topos-facing representable Π/Σ transport
package (routed through Prop-12) together with the formula-level path-order
star closure endpoint. -/
theorem oslf_formula_ntt_wm_star_internalLogic_endpoint_of_pathOrder
    (lang : LanguageDef)
    (s : LangSort lang)
    (seed qComm : Pattern) (φpred : Pattern → Prop)
    (relEnv : RelationEnv)
    (I : EvidenceAtomSem)
    (hPathOrder :
      ∀ {a b : LangSort lang}
        (g : SortPath lang a b) (h : SortPath lang b s),
          pathSem lang g (pathSem lang h seed) = pathSem lang (g.comp h) seed)
    (hSemEPolicy : ControlledStepPolicy relEnv I)
    (hφTop :
      Mettapedia.OSLF.Framework.CategoryBridge.languageSortPredNaturality
        lang s seed φpred)
    {Pm Bm Dm : CategoryTheory.Functor (Opposite (ConstructorObj lang)) (Type _)}
    (pi1m : Pm ⟶ (languageSortRepresentableObj lang s))
    (pi2m : Pm ⟶ Bm)
    (fm : (languageSortRepresentableObj lang s) ⟶ Dm)
    (gm : Bm ⟶ Dm)
    (hpbm : CategoryTheory.IsPullback pi1m pi2m fm gm)
    (hfm : CategoryTheory.Mono fm) (hpi2m : CategoryTheory.Mono pi2m)
    {Xmodal : Opposite (ConstructorObj lang)}
    (pmodal : Pattern)
    (H : Mettapedia.Logic.PLNWorldModelHyperdoctrine.WMHyperdoctrine SemEState)
    {P Aobj Bobj D : H.Obj}
    (pi1 : P ⟶ Aobj) (pi2 : P ⟶ Bobj) (fcat : Aobj ⟶ D) (gcat : Bobj ⟶ D)
    (hpb : CategoryTheory.IsPullback pi1 pi2 fcat gcat)
    (hmfcat : CategoryTheory.Mono fcat) (hmpi2 : CategoryTheory.Mono pi2)
    (queryOfAtom : String → Pattern → Pattern)
    (φf : OSLFFormula)
    (hφ : StepEvidenceControlledByPolicy hSemEPolicy φf)
    (Xobj : PLNObj)
    {Xgr : Opposite (Mettapedia.OSLF.Framework.ConstructorCategory.ConstructorObj
      Mettapedia.OSLF.Framework.MeTTaToNTT.mettaFull)}
    (p q : Pattern)
    (hstar : OSLFTheoryStepStar relEnv p q)
    (φcat : H.query Bobj) :
    ((∀ (χ ψ : CategoryTheory.Subfunctor Dm),
      ((((Mettapedia.GSLT.Topos.presheafChangeOfBase
          (C := ConstructorObj lang)).directImage fm)
          ((languageSortFiber_ofPatternPred lang s seed φpred hφTop :
            CategoryTheory.Subfunctor (languageSortRepresentableObj lang s)))
        ≤ ψ)
        ↔
        ((show CategoryTheory.Subfunctor (languageSortRepresentableObj lang s)
            from languageSortFiber_ofPatternPred lang s seed φpred hφTop)
          ≤ ((Mettapedia.GSLT.Topos.presheafChangeOfBase
            (C := ConstructorObj lang)).pullback fm) ψ))
      ∧
      ((((Mettapedia.GSLT.Topos.presheafChangeOfBase
          (C := ConstructorObj lang)).pullback fm) χ
        ≤ languageSortFiber_ofPatternPred lang s seed φpred hφTop)
        ↔
        (χ ≤
          (Mettapedia.GSLT.Topos.presheafChangeOfBase
            (C := ConstructorObj lang)).universalImage fm
            (languageSortFiber_ofPatternPred lang s seed φpred hφTop)))))
    ∧
    Mettapedia.OSLF.Framework.OSLFNTTWMBridge.FormulaGraphEndpoint
      (State := SemEState)
      (relEnv := relEnv)
      (W := semEState relEnv I φf)
      (queryOfAtom := queryOfAtom)
      (φf := φf) (Xobj := Xobj) (X := Xgr) (p := p)
    ∧
    EndpointStatement (H := H) pi1 pi2 fcat gcat (semEState relEnv I φf) φcat
    ∧
    WMEvidenceObligation SemEState SemEQuery
      (semEState relEnv I φf) p q := by
  have hTransport :=
    Mettapedia.OSLF.Framework.ToposTOGLBridge.topos_representable_patternPred_piSigma_transport_via_prop12_pack
      (lang := lang) (s := s) (seed := seed) (φ := φpred) (hNat := hφTop)
      (f := fm)
  have hClosure :=
    oslf_formula_ntt_wm_star_sound_of_pathOrder
      (lang := lang) (s := s)
      (seed := seed) (qComm := qComm) (φpred := φpred)
      (relEnv := relEnv)
      (I := I)
      (hPathOrder := hPathOrder)
      (hSemEPolicy := hSemEPolicy)
      (pi1m := pi1m) (pi2m := pi2m) (fm := fm) (gm := gm)
      (hpbm := hpbm) (hfm := hfm) (hpi2m := hpi2m)
      (Xmodal := Xmodal) (pmodal := pmodal)
      (H := H)
      (pi1 := pi1) (pi2 := pi2) (fcat := fcat) (gcat := gcat)
      (hpb := hpb) (hmfcat := hmfcat) (hmpi2 := hmpi2)
      (queryOfAtom := queryOfAtom)
      (φf := φf) (hφ := hφ)
      (Xobj := Xobj) (Xgr := Xgr)
      (p := p) (q := q) (hstar := hstar) (φcat := φcat)
  exact ⟨hTransport, hClosure.1, hClosure.2.2.2.1, hClosure.2.2.2.2⟩

/-- Canary: composed star closure still discharges WM evidence obligations when
the Topos-facing Π/Σ transport endpoint is the logic entry point. -/
theorem oslf_formula_ntt_wm_star_wmObligation_via_topos_transport_canary_of_pathOrder
    (lang : LanguageDef)
    (s : LangSort lang)
    (seed : Pattern) (φpred : Pattern → Prop)
    (relEnv : RelationEnv)
    (I : EvidenceAtomSem)
    (hSemEPolicy : ControlledStepPolicy relEnv I)
    (hφTop :
      Mettapedia.OSLF.Framework.CategoryBridge.languageSortPredNaturality
        lang s seed φpred)
    {Dm : CategoryTheory.Functor (Opposite (ConstructorObj lang)) (Type _)}
    (fm : (languageSortRepresentableObj lang s) ⟶ Dm)
    (φf : OSLFFormula)
    (hφ : StepEvidenceControlledByPolicy hSemEPolicy φf)
    (p q : Pattern)
    (hstar : OSLFTheoryStepStar relEnv p q)
    (χ ψ : CategoryTheory.Subfunctor Dm) :
    (((((Mettapedia.GSLT.Topos.presheafChangeOfBase
        (C := ConstructorObj lang)).directImage fm)
        ((languageSortFiber_ofPatternPred lang s seed φpred hφTop :
          CategoryTheory.Subfunctor (languageSortRepresentableObj lang s)))
      ≤ ψ)
      ↔
      ((show CategoryTheory.Subfunctor (languageSortRepresentableObj lang s)
          from languageSortFiber_ofPatternPred lang s seed φpred hφTop)
        ≤ ((Mettapedia.GSLT.Topos.presheafChangeOfBase
          (C := ConstructorObj lang)).pullback fm) ψ))
    ∧
    ((((Mettapedia.GSLT.Topos.presheafChangeOfBase
        (C := ConstructorObj lang)).pullback fm) χ
      ≤ languageSortFiber_ofPatternPred lang s seed φpred hφTop)
      ↔
      (χ ≤
        (Mettapedia.GSLT.Topos.presheafChangeOfBase
          (C := ConstructorObj lang)).universalImage fm
          (languageSortFiber_ofPatternPred lang s seed φpred hφTop))))
    ∧
    WMEvidenceObligation SemEState SemEQuery
      (semEState relEnv I φf) p q := by
  have hTransport :=
    Mettapedia.OSLF.Framework.ToposTOGLBridge.topos_representable_patternPred_piSigma_transport_via_prop12_pack
      (lang := lang) (s := s) (seed := seed) (φ := φpred) (hNat := hφTop)
      (f := fm)
  let Iev := semEPolicyEvidenceInterface
    (relEnv := relEnv) (I := I) (policy := hSemEPolicy) (φ := φf) hφ
  have hSide : Iev.side (semEState relEnv I φf) := rfl
  exact ⟨hTransport χ ψ, Iev.stepStar_sound hSide hstar⟩

/-- Canonical-to-fixpoint endpoint:
extract the formula-level canonical star closure obligation, package it as a
singleton WM consequence rule, and show it appears in both one-step iteration
and least-fixpoint closure (`immediateIter`/`leastRuleClosure`). -/
theorem canonical_star_to_fixpoint_endpoint
    (ctx : CanonicalClosureContext)
    {Pm Bm Dm : CategoryTheory.Functor (Opposite (ConstructorObj ctx.lang)) (Type _)}
    (pi1m : Pm ⟶ (languageSortRepresentableObj ctx.lang ctx.s))
    (pi2m : Pm ⟶ Bm)
    (fm : (languageSortRepresentableObj ctx.lang ctx.s) ⟶ Dm)
    (gm : Bm ⟶ Dm)
    (hpbm : CategoryTheory.IsPullback pi1m pi2m fm gm)
    (hfm : CategoryTheory.Mono fm) (hpi2m : CategoryTheory.Mono pi2m)
    {Xmodal : Opposite (ConstructorObj ctx.lang)}
    (pmodal : Pattern)
    (H : Mettapedia.Logic.PLNWorldModelHyperdoctrine.WMHyperdoctrine SemEState)
    {P Aobj Bobj D : H.Obj}
    (pi1 : P ⟶ Aobj) (pi2 : P ⟶ Bobj) (fcat : Aobj ⟶ D) (gcat : Bobj ⟶ D)
    (hpb : CategoryTheory.IsPullback pi1 pi2 fcat gcat)
    (hmfcat : CategoryTheory.Mono fcat) (hmpi2 : CategoryTheory.Mono pi2)
    (queryOfAtom : String → Pattern → Pattern)
    (φf : OSLFFormula)
    (hφ : StepEvidenceControlledByPolicy ctx.hSemEPolicy φf)
    (Xobj : PLNObj)
    {Xgr : Opposite (Mettapedia.OSLF.Framework.ConstructorCategory.ConstructorObj
      Mettapedia.OSLF.Framework.MeTTaToNTT.mettaFull)}
    (p q : Pattern)
    (hstar : OSLFTheoryStepStar ctx.relEnv p q)
    (φcat : H.query Bobj)
    (hStrengthFromEvidence :
      WMEvidenceObligation SemEState SemEQuery
        (semEState ctx.relEnv ctx.I φf) p q →
      WMStrengthObligation SemEState SemEQuery
        (semEState ctx.relEnv ctx.I φf) p q) :
    let W0 : SemEState := semEState ctx.relEnv ctx.I φf
    let r : WMConsequenceRuleOn SemEState SemEQuery :=
      { side := fun W => W = W0
        premise := p
        conclusion := q
        sound := by
          intro W hW
          subst hW
          have hCore :=
            oslf_formula_ntt_wm_star_sound_ctx
              (ctx := ctx)
              (pi1m := pi1m) (pi2m := pi2m) (fm := fm) (gm := gm)
              (hpbm := hpbm) (hfm := hfm) (hpi2m := hpi2m)
              (Xmodal := Xmodal) (pmodal := pmodal)
              (H := H)
              (pi1 := pi1) (pi2 := pi2) (fcat := fcat) (gcat := gcat)
              (hpb := hpb) (hmfcat := hmfcat) (hmpi2 := hmpi2)
              (queryOfAtom := queryOfAtom)
              (φf := φf) (hφ := hφ)
              (Xobj := Xobj) (Xgr := Xgr)
              (p := p) (q := q) (hstar := hstar) (φcat := φcat)
          rcases hCore with ⟨_hFormula, hRest⟩
          rcases hRest with ⟨_hModal, hRest⟩
          rcases hRest with ⟨_hDia, hRest⟩
          rcases hRest with ⟨_hEndpoint, hEv⟩
          exact hStrengthFromEvidence hEv }
    let R : Mettapedia.Logic.PLNWorldModelFixpointClosure.RuleSet SemEState SemEQuery := ({r} : Set _)
    p ∈ Mettapedia.Logic.PLNWorldModelFixpointClosure.immediateIter R W0 ({p} : Set SemEQuery) 0
      ∧ q ∈ Mettapedia.Logic.PLNWorldModelFixpointClosure.immediateIter R W0 ({p} : Set SemEQuery) 1
      ∧ q ∈ Mettapedia.Logic.PLNWorldModelFixpointClosure.leastRuleClosure R W0 ({p} : Set SemEQuery) := by
  classical
  dsimp
  let W0 : SemEState := semEState ctx.relEnv ctx.I φf
  let r : WMConsequenceRuleOn SemEState SemEQuery :=
    { side := fun W => W = W0
      premise := p
      conclusion := q
      sound := by
        intro W hW
        subst hW
        have hCore :=
          oslf_formula_ntt_wm_star_sound_ctx
            (ctx := ctx)
            (pi1m := pi1m) (pi2m := pi2m) (fm := fm) (gm := gm)
            (hpbm := hpbm) (hfm := hfm) (hpi2m := hpi2m)
            (Xmodal := Xmodal) (pmodal := pmodal)
            (H := H)
            (pi1 := pi1) (pi2 := pi2) (fcat := fcat) (gcat := gcat)
            (hpb := hpb) (hmfcat := hmfcat) (hmpi2 := hmpi2)
            (queryOfAtom := queryOfAtom)
            (φf := φf) (hφ := hφ)
            (Xobj := Xobj) (Xgr := Xgr)
            (p := p) (q := q) (hstar := hstar) (φcat := φcat)
        rcases hCore with ⟨_hFormula, hRest⟩
        rcases hRest with ⟨_hModal, hRest⟩
        rcases hRest with ⟨_hDia, hRest⟩
        rcases hRest with ⟨_hEndpoint, hEv⟩
        exact hStrengthFromEvidence hEv }
  let R : Mettapedia.Logic.PLNWorldModelFixpointClosure.RuleSet SemEState SemEQuery := ({r} : Set _)
  have hp0 :
      p ∈ Mettapedia.Logic.PLNWorldModelFixpointClosure.immediateIter R W0 ({p} : Set SemEQuery) 0 := by
    simp [Mettapedia.Logic.PLNWorldModelFixpointClosure.immediateIter]
  have hq1 :
      q ∈ Mettapedia.Logic.PLNWorldModelFixpointClosure.immediateIter R W0 ({p} : Set SemEQuery) 1 := by
    change q ∈ Mettapedia.Logic.PLNWorldModelFixpointClosure.immediateStep R W0
      ({p} : Set SemEQuery) ({p} : Set SemEQuery)
    refine Or.inr ?_
    refine ⟨r, by simp [R], by simp [r, W0], ?_, by simp [r]⟩
    show p ∈ ({p} : Set SemEQuery)
    simp
  have hqLfp :
      q ∈ Mettapedia.Logic.PLNWorldModelFixpointClosure.leastRuleClosure R W0 ({p} : Set SemEQuery) :=
    Mettapedia.Logic.PLNWorldModelFixpointClosure.immediateIter_subset_leastRuleClosure
      (State := SemEState) (Query := SemEQuery) R W0 ({p} : Set SemEQuery) 1 hq1
  exact ⟨hp0, hq1, hqLfp⟩

/-- Combined canonical endpoint:
consume the explicit representable Π/Σ rule-pack transport package and the
canonical star-to-fixpoint closure theorem under one shared context surface. -/
theorem canonical_rulePack_transport_and_fixpoint_endpoint
    (ctx : CanonicalClosureContext)
    (hφTop :
      languageSortPredNaturality ctx.lang ctx.s ctx.seed ctx.φpred)
    {Pm Bm Dm : CategoryTheory.Functor (Opposite (ConstructorObj ctx.lang)) (Type _)}
    (pi1m : Pm ⟶ (languageSortRepresentableObj ctx.lang ctx.s))
    (pi2m : Pm ⟶ Bm)
    (fm : (languageSortRepresentableObj ctx.lang ctx.s) ⟶ Dm)
    (gm : Bm ⟶ Dm)
    (hpbm : CategoryTheory.IsPullback pi1m pi2m fm gm)
    (hfm : CategoryTheory.Mono fm) (hpi2m : CategoryTheory.Mono pi2m)
    {Xmodal : Opposite (ConstructorObj ctx.lang)}
    (pmodal : Pattern)
    (H : Mettapedia.Logic.PLNWorldModelHyperdoctrine.WMHyperdoctrine SemEState)
    {P Aobj Bobj D : H.Obj}
    (pi1 : P ⟶ Aobj) (pi2 : P ⟶ Bobj) (fcat : Aobj ⟶ D) (gcat : Bobj ⟶ D)
    (hpb : CategoryTheory.IsPullback pi1 pi2 fcat gcat)
    (hmfcat : CategoryTheory.Mono fcat) (hmpi2 : CategoryTheory.Mono pi2)
    (queryOfAtom : String → Pattern → Pattern)
    (φf : OSLFFormula)
    (hφ : StepEvidenceControlledByPolicy ctx.hSemEPolicy φf)
    (Xobj : PLNObj)
    {Xgr : Opposite (Mettapedia.OSLF.Framework.ConstructorCategory.ConstructorObj
      Mettapedia.OSLF.Framework.MeTTaToNTT.mettaFull)}
    (p q : Pattern)
    (hstar : OSLFTheoryStepStar ctx.relEnv p q)
    (φcat : H.query Bobj)
    (χ ψ : CategoryTheory.Subfunctor Dm)
    (hStrengthFromEvidence :
      WMEvidenceObligation SemEState SemEQuery
        (semEState ctx.relEnv ctx.I φf) p q →
      WMStrengthObligation SemEState SemEQuery
        (semEState ctx.relEnv ctx.I φf) p q) :
    ((((Mettapedia.GSLT.Topos.presheafChangeOfBase
        (C := ConstructorObj ctx.lang)).directImage fm)
        ((languageSortFiber_ofPatternPred ctx.lang ctx.s ctx.seed ctx.φpred hφTop :
          CategoryTheory.Subfunctor (languageSortRepresentableObj ctx.lang ctx.s)))
      ≤ ψ)
      ↔
      ((show CategoryTheory.Subfunctor (languageSortRepresentableObj ctx.lang ctx.s)
          from languageSortFiber_ofPatternPred ctx.lang ctx.s ctx.seed ctx.φpred hφTop)
        ≤ ((Mettapedia.GSLT.Topos.presheafChangeOfBase
          (C := ConstructorObj ctx.lang)).pullback fm) ψ))
    ∧
    ((((Mettapedia.GSLT.Topos.presheafChangeOfBase
        (C := ConstructorObj ctx.lang)).pullback fm) χ
      ≤ languageSortFiber_ofPatternPred ctx.lang ctx.s ctx.seed ctx.φpred hφTop)
      ↔
      (χ ≤
        ((Mettapedia.GSLT.Topos.presheafChangeOfBase
          (C := ConstructorObj ctx.lang)).universalImage fm)
          (languageSortFiber_ofPatternPred ctx.lang ctx.s ctx.seed ctx.φpred hφTop)))
    ∧
    (let W0 : SemEState := semEState ctx.relEnv ctx.I φf
      let r : WMConsequenceRuleOn SemEState SemEQuery :=
        { side := fun W => W = W0
          premise := p
          conclusion := q
          sound := by
            intro W hW
            subst hW
            have hCore :=
              oslf_formula_ntt_wm_star_sound_ctx
                (ctx := ctx)
                (pi1m := pi1m) (pi2m := pi2m) (fm := fm) (gm := gm)
                (hpbm := hpbm) (hfm := hfm) (hpi2m := hpi2m)
                (Xmodal := Xmodal) (pmodal := pmodal)
                (H := H)
                (pi1 := pi1) (pi2 := pi2) (fcat := fcat) (gcat := gcat)
                (hpb := hpb) (hmfcat := hmfcat) (hmpi2 := hmpi2)
                (queryOfAtom := queryOfAtom)
                (φf := φf) (hφ := hφ)
                (Xobj := Xobj) (Xgr := Xgr)
                (p := p) (q := q) (hstar := hstar) (φcat := φcat)
            rcases hCore with ⟨_hFormula, hRest⟩
            rcases hRest with ⟨_hModal, hRest⟩
            rcases hRest with ⟨_hDia, hRest⟩
            rcases hRest with ⟨_hEndpoint, hEv⟩
            exact hStrengthFromEvidence hEv }
      let R : Mettapedia.Logic.PLNWorldModelFixpointClosure.RuleSet SemEState SemEQuery := ({r} : Set _)
      p ∈ Mettapedia.Logic.PLNWorldModelFixpointClosure.immediateIter R W0 ({p} : Set SemEQuery) 0
        ∧ q ∈ Mettapedia.Logic.PLNWorldModelFixpointClosure.immediateIter R W0 ({p} : Set SemEQuery) 1
        ∧ q ∈ Mettapedia.Logic.PLNWorldModelFixpointClosure.leastRuleClosure R W0 ({p} : Set SemEQuery)) := by
  let modal : CanonicalModalSquare ctx := {
    Pm := Pm
    Bm := Bm
    Dm := Dm
    pi1m := pi1m
    pi2m := pi2m
    fm := fm
    gm := gm
    hpbm := hpbm
    hfm := hfm
    hpi2m := hpi2m
    Xmodal := Xmodal
    pmodal := pmodal
  }
  let cat : CanonicalHyperSquare ctx := {
    H := H
    P := P
    Aobj := Aobj
    Bobj := Bobj
    D := D
    pi1 := pi1
    pi2 := pi2
    fcat := fcat
    gcat := gcat
    hpb := hpb
    hmfcat := hmfcat
    hmpi2 := hmpi2
  }
  let fa : CanonicalFormulaArgs ctx := {
    queryOfAtom := queryOfAtom
    φf := φf
    hφ := hφ
    Xobj := Xobj
    Xgr := Xgr
  }
  let goal : CanonicalGoalArgs ctx cat fa := {
    p := p
    q := q
    hstar := hstar
    φcat := φcat
    hStrengthFromEvidence := hStrengthFromEvidence
  }
  let transportGoal : CanonicalTransportGoalArgs ctx modal cat fa := {
    hφTop := hφTop
    χ := χ
    ψ := ψ
    goal := goal
  }
  simpa [modal, cat, fa, goal, transportGoal] using
    canonical_rulePack_transport_piSigma_and_fixpoint_of_transportGoal
      (ctx := ctx) (modal := modal) (cat := cat) (fa := fa)
      (hPiSigmaPack := Mettapedia.OSLF.NativeType.prop12_piSigmaPredicateRulePack
        (C := ConstructorObj ctx.lang))
      (transportGoal := transportGoal)

end Mettapedia.OSLF.Framework.OSLFNTTWMCanonicalClosure
