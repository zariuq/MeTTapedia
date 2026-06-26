import Mettapedia.Languages.MeTTa.PureKernel.Confluence
import Mettapedia.Languages.MeTTa.PureKernel.Parallel
import Mettapedia.Languages.MeTTa.PureKernel.Typing

namespace Mettapedia.Languages.MeTTa.PureKernel

open Syntax
open Renaming
open Context
open Substitution
open Reduction
open Confluence
open Parallel
open Typing

theorem inst0_rename_wk_cancel (a t : PureTm n) :
    inst0 a (rename wk t) = t := by
  calc
    inst0 a (rename wk t)
        = subst (subst0 a) (rename wk t) := by
            rfl
    _ = subst (fun i => subst0 a (wk i)) t := by
          simpa using (subst_rename (σ := subst0 a) (ρ := wk) (t := t))
    _ = subst ids t := by
          apply subst_ext
          intro i
          rfl
    _ = t := by
          exact subst_ids (t := t)

theorem conv_to_cdev (t : PureTm n) : Conv t (cdev t) :=
  redStar_implies_conv (par_to_redStar (par_to_cdev_self t))

theorem conv_of_cdev_eq {A B : PureTm n} (h : cdev A = cdev B) :
    Conv A B := by
  have hA : Conv A (cdev A) := conv_to_cdev A
  have hB : Conv B (cdev B) := conv_to_cdev B
  exact Relation.EqvGen.trans _ _ _ hA
    (Relation.EqvGen.symm _ _ (by simpa [h] using hB))

structure DefEqWitness (A B : PureTm n) : Type where
  conv : Conv A B

def defEqByNormalization? (A B : PureTm n) : Option (DefEqWitness A B) :=
  if h : cdev A = cdev B then
    some ⟨conv_of_cdev_eq h⟩
  else
    none

private def cdevIncompleteCtx : Ctx 1 :=
  .snoc .nil .u0

private def cdevIncompleteLeft : PureTm 1 :=
  .app (.fst (.pair (.lam (.var 0)) (.var 0))) (.var 0)

private def cdevIncompleteRight : PureTm 1 :=
  .var 0

private def cdevIncompleteId : PureTm 1 :=
  .lam (.var 0)

private def cdevIncompleteIdTy : PureTm 1 :=
  .pi (.u0 : PureTm 1) (.u0 : PureTm 2)

private theorem cdevIncompleteRight_typed :
    HasType cdevIncompleteCtx cdevIncompleteRight .u0 := by
  simpa [cdevIncompleteCtx, cdevIncompleteRight, Context.lookup_snoc_zero, Renaming.rename] using
    (HasType.var (Γ := cdevIncompleteCtx) (i := (0 : Fin 1)))

private theorem cdevIncompleteId_typed :
    HasType cdevIncompleteCtx cdevIncompleteId cdevIncompleteIdTy := by
  apply HasType.lam_intro
  simpa [cdevIncompleteCtx, cdevIncompleteId, cdevIncompleteIdTy,
    Context.lookup_snoc_zero, Renaming.rename] using
    (HasType.var (Γ := .snoc cdevIncompleteCtx .u0) (i := (0 : Fin 2)))

private theorem cdevIncompleteLeft_typed :
    HasType cdevIncompleteCtx cdevIncompleteLeft .u0 := by
  have hpair : HasType cdevIncompleteCtx
      (.pair cdevIncompleteId cdevIncompleteRight)
      (.sigma cdevIncompleteIdTy (.u0 : PureTm 2)) := by
    simpa [cdevIncompleteIdTy, cdevIncompleteRight, inst0] using
      (HasType.pair_intro
        (A := cdevIncompleteIdTy)
        (B := (.u0 : PureTm 2))
        cdevIncompleteId_typed
        cdevIncompleteRight_typed)
  have hfst : HasType cdevIncompleteCtx
      (.fst (.pair cdevIncompleteId cdevIncompleteRight))
      cdevIncompleteIdTy := by
    apply HasType.fst_elim
    exact hpair
  simpa [cdevIncompleteLeft, cdevIncompleteId, cdevIncompleteIdTy,
    cdevIncompleteRight, inst0, subst] using
    (HasType.app_elim
      (Γ := cdevIncompleteCtx)
      (f := .fst (.pair cdevIncompleteId cdevIncompleteRight))
      (a := cdevIncompleteRight)
      (A := (.u0 : PureTm 1))
      (B := (.u0 : PureTm 2))
      hfst
      cdevIncompleteRight_typed)

private theorem cdevIncomplete_conv :
    Conv cdevIncompleteLeft cdevIncompleteRight := by
  refine Relation.EqvGen.trans _ _ _
    (red_implies_conv (.congAppFun (.betaSigmaFst cdevIncompleteId (.var 0))))
    ?_
  exact red_implies_conv (.betaPi (.var 0) (.var 0))

@[simp] private theorem cdev_cdevIncompleteLeft :
    cdev cdevIncompleteLeft = .app (.lam (.var 0)) (.var 0) := rfl

@[simp] private theorem cdev_cdevIncompleteRight :
    cdev cdevIncompleteRight = .var 0 := rfl

theorem defEqByNormalization_not_complete :
    ∃ (Γ : Ctx 1) (t u A : PureTm 1),
      HasType Γ t A ∧
      HasType Γ u A ∧
      Conv t u ∧
      defEqByNormalization? t u = none := by
  refine ⟨cdevIncompleteCtx, cdevIncompleteLeft, cdevIncompleteRight, (.u0 : PureTm 1), ?_, ?_, ?_, ?_⟩
  · exact cdevIncompleteLeft_typed
  · exact cdevIncompleteRight_typed
  · exact cdevIncomplete_conv
  · simp [defEqByNormalization?, cdevIncompleteLeft, cdevIncompleteRight, cdev]

structure PiView (t : PureTm n) : Type where
  dom : PureTm n
  cod : PureTm (n + 1)
  conv : Conv t (.pi dom cod)

structure SigmaView (t : PureTm n) : Type where
  dom : PureTm n
  cod : PureTm (n + 1)
  conv : Conv t (.sigma dom cod)

def asPi? (t : PureTm n) : Option (PiView t) :=
  match hnorm : cdev t with
  | .pi A B =>
      some
        { dom := A
          cod := B
          conv := by
            simpa [hnorm] using conv_to_cdev t }
  | _ => none

def asSigma? (t : PureTm n) : Option (SigmaView t) :=
  match hnorm : cdev t with
  | .sigma A B =>
      some
        { dom := A
          cod := B
          conv := by
            simpa [hnorm] using conv_to_cdev t }
  | _ => none

private def cdevIncompletePiCtx : Ctx 1 :=
  .snoc .nil .u0

private def cdevIncompletePiWitness : PureTm 1 :=
  .var 0

private def cdevIncompletePiRight : PureTm 1 :=
  .pi (.u0 : PureTm 1) (.u0 : PureTm 2)

private def cdevIncompletePiBody : PureTm 2 :=
  rename wk cdevIncompletePiRight

private def cdevIncompletePiFun : PureTm 1 :=
  .lam cdevIncompletePiBody

private def cdevIncompletePiLeft : PureTm 1 :=
  .app (.fst (.pair cdevIncompletePiFun cdevIncompletePiWitness)) cdevIncompletePiWitness

private theorem cdevIncompletePiWitness_typed :
    HasType cdevIncompletePiCtx cdevIncompletePiWitness .u0 := by
  simpa [cdevIncompletePiCtx, cdevIncompletePiWitness, Context.lookup_snoc_zero, Renaming.rename] using
    (HasType.var (Γ := cdevIncompletePiCtx) (i := (0 : Fin 1)))

private theorem cdevIncompletePiRight_typed :
    HasType cdevIncompletePiCtx cdevIncompletePiRight .u1 := by
  apply HasType.pi_form
  · exact HasType.u0_type cdevIncompletePiCtx
  · exact HasType.u0_type (.snoc cdevIncompletePiCtx (.u0 : PureTm 1))

private theorem cdevIncompletePiFun_typed :
    HasType cdevIncompletePiCtx cdevIncompletePiFun (.pi (.u0 : PureTm 1) (.u1 : PureTm 2)) := by
  apply HasType.lam_intro
  simpa [cdevIncompletePiFun, cdevIncompletePiBody, cdevIncompletePiRight, Renaming.rename] using
    (weakening (Γ := cdevIncompletePiCtx) (U := (.u0 : PureTm 1))
      (ht := cdevIncompletePiRight_typed))

private theorem cdevIncompletePiLeft_typed :
    HasType cdevIncompletePiCtx cdevIncompletePiLeft .u1 := by
  have hpair : HasType cdevIncompletePiCtx
      (.pair cdevIncompletePiFun cdevIncompletePiWitness)
      (.sigma (.pi (.u0 : PureTm 1) (.u1 : PureTm 2)) (.u0 : PureTm 2)) := by
    simpa [cdevIncompletePiWitness, inst0] using
      (HasType.pair_intro
        (A := (.pi (.u0 : PureTm 1) (.u1 : PureTm 2)))
        (B := (.u0 : PureTm 2))
        cdevIncompletePiFun_typed
        cdevIncompletePiWitness_typed)
  have hfst : HasType cdevIncompletePiCtx
      (.fst (.pair cdevIncompletePiFun cdevIncompletePiWitness))
      (.pi (.u0 : PureTm 1) (.u1 : PureTm 2)) := by
    exact HasType.fst_elim hpair
  simpa [cdevIncompletePiLeft, cdevIncompletePiWitness, inst0, subst] using
    (HasType.app_elim
      (Γ := cdevIncompletePiCtx)
      (f := .fst (.pair cdevIncompletePiFun cdevIncompletePiWitness))
      (a := cdevIncompletePiWitness)
      (A := (.u0 : PureTm 1))
      (B := (.u1 : PureTm 2))
      hfst
      cdevIncompletePiWitness_typed)

private theorem cdevIncompletePi_conv :
    Conv cdevIncompletePiLeft cdevIncompletePiRight := by
  refine Relation.EqvGen.trans _ _ _
    (red_implies_conv (.congAppFun (.betaSigmaFst cdevIncompletePiFun cdevIncompletePiWitness)))
    ?_
  exact red_implies_conv (.betaPi cdevIncompletePiBody cdevIncompletePiWitness)

@[simp] private theorem cdev_cdevIncompletePiLeft :
    cdev cdevIncompletePiLeft = .app (.lam cdevIncompletePiBody) cdevIncompletePiWitness := rfl

theorem asPi_not_complete :
    ∃ (Γ : Ctx 1) (t A : PureTm 1) (B : PureTm 2),
      HasType Γ t .u1 ∧
      Conv t (.pi A B) ∧
      asPi? t = none := by
  refine ⟨cdevIncompletePiCtx, cdevIncompletePiLeft, (.u0 : PureTm 1), (.u0 : PureTm 2), ?_, ?_, ?_⟩
  · exact cdevIncompletePiLeft_typed
  · simpa [cdevIncompletePiRight] using cdevIncompletePi_conv
  · simp [asPi?, cdevIncompletePiLeft, cdev]

end Mettapedia.Languages.MeTTa.PureKernel
