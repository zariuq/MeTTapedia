import Mettapedia.Languages.MeTTa.PureKernel.DefEq
import Mettapedia.Languages.MeTTa.PureKernel.PresentationBoundary

/-!
# Decided conversion for the regular Pure kernel

The older algorithmic checker decides conversion through complete development,
but returns the unrestricted authored conversion relation.  This module proves
that the same computation stays inside the declaration-free presentation
fragment and returns `ConstantFreeConv`, the conversion relation used by the
regular kernel.
-/

namespace Mettapedia.Languages.MeTTa.PureKernel.PresentationBoundary

open Mettapedia.Languages.MeTTa.PureKernel.Syntax
open Mettapedia.Languages.MeTTa.PureKernel.Renaming
open Mettapedia.Languages.MeTTa.PureKernel.Substitution
open Mettapedia.Languages.MeTTa.PureKernel.Reduction
open Mettapedia.Languages.MeTTa.PureKernel.Confluence
open Mettapedia.Languages.MeTTa.PureKernel.Parallel

/-- One-step intrinsic reduction cannot introduce a declaration constant. -/
theorem ConstantFree.red {t u : PureTm n} (ht : ConstantFree t) (hred : Red t u) :
    ConstantFree u := by
  induction hred with
  | betaPi body a =>
      cases ht with
      | app hlam ha =>
          cases hlam with
          | lam hbody => exact ha.inst0 hbody
  | betaSigmaFst a b =>
      cases ht with
      | fst hpair =>
          cases hpair with
          | pair ha hb => exact ha
  | betaSigmaSnd a b =>
      cases ht with
      | snd hpair =>
          cases hpair with
          | pair ha hb => exact hb
  | congPiDom hred ih =>
      cases ht with
      | pi hA hB => exact .pi (ih hA) hB
  | congPiCod hred ih =>
      cases ht with
      | pi hA hB => exact .pi hA (ih hB)
  | congSigmaDom hred ih =>
      cases ht with
      | sigma hA hB => exact .sigma (ih hA) hB
  | congSigmaCod hred ih =>
      cases ht with
      | sigma hA hB => exact .sigma hA (ih hB)
  | congIdTy hred ih =>
      cases ht with
      | id hA ha hb => exact .id (ih hA) ha hb
  | congIdLeft hred ih =>
      cases ht with
      | id hA ha hb => exact .id hA (ih ha) hb
  | congIdRight hred ih =>
      cases ht with
      | id hA ha hb => exact .id hA ha (ih hb)
  | congLam hred ih =>
      cases ht with
      | lam hbody => exact .lam (ih hbody)
  | congAppFun hred ih =>
      cases ht with
      | app hf ha => exact .app (ih hf) ha
  | congAppArg hred ih =>
      cases ht with
      | app hf ha => exact .app hf (ih ha)
  | congPairFst hred ih =>
      cases ht with
      | pair ha hb => exact .pair (ih ha) hb
  | congPairSnd hred ih =>
      cases ht with
      | pair ha hb => exact .pair ha (ih hb)
  | congFst hred ih =>
      cases ht with
      | fst hp => exact .fst (ih hp)
  | congSnd hred ih =>
      cases ht with
      | snd hp => exact .snd (ih hp)
  | congRefl hred ih =>
      cases ht with
      | refl ha => exact .refl (ih ha)

/-- A finite reduction path whose source is in the common fragment yields a
fragment-internal conversion proof and keeps its target in the fragment. -/
theorem ConstantFree.redStar {t u : PureTm n} (ht : ConstantFree t)
    (hred : RedStar t u) : ConstantFreeConv t u ∧ ConstantFree u := by
  induction hred with
  | refl => exact ⟨.refl t ht, ht⟩
  | tail hxy hyz ih =>
      have hz := ih.2.red hyz
      exact ⟨.trans ih.1 (.rel ⟨hyz, ih.2, hz⟩), hz⟩

/-- Complete development preserves the exact common syntax. -/
theorem ConstantFree.cdev {t : PureTm n} (ht : ConstantFree t) :
    ConstantFree (cdev t) :=
  (ht.redStar (par_to_redStar (par_to_cdev_self t))).2

/-- Every declaration-free term is fragment-internally convertible to its
computed complete development. -/
theorem constantFreeConv_to_cdev {t : PureTm n} (ht : ConstantFree t) :
    ConstantFreeConv t (cdev t) :=
  (ht.redStar (par_to_redStar (par_to_cdev_self t))).1

/-- Evidence returned by the regular conversion decision. -/
structure RegularDefEqWitness (A B : PureTm n) : Type where
  conv : ConstantFreeConv A B

/-- Sound normalization-based conversion recognition for the regular kernel.
The proof arguments erase at runtime; the computation is exactly comparison of
complete developments.  The negative theorem below shows that this particular
development function is not yet a complete conversion decision. -/
def regularDefEq? (A B : PureTm n) (hA : ConstantFree A) (hB : ConstantFree B) :
    Option (RegularDefEqWitness A B) :=
  if h : cdev A = cdev B then
    some ⟨.trans (constantFreeConv_to_cdev hA)
      (.symm (h ▸ constantFreeConv_to_cdev hB))⟩
  else
    none

/-- A positive computation witness: reflexive universe conversion succeeds. -/
theorem regularDefEq_u0_self :
    (regularDefEq? (.u0 : PureTm 0) .u0 .u0 .u0).isSome = true := by
  rfl

/-- A negative computation witness: the two universe codes do not convert. -/
theorem regularDefEq_u0_u1_rejects :
    regularDefEq? (.u0 : PureTm 0) .u1 .u0 .u1 = none := by
  rfl

/-- A declaration-free conversion whose two-step redex is not fully developed
by the existing `cdev` function in one comparison. -/
def regularDefEqIncompleteLeft : PureTm 1 :=
  .app (.fst (.pair (.lam (.var 0)) (.var 0))) (.var 0)

def regularDefEqIncompleteRight : PureTm 1 :=
  .var 0

theorem regularDefEqIncompleteLeft_constantFree :
    ConstantFree regularDefEqIncompleteLeft := by
  exact .app (.fst (.pair (.lam (.var 0)) (.var 0))) (.var 0)

theorem regularDefEqIncompleteRight_constantFree :
    ConstantFree regularDefEqIncompleteRight :=
  .var 0

theorem regularDefEqIncomplete_fragmentConv :
    ConstantFreeConv regularDefEqIncompleteLeft regularDefEqIncompleteRight := by
  let middle : PureTm 1 := .app (.lam (.var 0)) (.var 0)
  have hmiddle : ConstantFree middle :=
    .app (.lam (.var 0)) (.var 0)
  have hfirst : Red regularDefEqIncompleteLeft middle := by
    exact .congAppFun (.betaSigmaFst (.lam (.var 0)) (.var 0))
  have hsecond : Red middle regularDefEqIncompleteRight := by
    simpa [middle, regularDefEqIncompleteRight, inst0, subst, subst0] using
      (Red.betaPi (.var 0 : PureTm 2) (.var 0 : PureTm 1))
  exact .trans
    (.rel ⟨hfirst, regularDefEqIncompleteLeft_constantFree, hmiddle⟩)
    (.rel ⟨hsecond, hmiddle, regularDefEqIncompleteRight_constantFree⟩)

/-- Negative ablation: the current executable comparison is sound but not
complete for fragment-internal conversion.  A production regular checker must
therefore supply a genuinely complete normalizer before claiming a
`DecidedRelation`. -/
theorem regularDefEq_not_complete :
    regularDefEq?
        regularDefEqIncompleteLeft regularDefEqIncompleteRight
        regularDefEqIncompleteLeft_constantFree
        regularDefEqIncompleteRight_constantFree = none := by
  rfl

end Mettapedia.Languages.MeTTa.PureKernel.PresentationBoundary
