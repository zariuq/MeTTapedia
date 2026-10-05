import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.ActiveMarkingLabels
import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.ScopedOpening

/-!
# Coupled marks along a supplied static derivation

An independent binder marker can be threaded through a supplied labeled
derivation while retaining all of that derivation's prefix labels. New unused
scopes receive an unselected marker; copied servers retain the markers of
their actual surviving copy.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.ActiveMarkingPairs

open Mettapedia.OSLF.Binding
open Mettapedia.Languages.ProcessCalculi.PolyadicPi
open Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges
open ActiveMarking ActiveMarkingLabels

universe u

theorem lift_pair {Label : Type u} {Γ : Ctx sig}
    {before after : ActiveMarking.Tree Label} {source target : Proc Γ}
    (tracked : Transport before source after target)
    (paired : ActiveMarking.Tree (Bool × Label)) (fits : Fits paired source)
    (projection : labels Prod.snd paired = before) :
    ∃ next : ActiveMarking.Tree (Bool × Label),
      labels Prod.snd next = after ∧ Transport paired source next target := by
  induction tracked generalizing paired with
  | refl => exact ⟨paired, projection, .refl _ _⟩
  | trans left right leftIH rightIH =>
      obtain ⟨middle, firstProjection, first⟩ := leftIH paired fits projection
      have middleFits := fits_of_labels Prod.fst _
        (ScopedOpening.transport_fits (transport_labels Prod.fst first) (fits_labels Prod.fst fits))
      obtain ⟨next, secondProjection, second⟩ := rightIH middle middleFits firstProjection
      exact ⟨next, secondProjection, first.trans second⟩
  | parComm m n p q =>
      cases fits with
      | @par _ _ _ first second firstFits secondFits =>
          have ⟨left, right⟩ := ActiveMarking.Tree.par.inj projection
          refine ⟨.par second first, ?_, .parComm _ _ _ _⟩
          simp only [labels, left, right]
  | parAssoc m n o p q r =>
      cases fits with
      | @par _ _ _ inside third insideFits thirdFits => cases insideFits with
        | @par _ _ _ first second firstFits secondFits =>
          have ⟨left, last⟩ := ActiveMarking.Tree.par.inj projection
          have ⟨one, two⟩ := ActiveMarking.Tree.par.inj left
          refine ⟨.par first (.par second third), ?_, .parAssoc _ _ _ _ _ _⟩
          simp only [labels, one, two, last]
  | parAssocBack m n o p q r =>
      cases fits with
      | @par _ _ _ first inside firstFits insideFits => cases insideFits with
        | @par _ _ _ second third secondFits thirdFits =>
          have ⟨one, last⟩ := ActiveMarking.Tree.par.inj projection
          have ⟨two, three⟩ := ActiveMarking.Tree.par.inj last
          refine ⟨.par (.par first second) third, ?_, .parAssocBack _ _ _ _ _ _⟩
          simp only [labels, one, two, three]
  | parUnit m p =>
      cases fits with
      | @par _ _ _ first empty firstFits emptyFits =>
          cases emptyFits
          exact ⟨first, (ActiveMarking.Tree.par.inj projection).1, .parUnit _ _⟩
  | parUnitBack m p =>
      refine ⟨.par paired .nil, ?_, .parUnitBack _ _⟩
      simp only [labels, projection]
  | nuUnused origin m p =>
      cases fits with
      | nu binder bodyFits =>
          have ⟨_, bodyProjection⟩ := ActiveMarking.Tree.nu.inj projection
          exact ⟨_, bodyProjection, .nuUnused binder _ _⟩
  | nuUnusedBack origin m p =>
      refine ⟨.nu (false, origin) paired, ?_, .nuUnusedBack _ _ _⟩
      simp only [labels, projection]
  | nuPar origin m n p q =>
      cases fits with
      | @par _ _ _ restrictedMark frame privateFits frameFits => cases privateFits with
        | nu binder bodyFits =>
          have ⟨privateProjection, frameProjection⟩ := ActiveMarking.Tree.par.inj projection
          have ⟨binderProjection, bodyProjection⟩ := ActiveMarking.Tree.nu.inj privateProjection
          refine ⟨.nu binder (.par _ frame), ?_, .nuPar binder _ _ _ _⟩
          simp only [labels, binderProjection, bodyProjection, frameProjection]
  | nuParBack origin m n p q =>
      cases fits with
      | nu binder bodyFits => cases bodyFits with
        | @par _ _ _ restrictedMark frame privateFits frameFits =>
          have ⟨binderProjection, bodyProjection⟩ := ActiveMarking.Tree.nu.inj projection
          have ⟨privateProjection, frameProjection⟩ := ActiveMarking.Tree.par.inj bodyProjection
          refine ⟨.par (.nu binder restrictedMark) frame, ?_, .nuParBack binder _ _ _ _⟩
          simp only [labels, binderProjection, privateProjection, frameProjection]
  | nuSwap outer inner m p =>
      cases fits with
      | nu outside insideFits => cases insideFits with
        | nu inside bodyFits =>
          have ⟨outsideProjection, nested⟩ := ActiveMarking.Tree.nu.inj projection
          have ⟨insideProjection, bodyProjection⟩ := ActiveMarking.Tree.nu.inj nested
          refine ⟨.nu inside (.nu outside _), ?_, .nuSwap outside inside _ _⟩
          simp only [labels, outsideProjection, insideProjection, bodyProjection]
  | nuSwapBack outer inner m p =>
      cases fits with
      | nu inside outsideFits => cases outsideFits with
        | nu outside bodyFits =>
          have ⟨insideProjection, nested⟩ := ActiveMarking.Tree.nu.inj projection
          have ⟨outsideProjection, bodyProjection⟩ := ActiveMarking.Tree.nu.inj nested
          refine ⟨.nu outside (.nu inside _), ?_, .nuSwapBack outside inside _ _⟩
          simp only [labels, outsideProjection, insideProjection, bodyProjection]
  | repUnfold m p =>
      cases fits with
      | @rep _ _ body bodyFits =>
          have bodyProjection := ActiveMarking.Tree.rep.inj projection
          refine ⟨.par body (.rep body), ?_, .repUnfold _ _⟩
          simp only [labels, bodyProjection]
  | repFold copy server p =>
      cases fits with
      | @par _ _ _ copied serving copiedFits servingFits => cases servingFits with
        | @rep _ _ body bodyFits =>
          have ⟨_, servingProjection⟩ := ActiveMarking.Tree.par.inj projection
          have bodyProjection := ActiveMarking.Tree.rep.inj servingProjection
          refine ⟨.rep body, ?_, .repFold copied body _⟩
          simp only [labels, bodyProjection]
  | par left right leftIH rightIH =>
      cases fits with
      | @par _ _ _ first second firstFits secondFits =>
          have ⟨leftProjection, rightProjection⟩ := ActiveMarking.Tree.par.inj projection
          obtain ⟨nextFirst, newLeft, leftTracked⟩ := leftIH first firstFits leftProjection
          obtain ⟨nextSecond, newRight, rightTracked⟩ := rightIH second secondFits rightProjection
          refine ⟨.par nextFirst nextSecond, ?_, .par leftTracked rightTracked⟩
          simp only [labels, newLeft, newRight]
  | nu origin body ih =>
      cases fits with
      | nu binder bodyFits =>
          have ⟨binderProjection, bodyProjection⟩ := ActiveMarking.Tree.nu.inj projection
          obtain ⟨next, nextProjection, nextTracked⟩ := ih _ bodyFits bodyProjection
          refine ⟨.nu binder next, ?_, .nu binder nextTracked⟩
          simp only [labels, binderProjection, nextProjection]
  | inp1 origin channel body ih =>
      cases fits with
      | inp1 binder _ bodyFits =>
          have ⟨binderProjection, bodyProjection⟩ := ActiveMarking.Tree.inp1.inj projection
          obtain ⟨next, nextProjection, nextTracked⟩ := ih _ bodyFits bodyProjection
          refine ⟨.inp1 binder next, ?_, .inp1 binder channel nextTracked⟩
          simp only [labels, binderProjection, nextProjection]
  | inp2 origin channel body ih =>
      cases fits with
      | inp2 binder _ bodyFits =>
          have ⟨binderProjection, bodyProjection⟩ := ActiveMarking.Tree.inp2.inj projection
          obtain ⟨next, nextProjection, nextTracked⟩ := ih _ bodyFits bodyProjection
          refine ⟨.inp2 binder next, ?_, .inp2 binder channel nextTracked⟩
          simp only [labels, binderProjection, nextProjection]
  | rep body ih =>
      cases fits with
      | rep bodyFits =>
          have bodyProjection := ActiveMarking.Tree.rep.inj projection
          obtain ⟨next, nextProjection, nextTracked⟩ := ih _ bodyFits bodyProjection
          refine ⟨.rep next, ?_, .rep nextTracked⟩
          simp only [labels, nextProjection]

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.ActiveMarkingPairs
