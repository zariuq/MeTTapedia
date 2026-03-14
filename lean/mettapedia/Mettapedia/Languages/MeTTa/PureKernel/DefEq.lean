import Mettapedia.Languages.MeTTa.PureKernel.Confluence
import Mettapedia.Languages.MeTTa.PureKernel.Parallel
import Mettapedia.Languages.MeTTa.PureKernel.Typing

namespace Mettapedia.Languages.MeTTa.PureKernel

open Syntax
open Renaming
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

end Mettapedia.Languages.MeTTa.PureKernel
