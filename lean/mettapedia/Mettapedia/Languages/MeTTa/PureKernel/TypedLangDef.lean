import Mettapedia.Languages.MeTTa.PureKernel.SubjectReduction

namespace Mettapedia.Languages.MeTTa.PureKernel.Assembly

open Mettapedia.Languages.MeTTa.PureKernel.Syntax
open Mettapedia.Languages.MeTTa.PureKernel.Context
open Mettapedia.Languages.MeTTa.PureKernel.Reduction
open Mettapedia.Languages.MeTTa.PureKernel.Typing
open Mettapedia.Languages.MeTTa.PureKernel.SubjectReduction

/-- Kernel-level typed language bundle over scoped terms (`PureTm`). -/
structure TypedKernelDef where
  hasType : ∀ {n}, Ctx n → PureTm n → PureTm n → Prop
  reduces : ∀ {n}, PureTm n → PureTm n → Prop
  subject_reduction :
    ∀ {n} {Γ : Ctx n} {t t' A : PureTm n},
      hasType Γ t A → reduces t t' → hasType Γ t' A

/-- MeTTa-Pure kernel packaged as a typed language definition. -/
def mettaPureKernelTyped : TypedKernelDef where
  hasType := @HasType
  reduces := @Red
  subject_reduction := by
    intro n Γ t t' A ht hr
    exact subject_reduction (Γ := Γ) (t := t) (t' := t') (A := A) ht hr

theorem mettaPureKernel_subject_reduction
    {n : Nat} {Γ : Ctx n} {t t' A : PureTm n}
    (ht : mettaPureKernelTyped.hasType Γ t A)
    (hr : mettaPureKernelTyped.reduces t t') :
    mettaPureKernelTyped.hasType Γ t' A :=
  mettaPureKernelTyped.subject_reduction ht hr

end Mettapedia.Languages.MeTTa.PureKernel.Assembly
