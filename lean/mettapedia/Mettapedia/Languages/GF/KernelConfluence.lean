import Mettapedia.OSLF.MeTTaIL.Syntax
import Mathlib.Logic.Relation

/-!
# GF Compact Rewrite Kernel: Termination and Confluence Skeleton

This module isolates the compact identity-wrapper rewrite kernel used in the
GF→OSLF bridge (`UseN`, `PositA`, `UseV`, `UseComp`, `UseN2`, `UseA2`) and
proves:

1. **Termination** via a decreasing wrapper-count measure
2. **Normalization invariance** (one-step and multi-step)
3. **Confluence modulo normalization**

Design choice:
- The step relation is context-closed over `.apply` argument positions, which
  matches the first-order `AbstractNode → Pattern` fragment emitted by
  `gfAbstractToPattern`.
- This provides a reusable base that can be extended to richer contexts
  (lambda/subst/collection) without changing the proof architecture.
-/

namespace Mettapedia.Languages.GF.KernelConfluence

open Mettapedia.OSLF.MeTTaIL.Syntax

/-- Wrapper constructors that are semantically identity in the compact kernel. -/
def isKernelWrapperName : String → Bool
  | "UseN" => true
  | "PositA" => true
  | "UseV" => true
  | "UseComp" => true
  | "UseN2" => true
  | "UseA2" => true
  | _ => false

@[simp] theorem isKernelWrapperName_UseN : isKernelWrapperName "UseN" = true := rfl
@[simp] theorem isKernelWrapperName_PositA : isKernelWrapperName "PositA" = true := rfl
@[simp] theorem isKernelWrapperName_UseV : isKernelWrapperName "UseV" = true := rfl
@[simp] theorem isKernelWrapperName_UseComp : isKernelWrapperName "UseComp" = true := rfl
@[simp] theorem isKernelWrapperName_UseN2 : isKernelWrapperName "UseN2" = true := rfl
@[simp] theorem isKernelWrapperName_UseA2 : isKernelWrapperName "UseA2" = true := rfl

/-- One-step compact-kernel rewrite, closed under `.apply` argument contexts. -/
inductive KernelStep : Pattern → Pattern → Prop where
  | useN (p : Pattern) : KernelStep (.apply "UseN" [p]) p
  | positA (p : Pattern) : KernelStep (.apply "PositA" [p]) p
  | useV (p : Pattern) : KernelStep (.apply "UseV" [p]) p
  | useComp (p : Pattern) : KernelStep (.apply "UseComp" [p]) p
  | useN2 (p : Pattern) : KernelStep (.apply "UseN2" [p]) p
  | useA2 (p : Pattern) : KernelStep (.apply "UseA2" [p]) p
  | appCtx {f : String} {pre post : List Pattern} {p q : Pattern} :
      KernelStep p q →
      KernelStep (.apply f (pre ++ p :: post)) (.apply f (pre ++ q :: post))

mutual

/-- Total number of kernel wrappers in a pattern. -/
def wrapperCount : Pattern → Nat
  | .fvar _ => 0
  | .bvar _ => 0
  | .apply f args =>
      (if isKernelWrapperName f && args.length = 1 then 1 else 0) + wrapperCountList args
  | .lambda body => wrapperCount body
  | .multiLambda _ body => wrapperCount body
  | .subst a b => wrapperCount a + wrapperCount b
  | .collection _ elems _ => wrapperCountList elems

/-- Total number of kernel wrappers in a list of patterns. -/
def wrapperCountList : List Pattern → Nat
  | [] => 0
  | p :: ps => wrapperCount p + wrapperCountList ps

end

attribute [simp] wrapperCountList wrapperCount

theorem wrapperCountList_append (xs ys : List Pattern) :
    wrapperCountList (xs ++ ys) = wrapperCountList xs + wrapperCountList ys := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      simp [ih, Nat.add_left_comm, Nat.add_comm]

theorem wrapperCountList_pre_post_lt {pre post : List Pattern} {p q : Pattern}
    (h : wrapperCount q < wrapperCount p) :
    wrapperCountList (pre ++ q :: post) < wrapperCountList (pre ++ p :: post) := by
  simp [wrapperCountList_append, Nat.add_left_comm, h]

/-- Each kernel step strictly decreases wrapper count. -/
theorem wrapperCount_decreases {p q : Pattern} (hstep : KernelStep p q) :
    wrapperCount q < wrapperCount p := by
  induction hstep with
  | useN p =>
      simp [wrapperCount]
  | positA p =>
      simp [wrapperCount]
  | useV p =>
      simp [wrapperCount]
  | useComp p =>
      simp [wrapperCount]
  | useN2 p =>
      simp [wrapperCount]
  | useA2 p =>
      simp [wrapperCount]
  | @appCtx f pre post p q hstep ih =>
      have hargs :
          wrapperCountList (pre ++ q :: post) <
          wrapperCountList (pre ++ p :: post) :=
        wrapperCountList_pre_post_lt ih
      have hlen : (pre ++ q :: post).length = (pre ++ p :: post).length := by simp
      have hhead :
          (if isKernelWrapperName f && (pre ++ q :: post).length = 1 then 1 else 0) =
          (if isKernelWrapperName f && (pre ++ p :: post).length = 1 then 1 else 0) := by
        simp [hlen]
      rw [wrapperCount, wrapperCount, hhead]
      exact Nat.add_lt_add_left hargs _

/-- No one-step kernel cycle is possible (strictly decreasing measure). -/
theorem kernelStep_irrefl (p : Pattern) : ¬ KernelStep p p := by
  intro hstep
  exact (Nat.lt_irrefl (wrapperCount p)) (wrapperCount_decreases hstep)

/-- Normalization by recursively erasing identity wrappers in the compact kernel. -/
def normalizeKernel : Pattern → Pattern
  | .fvar x => .fvar x
  | .bvar i => .bvar i
  | .apply f args =>
      let args' := args.map normalizeKernel
      match args' with
      | [p] => if isKernelWrapperName f then p else .apply f [p]
      | _ => .apply f args'
  | .lambda body => .lambda (normalizeKernel body)
  | .multiLambda names body => .multiLambda names (normalizeKernel body)
  | .subst a b => .subst (normalizeKernel a) (normalizeKernel b)
  | .collection k elems a => .collection k (elems.map normalizeKernel) a

theorem normalizeKernel_invariant_step {p q : Pattern} (hstep : KernelStep p q) :
    normalizeKernel p = normalizeKernel q := by
  induction hstep with
  | useN p =>
      simp [normalizeKernel]
  | positA p =>
      simp [normalizeKernel]
  | useV p =>
      simp [normalizeKernel]
  | useComp p =>
      simp [normalizeKernel]
  | useN2 p =>
      simp [normalizeKernel]
  | useA2 p =>
      simp [normalizeKernel]
  | @appCtx f pre post p q hstep ih =>
      simp [normalizeKernel, List.map_append, ih]

/-- Normalization is invariant along any finite kernel reduction path. -/
theorem normalizeKernel_invariant_rtg {p q : Pattern}
    (h : Relation.ReflTransGen KernelStep p q) :
    normalizeKernel p = normalizeKernel q := by
  induction h with
  | refl => rfl
  | tail hrest hstep ih =>
      exact ih.trans (normalizeKernel_invariant_step hstep)

/-- Local confluence modulo normalization:
    two one-step reducts share the same kernel normal form. -/
theorem kernel_local_confluence_mod {p q₁ q₂ : Pattern}
    (h₁ : KernelStep p q₁) (h₂ : KernelStep p q₂) :
    normalizeKernel q₁ = normalizeKernel q₂ := by
  calc
    normalizeKernel q₁ = normalizeKernel p := (normalizeKernel_invariant_step h₁).symm
    _ = normalizeKernel q₂ := normalizeKernel_invariant_step h₂

/-- Global confluence modulo normalization for the compact kernel. -/
theorem kernel_confluence_mod {p q₁ q₂ : Pattern}
    (h₁ : Relation.ReflTransGen KernelStep p q₁)
    (h₂ : Relation.ReflTransGen KernelStep p q₂) :
    normalizeKernel q₁ = normalizeKernel q₂ := by
  calc
    normalizeKernel q₁ = normalizeKernel p := (normalizeKernel_invariant_rtg h₁).symm
    _ = normalizeKernel q₂ := normalizeKernel_invariant_rtg h₂

end Mettapedia.Languages.GF.KernelConfluence
