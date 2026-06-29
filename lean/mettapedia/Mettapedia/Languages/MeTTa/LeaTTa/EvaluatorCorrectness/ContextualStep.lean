import MettaHyperonFull.Proofs.Correspondence

/-!
# Contextual closures of LeaTTa's certified step relations

LeaTTa proves the root-step correspondence `KernelStep ↔ MopsStep`.  Verified MeTTa
programs often need the same correspondence below expression contexts, because the
fuelled evaluator continues inside constructor results.  This module packages that
contextual closure once, without claiming full `mettaEval` scheduler correctness.
-/

namespace Mettapedia.Languages.MeTTa.LeaTTa.EvaluatorCorrectness.ContextualStep

open Metta

mutual

/-- Contextual closure of a MOPS rule step under expression positions. -/
inductive ExprCtxMopsStep (rules : List Atom) : Atom → Atom → Prop
  | root {a b : Atom} :
      MopsStep rules a b → ExprCtxMopsStep rules a b
  | expr {xs ys : List Atom} :
      ExprListCtxMopsStep rules xs ys → ExprCtxMopsStep rules (Atom.expr xs) (Atom.expr ys)

/-- Contextual closure of a MOPS rule step inside an expression argument list. -/
inductive ExprListCtxMopsStep (rules : List Atom) : List Atom → List Atom → Prop
  | head {x y : Atom} {xs : List Atom} :
      ExprCtxMopsStep rules x y → ExprListCtxMopsStep rules (x :: xs) (y :: xs)
  | tail {x : Atom} {xs ys : List Atom} :
      ExprListCtxMopsStep rules xs ys → ExprListCtxMopsStep rules (x :: xs) (x :: ys)

end

mutual

/-- Contextual closure of LeaTTa's executable-kernel root relation. -/
inductive ExprCtxKernelStep
    (rules : List Atom) (gt : GroundingTable) : Atom → Atom → Prop
  | root {a b : Atom} :
      KernelStep rules gt a b → ExprCtxKernelStep rules gt a b
  | expr {xs ys : List Atom} :
      ExprListCtxKernelStep rules gt xs ys → ExprCtxKernelStep rules gt (Atom.expr xs)
        (Atom.expr ys)

/-- Contextual closure of LeaTTa's executable-kernel relation inside an expression list. -/
inductive ExprListCtxKernelStep
    (rules : List Atom) (gt : GroundingTable) : List Atom → List Atom → Prop
  | head {x y : Atom} {xs : List Atom} :
      ExprCtxKernelStep rules gt x y → ExprListCtxKernelStep rules gt (x :: xs) (y :: xs)
  | tail {x : Atom} {xs ys : List Atom} :
      ExprListCtxKernelStep rules gt xs ys → ExprListCtxKernelStep rules gt (x :: xs) (x :: ys)

end

mutual

/-- LeaTTa's certified `KernelStep ↔ MopsStep` correspondence, lifted through one
contextual atom step, from the MOPS side to the kernel side. -/
theorem exprCtxMopsStep_to_kernel {rules : List Atom} {gt : GroundingTable}
    {a b : Atom}
    (h : ExprCtxMopsStep rules a b) : ExprCtxKernelStep rules gt a b := by
  cases h with
  | root hroot => exact ExprCtxKernelStep.root (kernelStep_iff_mopsStep.mpr hroot)
  | expr hlist => exact ExprCtxKernelStep.expr (exprListMopsStep_to_kernel hlist)

/-- LeaTTa's certified `KernelStep ↔ MopsStep` correspondence, lifted through one
contextual list step, from the MOPS side to the kernel side. -/
theorem exprListMopsStep_to_kernel {rules : List Atom} {gt : GroundingTable}
    {xs ys : List Atom}
    (h : ExprListCtxMopsStep rules xs ys) : ExprListCtxKernelStep rules gt xs ys := by
  cases h with
  | head hhead => exact ExprListCtxKernelStep.head (exprCtxMopsStep_to_kernel hhead)
  | tail htail => exact ExprListCtxKernelStep.tail (exprListMopsStep_to_kernel htail)

end

mutual

/-- LeaTTa's certified `KernelStep ↔ MopsStep` correspondence, lifted through one
contextual atom step, from the kernel side back to MOPS. -/
theorem exprCtxKernelStep_to_mops {rules : List Atom} {gt : GroundingTable}
    {a b : Atom}
    (h : ExprCtxKernelStep rules gt a b) : ExprCtxMopsStep rules a b := by
  cases h with
  | root hroot => exact ExprCtxMopsStep.root (kernelStep_iff_mopsStep.mp hroot)
  | expr hlist => exact ExprCtxMopsStep.expr (exprListKernelStep_to_mops hlist)

/-- LeaTTa's certified `KernelStep ↔ MopsStep` correspondence, lifted through one
contextual list step, from the kernel side back to MOPS. -/
theorem exprListKernelStep_to_mops {rules : List Atom} {gt : GroundingTable}
    {xs ys : List Atom}
    (h : ExprListCtxKernelStep rules gt xs ys) : ExprListCtxMopsStep rules xs ys := by
  cases h with
  | head hhead => exact ExprListCtxMopsStep.head (exprCtxKernelStep_to_mops hhead)
  | tail htail => exact ExprListCtxMopsStep.tail (exprListKernelStep_to_mops htail)

end

/-- Contextual kernel and MOPS one-step relations are equivalent. -/
theorem exprCtxKernelStep_iff_mopsStep {rules : List Atom} {gt : GroundingTable}
    {a b : Atom} :
    ExprCtxKernelStep rules gt a b ↔ ExprCtxMopsStep rules a b :=
  ⟨exprCtxKernelStep_to_mops, exprCtxMopsStep_to_kernel⟩

/-- LeaTTa's certified `KernelStep ↔ MopsStep` correspondence, lifted through contextual
reflexive-transitive chains, from the MOPS side to the kernel side. -/
theorem exprCtxMopsChain_to_kernel {rules : List Atom} {gt : GroundingTable}
    {a b : Atom}
    (h : Relation.ReflTransGen (ExprCtxMopsStep rules) a b) :
    Relation.ReflTransGen (ExprCtxKernelStep rules gt) a b := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ step ih => exact Relation.ReflTransGen.tail ih (exprCtxMopsStep_to_kernel step)

/-- LeaTTa's certified `KernelStep ↔ MopsStep` correspondence, lifted through contextual
reflexive-transitive chains, from the kernel side back to MOPS. -/
theorem exprCtxKernelChain_to_mops {rules : List Atom} {gt : GroundingTable}
    {a b : Atom}
    (h : Relation.ReflTransGen (ExprCtxKernelStep rules gt) a b) :
    Relation.ReflTransGen (ExprCtxMopsStep rules) a b := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ step ih => exact Relation.ReflTransGen.tail ih (exprCtxKernelStep_to_mops step)

/-- Contextual kernel and MOPS reachability are equivalent. -/
theorem exprCtxKernelChain_iff_mops {rules : List Atom} {gt : GroundingTable}
    {a b : Atom} :
    Relation.ReflTransGen (ExprCtxKernelStep rules gt) a b ↔
      Relation.ReflTransGen (ExprCtxMopsStep rules) a b :=
  ⟨exprCtxKernelChain_to_mops, exprCtxMopsChain_to_kernel⟩

/-- A root MOPS reachability chain is, in particular, a contextual MOPS chain. -/
theorem mopsChain_to_exprCtxMopsChain {rules : List Atom} {a b : Atom}
    (h : Relation.ReflTransGen (MopsStep rules) a b) :
    Relation.ReflTransGen (ExprCtxMopsStep rules) a b := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ step ih => exact Relation.ReflTransGen.tail ih (ExprCtxMopsStep.root step)

/-- A root `KernelStep` reachability chain is, in particular, a contextual kernel chain. -/
theorem kernelChain_to_exprCtxKernelChain {rules : List Atom} {gt : GroundingTable} {a b : Atom}
    (h : Relation.ReflTransGen (KernelStep rules gt) a b) :
    Relation.ReflTransGen (ExprCtxKernelStep rules gt) a b := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ step ih => exact Relation.ReflTransGen.tail ih (ExprCtxKernelStep.root step)

/-- Lift a contextual atom chain into the head position of an expression list. -/
theorem exprListMopsChain_head {rules : List Atom} {x y : Atom}
    {xs : List Atom}
    (h : Relation.ReflTransGen (ExprCtxMopsStep rules) x y) :
    Relation.ReflTransGen (ExprListCtxMopsStep rules) (x :: xs) (y :: xs) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ step ih => exact Relation.ReflTransGen.tail ih (ExprListCtxMopsStep.head step)

/-- Lift a contextual list chain below an unchanged list head. -/
theorem exprListMopsChain_tail {rules : List Atom} {x : Atom}
    {xs ys : List Atom}
    (h : Relation.ReflTransGen (ExprListCtxMopsStep rules) xs ys) :
    Relation.ReflTransGen (ExprListCtxMopsStep rules) (x :: xs) (x :: ys) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ step ih => exact Relation.ReflTransGen.tail ih (ExprListCtxMopsStep.tail step)

/-- Lift a contextual list chain to the enclosing expression. -/
theorem exprCtxMopsChain_expr {rules : List Atom} {xs ys : List Atom}
    (h : Relation.ReflTransGen (ExprListCtxMopsStep rules) xs ys) :
    Relation.ReflTransGen (ExprCtxMopsStep rules) (Atom.expr xs) (Atom.expr ys) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ step ih => exact Relation.ReflTransGen.tail ih (ExprCtxMopsStep.expr step)

/-- Lift a contextual kernel atom chain into the head position of an expression list. -/
theorem exprListKernelChain_head {rules : List Atom} {gt : GroundingTable} {x y : Atom}
    {xs : List Atom}
    (h : Relation.ReflTransGen (ExprCtxKernelStep rules gt) x y) :
    Relation.ReflTransGen (ExprListCtxKernelStep rules gt) (x :: xs) (y :: xs) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ step ih => exact Relation.ReflTransGen.tail ih (ExprListCtxKernelStep.head step)

/-- Lift a contextual kernel list chain below an unchanged list head. -/
theorem exprListKernelChain_tail {rules : List Atom} {gt : GroundingTable} {x : Atom}
    {xs ys : List Atom}
    (h : Relation.ReflTransGen (ExprListCtxKernelStep rules gt) xs ys) :
    Relation.ReflTransGen (ExprListCtxKernelStep rules gt) (x :: xs) (x :: ys) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ step ih => exact Relation.ReflTransGen.tail ih (ExprListCtxKernelStep.tail step)

/-- Lift a contextual kernel list chain to the enclosing expression. -/
theorem exprCtxKernelChain_expr {rules : List Atom} {gt : GroundingTable} {xs ys : List Atom}
    (h : Relation.ReflTransGen (ExprListCtxKernelStep rules gt) xs ys) :
    Relation.ReflTransGen (ExprCtxKernelStep rules gt) (Atom.expr xs) (Atom.expr ys) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ step ih => exact Relation.ReflTransGen.tail ih (ExprCtxKernelStep.expr step)

/-- Lift a contextual MOPS atom chain into an arbitrary expression-list position. -/
theorem exprListMopsChain_at {rules : List Atom} {x y : Atom}
    (pre post : List Atom)
    (h : Relation.ReflTransGen (ExprCtxMopsStep rules) x y) :
    Relation.ReflTransGen (ExprListCtxMopsStep rules) (pre ++ x :: post) (pre ++ y :: post) := by
  induction pre with
  | nil =>
      simpa using exprListMopsChain_head (xs := post) h
  | cons z pre ih =>
      simpa using exprListMopsChain_tail (x := z) ih

/-- Lift a contextual MOPS atom chain into an arbitrary expression position. -/
theorem exprCtxMopsChain_at {rules : List Atom} {x y : Atom}
    (pre post : List Atom)
    (h : Relation.ReflTransGen (ExprCtxMopsStep rules) x y) :
    Relation.ReflTransGen (ExprCtxMopsStep rules)
      (Atom.expr (pre ++ x :: post)) (Atom.expr (pre ++ y :: post)) :=
  exprCtxMopsChain_expr (exprListMopsChain_at pre post h)

/-- Lift a contextual kernel atom chain into an arbitrary expression-list position. -/
theorem exprListKernelChain_at {rules : List Atom} {gt : GroundingTable} {x y : Atom}
    (pre post : List Atom)
    (h : Relation.ReflTransGen (ExprCtxKernelStep rules gt) x y) :
    Relation.ReflTransGen (ExprListCtxKernelStep rules gt) (pre ++ x :: post) (pre ++ y :: post) := by
  induction pre with
  | nil =>
      simpa using exprListKernelChain_head (xs := post) h
  | cons z pre ih =>
      simpa using exprListKernelChain_tail (x := z) ih

/-- Lift a contextual kernel atom chain into an arbitrary expression position. -/
theorem exprCtxKernelChain_at {rules : List Atom} {gt : GroundingTable} {x y : Atom}
    (pre post : List Atom)
    (h : Relation.ReflTransGen (ExprCtxKernelStep rules gt) x y) :
    Relation.ReflTransGen (ExprCtxKernelStep rules gt)
      (Atom.expr (pre ++ x :: post)) (Atom.expr (pre ++ y :: post)) :=
  exprCtxKernelChain_expr (exprListKernelChain_at pre post h)

end Mettapedia.Languages.MeTTa.LeaTTa.EvaluatorCorrectness.ContextualStep
