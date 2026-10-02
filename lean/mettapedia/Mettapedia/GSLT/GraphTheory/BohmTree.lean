import Mettapedia.GSLT.GraphTheory.Basic
import Mathlib.Data.List.Basic
import Mathlib.Data.Set.Finite.Basic

/-!
# Böhm Trees

This file defines finite, search-bounded tree observations motivated by Böhm trees
in Bucciarelli-Salibra "Graph Lambda Theories" (2008). It is not yet a
formalization of the source's unbounded Böhm tree or Böhm lambda theory.

## Main Definitions

* `BohmTree` - Finite trees labelled by head variables
* `bohmTree` - Finite-depth observation with a bounded head-search budget
* `SearchTreeEqual` - Equality of the bounded observations at every depth

## Mathematical background

A **Böhm tree** BT(M) of a lambda term M is:
- ⊥ if M is unsolvable
- λx₁...xₙ.y[BT(M₁), ..., BT(Mₖ)] if M has head normal form λx₁...xₙ.y M₁ ... Mₖ

The **Böhm theory** B consists of all equations M = N such that BT(M) = BT(N).

**Source Results** (Bucciarelli-Salibra, not established by this packaging):
- B is sensible (all unsolvable terms have ⊥ as their Böhm tree)
- B is a graph theory (realized by a specific graph model)
- B is the UNIQUE maximal sensible graph theory

## References

- Bucciarelli & Salibra, "Graph Lambda Theories" (2008), §§2.2, 6
- Barendregt, "The Lambda Calculus", Chapter 10
-/

namespace Mettapedia.GSLT.GraphTheory

open Mettapedia.GSLT.Core

/-! ## Böhm Trees

A Böhm tree is a possibly infinite tree where each node is labelled with:
- A sequence of bound variables (from lambda abstractions)
- A head variable
- Children corresponding to arguments
-/

/-- A finite tree observation with nodes labelled by:
    - Number of lambda abstractions at this node
    - The head variable (de Bruijn index)
    - Children for each argument

    This is an inductive finite tree, not a coinductive representation. -/
inductive BohmTree : Type where
  /-- Bottom, also used for depth truncation and exhausted head-search budget. -/
  | bot : BohmTree
  /-- A node with lambda-abstractions, head variable, and argument subtrees -/
  | node : (numLams : Nat) → (headVar : Nat) → (args : List BohmTree) → BohmTree
  deriving Repr

-- Manual DecidableEq instance for BohmTree
-- We use a BEq instance and then build DecidableEq from it

mutual
  def BohmTree.beq : BohmTree → BohmTree → Bool
    | .bot, .bot => true
    | .node n1 h1 args1, .node n2 h2 args2 =>
        n1 == n2 && h1 == h2 && BohmTree.beqList args1 args2
    | _, _ => false

  def BohmTree.beqList : List BohmTree → List BohmTree → Bool
    | [], [] => true
    | a :: as, b :: bs => BohmTree.beq a b && BohmTree.beqList as bs
    | _, _ => false
end

instance : BEq BohmTree := ⟨BohmTree.beq⟩

/-- beq and beqList are reflexive (joint proof) -/
theorem BohmTree.beq_refl (a : BohmTree) : BohmTree.beq a a = true := by
  match a with
  | .bot => rfl
  | .node n h args =>
    simp only [beq, beq_self_eq_true, Bool.and_self, Bool.true_and]
    exact beqList_refl args
where
  beqList_refl : (as : List BohmTree) → BohmTree.beqList as as = true
    | [] => rfl
    | a :: as => by simp only [beqList, beq_refl a, beqList_refl as, Bool.and_self]

/-- Soundness: beq true implies equality -/
theorem BohmTree.beq_sound (a b : BohmTree) : BohmTree.beq a b = true → a = b := by
  match a, b with
  | .bot, .bot => intro _; rfl
  | .bot, .node _ _ _ => intro h; simp [beq] at h
  | .node _ _ _, .bot => intro h; simp [beq] at h
  | .node n1 h1 args1, .node n2 h2 args2 =>
    intro h
    simp only [beq, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨hn, hh⟩, hargs⟩ := h
    rw [hn, hh]
    congr 1
    exact beqList_sound args1 args2 hargs
where
  beqList_sound : (as bs : List BohmTree) → BohmTree.beqList as bs = true → as = bs
    | [], [], _ => rfl
    | [], _ :: _, h => by simp [beqList] at h
    | _ :: _, [], h => by simp [beqList] at h
    | a :: as, b :: bs, h => by
      simp only [beqList, Bool.and_eq_true] at h
      obtain ⟨hab, habs⟩ := h
      rw [beq_sound a b hab, beqList_sound as bs habs]

/-- The beq function correctly reflects equality. -/
theorem BohmTree.beq_eq_true_iff (a b : BohmTree) : BohmTree.beq a b = true ↔ a = b := by
  constructor
  · exact beq_sound a b
  · intro h; rw [h]; exact beq_refl b

instance : DecidableEq BohmTree := fun a b =>
  if h : BohmTree.beq a b = true then
    isTrue ((BohmTree.beq_eq_true_iff a b).mp h)
  else
    isFalse (fun hab => h ((BohmTree.beq_eq_true_iff a b).mpr hab))

namespace BohmTree

/-- No node information; its interpretation depends on the observation interface -/
def bottom : BohmTree := .bot

/-- Check if a Böhm tree is bottom -/
def isBottom : BohmTree → Bool
  | .bot => true
  | .node _ _ _ => false

/-- The finite maximum path length from the root; bottom has depth zero. -/
def depth : BohmTree → Nat
  | .bot => 0
  | .node _ _ args => 1 + (args.map depth).foldl max 0

/-- Transform a Böhm tree under variable shifting.
    This shifts free variables (those ≥ c + lambdaDepth) by d.
    The lambdaDepth accumulates as we traverse under lambda abstractions.

    Key insight: when we shift a term by (d, c), the Böhm tree transforms as follows:
    - Number of lambdas stays the same
    - Head variable h becomes: if h < c + lambdaDepth + numLams then h else h + d
    - Arguments are transformed recursively with increased lambda depth -/
def shiftHead (d c : Nat) : BohmTree → Nat → BohmTree
  | .bot, _ => .bot
  | .node numLams headVar args, lambdaDepth =>
      .node numLams
            (if headVar < c + lambdaDepth + numLams then headVar else headVar + d)
            (args.map (fun arg => shiftHead d c arg (lambdaDepth + numLams)))

end BohmTree

/-! ## Computing Böhm Trees

We compute Böhm trees by repeatedly finding head normal forms.
This is a partial function (may not terminate), so we use a fuel parameter.
-/

/-- Extract the head normal form structure from a term.
    Returns (numLams, headVar, args) if in HNF, or none if not. -/
def extractHNF : LambdaTerm → Option (Nat × Nat × List LambdaTerm)
  | .var n => some (0, n, [])
  | .lam t =>
      match extractHNF t with
      | some (k, h, args) => some (k + 1, h, args)
      | none => none
  | .app t s =>
      match t with
      | .var n => some (0, n, [s])
      | .app _ _ =>
          -- Need to collect all arguments
          let rec collectArgs : LambdaTerm → List LambdaTerm → Option (Nat × List LambdaTerm)
            | .var n, acc => some (n, acc)
            | .app t' s', acc => collectArgs t' (s' :: acc)
            | .lam _, _ => none
          match collectArgs t [s] with
          | some (n, args) => some (0, n, args)
          | none => none
      | .lam _ => none  -- Beta redex, not in HNF

/-- Head reduce a term one step (if possible) -/
def headReduce : LambdaTerm → Option LambdaTerm
  | .app (.lam t) s => some (s.subst 0 t)  -- subst 0 s t = substitute s (arg) for var 0 in t (body)
  | .app t s =>
      match headReduce t with
      | some t' => some (.app t' s)
      | none => none
  | .lam t =>
      match headReduce t with
      | some t' => some (.lam t')
      | none => none
  | .var _ => none

/-- Repeatedly head reduce until HNF or fuel exhausted -/
def toHNF (fuel : Nat) (t : LambdaTerm) : Option LambdaTerm :=
  match fuel with
  | 0 => none
  | fuel' + 1 =>
      if extractHNF t |>.isSome then some t
      else match headReduce t with
           | some t' => toHNF fuel' t'
           | none => none

/-- The argument collector succeeds exactly on variable-headed spines. -/
theorem collectArgs_isSome_eq (t : LambdaTerm) (arguments : List LambdaTerm) :
    (extractHNF.collectArgs t arguments).isSome = t.isAppHead := by
  induction t generalizing arguments with
  | var n => rfl
  | lam t ih => rfl
  | app t s ih _ =>
      simp only [extractHNF.collectArgs, LambdaTerm.isAppHead]
      exact ih (s :: arguments)

/-- The structural HNF extractor recognizes exactly the Boolean HNF predicate. -/
theorem extractHNF_isSome_eq_isHNF (t : LambdaTerm) :
    (extractHNF t).isSome = t.isHNF := by
  induction t with
  | var n => rfl
  | lam t ih =>
      cases h : extractHNF t with
      | none =>
          simpa only [extractHNF, h, LambdaTerm.isHNF, Option.isSome_none] using ih
      | some value =>
          simpa only [extractHNF, h, LambdaTerm.isHNF, Option.isSome_some] using ih
  | app t s ih _ =>
      cases t with
      | var n => rfl
      | lam body => rfl
      | app f a =>
          have h := collectArgs_isSome_eq (.app f a) [s]
          cases hCollect : extractHNF.collectArgs (.app f a) [s] with
          | none =>
              simpa only [extractHNF, hCollect, LambdaTerm.isHNF, Option.isSome_none] using h
          | some value =>
              simpa only [extractHNF, hCollect, LambdaTerm.isHNF, Option.isSome_some] using h

/-- A successful head-reduction operation is an actual parallel β step. -/
theorem headReduce_parRed {t result : LambdaTerm}
    (h : headReduce t = some result) : t ⇛ result := by
  induction t generalizing result with
  | var n => simp [headReduce] at h
  | lam body ih =>
      cases hBody : headReduce body with
      | none => simp [headReduce, hBody] at h
      | some reduced =>
          simp only [headReduce, hBody, Option.some.injEq] at h
          subst result
          exact ParRed.lam (ih hBody)
  | app function argument ihFunction _ =>
      cases function with
      | var n => simp [headReduce] at h
      | lam body =>
          simp only [headReduce, Option.some.injEq] at h
          subst result
          exact ParRed.beta (ParRed.refl body) (ParRed.refl argument)
      | app f a =>
          cases hFunction : headReduce (.app f a) with
          | none => simp [headReduce, hFunction] at h
          | some reduced =>
              simp only [headReduce, hFunction, Option.some.injEq] at h
              subst result
              exact ParRed.app (ihFunction hFunction) (ParRed.refl argument)

/-- Successful bounded search retains both a real reduction path and actual HNF. -/
theorem toHNF_sound {fuel : Nat} {t hnf : LambdaTerm}
    (h : toHNF fuel t = some hnf) : (t ⇛* hnf) ∧ hnf.isHNF = true := by
  induction fuel generalizing t with
  | zero => simp [toHNF] at h
  | succ fuel ih =>
      simp only [toHNF] at h
      split at h
      · rename_i hExtract
        simp only [Option.some.injEq] at h
        subst hnf
        exact ⟨Relation.ReflTransGen.refl,
          (extractHNF_isSome_eq_isHNF t).symm.trans hExtract⟩
      · cases hStep : headReduce t with
        | none => simp [hStep] at h
        | some reduced =>
            simp only [hStep] at h
            obtain ⟨hPath, hHead⟩ := ih h
            exact ⟨Relation.ReflTransGen.head (headReduce_parRed hStep) hPath, hHead⟩

/-- A successful search is evidence of reduction-sensitive solvability. -/
theorem solvable_of_toHNF {fuel : Nat} {t hnf : LambdaTerm}
    (h : toHNF fuel t = some hnf) : t.Solvable :=
  ⟨hnf, toHNF_sound h⟩

/-- Actual unsolvability prevents search success at every fuel. -/
theorem unsolvable_toHNF_none {t : LambdaTerm} (h : t.Unsolvable) (fuel : Nat) :
    toHNF fuel t = none := by
  cases hSearch : toHNF fuel t with
  | none => rfl
  | some hnf => exact (h (solvable_of_toHNF hSearch)).elim

/-! ### Helper lemmas for lambda terms -/

/-- extractHNF on lambda: succeeds iff body succeeds, with incremented numLams -/
lemma extractHNF_lam (t : LambdaTerm) :
    extractHNF (.lam t) = (extractHNF t).map fun (k, h, args) => (k + 1, h, args) := by
  simp only [extractHNF]
  cases extractHNF t <;> rfl

/-- extractHNF on lambda: some version -/
lemma extractHNF_lam_some {t : LambdaTerm} {k h : Nat} {args : List LambdaTerm}
    (hext : extractHNF t = some (k, h, args)) :
    extractHNF (.lam t) = some (k + 1, h, args) := by
  simp only [extractHNF, hext]

/-- extractHNF on lambda: none version -/
lemma extractHNF_lam_none {t : LambdaTerm} (hext : extractHNF t = none) :
    extractHNF (.lam t) = none := by
  simp only [extractHNF, hext]

/-- headReduce on lambda: succeeds iff body succeeds -/
lemma headReduce_lam (t : LambdaTerm) :
    headReduce (.lam t) = (headReduce t).map .lam := by
  simp only [headReduce]
  cases headReduce t <;> rfl

/-- headReduce on lambda: some version -/
lemma headReduce_lam_some {t t' : LambdaTerm} (hr : headReduce t = some t') :
    headReduce (.lam t) = some (.lam t') := by
  simp only [headReduce, hr]

/-- headReduce on lambda: none version -/
lemma headReduce_lam_none {t : LambdaTerm} (hr : headReduce t = none) :
    headReduce (.lam t) = none := by
  simp only [headReduce, hr]

/-! ### Shift commutes with head reduction -/

/-- Key lemma: headReduce commutes with shift.
    This is essential for proving shift_preserves_searchTreeEqual.

    The proof uses subst_0_shift for the beta redex case. -/
lemma headReduce_shift (t : LambdaTerm) (d c : Nat) :
    headReduce (t.shift d c) = (headReduce t).map (·.shift d c) := by
  match t with
  | .var n =>
    simp only [LambdaTerm.shift, headReduce]
    split <;> rfl
  | .lam body =>
    simp only [LambdaTerm.shift, headReduce]
    cases h : headReduce body with
    | none =>
      -- Need to show headReduce (body.shift d (c+1)) = none
      have ih := headReduce_shift body d (c + 1)
      simp only [ih, h, Option.map_none]
    | some body' =>
      -- Need to show headReduce (body.shift d (c+1)) = some (body'.shift d (c+1))
      have ih := headReduce_shift body d (c + 1)
      simp only [ih, h, Option.map_some, LambdaTerm.shift]
  | .app func arg =>
    match func with
    | .var n =>
      simp only [LambdaTerm.shift, headReduce]
      split <;> rfl
    | .lam body =>
      -- Beta redex case: this is the key case
      -- (.app (.lam body) arg).shift d c = .app (.lam (body.shift d (c+1))) (arg.shift d c)
      -- headReduce gives: (arg.shift d c).subst 0 (body.shift d (c+1))
      -- Which equals: subst 0 (arg.shift d c) (body.shift d (c+1))
      -- Original headReduce gives: arg.subst 0 body = subst 0 arg body
      -- Shifted: (subst 0 arg body).shift d c
      -- By subst_0_shift: shift d c (subst 0 arg body) = subst 0 (arg.shift d c) (body.shift d (c+1))
      simp only [LambdaTerm.shift, headReduce, Option.map_some]
      -- Goal: some (subst 0 (arg.shift d c) (body.shift d (c+1))) = some ((subst 0 arg body).shift d c)
      exact congrArg some (LambdaTerm.subst_0_shift body arg d c).symm
    | .app func' arg' =>
      simp only [LambdaTerm.shift, headReduce]
      -- Recurse on the inner application
      have ih := headReduce_shift (.app func' arg') d c
      simp only [LambdaTerm.shift] at ih
      cases h : headReduce (.app func' arg') with
      | none =>
        simp only [ih, h, Option.map_none]
      | some t' =>
        simp only [ih, h, Option.map_some, LambdaTerm.shift]

/-- Helper for collectArgs: collectArgs commutes with shift. -/
private lemma collectArgs_shift (t : LambdaTerm) (acc : List LambdaTerm) (d c : Nat) :
    (extractHNF.collectArgs t acc).map (fun (n, args) =>
        (if n < c then n else n + d, args.map (·.shift d c))) =
    extractHNF.collectArgs (t.shift d c) (acc.map (·.shift d c)) := by
  induction t generalizing acc with
  | var n =>
    simp only [extractHNF.collectArgs, LambdaTerm.shift, Option.map_some]
    split <;> rfl
  | lam _ =>
    simp only [extractHNF.collectArgs, LambdaTerm.shift, Option.map_none]
  | app t1 t2 ih1 _ =>
    simp only [extractHNF.collectArgs, LambdaTerm.shift]
    -- collectArgs (t1.shift d c) ((t2.shift d c) :: acc.map shift)
    have h := ih1 (t2 :: acc)
    simp only [List.map_cons] at h
    exact h

/-- If extractHNF t is some, then extractHNF (t.shift d c) is some.
    This is the key property for toHNF_shift. -/
lemma extractHNF_isSome_shift (t : LambdaTerm) (d c : Nat) :
    (extractHNF t).isSome → (extractHNF (t.shift d c)).isSome := by
  intro h
  induction t generalizing c with
  | var n =>
    simp only [LambdaTerm.shift]
    split <;> rfl
  | lam body ih =>
    simp only [extractHNF, LambdaTerm.shift] at h ⊢
    cases hext : extractHNF body with
    | none => simp [hext] at h
    | some val =>
      simp only [hext, Option.isSome_some] at h
      have ih_body := ih (c + 1)
      simp only [hext, Option.isSome_some, forall_true_left] at ih_body
      cases hext' : extractHNF (body.shift d (c + 1)) with
      | none => exact absurd ih_body (by simp [hext'])
      | some _ => simp
  | app t1 t2 ih1 ih2 =>
    simp only [extractHNF, LambdaTerm.shift] at h ⊢
    match t1 with
    | .var n =>
      -- After shift, var n becomes (if n < c then var n else var (n+d))
      -- Both cases result in (var k).app arg, so extractHNF returns some (0, k, [arg])
      simp only [LambdaTerm.shift]
      by_cases hlt : n < c
      · simp only [hlt, ↓reduceIte]; rfl
      · simp only [hlt, ↓reduceIte]; rfl
    | .lam _ =>
      simp at h
    | LambdaTerm.app t1' t2' =>
      simp only [LambdaTerm.shift]
      -- Need to show collectArgs succeeds on shifted term
      cases hcol : extractHNF.collectArgs (LambdaTerm.app t1' t2') [t2] with
      | none => simp [hcol] at h
      | some val =>
        -- collectArgs succeeded, show it succeeds on shifted term
        have hcol_shift := collectArgs_shift (LambdaTerm.app t1' t2') [t2] d c
        simp only [hcol, Option.map_some, List.map_cons, List.map_nil] at hcol_shift
        cases hcol' : extractHNF.collectArgs ((LambdaTerm.app t1' t2').shift d c) [t2.shift d c] with
        | none =>
          -- hcol_shift says some ... = none, which is impossible
          simp only [hcol'] at hcol_shift
          cases hcol_shift
        | some val' =>
          -- We have hcol' proving collectArgs succeeds
          -- Need to show the match produces some, hence .isSome = true
          -- The shift of an app is (app shifted shifted), so need to connect to hcol'
          have heq : extractHNF.collectArgs ((LambdaTerm.shift d c t1').app (LambdaTerm.shift d c t2'))
                       [LambdaTerm.shift d c t2] =
                     extractHNF.collectArgs ((LambdaTerm.app t1' t2').shift d c)
                       [t2.shift d c] := by
            simp only [LambdaTerm.shift]
          simp only [heq, hcol']
          rfl

/-- Helper: extractHNF commutes with shift.
    If a term is in HNF, shifting it preserves the HNF structure.

    Note: This is a complex lemma due to de Bruijn index arithmetic.
    The key insight is that:
    - Variables shift: n → n+d if n ≥ c
    - Lambda bodies shift with c+1
    - The head variable h in (k, h, args) is in scope after k lambdas, so it shifts if h ≥ c + k
    - IMPORTANT: Arguments also shift with cutoff c + k (they're inside k lambdas!)

    The proof requires careful tracking of the cutoff through the lambda nesting.
    This is a key technical lemma for shift_preserves_searchTreeEqual. -/
lemma extractHNF_shift (t : LambdaTerm) (d c : Nat) :
    (extractHNF t).map (fun (k, h, args) => (k, if h < c + k then h else h + d,
        args.map (·.shift d (c + k)))) = extractHNF (t.shift d c) := by
  induction t generalizing c with
  | var n =>
    -- k = 0, so c + k = c
    simp only [extractHNF, LambdaTerm.shift, Option.map_some, Nat.add_zero, List.map_nil]
    split <;> rfl
  | lam body ih =>
    simp only [extractHNF, LambdaTerm.shift]
    cases hext : extractHNF body with
    | none =>
      -- If extractHNF body = none, then extractHNF (body.shift) = none too
      simp only [Option.map_none]
      have ih_body := ih (c + 1)
      simp only [hext, Option.map_none] at ih_body
      -- ih_body: none = extractHNF (body.shift d (c+1))
      -- Goal: none = match extractHNF (body.shift) with | some => ... | none => none
      simp only [← ih_body]
    | some val =>
      obtain ⟨k, h, args⟩ := val
      simp only [Option.map_some]
      have ih_body := ih (c + 1)
      simp only [hext, Option.map_some] at ih_body
      -- ih_body: (k, if h < (c+1)+k then h else h+d, args.map (shift d ((c+1)+k)))
      --        = extractHNF (body.shift d (c+1))
      -- Goal: (k+1, if h < c+(k+1) then h else h+d, args.map (shift d (c+(k+1))))
      --     = (extractHNF (body.shift d (c+1))).map (fun (k,h,args) => (k+1, h, args))
      -- Key: c + (k+1) = (c+1) + k
      have hck : c + (k + 1) = (c + 1) + k := by omega
      simp only [hck, ← ih_body]
  | app t1 t2 ih1 ih2 =>
    simp only [extractHNF, LambdaTerm.shift]
    match t1 with
    | .var n =>
      -- Result is (0, n or n+d, [t2.shift])
      -- k = 0, so c + k = c
      simp only [LambdaTerm.shift, Option.map_some, Nat.add_zero, List.map_cons, List.map_nil]
      split <;> rfl
    | .lam _ =>
      -- Beta redex, extractHNF returns none
      simp only [LambdaTerm.shift, Option.map_none]
    | .app t1' t2' =>
      simp only [LambdaTerm.shift]
      -- Use collectArgs_shift for the nested application case
      cases hcol : extractHNF.collectArgs (.app t1' t2') [t2] with
      | none =>
        simp only [Option.map_none]
        have hcol_shift := collectArgs_shift (.app t1' t2') [t2] d c
        simp only [hcol, Option.map_none, List.map_cons, List.map_nil] at hcol_shift
        -- hcol_shift: none = extractHNF.collectArgs ((t1'.app t2').shift d c) [t2.shift d c]
        have heq : extractHNF.collectArgs ((t1'.shift d c).app (t2'.shift d c)) [t2.shift d c] =
                   extractHNF.collectArgs ((LambdaTerm.app t1' t2').shift d c) [t2.shift d c] := by
          simp only [LambdaTerm.shift]
        rw [heq, ← hcol_shift]
      | some val =>
        obtain ⟨n, args⟩ := val
        -- Result is (0, n or n+d, args.map shift)
        -- k = 0, so c + k = c
        simp only [Option.map_some, Nat.add_zero]
        have hcol_shift := collectArgs_shift (.app t1' t2') [t2] d c
        simp only [hcol, Option.map_some, List.map_cons, List.map_nil] at hcol_shift
        have heq : extractHNF.collectArgs ((t1'.shift d c).app (t2'.shift d c)) [t2.shift d c] =
                   extractHNF.collectArgs ((LambdaTerm.app t1' t2').shift d c) [t2.shift d c] := by
          simp only [LambdaTerm.shift]
        rw [heq, ← hcol_shift]

/-- toHNF commutes with shift when it succeeds.
    The proof follows by induction on fuel, using headReduce_shift for reduction steps.
    The key cases are:
    - If t is in HNF, then t.shift d c is also in HNF
    - If t reduces, then (headReduce t).shift d c = headReduce (t.shift d c) -/
lemma toHNF_shift (fuel : Nat) (t : LambdaTerm) (d c : Nat) :
    (toHNF fuel t).map (·.shift d c) = toHNF fuel (t.shift d c) := by
  induction fuel generalizing t with
  | zero =>
    simp only [toHNF, Option.map_none]
  | succ fuel' ih =>
    simp only [toHNF]
    -- Case split on whether t is already in HNF
    cases hext : (extractHNF t).isSome with
    | true =>
      -- t is in HNF, so toHNF returns some t
      simp only [↓reduceIte, Option.map_some]
      -- Need to show: t.shift d c is also in HNF
      -- By extractHNF_isSome_shift
      have hext_shift := extractHNF_isSome_shift t d c hext
      simp only [hext_shift, ↓reduceIte]
    | false =>
      -- t is not in HNF, try head reduction
      simp only [Bool.false_eq_true, ↓reduceIte]
      cases hred : headReduce t with
      | none =>
        -- No head reduction possible
        simp only [Option.map_none]
        -- Since extractHNF t is not some (hext = false), extractHNF t = none
        have hext_none : extractHNF t = none := by
          cases h : extractHNF t with
          | none => rfl
          | some _ => simp [h] at hext
        -- By extractHNF_shift with extractHNF t = none:
        have hshift := extractHNF_shift t d c
        simp only [hext_none, Option.map_none] at hshift
        -- hshift : none = extractHNF (t.shift d c)
        have hext_shift_none : extractHNF (t.shift d c) = none := hshift.symm
        have hext_shift_isSome : (extractHNF (t.shift d c)).isSome = false := by
          simp only [hext_shift_none, Option.isSome_none]
        simp only [hext_shift_isSome, Bool.false_eq_true, ↓reduceIte]
        -- headReduce (t.shift d c) = none
        have hred_shift := headReduce_shift t d c
        simp only [hred, Option.map_none] at hred_shift
        -- hred_shift : headReduce (t.shift d c) = none
        -- Goal: headReduce (t.shift d c) = match headReduce (t.shift d c) with | some => ... | none => headReduce (t.shift d c)
        -- Rewriting LHS with hred_shift gives: none = match none with ... = none
        simp only [hred_shift]
      | some t' =>
        -- Head reduction to t'
        -- Since extractHNF t is not some (hext = false), extractHNF t = none
        have hext_none : extractHNF t = none := by
          cases h : extractHNF t with
          | none => rfl
          | some _ => simp [h] at hext
        -- By extractHNF_shift with extractHNF t = none:
        have hshift := extractHNF_shift t d c
        simp only [hext_none, Option.map_none] at hshift
        -- hshift : none = extractHNF (t.shift d c)
        have hext_shift_none : extractHNF (t.shift d c) = none := hshift.symm
        have hext_shift_isSome : (extractHNF (t.shift d c)).isSome = false := by
          simp only [hext_shift_none, Option.isSome_none]
        simp only [hext_shift_isSome, Bool.false_eq_true, ↓reduceIte]
        -- headReduce (t.shift d c) = some (t'.shift d c)
        have hred_shift := headReduce_shift t d c
        simp only [hred, Option.map_some] at hred_shift
        -- hred_shift : headReduce (t.shift d c) = some (t'.shift d c)
        -- Goal: (toHNF fuel' t').map (·.shift d c) = match headReduce (t.shift d c) with ...
        simp only [hred_shift]
        -- Goal: (toHNF fuel' t').map (·.shift d c) = toHNF fuel' (t'.shift d c)
        exact ih t'

/-- toHNF on lambda: succeeds iff body succeeds -/
lemma toHNF_lam (fuel : Nat) (t : LambdaTerm) :
    toHNF fuel (.lam t) = (toHNF fuel t).map .lam := by
  induction fuel generalizing t with
  | zero => simp only [toHNF, Option.map_none]
  | succ fuel' ih =>
    simp only [toHNF]
    cases hext : extractHNF t with
    | none =>
      simp only [extractHNF_lam_none hext, Option.isSome_none, Bool.false_eq_true, ite_false]
      cases hr : headReduce t with
      | none =>
        simp only [headReduce_lam_none hr, Option.map_none]
      | some t' =>
        simp only [headReduce_lam_some hr]
        exact ih t'
    | some val =>
      obtain ⟨k, h, args⟩ := val
      simp only [extractHNF_lam_some hext, Option.isSome_some, ite_true, Option.map_some]

/-- toHNF on lambda: some version -/
lemma toHNF_lam_some {fuel : Nat} {t hnf : LambdaTerm}
    (h : toHNF fuel t = some hnf) :
    toHNF fuel (.lam t) = some (.lam hnf) := by
  rw [toHNF_lam]
  simp only [h, Option.map_some]

/-- toHNF on lambda: none version -/
lemma toHNF_lam_none {fuel : Nat} {t : LambdaTerm}
    (h : toHNF fuel t = none) :
    toHNF fuel (.lam t) = none := by
  rw [toHNF_lam]
  simp only [h, Option.map_none]

/-! ### Helper lemmas for applications -/

/-- extractHNF on application with variable head -/
lemma extractHNF_app_var (n : Nat) (s : LambdaTerm) :
    extractHNF (.app (.var n) s) = some (0, n, [s]) := rfl

/-- headReduce on application with variable head fails (already HNF) -/
lemma headReduce_app_var (n : Nat) (s : LambdaTerm) :
    headReduce (.app (.var n) s) = none := rfl

/-- toHNF on application with variable head returns the term itself -/
lemma toHNF_app_var (fuel : Nat) (hfuel : fuel > 0) (n : Nat) (s : LambdaTerm) :
    toHNF fuel (.app (.var n) s) = some (.app (.var n) s) := by
  cases fuel with
  | zero => exact (Nat.not_lt_zero 0 hfuel).elim
  | succ fuel' =>
    simp only [toHNF, extractHNF_app_var, Option.isSome_some, ite_true]

/-! ### Helper lemmas for nested applications -/

/-- extractHNF on nested applications with variable head: (x y z) -/
lemma extractHNF_app_app_var (n : Nat) (y z : LambdaTerm) :
    extractHNF (.app (.app (.var n) y) z) = some (0, n, [y, z]) := rfl

/-- headReduce on nested applications with variable head: no reduction possible -/
lemma headReduce_app_app_var (n : Nat) (y z : LambdaTerm) :
    headReduce (.app (.app (.var n) y) z) = none := rfl

/-- toHNF on nested applications with variable head: term is already HNF -/
lemma toHNF_app_app_var (fuel : Nat) (hfuel : fuel > 0) (n : Nat) (y z : LambdaTerm) :
    toHNF fuel (.app (.app (.var n) y) z) = some (.app (.app (.var n) y) z) := by
  cases fuel with
  | zero => exact (Nat.not_lt_zero 0 hfuel).elim
  | succ fuel' =>
    simp only [toHNF, extractHNF_app_app_var, Option.isSome_some, ite_true]

/-! ### Helper lemmas for beta reduction -/

/-- A beta redex (.app (.lam t) s) is not in HNF -/
lemma extractHNF_beta_redex (t s : LambdaTerm) :
    extractHNF (.app (.lam t) s) = none := rfl

/-- Head reduction of a beta redex performs the substitution -/
lemma headReduce_beta (t s : LambdaTerm) :
    headReduce (.app (.lam t) s) = some (s.subst 0 t) := rfl

/-- toHNF on a beta redex reduces to toHNF on the substituted term -/
lemma toHNF_beta_step (fuel : Nat) (t s : LambdaTerm) :
    toHNF (fuel + 1) (.app (.lam t) s) = toHNF fuel (s.subst 0 t) := by
  conv_lhs => unfold toHNF
  simp only [extractHNF_beta_redex, Option.isSome_none, Bool.false_eq_true, ite_false,
             headReduce_beta]

/-- If toHNF succeeds with some fuel, adding more fuel doesn't change the result -/
lemma toHNF_mono {t : LambdaTerm} {fuel : Nat} {hnf : LambdaTerm}
    (h : toHNF fuel t = some hnf) : toHNF (fuel + 1) t = some hnf := by
  induction fuel generalizing t with
  | zero =>
    -- toHNF 0 t = none, so h : none = some hnf is contradictory
    simp only [toHNF] at h
    cases h
  | succ fuel' ih =>
    simp only [toHNF] at h ⊢
    split at h <;> rename_i hex
    · -- Term is already in HNF
      split <;> rename_i hex'
      · exact h
      · -- hex says isSome = true, hex' says isSome ≠ true, contradiction
        exact absurd hex hex'
    · -- Term not in HNF, need to reduce
      split <;> rename_i hex'
      · -- hex says isSome ≠ true, hex' says isSome = true, contradiction
        exact absurd hex' hex
      · -- Both agree extractHNF is not some
        cases hr : headReduce t with
        | none =>
          -- Can't reduce, contradiction with h
          simp only [hr] at h
          cases h
        | some t' =>
          simp only [hr] at h ⊢
          exact ih h

/-- toHNF monotonicity for arbitrary fuel increase -/
lemma toHNF_mono_add {t : LambdaTerm} {fuel k : Nat} {hnf : LambdaTerm}
    (h : toHNF fuel t = some hnf) : toHNF (fuel + k) t = some hnf := by
  induction k with
  | zero => simp only [Nat.add_zero]; exact h
  | succ k' ih =>
    rw [Nat.add_succ]
    exact toHNF_mono ih

/-- If toHNF fails with some fuel, the term either needs more fuel or has no HNF.
    When it succeeds with more fuel, it returns the same result at any higher fuel. -/
lemma toHNF_result_stable {t : LambdaTerm} {fuel1 fuel2 : Nat} {hnf : LambdaTerm}
    (h1 : toHNF fuel1 t = some hnf) (h2 : fuel1 ≤ fuel2) : toHNF fuel2 t = some hnf := by
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le h2
  rw [hk]
  exact toHNF_mono_add h1

/-- Compute a finite, search-bounded tree observation. Tree depth determines
the head-search budget as well as recursive depth. Bottom may therefore mean
an unsolvable term, depth truncation, or exhausted head-search fuel; this
budget is not a normalization bound. -/
def bohmTree (depth : Nat) : LambdaTerm → BohmTree
  | t =>
      match depth with
      | 0 => .bot
      | depth' + 1 =>
          -- The finite head-search budget can truncate a solvable term.
          let reductionFuel := depth * (depth + 1) + 1
          match toHNF reductionFuel t with
          | none => .bot
          | some hnf =>
              match extractHNF hnf with
              | none => .bot
              | some (k, h, args) =>
                  .node k h (args.map (bohmTree depth'))

/-! ## Helper lemmas for bohmTree -/

/-- Böhm tree structure for application with variable head -/
lemma bohmTree_app_var (m : Nat) (n : Nat) (s : LambdaTerm) :
    bohmTree (m + 1) (.app (.var n) s) = .node 0 n [bohmTree m s] := by
  simp only [bohmTree]
  have hfuel : (m + 1) * (m + 1 + 1) + 1 > 0 := Nat.succ_pos _
  rw [toHNF_app_var _ hfuel]
  simp only [extractHNF_app_var, List.map]

/-- Böhm tree of nested application with variable head: (x y z) -/
lemma bohmTree_app_app_var (m : Nat) (n : Nat) (y z : LambdaTerm) :
    bohmTree (m + 1) (.app (.app (.var n) y) z) =
    .node 0 n [bohmTree m y, bohmTree m z] := by
  simp only [bohmTree]
  have hfuel : (m + 1) * (m + 1 + 1) + 1 > 0 := Nat.succ_pos _
  rw [toHNF_app_app_var _ hfuel]
  simp only [extractHNF_app_app_var, List.map]

/-- Böhm trees are congruent under application (right) when the function is a variable -/
lemma bohmTree_congAppRight_var (n : Nat) (s s' : LambdaTerm)
    (h : ∀ m, bohmTree m s = bohmTree m s') (d : Nat) :
    bohmTree d (.app (.var n) s) = bohmTree d (.app (.var n) s') := by
  cases d with
  | zero => rfl  -- Both return .bot when depth is 0
  | succ d' =>
    simp only [bohmTree_app_var]
    -- Now we have .node 0 n [bohmTree d' s] = .node 0 n [bohmTree d' s']
    rw [h d']

/-! ## Böhm Trees and Shifting

The key theorem: `bohmTree m (t.shift d c) = (bohmTree m t).shiftHead d c 0`.
This shows shifting transforms Böhm trees in a predictable way.
-/

/-- Cutoff and lambda depth are interchangeable: adding k to cutoff with depth l
    equals adding k to depth with original cutoff.
    The key property is: c + k + l + numLams = c + (k + l) + numLams. -/
theorem BohmTree.shiftHead_cutoff_eq (d c k l : Nat) : (bt : BohmTree) →
    bt.shiftHead d (c + k) l = bt.shiftHead d c (k + l)
  | .bot => by simp only [shiftHead]
  | .node numLams headVar args => by
    simp only [shiftHead]
    -- The head variable comparison: (c + k) + l + numLams = c + (k + l) + numLams
    have hcond : (c + k) + l + numLams = c + (k + l) + numLams := by omega
    simp only [hcond]
    -- The recursive args: need lambdaDepth l + numLams
    congr 1
    apply List.map_congr_left
    intro arg _
    -- Need: arg.shiftHead d (c + k) (l + numLams) = arg.shiftHead d c ((k + l) + numLams)
    have hkl : (k + l) + numLams = k + (l + numLams) := by omega
    rw [hkl]
    exact shiftHead_cutoff_eq d c k (l + numLams) arg

/-- Special case: shiftHead with offset k in lambdaDepth equals shiftHead with c+k as cutoff.
    This captures the fact that (c + k) in cutoff with 0 lambda depth
    is equivalent to c in cutoff with k lambda depth. -/
theorem BohmTree.shiftHead_offset (d c k : Nat) (bt : BohmTree) :
    bt.shiftHead d (c + k) 0 = bt.shiftHead d c k :=
  shiftHead_cutoff_eq d c k 0 bt

/-- Böhm tree commutes with shift via BohmTree.shiftHead.

    The Böhm tree of a shifted term equals the "shifted" Böhm tree of the original.
    This is essential for proving that shift preserves Böhm equality.

    Key insight: at each node with k lambdas:
    - The head variable shifts if it's free (≥ c + lambdaDepth + k)
    - Arguments are recursively shifted with increased lambda depth -/
theorem bohmTree_shift (t : LambdaTerm) (d c m : Nat) :
    bohmTree m (t.shift d c) = (bohmTree m t).shiftHead d c 0 := by
  induction m using Nat.strong_induction_on generalizing t c with
  | _ m ih =>
    cases m with
    | zero =>
      -- bohmTree 0 = .bot for any term
      simp only [bohmTree, BohmTree.shiftHead]
    | succ m' =>
      simp only [bohmTree]
      let fuel := (m' + 1) * (m' + 1 + 1) + 1
      -- Use toHNF_shift to relate the computations
      have hshift := toHNF_shift fuel t d c
      -- toHNF fuel (t.shift d c) = (toHNF fuel t).map (·.shift d c)
      rw [← hshift]
      cases htoHNF : toHNF fuel t with
      | none =>
        -- toHNF t = none: both sides give .bot
        simp only [Option.map_none, BohmTree.shiftHead]
      | some hnf =>
        -- toHNF t = some hnf
        simp only [Option.map_some]
        -- Now we need: extractHNF (hnf.shift d c) vs extractHNF hnf
        have hextshift := extractHNF_shift hnf d c
        cases hext : extractHNF hnf with
        | none =>
          -- extractHNF hnf = none: both sides give .bot
          simp only [hext, Option.map_none] at hextshift
          simp only [hextshift.symm, BohmTree.shiftHead]
        | some val =>
          obtain ⟨k, h, args⟩ := val
          -- extractHNF hnf = some (k, h, args)
          simp only [hext, Option.map_some] at hextshift
          -- hextshift tells us extractHNF (hnf.shift d c) = some (k, shifted_h, shifted_args)
          simp only [hextshift.symm]
          -- Now the goal is about .node structures
          simp only [BohmTree.shiftHead]
          -- We need to match the recursive structure
          simp only [Nat.add_zero]
          -- For the children: we need to show the mapped lists are equal
          congr 1
          -- Show the recursive args are equal
          rw [List.map_map, List.map_map]
          apply List.map_congr_left
          intro arg _
          -- Unfold function composition to get explicit form
          simp only [Function.comp_apply]
          -- Goal: bohmTree m' (arg.shift d (c + k)) = (bohmTree m' arg).shiftHead d c (0 + k)
          simp only [Nat.zero_add]
          -- Goal: bohmTree m' (arg.shift d (c + k)) = (bohmTree m' arg).shiftHead d c k
          -- Use IH with cutoff c + k
          have ih_arg := ih m' (Nat.lt_succ_self m') arg (c + k)
          -- ih_arg : bohmTree m' (arg.shift d (c + k)) = (bohmTree m' arg).shiftHead d (c + k) 0
          rw [ih_arg]
          -- Now use shiftHead_offset to relate shiftHead d (c+k) 0 to shiftHead d c k
          exact BohmTree.shiftHead_offset d c k (bohmTree m' arg)

/-- Shifting preserves Böhm equality.
    If two terms have equal Böhm trees, their shifts also have equal Böhm trees.

    Proof: bohmTree commutes with shift, so equal inputs give equal outputs. -/
theorem shift_preserves_searchTreeEqual' (s s' : LambdaTerm) (d c : Nat)
    (h : ∀ n, bohmTree n s = bohmTree n s') :
    ∀ m, bohmTree m (s.shift d c) = bohmTree m (s'.shift d c) := by
  intro m
  rw [bohmTree_shift s d c m, bohmTree_shift s' d c m, h m]

/-! ## Equality of bounded observations

This relation retains the search policy. It is not the source's exact
Böhm-tree equality, and it is not a lambda congruence: `HeadSearchControls`
refutes β-invariance (`bounded_beta_equality_fails`) and closure under
application and substitution (`searchTreeEqual_not_app_left_congruence`,
`searchTreeEqual_not_app_right_congruence`, `searchTreeEqual_not_subst_congruence`).
-/

/-- Equality of the current search-bounded observations at every depth. -/
def SearchTreeEqual (t s : LambdaTerm) : Prop :=
  ∀ n, bohmTree n t = bohmTree n s

/-- Key structural lemma: The Böhm tree of λt is determined by the Böhm tree of t,
    with the number of lambdas incremented. -/
lemma bohmTree_lam_structure (t : LambdaTerm) (m : Nat) :
    bohmTree m (.lam t) = match bohmTree m t with
      | .bot => .bot
      | .node k h args => .node (k + 1) h args := by
  cases m with
  | zero => simp only [bohmTree]
  | succ d =>
    simp only [bohmTree]
    -- Both use the same fuel
    set fuel := (d + 1) * (d + 1 + 1) + 1
    -- Use the toHNF_lam lemma
    rw [toHNF_lam fuel t]
    cases htoHNF : toHNF fuel t with
    | none =>
      simp only [Option.map_none]
    | some hnf =>
      simp only [Option.map_some]
      cases hext : extractHNF hnf with
      | none =>
        simp only [extractHNF_lam_none hext]
      | some val =>
        obtain ⟨k, h, args⟩ := val
        simp only [extractHNF_lam_some hext]

/-- Böhm trees are congruent under lambda abstraction.

    If t and t' have equal Böhm trees, then λt and λt' have equal Böhm trees.
    This follows because the Böhm tree of λt is determined by the Böhm tree of t.
-/
theorem bohmTree_congLam (t t' : LambdaTerm) (h : ∀ n, bohmTree n t = bohmTree n t') (m : Nat) :
    bohmTree m (.lam t) = bohmTree m (.lam t') := by
  -- Use the structural lemma: bohmTree of λt is determined by bohmTree of t
  rw [bohmTree_lam_structure t m, bohmTree_lam_structure t' m]
  -- Now we just need to show the match expressions are equal
  rw [h m]

/-! ## Search failure and actual unsolvability -/

/-- Failure of the existing head-search procedure at every finite fuel.
Actual unsolvability implies this predicate by `unsolvable_toHNF_none`;
the converse is proved by `semanticUnsolvable_iff_unsolvable` in
`HeadSearchAdequacy`, using head-normalization completeness. -/
def SemanticUnsolvable (t : LambdaTerm) : Prop :=
  ∀ fuel, toHNF fuel t = none

/-- All-fuel head-search failure gives bottom in every bounded tree observation. -/
theorem semanticUnsolvable_bohmTree_bot {t : LambdaTerm} (h : SemanticUnsolvable t) :
    ∀ n, bohmTree n t = .bot := by
  intro n
  cases n with
  | zero => rfl
  | succ d =>
    simp only [bohmTree]
    have h_none := h ((d + 1) * (d + 1 + 1) + 1)
    simp only [h_none]

/-- Actual unsolvable terms have bottom at every bounded tree observation.
Only search soundness is needed: success would give a real path to HNF. -/
theorem unsolvable_bohmTree_bot {t : LambdaTerm} (h : t.Unsolvable) :
    ∀ n, bohmTree n t = .bot := by
  exact semanticUnsolvable_bohmTree_bot (unsolvable_toHNF_none h)

/-!
Application/substitution congruence, graph realization, and graph-restricted
maximality for exact mathematical Böhm-tree equality are separate source
obligations. This evaluator does not supply a lambda-theory record: fixed
budgets can distinguish beta-equivalent terms. `BohmObservations` constructs
the uncapped coherent observations; `BohmSearchApproximation` relates finite
search to those observations without treating exhausted fuel as divergence.
-/

end Mettapedia.GSLT.GraphTheory
