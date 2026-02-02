import Mettapedia.GSLT.GraphTheory.BohmTree

/-!
# Approximants and the Approximation Theorem

This file formalizes finite approximations of Böhm trees, following Barendregt
"The Lambda Calculus" Chapter 10.1.

## Main Definitions

* `ApproxTerm` - Lambda terms extended with ⊥ (bottom)
* `approxLE` - Ordering on approximants (⊥ ⊑ everything)

## Key Results

* `shift_preserves_approxLE` - Shifting preserves approximation ordering
* `subst_preserves_approxLE` - Substitution preserves approximation ordering

## References

- Barendregt, "The Lambda Calculus", Chapter 10.1
-/

namespace Mettapedia.GSLT.GraphTheory

open Mettapedia.GSLT.Core

/-! ## Approximants

An approximant is a lambda term that may contain ⊥ (bottom), representing
"undefined" or "don't know yet".
-/

/-- Lambda terms extended with bottom (⊥).
    Used for finite approximations of potentially infinite Böhm trees. -/
inductive ApproxTerm : Type where
  | bot : ApproxTerm
  | var : Nat → ApproxTerm
  | lam : ApproxTerm → ApproxTerm
  | app : ApproxTerm → ApproxTerm → ApproxTerm
  deriving Repr, DecidableEq

namespace ApproxTerm

/-- Embed a regular lambda term into approximant terms -/
def ofLambdaTerm : LambdaTerm → ApproxTerm
  | .var n => .var n
  | .lam t => .lam (ofLambdaTerm t)
  | .app t s => .app (ofLambdaTerm t) (ofLambdaTerm s)

/-- Approximation ordering: t ⊑ s means t approximates s -/
def approxLE : ApproxTerm → ApproxTerm → Bool
  | .bot, _ => true
  | .var n, .var m => n == m
  | .lam t, .lam s => approxLE t s
  | .app t₁ t₂, .app s₁ s₂ => approxLE t₁ s₁ && approxLE t₂ s₂
  | _, _ => false

/-- ⊥ approximates everything -/
theorem bot_approxLE (t : ApproxTerm) : approxLE .bot t = true := rfl

/-- approxLE is reflexive -/
theorem approxLE_refl : ∀ (t : ApproxTerm), approxLE t t = true
  | .bot => rfl
  | .var _ => by simp [approxLE]
  | .lam t => by simp [approxLE, approxLE_refl t]
  | .app t s => by simp [approxLE, approxLE_refl t, approxLE_refl s]

end ApproxTerm

/-! ## Shifting on Approximants -/

/-- Shift variables in an approximant -/
def ApproxTerm.shift (d c : Nat) : ApproxTerm → ApproxTerm
  | .bot => .bot
  | .var n => .var (if n < c then n else n + d)
  | .lam t => .lam (t.shift d (c + 1))
  | .app t s => .app (t.shift d c) (s.shift d c)

/-- Shifting preserves the approximation ordering -/
theorem ApproxTerm.shift_preserves_approxLE (d c : Nat) :
    ∀ {t t' : ApproxTerm}, ApproxTerm.approxLE t t' = true →
    ApproxTerm.approxLE (t.shift d c) (t'.shift d c) = true
  | .bot, _, _ => rfl
  | .var n, .var m, h => by
      simp only [ApproxTerm.approxLE, beq_iff_eq] at h
      simp only [ApproxTerm.shift, ApproxTerm.approxLE, beq_iff_eq, h]
  | .lam t, .lam t', h => by
      simp only [ApproxTerm.approxLE] at h
      simp only [ApproxTerm.shift, ApproxTerm.approxLE]
      exact shift_preserves_approxLE d (c + 1) h
  | .app t₁ t₂, .app t₁' t₂', h => by
      simp only [ApproxTerm.approxLE, Bool.and_eq_true] at h
      simp only [ApproxTerm.shift, ApproxTerm.approxLE, Bool.and_eq_true]
      exact ⟨shift_preserves_approxLE d c h.1, shift_preserves_approxLE d c h.2⟩
  | .var _, .bot, h => Bool.false_ne_true h |>.elim
  | .var _, .lam _, h => Bool.false_ne_true h |>.elim
  | .var _, .app _ _, h => Bool.false_ne_true h |>.elim
  | .lam _, .bot, h => Bool.false_ne_true h |>.elim
  | .lam _, .var _, h => Bool.false_ne_true h |>.elim
  | .lam _, .app _ _, h => Bool.false_ne_true h |>.elim
  | .app _ _, .bot, h => Bool.false_ne_true h |>.elim
  | .app _ _, .var _, h => Bool.false_ne_true h |>.elim
  | .app _ _, .lam _, h => Bool.false_ne_true h |>.elim

/-! ## Substitution on Approximants -/

/-- Substitute in an approximant (well-founded on term structure) -/
def ApproxTerm.subst : Nat → ApproxTerm → ApproxTerm → ApproxTerm
  | _, _, .bot => .bot
  | n, s, .var m =>
      if m < n then .var m
      else if m == n then s.shift n 0
      else .var (m - 1)
  | n, s, .lam t => .lam (subst (n + 1) (s.shift 1 0) t)
  | n, s, .app t u => .app (subst n s t) (subst n s u)

/-! ## Key Lemma: Substitution preserves approximation

This is the crucial lemma for proving that Böhm equality is preserved by
substitution, which is needed for the application congruence theorems.
-/

/-- Substitution preserves the approximation ordering.
    If t ⊑ t' and s ⊑ s', then t[s/x] ⊑ t'[s'/x].

    This is proved by structural induction on t. The key insight is that
    we can fix the "substituted values must be compatible" property throughout. -/
theorem ApproxTerm.subst_preserves_approxLE :
    ∀ (t t' : ApproxTerm) (n : Nat) (s s' : ApproxTerm),
    approxLE t t' = true →
    approxLE s s' = true →
    approxLE (subst n s t) (subst n s' t') = true
  | .bot, _, _, _, _, _, _ => rfl
  | .var m, .var m', n, s, s', ht, hs => by
      simp only [approxLE, beq_iff_eq] at ht
      subst ht
      unfold subst
      split
      · simp only [approxLE, beq_self_eq_true]
      · split
        · exact shift_preserves_approxLE n 0 hs
        · simp only [approxLE, beq_self_eq_true]
  | .var _, .bot, _, _, _, ht, _ => Bool.false_ne_true ht |>.elim
  | .var _, .lam _, _, _, _, ht, _ => Bool.false_ne_true ht |>.elim
  | .var _, .app _ _, _, _, _, ht, _ => Bool.false_ne_true ht |>.elim
  | .lam t, .lam t', n, s, s', ht, hs => by
      simp only [approxLE] at ht
      unfold subst
      simp only [approxLE]
      exact subst_preserves_approxLE t t' (n + 1) (s.shift 1 0) (s'.shift 1 0) ht
        (shift_preserves_approxLE 1 0 hs)
  | .lam _, .bot, _, _, _, ht, _ => Bool.false_ne_true ht |>.elim
  | .lam _, .var _, _, _, _, ht, _ => Bool.false_ne_true ht |>.elim
  | .lam _, .app _ _, _, _, _, ht, _ => Bool.false_ne_true ht |>.elim
  | .app t₁ t₂, .app t₁' t₂', n, s, s', ht, hs => by
      simp only [approxLE, Bool.and_eq_true] at ht
      unfold subst
      simp only [approxLE, Bool.and_eq_true]
      exact ⟨subst_preserves_approxLE t₁ t₁' n s s' ht.1 hs,
             subst_preserves_approxLE t₂ t₂' n s s' ht.2 hs⟩
  | .app _ _, .bot, _, _, _, ht, _ => Bool.false_ne_true ht |>.elim
  | .app _ _, .var _, _, _, _, ht, _ => Bool.false_ne_true ht |>.elim
  | .app _ _, .lam _, _, _, _, ht, _ => Bool.false_ne_true ht |>.elim

/-! ## Böhm Tree to Approximant Conversion -/

/-- Convert a Böhm tree to an approximant at given depth -/
def BohmTree.toApproxTerm (depth : Nat) : BohmTree → ApproxTerm
  | .bot => .bot
  | .node 0 headVar args =>
      args.foldl (init := .var headVar) fun acc arg =>
        .app acc (match depth with
          | 0 => .bot
          | d + 1 => arg.toApproxTerm d)
  | .node (numLams + 1) headVar args =>
      .lam ((BohmTree.node numLams headVar args).toApproxTerm depth)

/-- toApproxTerm on bot gives bot -/
@[simp]
lemma BohmTree.toApproxTerm_bot (n : Nat) : (BohmTree.bot).toApproxTerm n = .bot := by
  unfold toApproxTerm
  rfl

/-- toApproxTerm on node with k > 0 gives a lam -/
lemma BohmTree.toApproxTerm_node_succ (n k : Nat) (hv : Nat) (args : List BohmTree) :
    (BohmTree.node (k + 1) hv args).toApproxTerm n =
    .lam ((BohmTree.node k hv args).toApproxTerm n) := by
  simp only [toApproxTerm]

/-- toApproxTerm on node 0 with empty args gives a var -/
lemma BohmTree.toApproxTerm_node_zero_nil (n : Nat) (hv : Nat) :
    (BohmTree.node 0 hv []).toApproxTerm n = .var hv := by
  unfold toApproxTerm
  simp only [List.foldl_nil]

/-- Count the number of leading lams in an ApproxTerm -/
def ApproxTerm.countLams : ApproxTerm → Nat
  | .lam t => 1 + t.countLams
  | _ => 0

/-- Count the number of nested applications in left-nested form -/
def ApproxTerm.countApps : ApproxTerm → Nat
  | .app t _ => 1 + t.countApps
  | .lam t => t.countApps  -- Look through lams
  | _ => 0

/-- Get the rightmost (last) argument from a left-nested application -/
def ApproxTerm.getLastArg : ApproxTerm → Option ApproxTerm
  | .app _ s => some s
  | .lam t => t.getLastArg  -- Look through lams
  | _ => none

/-- Get the function part of an application (one level) -/
def ApproxTerm.getAppFun : ApproxTerm → ApproxTerm
  | .app t _ => t
  | .lam t => .lam t.getAppFun  -- Preserve lams
  | t => t

/-- Strip k leading lams from an ApproxTerm -/
def ApproxTerm.stripLams : Nat → ApproxTerm → ApproxTerm
  | 0, t => t
  | n + 1, .lam t => stripLams n t
  | _ + 1, t => t  -- Shouldn't happen for well-formed input

/-- Extract args from a left-nested app structure in reverse order (rightmost first) -/
def ApproxTerm.getArgsRev : ApproxTerm → List ApproxTerm
  | .app t s => s :: t.getArgsRev
  | .lam t => t.getArgsRev.map (.lam ·)  -- Preserve lams (shouldn't happen for our use)
  | _ => []

/-- Extract args from a left-nested app structure in original order -/
def ApproxTerm.getArgs (t : ApproxTerm) : List ApproxTerm :=
  t.getArgsRev.reverse

/-- getArgsRev of a var is empty -/
lemma ApproxTerm.getArgsRev_var (n : Nat) : (ApproxTerm.var n).getArgsRev = [] := rfl

/-- getArgsRev of an app extracts the arg and recurses -/
lemma ApproxTerm.getArgsRev_app (t s : ApproxTerm) :
    (ApproxTerm.app t s).getArgsRev = s :: t.getArgsRev := rfl

/-- Generalized helper: getArgsRev of a foldl with apps gives accumulated args in reverse -/
lemma getArgsRev_foldl_app' (init : ApproxTerm) (initArgs : List ApproxTerm) (n : Nat) (args : List BohmTree)
    (h_init : init.getArgsRev = initArgs) :
    (List.foldl (fun (acc : ApproxTerm) (arg : BohmTree) =>
      ApproxTerm.app acc (arg.toApproxTerm n)) init args).getArgsRev =
    (args.map (·.toApproxTerm n)).reverse ++ initArgs := by
  induction args generalizing init initArgs with
  | nil => simp only [List.foldl_nil, List.map_nil, List.reverse_nil, List.nil_append]; exact h_init
  | cons hd tl ih =>
    simp only [List.foldl_cons, List.map_cons, List.reverse_cons, List.append_assoc]
    apply ih
    simp only [ApproxTerm.getArgsRev_app, h_init, List.singleton_append]

/-- Helper: getArgsRev of a foldl with apps starting from var hv gives args in reverse -/
lemma getArgsRev_foldl_app (hv : Nat) (n : Nat) (args : List BohmTree) :
    (List.foldl (fun (acc : ApproxTerm) (arg : BohmTree) =>
      ApproxTerm.app acc (arg.toApproxTerm n)) (ApproxTerm.var hv) args).getArgsRev =
    (args.map (·.toApproxTerm n)).reverse := by
  have h := getArgsRev_foldl_app' (ApproxTerm.var hv) [] n args rfl
  simp only [List.append_nil] at h
  exact h

/-- getArgs of the foldl gives the mapped args in order -/
lemma getArgs_foldl_app (hv : Nat) (n : Nat) (args : List BohmTree) :
    (List.foldl (fun (acc : ApproxTerm) (arg : BohmTree) =>
      ApproxTerm.app acc (arg.toApproxTerm n)) (ApproxTerm.var hv) args).getArgs =
    args.map (·.toApproxTerm n) := by
  unfold ApproxTerm.getArgs
  rw [getArgsRev_foldl_app, List.reverse_reverse]

/-- stripLams k followed by getArgs extracts the arg approximants -/
lemma BohmTree.toApproxTerm_succ_getArgs (n k hv : Nat) (args : List BohmTree) :
    (((BohmTree.node k hv args).toApproxTerm (n + 1)).stripLams k).getArgs =
    args.map (·.toApproxTerm n) := by
  induction k with
  | zero =>
    simp only [ApproxTerm.stripLams, toApproxTerm]
    exact getArgs_foldl_app hv n args
  | succ k' ih =>
    rw [toApproxTerm_node_succ]
    simp only [ApproxTerm.stripLams]
    exact ih

/-- Get the head variable from an approximant (after stripping lams and apps) -/
def ApproxTerm.getHeadVar : ApproxTerm → Option Nat
  | .var n => some n
  | .app t _ => t.getHeadVar
  | .lam t => t.getHeadVar  -- Handle nested lams
  | .bot => none

/-- getHeadVar of a foldl with apps extracts the init's head var -/
private lemma getHeadVar_foldl_app (hv : Nat) (f : ApproxTerm → BohmTree → ApproxTerm)
    (args : List BohmTree) (init : ApproxTerm) (hinit : init.getHeadVar = some hv)
    (hf : ∀ acc arg, (f acc arg).getHeadVar = acc.getHeadVar) :
    (List.foldl f init args).getHeadVar = some hv := by
  induction args generalizing init with
  | nil => simp only [List.foldl_nil]; exact hinit
  | cons hd tl ih =>
    simp only [List.foldl_cons]
    apply ih
    rw [hf]; exact hinit

/-- getHeadVar of an app extracts head var from the function part -/
private lemma ApproxTerm.getHeadVar_app (t s : ApproxTerm) : (ApproxTerm.app t s).getHeadVar = t.getHeadVar := rfl

/-- stripLams then getHeadVar equals hv for toApproxTerm -/
lemma BohmTree.toApproxTerm_headVar (n k : Nat) (hv : Nat) (args : List BohmTree) :
    (((BohmTree.node k hv args).toApproxTerm n).stripLams k).getHeadVar = some hv := by
  induction k with
  | zero =>
    simp only [ApproxTerm.stripLams, toApproxTerm]
    apply getHeadVar_foldl_app hv _ _ (.var hv) rfl
    intro acc arg
    exact ApproxTerm.getHeadVar_app acc _
  | succ k' ih =>
    rw [toApproxTerm_node_succ]
    simp only [ApproxTerm.stripLams]
    exact ih

/-- countLams of a foldl with app is 0 -/
private lemma countLams_foldl_app (init : ApproxTerm) (h_init : init.countLams = 0)
    (f : ApproxTerm → BohmTree → ApproxTerm) (args : List BohmTree)
    (hf : ∀ acc arg, (f acc arg).countLams = 0) :
    (List.foldl f init args).countLams = 0 := by
  induction args generalizing init with
  | nil => simp only [List.foldl_nil]; exact h_init
  | cons hd tl ih =>
    simp only [List.foldl_cons]
    exact ih (f init hd) (hf init hd)

/-- countLams of an app is 0 -/
private lemma ApproxTerm.countLams_app (t s : ApproxTerm) : (ApproxTerm.app t s).countLams = 0 := rfl

/-- countLams of a var is 0 -/
private lemma ApproxTerm.countLams_var (n : Nat) : (ApproxTerm.var n).countLams = 0 := rfl

/-- The number of lams in toApproxTerm equals k -/
lemma BohmTree.toApproxTerm_countLams (n k : Nat) (hv : Nat) (args : List BohmTree) :
    ((BohmTree.node k hv args).toApproxTerm n).countLams = k := by
  induction k with
  | zero =>
    unfold toApproxTerm
    apply countLams_foldl_app
    · exact ApproxTerm.countLams_var hv
    · intro acc arg; exact ApproxTerm.countLams_app acc _
  | succ k' ih =>
    rw [toApproxTerm_node_succ]
    simp [ApproxTerm.countLams, ih, Nat.add_comm]

/-- countApps of an app adds 1 -/
private lemma ApproxTerm.countApps_app (t s : ApproxTerm) : (ApproxTerm.app t s).countApps = 1 + t.countApps := rfl

/-- countApps of a var is 0 -/
private lemma ApproxTerm.countApps_var (n : Nat) : (ApproxTerm.var n).countApps = 0 := rfl

/-- countApps of a lam looks inside -/
private lemma ApproxTerm.countApps_lam (t : ApproxTerm) : (ApproxTerm.lam t).countApps = t.countApps := rfl

/-- countApps of a foldl equals length of args plus initial countApps -/
private lemma countApps_foldl' (init : ApproxTerm)
    (f : ApproxTerm → BohmTree → ApproxTerm) (args : List BohmTree)
    (hf : ∀ acc arg, (f acc arg).countApps = 1 + acc.countApps) :
    (List.foldl f init args).countApps = args.length + init.countApps := by
  induction args generalizing init with
  | nil => simp only [List.foldl_nil, List.length_nil, Nat.zero_add]
  | cons hd tl ih =>
    simp only [List.foldl_cons, List.length_cons]
    rw [ih (f init hd), hf]
    -- Goal: tl.length + (1 + init.countApps) = 1 + (tl.length + init.countApps)
    simp only [Nat.add_assoc]

/-- Specialized: countApps of a foldl starting with var equals length of args -/
private lemma countApps_foldl (init : ApproxTerm) (h_init : init.countApps = 0)
    (f : ApproxTerm → BohmTree → ApproxTerm) (args : List BohmTree)
    (hf : ∀ acc arg, (f acc arg).countApps = 1 + acc.countApps) :
    (List.foldl f init args).countApps = args.length := by
  rw [countApps_foldl' init f args hf, h_init, Nat.add_zero]

/-- The number of apps in toApproxTerm (after stripping lams) equals args.length -/
lemma BohmTree.toApproxTerm_countApps (n k : Nat) (hv : Nat) (args : List BohmTree) :
    ((BohmTree.node k hv args).toApproxTerm n).countApps = args.length := by
  induction k with
  | zero =>
    unfold toApproxTerm
    apply countApps_foldl
    · exact ApproxTerm.countApps_var hv
    · intro acc arg; exact ApproxTerm.countApps_app acc _
  | succ k' ih =>
    rw [toApproxTerm_node_succ]
    simp only [ApproxTerm.countApps_lam]
    exact ih

/-- ApproxTerm.app is never bot -/
private lemma approxTerm_app_ne_bot (t s : ApproxTerm) : ApproxTerm.app t s ≠ .bot := by
  intro h; cases h

/-- The foldl in toApproxTerm produces an app when the list is non-empty,
    and the initial value (a var or app) when the list is empty.
    Either way, it's never bot. -/
private lemma toApproxTerm_foldl_ne_bot (n : Nat) (init : ApproxTerm) (h_init : init ≠ .bot)
    (args : List BohmTree) :
    List.foldl (fun acc arg =>
      acc.app (match n with
        | 0 => .bot
        | d + 1 => arg.toApproxTerm d)) init args ≠ .bot := by
  induction args generalizing init with
  | nil => simp only [List.foldl_nil]; exact h_init
  | cons hd tl ih =>
    simp only [List.foldl_cons]
    apply ih
    exact approxTerm_app_ne_bot _ _

/-- toApproxTerm on a node never produces bot -/
lemma BohmTree.toApproxTerm_node_ne_bot (n : Nat) (k hv : Nat) (args : List BohmTree) :
    (BohmTree.node k hv args).toApproxTerm n ≠ .bot := by
  unfold toApproxTerm
  cases k with
  | zero =>
    cases args with
    | nil =>
      simp only [List.foldl_nil]
      intro h; cases h  -- .var hv ≠ .bot
    | cons hd tl =>
      simp only [List.foldl_cons]
      -- Result is foldl applied to (.var hv).app _, which is never .bot
      apply toApproxTerm_foldl_ne_bot
      exact approxTerm_app_ne_bot _ _
  | succ k' =>
    intro h; cases h  -- .lam _ ≠ .bot

/-- Helper: At any given n, if approximants are equal then k and hv are equal.
    This is the partial injectivity we can prove at a single depth. -/
private lemma toApproxTerm_eq_imp_k_hv_eq (n k₁ k₂ hv₁ hv₂ : Nat) (args₁ args₂ : List BohmTree)
    (h : (BohmTree.node k₁ hv₁ args₁).toApproxTerm n = (BohmTree.node k₂ hv₂ args₂).toApproxTerm n) :
    k₁ = k₂ ∧ hv₁ = hv₂ := by
  constructor
  · have h1 := BohmTree.toApproxTerm_countLams n k₁ hv₁ args₁
    have h2 := BohmTree.toApproxTerm_countLams n k₂ hv₂ args₂
    rw [h] at h1; omega
  · have hk : k₁ = k₂ := by
      have h1 := BohmTree.toApproxTerm_countLams n k₁ hv₁ args₁
      have h2 := BohmTree.toApproxTerm_countLams n k₂ hv₂ args₂
      rw [h] at h1; omega
    subst hk
    have h1 := BohmTree.toApproxTerm_headVar n k₁ hv₁ args₁
    have h2 := BohmTree.toApproxTerm_headVar n k₁ hv₂ args₂
    rw [h] at h1
    simp only [h1] at h2
    injection h2

/-- The sizeOf of a node is larger than the sizeOf of its args list -/
lemma BohmTree.sizeOf_node_gt_args (k hv : Nat) (args : List BohmTree) :
    sizeOf args < sizeOf (BohmTree.node k hv args) := by
  decreasing_trivial

/-- The approximation theorem: if two Böhm trees have equal approximants at ALL depths,
    they are equal. This is the fundamental connection between approximants and Böhm trees.

    Note: A single depth is NOT sufficient for injectivity!
    For example, at depth 0, all args become `.bot`, so different trees can have equal approximants.

    Proof by structural induction on the trees. For finite trees, there exists
    a depth where all subtrees are fully represented. -/
theorem BohmTree.approxEqual_imp_equal (t₁ t₂ : BohmTree)
    (h : ∀ n, t₁.toApproxTerm n = t₂.toApproxTerm n) : t₁ = t₂ := by
  match t₁, t₂ with
  | .bot, .bot => rfl
  | .bot, .node k hv args =>
    have hne := toApproxTerm_node_ne_bot 0 k hv args
    have h0 := h 0
    rw [toApproxTerm_bot] at h0
    exact absurd h0.symm hne
  | .node k hv args, .bot =>
    have hne := toApproxTerm_node_ne_bot 0 k hv args
    have h0 := h 0
    rw [toApproxTerm_bot] at h0
    exact absurd h0 hne
  | .node k₁ hv₁ args₁, .node k₂ hv₂ args₂ =>
    have ⟨hk, hhv⟩ := toApproxTerm_eq_imp_k_hv_eq 0 k₁ k₂ hv₁ hv₂ args₁ args₂ (h 0)
    subst hk hhv
    have hlen : args₁.length = args₂.length := by
      have h1 := toApproxTerm_countApps 0 k₁ hv₁ args₁
      have h2 := toApproxTerm_countApps 0 k₁ hv₁ args₂
      rw [h 0] at h1
      omega
    have hmap : ∀ n, args₁.map (·.toApproxTerm n) = args₂.map (·.toApproxTerm n) := by
      intro n
      have h_succ := h (n + 1)
      have h1 := toApproxTerm_succ_getArgs n k₁ hv₁ args₁
      have h2 := toApproxTerm_succ_getArgs n k₁ hv₁ args₂
      rw [h_succ] at h1
      rw [← h1, ← h2]
    have hargs : args₁ = args₂ := by
      apply List.ext_get hlen
      intro i h₁ h₂
      have h_elem : ∀ n, (args₁.get ⟨i, h₁⟩).toApproxTerm n = (args₂.get ⟨i, h₂⟩).toApproxTerm n := by
        intro n
        have hmapn := hmap n
        have heq := congrArg (·[i]?) hmapn
        simp only [List.getElem?_map] at heq
        simp only [List.getElem?_eq_getElem, h₁, h₂] at heq
        exact Option.some.inj heq
      exact approxEqual_imp_equal (args₁.get ⟨i, h₁⟩) (args₂.get ⟨i, h₂⟩) h_elem
    rw [hargs]
termination_by (t₁, t₂)
decreasing_by
  simp_wf
  apply Prod.Lex.left
  have hsz1 : sizeOf (args₁[i]) < sizeOf args₁ := by
    have := List.sizeOf_get args₁ ⟨i, h₁⟩
    simp only [List.get_eq_getElem] at this
    exact this
  have hsz_node : sizeOf args₁ < sizeOf (BohmTree.node k₁ hv₁ args₁) :=
    BohmTree.sizeOf_node_gt_args k₁ hv₁ args₁
  omega

/-- The n-th approximant of a lambda term -/
def nthApprox (n : Nat) (t : LambdaTerm) : ApproxTerm :=
  (bohmTree n t).toApproxTerm n

/-- If two terms have equal Böhm trees at all depths, their approximants are equal -/
theorem bohmEqual_imp_approxEqual {t s : LambdaTerm}
    (h : ∀ n, bohmTree n t = bohmTree n s) (n : Nat) :
    nthApprox n t = nthApprox n s := by
  unfold nthApprox
  rw [h n]

/-! ## Shift Preserves Böhm Equality

Shifting (de Bruijn index renaming) preserves Böhm equality because it doesn't
change the computational behavior of terms - only renames free variables.
-/

/-- Shifting preserves Böhm equality.
    If s and s' have equal Böhm trees at all depths, so do their shifted versions.

    Key insight: shift is a syntactic operation that doesn't affect reduction behavior.
    The HNF structure (lambdas, head variable, args) is preserved by consistent renaming. -/
theorem shift_preserves_bohmEqual (s s' : LambdaTerm) (d c : Nat)
    (h : ∀ n, bohmTree n s = bohmTree n s') :
    ∀ m, bohmTree m (s.shift d c) = bohmTree m (s'.shift d c) :=
  -- Proved in BohmTree.lean using bohmTree_shift
  shift_preserves_bohmEqual' s s' d c h

/-! ## Substitution Lemma for Böhm Equality

The key lemma for proving application congruence: substitution preserves Böhm equality.
-/

/-- Substitution preserves Böhm equality.
    If s and s' have equal Böhm trees, then body[s/x] and body[s'/x] have equal Böhm trees.

    Here s.subst 0 body = subst 0 s body = "substitute s for var 0 in body".

    This is the key lemma for proving bohmTree_congAppRight.

    Proof by induction on body structure, using shift_preserves_bohmEqual for lambdas. -/
theorem subst_preserves_bohmEqual (body : LambdaTerm) (s s' : LambdaTerm)
    (h : ∀ n, bohmTree n s = bohmTree n s') :
    ∀ m, bohmTree m (s.subst 0 body) = bohmTree m (s'.subst 0 body) := by
  intro m
  induction body generalizing m with
  | var n =>
    -- s.subst 0 (.var n) = subst 0 s (.var n)
    -- If n = 0: return s
    -- If n > 0: return .var (n-1)
    simp only [LambdaTerm.subst]
    split
    · -- n == 0: return s (or s')
      exact h m
    · split
      · -- n > 0: return .var (n-1), same for both
        rfl
      · -- n < 0: impossible for Nat, return .var n
        rfl
  | lam body' ih =>
    -- s.subst 0 (.lam body') = .lam ((s.shift 1 0).subst 1 body')
    -- But our theorem is for level 0 substitution. We need generalization.
    simp only [LambdaTerm.subst]
    -- Goal: bohmTree m (.lam ((s.shift 1 0).subst 1 body'))
    --     = bohmTree m (.lam ((s'.shift 1 0).subst 1 body'))
    -- By bohmTree_congLam, it suffices to show the bodies are Böhm-equal
    -- But (s.shift 1 0).subst 1 body' is a level-1 substitution, not level-0
    -- We need to generalize this theorem to arbitrary levels
    sorry
  | app body₁ body₂ ih₁ ih₂ =>
    -- s.subst 0 (.app body₁ body₂) = .app (s.subst 0 body₁) (s.subst 0 body₂)
    simp only [LambdaTerm.subst]
    -- By ih₁ and ih₂, the parts are Böhm-equal
    -- Need: bohmTree congruence for applications
    -- This creates a circular dependency with bohmTree_congAppLeft/Right
    -- The resolution requires proving these simultaneously or using a different approach
    sorry

end Mettapedia.GSLT.GraphTheory
