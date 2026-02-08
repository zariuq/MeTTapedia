import Mathlib.Data.List.Basic
import Mettapedia.OSLF.MeTTaIL.Syntax

/-!
# Locally Nameless Infrastructure for MeTTaIL

Locally nameless representation where bound variables use de Bruijn indices
and free variables/metavariables use names. α-equivalent terms are
syntactically identical.

## References

- Aydemir et al., "Engineering Formal Metatheory" (POPL 2008)
- Charguéraud, "The Locally Nameless Representation" (JAR 2012)
-/

namespace Mettapedia.OSLF.MeTTaIL.LN

open Mettapedia.OSLF.MeTTaIL.Syntax (CollType)

/-! ## The Locally Nameless Pattern Type -/

/-- Locally nameless pattern type.
    - `.bvar n`: bound variable (de Bruijn index)
    - `.fvar x`: free variable / metavariable
    - `.lambda body`: binder (no name needed)
    - `.subst body repl`: substitute `repl` for BVar 0 in `body` -/
inductive LNPattern where
  | bvar : Nat → LNPattern
  | fvar : String → LNPattern
  | apply : String → List LNPattern → LNPattern
  | lambda : LNPattern → LNPattern
  | multiLambda : Nat → LNPattern → LNPattern
  | subst : LNPattern → LNPattern → LNPattern
  | collection : CollType → List LNPattern → Option String → LNPattern
deriving Repr

/-! ## Custom Induction Principle -/

def LNPattern.inductionOn {motive : LNPattern → Prop}
    (p : LNPattern)
    (hbvar : ∀ n, motive (.bvar n))
    (hfvar : ∀ x, motive (.fvar x))
    (happly : ∀ c args, (∀ q ∈ args, motive q) → motive (.apply c args))
    (hlambda : ∀ body, motive body → motive (.lambda body))
    (hmultiLambda : ∀ n body, motive body → motive (.multiLambda n body))
    (hsubst : ∀ body repl, motive body → motive repl → motive (.subst body repl))
    (hcollection : ∀ ct elems rest, (∀ q ∈ elems, motive q) →
      motive (.collection ct elems rest))
    : motive p :=
  match p with
  | .bvar n => hbvar n
  | .fvar x => hfvar x
  | .apply c args =>
    happly c args (fun q _hq =>
      inductionOn q hbvar hfvar happly hlambda hmultiLambda hsubst hcollection)
  | .lambda body =>
    hlambda body
      (inductionOn body hbvar hfvar happly hlambda hmultiLambda hsubst hcollection)
  | .multiLambda n body =>
    hmultiLambda n body
      (inductionOn body hbvar hfvar happly hlambda hmultiLambda hsubst hcollection)
  | .subst body repl =>
    hsubst body repl
      (inductionOn body hbvar hfvar happly hlambda hmultiLambda hsubst hcollection)
      (inductionOn repl hbvar hfvar happly hlambda hmultiLambda hsubst hcollection)
  | .collection ct elems rest =>
    hcollection ct elems rest (fun q _hq =>
      inductionOn q hbvar hfvar happly hlambda hmultiLambda hsubst hcollection)
termination_by sizeOf p
decreasing_by
  all_goals simp_wf
  all_goals first
    | (have h := List.sizeOf_lt_of_mem _hq; omega)
    | omega

/-! ## List Helper -/

private theorem list_map_eq_self {α : Type*} {f : α → α} {l : List α}
    (h : ∀ a ∈ l, f a = a) : l.map f = l := by
  induction l with
  | nil => rfl
  | cons a as ih =>
    rw [List.map_cons]
    congr 1
    · exact h a (List.mem_cons.mpr (Or.inl rfl))
    · exact ih (fun b hb => h b (List.mem_cons.mpr (Or.inr hb)))

/-! ## Core Operations -/

/-- Shift bound variable indices ≥ `cutoff` by `shift`. -/
def liftBVars (cutoff shift : Nat) : LNPattern → LNPattern
  | .bvar n => if n >= cutoff then .bvar (n + shift) else .bvar n
  | .fvar x => .fvar x
  | .apply c args => .apply c (args.map (liftBVars cutoff shift))
  | .lambda body => .lambda (liftBVars (cutoff + 1) shift body)
  | .multiLambda n body => .multiLambda n (liftBVars (cutoff + n) shift body)
  | .subst body repl =>
    .subst (liftBVars (cutoff + 1) shift body) (liftBVars cutoff shift repl)
  | .collection ct elems rest =>
    .collection ct (elems.map (liftBVars cutoff shift)) rest
termination_by p => sizeOf p

/-- Replace `BVar k` with term `u` (opening a binder scope). -/
def openBVar (k : Nat) (u : LNPattern) : LNPattern → LNPattern
  | .bvar n => if n == k then u else .bvar n
  | .fvar x => .fvar x
  | .apply c args => .apply c (args.map (openBVar k u))
  | .lambda body => .lambda (openBVar (k + 1) u body)
  | .multiLambda n body => .multiLambda n (openBVar (k + n) u body)
  | .subst body repl =>
    .subst (openBVar (k + 1) u body) (openBVar k u repl)
  | .collection ct elems rest =>
    .collection ct (elems.map (openBVar k u)) rest
termination_by p => sizeOf p

/-- Replace `FVar x` with `BVar k` (abstracting a free variable). -/
def closeFVar (k : Nat) (x : String) : LNPattern → LNPattern
  | .bvar n => .bvar n
  | .fvar y => if y == x then .bvar k else .fvar y
  | .apply c args => .apply c (args.map (closeFVar k x))
  | .lambda body => .lambda (closeFVar (k + 1) x body)
  | .multiLambda n body => .multiLambda n (closeFVar (k + n) x body)
  | .subst body repl =>
    .subst (closeFVar (k + 1) x body) (closeFVar k x repl)
  | .collection ct elems rest =>
    .collection ct (elems.map (closeFVar k x)) rest
termination_by p => sizeOf p

/-- Substitute term `u` for free variable `x`. -/
def substFVar (x : String) (u : LNPattern) : LNPattern → LNPattern
  | .bvar n => .bvar n
  | .fvar y => if y == x then u else .fvar y
  | .apply c args => .apply c (args.map (substFVar x u))
  | .lambda body => .lambda (substFVar x u body)
  | .multiLambda n body => .multiLambda n (substFVar x u body)
  | .subst body repl =>
    .subst (substFVar x u body) (substFVar x u repl)
  | .collection ct elems rest =>
    .collection ct (elems.map (substFVar x u)) rest
termination_by p => sizeOf p

/-! ## Free Variables and Freshness -/

/-- Collect all free variable names. Trivial in locally nameless:
    just gather FVar names. No binder filtering needed. -/
def freeVars : LNPattern → List String
  | .bvar _ => []
  | .fvar x => [x]
  | .apply _ args => args.flatMap freeVars
  | .lambda body => freeVars body
  | .multiLambda _ body => freeVars body
  | .subst body repl => freeVars body ++ freeVars repl
  | .collection _ elems _ => elems.flatMap freeVars
termination_by p => sizeOf p

/-- Check if a name is fresh (not free) in a pattern. -/
def isFresh (x : String) (p : LNPattern) : Bool :=
  !(freeVars p).contains x

/-! ## Local Closure -/

mutual
  /-- All BVars in `p` have index < `k`. -/
  def lc_at : Nat → LNPattern → Bool
    | k, .bvar n => n < k
    | _, .fvar _ => true
    | k, .apply _ args => lc_at_list k args
    | k, .lambda body => lc_at (k + 1) body
    | k, .multiLambda n body => lc_at (k + n) body
    | k, .subst body repl => lc_at (k + 1) body && lc_at k repl
    | k, .collection _ elems _ => lc_at_list k elems

  def lc_at_list : Nat → List LNPattern → Bool
    | _, [] => true
    | k, p :: ps => lc_at k p && lc_at_list k ps
end

/-- A pattern is locally closed (no dangling BVars). -/
def lc (p : LNPattern) : Bool := lc_at 0 p

/-! ## Lemma: lc_at_list membership -/

theorem lc_at_list_mem {k : Nat} {ps : List LNPattern} {p : LNPattern}
    (hlc : lc_at_list k ps = true) (hp : p ∈ ps) : lc_at k p = true := by
  induction ps with
  | nil => cases hp
  | cons q qs ih =>
    simp only [lc_at_list, Bool.and_eq_true] at hlc
    cases List.mem_cons.mp hp with
    | inl heq => rw [heq]; exact hlc.1
    | inr hmem => exact ih hlc.2 hmem

/-! ## Lemma: liftBVars by 0 is identity -/

theorem liftBVars_zero (p : LNPattern) (cutoff : Nat) :
    liftBVars cutoff 0 p = p := by
  induction p using LNPattern.inductionOn generalizing cutoff with
  | hbvar n =>
    simp only [liftBVars]
    split <;> simp
  | hfvar _ => simp only [liftBVars]
  | happly c args ih =>
    simp only [liftBVars]; congr 1
    exact list_map_eq_self (fun q hq => ih q hq cutoff)
  | hlambda body ih =>
    simp only [liftBVars]; congr 1; exact ih (cutoff + 1)
  | hmultiLambda n body ih =>
    simp only [liftBVars]; congr 1; exact ih (cutoff + n)
  | hsubst body repl ihb ihr =>
    simp only [liftBVars]; congr 1
    · exact ihb (cutoff + 1)
    · exact ihr cutoff
  | hcollection ct elems rest ih =>
    simp only [liftBVars]; congr 1
    exact list_map_eq_self (fun q hq => ih q hq cutoff)

/-! ## Lemma: Opening a locally-closed term is identity -/

theorem openBVar_lc_at (k : Nat) (u : LNPattern) (p : LNPattern)
    (hlc : lc_at k p = true) : openBVar k u p = p := by
  induction p using LNPattern.inductionOn generalizing k with
  | hbvar n =>
    unfold openBVar
    split
    · next h =>
      -- n == k, but lc_at k (.bvar n) = true means n < k, contradiction
      exfalso
      have heq : n = k := eq_of_beq h
      subst heq; unfold lc_at at hlc; simp at hlc
    · rfl
  | hfvar _ => simp only [openBVar]
  | happly c args ih =>
    simp only [lc_at] at hlc
    simp only [openBVar]; congr 1
    exact list_map_eq_self (fun q hq => ih q hq k (lc_at_list_mem hlc hq))
  | hlambda body ih =>
    simp only [lc_at] at hlc
    simp only [openBVar]; congr 1; exact ih (k + 1) hlc
  | hmultiLambda n body ih =>
    simp only [lc_at] at hlc
    simp only [openBVar]; congr 1; exact ih (k + n) hlc
  | hsubst body repl ihb ihr =>
    simp only [lc_at, Bool.and_eq_true] at hlc
    simp only [openBVar]; congr 1
    · exact ihb (k + 1) hlc.1
    · exact ihr k hlc.2
  | hcollection ct elems rest ih =>
    simp only [lc_at] at hlc
    simp only [openBVar]; congr 1
    exact list_map_eq_self (fun q hq => ih q hq k (lc_at_list_mem hlc hq))

/-! ## Lemma: close then open is identity (when x is fresh) -/

theorem close_open_id (k : Nat) (x : String) (p : LNPattern)
    (hfresh : x ∉ freeVars p) :
    closeFVar k x (openBVar k (.fvar x) p) = p := by
  induction p using LNPattern.inductionOn generalizing k with
  | hbvar n =>
    simp only [openBVar]
    split
    · -- n == k, so openBVar produces .fvar x
      simp only [closeFVar, beq_self_eq_true, ↓reduceIte]
      next h => congr 1; exact (beq_iff_eq.mp h).symm
    · -- n ≠ k, openBVar produces .bvar n
      simp only [closeFVar]
  | hfvar y =>
    simp only [freeVars, List.mem_singleton] at hfresh
    simp only [openBVar, closeFVar]
    have : ¬(y = x) := fun h => hfresh (h ▸ rfl)
    simp [beq_eq_false_iff_ne.mpr this]
  | happly c args ih =>
    simp only [freeVars] at hfresh
    simp only [openBVar, closeFVar, List.map_map]
    congr 1
    exact list_map_eq_self fun q hq => ih q hq k
      (fun hxq => hfresh (List.mem_flatMap.mpr ⟨q, hq, hxq⟩))
  | hlambda body ih =>
    simp only [freeVars] at hfresh
    simp only [openBVar, closeFVar]; congr 1
    exact ih (k + 1) hfresh
  | hmultiLambda n body ih =>
    simp only [freeVars] at hfresh
    simp only [openBVar, closeFVar]; congr 1
    exact ih (k + n) hfresh
  | hsubst body repl ihb ihr =>
    simp only [freeVars, List.mem_append] at hfresh
    push_neg at hfresh
    simp only [openBVar, closeFVar]; congr 1
    · exact ihb (k + 1) hfresh.1
    · exact ihr k hfresh.2
  | hcollection ct elems rest ih =>
    simp only [freeVars] at hfresh
    simp only [openBVar, closeFVar, List.map_map]
    congr 1
    exact list_map_eq_self fun q hq => ih q hq k
      (fun hxq => hfresh (List.mem_flatMap.mpr ⟨q, hq, hxq⟩))

/-! ## Lemma: open then close is identity (when locally closed) -/

theorem open_close_id (k : Nat) (x : String) (p : LNPattern)
    (hlc : lc_at k p = true) :
    openBVar k (.fvar x) (closeFVar k x p) = p := by
  induction p using LNPattern.inductionOn generalizing k with
  | hbvar n =>
    -- closeFVar doesn't touch BVars, so closeFVar k x (.bvar n) = .bvar n
    simp only [closeFVar, openBVar]
    -- Goal: if n == k then .fvar x else .bvar n = .bvar n
    -- lc_at k (.bvar n) = true means n < k, so n ≠ k
    split
    · next h =>
      exfalso
      have heq : n = k := eq_of_beq h
      subst heq; unfold lc_at at hlc; simp at hlc
    · rfl
  | hfvar y =>
    simp only [closeFVar]
    split
    · next h =>
      simp only [openBVar, beq_self_eq_true, ↓reduceIte]
      congr 1; exact (beq_iff_eq.mp h).symm
    · simp only [openBVar]
  | happly c args ih =>
    simp only [lc_at] at hlc
    simp only [closeFVar, openBVar, List.map_map]
    congr 1
    exact list_map_eq_self fun q hq =>
      ih q hq k (lc_at_list_mem hlc hq)
  | hlambda body ih =>
    simp only [lc_at] at hlc
    simp only [closeFVar, openBVar]; congr 1
    exact ih (k + 1) hlc
  | hmultiLambda n body ih =>
    simp only [lc_at] at hlc
    simp only [closeFVar, openBVar]; congr 1
    exact ih (k + n) hlc
  | hsubst body repl ihb ihr =>
    simp only [lc_at, Bool.and_eq_true] at hlc
    simp only [closeFVar, openBVar]; congr 1
    · exact ihb (k + 1) hlc.1
    · exact ihr k hlc.2
  | hcollection ct elems rest ih =>
    simp only [lc_at] at hlc
    simp only [closeFVar, openBVar, List.map_map]
    congr 1
    exact list_map_eq_self fun q hq =>
      ih q hq k (lc_at_list_mem hlc hq)

end Mettapedia.OSLF.MeTTaIL.LN
