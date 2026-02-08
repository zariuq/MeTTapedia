import Mathlib.Data.List.Basic
import Mettapedia.OSLF.MeTTaIL.Syntax

/-!
# Substitution for MeTTaIL (Locally Nameless)

Substitution operations for the locally nameless Pattern representation.
Bound variables use de Bruijn indices, so capture-avoidance is automatic —
no environment filtering needed.

## Key Operations

- `openBVar`: Replace BVar k with a term (enter binder scope)
- `closeFVar`: Replace FVar x with BVar k (abstract a free variable)
- `liftBVars`: Shift de Bruijn indices (move under additional binders)
- `substFVar`: Substitute a term for a free variable (metavar instantiation)
- `applySubst`: Apply a substitution environment to a pattern

## References

- Aydemir et al., "Engineering Formal Metatheory" (POPL 2008)
- `/home/zar/claude/hyperon/mettail-rust/macros/src/gen/term_ops/subst.rs`
-/

namespace Mettapedia.OSLF.MeTTaIL.Substitution

open Mettapedia.OSLF.MeTTaIL.Syntax

/-! ## Locally Nameless Core Operations -/

/-- Replace `BVar k` with term `u` (opening a binder scope). -/
def openBVar (k : Nat) (u : Pattern) : Pattern → Pattern
  | .bvar n => if n == k then u else .bvar n
  | .fvar x => .fvar x
  | .apply c args => .apply c (args.map (openBVar k u))
  | .lambda body => .lambda (openBVar (k + 1) u body)
  | .multiLambda n body => .multiLambda n (openBVar (k + n) u body)
  | .subst body repl => .subst (openBVar (k + 1) u body) (openBVar k u repl)
  | .collection ct elems rest =>
    .collection ct (elems.map (openBVar k u)) rest
termination_by p => sizeOf p

/-- Replace `FVar x` with `BVar k` (abstracting a free variable). -/
def closeFVar (k : Nat) (x : String) : Pattern → Pattern
  | .bvar n => .bvar n
  | .fvar y => if y == x then .bvar k else .fvar y
  | .apply c args => .apply c (args.map (closeFVar k x))
  | .lambda body => .lambda (closeFVar (k + 1) x body)
  | .multiLambda n body => .multiLambda n (closeFVar (k + n) x body)
  | .subst body repl => .subst (closeFVar (k + 1) x body) (closeFVar k x repl)
  | .collection ct elems rest =>
    .collection ct (elems.map (closeFVar k x)) rest
termination_by p => sizeOf p

/-- Shift bound variable indices ≥ `cutoff` by `shift`. -/
def liftBVars (cutoff shift : Nat) : Pattern → Pattern
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

/-! ## Environment-Based Substitution

Substitution environment for replacing free variables (metavariables)
with terms. In locally nameless, NO capture-avoidance filtering is needed:
binders use de Bruijn indices, so there are no name conflicts.
-/

/-- An environment maps free variable names to patterns -/
abbrev SubstEnv := List (String × Pattern)

namespace SubstEnv

def empty : SubstEnv := []

def extend (env : SubstEnv) (name : String) (term : Pattern) : SubstEnv :=
  (name, term) :: env

def find (env : SubstEnv) (name : String) : Option Pattern :=
  match env.find? (fun p => p.1 == name) with
  | some (_, term) => some term
  | none => none

end SubstEnv

/-- Apply substitution environment to a pattern.
    In locally nameless, lambda/multiLambda cases do NOT filter the environment
    — de Bruijn indices eliminate capture. -/
def applySubst (env : SubstEnv) : Pattern → Pattern
  | .bvar n => .bvar n  -- BVars are not in the environment
  | .fvar name =>
    match env.find name with
    | some replacement => replacement
    | none => .fvar name
  | .apply constructor args =>
    .apply constructor (args.map (applySubst env))
  | .lambda body =>
    -- NO filtering! De Bruijn indices prevent capture.
    .lambda (applySubst env body)
  | .multiLambda n body =>
    .multiLambda n (applySubst env body)
  | .subst body replacement =>
    -- Explicit substitution: apply env to both parts, then openBVar
    let body' := applySubst env body
    let repl' := applySubst env replacement
    openBVar 0 repl' body'
  | .collection ct elements rest =>
    .collection ct (elements.map (applySubst env)) rest
termination_by p => sizeOf p

/-! ## Freshness Checking -/

/-- Get free variables of a pattern.
    Trivial in locally nameless: just collect FVar names.
    No filtering needed — binders are implicit via de Bruijn indices. -/
def freeVars : Pattern → List String
  | .bvar _ => []
  | .fvar name => [name]
  | .apply _ args => args.flatMap freeVars
  | .lambda body => freeVars body
  | .multiLambda _ body => freeVars body
  | .subst body replacement => freeVars body ++ freeVars replacement
  | .collection _ elements _ => elements.flatMap freeVars
termination_by p => sizeOf p

/-- Check if a variable is fresh in a pattern -/
def isFresh (x : String) (p : Pattern) : Bool :=
  !((freeVars p).contains x)

/-- Check a freshness condition -/
def checkFreshness (fc : FreshnessCondition) : Bool :=
  isFresh fc.varName fc.term

/-- Get ALL variables (both free and bound variable names).
    In locally nameless, BVars are indices not names, so allVars = freeVars.
    Kept for API compatibility during migration. -/
def allVars : Pattern → List String := freeVars

/-- A variable is globally fresh if it does not appear anywhere in the pattern.
    In locally nameless, this is the same as `isFresh` since BVars have no names. -/
def isGloballyFresh (x : String) (p : Pattern) : Bool := isFresh x p

/-! ## COMM Rule Substitution -/

/-- Apply the ρ-calculus COMM rule substitution.
    In locally nameless: substitute `NQuote(q)` for BVar 0 in the body. -/
def commSubst (pBody q : Pattern) : Pattern :=
  openBVar 0 (.apply "NQuote" [q]) pBody

/-! ## Pattern Normal Forms -/

mutual
  /-- A pattern has no explicit substitution nodes -/
  def noExplicitSubst : Pattern → Bool
    | .bvar _ => true
    | .fvar _ => true
    | .apply _ args => allNoExplicitSubst args
    | .lambda body => noExplicitSubst body
    | .multiLambda _ body => noExplicitSubst body
    | .subst _ _ => false
    | .collection _ elems _ => allNoExplicitSubst elems

  def allNoExplicitSubst : List Pattern → Bool
    | [] => true
    | p :: ps => noExplicitSubst p && allNoExplicitSubst ps
end

/-- If allNoExplicitSubst holds for a list and p ∈ list, then noExplicitSubst p -/
theorem allNoExplicitSubst_mem {ps : List Pattern} {p : Pattern}
    (hall : allNoExplicitSubst ps) (hp : p ∈ ps) : noExplicitSubst p := by
  induction ps with
  | nil => cases hp
  | cons q qs ih =>
    simp only [allNoExplicitSubst, Bool.and_eq_true] at hall
    cases List.mem_cons.mp hp with
    | inl heq => rw [heq]; exact hall.1
    | inr hmem => exact ih hall.2 hmem

/-! ## Local Closure -/

mutual
  /-- All BVars in `p` have index < `k`. -/
  def lc_at : Nat → Pattern → Bool
    | k, .bvar n => n < k
    | _, .fvar _ => true
    | k, .apply _ args => lc_at_list k args
    | k, .lambda body => lc_at (k + 1) body
    | k, .multiLambda n body => lc_at (k + n) body
    | k, .subst body repl => lc_at (k + 1) body && lc_at k repl
    | k, .collection _ elems _ => lc_at_list k elems

  def lc_at_list : Nat → List Pattern → Bool
    | _, [] => true
    | k, p :: ps => lc_at k p && lc_at_list k ps
end

/-- A pattern is locally closed (no dangling BVars). -/
def lc (p : Pattern) : Bool := lc_at 0 p

/-! ## Theorems -/

/-- Helper: if `f a = a` for all `a ∈ l`, then `l.map f = l`. -/
private theorem list_map_eq_self {α : Type*} {f : α → α} {l : List α}
    (h : ∀ a ∈ l, f a = a) : l.map f = l := by
  induction l with
  | nil => rfl
  | cons a as ih =>
    rw [List.map_cons]
    congr 1
    · exact h a (List.mem_cons.mpr (Or.inl rfl))
    · exact ih (fun b hb => h b (List.mem_cons.mpr (Or.inr hb)))

/-- lc_at_list membership: if all elements are lc_at k, then each is. -/
theorem lc_at_list_mem {k : Nat} {ps : List Pattern} {p : Pattern}
    (hlc : lc_at_list k ps = true) (hp : p ∈ ps) : lc_at k p = true := by
  induction ps with
  | nil => cases hp
  | cons q qs ih =>
    simp only [lc_at_list, Bool.and_eq_true] at hlc
    cases List.mem_cons.mp hp with
    | inl heq => rw [heq]; exact hlc.1
    | inr hmem => exact ih hlc.2 hmem

/-- Empty substitution is identity (BVars untouched, FVars not in empty env). -/
theorem subst_empty (p : Pattern) (h : noExplicitSubst p) :
    applySubst SubstEnv.empty p = p := by
  induction p using Pattern.inductionOn with
  | hbvar _ => simp only [applySubst]
  | hfvar name =>
    simp only [applySubst, SubstEnv.find, SubstEnv.empty, List.find?]
  | happly constructor args ih =>
    unfold noExplicitSubst at h
    simp only [applySubst]; congr 1
    exact list_map_eq_self (fun q hq => ih q hq (allNoExplicitSubst_mem h hq))
  | hlambda body ih =>
    unfold noExplicitSubst at h
    simp only [applySubst]; congr 1; exact ih h
  | hmultiLambda n body ih =>
    unfold noExplicitSubst at h
    simp only [applySubst]; congr 1; exact ih h
  | hsubst body repl _ _ =>
    unfold noExplicitSubst at h; exact absurd h Bool.false_ne_true
  | hcollection ct elems rest ih =>
    unfold noExplicitSubst at h
    simp only [applySubst]; congr 1
    exact list_map_eq_self (fun q hq => ih q hq (allNoExplicitSubst_mem h hq))

/-- Lifting by 0 is identity. -/
theorem liftBVars_zero (p : Pattern) (cutoff : Nat) :
    liftBVars cutoff 0 p = p := by
  induction p using Pattern.inductionOn generalizing cutoff with
  | hbvar n => simp only [liftBVars]; split <;> simp
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

/-- Opening a locally-closed term at level k is identity. -/
theorem openBVar_lc_at (k : Nat) (u : Pattern) (p : Pattern)
    (hlc : lc_at k p = true) : openBVar k u p = p := by
  induction p using Pattern.inductionOn generalizing k with
  | hbvar n =>
    unfold openBVar; split
    · next h =>
      exfalso; have := eq_of_beq h; subst this
      unfold lc_at at hlc; simp at hlc
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

/-- Close then open is identity when x is fresh. -/
theorem close_open_id (k : Nat) (x : String) (p : Pattern)
    (hfresh : x ∉ freeVars p) :
    closeFVar k x (openBVar k (.fvar x) p) = p := by
  induction p using Pattern.inductionOn generalizing k with
  | hbvar n =>
    simp only [openBVar]; split
    · simp only [closeFVar, beq_self_eq_true, ↓reduceIte]
      next h => congr 1; exact (beq_iff_eq.mp h).symm
    · simp only [closeFVar]
  | hfvar y =>
    simp only [freeVars, List.mem_singleton] at hfresh
    simp only [openBVar, closeFVar]
    have : ¬(y = x) := fun h => hfresh (h ▸ rfl)
    simp [beq_eq_false_iff_ne.mpr this]
  | happly c args ih =>
    simp only [freeVars] at hfresh
    simp only [openBVar, closeFVar, List.map_map]; congr 1
    exact list_map_eq_self fun q hq => ih q hq k
      (fun hxq => hfresh (List.mem_flatMap.mpr ⟨q, hq, hxq⟩))
  | hlambda body ih =>
    simp only [freeVars] at hfresh
    simp only [openBVar, closeFVar]; congr 1; exact ih (k + 1) hfresh
  | hmultiLambda n body ih =>
    simp only [freeVars] at hfresh
    simp only [openBVar, closeFVar]; congr 1; exact ih (k + n) hfresh
  | hsubst body repl ihb ihr =>
    simp only [freeVars, List.mem_append] at hfresh; push_neg at hfresh
    simp only [openBVar, closeFVar]; congr 1
    · exact ihb (k + 1) hfresh.1
    · exact ihr k hfresh.2
  | hcollection ct elems rest ih =>
    simp only [freeVars] at hfresh
    simp only [openBVar, closeFVar, List.map_map]; congr 1
    exact list_map_eq_self fun q hq => ih q hq k
      (fun hxq => hfresh (List.mem_flatMap.mpr ⟨q, hq, hxq⟩))

/-- Open then close is identity when locally closed at level k. -/
theorem open_close_id (k : Nat) (x : String) (p : Pattern)
    (hlc : lc_at k p = true) :
    openBVar k (.fvar x) (closeFVar k x p) = p := by
  induction p using Pattern.inductionOn generalizing k with
  | hbvar n =>
    simp only [closeFVar, openBVar]; split
    · next h =>
      exfalso; have := eq_of_beq h; subst this
      unfold lc_at at hlc; simp at hlc
    · rfl
  | hfvar y =>
    simp only [closeFVar]; split
    · next h =>
      simp only [openBVar, beq_self_eq_true, ↓reduceIte]
      congr 1; exact (beq_iff_eq.mp h).symm
    · simp only [openBVar]
  | happly c args ih =>
    simp only [lc_at] at hlc
    simp only [closeFVar, openBVar, List.map_map]; congr 1
    exact list_map_eq_self fun q hq => ih q hq k (lc_at_list_mem hlc hq)
  | hlambda body ih =>
    simp only [lc_at] at hlc
    simp only [closeFVar, openBVar]; congr 1; exact ih (k + 1) hlc
  | hmultiLambda n body ih =>
    simp only [lc_at] at hlc
    simp only [closeFVar, openBVar]; congr 1; exact ih (k + n) hlc
  | hsubst body repl ihb ihr =>
    simp only [lc_at, Bool.and_eq_true] at hlc
    simp only [closeFVar, openBVar]; congr 1
    · exact ihb (k + 1) hlc.1
    · exact ihr k hlc.2
  | hcollection ct elems rest ih =>
    simp only [lc_at] at hlc
    simp only [closeFVar, openBVar, List.map_map]; congr 1
    exact list_map_eq_self fun q hq => ih q hq k (lc_at_list_mem hlc hq)

/-! ## Substitution Helpers -/

/-- Helper: applySubst on NQuote -/
theorem applySubst_quote (env : SubstEnv) (p : Pattern) :
    applySubst env (.apply "NQuote" [p]) = .apply "NQuote" [applySubst env p] := by
  simp only [applySubst, List.map_cons, List.map_nil]

/-- Helper: applySubst on PDrop -/
theorem applySubst_drop (env : SubstEnv) (p : Pattern) :
    applySubst env (.apply "PDrop" [p]) = .apply "PDrop" [applySubst env p] := by
  simp only [applySubst, List.map_cons, List.map_nil]

/-- Helper: applySubst on POutput -/
theorem applySubst_output (env : SubstEnv) (n q : Pattern) :
    applySubst env (.apply "POutput" [n, q]) =
      .apply "POutput" [applySubst env n, applySubst env q] := by
  simp only [applySubst, List.map_cons, List.map_nil]

/-- commSubst unfolds to openBVar with NQuote -/
theorem commSubst_def (p q : Pattern) :
    commSubst p q = openBVar 0 (.apply "NQuote" [q]) p := by
  rfl

/-! ## Monotonicity of Local Closure -/

/-- Build lc_at_list from pointwise lc_at. -/
theorem lc_at_list_of_forall {k : Nat} {ps : List Pattern}
    (h : ∀ p ∈ ps, lc_at k p = true) : lc_at_list k ps = true := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    simp only [lc_at_list, Bool.and_eq_true]
    exact ⟨h p (List.mem_cons.mpr (Or.inl rfl)),
           ih (fun q hq => h q (List.mem_cons.mpr (Or.inr hq)))⟩

/-- Local closure is monotone in the level. -/
theorem lc_at_mono {k k' : Nat} {p : Pattern}
    (hlc : lc_at k p = true) (hle : k ≤ k') :
    lc_at k' p = true := by
  induction p using Pattern.inductionOn generalizing k k' with
  | hbvar n =>
    unfold lc_at at hlc ⊢
    exact decide_eq_true (Nat.lt_of_lt_of_le (of_decide_eq_true hlc) hle)
  | hfvar _ => rfl
  | happly _ args ih =>
    simp only [lc_at] at hlc ⊢
    have hmono : ∀ q ∈ args, lc_at k' q = true := fun q hq =>
      ih q hq (lc_at_list_mem hlc hq) hle
    exact lc_at_list_of_forall hmono
  | hlambda body ih =>
    unfold lc_at at hlc ⊢; exact ih hlc (Nat.add_le_add_right hle 1)
  | hmultiLambda n body ih =>
    unfold lc_at at hlc ⊢; exact ih hlc (Nat.add_le_add_right hle n)
  | hsubst body repl ihb ihr =>
    simp only [lc_at, Bool.and_eq_true] at hlc ⊢
    exact ⟨ihb hlc.1 (Nat.add_le_add_right hle 1), ihr hlc.2 hle⟩
  | hcollection _ elems _ ih =>
    simp only [lc_at] at hlc ⊢
    have hmono : ∀ q ∈ elems, lc_at k' q = true := fun q hq =>
      ih q hq (lc_at_list_mem hlc hq) hle
    exact lc_at_list_of_forall hmono

/-! ## Substitution and Freshness

These lemmas establish that substitution for a fresh variable is identity,
and that substitution commutes with opening under appropriate conditions.
These are standard locally nameless metatheory results needed for type soundness.
-/

/-- Helper: pointwise equal functions produce equal maps. -/
private theorem list_map_eq_map {α β : Type*} {f g : α → β} {l : List α}
    (h : ∀ a ∈ l, f a = g a) : l.map f = l.map g := by
  induction l with
  | nil => rfl
  | cons a as ih =>
    rw [List.map_cons, List.map_cons]
    congr 1
    · exact h a (List.mem_cons.mpr (Or.inl rfl))
    · exact ih (fun b hb => h b (List.mem_cons.mpr (Or.inr hb)))

/-- Helper: not-contains from flatMap -/
private theorem contains_false_of_flatMap_contains_false {x : String} {ps : List Pattern}
    (hfresh : (ps.flatMap freeVars).contains x = false)
    {p : Pattern} (hp : p ∈ ps) :
    (freeVars p).contains x = false := by
  by_contra habs
  have habs' : (freeVars p).contains x = true := by
    cases h : (freeVars p).contains x <;> simp_all
  have hmem : x ∈ freeVars p := by
    simp only [List.contains_iff_exists_mem_beq] at habs'
    obtain ⟨z, hz, hzx⟩ := habs'
    rwa [show z = x from (beq_iff_eq.mp hzx).symm] at hz
  have hmem' : x ∈ ps.flatMap freeVars := List.mem_flatMap.mpr ⟨p, hp, hmem⟩
  have hc : (ps.flatMap freeVars).contains x = true := by
    simp only [List.contains_iff_exists_mem_beq]; exact ⟨x, hmem', beq_self_eq_true x⟩
  exact Bool.false_ne_true (hfresh ▸ hc)

/-- Freshness decomposes: if x is fresh in an apply, it's fresh in each argument. -/
theorem isFresh_mem_of_flatMap {x : String} {c : String} {ps : List Pattern}
    (hfresh : isFresh x (.apply c ps) = true) {p : Pattern} (hp : p ∈ ps) :
    isFresh x p = true := by
  simp only [isFresh, freeVars, Bool.not_eq_true'] at hfresh ⊢
  exact contains_false_of_flatMap_contains_false hfresh hp

/-- Freshness decomposes for collections. -/
theorem isFresh_collection_mem {x : String} {ct : CollType} {ps : List Pattern} {rest : Option String}
    (hfresh : isFresh x (.collection ct ps rest) = true) {p : Pattern} (hp : p ∈ ps) :
    isFresh x p = true := by
  simp only [isFresh, freeVars, Bool.not_eq_true'] at hfresh ⊢
  exact contains_false_of_flatMap_contains_false hfresh hp

/-- Substituting for a fresh variable is identity on subst-free patterns.

    Requires `noExplicitSubst` because `applySubst` performs `openBVar` on
    `.subst` nodes, changing the term structure even when the env has no effect. -/
theorem applySubst_fresh_single {x : String} {q : Pattern} {p : Pattern}
    (hfresh : isFresh x p = true) (hnes : noExplicitSubst p = true) :
    applySubst (SubstEnv.extend SubstEnv.empty x q) p = p := by
  induction p using Pattern.inductionOn with
  | hbvar _ => simp [applySubst]
  | hfvar name =>
    simp only [applySubst, SubstEnv.extend, SubstEnv.empty, SubstEnv.find, List.find?]
    simp only [isFresh, freeVars, List.contains_cons, List.contains_nil, Bool.or_false,
               Bool.not_eq_true'] at hfresh
    have hne : x ≠ name := fun h => by simp [h] at hfresh
    simp [beq_eq_false_iff_ne.mpr hne]
  | happly c args ih =>
    simp only [applySubst]; congr 1
    exact list_map_eq_self fun a ha =>
      ih a ha (isFresh_mem_of_flatMap hfresh ha) (allNoExplicitSubst_mem (by exact hnes) ha)
  | hlambda body ih =>
    simp only [applySubst]; congr 1
    simp only [isFresh, freeVars] at hfresh
    exact ih hfresh (by exact hnes)
  | hmultiLambda _ body ih =>
    simp only [applySubst]; congr 1
    simp only [isFresh, freeVars] at hfresh
    exact ih hfresh (by exact hnes)
  | hsubst body repl _ _ =>
    have : noExplicitSubst (.subst body repl) = false := rfl
    rw [this] at hnes; exact absurd hnes Bool.false_ne_true
  | hcollection ct elems rest ih =>
    simp only [applySubst]; congr 1
    exact list_map_eq_self fun a ha =>
      ih a ha (isFresh_collection_mem hfresh ha) (allNoExplicitSubst_mem (by exact hnes) ha)

/-- Helper: applySubst on PInput -/
theorem applySubst_input (env : SubstEnv) (n : Pattern) (body : Pattern) :
    applySubst env (.apply "PInput" [n, .lambda body]) =
      .apply "PInput" [applySubst env n, .lambda (applySubst env body)] := by
  simp only [applySubst, List.map_cons, List.map_nil]

/-- Helper: applySubst on lambda -/
theorem applySubst_lambda (env : SubstEnv) (body : Pattern) :
    applySubst env (.lambda body) = .lambda (applySubst env body) := by
  simp only [applySubst]

/-- Helper: applySubst on collection -/
theorem applySubst_collection (env : SubstEnv) (ct : CollType) (ps : List Pattern) (rest : Option String) :
    applySubst env (.collection ct ps rest) =
      .collection ct (ps.map (applySubst env)) rest := by
  simp only [applySubst]

/-- SubstEnv.find for a singleton env: finds x, misses everything else -/
theorem SubstEnv.find_extend_empty_eq {x : String} {q : Pattern} :
    (SubstEnv.extend SubstEnv.empty x q).find x = some q := by
  simp only [SubstEnv.extend, SubstEnv.empty, SubstEnv.find, List.find?, beq_self_eq_true]

theorem SubstEnv.find_extend_empty_ne {x y : String} {q : Pattern} (hne : x ≠ y) :
    (SubstEnv.extend SubstEnv.empty x q).find y = none := by
  simp only [SubstEnv.extend, SubstEnv.empty, SubstEnv.find, List.find?]
  have : (x == y) = false := beq_eq_false_iff_ne.mpr hne
  simp only [this]

/-- `subst_intro`: substitution after opening with a fresh variable equals direct opening.

    This is the key lemma connecting the typing rule (which opens with a fresh FVar)
    to the COMM rule (which opens with a concrete term).

    If `z` is fresh in `p`, then:
    `applySubst [(z, u)] (openBVar 0 (.fvar z) p) = openBVar 0 u p`

    Note: requires `noExplicitSubst p` since `applySubst` changes `.subst` structure. -/
theorem subst_intro {z : String} {u : Pattern} {p : Pattern}
    (hfresh : isFresh z p = true) (hnes : noExplicitSubst p = true) :
    applySubst (SubstEnv.extend SubstEnv.empty z u) (openBVar 0 (.fvar z) p) =
      openBVar 0 u p := by
  suffices h : ∀ k, applySubst (SubstEnv.extend SubstEnv.empty z u) (openBVar k (.fvar z) p) =
      openBVar k u p from h 0
  intro k
  induction p using Pattern.inductionOn generalizing k with
  | hbvar n =>
    simp only [openBVar]
    split
    · simp only [applySubst, SubstEnv.find_extend_empty_eq]
    · simp only [applySubst]
  | hfvar name =>
    simp only [openBVar, applySubst]
    simp only [isFresh, freeVars, List.contains_cons, List.contains_nil, Bool.or_false,
               Bool.not_eq_true'] at hfresh
    have hne : z ≠ name := fun h => by simp [h] at hfresh
    simp [SubstEnv.find_extend_empty_ne hne]
  | happly c args ih =>
    simp only [openBVar, applySubst, List.map_map]; congr 1
    exact list_map_eq_map fun a ha =>
      ih a ha (isFresh_mem_of_flatMap hfresh ha)
        (allNoExplicitSubst_mem (by exact hnes) ha) k
  | hlambda body ih =>
    simp only [openBVar, applySubst]; congr 1
    simp only [isFresh, freeVars] at hfresh
    exact ih hfresh (by exact hnes) (k + 1)
  | hmultiLambda n body ih =>
    simp only [openBVar, applySubst]; congr 1
    simp only [isFresh, freeVars] at hfresh
    exact ih hfresh (by exact hnes) (k + n)
  | hsubst body repl _ _ =>
    have : noExplicitSubst (.subst body repl) = false := rfl
    rw [this] at hnes; exact absurd hnes Bool.false_ne_true
  | hcollection ct elems rest ih =>
    simp only [openBVar, applySubst, List.map_map]; congr 1
    exact list_map_eq_map fun a ha =>
      ih a ha (isFresh_collection_mem hfresh ha)
        (allNoExplicitSubst_mem (by exact hnes) ha) k

/-! ## Freshness for FVar -/

/-- Freshness for FVar: if x is fresh in `.fvar y` then x ≠ y. -/
theorem isFresh_fvar_neq {x y : String} (h : isFresh x (.fvar y) = true) : x ≠ y := by
  unfold isFresh freeVars at h
  simp only [List.contains_cons, List.contains_nil, Bool.or_false,
             Bool.not_eq_true', beq_eq_false_iff_ne, ne_eq] at h
  exact fun heq => h heq

/-- Freshness for lambda: x fresh in `.lambda body` iff x fresh in body. -/
theorem isFresh_lambda_iff {x : String} {body : Pattern} :
    isFresh x (.lambda body) = isFresh x body := by
  simp only [isFresh, freeVars]

/-! ## Opening Preserves noExplicitSubst -/

/-- All elements of a mapped list preserve noExplicitSubst. -/
private theorem allNoExplicitSubst_map_openBVar {k : Nat} {u : Pattern} {ps : List Pattern}
    (hall : allNoExplicitSubst ps = true) (_hnes_u : noExplicitSubst u = true)
    (ih : ∀ q ∈ ps, ∀ k, noExplicitSubst q = true → noExplicitSubst (openBVar k u q) = true) :
    allNoExplicitSubst (ps.map (openBVar k u)) = true := by
  induction ps with
  | nil => rfl
  | cons a as ih_list =>
    simp only [allNoExplicitSubst, Bool.and_eq_true] at hall ⊢
    simp only [List.map_cons, allNoExplicitSubst, Bool.and_eq_true]
    exact ⟨ih a (List.mem_cons.mpr (Or.inl rfl)) k hall.1,
           ih_list hall.2 (fun q hq => ih q (List.mem_cons.mpr (Or.inr hq)))⟩

/-- Opening a subst-free pattern preserves noExplicitSubst. -/
theorem noExplicitSubst_openBVar {k : Nat} {u : Pattern} {p : Pattern}
    (hnes_p : noExplicitSubst p = true) (hnes_u : noExplicitSubst u = true) :
    noExplicitSubst (openBVar k u p) = true := by
  suffices h : ∀ (p : Pattern) (k : Nat), noExplicitSubst p = true →
      noExplicitSubst (openBVar k u p) = true from h p k hnes_p
  intro p
  induction p using Pattern.inductionOn with
  | hbvar n =>
    intro k _
    unfold openBVar; split
    · exact hnes_u
    · rfl
  | hfvar _ =>
    intro _ _; unfold openBVar; rfl
  | happly c args ih =>
    intro k hnes'
    simp only [openBVar]
    change allNoExplicitSubst (args.map (openBVar k u)) = true
    exact allNoExplicitSubst_map_openBVar hnes' hnes_u ih
  | hlambda body ih =>
    intro k hnes'
    simp only [openBVar, noExplicitSubst]
    exact ih (k + 1) hnes'
  | hmultiLambda n body ih =>
    intro k hnes'
    simp only [openBVar, noExplicitSubst]
    exact ih (k + n) hnes'
  | hsubst body repl _ _ =>
    intro _ hnes'; exact absurd hnes' Bool.false_ne_true
  | hcollection ct elems rest ih =>
    intro k hnes'
    simp only [openBVar]
    change allNoExplicitSubst (elems.map (openBVar k u)) = true
    exact allNoExplicitSubst_map_openBVar hnes' hnes_u ih

/-! ## Commutation of Substitution and Opening -/

/-- Commutation: free-variable substitution commutes with binder opening
    when the opening variable differs from the substituted variable,
    and the replacement is locally closed.

    `applySubst [(x,q)] (openBVar k (.fvar z) p) = openBVar k (.fvar z) (applySubst [(x,q)] p)`

    Conditions:
    - `z ≠ x`: the opening variable is not the one being substituted
    - `lc_at k q`: the replacement is locally closed at level k (so openBVar doesn't affect it)
    - `noExplicitSubst p`: no `.subst` nodes (both sides are well-defined) -/
theorem applySubst_openBVar_comm {x : String} {q : Pattern} {z : String}
    {p : Pattern} {k : Nat}
    (hne : z ≠ x) (hlc : lc_at k q = true)
    (hnes : noExplicitSubst p = true) :
    applySubst (SubstEnv.extend SubstEnv.empty x q) (openBVar k (.fvar z) p) =
      openBVar k (.fvar z) (applySubst (SubstEnv.extend SubstEnv.empty x q) p) := by
  -- Strengthen: prove for all k and all p with noExplicitSubst, under fixed hne
  suffices h : ∀ (p : Pattern) (k : Nat), noExplicitSubst p = true → lc_at k q = true →
      applySubst (SubstEnv.extend SubstEnv.empty x q) (openBVar k (.fvar z) p) =
        openBVar k (.fvar z) (applySubst (SubstEnv.extend SubstEnv.empty x q) p) from
    h p k hnes hlc
  intro p
  induction p using Pattern.inductionOn with
  | hbvar n =>
    intro k _ hlc'
    by_cases hnk : n = k
    · -- n = k: both sides reduce to .fvar z
      subst hnk
      simp only [openBVar, beq_self_eq_true, ite_true, applySubst,
                 SubstEnv.find_extend_empty_ne (Ne.symm hne)]
    · -- n ≠ k: both sides reduce to .bvar n
      have hnk' : (n == k) = false := beq_eq_false_iff_ne.mpr hnk
      simp only [openBVar, hnk', if_neg Bool.false_ne_true, applySubst]
  | hfvar name =>
    intro k _ hlc'
    simp only [openBVar, applySubst]
    by_cases hxn : x = name
    · rw [hxn] at *
      simp only [SubstEnv.find_extend_empty_eq]
      rw [openBVar_lc_at k (.fvar z) q hlc']
    · simp only [SubstEnv.find_extend_empty_ne hxn, openBVar]
  | happly c args ih =>
    intro k hnes' hlc'
    simp only [openBVar, applySubst, List.map_map]
    congr 1
    exact list_map_eq_map fun a ha =>
      ih a ha k (allNoExplicitSubst_mem hnes' ha) hlc'
  | hlambda body ih =>
    intro k hnes' hlc'
    simp only [openBVar, applySubst]; congr 1
    exact ih (k + 1) hnes' (lc_at_mono hlc' (Nat.le_add_right k 1))
  | hmultiLambda n body ih =>
    intro k hnes' hlc'
    simp only [openBVar, applySubst]; congr 1
    exact ih (k + n) hnes' (lc_at_mono hlc' (Nat.le_add_right k n))
  | hsubst body repl _ _ =>
    intro _ hnes' _
    exact absurd hnes' Bool.false_ne_true
  | hcollection ct elems rest ih =>
    intro k hnes' hlc'
    simp only [openBVar, applySubst, List.map_map]
    congr 1
    exact list_map_eq_map fun a ha =>
      ih a ha k (allNoExplicitSubst_mem hnes' ha) hlc'

/-! ## Backward Freshness for Singleton Substitution -/

/-- Helper: list membership from contains -/
private theorem list_mem_of_contains {x : String} {L : List String}
    (h : L.contains x = true) : x ∈ L := by
  simp only [List.contains_iff_exists_mem_beq] at h
  obtain ⟨z, hz, hzx⟩ := h
  rwa [show z = x from (beq_iff_eq.mp hzx).symm] at hz

/-- Helper: contains from list membership -/
private theorem contains_of_list_mem {x : String} {L : List String}
    (h : x ∈ L) : L.contains x = true := by
  simp only [List.contains_iff_exists_mem_beq]
  exact ⟨x, h, beq_self_eq_true x⟩

/-- Free variable z appears in applySubst [(x,q)] p when z ∈ freeVars p and z ≠ x,
    for subst-free patterns. -/
private theorem freeVars_forward_single {x : String} {q : Pattern} {z : String}
    {p : Pattern}
    (hnes : noExplicitSubst p = true)
    (hz_in : z ∈ freeVars p) (hne : z ≠ x) :
    z ∈ freeVars (applySubst (SubstEnv.extend SubstEnv.empty x q) p) := by
  induction p using Pattern.inductionOn with
  | hbvar _ =>
    simp only [freeVars] at hz_in
    cases hz_in
  | hfvar name =>
    simp only [freeVars, List.mem_singleton] at hz_in
    subst hz_in
    simp only [applySubst, SubstEnv.find_extend_empty_ne (Ne.symm hne), freeVars,
               List.mem_singleton]
  | happly c args ih =>
    simp only [freeVars, List.mem_flatMap] at hz_in
    obtain ⟨a, ha, hz_a⟩ := hz_in
    show z ∈ freeVars (applySubst _ (.apply c args))
    simp only [applySubst, freeVars, List.mem_flatMap]
    exact ⟨applySubst _ a, List.mem_map.mpr ⟨a, ha, rfl⟩,
           ih a ha (allNoExplicitSubst_mem hnes ha) hz_a⟩
  | hlambda body ih =>
    simp only [freeVars] at hz_in
    show z ∈ freeVars (applySubst _ (.lambda body))
    simp only [applySubst, freeVars]
    exact ih hnes hz_in
  | hmultiLambda n body ih =>
    simp only [freeVars] at hz_in
    show z ∈ freeVars (applySubst _ (.multiLambda n body))
    simp only [applySubst, freeVars]
    exact ih hnes hz_in
  | hsubst body repl _ _ => exact absurd hnes Bool.false_ne_true
  | hcollection ct elems rest ih =>
    simp only [freeVars, List.mem_flatMap] at hz_in
    obtain ⟨a, ha, hz_a⟩ := hz_in
    show z ∈ freeVars (applySubst _ (.collection ct elems rest))
    simp only [applySubst, freeVars, List.mem_flatMap]
    exact ⟨applySubst _ a, List.mem_map.mpr ⟨a, ha, rfl⟩,
           ih a ha (allNoExplicitSubst_mem hnes ha) hz_a⟩

/-- Backward freshness for singleton substitution: if z is fresh in `applySubst [(x,q)] p`,
    z ≠ x, and p has no explicit subst nodes, then z is fresh in p. -/
theorem isFresh_of_isFresh_applySubst_single {x : String} {q : Pattern} {z : String}
    {p : Pattern}
    (hnes : noExplicitSubst p = true)
    (hfresh : isFresh z (applySubst (SubstEnv.extend SubstEnv.empty x q) p) = true)
    (hne : z ≠ x) :
    isFresh z p = true := by
  simp only [isFresh, Bool.not_eq_true'] at hfresh ⊢
  rw [Bool.eq_false_iff] at hfresh ⊢
  intro hz_in
  exact hfresh (contains_of_list_mem
    (freeVars_forward_single hnes (list_mem_of_contains hz_in) hne))

/-- Forward freshness for singleton substitution: if z is fresh in p and fresh in q,
    then z is fresh in applySubst [(x,q)] p (for subst-free p). -/
theorem isFresh_applySubst_single {x : String} {q : Pattern} {z : String}
    {p : Pattern}
    (hnes : noExplicitSubst p = true)
    (hfresh_p : isFresh z p = true) (hfresh_q : isFresh z q = true) :
    isFresh z (applySubst (SubstEnv.extend SubstEnv.empty x q) p) = true := by
  induction p using Pattern.inductionOn with
  | hbvar _ => simp [applySubst, isFresh, freeVars]
  | hfvar name =>
    simp only [applySubst]
    by_cases hxn : x = name
    · simp only [SubstEnv.extend, SubstEnv.empty, SubstEnv.find, List.find?,
                 beq_iff_eq.mpr hxn]
      exact hfresh_q
    · simp only [SubstEnv.find_extend_empty_ne hxn]
      exact hfresh_p
  | happly c args ih =>
    have hfresh_apply : isFresh z (.apply c args) = true := hfresh_p
    simp only [applySubst, isFresh, freeVars, Bool.not_eq_true']
    rw [Bool.eq_false_iff]
    intro hz_in
    have hz_mem := list_mem_of_contains hz_in
    simp only [List.mem_flatMap] at hz_mem
    obtain ⟨mapped, hmapped, hz_mapped⟩ := hz_mem
    rw [List.mem_map] at hmapped
    obtain ⟨a, ha, rfl⟩ := hmapped
    have ha_nes := allNoExplicitSubst_mem hnes ha
    have ha_fresh : isFresh z a = true := isFresh_mem_of_flatMap hfresh_apply ha
    have := ih a ha ha_nes ha_fresh
    simp only [isFresh, Bool.not_eq_true'] at this
    exact absurd (contains_of_list_mem hz_mapped) (Bool.eq_false_iff.mp this)
  | hlambda body ih =>
    simp only [applySubst, isFresh, freeVars] at *
    exact ih hnes hfresh_p
  | hmultiLambda _ body ih =>
    simp only [applySubst, isFresh, freeVars] at *
    exact ih hnes hfresh_p
  | hsubst body repl _ _ => exact absurd hnes Bool.false_ne_true
  | hcollection ct elems rest ih =>
    have hfresh_coll : isFresh z (.collection ct elems rest) = true := hfresh_p
    simp only [applySubst, isFresh, freeVars, Bool.not_eq_true']
    rw [Bool.eq_false_iff]
    intro hz_in
    have hz_mem := list_mem_of_contains hz_in
    simp only [List.mem_flatMap] at hz_mem
    obtain ⟨mapped, hmapped, hz_mapped⟩ := hz_mem
    rw [List.mem_map] at hmapped
    obtain ⟨a, ha, rfl⟩ := hmapped
    have ha_nes := allNoExplicitSubst_mem hnes ha
    have ha_fresh : isFresh z a = true := isFresh_collection_mem hfresh_coll ha
    have := ih a ha ha_nes ha_fresh
    simp only [isFresh, Bool.not_eq_true'] at this
    exact absurd (contains_of_list_mem hz_mapped) (Bool.eq_false_iff.mp this)

/-! ## Reverse: noExplicitSubst from opened pattern -/

/-- If `openBVar k u p` is subst-free, then `p` is subst-free.

    openBVar only replaces `.bvar` nodes with `u`. It never introduces `.subst` nodes.
    So if the result has no subst nodes, the original didn't either. -/
theorem noExplicitSubst_of_openBVar {k : Nat} {u : Pattern} {p : Pattern}
    (h : noExplicitSubst (openBVar k u p) = true) : noExplicitSubst p = true := by
  induction p using Pattern.inductionOn generalizing k with
  | hbvar _ => rfl
  | hfvar _ => rfl
  | happly c args ih =>
    simp only [openBVar] at h
    change allNoExplicitSubst (args.map (openBVar k u)) = true at h
    show allNoExplicitSubst args = true
    induction args with
    | nil => rfl
    | cons a as ih_list =>
      simp only [List.map_cons, allNoExplicitSubst, Bool.and_eq_true] at h ⊢
      exact ⟨ih a (List.mem_cons.mpr (Or.inl rfl)) h.1,
             ih_list (fun q hq => ih q (List.mem_cons.mpr (Or.inr hq))) h.2⟩
  | hlambda body ih =>
    simp only [openBVar, noExplicitSubst] at h ⊢
    exact ih h
  | hmultiLambda n body ih =>
    simp only [openBVar, noExplicitSubst] at h ⊢
    exact ih h
  | hsubst body repl _ _ =>
    -- openBVar k u (.subst body repl) = .subst ... ..., noExplicitSubst of .subst = false
    have : noExplicitSubst (openBVar k u (.subst body repl)) = false := by
      simp only [openBVar, noExplicitSubst]
    rw [this] at h
    exact absurd h Bool.false_ne_true
  | hcollection ct elems rest ih =>
    simp only [openBVar] at h
    change allNoExplicitSubst (elems.map (openBVar k u)) = true at h
    show allNoExplicitSubst elems = true
    induction elems with
    | nil => rfl
    | cons a as ih_list =>
      simp only [List.map_cons, allNoExplicitSubst, Bool.and_eq_true] at h ⊢
      exact ⟨ih a (List.mem_cons.mpr (Or.inl rfl)) h.1,
             ih_list (fun q hq => ih q (List.mem_cons.mpr (Or.inr hq))) h.2⟩

end Mettapedia.OSLF.MeTTaIL.Substitution
