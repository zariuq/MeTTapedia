import Mettapedia.GSLT.LanguageDef.NativeWord64
import Mettapedia.Languages.VibeITP.Spec.Basic
import Mathlib.Tactic

/-!
Unsigned native term-cache accumulation versus independent recursive metadata.
Argument storage, ownership and actual function execution are separate bridges.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.VibeITP.Native.TermMetadata

open Spec

theorem depth_wellFormed (signature : Sig) (term : Term)
    (formed : WellFormed signature term = true) : depth signature term < wordBound := by
  apply Term.rec (motive_1 := fun term => WellFormed signature term = true →
      depth signature term < wordBound)
    (motive_2 := fun terms => WellFormedList signature terms = true →
      ∀ symbol index, depthArgs signature symbol index terms < wordBound) _ _ _ _ _ term formed
  · intro index valid
    simpa only [WellFormed, depth, decide_eq_true_eq] using valid
  · intro bytes _
    exact Nat.two_pow_pos _
  · intro symbol terms children valid
    cases declared : signature symbol with
    | none => simp [WellFormed, declared] at valid
    | some info =>
      have shape : terms.length = info.arity ∧ WellFormedList signature terms = true := by
        simpa only [WellFormed, declared, Bool.and_eq_true, decide_eq_true_eq] using valid
      have arguments : WellFormedList signature terms = true := shape.2
      exact children arguments symbol 0
  · intro _ symbol index
    exact Nat.two_pow_pos _
  · intro term terms child tail valid symbol index
    have formed : WellFormed signature term = true ∧ WellFormedList signature terms = true := by
      simpa only [WellFormedList, Bool.and_eq_true] using valid
    exact max_lt (Nat.lt_of_le_of_lt (Nat.sub_le _ _) (child formed.1))
      (tail formed.2 symbol (index + 1))

structure Cache where
  depth : BitVec 64
  free : Bool
  deriving DecidableEq, Repr

structure Argument where
  depth : BitVec 64
  binders : BitVec 64
  free : Bool
  deriving DecidableEq, Repr

def push (cache : Cache) (argument : Argument) : Cache :=
  { depth := if argument.binders < argument.depth ∧ cache.depth < argument.depth - argument.binders
      then argument.depth - argument.binders else cache.depth
    free := cache.free || argument.free }

def scan : Cache → List Argument → Cache
  | cache, [] => cache
  | cache, argument :: rest => scan (push cache argument) rest

def maximum : List Argument → Nat
  | [] => 0
  | argument :: rest => max (argument.depth.toNat - argument.binders.toNat) (maximum rest)

def anyFree : List Argument → Bool
  | [] => false
  | argument :: rest => argument.free || anyFree rest

theorem subtraction_no_borrow (left right : BitVec 64) (ordered : right ≤ left) :
    (left - right).toNat = left.toNat - right.toNat := by
  apply BitVec.toNat_sub_of_not_usubOverflow
  simp only [BitVec.usubOverflow, decide_eq_true_eq, Nat.not_lt]
  exact (BitVec.le_def.mp ordered)

theorem push_depth (cache : Cache) (argument : Argument) :
    (push cache argument).depth.toNat =
      max cache.depth.toNat (argument.depth.toNat - argument.binders.toNat) := by
  unfold push
  by_cases contributes : argument.binders < argument.depth
  · have subtraction := subtraction_no_borrow argument.depth argument.binders (BitVec.le_of_lt contributes)
    by_cases bigger : cache.depth < argument.depth - argument.binders
    · simp only [contributes, bigger, and_self, if_true, subtraction]
      rw [max_eq_right]
      exact Nat.le_of_lt (by simpa only [BitVec.lt_def, subtraction] using bigger)
    · simp only [contributes, bigger, and_false, if_false]
      rw [max_eq_left]
      simpa only [BitVec.lt_def, subtraction, not_lt] using bigger
  · have bounded : argument.depth.toNat ≤ argument.binders.toNat := by
      simpa only [BitVec.lt_def, not_lt] using contributes
    simp only [contributes, false_and, if_false, Nat.sub_eq_zero_of_le bounded, max_zero]

theorem push_free (cache : Cache) (argument : Argument) :
    (push cache argument).free = (cache.free || argument.free) := rfl

theorem scan_depth (cache : Cache) (arguments : List Argument) :
    (scan cache arguments).depth.toNat = max cache.depth.toNat (maximum arguments) := by
  induction arguments generalizing cache with
  | nil => simp [scan, maximum]
  | cons argument rest ih =>
    rw [scan, ih, push_depth, maximum, max_assoc]

theorem scan_free (cache : Cache) (arguments : List Argument) :
    (scan cache arguments).free = (cache.free || anyFree arguments) := by
  induction arguments generalizing cache with
  | nil => simp [scan, anyFree]
  | cons argument rest ih =>
    rw [scan, ih, push_free, anyFree, Bool.or_assoc]

def ofTerms (signature : Sig) (symbol : SymId) : Nat → List Term → List Argument
  | _, [] => []
  | index, term :: rest =>
    ⟨BitVec.ofNat 64 (depth signature term), BitVec.ofNat 64 (binderAt signature symbol index),
      hasFvar signature term⟩ :: ofTerms signature symbol (index + 1) rest

theorem maximum_ofTerms (signature : Sig) (symbol : SymId) (index : Nat) (terms : List Term)
    (formed : WellFormedList signature terms = true)
    (binderBounds : ∀ offset < terms.length, binderAt signature symbol (index + offset) < wordBound) :
    maximum (ofTerms signature symbol index terms) = depthArgs signature symbol index terms := by
  induction terms generalizing index with
  | nil => rfl
  | cons term rest ih =>
    have valid : WellFormed signature term = true ∧ WellFormedList signature rest = true := by
      simpa only [WellFormedList, Bool.and_eq_true] using formed
    have headBound : binderAt signature symbol index < wordBound := by
      have first := binderBounds 0 (Nat.zero_lt_succ rest.length)
      simpa only [Nat.add_zero] using first
    have tailBounds : ∀ offset < rest.length, binderAt signature symbol (index + 1 + offset) < wordBound := by
      intro offset bound
      have next := binderBounds (offset + 1) (Nat.succ_lt_succ bound)
      simpa only [Nat.add_assoc, Nat.add_comm 1] using next
    have childBound : depth signature term < 2 ^ 64 := depth_wellFormed signature term valid.1
    change binderAt signature symbol index < 2 ^ 64 at headBound
    simp only [ofTerms, maximum, depthArgs, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt childBound, Nat.mod_eq_of_lt headBound]
    rw [ih (index + 1) valid.2 tailBounds]

theorem anyFree_ofTerms (signature : Sig) (symbol : SymId) (index : Nat) (terms : List Term) :
    anyFree (ofTerms signature symbol index terms) = hasFvarList signature terms := by
  induction terms generalizing index with
  | nil => rfl
  | cons term rest ih => simp only [ofTerms, anyFree, hasFvarList, ih]

theorem application_cache_correct (signature : Sig) (symbol : SymId) (terms : List Term)
    (formed : WellFormedList signature terms = true)
    (binderBounds : ∀ index < terms.length, binderAt signature symbol index < wordBound) :
    let cache := scan ⟨0, isFvarSym signature symbol⟩ (ofTerms signature symbol 0 terms)
    cache.depth.toNat = depth signature (.app symbol terms) ∧
      cache.free = hasFvar signature (.app symbol terms) := by
  dsimp only
  constructor
  · rw [scan_depth, maximum_ofTerms signature symbol 0 terms formed (by simpa using binderBounds)]
    rfl
  · rw [scan_free, anyFree_ofTerms]
    rfl

theorem shallower_than_binder_does_not_underflow : push ⟨0, false⟩ ⟨5, 9, false⟩ = ⟨0, false⟩ := rfl

theorem deeper_than_binder_contributes : push ⟨0, false⟩ ⟨5, 2, false⟩ = ⟨3, false⟩ := rfl

theorem free_flag_survives_zero_contribution : push ⟨7, false⟩ ⟨1, 2, true⟩ = ⟨7, true⟩ := rfl

end Mettapedia.Languages.VibeITP.Native.TermMetadata
