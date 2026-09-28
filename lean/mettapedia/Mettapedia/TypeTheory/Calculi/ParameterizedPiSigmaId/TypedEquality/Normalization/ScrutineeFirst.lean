import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Structural
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.PatternTelescopes

/-!
# Telescopes of closed types and the renamings that reorder them

A definition by structural recursion whose recursive calls change an
argument before the scrutinee is admitted through its scrutinee-first form:
the same equations with the scrutinee written first and the other arguments
in their order. For a telescope of closed types, that reordering is a
renaming of variables, and a renaming between two such telescopes is a
context renaming whenever the types agree along it, so typing and typed
equality transport along it. This module builds the telescope, the renaming
that moves the entry at index `k` to the front or to the back, the exchange
of adjacent independent entries, the lookups of the contexts `ofEntries` and
`extendEntries` build from closed entries, and the lifting of a context
renaming under further entries, which carries it into the equation contexts
with their recursive hypotheses.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Normalization

open TelescopeAbstraction (applyClosed)

variable {Head : Type}

/-! ## Telescopes of closed types -/

/-- The context whose entry at de Bruijn index `i` is the closed type `F i`. -/
def closedTele : {n : Nat} → (Fin n → Tm Head 0) → Ctx Head n
  | 0, _ => .nil
  | _ + 1, F => .snoc (closedTele fun j => F j.succ) (liftClosed (F 0))

@[simp] theorem closedTele_lookup {n : Nat} (F : Fin n → Tm Head 0) (i : Fin n) :
    Ctx.lookup (closedTele F) i = liftClosed (F i) := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
      refine Fin.cases ?_ (fun j => ?_) i
      · show Presentation.rename wk (liftClosed (F 0)) = liftClosed (F 0)
        exact rename_liftClosed wk (F 0)
      · show Presentation.rename wk (Ctx.lookup (closedTele fun j => F j.succ) j) =
          liftClosed (F j.succ)
        rw [ih (fun j => F j.succ) j]
        exact rename_liftClosed wk (F j.succ)

/-- A renaming between telescopes of closed types is a context renaming when
the types agree along it. -/
theorem ctxRen_closedTele {n m : Nat} {F : Fin n → Tm Head 0} {G : Fin m → Tm Head 0}
    (ρ : Ren n m) (agree : ∀ i, G (ρ i) = F i) : CtxRen (closedTele F) (closedTele G) ρ := by
  intro i
  rw [closedTele_lookup, closedTele_lookup, agree i, rename_liftClosed]

/-! ## Moving one entry to the front -/

/-- The renaming that sends the index `k` to `0`, the indices below `k` one up,
and the others to themselves. -/
def toFront {n : Nat} (k : Fin n) : Ren n n := fun i =>
  if i.val = k.val then ⟨0, k.pos⟩
  else if h : i.val < k.val then ⟨i.val + 1, Nat.lt_of_le_of_lt h k.isLt⟩
  else i

/-- The inverse: `0` back to `k`, the indices from `1` to `k` one down, and the
others to themselves. -/
def fromFront {n : Nat} (k : Fin n) : Ren n n := fun j =>
  if j.val = 0 then k
  else if j.val ≤ k.val then ⟨j.val - 1, Nat.lt_of_le_of_lt (Nat.sub_le _ _) j.isLt⟩
  else j

theorem fromFront_toFront {n : Nat} (k i : Fin n) : fromFront k (toFront k i) = i := by
  apply Fin.ext
  by_cases h₁ : i.val = k.val
  · simp [toFront, fromFront, h₁]
  · by_cases h₂ : i.val < k.val
    · have h₃ : i.val + 1 ≠ 0 := by omega
      have h₄ : i.val + 1 ≤ k.val := by omega
      simp [toFront, fromFront, h₁, h₂, h₄]
    · have h₃ : i.val ≠ 0 := by omega
      have h₄ : ¬ i.val ≤ k.val := by omega
      simp [toFront, fromFront, h₁, h₂, h₃, h₄]

theorem toFront_fromFront {n : Nat} (k j : Fin n) : toFront k (fromFront k j) = j := by
  apply Fin.ext
  by_cases h₁ : j.val = 0
  · simp [toFront, fromFront, h₁]
  · by_cases h₂ : j.val ≤ k.val
    · have h₃ : j.val - 1 ≠ k.val := by omega
      have h₄ : j.val - 1 < k.val := by omega
      simp [toFront, fromFront, h₁, h₂, h₃, h₄]
      omega
    · have h₃ : j.val ≠ k.val := by omega
      have h₄ : ¬ j.val < k.val := by omega
      simp [toFront, fromFront, h₁, h₂, h₃, h₄]

/-- The telescope with the entry at `k` moved to the front. -/
def frontTele {n : Nat} (k : Fin n) (F : Fin n → Tm Head 0) : Ctx Head n :=
  closedTele (F ∘ fromFront k)

theorem ctxRen_toFront {n : Nat} (k : Fin n) (F : Fin n → Tm Head 0) :
    CtxRen (closedTele F) (frontTele k F) (toFront k) :=
  ctxRen_closedTele (toFront k) fun i => by
    show F (fromFront k (toFront k i)) = F i
    rw [fromFront_toFront]

theorem ctxRen_fromFront {n : Nat} (k : Fin n) (F : Fin n → Tm Head 0) :
    CtxRen (frontTele k F) (closedTele F) (fromFront k) :=
  ctxRen_closedTele (fromFront k) fun _ => rfl

/-! ## Transport -/

variable {R : Rules Head}

/-- A typing in a telescope of closed types transports to the telescope with
the entry at `k` in front. -/
theorem Typed.rename_toFront {n : Nat} (k : Fin n) {F : Fin n → Tm Head 0} {t A : Tm Head n}
    (typing : Typed R (closedTele F) t A) :
    Typed R (frontTele k F) (Presentation.rename (Normalization.toFront k) t)
      (Presentation.rename (Normalization.toFront k) A) :=
  typing.rename (ctxRen_toFront k F)

theorem Typed.rename_fromFront {n : Nat} (k : Fin n) {F : Fin n → Tm Head 0} {t A : Tm Head n}
    (typing : Typed R (frontTele k F) t A) :
    Typed R (closedTele F) (Presentation.rename (Normalization.fromFront k) t)
      (Presentation.rename (Normalization.fromFront k) A) :=
  typing.rename (ctxRen_fromFront k F)

theorem Equal.rename_toFront {n : Nat} (k : Fin n) {F : Fin n → Tm Head 0} {a b A : Tm Head n}
    (equal : Equal R (closedTele F) a b A) :
    Equal R (frontTele k F) (Presentation.rename (Normalization.toFront k) a)
      (Presentation.rename (Normalization.toFront k) b)
      (Presentation.rename (Normalization.toFront k) A) :=
  equal.rename (ctxRen_toFront k F)

/-- Renaming there and back is the identity on terms. -/
theorem rename_fromFront_toFront {n : Nat} (k : Fin n) (t : Tm Head n) :
    Presentation.rename (fromFront k) (Presentation.rename (toFront k) t) = t := by
  rw [rename_comp]
  have h : (fun i => fromFront k (toFront k i)) = (idRen : Ren n n) := by
    funext i
    exact fromFront_toFront k i
  rw [h, rename_id]

theorem rename_toFront_fromFront {n : Nat} (k : Fin n) (t : Tm Head n) :
    Presentation.rename (toFront k) (Presentation.rename (fromFront k) t) = t := by
  rw [rename_comp]
  have h : (fun j => toFront k (fromFront k j)) = (idRen : Ren n n) := by
    funext j
    exact toFront_fromFront k j
  rw [h, rename_id]

/-! ## Moving one entry to the back

In telescope order the scrutinee-first form lists the scrutinee first, which
in de Bruijn terms makes it the oldest entry, at the highest index. -/

/-- The renaming that sends the index `k` to `n - 1`, the indices above `k`
one down, and the others to themselves. -/
def toBack {n : Nat} (k : Fin n) : Ren n n := fun i =>
  if i.val = k.val then ⟨n - 1, Nat.sub_one_lt (Nat.ne_of_gt k.pos)⟩
  else if k.val < i.val then ⟨i.val - 1, Nat.lt_of_le_of_lt (Nat.sub_le _ _) i.isLt⟩
  else i

/-- The inverse: `n - 1` back to `k`, the indices from `k` to `n - 2` one up,
and the others to themselves. -/
def fromBack {n : Nat} (k : Fin n) : Ren n n := fun j =>
  if h₀ : j.val = n - 1 then k
  else if h : k.val ≤ j.val then ⟨j.val + 1, by have := j.isLt; omega⟩
  else j

theorem fromBack_toBack {n : Nat} (k i : Fin n) : fromBack k (toBack k i) = i := by
  apply Fin.ext
  by_cases h₁ : i.val = k.val
  · simp [toBack, fromBack, h₁]
  · by_cases h₂ : k.val < i.val
    · have h₃ : i.val - 1 ≠ n - 1 := by omega
      have h₄ : k.val ≤ i.val - 1 := by omega
      simp [toBack, fromBack, h₁, h₂, h₃, h₄]
      omega
    · have h₃ : i.val ≠ n - 1 := by omega
      have h₄ : ¬ k.val ≤ i.val := by omega
      simp [toBack, fromBack, h₁, h₂, h₃, h₄]

theorem toBack_fromBack {n : Nat} (k j : Fin n) : toBack k (fromBack k j) = j := by
  apply Fin.ext
  by_cases h₁ : j.val = n - 1
  · simp [toBack, fromBack, h₁]
  · by_cases h₂ : k.val ≤ j.val
    · have h₃ : j.val + 1 ≠ k.val := by omega
      have h₄ : k.val < j.val + 1 := by omega
      simp [toBack, fromBack, h₁, h₂, h₃, h₄]
    · have h₃ : j.val ≠ k.val := by omega
      have h₄ : ¬ k.val < j.val := by omega
      simp [toBack, fromBack, h₁, h₂, h₃, h₄]

/-- The telescope with the entry at `k` moved to the back. -/
def backTele {n : Nat} (k : Fin n) (F : Fin n → Tm Head 0) : Ctx Head n :=
  closedTele (F ∘ fromBack k)

theorem ctxRen_toBack {n : Nat} (k : Fin n) (F : Fin n → Tm Head 0) :
    CtxRen (closedTele F) (backTele k F) (toBack k) :=
  ctxRen_closedTele (toBack k) fun i => by
    show F (fromBack k (toBack k i)) = F i
    rw [fromBack_toBack]

theorem Typed.rename_toBack {n : Nat} (k : Fin n) {F : Fin n → Tm Head 0} {t A : Tm Head n}
    (typing : Typed R (closedTele F) t A) :
    Typed R (backTele k F) (Presentation.rename (Normalization.toBack k) t)
      (Presentation.rename (Normalization.toBack k) A) :=
  typing.rename (ctxRen_toBack k F)

theorem Equal.rename_toBack {n : Nat} (k : Fin n) {F : Fin n → Tm Head 0} {a b A : Tm Head n}
    (equal : Equal R (closedTele F) a b A) :
    Equal R (backTele k F) (Presentation.rename (Normalization.toBack k) a)
      (Presentation.rename (Normalization.toBack k) b)
      (Presentation.rename (Normalization.toBack k) A) :=
  equal.rename (ctxRen_toBack k F)

/-! ## Exchange of adjacent independent entries

For any context, two adjacent entries can be exchanged when the later one
does not mention the earlier: `Γ, A, B` with `B` a type of `Γ` becomes
`Γ, B, A`. This is the step that moves an entry through a dependent
telescope. -/

/-- The renaming exchanging the indices `0` and `1`. -/
def swap01 {n : Nat} : Ren (n + 2) (n + 2) := fun i =>
  if i.val = 0 then ⟨1, by omega⟩ else if i.val = 1 then ⟨0, by omega⟩ else i

theorem swap01_zero {n : Nat} : (swap01 (0 : Fin (n + 2))) = Fin.succ 0 := rfl

theorem swap01_one {n : Nat} : swap01 (Fin.succ (0 : Fin (n + 1))) = 0 := rfl

theorem swap01_succ_succ {n : Nat} (j : Fin n) :
    swap01 (Fin.succ (Fin.succ j)) = Fin.succ (Fin.succ j) := rfl

theorem swap01_wk_wk {n : Nat} :
    (fun j : Fin n => swap01 (wk (wk j))) = fun j => wk (wk j) := by
  funext j
  exact swap01_succ_succ j

theorem ctxRen_exchange {n : Nat} (Γ : Ctx Head n) (A B : Tm Head n) :
    CtxRen (.snoc (.snoc Γ A) (Presentation.rename wk B))
      (.snoc (.snoc Γ B) (Presentation.rename wk A)) swap01 := by
  intro i
  refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun j' => ?_) j) i
  · rw [swap01_zero]
    show Presentation.rename wk (Presentation.rename wk B) =
      Presentation.rename swap01 (Presentation.rename wk (Presentation.rename wk B))
    rw [rename_comp, rename_comp, swap01_wk_wk]
  · rw [swap01_one]
    show Presentation.rename wk (Presentation.rename wk A) =
      Presentation.rename swap01 (Presentation.rename wk (Presentation.rename wk A))
    rw [rename_comp, rename_comp, swap01_wk_wk]
  · rw [swap01_succ_succ]
    show Presentation.rename wk (Presentation.rename wk (Ctx.lookup Γ j')) =
      Presentation.rename swap01 (Presentation.rename wk (Presentation.rename wk (Ctx.lookup Γ j')))
    rw [rename_comp, rename_comp, swap01_wk_wk]

/-- Typing transports across an exchange of adjacent independent entries. -/
theorem Typed.exchange {n : Nat} {Γ : Ctx Head n} {A B : Tm Head n} {t T : Tm Head (n + 2)}
    (typing : Typed R (.snoc (.snoc Γ A) (Presentation.rename wk B)) t T) :
    Typed R (.snoc (.snoc Γ B) (Presentation.rename wk A))
      (Presentation.rename swap01 t) (Presentation.rename swap01 T) :=
  typing.rename (ctxRen_exchange Γ A B)

theorem Equal.exchange {n : Nat} {Γ : Ctx Head n} {A B : Tm Head n} {a b T : Tm Head (n + 2)}
    (equal : Equal R (.snoc (.snoc Γ A) (Presentation.rename wk B)) a b T) :
    Equal R (.snoc (.snoc Γ B) (Presentation.rename wk A))
      (Presentation.rename swap01 a) (Presentation.rename swap01 b)
      (Presentation.rename swap01 T) :=
  equal.rename (ctxRen_exchange Γ A B)

/-! ## Contexts of closed types, by their lookups

The equation contexts of a recursive definition are built by `ofEntries` and
`extendEntries`. When the entries are closed, the lookups are the closed types
at the reversed positions, and a renaming between two such contexts is a
context renaming whenever the types agree along it. Stating this by lookups
rather than by an equation between contexts avoids reindexing the contexts
themselves. -/

/-- The lookups of a telescope of closed entries: the entry at position `j`
sits at de Bruijn index `n - 1 - j`. -/
theorem ofEntries_lookup_closed (G : Nat → Tm Head 0) :
    ∀ (n : Nat) (i : Fin n),
      Ctx.lookup (ofEntries (fun j => liftClosed (G j)) n) i = liftClosed (G (n - 1 - i.val))
  | 0, i => Fin.elim0 i
  | n + 1, i => by
      refine Fin.cases ?_ (fun j => ?_) i
      · show Presentation.rename wk (liftClosed (G n)) = _
        simp
      · show Presentation.rename wk (Ctx.lookup (ofEntries (fun j => liftClosed (G j)) n) j) = _
        rw [ofEntries_lookup_closed G n j, rename_liftClosed, Fin.val_succ,
          show n + 1 - 1 - (j.val + 1) = n - 1 - j.val by omega]

/-- The lookups of a context of closed types extended by closed entries: the
last `d` indices read the entries in reverse, the others the context. -/
theorem extendEntries_lookup_closed {n : Nat} {Γ : Ctx Head n} {F : Fin n → Tm Head 0}
    (closed : ∀ i, Ctx.lookup Γ i = liftClosed (F i)) (G : Nat → Tm Head 0) :
    ∀ (d : Nat) (i : Fin (n + d)),
      Ctx.lookup (extendEntries Γ (fun j => liftClosed (G j)) d) i =
        liftClosed (if h : i.val < d then G (d - 1 - i.val)
          else F ⟨i.val - d, by have := i.isLt; omega⟩)
  | 0, i => by
      rw [show extendEntries Γ (fun j => liftClosed (G j)) 0 = Γ from rfl, closed i]
      simp
  | d + 1, i => by
      refine Fin.cases ?_ (fun j => ?_) i
      · show Presentation.rename wk (liftClosed (G d)) = _
        simp
      · show Presentation.rename wk
          (Ctx.lookup (extendEntries Γ (fun j => liftClosed (G j)) d) j) = _
        rw [extendEntries_lookup_closed closed G d j, rename_liftClosed]
        by_cases h : j.val < d
        · rw [dif_pos h, dif_pos (by rw [Fin.val_succ]; omega), Fin.val_succ,
            show d + 1 - 1 - (j.val + 1) = d - 1 - j.val by omega]
        · rw [dif_neg h, dif_neg (by rw [Fin.val_succ]; omega)]
          exact congrArg (fun x => liftClosed (F x))
            (Fin.ext (by show j.val - d = (Fin.succ j).val - (d + 1); rw [Fin.val_succ]; omega))

/-- A renaming between contexts of closed types is a context renaming when
the types agree along it. -/
theorem ctxRen_of_closed {n m : Nat} {Γ : Ctx Head n} {Δ : Ctx Head m}
    {F : Fin n → Tm Head 0} {G : Fin m → Tm Head 0}
    (closedΓ : ∀ i, Ctx.lookup Γ i = liftClosed (F i))
    (closedΔ : ∀ j, Ctx.lookup Δ j = liftClosed (G j))
    (ρ : Ren n m) (agree : ∀ i, G (ρ i) = F i) : CtxRen Γ Δ ρ := by
  intro i
  rw [closedΓ, closedΔ, agree i, rename_liftClosed]

/-! ## Lifting a context renaming under further entries

The equation contexts extend a telescope by entries that are not closed: the
recursive hypotheses mention the fields. A context renaming lifts under such
an extension entry by entry, each entry renamed under the renaming lifted so
far. -/

/-- The renaming `ρ` lifted under `j` binders. -/
def liftRenN {n m : Nat} (ρ : Ren n m) : (j : Nat) → Ren (n + j) (m + j)
  | 0 => ρ
  | j + 1 => liftRen (liftRenN ρ j)

theorem ctxRen_extendEntries {n m : Nat} {Γ : Ctx Head n} {Δ : Ctx Head m} {ρ : Ren n m}
    (compatible : CtxRen Γ Δ ρ) (entry : (j : Nat) → Tm Head (n + j)) :
    ∀ (d : Nat), CtxRen (extendEntries Γ entry d)
      (extendEntries Δ (fun j => Presentation.rename (liftRenN ρ j) (entry j)) d)
      (liftRenN ρ d)
  | 0 => compatible
  | d + 1 => (ctxRen_extendEntries compatible entry d).snoc (entry d)

/-- Typing transports along a context renaming lifted under further entries. -/
theorem Typed.rename_extendEntries {n m : Nat} {Γ : Ctx Head n} {Δ : Ctx Head m} {ρ : Ren n m}
    (compatible : CtxRen Γ Δ ρ) (entry : (j : Nat) → Tm Head (n + j)) (d : Nat)
    {t A : Tm Head (n + d)} (typing : Typed R (extendEntries Γ entry d) t A) :
    Typed R (extendEntries Δ (fun j => Presentation.rename (liftRenN ρ j) (entry j)) d)
      (Presentation.rename (liftRenN ρ d) t) (Presentation.rename (liftRenN ρ d) A) :=
  typing.rename (ctxRen_extendEntries compatible entry d)

theorem Equal.rename_extendEntries {n m : Nat} {Γ : Ctx Head n} {Δ : Ctx Head m} {ρ : Ren n m}
    (compatible : CtxRen Γ Δ ρ) (entry : (j : Nat) → Tm Head (n + j)) (d : Nat)
    {a b A : Tm Head (n + d)} (equal : Equal R (extendEntries Γ entry d) a b A) :
    Equal R (extendEntries Δ (fun j => Presentation.rename (liftRenN ρ j) (entry j)) d)
      (Presentation.rename (liftRenN ρ d) a) (Presentation.rename (liftRenN ρ d) b)
      (Presentation.rename (liftRenN ρ d) A) :=
  equal.rename (ctxRen_extendEntries compatible entry d)

/-! ## The scrutinee-first form of a closed telescope

A definition by recursion on the argument at position `s` of a telescope of
closed types `F 0, …, F s, …` has the scrutinee-first form on the telescope
`F s, F 0, …, F (s-1), F (s+1), …`. In the equation context of a constructor,
the fields of the pattern then sit before the prefix instead of after it,
and the later entries keep their place. That move of the field block is a
renaming, and a context renaming between the two equation contexts. -/

/-- The scrutinee-first telescope: the entry at position `s` first, the
others in their order. -/
def scrutineeFirst (F : Nat → Tm Head 0) (s : Nat) : Nat → Tm Head 0
  | 0 => F s
  | j + 1 => if j < s then F j else F (j + 1)

theorem scrutineeFirst_later (F : Nat → Tm Head 0) (s j : Nat) :
    scrutineeFirst F s (0 + 1 + j) = if j < s then F j else F (j + 1) := by
  rw [Nat.zero_add, Nat.add_comm]
  rfl

/-- The renaming from the equation context of the authored form to that of
the scrutinee-first form: the `d` later entries stay, the `a` fields move
past the `s` prefix entries, and the prefix moves behind the fields. -/
def blockMove (s a d : Nat) : Ren (s + a + d) (0 + a + (s + d)) := fun i =>
  if h : i.val < d then ⟨i.val, by omega⟩
  else if h' : i.val < d + a then ⟨i.val + s, by omega⟩
  else ⟨i.val - a, by omega⟩

/-- The equation context of a closed telescope, with its later entries
closed: the pattern substitution does nothing to them. -/
theorem patternCtx_closed (T k : DeclName) (F : Nat → Tm Head 0) (s d : Nat)
    (fields : List (Field Head)) :
    patternCtx T k (fun i => liftClosed (F i)) s d fields =
      extendEntries
        (extendEntries (ofEntries (fun i => liftClosed (F i)) s)
          (fun l => liftClosed ((fields.getD l .recursive).type T)) fields.length)
        (fun j => liftClosed (F (s + 1 + j))) d := by
  unfold patternCtx fieldCtx
  congr 1
  funext j
  exact subst_liftClosed _ _

/-- The move of the field block is a context renaming from the equation
context of the authored form to that of the scrutinee-first form. -/
theorem ctxRen_patternCtx_scrutineeFirst (T k : DeclName) (F : Nat → Tm Head 0) (s d : Nat)
    (fields : List (Field Head)) :
    CtxRen (patternCtx T k (fun i => liftClosed (F i)) s d fields)
      (patternCtx T k (fun i => liftClosed (scrutineeFirst F s i)) 0 (s + d) fields)
      (blockMove s fields.length d) := by
  have authored := extendEntries_lookup_closed
    (extendEntries_lookup_closed (ofEntries_lookup_closed F s)
      (fun l => (fields.getD l .recursive).type T) fields.length)
    (fun j => F (s + 1 + j)) d
  have first := extendEntries_lookup_closed
    (extendEntries_lookup_closed (ofEntries_lookup_closed (scrutineeFirst F s) 0)
      (fun l => (fields.getD l .recursive).type T) fields.length)
    (fun j => scrutineeFirst F s (0 + 1 + j)) (s + d)
  refine ctxRen_of_closed (fun i => by rw [patternCtx_closed]; exact authored i)
    (fun i => by rw [patternCtx_closed]; exact first i) (blockMove s fields.length d)
    (fun i => ?_)
  rcases Nat.lt_or_ge i.val d with h₁ | h₁
  · rw [show blockMove s fields.length d i = ⟨i.val, by omega⟩ by simp [blockMove, h₁],
      scrutineeFirst_later]
    dsimp only
    rw [dif_pos (by omega : i.val < s + d), dif_pos h₁,
      if_neg (by omega : ¬ s + d - 1 - i.val < s)]
    exact congrArg F (by omega)
  · rcases Nat.lt_or_ge i.val (d + fields.length) with h₂ | h₂
    · rw [show blockMove s fields.length d i = ⟨i.val + s, by omega⟩ by
        simp [blockMove, Nat.not_lt.mpr h₁, h₂]]
      dsimp only
      rw [dif_neg (by omega : ¬ i.val + s < s + d),
        dif_pos (by omega : i.val + s - (s + d) < fields.length), dif_neg (Nat.not_lt.mpr h₁),
        dif_pos (by omega : i.val - d < fields.length)]
      exact congrArg (fun l => (fields.getD l .recursive).type T) (by omega)
    · rw [show blockMove s fields.length d i = ⟨i.val - fields.length, by omega⟩ by
        simp [blockMove, Nat.not_lt.mpr h₁, Nat.not_lt.mpr h₂], scrutineeFirst_later]
      dsimp only
      rw [dif_pos (by omega : i.val - fields.length < s + d),
        if_pos (by omega : s + d - 1 - (i.val - fields.length) < s), dif_neg (Nat.not_lt.mpr h₁),
        dif_neg (by omega : ¬ i.val - d < fields.length)]
      exact congrArg F (by omega)

/-! ## Iterated η over a telescope of closed types

A function of the entries `G 0, …, G (d-1)` is determined by its
application to the variables of those entries: two such functions are
equal when their full applications are, in the context extended by the
entries. This is `etaPi` repeated `d` times. It is how a recursive
hypothesis of the authored form, a function of the later arguments, is
compared with the scrutinee-first hypothesis applied to the prefix. -/

/-- The dependent function type over the closed entries `G 0, …, G (d-1)`,
ending in `C`; the entry `G (d-1)` is the innermost binder. -/
def piClosed {n : Nat} (G : Nat → Tm Head 0) : (d : Nat) → Tm Head (n + d) → Tm Head n
  | 0, C => C
  | d + 1, C => piClosed G d (.pi (liftClosed (G d)) C)

/-- `piRange` over closed entries is `piClosed` over the entries from `j`. -/
theorem piRange_closed (F : Nat → Tm Head 0) (j : Nat) :
    ∀ (d : Nat) (C : Tm Head (j + d)),
      piRange (fun i => liftClosed (F i)) j d C = piClosed (fun l => F (j + l)) d C
  | 0, _ => rfl
  | d + 1, C => piRange_closed F j d (.pi (liftClosed (F (j + d))) C)

/-- The variables of the last `d` entries, as the arguments of a telescope
of length `d`: the newest variable for the newest entry. -/
def varSub (n : Nat) (d : Nat) : Sub Head d (n + d) := fun i => .var ⟨i.val, by omega⟩

/-- The application of `t` to the variables of the last `d` entries, oldest
first. -/
def appVars {n : Nat} (G : Nat → Tm Head 0) (d : Nat) (t : Tm Head (n + d)) : Tm Head (n + d) :=
  applyClosed (ofEntries (fun j => liftClosed (G j)) d) (varSub n d) t

theorem wkN_zero {n : Nat} : (wkN 0 : Ren n (n + 0)) = idRen :=
  funext fun _ => Fin.ext rfl

theorem rename_wkN_succ {n : Nat} (d : Nat) (g : Tm Head n) :
    Presentation.rename (wkN (d + 1)) g = Presentation.rename wk (Presentation.rename (wkN d) g) := by
  rw [rename_comp]
  rfl

theorem appVars_succ {n : Nat} (G : Nat → Tm Head 0) (d : Nat) (g : Tm Head n) :
    appVars G (d + 1) (Presentation.rename (wkN (d + 1)) g) =
      .app (Presentation.rename wk (appVars G d (Presentation.rename (wkN d) g))) (.var 0) := by
  show Tm.app (applyClosed (ofEntries (fun j => liftClosed (G j)) d)
      (fun i => varSub n (d + 1) i.succ) (Presentation.rename (wkN (d + 1)) g))
      (varSub n (d + 1) 0) =
    Tm.app (Presentation.rename wk (applyClosed (ofEntries (fun j => liftClosed (G j)) d)
      (varSub n d) (Presentation.rename (wkN d) g))) (.var 0)
  rw [rename_applyClosed, rename_wkN_succ]
  rfl

/-- Opening a binder at its own variable, after weakening under it, is the
identity. -/
theorem inst0_var_zero_rename_liftRen_wk {n : Nat} (C : Tm Head (n + 1)) :
    inst0 (.var 0) (Presentation.rename (liftRen wk) C) = C := by
  show subst (subst0 (.var 0)) (Presentation.rename (liftRen wk) C) = C
  rw [subst_rename]
  have ident : (fun i => subst0 (.var 0 : Tm Head (n + 1)) (liftRen wk i)) = ids := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · rfl
  rw [ident, subst_ids]

/-- A function of the closed entries, applied to their variables. -/
theorem Typed.appVars {n : Nat} {Γ : Ctx Head n} (G : Nat → Tm Head 0) :
    ∀ (d : Nat) {g : Tm Head n} {C : Tm Head (n + d)},
      Typed R Γ g (piClosed G d C) →
      Typed R (extendEntries Γ (fun j => Presentation.liftClosed (G j)) d)
        (appVars G d (Presentation.rename (wkN d) g)) C
  | 0, g, C, typing => by
      show Typed R Γ (Presentation.rename (wkN 0) g) C
      rw [wkN_zero, rename_id]
      exact typing
  | d + 1, g, C, typing => by
      rw [appVars_succ]
      have earlier :=
        (Typed.appVars G d (C := .pi (Presentation.liftClosed (G d)) C) typing).weaken
          (extension := Presentation.liftClosed (G d))
      have application := Derivable.appElim earlier (Derivable.var 0)
      rw [inst0_var_zero_rename_liftRen_wk] at application
      exact application

/-- Two functions of the closed entries are equal when their applications to
the entries' variables are. -/
theorem Equal.etaClosed {n : Nat} {Γ : Ctx Head n} (G : Nat → Tm Head 0) :
    ∀ (d : Nat) {g h : Tm Head n} {C : Tm Head (n + d)},
      Typed R Γ g (piClosed G d C) → Typed R Γ h (piClosed G d C) →
      Equal R (extendEntries Γ (fun j => Presentation.liftClosed (G j)) d)
        (appVars G d (Presentation.rename (wkN d) g))
        (appVars G d (Presentation.rename (wkN d) h)) C →
      Equal R Γ g h (piClosed G d C)
  | 0, g, h, C, _, _, equal => by
      have equal' : Equal R Γ (Presentation.rename (wkN 0) g) (Presentation.rename (wkN 0) h) C :=
        equal
      rw [wkN_zero, rename_id, rename_id] at equal'
      exact equal'
  | d + 1, g, h, C, typingG, typingH, equal => by
      rw [appVars_succ, appVars_succ] at equal
      exact Equal.etaClosed G d (C := .pi (Presentation.liftClosed (G d)) C) typingG typingH
        (Derivable.etaPi (Typed.appVars G d (C := .pi (Presentation.liftClosed (G d)) C) typingG)
          (Typed.appVars G d (C := .pi (Presentation.liftClosed (G d)) C) typingH) equal)

end Normalization
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
