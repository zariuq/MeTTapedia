import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.ScrutineeFirstDefinition

/-!
# The scrutinee-first telescope of a dependent telescope

A definition recursive on its argument at `s` has the telescope
`x₀ : A₀, …, x_{s-1} : A_{s-1}, t : T, y₁ : B₁, …, y_d : B_d`, in which each
`Aᵢ` may mention the earlier `x`s and each `Bⱼ` everything before it. When
`T` is closed, moving `t` to the front gives the telescope
`t : T, x₀ : A₀, …, x_{s-1} : A_{s-1}, y₁ : B₁', …, y_d : B_d'`, with each
`Aᵢ` unchanged and each `Bⱼ` renamed along the move. The move is a context
renaming, so typing and typed equality transport from the authored telescope
to the scrutinee-first one: the scrutinee-first form's declared type is formed
whenever the authored type is, and its equations are typed wherever the
authored ones are. It is built from exchanges of adjacent entries, `t` passing
each `xᵢ` because `T` mentions none of them.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Normalization

variable {Head : Type}

/-- The entries of a telescope with the closed first entry `T₀`, followed by the
entries `e`, each past the new first entry. -/
def frontEntries (T₀ : Tm Head 0) (e : (i : Nat) → Tm Head i) : (j : Nat) → Tm Head j
  | 0 => liftClosed T₀
  | j + 1 => Presentation.rename Fin.castSucc (e j)

/-- The renaming moving the last entry of `s + 1` to the front: the last entry
goes to the oldest position, the others one step inward. -/
def rotate (s : Nat) : Ren (s + 1) (s + 1) := fun i =>
  if h : i.val = 0 then ⟨s, by omega⟩ else ⟨i.val - 1, by omega⟩

theorem rotate_wk (s : Nat) : (fun i : Fin s => rotate s (wk i)) = Fin.castSucc := by
  funext i
  apply Fin.ext
  simp [rotate, wk]

theorem rotate_succ (s : Nat) :
    (fun i : Fin (s + 1 + 1) => liftRen (rotate s) (swap01 i)) = rotate (s + 1) := by
  funext i
  apply Fin.ext
  rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨j, rfl⟩
  · rfl
  · rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨k, rfl⟩
    · rfl
    · show (liftRen (rotate s) (swap01 k.succ.succ)).val = (rotate (s + 1) k.succ.succ).val
      rw [swap01_succ_succ]
      show (rotate s k.succ).val + 1 = (rotate (s + 1) k.succ.succ).val
      simp only [rotate, Fin.val_succ]
      rw [dif_neg (by omega), dif_neg (by omega)]
      dsimp only
      omega

/-- Moving a closed last entry to the front of a telescope is a context
renaming. -/
theorem ctxRen_rotate (T₀ : Tm Head 0) (e : (i : Nat) → Tm Head i) :
    ∀ (s : Nat), CtxRen (.snoc (ofEntries e s) (liftClosed T₀))
      (ofEntries (frontEntries T₀ e) (s + 1)) (rotate s)
  | 0 => by
      intro i
      refine Fin.cases ?_ (fun j => Fin.elim0 j) i
      show Presentation.rename wk (liftClosed T₀) =
        Presentation.rename (rotate 0) (Presentation.rename wk (liftClosed T₀))
      simp only [rename_liftClosed]
  | s + 1 => by
      have ex := ctxRen_exchange (ofEntries e s) (e s) (liftClosed T₀)
      rw [rename_liftClosed] at ex
      have lifted := (ctxRen_rotate T₀ e s).snoc (Presentation.rename wk (e s))
      have comp := CtxRen.comp ex lifted
      rw [rotate_succ, rename_comp, rotate_wk] at comp
      exact comp

/-- A telescope of `n + d` entries is the first `n` extended by the rest. -/
theorem ofEntries_add (e : (i : Nat) → Tm Head i) (n : Nat) :
    ∀ (d : Nat), ofEntries e (n + d) = extendEntries (ofEntries e n) (fun j => e (n + j)) d
  | 0 => rfl
  | d + 1 => by
      show Ctx.snoc (ofEntries e (n + d)) (e (n + d)) = _
      rw [ofEntries_add e n d]
      rfl

/-- The scrutinee-first telescope: the closed scrutinee type first, the earlier
entries unchanged past it, the later entries renamed along the move. -/
def scrutineeFront (T₀ : Tm Head 0) (e : (i : Nat) → Tm Head i) (s d : Nat) : Ctx Head (s + 1 + d) :=
  extendEntries (ofEntries (frontEntries T₀ e) (s + 1))
    (fun j => Presentation.rename (liftRenN (rotate s) j) (e (s + 1 + j))) d

/-- For a telescope whose entry at `s` is closed, moving that entry to the
front is a context renaming onto the scrutinee-first telescope. -/
theorem ctxRen_scrutineeFront (T₀ : Tm Head 0) (e : (i : Nat) → Tm Head i) (s d : Nat)
    (closed : e s = liftClosed T₀) :
    CtxRen (ofEntries e (s + 1 + d)) (scrutineeFront T₀ e s d) (liftRenN (rotate s) d) := by
  rw [ofEntries_add e (s + 1) d]
  have front : ofEntries e (s + 1) = .snoc (ofEntries e s) (liftClosed T₀) := by
    show Ctx.snoc (ofEntries e s) (e s) = _
    rw [closed]
  rw [front]
  exact ctxRen_extendEntries (ctxRen_rotate T₀ e s) (fun j => e (s + 1 + j)) d

/-- The move sends each authored argument where the scrutinee-first form takes
it. -/
theorem liftRenN_rotate_val (s : Nat) :
    ∀ (d : Nat) (i : Fin (s + 1 + d)),
      (liftRenN (rotate s) d i).val = (teleMove s d i).val
  | 0, i => by
      rw [teleMove_val]
      show (rotate s i).val = _
      simp only [rotate]
      split_ifs <;> dsimp only <;> omega
  | d + 1, i => by
      rw [teleMove_val]
      rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨j, rfl⟩
      · show (0 : Nat) = _
        rw [if_pos (by simp)]
        rfl
      · show (liftRenN (rotate s) d j).val + 1 = _
        rw [liftRenN_rotate_val s d j, teleMove_val]
        simp only [Fin.val_succ]
        split_ifs <;> omega

section Transport

variable {R : Rules Head} (T₀ : Tm Head 0) (e : (i : Nat) → Tm Head i) (s d : Nat)
  (closed : e s = Presentation.liftClosed T₀)
include closed

/-- A term typed in the authored telescope is typed, renamed along the move, in
the scrutinee-first telescope. -/
theorem Typed.toScrutineeFront {t A : Tm Head (s + 1 + d)} (typing : Typed R (ofEntries e (s + 1 + d)) t A) :
    Typed R (scrutineeFront T₀ e s d) (Presentation.rename (liftRenN (rotate s) d) t)
      (Presentation.rename (liftRenN (rotate s) d) A) :=
  typing.rename (ctxRen_scrutineeFront T₀ e s d closed)

/-- A typed equality in the authored telescope holds, renamed along the move,
in the scrutinee-first telescope. -/
theorem Equal.toScrutineeFront {a b A : Tm Head (s + 1 + d)}
    (equal : Equal R (ofEntries e (s + 1 + d)) a b A) :
    Equal R (scrutineeFront T₀ e s d) (Presentation.rename (liftRenN (rotate s) d) a)
      (Presentation.rename (liftRenN (rotate s) d) b) (Presentation.rename (liftRenN (rotate s) d) A) :=
  equal.rename (ctxRen_scrutineeFront T₀ e s d closed)

end Transport

end Normalization
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
