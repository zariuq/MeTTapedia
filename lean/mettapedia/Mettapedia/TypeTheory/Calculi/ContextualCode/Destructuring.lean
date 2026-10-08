import Mettapedia.TypeTheory.Calculi.ContextualCode.Surface
import Mettapedia.TypeTheory.Calculi.ContextualCode.Matching

/-!
# Taking a binder apart: two readings

Rigid matching refuses to take the body of an abstraction when the body
mentions the bound variable (`show_bound_body_stuck`). A program that wants to
take such a body apart, like the draft's head `(show (quote ((lam $x $b) $c)))`,
needs one of two readings.

* **Raw body (D1).** The body is handed over with its bound variable still
  bound, as a template of one parameter (`rawBody`). Nothing is invented and
  nothing is lost: running the raw body gives back the abstraction
  (`run_rawBody`). Opening it with a name is the bracket, which goes through
  `lift` (`rawBody_bracket`); closing a symbol into a new parameter is
  `closeSym`, and the two are inverse (`openFirst_closeSym`,
  `closeSym_openFirst`).
* **Fresh name (D2).** The bound variable is replaced by a symbol the body does
  not contain, and the body is handed over as ordinary code (`openFresh`), which
  every operation on names accepts. Closing the same symbol restores the body
  (`close_openFresh`), a different fresh choice gives the same code up to
  swapping the two symbols (`openFresh_equivariant`), and a symbol that is not
  fresh is captured on closing (`openFresh_capture`).

Closing a freshly opened body gives the raw body (`close_fresh_is_raw`), so the
two readings agree on everything a program can rebuild; they differ in what a
program sees in between.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ContextualCode

open Term

/-! ## Opening the first parameter and closing a symbol -/

/-- Fill the outermost variable, which is the first parameter written, with
closed code; keep the others. -/
def firstParamSub {n : Nat} (V : Term 0) : Sub (n + 1) n := Fin.lastCases (ofClosed V) Term.var

theorem liftSub_firstParamSub {n : Nat} (V : Term 0) :
    liftSub (firstParamSub (n := n) V) = firstParamSub (n := n + 1) V := by
  funext i
  cases i using Fin.cases with
  | zero =>
      simp only [liftSub_zero, firstParamSub]
      rw [show (0 : Fin (n + 1 + 1)) = Fin.castSucc 0 from rfl, Fin.lastCases_castSucc]
  | succ j =>
      simp only [liftSub_succ, firstParamSub]
      cases j using Fin.lastCases with
      | last => rw [Fin.lastCases_last, Fin.succ_last, Fin.lastCases_last, rename_ofClosed]
      | cast j =>
          rw [Fin.lastCases_castSucc, Fin.succ_castSucc, Fin.lastCases_castSucc]
          rfl

/-- Fill the first parameter written with closed code, as written. -/
def openFirst {n : Nat} (V : Term 0) (M : Term (n + 1)) : Term n := M.subst (firstParamSub V)

/-- Abstract the symbol `a` as a new first parameter. The code of a template
is left alone, since it is closed. -/
def closeSym (a : String) : {n : Nat} → Term n → Term (n + 1)
  | _, .var i => .var i.castSucc
  | _, .sym s => if s = a then .var (Fin.last _) else .sym s
  | _, .lam b => .lam (closeSym a b)
  | _, .app f x => .app (closeSym a f) (closeSym a x)
  | _, .cquote k M => .cquote k M
  | _, .lift M => .lift (closeSym a M)
  | _, .drop K => .drop (closeSym a K)
  | _, .cmatch k K P F => .cmatch k (closeSym a K) P (closeSym a F)

/-- **Opening with `a` undoes closing `a`.** -/
theorem openFirst_closeSym (a : String) : ∀ {n : Nat} (M : Term n),
    openFirst (.sym a) (closeSym a M) = M
  | _, .var i => by
      simp only [closeSym, openFirst, subst, firstParamSub, Fin.lastCases_castSucc]
  | _, .sym s => by
      simp only [closeSym]
      split
      · next h =>
          subst h
          simp only [openFirst, subst, firstParamSub, Fin.lastCases_last]
          rfl
      · rfl
  | _, .lam b => by
      simp only [closeSym, openFirst, subst]
      rw [liftSub_firstParamSub]
      exact congrArg Term.lam (openFirst_closeSym a b)
  | _, .app f x => by
      simp only [closeSym, openFirst, subst]
      exact congrArg₂ Term.app (openFirst_closeSym a f) (openFirst_closeSym a x)
  | _, .cquote _ _ => rfl
  | _, .lift M => by
      simp only [closeSym, openFirst, subst]
      exact congrArg Term.lift (openFirst_closeSym a M)
  | _, .drop K => by
      simp only [closeSym, openFirst, subst]
      exact congrArg Term.drop (openFirst_closeSym a K)
  | _, .cmatch k K P F => by
      simp only [closeSym, openFirst, subst]
      exact congrArg₂ (fun K F => Term.cmatch k K P F) (openFirst_closeSym a K)
        (openFirst_closeSym a F)

/-- **Closing a fresh `a` undoes opening with `a`.** -/
theorem closeSym_openFirst (a : String) : ∀ {n : Nat} (M : Term (n + 1)), ¬ M.SymIn a →
    closeSym a (openFirst (.sym a) M) = M
  | n, .var i, _ => by
      cases i using Fin.lastCases with
      | last =>
          simp only [openFirst, subst, firstParamSub, Fin.lastCases_last]
          show closeSym a (.sym a) = .var (Fin.last n)
          simp only [closeSym, if_pos]
      | cast j =>
          simp only [openFirst, subst, firstParamSub, Fin.lastCases_castSucc, closeSym]
  | _, .sym s, fresh => by
      have hs : s ≠ a := fun h => fresh h
      simp only [openFirst, subst, closeSym, if_neg hs]
  | _, .lam b, fresh => by
      simp only [openFirst, subst, closeSym]
      rw [liftSub_firstParamSub]
      exact congrArg Term.lam (closeSym_openFirst a b fresh)
  | _, .app f x, fresh => by
      simp only [openFirst, subst, closeSym]
      exact congrArg₂ Term.app (closeSym_openFirst a f (fun h => fresh (.inl h)))
        (closeSym_openFirst a x (fun h => fresh (.inr h)))
  | _, .cquote _ _, _ => rfl
  | _, .lift M, fresh => by
      simp only [openFirst, subst, closeSym]
      exact congrArg Term.lift (closeSym_openFirst a M fresh)
  | _, .drop K, fresh => by
      simp only [openFirst, subst, closeSym]
      exact congrArg Term.drop (closeSym_openFirst a K fresh)
  | _, .cmatch k K P F, fresh => by
      simp only [openFirst, subst, closeSym]
      exact congrArg₂ (fun K F => Term.cmatch k K P F)
        (closeSym_openFirst a K (fun h => fresh (.inl h)))
        (closeSym_openFirst a F (fun h => fresh (.inr (.inr h))))

/-! ## (D1) The raw body -/

/-- The body of an abstraction, with its bound variable still bound: a
template of one parameter. -/
def rawBody {n : Nat} (b : Term 1) : Term n := .cquote 1 b

/-- **Running the raw body gives back the abstraction.** -/
theorem run_rawBody {n : Nat} (b : Term 1) :
    Step (.drop (rawBody b) : Term n) (ofClosed (.lam b)) :=
  .run 1 b

/-- **Opening the raw body with a name is the bracket.** -/
theorem rawBody_bracket {n : Nat} (b : Term 1) (V : Term 0) :
    Steps (inst (rawBody b) (.cquote 0 V) : Term n) (.lift (ofClosed (openFirst V b))) := by
  have h := instAll_template (n := n) b (fun _ : Fin 1 => V)
  have fill : b.subst (fillSub (fun _ : Fin 1 => V)) = openFirst V b := by
    unfold openFirst
    congr 1
    funext i
    rcases i with ⟨_ | _, hi⟩
    · simp only [fillSub, firstParamSub]
      exact (ofClosed_zero V).symm
    · omega
  rw [fill] at h
  exact h

/-! ## (D2) A fresh name -/

/-- Open the first parameter with the symbol `a`. -/
abbrev openFresh {n : Nat} (a : String) (M : Term (n + 1)) : Term n := openFirst (.sym a) M

/-- **Closing the same fresh symbol restores the body.** -/
theorem close_openFresh {n : Nat} (a : String) (M : Term (n + 1)) (fresh : ¬ M.SymIn a) :
    closeSym a (openFresh a M) = M :=
  closeSym_openFirst a M fresh

theorem renameSyms_rename (π : String → String) : ∀ {n m : Nat} (ρ : Ren n m) (M : Term n),
    (M.rename ρ).renameSyms π = (M.renameSyms π).rename ρ
  | _, _, _, .var _ => rfl
  | _, _, _, .sym _ => rfl
  | _, _, ρ, .lam b => by
      simp only [Term.rename, Term.renameSyms]
      rw [renameSyms_rename π (liftRen ρ) b]
  | _, _, ρ, .app f x => by
      simp only [Term.rename, Term.renameSyms]
      rw [renameSyms_rename π ρ f, renameSyms_rename π ρ x]
  | _, _, _, .cquote _ _ => rfl
  | _, _, ρ, .lift M => by
      simp only [Term.rename, Term.renameSyms]
      rw [renameSyms_rename π ρ M]
  | _, _, ρ, .drop K => by
      simp only [Term.rename, Term.renameSyms]
      rw [renameSyms_rename π ρ K]
  | _, _, ρ, .cmatch _ K _ F => by
      simp only [Term.rename, Term.renameSyms]
      rw [renameSyms_rename π ρ K, renameSyms_rename π ρ F]

theorem renameSyms_subst (π : String → String) : ∀ {n m : Nat} (σ : Sub n m) (M : Term n),
    (M.subst σ).renameSyms π = (M.renameSyms π).subst (fun i => (σ i).renameSyms π)
  | _, _, _, .var _ => rfl
  | _, _, _, .sym _ => rfl
  | _, _, σ, .lam b => by
      simp only [Term.subst, Term.renameSyms]
      rw [renameSyms_subst π (liftSub σ) b]
      congr 2
      funext i
      cases i using Fin.cases with
      | zero => rfl
      | succ i => exact renameSyms_rename π Fin.succ (σ i)
  | _, _, σ, .app f x => by
      simp only [Term.subst, Term.renameSyms]
      rw [renameSyms_subst π σ f, renameSyms_subst π σ x]
  | _, _, _, .cquote _ _ => rfl
  | _, _, σ, .lift M => by
      simp only [Term.subst, Term.renameSyms]
      rw [renameSyms_subst π σ M]
  | _, _, σ, .drop K => by
      simp only [Term.subst, Term.renameSyms]
      rw [renameSyms_subst π σ K]
  | _, _, σ, .cmatch _ K _ F => by
      simp only [Term.subst, Term.renameSyms]
      rw [renameSyms_subst π σ K, renameSyms_subst π σ F]

/-- **The choice of fresh symbol does not matter**: two fresh choices give the
same code up to swapping them. -/
theorem openFresh_equivariant {n : Nat} (a b : String) (M : Term (n + 1))
    (ha : ¬ M.SymIn a) (hb : ¬ M.SymIn b) :
    openFresh b M = (openFresh a M).renameSyms (Equiv.swap a b) := by
  unfold openFresh openFirst
  rw [renameSyms_subst]
  have fixed : M.renameSyms (Equiv.swap a b) = M := by
    apply Term.renameSyms_eq_self
    intro s hs
    exact Equiv.swap_apply_of_ne_of_ne (fun h => ha (h ▸ hs)) (fun h => hb (h ▸ hs))
  rw [fixed]
  congr 1
  funext i
  cases i using Fin.lastCases with
  | last =>
      simp only [firstParamSub, Fin.lastCases_last, ofClosed]
      rw [renameSyms_rename]
      simp only [Term.renameSyms, Equiv.swap_apply_left]
  | cast j =>
      simp only [firstParamSub, Fin.lastCases_castSucc]
      rfl

/-- **A symbol that is not fresh is captured on closing**: opening
`(quote (a $x) ($x))` with `a` and closing `a` binds both occurrences. -/
theorem openFresh_capture :
    closeSym "a" (openFresh "a" (.app (.sym "a") (.var 0) : Term 1)) = .app (.var 0) (.var 0) ∧
      (.app (.var 0) (.var 0) : Term 1) ≠ .app (.sym "a") (.var 0) := by
  refine ⟨by decide, by decide⟩

/-- **Closing a freshly opened body gives the raw body.** -/
theorem close_fresh_is_raw (a : String) (b : Term 1) (fresh : ¬ b.SymIn a) :
    (rawBody (closeSym a (openFresh a b)) : Term 0) = rawBody b := by
  rw [close_openFresh a b fresh]

/-! ## The fixture's head `(show (quote ((lam $x $b) $c)))` -/

/-- The body `(f $y)` of `(lam $y (f $y))`. -/
def showBody : Term 1 := .app (.sym "f") (.var 0)

/-- Under D1 the handler receives `@(quote (f $y) ($y))` for `$b`. -/
theorem show_D1 : (rawBody showBody : Term 0) = .cquote 1 (.app (.sym "f") (.var 0)) := rfl

/-- Under D2, with the fresh symbol `y#`, the handler receives `@(f y#)` for
`$b` and `@y#` for `$x`. -/
theorem show_D2 : (.cquote 0 (openFresh "y#" showBody) : Term 0) = .cquote 0 (.app (.sym "f") (.sym "y#")) :=
  rfl

/-- Closing `y#` in the D2 body gives back the D1 body. -/
theorem show_D2_closes_to_D1 :
    (rawBody (closeSym "y#" (openFresh "y#" showBody)) : Term 0) = rawBody showBody :=
  close_fresh_is_raw "y#" showBody (fun h => by
    simp only [showBody, Term.SymIn] at h
    rcases h with h | h
    · exact absurd h (by decide)
    · exact h)

end Mettapedia.TypeTheory.Calculi.ContextualCode
