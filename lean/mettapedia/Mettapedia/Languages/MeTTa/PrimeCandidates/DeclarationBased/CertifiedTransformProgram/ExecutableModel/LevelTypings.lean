import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel.Typings

/-!
# The recursor and the iterator at every level

The package declares the recursor on the numbers with its motive into the
lowest universe, and the iterator with its carrier and family in the lowest
universe. Their types at other universes:

* `numRecTypeAt w`: `Π P : num → w. P zero → (Π n : num. P n → P (suc n)) → Π n : num. P n`,
  the large elimination of the numbers when `w` is above the lowest universe;
* `iterTypeAt k l`: `Π (n : num) (A : k) (P : A → l) (step : Π x : A. P x → Σ y : A. P y)
  (x : A) (e : P x). Σ A P`, the iterator at large families.

The declared types are the instances at the lowest universe (`numRecTypeAt_zero`,
`iterTypeAt_zero`). At universes of the tower both are typed
(`numRecTypeAt_typed`, `iterTypeAt_typed`), in the stages of the package that
declare the numbers: each part is typed at its own universe and raised by
cumulativity to one universe; the level inequalities are those of the natural
numbers under every valuation.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId
open Mettapedia.TypeTheory.UniverseLevel
open Presentation
open Presentation.TypedEquality
open Presentation.TypedEquality.Normalization
open TelescopeAbstraction (closeType)
open SetProfile (zeroNative)
open Package (numT numRecType iterType stepFamily)

/-! ## The types -/

/-- The telescope of the recursor with its motive into `w`: the motive, the
value at zero and the step. -/
abbrev numRecTelescopeAt (w : Tower.Head) : Tower.Ctx 3 :=
  .snoc (.snoc (.snoc .nil (.pi numT (.head w))) (.app (.var 0) zeroNative))
    Package.numRecStepType

/-- **The recursor's type with its motive into the universe `w`**:
`Π P : num → w. P zero → (Π n : num. P n → P (suc n)) → Π n : num. P n`. -/
def numRecTypeAt (w : Tower.Head) : Tower.Tm 0 :=
  closeType (.snoc (numRecTelescopeAt w) numT) (.app (.var 3) (.var 0))

/-- The declared type of the recursor is its type with the motive into the
lowest universe. -/
theorem numRecTypeAt_zero : numRecTypeAt (.sort Tower.zero) = numRecType :=
  rfl

/-- The telescope of the iterator at a successor, with its carrier in `k` and
its family into `l`: the count, the carrier, the family, the step, the value and
its evidence. -/
abbrev iterSucTelescopeAt (k l : Tower.Head) : Tower.Ctx 6 :=
  .snoc (.snoc (.snoc (.snoc (.snoc (.snoc .nil numT) (.head k)) (.pi (.var 0) (.head l)))
    stepFamily) (.var 2)) (.app (.var 2) (.var 0))

/-- **The iterator's type with its carrier in `k` and its family into `l`.** -/
def iterTypeAt (k l : Tower.Head) : Tower.Tm 0 :=
  closeType (iterSucTelescopeAt k l) iterResult

/-- The declared type of the iterator is its type with carrier and family in
the lowest universe. -/
theorem iterTypeAt_zero : iterTypeAt (.sort Tower.zero) (.sort Tower.zero) = iterType :=
  rfl

/-! ## Typings at a level -/

section Toolkit

variable {allowed : DeclName → Bool} {n : Nat} {Γ : Tower.Ctx n}

/-- A type of one universe is a type of every universe above it. -/
theorem raiseTo {T : Tower.Tm n} {a b : LevelExpr Nat}
    (typed : Typed (stage allowed) Γ T (sortTm a))
    (le : ∀ ν, LevelExpr.eval ν a ≤ LevelExpr.eval ν b) :
    Typed (stage allowed) Γ T (sortTm b) :=
  .cumul typed le

/-- The numbers are a type of every universe. -/
theorem numT_typedAt {names : List DeclName} (mem : numN ∈ names) (level : LevelExpr Nat) :
    Typed (stage (allowedIn names)) Γ numT (sortTm level) :=
  raiseTo (numT_typed mem) fun _ => Nat.zero_le _

end Toolkit

/-- A level is at most its successor. -/
theorem le_succ_eval (ν : Nat → Nat) (a : LevelExpr Nat) :
    LevelExpr.eval ν a ≤ LevelExpr.eval ν (.succ a) :=
  Nat.le_succ _

/-- **The recursor's type with its motive into `U lw` is typed** in the stage of
the numbers and their constructors, at `U (lw + 1)`. -/
theorem numRecTypeAt_typed (lw : LevelExpr Nat) :
    Typed ctorStage .nil (numRecTypeAt (.sort lw)) (sortTm (.succ lw)) := by
  have numMem : numN ∈ [numN, zeroN, sucN] := by simp
  have zeroMem : zeroN ∈ [numN, zeroN, sucN] := by simp
  have sucMem : sucN ∈ [numN, zeroN, sucN] := by simp
  have tNum : ∀ {n : Nat} {Γ : Tower.Ctx n}, Typed ctorStage Γ numT (sortTm lw) :=
    fun {_ _} => numT_typedAt numMem lw
  have tZero : ∀ {n : Nat} {Γ : Tower.Ctx n}, Typed ctorStage Γ (.const zeroN) numT :=
    fun {_ _} => zero_typed numMem zeroMem
  have tSuc : ∀ {n : Nat} {Γ : Tower.Ctx n}, Typed ctorStage Γ (.const sucN) (.pi numT numT) :=
    fun {_ _} => suc_typed numMem sucMem
  have up : ∀ {n : Nat} {Γ : Tower.Ctx n} {T : Tower.Tm n},
      Typed ctorStage Γ T (sortTm lw) → Typed ctorStage Γ T (sortTm (.succ lw)) :=
    fun typed => raiseTo typed (le_succ_eval · lw)
  -- the motive's type
  have tE0 : Typed ctorStage .nil (.pi numT (.head (.sort lw))) (sortTm (.succ lw)) :=
    piT (up tNum) (universe_typed lw)
  -- the case of zero
  let Γ₁ : Tower.Ctx 1 := .snoc .nil (.pi numT (.head (.sort lw)))
  have tE1 : Typed ctorStage Γ₁ (.app (.var 0) (.const zeroN)) (sortTm lw) :=
    .appElim (B := sortTm lw) (.var 0) tZero
  -- the case of the successor
  let Γ₂ : Tower.Ctx 2 := .snoc Γ₁ (.app (.var 0) (.const zeroN))
  let Γ₂x : Tower.Ctx 3 := .snoc Γ₂ numT
  have tIH : Typed ctorStage Γ₂x (.app (.var 2) (.var 0)) (sortTm lw) :=
    .appElim (B := sortTm lw) (.var 2) (.var 0)
  let Γ₂h : Tower.Ctx 4 := .snoc Γ₂x (.app (.var 2) (.var 0))
  have tSucX : Typed ctorStage Γ₂h (.app (.const sucN) (.var 1)) numT := .appElim tSuc (.var 1)
  have tGoal : Typed ctorStage Γ₂h (.app (.var 3) (.app (.const sucN) (.var 1))) (sortTm lw) :=
    .appElim (B := sortTm lw) (.var 3) tSucX
  have tE2 : Typed ctorStage Γ₂ (.pi numT (.pi (.app (.var 2) (.var 0))
      (.app (.var 3) (.app (.const sucN) (.var 1))))) (sortTm lw) :=
    piT tNum (piT tIH tGoal)
  -- the scrutinee and the result
  let Γ₃ : Tower.Ctx 3 := .snoc Γ₂ (.pi numT (.pi (.app (.var 2) (.var 0))
      (.app (.var 3) (.app (.const sucN) (.var 1)))))
  have tBody : Typed ctorStage (.snoc Γ₃ numT) (.app (.var 3) (.var 0)) (sortTm lw) :=
    .appElim (B := sortTm lw) (.var 3) (.var 0)
  exact piT tE0 (piT (up tE1) (piT (up tE2) (piT (up tNum) (up tBody))))

/-! ## The iterator at large families -/

/-- The universe of the iterator's type with its carrier in `U lk` and its family
into `U ll`. -/
abbrev iterLevel (lk ll : LevelExpr Nat) : LevelExpr Nat := .max (.succ lk) (.succ ll)

/-- The universe of the iterator's step with its carrier in `U lk` and its family
into `U ll`. -/
abbrev stepLevel (lk ll : LevelExpr Nat) : LevelExpr Nat := .max lk ll

theorem lk_le_step (ν : Nat → Nat) (lk ll : LevelExpr Nat) :
    LevelExpr.eval ν lk ≤ LevelExpr.eval ν (stepLevel lk ll) :=
  le_max_left _ _

theorem ll_le_step (ν : Nat → Nat) (lk ll : LevelExpr Nat) :
    LevelExpr.eval ν ll ≤ LevelExpr.eval ν (stepLevel lk ll) :=
  le_max_right _ _

theorem succ_lk_le_iter (ν : Nat → Nat) (lk ll : LevelExpr Nat) :
    LevelExpr.eval ν (.succ lk) ≤ LevelExpr.eval ν (iterLevel lk ll) :=
  le_max_left _ _

theorem succ_ll_le_iter (ν : Nat → Nat) (lk ll : LevelExpr Nat) :
    LevelExpr.eval ν (.succ ll) ≤ LevelExpr.eval ν (iterLevel lk ll) :=
  le_max_right _ _

theorem step_le_iter (ν : Nat → Nat) (lk ll : LevelExpr Nat) :
    LevelExpr.eval ν (stepLevel lk ll) ≤ LevelExpr.eval ν (iterLevel lk ll) :=
  max_le ((le_succ_eval ν lk).trans (succ_lk_le_iter ν lk ll))
    ((le_succ_eval ν ll).trans (succ_ll_le_iter ν lk ll))

/-- The step's type `Π x : A. P x → Σ y : A. P y`, in the context of a carrier
`A : U lk` and a family `P : A → U ll`, is a type of the universe of their
join. -/
theorem stepFamily_typedAt {allowed : DeclName → Bool} {n : Nat} {Γ : Tower.Ctx n}
    (lk ll : LevelExpr Nat) :
    Typed (stage allowed) (.snoc (.snoc Γ (.head (.sort lk))) (.pi (.var 0) (.head (.sort ll))))
      stepFamily (sortTm (stepLevel lk ll)) := by
  have carrier : ∀ {m : Nat} {Δ : Tower.Ctx m} {A : Tower.Tm m},
      Typed (stage allowed) Δ A (sortTm lk) → Typed (stage allowed) Δ A (sortTm (stepLevel lk ll)) :=
    fun typed => raiseTo typed (lk_le_step · lk ll)
  have family : ∀ {m : Nat} {Δ : Tower.Ctx m} {A : Tower.Tm m},
      Typed (stage allowed) Δ A (sortTm ll) → Typed (stage allowed) Δ A (sortTm (stepLevel lk ll)) :=
    fun typed => raiseTo typed (ll_le_step · lk ll)
  exact piT (carrier (.var 1)) (piT (family (.appElim (B := sortTm ll) (.var 1) (.var 0)))
    (sigmaT (carrier (.var 3)) (family (.appElim (B := sortTm ll) (.var 3) (.var 0)))))

/-- **The iterator's type with its carrier in `U lk` and its family into `U ll`
is typed** in the stage of the numbers. -/
theorem iterTypeAt_typed (lk ll : LevelExpr Nat) :
    Typed numStage .nil (iterTypeAt (.sort lk) (.sort ll)) (sortTm (iterLevel lk ll)) := by
  have numMem : numN ∈ [numN] := by simp
  have carrier : ∀ {m : Nat} {Δ : Tower.Ctx m} {A : Tower.Tm m},
      Typed numStage Δ A (sortTm lk) → Typed numStage Δ A (sortTm (iterLevel lk ll)) :=
    fun typed => raiseTo typed fun ν => (le_succ_eval ν lk).trans (succ_lk_le_iter ν lk ll)
  have family : ∀ {m : Nat} {Δ : Tower.Ctx m} {A : Tower.Tm m},
      Typed numStage Δ A (sortTm ll) → Typed numStage Δ A (sortTm (iterLevel lk ll)) :=
    fun typed => raiseTo typed fun ν => (le_succ_eval ν ll).trans (succ_ll_le_iter ν lk ll)
  have step : ∀ {m : Nat} {Δ : Tower.Ctx m} {A : Tower.Tm m},
      Typed numStage Δ A (sortTm (stepLevel lk ll)) →
        Typed numStage Δ A (sortTm (iterLevel lk ll)) :=
    fun typed => raiseTo typed (step_le_iter · lk ll)
  have tFamily : Typed numStage (.snoc (.snoc .nil numT) (.head (.sort lk)))
      (.pi (.var 0) (.head (.sort ll))) (sortTm (iterLevel lk ll)) :=
    piT (carrier (.var 0)) (raiseTo (universe_typed ll) (succ_ll_le_iter · lk ll))
  exact piT (numT_typedAt numMem _)
    (piT (raiseTo (universe_typed lk) (succ_lk_le_iter · lk ll))
      (piT tFamily
        (piT (step (stepFamily_typedAt lk ll))
          (piT (carrier (.var 2))
            (piT (family (.appElim (B := sortTm ll) (.var 2) (.var 0)))
              (step (sigmaT (raiseTo (.var 4) (lk_le_step · lk ll))
                (raiseTo (.appElim (B := sortTm ll) (.var 4) (.var 0))
                  (ll_le_step · lk ll)))))))))

end Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel
