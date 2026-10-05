import Mettapedia.GSLT.Distinction.ProductionLicences
import Mettapedia.GSLT.Distinction.CausalGluing
import Mettapedia.GSLT.Dynamics.MemoizationObserver
import Mettapedia.GSLT.Core.NonFactorization

/-!
# One notion, two modules: identifications across the lane modules

Some notions of the lane modules were stated twice, under different names, in
different modules.  This module states each identification once, without
changing either statement.

* **Production ledgers are declared accounts.**  The denotation of a production
  ledger (`SharedCoefficientLedger.denote`) is the declared account of its factors
  read as occurrences (`CausalGluing.Occurrences.account`), so moving a bound
  production between eager and lazy charging is moving one occurrence of an
  account across a block (`eager_eq_lazy_iff_account_move`).  Both are decided by
  `Algebra.OrderedProductCommutation.prod_cons_eq_prod_concat_iff`: the exact
  condition is commutation with the block's product
  (`ProductionLicences.eager_eq_lazy_iff_commute_denote`,
  `CausalGluing.Occurrences.account_cons_eq_concat_iff`).
* **`MovesPast` is the pairwise tile condition.**  A production moves past a
  ledger in the sense of `ProductionLicences.MovesPast` exactly when every
  two-occurrence tile it forms with a factor of the ledger keeps the account
  (`movesPast_iff_forall_account_tile`, through
  `CausalGluing.Occurrences.account_tile_iff_commute`).  It is sufficient for the
  move and not necessary (`movesPast_sufficient_not_necessary`).
* **A sound memo key is constancy on fibres.**  `MemoizationObserver.SoundKey`
  and `NonFactorization.ConstantOnFibers` are the same predicate
  (`soundKey_iff_constantOnFibers`), so a `NonTrivialFiber` refutes a key
  (`not_soundKey_of_fiber`).
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Distinction.Consolidation

open Mettapedia.Algebra.SharedCoefficientLedger (Factor Ledger denote)
open Mettapedia.GSLT.Distinction.ProductionLicences (eagerLedger lazyLedger drawnAt MovesPast)
open Mettapedia.GSLT.Distinction.CausalGluing.Occurrences (account)

/-! ## Production ledgers and declared accounts -/

section Accounts

variable {Id A V : Type} [Monoid V]

/-- **A production ledger's denotation is the declared account of its factors.** -/
theorem denote_eq_account (ledger : Ledger Id A V) :
    denote ledger = account Factor.coefficient ledger :=
  rfl

/-- **Moving a production between eager and lazy charging is an account move**:
the bound production, as an occurrence, crosses the block of preceding factors. -/
theorem eager_eq_lazy_iff_account_move (production : Factor Id A V)
    (preceding : Ledger (List Id × Id) A V) :
    denote (eagerLedger production preceding) = denote (lazyLedger production preceding) ↔
      account Factor.coefficient (drawnAt [] production :: preceding) =
        account Factor.coefficient (preceding ++ [drawnAt [] production]) :=
  Iff.rfl

/-- **`MovesPast` is the pairwise tile condition** of the declared account. -/
theorem movesPast_iff_forall_account_tile (production : Factor Id A V)
    (preceding : Ledger (List Id × Id) A V) :
    MovesPast production preceding ↔
      ∀ factor ∈ preceding,
        account Factor.coefficient [drawnAt [] production, factor] =
          account Factor.coefficient [factor, drawnAt [] production] := by
  refine forall₂_congr fun factor _ => ?_
  rw [CausalGluing.Occurrences.account_tile_iff_commute]
  rfl

end Accounts

/-- **`MovesPast` is sufficient for the move and not necessary.**  With
permutation coefficients, a production `(0 1)` moved past two factors `(1 2)`:
eager and lazy charging agree, because the block's product is the identity, while
the production does not commute with either factor. -/
theorem movesPast_sufficient_not_necessary :
    let production : Factor ℕ Unit (Equiv.Perm (Fin 3)) := ⟨0, (), Equiv.swap 0 1⟩
    let preceding : Ledger (List ℕ × ℕ) Unit (Equiv.Perm (Fin 3)) :=
      [⟨([], 1), (), Equiv.swap 1 2⟩, ⟨([], 2), (), Equiv.swap 1 2⟩]
    denote (eagerLedger production preceding) = denote (lazyLedger production preceding) ∧
      ¬ MovesPast production preceding := by
  intro production preceding
  refine ⟨(ProductionLicences.eager_eq_lazy_iff_commute_denote production preceding).2 ?_,
    fun lawful => ?_⟩
  · have identity : denote preceding = 1 := by decide
    rw [identity]
    exact Commute.one_right _
  · have first := lawful ⟨([], 1), (), Equiv.swap 1 2⟩ (by simp [preceding])
    have : (Equiv.swap 0 1 : Equiv.Perm (Fin 3)) * Equiv.swap 1 2 =
        Equiv.swap 1 2 * Equiv.swap 0 1 := first.eq
    revert this
    decide

/-! ## Memo keys and fibres -/

section Keys

open Mettapedia.GSLT.Dynamics.MemoizationObserver (SoundKey)
open Mettapedia.GSLT.Core.NonFactorization (ConstantOnFibers NonTrivialFiber)

universe uX uK uO

variable {X : Type uX} {K : Type uK} {O : Type uO}

/-- **A sound memo key is a shadow on whose fibres the consumer is constant.** -/
theorem soundKey_iff_constantOnFibers (key : X → K) (obs : X → O) :
    SoundKey key obs ↔ ConstantOnFibers key obs :=
  Iff.rfl

/-- A non-trivial fibre refutes a memo key. -/
theorem not_soundKey_of_fiber {key : X → K} {obs : X → O} (fiber : NonTrivialFiber key obs) :
    ¬ SoundKey key obs :=
  fun sound => fiber.differentValue (sound _ _ fiber.sameShadow)

end Keys

end Mettapedia.GSLT.Distinction.Consolidation
