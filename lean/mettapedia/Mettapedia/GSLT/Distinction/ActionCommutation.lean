import Mettapedia.GSLT.Distinction.CausalGluing
import Mettapedia.GSLT.Dynamics.EffectTraceInterleaving
import Mettapedia.Machines.Cursor.PermutationInvariantFold

/-!
# Commutation of actions is commutation in a monoid

Three modules state when reordering does not change a result.
`EffectTraceInterleaving.CrossCommutes` asks that every event of one branch
commute with every event of the other as a state endomorphism;
`PermutationInvariantFold.ActionsCommute` asks it of all item actions of a
fold; `Algebra.OrderedProductCommutation` decides moves of factors in an
ordered product.  The first two are the third read in two monoids.

* **Actions as endomorphisms** (`endo`, `run_eq_endo_prod`,
  `crossCommutes_iff_commute`, `actionsCommute_iff_commute`).  An action of
  events on states is a map into the monoid of state endomorphisms; a run is
  the ordered product of the actions, latest first; cross commutation and
  commuting item actions are commutation of those endomorphisms.
* **Charging is the right action of the coefficients** (`charge`, `run_charge`,
  `crossCommutes_charge_iff`, `actionsCommute_charge_iff`).  Multiplying an
  account on the right by each occurrence's coefficient runs to the initial
  account times the ordered product of the coefficients, and the two action
  conditions become commutation of the coefficients.
* **The interleaving theorem for declared accounts** (`account_shuffle`,
  `account_perm`).  `run_eq_leftSerial_of_crossCommutes`, read through the
  charging action, says that every legal interleaving of two blocks whose
  coefficients commute across the blocks has the account of the left block
  followed by the right one; `CausalGluing.Occurrences.account_blocks` is the
  interleaving `right ++ left`.  With all coefficients commuting, every
  permutation keeps the account (`foldl_perm` through the charging action).

Controls: in a commutative monoid every interleaving keeps the account
(`commutative_account_shuffle`); two different letters of a free monoid do not
cross commute and their two serial interleavings have different accounts
(`free_letters_do_not_cross_commute`); and the pairwise condition is
sufficient, not necessary, for a block move (`block_move_without_cross_commutation`):
a transposition moves across the block `[s, s]` of another transposition
without commuting with `s`.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Distinction.ActionCommutation

open Mettapedia.Algebra.OrderedProductCommutation
open Mettapedia.GSLT.Dynamics.EffectTraceInterleaving (Shuffle CrossCommutes run run_append
  run_eq_leftSerial_of_crossCommutes)
open Mettapedia.Machines.Cursor.PermutationInvariantFold (ActionsCommute foldl_perm)
open Mettapedia.GSLT.Distinction.CausalGluing.Occurrences (account)

/-! ## Actions as endomorphisms -/

section Actions

universe uState uEvent

variable {State : Type uState} {Event : Type uEvent} (step : State → Event → State)

/-- The action of one event as an endomorphism of states. -/
def endo (event : Event) : Function.End State := fun state => step state event

/-- **A run is the ordered product of the actions, latest first.** -/
theorem run_eq_endo_prod (initial : State) (events : List Event) :
    run step initial events = (events.map (endo step)).reverse.prod initial := by
  induction events generalizing initial with
  | nil => rfl
  | cons event rest ih =>
      rw [List.map_cons, List.reverse_cons, List.prod_append, List.prod_singleton]
      exact ih (step initial event)

/-- Two actions commute at every state exactly when their endomorphisms
commute. -/
theorem forall_comm_iff_commute (first second : Event) :
    (∀ state, step (step state first) second = step (step state second) first) ↔
      Commute (endo step first) (endo step second) := by
  constructor
  · intro comm
    exact funext fun state => (comm state).symm
  · intro commute state
    exact (congrFun commute.eq state).symm

/-- **Cross commutation is commutation of endomorphisms.** -/
theorem crossCommutes_iff_commute (left right : List Event) :
    CrossCommutes step left right ↔
      ∀ a ∈ left, ∀ b ∈ right, Commute (endo step a) (endo step b) := by
  constructor
  · intro cross a inLeft b inRight
    exact (forall_comm_iff_commute step a b).1 (cross a inLeft b inRight)
  · intro commute a inLeft b inRight
    exact (forall_comm_iff_commute step a b).2 (commute a inLeft b inRight)

/-- **Commuting item actions are commuting endomorphisms.** -/
theorem actionsCommute_iff_commute :
    ActionsCommute step ↔ ∀ a b, Commute (endo step a) (endo step b) := by
  constructor
  · intro commute a b
    exact (forall_comm_iff_commute step a b).1 fun state => commute state a b
  · intro commute state a b
    exact (forall_comm_iff_commute step a b).2 (commute a b) state

end Actions

/-! ## Charging: the right action of the coefficients -/

section Charging

variable {ι M : Type} [Monoid M] (coefficient : ι → M)

/-- Charging an occurrence multiplies the account on the right by its
coefficient. -/
def charge (current : M) (occurrence : ι) : M := current * coefficient occurrence

/-- **A charging run is the initial account times the ordered product.** -/
theorem run_charge (initial : M) (occurrences : List ι) :
    run (charge coefficient) initial occurrences = initial * (occurrences.map coefficient).prod := by
  induction occurrences generalizing initial with
  | nil => exact (mul_one initial).symm
  | cons occurrence rest ih =>
      change run (charge coefficient) (initial * coefficient occurrence) rest =
        initial * (coefficient occurrence * (rest.map coefficient).prod)
      rw [ih, mul_assoc]

/-- The declared account is the charging run from `1`. -/
theorem account_eq_run (occurrences : List ι) :
    account coefficient occurrences = run (charge coefficient) 1 occurrences := by
  rw [run_charge, one_mul]
  rfl

/-- Two charges commute at every account exactly when the coefficients
commute. -/
theorem charge_comm_iff (a b : ι) :
    (∀ current, charge coefficient (charge coefficient current a) b =
        charge coefficient (charge coefficient current b) a) ↔
      Commute (coefficient a) (coefficient b) := by
  constructor
  · intro comm
    have atOne := comm 1
    change 1 * coefficient a * coefficient b = 1 * coefficient b * coefficient a at atOne
    rw [one_mul, one_mul] at atOne
    exact atOne
  · intro commute current
    change current * coefficient a * coefficient b = current * coefficient b * coefficient a
    rw [mul_assoc, commute.eq, ← mul_assoc]

/-- **Cross commutation of the charging action is commutation of the
coefficients across the blocks.** -/
theorem crossCommutes_charge_iff (left right : List ι) :
    CrossCommutes (charge coefficient) left right ↔
      ∀ a ∈ left, ∀ b ∈ right, Commute (coefficient a) (coefficient b) := by
  constructor
  · intro cross a inLeft b inRight
    exact (charge_comm_iff coefficient a b).1 (cross a inLeft b inRight)
  · intro commute a inLeft b inRight
    exact (charge_comm_iff coefficient a b).2 (commute a inLeft b inRight)

/-- **Commuting charges are commuting coefficients.** -/
theorem actionsCommute_charge_iff :
    ActionsCommute (charge coefficient) ↔ ∀ a b, Commute (coefficient a) (coefficient b) := by
  constructor
  · intro commute a b
    exact (charge_comm_iff coefficient a b).1 fun current => commute current a b
  · intro commute current a b
    exact (charge_comm_iff coefficient a b).2 (commute a b) current

/-- **Every legal interleaving of two blocks has the account of the left block
followed by the right one**, when the coefficients commute across the blocks.
The block move `CausalGluing.Occurrences.account_blocks` is the interleaving
`right ++ left`. -/
theorem account_shuffle {left right trace : List ι}
    (lawful : ∀ a ∈ left, ∀ b ∈ right, Commute (coefficient a) (coefficient b))
    (legal : Shuffle left right trace) (before : List ι) :
    account coefficient (before ++ trace) = account coefficient (before ++ left ++ right) := by
  rw [account_eq_run, account_eq_run, List.append_assoc, run_append, run_append]
  exact run_eq_leftSerial_of_crossCommutes (charge coefficient) legal
    ((crossCommutes_charge_iff coefficient left right).2 lawful) _

/-- **With all coefficients commuting, every permutation keeps the account.** -/
theorem account_perm (commute : ∀ a b, Commute (coefficient a) (coefficient b))
    {first second : List ι} (permutation : first.Perm second) :
    account coefficient first = account coefficient second := by
  rw [account_eq_run, account_eq_run]
  exact foldl_perm (charge coefficient) ((actionsCommute_charge_iff coefficient).2 commute)
    permutation 1

end Charging

/-! ## Controls -/

/-- **Positive**: in a commutative monoid every legal interleaving keeps the
account. -/
theorem commutative_account_shuffle {ι M : Type} [CommMonoid M] (coefficient : ι → M)
    {left right trace : List ι} (legal : Shuffle left right trace) (before : List ι) :
    account coefficient (before ++ trace) = account coefficient (before ++ left ++ right) :=
  account_shuffle coefficient (fun a _ b _ => Commute.all (coefficient a) (coefficient b)) legal
    before

/-- **Negative**: two different letters of a free monoid do not cross commute,
and the two serial interleavings of `[0]` and `[1]` have different accounts. -/
theorem free_letters_do_not_cross_commute :
    ¬ CrossCommutes (charge (FreeMonoid.of : ℕ → FreeMonoid ℕ)) [0] [1] ∧
      account (FreeMonoid.of : ℕ → FreeMonoid ℕ) ([0] ++ [1]) ≠
        account (FreeMonoid.of : ℕ → FreeMonoid ℕ) ([1] ++ [0]) := by
  refine ⟨fun cross => ?_, fun same => ?_⟩
  · exact free_monoid_tile_fails.2
      (((crossCommutes_charge_iff _ [0] [1]).1 cross) 0 List.mem_cons_self 1 List.mem_cons_self)
  · exact free_monoid_tile_fails.1 same

/-- The coefficients of the block-move control: a transposition `(0 1)` and a
transposition `(1 2)`. -/
def transposition : Bool → Equiv.Perm (Fin 3)
  | true => Equiv.swap 0 1
  | false => Equiv.swap 1 2

/-- **The pairwise condition is sufficient, not necessary.**  Moving `(0 1)`
across the block `[(1 2), (1 2)]` keeps the account, since the block's product
is the identity, while the charging action does not cross commute. -/
theorem block_move_without_cross_commutation :
    account transposition ([] ++ [true] ++ [false, false]) =
        account transposition ([] ++ [false, false] ++ [true]) ∧
      ¬ CrossCommutes (charge transposition) [true] [false, false] := by
  refine ⟨?_, fun cross => ?_⟩
  · have moved := (product_commutes_factor_does_not).1
    exact moved
  · exact (product_commutes_factor_does_not).2
      (((crossCommutes_charge_iff transposition [true] [false, false]).1 cross) true
        List.mem_cons_self false List.mem_cons_self)

end Mettapedia.GSLT.Distinction.ActionCommutation
