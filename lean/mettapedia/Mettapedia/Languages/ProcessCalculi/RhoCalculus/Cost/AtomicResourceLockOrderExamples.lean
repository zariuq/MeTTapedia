import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.AtomicResourceLockOrder

/-!
# Ordered occurrence-lock examples

The first finite state has a two-edge wait chain whose ranks increase, so the
general no-cycle theorem applies.  The second state reverses one acquisition
order: it contains a concrete mutual-wait cycle and therefore fails the
ordered-acquisition invariant.
-/

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost

namespace AtomicResourceLockOrderExamples

open OrderedOccurrenceLocks

inductive Transaction
  | alice
  | bob
  | carol
  deriving DecidableEq, Fintype

namespace OrderedChain

def owner (resource : Fin 3) : Option Transaction :=
  if resource = 0 then some .bob
  else if resource = 1 then some .carol
  else none

def waiting : Transaction → Option (Fin 3)
  | .alice => some ⟨0, by decide⟩
  | .bob => some ⟨1, by decide⟩
  | .carol => none

def state : State Transaction 3 := ⟨owner, waiting⟩

theorem wellOrdered : WellOrdered state := by
  intro transaction requested held waiting_eq owner_eq
  fin_cases transaction <;>
    fin_cases requested <;>
    fin_cases held <;>
    simp [state, waiting, owner] at waiting_eq owner_eq ⊢

theorem alice_waitsFor_bob : WaitsFor state .alice .bob := by
  exact ⟨⟨0, by decide⟩, rfl, rfl⟩

theorem bob_waitsFor_carol : WaitsFor state .bob .carol := by
  exact ⟨⟨1, by decide⟩, rfl, rfl⟩

theorem alice_waitsFor_carol_transitively :
    Relation.TransGen (WaitsFor state) .alice .carol := by
  exact Relation.TransGen.tail
    (Relation.TransGen.single alice_waitsFor_bob) bob_waitsFor_carol

theorem has_no_wait_cycle (transaction : Transaction) :
    ¬Relation.TransGen (WaitsFor state) transaction transaction :=
  no_wait_cycle wellOrdered transaction

end OrderedChain

namespace ReversedAcquisition

def owner (resource : Fin 2) : Option Transaction :=
  if resource = 0 then some .alice else some .bob

def waiting : Transaction → Option (Fin 2)
  | .alice => some ⟨1, by decide⟩
  | .bob => some ⟨0, by decide⟩
  | .carol => none

def state : State Transaction 2 := ⟨owner, waiting⟩

theorem alice_waitsFor_bob : WaitsFor state .alice .bob := by
  exact ⟨⟨1, by decide⟩, rfl, rfl⟩

theorem bob_waitsFor_alice : WaitsFor state .bob .alice := by
  exact ⟨⟨0, by decide⟩, rfl, rfl⟩

theorem mutual_wait_cycle :
    Relation.TransGen (WaitsFor state) .alice .alice := by
  exact Relation.TransGen.tail
    (Relation.TransGen.single alice_waitsFor_bob) bob_waitsFor_alice

theorem not_wellOrdered : ¬WellOrdered state := by
  intro ordered
  have impossible : (1 : Fin 2) < 0 :=
    ordered .bob 0 1 rfl rfl
  omega

end ReversedAcquisition

end AtomicResourceLockOrderExamples

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost
