import Mathlib.CategoryTheory.Category.Preorder
import Mettapedia.Logic.LinearLogic.KnowledgeTensorControls
import Mettapedia.Logic.LinearLogic.KnowledgeTensorTraces
import Mettapedia.Logic.LinearLogic.KnowledgeTensorFrames
import Mettapedia.Logic.LinearLogic.KnowledgeTensorFragments
import Mettapedia.Logic.LinearLogic.KnowledgeTensorSequent

/-!
# Controls for the lent zone, for independence, for frames and for the whole calculus

* **Lent atoms.** Two readers of one occurrence run in both orders from that single occurrence
  (`two_readers_share_one_occurrence`). Read as returned premises side by side they would need two
  copies (`side_by_side_premises_need_two_copies`). A lent atom is never taken
  (`a_lent_atom_is_not_taken`), while an owned one is (`an_owned_atom_is_taken`).
* **Independence.** Two uses that each take and remake the one occurrence run in both orders to
  the same state (`spinners_commute`) and are not independent (`spinners_are_not_independent`).
  A guard that needs the other use's tell breaks independence
  (`asker_and_teller_are_not_independent`). The two readers are related by a swap
  (`the_two_readers_swap`); the asker and the teller are related neither by swaps nor by
  interchange (`asker_and_teller_do_not_swap`, `asker_and_teller_do_not_interchange`).
* **Sequents.** The two readers have a tensor sequent over the one lent occurrence
  (`the_two_readers_have_a_tensor_sequent`). No sequent discards a leftover
  (`sequents_do_not_discard`).
* **The whole calculus.** The absence control, read in the whole calculus at one frame, runs
  alone and is refused beside `c` (`absence_runs_in_the_whole_calculus`,
  `absence_is_refused_in_the_whole_calculus`).
* **Frames.** Frames are the natural numbers, a frame map adds names, atoms of a frame are its
  names. The declaration that makes the last name of its target frame makes a fresh atom
  (`names_are_fresh`). The declaration that makes a carried atom does not (`reuse_is_not_fresh`).
-/

set_option autoImplicit false

namespace Mettapedia.Logic.LinearLogic.KnowledgeTensorControls

open KnowledgeTensor
open _root_.CategoryTheory
open Item Decl

/-! ## Lent atoms -/

def twoReaders : System Knowledge Item Bool where
  take := fun _ => 0
  read := fun _ => {a}
  make := fun
    | false => {b}
    | true => {c}
  tell := fun _ => Set.univ
  guard := fun _ _ => True
  guard_mono := fun _ _ _ _ _ => True.intro

theorem two_readers_share_one_occurrence :
    twoReaders.Run Set.univ (twoReaders.take false + twoReaders.take true + {a}) [false, true]
        (Set.univ ⊓ twoReaders.tell false ⊓ (Set.univ ⊓ twoReaders.tell true))
        (twoReaders.make false + twoReaders.make true + {a}) ∧
      twoReaders.Run Set.univ (twoReaders.take false + twoReaders.take true + {a}) [true, false]
        (Set.univ ⊓ twoReaders.tell false ⊓ (Set.univ ⊓ twoReaders.tell true))
        (twoReaders.make false + twoReaders.make true + {a}) :=
  System.shared_read_diamond false true Set.univ {a} le_rfl le_rfl True.intro True.intro

theorem side_by_side_premises_need_two_copies :
    ¬ (twoReaders.premises false + twoReaders.premises true ≤ ({a} : Multiset Item)) := by
  intro fits
  exact absurd (Multiset.card_le_card fits) (by decide)

def taker : System Knowledge Item Unit where
  take := fun _ => {a}
  read := fun _ => 0
  make := fun _ => {b}
  tell := fun _ => Set.univ
  guard := fun _ _ => True
  guard_mono := fun _ _ _ _ _ => True.intro

theorem an_owned_atom_is_taken :
    taker.RunUnder (taker.read ()) Set.univ (taker.take ()) [()] (Set.univ ⊓ taker.tell ())
      (taker.make ()) :=
  System.Lends.run (System.Lends.rule () Set.univ True.intro)

theorem a_lent_atom_is_not_taken :
    ¬ ∃ (known : Knowledge) (after : Multiset Item), taker.RunUnder {a} Set.univ 0 [()] known after := by
  rintro ⟨known, after, run⟩
  cases run with
  | fire fires later =>
      obtain ⟨frame, source, _, _, _, _⟩ := fires
      have inside : a ∈ taker.take () + frame :=
        Multiset.mem_add.mpr (Or.inl (Multiset.mem_singleton_self a))
      rw [← source] at inside
      exact Multiset.notMem_zero a inside

/-! ## Independence -/

def spinners : System Knowledge Item Bool where
  take := fun _ => {a}
  read := fun _ => 0
  make := fun _ => {a}
  tell := fun _ => Set.univ
  guard := fun _ _ => True
  guard_mono := fun _ _ _ _ _ => True.intro

theorem spinner_fires (which : Bool) (known : Knowledge) :
    spinners.Fires which known {a} (known ⊓ spinners.tell which) {a} := by
  refine ⟨0, ?_, True.intro, rfl, ?_⟩
  · show ({a} : Multiset Item) = ({a} + 0) + 0
    rw [add_zero, add_zero]
  · show ({a} : Multiset Item) = (0 + {a}) + 0
    rw [add_zero, zero_add]

theorem spinners_commute :
    spinners.Run Set.univ {a} [false, true]
        (Set.univ ⊓ spinners.tell false ⊓ spinners.tell true) {a} ∧
      spinners.Run Set.univ {a} [true, false]
        (Set.univ ⊓ spinners.tell true ⊓ spinners.tell false) {a} :=
  ⟨System.Run.fire (spinner_fires false _) (System.Run.fire (spinner_fires true _) (System.Run.done _ _)),
    System.Run.fire (spinner_fires true _) (System.Run.fire (spinner_fires false _) (System.Run.done _ _))⟩

theorem spinners_are_not_independent (known : Knowledge) :
    ¬ spinners.Independent false true known {a} := by
  rintro ⟨shared, source, _, _, _, _⟩
  have sizes := congrArg Multiset.card source
  rw [Multiset.card_add, Multiset.card_add] at sizes
  have one : Multiset.card ({a} : Multiset Item) = 1 := Multiset.card_singleton a
  have first : Multiset.card (spinners.take false) = 1 := Multiset.card_singleton a
  have second : Multiset.card (spinners.take true) = 1 := Multiset.card_singleton a
  omega

theorem asker_and_teller_are_not_independent (Γ : Multiset Item) :
    ¬ askTell.Independent asker teller Set.univ Γ := by
  rintro ⟨_, _, _, _, asked, _⟩
  have held : (Set.univ ⊓ Set.univ : Set Bool) ≤ {true} := asked
  have impossible : false = true :=
    held (show false ∈ (Set.univ ⊓ Set.univ : Set Bool) from ⟨True.intro, True.intro⟩)
  exact absurd impossible (by decide)

theorem the_two_readers_swap :
    System.Swaps twoReaders Set.univ (twoReaders.take false + twoReaders.take true + {a})
      [false, true] [true, false] := by
  refine System.Swaps.swap (before := []) (after := []) ?_ (System.Swaps.same _)
  intro k₁ Γ₁ start
  cases start
  exact ⟨{a}, rfl, le_rfl, le_rfl, True.intro, True.intro⟩

theorem asker_and_teller_do_not_swap :
    ¬ System.Swaps askTell Set.univ start [teller, asker] [asker, teller] := by
  intro related
  exact asker_first_is_refused ⟨_, _, System.Swaps.run related teller_then_asker_runs⟩

theorem asker_and_teller_do_not_interchange :
    ¬ System.Interchanges askTell Set.univ start [teller, asker] [asker, teller] := by
  intro related
  exact asker_and_teller_do_not_swap
    ((System.interchanges_iff_swaps teller_then_asker_runs _).mp related)

/-! ## Sequents -/

theorem the_two_readers_have_a_tensor_sequent :
    twoReaders.Sequent {a} Set.univ
      (TensorSequent.atomContext (twoReaders.take false) +
        TensorSequent.atomContext (twoReaders.take true))
      ([false] ++ [true]) (Set.univ ⊓ twoReaders.tell false ⊓ (Set.univ ⊓ twoReaders.tell true))
      (TensorSequent.Formula.tensor (TensorSequent.Formula.ofMultiset (twoReaders.make false))
        (TensorSequent.Formula.ofMultiset (twoReaders.make true))) :=
  System.Sequent.tensorR (System.Sequent.transition false Set.univ True.intro)
    (System.Sequent.transition true Set.univ True.intro)

theorem sequents_do_not_discard {known known' : Knowledge} {uses : List Unit} :
    ¬ lookup.Sequent 0 known (TensorSequent.atomContext ({a} + {c})) uses known'
      (TensorSequent.Formula.ofMultiset {a}) := by
  intro proof
  have run := (System.sequent_iff_run _ _ _ _ _).mp proof
  have counted := a_leftover_is_not_discarded (System.Run.derives run)
  exact absurd counted (by decide)

/-! ## The whole calculus -/

theorem absence_runs_in_the_whole_calculus :
    ∃ along : (() : Unit) ⟶ (),
      absence.zoned.RunUnder () 0 Set.univ (absence.premises ()) ([()].map (Sigma.mk ())) () along
        (Set.univ ⊓ Set.univ) (absence.conclusions ()) :=
  (CheckedSystem.run_iff_zoned _ _ _ _ _).mp absence_fires_alone

theorem absence_is_refused_in_the_whole_calculus :
    ¬ ∃ along : (() : Unit) ⟶ (),
      absence.zoned.RunUnder () 0 Set.univ (absence.premises () + {c}) ([()].map (Sigma.mk ())) ()
        along (Set.univ ⊓ Set.univ) (absence.conclusions () + {c}) := by
  rintro ⟨along, run⟩
  exact absence_blocked ((CheckedSystem.run_iff_zoned _ _ _ _ _).mpr ⟨along, run⟩) rfl rfl

/-! ## Frames and fresh names -/

def names : IndexedSystem ℕ (fun _ => Set Bool) Fin (fun _ => Unit) where
  know := fun _ known => known
  know_id := fun _ => rfl
  know_comp := fun _ _ _ => rfl
  know_inf := fun _ _ _ => rfl
  carry := fun step atom => Fin.castLE (leOfHom step) atom
  carry_id := fun _ => rfl
  carry_comp := fun _ _ _ => rfl
  target := fun {a} _ => a + 1
  extend := fun {a} _ => homOfLE (Nat.le_succ a)
  take := fun _ => 0
  read := fun _ => 0
  make := fun {a} _ => {Fin.last a}
  tell := fun _ => Set.univ
  guard := fun _ _ => True
  guard_mono := fun _ _ _ _ _ => True.intro

theorem names_are_fresh (frame : ℕ) : names.Fresh (a := frame) () := by
  intro atom made old same
  have last : atom = Fin.last frame := Multiset.mem_singleton.mp made
  have value : old.val = frame := congrArg Fin.val (same.trans last)
  exact absurd value (Nat.ne_of_lt old.isLt)

/-- A fresh name is none of the names carried along, here read on a run of one firing. -/
theorem a_born_name_is_not_among_the_carried (frame : ℕ) (present : Multiset (Fin frame)) :
    Fin.last frame ∉ names.carried (names.extend (a := frame) ()) present :=
  (names_are_fresh frame).not_carried (Multiset.mem_singleton_self _) present

def reuse : IndexedSystem ℕ (fun _ => Set Bool) (fun frame => Fin (frame + 1)) (fun _ => Unit) where
  know := fun _ known => known
  know_id := fun _ => rfl
  know_comp := fun _ _ _ => rfl
  know_inf := fun _ _ _ => rfl
  carry := fun step atom => Fin.castLE (Nat.succ_le_succ (leOfHom step)) atom
  carry_id := fun _ => rfl
  carry_comp := fun _ _ _ => rfl
  target := fun {a} _ => a + 1
  extend := fun {a} _ => homOfLE (Nat.le_succ a)
  take := fun _ => 0
  read := fun _ => 0
  make := fun {a} _ => {Fin.castLE (Nat.succ_le_succ (Nat.le_succ a)) (Fin.last a)}
  tell := fun _ => Set.univ
  guard := fun _ _ => True
  guard_mono := fun _ _ _ _ _ => True.intro

theorem reuse_is_not_fresh (frame : ℕ) : ¬ reuse.Fresh (a := frame) () := by
  intro fresh
  exact fresh _ (Multiset.mem_singleton_self _) (Fin.last frame) rfl

end Mettapedia.Logic.LinearLogic.KnowledgeTensorControls
