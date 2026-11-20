import Mathlib.Algebra.BigOperators.Group.Multiset.Basic
import Mathlib.Data.Multiset.AddSub
import Mathlib.Data.Multiset.Filter
import Mathlib.Data.Multiset.Powerset
import Mathlib.Logic.Relation

/-!
# Fixed banks of structural replication

A bank holds finite bodies that may be unfolded without taking their
registration. Only the equation allowing one copy of a body is assumed.
In particular, neither distributing replication over parallel composition
nor identifying two registrations is assumed.

For ordinary multiset rules, applying one rule modulo this equation has
exactly the successors found by exposing at most one copy per taken
occurrence. All witnesses for the same state and rule give one residual
class. For singleton bodies this specializes to a finite exact key:
retain the bank and omit explicit copies supplied by it.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Contracts.FixedReplication

universe u
variable {Atom : Type u}

/-- The bank itself is not quotiented by idempotence. -/
abbrev Bank (Atom : Type u) := Multiset (Multiset Atom)

def Available (bank : Bank Atom) (copies : Multiset (Multiset Atom)) : Prop :=
  ∀ body ∈ copies, body ∈ bank

inductive Unfold (bank : Bank Atom) : Multiset Atom → Multiset Atom → Prop
  | copy (rows : Multiset Atom) {body : Multiset Atom} (held : body ∈ bank) :
      Unfold bank rows (rows + body)

abbrev Equiv (bank : Bank Atom) := Relation.EqvGen (Unfold bank)

private theorem expose (bank : Bank Atom) (rows : Multiset Atom)
    (copies : Multiset (Multiset Atom)) (allowed : Available bank copies) :
    Equiv bank rows (rows + copies.sum) := by
  induction copies using Multiset.induction_on generalizing rows with
  | empty => simpa using Relation.EqvGen.refl (r := Unfold bank) rows
  | @cons body rest ih =>
      have present := allowed body (Multiset.mem_cons_self _ _)
      have remaining : Available bank rest := fun piece member =>
        allowed piece (Multiset.mem_cons_of_mem member)
      have thisCopy : Equiv bank rows (rows + body) := .rel _ _ (.copy rows present)
      simpa only [Multiset.sum_cons, add_assoc] using
        Relation.EqvGen.trans _ _ _ thisCopy (ih (rows + body) remaining)

/-- A common expansion characterizes equality without requiring a
global order of copies or a choice of canonical representative. -/
theorem equiv_iff_common (bank : Bank Atom) {a b : Multiset Atom} :
    Equiv bank a b ↔
      ∃ l r : Multiset (Multiset Atom), Available bank l ∧ Available bank r ∧
        a + l.sum = b + r.sum := by
  constructor
  · intro equivalent
    induction equivalent with
    | rel _ _ step =>
        cases step with
        | @copy body permitted =>
            exact ⟨{body}, 0, by simpa [Available] using permitted, by simp [Available], by simp⟩
    | refl rows =>
        exact ⟨0, 0, by simp [Available], by simp [Available], rfl⟩
    | symm _ _ _ ih =>
        obtain ⟨l, r, hl, hr, same⟩ := ih
        exact ⟨r, l, hr, hl, same.symm⟩
    | trans a b c _ _ ih₁ ih₂ =>
        obtain ⟨l, r, hl, hr, first⟩ := ih₁
        obtain ⟨l', r', hl', hr', second⟩ := ih₂
        refine ⟨l + l', r' + r, ?_, ?_, ?_⟩
        · intro body member
          exact (Multiset.mem_add.mp member).elim (hl body) (hl' body)
        · intro body member
          exact (Multiset.mem_add.mp member).elim (hr' body) (hr body)
        simp only [Multiset.sum_add, ← add_assoc, first]
        rw [add_right_comm b r.sum l'.sum, second]
  · rintro ⟨l, r, hl, hr, same⟩
    exact .trans _ _ _ (expose _ _ l hl)
      (.symm _ _ (same ▸ expose bank b r hr))

theorem equiv_frame (bank : Bank Atom) {a b : Multiset Atom} (equal : Equiv bank a b)
    (frame : Multiset Atom) : Equiv bank (frame + a) (frame + b) := by
  obtain ⟨l, r, hl, hr, same⟩ := (equiv_iff_common bank).mp equal
  exact (equiv_iff_common bank).mpr ⟨l, r, hl, hr,
    by simpa only [add_assoc] using congrArg (frame + ·) same⟩

theorem equiv_cancel_frame (bank : Bank Atom) {a b frame : Multiset Atom}
    (equal : Equiv bank (frame + a) (frame + b)) : Equiv bank a b := by
  obtain ⟨l, r, hl, hr, same⟩ := (equiv_iff_common bank).mp equal
  exact (equiv_iff_common bank).mpr
    ⟨l, r, hl, hr, add_left_cancel (a := frame) (by simpa only [add_assoc] using same)⟩

/-- The universal observer condition for the additive quotient: exactly
the additive maps that annihilate the supplied bodies descend. In
particular a charge for materializing a body is not part of this
structural equality. -/
theorem additive_observer_descends_iff {Measure : Type*} [AddMonoid Measure]
    (bank : Bank Atom) (measure : Multiset Atom →+ Measure) :
    (∀ {a b}, Equiv bank a b → measure a = measure b) ↔
      ∀ body ∈ bank, measure body = 0 := by
  constructor
  · intro invariant body present
    simpa using (invariant (Relation.EqvGen.rel _ _ (Unfold.copy 0 present))).symm
  · intro invisible a b equal
    induction equal with
    | rel _ _ step =>
        cases step with
        | copy held => rw [map_add, invisible _ held, add_zero]
    | refl _ => rfl
    | symm _ _ _ ih => exact ih.symm
    | trans _ _ _ _ _ first second => exact first.trans second

section ExecutableBounds

variable [DecidableEq Atom]

omit [DecidableEq Atom] in
private theorem supplier {atom : Atom} {pool : Multiset (Multiset Atom)}
    (member : atom ∈ pool.sum) : ∃ body ∈ pool, atom ∈ body := by
  induction pool using Multiset.induction_on with
  | empty => simp at member
  | @cons head tail ih =>
      rw [Multiset.sum_cons, Multiset.mem_add] at member
      rcases member with first | later
      · exact ⟨head, Multiset.mem_cons_self _ _, first⟩
      · obtain ⟨body, held, contains⟩ := ih later
        exact ⟨body, Multiset.mem_cons_of_mem held, contains⟩

/-- Trim an arbitrary witness: for each requested occurrence either
use one in the currently exposed stock or expose one supplying body.
Other occurrences in that body can serve later requests. -/
theorem bounded_cover (demand stock : Multiset Atom) (pool : Multiset (Multiset Atom))
    (available : demand ≤ stock + pool.sum) :
    ∃ used ≤ pool, used.card ≤ demand.card ∧ demand ≤ stock + used.sum := by
  induction demand using Multiset.induction_on generalizing stock pool with
  | empty => exact ⟨0, Multiset.zero_le _, by simp, Multiset.zero_le _⟩
  | @cons atom rest ih =>
      by_cases present : atom ∈ stock
      · have after : rest ≤ stock.erase atom + pool.sum := by
          rw [← Multiset.cons_le_cons_iff atom, ← Multiset.cons_add, Multiset.cons_erase present]
          exact available
        obtain ⟨used, subset, bound, enough⟩ := ih _ _ after
        refine ⟨used, subset, bound.trans (by simp), ?_⟩
        rw [← Multiset.cons_erase present, Multiset.cons_add, Multiset.cons_le_cons_iff]
        exact enough
      · have inPool : atom ∈ pool.sum := by
          rcases Multiset.mem_add.mp (Multiset.mem_of_le available (Multiset.mem_cons_self _ _)) with h | h
          · exact (present h).elim
          · exact h
        obtain ⟨body, held, supplies⟩ := supplier inPool
        have copies : pool.sum = body + (pool.erase body).sum := (Multiset.sum_erase held).symm
        have inExposed : atom ∈ stock + body := Multiset.mem_add.mpr (.inr supplies)
        have after : rest ≤ (stock + body).erase atom + (pool.erase body).sum := by
          rw [← Multiset.cons_le_cons_iff atom, ← Multiset.cons_add, Multiset.cons_erase inExposed,
            add_assoc, ← copies]
          exact available
        obtain ⟨used, subset, bound, enough⟩ := ih _ _ after
        refine ⟨body ::ₘ used, ?_, by simpa only [Multiset.card_cons] using Nat.succ_le_succ bound, ?_⟩
        · exact (Multiset.cons_erase held) ▸ Multiset.cons_le_cons _ subset
        · rw [Multiset.sum_cons, ← add_assoc, ← Multiset.cons_erase inExposed, Multiset.cons_add,
            Multiset.cons_le_cons_iff]
          exact enough

/-- Take and make modulo the structural equation, with no bound or
direction on the equations used before or after the rule. -/
def Step (bank : Bank Atom) (take make source target : Multiset Atom) : Prop :=
  ∃ rest, Equiv bank source (take + rest) ∧ Equiv bank (make + rest) target

/-- Exact one-step search by bounded unfolding, even though the source
equivalence also allows folding. The bound counts rule inputs, not
steps in an execution or the size of its live store. -/
theorem step_iff_bounded_exposure {bank : Bank Atom} {take make source target : Multiset Atom} :
    Step bank take make source target ↔
      ∃ copies : Multiset (Multiset Atom), Available bank copies ∧ copies.card ≤ take.card ∧
        ∃ rest, source + copies.sum = take + rest ∧ Equiv bank (make + rest) target := by
  constructor
  · rintro ⟨rest, unfoldSource, closeTarget⟩
    obtain ⟨l, r, hl, hr, same⟩ := (equiv_iff_common bank).mp unfoldSource
    have enough : take ≤ source + l.sum := by
      rw [same, add_assoc]
      exact Multiset.le_add_right _ _
    obtain ⟨used, subset, bound, exposure⟩ := bounded_cover take source l enough
    obtain ⟨unused, unusedEq⟩ := Multiset.le_iff_exists_add.mp subset
    obtain ⟨nextRest, newSplit⟩ := Multiset.le_iff_exists_add.mp exposure
    have left : Available bank used := fun body member => hl body (Multiset.mem_of_le subset member)
    have right : Available bank unused := fun body member =>
      hl body (unusedEq ▸ Multiset.mem_add.mpr (.inr member))
    have residual : Equiv bank nextRest rest := by
      apply (equiv_iff_common bank).mpr
      refine ⟨unused, r, right, hr, add_left_cancel (a := take) ?_⟩
      rw [← add_assoc, ← add_assoc, ← newSplit, add_assoc, ← Multiset.sum_add, ← unusedEq]
      exact same
    exact ⟨used, left, bound, nextRest, newSplit,
      .trans _ _ _ (equiv_frame bank residual make) closeTarget⟩
  · rintro ⟨copies, allowed, _, rest, split, later⟩
    exact ⟨rest, split ▸ expose bank source copies allowed, later⟩

omit [DecidableEq Atom] in
/-- Varying only the structural witness cannot create another
successor class for the same selected take and make. -/
theorem step_residual_unique {bank : Bank Atom} {take make source a b : Multiset Atom}
    (first : Step bank take make source a) (second : Step bank take make source b) :
    Equiv bank a b := by
  obtain ⟨r, fromR, toA⟩ := first
  obtain ⟨s, fromS, toB⟩ := second
  have common : Equiv bank r s :=
    equiv_cancel_frame bank (.trans _ _ _ (.symm _ _ fromR) fromS)
  exact .trans _ _ _ (.symm _ _ toA) (.trans _ _ _ (equiv_frame bank common make) toB)

/-- A finite search space for exposure witnesses. This is a reference
enumeration, not a choice of scheduling or of a matching index. -/
def boundedCandidates (bank : Bank Atom) (arity : Nat) : Multiset (Multiset (Multiset Atom)) :=
  ((arity • bank).powerset).filter fun used => used.card ≤ arity

theorem mem_boundedCandidates {bank : Bank Atom} {arity : Nat}
    {used : Multiset (Multiset Atom)} :
    used ∈ boundedCandidates bank arity ↔ Available bank used ∧ used.card ≤ arity := by
  rw [boundedCandidates, Multiset.mem_filter, Multiset.mem_powerset]
  constructor
  · rintro ⟨sub, size⟩
    exact ⟨fun body member => bank.smul_subset_self arity (Multiset.mem_of_le sub member), size⟩
  · rintro ⟨allowed, size⟩
    have support : used ⊆ bank := fun {body} member => allowed body member
    have mul : used.card • bank ≤ arity • bank := by
      apply Multiset.le_iff_count.mpr
      intro body
      simp only [Multiset.count_nsmul]
      exact Nat.mul_le_mul_right _ size
    exact ⟨((Multiset.le_card_smul_iff_subset).mpr support).trans mul, size⟩

theorem step_iff_finite_search {bank : Bank Atom} {take make source target : Multiset Atom} :
    Step bank take make source target ↔
      ∃ copies ∈ boundedCandidates bank take.card, ∃ rest,
        source + copies.sum = take + rest ∧ Equiv bank (make + rest) target := by
  rw [step_iff_bounded_exposure]
  constructor
  · rintro ⟨copies, allowed, size, tail⟩
    exact ⟨copies, mem_boundedCandidates.mpr ⟨allowed, size⟩, tail⟩
  · rintro ⟨copies, admissible, tail⟩
    obtain ⟨allowed, size⟩ := mem_boundedCandidates.mp admissible
    exact ⟨copies, allowed, size, tail⟩

/-- Only one body per missing label is needed. Which body the lookup
chooses is independent of successor-class semantics. -/
structure SupplyIndex (bank : Bank Atom) where
  pick : Atom → Option (Multiset Atom)
  sound : ∀ {atom body}, pick atom = some body → body ∈ bank ∧ atom ∈ body
  complete : ∀ {atom body}, body ∈ bank → atom ∈ body → (pick atom).isSome = true

omit [DecidableEq Atom] in
private theorem chosenCovers {bank : Bank Atom} (index : SupplyIndex bank)
    (shortage : Multiset Atom) (supply : ∀ atom ∈ shortage, (index.pick atom).isSome = true) :
    shortage ≤ (shortage.filterMap index.pick).sum := by
  induction shortage using Multiset.induction_on with
  | empty => exact Multiset.zero_le _
  | cons atom rest ih =>
      have tail : ∀ a ∈ rest, (index.pick a).isSome = true :=
        fun a member => supply a (Multiset.mem_cons_of_mem member)
      have selected := supply atom (Multiset.mem_cons_self _ _)
      cases chosen : index.pick atom with
      | none => simp [chosen] at selected
      | some body =>
          rw [Multiset.filterMap_cons_some index.pick atom rest chosen,
            Multiset.sum_cons, ← Multiset.singleton_add]
          exact add_le_add (Multiset.singleton_le.mpr (index.sound chosen).2) (ih tail)

/-- The fast path consults only the missing occurrences and never
enumerates the unfolding witnesses or decodes an equation key. -/
def guidedSuccessor {bank : Bank Atom} (index : SupplyIndex bank) (take make source : Multiset Atom) :
    Option (Multiset Atom) :=
  let missing := take - source
  if ∀ atom ∈ missing, (index.pick atom).isSome = true then
    some (make + (source + (missing.filterMap index.pick).sum - take))
  else none

/-- Exposing any one certified supplier for each missing occurrence
preserves and reflects the entire successor class of a selected rule.
It does not identify distinct rules or choose matches on their behalf. -/
theorem step_iff_guided_successor {bank : Bank Atom} (index : SupplyIndex bank)
    {take make source target : Multiset Atom} :
    Step bank take make source target ↔
      ∃ result, guidedSuccessor index take make source = some result ∧ Equiv bank result target := by
  let missing := take - source
  let copies := missing.filterMap index.pick
  let grown := source + copies.sum
  let candidate := make + (grown - take)
  let covered := ∀ atom ∈ missing, (index.pick atom).isSome = true
  have sound (ready : covered) : Step bank take make source candidate := by
    have allowed : Available bank copies := by
      intro body present
      obtain ⟨_, _, chosen⟩ := (Multiset.mem_filterMap index.pick missing).mp present
      exact (index.sound chosen).1
    have enough : take ≤ grown := le_add_tsub.trans
      (Multiset.add_le_add_left (chosenCovers index missing ready))
    have equal : grown = take + (grown - take) := by
      rw [add_comm]
      exact (Multiset.sub_add_cancel enough).symm
    exact ⟨grown - take, equal ▸ expose bank source copies allowed, .refl _⟩
  change Step bank take make source target ↔
    ∃ result, (if covered then some candidate else none) = some result ∧ Equiv bank result target
  constructor
  · intro step
    have ready : covered := by
      intro atom short
      obtain ⟨plan, allowed, _, rest, split, _⟩ := step_iff_bounded_exposure.mp step
      have enough : take ≤ source + plan.sum := Multiset.le_iff_exists_add.mpr ⟨rest, split⟩
      have deficit := Multiset.mem_sub.mp short
      have bound := Multiset.le_iff_count.mp enough atom
      rw [Multiset.count_add] at bound
      have available : 0 < plan.sum.count atom := by omega
      obtain ⟨body, inPlan, hasAtom⟩ := supplier (Multiset.count_pos.mp available)
      exact index.complete (allowed body inPlan) hasAtom
    exact ⟨candidate, if_pos ready, step_residual_unique (sound ready) step⟩
  · rintro ⟨result, computed, equivalent⟩
    by_cases ready : covered
    · rw [if_pos ready, Option.some.injEq] at computed
      subst result
      obtain ⟨rest, before, after⟩ := sound ready
      exact ⟨rest, before, .trans _ _ _ after equivalent⟩
    · simp [ready] at computed

end ExecutableBounds

section SingletonBodies

variable [DecidableEq Atom]

/-- A key for the one-body-per-copy profile, retaining all unsupplied
occurrences and leaving the bank untouched. -/
def finitePart (held : Multiset Atom) (rows : Multiset Atom) : Multiset Atom :=
  rows.filter fun atom => atom ∉ held

def singletonBank (held : Multiset Atom) : Bank Atom :=
  held.map fun atom => {atom}

theorem finitePart_equiv (held rows : Multiset Atom) :
    Equiv (singletonBank held) rows (finitePart held rows) := by
  induction rows using Multiset.induction_on with
  | empty => simpa [finitePart] using Relation.EqvGen.refl (r := Unfold (singletonBank held)) 0
  | @cons atom tail ih =>
      by_cases present : atom ∈ held
      · rw [finitePart, Multiset.filter_cons_of_neg (p := fun name => name ∉ held) tail (not_not_intro present)]
        have copy : ({atom} : Multiset Atom) ∈ singletonBank held :=
          Multiset.mem_map.mpr ⟨atom, present, rfl⟩
        have rolled : Equiv (singletonBank held) tail (atom ::ₘ tail) := by
          simpa only [add_comm tail, Multiset.singleton_add] using
            (Relation.EqvGen.rel _ _ (Unfold.copy tail copy))
        exact .trans _ _ _ (.symm _ _ rolled) ih
      · rw [finitePart, Multiset.filter_cons_of_pos (p := fun name => name ∉ held) tail present]
        change Equiv (singletonBank held) (atom ::ₘ tail) (atom ::ₘ finitePart held tail)
        simpa only [Multiset.singleton_add] using
          equiv_frame (singletonBank held) ih {atom}

theorem finitePart_eq_iff (held rows other : Multiset Atom) :
    finitePart held rows = finitePart held other ↔ Equiv (singletonBank held) rows other := by
  constructor
  · intro same
    exact .trans _ _ _ (finitePart_equiv held rows)
      (.symm _ _ (same ▸ finitePart_equiv held other))
  · intro eq
    induction eq with
    | rel _ _ step =>
        cases step with
        | @copy body permitted =>
            obtain ⟨atom, member, rfl⟩ := Multiset.mem_map.mp permitted
            simp [finitePart, Multiset.filter_add, member]
    | refl _ => rfl
    | symm _ _ _ ih => exact ih.symm
    | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

theorem finitePart_add (held first second : Multiset Atom) :
    finitePart held (first + second) = finitePart held first + finitePart held second :=
  Multiset.filter_add (fun atom => atom ∉ held) first second

/-- On the singleton-body key one can run the reaction directly.
No unfold enumeration, choice among witnesses, or reconstruction of
copies is needed. -/
theorem singleton_step_iff (held take make source target : Multiset Atom) :
    Step (singletonBank held) take make source target ↔
      finitePart held take ≤ finitePart held source ∧
      finitePart held target =
        (finitePart held source - finitePart held take) + finitePart held make := by
  constructor
  · rintro ⟨rest, before, finished⟩
    have input := (finitePart_eq_iff held ..).mpr before
    have output := (finitePart_eq_iff held ..).mpr finished
    rw [finitePart_add] at input output
    refine ⟨Multiset.le_iff_exists_add.mpr ⟨_, input⟩, ?_⟩
    rw [← output, input, add_tsub_cancel_left, add_comm]
  · rintro ⟨ready, after⟩
    let rest := finitePart held source - finitePart held take
    have split : finitePart held source = finitePart held take + rest := by
      rw [add_comm]
      exact (Multiset.sub_add_cancel ready).symm
    have stable : finitePart held rest = rest := by
      apply Multiset.filter_eq_self.mpr
      intro atom member
      have belongs := Multiset.mem_of_le (Multiset.sub_le_self (finitePart held source) _) member
      exact (Multiset.mem_filter.mp belongs).2
    refine ⟨rest, (finitePart_eq_iff held ..).mp ?_, (finitePart_eq_iff held ..).mp ?_⟩
    · rw [finitePart_add, stable]
      exact split
    · rw [finitePart_add, stable, after, add_comm]

/-- A guarded replicated receive is a permanent supply of the
receive role, not a permanent supply of the distinct offer role. -/
theorem guarded_singleton_step_iff {listener offer : Atom} (roles : offer ≠ listener)
    (make source target : Multiset Atom) :
    Step (singletonBank {listener}) ({offer, listener} : Multiset Atom) make source target ↔
      offer ∈ finitePart {listener} source ∧
      finitePart {listener} target =
        (finitePart {listener} source).erase offer + finitePart {listener} make := by
  have selected : finitePart ({listener} : Multiset Atom) ({offer, listener} : Multiset Atom) =
      {offer} := by
    change finitePart {listener} ({offer} + {listener}) = {offer}
    rw [finitePart_add]
    have included : finitePart ({listener} : Multiset Atom) {offer} = {offer} := by
      apply Multiset.filter_eq_self.mpr
      simpa [finitePart] using roles
    have excluded : finitePart ({listener} : Multiset Atom) {listener} = 0 := by
      apply Multiset.filter_eq_nil.mpr
      simp
    rw [included, excluded, add_zero]
  rw [singleton_step_iff, selected, Multiset.sub_singleton]
  simp

end SingletonBodies

namespace Controls

private def listenerIndex : SupplyIndex (singletonBank ({true} : Multiset Bool)) where
  pick atom := if atom then some {true} else none
  sound := by
    intro atom body returned
    cases atom with
    | false => simp at returned
    | true =>
        have same : ({true} : Multiset Bool) = body := by simpa using returned
        subst body
        simp [singletonBank]
  complete := by
    intro atom body held inside
    have same : body = {true} := by simpa [singletonBank] using held
    subst body
    have yes : atom = true := Multiset.mem_singleton.mp inside
    simp [yes]

theorem indexed_contact_still_needs_an_offer :
    guidedSuccessor listenerIndex {true, false} {false} {false} = some {false} ∧
    guidedSuccessor listenerIndex {true, false} {false} 0 = none := by
  decide

/-- Extra unfolds cannot change the residue class of a guarded response. -/
theorem guarded_response :
    Step (singletonBank ({true} : Multiset Bool)) ({true, false} : Multiset Bool) {false} {false} {false} := by
  apply step_iff_bounded_exposure.mpr
  refine ⟨{{true}}, ?_, by decide, 0, by decide, by simpa using Relation.EqvGen.refl _⟩
  simp [Available, singletonBank]

/-- Unfolding a grouped body supplies both atoms, not an equation that
erases either one independently. -/
theorem grouped_body_not_individually_erasable :
    ¬ Equiv ({{true, false}} : Bank Bool) {true} 0 := by
  intro eq
  have invariant {a b : Multiset Bool} (same : Equiv ({{true, false}} : Bank Bool) a b) :
      a.count true + b.count false = b.count true + a.count false := by
    induction same with
    | rel _ _ step =>
        cases step with
        | @copy body held =>
            have : body = {true, false} := Multiset.mem_singleton.mp held
            subst body
            simp only [Multiset.count_add]
            have votes : ({true, false} : Multiset Bool).count true =
                ({true, false} : Multiset Bool).count false := by decide
            omega
    | refl _ => rfl
    | symm _ _ _ ih => exact ih.symm
    | trans _ _ _ _ _ ih₁ ih₂ => omega
  have impossible := invariant eq
  simp at impossible

end Controls

#print axioms equiv_iff_common
#print axioms equiv_cancel_frame
#print axioms additive_observer_descends_iff
#print axioms bounded_cover
#print axioms step_iff_bounded_exposure
#print axioms step_residual_unique
#print axioms step_iff_finite_search
#print axioms step_iff_guided_successor
#print axioms finitePart_eq_iff
#print axioms singleton_step_iff
#print axioms guarded_singleton_step_iff
#print axioms Controls.guarded_response
#print axioms Controls.indexed_contact_still_needs_an_offer
#print axioms Controls.grouped_body_not_individually_erasable

end Mettapedia.GSLT.Contracts.FixedReplication
