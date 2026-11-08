import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.GuardLowering

/-!
# The cost of a guard, charged at its firing

A metered firing pays its price from a purse and is refused when the purse is short. Here the
price may read the configuration the firing fires from, so that a guard's own evaluation cost can
be charged: a scan of the store, the size of a certificate, a budget.

## Metered runs (`Metered`, `metered_iff`)

Metered runs are exactly the runs whose total price, read along the run, fits the purse. Metering
only removes runs.

## Site charges (`SiteCharge`)

A price that reads only the firing, and not the store, is a **site charge**. Its total is the sum
over the word (`total_eq_sum`), so it does not depend on the order of the firings
(`total_perm`): two interleavings of one causal history are funded alike.

* **The price of a checked certificate is a site charge** (`certificateCost`): one membership test
  of the datum, and for each state of the certificate one test of the predicate and one inclusion
  of its successors. So certified runs are metered exactly (`certified_metered_iff`), with the
  guard's own cost in the price.

## Control: a guard priced by the store it scans

A guard that scans the whole store costs the size of the store, which the other firings change.
Two independent firings, one making two occurrences and one reading, are runs in both orders and
end in the same configuration; priced by the scan, one order costs `2` and the other `4`, so a
purse of `3` funds one interleaving of the history and refuses the other (`scan_price_order`).
The guard's cost must be charged by what the firing observes (its own certificate, or the census
of its predicate query, `AnnotatedRuns.census_region_card`), not by the store it runs against.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.MeteredGuards

open Superposition (guarded syntactic clauseFiring_plain)
open GuardLowering (Template Runs runs_cons_iff ReadsDatum)
open GuardFragments

universe uT uO uI uR

variable {T : Type uT} {O : Type uO} [DecidableEq O] (label : O → T) {ι : Type uI}
  (template : ι → Template O T) (guard : ι → Prop) (price : Configuration T O → ι → ℕ)

/-- **Metered runs**: each firing pays its price, read at the configuration it fires from, from the
purse, and a firing whose price exceeds the purse is refused. -/
inductive Metered : ℕ → Configuration T O → List ι → Prop
  | nil (purse : ℕ) (C : Configuration T O) : Metered purse C []
  | cons {purse : ℕ} {C : Configuration T O} {i : ι} {rest : List ι}
      (admitted : (guarded (syntactic T) label).Admits (s := C) ((template i).withGuard (guard i)))
      (fits : price C i ≤ purse)
      (later : Metered (purse - price C i) ((template i).after label C) rest) :
      Metered purse C (i :: rest)

/-- The total price of a word, each firing priced at the configuration it fires from. -/
def total : Configuration T O → List ι → ℕ
  | _, [] => 0
  | C, i :: rest => price C i + total ((template i).after label C) rest

/-- **Metered runs are exactly the runs whose total price fits the purse.** -/
theorem metered_iff : ∀ (purse : ℕ) (C : Configuration T O) (w : List ι),
    Metered label template guard price purse C w ↔
      Runs label template guard C w ∧ total label template price C w ≤ purse
  | purse, C, [] => ⟨fun _ => ⟨.nil C, Nat.zero_le _⟩, fun _ => .nil purse C⟩
  | purse, C, i :: rest => by
      constructor
      · rintro (_ | ⟨admitted, fits, later⟩)
        obtain ⟨runs, bounded⟩ := (metered_iff (purse - price C i) _ rest).mp later
        refine ⟨.cons admitted runs, ?_⟩
        simp only [total]
        omega
      · rintro ⟨runs, bounded⟩
        cases runs with
        | cons admitted later =>
            simp only [total] at bounded
            exact .cons admitted (by omega)
              ((metered_iff (purse - price C i) _ rest).mpr ⟨later, by omega⟩)

/-- An admitted template leaves the knowledge plain, whatever its guard. -/
theorem plain_after {C : Configuration T O} {t : Template O T} {g : Prop}
    (admitted : (guarded (syntactic T) label).Admits (s := C) (t.withGuard g)) :
    Superposition.Plain (t.after label C) := by
  have plain := clauseFiring_plain label admitted
  exact plain

/-- **A site charge**: a price that reads only the firing. -/
def SiteCharge (cost : ι → ℕ) : Prop := ∀ C i, price C i = cost i

variable {label template price}

theorem total_eq_sum {cost : ι → ℕ} (site : SiteCharge price cost) :
    ∀ (C : Configuration T O) (w : List ι), total label template price C w = (w.map cost).sum
  | _, [] => rfl
  | C, i :: rest => by
      rw [total, site C i, total_eq_sum site _ rest, List.map_cons, List.sum_cons]

/-- **A site charge does not depend on the order of the firings.** -/
theorem total_perm {cost : ι → ℕ} (site : SiteCharge price cost) {w w' : List ι} (perm : w.Perm w')
    (C C' : Configuration T O) : total label template price C w = total label template price C' w' := by
  rw [total_eq_sum site, total_eq_sum site]
  exact (perm.map cost).sum_eq

/-! ## The price of a checked certificate -/

section Certificates

variable {R : Type uR} [DecidableEq R] (succ : R → Finset R)

/-- **The cost of checking a certificate**: one test of the datum's membership, and for each state
one test of the predicate and one inclusion of its successors, counted by their size. -/
def certificateCost (I : Finset R) : ℕ := 1 + I.sum fun e => 1 + (succ e).card

variable (label) (p : R → Bool) {embed : R → T}

/-- **Certified runs are metered exactly**, the guard's own check in the price. -/
theorem certified_metered_iff (base : ReadsDatum (O := O) embed → ℕ) (purse : ℕ)
    (C : Configuration T O) (v : List (ReadsDatum (O := O) embed × Finset R)) :
    Metered label (fun gc => gc.1.template) (fun gc => checkInvariant succ p gc.1.datum gc.2 = true)
        (fun _ gc => base gc.1 + certificateCost succ gc.2) purse C v ↔
      Runs label (fun gc => gc.1.template) (fun gc => checkInvariant succ p gc.1.datum gc.2 = true) C v ∧
        (v.map fun gc => base gc.1 + certificateCost succ gc.2).sum ≤ purse := by
  rw [metered_iff]
  have sum := total_eq_sum (label := label)
    (template := fun gc : ReadsDatum (O := O) embed × Finset R => gc.1.template)
    (price := fun (_ : Configuration T O) (gc : ReadsDatum (O := O) embed × Finset R) =>
      base gc.1 + certificateCost succ gc.2)
    (cost := fun gc => base gc.1 + certificateCost succ gc.2) (fun _ _ => rfl) C v
  rw [sum]

end Certificates

/-! ## Control: a guard priced by the store it scans -/

namespace Controls

open GuardLowering.Controls (probeLabel probeStart cycle belowThree)

/-- Make two occurrences. -/
def big : Template ℕ ℕ := ⟨[], [], [(1, 0), (2, 0)]⟩

/-- Read the occurrence `0`. -/
def small : Template ℕ ℕ := ⟨[], [(0, 0)], []⟩

/-- Both carry a checked certificate for the cyclic datum. -/
def certified : Template ℕ ℕ → Prop := fun _ => checkInvariant cycle belowThree 0 {0, 1, 2} = true

/-- The scan price: the size of the store. -/
def scan : Configuration ℕ ℕ → Template ℕ ℕ → ℕ := fun C _ => C.present.card

theorem certified_holds (t : Template ℕ ℕ) : certified t := by
  show checkInvariant cycle belowThree 0 {0, 1, 2} = true
  decide

theorem big_base (C : Configuration ℕ ℕ) (plain : Superposition.Plain C) (fresh1 : (1 : ℕ) ∉ C.present)
    (fresh2 : (2 : ℕ) ∉ C.present) : big.Base probeLabel C := by
  unfold Template.Base
  refine ⟨List.nodup_nil, by decide, fun _ member => by simp [big] at member,
    fun _ member => by simp [big] at member, ?_, plain⟩
  intro q member
  simp [big] at member
  rcases member with rfl | rfl
  · exact ⟨fresh1, rfl⟩
  · exact ⟨fresh2, rfl⟩

theorem small_base (C : Configuration ℕ ℕ) (plain : Superposition.Plain C) (present : (0 : ℕ) ∈ C.present) :
    small.Base probeLabel C := by
  unfold Template.Base
  refine ⟨List.nodup_nil, List.nodup_nil, ?_, fun _ member => by simp [small] at member,
    fun _ member => by simp [small] at member, plain⟩
  intro q member
  simp only [small, List.nil_append, List.mem_singleton] at member
  subst member
  exact ⟨present, rfl⟩

theorem start_plain : Superposition.Plain probeStart := by
  intro e member
  simp [probeStart] at member

theorem big_admitted (C : Configuration ℕ ℕ) (plain : Superposition.Plain C)
    (fresh1 : (1 : ℕ) ∉ C.present) (fresh2 : (2 : ℕ) ∉ C.present) :
    (guarded (syntactic ℕ) probeLabel).Admits (s := C) (big.withGuard (certified big)) :=
  (Template.admits_iff probeLabel C big _).mpr ⟨big_base C plain fresh1 fresh2, certified_holds big⟩

theorem small_admitted (C : Configuration ℕ ℕ) (plain : Superposition.Plain C)
    (present : (0 : ℕ) ∈ C.present) :
    (guarded (syntactic ℕ) probeLabel).Admits (s := C) (small.withGuard (certified small)) :=
  (Template.admits_iff probeLabel C small _).mpr ⟨small_base C plain present, certified_holds small⟩

theorem big_present : (big.after probeLabel probeStart).present = {0, 1, 2} := by
  rw [Template.present_after]
  decide

theorem small_present : (small.after probeLabel probeStart).present = {0} := by
  rw [Template.present_after]
  decide

theorem big_small_present : (small.after probeLabel (big.after probeLabel probeStart)).present = {0, 1, 2} := by
  rw [Template.present_after, big_present]
  decide

theorem small_big_present : (big.after probeLabel (small.after probeLabel probeStart)).present = {0, 1, 2} := by
  rw [Template.present_after, small_present]
  decide

theorem big_first_runs : Runs probeLabel id certified probeStart [big, small] := by
  have first := big_admitted probeStart start_plain (by decide) (by decide)
  refine .cons first (.cons (small_admitted _ (plain_after probeLabel first) ?_) (.nil _))
  show (0 : ℕ) ∈ (big.after probeLabel probeStart).present
  rw [big_present]
  decide

theorem small_first_runs : Runs probeLabel id certified probeStart [small, big] := by
  have first := small_admitted probeStart start_plain (by decide)
  refine .cons first (.cons (big_admitted _ (plain_after probeLabel first) ?_ ?_) (.nil _))
  · show (1 : ℕ) ∉ (small.after probeLabel probeStart).present
    rw [small_present]
    decide
  · show (2 : ℕ) ∉ (small.after probeLabel probeStart).present
    rw [small_present]
    decide

/-- **A guard priced by the store it scans funds one interleaving of a history and refuses the
other.** Both orders run and end with the same occurrences; the scan costs `4` in one order and
`2` in the other, and a purse of `3` funds only the second. -/
theorem scan_price_order :
    Runs probeLabel id certified probeStart [big, small] ∧
      Runs probeLabel id certified probeStart [small, big] ∧
      (small.after probeLabel (big.after probeLabel probeStart)).present =
        (big.after probeLabel (small.after probeLabel probeStart)).present ∧
      total probeLabel id scan probeStart [big, small] = 4 ∧
      total probeLabel id scan probeStart [small, big] = 2 ∧
      ¬ Metered probeLabel id certified scan 3 probeStart [big, small] ∧
      Metered probeLabel id certified scan 3 probeStart [small, big] := by
  have bigFirst : total probeLabel id scan probeStart [big, small] = 4 := by
    show probeStart.present.card + ((big.after probeLabel probeStart).present.card + 0) = 4
    rw [big_present]
    decide
  have smallFirst : total probeLabel id scan probeStart [small, big] = 2 := by
    show probeStart.present.card + ((small.after probeLabel probeStart).present.card + 0) = 2
    rw [small_present]
    decide
  refine ⟨big_first_runs, small_first_runs, by rw [big_small_present, small_big_present], bigFirst,
    smallFirst, fun metered => ?_, (metered_iff _ _ _ _ _ _ _).mpr ⟨small_first_runs, by omega⟩⟩
  have bounded := ((metered_iff _ _ _ _ _ _ _).mp metered).2
  omega

/-- **A site charge funds both interleavings alike.** -/
theorem site_charge_order (cost : Template ℕ ℕ → ℕ) :
    total probeLabel id (fun _ t => cost t) probeStart [big, small] =
      total probeLabel id (fun _ t => cost t) probeStart [small, big] :=
  total_perm (cost := cost) (fun _ _ => rfl) (List.Perm.swap small big []) _ _

end Controls

#print axioms metered_iff
#print axioms total_eq_sum
#print axioms total_perm
#print axioms certified_metered_iff
#print axioms Controls.big_first_runs
#print axioms Controls.small_first_runs
#print axioms Controls.scan_price_order
#print axioms Controls.site_charge_order

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.MeteredGuards
