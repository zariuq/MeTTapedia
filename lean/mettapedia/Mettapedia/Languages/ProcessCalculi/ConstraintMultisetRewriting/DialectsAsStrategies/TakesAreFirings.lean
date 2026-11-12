import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.ConcurrencySeparation

/-!
# A take on a bag of atoms is a firing of the step, read through labels

The concurrency separation works on bags of atoms, because PeTTa and HE remove atoms by value, not
by occurrence. This module ties that model to the step: on the first-order step over ground terms
(`IssuingControls.base`), the bag a configuration holds is the bag of its occurrences' labels
(`readout`).

* `firing_is_take`: a valid ground firing that reads distinct occurrences is, read through labels,
  an admitted take of its rule (`Take.ofRule`), and the labels of its result are the take fired on
  the labels of its start.
* `admitted_is_take`: the same for every firing the step admits without predicate queries.

So the atomic semantics of the separation is the step seen through its labels: every atomic take
used there is the readout of a firing, and every firing of the step that reads distinct
occurrences is such a take.

## Controls

* `Controls.taker_is_take`: the taker of `A` from `LinearTake` is the take of `A` on the labels.
* `Controls.repeated_read_admitted`: the step admits a firing that reads one occurrence twice; read
  through labels it is not an admitted take, so the hypothesis that reads are distinct is needed.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies

namespace Concurrency

open NamesOnTheStep NamesOnTheStep.IssuingControls FragmentsOfTheStep.GroundFirings
open MeTTaCalculus.OccurrenceCommits (fire mem_fire)

/-- The bag of labels a configuration holds. -/
def readout (C : Conf) : Multiset Expr := C.present.val.map Prod.fst

/-- A rule instance read as a take. -/
def Take.ofRule (r : RuleInstance Expr) : Take Expr := ⟨r.take, r.read, r.produce⟩

theorem map_sub_of_le {γ δ : Type*} [DecidableEq γ] [DecidableEq δ] (f : γ → δ) {s t : Multiset γ}
    (le : t ≤ s) : (s - t).map f = s.map f - t.map f := by
  have whole : (s - t).map f + t.map f = s.map f := by
    rw [← Multiset.map_add, tsub_add_cancel_of_le le]
  rw [← whole, add_tsub_cancel_right]

theorem labels_of_forall₂ : ∀ {ps : List Expr} {os : List Occ},
    List.Forall₂ (fun p (o : Occ) => p = o.1) ps os → ps = os.map Prod.fst
  | [], [], .nil => rfl
  | _ :: _, _ :: _, .cons head tail => by
      rw [List.map_cons, head, labels_of_forall₂ tail]

theorem toFinset_val_of_nodup {l : List Occ} (distinct : l.Nodup) : l.toFinset.val = (l : Multiset Occ) := by
  rw [List.toFinset_val, distinct.dedup]

/-- **A ground firing, read through labels, is a take.** -/
theorem firing_is_take {C : Conf} {r : RuleInstance Expr} {sel : Selection Occ}
    (valid : sel.Valid ground Prod.fst r C) (readsDistinct : sel.read.Nodup) :
    (Take.ofRule r).Admits (readout C) ∧
      readout (sel.result Prod.fst r C) = (Take.ofRule r).fire (readout C) := by
  have takes : r.take = sel.taken.map Prod.fst := labels_of_forall₂ (takes_match valid)
  have reads : r.read = sel.read.map Prod.fst := labels_of_forall₂ (reads_match valid)
  have outputs : sel.made.map Prod.fst = r.produce := valid.outputs
  have takenVal := toFinset_val_of_nodup valid.take_distinct
  have readVal := toFinset_val_of_nodup readsDistinct
  have madeVal := toFinset_val_of_nodup valid.output_distinct
  have takenSub : sel.taken.toFinset ⊆ C.present := valid.occurrences.taken_subset
  have readSub : sel.read.toFinset ⊆ C.present := valid.occurrences.kept_subset
  have apart : Disjoint sel.taken.toFinset sel.read.toFinset := valid.occurrences.apart
  have fresh : Disjoint sel.made.toFinset C.present := valid.occurrences.fresh
  constructor
  · show (((r.take ++ r.read : List Expr)) : Multiset Expr) ≤ C.present.val.map Prod.fst
    have union : (sel.taken.toFinset ∪ sel.read.toFinset).val =
        ((sel.taken ++ sel.read : List Occ) : Multiset Occ) := by
      rw [← Finset.disjUnion_eq_union _ _ apart]
      show sel.taken.toFinset.val + sel.read.toFinset.val = _
      rw [takenVal, readVal, Multiset.coe_add]
    have le : ((sel.taken ++ sel.read : List Occ) : Multiset Occ) ≤ C.present.val := by
      rw [← union]
      exact Finset.val_le_iff.mpr (Finset.union_subset takenSub readSub)
    rw [takes, reads, ← List.map_append, ← Multiset.map_coe]
    exact Multiset.map_le_map le
  · have takenLe : (sel.taken : Multiset Occ) ≤ C.present.val := by
      rw [← takenVal]
      exact Finset.val_le_iff.mpr takenSub
    have away : Disjoint (C.present \ sel.taken.toFinset) sel.made.toFinset :=
      Finset.disjoint_of_subset_left Finset.sdiff_subset fresh.symm
    show (fire C.present (sel.commit (T := Expr))).val.map Prod.fst =
      C.present.val.map Prod.fst - ((r.take : List Expr) : Multiset Expr) + (r.produce : Multiset Expr)
    change ((C.present \ sel.taken.toFinset) ∪ sel.made.toFinset).val.map Prod.fst = _
    rw [← Finset.disjUnion_eq_union _ _ away]
    show ((C.present \ sel.taken.toFinset).val + sel.made.toFinset.val).map Prod.fst = _
    rw [Finset.sdiff_val, takenVal, madeVal, Multiset.map_add, map_sub_of_le _ takenLe, takes,
      ← outputs, Multiset.map_coe, Multiset.map_coe]

/-- **Every firing the step admits without queries, and reading distinct occurrences, is a take on
labels**: admitted, and with the take's result. -/
theorem admitted_is_take {C : Conf} {f : Fir} (noQueries : f.queries = [])
    (admitted : base.Admits (s := C) f) (readsDistinct : f.selection.read.Nodup) :
    (Take.ofRule f.rule).block (readout C) = (readout (base.result (s := C) f admitted), true) := by
  have valid := FragmentsOfTheStep.RefinedScheduler.valid_of_admits noQueries admitted
  obtain ⟨takeAdmitted, result⟩ := firing_is_take valid readsDistinct
  rw [Take.block, if_pos takeAdmitted]
  exact congrArg (·, true) result.symm

namespace Controls

open FragmentsOfTheStep.LinearTake.Controls in
/-- **Positive control.** The taker of `A` from `LinearTake`, at the store holding `A` and `B`, is the
take of `A` making `W` on the bag of labels. -/
theorem taker_is_take :
    (Take.ofRule takeA.1).Admits (readout FragmentsOfTheStep.LinearTake.Controls.both) ∧
      readout (takeA.2.result Prod.fst takeA.1 FragmentsOfTheStep.LinearTake.Controls.both) =
        (Take.ofRule takeA.1).fire (readout FragmentsOfTheStep.LinearTake.Controls.both) :=
  firing_is_take takeA_valid List.nodup_nil

/-- Reads `T` twice, makes `U`. -/
def readTwice : RuleInstance Expr := rule [] [factT, factT] [factU]

/-- **Negative control: a repeated read.** The step admits a firing reading the one occurrence of
`T` twice; read through labels it would need two copies, so it is not an admitted take. -/
theorem repeated_read_admitted :
    (⟨[], [(factT, 0), (factT, 0)], [(factU, 0)]⟩ : Selection Occ).Valid ground Prod.fst readTwice
        ⟨[], {(factT, 0)}⟩ ∧
      ¬ (Take.ofRule readTwice).Admits (readout ⟨[], {(factT, 0)}⟩) := by
  constructor
  · exact ground_valid (by decide) (by decide) rfl rfl rfl (by decide) (by decide) rfl (no_checks rfl)
  · decide

end Controls

#print axioms firing_is_take
#print axioms admitted_is_take
#print axioms Controls.taker_is_take
#print axioms Controls.repeated_read_admitted

end Concurrency

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies
