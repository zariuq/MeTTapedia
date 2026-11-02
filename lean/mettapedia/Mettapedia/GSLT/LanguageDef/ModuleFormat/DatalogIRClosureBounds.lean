import Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIRClosureNoFault
import Mettapedia.Languages.Datalog.ClosureFinite

/-! Actual closure runs append new facts without duplicates. Their physical
facts lie in the image of the source program's finite fact universe. These
are proof bounds; the runtime does not enumerate that universe. -/

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIR.ClosureMachine

open Mettapedia.Languages.Datalog
open Mettapedia.OSLF.MeTTaIL Syntax

private instance : LawfulBEq Pattern where
  rfl := by intro value; change decide (value = value) = true; simp
  eq_of_beq := by intro first second same; change decide (first = second) = true at same; exact of_decide_eq_true same

private theorem insert_prefix {α : Type} [BEq α] (items : List α) (item : α) : items <+: insert items item := by
  unfold insert
  split
  · exact List.prefix_refl _
  · exact List.prefix_append _ _

private theorem insert_nodup {α : Type} [BEq α] [LawfulBEq α] (items : List α) (item : α) (distinct : items.Nodup) :
    (insert items item).Nodup := by
  by_cases present : item ∈ items
  · simp only [insert,show items.contains item = true from by simpa using present,if_true]
    exact distinct
  · have separate : ∀ value ∈ items, ¬ value = item := by
      intro value member same
      exact present (same ▸ member)
    simpa [insert,present,List.nodup_append] using And.intro distinct separate

private theorem eraseDups_distinct {α : Type} [BEq α] [LawfulBEq α] (items : List α) : items.eraseDups.Nodup := by
  cases items with
  | nil => simp
  | cons head tail =>
    rw [List.eraseDups_cons]
    apply List.nodup_cons.mpr
    constructor
    · intro member
      have selected := (List.mem_filter.mp (List.mem_eraseDups.mp member)).2
      simp at selected
    · exact eraseDups_distinct _
termination_by items.length
decreasing_by exact Nat.lt_succ_of_le (List.length_filter_le _ _)

theorem commit_fact_order (prepared : Executable.Prepared) (snapshot : List Pattern)
    (batch : List GeneralOccurrenceSemantics.Receipt) (facts : List Pattern) (before : List Key)
    (outputs : List Pattern) (after : List Key) (distinct : facts.Nodup)
    (committed : commit? prepared snapshot batch facts before = some (outputs,after)) : facts <+: outputs ∧ outputs.Nodup := by
  induction batch generalizing facts before with
  | nil =>
    have same : (facts,before) = (outputs,after) := Option.some.inj committed
    cases same
    exact ⟨List.prefix_refl _,distinct⟩
  | cons receipt batch ih =>
    cases read : key? prepared snapshot receipt with
    | none => simp [commit?,read] at committed
    | some key =>
      have tail : commit? prepared snapshot batch (insert facts receipt.target) (insert before key) = some (outputs,after) := by
        simpa only [commit?,read,Option.bind_eq_bind,Option.bind_some] using committed
      obtain ⟨front,outputDistinct⟩ := ih _ _ (insert_nodup facts receipt.target distinct) tail
      exact ⟨(insert_prefix facts receipt.target).trans front,outputDistinct⟩

theorem tick_fact_order (prepared : Executable.Prepared) (machine : Machine prepared) (distinct : machine.facts.Nodup) (quantum : Nat) :
    machine.facts <+: (tick prepared machine quantum).facts ∧ (tick prepared machine quantum).facts.Nodup := by
  unfold tick
  split
  · exact ⟨List.prefix_refl _,distinct⟩
  · dsimp only
    split
    · exact ⟨List.prefix_refl _,distinct⟩
    · try dsimp only
      split
      · exact ⟨List.prefix_refl _,distinct⟩
      · rename_i facts keys committed
        have ordered := commit_fact_order prepared machine.facts _ machine.facts machine.keys facts keys distinct committed
        try dsimp only
        split
        · exact ⟨List.prefix_refl _,distinct⟩
        · split
          · exact ordered
          · exact ⟨List.prefix_refl _,distinct⟩

theorem advance_fact_order (prepared : Executable.Prepared) (machine : Machine prepared) (distinct : machine.facts.Nodup)
    (ticks quantum : Nat) : machine.facts <+: (advance prepared ticks quantum machine).facts ∧
      (advance prepared ticks quantum machine).facts.Nodup := by
  induction ticks generalizing machine with
  | zero => exact ⟨List.prefix_refl _,distinct⟩
  | succ ticks ih =>
    have first := tick_fact_order prepared machine distinct quantum
    have rest := ih _ first.2
    exact ⟨first.1.trans rest.1,rest.2⟩

theorem run_fact_order (prepared : Executable.Prepared) (ticks quantum : Nat) :
    (begin prepared).facts <+: (advance prepared ticks quantum (begin prepared)).facts ∧
      (advance prepared ticks quantum (begin prepared)).facts.Nodup :=
  advance_fact_order prepared (begin prepared) (eraseDups_distinct _) ticks quantum

noncomputable def physicalFactUniverse (program : Program) (seeds : List GroundFact) (prepared : Executable.Prepared) : Finset Pattern :=
  ((Closure.factUniverse program seeds).toList.filterMap (Executable.fact? prepared.vocabulary)).toFinset

theorem run_facts_bounded (program : Program) (seeds : List GroundFact) (prepared : Executable.Prepared)
    (accepted : Executable.prepare program seeds = .ok prepared)
    (scope : GeneralPremise.Static.checkLanguage (GeneralPlanEnvironment.environment (Executable.plan prepared prepared.seedFacts)) = true)
    (ticks quantum : Nat) :
    (advance prepared ticks quantum (begin prepared)).facts.toFinset ⊆ physicalFactUniverse program seeds prepared := by
  intro code member
  have present := List.mem_toFinset.mp member
  obtain ⟨fact,formed⟩ := run_canonical program seeds prepared accepted scope ticks quantum code present
  obtain ⟨actual,decoded,derived⟩ := run_factsSound program seeds prepared accepted scope ticks quantum code present
  have read := Executable.decodeFact?_roundtrip prepared fact code formed
  have same : actual = fact := Option.some.inj (decoded.symm.trans read)
  have inUniverse := Closure.derives_in_universe Executable.policy program seeds (same ▸ derived)
  exact List.mem_toFinset.mpr (List.mem_filterMap.mpr ⟨fact,Finset.mem_toList.mpr inUniverse,formed⟩)

theorem run_fact_length_bound (program : Program) (seeds : List GroundFact) (prepared : Executable.Prepared)
    (accepted : Executable.prepare program seeds = .ok prepared)
    (scope : GeneralPremise.Static.checkLanguage (GeneralPlanEnvironment.environment (Executable.plan prepared prepared.seedFacts)) = true)
    (ticks quantum : Nat) :
    (advance prepared ticks quantum (begin prepared)).facts.length ≤ (physicalFactUniverse program seeds prepared).card := by
  have bounded := Finset.card_le_card (run_facts_bounded program seeds prepared accepted scope ticks quantum)
  simpa only [List.toFinset_card_of_nodup (run_fact_order prepared ticks quantum).2] using bounded

#print axioms run_fact_order
#print axioms run_facts_bounded
#print axioms run_fact_length_bound

end Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIR.ClosureMachine
