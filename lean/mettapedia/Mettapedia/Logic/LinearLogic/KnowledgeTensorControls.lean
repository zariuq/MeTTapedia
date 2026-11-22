import Mathlib.Data.Set.Basic
import Mettapedia.Logic.LinearLogic.KnowledgeTensorFrameGrades

/-!
# Controls for tensor proofs over a knowledge zone

Knowledge is a set of candidate solutions over two candidates, so one fact may be unknown, known
or refuted.

* **A guard asked before its tell.** `asker` asks a fact that only `teller` tells. The run
  `teller, asker` exists (`teller_then_asker_runs`); the order `asker, teller` is refused
  (`asker_first_is_refused`); yet at the final knowledge both leaves are admitted and a Horn
  derivation with the refused order of leaves exists
  (`refused_order_has_a_horn_proof_with_admitted_leaves`). Proofs in the fibre over the final
  knowledge are therefore not runs: knowledge has to be a zone of the sequent. A conclusion may
  forget knowledge (`knowledge_may_be_forgotten`) and may not invent it
  (`knowledge_is_not_invented`).
* **Reads.** One occurrence serves two successive reads and survives both
  (`one_occurrence_serves_two_reads`); it is not duplicated (`a_read_is_not_duplicated`), and a
  leftover is not discarded (`a_leftover_is_not_discarded`).
* **Absence.** The firing guarded by the absence of `c` fires alone (`absence_fires_alone`), is
  refused beside `c` (`absence_refuses_the_frame`), so it has no additive tensor reading
  (`absence_has_no_additive_tensor_reading`). Its proof carries the grade `c ∉ frame`
  (`absence_proof_is_graded`) and no proof admits every frame
  (`absence_has_no_proof_for_all_frames`). It admits every frame outside its region
  (`absence_admits_frames_outside_its_region`).
* **Counting.** The firing guarded by exactly one `c` in the frame is refused with none and with
  two (`counting_refuses_less`, `counting_refuses_more`): it is neither stable under growth nor
  under shrinking of the frame, and it has no additive tensor reading
  (`counting_has_no_additive_tensor_reading`).
* **Not knowing.** The test that a fact is not yet known is not stable under refinement
  (`not_knowing_is_not_a_guard`), so it is not a guard.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.LinearLogic.KnowledgeTensorControls

open KnowledgeTensor

inductive Item where
  | a | b | c | d | e
  deriving DecidableEq

inductive Decl where
  | asker | teller
  deriving DecidableEq

open Item Decl

abbrev Knowledge := Set Bool

def countOf (item : Item) : Multiset Item →+ Nat where
  toFun bag := bag.count item
  map_zero' := rfl
  map_add' _ _ := Multiset.count_add _ _ _

/-! ## A guard asked before its tell -/

def askTell : System Knowledge Item Decl where
  take := fun
    | asker => {a}
    | teller => {d}
  read := fun _ => 0
  make := fun
    | asker => {c}
    | teller => {e}
  tell := fun
    | asker => Set.univ
    | teller => {true}
  guard := fun
    | asker => fun known => known ≤ {true}
    | teller => fun _ => True
  guard_mono := by
    intro declaration stronger weaker refines holds
    cases declaration with
    | asker =>
        have held : weaker ≤ ({true} : Set Bool) := holds
        exact le_trans refines held
    | teller => exact True.intro

def start : Multiset Item := askTell.premises asker + askTell.premises teller

def finish : Multiset Item := askTell.conclusions asker + askTell.conclusions teller

theorem teller_then_asker_runs :
    askTell.Run Set.univ start [teller, asker]
      (Set.univ ⊓ askTell.tell teller ⊓ askTell.tell asker) finish := by
  have first : askTell.Fires teller Set.univ start (Set.univ ⊓ askTell.tell teller)
      (askTell.conclusions teller + askTell.premises asker) :=
    ⟨askTell.premises asker, add_comm _ _, True.intro, rfl, rfl⟩
  have second : askTell.Fires asker (Set.univ ⊓ askTell.tell teller)
      (askTell.conclusions teller + askTell.premises asker)
      (Set.univ ⊓ askTell.tell teller ⊓ askTell.tell asker) finish :=
    ⟨askTell.conclusions teller, add_comm _ _, fun _ member => member.1.2, rfl, rfl⟩
  exact System.Run.fire first (System.Run.fire second (System.Run.done _ _))

theorem asker_first_is_refused :
    ¬ ∃ (known : Knowledge) (after : Multiset Item), askTell.Run Set.univ start [asker, teller] known after := by
  rintro ⟨known, after, run⟩
  cases run with
  | fire fires later =>
      obtain ⟨_, _, asked, _, _⟩ := fires
      have held : (Set.univ ⊓ Set.univ : Set Bool) ≤ {true} := asked
      have impossible : false = true :=
        held (show false ∈ (Set.univ ⊓ Set.univ : Set Bool) from ⟨True.intro, True.intro⟩)
      exact absurd impossible (by decide)

theorem refused_order_has_a_horn_proof_with_admitted_leaves :
    (∀ declaration ∈ [asker, teller],
      askTell.AdmittedAt (Set.univ ⊓ askTell.tell teller ⊓ askTell.tell asker) declaration) ∧
      ∃ diagram : LinearHorn.Derivation askTell.premises askTell.conclusions start finish,
        diagram.uses = [asker, teller] := by
  have admitted := System.Derives.admitted (System.Run.derives teller_then_asker_runs)
  constructor
  · intro declaration _
    cases declaration with
    | asker => exact admitted asker (by decide)
    | teller => exact admitted teller (by decide)
  · exact ⟨.tensor (.rule asker) (.rule teller), rfl⟩

theorem knowledge_may_be_forgotten :
    askTell.DerivesUpTo Set.univ start [teller, asker] Set.univ finish :=
  ⟨_, fun _ _ => True.intro, System.Run.derives teller_then_asker_runs⟩

theorem knowledge_is_not_invented :
    ¬ askTell.DerivesUpTo Set.univ start [] {true} start := by
  rintro ⟨known, below, proof⟩
  have run := System.Derives.run proof
  cases run
  have impossible : false = true := below (show false ∈ (Set.univ : Set Bool) from True.intro)
  exact absurd impossible (by decide)

/-! ## Reads -/

def lookup : System Knowledge Item Unit where
  take := fun _ => 0
  read := fun _ => {a}
  make := fun _ => {b}
  tell := fun _ => Set.univ
  guard := fun _ _ => True
  guard_mono := fun _ _ _ _ _ => True.intro

theorem one_occurrence_serves_two_reads :
    lookup.Run Set.univ {a} [(), ()] (Set.univ ⊓ Set.univ ⊓ Set.univ) (lookup.conclusions () + {b}) := by
  have firstSource : ({a} : Multiset Item) = lookup.premises () + 0 := by
    show ({a} : Multiset Item) = (0 + {a}) + 0
    rw [add_zero, zero_add]
  have secondSource : lookup.conclusions () + 0 = lookup.premises () + {b} := by
    show (({a} : Multiset Item) + {b}) + 0 = (0 + {a}) + {b}
    rw [add_zero, zero_add]
  have first : lookup.Fires () Set.univ {a} (Set.univ ⊓ Set.univ) (lookup.conclusions () + 0) :=
    ⟨0, firstSource, True.intro, rfl, rfl⟩
  have second : lookup.Fires () (Set.univ ⊓ Set.univ) (lookup.conclusions () + 0)
      (Set.univ ⊓ Set.univ ⊓ Set.univ) (lookup.conclusions () + {b}) :=
    ⟨{b}, secondSource, True.intro, rfl, rfl⟩
  exact System.Run.fire first (System.Run.fire second (System.Run.done _ _))

theorem a_read_is_not_duplicated {known known' : Knowledge} {after : Multiset Item} {uses : List Unit}
    (proof : lookup.Derives known {a} uses known' after) : after.count a = 1 := by
  have balanced : ∀ declaration : Unit,
      (countOf a) (lookup.premises declaration) = (countOf a) (lookup.conclusions declaration) := by
    intro declaration
    cases declaration
    decide
  have same := System.Derives.preserves_valuation (countOf a) balanced proof
  have one : (countOf a) ({a} : Multiset Item) = 1 := by decide
  exact same.symm.trans one

theorem a_leftover_is_not_discarded {known known' : Knowledge} {after : Multiset Item} {uses : List Unit}
    (proof : lookup.Derives known ({a} + {c}) uses known' after) : after.count c = 1 := by
  have balanced : ∀ declaration : Unit,
      (countOf c) (lookup.premises declaration) = (countOf c) (lookup.conclusions declaration) := by
    intro declaration
    cases declaration
    decide
  have same := System.Derives.preserves_valuation (countOf c) balanced proof
  have one : (countOf c) (({a} : Multiset Item) + {c}) = 1 := by decide
  exact same.symm.trans one

/-! ## Absence -/

def absence : CheckedSystem Knowledge Item Unit where
  take := fun _ => {a}
  read := fun _ => 0
  make := fun _ => {b}
  tell := fun _ => Set.univ
  check := fun _ _ frame => c ∉ frame
  check_mono := fun _ _ _ _ _ holds => holds

theorem absence_fires_alone :
    absence.Run Set.univ (absence.premises ()) [()] (Set.univ ⊓ Set.univ) (absence.conclusions ()) := by
  have fires : absence.Fires () Set.univ (absence.premises ()) (Set.univ ⊓ Set.univ)
      (absence.conclusions ()) :=
    ⟨0, (add_zero _).symm, Multiset.notMem_zero c, rfl, (add_zero _).symm⟩
  exact CheckedSystem.Run.fire fires (CheckedSystem.Run.done _ _)

theorem absence_refuses_the_frame {known : Knowledge} {after : Multiset Item} :
    ¬ absence.Fires () Set.univ (absence.premises () + {c}) known after := by
  rintro ⟨frame, source, checked, _, _⟩
  have same : ({c} : Multiset Item) = frame := add_left_cancel source
  rw [← same] at checked
  exact checked (Multiset.mem_singleton_self c)

theorem absence_blocked {known' : Knowledge} {before after : Multiset Item} {uses : List Unit}
    (run : absence.Run Set.univ before uses known' after)
    (atStart : before = absence.premises () + {c}) (atFinish : after = absence.conclusions () + {c}) :
    False := by
  cases run with
  | done =>
      have equal : absence.premises () = absence.conclusions () :=
        add_right_cancel (atStart.symm.trans atFinish)
      have counts := congrArg (Multiset.count a) equal
      exact absurd counts (by decide)
  | fire fires later =>
      subst atStart
      exact absence_refuses_the_frame fires

/-- **Absence has no additive tensor reading**, over any knowledge and any atoms. -/
theorem absence_has_no_additive_tensor_reading {K' : Type*} {Atom' : Type*} {Rule' : Type*}
    [SemilatticeInf K'] (logic : System K' Atom' Rule') (reading : HomomorphicReading absence logic) :
    False :=
  reading.false_of_frame_failure ⟨[()], absence_fires_alone⟩ (extra := {c})
    (fun ⟨_, run⟩ => absence_blocked run rfl rfl)

theorem absence_proof_is_graded :
    absence.Proves Set.univ (absence.premises ()) (fun frame => c ∉ frame) [()]
      (Set.univ ⊓ Set.univ) (absence.conclusions ()) :=
  CheckedSystem.Proves.rule () Set.univ

theorem absence_has_no_proof_for_all_frames :
    ¬ absence.Proves Set.univ (absence.premises ()) (fun _ => True) [()]
      (Set.univ ⊓ Set.univ) (absence.conclusions ()) := by
  intro proof
  exact absence_blocked (CheckedSystem.Proves.run proof {c} True.intro) rfl rfl

theorem absence_reads_only_its_region : absence.ReadsOnly (fun item => item = c) := by
  intro _ _ frame
  exact ⟨fun clear member => clear (Multiset.mem_filter.mp member).1,
    fun clear member => clear (Multiset.mem_filter.mpr ⟨member, rfl⟩)⟩

theorem absence_admits_frames_outside_its_region :
    absence.Run Set.univ (absence.premises () + {d}) [()] (Set.univ ⊓ Set.univ)
      (absence.conclusions () + {d}) :=
  CheckedSystem.Run.frame_outside (fun item => item = c) absence_reads_only_its_region
    (by
      intro item member
      rw [Multiset.mem_singleton] at member
      rw [member]
      exact (by decide : (d : Item) ≠ c))
    absence_fires_alone

/-! ## Counting -/

def exactlyOne : CheckedSystem Knowledge Item Unit where
  take := fun _ => {a}
  read := fun _ => 0
  make := fun _ => {b}
  tell := fun _ => Set.univ
  check := fun _ _ frame => frame.count c = 1
  check_mono := fun _ _ _ _ _ holds => holds

theorem counting_fires :
    exactlyOne.Run Set.univ (exactlyOne.premises () + {c}) [()] (Set.univ ⊓ Set.univ)
      (exactlyOne.conclusions () + {c}) := by
  have fires : exactlyOne.Fires () Set.univ (exactlyOne.premises () + {c}) (Set.univ ⊓ Set.univ)
      (exactlyOne.conclusions () + {c}) :=
    ⟨{c}, rfl, Multiset.count_singleton_self c, rfl, rfl⟩
  exact CheckedSystem.Run.fire fires (CheckedSystem.Run.done _ _)

theorem counting_refuses_more {known : Knowledge} {after : Multiset Item} :
    ¬ exactlyOne.Fires () Set.univ (exactlyOne.premises () + {c} + {c}) known after := by
  rintro ⟨frame, source, checked, _, _⟩
  have same : ({c} : Multiset Item) + {c} = frame := add_left_cancel ((add_assoc _ _ _).symm.trans source)
  rw [← same] at checked
  have counted : Multiset.count c (({c} : Multiset Item) + {c}) = 1 := checked
  exact absurd counted (by decide)

theorem counting_refuses_less {known : Knowledge} {after : Multiset Item} :
    ¬ exactlyOne.Fires () Set.univ (exactlyOne.premises () + 0) known after := by
  rintro ⟨frame, source, checked, _, _⟩
  have same : (0 : Multiset Item) = frame := add_left_cancel source
  rw [← same] at checked
  have counted : Multiset.count c (0 : Multiset Item) = 1 := checked
  exact absurd counted (by decide)

theorem counting_blocked {known' : Knowledge} {before after : Multiset Item} {uses : List Unit}
    (run : exactlyOne.Run Set.univ before uses known' after)
    (atStart : before = exactlyOne.premises () + {c} + {c})
    (atFinish : after = exactlyOne.conclusions () + {c} + {c}) : False := by
  cases run with
  | done =>
      have equal := atStart.symm.trans atFinish
      have counts := congrArg (Multiset.count a) equal
      exact absurd counts (by decide)
  | fire fires later =>
      subst atStart
      exact counting_refuses_more fires

/-- **Counting has no additive tensor reading**, over any knowledge and any atoms. -/
theorem counting_has_no_additive_tensor_reading {K' : Type*} {Atom' : Type*} {Rule' : Type*}
    [SemilatticeInf K'] (logic : System K' Atom' Rule') (reading : HomomorphicReading exactlyOne logic) :
    False :=
  reading.false_of_frame_failure ⟨[()], counting_fires⟩ (extra := {c})
    (fun ⟨_, run⟩ => counting_blocked run rfl rfl)

/-! ## Not knowing -/

theorem not_knowing_is_not_a_guard :
    ¬ ∀ {stronger weaker : Knowledge}, stronger ≤ weaker → ¬ weaker ≤ {true} → ¬ stronger ≤ {true} := by
  intro stable
  refine stable (stronger := {true}) (weaker := Set.univ) (fun _ _ => True.intro) ?_ le_rfl
  intro known
  have impossible : false = true := known (show false ∈ (Set.univ : Set Bool) from True.intro)
  exact absurd impossible (by decide)

end Mettapedia.Logic.LinearLogic.KnowledgeTensorControls
