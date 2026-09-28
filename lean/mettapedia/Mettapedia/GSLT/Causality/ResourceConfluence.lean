import Mettapedia.GSLT.Causality.ResourceReads
import Mathlib.Logic.Relation

/-!
# Without conflicts, one run decides the outcome

A catalogue of instances is free of conflicts when any two different instances
enabled at one bag are concurrent there. Every run then ends in the same bag:
a committed run and an exhaustive search agree, and backtracking gains nothing.

Inference that reads its premises, and fires each rule instance once, is free
of conflicts. Saturation may therefore take its work in any order.

Where two firings conflict, runs part. A rho input with two messages takes
either; the two runs end in different bags. A committed run reaches one of
them, and an exhaustive search collects both.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Causality.ResourceInteraction

open Mettapedia.GSLT

universe uRes uRule

namespace System

variable {R : Type uRes} [DecidableEq R] (S : System.{uRes, uRule} R) (catalogue : List S.Entry)

/-- One firing of a catalogued instance. -/
def CatalogueStep (M N : Multiset R) : Prop :=
  ∃ entry ∈ catalogue, S.Enables M entry.2 ∧ N = S.fire M entry.2

/-- Different catalogued instances enabled at one bag are concurrent there. -/
def ConflictFree : Prop :=
  ∀ (M : Multiset R) (first second : S.Entry), first ∈ catalogue → second ∈ catalogue →
    first ≠ second → S.Enables M first.2 → S.Enables M second.2 →
      S.Concurrent M first.2 second.2

/-- **Without conflicts, catalogued firing is confluent.** -/
theorem confluent_of_conflictFree (free : S.ConflictFree catalogue) {M N₁ N₂ : Multiset R}
    (reach₁ : Relation.ReflTransGen (S.CatalogueStep catalogue) M N₁)
    (reach₂ : Relation.ReflTransGen (S.CatalogueStep catalogue) M N₂) :
    Relation.Join (Relation.ReflTransGen (S.CatalogueStep catalogue)) N₁ N₂ := by
  refine Relation.church_rosser ?_ reach₁ reach₂
  rintro source _ _ ⟨first, firstIn, firstEnabled, rfl⟩ ⟨second, secondIn, secondEnabled, rfl⟩
  by_cases same : first = second
  · subst same
    exact ⟨_, Relation.ReflGen.refl, Relation.ReflTransGen.refl⟩
  · have concurrent := free source first second firstIn secondIn same firstEnabled secondEnabled
    exact ⟨S.fire (S.fire source first.2) second.2,
      Relation.ReflGen.single ⟨second, secondIn, S.enables_fire concurrent, rfl⟩,
      Relation.ReflTransGen.single ⟨first, firstIn,
        S.enables_fire (S.concurrent_symm concurrent), S.fire_comm concurrent⟩⟩

/-- A run of catalogued instances is a sequence of catalogued firings. -/
theorem reflTransGen_of_fires : ∀ (path : List S.Entry) (M N : Multiset R),
    (∀ entry ∈ path, entry ∈ catalogue) → S.Fires path M N →
      Relation.ReflTransGen (S.CatalogueStep catalogue) M N
  | [], M, N, _, fires => by
      change N = M at fires
      subst fires
      exact .refl
  | entry :: rest, M, N, catalogued, fires =>
      Relation.ReflTransGen.head
        ⟨entry, catalogued entry List.mem_cons_self, fires.1, rfl⟩
        (reflTransGen_of_fires rest _ N
          (fun other member => catalogued other (List.mem_cons_of_mem entry member)) fires.2)

/-- Nothing fires from a bag where no catalogued instance is enabled. -/
theorem eq_of_terminal {N X : Multiset R} (terminal : S.enabledAt catalogue N = [])
    (reach : Relation.ReflTransGen (S.CatalogueStep catalogue) N X) : X = N := by
  induction reach with
  | refl => rfl
  | tail _ step ih =>
      obtain ⟨entry, member, enabled, _⟩ := step
      rw [ih] at enabled
      have enabledHere : entry ∈ S.enabledAt catalogue N :=
        List.mem_filter.mpr ⟨member, (S.enabledB_iff N entry).mpr enabled⟩
      rw [terminal] at enabledHere
      cases enabledHere

/-- Every firing of a returned run is catalogued. -/
theorem runs_catalogued : ∀ (fuel : ℕ) (M : Multiset R) (run : List S.Entry × Multiset R),
    run ∈ S.runs catalogue fuel M → ∀ entry ∈ run.1, entry ∈ catalogue
  | 0, M, run, member => by
      unfold runs at member
      split at member
      · simp only [List.mem_singleton] at member
        subst member
        simp
      · simp at member
  | fuel + 1, M, run, member => by
      unfold runs at member
      split at member
      · simp only [List.mem_singleton] at member
        subst member
        simp
      · obtain ⟨entry, enabledMember, member⟩ := List.mem_flatMap.mp member
        obtain ⟨tail, tailMember, rfl⟩ := List.mem_map.mp member
        intro other otherMember
        rcases List.mem_cons.mp otherMember with rfl | later
        · exact (List.mem_filter.mp enabledMember).1
        · exact runs_catalogued fuel _ tail tailMember other later

/-- **A committed run decides the outcome.** Without conflicts, every outcome
of an exhaustive search is the bag that any one maximal run reaches. -/
theorem committed_run_decides (free : S.ConflictFree catalogue) {path : List S.Entry}
    {M N : Multiset R} (catalogued : ∀ entry ∈ path, entry ∈ catalogue)
    (fires : S.Fires path M N) (terminal : S.enabledAt catalogue N = []) (fuel : ℕ) :
    ∀ outcome ∈ S.outcomes catalogue fuel M, outcome = N := by
  intro outcome member
  obtain ⟨run, runMember, rfl⟩ := List.mem_map.mp member
  obtain ⟨runFires, runTerminal⟩ := S.runs_sound catalogue fuel M run runMember
  obtain ⟨meet, fromRun, fromPath⟩ := S.confluent_of_conflictFree catalogue free
    (S.reflTransGen_of_fires catalogue run.1 M run.2
      (S.runs_catalogued catalogue fuel M run runMember) runFires)
    (S.reflTransGen_of_fires catalogue path M N catalogued fires)
  rw [← S.eq_of_terminal catalogue runTerminal fromRun, S.eq_of_terminal catalogue terminal fromPath]

/-- **Without conflicts, every run of a search ends in one bag.** -/
theorem outcomes_agree (free : S.ConflictFree catalogue) (fuel : ℕ) (M : Multiset R)
    {first second : Multiset R} (firstMember : first ∈ S.outcomes catalogue fuel M)
    (secondMember : second ∈ S.outcomes catalogue fuel M) : first = second := by
  obtain ⟨run, runMember, rfl⟩ := List.mem_map.mp secondMember
  obtain ⟨runFires, runTerminal⟩ := S.runs_sound catalogue fuel M run runMember
  exact S.committed_run_decides catalogue free (S.runs_catalogued catalogue fuel M run runMember)
    runFires runTerminal fuel first firstMember

end System

/-! ## Inference that reads its premises -/

/-- Facts, and one ticket for each rule instance. -/
inductive InferRes (Fact : Type) where
  | fact (value : Fact)
  | ticket (index : ℕ)
  deriving DecidableEq

/-- Rule instance `index` reads its premises, produces its conclusions, and
spends its own ticket, so it fires once. -/
def inference {Fact : Type} (rules : ℕ → Multiset Fact × Multiset Fact) :
    System (InferRes Fact) where
  Site := Unit
  Instance := fun _ => ℕ
  consume := fun index => {InferRes.ticket index}
  read := fun index => (rules index).1.map InferRes.fact
  produce := fun index => (rules index).2.map InferRes.fact

/-- **Inference that reads its premises is free of conflicts.** -/
theorem inference_conflictFree {Fact : Type} [DecidableEq Fact]
    (rules : ℕ → Multiset Fact × Multiset Fact) (catalogue : List (inference rules).Entry) :
    (inference rules).ConflictFree catalogue := by
  intro M first second _ _ different firstEnabled secondEnabled
  obtain ⟨⟨⟩, i⟩ := first
  obtain ⟨⟨⟩, j⟩ := second
  have apart : i ≠ j := fun same => different (by rw [same])
  change {InferRes.ticket i} + (rules i).1.map InferRes.fact ≤ M at firstEnabled
  change {InferRes.ticket j} + (rules j).1.map InferRes.fact ≤ M at secondEnabled
  have fits : ∀ index, index = i ∨ index = j →
      {InferRes.ticket i} + {InferRes.ticket j} + (rules index).1.map InferRes.fact ≤ M := by
    intro index which
    rw [Multiset.le_iff_count]
    intro resource
    rw [Multiset.count_add, Multiset.count_add]
    cases resource with
    | ticket k =>
        have noTicket : ((rules index).1.map InferRes.fact).count (InferRes.ticket k) = 0 :=
          Multiset.count_eq_zero.mpr (by simp)
        rw [noTicket, add_zero]
        have atI := Multiset.count_le_of_le (InferRes.ticket k) firstEnabled
        have atJ := Multiset.count_le_of_le (InferRes.ticket k) secondEnabled
        rw [Multiset.count_add, Multiset.count_singleton] at atI atJ
        rw [Multiset.count_singleton, Multiset.count_singleton]
        by_cases isI : (InferRes.ticket k : InferRes Fact) = InferRes.ticket i
        · have notJ : (InferRes.ticket k : InferRes Fact) ≠ InferRes.ticket j := by
            rw [isI]
            intro same
            exact apart (InferRes.ticket.inj same)
          rw [if_pos isI, if_neg notJ]
          rw [if_pos isI] at atI
          omega
        · rw [if_neg isI]
          by_cases isJ : (InferRes.ticket k : InferRes Fact) = InferRes.ticket j
          · rw [if_pos isJ]
            rw [if_pos isJ] at atJ
            omega
          · rw [if_neg isJ]
            exact Nat.zero_le _
    | fact value =>
        rw [Multiset.count_singleton, Multiset.count_singleton, if_neg (by simp),
          if_neg (by simp), zero_add, zero_add]
        rcases which with rfl | rfl
        · have atI := Multiset.count_le_of_le (InferRes.fact value) firstEnabled
          rw [Multiset.count_add, Multiset.count_singleton, if_neg (by simp), zero_add] at atI
          exact atI
        · have atJ := Multiset.count_le_of_le (InferRes.fact value) secondEnabled
          rw [Multiset.count_add, Multiset.count_singleton, if_neg (by simp), zero_add] at atJ
          exact atJ
  exact ⟨fits i (Or.inl rfl), fits j (Or.inr rfl)⟩

/-! ## Controls -/

namespace Controls

/-- Facts `a`, `b`, `c`, `d`. -/
inductive Letter where
  | a
  | b
  | c
  | d
  deriving DecidableEq

/-- From `a` infer `b` and `c`; from `b` and `c` infer `d`. -/
def letterRules : ℕ → Multiset Letter × Multiset Letter
  | 0 => ({Letter.a}, {Letter.b})
  | 1 => ({Letter.a}, {Letter.c})
  | 2 => ({Letter.b, Letter.c}, {Letter.d})
  | _ => (0, 0)

def rule (index : ℕ) : (inference letterRules).Entry := ⟨(), index⟩

def letterCatalogue : List (inference letterRules).Entry := [rule 0, rule 1, rule 2]

/-- The fact `a` and the three tickets. -/
def letterStart : Multiset (InferRes Letter) :=
  {InferRes.fact .a, InferRes.ticket 0, InferRes.ticket 1, InferRes.ticket 2}

/-- The saturated bag. -/
def saturated : Multiset (InferRes Letter) :=
  {InferRes.fact .a, InferRes.fact .b, InferRes.fact .c, InferRes.fact .d}

/-- **Saturation in either order.** The first two inferences may fire in
either order, so a search finds two runs, and both end saturated. -/
theorem saturation_two_runs_one_outcome :
    (inference letterRules).outcomes letterCatalogue 3 letterStart = [saturated, saturated] := by
  decide

/-- Every run of the search ends saturated, by freedom from conflicts. -/
theorem saturation_outcome (outcome : Multiset (InferRes Letter))
    (member : outcome ∈ (inference letterRules).outcomes letterCatalogue 3 letterStart) :
    outcome = saturated := by
  have runs := saturation_two_runs_one_outcome
  exact (inference letterRules).outcomes_agree letterCatalogue
    (inference_conflictFree letterRules letterCatalogue) 3 letterStart member
    (by rw [runs]; exact List.mem_cons_self)

def takeEntry (value : ℕ) : linearReceiver.Entry := ⟨(), value⟩

/-- **A conflict parts the runs.** The linear input takes either message, and
the two runs end in different bags. -/
theorem receiver_runs_part :
    linearReceiver.outcomes [takeEntry 1, takeEntry 2] 2 twoMessages =
      [{Res.received 1, Res.message 2}, {Res.received 2, Res.message 1}] := by
  decide

end Controls

#print axioms System.confluent_of_conflictFree
#print axioms System.committed_run_decides
#print axioms System.outcomes_agree
#print axioms inference_conflictFree
#print axioms Controls.saturation_two_runs_one_outcome
#print axioms Controls.saturation_outcome
#print axioms Controls.receiver_runs_part

end Mettapedia.GSLT.Causality.ResourceInteraction
