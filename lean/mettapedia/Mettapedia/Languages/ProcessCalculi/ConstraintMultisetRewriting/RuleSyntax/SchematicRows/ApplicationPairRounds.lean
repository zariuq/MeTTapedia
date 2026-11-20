import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.ApplicationPairRuns

/-!
# A finite snapshot of occurrence pairs has one coherent actual execution

Each pair refers to the store at the beginning of the round. Earlier
applications retain those occurrences and their exact reading families.
Composing their actual protected runs therefore accumulates precisely the
union of the original pair families. Newly made rows are not used as premises
until a later round.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.ApplicationMachine

open Mettapedia.Logic.LP
open Presentation.Schematic (Tm rowSig)

universe uOcc
variable {judgmentTag arrowTag : Nat} {O : Type uOcc} [DecidableEq O] {s : Store O}

def pairFamilies (judgmentTag arrowTag : Nat) (s : Store O) (caller : Subst rowSig) :
    List (O × O) → Set Tm
  | [] => ∅
  | pair :: rest => pairFamily judgmentTag arrowTag s caller pair.1 pair.2 ∪
      pairFamilies judgmentTag arrowTag s caller rest

omit [DecidableEq O] in
theorem mem_pairFamilies (judgmentTag arrowTag : Nat) (s : Store O) (caller : Subst rowSig)
    (pairs : List (O × O)) (value : Tm) :
    value ∈ pairFamilies judgmentTag arrowTag s caller pairs ↔
      ∃ pair ∈ pairs, value ∈ pairFamily judgmentTag arrowTag s caller pair.1 pair.2 := by
  induction pairs with
  | nil => simp [pairFamilies]
  | cons pair rest ih =>
    change (_ ∨ _) ↔ _
    rw [ih]
    constructor
    · rintro (first | ⟨later, member, value⟩)
      · exact ⟨pair, List.mem_cons_self, first⟩
      · exact ⟨later, List.mem_cons_of_mem _ member, value⟩
    · rintro ⟨later, member, value⟩
      rcases List.mem_cons.mp member with rfl | inside
      · exact Or.inl value
      · exact Or.inr ⟨later, inside, value⟩

theorem pairFamilies_retained {caller : Subst rowSig}
    (execution : ProtectedRun judgmentTag arrowTag s caller) (pairs : List (O × O))
    (within : ∀ pair ∈ pairs, pair.1 ∈ s.present ∧ pair.2 ∈ s.present) :
    pairFamilies judgmentTag arrowTag execution.run.last execution.source pairs =
      pairFamilies judgmentTag arrowTag s caller pairs := by
  induction pairs with
  | nil => rfl
  | cons pair rest ih =>
    change _ ∪ _ = _ ∪ _
    rw [pairFamily_retained execution pair.1 pair.2
      (within pair List.mem_cons_self).1 (within pair List.mem_cons_self).2,
      ih (fun later member => within later (List.mem_cons_of_mem _ member))]

variable [Infinite O]

theorem pairs_run_exists (pairs : List (O × O)) :
    ∀ (s : Store O) (caller : Subst rowSig),
      X.Models (a := PUnit.unit) (b := PUnit.unit) caller s.knowledge →
      (∀ pair ∈ pairs, pair.1 ∈ s.present ∧ pair.2 ∈ s.present) →
      ∃ execution : ProtectedRun judgmentTag arrowTag s caller,
        storeReadings execution.run.last execution.source =
          storeReadings s caller ∪ pairFamilies judgmentTag arrowTag s caller pairs := by
  induction pairs with
  | nil =>
    intro s caller known _
    refine ⟨ProtectedRun.start known, ?_⟩
    change storeReadings s caller = storeReadings s caller ∪ ∅
    exact (Set.union_empty _).symm
  | cons pair rest ih =>
    intro s caller known within
    obtain ⟨first, firstExact⟩ := pair_run_exists (judgmentTag := judgmentTag) (arrowTag := arrowTag)
      s caller known pair.1 pair.2
      (within pair List.mem_cons_self).1 (within pair List.mem_cons_self).2
    have laterWithin : ∀ later ∈ rest,
        later.1 ∈ first.run.last.present ∧ later.2 ∈ first.run.last.present := by
      intro later member
      have old := within later (List.mem_cons_of_mem _ member)
      exact ⟨run_present_mono first.run old.1, run_present_mono first.run old.2⟩
    obtain ⟨second, secondExact⟩ := ih first.run.last first.source first.known laterWithin
    refine ⟨first.append second, ?_⟩
    rw [ProtectedRun.append_last, ProtectedRun.append_source, secondExact, firstExact,
      pairFamilies_retained first rest (fun later member => within later (List.mem_cons_of_mem _ member))]
    exact Set.union_assoc _ _ _

#print axioms mem_pairFamilies
#print axioms pairFamilies_retained
#print axioms pairs_run_exists

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.ApplicationMachine
