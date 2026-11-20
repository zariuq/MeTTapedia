import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.RuleOccurrences.Relay
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.RuleOccurrences.Protection

/-!
# Removing a rule removes one occurrence

Over first-order atoms at one frame. The code system (`codes`) has the **remover** as code `0` and
the rule `Relay.bump n` as code `n + 1`; the constant `100 + k` denotes the code `k`.

**The remover** (`remover`) takes a message, a row labelled by its own unknown, and removes one held
rule whose code the unknown denotes.

At the state that holds the remover and **two** occurrences of the code `2`, with a message carrying
the code `2`:

* `remove_admitted`: the firing that removes one of the two occurrences is admitted;
* `removed_gone`, `other_stays`, `other_label`: the result does not hold the removed occurrence, and
  holds the other one with its label unchanged. One removal removes one copy.

**A rule may remove itself** (`self_remove_admitted`, `self_removed_gone`): with a message carrying
the code `0`, the remover removes the occurrence it uses, and the result does not hold it.

**Controls.**
* `wrong_code_refused`: a message carrying another code does not remove an occurrence of the code
  `2`.
* `remove_refused_sealed`: when the zone is guarded, the sealed step refuses the removal, which the
  unrestricted step admits.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.RuleOccurrences.Removal

open Interface (Frames)
open MeTTaCalculus.OccurrenceCommits (Enabled fire)
open Mettapedia.Logic.LP
open Examples (Tm X E x c shift)
open _root_.Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Controls
  (atoms action)

/-- **The remover**: take a message `x` and remove one held rule whose code `x` denotes. -/
def remover : Spec Tm ℕ Unit :=
  ⟨PUnit.unit, ⟨[x], [], [], [], []⟩, [], [], [], [], [], [((), x)], []⟩

/-- The code system: code `0` is the remover, code `n + 1` is `Relay.bump n`; the constant `100 + k`
denotes the code `k`. -/
def codes : Codes Tm ℕ Unit where
  unfold
    | 0 => remover
    | n + 1 => Spec.ofRule (Relay.bump n)
  denotes _ t k := t = c (100 + k)
  close _ _ _ := none

/-- A message carrying the code `k` at row `0`; held persistently: the remover at identity `0`, and
the code `2` at the identities `5` and `6`. -/
def twice (k : ℕ) : RState Tm ℕ ℕ ℕ Unit :=
  ⟨⟨PUnit.unit, [], {0}, fun _ => c (100 + k)⟩, {0, 5, 6},
    fun ρ => ⟨if ρ = 0 then 0 else 2, [], .persistent, ()⟩⟩

/-- The remover takes the message and removes the occurrence `ρ`. -/
def removeFiring (k ρ : ℕ) : RFiring ℕ ℕ E codes (twice k) :=
  ⟨.held 0, PUnit.unit, shift, ⟨[0], [], []⟩, [], [], [], [ρ], []⟩

theorem remove_information (k ρ : ℕ) :
    (removeFiring k ρ).information X = [(.var 1, c (100 + k))] := rfl

theorem remove_fresh (k ρ : ℕ) : (removeFiring k ρ).Fresh X := by
  intro b g h
  refine ⟨fun v => if v = 1 then h 0 else g v, ?_, ?_⟩
  · rintro t ((member | member | ⟨o, -, rfl⟩) | ⟨held, -, member⟩)
    · simp [twice] at member
    · simp [twice] at member
    · rfl
    · exact absurd member List.not_mem_nil
  · intro t member
    have inside : t ∈ remover.terms := member
    simp [remover, Spec.terms, Rule.terms] at inside
    subst inside
    rfl

/-- **A removal is admitted** when the occurrence is held and the message carries its code. -/
theorem remove_admitted_of {k ρ : ℕ} (held : ρ ∈ ({0, 5, 6} : Finset ℕ))
    (carried : (if ρ = 0 then 0 else 2) = k) : (removeFiring k ρ).Admits X (∅ : Set ℕ) := by
  refine ⟨⟨remove_fresh k ρ, ⟨List.nodup_singleton 0, List.nodup_nil, rfl, rfl, rfl, rfl⟩,
    ⟨Finset.mem_insert_self 0 {5, 6}, rfl, rfl, List.nodup_nil, rfl,
      fun _ inside => absurd inside List.not_mem_nil, rfl, List.nodup_singleton ρ, ?_, rfl⟩⟩,
    ?_, ?_, ?_⟩
  · intro y inside
    have member : y ∈ [((((), x) : Unit × Tm PUnit.unit), ρ)] := inside
    obtain rfl := List.mem_singleton.mp member
    exact ⟨held, rfl⟩
  · apply enabled_of <;> simp [removeFiring, twice]
  · rw [remove_information]
    exact ⟨PUnit.unit, fun _ => c (100 + k), fun e member => by
      obtain rfl := List.mem_singleton.mp member
      rfl⟩
  · rw [remove_information]
    intro b σ solved
    have value : σ 1 = c (100 + k) := solved (.var 1, c (100 + k)) List.mem_cons_self
    refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_, ?_⟩
    · intro check member
      exact absurd member List.not_mem_nil
    · intro q member
      exact absurd member List.not_mem_nil
    · intro q member
      exact absurd member List.not_mem_nil
    · intro y member
      exact absurd member List.not_mem_nil
    · intro y member
      have inside : y ∈ [((((), x) : Unit × Tm PUnit.unit), ρ)] := member
      obtain rfl := List.mem_singleton.mp inside
      show σ 1 = c (100 + (if ρ = 0 then 0 else 2))
      rw [carried]
      exact value
    · intro y member
      exact absurd member List.not_mem_nil

/-- **The removal is admitted**: the message carries the code of the occurrence removed. -/
theorem remove_admitted : (removeFiring 2 5).Admits X (∅ : Set ℕ) :=
  remove_admitted_of (by decide) rfl

/-- **A rule may remove itself**: with a message that carries the remover's own code, the firing of
the remover that removes the occurrence it uses is admitted. Admission reads the state before the
firing, in which that occurrence is held. -/
theorem self_remove_admitted : (removeFiring 0 0).Admits X (∅ : Set ℕ) :=
  remove_admitted_of (by decide) rfl

/-- **After it the remover is not held.** -/
theorem self_removed_gone : 0 ∉ ((removeFiring 0 0).result X).rules := by
  intro inside
  rcases (RFiring.mem_result_rules _).mp inside with kept | made
  · exact ((RFiring.mem_kept _).mp kept).2 (Or.inr (List.mem_singleton_self 0))
  · exact absurd made List.not_mem_nil

/-- **The removed occurrence is gone.** -/
theorem removed_gone : 5 ∉ ((removeFiring 2 5).result X).rules := by
  intro inside
  rcases (RFiring.mem_result_rules _).mp inside with kept | made
  · exact ((RFiring.mem_kept _).mp kept).2 (Or.inr (List.mem_singleton_self 5))
  · exact absurd made List.not_mem_nil

/-- **The other copy stays.** -/
theorem other_stays : 6 ∈ ((removeFiring 2 5).result X).rules := by
  refine (RFiring.mem_result_rules _).mpr (Or.inl ((RFiring.mem_kept _).mpr ⟨by decide, ?_⟩))
  intro takes
  rcases takes with used | removed
  · exact absurd (Use.held.inj used.1) (by decide)
  · exact absurd (List.mem_singleton.mp removed) (by decide)

/-- Its label is unchanged. -/
theorem other_label : ((removeFiring 2 5).result X).held 6 = ⟨2, [], .persistent, ()⟩ := rfl

/-! ## Controls -/

/-- **A message carrying another code removes nothing of the code `2`.** -/
theorem wrong_code_refused : ¬ (removeFiring 3 5).Admits X (∅ : Set ℕ) := by
  intro admitted
  have asks := admitted.2.2.2
  rw [remove_information] at asks
  have holds := asks PUnit.unit (fun _ => c 103) (fun e member => by
    obtain rfl := List.mem_singleton.mp member
    rfl)
  have inside : ((((), x) : Unit × Tm PUnit.unit), (5 : ℕ)) ∈
      (removeFiring 3 5).spec.removes.zip (removeFiring 3 5).removedRules :=
    List.mem_singleton_self _
  have denoted : c 103 = c (100 + 2) := holds.2.2.2.1 _ inside
  exact absurd (Term.const.inj denoted) (by decide)

/-- Every zone is guarded. -/
def guarded : Unit → Prop := fun _ => True

/-- **The sealed step refuses the removal**, which the unrestricted step admits (`remove_admitted`). -/
theorem remove_refused_sealed :
    ¬ (sealedStep X ℕ ℕ E codes (∅ : Set ℕ) guarded).Admits (removeFiring 2 5) :=
  fun admitted => admitted.2.2.2.1 5 (Or.inr (List.mem_singleton_self 5)) trivial

#print axioms remove_admitted_of
#print axioms remove_admitted
#print axioms self_remove_admitted
#print axioms self_removed_gone
#print axioms removed_gone
#print axioms other_stays
#print axioms other_label
#print axioms wrong_code_refused
#print axioms remove_refused_sealed

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.RuleOccurrences.Removal
