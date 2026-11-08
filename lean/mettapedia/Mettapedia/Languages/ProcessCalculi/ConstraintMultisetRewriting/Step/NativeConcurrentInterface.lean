import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.NativeUpToDead
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.NativeConcurrent

/-!
# The native concurrent step is a multi-firing step of the interface up to dead names

* **A sequential run of a clear family is a concurrent word up to dead names**
  (`concurrent_of_familyClear`): each firing is independent, up to dead names, of every later one,
  and the residuals form a clear family again.
* **So a concurrent step of an offered clear word is a multi-firing step of the interface**
  (`stepMoves_of_concurrent`), labelled by the multiset of its labels.
* **Concurrent-step bisimilarity** (`concurrent_step_matched`): at a state that agrees up to dead names,
  for a program that does not see dead names, every native concurrent step is matched by a
  multi-firing step of the interface with the same labels, and the two targets agree up to dead
  names.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open NativeDead NativeIterated NativeUpToDead

variable {S : Signature} {O : Type} [DecidableEq O] {Γ : Ctx S} {sort : S.Srt}
  [DecidableEq S.Srt] [∀ result, DecidableEq (S.Op result)]

namespace NativeConcurrent

/-- **A sequential run of a clear family is a concurrent word up to dead names.** -/
theorem concurrent_of_familyClear : ∀ (n : ℕ) {s : NativeState S O Γ sort} (fs : List (LiveFiring s)),
    fs.length = n → FamilyClear s fs → ∀ {t : NativeState S O Γ sort}, Sequential s fs t →
      DeadTransport.Concurrent residuals s fs t
  | _, s, [], _, _, t, run => by
      rw [sequential_nil_iff.mp run]
      exact .nil s
  | 0, _, _ :: _, length, _, _, _ => absurd length (by simp)
  | n + 1, _, k :: rest, length, clear, _, run => by
      obtain ⟨admitted, later⟩ := sequential_cons_iff.mp run
      refine concurrent_cons_iff.mpr ⟨admitted, fun g member => ?_,
        concurrent_of_familyClear n _ (by rw [List.length_map]; exact Nat.succ.inj length)
          (familyClear_residual clear admitted) later⟩
      exact independent_of_clears admitted (clear.admitted g (List.mem_cons_of_mem _ member))
        ((List.pairwise_cons.mp clear.pairwise).1 g member)

variable {L : Type} {s : NativeState S O Γ sort}

/-- **A concurrent step of an offered clear word is a multi-firing step of the interface**, labelled by
the multiset of its labels. -/
theorem stepMoves_of_concurrent {program : L → (u : NativeState S O Γ sort) → LiveFiring u → Prop}
    {w : List (L × LiveFiring s)} (nonempty : w ≠ []) (offered : ∀ x ∈ w, program x.1 s x.2)
    {t : NativeState S O Γ sort} (step : Concurrent s ((w.map Prod.snd : List (LiveFiring s)) : Multiset (LiveFiring s)) t) :
    ∃ t', DeadTransport.StepMoves residuals program s (↑(w.map Prod.fst) : Multiset L) t' ∧ DeadEquiv t t' := by
  obtain ⟨t', run, agree⟩ := step.agrees rfl
  obtain ⟨_, same, clear, _⟩ := step
  have clearW : FamilyClear s (w.map Prod.snd) := clear.perm (Multiset.coe_eq_coe.mp same).symm
  exact ⟨t', ⟨w, nonempty, offered, concurrent_of_familyClear _ _ rfl clearW run, rfl⟩, agree⟩

/-- **Concurrent-step bisimilarity**: at a state that agrees up to dead names, for a program that does
not see dead names, every native concurrent step of an offered clear word is matched by a multi-firing
step of the interface with the same labels, and the targets agree up to dead names. -/
theorem concurrent_step_matched {program : L → (u : NativeState S O Γ sort) → LiveFiring u → Prop}
    (invariant : DeadInvariant program) {s' : NativeState S O Γ sort} (same : DeadEquiv s s')
    {w : List (L × LiveFiring s)} (nonempty : w ≠ []) (offered : ∀ x ∈ w, program x.1 s x.2)
    {t : NativeState S O Γ sort} (step : Concurrent s ((w.map Prod.snd : List (LiveFiring s)) : Multiset (LiveFiring s)) t) :
    ∃ t', DeadTransport.StepMoves residuals program s' (↑(w.map Prod.fst) : Multiset L) t' ∧ DeadEquiv t t' := by
  obtain ⟨u, stepped, agree⟩ := stepMoves_of_concurrent nonempty offered step
  obtain ⟨v, ⟨e⟩, ⟨e'⟩⟩ := same
  obtain ⟨t', stepped', agree'⟩ :=
    DeadTransport.match_step ((invariant_iff program).mpr invariant) carriesWords e e' stepped
  exact ⟨t', stepped', agree.trans agree'⟩

end NativeConcurrent

#print axioms NativeConcurrent.concurrent_of_familyClear
#print axioms NativeConcurrent.stepMoves_of_concurrent
#print axioms NativeConcurrent.concurrent_step_matched

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface
