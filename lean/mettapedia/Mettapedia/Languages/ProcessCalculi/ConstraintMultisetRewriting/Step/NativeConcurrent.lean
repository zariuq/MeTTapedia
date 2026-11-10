import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.NativeIteratedAgreement

/-!
# The native concurrent step: a clear family fired at once

## The step

**The native concurrent step** (`Concurrent s M t`) fires a finite multiset `M` of live firings that
form a clear family (`FamilyClear`: admitted, pairwise clear, jointly solvable) at once. It publishes
the state of a sequentialization of `M`.

* **It is defined up to dead names** (`Concurrent.unique`): two concurrent steps of one multiset
  publish states that agree up to dead names.
* **It agrees with every sequentialization** (`Concurrent.agrees`): every order of `M` is a
  sequential run, and its final state agrees up to dead names with the concurrent step's.
* **Every clear family fires concurrently** (`concurrent_of_clear`).
* **Its present occurrences are the wave formula** (`Concurrent.present`): the state's present
  occurrences with every take of the family removed and every make added
  (`OccurrenceCommits.effectOf`), the same for every sequentialization.

## Bisimilarity with the sequential step

* **The concurrent step's state is bisimilar to every sequentialization's** (`Concurrent.bisimilar`),
  for every program that does not see dead names.
* **For closed programs a sequential run is a word of labelled moves** (`sequential_chain`): the
  residual of a closed firing is the same closed firing at the later state
  (`ClosedFiring.residualAt_atState`). So a concurrent step of offered closed firings is matched by a
  word of single moves in every order of its labels, ending at a bisimilar state
  (`Concurrent.chain`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits (fire fireList fireList_cons effectOf
  fireList_eq_fire_effectOf fireList_perm MatchedAt)
open NativeResidual NativeDead NativeIterated

variable {S : Signature} {O : Type} [DecidableEq O] {Γ : Ctx S} {sort : S.Srt}
  [DecidableEq S.Srt] [∀ result, DecidableEq (S.Op result)]

namespace NativeConcurrent

variable {s : NativeState S O Γ sort}

/-! ## The step -/

/-- **The native concurrent step**: a finite multiset of live firings forming a clear family, fired
at once; `t` is the state a sequentialization publishes. -/
def Concurrent (s : NativeState S O Γ sort) (M : Multiset (LiveFiring s)) (t : NativeState S O Γ sort) : Prop :=
  ∃ l : List (LiveFiring s), (l : Multiset (LiveFiring s)) = M ∧ FamilyClear s l ∧ Sequential s l t

/-- **Every clear family fires concurrently.** -/
theorem concurrent_of_clear {l : List (LiveFiring s)} (clear : FamilyClear s l) :
    ∃ t, Concurrent s (l : Multiset (LiveFiring s)) t := by
  obtain ⟨t, run⟩ := every_order_admitted clear (List.Perm.refl l)
  exact ⟨t, l, rfl, clear, run⟩

/-- **The concurrent step agrees with every sequentialization**: every order of the multiset is a
sequential run, and its final state agrees with the concurrent step's up to dead names. -/
theorem Concurrent.agrees {M : Multiset (LiveFiring s)} {t : NativeState S O Γ sort} (step : Concurrent s M t)
    {order : List (LiveFiring s)} (same : (order : Multiset (LiveFiring s)) = M) :
    ∃ t', Sequential s order t' ∧ DeadEquiv t t' := by
  obtain ⟨l, rfl, clear, run⟩ := step
  have perm : order.Perm l := Multiset.coe_eq_coe.mp same
  obtain ⟨t', other⟩ := every_order_admitted clear perm
  exact ⟨t', other, orders_agree _ l rfl clear perm run other⟩

/-- **The concurrent step is defined up to dead names.** -/
theorem Concurrent.unique {M : Multiset (LiveFiring s)} {t t' : NativeState S O Γ sort} (first : Concurrent s M t)
    (second : Concurrent s M t') : DeadEquiv t t' := by
  obtain ⟨l, same, _, run⟩ := second
  obtain ⟨t'', other, agree⟩ := first.agrees same
  rw [other.unique run] at agree
  exact agree

/-- **A sequential run publishes the occurrences its commits fire**, in order. -/
theorem sequential_present {l : List (LiveFiring s)} {t : NativeState S O Γ sort} (run : Sequential s l t) :
    t.state.present = fireList s.state.present (l.map fun f => f.selection.commit (T := Unit)) := by
  induction run with
  | nil s => rfl
  | @cons s' f rest admitted t' later ih =>
      have head : (native.result f.toNative admitted).state.present = fire s'.state.present (f.selection.commit (T := Unit)) :=
        native.present_result f.toNative admitted
      rw [ih, head, List.map_map]
      rfl

/-- **The concurrent step's present occurrences are the wave formula**: the state's present
occurrences with every take of the family removed and every make added. -/
theorem Concurrent.present {l : List (LiveFiring s)} {t : NativeState S O Γ sort}
    (step : Concurrent s (l : Multiset (LiveFiring s)) t) :
    t.state.present = fire s.state.present (effectOf (l.map fun f => f.selection.commit (T := Unit))) := by
  obtain ⟨l', same, clear, run⟩ := step
  have perm : l.Perm l' := (Multiset.coe_eq_coe.mp same).symm
  have matched : MatchedAt s.state.present (l.map fun f => f.selection.commit (T := Unit)) := by
    intro c member
    obtain ⟨f, inL, rfl⟩ := List.mem_map.mp member
    obtain ⟨_, enabled, _, _⟩ := (native_admits_iff f.toNative).mp (clear.admitted f (perm.subset inL))
    exact ⟨enabled.taken_subset, enabled.fresh⟩
  rw [sequential_present run, ← fireList_eq_fire_effectOf matched]
  exact (fireList_perm matched (perm.map _)).symm

/-! ## Bisimilarity with the sequential step -/

/-- **The concurrent step's state is bisimilar to every sequentialization's**, for every program that
does not see dead names. -/
theorem Concurrent.bisimilar {L : Type} {program : L → (u : NativeState S O Γ sort) → LiveFiring u → Prop}
    (invariant : DeadInvariant program) {M : Multiset (LiveFiring s)} {t : NativeState S O Γ sort}
    (step : Concurrent s M t) {order : List (LiveFiring s)} (same : (order : Multiset (LiveFiring s)) = M)
    {t' : NativeState S O Γ sort} (run : Sequential s order t') :
    Race.Generic.Bisimilar native.toStep (liveOffers program) t t' := by
  obtain ⟨t'', other, agree⟩ := step.agrees same
  rw [other.unique run] at agree
  exact bisimilar_of_deadEquiv invariant agree

omit [DecidableEq O] [DecidableEq S.Srt] [∀ result, DecidableEq (S.Op result)] in
/-- **Carrying a closed firing along any maps of frames is the closed firing at the later state.** -/
theorem ClosedFiring.atState_carryAlong {u : NativeState S O Γ sort} (k : ClosedFiring S O Γ sort)
    (φ : Assignment (ContextualActivatedStep.source s.locals s.state.declarations)
      (ContextualActivatedStep.source u.locals u.state.declarations))
    (ψ : Assignment (ContextualActivatedStep.target s.locals s.state.declarations)
      (ContextualActivatedStep.target u.locals u.state.declarations)) :
    carryAlong φ ψ (k.atState s) = k.atState u := by
  have rule : (k.rule.map (instantiate (fromNone _))).map (instantiate φ) = k.rule.map (instantiate (fromNone _)) := by
    rw [OccurrenceRelabeling.rule_map_comp]
    exact congrArg (fun mapping => k.rule.map mapping) (funext fun term =>
      (Assignment.instantiate_compose _ _ term).symm.trans
        (congrArg (fun assignment => instantiate assignment term) (fromNone_unique φ)))
  have outputs : (fun o => instantiate ψ (instantiate (fromNone _) (k.outputs o))) =
      fun o => instantiate (fromNone _) (k.outputs o) :=
    funext fun o => (Assignment.instantiate_compose _ _ _).symm.trans
      (congrArg (fun assignment => instantiate assignment (k.outputs o)) (fromNone_unique ψ))
  have patterns : (k.patterns.map fun pattern => (instantiate (fromNone _) pattern.1, pattern.2)).map
      (fun pattern => (instantiate ψ pattern.1, pattern.2)) =
      k.patterns.map fun pattern => (instantiate (fromNone _) pattern.1, pattern.2) := by
    rw [List.map_map]
    exact List.map_congr_left fun pattern _ => congrArg (fun term => (term, pattern.2))
      ((Assignment.instantiate_compose _ _ _).symm.trans
        (congrArg (fun assignment => instantiate assignment pattern.1) (fromNone_unique ψ)))
  unfold carryAlong ClosedFiring.atState
  rw [rule, outputs, patterns]

/-- **The residual of a closed firing is the same closed firing at the later state.** -/
theorem ClosedFiring.residualAt_atState (k : ClosedFiring S O Γ sort)
    (G : ContextualConditionalExecution.Firing s.locals s.state) :
    (k.atState s).residualAt G = k.atState (rawTarget G) :=
  (residualAt_eq G (k.atState s)).trans (ClosedFiring.atState_carryAlong k _ _)

/-- **A word of labelled moves**: single steps of the generic labelled step, one after another. -/
inductive Chain {L : Type} (program : L → (u : NativeState S O Γ sort) → LiveFiring u → Prop) :
    NativeState S O Γ sort → List L → NativeState S O Γ sort → Prop
  | nil (s : NativeState S O Γ sort) : Chain program s [] s
  | cons {s s' t : NativeState S O Γ sort} {ℓ : L} {labels : List L}
      (moved : Race.Generic.Moves native.toStep (liveOffers program) s ℓ s') (rest : Chain program s' labels t) :
      Chain program s (ℓ :: labels) t

/-- **For closed programs a sequential run is a word of labelled moves**, the labels in the order of
the run. -/
theorem sequential_chain {L : Type} (program : L → ClosedFiring S O Γ sort → Prop) :
    ∀ (w : List (L × ClosedFiring S O Γ sort)) {s t : NativeState S O Γ sort}, (∀ x ∈ w, program x.1 x.2) →
      Sequential s (w.map fun x => x.2.atState s) t → Chain (closedOffers program) s (w.map Prod.fst) t
  | [], s, t, _, run => by
      rw [List.map_nil, sequential_nil_iff] at run
      rw [run]
      exact .nil s
  | x :: rest, s, t, offered, run => by
      obtain ⟨admitted, later⟩ := sequential_cons_iff.mp run
      have residuals : (rest.map fun y => y.2.atState s).map (residualAfter admitted) =
          rest.map fun y => y.2.atState (native.result (x.2.atState s).toNative admitted) := by
        rw [List.map_map]
        exact List.map_congr_left fun y _ => ClosedFiring.residualAt_atState y.2 (LiveFiring.execution admitted)
      rw [residuals] at later
      exact .cons ⟨(x.2.atState s).toNative, admitted, ⟨x.2.atState s, ⟨x.2, offered x List.mem_cons_self, rfl⟩, rfl⟩, rfl⟩
        (sequential_chain program rest (fun y member => offered y (List.mem_cons_of_mem _ member)) later)

/-- **A concurrent step of offered closed firings is matched by a word of single moves in every order
of its labels**, ending at a state that agrees up to dead names, and is bisimilar. -/
theorem Concurrent.chain {L : Type} (program : L → ClosedFiring S O Γ sort → Prop)
    {w : List (L × ClosedFiring S O Γ sort)} (offered : ∀ x ∈ w, program x.1 x.2) {t : NativeState S O Γ sort}
    (step : Concurrent s ((w.map fun x => x.2.atState s) : Multiset (LiveFiring s)) t)
    {w' : List (L × ClosedFiring S O Γ sort)} (perm : w'.Perm w) :
    ∃ t', Chain (closedOffers program) s (w'.map Prod.fst) t' ∧ DeadEquiv t t' ∧
      Race.Generic.Bisimilar native.toStep (liveOffers (closedOffers program)) t t' := by
  obtain ⟨t', run, agree⟩ := step.agrees (order := w'.map fun x => x.2.atState s)
    (Multiset.coe_eq_coe.mpr (perm.map _))
  exact ⟨t', sequential_chain program w' (fun x member => offered x (perm.subset member)) run, agree,
    bisimilar_of_deadEquiv (closedOffers_invariant program) agree⟩

end NativeConcurrent

#print axioms NativeConcurrent.concurrent_of_clear
#print axioms NativeConcurrent.Concurrent.agrees
#print axioms NativeConcurrent.Concurrent.unique
#print axioms NativeConcurrent.sequential_present
#print axioms NativeConcurrent.Concurrent.present
#print axioms NativeConcurrent.Concurrent.bisimilar
#print axioms NativeConcurrent.ClosedFiring.residualAt_atState
#print axioms NativeConcurrent.sequential_chain
#print axioms NativeConcurrent.Concurrent.chain

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface
