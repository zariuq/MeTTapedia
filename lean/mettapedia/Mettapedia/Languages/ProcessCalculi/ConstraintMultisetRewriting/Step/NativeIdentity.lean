import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.NativeTransport
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.RaceGenericWeak

/-!
# Identity of renamed native states

Native states related by a renaming of occurrences (`NativeRenamed`) are identified by the races
layer over the generic step (`RaceGeneric`), read at the native step, for every **equivariant**
program: one whose offers are kept by renaming a state with a firing (`NativeEquivariant`).

* **Renaming is an equivalence** of states (`NativeRenamed.refl`, `.symm`, `.trans`) and of events
  (`NativeEventRenamed.refl`, `.symm`, `.trans`).
* **Bisimilar** (`native_bisimilar_of_renamed`): a move of a state is answered by the renamed
  firing at the renamed state (`native_moves_rename`), whose result is the renamed result; a move of
  the renamed state is answered by the firing carried back (`native_moves_unrename`).
* **Hennessy–Milner, weak and branching** (`native_sat_iff_of_renamed`,
  `native_weakBisimilar_of_renamed`, `native_branchingBisimilar_of_renamed`).
* **History-preserving bisimilar** (`native_hpBisimilar_of_renamed`) when the independence of events
  respects renaming (`NativeIndepEquivariant`): histories related event by event have the same
  causal pasts (`past_congr_of`, the causal-past congruence of `RaceGeneric` for any relation of
  events).

Step bisimilarity is not stated here: the races layer's multi-firing steps are words of
independent firings, and independence is defined through a residual of the step's transport, which
the native step does not have yet.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Race.Generic (Moves Bisimilar Sat system HMoves HPBisimilar past directPast mem_directPast Event History
  WeakBisimilar BranchingBisimilar)
open Mettapedia.GSLT.HennessyMilner (Formula)

/-! ## The causal past along any relation of events -/

section Past

universe uS uF

variable {State : Type uS} {Fir : State → Type uF}

/-- **Related histories give the same causal pasts** to related events, for every relation of
events that the independence respects. -/
theorem past_congr_of {E : Event State Fir → Event State Fir → Prop}
    {indep : Event State Fir → Event State Fir → Prop}
    (invariant : ∀ ⦃a a' b b' : Event State Fir⦄, E a a' → E b b' → (indep a b ↔ indep a' b'))
    {h h' : History State Fir} (related : List.Forall₂ (fun a b => E a.1 b.1 ∧ a.2 = b.2) h h')
    {e e' : Event State Fir} (same : E e e') : past indep h e = past indep h' e' := by
  have length : h.length = h'.length := related.length_eq
  have direct : directPast indep h e = directPast indep h' e' := by
    ext i
    rw [mem_directPast, mem_directPast, length]
    have rel := Race.Generic.forall₂_getElem? related i
    constructor
    · rintro ⟨lt, x, get, dependent⟩
      rw [get] at rel
      rcases get' : h'[i]? with _ | y
      · rw [get'] at rel
        cases rel
      · rw [get'] at rel
        cases rel with
        | some r => exact ⟨lt, y, rfl, fun ind => dependent ((invariant r.1 same).mpr ind)⟩
    · rintro ⟨lt, y, get', dependent⟩
      rw [get'] at rel
      rcases get : h[i]? with _ | x
      · rw [get] at rel
        cases rel
      · rw [get] at rel
        cases rel with
        | some r => exact ⟨lt, x, rfl, fun ind => dependent ((invariant r.1 same).mp ind)⟩
  unfold past
  rw [direct]
  congr 1
  refine Finset.biUnion_congr rfl fun i _ => ?_
  have rel := Race.Generic.forall₂_getElem? related i
  rcases get : h[i]? with _ | x <;> rcases get' : h'[i]? with _ | y <;> rw [get, get'] at rel <;>
    first
    | rfl
    | (cases rel with | some r => simp [r.2])
    | cases rel

end Past

variable {S : Signature} {O : Type} [DecidableEq O] {Γ : Ctx S} {sort : S.Srt}
  [DecidableEq S.Srt] [∀ result, DecidableEq (S.Op result)]

/-- **Native states related by a renaming of occurrences.** -/
def NativeRenamed (s t : NativeState S O Γ sort) : Prop := ∃ π : O ≃ O, s.rename π = t

variable {L : Type*}

omit [DecidableEq O] [DecidableEq S.Srt] [∀ result, DecidableEq (S.Op result)] in
theorem NativeRenamed.refl (s : NativeState S O Γ sort) : NativeRenamed s s :=
  ⟨Equiv.refl O, NativeState.rename_refl s⟩

omit [DecidableEq O] [DecidableEq S.Srt] [∀ result, DecidableEq (S.Op result)] in
theorem NativeRenamed.symm {s t : NativeState S O Γ sort} (renamed : NativeRenamed s t) : NativeRenamed t s := by
  obtain ⟨π, rfl⟩ := renamed
  exact ⟨π.symm, NativeState.rename_symm π s⟩

omit [DecidableEq O] [DecidableEq S.Srt] [∀ result, DecidableEq (S.Op result)] in
theorem NativeRenamed.trans {s t u : NativeState S O Γ sort} (first : NativeRenamed s t)
    (second : NativeRenamed t u) : NativeRenamed s u := by
  obtain ⟨π, rfl⟩ := first
  obtain ⟨ρ, rfl⟩ := second
  exact ⟨π.trans ρ, (NativeState.rename_trans π ρ s).symm⟩

/-- **An equivariant native program**: renaming a state with a firing keeps the firing's labels. -/
def NativeEquivariant (offers : L → (s : NativeState S O Γ sort) → NativeFiring s → Prop) : Prop :=
  ∀ (π : O ≃ O) (ℓ : L) (s : NativeState S O Γ sort) (f : NativeFiring s),
    offers ℓ (s.rename π) (f.rename π) ↔ offers ℓ s f

variable {offers : L → (s : NativeState S O Γ sort) → NativeFiring s → Prop}

/-- **A move of a state is a move of the renamed state**, by the renamed firing. -/
theorem native_moves_rename (equivariant : NativeEquivariant offers) (π : O ≃ O)
    {s s' : NativeState S O Γ sort} {ℓ : L} (moved : Moves native.toStep offers s ℓ s') :
    Moves native.toStep offers (s.rename π) ℓ (s'.rename π) := by
  obtain ⟨f, realized, offered, rfl⟩ := moved
  have realized' := (NativeFiring.realized_rename_iff π f).mpr realized
  exact ⟨f.rename π, realized', (equivariant π ℓ s f).mpr offered,
    (native_result_rename π f realized realized').symm⟩

/-- **A move of the renamed state comes from a move of the state**, by the firing carried back. -/
theorem native_moves_unrename (equivariant : NativeEquivariant offers) (π : O ≃ O)
    {s t' : NativeState S O Γ sort} {ℓ : L} (moved : Moves native.toStep offers (s.rename π) ℓ t') :
    ∃ s', Moves native.toStep offers s ℓ s' ∧ s'.rename π = t' := by
  obtain ⟨g, realized, offered, rfl⟩ := moved
  have realized' := (NativeFiring.realized_unrename_iff π g).mpr realized
  refine ⟨_, ⟨NativeFiring.unrename π g, realized', ?_, rfl⟩, native_result_unrename π g realized' realized⟩
  exact (equivariant π ℓ s _).mp (by rw [NativeFiring.rename_unrename]; exact offered)

/-- **Renamed native states are bisimilar**, for every equivariant program. -/
theorem native_bisimilar_of_renamed (equivariant : NativeEquivariant offers)
    {s t : NativeState S O Γ sort} (renamed : NativeRenamed s t) : Bisimilar native.toStep offers s t := by
  refine ⟨NativeRenamed, ⟨?_, ?_, fun _ _ _ atom => atom.elim⟩, renamed⟩
  · rintro s t ⟨π, rfl⟩ ℓ s' moved
    exact ⟨_, native_moves_rename equivariant π moved, π, rfl⟩
  · rintro s t ⟨π, rfl⟩ ℓ t' moved
    obtain ⟨s', moved', renamed'⟩ := native_moves_unrename equivariant π moved
    exact ⟨s', moved', π, renamed'⟩

/-- **Renamed native states satisfy the same Hennessy–Milner formulas.** -/
theorem native_sat_iff_of_renamed (equivariant : NativeEquivariant offers)
    {s t : NativeState S O Γ sort} (renamed : NativeRenamed s t) (φ : Formula PEmpty.{1} L) :
    Sat native.toStep offers φ s ↔ Sat native.toStep offers φ t :=
  (system native.toStep offers).logicallyEquivalent_of_bisimilar (native_bisimilar_of_renamed equivariant renamed) φ

/-- **Renamed native states are weakly bisimilar.** -/
theorem native_weakBisimilar_of_renamed (equivariant : NativeEquivariant offers) (internal : L → Prop)
    {s t : NativeState S O Γ sort} (renamed : NativeRenamed s t) :
    WeakBisimilar native.toStep offers internal s t :=
  Race.Weak.bisimilar_of_strong (native_bisimilar_of_renamed equivariant renamed)

/-- **Renamed native states are branching bisimilar.** -/
theorem native_branchingBisimilar_of_renamed (equivariant : NativeEquivariant offers) (internal : L → Prop)
    {s t : NativeState S O Γ sort} (renamed : NativeRenamed s t) :
    BranchingBisimilar native.toStep offers internal s t :=
  Race.Weak.branching_of_strong (native_bisimilar_of_renamed equivariant renamed)

/-! ## Histories -/

/-- **Native events related by a renaming**: the second is the first renamed, state and firing. -/
def NativeEventRenamed (a b : Event (NativeState S O Γ sort) NativeFiring) : Prop :=
  ∃ π : O ≃ O, b = ⟨a.1.rename π, a.2.rename π⟩

omit [DecidableEq O] [DecidableEq S.Srt] [∀ result, DecidableEq (S.Op result)] in
theorem NativeEventRenamed.refl (a : Event (NativeState S O Γ sort) NativeFiring) : NativeEventRenamed a a :=
  ⟨Equiv.refl O, (NativeFiring.sigma_rename_refl a.1 a.2).symm⟩

omit [DecidableEq O] [DecidableEq S.Srt] [∀ result, DecidableEq (S.Op result)] in
theorem NativeEventRenamed.trans {a b c : Event (NativeState S O Γ sort) NativeFiring}
    (first : NativeEventRenamed a b) (second : NativeEventRenamed b c) : NativeEventRenamed a c := by
  obtain ⟨π, rfl⟩ := first
  obtain ⟨ρ, rfl⟩ := second
  exact ⟨π.trans ρ, NativeFiring.sigma_rename_trans π ρ a.1 a.2⟩

omit [DecidableEq O] [DecidableEq S.Srt] [∀ result, DecidableEq (S.Op result)] in
theorem NativeEventRenamed.symm {a b : Event (NativeState S O Γ sort) NativeFiring}
    (renamed : NativeEventRenamed a b) : NativeEventRenamed b a := by
  obtain ⟨π, rfl⟩ := renamed
  refine ⟨π.symm, ?_⟩
  have back := NativeFiring.sigma_rename_trans π π.symm a.1 a.2
  rw [Equiv.self_trans_symm, NativeFiring.sigma_rename_refl] at back
  exact back.symm

/-- **An independence of native events that respects renaming.** -/
def NativeIndepEquivariant
    (indep : Event (NativeState S O Γ sort) NativeFiring → Event (NativeState S O Γ sort) NativeFiring → Prop) :
    Prop :=
  ∀ ⦃a a' b b' : Event (NativeState S O Γ sort) NativeFiring⦄,
    NativeEventRenamed a a' → NativeEventRenamed b b' → (indep a b ↔ indep a' b')

/-- **Renamed native states are history-preserving bisimilar**, for every equivariant program and
every independence of events that respects renaming. -/
theorem native_hpBisimilar_of_renamed (equivariant : NativeEquivariant offers)
    {indep : Event (NativeState S O Γ sort) NativeFiring → Event (NativeState S O Γ sort) NativeFiring → Prop}
    (indepEquivariant : NativeIndepEquivariant indep) {s t : NativeState S O Γ sort}
    (renamed : NativeRenamed s t) : HPBisimilar indep native.toStep offers s t := by
  refine ⟨fun x y => NativeRenamed x.1 y.1 ∧
      List.Forall₂ (fun a b => NativeEventRenamed a.1 b.1 ∧ a.2 = b.2) x.2 y.2,
    ⟨?_, ?_, fun _ _ _ atom => atom.elim⟩, renamed, .nil⟩
  · rintro ⟨s, hs⟩ ⟨t, ht⟩ ⟨⟨π, same⟩, histories⟩ lab x' ⟨f, realized, offered, labelled, rfl⟩
    dsimp only at same histories labelled offered realized f ⊢
    subst same
    have realized' := (NativeFiring.realized_rename_iff π f).mpr realized
    have event : NativeEventRenamed (⟨s, f⟩ : Event (NativeState S O Γ sort) NativeFiring)
        ⟨s.rename π, f.rename π⟩ := ⟨π, rfl⟩
    refine ⟨(native.result (f.rename π) realized', ht ++ [(⟨s.rename π, f.rename π⟩, lab.2)]),
      ⟨f.rename π, realized', (equivariant π lab.1 s f).mpr offered,
        labelled.trans (past_congr_of indepEquivariant histories event), rfl⟩,
      ⟨π, (native_result_rename π f realized realized').symm⟩, ?_⟩
    exact List.rel_append histories (.cons ⟨event, rfl⟩ .nil)
  · rintro ⟨s, hs⟩ ⟨t, ht⟩ ⟨⟨π, same⟩, histories⟩ lab y' ⟨g, realized, offered, labelled, rfl⟩
    dsimp only at same histories labelled offered realized g ⊢
    subst same
    have realized' := (NativeFiring.realized_unrename_iff π g).mpr realized
    have event : NativeEventRenamed (⟨s, NativeFiring.unrename π g⟩ : Event (NativeState S O Γ sort) NativeFiring)
        ⟨s.rename π, g⟩ :=
      ⟨π, congrArg (Sigma.mk (s.rename π)) (NativeFiring.rename_unrename π g).symm⟩
    refine ⟨(native.result (NativeFiring.unrename π g) realized',
        hs ++ [(⟨s, NativeFiring.unrename π g⟩, lab.2)]),
      ⟨NativeFiring.unrename π g, realized',
        (equivariant π lab.1 s _).mp (by rw [NativeFiring.rename_unrename]; exact offered),
        labelled.trans (past_congr_of indepEquivariant histories event).symm, rfl⟩,
      ⟨π, native_result_unrename π g realized' realized⟩, ?_⟩
    exact List.rel_append histories (.cons ⟨event, rfl⟩ .nil)

#print axioms past_congr_of
#print axioms NativeRenamed.symm
#print axioms NativeRenamed.trans
#print axioms NativeEventRenamed.symm
#print axioms NativeEventRenamed.trans
#print axioms native_moves_rename
#print axioms native_moves_unrename
#print axioms native_bisimilar_of_renamed
#print axioms native_sat_iff_of_renamed
#print axioms native_weakBisimilar_of_renamed
#print axioms native_branchingBisimilar_of_renamed
#print axioms native_hpBisimilar_of_renamed

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface
