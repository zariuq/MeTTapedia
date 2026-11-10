import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.NativeUpToDeadInterface
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.NativeIteratedControls

/-!
# Native transport up to dead names

## The live step

**The live step** (`live`) is the native step on its live fragment: its firings are live firings, and
its admission, results, settlement and knowledge are the native step's for the firing's native data.
A labelled move of the live step under a program is a move of the native step under the program's
live offers (`moves_live_iff`), so bisimilarity of the two is one relation (`bisimilar_live_iff`).

## Transport up to dead names

**The native transport up to dead names** (`deadTransport`): inclusions are dead-name extensions
(`NativeDead.DeadExtension`), composed and amalgamated by pushout; a live firing is carried by carrying
its rule, outputs and query patterns (`NativeDead.Inclusion.firing`), and carrying composes
(`Inclusion.firing_comp`). Its agreement is agreement up to dead names (`same_iff`); its invariant
programs are the programs that do not see dead names (`invariant_iff`). So:

* **Agreeing states are bisimilar** (`bisimilar_of_deadEquiv'`): R85's theorem, as an instance of the
  interface's.
* **Residuals** (`residuals`) are the native residuals after a step (`residualAfter`).
* **Independence up to dead names holds for every clear pair** (`independent_of_clears`), with the
  makers of `Step/NativeResidualExample` as a concrete pair (`makers_independent`).
* **Independence is carried along dead-name extensions** (`independent_along`), through the cores of
  the two steps (`span_admits`, `span_results`).
* **Concurrent words carry along dead-name extensions** (`carriesWords`), in both directions.
* **So agreeing states are step bisimilar** (`stepBisimilar_of_deadEquiv`), for every program that
  does not see dead names: the interface's multi-firing steps up to dead names.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open NativeResidual NativeDead NativeIterated

variable {S : Signature} {O : Type} [DecidableEq O] {Γ : Ctx S} {sort : S.Srt}
  [DecidableEq S.Srt] [∀ result, DecidableEq (S.Op result)]

namespace NativeUpToDead

/-! ## The live step -/

/-- **The live step**: the native step on its live fragment. -/
noncomputable def live : Interface.Step.Standard (Frames.contextual S) O (NativeState S O Γ sort) LiveFiring where
  frame s := native.frame s
  knowledge s := native.knowledge s
  present s := native.present s
  selection f := f.selection
  target f := native.target f.toNative
  extension f := native.extension f.toNative
  information f := native.information f.toNative
  transported f e member := native.transported f.toNative e member
  Shapes f := native.Shapes f.toNative
  Holds f := native.Holds f.toNative
  Admits f := f.toNative.Realized
  admits_iff f := native.admits_iff f.toNative
  preparedResult f p := native.preparedResult f.toNative p
  present_preparedResult f p := native.present_preparedResult f.toNative p
  preparedSettle f p := native.preparedSettle f.toNative p
  knowledge_preparedResult f p := native.knowledge_preparedResult f.toNative p

variable {L : Type}

/-- **A move of the live step is a move of the native step under the program's live offers.** -/
theorem moves_live_iff (program : L → (s : NativeState S O Γ sort) → LiveFiring s → Prop)
    {s t : NativeState S O Γ sort} {ℓ : L} :
    Race.Generic.Moves live.toStep program s ℓ t ↔ Race.Generic.Moves native.toStep (liveOffers program) s ℓ t := by
  constructor
  · rintro ⟨f, admitted, offered, rfl⟩
    exact ⟨f.toNative, admitted, ⟨f, offered, rfl⟩, rfl⟩
  · rintro ⟨_, admitted, ⟨f, offered, rfl⟩, rfl⟩
    exact ⟨f, admitted, offered, rfl⟩

/-- **Bisimilarity of the live step is bisimilarity of the native step under live offers.** -/
theorem bisimilar_live_iff (program : L → (s : NativeState S O Γ sort) → LiveFiring s → Prop)
    {s t : NativeState S O Γ sort} :
    Race.Generic.Bisimilar live.toStep program s t ↔ Race.Generic.Bisimilar native.toStep (liveOffers program) s t := by
  constructor
  · rintro ⟨R, ⟨forward, backward, _⟩, related⟩
    refine ⟨R, ⟨?_, ?_, fun _ _ _ atom => atom.elim⟩, related⟩
    · intro s t related ℓ s' moved
      obtain ⟨t', moved', related'⟩ := forward related ℓ ((moves_live_iff program).mpr moved)
      exact ⟨t', (moves_live_iff program).mp moved', related'⟩
    · intro s t related ℓ t' moved
      obtain ⟨s', moved', related'⟩ := backward related ℓ ((moves_live_iff program).mpr moved)
      exact ⟨s', (moves_live_iff program).mp moved', related'⟩
  · rintro ⟨R, ⟨forward, backward, _⟩, related⟩
    refine ⟨R, ⟨?_, ?_, fun _ _ _ atom => atom.elim⟩, related⟩
    · intro s t related ℓ s' moved
      obtain ⟨t', moved', related'⟩ := forward related ℓ ((moves_live_iff program).mp moved)
      exact ⟨t', (moves_live_iff program).mpr moved', related'⟩
    · intro s t related ℓ t' moved
      obtain ⟨s', moved', related'⟩ := backward related ℓ ((moves_live_iff program).mp moved)
      exact ⟨s', (moves_live_iff program).mpr moved', related'⟩

/-! ## Carrying composes -/

section Comp

variable {s u w : NativeState S O Γ sort}

omit [DecidableEq O] [DecidableEq S.Srt] [∀ result, DecidableEq (S.Op result)] in
theorem Inclusion.source_comp (e : Inclusion s u) (e' : Inclusion u w) :
    (e.comp e').source = Assignment.compose e'.source e.source := by
  unfold Inclusion.source
  rw [reindex_compose]
  exact reindex_congr (funext fun name => by cases name <;> rfl) _ _

omit [DecidableEq O] [DecidableEq S.Srt] [∀ result, DecidableEq (S.Op result)] in
theorem Inclusion.target_comp (e : Inclusion s u) (e' : Inclusion u w) :
    (e.comp e').target = Assignment.compose e'.target e.target := by
  unfold Inclusion.target
  rw [reindex_compose]
  exact reindex_congr (funext fun name => by cases name <;> rfl) _ _

omit [DecidableEq O] [DecidableEq S.Srt] [∀ result, DecidableEq (S.Op result)] in
/-- **Carrying a live firing composes.** -/
theorem Inclusion.firing_comp (e : Inclusion s u) (e' : Inclusion u w) (f : LiveFiring s) :
    (e.comp e').firing f = e'.firing (e.firing f) := by
  rw [firing_eq, firing_eq, firing_eq, carryAlong_comp, Inclusion.source_comp, Inclusion.target_comp]

end Comp

/-! ## The transport -/

/-- **The native transport up to dead names**: dead-name extensions, with live firings carried. -/
noncomputable def deadTransport : DeadTransport (live (S := S) (O := O) (Γ := Γ) (sort := sort)).toStep where
  Incl := DeadExtension
  toStateIncl e := ⟨e.frame, Frames.equivalent_of_mem_iff fun _ => e.equations.mem_iff.symm, Equiv.refl O, by
    show _ = _
    rw [Equiv.refl_toEmbedding, Finset.map_refl]
    exact e.present.symm⟩
  refl := DeadExtension.refl
  comp e e' := e.comp e'
  amalgamate tu tv := ⟨pushout _ tv, ⟨pushoutLeft _ tv⟩, ⟨pushoutRight tu tv⟩⟩
  Carries e f g := e.firing f = g
  carries_comp {_ _ _ e e' f _ _} first second := by
    show (e.toInclusion.comp e'.toInclusion).firing f = _
    rw [Inclusion.firing_comp, first, second]
  selection_carries {_ _ _ f _} carried := by
    subst carried
    exact (renameSelection_refl f.selection).symm
  admits_carries {_ _ e f _} carried := by
    subst carried
    exact e.admits_iff f
  result_carries {_ _ e f _} carried admitted admitted' := by
    subst carried
    exact DeadExtension.result_equiv e f admitted admitted'

/-- **Its agreement is agreement up to dead names.** -/
theorem same_iff {s t : NativeState S O Γ sort} : (deadTransport (S := S)).Same s t ↔ DeadEquiv s t :=
  Iff.rfl

/-- **Its invariant programs are the programs that do not see dead names.** -/
theorem invariant_iff (program : L → (s : NativeState S O Γ sort) → LiveFiring s → Prop) :
    (deadTransport (S := S)).Invariant program ↔ DeadInvariant program := by
  constructor
  · intro invariant s u e ℓ
    refine ⟨fun f offered => ?_, (invariant e ℓ).2⟩
    obtain ⟨g, carried, offeredG⟩ := (invariant e ℓ).1 f offered
    rw [← carried] at offeredG
    exact offeredG
  · intro invariant s u e ℓ
    exact ⟨fun f offered => ⟨_, rfl, (invariant e ℓ).1 f offered⟩, (invariant e ℓ).2⟩

/-- **Agreeing states are bisimilar**, for every program that does not see dead names: R85's theorem as
an instance of the interface's. -/
theorem bisimilar_of_deadEquiv' {program : L → (s : NativeState S O Γ sort) → LiveFiring s → Prop}
    (invariant : DeadInvariant program) {s t : NativeState S O Γ sort} (same : DeadEquiv s t) :
    Race.Generic.Bisimilar native.toStep (liveOffers program) s t :=
  (bisimilar_live_iff program).mp
    (DeadTransport.bisimilar_of_same ((invariant_iff program).mpr invariant) (same_iff.mpr same))

/-! ## Residuals and independence -/

/-- **The native residuals**, after a step. -/
noncomputable def residuals : (deadTransport (S := S) (O := O) (Γ := Γ) (sort := sort)).Residuals where
  Residual _ admitted f r := r = residualAfter admitted f
  selection_residual residual := by
    subst residual
    rfl

variable {s : NativeState S O Γ sort}

/-- **Every clear pair is independent up to dead names.** -/
theorem independent_of_clears {f g : LiveFiring s} (first : f.toNative.Realized) (second : g.toNative.Realized)
    (clears : Clears f g) : DeadTransport.Independent residuals f g :=
  ⟨first, second, residualAfter first g, residualAfter second f, rfl, rfl,
    LiveFiring.after second first clears.2, LiveFiring.after first second clears.1,
    (composites_deadEquiv first second clears.1 clears.2).symm⟩

/-- **The concrete makers of `Step/NativeResidualExample` are independent up to dead names.** -/
theorem makers_independent :
    DeadTransport.Independent residuals (NativeResidualExample.maker 0 none) (NativeResidualExample.maker 1 none) :=
  independent_of_clears (NativeResidualExample.maker_realized 0 none) (NativeResidualExample.maker_realized 1 none)
    (NativeIteratedControls.makers_clears 0 1 (by decide))

/-! ## Independence and concurrent words carry along dead-name extensions -/

section Along

/-- **Along a span of dead-name extensions, the two carryings of one firing are admitted together.** -/
theorem span_admits {c x y : NativeState S O Γ sort} (e₁ : DeadExtension c x) (e₂ : DeadExtension c y)
    (k : LiveFiring c) {f₁ : LiveFiring x} {f₂ : LiveFiring y} (first : e₁.firing k = f₁) (second : e₂.firing k = f₂) :
    f₁.toNative.Realized ↔ f₂.toNative.Realized := by
  subst first second
  exact (e₁.admits_iff k).symm.trans (e₂.admits_iff k)

/-- **Along a span of dead-name extensions, the two carryings of one firing have results that agree
up to dead names.** -/
theorem span_results {c x y : NativeState S O Γ sort} (e₁ : DeadExtension c x) (e₂ : DeadExtension c y)
    (k : LiveFiring c) {f₁ : LiveFiring x} {f₂ : LiveFiring y} (first : e₁.firing k = f₁) (second : e₂.firing k = f₂)
    (admitted₁ : f₁.toNative.Realized) (admitted₂ : f₂.toNative.Realized) :
    DeadEquiv (native.result f₁.toNative admitted₁) (native.result f₂.toNative admitted₂) := by
  subst first second
  have admitted := (e₁.admits_iff k).mpr admitted₁
  exact (e₁.result_equiv k admitted admitted₁).symm.trans (e₂.result_equiv k admitted admitted₂)

variable {u : NativeState S O Γ sort}

/-- The residual at the larger state is the core residual, carried along the core's span. -/
theorem residual_span (e : DeadExtension s u) {k : LiveFiring s}
    (admitted' : (e.firing k).toNative.Realized) (h : LiveFiring s) :
    ((coreCarried e k).comp (result_core (e.firing k) admitted')).firing (coreResidual k h) =
      residualAfter admitted' (e.firing h) := by
  show ((coreCarried e k).toInclusion.comp (result_core (e.firing k) admitted').toInclusion).firing _ = _
  rw [Inclusion.firing_comp]
  exact (congrArg (result_core (e.firing k) admitted').firing (coreResidual_coreCarried e k h)).trans
    (coreResidual_carried (e.firing k) admitted' (e.firing h))

/-- **A residual is admitted exactly when the residual of the carryings is.** -/
theorem residual_admits_along (e : DeadExtension s u) {k : LiveFiring s} (admitted : k.toNative.Realized)
    (admitted' : (e.firing k).toNative.Realized) (h : LiveFiring s) :
    (residualAfter admitted h).toNative.Realized ↔ (residualAfter admitted' (e.firing h)).toNative.Realized :=
  span_admits (result_core k admitted) ((coreCarried e k).comp (result_core (e.firing k) admitted'))
    (coreResidual k h) (coreResidual_carried k admitted h) (residual_span e admitted' h)

/-- **The results of a residual and of the residual of the carryings agree up to dead names.** -/
theorem residual_results_along (e : DeadExtension s u) {k : LiveFiring s} (admitted : k.toNative.Realized)
    (admitted' : (e.firing k).toNative.Realized) (h : LiveFiring s)
    (after : (residualAfter admitted h).toNative.Realized)
    (after' : (residualAfter admitted' (e.firing h)).toNative.Realized) :
    DeadEquiv (native.result (residualAfter admitted h).toNative after)
      (native.result (residualAfter admitted' (e.firing h)).toNative after') :=
  span_results (result_core k admitted) ((coreCarried e k).comp (result_core (e.firing k) admitted'))
    (coreResidual k h) (coreResidual_carried k admitted h) (residual_span e admitted' h) after after'

/-- **Independence is carried along dead-name extensions**, in both directions. -/
theorem independent_along (e : DeadExtension s u) (f g : LiveFiring s) :
    DeadTransport.Independent residuals f g ↔ DeadTransport.Independent residuals (e.firing f) (e.firing g) := by
  constructor
  · rintro ⟨first, second, _, _, rfl, rfl, afterFirst, afterSecond, same⟩
    have first' := (e.admits_iff f).mp first
    have second' := (e.admits_iff g).mp second
    have afterFirst' := (residual_admits_along e first first' g).mp afterFirst
    have afterSecond' := (residual_admits_along e second second' f).mp afterSecond
    exact ⟨first', second', _, _, rfl, rfl, afterFirst', afterSecond',
      ((residual_results_along e first first' g afterFirst afterFirst').symm.trans same).trans
        (residual_results_along e second second' f afterSecond afterSecond')⟩
  · rintro ⟨first', second', _, _, rfl, rfl, afterFirst', afterSecond', same⟩
    have first := (e.admits_iff f).mpr first'
    have second := (e.admits_iff g).mpr second'
    have afterFirst := (residual_admits_along e first first' g).mpr afterFirst'
    have afterSecond := (residual_admits_along e second second' f).mpr afterSecond'
    exact ⟨first, second, _, _, rfl, rfl, afterFirst, afterSecond,
      ((residual_results_along e first first' g afterFirst afterFirst').trans same).trans
        (residual_results_along e second second' f afterSecond afterSecond').symm⟩

omit [DecidableEq S.Srt] [∀ result, DecidableEq (S.Op result)] in
theorem forall₂_map_iff {α β : Type*} (F : α → β) :
    ∀ (l : List α) (l' : List β), List.Forall₂ (fun x y => y = F x) l l' ↔ l' = l.map F
  | [], [] => ⟨fun _ => rfl, fun _ => .nil⟩
  | [], _ :: _ => ⟨fun h => (by cases h), fun h => absurd h (List.cons_ne_nil _ _)⟩
  | _ :: _, [] => ⟨fun h => (by cases h), fun h => absurd (Eq.symm h) (List.cons_ne_nil _ _)⟩
  | x :: rest, y :: rest' => by
      rw [List.forall₂_cons, forall₂_map_iff F rest rest', List.map_cons, List.cons.injEq]

omit [DecidableEq S.Srt] [∀ result, DecidableEq (S.Op result)] in
theorem forall₂_eq_map_iff {α β : Type*} (F : α → β) (l : List α) (l' : List β) :
    List.Forall₂ (fun x y => F x = y) l l' ↔ l' = l.map F := by
  rw [← forall₂_map_iff F]
  exact ⟨List.Forall₂.imp fun _ _ same => same.symm, List.Forall₂.imp fun _ _ same => same.symm⟩

/-- A concurrent word of the live step, unfolded at its first firing. -/
theorem concurrent_cons_iff {k : LiveFiring s} {rest : List (LiveFiring s)} {t : NativeState S O Γ sort} :
    DeadTransport.Concurrent residuals s (k :: rest) t ↔ ∃ admitted : k.toNative.Realized,
      (∀ g ∈ rest, DeadTransport.Independent residuals k g) ∧
        DeadTransport.Concurrent residuals (native.result k.toNative admitted) (rest.map (residualAfter admitted)) t := by
  constructor
  · intro concurrent
    cases concurrent with
    | cons _ _ admitted residualList residual independent later =>
        have same := (forall₂_map_iff (residualAfter admitted) rest residualList).mp residual
        subst same
        exact ⟨admitted, independent, later⟩
  · rintro ⟨admitted, independent, later⟩
    exact .cons k rest admitted _ ((forall₂_map_iff (residualAfter admitted) rest _).mpr rfl) independent later

/-- **Concurrent words move along dead-name extensions**, in both directions, with final states that
agree up to dead names. -/
theorem concurrent_along : ∀ (n : ℕ) {s u : NativeState S O Γ sort} (e : DeadExtension s u)
    (l : List (LiveFiring s)), l.length = n →
    (∀ {t : NativeState S O Γ sort}, DeadTransport.Concurrent residuals s l t →
        ∃ t', DeadTransport.Concurrent residuals u (l.map e.firing) t' ∧ DeadEquiv t t') ∧
      ∀ {t' : NativeState S O Γ sort}, DeadTransport.Concurrent residuals u (l.map e.firing) t' →
        ∃ t, DeadTransport.Concurrent residuals s l t ∧ DeadEquiv t t'
  | _, s, u, e, [], _ =>
      ⟨fun {t} run => by
        cases run
        exact ⟨u, .nil u, DeadEquiv.of_extension e⟩,
        fun {t'} run => by
          cases run
          exact ⟨s, .nil s, DeadEquiv.of_extension e⟩⟩
  | 0, _, _, _, _ :: _, length => absurd length (by simp)
  | n + 1, s, u, e, k :: rest, length => by
      have short : rest.length = n := Nat.succ.inj length
      have lengthCore : (rest.map (coreResidual k)).length = n := by rw [List.length_map]; exact short
      have lengthCarried : ((rest.map (coreResidual k)).map (coreCarried e k).firing).length = n := by
        rw [List.length_map, List.length_map]; exact short
      have here : ∀ admitted : k.toNative.Realized,
          rest.map (residualAfter admitted) = (rest.map (coreResidual k)).map (result_core k admitted).firing := by
        intro admitted
        rw [List.map_map]
        exact List.map_congr_left fun h _ => (coreResidual_carried k admitted h).symm
      have there : ∀ admitted : (e.firing k).toNative.Realized,
          (rest.map e.firing).map (residualAfter admitted) =
            ((rest.map (coreResidual k)).map (coreCarried e k).firing).map
              (result_core (e.firing k) admitted).firing := by
        intro admitted
        rw [List.map_map, List.map_map, List.map_map]
        refine List.map_congr_left fun h _ => ?_
        show residualAfter admitted (e.firing h) =
          (result_core (e.firing k) admitted).firing ((coreCarried e k).firing (coreResidual k h))
        rw [coreResidual_coreCarried, coreResidual_carried]
      refine ⟨fun {t} run => ?_, fun {t'} run => ?_⟩
      · obtain ⟨admitted, independent, later⟩ := concurrent_cons_iff.mp run
        have admitted' := (e.admits_iff k).mp admitted
        rw [here admitted] at later
        obtain ⟨t₀, atCore, first⟩ := (concurrent_along n (result_core k admitted) _ lengthCore).2 later
        obtain ⟨t₁, atCarried, second⟩ := (concurrent_along n (coreCarried e k) _ lengthCore).1 atCore
        obtain ⟨t', atResult, third⟩ :=
          (concurrent_along n (result_core (e.firing k) admitted') _ lengthCarried).1 atCarried
        rw [← there admitted'] at atResult
        refine ⟨t', concurrent_cons_iff.mpr ⟨admitted', fun g' member => ?_, atResult⟩,
          first.symm.trans (second.trans third)⟩
        obtain ⟨g, inRest, rfl⟩ := List.mem_map.mp member
        exact (independent_along e k g).mp (independent g inRest)
      · obtain ⟨admitted', independent, later⟩ := concurrent_cons_iff.mp run
        have admitted := (e.admits_iff k).mpr admitted'
        rw [there admitted'] at later
        obtain ⟨t₁, atCarried, third⟩ :=
          (concurrent_along n (result_core (e.firing k) admitted') _ lengthCarried).2 later
        obtain ⟨t₀, atCore, second⟩ := (concurrent_along n (coreCarried e k) _ lengthCore).2 atCarried
        obtain ⟨t, atResult, first⟩ := (concurrent_along n (result_core k admitted) _ lengthCore).1 atCore
        rw [← here admitted] at atResult
        refine ⟨t, concurrent_cons_iff.mpr ⟨admitted, fun g inRest => ?_, atResult⟩,
          first.symm.trans (second.trans third)⟩
        exact (independent_along e k g).mpr (independent (e.firing g) (List.mem_map_of_mem inRest))

/-- **Concurrent words carry along dead-name extensions**: the law of the interface. -/
theorem carriesWords : DeadTransport.CarriesWords (residuals (S := S) (O := O) (Γ := Γ) (sort := sort)) := by
  intro s u e fs gs carried
  have same : gs = fs.map e.firing := (forall₂_eq_map_iff e.firing fs gs).mp carried
  subst same
  exact concurrent_along _ e fs rfl

/-- **Agreeing states are step bisimilar**, for every program that does not see dead names: the
interface's multi-firing steps up to dead names, on the native step's live fragment. -/
theorem stepBisimilar_of_deadEquiv {program : L → (s : NativeState S O Γ sort) → LiveFiring s → Prop}
    (invariant : DeadInvariant program) {s t : NativeState S O Γ sort} (same : DeadEquiv s t) :
    DeadTransport.StepBisimilar residuals program s t :=
  DeadTransport.stepBisimilar_of_same ((invariant_iff program).mpr invariant) carriesWords (same_iff.mpr same)

/-- **The two composites of a clear diamond are step bisimilar**, for every closed program. -/
theorem makers_composites_stepBisimilar {L : Type}
    (program : L → ClosedFiring NativeResidualExample.tiny ℕ ([] : Ctx NativeResidualExample.tiny) () → Prop) :
    DeadTransport.StepBisimilar residuals (closedOffers program)
      (native.result (LiveFiring.residual (NativeResidualExample.maker_realized 1 none) (NativeResidualExample.maker 0 none))
        (LiveFiring.after (NativeResidualExample.maker_realized 0 none) (NativeResidualExample.maker_realized 1 none)
          (NativeResidualExample.clear_makers 0 1 (by decide))))
      (native.result (LiveFiring.residual (NativeResidualExample.maker_realized 0 none) (NativeResidualExample.maker 1 none))
        (LiveFiring.after (NativeResidualExample.maker_realized 1 none) (NativeResidualExample.maker_realized 0 none)
          (NativeResidualExample.clear_makers 1 0 (by decide)))) :=
  stepBisimilar_of_deadEquiv (closedOffers_invariant program)
    (composites_deadEquiv (NativeResidualExample.maker_realized 0 none) (NativeResidualExample.maker_realized 1 none)
      (NativeResidualExample.clear_makers 0 1 (by decide)) (NativeResidualExample.clear_makers 1 0 (by decide)))

end Along

end NativeUpToDead

#print axioms NativeUpToDead.moves_live_iff
#print axioms NativeUpToDead.bisimilar_live_iff
#print axioms NativeUpToDead.Inclusion.firing_comp
#print axioms NativeUpToDead.deadTransport
#print axioms NativeUpToDead.invariant_iff
#print axioms NativeUpToDead.bisimilar_of_deadEquiv'
#print axioms NativeUpToDead.independent_of_clears
#print axioms NativeUpToDead.makers_independent
#print axioms NativeUpToDead.independent_along
#print axioms NativeUpToDead.concurrent_along
#print axioms NativeUpToDead.carriesWords
#print axioms NativeUpToDead.stepBisimilar_of_deadEquiv
#print axioms NativeUpToDead.makers_composites_stepBisimilar

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface
