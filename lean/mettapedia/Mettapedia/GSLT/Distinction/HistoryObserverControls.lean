import Mettapedia.GSLT.Distinction.HistoryObserver

/-!
# Controls for the history observer

* **No stabilization stage** (`not_stabilizes_of_faithful`,
  `forward_not_stabilizes`).  A faithful observer whose depth-`n` approximants
  relate two different terms at every depth has no stabilization certificate.
  On the one-node grammar the configurations are sizes; sizes `n + 2` and
  `n + 3` agree to depth `n` (`SizeDetermined.approx`), and erasures separate
  them, so for every positive scale and every result and fault reading (with
  zero potential) no depth stabilizes.  The stabilized readout classes of
  `GradedValueNativeDescent` are therefore not available for the whole
  history grammar; the finite-depth classes still retain every reading
  (`HistoryObserver.value_eq_of_stateOf_eq`).
* **Unbounded pasts** (`erase_pasts_unbounded`, `merge_pasts_unbounded`,
  `evolve_pasts_unbounded`, `kindSystem_not_predecessorFiniteModulo`).  With
  kind labels over `ℕ`, erasing any node of `{n}` reaches `0`, merging `0` with
  any `n` reaches `{0}` when the merge keeps its left node, and evolving any
  `n` reaches `{0}` when evolution is constant.  Fork pasts stay inside the
  configuration (`fork_pasts_bounded`).
* **Kind labels do not separate configurations** (`kind_bisimilar_not_eq`).
  Firing commutes with node renamings that respect the grammar
  (`fires_map`); swapping the two nodes of `swapGrammar` relates `{true}` and
  `{false}` in the kind-labelled system, which the event-labelled system
  separates.
* **A match cannot choose the same causal occurrence** (`eraseCopy`,
  `no_matcher_recovers_occurrences`, `matching_relates_distinct`).  Erasing
  the first or the second copy of `x` in `{x, x}` are two causal occurrences
  with one event and the same endpoints.  Matching by event and endpoints
  satisfies all four occurrence laws and keeps every event, so it preserves
  and reflects every labelled tense formula; it still relates the two
  occurrences, and no choice of occurrence from labelled steps returns both.
* **The cost meter saturates** (`cost_saturates`): outside `[0, one]` the cost
  reading is not the potential.
* **Faults are read** (`interleavings_read`): the observer reads `0` on the
  history that erases the only copy and then copies it, and a positive value
  on the other order.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Distinction.HistoryObserverControls

open Mettapedia.GSLT
open Mettapedia.GSLT.HennessyMilner
open Mettapedia.GSLT.Distinction.HistoryGrammar
open Mettapedia.GSLT.Distinction.HistoryObserver
open Mettapedia.GSLT.Distinction.Constructive
open Mettapedia.Cybernetics.DistinctionCalculus.History

/-! ## A faithful observer that never stabilizes -/

section Faithful

universe uS uAtom uLabel uObs uV

variable {W : Type uV} [AddCommGroup W] [LinearOrder W] [IsOrderedAddMonoid W]
variable {S : GSLT.{uS}} {K : Scale W}

/-- **A faithful observer whose approximants never close up has no
stabilization stage.** -/
theorem not_stabilizes_of_faithful (Q : PresentedSystem.{uS, uAtom, uLabel, uObs} S K)
    (vocabulary : Q.Vocabulary) (positive : K.Positive)
    (faithful : ∀ left right, Q.GradedBisimilar left right → S.Equiv left right)
    (separated : ∀ depth, ∃ left right, ¬ S.Equiv left right ∧ Q.Approx depth left right)
    (depth : Nat) : ¬ Q.Stabilizes vocabulary depth := by
  intro stable
  obtain ⟨left, right, distinct, approx⟩ := separated depth
  exact distinct (faithful left right
    ((Q.gradedBisimilar_iff_of_stabilizes vocabulary positive stable left right).2.mpr
      (Q.depthBound_eq_zero_of_approx vocabulary approx)))

end Faithful

/-! ## The one-node grammar -/

/-- The history grammar on a single node. -/
def unitGrammar : Grammar Unit := ⟨fun _ => (), fun _ _ => ()⟩

/-- A configuration of the one-node grammar is its size. -/
theorem unit_eq_replicate (live : Multiset Unit) :
    live = Multiset.replicate (Multiset.card live) () :=
  Multiset.eq_replicate_card.mpr fun _ _ => rfl

theorem unit_eq_of_card_eq {left right : Multiset Unit}
    (same : Multiset.card left = Multiset.card right) : left = right := by
  rw [unit_eq_replicate left, unit_eq_replicate right, same]

theorem unit_mem_iff (live : Multiset Unit) : () ∈ live ↔ 1 ≤ Multiset.card live := by
  rw [Nat.one_le_iff_ne_zero, ← Nat.pos_iff_ne_zero, Multiset.card_pos_iff_exists_mem]
  exact ⟨fun member => ⟨(), member⟩, fun ⟨_, member⟩ => member⟩

theorem unit_count (live : Multiset Unit) : live.count () = Multiset.card live :=
  Multiset.count_eq_card.mpr fun _ _ => rfl

theorem unit_pair_size : Multiset.card (pair () ()) = 2 := by simp [pair]

theorem unit_pair_le_iff (live : Multiset Unit) : pair () () ≤ live ↔ 2 ≤ Multiset.card live := by
  rw [Multiset.le_iff_count]
  constructor
  · intro le
    have := le ()
    rwa [unit_count, unit_count, unit_pair_size] at this
  · intro le unitValue
    cases unitValue
    rwa [unit_count, unit_count, unit_pair_size]

/-- What an event needs on the one-node grammar, as a size. -/
def need : Event Unit → Nat
  | .evolve _ => 1
  | .fork _ => 1
  | .merge _ _ => 2
  | .erase _ => 1

/-- The size an event reaches. -/
def shift : Event Unit → Nat → Nat
  | .evolve _, size => size
  | .fork _, size => size + 1
  | .merge _ _, size => size - 1
  | .erase _, size => size - 1

/-- **On one node an event is determined by sizes.** -/
theorem unit_fires_iff (event : Event Unit) (source target : Multiset Unit) :
    Fires unitGrammar event source target ↔
      need event ≤ Multiset.card source ∧ Multiset.card target = shift event (Multiset.card source) := by
  constructor
  · intro fires
    cases fires with
    | evolve member =>
        have size := Multiset.card_erase_of_mem member
        have enabled := (unit_mem_iff _).mp member
        refine ⟨enabled, ?_⟩
        simp only [Multiset.card_cons, size, shift, Nat.pred_eq_sub_one]
        omega
    | fork member =>
        exact ⟨(unit_mem_iff _).mp member, by simp [shift]⟩
    | @merge x y _ enabled =>
        cases x
        cases y
        have size := Multiset.card_sub enabled
        have twice := (unit_pair_le_iff _).mp enabled
        refine ⟨twice, ?_⟩
        rw [Multiset.card_cons, size, unit_pair_size]
        simp only [shift]
        omega
    | erase member =>
        have size := Multiset.card_erase_of_mem member
        exact ⟨(unit_mem_iff _).mp member, by simp only [size, shift, Nat.pred_eq_sub_one]⟩
  · rintro ⟨enabled, size⟩
    cases event with
    | evolve x =>
        cases x
        simp only [need, shift] at enabled size
        have member := (unit_mem_iff source).mpr enabled
        have fires := Fires.evolve (G := unitGrammar) member
        have erased := Multiset.card_erase_of_mem member
        rwa [unit_eq_of_card_eq (left := unitGrammar.evolve () ::ₘ source.erase ()) (right := target)
          (by simp only [Multiset.card_cons, erased, size, Nat.pred_eq_sub_one]; omega)] at fires
    | fork x =>
        cases x
        simp only [need, shift] at enabled size
        have member := (unit_mem_iff source).mpr enabled
        have fires := Fires.fork (G := unitGrammar) member
        rwa [unit_eq_of_card_eq (left := () ::ₘ source) (right := target)
          (by simp only [Multiset.card_cons, size])] at fires
    | merge x y =>
        cases x
        cases y
        simp only [need, shift] at enabled size
        have le := (unit_pair_le_iff source).mpr enabled
        have fires := Fires.merge (G := unitGrammar) le
        have subtracted := Multiset.card_sub le
        rwa [unit_eq_of_card_eq (left := unitGrammar.merge () () ::ₘ (source - pair () ())) (right := target)
          (by rw [Multiset.card_cons, subtracted, size, unit_pair_size]; omega)] at fires
    | erase x =>
        cases x
        simp only [need, shift] at enabled size
        have member := (unit_mem_iff source).mpr enabled
        have fires := Fires.erase (G := unitGrammar) member
        have erased := Multiset.card_erase_of_mem member
        rwa [unit_eq_of_card_eq (left := source.erase ()) (right := target)
          (by simp only [erased, size, Nat.pred_eq_sub_one])] at fires

/-! ## Size-determined systems on one node -/

section SizeDetermined

variable {W : Type} [AddCommGroup W] [LinearOrder W] [IsOrderedAddMonoid W] {K : Scale W}

/-- A presented system on the one-node grammar whose steps are determined by
sizes, moving one size at a time and needing at most two copies, and whose
readings agree on nonempty configurations. -/
structure SizeDetermined (Q : PresentedSystem (historyGSLT unitGrammar) K) where
  need : Q.dynamics.Label → Nat
  shift : Q.dynamics.Label → Nat → Nat
  need_le : ∀ label, need label ≤ 2
  shift_ge : ∀ label size, size ≤ shift label size + 1
  act_iff : ∀ label source target, Q.dynamics.act label source target ↔
    need label ≤ Multiset.card source ∧ Multiset.card target = shift label (Multiset.card source)
  value_agree : ∀ observation (left right : Multiset Unit), 1 ≤ Multiset.card left →
    1 ≤ Multiset.card right → Q.value observation left = Q.value observation right

namespace SizeDetermined

variable {Q : PresentedSystem (historyGSLT unitGrammar) K}

/-- **Large configurations agree to any depth below their size.** -/
theorem approx (sized : SizeDetermined Q) : ∀ (depth : Nat) (left right : Multiset Unit),
    depth + 2 ≤ Multiset.card left → depth + 2 ≤ Multiset.card right → Q.Approx depth left right
  | 0, left, right, leftSize, rightSize => by
      simp only [PresentedSystem.Approx]
      exact fun observation => sized.value_agree observation left right (by omega) (by omega)
  | depth + 1, left, right, leftSize, rightSize => by
      simp only [PresentedSystem.Approx]
      refine ⟨fun observation => sized.value_agree observation left right (by omega) (by omega),
        ?_, ?_⟩
      · intro label left' action
        obtain ⟨_, size⟩ := (sized.act_iff label left left').mp action
        have needed := sized.need_le label
        have lower := sized.shift_ge label (Multiset.card left)
        have lower' := sized.shift_ge label (Multiset.card right)
        refine ⟨Multiset.replicate (sized.shift label (Multiset.card right)) (),
          (sized.act_iff label right _).mpr ⟨by omega, by simp⟩, ?_⟩
        exact approx sized depth _ _ (by omega) (by simp; omega)
      · intro label right' action
        obtain ⟨_, size⟩ := (sized.act_iff label right right').mp action
        have needed := sized.need_le label
        have lower := sized.shift_ge label (Multiset.card left)
        have lower' := sized.shift_ge label (Multiset.card right)
        refine ⟨Multiset.replicate (sized.shift label (Multiset.card left)) (),
          (sized.act_iff label left _).mpr ⟨by omega, by simp⟩, ?_⟩
        exact approx sized depth _ _ (by simp; omega) (by omega)

/-- At every depth two different sizes agree. -/
theorem separated (sized : SizeDetermined Q) (depth : Nat) :
    ∃ left right : Multiset Unit, ¬ (historyGSLT unitGrammar).Equiv left right ∧
      Q.Approx depth left right := by
  refine ⟨Multiset.replicate (depth + 2) (), Multiset.replicate (depth + 3) (), ?_,
    sized.approx depth _ _ (by simp) (by simp)⟩
  intro same
  have sizes := congrArg Multiset.card (show Multiset.replicate (depth + 2) () =
    Multiset.replicate (depth + 3) () from same)
  simp at sizes

end SizeDetermined

/-- The readings of a nonempty one-node configuration, with zero potential,
do not depend on its size. -/
theorem reading_agree (R : NodeReadings K Unit) (zero : ∀ node, R.potential node = 0)
    (observation : Reading) (left right : Multiset Unit) (leftSize : 1 ≤ Multiset.card left)
    (rightSize : 1 ≤ Multiset.card right) :
    reading K R observation left = reading K R observation right := by
  have nonempty : ∀ live : Multiset Unit, 1 ≤ Multiset.card live →
      live = Multiset.replicate (Multiset.card live - 1 + 1) () := by
    intro live size
    rw [Nat.sub_add_cancel size]
    exact unit_eq_replicate live
  have potentialZero : ∀ live : Multiset Unit, potentialSum R.potential live = 0 := by
    intro live
    simp [potentialSum, zero]
  cases observation with
  | result =>
      change best R.result left = best R.result right
      rw [nonempty left leftSize, nonempty right rightSize,
        best_replicate_succ _ _ (R.result_nonneg ()), best_replicate_succ _ _ (R.result_nonneg ())]
  | fault =>
      change best (faultIndicator K R) left = best (faultIndicator K R) right
      rw [nonempty left leftSize, nonempty right rightSize,
        best_replicate_succ _ _ (faultIndicator_nonneg R ()),
        best_replicate_succ _ _ (faultIndicator_nonneg R ())]
  | cost =>
      change K.clamp (potentialSum R.potential left) = K.clamp (potentialSum R.potential right)
      rw [potentialZero, potentialZero]

/-- The forward history observer on one node is size-determined. -/
def forwardSized (R : NodeReadings K Unit) (zero : ∀ node, R.potential node = 0) :
    SizeDetermined (presented unitGrammar K R) where
  need := need
  shift := shift
  need_le event := by cases event <;> simp [need]
  shift_ge event size := by cases event <;> simp only [shift] <;> omega
  act_iff := unit_fires_iff
  value_agree := reading_agree R zero

/-- The one-node listing. -/
def unitListing : Listing Unit := ⟨[()], fun _ => List.mem_singleton_self _⟩

/-- **No stabilization stage for the history observer**: for every positive
scale and every result and fault reading with zero potential, the one-node
history observer has no stabilization certificate at any depth. -/
theorem forward_not_stabilizes (positive : K.Positive) (R : NodeReadings K Unit)
    (zero : ∀ node, R.potential node = 0) (depth : Nat) :
    ¬ (presented unitGrammar K R).Stabilizes (vocabulary unitGrammar K R unitListing) depth :=
  not_stabilizes_of_faithful _ _ positive
    (fun left right => (gradedBisimilar_iff_eq unitGrammar K R left right).mp)
    (forwardSized R zero).separated depth

end SizeDetermined

/-! ## Unbounded pasts of kind labels -/

/-- Evolution to `0` and a merge that keeps its left node. -/
def pastGrammar : Grammar ℕ := ⟨fun _ => 0, fun x _ => x⟩

/-- No finite set covers the pasts of `target` under `kind`. -/
def PastsUnbounded (kind : EventKind) (target : Multiset ℕ) : Prop :=
  ¬ ∃ representatives : Set (Multiset ℕ), representatives.Finite ∧
    ∀ ⦃source⦄, (kindSystem pastGrammar).act kind source target →
      ∃ representative ∈ representatives, (historyGSLT pastGrammar).Equiv source representative

theorem pastsUnbounded_of_injective {kind : EventKind} {target : Multiset ℕ}
    (family : ℕ → Multiset ℕ) (injective : Function.Injective family)
    (acts : ∀ index, (kindSystem pastGrammar).act kind (family index) target) :
    PastsUnbounded kind target := by
  rintro ⟨representatives, finite, cover⟩
  refine Set.infinite_of_injective_forall_mem injective (fun index => ?_) finite
  obtain ⟨representative, member, same⟩ := cover (acts index)
  change family index = representative at same
  rw [same]
  exact member

/-- **Erase pasts are unbounded**: erasing `n` from `{n}` reaches `0`, for every
`n`. -/
theorem erase_pasts_unbounded : PastsUnbounded .erase 0 :=
  pastsUnbounded_of_injective (fun index => {index}) (fun _ _ same => Multiset.singleton_inj.mp same)
    fun index => ⟨.erase index, rfl, by
      have fires := Fires.erase (G := pastGrammar) (Multiset.mem_singleton_self index)
      rwa [Multiset.erase_singleton] at fires⟩

/-- **Merge pasts are unbounded**: merging `0` with any `n` reaches `{0}` when
the merge keeps its left node. -/
theorem merge_pasts_unbounded : PastsUnbounded .merge {0} :=
  pastsUnbounded_of_injective (fun index => pair 0 index)
    (fun _ _ same => Multiset.singleton_inj.mp ((Multiset.cons_inj_right 0).mp same))
    fun index => ⟨.merge 0 index, rfl, by
      have fires := Fires.merge (G := pastGrammar) (le_refl (pair 0 index))
      rwa [pair_sub_pair] at fires⟩

/-- **Evolve pasts are unbounded**: evolving any `n` reaches `{0}` when
evolution is constant. -/
theorem evolve_pasts_unbounded : PastsUnbounded .evolve {0} :=
  pastsUnbounded_of_injective (fun index => {index}) (fun _ _ same => Multiset.singleton_inj.mp same)
    fun index => ⟨.evolve index, rfl, by
      have fires := Fires.evolve (G := pastGrammar) (Multiset.mem_singleton_self index)
      rwa [Multiset.erase_singleton] at fires⟩

/-- Unbounded pasts at one label refute predecessor finiteness. -/
theorem not_predecessorFiniteModulo_of_unbounded {kind : EventKind} {target : Multiset ℕ}
    (unbounded : PastsUnbounded kind target) :
    ¬ SpanTransport.PredecessorFiniteModulo (kindSystem pastGrammar) :=
  fun finite => unbounded (finite kind target)

/-- **Over `ℕ` no grammar has finitely branching kind-labelled pasts.** -/
theorem kindSystem_not_predecessorFiniteModulo (G : Grammar ℕ) :
    ¬ SpanTransport.PredecessorFiniteModulo (kindSystem G) :=
  fun finite => Set.infinite_univ ((kindSystem_predecessorFiniteModulo_iff G).mp finite)

/-- **Fork pasts stay inside the configuration**: a fork's past erases one live
copy. -/
theorem fork_pasts_bounded {V : Type} [DecidableEq V] (G : Grammar V) {source target : Multiset V}
    (action : (kindSystem G).act .fork source target) : ∃ x ∈ target, source = target.erase x := by
  obtain ⟨event, kind, fires⟩ := action
  cases fires with
  | evolve _ => cases kind
  | merge _ => cases kind
  | erase _ => cases kind
  | @fork x _ _ => exact ⟨x, Multiset.mem_cons_self x source, (Multiset.erase_cons_head x source).symm⟩

/-! ## Kind labels do not separate configurations -/

section Relabel

variable {V : Type} [DecidableEq V] (G : Grammar V)

/-- Rename the nodes of an event. -/
def relabel (f : V → V) : Event V → Event V
  | .evolve x => .evolve (f x)
  | .fork x => .fork (f x)
  | .merge x y => .merge (f x) (f y)
  | .erase x => .erase (f x)

omit [DecidableEq V] in
theorem kindOf_relabel (f : V → V) (event : Event V) : kindOf (relabel f event) = kindOf event := by
  cases event <;> rfl

/-- **Firing is equivariant** under an injective renaming of nodes that commutes
with evolution and merge. -/
theorem fires_map (f : V → V) (injective : Function.Injective f)
    (evolveComm : ∀ x, f (G.evolve x) = G.evolve (f x))
    (mergeComm : ∀ x y, f (G.merge x y) = G.merge (f x) (f y))
    {event : Event V} {source target : Multiset V} (fires : Fires G event source target) :
    Fires G (relabel f event) (source.map f) (target.map f) := by
  cases fires with
  | @evolve x _ member =>
      have mapped := Fires.evolve (G := G) (Multiset.mem_map_of_mem f member)
      rwa [← evolveComm, ← Multiset.map_erase f injective, ← Multiset.map_cons] at mapped
  | @fork x _ member =>
      have mapped := Fires.fork (G := G) (Multiset.mem_map_of_mem f member)
      rwa [← Multiset.map_cons] at mapped
  | @merge x y _ enabled =>
      have le : pair (f x) (f y) ≤ source.map f := by
        have := Multiset.map_le_map (f := f) enabled
        simpa [pair] using this
      have mapped := Fires.merge (G := G) le
      have difference : source.map f - pair (f x) (f y) = (source - pair x y).map f := by
        conv_lhs => rw [← add_tsub_cancel_of_le enabled]
        rw [Multiset.map_add, show (pair x y).map f = pair (f x) (f y) by simp [pair],
          add_tsub_cancel_left]
      rwa [difference, ← mergeComm, ← Multiset.map_cons] at mapped
  | @erase x _ member =>
      have mapped := Fires.erase (G := G) (Multiset.mem_map_of_mem f member)
      rwa [← Multiset.map_erase f injective] at mapped

/-- A grammar on two nodes whose node swap is an automorphism. -/
def swapGrammar : Grammar Bool := ⟨id, fun x _ => x⟩

/-- The node swap relates configurations with the same kind-labelled
behaviour. -/
theorem swap_isBisimulation :
    (kindSystem swapGrammar).IsBisimulation fun left right => right = left.map not := by
  have involutive : ∀ live : Multiset Bool, (live.map not).map not = live := by
    intro live
    rw [Multiset.map_map]
    conv_rhs => rw [← Multiset.map_id' live]
    congr 1
    funext b
    cases b <;> rfl
  have mapFires := fun {event : Event Bool} {source target : Multiset Bool}
      (fires : Fires swapGrammar event source target) =>
    fires_map swapGrammar not (fun a b same => by cases a <;> cases b <;> simp_all)
      (fun x => rfl) (fun x y => rfl) fires
  refine ⟨?_, ?_, fun _ _ _ atom => atom.elim⟩
  · rintro left right rfl kind left' ⟨event, kind, fires⟩
    exact ⟨left'.map not, ⟨relabel not event, (kindOf_relabel not event).trans kind, mapFires fires⟩,
      rfl⟩
  · rintro left right rfl kind right' ⟨event, kind, fires⟩
    refine ⟨right'.map not, ⟨relabel not event, (kindOf_relabel not event).trans kind, ?_⟩,
      (involutive right').symm⟩
    have mapped := mapFires fires
    rwa [involutive] at mapped

/-- **Kind labels identify different configurations**: `{true}` and `{false}`
are bisimilar for the kind-labelled system, while the event-labelled system
separates every two configurations (`HistoryObserver.eventSystem_bisimilar_iff_eq`). -/
theorem kind_bisimilar_not_eq :
    (kindSystem swapGrammar).Bisimilar {true} {false} ∧
      ¬ (eventSystem swapGrammar).Bisimilar {true} {false} :=
  ⟨⟨_, swap_isBisimulation, rfl⟩, fun bisimilar =>
    absurd ((eventSystem_bisimilar_iff_eq swapGrammar _ _).mp bisimilar)
      (fun same => Bool.noConfusion (Multiset.singleton_inj.mp same))⟩

end Relabel

/-! ## A match cannot choose the same causal occurrence -/

section Copies

variable {V : Type} [DecidableEq V] (G : Grammar V)

/-- Erasing one of the two copies of `x` in `{x, x}`. -/
def eraseCopy (x : V) (copy : Fin 2) : CausalOccurrence G where
  event := .erase x
  source := pair x x
  target := (pair x x).erase x
  fires := .erase (by simp [pair])
  copy := ⟨copy, by simpa [pair, principal] using copy.isLt⟩

/-- The two copies are different causal occurrences. -/
theorem eraseCopy_ne (x : V) : eraseCopy G x 0 ≠ eraseCopy G x 1 := by
  intro same
  have copies := congrArg (fun occurrence : CausalOccurrence G => (occurrence.copy : Nat)) same
  simp [eraseCopy] at copies

/-- They have one labelled step. -/
theorem eraseCopy_step (x : V) : (eraseCopy G x 0).step = (eraseCopy G x 1).step := rfl

/-- **Labelled steps do not determine causal occurrences.** -/
theorem step_not_injective (x : V) : ¬ Function.Injective (CausalOccurrence.step (G := G)) :=
  fun injective => eraseCopy_ne G x (injective (eraseCopy_step G x))

/-- **No matcher from labelled steps returns the same causal occurrence**:
every choice of an occurrence for each labelled step misses one copy. -/
theorem no_matcher_recovers_occurrences (x : V) (pick : LabelledStep G → CausalOccurrence G) :
    ¬ ∀ occurrence, pick occurrence.step = occurrence := by
  intro recovers
  have first := recovers (eraseCopy G x 0)
  have second := recovers (eraseCopy G x 1)
  rw [eraseCopy_step] at first
  exact eraseCopy_ne G x (first.symm.trans second)

/-- **Matching by event and endpoints**, as a phase or bisimulation match does. -/
def matching : SpanTransport.SpanRelation (causalSpan G) (causalSpan G) where
  states := Eq
  events first second := first.step = second.step
  source_rel _ _ same := congrArg (fun step : LabelledStep G => step.1.2.1) same
  target_rel _ _ same := congrArg (fun step : LabelledStep G => step.1.2.2) same

theorem matching_keeps_event :
    (matching G).Keeps CausalOccurrence.event CausalOccurrence.event :=
  fun _ _ same => congrArg (fun step : LabelledStep G => step.1.1) same

theorem matching_sourceForthOcc : (matching G).SourceForthOcc :=
  fun _ _ same occurrence sourceEq => ⟨occurrence, sourceEq.trans same, rfl⟩

theorem matching_sourceBackOcc : (matching G).SourceBackOcc :=
  fun _ _ same occurrence sourceEq => ⟨occurrence, sourceEq.trans same.symm, rfl⟩

theorem matching_targetForthOcc : (matching G).TargetForthOcc :=
  fun _ _ same occurrence targetEq => ⟨occurrence, targetEq.trans same, rfl⟩

theorem matching_targetBackOcc : (matching G).TargetBackOcc :=
  fun _ _ same occurrence targetEq => ⟨occurrence, targetEq.trans same.symm, rfl⟩

/-- **The match relates two different causal occurrences**, although it
satisfies all four occurrence laws and keeps every event. -/
theorem matching_relates_distinct (x : V) :
    (matching G).events (eraseCopy G x 0) (eraseCopy G x 1) ∧ eraseCopy G x 0 ≠ eraseCopy G x 1 :=
  ⟨eraseCopy_step G x, eraseCopy_ne G x⟩

/-- Causal occurrences read by their events, with atomic observations of
configurations. -/
def causalLabelled {Atom : Type} (observes : Atom → Multiset V → Prop) :
    SpanTransport.Labelled (Multiset V) Atom (Event V) where
  span := causalSpan G
  read := CausalOccurrence.event
  observes := observes

/-- Every labelled tense formula over events agrees across the match. -/
theorem matching_sat_related {Atom : Type} (observes : Atom → Multiset V → Prop) :
    ∀ formula : SpanTransport.Tense Atom (Event V),
      SpanTransport.Related (matching G).states
        (SpanTransport.Tense.sat (causalLabelled G observes) formula)
        (SpanTransport.Tense.sat (causalLabelled G observes) formula) :=
  SpanTransport.sat_related (causalLabelled G observes) (causalLabelled G observes) (matching G)
    (matching_keeps_event G)
    (by
      intro atom left right same
      change left = right at same
      subst same
      exact Iff.rfl)
    (matching_sourceForthOcc G) (matching_sourceBackOcc G)
    (matching_targetForthOcc G) (matching_targetBackOcc G)

/-- The shared trace core does not see the copy either: the two erasures are
one enabled occurrence. -/
theorem eraseCopies_one_enabled (x : V)
    (first second : (HistoryIndependence.presentation G).Enabled (pair x x))
    (firstSite : first.site = .erase x) (secondSite : second.site = .erase x) : first = second :=
  enabled_eq_of_site_eq G first second (firstSite.trans secondSite.symm)

end Copies

/-! ## The cost meter and fault readings -/

section Meter

variable {W : Type} [AddCommGroup W] [LinearOrder W] [IsOrderedAddMonoid W] (K : Scale W)

/-- One unit of potential on the single node. -/
def unitPotential : NodeReadings K Unit where
  result _ := 0
  result_nonneg _ := le_rfl
  result_le_one _ := K.zero_le_one
  faulty _ := false
  potential _ := K.one

/-- **The cost meter saturates**: two copies have potential `one + one`, read
as `one`. -/
theorem cost_saturates :
    reading K (unitPotential K) .cost (pair () ()) = K.one ∧
      potentialSum (unitPotential K).potential (pair () ()) = K.one + K.one ∧
      K.one + K.one ≠ K.one := by
  have sum : potentialSum (unitPotential K).potential (pair () ()) = K.one + K.one := by
    simp [potentialSum, pair, unitPotential]
  refine ⟨?_, sum, ?_⟩
  · change K.clamp (potentialSum (unitPotential K).potential (pair () ())) = K.one
    rw [sum]
    unfold Scale.clamp
    rw [min_eq_left (le_add_of_nonneg_left K.zero_le_one), max_eq_right K.zero_le_one]
  · intro same
    exact absurd (add_eq_left.mp same) (ne_of_gt K.one_pos)

/-- **Fault readings of the two interleavings**: the observer reads the
discounted unit on the fork-then-erase history of `{x}` and `0` on the
erase-then-fork history, which faults. -/
theorem interleavings_read {V : Type} [DecidableEq V] (G : Grammar V) (R : NodeReadings K V) (x : V) :
    (presented G K R).val (chain G K R [.fork x, .erase x] .top) {x} = K.discount^[2] K.one ∧
      (presented G K R).val (chain G K R [.erase x, .fork x] .top) {x} = 0 := by
  rw [val_chain, val_chain, (interleavings_differ G x).1, (interleavings_differ G x).2]
  exact ⟨rfl, rfl⟩

end Meter

end Mettapedia.GSLT.Distinction.HistoryObserverControls
