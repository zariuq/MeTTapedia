import Mettapedia.GSLT.Causality.ResourceProduct
import Mettapedia.GSLT.Causality.ResourceReads
import Mettapedia.GSLT.Causality.ResourceWaves
import Mettapedia.GSLT.Causality.HistoryMonad

/-!
# Runs of resource systems: firing lists and occurrence paths

A run of a resource system can be written two ways: as the list of instances it
fires, each enabled in the bag it fires in (`System.Fires`), or as an occurrence
path of the system's presentation, along which valuations, accounts and the
conservation law are read. They are the same runs: every occurrence path lists
its firings, and every list of firings is the list of an occurrence path.

The firings of a run determine where it ends, and every valuation of the run
is read off its firings. So a wave, which fires its instances in any order, is
a run. A run of a product is a run of each factor on its own part of the bag,
firing the parts of the joint instances in the same order, and a grade of a
factor's instances is read off the joint instances. For a system paid from a
purse, the first part is the run of the unpaid instances and the second takes
from the purse exactly what the run pays.

Two systems fired together on one bag, the first using only resources outside
a kind and the second only resources of it, are not a product: the first may
produce resources of the second's kind. Still, the first parts fire as a run of
their own, from the same bag, in the same order, ending with the same
resources outside the kind; the two ends differ by what the second parts
consumed and produced.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Causality.ResourceInteraction

open Mettapedia.GSLT.Causality.OccurrenceHistory (Occurrence OccurrencePath OccurrenceValuation)

universe uRes uRule uTok uPurse uJoint uObs

namespace System

section Runs

variable {R : Type uRes} (S : System.{uRes, uRule} R) [DecidableEq R]

/-- The firings of an occurrence path, in order. -/
def pathEntries : {M N : Multiset R} → OccurrencePath S.presentation M N → List S.Entry
  | _, _, .refl _ => []
  | _, _, .cons o rest => ⟨o.site, o.evidence.val⟩ :: pathEntries rest

@[simp] theorem pathEntries_refl (M : Multiset R) :
    S.pathEntries (OccurrencePath.refl (P := S.presentation) M) = [] := rfl

theorem pathEntries_append : ∀ {M N K : Multiset R} (first : OccurrencePath S.presentation M N)
    (second : OccurrencePath S.presentation N K),
    S.pathEntries (first.append second) = S.pathEntries first ++ S.pathEntries second
  | _, _, _, .refl _, _ => rfl
  | _, _, _, .cons o rest, second => by
      change ⟨o.site, o.evidence.val⟩ :: S.pathEntries (rest.append second) = _
      rw [pathEntries_append rest second]
      rfl

/-- **Every occurrence path is a list of firings.** -/
theorem fires_pathEntries : ∀ {M N : Multiset R} (p : OccurrencePath S.presentation M N),
    S.Fires (S.pathEntries p) M N
  | _, _, .refl _ => rfl
  | _, _, .cons o rest => by
      obtain ⟨enabled, same⟩ := o.evidence.property
      refine ⟨enabled, ?_⟩
      have restFires := fires_pathEntries rest
      generalize S.pathEntries rest = order at restFires ⊢
      change S.Fires order (S.fire _ o.evidence.val) _
      rw [← same]
      exact restFires

/-- **Every list of firings is the list of an occurrence path.** -/
theorem exists_path_of_fires : ∀ (order : List S.Entry) {M N : Multiset R},
    S.Fires order M N → ∃ p : OccurrencePath S.presentation M N, S.pathEntries p = order
  | [], M, N, fires => by
      change N = M at fires
      subst fires
      exact ⟨.refl _, rfl⟩
  | entry :: rest, _, _, ⟨enabled, restFires⟩ => by
      obtain ⟨p, entries⟩ := exists_path_of_fires rest restFires
      exact ⟨.cons ⟨entry.1, ⟨entry.2, enabled, rfl⟩⟩ p, congrArg (entry :: ·) entries⟩

/-- **Firings determine where they end.** The same firings from the same bag
end in the same bag. -/
theorem fires_target_unique : ∀ (order : List S.Entry) {M N N' : Multiset R},
    S.Fires order M N → S.Fires order M N' → N = N'
  | [], M, N, N', first, second => by
      change N = M at first
      change N' = M at second
      exact first.trans second.symm
  | _ :: rest, _, _, _, ⟨_, first⟩, ⟨_, second⟩ => fires_target_unique rest first second

/-- Two runs from the same bag with the same firings end in the same bag. -/
theorem target_eq_of_pathEntries_eq {M N N' : Multiset R}
    (first : OccurrencePath S.presentation M N) (second : OccurrencePath S.presentation M N')
    (same : S.pathEntries first = S.pathEntries second) : N = N' :=
  S.fires_target_unique (S.pathEntries first) (S.fires_pathEntries first)
    (same ▸ S.fires_pathEntries second)

/-- Firing lists and occurrence paths are the same runs. -/
theorem fires_iff_exists_path (order : List S.Entry) {M N : Multiset R} :
    S.Fires order M N ↔ ∃ p : OccurrencePath S.presentation M N, S.pathEntries p = order :=
  ⟨S.exists_path_of_fires order, fun ⟨p, entries⟩ => entries ▸ S.fires_pathEntries p⟩

/-- A grade of the instances fired, read along a path, is the sum over its
firings. -/
theorem instanceValuation_onPath {A : Type uObs} [AddCommMonoid A]
    (f : ∀ {site : S.Site}, S.Instance site → A) :
    ∀ {M N : Multiset R} (p : OccurrencePath S.presentation M N),
      (S.instanceValuation f).onPath p = ((S.pathEntries p).map fun entry => f entry.2).sum
  | _, _, .refl _ => rfl
  | _, _, .cons o rest => by
      change f o.evidence.val + (S.instanceValuation f).onPath rest = _
      rw [instanceValuation_onPath f rest]
      rfl

/-- An additive map of a valuation is the valuation of the mapped grades. -/
theorem instanceValuation_onPath_map {A B : Type uObs} [AddCommMonoid A] [AddCommMonoid B]
    (g : A →+ B) (f : ∀ {site : S.Site}, S.Instance site → A) {M N : Multiset R}
    (p : OccurrencePath S.presentation M N) :
    g ((S.instanceValuation f).onPath p) = (S.instanceValuation fun i => g (f i)).onPath p := by
  rw [S.instanceValuation_onPath, S.instanceValuation_onPath, map_list_sum, List.map_map]
  rfl

/-- **A wave is a run**: an enabled step fired in the listed order is an
occurrence path from the bag to the wave's target. -/
theorem exists_path_of_stepEnables (order : List S.Entry) {M : Multiset R}
    (enabled : S.StepEnables M order) :
    ∃ p : OccurrencePath S.presentation M (S.waveTarget M order), S.pathEntries p = order :=
  S.exists_path_of_fires order (S.fires_of_stepEnables order M enabled)

end Runs

/-! ## A run of a product is a run of each factor -/

section ProductRuns

variable {R : Type uRes} {T : Type uTok} [DecidableEq R] [DecidableEq T]
  (S : System.{uRes, uRule} R) (P : System.{uTok, uPurse} T)
  {Site : Type uJoint} {Joint : Site → Type uJoint}
  (left : ∀ {site : Site}, Joint site → S.Entry)
  (right : ∀ {site : Site}, Joint site → P.Entry)

/-- **A run of a product is a run of each factor on its own part of the bag**,
firing the parts of the joint instances in the same order. -/
theorem product_path_parts {A : Multiset R} {B : Multiset T} {N : Multiset (R ⊕ T)}
    (run : OccurrencePath (S.product P Site Joint @left @right).presentation (marking A B) N) :
    ∃ A' B', N = marking A' B' ∧
      (∃ first : OccurrencePath S.presentation A A',
        S.pathEntries first =
          ((S.product P Site Joint @left @right).pathEntries run).map fun entry => left entry.2) ∧
      ∃ second : OccurrencePath P.presentation B B',
        P.pathEntries second =
          ((S.product P Site Joint @left @right).pathEntries run).map fun entry => right entry.2 := by
  obtain ⟨A', B', rfl, firstFires, secondFires⟩ :=
    (S.product_fires_iff P @left @right _ A B N).mp
      ((S.product P Site Joint @left @right).fires_pathEntries run)
  exact ⟨A', B', rfl, S.exists_path_of_fires _ firstFires, P.exists_path_of_fires _ secondFires⟩

/-- A grade of the first factor's instances, read along the first part of a
run, is the grade of the joint instances' first parts along the run. -/
theorem product_part_valuation {Obs : Type uObs} [AddCommMonoid Obs]
    (f : ∀ {site : S.Site}, S.Instance site → Obs) {A A' : Multiset R}
    {M N : Multiset (R ⊕ T)}
    (run : OccurrencePath (S.product P Site Joint @left @right).presentation M N)
    (first : OccurrencePath S.presentation A A')
    (entries : S.pathEntries first =
      ((S.product P Site Joint @left @right).pathEntries run).map fun entry => left entry.2) :
    (S.instanceValuation f).onPath first =
      ((S.product P Site Joint @left @right).instanceValuation fun j => f (left j).2).onPath run := by
  rw [S.instanceValuation_onPath f first, entries,
    (S.product P Site Joint @left @right).instanceValuation_onPath, List.map_map]
  rfl

end ProductRuns

/-! ## Paying: the unpaid run and what the purse gives -/

section PaidRuns

variable {R : Type uRes} {T : Type uTok} [DecidableEq R] [DecidableEq T]
  (S : System.{uRes, uRule} R) (price : ∀ {site : S.Site}, S.Instance site → Multiset T)

/-- **A paid run is an unpaid run and a payment.** A run of the system paid at
`price` fires the same instances of the system, in the same order, on the
first part of the bag; and the purse before is the purse after with what the
run pays. -/
theorem funded_path_parts {A : Multiset R} {B : Multiset T} {N : Multiset (R ⊕ T)}
    (run : OccurrencePath (funded S @price).presentation (marking A B) N) :
    ∃ A' B', N = marking A' B' ∧
      (∃ unpaid : OccurrencePath S.presentation A A',
        S.pathEntries unpaid = (funded S @price).pathEntries run) ∧
      B = B' + ((funded S @price).instanceValuation @price).onPath run := by
  obtain ⟨A', B', rfl, ⟨unpaid, entries⟩, -⟩ :=
    S.product_path_parts (tokens T) (fun i => ⟨_, i⟩) (fun i => ⟨PUnit.unit, price i⟩) run
  refine ⟨A', B', rfl, ⟨unpaid, entries.trans ?_⟩, ?_⟩
  · exact List.map_id' _ ▸ (List.map_congr_left fun _ _ => rfl)
  · have conserved := funded_run_conserved S @price run
    rwa [rightPart_marking] at conserved

/-- **What a funded run pays is recoverable from where it ends.** The purse
before is fixed, so the payment is the purse before less the purse after:
erasing the recorded total loses nothing. -/
theorem funded_payment_recoverable (A : Multiset R) (B : Multiset T) :
    HistoryMonad.StateRecoverable (P := (funded S @price).presentation) (root := marking A B)
      (fun {_} run => ((funded S @price).instanceValuation @price).onPath run) := by
  refine ⟨fun N => B - rightPart N, fun run => ?_⟩
  obtain ⟨A', B', rfl, -, conserved⟩ := S.funded_path_parts @price run
  show ((funded S @price).instanceValuation @price).onPath run = B - rightPart (marking A' B')
  calc ((funded S @price).instanceValuation @price).onPath run
      = B' + ((funded S @price).instanceValuation @price).onPath run - B' :=
        (add_tsub_cancel_left _ _).symm
    _ = B - rightPart (marking A' B') := by rw [← conserved, rightPart_marking]

end PaidRuns

/-! ## Runs of two systems fired together on one bag -/

section JointRuns

variable {R : Type uRes} [DecidableEq R]
  (S : System.{uRes, uRule} R) (P : System.{uRes, uPurse} R)
  {Site : Type uJoint} {Joint : Site → Type uJoint}
  (left : ∀ {site : Site}, Joint site → S.Entry)
  (right : ∀ {site : Site}, Joint site → P.Entry)
  (kind : R → Prop) [DecidablePred kind]

/-- **A joint run projects to a run of its first part**, when the first part
consumes and reads only resources outside `kind` and the second part consumes,
reads and produces only resources of `kind`. From any bag with the same
resources outside `kind`, the first parts of the joint instances fire in the
same order, and the two runs end with the same resources outside `kind`. The
first part may produce resources of `kind`; nothing is asked of them. -/
theorem joint_path_left
    (leftUses : ∀ {site : Site} (j : Joint site),
      ∀ r ∈ S.consume (left j).2 + S.read (left j).2, ¬ kind r)
    (rightUses : ∀ {site : Site} (j : Joint site),
      ∀ r ∈ P.consume (right j).2 + P.read (right j).2, kind r)
    (rightProduces : ∀ {site : Site} (j : Joint site),
      ∀ r ∈ P.produce (right j).2, kind r) :
    ∀ {M N : Multiset R}
      (run : OccurrencePath (S.joint P Site Joint @left @right).presentation M N)
      (L : Multiset R), L.filter (fun r => ¬ kind r) = M.filter (fun r => ¬ kind r) →
      ∃ (N' : Multiset R) (first : OccurrencePath S.presentation L N'),
        S.pathEntries first =
            ((S.joint P Site Joint @left @right).pathEntries run).map
              (fun entry => left entry.2) ∧
          N'.filter (fun r => ¬ kind r) = N.filter (fun r => ¬ kind r)
  | _, _, .refl _, L, same => ⟨L, OccurrencePath.refl (P := S.presentation) L, rfl, same⟩
  | M, _, .cons o rest, L, same => by
      obtain ⟨enabled, fired⟩ := o.evidence.property
      have leftConsumes : ∀ r ∈ S.consume (left o.evidence.val).2, ¬ kind r :=
        fun r member => leftUses o.evidence.val r (Multiset.mem_add.mpr (Or.inl member))
      have rightConsumes : ∀ r ∈ P.consume (right o.evidence.val).2, kind r :=
        fun r member => rightUses o.evidence.val r (Multiset.mem_add.mpr (Or.inl member))
      have leftEnabled : S.Enables L (left o.evidence.val).2 := by
        have parts := (S.joint_enables_iff P @left @right kind M o.evidence.val
          (leftUses o.evidence.val) (rightUses o.evidence.val)).mp enabled
        refine le_trans ?_ (Multiset.filter_le (fun r => ¬ kind r) L)
        rw [same]
        exact parts.1
      have nextSame : (S.fire L (left o.evidence.val).2).filter (fun r => ¬ kind r) =
          ((S.joint P Site Joint @left @right).fire M o.evidence.val).filter
            (fun r => ¬ kind r) := by
        rw [S.joint_fire_filter_not P @left @right kind M o.evidence.val leftConsumes
          rightConsumes (rightProduces o.evidence.val), ← same]
        change (L - S.consume (left o.evidence.val).2 + S.produce (left o.evidence.val).2).filter
            (fun r => ¬ kind r) = _
        rw [Multiset.filter_add, Multiset.filter_sub,
          Multiset.filter_eq_self.mpr leftConsumes]
      rw [← fired] at nextSame
      obtain ⟨N', first, entries, ends⟩ := joint_path_left leftUses rightUses rightProduces
        rest (S.fire L (left o.evidence.val).2) nextSame
      exact ⟨N', .cons ⟨(left o.evidence.val).1, ⟨(left o.evidence.val).2, leftEnabled, rfl⟩⟩
        first, congrArg (left o.evidence.val :: ·) entries, ends⟩

/-- **The ledger between a joint run and the run of its first part.** When the
first parts of the joint instances fire in the same order from the same bag,
the end of that run, with all the second parts produce, is the end of the joint
run, with all the second parts consume. -/
theorem joint_path_left_ledger {M N N' : Multiset R}
    (run : OccurrencePath (S.joint P Site Joint @left @right).presentation M N)
    (first : OccurrencePath S.presentation M N')
    (entries : S.pathEntries first =
      ((S.joint P Site Joint @left @right).pathEntries run).map (fun entry => left entry.2)) :
    N' + ((S.joint P Site Joint @left @right).instanceValuation
        fun j => P.produce (right j).2).onPath run =
      N + ((S.joint P Site Joint @left @right).instanceValuation
        fun j => P.consume (right j).2).onPath run := by
  have jointBalance := (S.joint P Site Joint @left @right).balance run
  have firstBalance := S.balance first
  have leftProduced : S.producedValuation.onPath first =
      ((S.joint P Site Joint @left @right).instanceValuation
        fun j => S.produce (left j).2).onPath run := by
    rw [S.instanceValuation_onPath, (S.joint P Site Joint @left @right).instanceValuation_onPath,
      entries, List.map_map]
    rfl
  have leftConsumed : S.consumedValuation.onPath first =
      ((S.joint P Site Joint @left @right).instanceValuation
        fun j => S.consume (left j).2).onPath run := by
    rw [S.instanceValuation_onPath, (S.joint P Site Joint @left @right).instanceValuation_onPath,
      entries, List.map_map]
    rfl
  have jointProduced := (S.joint P Site Joint @left @right).instanceValuation_add
    (fun j => S.produce (left j).2) (fun j => P.produce (right j).2) run
  have jointConsumed := (S.joint P Site Joint @left @right).instanceValuation_add
    (fun j => S.consume (left j).2) (fun j => P.consume (right j).2) run
  change M + (S.joint P Site Joint @left @right).producedValuation.onPath run =
    N + (S.joint P Site Joint @left @right).consumedValuation.onPath run at jointBalance
  change (S.joint P Site Joint @left @right).producedValuation.onPath run = _ at jointProduced
  change (S.joint P Site Joint @left @right).consumedValuation.onPath run = _ at jointConsumed
  rw [jointProduced, jointConsumed] at jointBalance
  rw [leftProduced, leftConsumed] at firstBalance
  apply add_right_cancel (b := ((S.joint P Site Joint @left @right).instanceValuation
    fun j => S.consume (left j).2).onPath run)
  calc _ = N' + ((S.joint P Site Joint @left @right).instanceValuation
          fun j => S.consume (left j).2).onPath run +
        ((S.joint P Site Joint @left @right).instanceValuation
          fun j => P.produce (right j).2).onPath run := by ac_rfl
    _ = M + ((S.joint P Site Joint @left @right).instanceValuation
          fun j => S.produce (left j).2).onPath run +
        ((S.joint P Site Joint @left @right).instanceValuation
          fun j => P.produce (right j).2).onPath run := by rw [firstBalance]
    _ = N + (((S.joint P Site Joint @left @right).instanceValuation
          fun j => S.consume (left j).2).onPath run +
        ((S.joint P Site Joint @left @right).instanceValuation
          fun j => P.consume (right j).2).onPath run) := by rw [add_assoc, jointBalance]
    _ = _ := by ac_rfl

/-- **A joint run is a run of its first part and a ledger of its second.** -/
theorem joint_path_left_parts
    (leftUses : ∀ {site : Site} (j : Joint site),
      ∀ r ∈ S.consume (left j).2 + S.read (left j).2, ¬ kind r)
    (rightUses : ∀ {site : Site} (j : Joint site),
      ∀ r ∈ P.consume (right j).2 + P.read (right j).2, kind r)
    (rightProduces : ∀ {site : Site} (j : Joint site),
      ∀ r ∈ P.produce (right j).2, kind r)
    {M N : Multiset R}
    (run : OccurrencePath (S.joint P Site Joint @left @right).presentation M N) :
    ∃ (N' : Multiset R) (first : OccurrencePath S.presentation M N'),
      S.pathEntries first =
          ((S.joint P Site Joint @left @right).pathEntries run).map (fun entry => left entry.2) ∧
        N'.filter (fun r => ¬ kind r) = N.filter (fun r => ¬ kind r) ∧
        N' + ((S.joint P Site Joint @left @right).instanceValuation
            fun j => P.produce (right j).2).onPath run =
          N + ((S.joint P Site Joint @left @right).instanceValuation
            fun j => P.consume (right j).2).onPath run := by
  obtain ⟨N', first, entries, ends⟩ :=
    S.joint_path_left P @left @right kind leftUses rightUses rightProduces run M rfl
  exact ⟨N', first, entries, ends, S.joint_path_left_ledger P @left @right run first entries⟩

end JointRuns

end System

/-! ## Controls -/

namespace RunControls

open Controls ProductControls

/-- The replicated input paid one token per message, from a purse of two. -/
def twoPaidMessages : Multiset (Res ⊕ Unit) := marking twoMessages {(), ()}

/-- **The same payment, a different order of firings.** Taking the two
messages in either order pays two tokens; the two runs fire their instances in
different orders. -/
theorem two_orders_same_payment :
    ∃ (first second : OccurrencePath paidReceiver.presentation twoPaidMessages
        (marking {Res.receiver, Res.received 1, Res.received 2} 0)),
      (paidReceiver.instanceValuation fun _ => ({()} : Multiset Unit)).onPath first =
        (paidReceiver.instanceValuation fun _ => ({()} : Multiset Unit)).onPath second ∧
      paidReceiver.pathEntries first ≠ paidReceiver.pathEntries second := by
  obtain ⟨first, firstEntries⟩ := paidReceiver.exists_path_of_fires
    [⟨(), takePaid 1⟩, ⟨(), takePaid 2⟩] (M := twoPaidMessages) (N := marking {Res.receiver, Res.received 1, Res.received 2} 0)
    (by refine ⟨?_, ?_, ?_⟩ <;> (try unfold System.Enables) <;> (try unfold System.Fires) <;>
      (try unfold System.fire) <;> decide)
  obtain ⟨second, secondEntries⟩ := paidReceiver.exists_path_of_fires
    [⟨(), takePaid 2⟩, ⟨(), takePaid 1⟩] (M := twoPaidMessages) (N := marking {Res.receiver, Res.received 1, Res.received 2} 0)
    (by refine ⟨?_, ?_, ?_⟩ <;> (try unfold System.Enables) <;> (try unfold System.Fires) <;>
      (try unfold System.fire) <;> decide)
  refine ⟨first, second, ?_, ?_⟩
  · rw [paidReceiver.instanceValuation_onPath, paidReceiver.instanceValuation_onPath,
      firstEntries, secondEntries]
    rfl
  · rw [firstEntries, secondEntries]
    intro same
    have values := congrArg
      (fun order : List paidReceiver.Entry => order.map fun entry => (show ℕ from entry.2)) same
    exact absurd values (by decide)

/-- The replicated input paid nothing per message. -/
def freeReceiver : System (Res ⊕ Unit) := funded persistentReceiver (fun _ => (0 : Multiset Unit))

/-- **A firing at price zero still fires.** It pays nothing, is one firing of
work, and leaves the purse as it was: payment is not work. -/
theorem zero_price_still_works :
    ∃ run : OccurrencePath freeReceiver.presentation (marking twoMessages 0)
        (marking {Res.message 2, Res.receiver, Res.received 1} 0),
      (freeReceiver.instanceValuation fun _ => (0 : Multiset Unit)).onPath run = 0 ∧
        (freeReceiver.pathEntries run).length = 1 := by
  obtain ⟨run, entries⟩ := freeReceiver.exists_path_of_fires
    [⟨(), (show freeReceiver.Instance () from takeAgain 1)⟩] (M := marking twoMessages 0)
    (N := marking {Res.message 2, Res.receiver, Res.received 1} 0)
    (by refine ⟨?_, ?_⟩ <;> (try unfold System.Enables) <;> (try unfold System.Fires) <;>
      (try unfold System.fire) <;> decide)
  refine ⟨run, ?_, ?_⟩
  · rw [freeReceiver.instanceValuation_onPath, entries]
    rfl
  · rw [entries]
    rfl

/-- **The order of a run is not recoverable from where it ends**: two runs
with the same ends and the same payment fire in different orders, so erasing the
order loses information. -/
theorem order_not_recoverable :
    ¬ HistoryMonad.StateRecoverable (P := paidReceiver.presentation) (root := twoPaidMessages)
      (fun {_} run => paidReceiver.pathEntries run) := by
  rintro ⟨fromState, recovers⟩
  obtain ⟨first, second, -, different⟩ := two_orders_same_payment
  exact different ((recovers first).trans (recovers second).symm)

end RunControls

end Mettapedia.GSLT.Causality.ResourceInteraction
