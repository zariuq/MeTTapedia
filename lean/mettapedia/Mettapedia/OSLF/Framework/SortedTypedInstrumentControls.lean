import Mettapedia.OSLF.Framework.SortedTypedInstrumentFiring

/-!
# Genuine heterogeneous coordinates and the empty-source-sort boundary

Send has a channel coordinate and a process coordinate. Both complete
values, including a nested send with a different channel, survive the actual
ask/get/build receipts. The source also declares an uninhabited argument
sort. Raw administrative syntax can construct an observer-bearing value at
that sort, so no total erasure to source terms can exist. This distinguishes
typed raw syntax from admitted administrative firing and source purity.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.OSLF.Framework.SortedTypedInstrumentControls

open _root_.CategoryTheory
open Mettapedia.OSLF.SortedCommutative
open Mettapedia.GSLT.RedexRelativeCongruence
open SortedTypedInstruments

inductive DataSort where
  | process
  | channel
  | absent

inductive Symbol where
  | name (index : Nat)
  | send
  | blocked

abbrev sourceSignature : Mettapedia.OSLF.SortedConstructors.Signature.{0,0} where
  Srt := DataSort
  Constructor := Symbol
  arity
    | .name _ => 0
    | .send => 2
    | .blocked => 1
  input
    | .name _ => Fin.elim0
    | .send => Fin.cases .channel (fun _ => .process)
    | .blocked => fun _ => .absent
  output
    | .name _ => .channel
    | .send => .process
    | .blocked => .process

def sourceParallel (sort : DataSort) : Prop := sort = .process

abbrev SourceValue (sort : DataSort) := Term sourceSignature sourceParallel sort
abbrev NativeValue (sort : Srt sourceSignature sourceParallel) :=
  Value (source := sourceSignature) (Parallel := sourceParallel) sort

def sourceName (index : Nat) : SourceValue .channel :=
  Term.node (signature := sourceSignature) (Parallel := sourceParallel) (.name index)
    (fun position => Fin.elim0 position)

def sourcePayload (index : Nat) : SourceValue .process :=
  Term.node (signature := sourceSignature) (Parallel := sourceParallel) .send
    (Fin.cases (motive := fun position => SourceValue (sourceSignature.input .send position))
      (sourceName index) (fun _ => .zero rfl))

def sendArguments (index : Nat) (payload : SourceValue .process) :
    Arguments (SourceHead.ordinary (source := sourceSignature) (Parallel := sourceParallel) Symbol.send) :=
  Fin.cases (embed (sourceName index)) (fun _ => embed payload)

def sendAsk (origin index : Nat) (payload : SourceValue .process) :
    Occurrence sourceSignature sourceParallel Nat := .ask origin (.ordinary .send) (sendArguments index payload)

def channelGet (origin index : Nat) (payload : SourceValue .process) :
    Occurrence sourceSignature sourceParallel Nat := .get origin (.ordinary .send) (sendArguments index payload) 0

def processGet (origin index : Nat) (payload : SourceValue .process) :
    Occurrence sourceSignature sourceParallel Nat := .get origin (.ordinary .send) (sendArguments index payload) 1

def sendBuild (origin index : Nat) (payload : SourceValue .process) :
    Occurrence sourceSignature sourceParallel Nat := .build origin (.ordinary .send) (sendArguments index payload)

theorem send_has_genuinely_different_argument_sorts :
    headInput (SourceHead.ordinary (source := sourceSignature) (Parallel := sourceParallel) Symbol.send) 0 ≠
      headInput (SourceHead.ordinary (source := sourceSignature) (Parallel := sourceParallel) Symbol.send) 1 := by
  intro same
  cases same

theorem heterogeneous_get_results_retain_both_complete_values (origin index : Nat)
    (payload : SourceValue .process) :
    (channelGet origin index payload).output = embed (sourceName index) ∧
      (processGet origin index payload).output = embed payload := ⟨rfl, rfl⟩

theorem complete_nested_payload_is_retained :
    (processGet 24 7 (sourcePayload 9)).output =
      Term.node (signature := signature sourceSignature sourceParallel) (Parallel := NativeParallel)
        (.original Symbol.send)
        (Fin.cases (embed (sourceName 9)) (fun _ => .zero rfl)) := by
  change embed (sourcePayload 9) = _
  apply congrArg (Term.node (signature := signature sourceSignature sourceParallel)
    (Parallel := NativeParallel) (.original Symbol.send))
  funext position
  fin_cases position <;> rfl

theorem all_three_actual_firings (origin index : Nat) (payload : SourceValue .process) :
    ActIPO (rules sourceSignature sourceParallel Nat)
        (sendAsk origin index payload).label (sendAsk origin index payload).agent (sendAsk origin index payload).target ∧
      ActIPO (rules sourceSignature sourceParallel Nat)
        (channelGet origin index payload).label (channelGet origin index payload).agent
        (channelGet origin index payload).target ∧
      ActIPO (rules sourceSignature sourceParallel Nat)
        (sendBuild origin index payload).label (sendBuild origin index payload).agent (sendBuild origin index payload).target :=
  ⟨(sendAsk origin index payload).direct_step,
    (channelGet origin index payload).direct_step, (sendBuild origin index payload).direct_step⟩

theorem process_get_is_also_an_actual_firing (origin index : Nat) (payload : SourceValue .process) :
    ActIPO (rules sourceSignature sourceParallel Nat)
      (processGet origin index payload).label (processGet origin index payload).agent (processGet origin index payload).target :=
  (processGet origin index payload).direct_step

def nativeHeadConstructor {sort : Srt sourceSignature sourceParallel} :
    Head (signature := signature sourceSignature sourceParallel) (Parallel := NativeParallel) sort →
      SortedTypedInstruments.Constructor sourceSignature sourceParallel
  | .node constructor _ => constructor

theorem different_channel_indices_remain_distinct (first second : Nat) (different : first ≠ second) :
    classOf (embed (sourceName first)) ≠ classOf (embed (sourceName second)) := by
  intro same
  have inventories := congrArg inventoryQ same
  change inventory (embed (sourceName first)) = inventory (embed (sourceName second)) at inventories
  simp only [sourceName, embed, inventory] at inventories
  have heads := Multiset.singleton_inj.mp inventories
  have constructors := congrArg nativeHeadConstructor heads
  exact different (Symbol.name.inj (Constructor.original.inj constructors))

theorem complete_receipts_do_not_merge_duplicate_origins :
    (directReceipt (processGet 24 7 (sourcePayload 9))).occurrence.target =
        (directReceipt (processGet 25 7 (sourcePayload 9))).occurrence.target ∧
      directReceipt (processGet 24 7 (sourcePayload 9)) ≠ directReceipt (processGet 25 7 (sourcePayload 9)) := by
  refine ⟨rfl, ?_⟩
  intro same
  have origins := congrArg (fun receipt => receipt.occurrence.origin) same
  change (24 : Nat) = 25 at origins
  omega

def unitAsk : Occurrence sourceSignature sourceParallel Nat :=
  .ask 37 (.unit .process rfl) (fun position => Fin.elim0 position)

theorem nullary_unit_has_a_real_sorted_firing :
    ActIPO (rules sourceSignature sourceParallel Nat) unitAsk.label unitAsk.agent unitAsk.target :=
  unitAsk.direct_step

theorem no_source_value_at_absent_sort (supplied : SourceValue .absent) : False := by
  have absent : ∀ {sort : DataSort} (term : SourceValue sort), sort = .absent → False := by
    refine @Term.rec sourceSignature sourceParallel (fun sort _ => sort = .absent → False) ?_ ?_ ?_
    · intro sort parallel same
      subst sort
      cases same
    · intro sort parallel _ _ _ _ same
      subst sort
      cases same
    · intro constructor _ _ same
      cases constructor <;> cases same
  exact absent supplied rfl

def blockedArguments : NativeValue (.arguments (.ordinary Symbol.blocked)) :=
  cut (source := sourceSignature) (Parallel := sourceParallel)
    (.ask (.ordinary Symbol.blocked))
    (probe (source := sourceSignature) (Parallel := sourceParallel) (.ask (.ordinary Symbol.blocked)))
    (embed (.zero rfl : SourceValue .process))

def observerBearingAbsent : NativeValue (.original .absent) :=
  cut (source := sourceSignature) (Parallel := sourceParallel)
    (.get (.ordinary Symbol.blocked) 0)
    (probe (source := sourceSignature) (Parallel := sourceParallel) (.get (.ordinary Symbol.blocked) 0))
    blockedArguments

theorem no_total_original_sort_erasure :
    ¬Nonempty (NativeValue (.original .absent) → SourceValue .absent) := by
  rintro ⟨erase⟩
  exact no_source_value_at_absent_sort (erase observerBearingAbsent)

def blockedNativeTuple :
    Arguments (SourceHead.ordinary (source := sourceSignature) (Parallel := sourceParallel) Symbol.blocked) :=
  fun _ => observerBearingAbsent

def blockedNativeGet : Occurrence sourceSignature sourceParallel Nat :=
  .get 41 (.ordinary Symbol.blocked) blockedNativeTuple 0

theorem full_native_coordinates_do_not_assert_source_inhabitation :
    ActIPO (rules sourceSignature sourceParallel Nat) blockedNativeGet.label
        blockedNativeGet.agent blockedNativeGet.target ∧
      ¬Nonempty (SourceValue .absent) :=
  ⟨blockedNativeGet.direct_step, fun ⟨supplied⟩ => no_source_value_at_absent_sort supplied⟩

end Mettapedia.OSLF.Framework.SortedTypedInstrumentControls
