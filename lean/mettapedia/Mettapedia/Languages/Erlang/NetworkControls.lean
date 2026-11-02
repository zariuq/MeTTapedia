import Mettapedia.Languages.Erlang.Network

/-! Separating controls for FIFO on each channel, independent-channel
overtaking, duplicate occurrences, and delivery before receive. -/

set_option autoImplicit false

namespace Mettapedia.Languages.Erlang.Network.Controls

def first : Envelope String := ⟨⟨1, 0⟩, "a1"⟩
def second : Envelope String := ⟨⟨1, 0⟩, "a2"⟩
def other : Envelope String := ⟨⟨2, 0⟩, "b"⟩

/- b may be delivered before a1, even if b was sent after a2. It is on a
different point-to-point channel. a2 may not overtake a1. -/
#guard deliverAt? 2 [first, second, other] == some (other, [first, second])
#guard deliverAt? 1 [first, second, other] == none
#guard deliverAt? 0 [first, second, other] == some (first, [second, other])
#guard deliverAt? 0 [second, other] == some (second, [other])
#guard deliverAt? 0 [first, first] == some (first, [first])
#guard deliverAt? 1 [first, first] == none
#guard deliverAt? 100 [first] == none
#guard deliverAt? 0 ([] : List (Envelope String)) == none

theorem independent_channel_can_overtake : Delivers [first, second, other] other [first, second] :=
  deliverAt_sound (index := 2) (by decide)

theorem later_same_channel_refused : deliverAt? 1 [first, second, other] = none := by decide

theorem duplicate_occurrence_retained : Delivers [first, first] first [first] :=
  deliverAt_sound (index := 0) (by decide)

def box : Mailbox String := ⟨["skipped"], ["old"], ["arrived"]⟩
#guard (box.deliver "a1").contents == ["skipped", "old", "arrived", "a1"]
#guard (box.deliver "a1").savedRev == ["skipped"]
#guard Mailbox.selectFirst (fun message => if message = "a1" then some message else none)
  (box.deliver "a1").contents == some ("a1", ["skipped", "old", "arrived"])

end Mettapedia.Languages.Erlang.Network.Controls
