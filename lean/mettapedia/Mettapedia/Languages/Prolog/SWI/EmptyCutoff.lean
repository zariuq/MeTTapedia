import Std

/-!
Independent, finite generation model for the proposed empty-predicate
shortcut. This proves the guard's needed timestamp condition. It does not
verify SWI-Prolog's C implementation or its memory ordering.
-/
set_option autoImplicit false

namespace Mettapedia.Languages.Prolog.SWI.EmptyCutoff

def visible (born erased query : Nat) : Prop := born ≤ query ∧ query < erased
def fastFail (lastModified query : Nat) : Prop := lastModified ≤ query

/-- A published upper bound on every erased generation makes the shortcut
safe for a clause that an old reader could otherwise see. -/
theorem upper_bound_suffices (born erased lastModified query : Nat)
    (upper : erased ≤ lastModified) (useShortcut : fastFail lastModified query) :
    ¬ visible born erased query := by
  unfold fastFail at useShortcut
  unfold visible
  omega

/-- Pausing a writer after erasing at 4 and before publishing that stamp
leaves lastModified = 3. A reader at 3 takes the shortcut even though
the clause born at 2 was visible at that reader's generation. -/
theorem stale_stamp_loses_visible_clause :
    fastFail 3 3 ∧ visible 2 4 3 := by simp [fastFail, visible]

/-- A late older assignment can recreate that state after the newer
writer has completed: the last store need not be the last erase. -/
theorem out_of_order_plain_stores_regress :
    let olderErase := 3
    let newerErase := 4
    let lastModifiedAfterBoth := olderErase
    lastModifiedAfterBoth < newerErase ∧
      fastFail lastModifiedAfterBoth 3 ∧ visible 2 newerErase 3 := by
  simp [fastFail, visible]

/-- Maximum publication is order-independent once both writes complete.
It does not by itself close the interval before either write publishes. -/
theorem max_publication_commutes (old e1 e2 : Nat) :
    max (max old e1) e2 = max (max old e2) e1 := by
  omega

end Mettapedia.Languages.Prolog.SWI.EmptyCutoff
