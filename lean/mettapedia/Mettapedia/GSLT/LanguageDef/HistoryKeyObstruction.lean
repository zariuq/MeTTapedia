import Mettapedia.GSLT.LanguageDef.Cost.KeyObservation

/-!
# No monad on continued theories concatenates histories

A history construction on continued interactive GSLTs would send a theory to
one whose configurations carry a word of events, and its multiplication would
concatenate the two words of a history of histories. Every monad on that
category has a multiplication that is injective on canonical keys
(`canonicalMultiplication_bijective`), and concatenation is not injective: an
event followed by the empty word and the empty word followed by the event give
the same word. So no monad on the category reads, on canonical keys, as a key
with a word of events and concatenation.

What does hold is proved elsewhere: the words of events form the free monoid
and its writer monad; runs with their accounts form a parameterized monad read
into the writer (`RunAccount`); and every GSLT has a history theory that
appends one event per step (`HistoryMonad.history`).
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.CIGSLT

/-- **No monad on continued theories concatenates histories on canonical
keys.** Whatever reading of the keys of `T (T G)` as a key with two words and of
`T G` as a key with one word, the multiplication of `T` does not act as
concatenation, as soon as there is an event. -/
theorem no_concatenating_history_monad (T : CategoryTheory.Monad CIGSLT) (G : CIGSLT)
    {Key Event : Type*} (key : Key) (event : Event)
    (outer : (T.obj (T.obj G)).CanonicalKey ≃ (Key × List Event) × List Event)
    (inner : (T.obj G).CanonicalKey ≃ Key × List Event) :
    ¬ ∀ k, inner ((T.μ.app G).canonicalKeyMap k) =
      ((outer k).1.1, (outer k).1.2 ++ (outer k).2) := by
  intro concatenates
  have same : (T.μ.app G).canonicalKeyMap (outer.symm ((key, [event]), [])) =
      (T.μ.app G).canonicalKeyMap (outer.symm ((key, []), [event])) := by
    apply inner.injective
    rw [concatenates, concatenates]
    simp
  have keys := congrArg outer ((canonicalMultiplication_bijective T G).1 same)
  simp at keys

end Mettapedia.GSLT.LanguageDef.CIGSLT
