import Mettapedia.GSLT.LanguageDef.ModuleFormat.MaudeCompilation

/-! The independent first-order term IR embeds injectively into the common
Pattern carrier. Operator declaration identity and variable names survive
exactly; no ACU normalization is hidden in this boundary. -/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.MaudeCompilation

open Mettapedia.Languages

theorem decode_encode (term : Maude.Term) : decode? (encode term) = some term := by
  refine Maude.Term.rec
    (motive_1 := fun term => decode? (encode term) = some term)
    (motive_2 := fun terms => (terms.map encode).mapM decode? = some terms)
    ?_ ?_ ?_ ?_ term
  · intro name
    rw [encode, decode?]
  · intro id arguments ih
    rw [encode, decode?, ih]
    rfl
  · rfl
  · intro head tail first rest
    simp [List.mapM_cons, first, rest]

theorem encode_injective : Function.Injective encode := by
  intro first second same
  have decoded := congrArg decode? same
  simpa only [decode_encode, Option.some.injEq] using decoded

end Mettapedia.GSLT.LanguageDef.ModuleFormat.MaudeCompilation
