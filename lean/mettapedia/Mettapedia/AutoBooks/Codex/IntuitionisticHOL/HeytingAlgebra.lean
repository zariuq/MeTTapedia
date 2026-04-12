import Mathlib.Order.CompleteBooleanAlgebra

namespace Mettapedia.AutoBooks.Codex.IntuitionisticHOL

/-- Mathlib's complete Heyting algebra interface, used as the truth-value algebra. -/
abbrev HeytingFrame := Order.Frame

section

variable {α : Type*} [HeytingFrame α] {a b c : α}

theorem le_entails_iff : a ≤ b ⇨ c ↔ a ⊓ b ≤ c :=
  le_himp_iff

theorem entails_top : a ⇨ (⊤ : α) = ⊤ :=
  himp_top

theorem top_entails : (⊤ : α) ⇨ a = a :=
  top_himp

theorem antecedent_entails_consequent : a ⊓ (a ⇨ b) ≤ b :=
  inf_himp_le

end

end Mettapedia.AutoBooks.Codex.IntuitionisticHOL
