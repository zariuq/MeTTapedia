import Mettapedia.SetTheory.Surreal.SignExpansion

/-!
# Ordinal ranks on the surreal number line

The all-positive expansion of length `α` embeds ordinals into surreals.
It preserves and reflects order, so a decrease of this reading is precisely
an ordinal decrease. The ordinal carrier supplies well-foundedness; the full
surreal order does not.
-/

set_option autoImplicit false

namespace Mettapedia.SetTheory.SignExpansion.Surreal

def ordinalPre (α : Ordinal) : PreSurreal := ⟨α, fun _ => true⟩

noncomputable def ofOrdinal (α : Ordinal) : Surreal := mk (ordinalPre α)

theorem ordinalPre_signAt_of_lt {α β : Ordinal} (h : β < α) :
    (ordinalPre α).signAt β = Sign.pos := by
  simp [PreSurreal.signAt, ordinalPre, h]

theorem ofOrdinal_strictMono : StrictMono ofOrdinal := by
  intro α β smaller
  change PreSurreal.Lt (ordinalPre α) (ordinalPre β)
  refine ⟨α, ?_, ?_⟩
  · intro γ below
    rw [ordinalPre_signAt_of_lt below,
      ordinalPre_signAt_of_lt (below.trans smaller)]
  · rw [PreSurreal.signAt_of_ge (x := ordinalPre α) (le_refl α),
      ordinalPre_signAt_of_lt smaller]
    exact Sign.zero_lt_pos

theorem ofOrdinal_lt_iff (α β : Ordinal) : ofOrdinal α < ofOrdinal β ↔ α < β :=
  ofOrdinal_strictMono.lt_iff_lt

theorem ofOrdinal_le_iff (α β : Ordinal) : ofOrdinal α ≤ ofOrdinal β ↔ α ≤ β :=
  ofOrdinal_strictMono.le_iff_le

theorem ofOrdinal_injective : Function.Injective ofOrdinal :=
  ofOrdinal_strictMono.injective

noncomputable def ordinalOrderEmbedding : Ordinal ↪o Surreal :=
  OrderEmbedding.ofStrictMono ofOrdinal ofOrdinal_strictMono

@[simp] theorem ofOrdinal_nat (n : Nat) : ofOrdinal (n : Ordinal) = ofNat n := rfl

@[simp] theorem ofOrdinal_omega : ofOrdinal Ordinal.omega0 = omega := rfl

theorem ordinal_reading_wellFounded :
    WellFounded (fun α β : Ordinal => ofOrdinal α < ofOrdinal β) := by
  simpa only [ofOrdinal_lt_iff] using Ordinal.lt_wf

end Mettapedia.SetTheory.SignExpansion.Surreal
