import Mettapedia.GSLT.LanguageDef.ModuleFormat.Radix16Scalar

/-! The fixed-width scalar decoder admits only canonical word constructors.
This inverse is needed when printed lexical data is read back as syntax. -/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.Radix16Codec

open Mettapedia.OSLF.MeTTaIL.Syntax

theorem readNibble?_inverse (term : Pattern) (value : Fin 16)
    (read : readNibble? term = some value) : nibble value = term := by
  unfold readNibble? at read
  split at read <;> cases read <;> rfl

theorem decode?_inverse (term : Pattern) (value : Nat)
    (read : decode? term = some value) :
    ∃ bounded : value < 16 ^ 6, encode ⟨value, bounded⟩ = term := by
  unfold decode? at read
  split at read
  · rename_i n5 n4 n3 n2 n1 n0
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at read
    obtain ⟨a5, h5, a4, h4, a3, h3, a2, h2, a1, h1, a0, h0, rfl⟩ := read
    have b5 := a5.isLt
    have b4 := a4.isLt
    have b3 := a3.isLt
    have b2 := a2.isLt
    have b1 := a1.isLt
    have b0 := a0.isLt
    refine ⟨by norm_num; omega, ?_⟩
    rw [← readNibble?_inverse _ _ h5, ← readNibble?_inverse _ _ h4,
      ← readNibble?_inverse _ _ h3, ← readNibble?_inverse _ _ h2,
      ← readNibble?_inverse _ _ h1, ← readNibble?_inverse _ _ h0]
    change word _ _ _ _ _ _ = word a5 a4 a3 a2 a1 a0
    congr 1 <;> apply Fin.ext <;> simp only [digit] <;> norm_num <;> omega
  · cases read

end Mettapedia.GSLT.LanguageDef.ModuleFormat.Radix16Codec
