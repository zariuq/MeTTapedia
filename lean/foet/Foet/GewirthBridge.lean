import Foet.EthicsCore
import Foet.GewirthPGC

set_option autoImplicit false

namespace Foet

namespace GewirthBridge

universe u

namespace WorldEmbedding

abbrev PairWorld (Ctx : Type u) (World : Type u) : Type u :=
  Ctx × World

def toMeaning {Ctx : Type u} {World : Type u} (φ : Formula (PairWorld Ctx World)) : Gewirth.Meaning Ctx World :=
  fun c w => φ (c, w)

def ofMeaning {Ctx : Type u} {World : Type u} (m : Gewirth.Meaning Ctx World) : Formula (PairWorld Ctx World) :=
  fun cw => m cw.1 cw.2

theorem ofMeaning_toMeaning {Ctx : Type u} {World : Type u} (φ : Formula (PairWorld Ctx World)) :
    ofMeaning (toMeaning φ) = φ := by
  funext cw
  rfl

theorem toMeaning_ofMeaning {Ctx : Type u} {World : Type u} (m : Gewirth.Meaning Ctx World) :
    toMeaning (ofMeaning m) = m := by
  funext c w
  rfl

end WorldEmbedding

open WorldEmbedding

def deonticSemanticsOfGewirthOi {Ctx : Type u} {World : Type u}
    (ob : Formula World → Formula World → Prop) (pv : World → Formula World) :
    DeonticSemantics (PairWorld Ctx World) :=
  ⟨fun tag φ =>
    match tag with
    | .Obligation =>
        ofMeaning (Gewirth.Oi (Ctx := Ctx) (World := World) ob pv (toMeaning φ))
    | .Prohibition =>
        ofMeaning
          (Gewirth.Oi (Ctx := Ctx) (World := World) ob pv (fun c w => ¬ toMeaning φ c w))
    | .Permission =>
        fun cw =>
          ¬
            (ofMeaning
                (Gewirth.Oi (Ctx := Ctx) (World := World) ob pv (fun c w => ¬ toMeaning φ c w)))
              cw⟩

theorem deonticSemanticsOfGewirthOi_obligation {Ctx : Type u} {World : Type u}
    (ob : Formula World → Formula World → Prop) (pv : World → Formula World)
    (φ : Formula (PairWorld Ctx World)) :
    (deonticSemanticsOfGewirthOi (Ctx := Ctx) (World := World) ob pv).deontic .Obligation φ =
      ofMeaning (Gewirth.Oi (Ctx := Ctx) (World := World) ob pv (toMeaning φ)) := by
  rfl

theorem PGC_strong_implies_obligation_nonInterference (I : Gewirth.PGCInterpretation) (h : Gewirth.PGCAssumptions I) :
    (∀ C x, Gewirth.PPA (Ctx := I.Ctx) (World := I.World) I.ActsOnPurpose x C (I.worldOf C) →
      (deonticSemanticsOfGewirthOi (Ctx := I.Ctx) (World := I.World) I.ob I.pv).deontic .Obligation
        (ofMeaning (Gewirth.NonInterference (Ctx := I.Ctx) (World := I.World) I.InterferesWith x I.FWB))
        (C, I.worldOf C)) := by
  intro C x hPPA
  have hPGC : Gewirth.PGCStatement I .PGC_strong :=
    Gewirth.PGC_strong_ofAssumptions I h
  have hAtC :=
    hPGC C x hPPA
  -- unfold the bridge semantics: obligation is exactly Gewirth's `Oi`.
  simpa [deonticSemanticsOfGewirthOi, WorldEmbedding.ofMeaning, WorldEmbedding.toMeaning,
    WorldEmbedding.toMeaning_ofMeaning, Gewirth.RightTo,
    Gewirth.Oi, Gewirth.NonInterference]
    using hAtC

end GewirthBridge

end Foet
