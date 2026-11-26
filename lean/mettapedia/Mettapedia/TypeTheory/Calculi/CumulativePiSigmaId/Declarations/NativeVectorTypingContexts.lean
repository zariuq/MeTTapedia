import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorEvidenceSyntax
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.StructuralConversionCode
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.StructuralTypingReplayFormation

/-! Shared exact typing and context replay plans. -/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorTypingContexts

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation

private abbrev C (RootCode : Nat → Type) := StructuralConversionCode.Code Tower.Head RootCode
private abbrev T (RootCode : Nat → Type) := StructuralTypingReplay.Code Tower.Head (C RootCode)
private abbrev X (RootCode : Nat → Type) := StructuralTypingReplay.ContextCode Tower.Head (C RootCode)

variable {RootCode : Nat → Type}

def assemble_040dfca8646d0f847645 (ambient : Nat)
    (x0 : Tower.Tm ambient)
    (x1 : Tower.Tm (ambient + 1))
    (x2 : Tower.Head)
    (x3 : T RootCode 0)
    (x4 : Tower.Head)
    (x5 : Tower.Head)
    (x6 : Tower.Head)
    (x7 : T RootCode ambient)
    (x8 : T RootCode (ambient + 1))
    (x9 : T RootCode (ambient + 1)) : T RootCode ambient :=
  .appElim (x0) (x1) (.const (x2) (x3)) (.lamIntro (x4) (.piForm (x5) (x6) (x7) (x8)) (.cumul (x5) (x9)))

def assemble_17a6b16386a9978ede13 (ambient : Nat)
    (x0 : Tower.Tm ambient)
    (x1 : Tower.Tm (ambient + 1))
    (x2 : Tower.Tm ambient)
    (x3 : Tower.Tm (ambient + 1))
    (x4 : T RootCode ambient)
    (x5 : T RootCode ambient)
    (x6 : Tower.Head)
    (x7 : T RootCode ambient)
    (x8 : T RootCode (ambient + 1)) : T RootCode ambient :=
  .appElim (x0) (x1) (.appElim (x2) (x3) (x4) (x5)) (.lamIntro (x6) (x7) (x8))

def assemble_17c469b41bbbcdd4cd17 (ambient : Nat)
    (x0 : Tower.Head)
    (x1 : Tower.Head)
    (x2 : T RootCode ambient)
    (x3 : T RootCode (ambient + 1))
    (x4 : Tower.Tm (ambient + 1))
    (x5 : Tower.Tm (ambient + 2))
    (x6 : T RootCode (ambient + 1))
    (x7 : T RootCode (ambient + 1)) : T RootCode ambient :=
  .piForm (x0) (x1) (.sigmaForm (x1) (x1) (x2) (x3)) (.appElim (x4) (x5) (x6) (x7))

def assemble_26391316ca27450931a7 (ambient : Nat)
    (x0 : X RootCode ambient)
    (x1 : Tower.Head)
    (x2 : T RootCode ambient)
    (x3 : Tower.Head)
    (x4 : T RootCode (ambient + 1)) : X RootCode (ambient + 2) :=
  .snoc (.snoc (x0) (x1) (x2)) (x3) (x4)

def assemble_2d4461adb9d9d143309c (ambient : Nat)
    (x0 : Tower.Tm ambient)
    (x1 : Tower.Tm (ambient + 1))
    (x2 : Tower.Head)
    (x3 : T RootCode 0)
    (x4 : Tower.Head)
    (x5 : T RootCode ambient)
    (x6 : T RootCode (ambient + 1)) : T RootCode ambient :=
  .appElim (x0) (x1) (.const (x2) (x3)) (.lamIntro (x4) (x5) (x6))

def assemble_2e319dea3ae00cbdfc4c (ambient : Nat)
    (x0 : Tower.Head)
    (x1 : T RootCode ambient)
    (x2 : Tower.Head)
    (x3 : T RootCode (ambient + 1)) : T RootCode ambient :=
  .lamIntro (x0) (x1) (.cumul (x2) (x3))

def assemble_31719a6a14642750acdf (ambient : Nat)
    (x0 : Tower.Head)
    (x1 : T RootCode ambient)
    (x2 : Tower.Head)
    (x3 : Tower.Head)
    (x4 : T RootCode (ambient + 1))
    (x5 : T RootCode (ambient + 2)) : T RootCode ambient :=
  .lamIntro (x0) (x1) (.cumul (x2) (.sigmaForm (x3) (x3) (x4) (x5)))

def assemble_378c9b2c799750967bc0 (ambient : Nat)
    (x0 : Tower.Tm ambient)
    (x1 : Tower.Tm (ambient + 1))
    (x2 : Tower.Tm ambient)
    (x3 : Tower.Tm (ambient + 1))
    (x4 : T RootCode ambient)
    (x5 : T RootCode ambient)
    (x6 : Tower.Tm ambient)
    (x7 : Tower.Tm (ambient + 1))
    (x8 : T RootCode ambient)
    (x9 : T RootCode ambient) : T RootCode ambient :=
  .appElim (x0) (x1) (.appElim (x2) (x3) (x4) (x5)) (.appElim (x6) (x7) (x8) (x9))

def assemble_3d4333af0ad21e3b2bf8 (ambient : Nat)
    (x0 : Tower.Head)
    (x1 : T RootCode ambient)
    (x2 : Tower.Head)
    (x3 : T RootCode (ambient + 1))
    (x4 : Tower.Head)
    (x5 : T RootCode (ambient + 2))
    (x6 : T RootCode (ambient + 3)) : T RootCode ambient :=
  .lamIntro (x0) (x1) (.lamIntro (x2) (x3) (.lamIntro (x4) (x5) (x6)))

def assemble_45f2190696e076c4a4d3 (ambient : Nat)
    (x0 : Tower.Tm ambient)
    (x1 : Tower.Tm (ambient + 1))
    (x2 : T RootCode ambient)
    (x3 : Tower.Tm (ambient + 1))
    (x4 : T RootCode ambient)
    (x5 : T RootCode ambient) : T RootCode ambient :=
  .appElim (x0) (x1) (x2) (.appElim (x0) (x3) (x4) (x5))

def assemble_4815d32b20faf96e21c1 (ambient : Nat)
    (x0 : Tower.Head)
    (x1 : Tower.Head)
    (x2 : T RootCode ambient)
    (x3 : T RootCode (ambient + 1))
    (x4 : T RootCode (ambient + 2)) : T RootCode ambient :=
  .piForm (x0) (x1) (x2) (.piForm (x0) (x0) (x3) (x4))

def assemble_4b33c45d53a5e68e8f78 (ambient : Nat)
    (x0 : Tower.Head)
    (x1 : Tower.Head)
    (x2 : T RootCode ambient)
    (x3 : T RootCode (ambient + 1))
    (x4 : Tower.Tm (ambient + 2))
    (x5 : Tower.Tm (ambient + 3))
    (x6 : T RootCode (ambient + 2))
    (x7 : Tower.Tm (ambient + 3))
    (x8 : Tower.Tm (ambient + 2))
    (x9 : Tower.Tm (ambient + 3))
    (x10 : T RootCode (ambient + 2)) : T RootCode ambient :=
  .piForm (x0) (x1) (x2) (.piForm (x0) (x0) (x3) (.appElim (x4) (x5) (x6) (.appElim (x4) (x7) (.appElim (x8) (x9) (x10) (x6)) (x6))))

def assemble_4d5f04684bb1c9672070 (ambient : Nat)
    (x0 : Tower.Tm ambient)
    (x1 : Tower.Tm (ambient + 1))
    (x2 : Tower.Tm ambient)
    (x3 : Tower.Tm (ambient + 1))
    (x4 : T RootCode ambient)
    (x5 : T RootCode ambient) : T RootCode ambient :=
  .appElim (x0) (x1) (.appElim (x2) (x3) (x4) (x5)) (x5)

def assemble_59cd27e918c022ddb054 (ambient : Nat)
    (x0 : Tower.Head)
    (x1 : T RootCode ambient)
    (x2 : Tower.Tm (ambient + 1))
    (x3 : Tower.Tm (ambient + 2))
    (x4 : T RootCode (ambient + 1))
    (x5 : T RootCode (ambient + 1)) : T RootCode ambient :=
  .piForm (x0) (x0) (x1) (.appElim (x2) (x3) (x4) (x5))

def assemble_6562d93d6c87394cce14 (ambient : Nat)
    (x0 : Tower.Head)
    (x1 : Tower.Head)
    (x2 : T RootCode ambient)
    (x3 : T RootCode (ambient + 1)) : T RootCode ambient :=
  .cumul (x0) (.sigmaForm (x1) (x1) (x2) (x3))

def assemble_74d197e0f7817bd809e1 (ambient : Nat)
    (x0 : Tower.Head)
    (x1 : Tower.Head)
    (x2 : Tower.Tm ambient)
    (x3 : Tower.Tm (ambient + 1))
    (x4 : T RootCode ambient)
    (x5 : T RootCode ambient)
    (x6 : Tower.Head)
    (x7 : Tower.Head)
    (x8 : T RootCode (ambient + 1))
    (x9 : T RootCode (ambient + 2)) : T RootCode ambient :=
  .piForm (x0) (x1) (.appElim (x2) (x3) (x4) (x5)) (.piForm (x6) (x7) (x8) (x9))

def assemble_8704404f73c273f28b55 (ambient : Nat)
    (x0 : Tower.Head)
    (x1 : Tower.Head)
    (x2 : T RootCode ambient)
    (x3 : Tower.Head)
    (x4 : Tower.Head)
    (x5 : T RootCode (ambient + 1))
    (x6 : T RootCode (ambient + 2)) : T RootCode ambient :=
  .piForm (x0) (x1) (x2) (.piForm (x3) (x4) (x5) (x6))

def assemble_8db28e2c143426783158 (ambient : Nat)
    (x0 : Tower.Head)
    (x1 : Tower.Head)
    (x2 : T RootCode ambient)
    (x3 : Tower.Tm (ambient + 1))
    (x4 : Tower.Tm (ambient + 2))
    (x5 : Tower.Head)
    (x6 : Tower.Head)
    (x7 : T RootCode (ambient + 1))
    (x8 : T RootCode (ambient + 2))
    (x9 : T RootCode (ambient + 2)) : T RootCode ambient :=
  .cumul (x0) (.sigmaForm (x1) (x1) (x2) (.appElim (x3) (x4) (.lamIntro (x5) (.piForm (x1) (x6) (x7) (x8)) (x9)) (x7)))

def assemble_958149842244f9e10772 (ambient : Nat)
    (x0 : Tower.Head)
    (x1 : Tower.Head)
    (x2 : T RootCode ambient)
    (x3 : Tower.Head)
    (x4 : T RootCode (ambient + 1))
    (x5 : T RootCode (ambient + 2)) : T RootCode ambient :=
  .piForm (x0) (x1) (x2) (.piForm (x3) (x3) (x4) (x5))

def assemble_966b5ef0fda36d625109 (ambient : Nat)
    (x0 : Tower.Head)
    (x1 : Tower.Head)
    (x2 : Tower.Head)
    (x3 : T RootCode ambient)
    (x4 : T RootCode (ambient + 1))
    (x5 : T RootCode (ambient + 1)) : T RootCode ambient :=
  .piForm (x0) (x1) (.piForm (x2) (x2) (x3) (x4)) (x5)

def assemble_96c410b2c04018d2df28 (ambient : Nat)
    (x0 : Tower.Head)
    (x1 : Tower.Tm ambient)
    (x2 : Tower.Tm (ambient + 1))
    (x3 : T RootCode ambient)
    (x4 : T RootCode ambient)
    (x5 : T RootCode (ambient + 1)) : T RootCode ambient :=
  .piForm (x0) (x0) (.appElim (x1) (x2) (x3) (x4)) (x5)

def assemble_9ba4a5499b7761fa6764 (ambient : Nat)
    (x0 : Tower.Head)
    (x1 : Tower.Head)
    (x2 : Tower.Head)
    (x3 : T RootCode ambient)
    (x4 : T RootCode (ambient + 1))
    (x5 : T RootCode (ambient + 1)) : T RootCode ambient :=
  .lamIntro (x0) (.piForm (x1) (x2) (x3) (x4)) (x5)

def assemble_a01eeb0864f95e605a1b (ambient : Nat)
    (x0 : Tower.Head)
    (x1 : Tower.Head)
    (x2 : Tower.Head)
    (x3 : T RootCode ambient)
    (x4 : T RootCode (ambient + 1))
    (x5 : T RootCode (ambient + 2)) : T RootCode ambient :=
  .lamIntro (x0) (.piForm (x1) (x2) (x3) (x4)) (.lamIntro (x2) (x4) (x5))

def assemble_a73411227240aec8ed52 (ambient : Nat)
    (x0 : Tower.Head)
    (x1 : Tower.Head)
    (x2 : Tower.Head)
    (x3 : T RootCode ambient)
    (x4 : T RootCode (ambient + 1)) : T RootCode ambient :=
  .cumul (x0) (.sigmaForm (x1) (x2) (x3) (x4))

def assemble_a91180446b806f62c3ef (ambient : Nat)
    (x0 : Tower.Head)
    (x1 : Tower.Head)
    (x2 : Tower.Head)
    (x3 : T RootCode ambient)
    (x4 : T RootCode (ambient + 1))
    (x5 : T RootCode (ambient + 1)) : T RootCode ambient :=
  .piForm (x0) (x1) (.sigmaForm (x2) (x1) (x3) (x4)) (x5)

def assemble_a951cfdc4e886c32b0c9 (ambient : Nat)
    (x0 : Tower.Head)
    (x1 : T RootCode ambient)
    (x2 : Tower.Head)
    (x3 : T RootCode (ambient + 1))
    (x4 : T RootCode (ambient + 2)) : T RootCode ambient :=
  .lamIntro (x0) (x1) (.lamIntro (x2) (x3) (x4))

def assemble_abc997f471525f0ec2c2 (ambient : Nat)
    (x0 : Tower.Tm ambient)
    (x1 : Tower.Tm (ambient + 1))
    (x2 : Tower.Tm ambient)
    (x3 : Tower.Tm (ambient + 1))
    (x4 : T RootCode ambient)
    (x5 : T RootCode ambient)
    (x6 : T RootCode ambient) : T RootCode ambient :=
  .appElim (x0) (x1) (.appElim (x2) (x3) (x4) (x5)) (x6)

def assemble_ae4e86ba3e26a609c8e8 (ambient : Nat)
    (x0 : Tower.Tm ambient)
    (x1 : Tower.Tm (ambient + 1))
    (x2 : Tower.Tm ambient)
    (x3 : Tower.Head)
    (x4 : T RootCode ambient)
    (x5 : T RootCode ambient)
    (x6 : C RootCode ambient)
    (x7 : T RootCode ambient) : T RootCode ambient :=
  .appElim (x0) (x1) (.convert (x2) (x3) (x4) (x5) (x6)) (x7)

def assemble_bd03b1613e47bc49ec0e (ambient : Nat)
    (x0 : Tower.Tm ambient)
    (x1 : Tower.Tm (ambient + 1))
    (x2 : Tower.Head)
    (x3 : T RootCode 0)
    (x4 : T RootCode ambient) : T RootCode ambient :=
  .appElim (x0) (x1) (.const (x2) (x3)) (x4)

def assemble_c5746b0a816bb8bed278 (ambient : Nat)
    (x0 : Tower.Tm ambient)
    (x1 : Tower.Tm (ambient + 1))
    (x2 : Tower.Tm ambient)
    (x3 : Tower.Tm (ambient + 1))
    (x4 : T RootCode ambient) : T RootCode ambient :=
  .appElim (x0) (x1) (.appElim (x2) (x3) (x4) (x4)) (x4)

def assemble_cbd16c449718d7a707d4 (ambient : Nat)
    (x0 : Tower.Head)
    (x1 : Tower.Head)
    (x2 : Tower.Tm ambient)
    (x3 : Tower.Tm (ambient + 1))
    (x4 : T RootCode ambient)
    (x5 : T RootCode ambient)
    (x6 : T RootCode (ambient + 1)) : T RootCode ambient :=
  .piForm (x0) (x1) (.appElim (x2) (x3) (x4) (x5)) (x6)

def assemble_ccbda2594895a2260e59 (ambient : Nat)
    (x0 : Tower.Head)
    (x1 : T RootCode ambient)
    (x2 : T RootCode ambient) : T RootCode ambient :=
  .cumul (x0) (.idForm (x0) (x1) (x2) (x2))

def assemble_d01135a657f050a2df2d (ambient : Nat)
    (x0 : Tower.Head)
    (x1 : Tower.Head)
    (x2 : T RootCode ambient)
    (x3 : Tower.Head)
    (x4 : T RootCode (ambient + 1))
    (x5 : T RootCode (ambient + 2)) : T RootCode ambient :=
  .piForm (x0) (x1) (x2) (.piForm (x0) (x3) (x4) (x5))

def assemble_d03516a29f94fe310e7a (ambient : Nat)
    (x0 : Tower.Tm ambient)
    (x1 : Tower.Tm (ambient + 1))
    (x2 : Tower.Head)
    (x3 : Tower.Head)
    (x4 : Tower.Head)
    (x5 : T RootCode ambient)
    (x6 : T RootCode (ambient + 1))
    (x7 : T RootCode (ambient + 1)) : T RootCode ambient :=
  .appElim (x0) (x1) (.lamIntro (x2) (.piForm (x3) (x4) (x5) (x6)) (x7)) (x5)

end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorTypingContexts
