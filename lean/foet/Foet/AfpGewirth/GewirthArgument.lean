import Foet.AfpGewirth.ExtendedDDL

set_option autoImplicit false

namespace Foet
namespace AFP
namespace Gewirth

/-!
`GewirthArgument` (AFP session) introduces Gewirth-specific explications and
proves the PGC (weak and strong variants) in the shallow semantic embedding.

This is intended to closely mirror `GewirthPGCProof/GewirthArgument.thy`.

## Design note: `ldvalid` vs `modValid` (matches AFP)

Most explications are stated as *indexically valid* (`ldvalid`), reflecting Kaplan/LD
"a priori" validity. This includes `essentialPPA`, all `explicationGoodness*`, all
`explicationFWB*`, and `OIOAC`.

In the AFP sources, the interference explication is intentionally stated using the
*stronger* classical validity notion (`modValid`) rather than `ldvalid`, with an
explicit comment about prover/model-finder behavior if it is weakened to `ldvalid`.
We mirror that split here:

- `explicationInterference : ∀ φ, modValid ((∃b. InterferesWith b φ) ↔ ¬◇ₐ φ)`
- everything else: `ldvalid`.
-/

abbrev p : Type := e → m

/-! ### Agency -/

axiom ActsOnPurpose : e → m → m
axiom NeedsForPurpose : e → p → m → m

def PPA (a : e) : m :=
  ∃ₘ (fun E : m => ActsOnPurpose a E)

axiom essentialPPA : ⌊∀ₘ (fun a : e => PPA a →ₘ □ᴰ (PPA a))⌋ᴰ

/-! Named axiom content (object-language formulas) -/

def ax_essentialPPA : m :=
  ∀ₘ (fun a : e => PPA a →ₘ □ᴰ (PPA a))

theorem recognizeOtherPPA :
    ∀ c₁ c₂ : c, ⌊PPA (Agent c₂)⌋₍c₂₎ → ⌊PPA (Agent c₂)⌋₍c₁₎ := by
  intro c₁ c₂ hPPA
  have hEssAt : ⌊∀ₘ (fun a : e => (PPA a) →ₘ (□ᴰ (PPA a)))⌋₍c₂₎ :=
    essentialPPA c₂
  have hEss : ∀ a : e, ⌊PPA a⌋₍c₂₎ → ⌊PPA a⌋ᴰ := by
    simpa [ldtruectx, mforall, mimp, boxD] using hEssAt
  have hLd : ⌊PPA (Agent c₂)⌋ᴰ :=
    hEss (Agent c₂) hPPA
  exact hLd c₁

/-! ### Goodness -/

axiom Good : e → m → m

axiom explicationGoodness1 :
    ⌊∀ₘ (fun a : e => ∀ₘ (fun P : m => ActsOnPurpose a P →ₘ Good a P))⌋ᴰ

axiom explicationGoodness2 :
    ⌊∀ₘ (fun P : m =>
        ∀ₘ (fun M : p =>
          ∀ₘ (fun a : e =>
            (Good a P ∧ₘ NeedsForPurpose a M P) →ₘ Good a (M a))))⌋ᴰ

axiom explicationGoodness3 :
    ⌊∀ₘ (fun phi : m =>
        ∀ₘ (fun a : e =>
          (◇ₚ phi) →ₘ O⟨phi | □ᴰ (Good a phi)⟩))⌋ᴰ

def ax_Good1 : m :=
  ∀ₘ (fun a : e => ∀ₘ (fun P : m => ActsOnPurpose a P →ₘ Good a P))

def ax_Good2 : m :=
  ∀ₘ (fun P : m =>
    ∀ₘ (fun M : p =>
      ∀ₘ (fun a : e =>
        (Good a P ∧ₘ NeedsForPurpose a M P) →ₘ Good a (M a))))

def ax_Good3 : m :=
  ∀ₘ (fun phi : m =>
    ∀ₘ (fun a : e => (◇ₚ phi) →ₘ O⟨phi | □ᴰ (Good a phi)⟩))

/-! ### Freedom and well-being -/

axiom FWB : p

axiom explicationFWB1 :
    ⌊∀ₘ (fun P : m => ∀ₘ (fun a : e => NeedsForPurpose a FWB P))⌋ᴰ

axiom explicationFWB2 :
    ⌊∀ₘ (fun a : e => ◇ₚ (FWB a))⌋ᴰ

axiom explicationFWB3 :
    ⌊∀ₘ (fun a : e => ◇ₚ (¬ₘ (FWB a)))⌋ᴰ

def ax_FWB1 : m :=
  ∀ₘ (fun P : m => ∀ₘ (fun a : e => NeedsForPurpose a FWB P))

def ax_FWB2 : m :=
  ∀ₘ (fun a : e => ◇ₚ (FWB a))

def ax_FWB3 : m :=
  ∀ₘ (fun a : e => ◇ₚ (¬ₘ (FWB a)))

/-! ### Obligation, interference, and rights -/

axiom OIOAC : ∀ φ : m, ⌊(Oᵢ φ) →ₘ (Oᵢ (◇ₐ φ))⌋ᴰ

def ax_OIOAC (φ : m) : m :=
  (Oᵢ φ) →ₘ (Oᵢ (◇ₐ φ))

axiom InterferesWith : e → m → m

axiom explicationInterference :
    ∀ φ : m, ⌊(∃ₘ (fun b : e => InterferesWith b φ)) ↔ₘ (¬ₘ (◇ₐ φ))⌋

def ax_Interference (φ : m) : m :=
  (∃ₘ (fun b : e => InterferesWith b φ)) ↔ₘ (¬ₘ (◇ₐ φ))

theorem InterferenceWithFWB :
    ⌊∀ₘ (fun a : e =>
        (◇ₐ (FWB a)) ↔ₘ (∀ₘ (fun b : e => ¬ₘ (InterferesWith b (FWB a)))))⌋ := by
  classical
  intro ctx w0 a
  have hInterf :
      (∃ₘ (fun b : e => InterferesWith b (FWB a)) ctx w0) ↔ ¬ ◇ₐ (FWB a) ctx w0 := by
    simpa [miff, mnot, mexists] using (explicationInterference (FWB a) ctx w0)
  constructor
  · intro hDia
    have : ¬ (∃ b : e, InterferesWith b (FWB a) ctx w0) := by
      intro hex
      exact (hInterf.mp hex) hDia
    simpa [mforall, mnot, mexists, not_exists] using this
  · intro hNoInterf
    have hNoEx : ¬ (∃ b : e, InterferesWith b (FWB a) ctx w0) := by
      simpa [mforall, mnot, mexists, not_exists] using hNoInterf
    have hNN : ¬ ¬ diaa (FWB a) ctx w0 := by
      intro hNotDia
      have hex : ∃ b : e, InterferesWith b (FWB a) ctx w0 :=
        hInterf.mpr hNotDia
      exact hNoEx hex
    exact Classical.not_not.mp hNN

def RightTo (a : e) (φ : p) : m :=
  Oᵢ (∀ₘ (fun b : e => ¬ₘ (InterferesWith b (φ a))))

/-! ### A congruence lemma for `Oᵢ` (needed to rewrite via `InterferenceWithFWB`) -/

theorem Oi_congr (ctx : c) (w0 : w) (φ ψ : m)
    (h : ∀ v, pv w0 v → (φ ctx v ↔ ψ ctx v)) :
    Oi φ ctx w0 ↔ Oi ψ ctx w0 := by
  classical
  have hInter : setEq (inter (pv w0) (φ ctx)) (inter (pv w0) (ψ ctx)) := by
    intro v
    by_cases hv : pv w0 v
    · have hEq := h v hv
      simp [inter, hv, hEq]
    · simp [inter, hv]
  constructor
  · intro hOi
    rcases hOi with ⟨hOb, ⟨v, hv, hNotφ⟩⟩
    have hOb' : ob (pv w0) (ψ ctx) := (sem_5b (pv w0) (φ ctx) (ψ ctx) hInter).1 hOb
    have hNotψ : ¬ ψ ctx v := by
      have hEq := h v hv
      exact (not_congr hEq).1 hNotφ
    exact ⟨hOb', ⟨v, hv, hNotψ⟩⟩
  · intro hOi
    rcases hOi with ⟨hOb, ⟨v, hv, hNotψ⟩⟩
    have hInter' : setEq (inter (pv w0) (ψ ctx)) (inter (pv w0) (φ ctx)) := by
      intro v
      exact (hInter v).symm
    have hOb' : ob (pv w0) (φ ctx) := (sem_5b (pv w0) (ψ ctx) (φ ctx) hInter').1 hOb
    have hNotφ : ¬ φ ctx v := by
      have hEq := h v hv
      exact (not_congr hEq).2 hNotψ
    exact ⟨hOb', ⟨v, hv, hNotφ⟩⟩

/-! ### The PGC proofs -/

theorem RightTo_of_ActsOnPurpose (C : c) (I : e) (E : m) :
    ⌊ActsOnPurpose I E⌋₍C₎ → ⌊RightTo I FWB⌋₍C₎ := by
  classical
  intro hActs

  have hPPA : ⌊PPA I⌋₍C₎ := by
    refine ⟨E, ?_⟩
    exact hActs

  have hGoodE : ⌊Good I E⌋₍C₎ := by
    have hAx : ⌊∀ₘ (fun a : e => ∀ₘ (fun P : m => ActsOnPurpose a P →ₘ Good a P))⌋₍C₎ :=
      explicationGoodness1 C
    have hAx' : ∀ a : e, ∀ P : m, ActsOnPurpose a P C (World C) → Good a P C (World C) := by
      simpa [ldtruectx, mforall, mimp] using hAx
    exact hAx' I E hActs

  have hNeedsAll : ⌊∀ₘ (fun P : m => NeedsForPurpose I FWB P)⌋ᴰ := by
    intro ctx
    have hAx : ⌊∀ₘ (fun P : m => ∀ₘ (fun a : e => NeedsForPurpose a FWB P))⌋₍ctx₎ :=
      explicationFWB1 ctx
    have hAx' : ∀ P : m, ∀ a : e, NeedsForPurpose a FWB P ctx (World ctx) := by
      simpa [ldtruectx, mforall] using hAx
    have : ∀ P : m, NeedsForPurpose I FWB P ctx (World ctx) := fun P => hAx' P I
    simpa [ldtruectx, mforall] using this

  have hDiapFWB : ◇ₚ (FWB I) C (World C) := by
    have hAx : ⌊∀ₘ (fun a : e => ◇ₚ (FWB a))⌋₍C₎ :=
      explicationFWB2 C
    have hAx' : ∀ a : e, diap (FWB a) C (World C) := by
      simpa [ldtruectx, mforall] using hAx
    exact hAx' I

  have hOcondFWB : O⟨FWB I | □ᴰ (Good I (FWB I))⟩ C (World C) := by
    have hAx : ⌊∀ₘ (fun phi : m => ∀ₘ (fun a : e => (◇ₚ phi) →ₘ O⟨phi | □ᴰ (Good a phi)⟩))⌋₍C₎ :=
      explicationGoodness3 C
    have hAx' :
        ∀ φ : m, ∀ a : e,
          (diap φ C (World C) → Ocond φ (boxD (Good a φ)) C (World C)) := by
      simpa [ldtruectx, mforall, mimp] using hAx
    exact hAx' (FWB I) I hDiapFWB

  have hLdGoodFWB : ⌊Good I (FWB I)⌋ᴰ := by
    have hOb : ob (boxD (Good I (FWB I)) C) ((FWB I) C) := by
      simpa [Ocond] using hOcondFWB
    have hInst : instantiated (inter (boxD (Good I (FWB I)) C) ((FWB I) C)) :=
      sem_5ab (X := boxD (Good I (FWB I)) C) (Y := (FWB I) C) hOb
    rcases hInst with ⟨v, hv⟩
    exact hv.1

  have hExistsGoodNeeds : ∃ P : m, ⌊(Good I P) ∧ₘ (NeedsForPurpose I FWB P)⌋ᴰ := by
    refine ⟨FWB I, ?_⟩
    have hNeeds : ⌊NeedsForPurpose I FWB (FWB I)⌋ᴰ := by
      intro ctx
      have hAll : ∀ P : m, NeedsForPurpose I FWB P ctx (World ctx) := by
        simpa [ldtruectx, mforall] using hNeedsAll ctx
      exact hAll (FWB I)
    intro ctx
    have hGood : ⌊Good I (FWB I)⌋₍ctx₎ := hLdGoodFWB ctx
    have hNeed : ⌊NeedsForPurpose I FWB (FWB I)⌋₍ctx₎ := hNeeds ctx
    exact And.intro hGood hNeed

  have hLdGoodFWB' : ⌊Good I (FWB I)⌋ᴰ := by
    rcases hExistsGoodNeeds with ⟨P, hP⟩
    intro ctx
    have hAx : ⌊∀ₘ (fun P0 : m =>
          ∀ₘ (fun M0 : p =>
            ∀ₘ (fun a0 : e =>
              ((Good a0 P0) ∧ₘ (NeedsForPurpose a0 M0 P0)) →ₘ (Good a0 (M0 a0)))))⌋₍ctx₎ :=
      explicationGoodness2 ctx
    have hAx' :
        ∀ P0 : m, ∀ M0 : p, ∀ a0 : e,
          (mand (Good a0 P0) (NeedsForPurpose a0 M0 P0) ctx (World ctx)) →
            Good a0 (M0 a0) ctx (World ctx) := by
      simpa [ldtruectx, mforall, mimp] using hAx
    have hPrem : mand (Good I P) (NeedsForPurpose I FWB P) ctx (World ctx) := by
      simpa [ldtruectx, mand] using hP ctx
    exact hAx' P FWB I hPrem

  have hBoxA : boxp (boxD (Good I (FWB I))) C (World C) := by
    intro v hv
    simpa [boxD] using hLdGoodFWB'

  have hDiapNotFWB : ◇ₚ (¬ₘ (FWB I)) C (World C) := by
    have hAx : ⌊∀ₘ (fun a : e => ◇ₚ (¬ₘ (FWB a)))⌋₍C₎ :=
      explicationFWB3 C
    have hAx' : ∀ a : e, ◇ₚ (¬ₘ (FWB a)) C (World C) := by
      simpa [ldtruectx, mforall] using hAx
    exact hAx' I

  have hOiFWB : Oi (FWB I) C (World C) := by
    have hCJ := (CJ_14p (A := boxD (Good I (FWB I))) (B := FWB I)) C (World C)
    apply hCJ
    refine ⟨hOcondFWB, hBoxA, hDiapFWB, ?_⟩
    -- `CJ_14p` expects `diap (¬B)`; our `mnot` is `¬` (definitionally).
    exact hDiapNotFWB

  have hOiDiaFWB : Oᵢ (◇ₐ (FWB I)) C (World C) := by
    have hAx : ⌊(Oᵢ (FWB I)) →ₘ (Oᵢ (◇ₐ (FWB I)))⌋₍C₎ :=
      (OIOAC (FWB I)) C
    have hImp : Oi (FWB I) C (World C) → Oi (diaa (FWB I)) C (World C) := by
      simpa [ldtruectx, mimp] using hAx
    exact hImp hOiFWB

  have hEq : ∀ v, pv (World C) v →
      (diaa (FWB I) C v ↔ (mforall (fun a : e => mnot (InterferesWith a (FWB I)))) C v) := by
    intro v hv
    have hAll : ∀ a : e,
        diaa (FWB a) C v ↔ (mforall (fun b : e => mnot (InterferesWith b (FWB a)))) C v := by
      simpa [mforall, miff] using (InterferenceWithFWB C v)
    exact hAll I

  have hOiNonInterf :
      Oᵢ (∀ₘ (fun a : e => ¬ₘ (InterferesWith a (FWB I)))) C (World C) := by
    have hCong := (Oi_congr C (World C) (diaa (FWB I))
      (mforall (fun a : e => mnot (InterferesWith a (FWB I)))) hEq).1 hOiDiaFWB
    exact hCong

  -- Finally: RightTo I FWB holds by definition.
  simpa [RightTo, ldtruectx] using hOiNonInterf

theorem RightTo_of_PPA (C : c) (I : e) :
    ⌊PPA I⌋₍C₎ → ⌊RightTo I FWB⌋₍C₎ := by
  intro hPPA
  rcases hPPA with ⟨E, hE⟩
  exact RightTo_of_ActsOnPurpose C I E hE

theorem PGC_weak :
    ∀ C : c, ⌊(PPA (Agent C)) →ₘ (RightTo (Agent C) FWB)⌋₍C₎ := by
  intro C
  have h : PPA (Agent C) C (World C) → RightTo (Agent C) FWB C (World C) := by
    intro hPPA
    exact RightTo_of_PPA C (Agent C) hPPA
  simpa [ldtruectx, mimp] using h

theorem PGC_strong : ⌊∀ₘ (fun x : e => (PPA x) →ₘ (RightTo x FWB))⌋ᴰ := by
  intro C
  have : ∀ x : e, PPA x C (World C) → RightTo x FWB C (World C) := by
    intro x hPPA
    exact RightTo_of_PPA C x hPPA
  simpa [ldtruectx, mforall, mimp] using this

def φPGC_strong : m :=
  ∀ₘ (fun x : e => (PPA x) →ₘ (RightTo x FWB))

theorem PGC_strong_ldvalid : ⌊φPGC_strong⌋ᴰ := by
  simpa [φPGC_strong] using PGC_strong

theorem PGC_weak2 :
    ∀ C : c, ⌊(PPA (Agent C)) →ₘ (RightTo (Agent C) FWB)⌋₍C₎ := by
  intro C
  have hStrong : ⌊∀ₘ (fun x : e => (PPA x) →ₘ (RightTo x FWB))⌋₍C₎ :=
    PGC_strong C
  have hAll : ∀ x : e, PPA x C (World C) → RightTo x FWB C (World C) := by
    simpa [ldtruectx, mforall, mimp] using hStrong
  have h := hAll (Agent C)
  simpa [ldtruectx, mimp] using h

end Gewirth
end AFP
end Foet
