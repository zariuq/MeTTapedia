import Mettapedia.Languages.GF.GFCoreNTTDiagnostics
import Mettapedia.OSLF.Framework.DerivedTyping
import Mettapedia.OSLF.Framework.ConstructorFibration
import Mettapedia.OSLF.NativeType.Construction

/-!
# GF Typing Actions + Change-of-Base + Fiber Instantiation

This module extends the real GFCore NTT diagnostics with:

1. **Typing-action classification**: UseN and PassV2 are classified as **neutral**
   (neither domain nor codomain is the process sort "S"), mirroring the
   TinyML pattern from `TinyMLInstance.lean`.

2. **Change-of-base adjunctions**: the adjoint triples `∃f ⊣ f* ⊣ ∀f`
   for UseN and PassV2 morphisms, with concrete semantic content.

3. **Diamond-pullback interaction**: connects OSLF ◇ with the constructor
   fibration change-of-base.

4. **Grothendieck instantiation**: `ConstructorNatType` and `ConstructorNatTypeHom`
   for GF with nontrivial linguistic predicates.

## Why UseN/PassV2 are neutral

In the ρ-calculus, NQuote : Proc → Name introduces ◇ because its domain IS
the process sort. In GF, UseN : N → CN and PassV2 : V2 → VP are between
non-process sorts (the GF process sort is "S" where reduction happens).
This means their typing action is identity — they don't introduce new
modalities. The depth comes from the change-of-base adjunctions and
the fiber-level Grothendieck construction instead.

## References

- TinyMLInstance.lean (lines 294-325): pattern for classifyArrow + typingAction
- ConstructorFibration.lean (lines 99-106, 180-198): change-of-base + rho examples
- NativeType/Construction.lean (lines 269-360): ConstructorNatType machinery
-/

namespace Mettapedia.Languages.GF.GFCoreTypingActions

open Mettapedia.Languages.GF.GFCoreNTTDiagnostics
open Mettapedia.Languages.GF.GeneratedBridgeConformance
open Mettapedia.Languages.GF.GFCoreOSLFBridge
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.Framework.ConstructorCategory
open Mettapedia.OSLF.Framework.ConstructorFibration
open Mettapedia.OSLF.Framework.DerivedTyping
open Mettapedia.OSLF.Framework.TypeSynthesis
open Mettapedia.OSLF.NativeType
open Mettapedia.OSLF.MeTTaIL.Engine
open CategoryTheory

-- ═══════════════════════════════════════════════════════════════════
-- Section 1: Typing-Action Classification
-- ═══════════════════════════════════════════════════════════════════

/-- UseN is classified as **neutral** (domain=N, codomain=CN, procSort="S").
    Neither N nor CN is the process sort, so UseN introduces no modality.

    Contrast with ρ-calculus: NQuote (Proc→Name) is quoting because domain=Proc.
    Contrast with TinyML: Thunk (Expr→Val) is quoting because domain=Expr. -/
theorem useN_is_neutral :
    classifyArrow paperLangKR "S" useNArrow = .neutral := by
  simp [classifyArrow, paperNSort]
  decide

/-- PassV2 is classified as **neutral** (domain=V2, codomain=VP, procSort="S").
    Neither V2 nor VP is the process sort. -/
theorem passV2_is_neutral :
    classifyArrow paperLangKR "S" passV2Arrow = .neutral := by
  simp [classifyArrow, paperV2Sort]
  decide

/-- UseN typing action = identity (neutral arrows don't introduce modalities).

    When `n : (N, φ)`, the typing rule gives `UseN(n) : (CN, φ)` — same
    predicate, no ◇ or □ wrapping. -/
theorem useN_action_eq_id (φ : Pattern → Prop) :
    typingAction paperLangKR "S" useNArrow φ = φ := by
  simp [typingAction, useN_is_neutral, roleAction]

/-- PassV2 typing action = identity (neutral). -/
theorem passV2_action_eq_id (φ : Pattern → Prop) :
    typingAction paperLangKR "S" passV2Arrow φ = φ := by
  simp [typingAction, passV2_is_neutral, roleAction]

-- ═══════════════════════════════════════════════════════════════════
-- Section 2: Change-of-Base Adjunctions
-- ═══════════════════════════════════════════════════════════════════

/-- `∃_UseN ⊣ UseN*`: direct image is left adjoint to pullback along UseN. -/
theorem useN_di_pb_adj :
    GaloisConnection
      (constructorDirectImage paperLangKR useNMor)
      (constructorPullback paperLangKR useNMor) :=
  constructorDiPbAdj paperLangKR useNMor

/-- `UseN* ⊣ ∀_UseN`: pullback is left adjoint to universal image along UseN. -/
theorem useN_pb_ui_adj :
    GaloisConnection
      (constructorPullback paperLangKR useNMor)
      (constructorUniversalImage paperLangKR useNMor) :=
  constructorPbUiAdj paperLangKR useNMor

/-- `∃_PassV2 ⊣ PassV2*`. -/
theorem passV2_di_pb_adj :
    GaloisConnection
      (constructorDirectImage paperLangKR passV2Mor)
      (constructorPullback paperLangKR passV2Mor) :=
  constructorDiPbAdj paperLangKR passV2Mor

/-- `PassV2* ⊣ ∀_PassV2`. -/
theorem passV2_pb_ui_adj :
    GaloisConnection
      (constructorPullback paperLangKR passV2Mor)
      (constructorUniversalImage paperLangKR passV2Mor) :=
  constructorPbUiAdj paperLangKR passV2Mor

-- ═══════════════════════════════════════════════════════════════════
-- Section 3: Concrete Semantic Content
-- ═══════════════════════════════════════════════════════════════════

/-- UseN pullback: pull CN predicates back to N.
    `UseN*(φ)(p) = φ(.apply "UseN" [p])` -/
theorem useN_pullback_sem (φ : Pattern → Prop) (p : Pattern) :
    constructorPullback paperLangKR useNMor φ p =
    φ (.apply "UseN" [p]) := rfl

/-- PassV2 pullback: pull VP predicates back to V2.
    `PassV2*(φ)(p) = φ(.apply "PassV2" [p])` -/
theorem passV2_pullback_sem (φ : Pattern → Prop) (p : Pattern) :
    constructorPullback paperLangKR passV2Mor φ p =
    φ (.apply "PassV2" [p]) := rfl

/-- UseN direct image: push N predicates forward to CN.
    `∃UseN(ψ)(q) = ∃ p, .apply "UseN" [p] = q ∧ ψ p` -/
theorem useN_directImage_sem (ψ : Pattern → Prop) (q : Pattern) :
    constructorDirectImage paperLangKR useNMor ψ q =
    (∃ p, Pattern.apply "UseN" [p] = q ∧ ψ p) := rfl

/-- PassV2 direct image: push V2 predicates forward to VP.
    `∃PassV2(ψ)(q) = ∃ p, .apply "PassV2" [p] = q ∧ ψ p` -/
theorem passV2_directImage_sem (ψ : Pattern → Prop) (q : Pattern) :
    constructorDirectImage paperLangKR passV2Mor ψ q =
    (∃ p, Pattern.apply "PassV2" [p] = q ∧ ψ p) := rfl

/-- UseN universal image: push N predicates forward universally.
    `∀UseN(ψ)(q) = ∀ p, .apply "UseN" [p] = q → ψ p` -/
theorem useN_universalImage_sem (ψ : Pattern → Prop) (q : Pattern) :
    constructorUniversalImage paperLangKR useNMor ψ q =
    (∀ p, Pattern.apply "UseN" [p] = q → ψ p) := rfl

-- ═══════════════════════════════════════════════════════════════════
-- Section 4: Diamond-Pullback Interaction
-- ═══════════════════════════════════════════════════════════════════

/-- Key NTT theorem: ◇ distributes over UseN pullback.

    `langDiamond paperLangKR (UseN*(φ)) p` means "p can reduce to some q
    such that φ(UseN(q))".

    This connects the OSLF modal operator with the constructor fibration
    change-of-base: modal reachability at the N fiber factors through
    the UseN constructor crossing to the CN fiber. -/
theorem useN_diamond_pullback_spec (φ : Pattern → Prop) (p : Pattern) :
    langDiamond paperLangKR (constructorPullback paperLangKR useNMor φ) p ↔
    ∃ q, langReduces paperLangKR p q ∧ φ (.apply "UseN" [q]) := by
  constructor
  · intro h
    rw [langDiamond_spec] at h
    obtain ⟨q, hred, hphi⟩ := h
    exact ⟨q, hred, hphi⟩
  · intro ⟨q, hred, hphi⟩
    rw [langDiamond_spec]
    exact ⟨q, hred, hphi⟩

/-- Analogous for PassV2. -/
theorem passV2_diamond_pullback_spec (φ : Pattern → Prop) (p : Pattern) :
    langDiamond paperLangKR (constructorPullback paperLangKR passV2Mor φ) p ↔
    ∃ q, langReduces paperLangKR p q ∧ φ (.apply "PassV2" [q]) := by
  constructor
  · intro h
    rw [langDiamond_spec] at h
    obtain ⟨q, hred, hphi⟩ := h
    exact ⟨q, hred, hphi⟩
  · intro ⟨q, hred, hphi⟩
    rw [langDiamond_spec]
    exact ⟨q, hred, hphi⟩

-- ═══════════════════════════════════════════════════════════════════
-- Section 5: Grothendieck Instantiation with Nontrivial Predicates
-- ═══════════════════════════════════════════════════════════════════

/-- Native type at N sort: the concrete man_N predicate.
    Positive example: this is a linguistically meaningful predicate,
    not just ⊤. -/
def gf_N_manPred : ConstructorNatType paperLangKR where
  sort := ConstructorObj.mk paperNSort
  pred := fun p => p = .apply "man_N" []

/-- Native type at CN sort: the UseN-image predicate.
    All patterns that are in the image of UseN. -/
def gf_CN_useNImage : ConstructorNatType paperLangKR where
  sort := ConstructorObj.mk paperCNSort
  pred := fun p => ∃ n, p = .apply "UseN" [n]

/-- Grothendieck morphism from N (man_N) to CN (UseN-image) via UseN.

    The `predLe` obligation is: `(fun p => p = man_N) ≤ UseN*(∃ n, · = UseN(n))`.
    Unfolding: for all p, if p = man_N, then ∃ n, UseN(p) = UseN(n).
    Take n := p. -/
def gf_useN_manToImage_hom :
    ConstructorNatTypeHom paperLangKR gf_N_manPred gf_CN_useNImage where
  sortMap := useNMor
  predLe := by
    intro p hp
    show ∃ n, Pattern.apply "UseN" [p] = Pattern.apply "UseN" [n]
    exact ⟨p, rfl⟩

/-- Top-typed native type at N sort (for comparison). -/
def gf_N_top : ConstructorNatType paperLangKR where
  sort := ConstructorObj.mk paperNSort
  pred := fun _ => True

/-- Top-typed native type at CN sort (for comparison). -/
def gf_CN_top : ConstructorNatType paperLangKR where
  sort := ConstructorObj.mk paperCNSort
  pred := fun _ => True

/-- UseN morphism at the top level (trivial predLe). -/
def gf_useN_top_hom :
    ConstructorNatTypeHom paperLangKR gf_N_top gf_CN_top where
  sortMap := useNMor
  predLe := by
    intro _ _
    trivial

/-- Top-typed native type at V2 sort. -/
def gf_V2_top : ConstructorNatType paperLangKR where
  sort := ConstructorObj.mk paperV2Sort
  pred := fun _ => True

/-- Top-typed native type at VP sort. -/
def gf_VP_top : ConstructorNatType paperLangKR where
  sort := ConstructorObj.mk paperVPSort
  pred := fun _ => True

/-- PassV2 morphism at top level. -/
def gf_passV2_top_hom :
    ConstructorNatTypeHom paperLangKR gf_V2_top gf_VP_top where
  sortMap := passV2Mor
  predLe := by
    intro _ _
    trivial

/-- Identity morphism for the man_N native type (sanity check). -/
def gf_N_manPred_id :
    ConstructorNatTypeHom paperLangKR gf_N_manPred gf_N_manPred :=
  ConstructorNatTypeHom.id paperLangKR gf_N_manPred

/-- Weakening morphism: UseN-image → top at CN.
    Any pattern in the UseN-image is trivially in ⊤. -/
def gf_useNImage_to_top :
    ConstructorNatTypeHom paperLangKR gf_CN_useNImage gf_CN_top where
  sortMap := SortPath.nil
  predLe := by
    intro _ _
    show gf_CN_top.pred _
    trivial

/-- Composition: man_N → UseN-image → top at CN.
    Demonstrates that the Grothendieck composition works on GF types. -/
def gf_manToImage_top_comp :
    ConstructorNatTypeHom paperLangKR gf_N_manPred gf_CN_top :=
  ConstructorNatTypeHom.comp paperLangKR gf_useN_manToImage_hom gf_useNImage_to_top

-- ═══════════════════════════════════════════════════════════════════
-- Section 6: Concrete witnesses connecting GF linguistics to NTT
-- ═══════════════════════════════════════════════════════════════════

/-- man_N satisfies the N-sort man predicate (trivial witness). -/
theorem manN_in_N_manPred : gf_N_manPred.pred manPattern := rfl

/-- UseN(man_N) satisfies the CN-sort UseN-image predicate. -/
theorem useNManN_in_CN_useNImage : gf_CN_useNImage.pred useNManPattern :=
  ⟨manPattern, rfl⟩

/-- The predicate "is man_N" is preserved under UseN pullback:
    UseN*(λq. ∃n, q = UseN(n))(man_N) holds. -/
theorem manN_satisfies_useN_pullback :
    constructorPullback paperLangKR useNMor gf_CN_useNImage.pred manPattern :=
  ⟨manPattern, rfl⟩

/-- The full ChangeOfBase instance for GF's constructor fibration. -/
noncomputable def gfConstructorChangeOfBase :
    Mettapedia.GSLT.Core.ChangeOfBase (constructorFibration paperLangKR) :=
  constructorChangeOfBase paperLangKR

-- ═══════════════════════════════════════════════════════════════════
-- Section 7: EmbedS — The Quoting Arrow (◇)
--
-- This is the deep NTT result: EmbedS : S → SC is a genuine quoting
-- arrow whose domain IS the process sort. The typing action is ◇.
--
-- Linguistically: EmbedS takes a live, reducible sentence and freezes
-- it as a sentential complement (quotation). ◇ says: the SC contains
-- something that COULD reduce before it was quoted.
--
-- This is de re/de dicto in modal logic:
-- - de re (◇): the referent could change (the sentence can reduce)
-- - de dicto: the description is fixed (the SC is a snapshot)
--
-- Council: Meredith, Stay, Martin-Löf, Pfenning, de Paiva
-- ═══════════════════════════════════════════════════════════════════

def paperSCSort : LangSort paperLangKR :=
  LangSort.mk' paperLangKR "SC" (by decide)

/-- EmbedS : S → SC is a unary constructor-category crossing. -/
theorem embedS_crossing :
    ("EmbedS", "S", "SC") ∈ unaryCrossings paperLangKR := by
  decide

/-- The EmbedS sort arrow from S to SC. -/
def embedSArrow : SortArrow paperLangKR paperSSort paperSCSort :=
  ⟨"EmbedS", embedS_crossing⟩

/-- The EmbedS morphism in the constructor category. -/
def embedSMor : ConstructorObj.mk paperSSort ⟶ ConstructorObj.mk paperSCSort :=
  embedSArrow.toPath

/-- **Key NTT theorem**: EmbedS is classified as **quoting** because its
    domain IS the process sort "S".

    In the ρ-calculus, NQuote : Proc → Name is quoting.
    In TinyML, Thunk : Expr → Val is quoting.
    In GF, EmbedS : S → SC is quoting.

    All three take the "live" sort (where reduction happens) and embed it
    into a "frozen" sort (where the content is quoted). -/
theorem embedS_is_quoting :
    classifyArrow paperLangKR "S" embedSArrow = .quoting := by
  simp [classifyArrow, paperSSort]
  decide

/-- **The deep result**: EmbedS typing action = ◇ (diamond).

    When `s : (S, φ)`, the typing rule gives `EmbedS(s) : (SC, ◇φ)`.

    Meaning: if a sentence satisfies predicate φ, then its sentential
    complement (quotation) satisfies "possibly φ" — the quoted sentence
    could reduce to something satisfying φ.

    This recovers the de re reading: "the fact that John sees Anna"
    carries the diamond modality because the embedded sentence could
    reduce (e.g., via active→passive: "the fact that Anna is seen by John"). -/
theorem embedS_action_eq_diamond (φ : Pattern → Prop) :
    typingAction paperLangKR "S" embedSArrow φ = langDiamond paperLangKR φ := by
  simp [typingAction, embedS_is_quoting, roleAction]

-- ═══════════════════════════════════════════════════════════════════
-- Section 8: Concrete embedding witnesses
-- ═══════════════════════════════════════════════════════════════════

/-- EmbedS pullback: pull SC predicates back to S.
    `EmbedS*(φ)(s) = φ(.apply "EmbedS" [s])` -/
theorem embedS_pullback_sem (φ : Pattern → Prop) (s : Pattern) :
    constructorPullback paperLangKR embedSMor φ s =
    φ (.apply "EmbedS" [s]) := rfl

/-- EmbedS direct image: push S predicates forward to SC.
    `∃EmbedS(ψ)(q) = ∃ s, .apply "EmbedS" [s] = q ∧ ψ s` -/
theorem embedS_directImage_sem (ψ : Pattern → Prop) (q : Pattern) :
    constructorDirectImage paperLangKR embedSMor ψ q =
    (∃ s, Pattern.apply "EmbedS" [s] = q ∧ ψ s) := rfl

/-- `∃_EmbedS ⊣ EmbedS*` adjunction. -/
theorem embedS_di_pb_adj :
    GaloisConnection
      (constructorDirectImage paperLangKR embedSMor)
      (constructorPullback paperLangKR embedSMor) :=
  constructorDiPbAdj paperLangKR embedSMor

/-- `EmbedS* ⊣ ∀_EmbedS` adjunction. -/
theorem embedS_pb_ui_adj :
    GaloisConnection
      (constructorPullback paperLangKR embedSMor)
      (constructorUniversalImage paperLangKR embedSMor) :=
  constructorPbUiAdj paperLangKR embedSMor

/-- Concrete: embedding a present-tense sentence produces a reducible SC.
    The embedded sentence `EmbedS(UseCl(TPres, PPos, cl))` can reduce to
    `⊛embedded(cl)` — the bare propositional content with tense stripped. -/
def embeddedActivePattern : Pattern :=
  Pattern.apply "⊛embedded" [activeClausePattern]

def embedSPresentPattern : Pattern :=
  Pattern.apply "EmbedS" [presentSentencePattern]

-- Compiled-code regression: EmbedS reduction fires
#eval do
  let ok := embeddedActivePattern ∈
    rewriteWithContextWithPremises paperLangKR embedSPresentPattern
  if ok then IO.println "PASS: EmbedS(present) reduces to ⊛embedded(clause)"
  else IO.println "FAIL: EmbedS(present) reduction"

/-- Diamond-pullback factoring for EmbedS: "can the quotation reduce?"
    factors through the quoting arrow's change-of-base. -/
theorem embedS_diamond_pullback_spec (φ : Pattern → Prop) (s : Pattern) :
    langDiamond paperLangKR (constructorPullback paperLangKR embedSMor φ) s ↔
    ∃ q, langReduces paperLangKR s q ∧ φ (.apply "EmbedS" [q]) := by
  constructor
  · intro h
    rw [langDiamond_spec] at h
    obtain ⟨q, hred, hphi⟩ := h
    exact ⟨q, hred, hphi⟩
  · intro ⟨q, hred, hphi⟩
    rw [langDiamond_spec]
    exact ⟨q, hred, hphi⟩

end Mettapedia.Languages.GF.GFCoreTypingActions
