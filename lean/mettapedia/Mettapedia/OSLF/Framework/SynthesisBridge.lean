import Mettapedia.OSLF.Framework.GeneratedTyping
import Mettapedia.OSLF.Framework.InterpretedTypeSynthesis
import Mettapedia.OSLF.Framework.RhoInstance
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Soundness
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Engine
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefAdequacy
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedContextualStep

/-!
# Synthesis Bridge: Generated ↔ Hand-Written Type Systems

This file bridges four layers of the OSLF formalization:

1. **Hand-written** (Reduction.lean, Soundness.lean):
   - `Reduces : Pattern → Pattern → Type` (propositional)
   - `possiblyProp` / `relyProp` (hand-written modalities)
   - `HasType` (hand-written typing judgment)

2. **Derived abstract** (DerivedModalities.lean, RhoInstance.lean):
   - `rhoSpan` → `derivedDiamond` / `derivedBox`
   - Proven equal to `possiblyProp` / `relyProp`
   - `rhoOSLF` : OSLFTypeSystem

3. **Generated syntactic** (TypeSynthesis.lean, GeneratedTyping.lean):
   - `langReduces rhoCalc` (the reflection-free `LanguageDef` interpreter)
   - `langDiamond` / `langBox` (derived from that generic relation)
   - `GenHasType rhoCalc` (generated typing judgment)

4. **Explicitly interpreted** (DerivedContextualStep.lean):
   - `RhoStep` interprets the same authored rules with `rhoReflectionProfile`
   - `rhoInterpretedDiamond` / `rhoInterpretedBox` are derived from that relation

## Key Relationships

```
LanguageDef rhoCalc + rhoReflectionProfile
    ↓ explicit rule interpretation
RhoStep / rhoInterpretedDiamond / rhoInterpretedBox

Established Reduces (semantic COMM substitution and parallel closure)
    ↑ rhoStep_sound
Derived contextual LanguageDef step
```

The hand-written `possiblyProp`/`relyProp` use `Reduces` (propositional).
The generated `langDiamond`/`langBox` use reflection-free `langReduces`.
Rho's COMM semantics instead uses the separately authored reflection profile.
On syntax derived from the rho presentation, `rhoStep_sound` proves that the
explicitly interpreted contextual relation is sound for `Reduces`.

## References

- Meredith & Stay, "Operational Semantics in Logical Form" §6
-/

namespace Mettapedia.OSLF.Framework.SynthesisBridge

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.Reduction
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.Soundness
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.Engine (reduceStep reduceStep_sound)
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedContextualStep
open Mettapedia.OSLF.MeTTaIL.DerivedPresentationSyntax
open Mettapedia.OSLF.Framework
open Mettapedia.OSLF.Framework.DerivedModalities
open Mettapedia.OSLF.Framework.InterpretedTypeSynthesis
open Mettapedia.OSLF.Framework.RhoInstance
open Mettapedia.OSLF.Framework.TypeSynthesis
open Mettapedia.OSLF.Framework.GeneratedTyping
open Mettapedia.GSLT.LanguageDef.ReflectionExtension

/-! ## Layer 1 ↔ Layer 2: Propositional ↔ Derived (Already Proven)

These are from DerivedModalities.lean:
- `derived_diamond_eq_possiblyProp : derivedDiamond rhoSpan φ = possiblyProp φ`
- `derived_box_eq_relyProp : derivedBox rhoSpan φ = relyProp φ`
- `rho_galois_from_span : GaloisConnection possiblyProp relyProp`

This shows the abstract OSLF machinery (adjoint composition on spans)
recovers the same modalities as the hand-written definitions. -/

#check derived_diamond_eq_possiblyProp
#check derived_box_eq_relyProp
#check rho_galois_from_span

/-! ## Layer 2 ↔ Layer 4: Derived ↔ Explicitly Interpreted

`RhoStep` is the least finite relation induced by the authored rho rules under
the separately authored reflection profile.  Its span therefore induces OSLF
modalities and a Galois connection exactly as any other reduction relation
does.  On a source admitted by the presentation-derived process judgment, its
soundness for the established COMM/PAR/EQUIV relation is unconditional.
Completeness is deliberately separate. -/

/-- The reduction span of the authored rho rules under their explicit
reflection interpretation. -/
abbrev rhoInterpretedSpan : ReductionSpan Pattern :=
  interpretedSpan rhoRuleInterpretation rhoBasePremises rhoCalc

/-- Step-future modality induced by explicitly interpreted rho reduction. -/
abbrev rhoInterpretedDiamond : (Pattern → Prop) → Pattern → Prop :=
  interpretedDiamond rhoRuleInterpretation rhoBasePremises rhoCalc

/-- Step-past modality induced by explicitly interpreted rho reduction. -/
abbrev rhoInterpretedBox : (Pattern → Prop) → Pattern → Prop :=
  interpretedBox rhoRuleInterpretation rhoBasePremises rhoCalc

/-- The interpreted rho modalities form the canonical OSLF Galois
connection. -/
theorem rhoInterpretedGalois :
    GaloisConnection rhoInterpretedDiamond rhoInterpretedBox :=
  interpretedGalois rhoRuleInterpretation rhoBasePremises rhoCalc

/-- The interpreted diamond exposes exactly one `RhoStep`. -/
theorem rhoInterpretedDiamond_spec (φ : Pattern → Prop) (p : Pattern) :
    rhoInterpretedDiamond φ p ↔ ∃ q, RhoStep p q ∧ φ q := by
  exact interpretedDiamond_spec rhoRuleInterpretation rhoBasePremises rhoCalc φ p

/-- The interpreted rho box exposes exactly the incoming `RhoStep`s. -/
theorem rhoInterpretedBox_spec (φ : Pattern → Prop) (p : Pattern) :
    rhoInterpretedBox φ p ↔ ∀ q, RhoStep q p → φ q := by
  exact interpretedBox_spec rhoRuleInterpretation rhoBasePremises rhoCalc φ p

/-! ## The reflection-free synthesis is the syntactic specialization -/

/-- The generic explicitly interpreted diamond specializes exactly to the
existing `LanguageDef` diamond when the rule interpretation is syntactic. -/
theorem syntacticInterpretedDiamond_eq_langDiamondUsing
    (relationEnvironment : RelationEnv) (language : LanguageDef) :
    interpretedDiamond .syntactic
        (Mettapedia.OSLF.MeTTaIL.ContextualStep.engineBasePremises
          relationEnvironment) language =
      langDiamondUsing relationEnvironment language := by
  funext predicate source
  apply propext
  simp only [interpretedDiamond_spec, langDiamondUsing_spec,
    interpretedReduces_syntactic_iff, langReducesUsing]

/-- The generic explicitly interpreted box has the same conservative
syntactic specialization. -/
theorem syntacticInterpretedBox_eq_langBoxUsing
    (relationEnvironment : RelationEnv) (language : LanguageDef) :
    interpretedBox .syntactic
        (Mettapedia.OSLF.MeTTaIL.ContextualStep.engineBasePremises
          relationEnvironment) language =
      langBoxUsing relationEnvironment language := by
  funext predicate target
  apply propext
  simp only [interpretedBox_spec, langBoxUsing_spec,
    interpretedReduces_syntactic_iff, langReducesUsing]

/-! ## Interpretation dependence is operationally observable

The positive/negative pair below uses the actual admitted rho reflection
profile.  Its two channel expressions are different syntax but denote the
same canonical rho name.  The reflective interpretation can therefore fire
COMM; the syntactic interpretation of the same five-field core cannot. -/

namespace InterpretationDependenceCanary

/-- The COMM-only sublanguage isolates rule interpretation from contextual
closure. -/
def language : LanguageDef :=
  { rhoCalc with rewrites := [rhoCommRewrite] }

/-- The same five-field core equipped with rho's separately authored
reflection profile. -/
def reflectiveLanguage :
    Mettapedia.OSLF.MeTTaIL.Reflection.ReflectiveLanguageDef :=
  { language with reflection := rhoReflectionProfile }

/-- The rho reflection fibre remains admitted after restricting the core to
its COMM rule. -/
theorem reflectiveLanguage_validate_eq_nil :
    reflectiveLanguage.validate = [] := by
  change language.validate ++
      Mettapedia.OSLF.MeTTaIL.Reflection.validate
        language rhoReflectionProfile = []
  apply List.append_eq_nil_iff.mpr
  refine ⟨rhoCalc_without_ParCong_validate_eq_nil, ?_⟩
  have fullProfile :
      Mettapedia.OSLF.MeTTaIL.Reflection.validate
        rhoCalc rhoReflectionProfile = [] := by
    have full := rhoCalcReflective_validate_eq_nil
    change rhoCalc.validate ++
        Mettapedia.OSLF.MeTTaIL.Reflection.validate
          rhoCalc rhoReflectionProfile = [] at full
    exact (List.append_eq_nil_iff.mp full).2
  have presentationFull :
      rhoCalc.validateReflectivePresentation
        rhoReflectivePresentation.toReflectivePresentationDecl = [] :=
    Mettapedia.OSLF.MeTTaIL.Reflection.presentation_validate_eq_nil_of_validate_eq_nil
      fullProfile (by simp [rhoReflectionProfile])
  have ruleFull :
      rhoCalc.validateReflectiveRule
        [rhoReflectivePresentation.toReflectivePresentationDecl]
        rhoReflectiveRule = [] :=
    Mettapedia.OSLF.MeTTaIL.Reflection.rule_validate_eq_nil_of_validate_eq_nil
      fullProfile (by simp [rhoReflectionProfile])
  have presentationSame :
      language.validateReflectivePresentation
          rhoReflectivePresentation.toReflectivePresentationDecl =
        rhoCalc.validateReflectivePresentation
          rhoReflectivePresentation.toReflectivePresentationDecl := by
    rfl
  have selectedRewriteSame :
      language.rewrites.filter
          (fun rewrite => rewrite.name == rhoReflectiveRule.rewriteRule) =
        rhoCalc.rewrites.filter
          (fun rewrite => rewrite.name == rhoReflectiveRule.rewriteRule) := by
    simp [language, rhoCalc, rhoReflectiveRule, rhoCommRewrite,
      rhoParCongRewrite]
  have ruleSame :
      language.validateReflectiveRule
          [rhoReflectivePresentation.toReflectivePresentationDecl]
          rhoReflectiveRule =
        rhoCalc.validateReflectiveRule
          [rhoReflectivePresentation.toReflectivePresentationDecl]
          rhoReflectiveRule := by
    unfold LanguageDef.validateReflectiveRule
    rw [selectedRewriteSame]
  have presentationClean :
      language.validateReflectivePresentation
        rhoReflectivePresentation.toReflectivePresentationDecl = [] := by
    rw [presentationSame]
    exact presentationFull
  have ruleClean :
      language.validateReflectiveRule
        [rhoReflectivePresentation.toReflectivePresentationDecl]
        rhoReflectiveRule = [] := by
    rw [ruleSame]
    exact ruleFull
  simp [Mettapedia.OSLF.MeTTaIL.Reflection.validate,
    rhoReflectionProfile, presentationClean, ruleClean]

def canonicalChannel : Pattern :=
  .apply "NQuote" [.apply "PZero" []]

def unitExpandedChannel : Pattern :=
  .apply "NQuote"
    [.collection .hashBag [.apply "PZero" [], .apply "PZero" []] none]

def source : Pattern :=
  .collection .hashBag
    [.apply "PInput"
      [unitExpandedChannel, .lambda none (.apply "PZero" [])],
     .apply "POutput" [canonicalChannel, .apply "PZero" []]] none

def bindings : Mettapedia.OSLF.MeTTaIL.Match.Bindings :=
  [("q", .apply "PZero" []),
   ("rest", .collection .hashBag [] none),
   ("p", .apply "PZero" []),
   ("n", unitExpandedChannel)]

def target : Pattern :=
  (Mettapedia.OSLF.MeTTaIL.InterpretedContextualStep.RuleInterpretation.reflection
    rhoReflectionProfile).instantiateRule language rhoCommRewrite bindings

/-- Canonical repeated-variable matching accepts the two rho-equivalent
channel representations. -/
theorem reflective_match :
    bindings ∈
      Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.matchPatternForRuleUsing
        rhoReflectionProfile rhoCommRewrite source := by
  decide +kernel

/-- Ordinary repeated-variable matching rejects those distinct syntax trees. -/
theorem syntactic_match_rejects :
    Mettapedia.OSLF.MeTTaIL.Match.matchPattern rhoCommRewrite.left source = [] := by
  decide +kernel

/-- The admitted reflective interpretation produces the COMM step. -/
theorem reflective_step :
    interpretedReduces (.reflection rhoReflectionProfile)
      rhoBasePremises language source target := by
  refine ⟨1,
    Mettapedia.OSLF.MeTTaIL.InterpretedContextualStep.StepAt.rule
      (rule := rhoCommRewrite) ?_ reflective_match (.nil _) rfl⟩
  simp [language]

/-- The syntactic interpretation of the identical five-field core cannot
produce that step. -/
theorem syntactic_step_rejects :
    ¬ interpretedReduces .syntactic rhoBasePremises language source target := by
  rw [interpretedReduces_syntactic_iff]
  apply Mettapedia.OSLF.MeTTaIL.ContextualStep.not_step_of_matchPatternForRule_eq_nil
  intro rule ruleMember
  have ruleEq : rule = rhoCommRewrite := by
    simpa [language] using ruleMember
  subst rule
  simpa [Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.matchPatternForRule]
    using syntactic_match_rejects

/-- **Reflection can change modal answers.**  The reflective and syntactic
diamonds over the same five-field core disagree on a concrete target
predicate. -/
theorem reflection_changes_possibility :
    interpretedDiamond (.reflection rhoReflectionProfile)
        rhoBasePremises language (fun result => result = target) source ∧
      ¬ interpretedDiamond .syntactic
        rhoBasePremises language (fun result => result = target) source := by
  constructor
  · rw [interpretedDiamond_spec]
    exact ⟨target, reflective_step, rfl⟩
  · intro possible
    rw [interpretedDiamond_spec] at possible
    obtain ⟨result, step, resultEq⟩ := possible
    subst result
    exact syntactic_step_rejects step

end InterpretationDependenceCanary

/-- The explicitly interpreted rho possibility modality soundly maps into the
established possibility modality on presentation-derived process syntax. -/
theorem rhoInterpretedDiamond_implies_possibly
    {free : FreeSortContext} {bound : List String}
    (φ : Pattern → Prop) (p : Pattern)
    (typed : ProcWellSorted rhoReflectivePresentation free bound p)
    (holds : rhoInterpretedDiamond φ p) :
    possiblyProp φ p := by
  obtain ⟨q, step, satisfies⟩ :=
    (rhoInterpretedDiamond_spec (φ := φ) (p := p)).1 holds
  exact ⟨q, rhoStep_sound typed step, satisfies⟩

/-- Generic conditional sound-direction bridge for languages without a
    language-specific agreement theorem. -/
theorem langDiamond_implies_possibly_at (φ : Pattern → Prop) (p : Pattern)
    (h : langDiamond rhoCalc φ p)
    (sound : ∀ q, langReduces rhoCalc p q → Nonempty (Reduces p q)) :
    possiblyProp φ p := by
  have h' : ∃ q, langReduces rhoCalc p q ∧ φ q :=
    (langDiamond_spec (lang := rhoCalc) (φ := φ) (p := p)).1 h
  obtain ⟨q, hred, hφ⟩ := h'
  exact ⟨q, sound q hred, hφ⟩

/-- Dually: if possibly holds and the reduction is witnessed by the engine,
    then langDiamond holds. -/
theorem possibly_implies_langDiamond_at (φ : Pattern → Prop) (p : Pattern)
    (h : possiblyProp φ p)
    (complete : ∀ q, Nonempty (Reduces p q) → langReduces rhoCalc p q) :
    langDiamond rhoCalc φ p := by
  obtain ⟨q, hred, hφ⟩ := h
  rw [langDiamond_spec]
  exact ⟨q, complete q hred, hφ⟩

/-! ## Unconditional Specialized Engine Bridges

The specialized ρ-calculus engine (`reduceStep` from Engine.lean) is proven
sound with respect to the propositional `Reduces` relation. This gives
**unconditional** bridges between the specialized engine and the hand-written
modalities, without going through the generic premise-aware engine.

### Why use the specialized engine bridge?

Since the locally nameless migration, the generic engine (`matchPattern`) is
capture-safe by construction — bound variables are de Bruijn indices, so no
alpha-renaming occurs. However, the unconditional bridge via the specialized
engine is still the **simplest** path for ρ-calculus, since `reduceStep_sound`
directly connects to the propositional `Reduces` without going through the
generic `ContextualStep.rewriteAt` → `TypeSynthesis.langReducesUsing` chain. -/

/-- Unconditional bridge: if the specialized engine finds a reduct satisfying φ,
    then the hand-written ◇φ holds.

    This is the recommended way to verify `possiblyProp` computationally. -/
theorem specialized_possibly (φ : Pattern → Prop) (p : Pattern)
    (h : ∃ q ∈ reduceStep p, φ q) :
    possiblyProp φ p := by
  obtain ⟨q, hq, hφ⟩ := h
  exact ⟨q, reduceStep_sound p q _ hq, hφ⟩

/-- Unconditional bridge: if ⧫φ holds at p (all predecessors of p satisfy φ)
    and q reduces to p via the specialized engine, then φ q.

    This allows checking rely/box properties computationally. -/
theorem specialized_rely_check (φ : Pattern → Prop) (p : Pattern)
    (hbox : relyProp φ p) (q : Pattern) (hq : p ∈ reduceStep q) :
    φ q :=
  hbox q (reduceStep_sound q p _ hq)

/-- Unconditional bridge: the specialized engine is a sound decision procedure
    for `possiblyProp (fun _ => True)` (can the term reduce?).

    `reduceStep p ≠ [] → possiblyProp (fun _ => True) p` -/
theorem specialized_can_reduce (p : Pattern) (q : Pattern)
    (hq : q ∈ reduceStep p) :
    possiblyProp (fun _ => True) p :=
  specialized_possibly _ p ⟨q, hq, trivial⟩

/-- Tiny restricted bridge instance in the exact shape used by synthesis:
    on the specialized executable path (`reduceStep`), one-step results are
    propositionally sound (`Reduces`).

    This is the concrete bridge we can instantiate unconditionally today. -/
theorem specialized_soundBridge_at (p : Pattern) :
    ∀ q, q ∈ reduceStep p → Nonempty (Reduces p q) := by
  intro q hq
  exact reduceStep_sound p q _ hq

/-! ## The Three-Layer Architecture

We can now state the full picture:

```
possiblyProp φ p                         -- established rho reduction
  = derivedDiamond rhoSpan φ p           -- derived from its reduction span
  ← rhoInterpretedDiamond φ p            -- explicit interpreted LanguageDef step
    (sound unconditionally on derived rho syntax)

langDiamond rhoCalc φ p                  -- reflection-free generated step
    (related only under an explicit agreement hypothesis)
```

Layer 1 = Layer 2 is proven (`derived_diamond_eq_possiblyProp`).
The interpreted-to-established direction is proved by `rhoStep_sound`.
Agreement between the established relation and the reflection-free generic
`LanguageDef` interpretation remains conditional.  Currently:
- Sound direction on presentation-derived rho processes: `rhoStep_sound`
- Complete direction for the specialized engine is available up to structural
  congruence in `Engine.lean`
- The explicitly interpreted relation compiles the authored reflective
  substitution; unrestricted completeness remains separate

Additionally, the **specialized engine bridges** (above) give unconditional
connections from `reduceStep` to `possiblyProp`/`relyProp`, bypassing the
generic engine entirely. This is the recommended path for ρ-calculus. -/

/-! ## GenHasType ↔ HasType Correspondence

The generated `GenHasType rhoCalc` and hand-written `HasType` have
structurally identical rules. The only difference is:
- `HasType` uses `possiblyProp`/`relyProp` (from propositional Reduces)
- `GenHasType` uses `langDiamond`/`langBox` (from executable engine)

If an adequacy theorem makes the two modal operators agree, the corresponding
typing judgments can then be related.  That adequacy theorem is open. -/

/-- Convert a hand-written NativeType to a generated GenNativeType.

    The sort validity proof must be adapted from
    `sort ∈ ["Proc", "Name"]` to `sort ∈ rhoCalc.types`.
    These are the same list, so `decide` handles it. -/
def nativeToGen (τ : NativeType) : GenNativeType rhoCalc :=
  ⟨τ.sort, τ.predicate, by
    have h := τ.sort_valid
    simp at h
    rcases h with h | h
    · rw [h]
      decide
    · rw [h]
      decide⟩

/-- Convert a hand-written TypingContext to a generated one -/
def ctxToGen (Γ : TypingContext) : GenTypingContext rhoCalc :=
  Γ.map fun (x, τ) => (x, nativeToGen τ)

/-! ## Verification: The Generated System Types the Same Terms

We verify that standard ρ-calculus terms are typable in both systems.
This is a sanity check that the generated rules are correct. -/

-- In the hand-written system:
example : HasType TypingContext.empty
    (.apply "PZero" []) ⟨"Proc", fun _ => True, by simp⟩ :=
  HasType.nil

-- In the generated system:
example : GenHasType rhoCalc GenTypingContext.empty
    (.apply "PZero" []) ⟨"Proc", topPred, by decide⟩ :=
  .nullary rhoCalc_has_PZero (by decide)

-- Hand-written: @(0) has type (Name, ◇⊤)
example : HasType TypingContext.empty
    (.apply "NQuote" [.apply "PZero" []])
    ⟨"Name", possiblyProp (fun _ => True), by simp⟩ :=
  HasType.quote HasType.nil

-- Generated: @(0) has type (Name, langDiamond rhoCalc ⊤)
example : GenHasType rhoCalc GenTypingContext.empty
    (.apply "NQuote" [.apply "PZero" []])
    ⟨"Name", langDiamond rhoCalc topPred, by decide⟩ :=
  .quote (by decide) (by decide) rhoCalc_has_NQuote
    (.nullary rhoCalc_has_PZero (by decide))

-- Hand-written: *(@(0)) has type (Proc, □(◇⊤))
example : HasType TypingContext.empty
    (.apply "PDrop" [.apply "NQuote" [.apply "PZero" []]])
    ⟨"Proc", relyProp (possiblyProp (fun _ => True)), by simp⟩ :=
  HasType.drop (HasType.quote HasType.nil)

-- Generated: *(@(0)) has type (Proc, langBox(langDiamond ⊤))
example : GenHasType rhoCalc GenTypingContext.empty
    (.apply "PDrop" [.apply "NQuote" [.apply "PZero" []]])
    ⟨"Proc", langBox rhoCalc (langDiamond rhoCalc topPred), by decide⟩ :=
  .drop (by decide) (by decide) rhoCalc_has_PDrop
    (.quote (by decide) (by decide) rhoCalc_has_NQuote
      (.nullary rhoCalc_has_PZero (by decide)))

/-! ## Summary

**0 sorries. 0 axioms.**

The four-layer bridge demonstrates:

1. **Layer 1 = Layer 2** (proven in DerivedModalities.lean):
   `possiblyProp = derivedDiamond rhoSpan`, `relyProp = derivedBox rhoSpan`

2. **Explicit interpretation → Layer 2** (proven on derived rho syntax):
   `rhoInterpretedDiamond_implies_possibly`

3. **Specialized engine bridge** (unconditional):
   - `specialized_possibly`: `(∃ q ∈ reduceStep p, φ q) → possiblyProp φ p`
   - `specialized_rely_check`: `relyProp φ p → p ∈ reduceStep q → φ q`
   - `specialized_can_reduce`: `q ∈ reduceStep p → possiblyProp ⊤ p`

4. **HasType and GenHasType** (structurally aligned):
   Same rule shapes, with generated-to-established modal soundness proved on
   derived rho syntax; the converse remains separate

5. **Executable diagnostics**: the eight-case corpus agrees after reflective
   COMM compilation; it remains testing evidence, not universal adequacy

The generic OSLF construction itself is available:
- `LanguageDef` → `langOSLF` (automatic OSLFTypeSystem with Galois connection)
- `GenHasType` provides a concrete typing judgment
- The Galois connection `◇ ⊣ □` is proven automatically
- Specialized engine → propositional modalities is unconditional

The sound connection from the explicitly interpreted authored rho rules to
`Reduces` is `rhoStep_sound`.  A converse theorem would require a distinct
completeness proof and is not asserted here.
-/

end Mettapedia.OSLF.Framework.SynthesisBridge
