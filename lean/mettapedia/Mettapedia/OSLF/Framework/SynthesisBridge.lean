import Mettapedia.OSLF.Framework.GeneratedTyping
import Mettapedia.OSLF.Framework.RhoInstance
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Soundness
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Engine
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefAdequacy

/-!
# Synthesis Bridge: Generated ↔ Hand-Written Type Systems

This file bridges three layers of the OSLF formalization:

1. **Hand-written** (Reduction.lean, Soundness.lean):
   - `Reduces : Pattern → Pattern → Type` (propositional)
   - `possiblyProp` / `relyProp` (hand-written modalities)
   - `HasType` (hand-written typing judgment)

2. **Derived abstract** (DerivedModalities.lean, RhoInstance.lean):
   - `rhoSpan` → `derivedDiamond` / `derivedBox`
   - Proven equal to `possiblyProp` / `relyProp`
   - `rhoOSLF` : OSLFTypeSystem

3. **Generated** (TypeSynthesis.lean, GeneratedTyping.lean):
   - `langReduces rhoCalc` (the generic `LanguageDef` interpreter)
   - `langDiamond` / `langBox` (derived from that generic relation)
   - `GenHasType rhoCalc` (generated typing judgment)

## Key Relationships

```
LanguageDef rhoCalc
    ↓ declaration-compiled reflective COMM substitution
langReduces / langDiamond / langBox

Paper Reduces (semantic COMM substitution)
    ↑ reduceStep_sound
Specialized reduceStep
```

The hand-written `possiblyProp`/`relyProp` use `Reduces` (propositional).
The generated `langDiamond`/`langBox` use the generic `langReduces` relation.
`reduceStep_sound` proves only that the specialized executable engine is sound
for `Reduces`.  It does not connect the generic interpreter to `Reduces`.

## References

- Meredith & Stay, "Operational Semantics in Logical Form" §6
-/

namespace Mettapedia.OSLF.Framework.SynthesisBridge

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.Reduction
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.Soundness
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.Engine (reduceStep reduceStep_sound)
open Mettapedia.OSLF.Framework
open Mettapedia.OSLF.Framework.DerivedModalities
open Mettapedia.OSLF.Framework.RhoInstance
open Mettapedia.OSLF.Framework.TypeSynthesis
open Mettapedia.OSLF.Framework.GeneratedTyping

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

/-! ## Layer 2 ↔ Layer 3: Derived ↔ Generated

The key gap: `rhoSpan` uses `Nonempty (Reduces p q)` while `langSpan rhoCalc`
uses `langReduces rhoCalc p q = q ∈ rewriteWithContextWithPremises rhoCalc p`
(i.e. premise-aware execution with `RelationEnv.empty`).

They are not yet connected unconditionally.  The generic interpreter now
selects the validated reflective COMM declaration: a dropped received name
exposes the quoted process, literal quotation is opaque, and free drop remains
inert.  `LanguageDefAdequacy.lean` proves declaration selection, kernel-checked
language admission, compiled-RHS shape, and the critical positive/negative
agreement witnesses.  The remaining general theorem must restrict raw
`Pattern`s to the derived rho syntax and make channel matching respect the
authored static name equations. -/

-- The inclusion `langReduces rhoCalc p q → Nonempty (Reduces p q)` is an
-- open adequacy obligation.  Reflective substitution no longer blocks it;
-- derived sorting and static channel canonicalization are the remaining
-- semantic boundary.

/-- Conditional sound-direction bridge.  The `sound` argument is the still-open
    adequacy theorem relating generic `LanguageDef` interpretation to paper
    `Reduces`; this theorem does not manufacture that evidence. -/
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
generic `rewriteWithContextWithPremises` → `DeclReducesWithPremises` chain. -/

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
possiblyProp φ p            -- Layer 1: hand-written (Reduction.lean)
  = derivedDiamond rhoSpan φ p  -- Layer 2: derived from propositional Reduces
  ↔ langDiamond rhoCalc φ p     -- Layer 3: derived from executable engine
    (when soundness + completeness hold)
```

Layer 1 = Layer 2 is proven (`derived_diamond_eq_possiblyProp`).
Layer 2 ↔ Layer 3 depends on an adequacy theorem between the paper relation
and the generic `LanguageDef` interpretation.  Currently:
- Sound direction: `reduceStep_sound` (proven in Engine.lean)
- Complete direction for the specialized engine is available up to structural
  congruence in `Engine.lean`
- The generic interpreter compiles the authored reflective substitution and
  agrees on the checked COMM boundary cases; a universal relation bridge still
  requires derived sorting and static channel canonicalization

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

The three-layer bridge demonstrates:

1. **Layer 1 = Layer 2** (proven in DerivedModalities.lean):
   `possiblyProp = derivedDiamond rhoSpan`, `relyProp = derivedBox rhoSpan`

2. **Layer 2 ↔ Layer 3** (conditional on engine agreement):
   `langDiamond rhoCalc ↔ possiblyProp` when executable matches propositional

3. **Specialized engine bridge** (unconditional):
   - `specialized_possibly`: `(∃ q ∈ reduceStep p, φ q) → possiblyProp φ p`
   - `specialized_rely_check`: `relyProp φ p → p ∈ reduceStep q → φ q`
   - `specialized_can_reduce`: `q ∈ reduceStep p → possiblyProp ⊤ p`

4. **HasType ↔ GenHasType** (structurally):
   Same rules, different modal operators, agree when layers 2-3 agree

5. **Executable diagnostics**: the eight-case corpus agrees after reflective
   COMM compilation; it remains testing evidence, not universal adequacy

The generic OSLF construction itself is available:
- `LanguageDef` → `langOSLF` (automatic OSLFTypeSystem with Galois connection)
- `GenHasType` provides a concrete typing judgment
- The Galois connection `◇ ⊣ □` is proven automatically
- Specialized engine → propositional modalities is unconditional

The connection from the authored rho `LanguageDef` to the paper `Reduces`
relation remains open until the derived rho-syntax boundary and static channel
canonicalization are included in the universal agreement theorem.
-/

end Mettapedia.OSLF.Framework.SynthesisBridge
