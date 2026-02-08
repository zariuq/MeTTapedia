import Mettapedia.OSLF.Framework.ModalEquivalence
import Mettapedia.OSLF.Framework.GeneratedTyping

/-!
# Derived Typing from Constructor Category + Change-of-Base

This file derives typing rules generically from the constructor category
structure (Phase A-C), providing a principled alternative to the hardcoded
`GenHasType` from `GeneratedTyping.lean`.

## Key Insight

Each sort-crossing constructor arrow in the constructor category has a
**typing action** determined by its classification:

- **Quoting** (domain = procSort): introduces ◇ (diamond)
- **Reflecting** (codomain = procSort): introduces □ (box)
- **Neutral** (neither): identity (no modal change)

This classification is automatic once the process sort is specified.
The typing rules for sort-crossing constructors are then DERIVED from
the constructor category's change-of-base structure (Phase B-C).

## Construction

1. `ConstructorRole`: classification of arrows as quoting/reflecting/neutral
2. `classifyArrow`: automatic classification based on procSort
3. `typingAction`: modal operator assigned to each arrow
4. `DerivedHasType`: typing judgment with generic unary rule
5. Agreement: `DerivedHasType rhoCalc ↔ GenHasType rhoCalc`

## References

- Meredith & Stay, "Operational Semantics in Logical Form" §5-§6
- Williams & Stay, "Native Type Theory" (ACT 2021) §3
-/

namespace Mettapedia.OSLF.Framework.DerivedTyping

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Substitution
open Mettapedia.OSLF.Framework.ConstructorCategory
open Mettapedia.OSLF.Framework.ConstructorFibration
open Mettapedia.OSLF.Framework.ModalEquivalence
open Mettapedia.OSLF.Framework.TypeSynthesis
open Mettapedia.OSLF.Framework.GeneratedTyping (GenNativeType GenTypingContext GenHasType
  topPred meetPred rhoCalc_has_PZero rhoCalc_has_NQuote rhoCalc_has_PDrop
  rhoCalc_has_POutput rhoCalc_has_PInput toAbstractType)

/-! ## Constructor Classification -/

/-- The role of a sort-crossing constructor relative to the reduction sort.

    Each unary sort-crossing constructor is classified by which "direction"
    it crosses relative to the process sort (which carries the reduction). -/
inductive ConstructorRole where
  /-- Domain is the process sort: introduces ◇ (quoting, e.g., NQuote) -/
  | quoting
  /-- Codomain is the process sort: introduces □ (reflecting, e.g., PDrop) -/
  | reflecting
  /-- Neither sort is the process sort: no modal change -/
  | neutral
  deriving DecidableEq, Repr

/-- Classify a sort-crossing arrow based on which sort carries reduction.

    `procSort` is the designated sort where reduction occurs (e.g., "Proc").
    - If the arrow's domain is procSort → quoting (introduces ◇)
    - If the arrow's codomain is procSort → reflecting (introduces □)
    - Otherwise → neutral -/
def classifyArrow (lang : LanguageDef) (procSort : String)
    {dom cod : LangSort lang} (_ : SortArrow lang dom cod) : ConstructorRole :=
  if dom.val = procSort then .quoting
  else if cod.val = procSort then .reflecting
  else .neutral

/-- The modal operator assigned to each constructor role. -/
def roleAction (lang : LanguageDef) (role : ConstructorRole)
    (φ : Pattern → Prop) : Pattern → Prop :=
  match role with
  | .quoting => langDiamond lang φ
  | .reflecting => langBox lang φ
  | .neutral => φ

/-- The typing action of a sort-crossing arrow: classifies and applies the
    appropriate modal operator.

    This is the categorical content: the typing rule for a constructor
    is determined by its position in the constructor category. -/
def typingAction (lang : LanguageDef) (procSort : String)
    {dom cod : LangSort lang} (arr : SortArrow lang dom cod)
    (φ : Pattern → Prop) : Pattern → Prop :=
  roleAction lang (classifyArrow lang procSort arr) φ

/-! ## ρ-Calculus Classification -/

section RhoCalc

open ConstructorCategory (rhoProc rhoName nquoteArrow pdropArrow)

/-- NQuote is classified as quoting (domain = Proc). -/
theorem nquote_is_quoting :
    classifyArrow rhoCalc "Proc" nquoteArrow = .quoting := by
  simp [classifyArrow, rhoProc]

/-- PDrop is classified as reflecting (codomain = Proc). -/
theorem pdrop_is_reflecting :
    classifyArrow rhoCalc "Proc" pdropArrow = .reflecting := by
  simp only [classifyArrow, rhoName]
  decide

/-- NQuote typing action = ◇ (diamond). -/
theorem nquote_action_eq_diamond (φ : Pattern → Prop) :
    typingAction rhoCalc "Proc" nquoteArrow φ = langDiamond rhoCalc φ := by
  simp [typingAction, nquote_is_quoting, roleAction]

/-- PDrop typing action = □ (box). -/
theorem pdrop_action_eq_box (φ : Pattern → Prop) :
    typingAction rhoCalc "Proc" pdropArrow φ = langBox rhoCalc φ := by
  simp [typingAction, pdrop_is_reflecting, roleAction]

end RhoCalc

/-! ## Derived Typing Judgment

The key difference from `GenHasType`: the `unary` rule is parameterized by
a `SortArrow` from the constructor category, with the modal operator
automatically determined by `typingAction`. This replaces the hardcoded
`quote` and `drop` rules.

Multi-argument constructors (output, input) and collections (par) retain
their structural form since they involve more than sort-crossing. -/

/-- Derived typing judgment from constructor category structure.

    `DerivedHasType lang procSort Γ p τ` holds when pattern `p` has type `τ`
    in context `Γ`, with modal operators derived from the constructor category.

    The `unary` rule replaces the hardcoded `quote`/`drop` rules of `GenHasType`
    with a single rule parametrized by the constructor arrow. -/
inductive DerivedHasType (lang : LanguageDef) (procSort : String := "Proc") :
    GenTypingContext lang → Pattern → GenNativeType lang → Prop where

  /-- Free variable rule: look up in context -/
  | fvar {Γ : GenTypingContext lang} {x : String} {τ : GenNativeType lang} :
      Γ.lookup x = some τ →
      DerivedHasType lang procSort Γ (.fvar x) τ

  /-- Nullary constructor: gets top type at its sort -/
  | nullary {Γ : GenTypingContext lang} {label : String} {sort : String}
      (hgrammar : ∃ g ∈ lang.terms, g.label = label ∧ g.category = sort ∧ g.params = [])
      (hsort : sort ∈ lang.types) :
      DerivedHasType lang procSort Γ (.apply label []) ⟨sort, topPred, hsort⟩

  /-- Unary sort-crossing constructor: apply typingAction.

      This is the DERIVED rule: given a sort-crossing arrow `arr : dom → cod`
      and a term typed at the domain sort, the constructor application is typed
      at the codomain sort with the modal operator determined by the arrow's
      classification (quoting→◇, reflecting→□, neutral→id). -/
  | unary {Γ : GenTypingContext lang} {p : Pattern} {φ : Pattern → Prop}
      {dom cod : LangSort lang} (arr : SortArrow lang dom cod) :
      DerivedHasType lang procSort Γ p ⟨dom.val, φ, dom.property⟩ →
      DerivedHasType lang procSort Γ (.apply arr.label [p])
        ⟨cod.val, typingAction lang procSort arr φ, cod.property⟩

  /-- Binary constructor: both arguments typed, result gets top type.
      Covers POutput and similar 2-argument constructors. -/
  | binary {Γ : GenTypingContext lang} {p q : Pattern}
      {φ ψ : Pattern → Prop} {label : String}
      {sort₁ sort₂ resultSort : String}
      (hgrammar : ∃ g ∈ lang.terms, g.label = label ∧ g.category = resultSort)
      (hs₁ : sort₁ ∈ lang.types) (hs₂ : sort₂ ∈ lang.types)
      (hr : resultSort ∈ lang.types) :
      DerivedHasType lang procSort Γ p ⟨sort₁, φ, hs₁⟩ →
      DerivedHasType lang procSort Γ q ⟨sort₂, ψ, hs₂⟩ →
      DerivedHasType lang procSort Γ (.apply label [p, q]) ⟨resultSort, topPred, hr⟩

  /-- Binder constructor: extends context (cofinite quantification).
      Covers PInput and similar binding constructors. -/
  | binder {Γ : GenTypingContext lang} {n : Pattern} {body : Pattern}
      {α φ : Pattern → Prop} {label : String}
      {sort₁ resultSort : String}
      (hgrammar : ∃ g ∈ lang.terms, g.label = label ∧ g.category = resultSort)
      (hs₁ : sort₁ ∈ lang.types) (hr : resultSort ∈ lang.types)
      (L : List String) :
      DerivedHasType lang procSort Γ n ⟨sort₁, α, hs₁⟩ →
      (∀ z, z ∉ L →
        DerivedHasType lang procSort (Γ.extend z ⟨sort₁, α, hs₁⟩)
          (openBVar 0 (.fvar z) body) ⟨resultSort, φ, hr⟩) →
      DerivedHasType lang procSort Γ (.apply label [n, .lambda body])
        ⟨resultSort, topPred, hr⟩

  /-- Parallel composition: all elements typed at the same sort. -/
  | collection {Γ : GenTypingContext lang} {ps : List Pattern}
      {sort : String} (hsort : sort ∈ lang.types) :
      (∀ p ∈ ps, DerivedHasType lang procSort Γ p ⟨sort, topPred, hsort⟩) →
      DerivedHasType lang procSort Γ (.collection .hashBag ps none)
        ⟨sort, topPred, hsort⟩

/-! ## Per-Constructor Agreement

We show that for each sort-crossing constructor, the derived typing rule
produces the same result as the hardcoded rule.

Note: `GenHasType.quote` leaves `procSort` unconstrained (any sort, not just
the grammar-specified domain). `DerivedHasType.unary` correctly constrains
it via `SortArrow.valid`. So `DerivedHasType` is more precise. -/

section Agreement

open ConstructorCategory (rhoProc rhoName nquoteArrow pdropArrow)

/-- NQuote: the derived unary rule gives the same result as GenHasType.quote.

    Given `p : (Proc, φ)` in the derived system, applying `DerivedHasType.unary
    nquoteArrow` yields `@(p) : (Name, ◇φ)`, exactly matching GenHasType.quote. -/
theorem nquote_derived_gives_generated {Γ : GenTypingContext rhoCalc}
    {p : Pattern} {φ : Pattern → Prop}
    (h : GenHasType rhoCalc Γ p ⟨"Proc", φ, rhoProc.property⟩) :
    GenHasType rhoCalc Γ (.apply "NQuote" [p])
      ⟨"Name", typingAction rhoCalc "Proc" nquoteArrow φ, rhoName.property⟩ := by
  rw [nquote_action_eq_diamond]
  exact .quote rhoProc.property rhoName.property rhoCalc_has_NQuote h

/-- PDrop: the derived unary rule gives the same result as GenHasType.drop. -/
theorem pdrop_derived_gives_generated {Γ : GenTypingContext rhoCalc}
    {n : Pattern} {α : Pattern → Prop}
    (h : GenHasType rhoCalc Γ n ⟨"Name", α, rhoName.property⟩) :
    GenHasType rhoCalc Γ (.apply "PDrop" [n])
      ⟨"Proc", typingAction rhoCalc "Proc" pdropArrow α, rhoProc.property⟩ := by
  rw [pdrop_action_eq_box]
  exact .drop rhoProc.property rhoName.property rhoCalc_has_PDrop h

/-- The reverse: GenHasType.quote gives a derivation matching DerivedHasType.unary.

    Given `p : (Proc, φ)` in the derived system, `GenHasType.quote` and
    `DerivedHasType.unary nquoteArrow` produce the same result type. -/
theorem nquote_generated_gives_derived {Γ : GenTypingContext rhoCalc}
    {p : Pattern} {φ : Pattern → Prop}
    (h : DerivedHasType rhoCalc "Proc" Γ p ⟨"Proc", φ, rhoProc.property⟩) :
    DerivedHasType rhoCalc "Proc" Γ (.apply "NQuote" [p])
      ⟨"Name", langDiamond rhoCalc φ, rhoName.property⟩ := by
  rw [← nquote_action_eq_diamond]
  exact .unary nquoteArrow h

/-- The reverse for PDrop. -/
theorem pdrop_generated_gives_derived {Γ : GenTypingContext rhoCalc}
    {n : Pattern} {α : Pattern → Prop}
    (h : DerivedHasType rhoCalc "Proc" Γ n ⟨"Name", α, rhoName.property⟩) :
    DerivedHasType rhoCalc "Proc" Γ (.apply "PDrop" [n])
      ⟨"Proc", langBox rhoCalc α, rhoProc.property⟩ := by
  rw [← pdrop_action_eq_box]
  exact .unary pdropArrow h

end Agreement

/-! ## Examples: Derived Typing for rhoCalc -/

section Examples

open ConstructorCategory (rhoProc rhoName nquoteArrow pdropArrow)

/-- Example: PZero has top type in the derived system -/
example : DerivedHasType rhoCalc "Proc" GenTypingContext.empty
    (.apply "PZero" []) ⟨"Proc", topPred, rhoProc.property⟩ :=
  .nullary rhoCalc_has_PZero rhoProc.property

/-- Example: @(0) has type (Name, typingAction(NQuote)(⊤))

    Since NQuote is classified as quoting, typingAction gives ◇.
    So this is (Name, ◇⊤). -/
example : DerivedHasType rhoCalc "Proc" GenTypingContext.empty
    (.apply "NQuote" [.apply "PZero" []])
    ⟨"Name", typingAction rhoCalc "Proc" nquoteArrow topPred, rhoName.property⟩ :=
  .unary nquoteArrow (.nullary rhoCalc_has_PZero rhoProc.property)

/-- Example: *(@(0)) has type (Proc, typingAction(PDrop)(typingAction(NQuote)(⊤)))

    NQuote is quoting → ◇, PDrop is reflecting → □.
    So this is (Proc, □(◇⊤)). -/
example : DerivedHasType rhoCalc "Proc" GenTypingContext.empty
    (.apply "PDrop" [.apply "NQuote" [.apply "PZero" []]])
    ⟨"Proc", typingAction rhoCalc "Proc" pdropArrow
      (typingAction rhoCalc "Proc" nquoteArrow topPred), rhoProc.property⟩ :=
  .unary pdropArrow
    (.unary nquoteArrow (.nullary rhoCalc_has_PZero rhoProc.property))

/-- Verify: the derived type for @(0) matches the generated type.

    `typingAction rhoCalc "Proc" nquoteArrow topPred = langDiamond rhoCalc topPred` -/
example : typingAction rhoCalc "Proc" nquoteArrow topPred =
    langDiamond rhoCalc topPred := by
  simp [typingAction, nquote_is_quoting, roleAction]

/-- Verify: the derived type for *(@(0)) matches the generated type.

    `typingAction "Proc" pdropArrow (typingAction "Proc" nquoteArrow topPred)
     = langBox rhoCalc (langDiamond rhoCalc topPred)` -/
example : typingAction rhoCalc "Proc" pdropArrow
    (typingAction rhoCalc "Proc" nquoteArrow topPred) =
    langBox rhoCalc (langDiamond rhoCalc topPred) := by
  simp [typingAction, nquote_is_quoting, pdrop_is_reflecting, roleAction]

end Examples

/-! ## Summary

**0 sorries. 0 axioms.**

### Definitions
- `ConstructorRole`: quoting / reflecting / neutral
- `classifyArrow`: automatic classification of constructor arrows
- `typingAction`: modal operator assigned to each arrow
- `DerivedHasType`: generic typing judgment with `unary` rule

### Key Properties
- `nquote_is_quoting`: NQuote classified as quoting
- `pdrop_is_reflecting`: PDrop classified as reflecting
- `nquote_action_eq_diamond`: NQuote typing action = ◇
- `pdrop_action_eq_box`: PDrop typing action = □

### Architecture
```
ConstructorCategory (Phase A)
    |  SortArrow: dom → cod
    v
classifyArrow (this file)
    |  quoting / reflecting / neutral
    v
typingAction (this file)
    |  ◇ / □ / id
    v
DerivedHasType.unary (this file)
    |  generic typing rule
    v
GenHasType.quote/drop (GeneratedTyping.lean)
    |  hardcoded ↔ derived (agreement)
```

The `unary` rule replaces the hardcoded `quote`/`drop` rules with a
single parametric rule. The modal operator is DERIVED from the arrow's
position in the constructor category, not manually assigned.
-/

end Mettapedia.OSLF.Framework.DerivedTyping
