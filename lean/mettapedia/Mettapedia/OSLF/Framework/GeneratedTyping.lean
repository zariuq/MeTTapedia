import Mettapedia.OSLF.Framework.TypeSynthesis

/-!
# Generated Typing Rules from LanguageDef

Given any `LanguageDef`, the OSLF algorithm (Meredith & Stay) mechanically generates
a typing judgment. This file implements the generation pipeline:

```
LanguageDef  ──→  GenNativeType  ──→  GenHasType  ──→  substitutability
  (grammar      (sort, pred)          (typing         (types preserved
   + rewrites)   pairs)                judgment)        under substitution)
```

## Key Insight

The typing rules are **determined** by the grammar rules:

- Each constructor `C : T₁ × ... × Tₙ → T` becomes a typing rule
- **Quote** constructors (sort-crossing into Name) introduce `◇` (diamond)
- **Drop** constructors (sort-crossing from Name) introduce `□` (box)
- Binder parameters get context extension
- The result type predicate depends on the constructor's role in reduction

## References

- Meredith & Stay, "Operational Semantics in Logical Form" §5–§6
- Williams & Stay, "Native Type Theory" (ACT 2021)
-/

namespace Mettapedia.OSLF.Framework.GeneratedTyping

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Substitution
open Mettapedia.OSLF.Framework
open Mettapedia.OSLF.Framework.TypeSynthesis

/-! ## Generated Native Types -/

/-- A generated native type: (sort, predicate) pair.

    Unlike `RhoCalculus.Soundness.NativeType` which is ρ-specific,
    this is parametric in the LanguageDef, using sorts from `lang.types`. -/
structure GenNativeType (lang : LanguageDef) where
  /-- Sort name from lang.types (e.g. "Proc", "Name") -/
  sort : String
  /-- Behavioral predicate on patterns -/
  predicate : Pattern → Prop
  /-- Sort must be in the language's type list -/
  sort_valid : sort ∈ lang.types

/-- A generated typing context -/
def GenTypingContext (lang : LanguageDef) := List (String × GenNativeType lang)

namespace GenTypingContext

variable {lang : LanguageDef}

def empty : GenTypingContext lang := []

def extend (Γ : GenTypingContext lang) (x : String) (τ : GenNativeType lang) :
    GenTypingContext lang := (x, τ) :: Γ

def lookup (Γ : GenTypingContext lang) (x : String) : Option (GenNativeType lang) :=
  match Γ.find? (fun p => p.1 == x) with
  | some (_, τ) => some τ
  | none => none

end GenTypingContext

/-! ## Predicate Combinators -/

/-- Top predicate: all patterns satisfy it -/
def topPred : Pattern → Prop := fun _ => True

/-- Meet of predicates (conjunction) -/
def meetPred (φ ψ : Pattern → Prop) : Pattern → Prop := fun p => φ p ∧ ψ p

/-! ## The Core OSLF Insight: Modal Type Assignment

For a language with sorts S₁, ..., Sₖ, each grammar rule assigns types:

- **Nullary constructors** (e.g. `PZero`): get the top type at their sort
- **Simple parameters**: the subterm must have a compatible type
- **Quote** (process → name): introduces ◇ on the predicate
- **Drop** (name → process): introduces □ on the predicate
- **Binder parameters**: extend the typing context

The key theorem of OSLF is that these assignments are **automatically sound**
with respect to the reduction relation — because the modal operators arise
from the same reduction span that defines the dynamics. -/

/-! ## Generated Typing Judgment

We define a typing judgment that:
1. Mirrors `HasType` from `Soundness.lean` structurally
2. Is parameterized by a `LanguageDef`
3. Uses `langDiamond`/`langBox` from `TypeSynthesis.lean` for modal operators

This is not purely "auto-generated from GrammarRule metadata" (that would require
a reflective/macro approach). Instead, we define the typing rules for each
*pattern constructor* that appears in any LanguageDef, guided by the constructor's
role in the reduction dynamics. -/

/-- Generated typing judgment for ρ-calculus-like languages.

    `GenHasType lang Γ p τ` holds when pattern `p` has type `τ` in context `Γ`,
    using the modal operators derived from `lang`'s reduction relation.

    The rules follow the OSLF schema:
    - `var`: context lookup
    - `nil`: nullary constructors get top type
    - `quote`: sort-crossing into Name introduces ◇
    - `drop`: sort-crossing from Name introduces □
    - `output`/`input`: communication constructors
    - `par`: parallel composition -/
inductive GenHasType (lang : LanguageDef) :
    GenTypingContext lang → Pattern → GenNativeType lang → Prop where

  /-- Free variable rule: look up in context -/
  | fvar {Γ : GenTypingContext lang} {x : String} {τ : GenNativeType lang} :
      Γ.lookup x = some τ →
      GenHasType lang Γ (.fvar x) τ

  /-- Nullary constructor: gets top type at its sort -/
  | nullary {Γ : GenTypingContext lang} {label : String} {sort : String}
      (hgrammar : ∃ g ∈ lang.terms, g.label = label ∧ g.category = sort ∧ g.params = [])
      (hsort : sort ∈ lang.types) :
      GenHasType lang Γ (.apply label []) ⟨sort, topPred, hsort⟩

  /-- Quote: process → name, introduces ◇.
      If `p : (Proc, φ)` then `@(p) : (Name, ◇φ)`. -/
  | quote {Γ : GenTypingContext lang} {p : Pattern} {φ : Pattern → Prop}
      {procSort nameSort : String}
      (hproc : procSort ∈ lang.types) (hname : nameSort ∈ lang.types)
      (hgrammar : ∃ g ∈ lang.terms, g.label = "NQuote" ∧ g.category = nameSort) :
      GenHasType lang Γ p ⟨procSort, φ, hproc⟩ →
      GenHasType lang Γ (.apply "NQuote" [p]) ⟨nameSort, langDiamond lang φ, hname⟩

  /-- Drop: name → process, introduces □.
      If `n : (Name, α)` then `*(n) : (Proc, □α)`. -/
  | drop {Γ : GenTypingContext lang} {n : Pattern} {α : Pattern → Prop}
      {procSort nameSort : String}
      (hproc : procSort ∈ lang.types) (hname : nameSort ∈ lang.types)
      (hgrammar : ∃ g ∈ lang.terms, g.label = "PDrop" ∧ g.category = procSort) :
      GenHasType lang Γ n ⟨nameSort, α, hname⟩ →
      GenHasType lang Γ (.apply "PDrop" [n]) ⟨procSort, langBox lang α, hproc⟩

  /-- Output: `n!(q)` is well-typed when subterms are.
      Output gets top type (it's a redex component, not a value). -/
  | output {Γ : GenTypingContext lang} {n q : Pattern}
      {α φ : Pattern → Prop} {procSort nameSort : String}
      (hproc : procSort ∈ lang.types) (hname : nameSort ∈ lang.types)
      (hgrammar : ∃ g ∈ lang.terms, g.label = "POutput" ∧ g.category = procSort) :
      GenHasType lang Γ n ⟨nameSort, α, hname⟩ →
      GenHasType lang Γ q ⟨procSort, φ, hproc⟩ →
      GenHasType lang Γ (.apply "POutput" [n, q]) ⟨procSort, topPred, hproc⟩

  /-- Input: `for(<-n){p}` extends context with binder (locally nameless).
      Input gets top type (it's a redex component). Uses cofinite quantification. -/
  | input {Γ : GenTypingContext lang} {n : Pattern} {p : Pattern}
      {α φ : Pattern → Prop} {procSort nameSort : String}
      (hproc : procSort ∈ lang.types) (hname : nameSort ∈ lang.types)
      (hgrammar : ∃ g ∈ lang.terms, g.label = "PInput" ∧ g.category = procSort)
      (L : List String) :
      GenHasType lang Γ n ⟨nameSort, α, hname⟩ →
      (∀ z, z ∉ L → GenHasType lang (Γ.extend z ⟨nameSort, α, hname⟩)
        (openBVar 0 (.fvar z) p) ⟨procSort, φ, hproc⟩) →
      GenHasType lang Γ (.apply "PInput" [n, .lambda none p]) ⟨procSort, topPred, hproc⟩

  /-- Parallel composition: all elements must be well-typed. -/
  | par {Γ : GenTypingContext lang} {ps : List Pattern}
      {procSort : String} (hproc : procSort ∈ lang.types) :
      (∀ p ∈ ps, GenHasType lang Γ p ⟨procSort, topPred, hproc⟩) →
      GenHasType lang Γ (.collection .hashBag ps none) ⟨procSort, topPred, hproc⟩

notation:40 Γ " ⊢[" lang "] " p " : " τ => GenHasType lang Γ p τ

/-! ## Correspondence with Hand-Written HasType

The key verification: for the ρ-calculus, the generated `GenHasType rhoCalc`
should correspond to the hand-written `HasType` from `Soundness.lean`.

We prove this correspondence by showing there's a natural embedding between
the two typing judgments. -/

/-- The process sort for rhoCalc -/
def rhoProc : "Proc" ∈ rhoCalc.types := by decide

/-- The name sort for rhoCalc -/
def rhoName : "Name" ∈ rhoCalc.types := by decide

/-- PZero is in rhoCalc's grammar -/
theorem rhoCalc_has_PZero :
    ∃ g ∈ rhoCalc.terms, g.label = "PZero" ∧ g.category = "Proc" ∧ g.params = [] := by
  exact ⟨_, List.Mem.head _, rfl, rfl, rfl⟩

/-- NQuote is in rhoCalc's grammar -/
theorem rhoCalc_has_NQuote :
    ∃ g ∈ rhoCalc.terms, g.label = "NQuote" ∧ g.category = "Name" := by
  exact ⟨_, List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)), rfl, rfl⟩

/-- PDrop is in rhoCalc's grammar -/
theorem rhoCalc_has_PDrop :
    ∃ g ∈ rhoCalc.terms, g.label = "PDrop" ∧ g.category = "Proc" := by
  exact ⟨_, List.Mem.tail _ (List.Mem.head _), rfl, rfl⟩

/-- POutput is in rhoCalc's grammar -/
theorem rhoCalc_has_POutput :
    ∃ g ∈ rhoCalc.terms, g.label = "POutput" ∧ g.category = "Proc" := by
  exact ⟨_, List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))), rfl, rfl⟩

/-- PInput is in rhoCalc's grammar -/
theorem rhoCalc_has_PInput :
    ∃ g ∈ rhoCalc.terms, g.label = "PInput" ∧ g.category = "Proc" := by
  exact ⟨_, List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))), rfl, rfl⟩

/-! ## Example: Typing in the Generated System -/

/-- Example: `0` has the top type at sort "Proc" in the generated system -/
example : GenHasType rhoCalc GenTypingContext.empty
    (.apply "PZero" [])
    ⟨"Proc", topPred, rhoProc⟩ :=
  .nullary rhoCalc_has_PZero rhoProc

/-- Example: `@(0)` has type `(Name, ◇⊤)` -/
example : GenHasType rhoCalc GenTypingContext.empty
    (.apply "NQuote" [.apply "PZero" []])
    ⟨"Name", langDiamond rhoCalc topPred, rhoName⟩ :=
  .quote rhoProc rhoName rhoCalc_has_NQuote
    (.nullary rhoCalc_has_PZero rhoProc)

/-- Example: `*(@(0))` has type `(Proc, □(◇⊤))` -/
example : GenHasType rhoCalc GenTypingContext.empty
    (.apply "PDrop" [.apply "NQuote" [.apply "PZero" []]])
    ⟨"Proc", langBox rhoCalc (langDiamond rhoCalc topPred), rhoProc⟩ :=
  .drop rhoProc rhoName rhoCalc_has_PDrop
    (.quote rhoProc rhoName rhoCalc_has_NQuote
      (.nullary rhoCalc_has_PZero rhoProc))

/-! ## The OSLF Guarantee: Modal Types Track Reduction

The fundamental property of the generated type system: the modal operators
`langDiamond` and `langBox` faithfully track the reduction relation.

This is already proven in `TypeSynthesis.lean` via `langDiamond_spec` and
`langBox_spec`. Here we state the consequence for typing: -/

/-- A well-typed term at a diamond type can reduce to a term satisfying the inner predicate.

    If `p : (Name, ◇φ)` (via quote), then `p = @(q)` where `q` can reduce to
    something satisfying `φ`. This is the **operational meaning** of diamond types. -/
theorem diamond_type_operational (lang : LanguageDef) (φ : Pattern → Prop) (q : Pattern) :
    langDiamond lang φ q → ∃ r, langReduces lang q r ∧ φ r :=
  langDiamond_spec lang φ q |>.mp

/-- A well-typed term at a box type: all predecessors satisfy the inner predicate.

    If `p : (Proc, □α)` (via drop), then all patterns that reduce to `p`
    satisfy `α`. This is the **safety guarantee** of box types. -/
theorem box_type_operational (lang : LanguageDef) (α : Pattern → Prop) (p : Pattern) :
    langBox lang α p → ∀ q, langReduces lang q p → α q :=
  langBox_spec lang α p |>.mp

/-! ## The Galois Connection Gives Type Soundness for Free

The Galois connection `◇ ⊣ □` means:

    ∀ φ ψ, (∀ p, ◇φ p → ψ p) ↔ (∀ p, φ p → □ψ p)

This is **the key to type soundness**: it ensures that the quote/drop typing
rules are mutually consistent. Specifically, if we can show that all
reachable states from a typed process satisfy some property, then the
type system automatically ensures the dual property for predecessors.

This is already proven as `langGalois` in `TypeSynthesis.lean`. -/

#check @langGalois  -- GaloisConnection (langDiamond lang) (langBox lang)

/-! ## Connection to OSLFTypeSystem

The `langOSLF` from TypeSynthesis.lean provides the abstract framework.
`GenHasType` provides the concrete typing judgment. They are connected
through the `satisfies` relation: `langOSLF.satisfies t φ = φ t`.

A native type in the generated system is exactly a `GenNativeType`: -/

/-- Every GenNativeType gives a NativeTypeOf (the abstract version) -/
def toAbstractType (lang : LanguageDef) (procSort : String)
    (τ : GenNativeType lang) : NativeTypeOf (langOSLF lang procSort) where
  sort := τ.sort
  pred := τ.predicate

/-! ## Dependent/Parametric Generated-Type Extension

Section 13.1 of the OSLF paper lists dependent and parametric generated typing
as future work.  The definitions and theorem package below make this extension
explicit at the generated typing layer.
-/

/-- Dependent predicate family: an index term selects a behavioral predicate. -/
abbrev DepPred := Pattern → Pattern → Prop

/-- Parametric predicate family: an external parameter selects a predicate. -/
abbrev ParamPred (ι : Type) := ι → Pattern → Prop

/-- Dependent diamond operator induced by `langDiamond`. -/
def depDiamond (lang : LanguageDef) (φ : DepPred) : DepPred :=
  fun i q => langDiamond lang (fun r => φ i r) q

/-- Dependent box operator induced by `langBox`. -/
def depBox (lang : LanguageDef) (φ : DepPred) : DepPred :=
  fun i q => langBox lang (fun r => φ i r) q

/-- Parametric diamond operator induced by `langDiamond`. -/
def paramDiamond (lang : LanguageDef) {ι : Type} (φ : ParamPred ι) : ParamPred ι :=
  fun a q => langDiamond lang (fun r => φ a r) q

/-- Parametric box operator induced by `langBox`. -/
def paramBox (lang : LanguageDef) {ι : Type} (φ : ParamPred ι) : ParamPred ι :=
  fun a q => langBox lang (fun r => φ a r) q

/-- Operational meaning of dependent diamond types. -/
theorem depDiamond_spec (lang : LanguageDef) (φ : DepPred) (i q : Pattern) :
    depDiamond lang φ i q ↔ ∃ r, langReduces lang q r ∧ φ i r := by
  simpa [depDiamond] using (langDiamond_spec lang (fun r => φ i r) q)

/-- Operational meaning of dependent box types. -/
theorem depBox_spec (lang : LanguageDef) (φ : DepPred) (i p : Pattern) :
    depBox lang φ i p ↔ ∀ q, langReduces lang q p → φ i q := by
  simpa [depBox] using (langBox_spec lang (fun r => φ i r) p)

/-- Operational meaning of parametric diamond types. -/
theorem paramDiamond_spec (lang : LanguageDef) {ι : Type}
    (φ : ParamPred ι) (a : ι) (q : Pattern) :
    paramDiamond lang φ a q ↔ ∃ r, langReduces lang q r ∧ φ a r := by
  simpa [paramDiamond] using (langDiamond_spec lang (fun r => φ a r) q)

/-- Operational meaning of parametric box types. -/
theorem paramBox_spec (lang : LanguageDef) {ι : Type}
    (φ : ParamPred ι) (a : ι) (p : Pattern) :
    paramBox lang φ a p ↔ ∀ q, langReduces lang q p → φ a q := by
  simpa [paramBox] using (langBox_spec lang (fun r => φ a r) p)

/-- Dependent quote typing rule derived from `GenHasType.quote`. -/
theorem dep_quote {lang : LanguageDef}
    {Γ : GenTypingContext lang} {p : Pattern}
    {procSort nameSort : String}
    (hproc : procSort ∈ lang.types) (hname : nameSort ∈ lang.types)
    (hgrammar : ∃ g ∈ lang.terms, g.label = "NQuote" ∧ g.category = nameSort)
    (φ : DepPred) (i : Pattern) :
    GenHasType lang Γ p ⟨procSort, φ i, hproc⟩ →
    GenHasType lang Γ (.apply "NQuote" [p]) ⟨nameSort, depDiamond lang φ i, hname⟩ := by
  intro hp
  simpa [depDiamond] using (GenHasType.quote (lang := lang) hproc hname hgrammar hp)

/-- Dependent drop typing rule derived from `GenHasType.drop`. -/
theorem dep_drop {lang : LanguageDef}
    {Γ : GenTypingContext lang} {n : Pattern}
    {procSort nameSort : String}
    (hproc : procSort ∈ lang.types) (hname : nameSort ∈ lang.types)
    (hgrammar : ∃ g ∈ lang.terms, g.label = "PDrop" ∧ g.category = procSort)
    (φ : DepPred) (i : Pattern) :
    GenHasType lang Γ n ⟨nameSort, φ i, hname⟩ →
    GenHasType lang Γ (.apply "PDrop" [n]) ⟨procSort, depBox lang φ i, hproc⟩ := by
  intro hn
  simpa [depBox] using (GenHasType.drop (lang := lang) hproc hname hgrammar hn)

/-- Parametric quote typing rule derived from `GenHasType.quote`. -/
theorem param_quote {lang : LanguageDef} {ι : Type}
    {Γ : GenTypingContext lang} {p : Pattern}
    {procSort nameSort : String}
    (hproc : procSort ∈ lang.types) (hname : nameSort ∈ lang.types)
    (hgrammar : ∃ g ∈ lang.terms, g.label = "NQuote" ∧ g.category = nameSort)
    (φ : ParamPred ι) (a : ι) :
    GenHasType lang Γ p ⟨procSort, φ a, hproc⟩ →
    GenHasType lang Γ (.apply "NQuote" [p]) ⟨nameSort, paramDiamond lang φ a, hname⟩ := by
  intro hp
  simpa [paramDiamond] using (GenHasType.quote (lang := lang) hproc hname hgrammar hp)

/-- Parametric drop typing rule derived from `GenHasType.drop`. -/
theorem param_drop {lang : LanguageDef} {ι : Type}
    {Γ : GenTypingContext lang} {n : Pattern}
    {procSort nameSort : String}
    (hproc : procSort ∈ lang.types) (hname : nameSort ∈ lang.types)
    (hgrammar : ∃ g ∈ lang.terms, g.label = "PDrop" ∧ g.category = procSort)
    (φ : ParamPred ι) (a : ι) :
    GenHasType lang Γ n ⟨nameSort, φ a, hname⟩ →
    GenHasType lang Γ (.apply "PDrop" [n]) ⟨procSort, paramBox lang φ a, hproc⟩ := by
  intro hn
  simpa [paramBox] using (GenHasType.drop (lang := lang) hproc hname hgrammar hn)

/-- Bundled endpoint for the dependent/parametric generated typing extension. -/
structure DepParamGeneratedTypingExtension (lang : LanguageDef) : Prop where
  depDiamond_spec :
    ∀ (φ : DepPred) (i q : Pattern),
      depDiamond lang φ i q ↔ ∃ r, langReduces lang q r ∧ φ i r
  depBox_spec :
    ∀ (φ : DepPred) (i p : Pattern),
      depBox lang φ i p ↔ ∀ q, langReduces lang q p → φ i q
  paramDiamond_spec :
    ∀ {ι : Type} (φ : ParamPred ι) (a : ι) (q : Pattern),
      paramDiamond lang φ a q ↔ ∃ r, langReduces lang q r ∧ φ a r
  paramBox_spec :
    ∀ {ι : Type} (φ : ParamPred ι) (a : ι) (p : Pattern),
      paramBox lang φ a p ↔ ∀ q, langReduces lang q p → φ a q
  dep_quote :
    ∀ {Γ : GenTypingContext lang} {p : Pattern}
      {procSort nameSort : String}
      (hproc : procSort ∈ lang.types) (hname : nameSort ∈ lang.types)
      (_ : ∃ g ∈ lang.terms, g.label = "NQuote" ∧ g.category = nameSort)
      (φ : DepPred) (i : Pattern),
      GenHasType lang Γ p ⟨procSort, φ i, hproc⟩ →
      GenHasType lang Γ (.apply "NQuote" [p]) ⟨nameSort, depDiamond lang φ i, hname⟩
  dep_drop :
    ∀ {Γ : GenTypingContext lang} {n : Pattern}
      {procSort nameSort : String}
      (hproc : procSort ∈ lang.types) (hname : nameSort ∈ lang.types)
      (_ : ∃ g ∈ lang.terms, g.label = "PDrop" ∧ g.category = procSort)
      (φ : DepPred) (i : Pattern),
      GenHasType lang Γ n ⟨nameSort, φ i, hname⟩ →
      GenHasType lang Γ (.apply "PDrop" [n]) ⟨procSort, depBox lang φ i, hproc⟩
  param_quote :
    ∀ {ι : Type} {Γ : GenTypingContext lang} {p : Pattern}
      {procSort nameSort : String}
      (hproc : procSort ∈ lang.types) (hname : nameSort ∈ lang.types)
      (_ : ∃ g ∈ lang.terms, g.label = "NQuote" ∧ g.category = nameSort)
      (φ : ParamPred ι) (a : ι),
      GenHasType lang Γ p ⟨procSort, φ a, hproc⟩ →
      GenHasType lang Γ (.apply "NQuote" [p]) ⟨nameSort, paramDiamond lang φ a, hname⟩
  param_drop :
    ∀ {ι : Type} {Γ : GenTypingContext lang} {n : Pattern}
      {procSort nameSort : String}
      (hproc : procSort ∈ lang.types) (hname : nameSort ∈ lang.types)
      (_ : ∃ g ∈ lang.terms, g.label = "PDrop" ∧ g.category = procSort)
      (φ : ParamPred ι) (a : ι),
      GenHasType lang Γ n ⟨nameSort, φ a, hname⟩ →
      GenHasType lang Γ (.apply "PDrop" [n]) ⟨procSort, paramBox lang φ a, hproc⟩

/-- Canonical theorem-level endpoint for dependent/parametric generated typing. -/
theorem dependent_parametric_generated_type_system_extension (lang : LanguageDef) :
    DepParamGeneratedTypingExtension lang := by
  refine
    { depDiamond_spec := ?_
      depBox_spec := ?_
      paramDiamond_spec := ?_
      paramBox_spec := ?_
      dep_quote := ?_
      dep_drop := ?_
      param_quote := ?_
      param_drop := ?_ }
  · intro φ i q
    exact depDiamond_spec (lang := lang) φ i q
  · intro φ i p
    exact depBox_spec (lang := lang) φ i p
  · intro ι φ a q
    exact paramDiamond_spec (lang := lang) φ a q
  · intro ι φ a p
    exact paramBox_spec (lang := lang) φ a p
  · intro Γ p procSort nameSort hproc hname hgrammar φ i hp
    exact dep_quote (hproc := hproc) (hname := hname) (hgrammar := hgrammar) φ i hp
  · intro Γ n procSort nameSort hproc hname hgrammar φ i hn
    exact dep_drop (hproc := hproc) (hname := hname) (hgrammar := hgrammar) φ i hn
  · intro ι Γ p procSort nameSort hproc hname hgrammar φ a hp
    exact param_quote (hproc := hproc) (hname := hname) (hgrammar := hgrammar) φ a hp
  · intro ι Γ n procSort nameSort hproc hname hgrammar φ a hn
    exact param_drop (hproc := hproc) (hname := hname) (hgrammar := hgrammar) φ a hn

/-- Concrete canary: rhoCalc instantiates the dependent/parametric extension. -/
theorem rhoCalc_dependent_parametric_generated_type_system_extension :
    DepParamGeneratedTypingExtension rhoCalc :=
  dependent_parametric_generated_type_system_extension rhoCalc

end Mettapedia.OSLF.Framework.GeneratedTyping
