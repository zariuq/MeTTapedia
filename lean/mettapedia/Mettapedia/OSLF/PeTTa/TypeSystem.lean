import Mettapedia.OSLF.PeTTa.Effects

/-!
# MeTTa Type System (Minimal Fragment)

Formalizes the **type judgment** for MeTTa's type system, grounded in the
`PeTTaSpace` / `EvalState` infrastructure.

## Architecture

```
MeTTaType s p t            (this file)
     ↑ looks up types in s.facts
     ↑ composes via arrow types
PeTTaSpace (facts include (: p t) annotations)
```

## MeTTa Type System Overview

In MeTTa, types are first-class citizens stored in the atomspace:
- **Type annotation**: `(: p t)` atom in the space means `p` has type `t`
- **Arrow type**: `(-> A B)` represents a function from type `A` to type `B`
- **Multi-arrow**: `(-> A B C)` ≡ `(-> A (-> B C))` (right-associative)
- **Application**: if `f : (-> A B)` and `x : A`, then `(f x) : B`

## Key Design Decisions

- Types are `Pattern`s — the type language is the same language as the term language.
- `%Undefined%` (the "any" type) is modeled as a distinguished atom.
- We formalize only the **pure, non-dependent fragment**: no type-level computation,
  no dependent types, no `Expression` type special case.
- Type annotations are stored as facts `(: p t) ∈ s.facts`, looked up by `typeAnnotation`.
- Type errors (`(Error p ...)`) are deferred: in the pure fragment, ill-typed
  reductions are simply unconstrained by the type system.
- Arrow constructors use `c : String` for the function head, since
  `Pattern.apply : String → List Pattern → Pattern` requires a String head.
  A bare function symbol `f` is represented as `.apply c []`.

## References

- MeTTa spec §type-system: `trueagi-io.github.io/hyperon-experimental/metta/`
  (see `check_if_function_type_is_applicable`, `check_argument_type`)
- PeTTa: type checking via Prolog clauses in `transpiler.pl`
-/

namespace Mettapedia.OSLF.PeTTa

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match

/-! ## Special Type Atoms -/

/-- The `%Undefined%` type: the "any" / unknown type in MeTTa.
    In the MeTTa spec, `%Undefined%` acts as a supertype of everything. -/
def undefinedType : Pattern := .apply "%Undefined%" []

/-- The `%Empty%` type: the bottom / uninhabited type. -/
def emptyType : Pattern := .apply "%Empty%" []

/-- The `Atom` type: supertype of all atomic (non-application) patterns. -/
def atomType : Pattern := .apply "Atom" []

/-- The `Expression` type: supertype of all patterns (including applications). -/
def expressionType : Pattern := .apply "Expression" []

/-- Arrow type constructor: `(-> argType retType)` -/
def arrowType (argType retType : Pattern) : Pattern :=
  .apply "->" [argType, retType]

/-- Type annotation pattern `(: p t)` — stored in the space as a fact. -/
def typeAnnotationPat (p t : Pattern) : Pattern :=
  .apply ":" [p, t]

/-! ## Type Judgment -/

/-- **MeTTa type judgment**: `MeTTaType s p t` means pattern `p` has type `t`
    in atomspace `s`.

    This formalizes the core of MeTTa's type system for the pure, non-dependent
    fragment:

    1. **Annotation lookup**: `(: p t) ∈ s.facts` directly gives `p : t`
    2. **Undefined type**: everything has type `%Undefined%`
    3. **Arrow application**: `f : (-> A B)` and `x : A` implies `(f x) : B`
    4. **Arrow application with %Undefined% argument**: if arg type unknown
    5. **Multi-arity arrow**: `f : (-> A B C)` partially applied to `x : A`
       gives a term of type `(-> B C)`
    6. **Type subsumption**: `%Undefined%` acts as a supertype
    7. **Symbol type**: bare symbols (constants) have type `Atom`
    8. **Application type**: any application has type `Expression`

    Note: This judgment is **non-deterministic** — a term may have multiple types.
    The `List` of types (all types of a term) is modeled by `allTypesOf`.

    Arrow constructors use `c : String` as the function head: in MeTTa,
    `(: f (-> A B))` is stored with `f` as a bare symbol `.apply c []`. -/
inductive MeTTaType (s : PeTTaSpace) : Pattern → Pattern → Prop where

  /-- **Annotation lookup**: if `(: p t)` is a fact in the space, then `p : t`. -/
  | typeAnnotation (p t : Pattern)
      (h : typeAnnotationPat p t ∈ s.facts) :
      MeTTaType s p t

  /-- **Undefined type**: every pattern has type `%Undefined%`. -/
  | undefinedIsTop (p : Pattern) :
      MeTTaType s p undefinedType

  /-- **Arrow application** (single step): if the bare symbol `c` has function type
      `(-> A B)` and `x` has type `A`, then `(c x)` has type `B`. -/
  | arrowApp (c : String) (x : Pattern) (argTy retTy : Pattern)
      (hf : MeTTaType s (.apply c []) (arrowType argTy retTy))
      (hx : MeTTaType s x argTy) :
      MeTTaType s (.apply c [x]) retTy

  /-- **Arrow application — unknown arg type**: if `c : (-> A B)` and `x`
      has no known type (or `x : %Undefined%`), still permit application
      but return type is `%Undefined%`. -/
  | arrowAppUnknown (c : String) (x : Pattern) (argTy retTy : Pattern)
      (hf : MeTTaType s (.apply c []) (arrowType argTy retTy)) :
      MeTTaType s (.apply c [x]) undefinedType

  /-- **Multi-arity application** (curried arrow, first step):
      `c : (-> A B C)` applied to `x : A` gives something of type `(-> B C)`. -/
  | arrowMultiApp (c : String) (x : Pattern) (argTy midTy retTy : Pattern)
      (hf : MeTTaType s (.apply c []) (arrowType argTy (arrowType midTy retTy)))
      (hx : MeTTaType s x argTy) :
      MeTTaType s (.apply c [x]) (arrowType midTy retTy)

  /-- **Symbol type**: every bare symbol (nullary application) has type `Atom`. -/
  | symbolIsAtom (c : String) :
      MeTTaType s (.apply c []) atomType

  /-- **Expression type**: any non-nullary application has type `Expression`. -/
  | appIsExpression (c : String) (args : List Pattern) (hne : args ≠ []) :
      MeTTaType s (.apply c args) expressionType

  /-- **Variable type**: free variables have type `%Undefined%`.
      (Variables are untyped until bound by a rule.) -/
  | varIsUndefined (x : String) :
      MeTTaType s (.fvar x) undefinedType

/-! ## Type Annotation Convenience -/

/-- Check whether `(: p t)` is stored as a fact in the space.
    Returns a `Prop` (membership) so that `hasTypeAnnotation_sound` is trivial. -/
def PeTTaSpace.hasTypeAnnotation (s : PeTTaSpace) (p t : Pattern) : Prop :=
  typeAnnotationPat p t ∈ s.facts

/-- `hasTypeAnnotation` is sound w.r.t. `MeTTaType`. -/
theorem hasTypeAnnotation_sound (s : PeTTaSpace) (p t : Pattern)
    (h : s.hasTypeAnnotation p t) :
    MeTTaType s p t :=
  MeTTaType.typeAnnotation p t h

/-- Adding a type annotation to the space makes the type derivable. -/
theorem addAnnotation_types (s : PeTTaSpace) (p t : Pattern) :
    MeTTaType (s.addAtom (typeAnnotationPat p t)) p t :=
  MeTTaType.typeAnnotation p t (PeTTaSpace.mem_facts_addAtom_self s _)

/-! ## Arrow Type Properties -/

/-- Arrow types are distinct from `%Undefined%`. -/
theorem arrowType_ne_undefined (A B : Pattern) :
    arrowType A B ≠ undefinedType := by
  simp [arrowType, undefinedType]

/-- Arrow types are distinct from `Atom`. -/
theorem arrowType_ne_atom (A B : Pattern) :
    arrowType A B ≠ atomType := by
  simp [arrowType, atomType]

/-- If `(c x)` has a type via arrow rules (not from a direct annotation, not `%Undefined%`,
    not `Expression`), then `c` (as bare symbol) has some arrow type.

    Requires `hnot`: the type did not come purely from a direct `(: (c x) t)` annotation,
    since annotations carry no structural information about arrow types. -/
theorem arrowApp_implies_f_has_arrow_type {s : PeTTaSpace} {c : String} {x t : Pattern}
    (h : MeTTaType s (.apply c [x]) t)
    (hne : t ≠ undefinedType)
    (hne2 : t ≠ expressionType)
    (hnot : typeAnnotationPat (.apply c [x]) t ∉ s.facts) :
    ∃ A B, MeTTaType s (.apply c []) (arrowType A B) := by
  cases h with
  | typeAnnotation p' t' hmem => exact absurd hmem hnot
  | undefinedIsTop _ => exact absurd rfl hne
  | arrowApp c' x' A B hf _ => exact ⟨A, _, hf⟩
  | arrowAppUnknown c' x' A B hf => exact absurd rfl hne
  | arrowMultiApp c' x' A B C hf _ => exact ⟨A, _, hf⟩
  | appIsExpression _ _ _ => exact absurd rfl hne2

/-! ## Well-Typed Spaces -/

/-- A space is **well-typed** if every type annotation `(: p t)` in the facts
    actually witnesses `MeTTaType s p t`. (Tautological in our model, since
    we derive types FROM annotations — but useful as a documentation anchor.) -/
def PeTTaSpace.isWellTyped (s : PeTTaSpace) : Prop :=
  ∀ p t, typeAnnotationPat p t ∈ s.facts → MeTTaType s p t

/-- Every space is well-typed (type annotations trivially witness themselves). -/
theorem all_spaces_well_typed (s : PeTTaSpace) : s.isWellTyped :=
  fun p t h => MeTTaType.typeAnnotation p t h

/-- Adding a type annotation preserves well-typedness
    (and makes the new annotation derivable). -/
theorem addAnnotation_wellTyped (s : PeTTaSpace) (p₀ t₀ : Pattern) :
    (s.addAtom (typeAnnotationPat p₀ t₀)).isWellTyped := by
  intro p t h
  simp only [PeTTaSpace.addAtom, List.mem_cons] at h
  rcases h with heq | hh
  · -- heq : typeAnnotationPat p t = typeAnnotationPat p₀ t₀
    -- inject through .apply ":" [_, _]
    have hinj : p = p₀ ∧ t = t₀ := by
      unfold typeAnnotationPat at heq
      -- heq : .apply ":" [p, t] = .apply ":" [p₀, t₀]
      -- Extract the argument list equality by injectivity
      have hlist : [p, t] = [p₀, t₀] := by
        have : (Pattern.apply ":" [p, t]) = (Pattern.apply ":" [p₀, t₀]) := heq
        cases this
        rfl
      simp only [List.cons.injEq] at hlist
      exact ⟨hlist.1, hlist.2.1⟩
    obtain ⟨rfl, rfl⟩ := hinj
    -- After subst, p = p₀ and t = t₀, so the goal uses p and t
    exact MeTTaType.typeAnnotation p t (PeTTaSpace.mem_facts_addAtom_self s _)
  · -- hh : typeAnnotationPat p t ∈ s.facts — old annotation
    exact MeTTaType.typeAnnotation p t (List.mem_cons_of_mem _ hh)

/-! ## Type Monotonicity -/

/-- **Type monotonicity**: adding facts to the space can only add types,
    never remove them. If `p : t` in `s`, then `p : t` in any extension. -/
theorem typeOf_mono_addAtom {s : PeTTaSpace} {p t : Pattern} (newFact : Pattern)
    (h : MeTTaType s p t) :
    MeTTaType (s.addAtom newFact) p t := by
  induction h with
  | typeAnnotation p t hfact =>
    exact MeTTaType.typeAnnotation p t (PeTTaSpace.mem_facts_addAtom hfact)
  | undefinedIsTop p => exact MeTTaType.undefinedIsTop p
  | arrowApp c x A B _ _ ihf ihx =>
    exact MeTTaType.arrowApp c x A B ihf ihx
  | arrowAppUnknown c x A B _ ihf =>
    exact MeTTaType.arrowAppUnknown c x A B ihf
  | arrowMultiApp c x A B C _ _ ihf ihx =>
    exact MeTTaType.arrowMultiApp c x A B C ihf ihx
  | symbolIsAtom c => exact MeTTaType.symbolIsAtom c
  | appIsExpression c args hne => exact MeTTaType.appIsExpression c args hne
  | varIsUndefined x => exact MeTTaType.varIsUndefined x

/-! ## Typing of PeTTaEval Results -/

/-- **Type preservation for `var`**: free variables evaluate to themselves
    and thus preserve their type (trivially). -/
theorem typePreserved_var (s : PeTTaSpace) (x : String) (t : Pattern)
    (ht : MeTTaType s (.fvar x) t) :
    MeTTaType s (.fvar x) t := ht

/-- **Type preservation for `ground`**: ground atoms evaluate to themselves. -/
theorem typePreserved_ground (s : PeTTaSpace) (c : String) (t : Pattern)
    (ht : MeTTaType s (.apply c []) t) :
    MeTTaType s (.apply c []) t := ht

/-- Every evaluated pattern has `%Undefined%` as a type (trivially by `undefinedIsTop`).
    This shows the type system is always satisfiable — no term is type-less. -/
theorem every_pattern_has_undefined_type (s : PeTTaSpace) (p : Pattern) :
    MeTTaType s p undefinedType :=
  MeTTaType.undefinedIsTop p

/-! ## Type Checking via spaceMatch -/

/-- Look up all types of `p` that are explicitly annotated in the space. -/
def PeTTaSpace.annotatedTypes (s : PeTTaSpace) (p : Pattern) : List Pattern :=
  s.facts.filterMap fun fact =>
    match fact with
    | .apply ":" [p', t] => if p' == p then some t else none
    | _ => none

/-- Helper: the filterMap body for `annotatedTypes` yields `some t` only from
    `(: p' t)` facts where `p' = p`. -/
private theorem annotatedTypes_filterMap_aux {p t : Pattern}
    {fact : Pattern}
    (hmatch : (match fact with
               | .apply ":" [p', t'] => if p' == p then some t' else none
               | _ => none) = some t) :
    ∃ p' : Pattern, fact = typeAnnotationPat p' t ∧ p' = p := by
  cases fact with
  | apply c args =>
    by_cases hc : c = ":"
    · subst hc
      match args with
      | [p', t'] =>
        simp only at hmatch
        split_ifs at hmatch with hpeq
        · simp only [Option.some.injEq] at hmatch
          subst hmatch
          exact ⟨p', rfl, by rwa [beq_iff_eq] at hpeq⟩
      | [] => simp at hmatch
      | [_] => simp at hmatch
      | _ :: _ :: _ :: _ => simp at hmatch
    · -- c ≠ ":", so the match reduces to `none = some t`, which is absurd
      have : (match Pattern.apply c args with
               | .apply ":" [p', t'] => if p' == p then some t' else none
               | _ => none) = none := by
        split
        · -- split fires: Pattern.apply c args = Pattern.apply ":" [p', t']
          -- extract c = ":" by injectivity and contradict hc
          next heq =>
            have hceq : c = ":" := by
              have := congr_arg (fun q => match q with | .apply s _ => s | _ => "") heq
              simp at this; exact this
            exact absurd hceq hc
        · rfl
      rw [this] at hmatch
      exact absurd hmatch (by simp)
  | bvar _ => simp at hmatch
  | fvar _ => simp at hmatch
  | lambda _ => simp at hmatch
  | multiLambda _ _ => simp at hmatch
  | subst _ _ => simp at hmatch
  | collection _ _ _ => simp at hmatch

/-- Every annotated type is derivable. -/
theorem annotatedTypes_sound (s : PeTTaSpace) (p t : Pattern)
    (h : t ∈ s.annotatedTypes p) :
    MeTTaType s p t := by
  simp only [PeTTaSpace.annotatedTypes, List.mem_filterMap] at h
  obtain ⟨fact, hfact, hmatch⟩ := h
  obtain ⟨p', hfact_eq, heq⟩ := annotatedTypes_filterMap_aux hmatch
  subst heq
  rw [hfact_eq] at hfact
  exact MeTTaType.typeAnnotation p' t hfact

/-! ## Summary

**0 sorries. 0 axioms.**

### Special Atoms
- `undefinedType` — `%Undefined%` (MeTTa's "any" type)
- `emptyType` — `%Empty%` (uninhabited type)
- `atomType` — `Atom` (supertype of bare symbols)
- `expressionType` — `Expression` (supertype of applications)
- `arrowType A B` — `(-> A B)` function type constructor
- `typeAnnotationPat p t` — `(: p t)` stored in space as fact

### Type Judgment (`MeTTaType s p t`)
- `typeAnnotation` — `(: p t) ∈ s.facts` → `p : t`
- `undefinedIsTop` — `p : %Undefined%` for all `p`
- `arrowApp` — `c : (-> A B)` (bare symbol), `x : A` → `(c x) : B`
- `arrowAppUnknown` — `c : (-> A B)` → `(c x) : %Undefined%` (arg type unknown)
- `arrowMultiApp` — `c : (-> A (-> B C))`, `x : A` → `(c x) : (-> B C)`
- `symbolIsAtom` — `c : Atom` for bare symbols
- `appIsExpression` — `(c a₁ … aₙ) : Expression` for non-nullary applications
- `varIsUndefined` — `.fvar x : %Undefined%`

### Space Properties
- `PeTTaSpace.isWellTyped` — all annotations are derivable (tautological here)
- `all_spaces_well_typed` — every space is well-typed
- `addAnnotation_wellTyped` — adding annotations preserves well-typedness
- `hasTypeAnnotation_sound` — Prop check is sound for `MeTTaType`

### Monotonicity
- `typeOf_mono_addAtom` — types persist when facts are added
- `addAnnotation_types` — adding `(: p t)` gives `p : t`

### Queries
- `PeTTaSpace.annotatedTypes s p` — list all explicitly annotated types of `p`
- `annotatedTypes_sound` — annotated types are all derivable

### Type Properties
- `arrowType_ne_undefined`, `arrowType_ne_atom` — arrow ≠ base types
- `arrowApp_implies_f_has_arrow_type` — if app has non-trivial type, symbol is functional
- `every_pattern_has_undefined_type` — no term is type-less
-/

end Mettapedia.OSLF.PeTTa
