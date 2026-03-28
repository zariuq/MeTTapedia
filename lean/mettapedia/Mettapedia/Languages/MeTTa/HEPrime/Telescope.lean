import Mettapedia.Languages.MeTTa.HE.Matching

/-!
# HE′ (he_prime) — Dependent Telescope Extension for MeTTa

A principled, constructive extension of HE MeTTa's function type system.

## Motivation

In current HE, a function type `(-> (: $e (target $snp $gene)) (result $snp))` treats
`(: $e (target $snp $gene))` as a *literal atom* in the domain position. The type checker
compares this entire atom against the argument's type, which is just `(target $snp $gene)`.
This structural mismatch causes `BadArgType`.

HE′ adds a *telescope interpretation*: domain positions of the form `(: $x T)` are
elaborated as dependent binders. The variable `$x` is bound to the concrete argument
upon successful type matching, and subsequent domains and the codomain may depend on
values bound by earlier domains.

## Design Principles (Council quorum 91%)

1. **Extension, not replacement.** HE′ is an opt-in layer. Standard HE behavior
   (`he_compat`, `he_extended`) is preserved exactly.
2. **Left-to-right telescope walk.** Domains are checked in order; each successful
   check extends the binding environment.
3. **Generic and reusable.** The telescope semantics is parameterized over the
   matching algorithm, separating structure from implementation.

## References

- CeTTa: `src/eval.c` (`split_dependent_domain`, `bind_domain_binder`,
  `infer_dependent_application_types`)
- Discrepancy: `tests/DISCREPANCIES.md` C4
- Martin-Löf (1984), Pfenning (2001), McBride & McKinna (2004)
-/

namespace Mettapedia.Languages.MeTTa.HEPrime

open Mettapedia.Languages.MeTTa.OSLFCore (Atom GroundedValue)
open Mettapedia.Languages.MeTTa.HE (Bindings)

/-! ## Domain Classification -/

/-- A domain in a function type's telescope.
    - `plain T` — the argument must have type `T`, no witness binding.
    - `dep x T` — the argument must have type `T`, and its concrete value
      is bound to the variable named `x` for subsequent elaboration. -/
inductive Domain where
  | plain (ty : Atom) : Domain
  | dep (binder : String) (ty : Atom) : Domain
  deriving Repr, DecidableEq, Inhabited

/-- Extract the type body from a domain, ignoring the binder. -/
def Domain.typeBody : Domain → Atom
  | .plain ty => ty
  | .dep _ ty => ty

/-- The binder variable name, if this is a dependent domain. -/
def Domain.binderName? : Domain → Option String
  | .plain _ => none
  | .dep x _ => some x

/-! ## Splitting: Atom → Domain -/

/-- Classify an atom in a domain position.
    `(: (Atom.var x) T)` → `Domain.dep x T`; anything else → `Domain.plain atom`.
    **HE′ only.** Under standard HE, all domains are `plain`. -/
def splitDomain : Atom → Domain
  | .expression [.symbol ":", .var x, ty] => .dep x ty
  | other => .plain other

/-- Under standard HE semantics, all domains are plain. -/
def splitDomainHE : Atom → Domain
  | a => .plain a

/-! ## Telescope Structure -/

/-- An elaborated function type: a list of domains followed by a codomain. -/
structure FunTelescope where
  domains : List Domain
  codomain : Atom
  deriving Repr, DecidableEq, Inhabited

/-- Parse an arrow-type atom into a telescope using the given domain splitter. -/
def arrowToTelescope (split : Atom → Domain) : Atom → Option FunTelescope
  | .expression ((.symbol "->") :: rest) =>
    if h : rest.length ≥ 2 then
      let domains := (rest.dropLast).map split
      have hne : rest ≠ [] := by intro he; simp [he] at h
      let codomain := rest.getLast hne
      some ⟨domains, codomain⟩
    else none
  | _ => none

def arrowToTelescopeHEPrime := arrowToTelescope splitDomain
def arrowToTelescopeHE := arrowToTelescope splitDomainHE

/-! ## Elaboration Configuration

The telescope semantics is parameterized over:
- a type oracle (`getTypes : Atom → List Atom`)
- a type matcher (`matchFn : Atom → Atom → Option Bindings`)

This separates the telescope structure from the matching algorithm,
allowing kernel-decidable proofs with simple matchers while the
production system uses HE's full `matchTypes`. -/

/-- Configuration for telescope elaboration. -/
structure ElabConfig where
  /-- Return the known types of an atom (from space, intrinsics, etc.). -/
  getTypes : Atom → List Atom
  /-- Match expected type against actual type. Returns bindings on success. -/
  matchFn : Atom → Atom → Option Bindings
  deriving Inhabited

/-- Result of elaborating one argument. -/
inductive ElabStep where
  | ok (env : Bindings) : ElabStep
  | fail : ElabStep
  deriving Repr, DecidableEq

/-- Elaborate a single argument against a domain under the current environment.
    1. Apply accumulated bindings to the domain type.
    2. Match the expected type against the argument's actual type.
    3. If the domain is a dependent binder, bind the argument to the binder variable.
    Mirrors CeTTa's telescope walk inner loop. -/
def elabOneArg (cfg : ElabConfig) (env : Bindings) (dom : Domain) (arg : Atom)
    (fuel : Nat) : ElabStep :=
  let expectedType := env.apply dom.typeBody fuel
  let argTypes := cfg.getTypes arg
  let result := argTypes.findSome? fun atype => cfg.matchFn expectedType atype
  match result with
  | none => .fail
  | some matchedBindings =>
    let env' : Bindings := {
      assignments := env.assignments ++ matchedBindings.assignments
      equalities := env.equalities ++ matchedBindings.equalities }
    match dom.binderName? with
    | none => .ok env'
    | some x => .ok (env'.assign x arg)

/-- Elaborate all arguments against a telescope, threading bindings left-to-right. -/
def elabTelescope (cfg : ElabConfig) (tel : FunTelescope) (args : List Atom)
    (fuel : Nat) : Option Bindings :=
  if tel.domains.length ≠ args.length then none
  else
    let pairs := tel.domains.zip args
    pairs.foldlM (init := Bindings.empty) fun env (dom, arg) =>
      match elabOneArg cfg env dom arg fuel with
      | .ok env' => some env'
      | .fail => none

/-- Infer the return type of a function application under HE′ telescope semantics. -/
def inferReturnType (cfg : ElabConfig) (funcType : Atom) (args : List Atom)
    (fuel : Nat) : Option Atom :=
  match arrowToTelescopeHEPrime funcType with
  | none => none
  | some tel =>
    match elabTelescope cfg tel args fuel with
    | none => none
    | some env => some (env.apply tel.codomain fuel)

/-! ## Extension Boundary -/

theorem extension_boundary (a : Atom) : splitDomainHE a = Domain.plain a := rfl

theorem splitDomain_dep_iff (x : String) (ty : Atom) :
    splitDomain (.expression [.symbol ":", .var x, ty]) = .dep x ty := rfl

theorem splitDomain_symbol_plain (s : String) :
    splitDomain (.symbol s) = .plain (.symbol s) := rfl

/-! ## Simple Matcher for Kernel-Decidable Proofs

A minimal bidirectional matcher that handles symbol equality, variable binding,
and structural expression matching — sufficient for example proofs and
small enough for the Lean kernel to evaluate via `decide`. -/

/-- Simple bidirectional atom matcher. Handles symbols, variables, and
    structural expression matching. No mutual recursion with merge. -/
def simpleMatch : Atom → Atom → Nat → Option Bindings
  | _, _, 0 => none
  | .symbol s1, .symbol s2, _ =>
    if s1 == s2 then some Bindings.empty else none
  | .var v, a, _ => some (Bindings.empty.assign v a)
  | a, .var v, _ => some (Bindings.empty.assign v a)
  | .expression es1, .expression es2, n + 1 =>
    if es1.length != es2.length then none
    else
      (es1.zip es2).foldlM (init := Bindings.empty) fun acc (a1, a2) =>
        -- Apply accumulated bindings before matching
        let a1' := acc.apply a1 n
        let a2' := acc.apply a2 n
        match simpleMatch a1' a2' n with
        | none => none
        | some b => some {
            assignments := acc.assignments ++ b.assignments
            equalities := acc.equalities ++ b.equalities }
  | _, _, _ => none

/-! ## Examples and Theorems -/

section Examples

/-- Example type oracle for genomic proof rules. -/
private def exGetTypes : Atom → List Atom
  | .symbol "eqtl_rs1_gene1" => [.expression [.symbol "eqtl", .symbol "rs1", .symbol "gene1"]]
  | .symbol "coreg_rs1_rs2" => [.expression [.symbol "coreg", .symbol "rs1", .symbol "rs2"]]
  | .symbol "target_rs2_gene1" => [.expression [.symbol "target", .symbol "rs2", .symbol "gene1"]]
  | .symbol "target_rs1_gene1" => [.expression [.symbol "target", .symbol "rs1", .symbol "gene1"]]
  | _ => []

/-- Example config using `simpleMatch`. -/
private def exCfg : ElabConfig where
  getTypes := exGetTypes
  matchFn := fun a b => simpleMatch a b 20

/-- The unary `dt` rule type: `(-> (: $e (eqtl $snp $gene)) (target $snp $gene))` -/
private def dtType : Atom :=
  .expression [.symbol "->",
    .expression [.symbol ":", .var "e",
      .expression [.symbol "eqtl", .var "snp", .var "gene"]],
    .expression [.symbol "target", .var "snp", .var "gene"]]

/-- The binary `ct` rule type. -/
private def ctType : Atom :=
  .expression [.symbol "->",
    .expression [.symbol ":", .var "e1",
      .expression [.symbol "coreg", .var "snp1", .var "snp2"]],
    .expression [.symbol ":", .var "e2",
      .expression [.symbol "target", .var "snp2", .var "gene"]],
    .expression [.symbol "target", .var "snp1", .var "gene"]]

/-! ### Positive: Unary Rule `dt` -/

theorem dt_telescope_has_one_dep_domain :
    ∃ tel, arrowToTelescopeHEPrime dtType = some tel ∧
    tel.domains.length = 1 ∧
    ∃ x ty, tel.domains.head? = some (.dep x ty) := by
  exact ⟨_, rfl, rfl, "e", _, rfl⟩

/-- Applying `dt` to `eqtl_rs1_gene1 : (eqtl rs1 gene1)` infers `(target rs1 gene1)`.
    Kernel-checked via `decide` with the simple matcher. -/
theorem dt_positive_example :
    inferReturnType exCfg dtType [.symbol "eqtl_rs1_gene1"] 20 =
    some (.expression [.symbol "target", .symbol "rs1", .symbol "gene1"]) := by
  decide

/-! ### Positive: Binary Rule `ct` with Dependency -/

theorem ct_telescope_has_two_dep_domains :
    ∃ tel, arrowToTelescopeHEPrime ctType = some tel ∧
    tel.domains.length = 2 := by
  exact ⟨_, rfl, rfl⟩

/-- Applying `ct` to `coreg_rs1_rs2` and `target_rs2_gene1` infers `(target rs1 gene1)`.
    The second domain depends on `$snp2 := rs2` bound by the first. Kernel-checked. -/
theorem ct_positive_example :
    inferReturnType exCfg ctType
      [.symbol "coreg_rs1_rs2", .symbol "target_rs2_gene1"] 20 =
    some (.expression [.symbol "target", .symbol "rs1", .symbol "gene1"]) := by
  decide

/-! ### Negative: Type Mismatch -/

/-- Elaboration fails when `$snp2 = rs2` but second arg has type `(target rs1 ...)`. -/
theorem ct_negative_mismatch :
    inferReturnType exCfg ctType
      [.symbol "coreg_rs1_rs2", .symbol "target_rs1_gene1"] 20 = none := by
  decide

/-! ### Negative: HE Legacy Behavior is Distinct -/

/-- Standard HE telescope parsing treats `(: $e T)` as a plain domain. -/
theorem he_legacy_no_dep_binder :
    ∀ tel, arrowToTelescopeHE dtType = some tel →
    tel.domains.head? = some (.plain
      (.expression [.symbol ":", .var "e",
        .expression [.symbol "eqtl", .var "snp", .var "gene"]])) := by
  intro tel h
  simp [arrowToTelescopeHE, arrowToTelescope] at h
  obtain ⟨_, rfl⟩ := h
  rfl

end Examples

/-! ## Future Layers (notes only)

- **Search-policy layer:** backward chaining, tabled resolution
- **ATP/solver integration:** external witness search
- **Bidirectional elaboration:** codomain-directed checking
- **Erasure/extraction:** proof-irrelevant binder positions

Deferred to separate modules. -/

end Mettapedia.Languages.MeTTa.HEPrime
