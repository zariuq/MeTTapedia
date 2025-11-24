# How to Megalodon

A practical guide for writing kernel-verified proofs in Megalodon (for Proofgold).

## Quick Start

```bash
# Build Megalodon (requires OCaml)
cd /home/user/megalodon
./makeopt

# Verify a proof file
/home/user/megalodon/bin/megalodon -mizar \
  -I /home/user/megalodon/examples/mizar/PfgMizarNov2020Preamble.mgs \
  your_file.mg

# Exit code 0 = kernel verified!
```

## Basic Syntax

### Definitions

```
Definition name : type := body.
```

Examples:
```
Definition True : prop := forall p:prop, p -> p.
Definition False : prop := forall p:prop, p.
Definition not : prop -> prop := fun A:prop => A -> False.
Definition and : prop -> prop -> prop := fun A B:prop => forall p:prop, (A -> B -> p) -> p.
Definition or : prop -> prop -> prop := fun A B:prop => forall p:prop, (A -> p) -> (B -> p) -> p.
```

### Types

- `prop` - propositions
- `set` - ZF sets (ordinals like 0, 1, 2, ... are sets)
- `SType` - simple types (for polymorphism)
- `A -> B` - function type

### Parameters and Axioms

```
Parameter name : type.
Axiom name : proposition.
```

### Theorems

```
Theorem name : proposition.
proof_body.
Qed.
```

## Proof Tactics

### assume
Introduce a hypothesis:
```
assume H: A.
```

### prove
State what we're proving (helps clarify goal):
```
prove False.
```

### apply
Apply a lemma or hypothesis:
```
apply H.
apply orE A B C.
```

### exact
Provide exact proof term:
```
exact neq_0_1 Heq.
```

### Handling Disjunctions

For `A \/ B -> C`, use nested `apply` with bullet points:
```
apply H.
- assume HA: A.
  (* prove C from A *)
- assume HB: B.
  (* prove C from B *)
```

For deeper nesting, use `+` for sub-cases:
```
apply H.
- assume H1.
  apply H1.
  + assume HA: A.
    ...
  + assume HB: B.
    ...
- assume H2.
  ...
```

## Numbers as Ordinals

Numbers 0, 1, 2, ... are ordinal sets in the Mizar theory.

Key lemmas in the preamble:
- `neq_0_1`, `neq_0_2`, ..., `neq_n_m` for small n, m
- `neq_ordsucc_0` : `forall n, ordsucc n <> 0`
- `ordsucc_inj_contra` : for deriving inequalities

## Example: Simple Definition and Theorem

```
Definition MyPred : set -> set -> prop :=
  fun x y => x = 0 /\ y = 1.

Theorem MyPred_0_1 : MyPred 0 1.
prove 0 = 0 /\ 1 = 1.
apply andI.
- prove 0 = 0. exact eq_ref set 0.
- prove 1 = 1. exact eq_ref set 1.
Qed.
```

## Example: Proving Negation

```
Theorem not_MyPred_0_0 : ~MyPred 0 0.
assume H: MyPred 0 0.
prove False.
apply H.
assume Heq1: 0 = 0.
assume Heq2: 0 = 1.
exact neq_0_1 Heq2.
> LLM Context Refresher for Megalodon theorem proving

## Overview

**Megalodon** is an interactive theorem prover and proof checker developed by CIIRC/CTU. Its primary purpose is creating **Proofgold documents** - blockchain-verified mathematical proofs with cryptocurrency bounties.

**Location:** `/home/zar/claude/megalodon/`
**Executable:** `./bin/megalodon`
**Sources:** `./src`
**Examples:** `./examples`

## Building (if needed)

```bash
cd megalodon
./makeopt          # Optimized native build (preferred)
# fallback:
./makebytecode     # Bytecode build
```

Requires OCaml. No `make` needed.

## Quick Reference

```bash
# Check a file (silent = success)
./bin/megalodon file.mg

# With preamble (signature file)
./bin/megalodon -I preamble.mgs file.mg

# Different theories
./bin/megalodon -hf file.mg          # HF theory
./bin/megalodon -mizar file.mg       # Mizar theory
./bin/megalodon -hoas file.mg        # HOAS theory
# (default is Egal theory)

# Export to Proofgold format
./bin/megalodon -pfg file.mg > file.pfg

# Export ATP problems (for hammer)
./bin/megalodon -fof prefix file.mg   # First-order
./bin/megalodon -th0 prefix file.mg   # Higher-order

# Verbose output
./bin/megalodon -reporteachitem file.mg

# Check syntax errors
./bin/megalodon file.mg 2>&1 | head
```

## Supported Theories

| Theory | Flag | Description |
|--------|------|-------------|
| **Egal** | (default) | Higher-order Tarski-Grothendieck Set Theory (classical) |
| **Mizar** | `-mizar` | HOTG with Mizar's axioms |
| **HF** | `-hf` | Hereditarily finite sets |
| **HOAS** | `-hoas` | Higher-order abstract syntax (intuitionistic) |

Most set-theory and Ramsey examples use Egal.

## Type System

### Built-in Types
- `prop` - Propositions (type of logical formulas)
- `set` - Sets (the domain of set theory)
- `SType` - Meta-type for simple types (used in polymorphic definitions)

### Type Constructors
```
A -> B           Function type (A to B)
(set->prop)      Predicates on sets
(set->set)       Functions on sets
```

## Syntax Reference

### Declarations

```megalodon
(* Parameter - declared constant without definition *)
Parameter name : type.

(* Axiom - assumed proposition *)
Axiom name : prop.

(* Definition - constant with definition *)
Definition name : type := term.

(* Theorem/Lemma/Corollary - proves a proposition *)
Theorem name : prop.
<proof>
Qed.

Lemma name : prop.
<proof>
Qed.

(* Conjecture - unproven proposition (for bounties) *)
Conjecture name : prop.
Admitted.
```

### File Metadata (for Proofgold)

```megalodon
Title "My Document".
Author "Name".
Salt "random string".
Treasure <amount>.

(* Control definition visibility *)
Opaque name.      (* Don't unfold in proofs *)
Transparent name. (* Allow unfolding *)
```

### Sections (for polymorphism)

```megalodon
Section MySection.
Variable A : SType.           (* Type variable *)
Variable x : A.               (* Term variable *)
Hypothesis H : P x.           (* Local hypothesis *)

Definition foo : A -> A := fun y => y.
End MySection.
(* foo now has type: forall A:SType, A -> A *)
```

### Notation

```megalodon
(* Prefix operator *)
Prefix ~ 700 := not.                    (* ~P *)

(* Infix operator *)
Infix /\ 780 left := and.              (* P /\ Q *)
Infix \/ 785 left := or.               (* P \/ Q *)
Infix -> 790 right := imp.             (* P -> Q, built-in *)
Infix <-> 805 := iff.                  (* P <-> Q *)
Infix = 502 := eq.                     (* x = y *)

(* Binder notation *)
Binder+ exists , := ex.                (* exists x, P x *)
Binder+ exists , := ex; and.           (* exists x :e X, P x *)

(* Unicode aliases - special comment syntax *)
(* Unicode ~ "00ac" *)                 (* Allows using ¬ *)
(* Unicode /\ "2227" *)                (* Allows using ∧ *)
(* Unicode \/ "2228" *)                (* Allows using ∨ *)
(* Unicode <-> "2194" *)               (* Allows using ↔ *)
(* Unicode exists "2203" *)            (* Allows using ∃ *)
(* Unicode Union "22C3" *)             (* Allows using ⋃ *)
(* Unicode Power "1D4AB" *)            (* Allows using 𝒫 *)

(* Set membership shortcuts *)
x :e X                                 (* x ∈ X, In x X *)
X c= Y                                 (* X ⊆ Y, Subq X Y *)
{F x | x :e A}                         (* Replacement *)
```

### Terms

```megalodon
(* Lambda abstraction *)
fun x:A => body
fun x y:A => body                      (* Multiple args *)
fun (x:A) (y:B) => body

(* Application *)
f x
f x y                                  (* f applied to x, then to y *)

(* Quantifiers *)
forall x:A, P x
forall x y:A, P x y
forall x :e X, P x                     (* Bounded quantifier *)
exists x:A, P x
exists x :e X, P x                     (* Bounded existential *)

(* Local definitions in proofs *)
set name := term.
set name:type := term.                 (* With explicit type *)
```

## Proof Tactics

### Basic Tactics

| Tactic | Usage | Description |
|--------|-------|-------------|
| `exact` | `exact term.` | Provide exact proof term |
| `let` | `let x.` or `let x:A.` | Introduce universally quantified variable |
| `assume` | `assume H: P.` | Introduce hypothesis (for implication) |
| `apply` | `apply H.` | Apply theorem/hypothesis; generates subgoals |
| `prove` | `prove P.` | State current goal (documentation/debugging) |
| `witness` | `witness t.` | Provide existential witness |
| `claim` | `claim L: P. { proof }` | Prove local lemma |
| `reflexivity` | `reflexivity.` | Prove `x = x` |
| `symmetry` | `symmetry.` | Swap sides of equality goal |
| `set` | `set y := t.` | Local definition |

### Rewriting

```megalodon
rewrite H.                    (* Rewrite using H: a = b, left to right *)
rewrite <- H.                 (* Rewrite right to left *)
rewrite H at 2.               (* Rewrite only 2nd occurrence *)
```

### Case Analysis

```megalodon
(* Disjunction elimination - use bullets *)
apply H.                      (* H : A \/ B *)
- prove P.                    (* Case A *)
  <proof>
- prove P.                    (* Case B *)
  <proof>

(* Conjunction elimination *)
apply H.                      (* H : A /\ B *)
assume HA: A.
assume HB: B.
<proof>

(* Classical case split using excluded middle *)
apply xm P.                   (* xm : forall P, P \/ ~P *)
- assume HP: P.
  <proof when P holds>
- assume HnP: ~P.
  <proof when ~P holds>
```

### Structured Proofs

```megalodon
Theorem example : forall A B:prop, A -> B -> A /\ B.
let A B.                      (* Introduce A, B *)
assume HA: A.                 (* Introduce hypothesis *)
assume HB: B.
claim L: A.                   (* Local lemma *)
{ exact HA. }
apply andI.                   (* Apply conjunction intro *)
- exact L.                    (* First subgoal *)
- exact HB.                   (* Second subgoal *)
Qed.
```

## Common Patterns

### Case Analysis on Disjunction

```
Theorem example : A \/ B -> C.
assume H: A \/ B.
prove C.
apply orE A B C _ _ H.
- assume HA: A.
  (* prove C *)
- assume HB: B.
  (* prove C *)
Qed.
```

### Using andI/andEL/andER

```
(* Conjunction introduction *)
apply andI.
- prove A. ...
- prove B. ...

(* Conjunction elimination *)
apply andEL A B H.  (* gets A from A /\ B *)
apply andER A B H.  (* gets B from A /\ B *)
```

## File Structure

1. No `Module` declarations (unlike Coq)
2. Definitions and Theorems at top level
3. Include preamble with `-I` flag
4. Use `(* comments *)` for documentation

## Important Gotchas

1. **NO COMMENT-ONLY LINES IN MIZAR MODE** - In `-mizar` mode, files MUST NOT start with comment-only lines (lines starting with `%`). This causes "lexing: empty token" errors. Start directly with `Definition` or `Theorem`. Inline comments (e.g., `assume H. % this is ok`) are fine, but standalone comment lines at the file start or between top-level declarations will break the lexer.

2. **Argument order for `forall x :e V` telescopes** - When applying a function with type `forall a b c :e V, ...`, arguments must be interleaved with membership proofs: `f a Ha b Hb c Hc ...` NOT `f a b c Ha Hb Hc ...`. The telescope `forall x :e V` desugars to `forall x, x :e V -> ...`.

3. **No `_` placeholders in `-mizar` mode** - Unlike standard mode, Mizar mode does not accept `_` for implicit arguments in function applications. You must provide all arguments explicitly or use the proof branching syntax (`-`, `+`, `*`, etc.).

4. **Use `reflexivity`** for equality proofs like `0 = 0`

5. **Use `claim`** for local lemmas within a proof

## If-Then-Else Proofs

Key axioms for conditional reasoning:
- `If_i_1 : forall p:prop, forall x y:set, p -> (if p then x else y) = x`
- `If_i_0 : forall p:prop, forall x y:set, ~p -> (if p then x else y) = y`

Pattern for nested if-then-else:
```
claim L1: ~(1 = 0). exact neq_1_0.
claim L2: 1 = 1. reflexivity.
apply eq_i_tra (if 1 = 0 then x else y) (y) result.
- exact If_i_0 (1 = 0) x y L1.
- (* continue with inner if *)
```

## Transitivity Chains

Use `eq_i_tra` to chain equalities:
```
apply eq_i_tra A B C.
- (* prove A = B *)
- (* prove B = C *)
(* concludes A = C *)
```

## Sub-proofs with Braces

For parallel sub-goals, use `{ }`:
```
apply eq_i_tra A B C.
{ (* prove A = B *) }
{ (* prove B = C *) }
```

## Tips

1. **Verify often** - Run megalodon after each theorem
2. **Start simple** - Get basic definitions working first
3. **Use prove** - Clarify goals for yourself
4. **Check preamble** - Many useful lemmas already exist
5. **Exit code 0 = success** - No output usually means it worked
6. **Read error messages carefully** - They tell you expected vs actual types

## Resources

- Preamble: `/home/user/megalodon/examples/mizar/PfgMizarNov2020Preamble.mgs`
- Examples: `/home/user/megalodon/examples/`
- Ramsey proofs: `/home/user/ai-agents/megalodon/ramsey36/`
### Church Encodings (Egal Theory)

```megalodon
(* Propositions are encoded via their elimination principles *)
Definition True : prop := forall p:prop, p -> p.
Definition False : prop := forall p:prop, p.
Definition not : prop -> prop := fun A => A -> False.
Definition and : prop -> prop -> prop :=
  fun A B => forall p:prop, (A -> B -> p) -> p.
Definition or : prop -> prop -> prop :=
  fun A B => forall p:prop, (A -> p) -> (B -> p) -> p.
Definition ex : (A->prop)->prop :=
  fun Q => forall P:prop, (forall x:A, Q x -> P) -> P.
```

### Standard Theorems

```megalodon
(* Introduction rules *)
Theorem andI : forall A B:prop, A -> B -> A /\ B.
exact (fun A B a b p H => H a b).
Qed.

Theorem orIL : forall A B:prop, A -> A \/ B.
exact (fun A B a p H1 H2 => H1 a).
Qed.

Theorem orIR : forall A B:prop, B -> A \/ B.
exact (fun A B b p H1 H2 => H2 b).
Qed.

(* Elimination rules *)
Theorem andEL : forall A B:prop, A /\ B -> A.
exact (fun A B H => H A (fun a b => a)).
Qed.

Theorem FalseE : False -> forall p:prop, p.
exact (fun H => H).
Qed.

(* Excluded middle (classical, in Egal preambles) *)
Axiom xm : forall P:prop, P \/ ~P.
```

### Set Theory Basics

```megalodon
Parameter In : set -> set -> prop.        (* Membership *)
Parameter Empty : set.                     (* Empty set *)
Parameter Union : set -> set.              (* Union *)
Parameter Power : set -> set.              (* Power set *)

Axiom EmptyAx : ~exists x:set, x :e Empty.
Axiom UnionEq : forall X x, x :e Union X <-> exists Y, x :e Y /\ Y :e X.
Axiom PowerEq : forall X Y:set, Y :e Power X <-> Y c= X.

Definition Subq : set -> set -> prop := fun A B => forall x :e A, x :e B.
Infix c= 502 := Subq.

(* Typical proof pattern: subset transitivity *)
Theorem Subq_tra : forall X Y Z:set, X c= Y -> Y c= Z -> X c= Z.
let X Y Z.
assume H1: X c= Y.
assume H2: Y c= Z.
let x.
assume Hx: x :e X.
prove x :e Z.
apply H2.
prove x :e Y.
apply H1.
exact Hx.
Qed.
```

## File Organization

### Main File (.mg)
Contains definitions, theorems with proofs, and conjectures.

### Signature File (.mgs)
Contains definitions, parameters, and axioms **WITHOUT proofs**. Used as preamble with `-I` flag.

**Important:** `.mgs` files cannot contain `Theorem` proofs. Only declarations.

```bash
./bin/megalodon -I preamble.mgs main.mg
```

### Proofgold References

```megalodon
(* Reference to previously defined object by Merkle root *)
(* Parameter ordsucc "9db634da..." "65d8837d..." *)
Parameter ordsucc : set->set.
```

## ATP Integration (Hammer)

### Generating ATP Problems

```bash
# Generate first-order (FOF) problems
./bin/megalodon -fof output_prefix -I preamble.mgs file.mg

# Generate higher-order (TH0) problems
./bin/megalodon -th0 output_prefix -I preamble.mgs file.mg
```

### Using with Vampire/E Prover

```bash
# Test with E prover
eprover --cpu-limit=60 --auto --tstp-format -s problem.fof.p

# Test with Vampire
vampire -t 60 problem.fof.p
```

### Getting Dedukti Proofs from Vampire

**Workflow:** Megalodon hammer → TPTP → Vampire Dedukti output → analyze → translate to Megalodon

When ATP provers succeed, you can extract the full proof in Dedukti format to guide your Megalodon formalization:

```bash
# Generate Dedukti proof (both flags required!)
vampire -t 60 --proof dedukti --proof_extra full problem.fof.p > problem.dk

# Constraint: --proof dedukti REQUIRES --proof_extra full
# Without --proof_extra full, Vampire errors:
#   "User error: Broken Constraint: if proof(dedukti) is equal to dedukti
#    then proof_extra(off) is equal to full"
```

**Dedukti Output Structure:**

The `.dk` file contains a resolution-based proof with:
- **Clausification steps**: CNF transformation of the original problem
- **Resolution inferences**: Systematic literal elimination via resolution
- **Final empty clause**: The contradiction proving the conjecture

Example structure:
```dedukti
def cnf123: Prf_clause (bind iota (x : El iota => ...)) := ...
def deduction456: Prf_clause ... := resolution cnf123 cnf789 ...
def bot: Prf_clause (EpsC) := resolution ... (final empty clause)
```

**Using Dedukti as Translation Guide:**

The Dedukti proof shows the **proof strategy** used by the ATP prover:
1. Which hypotheses were actually used (premise selection)
2. Which instantiations were critical (from resolution steps)
3. What intermediate lemmas emerged (from deduction steps)
4. The logical flow to contradiction

**Translation workflow:**
1. Identify the key resolution steps in the Dedukti proof
2. Understand which original hypotheses were combined
3. Translate the ATP's clausification back to natural Megalodon proof structure
4. Use the resolution tree as a roadmap for `apply`, `claim`, and case analysis

**Example: vertex_degree_bound.mg**

The successful pattern for translating ATP proofs to Megalodon:
- ATP proof showed which graph axioms were needed
- Resolution steps revealed the critical case splits
- Dedukti instantiations guided the `let` and `assume` structure
- Final proof was 141 lines, kernel-verified

**Practical Notes:**
- Dedukti proofs can be hundreds of lines (vertex_12_nonneighbors_v2.dk: 265 lines)
- Don't translate literally - extract the **proof insight**
- Resolution-based proofs often reveal simpler natural deduction structure
- If Dedukti shows pure graph reasoning (no cardinality arithmetic), the Megalodon proof should too

**Critical Notes:**
- Use simple output prefixes (no `/` in path) to avoid TPTP naming issues
  - Bad: `./bin/megalodon -fof /tmp/output ...` → creates `conj_/tmp/output_50` (invalid!)
  - Good: `./bin/megalodon -fof output ...` → creates `conj_output_50` (valid)
- The full preamble exports 5000+ axioms (surreals, complex numbers, etc.)
  - This makes ATP problems very hard to solve
  - For targeted problems, consider a minimal custom preamble
- Each `Admitted.` theorem generates a separate `.fof.p` file
- Problem numbers correspond to theorem order in the file

### ATP Practical Experience (Nov 2025)

**Premise Selection with E's SInE:**
```bash
# Use E as premise selector, then run other provers
eprover --tstp-in --tstp-out --sine=Auto --prune --auto --cpu-limit=10 big_problem.p > pruned.p
vampire --mode casc --time_limit 60 pruned.p
zipperposition -i tptp -o tptp --timeout 60 pruned.p
```

**What Works:**
- Simple lemmas in smaller preambles (< 1000 axioms)
- Theorems with clear instantiation patterns
- Files using `examples/hammer/100thms_12_h.mg` style inline axioms

**What Struggles:**
- Full Egal preamble (5000+ axioms): too much irrelevant set theory
- Large definitional case analysis (e.g., 17-way disjunctions with symmetry)
- Problems requiring ground enumeration (E/Vampire/Zipperposition all timed out on `Adj17_sym`)

**Prover Comparison (Adj17_sym, 60s each):**
| Prover | Result | Notes |
|--------|--------|-------|
| E | ResourceOut | Generates millions of clauses |
| Vampire (CASC) | Timeout | Portfolio strategies all fail |
| Zipperposition | ResourceOut | Similar to E |
| cvc5 | N/A | Only reads SMT-LIB2, not TPTP |

**Recommendation:** For combinatorial graph properties like `Adj17_sym`, manual case-by-case proofs are more practical than ATP. Consider generating proof scripts programmatically.

## Workflow Tips

### 1. Start with Structure, Not Detail
- Declare `Theorem ...` then use `Admitted.` first to check syntax, imports, and notation
- Only then refine into a full proof

### 2. Use Preambles
- Include existing `.mgs` files with `-I` instead of re-declaring basics
- Standard preambles provide `xm`, `setext`, logical connectives, etc.

### 3. Prefer `Definition` over `Axiom`
- Only use `Axiom` when mirroring an external fact not being proven here
- Definitions are transparent and can be unfolded

### 4. Keep Proofs Linear and Modular
- Megalodon has simple `apply`/`rewrite` - no heavy automation
- Use `claim L: P. { ... }` and `prove P.` to decompose complex arguments

### 5. Make Classical Reasoning Explicit
- Use excluded middle `xm : forall P, P \/ ~P` when you need case splits
- Pattern: `apply xm P. - assume HP. ... - assume HnP. ...`

### 6. Be Explicit with Types
- When type inference fails:
  ```megalodon
  let x:set.
  assume H: x :e X.
  set y:T := t.
  ```

### 7. Debug with `prove` and Small Steps
- Interleave `prove <expected_goal>.` to ensure agreement on current target
- When `apply` fails, check that goal matches the conclusion of your lemma

### 8. Large Disjunctions and Definition Unfolding
- `\/` is left-associative: `P1 \/ P2 \/ P3` means `((P1 \/ P2) \/ P3)`
- For n-way disjunction, to prove the k-th disjunct:
  - Apply `orIL` (n-k) times, then prove your disjunct
  - Example: For 17-way disjunction, prove P1 with 16 `orIL` applications
- Definitions may not unfold automatically. Use `prove <expanded form>.` to force:
  ```megalodon
  Definition Adj : set -> set -> prop := fun i j => ...

  Theorem test : Adj 0 9.
  prove (0 = 0 /\ ...) \/ ...   (* Expand definition manually *)
  apply orIL. apply orIL. ...   (* Navigate to correct disjunct *)
  ```
- The preamble has `or3I1..or3I3`, `or4I1..or4I4`, `or5I1..or5I5` for small disjunctions

### 8a. Church-Encoded Disjunction Elimination (CRITICAL)

**Problem:** Given `H : P1 \/ P2 \/ ... \/ Pn` and case handlers `C1 : P1 -> False`, ..., `Cn : Pn -> False`, prove `False`.

**Key Insight:** The `\/` operator is **LEFT-ASSOCIATIVE**:
```megalodon
Infix \/ 785 left := or.
```

This means `P1 \/ P2 \/ P3` parses as `((P1 \/ P2) \/ P3)`, NOT `P1 \/ (P2 \/ P3)`.

**Church Encoding:**
```megalodon
Definition or : prop -> prop -> prop :=
  fun A B => forall p:prop, (A -> p) -> (B -> p) -> p.
```

So a proof `H : A \/ B` has type:
```megalodon
forall p:prop, (A -> p) -> (B -> p) -> p
```

**Elimination Pattern:** To eliminate left-associative n-way disjunction, peel from OUTSIDE-IN:

```megalodon
(* For P1 \/ P2 \/ P3 = ((P1 \/ P2) \/ P3) *)
exact (
  H False
    (fun H2 =>              (* H2 : P1 \/ P2 *)
      H2 False C1 C2)       (* Eliminate inner disjunction *)
    C3).                    (* Handle outermost case P3 *)
```

**General n-way pattern (15-way example):**
```megalodon
(* Given: Ledge : P1 \/ P2 \/ ... \/ P15  (left-associative)
   Goal: False
   Have: C1 : P1 -> False, ..., C15 : P15 -> False *)

exact (
  Ledge False
    (fun H14 =>             (* H14 : prefix14 = P1 \/ ... \/ P14 *)
      H14 False
        (fun H13 =>         (* H13 : prefix13 *)
          H13 False
            (fun H12 =>     (* Keep nesting... *)
              ...
                (fun H2 =>  (* H2 : P1 \/ P2 *)
                  H2 False C1 C2)
                C3)         (* Handle P3 *)
            C4)             (* Handle P4 *)
        C14)                (* Handle P14 *)
    C15).                   (* Handle P15 (outermost) *)
```

**Why This Works:**
1. `Ledge` has type `(prefix14 \/ P15)` where `prefix14 = P1 \/ ... \/ P14` (left-nested)
2. Applying `Ledge False` gives: `(prefix14 -> False) -> (P15 -> False) -> False`
3. First argument needs type `prefix14 -> False`, constructed recursively
4. Second argument is `C15 : P15 -> False`
5. Recursively build `kill_k : prefix_k -> False` from `kill_(k-1)` and `Ck`
6. Base case: `kill_2 = fun H2 => H2 False C1 C2`

**Common Mistake:** Trying to eliminate left-to-right (handling P1 first):
```megalodon
(* WRONG - treats as right-associative *)
exact (Ledge False C1 (fun rest => ...)).  (* Type error! *)
```
The error occurs because `C1 : P1 -> False` but the first argument expects `prefix14 -> False`.

### 9. Use Bullets and Braces Consistently
- Each branch from `apply` starts with `-` / `+` / `*`
- `claim` proofs go in `{ ... }` braces

## Common Pitfalls

### 1. File Start (CRITICAL FOR MIZAR MODE)
**DO NOT** start `.mg` files with comment-only lines (`%` at start of line) when using `-mizar` mode. This causes "lexing: empty token" errors that are hard to debug.

**WRONG:**
```megalodon
% This is a proof of...
% Author: ...

Definition foo := ...
```

**CORRECT:**
```megalodon
Definition foo := ...  % This comment is OK

% Later comments between definitions are also fine in some contexts
Definition bar := ...
```

**SAFEST:** Just don't use standalone comment lines at all in Mizar mode. Use inline comments instead.

### 2. Preamble Restrictions
`.mgs` files cannot contain proofs. If you add a proof there, compilation fails.

### 3. Proof Structure
- Use `-` bullets for subgoals from `apply`
- Use `{ }` braces for `claim` proofs
- End proofs with `Qed.`
- Use `Admitted.` for incomplete proofs

### 4. Type Inference
Megalodon has limited type inference. When in doubt, provide explicit types:
```megalodon
let x:set.                    (* Explicit type *)
assume H: x :e X.             (* Named hypothesis *)
```

### 5. Binder Precedence
Quantifiers bind tightly. Use parentheses for clarity:
```megalodon
forall x, P x -> Q x          (* Means: forall x, (P x -> Q x) *)
(forall x, P x) -> Q          (* Different meaning *)
```

### 6. Opaque vs Transparent
- `Opaque`/`Transparent` metadata affects delta-reduction
- Make sure intended constants are unfoldable (or not) for Proofgold submissions

### 7. ATP Naming
Keep the prefix simple (no slashes) when generating ATP problems.

## Where to Look for Patterns

Concrete templates and larger examples:

| File | What it demonstrates |
|------|---------------------|
| `examples/mizar/MizExample1.mg` | Minimal complete set-theoretic proof |
| `examples/egal/Ramsey_3_3_5.mg` | Classical Ramsey configuration |
| `examples/egal/Ramsey_3_3_6.mg` | Ramsey with preamble |
| `examples/UpToOctonions/*` | Large structured proofs (claims, rewrites, sections) |
| `examples/hoas/CoreSimplicity*` | Working with binders/signatures in HOAS |
| `examples/hammer/` | ATP export and integration workflows |
| `examples/form100/` | Freek's "100 theorems" |
| `experiments/` | Test files for learning |

## Example: Complete Proof

```megalodon
Definition True : prop := forall p:prop, p -> p.
Definition and : prop -> prop -> prop :=
  fun A B:prop => forall p:prop, (A -> B -> p) -> p.
Infix /\ 780 left := and.

Section Eq.
Variable A:SType.
Definition eq : A->A->prop := fun x y:A => forall Q:A->A->prop, Q x y -> Q y x.
End Eq.
Infix = 502 := eq.

Theorem andI : forall A B:prop, A -> B -> A /\ B.
let A B.
assume HA: A.
assume HB: B.
prove A /\ B.
exact (fun p H => H HA HB).
Qed.

Theorem and_comm : forall A B:prop, A /\ B -> B /\ A.
let A B.
assume H: A /\ B.
apply H.
assume HA: A.
assume HB: B.
apply andI.
- exact HB.
- exact HA.
Qed.
```

## Documentation

- `docs/HOTG_Mizar_Theory.pdf` - Mizar theory
- `docs/HF_Theory_Hereditarily_Finite_Sets.pdf` - HF theory
- `docs/HOAS_Theory_Higher_Order_Abstract_Syntax.pdf` - HOAS theory
- `docs/Megalodon_Ramsey_Theory_Examples.pdf` - Ramsey examples
- `docs/Hammering_Higher_Order_Set_Theory.pdf` - ATP integration

## See Also

- Proofgold: https://proofgold.org
- Freek's 100 Theorems: http://www.cs.ru.nl/~freek/100/
- Brown & Pak "A Tale of Two Set Theories" (CICM 2019)
