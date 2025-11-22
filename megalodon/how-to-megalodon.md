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

## Tips

1. **Verify often** - Run megalodon after each theorem
2. **Start simple** - Get basic definitions working first
3. **Use prove** - Clarify goals for yourself
4. **Check preamble** - Many useful lemmas already exist
5. **Exit code 0 = success** - No output usually means it worked

## Resources

- Preamble: `/home/user/megalodon/examples/mizar/PfgMizarNov2020Preamble.mgs`
- Examples: `/home/user/megalodon/examples/`
- Ramsey proofs: `/home/user/ai-agents/megalodon/ramsey36/`
