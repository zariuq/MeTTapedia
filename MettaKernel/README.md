# MeTTaKernel

A small, generic proof kernel written **in MeTTa**, together with a curriculum that samples what
an ITP-class system must be able to check.

MeTTaKernel targets one deterministic generic checker of finite proof terms over
validated language and inference-calculus presentations.  Current prototypes do
not yet establish this full claim: generic one-step semantics and several
calibrations exist, while the proof-relevant `Deriv`/checker layer and named
source-adequacy theorems remain open.  The design rule is **derive, don't
impose**: source systems supply calculus data and untrusted source adapters;
meaning is established by explicit adequacy theorems, never by bespoke product
checkers or by relabeling an encoding as native.

The metatheory, with the status of each part, is in
[the metatheory paper](../papers/metatheory.tex).

## Runtime: this is prototyped in `.metta` and runs on CeTTa

Every kernel file here is a `.metta` prototype whose **runtime is CeTTa** (a C runtime for several
MeTTa dialects, HE and PeTTa among them). Set `CETTA` to your CeTTa binary and the gate scripts run the kernel through
it; a companion PeTTa build (SWI-Prolog) is used as a second engine for parity, and LeaTTa (the
Lean-verified minimal MeTTa) is used as a light correctness oracle on the rows it runs.

```sh
CETTA=/path/to/CeTTa/cetta   PETTA=/path/to/PeTTa/run.sh   bash kernel/run_kernel_parity.sh
```

The development method is deliberate: **prototype in `.metta`, internalize proved
components into CeTTa's C, and keep the `.metta` as a differential oracle.** The
parser implementation explored this route first: a probe grew into generic
`lib_parse.metta`, followed by CeTTa's native `lib_parse_native_grammar.c`.
Their correspondence remains an obligation; implementation succession is not a
proof of equivalence. MeTTaKernel is CeTTa-resident by runtime and destination,
while its current prototypes are housed here during development.

## Trust: prove source reading or its correspondence

The proof verdict's trust account includes the generic checker implementation,
the admitted validated presentation, checker/source-adequacy theorems in their
foundation, running-artifact correspondence, and the physical execution
boundary. Every residual item remains explicit.

For source syntax, use a proved generic reader where its input class supports
one, or prove a reader correspondence for the named format. `mkGram` is a
candidate generic parser for grammar-backed inputs, not a universal reader
topology. A producer-emits-certificate / trusted-recheck split is an explicitly
ledgered interim. The fast native parser is a performance sibling outside the
trusted path until equivalence is proved; differential comparison is regression
evidence, not proof of conformance. Verified extraction/compilation and
reflective predecessor checking remain alternative staged routes, each with its
own artifact-correspondence and assumption obligations.

## Layout

- `kernel/` — the kernel proper. LCF core (`lcf_core.metta`); admitted-signature kernels
  (`kernel_signature_v0`, `kernel_signature_lf_v0`, `kernel_signature_lf_natrec_v0`); the binding
  substrate (`kernel_binding_waist_v1`, `kernel_binding_abt_engine_v1`, `kernel_binding_decl_v1`);
  and the generic indexed-inductive engine (`kernel_signature_lf_indexed_v0`) into which earlier
  eq/inductive primitives have been retired. Each `<name>.metta` has a `<name>_petta.metta` parity
  twin. Gates: `run_kernel_parity.sh`, `run_conv_soundness_gate.sh`, `run_sr_admission_gate.sh`,
  `run_binding_mutation_gate.sh`, and `run_ocoherence_gate.sh`.
- `Curriculum/` — the completeness scaffold: small positive/negative examples across `HOL/`,
  `Megalodon/`, `Coq/`, `Lean/`, `DeduktiLambdapi/`, `VibeITP/`, `DTTBench/`, `VerifiedMeTTa/`,
  `PrimeMotivation/`, `ProgramVerification/`, plus `Notation/` (concrete-syntax specs the parser
  corpus aligns to). `run_all.sh` checks positives and
  requires negatives to be rejected; it prints per-file theorem counts and an assumption ledger.
  Curriculum coverage is regression and breadth evidence.  It is not a
  substitute for generic checker correctness or source-adequacy theorems.
- `Examples/` — MeTTa example families, some with expected outputs.
- `discriminators/` — programs that each separate one semantic question.
- `tcalc-tier0/` — a C reference implementation of the transform calculus, with proof-format
  verifiers hosted on it (MM0, MMB, HOL Light, Megalodon, Dedukti) and their controls.
- `tcalc-compiled/` — Micromath's theory compiled to Cesta, its lockstep checks against tier 0, and
  machine-code proofs in `proofs/`.
- `tools/` — generators and converters for controls and certificates.

## Status

Several kernel and `_petta` parity slices and curriculum gates have passed at
their recorded scopes.  The core open frontier is larger: presentation
admission, a generated proof-relevant checker, source adequacy for Metamath and
real HOL systems, parser correctness, conversion metatheory, and staged runtime
correspondence.  Read each gate's stated scope and the assumption ledger printed
by `Curriculum/run_all.sh` rather than inferring program status from a green
fixture count.
