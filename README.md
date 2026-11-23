# MeTTapedia

Formal theory across proof systems — a working library of machine-checked
mathematics, logic, and AI theory, developed in the spirit of the QED
manifesto. One repository, several formal systems, each subtree independently
buildable.

## Layout

| Directory   | System            | Contents |
|-------------|-------------------|----------|
| `lean/`     | Lean 4            | Six Lake packages — see below |
| `cakeml/`   | HOL4 / CakeML     | `metta-ref`: verified MeTTa reference work (HOL4 specs, SML reference, curated tests) |
| `megalodon/`| Megalodon         | Set-theory developments: 4CT, Ramsey R(3,6), probability theory, PNP crux, hammer experiments |
| `mizar/`    | Mizar             | `4cp`: four-color theorem development (Kempe chains, face parity, indicator chains, lesson series) |
| `isabelle/` | Isabelle/HOL      | `4CP`: four-color port (graph primitives, disk lemmas, Tait equivalence) |

### Lean packages (`lean/`)

- **`mettapedia/`** — the flagship library: probability (Knuth–Skilling, Cox,
  de Finetti), information theory, PLN and evidence logics, HOL with Henkin
  semantics, universal AI (AIXI), MeTTa semantics, process calculi, GF
  linguistics, and more. See `lean/mettapedia/README.md`.
- **`algorithms/`** — pure algorithm checker kernels; MeTTa evaluation
  semantics and sessions.
- **`batteries/`** — `mettail-core` and `gf-core` support libraries
  (batteries-only).
- **`fourcolor/`** — the Four-Color Theorem in Lean.
- **`ramsey36/`** — Ramsey R(3,6) in Lean.
- **`foet/`** — formalized ethical theories (incl. a Gewirth/AFP-derived
  development).

A cross-system thread: the four-color theorem is attacked in Lean
(`lean/fourcolor`), Mizar (`mizar/4cp`), Isabelle (`isabelle/4CP`), and
Megalodon (`megalodon/4CT`); Ramsey R(3,6) likewise spans Lean and Megalodon.

### PLN / WM-PLN curriculum

The flagship Lean package has a focused PLN/WM-PLN curriculum and bridge map:

- `lean/mettapedia/Mettapedia/Examples/PLN/README.md` lists the worked
  curriculum order and entry modules.
- `lean/mettapedia/Mettapedia/PLN/Bridges/Logic/README.md` summarizes the
  BinaryEvidence and LC bridge status.
- `lean/mettapedia/Mettapedia/PLN/Bridges/HOL/README.md` summarizes the HOL
  derivation-tree readouts and ledger-to-multipath adapter.

## Building the flagship Lean library

```bash
./lean/bootstrap_local_repos.sh
cd lean/mettapedia
lake exe cache get   # mathlib oleans
scripts/check_library_sanity.sh
```

The flagship package uses Lean 4.33.1, with Mathlib pinned in
`lean/mettapedia/lakefile.lean` and `lake-manifest.json`. Its external Lean
dependencies use editable local checkouts prepared by the bootstrap script;
the migration bundle records their required source profiles. See
`lean/mettapedia/README.md` for qualification and source-coverage checks.
The other Lean packages declare their own toolchains and build from their
own directories.

Prover toolchains for the non-Lean subtrees (Megalodon, Mizar, Isabelle,
HOL4/CakeML) are not vendored here; install them separately:
[Megalodon](https://github.com/ai4reason/Megalodon),
[Mizar](http://mizar.org), [Isabelle](https://isabelle.in.tum.de),
[HOL4](https://hol-theorem-prover.org) / [CakeML](https://cakeml.org).

## Provenance, attribution, licensing

- MeTTapedia's original code, including its Lean formalizations, uses the repository's MIT license. Third-party material retains the licenses in its accompanying notices.
- `megalodon/theory/mizar/mml/` contains original Megalodon developments whose
  statements parallel MML articles — see the README there for MML attribution.
- `megalodon/theory/logic/GoedelGod.mg` is Chad E. Brown's Megalodon port of
  the Coq formalization by Benzmüller and Woltzenlogel Paleo (credited
  in-file).
- `lean/foet/Foet/AfpGewirth/` derives from the Fuenmayor–Benzmüller AFP
  entry.
- `cakeml/milawa-ref/`, if present locally, is a vendored reference copy of
  Magnus O. Myreen's Milawa theorem prover (from CakeML). It carries only a
  copyright notice and no bundled license, so it is **git-ignored and never
  committed here**; fetch it from upstream CakeML if needed.
- Proof-gap review: `rg -n "sorry"` in any subtree; completeness varies by
  subproject and is documented locally.
