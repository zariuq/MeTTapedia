# Mettapedia/CategoryTheory

Categorical foundations for OSLF, PLN, and the de Finetti theorem.

## Architecture

Three main strands:

### 1. Lambda Theory and Native Type Theory (7 files)

The OSLF type-synthesis pipeline: subobject fibrations over lambda theories yield
modal types via the Grothendieck construction.

| File | Description |
|------|-------------|
| `LambdaTheory.lean` | SubobjectFibration, LambdaTheory with finite limits and Heyting fibers |
| `NativeTypeTheory.lean` | NativeTypeBundle (NT) as Grothendieck construction of Sub |
| `PLNInstance.lean` | PLN as Frame-fiber instance; deduction as modal composition |
| `PLNTerms.lean` | PLN term syntax and reduction relation |
| `ModalTypes.lean` | Modal types via comprehension; rely-possibly semantics |
| `Hypercube.lean` | H_Sigma endofunctor (Stay & Wells); generates modal type systems |
| `PLNSemiringQuantale.lean` | Semiring quantale on Evidence: tensor and plus |

### 2. Categorical De Finetti (13 files)

Comprehensive categorical treatment of de Finetti's theorem through kernel-level
interfaces, permutation cones, Hausdorff moment uniqueness, and Kleisli(Giry)
diagrams.

| File | Description |
|------|-------------|
| `DeFinettiCategoricalInterface.lean` | Qualitative factorization interface |
| `DeFinettiPermutationCone.lean` | Finite-prefix laws commute with permutations |
| `DeFinettiKernelInterface.lean` | Kernel-level categorical de Finetti |
| `DeFinettiSequenceKernelCone.lean` | Sequence-kernel permutation cone on Bool^N |
| `DeFinettiHausdorffBridge.lean` | Hausdorff moment uniqueness |
| `DeFinettiPerNDiagram.lean` | Per-n permutation diagram surface |
| `DeFinettiGlobalFinitaryDiagram.lean` | Global finitary-permutation index |
| `DeFinettiLimitConePackage.lean` | Universal-property package |
| `DeFinettiKleisliGirySkeleton.lean` | Kleisli(Giry) global diagram and IID cone |
| `DeFinettiMarkovCategoryBridge.lean` | MarkovCategoryCore viewpoint |
| `DeFinettiExternalBridge.lean` | Bridge to vendored exchangeability package |
| `DeFinettiStableExports.lean` | Stable alias layer |
| `DeFinettiExports.lean` | Recommended import surface (18-theorem chain) |

### 3. Other

| File | Description |
|------|-------------|
| `FuzzyFrame.lean` | Unit interval [0,1] as Frame for PLN truth values |
| `TOGL.lean` | Greg Meredith's formal theory of graphs G[X,V] |
| `Topos/InternalLanguage.lean` | Kripke-Joyal semantics for OSLF |

## Proof Status

- 19 of 23 files fully proven (zero sorries)
- 4 files with sorries (6 total): TOGL (1), FuzzyFrame (2), ModalTypes (1), Hypercube (2)

## Dependency Flow

```
LambdaTheory -> PLNInstance -> NativeTypeTheory
                    |
              PLNTerms -> ModalTypes -> Hypercube

DeFinettiCategoricalInterface -> PermutationCone -> KernelInterface
  -> SequenceKernelCone -> HausdorffBridge -> PerNDiagram
  -> GlobalFinitaryDiagram -> KleisliGirySkeleton -> StableExports -> Exports
```
