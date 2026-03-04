# CategoryTheory foundation

Mettapedia/CategoryTheory provides categorical foundations for OSLF, PLN, and de Finetti formalization.

## Architecture

- The architecture is three main strands.
- Strand one is lambda theory and native type theory across seven files.
- Strand two is categorical de Finetti across thirteen files.
- Strand three is supporting files for fuzzy frames, graph theory, and internal language.

### Lambda theory and native type theory strand

- `LambdaTheory.lean`
  - LambdaTheory.lean defines SubobjectFibration and LambdaTheory with finite limits and Heyting fibers

- `NativeTypeTheory.lean`
  - NativeTypeTheory.lean defines NativeTypeBundle as a Grothendieck construction

- `PLNInstance.lean`
  - PLNInstance.lean defines PLN as a frame-fiber instance with modal composition

- `PLNTerms.lean`
  - PLNTerms.lean defines PLN term syntax and reduction relation

- `ModalTypes.lean`
  - ModalTypes.lean defines modal types via comprehension and rely-possibly semantics

- `Hypercube.lean`
  - Hypercube.lean defines the H_Sigma endofunctor for modal type generation

- `PLNSemiringQuantale.lean`
  - PLNSemiringQuantale.lean defines a semiring quantale on Evidence with tensor and plus

### Categorical de Finetti strand

- `DeFinettiCategoricalInterface.lean`
  - DeFinettiCategoricalInterface.lean defines a qualitative factorization interface

- `DeFinettiPermutationCone.lean`
  - DeFinettiPermutationCone.lean proves permutation commutation of finite-prefix laws

- `DeFinettiKernelInterface.lean`
  - DeFinettiKernelInterface.lean defines kernel-level categorical de Finetti interfaces

- `DeFinettiSequenceKernelCone.lean`
  - DeFinettiSequenceKernelCone.lean defines sequence-kernel permutation cones on Bool power N

- `DeFinettiHausdorffBridge.lean`
  - DeFinettiHausdorffBridge.lean proves Hausdorff moment uniqueness links

- `DeFinettiPerNDiagram.lean`
  - DeFinettiPerNDiagram.lean defines per-n permutation diagram surfaces

- `DeFinettiGlobalFinitaryDiagram.lean`
  - DeFinettiGlobalFinitaryDiagram.lean defines global finitary-permutation indexing

- `DeFinettiLimitConePackage.lean`
  - DeFinettiLimitConePackage.lean packages the universal-property layer

- `DeFinettiKleisliGirySkeleton.lean`
  - DeFinettiKleisliGirySkeleton.lean defines Kleisli Giry global diagrams and IID cones

- `DeFinettiMarkovCategoryBridge.lean`
  - DeFinettiMarkovCategoryBridge.lean provides a MarkovCategoryCore viewpoint

- `DeFinettiExternalBridge.lean`
  - DeFinettiExternalBridge.lean provides bridges to vendored exchangeability formalization

- `DeFinettiStableExports.lean`
  - DeFinettiStableExports.lean provides stable alias exports

- `DeFinettiExports.lean`
  - DeFinettiExports.lean provides the recommended import surface

### Other

- `FuzzyFrame.lean`
  - FuzzyFrame.lean formalizes the unit interval frame for PLN truth values

- `GeneralizedOpenMaps.lean`
  - GeneralizedOpenMaps.lean defines the minimal generalized-open-map core:
    `BisimulationKit`, `GOpen`, `PathBisim`, `StrongPathBisim`, and `(E,S)`-style
    span witness equivalence (`pathBisim_iff_esBisimilar`)

- `TOGL.lean`
  - TOGL.lean formalizes Greg Meredith's theory of graphs

- `Topos/InternalLanguage.lean`
  - Topos/InternalLanguage.lean formalizes Kripke-Joyal semantics for OSLF

## Open-map bridge map

- `GeneralizedOpenMaps.lean`
  - Core theorem: `pathBisim_iff_esBisimilar`
- `../Languages/ProcessCalculi/PiCalculus/WeakBisimOpenMapBridge.lean`
  - Core theorem: `weakRestrictedBisim_iff_pathBisim`
- `../Languages/ProcessCalculi/PiCalculus/BranchingBisim.lean`
  - Core theorem: `branching_implies_weak`
- `../Logic/WeightedOpenMaps.lean`
  - Core theorem: `weightedBisim_iff_gopen_span`
- `../Logic/OSLFOpenMapBridge.lean`
  - Core theorem: `fullOpenWitness_implies_obsEq`

## Proof status

- Nineteen of twenty-three files are fully proven with zero sorries.
- The remaining four files are TOGL one sorry, FuzzyFrame two sorries, ModalTypes one sorry, and Hypercube two sorries.

## Dependency flow

The dependency flow is the following architecture diagram.

```
LambdaTheory -> PLNInstance -> NativeTypeTheory
                    |
              PLNTerms -> ModalTypes -> Hypercube

DeFinettiCategoricalInterface -> PermutationCone -> KernelInterface
  -> SequenceKernelCone -> HausdorffBridge -> PerNDiagram
  -> GlobalFinitaryDiagram -> KleisliGirySkeleton -> StableExports -> Exports
```
