import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TowerInterpretation.SetModel
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TowerInterpretation.Soundness
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TowerInterpretation.ChurchSoundness
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Annotated.ConstantInstantiation
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Annotated.PurePackages
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TowerInterpretation.TypedInstances
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TowerInterpretation.MappedSchemas
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TowerInterpretation.SetInductive
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TowerInterpretation.SetDeclarationLists
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TowerInterpretation.SetDefinitions
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TowerInterpretation.SetRecursion
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TowerInterpretation.SetLaterArguments
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Annotated.TelescopeAbstractions
import Mettapedia.Logic.HOL.Embedding.ZFSetInductive
import Mettapedia.Logic.HOL.Embedding.ZFSetInductiveRecursion
import Mettapedia.Logic.HOL.Embedding.ZFSetInductiveFunctions
import Mettapedia.Logic.HOL.Embedding.ZFSetIndexedTrees
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TowerInterpretation.SetEliminators
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TowerInterpretation.DomainVisibility

/-!
# The candidate calculus interpreted in the set tower

The parameterized dependent calculus writes λ-abstractions without their
domains, so a set value cannot be read off a term. The interpretation goes
through the annotated calculus of `TypedEquality.Annotated`, whose terms
(`CTm`) record the domain of every abstraction and whose judgment
(`CDerivable`) is the candidate's declarative judgment over them. The
*annotated fragment* consists of the candidate statements that are erasures of
annotated derivations. For a package with the lifting facts every candidate
derivation over a formed context elaborates to an annotated derivation, so the
fragment contains every such derivation, and the set interpretation validates
it.

* `SetModel`: the total interpretation of annotated terms into `ZFSet` —
  trace functions for Π, Kuratowski pairs for Σ, identity as a truth value —
  with its renaming and substitution lemmas.
* `Soundness`: every annotated derivation holds in every set model of its
  package (`CDerivable.sound`), the one soundness induction; the annotated
  fragment `InAnnotatedImage` of the candidate judgment.
* `ChurchSoundness`: every candidate derivation over a formed context of a
  package with the lifting facts is sound through its elaboration
  (`Derivable.sound_elaborated`) and lies in the annotated fragment
  (`Derivable.inAnnotatedImage`); a closed type without abstractions whose
  annotation is empty in a set model has no closed candidate inhabitant
  (`Derivable.no_closed_inhabitant`); rigid packages
  (`Derivable.sound_rigid`).
* `TypedEquality.Annotated.ConstantInstantiation`: instantiating declared constants by closed
  terms, of terms and of derivations; constant-free statements.
* `TypedEquality.Annotated.PurePackages`: for a package without root computation,
  injectivity and no-confusion of the annotated type formers, whatever constants it declares
  (`CFormerFacts.ofNoSteps`), from the logical relation and a conservative rigid extension
  into which its constants are renamed; and, for a rigid package, whose declared types have no
  abstraction, the lifting of every derivation (`LiftingFacts.ofRigid`), with pure packages as
  an instance (`LiftingFacts.ofPure`).
* `TypedInstances`: root steps at their typed instances. A rewrite schema is valid at its
  typed instances (`SchemaValid`) when its two sides have one value wherever the values of its
  metavariables lie in the values of the types its left side's positions require and its
  reflexivity points have the values of their endpoints (`TypedInstance`); the premises a typed
  root rule would carry give such instances (`typedInstance_of_holds`). Values read only the
  constants a term mentions (`ev_congr_consts`). Traced graphs over telescopes
  (`telescopeGraph`) give their family's value at a typed instance
  (`applyValues_telescopeGraph`) and lie in the products over the telescope
  (`telescopeGraph_mem_pisCtx`); a definition by one equation whose value is the traced graph
  of its right side is valid at typed instances (`definition_valid`).
* `SetEliminators`: the numerals and `ω`, recursion on the naturals and the hereditarily
  finite sets; the least closed universe around the empty set does not contain `ω`
  (`omega_not_mem_univOf_empty`). The recursor of the natural numbers as the traced graph of
  recursion on the naturals, in the value of its declared type, with its two iota laws
  (`numRecValue_mem`, `numRecValue_zero`, `numRecValue_succ`); identity elimination as the
  traced graph returning the method, in the value of its declared type by uniqueness of
  identity proofs (`jValue_mem`), with its linear law (`jValue_apply`).
* `DomainVisibility`: a reading in which the value of a function type determines
  its domain cannot read an impredicative proposition sort as truth values: with
  the decoder rule and fewer propositions than quantifier domains, two domains
  receive one function type (`not_injective_pi_of_decoderRule`,
  `ThreeDomains.exists_same_value`); reading propositions as data avoids it.
* The concrete instantiation lives with the other concrete profiles, in
  `Instances.TowerInterpretation`: the universe package `Tower.rules` in the
  tower of universes built from `CofinalInaccessibles`, relative consistency of
  the annotated fragment and of every candidate derivation, the elaboration of
  candidate derivations, examples, controls, and the comparison square with
  the strong-normalization model (model SN).
-/
