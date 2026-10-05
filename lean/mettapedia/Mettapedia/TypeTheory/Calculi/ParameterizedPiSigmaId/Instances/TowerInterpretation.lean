import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TowerInterpretation
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.TowerInterpretation.Consistency
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.TowerInterpretation.Examples
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.TowerInterpretation.Controls
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.TowerInterpretation.Square
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.TowerInterpretation.Elaboration
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.TowerInterpretation.CandidateSoundness
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.TowerInterpretation.ElaborationControls
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.TowerInterpretation.RigidCodes
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.TowerInterpretation.LevelNames
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.TowerInterpretation.LevelFamilies
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.TowerInterpretation.ParametricFamilies
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.TowerInterpretation.LevelDecoders
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.TowerInterpretation.LevelNamesModel
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.TowerInterpretation.ComputationControls
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.TowerInterpretation.ClosedChains

/-!
# The set-tower interpretation, instantiated

The generic interpretation of the annotated calculus (set model, soundness)
is in `TowerInterpretation`. This file gathers its concrete instantiation:

* `Consistency`: the candidate's universe package `Tower.rules` in the tower of
  universes built from the named hypothesis `CofinalInaccessibles`, and
  relative consistency of the annotated fragment (`fragment_consistent`).
* `Examples`: closed derivations with their candidate erasures and computed
  values.
* `Controls`: Type : Type has no set model; the model validates `UIP` and
  equality reflection and its identity lies in the h-set fragment; an
  impredicative universe with transitive value is proof-irrelevant (Cantor),
  while truth values are closed under quantification over any set.
* `Square`: the truth reading of proposition codes of the strong-normalization
  model (model SN) and the tower's truth values are isomorphic readings on the
  carriers without data, through `ZFSet` and through the hyperset tower; a
  two-point rigid type breaks it.
* `Elaboration`: every candidate derivation of `Tower.rules` over a formed
  context lifts to its annotation, the domain of every abstraction
  reconstructed (`tower_lifts`); the annotated type formers are injective
  (`towerFormerFacts`) and annotations are coherent (`tower_coherence`).
* `CandidateSoundness`: every candidate derivation over a formed context holds,
  through its elaboration, in the tower model (`Derivable.sound_tower`) and lies
  in the annotated fragment (`inAnnotatedImage`), and no closed candidate term
  has type `Π (X : U₀). X` (`candidate_consistent`), relative to
  `CofinalInaccessibles`.
* `ElaborationControls`: the domains of a Curry-style term are reconstructed
  and its value does not depend on the elaboration; a judgment over an
  ill-formed context does not elaborate; abstractions over distinct but equal
  domains are equal by one rule, and an abstraction over an ill-formed domain
  has no type.
* `RigidCodes`: the proposition codes of System F over the tower without their
  decoding, a rigid package with declared constants: every derivation lifts to
  its annotation (`codes_lifts`) and holds in the tower model with the code
  constants interpreted by truth values (`Derivable.sound_codes`); no closed
  term has type `Π (X : U₀). X` or `Π (p : prop). holds p`
  (`codes_consistent`, `codes_not_all_true`), relative to
  `CofinalInaccessibles`. A declared type with an abstraction is not rigid
  (`lamDeclared_not_rigid`).
* `LevelNames`: the levels as terms. The heads of the tower extended by the type
  of the names of the levels below a level expression and by the name of a
  level expression, with their rules under bounds on the level parameters
  (`LevelNames.Head`, `LevelNames.baseRules`); level substitution on them, and
  the tower contained in the extension (`LevelNames.tower_morphism`).
* `LevelFamilies`: families over the names of the levels below a bound, the one
  mechanism by which the package computes: a declared function on the names and
  a root step at the name of every level expression at which the family
  computes, with the typing of the name as its premise (`LevelNames.church`).
  Admission (`LevelNames.Admitted`): every value the family can compute to is
  typed. Typing and computation of an admitted family
  (`LevelNames.family_typed`, `LevelNames.family_at`); stability of derivations
  under admissible level substitutions (`LevelNames.substLevels`).
* `ParametricFamilies`: the two sources of admitted families. Values at every
  closed level, the rule with one premise for every closed level
  (`LevelNames.admitted_pointwise`); and one check of one term under a bounded
  level parameter (`LevelNames.admitted_uniform`), whose family computes at the
  name of every level expression. The successor on names, the universes at
  their precise type, and a family that uses an earlier one at the successor of
  its parameter, each from one check.
* `LevelDecoders`: the decoder from names to universes and the decoder of their
  members, two families from one check each
  (`LevelNames.decoders_admitted_over`); they compute away at the name of every
  level expression (`LevelNames.univ_at`, `LevelNames.el_at`). The polymorphic
  identity as a term under a variable name (`LevelNames.polyId_typed`) and as a
  family from one check (`LevelNames.identity_admitted`). The term computes at
  a variable name (`LevelNames.polyId_apply`), so its identity law has one proof
  by reflexivity for every level below the bound (`LevelNames.polyId_law`).
  Decoders at two
  bounds in one package: the product of the universes below a level is a member
  of the universe named by that level (`LevelNames.allUniverses_mem_above`).
  Decoding by a code of a universe does not combine with decoding by the name
  (`LevelNames.overlap_not_churchRosser`).
* `LevelNamesModel`: the set models of the level names and of every admitted
  list of families, for a package with bounds at every valuation that respects
  them (`LevelNames.familyModel`). The models differ in what they take the
  names to be (`LevelNames.NameSets`): the standard reading, in which the names
  below a level are the universes below it, and a reading with one more name.
  Soundness and relative consistency in the standard reading
  (`LevelNames.sound`, `LevelNames.consistent`). The judgment is weaker than
  its standard model: the decoders at two bounds agree at a variable name in
  the standard reading (`LevelNames.decoders_agree_holds`), and the judgment
  does not derive it (`LevelNames.decoders_agree_not_derivable`). A family with
  an untyped value has no set model
  (`LevelNames.untyped_instance_no_setModel`); without the bound a check under a
  level parameter fails (`LevelNames.next_not_typed_unbounded`); without the
  root steps the decoder at a name is not provably the universe it names
  (`LevelNames.rigid_not_equal`).
* `ComputationControls`: a root step that applies a computing constant cannot
  preserve values at every environment, since a trace function gives the empty
  set outside its domain: the δ-step of the identity on `U₀` has no set model
  (`deltaPackage_no_setModel`), yet it is valid at its typed instances
  (`delta_valid_at_typed`); and the value of a dependent function type does not
  determine its domain (`tracePiSet_domain_invisible`).
* `ClosedChains`: the tower read by any chain of closed universes, each a member
  of every later one (`ClosedChain`, `chain_setModel`), also with bounds on the
  level parameters (`chain_setModel_bounded`). The least closed universes are one
  such chain; no least closed universe is closed under the universe operation
  (`univOf_not_closed_under_univOf`).

These are set-model instances under their named hypotheses. They do not select
Prime's native set theory. The Megalodon HOTG package and its associated
examples are collected separately by `Instances.MegalodonHOTG`, which this
aggregate does not import.
-/
