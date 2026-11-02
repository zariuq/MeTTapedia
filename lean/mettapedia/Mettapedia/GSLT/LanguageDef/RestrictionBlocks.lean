import Mettapedia.GSLT.LanguageDef.RestrictionBlocks.Form
import Mettapedia.GSLT.LanguageDef.RestrictionBlocks.Signature
import Mettapedia.GSLT.LanguageDef.RestrictionBlocks.Sorted
import Mettapedia.GSLT.LanguageDef.RestrictionBlocks.Soundness
import Mettapedia.GSLT.LanguageDef.RestrictionBlocks.Completeness
import Mettapedia.GSLT.LanguageDef.RestrictionBlocks.Coherence
import Mettapedia.GSLT.LanguageDef.RestrictionBlocks.Typed
import Mettapedia.GSLT.LanguageDef.RestrictionBlocks.Generators
import Mettapedia.GSLT.LanguageDef.RestrictionBlocks.Substitution
import Mettapedia.GSLT.LanguageDef.RestrictionBlocks.Closing
import Mettapedia.GSLT.LanguageDef.RestrictionBlocks.Reactions
import Mettapedia.GSLT.LanguageDef.RestrictionBlocks.Section
import Mettapedia.GSLT.LanguageDef.RestrictionBlocks.Molecules
import Mettapedia.GSLT.LanguageDef.RestrictionBlocks.Split
import Mettapedia.GSLT.LanguageDef.RestrictionBlocks.MoleculeSplit
import Mettapedia.GSLT.LanguageDef.RestrictionBlocks.Narrow
import Mettapedia.GSLT.LanguageDef.RestrictionBlocks.Replication
import Mettapedia.GSLT.LanguageDef.RestrictionBlocks.ReplicationForm
import Mettapedia.GSLT.LanguageDef.RestrictionBlocks.ReplicationLaws
import Mettapedia.GSLT.LanguageDef.RestrictionBlocks.ReplicationSoundness
import Mettapedia.GSLT.LanguageDef.RestrictionBlocks.ReplicationCanonSound
import Mettapedia.GSLT.LanguageDef.RestrictionBlocks.Linked
import Mettapedia.GSLT.LanguageDef.RestrictionBlocks.CopyGroups
import Mettapedia.GSLT.LanguageDef.RestrictionBlocks.GroupsLinked
import Mettapedia.GSLT.LanguageDef.RestrictionBlocks.AbsorbSystem
import Mettapedia.GSLT.LanguageDef.RestrictionBlocks.ReplicationSettle
import Mettapedia.GSLT.LanguageDef.RestrictionBlocks.ReplicationSimilar
import Mettapedia.GSLT.LanguageDef.RestrictionBlocks.ReplicationNormal
import Mettapedia.GSLT.LanguageDef.RestrictionBlocks.ReplicationRestrict
import Mettapedia.GSLT.LanguageDef.RestrictionBlocks.CopyTwins
import Mettapedia.GSLT.LanguageDef.RestrictionBlocks.ReplicationRename
import Mettapedia.GSLT.LanguageDef.RestrictionBlocks.ReplicationRenamed
import Mettapedia.GSLT.LanguageDef.RestrictionBlocks.ReplicationAlike
import Mettapedia.GSLT.LanguageDef.RestrictionBlocks.ReplicationLawful
import Mettapedia.GSLT.LanguageDef.RestrictionBlocks.ReplicationContent
import Mettapedia.GSLT.LanguageDef.RestrictionBlocks.ReplicationParts
import Mettapedia.GSLT.LanguageDef.RestrictionBlocks.ReplicationShapes
import Mettapedia.GSLT.LanguageDef.RestrictionBlocks.ReplicationFreePast
import Mettapedia.GSLT.LanguageDef.RestrictionBlocks.ReplicationOrders
import Mettapedia.GSLT.LanguageDef.RestrictionBlocks.ReplicationStep
import Mettapedia.GSLT.LanguageDef.RestrictionBlocks.ReplicationFree
import Mettapedia.GSLT.LanguageDef.RestrictionBlocks.ReplicationDuplicates
import Mettapedia.GSLT.LanguageDef.RestrictionBlocks.ReplicationIdem
import Mettapedia.GSLT.LanguageDef.RestrictionBlocks.ReplicationPar
import Mettapedia.GSLT.LanguageDef.RestrictionBlocks.ReplicationClose
import Mettapedia.GSLT.LanguageDef.RestrictionBlocks.ReplicationClasses
import Mettapedia.GSLT.LanguageDef.RestrictionBlocks.ReplicationEntries
import Mettapedia.GSLT.LanguageDef.RestrictionBlocks.ReplicationEntryMoves
import Mettapedia.GSLT.LanguageDef.RestrictionBlocks.ReplicationEntryAbsorb
import Mettapedia.GSLT.LanguageDef.RestrictionBlocks.ReplicationMolecules
import Mettapedia.GSLT.LanguageDef.RestrictionBlocks.ReplicationUnfold
import Mettapedia.GSLT.LanguageDef.RestrictionBlocks.ReplicationCanonFacts
import Mettapedia.GSLT.LanguageDef.RestrictionBlocks.ReplicationEquivariance
import Mettapedia.GSLT.LanguageDef.RestrictionBlocks.ReplicationContext
import Mettapedia.GSLT.LanguageDef.RestrictionBlocks.ReplicationRawLaws
import Mettapedia.GSLT.LanguageDef.RestrictionBlocks.ReplicationTails
import Mettapedia.GSLT.LanguageDef.RestrictionBlocks.ReplicationLawsCanon
import Mettapedia.GSLT.LanguageDef.RestrictionBlocks.ReplicationKeeps
import Mettapedia.GSLT.LanguageDef.RestrictionBlocks.ReplicationLawShapes
import Mettapedia.GSLT.LanguageDef.RestrictionBlocks.ReplicationCompleteness
import Mettapedia.GSLT.LanguageDef.RestrictionBlocks.ReplicationSubstitution
import Mettapedia.GSLT.LanguageDef.RestrictionBlocks.ReplicationReference
import Mettapedia.GSLT.LanguageDef.RestrictionBlocks.ReplicationObjects
import Mettapedia.GSLT.LanguageDef.RestrictionBlocks.ReplicationInstance
import Mettapedia.GSLT.LanguageDef.RestrictionBlocks.ReplicationUnfolding
import Mettapedia.GSLT.LanguageDef.RestrictionBlocks.ProtectedRemoval
import Mettapedia.GSLT.LanguageDef.RestrictionBlocks.ReplicationProtect
import Mettapedia.GSLT.LanguageDef.RestrictionBlocks.ReplicationExposure
import Mettapedia.GSLT.LanguageDef.RestrictionBlocks.ReplicationAlign
import Mettapedia.GSLT.LanguageDef.RestrictionBlocks.ReplicationExpose
import Mettapedia.GSLT.LanguageDef.RestrictionBlocks.ReplicationSimulation
import Mettapedia.GSLT.LanguageDef.RestrictionBlocks.ReplicationReflection
import Mettapedia.GSLT.LanguageDef.RestrictionBlocks.ReplicationPresentations
import Mettapedia.GSLT.LanguageDef.RestrictionBlocks.ReplicationMultisets
import Mettapedia.GSLT.LanguageDef.RestrictionBlocks.ReplicationStore
import Mettapedia.GSLT.LanguageDef.RestrictionBlocks.ReplicationRefined
import Mettapedia.GSLT.LanguageDef.RestrictionBlocks.ReplicationSection
import Mettapedia.GSLT.LanguageDef.RestrictionBlocks.FormComputable
import Mettapedia.GSLT.LanguageDef.RestrictionBlocks.ReplicationFormComputable

/-!
# Restriction blocks: one theory for every calculus with restriction

A calculus with restriction (`BlockLanguage`) composes processes in a bare bag with a unit, binds names over
processes by a restriction, and declares exactly the laws of restriction: ν of the unit, exchange of restrictions
and scope extrusion. The theory is proved once and instantiated by each calculus.

- `Form`: the block of a process (`decompose`) and its canonical form (`canon`): the block's restrictions in the
  order that makes the sorted canonical components least, canonical parts inside every component.
- `Signature`: the laws, the class `BlockLanguage`, and the typing and bag laws it gives.
- `Sorted`: chains of laws through terms of one sort (`SortedEquiv`).
- `Soundness`: every term of every sort is related to its canonical form by such a chain (`canon_sound`).
- `Completeness`: equivalent object terms have one canonical form (`canon_complete`), so the canonical form decides
  the static theory at every sort (`equationEquiv_iff_canon_eq`).
- `Coherence`: the reference relation's equation steps are the static theory's (`equationStep_iff`).
- `Typed`, `Generators`: typing at a hole, and each law between processes as a sorted chain.
- `Substitution`, `Closing`: the theory is closed under sort-respecting substitution and under binding a free name.
- `Reactions`: for a calculus whose steps are reactions between components of a block, the canonical form steps
  with every step, to a contractum with the same canonical form (`simulation`).
- `Section`: on closed terms, the canonical form is a computable section of the static equivalence
  (`blockCanonicalSection`).
- `Molecules`, `Split`, `MoleculeSplit`, `Narrow`: a block's molecules, the components linked through its
  restrictions (`groups`); a block splits along restrictions its parts use apart (`split_equivalent`), so it is its
  molecules side by side (`molecules_equivalent`); restrictions one part uses alone narrow onto it
  (`narrow_equivalent`). These read only the signature (`BlockSignature`), so they hold with further laws too.
- `Replication`, `ReplicationForm`, `ReplicationLaws`, `ReplicationSoundness`, `ReplicationCanonSound`: a calculus with
  replication (`ReplicationLanguage`) declares `!P = {P, !P}`, `!0 = 0`, `!!P = !P`, `!{P, Q} = {!P, !Q}` and
  `{!P, !P} = !P` besides the laws of restriction. Its canonical form (`canonR`) unfolds a replicated process into one
  replicated component per molecule, absorbs copies of replicated components and keeps one of each; it is sound
  (`canonR_sound`).
- `ReplicationPar` to `ReplicationCompleteness`: the canonical form with replication is its own canonical form, and
  reads blocks side by side, closed, renamed and replicated through their canonical forms; the canonical block of an
  object term whose restrictions bind is canonical (`canonFacts`), renaming the term renames it
  (`canonP_rename`), and every context reads a part through its canonical block (`fills_context`). Each law keeps
  the canonical block of the object reading, which closes the tails a raw match of a bag leaves, so equivalent
  object terms whose restrictions bind have one canonical form (`canonR_complete`), and the canonical form decides the
  static theory with replication on object terms of a sort (`equationEquiv_iff_canonR_eq`).
- `ReplicationLawShapes`, `ReplicationSubstitution`: every law instance has one of a few shapes, one way or the other
  (`generator_lawShape`), each keeping the object reading's canonical block; a substitution of terms that are no
  abstractions keeps each shape, so the static theory with replication is closed under substitution
  (`equationEquiv_substitute_replication`), and equivalent continuations stay equivalent once a datum is received
  (`sortedEquiv_instantiate_replication`); the reference relation's equation steps are the static theory's
  (`ReplicationReference`, `equationStep_iff_replication`), and a chain of laws between object terms, read through
  its object reading, passes through object terms only (`ReplicationObjects`, `objectChain_of_equationEquiv`). The
  argument reads only the shapes of a language's laws (`ObjectShapes`), so a language with more laws, whose shapes
  keep these properties, has it too.
- `ReplicationInstance`: a minimal calculus with restriction and replication (`repLanguage`), its equivalences
  read off canonical forms by the kernel, positive and negative.
- `ReplicationUnfolding`, `ProtectedRemoval`, `ReplicationProtect`: unfolding replicated components of a block, each
  copy's block in canonical form (`Unfolds`, listed within a number of unfoldings), and removing copy groups around
  the components a redex takes, which keeps the canonical forms of the block with the redex and with what it leaves
  (`protect`).
- `ReplicationExposure`, `ReplicationAlign`, `ReplicationExpose`: a redex's parts come back in an unfolding of the
  block's canonical form, within as many unfoldings as the parts times a ceiling on the heights of the replicated
  components, read alike under a renaming, the unfolding's other components reading every context of the parts as
  the block's other components do (`exposure`).
- `ReplicationSimulation`: for a calculus with replication whose steps are reactions (`ReplicationReactions`), a step
  of any process is matched by a step of an unfolding of its canonical form, within the calculus's arity times the
  ceiling read off the canonical form, to an equivalent contractum (`replication_simulation`); canonical forms keep
  object terms and free names (`isObject_canonR`, `freeIn_canonR`). Unfoldings read as the state, so every
  presentation of a typed object process is one with its canonical form (`replicationPresentations_admitted`).
- `ReplicationReflection`: the converse, for blocks of canonical components whose replicated components copy one
  canonical component each: a reaction of an unfolding of the canonical form is a reaction of the block beside copies
  of its own replicated components, leaving what reads beside the rest as the unfolding's reaction leaves it
  (`replication_reflection`). Absorption keeps exactly the places in no copy group (`kept_block`), and the canonical
  components come from those places under one renaming fixed by the block (`reflect_kept`).
- `ReplicationPresentations`: when the replicated components of a canonical form copy one component each, a reaction
  of any unfolding is a reaction of an unfolding within the arity, the copies it does not take absorbed in what it
  leaves (`compress_flat`); so the presentations of such a state are its unfoldings within the arity, and a step of a
  process is matched by a step of a presentation of its canonical form (`replication_presented`).
- `ReplicationMultisets`: a block of plain atoms without restrictions reads as its components read again
  (`normal_plain_perm`), so two such blocks with one canonical form have components read alike, one for one
  (`plain_reads_alike`); a bag with a member whose canonical block is not inaction has a canonical block that is not
  inaction (`canonP_bag_ne_nil`). This is how a named multiset of guards, a sum, is told by its summands.
- `ReplicationStore`: a process stored as its canonical block, its steps read off by a plan the calculus gives, the
  keys its components react on and what parts leave (`StorePlan`); a replicated component generates copies and is
  never consumed. When the store's replicated components copy one component each, every successor of the store is
  equivalent to a step of an unfolding within the arity (`StorePlan.successors_sound`), and every step of the process
  ends at a process equivalent to a successor of its store (`StorePlan.successors_complete`).
- `ReplicationOrders`, `ReplicationRefined`: the orders a block is read under (`readingOrders`). A refined block is
  read only under the orders sorting its restrictions by their signatures, the profiles of the components that mention
  them; signatures are carried along renamings and kept by components read alike, so every theorem holds either way,
  and the refined labelling decides the same equivalence as the least reading over every order (`canonR_refined_iff`).
- `ReplicationFreePast`: reading a block keeps the names it uses past its restrictions, below a size, so the induction
  establishing the laws of absorption carries free names too.
- `ReplicationSection`: on closed terms, the canonical form with replication is a computable section of the static
  equivalence (`replicationCanonicalSection`): a chain through object terms from a closed term stays among closed terms.
- `FormComputable`: the canonical form is computable on codes (`FormCodes.canon_codeComputable`), read as one family
  within a fuel (`canonFamily`). `SectionEffective`, which needs the framework of effective sections and is imported
  with it rather than here, makes the canonical section effective (`blockCanonicalSection_effective`) and the static
  equivalence decidable along computable families.
- `ReplicationFormComputable`, `ReplicationSectionEffective`: the canonical form with replication is computable on codes
  (`ReplicationCodes.canonR_codeComputable`). Its normalization is a recursion in rounds (`normalFamily`): each
  absorption round asks for the canonical blocks of the patterns the round may judge (`absorbQueries`), which settle
  the absorption as the canonical form below does (`absorbOnce_congr`, `replay_roundsSoFar`), and the last round reads
  the absorbed block under its reading orders. `ReplicationSectionEffective`, imported with the framework of effective
  sections, makes its canonical section effective (`replicationCanonicalSection_effective`).
-/
