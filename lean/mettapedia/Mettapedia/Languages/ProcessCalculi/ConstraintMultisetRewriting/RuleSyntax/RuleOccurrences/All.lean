import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.RuleOccurrences.Step
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.RuleOccurrences.Plain
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.RuleOccurrences.Program
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.RuleOccurrences.Derivations
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.RuleOccurrences.Atoms
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.RuleOccurrences.Protection
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.RuleOccurrences.Composition
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.RuleOccurrences.Relay
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.RuleOccurrences.Removal
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.RuleOccurrences.Publish
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.RuleOccurrences.Equations
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.RuleOccurrences.Exec
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.RuleOccurrences.Closure
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.RuleOccurrences.Dependent
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.RuleOccurrences.Congruence
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.RuleOccurrences.Derived
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.RuleOccurrences.DerivedCongruent
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.RuleOccurrences.Overlap
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.RuleOccurrences.OwnUnknowns
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.RuleOccurrences.Counting
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.RuleOccurrences.Doubling
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.RuleOccurrences.Correspondences
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.RuleOccurrences.WritingBack
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.RuleOccurrences.UsedUp
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.RuleOccurrences.SameFirings
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.RuleOccurrences.Ambient
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.RuleOccurrences.RowLocality
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.RuleOccurrences.DependentCorrespondence
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.RuleOccurrences.RuleLocality
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.RuleOccurrences.SelectionsFinite

/-!
# A candidate: the rules a firing may use are held by the state

This folder defines a **candidate** step of constraint multiset rewriting. The one-match step of a program
(`RuleSyntax/Core`) is an instance of it (`Program`).

**The candidate** (`Step`). A state holds finitely many rule occurrences beside its rows, each
labelled by a code, arguments at the state's frame (a closure), a mode (persistent or linear) and a
zone. The step has an ambient program as a parameter: a set of codes, static, possibly infinite. A
firing uses a code of the ambient program or a held occurrence; a linear occurrence is taken by its
own firing; a firing may make rule occurrences, from codes its spec names, from terms that denote
codes, or as the closed row of a term under its own information, and may remove held occurrences
whose codes its terms denote; a rule query asks that no held rule of a zone could take a row of a
pattern. Admission and the result are derived as in `RuleSyntax/Core`, and `rstep` is an
`Interface.Step.Standard`.

**The present step is its instance** (`Plain`, `Program`, `Derivations`). A firing of a plain code at
a closed state is a firing of the present step with the shapes of the rule occurrences
(`RFiring.admits_plain`). With ambient program `P` at states that hold the rules of `Q` persistently,
the transition relation is that of `step X O E (P ∪ Q)` (`program_eq`): for every program in the
ambient form (`ambient_eq`), and for the finite programs in the held form (`held_eq`,
`offers_finite`). Over each firing of the program there is one firing per use of its rule
(`fibre_use_injective`, `fibre_use_surjective`, `two_over_one`); when each rule is offered once the
candidate realizes the present step firing for firing, in the sense of
`Interface.EventMultiplicity.Realization` (`realization`, `bisimilar_program`).

**Other steps and relations.**
* `Dependent`, `DependentCorrespondence`: the dependent full step restricted to a program is the
  candidate with that program ambient (`dependent_full_eq`), by composition with
  `RuleSyntax.Dependent.dependent_eq`; as an operational correspondence, `dependentCorrespondence`.
* `Congruence`: the congruence of systems of `RuleSyntax/Equivalence` is the contextual congruence
  of the candidate's configurations in the persistent case (`ccongruent_iff`).
* `Derived`, `DerivedCongruent`: every firing of a derived link is a run of the two links it is
  derived from, ending in a state congruent with every program (`derived_firing`,
  `derived_congruent`), and the program with the derived link reaches no state that is not congruent
  to one the program without it reaches (`reach_with_derived`); a link that is not derived reaches a
  row that no run of the others reaches.
* `OwnUnknowns`: a rule and a copy with its own unknowns renamed have the same firings and results
  (`renamed_firing`, `renamed_firing_back`, `renamed_succ`, `held_renamed`).
* `Counting`: over a firing of the program there is one firing per occurrence of its rule
  (`fibre_occurrences`, `fibre_card`; `exactly_two`, `exactly_one`, `fibre_card_two`,
  `fibre_card_one`), at every frame action. The congruence of systems does not tell one occurrence
  from two
  (`ccongruent_twice`, in `Congruence`); the event bisimulation by rule and selection does, when a
  firing is determined by its rule and its selection (`not_bisimilar_of_twice`,
  `Closed.one_not_two`), and does not observe which identity holds a rule (`bisimilar_moved`).
* `Doubling`: over first-order atoms a firing has a free opening, and the state that holds a link
  once is bisimilar with multiplicities to the state that holds it twice
  (`Doubling.one_two_bisimilar`): comparing firings counts derivations only where a firing has no
  free data. The count over one firing of the program tells the two states apart there too
  (`Doubling.fibres_one_two`).
* `Correspondences`: the step of a program against the candidate, the configurations against the
  systems they present, and the program with a derived link against the program without it, are
  operational correspondences in the sense of `GSLT.IndexedOperational.OperationalCorrespondence`
  (`programCorrespondence`, `configCorrespondence`, `Derived.derivedCorrespondence`), with what each
  reaches (`program_reachable_iff`, `config_reachable_iff`, `Derived.derived_same_barbs`).
* `WritingBack`: a program and a store that holds its rules linearly, each making itself again when
  it fires, are in operational correspondence, each step one step
  (`WritingBack.consumedCorrespondence`); so holding rules persistently and holding them consumed
  and written back reach the same rows and knowledge (`WritingBack.persistent_iff_consumed`). The
  store needs a new rule identity at each firing (`WritingBack.stuck_of_no_identity`), and which one
  it takes is free data of the firing (`WritingBack.Atoms.new_identity_free`).
* `UsedUp`: with no ambient program, a store of linear rules whose codes make no rule loses an
  occurrence at every firing, and a run has at most as many firings as occurrences
  (`linear_used_up`, `linear_run_bounded`).
* `SameFirings`: two rules with the same transitions that are not renamings of each other
  (`SameFirings.silent_same`, `SameFirings.silent_not_renamed`): equality up to the names of a
  rule's own unknowns is sufficient for the same firings and not necessary.

**What holds of the candidate itself.**
* `Ambient`: a larger ambient program admits every firing a smaller one admits, with the same
  result (`succ_ambient_mono`), and the transitions beside a union of ambient programs are those
  beside one or the other (`succ_ambient_union`).
* `RowLocality`: a firing reads the present rows only through the regions of the firing read in the
  present step (`RFiring.admits_of_outsideRegions`); rule queries, installs, removals and
  publications read no row.
* `RuleLocality`: of the rules held, a firing reads the occurrence it uses, the occurrences it
  removes, the zones its rule queries name, and that the identities it makes are new
  (`RFiring.admits_of_outsideRules`).
* `SelectionsFinite`: at a finite store the admitted firings with one use, extension, opening and
  choice of made identities, installed codes, removed occurrences and published codes are finitely
  many (`RFiring.selections_finite`).
* `Protection`: adding never removes (`RFiring.held_stays`); a made occurrence lies in the zone its
  spec names; the sealed step, a restriction, changes no guarded zone along any run (`sealed_run`).
* `Composition`: holding more rules adds occurrences, so composition is not idempotent (`hold_ne`)
  and the bag of codes cancels (`codeBag_cancel`); what finite states show is countable
  (`shown_countable`).

**Models over first-order atoms at one frame** (`Atoms` holds their tools).
* `Relay`: a rule received as a message is installed and fires as a rule, for every code.
* `Removal`: a rule named by a message is removed; of two occurrences of its code one is removed
  and the other stays; a rule may remove the occurrence it uses.
* `Publish`: publishing a row is a firing that makes a rule occurrence, the closed row of the term
  under the firing's information; a tell made after the publication does not reach the published
  row, and a binding made before it is carried.
* `Equations`: an equation as one rule occurrence; the rule for an unmatched call asks about rule
  occurrences; adding an equation at run time; two copies; sealing.
* `Exec`: a linear rule is taken when it fires; a loop is a rule that makes itself again; the next
  rule by a key is a restriction of the step.
* `Closure`: a held rule that mentions an unknown of the state fires or not according to what the
  knowledge says of that unknown.
* `Overlap`: two held rules with the same take pattern, with results that agree and with results
  that differ, and the test between the two cases for rules without unknowns.
-/
