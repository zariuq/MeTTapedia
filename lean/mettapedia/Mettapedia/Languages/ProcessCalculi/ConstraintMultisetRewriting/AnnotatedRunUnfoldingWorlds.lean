import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRunUnfolding
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.StratifiedCensusCollection

/-!
# Branch observations and causal classes of the finite unfolding

Each history has its own successor state. Collection flatMaps the actual
observation of each branch and preserves equal answers from distinct branches.
This is a finite branch observation, not an implementation of unrestricted
language `superpose`/`collapse`. Terminal completeness must be established
separately; a depth frontier alone does not establish it.

The causal frontier is a set of round-equivalence classes, so commuting
interleavings can be identified before assigning a weight to causal histories.
The answer bag of an explicitly branched search is a different observation.
This set quotient does not license dropping probability mass from stochastic
trajectories: a probabilistic quotient needs its own summed-mass law.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRunUnfolding

open AnnotatedRuns

variable {T S O Answer : Type*} [DecidableEq O]
variable (A : SubstitutionAction T S) (label : O → T)

abbrev CausalClass (root : Configuration T O) := Quot (RoundEquiv A label root)

/-- Exactly one representative class per causal history at this depth. -/
noncomputable def causalFrontier (catalogue : List (Firing T S O)) (depth : Nat)
    (root : Configuration T O) : Finset (CausalClass A label root) := by
  classical
  exact ((frontier A label catalogue depth root).map (Quot.mk _)).toFinset

theorem mem_causalFrontier (catalogue : List (Firing T S O)) (depth : Nat)
    (root : Configuration T O) (trace : CausalClass A label root) :
    trace ∈ causalFrontier A label catalogue depth root ↔
      ∃ word, word.length = depth ∧ Executable A label root word ∧
        (∀ firing ∈ word, firing ∈ catalogue) ∧ Quot.mk _ word = trace := by
  classical
  simp only [causalFrontier, List.mem_toFinset, List.mem_map, mem_frontier]
  constructor
  · rintro ⟨word, ⟨length, executable, covered⟩, same⟩
    exact ⟨word, length, executable, covered, same⟩
  · rintro ⟨word, length, executable, covered, same⟩
    exact ⟨word, ⟨length, executable, covered⟩, same⟩

/-- Collect from explicitly identified branches, keeping their multiplicity. -/
def collect (root : Configuration T O) (observe : Configuration T O → List Answer)
    (worlds : List (List (Firing T S O))) : List Answer :=
  worlds.flatMap fun history => observe (follow label root history)

theorem collect_append (root : Configuration T O) (observe : Configuration T O → List Answer)
    (first second : List (List (Firing T S O))) :
    collect label root observe (first ++ second) =
      collect label root observe first ++ collect label root observe second := by
  simp [collect]

/-- Reordering the branch traversal preserves answer multiplicity. -/
theorem collect_perm (root : Configuration T O) (observe : Configuration T O → List Answer)
    {first second : List (List (Firing T S O))} (permuted : first.Perm second) :
    (collect label root observe first).Perm (collect label root observe second) :=
  permuted.flatMap_right _

theorem mem_collect_frontier (catalogue : List (Firing T S O)) (depth : Nat)
    (root : Configuration T O) (observe : Configuration T O → List Answer) (answer : Answer) :
    answer ∈ collect label root observe (frontier A label catalogue depth root) ↔
      ∃ word, word.length = depth ∧ Executable A label root word ∧
        (∀ firing ∈ word, firing ∈ catalogue) ∧ answer ∈ observe (follow label root word) := by
  simp only [collect, List.mem_flatMap, mem_frontier]
  constructor
  · rintro ⟨word, ⟨length, executable, covered⟩, member⟩
    exact ⟨word, length, executable, covered, member⟩
  · rintro ⟨word, length, executable, covered, member⟩
    exact ⟨word, ⟨length, executable, covered⟩, member⟩

section Stratified

open Mettapedia.Machines
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits
open Mettapedia.GSLT.LanguageDef.SequentialBindingDiscipline
open Mettapedia.GSLT.LanguageDef.TemplateScope.Roles.Collection

variable {N Value Pattern Row World : Type*} [DecidableEq Row]

/-- Concrete query collection in each supplied branch: this invokes w9's
existing scanner observation, not a separately supplied answer list. -/
def collectQueries (layer : Sources.TermLayer N Value Pattern)
    (matcher : Sources.Matcher N Value Pattern) (label : Row → Value)
    (contents : List Row) (pattern template : Pattern)
    (store : World → Store N Value) (worlds : List World) : List Value :=
  worlds.flatMap fun world =>
    (StratifiedCensusCollection.observe layer matcher label contents pattern template (store world)).answer

/-- When each branch's dependencies are determined, refining its store
leaves the actual collected answer sequence unchanged. Scanner order and row
view are deliberately fixed, exactly as in the source theorem. -/
theorem collectQueries_stable (layer : Sources.TermLayer N Value Pattern)
    (matcher : Sources.Matcher N Value Pattern) (label : Row → Value)
    (contents : List Row) (pattern template : Pattern) (names : List N)
    (regionReads : ∀ value, ReadsOnly names
      (fun state => Sources.Matcher.region matcher state pattern value))
    (valueReads : ∀ value, ReadsOnly names
      (fun state => StratifiedCensusCollection.emitted layer matcher pattern template state value))
    (first second : World → Store N Value) (worlds : List World)
    (determined : ∀ world ∈ worlds, Determined names (first world))
    (refines : ∀ world ∈ worlds, first world ⊑ second world) :
    collectQueries layer matcher label contents pattern template second worlds =
      collectQueries layer matcher label contents pattern template first worlds := by
  induction worlds with
  | nil => rfl
  | cons world rest ih =>
    have same := StratifiedCensusCollection.stable_after_determination layer matcher label
      contents pattern template names regionReads valueReads
      (determined world (by simp)) (refines world (by simp))
    exact congrArg₂ (· ++ ·) (congrArg (fun packet => packet.1.answer) same)
      (ih (fun w member => determined w (List.mem_cons_of_mem _ member))
        (fun w member => refines w (List.mem_cons_of_mem _ member)))

end Stratified

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRunUnfolding
