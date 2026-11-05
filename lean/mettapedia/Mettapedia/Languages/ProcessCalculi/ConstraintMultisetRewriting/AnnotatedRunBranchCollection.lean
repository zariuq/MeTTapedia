import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRunUnfoldingWorlds
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.MeTTaOperationsCollapse
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRunEvents

/-!
# Branch collection: `superpose` and `collapse` over the unfolding

`superpose` forks worlds, and each world runs on its own copy of the store. Within a world the
alternatives are the branches of its unfolding: its terminal histories up to round equivalence,
the causal classes of `AnnotatedRunUnfoldingWorlds`. Two interleavings of one round are one
branch; two histories that no swap of rounds relates are two. `collapse` gathers the complete
answer bag over the branches of every world, each observed at its own end. This module defines
that gathering (`collectWorlds`) and connects it to the existing source-level operations; it does
not define `collapse` anew.

## The collection and its status

* **Branches** (`terminalBranches`): the causal classes of the terminal histories within a depth
  budget. An observation of configurations that depends only on their solutions and occurrences
  (`RespectsClasses`) is an observation of branches (`observeClass`), since round-equivalent
  words reach such configurations (`RoundEquiv.follow_sameUpTo`). In the fragment of
  `AnnotatedRunEvents`, a branch is observed at the end of its configuration of events
  (`observeClass_eq_endOf`).
* **Status** (`Collection`): the collection is complete exactly when the depth frontier of every
  world is closed (`collectWorlds_eq_complete_iff`), and incomplete when some world still has a
  history that can be extended (`collectWorlds_incomplete_of_open`). An incomplete collection
  that found nothing is not the complete empty collection.
* **Exactness** (`branches_exact_of_closed`): at a closed frontier the branches are exactly the
  causal classes of all terminal histories of the catalogue, with no length bound assumed.
* **Duplicates** (`collectWorlds_count`): answer counts add over worlds and branches.
* **Order** (`collectWorlds_perm`): the collection does not depend on the order of the worlds.
* **Interleavings over-count** (`branchBag_le_collect`): w10's word-level collection over the
  complete histories counts each branch at least once, and once per interleaving.

## The source-level operations

* **R17's `collapse` at one store** (`MeTTaOperationsMatch.encodedAnswers`, the bag of every
  valid single-read firing) respects classes (`encodedAnswers_respects`); the collection with it
  is the sum of the one-store collapses at the ends of the branches
  (`collectWorlds_encodedAnswers`), and the reference bags where the branches are prepared
  (`branch_reference`).
* **R16's stratification rule** (`Roles.Collection.stratified_meaning`): a world's collection taken
  after its constraints (`worldAnswers`) is the observation of the conjunction's solution, in
  every order of the constraints (`worldAnswers_meaning`, `collectAtCut_constraint_perm`).
* **w9's actual query collection** (`StratifiedCensusCollection.observe`): collected at the
  stratified cut of every world, it is the bag of w10's `collectQueries` over the solved stores
  (`collectAtCut_eq_collectQueries`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRunBranchCollection

open AnnotatedRuns
open AnnotatedRunUnfolding (frontier completed mem_completed Terminal CausalClass
  completed_exact_of_closed_frontier)
open GuardFreeProcessOrders (SameUpTo)

/-! ## Branches of a world -/

section Branches

variable {T S O : Type*} [DecidableEq O] {Answer : Type*}
variable (A : SubstitutionAction T S) (label : O → T)

/-- **Round-equivalent words reach one class**, executable or not. -/
theorem RoundEquiv.follow_sameUpTo {C : Configuration T O} {w w' : List (Firing T S O)}
    (equivalent : RoundEquiv A label C w w') : SameUpTo A (follow label C w) (follow label C w') := by
  induction equivalent with
  | rel _ _ swapped =>
      cases swapped with
      | swap u v f g isRound => exact (swap_round_executable A label u v f g C isRound).2
  | refl => exact SameUpTo.refl A _
  | symm _ _ _ ih => exact sameUpTo_symm A ih
  | trans _ _ _ _ _ first second => exact first.trans A second

omit [DecidableEq O] in
/-- An observation of configurations that depends only on their solutions and occurrences. -/
def RespectsClasses (observe : Configuration T O → Multiset Answer) : Prop :=
  ∀ C D, SameUpTo A C D → observe C = observe D

/-- **The observation of a branch**: of the configuration its histories reach. -/
def observeClass (root : Configuration T O) (observe : Configuration T O → Multiset Answer)
    (respects : RespectsClasses A observe) : CausalClass A label root → Multiset Answer :=
  Quot.lift (fun w => observe (follow label root w)) fun _ _ related =>
    respects _ _ (RoundEquiv.follow_sameUpTo A label related)

theorem observeClass_mk (root : Configuration T O) (observe : Configuration T O → Multiset Answer)
    (respects : RespectsClasses A observe) (w : List (Firing T S O)) :
    observeClass A label root observe respects (Quot.mk _ w) = observe (follow label root w) := rfl

/-- **A branch of the fragment is observed at the end of its configuration**: what a branch
answers depends only on its configuration of events. -/
theorem observeClass_eq_endOf {root : Configuration T O}
    {observe : Configuration T O → Multiset Answer} (respects : RespectsClasses A observe)
    {w : List (Firing T S O)} (run : Executable A label root w)
    (fragment : AnnotatedRunEvents.Fragment root w) :
    observeClass A label root observe respects (Quot.mk _ w) =
      observe (AnnotatedRunEvents.endOf label root (AnnotatedRunEvents.configOf label w)) :=
  respects _ _ (AnnotatedRunEvents.follow_sameUpTo_endOf A label run fragment)

open Classical in
/-- **The branches of a world** within a depth budget: the causal classes of its terminal
histories. -/
noncomputable def terminalBranches (catalogue : List (Firing T S O)) (budget : ℕ)
    (root : Configuration T O) : Finset (CausalClass A label root) :=
  ((completed A label catalogue budget root).map (Quot.mk _)).toFinset

theorem mem_terminalBranches (catalogue : List (Firing T S O)) (budget : ℕ)
    (root : Configuration T O) (trace : CausalClass A label root) :
    trace ∈ terminalBranches A label catalogue budget root ↔
      ∃ word, word.length ≤ budget ∧ Executable A label root word ∧
        (∀ f ∈ word, f ∈ catalogue) ∧ Terminal A label catalogue (follow label root word) ∧
        Quot.mk _ word = trace := by
  classical
  unfold terminalBranches
  rw [List.mem_toFinset, List.mem_map]
  constructor
  · rintro ⟨word, member, same⟩
    obtain ⟨length, run, covered, terminal⟩ := (mem_completed A label catalogue budget root word).mp member
    exact ⟨word, length, run, covered, terminal, same⟩
  · rintro ⟨word, length, run, covered, terminal, same⟩
    exact ⟨word, (mem_completed A label catalogue budget root word).mpr ⟨length, run, covered, terminal⟩,
      same⟩

/-- The depth frontier of a world is closed: every history of that depth is terminal. -/
def Closed (catalogue : List (Firing T S O)) (budget : ℕ) (root : Configuration T O) : Prop :=
  ∀ word ∈ frontier A label catalogue budget root, Terminal A label catalogue (follow label root word)

/-- **Exactness at a closed frontier**: the branches are the causal classes of all terminal
histories of the catalogue, with no length bound assumed. -/
theorem branches_exact_of_closed {catalogue : List (Firing T S O)} {budget : ℕ}
    {root : Configuration T O} (closed : Closed A label catalogue budget root)
    (trace : CausalClass A label root) :
    trace ∈ terminalBranches A label catalogue budget root ↔
      ∃ word, Executable A label root word ∧ (∀ f ∈ word, f ∈ catalogue) ∧
        Terminal A label catalogue (follow label root word) ∧ Quot.mk _ word = trace := by
  classical
  unfold terminalBranches
  rw [List.mem_toFinset, List.mem_map]
  constructor
  · rintro ⟨word, member, same⟩
    obtain ⟨run, covered, terminal⟩ :=
      (completed_exact_of_closed_frontier A label catalogue budget root closed word).mp member
    exact ⟨word, run, covered, terminal, same⟩
  · rintro ⟨word, run, covered, terminal, same⟩
    exact ⟨word, (completed_exact_of_closed_frontier A label catalogue budget root closed word).mpr
      ⟨run, covered, terminal⟩, same⟩

/-- The answers of a world: every branch, observed once at its end. -/
noncomputable def branchBag (catalogue : List (Firing T S O)) (budget : ℕ) (root : Configuration T O)
    (observe : Configuration T O → Multiset Answer) (respects : RespectsClasses A observe) :
    Multiset Answer :=
  ∑ trace ∈ terminalBranches A label catalogue budget root,
    observeClass A label root observe respects trace

omit [DecidableEq O] in
/-- Summing once per distinct image is at most summing once per element. -/
theorem sum_toFinset_le {α β γ : Type*} [DecidableEq β] (l : List α) (f : α → β)
    (g : β → Multiset γ) : ∑ b ∈ (l.map f).toFinset, g b ≤ (l.map fun a => g (f a)).sum := by
  induction l with
  | nil => simp
  | cons a rest ih =>
      rw [List.map_cons, List.toFinset_cons, List.map_cons, List.sum_cons]
      by_cases seen : f a ∈ (rest.map f).toFinset
      · rw [Finset.insert_eq_of_mem seen]
        exact ih.trans (Multiset.le_add_left _ _)
      · rw [Finset.sum_insert seen]
        exact add_le_add le_rfl ih

omit [DecidableEq O] in
theorem coe_flatMap {α γ : Type*} (l : List α) (f : α → List γ) :
    ((l.flatMap f : List γ) : Multiset γ) = (l.map fun a => (f a : Multiset γ)).sum := by
  induction l with
  | nil => rfl
  | cons a rest ih => rw [List.flatMap_cons, ← Multiset.coe_add, ih, List.map_cons, List.sum_cons]

/-- **Interleavings over-count.** The word-level collection of `AnnotatedRunUnfoldingWorlds` over
the complete histories counts every branch at least once, and once per interleaving. -/
theorem branchBag_le_collect (catalogue : List (Firing T S O)) (budget : ℕ)
    (root : Configuration T O) (observe : Configuration T O → Multiset Answer)
    (respects : RespectsClasses A observe) :
    branchBag A label catalogue budget root observe respects ≤
      (AnnotatedRunUnfolding.collect label root (fun C => (observe C).toList)
        (completed A label catalogue budget root) : Multiset Answer) := by
  classical
  rw [AnnotatedRunUnfolding.collect, coe_flatMap]
  simp only [Multiset.coe_toList]
  unfold branchBag terminalBranches
  exact sum_toFinset_le _ _ _

end Branches

/-! ## Collections with a status -/

/-- A collection, complete or not, with the answers it found. -/
inductive Collection (Answer : Type*) where
  | complete (bag : Multiset Answer)
  | incomplete (found : Multiset Answer)

namespace Collection

variable {Answer : Type*}

/-- The answers found. -/
def found : Collection Answer → Multiset Answer
  | .complete bag => bag
  | .incomplete found => found

/-- Whether the collection is complete. -/
def isComplete : Collection Answer → Bool
  | .complete _ => true
  | .incomplete _ => false

/-- **Incompleteness is not emptiness**: an incomplete collection is never complete, whatever
it found. -/
theorem incomplete_ne_complete (found bag : Multiset Answer) :
    (Collection.incomplete found : Collection Answer) ≠ .complete bag := by
  intro same
  cases same

end Collection

section Worlds

variable {T S O : Type*} [DecidableEq O] {Answer : Type*}
variable (A : SubstitutionAction T S) (label : O → T)

open Classical in
/-- **What `collapse` gathers over superposed worlds**: the answers of every branch of every world, complete
exactly when every world's frontier is closed. -/
noncomputable def collectWorlds (catalogue : List (Firing T S O)) (budget : ℕ)
    (worlds : List (Configuration T O)) (observe : Configuration T O → Multiset Answer)
    (respects : RespectsClasses A observe) : Collection Answer :=
  if ∀ root ∈ worlds, Closed A label catalogue budget root then
    .complete (worlds.map fun root => branchBag A label catalogue budget root observe respects).sum
  else
    .incomplete (worlds.map fun root => branchBag A label catalogue budget root observe respects).sum

variable {catalogue : List (Firing T S O)} {budget : ℕ} {worlds : List (Configuration T O)}
  {observe : Configuration T O → Multiset Answer} {respects : RespectsClasses A observe}

theorem collectWorlds_found :
    (collectWorlds A label catalogue budget worlds observe respects).found =
      (worlds.map fun root => branchBag A label catalogue budget root observe respects).sum := by
  classical
  unfold collectWorlds
  split <;> rfl

/-- **The collection is complete exactly when every world's frontier is closed.** -/
theorem collectWorlds_eq_complete_iff (bag : Multiset Answer) :
    collectWorlds A label catalogue budget worlds observe respects = .complete bag ↔
      (∀ root ∈ worlds, Closed A label catalogue budget root) ∧
        bag = (worlds.map fun root => branchBag A label catalogue budget root observe respects).sum := by
  classical
  unfold collectWorlds
  split
  · next closed =>
      constructor
      · intro same
        cases same
        exact ⟨closed, rfl⟩
      · rintro ⟨_, rfl⟩
        rfl
  · next open_ =>
      constructor
      · intro same
        cases same
      · rintro ⟨closed, _⟩
        exact absurd closed open_

/-- **A world with an open frontier makes the collection incomplete**, whatever it found. -/
theorem collectWorlds_incomplete_of_open {root : Configuration T O} (member : root ∈ worlds)
    (open_ : ¬ Closed A label catalogue budget root) :
    collectWorlds A label catalogue budget worlds observe respects =
      .incomplete (worlds.map fun root => branchBag A label catalogue budget root observe respects).sum := by
  classical
  unfold collectWorlds
  rw [if_neg fun closed => open_ (closed root member)]

/-- **Complete collection is exact**: every world contributes the observation of each of its
terminal causal classes, once. -/
theorem collectWorlds_complete_exact {bag : Multiset Answer}
    (complete : collectWorlds A label catalogue budget worlds observe respects = .complete bag) :
    bag = (worlds.map fun root => branchBag A label catalogue budget root observe respects).sum ∧
      ∀ root ∈ worlds, ∀ trace : CausalClass A label root,
        trace ∈ terminalBranches A label catalogue budget root ↔
          ∃ word, Executable A label root word ∧ (∀ f ∈ word, f ∈ catalogue) ∧
            Terminal A label catalogue (follow label root word) ∧ Quot.mk _ word = trace := by
  obtain ⟨closed, rfl⟩ := (collectWorlds_eq_complete_iff A label bag).mp complete
  exact ⟨rfl, fun root member trace => branches_exact_of_closed A label (closed root member) trace⟩

/-- **The order of the worlds does not matter.** -/
theorem collectWorlds_perm {worlds' : List (Configuration T O)} (perm : worlds.Perm worlds') :
    collectWorlds A label catalogue budget worlds observe respects =
      collectWorlds A label catalogue budget worlds' observe respects := by
  classical
  have sums : (worlds.map fun root => branchBag A label catalogue budget root observe respects).sum =
      (worlds'.map fun root => branchBag A label catalogue budget root observe respects).sum :=
    (perm.map _).sum_eq
  have conditions : (∀ root ∈ worlds, Closed A label catalogue budget root) ↔
      (∀ root ∈ worlds', Closed A label catalogue budget root) :=
    ⟨fun closed root member => closed root (perm.mem_iff.mpr member),
      fun closed root member => closed root (perm.mem_iff.mp member)⟩
  unfold collectWorlds
  by_cases closed : ∀ root ∈ worlds, Closed A label catalogue budget root
  · rw [if_pos closed, if_pos (conditions.mp closed), sums]
  · rw [if_neg closed, if_neg fun closed' => closed (conditions.mpr closed'), sums]

/-- **Duplicates are kept**: the count of an answer adds over the worlds and their branches. -/
theorem collectWorlds_count (a : Answer) [DecidableEq Answer] :
    Multiset.count a (collectWorlds A label catalogue budget worlds observe respects).found =
      (worlds.map fun root => ∑ trace ∈ terminalBranches A label catalogue budget root,
        Multiset.count a (observeClass A label root observe respects trace)).sum := by
  rw [collectWorlds_found]
  induction worlds with
  | nil => simp
  | cons root rest ih =>
      rw [List.map_cons, List.sum_cons, Multiset.count_add, ih, List.map_cons, List.sum_cons]
      unfold branchBag
      rw [Multiset.count_sum']

end Worlds

/-! ## R17's `collapse` at one store -/

section OneStore

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.SubstitutionAlgebra (Subst)
open MetaMeTTaComparison (atomAction)
open MeTTaOperationsMatch (encodedAnswers answerOccurrences Prepared referenceAnswers)

variable {O : Type*} [DecidableEq O]

/-- **R17's one-store `collapse` depends only on the class of the store.** -/
theorem encodedAnswers_respects (label : O → Atom) (pattern template : Atom) :
    RespectsClasses atomAction (encodedAnswers label pattern template) := by
  intro C D same
  have occurrences : answerOccurrences label pattern template C =
      answerOccurrences label pattern template D := by
    classical
    unfold answerOccurrences
    rw [same.2]
    exact Finset.filter_congr fun o _ =>
      exists_congr fun m => GuardFreeProcessOrders.valid_congr atomAction label same
  unfold encodedAnswers
  rw [occurrences]

variable (label : O → Atom) (pattern template : Atom)

/-- **The collection with R17's `collapse`**: complete collection gathers, for every world, the
one-store `collapse` at the end of each of its branches. -/
theorem collectWorlds_encodedAnswers {catalogue : List (Firing Atom Subst O)} {budget : ℕ}
    {worlds : List (Configuration Atom O)} {bag : Multiset Atom}
    (complete : collectWorlds atomAction label catalogue budget worlds
      (encodedAnswers label pattern template) (encodedAnswers_respects label pattern template) =
        .complete bag) :
    bag = (worlds.map fun root => ∑ trace ∈ terminalBranches atomAction label catalogue budget root,
      observeClass atomAction label root (encodedAnswers label pattern template)
        (encodedAnswers_respects label pattern template) trace).sum :=
  ((collectWorlds_eq_complete_iff atomAction label bag).mp complete).2

/-- At a prepared end, a branch observes R17's reference bag of the stored labels. -/
theorem branch_reference {root : Configuration Atom O} {w : List (Firing Atom Subst O)}
    (prepared : Prepared label pattern template (follow label root w)) :
    observeClass atomAction label root (encodedAnswers label pattern template)
        (encodedAnswers_respects label pattern template) (Quot.mk _ w) =
      referenceAnswers ((follow label root w).present.val.map label) pattern template :=
  MeTTaOperationsMatch.encodedAnswers_eq_reference prepared

end OneStore

/-! ## R16's stratification rule and w9's query collection -/

section StratifiedCut

open Mettapedia.GSLT.LanguageDef.SequentialBindingDiscipline
open Mettapedia.GSLT.LanguageDef.TemplateScope.Roles.Collection

variable {N V R W : Type*} [DecidableEq N] [DecidableEq V]

/-- **A world's collection at its stratified cut**: taken after the world's constraints. A world
whose constraints fail has no answers; that is a completed failure, not an unfinished search. -/
def worldAnswers (obs : Store N V → Multiset R) (constraints : W → Steps N V) (world : W) :
    Multiset R :=
  ((constrainFirst obs Store.empty (constraints world)).map Prod.fst).getD 0

/-- The answers of all worlds at their stratified cuts. -/
def collectAtCut (obs : Store N V → Multiset R) (constraints : W → Steps N V) (worlds : List W) :
    Multiset R :=
  (worlds.map (worldAnswers obs constraints)).sum

/-- **The stratification rule per world**: the collection after the constraints is the
observation of the conjunction's solution. -/
theorem worldAnswers_meaning (obs : Store N V → Multiset R) (constraints : W → Steps N V)
    (world : W) : worldAnswers obs constraints world = ((solveConj (constraints world)).map obs).getD 0 := by
  unfold worldAnswers
  rw [stratified_meaning obs (List.Perm.refl (constraints world))]
  cases solveConj (constraints world) <;> rfl

/-- **The order of each world's constraints does not matter.** -/
theorem collectAtCut_constraint_perm (obs : Store N V → Multiset R)
    {constraints constraints' : W → Steps N V} {worlds : List W}
    (reordered : ∀ world ∈ worlds, (constraints world).Perm (constraints' world)) :
    collectAtCut obs constraints worlds = collectAtCut obs constraints' worlds := by
  unfold collectAtCut
  congr 1
  apply List.map_congr_left
  intro world member
  unfold worldAnswers
  rw [stratified_perm obs (reordered world member)]

/-- **The order of the worlds does not matter.** -/
theorem collectAtCut_world_perm (obs : Store N V → Multiset R) (constraints : W → Steps N V)
    {worlds worlds' : List W} (perm : worlds.Perm worlds') :
    collectAtCut obs constraints worlds = collectAtCut obs constraints worlds' :=
  (perm.map _).sum_eq



variable {Pattern Row : Type*} [DecidableEq Row]

/-- **w9's query collection at the stratified cut of every world is w10's branch collection of
the solved stores**, as a bag. -/
theorem collectAtCut_eq_collectQueries (layer : MeTTaCalculus.OccurrenceCommits.Sources.TermLayer N V Pattern)
    (matcher : MeTTaCalculus.OccurrenceCommits.Sources.Matcher N V Pattern) (label : Row → V) (contents : List Row)
    (pattern template : Pattern) (constraints : W → Steps N V) (store : W → Store N V) :
    ∀ worlds : List W, (∀ world ∈ worlds, solveConj (constraints world) = some (store world)) →
      collectAtCut (fun state => ((StratifiedCensusCollection.observe layer matcher label contents
          pattern template state).answer : Multiset V)) constraints worlds =
        (AnnotatedRunUnfolding.collectQueries layer matcher label contents pattern template store
          worlds : Multiset V)
  | [], _ => rfl
  | world :: rest, solved => by
      have head := worldAnswers_meaning (fun state => ((StratifiedCensusCollection.observe layer
        matcher label contents pattern template state).answer : Multiset V)) constraints world
      rw [solved world List.mem_cons_self] at head
      have tail := collectAtCut_eq_collectQueries layer matcher label contents pattern template
        constraints store rest fun w member => solved w (List.mem_cons_of_mem _ member)
      unfold collectAtCut at tail ⊢
      rw [List.map_cons, List.sum_cons, tail, head]
      simp [AnnotatedRunUnfolding.collectQueries]

end StratifiedCut

#print axioms RoundEquiv.follow_sameUpTo
#print axioms observeClass_eq_endOf
#print axioms mem_terminalBranches
#print axioms branches_exact_of_closed
#print axioms Collection.incomplete_ne_complete
#print axioms sum_toFinset_le
#print axioms branchBag_le_collect
#print axioms collectWorlds_found
#print axioms collectWorlds_eq_complete_iff
#print axioms collectWorlds_incomplete_of_open
#print axioms collectWorlds_complete_exact
#print axioms collectWorlds_perm
#print axioms collectWorlds_count
#print axioms encodedAnswers_respects
#print axioms collectWorlds_encodedAnswers
#print axioms branch_reference
#print axioms worldAnswers_meaning
#print axioms collectAtCut_constraint_perm
#print axioms collectAtCut_world_perm
#print axioms collectAtCut_eq_collectQueries

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRunBranchCollection
