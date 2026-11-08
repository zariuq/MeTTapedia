import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.RaceRecords
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.SearchClasses

/-!
# Readouts that respect identity: answers read up to classes

R61's `collect` gathers the raw final configurations of a bounded search, one per complete run. It
counts runs, it sees the identities of occurrences, and it never sees independence. This module reads
answers up to a state equivalence instead.

## The class readout of a search (`Search.classSet`, `Search.classBag`)

An outcome's answers are read through a classifier: as a set of classes (`classSet`) or with
multiplicity (`classBag`). For a step with a transport, the classifier is the class of a state up to
isomorphism (`Transport.StateClass.mk`).

* **Finished, the class set is the classes of the ends of complete runs** (`classSet_of_finished`),
  for every set of representatives.
* **It respects the state class and does not depend on the representatives**
  (`classSet_eq_of_same`): from isomorphic starts, any two sets of representatives report the same
  answer classes at every finished budget, and they finish at the same budgets
  (`finished_iff_of_same`).

## Answers of a program, up to classes (`Answers`, `AnswerClasses`)

For the labelled step of a program (`RaceSpectrum.Moves`), the answers from a configuration are the
dead configurations it reaches; the class readout reads them through a classifier.

* **The answer system** (`answerSystem`): the labelled step observing, at each dead configuration,
  its class. Its bisimilarity (`AnswerBisimilar`) is answer-respecting bisimilarity; it implies
  bisimilarity (`bisimilar_of_answerBisimilar`), and when each label offers finitely many firings the
  Hennessy–Milner logic with answer atoms characterizes it (`answerBisimilar_iff_sat`).
* **Answer-respecting bisimilar configurations have the same answer classes**
  (`answerClasses_eq_of_answerBisimilar`).
* **Renaming.** For a program closed under the renamings that keep every label (`Equivariant`),
  configurations related by such a renaming are answer-respecting bisimilar for the classes of
  `renamingTransport` (`answerBisimilar_of_renamingIso`), so they have the same answer classes
  (`answerClasses_eq_of_renamingIso`).
* **The search computes them** (`classSet_eq_answerClasses`): for a program given by a finite
  alphabet without repetition, at every finished budget the class set of R61's search is the class
  readout of the program. Hence answer-respecting bisimilar starts, and renaming-related starts of an
  equivariant program, have equal class sets at every finished budget
  (`classSet_eq_of_answerBisimilar`, `classSet_eq_of_renamingIso`), and bisimilar starts finish at
  the same budgets (`finished_iff_of_bisimilar`).

Plain bisimilarity does not fix the answer classes, and a finite alphabet need not be equivariant;
these controls, and an equivariant finite alphabet, are in `RaceReadoutsControls`.

## The readouts stay on rung one (`Pair.classReadout_blind`)

The race pair `P`, `Q` has equal class sets and equal class bags at every budget and for every
classifier, and equal answer classes, while it is neither bisimilar nor history-preserving
bisimilar. Reading answers up to classes repairs identity, not branching.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Search

open Interface

universe uO uT uH uOcc uS uF uI u v

/-! ## Readouts of an outcome -/

section Readouts

variable {α : Type u} {β : Type v}

/-- **The class readout of an outcome**: the classes of its answers, as a set. -/
def classSet (cls : α → β) (o : Outcome α) : Set β := {b | ∃ a ∈ o.answers, cls a = b}

/-- **The class bag of an outcome**: the classes of its answers, with multiplicity. -/
def classBag (cls : α → β) (o : Outcome α) : Multiset β := o.answers.map cls

theorem mem_classSet {cls : α → β} {o : Outcome α} {b : β} :
    b ∈ classSet cls o ↔ ∃ a ∈ o.answers, cls a = b := Iff.rfl

/-- The class set is the support of the class bag. -/
theorem mem_classSet_iff_mem_classBag {cls : α → β} {o : Outcome α} {b : β} :
    b ∈ classSet cls o ↔ b ∈ classBag cls o :=
  Multiset.mem_map.symm

end Readouts

/-! ## The class readout of a search over the step -/

section Classes

variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}
  {X : Interface.Frames Tm Hom} {O : Type uOcc} [DecidableEq O] {State : Type uS}
  {Firing : State → Type uF} {P : Interface.Step X O State Firing}
  (T : Interface.Transport.{uO, uT, uH, uOcc, uS, uF, uI} P)

/-- **The answer classes of the step from a state**: the classes of the ends of its complete
runs. -/
def completeClasses (s : State) : Set T.StateClass :=
  {c | ∃ r : P.Run s, Halted P r.last ∧ Transport.StateClass.mk T r.last = c}

variable {T}

/-- **Answer classes are invariants of the state class.** -/
theorem completeClasses_eq_of_same {s t : State} (same : T.Same s t) :
    completeClasses T s = completeClasses T t := by
  have half : ∀ {s t : State}, T.Same s t → completeClasses T s ⊆ completeClasses T t := by
    rintro s t ⟨i⟩ c ⟨r, halted, rfl⟩
    have ends := Transport.Similar.same_last (Transport.Similar.moveRun i r)
    exact ⟨T.moveRun i r, halted_of_same ends halted,
      ((Transport.StateClass.mk_eq_mk_iff T).mpr ends).symm⟩
  exact Set.Subset.antisymm (half same) (half (Transport.Same.symm same))

/-- **Finished, the class readout is the answer classes of the step**, for every set of
representatives. -/
theorem classSet_of_finished (R : Representatives T) {n : ℕ} {s : State}
    (finished : (R.space.run n (.inr s)).status = .finished) :
    classSet (Transport.StateClass.mk T) (R.space.approx n (.inr s)) = completeClasses T s := by
  ext c
  refine Iff.trans ?_ (R.classes_of_finished finished c)
  constructor
  · rintro ⟨a, member, rfl⟩
    have member' : a ∈ (R.space.run n (.inr s)).answers.map Prod.snd := member
    obtain ⟨p, found, rfl⟩ := Multiset.mem_map.mp member'
    exact ⟨p, found, rfl⟩
  · rintro ⟨p, found, rfl⟩
    exact ⟨p.2, (Multiset.mem_map.mpr ⟨p, found, rfl⟩ :
      p.2 ∈ (R.space.run n (.inr s)).answers.map Prod.snd), rfl⟩

/-- **Finishing respects the state class and the choice of representatives.** -/
theorem finished_iff_of_same (R R' : Representatives T) {s t : State} (same : T.Same s t) (n : ℕ) :
    (R.space.run n (.inr s)).status = .finished ↔ (R'.space.run n (.inr t)).status = .finished := by
  rw [R.status_run_space n s, R'.status_run_space n t]
  obtain ⟨i⟩ := same
  constructor
  · intro short r
    rw [similar_length (Transport.Similar.moveRun (T.symm i) r)]
    exact short _
  · intro short r
    rw [similar_length (Transport.Similar.moveRun i r)]
    exact short _

/-- **The class readout respects the state class and does not depend on the representatives**:
from isomorphic starts, any two sets of representatives report the same answer classes at every
finished budget. -/
theorem classSet_eq_of_same (R R' : Representatives T) {s t : State} (same : T.Same s t)
    {n m : ℕ} (finished : (R.space.run n (.inr s)).status = .finished)
    (finished' : (R'.space.run m (.inr t)).status = .finished) :
    classSet (Transport.StateClass.mk T) (R.space.approx n (.inr s)) =
      classSet (Transport.StateClass.mk T) (R'.space.approx m (.inr t)) := by
  rw [classSet_of_finished R finished, classSet_of_finished R' finished',
    completeClasses_eq_of_same same]

end Classes

#print axioms mem_classSet_iff_mem_classBag
#print axioms completeClasses_eq_of_same
#print axioms classSet_of_finished
#print axioms finished_iff_of_same
#print axioms classSet_eq_of_same

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Search

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Race

open AnnotatedRuns (Firing RenamingIso renamingTransport)
open Mettapedia.GSLT.HennessyMilner (Formula System)

universe uT uS uO uL uB

variable {T : Type uT} {S : Type uS} {O : Type uO} [DecidableEq O] {L : Type uL}

/-! ## Answers of a program -/

section Answers

variable (A : SubstitutionAction T S) (label : O → T) (offers : L → Firing T S O → Prop)

/-- One move, under some label. -/
def Moved (C D : Configuration T O) : Prop := ∃ ℓ, Moves A label offers C ℓ D

/-- **A dead configuration**: no offered firing is admitted. -/
def Dead (C : Configuration T O) : Prop := ∀ ℓ D, ¬ Moves A label offers C ℓ D

/-- **The answers of a program from a configuration**: the dead configurations it reaches. -/
def Answers (C : Configuration T O) : Set (Configuration T O) :=
  {F | Relation.ReflTransGen (Moved A label offers) C F ∧ Dead A label offers F}

/-- **The class readout of a program**: its answers read through a classifier. -/
def AnswerClasses {β : Type uB} (cls : Configuration T O → β) (C : Configuration T O) : Set β :=
  cls '' Answers A label offers C

/-- **The answer system**: the labelled step observing, at each dead configuration, its class. -/
def answerSystem {β : Type uB} (cls : Configuration T O → β) : System (gslt A label offers) where
  Atom := β
  observes b C := Dead A label offers C ∧ cls C = b
  observes_resp b := by
    intro C D same
    have equal : C = D := same
    subst equal
    exact Iff.rfl
  Label := L
  act ℓ C D := Moves A label offers C ℓ D
  act_resp_left := by
    intro ℓ C C' D same step
    exact ⟨D, (same : C = C') ▸ step, rfl⟩
  act_resp_right := by
    intro ℓ C D D' step same
    exact (same : D = D') ▸ step

/-- **Answer-respecting bisimilarity**: bisimilarity of the answer system. -/
def AnswerBisimilar {β : Type uB} (cls : Configuration T O → β) (C D : Configuration T O) : Prop :=
  (answerSystem A label offers cls).Bisimilar C D

/-- Answer-respecting satisfaction: Hennessy–Milner formulas with the answer classes as atoms. -/
def AnswerSat {β : Type uB} (cls : Configuration T O → β) (φ : Formula β L)
    (C : Configuration T O) : Prop :=
  (answerSystem A label offers cls).sat φ C

variable {A label offers}

/-- **Answer-respecting bisimilarity implies bisimilarity.** -/
theorem bisimilar_of_answerBisimilar {β : Type uB} {cls : Configuration T O → β}
    {C D : Configuration T O} (bisimilar : AnswerBisimilar A label offers cls C D) :
    Bisimilar A label offers C D := by
  obtain ⟨R, ⟨forward, backward, _⟩, related⟩ := bisimilar
  exact ⟨R, ⟨forward, backward, fun _ _ _ atom => atom.elim⟩, related⟩

/-- Reaching transfers along a bisimulation. -/
theorem reaches_of_isBisimulation {β : Type uB} {cls : Configuration T O → β}
    {R : Configuration T O → Configuration T O → Prop}
    (bisimulation : (answerSystem A label offers cls).IsBisimulation R) {C D F : Configuration T O}
    (related : R C D) (reached : Relation.ReflTransGen (Moved A label offers) C F) :
    ∃ G, Relation.ReflTransGen (Moved A label offers) D G ∧ R F G := by
  induction reached with
  | refl => exact ⟨D, .refl, related⟩
  | tail _ step ih =>
      obtain ⟨G', reachedG, relatedG⟩ := ih
      obtain ⟨ℓ, moved⟩ := step
      obtain ⟨G, movedG, relatedG'⟩ := bisimulation.1 relatedG ℓ moved
      exact ⟨G, reachedG.tail ⟨ℓ, movedG⟩, relatedG'⟩

theorem answerClasses_subset_of_answerBisimilar {β : Type uB} {cls : Configuration T O → β}
    {C D : Configuration T O} (bisimilar : AnswerBisimilar A label offers cls C D) :
    AnswerClasses A label offers cls C ⊆ AnswerClasses A label offers cls D := by
  obtain ⟨R, bisimulation, related⟩ := bisimilar
  rintro b ⟨F, ⟨reached, dead⟩, rfl⟩
  obtain ⟨G, reachedG, relatedG⟩ := reaches_of_isBisimulation bisimulation related reached
  have observed : Dead A label offers G ∧ cls G = cls F :=
    (bisimulation.2.2 relatedG (cls F)).mp ⟨dead, rfl⟩
  exact ⟨G, ⟨reachedG, observed.1⟩, observed.2⟩

/-- **Answer-respecting bisimilar configurations have the same answer classes.** -/
theorem answerClasses_eq_of_answerBisimilar {β : Type uB} {cls : Configuration T O → β}
    {C D : Configuration T O} (bisimilar : AnswerBisimilar A label offers cls C D) :
    AnswerClasses A label offers cls C = AnswerClasses A label offers cls D :=
  Set.Subset.antisymm (answerClasses_subset_of_answerBisimilar bisimilar)
    (answerClasses_subset_of_answerBisimilar
      ((answerSystem A label offers cls).bisimilar_symm bisimilar))

variable (A label offers) in
/-- A program offering finitely many firings under each label gives an image-finite answer
system. -/
theorem answer_imageFiniteModulo {β : Type uB} (cls : Configuration T O → β)
    (finite : ∀ ℓ, {f | offers ℓ f}.Finite) : (answerSystem A label offers cls).ImageFiniteModulo := by
  intro ℓ C
  refine ⟨(fun f => f.result label C) '' {f | offers ℓ f}, (finite ℓ).image _, ?_⟩
  rintro D ⟨f, offered, _, rfl⟩
  exact ⟨f.result label C, ⟨f, offered, rfl⟩, rfl⟩

variable (A label offers) in
/-- **Hennessy–Milner characterization with answer atoms**: when each label offers finitely many
firings, answer-respecting bisimilarity is agreement on every formula whose atoms are answer
classes. -/
theorem answerBisimilar_iff_sat {β : Type uB} (cls : Configuration T O → β)
    (finite : ∀ ℓ, {f | offers ℓ f}.Finite) (C D : Configuration T O) :
    AnswerBisimilar A label offers cls C D ↔
      ∀ φ : Formula β L, (AnswerSat A label offers cls φ C ↔ AnswerSat A label offers cls φ D) :=
  ((answerSystem A label offers cls).logicallyEquivalent_iff_bisimilar
    (answer_imageFiniteModulo A label offers cls finite) C D).symm

end Answers

/-! ## Renaming -/

section Renaming

variable {A : SubstitutionAction T S} {label : O → T} {offers : L → Firing T S O → Prop}

variable (label offers) in
/-- **An equivariant program**: its offers are closed under the renamings that keep every label. -/
def Equivariant : Prop :=
  ∀ π : O ≃ O, (∀ o, label (π o) = label o) → ∀ ℓ f, offers ℓ f → offers ℓ (f.rename π)

/-- A move of an equivariant program has its renamed counterpart. -/
theorem renaming_forward (equivariant : Equivariant label offers) {X Y : Configuration T O}
    (i : RenamingIso A label X Y) {ℓ : L} {X' : Configuration T O}
    (moved : Moves A label offers X ℓ X') :
    ∃ Y', Moves A label offers Y ℓ Y' ∧ Nonempty (RenamingIso A label X' Y') := by
  obtain ⟨f, offered, valid, rfl⟩ := moved
  exact ⟨(f.rename i.rename).result label Y,
    ⟨f.rename i.rename, equivariant i.rename i.keeps ℓ f offered,
      (Observation.valid_renamed i.keeps i.same f).mpr valid, rfl⟩,
    ⟨⟨i.rename, i.keeps, Observation.result_renamed i.keeps i.same f⟩⟩⟩

/-- **Renaming-related configurations of an equivariant program are answer-respecting bisimilar**
for the classes of the renaming transport. -/
theorem answerBisimilar_of_renamingIso (equivariant : Equivariant label offers)
    {C D : Configuration T O} (i : RenamingIso A label C D) :
    AnswerBisimilar A label offers
      (Interface.Transport.StateClass.mk (renamingTransport A label)) C D := by
  refine ⟨fun X Y => Nonempty (RenamingIso A label X Y), ⟨?_, ?_, ?_⟩, ⟨i⟩⟩
  · rintro X Y ⟨j⟩ ℓ X' moved
    exact renaming_forward equivariant j moved
  · rintro X Y ⟨j⟩ ℓ Y' moved
    obtain ⟨X', movedX, ⟨k⟩⟩ := renaming_forward equivariant j.symm moved
    exact ⟨X', movedX, ⟨k.symm⟩⟩
  · rintro X Y ⟨j⟩ b
    have deadIff : Dead A label offers X ↔ Dead A label offers Y := by
      constructor
      · intro dead ℓ Y' moved
        obtain ⟨X', movedX, _⟩ := renaming_forward equivariant j.symm moved
        exact dead ℓ X' movedX
      · intro dead ℓ X' moved
        obtain ⟨Y', movedY, _⟩ := renaming_forward equivariant j moved
        exact dead ℓ Y' movedY
    have sameClass : Interface.Transport.StateClass.mk (renamingTransport A label) X =
        Interface.Transport.StateClass.mk (renamingTransport A label) Y :=
      (Interface.Transport.StateClass.mk_eq_mk_iff (renamingTransport A label)).mpr ⟨j⟩
    exact and_congr deadIff (by rw [sameClass])

/-- **Renaming-related configurations of an equivariant program have the same answer classes.** -/
theorem answerClasses_eq_of_renamingIso (equivariant : Equivariant label offers)
    {C D : Configuration T O} (i : RenamingIso A label C D) :
    AnswerClasses A label offers (Interface.Transport.StateClass.mk (renamingTransport A label)) C =
      AnswerClasses A label offers (Interface.Transport.StateClass.mk (renamingTransport A label)) D :=
  answerClasses_eq_of_answerBisimilar (answerBisimilar_of_renamingIso equivariant i)

end Renaming

/-! ## The search computes the class readout -/

section SearchReadout

variable {A : SubstitutionAction T S} {label : O → T} {offers : L → Firing T S O → Prop}
  {alphabet : List (Firing T S O)}

theorem moved_iff (covers : ∀ f, f ∈ alphabet ↔ ∃ ℓ, offers ℓ f) {C D : Configuration T O} :
    Moved A label offers C D ↔ ∃ f ∈ alphabet, f.Valid A label C ∧ D = f.result label C := by
  constructor
  · rintro ⟨ℓ, f, offered, valid, rfl⟩
    exact ⟨f, (covers f).mpr ⟨ℓ, offered⟩, valid, rfl⟩
  · rintro ⟨f, member, valid, rfl⟩
    obtain ⟨ℓ, offered⟩ := (covers f).mp member
    exact ⟨ℓ, f, offered, valid, rfl⟩

/-- **Dead is halted**, for the program of an alphabet that every label covers. -/
theorem dead_iff (covers : ∀ f, f ∈ alphabet ↔ ∃ ℓ, offers ℓ f) {C : Configuration T O} :
    Dead A label offers C ↔ Search.Halted (program A label alphabet) C := by
  constructor
  · rintro dead ⟨f, member⟩ valid
    obtain ⟨ℓ, offered⟩ := (covers f).mp member
    exact dead ℓ _ ⟨f, offered, valid, rfl⟩
  · rintro halted ℓ D ⟨f, offered, valid, rfl⟩
    exact halted ⟨f, (covers f).mpr ⟨ℓ, offered⟩⟩ valid

/-- **Reaching is running**: a configuration reaches another by moves exactly when a run of the
program goes there. -/
theorem reaches_iff_run (covers : ∀ f, f ∈ alphabet ↔ ∃ ℓ, offers ℓ f) {C F : Configuration T O} :
    Relation.ReflTransGen (Moved A label offers) C F ↔
      ∃ r : (program A label alphabet).Run C, r.last = F := by
  constructor
  · intro reached
    refine Relation.ReflTransGen.head_induction_on reached ⟨.nil F, rfl⟩ ?_
    intro a c step _ ih
    obtain ⟨f, member, valid, rfl⟩ := (moved_iff covers).mp step
    obtain ⟨r, last⟩ := ih
    exact ⟨.cons ⟨f, member⟩ valid r, last⟩
  · rintro ⟨r, rfl⟩
    induction r with
    | nil => exact .refl
    | cons f admitted rest ih =>
        exact Relation.ReflTransGen.head ((moved_iff covers).mpr ⟨f.1, f.2, admitted, rfl⟩) ih

/-- **Finished, the search reports exactly the answers of the program.** -/
theorem mem_approx_iff_answers (nodup : alphabet.Nodup) (covers : ∀ f, f ∈ alphabet ↔ ∃ ℓ, offers ℓ f)
    {n : ℕ} {C : Configuration T O}
    (finished : ((alternatives A label alphabet).space.run n (.inr C)).status = .finished)
    (F : Configuration T O) :
    F ∈ ((alternatives A label alphabet).space.approx n (.inr C)).answers ↔
      F ∈ Answers A label offers C := by
  let E := enumeration A label alphabet nodup
  have finishedE : (E.space.run n (.inr C)).status = .finished := finished
  have short := (E.status_run_space n C).mp finishedE
  constructor
  · intro member
    have member' : F ∈ ((alternatives A label alphabet).space.run n (.inr C)).answers.map Prod.snd :=
      member
    obtain ⟨⟨w, F'⟩, found, rfl⟩ := Multiset.mem_map.mp member'
    obtain ⟨r, _, _, _, last, halted, _⟩ := (E.mem_run_space n C w F').mp found
    exact ⟨(reaches_iff_run covers).mpr ⟨r, last⟩, (dead_iff covers).mpr halted⟩
  · rintro ⟨reached, dead⟩
    obtain ⟨r, last⟩ := (reaches_iff_run covers).mp reached
    obtain ⟨w, path⟩ := E.exists_path r
    have found : (w ++ [0], F) ∈ (E.space.run n (.inr C)).answers :=
      (E.mem_run_space n C _ F).mpr ⟨r, w, path, rfl, last, (dead_iff covers).mp dead, short r⟩
    exact (Multiset.mem_map.mpr ⟨(w ++ [0], F), found, rfl⟩ :
      F ∈ ((alternatives A label alphabet).space.run n (.inr C)).answers.map Prod.snd)

/-- **The search computes the class readout**: at every finished budget, the class set of R61's
search is the class readout of the program, for every classifier. -/
theorem classSet_eq_answerClasses (nodup : alphabet.Nodup)
    (covers : ∀ f, f ∈ alphabet ↔ ∃ ℓ, offers ℓ f) {n : ℕ} {C : Configuration T O}
    (finished : ((alternatives A label alphabet).space.run n (.inr C)).status = .finished)
    {β : Type uB} (cls : Configuration T O → β) :
    Search.classSet cls ((alternatives A label alphabet).space.approx n (.inr C)) =
      AnswerClasses A label offers cls C := by
  ext b
  constructor
  · rintro ⟨F, member, rfl⟩
    exact ⟨F, (mem_approx_iff_answers nodup covers finished F).mp member, rfl⟩
  · rintro ⟨F, answer, rfl⟩
    exact ⟨F, (mem_approx_iff_answers nodup covers finished F).mpr answer, rfl⟩

/-- A run of the program transfers along a bisimulation, with its length. -/
theorem run_of_isBisimulation (covers : ∀ f, f ∈ alphabet ↔ ∃ ℓ, offers ℓ f)
    {R : Configuration T O → Configuration T O → Prop}
    (bisimulation : (system A label offers).IsBisimulation R) :
    ∀ {C D : Configuration T O}, R C D → ∀ r : (program A label alphabet).Run C,
      ∃ r' : (program A label alphabet).Run D, r'.word.length = r.word.length
  | _, D, _, .nil _ => ⟨.nil D, rfl⟩
  | C, _, related, .cons f admitted rest => by
      obtain ⟨ℓ, offered⟩ := (covers f.1).mp f.2
      obtain ⟨_, ⟨g, offeredG, validG, rfl⟩, related'⟩ := bisimulation.1 related ℓ
        (⟨f.1, offered, admitted, rfl⟩ : Moves A label offers C ℓ (f.1.result label C))
      obtain ⟨r', length⟩ := run_of_isBisimulation covers bisimulation related' rest
      exact ⟨.cons ⟨g, (covers g).mpr ⟨ℓ, offeredG⟩⟩ validG r', congrArg (· + 1) length⟩

/-- **Bisimilar starts finish at the same budgets.** -/
theorem finished_iff_of_bisimilar (nodup : alphabet.Nodup)
    (covers : ∀ f, f ∈ alphabet ↔ ∃ ℓ, offers ℓ f) {C D : Configuration T O}
    (bisimilar : Bisimilar A label offers C D) (n : ℕ) :
    ((alternatives A label alphabet).space.run n (.inr C)).status = .finished ↔
      ((alternatives A label alphabet).space.run n (.inr D)).status = .finished := by
  let E := enumeration A label alphabet nodup
  obtain ⟨R, bisimulation, related⟩ := bisimilar
  have flipped : (system A label offers).IsBisimulation fun X Y => R Y X :=
    ⟨fun _ _ rel ℓ _ moved => bisimulation.2.1 rel ℓ moved,
      fun _ _ rel ℓ _ moved => bisimulation.1 rel ℓ moved, fun _ _ _ atom => atom.elim⟩
  show (E.space.run n (.inr C)).status = .finished ↔ (E.space.run n (.inr D)).status = .finished
  rw [E.status_run_space n C, E.status_run_space n D]
  constructor
  · intro short r
    obtain ⟨r', length⟩ := run_of_isBisimulation covers flipped related r
    rw [← length]
    exact short r'
  · intro short r
    obtain ⟨r', length⟩ := run_of_isBisimulation covers bisimulation related r
    rw [← length]
    exact short r'

/-- **Answer-respecting bisimilar starts have equal class sets at every finished budget.** -/
theorem classSet_eq_of_answerBisimilar (nodup : alphabet.Nodup)
    (covers : ∀ f, f ∈ alphabet ↔ ∃ ℓ, offers ℓ f) {n m : ℕ} {C D : Configuration T O}
    (finishedC : ((alternatives A label alphabet).space.run n (.inr C)).status = .finished)
    (finishedD : ((alternatives A label alphabet).space.run m (.inr D)).status = .finished)
    {β : Type uB} {cls : Configuration T O → β} (bisimilar : AnswerBisimilar A label offers cls C D) :
    Search.classSet cls ((alternatives A label alphabet).space.approx n (.inr C)) =
      Search.classSet cls ((alternatives A label alphabet).space.approx m (.inr D)) := by
  rw [classSet_eq_answerClasses nodup covers finishedC, classSet_eq_answerClasses nodup covers finishedD]
  exact answerClasses_eq_of_answerBisimilar bisimilar

/-- **Renaming-equivalent starts of an equivariant program have equal class sets at every finished
budget.** -/
theorem classSet_eq_of_renamingIso (nodup : alphabet.Nodup)
    (covers : ∀ f, f ∈ alphabet ↔ ∃ ℓ, offers ℓ f) (equivariant : Equivariant label offers)
    {n m : ℕ} {C D : Configuration T O}
    (finishedC : ((alternatives A label alphabet).space.run n (.inr C)).status = .finished)
    (finishedD : ((alternatives A label alphabet).space.run m (.inr D)).status = .finished)
    (i : RenamingIso A label C D) :
    Search.classSet (Interface.Transport.StateClass.mk (renamingTransport A label))
        ((alternatives A label alphabet).space.approx n (.inr C)) =
      Search.classSet (Interface.Transport.StateClass.mk (renamingTransport A label))
        ((alternatives A label alphabet).space.approx m (.inr D)) :=
  classSet_eq_of_answerBisimilar nodup covers finishedC finishedD
    (answerBisimilar_of_renamingIso equivariant i)

end SearchReadout

/-! ## The readouts stay on rung one -/

namespace Pair

variable (t : Tags T) (A : SubstitutionAction T S)

theorem covers (f : AnnotatedRuns.Firing T S Site) : f ∈ alphabet t ↔ ∃ r, offers t r f :=
  ⟨fun member => ⟨f.rule, member, rfl⟩, fun ⟨_, member, _⟩ => member⟩

theorem finished_P : ((search t A).run 3 (.inr P)).status = .finished := by
  have status : ((search t A).approx 3 (.inr P)).status = .finished := by
    rw [approx_P, approx_K, approx_Fb, approx_Fc]
    rfl
  exact status

theorem finished_Q : ((search t A).run 3 (.inr Q)).status = .finished := by
  have status : ((search t A).approx 3 (.inr Q)).status = .finished := by
    rw [← approx_P_eq_approx_Q]
    exact finished_P t A
  exact status

/-- **The class readouts stay on rung one.** For every classifier, `P` and `Q` have equal class
sets and class bags at every budget and equal answer classes, and they are neither bisimilar nor
history-preserving bisimilar. -/
theorem classReadout_blind {β : Type uB} (cls : Configuration T Site → β) (apart : t.b ≠ t.c) :
    (∀ n, Search.classSet cls ((search t A).approx n (.inr P)) =
      Search.classSet cls ((search t A).approx n (.inr Q))) ∧
    (∀ n, Search.classBag cls ((search t A).approx n (.inr P)) =
      Search.classBag cls ((search t A).approx n (.inr Q))) ∧
    AnswerClasses A (label t) (offers t) cls P = AnswerClasses A (label t) (offers t) cls Q ∧
    ¬ Bisimilar A (label t) (offers t) P Q ∧ ¬ HPBisimilar A (label t) (offers t) P Q := by
  refine ⟨fun n => by rw [approx_P_eq_approx_Q], fun n => by rw [approx_P_eq_approx_Q], ?_,
    not_bisimilar_P_Q t A apart, fun hp => not_bisimilar_P_Q t A apart (bisimilar_of_hpBisimilar hp)⟩
  rw [← classSet_eq_answerClasses (alphabet_nodup t) (covers t) (finished_P t A) cls,
    ← classSet_eq_answerClasses (alphabet_nodup t) (covers t) (finished_Q t A) cls,
    approx_P_eq_approx_Q]

end Pair

#print axioms bisimilar_of_answerBisimilar
#print axioms answerClasses_eq_of_answerBisimilar
#print axioms answerBisimilar_iff_sat
#print axioms answerBisimilar_of_renamingIso
#print axioms answerClasses_eq_of_renamingIso
#print axioms reaches_iff_run
#print axioms mem_approx_iff_answers
#print axioms classSet_eq_answerClasses
#print axioms finished_iff_of_bisimilar
#print axioms classSet_eq_of_answerBisimilar
#print axioms classSet_eq_of_renamingIso
#print axioms Pair.classReadout_blind

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Race
