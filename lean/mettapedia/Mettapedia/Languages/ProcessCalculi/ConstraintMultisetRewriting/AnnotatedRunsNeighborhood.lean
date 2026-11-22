import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRunsLogicModalities
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRunsWorldModel
import Mettapedia.PLN.Bridges.GSLT.NeighborhoodProofAuthority
import Mettapedia.OSLF.Framework.WMCalculusNeighborhoodBridge

/-!
# Neighborhood modalities over runs: evidence, belief and the Kripke boundary

Worlds are histories: runs from a fixed root, at every stage. Propositions are families of
histories, the `Family` of the logic over runs. A **neighborhood function** gives, at each history,
the families that are neighborhoods there; its box holds of `ψ` at a history when `ψ` is one of
them (`box`).

## Programs are the augmented case

* The successors of a history under a program are its extensions by runs of the program
  (`successors`). The neighborhoods of a program are the supersets of its successors
  (`programNeighborhoods`): an augmented function (`programNeighborhoods_augmented`), and its box
  is the necessity along the program (`nec_eq_box`).
* A neighborhood function is augmented exactly when it is monotone and contains the meet of its
  neighborhoods (`augmented_iff`). Augmented functions are normal: their box keeps the top and
  binary meets (`Augmented.box_top`, `Augmented.box_inf`). For a monotone function, the box keeps
  binary meets exactly when neighborhoods are closed under meets (`meetClosed_iff_box_inf`).

## Evidence

* An **evidence model** gives the pieces of evidence available at each history, each a family of
  histories (`EvidenceModel`). There is evidence for `ψ` when some piece entails it
  (`evidenceFor`). Its neighborhoods are monotone (`evidenceNeighborhoods_monotone`); a program is
  the evidence model with one piece, its successors (`programNeighborhoods_eq_evidence`).
* **Evidence is not normal** (`evidence_not_normal`): with pieces for `φ` and for `ψ` and no piece
  entailing both, there is evidence for each and none for the conjunction. Such a function is not
  closed under meets, not augmented, and not the neighborhood function of any program
  (`not_meetClosed_of_separated`, `not_augmented_of_separated`, `ne_program_of_separated`).
* **Belief from evidence**, after van Benthem and Pacuit: a body of evidence is a set of available
  pieces with a common history; belief in `ψ` is entailment of `ψ` by the meet of every maximal
  consistent body (`belief`). Belief is normal (`belief_inf`, `belief_mono`). With two pieces:
  - two consistent pieces form the only maximal body, so belief is their meet
    (`belief_pair_consistent`), while evidence for the meet may be absent;
  - two conflicting pieces form two maximal bodies, so belief is their join
    (`belief_pair_conflict`): evidence for each, belief in neither.

## Evidence from the ledger

On the candidate step, the evidence at a history is the image of the ledger of the class where it
ends under a report map (`ledgerEvidenceModel`, with `ledgerClass` the ledger on classes). The
report that an observation was made in the history (`madeIn`) is true of every history that
leaves the observation present and did not start with it (`madeIn_of_mem_ledger`). Along the runs
that keep evidence the ledger only grows, so evidence for any family is an invariant of that
program (`ledgerEvidence_invariant`); retraction is what can remove it.

## The bridge to neighborhood semantics

For a small base, families are sets of histories (`toSet`, `ofSet`), and a neighborhood function
is a neighborhood frame on histories (`frame`, `frame_box`).

* The Kripke frame of a program relates a history to its extensions by the program
  (`kripkeFrame`). The neighborhood frame of the program is the canonical translation of that
  Kripke frame (`frame_program`), whose box on families is the necessity along the program
  (`programModel_box`). Points of program models are therefore Kripke-representable
  (`program_point_representable`).
* Every Kripke point satisfies `□p ∧ □q → □(p ∧ q)` (`kripke_aggregation`). A point of an evidence
  model with separated pieces refutes it (`evidence_point_refutes`), so it is not
  Kripke-representable (`evidence_point_not_representable`): evidence over runs lies strictly
  outside the Kripke boundary.
* Multisets of history points are states of the neighborhood world model, so PLN strength
  applies: the singleton state of a history has strength one for `□p` exactly when there is
  evidence there (`singleton_strength_one_iff`).
-/

set_option autoImplicit false

open CategoryTheory

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRuns

namespace NeighborhoodRuns

/-! ## Neighborhood functions on histories -/

section Frames

universe uB vB

variable {B : Type uB} [Category.{vB} B] {root : B}

/-- **A neighborhood function on histories**: the families that are neighborhoods at each
history. -/
abbrev Neighborhoods (root : B) := ∀ ⦃x : B⦄, (root ⟶ x) → Set (Family root)

/-- The box of a neighborhood function. -/
def box (N : Neighborhoods root) (ψ : Family root) : Family root := fun _ => {h | ψ ∈ N h}

theorem mem_box {N : Neighborhoods root} {ψ : Family root} {x : B} {h : root ⟶ x} :
    h ∈ box N ψ x ↔ ψ ∈ N h := Iff.rfl

/-- Neighborhoods are closed upward. -/
def IsMonotone (N : Neighborhoods root) : Prop :=
  ∀ ⦃x : B⦄ (h : root ⟶ x) ⦃X Y : Family root⦄, X ≤ Y → X ∈ N h → Y ∈ N h

/-- Neighborhoods are closed under binary meets. -/
def MeetClosed (N : Neighborhoods root) : Prop :=
  ∀ ⦃x : B⦄ (h : root ⟶ x) ⦃X Y : Family root⦄, X ∈ N h → Y ∈ N h → X ⊓ Y ∈ N h

/-- **Augmented**: at each history, the neighborhoods are the supersets of one family. -/
def Augmented (N : Neighborhoods root) : Prop :=
  ∀ ⦃x : B⦄ (h : root ⟶ x), ∃ core : Family root, ∀ X, X ∈ N h ↔ core ≤ X

/-- **Augmented exactly when monotone and containing the meet of its neighborhoods.** -/
theorem augmented_iff (N : Neighborhoods root) :
    Augmented N ↔ IsMonotone N ∧ ∀ ⦃x : B⦄ (h : root ⟶ x), sInf (N h) ∈ N h := by
  constructor
  · intro augmented
    refine ⟨fun x h X Y le member => ?_, fun x h => ?_⟩
    · obtain ⟨core, spec⟩ := augmented h
      exact (spec Y).mpr (((spec X).mp member).trans le)
    · obtain ⟨core, spec⟩ := augmented h
      exact (spec _).mpr (le_sInf fun X member => (spec X).mp member)
  · rintro ⟨mono, least⟩ x h
    exact ⟨sInf (N h), fun X => ⟨fun member => sInf_le member, fun le => mono h le (least h)⟩⟩

theorem Augmented.isMonotone {N : Neighborhoods root} (augmented : Augmented N) : IsMonotone N :=
  ((augmented_iff N).mp augmented).1

theorem Augmented.meetClosed {N : Neighborhoods root} (augmented : Augmented N) : MeetClosed N := by
  intro x h X Y first second
  obtain ⟨core, spec⟩ := augmented h
  exact (spec _).mpr (le_inf ((spec X).mp first) ((spec Y).mp second))

theorem box_mono {N : Neighborhoods root} (mono : IsMonotone N) {φ ψ : Family root} (le : φ ≤ ψ) :
    box N φ ≤ box N ψ := fun _ h member => mono h le member

/-- **For a monotone function, the box keeps binary meets exactly when neighborhoods are closed
under meets.** -/
theorem meetClosed_iff_box_inf {N : Neighborhoods root} (mono : IsMonotone N) :
    MeetClosed N ↔ ∀ φ ψ : Family root, box N (φ ⊓ ψ) = box N φ ⊓ box N ψ := by
  constructor
  · intro closed φ ψ
    funext x
    ext h
    exact ⟨fun member => ⟨mono h inf_le_left member, mono h inf_le_right member⟩,
      fun ⟨first, second⟩ => closed h first second⟩
  · intro keeps x h X Y first second
    have both : h ∈ (box N X ⊓ box N Y) x := ⟨first, second⟩
    rw [← keeps X Y] at both
    exact both

/-- **Augmented functions are normal: the box keeps binary meets.** -/
theorem Augmented.box_inf {N : Neighborhoods root} (augmented : Augmented N) (φ ψ : Family root) :
    box N (φ ⊓ ψ) = box N φ ⊓ box N ψ :=
  (meetClosed_iff_box_inf augmented.isMonotone).mp augmented.meetClosed φ ψ

/-- Augmented functions are normal: the box keeps the top. -/
theorem Augmented.box_top {N : Neighborhoods root} (augmented : Augmented N) :
    box N ⊤ = ⊤ := by
  funext x
  ext h
  obtain ⟨core, spec⟩ := augmented h
  exact ⟨fun _ => Set.mem_univ h, fun _ => (spec ⊤).mpr le_top⟩

/-! ## Programs: the augmented case -/

/-- The histories a program reaches from `h`. -/
def successors (R : Program B) {x : B} (h : root ⟶ x) : Family root :=
  fun y => {k | ∃ p : x ⟶ y, p ∈ R x y ∧ h ≫ p = k}

/-- **The neighborhoods of a program**: the supersets of the successors. -/
def programNeighborhoods (R : Program B) : Neighborhoods root :=
  fun _ h => {X | successors R h ≤ X}

/-- **A program's neighborhoods are augmented.** -/
theorem programNeighborhoods_augmented (R : Program B) :
    Augmented (programNeighborhoods (root := root) R) :=
  fun _ h => ⟨successors R h, fun _ => Iff.rfl⟩

/-- **Necessity along a program is the box of its neighborhoods.** -/
theorem nec_eq_box (R : Program B) (ψ : Family root) :
    nec R ψ = box (programNeighborhoods R) ψ := by
  funext x
  ext h
  constructor
  · rintro holds y k ⟨p, inR, rfl⟩
    exact holds p inR
  · intro holds y p inR
    exact holds y ⟨p, inR, rfl⟩

/-! ## Evidence -/

/-- **An evidence model**: the pieces of evidence available at each history. -/
abbrev EvidenceModel (root : B) := ∀ ⦃x : B⦄, (root ⟶ x) → Set (Family root)

/-- The neighborhoods of evidence: the families some available piece entails. -/
def evidenceNeighborhoods (E : EvidenceModel root) : Neighborhoods root :=
  fun _ h => {Y | ∃ X ∈ E h, X ≤ Y}

/-- **Evidence for `ψ`**: some available piece entails it. -/
def evidenceFor (E : EvidenceModel root) (ψ : Family root) : Family root :=
  box (evidenceNeighborhoods E) ψ

theorem mem_evidenceFor {E : EvidenceModel root} {ψ : Family root} {x : B} {h : root ⟶ x} :
    h ∈ evidenceFor E ψ x ↔ ∃ X ∈ E h, X ≤ ψ := Iff.rfl

theorem evidenceNeighborhoods_monotone (E : EvidenceModel root) :
    IsMonotone (evidenceNeighborhoods E) :=
  fun _ _ _ _ le ⟨X, member, below⟩ => ⟨X, member, below.trans le⟩

/-- **A program is evidence with one piece**, its successors. -/
theorem programNeighborhoods_eq_evidence (R : Program B) {x : B} (h : root ⟶ x) :
    programNeighborhoods R h =
      evidenceNeighborhoods (fun _ (k : root ⟶ _) => {successors R k}) h := by
  ext Y
  constructor
  · intro below
    exact ⟨successors R h, rfl, below⟩
  · rintro ⟨X, rfl, below⟩
    exact below

section Separated

variable {E : EvidenceModel root} {x : B} {h : root ⟶ x} {φ ψ : Family root}

/-- **Evidence is not normal**: pieces for `φ` and `ψ`, and none entailing both. -/
theorem evidence_not_normal (hφ : φ ∈ E h) (hψ : ψ ∈ E h) (none : ∀ X ∈ E h, ¬ X ≤ φ ⊓ ψ) :
    h ∈ evidenceFor E φ x ∧ h ∈ evidenceFor E ψ x ∧ h ∉ evidenceFor E (φ ⊓ ψ) x :=
  ⟨⟨φ, hφ, le_rfl⟩, ⟨ψ, hψ, le_rfl⟩, fun ⟨X, member, below⟩ => none X member below⟩

theorem not_meetClosed_of_separated (hφ : φ ∈ E h) (hψ : ψ ∈ E h)
    (none : ∀ X ∈ E h, ¬ X ≤ φ ⊓ ψ) : ¬ MeetClosed (evidenceNeighborhoods E) := fun closed =>
  (evidence_not_normal hφ hψ none).2.2 (closed h ⟨φ, hφ, le_rfl⟩ ⟨ψ, hψ, le_rfl⟩)

theorem not_augmented_of_separated (hφ : φ ∈ E h) (hψ : ψ ∈ E h)
    (none : ∀ X ∈ E h, ¬ X ≤ φ ⊓ ψ) : ¬ Augmented (evidenceNeighborhoods E) := fun augmented =>
  not_meetClosed_of_separated hφ hψ none augmented.meetClosed

/-- **Separated evidence is the neighborhood function of no program**, not even at the one
history. -/
theorem ne_program_of_separated (hφ : φ ∈ E h) (hψ : ψ ∈ E h)
    (none : ∀ X ∈ E h, ¬ X ≤ φ ⊓ ψ) (R : Program B) :
    evidenceNeighborhoods E h ≠ programNeighborhoods R h := by
  intro same
  have first : φ ∈ programNeighborhoods R h := same ▸ ⟨φ, hφ, le_rfl⟩
  have second : ψ ∈ programNeighborhoods R h := same ▸ ⟨ψ, hψ, le_rfl⟩
  have both : φ ⊓ ψ ∈ evidenceNeighborhoods E h :=
    same ▸ ((programNeighborhoods_augmented R).meetClosed h first second)
  exact (evidence_not_normal hφ hψ none).2.2 both

end Separated

/-! ## Belief from evidence -/

/-- A set of pieces is consistent when some history lies in all of them. -/
def Consistent (F : Set (Family root)) : Prop := ∃ (y : B) (k : root ⟶ y), ∀ X ∈ F, k ∈ X y

/-- A maximal consistent body of the evidence available at `h`. -/
def MaximalBody (E : EvidenceModel root) {x : B} (h : root ⟶ x) (F : Set (Family root)) : Prop :=
  F ⊆ E h ∧ Consistent F ∧ ∀ G, G ⊆ E h → Consistent G → F ⊆ G → G ⊆ F

/-- **Belief from evidence**: `ψ` is entailed by the meet of every maximal consistent body. -/
def belief (E : EvidenceModel root) (ψ : Family root) : Family root :=
  fun _ => {h | ∀ F, MaximalBody E h F → sInf F ≤ ψ}

theorem mem_belief {E : EvidenceModel root} {ψ : Family root} {x : B} {h : root ⟶ x} :
    h ∈ belief E ψ x ↔ ∀ F, MaximalBody E h F → sInf F ≤ ψ := Iff.rfl

/-- **Belief is normal**: it keeps binary meets. -/
theorem belief_inf (E : EvidenceModel root) (φ ψ : Family root) :
    belief E (φ ⊓ ψ) = belief E φ ⊓ belief E ψ := by
  funext x
  ext h
  exact ⟨fun all => ⟨fun F body => (all F body).trans inf_le_left,
      fun F body => (all F body).trans inf_le_right⟩,
    fun ⟨first, second⟩ F body => le_inf (first F body) (second F body)⟩

theorem belief_mono (E : EvidenceModel root) {φ ψ : Family root} (le : φ ≤ ψ) :
    belief E φ ≤ belief E ψ := fun _ _ all F body => (all F body).trans le

section Pairs

variable {E : EvidenceModel root} {x : B} {h : root ⟶ x} {φ ψ : Family root}

/-- **Two consistent pieces**: the only maximal body is both, so belief is their meet. -/
theorem belief_pair_consistent (pieces : E h = {φ, ψ})
    (both : ∃ (y : B) (k : root ⟶ y), k ∈ φ y ∧ k ∈ ψ y) (χ : Family root) :
    h ∈ belief E χ x ↔ φ ⊓ ψ ≤ χ := by
  have whole : Consistent ({φ, ψ} : Set (Family root)) := by
    obtain ⟨y, k, inφ, inψ⟩ := both
    refine ⟨y, k, fun X member => ?_⟩
    rcases member with rfl | rfl
    · exact inφ
    · exact inψ
  constructor
  · intro believed
    have body : MaximalBody E h {φ, ψ} :=
      ⟨pieces.symm.subset, whole, fun G sub _ _ => sub.trans pieces.subset⟩
    have := believed _ body
    rwa [sInf_pair] at this
  · intro below F body
    have all : ({φ, ψ} : Set (Family root)) ⊆ F :=
      body.2.2 {φ, ψ} pieces.symm.subset whole (body.1.trans pieces.subset)
    exact (sInf_le_sInf all).trans (by rw [sInf_pair]; exact below)

/-- **Two conflicting pieces**: each alone is a maximal body, so belief is entailment by both. -/
theorem belief_pair_conflict (pieces : E h = {φ, ψ})
    (apart : ∀ (y : B) (k : root ⟶ y), k ∈ φ y → k ∉ ψ y)
    (φSome : ∃ (y : B) (k : root ⟶ y), k ∈ φ y) (ψSome : ∃ (y : B) (k : root ⟶ y), k ∈ ψ y)
    (χ : Family root) :
    h ∈ belief E χ x ↔ φ ≤ χ ∧ ψ ≤ χ := by
  have alone : ∀ X, (∃ (y : B) (k : root ⟶ y), k ∈ X y) → Consistent ({X} : Set (Family root)) := by
    rintro X ⟨y, k, member⟩
    exact ⟨y, k, fun X' same => by rw [Set.mem_singleton_iff.mp same]; exact member⟩
  have notBoth : ∀ G : Set (Family root), Consistent G → ¬ (φ ∈ G ∧ ψ ∈ G) := by
    rintro G ⟨y, k, all⟩ ⟨inφ, inψ⟩
    exact apart y k (all φ inφ) (all ψ inψ)
  have maximal : ∀ X, X ∈ E h → (∃ (y : B) (k : root ⟶ y), k ∈ X y) → MaximalBody E h {X} := by
    intro X member nonempty
    refine ⟨Set.singleton_subset_iff.mpr member, alone X nonempty, fun G sub consistent has => ?_⟩
    intro Y inG
    have XG : X ∈ G := has rfl
    have YE := sub inG
    rw [pieces] at YE member
    rcases member with rfl | rfl <;> rcases YE with rfl | rfl
    · rfl
    · exact absurd ⟨XG, inG⟩ (notBoth G consistent)
    · exact absurd ⟨inG, XG⟩ (notBoth G consistent)
    · rfl
  constructor
  · intro believed
    have first := believed _ (maximal φ (by rw [pieces]; exact Or.inl rfl) φSome)
    have second := believed _ (maximal ψ (by rw [pieces]; exact Or.inr rfl) ψSome)
    rw [sInf_singleton] at first second
    exact ⟨first, second⟩
  · rintro ⟨first, second⟩ F body
    by_cases hasφ : φ ∈ F
    · exact (sInf_le hasφ).trans first
    by_cases hasψ : ψ ∈ F
    · exact (sInf_le hasψ).trans second
    exfalso
    have grow := body.2.2 {φ} (by rw [pieces]; exact Set.singleton_subset_iff.mpr (Or.inl rfl))
      (alone φ φSome) (by
        intro X inF
        have XE := body.1 inF
        rw [pieces] at XE
        rcases XE with rfl | rfl
        · exact absurd inF hasφ
        · exact absurd inF hasψ)
    exact hasφ (grow rfl)

end Pairs

end Frames

/-! ## Evidence from the ledger of the candidate step -/

universe uT uS uO
variable {T : Type uT} {S : Type uS} {O : Type uO} [DecidableEq O]

section Ledger

open Mettapedia.GSLT.Causality.OccurrenceHistory (OccurrencePath)

variable (A : SubstitutionAction T S) (label : O → T) (space : T → Bool)

/-- The ledger of a configuration class. -/
def ledgerClass : ConfigurationClass A O → Finset O :=
  Quotient.lift (WorldModelRuns.ledger label space) fun _ _ same =>
    WorldModelRuns.ledger_congr label space same.2

theorem ledgerClass_classOf (C : Configuration T O) :
    ledgerClass A label space (classOf A label C) = WorldModelRuns.ledger label space C := rfl

variable (C₀ : Configuration T O)

/-- **Evidence from the ledger**: at a history, the reports of the observations in the ledger of
the class where it ends. -/
def ledgerEvidenceModel (report : O → Family (runObject A label C₀)) :
    EvidenceModel (runObject A label C₀) :=
  fun x _ => report '' ↑(ledgerClass A label space x)

/-- The report that an occurrence was made in the history. -/
def madeIn (o : O) : Family (runObject A label C₀) :=
  fun _ => {h | ∃ f ∈ OccurrencePath.sites h, o ∈ f.selection.made}

theorem made_of_mem_follow (o : O) :
    ∀ {C : Configuration T O} {w : List (Firing T S O)}, o ∈ (follow label C w).present →
      o ∉ C.present → ∃ f ∈ w, o ∈ f.selection.made
  | C, [], present, absent => absurd present absent
  | C, f :: rest, present, absent => by
      by_cases made : o ∈ f.selection.made
      · exact ⟨f, List.mem_cons_self, made⟩
      · have notAfter : o ∉ (f.result label C).present := by
          intro after
          simp only [Firing.result, Selection.result, MeTTaCalculus.OccurrenceCommits.mem_fire,
            Selection.commit, List.mem_toFinset] at after
          rcases after with ⟨old, _⟩ | new
          · exact absent old
          · exact made new
        obtain ⟨g, member, inG⟩ := made_of_mem_follow o (C := f.result label C) present notAfter
        exact ⟨g, List.mem_cons_of_mem f member, inG⟩

/-- **Provenance evidence is sound**: an observation in the ledger where a history ends, absent at
its start, was made in that history. -/
theorem madeIn_of_mem_ledger {y : Runs A label} (h : runObject A label C₀ ⟶ y) {o : O}
    (inLedger : o ∈ ledgerClass A label space y) (absent : o ∉ C₀.present) :
    h ∈ madeIn A label C₀ o y := by
  have target := target_eq A label h C₀ rfl
  have present : o ∈ (follow label C₀ (OccurrencePath.sites h)).present := by
    have : o ∈ ledgerClass A label space
        (classOf A label (follow label C₀ (OccurrencePath.sites h))) := target ▸ inLedger
    exact ((WorldModelRuns.mem_ledger label space).mp this).1
  exact made_of_mem_follow label o present absent

/-- The ledger only grows along a run whose firings keep evidence. -/
theorem ledger_subset_follow_of_keeps :
    ∀ {C : Configuration T O} {w : List (Firing T S O)},
      (∀ f ∈ w, WorldModelRuns.KeepsEvidence label space f) →
        WorldModelRuns.ledger label space C ⊆ WorldModelRuns.ledger label space (follow label C w)
  | C, [], _ => subset_rfl
  | C, f :: rest, keeps => by
      have later := ledger_subset_follow_of_keeps (C := f.result label C) (w := rest)
        (fun g member => keeps g (List.mem_cons_of_mem f member))
      refine Finset.Subset.trans ?_ later
      rw [WorldModelRuns.ledger_result_of_keeps label space (keeps f List.mem_cons_self) C]
      exact Finset.subset_union_left

/-- The firings that keep evidence. -/
def keepers : Set (Firing T S O) := {f | WorldModelRuns.KeepsEvidence label space f}

/-- **Evidence from the ledger persists along the runs that keep evidence**: for every family,
evidence for it is an invariant of that program. -/
theorem ledgerEvidence_invariant (report : O → Family (runObject A label C₀))
    (ψ : Family (runObject A label C₀)) :
    Hoare (runsOf A label (keepers label space))
      (evidenceFor (ledgerEvidenceModel A label space C₀ report) ψ)
      (evidenceFor (ledgerEvidenceModel A label space C₀ report) ψ) := by
  intro x y p inR h member
  obtain ⟨C, rfl⟩ := Quotient.exists_rep x
  have target := target_eq A label p C rfl
  obtain ⟨X, ⟨o, inLedger, rfl⟩, below⟩ := member
  refine ⟨report o, ⟨o, ?_, rfl⟩, below⟩
  have grows := ledger_subset_follow_of_keeps label space (C := C) (w := OccurrencePath.sites p) inR
  rw [target, ledgerClass_classOf]
  exact Finset.mem_coe.mpr (grows (Finset.mem_coe.mp inLedger))

end Ledger

/-! ## The bridge to neighborhood semantics -/

section Bridge

open LO LO.Modal
open Mettapedia.PLN.Bridges.Logic.WorldModel.PLNWorldModelNeighborhood
open Mettapedia.PLN.Bridges.Logic.WorldModel.PLNWorldModelKripke
open Mettapedia.PLN.Bridges.Logic.WorldModel.PLNWorldModelKripkeNeighborhoodCanonical
open Mettapedia.PLN.Bridges.GSLT.NeighborhoodProofAuthority
open Mettapedia.OSLF.Framework.WMCalculusNeighborhoodBridge
open Mettapedia.PLN.WorldModel

variable {B : Type} [Category.{0} B] {root : B}

/-- A history at any stage. -/
abbrev History (root : B) := Σ y : B, (root ⟶ y)

/-- A family as a set of histories. -/
def toSet (ψ : Family root) : Set (History root) := {w | w.2 ∈ ψ w.1}

/-- A set of histories as a family. -/
def ofSet (X : Set (History root)) : Family root := fun y => {k | (⟨y, k⟩ : History root) ∈ X}

theorem ofSet_toSet (ψ : Family root) : ofSet (toSet ψ) = ψ := rfl

theorem toSet_ofSet (X : Set (History root)) : toSet (ofSet X) = X := rfl

theorem ofSet_inter (X Y : Set (History root)) : ofSet (X ∩ Y) = ofSet X ⊓ ofSet Y := rfl

/-- **The neighborhood frame on histories** of a neighborhood function. -/
def frame (N : Neighborhoods root) : Neighborhood.Frame where
  World := History root
  world_nonempty := ⟨⟨root, 𝟙 root⟩⟩
  𝒩 w := {X | ofSet X ∈ N w.2}

theorem frame_box (N : Neighborhoods root) (ψ : Family root) :
    (frame N).box (toSet ψ) = toSet (box N ψ) := rfl

/-- **The Kripke frame of a program**: a history is related to its extensions by the program. -/
def kripkeFrame (R : Program B) : Kripke.Frame where
  World := History root
  Rel w v := ∃ p : w.1 ⟶ v.1, p ∈ R w.1 v.1 ∧ w.2 ≫ p = v.2
  world_nonempty := ⟨⟨root, 𝟙 root⟩⟩

/-- **The neighborhood frame of a program is the canonical translation of its Kripke frame.** -/
theorem frame_program (R : Program B) :
    frame (root := root) (programNeighborhoods R) =
      kripkeFrameToNeighborhood (kripkeFrame (root := root) R) := by
  unfold frame kripkeFrameToNeighborhood
  congr
  funext w
  ext X
  constructor
  · rintro below v ⟨p, inR, same⟩
    exact below v.1 ⟨p, inR, same⟩
  · rintro sub y k ⟨p, inR, same⟩
    exact sub (show (kripkeFrame R).Rel w ⟨y, k⟩ from ⟨p, inR, same⟩)

/-- The Kripke model of a program with a valuation in sets of histories. -/
def kripkeModel (R : Program B) (V : ℕ → Set (History root)) : Kripke.Model where
  toFrame := kripkeFrame (root := root) R
  Val a w := w ∈ V a

/-- The neighborhood model of a program: the canonical translation of its Kripke model. -/
abbrev programModel (R : Program B) (V : ℕ → Set (History root)) : Neighborhood.Model :=
  kripkeModelToNeighborhood (kripkeModel R V)

/-- **Its box on families is necessity along the program.** -/
theorem programModel_box (R : Program B) (V : ℕ → Set (History root)) (ψ : Family root) :
    (programModel R V).box (toSet ψ) = toSet (nec R ψ) := by
  ext w
  change {v | (kripkeFrame R).Rel w v} ⊆ toSet ψ ↔ w.2 ∈ nec R ψ w.1
  rw [nec_eq_box]
  constructor
  · rintro sub y k ⟨p, inR, rfl⟩
    exact sub (show (kripkeFrame R).Rel w ⟨y, w.2 ≫ p⟩ from ⟨p, inR, rfl⟩)
  · rintro below v ⟨p, inR, same⟩
    exact below v.1 ⟨p, inR, same⟩

/-- **Points of program models are Kripke-representable.** -/
theorem program_point_representable (R : Program B) (V : ℕ → Set (History root))
    (w : History root) :
    KripkeBoundary.KripkeRepresentable ⟨programModel R V, w⟩ :=
  KripkeBoundary.canonical_point_representable ⟨kripkeModel R V, w⟩

/-- The neighborhood model of an evidence model with a valuation in sets of histories. -/
def evidenceModel (E : EvidenceModel root) (V : ℕ → Set (History root)) : Neighborhood.Model where
  toFrame := frame (evidenceNeighborhoods E)
  Val := V

/-- The aggregation formula `□p ∧ □q → □(p ∧ q)`. -/
def aggregation : Formula ℕ :=
  (□(Formula.atom 0) ⋏ □(Formula.atom 1)) ➝ □(Formula.atom 0 ⋏ Formula.atom 1)

/-- **Every Kripke point aggregates.** -/
theorem kripke_aggregation (point : PointedKripke) : point.satisfies aggregation := by
  unfold PointedKripke.satisfies aggregation
  apply (Formula.Kripke.Satisfies.imp_def (M := point.model) (x := point.world)).mpr
  intro both
  obtain ⟨first, second⟩ :=
    (Formula.Kripke.Satisfies.and_def (M := point.model) (x := point.world)).mp both
  apply (Formula.Kripke.Satisfies.box_def (M := point.model) (x := point.world)).mpr
  intro y related
  exact (Formula.Kripke.Satisfies.and_def (M := point.model) (x := y)).mpr
    ⟨(Formula.Kripke.Satisfies.box_def (M := point.model) (x := point.world)).mp first y related,
      (Formula.Kripke.Satisfies.box_def (M := point.model) (x := point.world)).mp second y related⟩

/-- The valuation sending the atoms `0` and `1` to two families. -/
def pairValuation (φ ψ : Family root) : ℕ → Set (History root)
  | 0 => toSet φ
  | 1 => toSet ψ
  | _ => ∅

/-- **A point of separated evidence refutes aggregation.** -/
theorem evidence_point_refutes {E : EvidenceModel root} {x : B} {h : root ⟶ x} {φ ψ : Family root}
    (hφ : φ ∈ E h) (hψ : ψ ∈ E h) (none : ∀ X ∈ E h, ¬ X ≤ φ ⊓ ψ) :
    ¬ (⟨evidenceModel E (pairValuation φ ψ), ⟨x, h⟩⟩ : PointedNeighborhood).satisfies
      aggregation := by
  obtain ⟨first, second, notBoth⟩ := evidence_not_normal hφ hψ none
  intro holds
  have imp := (Formula.Neighborhood.Satisfies.def_imp
    (M := evidenceModel E (pairValuation φ ψ)) (x := ⟨x, h⟩)).mp holds
  have premise : Formula.Neighborhood.Satisfies (evidenceModel E (pairValuation φ ψ)) ⟨x, h⟩
      (□(Formula.atom 0) ⋏ □(Formula.atom 1)) :=
    (Formula.Neighborhood.Satisfies.def_and (M := evidenceModel E (pairValuation φ ψ))
      (x := ⟨x, h⟩)).mpr
      ⟨(Formula.Neighborhood.Satisfies.def_box (M := evidenceModel E (pairValuation φ ψ))
          (x := ⟨x, h⟩)).mpr first,
        (Formula.Neighborhood.Satisfies.def_box (M := evidenceModel E (pairValuation φ ψ))
          (x := ⟨x, h⟩)).mpr second⟩
  have conclusion := (Formula.Neighborhood.Satisfies.def_box
    (M := evidenceModel E (pairValuation φ ψ)) (x := ⟨x, h⟩)).mp (imp premise)
  apply notBoth
  have truth : (evidenceModel E (pairValuation φ ψ)) (Formula.atom 0 ⋏ Formula.atom 1) =
      toSet φ ∩ toSet ψ := by
    simp only [Neighborhood.Model.truthset.eq_and, Neighborhood.Model.truthset.eq_atom]
    rfl
  rw [truth] at conclusion
  exact conclusion

/-- **Separated evidence over runs is not Kripke-representable.** -/
theorem evidence_point_not_representable {E : EvidenceModel root} {x : B} {h : root ⟶ x}
    {φ ψ : Family root} (hφ : φ ∈ E h) (hψ : ψ ∈ E h) (none : ∀ X ∈ E h, ¬ X ≤ φ ⊓ ψ) :
    ¬ KripkeBoundary.KripkeRepresentable ⟨evidenceModel E (pairValuation φ ψ), ⟨x, h⟩⟩ := by
  rintro ⟨point, agrees⟩
  exact evidence_point_refutes hφ hψ none ((agrees aggregation).mpr (kripke_aggregation point))

/-- **PLN strength over history points**: the singleton state of a history has strength one for
`□p` exactly when there is evidence for the family of `p` there. -/
theorem singleton_strength_one_iff (E : EvidenceModel root) (V : ℕ → Set (History root))
    (w : History root) (val : NeighborhoodValuation) (s : String)
    (state : val.stateVal s = {⟨evidenceModel E V, w⟩}) :
    BinaryWorldModel.queryStrength (State := Multiset PointedNeighborhood) (Query := Formula ℕ)
        (val.stateVal s) (□(Formula.atom 0)) = 1 ↔
      w.2 ∈ evidenceFor E (ofSet (V 0)) w.1 := by
  rw [← neighborhood_singleton_adequacy_lift val _ _ s state]
  exact Formula.Neighborhood.Satisfies.def_box (M := evidenceModel E V) (x := w)

end Bridge

end NeighborhoodRuns

open NeighborhoodRuns

#print axioms augmented_iff
#print axioms Augmented.meetClosed
#print axioms meetClosed_iff_box_inf
#print axioms Augmented.box_inf
#print axioms Augmented.box_top
#print axioms programNeighborhoods_augmented
#print axioms nec_eq_box
#print axioms evidenceNeighborhoods_monotone
#print axioms programNeighborhoods_eq_evidence
#print axioms evidence_not_normal
#print axioms not_meetClosed_of_separated
#print axioms not_augmented_of_separated
#print axioms ne_program_of_separated
#print axioms belief_inf
#print axioms belief_mono
#print axioms belief_pair_consistent
#print axioms belief_pair_conflict
#print axioms ledgerClass_classOf
#print axioms made_of_mem_follow
#print axioms madeIn_of_mem_ledger
#print axioms ledger_subset_follow_of_keeps
#print axioms ledgerEvidence_invariant
#print axioms frame_box
#print axioms frame_program
#print axioms programModel_box
#print axioms program_point_representable
#print axioms kripke_aggregation
#print axioms evidence_point_refutes
#print axioms evidence_point_not_representable
#print axioms singleton_strength_one_iff

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRuns
