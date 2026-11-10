import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Permissions
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.DisequalityFramesStep
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.DependentFull

/-!
# Read polarity of permissions at the interface

`Permissions` proves the two read-polarity results on the located first-order step. Here they hold
for every instance of `Interface.Step`, and the first-order statements are corollaries.

## Owned existential reads (`witness_present`, any instance)

A present occurrence at a space where the firing lacks `receive` is present after the firing.
`Permissions.owned_witness_present` is its first-order instance (`old_owned_witness_present`).

## Owned universal reads (`absence_preserved`, any instance whose labels move along firings)

Absence needs labels, which the interface does not carry. A **label transport** of an instance gives
every state a label for each occurrence at its frame, and its law (`LabelLaw`): an occurrence that an
admitted firing does not make keeps its label, read along the firing's morphism of frames.

* **The restriction.** For every instance with a lawful label transport, an absence at a space that
  the knowledge entails stays entailed, read along the firing, after any admitted firing formed under
  rights without `send` there (`absence_preserved`).
* **It holds for the main row-bearing instances**: the located first-order step (`locatedLabels`,
  with `old_owned_absence_preserved` the corollary that is `Permissions.owned_absence_preserved`) and
  the dependent full step (`dependentLabels`, `dependent_absence_preserved`).
* **The separating control** (`Controls.relabel_spoils_absence`): an instance whose firing relabels a
  present row without making it, at a space without `send`, is permitted and spoils the absence. The
  law is the exact hypothesis that rules this out.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.PermissionsInterface

open Interface (Frames)
open MeTTaCalculus.OccurrenceCommits (Commit Enabled fire mem_fire)
open MeTTaCalculus.InteractionTypes (Facet Rights FormedUnder)
open Permissions (Permitted)

universe uO uT uH uOcc uS uF uN

section Generic

variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}
  {X : Frames Tm Hom} {O : Type uOcc} [DecidableEq O] {State : Type uS} {Firing : State → Type uF}
  (P : Interface.Step X O State Firing) {H : Type uN} (space : O → H) (Γ : Rights H)

/-- **Owned existential reads are stable, in every instance**: a witness at a space where the firing
lacks `receive` is still present after it. -/
theorem witness_present {s : State} {f : Firing s} (admitted : P.Admits f) (formed : Permitted P space Γ f)
    {o : O} (present : o ∈ P.present s) (owned : Γ (space o) .receive = false) :
    o ∈ P.present (P.result f admitted) := by
  rw [P.present_result f admitted]
  refine mem_fire.mpr (Or.inl ⟨present, fun taken => ?_⟩)
  have allowed := formed.taken o (by simpa [Selection.commit] using taken)
  simp [owned] at allowed

/-- **The law of a label transport**: an occurrence that an admitted firing does not make keeps its
label, read along the firing's morphism of frames. -/
def LabelLaw (label : (s : State) → O → Tm (P.frame s)) : Prop :=
  ∀ {s : State} (f : Firing s) (admitted : P.Admits f) (o : O), o ∉ (P.selection f).made →
    label (P.result f admitted) o = X.act (P.along f admitted) (label s o)

/-- The absence of a pattern among the present occurrences at the space `h`, at one solution. -/
def AbsentAt (label : (s : State) → O → Tm (P.frame s)) (h : H) {s : State} (p : Tm (P.frame s))
    {b : Obj} (σ : Hom (P.frame s) b) : Prop :=
  ∀ o ∈ P.present s, space o = h → ¬ X.E (X.act σ p) (X.act σ (label s o))

/-- **Owned universal reads are stable, in every instance with a lawful label transport**: an
absence at a space that the knowledge entails stays entailed after any admitted firing formed under
rights without `send` there, the pattern read along the firing. -/
theorem absence_preserved (label : (s : State) → O → Tm (P.frame s)) (law : LabelLaw P label)
    {s : State} {f : Firing s} (admitted : P.Admits f) (formed : Permitted P space Γ f) {h : H}
    (owned : Γ h .send = false) {p : Tm (P.frame s)}
    (absent : X.Entails (P.knowledge s) (fun _ σ => AbsentAt P space label h p σ)) :
    X.Entails (P.knowledge (P.result f admitted))
      (fun _ τ => AbsentAt P space label h (X.act (P.along f admitted) p) τ) := by
  intro b τ solved o present atH same
  have earlier := P.models_along admitted τ solved
  have fired : o ∈ fire (P.present s) ((P.selection f).commit (T := Unit)) := by
    rw [← P.present_result f admitted]
    exact present
  rcases mem_fire.mp fired with ⟨old, _⟩ | made
  · have notMade : o ∉ (P.selection f).made := fun inside =>
      Finset.disjoint_left.mp (P.prepares admitted).2.1.fresh
        (by simpa [Selection.commit] using inside) old
    rw [law f admitted o notMade] at same
    apply absent b (X.comp τ (P.along f admitted)) earlier o old atH
    rw [X.act_comp, X.act_comp]
    exact same
  · have allowed := formed.made o (by simpa [Selection.commit] using made)
    simp [atH, owned] at allowed

end Generic

/-! ## The located first-order step -/

section Located

universe uA uB uC uD

variable {T : Type uA} {S : Type uB} {H : Type uC} {O : Type uD} [DecidableEq O] [DecidableEq H]
  (A : SubstitutionAction T S) (space : O → H) (payload : O → T) (Γ : Rights H)

/-- The labels of the located first-order step: a handle and a payload, at every state. -/
def locatedLabels : (C : Configuration (H × T) O) → O → H × T :=
  fun _ => Spaces.label space payload

omit [DecidableEq H] in
/-- **They move along firings.** -/
theorem locatedLabels_law :
    LabelLaw (Spaces.located A space payload).toStep (locatedLabels space payload) := by
  intro C f admitted o _
  show Spaces.label space payload o =
    (LocatedSubstitution.action (N := H) A).apply
      ((LocatedSubstitution.action (N := H) A).compose (LocatedSubstitution.action (N := H) A).identity
        (LocatedSubstitution.action (N := H) A).identity) (Spaces.label space payload o)
  rw [(LocatedSubstitution.action (N := H) A).apply_compose, (LocatedSubstitution.action (N := H) A).apply_identity,
    (LocatedSubstitution.action (N := H) A).apply_identity]

omit [DecidableEq H] in
/-- At the located step, the absence of `p` among all rows is its absence among the rows at `p`'s
handle: rows at other handles never match. -/
theorem absent_iff_absentAt {C : Configuration (H × T) O} (p : H × T) (σ : S) :
    (Check.absent p).Holds (LocatedSubstitution.action (N := H) A) σ (Spaces.label space payload) C.present ↔
      AbsentAt (Spaces.located A space payload).toStep space (locatedLabels space payload) p.1 (s := C) p
        (b := PUnit.unit) σ := by
  constructor
  · intro holds o present _
    exact holds o present
  · intro holds o present same
    exact holds o present same.1.symm same

omit [DecidableEq H] in
/-- **`Permissions.owned_witness_present` is the first-order instance of `witness_present`.** -/
theorem old_owned_witness_present {C : Configuration (H × T) O} {f : AnnotatedRuns.Firing (H × T) S O}
    (admitted : (Spaces.located A space payload).toStep.Admits (s := C) f)
    (formed : Permissions.LocatedPermitted space Γ f) {o : O} (present : o ∈ C.present)
    (owned : Γ (space o) .receive = false) :
    o ∈ ((Spaces.located A space payload).toStep.result f admitted).present :=
  witness_present (Spaces.located A space payload).toStep space Γ admitted formed present owned

omit [DecidableEq H] in
/-- **`Permissions.owned_absence_preserved` is the first-order instance of `absence_preserved`.** -/
theorem old_owned_absence_preserved {C : Configuration (H × T) O} {f : AnnotatedRuns.Firing (H × T) S O}
    (admitted : (Spaces.located A space payload).toStep.Admits (s := C) f)
    (formed : Permissions.LocatedPermitted space Γ f) {p : H × T} (owned : Γ p.1 .send = false)
    (absent : (LocatedSubstitution.action (N := H) A).Entails C.equations
      (fun σ => (Check.absent p).Holds (LocatedSubstitution.action (N := H) A) σ
        (Spaces.label space payload) C.present)) :
    (LocatedSubstitution.action (N := H) A).Entails
      ((Spaces.located A space payload).toStep.result f admitted).equations
      (fun σ => (Check.absent p).Holds (LocatedSubstitution.action (N := H) A) σ
        (Spaces.label space payload) ((Spaces.located A space payload).toStep.result f admitted).present) := by
  have general := absence_preserved (Spaces.located A space payload).toStep space Γ (locatedLabels space payload)
    (locatedLabels_law A space payload) admitted formed owned (p := p)
    (fun _ σ solved => (absent_iff_absentAt A space payload p σ).mp (absent σ solved))
  intro σ solved
  have holds := general PUnit.unit σ solved
  have moved : (LocatedSubstitution.action (N := H) A).apply
      ((LocatedSubstitution.action (N := H) A).compose (LocatedSubstitution.action (N := H) A).identity
        (LocatedSubstitution.action (N := H) A).identity) p = p := by
    rw [(LocatedSubstitution.action (N := H) A).apply_compose,
      (LocatedSubstitution.action (N := H) A).apply_identity,
      (LocatedSubstitution.action (N := H) A).apply_identity]
  change AbsentAt (Spaces.located A space payload).toStep space (locatedLabels space payload) p.1
    (s := (Spaces.located A space payload).toStep.result f admitted)
    ((LocatedSubstitution.action (N := H) A).apply
      ((LocatedSubstitution.action (N := H) A).compose (LocatedSubstitution.action (N := H) A).identity
        (LocatedSubstitution.action (N := H) A).identity) p) (b := PUnit.unit) σ at holds
  rw [moved] at holds
  exact (absent_iff_absentAt A space payload p σ).mpr holds

end Located

/-! ## The dependent full step -/

section Dependent

open _root_.CategoryTheory
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta
open Interface.DependentFull

variable {Head L : Type} [UniverseLevel.LevelOrder L] {rules : Rules Head} (levels : LevelModel rules L)
  (O : Type) [DecidableEq O]

/-- The labels of the dependent full step: the typed rows of each state. -/
def dependentLabels : (s : State rules O) → O → TotalTerm s.frame := fun s => s.label

/-- **They move along firings**: a row the firing does not make is its old label read along the
weakening. -/
theorem dependentLabels_law : LabelLaw (step levels O).toStep (dependentLabels O) := by
  intro s f admitted o notMade
  show (f.after admitted).label o =
    (frames levels).act ((frames levels).comp ((frames levels).id f.helpers.frame) f.helpers.weaken) (s.label o)
  rw [Firing.label_after_of_not_mem f admitted notMade, (frames levels).act_comp, (frames levels).act_id]
  rfl

variable {levels O}

/-- **Owned universal reads are stable at dependent frames.** -/
theorem dependent_absence_preserved {H : Type} (space : O → H) (Γ : Rights H) {s : State rules O}
    {f : Firing levels s} (admitted : (step levels O).toStep.Admits f)
    (formed : Permitted (step levels O).toStep space Γ f) {h : H} (owned : Γ h .send = false)
    {p : TotalTerm s.frame}
    (absent : (frames levels).Entails s.knowledge
      (fun _ σ => AbsentAt (step levels O).toStep space (dependentLabels O) h p σ)) :
    (frames levels).Entails (f.after admitted).knowledge
      (fun _ τ => AbsentAt (step levels O).toStep space (dependentLabels O) h
        ((frames levels).act ((step levels O).toStep.along f admitted) p) τ) :=
  absence_preserved (step levels O).toStep space Γ (dependentLabels O) (dependentLabels_law levels O) admitted formed
    owned absent

end Dependent

/-! ## The separating control: relabelling without making -/

namespace Controls

open DisequalityFrames (Prestep)

/-- The action on numbers with one substitution, the identity. -/
def trivial : SubstitutionAction Nat Unit where
  E := Eq
  equivalence := ⟨Eq.refl, Eq.symm, Eq.trans⟩
  apply _ t := t
  identity := ()
  compose _ _ := ()
  apply_identity _ := rfl
  apply_compose _ _ _ := rfl
  preserves _ _ _ same := same

/-- A state: present occurrences and their labels. -/
structure RState where
  present : Finset Nat
  label : Nat → Nat

/-- An instance whose only firing relabels an occurrence: it takes, reads and makes nothing. -/
def relabel : Prestep (Frames.ofSubstitution trivial) Nat RState (fun _ => Nat × Nat) where
  frame _ := PUnit.unit
  knowledge _ := []
  present s := s.present
  selection _ := ⟨[], [], []⟩
  target _ := PUnit.unit
  extension _ := ()
  information _ := []
  transported _ _ member := absurd member List.not_mem_nil
  Shapes {s} f := f.1 ∈ s.present
  Holds _ _ σ := (Frames.ofSubstitution trivial).Models (a := PUnit.unit) (b := PUnit.unit) σ []
  result {s} f _ := ⟨s.present, Function.update s.label f.1 f.2⟩
  present_result _ _ := by
    ext o
    simp [MeTTaCalculus.OccurrenceCommits.fire, Selection.commit]
  settle _ _ := ()
  knowledge_result _ _ := rfl

abbrev P := relabel.step.toStep

def start : RState := ⟨{0}, fun _ => 1⟩

/-- Only space `1`, without `send`. -/
def space : Nat → Nat := fun _ => 1

def rights : Rights Nat := fun _ facet => facet != .send

/-- The empty selection is enabled at every store. -/
theorem enabled_nothing (store : Finset Nat) :
    Enabled (fun _ : Nat => ()) store ((⟨[], [], []⟩ : Selection Nat).commit (T := Unit)) :=
  ⟨by simp [Selection.commit], by simp [Selection.commit], by simp [Selection.commit],
    by simp [Selection.commit], by simp [Selection.commit]⟩

/-- The empty selection is formed under all rights. -/
theorem formed_nothing (Γ : Rights Nat) :
    FormedUnder space id Γ ((⟨[], [], []⟩ : Selection Nat).commit (T := Nat)) :=
  ⟨by simp [Selection.commit], by simp [Selection.commit], by simp [Selection.commit],
    by simp [Selection.commit]⟩

theorem relabel_admitted : P.Admits (s := start) (0, 3) :=
  ⟨Finset.mem_singleton_self 0, enabled_nothing _, ⟨PUnit.unit, (), Frames.models_nil _⟩,
    fun _ _ _ => show (Frames.ofSubstitution trivial).Models _ [] from Frames.models_nil _⟩

/-- **Relabelling without making spoils an absence, at a space without `send`**: the firing is
admitted and permitted, the absence of `3` at space `1` is entailed before and not after, and the
state's labels break the law. -/
theorem relabel_spoils_absence :
    Permitted P space rights (s := start) (0, 3) ∧ rights 1 .send = false ∧
      (Frames.ofSubstitution trivial).Entails (a := PUnit.unit) (P.knowledge start)
        (fun _ σ => AbsentAt P space (fun s => s.label) 1 (s := start) 3 (b := PUnit.unit) σ) ∧
      ¬ (Frames.ofSubstitution trivial).Entails (a := PUnit.unit) (P.knowledge (P.result (0, 3) relabel_admitted))
        (fun _ τ => AbsentAt P space (fun s => s.label) 1 (s := P.result (0, 3) relabel_admitted)
          ((Frames.ofSubstitution trivial).act (a := PUnit.unit) (b := PUnit.unit)
            (P.along (0, 3) relabel_admitted) 3) (b := PUnit.unit) τ) ∧
      ¬ LabelLaw P (fun s => s.label) := by
  refine ⟨formed_nothing rights, rfl, ?_, ?_, ?_⟩
  · intro _ σ _ o present _ same
    have one : o = 0 := Finset.mem_singleton.mp present
    subst one
    have wrong : (3 : Nat) = 1 := same
    exact absurd wrong (by decide)
  · intro entailed
    exact entailed PUnit.unit () (Frames.models_nil _) 0 (Finset.mem_singleton_self 0) rfl rfl
  · intro law
    have moved := law (s := start) (0, 3) relabel_admitted 0 List.not_mem_nil
    exact absurd (moved : 3 = 1) (by decide)

end Controls

#print axioms witness_present
#print axioms absence_preserved
#print axioms locatedLabels_law
#print axioms absent_iff_absentAt
#print axioms old_owned_witness_present
#print axioms old_owned_absence_preserved
#print axioms dependentLabels_law
#print axioms dependent_absence_preserved
#print axioms Controls.relabel_spoils_absence

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.PermissionsInterface
