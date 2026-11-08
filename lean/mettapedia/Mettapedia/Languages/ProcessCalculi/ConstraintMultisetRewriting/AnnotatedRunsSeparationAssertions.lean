import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRunsSeparation
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRunsLogicStored

/-!
# Assertions of separation logic over configurations

An assertion is a predicate of configurations (`Assertion`). Over the separation algebra of
`AnnotatedRunsSeparation`:

* `emp`: no occurrence and no knowledge;
* `pointsTo o t` (`o ↦ t`): exactly the occurrence `o`, which carries `t`, and no knowledge;
* `pureFact φ` (`⌜φ⌝`): a fact independent of the configuration, holding of `emp`;
* `knows ψ`: knowledge only, a store with a solution all of whose solutions satisfy `ψ`;
* `star P Q` (`P ∗ Q`): the configuration is, up to its class, the tensor of two separable parts,
  one in `P` and one in `Q`;
* `wand P Q` (`P −∗ Q`): every separable extension in `P` lands in `Q`.

## The laws of Boolean BI

`∗` is commutative and associative (`star_comm`, `star_assoc`, `star_assoc'`), with `emp` as its
unit on configurations whose store has a solution (`star_emp_iff`); `−∗` is its right adjoint
(`wand_adjoint`); `∗` is monotone and distributes over disjunction (`star_mono`, `star_or_iff`).
Assertions are all predicates, so the connectives of the Boolean algebra are the classical ones.

## Linear and duplicable assertions

* **Points-to is linear**: `o ↦ t ∗ o ↦ t'` holds nowhere (`pointsTo_star_self`).
* **Knowledge is duplicable**: `knows ψ ⊢ knows ψ ∗ knows ψ` (`knows_duplicable`), and on knowledge
  `∗` is conjunction (`star_knows_iff`).
* **Pure facts** pass through `∗` (`star_pureFact_iff`).
* **Intuitionistic readings**: `knows ψ ∗ ⊤` is "the store entails `ψ`" (`star_true_knows_iff`) and
  `o ↦ t ∗ ⊤` is "`o` is present and carries `t`" (`star_true_pointsTo_iff`). They are upward
  closed in the resource order.

## Persistent against Boolean (R28)

R28's logic over runs has two layers: R26's Boolean doctrine (sets of histories at each class) and
the persistent predicates of the copresheaf topos (sets of histories closed under extension by
runs). An assertion that respects classes, read where a history ends (`atEnd`), is a predicate of
the Boolean doctrine. Whether it is persistent is a question about time, not about space:

* **Knowledge is persistent** (`knowledge_persistent`): runs only add equations, so what the store
  entails is carried by every run (`entailedAt_path`).
* **Occupancy is not** (`presentAt_not_persistent`): a run that takes an occurrence present at its
  start breaks "the occurrence is present", although `o ↦ t ∗ ⊤` is upward closed in the resource
  order.

So the upward closure of intuitionistic BI (along frames) and R28's persistence (along runs) are
two different Kripke structures on the same classes; they agree on knowledge and part on
occurrences.
-/

set_option autoImplicit false

open CategoryTheory

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRuns

open MeTTaCalculus.OccurrenceCommits (regionOf mem_regionOf fire mem_fire)
open GuardFreeProcessOrders (SameUpTo)
open Mettapedia.GSLT.Causality.OccurrenceHistory (OccurrencePath)

universe uT uS uO

namespace SeparationRuns

variable {T : Type uT} {S : Type uS} {O : Type uO} [DecidableEq O]

/-- **Assertions**: predicates of configurations. -/
abbrev Assertion (T : Type uT) (O : Type uO) := Configuration T O → Prop

section Connectives

variable (A : SubstitutionAction T S) (label : O → T)

/-- An assertion that is a property of classes. -/
def Respects (P : Assertion T O) : Prop :=
  ∀ ⦃C D : Configuration T O⦄, SameUpTo A C D → P C → P D

/-- `emp`: no occurrence and no knowledge. -/
def emp : Assertion T O := fun C => C.present = ∅ ∧ A.Equivalent C.equations []

/-- `o ↦ t`: exactly the occurrence `o`, which carries `t`, and no knowledge. -/
def pointsTo (o : O) (t : T) : Assertion T O :=
  fun C => C.present = {o} ∧ label o = t ∧ A.Equivalent C.equations []

/-- `⌜φ⌝`: a fact independent of the configuration, holding of `emp`. -/
def pureFact (φ : Prop) : Assertion T O := fun C => φ ∧ emp A C

/-- `knows ψ`: knowledge only, with a solution, and every solution satisfies `ψ`. -/
def knows (ψ : S → Prop) : Assertion T O :=
  fun C => C.present = ∅ ∧ A.Consistent C.equations ∧ A.Entails C.equations ψ

/-- **Separating conjunction** `P ∗ Q`. -/
def star (P Q : Assertion T O) : Assertion T O :=
  fun C => ∃ C₁ C₂ : Configuration T O,
    Separable A C₁ C₂ ∧ SameUpTo A (tensor C₁ C₂) C ∧ P C₁ ∧ Q C₂

/-- **Magic wand** `P −∗ Q`. -/
def wand (P Q : Assertion T O) : Assertion T O :=
  fun C => ∀ D : Configuration T O, Separable A C D → P D → Q (tensor C D)

theorem star_respects (P Q : Assertion T O) : Respects A (star A P Q) := by
  rintro C D same ⟨C₁, C₂, sep, eq, hP, hQ⟩
  exact ⟨C₁, C₂, sep, eq.trans A same, hP, hQ⟩

omit [DecidableEq O] in
theorem emp_respects : Respects A (emp A : Assertion T O) := by
  rintro C D same ⟨present, none⟩
  exact ⟨same.2.symm.trans present, fun σ => (same.1 σ).symm.trans (none σ)⟩

omit [DecidableEq O] in
theorem pointsTo_respects (o : O) (t : T) : Respects A (pointsTo A label o t) := by
  rintro C D same ⟨present, labelled, none⟩
  exact ⟨same.2.symm.trans present, labelled, fun σ => (same.1 σ).symm.trans (none σ)⟩

omit [DecidableEq O] in
theorem knows_respects (ψ : S → Prop) : Respects A (knows A ψ : Assertion T O) := by
  rintro C D same ⟨present, consistent, entails⟩
  exact ⟨same.2.symm.trans present, (SubstitutionAction.equivalent_consistent A same.1).mp consistent,
    fun σ solved => entails σ ((same.1 σ).mpr solved)⟩

theorem wand_respects (P Q : Assertion T O) (respects : Respects A Q) : Respects A (wand A P Q) := by
  intro C D same wandC E sepDE hP
  have sepCE : Separable A C E :=
    (separable_congr A (sameUpTo_symm A same) (SameUpTo.refl A E)).mp sepDE
  exact respects (tensor_congr A same (SameUpTo.refl A E)) (wandC E sepCE hP)

end Connectives

/-! ## The laws of Boolean BI -/

section Laws

variable (A : SubstitutionAction T S) (label : O → T)

/-- **Commutativity of `∗`.** -/
theorem star_comm {P Q : Assertion T O} {C : Configuration T O} (holds : star A P Q C) :
    star A Q P C := by
  obtain ⟨C₁, C₂, sep, same, hP, hQ⟩ := holds
  exact ⟨C₂, C₁, (separable_comm A).mp sep, (tensor_comm A C₂ C₁).trans A same, hQ, hP⟩

/-- **Associativity of `∗`.** -/
theorem star_assoc {P Q R : Assertion T O} {C : Configuration T O}
    (holds : star A (star A P Q) R C) : star A P (star A Q R) C := by
  obtain ⟨C₁₂, C₃, sep₁₂₃, same, ⟨C₁, C₂, sep₁₂, same₁₂, hP, hQ⟩, hR⟩ := holds
  have sep' : Separable A (tensor C₁ C₂) C₃ :=
    (separable_congr A (sameUpTo_symm A same₁₂) (SameUpTo.refl A C₃)).mp sep₁₂₃
  obtain ⟨sep₂₃, sep₁₂₃'⟩ := (separable_assoc A).mp ⟨sep₁₂, sep'⟩
  refine ⟨C₁, tensor C₂ C₃, sep₁₂₃', ?_, hP, C₂, C₃, sep₂₃, SameUpTo.refl A _, hQ, hR⟩
  rw [← tensor_assoc]
  exact (tensor_congr A same₁₂ (SameUpTo.refl A C₃)).trans A same

/-- **Associativity of `∗`, the other way.** -/
theorem star_assoc' {P Q R : Assertion T O} {C : Configuration T O}
    (holds : star A P (star A Q R) C) : star A (star A P Q) R C :=
  star_comm A (star_assoc A (star_comm A (star_assoc A (star_comm A holds))))

/-- **`emp` is the unit of `∗`** on configurations whose store has a solution. -/
theorem star_emp_iff {P : Assertion T O} (respects : Respects A P) {C : Configuration T O} :
    star A P (emp A) C ↔ P C ∧ A.Consistent C.equations := by
  constructor
  · rintro ⟨C₁, C₂, sep, same, hP, ⟨present, none⟩⟩
    have toC₁ : SameUpTo A (tensor C₁ C₂) C₁ := by
      refine ⟨fun σ => ?_, ?_⟩
      · change A.Models σ (C₁.equations ++ C₂.equations) ↔ A.Models σ C₁.equations
        rw [A.models_append, none σ]
        simp
      · change C₁.present ∪ C₂.present = C₁.present
        rw [present, Finset.union_empty]
    exact ⟨respects ((sameUpTo_symm A toC₁).trans A same) hP,
      (SubstitutionAction.equivalent_consistent A same.1).mp sep.2⟩
  · rintro ⟨hP, consistent⟩
    refine ⟨C, unitConfiguration, (separable_unit_right A C).mpr consistent, ?_, hP, rfl,
      fun σ => Iff.rfl⟩
    rw [tensor_unit_right]
    exact SameUpTo.refl A C

/-- **The magic wand is right adjoint to `∗`.** -/
theorem wand_adjoint {P Q R : Assertion T O} (respects : Respects A R) :
    (∀ C, star A P Q C → R C) ↔ (∀ C, P C → wand A Q R C) := by
  constructor
  · intro entails C hP D sep hQ
    exact entails _ ⟨C, D, sep, SameUpTo.refl A _, hP, hQ⟩
  · rintro entails C ⟨C₁, C₂, sep, same, hP, hQ⟩
    exact respects same (entails C₁ hP C₂ sep hQ)

/-- `∗` is monotone. -/
theorem star_mono {P P' Q Q' : Assertion T O} (hP : ∀ C, P C → P' C) (hQ : ∀ C, Q C → Q' C)
    {C : Configuration T O} (holds : star A P Q C) : star A P' Q' C := by
  obtain ⟨C₁, C₂, sep, same, p, q⟩ := holds
  exact ⟨C₁, C₂, sep, same, hP C₁ p, hQ C₂ q⟩

/-- `∗` distributes over disjunction. -/
theorem star_or_iff {P P' Q : Assertion T O} {C : Configuration T O} :
    star A (fun D => P D ∨ P' D) Q C ↔ star A P Q C ∨ star A P' Q C := by
  constructor
  · rintro ⟨C₁, C₂, sep, same, p | p, q⟩
    · exact Or.inl ⟨C₁, C₂, sep, same, p, q⟩
    · exact Or.inr ⟨C₁, C₂, sep, same, p, q⟩
  · rintro (⟨C₁, C₂, sep, same, p, q⟩ | ⟨C₁, C₂, sep, same, p, q⟩)
    · exact ⟨C₁, C₂, sep, same, Or.inl p, q⟩
    · exact ⟨C₁, C₂, sep, same, Or.inr p, q⟩

/-- **Points-to is linear**: one occurrence cannot be owned twice. -/
theorem pointsTo_star_self (o : O) (t t' : T) (C : Configuration T O) :
    ¬ star A (pointsTo A label o t) (pointsTo A label o t') C := by
  rintro ⟨C₁, C₂, sep, -, ⟨p₁, -, -⟩, ⟨p₂, -, -⟩⟩
  exact not_separable_of_mem A (by rw [p₁]; exact Finset.mem_singleton_self o)
    (by rw [p₂]; exact Finset.mem_singleton_self o) sep

/-- **`o ↦ t ∗ ⊤`** holds exactly where `o` is present, carries `t`, and the store has a
solution. -/
theorem star_true_pointsTo_iff (o : O) (t : T) (C : Configuration T O) :
    star A (pointsTo A label o t) (fun _ => True) C ↔
      o ∈ C.present ∧ label o = t ∧ A.Consistent C.equations := by
  constructor
  · rintro ⟨C₁, C₂, sep, same, ⟨present, labelled, -⟩, -⟩
    refine ⟨?_, labelled, (SubstitutionAction.equivalent_consistent A same.1).mp sep.2⟩
    rw [← same.2]
    change o ∈ C₁.present ∪ C₂.present
    rw [present]
    exact Finset.mem_union_left _ (Finset.mem_singleton_self o)
  · rintro ⟨present, labelled, consistent⟩
    refine ⟨⟨[], {o}⟩, ⟨C.equations, C.present.erase o⟩, ⟨?_, ?_⟩, ⟨fun σ => ?_, ?_⟩,
      ⟨rfl, labelled, fun σ => Iff.rfl⟩, trivial⟩
    · exact Finset.disjoint_singleton_left.mpr (Finset.notMem_erase o C.present)
    · simpa using consistent
    · change A.Models σ ([] ++ C.equations) ↔ A.Models σ C.equations
      rw [List.nil_append]
    · change {o} ∪ C.present.erase o = C.present
      rw [← Finset.insert_eq, Finset.insert_erase present]

/-- **Knowledge is duplicable.** -/
theorem knows_duplicable {ψ : S → Prop} {C : Configuration T O} (holds : knows A ψ C) :
    star A (knows A ψ) (knows A ψ) C := by
  obtain ⟨present, consistent, entails⟩ := holds
  refine ⟨C, C, (separable_self_iff A C).mpr ⟨present, consistent⟩, ⟨fun σ => ?_, ?_⟩,
    ⟨present, consistent, entails⟩, ⟨present, consistent, entails⟩⟩
  · change A.Models σ (C.equations ++ C.equations) ↔ A.Models σ C.equations
    rw [A.models_append, and_self]
  · change C.present ∪ C.present = C.present
    exact Finset.union_self _

/-- **On knowledge, `∗` is conjunction.** -/
theorem star_knows_iff {ψ χ : S → Prop} {C : Configuration T O} :
    star A (knows A ψ) (knows A χ) C ↔ knows A (fun σ => ψ σ ∧ χ σ) C := by
  constructor
  · rintro ⟨C₁, C₂, sep, same, ⟨p₁, -, e₁⟩, ⟨p₂, -, e₂⟩⟩
    refine ⟨?_, (SubstitutionAction.equivalent_consistent A same.1).mp sep.2, fun σ solved => ?_⟩
    · rw [← same.2]
      change C₁.present ∪ C₂.present = ∅
      rw [p₁, p₂, Finset.union_empty]
    · have both := (A.models_append σ _ _).mp ((same.1 σ).mpr solved)
      exact ⟨e₁ σ both.1, e₂ σ both.2⟩
  · rintro ⟨present, consistent, entails⟩
    refine ⟨C, C, (separable_self_iff A C).mpr ⟨present, consistent⟩, ⟨fun σ => ?_, ?_⟩,
      ⟨present, consistent, fun σ solved => (entails σ solved).1⟩,
      ⟨present, consistent, fun σ solved => (entails σ solved).2⟩⟩
    · change A.Models σ (C.equations ++ C.equations) ↔ A.Models σ C.equations
      rw [A.models_append, and_self]
    · change C.present ∪ C.present = C.present
      exact Finset.union_self _

/-- **Intuitionistic knowledge**: `knows ψ ∗ ⊤` holds exactly where the store has a solution and
entails `ψ`. -/
theorem star_true_knows_iff {ψ : S → Prop} {C : Configuration T O} :
    star A (knows A ψ) (fun _ => True) C ↔ A.Consistent C.equations ∧ A.Entails C.equations ψ := by
  constructor
  · rintro ⟨C₁, C₂, sep, same, ⟨-, -, entails⟩, -⟩
    refine ⟨(SubstitutionAction.equivalent_consistent A same.1).mp sep.2, fun σ solved => ?_⟩
    exact entails σ ((A.models_append σ _ _).mp ((same.1 σ).mpr solved)).1
  · rintro ⟨consistent, entails⟩
    exact ⟨knowledge C.equations, spatial C.present, decompose_separable A consistent,
      decompose_sameUpTo A C, ⟨rfl, consistent, entails⟩, trivial⟩

/-- **Pure facts pass through `∗`.** -/
theorem star_pureFact_iff {φ : Prop} {P : Assertion T O} (respects : Respects A P)
    {C : Configuration T O} :
    star A (pureFact A φ) P C ↔ φ ∧ P C ∧ A.Consistent C.equations := by
  constructor
  · intro holds
    obtain ⟨hP, consistent⟩ := (star_emp_iff A respects).mp
      (star_comm A (star_mono A (P := pureFact A φ) (P' := emp A) (Q := P) (Q' := P)
        (fun _ h => h.2) (fun _ h => h) holds))
    obtain ⟨C₁, C₂, -, -, ⟨fact, -⟩, -⟩ := holds
    exact ⟨fact, hP, consistent⟩
  · rintro ⟨fact, hP, consistent⟩
    exact star_comm A (star_mono A (fun _ h => h) (fun _ h => ⟨fact, h⟩)
      ((star_emp_iff A respects).mpr ⟨hP, consistent⟩))

end Laws

/-! ## Persistent against Boolean -/

section Persistence

variable (A : SubstitutionAction T S) (label : O → T)

omit [DecidableEq O] in
/-- What the store entails, as a property of classes. -/
def EntailedAt (ψ : S → Prop) : ConfigurationClass A O → Prop :=
  Quotient.lift (s := sameSetoid A) (fun C : Configuration T O => A.Entails C.equations ψ)
    (fun _ _ (same : SameUpTo A _ _) => propext
      ⟨fun e σ s => e σ ((same.1 σ).mpr s), fun e σ s => e σ ((same.1 σ).mp s)⟩)

omit [DecidableEq O] in
/-- Where an occurrence is present, as a property of classes. -/
def PresentAt (o : O) : ConfigurationClass A O → Prop :=
  Quotient.lift (s := sameSetoid A) (fun C : Configuration T O => o ∈ C.present)
    (fun _ _ (same : SameUpTo A _ _) => congrArg (fun P : Finset O => o ∈ P) same.2)

/-- A firing keeps what the store entails. -/
theorem entails_result {ψ : S → Prop} (f : Firing T S O) {C : Configuration T O}
    (entailed : A.Entails C.equations ψ) : A.Entails (f.result label C).equations ψ := by
  intro σ solved
  rw [Firing.result_equations', A.models_append] at solved
  exact entailed σ solved.1

/-- **Knowledge grows along every run.** -/
theorem entailedAt_path (ψ : S → Prop) {x y : (theory A label).Term}
    (p : OccurrencePath (presentation A label) x y) : EntailedAt A ψ x → EntailedAt A ψ y := by
  induction p with
  | refl => exact id
  | cons o rest ih =>
      intro entailed
      obtain ⟨f, ⟨⟨-, fTarget⟩⟩⟩ := o
      subst fTarget
      apply ih
      have step : ∀ c : ConfigurationClass A O, EntailedAt A ψ c →
          EntailedAt A ψ (f.resultClass A label c) := by
        intro c
        refine Quotient.inductionOn c ?_
        intro C entailedC
        exact entails_result A label f entailedC
      exact step _ entailed

/-- **Knowledge is persistent** (R28): what the store entails, read where histories end, is a
persistent predicate of the run topos. -/
theorem knowledge_persistent (C₀ : Configuration T O) (ψ : S → Prop) :
    ∃ P : Persistent A label C₀, ∀ y, restrict P y = atEnd A label C₀ (EntailedAt A ψ) y :=
  (persistent_iff (atEnd A label C₀ (EntailedAt A ψ))).mpr
    fun _ _ p _ entailed => entailedAt_path A label ψ p entailed

/-- **Occupancy is not persistent**: when some run takes an occurrence present where it starts,
"the occurrence is present", read where histories end, is no persistent predicate. -/
theorem presentAt_not_persistent {C₀ : Configuration T O} {o : O} {w : List (Firing T S O)}
    (runs : Executable A label C₀ w) (present : o ∈ C₀.present)
    (gone : o ∉ (follow label C₀ w).present) :
    ¬ ∃ P : Persistent A label C₀, ∀ y, restrict P y = atEnd A label C₀ (PresentAt A o) y := by
  intro persistent
  have carried := (persistent_iff (atEnd A label C₀ (PresentAt A o))).mp persistent
  obtain ⟨p, -⟩ := exists_path A label C₀ w runs _ rfl
  exact gone (carried p (show 𝟙 (runObject A label C₀) ∈
    atEnd A label C₀ (PresentAt A o) (runObject A label C₀) from present))

end Persistence

end SeparationRuns

open SeparationRuns

#print axioms star_respects
#print axioms emp_respects
#print axioms pointsTo_respects
#print axioms knows_respects
#print axioms wand_respects
#print axioms star_comm
#print axioms star_assoc
#print axioms star_assoc'
#print axioms star_emp_iff
#print axioms wand_adjoint
#print axioms star_mono
#print axioms star_or_iff
#print axioms pointsTo_star_self
#print axioms star_true_pointsTo_iff
#print axioms knows_duplicable
#print axioms star_knows_iff
#print axioms star_true_knows_iff
#print axioms star_pureFact_iff
#print axioms entails_result
#print axioms entailedAt_path
#print axioms knowledge_persistent
#print axioms presentAt_not_persistent

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRuns
