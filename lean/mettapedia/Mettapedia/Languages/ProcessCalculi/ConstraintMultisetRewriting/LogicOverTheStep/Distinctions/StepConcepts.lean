import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.Distinctions.ObserverConcepts
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.InfinitaryAdequacy

/-!
# The types of the logic over the step

The formulas of Hennessy–Milner logic are an observer family: each formula reads its truth
(`formulas`, `iformulas`). Their indistinguishability is logical equivalence, finitary or
infinitary (`indist_formulas_iff`, `indist_iformulas_iff`), so by `ObserverConcepts` their concepts
are the classes closed under logical equivalence.

* **Every formula denotes a concept** (`isConcept_sat`), with no hypothesis, and **every concept is
  closed under bisimilarity** (`bisimClosed_of_isConcept`).
* **Where the formulas and bisimilarity part** (`bisimClosed_isConcept_iff`): every class closed
  under bisimilarity is a concept of the finitary formulas exactly when logically equivalent states
  are bisimilar. So under Hennessy–Milner adequacy the concepts are exactly the classes closed under
  bisimilarity (`isConcept_formulas_iff_bisimClosed`); on the first-order step this holds under every
  finite program, for observations invariant under renaming, with fresh identities for every label
  (`program_isConcept_iff_bisimClosed`, from `ProgramAdequacy.program_adequacy`).
* **The infinitary concepts are the classes closed under bisimilarity on every system**
  (`isConcept_iformulas_iff`), and **each is denoted by an infinitary formula**
  (`exists_iformula_of_bisimClosed`): the disjunction, over the class, of characteristic formulas,
  each the conjunction, over the states not bisimilar to its centre, of a separating formula
  (`characteristic`, `isat_characteristic`). The only hypothesis is the one `IFormula` carries:
  conjunctions indexed by types as large as the type of states; the separating formulas are chosen.
* **Denotation by one finitary formula** (`denoted_iff_finitelyDetermined`): a class is the
  extension of one finitary formula exactly when finitely many formulas decide it
  (`ObserverConcepts.BooleanTests.denoted_iff_finitelyDetermined`).

Control on the tree's counterexample to finitary adequacy (`ImageFinitenessNecessary`): having an
infinite run is closed under bisimilarity and denoted by an infinitary formula, and it is not a
concept of the finitary formulas (`endless_control`). A concrete program on the step with a concept
no finitary formula denotes is in `ParityBoundary`.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.Distinctions.StepConcepts

open Set
open Mettapedia.Cybernetics.DistinctionCalculus.Exclusion
open Mettapedia.GSLT Mettapedia.GSLT.HennessyMilner
open ObserverConcepts InfinitaryAdequacy

universe u uAtom uLabel uT uS uO

section Systems

variable {S : GSLT.{u}} (M : System.{uAtom, uLabel} S)

/-- **The finitary formulas as observers**: each reads its truth. -/
def formulas : Formula M.Atom M.Label → S.Term → Prop := fun φ t => M.sat φ t

/-- **The infinitary formulas as observers.** -/
def iformulas : IFormula.{u, uAtom, uLabel} M.Atom M.Label → S.Term → Prop := fun φ t => isat M φ t

/-- A class closed under bisimilarity. -/
def BisimClosed (A : Set S.Term) : Prop := ∀ x ∈ A, ∀ y, M.Bisimilar x y → y ∈ A

theorem indist_formulas_iff (x y : S.Term) :
    Indist (formulas M) x y ↔ M.LogicallyEquivalent x y :=
  ⟨fun same φ => Iff.of_eq (same φ), fun equivalent φ => propext (equivalent φ)⟩

theorem indist_iformulas_iff (x y : S.Term) : Indist (iformulas M) x y ↔ M.Bisimilar x y := by
  rw [← iequivalent_iff_bisimilar M x y]
  exact ⟨fun same φ => Iff.of_eq (same φ), fun equivalent φ => propext (equivalent φ)⟩

/-- The concepts of the finitary formulas are the classes closed under logical equivalence. -/
theorem isConcept_formulas_iff (A : Set S.Term) :
    IsConcept (Apart (formulas M)) A ↔ ∀ x ∈ A, ∀ y, M.LogicallyEquivalent x y → y ∈ A := by
  rw [isConcept_iff_saturated]
  simp only [indist_formulas_iff]

/-- **Every formula denotes a concept.** -/
theorem isConcept_sat (φ : Formula M.Atom M.Label) : IsConcept (Apart (formulas M)) {t | M.sat φ t} :=
  isConcept_preimage (read := formulas M) φ {p | p}

/-- **Every concept of the formulas is closed under bisimilarity.** -/
theorem bisimClosed_of_isConcept {A : Set S.Term} (concept : IsConcept (Apart (formulas M)) A) :
    BisimClosed M A :=
  fun x inA y bisimilar =>
    (isConcept_formulas_iff M A).mp concept x inA y (M.logicallyEquivalent_of_bisimilar bisimilar)

/-- A bisimilarity class is closed under bisimilarity. -/
theorem bisimClosed_class (x : S.Term) : BisimClosed M {y | M.Bisimilar x y} :=
  fun _ first _ second => M.bisimilar_trans first second

/-- **Where the formulas and bisimilarity part**: every class closed under bisimilarity is a concept
of the finitary formulas exactly when logical equivalence implies bisimilarity. -/
theorem bisimClosed_isConcept_iff :
    (∀ A, BisimClosed M A → IsConcept (Apart (formulas M)) A) ↔
      ∀ x y, M.LogicallyEquivalent x y → M.Bisimilar x y := by
  constructor
  · intro concepts x y equivalent
    exact (isConcept_formulas_iff M _).mp (concepts _ (bisimClosed_class M x)) x
      (M.bisimilar_refl x) y equivalent
  · intro adequate A closed
    exact (isConcept_formulas_iff M A).mpr fun x inA y equivalent =>
      closed x inA y (adequate x y equivalent)

/-- **Under adequacy the types of the formulas are the classes closed under bisimilarity.** -/
theorem isConcept_formulas_iff_bisimClosed
    (adequate : ∀ x y, M.LogicallyEquivalent x y ↔ M.Bisimilar x y) (A : Set S.Term) :
    IsConcept (Apart (formulas M)) A ↔ BisimClosed M A :=
  ⟨bisimClosed_of_isConcept M,
    (bisimClosed_isConcept_iff M).mpr (fun x y equivalent => (adequate x y).mp equivalent) A⟩

/-- **The infinitary concepts are the classes closed under bisimilarity**, on every system. -/
theorem isConcept_iformulas_iff (A : Set S.Term) :
    IsConcept (Apart (iformulas M)) A ↔ BisimClosed M A := by
  rw [isConcept_iff_saturated]
  simp only [indist_iformulas_iff]
  rfl

/-! ## Every infinitary concept is denoted -/

theorem exists_separating_of_not_bisimilar {x y : S.Term} (apart : ¬ M.Bisimilar x y) :
    ∃ φ : IFormula.{u, uAtom, uLabel} M.Atom M.Label, isat M φ x ∧ ¬ isat M φ y :=
  exists_separating M fun equivalent => apart ((iequivalent_iff_bisimilar M x y).mp equivalent)

/-- **The characteristic formula of a state**: the conjunction, over the states not bisimilar to
it, of a formula separating it from each. -/
noncomputable def characteristic (x : S.Term) : IFormula.{u, uAtom, uLabel} M.Atom M.Label :=
  IFormula.conj (Index := {y : S.Term // ¬ M.Bisimilar x y})
    fun y => Classical.choose (exists_separating_of_not_bisimilar M y.2)

/-- **A characteristic formula denotes a bisimilarity class.** -/
theorem isat_characteristic (x z : S.Term) : isat M (characteristic M x) z ↔ M.Bisimilar x z := by
  constructor
  · intro holds
    by_contra apart
    have all : ∀ y : {y : S.Term // ¬ M.Bisimilar x y},
        isat M (Classical.choose (exists_separating_of_not_bisimilar M y.2)) z := holds
    exact (Classical.choose_spec (exists_separating_of_not_bisimilar M apart)).2 (all ⟨z, apart⟩)
  · rintro ⟨R, bisimulation, related⟩
    show ∀ y : {y : S.Term // ¬ M.Bisimilar x y},
      isat M (Classical.choose (exists_separating_of_not_bisimilar M y.2)) z
    intro y
    exact (isat_iff_of_isBisimulation M bisimulation _ related).mp
      (Classical.choose_spec (exists_separating_of_not_bisimilar M y.2)).1

/-- **Every class closed under bisimilarity is denoted by an infinitary formula.** -/
theorem exists_iformula_of_bisimClosed {A : Set S.Term} (closed : BisimClosed M A) :
    ∃ φ : IFormula.{u, uAtom, uLabel} M.Atom M.Label, ∀ t, isat M φ t ↔ t ∈ A := by
  refine ⟨.neg (.conj (Index := A) fun x => .neg (characteristic M x.1)), fun t => ?_⟩
  show (¬ ∀ x : A, ¬ isat M (characteristic M x.1) t) ↔ t ∈ A
  constructor
  · intro notAll
    by_contra outside
    exact notAll fun x holds => outside (closed x.1 x.2 t ((isat_characteristic M x.1 t).mp holds))
  · intro inside all
    exact all ⟨t, inside⟩ ((isat_characteristic M t t).mpr (M.bisimilar_refl t))

/-- **Every infinitary concept is denoted by an infinitary formula.** -/
theorem iconcept_denoted {A : Set S.Term} (concept : IsConcept (Apart (iformulas M)) A) :
    ∃ φ : IFormula.{u, uAtom, uLabel} M.Atom M.Label, ∀ t, isat M φ t ↔ t ∈ A :=
  exists_iformula_of_bisimClosed M ((isConcept_iformulas_iff M A).mp concept)

/-! ## Denotation by one finitary formula -/

/-- The finitary formulas are closed under truth, negation and conjunction. -/
def tests : BooleanTests S.Term where
  Test := Formula M.Atom M.Label
  holds := M.sat
  top := .top
  neg := .neg
  conj := .conj
  holds_top _ := trivial
  holds_neg _ _ := Iff.rfl
  holds_conj _ _ _ := Iff.rfl

/-- **A class is the extension of one finitary formula exactly when finitely many formulas decide
it.** -/
theorem denoted_iff_finitelyDetermined (A : Set S.Term) :
    (∃ φ : Formula M.Atom M.Label, ∀ t, M.sat φ t ↔ t ∈ A) ↔
      ∃ F : List (Formula M.Atom M.Label),
        ∀ x ∈ A, ∀ y, (∀ φ ∈ F, M.sat φ x ↔ M.sat φ y) → y ∈ A :=
  (tests M).denoted_iff_finitelyDetermined A

end Systems

/-! ## On the first-order step under a finite program -/

section Program

open ProgramAdequacy StepSpan

variable {T : Type uT} {S : Type uS} {O : Type uO} [DecidableEq O]
  (A : SubstitutionAction T S) (label : O → T)

/-- **On the first-order step under every finite program, the types of the formulas are exactly
the classes closed under bisimilarity**, for observations invariant under renaming, with fresh
identities for every label. -/
theorem program_isConcept_iff_bisimClosed (supply : Supply label) {R : Set (RuleInstance T)}
    (finite : R.Finite) {Atom : Type} (observes : Atom → Configuration T O → Prop)
    (invariant : ∀ (a : Atom) (π : Equiv.Perm O) (C : Configuration T O), Keeps label π →
      (observes a (renameConf π C) ↔ observes a C))
    (X : Set (Configuration T O)) :
    IsConcept (Apart (formulas (stepSystem (program A label R) observes))) X ↔
      BisimClosed (stepSystem (program A label R) observes) X :=
  isConcept_formulas_iff_bisimClosed (stepSystem (program A label R) observes)
    (program_adequacy A label supply finite observes invariant) X

/-- Under the same hypotheses, every type of the finitary formulas is denoted by an infinitary
formula. -/
theorem program_isConcept_denoted (supply : Supply label) {R : Set (RuleInstance T)}
    (finite : R.Finite) {Atom : Type} (observes : Atom → Configuration T O → Prop)
    (invariant : ∀ (a : Atom) (π : Equiv.Perm O) (C : Configuration T O), Keeps label π →
      (observes a (renameConf π C) ↔ observes a C))
    {X : Set (Configuration T O)}
    (concept : IsConcept (Apart (formulas (stepSystem (program A label R) observes))) X) :
    ∃ φ : IFormula (stepSystem (program A label R) observes).Atom
        (stepSystem (program A label R) observes).Label,
      ∀ C, isat (stepSystem (program A label R) observes) φ C ↔ C ∈ X :=
  exists_iformula_of_bisimClosed _
    ((program_isConcept_iff_bisimClosed A label supply finite observes invariant X).mp concept)

end Program

/-! ## Control: the tree's counterexample to finitary adequacy -/

section Control

open ImageFinitenessNecessary

/-- Having an infinite run is closed under bisimilarity. -/
theorem endless_bisimClosed : BisimClosed hm {t | Endless hm () t} := by
  rintro x endless y ⟨R, bisimulation, related⟩
  exact endless_of_isBisimulation hm bisimulation () related endless

/-- **Control: a class closed under bisimilarity that no finitary formula can see.** Having an
infinite run is denoted by an infinitary formula, and it is not a concept of the finitary formulas:
the two states of the counterexample are logically equivalent, one has an infinite run and the
other does not. -/
theorem endless_control :
    BisimClosed hm {t | Endless hm () t} ∧
      (∃ φ : IFormula.{0, 0, 0} hm.Atom hm.Label, ∀ t, isat hm φ t ↔ t ∈ {t | Endless hm () t}) ∧
      ¬ IsConcept (Apart (formulas hm)) {t | Endless hm () t} := by
  refine ⟨endless_bisimClosed, exists_iformula_of_bisimClosed hm endless_bisimClosed, ?_⟩
  intro concept
  exact not_endless_left ((isConcept_formulas_iff hm _).mp concept St.right endless_right St.left
    (hm.logicallyEquivalent_symm logically_equivalent))

/-- **The finitary converse fails on this system.** -/
theorem finitary_converse_fails :
    ¬ ∀ A, BisimClosed hm A → IsConcept (Apart (formulas hm)) A :=
  fun concepts => endless_control.2.2 (concepts _ endless_bisimClosed)

end Control

#print axioms indist_formulas_iff
#print axioms indist_iformulas_iff
#print axioms isConcept_sat
#print axioms bisimClosed_of_isConcept
#print axioms bisimClosed_isConcept_iff
#print axioms isConcept_formulas_iff_bisimClosed
#print axioms isConcept_iformulas_iff
#print axioms isat_characteristic
#print axioms exists_iformula_of_bisimClosed
#print axioms iconcept_denoted
#print axioms denoted_iff_finitelyDetermined
#print axioms program_isConcept_iff_bisimClosed
#print axioms program_isConcept_denoted
#print axioms endless_control
#print axioms finitary_converse_fails

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.Distinctions.StepConcepts
