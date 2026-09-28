import Mettapedia.Logic.InformationFlow.ObservationalSecurity

/-!
# Security under refinement and finite scheduling

Preserving the declared public observation preserves noninterference. Merely
removing possible behaviors does not: a secret-dependent selector can resolve
a publicly nondeterministic program in different ways on low-equivalent inputs.
Likewise, occurrence permutations preserve bag observations, but can reveal a
secret through a first-answer observer.

The composition theorem for delimited release retains both stage observations
and both declared releases. It does not grant authority to release a new value.
The finite source controls use `FiniteProgram.execute`; no result here asserts
that arbitrary graph schedulers preserve timing, fairness, divergence, or
unmodeled effects.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.InformationFlow.Refinement

open Mettapedia.Cybernetics ObservationalSecurity

universe uInput uSource uTarget uView

/-- Pointwise equality at the declared public observation transfers a
two-execution security property across independently given implementations. -/
theorem noninterference_of_observation_eq
    {Input : Type uInput} {Source : Type uSource} {Target : Type uTarget}
    {View : Type uView} {lowEquivalent : Input → Input → Prop}
    {sourceObserver : Observer Source View} {targetObserver : Observer Target View}
    {source : Input → Source} {target : Input → Target}
    (secure : Noninterference lowEquivalent sourceObserver source)
    (preserves : ∀ input, targetObserver.observe (target input) =
      sourceObserver.observe (source input)) :
    Noninterference lowEquivalent targetObserver target := by
  intro left right related
  rw [preserves left, preserves right]
  exact secure left right related

theorem delimitedRelease_of_observation_eq
    {Input : Type uInput} {Source : Type uSource} {Target : Type uTarget}
    {View Released : Type*} {lowEquivalent : Input → Input → Prop}
    {release : Input → Released}
    {sourceObserver : Observer Source View} {targetObserver : Observer Target View}
    {source : Input → Source} {target : Input → Target}
    (secure : DelimitedRelease lowEquivalent release sourceObserver source)
    (preserves : ∀ input, targetObserver.observe (target input) =
      sourceObserver.observe (source input)) :
    DelimitedRelease lowEquivalent release targetObserver target := by
  intro left right related sameRelease
  rw [preserves left, preserves right]
  exact secure left right related sameRelease

/-! ## Sequential delimited release -/

/-- The transcript exposes the public observations from both stages. -/
def transcriptObserver {Middle Output MidView OutView : Type*}
    (middleObserver : Observer Middle MidView) (outputObserver : Observer Output OutView) :
    Observer (Middle × Output) (MidView × OutView) where
  observe result := (middleObserver.observe result.1, outputObserver.observe result.2)

/-- Retain the intermediate state as well as the final result so the public
transcript cannot silently forget the first stage's disclosure. -/
def executeStages {Input Middle Output : Type*}
    (first : Input → Middle) (second : Middle → Output) (input : Input) : Middle × Output :=
  let middle := first input
  (middle, second middle)

/-- Two local release contracts compose. The second stage receives a state
whose public view is protected by the first contract. The combined policy
records its release at that actual intermediate state, and the theorem
preserves both public observations, not only the final result. -/
theorem delimitedRelease_sequential
    {Input Middle Output MidView OutView ReleaseOne ReleaseTwo : Type*}
    {lowEquivalent : Input → Input → Prop}
    {releaseOne : Input → ReleaseOne} {releaseTwo : Middle → ReleaseTwo}
    {middleObserver : Observer Middle MidView} {outputObserver : Observer Output OutView}
    {first : Input → Middle} {second : Middle → Output}
    (firstSecure : DelimitedRelease lowEquivalent releaseOne middleObserver first)
    (secondSecure : DelimitedRelease
      (fun left right => middleObserver.observe left = middleObserver.observe right)
      releaseTwo outputObserver second) :
    DelimitedRelease lowEquivalent
      (fun input => (releaseOne input, releaseTwo (first input)))
      (transcriptObserver middleObserver outputObserver) (executeStages first second) := by
  intro left right related releases
  have firstRelease := congrArg Prod.fst releases
  have secondRelease := congrArg Prod.snd releases
  have middleEqual := firstSecure left right related firstRelease
  have outputEqual := secondSecure (first left) (first right) middleEqual secondRelease
  exact Prod.ext middleEqual outputEqual

/-! ## Possibilistic refinement and observer-specific scheduling -/

/-- Ordinary behavior inclusion: every refined answer is a possible source
answer. This does not relate choices made on different secret inputs. -/
def PossibilisticRefinement {Input Value : Type*}
    (refined source : Input → List Value) : Prop :=
  ∀ input value, value ∈ refined input → value ∈ source input

theorem possibilisticRefinement_trans {Input Value : Type*}
    {first second third : Input → List Value}
    (firstSecond : PossibilisticRefinement first second)
    (secondThird : PossibilisticRefinement second third) :
    PossibilisticRefinement first third := by
  intro input value present
  exact secondThird input value (firstSecond input value present)

theorem once_possibilisticRefinement {Input Value : Type*} (source : Input → List Value) :
    PossibilisticRefinement (fun input => (source input).take 1) source := by
  intro input value present
  exact List.mem_of_mem_take present

/-- A possibly input-dependent permutation preserves the occurrence bag.
This is enough for bag noninterference, regardless of how the permutation
was proposed. It says nothing about a first-answer or timing observation. -/
theorem bag_noninterference_of_permutation
    {Input Value : Type*} {lowEquivalent : Input → Input → Prop}
    {source target : Input → List Value}
    (secure : Noninterference lowEquivalent (Observers.bag Value) source)
    (permutation : ∀ input, (target input).Perm (source input)) :
    Noninterference lowEquivalent (Observers.bag Value) target := by
  apply noninterference_of_observation_eq secure
  intro input
  exact Quot.sound (permutation input)

theorem support_noninterference_of_permutation
    {Input Value : Type*} {lowEquivalent : Input → Input → Prop}
    {source target : Input → List Value}
    (secure : Noninterference lowEquivalent (Observers.support Value) source)
    (permutation : ∀ input, (target input).Perm (source input)) :
    Noninterference lowEquivalent (Observers.support Value) target := by
  apply noninterference_of_observation_eq secure
  intro input
  apply Set.ext
  intro value
  exact (permutation input).mem_iff

namespace Controls

open FiniteProgram
open ObservationalSecurity.Controls (zeroSecret oneSecret)

/-- Public nondeterminism, with no access to the secret. -/
def publicChoice : FiniteProgram := .choice (.emit 0) (.emit 1)

/-- The refinement selects a different public answer using the secret. -/
def secretSelection : FiniteProgram := .ifSecretZero (.emit 0) (.emit 1)

theorem publicChoice_noninterference {View : Type*}
    (observer : Observer (List Nat) View) :
    Noninterference lowEquivalent observer publicChoice.execute :=
  publicProgram_noninterference (.choice (.emit 0) (.emit 1)) observer

theorem secretSelection_refines_publicChoice :
    PossibilisticRefinement secretSelection.execute publicChoice.execute := by
  intro store value present
  by_cases secretZero : store.secret = 0 <;>
    simp [secretSelection, publicChoice, execute, secretZero] at present ⊢ <;>
    simp [present]

theorem secretSelection_is_deterministic (store : Store) :
    (secretSelection.execute store).length = 1 := by
  by_cases secretZero : store.secret = 0 <;>
    simp [secretSelection, execute, secretZero]

theorem secretSelection_leaks :
    ¬ Noninterference lowEquivalent (Observers.support Nat) secretSelection.execute := by
  intro secure
  have same := secure zeroSecret oneSecret rfl
  have sameMembership := congrArg (fun values : Set Nat => 0 ∈ values) same
  simp [Observers.support, secretSelection, execute, zeroSecret, oneSecret] at sameMembership

/-- A scheduler may inspect the secret and still preserve every answer and
its multiplicity. The ordering decision itself can remain observable. -/
def secretSchedule (store : Store) (answers : List Nat) : List Nat :=
  if store.secret = 0 then answers else answers.reverse

theorem secretSchedule_permutation (store : Store) (answers : List Nat) :
    (secretSchedule store answers).Perm answers := by
  by_cases secretZero : store.secret = 0
  · simp [secretSchedule, secretZero]
  · simp [secretSchedule, secretZero]

theorem secretSchedule_bag_noninterference :
    Noninterference lowEquivalent (Observers.bag Nat)
      (fun store => secretSchedule store (publicChoice.execute store)) :=
  bag_noninterference_of_permutation (publicChoice_noninterference _)
    (fun store => secretSchedule_permutation store _)

theorem secretSchedule_first_leaks :
    ¬ Noninterference lowEquivalent (Observers.first Nat)
      (fun store => secretSchedule store (publicChoice.execute store)) := by
  intro secure
  have same := secure zeroSecret oneSecret rfl
  simp [Observers.first, secretSchedule, publicChoice, execute, zeroSecret, oneSecret] at same

/-- This source program has equal answer sets and bags on every secret,
but its authored order depends on that secret. -/
def secretOrdering : FiniteProgram :=
  .ifSecretZero (.choice (.emit 0) (.emit 1)) (.choice (.emit 1) (.emit 0))

theorem secretOrdering_eq_schedule (store : Store) :
    secretOrdering.execute store = secretSchedule store (publicChoice.execute store) := by
  by_cases secretZero : store.secret = 0 <;>
    simp [secretOrdering, secretSchedule, publicChoice, execute, secretZero]

theorem secretOrdering_support_noninterference :
    Noninterference lowEquivalent (Observers.support Nat) secretOrdering.execute := by
  apply support_noninterference_of_permutation (publicChoice_noninterference _)
  intro store
  rw [secretOrdering_eq_schedule]
  exact secretSchedule_permutation store _

theorem once_secretOrdering_leaks :
    ¬ Noninterference lowEquivalent (Observers.support Nat)
      (FiniteProgram.once secretOrdering).execute := by
  intro secure
  have same := secure zeroSecret oneSecret rfl
  have sameMembership := congrArg (fun values : Set Nat => 0 ∈ values) same
  simp [Observers.support, secretOrdering, execute, zeroSecret, oneSecret] at sameMembership

/-- The executable counterexample packages the refinement paradox: source
possibilistic noninterference, behavior inclusion, and target leakage. -/
theorem possibilistic_noninterference_not_refinement_closed :
    Noninterference lowEquivalent (Observers.support Nat) publicChoice.execute ∧
      PossibilisticRefinement secretSelection.execute publicChoice.execute ∧
      ¬ Noninterference lowEquivalent (Observers.support Nat) secretSelection.execute :=
  ⟨publicChoice_noninterference _, secretSelection_refines_publicChoice, secretSelection_leaks⟩

/-! A concrete composition exposes two declared low bits in successive
stages, while keeping the remaining high bits outside the public transcript. -/

def publicStoreObserver : Observer Store Nat where
  observe := Store.publicValue

def discloseLowBit (store : Store) : Store :=
  { publicValue := store.publicValue + 10 * (store.secret % 2)
    secret := store.secret / 2 }

theorem discloseLowBit_delimitedRelease :
    DelimitedRelease lowEquivalent ObservationalSecurity.Controls.releaseParity
      publicStoreObserver discloseLowBit := by
  intro left right related released
  change left.publicValue + 10 * ObservationalSecurity.Controls.releaseParity left =
    right.publicValue + 10 * ObservationalSecurity.Controls.releaseParity right
  rw [related, released]

theorem twoStage_delimitedRelease :
    DelimitedRelease lowEquivalent
      (fun store =>
        (ObservationalSecurity.Controls.releaseParity store,
          ObservationalSecurity.Controls.releaseParity (discloseLowBit store)))
      (transcriptObserver publicStoreObserver (Observer.identity Nat))
      (executeStages discloseLowBit ObservationalSecurity.Controls.parityComputation) :=
  delimitedRelease_sequential discloseLowBit_delimitedRelease
    ObservationalSecurity.Controls.parityComputation_delimitedRelease

/-- The transcript retains the first disclosure even though both examples
have the same first bit. Higher bits not in the policy remain unobserved. -/
theorem twoStage_concrete_transcripts :
    (transcriptObserver publicStoreObserver (Observer.identity Nat)).observe
      (executeStages discloseLowBit ObservationalSecurity.Controls.parityComputation
        (⟨3, 5⟩ : Store)) = (13, 13) ∧
    (transcriptObserver publicStoreObserver (Observer.identity Nat)).observe
      (executeStages discloseLowBit ObservationalSecurity.Controls.parityComputation
        (⟨3, 7⟩ : Store)) = (13, 23) := by
  decide

end Controls

end Mettapedia.Logic.InformationFlow.Refinement
