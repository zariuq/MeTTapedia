import Mettapedia.Cybernetics.ObservedVariety
import Mathlib.Data.List.Perm.Basic

/-!
# Noninterference at a declared observation

Noninterference compares executions on low-equivalent inputs. The output
observer is explicit: public answer contents, existence, occurrence counts,
and the first answer expose different information. Delimited release permits
dependence on a named release function, rather than treating every annotation
as authority to reveal its input.

The finite language below is an executable example, with ordered choice,
public and secret conditionals, and `once`. Its evaluator enumerates a finite
ordered family of answers. It is not a semantics of concurrency, timing,
divergence, or the native MeTTa runtime.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.InformationFlow.ObservationalSecurity

open Mettapedia.Cybernetics

universe uInput uOutput uView uReleased

/-- Equal public inputs give equal observations of execution. The relation
may identify inputs differing in their secret state. -/
def Noninterference {Input : Type uInput} {Output : Type uOutput}
    {View : Type uView} (lowEquivalent : Input → Input → Prop)
    (observer : Observer Output View) (execute : Input → Output) : Prop :=
  ∀ left right, lowEquivalent left right →
    observer.observe (execute left) = observer.observe (execute right)

/-- Public execution can reveal the declared release value, but cannot
distinguish low-equivalent inputs with the same released information.
Authorization of the release function is a separate policy obligation. -/
def DelimitedRelease {Input : Type uInput} {Output : Type uOutput}
    {View : Type uView} {Released : Type uReleased}
    (lowEquivalent : Input → Input → Prop) (release : Input → Released)
    (observer : Observer Output View) (execute : Input → Output) : Prop :=
  ∀ left right, lowEquivalent left right → release left = release right →
    observer.observe (execute left) = observer.observe (execute right)

theorem noninterference_postcompose
    {Input : Type uInput} {Output : Type uOutput} {View : Type uView}
    {Summary : Type*} {lowEquivalent : Input → Input → Prop}
    {observer : Observer Output View} {execute : Input → Output}
    (secure : Noninterference lowEquivalent observer execute)
    (summarize : View → Summary) :
    Noninterference lowEquivalent (observer.postcompose summarize) execute := by
  intro left right related
  exact congrArg summarize (secure left right related)

theorem noninterference_delimitedRelease
    {Input : Type uInput} {Output : Type uOutput} {View : Type uView}
    {Released : Type uReleased} {lowEquivalent : Input → Input → Prop}
    {observer : Observer Output View} {execute : Input → Output}
    (secure : Noninterference lowEquivalent observer execute)
    (release : Input → Released) :
    DelimitedRelease lowEquivalent release observer execute := by
  intro left right related _
  exact secure left right related

namespace Observers

/-- The ordered answer family retains every occurrence. -/
def ordered (Value : Type*) : Observer (List Value) (List Value) :=
  Observer.identity (List Value)

/-- A bag forgets order and retains multiplicity. -/
def bag (Value : Type*) : Observer (List Value) (Multiset Value) where
  observe values := (values : Multiset Value)

/-- A support set forgets both order and multiplicity, but retains whether
each public value is possible. It can therefore reveal secret existence. -/
def support (Value : Type*) : Observer (List Value) (Set Value) where
  observe values := {value | value ∈ values}

/-- `none` remains distinguishable from every published answer. -/
def first (Value : Type*) : Observer (List Value) (Option Value) where
  observe := List.head?

end Observers

/-! ## Executable finite source language -/

structure Store where
  publicValue : Nat
  secret : Nat
deriving DecidableEq, Repr

def lowEquivalent (left right : Store) : Prop :=
  left.publicValue = right.publicValue

inductive FiniteProgram where
  | fail
  | emit (value : Nat)
  | readPublic
  | choice (left right : FiniteProgram)
  | ifPublicZero (yes no : FiniteProgram)
  | ifSecretZero (yes no : FiniteProgram)
  | once (body : FiniteProgram)
deriving Repr

namespace FiniteProgram

/-- Structural evaluation enumerates all finite alternatives in source
order; `once` retains only the first resulting occurrence. No laziness or
resource bound for the enumeration is asserted here. -/
def execute : FiniteProgram → Store → List Nat
  | .fail, _ => []
  | .emit value, _ => [value]
  | .readPublic, store => [store.publicValue]
  | .choice left right, store => execute left store ++ execute right store
  | .ifPublicZero yes no, store =>
      if store.publicValue = 0 then execute yes store else execute no store
  | .ifSecretZero yes no, store =>
      if store.secret = 0 then execute yes store else execute no store
  | .once body, store => (execute body store).take 1

/-- A syntactic sufficient condition. Secret conditionals are excluded;
public control, choice, and first-answer consumption remain available. -/
inductive PublicProgram : FiniteProgram → Prop where
  | fail : PublicProgram .fail
  | emit (value : Nat) : PublicProgram (.emit value)
  | readPublic : PublicProgram .readPublic
  | choice {left right : FiniteProgram} :
      PublicProgram left → PublicProgram right → PublicProgram (.choice left right)
  | ifPublicZero {yes no : FiniteProgram} :
      PublicProgram yes → PublicProgram no → PublicProgram (.ifPublicZero yes no)
  | once {body : FiniteProgram} : PublicProgram body → PublicProgram (.once body)

/-- A structural proof over actual source syntax establishes equality of
the complete ordered result, including empty results and duplicates. -/
theorem publicProgram_execution_eq {program : FiniteProgram}
    (publicOnly : PublicProgram program) (left right : Store)
    (related : lowEquivalent left right) : execute program left = execute program right := by
  induction publicOnly with
  | fail => rfl
  | emit => rfl
  | readPublic => exact congrArg (fun value => [value]) related
  | choice _ _ ihLeft ihRight => simp only [execute, ihLeft, ihRight]
  | ifPublicZero _ _ ihYes ihNo =>
      unfold lowEquivalent at related
      simp only [execute, related, ihYes, ihNo]
  | once _ ih => simp only [execute, ih]

theorem publicProgram_noninterference {program : FiniteProgram}
    (publicOnly : PublicProgram program) {View : Type*}
    (observer : Observer (List Nat) View) :
    Noninterference lowEquivalent observer program.execute := by
  intro left right related
  exact congrArg observer.observe (publicProgram_execution_eq publicOnly left right related)

end FiniteProgram

/-! ## Concrete observation boundaries -/

namespace Controls

open FiniteProgram

def zeroSecret : Store := ⟨0, 0⟩
def oneSecret : Store := ⟨0, 1⟩

/-- Both branches publish only the public literal zero; existence leaks. -/
def existenceProgram : FiniteProgram := .ifSecretZero (.emit 0) .fail

theorem support_can_leak_existence :
    ¬ Noninterference lowEquivalent (Observers.support Nat) existenceProgram.execute := by
  intro secure
  have same := secure zeroSecret oneSecret rfl
  have sameMembership := congrArg (fun values : Set Nat => 0 ∈ values) same
  simp [Observers.support, existenceProgram, execute, zeroSecret, oneSecret] at sameMembership

def multiplicityProgram : FiniteProgram :=
  .ifSecretZero (.choice (.emit 0) (.emit 0)) (.emit 0)

theorem multiplicityProgram_support_noninterference :
    Noninterference lowEquivalent (Observers.support Nat) multiplicityProgram.execute := by
  intro left right _
  apply Set.ext
  intro value
  by_cases leftZero : left.secret = 0 <;>
    by_cases rightZero : right.secret = 0 <;>
      simp [Observers.support, multiplicityProgram, execute, leftZero, rightZero]

theorem multiplicityProgram_bag_leaks :
    ¬ Noninterference lowEquivalent (Observers.bag Nat) multiplicityProgram.execute := by
  intro secure
  have same := secure zeroSecret oneSecret rfl
  have sameCount := congrArg Multiset.card same
  simp [Observers.bag, multiplicityProgram, execute, zeroSecret, oneSecret] at sameCount

/-- A deliberate release of parity permits a public computation using that
parity. It does not authorize revealing the entire secret. -/
def releaseParity (store : Store) : Nat := store.secret % 2

def parityComputation (store : Store) : Nat :=
  store.publicValue + 10 * (store.secret % 2)

theorem parityComputation_delimitedRelease :
    DelimitedRelease lowEquivalent releaseParity (Observer.identity Nat) parityComputation := by
  intro left right related released
  change left.publicValue + 10 * releaseParity left =
    right.publicValue + 10 * releaseParity right
  rw [related, released]

theorem parityComputation_not_noninterfering :
    ¬ Noninterference lowEquivalent (Observer.identity Nat) parityComputation := by
  intro secure
  have same := secure zeroSecret oneSecret rfl
  simp [Observer.identity, parityComputation, zeroSecret, oneSecret] at same

theorem parity_release_does_not_license_full_secret :
    ¬ DelimitedRelease lowEquivalent releaseParity (Observer.identity Nat) Store.secret := by
  intro secure
  have same := secure (⟨0, 0⟩ : Store) (⟨0, 2⟩ : Store) rfl (by decide)
  simp [Observer.identity] at same

end Controls

end Mettapedia.Logic.InformationFlow.ObservationalSecurity
