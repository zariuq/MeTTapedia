import Mettapedia.Machines.ShapeHeadRouting

/-!
# Exact membership may decide matching only with a complete certificate

A positive identity hit is sufficient when the query matches itself. A miss
needs a certificate covering every logical matching candidate, including facts
stored compactly. The executable whole-store summary below folds both physical
components. An empty ordinary row array alone supplies no such certificate.

The controls instantiate a one-column open fact: `none` is a fresh variable,
`some n` a ground atom. They separate identity membership from unifiability.
This is an admission law, not a verification of native metadata maintenance.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.MatchExistenceAdmission

open ShapeHeadRouting
variable {Head Fact : Type} [DecidableEq Fact]

def identityPresent (query : Fact) (state : State Head Fact) : Bool :=
  decide (query ∈ state.data.compact) || decide (query ∈ state.data.rows)

def existsMatch (accept : Fact → Bool) (state : State Head Fact) : Bool :=
  decide (0 < (observe state).countP (fun fact => accept fact = true))

omit [DecidableEq Fact] in
theorem existsMatch_iff (accept : Fact → Bool) (state : State Head Fact) :
    existsMatch accept state = true ↔ ∃ fact ∈ observe state, accept fact = true := by
  simp [existsMatch, Multiset.countP_pos]

def allExact (exact : Fact → Bool) (state : State Head Fact) : Bool :=
  decide (∀ fact ∈ state.data.compact, exact fact = true) &&
    decide (∀ fact ∈ state.data.rows, exact fact = true)

theorem identityPresent_iff (query : Fact) (state : State Head Fact) :
    identityPresent query state = true ↔ query ∈ observe state := by
  simp [identityPresent, observe, HybridShapeStore.denote]

omit [DecidableEq Fact] in
theorem allExact_iff (exact : Fact → Bool) (state : State Head Fact) :
    allExact exact state = true ↔ ∀ fact ∈ observe state, exact fact = true := by
  simp only [allExact, Bool.and_eq_true, decide_eq_true_eq,
    observe, HybridShapeStore.denote, Multiset.mem_add, Finset.mem_val]
  constructor
  · rintro ⟨compact, rows⟩ fact (kept | plain)
    · exact compact fact kept
    · exact rows fact plain
  · intro all
    exact ⟨fun fact member => all fact (Or.inl member),
      fun fact member => all fact (Or.inr member)⟩

def decideWithCertificate (query : Fact) (certified : Bool) (state : State Head Fact) : Option Bool :=
  if identityPresent query state then some true
  else if certified then some false else none

theorem certificate_sound (query : Fact) (accept : Fact → Bool) (state : State Head Fact)
    (self : accept query = true) (certified : Bool)
    (complete : certified = true → ∀ fact ∈ observe state, accept fact = true → fact = query)
    (answer : Bool) (returned : decideWithCertificate query certified state = some answer) :
    answer = existsMatch accept state := by
  by_cases present : identityPresent query state = true
  · have same : answer = true := by simpa [decideWithCertificate, present] using returned.symm
    subst answer
    symm
    apply (existsMatch_iff accept state).mpr
    exact ⟨query, (identityPresent_iff query state).mp present, self⟩
  · have absent : query ∉ observe state := by simpa [identityPresent_iff] using present
    cases certified with
    | false => simp [decideWithCertificate, present] at returned
    | true =>
        have same : answer = false := by simpa [decideWithCertificate, present] using returned.symm
        subst answer
        have noMatch : ¬ ∃ fact ∈ observe state, accept fact = true := by
          rintro ⟨fact, member, matched⟩
          have same := complete rfl fact member matched
          subst fact
          exact absent member
        simp [existsMatch, Multiset.countP_pos, noMatch]

theorem complete_summary_sound (query : Fact) (accept exact : Fact → Bool) (state : State Head Fact)
    (self : accept query = true)
    (classifier : ∀ fact, exact fact = true → accept fact = true → fact = query)
    (answer : Bool) (returned : decideWithCertificate query (allExact exact state) state = some answer) :
    answer = existsMatch accept state := by
  apply certificate_sound query accept state self (allExact exact state) _ answer returned
  intro complete fact member matched
  exact classifier fact ((allExact_iff exact state).mp complete fact member) matched

omit [DecidableEq Fact] in
theorem summary_representation_independent (exact : Fact → Bool) (left right : State Head Fact)
    (same : observe left = observe right) : allExact exact left = allExact exact right := by
  apply Bool.eq_iff_iff.mpr
  rw [allExact_iff, allExact_iff, same]

namespace Controls

def acceptsAtom (query : Nat) : Option Nat → Bool
  | none => true
  | some value => value == query

def compactVariable : State Unit (Option Nat) := ⟨fun _ => true, ⟨{none}, 0⟩⟩

theorem row_only_summary_certifies_a_false_absence :
    decideWithCertificate (some 2)
        (decide (∀ fact ∈ compactVariable.data.rows, Option.isSome fact = true)) compactVariable = some false ∧
      existsMatch (acceptsAtom 2) compactVariable = true := by decide

theorem complete_summary_declines_the_open_miss :
    decideWithCertificate (some 2) (allExact Option.isSome compactVariable) compactVariable = none := by decide

theorem a_positive_hit_needs_no_global_groundness :
    let mixed : State Unit (Option Nat) := ⟨fun _ => true, ⟨{none, some 2}, 0⟩⟩
    allExact Option.isSome mixed = false ∧
      decideWithCertificate (some 2) false mixed = some true := by decide

theorem ground_classifier_is_sound (query : Nat) :
    ∀ fact, Option.isSome fact = true → acceptsAtom query fact = true → fact = some query := by
  intro fact exact matched
  cases fact with
  | none => simp at exact
  | some value => simpa [acceptsAtom] using matched

theorem missing_compact_summary_changes_the_effect :
    let faulty := if decideWithCertificate (some 2) true compactVariable = some false then
        some 2 ::ₘ observe compactVariable else observe compactVariable
    let ordinary := if existsMatch (acceptsAtom 2) compactVariable then observe compactVariable else
        some 2 ::ₘ observe compactVariable
    faulty.card = 2 ∧ ordinary.card = 1 := by decide

end Controls
end Mettapedia.Machines.MatchExistenceAdmission
