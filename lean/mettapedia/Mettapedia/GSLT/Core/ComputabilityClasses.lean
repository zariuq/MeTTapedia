import Mettapedia.GSLT.Core.ComputabilityExamples
import Mettapedia.Computability.CodedRelations

/-!
# Computability classes of GSLTs

For a GSLT whose terms are coded, these are properties of the theory itself,
whatever presentation produced it:

* `DecidableEquations` and `EnumerableEquations`;
* `DecidableSteps` and `EnumerableSteps`, for the one-step relation;
* `ComputableSuccessors`: a function computable on codes lists exactly the
  successors of every term.

They are stated on codes, so they apply to any coding of terms, and at
Mathlib's encodings they are Mathlib's computable and recursively enumerable
predicates (`Computability.decidableOnCodes_iff`,
`Computability.enumerableOnCodes_iff`).

Computable successor lists give a decidable one-step relation when distinct
terms have distinct codes, and decidable relations are enumerable. Neither
converse holds. A program steps to the fuel at which it first returns: this
relation is decidable and every program has at most one successor, yet no
computable function lists the successors (`fuelTheory`). A program steps to a
mark when it halts: this relation is enumerable and not decidable
(`haltingTheory`). Equations can fail to be enumerable even without steps
(`ComputabilityExamples.static_equivalence_not_enumerable`).
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.ComputabilityClasses

open Mettapedia.Computability
open Nat.Partrec (Code)
open ComputabilityExamples (firstFuel firstFuel_computable no_computable_frontier)

section Classes

variable (G : GSLT.{0}) [Coded G.Term]

def DecidableEquations : Prop := DecidableOnCodes G.Equiv

def EnumerableEquations : Prop := EnumerableOnCodes G.Equiv

def DecidableSteps : Prop := DecidableOnCodes G.Step

def EnumerableSteps : Prop := EnumerableOnCodes G.Step

/-- A function computable on codes lists exactly the successors of every term. -/
def ComputableSuccessors : Prop :=
  ∃ next : G.Term → List G.Term, CodeComputable next ∧ ∀ s t, t ∈ next s ↔ G.Step s t

variable {G}

theorem DecidableEquations.enumerable (decidable : DecidableEquations G) : EnumerableEquations G :=
  DecidableOnCodes.enumerable decidable

theorem DecidableSteps.enumerable (decidable : DecidableSteps G) : EnumerableSteps G :=
  DecidableOnCodes.enumerable decidable

/-- Membership in a computed successor list decides the one-step relation, when distinct terms have distinct
codes. -/
theorem ComputableSuccessors.decidable (injective : Function.Injective (code : G.Term → ℕ))
    (listed : ComputableSuccessors G) : DecidableSteps G := by
  obtain ⟨next, ⟨track, trackComputable, tracks⟩, exact⟩ := listed
  refine ⟨fun p => decide (p.2 ∈ Denumerable.ofNat (List ℕ) (track p.1)),
    member_computable ((Primrec.ofNat (List ℕ)).to_comp.comp (trackComputable.comp Computable.fst))
      Computable.snd, fun s t => ?_⟩
  beta_reduce
  rw [tracks, ofNat_code_list, decide_eq_true_iff, ← exact]
  constructor
  · intro member
    obtain ⟨found, inside, same⟩ := List.mem_map.mp member
    exact injective same ▸ inside
  · exact List.mem_map_of_mem

end Classes

/-- Programs with an input or a fuel are coded by Mathlib's encodings. -/
instance : Coded Code := ⟨Encodable.encode⟩

theorem code_eq_encode (term : Code × ℕ) : code term = Encodable.encode term := rfl

/-! ## Decidable steps without computable successor lists -/

/-- Equality on a type of terms. -/
abbrev equality (Term : Type) : Setoid Term := ⟨Eq, ⟨Eq.refl, Eq.symm, Eq.trans⟩⟩

/-- A term `(code, 0)` is a program. It steps to `(code, n + 1)` when the program
first returns at fuel `n`. -/
def fuelTheory : GSLT.{0} where
  Term := Code × ℕ
  equations := equality _
  rewrites x y := x.2 = 0 ∧ y.1 = x.1 ∧ y.2 ≠ 0 ∧ firstFuel x.1 (y.2 - 1)
  rewrites_resp_left := fun {_ _ u} same moved => by
    cases same
    exact ⟨u, moved, rfl⟩
  rewrites_resp_right := fun moved same => by
    cases same
    exact moved

instance : Primcodable fuelTheory.Term := inferInstanceAs (Primcodable (Code × ℕ))

instance : Coded fuelTheory.Term := inferInstanceAs (Coded (Code × ℕ))

private theorem returns_primrec (fuel : (Code × ℕ) × (Code × ℕ) → ℕ) (effective : Primrec fuel) :
    Primrec fun p : (Code × ℕ) × (Code × ℕ) => (p.1.1.evaln (fuel p) 0).isSome :=
  Primrec.option_isSome.comp
    (Code.primrec_evaln.comp ((effective.pair (Primrec.fst.comp Primrec.fst)).pair (Primrec.const 0)))

theorem fuelTheory_decidable : DecidableSteps fuelTheory := by
  refine (decidableOnCodes_iff (γ := fuelTheory.Term) (δ := fuelTheory.Term) code_eq_encode code_eq_encode
    fuelTheory.Step).mpr ?_
  refine ComputablePred.computable_iff.mpr
    ⟨fun p : (Code × ℕ) × (Code × ℕ) =>
      decide (p.1.2 = 0) && decide (Encodable.encode p.2.1 = Encodable.encode p.1.1) &&
        !decide (p.2.2 = 0) &&
        ((p.1.1.evaln (p.2.2 - 1 + 1) 0).isSome && !(p.1.1.evaln (p.2.2 - 1) 0).isSome), ?_, ?_⟩
  · have later : Primrec fun p : (Code × ℕ) × (Code × ℕ) => p.2.2 - 1 :=
      Primrec.nat_sub.comp (Primrec.snd.comp Primrec.snd) (Primrec.const 1)
    exact (Primrec.and.comp
      (Primrec.and.comp
        (Primrec.and.comp
          (Primrec.eq.comp (Primrec.snd.comp Primrec.fst) (Primrec.const 0)).decide
          (Primrec.eq.comp (Primrec.encode.comp (Primrec.fst.comp Primrec.snd))
            (Primrec.encode.comp (Primrec.fst.comp Primrec.fst))).decide)
        (Primrec.not.comp (Primrec.eq.comp (Primrec.snd.comp Primrec.snd) (Primrec.const 0)).decide))
      (Primrec.and.comp (returns_primrec _ (Primrec.succ.comp later))
        (Primrec.not.comp (returns_primrec _ later)))).to_comp
  · funext p
    apply propext
    simp [fuelTheory, firstFuel, GSLT.Step, Bool.and_assoc, Encodable.encode_inj]

/-- The successors of a program cannot be listed by a computable function, since
the list would tell whether the program ever returns. -/
theorem fuelTheory_not_listed : ¬ ComputableSuccessors fuelTheory := by
  rintro ⟨next, codeComputable, exact⟩
  have computable : Computable next :=
    codeComputable.computable code_eq_encode (code_list_of_encode code_eq_encode)
  have shift : Primrec fun l : List (Code × ℕ) => l.map fun y : Code × ℕ => y.2 - 1 :=
    Primrec.list_map Primrec.id (Primrec.nat_sub.comp (Primrec.snd.comp Primrec.snd) (Primrec.const 1))
  refine no_computable_frontier (fun code => (next (code, 0)).map fun y : Code × ℕ => y.2 - 1)
    (shift.to_comp.comp (computable.comp (Computable.pair Computable.id (Computable.const 0)))) ?_
  intro code fuel
  constructor
  · intro member
    obtain ⟨y, inside, rfl⟩ := List.mem_map.mp member
    exact ((exact _ y).mp inside).2.2.2
  · intro first
    exact List.mem_map.mpr ⟨(code, fuel + 1), (exact _ _).mpr ⟨rfl, rfl, Nat.succ_ne_zero fuel, first⟩, rfl⟩

/-- **Strictness**: decidable steps do not give computable successor lists, even
with at most one successor per term. -/
theorem decidable_not_listed :
    DecidableSteps fuelTheory ∧ ¬ ComputableSuccessors fuelTheory :=
  ⟨fuelTheory_decidable, fuelTheory_not_listed⟩

/-! ## Enumerable steps that are not decidable -/

/-- A term `(code, 0)` is a program. It steps to `(code, 1)` when the program halts on `0`. -/
def haltingTheory : GSLT.{0} where
  Term := Code × ℕ
  equations := equality _
  rewrites x y := x.2 = 0 ∧ y = (x.1, 1) ∧ (x.1.eval 0).Dom
  rewrites_resp_left := fun {_ _ u} same moved => by
    cases same
    exact ⟨u, moved, rfl⟩
  rewrites_resp_right := fun moved same => by
    cases same
    exact moved

instance : Primcodable haltingTheory.Term := inferInstanceAs (Primcodable (Code × ℕ))

instance : Coded haltingTheory.Term := inferInstanceAs (Coded (Code × ℕ))

theorem haltingTheory_enumerable : EnumerableSteps haltingTheory := by
  refine (enumerableOnCodes_iff (γ := haltingTheory.Term) (δ := haltingTheory.Term) code_eq_encode code_eq_encode
    haltingTheory.Step).mpr ?_
  have shape : Computable fun p : (Code × ℕ) × (Code × ℕ) =>
      decide (p.1.2 = 0) && decide (Encodable.encode p.2 = Encodable.encode (p.1.1, 1)) :=
    (Primrec.and.comp (Primrec.eq.comp (Primrec.snd.comp Primrec.fst) (Primrec.const 0)).decide
      (Primrec.eq.comp (Primrec.encode.comp Primrec.snd)
        (Primrec.encode.comp ((Primrec.fst.comp Primrec.fst).pair (Primrec.const 1)))).decide).to_comp
  have runs : Partrec fun p : (Code × ℕ) × (Code × ℕ) => p.1.1.eval 0 :=
    Code.eval_part.comp (Computable.fst.comp Computable.fst) (Computable.const 0)
  refine (Partrec.dom_re (Partrec.cond shape runs Partrec.none)).of_eq fun p => ?_
  change (cond (decide (p.1.2 = 0) && decide (Encodable.encode p.2 = Encodable.encode (p.1.1, 1)))
      (p.1.1.eval 0) Part.none).Dom ↔ p.1.2 = 0 ∧ p.2 = (p.1.1, 1) ∧ (p.1.1.eval 0).Dom
  by_cases first : p.1.2 = 0 <;> by_cases second : p.2 = (p.1.1, 1)
  · rw [decide_eq_true first, decide_eq_true (congrArg Encodable.encode second)]
    simp [first, second]
  · rw [decide_eq_true first, decide_eq_false fun same => second (Encodable.encode_injective same)]
    simp [second]
  · rw [decide_eq_false first]
    simp [first]
  · rw [decide_eq_false first]
    simp [first]

/-- Halting is not decidable, so neither is this step relation. -/
theorem haltingTheory_not_decidable : ¬ DecidableSteps haltingTheory := by
  intro onCodes
  have decidable := (decidableOnCodes_iff (γ := haltingTheory.Term) (δ := haltingTheory.Term) code_eq_encode
    code_eq_encode haltingTheory.Step).mp onCodes
  apply ComputablePred.halting_problem 0
  obtain ⟨test, computable, spec⟩ := ComputablePred.computable_iff.mp decidable
  refine ComputablePred.computable_iff.mpr
    ⟨fun code => test ((code, 0), (code, 1)),
      computable.comp ((Computable.pair Computable.id (Computable.const 0)).pair
        (Computable.pair Computable.id (Computable.const 1))), ?_⟩
  funext code
  have here := congrFun spec ((code, 0), (code, 1))
  simp only at here
  rw [← here]
  apply propext
  simp [haltingTheory, GSLT.Step]

/-- **Strictness**: enumerable steps need not be decidable. -/
theorem enumerable_not_decidable :
    EnumerableSteps haltingTheory ∧ ¬ DecidableSteps haltingTheory :=
  ⟨haltingTheory_enumerable, haltingTheory_not_decidable⟩

end Mettapedia.GSLT.ComputabilityClasses

#print axioms Mettapedia.GSLT.ComputabilityClasses.ComputableSuccessors.decidable
#print axioms Mettapedia.GSLT.ComputabilityClasses.decidable_not_listed
#print axioms Mettapedia.GSLT.ComputabilityClasses.enumerable_not_decidable
