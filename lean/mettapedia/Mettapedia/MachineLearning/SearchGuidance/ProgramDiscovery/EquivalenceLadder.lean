import Mettapedia.MachineLearning.SearchGuidance.ProgramDiscovery.DiscoveryKernel
import Mettapedia.GSLT.Logic.LogicalMetric
import Mettapedia.GSLT.LanguageDef.Gauthier.ProbeRigidity
import Mettapedia.GSLT.LanguageDef.Gauthier.Skeleton

/-!
# Program equivalence and bounded similarity

Exact syntax, bounded output agreement, finite-corpus solve footprints, and
full extensional equality are deliberately separate relations.  This file
proves their valid implications, concrete failures of invalid converses, and
an instantiation against the actual Gauthier E1 evaluator.
-/

namespace Mettapedia.MachineLearning.SearchGuidance.ProgramDiscovery

universe uP uT uO

/-- Equality in one authenticated program encoding. -/
def ExactSyntaxEq {Program : Type uP} (left right : Program) : Prop :=
  left = right

/-- Agreement of the first `n` outputs of a declared semantics. -/
def PrefixEquivalent {Program : Type uP} {Output : Type uO}
    (semantics : Program → ℕ → Output) (n : ℕ) (left right : Program) : Prop :=
  ∀ i, i < n → semantics left i = semantics right i

/-- Equality of solve footprints only on a declared finite corpus. -/
def FootprintEquivalent {Program : Type uP} {Target : Type uT}
    (solves : Program → Target → Prop) (corpus : Finset Target)
    (left right : Program) : Prop :=
  ∀ target ∈ corpus, solves left target ↔ solves right target

/-- Full equality of generated outputs. -/
def ExtensionalEquivalent {Program : Type uP} {Output : Type uO}
    (semantics : Program → ℕ → Output) (left right : Program) : Prop :=
  ∀ i, semantics left i = semantics right i

theorem exactSyntax_implies_prefixEquivalent
    {Program : Type uP} {Output : Type uO}
    (semantics : Program → ℕ → Output) (n : ℕ) {left right : Program}
    (h : ExactSyntaxEq left right) : PrefixEquivalent semantics n left right := by
  subst right
  intro i hi
  rfl

theorem exactSyntax_implies_footprintEquivalent
    {Program : Type uP} {Target : Type uT}
    (solves : Program → Target → Prop) (corpus : Finset Target)
    {left right : Program} (h : ExactSyntaxEq left right) :
    FootprintEquivalent solves corpus left right := by
  subst right
  intro target htarget
  rfl

theorem exactSyntax_implies_extensionalEquivalent
    {Program : Type uP} {Output : Type uO}
    (semantics : Program → ℕ → Output) {left right : Program}
    (h : ExactSyntaxEq left right) : ExtensionalEquivalent semantics left right := by
  subst right
  intro i
  rfl

theorem extensional_implies_prefixEquivalent
    {Program : Type uP} {Output : Type uO}
    (semantics : Program → ℕ → Output) (n : ℕ) {left right : Program}
    (h : ExtensionalEquivalent semantics left right) :
    PrefixEquivalent semantics n left right := by
  intro i hi
  exact h i

/-- Extensional equality transports finite solve footprints exactly when the
checker/solve relation is extensional.  This assumption is explicit because
arbitrary metadata predicates need not respect program behavior. -/
theorem extensional_implies_footprintEquivalent
    {Program : Type uP} {Target : Type uT} {Output : Type uO}
    (semantics : Program → ℕ → Output)
    (solves : Program → Target → Prop) (corpus : Finset Target)
    (solveCongr : ∀ {left right}, ExtensionalEquivalent semantics left right →
      ∀ target, solves left target ↔ solves right target)
    {left right : Program} (h : ExtensionalEquivalent semantics left right) :
    FootprintEquivalent solves corpus left right := by
  intro target htarget
  exact solveCongr h target

theorem prefixEquivalent_refl {Program : Type uP} {Output : Type uO}
    (semantics : Program → ℕ → Output) (n : ℕ) (program : Program) :
    PrefixEquivalent semantics n program program := by
  intro i hi
  rfl

theorem prefixEquivalent_symm {Program : Type uP} {Output : Type uO}
    {semantics : Program → ℕ → Output} {n : ℕ} {left right : Program}
    (h : PrefixEquivalent semantics n left right) :
    PrefixEquivalent semantics n right left := by
  intro i hi
  exact (h i hi).symm

theorem prefixEquivalent_trans {Program : Type uP} {Output : Type uO}
    {semantics : Program → ℕ → Output} {n : ℕ}
    {first second third : Program}
    (h₁ : PrefixEquivalent semantics n first second)
    (h₂ : PrefixEquivalent semantics n second third) :
    PrefixEquivalent semantics n first third := by
  intro i hi
  exact (h₁ i hi).trans (h₂ i hi)

/-- Binary bounded semantic prefix pseudometric.  It identifies exactly the
programs that no observation in the first `n` outputs distinguishes. -/
noncomputable def prefixDistance {Program : Type uP} {Output : Type uO}
    (semantics : Program → ℕ → Output) (n : ℕ)
    (left right : Program) : ℕ := by
  classical
  exact if PrefixEquivalent semantics n left right then 0 else 1

@[simp] theorem prefixDistance_self {Program : Type uP} {Output : Type uO}
    (semantics : Program → ℕ → Output) (n : ℕ) (program : Program) :
    prefixDistance semantics n program program = 0 := by
  classical
  simp [prefixDistance, prefixEquivalent_refl]

theorem prefixDistance_eq_zero_iff {Program : Type uP} {Output : Type uO}
    (semantics : Program → ℕ → Output) (n : ℕ) (left right : Program) :
    prefixDistance semantics n left right = 0 ↔
      PrefixEquivalent semantics n left right := by
  classical
  by_cases h : PrefixEquivalent semantics n left right <;> simp [prefixDistance, h]

theorem prefixDistance_comm {Program : Type uP} {Output : Type uO}
    (semantics : Program → ℕ → Output) (n : ℕ) (left right : Program) :
    prefixDistance semantics n left right = prefixDistance semantics n right left := by
  classical
  by_cases h : PrefixEquivalent semantics n left right
  · have h' := prefixEquivalent_symm h
    simp [prefixDistance, h, h']
  · have h' : ¬ PrefixEquivalent semantics n right left := fun hs ↦
      h (prefixEquivalent_symm hs)
    simp [prefixDistance, h, h']

theorem prefixDistance_ultrametric {Program : Type uP} {Output : Type uO}
    (semantics : Program → ℕ → Output) (n : ℕ)
    (first second third : Program) :
    prefixDistance semantics n first third ≤
      max (prefixDistance semantics n first second)
        (prefixDistance semantics n second third) := by
  classical
  by_cases h₁₃ : PrefixEquivalent semantics n first third
  · simp [prefixDistance, h₁₃]
  · by_cases h₁₂ : PrefixEquivalent semantics n first second
    · by_cases h₂₃ : PrefixEquivalent semantics n second third
      · exact (h₁₃ (prefixEquivalent_trans h₁₂ h₂₃)).elim
      · simp [prefixDistance, h₁₃, h₁₂, h₂₃]
    · simp [prefixDistance, h₁₃, h₁₂]

/-- Exact syntactic distance is introduced only after the semantic boundary:
zero here means authenticated syntax equality, not behavioral equivalence. -/
noncomputable def exactSyntaxDistance {Program : Type uP} (left right : Program) : ℕ := by
  classical
  exact if ExactSyntaxEq left right then 0 else 1

theorem exactSyntaxDistance_eq_zero_iff {Program : Type uP} (left right : Program) :
    exactSyntaxDistance left right = 0 ↔ ExactSyntaxEq left right := by
  classical
  by_cases h : ExactSyntaxEq left right <;> simp [exactSyntaxDistance, h]

/-- The HML logical metric and output-prefix metric coincide only after an
explicit theorem identifies their two observational equivalences. -/
theorem prefixDistance_eq_logicalDistanceApprox_of_iff
    {Program : Type uP} {Output : Type uO}
    {S : Mettapedia.GSLT.GSLT} [Mettapedia.GSLT.HasMinimalContexts S]
    (semantics : Program → ℕ → Output) (n : ℕ)
    (left right : Program) (t u : S.Term)
    (hbridge : PrefixEquivalent semantics n left right ↔
      Mettapedia.GSLT.HMLFormula.hmlEquivUpTo (S := S) n t u) :
    prefixDistance semantics n left right =
      Mettapedia.GSLT.HMLFormula.logicalDistanceApprox (S := S) n t u := by
  classical
  by_cases h : PrefixEquivalent semantics n left right
  · simp [prefixDistance, h,
      Mettapedia.GSLT.HMLFormula.logicalDistanceApprox, hbridge.mp h]
  · have hhml :
        ¬ Mettapedia.GSLT.HMLFormula.hmlEquivUpTo (S := S) n t u := fun hh ↦
      h (hbridge.mpr hh)
    simp [prefixDistance, h,
      Mettapedia.GSLT.HMLFormula.logicalDistanceApprox, hhml]

/-! ## Concrete converse failures -/

namespace EquivalenceFixtures

inductive Program where
  | zeroA
  | zeroB
  | lateOne
  deriving DecidableEq, Repr

def semantics : Program → ℕ → ℕ
  | .zeroA, _ => 0
  | .zeroB, _ => 0
  | .lateOne, i => if i < 2 then 0 else 1

def solves : Program → Bool → Prop
  | .zeroA, false => True
  | .zeroA, true => False
  | .zeroB, false => True
  | .zeroB, true => False
  | .lateOne, false => True
  | .lateOne, true => True

theorem distinct_programs_can_be_extensionally_equal :
    Program.zeroA ≠ Program.zeroB ∧
      ExtensionalEquivalent semantics .zeroA .zeroB := by
  constructor
  · decide
  · intro i
    rfl

theorem finite_prefix_equality_not_extensional :
    PrefixEquivalent semantics 2 .zeroA .lateOne ∧
      ¬ ExtensionalEquivalent semantics .zeroA .lateOne := by
  constructor
  · intro i hi
    simp [semantics, hi]
  · intro h
    have := h 2
    simp [semantics] at this

theorem equal_finite_footprint_not_global :
    FootprintEquivalent solves {false} .zeroA .lateOne ∧
      ¬ (solves .zeroA true ↔ solves .lateOne true) := by
  constructor
  · intro target htarget
    have : target = false := by simpa using htarget
    subst target
    rfl
  · simp [solves]

theorem one_common_target_not_extensional :
    solves .zeroA false ∧ solves .lateOne false ∧
      ¬ ExtensionalEquivalent semantics .zeroA .lateOne := by
  exact ⟨trivial, trivial, finite_prefix_equality_not_extensional.2⟩

theorem prefix_pseudometric_zero :
    prefixDistance semantics 2 .zeroA .lateOne = 0 :=
  (prefixDistance_eq_zero_iff semantics 2 .zeroA .lateOne).2
    finite_prefix_equality_not_extensional.1

end EquivalenceFixtures

/-! ## Gauthier E1 instantiation -/

namespace Gauthier

open Mettapedia.GSLT.LanguageDef.GauthierE1
open Mettapedia.GSLT.LanguageDef.GauthierBigStepGSLT
open Mettapedia.GSLT.LanguageDef.GauthierProbeRigidity
open Mettapedia.GSLT.LanguageDef.GauthierSkeleton

/-- Bounded OEIS behavior in the real E1 evaluator: at every probed seed, both
programs produce exactly the same emitted values. -/
def PrefixEquivalent (fuel n : ℕ) (left right : Prog) : Prop :=
  ∀ i, i < n → ∀ value,
    EmitsAt orgE1Signature fuel left (Int.ofNat i) value ↔
      EmitsAt orgE1Signature fuel right (Int.ofNat i) value

theorem prefixEquivalent_refl (fuel n : ℕ) (program : Prog) :
    PrefixEquivalent fuel n program program := by
  intro i hi value
  rfl

theorem extensional_implies_prefixEquivalent
    {left right : Prog} (h : Extensional orgE1Signature left right)
    (fuel n : ℕ) : PrefixEquivalent fuel n left right := by
  intro i hi value
  rw [emitsAt_iff, emitsAt_iff]
  constructor
  · rintro ⟨store, heval⟩
    exact ⟨store, (h fuel (seed (Int.ofNat i)) Store.zero).symm.trans heval⟩
  · rintro ⟨store, heval⟩
    exact ⟨store, (h fuel (seed (Int.ofNat i)) Store.zero).trans heval⟩

private theorem listGet?_some_lt {values : List Int} {i : ℕ} {value : Int}
    (h : listGet? values i = some value) : i < values.length := by
  induction values generalizing i with
  | nil => simp [listGet?] at h
  | cons head tail ih =>
      cases i with
      | zero => simp
      | succ i =>
          simp only [listGet?] at h
          simpa using ih h

/-- Mutual bounded behavior transports the public `EmitsPrefix` observation
predicate; this is the required bridge to the evaluator's existing boundary. -/
theorem prefixEquivalent_transports_emitsPrefix
    {fuel n : ℕ} {left right : Prog} (h : PrefixEquivalent fuel n left right)
    {values : List Int} (hlen : values.length ≤ n) :
    EmitsPrefix orgE1Signature fuel left values ↔
      EmitsPrefix orgE1Signature fuel right values := by
  constructor
  · intro hp i value hget
    exact (h i (lt_of_lt_of_le (listGet?_some_lt hget) hlen) value).mp
      (hp i value hget)
  · intro hp i value hget
    exact (h i (lt_of_lt_of_le (listGet?_some_lt hget) hlen) value).mpr
      (hp i value hget)

/-- Two syntactically distinct Gauthier programs are fully extensionally equal
by the authenticated commutativity law for the actual scalar table. -/
theorem distinct_syntax_extensionally_equal :
    Org.addi Org.X Org.z ≠ Org.addi Org.z Org.X ∧
      Extensional orgE1Signature (Org.addi Org.X Org.z) (Org.addi Org.z Org.X) := by
  constructor
  · simp [Org.addi, Org.X, Org.z]
  · intro fuel cfg store
    exact scalarOrg_addi_commutativeEvalLaw fuel Org.X Org.z cfg store

/-- The sealed rigidity witness is promoted from "shares one emitted list" to
the actual mutual one-seed observational equivalence relation. -/
theorem one_seed_prefixEquivalent_not_extensional :
    PrefixEquivalent 20 1 probeId probeZeroAfterZero ∧
      ¬ Extensional orgE1Signature probeId probeZeroAfterZero := by
  constructor
  · intro i hi value
    have hi0 : i = 0 := Nat.lt_one_iff.mp hi
    subst i
    rw [emitsAt_iff, emitsAt_iff]
    simp [probeId, probeZeroAfterZero, Org.cond, Org.X, Org.z, eval,
      orgE1Signature, entryAt, listGet?, entry, seed]
  · exact probe_witness_not_extensional

/-- Binary E1 prefix distance; zero is exactly the bounded evaluator relation,
not full program equivalence. -/
noncomputable def prefixDistance (fuel n : ℕ) (left right : Prog) : ℕ := by
  classical
  exact if PrefixEquivalent fuel n left right then 0 else 1

theorem prefixDistance_eq_zero_iff (fuel n : ℕ) (left right : Prog) :
    prefixDistance fuel n left right = 0 ↔ PrefixEquivalent fuel n left right := by
  classical
  by_cases h : PrefixEquivalent fuel n left right <;> simp [prefixDistance, h]

theorem probe_prefixDistance_zero_but_not_extensional :
    prefixDistance 20 1 probeId probeZeroAfterZero = 0 ∧
      ¬ Extensional orgE1Signature probeId probeZeroAfterZero := by
  exact ⟨(prefixDistance_eq_zero_iff 20 1 _ _).2
    one_seed_prefixEquivalent_not_extensional.1,
    one_seed_prefixEquivalent_not_extensional.2⟩

end Gauthier

end Mettapedia.MachineLearning.SearchGuidance.ProgramDiscovery
