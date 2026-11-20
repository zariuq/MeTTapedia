import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.Budgets.Laws
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.Prices.SearchPrice

/-!
# Sound checkers form a directed family with no top: why a type discipline is a region

The ambient question "does `q` have property `P`" may be answered by many checkers. This module states
the precise form of the claim that faster, partial checkers for a rich property form an endless tree.

## (a) Sound checkers, directed

A **sound checker** (`Checker`) answers yes, no or "not decided" at every instance, and its yes and no
are sound. "Accept if either accepts" (`Checker.or`) is a sound checker extending both (`or_extends_left`,
`or_extends_right`), so sound checkers form a directed family; it accepts nothing that neither accepts
(`or_equal_iff`). Every budget of the tree's budgeted procedures is a sound checker
(`Procedure.atBudget`), the budgets form an increasing chain (`atBudget_extends`), and a checker is a
procedure whose verdict does not depend on the budget (`Checker.toProcedure`).

## (b) No top

For computable yes-or-unknown checkers on the naturals (`SoundChecker`), the only hypothesis used is
that the property is **not decidable** (`¬ ComputablePred P`); semidecidability is not used here.
* every sound checker misses an instance of the property (`exists_missed`);
* so every sound checker is strictly extended by another (`exists_strict_extension`);
* any given one has two incomparable strict extensions (`exists_incomparable_extensions`): a tree, not a
  line;
* there is an infinite strictly increasing chain (`exists_strict_chain`).
The instance: membership in the least-fixpoint type "the search succeeds" on the chain of states built
from the halting times of a program (`haltChain`, `reachesHalting_iff`) is not decidable
(`not_computablePred_reachesHalting`), so its sound checkers have no top (`reachesHalting_no_top`).
**Control:** for a decidable property the decider is the greatest sound checker
(`greatest_of_computablePred`, instance `zero_greatest`).

## (c) The limit: certificates

For a property given by a decidable certificate relation `R` (`Certified R q := ∃ n, R n q = true`):
* the certificate checker is complete by definition, and its budgets are the tree's budgeted decider
  (`certDecider`), answered exactly on the property (`certDecider_answered_iff`), with the budget
  dropped by the search for the least certificate (`Decider.search`, `certDecider_search`);
* **a sound certificate-free checker is a computable choice of certificate on its region**: the search
  for a certificate is partial recursive and converges on every instance the checker accepts
  (`certificate_choice`); conversely a decidable region with a computable certificate function on it is a
  computable sound checker whose region is exactly that region (`checker_of_certificates`).
A type discipline is such a region: on it the proof is a computable function of the term, and outside
it the ambient certificate search remains, sound and endless.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.Prices.CheckerTower

open UnificationWithLevels.TreeFibre.Budgets
open NativeTypesOnTheStep.Computing
open Nat.Partrec

/-! ## (a) Sound checkers form a directed family -/

section Directed

variable {Q : Type} {P : Q → Prop}

/-- **A sound checker**: a verdict at every instance, yes and no sound. -/
structure Checker (P : Q → Prop) where
  verdict : Q → Budgeted.Verdict
  yes_sound : ∀ {q : Q}, verdict q = .equal → P q
  no_sound : ∀ {q : Q}, verdict q = .different → ¬ P q

namespace Checker

/-- `d` extends `c`: every answer of `c` is an answer of `d`. -/
def Extends (d c : Checker P) : Prop := ∀ q, c.verdict q ≠ .undecided → d.verdict q = c.verdict q

/-- **Accept if either accepts, refuse if either refuses.** -/
def or (c d : Checker P) : Checker P where
  verdict q :=
    if c.verdict q = .equal ∨ d.verdict q = .equal then .equal
    else if c.verdict q = .different ∨ d.verdict q = .different then .different else .undecided
  yes_sound {q} h := by
    by_cases yes : c.verdict q = .equal ∨ d.verdict q = .equal
    · rcases yes with yes | yes
      · exact c.yes_sound yes
      · exact d.yes_sound yes
    · rw [if_neg yes] at h
      by_cases no : c.verdict q = .different ∨ d.verdict q = .different
      · rw [if_pos no] at h
        exact Budgeted.Verdict.noConfusion h
      · rw [if_neg no] at h
        exact Budgeted.Verdict.noConfusion h
  no_sound {q} h := by
    by_cases yes : c.verdict q = .equal ∨ d.verdict q = .equal
    · rw [if_pos yes] at h
      exact Budgeted.Verdict.noConfusion h
    · rw [if_neg yes] at h
      by_cases no : c.verdict q = .different ∨ d.verdict q = .different
      · rcases no with no | no
        · exact c.no_sound no
        · exact d.no_sound no
      · rw [if_neg no] at h
        exact Budgeted.Verdict.noConfusion h

/-- **Control: the combination accepts nothing that neither accepts.** -/
theorem or_equal_iff (c d : Checker P) (q : Q) :
    (c.or d).verdict q = .equal ↔ c.verdict q = .equal ∨ d.verdict q = .equal := by
  constructor
  · intro h
    by_contra neither
    have unfolded : (if c.verdict q = .equal ∨ d.verdict q = .equal then Budgeted.Verdict.equal
        else if c.verdict q = .different ∨ d.verdict q = .different then .different
          else .undecided) = .equal := h
    rw [if_neg neither] at unfolded
    split_ifs at unfolded
  · intro either
    show (if c.verdict q = .equal ∨ d.verdict q = .equal then Budgeted.Verdict.equal else _) = _
    rw [if_pos either]

/-- **The combination extends the first checker.** -/
theorem or_extends_left (c d : Checker P) : (c.or d).Extends c := by
  intro q decided
  cases hc : c.verdict q with
  | equal => exact (or_equal_iff c d q).mpr (Or.inl hc)
  | different =>
    have notYes : ¬ (c.verdict q = .equal ∨ d.verdict q = .equal) := by
      rintro (yes | yes)
      · rw [hc] at yes
        exact Budgeted.Verdict.noConfusion yes
      · exact c.no_sound hc (d.yes_sound yes)
    show (if c.verdict q = .equal ∨ d.verdict q = .equal then Budgeted.Verdict.equal
      else if c.verdict q = .different ∨ d.verdict q = .different then .different else .undecided) = _
    rw [if_neg notYes, if_pos (Or.inl hc)]
  | undecided => exact absurd hc decided

/-- **The combination extends the second checker.** -/
theorem or_extends_right (c d : Checker P) : (c.or d).Extends d := by
  intro q decided
  cases hd : d.verdict q with
  | equal => exact (or_equal_iff c d q).mpr (Or.inr hd)
  | different =>
    have notYes : ¬ (c.verdict q = .equal ∨ d.verdict q = .equal) := by
      rintro (yes | yes)
      · exact d.no_sound hd (c.yes_sound yes)
      · rw [hd] at yes
        exact Budgeted.Verdict.noConfusion yes
    show (if c.verdict q = .equal ∨ d.verdict q = .equal then Budgeted.Verdict.equal
      else if c.verdict q = .different ∨ d.verdict q = .different then .different else .undecided) = _
    rw [if_neg notYes, if_pos (Or.inr hd)]
  | undecided => exact absurd hd decided

/-- **Sound checkers form a directed family.** -/
theorem directed (c d : Checker P) : ∃ e : Checker P, e.Extends c ∧ e.Extends d :=
  ⟨c.or d, or_extends_left c d, or_extends_right c d⟩

/-- A checker is a budgeted procedure whose verdict does not depend on the budget. -/
def toProcedure (c : Checker P) : Procedure P where
  verdict _ q := c.verdict q
  ranOut _ q := c.verdict q = .undecided
  equal_sound := c.yes_sound
  different_sound := c.no_sound
  resolves _ _ := rfl
  undecided_iff := Iff.rfl

end Checker

/-- **Every budget of a budgeted procedure is a sound checker.** -/
def Procedure.atBudget (D : Procedure P) (k : ℕ) : Checker P where
  verdict q := D.verdict k q
  yes_sound := D.equal_sound
  no_sound := D.different_sound

/-- **The budgets of a procedure form an increasing chain of sound checkers.** -/
theorem atBudget_extends (D : Procedure P) {k k' : ℕ} (le : k ≤ k') :
    (Procedure.atBudget D k').Extends (Procedure.atBudget D k) :=
  fun _ decided => D.resolves le decided

end Directed

/-! ## (b) No top for an undecidable property -/

section NoTop

variable {P : ℕ → Prop}

/-- **A computable sound yes-or-unknown checker**: `true` means yes, `false` means not decided. -/
def SoundChecker (P : ℕ → Prop) (c : ℕ → Bool) : Prop := Computable c ∧ ∀ q, c q = true → P q

/-- `c'` accepts everything `c` accepts, and more. -/
def StrictlyExtends (c' c : ℕ → Bool) : Prop :=
  (∀ q, c q = true → c' q = true) ∧ ∃ q, c' q = true ∧ c q = false

/-- **An undecidable property defeats every sound checker**: some instance is missed. -/
theorem exists_missed (undecidable : ¬ ComputablePred P) {c : ℕ → Bool} (sound : SoundChecker P c) :
    ∃ q, P q ∧ c q = false := by
  classical
  by_contra none
  apply undecidable
  refine ⟨inferInstance, sound.1.of_eq fun q => ?_⟩
  rw [Bool.eq_iff_iff, decide_eq_true_iff]
  constructor
  · exact sound.2 q
  · intro holds
    cases hc : c q with
    | true => rfl
    | false => exact absurd ⟨q, holds, hc⟩ none

/-- Accept one more instance. -/
def addOne (c : ℕ → Bool) (q₀ : ℕ) : ℕ → Bool := fun q => c q || (q == q₀)

theorem addOne_sound {c : ℕ → Bool} (sound : SoundChecker P c) {q₀ : ℕ} (holds : P q₀) :
    SoundChecker P (addOne c q₀) := by
  refine ⟨Primrec.or.to_comp.comp sound.1 (Primrec.beq.comp Primrec.id (Primrec.const q₀)).to_comp,
    fun q accepted => ?_⟩
  rcases Bool.or_eq_true_iff.mp accepted with yes | same
  · exact sound.2 q yes
  · rw [beq_iff_eq.mp same]
    exact holds

theorem addOne_extends (c : ℕ → Bool) (q₀ q : ℕ) (accepted : c q = true) : addOne c q₀ q = true := by
  simp [addOne, accepted]

theorem addOne_self (c : ℕ → Bool) (q₀ : ℕ) : addOne c q₀ q₀ = true := by
  simp [addOne]

theorem addOne_other {c : ℕ → Bool} {q₀ q : ℕ} (ne : q ≠ q₀) (missed : c q = false) :
    addOne c q₀ q = false := by
  simp [addOne, missed, ne]

/-- **No top: every sound checker of an undecidable property is strictly extended.** -/
theorem exists_strict_extension (undecidable : ¬ ComputablePred P) {c : ℕ → Bool}
    (sound : SoundChecker P c) : ∃ c', SoundChecker P c' ∧ StrictlyExtends c' c := by
  obtain ⟨q₀, holds, missed⟩ := exists_missed undecidable sound
  exact ⟨addOne c q₀, addOne_sound sound holds, fun q accepted => addOne_extends c q₀ q accepted,
    q₀, addOne_self c q₀, missed⟩

/-- **A tree, not a line: two incomparable strict extensions.** -/
theorem exists_incomparable_extensions (undecidable : ¬ ComputablePred P) {c : ℕ → Bool}
    (sound : SoundChecker P c) :
    ∃ c₁ c₂, SoundChecker P c₁ ∧ SoundChecker P c₂ ∧ StrictlyExtends c₁ c ∧ StrictlyExtends c₂ c ∧
      (∃ q, c₁ q = true ∧ c₂ q = false) ∧ (∃ q, c₂ q = true ∧ c₁ q = false) := by
  obtain ⟨q₀, holds₀, missed₀⟩ := exists_missed undecidable sound
  have sound₀ := addOne_sound sound holds₀
  obtain ⟨q₁, holds₁, missed₁⟩ := exists_missed undecidable sound₀
  have ne : q₁ ≠ q₀ := fun same => by
    rw [same, addOne_self] at missed₁
    exact Bool.noConfusion missed₁
  have missedC : c q₁ = false := by
    cases hc : c q₁ with
    | false => rfl
    | true => rw [addOne_extends c q₀ q₁ hc] at missed₁; exact Bool.noConfusion missed₁
  refine ⟨addOne c q₀, addOne c q₁, sound₀, addOne_sound sound holds₁,
    ⟨fun q accepted => addOne_extends c q₀ q accepted, q₀, addOne_self c q₀, missed₀⟩,
    ⟨fun q accepted => addOne_extends c q₁ q accepted, q₁, addOne_self c q₁, missedC⟩,
    ⟨q₀, addOne_self c q₀, addOne_other (Ne.symm ne) missed₀⟩, ⟨q₁, addOne_self c q₁, missed₁⟩⟩

/-- **An infinite strictly increasing chain of sound checkers.** -/
theorem exists_strict_chain (undecidable : ¬ ComputablePred P) :
    ∃ chain : ℕ → ℕ → Bool, (∀ n, SoundChecker P (chain n)) ∧
      ∀ n, StrictlyExtends (chain (n + 1)) (chain n) := by
  classical
  let step : {c : ℕ → Bool // SoundChecker P c} → {c : ℕ → Bool // SoundChecker P c} := fun c =>
    ⟨Classical.choose (exists_strict_extension undecidable c.2),
      (Classical.choose_spec (exists_strict_extension undecidable c.2)).1⟩
  let start : {c : ℕ → Bool // SoundChecker P c} :=
    ⟨fun _ => false, Computable.const false, fun _ accepted => Bool.noConfusion accepted⟩
  let seq : ℕ → {c : ℕ → Bool // SoundChecker P c} := fun n => Nat.rec start (fun _ c => step c) n
  exact ⟨fun n => (seq n).1, fun n => (seq n).2,
    fun n => (Classical.choose_spec (exists_strict_extension undecidable (seq n).2)).2⟩

/-- **Control: a decidable property has a greatest sound checker**, its decider. -/
theorem greatest_of_computablePred (decidable : ComputablePred P) :
    ∃ d, SoundChecker P d ∧ ∀ c, SoundChecker P c → ∀ q, c q = true → d q = true := by
  obtain ⟨_, computable⟩ := decidable
  exact ⟨fun q => decide (P q), ⟨computable, fun q accepted => of_decide_eq_true accepted⟩,
    fun c sound q accepted => decide_eq_true (sound.2 q accepted)⟩

/-- Control instance: "is zero" is decidable, so its sound checkers have a greatest one. -/
theorem zero_greatest :
    ∃ d, SoundChecker (fun n => n = 0) d ∧
      ∀ c, SoundChecker (fun n => n = 0) c → ∀ q, c q = true → d q = true :=
  greatest_of_computablePred ⟨inferInstance,
    (Primrec.beq.comp Primrec.id (Primrec.const 0)).to_comp.of_eq fun n => by cases n <;> rfl⟩

/-! ### The instance: a least-fixpoint type built from the halting times of programs -/

open SearchPrice

/-- The chain whose goals are the stages at which program `n` has halted on input `0`. -/
def haltChain (n : ℕ) : SearchSystem ℕ :=
  chain fun k => (Code.evaln k (Denumerable.ofNat Code n) 0).isSome

/-- Membership of the first state in the least-fixpoint type "the search succeeds". -/
def ReachesHalting (n : ℕ) : Prop := Reaches (haltChain n) 0

theorem reachesHalting_iff (n : ℕ) :
    ReachesHalting n ↔ (Code.eval (Denumerable.ofNat Code n) 0).Dom := by
  rw [ReachesHalting, haltChain, chain_reaches_iff,
    Mettapedia.Logic.ReverseMathematics.Omniscience.halts_iff_exists_haltBit]

/-- **Membership in this least-fixpoint type is not decidable.** -/
theorem not_computablePred_reachesHalting : ¬ ComputablePred ReachesHalting := by
  classical
  rintro ⟨_, computable⟩
  apply ComputablePred.halting_problem 0
  refine ⟨inferInstance, (computable.comp Computable.encode).of_eq fun c => ?_⟩
  rw [Bool.eq_iff_iff, decide_eq_true_iff, decide_eq_true_iff, reachesHalting_iff,
    Denumerable.ofNat_encode]

/-- **Its sound checkers have no top**, and branch. -/
theorem reachesHalting_no_top {c : ℕ → Bool} (sound : SoundChecker ReachesHalting c) :
    ∃ c', SoundChecker ReachesHalting c' ∧ StrictlyExtends c' c :=
  exists_strict_extension not_computablePred_reachesHalting sound

theorem reachesHalting_chain :
    ∃ chain : ℕ → ℕ → Bool, (∀ n, SoundChecker ReachesHalting (chain n)) ∧
      ∀ n, StrictlyExtends (chain (n + 1)) (chain n) :=
  exists_strict_chain not_computablePred_reachesHalting

end NoTop

/-! ## (c) The limit: certificates -/

section Certificates

variable {Q : Type} [Primcodable Q] (R : ℕ → Q → Bool)

/-- The property certified by `R`: some number is a certificate. -/
def Certified (q : Q) : Prop := ∃ n, R n q = true

/-- **The certificate checker, budgeted**: at budget `k`, the certificate `k`; the tree's decider. -/
def certDecider : Decider (Certified R) where
  Answer q := {n : ℕ // R n q = true}
  attempt k q := if h : R k q = true then some ⟨k, h⟩ else none
  sign _ := true
  yes a _ := ⟨a.1, a.2⟩
  no _ h := Bool.noConfusion h

omit [Primcodable Q] in
/-- **The certificate checker is answered exactly on the property.** -/
theorem certDecider_answered_iff (q : Q) :
    (∃ k, (certDecider R).procedure.verdict k q ≠ .undecided) ↔ Certified R q := by
  rw [Decider.answered_iff]
  constructor
  · rintro ⟨k, a, _⟩
    exact ⟨a.1, a.2⟩
  · rintro ⟨n, hn⟩
    exact ⟨n, ⟨n, hn⟩, by simp [certDecider, hn]⟩

omit [Primcodable Q] in
/-- **On the property, the budget is dropped**: the search with no budget returns a certificate. -/
theorem certDecider_search {q : Q} (answered : ∃ k a, (certDecider R).attempt k q = some a) :
    R ((certDecider R).search answered).1 q = true :=
  ((certDecider R).search answered).2

/-- **A sound certificate-free checker is a computable choice of certificate on its region**: the
search for a certificate is partial recursive and converges on every accepted instance. -/
theorem certificate_choice (computableR : Computable₂ R) (c : Q → Bool)
    (sound : ∀ q, c q = true → Certified R q) :
    ∃ f : Q →. ℕ, Partrec f ∧ ∀ q, c q = true → ∃ n ∈ f q, R n q = true := by
  classical
  refine ⟨fun q => Nat.rfind fun n => (R n q : Part Bool), ?_, fun q accepted => ?_⟩
  · exact Partrec.rfind ((computableR.comp Computable.snd Computable.fst).to₂.partrec₂)
  · obtain ⟨m, hm⟩ := sound q accepted
    obtain ⟨n, mem, _⟩ := Nat.rfind_min' (p := fun n => R n q) hm
    refine ⟨n, mem, ?_⟩
    have spec := Nat.rfind_spec mem
    simpa using spec

/-- **A decidable region with a computable certificate on it is a computable sound checker**, whose
region is exactly that region. -/
theorem checker_of_certificates (computableR : Computable₂ R) (region : Q → Bool) (certificate : Q → ℕ)
    (computableRegion : Computable region) (computableCertificate : Computable certificate)
    (valid : ∀ q, region q = true → R (certificate q) q = true) :
    ∃ c : Q → Bool, Computable c ∧ (∀ q, c q = true → Certified R q) ∧
      ∀ q, c q = true ↔ region q = true := by
  refine ⟨fun q => region q && R (certificate q) q, ?_, fun q accepted => ?_, fun q => ?_⟩
  · exact Primrec.and.to_comp.comp computableRegion
      (computableR.comp computableCertificate Computable.id)
  · exact ⟨certificate q, (Bool.and_eq_true_iff.mp accepted).2⟩
  · constructor
    · intro accepted
      exact (Bool.and_eq_true_iff.mp accepted).1
    · intro inside
      exact Bool.and_eq_true_iff.mpr ⟨inside, valid q inside⟩

end Certificates

#print axioms Checker.or_equal_iff
#print axioms Checker.or_extends_left
#print axioms Checker.or_extends_right
#print axioms Checker.directed
#print axioms atBudget_extends
#print axioms exists_missed
#print axioms exists_strict_extension
#print axioms exists_incomparable_extensions
#print axioms exists_strict_chain
#print axioms greatest_of_computablePred
#print axioms zero_greatest
#print axioms reachesHalting_iff
#print axioms not_computablePred_reachesHalting
#print axioms reachesHalting_no_top
#print axioms reachesHalting_chain
#print axioms certDecider_answered_iff
#print axioms certDecider_search
#print axioms certificate_choice
#print axioms checker_of_certificates

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.Prices.CheckerTower
