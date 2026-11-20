import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.ReflQuotientTransport
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.FiniteControls

/-!
# Where the frame modulo the bag laws and the corrected semantics agree, and where they differ

The finite program of `FiniteComm` runs at the quotient frame `QX` (`ReflQuotientTransport`). These are its
controls, each with the same program and the same opening as `FiniteControls`.

* **The transport applies** (`example_comm_bag`): the manuscript's example `for((0) <- @0)0 | for(y <- @0)y`
  meets the named hypothesis (no parallel bag in its patterns, canonical patterns) and fires at `QX`.
* **Positive** (`names_admitted_at_quotient`, `names_refused_at_syntax`): a COMM through the names `@(a | b)`
  and `@(b | a)`, equal only modulo the bag laws, is admitted at `QX` and refused at the syntactic frame at
  every opening.
* **Negative, (d)** (`open_admitted_at_quotient`, `open_refused_by_source`, `open_refused_at_syntax`): with a
  name pattern quoting a bag with an unknown, `((Y | a))` against `((a | b))`, `QX` admits a COMM (reading `Y`
  as `b`) that the corrected semantics refuses: its executable steps are empty, so by its completeness no step
  of the corrected semantics modulo the bag laws exists. The named hypothesis fails there
  (`patY_not_groundBags`).
* **(d')** (`written_order_partner_meets_at_quotient`): on the corrected semantics' own control
  `written_order_partner_misses`, a partner quoting `(b | a)` misses the canonical listener `((a | b))` in the
  corrected semantics and meets it at `QX`. The partner's written name is not canonical
  (`written_order_facts`), so the named hypothesis of `comm_one_firing_bag` fails there.
* **Heating** (`heat_admitted_at_quotient`, `heat_refused_at_syntax`, `heat_reads_ambiguous`): at `QX` the heat
  rule's pattern `A | B` matches an input that is no parallel composition, as `0 | input`, and the made rows have
  no determined reading: two solutions of the result read the first made row as `0` and as the input. The
  syntactic frame refuses that heating at every opening.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.ReflQuotient.Controls

open Mettapedia.OSLF.MeTTaIL.Syntax (Pattern)
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus (pFor par pZero nQuote applyDot tProc demoChan pPar)
open MeTTaOperationsComm (psubst pvars PSubst psubst_of_pvars_nil)
open FiniteProgram (predot commAt program comm_reads_inputs)
open FiniteProgram.Controls (fresh_at rename rows example_apart)
open Comm (X E renameBy)
open Comm.Controls (start zeroTerm y unifier unifier_groundPrincipal)
open OneFrame (embed)
open MeTTaCalculus.Corrected.BagControls (atomA atomB)
open MeTTaCalculus.Corrected (canonicalBag cstep cstepCanon cstepCanon_complete CanonicalBagStep closing)
open MeTTaCalculus.Corrected.ReflectionControls (canonicalListener written_order_partner_misses)

/-! ## The transport applies -/

/-- `y` read as `(0)`. -/
def yToZero : PSubst := fun v => if v = "y" then some zeroTerm else none

/-- **The manuscript's example fires at the quotient frame**, through `comm_one_firing_bag`: its patterns have
no parallel bag and are canonical. Every solution reads the receiver's made row as the representation of
`@((0))`, modulo the bag laws. -/
theorem example_comm_bag :
    (RuleSyntax.step QX ℕ QE program).Admits (s := embed rows start) (commAtQ (renameBy rename) 0 1 2 3) ∧
      ∀ σ : PSubst,
        bagAction.Models σ ((commAtQ (renameBy rename) 0 1 2 3).result QX (embed rows start)).knowledge →
          BagLaws (psubst σ (((commAtQ (renameBy rename) 0 1 2 3).result QX (embed rows start)).label 3))
            (psubst σ (predot (applyDot unifier y))) := by
  obtain ⟨admitted, -, -, reads⟩ := comm_one_firing_bag rows zeroTerm y demoChan pZero y unifier
    unifier_groundPrincipal example_apart (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    start 0 1 2 3 (fun _ _ => BagLaws.refl _) (fun _ _ => BagLaws.refl _)
    (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    ⟨yToZero, fun _ member => absurd member List.not_mem_nil, by decide +kernel⟩
    (fresh_quotient (fresh_at rows (by decide +kernel) (by decide +kernel)))
  exact ⟨admitted, fun σ solved => (reads σ solved).2⟩

/-! ## Positive: a COMM through names equal modulo the bag laws -/

/-- The names `@(a | b)` and `@(b | a)`. -/
def chanAB : Pattern := nQuote (par atomA atomB)
def chanBA : Pattern := nQuote (par atomB atomA)

/-- An input on each. -/
def onAB : Pattern := pFor pZero chanAB pZero
def onBA : Pattern := pFor pZero chanBA pZero

/-- The input on `@(a | b)` at `0`, the input on `@(b | a)` at `1`. -/
def rowsNames : ℕ → Pattern
  | 0 => onAB
  | 1 => onBA
  | _ => pZero

/-- The inputs are their own representations. -/
theorem names_represented : predot onAB = onAB ∧ predot onBA = onBA := by
  constructor <;> decide +kernel

theorem names_related : BagLaws onBA onAB := by decide +kernel

/-- **Positive control, the quotient frame**: the COMM through the two names is admitted. -/
theorem names_admitted_at_quotient :
    (RuleSyntax.step QX ℕ QE program).Admits (s := embed rowsNames start) (commAtQ (renameBy rename) 0 1 2 3) :=
  comm_admits_bag rowsNames pZero pZero chanAB pZero pZero start 0 1 2 3
    (fun _ _ => BagLaws.refl _) (fun σ _ => bagLaws_psubst σ names_related)
    (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (σ₀ := fun _ => none) (fun _ member => absurd member List.not_mem_nil) (BagLaws.refl _)
    (fresh_quotient (fresh_at rowsNames (by decide +kernel) (by decide +kernel)))

/-- **Positive control, the syntactic frame**: the same COMM is refused at every opening. -/
theorem names_refused_at_syntax (ρ : PSubst) :
    ¬ (RuleSyntax.step X ℕ E program).Admits (s := embed rowsNames start) (commAt ρ 0 1 2 3) := by
  intro admitted
  obtain ⟨_, σ, solved⟩ := ((RuleSyntax.admits_iff _).mp admitted).2.2.2.1
  obtain ⟨-, -, channels, -, -⟩ := comm_reads_inputs rowsNames pZero pZero chanAB chanBA pZero pZero start 0 1 2 3
    (fun _ _ => rfl) (fun _ _ => rfl) (by decide) ρ solved
  rw [psubst_of_pvars_nil σ chanAB (by decide +kernel), psubst_of_pvars_nil σ chanBA (by decide +kernel)] at channels
  exact absurd channels (by decide +kernel)

/-! ## Negative, (d): a name pattern quoting a bag with an unknown -/

/-- The pattern `((Y | a))`, and the ground pattern `((a | b))`. -/
def patY : Pattern := tProc (par (.fvar "Y") atomA)
def patAB : Pattern := tProc (par atomA atomB)

/-- An input with each pattern. -/
def inputY : Pattern := pFor patY demoChan pZero
def inputAB : Pattern := pFor patAB demoChan pZero

/-- The two inputs at `0` and `1`. -/
def rowsOpen : ℕ → Pattern
  | 0 => inputY
  | 1 => inputAB
  | _ => pZero

/-- The inputs are their own representations; the bag of `((Y | a))` is not ground, so the named hypothesis of
`comm_one_firing_bag` fails. -/
theorem open_facts : predot inputY = inputY ∧ predot inputAB = inputAB ∧ groundBags patY = false := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩

/-- `Y` read as `b`. -/
def yToB : PSubst := fun v => if v = "Y" then some atomB else none

/-- **Control (d), the quotient frame**: the COMM is admitted, reading `Y` as `b`. -/
theorem open_admitted_at_quotient :
    (RuleSyntax.step QX ℕ QE program).Admits (s := embed rowsOpen start) (commAtQ (renameBy rename) 0 1 2 3) :=
  comm_admits_bag rowsOpen patY patAB demoChan pZero pZero start 0 1 2 3
    (fun _ _ => BagLaws.refl _) (fun _ _ => BagLaws.refl _)
    (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (σ₀ := yToB) (fun _ member => absurd member List.not_mem_nil) (by decide +kernel)
    (fresh_quotient (fresh_at rowsOpen (by decide +kernel) (by decide +kernel)))

/-- **Control (d), the source**: the corrected semantics refuses. Its executable steps, with and without
canonical reflection, are empty, and by completeness no step of the corrected semantics modulo the bag laws
exists from the redex. -/
theorem open_refused_by_source :
    cstep (par inputY inputAB) = [] ∧ cstepCanon (par inputY inputAB) = [] ∧
      ∀ Q, ¬ CanonicalBagStep closing (par inputY inputAB) Q := by
  have empty : cstepCanon (par inputY inputAB) = [] := by decide +kernel
  refine ⟨by decide +kernel, empty, fun Q step => ?_⟩
  obtain ⟨Q', member, -⟩ := cstepCanon_complete step
  rw [empty] at member
  exact List.not_mem_nil member

/-- **Control (d), the syntactic frame**: the COMM is refused at every opening. -/
theorem open_refused_at_syntax (ρ : PSubst) :
    ¬ (RuleSyntax.step X ℕ E program).Admits (s := embed rowsOpen start) (commAt ρ 0 1 2 3) := by
  intro admitted
  obtain ⟨_, σ, solved⟩ := ((RuleSyntax.admits_iff _).mp admitted).2.2.2.1
  obtain ⟨-, patterns, -, -, -⟩ := comm_reads_inputs rowsOpen patY patAB demoChan demoChan pZero pZero start
    0 1 2 3 (fun _ _ => rfl) (fun _ _ => rfl) (by decide) ρ solved
  rw [psubst_of_pvars_nil σ patAB (by decide +kernel)] at patterns
  have shape : psubst σ patY = tProc (par ((σ "Y").getD (.fvar "Y")) atomA) := rfl
  rw [shape] at patterns
  have inner : par ((σ "Y").getD (.fvar "Y")) atomA = par atomA atomB := by
    simpa [tProc, patAB] using patterns
  exact absurd (MeTTaCalculus.Corrected.ResidualControls.par_injective inner).2 (by decide +kernel)

/-! ## (d'): the corrected semantics misses, the quotient frame meets -/

/-- The partner of `written_order_partner_misses`, quoting the bag in written order. -/
def writtenPartner : Pattern := pFor (tProc (par atomB atomA)) demoChan pZero

/-- The canonical listener at `0`, the partner at `1`. -/
def rowsWrittenOrder : ℕ → Pattern
  | 0 => canonicalListener
  | 1 => writtenPartner
  | _ => pZero

/-- Both rows are their own representations; the listener's quote is canonical and the partner's is not. -/
theorem written_order_facts :
    predot canonicalListener = canonicalListener ∧ predot writtenPartner = writtenPartner ∧
      bagCanon (tProc (canonicalBag (par atomA atomB))) = tProc (canonicalBag (par atomA atomB)) ∧
      bagCanon (tProc (par atomB atomA)) ≠ tProc (par atomB atomA) := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

/-- **Control (d')**: the corrected semantics misses (its executable is empty, and by completeness no step of
the corrected semantics modulo the bag laws exists), the quotient frame admits the COMM, and the syntactic
frame refuses it at every opening. -/
theorem written_order_partner_meets_at_quotient :
    cstep (par canonicalListener writtenPartner) = [] ∧
      (∀ Q, ¬ CanonicalBagStep closing (par canonicalListener writtenPartner) Q) ∧
      (RuleSyntax.step QX ℕ QE program).Admits (s := embed rowsWrittenOrder start)
        (commAtQ (renameBy rename) 0 1 2 3) ∧
      ∀ ρ : PSubst,
        ¬ (RuleSyntax.step X ℕ E program).Admits (s := embed rowsWrittenOrder start) (commAt ρ 0 1 2 3) := by
  have empty : cstepCanon (par canonicalListener writtenPartner) = [] := by decide +kernel
  refine ⟨written_order_partner_misses, fun Q step => ?_, ?_, fun ρ admitted => ?_⟩
  · obtain ⟨Q', member, -⟩ := cstepCanon_complete step
    rw [empty] at member
    exact List.not_mem_nil member
  · exact comm_admits_bag rowsWrittenOrder (tProc (canonicalBag (par atomA atomB))) (tProc (par atomB atomA))
      demoChan pZero pZero start 0 1 2 3 (fun _ _ => BagLaws.refl _) (fun _ _ => BagLaws.refl _)
      (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (σ₀ := fun _ => none) (fun _ member => absurd member List.not_mem_nil) (by decide +kernel)
      (fresh_quotient (fresh_at rowsWrittenOrder (by decide +kernel) (by decide +kernel)))
  · obtain ⟨_, σ, solved⟩ := ((RuleSyntax.admits_iff _).mp admitted).2.2.2.1
    obtain ⟨-, patterns, -, -, -⟩ := comm_reads_inputs rowsWrittenOrder (tProc (canonicalBag (par atomA atomB)))
      (tProc (par atomB atomA)) demoChan demoChan pZero pZero start 0 1 2 3 (fun _ _ => rfl) (fun _ _ => rfl)
      (by decide) ρ solved
    rw [psubst_of_pvars_nil σ _ (by decide +kernel), psubst_of_pvars_nil σ _ (by decide +kernel)] at patterns
    exact absurd patterns (by decide +kernel)

/-! ## Heating at the quotient frame -/

/-- The renaming that opens the heat rule: `A` to `a0`, `B` to `b0`. -/
def heatNames : String → String := fun v => if v = "A" then "a0" else if v = "B" then "b0" else v

/-- The heating firing of the finite program: take `0`, make `2` and `3`. -/
def heatAt (ρ : PSubst) : Firing ℕ E program PUnit.unit :=
  ⟨FiniteProgram.heatRule, FiniteProgram.heatRule_mem, PUnit.unit, ρ, ⟨[0], [], [2, 3]⟩, []⟩

/-- One input, which is not a parallel composition, at `0`. -/
def rowsInput : ℕ → Pattern
  | 0 => onAB
  | _ => pZero

/-- No knowledge; identity `0` present. -/
def startOne : Configuration Pattern ℕ := ⟨[], {0}⟩

theorem heat_information (ρ : PSubst) :
    (heatAt ρ).information X (embed rowsInput startOne) =
      [(psubst ρ (par FiniteProgram.leftPart FiniteProgram.rightPart), onAB)] ∧
    (quotientFiring (heatAt ρ)).information QX (embed rowsInput startOne) =
      [(psubst ρ (par FiniteProgram.leftPart FiniteProgram.rightPart), onAB)] := by
  constructor
  · rw [OneFrame.information_eq]
    rfl
  · rw [OneFrame.information_eq]
    rfl

theorem heat_fresh_quotient :
    (quotientFiring (heatAt (renameBy heatNames))).Fresh QX (embed rowsInput startOne) := by
  refine fresh_quotient (Comm.fresh_of_renaming (embed rowsInput startOne) (heatAt (renameBy heatNames)) heatNames
    rfl (by decide +kernel) ?_)
  intro x _ m mentions
  rcases mentions with known | known | ⟨o, present, rfl⟩
  · simp [embed, startOne] at known
  · simp [embed, startOne] at known
  · have zero : o = 0 := by simpa [embed, startOne] using present
    subst zero
    have ground : pvars (rowsInput 0) = [] := by decide +kernel
    show heatNames x ∉ pvars (rowsInput 0)
    rw [ground]
    exact List.not_mem_nil

/-- Split off `0`: `a0` is `0`, `b0` the input. -/
def splitOffZero : PSubst := fun v => if v = "a0" then some pZero else if v = "b0" then some onAB else none

/-- The other split: `a0` the input, `b0` is `0`. -/
def splitOffRest : PSubst := fun v => if v = "a0" then some onAB else if v = "b0" then some pZero else none

/-- **Heating at the quotient frame takes a row that is not a parallel composition**: `A | B` matches the
input as `0 | input`. -/
theorem heat_admitted_at_quotient :
    (RuleSyntax.step QX ℕ QE program).Admits (s := embed rowsInput startOne)
      (quotientFiring (heatAt (renameBy heatNames))) := by
  refine (RuleSyntax.admits_iff _).mpr ⟨heat_fresh_quotient, ⟨by decide, by decide, rfl, rfl, rfl, rfl⟩,
    ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
      fun query member => by simp [Selection.commit] at member⟩,
    ⟨PUnit.unit, splitOffZero, ?_⟩, fun _ member => (List.not_mem_nil member).elim,
    fun _ member => (List.not_mem_nil member).elim⟩
  rw [(heat_information _).2]
  intro e member
  rw [List.mem_singleton] at member
  subst member
  show BagLaws (psubst splitOffZero (psubst (renameBy heatNames) (par FiniteProgram.leftPart FiniteProgram.rightPart)))
    (psubst splitOffZero onAB)
  decide +kernel

/-- The syntactic frame refuses the same heating at every opening: an input is not a parallel composition. -/
theorem heat_refused_at_syntax (ρ : PSubst) :
    ¬ (RuleSyntax.step X ℕ E program).Admits (s := embed rowsInput startOne) (heatAt ρ) := by
  intro admitted
  obtain ⟨_, σ, solved⟩ := ((RuleSyntax.admits_iff _).mp admitted).2.2.2.1
  rw [(heat_information ρ).1] at solved
  have take : psubst σ (psubst ρ (par FiniteProgram.leftPart FiniteProgram.rightPart)) = psubst σ onAB :=
    solved _ List.mem_cons_self
  simp [par, pPar, psubst, onAB, pFor] at take

/-- **The made rows of a heating at the quotient frame have no determined reading**: both splits solve the
result's knowledge, and they read the first made row as `0` and as the input. The finite hosting's reading of
heating (every solution reads the made rows as the two parts) does not hold at the quotient frame. -/
theorem heat_reads_ambiguous :
    bagAction.Models splitOffZero
        ((quotientFiring (heatAt (renameBy heatNames))).result QX (embed rowsInput startOne)).knowledge ∧
      bagAction.Models splitOffRest
        ((quotientFiring (heatAt (renameBy heatNames))).result QX (embed rowsInput startOne)).knowledge ∧
      ((quotientFiring (heatAt (renameBy heatNames))).result QX (embed rowsInput startOne)).label 2 = .fvar "a0" ∧
      ¬ BagLaws (psubst splitOffZero (.fvar "a0")) (psubst splitOffRest (.fvar "a0")) := by
  have knowledge : ((quotientFiring (heatAt (renameBy heatNames))).result QX (embed rowsInput startOne)).knowledge =
      [(psubst (renameBy heatNames) (par FiniteProgram.leftPart FiniteProgram.rightPart), onAB)] :=
    (heat_information _).2
  refine ⟨?_, ?_, by decide +kernel, by decide +kernel⟩
  · rw [knowledge]
    intro e member
    rw [List.mem_singleton] at member
    subst member
    show BagLaws (psubst splitOffZero (psubst (renameBy heatNames) (par FiniteProgram.leftPart FiniteProgram.rightPart)))
      (psubst splitOffZero onAB)
    decide +kernel
  · rw [knowledge]
    intro e member
    rw [List.mem_singleton] at member
    subst member
    show BagLaws (psubst splitOffRest (psubst (renameBy heatNames) (par FiniteProgram.leftPart FiniteProgram.rightPart)))
      (psubst splitOffRest onAB)
    decide +kernel

#print axioms heat_admitted_at_quotient
#print axioms heat_refused_at_syntax
#print axioms heat_reads_ambiguous
#print axioms example_comm_bag
#print axioms names_admitted_at_quotient
#print axioms names_refused_at_syntax
#print axioms open_facts
#print axioms open_admitted_at_quotient
#print axioms open_refused_by_source
#print axioms open_refused_at_syntax
#print axioms written_order_facts
#print axioms written_order_partner_meets_at_quotient

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.ReflQuotient.Controls
