import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.ReflNameTransport
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.ReflQuotientControls

/-!
# Where the name frame, the corrected semantics and `QX` agree, and where they differ

The finite program of `FiniteComm` runs at the name frame `QN` (`ReflNameTransport`). Its controls, with the
same program, openings and rows as `ReflQuotient.Controls`.

* **The transport applies** (`example_comm_name`): the manuscript's example meets the named hypothesis and
  fires at `QN`.
* **Positive** (`names_separate_name_frame`): the COMM through `@(a | b)` and `@(b | a)`, names equal only
  modulo the bag laws, is admitted at `QN` and refused at the syntactic frame at every opening.
* **(d′) still separates** (`written_order_partner_meets_at_name_frame`): the pattern quote `MTermProc` is a
  quote, so the partner quoting `(b | a)` meets the canonical listener at `QN`, while the corrected semantics
  misses it.
* **(d) still separates** (`open_meets_at_name_frame`): a pattern quoting a bag with an unknown meets at `QN`
  (inside the quote, the bag laws), and the corrected semantics refuses.
* **`QN` is not `QX`** (`spine_patterns_separate`): patterns that are unquoted parallel bags, `a | b` and
  `b | a`, meet at `QX` and not at `QN` (at any opening), and the corrected semantics, which compares them as
  written, refuses too: at the spine `QN` agrees with the corrected semantics and `QX` does not.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.ReflNames.Controls

open Mettapedia.OSLF.MeTTaIL.Syntax (Pattern)
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus (pFor par pZero nQuote applyDot tProc demoChan pPar)
open MeTTaOperationsComm (psubst pvars PSubst psubst_of_pvars_nil)
open FiniteProgram (predot commAt program)
open FiniteProgram.Controls (fresh_at rename rows example_apart)
open Comm (X E renameBy)
open Comm.Controls (start zeroTerm y unifier unifier_groundPrincipal)
open OneFrame (embed)
open MeTTaCalculus.Corrected.BagControls (atomA atomB)
open MeTTaCalculus.Corrected (canonicalBag cstep cstepCanon cstepCanon_complete CanonicalBagStep closing)
open MeTTaCalculus.Corrected.ReflectionControls (canonicalListener written_order_partner_misses)
open ReflQuotient (BagLaws QX QE commAtQ fresh_quotient)
open ReflQuotient.Controls (yToZero chanAB onAB onBA rowsNames names_refused_at_syntax patY patAB rowsOpen yToB
  open_refused_by_source writtenPartner rowsWrittenOrder)

/-! ## The transport applies -/

/-- **The manuscript's example fires at the name frame**, through `comm_one_firing_name`: its patterns have no
parallel bag and are canonical. Every solution reads the receiver's made row as the representation of
`@((0))`, modulo the name laws. -/
theorem example_comm_name :
    (RuleSyntax.step QN ℕ QNE program).Admits (s := embed rows start) (commAtN (renameBy rename) 0 1 2 3) ∧
      ∀ σ : PSubst,
        nameAction.Models σ ((commAtN (renameBy rename) 0 1 2 3).result QN (embed rows start)).knowledge →
          NameLaws (psubst σ (((commAtN (renameBy rename) 0 1 2 3).result QN (embed rows start)).label 3))
            (psubst σ (predot (applyDot unifier y))) := by
  obtain ⟨admitted, -, -, reads⟩ := comm_one_firing_name rows zeroTerm y demoChan pZero y unifier
    unifier_groundPrincipal example_apart (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    start 0 1 2 3 (fun _ _ => NameLaws.refl _) (fun _ _ => NameLaws.refl _)
    (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    ⟨yToZero, fun _ member => absurd member List.not_mem_nil, by decide +kernel⟩
    (fresh_name (fresh_at rows (by decide +kernel) (by decide +kernel)))
  exact ⟨admitted, fun σ solved => (reads σ solved).2⟩

/-! ## Positive: a COMM through names equal modulo the bag laws -/

theorem names_related_by_name_laws : NameLaws onBA onAB := by decide +kernel

/-- **Positive control**: the COMM through `@(a | b)` and `@(b | a)` is admitted at the name frame, and refused
at the syntactic frame at every opening. -/
theorem names_separate_name_frame :
    (RuleSyntax.step QN ℕ QNE program).Admits (s := embed rowsNames start) (commAtN (renameBy rename) 0 1 2 3) ∧
      ∀ ρ : PSubst, ¬ (RuleSyntax.step X ℕ E program).Admits (s := embed rowsNames start) (commAt ρ 0 1 2 3) :=
  ⟨comm_admits_name rowsNames pZero pZero chanAB pZero pZero start 0 1 2 3
    (fun _ _ => NameLaws.refl _) (fun σ _ => nameLaws_psubst σ names_related_by_name_laws)
    (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (σ₀ := fun _ => none) (fun _ member => absurd member List.not_mem_nil) (NameLaws.refl _)
    (fresh_name (fresh_at rowsNames (by decide +kernel) (by decide +kernel))), names_refused_at_syntax⟩

/-! ## (d′) and (d) at the name frame -/

/-- **Control (d′) at the name frame**: the corrected semantics misses the written-order partner (its executable
is empty, and by completeness no step of the corrected semantics modulo the bag laws exists), and the name
frame admits the COMM: the listener's and the partner's patterns are quotes. -/
theorem written_order_partner_meets_at_name_frame :
    cstep (par canonicalListener writtenPartner) = [] ∧
      (∀ Q, ¬ CanonicalBagStep closing (par canonicalListener writtenPartner) Q) ∧
      (RuleSyntax.step QN ℕ QNE program).Admits (s := embed rowsWrittenOrder start)
        (commAtN (renameBy rename) 0 1 2 3) := by
  have empty : cstepCanon (par canonicalListener writtenPartner) = [] := by decide +kernel
  refine ⟨written_order_partner_misses, fun Q step => ?_, ?_⟩
  · obtain ⟨Q', member, -⟩ := cstepCanon_complete step
    rw [empty] at member
    exact List.not_mem_nil member
  · exact comm_admits_name rowsWrittenOrder (tProc (canonicalBag (par atomA atomB))) (tProc (par atomB atomA))
      demoChan pZero pZero start 0 1 2 3 (fun _ _ => NameLaws.refl _) (fun _ _ => NameLaws.refl _)
      (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (σ₀ := fun _ => none) (fun _ member => absurd member List.not_mem_nil) (by decide +kernel)
      (fresh_name (fresh_at rowsWrittenOrder (by decide +kernel) (by decide +kernel)))

/-- **Control (d) at the name frame**: with the name pattern `((Y | a))` against `((a | b))`, the name frame
admits the COMM (reading `Y` as `b` inside the quote), and the corrected semantics refuses. -/
theorem open_meets_at_name_frame :
    (RuleSyntax.step QN ℕ QNE program).Admits (s := embed rowsOpen start) (commAtN (renameBy rename) 0 1 2 3) ∧
      cstep (par (pFor patY demoChan pZero) (pFor patAB demoChan pZero)) = [] ∧
      ∀ Q, ¬ CanonicalBagStep closing (par (pFor patY demoChan pZero) (pFor patAB demoChan pZero)) Q :=
  ⟨comm_admits_name rowsOpen patY patAB demoChan pZero pZero start 0 1 2 3
    (fun _ _ => NameLaws.refl _) (fun _ _ => NameLaws.refl _)
    (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (σ₀ := yToB) (fun _ member => absurd member List.not_mem_nil) (by decide +kernel)
    (fresh_name (fresh_at rowsOpen (by decide +kernel) (by decide +kernel))),
    open_refused_by_source.1, open_refused_by_source.2.2⟩

/-! ## The name frame is not `QX`: patterns that are unquoted bags -/

/-- An input whose pattern is the unquoted bag `a | b`, and one with `b | a`. -/
def inputSpineAB : Pattern := pFor (par atomA atomB) demoChan pZero
def inputSpineBA : Pattern := pFor (par atomB atomA) demoChan pZero

/-- The two inputs at `0` and `1`. -/
def rowsSpine : ℕ → Pattern
  | 0 => inputSpineAB
  | 1 => inputSpineBA
  | _ => pZero

/-- **At the spine the name frame agrees with the corrected semantics, and `QX` does not**: the COMM between
inputs with the patterns `a | b` and `b | a` is admitted at `QX`, refused at `QN` at every opening, and the
corrected semantics' executable steps from that redex are empty. -/
theorem spine_patterns_separate :
    (RuleSyntax.step QX ℕ QE program).Admits (s := embed rowsSpine start) (commAtQ (renameBy rename) 0 1 2 3) ∧
      (∀ ρ : PSubst, ¬ (RuleSyntax.step QN ℕ QNE program).Admits (s := embed rowsSpine start) (commAtN ρ 0 1 2 3)) ∧
      cstep (par inputSpineAB inputSpineBA) = [] := by
  refine ⟨ReflQuotient.comm_admits_bag rowsSpine (par atomA atomB) (par atomB atomA) demoChan pZero pZero start
      0 1 2 3 (fun _ _ => BagLaws.refl _) (fun _ _ => BagLaws.refl _)
      (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (σ₀ := fun _ => none) (fun _ member => absurd member List.not_mem_nil) (by decide +kernel)
      (fresh_quotient (fresh_at rowsSpine (by decide +kernel) (by decide +kernel))), fun ρ admitted => ?_,
    by decide +kernel⟩
  obtain ⟨_, σ, solved⟩ := ((RuleSyntax.admits_iff _).mp admitted).2.2.2.1
  obtain ⟨-, patterns, -, -⟩ := comm_reads_name rowsSpine (par atomA atomB) (par atomB atomA) demoChan demoChan
    pZero pZero start 0 1 2 3 (fun _ _ => NameLaws.refl _) (fun _ _ => NameLaws.refl _) (by decide) ρ solved
  rw [psubst_of_pvars_nil σ (par atomA atomB) (by decide +kernel),
    psubst_of_pvars_nil σ (par atomB atomA) (by decide +kernel)] at patterns
  exact spine_as_written patterns

#print axioms example_comm_name
#print axioms names_related_by_name_laws
#print axioms names_separate_name_frame
#print axioms written_order_partner_meets_at_name_frame
#print axioms open_meets_at_name_frame
#print axioms spine_patterns_separate

/-! ## Alpha, name and top-level bag equalities have different boundaries -/

namespace Binding
open Mettapedia.OSLF.MeTTaIL.Syntax (Pattern)
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus
open MeTTaCalculus.Corrected (AlphaEq BagEq canonicalBag)
open MeTTaOperationsComm (psubst PSubst)

def first : Pattern := pFor (.fvar "x") demoChan (.fvar "x")
def second : Pattern := pFor (.fvar "y") demoChan (.fvar "y")
def specialize : PSubst := fun name => if name = "x" then some pZero else none

theorem guards_are_alpha_equivalent : AlphaEq first second := by decide +kernel

theorem structural_substitution_does_not_preserve_guard_alpha :
    ¬ AlphaEq (psubst specialize first) (psubst specialize second) := by decide +kernel

theorem guard_bag_equality_iff_alpha (t channel body u otherChannel otherBody : Pattern) :
    BagEq (pFor t channel body) (pFor u otherChannel otherBody) ↔
      AlphaEq (pFor t channel body) (pFor u otherChannel otherBody) := by
  change List.Perm (MeTTaCalculus.Corrected.components (MeTTaCalculus.Corrected.close _))
    (MeTTaCalculus.Corrected.components (MeTTaCalculus.Corrected.close _)) ↔ _
  rw [MeTTaCalculus.Corrected.components_close_pFor,
    MeTTaCalculus.Corrected.components_close_pFor]
  constructor
  · intro same
    exact List.singleton_inj.mp (List.perm_singleton.mp same)
  · intro same
    rw [show MeTTaCalculus.Corrected.close (pFor t channel body) =
      MeTTaCalculus.Corrected.close (pFor u otherChannel otherBody) from same]

theorem structural_substitution_does_not_preserve_top_level_bag_equality :
    ¬ BagEq (psubst specialize first) (psubst specialize second) := by
  intro same
  exact structural_substitution_does_not_preserve_guard_alpha
    ((guard_bag_equality_iff_alpha _ _ _ _ _ _).mp same)

theorem no_guard_alpha_frame_with_the_raw_action :
    ¬ ∃ frames : Interface.Frames (fun _ : PUnit => Pattern) (fun _ _ => PSubst),
      (∀ first second, frames.E (a := PUnit.unit) first second ↔ AlphaEq first second) ∧
      (∀ substitution term, frames.act (a := PUnit.unit) (b := PUnit.unit) substitution term =
        psubst substitution term) := by
  rintro ⟨frames, equality, action⟩
  have same := frames.preserves (a := PUnit.unit) (b := PUnit.unit) specialize
    ((equality first second).mpr guards_are_alpha_equivalent)
  rw [action, action] at same
  exact structural_substitution_does_not_preserve_guard_alpha ((equality _ _).mp same)

theorem no_canonical_bag_frame_with_the_raw_action :
    ¬ ∃ frames : Interface.Frames (fun _ : PUnit => Pattern) (fun _ _ => PSubst),
      (∀ first second, frames.E (a := PUnit.unit) first second ↔ canonicalBag first = canonicalBag second) ∧
      (∀ substitution term, frames.act (a := PUnit.unit) (b := PUnit.unit) substitution term =
        psubst substitution term) := by
  rintro ⟨frames, equality, action⟩
  have related : BagEq first second := BagEq.of_alphaEq guards_are_alpha_equivalent
  have same := frames.preserves (a := PUnit.unit) (b := PUnit.unit) specialize
    ((equality first second).mpr (MeTTaCalculus.Corrected.canonicalBag_eq_of_bagEq related))
  rw [action, action] at same
  exact structural_substitution_does_not_preserve_top_level_bag_equality
    ((MeTTaCalculus.Corrected.bagEq_iff_canonicalBag_eq _ _).mpr ((equality _ _).mp same))

theorem canonical_bag_identifies_the_renamed_guards : canonicalBag first = canonicalBag second :=
  MeTTaCalculus.Corrected.canonicalBag_eq_of_bagEq (BagEq.of_alphaEq guards_are_alpha_equivalent)

theorem quoted_bag_equality_does_not_identify_the_renamed_guards :
    ¬ ReflNames.NameLaws first second := by decide +kernel

open MeTTaCalculus.Corrected.BagControls (atomA atomB)

def quotedFirst : Pattern := pFor (tProc (par atomA atomB)) demoChan pZero
def quotedSecond : Pattern := pFor (tProc (par atomB atomA)) demoChan pZero

theorem quoted_bag_equality_identifies_the_permuted_names :
    ReflNames.NameLaws quotedFirst quotedSecond := by
  apply ReflNames.nameLaws_apply "MFor"
  exact .cons (ReflNames.NameLaws.of_rewrite
    (.quote (Or.inr rfl) (ReflQuotient.bagLaws_par_comm atomA atomB)))
    (.cons (ReflNames.NameLaws.refl _) (.cons (ReflNames.NameLaws.refl _) .nil))

theorem top_level_bag_equality_does_not_identify_the_permuted_names :
    ¬ BagEq quotedFirst quotedSecond := by
  intro same
  have components := (MeTTaCalculus.Corrected.bagEq_iff _ _).mp same
  change List.Perm [_] [_] at components
  have equal := List.singleton_inj.mp (List.perm_singleton.mp components)
  exact (show MeTTaCalculus.Corrected.close quotedFirst ≠
    MeTTaCalculus.Corrected.close quotedSecond from by decide +kernel) equal

theorem name_and_top_level_bag_equalities_are_incomparable :
    (¬ ∀ first second, ReflNames.NameLaws first second → BagEq first second) ∧
      (¬ ∀ first second, BagEq first second → ReflNames.NameLaws first second) := by
  constructor
  · intro preserves
    exact top_level_bag_equality_does_not_identify_the_permuted_names
      (preserves _ _ quoted_bag_equality_identifies_the_permuted_names)
  · intro preserves
    exact quoted_bag_equality_does_not_identify_the_renamed_guards
      (preserves _ _ (BagEq.of_alphaEq guards_are_alpha_equivalent))

#print axioms guards_are_alpha_equivalent
#print axioms no_guard_alpha_frame_with_the_raw_action
#print axioms no_canonical_bag_frame_with_the_raw_action
#print axioms canonical_bag_identifies_the_renamed_guards
#print axioms name_and_top_level_bag_equalities_are_incomparable

end Binding

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.ReflNames.Controls
