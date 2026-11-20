import Mettapedia.GSLT.Contracts.PaperRhoAdequacy

/-!
# Controls for rho step adequacy

Positive controls replay the paper's own examples through the adequacy
theorems. Negative controls check that the bridge keeps the paper's
distinctions, and the separations show that each hypothesis of the
adequacy theorems is needed:

* a step from the plain encoding of a redex can fail, because our step
  relation reads the parallel bag as written and has no rule for the
  paper's equations; from the canonical form it never fails;
* a step from an open plain encoding can have no paper counterpart,
  because the paper's COMM rule admits only closed communication;
* exact substitution fails outside the resolved fiber.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Contracts.PaperRho.AdequacyControls

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution
open Mettapedia.OSLF.MeTTaIL.ReflectiveCoherent (QuotesResolved QuotesResolvedList)
open Mettapedia.GSLT.Contracts.PaperRho.PatternBoundary
open Mettapedia.GSLT.Contracts.PaperRho.Adequacy
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedContextualStep (RhoStep)
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.CanonicalRepresentativeStep
  (rhoStepAt_comm_at CanonicalStep)
open Separation (base wrapped)

/-! ## Positive controls -/

/-- The output sugar of p. 58 steps in our calculus. -/
theorem output_sugar_steps {channel z : Name} {body : Process}
    (channelScoped : ScopedName 0 channel) (zScoped : ScopedName 0 z)
    (bodyScoped : ScopedProcess 1 body) :
    ∃ r, RhoStep (canonicalForm (.par (.send channel (.drop z)) (.receive channel body))) r ∧
      canonicalize rhoReflectivePresentation r = canonicalForm (rename z 0 body) :=
  rhoStep_of_reduction (output_sugar_reduces channelScoped zScoped bodyScoped)

private theorem dropBound_resolved :
    QuotesResolved rhoReflectivePresentation (encodeProcess (.drop (.bound 0))) := by
  simp [QuotesResolved, QuotesResolvedList, encodeProcess, encodeName, rhoReflectivePresentation]

private theorem zero_resolved : QuotesResolved rhoReflectivePresentation (encodeProcess .zero) := by
  simp [QuotesResolved, QuotesResolvedList, encodeProcess]

/-- The wrapped alias communicates in our calculus straight from the plain
encoding: the matcher compares the two spellings of the channel by the
paper's name equivalence, and the step lands exactly on the paper's
contractum. -/
theorem alias_steps_exactly :
    RhoStep (encodeProcess (.par (.receive base (.drop (.bound 0))) (.send wrapped .zero)))
      (.collection .hashBag [encodeProcess .zero] none) :=
  rhoStep_encode_comm_exact (.quote_drop base) dropBound_resolved zero_resolved

/-- The paper's `alias_communicates`, replayed through both directions. -/
theorem alias_communicates_replayed :
    (∃ r, RhoStep (canonicalForm
        (.par (.send wrapped .zero) (.receive base (.drop (.bound 0))))) r ∧
      canonicalize rhoReflectivePresentation r = canonicalForm .zero) ∧
    ∀ r, RhoStep (encodeProcess
        (.par (.receive base (.drop (.bound 0))) (.send wrapped .zero))) r →
      ∃ q, Reduction (.par (.receive base (.drop (.bound 0))) (.send wrapped .zero)) q ∧
        canonicalize rhoReflectivePresentation r = canonicalForm q :=
  ⟨rhoStep_of_reduction (Reduces.reduction Controls.alias_communicates),
    fun _ step => rhoStep_encodeProcess_reduction
      (.par (.receive (.literal .zero) (.drop (.bound (by decide))))
        (.send (.literal (.drop (.literal .zero))) .zero)) step⟩

/-- The paper's `whole_name_under_unit_receives_payload`, replayed. -/
theorem whole_name_under_unit_replayed :
    ∃ r, RhoStep (canonicalForm (.par (.send base (.send base .zero))
        (.receive base (.drop (.quote (.par (.drop (.bound 0)) .zero)))))) r ∧
      canonicalize rhoReflectivePresentation r = canonicalForm (.send base .zero) :=
  rhoStep_of_reduction (Reduces.reduction Controls.whole_name_under_unit_receives_payload)

/-- The same receiver, from the plain encoding: its binder is spelled through
the parallel unit, outside the resolved fiber, and the compiled COMM step
still runs the received code at it. -/
theorem whole_name_under_unit_steps :
    RhoStep (encodeProcess (.par (.receive base (.drop (.quote (.par (.drop (.bound 0)) .zero))))
        (.send base (.send base .zero))))
      (.collection .hashBag [encodeProcess (.send base .zero)] none) := by
  have step : RhoStep _ _ := ⟨1, rhoStepAt_comm_at
    (elements := [encodeProcess (.receive base (.drop (.quote (.par (.drop (.bound 0)) .zero)))),
      encodeProcess (.send base (.send base .zero))]) (termRest := none)
    (inputIndex := 0) (outputIndex := 0) (by simp) (by simp) rfl rfl rfl⟩
  have landed : substituteReflective rhoReflectivePresentation 0
      (.apply "NQuote" [normalizeReflective rhoReflectivePresentation
        (encodeProcess (.send base .zero))])
      (encodeProcess (.drop (.quote (.par (.drop (.bound 0)) .zero)))) =
      encodeProcess (.send base .zero) := by
    decide +kernel
  rw [landed] at step
  exact step

/-! ## Negative controls -/

/-- A second parallel component prevents a binder hit in our substitution too. -/
theorem another_component_misses :
    matchesBinder rhoReflectivePresentation 0 (canonicalize rhoReflectivePresentation
      (encodeName (.quote (.par (.drop (.bound 0)) (.drop (.bound 0)))))) = false := by
  rw [Bool.eq_false_iff]
  intro hit
  rw [matchesBinder_canonicalize_encodeName, ← nameEquivalence_bound_iff] at hit
  exact StructuralControls.another_component_prevents_hit hit

/-- An output and an input never have the same canonical form. -/
theorem output_not_input_canonical (x y : Name) (p q : Process) :
    canonicalForm (.send x p) ≠ canonicalForm (.receive y q) := fun same =>
  StructuralControls.output_not_input x y p q ((canonicalize_encodeProcess_eq_iff _ _).mp same)

/-- The bridge is not complete for the finer reading `ProcEq`: our canonical
equality identifies the wrapped and the plain output subject, as the paper's
structural congruence does, while `ProcEq` separates them. -/
theorem canonical_equality_not_procEq :
    canonicalForm (.send wrapped .zero) = canonicalForm (.send base .zero) ∧
      ¬ ProcEq (.send wrapped .zero) (.send base .zero) :=
  ⟨(canonicalize_encodeProcess_eq_iff _ _).mpr StructuralControls.wrapped_output_congruent,
    process_equations_not_reflected.2.2.2⟩

theorem bridge_not_procEq_complete :
    ¬ ∀ p q : Process, canonicalForm p = canonicalForm q → ProcEq p q := fun complete =>
  canonical_equality_not_procEq.2 (complete _ _ canonical_equality_not_procEq.1)

/-! ## Separation: plain encodings do not reach the paper's equations -/

/-- `(base!(0) | 0) | base(y).0`: the redex is split across two parallel levels. -/
def nestedRedex : Process := .par (.par (.send base .zero) .zero) (.receive base .zero)

theorem nestedRedex_closed : ScopedProcess 0 nestedRedex :=
  .par (.par (.send (.literal .zero) .zero) .zero) (.receive (.literal .zero) .zero)

theorem nestedRedex_reduces : Reduction nestedRedex .zero :=
  .equiv (.par (.unit _) (.refl _))
    (.comm (.literal .zero) (.literal .zero) .zero .zero (.refl _) .zero) (.refl _)

/-- The plain encoding of `nestedRedex` is the calculus-level witness
`CanonicalRepresentativeStep.nestedRedex`. -/
theorem encodeProcess_nestedRedex :
    encodeProcess nestedRedex =
      Mettapedia.Languages.ProcessCalculi.RhoCalculus.CanonicalRepresentativeStep.nestedRedex :=
  rfl

/-- Our step relation has no step from the plain encoding of `nestedRedex`. -/
theorem nestedRedex_plain_encoding_stuck (target : Pattern) :
    ¬ RhoStep (encodeProcess nestedRedex) target := by
  rw [encodeProcess_nestedRedex]
  exact Mettapedia.Languages.ProcessCalculi.RhoCalculus.CanonicalRepresentativeStep.nestedRedex_stuck
    target

/-- **Separation.** Step adequacy from plain encodings fails: a closed process
reduces in the paper while its plain encoding has no step in our calculus. The
responsible law is the paper's parallel unit `P | 0 ≡ P`, used through EQUIV;
our step relation matches a parallel bag as written, so it needs the canonical
form, which applies that law (`reduction_iff_rhoStep`). -/
theorem plain_encoding_not_complete :
    ∃ p q, ScopedProcess 0 p ∧ Reduction p q ∧ ∀ r, ¬ RhoStep (encodeProcess p) r :=
  ⟨nestedRedex, .zero, nestedRedex_closed, nestedRedex_reduces,
    nestedRedex_plain_encoding_stuck⟩

/-- From the canonical form, the same redex steps. -/
theorem nestedRedex_canonical_steps :
    ∃ r, RhoStep (canonicalForm nestedRedex) r ∧
      canonicalize rhoReflectivePresentation r = canonicalForm .zero :=
  rhoStep_of_reduction nestedRedex_reduces

/-! ## Separation: open communication -/

/-- `y(z).0 | y!(0)` on a bound, unscoped channel. -/
def openRedex : Process := .par (.receive (.bound 0) .zero) (.send (.bound 0) .zero)

/-- Our calculus communicates on the open channel. -/
theorem openRedex_steps :
    RhoStep (encodeProcess openRedex) (.collection .hashBag [encodeProcess .zero] none) :=
  rhoStep_encode_comm_exact (.refl (.bound 0)) zero_resolved zero_resolved

/-- The paper does not: COMM admits only closed communication, and no
congruent spelling of the redex has a closed channel. -/
theorem openRedex_irreducible (q : Process) : ¬ Reduction openRedex q := by
  intro step
  obtain ⟨offered, waiting, payload, body, rest, offeredScoped, _, _, _, _, before, _⟩ :=
    redex_of_reduction step
  have members := parallelMembers_perm_of_canonicalForm_eq (p := openRedex)
    (by simp [openRedex, parallelMembers]) ((canonicalize_encodeProcess_eq_iff _ _).mpr before)
  have offeredMember : canonicalForm (.send offered payload) ∈
      (parallelMembers openRedex).map canonicalForm :=
    members.symm.subset (by simp [parallelMembers])
  simp only [openRedex, parallelMembers] at offeredMember
  simp [canonicalForm, canonicalize_send, canonicalize_receive] at offeredMember
  obtain ⟨channel, -⟩ := offeredMember
  have agrees := (canonicalize_encodeName_eq_iff _ _).mp channel
  have bound := (agrees.scoped_iff 0).mp offeredScoped
  cases bound with
  | bound below => exact absurd below (by decide)

/-- **Separation.** Steps from an open plain encoding need not be paper
reductions. The responsible rule is the paper's COMM, whose premises admit only
closed channels, payloads and bodies; our step relation has no scope premise.
This is why the converse direction assumes a closed source. -/
theorem open_step_not_sound :
    ∃ p r, RhoStep (encodeProcess p) r ∧ ∀ q, ¬ Reduction p q :=
  ⟨openRedex, _, openRedex_steps, openRedex_irreducible⟩

/-! ## Separation: exact substitution off the resolved fiber -/

/-- `@(*@0 | 0)`: a closed literal quotation that exposes a drop through the
parallel unit. -/
def hiddenAlias : Name := .quote (.par (.drop base) .zero)

/-- `@(*@0 | 0)!(0)`, a closed body under the binder that never mentions it. -/
def hiddenAliasBody : Process := .send hiddenAlias .zero

theorem hiddenAliasBody_scoped : ScopedProcess 1 hiddenAliasBody :=
  .send (.literal (.par (.drop (.literal .zero)) .zero)) .zero

/-- **Separation.** Outside the resolved fiber the compiled substitution is not
the paper's substitution spelling for spelling, although the two have the same
canonical form. The responsible laws are the parallel unit `P | 0 ≡ P` and
quote-drop `@(*x) ≡N x`: the compiled substitution normalizes the channel by
them, the paper's substitution only compares names by them. -/
theorem substitution_not_exact_off_fiber :
    substituteReflective rhoReflectivePresentation 0
        (.apply "NQuote" [normalizeReflective rhoReflectivePresentation (encodeProcess .zero)])
        (encodeProcess hiddenAliasBody) ≠
      encodeProcess (substitute .zero 0 hiddenAliasBody) ∧
    canonicalize rhoReflectivePresentation
        (substituteReflective rhoReflectivePresentation 0
          (.apply "NQuote" [normalizeReflective rhoReflectivePresentation (encodeProcess .zero)])
          (encodeProcess hiddenAliasBody)) =
      canonicalForm (substitute .zero 0 hiddenAliasBody) :=
  ⟨by decide +kernel, canonicalize_substituteReflective_encode _ _ 0⟩

/-- The body is outside the resolved fiber, as it must be. -/
theorem hiddenAliasBody_not_resolved :
    ¬ QuotesResolved rhoReflectivePresentation (encodeProcess hiddenAliasBody) := fun resolved =>
  substitution_not_exact_off_fiber.1
    (substituteReflective_encode_exact _ _ 0 resolved zero_resolved)

/-! ## Many steps: the reflexive case needs the congruence -/

private theorem par_zero_irreducible (r : Process) : ¬ Reduction (.par .zero .zero) r := by
  intro step
  obtain ⟨offered, waiting, payload, body, rest, _, _, _, _, _, before, _⟩ := redex_of_reduction step
  have members := parallelMembers_perm_of_canonicalForm_eq
    (p := .par (.par (.send offered payload) (.receive waiting body)) rest)
    (by simp [parallelMembers]) ((canonicalize_encodeProcess_eq_iff _ _).mpr before.symm)
  simpa [parallelMembers] using members.length_eq

/-- **Negative control.** Many-step adequacy cannot be stated as an equivalence
between `ReflTransGen Reduction p q` and reachability of `canonicalForm q`: the
closed process `0 | 0` has the canonical form of `0` and no reduction, so its
zero-step path reaches `canonicalForm 0` while the paper's reflexive closure does
not reach `0`. `reflTransGen_canonicalStep_iff_congruent` keeps the congruence. -/
theorem reflTransGen_needs_congruence :
    ScopedProcess 0 (.par .zero .zero) ∧
      Relation.ReflTransGen CanonicalStep (canonicalForm (.par .zero .zero)) (canonicalForm .zero) ∧
      ¬ Relation.ReflTransGen Reduction (.par .zero .zero) .zero := by
  refine ⟨.par .zero .zero, ?_, ?_⟩
  · have same : canonicalForm (.par .zero .zero) = canonicalForm .zero :=
      Congruence.canonicalize_eq (.unit .zero)
    rw [same]
  · intro steps
    rcases Relation.ReflTransGen.cases_head steps with same | ⟨r, step, _⟩
    · cases same
    · exact par_zero_irreducible r step

/-- **Positive control.** One paper reduction followed by none: the transitive
closures agree on `nestedRedex`, whose plain encoding is stuck. -/
theorem nestedRedex_transGen :
    Relation.TransGen CanonicalStep (canonicalForm nestedRedex) (canonicalForm .zero) :=
  (transGen_reduction_iff_canonicalStep nestedRedex_closed).mp (.single nestedRedex_reduces)

#print axioms output_sugar_steps
#print axioms alias_steps_exactly
#print axioms alias_communicates_replayed
#print axioms whole_name_under_unit_replayed
#print axioms whole_name_under_unit_steps
#print axioms another_component_misses
#print axioms output_not_input_canonical
#print axioms canonical_equality_not_procEq
#print axioms bridge_not_procEq_complete
#print axioms plain_encoding_not_complete
#print axioms nestedRedex_canonical_steps
#print axioms open_step_not_sound
#print axioms substitution_not_exact_off_fiber
#print axioms hiddenAliasBody_not_resolved
#print axioms reflTransGen_needs_congruence
#print axioms nestedRedex_transGen

end Mettapedia.GSLT.Contracts.PaperRho.AdequacyControls
