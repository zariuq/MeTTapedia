import Mettapedia.Logic.TheoryModel.EpsilonHosting
import Mettapedia.Logic.TheoryModel.IdentityProofs
import Mettapedia.Logic.TheoryModel.InstitutionBridge

/-!
# ε-hosting: comorphisms and controls

**Comorphisms.** A comorphism's model reduct preserves and reflects every
tested disagreement once source sentences are tested through their
translations (`withinTest_reduct_iff`): reducts are isometries of the testing
pseudometric. A leak through a comorphism is therefore never a distortion of
distances; it is a coverage defect, which ε-hosting measures. Coverage up to
isomorphism with isomorphism-invariant satisfaction gives zero hosting for
every weighting and theory (`zeroHosts_of_coversModelsUpToIso`).

**Controls.**
* The collapsing comorphism hosts `{false}` up to the weight of `true` and no
  better; the representative comorphism hosts every theory with error zero.
* Identity proofs, testing `uip` with weight `w`: the thin universe hosts the
  groupoid laws up to `w` and no better (the two-proof structure refutes the
  leaked `uip`); adding the two-proof structure brings the tested error to
  zero, while `loopComm`, which is not tested, still leaks.
* Testing `uip` and `connected`: the ladder universe with the dihedral
  structure is faithful, but it does not host with error below either weight,
  because no member refutes both sentences while the univalent structure
  does. Faithful hosting finds a countermodel for each non-consequence;
  ε-hosting asks for a twin of each model. Adding the univalent structure
  brings the error to zero.

The zero-hosting results for the ladder decide `uip` and `connected` for an
arbitrary structure; they use `Classical.em` deliberately.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.TheoryModel.EpsilonHostingControls

open Set CategoryTheory
open Mettapedia.Logic (Institution)
open Mettapedia.Logic.TheoryModel.InstitutionBridge

universe u uSignature uSignatureHom uSentence uModel uModelHom

/-! ## Comorphisms: reducts are isometries of testing pseudometrics -/

section Comorphisms

variable {SourceSignature TargetSignature : Type uSignature}
  [Category.{uSignatureHom} SourceSignature] [Category.{uSignatureHom} TargetSignature]
  {source : Institution.{uSignature, uSignatureHom, uSentence, uModel, uModelHom} SourceSignature}
  {target : Institution.{uSignature, uSignatureHom, uSentence, uModel, uModelHom} TargetSignature}
  (translation : Institution.Comorphism source target) (signature : SourceSignature)

/-- **Reducts are isometries of the testing pseudometric**: two target models
are within `ε` on the translated tested sentences exactly when their reducts
are within `ε` on the tested sentences. -/
theorem withinTest_reduct_iff (ν : SentenceWeighting (source.sentence.obj signature))
    (N N' : target.model.obj (Opposite.op (translation.mapSignature.obj signature))) (ε : ℚ) :
    WithinTest (source.satisfies signature) ν (modelReduct translation signature N)
        (modelReduct translation signature N') ε ↔
      WithinTest (fun M φ => target.satisfies (translation.mapSignature.obj signature) M
        (translation.mapSentence.app signature φ)) ν N N' ε := by
  constructor
  · rintro ⟨D, inside, agree, small⟩
    exact ⟨D, inside, fun φ member outside =>
      (translation.satisfaction_condition signature N φ).trans
        ((agree φ member outside).trans (translation.satisfaction_condition signature N' φ).symm),
      small⟩
  · rintro ⟨D, inside, agree, small⟩
    exact ⟨D, inside, fun φ member outside =>
      (translation.satisfaction_condition signature N φ).symm.trans
        ((agree φ member outside).trans (translation.satisfaction_condition signature N' φ)),
      small⟩

/-- **Coverage up to isomorphism gives zero hosting** for every weighting and
every theory. -/
theorem zeroHosts_of_coversModelsUpToIso (invariant : source.SatisfactionIsoInvariant)
    (coverage : translation.CoversModelsUpToIso)
    (ν : SentenceWeighting (source.sentence.obj signature))
    (T : Set (source.sentence.obj signature)) :
    EpsHosts (source.satisfies signature) ν (reductUniverse translation signature) T 0 :=
  zeroHosts_of_twins (fun sourceModel => by
    obtain ⟨targetModel, ⟨isomorphism⟩⟩ := coverage signature sourceModel
    exact ⟨modelReduct translation signature targetModel, ⟨targetModel, rfl⟩,
      fun φ => invariant signature _ _ isomorphism φ⟩) T

end Comorphisms

/-! ## The collapsing and the representative comorphism -/

section Collapse

open Mettapedia.Logic.InstitutionCanary
open Mettapedia.Logic.TheoryModel.InstitutionBridge.Control

instance : DecidableEq BoolSentence := inferInstanceAs (DecidableEq Bool)

/-- Test only the source sentence `true`, with weight `w`. -/
def trueWeighting (w : ℚ) (positive : 0 < w) : SentenceWeighting BoolSentence where
  support := {true}
  weight _ := w
  weight_pos _ _ := positive

/-- The source model `{false}` is a model of `{false}` refuting `true`. -/
theorem falseModel_facts :
    (Discrete.mk ({false} : Set Bool) :
        (Mettapedia.Logic.PredicateInstitution.ofCarrier boolCarrier).model.obj
          (Opposite.op (Discrete.mk ()))) ∈
      models ((Mettapedia.Logic.PredicateInstitution.ofCarrier boolCarrier).satisfies
        (Discrete.mk ())) ({false} : Set BoolSentence) ∧
      ¬ (Mettapedia.Logic.PredicateInstitution.ofCarrier boolCarrier).satisfies (Discrete.mk ())
        (Discrete.mk ({false} : Set Bool)) (true : BoolSentence) := by
  constructor
  · intro φ member
    exact member
  · intro member
    exact Bool.false_ne_true (Set.mem_singleton_iff.mp member).symm

/-- **The collapse leaks `true`: no hosting error below its weight.** -/
theorem collapse_not_epsHosts {w ε : ℚ} (positive : 0 < w) (small : ε < w) :
    ¬ EpsHosts ((Mettapedia.Logic.PredicateInstitution.ofCarrier boolCarrier).satisfies
        (Discrete.mk ())) (trueWeighting w positive)
      (reductUniverse collapseComorphism (Discrete.mk ())) ({false} : Set BoolSentence) ε := by
  intro hosts
  have bound := weight_le_of_leak hosts (φ := (true : BoolSentence)) (Finset.mem_singleton_self _)
    collapse_validates_true falseModel_facts.1 falseModel_facts.2
  change w ≤ ε at bound
  linarith

/-- The reduct of the full target predicate satisfies every source sentence. -/
theorem fullReduct_satisfies (φ : BoolSentence) :
    (Mettapedia.Logic.PredicateInstitution.ofCarrier boolCarrier).satisfies (Discrete.mk ())
      (modelReduct collapseComorphism (Discrete.mk ()) (Discrete.mk (Set.univ : Set Unit))) φ :=
  (collapseComorphism.satisfaction_condition (Discrete.mk ()) (Discrete.mk Set.univ) φ).mp
    (Set.mem_univ _)

/-- **The collapse hosts `{false}` up to the weight of `true`.** -/
theorem collapse_epsHosts (w : ℚ) (positive : 0 < w) :
    EpsHosts ((Mettapedia.Logic.PredicateInstitution.ofCarrier boolCarrier).satisfies
        (Discrete.mk ())) (trueWeighting w positive)
      (reductUniverse collapseComorphism (Discrete.mk ())) ({false} : Set BoolSentence) w := by
  rw [epsHosts_iff]
  intro m _
  refine ⟨modelReduct collapseComorphism (Discrete.mk ()) (Discrete.mk Set.univ),
    ⟨⟨_, rfl⟩, fun φ _ => fullReduct_satisfies φ⟩, {true}, Finset.Subset.refl _,
    fun φ member outside => absurd member outside, ?_⟩
  unfold SentenceWeighting.mass
  exact (Finset.sum_singleton _ _).le

/-- **The representative comorphism hosts every theory with error zero.** -/
theorem representative_zeroHosts (ν : SentenceWeighting Unit) (T : Set Unit) :
    EpsHosts (isoInvariantInstitution.satisfies (Discrete.mk ())) ν
      (reductUniverse invariantRepresentativeComorphism (Discrete.mk ())) T 0 :=
  zeroHosts_of_coversModelsUpToIso invariantRepresentativeComorphism (Discrete.mk ())
    isoInvariantInstitution_satisfactionIsoInvariant
    invariantRepresentativeComorphism_coversModelsUpToIso ν T

end Collapse

/-! ## Identity proofs, testing `uip` -/

section Ladder

open Mettapedia.Logic.TheoryModel.IdentityProofs

/-- Test only `uip`, with weight `w`. -/
def uipWeighting (w : ℚ) (positive : 0 < w) : SentenceWeighting IdSentence where
  support := {.uip}
  weight _ := w
  weight_pos _ _ := positive

/-- **The thin universe hosts the groupoid laws up to the weight of `uip`.** -/
theorem thin_epsHosts (w : ℚ) (positive : 0 < w) :
    EpsHosts IdStructure.Sat (uipWeighting w positive) thin.{u} groupoidLaws w := by
  rw [epsHosts_iff]
  intro m _
  refine ⟨eqModel (ULift.{u} Bool), ⟨eqModel_bool_mem_thin, eqModel_mem_groupoidLaws _⟩,
    {.uip}, Finset.Subset.refl _, fun φ member outside => absurd member outside, ?_⟩
  unfold SentenceWeighting.mass
  exact (Finset.sum_singleton _ _).le

/-- **And no better**: `uip` leaks from the thin universe, and the two-proof
structure refutes it. -/
theorem thin_not_epsHosts {w ε : ℚ} (positive : 0 < w) (small : ε < w) :
    ¬ EpsHosts IdStructure.Sat (uipWeighting w positive) thin.{u} groupoidLaws ε := by
  intro hosts
  have validated : IdSentence.uip ∈ consequencesIn IdStructure.Sat thin.{u} groupoidLaws := by
    rw [consequencesIn_thin]
    exact fun equal => IdSentence.noConfusion equal
  have bound := weight_le_of_leak hosts (φ := .uip) (Finset.mem_singleton_self _) validated
    xorModel_mem_groupoidLaws xorModel_not_uip
  change w ≤ ε at bound
  linarith

/-- **Adding the two-proof structure brings the tested error to zero.**
Choosing a twin decides `uip` for an arbitrary structure. -/
theorem ladderOne_zeroHosts (w : ℚ) (positive : 0 < w) :
    EpsHosts IdStructure.Sat (uipWeighting w positive) ladderOne.{u} groupoidLaws 0 := by
  rw [zeroHosts_iff_twins]
  intro m _
  by_cases proofIrrelevant : m.Sat .uip
  · refine ⟨eqModel (ULift.{u} Bool),
      ⟨thin_subset_ladderOne eqModel_bool_mem_thin, eqModel_mem_groupoidLaws _⟩, ?_⟩
    intro φ member
    simp only [uipWeighting, Finset.mem_singleton] at member
    subst member
    exact ⟨fun _ => eqModel_sat_uip _, fun _ => proofIrrelevant⟩
  · refine ⟨xorModel, ⟨mem_insert _ _, xorModel_mem_groupoidLaws⟩, ?_⟩
    intro φ member
    simp only [uipWeighting, Finset.mem_singleton] at member
    subst member
    exact ⟨fun holds => (proofIrrelevant holds).elim, fun holds => (xorModel_not_uip holds).elim⟩

/-- **Zero hosting on the tested sentence leaves an untested leak**: the same
universe validates `loopComm`, which is not tested. -/
theorem ladderOne_untested_leak (w : ℚ) (positive : 0 < w) :
    EpsHosts IdStructure.Sat (uipWeighting w positive) ladderOne.{u} groupoidLaws 0 ∧
      ¬ HostsFaithfully IdStructure.Sat ladderOne.{u} groupoidLaws ∧
      IdSentence.loopComm ∉ (uipWeighting w positive).support :=
  ⟨ladderOne_zeroHosts w positive, not_hostsFaithfully_ladderOne, by simp [uipWeighting]⟩

/-! ## Testing `uip` and `connected`: faithful is not zero hosting -/

/-- Test `uip` with weight `a` and `connected` with weight `b`. -/
def uipConnectedWeighting (a b : ℚ) (ha : 0 < a) (hb : 0 < b) : SentenceWeighting IdSentence where
  support := {.uip, .connected}
  weight φ := if φ = .uip then a else b
  weight_pos φ _ := by split_ifs; exacts [ha, hb]

/-- Every structure of the dihedral ladder satisfies `uip` or `connected`. -/
theorem ladderTwo_uip_or_connected {M : IdStructure.{u}} (member : M ∈ ladderTwo.{u}) :
    M.Sat .uip ∨ M.Sat .connected := by
  rcases member with equal | equal | thinM
  · subst equal
    exact Or.inr loopModel_sat_connected
  · subst equal
    exact Or.inr loopModel_sat_connected
  · exact Or.inl thinM

/-- **Faithful hosting does not give zero hosting.** The dihedral ladder hosts
the groupoid laws faithfully, but no member refutes both `uip` and
`connected`, which the univalent structure does. -/
theorem ladderTwo_faithful_not_epsHosts {a b ε : ℚ} (ha : 0 < a) (hb : 0 < b) (small : ε < a)
    (small' : ε < b) :
    HostsFaithfully IdStructure.Sat ladderTwo.{1} groupoidLaws ∧
      ¬ EpsHosts IdStructure.Sat (uipConnectedWeighting a b ha hb) ladderTwo.{1} groupoidLaws
        ε := by
  refine ⟨hostsFaithfully_ladderTwo, fun hosts => ?_⟩
  obtain ⟨m', ⟨inLadder, _⟩, D, inside, agree, massLe⟩ :=
    (epsHosts_iff.mp hosts) univalentModel_mem_groupoidLaws
  have uipWeight : (uipConnectedWeighting a b ha hb).weight .uip = a := by
    simp [uipConnectedWeighting]
  have connectedWeight : (uipConnectedWeighting a b ha hb).weight .connected = b := by
    simp [uipConnectedWeighting]
  have uipOut : IdSentence.uip ∉ D := fun member => by
    have := (uipConnectedWeighting a b ha hb).weight_le_mass inside member
    rw [uipWeight] at this
    linarith
  have connectedOut : IdSentence.connected ∉ D := fun member => by
    have := (uipConnectedWeighting a b ha hb).weight_le_mass inside member
    rw [connectedWeight] at this
    linarith
  have agreeUip := agree .uip (by simp [uipConnectedWeighting]) uipOut
  have agreeConnected := agree .connected (by simp [uipConnectedWeighting]) connectedOut
  rcases ladderTwo_uip_or_connected inLadder with holds | holds
  · exact univalentModel_not_uip (agreeUip.mpr holds)
  · exact univalentModel_not_connected (agreeConnected.mpr holds)

/-- One point with its equality proofs: proof-irrelevant and connected. -/
theorem eqModel_punit_facts :
    (eqModel PUnit.{2}).Sat .uip ∧ (eqModel PUnit.{2}).Sat .connected :=
  ⟨eqModel_sat_uip _, fun a b => ⟨⟨⟨Subsingleton.elim (α := PUnit.{2}) a b⟩⟩⟩⟩

/-- **Adding the univalent structure brings the tested error to zero.** Every
combination of `uip` and `connected` now has a representative. -/
theorem univalent_completes_zeroHosts {a b : ℚ} (ha : 0 < a) (hb : 0 < b) :
    EpsHosts IdStructure.Sat (uipConnectedWeighting a b ha hb)
      (insert univalentModel ladderTwo.{1}) groupoidLaws 0 := by
  rw [zeroHosts_iff_twins]
  intro m _
  have inLadder : ∀ {M : IdStructure.{1}}, M.Sat .uip → M ∈ insert univalentModel ladderTwo.{1} :=
    fun holds => mem_insert_of_mem _ (ladderOne_subset_ladderTwo (thin_subset_ladderOne holds))
  have agreeOn : ∀ M : IdStructure.{1}, (M.Sat .uip ↔ m.Sat .uip) →
      (M.Sat .connected ↔ m.Sat .connected) →
      ∀ φ ∈ (uipConnectedWeighting a b ha hb).support, (m.Sat φ ↔ M.Sat φ) := by
    intro M sameUip sameConnected φ member
    simp only [uipConnectedWeighting, Finset.mem_insert, Finset.mem_singleton] at member
    rcases member with rfl | rfl
    · exact sameUip.symm
    · exact sameConnected.symm
  by_cases proofIrrelevant : m.Sat .uip <;> by_cases joined : m.Sat .connected
  · exact ⟨eqModel PUnit.{2}, ⟨inLadder eqModel_punit_facts.1, eqModel_mem_groupoidLaws _⟩,
      agreeOn _ (iff_of_true eqModel_punit_facts.1 proofIrrelevant)
        (iff_of_true eqModel_punit_facts.2 joined)⟩
  · exact ⟨eqModel (ULift.{1} Bool), ⟨inLadder (eqModel_sat_uip _), eqModel_mem_groupoidLaws _⟩,
      agreeOn _ (iff_of_true (eqModel_sat_uip _) proofIrrelevant)
        (iff_of_false eqModel_bool_not_connected joined)⟩
  · exact ⟨xorModel, ⟨mem_insert_of_mem _ (ladderOne_subset_ladderTwo (mem_insert _ _)),
      xorModel_mem_groupoidLaws⟩,
      agreeOn _ (iff_of_false xorModel_not_uip proofIrrelevant)
        (iff_of_true loopModel_sat_connected joined)⟩
  · exact ⟨univalentModel, ⟨mem_insert _ _, univalentModel_mem_groupoidLaws⟩,
      agreeOn _ (iff_of_false univalentModel_not_uip proofIrrelevant)
        (iff_of_false univalentModel_not_connected joined)⟩

end Ladder

end Mettapedia.Logic.TheoryModel.EpsilonHostingControls
