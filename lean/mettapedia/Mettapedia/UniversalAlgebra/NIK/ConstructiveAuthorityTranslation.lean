import Mettapedia.UniversalAlgebra.CertificateSubstitution
import Mettapedia.UniversalAlgebra.NIK.RejectedCertificate
import Mettapedia.UniversalAlgebra.NIK.TheoryEquivalence

/-!
# Constructive authority translations from axiom certificates

An equational theory translation becomes executable when every source axiom
occurrence is accompanied by a concrete accepted certificate over the target
system.  This module compiles complete native derivation trees structurally,
totalizes the compiler on rejected inputs, and packages the result as an exact
NIK authority translation.

No proof search or classical certificate selection occurs in the compiler.
-/

set_option autoImplicit false

namespace Mettapedia.UniversalAlgebra.NIK

open Mettapedia.Logic
open Mettapedia.OSLF.Framework.InitialModalSchema
open Mettapedia.GSLT.LanguageDef.NIKHeterogeneousTheory
open scoped BigOperators

universe u

variable {S : Signature.{u}} [DecidableEq S.Operation]

/-- Constructive translation data for equation systems over one signature:
every occurrence in the source system has a concrete accepted target
certificate for that exact equation. -/
structure AxiomCertificateTranslation
    (source target : EquationSystem S) : Type u where
  certificate : (occurrence : Fin source.equations.length) →
    AcceptedCertificate (equationalRuleInterface target)
      (source.equations.get occurrence)

namespace AxiomCertificateTranslation

variable {source target : EquationSystem S}

/-- Exact output-node budget for structural certificate compilation.  A
source axiom occurrence costs the size of its supplied target certificate;
every logical rule retains its root and recursively compiles its children. -/
def compiledNodeCount
    (translation : AxiomCertificateTranslation source target) :
    Derivation (Equation S) (EquationalRuleWitness source) → Nat
  | .node _ witness n children =>
      match witness with
      | .systemInstance occurrence _ =>
          (translation.certificate occurrence).nodeCount
      | .refl _ =>
          1 + ∑ position : Fin n,
            translation.compiledNodeCount (children position)
      | .symm _ _ =>
          1 + ∑ position : Fin n,
            translation.compiledNodeCount (children position)
      | .trans _ _ _ =>
          1 + ∑ position : Fin n,
            translation.compiledNodeCount (children position)
      | .congruence _ _ _ =>
          1 + ∑ position : Fin n,
            translation.compiledNodeCount (children position)

/-- Every listed target equation has its canonical one-node certificate. -/
def listedEquationCertificate (system : EquationSystem S)
    (occurrence : Fin system.equations.length) :
    AcceptedCertificate (equationalRuleInterface system)
      (system.equations.get occurrence) := by
  let noPremises : Fin 0 → Equation S := Fin.elim0
  let noChildren : (position : Fin 0) →
      AcceptedCertificate (equationalRuleInterface system)
        (noPremises position) := fun position => Fin.elim0 position
  exact AcceptedCertificate.node (equationalRuleInterface system)
    (.systemInstance occurrence Term.var)
    (system.equations.get occurrence) noPremises (by
      simp [equationalRuleInterface, EquationalRuleWitness.isInstance,
        Term.subst_variables]) noChildren

/-- Computational payload of certificate translation.  It is defined on all
source trees without consulting their validity proof.  A source axiom node is
replaced by its supplied target certificate; logical nodes are retained. -/
def compilePayload
    (translation : AxiomCertificateTranslation source target) :
    Derivation (Equation S) (EquationalRuleWitness source) →
      Derivation (Equation S) (EquationalRuleWitness target)
  | .node conclusion witness n children =>
      match witness with
      | .systemInstance occurrence substitution =>
          EquationalCertificate.instantiate substitution
            (translation.certificate occurrence).certificate
      | .refl term =>
          .node conclusion (.refl term) n
            (fun position => translation.compilePayload (children position))
      | .symm left right =>
          .node conclusion (.symm left right) n
            (fun position => translation.compilePayload (children position))
      | .trans left middle right =>
          .node conclusion (.trans left middle right) n
            (fun position => translation.compilePayload (children position))
      | .congruence operation left right =>
          .node conclusion (.congruence operation left right) n
            (fun position => translation.compilePayload (children position))

/-- The computational payload realizes its compositional node budget exactly
on every source tree, independently of replay validity. -/
theorem compilePayload_nodeCount
    (translation : AxiomCertificateTranslation source target) :
    ∀ sourceCertificate,
      (translation.compilePayload sourceCertificate).nodeCount =
        translation.compiledNodeCount sourceCertificate
  | .node conclusion witness n children => by
      cases witness with
      | systemInstance occurrence substitution =>
          simp only [compilePayload, compiledNodeCount,
            EquationalCertificate.instantiate_nodeCount]
          rfl
      | refl term =>
          simp only [compilePayload, compiledNodeCount,
            Derivation.nodeCount_node]
          exact congrArg (1 + ·) <| Finset.sum_congr rfl fun position _member =>
            compilePayload_nodeCount translation (children position)
      | symm left right =>
          simp only [compilePayload, compiledNodeCount,
            Derivation.nodeCount_node]
          exact congrArg (1 + ·) <| Finset.sum_congr rfl fun position _member =>
            compilePayload_nodeCount translation (children position)
      | trans left middle right =>
          simp only [compilePayload, compiledNodeCount,
            Derivation.nodeCount_node]
          exact congrArg (1 + ·) <| Finset.sum_congr rfl fun position _member =>
            compilePayload_nodeCount translation (children position)
      | congruence operation left right =>
          simp only [compilePayload, compiledNodeCount,
            Derivation.nodeCount_node]
          exact congrArg (1 + ·) <| Finset.sum_congr rfl fun position _member =>
            compilePayload_nodeCount translation (children position)

/-- Successful payload compilation preserves the physical root conclusion. -/
theorem compilePayload_concl_of_valid
    (translation : AxiomCertificateTranslation source target) :
    ∀ sourceCertificate,
      sourceCertificate.valid (equationalRuleInterface source) = true →
        (translation.compilePayload sourceCertificate).concl =
          sourceCertificate.concl
  | .node conclusion witness n children, accepted => by
      cases witness with
      | systemInstance occurrence substitution =>
          have rootAccepted := accepted
          simp only [Derivation.valid, Bool.and_eq_true, List.all_eq_true,
            List.forall_mem_ofFn_iff, id, equationalRuleInterface,
            EquationalRuleWitness.isInstance, decide_eq_true_eq]
            at rootAccepted
          rcases rootAccepted.1 with ⟨_premisesEmpty, conclusionEqual⟩
          simp only [compilePayload,
            EquationalCertificate.instantiate_concl]
          have certificateConcludes :=
            (translation.certificate occurrence).concludes
          have substitutedConcludes := congrArg
            (fun equation : Equation S => equation.subst substitution)
            certificateConcludes
          change
            (translation.certificate occurrence).certificate.concl.subst
              substitution = conclusion
          exact substitutedConcludes.trans (by
            simpa only [Equation.subst] using conclusionEqual.symm)
      | refl term => rfl
      | symm left right => rfl
      | trans left middle right => rfl
      | congruence operation left right => rfl

/-- Successfully replayed source trees compile to successfully replayed
target trees. -/
theorem compilePayload_valid_of_valid
    (translation : AxiomCertificateTranslation source target) :
    ∀ sourceCertificate,
      sourceCertificate.valid (equationalRuleInterface source) = true →
        (translation.compilePayload sourceCertificate).valid
          (equationalRuleInterface target) = true
  | .node conclusion witness n children, accepted => by
      simp only [Derivation.valid, Bool.and_eq_true, List.all_eq_true,
        List.forall_mem_ofFn_iff, id] at accepted
      cases witness with
      | systemInstance occurrence substitution =>
          exact EquationalCertificate.instantiate_valid_of_valid substitution
            (translation.certificate occurrence).certificate
            (translation.certificate occurrence).accepted
      | refl term =>
          simp only [compilePayload, Derivation.valid, Bool.and_eq_true,
            List.all_eq_true, List.forall_mem_ofFn_iff, id]
          have premiseConclusions :
              (List.ofFn fun position =>
                (translation.compilePayload (children position)).concl) =
              List.ofFn (fun position => (children position).concl) := by
            exact congrArg List.ofFn <| funext fun position =>
              compilePayload_concl_of_valid translation
                (children position) (accepted.2 position)
          have sourceRoot := accepted.1
          change decide
            ((List.ofFn fun position => (children position).concl) = [] ∧
              conclusion = (term, term)) = true at sourceRoot
          exact ⟨by
            change decide
              ((List.ofFn fun position =>
                  (translation.compilePayload (children position)).concl) = [] ∧
                conclusion = (term, term)) = true
            rw [premiseConclusions]
            exact sourceRoot,
            fun position => compilePayload_valid_of_valid translation
              (children position) (accepted.2 position)⟩
      | symm left right =>
          simp only [compilePayload, Derivation.valid, Bool.and_eq_true,
            List.all_eq_true, List.forall_mem_ofFn_iff, id]
          have premiseConclusions :
              (List.ofFn fun position =>
                (translation.compilePayload (children position)).concl) =
              List.ofFn (fun position => (children position).concl) := by
            exact congrArg List.ofFn <| funext fun position =>
              compilePayload_concl_of_valid translation
                (children position) (accepted.2 position)
          have sourceRoot := accepted.1
          change decide
            ((List.ofFn fun position => (children position).concl) =
                [(left, right)] ∧ conclusion = (right, left)) = true
            at sourceRoot
          exact ⟨by
            change decide
              ((List.ofFn fun position =>
                  (translation.compilePayload (children position)).concl) =
                    [(left, right)] ∧ conclusion = (right, left)) = true
            rw [premiseConclusions]
            exact sourceRoot,
            fun position => compilePayload_valid_of_valid translation
              (children position) (accepted.2 position)⟩
      | trans left middle right =>
          simp only [compilePayload, Derivation.valid, Bool.and_eq_true,
            List.all_eq_true, List.forall_mem_ofFn_iff, id]
          have premiseConclusions :
              (List.ofFn fun position =>
                (translation.compilePayload (children position)).concl) =
              List.ofFn (fun position => (children position).concl) := by
            exact congrArg List.ofFn <| funext fun position =>
              compilePayload_concl_of_valid translation
                (children position) (accepted.2 position)
          have sourceRoot := accepted.1
          change decide
            ((List.ofFn fun position => (children position).concl) =
                [(left, middle), (middle, right)] ∧
              conclusion = (left, right)) = true at sourceRoot
          exact ⟨by
            change decide
              ((List.ofFn fun position =>
                  (translation.compilePayload (children position)).concl) =
                    [(left, middle), (middle, right)] ∧
                conclusion = (left, right)) = true
            rw [premiseConclusions]
            exact sourceRoot,
            fun position => compilePayload_valid_of_valid translation
              (children position) (accepted.2 position)⟩
      | congruence operation left right =>
          simp only [compilePayload, Derivation.valid, Bool.and_eq_true,
            List.all_eq_true, List.forall_mem_ofFn_iff, id]
          have premiseConclusions :
              (List.ofFn fun position =>
                (translation.compilePayload (children position)).concl) =
              List.ofFn (fun position => (children position).concl) := by
            exact congrArg List.ofFn <| funext fun position =>
              compilePayload_concl_of_valid translation
                (children position) (accepted.2 position)
          have sourceRoot := accepted.1
          change decide
            ((List.ofFn fun position => (children position).concl) =
                List.ofFn (fun position =>
                  (left position, right position)) ∧
              conclusion = (.op operation left, .op operation right)) = true
            at sourceRoot
          exact ⟨by
            change decide
              ((List.ofFn fun position =>
                  (translation.compilePayload (children position)).concl) =
                    List.ofFn (fun position =>
                      (left position, right position)) ∧
                conclusion = (.op operation left, .op operation right)) = true
            rw [premiseConclusions]
            exact sourceRoot,
            fun position => compilePayload_valid_of_valid translation
              (children position) (accepted.2 position)⟩

/-- Compile a successfully replayed native source certificate into a
successfully replayed native target certificate with the same conclusion. -/
def compileAccepted (translation : AxiomCertificateTranslation source target)
    (sourceCertificate :
      Derivation (Equation S) (EquationalRuleWitness source))
    (accepted : sourceCertificate.valid
      (equationalRuleInterface source) = true) :
    AcceptedCertificate (equationalRuleInterface target)
      sourceCertificate.concl where
  certificate := translation.compilePayload sourceCertificate
  accepted := translation.compilePayload_valid_of_valid sourceCertificate accepted
  concludes := translation.compilePayload_concl_of_valid sourceCertificate accepted

/-- The accepted compiler has exactly the same structural cost as its
proof-independent computational payload. -/
theorem compileAccepted_nodeCount
    (translation : AxiomCertificateTranslation source target)
    (sourceCertificate :
      Derivation (Equation S) (EquationalRuleWitness source))
    (accepted : sourceCertificate.valid
      (equationalRuleInterface source) = true) :
    (translation.compileAccepted sourceCertificate accepted).nodeCount =
      translation.compiledNodeCount sourceCertificate :=
  translation.compilePayload_nodeCount sourceCertificate

/-- Total structural certificate compilation.  Successfully replayed inputs
are recursively translated; rejected inputs become the canonical rejected
target sentinel with the same root conclusion. -/
def compile (translation : AxiomCertificateTranslation source target)
    (sourceCertificate :
      Derivation (Equation S) (EquationalRuleWitness source)) :
    Derivation (Equation S) (EquationalRuleWitness target) :=
  if accepted :
      sourceCertificate.valid (equationalRuleInterface source) = true then
    (translation.compileAccepted sourceCertificate accepted).certificate
  else
    rejectedCertificate target sourceCertificate.concl

/-- Structural compilation preserves the physical root conclusion on every
input. -/
theorem compile_concl
    (translation : AxiomCertificateTranslation source target)
    (sourceCertificate :
      Derivation (Equation S) (EquationalRuleWitness source)) :
    (translation.compile sourceCertificate).concl =
      sourceCertificate.concl := by
  by_cases accepted :
      sourceCertificate.valid (equationalRuleInterface source) = true
  · simp only [compile, dif_pos accepted]
    exact (translation.compileAccepted sourceCertificate accepted).concludes
  · simp [compile, accepted]

/-- Structural compilation preserves the replay-validity bit exactly. -/
theorem compile_valid
    (translation : AxiomCertificateTranslation source target)
    (sourceCertificate :
      Derivation (Equation S) (EquationalRuleWitness source)) :
    (translation.compile sourceCertificate).valid
        (equationalRuleInterface target) =
      sourceCertificate.valid (equationalRuleInterface source) := by
  by_cases accepted :
      sourceCertificate.valid (equationalRuleInterface source) = true
  · rw [accepted]
    simp only [compile, dif_pos accepted]
    exact (translation.compileAccepted sourceCertificate accepted).accepted
  · have rejected :
        sourceCertificate.valid (equationalRuleInterface source) = false :=
      Bool.eq_false_of_not_eq_true accepted
    rw [rejected]
    simp [compile, accepted]

/-- On an accepted source certificate, total compilation has exactly the
compositional node count above. -/
theorem compile_nodeCount_of_valid
    (translation : AxiomCertificateTranslation source target)
    (sourceCertificate :
      Derivation (Equation S) (EquationalRuleWitness source))
    (accepted : sourceCertificate.valid
      (equationalRuleInterface source) = true) :
    (translation.compile sourceCertificate).nodeCount =
      translation.compiledNodeCount sourceCertificate := by
  simp only [compile, dif_pos accepted]
  exact translation.compileAccepted_nodeCount sourceCertificate accepted

/-- A canonical one-node source-axiom certificate compiles to exactly the
size of the supplied target certificate for that occurrence. -/
theorem compile_listedEquation_nodeCount
    (translation : AxiomCertificateTranslation source target)
    (occurrence : Fin source.equations.length) :
    (translation.compile
      (listedEquationCertificate source occurrence).certificate).nodeCount =
        (translation.certificate occurrence).nodeCount := by
  rw [translation.compile_nodeCount_of_valid
    (listedEquationCertificate source occurrence).certificate
    (listedEquationCertificate source occurrence).accepted]
  rfl

/-- The structural compiler makes profile-blind replay commute for every
claim and every source certificate. -/
theorem compile_check_commutes
    (translation : AxiomCertificateTranslation source target)
    (claim : Equation S)
    (sourceCertificate :
      Derivation (Equation S) (EquationalRuleWitness source)) :
    ((translation.compile sourceCertificate).valid
          (equationalRuleInterface target) &&
        decide ((translation.compile sourceCertificate).concl = claim)) =
      (sourceCertificate.valid (equationalRuleInterface source) &&
        decide (sourceCertificate.concl = claim)) := by
  rw [translation.compile_valid]
  simp only [translation.compile_concl]

/-- Every source axiom occurrence is a generated target consequence. -/
theorem occurrence_consequence
    (translation : AxiomCertificateTranslation source target)
    (occurrence : Fin source.equations.length) :
    EquationalConsequence target (source.equations.get occurrence) := by
  let output := translation.certificate occurrence
  have derived := Derivation.valid_sound (equationalRuleInterface target)
    output.certificate output.accepted
  rw [output.concludes] at derived
  exact derived

/-- Concrete occurrence certificates extend to preservation of every
generated equational consequence. -/
theorem preservesConsequence
    (translation : AxiomCertificateTranslation source target)
    (equation : Equation S) :
    EquationalConsequence source equation →
      EquationalConsequence target equation := by
  apply EquationalConsequence.translate_axioms
  intro listedEquation member
  obtain ⟨occurrence, equationEqual⟩ := List.mem_iff_get.mp member
  rw [← equationEqual]
  exact translation.occurrence_consequence occurrence

/-- Concrete source-axiom certificates ensure that every target model is also
a source model. -/
theorem targetModel_satisfies_source
    (translation : AxiomCertificateTranslation source target)
    {Carrier : Type u} (model : Model S Carrier)
    (satisfiesTarget : model.Satisfies target) :
    model.Satisfies source := by
  intro equation member
  exact equationalConsequence_sound
    (translation.preservesConsequence equation
      (EquationalConsequence.of_mem member)) Carrier model satisfiesTarget

/-- Model-theoretic meaning is preserved by a constructive axiom-certificate
translation. -/
theorem preservesEntails
    (translation : AxiomCertificateTranslation source target)
    (equation : Equation S) :
    Entails source equation → Entails target equation := by
  intro sourceEntails Carrier model satisfiesTarget
  exact sourceEntails Carrier model
    (translation.targetModel_satisfies_source model satisfiesTarget)

/-- The total structural compiler is an exact native NIK authority
translation. -/
def authorityTranslation
    (translation : AxiomCertificateTranslation source target) :
    AuthorityTranslation (contract source) (contract target) where
  mapKind := id
  mapSignature := id
  signature_commutes := by intro _kind; rfl
  mapClaim := fun _kind equation => equation
  mapCertificate := fun _kind certificate => translation.compile certificate
  check_commutes := by
    intro _kind claim certificate
    change
      ((translation.compile certificate).valid
          (equationalRuleInterface target) &&
        decide ((translation.compile certificate).concl = claim)) =
      (certificate.valid (equationalRuleInterface source) &&
        decide (certificate.concl = claim))
    exact translation.compile_check_commutes claim certificate
  meaning_preserved := by
    intro _kind equation meaningful
    exact translation.preservesEntails equation meaningful

/-- Certificate translations in both directions identify the generated
consequence relations. -/
theorem sameConsequences
    (forward : AxiomCertificateTranslation source target)
    (backward : AxiomCertificateTranslation target source) :
    EquationSystem.SameConsequences source target :=
  fun equation =>
    ⟨forward.preservesConsequence equation,
      backward.preservesConsequence equation⟩

/-- With a reverse certificate translation, the forward exact authority route
is conservative after forgetting certificates. -/
theorem authorityTranslation_conservative
    (forward : AxiomCertificateTranslation source target)
    (backward : AxiomCertificateTranslation target source) :
    forward.authorityTranslation.toTheoryTranslation.Conservative := by
  have equivalent := forward.sameConsequences backward
  constructor
  · intro _kind equation targetScope
    exact (equivalent equation).mpr targetScope
  · intro _kind equation targetMeaning
    exact (entails_iff_of_sameConsequences equivalent equation).mpr
      targetMeaning

end AxiomCertificateTranslation

end Mettapedia.UniversalAlgebra.NIK
