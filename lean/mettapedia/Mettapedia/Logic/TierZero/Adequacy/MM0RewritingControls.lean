import Mettapedia.Logic.TierZero.Adequacy.MM0Rewriting
import Mettapedia.Logic.TierZero.Adequacy.MM0RewritingTheoremControls

/-! # Whole-catalog MM0 adequacy and authority controls -/

set_option autoImplicit false

namespace Mettapedia.Logic.TierZero.Adequacy.MM0Rewriting.CatalogControls

open Mettapedia.Languages.MM0.Kernel
open Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Sources

def theory : Theory where
  sorts := [(0, { provable := true }), (1, {})]
  terms := [(0, ⟨[.regular 0 ∅, .regular 0 ∅], 0, ∅⟩),
    (1, ⟨[.bound 1, .regular 0 {0}], 0, ∅⟩)]
  theorems := [(0, TheoremControls.nf)]

theorem signature_agrees : theory.termSignature = TheoremControls.signature := by
  funext index
  cases index with
  | zero => rfl
  | succ index => cases index <;> rfl

theorem theory_formed : theory.WellFormed := by
  constructor
  · intro index declaration known
    cases index with
    | zero =>
        cases known
        apply (TermDecl.check_iff _ _).mp
        decide
    | succ index =>
        cases index with
        | zero =>
            cases known
            apply (TermDecl.check_iff _ _).mp
            decide
        | succ index => simp [Theory.termSignature, theory, List.lookup_cons] at known
  · intro index body known
    simp [Theory.definitionSignature, theory] at known
  · intro index declaration known
    cases index with
    | zero =>
        cases known
        apply (TheoremDecl.check_iff _ _ _).mp
        decide
    | succ index => simp [Theory.theoremSignature, theory, List.lookup_cons] at known

theorem target_formed : Context.WellFormed theory.sortSignature TheoremControls.independentContext := by
  apply (Context.check_iff _ _).mp
  decide

theorem independent_nf_derivation :
    Derives theory.termSignature theory.definitionSignature theory.theoremSignature
      TheoremControls.independentContext [] TheoremControls.goal := by
  have instantiated : TheoremControls.nf.Instantiates theory.termSignature TheoremControls.independentContext
      TheoremControls.arguments ⟨[], TheoremControls.goal⟩ := by
    rw [signature_agrees]
    exact TheoremControls.nf_instance
  exact .theoremApp (index := 0) (instantiation := ⟨[], TheoremControls.goal⟩) rfl instantiated .nil

/-- The adequacy theorem applies to a finite theory with a genuine bound
formal and an independence-sensitive axiom. -/
theorem full_catalog_accepts_nf :
    ∃ requests after,
      Relation.ReflTransGen (process theory TheoremControls.independentContext (catalog theory)).Step
        (requestBag requests + hypothesisBag TheoremControls.independentContext []) after ∧
      proofValue TheoremControls.independentContext TheoremControls.goal ∈ after :=
  (rewriting_reaches_iff_derives theory_formed target_formed [] TheoremControls.goal).mpr independent_nf_derivation

theorem unauthorized_client_cannot_publish (client : calculus.Process)
    (denied : client.rights .judgments .send = false) (target : Context) (expression : Preterm) :
    ¬client.Step 0 {proofValue target expression} := by
  intro step
  have noNew := step.no_make_without_send denied
  have present : proofValue target expression ∈ snapshot space .judgments {proofValue target expression} := by
    simp [snapshot, space_proof]
  have old := Multiset.mem_of_le noNew present
  simp [snapshot] at old

theorem request_named_pf_stays_request (arguments : List Tm) :
    space (requestValue "pf" arguments) = .requests := space_request _ _

theorem request_named_cv_stays_request (arguments : List Tm) :
    space (requestValue "cv" arguments) = .requests := space_request _ _

end Mettapedia.Logic.TierZero.Adequacy.MM0Rewriting.CatalogControls
