import Mettapedia.Logic.TierZero.Adequacy.MM0RewritingPromotion
import Mettapedia.Logic.TierZero.Adequacy.MM0RewritingControls

/-! # Native promotion retains assumptions and refuses unjustified schemas -/

set_option autoImplicit false

namespace Mettapedia.Logic.TierZero.Adequacy.MM0Rewriting.PromotionControls

open Mettapedia.Languages.MM0.Kernel

def nfPromotion : Promotion CatalogControls.theory where
  index := 1
  declaration := TheoremControls.nf
  fresh := rfl
  admitted := CatalogControls.theory_formed.theorems 0 TheoremControls.nf rfl
  native := CatalogControls.full_catalog_accepts_nf

theorem nf_copy_is_conservative {target : Context}
    (formed : Context.WellFormed CatalogControls.theory.sortSignature target)
    (hypotheses : List Preterm) (expression : Preterm) :
    Reaches nfPromotion.installed target hypotheses expression ↔
      Reaches CatalogControls.theory target hypotheses expression :=
  nfPromotion.conservative CatalogControls.theory_formed formed hypotheses expression

def base : Theory where
  sorts := [(0, { provable := true })]
  terms := [(0, ⟨[], 0, ∅⟩)]

theorem base_formed : base.WellFormed := by
  constructor
  · intro index declaration known
    cases index with
    | zero =>
        cases known
        apply (TermDecl.check_iff _ _).mp
        decide
    | succ index => simp [Theory.termSignature, base, List.lookup_cons] at known
  · intro index body known
    simp [Theory.definitionSignature, base] at known
  · intro index declaration known
    simp [Theory.theoremSignature, base] at known

theorem empty_context_formed : Context.WellFormed base.sortSignature [] := .nil []

def unsupported : TheoremDecl := ⟨[], [], .term 0⟩
def retained : TheoremDecl := ⟨[], [.term 0], .term 0⟩

theorem unsupported_payload_is_well_typed : unsupported.Admissible base.sortSignature base.termSignature := by
  apply (TheoremDecl.check_iff _ _ _).mp
  decide

theorem unjustified_publication_has_no_certificate :
    ¬∃ certificate : Promotion base, certificate.declaration = unsupported := by
  rintro ⟨certificate, same⟩
  have accepted := certificate.native
  rw [same] at accepted
  exact no_unjustified_reach base_formed empty_context_formed (fun _ => rfl) (.term 0) accepted

def retainedPromotion : Promotion base where
  index := 0
  declaration := retained
  fresh := rfl
  admitted := by
    apply (TheoremDecl.check_iff _ _ _).mp
    decide
  native := (reaches_iff base_formed empty_context_formed _ _).mpr (.hypothesis (by simp [retained]))

theorem retained_assumption_suffices : Reaches retainedPromotion.installed [] [.term 0] (.term 0) :=
  (retainedPromotion.conservative base_formed empty_context_formed _ _).mpr retainedPromotion.native

/-- The conclusion has no variables, but that does not discharge its used
logical assumption. Even after installation it cannot be proved from nothing. -/
theorem closed_conclusion_does_not_erase_assumption :
    ¬Reaches retainedPromotion.installed [] [] (.term 0) := by
  intro accepted
  have original := (retainedPromotion.conservative base_formed empty_context_formed _ _).mp accepted
  exact no_unjustified_reach base_formed empty_context_formed (fun _ => rfl) (.term 0) original

end Mettapedia.Logic.TierZero.Adequacy.MM0Rewriting.PromotionControls
