import Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Regular.SyntacticCwf
import Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Regular.BidirectionalCompleteness
import Mettapedia.TypeTheory.CwfYonedaCoherence

/-!
# Regular source terms in the displayed-presheaf CwF

The generic Yoneda/comprehension construction applies to the actual regular
two-sort syntactic CwF. Its semantic terms recover the exact source terms.
Accepted results of the existing checker enter this interpretation with
their computation equation retained, and further contextual substitution
acts on that returned term.

This is a syntax-retaining interpretation. Beta conversion is not equality
of its presheaf sections. It does not supply a conversion quotient, full
native-candidate initiality, identity elimination, or a cumulative tower.
-/

namespace Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Regular.SyntacticCwf

open Syntax Substitution Regular
open Mettapedia.TypeTheory

/-- The general comprehension lift is the regular calculus's existing
de Bruijn binder lift, not a second substitution implementation. -/
theorem comprehension_lift_eq {Γ Δ : Context} (σ : Hom Γ Δ) (A : Ty Δ) :
    Mettapedia.GSLT.Core.ContextualLadder.TypeOver.extensionSubstitution
        (C := cwf) σ A = lift σ A := by
  apply Subtype.ext
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact cast_term_val (typeSub_compose A σ (weaken (typeSub A σ))).symm
      (lastTerm (typeSub A σ))
  · change subst (Permissive.Typing.renToSub Renaming.wk) (σ.val j) =
      Renaming.rename Renaming.wk (σ.val j)
    exact Permissive.Typing.subst_renToSub _ _

abbrev representedFamily {Γ : Context} (A : Ty Γ) := CwfYoneda.family cwf A

/-- The existing semantic CwF's terms at a represented regular source type
are precisely the source terms. -/
def representedTermEquiv {Γ : Context} (A : Ty Γ) :
    Tm Γ A ≃ (representedFamily A).sections :=
  CwfYoneda.termSectionEquiv cwf A

/-- Reading an interpreted term at any source substitution recovers the
actual simultaneous substitution, not another inhabitant of its type. -/
theorem representedTerm_at {Γ Δ : Context} {A : Ty Γ}
    (term : Tm Γ A) (σ : Hom Δ Γ) :
    CwfYoneda.decodeTerm cwf A σ
        ((representedTermEquiv A term).val
          ⟨Opposite.op (CwfYoneda.context cwf Δ), σ⟩) =
      termSub term σ :=
  CwfYoneda.decode_encode cwf A σ (termSub term σ)

/-- Every successful checker receipt retains exactly the requested term. -/
def termOfChecked {Γ : Context} {A : Ty Γ} {term : ScopedTerm Γ.length}
    (checked : RegularChecked (Γ := Γ.raw) term A.val) : Tm Γ A :=
  ⟨term, checked.typing⟩

/-- An accepted direct check supplies its actual computed receipt and a
natural semantic term whose value at every substitution is the source term
under that substitution. -/
theorem accepted_has_represented_term {Γ : Context} (A : Ty Γ)
    (term : ScopedTerm Γ.length)
    (accepted : regularCheckBool Γ.regular term A.val = true) :
    ∃ checked : RegularChecked (Γ := Γ.raw) term A.val,
      checkRegularType Γ.regular term A.val = .ok checked ∧
      ∀ (Δ : Context) (σ : Hom Δ Γ),
        (CwfYoneda.decodeTerm cwf A σ
          ((representedTermEquiv A (termOfChecked checked)).val
            ⟨Opposite.op (CwfYoneda.context cwf Δ), σ⟩)).val =
          subst σ.val term := by
  unfold regularCheckBool at accepted
  cases computed : checkRegularType Γ.regular term A.val with
  | error failure =>
      rw [computed] at accepted
      change false = true at accepted
      cases accepted
  | ok checked =>
      refine ⟨checked, rfl, ?_⟩
      intro Δ σ
      rw [representedTerm_at]
      rfl

/-- The semantic connection accepts exactly the checker's already proved
public bidirectional specification, without introducing another checker. -/
theorem checked_receipt_iff_public {Γ : Context} (A : Ty Γ)
    (term : ScopedTerm Γ.length) :
    (∃ checked : RegularChecked (Γ := Γ.raw) term A.val,
      checkRegularType Γ.regular term A.val = .ok checked) ↔
      RegularPublicChecks Γ.regular term A.val := by
  constructor
  · rintro ⟨checked, computed⟩
    exact checkRegularType_reflects Γ.regular term A.val checked computed
  · intro derivation
    have accepted := regularCheckBool_complete derivation
    obtain ⟨checked, computed, _⟩ := accepted_has_represented_term A term accepted
    exact ⟨checked, computed⟩

/-! ## Inhabited controls and equality boundaries -/

def smallSort (Γ : Context) : Ty Γ := ⟨.u0, .u0_type Γ.raw⟩

def sampleContext : Context := extend empty (smallSort empty)

def sampleTerm : Tm sampleContext (smallSort sampleContext) :=
  lastTerm (smallSort empty)

def sampleIdentity : Tm sampleContext
    (piType (smallSort sampleContext)
      (smallSort (extend sampleContext (smallSort sampleContext)))) :=
  lambdaTerm (lastTerm (smallSort sampleContext))

def sampleBeta : Tm sampleContext (smallSort sampleContext) :=
  applyTerm sampleIdentity sampleTerm

/-- Both terms are well typed and convertible, while their source-retaining
semantic sections remain distinct. Conversion is not silently reflected. -/
theorem beta_conversion_does_not_collapse_sections :
    ConstantFreeConv sampleBeta.val sampleTerm.val ∧
      representedTermEquiv (smallSort sampleContext) sampleBeta ≠
        representedTermEquiv (smallSort sampleContext) sampleTerm := by
  constructor
  · exact apply_lambda_converts (lastTerm (smallSort sampleContext)) sampleTerm
  · intro same
    have terms := (representedTermEquiv (smallSort sampleContext)).injective same
    have raw := congrArg Subtype.val terms
    cases raw

/-- A type family genuinely depends on the newly bound term. -/
def dependentIdentityFamily : Ty sampleContext :=
  identityType (smallSort sampleContext) sampleTerm sampleTerm

def dependentIdentityWitness : Tm sampleContext dependentIdentityFamily :=
  reflexivityTerm sampleTerm

theorem dependent_witness_recovered :
    (representedTermEquiv dependentIdentityFamily).symm
        (representedTermEquiv dependentIdentityFamily dependentIdentityWitness) =
      dependentIdentityWitness :=
  (representedTermEquiv dependentIdentityFamily).symm_apply_apply _

/-- The untyped top sort cannot enter the represented source type family. -/
theorem upper_sort_not_formed (Γ : Context) :
    ¬ ∃ A : Ty Γ, A.val = .u1 := by
  rintro ⟨A, equal⟩
  exact no_regular_u1_term (equal ▸ A.property)

/-- The old raw-typing counterexample is rejected at type formation. -/
theorem top_domain_not_formed :
    ¬ ∃ A : Ty empty, A.val = .pi .u1 .u1 := by
  rintro ⟨A, equal⟩
  exact A.property.subject_ne_pi_u1_domain equal

/-- A public, executable positive case feeds the semantic connection. -/
theorem checked_identity_has_represented_term :
    ∃ checked : RegularChecked (Γ := empty.raw) (.lam (.var 0))
        (piType (smallSort empty) (smallSort (extend empty (smallSort empty)))).val,
      checkRegularType empty.regular (.lam (.var 0)) (.pi .u0 .u0) = .ok checked ∧
      ∀ (Δ : Context) (σ : Hom Δ empty),
        (CwfYoneda.decodeTerm cwf _ σ
          ((representedTermEquiv _ (termOfChecked checked)).val
            ⟨Opposite.op (CwfYoneda.context cwf Δ), σ⟩)).val =
          subst σ.val (.lam (.var 0)) :=
  accepted_has_represented_term
    (piType (smallSort empty) (smallSort (extend empty (smallSort empty))))
    (.lam (.var 0)) checkRegular_identity_accepts

#print axioms comprehension_lift_eq
#print axioms representedTermEquiv
#print axioms representedTerm_at
#print axioms accepted_has_represented_term
#print axioms checked_receipt_iff_public
#print axioms beta_conversion_does_not_collapse_sections
#print axioms dependent_witness_recovered
#print axioms upper_sort_not_formed
#print axioms top_domain_not_formed
#print axioms checked_identity_has_represented_term

end Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Regular.SyntacticCwf
