import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentFibreAdequacy

/-!
# Second-order fibre conservativity

Over a rule package whose constants are exactly the realized sorts and operators, the map
`fibre` of the second-order step into the unifier's typed βη frame is **full and faithful up to
typed equality** on translated frames:

* `fibre_full`: every substitution between translated telescopes is pointwise equal to the
  translation of a second-order assignment (read it in η-long form, then by adequacy);
* `fibre_reflects`: translations of distinct observations are not equal.

So on translated stores, for solutions into translated frames:

* **solutions correspond** (`fibre_solutions_correspond`);
* **principal answers correspond**: a translated assignment is principal in the unifier's frame
  only if it is principal in the second-order step (`fibre_principal_reflect`), and every principal
  answer of the unifier's frame landing in a translated frame is, up to typed equality, the
  translation of a second-order principal answer (`fibre_answer_in_fibre`);
* **certified refutations transfer back** (`fibre_refutation`).

The second-order frames are the η-long fibre of the dependent frames.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentFibre

open CategoryTheory Interface Interface.Translation
open Mettapedia.OSLF
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization
open ContextualDependentEtaLong

variable {Head L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L}

omit [UniverseLevel.LevelOrder L] in
theorem metaCtx_lookup_subst {sig : Binding.Signature} (names : BindingSignatureEmbedding.Names sig)
    (M : List (Binding.MetaArity sig)) {k : Nat} (σ : Sub Head M.length k) (i : Fin M.length) :
    subst σ (Ctx.lookup (metaCtx (Head := Head) names M) i) =
      liftClosed (BindingSignatureEmbedding.bindingType names (M.get i).1 (M.get i).2) := by
  rw [metaCtx_lookup, subst_liftClosed]

/-- Pointwise equal substitutions solve the same stores of the unifier's frame. -/
theorem models_iff_of_substEq {Γ Δ : TypedContextual.Context S.R} {σ σ' : Δ ⟶ Γ}
    (equal : SubstEq S.R Γ.raw Δ.raw σ.substitution σ'.substitution)
    (K : EquationStore (TypedContextual.TotalTerm Γ)) :
    (ContextualDependentEta.frames S.levels).Models σ K ↔
      (ContextualDependentEta.frames S.levels).Models σ' K := by
  have eqv := (ContextualDependentEta.frames S.levels).equivalence Δ
  constructor
  · intro solved e member
    exact eqv.trans (eqv.symm (act_equal_of_substEq equal e.1))
      (eqv.trans (solved e member) (act_equal_of_substEq equal e.2))
  · intro solved e member
    exact eqv.trans (act_equal_of_substEq equal e.1)
      (eqv.trans (solved e member) (eqv.symm (act_equal_of_substEq equal e.2)))

variable (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R) (heads : HeadPreserving S.R)
  (algebra : CumulativeAlgebra S.R) (complete : AlgorithmicComplete S.R S.roles)
  (rigid : ∀ name, S.roles name = .rigid) (church : ConversionCoherence.ChurchRosser S.R)
variable {sig : Binding.Signature} (names : BindingSignatureEmbedding.Names sig)
  (realization : BindingSignatureEmbedding.Realization names S.R)
  (sortInjective : Function.Injective names.sort)
  (closed : ClosedRealization (S := S) names)

include facts roots heads algebra complete rigid sortInjective closed

/-- **Fullness**: every substitution between translated telescopes is pointwise equal to the
translation of a second-order assignment. -/
theorem fibre_full {M N : List (Binding.MetaArity sig)}
    (ρ : (fibre facts roots heads church names realization).obj N ⟶
      (fibre facts roots heads church names realization).obj M) :
    ∃ f : Binding.ContextualFamily.Assignment (S := sig) M.get N.get,
      SubstEq S.R (metaCtx names M) (metaCtx names N) ρ.substitution
        ((fibre facts roots heads church names realization).hom f).substitution := by
  obtain ⟨ρ', reading⟩ := longReading_exists facts roots heads algebra complete rigid ρ
  have each : ∀ i : Fin M.length,
      ∃ t : Binding.Term (Sig sig N) (M.get i).1 (M.get i).2,
        abstractN (M.get i).1.length (encode names N t) = ρ'.substitution i := by
    intro i
    have long := (reading i).1
    have retyped : Long S.R S.roles (.term (metaCtx names N) (ρ'.substitution i)
        (liftClosed (BindingSignatureEmbedding.bindingType names (M.get i).1 (M.get i).2))) :=
      metaCtx_lookup_subst names M ρ.substitution i ▸ long
    exact adequate_entry names realization facts complete rigid sortInjective closed N retyped
  choose f hf using each
  refine ⟨f, ?_⟩
  have same : ((fibre facts roots heads church names realization).hom f).substitution =
      ρ'.substitution := funext hf
  rw [same]
  exact reading.substEq

variable (operatorInjective : ∀ {s : sig.Srt}, Function.Injective (names.operator (sort := s)))
include operatorInjective

/-- **Solutions correspond on translated stores**: every solution into a translated frame is
pointwise equal to a translated assignment, and solves the translated store exactly when the
assignment solves the store. -/
theorem fibre_solutions_correspond {M N : List (Binding.MetaArity sig)}
    (K : EquationStore (Binding.ContextualFamily.Observation sig M.get))
    (ρ : (fibre facts roots heads church names realization).obj N ⟶
      (fibre facts roots heads church names realization).obj M) :
    ∃ f : Binding.ContextualFamily.Assignment (S := sig) M.get N.get,
      SubstEq S.R (metaCtx names M) (metaCtx names N) ρ.substitution
        ((fibre facts roots heads church names realization).hom f).substitution ∧
      ((ContextualDependentEta.frames S.levels).Models ρ
          ((fibre facts roots heads church names realization).store K) ↔
        (listFrames sig).Models (a := M) (b := N) f K) := by
  obtain ⟨f, equal⟩ := fibre_full facts roots heads algebra complete rigid church names realization
    sortInjective closed ρ
  exact ⟨f, equal, (models_iff_of_substEq equal _).trans
    (fibre_models_iff facts roots heads algebra complete rigid church names realization sortInjective
      @operatorInjective f K)⟩

/-- **Principal answers reflect**: a translated assignment that is principal in the unifier's
frame is principal in the second-order step. -/
theorem fibre_principal_reflect {M N : List (Binding.MetaArity sig)}
    {K : EquationStore (Binding.ContextualFamily.Observation sig M.get)}
    {σ : Binding.ContextualFamily.Assignment (S := sig) M.get N.get}
    (principal : (ContextualDependentEta.frames S.levels).Principal
      ((fibre facts roots heads church names realization).store K)
      ((fibre facts roots heads church names realization).hom σ)) :
    (listFrames sig).Principal (a := M) (m := N) K σ where
  sound := fibre_principal_solves facts roots heads algebra complete rigid church names realization
    sortInjective @operatorInjective principal
  factors := by
    intro L g solved
    let Ψ := fibre facts roots heads church names realization
    let Y := ContextualDependentEta.frames S.levels
    obtain ⟨ρ, through⟩ := principal.factors _ (Ψ.hom g) (Ψ.models solved)
    obtain ⟨r, equal⟩ := fibre_full facts roots heads algebra complete rigid church names realization
      sortInjective closed ρ
    refine ⟨r, fun o => ?_⟩
    apply fibre_reflects facts roots heads algebra complete rigid church names realization
      sortInjective @operatorInjective
    have eqv := Y.equivalence (Ψ.obj L)
    have h₁ := Ψ.act g o
    have h₂ := through (Ψ.tm o)
    rw [Y.act_comp] at h₂
    have h₃ := act_equal_of_substEq (Γ := Ψ.obj N) (Δ := Ψ.obj L) (σ := ρ) (σ' := Ψ.hom r) equal
      (Y.act (Ψ.hom σ) (Ψ.tm o))
    have h₄ := Y.preserves (Ψ.hom r)
      ((Y.equivalence (Ψ.obj N)).symm (Ψ.act σ o))
    have h₅ := eqv.symm (Ψ.act r ((listFrames sig).act σ o))
    show Y.E (Ψ.tm ((listFrames sig).act g o))
      (Ψ.tm ((listFrames sig).act ((listFrames sig).comp r σ) o))
    rw [(listFrames sig).act_comp]
    exact eqv.trans h₁ (eqv.trans h₂ (eqv.trans h₃ (eqv.trans h₄ h₅)))

/-- **Every principal answer of the unifier's frame that lands in a translated frame is the
translation of a second-order principal answer**, up to typed equality. -/
theorem fibre_answer_in_fibre {M N : List (Binding.MetaArity sig)}
    {K : EquationStore (Binding.ContextualFamily.Observation sig M.get)}
    {τ : (fibre facts roots heads church names realization).obj N ⟶
      (fibre facts roots heads church names realization).obj M}
    (principal : (ContextualDependentEta.frames S.levels).Principal
      ((fibre facts roots heads church names realization).store K) τ) :
    ∃ σ : Binding.ContextualFamily.Assignment (S := sig) M.get N.get,
      SubstEq S.R (metaCtx names M) (metaCtx names N) τ.substitution
        ((fibre facts roots heads church names realization).hom σ).substitution ∧
      (ContextualDependentEta.frames S.levels).Principal
        ((fibre facts roots heads church names realization).store K)
        ((fibre facts roots heads church names realization).hom σ) ∧
      (listFrames sig).Principal (a := M) (m := N) K σ := by
  obtain ⟨σ, equal⟩ := fibre_full facts roots heads algebra complete rigid church names realization
    sortInjective closed τ
  have principal' := principal_of_substEq equal principal
  exact ⟨σ, equal, principal', fibre_principal_reflect facts roots heads algebra complete rigid church
    names realization sortInjective closed @operatorInjective principal'⟩

omit sortInjective closed operatorInjective in
/-- **Which solver results transfer.** A decision of the unifier's frame on a translated store,
given as a principal answer landing in a translated frame or as a certified refutation, is a
decision of the second-order step: a second-order principal answer, or a second-order
refutation. -/
theorem fibre_decision_transfer
    (sortInjective : Function.Injective names.sort) (closed : ClosedRealization (S := S) names)
    (operatorInjective : ∀ {s : sig.Srt}, Function.Injective (names.operator (sort := s)))
    {M : List (Binding.MetaArity sig)} {K : EquationStore (Binding.ContextualFamily.Observation sig M.get)}
    (decided : (∃ (N : List (Binding.MetaArity sig))
        (τ : (fibre facts roots heads church names realization).obj N ⟶
          (fibre facts roots heads church names realization).obj M),
        (ContextualDependentEta.frames S.levels).Principal
          ((fibre facts roots heads church names realization).store K) τ) ∨
      ¬ (ContextualDependentEta.frames S.levels).Solvable
          ((fibre facts roots heads church names realization).store K)) :
    (∃ (N : List (Binding.MetaArity sig))
        (σ : Binding.ContextualFamily.Assignment (S := sig) M.get N.get),
        (listFrames sig).Principal (a := M) (m := N) K σ) ∨
      ¬ (listFrames sig).Solvable (a := M) K := by
  rcases decided with ⟨N, τ, principal⟩ | refuted
  · obtain ⟨σ, _, _, principalSO⟩ := fibre_answer_in_fibre facts roots heads algebra complete rigid
      church names realization sortInjective closed @operatorInjective principal
    exact .inl ⟨N, σ, principalSO⟩
  · exact .inr (fibre_refutation facts roots heads church names realization refuted)

end ContextualDependentFibre
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
