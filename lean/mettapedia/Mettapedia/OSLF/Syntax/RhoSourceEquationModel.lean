import Mettapedia.OSLF.Syntax.BindingEquationExtension
import Mettapedia.OSLF.Syntax.RhoEquationEncoding

/-!
# The source rho equations and their free binding model

The binary-parallel intrinsic presentation first uses commutative-monoid
equations. The Chapter 7 source also identifies `@(*n)` with `n` at the name
sort. These are two distinct equation presentations over the same scoped
syntax. Their model categories, initial models, quotient comparison and
authored-pattern interpretation are related below.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.RhoSourceEquationModel

open CategoryTheory.Limits
open Mettapedia.OSLF.Binding.RhoSchema
open Mettapedia.OSLF.Binding.BindingEquationExtension
open Mettapedia.OSLF.Binding.RhoSchema.IntrinsicEncoding

/-- The ACU axioms occur literally in the complete source equation list. -/
theorem acu_in_source : AxiomInclusion rhoE rhoSourceE := by
  intro i
  fin_cases i
  · exact ⟨0, rfl⟩
  · exact ⟨1, rfl⟩
  · exact ⟨2, rfl⟩

/-- Every source equation, including reflection at the name sort, holds for
all semantic valuations in the quotient binding clone. -/
theorem source_quotient_satisfies :
    BindingEquationInterpretation.Satisfies
      (BindingEquationQuotientModel.algebra rhoSourceE) rhoSourceE :=
  BindingEquationQuotientModel.algebra_satisfies rhoSourceE

/-- The full source equation quotient is initial among binding-clone models
of the complete equation list. -/
noncomputable def source_equation_model_initial :
    IsInitial (FreeBindingEquationModel.presented rhoSourceE) :=
  FreeBindingEquationModel.presentedIsInitial rhoSourceE

/-- Adding the source reflection equation yields a surjective binding-clone
morphism between the two initial models. It preserves input binding and full
equation-class substitution, since it is a binding-clone morphism. -/
noncomputable def acu_to_source :
    (FreeBindingEquationModel.presented rhoE) ⟶
      restrictModel acu_in_source
        (FreeBindingEquationModel.presented rhoSourceE) :=
  comparisonHom acu_in_source

theorem acu_to_source_mk {Γ : Ctx sig} {sort : Srt}
    (term : Term sig Γ sort) :
    acu_to_source.raw.map
        (Quotient.mk _ term : TermQ rhoE Γ sort) =
      (Quotient.mk _ term : TermQ rhoSourceE Γ sort) :=
  comparisonHom_mk acu_in_source term

theorem acu_to_source_surjective {Γ : Ctx sig} {sort : Srt} :
    Function.Surjective
      (fun q : TermQ rhoE Γ sort => acu_to_source.raw.map q) :=
  comparisonHom_surjective acu_in_source

/-! ## The source equation is genuinely additional -/

/-- Count quotation constructors, even beneath input binders and drops. -/
def quoteHeadCount {sort : Srt} : Op sort → Nat
  | .quo => 1
  | _ => 0

mutual
def quoteCount : {Γ : Ctx sig} → {sort : Srt} → Term sig Γ sort → Nat
  | _, _, .var _ => 0
  | _, _, .op op args => quoteHeadCount op + quoteCountArgs args

def quoteCountArgs : {arity : List (List Srt × Srt)} → {Γ : Ctx sig} →
    Args sig arity Γ → Nat
  | _, _, .nil => 0
  | _, _, .cons head tail => quoteCount head + quoteCountArgs tail
end

mutual
/-- An ACU axiom rearranges parallel components without changing their
quotation count, for every closing substitution and continuation body. -/
theorem quoteCount_acu_axiom : ∀ (i : Fin rhoE.length) {Θ Γ : Ctx sig}
    (body : ContextualAssignment sig metas Θ)
    (ambient : Sub sig Θ Γ)
    (close : Sub sig (rhoE.get i).ctx Γ),
    quoteCount (ContextualAssignment.instantiate body ambient close (rhoE.get i).lhs) =
      quoteCount (ContextualAssignment.instantiate body ambient close (rhoE.get i).rhs)
  | ⟨0, _⟩, _, _, body, ambient, close => by
      show quoteCount (ContextualAssignment.instantiate body ambient close commPar.lhs) =
        quoteCount (ContextualAssignment.instantiate body ambient close commPar.rhs)
      simp only [commPar, ContextualAssignment.instantiate, ContextualAssignment.instantiateArgs,
        liftSub, quoteCount, quoteCountArgs, quoteHeadCount]
      omega
  | ⟨1, _⟩, _, _, body, ambient, close => by
      show quoteCount (ContextualAssignment.instantiate body ambient close assocPar.lhs) =
        quoteCount (ContextualAssignment.instantiate body ambient close assocPar.rhs)
      simp only [assocPar, ContextualAssignment.instantiate, ContextualAssignment.instantiateArgs,
        liftSub, quoteCount, quoteCountArgs, quoteHeadCount]
      omega
  | ⟨2, _⟩, _, _, body, ambient, close => by
      show quoteCount (ContextualAssignment.instantiate body ambient close rightUnitPar.lhs) =
        quoteCount (ContextualAssignment.instantiate body ambient close rightUnitPar.rhs)
      simp only [rightUnitPar, ContextualAssignment.instantiate, ContextualAssignment.instantiateArgs,
        liftSub, quoteCount, quoteCountArgs, quoteHeadCount]
      omega
  | ⟨_ + 3, h⟩, _, _, _, _, _ => by simp [rhoE] at h

/-- The quotation count is invariant under the entire ACU congruence,
including congruence below an input binder. -/
theorem quoteCount_eqClosure : ∀ {Γ : Ctx sig} {sort : Srt}
    {left right : Term sig Γ sort},
    EqClosure rhoE left right → quoteCount left = quoteCount right
  | _, _, _, _, .ax i body ambient ordinary => quoteCount_acu_axiom i body ambient ordinary
  | _, _, _, _, .refl _ => rfl
  | _, _, _, _, .symm h => (quoteCount_eqClosure h).symm
  | _, _, _, _, .trans h h' =>
      (quoteCount_eqClosure h).trans (quoteCount_eqClosure h')
  | _, _, _, _, .cong _ h => by
      simp only [quoteCount, quoteCountArgs_eqClosure h]

theorem quoteCountArgs_eqClosure : ∀ {arity : List (List Srt × Srt)}
    {Γ : Ctx sig} {left right : Args sig arity Γ},
    EqArgs rhoE left right → quoteCountArgs left = quoteCountArgs right
  | _, _, _, _, .nil => rfl
  | _, _, _, _, .cons head tail => by
      simp only [quoteCountArgs, quoteCount_eqClosure head,
        quoteCountArgs_eqClosure tail]
end

/-- The name variable in the source QuoteDrop axiom. -/
def nameVariable : Term sig [Srt.nm] Srt.nm := .var .zero

/-- The left side of the Chapter 7 name-sorted reflection equation. -/
def quotedDroppedName : Term sig [Srt.nm] Srt.nm :=
  .op Op.quo (.cons (.op Op.drp (.cons nameVariable .nil)) .nil)

theorem quote_drop_source_equation :
    EqClosure rhoSourceE quotedDroppedName nameVariable := by
  simpa [rhoSourceE, quotedDroppedName, nameVariable, quoteDrop,
    instantiate, instantiateArgs, bind, bindArgs, liftSub] using
    (EqClosure.ax_closed (E := rhoSourceE) (Γ := [Srt.nm]) 3 contDiscard
      (fun _ v => Term.var v))

/-- ACU alone does not derive the source's name reflection equation. -/
theorem quote_drop_not_acu :
    ¬ EqClosure rhoE quotedDroppedName nameVariable := by
  intro h
  have counts := quoteCount_eqClosure h
  simp [quotedDroppedName, nameVariable, quoteCount,
    quoteCountArgs, quoteHeadCount] at counts

theorem quote_drop_distinct_in_acu :
    (Quotient.mk _ quotedDroppedName : TermQ rhoE [Srt.nm] Srt.nm) ≠
      Quotient.mk _ nameVariable := by
  intro h
  exact quote_drop_not_acu (Quotient.exact h)

/-- The source reflection equation identifies two genuinely different ACU
classes. Hence adding it is a proper quotient, even though the comparison is
surjective and preserves all binding-clone operations. -/
theorem acu_to_source_not_injective :
    ¬ Function.Injective
      (fun q : TermQ rhoE [Srt.nm] Srt.nm => acu_to_source.raw.map q) := by
  intro injective
  have equalImages :
      acu_to_source.raw.map
          (Quotient.mk _ quotedDroppedName : TermQ rhoE [Srt.nm] Srt.nm) =
        acu_to_source.raw.map
          (Quotient.mk _ nameVariable : TermQ rhoE [Srt.nm] Srt.nm) := by
    rw [acu_to_source_mk, acu_to_source_mk]
    exact Quotient.sound quote_drop_source_equation
  exact quote_drop_distinct_in_acu (injective equalImages)

/-! ## Comparison with the actual authored pattern equations -/

/-- The canonical authored image of an ACU class. Its soundness follows from
the proved inclusion of ACU in the complete source equations. -/
def encodeACUClass {Γ : Ctx sig} {sort : Srt} :
    TermQ rhoE Γ sort → Mettapedia.OSLF.MeTTaIL.Syntax.Pattern :=
  Quotient.lift
    (fun term =>
      Mettapedia.Languages.ProcessCalculi.RhoCalculus.Canonical.canonicalize
        (encodeTerm term))
    (fun _ _ h => eqClosure_encoded_canonical
      (eqClosure_of_axiom_inclusion acu_in_source h))

/-- The authored canonical image of the weaker quotient factors through the
proper source-equation quotient, at every sorted context. -/
theorem encodeACUClass_factors {Γ : Ctx sig} {sort : Srt}
    (q : TermQ rhoE Γ sort) :
    encodeACUClass q = encodeEquationClass (acu_to_source.raw.map q) := by
  induction q using Quotient.inductionOn with
  | _ term =>
      rw [acu_to_source_mk]
      rfl

end Mettapedia.OSLF.Binding.RhoSourceEquationModel
