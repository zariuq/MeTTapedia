import Mettapedia.OSLF.Syntax.RhoSubstitutionEncoding
import Mettapedia.OSLF.Syntax.RhoDropProfile
import Mettapedia.OSLF.Syntax.EquationalQuotient
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Canonical

/-!
# Equations respected by the intrinsic-to-authored rho encoding

Every authored intrinsic ACU and QuoteDrop equation maps to the corresponding
canonical structural congruence, including under arbitrary constructors and
input binders. The encoded image is hash-set free, so canonicalization is
constant on each intrinsic equation class. This gives a well-defined map from
the intrinsic quotient; no injectivity, surjectivity or operational comparison
is inferred from that fact alone.
-/

namespace Mettapedia.OSLF.Binding.RhoSchema.IntrinsicEncoding

open Mettapedia.Languages.ProcessCalculi.RhoCalculus
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefRewriteSystem
open Mettapedia.OSLF.Framework.ConstructorCategory
open Mettapedia.OSLF.MeTTaIL.Syntax

set_option autoImplicit false

/-- Each intrinsic source equation is respected by the actual authored
structural congruence, for every substitution of its variables. -/
theorem sourceAxiom_encoded_SC : ∀ (i : Fin rhoSourceE.length)
    {Θ Γ : Ctx sig}
    (body : ContextualAssignment sig metas Θ)
    (ambient : Sub sig Θ Γ)
    (close : Sub sig (rhoSourceE.get i).ctx Γ),
    StructuralCongruence
      (encodeTerm (ContextualAssignment.instantiate body ambient close (rhoSourceE.get i).lhs))
      (encodeTerm (ContextualAssignment.instantiate body ambient close (rhoSourceE.get i).rhs))
  | ⟨0, _⟩, _, _, body, ambient, close => by
      simpa [rhoSourceE, commPar, ContextualAssignment.instantiate, ContextualAssignment.instantiateArgs,
        bind, bindArgs, liftSub, encodeTerm, encodeArgs, wrapBinders]
        using StructuralCongruence.par_comm
          (encodeTerm (close Srt.pr Var.zero))
          (encodeTerm (close Srt.pr (Var.succ Var.zero)))
  | ⟨1, _⟩, _, _, body, ambient, close => by
      simpa [rhoSourceE, assocPar, ContextualAssignment.instantiate, ContextualAssignment.instantiateArgs,
        bind, bindArgs, liftSub, encodeTerm, encodeArgs, wrapBinders]
        using StructuralCongruence.par_assoc
          (encodeTerm (close Srt.pr Var.zero))
          (encodeTerm (close Srt.pr (Var.succ Var.zero)))
          (encodeTerm (close Srt.pr (Var.succ (Var.succ Var.zero))))
  | ⟨2, _⟩, _, _, body, ambient, close => by
      simpa [rhoSourceE, rightUnitPar, ContextualAssignment.instantiate, ContextualAssignment.instantiateArgs,
        bind, bindArgs, liftSub, encodeTerm, encodeArgs, wrapBinders]
        using StructuralCongruence.par_nil_right
          (encodeTerm (close Srt.pr Var.zero))
  | ⟨3, _⟩, _, _, body, ambient, close => by
      simpa [rhoSourceE, quoteDrop, ContextualAssignment.instantiate, ContextualAssignment.instantiateArgs,
        bind, bindArgs, liftSub, encodeTerm, encodeArgs, wrapBinders]
        using StructuralCongruence.quote_drop
          (encodeTerm (close Srt.nm Var.zero))
  | ⟨_ + 4, h⟩, _, _, _, _, _ => by simp [rhoSourceE] at h

/-- Pointwise structural congruence remains valid under the encoded binder list. -/
theorem wrapBinders_SC (bs : List Srt) {left right : Pattern}
    (equivalent : StructuralCongruence left right) :
    StructuralCongruence (wrapBinders bs left) (wrapBinders bs right) := by
  induction bs with
  | nil => exact equivalent
  | cons binder rest ih =>
      exact StructuralCongruence.lambda_cong none _ _ ih

mutual
/-- The interpretation respects the entire intrinsic equational closure,
including congruence below input binders. -/
theorem eqClosure_encoded_SC : ∀ {Γ : Ctx sig} {s : Srt}
    {left right : Term sig Γ s}, EqClosure rhoSourceE left right →
      StructuralCongruence (encodeTerm left) (encodeTerm right)
  | _, _, _, _, .ax i body ambient ordinary => sourceAxiom_encoded_SC i body ambient ordinary
  | _, _, _, _, .refl t => .refl _
  | _, _, _, _, .symm h => .symm _ _ (eqClosure_encoded_SC h)
  | _, _, _, _, .trans h h' =>
      .trans _ _ _ (eqClosure_encoded_SC h) (eqClosure_encoded_SC h')
  | _, _, _, _, .cong o h => by
      have argsSC := eqArgs_encoded_SC h
      have lengthEq := argsSC.length_eq
      have pointwise : ∀ i h₁ h₂,
          StructuralCongruence
            ((encodeArgs _).get ⟨i, h₁⟩)
            ((encodeArgs _).get ⟨i, h₂⟩) :=
        fun i h₁ h₂ => argsSC.get h₁ h₂
      cases o with
      | nil => exact .refl _
      | par => exact .par_cong _ _ lengthEq pointwise
      | out => exact .apply_cong "POutput" _ _ lengthEq pointwise
      | inp => exact .apply_cong "PInput" _ _ lengthEq pointwise
      | quo => exact .apply_cong "NQuote" _ _ lengthEq pointwise
      | drp => exact .apply_cong "PDrop" _ _ lengthEq pointwise

/-- The argument-wise induction accompanying `eqClosure_encoded_SC`. -/
theorem eqArgs_encoded_SC : ∀ {ars : List (List Srt × Srt)}
    {Γ : Ctx sig} {left right : Args sig ars Γ},
    EqArgs rhoSourceE left right →
      List.Forall₂ StructuralCongruence (encodeArgs left) (encodeArgs right)
  | _, _, _, _, .nil => .nil
  | _, _, _, _, .cons (bs := bs) head tail =>
      .cons (wrapBinders_SC bs (eqClosure_encoded_SC head))
        (eqArgs_encoded_SC tail)
end

/-- Encoding binders does not introduce the extended-rho set constructor. -/
theorem hashSetFree_wrapBinders (bs : List Srt) (body : Pattern)
    (pure : Canonical.HashSetFree body) :
    Canonical.HashSetFree (wrapBinders bs body) := by
  induction bs with
  | nil => exact pure
  | cons _ bs ih =>
      simpa [wrapBinders, Canonical.HashSetFree] using ih

mutual
/-- Every encoded intrinsic term belongs to the pure-rho fragment required by
the canonicalization soundness theorem. -/
theorem encodedTerm_hashSetFree : ∀ {Γ : Ctx sig} {s : Srt}
    (term : Term sig Γ s), Canonical.HashSetFree (encodeTerm term)
  | _, _, .var _ => trivial
  | _, _, .op .nil .nil => trivial
  | _, _, .op .par args => encodedArgs_hashSetFree args
  | _, _, .op .out args => encodedArgs_hashSetFree args
  | _, _, .op .inp args => encodedArgs_hashSetFree args
  | _, _, .op .quo args => encodedArgs_hashSetFree args
  | _, _, .op .drp args => encodedArgs_hashSetFree args

/-- Pure-fragment preservation for encoded argument vectors. -/
theorem encodedArgs_hashSetFree : ∀ {ars : List (List Srt × Srt)}
    {Γ : Ctx sig} (args : Args sig ars Γ),
    Canonical.HashSetFreeList (encodeArgs args)
  | _, _, .nil => trivial
  | _, _, .cons (bs := bs) head tail => by
      simp only [encodeArgs, Canonical.HashSetFreeList]
      exact ⟨hashSetFree_wrapBinders bs _ (encodedTerm_hashSetFree head),
        encodedArgs_hashSetFree tail⟩
end

/-- Intrinsic equation-equivalent terms have identical authored canonical
representatives. This is soundness, not reflection. -/
theorem eqClosure_encoded_canonical {Γ : Ctx sig} {s : Srt}
    {left right : Term sig Γ s} (equivalent : EqClosure rhoSourceE left right) :
    Canonical.canonicalize (encodeTerm left) =
      Canonical.canonicalize (encodeTerm right) :=
  Canonical.canonicalize_eq_of_structuralCongruence
    (eqClosure_encoded_SC equivalent)
    (encodedTerm_hashSetFree left) (encodedTerm_hashSetFree right)

/-- Authored pattern substitution of encoded representatives respects every
intrinsic equation after canonicalization. The proof uses exact raw
substitution commutation and intrinsic equation closure under substitution. -/
theorem encodedSubstitute_respects_equation {Γ Δ : Ctx sig} {s : Srt}
    (sigma : Sub sig Γ Δ) {left right : Term sig Γ s}
    (equivalent : EqClosure rhoSourceE left right) :
    Canonical.canonicalize
        (Mettapedia.OSLF.MeTTaIL.ContextSubstitution.substitute
          (encodeSub sigma) (encodeTerm left)) =
      Canonical.canonicalize
        (Mettapedia.OSLF.MeTTaIL.ContextSubstitution.substitute
          (encodeSub sigma) (encodeTerm right)) := by
  rw [← encodeTerm_bind sigma left, ← encodeTerm_bind sigma right]
  exact eqClosure_encoded_canonical (eqClosure_bind sigma equivalent)

/-- The sound comparison map out of intrinsic equation classes. Its codomain
is raw canonical patterns because quote-safe admission must be established
separately. -/
def encodeEquationClass {Γ : Ctx sig} {s : Srt} :
    TermQ rhoSourceE Γ s → Pattern :=
  Quotient.lift (fun term => Canonical.canonicalize (encodeTerm term))
    (fun _ _ equivalent => eqClosure_encoded_canonical equivalent)

theorem encodeEquationClass_mk {Γ : Ctx sig} {s : Srt}
    (term : Term sig Γ s) :
    encodeEquationClass (Quotient.mk (eqSetoid rhoSourceE Γ s) term) =
      Canonical.canonicalize (encodeTerm term) := rfl

/-- Applying the existing pattern substitution to raw representatives gives
a well-defined canonical pattern on intrinsic equation classes. This is a
quotient lift, not an asserted action on arbitrary canonical patterns. -/
def encodeSubstitutedEquationClass {Γ Δ : Ctx sig} {s : Srt}
    (sigma : Sub sig Γ Δ) : TermQ rhoSourceE Γ s → Pattern :=
  Quotient.lift
    (fun term => Canonical.canonicalize
      (Mettapedia.OSLF.MeTTaIL.ContextSubstitution.substitute
        (encodeSub sigma) (encodeTerm term)))
    (fun _ _ equivalent => encodedSubstitute_respects_equation sigma equivalent)

/-- The representative-level authored substitution and the intrinsic
quotient substitution have the same canonical image. -/
theorem encodeSubstitutedEquationClass_eq {Γ Δ : Ctx sig} {s : Srt}
    (sigma : Sub sig Γ Δ) (q : TermQ rhoSourceE Γ s) :
    encodeSubstitutedEquationClass sigma q =
      encodeEquationClass (bindQ sigma q) := by
  induction q using Quotient.inductionOn with
  | _ term =>
      change Canonical.canonicalize
          (Mettapedia.OSLF.MeTTaIL.ContextSubstitution.substitute
            (encodeSub sigma) (encodeTerm term)) =
        Canonical.canonicalize (encodeTerm (bind sigma term))
      rw [encodeTerm_bind]

/-- Contracting the name-sorted quote/drop equation beneath an input binder
removes the quotation that made `crossingQuote` inadmissible. -/
def crossingQuoteRepaired : Term sig [] Srt.pr :=
  .op Op.inp (.cons chan
    (.cons (.op Op.drp (.cons (.var Var.zero) .nil)) .nil))

theorem crossingQuote_equation_repair :
    EqClosure rhoSourceE crossingQuote crossingQuoteRepaired := by
  have nameEquation : EqClosure rhoSourceE
      (Term.op (S := sig) (Γ := [Srt.nm]) Op.quo
        (.cons (.op Op.drp (.cons (.var Var.zero) .nil)) .nil))
      (.var Var.zero) :=
    EqClosure.ax_closed (E := rhoSourceE) (Γ := [Srt.nm]) 3 contDiscard
      (fun _ v => .var v)
  have processEquation : EqClosure rhoSourceE
      (Term.op (S := sig) (Γ := [Srt.nm]) Op.drp
        (.cons (.op Op.quo
          (.cons (.op Op.drp (.cons (.var Var.zero) .nil)) .nil)) .nil))
      (.op Op.drp (.cons (.var Var.zero) .nil)) :=
    EqClosure.cong (E := rhoSourceE) Op.drp (.cons nameEquation .nil)
  exact EqClosure.cong (E := rhoSourceE) Op.inp
    (.cons (.refl chan) (.cons processEquation .nil))

theorem crossingQuoteRepaired_safe :
    intrinsicQuoteSafe 0 crossingQuoteRepaired = true := by
  decide +kernel

/-- Quote safety is not a property of intrinsic equation classes: the two
closed terms are equated by the authored reflection law, but only one is
admitted by the canonical raw quotation-scope check. -/
theorem quoteSafety_not_equation_invariant :
    EqClosure rhoSourceE crossingQuote crossingQuoteRepaired ∧
    intrinsicQuoteSafe 0 crossingQuote = false ∧
    intrinsicQuoteSafe 0 crossingQuoteRepaired = true :=
  ⟨crossingQuote_equation_repair,
    crossingQuote_intrinsically_unsafe, crossingQuoteRepaired_safe⟩

theorem crossingQuote_same_class :
    (Quotient.mk (eqSetoid rhoSourceE [] Srt.pr) crossingQuote :
      TermQ rhoSourceE [] Srt.pr) =
    Quotient.mk (eqSetoid rhoSourceE [] Srt.pr) crossingQuoteRepaired :=
  Quotient.sound crossingQuote_equation_repair

/-- A quotient class is admissible when it has at least one raw representative
passing the authored quotation boundary. This is the saturated, genuinely
quotient-level replacement for the non-invariant raw predicate. -/
def HasQuoteSafeRepresentative {s : Srt}
    (q : TermQ rhoSourceE [] s) : Prop :=
  ∃ term : Term sig [] s,
    Quotient.mk (eqSetoid rhoSourceE [] s) term = q ∧
      intrinsicQuoteSafe 0 term = true

/-- Membership of a represented class is precisely saturation of raw quote
safety under the intrinsic equation closure. -/
theorem quoteSafeClass_mk_iff {s : Srt} (term : Term sig [] s) :
    HasQuoteSafeRepresentative
      (Quotient.mk (eqSetoid rhoSourceE [] s) term) ↔
    ∃ equivalent : Term sig [] s,
      EqClosure rhoSourceE term equivalent ∧
        intrinsicQuoteSafe 0 equivalent = true := by
  constructor
  · rintro ⟨equivalent, equality, safe⟩
    exact ⟨equivalent, Quotient.exact equality.symm, safe⟩
  · rintro ⟨equivalent, equation, safe⟩
    exact ⟨equivalent, (Quotient.sound equation).symm, safe⟩

theorem quoteSafeClass_of_raw {s : Srt} (term : Term sig [] s)
    (safe : intrinsicQuoteSafe 0 term = true) :
    HasQuoteSafeRepresentative
      (Quotient.mk (eqSetoid rhoSourceE [] s) term) :=
  ⟨term, rfl, safe⟩

/-- The unsafe raw term nevertheless belongs to an admissible equation class,
because reflection contracts it to the quote-safe representative. -/
theorem crossingQuote_class_has_safe_representative :
    HasQuoteSafeRepresentative
      (Quotient.mk (eqSetoid rhoSourceE [] Srt.pr) crossingQuote) :=
  ⟨crossingQuoteRepaired, crossingQuote_same_class.symm,
    crossingQuoteRepaired_safe⟩

/-- The saturated process quotient maps into the actual declaration-derived
closed process carrier. The pattern component is independent of which safe
representative witnesses membership. -/
def encodeQuoteSafeProcessClass
    (q : {qClass : TermQ rhoSourceE [] Srt.pr //
      HasQuoteSafeRepresentative qClass}) : RhoClosedTerm rhoProc := by
  refine ⟨encodeEquationClass q.1, ?_⟩
  obtain ⟨term, represented, safe⟩ := q.2
  rw [← represented, encodeEquationClass_mk]
  exact (RhoClosedTerm.canonicalize (encodeClosedProcess term safe)).2

/-- The same saturated quotient comparison at the name sort. -/
def encodeQuoteSafeNameClass
    (q : {qClass : TermQ rhoSourceE [] Srt.nm //
      HasQuoteSafeRepresentative qClass}) : RhoClosedTerm rhoName := by
  refine ⟨encodeEquationClass q.1, ?_⟩
  obtain ⟨term, represented, safe⟩ := q.2
  rw [← represented, encodeEquationClass_mk]
  exact (RhoClosedTerm.canonicalize (encodeClosedName term safe)).2

@[simp] theorem encodeQuoteSafeProcessClass_pattern
    (q : {qClass : TermQ rhoSourceE [] Srt.pr //
      HasQuoteSafeRepresentative qClass}) :
    (encodeQuoteSafeProcessClass q).1 = encodeEquationClass q.1 := rfl

@[simp] theorem encodeQuoteSafeNameClass_pattern
    (q : {qClass : TermQ rhoSourceE [] Srt.nm //
      HasQuoteSafeRepresentative qClass}) :
    (encodeQuoteSafeNameClass q).1 = encodeEquationClass q.1 := rfl

/-- The repaired quotient class lands in the authored closed carrier even
though its original raw representative does not. -/
theorem crossingQuote_class_image_admitted :
    RhoClosedTermWellSorted rhoProc
      (encodeEquationClass
        (Quotient.mk (eqSetoid rhoSourceE [] Srt.pr) crossingQuote)) :=
  (encodeQuoteSafeProcessClass
    ⟨_, crossingQuote_class_has_safe_representative⟩).2

/-- No predicate on intrinsic equation classes can recognize precisely the
raw representatives passing the canonical quotation-scope check. -/
theorem no_raw_quoteSafety_predicate_on_equation_classes :
    ¬ ∃ admitted : TermQ rhoSourceE [] Srt.pr → Prop,
      ∀ term : Term sig [] Srt.pr,
        admitted (Quotient.mk (eqSetoid rhoSourceE [] Srt.pr) term) ↔
          intrinsicQuoteSafe 0 term = true := by
  rintro ⟨admitted, exactness⟩
  have repairedAdmitted := (exactness crossingQuoteRepaired).mpr
    crossingQuoteRepaired_safe
  have crossingAdmitted :
      admitted (Quotient.mk (eqSetoid rhoSourceE [] Srt.pr) crossingQuote) := by
    rw [crossingQuote_same_class]
    exact repairedAdmitted
  have crossingSafe := (exactness crossingQuote).mp crossingAdmitted
  rw [crossingQuote_intrinsically_unsafe] at crossingSafe
  cases crossingSafe

theorem crossingQuoteRepaired_admitted :
    Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefRewriteSystem.RhoClosedTermWellSorted
      Mettapedia.OSLF.Framework.ConstructorCategory.rhoProc
      (encodeTerm crossingQuoteRepaired) :=
  (encoded_process_admitted_iff_quoteSafe crossingQuoteRepaired).mpr
    crossingQuoteRepaired_safe

/-- The quotient map identifies the inadmissible raw representative with the
admissible one; admission of raw representatives cannot define its codomain. -/
theorem crossingQuote_same_equation_class_image :
    encodeEquationClass
        (Quotient.mk (eqSetoid rhoSourceE [] Srt.pr) crossingQuote) =
      encodeEquationClass
        (Quotient.mk (eqSetoid rhoSourceE [] Srt.pr) crossingQuoteRepaired) := by
  exact eqClosure_encoded_canonical crossingQuote_equation_repair

end Mettapedia.OSLF.Binding.RhoSchema.IntrinsicEncoding
