import Mettapedia.Languages.HOLLight.ReferenceBooleanSemantics

/-!
# Finite lists from interpreted source datatype laws

The constructors are closed terms in the receiving model. Separation,
injectivity and full predicate induction are read as formulas about those
terms. Together they determine a constructor-preserving equivalence with Lean
lists. The interpretation does not replace a declared type operator with an
arbitrarily chosen native carrier.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.HOLLight.ListModelCategoricity

open Mettapedia.Logic Mettapedia.Languages.OpenTheory
open ReferenceBooleanSemantics ModelInterpretation

universe w

structure Signature where
  element : HOL.Ty AtomicTy
  sequence : HOL.Ty AtomicTy
  nil : HOL.ClosedTerm Symbol sequence
  cons : HOL.ClosedTerm Symbol (element.arr (sequence.arr sequence))

namespace Signature

variable (signature : Signature)

def separation : HOL.ClosedFormula Symbol :=
  universal (type := signature.element) (universal (type := signature.sequence)
    (negation (.eq
      (.app (.app (HOL.weakenCtx _ signature.cons) (.var (.vs .vz))) (.var .vz))
      (HOL.weakenCtx _ signature.nil))))

def injectivity : HOL.ClosedFormula Symbol :=
  universal (type := signature.element) (universal (type := signature.element)
    (universal (type := signature.sequence) (universal (type := signature.sequence)
      (.eq
        (.eq
          (.app (.app (HOL.weakenCtx _ signature.cons) (.var (.vs (.vs (.vs .vz)))))
            (.var (.vs .vz)))
          (.app (.app (HOL.weakenCtx _ signature.cons) (.var (.vs (.vs .vz)))) (.var .vz)))
        (conjunction (.eq (.var (.vs (.vs (.vs .vz)))) (.var (.vs (.vs .vz))))
          (.eq (.var (.vs .vz)) (.var .vz)))))))

def induction : HOL.ClosedFormula Symbol :=
  universal (type := signature.sequence.arr .prop)
    (implication
      (conjunction (.app (.var .vz) (HOL.weakenCtx _ signature.nil))
        (universal (type := signature.element) (universal (type := signature.sequence)
          (implication (.app (.var (.vs (.vs .vz))) (.var .vz))
            (.app (.var (.vs (.vs .vz)))
              (.app (.app (HOL.weakenCtx _ signature.cons) (.var (.vs .vz))) (.var .vz)))))))
      (universal (type := signature.sequence) (.app (.var (.vs .vz)) (.var .vz))))

abbrev Element (model : HOL.HenkinModel.{0,0,w+1} AtomicTy Symbol) :=
  HOL.Ty.denote.{0,w+1} model.Carrier signature.element

abbrev Carrier (model : HOL.HenkinModel.{0,0,w+1} AtomicTy Symbol) :=
  HOL.Ty.denote.{0,w+1} model.Carrier signature.sequence

def empty (model : HOL.HenkinModel.{0,0,w+1} AtomicTy Symbol) : signature.Carrier model :=
  model.denote signature.nil (fun index => nomatch index)

def prepend (model : HOL.HenkinModel.{0,0,w+1} AtomicTy Symbol) :
    signature.Element model → signature.Carrier model → signature.Carrier model :=
  model.denote signature.cons (fun index => nomatch index)

variable (model : HOL.HenkinModel.{0,0,w+1} AtomicTy Symbol)

theorem denote_nil (valuation : model.Valuation []) :
    model.denote signature.nil valuation = signature.empty model := by
  apply congrArg (model.denote signature.nil)
  funext type index
  exact nomatch index

theorem denote_cons (valuation : model.Valuation []) :
    model.denote signature.cons valuation = signature.prepend model := by
  apply congrArg (model.denote signature.cons)
  funext type index
  exact nomatch index

variable (full : model.FullDomains) (meanings : Meanings model)
include full meanings

theorem separation_meaning : model.models signature.separation ↔
    ∀ head tail, signature.prepend model head tail ≠ signature.empty model := by
  have admitted : ∀ type value, model.adm type value := full
  simp only [separation, HOL.HenkinModel.models, HOL.PreModel.models,
    denote_universal model meanings, denote_negation model meanings,
    HOL.HenkinModel.denote_weakenCtx, HOL.HenkinModel.denote, HOL.PreModel.denote,
    HOL.PreModel.extend, signature.denote_nil model, signature.denote_cons model]
  simp only [model.eqv_iff_eq_of_fullDomains full, admitted, forall_true_left]

theorem injectivity_meaning : model.models signature.injectivity ↔
    ∀ head head' tail tail',
      signature.prepend model head tail = signature.prepend model head' tail' ↔
        head = head' ∧ tail = tail' := by
  have admitted : ∀ type value, model.adm type value := full
  simp only [injectivity, HOL.HenkinModel.models, HOL.PreModel.models,
    denote_universal model meanings, denote_conjunction model meanings,
    HOL.HenkinModel.denote_weakenCtx, HOL.HenkinModel.denote, HOL.PreModel.denote,
    HOL.PreModel.extend, signature.denote_cons model]
  simp only [model.eqv_iff_eq_of_fullDomains full, admitted, forall_true_left]
  rfl

theorem induction_meaning : model.models signature.induction ↔
    ∀ predicate : signature.Carrier model → Prop, predicate (signature.empty model) →
      (∀ head tail, predicate tail → predicate (signature.prepend model head tail)) →
      ∀ value, predicate value := by
  have admitted : ∀ type value, model.adm type value := full
  simp only [induction, HOL.HenkinModel.models, HOL.PreModel.models,
    denote_universal model meanings, denote_implication model meanings,
    denote_conjunction model meanings, HOL.HenkinModel.denote_weakenCtx,
    HOL.HenkinModel.denote, HOL.PreModel.denote, HOL.PreModel.extend,
    signature.denote_nil model, signature.denote_cons model]
  simp only [admitted, forall_true_left]
  constructor
  · intro valid predicate atNil atCons
    exact valid (fun value => ULift.up (predicate value)) ⟨atNil, atCons⟩
  · intro principle predicate premises
    exact principle (fun value => (predicate value).down) premises.1 premises.2

omit full meanings in
def encode : List (signature.Element model) → signature.Carrier model
  | [] => signature.empty model
  | head :: tail => signature.prepend model head (encode tail)

theorem encode_injective
    (separated : model.models signature.separation)
    (injective : model.models signature.injectivity) :
    Function.Injective (signature.encode model) := by
  have sep := (signature.separation_meaning model full meanings).mp separated
  have inj := (signature.injectivity_meaning model full meanings).mp injective
  intro left
  induction left with
  | nil =>
      intro right same
      cases right with
      | nil => rfl
      | cons head tail => exact False.elim (sep head (signature.encode model tail) same.symm)
  | cons head tail ih =>
      intro right same
      cases right with
      | nil => exact False.elim (sep head (signature.encode model tail) same)
      | cons other rest =>
          obtain ⟨heads, tails⟩ := (inj _ _ _ _).mp same
          exact congrArg₂ List.cons heads (ih tails)

theorem encode_surjective (inductionLaw : model.models signature.induction) :
    Function.Surjective (signature.encode model) := by
  apply (signature.induction_meaning model full meanings).mp inductionLaw
    (fun value => ∃ values, signature.encode model values = value)
  · exact ⟨[], rfl⟩
  · intro head tail prior
    obtain ⟨values, same⟩ := prior
    exact ⟨head :: values, congrArg (signature.prepend model head) same⟩

noncomputable def listEquivalence
    (separated : model.models signature.separation)
    (injective : model.models signature.injectivity)
    (inductionLaw : model.models signature.induction) :
    List (signature.Element model) ≃ signature.Carrier model :=
  Equiv.ofBijective (signature.encode model)
    ⟨signature.encode_injective model full meanings separated injective,
      signature.encode_surjective model full meanings inductionLaw⟩

theorem listEquivalence_nil
    (separated : model.models signature.separation)
    (injective : model.models signature.injectivity)
    (inductionLaw : model.models signature.induction) :
    signature.listEquivalence model full meanings separated injective inductionLaw [] =
      signature.empty model := rfl

theorem listEquivalence_cons
    (separated : model.models signature.separation)
    (injective : model.models signature.injectivity)
    (inductionLaw : model.models signature.induction)
    (head : signature.Element model) (tail : List (signature.Element model)) :
    signature.listEquivalence model full meanings separated injective inductionLaw (head :: tail) =
      signature.prepend model head
        (signature.listEquivalence model full meanings separated injective inductionLaw tail) := rfl

omit full meanings in
/-- Constructor preservation determines the encoding on every finite word. -/
theorem encode_unique (reader : List (signature.Element model) → signature.Carrier model)
    (atNil : reader [] = signature.empty model)
    (atCons : ∀ head tail, reader (head :: tail) = signature.prepend model head (reader tail)) :
    reader = signature.encode model := by
  funext values
  induction values with
  | nil => exact atNil
  | cons head tail ih => exact (atCons head tail).trans (congrArg (signature.prepend model head) ih)

end Signature

end Mettapedia.Languages.HOLLight.ListModelCategoricity
