import Mettapedia.TypeTheory.ContextualCode

/-!
# A nonidentity exact-code modality model

This module gives the contextual quote/splice interfaces a material graded
model.  Modalities are natural-number code depths under addition.  A positive
depth changes the term representation by adding explicit `ExactCodeLayer`
wrappers, while quotation and splicing retain enough information to satisfy
both beta and eta.

The model is a discriminator, not a proposed language.  It proves that
nonidentity modal structure, substitution-stable contextual code, exact
execution, dependent products, and a small Tarski universe can coexist.  The
separate constant-token counterexample in `ContextualCode` proves that merely
having a code token cannot provide the same execution laws.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.ExactCodeModalityModel

open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.ContextualCode
open Mettapedia.TypeTheory.ModeTheoryProducts
open Mettapedia.TypeTheory.SelectedModalIntroduction

universe u v

/-! ## Exact iterated code -/

/-- One explicit representation layer around a body. -/
structure ExactCodeLayer (Body : Type u) where
  body : Body
  deriving DecidableEq, Repr

/-- Add exactly `depth` representation layers. -/
def ExactCodeIter : Nat -> Type u -> Type u
  | 0, Body => Body
  | depth + 1, Body => ExactCodeLayer (ExactCodeIter depth Body)

/-- Sequential code depths compose by addition. -/
theorem exactCodeIter_add (earlier later : Nat) (Body : Type u) :
    ExactCodeIter (earlier + later) Body =
      ExactCodeIter later (ExactCodeIter earlier Body) := by
  induction later with
  | zero => simp [ExactCodeIter]
  | succ later inductionHypothesis =>
      change ExactCodeLayer (ExactCodeIter (earlier + later) Body) =
        ExactCodeLayer (ExactCodeIter later (ExactCodeIter earlier Body))
      exact congrArg ExactCodeLayer inductionHypothesis

/-- Quote a body through exactly the requested number of code layers. -/
def quoteIter : (depth : Nat) -> {Body : Type u} ->
    Body -> ExactCodeIter depth Body
  | 0, _, body => body
  | depth + 1, _, body => ⟨quoteIter depth body⟩

/-- Splice a body out of exactly the requested number of code layers. -/
def spliceIter : (depth : Nat) -> {Body : Type u} ->
    ExactCodeIter depth Body -> Body
  | 0, _, body => body
  | depth + 1, _, code => spliceIter depth code.body

@[simp] theorem splice_quote (depth : Nat) {Body : Type u} (body : Body) :
    spliceIter depth (quoteIter depth body) = body := by
  induction depth with
  | zero => rfl
  | succ depth inductionHypothesis =>
      exact inductionHypothesis

@[simp] theorem quote_splice (depth : Nat) {Body : Type u}
    (code : ExactCodeIter depth Body) :
    quoteIter depth (spliceIter depth code) = code := by
  induction depth with
  | zero => rfl
  | succ depth inductionHypothesis =>
      cases code with
      | mk nested =>
          change ExactCodeLayer.mk
              (quoteIter depth (spliceIter depth nested)) =
            ExactCodeLayer.mk nested
          rw [inductionHypothesis]

/-- Each iterated code carrier is equivalent to its body carrier. -/
def iterEquiv (depth : Nat) (Body : Type u) :
    ExactCodeIter depth Body ≃ Body where
  toFun := spliceIter depth
  invFun := quoteIter depth
  left_inv := quote_splice depth
  right_inv := splice_quote depth

/-- Exact-code layers preserve equivalences of their represented bodies.
This is representation transport only; it does not identify code execution
with any operational reduction relation. -/
def iterCongrEquiv (depth : Nat) {First : Type u} {Second : Type v}
    (equivalence : First ≃ Second) :
    ExactCodeIter depth First ≃ ExactCodeIter depth Second :=
  (iterEquiv depth First).trans
    (equivalence.trans (iterEquiv depth Second).symm)

/-! ## Additive code modalities -/

/-- The one-object additive mode theory: a modality is its code depth. -/
abbrev modes : ModeTheory := ModeTheoryProducts.Canary.additiveModes

/-- An optional cost grading records the same additive depth.  The grading is
additional structure; the modal laws do not make it the unique cost model. -/
abbrev grading : CostGrading modes :=
  ModeTheoryProducts.Canary.additiveGrading

/-- A small collection of codes used by the model's Tarski universe. -/
inductive SmallCode where
  | empty
  | unit
  | bool
  deriving DecidableEq, Repr

def SmallCode.decode : SmallCode -> Type
  | .empty => Empty
  | .unit => PUnit
  | .bool => Bool

/-- The families CwF with identity context locking and representation-changing
code types graded by the additive modality. -/
def cwf : ModalCwF modes where
  Con := fun _ => Type
  Sub := fun source target => source -> target
  sid := fun _ value => value
  scomp := fun earlier later value => later (earlier value)
  Ty := fun context => context -> Type
  Tm := fun context type => (value : context) -> type value
  tySub := fun type substitution value => type (substitution value)
  tmSub := fun term substitution value => term (substitution value)
  tySub_id := by intros; rfl
  tySub_comp := by intros; rfl
  empty := fun _ => PUnit
  ext := fun context type => Sigma type
  wk := fun _ pair => pair.1
  vz := fun _ pair => pair.2
  sext := fun substitution term value =>
    ⟨substitution value, term value⟩
  pi := fun domain codomain value =>
    (argument : domain value) -> codomain ⟨value, argument⟩
  univ := fun context _ => SmallCode
  el := fun code value => (code value).decode
  lock := fun _ context => context
  boxTy := by
    intro high low depth context type
    exact fun value => ExactCodeIter depth (type value)

namespace Cwf

def lam {context : Type} {domain : context -> Type}
    {codomain : Sigma domain -> Type}
    (body : (value : Sigma domain) -> codomain value) :
    (value : context) ->
      (argument : domain value) -> codomain ⟨value, argument⟩ :=
  fun value argument => body ⟨value, argument⟩

def app {context : Type} {domain : context -> Type}
    {codomain : Sigma domain -> Type}
    (function : (value : context) ->
      (argument : domain value) -> codomain ⟨value, argument⟩)
    (argument : (value : context) -> domain value) :
    (value : context) -> codomain ⟨value, argument value⟩ :=
  fun value => function value (argument value)

end Cwf

def piStructure : PiStructure modes cwf where
  lam := Cwf.lam
  app := Cwf.app
  beta := by intros; rfl
  pi_sub := by intros; rfl
  extensional := by
    intro mode context domain codomain left right pointwise
    funext contextPoint
    funext argument
    have functionsAgree := pointwise
      (Δ := Sigma domain)
      (cwf.wk domain)
      (cwf.vz domain)
    exact congrFun (eq_of_heq functionsAgree) ⟨contextPoint, argument⟩

/-- All contextual, modal, and dependent-product laws hold in the model. -/
def laws : ModalCwFLaws modes cwf where
  scomp_sid_left := by intros; rfl
  scomp_sid_right := by intros; rfl
  scomp_assoc := by intros; rfl
  tmSub_id := by intros; exact HEq.rfl
  tmSub_comp := by intros; exact HEq.rfl
  wk_sext := by intros; rfl
  vz_sext := by intros; exact HEq.rfl
  sext_eta := by
    intro mode context type
    funext value
    rcases value with ⟨base, fibre⟩
    rfl
  piLaws := piStructure
  lockSub := by
    intro high low depth first last substitution
    exact substitution
  lockSub_sid := by intros; rfl
  lockSub_comp := by intros; rfl
  boxTy_natural := by intros; rfl
  lock_id := by intros; rfl
  lock_comp := by intros; rfl
  lockSub_id := by intros; exact HEq.rfl
  lockSub_modal_comp := by intros; exact HEq.rfl
  boxTy_id := by intros; exact HEq.rfl
  boxTy_comp := by
    intro first middle last earlier later context direct nested sameType
    have sameTypes : direct = nested := eq_of_heq sameType
    subst nested
    apply heq_of_eq
    funext value
    exact exactCodeIter_add earlier later (direct value)

/-- The designated empty context, comprehension, and small Tarski universe
also satisfy the semantic coherence laws. -/
def coherence : ModalCwFCoherence modes cwf laws where
  empty_sub_unique := by
    intro mode context left right
    funext value
    cases left value
    cases right value
    rfl
  sext_natural := by intros; rfl
  univ_natural := by intros; rfl
  el_natural := by intros; rfl

/-- Every additive code modality supports quotation and splicing. -/
def selected : WideSubtheory modes := WideSubtheory.all modes

def quotation :
    SelectedQuotationTermStructure modes cwf laws selected where
  introduce := by
    intro high low depth admitted context type term
    exact fun value => quoteIter depth (term value)
  introduce_sub := by intros; exact HEq.rfl
  introduce_id := by intros; exact HEq.rfl

def splicing :
    SelectedSpliceTermStructure modes cwf laws selected where
  splice := by
    intro high low depth admitted context type code
    exact fun value => spliceIter depth (code value)
  splice_sub := by
    intros
    simp [cwf, laws, ModalCwF.castTm]
  splice_id := by intros; exact HEq.rfl

def beta :
    SelectedQuoteSpliceBeta modes cwf laws selected quotation splicing where
  splice_quote := by
    intro high low depth admitted context type term
    funext value
    exact splice_quote depth (term value)

def eta :
    SelectedQuoteSpliceEta modes cwf laws selected quotation splicing where
  quote_splice := by
    intro high low depth admitted context type code
    funext value
    exact quote_splice depth (code value)

/-! ## Nonidentity and exactness controls -/

def oneStep : modes.Hom () () :=
  ModeTheoryProducts.Canary.additiveModality 1

theorem oneStep_not_identity : oneStep ≠ modes.id () := by
  intro same
  change (1 : Nat) = 0 at same
  exact Nat.one_ne_zero same

theorem oneStep_grade_nonzero :
    grading.gradeOf oneStep ≠ grading.unit := by
  intro same
  change (1 : Nat) = 0 at same
  exact Nat.one_ne_zero same

def boolType : cwf.Ty (mode := ()) (PUnit : cwf.Con ()) := fun _ => Bool

def falseTerm : cwf.Tm (mode := ()) (PUnit : cwf.Con ()) boolType :=
  fun _ => false
def trueTerm : cwf.Tm (mode := ()) (PUnit : cwf.Con ()) boolType :=
  fun _ => true

/-- One-step quotation visibly adds a representation constructor. -/
theorem quote_false_has_one_layer :
    quotation.introduce oneStep trivial falseTerm PUnit.unit =
      (ExactCodeLayer.mk false : ExactCodeIter 1 Bool) :=
  rfl

/-- The wrapper retains the body distinction required by executable beta. -/
theorem quoted_false_ne_quoted_true :
    quotation.introduce oneStep trivial falseTerm ≠
      quotation.introduce oneStep trivial trueTerm := by
  intro sameTerms
  have sameCodes := congrFun sameTerms PUnit.unit
  exact Bool.false_ne_true (congrArg ExactCodeLayer.body sameCodes)

/-- The nonidentity one-step code fibre is genuinely equivalent to its body
because both beta and eta hold. -/
def oneStepCodeBodyEquiv :
    cwf.Tm (PUnit : cwf.Con ()) (cwf.boxTy oneStep boolType) ≃
      cwf.Tm (cwf.lock oneStep (PUnit : cwf.Con ())) boolType :=
  beta.codeBodyEquiv eta oneStep trivial

/-- The induced one-step computational-trinity comparison is globally
information preserving in this exact wrapper model. -/
theorem oneStep_comparison_not_loses :
    ¬
      (Mettapedia.Computability.SplitReadoutComparison.comparison
        (beta.readout oneStep trivial
          (context := (PUnit : cwf.Con ())) (type := boolType))).LosesProgramInformation := by
  rw [Mettapedia.Computability.SplitReadoutComparison.not_loses_iff_faithful]
  rw [beta.faithful_iff_quote_splice oneStep trivial]
  exact eta.quote_splice oneStep trivial

theorem oneStep_roundtrip (code :
    cwf.Tm (PUnit : cwf.Con ()) (cwf.boxTy oneStep boolType)) :
    quotation.introduce oneStep trivial
        (splicing.splice oneStep trivial code) = code :=
  eta.quote_splice oneStep trivial code

/-- The exact model and the constant-token obstruction coexist: changing
representation is compatible with execution, while discarding the body is
not. -/
theorem exact_wrapper_not_constant_token :
    Function.Injective
        (quotation.introduce oneStep trivial :
          cwf.Tm (cwf.lock oneStep (PUnit : cwf.Con ())) boolType ->
            cwf.Tm (PUnit : cwf.Con ()) (cwf.boxTy oneStep boolType)) /\
      ¬ (exists splice : PUnit -> Bool,
        forall body : Bool, splice PUnit.unit = body) :=
  ⟨beta.quotation_injective oneStep trivial,
    FibreCanary.constant_token_quotation_has_no_beta_splice⟩

#print axioms exactCodeIter_add
#print axioms splice_quote
#print axioms quote_splice
#print axioms iterEquiv
#print axioms laws
#print axioms coherence
#print axioms beta
#print axioms eta
#print axioms oneStep_not_identity
#print axioms oneStep_grade_nonzero
#print axioms quoted_false_ne_quoted_true
#print axioms oneStepCodeBodyEquiv
#print axioms oneStep_comparison_not_loses
#print axioms exact_wrapper_not_constant_token

end Mettapedia.TypeTheory.ExactCodeModalityModel
