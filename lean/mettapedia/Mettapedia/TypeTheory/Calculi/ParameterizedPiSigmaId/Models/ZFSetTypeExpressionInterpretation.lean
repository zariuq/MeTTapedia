import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
import Mettapedia.Logic.HOL.Embedding.ZFSetTraceProducts
import Mettapedia.Logic.HOL.Embedding.ZFSetTraceProofDecoding
import Mettapedia.SetTheory.ZFSet.OrderedPair

/-!
# Structural set interpretation of scoped type expressions

The input is the existing scoped syntax, not a copied grammar. Products, sums,
identity codes, application, pairs, their projections and reflexivity use
the existing set operations. Heads and declarations are interpretation parameters.

This fragment excludes unannotated lambdas and any expression with an
unsupported operand: a lambda's semantic domain must come from typing
evidence, not from guessing a domain from a trace code. Recognition is not
typing or a semantic soundness certificate.
In particular this function is not an interpretation of all accepted terms.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace ZFSetTypeExpressionInterpretation

open Mettapedia.Logic.HOL.Embedding
open ZFSetDependentProducts (sigmaSet)
open ZFSetTraceProducts (tracePiSet traceApp)
open ZFSetTraceProofDecoding (truthCode)
open Mettapedia.SetTheory

universe u
variable {Head : Type} {n m : Nat}

def supported : {n : Nat} → Tm Head n → Bool
  | _, .var _ | _, .const _ | _, .head _ => true
  | _, .pi a b | _, .sigma a b => supported a && supported b
  | _, .app f a | _, .pair f a => supported f && supported a
  | _, .id a x y => supported a && supported x && supported y
  | _, .refl a => supported a
  | _, .fst p | _, .snd p => supported p
  | _, .lam _ => false

abbrev Environment (n : Nat) := Fin n → ZFSet.{u}

def extend (environment : Environment.{u} n) (value : ZFSet.{u}) : Environment.{u} (n + 1) :=
  Fin.cases value environment

/-- A total function on the explicitly recognized fragment. A missing lambda
annotation never becomes a default set or an assumed semantic value. -/
noncomputable def interpret (heads : Head → ZFSet.{u}) (constants : DeclName → ZFSet.{u}) :
    {n : Nat} → (term : Tm Head n) → supported term = true → Environment.{u} n → ZFSet.{u}
  | _, .var i, _, environment => environment i
  | _, .const c, _, _ => constants c
  | _, .head h, _, _ => heads h
  | _, .pi a b, admitted, environment =>
      tracePiSet (interpret heads constants a (Bool.and_eq_true_iff.mp admitted).1 environment)
        (fun x => interpret heads constants b (Bool.and_eq_true_iff.mp admitted).2 (extend environment x))
  | _, .sigma a b, admitted, environment =>
      sigmaSet (interpret heads constants a (Bool.and_eq_true_iff.mp admitted).1 environment)
        (fun x => interpret heads constants b (Bool.and_eq_true_iff.mp admitted).2 (extend environment x))
  | _, .app f a, admitted, environment =>
      traceApp (interpret heads constants f (Bool.and_eq_true_iff.mp admitted).1 environment)
        (interpret heads constants a (Bool.and_eq_true_iff.mp admitted).2 environment)
  | _, .pair a b, admitted, environment =>
      ZFSet.pair (interpret heads constants a (Bool.and_eq_true_iff.mp admitted).1 environment)
        (interpret heads constants b (Bool.and_eq_true_iff.mp admitted).2 environment)
  | _, .id _ x y, admitted, environment =>
      truthCode (interpret heads constants x (Bool.and_eq_true_iff.mp
        (Bool.and_eq_true_iff.mp admitted).1).2 environment =
        interpret heads constants y (Bool.and_eq_true_iff.mp admitted).2 environment)
  | _, .refl _, _, _ => ∅
  | _, .fst p, admitted, environment =>
      ZFSetOrderedPair.first (interpret heads constants p admitted environment)
  | _, .snd p, admitted, environment =>
      ZFSetOrderedPair.second (interpret heads constants p admitted environment)
  | _, .lam _, admitted, _ =>
      False.elim (Bool.noConfusion admitted)

private theorem freeVariables_agree_under_binder (body : Tm Head (n + 1))
    (left right : Environment.{u} n) (value : ZFSet.{u})
    (agreement : ∀ index, Fin.succ index ∈ body.freeVariables →
      left index = right index) :
    ∀ index, index ∈ body.freeVariables →
      extend left value index = extend right value index := by
  intro index present
  cases index using Fin.cases with
  | zero => rfl
  | succ prior => exact agreement prior present

/-- The set interpretation of a supported term reads only its syntactic free
outer variables. This applies to computed applications, dependent products,
sums and identity codes, not just to variables. The set of free variables is
an over-approximation for constructors whose interpretation discards an
annotation, so no effectful or certificate-dependent term is inferred from
this theorem. -/
theorem interpret_eq_of_freeVariables_agree
    (heads : Head → ZFSet.{u}) (constants : DeclName → ZFSet.{u})
    (term : Tm Head n) (admitted : supported term = true)
    (left right : Environment.{u} n)
    (agreement : ∀ index, index ∈ term.freeVariables → left index = right index) :
    interpret heads constants term admitted left =
      interpret heads constants term admitted right := by
  induction term with
  | var index =>
      exact agreement index (by simp [Tm.freeVariables])
  | const _ | head _ => rfl
  | pi A B ihA ihB | sigma A B ihA ihB =>
      simp only [interpret]
      rw [ihA (Bool.and_eq_true_iff.mp admitted).1 left right
        (by intro index present; exact agreement index (Or.inl present))]
      congr 1
      funext value
      exact ihB (Bool.and_eq_true_iff.mp admitted).2 (extend left value)
        (extend right value)
        (freeVariables_agree_under_binder B left right value
          (by intro index present; exact agreement index (Or.inr present)))
  | app f a ihf iha | pair f a ihf iha =>
      simp only [interpret]
      rw [ihf (Bool.and_eq_true_iff.mp admitted).1 left right
        (by intro index present; exact agreement index (Or.inl present)),
        iha (Bool.and_eq_true_iff.mp admitted).2 left right
          (by intro index present; exact agreement index (Or.inr present))]
  | id A x y _ ihx ihy =>
      simp only [interpret]
      rw [ihx (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp admitted).1).2 left right
        (by intro index present; exact agreement index (Or.inl (Or.inr present))),
        ihy (Bool.and_eq_true_iff.mp admitted).2 left right
          (by intro index present; exact agreement index (Or.inr present))]
  | refl _ _ => rfl
  | fst p ih | snd p ih =>
      simp only [interpret]
      rw [ih admitted left right (by
        intro index present
        exact agreement index (by simpa [Tm.freeVariables] using present))]
  | lam _ _ => exact False.elim (Bool.noConfusion admitted)

theorem supported_rename (rho : Ren n m) (term : Tm Head n) :
    supported (rename rho term) = supported term := by
  induction term generalizing m <;> simp_all [rename, supported]

theorem supported_mapHead {Head' : Type} (map : Head → Head') (term : Tm Head n) :
    supported (term.mapHead map) = supported term := by
  induction term <;> simp_all [Tm.mapHead, supported]

/-- Changing head syntax and then interpreting agrees with composing the
head interpretation. Constants keep their selected interpretation. -/
theorem interpret_mapHead {Head' : Type} (map : Head → Head')
    (heads : Head' → ZFSet.{u}) (constants : DeclName → ZFSet.{u})
    (term : Tm Head n) (admitted : supported term = true)
    (environment : Environment.{u} n) :
    interpret heads constants (term.mapHead map)
      ((supported_mapHead map term).trans admitted) environment =
      interpret (heads ∘ map) constants term admitted environment := by
  induction term with
  | var _ | const _ | head _ => rfl
  | pi a b iha ihb | sigma a b iha ihb =>
      simp only [interpret, Tm.mapHead]
      rw [iha (Bool.and_eq_true_iff.mp admitted).1]
      congr 1
      funext value
      exact ihb (Bool.and_eq_true_iff.mp admitted).2 (extend environment value)
  | app f a ihf iha | pair f a ihf iha =>
      simp only [interpret, Tm.mapHead]
      rw [ihf (Bool.and_eq_true_iff.mp admitted).1,
        iha (Bool.and_eq_true_iff.mp admitted).2]
  | id a x y _ ihx ihy =>
      simp only [interpret, Tm.mapHead]
      rw [ihx (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp admitted).1).2,
        ihy (Bool.and_eq_true_iff.mp admitted).2]
  | refl _ _ => rfl
  | fst p ih | snd p ih =>
      simp only [interpret, Tm.mapHead]
      rw [ih admitted environment]
  | lam _ _ => exact False.elim (Bool.noConfusion admitted)

theorem extend_rename (rho : Ren n m) (environment : Environment.{u} m) (value : ZFSet.{u}) :
    extend environment value ∘ liftRen rho = extend (environment ∘ rho) value := by
  funext index
  refine Fin.cases ?_ (fun _ => ?_) index <;> rfl

/-- Scope transport commutes with the actual set interpretation, including
the dependent product and sum binders. -/
theorem interpret_rename (heads : Head → ZFSet.{u}) (constants : DeclName → ZFSet.{u})
    (term : Tm Head n) (admitted : supported term = true) (rho : Ren n m)
    (environment : Environment.{u} m) :
    interpret heads constants (rename rho term)
      ((supported_rename rho term).trans admitted) environment =
      interpret heads constants term admitted (environment ∘ rho) := by
  induction term generalizing m with
  | var i => rfl
  | const c => rfl
  | head h => rfl
  | pi a b iha ihb =>
      simp only [interpret, rename]
      rw [iha (Bool.and_eq_true_iff.mp admitted).1]
      congr 1
      funext value
      rw [ihb (Bool.and_eq_true_iff.mp admitted).2, extend_rename]
  | sigma a b iha ihb =>
      simp only [interpret, rename]
      rw [iha (Bool.and_eq_true_iff.mp admitted).1]
      congr 1
      funext value
      rw [ihb (Bool.and_eq_true_iff.mp admitted).2, extend_rename]
  | app f a ihf iha => simp only [interpret, rename]; rw [ihf, iha]
  | pair a b iha ihb => simp only [interpret, rename]; rw [iha, ihb]
  | id a x y _ ihx ihy => simp only [interpret, rename]; rw [ihx, ihy]
  | refl a _ => rfl
  | fst p ih | snd p ih =>
      have supportedP : supported p = true := by simpa only [supported] using admitted
      simp only [interpret, rename]
      rw [ih supportedP]
  | lam body _ => exact False.elim (Bool.noConfusion admitted)

theorem supported_liftSub (sigma : Sub Head n m)
    (admitted : ∀ index, supported (sigma index) = true) :
    ∀ index, supported (liftSub sigma index) = true := by
  intro index
  refine Fin.cases rfl (fun prior => ?_) index
  exact (supported_rename wk (sigma prior)).trans (admitted prior)

theorem supported_subst (term : Tm Head n) (admitted : supported term = true)
    (sigma : Sub Head n m) (components : ∀ index, supported (sigma index) = true) :
    supported (subst sigma term) = true := by
  induction term generalizing m with
  | var index => exact components index
  | const _ => rfl
  | head _ => rfl
  | pi a b iha ihb | sigma a b iha ihb =>
      exact Bool.and_eq_true_iff.mpr
        ⟨iha (Bool.and_eq_true_iff.mp admitted).1 sigma components,
          ihb (Bool.and_eq_true_iff.mp admitted).2 (liftSub sigma)
            (supported_liftSub sigma components)⟩
  | app a b iha ihb | pair a b iha ihb =>
      exact Bool.and_eq_true_iff.mpr
        ⟨iha (Bool.and_eq_true_iff.mp admitted).1 sigma components,
          ihb (Bool.and_eq_true_iff.mp admitted).2 sigma components⟩
  | id a x y iha ihx ihy =>
      obtain ⟨⟨ha, hx⟩, hy⟩ := (Bool.and_eq_true_iff.mp admitted).imp_left Bool.and_eq_true_iff.mp
      exact Bool.and_eq_true_iff.mpr
        ⟨Bool.and_eq_true_iff.mpr ⟨iha ha sigma components, ihx hx sigma components⟩,
          ihy hy sigma components⟩
  | refl a iha => exact iha admitted sigma components
  | fst p ih | snd p ih => exact ih admitted sigma components
  | lam _ _ => exact False.elim (Bool.noConfusion admitted)

theorem interpret_liftSub (heads : Head → ZFSet.{u}) (constants : DeclName → ZFSet.{u})
    (sigma : Sub Head n m) (components : ∀ index, supported (sigma index) = true)
    (environment : Environment.{u} m) (value : ZFSet.{u}) :
    (fun index => interpret heads constants (liftSub sigma index)
      (supported_liftSub sigma components index) (extend environment value)) =
      extend (fun index => interpret heads constants (sigma index) (components index) environment)
        value := by
  funext index
  refine Fin.cases rfl (fun prior => ?_) index
  exact interpret_rename heads constants (sigma prior) (components prior) wk
    (extend environment value)

/-- Capture-avoiding simultaneous substitution is interpreted by substituting
the actual set values, not by transporting an independently chosen meaning. -/
theorem interpret_subst (heads : Head → ZFSet.{u}) (constants : DeclName → ZFSet.{u})
    (term : Tm Head n) (admitted : supported term = true)
    (sigma : Sub Head n m) (components : ∀ index, supported (sigma index) = true)
    (environment : Environment.{u} m) :
    interpret heads constants (subst sigma term) (supported_subst term admitted sigma components)
      environment = interpret heads constants term admitted
        (fun index => interpret heads constants (sigma index) (components index) environment) := by
  induction term generalizing m with
  | var _ => rfl
  | const _ => rfl
  | head _ => rfl
  | pi a b iha ihb | sigma a b iha ihb =>
      simp only [subst, interpret]
      rw [iha (Bool.and_eq_true_iff.mp admitted).1 sigma components]
      congr 1
      funext value
      rw [ihb (Bool.and_eq_true_iff.mp admitted).2 (liftSub sigma)
        (supported_liftSub sigma components), interpret_liftSub]
  | app a b iha ihb | pair a b iha ihb =>
      simp only [subst, interpret]
      rw [iha (Bool.and_eq_true_iff.mp admitted).1 sigma components,
        ihb (Bool.and_eq_true_iff.mp admitted).2 sigma components]
  | id a x y _ ihx ihy =>
      simp only [subst, interpret]
      rw [ihx (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp admitted).1).2 sigma components,
        ihy (Bool.and_eq_true_iff.mp admitted).2 sigma components]
  | refl _ _ => rfl
  | fst p ih | snd p ih =>
      simp only [subst, interpret]
      rw [ih admitted sigma components]
  | lam _ _ => exact False.elim (Bool.noConfusion admitted)

theorem lambda_needs_annotation (body : Tm Head (n + 1)) : supported (.lam body) = false := rfl

namespace Controls

def repeatedArgument : Tm Unit 2 := .app (.var 0) (.var 0)

theorem repeatedArgument_supported : supported repeatedArgument = true := by decide

/-- A genuinely computed structural application ignores the second context
entry. The two environments can differ there without changing its value. -/
theorem repeatedArgument_ignores_other_variable (x y z : ZFSet.{u})
    (different : y ≠ z) (constants : DeclName → ZFSet.{u}) :
    extend (extend Fin.elim0 y) x ≠ extend (extend Fin.elim0 z) x ∧
      interpret (fun _ : Unit => x) constants repeatedArgument
        repeatedArgument_supported (extend (extend Fin.elim0 y) x) =
      interpret (fun _ : Unit => x) constants repeatedArgument
        repeatedArgument_supported (extend (extend Fin.elim0 z) x) := by
  constructor
  · intro equal
    exact different (congrFun equal 1)
  · apply interpret_eq_of_freeVariables_agree
    intro index free
    have atArgument : index = 0 := by
      simpa [repeatedArgument, Tm.freeVariables] using free
    subst index
    rfl

/-- Reading the changed context entry does detect the difference. -/
theorem changed_variable_detects_difference (x y z : ZFSet.{u})
    (different : y ≠ z) (constants : DeclName → ZFSet.{u}) :
    interpret (fun _ : Unit => x) constants (.var 1 : Tm Unit 2) (by decide)
      (extend (extend Fin.elim0 y) x) ≠
    interpret (fun _ : Unit => x) constants (.var 1 : Tm Unit 2) (by decide)
      (extend (extend Fin.elim0 z) x) := by
  exact different

/-- Pairs of a point and evidence that it equals the outer variable. -/
def anchoredPairType : Tm Unit 1 :=
  .sigma (.head ()) (.id (.head ()) (.var 1) (.var 0))

def moveAnchor : Sub Unit 1 2 := fun _ => .var 1

theorem anchoredPairType_supported : supported anchoredPairType = true := by decide
theorem moveAnchor_supported : ∀ index, supported (moveAnchor index) = true := fun _ => rfl

/-- Moving the free variable across another context entry and the Sigma
binder retains its original value. -/
theorem substituted_pair_membership (a x y extra : ZFSet.{u})
    (constants : DeclName → ZFSet.{u}) :
    ZFSet.pair y ∅ ∈ interpret (fun _ : Unit => a) constants
      (subst moveAnchor anchoredPairType)
      (supported_subst anchoredPairType anchoredPairType_supported moveAnchor moveAnchor_supported)
      (extend (extend Fin.elim0 x) extra) ↔ y ∈ a ∧ x = y := by
  rw [interpret_subst (fun _ : Unit => a) constants anchoredPairType
    anchoredPairType_supported moveAnchor moveAnchor_supported]
  change ZFSet.pair y ∅ ∈ sigmaSet a (fun point => truthCode (x = point)) ↔ _
  constructor
  · rintro member
    obtain ⟨point, inside, proof, valid, same⟩ := ZFSetDependentProducts.mem_sigmaSet.mp member
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.mp same
    exact ⟨inside, (ZFSetTraceProofDecoding.mem_truthCode _ _).mp valid |>.2⟩
  · rintro ⟨inside, equal⟩
    exact ZFSetDependentProducts.mem_sigmaSet.mpr
      ⟨y, inside, ∅, (ZFSetTraceProofDecoding.mem_truthCode _ _).mpr ⟨rfl, equal⟩, rfl⟩

theorem substituted_pair_accepts_anchor (a x extra : ZFSet.{u})
    (constants : DeclName → ZFSet.{u}) (inside : x ∈ a) :
    ZFSet.pair x ∅ ∈ interpret (fun _ : Unit => a) constants
      (subst moveAnchor anchoredPairType)
      (supported_subst anchoredPairType anchoredPairType_supported moveAnchor moveAnchor_supported)
      (extend (extend Fin.elim0 x) extra) :=
  (substituted_pair_membership a x x extra constants).mpr ⟨inside, rfl⟩

theorem substituted_pair_rejects_capture (a x y extra : ZFSet.{u})
    (constants : DeclName → ZFSet.{u}) (different : x ≠ y) :
    ZFSet.pair y ∅ ∉ interpret (fun _ : Unit => a) constants
      (subst moveAnchor anchoredPairType)
      (supported_subst anchoredPairType anchoredPairType_supported moveAnchor moveAnchor_supported)
      (extend (extend Fin.elim0 x) extra) :=
  fun member => different ((substituted_pair_membership a x y extra constants).mp member).2

def projectedPair : Tm Unit 1 := .pair (.var 0) (.refl (.var 0))

/-- Both projections of a structural pair have fixed values without a
chosen typing certificate. -/
theorem projectedPair_values (heads : Unit → ZFSet.{u})
    (constants : DeclName → ZFSet.{u}) (env : Environment.{u} 1) :
    interpret heads constants (.fst projectedPair) (by decide) env = env 0 ∧
      interpret heads constants (.snd projectedPair) (by decide) env = ∅ := by
  constructor <;> simp [projectedPair, interpret, ZFSetOrderedPair.first_pair,
    ZFSetOrderedPair.second_pair]

/-- A projection does not make an unannotated lambda structurally
interpretable. Its pair operand still needs a meaning from typing evidence. -/
theorem lambda_projection_not_supported :
    supported (.fst (.lam (.var 0) : Tm Unit 0)) = false ∧
      supported (.snd (.lam (.var 0) : Tm Unit 0)) = false := ⟨rfl, rfl⟩

end Controls

#print axioms interpret_rename
#print axioms interpret_eq_of_freeVariables_agree
#print axioms interpret_mapHead
#print axioms interpret_subst
#print axioms Controls.substituted_pair_membership
#print axioms Controls.substituted_pair_rejects_capture
#print axioms Controls.repeatedArgument_ignores_other_variable
#print axioms Controls.changed_variable_detects_difference
#print axioms Controls.projectedPair_values
#print axioms Controls.lambda_projection_not_supported

end ZFSetTypeExpressionInterpretation
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
