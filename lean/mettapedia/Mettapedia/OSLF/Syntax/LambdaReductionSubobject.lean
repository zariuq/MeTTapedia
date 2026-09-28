import Mettapedia.OSLF.Syntax.BinderLocalPremise
import Mettapedia.OSLF.Syntax.StableRewriteRelationBoundary
import Mathlib.CategoryTheory.Subfunctor.Subobject

/-!
# The least scoped reduction subobject for the Chapter 7 lambda rules

The source's beta and three congruence rules generate a relation on pairs
of terms in every variable context. The relation is stable under simultaneous
substitution, so it is a subfunctor of the term-pair presheaf. Its universal
property below is least closure under the four rules among such subfunctors.
This is an operational subobject in the presheaf model, not the free finite-
limit cartesian-closed classifying category of the whole presentation.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.LambdaReductionSubobject

open CategoryTheory
open Mettapedia.OSLF.Binding.LambdaContextualRung
open Mettapedia.OSLF.Binding.BinderLocalPremise

private def ctx (Γ : Ctx sig) : (Syntactic.Ctxt sig)ᵒᵖ :=
  Opposite.op ⟨Γ⟩

private def pair {Γ : Ctx sig}
    (source target : Term sig Γ .term) : rootPairs sig Γ :=
  ⟨.term, source, target⟩

/-- The exact source reduction predicate, at each substitution context. -/
def reduction : Subfunctor (rootPairsPresheaf sig) where
  obj X := { p | match p with
    | ⟨.term, source, target⟩ => LambdaContextualRung.Step X.unop.vars source target }
  map := by
    intro X Y substitution p step
    rcases p with ⟨sort, source, target⟩
    cases sort
    exact LambdaContextualRung.substitute substitution.unop step

/-- Membership is precisely the four-rule inductive judgment, with no
extra equation or execution rule hidden in the presheaf packaging. -/
theorem member_iff_step {Γ : Ctx sig}
    (source target : Term sig Γ .term) :
    pair source target ∈ (reduction.obj (ctx Γ)) ↔ LambdaContextualRung.Step Γ source target :=
  Iff.rfl

/-- This is a genuine categorical subobject of the pair presheaf. -/
def categoricalSubobject : Subobject (rootPairsPresheaf sig) :=
  Subobject.mk reduction.ι

/-- A contextual family of endpoint pairs factors through the actual
reduction mono exactly when every one of its observations is a source-step.
This is the represented-relation law needed by semantic consumers; mere
substitution stability would not have supplied such a mono. -/
theorem factors_iff_pointwise_steps
    (test : (Syntactic.Ctxt sig)ᵒᵖ ⥤ Type)
    (endpoints : test ⟶ rootPairsPresheaf sig) :
    categoricalSubobject.Factors endpoints ↔
      ∀ (X : (Syntactic.Ctxt sig)ᵒᵖ) (point : test.obj X),
        (match endpoints.app X point with
          | ⟨.term, source, target⟩ =>
              LambdaContextualRung.Step X.unop.vars source target) := by
  exact StableRewriteRelationBoundary.subfunctor_factors_iff_pointwise
    reduction endpoints

/-- Membership in an arbitrary candidate subfunctor at one sorted pair. -/
def Holds (R : Subfunctor (rootPairsPresheaf sig)) {Γ : Ctx sig}
    (source target : Term sig Γ .term) : Prop :=
  pair source target ∈ R.obj (ctx Γ)

/-- The four source rules, now as closure requirements on an actual
subfunctor of term pairs. Binder congruence asks for the premise in the
extended context, rather than at the rule root. -/
structure RespectsRules (R : Subfunctor (rootPairsPresheaf sig)) : Prop where
  beta : ∀ {Γ : Ctx sig} (body : Term sig (.term :: Γ) .term)
    (arg : Term sig Γ .term),
    Holds R (appT (lamT body) arg) (inst body arg)
  appCongL : ∀ {Γ : Ctx sig} {source target : Term sig Γ .term}
    (arg : Term sig Γ .term),
    Holds R source target →
    Holds R (appT source arg) (appT target arg)
  appCongR : ∀ {Γ : Ctx sig} {source target : Term sig Γ .term}
    (funTerm : Term sig Γ .term),
    Holds R source target →
    Holds R (appT funTerm source) (appT funTerm target)
  lamCong : ∀ {Γ : Ctx sig}
    {source target : Term sig (.term :: Γ) .term},
    Holds R source target → Holds R (lamT source) (lamT target)

/-- The induced reduction subobject satisfies exactly the generating rules. -/
theorem reduction_respectsRules : RespectsRules reduction where
  beta body arg := LambdaContextualRung.Step.beta body arg
  appCongL arg step := LambdaContextualRung.Step.appCongL arg step
  appCongR funTerm step := LambdaContextualRung.Step.appCongR funTerm step
  lamCong step := LambdaContextualRung.Step.lamCong step

/-- Induction on the source derivation proves leastness against every
substitution-stable relation that validates the four rules. -/
theorem reduction_le_of_respectsRules
    (R : Subfunctor (rootPairsPresheaf sig))
    (laws : RespectsRules R) : reduction ≤ R := by
  intro X p member
  rcases p with ⟨sort, source, target⟩
  cases sort
  change LambdaContextualRung.Step X.unop.vars source target at member
  have go : ∀ {Γ : Ctx sig} {left right : Term sig Γ .term},
      LambdaContextualRung.Step Γ left right → Holds R left right := by
    intro Γ left right step
    induction step with
    | beta body arg => exact laws.beta body arg
    | appCongL arg _ inductionHypothesis =>
        exact laws.appCongL arg inductionHypothesis
    | appCongR funTerm _ inductionHypothesis =>
        exact laws.appCongR funTerm inductionHypothesis
    | lamCong _ inductionHypothesis =>
        exact laws.lamCong inductionHypothesis
  exact go member

/-- The least subfunctor satisfying the source rules is their intersection.
The intersection is nonempty because the generated reduction itself satisfies
the rules; no closure axiom is assumed of an arbitrary larger relation. -/
theorem reduction_eq_infimum :
    reduction = sInf { R : Subfunctor (rootPairsPresheaf sig) |
      RespectsRules R } := by
  apply le_antisymm
  · apply le_sInf
    intro R membership
    exact reduction_le_of_respectsRules R membership
  · exact sInf_le reduction_respectsRules

/-- The same leastness holds against every categorical subobject. Mathlib's
subobject poset is not given a complete-lattice instance here; the actual
universal property is the order comparison, transported across its proved
equivalence with the complete lattice of subfunctors. -/
theorem categoricalSubobject_le_of_respectsRules
    (Q : Subobject (rootPairsPresheaf sig))
    (laws : RespectsRules
      ((Subfunctor.orderIsoSubobject (rootPairsPresheaf sig)).symm Q)) :
    categoricalSubobject ≤ Q := by
  let equivalence := Subfunctor.orderIsoSubobject (rootPairsPresheaf sig)
  have identified : categoricalSubobject = equivalence reduction := rfl
  rw [identified]
  have inclusion := reduction_le_of_respectsRules
    (equivalence.symm Q) laws
  have mapped := equivalence.monotone inclusion
  simpa only [OrderIso.apply_symm_apply] using mapped

/-- The source's open beta premise is an actual point of the reduction
subobject at the binder-extended context. -/
theorem open_beta_member :
    pair
      (appT (lamT (.var .zero)) (.var .zero))
      (.var .zero : Term sig [.term] .term) ∈
      reduction.obj (ctx [.term]) :=
  open_beta_uses_bound_variable

/-- A bare variable has no outgoing edge, even in a nonempty context. -/
theorem variable_not_member {Γ : Ctx sig} (v : Var Γ .term)
    (target : Term sig Γ .term) :
    pair (.var v) target ∉ reduction.obj (ctx Γ) :=
  variable_has_no_step v

end Mettapedia.OSLF.Binding.LambdaReductionSubobject
