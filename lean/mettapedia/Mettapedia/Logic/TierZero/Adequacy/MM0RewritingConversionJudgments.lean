import Mettapedia.Logic.TierZero.Adequacy.MM0RewritingArgumentRules

/-!
# Independent MM0 meanings for stored proof and conversion judgments

The invariant distinguishes proved statements from typed conversion facts.
All other data may coexist in the store. Conversion tags and endpoints are
ordinary contextual patterns over the same object encoding.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.TierZero.Adequacy.MM0Rewriting

open Mettapedia.Languages.MM0.Kernel
open Mettapedia.GSLT.LanguageDef.SignatureIndexedABT
open Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting
open Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting.Thinnings
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Sources
open MM0ContextualSupport

def conversionValue (target : Context) (sort : Nat) (left right : Preterm) : Tm :=
  judgment "cv" [encode target (.term sort), encode target left, encode target right]

def conversionPattern (width sort : Nat) (left right : Preterm) : Pat :=
  judgmentPattern width "cv" [.term sort, left, right]

theorem conversionValue_injective {target : Context} {sort otherSort : Nat}
    {left right otherLeft otherRight : Preterm}
    (same : conversionValue target sort left right = conversionValue target otherSort otherLeft otherRight) :
    sort = otherSort ∧ left = otherLeft ∧ right = otherRight := by
  have parts := judgment_injective "cv" same
  have first := List.cons.inj parts
  have rest := List.cons.inj first.2
  have last := List.cons.inj rest.2
  have sortsSame : sort = otherSort := by
    simpa [MM0ContextualSupport.encode] using first.1
  exact ⟨sortsSame, encode_injective target rest.1, encode_injective target last.1⟩

def ValidValue (signature : TermSignature) (definitions : Definition.Signature) (theorems : TheoremSignature)
    (target : Context) (hypotheses : List Preterm) (value : Tm) : Prop :=
  (∀ expression, value = proofValue target expression →
    Derives signature definitions theorems target hypotheses expression) ∧
  (∀ sort left right, value = conversionValue target sort left right →
    Converts signature definitions target left right sort)

/-- An untrusted request name cannot turn request data into a proof or a
conversion judgment. Logical publication uses a separate reserved tag. -/
theorem valid_request (signature : TermSignature) (definitions : Definition.Signature) (theorems : TheoremSignature)
    (target : Context) (hypotheses : List Preterm) (name : String) (arguments : List Tm) :
    ValidValue signature definitions theorems target hypotheses (requestValue name arguments) := by
  constructor
  · intro expression equal
    exact False.elim (requestValue_ne_proof name arguments target expression equal)
  · intro sort left right equal
    have tags : requestTag name = "cv" := Head.judgment.inj (Term.node.inj equal).1
    exact False.elim (requestTag_ne_conversion name tags)

theorem valid_proof {signature : TermSignature} {definitions : Definition.Signature} {theorems : TheoremSignature}
    {target : Context} {hypotheses : List Preterm} {expression : Preterm}
    (derived : Derives signature definitions theorems target hypotheses expression) :
    ValidValue signature definitions theorems target hypotheses (proofValue target expression) := by
  constructor
  · intro other same
    exact proofValue_injective target same ▸ derived
  · intro sort left right same
    simp [proofValue, conversionValue, judgment] at same

theorem valid_conversion {signature : TermSignature} {definitions : Definition.Signature} {theorems : TheoremSignature}
    {target : Context} {hypotheses : List Preterm} {sort : Nat} {left right : Preterm}
    (converted : Converts signature definitions target left right sort) :
    ValidValue signature definitions theorems target hypotheses (conversionValue target sort left right) := by
  constructor
  · intro expression same
    simp [proofValue, conversionValue, judgment] at same
  · intro otherSort otherLeft otherRight same
    obtain ⟨rfl, rfl, rfl⟩ := conversionValue_injective same
    exact converted

theorem conversionPattern_instantiated (target : Context) (arguments : List Preterm)
    (scopedArguments : ∀ argument ∈ arguments, Term.supportedAt target.length (encode target argument) = true)
    (sort : Nat) {left right leftResult rightResult : Preterm}
    (first : Preterm.Substitutes (Substitution.ofList arguments) left leftResult)
    (second : Preterm.Substitutes (Substitution.ofList arguments) right rightResult) :
    (conversionPattern target.length sort left right).inst (expressionAssignment target arguments) =
      some (conversionValue target sort leftResult rightResult) := by
  rw [conversionPattern, judgmentPattern_instantiation target arguments target.length scopedArguments]
  simp [Substitution.substituteList, Preterm.substitute, first.eval, second.eval, conversionValue]

theorem matches_conversionPattern_iff (target : Context) (arguments : List Preterm)
    (scopedArguments : ∀ argument ∈ arguments, Term.supportedAt target.length (encode target argument) = true)
    (sort : Nat) {left right leftResult rightResult : Preterm}
    (first : Preterm.Substitutes (Substitution.ofList arguments) left leftResult)
    (second : Preterm.Substitutes (Substitution.ofList arguments) right rightResult) (value : Tm) :
    ContextualPatterns.layer.Solves (expressionAssignment target arguments)
      (conversionPattern target.length sort left right) value ↔
      value = conversionValue target sort leftResult rightResult := by
  rw [ContextualPatterns.solves_iff,
    conversionPattern_instantiated target arguments scopedArguments sort first second]
  simp only [Option.some.injEq, eq_comm]

def regularFormals (arity sort : Nat) : Context := List.replicate arity (.regular sort ∅)

theorem regular_admissible_iff (signature : TermSignature) (target : Context) (arity sort : Nat)
    (arguments : List Preterm) :
    Substitution.Admissible signature (regularFormals arity sort) target arguments ↔
      arguments.length = arity ∧ ∀ argument ∈ arguments, Preterm.HasType signature target argument [] sort := by
  rw [Substitution.admissible_iff_typed_of_regular_formals signature (regularFormals arity sort) target arguments
    (by intro binder member; obtain rfl := (List.mem_replicate.mp member).2; exact ⟨sort, ∅, rfl⟩)]
  have fits (expression : Preterm) : Preterm.FitsBinder signature target expression (.regular sort ∅) ↔
      Preterm.HasType signature target expression [] sort := by
    constructor
    · intro fitted; cases fitted with | regular typed => exact typed
    · exact Preterm.FitsBinder.regular
  induction arguments generalizing arity with
  | nil => cases arity <;> simp [regularFormals]
  | cons argument arguments ih =>
      cases arity with
      | zero => simp [regularFormals]
      | succ arity =>
          change List.Forall₂ _ (argument :: arguments) (.regular sort ∅ :: regularFormals arity sort) ↔ _
          simp only [List.forall₂_cons, fits,
            ih, List.length_cons, Nat.succ.injEq, List.mem_cons, forall_eq_or_imp]
          tauto

theorem conversionPattern_bounded (width arity sort : Nat) (left right : Preterm)
    (leftBounded : left.VarsBelow arity) (rightBounded : right.VarsBelow arity) :
    ∀ index ∈ (conversionPattern width sort left right).vars, index < arity := by
  apply judgmentPattern_vars_below
  simpa [Preterm.VarsBelow] using And.intro leftBounded rightBounded

end Mettapedia.Logic.TierZero.Adequacy.MM0Rewriting
