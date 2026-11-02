import Mettapedia.Languages.Metamath.MM0Transfer.SourceSupport

/-!
# Removing derived regular/regular distinctness from source proofs

The source judgments are the original mm-lean4 declarative judgments. A base
axiom profile is a syntactic property: bound-sort formulas are not axioms,
every base distinctness pair has a bound-sort endpoint, and those endpoints
are mandatory variables of the axiom. It does not assert target derivability.

Under this profile and with only variable-shaped bound-sort hypotheses, a derivation
uses no regular/regular distinctness assumption. This is a proof induction,
not a claim that deleting an arbitrary source axiom restriction is sound.
Certification of the profile for a parsed concrete database, normalization
to structured expressions, and refinement of the Haskell converter are
separate obligations.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Metamath.MM0Transfer.DistinctnessProjection

open _root_.Metamath

/-- Keep exactly the distinctness pairs with a bound-sort endpoint. -/
def projectDJ (boundSort : CN → Prop) (source : DJ) : DJ where
  disj left right := source left right ∧ (boundSort left.type ∨ boundSort right.type)
  irr := fun pair => source.irr pair.1
  symm := fun pair => ⟨source.symm pair.1, pair.2.symm⟩

theorem projectDJ_le (boundSort : CN → Prop) (source : DJ) :
    projectDJ boundSort source ≤ source := fun _ _ pair => pair.1

theorem projectDJ_idempotent (boundSort : CN → Prop) (source : DJ) :
    projectDJ boundSort (projectDJ boundSort source) = projectDJ boundSort source := by
  apply DJ.ext
  intro left right
  exact ⟨fun pair => pair.1, fun pair => ⟨pair, pair.2⟩⟩

theorem projectDJ_retains_bound_pair (boundSort : CN → Prop) (source : DJ)
    {left right : VR} (pair : source left right)
    (bound : boundSort left.type ∨ boundSort right.type) :
    projectDJ boundSort source left right := ⟨pair, bound⟩

theorem projectDJ_removes_regular_pair (boundSort : CN → Prop) (source : DJ)
    {left right : VR} (leftRegular : ¬ boundSort left.type)
    (rightRegular : ¬ boundSort right.type) :
    ¬ projectDJ boundSort source left right :=
  fun pair => pair.2.elim leftRegular rightRegular

/-- Hypotheses and formulas are untouched; only the distinctness relation changes. -/
def projectContext (boundSort : CN → Prop) (source : Context) : Context :=
  ⟨source.hyps, projectDJ boundSort source.dj⟩

/-- These are checkable properties of the admitted source axioms, not an
assumption of a whole translation or an axiom's semantic soundness. -/
structure AxiomProfile (boundSort : CN → Prop) (axioms : Statement → Prop) : Prop where
  noBoundConclusion : ∀ statement, axioms statement → ¬ boundSort statement.fmla.1
  distinctHasBound : ∀ statement, axioms statement →
    ∀ left right, statement.ctx.dj left right →
      boundSort left.type ∨ boundSort right.type
  mandatoryDistinct : ∀ statement, axioms statement →
    ∀ left right, statement.ctx.dj left right →
      left ∈ statement.vars ∧ right ∈ statement.vars

/-- The original floating hypotheses are allowed. A bound-sort essential
hypothesis must also be a variable, rather than arbitrary expression data. -/
def AtomicHypotheses (boundSort : CN → Prop) (context : Context) : Prop :=
  ∀ formula ∈ context.hyps, boundSort formula.1 →
    ∃ reference : VR, formula = reference.vhyp

/-- A bound-sort formula cannot be manufactured by an axiom application. Its
actual hypotheses and floating-variable rule preserve variable shape. -/
theorem bound_sort_proof_is_variable {boundSort : CN → Prop}
    {axioms : Statement → Prop} (profile : AxiomProfile boundSort axioms)
    {context : Context}
    (boundHypotheses : AtomicHypotheses boundSort context)
    {formula : Formula} (derived : Provable axioms context formula)
    (bound : boundSort formula.1) :
    ∃ reference : VR, formula = reference.vhyp := by
  cases derived with
  | hyp formula present => exact boundHypotheses formula present bound
  | var reference => exact ⟨reference, rfl⟩
  | ax substitution accepted _ _ _ =>
      exact False.elim (profile.noBoundConclusion _ accepted bound)

/-- An actual bound-sort substitution image is one variable of the same sort. -/
theorem bound_image_is_variable {boundSort : CN → Prop}
    {axioms : Statement → Prop} (profile : AxiomProfile boundSort axioms)
    {context : Context}
    (boundHypotheses : AtomicHypotheses boundSort context)
    {reference : VR} {image : Expr}
    (derived : Provable axioms context (reference.type, image))
    (bound : boundSort reference.type) :
    ∃ target : VR, image = target.expr ∧ target.type = reference.type := by
  obtain ⟨target, equal⟩ := bound_sort_proof_is_variable profile boundHypotheses derived bound
  exact ⟨target, congrArg Prod.snd equal, (congrArg Prod.fst equal).symm⟩

/-- Every source base-axiom substitution still respects distinctness after
regular/regular caller assumptions are removed. -/
theorem base_substitution_projects {boundSort : CN → Prop}
    {axioms : Statement → Prop} (profile : AxiomProfile boundSort axioms)
    {context : Context}
    (boundHypotheses : AtomicHypotheses boundSort context)
    {statement : Statement} (accepted : axioms statement)
    {substitution : VR → Expr}
    (distinct : statement.ctx.dj.subst substitution context.dj)
    (typed : ∀ reference ∈ statement.vars,
      Provable axioms context (reference.type, substitution reference)) :
    statement.ctx.dj.subst substitution (projectDJ boundSort context.dj) := by
  intro left right pair targetLeft targetRight inLeft inRight
  refine ⟨distinct left right pair targetLeft targetRight inLeft inRight, ?_⟩
  obtain ⟨leftMandatory, rightMandatory⟩ := profile.mandatoryDistinct statement accepted _ _ pair
  rcases profile.distinctHasBound statement accepted left right pair with leftBound | rightBound
  · obtain ⟨target, image, sameType⟩ :=
      bound_image_is_variable profile boundHypotheses (typed left leftMandatory) leftBound
    rw [image] at inLeft
    have equal : targetLeft = target := by simpa [VR.expr, Expr.mem] using inLeft
    exact .inl (by simpa [equal, sameType] using leftBound)
  · obtain ⟨target, image, sameType⟩ :=
      bound_image_is_variable profile boundHypotheses (typed right rightMandatory) rightBound
    rw [image] at inRight
    have equal : targetRight = target := by simpa [VR.expr, Expr.mem] using inRight
    exact .inr (by simpa [equal, sameType] using rightBound)

/-- A real source derivation from the base axioms does not need caller
regular/regular restrictions under the stated syntactic profile. -/
theorem derivation_projects {boundSort : CN → Prop}
    {axioms : Statement → Prop} (profile : AxiomProfile boundSort axioms)
    {context : Context}
    (boundHypotheses : AtomicHypotheses boundSort context)
    {formula : Formula} (derived : Provable axioms context formula) :
    Provable axioms (projectContext boundSort context) formula := by
  induction derived with
  | hyp formula present => exact .hyp formula present
  | var reference => exact .var reference
  | ax substitution accepted distinct hypotheses typed ihHypotheses ihTyped =>
      exact .ax substitution accepted
        (base_substitution_projects profile boundHypotheses accepted distinct typed)
        ihHypotheses ihTyped

/-- Strengthening back to the original context gives equivalence, not merely a
forward encoding. No theorem is added to the source axiom set. -/
theorem derivable_iff_projected {boundSort : CN → Prop}
    {axioms : Statement → Prop} (profile : AxiomProfile boundSort axioms)
    {context : Context}
    (boundHypotheses : AtomicHypotheses boundSort context)
    (formula : Formula) :
    Provable axioms context formula ↔
      Provable axioms (projectContext boundSort context) formula := by
  constructor
  · exact derivation_projects profile boundHypotheses
  · intro derived
    exact Provable.mono (Γ₁ := projectContext boundSort context) (Γ₂ := context)
      (fun _ => id) ⟨fun _ => id, projectDJ_le boundSort context.dj⟩ derived

end Mettapedia.Languages.Metamath.MM0Transfer.DistinctnessProjection
