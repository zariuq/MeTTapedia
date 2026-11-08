import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentGeneralPattern

/-!
# Composition of spine reindexing, up to transport

Reindexing a dependent Pi spine first along `σ` and then along `τ` gives the
spine reindexed along `τ ≫ σ`, up to transport along the propositional
equality of the reindexed annotations. The same holds for every derived
object: the extended context, the final result, the lifted context map, the
binder correspondence, opening and abstraction. In particular a spine read in
the context of a newer metavariable and then reindexed by a solution is the
spine reindexed by the composite directly.

The pattern argument maps of `ContextualDependentGeneralPattern` compose the
same way: the argument map of the twice-reindexed spines is, up to the same
transport, the argument map at the composite. The lifted square of a pattern
therefore composes along successive outer substitutions.

All statements are heterogeneous equalities between objects whose indices are
equal but not definitionally equal; their homogeneous consequences on codes in
a fixed context follow by the congruence lemmas below.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentPiSpine

open CategoryTheory
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open TypedContextual.QuotientComprehensionSyntax
open ContextualDependentPiShape

variable {Head : Type} {rules : Rules Head}

namespace Transport

/-! ## Congruence under transport -/

theorem lift_heq {Θ Γ : Context rules} {first second : TypeOver Θ} (same : first = second)
    (one : extend Θ first ⟶ Γ) (two : extend Θ second ⟶ Γ)
    (sameSubstitution : one.substitution = two.substitution) : HEq one two := by
  subst same
  exact heq_of_eq (Hom.ext sameSubstitution)

/-- Lifting through two successive binders is lifting through the composite. -/
theorem rawLift_comp_heq {Θ Δ Γ : Context rules} (τ : Θ ⟶ Δ) (σ : Δ ⟶ Γ) (type : TypeOver Γ) :
    HEq (rawLift τ (type.reindex σ) ≫ rawLift σ type) (rawLift (τ ≫ σ) type) :=
  lift_heq (type.reindex_comp τ σ).symm _ _ (liftSub_subComp τ.substitution σ.substitution)

theorem extend_congr {Θ : Context rules} {first second : TypeOver Θ} (same : first = second) :
    extend Θ first = extend Θ second := congrArg (extend Θ) same

theorem typeOver_reindex_heq {Γ : Context rules} (type : TypeOver Γ) {first second : Context rules}
    (same : first = second) {one : first ⟶ Γ} {two : second ⟶ Γ} (sameMap : HEq one two) :
    HEq (type.reindex one) (type.reindex two) := by
  subst same
  obtain rfl := eq_of_heq sameMap
  rfl

theorem reindex_heq {Γ : Context rules} {type : TypeOver Γ} (spine : Spine type)
    {first second : Context rules} (same : first = second) {one : first ⟶ Γ} {two : second ⟶ Γ}
    (sameMap : HEq one two) : HEq (spine.reindex one) (spine.reindex two) := by
  subst same
  obtain rfl := eq_of_heq sameMap
  rfl

theorem map_heq {Γ : Context rules} {type : TypeOver Γ} (spine : Spine type)
    {first second : Context rules} (same : first = second) {one : first ⟶ Γ} {two : second ⟶ Γ}
    (sameMap : HEq one two) : HEq (spine.map one) (spine.map two) := by
  subst same
  obtain rfl := eq_of_heq sameMap
  rfl

theorem localReindexEquiv_heq {Γ : Context rules} {type : TypeOver Γ} (spine : Spine type)
    {first second : Context rules} (same : first = second) {one : first ⟶ Γ} {two : second ⟶ Γ}
    (sameMap : HEq one two) : HEq (spine.localReindexEquiv one) (spine.localReindexEquiv two) := by
  subst same
  obtain rfl := eq_of_heq sameMap
  rfl

theorem stop_heq {Θ : Context rules} {first second : TypeOver Θ} (same : first = second) :
    HEq (Spine.stop first) (Spine.stop second) := by
  subst same
  rfl

theorem bind_heq {Θ : Context rules} {first second : Shape Θ} (same : first = second)
    {one : Spine first.codomain} {two : Spine second.codomain} (rest : HEq one two) :
    HEq (Spine.bind first one) (Spine.bind second two) := by
  subst same
  obtain rfl := eq_of_heq rest
  rfl

theorem shape_ext {Θ : Context rules} {first second : Shape Θ} (domain : first.domain = second.domain)
    (codomain : HEq first.codomain second.codomain) (whole : first.whole = second.whole) :
    first = second := by
  rcases first with ⟨firstDomain, firstCodomain, firstWhole, firstCode⟩
  rcases second with ⟨secondDomain, secondCodomain, secondWhole, secondCode⟩
  dsimp only at domain codomain whole
  subst domain
  subst whole
  obtain rfl := eq_of_heq codomain
  rfl

/-- A transported spine has the transported target, result, length and binders. -/
theorem target_congr {Θ : Context rules} {first second : TypeOver Θ} (same : first = second)
    {one : Spine first} {two : Spine second} (sameSpine : HEq one two) : one.target = two.target := by
  subst same
  obtain rfl := eq_of_heq sameSpine
  rfl

theorem result_congr {Θ : Context rules} {first second : TypeOver Θ} (same : first = second)
    {one : Spine first} {two : Spine second} (sameSpine : HEq one two) : HEq one.result two.result := by
  subst same
  obtain rfl := eq_of_heq sameSpine
  rfl

theorem length_congr {Θ : Context rules} {first second : TypeOver Θ} (same : first = second)
    {one : Spine first} {two : Spine second} (sameSpine : HEq one two) : one.length = two.length := by
  subst same
  obtain rfl := eq_of_heq sameSpine
  rfl

theorem local_congr {Θ : Context rules} {first second : TypeOver Θ} (same : first = second)
    {one : Spine first} {two : Spine second} (sameSpine : HEq one two) : one.Local = two.Local := by
  subst same
  obtain rfl := eq_of_heq sameSpine
  rfl

theorem openFunction_congr {Θ : Context rules} {first second : TypeOver Θ} (same : first = second)
    {one : Spine first} {two : Spine second} (sameSpine : HEq one two)
    {left : Term Θ first} {right : Term Θ second} (sameFunction : HEq left right) :
    HEq (one.openFunction left) (two.openFunction right) := by
  subst same
  obtain rfl := eq_of_heq sameSpine
  obtain rfl := eq_of_heq sameFunction
  rfl

theorem abstractBody_congr {Θ : Context rules} {first second : TypeOver Θ} (same : first = second)
    {one : Spine first} {two : Spine second} (sameSpine : HEq one two)
    {left : Term one.target one.result} {right : Term two.target two.result} (sameBody : HEq left right) :
    HEq (one.abstractBody left) (two.abstractBody right) := by
  subst same
  obtain rfl := eq_of_heq sameSpine
  obtain rfl := eq_of_heq sameBody
  rfl

/-- Terms over one context at transported annotations have the same code. -/
theorem code_eq {Θ : Context rules} {first second : TypeOver Θ} (same : first = second)
    {left : Term Θ first} {right : Term Θ second} (sameTerm : HEq left right) : left.code = right.code := by
  subst same
  obtain rfl := eq_of_heq sameTerm
  rfl

theorem code_heq {first second : Context rules} (same : first = second) {one : TypeOver first}
    {two : TypeOver second} (sameType : HEq one two) {left : Term first one} {right : Term second two}
    (sameTerm : HEq left right) : HEq left.code right.code := by
  subst same
  obtain rfl := eq_of_heq sameType
  obtain rfl := eq_of_heq sameTerm
  rfl

/-- Terms in transported contexts are transported when their codes are. -/
theorem term_heq {first second : Context rules} (same : first = second) {one : TypeOver first}
    {two : TypeOver second} (sameType : HEq one two) {left : Term first one} {right : Term second two}
    (sameCode : HEq left.code right.code) : HEq left right := by
  subst same
  obtain rfl := eq_of_heq sameType
  exact heq_of_eq (Term.ext (eq_of_heq sameCode))

theorem cast_heq {Θ : Context rules} {first second : TypeOver Θ} (same : first = second)
    (term : Term Θ first) : HEq (term.cast same) term := by
  subst same
  rfl

theorem term_reindex_comp_heq {first middle last : Context rules} {type : TypeOver last}
    (term : Term last type) (earlier : first ⟶ middle) (later : middle ⟶ last) :
    HEq ((term.reindex later).reindex earlier) (term.reindex (earlier ≫ later)) :=
  (heq_of_eq (Term.reindex_comp term earlier later)).symm.trans (cast_heq _ _)

theorem term_reindex_heq {Γ : Context rules} {type : TypeOver Γ} (term : Term Γ type)
    {first second : Context rules} (same : first = second) {one : first ⟶ Γ} {two : second ⟶ Γ}
    (sameMap : HEq one two) : HEq (term.reindex one) (term.reindex two) := by
  subst same
  obtain rfl := eq_of_heq sameMap
  rfl

theorem rename_heq {source source' target target' : Nat} (sameSource : source = source')
    (sameTarget : target = target') {one : Ren source target} {two : Ren source' target'}
    (sameMap : HEq one two) {left : Tm Head source} {right : Tm Head source'} (sameTerm : HEq left right) :
    HEq (Presentation.rename one left) (Presentation.rename two right) := by
  subst sameSource
  subst sameTarget
  obtain rfl := eq_of_heq sameMap
  obtain rfl := eq_of_heq sameTerm
  rfl

theorem eq_eqToHom_comp_of_heq {X Y Z : Context rules} (same : X = Y) (one : X ⟶ Z) (two : Y ⟶ Z)
    (sameMap : HEq one two) : one = eqToHom same ≫ two := by
  subst same
  rw [eqToHom_refl, Category.id_comp]
  exact eq_of_heq sameMap

end Transport

open Transport

namespace Spine

/-! ## Shapes and spines -/

theorem shape_reindex_comp {Γ Δ Θ : Context rules} (shape : Shape Γ) (σ : Δ ⟶ Γ) (τ : Θ ⟶ Δ) :
    (shape.reindex σ).reindex τ = shape.reindex (τ ≫ σ) := by
  apply shape_ext (shape.domain.reindex_comp τ σ).symm
  · change HEq ((shape.codomain.reindex (rawLift σ shape.domain)).reindex (rawLift τ (shape.domain.reindex σ)))
      (shape.codomain.reindex (rawLift (τ ≫ σ) shape.domain))
    exact (heq_of_eq (shape.codomain.reindex_comp (rawLift τ (shape.domain.reindex σ))
      (rawLift σ shape.domain)).symm).trans <| typeOver_reindex_heq shape.codomain (extend_congr (shape.domain.reindex_comp τ σ).symm)
      (rawLift_comp_heq τ σ shape.domain)
  · exact (shape.whole.reindex_comp τ σ).symm

/-- **Composition of reindexing**: reindexing along `σ` then `τ` is reindexing along `τ ≫ σ`,
up to transport of the annotation. -/
theorem reindex_comp_heq {Γ : Context rules} {type : TypeOver Γ} (spine : Spine type) :
    ∀ {Δ Θ : Context rules} (σ : Δ ⟶ Γ) (τ : Θ ⟶ Δ),
      HEq ((spine.reindex σ).reindex τ) (spine.reindex (τ ≫ σ)) := by
  induction spine with
  | stop type => intro Δ Θ σ τ; exact stop_heq (type.reindex_comp τ σ).symm
  | bind shape rest ih =>
      intro Δ Θ σ τ
      exact bind_heq (shape_reindex_comp shape σ τ)
        ((ih (rawLift σ shape.domain) (rawLift τ (shape.domain.reindex σ))).trans
          (reindex_heq rest (extend_congr (shape.domain.reindex_comp τ σ).symm)
            (rawLift_comp_heq τ σ shape.domain)))

theorem target_comp {Γ Δ Θ : Context rules} {type : TypeOver Γ} (spine : Spine type)
    (σ : Δ ⟶ Γ) (τ : Θ ⟶ Δ) :
    ((spine.reindex σ).reindex τ).target = (spine.reindex (τ ≫ σ)).target :=
  target_congr (type.reindex_comp τ σ).symm (spine.reindex_comp_heq σ τ)

theorem result_comp_heq {Γ Δ Θ : Context rules} {type : TypeOver Γ} (spine : Spine type)
    (σ : Δ ⟶ Γ) (τ : Θ ⟶ Δ) :
    HEq ((spine.reindex σ).reindex τ).result (spine.reindex (τ ≫ σ)).result :=
  result_congr (type.reindex_comp τ σ).symm (spine.reindex_comp_heq σ τ)

theorem local_comp {Γ Δ Θ : Context rules} {type : TypeOver Γ} (spine : Spine type)
    (σ : Δ ⟶ Γ) (τ : Θ ⟶ Δ) :
    ((spine.reindex σ).reindex τ).Local = (spine.reindex (τ ≫ σ)).Local :=
  local_congr (type.reindex_comp τ σ).symm (spine.reindex_comp_heq σ τ)

/-- **The lifted maps compose**: lifting along `τ` through the reindexed spine, then along `σ`,
is lifting along `τ ≫ σ`. -/
theorem map_comp_heq {Γ : Context rules} {type : TypeOver Γ} (spine : Spine type) :
    ∀ {Δ Θ : Context rules} (σ : Δ ⟶ Γ) (τ : Θ ⟶ Δ),
      HEq ((spine.reindex σ).map τ ≫ spine.map σ) (spine.map (τ ≫ σ)) := by
  induction spine with
  | stop type => intros; rfl
  | bind shape rest ih =>
      intro Δ Θ σ τ
      exact (ih (rawLift σ shape.domain) (rawLift τ (shape.domain.reindex σ))).trans
        (map_heq rest (extend_congr (shape.domain.reindex_comp τ σ).symm) (rawLift_comp_heq τ σ shape.domain))

/-- The composition law of lifted maps in the category, with the transport as `eqToHom`. -/
theorem map_comp {Γ Δ Θ : Context rules} {type : TypeOver Γ} (spine : Spine type)
    (σ : Δ ⟶ Γ) (τ : Θ ⟶ Δ) :
    (spine.reindex σ).map τ ≫ spine.map σ = eqToHom (spine.target_comp σ τ) ≫ spine.map (τ ≫ σ) :=
  eq_eqToHom_comp_of_heq _ _ _ (spine.map_comp_heq σ τ)


theorem local_reindex_eq {Γ : Context rules} {type : TypeOver Γ} (spine : Spine type)
    {first second : Context rules} (same : first = second) {one : first ⟶ Γ} {two : second ⟶ Γ}
    (sameMap : HEq one two) : (spine.reindex one).Local = (spine.reindex two).Local := by
  subst same
  obtain rfl := eq_of_heq sameMap
  rfl

theorem sumCongr_heq {first second target : Type} (same : first = second)
    {one : first ≃ target} {two : second ≃ target} (sameEquiv : HEq one two) :
    HEq (Equiv.sumCongr (Equiv.refl Unit) one) (Equiv.sumCongr (Equiv.refl Unit) two) := by
  subst same
  obtain rfl := eq_of_heq sameEquiv
  rfl

/-- The binder correspondences compose. -/
theorem localReindexEquiv_comp_heq {Γ : Context rules} {type : TypeOver Γ} (spine : Spine type) :
    ∀ {Δ Θ : Context rules} (σ : Δ ⟶ Γ) (τ : Θ ⟶ Δ),
      HEq (((spine.reindex σ).localReindexEquiv τ).trans (spine.localReindexEquiv σ))
        (spine.localReindexEquiv (τ ≫ σ)) := by
  induction spine with
  | stop type =>
      intro Δ Θ σ τ
      exact heq_of_eq (Equiv.ext fun impossible => impossible.elim)
  | bind shape rest ih =>
      intro Δ Θ σ τ
      change HEq ((Equiv.sumCongr (Equiv.refl Unit)
            ((rest.reindex (rawLift σ shape.domain)).localReindexEquiv (rawLift τ (shape.domain.reindex σ)))).trans
          (Equiv.sumCongr (Equiv.refl Unit) (rest.localReindexEquiv (rawLift σ shape.domain))))
        (Equiv.sumCongr (Equiv.refl Unit) (rest.localReindexEquiv (rawLift (τ ≫ σ) shape.domain)))
      rw [Equiv.sumCongr_trans, Equiv.refl_trans]
      exact sumCongr_heq
        ((rest.local_comp (rawLift σ shape.domain) (rawLift τ (shape.domain.reindex σ))).trans
          (rest.local_reindex_eq (extend_congr (shape.domain.reindex_comp τ σ).symm)
            (rawLift_comp_heq τ σ shape.domain)))
        ((ih (rawLift σ shape.domain) (rawLift τ (shape.domain.reindex σ))).trans
          (localReindexEquiv_heq rest (extend_congr (shape.domain.reindex_comp τ σ).symm)
            (rawLift_comp_heq τ σ shape.domain)))

/-- Opening commutes with composite reindexing, up to transport. -/
theorem openFunction_comp_heq {Γ Δ Θ : Context rules} {type : TypeOver Γ} (spine : Spine type)
    (σ : Δ ⟶ Γ) (τ : Θ ⟶ Δ) (function : Term Γ type) :
    HEq (((spine.reindex σ).reindex τ).openFunction ((function.reindex σ).reindex τ))
      ((spine.reindex (τ ≫ σ)).openFunction (function.reindex (τ ≫ σ))) :=
  openFunction_congr (type.reindex_comp τ σ).symm (spine.reindex_comp_heq σ τ)
    (term_reindex_comp_heq function τ σ)

/-- Abstraction commutes with composite reindexing, up to transport. -/
theorem abstractBody_comp_code {Γ Δ Θ : Context rules} {type : TypeOver Γ} (spine : Spine type)
    (σ : Δ ⟶ Γ) (τ : Θ ⟶ Δ) (left : Term ((spine.reindex σ).reindex τ).target ((spine.reindex σ).reindex τ).result)
    (right : Term (spine.reindex (τ ≫ σ)).target (spine.reindex (τ ≫ σ)).result) (same : HEq left right) :
    (((spine.reindex σ).reindex τ).abstractBody left).code = ((spine.reindex (τ ≫ σ)).abstractBody right).code :=
  code_eq (type.reindex_comp τ σ).symm
    (abstractBody_congr (type.reindex_comp τ σ).symm (spine.reindex_comp_heq σ τ) same)

/-- A spine read in the context of a newer metavariable and then reindexed by a solution is
the spine reindexed directly by the composite. -/
theorem lifted_reindex_heq {Γ Δ : Context rules} {type : TypeOver Γ} (spine : Spine type)
    (newer : TypeOver Γ) (solution : Δ ⟶ extend Γ newer) :
    HEq ((spine.reindex (projectionHom Γ newer)).reindex solution)
      (spine.reindex (solution ≫ projectionHom Γ newer)) :=
  spine.reindex_comp_heq (projectionHom Γ newer) solution

end Spine

/-! ## Pattern argument maps -/

namespace Transport

theorem conjugate_heq {first second middle third fourth last : Type} (sameSource : first = second)
    (sameTarget : third = fourth) {one : first ≃ middle} {two : second ≃ middle} (sameOne : HEq one two)
    {left : third ≃ last} {right : fourth ≃ last} (sameLeft : HEq left right) (map : middle → last) :
    HEq (fun position => left.symm (map (one position))) (fun position => right.symm (map (two position))) := by
  subst sameSource
  subst sameTarget
  obtain rfl := eq_of_heq sameOne
  obtain rfl := eq_of_heq sameLeft
  rfl

theorem argRen_congr {Θ : Context rules} {first second other another : TypeOver Θ}
    (sameType : first = second) (sameScope : other = another)
    {one : Spine first} {two : Spine second} (sameSpine : HEq one two)
    {left : Spine other} {right : Spine another} (sameLeft : HEq left right)
    {args : one.Local → left.Local} {args' : two.Local → right.Local} (sameArgs : HEq args args') :
    HEq (ContextualDependentGeneralPattern.argRen one left idRen args)
      (ContextualDependentGeneralPattern.argRen two right idRen args') := by
  subst sameType
  subst sameScope
  obtain rfl := eq_of_heq sameSpine
  obtain rfl := eq_of_heq sameLeft
  obtain rfl := eq_of_heq sameArgs
  rfl

end Transport

namespace Spine

open ContextualDependentGeneralPattern

/-- Reading pattern arguments after two outer substitutions is reading them at the composite. -/
theorem reindexArgs_comp_heq {Γ Δ Θ : Context rules} {type scopeType : TypeOver Γ} (spine : Spine type)
    (scope : Spine scopeType) (args : spine.Local → scope.Local) (σ : Δ ⟶ Γ) (τ : Θ ⟶ Δ) :
    HEq (reindexArgs (spine.reindex σ) (scope.reindex σ) (reindexArgs spine scope args σ) τ)
      (reindexArgs spine scope args (τ ≫ σ)) := by
  have composed := conjugate_heq (spine.local_comp σ τ) (scope.local_comp σ τ)
    (spine.localReindexEquiv_comp_heq σ τ) (scope.localReindexEquiv_comp_heq σ τ) args
  exact composed

/-- **The pattern argument map composes**: the argument map of the twice-reindexed spines is the
argument map at the composite, up to transport. -/
theorem argRen_comp_heq {Γ Δ Θ : Context rules} {type scopeType : TypeOver Γ} (spine : Spine type)
    (scope : Spine scopeType) (args : spine.Local → scope.Local) (σ : Δ ⟶ Γ) (τ : Θ ⟶ Δ) :
    HEq (argRen ((spine.reindex σ).reindex τ) ((scope.reindex σ).reindex τ) idRen
        (reindexArgs (spine.reindex σ) (scope.reindex σ) (reindexArgs spine scope args σ) τ))
      (argRen (spine.reindex (τ ≫ σ)) (scope.reindex (τ ≫ σ)) idRen (reindexArgs spine scope args (τ ≫ σ))) :=
  argRen_congr (type.reindex_comp τ σ).symm (scopeType.reindex_comp τ σ).symm
    (spine.reindex_comp_heq σ τ) (scope.reindex_comp_heq σ τ) (spine.reindexArgs_comp_heq scope args σ τ)

end Spine

end ContextualDependentPiSpine
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
