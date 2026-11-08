import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentWeightPruneSpines

/-!
# The pruning answer under local binders: its spines and its types

R76's pruning answer `G := λ z̄. H (z̄ restricted)` (`ContextualDependentPrune.Restriction.answer`), read under any number
of local binders (`Site`): every variable other than `G` goes to a variable with the substituted declared type, and `G`
goes to the answer's value, renamed.

* **Telescope compatibility** (`lookup_kept`, `piAfter_kept`): the restriction's binder map instantiates `H`'s
  telescope at the kept arguments exactly where `G`'s telescope is instantiated at all of them, binder by binder and at
  the result. This is the restriction's `CtxRen` fact read through `spineInst`, for any arguments.
* **Contraction** (`whRed_answer`): `G`'s value applied to a full list of arguments reduces in weak-head steps to `H`
  applied to the kept arguments.
* **The η-long spine of `G`** (`complete`): a full η-long spine of `G` whose arguments have η-long images becomes an
  η-long spine of `H`, at the substituted type, typed-equal to the instance, and no heavier.
* **`Base` is kept** (`base_subst`): a type that is not a Π or Σ type stays so under the answer. Its η-long normal type is
  a head, an identity type or a neutral type; a neutral type headed by `G` is applied to all of `G`'s binders (a shorter
  spine of `G` has a Π type, which is neither a universe nor a Σ type), so its instance reduces to a neutral type headed
  by `H` (`neutralAt`), and a neutral type is equal to no Π or Σ type (`TypeEq.neutral_form`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentWeightPrune

open CategoryTheory
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentPiSpine ContextualDependentGeneralPattern ContextualDependentHereditary
open ContextualDependentDynamicFragment ContextualDependentRank ContextualDependentPrune ContextualDependentEtaLong

/-! ## Compatible telescopes -/

section Telescopes

variable {Head : Type} {rules : Rules Head}

/-- **Binder by binder**: the restricted telescope's binder types, instantiated at the kept arguments, are the full
telescope's binder types at the kept positions, instantiated at all arguments. -/
theorem lookup_kept {Γ : Context rules} {type keptType : TypeOver Γ} (spine : Spine type) (kept : Spine keptType)
    (keep : kept.Local → spine.Local) (compatible : CtxRen kept.target.raw spine.target.raw (argRen kept spine idRen keep))
    {M : Nat} (θ : Sub Head Γ.arity M) (values : spine.Local → Tm Head M) (position : kept.Local) :
    subst (spineInst kept θ fun p => values (keep p)) (Ctx.lookup kept.target.raw (kept.localIndex position)) =
      subst (spineInst spine θ values) (Ctx.lookup spine.target.raw (spine.localIndex (keep position))) := by
  rw [← argRen_local kept spine idRen keep position, compatible, subst_rename]
  exact subst_ext (fun index => (spineInst_argRen spine kept keep θ values index).symm) _

/-- **At the result**: both telescopes, instantiated, end at the same type. -/
theorem piAfter_kept {Γ : Context rules} {type keptType : TypeOver Γ} (spine : Spine type) (kept : Spine keptType)
    (keep : kept.Local → spine.Local)
    (resultCode : spine.result.code = Presentation.rename (argRen kept spine idRen keep) kept.result.code)
    {M : Nat} (θ : Sub Head Γ.arity M) (values : spine.Local → Tm Head M) :
    piAfter (subst θ keptType.code) (spineList kept fun p => values (keep p)).reverse =
      piAfter (subst θ type.code) (spineList spine values).reverse := by
  rw [piAfter_spineList, piAfter_spineList, resultCode, subst_rename]
  exact (subst_ext (fun index => spineInst_argRen spine kept keep θ values index) _).symm

/-- Pointwise relations of instantiated telescopes transfer along the binder map. -/
theorem argsAt_kept {Γ : Context rules} {type keptType : TypeOver Γ} (spine : Spine type) (kept : Spine keptType)
    (keep : kept.Local → spine.Local) (compatible : CtxRen kept.target.raw spine.target.raw (argRen kept spine idRen keep))
    {M : Nat} (Q : Tm Head M → Tm Head M → Tm Head M → Prop) (θ : Sub Head Γ.arity M)
    (values others : spine.Local → Tm Head M)
    (all : ArgsAt2 Q (subst θ type.code) (spineList spine values).reverse (spineList spine others).reverse) :
    ArgsAt2 Q (subst θ keptType.code) (spineList kept fun p => values (keep p)).reverse
      (spineList kept fun p => others (keep p)).reverse := by
  refine (argsAt_spine Q kept θ _ _).mpr fun position => ?_
  rw [lookup_kept spine kept keep compatible θ values position]
  exact (argsAt_spine Q spine θ values others).mp all (keep position)

end Telescopes

/-! ## Congruence along literal Π binders -/

section Congruence

variable {Head L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L}

/-- **Equal arguments give equal types along literal Π binders**, and move a type-invariant property of the second
list's arguments from the first list's domains to its own. -/
theorem args_cong (facts : FormFacts S.R S.roles) {n : Nat} {Γ : Ctx Head n} (formed : CtxFormed S.R Γ)
    (Q : Tm Head n → Tm Head n → Prop) (invariant : ∀ a T T', Q a T → TypeEq S.R Γ T T' → Q a T')
    (type : Tm Head n) (isType : IsType S.R Γ type) :
    ∀ (first second : List (Tm Head n)), first.length ≤ piCount type →
      ArgsAt2 (fun b a T => Q a T ∧ Equal S.R Γ b a T) type first second →
      TypeEq S.R Γ (piAfter type first) (piAfter type second) ∧ ArgsAt2 (fun a _ T => Q a T) type second second
  | [], [], _, _ => ⟨IsType.refl isType, trivial⟩
  | b :: rest, a :: others, short, ⟨related, now, equal⟩ => by
      have restShort : rest.length < piCount type := by simp at short; omega
      obtain ⟨types, restQ⟩ := args_cong facts formed Q invariant type isType rest others (by omega) related
      obtain ⟨A, B, isPi⟩ := piAfter_pi type rest restShort
      obtain ⟨A', B', isPi'⟩ := piAfter_pi type others (by rw [← related.length_eq]; exact restShort)
      rw [isPi, isPi'] at types
      obtain ⟨eA, eB⟩ := TypeEq.pi_injective facts types formed
      rw [isPi] at now equal
      change Q a A at now
      change Equal S.R Γ b a A at equal
      refine ⟨?_, restQ, ?_⟩
      · simp only [piAfter, isPi, isPi']
        obtain ⟨w, hw, eTypes⟩ := types
        obtain ⟨_, v, hv, family⟩ := IsType.pi_parts ⟨w, hw, (Equal.typed eTypes formed).1⟩
        exact TypeEq.trans S.levels (TypeEq.of_instantiateEq family hv (Equal.typed equal formed).1 equal)
          (TypeEq.instantiate eB (Equal.typed equal formed).2)
      · rw [isPi']
        exact invariant _ _ _ now eA
  | [], _ :: _, _, impossible | _ :: _, [], _, impossible => impossible.elim

/-- **Congruence of a variable spine** along the variable's literal Π binders. -/
theorem varSpine_cong {n : Nat} {Γ : Ctx Head n} (x : Fin n) :
    ∀ (first second : List (Tm Head n)), first.length ≤ piCount (Ctx.lookup Γ x) →
      ArgsAt2 (fun b a T => Equal S.R Γ b a T) (Ctx.lookup Γ x) first second →
      Equal S.R Γ (appsRev (.var x) first) (appsRev (.var x) second) (piAfter (Ctx.lookup Γ x) first)
  | [], [], _, _ => .refl (Derivable.var x)
  | b :: rest, a :: others, short, ⟨related, equal⟩ => by
      have ih := varSpine_cong x rest others (by simp at short; omega) related
      obtain ⟨A, B, isPi⟩ := piAfter_pi (Ctx.lookup Γ x) rest (by simp at short; omega)
      rw [isPi] at ih equal
      simp only [piAfter, isPi]
      exact Derivable.appCong ih equal
  | [], _ :: _, _, impossible | _ :: _, [], _, impossible => impossible.elim

end Congruence

/-! ## The sites of the pruning answer -/

section Site

variable {Head L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L}
variable {Γ : Context S.R} {type keptType : TypeOver Γ} {spine : Spine type} {kept : Spine keptType}
  (restriction : Restriction spine kept)

/-- **The sites of the pruning answer**: the answer itself, and its liftings under local binders. `ρ` and `ρ'` place the
answer's source and target contexts in the two local contexts. -/
inductive Site : {N N' : Nat} → Ctx Head N → Ctx Head N' → Sub Head N N' → Ren (Γ.arity + 1) N →
    Ren (Γ.arity + 1) N' → Prop
  | base : Site (extend Γ type).raw (extend Γ keptType).raw restriction.answer.substitution idRen idRen
  | lift {N N' : Nat} {Δ : Ctx Head N} {Δ' : Ctx Head N'} {ς : Sub Head N N'} {ρ : Ren (Γ.arity + 1) N}
      {ρ' : Ren (Γ.arity + 1) N'} (A : Tm Head N) :
      Site Δ Δ' ς ρ ρ' → IsType S.R Δ A →
      Site (.snoc Δ A) (.snoc Δ' (subst ς A)) (liftSub ς) (fun i => wk (ρ i)) (fun i => wk (ρ' i))

variable {restriction}
variable {N N' : Nat} {Δ : Ctx Head N} {Δ' : Ctx Head N'} {ς : Sub Head N N'} {ρ : Ren (Γ.arity + 1) N}
  {ρ' : Ren (Γ.arity + 1) N'}

theorem Site.formed (site : Site restriction Δ Δ' ς ρ ρ') :
    CtxFormed S.R Δ ∧ CtxFormed S.R Δ' ∧ SubstMor S.R Δ Δ' ς := by
  induction site with
  | base => exact ⟨(extend Γ type).formed, (extend Γ keptType).formed, restriction.answer.typed⟩
  | lift A _ isA ih =>
      obtain ⟨formed, formed', typed⟩ := ih
      obtain ⟨u, hu, tA⟩ := isA
      exact ⟨formed.snoc ⟨u, hu, tA⟩, formed'.snoc ⟨u, hu, tA.substitute typed⟩, typed.lift A⟩

/-- The answer's source variables go to its value, renamed into the target. -/
theorem Site.outer (site : Site restriction Δ Δ' ς ρ ρ') :
    ∀ i, ς (ρ i) = Presentation.rename ρ' (restriction.answer.substitution i) := by
  induction site with
  | base => exact fun i => (rename_id _).symm
  | lift A _ _ ih =>
      intro i
      change Presentation.rename wk (_ : Tm Head _) = _
      rw [ih i, rename_comp]

/-- Local binders go to local binders, at their substituted declared types. -/
theorem Site.locals (site : Site restriction Δ Δ' ς ρ ρ') :
    ∀ j, (∀ i, ρ i ≠ j) → ∃ j', ς j = .var j' ∧ Ctx.lookup Δ' j' = subst ς (Ctx.lookup Δ j) := by
  induction site with
  | base => exact fun j outside => absurd rfl (outside j)
  | @lift N N' Δ Δ' ς ρ ρ' A _ _ ih =>
      intro j outside
      rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨prior, rfl⟩
      · exact ⟨0, rfl, by
          change Presentation.rename wk (subst ς A) = subst (liftSub ς) (Presentation.rename wk A)
          rw [subst_liftSub_wk]⟩
      · have outsidePrior : ∀ i, ρ i ≠ prior := fun i same => outside i (by
          change wk (ρ i) = prior.succ
          rw [same]
          rfl)
        obtain ⟨j', image, typed⟩ := ih prior outsidePrior
        refine ⟨j'.succ, ?_, ?_⟩
        · change Presentation.rename wk (ς prior) = _
          rw [image]
          rfl
        · change Presentation.rename wk (Ctx.lookup Δ' j') = subst (liftSub ς) (Presentation.rename wk (Ctx.lookup Δ prior))
          rw [typed, subst_liftSub_wk]

theorem Site.ren (site : Site restriction Δ Δ' ς ρ ρ') :
    CtxRen (extend Γ type).raw Δ ρ ∧ CtxRen (extend Γ keptType).raw Δ' ρ' := by
  induction site with
  | base => exact ⟨CtxRen.id _, CtxRen.id _⟩
  | @lift N N' Δ Δ' ς ρ ρ' A _ _ ih =>
      exact ⟨CtxRen.comp ih.1 (CtxRen.wk Δ A), CtxRen.comp ih.2 (CtxRen.wk Δ' (subst ς A))⟩

/-- Codes over the answer's source context, renamed, are instantiated as the answer, renamed. -/
theorem Site.subst_rename (site : Site restriction Δ Δ' ς ρ ρ') (code : Tm Head (Γ.arity + 1)) :
    subst ς (Presentation.rename ρ code) = Presentation.rename ρ' (subst restriction.answer.substitution code) := by
  rw [Presentation.subst_rename, rename_subst]
  exact subst_ext (fun i => site.outer i) _

/-- **The variables other than `G`** go to variables at their substituted declared types. -/
theorem Site.others (site : Site restriction Δ Δ' ς ρ ρ') :
    ∀ x, x ≠ ρ 0 → ∃ x', ς x = .var x' ∧ Ctx.lookup Δ' x' = subst ς (Ctx.lookup Δ x) := by
  intro x notG
  by_cases inside : ∃ i, ρ i = x
  · obtain ⟨i, rfl⟩ := inside
    rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨k, rfl⟩
    · exact absurd rfl notG
    · refine ⟨ρ' k.succ, by rw [site.outer]; rfl, ?_⟩
      rw [site.ren.2 k.succ, site.ren.1 k.succ, site.subst_rename]
      change _ = Presentation.rename ρ' (subst restriction.answer.substitution
        (Presentation.rename wk (Ctx.lookup Γ.raw k)))
      rw [ContextualDependentIntersection.subst_weakened restriction.answer restriction.answer_projection]
      rfl
  · exact site.locals x fun i same => inside ⟨i, same⟩

/-- `G`'s type in the source context. -/
theorem Site.lookup_g (site : Site restriction Δ Δ' ς ρ ρ') :
    Ctx.lookup Δ (ρ 0) = subst (renSub ρ) (type.reindex (projectionHom Γ keptType)).code := by
  rw [site.ren.1 0, subst_renSub]
  change _ = Presentation.rename ρ (subst projection type.code)
  rw [subst_projection]
  rfl

/-- `G`'s type, instantiated. -/
theorem Site.subst_g (site : Site restriction Δ Δ' ς ρ ρ') :
    subst ς (Ctx.lookup Δ (ρ 0)) = subst (renSub ρ') (type.reindex (projectionHom Γ keptType)).code := by
  rw [site.ren.1 0, site.subst_rename, subst_renSub]
  change Presentation.rename ρ' (subst restriction.answer.substitution (Presentation.rename wk type.code)) =
    Presentation.rename ρ' (subst projection type.code)
  rw [ContextualDependentIntersection.subst_weakened restriction.answer restriction.answer_projection,
    subst_projection]

/-- `H`'s type in the target context. -/
theorem Site.lookup_h (site : Site restriction Δ Δ' ς ρ ρ') :
    Ctx.lookup Δ' (ρ' 0) = subst (renSub ρ') (keptType.reindex (projectionHom Γ keptType)).code := by
  rw [site.ren.2 0, subst_renSub]
  change _ = Presentation.rename ρ' (subst projection keptType.code)
  rw [subst_projection]
  rfl

/-- `G`'s binders are at least the spine's positions. -/
theorem Site.short (site : Site restriction Δ Δ' ς ρ ρ') :
    spine.length ≤ piCount (Ctx.lookup Δ (ρ 0)) := by
  rw [site.lookup_g, ← Spine.length_reindex spine (projectionHom Γ keptType)]
  exact length_le_piCount _ _

theorem Site.short' (site : Site restriction Δ Δ' ς ρ ρ') :
    kept.length ≤ piCount (Ctx.lookup Δ' (ρ' 0)) := by
  rw [site.lookup_h, ← Spine.length_reindex kept (projectionHom Γ keptType)]
  exact length_le_piCount _ _

/-- **The answer's value applied to a full list of arguments contracts to `H` applied to the kept ones.** -/
theorem Site.whRed_answer (site : Site restriction Δ Δ' ς ρ ρ')
    (values : (spine.reindex (projectionHom Γ keptType)).Local → Tm Head N') :
    WhRed S.R S.roles (appsRev (ς (ρ 0)) (spineList (spine.reindex (projectionHom Γ keptType)) values).reverse)
      (appsRev (.var (ρ' 0)) (spineList (kept.reindex (projectionHom Γ keptType))
        fun p => values (reindexArgs kept spine restriction.keep (projectionHom Γ keptType) p)).reverse) := by
  rw [site.outer 0, ← subst_renSub]
  have reduced := whRed_abstractBody (R := S.R) (roles := S.roles) (spine.reindex (projectionHom Γ keptType))
    (renSub ρ') values (restriction.body (projectionHom Γ keptType) (newest Γ keptType))
  rw [Restriction.body_code, Presentation.subst_rename] at reduced
  have kept' : (fun index => spineInst (spine.reindex (projectionHom Γ keptType)) (renSub ρ') values
      (restriction.ren (projectionHom Γ keptType) index)) =
      spineInst (kept.reindex (projectionHom Γ keptType)) (renSub ρ')
        fun p => values (reindexArgs kept spine restriction.keep (projectionHom Γ keptType) p) :=
    funext fun index => spineInst_argRen _ _ _ _ _ index
  rw [kept', subst_openFunction] at reduced
  exact reduced

end Site

/-! ## Spines of `G` -/

section Spines

variable {Head L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L}
variable {Γ : Context S.R} {type keptType : TypeOver Γ} {spine : Spine type} {kept : Spine keptType}
  {restriction : Restriction spine kept}
variable {N N' : Nat} {Δ : Ctx Head N} {Δ' : Ctx Head N'} {ς : Sub Head N N'} {ρ : Ren (Γ.arity + 1) N}
  {ρ' : Ren (Γ.arity + 1) N'}

/-- An η-long spine of `G` shorter than `G`'s binders has a literal Π type. -/
theorem Site.partial_pi (facts : FormFacts S.R S.roles) (site : Site restriction Δ Δ' ς ρ ρ')
    {args : List (Tm Head N)} {U : Tm Head N} (long : Long S.R S.roles (.spine Δ (appsRev (.var (ρ 0)) args) U))
    (short : args.length < spine.length) :
    ∃ A B, TypeEq S.R Δ U (.pi A B) := by
  obtain ⟨_, typeU⟩ := spine_args facts site.formed.1 (ρ 0) args long (by have := site.short; omega)
  obtain ⟨A, B, isPi⟩ := piAfter_pi (Ctx.lookup Δ (ρ 0)) args (by have := site.short; omega)
  exact ⟨A, B, isPi ▸ typeU⟩

/-- What a neutral spine of the source context gives under the answer: a spine of `G` shorter than its binders, or an
instance that reduces in weak-head steps to a neutral term. -/
def NeutralAt (restriction : Restriction spine kept) : LongStatement Head → Prop
  | .spine (n := N) Δ e _ => ∀ {N' : Nat} {Δ' : Ctx Head N'} {ς : Sub Head N N'} {ρ : Ren (Γ.arity + 1) N}
      {ρ' : Ren (Γ.arity + 1) N'}, Site restriction Δ Δ' ς ρ ρ' →
      (∃ args, e = appsRev (.var (ρ 0)) args ∧ args.length < spine.length) ∨
        ∃ e', WhRed S.R S.roles (subst ς e) e' ∧ Neutral S.roles e'
  | _ => True

/-- A full spine of `G`, instantiated, reduces to a neutral spine of `H`. -/
theorem Site.full_neutral (site : Site restriction Δ Δ' ς ρ ρ') (args : List (Tm Head N))
    (count : args.length = spine.length) :
    ∃ e', WhRed S.R S.roles (subst ς (appsRev (.var (ρ 0)) args)) e' ∧ Neutral S.roles e' := by
  obtain ⟨values, listed⟩ := spineList_surjective (spine.reindex (projectionHom Γ keptType))
    (args.map (subst ς)).reverse (by simp [count, Spine.length_reindex])
  refine ⟨appsRev (.var (ρ' 0)) (spineList (kept.reindex (projectionHom Γ keptType))
    fun p => values (reindexArgs kept spine restriction.keep (projectionHom Γ keptType) p)).reverse, ?_,
    neutral_appsRev (.var _) _⟩
  rw [subst_appsRev]
  have reduced := site.whRed_answer values
  rw [listed, List.reverse_reverse] at reduced
  exact reduced

theorem Long.neutralAt (facts : FormFacts S.R S.roles) (restriction : Restriction spine kept)
    {st : LongStatement Head} (long : Long S.R S.roles st) : NeutralAt restriction st := by
  induction long with
  | head | pi | sigma | id | neutralType | univ | lam | pair | refl | neutral => trivial
  | var i e =>
      intro N' Δ' ς ρ ρ' site
      by_cases isG : i = ρ 0
      · subst isG
        by_cases empty : spine.length = 0
        · exact .inr (site.full_neutral [] empty.symm)
        · exact .inl ⟨[], rfl, by simp; omega⟩
      · obtain ⟨x', image, _⟩ := site.others i isG
        exact .inr ⟨.var x', by rw [show subst ς (Tm.var i) = ς i from rfl, image], .var x'⟩
  | const role _ _ _ =>
      intro N' Δ' ς ρ ρ' _
      exact .inr ⟨_, .refl, Neutral.rigid (c := _) [] role⟩
  | @app n Δ f a U F A B lf _ _ _ ihf _ =>
      intro N' Δ' ς ρ ρ' site
      rcases ihf site with ⟨args, rfl, short⟩ | ⟨f', red, neutral⟩
      · by_cases full : args.length + 1 = spine.length
        · exact .inr (site.full_neutral (a :: args) (by simpa using full))
        · exact .inl ⟨a :: args, rfl, by simp; omega⟩
      · exact .inr ⟨.app f' (subst ς a), whRed_appsRev red [subst ς a], .app neutral⟩
  | @fst n Δ p U P A B lp eP _ ihp =>
      intro N' Δ' ς ρ ρ' site
      rcases ihp site with ⟨args, rfl, short⟩ | ⟨p', red, neutral⟩
      · obtain ⟨A', B', isPi⟩ := site.partial_pi facts lp short
        exact absurd (TypeEq.trans S.levels isPi.symm eP) (TypeEq.pi_ne_sigma facts site.formed.1)
      · exact .inr ⟨.fst p', Relation.ReflTransGen.lift Tm.fst (fun _ _ step => WhStep.fst step) _ _ red, .fst neutral⟩
  | @snd n Δ p U P A B lp eP _ ihp =>
      intro N' Δ' ς ρ ρ' site
      rcases ihp site with ⟨args, rfl, short⟩ | ⟨p', red, neutral⟩
      · obtain ⟨A', B', isPi⟩ := site.partial_pi facts lp short
        exact absurd (TypeEq.trans S.levels isPi.symm eP) (TypeEq.pi_ne_sigma facts site.formed.1)
      · exact .inr ⟨.snd p', Relation.ReflTransGen.lift Tm.snd (fun _ _ step => WhStep.snd step) _ _ red, .snd neutral⟩

variable (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R) (heads : HeadPreserving S.R)
  (algebra : CumulativeAlgebra S.R) (rigid : ∀ name, S.roles name = .rigid)
  (complete : AlgorithmicComplete S.R S.roles)

include facts roots heads algebra rigid complete in
/-- **The `Base` condition is kept by the answer**: a type that is not a Π or Σ type stays so. -/
theorem Site.base_subst (site : Site restriction Δ Δ' ς ρ ρ') {T : Tm Head N} (base : Base S.R Δ T)
    (isT : IsType S.R Δ T) : Base S.R Δ' (subst ς T) := by
  obtain ⟨formed, formed', typed⟩ := site.formed
  obtain ⟨Z, lZ, atZ⟩ := long_type_exists facts roots heads algebra rigid complete formed isT
  obtain ⟨u, hu, tT⟩ := isT
  obtain ⟨tZ, eTZ⟩ := atZ hu tT
  have eSub : TypeEq S.R Δ' (subst ς T) (subst ς Z) := ⟨u, hu, eTZ.substitute typed⟩
  have notPiSigma : (∀ (A : Tm Head N') (B : Tm Head (N' + 1)), ¬ TypeEq S.R Δ' (subst ς Z) (.pi A B)) ∧
      (∀ (A : Tm Head N') (B : Tm Head (N' + 1)), ¬ TypeEq S.R Δ' (subst ς Z) (.sigma A B)) := by
    cases lZ with
    | head _ =>
        exact ⟨fun A B e => TypeEq.pi_ne_head facts formed' e.symm,
          fun A B e => TypeEq.sigma_ne_head facts formed' e.symm⟩
    | pi _ _ _ => exact absurd ⟨u, hu, eTZ⟩ (base.1 _ _)
    | sigma _ _ _ => exact absurd ⟨u, hu, eTZ⟩ (base.2 _ _)
    | id _ _ _ _ =>
        exact ⟨fun A B e => TypeEq.pi_ne_id facts formed' e.symm,
          fun A B e => TypeEq.sigma_ne_id facts formed' e.symm⟩
    | neutralType lspine hv le =>
        rcases (Long.neutralAt facts restriction lspine) site with ⟨args, rfl, short⟩ | ⟨W, red, neutral⟩
        · obtain ⟨A, B, isPi⟩ := site.partial_pi facts lspine short
          obtain ⟨w, _, isUniverse, _⟩ := Below.universe_target facts le formed hv (IsType.refl (IsType.head_of_universe hv))
          exact absurd (TypeEq.trans S.levels isPi.symm isUniverse) (TypeEq.pi_ne_head facts formed)
        · obtain ⟨_, toW⟩ := WhRed.preserve facts roots formed' red (tZ.substitute typed)
          constructor
          · intro A B e
            have back : TypeEq S.R Δ' W (.pi A B) := TypeEq.trans S.levels ⟨u, hu, toW.symm⟩ e
            exact (TypeEq.neutral_form facts back formed' neutral (.inr (.inl ⟨_, _, rfl⟩))).not_former.2.1 A B rfl
          · intro A B e
            have back : TypeEq S.R Δ' W (.sigma A B) := TypeEq.trans S.levels ⟨u, hu, toW.symm⟩ e
            exact (TypeEq.neutral_form facts back formed' neutral (.inr (.inr (.inl ⟨_, _, rfl⟩)))).not_former.2.2.1 A B
              rfl
  exact ⟨fun A B e => notPiSigma.1 A B (TypeEq.trans S.levels eSub.symm e),
    fun A B e => notPiSigma.2 A B (TypeEq.trans S.levels eSub.symm e)⟩

end Spines

end ContextualDependentWeightPrune
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
