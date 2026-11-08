import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentWeightPruneSite

/-!
# The η-long weight does not grow under pruning

R76's pruning answer `G := λ z̄. H (z̄ restricted)` (`ContextualDependentPrune.Restriction.answer`) instantiates every
store over `Γ, G` to a store over `Γ, H`. **Its normal weight does not grow** (`storeWeight_prune`): the η-long β-normal
form of each instantiated side weighs at most the η-long form of the side (`sideWeight_prune`).

The proof is hereditary substitution of the answer on η-long forms (`Long.prunes`), by induction on the η-long
derivation, under any number of local binders (`Site`):

* a type, a term or a spine not headed by `G` is instantiated part by part, each part replaced by its η-long image
  (abstractions, pairs, reflexivity and formers through their congruences; the `Base` condition of a neutral term by
  `Site.base_subst`);
* a spine of `G` shorter than `G`'s binders keeps the η-long images of its arguments; once it has all of them it becomes
  the η-long spine of `H` at the kept arguments (`Site.complete`). Its arguments are those of the spine, at the kept
  positions only, so it is no heavier.

The η-long image is a normal form of the instance (it is typed-equal to it), so by uniqueness of normal forms
(`sideWeight_eq`) the instance weighs what the image weighs.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentWeightPrune

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentPiSpine ContextualDependentGeneralPattern ContextualDependentHereditary
open ContextualDependentDynamicFragment ContextualDependentRank ContextualDependentPrune ContextualDependentEtaLong
open ContextualDependentEta

section Helpers

variable {Head : Type} {R : Rules Head}

theorem ArgsAt2.mono {n : Nat} {Q Q' : Tm Head n → Tm Head n → Tm Head n → Prop} (weaker : ∀ a b T, Q a b T → Q' a b T)
    {type : Tm Head n} : ∀ {first second : List (Tm Head n)}, ArgsAt2 Q type first second → ArgsAt2 Q' type first second
  | [], [], _ => trivial
  | _ :: _, _ :: _, ⟨rest, now⟩ => ⟨ArgsAt2.mono weaker rest, weaker _ _ _ now⟩
  | [], _ :: _, impossible | _ :: _, [], impossible => impossible.elim

theorem typeEq_subst {n m : Nat} {Δ : Ctx Head n} {Δ' : Ctx Head m} {ς : Sub Head n m} {A B : Tm Head n}
    (equal : TypeEq R Δ A B) (typed : SubstMor R Δ Δ' ς) : TypeEq R Δ' (subst ς A) (subst ς B) := by
  obtain ⟨u, hu, e⟩ := equal
  exact ⟨u, hu, e.substitute typed⟩

theorem isType_subst {n m : Nat} {Δ : Ctx Head n} {Δ' : Ctx Head m} {ς : Sub Head n m} {A : Tm Head n}
    (isType : IsType R Δ A) (typed : SubstMor R Δ Δ' ς) : IsType R Δ' (subst ς A) := by
  obtain ⟨u, hu, t⟩ := isType
  exact ⟨u, hu, t.substitute typed⟩

theorem typeLe_subst {n m : Nat} {Δ : Ctx Head n} {Δ' : Ctx Head m} {ς : Sub Head n m} {A B : Tm Head n}
    (below : Below R Δ A B) (typed : SubstMor R Δ Δ' ς) : TypeLe R Δ' (subst ς A) (subst ς B) :=
  .sub (Derivable.substitutes below typed) (.refl _)

end Helpers

variable {Head L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L}
variable {Γ : Context S.R} {type keptType : TypeOver Γ} {spine : Spine type} {kept : Spine keptType}

/-- The relation of `G`'s arguments, instantiated, with their η-long images. -/
abbrev ImageRel {N' : Nat} (Δ' : Ctx Head N') : Tm Head N' → Tm Head N' → Tm Head N' → Prop :=
  fun instantiated image domain => Long S.R S.roles (.term Δ' image domain) ∧ Equal S.R Δ' instantiated image domain

/-! ## Full spines of `G` -/

section Complete

variable {restriction : Restriction spine kept}
variable {N N' : Nat} {Δ : Ctx Head N} {Δ' : Ctx Head N'} {ς : Sub Head N N'} {ρ : Ren (Γ.arity + 1) N}
  {ρ' : Ren (Γ.arity + 1) N'}
variable (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R)

include facts roots in
/-- **A full η-long spine of `G` becomes an η-long spine of `H`**: given η-long images of its arguments, `H` applied to
the kept images is η-long at the instantiated type, typed-equal to the instance, and weighs at most the spine. -/
theorem Site.complete (site : Site restriction Δ Δ' ς ρ ρ') {args : List (Tm Head N)} {U : Tm Head N}
    (long : Long S.R S.roles (.spine Δ (appsRev (.var (ρ 0)) args) U)) (count : args.length = spine.length)
    {images : List (Tm Head N')}
    (related : ArgsAt2 (ImageRel (S := S) Δ') (subst (renSub ρ') (type.reindex (projectionHom Γ keptType)).code)
      (args.map (subst ς)) images)
    (lighter : (images.map fun a => weight a + 1).sum ≤ (args.map fun a => weight a + 1).sum) :
    ∃ e', Long S.R S.roles (.spine Δ' e' (subst ς U)) ∧
      Equal S.R Δ' (subst ς (appsRev (.var (ρ 0)) args)) e' (subst ς U) ∧
      weight e' ≤ weight (appsRev (.var (ρ 0)) args) := by
  obtain ⟨formed, formed', typed⟩ := site.formed
  have short : args.length ≤ piCount (Ctx.lookup Δ (ρ 0)) := count ▸ site.short
  obtain ⟨_, typeU⟩ := spine_args facts formed (ρ 0) args long short
  have isG' : IsType S.R Δ' (subst (renSub ρ') (type.reindex (projectionHom Γ keptType)).code) := by
    rw [← site.subst_g]
    exact isType_subst (formed.lookup (ρ 0)) typed
  have mapped : subst ς (piAfter (Ctx.lookup Δ (ρ 0)) args) =
      piAfter (subst (renSub ρ') (type.reindex (projectionHom Γ keptType)).code) (args.map (subst ς)) := by
    rw [subst_piAfter _ _ _ short, site.subst_g]
  have typeU' : TypeEq S.R Δ' (subst ς U)
      (piAfter (subst (renSub ρ') (type.reindex (projectionHom Γ keptType)).code) (args.map (subst ς))) := by
    rw [← mapped]
    exact typeEq_subst typeU typed
  have lengthSp : (spine.reindex (projectionHom Γ keptType)).length = spine.length := Spine.length_reindex spine _
  obtain ⟨values, listed⟩ := spineList_surjective (spine.reindex (projectionHom Γ keptType)) (args.map (subst ς)).reverse
    (by simp [count, lengthSp])
  obtain ⟨others, listed'⟩ := spineList_surjective (spine.reindex (projectionHom Γ keptType)) images.reverse
    (by simp [← related.length_eq, count, lengthSp])
  have hv : (spineList (spine.reindex (projectionHom Γ keptType)) values).reverse = args.map (subst ς) := by
    rw [listed, List.reverse_reverse]
  have ho : (spineList (spine.reindex (projectionHom Γ keptType)) others).reverse = images := by
    rw [listed', List.reverse_reverse]
  have piShort : (args.map (subst ς)).length ≤ piCount (subst (renSub ρ') (type.reindex (projectionHom Γ keptType)).code) := by
    rw [List.length_map, count, ← lengthSp]
    exact length_le_piCount _ _
  obtain ⟨types, ownLong⟩ := args_cong facts formed' (fun a T => Long S.R S.roles (.term Δ' a T))
    (fun _ _ _ l e => l.convType S.levels e) _ isG' (args.map (subst ς)) images piShort related
  -- The telescopes of `G` and `H` through the restriction's binder map.
  have compatible := restriction.ren_compatible (projectionHom Γ keptType)
  have resultCode : (spine.reindex (projectionHom Γ keptType)).result.code =
      Presentation.rename (restriction.ren (projectionHom Γ keptType)) (kept.reindex (projectionHom Γ keptType)).result.code := by
    have same := congrArg TypeOver.code (restriction.resultAt (projectionHom Γ keptType))
    change subst (renSub (restriction.ren (projectionHom Γ keptType))) (kept.reindex (projectionHom Γ keptType)).result.code =
      (spine.reindex (projectionHom Γ keptType)).result.code at same
    rw [subst_renSub] at same
    exact same.symm
  have equalArgs := argsAt_kept _ _ _ compatible _ (renSub ρ') values others (by
    rw [hv, ho]
    exact ArgsAt2.mono (fun _ _ _ both => both.2) related)
  have longArgs := argsAt_kept _ _ _ compatible _ (renSub ρ') others others (by
    rw [ho]
    exact ownLong)
  have alignValues := piAfter_kept _ _ _ resultCode (renSub ρ') values
  have alignOthers := piAfter_kept _ _ _ resultCode (renSub ρ') others
  have shortH : ∀ (some : (spine.reindex (projectionHom Γ keptType)).Local → Tm Head N'),
      (spineList (kept.reindex (projectionHom Γ keptType))
        fun p => some (reindexArgs kept spine restriction.keep (projectionHom Γ keptType) p)).reverse.length ≤
        piCount (Ctx.lookup Δ' (ρ' 0)) := by
    intro some
    rw [List.length_reverse, length_spineList, Spine.length_reindex]
    exact site.short'
  have argsLongH : ArgsLong S.R S.roles Δ' (Ctx.lookup Δ' (ρ' 0)) (spineList (kept.reindex (projectionHom Γ keptType))
      fun p => others (reindexArgs kept spine restriction.keep (projectionHom Γ keptType) p)).reverse := by
    rw [site.lookup_h]
    exact (argsLong_iff _ _ _).mpr longArgs
  obtain ⟨longH, _⟩ := spine_build formed' (ρ' 0) _ argsLongH (shortH others)
  have typeH : TypeEq S.R Δ' (piAfter (Ctx.lookup Δ' (ρ' 0)) (spineList (kept.reindex (projectionHom Γ keptType))
      fun p => others (reindexArgs kept spine restriction.keep (projectionHom Γ keptType) p)).reverse) (subst ς U) := by
    rw [site.lookup_h, alignOthers, ho]
    exact TypeEq.trans S.levels types.symm typeU'.symm
  refine ⟨_, longH.spine_convType S.levels typeH, ?_, ?_⟩
  · have reduced := site.whRed_answer values
    rw [hv] at reduced
    have typing : Typed S.R Δ' (subst ς (appsRev (.var (ρ 0)) args)) (subst ς U) := long.spine_typed.substitute typed
    rw [subst_appsRev] at typing ⊢
    change Typed S.R Δ' (appsRev (ς (ρ 0)) _) _ at typing
    change Equal S.R Δ' (appsRev (ς (ρ 0)) _) _ _
    obtain ⟨_, toH⟩ := WhRed.preserve facts roots formed' reduced typing
    have congruent := varSpine_cong (S := S) (ρ' 0) _ _ (shortH values) (by
      rw [site.lookup_h]
      exact equalArgs)
    have typeV : TypeEq S.R Δ' (piAfter (Ctx.lookup Δ' (ρ' 0)) (spineList (kept.reindex (projectionHom Γ keptType))
        fun p => values (reindexArgs kept spine restriction.keep (projectionHom Γ keptType) p)).reverse) (subst ς U) := by
      rw [site.lookup_h, alignValues, hv]
      exact typeU'.symm
    exact toH.trans (Equal.convType congruent typeV)
  · rw [weight_appsRev, weight_appsRev, List.map_reverse, List.sum_reverse]
    have keptLe := sum_kept_le (spine.reindex (projectionHom Γ keptType)) (kept.reindex (projectionHom Γ keptType))
      (reindexArgs kept spine restriction.keep (projectionHom Γ keptType))
      (reindexArgs_injective kept spine restriction.keep (projectionHom Γ keptType) restriction.injective)
      others fun a => weight a + 1
    have allSum : ((spineList (spine.reindex (projectionHom Γ keptType)) others).map fun a => weight a + 1).sum =
        (images.map fun a => weight a + 1).sum := by
      rw [← ho, List.map_reverse, List.sum_reverse]
    simp only [weight]
    omega

end Complete

/-! ## Hereditary substitution of the pruning answer on η-long forms -/

/-- What an η-long derivation of the source context gives under the answer, at every site: an η-long image of the
same or smaller weight, typed-equal to the instance; for a spine of `G` shorter than its binders, the images of its
arguments instead. -/
def PrunesAt (restriction : Restriction spine kept) : LongStatement Head → Prop
  | .type (n := N) Δ V => ∀ {N' : Nat} {Δ' : Ctx Head N'} {ς : Sub Head N N'} {ρ : Ren (Γ.arity + 1) N}
      {ρ' : Ren (Γ.arity + 1) N'}, Site restriction Δ Δ' ς ρ ρ' →
      ∃ V', Long S.R S.roles (.type Δ' V') ∧
        (∀ u, S.R.isUniverse u → Typed S.R Δ V (.head u) → Equal S.R Δ' (subst ς V) V' (.head u)) ∧
        weight V' ≤ weight V
  | .term (n := N) Δ v T => ∀ {N' : Nat} {Δ' : Ctx Head N'} {ς : Sub Head N N'} {ρ : Ren (Γ.arity + 1) N}
      {ρ' : Ren (Γ.arity + 1) N'}, Site restriction Δ Δ' ς ρ ρ' →
      ∃ v', Long S.R S.roles (.term Δ' v' (subst ς T)) ∧ Equal S.R Δ' (subst ς v) v' (subst ς T) ∧ weight v' ≤ weight v
  | .spine (n := N) Δ e U => ∀ {N' : Nat} {Δ' : Ctx Head N'} {ς : Sub Head N N'} {ρ : Ren (Γ.arity + 1) N}
      {ρ' : Ren (Γ.arity + 1) N'}, Site restriction Δ Δ' ς ρ ρ' →
      (∃ args, e = appsRev (.var (ρ 0)) args ∧ args.length < spine.length ∧ ∃ images,
        ArgsAt2 (ImageRel (S := S) Δ') (subst (renSub ρ') (type.reindex (projectionHom Γ keptType)).code)
          (args.map (subst ς)) images ∧
        (images.map fun a => weight a + 1).sum ≤ (args.map fun a => weight a + 1).sum) ∨
      ∃ e', Long S.R S.roles (.spine Δ' e' (subst ς U)) ∧ Equal S.R Δ' (subst ς e) e' (subst ς U) ∧ weight e' ≤ weight e

variable (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R) (heads : HeadPreserving S.R)
  (algebra : CumulativeAlgebra S.R) (rigid : ∀ name, S.roles name = .rigid)
  (complete : AlgorithmicComplete S.R S.roles)

include facts roots heads algebra rigid complete in
/-- **Hereditary substitution of the pruning answer on η-long forms.** -/
theorem Long.prunes (restriction : Restriction spine kept) {st : LongStatement Head} (long : Long S.R S.roles st) :
    PrunesAt restriction st := by
  induction long with
  | @head n Δ h isType =>
      intro N' Δ' ς ρ ρ' site
      obtain ⟨_, _, typed⟩ := site.formed
      exact ⟨.head h, .head (isType_subst isType typed), fun u _ t => .refl (t.substitute typed), le_refl _⟩
  | @pi n Δ A B lA _ isType ihA ihB =>
      intro N' Δ' ς ρ ρ' site
      obtain ⟨formed, formed', typed⟩ := site.formed
      obtain ⟨A', lA', eqA, wA⟩ := ihA site
      obtain ⟨B', lB', eqB, wB⟩ := ihB (site.lift A lA.isType)
      obtain ⟨uA, huA, tA⟩ := lA.isType
      have AA' : TypeEq S.R Δ' (subst ς A) A' := ⟨uA, huA, eqA uA huA tA⟩
      have lB'' := (lB'.stable S.levels) (.snoc (CtxEq.refl Δ' formed') AA'.symm) (.snoc (CtxEq.refl Δ' formed') AA')
      have eqPi : ∀ u, S.R.isUniverse u → Typed S.R Δ (.pi A B) (.head u) →
          Equal S.R Δ' (subst ς (.pi A B)) (.pi A' B') (.head u) := by
        intro u hu t
        obtain ⟨u₁, v₁, w₁, t₁, hu₁, t₂, hv₁, join, le⟩ := t.generation
        have e := Derivable.piCong (eqA u₁ hu₁ t₁) hu₁ (eqB v₁ hv₁ t₂) hv₁ join
        exact Equal.subsume e (typeLe_subst (TypeLe.toBelow le (IsType.head_of_universe hu)) typed)
      obtain ⟨u, hu, t⟩ := isType
      exact ⟨.pi A' B', .pi lA' lB'' ⟨u, hu, (Equal.typed (eqPi u hu t) formed').2⟩, eqPi,
        by simp only [weight]; omega⟩
  | @sigma n Δ A B lA _ isType ihA ihB =>
      intro N' Δ' ς ρ ρ' site
      obtain ⟨formed, formed', typed⟩ := site.formed
      obtain ⟨A', lA', eqA, wA⟩ := ihA site
      obtain ⟨B', lB', eqB, wB⟩ := ihB (site.lift A lA.isType)
      obtain ⟨uA, huA, tA⟩ := lA.isType
      have AA' : TypeEq S.R Δ' (subst ς A) A' := ⟨uA, huA, eqA uA huA tA⟩
      have lB'' := (lB'.stable S.levels) (.snoc (CtxEq.refl Δ' formed') AA'.symm) (.snoc (CtxEq.refl Δ' formed') AA')
      have eqSigma : ∀ u, S.R.isUniverse u → Typed S.R Δ (.sigma A B) (.head u) →
          Equal S.R Δ' (subst ς (.sigma A B)) (.sigma A' B') (.head u) := by
        intro u hu t
        obtain ⟨u₁, v₁, w₁, t₁, hu₁, t₂, hv₁, join, le⟩ := t.generation
        have e := Derivable.sigmaCong (eqA u₁ hu₁ t₁) hu₁ (eqB v₁ hv₁ t₂) hv₁ join
        exact Equal.subsume e (typeLe_subst (TypeLe.toBelow le (IsType.head_of_universe hu)) typed)
      obtain ⟨u, hu, t⟩ := isType
      exact ⟨.sigma A' B', .sigma lA' lB'' ⟨u, hu, (Equal.typed (eqSigma u hu t) formed').2⟩, eqSigma,
        by simp only [weight]; omega⟩
  | @id n Δ A x y lA _ _ isType ihA ihx ihy =>
      intro N' Δ' ς ρ ρ' site
      obtain ⟨formed, formed', typed⟩ := site.formed
      obtain ⟨A', lA', eqA, wA⟩ := ihA site
      obtain ⟨x', lx', ex, wx⟩ := ihx site
      obtain ⟨y', ly', ey, wy⟩ := ihy site
      obtain ⟨uA, huA, tA⟩ := lA.isType
      have AA' : TypeEq S.R Δ' (subst ς A) A' := ⟨uA, huA, eqA uA huA tA⟩
      have eqId : ∀ u, S.R.isUniverse u → Typed S.R Δ (.id A x y) (.head u) →
          Equal S.R Δ' (subst ς (.id A x y)) (.id A' x' y') (.head u) := by
        intro u hu t
        obtain ⟨u₁, t₁, hu₁, _, _, le⟩ := t.generation
        have e := Derivable.idCong (eqA u₁ hu₁ t₁) hu₁ ex ey
        exact Equal.subsume e (typeLe_subst (TypeLe.toBelow le (IsType.head_of_universe hu)) typed)
      obtain ⟨u, hu, t⟩ := isType
      exact ⟨.id A' x' y', .id lA' (lx'.convType S.levels AA') (ly'.convType S.levels AA')
        ⟨u, hu, (Equal.typed (eqId u hu t) formed').2⟩, eqId, by simp only [weight]; omega⟩
  | @neutralType n Δ V U u lspine hu le ih =>
      intro N' Δ' ς ρ ρ' site
      obtain ⟨formed, formed', typed⟩ := site.formed
      rcases ih site with ⟨args, rfl, short, -⟩ | ⟨V', lV', eV, wV⟩
      · obtain ⟨A, B, isPi⟩ := site.partial_pi facts lspine short
        obtain ⟨w, _, isUniverse, _⟩ := Below.universe_target facts le formed hu (IsType.refl (IsType.head_of_universe hu))
        exact absurd (TypeEq.trans S.levels isPi.symm isUniverse) (TypeEq.pi_ne_head facts formed)
      · refine ⟨V', .neutralType lV' hu (Derivable.substitutes le typed), fun u' _ t => ?_, wV⟩
        exact Equal.subsume eV (typeLe_subst (ContextualDependentCumulative.spine_principal facts V formed lspine t) typed)
  | @univ n Δ v T u hu e typed lv ih =>
      intro N' Δ' ς ρ ρ' site
      obtain ⟨formed, formed', substituted⟩ := site.formed
      obtain ⟨V', lV', eV, wV⟩ := ih site
      have equal := eV u hu (Typed.convType typed e)
      have e' : TypeEq S.R Δ' (subst ς T) (.head u) := typeEq_subst e substituted
      exact ⟨V', .univ hu e' (Typed.convType (Equal.typed equal formed').2 e'.symm) lV', Equal.convType equal e'.symm,
        wV⟩
  | @lam n Δ T A b B e isA _ _ ih =>
      intro N' Δ' ς ρ ρ' site
      obtain ⟨formed, formed', typed⟩ := site.formed
      obtain ⟨b', lb', eb, wb⟩ := ih (site.lift A isA)
      have e' : TypeEq S.R Δ' (subst ς T) (subst ς (.pi A B)) := typeEq_subst e typed
      obtain ⟨u, hu, eT⟩ := e'
      have tPi : Typed S.R Δ' (subst ς (.pi A B)) (.head u) := (Equal.typed eT formed').2
      have equal : Equal S.R Δ' (subst ς (.lam b)) (.lam b') (subst ς T) :=
        Equal.convType (Derivable.lamCong tPi hu eb) ⟨u, hu, eT.symm⟩
      exact ⟨.lam b', .lam ⟨u, hu, eT⟩ (isType_subst isA typed) (Equal.typed equal formed').2 lb', equal, wb⟩
  | @pair n Δ T A a b B e _ _ _ iha ihb =>
      intro N' Δ' ς ρ ρ' site
      obtain ⟨formed, formed', typed⟩ := site.formed
      obtain ⟨a', la', ea, wa⟩ := iha site
      obtain ⟨b', lb', eb, wb⟩ := ihb site
      rw [subst_inst0] at lb' eb
      have e' : TypeEq S.R Δ' (subst ς T) (subst ς (.sigma A B)) := typeEq_subst e typed
      obtain ⟨u, hu, eT⟩ := e'
      have tSigma : Typed S.R Δ' (subst ς (.sigma A B)) (.head u) := (Equal.typed eT formed').2
      obtain ⟨_, v, hv, family⟩ := IsType.sigma_parts ⟨u, hu, tSigma⟩
      have fibres := TypeEq.of_instantiateEq family hv (Equal.typed ea formed').1 ea
      have equal : Equal S.R Δ' (subst ς (.pair a b)) (.pair a' b') (subst ς T) :=
        Equal.convType (Derivable.pairCong tSigma hu ea eb) ⟨u, hu, eT.symm⟩
      exact ⟨.pair a' b', .pair ⟨u, hu, eT⟩ (Equal.typed equal formed').2 la' (lb'.convType S.levels fibres), equal,
        by simp only [weight]; omega⟩
  | @refl n Δ T A x y z e typed _ ih =>
      intro N' Δ' ς ρ ρ' site
      obtain ⟨formed, formed', substituted⟩ := site.formed
      obtain ⟨z', lz', ez, wz⟩ := ih site
      have e' : TypeEq S.R Δ' (subst ς T) (subst ς (.id A x y)) := typeEq_subst e substituted
      have typed' : Typed S.R Δ' (subst ς (.refl z)) (subst ς T) := typed.substitute substituted
      obtain ⟨A₀, _, le⟩ := typed'.generation
      have below := TypeLe.toBelow le (Typed.isType typed' formed')
      have eqT : TypeEq S.R Δ' (.id A₀ (subst ς z) (subst ς z)) (subst ς T) :=
        Below.rigid below formed' (fun _ _ same => TypeEq.id_ne_head facts formed' same)
          (fun _ _ same => TypeEq.pi_ne_id facts formed' same.symm)
          (fun _ _ same => TypeEq.sigma_ne_id facts formed' same.symm)
      obtain ⟨eA, _, _⟩ := TypeEq.id_injective facts (TypeEq.trans S.levels eqT e') formed'
      have equal : Equal S.R Δ' (subst ς (.refl z)) (.refl z') (subst ς T) :=
        Equal.subsume (Derivable.reflCong (Equal.convType ez eA.symm)) le
      exact ⟨.refl z', .refl e' (Equal.typed equal formed').2 lz', equal, by simp only [weight]; omega⟩
  | @neutral n Δ v T U lspine le typed base ih =>
      intro N' Δ' ς ρ ρ' site
      obtain ⟨formed, formed', substituted⟩ := site.formed
      rcases ih site with ⟨args, rfl, short, -⟩ | ⟨e', le', ee, we⟩
      · obtain ⟨A, B, isPi⟩ := site.partial_pi facts lspine short
        obtain ⟨A', B', isPi', _, _⟩ := Below.pi_source facts le formed isPi
        exact absurd isPi' (base.1 A' B')
      · have below : Below S.R Δ' (subst ς U) (subst ς T) := Derivable.substitutes le substituted
        have equal := Equal.subsume ee (.sub below (.refl _))
        exact ⟨e', .neutral le' below (Equal.typed equal formed').2
          (site.base_subst facts roots heads algebra rigid complete base (Typed.isType typed formed)), equal, we⟩
  | @var n Δ U i e =>
      intro N' Δ' ς ρ ρ' site
      obtain ⟨formed, formed', typed⟩ := site.formed
      by_cases isG : i = ρ 0
      · subst isG
        by_cases empty : spine.length = 0
        · exact .inr (site.complete facts roots (args := []) (Long.var _ e) empty.symm (images := []) trivial (le_refl _))
        · exact .inl ⟨[], rfl, by simp only [List.length_nil]; omega, [], trivial, le_refl _⟩
      · obtain ⟨x', image, lookup⟩ := site.others i isG
        have e' : TypeEq S.R Δ' (subst ς U) (Ctx.lookup Δ' x') := by
          rw [lookup]
          exact typeEq_subst e typed
        refine .inr ⟨.var x', .var x' e', ?_, le_refl _⟩
        rw [show subst ς (Tm.var i) = ς i from rfl, image]
        exact .refl (Typed.convType (Derivable.var x') e'.symm)
  | @const n Δ U c declaredType role declared typed e =>
      intro N' Δ' ς ρ ρ' site
      obtain ⟨_, _, substituted⟩ := site.formed
      have typed' := typed.substitute substituted
      have e' := typeEq_subst e substituted
      rw [subst_liftClosed] at typed' e'
      exact .inr ⟨.const c, .const role declared typed' e', .refl (Typed.convType typed' e'.symm), le_refl _⟩
  | @app n Δ f a U F A B lf eF la eU ihf iha =>
      intro N' Δ' ς ρ ρ' site
      obtain ⟨formed, formed', typed⟩ := site.formed
      obtain ⟨a', la', ea, wa⟩ := iha site
      rcases ihf site with ⟨args, rfl, short, images, related, lighter⟩ | ⟨f', lf', ef, wf⟩
      · have below : args.length < piCount (Ctx.lookup Δ (ρ 0)) := lt_of_lt_of_le short site.short
        obtain ⟨_, typeF⟩ := spine_args facts formed (ρ 0) args lf (le_of_lt below)
        obtain ⟨Ad, Bd, isPi⟩ := piAfter_pi (Ctx.lookup Δ (ρ 0)) args below
        rw [isPi] at typeF
        obtain ⟨eA, _⟩ := TypeEq.pi_injective facts (TypeEq.trans S.levels eF.symm typeF) formed
        have domain : piDomain (piAfter (subst (renSub ρ') (type.reindex (projectionHom Γ keptType)).code)
            (args.map (subst ς))) = subst ς Ad := by
          rw [← site.subst_g, ← subst_piDomain_piAfter ς _ args below, isPi]
          rfl
        have eA' : TypeEq S.R Δ' (subst ς A) (subst ς Ad) := typeEq_subst eA typed
        have newRelated : ArgsAt2 (ImageRel (S := S) Δ')
            (subst (renSub ρ') (type.reindex (projectionHom Γ keptType)).code) ((a :: args).map (subst ς)) (a' :: images) :=
          ⟨related, by
            rw [domain]
            exact ⟨la'.convType S.levels eA', Equal.convType ea eA'⟩⟩
        have newLighter : ((a' :: images).map fun a => weight a + 1).sum ≤
            ((a :: args).map fun a => weight a + 1).sum := by
          simp only [List.map_cons, List.sum_cons]
          omega
        by_cases full : args.length + 1 = spine.length
        · exact .inr (site.complete facts roots (args := a :: args) (Long.app lf eF la eU) (by simpa using full)
            newRelated newLighter)
        · exact .inl ⟨a :: args, rfl, by simp only [List.length_cons]; omega, a' :: images, newRelated, newLighter⟩
      · have eF' : TypeEq S.R Δ' (subst ς F) (subst ς (.pi A B)) := typeEq_subst eF typed
        have eU' : TypeEq S.R Δ' (subst ς U) (inst0 (subst ς a) (subst (liftSub ς) B)) := by
          have := typeEq_subst eU typed
          rwa [subst_inst0] at this
        obtain ⟨w, hw, ePi⟩ := eF'
        obtain ⟨_, v, hv, family⟩ := IsType.pi_parts ⟨w, hw, (Equal.typed ePi formed').2⟩
        have fibres := TypeEq.of_instantiateEq family hv (Equal.typed ea formed').1 ea
        have equal : Equal S.R Δ' (subst ς (.app f a)) (.app f' a') (subst ς U) :=
          Equal.convType (Derivable.appCong (Equal.convType ef ⟨w, hw, ePi⟩) ea) eU'.symm
        exact .inr ⟨.app f' a', .app lf' ⟨w, hw, ePi⟩ la' (TypeEq.trans S.levels eU' fibres), equal,
          by simp only [weight]; omega⟩
  | @fst n Δ p U P A B lp eP eU ihp =>
      intro N' Δ' ς ρ ρ' site
      obtain ⟨formed, formed', typed⟩ := site.formed
      rcases ihp site with ⟨args, rfl, short, -⟩ | ⟨p', lp', ep, wp⟩
      · obtain ⟨A', B', isPi⟩ := site.partial_pi facts lp short
        exact absurd (TypeEq.trans S.levels isPi.symm eP) (TypeEq.pi_ne_sigma facts formed)
      · have eP' : TypeEq S.R Δ' (subst ς P) (subst ς (.sigma A B)) := typeEq_subst eP typed
        have eU' : TypeEq S.R Δ' (subst ς U) (subst ς A) := typeEq_subst eU typed
        have equal : Equal S.R Δ' (subst ς (.fst p)) (.fst p') (subst ς U) :=
          Equal.convType (Derivable.fstCong (Equal.convType ep eP')) eU'.symm
        exact .inr ⟨.fst p', .fst lp' eP' eU', equal, by simp only [weight]; omega⟩
  | @snd n Δ p U P A B lp eP eU ihp =>
      intro N' Δ' ς ρ ρ' site
      obtain ⟨formed, formed', typed⟩ := site.formed
      rcases ihp site with ⟨args, rfl, short, -⟩ | ⟨p', lp', ep, wp⟩
      · obtain ⟨A', B', isPi⟩ := site.partial_pi facts lp short
        exact absurd (TypeEq.trans S.levels isPi.symm eP) (TypeEq.pi_ne_sigma facts formed)
      · have eP' : TypeEq S.R Δ' (subst ς P) (subst ς (.sigma A B)) := typeEq_subst eP typed
        have eU' : TypeEq S.R Δ' (subst ς U) (inst0 (.fst (subst ς p)) (subst (liftSub ς) B)) := by
          have := typeEq_subst eU typed
          rwa [subst_inst0] at this
        obtain ⟨w, hw, eSigma⟩ := eP'
        obtain ⟨_, v, hv, family⟩ := IsType.sigma_parts ⟨w, hw, (Equal.typed eSigma formed').2⟩
        have projected := Derivable.fstCong (Equal.convType ep ⟨w, hw, eSigma⟩)
        have fibres := TypeEq.of_instantiateEq family hv (Equal.typed projected formed').1 projected
        have equal : Equal S.R Δ' (subst ς (.snd p)) (.snd p') (subst ς U) :=
          Equal.convType (Derivable.sndCong (Equal.convType ep ⟨w, hw, eSigma⟩)) eU'.symm
        exact .inr ⟨.snd p', .snd lp' ⟨w, hw, eSigma⟩ (TypeEq.trans S.levels eU' fibres), equal,
          by simp only [weight]; omega⟩

/-! ## The weight bound -/

include facts roots heads algebra rigid complete in
/-- **A side weighs no more after the pruning answer.** -/
theorem sideWeight_prune (restriction : Restriction spine kept) (side : TotalTerm (extend Γ type)) :
    sideWeight facts roots heads algebra rigid complete (side.reindex restriction.answer) ≤
      sideWeight facts roots heads algebra rigid complete side := by
  obtain ⟨v, normal⟩ := long_exists facts roots heads algebra rigid complete (extend Γ type).formed side.2.typed
  obtain ⟨v', lv', ev, wv⟩ := (Long.prunes facts roots heads algebra rigid complete restriction normal.1)
    (Site.base (restriction := restriction))
  have normal' : NormalForm S.R S.roles (extend Γ keptType).raw (side.reindex restriction.answer).2.code v'
      (side.reindex restriction.answer).1.code :=
    ⟨lv', (normal.2.substitute restriction.answer.typed).trans ev⟩
  rw [sideWeight_eq facts roots heads algebra rigid complete side normal,
    sideWeight_eq facts roots heads algebra rigid complete _ normal']
  exact wv

include facts roots heads algebra rigid complete in
/-- **The η-long weight bound under pruning**: the normal weight of a store does not grow under the pruning answer,
whatever the store's equations are. -/
theorem storeWeight_prune (restriction : Restriction spine kept) :
    ∀ problem : EquationStore (TotalTerm (extend Γ type)),
      storeWeight facts roots heads algebra rigid complete ((frames S.levels).applyStore restriction.answer problem) ≤
        storeWeight facts roots heads algebra rigid complete problem
  | [] => le_refl _
  | equation :: rest => by
      have ih := storeWeight_prune restriction rest
      have left := sideWeight_prune facts roots heads algebra rigid complete restriction equation.1
      have right := sideWeight_prune facts roots heads algebra rigid complete restriction equation.2
      change equationWeight facts roots heads algebra rigid complete
          (equation.1.reindex restriction.answer, equation.2.reindex restriction.answer) +
          storeWeight facts roots heads algebra rigid complete ((frames S.levels).applyStore restriction.answer rest) ≤
        equationWeight facts roots heads algebra rigid complete equation +
          storeWeight facts roots heads algebra rigid complete rest
      unfold equationWeight
      dsimp only
      omega

include facts roots heads algebra rigid complete in
/-- **Pruning, then dropping the first equation, lowers the normal weight**, whatever the other equations are. -/
theorem storeWeight_prune_drop (restriction : Restriction spine kept) (first : Equation (TotalTerm (extend Γ type)))
    (rest : EquationStore (TotalTerm (extend Γ type))) :
    storeWeight facts roots heads algebra rigid complete ((frames S.levels).applyStore restriction.answer rest) <
      storeWeight facts roots heads algebra rigid complete (first :: rest) := by
  have bound := storeWeight_prune facts roots heads algebra rigid complete restriction rest
  have positive := equationWeight_pos facts roots heads algebra rigid complete first
  change _ < equationWeight facts roots heads algebra rigid complete first +
    storeWeight facts roots heads algebra rigid complete rest
  omega

end ContextualDependentWeightPrune
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
