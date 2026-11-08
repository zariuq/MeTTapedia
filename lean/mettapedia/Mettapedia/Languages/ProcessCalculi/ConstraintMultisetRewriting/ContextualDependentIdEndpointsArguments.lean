import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentConstantHeadsProjectionsRound

/-!
# The occurs check at spine arguments

A type can occur as an **argument of a neutral type**: `λ g. F g ≐ λ g. g (F g)` at `(U0 → U0) → U0` is in the
dynamic pattern fragment and has no solution, since `g (F g)` would contain `F g` properly. The occurrence
is at an argument of a spine of a bound local `g` whose literal type gives the argument a universe as its
domain.

At such a position the argument is a type, and its η-long normal form as a term at the universe is its
η-long normal form as a type (`Long.type_of_universe`). The normal form of the spine is the head applied to
the normal forms of its arguments along the literal Π types of its prefixes (`argParts_forms`), so it is
strictly larger than the normal form of each argument (`nodes_appSpine_mem`). Together with the
type-former positions and the identity endpoints, an occurrence along these positions makes the normal form
of the whole type strictly larger than that of the occurring type (`normal_occursAt`), so the two are never
equal (`occursAt_not_typeEq`). The relation carries the literal types of the bound locals, as R97's spine
decomposition does.

The **arguments round** is the projections round, and when that round is stuck, this occurs check, read
under the leading abstractions of each equation, on the prepared store with homogeneous twins.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentIdEndpointsArguments

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentUpdate ContextualDependentWorklist
open ContextualDependentPatternSolver ContextualDependentFragment ContextualDependentDecisiveFragment
open ContextualDependentRigidFormers ContextualDependentEtaLong ContextualDependentRank ContextualDependentOccursCheck
open ContextualDependentSpinesMany ContextualDependentConversionBudget ContextualDependentFragmentDecisive
open ContextualDependentTwinsUnder ContextualDependentConstantHeads ContextualDependentEtaExpansion
open ContextualDependentCensusPairEta ContextualDependentIdEndpoints ContextualDependentConstantHeadsProjections

variable {Head L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L}

/-! ## Nodes of spines -/

theorem nodes_le_appSpine {n : Nat} : ∀ (f : Tm Head n) (as : List (Tm Head n)), nodes f ≤ nodes (appSpine f as)
  | _, [] => le_refl _
  | f, a :: as => by
      have inner := nodes_le_appSpine (.app f a) as
      change nodes f ≤ nodes (appSpine (.app f a) as)
      simp only [nodes] at inner
      omega

/-- **An argument of a spine has fewer nodes than the spine.** -/
theorem nodes_appSpine_mem {n : Nat} {a : Tm Head n} : ∀ {f : Tm Head n} {as : List (Tm Head n)}, a ∈ as →
    nodes a < nodes (appSpine f as)
  | _, [], member => absurd member List.not_mem_nil
  | f, b :: as, member => by
      change nodes a < nodes (appSpine (.app f b) as)
      rcases List.mem_cons.mp member with rfl | inside
      · have := nodes_le_appSpine (.app f a) as
        simp only [nodes] at this
        omega
      · exact nodes_appSpine_mem inside

/-! ## Occurrences along positions, endpoints and spine arguments -/

/-- **`V` occurs in `T` along type-former positions, identity endpoints at a universe, and spine arguments at a
universe domain**, with the literal types of the bound locals. The flag records that at least one position
was passed. -/
inductive OccursAt (R : Rules Head) : {n : Nat} → List (Tm Head n) → Bool → Tm Head n → Tm Head n → Prop
  | here {n : Nat} (locals : List (Tm Head n)) (value : Tm Head n) : OccursAt R locals false value value
  | domain (isPi : Bool) {proper : Bool} {n : Nat} {locals : List (Tm Head n)} {value A : Tm Head n}
      {B : Tm Head (n + 1)} :
      OccursAt R locals proper value A → OccursAt R locals true value (binder isPi A B)
  | codomain (isPi : Bool) {proper : Bool} {n : Nat} {locals : List (Tm Head n)} {value A : Tm Head n}
      {B : Tm Head (n + 1)} :
      OccursAt R (Presentation.rename wk A :: locals.map (Presentation.rename wk)) proper
        (Presentation.rename wk value) B → OccursAt R locals true value (binder isPi A B)
  | carrier {proper : Bool} {n : Nat} {locals : List (Tm Head n)} {value A x y : Tm Head n} :
      OccursAt R locals proper value A → OccursAt R locals true value (.id A x y)
  | left {proper : Bool} {n : Nat} {locals : List (Tm Head n)} {value x y : Tm Head n} {u : Head} :
      R.isUniverse u → OccursAt R locals proper value x → OccursAt R locals true value (.id (.head u) x y)
  | right {proper : Bool} {n : Nat} {locals : List (Tm Head n)} {value x y : Tm Head n} {u : Head} :
      R.isUniverse u → OccursAt R locals proper value y → OccursAt R locals true value (.id (.head u) x y)
  | argument {proper : Bool} {n : Nat} {locals : List (Tm Head n)} {value : Tm Head n} {j : Fin n}
      {as : List (Tm Head n)} {T : Tm Head n} {pieces : List (Piece Head n)} {piece : Piece Head n} {u : Head} :
      j.val < locals.length → locals[j.val]? = some T → argParts T T as as = some pieces → piece ∈ pieces →
      piece.leftType = .head u → R.isUniverse u → OccursAt R locals proper value piece.left →
      OccursAt R locals true value (appSpine (.var j) as)

omit [UniverseLevel.LevelOrder L] in
/-- Occurrences are kept by substitutions that fix the bound locals. -/
theorem OccursAt.subst {R : Rules Head} {proper : Bool} {n : Nat} {locals : List (Tm Head n)} {value T : Tm Head n}
    (occurrence : OccursAt R locals proper value T) :
    ∀ {m : Nat} (σ : Sub Head n m), Fixes σ locals.length → locals.length ≤ m →
      OccursAt R (locals.map (Presentation.subst σ)) proper (Presentation.subst σ value) (Presentation.subst σ T) := by
  induction occurrence with
  | here locals value => exact fun σ _ _ => .here _ _
  | domain isPi _ ih =>
      intro m σ fixes bound
      rw [subst_binder]
      exact .domain isPi (ih σ fixes bound)
  | @codomain isPi proper n locals value A B _ ih =>
      intro m σ fixes bound
      rw [subst_binder]
      have inner := ih (liftSub σ) (by simpa using fixes.lift) (by simp; omega)
      have localsSame : (Presentation.rename wk A :: locals.map (Presentation.rename wk)).map
          (Presentation.subst (liftSub σ)) =
          Presentation.rename wk (Presentation.subst σ A) :: (locals.map (Presentation.subst σ)).map
            (Presentation.rename wk) := by
        rw [List.map_cons, subst_liftSub_wk, List.map_map, List.map_map]
        congr 1
        congr 1
        funext t
        exact subst_liftSub_wk σ t
      rw [localsSame, subst_liftSub_wk] at inner
      exact .codomain isPi inner
  | carrier _ ih => exact fun σ fixes bound => .carrier (ih σ fixes bound)
  | left hu _ ih => exact fun σ fixes bound => .left hu (ih σ fixes bound)
  | right hu _ ih => exact fun σ fixes bound => .right hu (ih σ fixes bound)
  | @argument proper n locals value j as T pieces piece u small looked read member domain hu _ ih =>
      intro m σ fixes bound
      have hm : j.val < m := by omega
      have fixedHead : σ j = .var ⟨j.val, hm⟩ := fixes j.val j.isLt hm small
      rw [subst_appSpine]
      change OccursAt R _ _ _ (appSpine (σ j) _)
      rw [fixedHead]
      refine .argument (j := ⟨j.val, hm⟩) (T := Presentation.subst σ T) (pieces := pieces.map (Piece.subst σ))
        (piece := piece.subst σ) (u := u) (by simpa using small) (by simp [looked]) (argParts_subst σ as as read)
        (List.mem_map.mpr ⟨piece, member, rfl⟩) (by simp [Piece.subst, domain, Presentation.subst]) hu
        (ih σ fixes bound)

/-! ## Normal forms -/

section Normal

variable (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R) (heads : HeadPreserving S.R)
  (algebra : CumulativeAlgebra S.R) (rigid : ∀ name, S.roles name = .rigid)
  (complete : AlgorithmicComplete S.R S.roles)

include facts roots heads algebra rigid complete in
/-- **The normal form of a spine along literal Π types**, with the normal form of each argument among its
arguments. -/
theorem argParts_forms {n : Nat} {Γ : Ctx Head n} (formed : CtxFormed S.R Γ) :
    ∀ (as bs : List (Tm Head n)) {TL TR f fn : Tm Head n} {pieces : List (Piece Head n)},
      argParts TL TR as bs = some pieces → Long S.R S.roles (.spine Γ fn TL) → Equal S.R Γ f fn TL →
      (∀ piece ∈ pieces, TypedEquality.Typed S.R Γ piece.left piece.leftType) →
      ∃ ns : List (Tm Head n), Long S.R S.roles (.spine Γ (appSpine fn ns) (argFinal TL as)) ∧
        Equal S.R Γ (appSpine f as) (appSpine fn ns) (argFinal TL as) ∧
        ∀ piece ∈ pieces, ∃ na ∈ ns, NormalForm S.R S.roles Γ piece.left na piece.leftType
  | [], bs, TL, TR, f, fn, pieces, found, long, same, _ => by
      obtain ⟨rfl, rfl⟩ := argParts_nil_cases found
      refine ⟨[], ?_, ?_, fun _ member => absurd member List.not_mem_nil⟩ <;> rw [argFinal_nil] <;> assumption
  | a :: as, [], _, _, _, _, _, found, _, _, _ => (argParts_right_nil found).elim
  | a :: as, b :: bs, TL, TR, f, fn, pieces, found, long, same, typed => by
      obtain ⟨D, E, DR, ER, rest, rfl, rfl, computed, rfl⟩ := argParts_cons_cases found
      have ta := typed _ List.mem_cons_self
      obtain ⟨na, nA⟩ := long_exists facts roots heads algebra rigid complete formed ta
      have tPi := Typed.isType long.spine_typed formed
      obtain ⟨_, ⟨v, hv, tE⟩⟩ := IsType.pi_parts tPi
      have longApp : Long S.R S.roles (.spine Γ (.app fn na) (inst0 a E)) :=
        .app long (IsType.refl tPi) nA.1 (TypeEq.of_instantiateEq tE hv ta nA.2)
      have applied : Equal S.R Γ (.app f a) (.app fn na) (inst0 a E) := Derivable.appCong same nA.2
      obtain ⟨ns, longRest, equalRest, forms⟩ := argParts_forms formed as bs computed longApp applied
        (fun piece member => typed piece (List.mem_cons_of_mem _ member))
      refine ⟨na :: ns, longRest, equalRest, fun piece member => ?_⟩
      rcases List.mem_cons.mp member with rfl | inside
      · exact ⟨na, List.mem_cons_self, nA⟩
      · obtain ⟨other, here, form⟩ := forms piece inside
        exact ⟨other, List.mem_cons_of_mem _ here, form⟩

include facts roots heads algebra rigid complete in
/-- **Normal forms along positions, endpoints and spine arguments**: when `V` occurs in `T` and `V` is equal
to a normal type `N`, `T` has a normal form with at least as many nodes as `N`, and strictly more when the
occurrence is proper. -/
theorem normal_occursAt {proper : Bool} {n : Nat} {locals : List (Tm Head n)} {V T : Tm Head n}
    (occurrence : OccursAt S.R locals proper V T) :
    ∀ {Γ : Ctx Head n}, CtxFormed S.R Γ → LocalTypes Γ locals → ∀ {N : Tm Head n}, Long S.R S.roles (.type Γ N) →
      TypeEq S.R Γ V N → IsType S.R Γ T →
      ∃ W, Long S.R S.roles (.type Γ W) ∧ TypeEq S.R Γ T W ∧ nodes N ≤ nodes W ∧
        (proper = true → nodes N < nodes W) := by
  induction occurrence with
  | here locals value =>
      intro Γ _ _ N lN VN _
      exact ⟨N, lN, VN, le_refl _, fun h => absurd h (by decide)⟩
  | domain isPi _ ih =>
      intro Γ formed types N lN VN isType
      obtain ⟨isA, _⟩ := binder_parts_typed isPi isType
      obtain ⟨WA, lWA, AWA, le, _⟩ := ih formed types lN VN isA
      obtain ⟨W, lW, TW, larger⟩ :=
        normal_binder facts roots heads algebra rigid complete isPi formed lWA AWA isType
      exact ⟨W, lW, TW, by omega, fun _ => by omega⟩
  | @codomain isPi _ _ locals value A B _ ih =>
      intro Γ formed types N lN VN isType
      obtain ⟨isA, v, hv, tB⟩ := binder_parts_typed isPi isType
      have lN' := lN.type_weaken facts formed isA
      have VN' : TypeEq S.R (.snoc Γ A) (Presentation.rename wk value) (Presentation.rename wk N) :=
        VN.rename (CtxRen.wk Γ A)
      obtain ⟨WB, lWB, BWB, le, _⟩ := ih (formed.snoc isA) (types.under A) lN' VN' ⟨v, hv, tB⟩
      obtain ⟨W, lW, TW, larger⟩ :=
        ContextualDependentOccursFull.normal_codomain facts roots heads algebra rigid complete isPi formed lWB BWB
          isType
      rw [ContextualDependentOccursFull.nodes_rename] at le
      exact ⟨W, lW, TW, by omega, fun _ => by omega⟩
  | carrier _ ih =>
      intro Γ formed types N lN VN isType
      obtain ⟨u, hu, tId⟩ := isType
      obtain ⟨WA, lWA, AWA, le, _⟩ := ih formed types lN VN ⟨u, hu, (id_typed tId).1⟩
      obtain ⟨W, lW, TW, larger⟩ :=
        ContextualDependentOccursFull.normal_carrier facts roots heads algebra rigid complete formed lWA AWA
          ⟨u, hu, tId⟩
      exact ⟨W, lW, TW, by omega, fun _ => by omega⟩
  | @left _ _ _ _ x y u hu _ ih =>
      intro Γ formed types N lN VN isType
      obtain ⟨v, hv, tId⟩ := isType
      obtain ⟨Wx, lWx, xWx, le, _⟩ := ih formed types lN VN ⟨u, hu, (id_typed tId).2.1⟩
      obtain ⟨W, lW, TW, larger⟩ :=
        normal_endpoint facts roots heads algebra rigid complete formed hu true lWx xWx ⟨v, hv, tId⟩
      exact ⟨W, lW, TW, by omega, fun _ => by omega⟩
  | @right _ _ _ _ x y u hu _ ih =>
      intro Γ formed types N lN VN isType
      obtain ⟨v, hv, tId⟩ := isType
      obtain ⟨Wy, lWy, yWy, le, _⟩ := ih formed types lN VN ⟨u, hu, (id_typed tId).2.2⟩
      obtain ⟨W, lW, TW, larger⟩ :=
        normal_endpoint facts roots heads algebra rigid complete formed hu false lWy yWy ⟨v, hv, tId⟩
      exact ⟨W, lW, TW, by omega, fun _ => by omega⟩
  | @argument proper n locals value j as T pieces piece u small looked read member domain hu _ ih =>
      intro Γ formed types N lN VN isType
      obtain ⟨v, hv, tT⟩ := isType
      have headType := types.head looked
      have principal : ∀ U, TypedEquality.Typed S.R Γ (.var j) U → TypeLe S.R Γ T U := by
        intro U typed
        have le : TypeLe S.R Γ (Ctx.lookup Γ j) U := Typed.generation typed
        rwa [headType] at le
      have th : TypedEquality.Typed S.R Γ (.var j) T := by
        have typed : TypedEquality.Typed S.R Γ (.var j) (Ctx.lookup Γ j) := .var j
        rwa [headType] at typed
      have longHead : Long S.R S.roles (.spine Γ (.var j) T) := by
        refine .var j ?_
        rw [headType]
        exact IsType.refl (Typed.isType th formed)
      obtain ⟨typed, final⟩ := argParts_typed_left facts formed as as read principal th tT
      have ta : TypedEquality.Typed S.R Γ piece.left (.head u) := domain ▸ typed piece member
      obtain ⟨Wa, lWa, aWa, le, strict⟩ := ih formed types lN VN ⟨u, hu, ta⟩
      obtain ⟨ns, longSpine, equalSpine, forms⟩ :=
        argParts_forms facts roots heads algebra rigid complete formed as as read longHead (.refl th) typed
      obtain ⟨na, inside, form⟩ := forms piece member
      rw [domain] at form
      have lna := Long.type_of_universe facts formed hu form.1
      have naWa : TypeEq S.R Γ na Wa :=
        TypeEq.trans S.levels (show TypeEq S.R Γ piece.left na from ⟨u, hu, form.2⟩).symm aWa
      have same := nodes_of_same (long_type_unique facts roots heads algebra complete formed lna lWa naWa)
      have below := TypeLe.toBelow final (Typed.isType tT formed)
      have bigger : nodes na < nodes (appSpine (.var j) ns) := nodes_appSpine_mem inside
      exact ⟨appSpine (.var j) ns, .neutralType longSpine hv below, ⟨v, hv, .subEq equalSpine below⟩,
        by omega, fun _ => by omega⟩

include facts roots heads algebra rigid complete in
/-- **The occurs check along positions, endpoints and spine arguments**: a type is never equal to a type in
which it occurs properly. -/
theorem occursAt_not_typeEq {n : Nat} {Γ : Ctx Head n} (formed : CtxFormed S.R Γ) {locals : List (Tm Head n)}
    (types : LocalTypes Γ locals) {V T : Tm Head n} (occurrence : OccursAt S.R locals true V T)
    (isV : IsType S.R Γ V) (isT : IsType S.R Γ T) : ¬ TypeEq S.R Γ V T := by
  intro same
  obtain ⟨N, lN, atN⟩ := long_type_exists facts roots heads algebra rigid complete formed isV
  obtain ⟨u, hu, tV⟩ := isV
  have VN : TypeEq S.R Γ V N := ⟨u, hu, (atN hu tV).2⟩
  obtain ⟨W, lW, TW, _, larger⟩ :=
    normal_occursAt facts roots heads algebra rigid complete occurrence formed types lN VN isT
  have NW : TypeEq S.R Γ N W := TypeEq.trans S.levels VN.symm (TypeEq.trans S.levels same TW)
  have equalNodes := nodes_of_same (long_type_unique facts roots heads algebra complete formed lN lW NW)
  have := larger rfl
  omega

end Normal

/-! ## Under abstractions -/

/-- **`λ x̄. V ≐ λ x̄. T` at `Π x̄. U`**, with `U` a universe and `V` occurring properly in `T`, with the literal
types of the abstractions read so far. -/
inductive UnderAt (R : Rules Head) : {n : Nat} → List (Tm Head n) → Tm Head n → Tm Head n → Tm Head n → Prop
  | base {n : Nat} {locals : List (Tm Head n)} {u : Head} {V T : Tm Head n} :
      R.isUniverse u → OccursAt R locals true V T → UnderAt R locals (.head u) V T
  | bind {n : Nat} {locals : List (Tm Head n)} {D : Tm Head n} {B V T : Tm Head (n + 1)} :
      UnderAt R (Presentation.rename wk D :: locals.map (Presentation.rename wk)) B V T →
      UnderAt R locals (.pi D B) (.lam V) (.lam T)

omit [UniverseLevel.LevelOrder L] in
theorem UnderAt.subst {R : Rules Head} {n : Nat} {locals : List (Tm Head n)} {annotation left right : Tm Head n}
    (under : UnderAt R locals annotation left right) :
    ∀ {m : Nat} (σ : Sub Head n m), Fixes σ locals.length → locals.length ≤ m →
      UnderAt R (locals.map (Presentation.subst σ)) (Presentation.subst σ annotation) (Presentation.subst σ left)
        (Presentation.subst σ right) := by
  induction under with
  | base universal occurrence => exact fun σ fixes bound => .base universal (occurrence.subst σ fixes bound)
  | @bind n locals D B V T _ ih =>
      intro m σ fixes bound
      have inner := ih (liftSub σ) (by simpa using fixes.lift) (by simp; omega)
      have localsSame : (Presentation.rename wk D :: locals.map (Presentation.rename wk)).map
          (Presentation.subst (liftSub σ)) =
          Presentation.rename wk (Presentation.subst σ D) :: (locals.map (Presentation.subst σ)).map
            (Presentation.rename wk) := by
        rw [List.map_cons, subst_liftSub_wk, List.map_map, List.map_map]
        congr 1
        congr 1
        funext t
        exact subst_liftSub_wk σ t
      rw [localsSame] at inner
      exact .bind inner

section Refutation

variable (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R) (heads : HeadPreserving S.R)
  (algebra : CumulativeAlgebra S.R) (rigid : ∀ name, S.roles name = .rigid)
  (complete : AlgorithmicComplete S.R S.roles)

include facts roots heads algebra rigid complete in
/-- **The occurs check under abstractions**: such an equation never holds. -/
theorem underAt_not_equal {n : Nat} {locals : List (Tm Head n)} {annotation left right : Tm Head n}
    (under : UnderAt S.R locals annotation left right) :
    ∀ {Δ : Ctx Head n}, CtxFormed S.R Δ → LocalTypes Δ locals → Typed S.R Δ left annotation →
      Typed S.R Δ right annotation → ¬ Equal S.R Δ left right annotation := by
  induction under with
  | base universal occurrence =>
      intro Δ formed types tLeft tRight same
      exact occursAt_not_typeEq facts roots heads algebra rigid complete formed types occurrence ⟨_, universal, tLeft⟩
        ⟨_, universal, tRight⟩ ⟨_, universal, same⟩
  | @bind n locals D B V T _ ih =>
      intro Δ formed types tLeft tRight same
      obtain ⟨⟨u, hu, tD⟩, _⟩ := IsType.pi_parts (Typed.isType tLeft formed)
      exact ih (formed.snoc ⟨u, hu, tD⟩) (types.under D) (Typed.lam_inv facts tLeft formed)
        (Typed.lam_inv facts tRight formed) (ContextualDependentOccursFull.lam_equal_inv facts formed same)

end Refutation

/-! ## Deciding an occurrence -/

variable [DecidableEq Head] [∀ head, Decidable (S.R.isUniverse head)]

/-- **The decision of a proper occurrence**, with a budget of positions; no reduction. -/
def occursAtCode : Nat → {n : Nat} → List (Tm Head n) → Tm Head n → Tm Head n → Bool
  | 0, _, _, _, _ => false
  | fuel + 1, _, locals, value, T =>
      match T with
      | .pi A B => decide (A = value) || occursAtCode fuel locals value A ||
          decide (B = Presentation.rename wk value) ||
          occursAtCode fuel (Presentation.rename wk A :: locals.map (Presentation.rename wk))
            (Presentation.rename wk value) B
      | .sigma A B => decide (A = value) || occursAtCode fuel locals value A ||
          decide (B = Presentation.rename wk value) ||
          occursAtCode fuel (Presentation.rename wk A :: locals.map (Presentation.rename wk))
            (Presentation.rename wk value) B
      | .id A x y => decide (A = value) || occursAtCode fuel locals value A ||
          (universeCode (S := S) A && (decide (x = value) || occursAtCode fuel locals value x ||
            decide (y = value) || occursAtCode fuel locals value y))
      | .app f a =>
          match spineOf (.app f a) with
          | some (j, as) =>
              if j.val < locals.length then
                match locals[j.val]? with
                | some type =>
                    match argParts type type as as with
                    | some pieces => pieces.any fun piece => universeCode (S := S) piece.leftType &&
                        (decide (piece.left = value) || occursAtCode fuel locals value piece.left)
                    | none => false
                | none => false
              else false
          | none => false
      | .var _ | .const _ | .head _ | .lam _ | .pair _ _ | .fst _ | .snd _ | .refl _ => false

theorem occursAtCode_sound : ∀ (fuel : Nat) {n : Nat} (locals : List (Tm Head n)) (value T : Tm Head n),
    occursAtCode (S := S) fuel locals value T = true → OccursAt S.R locals true value T
  | 0, _, _, _, _, found => by simp [occursAtCode] at found
  | fuel + 1, _, locals, value, .pi A B, found => by
      simp only [occursAtCode, Bool.or_eq_true, decide_eq_true_eq] at found
      rcases found with ((same | inner) | same) | inner
      · subst same
        exact .domain true (.here _ _)
      · exact .domain true (occursAtCode_sound fuel locals value A inner)
      · subst same
        exact .codomain true (.here _ _)
      · exact .codomain true (occursAtCode_sound fuel _ _ B inner)
  | fuel + 1, _, locals, value, .sigma A B, found => by
      simp only [occursAtCode, Bool.or_eq_true, decide_eq_true_eq] at found
      rcases found with ((same | inner) | same) | inner
      · subst same
        exact .domain false (.here _ _)
      · exact .domain false (occursAtCode_sound fuel locals value A inner)
      · subst same
        exact .codomain false (.here _ _)
      · exact .codomain false (occursAtCode_sound fuel _ _ B inner)
  | fuel + 1, _, locals, value, .id A x y, found => by
      simp only [occursAtCode, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at found
      rcases found with (same | inner) | ⟨universal, ((sameX | insideX) | sameY) | insideY⟩
      · subst same
        exact .carrier (.here _ _)
      · exact .carrier (occursAtCode_sound fuel locals value A inner)
      · obtain ⟨u, rfl, hu⟩ := universeCode_spec universal
        subst sameX
        exact .left hu (.here _ _)
      · obtain ⟨u, rfl, hu⟩ := universeCode_spec universal
        exact .left hu (occursAtCode_sound fuel locals value x insideX)
      · obtain ⟨u, rfl, hu⟩ := universeCode_spec universal
        subst sameY
        exact .right hu (.here _ _)
      · obtain ⟨u, rfl, hu⟩ := universeCode_spec universal
        exact .right hu (occursAtCode_sound fuel locals value y insideY)
  | fuel + 1, _, locals, value, .app f a, found => by
      simp only [occursAtCode] at found
      cases spine : spineOf (Tm.app f a) with
      | none => rw [spine] at found; cases found
      | some read =>
          obtain ⟨j, as⟩ := read
          rw [spine] at found
          dsimp only at found
          by_cases small : j.val < locals.length
          · rw [if_pos small] at found
            cases looked : locals[j.val]? with
            | none => rw [looked] at found; cases found
            | some type =>
                rw [looked] at found
                dsimp only at found
                cases parts : argParts type type as as with
                | none => rw [parts] at found; cases found
                | some pieces =>
                    rw [parts] at found
                    dsimp only at found
                    obtain ⟨piece, member, test⟩ := List.any_eq_true.mp found
                    simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at test
                    obtain ⟨universal, same | inner⟩ := test
                    · obtain ⟨u, domain, hu⟩ := universeCode_spec universal
                      rw [spineOf_spec spine]
                      exact .argument (proper := false) small looked parts member domain hu
                        (by rw [same]; exact .here _ _)
                    · obtain ⟨u, domain, hu⟩ := universeCode_spec universal
                      rw [spineOf_spec spine]
                      exact .argument small looked parts member domain hu
                        (occursAtCode_sound fuel locals value piece.left inner)
          · rw [if_neg small] at found
            cases found
  | fuel + 1, _, _, _, .var _, found | fuel + 1, _, _, _, .const _, found | fuel + 1, _, _, _, .head _, found
  | fuel + 1, _, _, _, .lam _, found | fuel + 1, _, _, _, .pair _ _, found | fuel + 1, _, _, _, .fst _, found
  | fuel + 1, _, _, _, .snd _, found | fuel + 1, _, _, _, .refl _, found => by simp [occursAtCode] at found

/-- **The decision under abstractions**, with the budget of positions given by the size of the right side. -/
def underAtCode : {n : Nat} → List (Tm Head n) → Tm Head n → Tm Head n → Tm Head n → Bool
  | _, locals, .pi D B, .lam V, .lam T =>
      underAtCode (Presentation.rename wk D :: locals.map (Presentation.rename wk)) B V T
  | _, locals, .head u, V, T => decide (S.R.isUniverse u) && occursAtCode (S := S) (nodes T) locals V T
  | _, _, _, _, _ => false

theorem underAtCode_cases {n : Nat} {locals : List (Tm Head n)} {annotation left right : Tm Head n}
    (found : underAtCode (S := S) locals annotation left right = true) :
    (∃ D B V T, annotation = .pi D B ∧ left = .lam V ∧ right = .lam T ∧
        underAtCode (S := S) (Presentation.rename wk D :: locals.map (Presentation.rename wk)) B V T = true) ∨
      ∃ u, annotation = .head u ∧ S.R.isUniverse u ∧ occursAtCode (S := S) (nodes right) locals left right = true := by
  cases annotation with
  | pi D B =>
      cases left with
      | lam V =>
          cases right with
          | lam T => exact .inl ⟨D, B, V, T, rfl, rfl, rfl, by simpa [underAtCode] using found⟩
          | _ => simp [underAtCode] at found
      | _ => simp [underAtCode] at found
  | head u =>
      simp only [underAtCode, Bool.and_eq_true, decide_eq_true_eq] at found
      exact .inr ⟨u, rfl, found⟩
  | _ => simp [underAtCode] at found

theorem underAtCode_sound : ∀ {n : Nat} (locals : List (Tm Head n)) (annotation left right : Tm Head n),
    underAtCode (S := S) locals annotation left right = true → UnderAt S.R locals annotation left right
  | _, locals, .pi D B, left, right, found => by
      rcases underAtCode_cases found with ⟨D', B', V, T, same, rfl, rfl, inner⟩ | ⟨_, same, _⟩
      · injection same with _ sameD sameB
        subst sameD
        subst sameB
        exact .bind (underAtCode_sound _ B V T inner)
      · cases same
  | _, locals, .head u, left, right, found => by
      rcases underAtCode_cases found with ⟨_, _, _, _, same, _⟩ | ⟨u', same, universal, inner⟩
      · cases same
      · simp only [Tm.head.injEq] at same
        subst same
        exact .base universal (occursAtCode_sound _ _ _ _ inner)
  | _, _, .var _, _, _, found | _, _, .const _, _, _, found | _, _, .sigma _ _, _, _, found
  | _, _, .id _ _ _, _, _, found | _, _, .lam _, _, _, found | _, _, .app _ _, _, _, found
  | _, _, .pair _ _, _, _, found | _, _, .fst _, _, _, found | _, _, .snd _, _, _, found
  | _, _, .refl _, _, _, found => by
      rcases underAtCode_cases found with ⟨_, _, _, _, same, _⟩ | ⟨_, same, _⟩ <;> cases same

/-! ## The rule -/

/-- **A store equation read under its abstractions with a proper occurrence along positions, endpoints and
spine arguments**, both sides at one annotation code. -/
structure ArgumentShape {Θ : Context S.R} (equation : Equation (TotalTerm Θ)) : Type where
  same : equation.2.1.code = equation.1.1.code
  under : UnderAt S.R [] equation.1.1.code equation.1.2.code equation.2.2.code

/-- Read the shape from the codes; no budget. -/
def argumentShape {Θ : Context S.R} (equation : Equation (TotalTerm Θ)) : Option (ArgumentShape equation) :=
  if same : equation.2.1.code = equation.1.1.code then
    if found : underAtCode (S := S) [] equation.1.1.code equation.1.2.code equation.2.2.code = true then
      some ⟨same, underAtCode_sound _ _ _ _ found⟩
    else none
  else none

variable (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R) (heads : HeadPreserving S.R)
  (algebra : CumulativeAlgebra S.R) (rigid : ∀ name, S.roles name = .rigid)
  (complete : AlgorithmicComplete S.R S.roles)

omit [DecidableEq Head] [∀ head, Decidable (S.R.isUniverse head)] in
include facts roots heads algebra rigid complete in
/-- **Such an equation has no solution at any later context.** -/
theorem ArgumentShape.refutes {Θ : Context S.R} {equation : Equation (TotalTerm Θ)} (shape : ArgumentShape equation)
    {Δ : Context S.R} (σ : Δ ⟶ Θ) : ¬ (frames S.levels).Solves σ equation := by
  intro solved
  rw [solves_raw] at solved
  have tLeft := equation.1.2.typed.substitute σ.typed
  have tRight := equation.2.2.typed.substitute σ.typed
  rw [shape.same] at tRight
  have moved := shape.under.subst σ.substitution (fun _ _ _ small => absurd small (Nat.not_lt_zero _))
    (Nat.zero_le _)
  rw [List.map_nil] at moved
  exact underAt_not_equal facts roots heads algebra rigid complete moved Δ.formed (LocalTypes.nil _) tLeft tRight
    solved.2

/-- **The spine-argument occurs rule**: refute the store at the first such equation, read in either
orientation. -/
def argumentSearch {Θ : Context S.R} : (problem : EquationStore (TotalTerm Θ)) → Option (Found problem)
  | [] => none
  | equation :: rest =>
      match argumentShape equation with
      | some shape => some (.refuted fun ⟨_, σ, solved⟩ =>
          shape.refutes facts roots heads algebra rigid complete σ (solved equation List.mem_cons_self))
      | none =>
          match argumentShape (swap equation) with
          | some shape => some (.refuted fun ⟨_, σ, solved⟩ =>
              shape.refutes facts roots heads algebra rigid complete σ
                ((solves_swap σ equation).mpr (solved equation List.mem_cons_self)))
          | none => (argumentSearch rest).map (Found.keepLeft equation)

/-- The refutation of the rule on an update of a store, moved back to the store. -/
def argumentOf {Θ : Context S.R} {problem : EquationStore (TotalTerm Θ)} (prepared : Update S.levels problem) :
    Option (PLift (¬ (frames S.levels).Solvable problem)) :=
  match argumentSearch facts roots heads algebra rigid complete prepared.remaining with
  | some (.refuted absent) => some ⟨fun solvable => absent (prepared.solvable_iff.mp solvable)⟩
  | _ => none

/-! ## The arguments round -/

variable [DecidableRel S.R.headEq] [DecidableRel S.R.cumulative]
variable (declared : DeclaredTypesFormed S.R) (choices : ExecutableChecking.HeadChoices S.R)
  (reducer : ExecutableReduction.Reducer S.R) (root : ExecutableReduction.RootEvaluator S.R)
  (normalizes : ∀ {Θ : Context S.R} {type : TypeOver Θ} (term : Term Θ type),
    ∃ code : Tm Head Θ.arity, ContextualDependentNormalChecking.Normal (S := S) code ∧
      Equal S.R Θ.raw term.code code type.code)
  (certifyNormal : ∀ {n : Nat} (term : Tm Head n),
    Option (PLift (ContextualDependentNormalChecking.Normal (S := S) term)))
  (headTypingUnique : ∀ {head first second : Head},
    S.R.headTyping head first → S.R.headTyping head second → first = second)
  (rootComplete : ∀ {n : Nat} (term : Tm Head n), root term = none → ∀ target, ¬ S.R.computation.step term target)

/-- The spine-argument occurs rule on the prepared store with homogeneous twins. -/
def argumentsRefuted (fuel : Nat) {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) :
    Option (PLift (¬ (frames S.levels).Solvable problem)) :=
  argumentOf facts roots heads algebra rigid complete
    (preparedTwins facts roots heads algebra reducer root rootComplete fuel problem)

/-- **One arguments round**: the projections round; when it is stuck, the spine-argument occurs rule on the
prepared store with homogeneous twins. -/
def argumentsRound (fuel : Nat) {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) :
    Round S.levels (weightRank facts roots heads algebra rigid complete) problem :=
  match projectionsRound facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique rootComplete fuel problem with
  | .stuck =>
      match argumentsRefuted facts roots heads algebra rigid complete reducer root rootComplete fuel problem with
      | some absent => .refuted absent.down
      | none => .stuck
  | other => other

/-- **The arguments family**, at the weight rank: the last family of the chain. -/
noncomputable def argumentsFamily : ContextualDependentDecisiveDriver.Family S.levels where
  rank := weightRank facts roots heads algebra rigid complete
  round fuel := argumentsRound facts roots heads algebra rigid complete declared choices reducer root normalizes
    certifyNormal headTypingUnique rootComplete fuel

/-! ## Eventual constancy -/

variable (stable : ∀ {n : Nat} (fuel : Nat) (term : Tm Head n),
  Keeps (reducer fuel term) (reducer (fuel + 1) term))

omit [DecidableRel S.R.cumulative] in
include stable in
theorem argumentsRefuted_const {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) :
    EventuallyConst fun fuel =>
      (argumentsRefuted facts roots heads algebra rigid complete reducer root rootComplete fuel problem).isSome := by
  unfold argumentsRefuted preparedTwins
  exact EventuallyConst.dep (h := fun fuel => ContextualDependentNormalizing.prepare root rootComplete facts roots heads
      fuel problem)
    (k := fun fuel prepared => (argumentOf facts roots heads algebra rigid complete
      (prepared.then (collapseOf (collapsed facts roots heads algebra reducer fuel prepared.remaining)))).isSome)
    (prepare_const root rootComplete facts roots heads problem)
    (fun prepared => EventuallyConst.comp (fun store => (argumentOf facts roots heads algebra rigid complete
        (prepared.then (collapseOf store))).isSome)
      (collapsed_const facts roots heads algebra reducer stable prepared.remaining))

theorem argumentsRound_view (fuel : Nat) {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) :
    roundView (argumentsRound facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique rootComplete fuel problem) =
      (roundView (projectionsRound facts roots heads algebra rigid complete declared choices reducer root normalizes
          certifyNormal headTypingUnique rootComplete fuel problem)).or
        (if (argumentsRefuted facts roots heads algebra rigid complete reducer root rootComplete fuel problem).isSome
          then some none else none) := by
  unfold argumentsRound
  cases projectionsRound facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique rootComplete fuel problem with
  | stuck =>
      cases argumentsRefuted facts roots heads algebra rigid complete reducer root rootComplete fuel problem <;> rfl
  | progress update smaller => rfl
  | refuted absent => rfl

include stable in
/-- **The arguments round is eventually constant on every store.** -/
theorem argumentsRound_const {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) :
    EventuallyConst fun fuel => argumentsRound facts roots heads algebra rigid complete declared choices reducer root
      normalizes certifyNormal headTypingUnique rootComplete fuel problem := by
  refine round_const_of_view ?_
  refine EventuallyConst.of_eq (fun fuel => argumentsRound_view facts roots heads algebra rigid complete declared
    choices reducer root normalizes certifyNormal headTypingUnique rootComplete fuel problem) ?_
  exact EventuallyConst.comp (fun pair : Option (Option (Update S.levels problem)) × Bool =>
      pair.1.or (if pair.2 then some none else none))
    (EventuallyConst.pair
      (EventuallyConst.comp roundView (projectionsRound_const facts roots heads algebra rigid complete declared choices
        reducer root normalizes certifyNormal headTypingUnique rootComplete stable problem))
      (argumentsRefuted_const facts roots heads algebra rigid complete reducer root rootComplete stable problem))

include stable in
/-- **The arguments family settles** on every class of stores on which, at each nonempty store and from some
budget on, its round is not stuck and keeps every residual store in the class. -/
noncomputable def argumentsSettledOfConst (holds : {Γ : Context S.R} → EquationStore (TotalTerm Γ) → Prop)
    (eventual : ∀ {Γ : Context S.R} {problem : EquationStore (TotalTerm Γ)}, holds problem → problem ≠ [] →
      ∃ bound, ∀ larger, bound ≤ larger →
        argumentsRound facts roots heads algebra rigid complete declared choices reducer root normalizes
            certifyNormal headTypingUnique rootComplete larger problem ≠ .stuck ∧
        ∀ {update : Update S.levels problem}
          {smaller : Below (weightRank facts roots heads algebra rigid complete update.remaining)
            (weightRank facts roots heads algebra rigid complete problem)},
          argumentsRound facts roots heads algebra rigid complete declared choices reducer root normalizes
              certifyNormal headTypingUnique rootComplete larger problem = .progress update smaller →
            holds update.remaining) :
    ContextualDependentDecisiveDriver.Settled
      (argumentsFamily facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
        headTypingUnique rootComplete) :=
  Settled.ofConst _ (fun problem => argumentsRound_const facts roots heads algebra rigid complete declared choices
    reducer root normalizes certifyNormal headTypingUnique rootComplete stable problem) holds eventual

end ContextualDependentIdEndpointsArguments
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
