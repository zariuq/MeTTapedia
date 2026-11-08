import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentCensusPairEta

/-!
# The occurs check at identity endpoints

R97's full occurs check follows the type-former positions: domains, codomains and carriers. A type can
also occur as an **endpoint** of an identity type whose carrier is a universe: `X ≐ Id U0 X X` at `U1`
is in the dynamic pattern fragment (`X : U0` lives in `U1` by cumulativity), and has no solution.

At a universe carrier an endpoint is itself a type, and its η-long normal form as a term at the universe
is its η-long normal form as a type (`Long.type_of_universe`). So the normal form of `Id U x y` contains
the normal form of `x` with its number of nodes, and an occurrence of `V` at an endpoint, at any depth
along the positions, makes the normal form of the whole type strictly larger than that of `V`
(`normal_inside`). A type is never equal to a type in which it occurs properly along these positions
(`inside_not_typeEq`). The check is read under the leading abstractions of an equation, as R97's occurs
check under abstractions is (`UnderInside`, `underInside_not_equal`): `λ y. X ≐ λ y. Id U0 X y` at
`U0 → U1` is refused.

The **endpoints round** is the pairs round, and when that round is stuck, this occurs check on the
prepared store with homogeneous twins.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentIdEndpoints

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentUpdate ContextualDependentWorklist
open ContextualDependentPatternSolver ContextualDependentDecisiveFragment ContextualDependentFragment
open ContextualDependentRigidFormers ContextualDependentEtaExpansion ContextualDependentConversionBudget
open ContextualDependentEtaLong ContextualDependentOccursCheck ContextualDependentOccursFull
open ContextualDependentRank ContextualDependentTwinsUnder ContextualDependentConstantHeads
open ContextualDependentCensusPairEta ContextualDependentFragmentDecisive

variable {Head L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L}

/-! ## Occurrences along positions and endpoints -/

/-- **`V` occurs in `T` along type-former positions and identity endpoints at a universe.** The flag
records that at least one former was passed. -/
inductive Inside (R : Rules Head) : Bool → {n : Nat} → Tm Head n → Tm Head n → Prop
  | here {n : Nat} (value : Tm Head n) : Inside R false value value
  | domain (isPi : Bool) {proper : Bool} {n : Nat} {value A : Tm Head n} {B : Tm Head (n + 1)} :
      Inside R proper value A → Inside R true value (binder isPi A B)
  | codomain (isPi : Bool) {proper : Bool} {n : Nat} {value A : Tm Head n} {B : Tm Head (n + 1)} :
      Inside R proper (Presentation.rename wk value) B → Inside R true value (binder isPi A B)
  | carrier {proper : Bool} {n : Nat} {value A x y : Tm Head n} :
      Inside R proper value A → Inside R true value (.id A x y)
  | left {proper : Bool} {n : Nat} {value x y : Tm Head n} {u : Head} :
      R.isUniverse u → Inside R proper value x → Inside R true value (.id (.head u) x y)
  | right {proper : Bool} {n : Nat} {value x y : Tm Head n} {u : Head} :
      R.isUniverse u → Inside R proper value y → Inside R true value (.id (.head u) x y)

omit [UniverseLevel.LevelOrder L] in
/-- Occurrences are kept by substitution. -/
theorem Inside.subst {R : Rules Head} {proper : Bool} {n : Nat} {value T : Tm Head n} (inside : Inside R proper value T) :
    ∀ {m : Nat} (σ : Sub Head n m), Inside R proper (Presentation.subst σ value) (Presentation.subst σ T) := by
  induction inside with
  | here value => exact fun σ => .here _
  | domain isPi _ ih =>
      intro m σ
      rw [subst_binder]
      exact .domain isPi (ih σ)
  | codomain isPi _ ih =>
      intro m σ
      rw [subst_binder]
      have inner := ih (liftSub σ)
      rw [subst_liftSub_wk] at inner
      exact .codomain isPi inner
  | carrier _ ih => exact fun σ => .carrier (ih σ)
  | left hu _ ih => exact fun σ => .left hu (ih σ)
  | right hu _ ih => exact fun σ => .right hu (ih σ)

/-! ## Normal forms along the positions and endpoints -/

section Normal

variable (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R) (heads : HeadPreserving S.R)
  (algebra : CumulativeAlgebra S.R) (rigid : ∀ name, S.roles name = .rigid)
  (complete : AlgorithmicComplete S.R S.roles)

include facts roots heads algebra rigid complete in
/-- **An endpoint over a normal type**: an identity type at a universe carrier whose endpoint `x` is equal
to a normal type `W` has a normal form with strictly more nodes than `W`. -/
theorem normal_endpoint {n : Nat} {Γ : Ctx Head n} (formed : CtxFormed S.R Γ) {u : Head} (hu : S.R.isUniverse u)
    {x y W : Tm Head n} (isLeft : Bool) (lW : Long S.R S.roles (.type Γ W)) (xW : TypeEq S.R Γ (if isLeft then x else y) W)
    (isType : IsType S.R Γ (.id (.head u) x y)) :
    ∃ Z, Long S.R S.roles (.type Γ Z) ∧ TypeEq S.R Γ (.id (.head u) x y) Z ∧ nodes W < nodes Z := by
  obtain ⟨v, hv, tId⟩ := isType
  obtain ⟨tU, tx, ty⟩ := id_typed tId
  obtain ⟨nx, lnx, ex⟩ := long_exists facts roots heads algebra rigid complete formed tx
  obtain ⟨ny, lny, ey⟩ := long_exists facts roots heads algebra rigid complete formed ty
  have isZ : IsType S.R Γ (.id (.head u) nx ny) := ⟨v, hv, .idForm tU hv lnx.typed lny.typed⟩
  have lU : Long S.R S.roles (.type Γ (.head u)) := .head ⟨v, hv, tU⟩
  refine ⟨.id (.head u) nx ny, .id lU lnx lny isZ, ⟨v, hv, .idCong (.refl tU) hv ex ey⟩, ?_⟩
  cases isLeft with
  | true =>
      have nxW : TypeEq S.R Γ nx W := TypeEq.trans S.levels (show TypeEq S.R Γ x nx from ⟨u, hu, ex⟩).symm xW
      have same := nodes_of_same (long_type_unique facts roots heads algebra complete formed
        (Long.type_of_universe facts formed hu lnx) lW nxW)
      simp only [nodes]
      omega
  | false =>
      have nyW : TypeEq S.R Γ ny W := TypeEq.trans S.levels (show TypeEq S.R Γ y ny from ⟨u, hu, ey⟩).symm xW
      have same := nodes_of_same (long_type_unique facts roots heads algebra complete formed
        (Long.type_of_universe facts formed hu lny) lW nyW)
      simp only [nodes]
      omega

include facts roots heads algebra rigid complete in
/-- **Normal forms along the positions and endpoints**: when `V` occurs in `T` and `V` is equal to a
normal type `N`, `T` has a normal form with at least as many nodes as `N`, and strictly more when the
occurrence is proper. -/
theorem normal_inside {proper : Bool} {n : Nat} {V T : Tm Head n} (inside : Inside S.R proper V T) :
    ∀ {Γ : Ctx Head n}, CtxFormed S.R Γ → ∀ {N : Tm Head n}, Long S.R S.roles (.type Γ N) →
      TypeEq S.R Γ V N → IsType S.R Γ T →
      ∃ W, Long S.R S.roles (.type Γ W) ∧ TypeEq S.R Γ T W ∧ nodes N ≤ nodes W ∧
        (proper = true → nodes N < nodes W) := by
  induction inside with
  | here value =>
      intro Γ _ N lN VN _
      exact ⟨N, lN, VN, le_refl _, fun h => absurd h (by decide)⟩
  | domain isPi _ ih =>
      intro Γ formed N lN VN isType
      obtain ⟨isA, _⟩ := binder_parts_typed isPi isType
      obtain ⟨WA, lWA, AWA, le, _⟩ := ih formed lN VN isA
      obtain ⟨W, lW, TW, larger⟩ :=
        normal_binder facts roots heads algebra rigid complete isPi formed lWA AWA isType
      exact ⟨W, lW, TW, by omega, fun _ => by omega⟩
  | @codomain isPi _ _ value A B _ ih =>
      intro Γ formed N lN VN isType
      obtain ⟨isA, v, hv, tB⟩ := binder_parts_typed isPi isType
      have lN' := lN.type_weaken facts formed isA
      have VN' : TypeEq S.R (.snoc Γ A) (Presentation.rename wk value) (Presentation.rename wk N) :=
        VN.rename (CtxRen.wk Γ A)
      obtain ⟨WB, lWB, BWB, le, _⟩ := ih (formed.snoc isA) lN' VN' ⟨v, hv, tB⟩
      obtain ⟨W, lW, TW, larger⟩ :=
        normal_codomain facts roots heads algebra rigid complete isPi formed lWB BWB isType
      rw [nodes_rename] at le
      exact ⟨W, lW, TW, by omega, fun _ => by omega⟩
  | carrier _ ih =>
      intro Γ formed N lN VN isType
      obtain ⟨u, hu, tId⟩ := isType
      obtain ⟨WA, lWA, AWA, le, _⟩ := ih formed lN VN ⟨u, hu, (id_typed tId).1⟩
      obtain ⟨W, lW, TW, larger⟩ :=
        normal_carrier facts roots heads algebra rigid complete formed lWA AWA ⟨u, hu, tId⟩
      exact ⟨W, lW, TW, by omega, fun _ => by omega⟩
  | @left _ _ _ x y u hu _ ih =>
      intro Γ formed N lN VN isType
      obtain ⟨v, hv, tId⟩ := isType
      obtain ⟨Wx, lWx, xWx, le, _⟩ := ih formed lN VN ⟨u, hu, (id_typed tId).2.1⟩
      obtain ⟨W, lW, TW, larger⟩ :=
        normal_endpoint facts roots heads algebra rigid complete formed hu true lWx xWx ⟨v, hv, tId⟩
      exact ⟨W, lW, TW, by omega, fun _ => by omega⟩
  | @right _ _ _ x y u hu _ ih =>
      intro Γ formed N lN VN isType
      obtain ⟨v, hv, tId⟩ := isType
      obtain ⟨Wy, lWy, yWy, le, _⟩ := ih formed lN VN ⟨u, hu, (id_typed tId).2.2⟩
      obtain ⟨W, lW, TW, larger⟩ :=
        normal_endpoint facts roots heads algebra rigid complete formed hu false lWy yWy ⟨v, hv, tId⟩
      exact ⟨W, lW, TW, by omega, fun _ => by omega⟩

include facts roots heads algebra rigid complete in
/-- **The occurs check at identity endpoints**: a type is never equal to a type in which it occurs
properly along type-former positions and identity endpoints at a universe. -/
theorem inside_not_typeEq {n : Nat} {Γ : Ctx Head n} (formed : CtxFormed S.R Γ) {V T : Tm Head n}
    (occurrence : Inside S.R true V T) (isV : IsType S.R Γ V) (isT : IsType S.R Γ T) : ¬ TypeEq S.R Γ V T := by
  intro same
  obtain ⟨N, lN, atN⟩ := long_type_exists facts roots heads algebra rigid complete formed isV
  obtain ⟨u, hu, tV⟩ := isV
  have VN : TypeEq S.R Γ V N := ⟨u, hu, (atN hu tV).2⟩
  obtain ⟨W, lW, TW, _, larger⟩ :=
    normal_inside facts roots heads algebra rigid complete occurrence formed lN VN isT
  have NW : TypeEq S.R Γ N W := TypeEq.trans S.levels VN.symm (TypeEq.trans S.levels same TW)
  have equalNodes := nodes_of_same (long_type_unique facts roots heads algebra complete formed lN lW NW)
  have := larger rfl
  omega

end Normal

/-! ## Deciding an occurrence -/

variable [DecidableEq Head] [∀ head, Decidable (S.R.isUniverse head)]

/-- **The decision of a proper occurrence along positions and endpoints**, by the codes. -/
def occursInside : {n : Nat} → Tm Head n → Tm Head n → Bool
  | _, value, .pi A B => decide (A = value) || occursInside value A ||
      decide (B = Presentation.rename wk value) || occursInside (Presentation.rename wk value) B
  | _, value, .sigma A B => decide (A = value) || occursInside value A ||
      decide (B = Presentation.rename wk value) || occursInside (Presentation.rename wk value) B
  | _, value, .id A x y => decide (A = value) || occursInside value A ||
      (universeCode (S := S) A && (decide (x = value) || occursInside value x || decide (y = value) ||
        occursInside value y))
  | _, _, .var _ | _, _, .const _ | _, _, .head _ | _, _, .lam _ | _, _, .app _ _ | _, _, .pair _ _
  | _, _, .fst _ | _, _, .snd _ | _, _, .refl _ => false

omit [DecidableEq Head] in
theorem universeCode_spec {n : Nat} {A : Tm Head n} (found : universeCode (S := S) A = true) :
    ∃ u, A = .head u ∧ S.R.isUniverse u := by
  cases A with
  | head u => exact ⟨u, rfl, by simpa [universeCode] using found⟩
  | _ => simp [universeCode] at found

theorem occursInside_sound : ∀ {n : Nat} (value T : Tm Head n), occursInside (S := S) value T = true →
    Inside S.R true value T
  | _, value, .pi A B, found => by
      simp only [occursInside, Bool.or_eq_true, decide_eq_true_eq] at found
      rcases found with ((same | inner) | same) | inner
      · subst same
        exact .domain true (.here _)
      · exact .domain true (occursInside_sound value A inner)
      · subst same
        exact .codomain true (.here _)
      · exact .codomain true (occursInside_sound _ B inner)
  | _, value, .sigma A B, found => by
      simp only [occursInside, Bool.or_eq_true, decide_eq_true_eq] at found
      rcases found with ((same | inner) | same) | inner
      · subst same
        exact .domain false (.here _)
      · exact .domain false (occursInside_sound value A inner)
      · subst same
        exact .codomain false (.here _)
      · exact .codomain false (occursInside_sound _ B inner)
  | _, value, .id A x y, found => by
      simp only [occursInside, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at found
      rcases found with (same | inner) | ⟨universal, ((sameX | insideX) | sameY) | insideY⟩
      · subst same
        exact .carrier (.here _)
      · exact .carrier (occursInside_sound value A inner)
      · obtain ⟨u, rfl, hu⟩ := universeCode_spec universal
        subst sameX
        exact .left hu (.here _)
      · obtain ⟨u, rfl, hu⟩ := universeCode_spec universal
        exact .left hu (occursInside_sound value x insideX)
      · obtain ⟨u, rfl, hu⟩ := universeCode_spec universal
        subst sameY
        exact .right hu (.here _)
      · obtain ⟨u, rfl, hu⟩ := universeCode_spec universal
        exact .right hu (occursInside_sound value y insideY)
  | _, _, .var _, found | _, _, .const _, found | _, _, .head _, found | _, _, .lam _, found
  | _, _, .app _ _, found | _, _, .pair _ _, found | _, _, .fst _, found | _, _, .snd _, found
  | _, _, .refl _, found => by simp [occursInside] at found

/-! ## Occurrences under abstractions -/

/-- **`λ x̄. V ≐ λ x̄. T` at `Π x̄. U`**, with `U` a universe and `V` occurring properly in `T` along
type-former positions and identity endpoints. -/
inductive UnderInside (R : Rules Head) : {n : Nat} → Tm Head n → Tm Head n → Tm Head n → Prop
  | base {n : Nat} {u : Head} {V T : Tm Head n} : R.isUniverse u → Inside R true V T → UnderInside R (.head u) V T
  | bind {n : Nat} {A : Tm Head n} {B V T : Tm Head (n + 1)} :
      UnderInside R B V T → UnderInside R (.pi A B) (.lam V) (.lam T)

omit [DecidableEq Head] [∀ head, Decidable (S.R.isUniverse head)] [UniverseLevel.LevelOrder L] in
theorem UnderInside.subst {R : Rules Head} {n : Nat} {annotation left right : Tm Head n}
    (under : UnderInside R annotation left right) :
    ∀ {m : Nat} (σ : Sub Head n m),
      UnderInside R (Presentation.subst σ annotation) (Presentation.subst σ left) (Presentation.subst σ right) := by
  induction under with
  | base universal inside => exact fun σ => .base universal (inside.subst σ)
  | bind _ ih => exact fun σ => .bind (ih (liftSub σ))

section Refutation

variable (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R) (heads : HeadPreserving S.R)
  (algebra : CumulativeAlgebra S.R) (rigid : ∀ name, S.roles name = .rigid)
  (complete : AlgorithmicComplete S.R S.roles)

omit [DecidableEq Head] [∀ head, Decidable (S.R.isUniverse head)] in
include facts roots heads algebra rigid complete in
/-- **The occurs check at endpoints, under abstractions**: such an equation never holds. -/
theorem underInside_not_equal {n : Nat} {annotation left right : Tm Head n}
    (under : UnderInside S.R annotation left right) :
    ∀ {Δ : Ctx Head n}, CtxFormed S.R Δ → Typed S.R Δ left annotation → Typed S.R Δ right annotation →
      ¬ Equal S.R Δ left right annotation := by
  induction under with
  | base universal inside =>
      intro Δ formed tLeft tRight same
      exact inside_not_typeEq facts roots heads algebra rigid complete formed inside ⟨_, universal, tLeft⟩
        ⟨_, universal, tRight⟩ ⟨_, universal, same⟩
  | @bind n A B V T _ ih =>
      intro Δ formed tLeft tRight same
      obtain ⟨⟨u, hu, tA⟩, _⟩ := IsType.pi_parts (Typed.isType tLeft formed)
      exact ih (formed.snoc ⟨u, hu, tA⟩) (Typed.lam_inv facts tLeft formed) (Typed.lam_inv facts tRight formed)
        (lam_equal_inv facts formed same)

end Refutation

/-- **The decision of a proper occurrence under abstractions**, endpoints included, by the codes. -/
def underInsideOccurs : {n : Nat} → Tm Head n → Tm Head n → Tm Head n → Bool
  | _, .pi _ B, .lam V, .lam T => underInsideOccurs B V T
  | _, .head u, V, T => decide (S.R.isUniverse u) && occursInside (S := S) V T
  | _, _, _, _ => false

theorem underInsideOccurs_cases {n : Nat} {annotation left right : Tm Head n}
    (found : underInsideOccurs (S := S) annotation left right = true) :
    (∃ D B V T, annotation = .pi D B ∧ left = .lam V ∧ right = .lam T ∧ underInsideOccurs (S := S) B V T = true) ∨
      ∃ u, annotation = .head u ∧ S.R.isUniverse u ∧ occursInside (S := S) left right = true := by
  cases annotation with
  | pi D B =>
      cases left with
      | lam V =>
          cases right with
          | lam T => exact .inl ⟨D, B, V, T, rfl, rfl, rfl, by simpa [underInsideOccurs] using found⟩
          | _ => simp [underInsideOccurs] at found
      | _ => simp [underInsideOccurs] at found
  | head u =>
      simp only [underInsideOccurs, Bool.and_eq_true, decide_eq_true_eq] at found
      exact .inr ⟨u, rfl, found⟩
  | _ => simp [underInsideOccurs] at found

theorem underInsideOccurs_sound : ∀ {n : Nat} (annotation left right : Tm Head n),
    underInsideOccurs (S := S) annotation left right = true → UnderInside S.R annotation left right
  | _, .pi D B, left, right, found => by
      rcases underInsideOccurs_cases found with ⟨D', B', V, T, same, rfl, rfl, inner⟩ | ⟨_, same, _⟩
      · injection same with _ sameD sameB
        subst sameD
        subst sameB
        exact .bind (underInsideOccurs_sound B V T inner)
      · cases same
  | _, .head u, left, right, found => by
      rcases underInsideOccurs_cases found with ⟨_, _, _, _, same, _⟩ | ⟨u', same, universal, inner⟩
      · cases same
      · simp only [Tm.head.injEq] at same
        subst same
        exact .base universal (occursInside_sound _ _ inner)
  | _, .var _, _, _, found | _, .const _, _, _, found | _, .sigma _ _, _, _, found
  | _, .id _ _ _, _, _, found | _, .lam _, _, _, found | _, .app _ _, _, _, found
  | _, .pair _ _, _, _, found | _, .fst _, _, _, found | _, .snd _, _, _, found
  | _, .refl _, _, _, found => by
      rcases underInsideOccurs_cases found with ⟨_, _, _, _, same, _⟩ | ⟨_, same, _⟩ <;> cases same

/-! ## The endpoint occurs rule -/

/-- **A store equation read under its abstractions with a proper occurrence**, endpoints included, both
sides at one annotation code. -/
structure InsideShape {Θ : Context S.R} (equation : Equation (TotalTerm Θ)) : Type where
  same : equation.2.1.code = equation.1.1.code
  under : UnderInside S.R equation.1.1.code equation.1.2.code equation.2.2.code

/-- Read the shape from the codes; no budget. -/
def insideShape {Θ : Context S.R} (equation : Equation (TotalTerm Θ)) : Option (InsideShape equation) :=
  if same : equation.2.1.code = equation.1.1.code then
    if found : underInsideOccurs (S := S) equation.1.1.code equation.1.2.code equation.2.2.code = true then
      some ⟨same, underInsideOccurs_sound _ _ _ found⟩
    else none
  else none

variable (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R) (heads : HeadPreserving S.R)
  (algebra : CumulativeAlgebra S.R) (rigid : ∀ name, S.roles name = .rigid)
  (complete : AlgorithmicComplete S.R S.roles)

omit [DecidableEq Head] [∀ head, Decidable (S.R.isUniverse head)] in
include facts roots heads algebra rigid complete in
/-- **A proper occurrence has no solution at any later context.** -/
theorem InsideShape.refutes {Θ : Context S.R} {equation : Equation (TotalTerm Θ)} (shape : InsideShape equation)
    {Δ : Context S.R} (σ : Δ ⟶ Θ) : ¬ (frames S.levels).Solves σ equation := by
  intro solved
  rw [solves_raw] at solved
  have tLeft := equation.1.2.typed.substitute σ.typed
  have tRight := equation.2.2.typed.substitute σ.typed
  rw [shape.same] at tRight
  exact underInside_not_equal facts roots heads algebra rigid complete (shape.under.subst _) Δ.formed tLeft tRight
    solved.2

/-- **The endpoint occurs rule**: refute the store at the first equation with a proper occurrence, read in
either orientation. -/
def insideSearch {Θ : Context S.R} : (problem : EquationStore (TotalTerm Θ)) → Option (Found problem)
  | [] => none
  | equation :: rest =>
      match insideShape equation with
      | some shape => some (.refuted fun ⟨_, σ, solved⟩ =>
          shape.refutes facts roots heads algebra rigid complete σ (solved equation List.mem_cons_self))
      | none =>
          match insideShape (swap equation) with
          | some shape => some (.refuted fun ⟨_, σ, solved⟩ =>
              shape.refutes facts roots heads algebra rigid complete σ
                ((solves_swap σ equation).mpr (solved equation List.mem_cons_self)))
          | none => (insideSearch rest).map (Found.keepLeft equation)

/-- The refutation of the endpoint occurs rule on an update of a store, moved back to the store. -/
def insideOf {Θ : Context S.R} {problem : EquationStore (TotalTerm Θ)} (prepared : Update S.levels problem) :
    Option (PLift (¬ (frames S.levels).Solvable problem)) :=
  match insideSearch facts roots heads algebra rigid complete prepared.remaining with
  | some (.refuted absent) => some ⟨fun solvable => absent (prepared.solvable_iff.mp solvable)⟩
  | _ => none

/-! ## The endpoints round -/

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

/-- The endpoint occurs rule on the prepared store with homogeneous twins. -/
def endpointsRefuted (fuel : Nat) {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) :
    Option (PLift (¬ (frames S.levels).Solvable problem)) :=
  insideOf facts roots heads algebra rigid complete
    (preparedTwins facts roots heads algebra reducer root rootComplete fuel problem)

/-- **One endpoints round**: the pairs round; when it is stuck, the endpoint occurs rule on the prepared
store with homogeneous twins. -/
def endpointsRound (fuel : Nat) {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) :
    Round S.levels (weightRank facts roots heads algebra rigid complete) problem :=
  match pairsRound facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
      headTypingUnique rootComplete fuel problem with
  | .stuck =>
      match endpointsRefuted facts roots heads algebra rigid complete reducer root rootComplete fuel problem with
      | some absent => .refuted absent.down
      | none => .stuck
  | other => other

/-- **The endpoints family**, at the weight rank. -/
noncomputable def endpointsFamily : ContextualDependentDecisiveDriver.Family S.levels where
  rank := weightRank facts roots heads algebra rigid complete
  round fuel := endpointsRound facts roots heads algebra rigid complete declared choices reducer root normalizes
    certifyNormal headTypingUnique rootComplete fuel

/-! ## Eventual constancy -/

variable (stable : ∀ {n : Nat} (fuel : Nat) (term : Tm Head n),
  Keeps (reducer fuel term) (reducer (fuel + 1) term))

omit [DecidableRel S.R.cumulative] in
include stable in
theorem endpointsRefuted_const {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) :
    EventuallyConst fun fuel =>
      (endpointsRefuted facts roots heads algebra rigid complete reducer root rootComplete fuel problem).isSome := by
  unfold endpointsRefuted preparedTwins
  exact EventuallyConst.dep (h := fun fuel => ContextualDependentNormalizing.prepare root rootComplete facts roots heads
      fuel problem)
    (k := fun fuel prepared => (insideOf facts roots heads algebra rigid complete
      (prepared.then (collapseOf (collapsed facts roots heads algebra reducer fuel prepared.remaining)))).isSome)
    (prepare_const root rootComplete facts roots heads problem)
    (fun prepared => EventuallyConst.comp (fun store => (insideOf facts roots heads algebra rigid complete
        (prepared.then (collapseOf store))).isSome)
      (collapsed_const facts roots heads algebra reducer stable prepared.remaining))

theorem endpointsRound_view (fuel : Nat) {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) :
    roundView (endpointsRound facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique rootComplete fuel problem) =
      (roundView (pairsRound facts roots heads algebra rigid complete declared choices reducer root normalizes
          certifyNormal headTypingUnique rootComplete fuel problem)).or
        (if (endpointsRefuted facts roots heads algebra rigid complete reducer root rootComplete fuel problem).isSome
          then some none else none) := by
  unfold endpointsRound
  cases pairsRound facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
      headTypingUnique rootComplete fuel problem with
  | stuck =>
      cases endpointsRefuted facts roots heads algebra rigid complete reducer root rootComplete fuel problem <;> rfl
  | progress update smaller => rfl
  | refuted absent => rfl

include stable in
/-- **The endpoints round is eventually constant on every store.** -/
theorem endpointsRound_const {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) :
    EventuallyConst fun fuel => endpointsRound facts roots heads algebra rigid complete declared choices reducer root
      normalizes certifyNormal headTypingUnique rootComplete fuel problem := by
  refine round_const_of_view ?_
  refine EventuallyConst.of_eq (fun fuel => endpointsRound_view facts roots heads algebra rigid complete declared
    choices reducer root normalizes certifyNormal headTypingUnique rootComplete fuel problem) ?_
  exact EventuallyConst.comp (fun pair : Option (Option (Update S.levels problem)) × Bool =>
      pair.1.or (if pair.2 then some none else none))
    (EventuallyConst.pair
      (EventuallyConst.comp roundView (pairsRound_const facts roots heads algebra rigid complete declared choices
        reducer root normalizes certifyNormal headTypingUnique rootComplete stable problem))
      (endpointsRefuted_const facts roots heads algebra rigid complete reducer root rootComplete stable problem))

include stable in
/-- **The endpoints family settles** on every class of stores on which, at each nonempty store and from
some budget on, its round is not stuck and keeps every residual store in the class. -/
noncomputable def endpointsSettledOfConst (holds : {Γ : Context S.R} → EquationStore (TotalTerm Γ) → Prop)
    (eventual : ∀ {Γ : Context S.R} {problem : EquationStore (TotalTerm Γ)}, holds problem → problem ≠ [] →
      ∃ bound, ∀ larger, bound ≤ larger →
        endpointsRound facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
            headTypingUnique rootComplete larger problem ≠ .stuck ∧
        ∀ {update : Update S.levels problem}
          {smaller : Below (weightRank facts roots heads algebra rigid complete update.remaining)
            (weightRank facts roots heads algebra rigid complete problem)},
          endpointsRound facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
              headTypingUnique rootComplete larger problem = .progress update smaller →
            holds update.remaining) :
    ContextualDependentDecisiveDriver.Settled
      (endpointsFamily facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
        headTypingUnique rootComplete) :=
  Settled.ofConst _ (fun problem => endpointsRound_const facts roots heads algebra rigid complete declared choices
    reducer root normalizes certifyNormal headTypingUnique rootComplete stable problem) holds eventual

end ContextualDependentIdEndpoints
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
