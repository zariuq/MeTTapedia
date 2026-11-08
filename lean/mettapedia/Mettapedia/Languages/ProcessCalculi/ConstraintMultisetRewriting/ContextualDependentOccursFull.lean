import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentEtaLongWeakening
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentRecognitionConversion

/-!
# The occurs check along every type-former position

R94's occurs check followed the domains of Π and Σ types. Here it follows every position of a type
former whose normal form keeps it: the domain and the **codomain** of a Π or Σ type, and the
**carrier** of an identity type, to any depth. Under a codomain the value is weakened past the bound
variable.

`Within proper V T` says that `V` occurs in `T` along such positions; `proper` records that at least
one former was passed. A type is never equal to a type in which it occurs properly
(`occurrence_not_typeEq`). Let `N` be the normal form of `V`. Along the positions, `T` has a normal
form `W` that keeps every former it passes and whose part at the occurrence is a normal form of
the occurrence (`normal_within`). Under a codomain that part is the normal form of the weakened value,
which is the weakened normal form, with the same number of nodes, because η-long normal forms are kept
by weakening (`Long.type_weaken`). So `W` has strictly more nodes than `N`, while equal normal types are
the same term up to heads (`long_type_unique`).

A **flexible** occurrence, under a metavariable application, is not a former position, so
`X ≐ Π (G X) A` is not refused.

The **full occurs rule** refutes a store with an equation `V ≐ T` (or `T ≐ V`) at a universe where `V`
occurs properly in `T`, with a certificate. The **full occurs round** extends R94's last round, the
recognition round, by it.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentOccursFull

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentUpdate ContextualDependentWorklist
open ContextualDependentPatternSolver ContextualDependentDecisiveFragment ContextualDependentFragment
open ContextualDependentInPlace ContextualDependentRigidFormers ContextualDependentEtaExpansion
open ContextualDependentConversionBudget ContextualDependentEtaLong ContextualDependentOccursCheck
open ContextualDependentRecognitionConversion

variable {Head L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L}

/-! ## Nodes under renaming -/

/-- Renaming does not change the number of nodes. -/
theorem nodes_rename : ∀ {n m : Nat} (ρ : Ren n m) (t : Tm Head n), nodes (Presentation.rename ρ t) = nodes t
  | _, _, _, .var _ => rfl
  | _, _, _, .const _ => rfl
  | _, _, _, .head _ => rfl
  | _, _, ρ, .pi A B => by simp only [Presentation.rename, nodes, nodes_rename ρ A, nodes_rename (liftRen ρ) B]
  | _, _, ρ, .sigma A B => by simp only [Presentation.rename, nodes, nodes_rename ρ A, nodes_rename (liftRen ρ) B]
  | _, _, ρ, .id A x y => by simp only [Presentation.rename, nodes, nodes_rename ρ A, nodes_rename ρ x, nodes_rename ρ y]
  | _, _, ρ, .lam b => by simp only [Presentation.rename, nodes, nodes_rename (liftRen ρ) b]
  | _, _, ρ, .app f a => by simp only [Presentation.rename, nodes, nodes_rename ρ f, nodes_rename ρ a]
  | _, _, ρ, .pair a b => by simp only [Presentation.rename, nodes, nodes_rename ρ a, nodes_rename ρ b]
  | _, _, ρ, .fst p => by simp only [Presentation.rename, nodes, nodes_rename ρ p]
  | _, _, ρ, .snd p => by simp only [Presentation.rename, nodes, nodes_rename ρ p]
  | _, _, ρ, .refl z => by simp only [Presentation.rename, nodes, nodes_rename ρ z]

/-! ## Occurrences along type-former positions -/

/-- **`V` occurs in `T` along type-former positions**: `T` is `V`, or a Π or Σ type with `V` in its
domain or the weakened `V` in its codomain, or an identity type with `V` in its carrier. The flag
records that at least one former was passed. -/
inductive Within : Bool → {n : Nat} → Tm Head n → Tm Head n → Prop
  | here {n : Nat} (value : Tm Head n) : Within false value value
  | domain (isPi : Bool) {proper : Bool} {n : Nat} {value A : Tm Head n} {B : Tm Head (n + 1)} :
      Within proper value A → Within true value (binder isPi A B)
  | codomain (isPi : Bool) {proper : Bool} {n : Nat} {value A : Tm Head n} {B : Tm Head (n + 1)} :
      Within proper (Presentation.rename wk value) B → Within true value (binder isPi A B)
  | carrier {proper : Bool} {n : Nat} {value A x y : Tm Head n} :
      Within proper value A → Within true value (.id A x y)

/-- R94's occurrences along domains are proper occurrences. -/
theorem DomainOccurrence.within {n : Nat} {value T : Tm Head n} (occurrence : DomainOccurrence value T) :
    Within true value T := by
  induction occurrence with
  | here isPi => exact .domain isPi (.here _)
  | deeper isPi _ ih => exact .domain isPi ih

/-- Occurrences are kept by substitution. -/
theorem Within.subst {proper : Bool} {n : Nat} {value T : Tm Head n} (within : Within proper value T) :
    ∀ {m : Nat} (σ : Sub Head n m), Within proper (Presentation.subst σ value) (Presentation.subst σ T) := by
  induction within with
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

variable [DecidableEq Head]

/-- **The decision of a proper occurrence**, by the codes. -/
def occurs : {n : Nat} → Tm Head n → Tm Head n → Bool
  | _, value, .pi A B => decide (A = value) || occurs value A ||
      decide (B = Presentation.rename wk value) || occurs (Presentation.rename wk value) B
  | _, value, .sigma A B => decide (A = value) || occurs value A ||
      decide (B = Presentation.rename wk value) || occurs (Presentation.rename wk value) B
  | _, value, .id A _ _ => decide (A = value) || occurs value A
  | _, _, .var _ | _, _, .const _ | _, _, .head _ | _, _, .lam _ | _, _, .app _ _ | _, _, .pair _ _
  | _, _, .fst _ | _, _, .snd _ | _, _, .refl _ => false

theorem occurs_sound : ∀ {n : Nat} (value T : Tm Head n), occurs value T = true → Within true value T
  | _, value, .pi A B, found => by
      simp only [occurs, Bool.or_eq_true, decide_eq_true_eq] at found
      rcases found with ((same | inner) | same) | inner
      · subst same
        exact .domain true (.here _)
      · exact .domain true (occurs_sound value A inner)
      · subst same
        exact .codomain true (.here _)
      · exact .codomain true (occurs_sound _ B inner)
  | _, value, .sigma A B, found => by
      simp only [occurs, Bool.or_eq_true, decide_eq_true_eq] at found
      rcases found with ((same | inner) | same) | inner
      · subst same
        exact .domain false (.here _)
      · exact .domain false (occurs_sound value A inner)
      · subst same
        exact .codomain false (.here _)
      · exact .codomain false (occurs_sound _ B inner)
  | _, value, .id A x y, found => by
      simp only [occurs, Bool.or_eq_true, decide_eq_true_eq] at found
      rcases found with same | inner
      · subst same
        exact .carrier (.here _)
      · exact .carrier (occurs_sound value A inner)
  | _, _, .var _, found | _, _, .const _, found | _, _, .head _, found | _, _, .lam _, found
  | _, _, .app _ _, found | _, _, .pair _ _, found | _, _, .fst _, found | _, _, .snd _, found
  | _, _, .refl _, found => by simp [occurs] at found

/-! ## Normal forms along the positions -/

section Normal

variable (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R) (heads : HeadPreserving S.R)
  (algebra : CumulativeAlgebra S.R) (rigid : ∀ name, S.roles name = .rigid)
  (complete : AlgorithmicComplete S.R S.roles)

omit [DecidableEq Head] in
include facts roots heads algebra rigid complete in
/-- **A codomain over a normal family**: a binder type whose family is equal to a normal type `E`
under the domain has a normal form with strictly more nodes than `E`. -/
theorem normal_codomain (isPi : Bool) {n : Nat} {Γ : Ctx Head n} (formed : CtxFormed S.R Γ) {A : Tm Head n}
    {B E : Tm Head (n + 1)} (lE : Long S.R S.roles (.type (.snoc Γ A) E)) (BE : TypeEq S.R (.snoc Γ A) B E)
    (isType : IsType S.R Γ (binder isPi A B)) :
    ∃ W, Long S.R S.roles (.type Γ W) ∧ TypeEq S.R Γ (binder isPi A B) W ∧ nodes E < nodes W := by
  obtain ⟨isA, _⟩ := binder_parts_typed isPi isType
  obtain ⟨D, lD, atD⟩ := long_type_exists facts roots heads algebra rigid complete formed isA
  obtain ⟨u, hu, tA⟩ := isA
  obtain ⟨tD, eAD⟩ := atD hu tA
  have AD : TypeEq S.R Γ A D := ⟨u, hu, eAD⟩
  have there : CtxEq S.R (.snoc Γ A) (.snoc Γ D) := .snoc (CtxEq.refl Γ formed) AD.symm
  have back : CtxEq S.R (.snoc Γ D) (.snoc Γ A) := .snoc (CtxEq.refl Γ formed) AD
  have lE' : Long S.R S.roles (.type (.snoc Γ D) E) := lE.stable S.levels there back
  obtain ⟨v, hv, tE⟩ := lE'.isType
  obtain ⟨w, joined⟩ := S.levels.join_exists hu hv
  have isW : IsType S.R Γ (binder isPi D E) :=
    ⟨w, (S.levels.join_level joined).1, binder_formed isPi tD hu tE hv joined⟩
  refine ⟨binder isPi D E, binder_long isPi lD lE' isW, ?_, ?_⟩
  · exact (typeEq_binder_iff facts isPi formed).mpr ⟨AD, BE⟩
  · cases isPi <;> simp only [binder, nodes] <;> omega

omit [DecidableEq Head] in
include facts roots heads algebra rigid complete in
/-- **A carrier over a normal type**: an identity type whose carrier is equal to a normal type `C` has
a normal form with strictly more nodes than `C`. -/
theorem normal_carrier {n : Nat} {Γ : Ctx Head n} (formed : CtxFormed S.R Γ) {A C x y : Tm Head n}
    (lC : Long S.R S.roles (.type Γ C)) (AC : TypeEq S.R Γ A C) (isType : IsType S.R Γ (.id A x y)) :
    ∃ W, Long S.R S.roles (.type Γ W) ∧ TypeEq S.R Γ (.id A x y) W ∧ nodes C < nodes W := by
  obtain ⟨u, hu, tId⟩ := isType
  obtain ⟨_, tx, ty⟩ := id_typed tId
  obtain ⟨nx, lx, ex⟩ := long_exists facts roots heads algebra rigid complete formed tx
  obtain ⟨ny, ly, ey⟩ := long_exists facts roots heads algebra rigid complete formed ty
  obtain ⟨u', hu', eAC⟩ := AC
  have tC : Typed S.R Γ C (.head u') := (Equal.typed eAC formed).2
  have lx' := lx.convType S.levels ⟨u', hu', eAC⟩
  have ly' := ly.convType S.levels ⟨u', hu', eAC⟩
  have isW : IsType S.R Γ (.id C nx ny) := ⟨u', hu', .idForm tC hu' lx'.typed ly'.typed⟩
  refine ⟨.id C nx ny, .id lC lx' ly' isW, ⟨u', hu', .idCong eAC hu' ex ey⟩, ?_⟩
  simp only [nodes]
  omega

omit [DecidableEq Head] in
include facts roots heads algebra rigid complete in
/-- **Normal forms along the positions**: when `V` occurs in `T` and `V` is equal to a normal type `N`,
`T` has a normal form with at least as many nodes as `N`, and strictly more when the occurrence is
proper. -/
theorem normal_within {proper : Bool} {n : Nat} {V T : Tm Head n} (within : Within proper V T) :
    ∀ {Γ : Ctx Head n}, CtxFormed S.R Γ → ∀ {N : Tm Head n}, Long S.R S.roles (.type Γ N) →
      TypeEq S.R Γ V N → IsType S.R Γ T →
      ∃ W, Long S.R S.roles (.type Γ W) ∧ TypeEq S.R Γ T W ∧ nodes N ≤ nodes W ∧
        (proper = true → nodes N < nodes W) := by
  induction within with
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

omit [DecidableEq Head] in
include facts roots heads algebra rigid complete in
/-- **The full occurs check**: a type is never equal to a type in which it occurs properly along
type-former positions, codomains and carriers included. -/
theorem occurrence_not_typeEq {n : Nat} {Γ : Ctx Head n} (formed : CtxFormed S.R Γ) {V T : Tm Head n}
    (occurrence : Within true V T) (isV : IsType S.R Γ V) (isT : IsType S.R Γ T) : ¬ TypeEq S.R Γ V T := by
  intro same
  obtain ⟨N, lN, atN⟩ := long_type_exists facts roots heads algebra rigid complete formed isV
  obtain ⟨u, hu, tV⟩ := isV
  have VN : TypeEq S.R Γ V N := ⟨u, hu, (atN hu tV).2⟩
  obtain ⟨W, lW, TW, _, larger⟩ :=
    normal_within facts roots heads algebra rigid complete occurrence formed lN VN isT
  have NW : TypeEq S.R Γ N W := TypeEq.trans S.levels VN.symm (TypeEq.trans S.levels same TW)
  have equalNodes := nodes_of_same (long_type_unique facts roots heads algebra complete formed lN lW NW)
  have := larger rfl
  omega

end Normal

/-! ## The full occurs rule -/

/-- **An equation `V ≐ T` at a universe with `V` occurring properly in `T`.** -/
structure OccursFullShape {Θ : Context S.R} (equation : Equation (TotalTerm Θ)) where
  u : Head
  universal : S.R.isUniverse u
  annotation : equation.1.1.code = .head u
  same : equation.2.1.code = .head u
  occurs : Within true equation.1.2.code equation.2.2.code

variable [∀ head, Decidable (S.R.isUniverse head)]

/-- Read a proper occurrence from the codes; no budget. -/
def occursFullShape {Θ : Context S.R} (equation : Equation (TotalTerm Θ)) : Option (OccursFullShape equation) :=
  match annotation : equation.1.1.code with
  | .head u =>
      if same : equation.2.1.code = .head u then
        if universal : S.R.isUniverse u then
          if found : occurs equation.1.2.code equation.2.2.code = true then
            some ⟨u, universal, annotation, same, occurs_sound _ _ found⟩
          else none
        else none
      else none
  | _ => none

variable (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R) (heads : HeadPreserving S.R)
  (algebra : CumulativeAlgebra S.R) (rigid : ∀ name, S.roles name = .rigid)
  (complete : AlgorithmicComplete S.R S.roles)

omit [DecidableEq Head] [∀ head, Decidable (S.R.isUniverse head)] in
include facts roots heads algebra rigid complete in
/-- **A proper occurrence has no solution at any later context.** -/
theorem OccursFullShape.refutes {Θ : Context S.R} {equation : Equation (TotalTerm Θ)}
    (shape : OccursFullShape equation) {Δ : Context S.R} (σ : Δ ⟶ Θ) :
    ¬ (frames S.levels).Solves σ equation := by
  intro solved
  rw [solves_raw, shape.annotation] at solved
  have tLeft := equation.1.2.typed.substitute σ.typed
  have tRight := equation.2.2.typed.substitute σ.typed
  rw [shape.annotation] at tLeft
  rw [shape.same] at tRight
  exact occurrence_not_typeEq facts roots heads algebra rigid complete Δ.formed (shape.occurs.subst _)
    ⟨shape.u, shape.universal, tLeft⟩ ⟨shape.u, shape.universal, tRight⟩ ⟨shape.u, shape.universal, solved.2⟩

/-- **The full occurs rule**: refute the store at the first equation with a proper occurrence, read
in either orientation. -/
def occursFullSearch {Θ : Context S.R} : (problem : EquationStore (TotalTerm Θ)) → Option (Found problem)
  | [] => none
  | equation :: rest =>
      match occursFullShape equation with
      | some shape => some (.refuted fun ⟨_, σ, solved⟩ =>
          shape.refutes facts roots heads algebra rigid complete σ (solved equation List.mem_cons_self))
      | none =>
          match occursFullShape (swap equation) with
          | some shape => some (.refuted fun ⟨_, σ, solved⟩ =>
              shape.refutes facts roots heads algebra rigid complete σ
                ((solves_swap σ equation).mpr (solved equation List.mem_cons_self)))
          | none => (occursFullSearch rest).map (Found.keepLeft equation)

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

/-- **One full occurs round**: the recognition round, and when it is stuck, the full occurs rule on
the prepared store. -/
def occursFullRound (fuel : Nat) {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) :
    Round S.levels size problem :=
  extendRound root rootComplete facts roots heads
    (fun fuel => recognitionRound facts roots heads algebra declared choices reducer rigid complete root normalizes
      certifyNormal headTypingUnique rootComplete fuel)
    (fun _ => occursFullSearch facts roots heads algebra rigid complete) fuel problem

/-- **The full occurs family.** -/
def occursFullFamily : ContextualDependentDecisiveDriver.Family S.levels where
  rank := size
  round fuel := occursFullRound facts roots heads algebra rigid complete declared choices reducer root normalizes
    certifyNormal headTypingUnique rootComplete fuel

variable (stable : ∀ {n : Nat} (fuel : Nat) (term : Tm Head n),
  Keeps (reducer fuel term) (reducer (fuel + 1) term))
include stable

/-- **The full occurs round is eventually constant on every store.** -/
theorem occursFullRound_const {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) :
    EventuallyConst fun fuel => occursFullRound facts roots heads algebra rigid complete declared choices reducer root
      normalizes certifyNormal headTypingUnique rootComplete fuel problem :=
  extendRound_const root rootComplete facts roots heads _ _
    (fun problem => recognitionRound_const facts roots heads algebra declared choices reducer rigid complete root
      normalizes certifyNormal headTypingUnique rootComplete stable problem)
    (fun _ => EventuallyConst.const _) problem

/-- **The full occurs family settles** on every class of stores on which, at each nonempty store and
from some budget on, its round is not stuck and keeps every residual store in the class. -/
def occursFullSettledOfConst (holds : {Γ : Context S.R} → EquationStore (TotalTerm Γ) → Prop)
    (eventual : ∀ {Γ : Context S.R} {problem : EquationStore (TotalTerm Γ)}, holds problem → problem ≠ [] →
      ∃ bound, ∀ larger, bound ≤ larger →
        occursFullRound facts roots heads algebra rigid complete declared choices reducer root normalizes
            certifyNormal headTypingUnique rootComplete larger problem ≠ .stuck ∧
        ∀ {update : Update S.levels problem} {smaller : Below (size update.remaining) (size problem)},
          occursFullRound facts roots heads algebra rigid complete declared choices reducer root normalizes
              certifyNormal headTypingUnique rootComplete larger problem = .progress update smaller →
            holds update.remaining) :
    ContextualDependentDecisiveDriver.Settled
      (occursFullFamily facts roots heads algebra rigid complete declared choices reducer root normalizes
        certifyNormal headTypingUnique rootComplete) :=
  Settled.ofConst _ (fun problem => occursFullRound_const facts roots heads algebra rigid complete declared choices
    reducer root normalizes certifyNormal headTypingUnique rootComplete stable problem) holds eventual

end ContextualDependentOccursFull
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
