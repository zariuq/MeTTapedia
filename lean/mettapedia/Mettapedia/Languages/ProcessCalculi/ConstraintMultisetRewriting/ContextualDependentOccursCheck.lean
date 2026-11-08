import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentEtaExpansion
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentEtaLongExistence

/-!
# The occurs check at Π and Σ types, through η-long normal forms

A type metavariable `X` that occurs **rigidly** in the domain of a Π or Σ type, or along a chain of
such domains, can never equal that type: `X ≐ Π X B` and `X ≐ Σ (Π X B) C` have no solution in any
later context.

The argument reads the η-long β-normal forms of R88. Let `N` be the normal form of the value of `X`.
Along the chain of domains, the type has a normal form `W` built from `N`: each former keeps its
normal domain and takes the normal form of its family under that domain (`normal_along`). So `W`
has strictly more nodes than `N`. If `X` were equal to the type, `N` and `W` would be two equal
normal types, hence the same term up to heads (`long_type_unique`), with the same number of nodes:
a contradiction (`domain_occurrence_not_typeEq`). Since the argument is about normal forms, it is
insensitive to η-conversion of the sides.

A **flexible** occurrence, under a metavariable application such as `X ≐ Π (G X) A`, is not a
domain occurrence and is not refused.

The **occurs rule** refutes a store with an equation `X ≐ T` (or `T ≐ X`) at a universe where `X`
occurs rigidly along the domains of `T`, with a certificate. The **occurs round** extends the η
round by it.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentOccursCheck

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentUpdate ContextualDependentWorklist
open ContextualDependentPatternSolver ContextualDependentDecisiveFragment ContextualDependentFragment
open ContextualDependentInPlace ContextualDependentRigidFormers ContextualDependentEtaExpansion
open ContextualDependentConversionBudget ContextualDependentEtaLong

variable {Head L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L}

/-! ## Nodes -/

/-- The number of formers of a code, heads counted as one node. -/
def nodes : {n : Nat} → Tm Head n → Nat
  | _, .var _ => 1
  | _, .const _ => 1
  | _, .head _ => 1
  | _, .pi A B => nodes A + nodes B + 1
  | _, .sigma A B => nodes A + nodes B + 1
  | _, .id A x y => nodes A + nodes x + nodes y + 1
  | _, .lam b => nodes b + 1
  | _, .app f a => nodes f + nodes a + 1
  | _, .pair a b => nodes a + nodes b + 1
  | _, .fst p => nodes p + 1
  | _, .snd p => nodes p + 1
  | _, .refl z => nodes z + 1

/-- Terms that are the same up to heads have the same number of nodes. -/
theorem nodes_of_same {R : Rules Head} {n : Nat} {s t : Tm Head n} (same : SameUpToHeads R s t) :
    nodes s = nodes t := by
  induction same with
  | var => rfl
  | const => rfl
  | head => rfl
  | pi _ _ ih₁ ih₂ => simp only [nodes, ih₁, ih₂]
  | sigma _ _ ih₁ ih₂ => simp only [nodes, ih₁, ih₂]
  | id _ _ _ ih₁ ih₂ ih₃ => simp only [nodes, ih₁, ih₂, ih₃]
  | lam _ ih => simp only [nodes, ih]
  | app _ _ ih₁ ih₂ => simp only [nodes, ih₁, ih₂]
  | pair _ _ ih₁ ih₂ => simp only [nodes, ih₁, ih₂]
  | fst _ ih => simp only [nodes, ih]
  | snd _ ih => simp only [nodes, ih]
  | refl _ ih => simp only [nodes, ih]

/-! ## Rigid occurrences along domains -/

/-- **A rigid occurrence along domains**: the code is a Π or Σ type whose domain is the value, or one
along its domain. -/
inductive DomainOccurrence {n : Nat} (value : Tm Head n) : Tm Head n → Prop
  | here (isPi : Bool) {B : Tm Head (n + 1)} : DomainOccurrence value (binder isPi value B)
  | deeper (isPi : Bool) {A : Tm Head n} {B : Tm Head (n + 1)} :
      DomainOccurrence value A → DomainOccurrence value (binder isPi A B)

theorem DomainOccurrence.subst {n m : Nat} {value T : Tm Head n} (σ : Sub Head n m)
    (occurrence : DomainOccurrence value T) :
    DomainOccurrence (Presentation.subst σ value) (Presentation.subst σ T) := by
  induction occurrence with
  | here isPi =>
      rw [subst_binder]
      exact .here isPi
  | deeper isPi _ ih =>
      rw [subst_binder]
      exact .deeper isPi ih

variable [DecidableEq Head]

/-- **The decision of a domain occurrence**, by the codes. -/
def domainOccurs {n : Nat} (value : Tm Head n) : Tm Head n → Bool
  | .pi A _ => decide (A = value) || domainOccurs value A
  | .sigma A _ => decide (A = value) || domainOccurs value A
  | _ => false

theorem domainOccurs_sound {n : Nat} (value : Tm Head n) :
    ∀ {T : Tm Head n}, domainOccurs value T = true → DomainOccurrence value T
  | .pi A B, found => by
      simp only [domainOccurs, Bool.or_eq_true, decide_eq_true_eq] at found
      rcases found with same | inner
      · subst same
        exact .here true
      · exact .deeper true (domainOccurs_sound value inner)
  | .sigma A B, found => by
      simp only [domainOccurs, Bool.or_eq_true, decide_eq_true_eq] at found
      rcases found with same | inner
      · subst same
        exact .here false
      · exact .deeper false (domainOccurs_sound value inner)
  | .var _, found => by simp [domainOccurs] at found
  | .const _, found => by simp [domainOccurs] at found
  | .head _, found => by simp [domainOccurs] at found
  | .id _ _ _, found => by simp [domainOccurs] at found
  | .lam _, found => by simp [domainOccurs] at found
  | .app _ _, found => by simp [domainOccurs] at found
  | .pair _ _, found => by simp [domainOccurs] at found
  | .fst _, found => by simp [domainOccurs] at found
  | .snd _, found => by simp [domainOccurs] at found
  | .refl _, found => by simp [domainOccurs] at found

/-! ## Normal forms along domains -/

section Normal

variable (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R) (heads : HeadPreserving S.R)
  (algebra : CumulativeAlgebra S.R) (rigid : ∀ name, S.roles name = .rigid) (complete : AlgorithmicComplete S.R S.roles)

omit [DecidableEq Head] in
theorem binder_formed (isPi : Bool) {n : Nat} {Γ : Ctx Head n} {A : Tm Head n} {B : Tm Head (n + 1)} {u v w : Head}
    (tA : Typed S.R Γ A (.head u)) (hu : S.R.isUniverse u) (tB : Typed S.R (.snoc Γ A) B (.head v))
    (hv : S.R.isUniverse v) (joined : S.R.join u v w) : Typed S.R Γ (binder isPi A B) (.head w) := by
  cases isPi
  · exact .sigmaForm tA hu tB hv joined
  · exact .piForm tA hu tB hv joined

omit [DecidableEq Head] in
theorem binder_long (isPi : Bool) {n : Nat} {Γ : Ctx Head n} {A : Tm Head n} {B : Tm Head (n + 1)}
    (lA : Long S.R S.roles (.type Γ A)) (lB : Long S.R S.roles (.type (.snoc Γ A) B))
    (isType : IsType S.R Γ (binder isPi A B)) : Long S.R S.roles (.type Γ (binder isPi A B)) := by
  cases isPi
  · exact .sigma lA lB isType
  · exact .pi lA lB isType

omit [DecidableEq Head] in
theorem binder_parts_typed (isPi : Bool) {n : Nat} {Γ : Ctx Head n} {A : Tm Head n} {B : Tm Head (n + 1)}
    (isType : IsType S.R Γ (binder isPi A B)) :
    IsType S.R Γ A ∧ ∃ v, S.R.isUniverse v ∧ Typed S.R (.snoc Γ A) B (.head v) := by
  obtain ⟨_, _, typed⟩ := isType
  cases isPi
  · obtain ⟨u₁, v, _, tA, hu₁, tB, hv, _, _⟩ := (typed : Typed S.R Γ (.sigma A B) _).generation
    exact ⟨⟨u₁, hu₁, tA⟩, v, hv, tB⟩
  · obtain ⟨u₁, v, _, tA, hu₁, tB, hv, _, _⟩ := (typed : Typed S.R Γ (.pi A B) _).generation
    exact ⟨⟨u₁, hu₁, tA⟩, v, hv, tB⟩

omit [DecidableEq Head] in
include facts roots heads algebra rigid complete in
/-- **One former over a normal domain**: a binder type whose domain is equal to a normal type `D`
has a normal form with `D` as its domain, so strictly more nodes than `D`. -/
theorem normal_binder (isPi : Bool) {n : Nat} {Γ : Ctx Head n} (formed : CtxFormed S.R Γ) {A D : Tm Head n}
    {B : Tm Head (n + 1)} (lD : Long S.R S.roles (.type Γ D)) (AD : TypeEq S.R Γ A D)
    (isType : IsType S.R Γ (binder isPi A B)) :
    ∃ W, Long S.R S.roles (.type Γ W) ∧ TypeEq S.R Γ (binder isPi A B) W ∧ nodes D < nodes W := by
  obtain ⟨_, v, hv, tB⟩ := binder_parts_typed isPi isType
  have tB' := Typed.stable tB (CtxEq.snoc (CtxEq.refl Γ formed) AD.symm)
  have formedD : CtxFormed S.R (.snoc Γ D) := .snoc formed lD.isType
  obtain ⟨M, lM, atM⟩ := long_type_exists facts roots heads algebra rigid complete formedD ⟨v, hv, tB'⟩
  obtain ⟨tM, BM⟩ := atM hv tB'
  obtain ⟨u, hu, tD⟩ := lD.isType
  obtain ⟨w, joined⟩ := S.levels.join_exists hu hv
  have isW : IsType S.R Γ (binder isPi D M) :=
    ⟨w, (S.levels.join_level joined).1, binder_formed isPi tD hu tM hv joined⟩
  refine ⟨binder isPi D M, binder_long isPi lD lM isW, ?_, ?_⟩
  · exact (typeEq_binder_iff facts isPi formed).mpr
      ⟨AD, ⟨v, hv, Equal.stable BM (CtxEq.snoc (CtxEq.refl Γ formed) AD)⟩⟩
  · cases isPi <;> simp only [binder, nodes] <;> omega

omit [DecidableEq Head] in
include facts roots heads algebra rigid complete in
/-- **Normal forms along domains**: a type in which `V` occurs along the domains, with `V` equal to a
normal type `N`, has a normal form with strictly more nodes than `N`. -/
theorem normal_along {n : Nat} {Γ : Ctx Head n} (formed : CtxFormed S.R Γ) {V N : Tm Head n}
    (lN : Long S.R S.roles (.type Γ N)) (VN : TypeEq S.R Γ V N) :
    ∀ {T : Tm Head n}, DomainOccurrence V T → IsType S.R Γ T →
      ∃ W, Long S.R S.roles (.type Γ W) ∧ TypeEq S.R Γ T W ∧ nodes N < nodes W := by
  intro T occurrence
  induction occurrence with
  | here isPi =>
      intro isType
      exact normal_binder facts roots heads algebra rigid complete isPi formed lN VN isType
  | deeper isPi _ ih =>
      intro isType
      obtain ⟨isA, _⟩ := binder_parts_typed isPi isType
      obtain ⟨WA, lWA, AWA, smaller⟩ := ih isA
      obtain ⟨W, lW, TW, larger⟩ := normal_binder facts roots heads algebra rigid complete isPi formed lWA AWA isType
      exact ⟨W, lW, TW, by omega⟩

omit [DecidableEq Head] in
include facts roots heads algebra rigid complete in
/-- **The occurs check along domains**: a type is never equal to a type in which it occurs rigidly
along the domains. -/
theorem domain_occurrence_not_typeEq {n : Nat} {Γ : Ctx Head n} (formed : CtxFormed S.R Γ) {V T : Tm Head n}
    (occurrence : DomainOccurrence V T) (isV : IsType S.R Γ V) (isT : IsType S.R Γ T) : ¬ TypeEq S.R Γ V T := by
  intro same
  obtain ⟨N, lN, atN⟩ := long_type_exists facts roots heads algebra rigid complete formed isV
  obtain ⟨u, hu, tV⟩ := isV
  have VN : TypeEq S.R Γ V N := ⟨u, hu, (atN hu tV).2⟩
  obtain ⟨W, lW, TW, larger⟩ := normal_along facts roots heads algebra rigid complete formed lN VN occurrence isT
  have NW : TypeEq S.R Γ N W := TypeEq.trans S.levels VN.symm (TypeEq.trans S.levels same TW)
  have equalNodes := nodes_of_same (long_type_unique facts roots heads algebra complete formed lN lW NW)
  omega

end Normal

/-! ## The occurs rule -/

/-- **An equation `X ≐ T` at a universe with `X` occurring rigidly along the domains of `T`.** -/
structure OccursShape {Θ : Context S.R} (equation : Equation (TotalTerm Θ)) where
  u : Head
  universal : S.R.isUniverse u
  annotation : equation.1.1.code = .head u
  same : equation.2.1.code = .head u
  occurs : DomainOccurrence equation.1.2.code equation.2.2.code

variable [∀ head, Decidable (S.R.isUniverse head)]

/-- Read an occurs-check failure from the codes; no budget. -/
def occursShape {Θ : Context S.R} (equation : Equation (TotalTerm Θ)) : Option (OccursShape equation) :=
  match annotation : equation.1.1.code with
  | .head u =>
      if same : equation.2.1.code = .head u then
        if universal : S.R.isUniverse u then
          if found : (∃ x, equation.1.2.code = .var x) ∧ domainOccurs equation.1.2.code equation.2.2.code = true then
            some ⟨u, universal, annotation, same, domainOccurs_sound _ found.2⟩
          else none
        else none
      else none
  | _ => none

variable (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R) (heads : HeadPreserving S.R)
  (algebra : CumulativeAlgebra S.R) (rigid : ∀ name, S.roles name = .rigid) (complete : AlgorithmicComplete S.R S.roles)

omit [DecidableEq Head] [∀ head, Decidable (S.R.isUniverse head)] in
include facts roots heads algebra rigid complete in
/-- **An occurs-check failure has no solution at any later context.** -/
theorem OccursShape.refutes {Θ : Context S.R} {equation : Equation (TotalTerm Θ)} (shape : OccursShape equation)
    {Δ : Context S.R} (σ : Δ ⟶ Θ) : ¬ (frames S.levels).Solves σ equation := by
  intro solved
  rw [solves_raw, shape.annotation] at solved
  have tLeft := equation.1.2.typed.substitute σ.typed
  have tRight := equation.2.2.typed.substitute σ.typed
  rw [shape.annotation] at tLeft
  rw [shape.same] at tRight
  exact domain_occurrence_not_typeEq facts roots heads algebra rigid complete Δ.formed (shape.occurs.subst _)
    ⟨shape.u, shape.universal, tLeft⟩ ⟨shape.u, shape.universal, tRight⟩ ⟨shape.u, shape.universal, solved.2⟩

/-- **The occurs rule**: refute the store at the first equation with a rigid occurrence along domains,
read in either orientation. -/
def occursSearch {Θ : Context S.R} : (problem : EquationStore (TotalTerm Θ)) → Option (Found problem)
  | [] => none
  | equation :: rest =>
      match occursShape equation with
      | some shape => some (.refuted fun ⟨_, σ, solved⟩ =>
          shape.refutes facts roots heads algebra rigid complete σ (solved equation List.mem_cons_self))
      | none =>
          match occursShape (swap equation) with
          | some shape => some (.refuted fun ⟨_, σ, solved⟩ =>
              shape.refutes facts roots heads algebra rigid complete σ
                ((solves_swap σ equation).mpr (solved equation List.mem_cons_self)))
          | none => (occursSearch rest).map (Found.keepLeft equation)

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

/-- **One occurs round**: the η round, and when it is stuck, the occurs rule on the prepared store. -/
def occursRound (fuel : Nat) {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) : Round S.levels size problem :=
  extendRound root rootComplete facts roots heads
    (fun fuel => etaRound facts roots heads algebra declared choices reducer rigid complete root normalizes
      certifyNormal headTypingUnique rootComplete fuel)
    (fun _ => occursSearch facts roots heads algebra rigid complete) fuel problem

/-- **The occurs family.** -/
def occursFamily : ContextualDependentDecisiveDriver.Family S.levels where
  rank := size
  round fuel := occursRound facts roots heads algebra rigid complete declared choices reducer root normalizes
    certifyNormal headTypingUnique rootComplete fuel

variable (stable : ∀ {n : Nat} (fuel : Nat) (term : Tm Head n),
  Keeps (reducer fuel term) (reducer (fuel + 1) term))
include stable

/-- **The occurs round is eventually constant on every store.** -/
theorem occursRound_const {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) :
    EventuallyConst fun fuel => occursRound facts roots heads algebra rigid complete declared choices reducer root
      normalizes certifyNormal headTypingUnique rootComplete fuel problem :=
  extendRound_const root rootComplete facts roots heads _ _
    (fun problem => etaRound_const facts roots heads algebra declared choices reducer rigid complete root normalizes
      certifyNormal headTypingUnique rootComplete stable problem)
    (fun _ => EventuallyConst.const _) problem

/-- **The occurs family settles** on every class of stores on which, at each nonempty store and from
some budget on, its round is not stuck and keeps every residual store in the class. -/
def occursSettledOfConst (holds : {Γ : Context S.R} → EquationStore (TotalTerm Γ) → Prop)
    (eventual : ∀ {Γ : Context S.R} {problem : EquationStore (TotalTerm Γ)}, holds problem → problem ≠ [] →
      ∃ bound, ∀ larger, bound ≤ larger →
        occursRound facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
            headTypingUnique rootComplete larger problem ≠ .stuck ∧
        ∀ {update : Update S.levels problem} {smaller : Below (size update.remaining) (size problem)},
          occursRound facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
              headTypingUnique rootComplete larger problem = .progress update smaller → holds update.remaining) :
    ContextualDependentDecisiveDriver.Settled
      (occursFamily facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
        headTypingUnique rootComplete) :=
  Settled.ofConst _ (fun problem => occursRound_const facts roots heads algebra rigid complete declared choices reducer
    root normalizes certifyNormal headTypingUnique rootComplete stable problem) holds eventual

end ContextualDependentOccursCheck
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
