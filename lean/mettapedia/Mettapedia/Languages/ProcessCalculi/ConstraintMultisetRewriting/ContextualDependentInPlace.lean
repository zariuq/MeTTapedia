import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentFragmentFiringPi

/-!
# Solving a metavariable in place, with the later declarations instantiated

The pattern, prune and exchange rules solve the newest metavariable, or the one below it when the
newest does not depend on it. A metavariable on which a later declaration depends stays out of
their reach. **Solving in place** reaches it: in `Γ, X : A, Y₁ : B₁, …, Yₖ : Bₖ`, the equations
that mention none of `Y₁ … Yₖ` are strengthened to `Γ, X : A`, a rule solves `X` there, and the
answer is carried past every later declaration, whose type is instantiated by it
(`ContextualDependentUpdate.Update.lift`). The equations that mention a later declaration are
instantiated by the carried answer, never dropped.

* **Strengthening** reads a judged term without the newest variable, forms its type and checks it
  in the older context (`strengthen`); its codes are the original ones, renamed.
* **Separation** splits a store into the strengthened equations and the others; the store has
  exactly the solutions of the others together with the weakened strengthened ones
  (`separate_models`).
* **Carrying** turns a rule outcome on the strengthened store into one on the original store
  (`carry`): an answer is lifted past the newest declaration, a refutation restricts every
  solution to the older context. Nothing is chosen and nothing is lost.

The **in-place rule** tries every depth from `1` below the newest declaration, and at each runs the
first of the pattern, prune and exchange rules on the strengthened store. The **in-place round**
runs the Π round of the fragment solver, and when that is stuck, prepares the store and runs the
in-place rule. Every progress removes a declaration, every refutation is certified.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentInPlace

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentUpdate ContextualDependentWorklist
open ContextualDependentPatternSolver ContextualDependentDecisiveFragment ContextualDependentFragment

variable {Head L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L}

/-! ## Equations with the same codes -/

/-- Two equations with the same four codes have the same solutions: the frame reads codes only. -/
theorem solves_of_codes {Θ Δ : Context S.R} (σ : Δ ⟶ Θ) {first second : Equation (TotalTerm Θ)}
    (leftType : first.1.1.code = second.1.1.code) (leftTerm : first.1.2.code = second.1.2.code)
    (rightType : first.2.1.code = second.2.1.code) (rightTerm : first.2.2.code = second.2.2.code) :
    (frames S.levels).Solves σ first ↔ (frames S.levels).Solves σ second := by
  show TypeEq S.R Δ.raw (subst σ.substitution first.1.1.code) (subst σ.substitution first.2.1.code) ∧
      Equal S.R Δ.raw (subst σ.substitution first.1.2.code) (subst σ.substitution first.2.2.code)
        (subst σ.substitution first.1.1.code) ↔
    TypeEq S.R Δ.raw (subst σ.substitution second.1.1.code) (subst σ.substitution second.2.1.code) ∧
      Equal S.R Δ.raw (subst σ.substitution second.1.2.code) (subst σ.substitution second.2.2.code)
        (subst σ.substitution second.1.1.code)
  rw [leftType, leftTerm, rightType, rightTerm]

theorem models_cons {Θ Δ : Context S.R} (σ : Δ ⟶ Θ) (equation : Equation (TotalTerm Θ))
    (rest : EquationStore (TotalTerm Θ)) :
    (frames S.levels).Models σ (equation :: rest) ↔
      (frames S.levels).Solves σ equation ∧ (frames S.levels).Models σ rest := by
  simp only [Frames.Models, List.mem_cons, forall_eq_or_imp]

theorem applyStore_cons {Θ Δ : Context S.R} (σ : Δ ⟶ Θ) (equation : Equation (TotalTerm Θ))
    (rest : EquationStore (TotalTerm Θ)) :
    (frames S.levels).applyStore σ (equation :: rest) =
      (equation.1.reindex σ, equation.2.reindex σ) :: (frames S.levels).applyStore σ rest := rfl

/-! ## Strengthening past the newest declaration -/

section Strengthening

variable [DecidableEq Head] [DecidableRel S.R.headEq]
  [∀ head, Decidable (S.R.isUniverse head)] [DecidableRel S.R.cumulative]
variable (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R)
  (heads : HeadPreserving S.R) (algebra : CumulativeAlgebra S.R) (declared : DeclaredTypesFormed S.R)
  (choices : ExecutableChecking.HeadChoices S.R) (reducer : ExecutableReduction.Reducer S.R)

omit [DecidableRel S.R.headEq] [∀ head, Decidable (S.R.isUniverse head)] [DecidableRel S.R.cumulative] in
/-- **A code read without the newest variable**, inverting the weakening; it needs no budget. -/
def strengthenCode {n : Nat} (code : Tm Head (n + 1)) : Option {strong : Tm Head n // rename wk strong = code} :=
  match found : ContextualDependentInversion.invert (ContextualDependentInversion.lookup (wk : Ren n (n + 1))) code with
  | none => none
  | some strong => some ⟨strong, ContextualDependentInversion.invert_sound code wk _
      (ContextualDependentInversion.lookup_exact wk (Fin.succ_injective _)) strong found⟩

/-- **A judged term read without the newest variable**: its type code and its code are inverted
along the weakening, the type is formed and the term checked in the older context. -/
def strengthen (fuel : Nat) {Γ : Context S.R} (type : TypeOver Γ) (term : TotalTerm (extend Γ type)) :
    Option {strong : TotalTerm Γ // rename wk strong.1.code = term.1.code ∧ rename wk strong.2.code = term.2.code} :=
  (strengthenCode (n := Γ.arity) term.1.code).bind fun code =>
    (ContextualDependentPruning.formType facts roots heads algebra declared choices reducer fuel Γ code.val).bind
      fun formed =>
        (ContextualDependentTypedInversion.recover facts roots heads algebra declared choices reducer fuel
            (ContextualDependentFlex.withoutNewest Γ type) formed.val term.2.code).map fun recovered =>
          ⟨⟨formed.val, recovered.body⟩, by
            refine ⟨?_, recovered.recovers⟩
            change rename wk formed.val.code = term.1.code
            rw [formed.property]
            exact code.property⟩

omit [DecidableEq Head] [DecidableRel S.R.headEq] [∀ head, Decidable (S.R.isUniverse head)]
  [DecidableRel S.R.cumulative] in
/-- A strengthened judged term, weakened back, has the original codes. -/
theorem weakened_codes {Γ : Context S.R} (type : TypeOver Γ) {term : TotalTerm (extend Γ type)}
    (strong : {strong : TotalTerm Γ // rename wk strong.1.code = term.1.code ∧ rename wk strong.2.code = term.2.code}) :
    (strong.val.reindex (projectionHom Γ type)).1.code = term.1.code ∧
      (strong.val.reindex (projectionHom Γ type)).2.code = term.2.code := by
  refine ⟨?_, ?_⟩
  · change subst projection strong.val.1.code = term.1.code
    rw [subst_projection]
    exact strong.property.1
  · change subst projection strong.val.2.code = term.2.code
    rw [subst_projection]
    exact strong.property.2

/-- **Separate a store**: the equations whose both sides strengthen, strengthened, and the others. -/
def separate (fuel : Nat) {Γ : Context S.R} (type : TypeOver Γ) :
    EquationStore (TotalTerm (extend Γ type)) → EquationStore (TotalTerm Γ) × EquationStore (TotalTerm (extend Γ type))
  | [] => ([], [])
  | equation :: rest =>
      match strengthen facts roots heads algebra declared choices reducer fuel type equation.1,
          strengthen facts roots heads algebra declared choices reducer fuel type equation.2 with
      | some left, some right =>
          ((left.val, right.val) :: (separate fuel type rest).1, (separate fuel type rest).2)
      | _, _ => ((separate fuel type rest).1, equation :: (separate fuel type rest).2)

/-- **Separation keeps exactly the solutions**: a store over `Γ, A` has the solutions of the
equations that were not strengthened together with the strengthened ones weakened back. -/
theorem separate_models (fuel : Nat) {Γ : Context S.R} (type : TypeOver Γ) {Δ : Context S.R}
    (σ : Δ ⟶ extend Γ type) :
    ∀ problem : EquationStore (TotalTerm (extend Γ type)),
      (frames S.levels).Models σ problem ↔
        (frames S.levels).Models σ ((separate facts roots heads algebra declared choices reducer fuel type problem).2 ++
          (frames S.levels).applyStore (projectionHom Γ type)
            (separate facts roots heads algebra declared choices reducer fuel type problem).1)
  | [] => by simp [separate, Frames.applyStore]
  | equation :: rest => by
      have ih := separate_models fuel type σ rest
      simp only [separate]
      split
      · rename_i left right _ _
        rw [models_cons, ih, Frames.models_append, Frames.models_append, applyStore_cons, models_cons]
        have same : (frames S.levels).Solves σ equation ↔
            (frames S.levels).Solves σ ((left.val.reindex (projectionHom Γ type)),
              (right.val.reindex (projectionHom Γ type))) :=
          solves_of_codes σ (weakened_codes type left).1.symm (weakened_codes type left).2.symm
            (weakened_codes type right).1.symm (weakened_codes type right).2.symm
        rw [same]
        tauto
      · rw [models_cons, ih, List.cons_append, models_cons]

/-- The separated store is equivalent to the original one. -/
theorem separate_equivalent (fuel : Nat) {Γ : Context S.R} (type : TypeOver Γ)
    (problem : EquationStore (TotalTerm (extend Γ type))) :
    (frames S.levels).Equivalent problem
      ((separate facts roots heads algebra declared choices reducer fuel type problem).2 ++
        (frames S.levels).applyStore (projectionHom Γ type)
          (separate facts roots heads algebra declared choices reducer fuel type problem).1) :=
  fun _ σ => separate_models facts roots heads algebra declared choices reducer fuel type σ problem


/-- **Separation with its equivalence**, as one value. -/
def separation (fuel : Nat) {Γ : Context S.R} (type : TypeOver Γ) (problem : EquationStore (TotalTerm (extend Γ type))) :
    {pair : EquationStore (TotalTerm Γ) × EquationStore (TotalTerm (extend Γ type)) //
      (frames S.levels).Equivalent problem (pair.2 ++ (frames S.levels).applyStore (projectionHom Γ type) pair.1)} :=
  ⟨separate facts roots heads algebra declared choices reducer fuel type problem,
    separate_equivalent facts roots heads algebra declared choices reducer fuel type problem⟩
end Strengthening

/-! ## Carrying an outcome past the newest declaration -/

/-- **Carry a rule outcome on a strengthened store past the newest declaration.** An answer is
lifted, instantiating the newest declaration's type, and the unstrengthened equations are
instantiated by it; a refutation of the strengthened store refutes the original one, since every
solution restricts to the older context. -/
def carry {Γ : Context S.R} (type : TypeOver Γ) {strong : EquationStore (TotalTerm Γ)}
    {problem weak : EquationStore (TotalTerm (extend Γ type))}
    (same : (frames S.levels).Equivalent problem (weak ++ (frames S.levels).applyStore (projectionHom Γ type) strong)) :
    Found strong → Found problem
  | .solved update smaller =>
      .solved (((update.lift type).keepLeft weak).rephrase same) (by
        change update.target.arity + 1 < Γ.arity + 1
        omega)
  | .refuted absent =>
      .refuted fun ⟨Δ, σ, solved⟩ =>
        absent ⟨Δ, σ ≫ projectionHom Γ type,
          (Frames.models_applyStore (X := frames S.levels) (projectionHom Γ type) σ strong).mp
            ((Frames.models_append (X := frames S.levels) σ weak _).mp ((same Δ σ).mp solved)).2⟩

/-- **The carried answer instantiates the later declaration**: the target context ends with the
newest declaration's type, substituted by the answer on the strengthened store. -/
theorem carry_target {Γ : Context S.R} (type : TypeOver Γ) {strong : EquationStore (TotalTerm Γ)}
    {problem weak : EquationStore (TotalTerm (extend Γ type))}
    (same : (frames S.levels).Equivalent problem (weak ++ (frames S.levels).applyStore (projectionHom Γ type) strong))
    (update : Update S.levels strong) :
    (((update.lift type).keepLeft weak).rephrase same).target = extend update.target (type.reindex update.answer) ∧
      (((update.lift type).keepLeft weak).rephrase same).target.raw =
        .snoc update.target.raw (subst update.answer.substitution type.code) ∧
      (((update.lift type).keepLeft weak).rephrase same).remaining =
        (frames S.levels).applyStore (update.lift type).answer weak ++
          ((frames S.levels).applyStore (projectionHom update.target (type.reindex update.answer)) update.remaining :
            EquationStore (TotalTerm (update.lift type).target)) :=
  ⟨rfl, rfl, rfl⟩

/-- **An update keeps exactly the solutions**: a later solution of the original store is one of the
residual store composed with the answer, up to typed equality, and conversely. -/
theorem Update.exact {Γ : Context S.R} {problem : EquationStore (TotalTerm Γ)} (update : Update S.levels problem)
    {Δ : Context S.R} (σ : Δ ⟶ Γ) :
    (frames S.levels).Models σ problem ↔
      ∃ residual : Δ ⟶ update.target, (frames S.levels).Models residual update.remaining ∧
        ∀ term : TotalTerm Γ, (frames S.levels).E (term.reindex σ) (term.reindex (residual ≫ update.answer)) := by
  constructor
  · exact update.complete Δ σ
  · rintro ⟨residual, solved, factor⟩
    exact (Elimination.models_pointwise S.levels factor problem).mpr (update.sound Δ residual solved)

/-! ## The in-place rule and round -/

variable [DecidableEq Head] [DecidableRel S.R.headEq]
  [∀ head, Decidable (S.R.isUniverse head)] [DecidableRel S.R.cumulative]
variable (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R)
  (heads : HeadPreserving S.R) (algebra : CumulativeAlgebra S.R) (declared : DeclaredTypesFormed S.R)
  (choices : ExecutableChecking.HeadChoices S.R) (reducer : ExecutableReduction.Reducer S.R)
  (rigid : ∀ name, S.roles name = .rigid) (complete : AlgorithmicComplete S.R S.roles)
  (root : ExecutableReduction.RootEvaluator S.R)
  (normalizes : ∀ {Θ : Context S.R} {type : TypeOver Θ} (term : Term Θ type),
    ∃ code : Tm Head Θ.arity, ContextualDependentNormalChecking.Normal (S := S) code ∧
      Equal S.R Θ.raw term.code code type.code)
  (certifyNormal : ∀ {n : Nat} (term : Tm Head n),
    Option (PLift (ContextualDependentNormalChecking.Normal (S := S) term)))
  (headTypingUnique : ∀ {head first second : Head},
    S.R.headTyping head first → S.R.headTyping head second → first = second)
  (rootComplete : ∀ {n : Nat} (term : Tm Head n), root term = none → ∀ target, ¬ S.R.computation.step term target)

/-- **Solving at one depth below the newest declaration.** At depth `0` the first of the pattern,
prune and exchange rules runs on the store; at depth `d + 1` the store is separated at the newest
declaration, solved at depth `d` on the strengthened equations, and the outcome is carried back. -/
def inPlaceAt (fuel : Nat) : (depth : Nat) → {Θ : Context S.R} → (problem : EquationStore (TotalTerm Θ)) →
    Option (Found problem)
  | 0, _, problem => firstRule rigid facts complete roots heads algebra declared choices reducer root normalizes
      certifyNormal headTypingUnique fuel problem
  | depth + 1, Θ, problem =>
      match newestOf facts roots heads algebra declared choices reducer fuel Θ with
      | none => none
      | some view => ContextualDependentPatternSolver.throughNewest view problem fun stored =>
          (inPlaceAt fuel depth (separation facts roots heads algebra declared choices reducer fuel view.type
              stored).val.1).map
            (carry view.type (separation facts roots heads algebra declared choices reducer fuel view.type stored).property)

/-- Try the depths in turn. -/
def inPlaceSearch (fuel : Nat) {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) : List Nat → Option (Found problem)
  | [] => none
  | depth :: rest =>
      match inPlaceAt facts roots heads algebra declared choices reducer rigid complete root normalizes certifyNormal
          headTypingUnique fuel depth problem with
      | some found => some found
      | none => inPlaceSearch fuel problem rest

/-- **The in-place rule**: every depth below the newest declaration. -/
def inPlaceRule (fuel : Nat) {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) : Option (Found problem) :=
  inPlaceSearch facts roots heads algebra declared choices reducer rigid complete root normalizes certifyNormal
    headTypingUnique fuel problem (List.range' 1 (Θ.arity - 1))

/-- **One in-place round**: the Π round, and when it is stuck, the in-place rule on the prepared
store. -/
def inPlaceRound (fuel : Nat) {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) : Round S.levels size problem :=
  match piRound facts roots heads algebra declared choices reducer rigid complete root normalizes certifyNormal
      headTypingUnique rootComplete fuel problem with
  | .progress update smaller => .progress update smaller
  | .refuted absent => .refuted absent
  | .stuck =>
      match inPlaceRule facts roots heads algebra declared choices reducer rigid complete root normalizes certifyNormal
          headTypingUnique fuel (ContextualDependentNormalizing.prepare root rootComplete facts roots heads fuel problem).remaining with
      | some (.solved update smaller) =>
          .progress ((ContextualDependentNormalizing.prepare root rootComplete facts roots heads fuel problem).then update)
            (Prod.Lex.left _ _ (by
              have same := prepare_arity facts roots heads root rootComplete fuel problem
              change update.target.arity < Θ.arity
              omega))
      | some (.refuted absent) =>
          .refuted fun solvable =>
            absent ((ContextualDependentNormalizing.prepare root rootComplete facts roots heads fuel problem).solvable_iff.mp
              solvable)
      | none => .stuck

/-- **The in-place solver** at one budget. -/
def inPlaceSolver (fuel : Nat) : Solver S.levels where
  rank := size
  round := inPlaceRound facts roots heads algebra declared choices reducer rigid complete root normalizes certifyNormal
    headTypingUnique rootComplete fuel

/-- **The in-place solver as a fuel-indexed family.** -/
def inPlaceFamily : ContextualDependentDecisiveDriver.Family S.levels where
  rank := size
  round fuel := inPlaceRound facts roots heads algebra declared choices reducer rigid complete root normalizes
    certifyNormal headTypingUnique rootComplete fuel

/-- **Every refutation of the in-place round is certified**: it is the Π round's, or a refutation of
the prepared store by the in-place rule. -/
theorem inPlaceRound_refuted {fuel : Nat} {Θ : Context S.R} {problem : EquationStore (TotalTerm Θ)}
    {absent : ¬ (frames S.levels).Solvable problem}
    (refuted : inPlaceRound facts roots heads algebra declared choices reducer rigid complete root normalizes
      certifyNormal headTypingUnique rootComplete fuel problem = .refuted absent) :
    (∃ absent', piRound facts roots heads algebra declared choices reducer rigid complete root normalizes certifyNormal
        headTypingUnique rootComplete fuel problem = .refuted absent') ∨
      ∃ absent', inPlaceRule facts roots heads algebra declared choices reducer rigid complete root normalizes
        certifyNormal headTypingUnique fuel
        (ContextualDependentNormalizing.prepare root rootComplete facts roots heads fuel problem).remaining =
          some (.refuted absent') := by
  unfold inPlaceRound at refuted
  split at refuted
  · cases refuted
  · rename_i absent' computed
    exact .inl ⟨absent', computed⟩
  · split at refuted
    · cases refuted
    · rename_i absent' computed
      exact .inr ⟨absent', computed⟩
    · cases refuted

end ContextualDependentInPlace
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
