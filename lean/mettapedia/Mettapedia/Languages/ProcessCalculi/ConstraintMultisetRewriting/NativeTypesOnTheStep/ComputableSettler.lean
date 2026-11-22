import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NativeTypesOnTheStep.ConversionSettling
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentWorklist
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.Preservation

/-!
# A computable settler from decided solver families

**Decided families.** A decision on a store (`Decision`) is an initial solution, a certified
refutation, or no decision. A decided solver family (`Family`) decides some stores and declines the
rest. The settler of a list of families (`Settler.ofFamilies`) asks them in order and settles along the
first initial solution; it postpones a refuted or undecided store. It is computable whenever its
families are.

* **It agrees with the semantic settler on the union of the decided fragments**
  (`ofFamilies_agrees_ideal`): on every store some family decides, both settle exactly when the store is
  solvable, along answers inverse to each other up to agreement (`initial_unique_up_to_iso`).
* **The converting step does not depend on the representative** (`converting_admits_iff_of_settled`,
  `converting_admits_iff_of_postponed`): read at any settled answer, admission asks each row to convert
  along it, and conversion along one principal answer is conversion along every other. So on the union
  of the decided fragments the computable converting step admits exactly what the semantic one admits
  (`ofFamilies_converting_iff_ideal`), which is admission by conversion
  (`ofFamilies_converting_iff`). This is what fails for the settling step of raw rows
  (`Eta.representative_dependence`).

**The tree's worklist driver as a family** (`driverFamily`). A solved run carries a principal answer;
it is initial when its answer covers its frame by variables at their own types (`VariableCover`,
decidable, `epi_of_cover`, `initial_of_cover`). A refuted run carries its refutation.

**Typing a variable code** (`convertsAlong_var_iff`): a variable is typed exactly at the types its
declaration is usable at, so it converts along σ exactly when its declaration, substituted, is usable at
the row's type. Codes in general have no principal type here (an abstraction carries no domain), which is
also why raw typing is not closed under agreement.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace NativeTypesOnTheStep

open _root_.CategoryTheory Opposite Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta
open Interface.DependentFull (Make State Firing relabel)
open UnificationWithLevels (Agree InitialSolution EpiOnTerms)
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits (Enabled fire)

variable {Head L : Type} [UniverseLevel.LevelOrder L] {rules : Rules Head}
variable (levels : LevelModel rules L)

/-! ## Decisions and decided families -/

section Families

/-- **A decision on a store**: an initial solution, a certified refutation, or no decision. -/
inductive Decision {Δ : Context rules} (I : EquationStore (TotalTerm Δ)) : Type
  | settled (M : Context rules) (σ : M ⟶ Δ) (initial : InitialSolution (frames levels) I σ)
  | refuted (none : ¬ (frames levels).Solvable I)
  | undecided

/-- **A decided solver family**: a decision on every store. -/
def Family : Type := ∀ {Δ : Context rules} (I : EquationStore (TotalTerm Δ)), Decision levels I

variable {levels}

/-- A decision is decisive when it settles or refutes. -/
def Decision.Decisive {Δ : Context rules} {I : EquationStore (TotalTerm Δ)} :
    Decision levels I → Prop
  | .undecided => False
  | _ => True

/-- The verdict a decision gives the step: settle along its answer, or postpone. -/
def Decision.verdict {Δ : Context rules} {I : EquationStore (TotalTerm Δ)} :
    Decision levels I → Verdict levels I
  | .settled M σ initial => .settled M σ initial
  | .refuted _ => .postponed
  | .undecided => .postponed

/-- Whether a decision settles, as a computable readout. -/
def Decision.isSettled {Δ : Context rules} {I : EquationStore (TotalTerm Δ)} :
    Decision levels I → Bool
  | .settled _ _ _ => true
  | _ => false

/-- Whether a decision refutes, as a computable readout. -/
def Decision.isRefuted {Δ : Context rules} {I : EquationStore (TotalTerm Δ)} :
    Decision levels I → Bool
  | .refuted _ => true
  | _ => false

/-- A decisive decision makes the store decided: an initial solution, or no solution. -/
theorem Decision.decided {Δ : Context rules} {I : EquationStore (TotalTerm Δ)}
    {d : Decision levels I} (decisive : d.Decisive) : Decided levels I := by
  cases d with
  | settled M σ initial => exact Or.inl ⟨M, σ, initial⟩
  | refuted none => exact Or.inr none
  | undecided => exact decisive.elim

variable (levels)

/-- **The first decisive decision** of a list of families on a store. -/
def firstDecisionAt {Δ : Context rules} (I : EquationStore (TotalTerm Δ)) :
    List (Family levels) → Decision levels I
  | [] => .undecided
  | F :: rest =>
      match F I with
      | .undecided => firstDecisionAt I rest
      | decision => decision

/-- **The settler of a list of families**: the first decisive family's initial solution, or
postponement. -/
def Settler.ofFamilies (families : List (Family levels)) : Settler levels :=
  fun I => (firstDecisionAt levels I families).verdict

/-- A store is **decided by** a list of families when one of them is decisive on it. -/
def DecidedBy (families : List (Family levels)) {Δ : Context rules}
    (I : EquationStore (TotalTerm Δ)) : Prop :=
  ∃ F ∈ families, (F I).Decisive

/-- **On a store some family decides, the first decisive decision is decisive.** -/
theorem firstDecisionAt_decisive {Δ : Context rules} {I : EquationStore (TotalTerm Δ)} :
    ∀ {families : List (Family levels)}, DecidedBy levels families I →
      (firstDecisionAt levels I families).Decisive
  | [], ⟨_, member, _⟩ => absurd member List.not_mem_nil
  | F :: rest, ⟨G, member, decisive⟩ => by
      unfold firstDecisionAt
      cases first : F I with
      | settled M σ initial => trivial
      | refuted none => trivial
      | undecided =>
          rcases List.mem_cons.mp member with same | later
          · subst same
            rw [first] at decisive
            exact decisive.elim
          · exact firstDecisionAt_decisive ⟨G, later, decisive⟩

/-- **Two initial solutions of a store are inverse to each other up to agreement.** -/
theorem initial_unique_up_to_iso {Δ M M' : Context rules} {I : EquationStore (TotalTerm Δ)}
    {σ : M ⟶ Δ} {σ' : M' ⟶ Δ} (initial : InitialSolution (frames levels) I σ)
    (initial' : InitialSolution (frames levels) I σ') :
    ∃ (g : M ⟶ M') (g' : M' ⟶ M), Agree (frames levels) σ (g ≫ σ') ∧ Agree (frames levels) σ' (g' ≫ σ) ∧
      Agree (frames levels) (g ≫ g') (𝟙 M) ∧ Agree (frames levels) (g' ≫ g) (𝟙 M') := by
  obtain ⟨g, through⟩ := initial'.factor M σ initial.solves
  obtain ⟨g', through'⟩ := initial.factor M' σ' initial'.solves
  refine ⟨g, g', through, through', ?_, ?_⟩
  · apply initial.unique M σ (g ≫ g') (𝟙 M)
    · have back : Agree (frames levels) (g ≫ σ') (g ≫ (g' ≫ σ)) := through'.comp_left g
      have assoc : g ≫ (g' ≫ σ) = (g ≫ g') ≫ σ := (Category.assoc g g' σ).symm
      rw [assoc] at back
      exact UnificationWithLevels.Agree.trans through back
    · exact UnificationWithLevels.agree_id_comp (X := frames levels) (a := Δ) (b := M) σ
  · apply initial'.unique M' σ' (g' ≫ g) (𝟙 M')
    · have back : Agree (frames levels) (g' ≫ σ) (g' ≫ (g ≫ σ')) := through.comp_left g'
      have assoc : g' ≫ (g ≫ σ') = (g' ≫ g) ≫ σ' := (Category.assoc g' g σ').symm
      rw [assoc] at back
      exact UnificationWithLevels.Agree.trans through' back
    · exact UnificationWithLevels.agree_id_comp (X := frames levels) (a := Δ) (b := M') σ'

/-- **On the union of the decided fragments the computable settler agrees with the semantic one**:
both settle exactly the solvable stores, and their answers are inverse to each other up to agreement. -/
theorem ofFamilies_agrees_ideal {families : List (Family levels)} {Δ : Context rules}
    {I : EquationStore (TotalTerm Δ)} (decided : DecidedBy levels families I) :
    ((∃ (M : Context rules) (σ : M ⟶ Δ) (initial : InitialSolution (frames levels) I σ),
        Settler.ofFamilies levels families I = .settled M σ initial) ↔ (frames levels).Solvable I) ∧
      ((∃ (M : Context rules) (σ : M ⟶ Δ) (initial : InitialSolution (frames levels) I σ),
        Settler.ideal levels I = .settled M σ initial) ↔ (frames levels).Solvable I) ∧
      ∀ (M M' : Context rules) (σ : M ⟶ Δ) (σ' : M' ⟶ Δ) (initial : InitialSolution (frames levels) I σ)
        (initial' : InitialSolution (frames levels) I σ'),
        Settler.ofFamilies levels families I = .settled M σ initial →
        Settler.ideal levels I = .settled M' σ' initial' →
        ∃ (g : M ⟶ M') (g' : M' ⟶ M), Agree (frames levels) σ (g ≫ σ') ∧
          Agree (frames levels) σ' (g' ≫ σ) ∧ Agree (frames levels) (g ≫ g') (𝟙 M) ∧
          Agree (frames levels) (g' ≫ g) (𝟙 M') := by
  have decisive := firstDecisionAt_decisive levels decided
  refine ⟨⟨fun ⟨M, σ, initial, _⟩ => (principal_of_initial levels initial).solvable, fun solvable => ?_⟩,
    ⟨fun ⟨M, σ, initial, _⟩ => (principal_of_initial levels initial).solvable, fun solvable => ?_⟩,
    fun M M' σ σ' initial initial' _ _ => initial_unique_up_to_iso levels initial initial'⟩
  · unfold Settler.ofFamilies
    cases first : firstDecisionAt levels I families with
    | settled M σ initial => exact ⟨M, σ, initial, rfl⟩
    | refuted none => exact absurd solvable none
    | undecided =>
        rw [first] at decisive
        exact decisive.elim
  · rcases Decision.decided decisive with ⟨M, σ, initial⟩ | none
    · exact Settler.ideal_settles levels initial
    · exact absurd solvable none

end Families

/-! ## The converting step does not depend on the representative -/

section Independence

variable {O : Type} [DecidableEq O] (settler : Settler levels)

omit [DecidableEq O] in
/-- **Read at a settled answer, the converting shapes ask each row to convert along it.** -/
theorem convertingShapes_iff_of_settled {s : State rules O} {f : Firing levels s} {M : Context rules}
    {σ : M ⟶ f.helpers.frame} {initial : InitialSolution (frames levels) f.information σ}
    (verdict : settler f.information = .settled M σ initial) :
    ConvertingShapes levels settler f ↔
      f.taken.Nodup ∧ f.made.Nodup ∧ f.takes.length = f.taken.length ∧ f.reads.length = f.read.length ∧
        ∀ m ∈ f.makes, ConvertsAlong m.2 σ := by
  unfold ConvertingShapes
  by_cases typed : FrameTyped levels f
  · rw [plan_of_frameTyped levels settler typed]
    constructor
    · rintro ⟨a, b, c, d, _⟩
      exact ⟨a, b, c, d, fun m member => convertsAlong_of_wellTyped (typed m member) σ⟩
    · rintro ⟨a, b, c, d, _⟩
      exact ⟨a, b, c, d, fun m member => convertsAlong_of_wellTyped (typed m member) _⟩
  · rw [plan_of_not_frameTyped levels settler typed, verdict]
    rfl

omit [DecidableEq O] in
/-- **Postponed, the converting shapes ask each row to be typed in its frame.** -/
theorem convertingShapes_iff_of_postponed {s : State rules O} {f : Firing levels s}
    (verdict : settler f.information = .postponed) :
    ConvertingShapes levels settler f ↔ f.Shapes := by
  have identity : plan levels settler f = ⟨f.helpers.frame, 𝟙 _⟩ := by
    by_cases typed : FrameTyped levels f
    · exact plan_of_frameTyped levels settler typed
    · rw [plan_of_not_frameTyped levels settler typed, verdict]
      rfl
  unfold ConvertingShapes Firing.Shapes
  rw [identity]
  constructor
  · rintro ⟨a, b, c, d, rows⟩
    exact ⟨a, b, c, d, fun m member => (convertsAlong_id_iff m.2).mp (rows m member)⟩
  · rintro ⟨a, b, c, d, rows⟩
    exact ⟨a, b, c, d, fun m member => (convertsAlong_id_iff m.2).mpr (rows m member)⟩

/-- **Admission of the converting step, read at a settled answer**, for a firing without queries: its
shapes with each row converting along the answer, its enabling, and its guards at the answer. No plan
and no case on the frame typing is involved. -/
theorem converting_admits_iff_of_settled {s : State rules O} {f : Firing levels s}
    (noQueries : f.queries = []) {M : Context rules} {σ : M ⟶ f.helpers.frame}
    {initial : InitialSolution (frames levels) f.information σ}
    (verdict : settler f.information = .settled M σ initial) :
    (convertingStep levels O settler).Admits f ↔
      (f.taken.Nodup ∧ f.made.Nodup ∧ f.takes.length = f.taken.length ∧ f.reads.length = f.read.length ∧
        ∀ m ∈ f.makes, ConvertsAlong m.2 σ) ∧
      Enabled (fun _ : O => ()) s.present (f.selection.commit (T := Unit)) ∧
      (frames levels).Models σ f.guards := by
  have principal := principal_of_initial levels initial
  have guards : (frames levels).Entails f.information (fun _ τ => f.Holds τ) ↔
      (frames levels).Models σ f.guards := by
    rw [← Frames.Principal.entails_models_iff principal f.guards]
    unfold Firing.Holds
    rw [noQueries]
    constructor
    · exact fun entailed b τ solved => (entailed b τ solved).1
    · exact fun entailed b τ solved => ⟨entailed b τ solved, fun q member => absurd member List.not_mem_nil⟩
  constructor
  · rintro ⟨shapes, enabled, _, holds⟩
    exact ⟨(convertingShapes_iff_of_settled levels settler verdict).mp shapes, enabled, guards.mp holds⟩
  · rintro ⟨shapes, enabled, holds⟩
    exact ⟨(convertingShapes_iff_of_settled levels settler verdict).mpr shapes, enabled,
      principal.solvable, guards.mpr holds⟩

/-- **Postponed, the converting step admits what the present step admits.** -/
theorem converting_admits_iff_of_postponed {s : State rules O} {f : Firing levels s}
    (verdict : settler f.information = .postponed) :
    (convertingStep levels O settler).Admits f ↔ (DependentFull.step levels O).Admits f := by
  constructor
  · rintro ⟨shapes, enabled, solvable, holds⟩
    exact ⟨(convertingShapes_iff_of_postponed levels settler verdict).mp shapes, enabled, solvable, holds⟩
  · rintro ⟨shapes, enabled, solvable, holds⟩
    exact ⟨(convertingShapes_iff_of_postponed levels settler verdict).mpr shapes, enabled, solvable, holds⟩

/-- **Representative independence**: two settlers that both settle a firing's information give the
converting step the same admission. -/
theorem converting_admits_iff_of_both_settled (settler' : Settler levels) {s : State rules O}
    {f : Firing levels s} {M M' : Context rules} {σ : M ⟶ f.helpers.frame} {σ' : M' ⟶ f.helpers.frame}
    {initial : InitialSolution (frames levels) f.information σ}
    {initial' : InitialSolution (frames levels) f.information σ'}
    (verdict : settler f.information = .settled M σ initial)
    (verdict' : settler' f.information = .settled M' σ' initial') :
    (convertingStep levels O settler).Admits f ↔ (convertingStep levels O settler').Admits f := by
  have rows : ∀ m ∈ f.makes, ConvertsAlong m.2 σ ↔ ConvertsAlong m.2 σ' := fun m _ =>
    ((convertsAlong_iff_of_principal levels (principal_of_initial levels initial) m.2).trans
      (convertsAlong_iff_of_principal levels (principal_of_initial levels initial') m.2).symm)
  constructor
  · rintro ⟨shapes, enabled, solvable, holds⟩
    obtain ⟨a, b, c, d, along⟩ := (convertingShapes_iff_of_settled levels settler verdict).mp shapes
    exact ⟨(convertingShapes_iff_of_settled levels settler' verdict').mpr
      ⟨a, b, c, d, fun m member => (rows m member).mp (along m member)⟩, enabled, solvable, holds⟩
  · rintro ⟨shapes, enabled, solvable, holds⟩
    obtain ⟨a, b, c, d, along⟩ := (convertingShapes_iff_of_settled levels settler' verdict').mp shapes
    exact ⟨(convertingShapes_iff_of_settled levels settler verdict).mpr
      ⟨a, b, c, d, fun m member => (rows m member).mpr (along m member)⟩, enabled, solvable, holds⟩

/-- **On the union of the decided fragments the computable converting step admits exactly what the
semantic converting step admits.** -/
theorem ofFamilies_converting_iff_ideal (families : List (Family levels)) {s : State rules O}
    {f : Firing levels s} (decided : DecidedBy levels families f.information) :
    (convertingStep levels O (Settler.ofFamilies levels families)).Admits f ↔
      (convertingStep levels O (Settler.ideal levels)).Admits f := by
  have decisive := firstDecisionAt_decisive levels decided
  cases first : firstDecisionAt levels f.information families with
  | settled M σ initial =>
      have verdict : Settler.ofFamilies levels families f.information = .settled M σ initial := by
        unfold Settler.ofFamilies
        rw [first]
        rfl
      obtain ⟨M', σ', initial', verdict'⟩ := Settler.ideal_settles levels initial
      exact converting_admits_iff_of_both_settled levels _ _ verdict verdict'
  | refuted none =>
      have verdict : Settler.ofFamilies levels families f.information = .postponed := by
        unfold Settler.ofFamilies
        rw [first]
        rfl
      have verdict' : Settler.ideal levels f.information = .postponed :=
        Verdict.eq_postponed levels
          (fun M σ initial => none (principal_of_initial levels initial).solvable) _
      exact (converting_admits_iff_of_postponed levels _ verdict).trans
        (converting_admits_iff_of_postponed levels _ verdict').symm
  | undecided =>
      rw [first] at decisive
      exact decisive.elim

/-- **On the union of the decided fragments the computable converting step decides admission by
conversion.** -/
theorem ofFamilies_converting_iff (families : List (Family levels)) {s : State rules O}
    {f : Firing levels s} (decided : DecidedBy levels families f.information) :
    (convertingStep levels O (Settler.ofFamilies levels families)).Admits f ↔
      AdmitsByConversion levels f :=
  (ofFamilies_converting_iff_ideal levels families decided).trans
    (ideal_converting_iff_of_decided levels
      (Decision.decided (firstDecisionAt_decisive levels decided)))

end Independence

/-! ## The tree's worklist driver as a decided family -/

section Driver

variable [DecidableEq Head]

omit [UniverseLevel.LevelOrder L] [DecidableEq Head] in
/-- **A variable cover**: every variable of the answer's frame is the image of a variable of the
store's frame, at its own type. -/
def VariableCover {M Δ : Context rules} (σ : M ⟶ Δ) : Prop :=
  ∀ j : Fin M.arity, ∃ i : Fin Δ.arity, σ.substitution i = .var j ∧
    subst σ.substitution (Ctx.lookup Δ.raw i) = Ctx.lookup M.raw j

omit [UniverseLevel.LevelOrder L] in
instance {M Δ : Context rules} (σ : M ⟶ Δ) : Decidable (VariableCover σ) := by
  unfold VariableCover
  infer_instance

omit [DecidableEq Head] in
/-- **A covering answer is an epimorphism on terms**: two substitutions agreeing on its image agree on
each variable it covers, hence everywhere. -/
theorem epi_of_cover {M Δ : Context rules} {σ : M ⟶ Δ} (cover : VariableCover σ) :
    EpiOnTerms (frames levels) σ := by
  intro Θ g h same
  have equal : homTypedEquality rules g h := by
    refine ⟨g.typed, fun j => ?_⟩
    obtain ⟨i, hi, htype⟩ := cover j
    obtain ⟨u, hu, typed⟩ := Δ.formed.lookup i
    let t : TotalTerm Δ := ⟨⟨Ctx.lookup Δ.raw i, u, hu, typed⟩, ⟨.var i, Derivable.var i⟩⟩
    have e := (same t).2
    change Equal rules Θ.raw (subst g.substitution (subst σ.substitution (.var i)))
      (subst h.substitution (subst σ.substitution (.var i)))
      (subst g.substitution (subst σ.substitution (Ctx.lookup Δ.raw i))) at e
    rw [show subst σ.substitution (.var i) = .var j from hi, htype] at e
    exact e
  exact fun t => act_equal_of_substEq levels equal t

omit [DecidableEq Head] in
/-- A principal answer that covers its frame is the initial solution. -/
theorem initial_of_cover {M Δ : Context rules} {I : EquationStore (TotalTerm Δ)} {σ : M ⟶ Δ}
    (principal : (frames levels).Principal I σ) (cover : VariableCover σ) :
    InitialSolution (frames levels) I σ :=
  UnificationWithLevels.Principal.initial principal (epi_of_cover levels cover)

/-- **The tree's worklist driver as a decided family**: a solved run whose answer covers its frame
settles along it, a refuted run refutes, every other run declines. -/
def driverFamily (solver : ContextualDependentWorklist.Solver levels) (fuel : Nat) : Family levels :=
  fun I =>
    match ContextualDependentWorklist.run solver I fuel with
    | .solved state finished =>
        if cover : VariableCover state.answer then
          .settled state.target state.answer (initial_of_cover levels (state.completed finished) cover)
        else .undecided
    | .refuted absent => .refuted absent
    | .stuck _ => .undecided
    | .cutoff _ => .undecided

end Driver

/-! ## Typing a variable code -/

section Variables

omit [UniverseLevel.LevelOrder L] in
/-- **A variable converts exactly when its declaration does**: it is typed in its frame exactly at the
types its declaration is usable at. -/
theorem convertsAlong_var_iff {M Δ : Context rules} (m : Make Δ) (σ : M ⟶ Δ) {i : Fin Δ.arity}
    (code : m.code = .var i) :
    ConvertsAlong m σ ↔
      Below rules M.raw (subst σ.substitution (Ctx.lookup Δ.raw i)) (m.type.reindex σ).code := by
  constructor
  · rintro ⟨B, typed, inside⟩
    have typedVar : Typed rules Δ.raw (.var i) B.code := code ▸ typed
    have le : TypeLe rules Δ.raw (Ctx.lookup Δ.raw i) B.code := Typed.generation typedVar
    have below : Below rules Δ.raw (Ctx.lookup Δ.raw i) B.code := TypeLe.toBelow le B.isType
    exact .subTrans (below_substitute below σ.typed) inside
  · intro below
    obtain ⟨u, hu, typed⟩ := Δ.formed.lookup i
    refine ⟨⟨Ctx.lookup Δ.raw i, u, hu, typed⟩, ?_, below⟩
    show Typed rules Δ.raw m.code (Ctx.lookup Δ.raw i)
    rw [code]
    exact Derivable.var i

end Variables

end NativeTypesOnTheStep

#print axioms NativeTypesOnTheStep.Decision.decided
#print axioms NativeTypesOnTheStep.Settler.ofFamilies
#print axioms NativeTypesOnTheStep.firstDecisionAt_decisive
#print axioms NativeTypesOnTheStep.initial_unique_up_to_iso
#print axioms NativeTypesOnTheStep.ofFamilies_agrees_ideal
#print axioms NativeTypesOnTheStep.convertingShapes_iff_of_settled
#print axioms NativeTypesOnTheStep.convertingShapes_iff_of_postponed
#print axioms NativeTypesOnTheStep.converting_admits_iff_of_settled
#print axioms NativeTypesOnTheStep.converting_admits_iff_of_postponed
#print axioms NativeTypesOnTheStep.converting_admits_iff_of_both_settled
#print axioms NativeTypesOnTheStep.ofFamilies_converting_iff_ideal
#print axioms NativeTypesOnTheStep.ofFamilies_converting_iff
#print axioms NativeTypesOnTheStep.epi_of_cover
#print axioms NativeTypesOnTheStep.initial_of_cover
#print axioms NativeTypesOnTheStep.driverFamily
#print axioms NativeTypesOnTheStep.convertsAlong_var_iff

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
