import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NativeTypesOnTheStep.DeclaredComputation
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ProgrammingOnTheStep.VectorPrograms
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentEtaElimination
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.RigidReadback

/-!
# Vector append: the match settles the length, declared addition computes the type

The clause `vappend nil ys = ys` of
`vappend : vec m → vec k → vec (add m k)`. Matching `nil` teaches `m ≐ zero` (`matchNil`), and the
right side `ys : vec k` must be accepted at the declared result type `vec (add m k)`. Both missing
pieces are needed:

* **F1, settling.** The firing makes `ys` at `vec (add m k)` and is told `m ≐ zero`. Eliminating the
  defined variable `m` is the initial solution of that information (`definition_initial`, from
  `ContextualDependentEta.Elimination.definition_principal` and `instantiate_epi`).
* **F5, declared computation.** With addition declared computing, `add zero b ↦ b` and
  `add (succ a) b ↦ succ (add a b)` (`addComputation`, `vrules`), the row is typed after the match
  (`vappend_typedAfterMatch`): at every solution `m` is `zero`, so `vec (add m k)` converts to `vec k`.

The settling step with the semantic settler admits the clause (`vappend_settled`); settled along
the match, the row is typed at `vec (add zero k)` in the frame `k : nat, ys : vec k`
(`vappend_settled_type`, `vappend_settled_typed`).

**Declared computation turns refutations into equations.** The equations D2 found refuted in the
rigid package, `add 0 1 ≐ 1` and `add (succ 0) 1 ≐ succ (add 0 1)`
(`VectorPrograms.add_not_in_knowledge`, `add_equation_not_in_knowledge`), are solved by the identity
here (`add_solvable`, `add_equation_solvable`).

**Controls.**
* Matching alone does not type the row. At a closed instance the clause's type equation is
  `vec 1 ≐ vec (add 0 1)`: refuted in the rigid package (`rigid_vec_unsolvable`, through the
  injectivity of `vec` that `LogicOverTheStep.RigidReadback` derives from the algorithmic equality),
  and solved in the declared one (`declared_vec_solvable`). The same holds for the length equation
  `add 0 1 ≐ 1` (`length_equation_separation`).
* A declaration that is not confluent is refused: `add zero b ↦ b` together with
  `add zero b ↦ zero` gives the term `add 0 1` two reducts (`bad_not_rootDeterministic`), while the
  declared addition has at most one (`add_rootDeterministic`). Accepted, it would identify the two
  distinct normal forms `1` and `0` (`bad_breaks_uniqueness`), so the knowledge would solve
  `1 ≐ 0` (`bad_solves_one_zero`), which the rigid package refutes (`rigid_one_zero_unsolvable`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace NativeTypesOnTheStep

open _root_.CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta
open Interface.DependentFull (Make State Firing enabled_iff)
open UnificationWithLevels (Agree InitialSolution EpiOnTerms)

/-! ## Eliminating a defined variable is the initial solution -/

section Definitions

variable {Head L : Type} [UniverseLevel.LevelOrder L] {rules : Rules Head}
variable (levels : LevelModel rules L)

omit [UniverseLevel.LevelOrder L] in
/-- A variable of a frame, as a judged term at its declared type. -/
noncomputable def variableTerm (Γ : Context rules) (i : Fin Γ.arity) : TotalTerm Γ :=
  ⟨⟨Ctx.lookup Γ.raw i, Classical.choose (Γ.formed.lookup i), (Classical.choose_spec (Γ.formed.lookup i)).1,
      (Classical.choose_spec (Γ.formed.lookup i)).2⟩, ⟨.var i, Derivable.var (R := rules) (Γ := Γ.raw) i⟩⟩

/-- **Eliminating a defined variable is an epimorphism on terms**: two substitutions that agree on
the image of the elimination agree on every variable. -/
theorem instantiate_epi (Γ : Context rules) {type : TypeOver Γ} (value : Term Γ type) :
    EpiOnTerms (frames levels) (Elimination.instantiate Γ value) := by
  intro Θ g h agree
  have same : homTypedEquality rules g h := by
    refine ⟨g.typed, fun i => ?_⟩
    have back : ((variableTerm Γ i).reindex (projectionHom Γ type)).reindex
        (Elimination.instantiate Γ value) = variableTerm Γ i := by
      rw [← reindex_comp, Elimination.instantiate_projection, reindex_id]
    have e := agree ((variableTerm Γ i).reindex (projectionHom Γ type))
    change (frames levels).E ((((variableTerm Γ i).reindex (projectionHom Γ type)).reindex
        (Elimination.instantiate Γ value)).reindex g)
      ((((variableTerm Γ i).reindex (projectionHom Γ type)).reindex (Elimination.instantiate Γ value)).reindex h) at e
    rw [back] at e
    exact e.2
  exact fun t => act_equal_of_substEq levels same t

/-- **Eliminating a defined variable is the initial solution of its definition.** -/
theorem definition_initial (Γ : Context rules) {type : TypeOver Γ} (value : Term Γ type) :
    InitialSolution (frames levels) [Elimination.definition Γ value] (Elimination.instantiate Γ value) :=
  UnificationWithLevels.Principal.initial (Elimination.definition_principal levels Γ value)
    (instantiate_epi levels Γ value)

end Definitions

namespace VectorAppend

open ProgrammingOnTheStep.VectorPackage
open ProgrammingOnTheStep.VectorPrograms (one one_typed natTerm)

/-! ## Addition declared computing -/

/-- **Addition's computing rules**, by recursion on the first argument. -/
inductive AddStep : {n : Nat} → Tower.Tm n → Tower.Tm n → Prop
  | zero {n : Nat} (b : Tower.Tm n) : AddStep (.app (.app (.const addN) (.const zeroN)) b) b
  | succ {n : Nat} (a b : Tower.Tm n) :
      AddStep (.app (.app (.const addN) (.app (.const succN) a)) b)
        (.app (.const succN) (.app (.app (.const addN) a) b))

/-- The declared root computation of addition. -/
def addComputation : RootComputation Tower.Head where
  step l r := AddStep l r
  rename := by
    intro n m ρ left right h
    exact match h with
      | .zero b => AddStep.zero (Presentation.rename ρ b)
      | .succ a b => AddStep.succ (Presentation.rename ρ a) (Presentation.rename ρ b)
  substitute := by
    intro n m σ left right h
    exact match h with
      | .zero b => AddStep.zero (subst σ b)
      | .succ a b => AddStep.succ (subst σ a) (subst σ b)

/-- **The vector package with addition declared computing.** -/
abbrev vrules : Rules Tower.Head := declare rules addComputation

abbrev vlevels : LevelModel vrules Nat := declareLevels levels addComputation

theorem vtyped {n : Nat} {Γ : Tower.Ctx n} {t A : Tower.Tm n} (typed : Typed rules Γ t A) :
    Typed vrules Γ t A :=
  typed_declare addComputation typed

/-- **No term has two declared reducts**: the declaration passes the check. -/
theorem add_rootDeterministic : RootDeterministic addComputation := by
  intro n l r r' h h'
  cases h with
  | zero b => cases h' with
    | zero => rfl
  | succ a b => cases h' with
    | succ => rfl

/-! ## The equations D2 found refuted -/

/-- `nat` as a formed type over any frame of the declared package. -/
def vnat (Γ : Context vrules) : TypeOver Γ := ⟨natC, u0, .sort _, vtyped (nat_typed _)⟩

theorem addZeroOne_typed : Typed vrules .nil (addC zeroC one) natC :=
  vtyped (add_typed (zero_typed _) (one_typed _))

/-- `add 0 1 ≐ 1`, in the declared package. -/
def addStore : EquationStore (TotalTerm (empty vrules)) :=
  [(⟨vnat _, ⟨addC zeroC one, addZeroOne_typed⟩⟩, ⟨vnat _, ⟨one, vtyped (one_typed _)⟩⟩)]

/-- **`add 0 1 ≐ 1` is solved by the identity** once addition computes. -/
theorem add_solvable : (frames vlevels).Solvable addStore := by
  refine ⟨empty vrules, 𝟙 _, ?_⟩
  intro e member
  obtain rfl := List.mem_singleton.mp member
  show (frames vlevels).E (TotalTerm.reindex _ (𝟙 _)) (TotalTerm.reindex _ (𝟙 _))
  rw [reindex_id, reindex_id]
  exact (equivalent_iff vlevels _ _).mpr ⟨(vnat _).isType.refl,
    .root (declare_step (AddStep.zero one)) addZeroOne_typed (vtyped (one_typed _))⟩

/-- `add (succ 0) 1 ≐ succ (add 0 1)`, in the declared package. -/
def addEquationStore : EquationStore (TotalTerm (empty vrules)) :=
  [(⟨vnat _, ⟨addC one one, vtyped (add_typed (one_typed _) (one_typed _))⟩⟩,
    ⟨vnat _, ⟨succC (addC zeroC one), vtyped (succ_typed (add_typed (zero_typed _) (one_typed _)))⟩⟩)]

/-- **The recursion equation of addition is solved by the identity.** -/
theorem add_equation_solvable : (frames vlevels).Solvable addEquationStore := by
  refine ⟨empty vrules, 𝟙 _, ?_⟩
  intro e member
  obtain rfl := List.mem_singleton.mp member
  show (frames vlevels).E (TotalTerm.reindex _ (𝟙 _)) (TotalTerm.reindex _ (𝟙 _))
  rw [reindex_id, reindex_id]
  exact (equivalent_iff vlevels _ _).mpr ⟨(vnat _).isType.refl,
    .root (declare_step (AddStep.succ zeroC one)) (vtyped (add_typed (one_typed _) (one_typed _)))
      (vtyped (succ_typed (add_typed (zero_typed _) (one_typed _))))⟩

/-! ## The clause `vappend nil ys = ys` -/

/-- The frame `k : nat`. -/
abbrev ctxK : Context vrules := extend (empty vrules) (vnat _)

/-- `vec k`, over `k : nat`. -/
def vecK : TypeOver ctxK :=
  ⟨vecC (.var 0), u0, .sort _, vtyped (vec_typed (Derivable.var (R := rules) (Γ := ctxK.raw) 0))⟩

/-- The frame `k : nat, ys : vec k`. -/
abbrev ctxKY : Context vrules := extend ctxK vecK

/-- The call frame `k : nat, ys : vec k, m : nat`. -/
abbrev callFrame : Context vrules := extend ctxKY (vnat _)

/-- `vec (add m k)`, the declared result type of the call. -/
def callType : TypeOver callFrame :=
  ⟨vecC (addC (.var 0) (.var 2)), u0, .sort _,
    vtyped (vec_typed (add_typed (Derivable.var (R := rules) (Γ := callFrame.raw) 0)
      (Derivable.var (R := rules) (Γ := callFrame.raw) 2)))⟩

/-- **The clause's made row**: `ys`, at the call's declared type `vec (add m k)`. -/
def vappendRow : Make callFrame := ⟨callType, .var 1⟩

/-- `zero`, as a term of `nat` over `k, ys`. -/
def zeroTerm : Term ctxKY (vnat _) := ⟨zeroC, vtyped (zero_typed _)⟩

/-- **What matching `nil` teaches**: `m ≐ zero`. -/
def matchNil : Equation (TotalTerm callFrame) := Elimination.definition ctxKY zeroTerm

/-- The state of the call: its frame, no knowledge, no rows. -/
def callState : State vrules Nat :=
  ⟨callFrame, [], ∅, fun _ => ⟨vnat _, ⟨.var 0, Derivable.var (R := vrules) (Γ := callFrame.raw) 0⟩⟩⟩

/-- **The clause `vappend nil ys = ys`**: told what matching `nil` teaches, it makes `ys` at the
call's declared type. -/
def vappendFiring : Firing vlevels callState where
  helpers := .nil _
  taken := []
  read := []
  takes := []
  reads := []
  makes := [(0, vappendRow)]
  tells := [matchNil]
  guards := []
  queries := []

theorem vappendFiring_information : vappendFiring.information = [matchNil] := rfl

/-- **The row is typed after the match**: at every solution `m` is `zero`, so `vec (add m k)`
converts to `vec k` by the declared computation of addition. -/
theorem vappend_typedAfterMatch :
    TypedAfterMatch vlevels ([matchNil] : EquationStore (TotalTerm callFrame)) vappendRow := by
  rw [typedAfterMatch_iff]
  intro Θ τ solved
  have mZero : Equal vrules Θ.raw (τ.substitution 0) zeroC natC :=
    (solved matchNil (List.mem_singleton_self _)).2
  have mTyped : Typed vrules Θ.raw (τ.substitution 0) natC := τ.typed 0
  have kTyped : Typed vrules Θ.raw (τ.substitution 2) natC := τ.typed 2
  have ysTyped : Typed vrules Θ.raw (τ.substitution 1) (vecC (τ.substitution 2)) := τ.typed 1
  have zeroTyped : Typed vrules Θ.raw zeroC natC := vtyped (zero_typed _)
  have addConst : Typed vrules Θ.raw (.const addN) (.pi natC (.pi natC natC)) :=
    vtyped (.const declared_add addTy_typed (.sort _))
  have vecConst : Typed vrules Θ.raw (.const vecN) (.pi natC U0) :=
    vtyped (.const declared_vec vecTy_typed (.sort _))
  have addZeroK : Typed vrules Θ.raw (addC zeroC (τ.substitution 2)) natC :=
    .appElim (.appElim addConst zeroTyped) kTyped
  have toZero : Equal vrules Θ.raw (addC (τ.substitution 0) (τ.substitution 2))
      (addC zeroC (τ.substitution 2)) natC :=
    .appCong (.appCong (.refl addConst) mZero) (.refl kTyped)
  have computes : Equal vrules Θ.raw (addC zeroC (τ.substitution 2)) (τ.substitution 2) natC :=
    .root (declare_step (AddStep.zero _)) addZeroK kTyped
  have vecEq : Equal vrules Θ.raw (vecC (addC (τ.substitution 0) (τ.substitution 2)))
      (vecC (τ.substitution 2)) U0 :=
    .appCong (.refl vecConst) (.trans toZero computes)
  exact .conv ysTyped (.symm vecEq) (.sort _)

/-- **The clause is admitted after the match.** -/
theorem vappend_admitsAfterMatch : AdmitsAfterMatch vlevels vappendFiring := by
  refine ⟨⟨List.nodup_nil, List.nodup_singleton _, rfl, rfl, fun m member => ?_⟩,
    (enabled_iff vappendFiring).mpr ⟨fun _ member => absurd member List.not_mem_nil,
      fun _ member => absurd member List.not_mem_nil, fun _ member => absurd member List.not_mem_nil,
      fun o _ inside => Finset.notMem_empty o inside⟩,
    ⟨ctxKY, Elimination.instantiate ctxKY zeroTerm, (definition_initial vlevels ctxKY zeroTerm).solves⟩, ?_⟩
  · obtain rfl := List.mem_singleton.mp member
    exact vappend_typedAfterMatch
  · intro _ _ _
    exact ⟨fun _ member => absurd member List.not_mem_nil, fun _ member => absurd member List.not_mem_nil⟩

/-- **The settling step admits the clause**, settling along the match. -/
theorem vappend_settled : (settlingStep vlevels Nat (Settler.ideal vlevels)).Admits vappendFiring :=
  ideal_admits_of_admitsAfterMatch vlevels vappend_admitsAfterMatch (definition_initial vlevels ctxKY zeroTerm)

/-- **Settled along the match, the declared result type is `vec (add zero k)`** over `k, ys`. -/
theorem vappend_settled_type :
    (vappendRow.reindex (Elimination.instantiate ctxKY zeroTerm)).type.code = vecC (addC zeroC (.var 1)) :=
  rfl

/-- **... and `ys` is accepted at it.** -/
theorem vappend_settled_typed : (vappendRow.reindex (Elimination.instantiate ctxKY zeroTerm)).WellTyped :=
  settled_complete vlevels (definition_initial vlevels ctxKY zeroTerm).solves vappend_typedAfterMatch

/-! ## Controls -/

/-- **Control: matching alone does not type the row.** The length equation the clause's type
equation reduces to, `add 0 1 ≐ 1` at a closed instance, is refuted in the rigid package and solved
once addition is declared computing. -/
theorem length_equation_separation :
    ¬ (frames levels).Solvable ProgrammingOnTheStep.VectorPrograms.addStore ∧
      (frames vlevels).Solvable addStore :=
  ⟨ProgrammingOnTheStep.VectorPrograms.add_not_in_knowledge, add_solvable⟩

/-- `U0`, as a formed type of the empty frame of the rigid package. -/
def u0Type : TypeOver (empty rules) := ⟨U0, .sort (.succ Tower.zero), .sort _, universe_typed _⟩

/-- `vec 1 ≐ vec (add 0 1)` in the rigid package: the clause's type equation at a closed instance. -/
def rigidVecStore : EquationStore (TotalTerm (empty rules)) :=
  [(⟨u0Type, ⟨vecC one, vec_typed (one_typed _)⟩⟩,
    ⟨u0Type, ⟨vecC (addC zeroC one), vec_typed (add_typed (zero_typed _) (one_typed _))⟩⟩)]

/-- **Control at the type: without declared computation the clause's type equation is refuted.** A
solution would make `vec 1` and `vec (add 0 1)` equal types, so `1` and `add 0 1` equal naturals
(`LogicOverTheStep.RigidReadback.vec_injective`), which the rigid package refutes. -/
theorem rigid_vec_unsolvable : ¬ (frames levels).Solvable rigidVecStore := by
  rintro ⟨Θ, σ, solved⟩
  have e := (solved _ (List.mem_singleton_self _)).2
  have types : TypeEq rules Θ.raw (vecC one) (vecC (addC zeroC one)) := ⟨u0, .sort _, e⟩
  have lengths : Equal rules Θ.raw one (addC zeroC one) natC :=
    LogicOverTheStep.RigidReadback.vec_injective types
  apply ProgrammingOnTheStep.VectorPrograms.add_not_in_knowledge
  refine ⟨Θ, σ, fun e' member => ?_⟩
  obtain rfl := List.mem_singleton.mp member
  exact ⟨⟨u0, .sort _, .refl (nat_typed _)⟩, .symm lengths⟩

/-- `U0`, as a formed type of the empty frame of the declared package. -/
def vu0Type : TypeOver (empty vrules) := ⟨U0, .sort (.succ Tower.zero), .sort _, vtyped (universe_typed _)⟩

/-- The same equation in the declared package. -/
def declaredVecStore : EquationStore (TotalTerm (empty vrules)) :=
  [(⟨vu0Type, ⟨vecC one, vtyped (vec_typed (one_typed _))⟩⟩,
    ⟨vu0Type, ⟨vecC (addC zeroC one), vtyped (vec_typed (add_typed (zero_typed _) (one_typed _)))⟩⟩)]

/-- **... and solved by the identity once addition computes.** -/
theorem declared_vec_solvable : (frames vlevels).Solvable declaredVecStore := by
  refine ⟨empty vrules, 𝟙 _, ?_⟩
  intro e member
  obtain rfl := List.mem_singleton.mp member
  show (frames vlevels).E (TotalTerm.reindex _ (𝟙 _)) (TotalTerm.reindex _ (𝟙 _))
  rw [reindex_id, reindex_id]
  have vecConst : Typed vrules .nil (.const vecN) (.pi natC U0) :=
    vtyped (.const declared_vec vecTy_typed (.sort _))
  have computes : Equal vrules .nil one (addC zeroC one) natC :=
    .symm (.root (declare_step (AddStep.zero one)) addZeroOne_typed (vtyped (one_typed _)))
  exact (equivalent_iff vlevels _ _).mpr ⟨vu0Type.isType.refl, .appCong (.refl vecConst) computes⟩

/-- **A declaration that is not confluent**: `add zero b ↦ b` and `add zero b ↦ zero`. -/
inductive BadStep : {n : Nat} → Tower.Tm n → Tower.Tm n → Prop
  | keep {n : Nat} (b : Tower.Tm n) : BadStep (.app (.app (.const addN) (.const zeroN)) b) b
  | drop {n : Nat} (b : Tower.Tm n) : BadStep (.app (.app (.const addN) (.const zeroN)) b) (.const zeroN)

def badComputation : RootComputation Tower.Head where
  step l r := BadStep l r
  rename := by
    intro n m ρ left right h
    exact match h with
      | .keep b => BadStep.keep (Presentation.rename ρ b)
      | .drop b => BadStep.drop (Presentation.rename ρ b)
  substitute := by
    intro n m σ left right h
    exact match h with
      | .keep b => BadStep.keep (subst σ b)
      | .drop b => BadStep.drop (subst σ b)

/-- The package with the bad declaration. -/
abbrev brules : Rules Tower.Head := declare rules badComputation

/-- **Control: the bad declaration fails the check**: `add 0 1` has the two reducts `1` and `0`. -/
theorem bad_not_rootDeterministic : ¬ RootDeterministic badComputation := by
  intro deterministic
  have same := deterministic (addC zeroC one : Tower.Tm 0) one zeroC (BadStep.keep one) (BadStep.drop one)
  exact absurd same (by decide)

/-- A term is normal for a package when no step of its conversion applies to it. -/
def Normal {Head : Type} (R : Rules Head) {n : Nat} (t : Tm Head n) : Prop :=
  ∀ t' : Tm Head n, ¬ StepCore R.computation R.headEq t t'

theorem bad_zero_normal : Normal brules (.const zeroN : Tower.Tm 0) := by
  intro t h
  cases h with
  | root h => rcases h with h | h <;> cases h

theorem bad_one_normal : Normal brules (.app (.const succN) (.const zeroN) : Tower.Tm 0) := by
  intro t h
  cases h with
  | root h => rcases h with h | h <;> cases h
  | congAppFun h => cases h with
    | root h => rcases h with h | h <;> cases h
  | congAppArg h => cases h with
    | root h => rcases h with h | h <;> cases h

/-- **The bad declaration breaks uniqueness of normal forms**: `1` and `0` are distinct normal
forms, and typed conversion identifies them. -/
theorem bad_breaks_uniqueness :
    (one : Tower.Tm 0) ≠ zeroC ∧ Normal brules (one : Tower.Tm 0) ∧ Normal brules (zeroC : Tower.Tm 0) ∧
      Equal brules .nil one zeroC natC := by
  have addTyped : Typed brules .nil (addC zeroC one) natC :=
    typed_declare badComputation (add_typed (zero_typed _) (one_typed _))
  refine ⟨by decide, bad_one_normal, bad_zero_normal, ?_⟩
  exact .trans (.symm (.root (declare_step (BadStep.keep one)) addTyped
      (typed_declare badComputation (one_typed _))))
    (.root (declare_step (BadStep.drop one)) addTyped (typed_declare badComputation (zero_typed _)))

/-- `1 ≐ 0` in the rigid package. -/
def rigidOneZero : EquationStore (TotalTerm (empty rules)) :=
  [(natTerm one (one_typed _), natTerm zeroC (zero_typed _))]

/-- **The rigid package refutes `1 ≐ 0`.** -/
theorem rigid_one_zero_unsolvable : ¬ (frames levels).Solvable rigidOneZero :=
  ContextualDependentRigid.not_solvable_of_storeClashes (S := setting) rigid facts complete (by decide)

/-- `nat` over the empty frame of the bad package. -/
def bnat : TypeOver (empty brules) := ⟨natC, u0, .sort _, typed_declare badComputation (nat_typed _)⟩

/-- `1 ≐ 0` in the bad package. -/
def badOneZero : EquationStore (TotalTerm (empty brules)) :=
  [(⟨bnat, ⟨one, typed_declare badComputation (one_typed _)⟩⟩,
    ⟨bnat, ⟨zeroC, typed_declare badComputation (zero_typed _)⟩⟩)]

/-- **... and the bad package's knowledge solves it**: the declaration must be refused. -/
theorem bad_solves_one_zero : (frames (declareLevels levels badComputation)).Solvable badOneZero := by
  refine ⟨empty brules, 𝟙 _, ?_⟩
  intro e member
  obtain rfl := List.mem_singleton.mp member
  show (frames (declareLevels levels badComputation)).E (TotalTerm.reindex _ (𝟙 _)) (TotalTerm.reindex _ (𝟙 _))
  rw [reindex_id, reindex_id]
  exact (equivalent_iff (declareLevels levels badComputation) _ _).mpr
    ⟨bnat.isType.refl, bad_breaks_uniqueness.2.2.2⟩

end VectorAppend

end NativeTypesOnTheStep

#print axioms NativeTypesOnTheStep.instantiate_epi
#print axioms NativeTypesOnTheStep.definition_initial
#print axioms NativeTypesOnTheStep.VectorAppend.add_rootDeterministic
#print axioms NativeTypesOnTheStep.VectorAppend.add_solvable
#print axioms NativeTypesOnTheStep.VectorAppend.add_equation_solvable
#print axioms NativeTypesOnTheStep.VectorAppend.vappend_typedAfterMatch
#print axioms NativeTypesOnTheStep.VectorAppend.vappend_admitsAfterMatch
#print axioms NativeTypesOnTheStep.VectorAppend.vappend_settled
#print axioms NativeTypesOnTheStep.VectorAppend.vappend_settled_type
#print axioms NativeTypesOnTheStep.VectorAppend.vappend_settled_typed
#print axioms NativeTypesOnTheStep.VectorAppend.length_equation_separation
#print axioms NativeTypesOnTheStep.VectorAppend.rigid_vec_unsolvable
#print axioms NativeTypesOnTheStep.VectorAppend.declared_vec_solvable
#print axioms NativeTypesOnTheStep.VectorAppend.bad_not_rootDeterministic
#print axioms NativeTypesOnTheStep.VectorAppend.bad_breaks_uniqueness
#print axioms NativeTypesOnTheStep.VectorAppend.rigid_one_zero_unsolvable
#print axioms NativeTypesOnTheStep.VectorAppend.bad_solves_one_zero

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
