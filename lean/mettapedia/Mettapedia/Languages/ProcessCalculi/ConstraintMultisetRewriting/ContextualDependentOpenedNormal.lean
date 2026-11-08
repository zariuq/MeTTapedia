import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentAcceptance3DeadBinder

/-!
# Normal reducts of opened sides, from strong normalization

`OpenedNormal` asks that both opened sides of every equation have a directed normal reduct. In a rule package without
root computation whose typed terms are strongly normalizing (`StronglyNormalizing`), **every store has it**
(`openedNormal_of_sn`): each side is a typed term, so it has a normal reduct (`exists_normal_of_sn`); opening follows
reduction (`star_openCode`); and a normal code opens to a normal form at every depth
(`ContextualDependentShortClosure.opens_normal`).

So on such a package the corrected class `PermutedNormal` is the permuted Miller class alone
(`permutedNormal_iff_permutedMiller`), and a round keeps `PermutedNormal` exactly when it keeps `PermutedMiller`
(`keepsPermutedNormal_iff`). Strong normalization is the property a package must supply; the tower supplies it
(`ContextualDependentAcceptance4.tower_stronglyNormalizing`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentOpenedNormal

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentUpdate ContextualDependentWorklist
open ContextualDependentDynamicFragment ContextualDependentShortClosure ContextualDependentMillerClosure
open ContextualDependentRank ContextualDependentAcceptance3
open ExecutableReduction ContextualDependentExecutableJoin

section Raw

variable {Head : Type} {R : Rules Head}

/-- **A strongly normalizing term has a directed normal reduct.** -/
theorem exists_normal_of_sn {n : Nat} {t : Tm Head n} (sn : StrongNormalization.SN R t) :
    ∃ N, Star (R := R) t N ∧ Normal R N := by
  induction sn with
  | intro t _ next =>
      by_cases moves : ∃ u, StrongNormalization.Reduces R t u
      · obtain ⟨u, step⟩ := moves
        obtain ⟨N, toN, normal⟩ := next u step
        exact ⟨N, Relation.ReflTransGen.head step toN, normal⟩
      · exact ⟨t, .refl, fun u step => moves ⟨u, step⟩⟩

/-- **Opening follows reduction.** -/
theorem star_openCode {n : Nat} {code code' : Tm Head n} (steps : Star (R := R) code code') :
    ∀ count, Star (R := R) (openCode count code) (openCode count code')
  | 0 => steps
  | count + 1 => by
      change Star (R := R) (.app (Presentation.rename wk (openCode count code)) (.var 0))
        (.app (Presentation.rename wk (openCode count code')) (.var 0))
      exact star_app (star_rename wk (star_openCode steps count)) .refl

/-- **A code with a normal reduct opens to a normal form at every depth**, in a package without root computation. -/
theorem opens_normal_of_reduct (empty : R.computation = RootComputation.empty) {n : Nat} {code : Tm Head n}
    (reduct : ∃ N, Star (R := R) code N ∧ Normal R N) (count : Nat) :
    ∃ opened, Star (R := R) (openCode count code) opened ∧ Normal R opened := by
  obtain ⟨N, toN, normalN⟩ := reduct
  obtain ⟨opened, toOpened, normalOpened⟩ := opens_normal empty normalN count
  exact ⟨opened, (star_openCode toN count).trans toOpened, normalOpened⟩

end Raw

section Package

variable {Head : Type}

/-- **Strong normalization of a rule package**: every term typed in a formed context is strongly normalizing. This
is the property a package supplies for the normal reducts of the solver's opened sides. -/
def StronglyNormalizing (R : Rules Head) : Prop :=
  ∀ {n : Nat} {Γ : Ctx Head n} {t A : Tm Head n}, CtxFormed R Γ → Typed R Γ t A → StrongNormalization.SN R t

variable {L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L}

/-- Every typed term of a strongly normalizing package has a directed normal reduct. -/
theorem term_normal (sn : StronglyNormalizing S.R) {Θ : Context S.R} {type : TypeOver Θ} (term : Term Θ type) :
    ∃ N, Star (R := S.R) term.code N ∧ Normal S.R N :=
  exists_normal_of_sn (sn Θ.formed term.typed)

/-- **Every store has normal reducts of its opened sides**, in a strongly normalizing package without root
computation. -/
theorem openedNormal_of_sn (empty : S.R.computation = RootComputation.empty) (sn : StronglyNormalizing S.R)
    {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) : OpenedNormal problem := fun equation _ =>
  ⟨opens_normal_of_reduct empty (term_normal sn equation.1.2) _,
    opens_normal_of_reduct empty (term_normal sn equation.2.2) _⟩

/-- **On such a package the corrected class is the permuted Miller class.** -/
theorem permutedNormal_iff_permutedMiller (empty : S.R.computation = RootComputation.empty)
    (sn : StronglyNormalizing S.R) {Θ : Context S.R} {problem : EquationStore (TotalTerm Θ)} :
    PermutedNormal problem ↔ PermutedMiller S.levels problem :=
  ⟨fun held => held.1, fun permuted => ⟨permuted, openedNormal_of_sn empty sn problem⟩⟩

/-- **A round keeps a class of stores**: every progress of a store of the class lands in the class. -/
def RoundKeeps {rank : {Γ : Context S.R} → EquationStore (TotalTerm Γ) → Nat × Nat}
    (holds : {Γ : Context S.R} → EquationStore (TotalTerm Γ) → Prop)
    (round : ∀ {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)), Round S.levels rank problem) : Prop :=
  ∀ {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) (update : Update S.levels problem)
    (smaller : ContextualDependentWorklist.Below (rank update.remaining) (rank problem)),
    holds problem → round problem = .progress update smaller → holds update.remaining

variable (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R) (heads : HeadPreserving S.R)
  (algebra : CumulativeAlgebra S.R) (rigid : ∀ name, S.roles name = .rigid)
  (complete : AlgorithmicComplete S.R S.roles)

/-- `KeepsPermutedNormal` is keeping the class `PermutedNormal`. -/
theorem keepsPermutedNormal_iff_roundKeeps
    (round : ∀ {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)),
      Round S.levels (weightRank facts roots heads algebra rigid complete) problem) :
    KeepsPermutedNormal facts roots heads algebra rigid complete round ↔
      RoundKeeps (fun problem => PermutedNormal problem) round :=
  Iff.rfl

include rigid in
/-- **On a strongly normalizing package, a round keeps `PermutedNormal` exactly when it keeps `PermutedMiller`.** -/
theorem keepsPermutedNormal_iff (sn : StronglyNormalizing S.R)
    (round : ∀ {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)),
      Round S.levels (weightRank facts roots heads algebra rigid complete) problem) :
    KeepsPermutedNormal facts roots heads algebra rigid complete round ↔
      RoundKeeps (fun problem => PermutedMiller S.levels problem) round := by
  have same := fun {Γ : Context S.R} (problem : EquationStore (TotalTerm Γ)) =>
    permutedNormal_iff_permutedMiller (problem := problem) (computation_empty rigid) sn
  constructor
  · intro keeps Θ problem update smaller permuted fired
    exact (same _).mp (keeps problem update smaller ((same _).mpr permuted) fired)
  · intro keeps Θ problem update smaller held fired
    exact (same _).mpr (keeps problem update smaller ((same _).mp held) fired)

end Package

end ContextualDependentOpenedNormal
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
