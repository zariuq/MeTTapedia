import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ProgrammingOnTheStep.IndexedFamilies.ClosedCalls
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.TowerVectorsConversion

/-!
# Append with implicit lengths: the made row has the call's declared type

The program `VectorPrograms.appendFiring`, in the package with vectors and their eliminator
(`TowerVectorsModel.rules`). The state's frame holds the implicit lengths `m k : num` and the
arguments `xs : vec num m`, `ys : vec num k`; its knowledge says, heterogeneously,
`(xs : vec num m) ≐ (tt : vec num zero)` and `(ys : vec num k) ≐ ([2] : vec num 1)`. The call row is
`append num m k xs ys : vec num (add m k)`.

The base equation `append num zero p tt ys' = ys'`, with the fresh telescope
`p : num, ys' : vec num p`, fires on it (`append_admitted`): the solution sets `m ↦ 0`, `k ↦ 1`
(`append_solution_lengths`).

**The made row has the call's declared type.** The right side `ys'` is made at the left side's
type `vec num (add zero p)`, where it is typed because addition computes in conversion
(`result_typed`). At the solution this is the call's declared type `vec num (add 0 1)`
(`append_result_types`), and the rule's own type `vec num 1` is equal to it
(`rule_types_meet`). In a package that evaluates addition by firings the made row has the type
`vec 1`, which never meets the call's type (`VectorPrograms.append_result_types`,
`VectorPrograms.add_not_in_knowledge`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ProgrammingOnTheStep.IndexedFamilies

open _root_.CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.UniverseLevel
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta
open Interface.DependentFull

namespace ImplicitLengths

open TowerVectorsModel TowerVectorsPrograms TowerVectorsConversion
open TowerNumbersModel (u)
open Eliminator (level1 pkg pkgLevels D numType)
open ClosedCalls (one two single one_typed two_typed single_typed)

/-- `vec num t`, as a formed type over a frame. -/
def vecNum {Γ : Context pkg} (t : Tower.Tm Γ.arity) (typed : Typed pkg Γ.raw t numC) : TypeOver Γ :=
  ⟨vecC numC t, u, LevelTower.IsUniverse.sort _, D.vec_typed D.num_typed typed⟩

/-! ## The call, with its lengths implicit -/

abbrev ctxM : Context pkg := extend (empty pkg) (numType _)
abbrev ctxMK : Context pkg := extend ctxM (numType _)

/-- `xs : vec num m`. -/
def xsType : TypeOver ctxMK := vecNum (.var 1) (Derivable.var (1 : Fin 2))

abbrev ctxMKX : Context pkg := extend ctxMK xsType

/-- `ys : vec num k`. -/
def ysType : TypeOver ctxMKX := vecNum (.var 1) (Derivable.var (1 : Fin 3))

/-- **The frame of the call**: `m k : num, xs : vec num m, ys : vec num k`. -/
abbrev frame0 : Context pkg := extend ctxMKX ysType

def xsRow : TotalTerm frame0 :=
  ⟨vecNum (.var 3) (Derivable.var (3 : Fin 4)), ⟨.var 1, Derivable.var (1 : Fin 4)⟩⟩

def ysRow : TotalTerm frame0 :=
  ⟨vecNum (.var 2) (Derivable.var (2 : Fin 4)), ⟨.var 0, Derivable.var (0 : Fin 4)⟩⟩

/-- `tt : vec num zero`. -/
def nilRow : TotalTerm frame0 := ⟨vecNum zeroC D.zero_typed, ⟨ttC, D.nil_typed D.num_typed⟩⟩

/-- `[2] : vec num 1`. -/
def oneVecRow : TotalTerm frame0 :=
  ⟨vecNum one (one_typed _), ⟨single two, single_typed (two_typed _)⟩⟩

theorem call_typed :
    Typed pkg frame0.raw (appendTm numC (.var 3) (.var 2) (.var 1) (.var 0))
      (vecC numC (addC (.var 3) (.var 2))) := by
  have tm : Typed pkg frame0.raw (.var 3) numC := Derivable.var (3 : Fin 4)
  have tk : Typed pkg frame0.raw (.var 2) numC := Derivable.var (2 : Fin 4)
  have txs : Typed pkg frame0.raw (.var 1) (vecC numC (.var 3)) := Derivable.var (1 : Fin 4)
  have tys : Typed pkg frame0.raw (.var 0) (vecC numC (.var 2)) := Derivable.var (0 : Fin 4)
  have m₀ : SubstMor pkg .nil frame0.raw fun i => Fin.elim0 i := fun i => Fin.elim0 i
  have mor : SubstMor pkg appendCtx frame0.raw
      (consSub (.var 0) (consSub (.var 1) (consSub (.var 2) (consSub (.var 3) (consSub numC
        fun i => Fin.elim0 i))))) :=
    SubstMor.cons (SubstMor.cons (SubstMor.cons (SubstMor.cons (SubstMor.cons m₀ D.num_typed) tm) tk)
      txs) tys
  exact (append_typed level1).substitute mor

/-- **The call** `append num m k xs ys : vec num (add m k)`. -/
def callRow : TotalTerm frame0 :=
  ⟨vecNum (addC (.var 3) (.var 2))
      (add_typed level1 (Derivable.var (3 : Fin 4)) (Derivable.var (2 : Fin 4))),
    ⟨appendTm numC (.var 3) (.var 2) (.var 1) (.var 0), call_typed⟩⟩

/-- **The state of the call**: the lengths are unknowns; the knowledge relates the arguments to
their values, heterogeneously. -/
def callState : State pkg Nat :=
  ⟨frame0, [(xsRow, nilRow), (ysRow, oneVecRow)], {0}, fun _ => callRow⟩

/-! ## The base equation, with its fresh telescope -/

/-- `ys' : vec num p`, over the call's frame extended by `p : num`. -/
def ysPrimeType : TypeOver (extend frame0 (numType _)) := vecNum (.var 0) (Derivable.var (0 : Fin 5))

/-- The rule's frame: the call's frame, `p : num`, `ys' : vec num p`. -/
abbrev appendFrame : Context pkg := extend (extend frame0 (numType _)) ysPrimeType

theorem pattern_typed :
    Typed pkg appendFrame.raw (appendTm numC zeroC (.var 1) ttC (.var 0))
      (vecC numC (addC zeroC (.var 1))) := by
  have tp : Typed pkg appendFrame.raw (.var 1) numC := Derivable.var (1 : Fin 6)
  have tys : Typed pkg appendFrame.raw (.var 0) (vecC numC (.var 1)) := Derivable.var (0 : Fin 6)
  have m₀ : SubstMor pkg .nil appendFrame.raw fun i => Fin.elim0 i := fun i => Fin.elim0 i
  have mor : SubstMor pkg appendCtx appendFrame.raw
      (consSub (.var 0) (consSub ttC (consSub (.var 1) (consSub zeroC (consSub numC
        fun i => Fin.elim0 i))))) :=
    SubstMor.cons (SubstMor.cons (SubstMor.cons (SubstMor.cons (SubstMor.cons m₀ D.num_typed)
      D.zero_typed) tp) (D.nil_typed D.num_typed)) tys
  exact (append_typed level1).substitute mor

/-- The left side's type `vec num (add zero p)`. -/
def patternType : TypeOver appendFrame :=
  vecNum (addC zeroC (.var 1)) (add_typed level1 D.zero_typed (Derivable.var (1 : Fin 6)))

/-- The left side `append num zero p tt ys' : vec num (add zero p)` of the rule. -/
def appendPattern : TotalTerm appendFrame :=
  ⟨patternType, ⟨appendTm numC zeroC (.var 1) ttC (.var 0), pattern_typed⟩⟩

/-- The two types of the rule are equal: `vec num (add zero p) ≡ vec num p`. -/
theorem rule_types : TypeEq pkg appendFrame.raw (vecC numC (addC zeroC (.var 1))) (vecC numC (.var 1)) :=
  vec_left_zero_meets D.num_typed (Derivable.var (1 : Fin 6))

/-- **The right side at the left side's type**: `ys' : vec num (add zero p)`, by conversion. -/
theorem result_typed : Typed pkg appendFrame.raw (.var 0) (vecC numC (addC zeroC (.var 1))) :=
  Typed.convType (Derivable.var (0 : Fin 6)) rule_types.symm

/-- The right side `ys'`, at its own type `vec num p`. -/
def resultRow : TotalTerm appendFrame :=
  ⟨vecNum (.var 1) (Derivable.var (1 : Fin 6)), ⟨.var 0, Derivable.var (0 : Fin 6)⟩⟩

/-- **The two sides of the rule are equal in the knowledge**, at their two types. -/
theorem pattern_meets_result : (frames pkgLevels).E appendPattern resultRow := by
  have tp : Typed pkg appendFrame.raw (.var 1) numC := Derivable.var (1 : Fin 6)
  have tys : Typed pkg appendFrame.raw (.var 0) (vecC numC (.var 1)) := Derivable.var (0 : Fin 6)
  have m₀ : SubstMor pkg .nil appendFrame.raw fun i => Fin.elim0 i := fun i => Fin.elim0 i
  have mor : SubstMor pkg nilCtx appendFrame.raw
      (consSub (.var 0) (consSub (.var 1) (consSub numC fun i => Fin.elim0 i))) :=
    SubstMor.cons (SubstMor.cons (SubstMor.cons m₀ D.num_typed) tp) tys
  exact (equivalent_iff pkgLevels _ _).mpr ⟨rule_types, (append_nil level1).substitute mor⟩

/-- **The rule `append num zero p tt ys' = ys'`, firing on the call**: it makes the right side at
the left side's type, and tells that the two sides are equal. -/
def appendFiring : Firing pkgLevels callState where
  helpers := .cons (numType _) (.cons ysPrimeType (.nil _))
  taken := [0]
  read := []
  takes := [appendPattern]
  reads := []
  makes := [(1, ⟨patternType, (.var 0 : Tower.Tm 6)⟩)]
  tells := [(appendPattern, resultRow)]
  guards := []
  queries := []

/-- The solution `m ↦ 0, k ↦ 1, xs ↦ tt, ys ↦ [2], p ↦ 1, ys' ↦ [2]`, closed. -/
def appendSolution : empty pkg ⟶ appendFrame :=
  pair (pair (pair (pair (pair (pair (toEmpty (empty pkg)) ⟨zeroC, D.zero_typed⟩) ⟨one, one_typed _⟩)
    ⟨ttC, D.nil_typed D.num_typed⟩) ⟨single two, single_typed (two_typed _)⟩) ⟨one, one_typed _⟩)
    ⟨single two, single_typed (two_typed _)⟩

theorem appendFiring_information :
    appendFiring.information =
      [((frames pkgLevels).act appendFiring.helpers.weaken xsRow,
          (frames pkgLevels).act appendFiring.helpers.weaken nilRow),
       ((frames pkgLevels).act appendFiring.helpers.weaken ysRow,
          (frames pkgLevels).act appendFiring.helpers.weaken oneVecRow),
       (appendPattern, appendFiring.row 0), (appendPattern, resultRow)] := rfl

theorem append_xs :
    ((frames pkgLevels).act appendFiring.helpers.weaken xsRow).reindex appendSolution =
      ((frames pkgLevels).act appendFiring.helpers.weaken nilRow).reindex appendSolution :=
  totalTerm_ext (TypeOver.ext rfl rfl) rfl

theorem append_ys :
    ((frames pkgLevels).act appendFiring.helpers.weaken ysRow).reindex appendSolution =
      ((frames pkgLevels).act appendFiring.helpers.weaken oneVecRow).reindex appendSolution :=
  totalTerm_ext (TypeOver.ext rfl rfl) rfl

/-- At the solution, the left side is the call. -/
theorem append_identifies :
    appendPattern.reindex appendSolution = (appendFiring.row 0).reindex appendSolution :=
  totalTerm_ext (TypeOver.ext rfl rfl) rfl

/-- **The rule fires on the call with implicit lengths.** -/
theorem append_admitted : (step pkgLevels Nat).Admits appendFiring := by
  refine ⟨⟨List.nodup_singleton _, List.nodup_singleton _, rfl, rfl, fun m member => ?_⟩,
    (enabled_iff appendFiring).mpr ⟨fun o member => ?_, fun _ member => absurd member List.not_mem_nil,
      fun _ _ readToo => absurd readToo List.not_mem_nil, fun o member inside => ?_⟩,
    ⟨empty pkg, appendSolution, ?_⟩, ?_⟩
  · obtain rfl := List.mem_singleton.mp member
    exact result_typed
  · obtain rfl := List.mem_singleton.mp member
    exact Finset.mem_singleton_self 0
  · obtain rfl := List.mem_singleton.mp member
    exact absurd (Finset.mem_singleton.mp inside) (by decide)
  · rw [appendFiring_information]
    intro e member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl
    · show (frames pkgLevels).E
        (((frames pkgLevels).act appendFiring.helpers.weaken xsRow).reindex appendSolution)
        (((frames pkgLevels).act appendFiring.helpers.weaken nilRow).reindex appendSolution)
      rw [append_xs]
      exact ((frames pkgLevels).equivalence _).refl _
    · show (frames pkgLevels).E
        (((frames pkgLevels).act appendFiring.helpers.weaken ysRow).reindex appendSolution)
        (((frames pkgLevels).act appendFiring.helpers.weaken oneVecRow).reindex appendSolution)
      rw [append_ys]
      exact ((frames pkgLevels).equivalence _).refl _
    · show (frames pkgLevels).E (appendPattern.reindex appendSolution)
        ((appendFiring.row 0).reindex appendSolution)
      rw [append_identifies]
      exact ((frames pkgLevels).equivalence _).refl _
    · exact (frames pkgLevels).preserves appendSolution pattern_meets_result
  · intro b τ _
    exact ⟨fun _ member => absurd member List.not_mem_nil, fun _ member => absurd member List.not_mem_nil⟩

/-- **The implicit lengths**: the solution sets `m ↦ 0` and `k ↦ 1`. -/
theorem append_solution_lengths :
    appendSolution.substitution 5 = zeroC ∧ appendSolution.substitution 4 = one := ⟨rfl, rfl⟩

/-- **The made row has the call's declared type**: at the solution both are `vec num (add 0 1)`,
and the made row is `[2]`. -/
theorem append_result_types :
    subst appendSolution.substitution
        (((step pkgLevels Nat).result appendFiring append_admitted).label 1).1.code =
        vecC numC (addC zeroC one) ∧
      subst appendSolution.substitution (appendFiring.row 0).1.code = vecC numC (addC zeroC one) ∧
      subst appendSolution.substitution
        (((step pkgLevels Nat).result appendFiring append_admitted).label 1).2.code = single two :=
  ⟨rfl, rfl, rfl⟩

/-- **The rule's own type meets the call's declared type**: `vec num 1 ≡ vec num (add 0 1)`. -/
theorem rule_types_meet : TypeEq pkg .nil (vecC numC one) (vecC numC (addC zeroC one)) :=
  (vec_left_zero_meets D.num_typed (one_typed _)).symm

end ImplicitLengths

end ProgrammingOnTheStep.IndexedFamilies

#print axioms ProgrammingOnTheStep.IndexedFamilies.ImplicitLengths.result_typed
#print axioms ProgrammingOnTheStep.IndexedFamilies.ImplicitLengths.pattern_meets_result
#print axioms ProgrammingOnTheStep.IndexedFamilies.ImplicitLengths.append_admitted
#print axioms ProgrammingOnTheStep.IndexedFamilies.ImplicitLengths.append_solution_lengths
#print axioms ProgrammingOnTheStep.IndexedFamilies.ImplicitLengths.append_result_types
#print axioms ProgrammingOnTheStep.IndexedFamilies.ImplicitLengths.rule_types_meet

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
