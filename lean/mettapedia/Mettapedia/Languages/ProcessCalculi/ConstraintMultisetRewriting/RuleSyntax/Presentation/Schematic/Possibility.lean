import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Presentation.Schematic.Firings

/-!
# Generated possibility is firing possibility, for programs with unknowns

**The theorem** (`generated_possibility`): for a program of the fragment (`RangeRestrictedPositive`:
no collect query, only equation checks, every unknown of a tell, a check or a made row bound by a take or read
pattern), at a ground state of `RuleSyntax.step` with trivial knowledge, the framework's generated
possibility (`langDiamondUsing`) of an equation-invariant property at the state's store holds exactly when
some admitted firing reaches a state that reads, through its knowledge, as a store with the property. No
premise asks the step: every premise is the framework's builtin equality (`Language.premisesOf`), and the
relation environment is only asked to add nothing to it (`noEq`). The comparison is with `RuleSyntax.step`
itself, not with the instance-set program, which shares a rule's unknowns with the caller
(`RuleSyntax.OneFrame.Controls.instanceSet_captures`).

## Existence (`Examples`)

The rule `pair` takes `(x x)` and makes the code of `x`: its unknown occurs twice.
* At the store holding `(1 1)` the generated possibility of "the store is the code of `1`" holds, and
  `RuleSyntax.step` has an admitted firing there whose result reads as that store (`pair_fires`).
* At the store holding `(1 2)` no generated possibility holds and no firing is admitted (`pair_refused`):
  the framework's matcher refuses the two occurrences of `x` at different rows, and the step's take
  equation `(x₁ x₁) = (1 2)` has no solution.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Presentation.Schematic

open Mettapedia.Logic.LP
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine (RelationEnv)
open Mettapedia.OSLF.Framework.TypeSynthesis (langDiamondUsing langGSLTUsing)
open Mettapedia.OSLF.Framework.GSLTTypeSynthesis (EquationPredicate saturatePredicate)
open Interface (Frames)
open NamesOnTheStep (Expr)

universe uO

variable {O : Type uO} [DecidableEq O] {rules : List SRule} {relEnv : RelationEnv}

omit [DecidableEq O] in
theorem coe_storeRows (s : SState O) (rows : O → Expr) :
    ((s.present.toList.map rows : List Expr) : Multiset Expr) = s.present.val.map rows := by
  rw [← Multiset.map_coe, Finset.coe_toList]

/-- **The generated possibility is the firing possibility of `RuleSyntax.step` with unknowns**: for a program
of the fragment, at the store of a ground state with trivial knowledge, the framework's derived possibility of
an equation-invariant property holds exactly when some admitted firing reaches a state that reads, through its
knowledge, as a store with the property. -/
theorem generated_possibility [Infinite O] (noEq : ∀ args, relEnv.tuples "eq" args = [])
    (fragment : ∀ r ∈ rules, RangeRestrictedPositive r) {s : SState O} {rows : O → Expr}
    (ground : GroundLabels s rows) (knowledge : TrivialKnowledge s.knowledge)
    (φ : EquationPredicate (langGSLTUsing relEnv (presentSchematic rules))) :
    (langDiamondUsing relEnv (presentSchematic rules) φ).1 (storeCode (s.present.toList.map rows)) ↔
      ∃ (g : Firing O E {r | r ∈ rules} s.frame) (admitted : (schematicStep O rules).Admits (s := s) g),
        ∃ next : List Expr, ReadsAs ((schematicStep O rules).result g admitted) next ∧ φ.1 (storeCode next) := by
  refine (diamond_storeCode_iff noEq fragment φ _).trans ?_
  constructor
  · rintro ⟨r, member, θ, rest, fires, holds⟩
    have split : (r.body.take.map (inst θ) : Multiset Expr) + rest = s.present.val.map rows := by
      rw [← coe_storeRows, Multiset.coe_add]
      exact Multiset.coe_eq_coe.mpr fires.takes
    obtain ⟨g, admitted, -, reads⟩ := admitted_of_match ground knowledge member (fragment r member) split
      (fun q inRead => Multiset.mem_coe.mpr (fires.reads q inRead)) fires.equations
    exact ⟨g, admitted, r.body.produce.map (inst θ) ++ rest, by rw [Multiset.coe_add] at reads; exact reads, holds⟩
  · rintro ⟨g, admitted, next, reads, holds⟩
    obtain ⟨θ, fires, readsResult⟩ := match_of_admitted ground fragment g admitted
    obtain ⟨-, -, -, solvable, -, -⟩ := (admits_iff g).mp admitted
    have same := readsAs_unique ((Frames.ofSubstitution_solvable_iff A _).mp solvable) reads readsResult
    refine ⟨g.rule, g.member, θ, _, fires, (φ.2 ?_).mp holds⟩
    refine equationEquiv_storeCode_of_perm presentSchematic_formers presentSchematic_store
      (Multiset.coe_eq_coe.mp ?_)
    rw [same, ← Multiset.coe_add, ← Multiset.map_coe rows (s.present \ g.selection.taken.toFinset).toList,
      Finset.coe_toList, add_comm]

#print axioms coe_storeRows
#print axioms generated_possibility

/-! ## Existence -/

namespace Examples

/-- The unknown `x`. -/
def x : Tm := .var 0

/-- A constant row. -/
def sym (k : ℕ) : Tm := .const (.sym k)

/-- An application. -/
def app (f a : Tm) : Tm := .app .app (args2 f a)

/-- A code. -/
def code (e : Tm) : Tm := .app .code (args1 e)

/-- **A rule whose unknown occurs twice**: take `(x x)`, make the code of `x`. -/
def pair : SRule := ⟨PUnit.unit, ⟨[app x x], [], [], [], [code x]⟩, []⟩

/-- The program of that rule. -/
def pairProgram : List SRule := [pair]

theorem x_bound : Bound pair 0 :=
  ⟨app x x, List.mem_cons_self, mem_vars_head (mem_vars_var.mpr rfl)⟩

theorem pair_fragment : ∀ r ∈ pairProgram, RangeRestrictedPositive r := by
  intro r member
  rw [List.mem_singleton.mp member]
  refine ⟨rfl, rfl, fun t inWritten y vars => ?_⟩
  have isCode : t = code x := by simpa [written, pair] using inWritten
  subst isCode
  rw [mem_vars_var.mp (mem_vars_code_cases vars)]
  exact x_bound

/-- The rows `(1 1)` and `(1 2)`. -/
def same : Expr := .app (.sym 1) (.sym 1)

/-- The rows `(1 2)`. -/
def different : Expr := .app (.sym 1) (.sym 2)

/-- One row at identity `0`. -/
def single (e : Expr) : SState ℕ := ⟨PUnit.unit, [], {0}, fun _ => toTerm e⟩

theorem single_ground (e : Expr) : GroundLabels (single e) (fun _ => e) := fun _ _ => rfl

theorem single_trivial (e : Expr) : TrivialKnowledge (single e).knowledge := fun _ member =>
  absurd member List.not_mem_nil

theorem single_store (e : Expr) : (single e).present.toList.map (fun _ => e) = [e] := by
  simp [single, Finset.toList_singleton]

/-- "The store is the code of `1`", closed under the equations. -/
def isCodeOne (relEnv : RelationEnv) : EquationPredicate (langGSLTUsing relEnv (presentSchematic pairProgram)) :=
  saturatePredicate _ fun p => p = storeCode [.code (.sym 1)]

/-- Every term. -/
def everything (relEnv : RelationEnv) : EquationPredicate (langGSLTUsing relEnv (presentSchematic pairProgram)) :=
  ⟨fun _ => True, fun _ _ _ => Iff.rfl⟩

theorem inst_pair (θ : ℕ → Expr) : inst θ (app x x) = .app (θ 0) (θ 0) := rfl

/-- **Existence, positive**: at `(1 1)` the generated possibility of "the store is the code of `1`" holds, and
`RuleSyntax.step` has an admitted firing there whose result reads as a store with that property. -/
theorem pair_fires (noEq : ∀ args, relEnv.tuples "eq" args = []) :
    (langDiamondUsing relEnv (presentSchematic pairProgram) (isCodeOne relEnv)).1 (storeCode [same]) ∧
      ∃ (g : Firing ℕ E {r | r ∈ pairProgram} (single same).frame)
        (admitted : (schematicStep ℕ pairProgram).Admits (s := single same) g),
        ∃ next : List Expr, ReadsAs ((schematicStep ℕ pairProgram).result g admitted) next ∧
          (isCodeOne relEnv).1 (storeCode next) := by
  have holds : (langDiamondUsing relEnv (presentSchematic pairProgram) (isCodeOne relEnv)).1 (storeCode [same]) :=
    (diamond_storeCode_iff noEq pair_fragment _ _).mpr ⟨pair, List.mem_singleton_self _, fun _ => .sym 1, [],
      ⟨List.Perm.refl _, fun _ member => absurd member List.not_mem_nil, fun _ member => absurd member
        List.not_mem_nil⟩, ⟨_, Relation.EqvGen.refl _, rfl⟩⟩
  refine ⟨holds, ?_⟩
  have atState := holds
  rw [← single_store same] at atState
  exact (generated_possibility noEq pair_fragment (single_ground same) (single_trivial same) _).mp atState

/-- **A firing by matching of `pair` at `(1 2)` is impossible**: the two occurrences of `x` meet different rows. -/
theorem pair_no_match {θ : ℕ → Expr} {rest : List Expr} (fires : MatchFires pair θ [different] rest) : False := by
  have restEmpty : rest = [] := by simpa [pair] using fires.takes.length_eq
  subst restEmpty
  have single := List.perm_singleton.mp fires.takes
  simp only [pair, List.map_cons, List.map_nil, List.append_nil, List.cons.injEq, and_true] at single
  rw [inst_pair] at single
  have parts := Expr.app.inj single
  rw [parts.1] at parts
  exact absurd (Expr.sym.inj parts.2) (by decide)

/-- **Existence, negative**: at `(1 2)` no generated possibility holds, and `RuleSyntax.step` admits no
firing. -/
theorem pair_refused (noEq : ∀ args, relEnv.tuples "eq" args = []) :
    ¬ (langDiamondUsing relEnv (presentSchematic pairProgram) (everything relEnv)).1 (storeCode [different]) ∧
      ¬ ∃ g : Firing ℕ E {r | r ∈ pairProgram} (single different).frame,
        (schematicStep ℕ pairProgram).Admits (s := single different) g := by
  refine ⟨fun possible => ?_, fun ⟨g, admitted⟩ => ?_⟩
  · obtain ⟨r, member, θ, rest, fires, -⟩ := (diamond_storeCode_iff noEq pair_fragment _ _).mp possible
    rw [List.mem_singleton.mp member] at fires
    exact pair_no_match fires
  · obtain ⟨θ, fires, -⟩ := match_of_admitted (single_ground different) pair_fragment g admitted
    have isPair : g.rule = pair := List.mem_singleton.mp g.member
    rw [isPair, single_store different] at fires
    exact pair_no_match fires

#print axioms pair_fragment
#print axioms pair_fires
#print axioms pair_no_match
#print axioms pair_refused

end Examples

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Presentation.Schematic
