import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Presentation.Controls

/-!
# The types the row formers generate, and the OSLF type system of the presentation

**Row formers.** Each row former of the presentation (`Sym`, `App`, `Name`, `Code`) is a constructor of the
language, so the generated logic has its structural former `built c [A₁, …, Aₙ]`: a term built by `c` from parts
of the types `Aᵢ`. A row is equal, modulo the equations, only to itself (`objectEquivalent_rowCode_iff`), so
`built` at a row reads the row's own constructor and arguments (`sat_built_rowCode_iff`, `sat_built_app_iff`).
With the bag's one-element former and its split, "some row of the store has type `A`" is generated
(`someRow`, `sat_someRow_iff`): for instance "some row is an application whose function is the constant `0`"
(`someApplication_example`).

**The OSLF type system.** The framework's `TypeSynthesis.langOSLFUsing` generates from the presentation an
`OSLFTypeSystem` at the sort `Store`, whose types are pairs of a sort and an equation-invariant predicate; its
diamond is the firing possibility (`oslf_diamond_iff`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Presentation

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine (RelationEnv)
open Mettapedia.OSLF.MeTTaIL.CanonicalBags (canon)
open Mettapedia.OSLF.NativeTypes.GeneratedLogic
  (Formula Formulas Env referenceStructure ObjectEquivalent GeneratedBy HasConstructor)
open Mettapedia.OSLF.Framework.TypeSynthesis (langOSLFUsing)
open NamesOnTheStep (Expr)
open NamesOnTheStep.IssuingControls (ground)
open LogicOverTheStep.ProgramAdequacy (program Supply)
open LogicOverTheStep.StepSpan (Succ)
open OneFrame (bodies)

universe uO

variable {R : Reading} {rules : List (Rule Rows)} {relEnv : RelationEnv}

/-! ## Row formers -/

/-- **A row is equal, modulo the equations of the generated logic, only to itself.** -/
theorem objectEquivalent_rowCode_iff (e : Expr) (q : Pattern) :
    ObjectEquivalent relEnv (presentWith R rules) .syntax (rowCode e) q ↔ q = rowCode e := by
  constructor
  · intro equivalent
    exact eq_of_same_rowCode e q
      (Mettapedia.OSLF.NativeTypes.GeneratedLogic.BagForms.canon_eq_of_equivalent presentWith_equations
        presentWith_noAlgebra equivalent)
  · rintro rfl
    exact Relation.EqvGen.refl _

/-- **The structural former at a row reads the row's own constructor and arguments.** -/
theorem sat_built_rowCode_iff (c : String) (arguments : Formulas 0) (e : Expr) :
    (referenceStructure relEnv (presentWith R rules)).sat Env.closed (.built c arguments) (rowCode e) ↔
      ∃ parts, rowCode e = .apply c parts ∧
        (referenceStructure relEnv (presentWith R rules)).satAll Env.closed arguments parts := by
  change (∃ parts, (Mettapedia.OSLF.NativeTypes.GeneratedLogic.IsObject (rowCode e) ∧
      ObjectEquivalent relEnv (presentWith R rules) .syntax (rowCode e) (.apply c parts)) ∧
      (referenceStructure relEnv (presentWith R rules)).satAll Env.closed arguments parts) ↔ _
  constructor
  · rintro ⟨parts, ⟨-, equivalent⟩, holds⟩
    exact ⟨parts, ((objectEquivalent_rowCode_iff e _).mp equivalent).symm, holds⟩
  · rintro ⟨parts, same, holds⟩
    exact ⟨parts, ⟨object_rowCode e, (objectEquivalent_rowCode_iff e _).mpr same.symm⟩, holds⟩

/-- **An application row has the type `App(A, B)` exactly when its parts have the types `A` and `B`.** -/
theorem sat_built_app_iff (A B : Formula 0) (f a : Expr) :
    (referenceStructure relEnv (presentWith R rules)).sat Env.closed (.built "App" (.cons A (.cons B .nil)))
        (rowCode (.app f a)) ↔
      (referenceStructure relEnv (presentWith R rules)).sat Env.closed A (rowCode f) ∧
        (referenceStructure relEnv (presentWith R rules)).sat Env.closed B (rowCode a) := by
  rw [sat_built_rowCode_iff]
  constructor
  · rintro ⟨parts, same, holds⟩
    have parts' : parts = [rowCode f, rowCode a] := (Pattern.apply.inj same).2.symm
    subst parts'
    exact ⟨holds.1, holds.2.1⟩
  · rintro ⟨holdsA, holdsB⟩
    exact ⟨[rowCode f, rowCode a], rfl, holdsA, holdsB, trivial⟩

/-- `App` is a constructor of the presented language, of arity two. -/
theorem app_constructor : HasConstructor (presentWith R rules) "App" 2 :=
  ⟨appFormer, presentWith_formers (.tail _ (.tail _ (.tail _ (.head _)))), rfl, rfl,
    not_bare_of_simple rfl⟩

/-! ## Rows of a store -/

/-- **Some row of the store has the type.** -/
def someRow (A : Formula 0) : Formula 0 := .split .hashBag (.single .hashBag A) .top

/-- The bag's one-element former at a store: the store has one row, of the type. -/
theorem sat_single_iff (A : Formula 0) (rows : List Expr) :
    (referenceStructure relEnv (presentWith R rules)).sat Env.closed (.single .hashBag A) (storeCode rows) ↔
      ∃ r, rows = [r] ∧ (referenceStructure relEnv (presentWith R rules)).sat Env.closed A (rowCode r) := by
  change (∃ member, (Mettapedia.OSLF.NativeTypes.GeneratedLogic.IsObject (storeCode rows) ∧
      ObjectEquivalent relEnv (presentWith R rules) .syntax (storeCode rows) (.collection .hashBag [member] none)) ∧
      (referenceStructure relEnv (presentWith R rules)).sat Env.closed A member) ↔ _
  constructor
  · rintro ⟨member, ⟨-, equivalent⟩, holds⟩
    obtain ⟨others, same, perm⟩ := storeCode_of_objectEquivalent equivalent
    have codes : [member] = others.map rowCode := (Pattern.collection.inj same).2.1
    obtain ⟨r, rfl, rfl⟩ : ∃ r, others = [r] ∧ member = rowCode r := by
      cases others with
      | nil => cases codes
      | cons r rest =>
          cases rest with
          | nil => exact ⟨r, rfl, (List.cons.inj codes).1⟩
          | cons _ _ => cases (List.cons.inj codes).2
    exact ⟨r, List.perm_singleton.mp perm, holds⟩
  · rintro ⟨r, rfl, holds⟩
    exact ⟨rowCode r, ⟨(isState_storeCode [r]).2, Relation.EqvGen.refl _⟩, holds⟩

/-- **Some row of the store has a type exactly when one of its rows has it.** -/
theorem sat_someRow_iff (A : Formula 0) (rows : List Expr) :
    (referenceStructure relEnv (presentWith R rules)).sat Env.closed (someRow A) (storeCode rows) ↔
      ∃ r ∈ rows, (referenceStructure relEnv (presentWith R rules)).sat Env.closed A (rowCode r) := by
  refine (sat_split_iff _ _ rows).trans ?_
  constructor
  · rintro ⟨left, right, perm, single, -⟩
    obtain ⟨r, rfl, holds⟩ := (sat_single_iff A left).mp single
    exact ⟨r, perm.subset (List.mem_append_left _ (List.mem_singleton_self r)), holds⟩
  · rintro ⟨r, member, holds⟩
    exact ⟨[r], rows.erase r, (List.perm_cons_erase member).symm, (sat_single_iff A [r]).mpr ⟨r, rfl, holds⟩,
      trivial⟩

/-- **Example**: the store `{(0 1), 5}` has a row that is an application whose function is the constant `0`. -/
theorem someApplication_example :
    (referenceStructure relEnv (presentWith R rules)).sat Env.closed
      (someRow (.built "App" (.cons (.is (rowCode (.sym 0))) (.cons .top .nil))))
      (storeCode [.app (.sym 0) (.sym 1), .sym 5]) := by
  refine (sat_someRow_iff _ _).mpr ⟨.app (.sym 0) (.sym 1), List.mem_cons_self, ?_⟩
  refine (sat_built_app_iff _ _ _ _).mpr ⟨⟨object_rowCode _, Relation.EqvGen.refl _⟩, trivial⟩

/-- **Control**: the store `{5}` has no application row. -/
theorem noApplication_example :
    ¬ (referenceStructure relEnv (presentWith R rules)).sat Env.closed
      (someRow (.built "App" (.cons .top (.cons .top .nil)))) (storeCode [.sym 5]) := by
  intro holds
  obtain ⟨r, member, built⟩ := (sat_someRow_iff _ _).mp holds
  rw [List.mem_singleton.mp member] at built
  obtain ⟨parts, same, -⟩ := (sat_built_rowCode_iff _ _ _).mp built
  exact absurd (Pattern.apply.inj same).1 (by decide)

/-! ## The OSLF type system of the presentation -/

variable {O : Type uO} [DecidableEq O] (label : O → Expr)

/-- **The OSLF type system the framework generates from the presentation, at the sort `Store`**: its diamond is the
firing possibility. Its types are pairs of a sort and an equation-invariant predicate. -/
theorem oslf_diamond_iff (supply : Supply label) (positive : ∀ r ∈ rules, Positive r)
    {C : Configuration Expr O} (knowledge : Trivial C.equations)
    (φ : (langOSLFUsing relEnv (present rules) "Store").Pred "Store") :
    (langOSLFUsing relEnv (present rules) "Store").satisfies (S := "Store") (storeOf label C)
        ((langOSLFUsing relEnv (present rules) "Store").diamond φ) ↔
      ∃ C', Succ (program ground label (bodies {r | r ∈ rules})) C C' ∧
        (langOSLFUsing relEnv (present rules) "Store").satisfies (S := "Store") (storeOf label C') φ :=
  generated_possibility_iff label supply positive knowledge φ

#print axioms objectEquivalent_rowCode_iff
#print axioms sat_built_rowCode_iff
#print axioms sat_built_app_iff
#print axioms app_constructor
#print axioms sat_single_iff
#print axioms sat_someRow_iff
#print axioms someApplication_example
#print axioms noApplication_example
#print axioms oslf_diamond_iff

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Presentation
