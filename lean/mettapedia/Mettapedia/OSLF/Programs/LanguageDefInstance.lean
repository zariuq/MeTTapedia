import Mettapedia.OSLF.Programs.NativeType
import Mettapedia.OSLF.Programs.Completion
import Mettapedia.OSLF.Framework.TypeSynthesis

/-!
# Program native types in a `LanguageDef`

A four-constructor language: constants `a`, `b`, `c`, a unary `f`, and one
authored rewrite `a → b`.  It is equation-free, so its canonical GSLT
`langGSLT language` has syntactic equality as its equations and the authored
rewrite as its steps (`semanticStep_iff`, `equiv_iff`).

Program-level facts, all about the generated OSLF of the language:
* `a` can step into the native type of `b` (`a_diamond_b`); `b` and `c` cannot
  step (`b_normal`, `c_normal`).  In Hennessy–Milner terms, `a` satisfies
  `⟨⟩¬⟨⟩⊤` ("can step into a program that cannot step") and `b` does not
  (`a_steps_to_normal`, `b_not_steps_to_normal`).
* **Native types are finer than modal theories**: `b` and `c` satisfy the same
  step formulas (`b_c_same_modalTheory`) but have different native types
  (`b_c_different_nativeTypes`).
* **Context is not free**: the language authors no congruence, so `a` can
  step while `f a` cannot (`fa_normal`); the pullback of "can step" along the
  context `f [-]` fails at `a` (`step_not_lifted_by_context`).
* **Restriction gains a step-past formula**: in the fragment `{b}`, `b` has no
  predecessor, while in the whole language `a` precedes it
  (`restriction_box_gained`).
* **Holes are metavariables**: the partial program `f $x`, filled by MeTTaIL
  substitution (`contextF`), has no completion that can step
  (`contextF_never_steps`), a behaviour known before the hole is filled; the
  bare hole `$x` typed by the native type of `a` meets the goal "can step"
  (`holeA_meets_goal`), while the untyped bare hole does not
  (`hole_untyped_fails_goal`).
* **Extending the language is a translation that preserves steps and does not
  reflect them**: adding the rule `b → c` keeps every program's native type
  (`extension_directImage_nativeTypeOf`) and every old step
  (`extension_forth`), but `b` gains a step (`extension_not_back`), so the
  step-future modality is not preserved (`extension_diamond_not_natural`).
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Programs.TinyLanguage

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.OSLF.Framework.TypeSynthesis
open Mettapedia.OSLF.Framework.GSLTTypeSynthesis
open Mettapedia.GSLT.HennessyMilner
open Mettapedia.OSLF.MeTTaIL.Substitution
open Mettapedia.OSLF.Programs.Completion

/-- The one sort. -/
def sort : TypeDecl := TypeDecl.plain "T"

/-- Constructor `a`. -/
def ruleA : GrammarRule := { label := "a", category := "T", params := [], syntaxPattern := [] }

/-- Constructor `b`. -/
def ruleB : GrammarRule := { label := "b", category := "T", params := [], syntaxPattern := [] }

/-- Constructor `c`. -/
def ruleC : GrammarRule := { label := "c", category := "T", params := [], syntaxPattern := [] }

/-- Constructor `f`. -/
def ruleF : GrammarRule :=
  { label := "f", category := "T", params := [.simple "arg" (.base "T")], syntaxPattern := [] }

/-- The program `a`. -/
def termA : Pattern := .apply "a" []

/-- The program `b`. -/
def termB : Pattern := .apply "b" []

/-- The program `c`. -/
def termC : Pattern := .apply "c" []

/-- The context `f [-]` applied to a program. -/
def termF (argument : Pattern) : Pattern := .apply "f" [argument]

/-- The authored rewrite `a → b`. -/
def rewriteAB : RewriteRule :=
  { name := "ab", typeContext := [], premises := [], left := termA, right := termB }

/-- The language. -/
def language : LanguageDef :=
  { name := "programs-native-type-fixture"
    types := [sort]
    terms := [ruleA, ruleB, ruleC, ruleF]
    equations := []
    rewrites := [rewriteAB] }

theorem equationFree : language.isEquationFree = true := by
  decide

/-- The canonical GSLT of the language. -/
abbrev programs : Mettapedia.GSLT.GSLT := langGSLT language

theorem equiv_iff (P Q : programs.Term) : programs.Equiv P Q ↔ P = Q :=
  langGSLT_equiv_iff_eq_of_equation_free equationFree P Q

theorem semanticStep_iff (P Q : Pattern) : programs.Step P Q ↔ langReduces language P Q :=
  langSemanticReduces_iff_langReduces_of_equation_free equationFree P Q

/-- `a → b` is a step of the language. -/
theorem a_reduces_b : langReduces language termA termB := by
  refine ⟨1, .rule (rule := rewriteAB) (initialBindings := [])
    (finalBindings := []) ?_ ?_ ?_ ?_⟩
  · simp [language]
  · simp [rewriteAB, termA, matchPattern, matchArgs]
  · exact .nil []
  · change applyRuleBindings rewriteAB [] = termB
    rw [applyRuleBindings_eq_applyBindings _ _
      (ruleDepthAligned_of_binderFree _ (by decide) (by decide))]
    simp [rewriteAB, termB, applyBindings]

/-- A program that the rule `a → b` does not match has no step. -/
theorem no_step_of_no_match {P : Pattern}
    (noMatch : matchPatternForRule language rewriteAB P = []) (Q : Pattern) :
    ¬ langReduces language P Q := by
  apply not_step_of_matchPatternForRule_eq_nil
  intro rule member
  have ruleShape : rule = rewriteAB := by
    simpa [language] using member
  subst ruleShape
  exact noMatch

theorem b_normal (Q : Pattern) : ¬ langReduces language termB Q :=
  no_step_of_no_match (by
    simp [rewriteAB, termA, termB, matchPattern]) Q

theorem c_normal (Q : Pattern) : ¬ langReduces language termC Q :=
  no_step_of_no_match (by
    simp [rewriteAB, termA, termC, matchPattern]) Q

/-- **Context is not free**: `f a` has no step, although `a` has one. -/
theorem fa_normal (Q : Pattern) : ¬ langReduces language (termF termA) Q :=
  no_step_of_no_match (by
    simp [rewriteAB, termA, termF, matchPattern]) Q

/-! ## Native types of programs -/

/-- The native predicate that always holds. -/
def top : EquationPredicate programs := ⟨fun _ => True, fun _ _ _ => Iff.rfl⟩

/-- `a` can step into the native type of `b`. -/
theorem a_diamond_b : (semanticDiamond programs (nativeTypeOf programs termB)).1 termA :=
  (gsltDiamond_spec programs _ termA).mpr
    ⟨termB, (semanticStep_iff _ _).mpr a_reduces_b, nativeTypeOf_self (S := programs) termB⟩

/-- A program without steps satisfies no step-future formula. -/
theorem not_diamond_of_normal {P : Pattern} (normal : ∀ Q, ¬ langReduces language P Q)
    (φ : EquationPredicate programs) : ¬ (semanticDiamond programs φ).1 P := by
  intro holds
  obtain ⟨Q, step, _⟩ := (gsltDiamond_spec programs _ P).mp holds
  exact normal Q ((semanticStep_iff _ _).mp step)

/-- The step system of the language: no atoms, one label. -/
def stepSystem : System.{0, 0} programs where
  Atom := Empty
  observes := fun atom => atom.elim
  observes_resp := fun atom => atom.elim
  Label := Unit
  act _ := programs.Step
  act_resp_left := programs.rewrites_resp_left
  act_resp_right := programs.rewrites_resp_right

/-- `⟨⟩¬⟨⟩⊤`: can step into a program that cannot step. -/
def stepsToNormal : Formula stepSystem.Atom stepSystem.Label :=
  .dia () (.neg (.dia () .top))

/-- **`a` satisfies `⟨⟩¬⟨⟩⊤`.** -/
theorem a_steps_to_normal : stepSystem.sat stepsToNormal termA :=
  ⟨termB, (semanticStep_iff _ _).mpr a_reduces_b, fun ⟨Q, step, _⟩ =>
    b_normal Q ((semanticStep_iff _ _).mp step)⟩

/-- **`b` does not.** -/
theorem b_not_steps_to_normal : ¬ stepSystem.sat stepsToNormal termB :=
  fun ⟨Q, step, _⟩ => b_normal Q ((semanticStep_iff _ _).mp step)

/-- The modal theories of `a` and `b` differ. -/
theorem a_b_different_modalTheory : modalTheory stepSystem termA ≠ modalTheory stepSystem termB := by
  intro equal
  have member : stepsToNormal ∈ modalTheory stepSystem termA :=
    (mem_modalTheory stepSystem).mpr a_steps_to_normal
  rw [equal] at member
  exact b_not_steps_to_normal ((mem_modalTheory stepSystem).mp member)

/-- Two normal forms satisfy the same step formulas. -/
theorem sat_iff_of_normal {P Q : Pattern} (normalP : ∀ R, ¬ langReduces language P R)
    (normalQ : ∀ R, ¬ langReduces language Q R) :
    ∀ formula : Formula stepSystem.Atom stepSystem.Label,
      stepSystem.sat formula P ↔ stepSystem.sat formula Q
  | .top => Iff.rfl
  | .atom atom => atom.elim
  | .conj left right =>
      and_congr (sat_iff_of_normal normalP normalQ left) (sat_iff_of_normal normalP normalQ right)
  | .neg inner => not_congr (sat_iff_of_normal normalP normalQ inner)
  | .dia _ _ =>
      ⟨fun ⟨R, step, _⟩ => absurd ((semanticStep_iff _ _).mp step) (normalP R),
        fun ⟨R, step, _⟩ => absurd ((semanticStep_iff _ _).mp step) (normalQ R)⟩

/-- **`b` and `c` have the same modal theory.** -/
theorem b_c_same_modalTheory : modalTheory stepSystem termB = modalTheory stepSystem termC := by
  ext formula
  exact ((mem_modalTheory stepSystem).trans (sat_iff_of_normal b_normal c_normal formula)).trans
    (mem_modalTheory stepSystem).symm

/-- **`b` and `c` have different native types**: the native type is finer
than the modal theory. -/
theorem b_c_different_nativeTypes : programTheory programs termB ≠ programTheory programs termC := by
  intro equal
  have equal' : termB = termC := (equiv_iff termB termC).mp (programTheory_eq_iff.mp equal)
  exact absurd equal' (by decide)

/-- Plugging into the context `f [-]`, which respects the syntactic equations. -/
def plugF : EquationRespectingMap programs programs where
  toFun := termF
  map_equiv := by
    intro P Q equivalent
    exact (equiv_iff _ _).mpr (congrArg termF ((equiv_iff P Q).mp equivalent))

/-- **A step does not lift through a context the language does not
congruence-close**: `a` can step, while its pullback along `f [-]` cannot. -/
theorem step_not_lifted_by_context :
    (semanticDiamond programs top).1 termA ∧
      ¬ (plugF.pullback (semanticDiamond programs top)).1 termA :=
  ⟨(gsltDiamond_spec programs _ termA).mpr ⟨termB, (semanticStep_iff _ _).mpr a_reduces_b, trivial⟩,
    not_diamond_of_normal fa_normal top⟩

/-! ## Holes as metavariables -/

/-- The partial program `f $x`: its hole is the metavariable `x`, filled by
MeTTaIL substitution. -/
def contextF : PartialProgram programs Unit where
  plug σ := applySubst [("x", σ ())] (termF (.fvar "x"))
  plug_resp {σ τ} related := by
    have equal : σ () = τ () := (equiv_iff _ _).mp (related ())
    show programs.Equiv (applySubst [("x", σ ())] (termF (.fvar "x")))
      (applySubst [("x", τ ())] (termF (.fvar "x")))
    rw [equal]
    exact programs.equations.iseqv.refl _

theorem contextF_plug (σ : Unit → programs.Term) : contextF.plug σ = termF (σ ()) := by
  simp [contextF, applySubst, SubstEnv.find, termF]
  rfl

/-- `f P` has no step, whatever `P` is. -/
theorem f_normal (P Q : Pattern) : ¬ langReduces language (termF P) Q :=
  no_step_of_no_match (by simp [rewriteAB, termA, termF, matchPattern]) Q

/-- "Cannot step", as a native predicate. -/
def normal : EquationPredicate programs :=
  ⟨fun P => ¬ (semanticDiamond programs top).1 P, fun _ _ equivalent =>
    not_congr ((semanticDiamond programs top).2 equivalent)⟩

/-- **No completion of `f $x` can step**, whatever type the hole is given: the
obligation "cannot step" holds for every filling. -/
theorem contextF_never_steps (ψ : Unit → EquationPredicate programs) (t : Pattern)
    (member : (contextF.completionType ψ).1 t) : normal.1 t := by
  refine (contextF.completionType_implies_iff ψ normal).mpr ?_ t member
  intro σ _
  change ¬ (semanticDiamond programs top).1 (contextF.plug σ)
  rw [contextF_plug]
  exact not_diamond_of_normal (f_normal (σ ())) top

/-- The partial program `$x`: a bare hole. -/
def bareHole : PartialProgram programs Unit where
  plug σ := applySubst [("x", σ ())] (.fvar "x")
  plug_resp {σ τ} related := by
    have equal : σ () = τ () := (equiv_iff _ _).mp (related ())
    show programs.Equiv (applySubst [("x", σ ())] (.fvar "x")) (applySubst [("x", τ ())] (.fvar "x"))
    rw [equal]
    exact programs.equations.iseqv.refl _

theorem bareHole_plug (σ : Unit → programs.Term) : bareHole.plug σ = σ () := by
  simp [bareHole, applySubst, SubstEnv.find]

/-- "Can step", as a native predicate. -/
def canStep : EquationPredicate programs := semanticDiamond programs top

/-- **Positive**: typing the hole with the native type of `a` meets the goal
"can step". -/
theorem holeA_meets_goal (t : Pattern)
    (member : (bareHole.completionType fun _ => nativeTypeOf programs termA).1 t) :
    canStep.1 t := by
  refine (bareHole.completionType_implies_iff _ canStep).mpr ?_ t member
  intro σ typed
  change (semanticDiamond programs top).1 (bareHole.plug σ)
  rw [bareHole_plug]
  have isA : σ () = termA := (equiv_iff _ _).mp (nativeTypeOf_apply.mp (typed ()))
  rw [isA]
  exact (gsltDiamond_spec programs _ termA).mpr
    ⟨termB, (semanticStep_iff _ _).mpr a_reduces_b, trivial⟩

/-- **Negative**: with the hole untyped, the goal fails, since `b` fills it. -/
theorem hole_untyped_fails_goal :
    ¬ ∀ t, (bareHole.completionType fun _ => top).1 t → canStep.1 t := by
  intro meets
  have plugged : bareHole.plug (fun _ => termB) = termB := bareHole_plug _
  have member : (bareHole.completionType fun _ => top).1 termB :=
    (bareHole.completionType_apply _ _).mpr
      ⟨fun _ => termB, fun _ => trivial,
        Eq.subst (motive := fun x => programs.Equiv termB x) plugged.symm
          (programs.equations.iseqv.refl termB)⟩
  exact not_diamond_of_normal b_normal top (meets termB member)

/-! ## Restriction -/

/-- The fragment `{b}`: closed under the (syntactic) equations and under steps. -/
def fragmentB : Fragment programs where
  mem P := P = termB
  mem_equiv P Q equivalent member := by
    rw [← (equiv_iff P Q).mp equivalent]
    exact member
  mem_step P Q step member := by
    subst member
    exact absurd ((semanticStep_iff _ _).mp step) (b_normal Q)

/-- "Has no predecessor". -/
def noPredecessor (S : Mettapedia.GSLT.GSLT) : EquationPredicate S :=
  semanticBox S ⟨fun _ => False, fun _ _ _ => Iff.rfl⟩

/-- **Restriction gains a step-past formula**: in the fragment `{b}`, `b` has
no predecessor, while in the whole language `a` precedes it. -/
theorem restriction_box_gained :
    (noPredecessor fragmentB.gslt).1 ⟨termB, rfl⟩ ∧ ¬ (noPredecessor programs).1 termB := by
  refine ⟨(gsltBox_spec _ _ _).mpr fun Q step => ?_, fun holds => ?_⟩
  · have isB : Q.1 = termB := Q.2
    have step' : langReduces language Q.1 termB := (semanticStep_iff _ _).mp step
    rw [isB] at step'
    exact b_normal termB step'
  · exact (gsltBox_spec _ _ _).mp holds termA ((semanticStep_iff _ _).mpr a_reduces_b)

/-! ## Extending the language -/

/-- The authored rewrite `b → c`. -/
def rewriteBC : RewriteRule :=
  { name := "bc", typeContext := [], premises := [], left := termB, right := termC }

/-- The language extended by `b → c`. -/
def extendedLanguage : LanguageDef :=
  { language with
    name := "programs-native-type-fixture-extended"
    rewrites := [rewriteAB, rewriteBC] }

theorem extended_equationFree : extendedLanguage.isEquationFree = true := by
  decide

/-- The canonical GSLT of the extended language. -/
abbrev extendedPrograms : Mettapedia.GSLT.GSLT := langGSLT extendedLanguage

theorem extended_equiv_iff (P Q : extendedPrograms.Term) : extendedPrograms.Equiv P Q ↔ P = Q :=
  langGSLT_equiv_iff_eq_of_equation_free extended_equationFree P Q

theorem extended_semanticStep_iff (P Q : Pattern) :
    extendedPrograms.Step P Q ↔ langReduces extendedLanguage P Q :=
  langSemanticReduces_iff_langReduces_of_equation_free extended_equationFree P Q

/-- `b → c` is a step of the extended language. -/
theorem extended_b_reduces_c : langReduces extendedLanguage termB termC := by
  refine ⟨1, .rule (rule := rewriteBC) (initialBindings := [])
    (finalBindings := []) ?_ ?_ ?_ ?_⟩
  · simp [extendedLanguage]
  · simp [rewriteBC, termB, matchPattern, matchArgs]
  · exact .nil []
  · change applyRuleBindings rewriteBC [] = termC
    rw [applyRuleBindings_eq_applyBindings _ _
      (ruleDepthAligned_of_binderFree _ (by decide) (by decide))]
    simp [rewriteBC, termC, applyBindings]

/-- The extension, as a translation of programs: the identity on patterns. -/
def extension : EquationRespectingMap programs extendedPrograms where
  toFun P := P
  map_equiv {P Q} equivalent := (extended_equiv_iff P Q).mpr ((equiv_iff P Q).mp equivalent)

/-- The extension keeps the native type of every program. -/
theorem extension_directImage_nativeTypeOf (P Q : Pattern) :
    (extension.directImage (nativeTypeOf programs P)).1 Q ↔
      (nativeTypeOf extendedPrograms P).1 Q :=
  directImage_nativeTypeOf extension P Q

/-- **The extension preserves steps.** -/
theorem extension_forth : Forth extension := by
  intro P Q step
  apply (extended_semanticStep_iff P Q).mpr
  apply Step.mono_rules _ ((semanticStep_iff P Q).mp step)
  intro rule member
  simp only [language, List.mem_singleton] at member
  simp [extendedLanguage, member]

/-- **The extension does not reflect steps**: `b` gains the step `b → c`. -/
theorem extension_not_back : ¬ Back extension := by
  intro back
  obtain ⟨Q, step, _⟩ := back (P := termB) (Q' := termC)
    ((extended_semanticStep_iff _ _).mpr extended_b_reduces_c)
  exact b_normal Q ((semanticStep_iff _ _).mp step)

/-- The native predicate that always holds, in the extended language. -/
def extendedTop : EquationPredicate extendedPrograms := ⟨fun _ => True, fun _ _ _ => Iff.rfl⟩

/-- **Negative control**: after extending the language, `b` can step; before,
it cannot.  The step-future modality does not commute with the extension. -/
theorem extension_diamond_not_natural :
    (extension.pullback (semanticDiamond extendedPrograms extendedTop)).1 termB ∧
      ¬ (semanticDiamond programs (extension.pullback extendedTop)).1 termB :=
  ⟨(gsltDiamond_spec extendedPrograms _ termB).mpr
      ⟨termC, (extended_semanticStep_iff _ _).mpr extended_b_reduces_c, trivial⟩,
    not_diamond_of_normal b_normal _⟩

/-- The failure is exactly the failure of the back condition. -/
theorem extension_not_bounded : ¬ (Forth extension ∧ Back extension) :=
  fun bounded => extension_not_back bounded.2

end Mettapedia.OSLF.Programs.TinyLanguage
