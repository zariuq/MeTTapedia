import Mettapedia.GSLT.Dedukti.ConfluenceApplied

/-!
# Orthogonal theories: positive and negative examples

Positive: a rule whose right side binds (`withRule_orthogonal`), and a closed
transparent definition (`identity_orthogonal`).  The theories of the worked
translations are in `ConfluenceApplied`.

Negative: for six of the seven conditions of `Theory.Orthogonal`, a theory
that fails that condition and is not confluent.

| Condition | Theory | Two normal forms of one term |
|---|---|---|
| `closedBodies` | the definition `c := x` | `(λ y. c) a` reduces to `x` and to `a` |
| `leftAlgebraic` | `f (x y) ⟶ c` | `f ((λ z. z) a)` reduces to `c` and to `f a` |
| `rightDetermined` | `c ⟶ x` | `c` reduces to every term |
| `leftUndefined` | `c := a` and `c ⟶ b` | `c` reduces to `a` and to `b` |
| `rootUnique` | `choose x y ⟶ x`, `choose x y ⟶ y` | existing `withChoice_not_confluent` |
| `nonOverlapping` | `f (g x) ⟶ a`, `g x ⟶ b` | `f (g c)` reduces to `a` and to `f b` |

For the seventh, `leftLinear`, the rule `eq x x ⟶ t` fails the condition
(`equalRule_not_leftLinear`).  That this rule destroys confluence of the
untyped calculus is Klop's theorem; it is not proved here.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Dedukti.ConfluenceExamples

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.LF
open Mettapedia.GSLT.LanguageDef.LFTyping (Sig Decl lookupBody lift subst subst0)
open Mettapedia.GSLT.LanguageDef.LFContextualBetaEta (Context)
open Mettapedia.Logic.Relation (Confluent IsNormal)

variable {theory : Theory}

/-- A term with two reductions to distinct normal terms: reduction is not
confluent. -/
theorem not_confluent_of_fork {source left right : Term}
    (leftReduces : Reduces theory source left) (rightReduces : Reduces theory source right)
    (leftNormal : IsNormal (Step theory) left) (rightNormal : IsNormal (Step theory) right)
    (distinct : left ≠ right) : ¬ Confluent (Step theory) :=
  fun confluent => not_joinable_of_normal leftNormal rightNormal distinct
    (confluent source left right leftReduces rightReduces)

/-- An instance of a declared rule, with both sides computed. -/
theorem step_of_rule {rule : RewriteRule} (member : theory.rule rule) (assignment : Nat → Term)
    {source target : Term} (left : inst assignment rule.lhs = source)
    (right : inst assignment rule.rhs = target) : Step theory source target :=
  left ▸ right ▸ Step.root (.rule assignment member)

/-! ## Positive -/

/-- **A rule whose right side binds**: `P ⟶ Q → Q`. -/
theorem withRule_orthogonal : Example.withRule.Orthogonal :=
  orthogonal_of_check [Example.unfoldP] (fun _ member => member)
    (fun name => by
      show lookupBody Example.signature name = none
      simp [Example.signature, lookupBody])
    (by decide)

/-- A signature with one transparent definition: the identity on types. -/
def identitySig : Sig :=
  [.defn "I" (.pi (.srt .type) (.srt .type)) (.lam (.srt .type) (.var 0))]

/-- **A closed transparent definition.** -/
theorem identity_orthogonal : (Theory.ofSig identitySig []).Orthogonal :=
  ofSig_orthogonal fun name term defined => by
    have computed : lookupBody identitySig name =
        if name = "I" then some (.lam (.srt .type) (.var 0)) else none := by
      simp [identitySig, lookupBody]
    have found : lookupBody identitySig name = some term := defined
    rw [computed] at found
    split at found
    · obtain rfl := Option.some.inj found
      exact .lam .srt (.var (by omega))
    · cases found

/-! ## Negative: a definition that is not closed -/

/-- The definition `c := x`, with `x` a free variable. -/
def openDefinition : Theory where
  constType := fun _ => none
  body := fun name => if name = "c" then some (.var 0) else none
  rule := fun _ => False

theorem openDefinition_headed : openDefinition.Headed := fun _ member => member.elim

theorem openDefinition_not_closedBodies : ¬ openDefinition.ClosedBodies := by
  intro closed
  have wellScoped : Closed (.var 0) := closed "c" (.var 0) rfl
  cases wellScoped with
  | var bound => omega

/-- **With a definition that is not closed, reduction is not confluent.** -/
theorem openDefinition_not_confluent : ¬ Confluent (Step openDefinition) := by
  have unfold : RootStep openDefinition (.con "c") (.var 0) := .delta rfl
  refine not_confluent_of_fork (source := .app (.lam (.srt .type) (.con "c")) (.srt .kind))
    (left := .var 0) (right := .srt .kind) ?_ ?_ (var_normal openDefinition_headed 0)
    (srt_normal openDefinition_headed .kind) (by decide)
  · exact (Relation.ReflTransGen.single
      (Step.root (.beta (.srt .type) (.con "c") (.srt .kind)))).tail (Step.root unfold)
  · exact (Relation.ReflTransGen.single
      (Step.inContext (.appFunction (.lamBody (.srt .type) .hole) (.srt .kind)) unfold)).tail
      (Step.root (.beta (.srt .type) (.var 0) (.srt .kind)))

/-! ## Negative: a variable applied on the left -/

/-- `f (x y) ⟶ c`. -/
def appliedRule : RewriteRule := ⟨.app (.con "f") (.app (.var 1) (.var 0)), .con "c"⟩

def appliedVariable : Theory := Theory.ofSig [] [appliedRule]

def appliedCover : appliedVariable.Cover := Theory.coverOfRules [] [appliedRule] fun _ => rfl

theorem appliedVariable_not_leftAlgebraic : ¬ appliedVariable.LeftAlgebraic := by
  intro leftAlgebraic
  have headed := leftAlgebraic appliedRule (List.mem_singleton.mpr rfl)
  revert headed
  decide

/-- **With a variable applied on the left, reduction is not confluent**: a
beta step inside the instance destroys the match. -/
theorem appliedVariable_not_confluent : ¬ Confluent (Step appliedVariable) := by
  refine not_confluent_of_fork
    (source := .app (.con "f") (.app (.lam (.srt .type) (.var 0)) (.con "a")))
    (left := .con "c") (right := .app (.con "f") (.con "a")) ?_ ?_
    (normal_of_normalTest appliedCover _ (by decide))
    (normal_of_normalTest appliedCover _ (by decide)) (by decide)
  · exact .single (step_of_rule (rule := appliedRule) (List.mem_singleton.mpr rfl)
      (fun index => if index = 0 then .con "a" else .lam (.srt .type) (.var 0))
      (by decide) (by decide))
  · exact .single (Step.inContext (.appArgument (.con "f") .hole)
      (.beta (.srt .type) (.var 0) (.con "a")))

/-! ## Negative: a variable on the right that is not on the left -/

/-- `c ⟶ x`. -/
def freeRule : RewriteRule := ⟨.con "c", .var 0⟩

def freeVariable : Theory := Theory.ofSig [] [freeRule]

theorem freeVariable_headed : freeVariable.Headed := by
  intro rule member
  obtain rfl := List.mem_singleton.mp member
  exact ⟨"c", rfl⟩

/-- The right side is not determined by the variables of the left side. -/
theorem freeRule_not_rightDetermined :
    ¬ ∀ first second : Nat → Term,
      (∀ index ∈ patternVars freeRule.lhs, first index = second index) →
        inst first freeRule.rhs = inst second freeRule.rhs := by
  intro determined
  have same := determined (fun _ => .srt .type) (fun _ => .srt .kind) (by decide)
  revert same
  decide

/-- **With a variable on the right that is not on the left, reduction is not
confluent.** -/
theorem freeVariable_not_confluent : ¬ Confluent (Step freeVariable) := by
  refine not_confluent_of_fork (source := .con "c") (left := .srt .type) (right := .srt .kind)
    ?_ ?_ (srt_normal freeVariable_headed .type) (srt_normal freeVariable_headed .kind)
    (by decide)
  · exact .single (step_of_rule (rule := freeRule) (List.mem_singleton.mpr rfl)
      (fun _ => .srt .type) (by decide) (by decide))
  · exact .single (step_of_rule (rule := freeRule) (List.mem_singleton.mpr rfl)
      (fun _ => .srt .kind) (by decide) (by decide))

/-! ## Negative: a rule on a defined constant -/

/-- `c ⟶ b`. -/
def definedRule : RewriteRule := ⟨.con "c", .con "b"⟩

/-- The definition `c := a` together with the rule `c ⟶ b`. -/
def definedConstant : Theory where
  constType := fun _ => none
  body := fun name => if name = "c" then some (.con "a") else none
  rule := fun rule => rule ∈ [definedRule]

def definedCover : definedConstant.Cover where
  rigid := fun name => name != "c"
  rules := [definedRule]
  rigid_sound := fun name rigid => by
    have distinct : name ≠ "c" := by simpa using rigid
    simp [definedConstant, distinct]
  rules_sound := fun _ member => member

theorem definedConstant_not_leftUndefined :
    ¬ ∀ name, definedRule.lhs = .con name → definedConstant.body name = none := by
  intro undefined
  have absent := undefined "c" rfl
  revert absent
  decide

/-- **With a rule on a defined constant, reduction is not confluent.** -/
theorem definedConstant_not_confluent : ¬ Confluent (Step definedConstant) := by
  refine not_confluent_of_fork (source := .con "c") (left := .con "a") (right := .con "b")
    ?_ ?_ (normal_of_normalTest definedCover _ (by decide))
    (normal_of_normalTest definedCover _ (by decide)) (by decide)
  · exact .single (Step.root (.delta rfl))
  · exact .single (step_of_rule (rule := definedRule) (List.mem_singleton.mpr rfl)
      (fun _ => .srt .type) (by decide) (by decide))

/-! ## Negative: two rules for one left side -/

/-- **A theory with choice is not orthogonal.** -/
theorem withChoice_not_orthogonal (headed : theory.Headed) : ¬ (withChoice theory).Orthogonal :=
  fun orthogonal => withChoice_not_confluent headed (confluent_of_orthogonal orthogonal)

/-- The two rules of choice have one left side and are two rules. -/
theorem choice_not_rootUnique :
    ¬ ∀ left right : Nat → Term, inst left chooseLeft.lhs = inst right chooseRight.lhs →
      chooseLeft = chooseRight := by
  intro unique
  have same := unique (fun index => .var index) (fun index => .var index) rfl
  revert same
  decide

/-! ## Negative: a left side inside a left side -/

/-- `f (g x) ⟶ a`. -/
def outerRule : RewriteRule := ⟨.app (.con "f") (.app (.con "g") (.var 0)), .con "a"⟩

/-- `g x ⟶ b`. -/
def innerRule : RewriteRule := ⟨.app (.con "g") (.var 0), .con "b"⟩

def overlapping : Theory := Theory.ofSig [] [outerRule, innerRule]

def overlappingCover : overlapping.Cover :=
  Theory.coverOfRules [] [outerRule, innerRule] fun _ => rfl

/-- A proper part of the first left side is an instance of the second. -/
theorem overlapping_not_inert : ¬ Inert overlapping (.app (.con "g") (.var 0)) := by
  intro inert
  exact inert.unmatched innerRule (fun index => .var index) (fun index => .var index)
    (by simp [overlapping, Theory.ofSig]) rfl

/-- **With a left side inside a left side, reduction is not confluent.** -/
theorem overlapping_not_confluent : ¬ Confluent (Step overlapping) := by
  refine not_confluent_of_fork
    (source := .app (.con "f") (.app (.con "g") (.con "c")))
    (left := .con "a") (right := .app (.con "f") (.con "b")) ?_ ?_
    (normal_of_normalTest overlappingCover _ (by decide))
    (normal_of_normalTest overlappingCover _ (by decide)) (by decide)
  · exact .single (step_of_rule (rule := outerRule) (by simp [overlapping, Theory.ofSig])
      (fun _ => .con "c") (by decide) (by decide))
  · exact .single (Step.plug (.appArgument (.con "f") .hole)
      (step_of_rule (rule := innerRule) (by simp [overlapping, Theory.ofSig])
        (fun _ => .con "c") (by decide) (by decide)))

theorem overlapping_not_orthogonal : ¬ overlapping.Orthogonal :=
  fun orthogonal => overlapping_not_confluent (confluent_of_orthogonal orthogonal)

/-! ## Negative: a variable twice on the left -/

/-- `eq x x ⟶ t`. -/
def equalRule : RewriteRule := ⟨.app (.app (.con "eq") (.var 0)) (.var 0), .con "t"⟩

/-- The rule is not linear on the left. -/
theorem equalRule_not_leftLinear : ¬ (patternVars equalRule.lhs).Nodup := by
  decide

/-- A theory that declares it is not orthogonal. -/
theorem equal_not_orthogonal : ¬ (Theory.ofSig [] [equalRule]).Orthogonal :=
  fun orthogonal => equalRule_not_leftLinear
    (orthogonal.leftLinear equalRule (List.mem_singleton.mpr rfl))

/-- The test rejects each of the rule lists above. -/
theorem checks_fail :
    orthogonalCheck [appliedRule] = false ∧ orthogonalCheck [freeRule] = false ∧
      orthogonalCheck [chooseLeft, chooseRight] = false ∧
      orthogonalCheck [outerRule, innerRule] = false ∧ orthogonalCheck [equalRule] = false := by
  decide

#print axioms withRule_orthogonal
#print axioms identity_orthogonal
#print axioms openDefinition_not_confluent
#print axioms appliedVariable_not_confluent
#print axioms freeVariable_not_confluent
#print axioms definedConstant_not_confluent
#print axioms withChoice_not_orthogonal
#print axioms overlapping_not_confluent
#print axioms equal_not_orthogonal

end Mettapedia.GSLT.Dedukti.ConfluenceExamples
