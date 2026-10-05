import Mettapedia.Logic.LP.FirstOrderRewriting
import Mettapedia.Logic.LP.UnificationMGU

/-!
# Narrowing, rewriting, and paramodulation

A rule is an equation used from left to right. Narrowing applies it where a
non-variable subterm unifies with the left side, and the unifier may instantiate
the query. Rewriting is the narrowing step whose substitution leaves the query
unchanged. Paramodulation is that replacement inside one unit equation, and the
rule may be used in either direction.

The rule is given already renamed apart from the query. The step does not choose
a fresh variable: an arbitrary variable type need not have one.

Positive example, `Fork`: rules `a ⟶ b` and `a ⟶ c`. Paramodulation derives
`b = c`, and that equation holds in every model of the rules. No narrowing or
rewriting sequence leads from `b` to `c` or from `c` to `b`. The query `a`
reaches two terms with no further step, `b` and `c`.

Negative example, `Growth`: the rule `f x ⟶ f (g x)`. Rewriting from `f x`
never stops, and no well-founded order compatible with contexts and
substitutions decreases along that direction. The same equation from right to
left always stops.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.LP.Narrowing

open Mettapedia.Logic.LP
open Mettapedia.Logic.LP.FirstOrderRewriting
open Mettapedia.Logic.LP.FirstOrderBridge

section

variable {σ : LPSignature} [DecidableEq σ.vars]

omit [DecidableEq σ.vars] in
/-- The context with the substitution applied to every term outside the hole. -/
def mapContext (substitution : Subst σ) : Context σ → Context σ
  | .hole => .hole
  | .app symbol arguments position inner =>
      .app symbol (fun i => substitution.applyTerm (arguments i)) position
        (mapContext substitution inner)

omit [DecidableEq σ.vars] in
/-- Applying a substitution commutes with filling the hole. -/
theorem mapContext_fill (substitution : Subst σ) (context : Context σ) (term : Term σ) :
    substitution.applyTerm (context.fill term) =
      (mapContext substitution context).fill (substitution.applyTerm term) := by
  induction context with
  | hole => rfl
  | app symbol arguments position inner ih =>
      simp only [Context.fill, mapContext, Subst.applyTerm_app]
      congr 1
      funext i
      by_cases same : i = position
      · subst same
        simp only [Function.update_self]
        exact ih
      · simp only [Function.update_of_ne same]

/-- Variables of a context that are not the hole. -/
def outsideVars : Context σ → Finset σ.vars
  | .hole => ∅
  | .app _ arguments position inner =>
      (Finset.univ.filter fun i => i ≠ position).biUnion (fun i => (arguments i).freeVars) ∪
        outsideVars inner

/-- Substitutions that agree on the variables of a term agree on the term. -/
theorem Subst.applyTerm_congr {substitution other : Subst σ} {term : Term σ}
    (agree : ∀ v ∈ term.freeVars, substitution v = other v) :
    substitution.applyTerm term = other.applyTerm term := by
  induction term with
  | var v => exact agree v (by simp [Term.freeVars])
  | const _ => rfl
  | app _ arguments ih =>
      simp only [Subst.applyTerm_app]
      congr 1
      funext i
      exact ih i fun v member => agree v (by
        simp only [Term.freeVars, Finset.mem_biUnion, Finset.mem_univ, true_and]
        exact ⟨i, member⟩)

/-- A substitution that fixes every variable of a term fixes the term. -/
theorem Subst.applyTerm_id_of_fixed {term : Term σ} {substitution : Subst σ}
    (fixed : ∀ v ∈ term.freeVars, substitution v = .var v) :
    substitution.applyTerm term = term := by
  have : substitution.applyTerm term = (Subst.id σ).applyTerm term :=
    Subst.applyTerm_congr fixed
  simpa [Subst.applyTerm_id] using this

/-- The variables of the hole occur in the filled term. -/
theorem freeVars_hole_subset (context : Context σ) (hole : Term σ) :
    hole.freeVars ⊆ (context.fill hole).freeVars := by
  induction context with
  | hole => exact Finset.Subset.refl _
  | app _ _ position inner ih =>
      intro v member
      simp only [Context.fill, Term.freeVars, Finset.mem_biUnion, Finset.mem_univ, true_and]
      exact ⟨position, by simpa [Function.update_self] using ih member⟩

/-- A variable outside the hole occurs in every filling of the context. -/
theorem outsideVars_subset_fill (context : Context σ) (hole : Term σ) :
    outsideVars context ⊆ (context.fill hole).freeVars := by
  induction context with
  | hole =>
      simp [outsideVars]
  | app _ arguments position inner ih =>
      intro v member
      simp only [outsideVars, Finset.mem_union] at member
      simp only [Context.fill, Term.freeVars, Finset.mem_biUnion, Finset.mem_univ, true_and]
      rcases member with member | member
      · obtain ⟨i, kept, occurs⟩ := Finset.mem_biUnion.mp member
        have different : i ≠ position := by simpa using kept
        exact ⟨i, by simpa [Function.update_of_ne different] using occurs⟩
      · exact ⟨position, by simpa [Function.update_self] using ih member⟩

/-- Filling after a substitution that fixes the context outside the hole. -/
theorem fill_fixed_outside (context : Context σ) (hole : Term σ) (substitution : Subst σ)
    (fixed : ∀ v ∈ outsideVars context, substitution v = .var v) :
    substitution.applyTerm (context.fill hole) = context.fill (substitution.applyTerm hole) := by
  induction context with
  | hole => rfl
  | app _ arguments position inner ih =>
      simp only [Context.fill, Subst.applyTerm_app]
      congr 1
      funext i
      by_cases same : i = position
      · subst same
        simp only [Function.update_self]
        apply ih
        intro v member
        apply fixed
        simp only [outsideVars, Finset.mem_union]
        exact Or.inr member
      · simp only [Function.update_of_ne same]
        apply Subst.applyTerm_id_of_fixed
        intro v member
        apply fixed
        simp only [outsideVars, Finset.mem_union, Finset.mem_biUnion,
          Finset.mem_filter, Finset.mem_univ, true_and]
        exact Or.inl ⟨i, same, member⟩

/-- The substitution that keeps `domain` and is the identity outside it. -/
def Subst.keep (domain : Finset σ.vars) (substitution : Subst σ) : Subst σ :=
  fun v => if v ∈ domain then substitution v else .var v

/-- The two sides of a rule share no variable with the term. -/
def apart (equation : Equation σ) (term : Term σ) : Prop :=
  ∀ v ∈ equation.left.freeVars ∪ equation.right.freeVars, v ∉ term.freeVars

omit [DecidableEq σ.vars] in
/-- A unifier more general than every unifier of the two terms. -/
def MostGeneralUnifier (substitution : Subst σ) (left right : Term σ) : Prop :=
  substitution.applyTerm left = substitution.applyTerm right ∧
    ∀ other : Subst σ, other.applyTerm left = other.applyTerm right →
      substitution.moreGeneral other

omit [DecidableEq σ.vars] in
/-- A variable redex comes from a rule whose left side is a variable. -/
theorem variable_redex_left {substitution : Subst σ} {left : Term σ} {v : σ.vars}
    (redex : substitution.applyTerm left = .var v) : ∃ w, left = .var w := by
  cases left with
  | var w => exact ⟨w, rfl⟩
  | const _ =>
      simp only [Subst.applyTerm_const] at redex
      cases redex
  | app _ _ =>
      simp only [Subst.applyTerm_app] at redex
      cases redex

/-- One narrowing step: a renamed-apart rule, a non-variable subterm, and any unifier. -/
inductive Narrow (rules : Set (Equation σ)) : Term σ → Subst σ → Term σ → Prop where
  | step {source target : Term σ} {substitution : Subst σ}
      (equation : Equation σ) (member : equation ∈ rules)
      (context : Context σ) (subterm : Term σ)
      (notVariable : ∀ v, subterm ≠ Term.var v)
      (atSubterm : source = context.fill subterm)
      (unifies : substitution.applyTerm equation.left = substitution.applyTerm subterm)
      (apart : apart equation source)
      (result : target = substitution.applyTerm (context.fill equation.right)) :
      Narrow rules source substitution target

/-- A narrowing sequence and the substitution composed along it. -/
inductive Narrows (rules : Set (Equation σ)) : Term σ → Subst σ → Term σ → Prop where
  | refl (term : Term σ) : Narrows rules term (Subst.id σ) term
  | step {source middle target : Term σ} {earlier later : Subst σ}
      (before : Narrows rules source earlier middle)
      (one : Narrow rules middle later target) :
      Narrows rules source (later ∘ₛ earlier) target

/-- `unifyTerms` returns a most general narrowing step when the rule is renamed apart. -/
theorem narrow_of_unifyTerms {rules : Set (Equation σ)}
    [DecidableEq σ.constants] [DecidableEq σ.functionSymbols]
    {equation : Equation σ} (member : equation ∈ rules)
    {context : Context σ} {subterm source : Term σ}
    (notVariable : ∀ v, subterm ≠ Term.var v)
    (atSubterm : source = context.fill subterm)
    (apart : apart equation source)
    {fuel : ℕ} {substitution : Subst σ}
    (found : unifyTerms equation.left subterm fuel = some substitution) :
    Narrow rules source substitution
      (substitution.applyTerm (context.fill equation.right)) ∧
      MostGeneralUnifier substitution equation.left subterm := by
  refine ⟨Narrow.step equation member context subterm notVariable atSubterm ?_ apart rfl, ?_⟩
  · exact unifyTerms_sound equation.left subterm fuel substitution found
  · refine ⟨unifyTerms_sound equation.left subterm fuel substitution found, ?_⟩
    intro other unifies
    exact unifyTerms_mgu equation.left subterm fuel substitution found other unifies

/-- A narrowing step is one rewrite of the instantiated query. -/
theorem narrow_sound {rules : Set (Equation σ)} {source : Term σ} {substitution : Subst σ}
    {target : Term σ} (step : Narrow rules source substitution target) :
    Rewrite rules (substitution.applyTerm source) target := by
  cases step with
  | step equation member context subterm _ atSubterm unifies _ result =>
      subst atSubterm
      subst result
      have left : substitution.applyTerm (context.fill subterm) =
          (mapContext substitution context).fill (substitution.applyTerm equation.left) := by
        rw [mapContext_fill, unifies]
      have right : substitution.applyTerm (context.fill equation.right) =
          (mapContext substitution context).fill (substitution.applyTerm equation.right) :=
        mapContext_fill substitution context equation.right
      rw [left, right]
      exact Rewrite.rule equation member substitution (mapContext substitution context)

omit [DecidableEq σ.vars] in
/-- Instantiating a rewrite step gives a rewrite step. -/
theorem rewrite_subst {rules : Set (Equation σ)} {left right : Term σ}
    (step : Rewrite rules left right) (substitution : Subst σ) :
    Rewrite rules (substitution.applyTerm left) (substitution.applyTerm right) := by
  cases step with
  | rule equation member earlier context =>
      simp only [mapContext_fill, ← Subst.applyTerm_comp]
      exact Rewrite.rule equation member (substitution ∘ₛ earlier) (mapContext substitution context)

omit [DecidableEq σ.vars] in
/-- Instantiating a rewriting sequence gives a rewriting sequence. -/
theorem rewrites_subst {rules : Set (Equation σ)} {left right : Term σ}
    (derivation : Rewrites rules left right) (substitution : Subst σ) :
    Rewrites rules (substitution.applyTerm left) (substitution.applyTerm right) := by
  induction derivation with
  | refl => exact Rewrites.refl _
  | step _ rewrite ih => exact Rewrites.step ih (rewrite_subst rewrite substitution)

/-- A narrowing sequence rewrites the query instantiated by the composed substitution. -/
theorem narrows_sound {rules : Set (Equation σ)} {source : Term σ} {substitution : Subst σ}
    {target : Term σ} (derivation : Narrows rules source substitution target) :
    Rewrites rules (substitution.applyTerm source) target := by
  induction derivation with
  | refl => simpa [Subst.applyTerm_id] using Rewrites.refl source
  | step _ one ih =>
      simpa [Subst.applyTerm_comp] using
        Rewrites.step (rewrites_subst ih _) (narrow_sound one)

/-- In a model of the rules, the two ends of a narrowing step denote the same element. -/
theorem narrow_valid {Model : Type*} [(language σ).Structure Model]
    {rules : Set (Equation σ)}
    (valid : ∀ equation ∈ rules, equation.Valid Model)
    {source : Term σ} {substitution : Subst σ} {target : Term σ}
    (step : Narrow rules source substitution target) (assignment : σ.vars → Model) :
    realizeTerm assignment (substitution.applyTerm source) = realizeTerm assignment target :=
  rewrite_sound valid (narrow_sound step) assignment

/-- In a model of the rules, the two ends of a narrowing sequence denote the same element. -/
theorem narrows_valid {Model : Type*} [(language σ).Structure Model]
    {rules : Set (Equation σ)}
    (valid : ∀ equation ∈ rules, equation.Valid Model)
    {source : Term σ} {substitution : Subst σ} {target : Term σ}
    (derivation : Narrows rules source substitution target) (assignment : σ.vars → Model) :
    realizeTerm assignment (substitution.applyTerm source) = realizeTerm assignment target :=
  rewrites_sound valid (narrows_sound derivation) assignment

/-- A narrowing step whose substitution fixes the query is a rewrite step. -/
theorem rewrite_of_narrow_fixed {rules : Set (Equation σ)} {source : Term σ}
    {substitution : Subst σ} {target : Term σ}
    (step : Narrow rules source substitution target)
    (fixed : substitution.applyTerm source = source) :
    Rewrite rules source target := by
  simpa [fixed] using narrow_sound step

/-- A rewrite at a non-variable subterm of a renamed-apart rule is a narrowing that fixes the query. -/
theorem narrow_of_rewrite {rules : Set (Equation σ)}
    {equation : Equation σ} {substitution : Subst σ} {context : Context σ}
    (member : equation ∈ rules)
    (notVariable : ∀ v, substitution.applyTerm equation.left ≠ Term.var v)
    (apart : apart equation (context.fill (substitution.applyTerm equation.left))) :
    let kept := Subst.keep (equation.left.freeVars ∪ equation.right.freeVars) substitution
    let source := context.fill (substitution.applyTerm equation.left)
    Narrow rules source kept (context.fill (substitution.applyTerm equation.right)) ∧
      kept.applyTerm source = source := by
  let domain := equation.left.freeVars ∪ equation.right.freeVars
  let redex := substitution.applyTerm equation.left
  let source := context.fill redex
  let kept := Subst.keep domain substitution
  have idOnSource : ∀ v ∈ source.freeVars, kept v = .var v := by
    intro v memberVar
    have notDomain : v ∉ domain := fun memDomain => apart v memDomain memberVar
    simp [kept, Subst.keep, notDomain]
  have redexSubset : redex.freeVars ⊆ source.freeVars := freeVars_hole_subset context redex
  have fixesRedex : kept.applyTerm redex = redex :=
    Subst.applyTerm_id_of_fixed fun v memberVar => idOnSource v (redexSubset memberVar)
  have agreeLeft : kept.applyTerm equation.left = redex := by
    apply Subst.applyTerm_congr
    intro v memberVar
    have : v ∈ domain := Finset.mem_union_left _ memberVar
    simp [kept, Subst.keep, this]
  have outsideFixed : ∀ v ∈ outsideVars context, kept v = .var v :=
    fun v memberVar => idOnSource v (outsideVars_subset_fill context redex memberVar)
  have agreeRight : kept.applyTerm equation.right = substitution.applyTerm equation.right := by
    apply Subst.applyTerm_congr
    intro v memberVar
    have : v ∈ domain := Finset.mem_union_right _ memberVar
    simp [kept, Subst.keep, this]
  refine ⟨?_, Subst.applyTerm_id_of_fixed idOnSource⟩
  · exact Narrow.step equation member context redex notVariable rfl
      (by rw [agreeLeft, fixesRedex]) apart
      (by rw [fill_fixed_outside context equation.right kept outsideFixed, agreeRight])

omit σ [DecidableEq σ.vars] in
/-- Which side of a rule is matched. -/
inductive Side where
  | forward
  | backward

omit [DecidableEq σ.vars] in
/-- The side that is matched against the subterm. -/
def fromSide (side : Side) (equation : Equation σ) : Term σ :=
  match side with
  | .forward => equation.left
  | .backward => equation.right

omit [DecidableEq σ.vars] in
/-- The side written in place of the matched subterm. -/
def toSide (side : Side) (equation : Equation σ) : Term σ :=
  match side with
  | .forward => equation.right
  | .backward => equation.left

/-- Paramodulation of one rule into the left side of one unit equation. -/
inductive Paramodulate (rules : Set (Equation σ)) : Equation σ → Equation σ → Prop where
  | step {goal conclusion : Equation σ} (substitution : Subst σ)
      (equation : Equation σ) (member : equation ∈ rules) (side : Side)
      (context : Context σ) (subterm : Term σ)
      (notVariable : ∀ v, subterm ≠ Term.var v)
      (atSubterm : goal.left = context.fill subterm)
      (unifies : substitution.applyTerm (fromSide side equation) =
        substitution.applyTerm subterm)
      (apart : apart equation goal.left ∧ apart equation goal.right)
      (result : conclusion =
        ⟨substitution.applyTerm (context.fill (toSide side equation)),
          substitution.applyTerm goal.right⟩) :
      Paramodulate rules goal conclusion

/-- A narrowing of the left side is forward paramodulation when the right side adds no variables. -/
theorem paramodulate_of_narrow {rules : Set (Equation σ)} {goal : Equation σ}
    {substitution : Subst σ} {newLeft : Term σ}
    (step : Narrow rules goal.left substitution newLeft)
    (rightVars : goal.right.freeVars ⊆ goal.left.freeVars) :
    Paramodulate rules goal ⟨newLeft, substitution.applyTerm goal.right⟩ := by
  cases step with
  | step equation member context subterm notVariable atSubterm unifies separated result =>
      have apartRight : apart equation goal.right := by
        intro v memberVar occurs
        exact separated v memberVar (rightVars occurs)
      subst result
      exact Paramodulate.step (substitution := substitution) equation member .forward
        context subterm notVariable atSubterm unifies ⟨separated, apartRight⟩ rfl

omit [DecidableEq σ.vars] in
/-- The two sides of a valid equation stay equal when the equation is turned around. -/
theorem fromSide_eq_toSide {Model : Type*} [(language σ).Structure Model]
    {equation : Equation σ} (side : Side) (valid : equation.Valid Model)
    (assignment : σ.vars → Model) :
    realizeTerm assignment (fromSide side equation) = realizeTerm assignment (toSide side equation) := by
  cases side with
  | forward => exact valid assignment
  | backward => exact (valid assignment).symm

/-- Paramodulation is sound for rules and a goal that hold in the model. -/
theorem paramodulate_sound {Model : Type*} [(language σ).Structure Model]
    {rules : Set (Equation σ)}
    (valid : ∀ equation ∈ rules, equation.Valid Model)
    {goal conclusion : Equation σ}
    (goalValid : goal.Valid Model)
    (step : Paramodulate rules goal conclusion) :
    conclusion.Valid Model := by
  intro assignment
  cases step with
  | step substitution equation member side context subterm _ atSubterm unifies _ result =>
      subst result
      set ρ := fun name => realizeTerm assignment (substitution name) with ρEq
      have matched : realizeTerm ρ (fromSide side equation) = realizeTerm ρ subterm := by
        have same := congrArg (realizeTerm assignment) unifies
        simpa [realizeTerm_applyTerm, ρEq] using same
      have replaced : realizeTerm ρ (toSide side equation) = realizeTerm ρ subterm :=
        (fromSide_eq_toSide side (valid equation member) ρ).symm.trans matched
      have atContext : realizeTerm ρ (context.fill (toSide side equation)) =
          realizeTerm ρ (context.fill subterm) :=
        context.realize_congr ρ replaced
      have goalEq : realizeTerm ρ goal.left = realizeTerm ρ goal.right := goalValid ρ
      have source : realizeTerm ρ (context.fill subterm) = realizeTerm ρ goal.right := by
        simpa [atSubterm] using goalEq
      have denotations : realizeTerm ρ (context.fill (toSide side equation)) =
          realizeTerm ρ goal.right := atContext.trans source
      simpa [realizeTerm_applyTerm, ρEq] using denotations

omit [DecidableEq σ.vars] in
/-- Two terms reached from one term denote the same element in every model of the rules. -/
theorem reachable_terms_agree {Model : Type*} [(language σ).Structure Model]
    {rules : Set (Equation σ)}
    (valid : ∀ equation ∈ rules, equation.Valid Model)
    {start left right : Term σ}
    (toLeft : Rewrites rules start left) (toRight : Rewrites rules start right)
    (assignment : σ.vars → Model) :
    realizeTerm assignment left = realizeTerm assignment right :=
  (rewrites_sound valid toLeft assignment).symm.trans (rewrites_sound valid toRight assignment)

end

/-! ## `a ⟶ b` and `a ⟶ c` -/

namespace Fork

inductive Const where
  | a
  | b
  | c
deriving DecidableEq

/-- Three constants and no function symbols. -/
def signature : LPSignature where
  constants := Const
  vars := Unit
  relationSymbols := Empty
  relationArity := Empty.elim
  functionSymbols := Empty
  functionArity := Empty.elim

/-- The one variable of this signature has decidable equality. -/
instance : DecidableEq signature.vars := by
  unfold signature
  infer_instance

/-- The constant `a`. -/
def ca : Term signature := .const .a

/-- The constant `b`. -/
def cb : Term signature := .const .b

/-- The constant `c`. -/
def cc : Term signature := .const .c

/-- The rule `a ⟶ b`. -/
def toB : Equation signature := ⟨ca, cb⟩

/-- The rule `a ⟶ c`. -/
def toC : Equation signature := ⟨ca, cc⟩

/-- The two rules, and no others. -/
def rules : Set (Equation signature) := fun equation => equation = toB ∨ equation = toC

/-- A ground term shares no variable with any rule. -/
theorem apart_const (equation : Equation signature) (symbol : Const) :
    apart equation (.const symbol) := by
  intro _ _
  simp [Term.freeVars]

/-- `a` rewrites to `b`. -/
theorem a_rewrites_b : Rewrite rules ca cb :=
  Rewrite.rule toB (Or.inl rfl) (Subst.id signature) .hole

/-- `a` rewrites to `c`. -/
theorem a_rewrites_c : Rewrite rules ca cc :=
  Rewrite.rule toC (Or.inr rfl) (Subst.id signature) .hole

/-- Every one-step rewrite starts at `a` and ends at `b` or at `c`. -/
theorem rewrite_shape {left right : Term signature} (step : Rewrite rules left right) :
    left = ca ∧ (right = cb ∨ right = cc) := by
  cases step with
  | rule equation member substitution context =>
      cases context with
      | hole =>
          rcases member with rfl | rfl
          · exact ⟨rfl, Or.inl rfl⟩
          · exact ⟨rfl, Or.inr rfl⟩
      | app symbol _ _ _ => exact symbol.elim

/-- Every rewrite with these rules starts at `a`. -/
theorem rewrite_source {left right : Term signature} (step : Rewrite rules left right) :
    left = ca :=
  (rewrite_shape step).1

/-- A rewrite from `a` ends at `b` or at `c`. -/
theorem rewrite_from_a {right : Term signature} (step : Rewrite rules ca right) :
    right = cb ∨ right = cc :=
  (rewrite_shape step).2

/-- `b` has no rewrite step. -/
theorem b_stuck {right : Term signature} (step : Rewrite rules cb right) : False := by
  have source := rewrite_source step
  injection source with h
  cases h

/-- `c` has no rewrite step. -/
theorem c_stuck {right : Term signature} (step : Rewrite rules cc right) : False := by
  have source := rewrite_source step
  injection source with h
  cases h

/-- A rewriting sequence from `b` stays at `b`. -/
theorem rewrites_from_b {right : Term signature} (derivation : Rewrites rules cb right) :
    right = cb := by
  induction derivation with
  | refl => rfl
  | step _ rewrite ih =>
      subst ih
      exact (b_stuck rewrite).elim

/-- A rewriting sequence from `c` stays at `c`. -/
theorem rewrites_from_c {right : Term signature} (derivation : Rewrites rules cc right) :
    right = cc := by
  induction derivation with
  | refl => rfl
  | step _ rewrite ih =>
      subst ih
      exact (c_stuck rewrite).elim

/-- No rewriting sequence leads from `b` to `c`. -/
theorem no_rewrites_b_c (derivation : Rewrites rules cb cc) : False := by
  have same := rewrites_from_b derivation
  injection same with h
  cases h

/-- No rewriting sequence leads from `c` to `b`. -/
theorem no_rewrites_c_b (derivation : Rewrites rules cc cb) : False := by
  have same := rewrites_from_c derivation
  injection same with h
  cases h

/-- Distinct constants do not unify. -/
theorem const_apart {substitution : Subst signature} {left right : Const}
    (same : substitution.applyTerm (.const left) = substitution.applyTerm (.const right))
    (different : left ≠ right) : False := by
  injection same with equal
  exact different equal

/-- `b` has no narrowing step. -/
theorem no_narrow_b {substitution : Subst signature} {right : Term signature}
    (step : Narrow rules cb substitution right) : False := by
  cases step with
  | step equation member context subterm _ atSubterm unifies _ _ =>
      cases context with
      | hole =>
          simp only [Context.fill] at atSubterm
          have subEq : subterm = cb := atSubterm.symm
          subst subEq
          rcases member with rfl | rfl
          · exact const_apart unifies (by decide)
          · exact const_apart unifies (by decide)
      | app symbol _ _ _ => exact symbol.elim

/-- `c` has no narrowing step. -/
theorem no_narrow_c {substitution : Subst signature} {right : Term signature}
    (step : Narrow rules cc substitution right) : False := by
  cases step with
  | step equation member context subterm _ atSubterm unifies _ _ =>
      cases context with
      | hole =>
          simp only [Context.fill] at atSubterm
          have subEq : subterm = cc := atSubterm.symm
          subst subEq
          rcases member with rfl | rfl
          · exact const_apart unifies (by decide)
          · exact const_apart unifies (by decide)
      | app symbol _ _ _ => exact symbol.elim

/-- A narrowing sequence from `b` stays at `b`. -/
theorem narrows_from_b {substitution : Subst signature} {right : Term signature}
    (derivation : Narrows rules cb substitution right) : right = cb := by
  induction derivation with
  | refl => rfl
  | step _ one ih =>
      subst ih
      exact (no_narrow_b one).elim

/-- A narrowing sequence from `c` stays at `c`. -/
theorem narrows_from_c {substitution : Subst signature} {right : Term signature}
    (derivation : Narrows rules cc substitution right) : right = cc := by
  induction derivation with
  | refl => rfl
  | step _ one ih =>
      subst ih
      exact (no_narrow_c one).elim

/-- No narrowing sequence leads from `b` to `c`. -/
theorem no_narrows_b_c {substitution : Subst signature}
    (derivation : Narrows rules cb substitution cc) : False := by
  have same := narrows_from_b derivation
  injection same with h
  cases h

/-- No narrowing sequence leads from `c` to `b`. -/
theorem no_narrows_c_b {substitution : Subst signature}
    (derivation : Narrows rules cc substitution cb) : False := by
  have same := narrows_from_c derivation
  injection same with h
  cases h

/-- The terms reachable from `a` are `a`, `b`, and `c`. -/
theorem reachable_from_a {right : Term signature} (derivation : Rewrites rules ca right) :
    right = ca ∨ right = cb ∨ right = cc := by
  induction derivation with
  | refl => exact Or.inl rfl
  | step _ rewrite ih =>
      rcases ih with rfl | rfl | rfl
      · rcases rewrite_from_a rewrite with rfl | rfl
        · exact Or.inr (Or.inl rfl)
        · exact Or.inr (Or.inr rfl)
      · exact (b_stuck rewrite).elim
      · exact (c_stuck rewrite).elim

/-- The terms `a` reaches that have no further step are `b` and `c`. -/
theorem answers {right : Term signature} (derivation : Rewrites rules ca right)
    (stuck : ∀ further, ¬ Rewrite rules right further) : right = cb ∨ right = cc := by
  rcases reachable_from_a derivation with rfl | rfl | rfl
  · exact (stuck cb a_rewrites_b).elim
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- Paramodulation of `a ⟶ b` into `a = c` derives `b = c`. -/
theorem critical_pair : Paramodulate rules toC ⟨cb, cc⟩ := by
  exact Paramodulate.step (substitution := Subst.id signature) toB (Or.inl rfl) .forward .hole ca
    (by intro _ equal; cases equal) rfl
    (by simp [fromSide, toB, Subst.applyTerm_id])
    ⟨apart_const toB .a, apart_const toB .c⟩
    (by simp [toSide, toB, toC, cb, cc, Context.fill, Subst.applyTerm_id])

/-- `b = c` holds in every model of the two rules. -/
theorem b_eq_c {Model : Type*} [(language signature).Structure Model]
    (valid : ∀ equation ∈ rules, equation.Valid Model) : (⟨cb, cc⟩ : Equation signature).Valid Model :=
  paramodulate_sound valid (valid toC (Or.inr rfl)) critical_pair

end Fork

/-! ## `f x ⟶ f (g x)` -/

namespace Growth

inductive Symbol where
  | f
  | g
deriving DecidableEq

/-- One variable, and the unary symbols `f` and `g`. -/
abbrev signature : LPSignature where
  constants := Empty
  vars := Unit
  relationSymbols := Empty
  relationArity := Empty.elim
  functionSymbols := Symbol
  functionArity := fun _ => 1

/-- `g` applied `n` times to the variable. -/
def wrapped : ℕ → Term signature
  | 0 => .var ()
  | n + 1 => .app .g fun _ => wrapped n

/-- `f` applied to `g` nested `n` times. -/
def query (n : ℕ) : Term signature := .app .f fun _ => wrapped n

/-- The authored rule `f x ⟶ f (g x)`. -/
def grow : Equation signature := ⟨query 0, query 1⟩

/-- The same equation used from right to left. -/
def shrink : Equation signature := ⟨query 1, query 0⟩

/-- The authored rule alone. -/
def growRules : Set (Equation signature) := fun equation => equation = grow

/-- The reversed rule alone. -/
def shrinkRules : Set (Equation signature) := fun equation => equation = shrink

/-- The only argument position of a unary symbol. -/
def zeroIndex (symbol : Symbol) : Fin (signature.functionArity symbol) :=
  ⟨0, Nat.zero_lt_one⟩

/-- Each unfolding of `f x ⟶ f (g x)` is one rewrite. -/
theorem grow_step (n : ℕ) : Rewrite growRules (query n) (query (n + 1)) := by
  let substitution : Subst signature := fun _ => wrapped n
  have step := Rewrite.rule (rules := growRules) grow rfl substitution .hole
  have leftEq : Context.hole.fill (substitution.applyTerm grow.left) = query n := by
    rw [Context.fill, grow, query, wrapped, Subst.applyTerm_app, Subst.applyTerm_var]
    rfl
  have rightEq : Context.hole.fill (substitution.applyTerm grow.right) = query (n + 1) := by
    show substitution.applyTerm (.app .f fun _ => .app .g fun _ => .var ()) =
      .app .f fun _ => .app .g fun _ => wrapped n
    rw [Subst.applyTerm_app, Subst.applyTerm_app, Subst.applyTerm_var]
  simpa [leftEq, rightEq] using step

/-- An infinite chain of rewrites shows that its start is not accessible. -/
theorem not_acc_of_steps {α : Sort _} {rel : α → α → Prop} (seq : ℕ → α)
    (step : ∀ k, rel (seq k) (seq (k + 1))) (k : ℕ)
    (acc : Acc (fun later earlier => rel earlier later) (seq k)) : False :=
  Acc.rec (motive := fun term _ => ∀ k, term = seq k → False)
    (fun _ _ ih k equal => ih (seq (k + 1)) (equal.symm ▸ step k) (k + 1) rfl) acc k rfl

/-- Rewriting from `f x` along the authored rule never stops. -/
theorem grow_never_stops :
    ¬ Acc (fun later earlier => Rewrite growRules earlier later) (query 0) :=
  fun acc => not_acc_of_steps query grow_step 0 acc

/-- A well-founded order compatible with contexts and with substitutions. -/
structure ReductionOrder {τ : LPSignature} (rel : Term τ → Term τ → Prop) : Prop where
  wellFounded : WellFounded (fun later earlier => rel earlier later)
  context : ∀ (context : Context τ) {left right : Term τ},
    rel left right → rel (context.fill left) (context.fill right)
  substitution : ∀ (substitution : Subst τ) {left right : Term τ},
    rel left right → rel (substitution.applyTerm left) (substitution.applyTerm right)

/-- No reduction order decreases along `f x ⟶ f (g x)`. -/
theorem grow_no_reduction_order (rel : Term signature → Term signature → Prop)
    (order : ReductionOrder rel) (orients : rel grow.left grow.right) : False := by
  have chain : ∀ n, rel (query n) (query (n + 1)) := by
    intro n
    let substitution : Subst signature := fun _ => wrapped n
    have oriented := order.substitution substitution orients
    have leftEq : substitution.applyTerm grow.left = query n := by
      rw [grow, query, wrapped, Subst.applyTerm_app, Subst.applyTerm_var]
      rfl
    have rightEq : substitution.applyTerm grow.right = query (n + 1) := by
      show substitution.applyTerm (.app .f fun _ => .app .g fun _ => .var ()) =
        .app .f fun _ => .app .g fun _ => wrapped n
      rw [Subst.applyTerm_app, Subst.applyTerm_app, Subst.applyTerm_var]
    simpa [leftEq, rightEq] using oriented
  exact not_acc_of_steps query chain 0 (order.wellFounded.apply (query 0))

/-- The value of a term when the variable is read as a natural number. -/
def val (assign : Unit → ℕ) : Term signature → ℕ
  | .var _ => assign ()
  | .const empty => empty.elim
  | .app symbol arguments => val assign (arguments (zeroIndex symbol)) + 1

/-- Evaluation commutes with substitution. -/
theorem val_apply (assign : Unit → ℕ) (substitution : Subst signature) (term : Term signature) :
    val assign (substitution.applyTerm term) =
      val (fun v => val assign (substitution v)) term := by
  induction term with
  | var _ => rfl
  | const empty => exact empty.elim
  | app symbol arguments ih =>
      simp only [Subst.applyTerm_app, val]
      exact congrArg Nat.succ (ih (zeroIndex symbol))

/-- A strictly smaller hole stays strictly smaller in every context. -/
theorem val_fill_lt (assign : Unit → ℕ) (context : Context signature)
    {left right : Term signature} (smaller : val assign right < val assign left) :
    val assign (context.fill right) < val assign (context.fill left) := by
  induction context with
  | hole => exact smaller
  | app symbol _ position inner ih =>
      have pos0 : position = zeroIndex symbol := by
        apply Fin.ext
        simp only [zeroIndex]
        have lt : position.val < 1 := position.isLt
        omega
      simp only [Context.fill, val, pos0, Function.update_self]
      omega

/-- One reverse step decreases the value at every reading of the variable. -/
theorem shrink_val_lt {left right : Term signature} (step : Rewrite shrinkRules left right)
    (assign : Unit → ℕ) : val assign right < val assign left := by
  cases step with
  | rule equation member substitution context =>
      have equation_eq : equation = shrink := member
      subst equation_eq
      have hole : val assign (substitution.applyTerm shrink.right) <
          val assign (substitution.applyTerm shrink.left) := by
        simp only [val_apply, shrink, query, wrapped, val]
        omega
      exact val_fill_lt assign context hole

/-- A relation contained in a well-founded relation is well-founded. -/
theorem wellFounded_of_subrelation {α : Sort _} {smaller larger : α → α → Prop}
    (contained : ∀ a b, smaller a b → larger a b) (wf : WellFounded larger) :
    WellFounded smaller := by
  constructor
  intro a
  induction wf.apply a with
  | intro a _ ih =>
      exact Acc.intro a fun b related => ih b (contained b a related)

/-- Rewriting with `f (g x) ⟶ f x` always stops. -/
theorem shrink_stops : WellFounded (fun later earlier => Rewrite shrinkRules earlier later) := by
  refine wellFounded_of_subrelation ?_ (InvImage.wf (val fun _ => 0) Nat.lt_wfRel.wf)
  intro later earlier step
  exact shrink_val_lt step fun _ => 0

/-- `left` decreases to `right` when every reading of the variable decreases. -/
def decreases (left right : Term signature) : Prop :=
  ∀ assign : Unit → ℕ, val assign right < val assign left

/-- Decreasing values are a reduction order, and they orient the reversed rule. -/
theorem decreases_reduction_order : ReductionOrder decreases ∧ decreases shrink.left shrink.right := by
  refine ⟨?_, ?_⟩
  · refine ⟨?_, ?_, ?_⟩
    · refine wellFounded_of_subrelation ?_ (InvImage.wf (val fun _ => 0) Nat.lt_wfRel.wf)
      intro later earlier related
      exact related (fun _ => 0)
    · intro context _ _ related assign
      exact val_fill_lt assign context (related assign)
    · intro substitution _ _ related assign
      have smaller := related fun v => val assign (substitution v)
      simpa [val_apply] using smaller
  · intro assign
    simp only [shrink, query, wrapped, val]
    omega

end Growth

end Mettapedia.Logic.LP.Narrowing
