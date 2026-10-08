import Mettapedia.GSLT.Dedukti.TypingSubstitution

/-!
# Confluence of beta with orthogonal declared rules

Reduction of the λΠ terms is confluent for every theory whose declared rules
are orthogonal (`confluent_of_orthogonal`).  The theory with no rule is the
first case: beta alone is confluent (`confluent_empty`), and so is beta with
closed transparent definitions (`confluent_of_no_rule`).

## Method

The method is the one of the existing Church–Rosser proofs in the tree
(`Mettapedia.TypeTheory.Calculi.ContextualCode`, `SealedCode`, and the
parallel development of `MetaInterpretiveLearning/CumulativeTheory`), carried
out on the terms of this calculus: `Par` contracts any set of redexes at
once, `Dev` relates a term to its complete development, every parallel
reduct of a term reduces in parallel to the development (`Dev.triangle`), so
`Par` has the diamond property, and Mathlib's `Relation.church_rosser` gives
confluence.  The development is a relation and not a function, because the
declared rules are an arbitrary predicate: whether a term is an instance of
a left side is not decided, and the existence of a development
(`Dev.exists`) is proved classically.

Those proofs cannot be transported.  Their terms are scoped by `Fin`, their
abstraction carries no domain, and they have no product and no constant.
Here an abstraction carries a domain in which steps occur, so no map into
those calculi sends a redex to a redex and a term without redex to one.

## What orthogonal means here

`Theory.Orthogonal` asks seven things of a theory.

* `closedBodies`: transparent definitions are closed terms.
* `leftAlgebraic`: a left side is a constant applied to patterns built from
  constants, sorts, variables and application; no variable is applied, and
  there is no binder (`algebraic`).
* `leftLinear`: no variable occurs twice in a left side.
* `rightDetermined`: an instance of the right side is determined by the
  variables of the left side.
* `leftUndefined`: a constant that is a left side has no definition.
* `rootUnique`: two rules whose left sides have a common instance are one
  rule.
* `nonOverlapping`: no instance of a proper part of a left side that is not
  a variable is a redex by a definition or a rule (`Inert`).

Each is used, and three of them fail in theories that are not confluent
(`ConfluenceExamples`).
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Dedukti

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.LF
open Mettapedia.GSLT.LanguageDef.LFTyping (lift subst subst0)
open Mettapedia.Logic.Relation (Confluent IsNormal)

/-! ## Algebraic patterns -/

/-- A term built from constants, sorts, variables and application.  Every
function position holds a constant applied to arguments; with `headed` the
term itself is such a spine. -/
def algebraic (headed : Bool) : Term → Bool
  | .con _ => true
  | .app function argument => algebraic true function && algebraic false argument
  | .var _ => !headed
  | .srt _ => !headed
  | .pi _ _ => false
  | .lam _ _ => false

/-- The variables of an algebraic pattern, with repetition. -/
def patternVars : Term → List Nat
  | .var index => [index]
  | .app function argument => patternVars function ++ patternVars argument
  | _ => []

/-- The proper parts of an applicative term. -/
def subpatterns : Term → List Term
  | .app function argument =>
      function :: argument :: (subpatterns function ++ subpatterns argument)
  | _ => []

theorem algebraic_of_headed {term : Term} (headed : algebraic true term = true) :
    algebraic false term = true := by
  cases term <;> simp_all [algebraic]

theorem algebraic_app {headed : Bool} {function argument : Term} :
    algebraic headed (.app function argument) = true ↔
      algebraic true function = true ∧ algebraic false argument = true := by
  simp [algebraic]

/-- A headed algebraic term has a constant at its head. -/
theorem headConst_of_algebraic : ∀ {term : Term}, algebraic true term = true →
    ∃ name, headConst term = some name := by
  intro term
  induction term with
  | var index => intro headed; simp [algebraic] at headed
  | srt sort => intro headed; simp [algebraic] at headed
  | con name => intro _; exact ⟨name, rfl⟩
  | pi domain body _ _ => intro headed; simp [algebraic] at headed
  | lam domain body _ _ => intro headed; simp [algebraic] at headed
  | app function argument ihFunction _ =>
      intro headed
      exact ihFunction (algebraic_app.mp headed).1

/-- A term with no constant at its head is no instance of a headed algebraic
pattern. -/
theorem ne_inst_of_headConst_none {pattern : Term} (headed : algebraic true pattern = true)
    (assignment : Nat → Term) {term : Term} (headless : headConst term = none) :
    term ≠ inst assignment pattern := by
  intro same
  obtain ⟨name, head⟩ := headConst_of_algebraic headed
  have instance_ : headConst (inst assignment pattern) = some name :=
    headConst_instantiate assignment 0 head
  rw [← same, headless] at instance_
  cases instance_

/-- An instance of an algebraic pattern is determined by the variables of the
pattern. -/
theorem inst_congr_patternVars {first second : Nat → Term} :
    ∀ {term : Term} {headed : Bool}, algebraic headed term = true →
      (∀ index ∈ patternVars term, first index = second index) →
        inst first term = inst second term := by
  intro term
  induction term with
  | var index =>
      intro headed _ agree
      rw [inst_var, inst_var]
      exact agree index (List.mem_singleton.mpr rfl)
  | srt sort => intro headed _ _; rfl
  | con name => intro headed _ _; rfl
  | pi domain body _ _ => intro headed isAlgebraic; simp [algebraic] at isAlgebraic
  | lam domain body _ _ => intro headed isAlgebraic; simp [algebraic] at isAlgebraic
  | app function argument ihFunction ihArgument =>
      intro headed isAlgebraic agree
      obtain ⟨functionAlgebraic, argumentAlgebraic⟩ := algebraic_app.mp isAlgebraic
      rw [inst_app, inst_app,
        ihFunction functionAlgebraic fun index member =>
          agree index (List.mem_append_left _ member),
        ihArgument argumentAlgebraic fun index member =>
          agree index (List.mem_append_right _ member)]

/-- Two assignments with one instance of an algebraic pattern agree on its
variables. -/
theorem eq_of_inst_eq {first second : Nat → Term} :
    ∀ {term : Term} {headed : Bool}, algebraic headed term = true →
      inst first term = inst second term →
        ∀ index ∈ patternVars term, first index = second index := by
  intro term
  induction term with
  | var index =>
      intro headed _ same other member
      rw [inst_var, inst_var] at same
      rw [List.mem_singleton.mp member]
      exact same
  | srt sort => intro headed _ _ other member; simp [patternVars] at member
  | con name => intro headed _ _ other member; simp [patternVars] at member
  | pi domain body _ _ => intro headed isAlgebraic; simp [algebraic] at isAlgebraic
  | lam domain body _ _ => intro headed isAlgebraic; simp [algebraic] at isAlgebraic
  | app function argument ihFunction ihArgument =>
      intro headed isAlgebraic same other member
      obtain ⟨functionAlgebraic, argumentAlgebraic⟩ := algebraic_app.mp isAlgebraic
      rw [inst_app, inst_app] at same
      obtain ⟨functions, arguments⟩ := Term.app.inj same
      rcases List.mem_append.mp member with inFunction | inArgument
      · exact ihFunction functionAlgebraic functions other inFunction
      · exact ihArgument argumentAlgebraic arguments other inArgument

/-- What a variable of an algebraic pattern is assigned is no larger than the
instance. -/
theorem sizeOf_le_inst (assignment : Nat → Term) :
    ∀ {term : Term} {headed : Bool}, algebraic headed term = true →
      ∀ index ∈ patternVars term, sizeOf (assignment index) ≤ sizeOf (inst assignment term) := by
  intro term
  induction term with
  | var index =>
      intro headed _ other member
      rw [List.mem_singleton.mp member, inst_var]
      exact Nat.le_refl _
  | srt sort => intro headed _ other member; simp [patternVars] at member
  | con name => intro headed _ other member; simp [patternVars] at member
  | pi domain body _ _ => intro headed isAlgebraic; simp [algebraic] at isAlgebraic
  | lam domain body _ _ => intro headed isAlgebraic; simp [algebraic] at isAlgebraic
  | app function argument ihFunction ihArgument =>
      intro headed isAlgebraic other member
      obtain ⟨functionAlgebraic, argumentAlgebraic⟩ := algebraic_app.mp isAlgebraic
      rw [inst_app, Term.app.sizeOf_spec]
      rcases List.mem_append.mp member with inFunction | inArgument
      · have bound := ihFunction functionAlgebraic other inFunction
        omega
      · have bound := ihArgument argumentAlgebraic other inArgument
        omega

/-- What a variable of a headed algebraic pattern is assigned is smaller than
the instance. -/
theorem sizeOf_lt_inst (assignment : Nat → Term) {term : Term}
    (headed : algebraic true term = true) {index : Nat} (member : index ∈ patternVars term) :
    sizeOf (assignment index) < sizeOf (inst assignment term) := by
  cases term with
  | var other => simp [algebraic] at headed
  | srt sort => simp [patternVars] at member
  | con name => simp [patternVars] at member
  | pi domain body => simp [algebraic] at headed
  | lam domain body => simp [algebraic] at headed
  | app function argument =>
      obtain ⟨functionAlgebraic, argumentAlgebraic⟩ := algebraic_app.mp headed
      rw [inst_app, Term.app.sizeOf_spec]
      rcases List.mem_append.mp member with inFunction | inArgument
      · have bound := sizeOf_le_inst assignment functionAlgebraic index inFunction
        omega
      · have bound := sizeOf_le_inst assignment argumentAlgebraic index inArgument
        omega

/-- The parts of a part are parts. -/
theorem subpatterns_subset {part : Term} :
    ∀ {whole : Term}, part ∈ subpatterns whole →
      ∀ inner ∈ subpatterns part, inner ∈ subpatterns whole := by
  intro whole
  induction whole with
  | var index => intro member; simp [subpatterns] at member
  | srt sort => intro member; simp [subpatterns] at member
  | con name => intro member; simp [subpatterns] at member
  | pi domain body _ _ => intro member; simp [subpatterns] at member
  | lam domain body _ _ => intro member; simp [subpatterns] at member
  | app function argument ihFunction ihArgument =>
      intro member inner innerMember
      simp only [subpatterns, List.mem_cons, List.mem_append] at member ⊢
      rcases member with rfl | rfl | inFunction | inArgument
      · exact Or.inr (Or.inr (Or.inl innerMember))
      · exact Or.inr (Or.inr (Or.inr innerMember))
      · exact Or.inr (Or.inr (Or.inl (ihFunction inFunction inner innerMember)))
      · exact Or.inr (Or.inr (Or.inr (ihArgument inArgument inner innerMember)))

/-! ## Orthogonal theories -/

/-- The left side of every declared rule is a headed algebraic pattern. -/
def Theory.LeftAlgebraic (theory : Theory) : Prop :=
  ∀ rule, theory.rule rule → algebraic true rule.lhs = true

/-- **No instance of the term is a redex at its root**, by a definition or by
a declared rule. -/
structure Inert (theory : Theory) (part : Term) : Prop where
  undefined : ∀ name, part = .con name → theory.body name = none
  unmatched : ∀ rule (first second : Nat → Term), theory.rule rule →
    inst first part ≠ inst second rule.lhs

/-- **An orthogonal theory**: closed definitions, and declared rules that are
algebraic and linear on the left, determined on the right, and without
overlap, among themselves and with the definitions. -/
structure Theory.Orthogonal (theory : Theory) : Prop where
  closedBodies : theory.ClosedBodies
  leftAlgebraic : theory.LeftAlgebraic
  leftLinear : ∀ rule, theory.rule rule → (patternVars rule.lhs).Nodup
  rightDetermined : ∀ rule, theory.rule rule → ∀ first second : Nat → Term,
    (∀ index ∈ patternVars rule.lhs, first index = second index) →
      inst first rule.rhs = inst second rule.rhs
  leftUndefined : ∀ rule, theory.rule rule → ∀ name, rule.lhs = .con name →
    theory.body name = none
  rootUnique : ∀ first second, theory.rule first → theory.rule second →
    ∀ left right : Nat → Term, inst left first.lhs = inst right second.lhs → first = second
  nonOverlapping : ∀ rule, theory.rule rule → ∀ part ∈ subpatterns rule.lhs,
    algebraic true part = true → Inert theory part

variable {theory : Theory}

theorem Theory.LeftAlgebraic.headed (leftAlgebraic : theory.LeftAlgebraic) : theory.Headed :=
  fun rule member => headConst_of_algebraic (leftAlgebraic rule member)

/-- **A theory with no declared rule and closed definitions is orthogonal.** -/
theorem Theory.orthogonal_of_no_rule (closed : theory.ClosedBodies)
    (empty : ∀ rule, ¬ theory.rule rule) : theory.Orthogonal where
  closedBodies := closed
  leftAlgebraic := fun rule member => (empty rule member).elim
  leftLinear := fun rule member => (empty rule member).elim
  rightDetermined := fun rule member => (empty rule member).elim
  leftUndefined := fun rule member => (empty rule member).elim
  rootUnique := fun first _ member => (empty first member).elim
  nonOverlapping := fun rule member => (empty rule member).elim

theorem Theory.empty_closedBodies : Theory.empty.ClosedBodies := by
  intro name term defined
  cases defined

/-- The theory with no constant and no rule is orthogonal. -/
theorem Theory.empty_orthogonal : Theory.empty.Orthogonal :=
  Theory.orthogonal_of_no_rule Theory.empty_closedBodies fun _ member => member

/-! ## Parallel reduction -/

/-- **Parallel reduction**: contract any set of redexes of a term at once. -/
inductive Par (theory : Theory) : Term → Term → Prop where
  | var (index : Nat) : Par theory (.var index) (.var index)
  | srt (sort : Srt) : Par theory (.srt sort) (.srt sort)
  | con (name : String) : Par theory (.con name) (.con name)
  | pi {domain domain' body body' : Term} :
      Par theory domain domain' → Par theory body body' →
        Par theory (.pi domain body) (.pi domain' body')
  | lam {domain domain' body body' : Term} :
      Par theory domain domain' → Par theory body body' →
        Par theory (.lam domain body) (.lam domain' body')
  | app {function function' argument argument' : Term} :
      Par theory function function' → Par theory argument argument' →
        Par theory (.app function argument) (.app function' argument')
  | beta {domain body body' argument argument' : Term} :
      Par theory body body' → Par theory argument argument' →
        Par theory (.app (.lam domain body) argument) (subst0 argument' body')
  | delta {name : String} {term : Term} :
      theory.body name = some term → Par theory (.con name) term
  | rule {rule : RewriteRule} {first second : Nat → Term} :
      theory.rule rule → (∀ index, Par theory (first index) (second index)) →
        Par theory (inst first rule.lhs) (inst second rule.rhs)

theorem Par.refl (term : Term) : Par theory term term := by
  induction term with
  | var index => exact .var index
  | srt sort => exact .srt sort
  | con name => exact .con name
  | pi domain body ihDomain ihBody => exact .pi ihDomain ihBody
  | lam domain body ihDomain ihBody => exact .lam ihDomain ihBody
  | app function argument ihFunction ihArgument => exact .app ihFunction ihArgument

theorem RootStep.par {source target : Term} (step : RootStep theory source target) :
    Par theory source target := by
  cases step with
  | beta domain body argument => exact .beta (.refl body) (.refl argument)
  | delta defined => exact .delta defined
  | rule assignment member => exact .rule member fun index => .refl (assignment index)

/-- A step is a parallel reduction. -/
theorem Step.par {source target : Term} (step : Step theory source target) :
    Par theory source target := by
  cases step with
  | inContext context root =>
      induction context with
      | hole => exact root.par
      | piDomain rest body ih => exact .pi ih (.refl body)
      | piBody domain rest ih => exact .pi (.refl domain) ih
      | lamDomain rest body ih => exact .lam ih (.refl body)
      | lamBody domain rest ih => exact .lam (.refl domain) ih
      | appFunction rest argument ih => exact .app ih (.refl argument)
      | appArgument function rest ih => exact .app (.refl function) ih

/-! ### Parallel reduction is reduction -/

theorem Reduces.liftTerm (closed : theory.ClosedBodies) {source target : Term}
    (reduces : Reduces theory source target) (amount cutoff : Nat) :
    Reduces theory (LFTyping.lift amount cutoff source) (LFTyping.lift amount cutoff target) := by
  induction reduces with
  | refl => exact .refl
  | tail _ step ih => exact ih.tail (step.lift closed amount cutoff)

/-- Reduction of the assigned terms is reduction of the instance. -/
theorem Reduces.instantiate (closed : theory.ClosedBodies) {first second : Nat → Term}
    (pointwise : ∀ index, Reduces theory (first index) (second index)) (term : Term) :
    ∀ depth : Nat,
      Reduces theory (Dedukti.instantiate first depth term)
        (Dedukti.instantiate second depth term) := by
  induction term with
  | var index =>
      intro depth
      by_cases below : index < depth
      · simp only [Dedukti.instantiate, below, if_true]
        exact .refl
      · simp only [Dedukti.instantiate, below, if_false]
        exact (pointwise _).liftTerm closed depth 0
  | srt sort => intro depth; exact .refl
  | con name => intro depth; exact .refl
  | pi domain body ihDomain ihBody => intro depth; exact Reduces.pi (ihDomain depth) (ihBody _)
  | lam domain body ihDomain ihBody => intro depth; exact Reduces.lam (ihDomain depth) (ihBody _)
  | app function argument ihFunction ihArgument =>
      intro depth
      exact Reduces.app (ihFunction depth) (ihArgument depth)

/-- **A parallel reduction is a reduction.** -/
theorem Par.reduces (closed : theory.ClosedBodies) {source target : Term}
    (par : Par theory source target) : Reduces theory source target := by
  induction par with
  | var index => exact .refl
  | srt sort => exact .refl
  | con name => exact .refl
  | pi _ _ ihDomain ihBody => exact Reduces.pi ihDomain ihBody
  | lam _ _ ihDomain ihBody => exact Reduces.lam ihDomain ihBody
  | app _ _ ihFunction ihArgument => exact Reduces.app ihFunction ihArgument
  | beta _ _ ihBody ihArgument =>
      exact (Reduces.app (Reduces.lam .refl ihBody) ihArgument).tail
        (Step.root (.beta _ _ _))
  | delta defined => exact .single (Step.root (.delta defined))
  | @rule rule first second member _ ih =>
      exact (Reduces.instantiate closed ih rule.lhs 0).tail (Step.root (.rule second member))

/-! ### Parallel reduction under lifting, instantiation and substitution -/

theorem Par.liftTerm (closed : theory.ClosedBodies) {source target : Term}
    (par : Par theory source target) :
    ∀ amount cutoff : Nat,
      Par theory (LFTyping.lift amount cutoff source) (LFTyping.lift amount cutoff target) := by
  induction par with
  | var index => intro amount cutoff; exact .refl _
  | srt sort => intro amount cutoff; exact .srt sort
  | con name => intro amount cutoff; exact .con name
  | pi _ _ ihDomain ihBody => intro amount cutoff; exact .pi (ihDomain _ _) (ihBody _ _)
  | lam _ _ ihDomain ihBody => intro amount cutoff; exact .lam (ihDomain _ _) (ihBody _ _)
  | app _ _ ihFunction ihArgument =>
      intro amount cutoff; exact .app (ihFunction _ _) (ihArgument _ _)
  | @beta domain body body' argument argument' _ _ ihBody ihArgument =>
      intro amount cutoff
      rw [lift_subst0]
      exact .beta (ihBody amount (cutoff + 1)) (ihArgument amount cutoff)
  | @delta name term defined =>
      intro amount cutoff
      rw [(closed _ _ defined).lift]
      exact .delta defined
  | @rule rule first second member _ ih =>
      intro amount cutoff
      rw [lift_inst, lift_inst]
      exact .rule member fun index => ih index amount cutoff

/-- Parallel reduction of the assigned terms is parallel reduction of the
instance. -/
theorem Par.instantiate (closed : theory.ClosedBodies) {first second : Nat → Term}
    (pointwise : ∀ index, Par theory (first index) (second index)) (term : Term) :
    ∀ depth : Nat,
      Par theory (Dedukti.instantiate first depth term) (Dedukti.instantiate second depth term) := by
  induction term with
  | var index =>
      intro depth
      by_cases below : index < depth
      · simp only [Dedukti.instantiate, below, if_true]
        exact .var index
      · simp only [Dedukti.instantiate, below, if_false]
        exact (pointwise _).liftTerm closed depth 0
  | srt sort => intro depth; exact .srt sort
  | con name => intro depth; exact .con name
  | pi domain body ihDomain ihBody => intro depth; exact .pi (ihDomain depth) (ihBody _)
  | lam domain body ihDomain ihBody => intro depth; exact .lam (ihDomain depth) (ihBody _)
  | app function argument ihFunction ihArgument =>
      intro depth
      exact .app (ihFunction depth) (ihArgument depth)

/-- **Parallel reduction is stable under substitution**, in the term and in
what is substituted at once. -/
theorem Par.substTerm (closed : theory.ClosedBodies) {body body' : Term}
    (bodies : Par theory body body') :
    ∀ {argument argument' : Term}, Par theory argument argument' → ∀ index : Nat,
      Par theory (LFTyping.subst index argument body) (LFTyping.subst index argument' body') := by
  induction bodies with
  | var variable_ =>
      intro argument argument' arguments index
      by_cases same : variable_ = index
      · simpa [LFTyping.subst, same] using arguments
      · by_cases above : index < variable_
        · simpa [LFTyping.subst, same, above] using Par.var (theory := theory) (variable_ - 1)
        · simpa [LFTyping.subst, same, above] using Par.var (theory := theory) variable_
  | srt sort => intro argument argument' _ index; exact .srt sort
  | con name => intro argument argument' _ index; exact .con name
  | pi _ _ ihDomain ihBody =>
      intro argument argument' arguments index
      exact .pi (ihDomain arguments index) (ihBody (arguments.liftTerm closed 1 0) (index + 1))
  | lam _ _ ihDomain ihBody =>
      intro argument argument' arguments index
      exact .lam (ihDomain arguments index) (ihBody (arguments.liftTerm closed 1 0) (index + 1))
  | app _ _ ihFunction ihArgument =>
      intro argument argument' arguments index
      exact .app (ihFunction arguments index) (ihArgument arguments index)
  | @beta domain inner inner' operand operand' _ _ ihBody ihArgument =>
      intro argument argument' arguments index
      rw [subst_subst0]
      exact .beta (ihBody (arguments.liftTerm closed 1 0) (index + 1)) (ihArgument arguments index)
  | @delta name term defined =>
      intro argument argument' _ index
      rw [(closed _ _ defined).subst]
      exact .delta defined
  | @rule rule first second member _ ih =>
      intro argument argument' arguments index
      rw [subst_inst, subst_inst]
      exact .rule member fun position => ih position arguments index

/-! ### Where a parallel reduction can be -/

theorem Par.var_inv (leftAlgebraic : theory.LeftAlgebraic) {index : Nat} {target : Term}
    (par : Par theory (.var index) target) : target = .var index := by
  generalize same : Term.var index = source at par
  cases par with
  | var other => rfl
  | srt sort => cases same
  | con name => cases same
  | pi _ _ => cases same
  | lam _ _ => cases same
  | app _ _ => cases same
  | beta _ _ => cases same
  | delta _ => cases same
  | rule member _ => exact absurd same (ne_inst_of_headConst_none (leftAlgebraic _ member) _ rfl)

theorem Par.srt_inv (leftAlgebraic : theory.LeftAlgebraic) {sort : Srt} {target : Term}
    (par : Par theory (.srt sort) target) : target = .srt sort := by
  generalize same : Term.srt sort = source at par
  cases par with
  | var other => cases same
  | srt other => rfl
  | con name => cases same
  | pi _ _ => cases same
  | lam _ _ => cases same
  | app _ _ => cases same
  | beta _ _ => cases same
  | delta _ => cases same
  | rule member _ => exact absurd same (ne_inst_of_headConst_none (leftAlgebraic _ member) _ rfl)

theorem Par.pi_inv (leftAlgebraic : theory.LeftAlgebraic) {domain body target : Term}
    (par : Par theory (.pi domain body) target) :
    ∃ domain' body', target = .pi domain' body' ∧ Par theory domain domain' ∧
      Par theory body body' := by
  generalize same : Term.pi domain body = source at par
  cases par with
  | var other => cases same
  | srt other => cases same
  | con name => cases same
  | pi domains bodies =>
      obtain ⟨rfl, rfl⟩ := Term.pi.inj same
      exact ⟨_, _, rfl, domains, bodies⟩
  | lam _ _ => cases same
  | app _ _ => cases same
  | beta _ _ => cases same
  | delta _ => cases same
  | rule member _ => exact absurd same (ne_inst_of_headConst_none (leftAlgebraic _ member) _ rfl)

theorem Par.lam_inv (leftAlgebraic : theory.LeftAlgebraic) {domain body target : Term}
    (par : Par theory (.lam domain body) target) :
    ∃ domain' body', target = .lam domain' body' ∧ Par theory domain domain' ∧
      Par theory body body' := by
  generalize same : Term.lam domain body = source at par
  cases par with
  | var other => cases same
  | srt other => cases same
  | con name => cases same
  | pi _ _ => cases same
  | lam domains bodies =>
      obtain ⟨rfl, rfl⟩ := Term.lam.inj same
      exact ⟨_, _, rfl, domains, bodies⟩
  | app _ _ => cases same
  | beta _ _ => cases same
  | delta _ => cases same
  | rule member _ => exact absurd same (ne_inst_of_headConst_none (leftAlgebraic _ member) _ rfl)

/-- A parallel reduction of a constant keeps it, unfolds it, or applies a
rule to it. -/
theorem Par.con_inv {name : String} {target : Term} (par : Par theory (.con name) target) :
    target = .con name ∨ theory.body name = some target ∨
      ∃ rule first second, theory.rule rule ∧ Term.con name = inst first rule.lhs ∧
        target = inst second rule.rhs ∧ ∀ index, Par theory (first index) (second index) := by
  generalize same : Term.con name = source at par
  cases par with
  | var other => cases same
  | srt other => cases same
  | con other => exact Or.inl rfl
  | pi _ _ => cases same
  | lam _ _ => cases same
  | app _ _ => cases same
  | beta _ _ => cases same
  | delta defined =>
      obtain rfl := Term.con.inj same
      exact Or.inr (Or.inl defined)
  | rule member pointwise => exact Or.inr (Or.inr ⟨_, _, _, member, rfl, rfl, pointwise⟩)

/-- A parallel reduction of an application reduces its two parts, contracts
it as a beta redex, or applies a rule to it. -/
theorem Par.app_inv {function argument target : Term}
    (par : Par theory (.app function argument) target) :
    (∃ function' argument', target = .app function' argument' ∧ Par theory function function' ∧
        Par theory argument argument') ∨
      (∃ domain body body' argument', function = .lam domain body ∧
        target = subst0 argument' body' ∧ Par theory body body' ∧
          Par theory argument argument') ∨
      ∃ rule first second, theory.rule rule ∧ Term.app function argument = inst first rule.lhs ∧
        target = inst second rule.rhs ∧ ∀ index, Par theory (first index) (second index) := by
  generalize same : Term.app function argument = source at par
  cases par with
  | var other => cases same
  | srt other => cases same
  | con other => cases same
  | pi _ _ => cases same
  | lam _ _ => cases same
  | app functions arguments =>
      obtain ⟨rfl, rfl⟩ := Term.app.inj same
      exact Or.inl ⟨_, _, rfl, functions, arguments⟩
  | beta bodies arguments =>
      obtain ⟨rfl, rfl⟩ := Term.app.inj same
      exact Or.inr (Or.inl ⟨_, _, _, _, rfl, rfl, bodies, arguments⟩)
  | delta _ => cases same
  | rule member pointwise => exact Or.inr (Or.inr ⟨_, _, _, member, rfl, rfl, pointwise⟩)

/-! ### Parallel moves into a pattern -/

/-- The statement of the parallel-moves lemma at one pattern: a parallel
reduction of an instance is an instance, the assigned terms being reduced in
parallel and those the pattern does not mention left as they are. -/
def MovesInto (theory : Theory) (part : Term) : Prop :=
  ∀ (first : Nat → Term) (target : Term), Par theory (inst first part) target →
    ∃ second : Nat → Term, target = inst second part ∧
      (∀ index, Par theory (first index) (second index)) ∧
      ∀ index, index ∉ patternVars part → second index = first index

/-- Parallel moves into the two parts of an application give parallel moves
into the application, when the parts share no variable. -/
theorem MovesInto.app {function argument : Term}
    (functionAlgebraic : algebraic true function = true)
    (argumentAlgebraic : algebraic false argument = true)
    (nodup : (patternVars function ++ patternVars argument).Nodup)
    (functionMoves : MovesInto theory function) (argumentMoves : MovesInto theory argument)
    {first : Nat → Term} {function' argument' : Term}
    (functions : Par theory (inst first function) function')
    (arguments : Par theory (inst first argument) argument') :
    ∃ second : Nat → Term, Term.app function' argument' = inst second (.app function argument) ∧
      (∀ index, Par theory (first index) (second index)) ∧
      ∀ index, index ∉ patternVars (.app function argument) → second index = first index := by
  obtain ⟨-, -, disjoint⟩ := List.nodup_append.mp nodup
  obtain ⟨middle, rfl, firstMiddle, middleKeeps⟩ := functionMoves first function' functions
  have argumentSame : inst first argument = inst middle argument :=
    inst_congr_patternVars argumentAlgebraic fun index member =>
      (middleKeeps index fun inFunction => disjoint index inFunction index member rfl).symm
  rw [argumentSame] at arguments
  obtain ⟨last, rfl, middleLast, lastKeeps⟩ := argumentMoves middle argument' arguments
  have functionSame : inst middle function = inst last function :=
    inst_congr_patternVars functionAlgebraic fun index member =>
      (lastKeeps index fun inArgument => disjoint index member index inArgument rfl).symm
  refine ⟨last, by rw [inst_app, functionSame], fun index => ?_, fun index absent => ?_⟩
  · by_cases inArgument : index ∈ patternVars argument
    · by_cases inFunction : index ∈ patternVars function
      · exact (disjoint index inFunction index inArgument rfl).elim
      · have kept := middleKeeps index inFunction
        have moved := middleLast index
        rwa [kept] at moved
    · rw [lastKeeps index inArgument]
      exact firstMiddle index
  · have notFunction : index ∉ patternVars function := fun member =>
      absent (List.mem_append_left _ member)
    have notArgument : index ∉ patternVars argument := fun member =>
      absent (List.mem_append_right _ member)
    rw [lastKeeps index notArgument, middleKeeps index notFunction]

/-- **Parallel moves**: a parallel reduction of an instance of a linear
algebraic pattern whose headed parts are inert is an instance of the pattern,
the assigned terms being reduced in parallel. -/
theorem movesInto_of_inert (leftAlgebraic : theory.LeftAlgebraic) :
    ∀ part : Term, algebraic false part = true → (patternVars part).Nodup →
      (∀ inner ∈ part :: subpatterns part, algebraic true inner = true → Inert theory inner) →
        MovesInto theory part := by
  intro part
  induction part with
  | var variable_ =>
      intro _ _ _ first target par
      rw [inst_var] at par
      refine ⟨Function.update first variable_ target, by simp, fun index => ?_,
        fun index absent => ?_⟩
      · by_cases same : index = variable_
        · rw [same, Function.update_self]
          exact par
        · rw [Function.update_of_ne same]
          exact .refl _
      · exact Function.update_of_ne (fun same => absent (by simp [patternVars, same])) _ _
  | srt sort =>
      intro _ _ _ first target par
      have same : target = .srt sort := Par.srt_inv leftAlgebraic par
      exact ⟨first, same, fun index => .refl _, fun _ _ => rfl⟩
  | con name =>
      intro _ _ inert first target par
      have here : Inert theory (.con name) := inert _ (List.mem_cons_self ..) rfl
      have constant : Par theory (.con name) target := par
      rcases constant.con_inv with same | defined | ⟨rule, left, right, member, isInstance, _, _⟩
      · exact ⟨first, same, fun index => .refl _, fun _ _ => rfl⟩
      · rw [here.undefined name rfl] at defined
        cases defined
      · exact (here.unmatched rule first left member isInstance).elim
  | pi domain body _ _ => intro isAlgebraic; simp [algebraic] at isAlgebraic
  | lam domain body _ _ => intro isAlgebraic; simp [algebraic] at isAlgebraic
  | app function argument ihFunction ihArgument =>
      intro isAlgebraic nodup inert first target par
      obtain ⟨functionAlgebraic, argumentAlgebraic⟩ := algebraic_app.mp isAlgebraic
      obtain ⟨functionNodup, argumentNodup, -⟩ := List.nodup_append.mp nodup
      have here : Inert theory (.app function argument) :=
        inert _ (List.mem_cons_self ..) (algebraic_app.mpr ⟨functionAlgebraic, argumentAlgebraic⟩)
      have functionMoves : MovesInto theory function :=
        ihFunction (algebraic_of_headed functionAlgebraic) functionNodup fun inner member =>
          inert inner (List.mem_cons_of_mem _ (by
            rcases List.mem_cons.mp member with rfl | deeper
            · simp [subpatterns]
            · simp [subpatterns, deeper]))
      have argumentMoves : MovesInto theory argument :=
        ihArgument argumentAlgebraic argumentNodup fun inner member =>
          inert inner (List.mem_cons_of_mem _ (by
            rcases List.mem_cons.mp member with rfl | deeper
            · simp [subpatterns]
            · simp [subpatterns, deeper]))
      have application : Par theory (.app (inst first function) (inst first argument)) target := par
      rcases application.app_inv with ⟨function', argument', rfl, functions, arguments⟩ |
        ⟨domain, body, _, _, isLam, _, _, _⟩ | ⟨rule, left, right, member, isInstance, _, _⟩
      · exact MovesInto.app functionAlgebraic argumentAlgebraic nodup functionMoves argumentMoves
          functions arguments
      · exact absurd isLam.symm (ne_inst_of_headConst_none functionAlgebraic first rfl)
      · exact (here.unmatched rule first left member isInstance).elim

/-- **A parallel reduction of an instance of a left side** either reduces the
assigned terms and keeps the instance, or applies the rule. -/
theorem Par.rule_inv (orthogonal : theory.Orthogonal) {rule : RewriteRule}
    (member : theory.rule rule) {first : Nat → Term} {target : Term}
    (par : Par theory (inst first rule.lhs) target) :
    (∃ second, target = inst second rule.lhs ∧ ∀ index, Par theory (first index) (second index)) ∨
      ∃ second, target = inst second rule.rhs ∧
        ∀ index ∈ patternVars rule.lhs, Par theory (first index) (second index) := by
  have applied : ∀ (other : RewriteRule) (left right : Nat → Term), theory.rule other →
      inst first rule.lhs = inst left other.lhs → target = inst right other.rhs →
        (∀ index, Par theory (left index) (right index)) →
          ∃ second, target = inst second rule.rhs ∧
            ∀ index ∈ patternVars rule.lhs, Par theory (first index) (second index) := by
    intro other left right otherMember isInstance result pointwise
    obtain rfl := orthogonal.rootUnique rule other member otherMember first left isInstance
    refine ⟨right, result, fun index present => ?_⟩
    rw [eq_of_inst_eq (orthogonal.leftAlgebraic _ member) isInstance index present]
    exact pointwise index
  have headed := orthogonal.leftAlgebraic rule member
  have linear := orthogonal.leftLinear rule member
  have inert := orthogonal.nonOverlapping rule member
  have undefined := orthogonal.leftUndefined rule member
  generalize rule.lhs = left at par applied headed linear inert undefined
  cases left with
  | var index => simp [algebraic] at headed
  | srt sort => simp [algebraic] at headed
  | pi domain body => simp [algebraic] at headed
  | lam domain body => simp [algebraic] at headed
  | con name =>
      have constant : Par theory (.con name) target := par
      rcases constant.con_inv with same | defined | ⟨other, left, right, otherMember, isInstance,
        result, pointwise⟩
      · exact Or.inl ⟨first, same, fun index => .refl _⟩
      · rw [undefined name rfl] at defined
        cases defined
      · exact Or.inr (applied other left right otherMember isInstance result pointwise)
  | app function argument =>
      obtain ⟨functionAlgebraic, argumentAlgebraic⟩ := algebraic_app.mp headed
      obtain ⟨functionNodup, argumentNodup, -⟩ := List.nodup_append.mp linear
      have functionMoves : MovesInto theory function :=
        movesInto_of_inert orthogonal.leftAlgebraic function (algebraic_of_headed functionAlgebraic)
          functionNodup fun inner inside => inert inner (by
            rcases List.mem_cons.mp inside with rfl | deeper
            · simp [subpatterns]
            · simp [subpatterns, deeper])
      have argumentMoves : MovesInto theory argument :=
        movesInto_of_inert orthogonal.leftAlgebraic argument argumentAlgebraic argumentNodup
          fun inner inside => inert inner (by
            rcases List.mem_cons.mp inside with rfl | deeper
            · simp [subpatterns]
            · simp [subpatterns, deeper])
      have application : Par theory (.app (inst first function) (inst first argument)) target := par
      rcases application.app_inv with ⟨function', argument', rfl, functions, arguments⟩ |
        ⟨domain, body, _, _, isLam, _, _, _⟩ |
        ⟨other, left, right, otherMember, isInstance, result, pointwise⟩
      · obtain ⟨second, same, moved, -⟩ :=
          MovesInto.app functionAlgebraic argumentAlgebraic linear functionMoves argumentMoves
            functions arguments
        exact Or.inl ⟨second, same, moved⟩
      · exact absurd isLam.symm (ne_inst_of_headConst_none functionAlgebraic first rfl)
      · exact Or.inr (applied other left right otherMember isInstance result pointwise)

/-! ## Complete development -/

/-- The term is an instance of the left side of a declared rule. -/
def Theory.Matches (theory : Theory) (term : Term) : Prop :=
  ∃ rule assignment, theory.rule rule ∧ term = inst assignment rule.lhs

/-- **Complete development**: contract every redex of a term. -/
inductive Dev (theory : Theory) : Term → Term → Prop where
  | var (index : Nat) : Dev theory (.var index) (.var index)
  | srt (sort : Srt) : Dev theory (.srt sort) (.srt sort)
  | con {name : String} : theory.body name = none → ¬ theory.Matches (.con name) →
      Dev theory (.con name) (.con name)
  | delta {name : String} {term : Term} : theory.body name = some term →
      Dev theory (.con name) term
  | pi {domain domain' body body' : Term} :
      Dev theory domain domain' → Dev theory body body' →
        Dev theory (.pi domain body) (.pi domain' body')
  | lam {domain domain' body body' : Term} :
      Dev theory domain domain' → Dev theory body body' →
        Dev theory (.lam domain body) (.lam domain' body')
  | app {function function' argument argument' : Term} :
      Dev theory function function' → Dev theory argument argument' →
        (∀ domain body, function ≠ .lam domain body) →
          ¬ theory.Matches (.app function argument) →
            Dev theory (.app function argument) (.app function' argument')
  | beta {domain body body' argument argument' : Term} :
      Dev theory body body' → Dev theory argument argument' →
        Dev theory (.app (.lam domain body) argument) (subst0 argument' body')
  | rule {rule : RewriteRule} {first second : Nat → Term} :
      theory.rule rule → (∀ index, Dev theory (first index) (second index)) →
        Dev theory (inst first rule.lhs) (inst second rule.rhs)

/-- Every term below a size has a complete development. -/
theorem Dev.exists_below (leftAlgebraic : theory.LeftAlgebraic) :
    ∀ (bound : Nat) (term : Term), sizeOf term < bound → ∃ developed, Dev theory term developed := by
  intro bound
  induction bound with
  | zero => intro term small; omega
  | succ bound ih =>
      intro term small
      by_cases matched : theory.Matches term
      · obtain ⟨rule, assignment, member, rfl⟩ := matched
        let trimmed : Nat → Term := fun index =>
          if index ∈ patternVars rule.lhs then assignment index else .srt .type
        have same : inst assignment rule.lhs = inst trimmed rule.lhs :=
          inst_congr_patternVars (leftAlgebraic rule member) fun index present => by
            simp [trimmed, present]
        have each : ∀ index, ∃ developed, Dev theory (trimmed index) developed := by
          intro index
          by_cases present : index ∈ patternVars rule.lhs
          · have smaller := sizeOf_lt_inst assignment (leftAlgebraic rule member) present
            obtain ⟨developed, development⟩ := ih (assignment index) (by omega)
            exact ⟨developed, by simpa [trimmed, present] using development⟩
          · exact ⟨.srt .type, by simpa [trimmed, present] using Dev.srt (theory := theory) .type⟩
        obtain ⟨second, developments⟩ := Classical.skolem.mp each
        exact ⟨inst second rule.rhs, same ▸ Dev.rule member developments⟩
      · cases term with
        | var index => exact ⟨_, .var index⟩
        | srt sort => exact ⟨_, .srt sort⟩
        | con name =>
            cases defined : theory.body name with
            | none => exact ⟨_, .con defined matched⟩
            | some body => exact ⟨_, .delta defined⟩
        | pi domain body =>
            rw [Term.pi.sizeOf_spec] at small
            obtain ⟨domain', domains⟩ := ih domain (by omega)
            obtain ⟨body', bodies⟩ := ih body (by omega)
            exact ⟨_, .pi domains bodies⟩
        | lam domain body =>
            rw [Term.lam.sizeOf_spec] at small
            obtain ⟨domain', domains⟩ := ih domain (by omega)
            obtain ⟨body', bodies⟩ := ih body (by omega)
            exact ⟨_, .lam domains bodies⟩
        | app function argument =>
            rw [Term.app.sizeOf_spec] at small
            obtain ⟨argument', arguments⟩ := ih argument (by omega)
            by_cases isLam : ∃ domain body, function = .lam domain body
            · obtain ⟨domain, body, rfl⟩ := isLam
              rw [Term.lam.sizeOf_spec] at small
              obtain ⟨body', bodies⟩ := ih body (by omega)
              exact ⟨_, .beta bodies arguments⟩
            · obtain ⟨function', functions⟩ := ih function (by omega)
              exact ⟨_, .app functions arguments
                (fun domain body same => isLam ⟨domain, body, same⟩) matched⟩

/-- **Every term has a complete development.** -/
theorem Dev.exists (leftAlgebraic : theory.LeftAlgebraic) (term : Term) :
    ∃ developed, Dev theory term developed :=
  Dev.exists_below leftAlgebraic (sizeOf term + 1) term (Nat.lt_succ_self _)

/-- **The triangle**: every parallel reduct of a term reduces in parallel to
its complete development. -/
theorem Dev.triangle (orthogonal : theory.Orthogonal) {source developed : Term}
    (development : Dev theory source developed) :
    ∀ target : Term, Par theory source target → Par theory target developed := by
  have leftAlgebraic := orthogonal.leftAlgebraic
  induction development with
  | var index =>
      intro target par
      rw [Par.var_inv leftAlgebraic par]
      exact .var index
  | srt sort =>
      intro target par
      rw [Par.srt_inv leftAlgebraic par]
      exact .srt sort
  | @con name undefined unmatched =>
      intro target par
      rcases par.con_inv with same | defined | ⟨rule, first, second, member, isInstance, _, _⟩
      · rw [same]
        exact .con name
      · rw [undefined] at defined
        cases defined
      · exact (unmatched ⟨rule, first, member, isInstance⟩).elim
  | @delta name term defined =>
      intro target par
      rcases par.con_inv with same | unfolded | ⟨rule, first, second, member, isInstance, _, _⟩
      · rw [same]
        exact .delta defined
      · obtain rfl := Option.some.inj (unfolded.symm.trans defined)
        exact .refl _
      · have headed := leftAlgebraic rule member
        have undefined := orthogonal.leftUndefined rule member
        generalize rule.lhs = left at isInstance headed undefined
        cases left with
        | var index => simp [algebraic] at headed
        | srt sort => simp [algebraic] at headed
        | pi domain body => simp [algebraic] at headed
        | lam domain body => simp [algebraic] at headed
        | app function argument => cases isInstance
        | con other =>
            obtain rfl := Term.con.inj isInstance
            rw [undefined name rfl] at defined
            cases defined
  | pi _ _ ihDomain ihBody =>
      intro target par
      obtain ⟨domain', body', rfl, domains, bodies⟩ := Par.pi_inv leftAlgebraic par
      exact .pi (ihDomain _ domains) (ihBody _ bodies)
  | lam _ _ ihDomain ihBody =>
      intro target par
      obtain ⟨domain', body', rfl, domains, bodies⟩ := Par.lam_inv leftAlgebraic par
      exact .lam (ihDomain _ domains) (ihBody _ bodies)
  | app _ _ notLam unmatched ihFunction ihArgument =>
      intro target par
      rcases par.app_inv with ⟨function', argument', rfl, functions, arguments⟩ |
        ⟨domain, body, _, _, isLam, _, _, _⟩ | ⟨rule, first, second, member, isInstance, _, _⟩
      · exact .app (ihFunction _ functions) (ihArgument _ arguments)
      · exact (notLam domain body isLam).elim
      · exact (unmatched ⟨rule, first, member, isInstance⟩).elim
  | @beta domain body body' argument argument' _ _ ihBody ihArgument =>
      intro target par
      rcases par.app_inv with ⟨function', argument'', rfl, functions, arguments⟩ |
        ⟨domain₀, body₀, body'', argument'', isLam, rfl, bodies, arguments⟩ |
        ⟨rule, first, second, member, isInstance, _, _⟩
      · obtain ⟨domain'', body'', rfl, -, bodies⟩ := Par.lam_inv leftAlgebraic functions
        exact .beta (ihBody _ bodies) (ihArgument _ arguments)
      · obtain ⟨rfl, rfl⟩ := Term.lam.inj isLam
        exact Par.substTerm orthogonal.closedBodies (ihBody _ bodies) (ihArgument _ arguments) 0
      · have headed := leftAlgebraic rule member
        generalize rule.lhs = left at isInstance headed
        cases left with
        | var index => simp [algebraic] at headed
        | srt sort => simp [algebraic] at headed
        | pi domain body => simp [algebraic] at headed
        | lam domain body => simp [algebraic] at headed
        | con other => cases isInstance
        | app function operand =>
            obtain ⟨functionSame, -⟩ := Term.app.inj isInstance
            exact absurd functionSame
              (ne_inst_of_headConst_none (algebraic_app.mp headed).1 first rfl)
  | @rule rule first second member _ ih =>
      intro target par
      rcases Par.rule_inv orthogonal member par with ⟨third, rfl, moved⟩ | ⟨third, rfl, moved⟩
      · exact .rule member fun index => ih index _ (moved index)
      · let mixed : Nat → Term := fun index =>
          if index ∈ patternVars rule.lhs then third index else second index
        have same : inst third rule.rhs = inst mixed rule.rhs :=
          orthogonal.rightDetermined rule member third mixed fun index present => by
            simp [mixed, present]
        rw [same]
        refine Par.instantiate orthogonal.closedBodies (fun index => ?_) rule.rhs 0
        by_cases present : index ∈ patternVars rule.lhs
        · simpa [mixed, present] using ih index _ (moved index present)
        · simpa [mixed, present] using Par.refl (theory := theory) (second index)

/-! ## The diamond property and confluence -/

/-- **Parallel reduction has the diamond property.** -/
theorem Par.diamond (orthogonal : theory.Orthogonal) {source left right : Term}
    (leftPar : Par theory source left) (rightPar : Par theory source right) :
    ∃ common, Par theory left common ∧ Par theory right common := by
  obtain ⟨developed, development⟩ := Dev.exists orthogonal.leftAlgebraic source
  exact ⟨developed, development.triangle orthogonal _ leftPar,
    development.triangle orthogonal _ rightPar⟩

/-- Finitely many parallel reductions are a reduction. -/
theorem reduces_of_parStar (closed : theory.ClosedBodies) {source target : Term}
    (steps : Relation.ReflTransGen (Par theory) source target) : Reduces theory source target := by
  induction steps with
  | refl => exact .refl
  | tail _ par ih => exact ih.trans (par.reduces closed)

/-- A reduction is finitely many parallel reductions. -/
theorem parStar_of_reduces {source target : Term} (reduces : Reduces theory source target) :
    Relation.ReflTransGen (Par theory) source target := by
  induction reduces with
  | refl => exact .refl
  | tail _ step ih => exact ih.tail step.par

/-- **Reduction is confluent in every orthogonal theory.** -/
theorem confluent_of_orthogonal (orthogonal : theory.Orthogonal) : Confluent (Step theory) := by
  intro source left right leftReduces rightReduces
  have join : ∀ a b c : Term, Par theory a b → Par theory a c →
      ∃ d, Relation.ReflGen (Par theory) b d ∧ Relation.ReflTransGen (Par theory) c d := by
    intro a b c leftPar rightPar
    obtain ⟨common, leftJoin, rightJoin⟩ := Par.diamond orthogonal leftPar rightPar
    exact ⟨common, .single leftJoin, .single rightJoin⟩
  obtain ⟨common, leftJoin, rightJoin⟩ := Relation.church_rosser join
    (parStar_of_reduces leftReduces) (parStar_of_reduces rightReduces)
  exact ⟨common, reduces_of_parStar orthogonal.closedBodies leftJoin,
    reduces_of_parStar orthogonal.closedBodies rightJoin⟩

/-- **Beta reduction is confluent.** -/
theorem confluent_empty : Confluent (Step Theory.empty) :=
  confluent_of_orthogonal Theory.empty_orthogonal

/-- **Beta with closed transparent definitions is confluent.** -/
theorem confluent_of_no_rule (closed : theory.ClosedBodies) (empty : ∀ rule, ¬ theory.rule rule) :
    Confluent (Step theory) :=
  confluent_of_orthogonal (Theory.orthogonal_of_no_rule closed empty)

#print axioms Par.reduces
#print axioms Par.substTerm
#print axioms movesInto_of_inert
#print axioms Par.rule_inv
#print axioms Dev.exists
#print axioms Dev.triangle
#print axioms Par.diamond
#print axioms confluent_of_orthogonal
#print axioms confluent_empty
#print axioms confluent_of_no_rule

end Mettapedia.GSLT.Dedukti
