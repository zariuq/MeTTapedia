import Mettapedia.GSLT.Dedukti.Substitution
import Mettapedia.GSLT.LanguageDef.LF.ContextualBetaEtaClosure
import Mettapedia.Logic.Relation.Normalization

/-!
# Declared rewrite rules on λΠ terms

A theory of the λΠ-calculus modulo rewriting is a signature together with
declared rewrite rules.  This module is the untyped half: the terms `T`, and
the rewrites `R` of the triple `(T, E, R)`.

* `Theory` gives each constant a type, optionally a transparent definition,
  and a set of declared rules.  `Theory.ofSig` reads an existing finite
  signature `LFTyping.Sig`, whose transparent definitions become unfoldings.
* `RootStep` is one contraction at the root: beta, the unfolding of a
  definition, or an instance of a declared rule.
* `Step` is a root contraction at one position, the position being an existing
  one-hole context `LFContextualBetaEta.Context`.  `Reduces` is its
  reflexive-transitive closure and `Conv` the equivalence it generates: the
  conversion that the typing rule of the calculus uses.

With no declared rule the reduction is exactly the existing beta-delta
reduction of `LFTyping` (`reduces_ofSig_iff`).  The existing conversion of
that module is conversion by a common reduct; it is contained in `Conv`, and
equals it exactly when the reduction is confluent (`lfConv_iff_conv`).

## Where confluence is used

Confluence is not assumed anywhere in the definitions.  It is a hypothesis of
the following statements, each of which fails to be provable without it.

* `conv_iff_joinable`: conversion is decided by reducing both sides.
* `Conv.pi_injective`: convertible products have convertible domains and
  convertible codomains.  This is the step on which preservation of types
  under beta rests.  It also needs `Theory.Headed`: the left side of every
  declared rule is headed by a constant, so no rule rewrites a product.
* `Conv.srt_injective`, `Conv.srt_ne_pi`: a sort is convertible to no other
  sort and to no product.
* `not_conv_of_normal`: two distinct normal terms are not convertible.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Dedukti

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.LF
open Mettapedia.GSLT.LanguageDef.LFTyping (Sig sigT lookupBody lift subst subst0)
open Mettapedia.GSLT.LanguageDef.LFContextualBetaEta (Context)
open Mettapedia.Logic.Relation (Confluent IsNormal)

/-- A declared rewrite rule.  The free variables of the two sides are the
pattern variables. -/
structure RewriteRule where
  lhs : Term
  rhs : Term
  deriving DecidableEq, Repr

/-- A theory of the λΠ-calculus modulo rewriting: typed constants, transparent
definitions and declared rewrite rules. -/
structure Theory where
  /-- The declared type of a constant. -/
  constType : String → Option Term
  /-- The body of a transparent definition. -/
  body : String → Option Term
  /-- The declared rewrite rules. -/
  rule : RewriteRule → Prop

namespace Theory

/-- The theory with no constant and no rule: beta alone. -/
def empty : Theory where
  constType := fun _ => none
  body := fun _ => none
  rule := fun _ => False

/-- The theory of an existing finite signature with a list of declared rules. -/
def ofSig (signature : Sig) (rules : List RewriteRule) : Theory where
  constType := sigT signature
  body := lookupBody signature
  rule := fun rule => rule ∈ rules

/-- The left side of every declared rule is headed by a constant. -/
def Headed (theory : Theory) : Prop :=
  ∀ rule, theory.rule rule → ∃ name, headConst rule.lhs = some name

/-- One theory is contained in another. -/
structure Extends (small large : Theory) : Prop where
  constType : ∀ name type, small.constType name = some type → large.constType name = some type
  body : ∀ name term, small.body name = some term → large.body name = some term
  rule : ∀ rule, small.rule rule → large.rule rule

theorem Extends.refl (theory : Theory) : theory.Extends theory :=
  ⟨fun _ _ same => same, fun _ _ same => same, fun _ member => member⟩

theorem Extends.trans {first second third : Theory} (lower : first.Extends second)
    (upper : second.Extends third) : first.Extends third :=
  ⟨fun name type same => upper.constType name type (lower.constType name type same),
    fun name term same => upper.body name term (lower.body name term same),
    fun rule member => upper.rule rule (lower.rule rule member)⟩

theorem empty_headed : empty.Headed := fun _ member => member.elim

end Theory

variable {theory : Theory}

/-- One contraction at the root. -/
inductive RootStep (theory : Theory) : Term → Term → Prop where
  | beta (domain body argument : Term) :
      RootStep theory (.app (.lam domain body) argument) (subst0 argument body)
  | delta {name : String} {term : Term} :
      theory.body name = some term → RootStep theory (.con name) term
  | rule {rule : RewriteRule} (assignment : Nat → Term) :
      theory.rule rule → RootStep theory (inst assignment rule.lhs) (inst assignment rule.rhs)

/-- One contraction at one position. -/
inductive Step (theory : Theory) : Term → Term → Prop where
  | inContext (context : Context) {source target : Term} :
      RootStep theory source target → Step theory (context.plug source) (context.plug target)

/-- Reduction: finitely many steps. -/
abbrev Reduces (theory : Theory) : Term → Term → Prop := Relation.ReflTransGen (Step theory)

/-- **The declared conversion**: the equivalence generated by the steps. -/
abbrev Conv (theory : Theory) : Term → Term → Prop := Relation.EqvGen (Step theory)

/-- Two terms with a common reduct. -/
abbrev Joinable (theory : Theory) : Term → Term → Prop := Relation.Join (Reduces theory)

/-! ## Closure under positions -/

theorem Step.root {source target : Term} (step : RootStep theory source target) :
    Step theory source target :=
  Step.inContext .hole step

theorem Step.plug (context : Context) {source target : Term} (step : Step theory source target) :
    Step theory (context.plug source) (context.plug target) := by
  cases step with
  | inContext inner root =>
      rw [← Context.plug_comp, ← Context.plug_comp]
      exact .inContext (context.comp inner) root

theorem Reduces.plug (context : Context) {source target : Term}
    (reduces : Reduces theory source target) :
    Reduces theory (context.plug source) (context.plug target) := by
  induction reduces with
  | refl => exact .refl
  | tail _ step ih => exact ih.tail (step.plug context)

theorem Conv.plug (context : Context) {source target : Term} (convertible : Conv theory source target) :
    Conv theory (context.plug source) (context.plug target) := by
  induction convertible with
  | rel _ _ step => exact .rel _ _ (step.plug context)
  | refl _ => exact .refl _
  | symm _ _ _ ih => exact .symm _ _ ih
  | trans _ _ _ _ _ ihFirst ihSecond => exact .trans _ _ _ ihFirst ihSecond

theorem Reduces.conv {source target : Term} (reduces : Reduces theory source target) :
    Conv theory source target := by
  induction reduces with
  | refl => exact .refl _
  | tail _ step ih => exact .trans _ _ _ ih (.rel _ _ step)

theorem Conv.of_eq {source target : Term} (same : source = target) : Conv theory source target :=
  same ▸ .refl _

theorem Reduces.app {function function' argument argument' : Term}
    (functions : Reduces theory function function') (arguments : Reduces theory argument argument') :
    Reduces theory (.app function argument) (.app function' argument') :=
  (functions.plug (.appFunction .hole argument)).trans (arguments.plug (.appArgument function' .hole))

theorem Reduces.pi {domain domain' body body' : Term} (domains : Reduces theory domain domain')
    (bodies : Reduces theory body body') : Reduces theory (.pi domain body) (.pi domain' body') :=
  (domains.plug (.piDomain .hole body)).trans (bodies.plug (.piBody domain' .hole))

theorem Reduces.lam {domain domain' body body' : Term} (domains : Reduces theory domain domain')
    (bodies : Reduces theory body body') : Reduces theory (.lam domain body) (.lam domain' body') :=
  (domains.plug (.lamDomain .hole body)).trans (bodies.plug (.lamBody domain' .hole))

theorem Conv.app {function function' argument argument' : Term}
    (functions : Conv theory function function') (arguments : Conv theory argument argument') :
    Conv theory (.app function argument) (.app function' argument') :=
  .trans _ _ _ (functions.plug (.appFunction .hole argument))
    (arguments.plug (.appArgument function' .hole))

theorem Conv.pi {domain domain' body body' : Term} (domains : Conv theory domain domain')
    (bodies : Conv theory body body') : Conv theory (.pi domain body) (.pi domain' body') :=
  .trans _ _ _ (domains.plug (.piDomain .hole body)) (bodies.plug (.piBody domain' .hole))

theorem Conv.lam {domain domain' body body' : Term} (domains : Conv theory domain domain')
    (bodies : Conv theory body body') : Conv theory (.lam domain body) (.lam domain' body') :=
  .trans _ _ _ (domains.plug (.lamDomain .hole body)) (bodies.plug (.lamBody domain' .hole))

/-- A beta contraction, as a conversion. -/
theorem Conv.beta (domain body argument : Term) :
    Conv theory (.app (.lam domain body) argument) (subst0 argument body) :=
  .rel _ _ (Step.root (.beta domain body argument))

/-- An instance of a declared rule, as a conversion. -/
theorem Conv.rule {rule : RewriteRule} (member : theory.rule rule) (assignment : Nat → Term) :
    Conv theory (inst assignment rule.lhs) (inst assignment rule.rhs) :=
  .rel _ _ (Step.root (.rule assignment member))

/-! ## Containment of theories -/

theorem RootStep.mono {small large : Theory} (contained : small.Extends large) {source target : Term}
    (step : RootStep small source target) : RootStep large source target := by
  cases step with
  | beta domain body argument => exact .beta domain body argument
  | delta defined => exact .delta (contained.body _ _ defined)
  | rule assignment member => exact .rule assignment (contained.rule _ member)

theorem Step.mono {small large : Theory} (contained : small.Extends large) {source target : Term}
    (step : Step small source target) : Step large source target := by
  cases step with
  | inContext context root => exact .inContext context (root.mono contained)

theorem Reduces.mono {small large : Theory} (contained : small.Extends large) {source target : Term}
    (reduces : Reduces small source target) : Reduces large source target := by
  induction reduces with
  | refl => exact .refl
  | tail _ step ih => exact ih.tail (step.mono contained)

theorem Conv.mono {small large : Theory} (contained : small.Extends large) {source target : Term}
    (convertible : Conv small source target) : Conv large source target := by
  induction convertible with
  | rel _ _ step => exact .rel _ _ (step.mono contained)
  | refl _ => exact .refl _
  | symm _ _ _ ih => exact .symm _ _ ih
  | trans _ _ _ _ _ ihFirst ihSecond => exact .trans _ _ _ ihFirst ihSecond

/-! ## Where a step can be -/

theorem Step.app_inv {function argument target : Term}
    (step : Step theory (.app function argument) target) :
    RootStep theory (.app function argument) target ∨
      (∃ function', Step theory function function' ∧ target = .app function' argument) ∨
      (∃ argument', Step theory argument argument' ∧ target = .app function argument') := by
  generalize same : Term.app function argument = source at step
  cases step with
  | inContext context root =>
      cases context with
      | hole =>
          simp only [Context.plug] at same
          subst same
          exact Or.inl root
      | appFunction rest other =>
          simp only [Context.plug, Term.app.injEq] at same
          obtain ⟨rfl, rfl⟩ := same
          exact Or.inr (Or.inl ⟨_, .inContext rest root, rfl⟩)
      | appArgument other rest =>
          simp only [Context.plug, Term.app.injEq] at same
          obtain ⟨rfl, rfl⟩ := same
          exact Or.inr (Or.inr ⟨_, .inContext rest root, rfl⟩)
      | piDomain rest other => simp [Context.plug] at same
      | piBody other rest => simp [Context.plug] at same
      | lamDomain rest other => simp [Context.plug] at same
      | lamBody other rest => simp [Context.plug] at same

theorem Step.pi_inv {domain body target : Term} (step : Step theory (.pi domain body) target) :
    RootStep theory (.pi domain body) target ∨
      (∃ domain', Step theory domain domain' ∧ target = .pi domain' body) ∨
      (∃ body', Step theory body body' ∧ target = .pi domain body') := by
  generalize same : Term.pi domain body = source at step
  cases step with
  | inContext context root =>
      cases context with
      | hole =>
          simp only [Context.plug] at same
          subst same
          exact Or.inl root
      | piDomain rest other =>
          simp only [Context.plug, Term.pi.injEq] at same
          obtain ⟨rfl, rfl⟩ := same
          exact Or.inr (Or.inl ⟨_, .inContext rest root, rfl⟩)
      | piBody other rest =>
          simp only [Context.plug, Term.pi.injEq] at same
          obtain ⟨rfl, rfl⟩ := same
          exact Or.inr (Or.inr ⟨_, .inContext rest root, rfl⟩)
      | appFunction rest other => simp [Context.plug] at same
      | appArgument other rest => simp [Context.plug] at same
      | lamDomain rest other => simp [Context.plug] at same
      | lamBody other rest => simp [Context.plug] at same

theorem Step.lam_inv {domain body target : Term} (step : Step theory (.lam domain body) target) :
    RootStep theory (.lam domain body) target ∨
      (∃ domain', Step theory domain domain' ∧ target = .lam domain' body) ∨
      (∃ body', Step theory body body' ∧ target = .lam domain body') := by
  generalize same : Term.lam domain body = source at step
  cases step with
  | inContext context root =>
      cases context with
      | hole =>
          simp only [Context.plug] at same
          subst same
          exact Or.inl root
      | lamDomain rest other =>
          simp only [Context.plug, Term.lam.injEq] at same
          obtain ⟨rfl, rfl⟩ := same
          exact Or.inr (Or.inl ⟨_, .inContext rest root, rfl⟩)
      | lamBody other rest =>
          simp only [Context.plug, Term.lam.injEq] at same
          obtain ⟨rfl, rfl⟩ := same
          exact Or.inr (Or.inr ⟨_, .inContext rest root, rfl⟩)
      | appFunction rest other => simp [Context.plug] at same
      | appArgument other rest => simp [Context.plug] at same
      | piDomain rest other => simp [Context.plug] at same
      | piBody other rest => simp [Context.plug] at same

theorem Step.srt_inv {sort : Srt} {target : Term} (step : Step theory (.srt sort) target) :
    RootStep theory (.srt sort) target := by
  generalize same : Term.srt sort = source at step
  cases step with
  | inContext context root =>
      cases context <;> simp only [Context.plug] at same ⊢ <;> first
        | (subst same; exact root)
        | cases same

theorem Step.var_inv {index : Nat} {target : Term} (step : Step theory (.var index) target) :
    RootStep theory (.var index) target := by
  generalize same : Term.var index = source at step
  cases step with
  | inContext context root =>
      cases context <;> simp only [Context.plug] at same ⊢ <;> first
        | (subst same; exact root)
        | cases same

theorem Step.con_inv {name : String} {target : Term} (step : Step theory (.con name) target) :
    RootStep theory (.con name) target := by
  generalize same : Term.con name = source at step
  cases step with
  | inContext context root =>
      cases context <;> simp only [Context.plug] at same ⊢ <;> first
        | (subst same; exact root)
        | cases same

theorem RootStep.con_inv {name : String} {target : Term}
    (step : RootStep theory (.con name) target) :
    theory.body name = some target ∨
      ∃ rule assignment, theory.rule rule ∧ inst assignment rule.lhs = .con name ∧
        target = inst assignment rule.rhs := by
  generalize same : Term.con name = source at step
  cases step with
  | beta domain body argument => cases same
  | delta defined => cases same; exact Or.inl defined
  | rule assignment member => exact Or.inr ⟨_, assignment, member, rfl, rfl⟩

/-- A root contraction of a term whose head is not a constant is beta: no
declared rule applies, when the left sides are headed by constants. -/
theorem RootStep.headConst_or_beta (headed : theory.Headed) {source target : Term}
    (step : RootStep theory source target) :
    (∃ domain body argument, source = .app (.lam domain body) argument) ∨
      ∃ name, headConst source = some name := by
  cases step with
  | beta domain body argument => exact Or.inl ⟨domain, body, argument, rfl⟩
  | delta defined => exact Or.inr ⟨_, rfl⟩
  | rule assignment member =>
      obtain ⟨name, head⟩ := headed _ member
      exact Or.inr ⟨name, headConst_instantiate assignment 0 head⟩

theorem RootStep.not_pi (headed : theory.Headed) {domain body target : Term} :
    ¬ RootStep theory (.pi domain body) target := by
  intro step
  rcases step.headConst_or_beta headed with ⟨_, _, _, same⟩ | ⟨_, head⟩
  · cases same
  · simp [headConst] at head

theorem RootStep.not_srt (headed : theory.Headed) {sort : Srt} {target : Term} :
    ¬ RootStep theory (.srt sort) target := by
  intro step
  rcases step.headConst_or_beta headed with ⟨_, _, _, same⟩ | ⟨_, head⟩
  · cases same
  · simp [headConst] at head

theorem RootStep.not_var (headed : theory.Headed) {index : Nat} {target : Term} :
    ¬ RootStep theory (.var index) target := by
  intro step
  rcases step.headConst_or_beta headed with ⟨_, _, _, same⟩ | ⟨_, head⟩
  · cases same
  · simp [headConst] at head

theorem RootStep.not_lam (headed : theory.Headed) {domain body target : Term} :
    ¬ RootStep theory (.lam domain body) target := by
  intro step
  rcases step.headConst_or_beta headed with ⟨_, _, _, same⟩ | ⟨_, head⟩
  · cases same
  · simp [headConst] at head

/-- A theory defines a constant when it has a definition for it or a declared
rule whose left side it heads. -/
def Theory.Defines (theory : Theory) (name : String) : Prop :=
  theory.body name ≠ none ∨ ∃ rule, theory.rule rule ∧ headConst rule.lhs = some name

/-- A root contraction is beta or happens at a defined head. -/
theorem RootStep.defines (headed : theory.Headed) {source target : Term}
    (step : RootStep theory source target) :
    (∃ domain body argument, source = .app (.lam domain body) argument) ∨
      ∃ name, headConst source = some name ∧ theory.Defines name := by
  cases step with
  | beta domain body argument => exact Or.inl ⟨domain, body, argument, rfl⟩
  | @delta name term defined =>
      exact Or.inr ⟨name, rfl, Or.inl fun undefined => by rw [undefined] at defined; cases defined⟩
  | @rule rule assignment member =>
      obtain ⟨name, head⟩ := headed _ member
      exact Or.inr ⟨name, headConst_instantiate assignment 0 head, Or.inr ⟨rule, member, head⟩⟩

/-- **A head that the theory does not define is kept by every step.** -/
theorem Step.headConst_rigid (headed : theory.Headed) {name : String}
    (rigid : ¬ theory.Defines name) :
    ∀ {source target : Term}, headConst source = some name → Step theory source target →
      headConst target = some name := by
  intro source
  induction source with
  | var index => intro target head; simp [headConst] at head
  | srt sort => intro target head; simp [headConst] at head
  | pi domain body _ _ => intro target head; simp [headConst] at head
  | lam domain body _ _ => intro target head; simp [headConst] at head
  | con other =>
      intro target head step
      rcases step.con_inv.defines headed with ⟨_, _, _, same⟩ | ⟨defined, isHead, defines⟩
      · cases same
      · rw [head] at isHead
        cases isHead
        exact (rigid defines).elim
  | app function argument ihFunction _ =>
      intro target head step
      have functionHead : headConst function = some name := head
      rcases step.app_inv with root | ⟨next, inner, rfl⟩ | ⟨next, inner, rfl⟩
      · rcases root.defines headed with ⟨_, _, _, same⟩ | ⟨defined, isHead, defines⟩
        · cases same
          simp [headConst] at functionHead
        · rw [head] at isHead
          cases isHead
          exact (rigid defines).elim
      · exact ihFunction (target := next) functionHead inner
      · exact functionHead

theorem Reduces.headConst_rigid (headed : theory.Headed) {name : String}
    (rigid : ¬ theory.Defines name) {source target : Term} (head : headConst source = some name)
    (reduces : Reduces theory source target) : headConst target = some name := by
  induction reduces with
  | refl => exact head
  | tail _ step ih => exact Step.headConst_rigid headed rigid ih step

/-- A term with an undefined head has no root contraction. -/
theorem RootStep.not_of_rigid (headed : theory.Headed) {name : String}
    (rigid : ¬ theory.Defines name) {source target : Term} (head : headConst source = some name) :
    ¬ RootStep theory source target := by
  intro step
  rcases step.defines headed with ⟨_, _, _, same⟩ | ⟨defined, isHead, defines⟩
  · rw [same] at head
    simp [headConst] at head
  · rw [head] at isHead
    cases isHead
    exact rigid defines

/-- Two terms with different undefined heads have no common reduct. -/
theorem not_joinable_of_heads (headed : theory.Headed) {first second : String}
    (firstRigid : ¬ theory.Defines first) (secondRigid : ¬ theory.Defines second)
    (distinct : first ≠ second) {left right : Term} (leftHead : headConst left = some first)
    (rightHead : headConst right = some second) : ¬ Joinable theory left right := by
  rintro ⟨common, leftReduces, rightReduces⟩
  have one := leftReduces.headConst_rigid headed firstRigid leftHead
  have two := rightReduces.headConst_rigid headed secondRigid rightHead
  exact distinct (Option.some.inj (one.symm.trans two))

/-- A sort has no step. -/
theorem srt_normal (headed : theory.Headed) (sort : Srt) : IsNormal (Step theory) (.srt sort) :=
  fun _ step => RootStep.not_srt headed step.srt_inv

/-- A variable has no step. -/
theorem var_normal (headed : theory.Headed) (index : Nat) : IsNormal (Step theory) (.var index) :=
  fun _ step => RootStep.not_var headed step.var_inv

/-- A product reduces only to a product, componentwise. -/
theorem Reduces.pi_inv (headed : theory.Headed) {domain body target : Term}
    (reduces : Reduces theory (.pi domain body) target) :
    ∃ domain' body', target = .pi domain' body' ∧ Reduces theory domain domain' ∧
      Reduces theory body body' := by
  induction reduces with
  | refl => exact ⟨domain, body, rfl, .refl, .refl⟩
  | tail _ step ih =>
      obtain ⟨domain', body', rfl, domains, bodies⟩ := ih
      rcases step.pi_inv with root | ⟨next, inner, rfl⟩ | ⟨next, inner, rfl⟩
      · exact (RootStep.not_pi headed root).elim
      · exact ⟨next, body', rfl, domains.tail inner, bodies⟩
      · exact ⟨domain', next, rfl, domains, bodies.tail inner⟩

/-! ## Where confluence is used -/

/-- **Under confluence, conversion is decided by reducing both sides.** -/
theorem conv_iff_joinable (confluent : Confluent (Step theory)) {left right : Term} :
    Conv theory left right ↔ Joinable theory left right :=
  confluent.eqvGen_iff_join

/-- Two terms with a common reduct are convertible, in every theory. -/
theorem Joinable.conv {left right : Term} (joinable : Joinable theory left right) :
    Conv theory left right := by
  obtain ⟨common, leftReduces, rightReduces⟩ := joinable
  exact .trans _ _ _ leftReduces.conv (.symm _ _ rightReduces.conv)

/-- Two distinct normal terms have no common reduct. -/
theorem not_joinable_of_normal {left right : Term} (leftNormal : IsNormal (Step theory) left)
    (rightNormal : IsNormal (Step theory) right) (distinct : left ≠ right) :
    ¬ Joinable theory left right := by
  rintro ⟨common, leftReduces, rightReduces⟩
  exact distinct ((leftNormal.reflTransGen_eq leftReduces).symm.trans
    (rightNormal.reflTransGen_eq rightReduces))

/-- **Under confluence, two distinct normal terms are not convertible.** -/
theorem not_conv_of_normal (confluent : Confluent (Step theory)) {left right : Term}
    (leftNormal : IsNormal (Step theory) left) (rightNormal : IsNormal (Step theory) right)
    (distinct : left ≠ right) : ¬ Conv theory left right :=
  fun convertible => not_joinable_of_normal leftNormal rightNormal distinct
    ((conv_iff_joinable confluent).mp convertible)

/-- **Under confluence, convertible products have convertible parts.** -/
theorem Conv.pi_injective (confluent : Confluent (Step theory)) (headed : theory.Headed)
    {domain domain' body body' : Term}
    (convertible : Conv theory (.pi domain body) (.pi domain' body')) :
    Conv theory domain domain' ∧ Conv theory body body' := by
  obtain ⟨common, leftReduces, rightReduces⟩ := (conv_iff_joinable confluent).mp convertible
  obtain ⟨leftDomain, leftBody, rfl, leftDomains, leftBodies⟩ := leftReduces.pi_inv headed
  obtain ⟨rightDomain, rightBody, same, rightDomains, rightBodies⟩ := rightReduces.pi_inv headed
  cases same
  exact ⟨.trans _ _ _ leftDomains.conv (.symm _ _ rightDomains.conv),
    .trans _ _ _ leftBodies.conv (.symm _ _ rightBodies.conv)⟩

/-- **Under confluence, convertible sorts are equal.** -/
theorem Conv.srt_injective (confluent : Confluent (Step theory)) (headed : theory.Headed)
    {first second : Srt} (convertible : Conv theory (.srt first) (.srt second)) : first = second := by
  obtain ⟨common, leftReduces, rightReduces⟩ := (conv_iff_joinable confluent).mp convertible
  have left := (srt_normal headed first).reflTransGen_eq leftReduces
  have right := (srt_normal headed second).reflTransGen_eq rightReduces
  exact Term.srt.inj (left.symm.trans right)

/-- **Under confluence, a sort is convertible to no product.** -/
theorem Conv.srt_ne_pi (confluent : Confluent (Step theory)) (headed : theory.Headed)
    {sort : Srt} {domain body : Term} : ¬ Conv theory (.srt sort) (.pi domain body) := by
  intro convertible
  obtain ⟨common, leftReduces, rightReduces⟩ := (conv_iff_joinable confluent).mp convertible
  have left := (srt_normal headed sort).reflTransGen_eq leftReduces
  obtain ⟨_, _, same, _, _⟩ := rightReduces.pi_inv headed
  rw [left] at same
  cases same

/-! ## The existing beta-delta reduction is the case of no declared rule -/

theorem lfReduces_plug {signature : Sig} (context : Context) {source target : Term}
    (reduces : LFTyping.Reduces signature source target) :
    LFTyping.Reduces signature (context.plug source) (context.plug target) := by
  induction context with
  | hole => exact reduces
  | piDomain rest body ih => exact .pi ih .refl
  | piBody domain rest ih => exact .pi .refl ih
  | lamDomain rest body ih => exact .lam ih .refl
  | lamBody domain rest ih => exact .lam .refl ih
  | appFunction rest argument ih => exact .app ih .refl
  | appArgument function rest ih => exact .app .refl ih

theorem lfReduces_of_step {signature : Sig} {source target : Term}
    (step : Step (Theory.ofSig signature []) source target) :
    LFTyping.Reduces signature source target := by
  cases step with
  | inContext context root =>
      apply lfReduces_plug
      cases root with
      | beta domain body argument => exact .beta
      | delta defined => exact .delta defined
      | rule assignment member => exact absurd member List.not_mem_nil

/-- **With no declared rule, reduction is the existing beta-delta reduction.** -/
theorem reduces_ofSig_iff (signature : Sig) {source target : Term} :
    Reduces (Theory.ofSig signature []) source target ↔ LFTyping.Reduces signature source target := by
  constructor
  · intro reduces
    induction reduces with
    | refl => exact .refl
    | tail _ step ih => exact .trans ih (lfReduces_of_step step)
  · intro reduces
    induction reduces with
    | refl => exact .refl
    | beta => exact .single (Step.root (.beta _ _ _))
    | delta defined => exact .single (Step.root (.delta defined))
    | app _ _ ihFunction ihArgument => exact Reduces.app ihFunction ihArgument
    | pi _ _ ihDomain ihBody => exact Reduces.pi ihDomain ihBody
    | lam _ _ ihDomain ihBody => exact Reduces.lam ihDomain ihBody
    | trans _ _ ihFirst ihSecond => exact ihFirst.trans ihSecond

/-- The existing conversion, by a common reduct, is contained in the declared
conversion. -/
theorem conv_of_lfConv {signature : Sig} {left right : Term}
    (convertible : LFTyping.Conv signature left right) :
    Conv (Theory.ofSig signature []) left right := by
  cases convertible with
  | common leftReduces rightReduces =>
      exact Joinable.conv ⟨_, (reduces_ofSig_iff signature).mpr leftReduces,
        (reduces_ofSig_iff signature).mpr rightReduces⟩

/-- **Where confluence is used**: the existing conversion by a common reduct
is the declared conversion exactly when reduction is confluent on the pair. -/
theorem lfConv_iff_conv {signature : Sig} (confluent : Confluent (Step (Theory.ofSig signature [])))
    {left right : Term} :
    LFTyping.Conv signature left right ↔ Conv (Theory.ofSig signature []) left right := by
  refine ⟨conv_of_lfConv, fun convertible => ?_⟩
  obtain ⟨common, leftReduces, rightReduces⟩ := (conv_iff_joinable confluent).mp convertible
  exact .common ((reduces_ofSig_iff signature).mp leftReduces)
    ((reduces_ofSig_iff signature).mp rightReduces)

/-! ## A sound test for normal terms -/

/-- A necessary condition for a term to be an instance of a pattern: the
shapes agree outside the pattern variables.  Beneath a binder nothing is
tested. -/
def firstOrderMatch : Term → Term → Bool
  | .var _, _ => true
  | .con name, .con other => name == other
  | .srt sort, .srt other => sort == other
  | .app function argument, .app function' argument' =>
      firstOrderMatch function function' && firstOrderMatch argument argument'
  | .pi _ _, .pi _ _ => true
  | .lam _ _, .lam _ _ => true
  | _, _ => false

theorem firstOrderMatch_instantiate (pattern : Term) (assignment : Nat → Term) :
    firstOrderMatch pattern (inst assignment pattern) = true := by
  induction pattern with
  | var index => rfl
  | srt sort => simp [inst, instantiate, firstOrderMatch]
  | con name => simp [inst, instantiate, firstOrderMatch]
  | pi domain body _ _ => rfl
  | lam domain body _ _ => rfl
  | app function argument ihFunction ihArgument =>
      simp only [inst, instantiate, firstOrderMatch, Bool.and_eq_true]
      exact ⟨ihFunction, ihArgument⟩

/-- Whether a term is a beta redex. -/
def isBetaRedex : Term → Bool
  | .app (.lam _ _) _ => true
  | _ => false

/-- Whether a term is a constant that may have a definition. -/
def mayUnfold (rigid : String → Bool) : Term → Bool
  | .con name => !rigid name
  | _ => false

/-- A sound over-approximation of "is a redex at the root". -/
def mayContract (rigid : String → Bool) (rules : List RewriteRule) (term : Term) : Bool :=
  isBetaRedex term || mayUnfold rigid term || rules.any fun rule => firstOrderMatch rule.lhs term

/-- A sound test for "has no step". -/
def normalTest (rigid : String → Bool) (rules : List RewriteRule) : Term → Bool
  | .app function argument =>
      !mayContract rigid rules (.app function argument) && normalTest rigid rules function &&
        normalTest rigid rules argument
  | .pi domain body =>
      !mayContract rigid rules (.pi domain body) && normalTest rigid rules domain &&
        normalTest rigid rules body
  | .lam domain body =>
      !mayContract rigid rules (.lam domain body) && normalTest rigid rules domain &&
        normalTest rigid rules body
  | term => !mayContract rigid rules term

/-- A finite description of a theory that is enough to test for normal terms:
which constants have no definition, and a list containing every declared rule. -/
structure Theory.Cover (theory : Theory) where
  rigid : String → Bool
  rules : List RewriteRule
  rigid_sound : ∀ name, rigid name = true → theory.body name = none
  rules_sound : ∀ rule, theory.rule rule → rule ∈ rules

theorem mayContract_of_rootStep (cover : theory.Cover) {source target : Term}
    (step : RootStep theory source target) : mayContract cover.rigid cover.rules source = true := by
  cases step with
  | beta domain body argument => simp [mayContract, isBetaRedex]
  | @delta name term defined =>
      have transparent : cover.rigid name = false := by
        cases known : cover.rigid name with
        | false => rfl
        | true => rw [cover.rigid_sound name known] at defined; cases defined
      simp [mayContract, mayUnfold, transparent]
  | @rule rule assignment member =>
      have found : (cover.rules.any fun other =>
          firstOrderMatch other.lhs (inst assignment rule.lhs)) = true :=
        List.any_eq_true.mpr ⟨rule, cover.rules_sound rule member,
          firstOrderMatch_instantiate rule.lhs assignment⟩
      unfold mayContract
      rw [found, Bool.or_true]

/-- **The test is sound**: a term that passes has no step. -/
theorem normal_of_normalTest (cover : theory.Cover) :
    ∀ term : Term, normalTest cover.rigid cover.rules term = true → IsNormal (Step theory) term := by
  intro term
  induction term with
  | var index =>
      intro passed target step
      have contracts := mayContract_of_rootStep cover step.var_inv
      simp [normalTest, contracts] at passed
  | srt sort =>
      intro passed target step
      have contracts := mayContract_of_rootStep cover step.srt_inv
      simp [normalTest, contracts] at passed
  | con name =>
      intro passed target step
      have contracts := mayContract_of_rootStep cover step.con_inv
      simp [normalTest, contracts] at passed
  | pi domain body ihDomain ihBody =>
      intro passed target step
      simp only [normalTest, Bool.and_eq_true, Bool.not_eq_true'] at passed
      rcases step.pi_inv with root | ⟨_, inner, _⟩ | ⟨_, inner, _⟩
      · rw [mayContract_of_rootStep cover root] at passed
        exact absurd passed.1.1 (by simp)
      · exact ihDomain passed.1.2 _ inner
      · exact ihBody passed.2 _ inner
  | lam domain body ihDomain ihBody =>
      intro passed target step
      simp only [normalTest, Bool.and_eq_true, Bool.not_eq_true'] at passed
      rcases step.lam_inv with root | ⟨_, inner, _⟩ | ⟨_, inner, _⟩
      · rw [mayContract_of_rootStep cover root] at passed
        exact absurd passed.1.1 (by simp)
      · exact ihDomain passed.1.2 _ inner
      · exact ihBody passed.2 _ inner
  | app function argument ihFunction ihArgument =>
      intro passed target step
      simp only [normalTest, Bool.and_eq_true, Bool.not_eq_true'] at passed
      rcases step.app_inv with root | ⟨_, inner, _⟩ | ⟨_, inner, _⟩
      · rw [mayContract_of_rootStep cover root] at passed
        exact absurd passed.1.1 (by simp)
      · exact ihFunction passed.1.2 _ inner
      · exact ihArgument passed.2 _ inner

/-- The cover of the theory of a finite signature without definitions. -/
def Theory.coverOfRules (signature : Sig) (rules : List RewriteRule)
    (undefined : ∀ name, lookupBody signature name = none) :
    (Theory.ofSig signature rules).Cover where
  rigid := fun _ => true
  rules := rules
  rigid_sound := fun name _ => undefined name
  rules_sound := fun _ member => member

#print axioms Step.plug
#print axioms reduces_ofSig_iff
#print axioms lfConv_iff_conv
#print axioms Conv.pi_injective
#print axioms Conv.srt_injective
#print axioms not_conv_of_normal
#print axioms normal_of_normalTest
#print axioms Step.headConst_rigid
#print axioms not_joinable_of_heads

end Mettapedia.GSLT.Dedukti
