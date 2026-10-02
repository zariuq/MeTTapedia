import Mettapedia.Logic.HOL.ReplayCore

/-!
# Replay with acceptance and derivability defined as least predicates

`Logic.HOL.ReplayCore` presents certificate replay as a theory of
higher-order logic in the deep embedding with seven axioms: three recursion
equations of acceptance, three closure clauses of derivability, and induction
on certificates.  Here acceptance and derivability are not constants but
λ-terms, the least relations closed under their clauses by the impredicative
definition.  The theory says less and proves more.

**Signature.**  The constructors of certificates, certificate lists and
premise lists, and the rule relation `rule l ps g`, the graph of the local
rule map.

**Definitions.**
* `derDef := λg. ∀ D E. derRuleClosed D E → E goalsNil → derConsClosed D E → D g`,
  and `dersDef` with conclusion `E ps`;
* `accDef := λg c. ∀ A B. accNodeClosed A B → B goalsNil nil → accConsClosed A B → A g c`,
  and `accsDef` with conclusion `B ps cs`;
* `certDef`/`certsDef`: the genuine certificates, the least predicates closed
  under the certificate constructors.

**Theorems with no assumption** (derivations in `ExtDerivation` from any list
of assumptions, in particular the empty one):
* the closure clauses of derivability and the introduction clauses of
  acceptance (`derRule_derivation`, `accNodeIntro_derivation`, …);
* `soundness_derivation`: `∀ c g. acc g c → der g`;
* `completeness_derivation`: `∀ g. der g → ∃ c. acc g c`;
* `leastBelowSolutions_derivation`, `solutionCompleteness_derivation`: every
  pair satisfying the three replay equations contains the least acceptance and
  is complete;
* `genuineInduction_derivation`: induction on genuine certificates;
* `genuineSolutionSoundness_derivation`: on genuine certificates, every
  solution of the replay equations is sound.

**The theory** (`theory`): induction on certificates (`certInduction`) and
freeness of their constructors (`nodeInjective`, `consInjective`,
`consNotNil`).  No axiom mentions acceptance or derivability.
* Freeness gives the elimination halves of the replay equations, so the least
  acceptance is a solution (`accNode_derivation`, `accsNil_derivation`,
  `accsCons_derivation`).
* Induction gives that every solution is contained in the least acceptance
  (`solutionsBelowLeast_derivation`), hence unique (`solutionUnique_derivation`)
  and sound (`solutionSoundness_derivation`).
* Each derivation from axioms derives the implication from exactly the axioms
  it uses, so the dependency is part of the derived sentence.

**The old theory is interpreted.**  `interpretOld` sends the old constants to
the constructors and to the definitions.  Every old axiom translates to a
theorem (`translate_theory`) and every old derivation transports
(`transport`, `soundness_transported`).

**The derivations are intuitionistic.**  `ExtDerivation` has no excluded
middle and the signature has no choice or description operator; Kripke–Henkin
certificates: `soundness_kripkeConsequence`, `completeness_kripkeConsequence`,
`solutionSoundness_kripkeConsequence`.

**Controls.**
* `FreeJunkModel`: free constructors and a loop certificate.  Freeness holds,
  induction fails, and "is the loop" solves the replay equations while nothing
  is derivable (`freeness_do_not_derive_solutionSoundness`).
* `CollapsedNodeModel`, `CollapsedListModel`, `CollapsedConsModel`: each
  validates induction and two freeness axioms and refutes the third with its
  equation (`nodeInjective_needed`, `consNotNil_needed`,
  `consInjective_needed`).
* `OldTopModel`: a model of the whole old theory in which derivability is not
  least; completeness fails (`oldTheory_does_not_derive_completeness`), while
  its translation is a theorem with no assumption.

**Note on elaboration.**  Instantiating bound variables one at a time stacks
substitutions, and the elaborator is slow when two different stacks over the
same closed λ-term meet.  The simultaneous instantiations `inst2`, `inst3`,
`inst4` with `allE2`, `allE3`, `allE4`, `exI2` keep each step at one
substitution, and type ascriptions put one side of every junction in normal
form.  The substitution laws behind them (`subst_subst`, `subst_after_rename`,
`subst_vars`, …) are proved here by structural recursion with congruence
alone, so the object derivations depend on no axiom of the metalogic.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HOL.ReplayCoreDefined

open Mettapedia.Logic.HOL
open Mettapedia.Logic.HOL.ReplayCore (BaseSort goal label cert certs goals certPredicate
  certsPredicate)

universe w

/-- The primitive constants: the certificate constructors, the premise-list
constructors, and the rule relation.  Acceptance and derivability are not
constants; they are λ-terms over these. -/
inductive Symbol : Ty BaseSort → Type where
  | node : Symbol (label ⇒ certs ⇒ cert)
  | nil : Symbol certs
  | cons : Symbol (cert ⇒ certs ⇒ certs)
  | goalsNil : Symbol goals
  | goalsCons : Symbol (goal ⇒ goals ⇒ goals)
  | rule : Symbol (label ⇒ goals ⇒ goal ⇒ .prop)

abbrev Expr (Γ : Ctx BaseSort) (τ : Ty BaseSort) := Term Symbol Γ τ
abbrev Sentence (Γ : Ctx BaseSort) := Formula Symbol Γ

/-- Predicates on goals. -/
abbrev goalPredicate : Ty BaseSort := goal ⇒ .prop
/-- Predicates on premise lists. -/
abbrev goalsPredicate : Ty BaseSort := goals ⇒ .prop
/-- Relations between goals and certificates. -/
abbrev acceptance : Ty BaseSort := goal ⇒ cert ⇒ .prop
/-- Relations between premise lists and certificate lists. -/
abbrev listAcceptance : Ty BaseSort := goals ⇒ certs ⇒ .prop

/-! ## Simultaneous instantiation

Instantiating several bound variables one after another stacks
substitutions.  The lemmas below replace such a stack by one simultaneous
substitution, so that every derivation step meets a single substitution of
a concrete formula. -/

section Simultaneous

variable {Const : Ty BaseSort → Type} {Γ : Ctx BaseSort}

/-! ### Substitution lemmas proved by structural recursion

The general laws of renaming and substitution, proved by structural recursion
with congruence alone, so that the derivations below use no axiom of the
metalogic. -/

/-- Renamings that agree pointwise rename alike. -/
theorem rename_congr {Γ₁ Γ₂ : Ctx BaseSort} {ρ ρ' : Rename BaseSort Γ₁ Γ₂}
    (h : ∀ {τ} (v : Var Γ₁ τ), ρ v = ρ' v) :
    ∀ {τ} (t : Term Const Γ₁ τ), rename ρ t = rename ρ' t
  | _, .var v => congrArg Term.var (h v)
  | _, .const _ => rfl
  | _, .app f t => congrArg₂ Term.app (rename_congr h f) (rename_congr h t)
  | _, .lam t => congrArg Term.lam (rename_congr (fun v => by
      cases v with
      | vz => rfl
      | vs v => exact congrArg Var.vs (h v)) t)
  | _, .top => rfl
  | _, .bot => rfl
  | _, .and φ ψ => congrArg₂ Term.and (rename_congr h φ) (rename_congr h ψ)
  | _, .or φ ψ => congrArg₂ Term.or (rename_congr h φ) (rename_congr h ψ)
  | _, .imp φ ψ => congrArg₂ Term.imp (rename_congr h φ) (rename_congr h ψ)
  | _, .not φ => congrArg Term.not (rename_congr h φ)
  | _, .eq t u => congrArg₂ Term.eq (rename_congr h t) (rename_congr h u)
  | _, .all φ => congrArg Term.all (rename_congr (fun v => by
      cases v with
      | vz => rfl
      | vs v => exact congrArg Var.vs (h v)) φ)
  | _, .ex φ => congrArg Term.ex (rename_congr (fun v => by
      cases v with
      | vz => rfl
      | vs v => exact congrArg Var.vs (h v)) φ)

/-- Two renamings in a row are one renaming. -/
theorem rename_rename {Γ₁ Γ₂ Γ₃ : Ctx BaseSort} (ρ₂ : Rename BaseSort Γ₂ Γ₃)
    (ρ₁ : Rename BaseSort Γ₁ Γ₂) :
    ∀ {τ} (t : Term Const Γ₁ τ), rename ρ₂ (rename ρ₁ t) = rename (fun v => ρ₂ (ρ₁ v)) t
  | _, .var _ => rfl
  | _, .const _ => rfl
  | _, .app f t => congrArg₂ Term.app (rename_rename ρ₂ ρ₁ f) (rename_rename ρ₂ ρ₁ t)
  | _, .lam t => congrArg Term.lam ((rename_rename (Rename.lift ρ₂) (Rename.lift ρ₁) t).trans
      (rename_congr (fun v => by cases v <;> rfl) t))
  | _, .top => rfl
  | _, .bot => rfl
  | _, .and φ ψ => congrArg₂ Term.and (rename_rename ρ₂ ρ₁ φ) (rename_rename ρ₂ ρ₁ ψ)
  | _, .or φ ψ => congrArg₂ Term.or (rename_rename ρ₂ ρ₁ φ) (rename_rename ρ₂ ρ₁ ψ)
  | _, .imp φ ψ => congrArg₂ Term.imp (rename_rename ρ₂ ρ₁ φ) (rename_rename ρ₂ ρ₁ ψ)
  | _, .not φ => congrArg Term.not (rename_rename ρ₂ ρ₁ φ)
  | _, .eq t u => congrArg₂ Term.eq (rename_rename ρ₂ ρ₁ t) (rename_rename ρ₂ ρ₁ u)
  | _, .all φ => congrArg Term.all ((rename_rename (Rename.lift ρ₂) (Rename.lift ρ₁) φ).trans
      (rename_congr (fun v => by cases v <;> rfl) φ))
  | _, .ex φ => congrArg Term.ex ((rename_rename (Rename.lift ρ₂) (Rename.lift ρ₁) φ).trans
      (rename_congr (fun v => by cases v <;> rfl) φ))

/-- Substitutions that agree pointwise substitute alike. -/
theorem subst_congr {Γ₁ Γ₂ : Ctx BaseSort} {σs τs : Subst Const Γ₁ Γ₂}
    (h : ∀ {τ} (v : Var Γ₁ τ), σs v = τs v) :
    ∀ {τ} (t : Term Const Γ₁ τ), subst σs t = subst τs t
  | _, .var v => h v
  | _, .const _ => rfl
  | _, .app f t => congrArg₂ Term.app (subst_congr h f) (subst_congr h t)
  | _, .lam t => congrArg Term.lam (subst_congr (fun v => by
      cases v with
      | vz => rfl
      | vs v => exact congrArg (rename Rename.weaken) (h v)) t)
  | _, .top => rfl
  | _, .bot => rfl
  | _, .and φ ψ => congrArg₂ Term.and (subst_congr h φ) (subst_congr h ψ)
  | _, .or φ ψ => congrArg₂ Term.or (subst_congr h φ) (subst_congr h ψ)
  | _, .imp φ ψ => congrArg₂ Term.imp (subst_congr h φ) (subst_congr h ψ)
  | _, .not φ => congrArg Term.not (subst_congr h φ)
  | _, .eq t u => congrArg₂ Term.eq (subst_congr h t) (subst_congr h u)
  | _, .all φ => congrArg Term.all (subst_congr (fun v => by
      cases v with
      | vz => rfl
      | vs v => exact congrArg (rename Rename.weaken) (h v)) φ)
  | _, .ex φ => congrArg Term.ex (subst_congr (fun v => by
      cases v with
      | vz => rfl
      | vs v => exact congrArg (rename Rename.weaken) (h v)) φ)

/-- A substitution after a renaming is one substitution. -/
theorem subst_after_rename {Γ₁ Γ₂ Γ₃ : Ctx BaseSort} (σs : Subst Const Γ₂ Γ₃)
    (ρ : Rename BaseSort Γ₁ Γ₂) :
    ∀ {τ} (t : Term Const Γ₁ τ), subst σs (rename ρ t) = subst (fun v => σs (ρ v)) t
  | _, .var _ => rfl
  | _, .const _ => rfl
  | _, .app f t => congrArg₂ Term.app (subst_after_rename σs ρ f) (subst_after_rename σs ρ t)
  | _, .lam t => congrArg Term.lam ((subst_after_rename (Subst.lift σs) (Rename.lift ρ) t).trans
      (subst_congr (fun v => by cases v <;> rfl) t))
  | _, .top => rfl
  | _, .bot => rfl
  | _, .and φ ψ => congrArg₂ Term.and (subst_after_rename σs ρ φ) (subst_after_rename σs ρ ψ)
  | _, .or φ ψ => congrArg₂ Term.or (subst_after_rename σs ρ φ) (subst_after_rename σs ρ ψ)
  | _, .imp φ ψ => congrArg₂ Term.imp (subst_after_rename σs ρ φ) (subst_after_rename σs ρ ψ)
  | _, .not φ => congrArg Term.not (subst_after_rename σs ρ φ)
  | _, .eq t u => congrArg₂ Term.eq (subst_after_rename σs ρ t) (subst_after_rename σs ρ u)
  | _, .all φ => congrArg Term.all ((subst_after_rename (Subst.lift σs) (Rename.lift ρ) φ).trans
      (subst_congr (fun v => by cases v <;> rfl) φ))
  | _, .ex φ => congrArg Term.ex ((subst_after_rename (Subst.lift σs) (Rename.lift ρ) φ).trans
      (subst_congr (fun v => by cases v <;> rfl) φ))

/-- Under one binder, a renaming after a substitution agrees pointwise with
the lifted composite. -/
theorem rename_lift_after_lift {Γ₁ Γ₂ Γ₃ : Ctx BaseSort} (ρ : Rename BaseSort Γ₂ Γ₃)
    (σs : Subst Const Γ₁ Γ₂) {σ τ : Ty BaseSort} (v : Var (σ :: Γ₁) τ) :
    rename (Rename.lift ρ) (Subst.lift σs v) = Subst.lift (fun w => rename ρ (σs w)) v := by
  cases v with
  | vz => rfl
  | vs v =>
      exact (rename_rename (Rename.lift ρ) Rename.weaken (σs v)).trans
        ((rename_congr (fun _ => rfl) (σs v)).trans
          (rename_rename Rename.weaken ρ (σs v)).symm)

/-- A renaming after a substitution is one substitution. -/
theorem rename_after_subst {Γ₁ Γ₂ Γ₃ : Ctx BaseSort} (ρ : Rename BaseSort Γ₂ Γ₃)
    (σs : Subst Const Γ₁ Γ₂) :
    ∀ {τ} (t : Term Const Γ₁ τ), rename ρ (subst σs t) = subst (fun v => rename ρ (σs v)) t
  | _, .var _ => rfl
  | _, .const _ => rfl
  | _, .app f t => congrArg₂ Term.app (rename_after_subst ρ σs f) (rename_after_subst ρ σs t)
  | _, .lam t => congrArg Term.lam ((rename_after_subst (Rename.lift ρ) (Subst.lift σs) t).trans
      (subst_congr (fun v => rename_lift_after_lift ρ σs v) t))
  | _, .top => rfl
  | _, .bot => rfl
  | _, .and φ ψ => congrArg₂ Term.and (rename_after_subst ρ σs φ) (rename_after_subst ρ σs ψ)
  | _, .or φ ψ => congrArg₂ Term.or (rename_after_subst ρ σs φ) (rename_after_subst ρ σs ψ)
  | _, .imp φ ψ => congrArg₂ Term.imp (rename_after_subst ρ σs φ) (rename_after_subst ρ σs ψ)
  | _, .not φ => congrArg Term.not (rename_after_subst ρ σs φ)
  | _, .eq t u => congrArg₂ Term.eq (rename_after_subst ρ σs t) (rename_after_subst ρ σs u)
  | _, .all φ => congrArg Term.all ((rename_after_subst (Rename.lift ρ) (Subst.lift σs) φ).trans
      (subst_congr (fun v => rename_lift_after_lift ρ σs v) φ))
  | _, .ex φ => congrArg Term.ex ((rename_after_subst (Rename.lift ρ) (Subst.lift σs) φ).trans
      (subst_congr (fun v => rename_lift_after_lift ρ σs v) φ))

/-- Substitution under one binder commutes with weakening. -/
theorem subst_lift_weaken {Γ₁ Γ₂ : Ctx BaseSort} {σ : Ty BaseSort} (σs : Subst Const Γ₁ Γ₂)
    {τ : Ty BaseSort} (t : Term Const Γ₁ τ) :
    subst (Subst.lift (σ := σ) σs) (rename Rename.weaken t) =
      rename Rename.weaken (subst σs t) :=
  (subst_after_rename _ _ t).trans ((subst_congr (fun _ => rfl) t).trans
    (rename_after_subst _ _ t).symm)

/-- Two substitutions in a row are one substitution. -/
theorem subst_subst {Γ₁ Γ₂ Γ₃ : Ctx BaseSort} (τs : Subst Const Γ₂ Γ₃)
    (σs : Subst Const Γ₁ Γ₂) :
    ∀ {τ} (t : Term Const Γ₁ τ), subst τs (subst σs t) = subst (fun v => subst τs (σs v)) t
  | _, .var _ => rfl
  | _, .const _ => rfl
  | _, .app f t => congrArg₂ Term.app (subst_subst τs σs f) (subst_subst τs σs t)
  | _, .lam t => congrArg Term.lam ((subst_subst (Subst.lift τs) (Subst.lift σs) t).trans
      (subst_congr (fun v => by
        cases v with
        | vz => rfl
        | vs v => exact subst_lift_weaken τs (σs v)) t))
  | _, .top => rfl
  | _, .bot => rfl
  | _, .and φ ψ => congrArg₂ Term.and (subst_subst τs σs φ) (subst_subst τs σs ψ)
  | _, .or φ ψ => congrArg₂ Term.or (subst_subst τs σs φ) (subst_subst τs σs ψ)
  | _, .imp φ ψ => congrArg₂ Term.imp (subst_subst τs σs φ) (subst_subst τs σs ψ)
  | _, .not φ => congrArg Term.not (subst_subst τs σs φ)
  | _, .eq t u => congrArg₂ Term.eq (subst_subst τs σs t) (subst_subst τs σs u)
  | _, .all φ => congrArg Term.all ((subst_subst (Subst.lift τs) (Subst.lift σs) φ).trans
      (subst_congr (fun v => by
        cases v with
        | vz => rfl
        | vs v => exact subst_lift_weaken τs (σs v)) φ))
  | _, .ex φ => congrArg Term.ex ((subst_subst (Subst.lift τs) (Subst.lift σs) φ).trans
      (subst_congr (fun v => by
        cases v with
        | vz => rfl
        | vs v => exact subst_lift_weaken τs (σs v)) φ))

/-- Substituting every variable by itself changes nothing. -/
theorem subst_vars {Γ₁ : Ctx BaseSort} :
    ∀ {τ} (t : Term Const Γ₁ τ), subst (fun v => .var v) t = t
  | _, .var _ => rfl
  | _, .const _ => rfl
  | _, .app f t => congrArg₂ Term.app (subst_vars f) (subst_vars t)
  | _, .lam t => congrArg Term.lam ((subst_congr (fun v => by cases v <;> rfl) t).trans
      (subst_vars t))
  | _, .top => rfl
  | _, .bot => rfl
  | _, .and φ ψ => congrArg₂ Term.and (subst_vars φ) (subst_vars ψ)
  | _, .or φ ψ => congrArg₂ Term.or (subst_vars φ) (subst_vars ψ)
  | _, .imp φ ψ => congrArg₂ Term.imp (subst_vars φ) (subst_vars ψ)
  | _, .not φ => congrArg Term.not (subst_vars φ)
  | _, .eq t u => congrArg₂ Term.eq (subst_vars t) (subst_vars u)
  | _, .all φ => congrArg Term.all ((subst_congr (fun v => by cases v <;> rfl) φ).trans
      (subst_vars φ))
  | _, .ex φ => congrArg Term.ex ((subst_congr (fun v => by cases v <;> rfl) φ).trans
      (subst_vars φ))

/-- Instantiating a weakened term gives it back. -/
theorem instantiate_weakened {σ τ : Ty BaseSort} (a : Term Const Γ σ) (t : Term Const Γ τ) :
    instantiate a (weaken t) = t :=
  (subst_after_rename _ _ t).trans ((subst_congr (fun _ => rfl) t).trans (subst_vars t))

/-- Instantiate the two innermost variables: the outer by `a`, the inner
by `b`. -/
def inst2 {σ τ : Ty BaseSort} (a : Term Const Γ σ) (b : Term Const Γ τ) :
    Subst Const (τ :: σ :: Γ) Γ
  | _, .vz => b
  | _, .vs .vz => a
  | _, .vs (.vs x) => .var x

/-- Instantiate the three innermost variables, outermost first. -/
def inst3 {σ τ υ : Ty BaseSort} (a : Term Const Γ σ) (b : Term Const Γ τ)
    (c : Term Const Γ υ) : Subst Const (υ :: τ :: σ :: Γ) Γ
  | _, .vz => c
  | _, .vs .vz => b
  | _, .vs (.vs .vz) => a
  | _, .vs (.vs (.vs x)) => .var x

/-- Instantiate the four innermost variables, outermost first. -/
def inst4 {σ τ υ ω : Ty BaseSort} (a : Term Const Γ σ) (b : Term Const Γ τ)
    (c : Term Const Γ υ) (d : Term Const Γ ω) : Subst Const (ω :: υ :: τ :: σ :: Γ) Γ
  | _, .vz => d
  | _, .vs .vz => c
  | _, .vs (.vs .vz) => b
  | _, .vs (.vs (.vs .vz)) => a
  | _, .vs (.vs (.vs (.vs x))) => .var x

theorem subst_inst2_weaken_weaken {σ τ ρ : Ty BaseSort} (a : Term Const Γ σ)
    (b : Term Const Γ τ) (t : Term Const Γ ρ) :
    subst (inst2 a b) (weaken (σ := τ) (weaken (σ := σ) t)) = t :=
  (subst_after_rename _ _ _).trans ((subst_after_rename _ _ t).trans
    ((subst_congr (fun _ => rfl) t).trans (subst_vars t)))

theorem subst_inst3_weaken3 {σ τ υ ρ : Ty BaseSort} (a : Term Const Γ σ)
    (b : Term Const Γ τ) (c : Term Const Γ υ) (t : Term Const Γ ρ) :
    subst (inst3 a b c) (weaken (σ := υ) (weaken (σ := τ) (weaken (σ := σ) t))) = t :=
  (subst_after_rename _ _ _).trans ((subst_after_rename _ _ _).trans
    ((subst_after_rename _ _ t).trans ((subst_congr (fun _ => rfl) t).trans (subst_vars t))))

/-- Two single instantiations make one simultaneous instantiation. -/
theorem instantiate_lift_single {σ τ ρ : Ty BaseSort} (a : Term Const Γ σ)
    (b : Term Const Γ τ) (φ : Term Const (τ :: σ :: Γ) ρ) :
    instantiate b (subst (Subst.lift (Subst.single a)) φ) = subst (inst2 a b) φ := by
  refine (subst_subst _ _ φ).trans (subst_congr (fun x => ?_) φ)
  cases x with
  | vz => rfl
  | vs x =>
      cases x with
      | vz => exact instantiate_weakened b a
      | vs x => rfl

theorem subst_inst2_lift_lift_single {σ τ υ ρ : Ty BaseSort} (a : Term Const Γ σ)
    (b : Term Const Γ τ) (c : Term Const Γ υ) (φ : Term Const (υ :: τ :: σ :: Γ) ρ) :
    subst (inst2 b c) (subst (Subst.lift (Subst.lift (Subst.single a))) φ) =
      subst (inst3 a b c) φ := by
  refine (subst_subst _ _ φ).trans (subst_congr (fun x => ?_) φ)
  cases x with
  | vz => rfl
  | vs x =>
      cases x with
      | vz => rfl
      | vs x =>
          cases x with
          | vz => exact subst_inst2_weaken_weaken b c a
          | vs x => rfl

theorem subst_inst2_lift_lift_inst2 {σ τ υ ω ρ : Ty BaseSort} (a : Term Const Γ σ)
    (b : Term Const Γ τ) (c : Term Const Γ υ) (d : Term Const Γ ω)
    (φ : Term Const (ω :: υ :: τ :: σ :: Γ) ρ) :
    subst (inst2 c d) (subst (Subst.lift (Subst.lift (inst2 a b))) φ) =
      subst (inst4 a b c d) φ := by
  refine (subst_subst _ _ φ).trans (subst_congr (fun x => ?_) φ)
  cases x with
  | vz => rfl
  | vs x =>
      cases x with
      | vz => rfl
      | vs x =>
          refine (subst_inst2_weaken_weaken c d (inst2 a b x)).trans ?_
          cases x with
          | vz => rfl
          | vs x =>
              cases x with
              | vz => rfl
              | vs x => rfl

theorem subst_inst3_lift3_single {σ τ υ ω ρ : Ty BaseSort} (a : Term Const Γ σ)
    (b : Term Const Γ τ) (c : Term Const Γ υ) (d : Term Const Γ ω)
    (φ : Term Const (ω :: υ :: τ :: σ :: Γ) ρ) :
    subst (inst3 b c d) (subst (Subst.lift (Subst.lift (Subst.lift (Subst.single a)))) φ) =
      subst (inst4 a b c d) φ := by
  refine (subst_subst _ _ φ).trans (subst_congr (fun x => ?_) φ)
  cases x with
  | vz => rfl
  | vs x =>
      cases x with
      | vz => rfl
      | vs x =>
          cases x with
          | vz => rfl
          | vs x =>
              cases x with
              | vz => exact subst_inst3_weaken3 b c d a
              | vs x => rfl

theorem instantiate_lift_inst2 {σ τ υ ρ : Ty BaseSort} (a : Term Const Γ σ)
    (b : Term Const Γ τ) (c : Term Const Γ υ) (φ : Term Const (υ :: τ :: σ :: Γ) ρ) :
    instantiate c (subst (Subst.lift (inst2 a b)) φ) = subst (inst3 a b c) φ := by
  refine (subst_subst _ _ φ).trans (subst_congr (fun x => ?_) φ)
  cases x with
  | vz => rfl
  | vs x =>
      refine (instantiate_weakened c (inst2 a b x)).trans ?_
      cases x with
      | vz => rfl
      | vs x =>
          cases x with
          | vz => rfl
          | vs x => rfl

theorem instantiate_app_app_weaken {σ τ : Ty BaseSort} (F : Term Const Γ (σ ⇒ τ ⇒ .prop))
    (a : Term Const Γ σ) (t : Term Const Γ τ) :
    instantiate t (.app (.app (weaken F) (weaken a)) (.var .vz)) = .app (.app F a) t := by
  change Term.app (Term.app (instantiate t (weaken F)) (instantiate t (weaken a))) t = _
  rw [instantiate_weakened, instantiate_weakened]

variable {Δ : List (Formula Const Γ)}

/-- Instantiate two quantifiers at once. -/
theorem allE2 {σ τ : Ty BaseSort} {φ : Formula Const (τ :: σ :: Γ)} (a : Term Const Γ σ)
    (b : Term Const Γ τ) (h : ExtDerivation Const Δ (.all (.all φ))) :
    ExtDerivation Const Δ (subst (inst2 a b) φ) :=
  Eq.mp (congrArg (ExtDerivation Const Δ) (instantiate_lift_single a b φ))
    (ExtDerivation.allE b (ExtDerivation.allE a h))

/-- Instantiate three quantifiers at once. -/
theorem allE3 {σ τ υ : Ty BaseSort} {φ : Formula Const (υ :: τ :: σ :: Γ)}
    (a : Term Const Γ σ) (b : Term Const Γ τ) (c : Term Const Γ υ)
    (h : ExtDerivation Const Δ (.all (.all (.all φ)))) :
    ExtDerivation Const Δ (subst (inst3 a b c) φ) :=
  Eq.mp (congrArg (ExtDerivation Const Δ) (subst_inst2_lift_lift_single a b c φ))
    (allE2 b c (ExtDerivation.allE a h))

/-- Instantiate four quantifiers at once. -/
theorem allE4 {σ τ υ ω : Ty BaseSort} {φ : Formula Const (ω :: υ :: τ :: σ :: Γ)}
    (a : Term Const Γ σ) (b : Term Const Γ τ) (c : Term Const Γ υ) (d : Term Const Γ ω)
    (h : ExtDerivation Const Δ (.all (.all (.all (.all φ))))) :
    ExtDerivation Const Δ (subst (inst4 a b c d) φ) :=
  Eq.mp (congrArg (ExtDerivation Const Δ) (subst_inst3_lift3_single a b c d φ))
    (allE3 b c d (ExtDerivation.allE a h))

/-- Instantiate one quantifier under a two-variable instantiation. -/
theorem allE_inst2 {σ τ υ : Ty BaseSort} {φ : Formula Const (υ :: τ :: σ :: Γ)}
    (a : Term Const Γ σ) (b : Term Const Γ τ) (c : Term Const Γ υ)
    (h : ExtDerivation Const Δ (subst (inst2 a b) (.all φ))) :
    ExtDerivation Const Δ (subst (inst3 a b c) φ) :=
  Eq.mp (congrArg (ExtDerivation Const Δ) (instantiate_lift_inst2 a b c φ))
    (ExtDerivation.allE c h)

/-- Instantiate two quantifiers under a two-variable instantiation. -/
theorem allE2_inst2 {σ τ υ ω : Ty BaseSort} {φ : Formula Const (ω :: υ :: τ :: σ :: Γ)}
    (a : Term Const Γ σ) (b : Term Const Γ τ) (c : Term Const Γ υ) (d : Term Const Γ ω)
    (h : ExtDerivation Const Δ (subst (inst2 a b) (.all (.all φ)))) :
    ExtDerivation Const Δ (subst (inst4 a b c d) φ) :=
  Eq.mp (congrArg (ExtDerivation Const Δ) (subst_inst2_lift_lift_inst2 a b c d φ))
    (allE2 c d h)

/-- Instantiate a quantified binary application `∀x. F a x` at `t`. -/
theorem allE_app2 {σ τ : Ty BaseSort} (F : Term Const Γ (σ ⇒ τ ⇒ .prop)) (a : Term Const Γ σ)
    (t : Term Const Γ τ)
    (h : ExtDerivation Const Δ (.all (.app (.app (weaken F) (weaken a)) (.var .vz)))) :
    ExtDerivation Const Δ (.app (.app F a) t) :=
  Eq.mp (congrArg (ExtDerivation Const Δ) (instantiate_app_app_weaken F a t))
    (ExtDerivation.allE t h)

/-- Introduce two existential quantifiers at once. -/
theorem exI2 {σ τ : Ty BaseSort} {φ : Formula Const (τ :: σ :: Γ)} (a : Term Const Γ σ)
    (b : Term Const Γ τ) (h : ExtDerivation Const Δ (subst (inst2 a b) φ)) :
    ExtDerivation Const Δ (.ex (.ex φ)) :=
  .exI a (.exI b (Eq.mpr (congrArg (ExtDerivation Const Δ) (instantiate_lift_single a b φ)) h))

end Simultaneous

variable {Γ : Ctx BaseSort}

/-! ## Terms and atomic formulas -/

def node (l : Expr Γ label) (cs : Expr Γ certs) : Expr Γ cert :=
  .app (.app (.const .node) l) cs
def nil : Expr Γ certs := .const .nil
def cons (c : Expr Γ cert) (cs : Expr Γ certs) : Expr Γ certs :=
  .app (.app (.const .cons) c) cs
def goalsNil : Expr Γ goals := .const .goalsNil
def goalsCons (g : Expr Γ goal) (gs : Expr Γ goals) : Expr Γ goals :=
  .app (.app (.const .goalsCons) g) gs
def rule (l : Expr Γ label) (ps : Expr Γ goals) (g : Expr Γ goal) : Sentence Γ :=
  .app (.app (.app (.const .rule) l) ps) g

/-- A binary predicate applied to two arguments. -/
def app2 {σ τ : Ty BaseSort} (F : Expr Γ (σ ⇒ τ ⇒ .prop)) (x : Expr Γ σ) (y : Expr Γ τ) :
    Sentence Γ :=
  .app (.app F x) y

section Variables

variable {σ₀ σ₁ σ₂ σ₃ σ₄ σ₅ σ₆ σ₇ : Ty BaseSort}

/-- The innermost bound variable. -/
abbrev v0 : Expr (σ₀ :: Γ) σ₀ := .var .vz
/-- The second bound variable, counting outwards. -/
abbrev v1 : Expr (σ₀ :: σ₁ :: Γ) σ₁ := .var (.vs .vz)
/-- The third bound variable, counting outwards. -/
abbrev v2 : Expr (σ₀ :: σ₁ :: σ₂ :: Γ) σ₂ := .var (.vs (.vs .vz))
/-- The fourth bound variable, counting outwards. -/
abbrev v3 : Expr (σ₀ :: σ₁ :: σ₂ :: σ₃ :: Γ) σ₃ := .var (.vs (.vs (.vs .vz)))
/-- The fifth bound variable, counting outwards. -/
abbrev v4 : Expr (σ₀ :: σ₁ :: σ₂ :: σ₃ :: σ₄ :: Γ) σ₄ :=
  .var (.vs (.vs (.vs (.vs .vz))))
/-- The sixth bound variable, counting outwards. -/
abbrev v5 : Expr (σ₀ :: σ₁ :: σ₂ :: σ₃ :: σ₄ :: σ₅ :: Γ) σ₅ :=
  .var (.vs (.vs (.vs (.vs (.vs .vz)))))
/-- The seventh bound variable, counting outwards. -/
abbrev v6 : Expr (σ₀ :: σ₁ :: σ₂ :: σ₃ :: σ₄ :: σ₅ :: σ₆ :: Γ) σ₆ :=
  .var (.vs (.vs (.vs (.vs (.vs (.vs .vz))))))
/-- The eighth bound variable, counting outwards. -/
abbrev v7 : Expr (σ₀ :: σ₁ :: σ₂ :: σ₃ :: σ₄ :: σ₅ :: σ₆ :: σ₇ :: Γ) σ₇ :=
  .var (.vs (.vs (.vs (.vs (.vs (.vs (.vs .vz)))))))

end Variables

/-! ## β-conversion and assumptions -/

section Beta

variable {Δ : List (Sentence Γ)}

/-- An applied λ-predicate from its β-instance. -/
theorem lam_intro {σ : Ty BaseSort} {body : Sentence (σ :: Γ)} {t : Expr Γ σ}
    (h : ExtDerivation Symbol Δ (instantiate t body)) :
    ExtDerivation Symbol Δ (.app (.lam body) t) :=
  .impE (.eqPropER (.beta t body)) h

/-- The β-instance of an applied λ-predicate. -/
theorem lam_elim {σ : Ty BaseSort} {body : Sentence (σ :: Γ)} {t : Expr Γ σ}
    (h : ExtDerivation Symbol Δ (.app (.lam body) t)) :
    ExtDerivation Symbol Δ (instantiate t body) :=
  .impE (.eqPropEL (.beta t body)) h

/-- Two β-steps for a binary λ-predicate, as one simultaneous instantiation. -/
theorem lam2_eq {σ τ : Ty BaseSort} (body : Sentence (τ :: σ :: Γ)) (t : Expr Γ σ)
    (u : Expr Γ τ) :
    ExtDerivation Symbol Δ (.eq (app2 (.lam (.lam body)) t u) (subst (inst2 t u) body)) :=
  Eq.mp (congrArg (fun φ => ExtDerivation Symbol Δ (.eq (app2 (.lam (.lam body)) t u) φ))
      (instantiate_lift_single t u body))
    (.eqTrans (.eqApp u (.beta t (.lam body)))
      (.beta u (subst (Subst.lift (Subst.single t)) body)))

/-- An applied binary λ-predicate from its β-instance. -/
theorem lam2_intro {σ τ : Ty BaseSort} {body : Sentence (τ :: σ :: Γ)} {t : Expr Γ σ}
    {u : Expr Γ τ} (h : ExtDerivation Symbol Δ (subst (inst2 t u) body)) :
    ExtDerivation Symbol Δ (app2 (.lam (.lam body)) t u) :=
  .impE (.eqPropER (lam2_eq body t u)) h

/-- The β-instance of an applied binary λ-predicate. -/
theorem lam2_elim {σ τ : Ty BaseSort} {body : Sentence (τ :: σ :: Γ)} {t : Expr Γ σ}
    {u : Expr Γ τ} (h : ExtDerivation Symbol Δ (app2 (.lam (.lam body)) t u)) :
    ExtDerivation Symbol Δ (subst (inst2 t u) body) :=
  .impE (.eqPropEL (lam2_eq body t u)) h

end Beta

section Hypotheses

variable {Δ : List (Sentence Γ)} {φ ψ₀ ψ₁ ψ₂ ψ₃ : Sentence Γ}

/-- The first assumption. -/
theorem hyp0 : ExtDerivation Symbol (φ :: Δ) φ := .hyp List.mem_cons_self
/-- The second assumption. -/
theorem hyp1 : ExtDerivation Symbol (ψ₀ :: φ :: Δ) φ :=
  .hyp (List.mem_cons_of_mem _ List.mem_cons_self)
/-- The third assumption. -/
theorem hyp2 : ExtDerivation Symbol (ψ₀ :: ψ₁ :: φ :: Δ) φ :=
  .hyp (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
/-- The fourth assumption. -/
theorem hyp3 : ExtDerivation Symbol (ψ₀ :: ψ₁ :: ψ₂ :: φ :: Δ) φ :=
  .hyp (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
    List.mem_cons_self)))
/-- The fifth assumption. -/
theorem hyp4 : ExtDerivation Symbol (ψ₀ :: ψ₁ :: ψ₂ :: ψ₃ :: φ :: Δ) φ :=
  .hyp (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
    (List.mem_cons_of_mem _ List.mem_cons_self))))

end Hypotheses

/-! ## Derivability: the least predicates closed under the rule clauses -/

/-- `∀ l ps g. rule l ps g → E ps → D g`. -/
def derRuleClosed (D : Expr Γ goalPredicate) (E : Expr Γ goalsPredicate) : Sentence Γ :=
  .all (σ := label) (.all (σ := goals) (.all (σ := goal)
    (.imp (rule v2 v1 v0)
      (.imp (.app (weaken (weaken (weaken E))) v1) (.app (weaken (weaken (weaken D))) v0)))))

/-- `E goalsNil`. -/
def derNilClosed (E : Expr Γ goalsPredicate) : Sentence Γ := .app E goalsNil

/-- `∀ g gs. D g → E gs → E (goalsCons g gs)`. -/
def derConsClosed (D : Expr Γ goalPredicate) (E : Expr Γ goalsPredicate) : Sentence Γ :=
  .all (σ := goal) (.all (σ := goals)
    (.imp (.app (weaken (weaken D)) v1)
      (.imp (.app (weaken (weaken E)) v0) (.app (weaken (weaken E)) (goalsCons v1 v0)))))

/-- The matrix of derivability, with `E = v0`, `D = v1` and the goal `v2`. -/
def derInner : Sentence (goalsPredicate :: goalPredicate :: goal :: Γ) :=
  .imp (derRuleClosed v1 v0) (.imp (derNilClosed v0) (.imp (derConsClosed v1 v0) (.app v1 v2)))

/-- The matrix of list derivability, with `E = v0`, `D = v1` and the list `v2`. -/
def dersInner : Sentence (goalsPredicate :: goalPredicate :: goals :: Γ) :=
  .imp (derRuleClosed v1 v0) (.imp (derNilClosed v0) (.imp (derConsClosed v1 v0) (.app v0 v2)))

/-- Derivability of a goal, by the impredicative definition:
`λg. ∀ D E. derRuleClosed D E → E goalsNil → derConsClosed D E → D g`. -/
def derDef : Expr Γ goalPredicate :=
  .lam (.all (σ := goalPredicate) (.all (σ := goalsPredicate) derInner))

/-- Derivability of every goal of a premise list, the second component of the
same least pair. -/
def dersDef : Expr Γ goalsPredicate :=
  .lam (.all (σ := goalPredicate) (.all (σ := goalsPredicate) dersInner))

def der (g : Expr Γ goal) : Sentence Γ := .app derDef g
def ders (ps : Expr Γ goals) : Sentence Γ := .app dersDef ps

/-- Leastness of derivability, read off its definition, at a pair `(D, E)`. -/
theorem der_elim {Δ : List (Sentence Γ)} (D : Expr Γ goalPredicate)
    (E : Expr Γ goalsPredicate) {g : Expr Γ goal} (h : ExtDerivation Symbol Δ (der g)) :
    ExtDerivation Symbol Δ (subst (inst3 g D E) derInner) :=
  Eq.mp (congrArg (ExtDerivation Symbol Δ) (subst_inst2_lift_lift_single g D E derInner))
    (allE2 D E (lam_elim h))

/-- Leastness of list derivability, at a pair `(D, E)`. -/
theorem ders_elim {Δ : List (Sentence Γ)} (D : Expr Γ goalPredicate)
    (E : Expr Γ goalsPredicate) {ps : Expr Γ goals} (h : ExtDerivation Symbol Δ (ders ps)) :
    ExtDerivation Symbol Δ (subst (inst3 ps D E) dersInner) :=
  Eq.mp (congrArg (ExtDerivation Symbol Δ) (subst_inst2_lift_lift_single ps D E dersInner))
    (allE2 D E (lam_elim h))

/-! ## The closure clauses of derivability are theorems -/

/-- `∀ l ps g. rule l ps g → ders ps → der g`. -/
def derRule : Sentence Γ :=
  .all (σ := label) (.all (σ := goals) (.all (σ := goal)
    (.imp (rule v2 v1 v0) (.imp (ders v1) (der v0)))))

/-- `ders goalsNil`. -/
def dersNil : Sentence Γ := ders goalsNil

/-- `∀ g gs. der g → ders gs → ders (goalsCons g gs)`. -/
def dersCons : Sentence Γ :=
  .all (σ := goal) (.all (σ := goals)
    (.imp (der v1) (.imp (ders v0) (ders (goalsCons v1 v0)))))

/-- The rule clause, derived: unfold `der g`, take a closed pair `(D, E)`,
unfold `ders ps` at the same pair, and apply the rule clause of `(D, E)`. -/
theorem derRule_derivation {Δ : List (Sentence Γ)} : ExtDerivation Symbol Δ derRule := by
  refine .allI (.allI (.allI (.impI (.impI ?_))))
  refine lam_intro (.allI (.allI (.impI (.impI (.impI ?_)))))
  change ExtDerivation Symbol
    (derConsClosed v1 v0 :: derNilClosed v0 :: derRuleClosed v1 v0 ::
      ders v3 :: rule v4 v3 v2 ::
        weakenHyps (weakenHyps (weakenHyps (weakenHyps (weakenHyps Δ)))))
    (.app v1 v2)
  exact .impE (.impE (allE3 v4 v3 v2 (hyp2
      (Γ := goalsPredicate :: goalPredicate :: goal :: goals :: label :: Γ)
      (φ := derRuleClosed v1 v0))) hyp4)
    (.impE (.impE (.impE (ders_elim v1 v0 (hyp3
      (Γ := goalsPredicate :: goalPredicate :: goal :: goals :: label :: Γ)
      (φ := ders v3))) hyp2) hyp1) hyp0)

/-- The empty-list clause, derived. -/
theorem dersNil_derivation {Δ : List (Sentence Γ)} : ExtDerivation Symbol Δ dersNil :=
  lam_intro (.allI (.allI (.impI (.impI (.impI hyp1)))))

/-- The nonempty-list clause, derived. -/
theorem dersCons_derivation {Δ : List (Sentence Γ)} : ExtDerivation Symbol Δ dersCons := by
  refine .allI (.allI (.impI (.impI ?_)))
  refine lam_intro (.allI (.allI (.impI (.impI (.impI ?_)))))
  change ExtDerivation Symbol
    (derConsClosed v1 v0 :: derNilClosed v0 :: derRuleClosed v1 v0 ::
      ders v2 :: der v3 :: weakenHyps (weakenHyps (weakenHyps (weakenHyps Δ))))
    (.app v0 (goalsCons v3 v2))
  exact .impE (.impE (allE2 v3 v2 (hyp0
      (Γ := goalsPredicate :: goalPredicate :: goals :: goal :: Γ)
      (φ := derConsClosed v1 v0)))
    (.impE (.impE (.impE (der_elim v1 v0 (hyp4
      (Γ := goalsPredicate :: goalPredicate :: goals :: goal :: Γ)
      (φ := der v3))) hyp2) hyp1) hyp0))
    (.impE (.impE (.impE (ders_elim v1 v0 (hyp3
      (Γ := goalsPredicate :: goalPredicate :: goals :: goal :: Γ)
      (φ := ders v2))) hyp2) hyp1) hyp0)

/-! ## Acceptance: the least relations closed under the replay clauses -/

/-- `∀ l ps g cs. rule l ps g → B ps cs → A g (node l cs)`. -/
def accNodeClosed (A : Expr Γ acceptance) (B : Expr Γ listAcceptance) : Sentence Γ :=
  .all (σ := label) (.all (σ := goals) (.all (σ := goal) (.all (σ := certs)
    (.imp (rule v3 v2 v1)
      (.imp (app2 (weaken (weaken (weaken (weaken B)))) v2 v0)
        (app2 (weaken (weaken (weaken (weaken A)))) v1 (node v3 v0)))))))

/-- `B goalsNil nil`. -/
def accNilClosed (B : Expr Γ listAcceptance) : Sentence Γ := app2 B goalsNil nil

/-- `∀ g c gs cs. A g c → B gs cs → B (goalsCons g gs) (cons c cs)`. -/
def accConsClosed (A : Expr Γ acceptance) (B : Expr Γ listAcceptance) : Sentence Γ :=
  .all (σ := goal) (.all (σ := cert) (.all (σ := goals) (.all (σ := certs)
    (.imp (app2 (weaken (weaken (weaken (weaken A)))) v3 v2)
      (.imp (app2 (weaken (weaken (weaken (weaken B)))) v1 v0)
        (app2 (weaken (weaken (weaken (weaken B)))) (goalsCons v3 v1) (cons v2 v0)))))))

/-- The matrix of acceptance, with `B = v0`, `A = v1`, the certificate `v2`
and the goal `v3`. -/
def accInner : Sentence (listAcceptance :: acceptance :: cert :: goal :: Γ) :=
  .imp (accNodeClosed v1 v0) (.imp (accNilClosed v0)
    (.imp (accConsClosed v1 v0) (app2 v1 v3 v2)))

/-- The matrix of list acceptance, with `B = v0`, `A = v1`, the certificate
list `v2` and the premise list `v3`. -/
def accsInner : Sentence (listAcceptance :: acceptance :: certs :: goals :: Γ) :=
  .imp (accNodeClosed v1 v0) (.imp (accNilClosed v0)
    (.imp (accConsClosed v1 v0) (app2 v0 v3 v2)))

/-- Acceptance of a certificate for a goal, by the impredicative definition:
`λg c. ∀ A B. accNodeClosed A B → B goalsNil nil → accConsClosed A B → A g c`. -/
def accDef : Expr Γ acceptance :=
  .lam (.lam (.all (σ := acceptance) (.all (σ := listAcceptance) accInner)))

/-- Acceptance of a certificate list for a premise list, the second component
of the same least pair. -/
def accsDef : Expr Γ listAcceptance :=
  .lam (.lam (.all (σ := acceptance) (.all (σ := listAcceptance) accsInner)))

def acc (g : Expr Γ goal) (c : Expr Γ cert) : Sentence Γ := app2 accDef g c
def accs (ps : Expr Γ goals) (cs : Expr Γ certs) : Sentence Γ := app2 accsDef ps cs

/-- Leastness of acceptance, read off its definition, at a pair `(A, B)`. -/
theorem acc_elim {Δ : List (Sentence Γ)} (A : Expr Γ acceptance) (B : Expr Γ listAcceptance)
    {g : Expr Γ goal} {c : Expr Γ cert} (h : ExtDerivation Symbol Δ (acc g c)) :
    ExtDerivation Symbol Δ (subst (inst4 g c A B) accInner) :=
  Eq.mp (congrArg (ExtDerivation Symbol Δ) (subst_inst2_lift_lift_inst2 g c A B accInner))
    (allE2 A B (lam2_elim h))

/-- Leastness of list acceptance, at a pair `(A, B)`. -/
theorem accs_elim {Δ : List (Sentence Γ)} (A : Expr Γ acceptance)
    (B : Expr Γ listAcceptance) {ps : Expr Γ goals} {cs : Expr Γ certs}
    (h : ExtDerivation Symbol Δ (accs ps cs)) :
    ExtDerivation Symbol Δ (subst (inst4 ps cs A B) accsInner) :=
  Eq.mp (congrArg (ExtDerivation Symbol Δ) (subst_inst2_lift_lift_inst2 ps cs A B accsInner))
    (allE2 A B (lam2_elim h))

/-! ## The introduction clauses of acceptance are theorems -/

/-- `∀ l ps g cs. rule l ps g → accs ps cs → acc g (node l cs)`. -/
def accNodeIntro : Sentence Γ :=
  .all (σ := label) (.all (σ := goals) (.all (σ := goal) (.all (σ := certs)
    (.imp (rule v3 v2 v1) (.imp (accs v2 v0) (acc v1 (node v3 v0)))))))

/-- `accs goalsNil nil`. -/
def accsNilIntro : Sentence Γ := accs goalsNil nil

/-- `∀ g c gs cs. acc g c → accs gs cs → accs (goalsCons g gs) (cons c cs)`. -/
def accsConsIntro : Sentence Γ :=
  .all (σ := goal) (.all (σ := cert) (.all (σ := goals) (.all (σ := certs)
    (.imp (acc v3 v2) (.imp (accs v1 v0) (accs (goalsCons v3 v1) (cons v2 v0)))))))

theorem accNodeIntro_derivation {Δ : List (Sentence Γ)} :
    ExtDerivation Symbol Δ accNodeIntro := by
  refine .allI (.allI (.allI (.allI (.impI (.impI ?_)))))
  refine lam2_intro (.allI (.allI (.impI (.impI (.impI ?_)))))
  change ExtDerivation Symbol
    (accConsClosed v1 v0 :: accNilClosed v0 :: accNodeClosed v1 v0 ::
      accs v4 v2 :: rule v5 v4 v3 ::
        weakenHyps (weakenHyps (weakenHyps (weakenHyps (weakenHyps (weakenHyps Δ))))))
    (app2 v1 v3 (node v5 v2))
  exact .impE (.impE (allE4 v5 v4 v3 v2 (hyp2
      (Γ := listAcceptance :: acceptance :: certs :: goal :: goals :: label :: Γ)
      (φ := accNodeClosed v1 v0))) hyp4)
    (.impE (.impE (.impE (accs_elim v1 v0 (hyp3
      (Γ := listAcceptance :: acceptance :: certs :: goal :: goals :: label :: Γ)
      (φ := accs v4 v2))) hyp2) hyp1) hyp0)

theorem accsNilIntro_derivation {Δ : List (Sentence Γ)} :
    ExtDerivation Symbol Δ accsNilIntro :=
  lam2_intro (.allI (.allI (.impI (.impI (.impI hyp1)))))

theorem accsConsIntro_derivation {Δ : List (Sentence Γ)} :
    ExtDerivation Symbol Δ accsConsIntro := by
  refine .allI (.allI (.allI (.allI (.impI (.impI ?_)))))
  refine lam2_intro (.allI (.allI (.impI (.impI (.impI ?_)))))
  change ExtDerivation Symbol
    (accConsClosed v1 v0 :: accNilClosed v0 :: accNodeClosed v1 v0 ::
      accs v3 v2 :: acc v5 v4 ::
        weakenHyps (weakenHyps (weakenHyps (weakenHyps (weakenHyps (weakenHyps Δ))))))
    (app2 v0 (goalsCons v5 v3) (cons v4 v2))
  exact .impE (.impE (allE4 v5 v4 v3 v2 (hyp0
      (Γ := listAcceptance :: acceptance :: certs :: goals :: cert :: goal :: Γ)
      (φ := accConsClosed v1 v0)))
    (.impE (.impE (.impE (acc_elim v1 v0 (hyp4
      (Γ := listAcceptance :: acceptance :: certs :: goals :: cert :: goal :: Γ)
      (φ := acc v5 v4))) hyp2) hyp1) hyp0))
    (.impE (.impE (.impE (accs_elim v1 v0 (hyp3
      (Γ := listAcceptance :: acceptance :: certs :: goals :: cert :: goal :: Γ)
      (φ := accs v3 v2))) hyp2) hyp1) hyp0)

/-! ## Soundness and completeness of the least acceptance -/

/-- Soundness: `∀ c g. acc g c → der g`. -/
def soundness : Sentence Γ :=
  .all (σ := cert) (.all (σ := goal) (.imp (acc v0 v1) (der v0)))

/-- Completeness: `∀ g. der g → ∃ c. acc g c`. -/
def completeness : Sentence Γ :=
  .all (σ := goal) (.imp (der v0) (.ex (σ := cert) (acc v1 v0)))

/-- The relation `λg c. der g`. -/
def derivedGoal : Expr Γ acceptance := .lam (.lam (der v1))

/-- The relation `λps cs. ders ps`. -/
def derivedGoals : Expr Γ listAcceptance := .lam (.lam (ders v1))

/-- The predicate `λg. ∃c. acc g c`. -/
def acceptedGoal : Expr Γ goalPredicate := .lam (.ex (σ := cert) (acc v1 v0))

/-- The predicate `λps. ∃cs. accs ps cs`. -/
def acceptedGoals : Expr Γ goalsPredicate := .lam (.ex (σ := certs) (accs v1 v0))

theorem weaken_derivedGoal {σ : Ty BaseSort} :
    weaken (σ := σ) (derivedGoal (Γ := Γ)) = derivedGoal := rfl
theorem weaken_derivedGoals {σ : Ty BaseSort} :
    weaken (σ := σ) (derivedGoals (Γ := Γ)) = derivedGoals := rfl
theorem weaken_acceptedGoal {σ : Ty BaseSort} :
    weaken (σ := σ) (acceptedGoal (Γ := Γ)) = acceptedGoal := rfl
theorem weaken_acceptedGoals {σ : Ty BaseSort} :
    weaken (σ := σ) (acceptedGoals (Γ := Γ)) = acceptedGoals := rfl

/-- Derivability is closed under the node clause of acceptance. -/
theorem derived_nodeClosed {Δ : List (Sentence Γ)} :
    ExtDerivation Symbol Δ (accNodeClosed derivedGoal derivedGoals) := by
  refine .allI (.allI (.allI (.allI (.impI (.impI ?_)))))
  dsimp only [weaken_derivedGoal, weaken_derivedGoals]
  refine lam2_intro ?_
  exact .impE (.impE (allE3 v3 v2 v1
      (derRule_derivation (Γ := certs :: goal :: goals :: label :: Γ))) hyp1)
    (lam2_elim (hyp0 (Γ := certs :: goal :: goals :: label :: Γ)
      (φ := app2 derivedGoals v2 v0)) :)

/-- Derivability is closed under the empty-list clause of acceptance. -/
theorem derived_nilClosed {Δ : List (Sentence Γ)} :
    ExtDerivation Symbol Δ (accNilClosed derivedGoals) :=
  lam2_intro dersNil_derivation

/-- Derivability is closed under the nonempty-list clause of acceptance. -/
theorem derived_consClosed {Δ : List (Sentence Γ)} :
    ExtDerivation Symbol Δ (accConsClosed derivedGoal derivedGoals) := by
  refine .allI (.allI (.allI (.allI (.impI (.impI ?_)))))
  dsimp only [weaken_derivedGoal, weaken_derivedGoals]
  refine lam2_intro ?_
  exact .impE (.impE (allE2 v3 v1
      (dersCons_derivation (Γ := certs :: goals :: cert :: goal :: Γ)))
      (lam2_elim (hyp1 (Γ := certs :: goals :: cert :: goal :: Γ)
        (φ := app2 derivedGoal v3 v2)) :))
    (lam2_elim (hyp0 (Γ := certs :: goals :: cert :: goal :: Γ)
      (φ := app2 derivedGoals v1 v0)) :)

/-- **Soundness of the least acceptance, a theorem of pure higher-order
logic.**  Derivability is closed under the clauses of acceptance, so the
least acceptance is contained in it.  No assumption is used. -/
theorem soundness_derivation {Δ : List (Sentence Γ)} : ExtDerivation Symbol Δ soundness := by
  refine .allI (.allI (.impI ?_))
  exact lam2_elim (.impE (.impE (.impE (acc_elim derivedGoal derivedGoals
    (hyp0 (Γ := goal :: cert :: Γ) (φ := acc v0 v1))) derived_nodeClosed) derived_nilClosed)
    derived_consClosed)

/-- Acceptance is closed under the rule clause of derivability. -/
theorem accepted_ruleClosed {Δ : List (Sentence Γ)} :
    ExtDerivation Symbol Δ (derRuleClosed acceptedGoal acceptedGoals) := by
  refine .allI (.allI (.allI (.impI (.impI ?_))))
  dsimp only [weaken_acceptedGoal, weaken_acceptedGoals]
  refine lam_intro ?_
  show ExtDerivation Symbol _ (.ex (σ := cert) (acc v1 v0))
  refine .exE (lam_elim (hyp0 (Γ := goal :: goals :: label :: Γ)
    (φ := .app acceptedGoals v1))) ?_
  show ExtDerivation Symbol (accs v2 v0 :: _) (.ex (σ := cert) (acc v2 v0))
  refine .exI (node v3 v0) ?_
  exact .impE (.impE (allE4 v3 v2 v1 v0
    (accNodeIntro_derivation (Γ := certs :: goal :: goals :: label :: Γ))) hyp2) hyp0

/-- Acceptance is closed under the empty-list clause of derivability. -/
theorem accepted_nilClosed {Δ : List (Sentence Γ)} :
    ExtDerivation Symbol Δ (derNilClosed acceptedGoals) :=
  lam_intro (.exI nil accsNilIntro_derivation)

/-- Acceptance is closed under the nonempty-list clause of derivability. -/
theorem accepted_consClosed {Δ : List (Sentence Γ)} :
    ExtDerivation Symbol Δ (derConsClosed acceptedGoal acceptedGoals) := by
  refine .allI (.allI (.impI (.impI ?_)))
  dsimp only [weaken_acceptedGoal, weaken_acceptedGoals]
  refine lam_intro ?_
  show ExtDerivation Symbol _ (.ex (σ := certs) (accs (goalsCons v2 v1) v0))
  refine .exE (lam_elim (hyp1 (Γ := goals :: goal :: Γ)
    (φ := .app acceptedGoal v1))) ?_
  show ExtDerivation Symbol (acc v2 v0 :: _) (.ex (σ := certs) (accs (goalsCons v3 v2) v0))
  refine .exE (lam_elim (hyp1 (Γ := cert :: goals :: goal :: Γ)
    (φ := .app acceptedGoals v1))) ?_
  show ExtDerivation Symbol (accs v2 v0 :: acc v3 v1 :: _)
    (.ex (σ := certs) (accs (goalsCons v4 v3) v0))
  refine .exI (cons v1 v0) ?_
  exact .impE (.impE (allE4 v3 v1 v2 v0
    (accsConsIntro_derivation (Γ := certs :: cert :: goals :: goal :: Γ))) hyp1) hyp0

/-- **Completeness of the least acceptance, a theorem of pure higher-order
logic.**  Having an accepted certificate is closed under the rule clauses, so
the least derivability predicate is contained in it.  No assumption is
used. -/
theorem completeness_derivation {Δ : List (Sentence Γ)} :
    ExtDerivation Symbol Δ completeness := by
  refine .allI (.impI ?_)
  exact lam_elim (.impE (.impE (.impE (der_elim acceptedGoal acceptedGoals
    (hyp0 (Γ := goal :: Γ) (φ := der v0))) accepted_ruleClosed) accepted_nilClosed)
    accepted_consClosed)

/-! ## Leibniz rewriting at the atomic formulas -/

section Rewriting

variable {Δ : List (Sentence Γ)}

/-- Rewrite the second argument of an applied binary predicate. -/
theorem app2_congr_right {σ τ : Ty BaseSort} {F : Expr Γ (σ ⇒ τ ⇒ .prop)} {x : Expr Γ σ}
    {y y' : Expr Γ τ} (e : ExtDerivation Symbol Δ (.eq y y'))
    (h : ExtDerivation Symbol Δ (app2 F x y)) : ExtDerivation Symbol Δ (app2 F x y') :=
  .impE (.eqPropEL (.eqAppArg (.app F x) e)) h

/-- Rewrite the first argument of an applied binary predicate. -/
theorem app2_congr_left {σ τ : Ty BaseSort} {F : Expr Γ (σ ⇒ τ ⇒ .prop)} {x x' : Expr Γ σ}
    {y : Expr Γ τ} (e : ExtDerivation Symbol Δ (.eq x x'))
    (h : ExtDerivation Symbol Δ (app2 F x y)) : ExtDerivation Symbol Δ (app2 F x' y) :=
  .impE (.eqPropEL (.eqApp y (.eqAppArg F e))) h

/-- Rewrite the label of a rule instance. -/
theorem rule_congr_label {l l' : Expr Γ label} {ps : Expr Γ goals} {g : Expr Γ goal}
    (e : ExtDerivation Symbol Δ (.eq l l')) (h : ExtDerivation Symbol Δ (rule l ps g)) :
    ExtDerivation Symbol Δ (rule l' ps g) :=
  .impE (.eqPropEL (.eqApp g (.eqApp ps (.eqAppArg (.const Symbol.rule) e)))) h

end Rewriting

theorem weaken_accDef {σ : Ty BaseSort} : weaken (σ := σ) (accDef (Γ := Γ)) = accDef := rfl
theorem weaken_accsDef {σ : Ty BaseSort} : weaken (σ := σ) (accsDef (Γ := Γ)) = accsDef := rfl

/-! ## Freeness of the certificate constructors -/

/-- `∀ l cs l' cs'. node l cs = node l' cs' → l = l' ∧ cs = cs'`. -/
def nodeInjective : Sentence Γ :=
  .all (σ := label) (.all (σ := certs) (.all (σ := label) (.all (σ := certs)
    (.imp (.eq (node v3 v2) (node v1 v0)) (.and (.eq v3 v1) (.eq v2 v0))))))

/-- `∀ c cs c' cs'. cons c cs = cons c' cs' → c = c' ∧ cs = cs'`. -/
def consInjective : Sentence Γ :=
  .all (σ := cert) (.all (σ := certs) (.all (σ := cert) (.all (σ := certs)
    (.imp (.eq (cons v3 v2) (cons v1 v0)) (.and (.eq v3 v1) (.eq v2 v0))))))

/-- `∀ c cs. ¬ cons c cs = nil`. -/
def consNotNil : Sentence Γ :=
  .all (σ := cert) (.all (σ := certs) (.not (.eq (cons v1 v0) nil)))

/-! ## Inversion of acceptance

The least acceptance satisfies the introduction halves of the replay
equations by definition.  Their elimination halves are inversion
principles: an instance of leastness at a relation that also records how a
pair was introduced.  Reading the introduction back needs the constructors to
be free. -/

/-- `∀ l cs. c = node l cs → ∃ ps. rule l ps g ∧ accs ps cs`. -/
def nodeInversion (g : Expr Γ goal) (c : Expr Γ cert) : Sentence Γ :=
  .all (σ := label) (.all (σ := certs)
    (.imp (.eq (weaken (weaken c)) (node v1 v0))
      (.ex (σ := goals) (.and (rule v2 v0 (weaken (weaken (weaken g)))) (accs v0 v1)))))

/-- `cs = nil → ps = goalsNil`. -/
def nilInversion (ps : Expr Γ goals) (cs : Expr Γ certs) : Sentence Γ :=
  .imp (.eq cs nil) (.eq ps goalsNil)

/-- `∀ c cs'. cs = cons c cs' → ∃ g gs. ps = goalsCons g gs ∧ acc g c ∧ accs gs cs'`. -/
def consInversion (ps : Expr Γ goals) (cs : Expr Γ certs) : Sentence Γ :=
  .all (σ := cert) (.all (σ := certs)
    (.imp (.eq (weaken (weaken cs)) (cons v1 v0))
      (.ex (σ := goal) (.ex (σ := goals)
        (.and (.eq (weaken (weaken (weaken (weaken ps)))) (goalsCons v1 v0))
          (.and (acc v1 v3) (accs v0 v2)))))))

/-- The relation `λg c. acc g c ∧ nodeInversion g c`. -/
def nodeInvertible : Expr Γ acceptance := .lam (.lam (.and (acc v1 v0) (nodeInversion v1 v0)))

/-- The relation `λps cs. accs ps cs ∧ nilInversion ps cs`. -/
def nilInvertible : Expr Γ listAcceptance :=
  .lam (.lam (.and (accs v1 v0) (nilInversion v1 v0)))

/-- The relation `λps cs. accs ps cs ∧ consInversion ps cs`. -/
def consInvertible : Expr Γ listAcceptance :=
  .lam (.lam (.and (accs v1 v0) (consInversion v1 v0)))

theorem weaken_nodeInvertible {σ : Ty BaseSort} :
    weaken (σ := σ) (nodeInvertible (Γ := Γ)) = nodeInvertible := rfl
theorem weaken_nilInvertible {σ : Ty BaseSort} :
    weaken (σ := σ) (nilInvertible (Γ := Γ)) = nilInvertible := rfl
theorem weaken_consInvertible {σ : Ty BaseSort} :
    weaken (σ := σ) (consInvertible (Γ := Γ)) = consInvertible := rfl

/-- With an injective node constructor, `nodeInvertible` is closed under the
node clause. -/
theorem nodeInvertible_nodeClosed {Δ : List (Sentence Γ)} :
    ExtDerivation Symbol Δ (.imp nodeInjective (accNodeClosed nodeInvertible accsDef)) := by
  refine .impI (.allI (.allI (.allI (.allI (.impI (.impI ?_))))))
  dsimp only [weaken_nodeInvertible, weaken_accsDef]
  refine lam2_intro ?_
  show ExtDerivation Symbol (accs v2 v0 :: rule v3 v2 v1 :: _)
    (.and (acc v1 (node v3 v0)) (nodeInversion v1 (node v3 v0)))
  refine .andI (.impE (.impE (allE4 v3 v2 v1 v0
    (accNodeIntro_derivation (Γ := certs :: goal :: goals :: label :: Γ))) hyp1) hyp0) ?_
  refine .allI (.allI (.impI ?_))
  show ExtDerivation Symbol
    (.eq (node v5 v2) (node v1 v0) :: accs v4 v2 :: rule v5 v4 v3 :: nodeInjective :: _)
    (.ex (σ := goals) (.and (rule v2 v0 v4) (accs v0 v1)))
  exact .exI v4 (.andI
    (rule_congr_label (.andEL (.impE (allE4 v5 v2 v1 v0 (hyp3
      (Γ := certs :: label :: certs :: goal :: goals :: label :: Γ)
      (φ := nodeInjective))) hyp0)) hyp2)
    (app2_congr_right (.andER (.impE (allE4 v5 v2 v1 v0 (hyp3
      (Γ := certs :: label :: certs :: goal :: goals :: label :: Γ)
      (φ := nodeInjective))) hyp0)) hyp1))

/-- `nodeInvertible` is closed under the nonempty-list clause. -/
theorem nodeInvertible_consClosed {Δ : List (Sentence Γ)} :
    ExtDerivation Symbol Δ (accConsClosed nodeInvertible accsDef) := by
  refine .allI (.allI (.allI (.allI (.impI (.impI ?_)))))
  dsimp only [weaken_nodeInvertible, weaken_accsDef]
  exact .impE (.impE (allE4 v3 v2 v1 v0
      (accsConsIntro_derivation (Γ := certs :: goals :: cert :: goal :: Γ)))
    (.andEL (lam2_elim (hyp1 (Γ := certs :: goals :: cert :: goal :: Γ)
      (φ := app2 nodeInvertible v3 v2)) :))) hyp0

/-- `∀ l cs g. acc g (node l cs) → ∃ ps. rule l ps g ∧ accs ps cs`. -/
def accNodeInversion : Sentence Γ :=
  .all (σ := label) (.all (σ := certs) (.all (σ := goal)
    (.imp (acc v0 (node v2 v1)) (.ex (σ := goals) (.and (rule v3 v0 v1) (accs v0 v2))))))

/-- Inversion at a node, from injectivity of the node constructor. -/
theorem accNodeInversion_derivation {Δ : List (Sentence Γ)} :
    ExtDerivation Symbol Δ (.imp nodeInjective accNodeInversion) := by
  refine .impI (.allI (.allI (.allI (.impI ?_))))
  exact .impE (allE2 v2 v1 (.andER (lam2_elim (ExtDerivation.impE (ExtDerivation.impE
    (ExtDerivation.impE (acc_elim nodeInvertible accsDef
      (hyp0 (Γ := goal :: certs :: label :: Γ) (φ := acc v0 (node v2 v1))))
      (ExtDerivation.impE (nodeInvertible_nodeClosed (Γ := goal :: certs :: label :: Γ))
        (hyp1 (Γ := goal :: certs :: label :: Γ) (φ := nodeInjective))))
    accsNilIntro_derivation) nodeInvertible_consClosed) :))) (.eqRefl (node v2 v1))

/-- `nilInvertible` is closed under the node clause. -/
theorem nilInvertible_nodeClosed {Δ : List (Sentence Γ)} :
    ExtDerivation Symbol Δ (accNodeClosed accDef nilInvertible) := by
  refine .allI (.allI (.allI (.allI (.impI (.impI ?_)))))
  dsimp only [weaken_accDef, weaken_nilInvertible]
  exact .impE (.impE (allE4 v3 v2 v1 v0
      (accNodeIntro_derivation (Γ := certs :: goal :: goals :: label :: Γ))) hyp1)
    (.andEL (lam2_elim (hyp0 (Γ := certs :: goal :: goals :: label :: Γ)
      (φ := app2 nilInvertible v2 v0)) :))

/-- `nilInvertible` holds of the empty lists. -/
theorem nilInvertible_nilClosed {Δ : List (Sentence Γ)} :
    ExtDerivation Symbol Δ (accNilClosed nilInvertible) :=
  lam2_intro (.andI accsNilIntro_derivation (.impI (.eqRefl goalsNil)))

/-- With `cons c cs ≠ nil`, `nilInvertible` is closed under the nonempty-list
clause. -/
theorem nilInvertible_consClosed {Δ : List (Sentence Γ)} :
    ExtDerivation Symbol Δ (.imp consNotNil (accConsClosed accDef nilInvertible)) := by
  refine .impI (.allI (.allI (.allI (.allI (.impI (.impI ?_))))))
  dsimp only [weaken_accDef, weaken_nilInvertible]
  refine lam2_intro ?_
  show ExtDerivation Symbol (app2 nilInvertible v1 v0 :: acc v3 v2 :: consNotNil :: _)
    (.and (accs (goalsCons v3 v1) (cons v2 v0)) (nilInversion (goalsCons v3 v1) (cons v2 v0)))
  refine .andI (.impE (.impE (allE4 v3 v2 v1 v0
      (accsConsIntro_derivation (Γ := certs :: goals :: cert :: goal :: Γ))) hyp1)
    (.andEL (lam2_elim (hyp0 (Γ := certs :: goals :: cert :: goal :: Γ)
      (φ := app2 nilInvertible v1 v0)) :))) ?_
  exact .impI (.botE (.notE (allE2 v2 v0 (hyp3 (Γ := certs :: goals :: cert :: goal :: Γ)
    (φ := consNotNil))) hyp0))

/-- `∀ ps. accs ps nil → ps = goalsNil`. -/
def accsNilInversion : Sentence Γ :=
  .all (σ := goals) (.imp (accs v0 nil) (.eq v0 goalsNil))

/-- Inversion at the empty list, from `cons c cs ≠ nil`. -/
theorem accsNilInversion_derivation {Δ : List (Sentence Γ)} :
    ExtDerivation Symbol Δ (.imp consNotNil accsNilInversion) := by
  refine .impI (.allI (.impI ?_))
  exact .impE (.andER (lam2_elim (ExtDerivation.impE (ExtDerivation.impE
    (ExtDerivation.impE (accs_elim accDef nilInvertible
      (hyp0 (Γ := goals :: Γ) (φ := accs v0 nil))) nilInvertible_nodeClosed)
      nilInvertible_nilClosed)
    (ExtDerivation.impE (nilInvertible_consClosed (Γ := goals :: Γ))
      (hyp1 (Γ := goals :: Γ) (φ := consNotNil)))) :)) (.eqRefl nil)

/-- `consInvertible` is closed under the node clause. -/
theorem consInvertible_nodeClosed {Δ : List (Sentence Γ)} :
    ExtDerivation Symbol Δ (accNodeClosed accDef consInvertible) := by
  refine .allI (.allI (.allI (.allI (.impI (.impI ?_)))))
  dsimp only [weaken_accDef, weaken_consInvertible]
  exact .impE (.impE (allE4 v3 v2 v1 v0
      (accNodeIntro_derivation (Γ := certs :: goal :: goals :: label :: Γ))) hyp1)
    (.andEL (lam2_elim (hyp0 (Γ := certs :: goal :: goals :: label :: Γ)
      (φ := app2 consInvertible v2 v0)) :))

/-- With `cons c cs ≠ nil`, `consInvertible` holds of the empty lists. -/
theorem consInvertible_nilClosed {Δ : List (Sentence Γ)} :
    ExtDerivation Symbol Δ (.imp consNotNil (accNilClosed consInvertible)) := by
  refine .impI (lam2_intro (.andI accsNilIntro_derivation ?_))
  refine .allI (.allI (.impI ?_))
  show ExtDerivation Symbol (.eq nil (cons v1 v0) :: consNotNil :: _) _
  exact .botE (.notE (allE2 v1 v0 (hyp1 (Γ := certs :: cert :: Γ) (φ := consNotNil)))
    (.eqSymm hyp0))

/-- With an injective cons constructor, `consInvertible` is closed under the
nonempty-list clause. -/
theorem consInvertible_consClosed {Δ : List (Sentence Γ)} :
    ExtDerivation Symbol Δ (.imp consInjective (accConsClosed accDef consInvertible)) := by
  refine .impI (.allI (.allI (.allI (.allI (.impI (.impI ?_))))))
  dsimp only [weaken_accDef, weaken_consInvertible]
  refine lam2_intro ?_
  show ExtDerivation Symbol (app2 consInvertible v1 v0 :: acc v3 v2 :: consInjective :: _)
    (.and (accs (goalsCons v3 v1) (cons v2 v0)) (consInversion (goalsCons v3 v1) (cons v2 v0)))
  refine .andI (.impE (.impE (allE4 v3 v2 v1 v0
      (accsConsIntro_derivation (Γ := certs :: goals :: cert :: goal :: Γ))) hyp1)
    (.andEL (lam2_elim (hyp0 (Γ := certs :: goals :: cert :: goal :: Γ)
      (φ := app2 consInvertible v1 v0)) :))) ?_
  refine .allI (.allI (.impI ?_))
  show ExtDerivation Symbol
    (.eq (cons v4 v2) (cons v1 v0) :: app2 consInvertible v3 v2 :: acc v5 v4 ::
      consInjective :: _)
    (.ex (σ := goal) (.ex (σ := goals)
      (.and (.eq (goalsCons v7 v5) (goalsCons v1 v0)) (.and (acc v1 v3) (accs v0 v2)))))
  refine exI2 v5 v3 (.andI (.eqRefl _) (.andI ?_ ?_))
  · exact app2_congr_right (.andEL (.impE (allE4 v4 v2 v1 v0 (hyp3
      (Γ := certs :: cert :: certs :: goals :: cert :: goal :: Γ)
      (φ := consInjective))) hyp0)) hyp2
  · exact app2_congr_right (.andER (.impE (allE4 v4 v2 v1 v0 (hyp3
      (Γ := certs :: cert :: certs :: goals :: cert :: goal :: Γ)
      (φ := consInjective))) hyp0))
      (.andEL (lam2_elim (hyp1 (Γ := certs :: cert :: certs :: goals :: cert :: goal :: Γ)
        (φ := app2 consInvertible v3 v2)) :))

/-- `∀ c cs ps. accs ps (cons c cs) → ∃ g gs. ps = goalsCons g gs ∧ acc g c ∧ accs gs cs`. -/
def accsConsInversion : Sentence Γ :=
  .all (σ := cert) (.all (σ := certs) (.all (σ := goals)
    (.imp (accs v0 (cons v2 v1))
      (.ex (σ := goal) (.ex (σ := goals)
        (.and (.eq v2 (goalsCons v1 v0)) (.and (acc v1 v4) (accs v0 v3))))))))

/-- Inversion at a nonempty list, from freeness of the list constructors. -/
theorem accsConsInversion_derivation {Δ : List (Sentence Γ)} :
    ExtDerivation Symbol Δ (.imp consInjective (.imp consNotNil accsConsInversion)) := by
  refine .impI (.impI (.allI (.allI (.allI (.impI ?_)))))
  exact .impE (allE2 v2 v1 (.andER (lam2_elim (ExtDerivation.impE (ExtDerivation.impE
    (ExtDerivation.impE (accs_elim accDef consInvertible
      (hyp0 (Γ := goals :: certs :: cert :: Γ) (φ := accs v0 (cons v2 v1))))
      consInvertible_nodeClosed)
      (ExtDerivation.impE (consInvertible_nilClosed (Γ := goals :: certs :: cert :: Γ))
        (hyp1 (Γ := goals :: certs :: cert :: Γ) (φ := consNotNil))))
    (ExtDerivation.impE (consInvertible_consClosed (Γ := goals :: certs :: cert :: Γ))
      (hyp2 (Γ := goals :: certs :: cert :: Γ) (φ := consInjective)))) :)))
    (.eqRefl (cons v2 v1))

/-! ## The replay equations

A checker given by structural recursion on certificates is specified by its
recursion equations, read with equality at type `prop` as the biconditional.
For a pair `(A, B)` of a relation on goals and certificates and a relation on
premise lists and certificate lists: -/

/-- `∀ l cs g. A g (node l cs) = ∃ ps. rule l ps g ∧ B ps cs`. -/
def nodeEquation (A : Expr Γ acceptance) (B : Expr Γ listAcceptance) : Sentence Γ :=
  .all (σ := label) (.all (σ := certs) (.all (σ := goal)
    (.eq (app2 (weaken (weaken (weaken A))) v0 (node v2 v1))
      (.ex (σ := goals)
        (.and (rule v3 v0 v1) (app2 (weaken (weaken (weaken (weaken B)))) v0 v2))))))

/-- `∀ ps. B ps nil = (ps = goalsNil)`. -/
def nilEquation (B : Expr Γ listAcceptance) : Sentence Γ :=
  .all (σ := goals) (.eq (app2 (weaken B) v0 nil) (.eq v0 goalsNil))

/-- `∀ c cs ps. B ps (cons c cs) = ∃ g gs. ps = goalsCons g gs ∧ A g c ∧ B gs cs`. -/
def consEquation (A : Expr Γ acceptance) (B : Expr Γ listAcceptance) : Sentence Γ :=
  .all (σ := cert) (.all (σ := certs) (.all (σ := goals)
    (.eq (app2 (weaken (weaken (weaken B))) v0 (cons v2 v1))
      (.ex (σ := goal) (.ex (σ := goals)
        (.and (.eq v2 (goalsCons v1 v0))
          (.and (app2 (weaken (weaken (weaken (weaken (weaken A))))) v1 v4)
            (app2 (weaken (weaken (weaken (weaken (weaken B))))) v0 v3))))))))

/-- The node equation of the least acceptance. -/
def accNode : Sentence Γ := nodeEquation accDef accsDef
/-- The empty-list equation of the least acceptance. -/
def accsNil : Sentence Γ := nilEquation accsDef
/-- The nonempty-list equation of the least acceptance. -/
def accsCons : Sentence Γ := consEquation accDef accsDef

/-- The node equation, from injectivity of the node constructor. -/
theorem accNode_derivation {Δ : List (Sentence Γ)} :
    ExtDerivation Symbol Δ (.imp nodeInjective accNode) := by
  refine .impI (.allI (.allI (.allI ?_)))
  dsimp only [weaken_accDef, weaken_accsDef]
  refine .eqPropI (.impI ?_) (.impI ?_)
  · exact .impE (allE3 v2 v1 v0 (.impE (accNodeInversion_derivation
      (Γ := goal :: certs :: label :: Γ)) (hyp1 (Γ := goal :: certs :: label :: Γ)
        (φ := nodeInjective)))) hyp0
  · refine .exE (hyp0 (Γ := goal :: certs :: label :: Γ)
      (φ := .ex (σ := goals) (.and (rule v3 v0 v1) (accs v0 v2)))) ?_
    show ExtDerivation Symbol (.and (rule v3 v0 v1) (accs v0 v2) :: _) (acc v1 (node v3 v2))
    exact .impE (.impE (allE4 v3 v0 v1 v2
      (accNodeIntro_derivation (Γ := goals :: goal :: certs :: label :: Γ))) (.andEL hyp0))
      (.andER hyp0)

/-- The empty-list equation, from `cons c cs ≠ nil`. -/
theorem accsNil_derivation {Δ : List (Sentence Γ)} :
    ExtDerivation Symbol Δ (.imp consNotNil accsNil) := by
  refine .impI (.allI ?_)
  dsimp only [weaken_accsDef]
  refine .eqPropI (.impI ?_) (.impI ?_)
  · exact .impE (.allE v0 (.impE (accsNilInversion_derivation (Γ := goals :: Γ))
      (hyp1 (Γ := goals :: Γ) (φ := consNotNil)))) hyp0
  · exact app2_congr_left (.eqSymm (hyp0 (Γ := goals :: Γ) (φ := .eq v0 goalsNil)))
      (accsNilIntro_derivation (Γ := goals :: Γ))

/-- The nonempty-list equation, from freeness of the list constructors. -/
theorem accsCons_derivation {Δ : List (Sentence Γ)} :
    ExtDerivation Symbol Δ (.imp consInjective (.imp consNotNil accsCons)) := by
  refine .impI (.impI (.allI (.allI (.allI ?_))))
  dsimp only [weaken_accDef, weaken_accsDef]
  refine .eqPropI (.impI ?_) (.impI ?_)
  · exact .impE (allE3 v2 v1 v0 (.impE (.impE (accsConsInversion_derivation
      (Γ := goals :: certs :: cert :: Γ))
      (hyp2 (Γ := goals :: certs :: cert :: Γ) (φ := consInjective)))
      (hyp1 (Γ := goals :: certs :: cert :: Γ) (φ := consNotNil)))) hyp0
  · refine .exE (hyp0 (Γ := goals :: certs :: cert :: Γ)
      (φ := .ex (σ := goal) (.ex (σ := goals)
        (.and (.eq v2 (goalsCons v1 v0)) (.and (acc v1 v4) (accs v0 v3)))))) ?_
    refine .exE (hyp0 (Γ := goal :: goals :: certs :: cert :: Γ)
      (φ := .ex (σ := goals)
        (.and (.eq v2 (goalsCons v1 v0)) (.and (acc v1 v4) (accs v0 v3))))) ?_
    show ExtDerivation Symbol
      (.and (.eq v2 (goalsCons v1 v0)) (.and (acc v1 v4) (accs v0 v3)) :: _)
      (accs v2 (cons v4 v3))
    exact app2_congr_left (.eqSymm (.andEL hyp0)) (.impE (.impE (allE4 v1 v4 v0 v3
      (accsConsIntro_derivation (Γ := goals :: goal :: goals :: certs :: cert :: Γ)))
      (.andEL (.andER hyp0))) (.andER (.andER hyp0)))

/-! ## Induction on certificates, and the theory -/

/-- `∀ l cs. Q cs → P (node l cs)`, for predicates `P` and `Q`. -/
def nodeClosed (P : Expr Γ certPredicate) (Q : Expr Γ certsPredicate) : Sentence Γ :=
  .all (σ := label) (.all (σ := certs)
    (.imp (.app (weaken (weaken Q)) v0) (.app (weaken (weaken P)) (node v1 v0))))

/-- `∀ c cs. P c → Q cs → Q (cons c cs)`, for predicates `P` and `Q`. -/
def consClosed (P : Expr Γ certPredicate) (Q : Expr Γ certsPredicate) : Sentence Γ :=
  .all (σ := cert) (.all (σ := certs)
    (.imp (.app (weaken (weaken P)) v1)
      (.imp (.app (weaken (weaken Q)) v0) (.app (weaken (weaken Q)) (cons v1 v0)))))

/-- Induction on certificates, one sentence of the object logic:
`∀ P Q. nodeClosed P Q → Q nil → consClosed P Q → ∀ c. P c`. -/
def certInduction : Sentence Γ :=
  .all (σ := certPredicate) (.all (σ := certsPredicate)
    (.imp (nodeClosed v1 v0)
      (.imp (.app v0 nil)
        (.imp (consClosed v1 v0) (.all (σ := cert) (.app v2 v0))))))

/-- Freeness of the certificate constructors. -/
def freeness : List (Sentence Γ) := [nodeInjective, consInjective, consNotNil]

/-- The theory: induction on certificates and freeness of their constructors.
Acceptance and derivability are definitions, so no sentence of the theory
mentions replay or derivations. -/
def theory : List (Sentence Γ) := certInduction :: freeness

theorem mem_theory_certInduction : certInduction ∈ theory (Γ := Γ) := List.mem_cons_self
theorem mem_theory_nodeInjective : nodeInjective ∈ theory (Γ := Γ) :=
  List.mem_cons_of_mem _ List.mem_cons_self
theorem mem_theory_consInjective : consInjective ∈ theory (Γ := Γ) :=
  List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)
theorem mem_theory_consNotNil : consNotNil ∈ theory (Γ := Γ) :=
  List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))

/-- The node equation of the least acceptance holds in the theory. -/
theorem accNode_theory : ExtDerivation Symbol (theory (Γ := Γ)) accNode :=
  .impE accNode_derivation (.hyp mem_theory_nodeInjective)

/-- The empty-list equation of the least acceptance holds in the theory. -/
theorem accsNil_theory : ExtDerivation Symbol (theory (Γ := Γ)) accsNil :=
  .impE accsNil_derivation (.hyp mem_theory_consNotNil)

/-- The nonempty-list equation of the least acceptance holds in the theory. -/
theorem accsCons_theory : ExtDerivation Symbol (theory (Γ := Γ)) accsCons :=
  .impE (.impE accsCons_derivation (.hyp mem_theory_consInjective))
    (.hyp mem_theory_consNotNil)

/-! ## Checkers given by the replay equations

A solution of the replay equations is any pair `(A, B)` satisfying the three
equations.  The least acceptance is one (from freeness).  Every solution
contains it, by leastness alone; with induction on certificates every
solution is contained in it, so the solution is unique.  Soundness of every
solution needs induction; completeness does not. -/

/-- `∀ A B. nodeEquation A B → nilEquation B → consEquation A B → body`. -/
def solutions (body : Sentence (listAcceptance :: acceptance :: Γ)) : Sentence Γ :=
  .all (σ := acceptance) (.all (σ := listAcceptance)
    (.imp (nodeEquation v1 v0) (.imp (nilEquation v0) (.imp (consEquation v1 v0) body))))

/-- Every solution contains the least acceptance. -/
def leastBelowSolutions : Sentence Γ :=
  solutions (.all (σ := cert) (.all (σ := goal) (.imp (acc v0 v1) (app2 v3 v0 v1))))

/-- Every solution is contained in the least acceptance. -/
def solutionsBelowLeast : Sentence Γ :=
  solutions (.all (σ := cert) (.all (σ := goal) (.imp (app2 v3 v0 v1) (acc v0 v1))))

/-- Soundness of every solution: `∀ A B. equations → ∀ c g. A g c → der g`. -/
def solutionSoundness : Sentence Γ :=
  solutions (.all (σ := cert) (.all (σ := goal) (.imp (app2 v3 v0 v1) (der v0))))

/-- Completeness of every solution: `∀ A B. equations → ∀ g. der g → ∃ c. A g c`. -/
def solutionCompleteness : Sentence Γ :=
  solutions (.all (σ := goal) (.imp (der v0) (.ex (σ := cert) (app2 v3 v1 v0))))

/-- Every solution is the least acceptance: `∀ A B. equations → ∀ c g. A g c = acc g c`. -/
def solutionUnique : Sentence Γ :=
  solutions (.all (σ := cert) (.all (σ := goal) (.eq (app2 v3 v0 v1) (acc v0 v1))))

/-- `∀ A B. nodeEquation A B → accNodeClosed A B`. -/
def nodeEquationClosed : Sentence Γ :=
  .all (σ := acceptance) (.all (σ := listAcceptance)
    (.imp (nodeEquation v1 v0) (accNodeClosed v1 v0)))

/-- `∀ B. nilEquation B → accNilClosed B`. -/
def nilEquationClosed : Sentence Γ :=
  .all (σ := listAcceptance) (.imp (nilEquation v0) (accNilClosed v0))

/-- `∀ A B. consEquation A B → accConsClosed A B`. -/
def consEquationClosed : Sentence Γ :=
  .all (σ := acceptance) (.all (σ := listAcceptance)
    (.imp (consEquation v1 v0) (accConsClosed v1 v0)))

theorem nodeEquationClosed_derivation {Δ : List (Sentence Γ)} :
    ExtDerivation Symbol Δ nodeEquationClosed := by
  refine .allI (.allI (.impI (.allI (.allI (.allI (.allI (.impI (.impI ?_))))))))
  show ExtDerivation Symbol (app2 v4 v2 v0 :: rule v3 v2 v1 :: nodeEquation v5 v4 :: _)
    (app2 v5 v1 (node v3 v0))
  exact .impE (.eqPropER (allE3 v3 v0 v1 (hyp2
      (Γ := certs :: goal :: goals :: label :: listAcceptance :: acceptance :: Γ)
      (φ := nodeEquation v5 v4))))
    (.exI v2 (.andI hyp1 hyp0))

theorem nilEquationClosed_derivation {Δ : List (Sentence Γ)} :
    ExtDerivation Symbol Δ nilEquationClosed := by
  refine .allI (.impI ?_)
  exact .impE (.eqPropER (.allE goalsNil (hyp0 (Γ := listAcceptance :: Γ)
    (φ := nilEquation v0)))) (.eqRefl goalsNil)

theorem consEquationClosed_derivation {Δ : List (Sentence Γ)} :
    ExtDerivation Symbol Δ consEquationClosed := by
  refine .allI (.allI (.impI (.allI (.allI (.allI (.allI (.impI (.impI ?_))))))))
  show ExtDerivation Symbol (app2 v4 v1 v0 :: app2 v5 v3 v2 :: consEquation v5 v4 :: _)
    (app2 v4 (goalsCons v3 v1) (cons v2 v0))
  exact .impE (.eqPropER (allE3 v2 v0 (goalsCons v3 v1) (hyp2
      (Γ := certs :: goals :: cert :: goal :: listAcceptance :: acceptance :: Γ)
      (φ := consEquation v5 v4))))
    (exI2 v3 v1 (.andI (.eqRefl _) (.andI hyp1 hyp0)))

/-- **Every solution contains the least acceptance**, by leastness alone. -/
theorem leastBelowSolutions_derivation {Δ : List (Sentence Γ)} :
    ExtDerivation Symbol Δ leastBelowSolutions := by
  refine .allI (.allI (.impI (.impI (.impI (.allI (.allI (.impI ?_)))))))
  show ExtDerivation Symbol
    (acc v0 v1 :: consEquation v3 v2 :: nilEquation v2 :: nodeEquation v3 v2 :: _)
    (app2 v3 v0 v1)
  exact .impE (.impE (.impE (acc_elim v3 v2 (hyp0
        (Γ := goal :: cert :: listAcceptance :: acceptance :: Γ) (φ := acc v0 v1)))
      (.impE (allE2 v3 v2 (nodeEquationClosed_derivation
        (Γ := goal :: cert :: listAcceptance :: acceptance :: Γ))) hyp3))
      (.impE (.allE v2 (nilEquationClosed_derivation
        (Γ := goal :: cert :: listAcceptance :: acceptance :: Γ))) hyp2))
    (.impE (allE2 v3 v2 (consEquationClosed_derivation
      (Γ := goal :: cert :: listAcceptance :: acceptance :: Γ))) hyp1)

/-- The certificate claim `λA c. ∀g. A g c → acc g c`. -/
def belowCert : Expr Γ (acceptance ⇒ cert ⇒ .prop) :=
  .lam (.lam (.all (σ := goal) (.imp (app2 v2 v0 v1) (acc v0 v1))))

/-- The list claim `λB cs. ∀ps. B ps cs → accs ps cs`. -/
def belowCerts : Expr Γ (listAcceptance ⇒ certs ⇒ .prop) :=
  .lam (.lam (.all (σ := goals) (.imp (app2 v2 v0 v1) (accs v0 v1))))

section Below

variable {Δ : List (Sentence (listAcceptance :: acceptance :: Γ))}

/-- Node case of the induction for `solutionsBelowLeast`. -/
theorem solutionsBelow_nodeCase :
    ExtDerivation Symbol Δ
      (.imp (nodeEquation v1 v0) (nodeClosed (.app belowCert v1) (.app belowCerts v0))) := by
  refine .impI (.allI (.allI (.impI ?_)))
  show ExtDerivation Symbol (app2 belowCerts v2 v0 :: nodeEquation v3 v2 :: _)
    (app2 belowCert v3 (node v1 v0))
  refine lam2_intro (.allI (.impI ?_))
  show ExtDerivation Symbol
    (app2 v4 v0 (node v2 v1) :: app2 belowCerts v3 v1 :: nodeEquation v4 v3 :: _)
    (acc v0 (node v2 v1))
  refine .exE (.impE (.eqPropEL (allE3 v2 v1 v0 (hyp2
    (Γ := goal :: certs :: label :: listAcceptance :: acceptance :: Γ)
    (φ := nodeEquation v4 v3)))) hyp0) ?_
  show ExtDerivation Symbol
    (.and (rule v3 v0 v1) (app2 v4 v0 v2) :: app2 v5 v1 (node v3 v2) ::
      app2 belowCerts v4 v2 :: _)
    (acc v1 (node v3 v2))
  exact .impE (.impE (allE4 v3 v0 v1 v2 (accNodeIntro_derivation
      (Γ := goals :: goal :: certs :: label :: listAcceptance :: acceptance :: Γ)))
      (.andEL hyp0))
    (.impE ((allE_inst2 v4 v2 v0 (lam2_elim (hyp2
      (Γ := goals :: goal :: certs :: label :: listAcceptance :: acceptance :: Γ)
      (φ := app2 belowCerts v4 v2))) :) : ExtDerivation Symbol _
        (.imp (app2 v4 v0 v2) (accs v0 v2))) (.andER hyp0))

/-- Empty-list case of the induction for `solutionsBelowLeast`. -/
theorem solutionsBelow_nilCase :
    ExtDerivation Symbol Δ (.imp (nilEquation v0) (.app (.app belowCerts v0) nil)) := by
  refine .impI (lam2_intro (.allI (.impI ?_)))
  show ExtDerivation Symbol (app2 v1 v0 nil :: nilEquation v1 :: _) (accs v0 nil)
  exact app2_congr_left (.eqSymm (.impE (.eqPropEL (.allE v0 (hyp1
      (Γ := goals :: listAcceptance :: acceptance :: Γ) (φ := nilEquation v1)))) hyp0))
    (accsNilIntro_derivation (Γ := goals :: listAcceptance :: acceptance :: Γ))

/-- The step of the nonempty-list case: from the claims for the head and the
tail, and a decomposition of the premise list, acceptance of the list. -/
theorem solutionsBelow_consStep
    {Δ' : List (Sentence
      (goals :: goal :: goals :: certs :: cert :: listAcceptance :: acceptance :: Γ))}
    (head : ExtDerivation Symbol Δ' (app2 belowCert v6 v4))
    (tail : ExtDerivation Symbol Δ' (app2 belowCerts v5 v3))
    (headAccepted : ExtDerivation Symbol Δ' (app2 v6 v1 v4))
    (tailAccepted : ExtDerivation Symbol Δ' (app2 v5 v0 v3)) :
    ExtDerivation Symbol Δ' (accs (goalsCons v1 v0) (cons v4 v3)) :=
  .impE (.impE (allE4 v1 v4 v0 v3 (accsConsIntro_derivation
      (Γ := goals :: goal :: goals :: certs :: cert :: listAcceptance :: acceptance :: Γ)))
      (.impE ((allE_inst2 v6 v4 v1 (lam2_elim head) :) : ExtDerivation Symbol _
        (.imp (app2 v6 v1 v4) (acc v1 v4))) headAccepted))
    (.impE ((allE_inst2 v5 v3 v0 (lam2_elim tail) :) : ExtDerivation Symbol _
      (.imp (app2 v5 v0 v3) (accs v0 v3))) tailAccepted)

/-- Nonempty-list case of the induction for `solutionsBelowLeast`. -/
theorem solutionsBelow_consCase :
    ExtDerivation Symbol Δ
      (.imp (consEquation v1 v0) (consClosed (.app belowCert v1) (.app belowCerts v0))) := by
  refine .impI (.allI (.allI (.impI (.impI ?_))))
  show ExtDerivation Symbol
    (app2 belowCerts v2 v0 :: app2 belowCert v3 v1 :: consEquation v3 v2 :: _)
    (app2 belowCerts v2 (cons v1 v0))
  refine lam2_intro (.allI (.impI ?_))
  show ExtDerivation Symbol
    (app2 v3 v0 (cons v2 v1) :: app2 belowCerts v3 v1 :: app2 belowCert v4 v2 ::
      consEquation v4 v3 :: _)
    (accs v0 (cons v2 v1))
  refine .exE (.impE (.eqPropEL (allE3 v2 v1 v0 (hyp3
    (Γ := goals :: certs :: cert :: listAcceptance :: acceptance :: Γ)
    (φ := consEquation v4 v3)))) hyp0) ?_
  refine .exE (hyp0 (Γ := goal :: goals :: certs :: cert :: listAcceptance :: acceptance :: Γ)
    (φ := .ex (σ := goals)
      (.and (.eq v2 (goalsCons v1 v0)) (.and (app2 v6 v1 v4) (app2 v5 v0 v3))))) ?_
  show ExtDerivation Symbol
    (.and (.eq v2 (goalsCons v1 v0)) (.and (app2 v6 v1 v4) (app2 v5 v0 v3)) :: _ ::
      app2 v5 v2 (cons v4 v3) :: app2 belowCerts v5 v3 :: app2 belowCert v6 v4 :: _)
    (accs v2 (cons v4 v3))
  exact app2_congr_left (.eqSymm (.andEL hyp0))
    (solutionsBelow_consStep hyp4 hyp3 (.andEL (.andER hyp0)) (.andER (.andER hyp0)))

end Below

/-- **With induction, every solution is contained in the least acceptance.**
One application of the induction axiom, to the claims `belowCert A` and
`belowCerts B`. -/
theorem solutionsBelowLeast_derivation {Δ : List (Sentence Γ)} :
    ExtDerivation Symbol Δ (.imp certInduction solutionsBelowLeast) := by
  refine .impI (.allI (.allI (.impI (.impI (.impI ?_)))))
  refine .impE (φ := .all (σ := cert) (app2 belowCert v2 v0)) (.impI (.allI ?_)) ?_
  · exact lam2_elim (allE_app2 belowCert v2 v0 (hyp0
      (Γ := cert :: listAcceptance :: acceptance :: Γ)
      (φ := .all (σ := cert) (app2 belowCert v3 v0))))
  · exact .impE (.impE (.impE (allE2 (.app belowCert v1) (.app belowCerts v0) (hyp3
        (Γ := listAcceptance :: acceptance :: Γ) (φ := certInduction)))
        (.impE solutionsBelow_nodeCase hyp2)) (.impE solutionsBelow_nilCase hyp1))
      (.impE solutionsBelow_consCase hyp0)

/-- **Soundness of every solution of the replay equations, from induction.** -/
theorem solutionSoundness_derivation {Δ : List (Sentence Γ)} :
    ExtDerivation Symbol Δ (.imp certInduction solutionSoundness) := by
  refine .impI (.allI (.allI (.impI (.impI (.impI (.allI (.allI (.impI ?_))))))))
  show ExtDerivation Symbol
    (app2 v3 v0 v1 :: consEquation v3 v2 :: nilEquation v2 :: nodeEquation v3 v2 ::
      certInduction :: _)
    (der v0)
  exact .impE (allE2 v1 v0 (soundness_derivation
      (Γ := goal :: cert :: listAcceptance :: acceptance :: Γ)))
    (.impE (allE2_inst2 v3 v2 v1 v0 (.impE (.impE (.impE (allE2 v3 v2 (.impE
      (solutionsBelowLeast_derivation (Γ := goal :: cert :: listAcceptance :: acceptance :: Γ))
      hyp4)) hyp3) hyp2) hyp1)) hyp0)

/-- **Completeness of every solution of the replay equations**, with no
assumption: completeness of the least acceptance and leastness. -/
theorem solutionCompleteness_derivation {Δ : List (Sentence Γ)} :
    ExtDerivation Symbol Δ solutionCompleteness := by
  refine .allI (.allI (.impI (.impI (.impI (.allI (.impI ?_))))))
  show ExtDerivation Symbol
    (der v0 :: consEquation v2 v1 :: nilEquation v1 :: nodeEquation v2 v1 :: _)
    (.ex (σ := cert) (app2 v3 v1 v0))
  refine .exE (.impE (.allE v0 (completeness_derivation
    (Γ := goal :: listAcceptance :: acceptance :: Γ))) hyp0) ?_
  show ExtDerivation Symbol
    (acc v1 v0 :: der v1 :: consEquation v3 v2 :: nilEquation v2 :: nodeEquation v3 v2 :: _)
    (.ex (σ := cert) (app2 v4 v2 v0))
  exact .exI v0 (.impE (allE2_inst2 v3 v2 v0 v1 (.impE (.impE (.impE (allE2 v3 v2
    (leastBelowSolutions_derivation
      (Γ := cert :: goal :: listAcceptance :: acceptance :: Γ))) hyp4) hyp3) hyp2)) hyp0)

/-- **With induction, every solution of the replay equations is the least
acceptance.** -/
theorem solutionUnique_derivation {Δ : List (Sentence Γ)} :
    ExtDerivation Symbol Δ (.imp certInduction solutionUnique) := by
  refine .impI (.allI (.allI (.impI (.impI (.impI (.allI (.allI ?_)))))))
  exact .eqPropI
    (allE2_inst2 v3 v2 v1 v0 (.impE (.impE (.impE (allE2 v3 v2 (.impE
      (solutionsBelowLeast_derivation (Γ := goal :: cert :: listAcceptance :: acceptance :: Γ))
      (hyp3 (Γ := goal :: cert :: listAcceptance :: acceptance :: Γ) (φ := certInduction))))
      (hyp2 (Γ := goal :: cert :: listAcceptance :: acceptance :: Γ)
        (φ := nodeEquation v3 v2)))
      (hyp1 (Γ := goal :: cert :: listAcceptance :: acceptance :: Γ) (φ := nilEquation v2)))
      (hyp0 (Γ := goal :: cert :: listAcceptance :: acceptance :: Γ)
        (φ := consEquation v3 v2))))
    (allE2_inst2 v3 v2 v1 v0 (.impE (.impE (.impE (allE2 v3 v2
      (leastBelowSolutions_derivation
        (Γ := goal :: cert :: listAcceptance :: acceptance :: Γ)))
      (hyp2 (Γ := goal :: cert :: listAcceptance :: acceptance :: Γ)
        (φ := nodeEquation v3 v2)))
      (hyp1 (Γ := goal :: cert :: listAcceptance :: acceptance :: Γ) (φ := nilEquation v2)))
      (hyp0 (Γ := goal :: cert :: listAcceptance :: acceptance :: Γ)
        (φ := consEquation v3 v2))))

/-! ## Consequences in the theory -/

/-- Soundness of the least acceptance holds in the theory (it needs none of
its axioms). -/
theorem soundness_theory : ExtDerivation Symbol (theory (Γ := Γ)) soundness :=
  soundness_derivation

/-- Completeness of the least acceptance holds in the theory (it needs none of
its axioms). -/
theorem completeness_theory : ExtDerivation Symbol (theory (Γ := Γ)) completeness :=
  completeness_derivation

/-- Soundness of every solution of the replay equations holds in the theory. -/
theorem solutionSoundness_theory : ExtDerivation Symbol (theory (Γ := Γ)) solutionSoundness :=
  .impE solutionSoundness_derivation (.hyp mem_theory_certInduction)

/-- Every solution of the replay equations is the least acceptance, in the
theory. -/
theorem solutionUnique_theory : ExtDerivation Symbol (theory (Γ := Γ)) solutionUnique :=
  .impE solutionUnique_derivation (.hyp mem_theory_certInduction)

/-- **Soundness is intuitionistically valid with no assumption**: it holds at
every world of every substitutional Kripke–Henkin structure. -/
theorem soundness_kripkeConsequence :
    KripkeHenkin.Consequence.{0, 0, w} (∅ : ClosedTheorySet Symbol) soundness :=
  KripkeHenkin.consequence_of_provable
    ⟨[], fun _ member => absurd member List.not_mem_nil, soundness_derivation⟩

/-- Completeness is intuitionistically valid with no assumption. -/
theorem completeness_kripkeConsequence :
    KripkeHenkin.Consequence.{0, 0, w} (∅ : ClosedTheorySet Symbol) completeness :=
  KripkeHenkin.consequence_of_provable
    ⟨[], fun _ member => absurd member List.not_mem_nil, completeness_derivation⟩

/-- Soundness of every solution is an intuitionistic consequence of the
induction axiom alone. -/
theorem solutionSoundness_kripkeConsequence :
    KripkeHenkin.Consequence.{0, 0, w} {φ | φ = certInduction} solutionSoundness :=
  KripkeHenkin.consequence_of_provable ⟨[certInduction],
    fun _ member => List.mem_singleton.mp member,
    .impE solutionSoundness_derivation (.hyp List.mem_cons_self)⟩

/-! ## The old theory is interpreted in the new one

Each constant of the replay core with axiomatised acceptance and derivability
is sent to a closed term of the new signature: the constructors and the rule
relation to themselves, acceptance and derivability to their definitions.
Every axiom of the old theory translates to a theorem of the new one, so every
old derivation transports. -/

/-- The constants of the old signature as closed terms of the new one. -/
def interpretOld : {τ : Ty BaseSort} → ReplayCore.Symbol τ → ClosedTerm Symbol τ
  | _, .node => .const .node
  | _, .nil => .const .nil
  | _, .cons => .const .cons
  | _, .goalsNil => .const .goalsNil
  | _, .goalsCons => .const .goalsCons
  | _, .rule => .const .rule
  | _, .acc => accDef
  | _, .accs => accsDef
  | _, .der => derDef
  | _, .ders => dersDef

/-- Translation of old closed sentences. -/
abbrev translate (φ : ReplayCore.Sentence []) : Sentence [] := substConst interpretOld φ

theorem translate_certInduction : translate ReplayCore.certInduction = certInduction := rfl
theorem translate_accNode : translate ReplayCore.accNode = accNode := rfl
theorem translate_accsNil : translate ReplayCore.accsNil = accsNil := rfl
theorem translate_accsCons : translate ReplayCore.accsCons = accsCons := rfl
theorem translate_derRule : translate ReplayCore.derRule = derRule := rfl
theorem translate_dersNil : translate ReplayCore.dersNil = dersNil := rfl
theorem translate_dersCons : translate ReplayCore.dersCons = dersCons := rfl
theorem translate_soundness : translate ReplayCore.soundness = soundness := rfl

/-- **The old axioms are theorems of the new theory.**  Induction is an axiom
of both; the three acceptance equations follow from freeness; the three
closure clauses of derivability need no axiom. -/
theorem translate_theory :
    ∀ φ ∈ ReplayCore.theory (Γ := []), ExtDerivation Symbol (theory (Γ := [])) (translate φ)
  | _, .head _ => translate_certInduction ▸ .hyp mem_theory_certInduction
  | _, .tail _ (.head _) => translate_accNode ▸ accNode_theory
  | _, .tail _ (.tail _ (.head _)) => translate_accsNil ▸ accsNil_theory
  | _, .tail _ (.tail _ (.tail _ (.head _))) => translate_accsCons ▸ accsCons_theory
  | _, .tail _ (.tail _ (.tail _ (.tail _ (.head _)))) => translate_derRule ▸ derRule_derivation
  | _, .tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))) =>
      translate_dersNil ▸ dersNil_derivation
  | _, .tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))) =>
      translate_dersCons ▸ dersCons_derivation

/-- Cut: derivable assumptions can be discharged. -/
theorem cut {Γ' : Ctx BaseSort} {Θ Δ : List (Sentence Γ')} {φ : Sentence Γ'}
    (assumptions : ∀ ψ ∈ Θ, ExtDerivation Symbol Δ ψ) (d : ExtDerivation Symbol Θ φ) :
    ExtDerivation Symbol Δ φ := by
  induction Θ generalizing φ with
  | nil => exact ExtDerivation.mono (fun member => absurd member List.not_mem_nil) d
  | cons ψ Θ ih =>
      exact .impE (ih (fun χ member => assumptions χ (List.mem_cons_of_mem _ member)) (.impI d))
        (assumptions ψ List.mem_cons_self)

/-- **Every derivation of the old theory transports to the new theory.** -/
theorem transport {φ : ReplayCore.Sentence []}
    (d : ExtDerivation ReplayCore.Symbol (ReplayCore.theory (Γ := [])) φ) :
    ExtDerivation Symbol (theory (Γ := [])) (translate φ) :=
  cut (fun ψ member => by
      obtain ⟨χ, hχ, rfl⟩ := List.mem_map.mp member
      exact translate_theory χ hχ)
    (ExtDerivation.substConst_derivation interpretOld d)

/-- The old derivation of soundness, transported: a second derivation of the
soundness sentence in the new theory, through the induction axiom. -/
theorem soundness_transported : ExtDerivation Symbol (theory (Γ := [])) soundness :=
  translate_soundness ▸ transport ReplayCore.soundness_derivation

/-! ## Genuine certificates: the inductive subset

The genuine certificates are the least predicate pair closed under the
certificate constructors.  Induction restricted to them is a theorem, and so
is the soundness of every solution of the replay equations on them: with
certificates taken as an inductive subset, soundness needs no non-logical
axiom at all. -/

/-- The matrix of genuineness, with `Q = v0`, `P = v1` and the certificate `v2`. -/
def certInner : Sentence (certsPredicate :: certPredicate :: cert :: Γ) :=
  .imp (nodeClosed v1 v0) (.imp (.app v0 nil) (.imp (consClosed v1 v0) (.app v1 v2)))

/-- The matrix of list genuineness. -/
def certsInner : Sentence (certsPredicate :: certPredicate :: certs :: Γ) :=
  .imp (nodeClosed v1 v0) (.imp (.app v0 nil) (.imp (consClosed v1 v0) (.app v0 v2)))

/-- Genuine certificates: `λc. ∀ P Q. nodeClosed P Q → Q nil → consClosed P Q → P c`. -/
def certDef : Expr Γ certPredicate :=
  .lam (.all (σ := certPredicate) (.all (σ := certsPredicate) certInner))

/-- Genuine certificate lists, the second component of the same least pair. -/
def certsDef : Expr Γ certsPredicate :=
  .lam (.all (σ := certPredicate) (.all (σ := certsPredicate) certsInner))

def isCert (c : Expr Γ cert) : Sentence Γ := .app certDef c
def isCerts (cs : Expr Γ certs) : Sentence Γ := .app certsDef cs

theorem cert_elim {Δ : List (Sentence Γ)} (P : Expr Γ certPredicate)
    (Q : Expr Γ certsPredicate) {c : Expr Γ cert} (h : ExtDerivation Symbol Δ (isCert c)) :
    ExtDerivation Symbol Δ (subst (inst3 c P Q) certInner) :=
  Eq.mp (congrArg (ExtDerivation Symbol Δ) (subst_inst2_lift_lift_single c P Q certInner))
    (allE2 P Q (lam_elim h))

theorem certs_elim {Δ : List (Sentence Γ)} (P : Expr Γ certPredicate)
    (Q : Expr Γ certsPredicate) {cs : Expr Γ certs} (h : ExtDerivation Symbol Δ (isCerts cs)) :
    ExtDerivation Symbol Δ (subst (inst3 cs P Q) certsInner) :=
  Eq.mp (congrArg (ExtDerivation Symbol Δ) (subst_inst2_lift_lift_single cs P Q certsInner))
    (allE2 P Q (lam_elim h))

/-- Induction on genuine certificates:
`∀ P Q. nodeClosed P Q → Q nil → consClosed P Q → ∀ c. isCert c → P c`. -/
def genuineInduction : Sentence Γ :=
  .all (σ := certPredicate) (.all (σ := certsPredicate)
    (.imp (nodeClosed v1 v0) (.imp (.app v0 nil) (.imp (consClosed v1 v0)
      (.all (σ := cert) (.imp (isCert v0) (.app v2 v0)))))))

/-- **Induction on genuine certificates is a theorem**, read off the
definition of genuineness. -/
theorem genuineInduction_derivation {Δ : List (Sentence Γ)} :
    ExtDerivation Symbol Δ genuineInduction := by
  refine .allI (.allI (.impI (.impI (.impI (.allI (.impI ?_))))))
  show ExtDerivation Symbol
    (isCert v0 :: consClosed v2 v1 :: .app v1 nil :: nodeClosed v2 v1 :: _) (.app v2 v0)
  exact .impE (.impE (.impE (cert_elim v2 v1 (hyp0
    (Γ := cert :: certsPredicate :: certPredicate :: Γ) (φ := isCert v0))) hyp3) hyp2) hyp1

/-- `∀ l cs. isCerts cs → isCert (node l cs)`. -/
def genuineNode : Sentence Γ :=
  .all (σ := label) (.all (σ := certs) (.imp (isCerts v0) (isCert (node v1 v0))))

/-- `isCerts nil`. -/
def genuineNil : Sentence Γ := isCerts nil

/-- `∀ c cs. isCert c → isCerts cs → isCerts (cons c cs)`. -/
def genuineCons : Sentence Γ :=
  .all (σ := cert) (.all (σ := certs)
    (.imp (isCert v1) (.imp (isCerts v0) (isCerts (cons v1 v0)))))

theorem genuineNode_derivation {Δ : List (Sentence Γ)} :
    ExtDerivation Symbol Δ genuineNode := by
  refine .allI (.allI (.impI ?_))
  refine lam_intro (.allI (.allI (.impI (.impI (.impI ?_)))))
  show ExtDerivation Symbol
    (consClosed v1 v0 :: .app v0 nil :: nodeClosed v1 v0 :: isCerts v2 :: _)
    (.app v1 (node v3 v2))
  exact .impE (allE2 v3 v2 (hyp2
      (Γ := certsPredicate :: certPredicate :: certs :: label :: Γ) (φ := nodeClosed v1 v0)))
    (.impE (.impE (.impE (certs_elim v1 v0 (hyp3
      (Γ := certsPredicate :: certPredicate :: certs :: label :: Γ) (φ := isCerts v2)))
      hyp2) hyp1) hyp0)

theorem genuineNil_derivation {Δ : List (Sentence Γ)} :
    ExtDerivation Symbol Δ genuineNil :=
  lam_intro (.allI (.allI (.impI (.impI (.impI hyp1)))))

theorem genuineCons_derivation {Δ : List (Sentence Γ)} :
    ExtDerivation Symbol Δ genuineCons := by
  refine .allI (.allI (.impI (.impI ?_)))
  refine lam_intro (.allI (.allI (.impI (.impI (.impI ?_)))))
  show ExtDerivation Symbol
    (consClosed v1 v0 :: .app v0 nil :: nodeClosed v1 v0 :: isCerts v2 :: isCert v3 :: _)
    (.app v0 (cons v3 v2))
  exact .impE (.impE (allE2 v3 v2 (hyp0
      (Γ := certsPredicate :: certPredicate :: certs :: cert :: Γ) (φ := consClosed v1 v0)))
      (.impE (.impE (.impE (cert_elim v1 v0 (hyp4
        (Γ := certsPredicate :: certPredicate :: certs :: cert :: Γ) (φ := isCert v3)))
        hyp2) hyp1) hyp0))
    (.impE (.impE (.impE (certs_elim v1 v0 (hyp3
      (Γ := certsPredicate :: certPredicate :: certs :: cert :: Γ) (φ := isCerts v2)))
      hyp2) hyp1) hyp0)

/-- The relation `λg c. isCert c`. -/
def genuineCertOf : Expr Γ acceptance := .lam (.lam (isCert v0))

/-- The relation `λps cs. isCerts cs`. -/
def genuineCertsOf : Expr Γ listAcceptance := .lam (.lam (isCerts v0))

theorem weaken_genuineCertOf {σ : Ty BaseSort} :
    weaken (σ := σ) (genuineCertOf (Γ := Γ)) = genuineCertOf := rfl
theorem weaken_genuineCertsOf {σ : Ty BaseSort} :
    weaken (σ := σ) (genuineCertsOf (Γ := Γ)) = genuineCertsOf := rfl

/-- Accepted certificates are genuine: `∀ c g. acc g c → isCert c`. -/
def acceptedGenuine : Sentence Γ :=
  .all (σ := cert) (.all (σ := goal) (.imp (acc v0 v1) (isCert v1)))

/-- Genuineness is closed under the node clause of acceptance. -/
theorem genuine_nodeClosed {Δ : List (Sentence Γ)} :
    ExtDerivation Symbol Δ (accNodeClosed genuineCertOf genuineCertsOf) := by
  refine .allI (.allI (.allI (.allI (.impI (.impI ?_)))))
  dsimp only [weaken_genuineCertOf, weaken_genuineCertsOf]
  refine lam2_intro ?_
  show ExtDerivation Symbol (app2 genuineCertsOf v2 v0 :: _) (isCert (node v3 v0))
  exact .impE (allE2 v3 v0 (genuineNode_derivation (Γ := certs :: goal :: goals :: label :: Γ)))
    ((lam2_elim (hyp0 (Γ := certs :: goal :: goals :: label :: Γ)
      (φ := app2 genuineCertsOf v2 v0)) :) : ExtDerivation Symbol _ (isCerts v0))

/-- Genuineness holds of the empty lists. -/
theorem genuine_nilClosed {Δ : List (Sentence Γ)} :
    ExtDerivation Symbol Δ (accNilClosed genuineCertsOf) :=
  lam2_intro genuineNil_derivation

/-- Genuineness is closed under the nonempty-list clause of acceptance. -/
theorem genuine_consClosed {Δ : List (Sentence Γ)} :
    ExtDerivation Symbol Δ (accConsClosed genuineCertOf genuineCertsOf) := by
  refine .allI (.allI (.allI (.allI (.impI (.impI ?_)))))
  dsimp only [weaken_genuineCertOf, weaken_genuineCertsOf]
  refine lam2_intro ?_
  show ExtDerivation Symbol (app2 genuineCertsOf v1 v0 :: app2 genuineCertOf v3 v2 :: _)
    (isCerts (cons v2 v0))
  exact .impE (.impE (allE2 v2 v0 (genuineCons_derivation
      (Γ := certs :: goals :: cert :: goal :: Γ)))
      ((lam2_elim (hyp1 (Γ := certs :: goals :: cert :: goal :: Γ)
        (φ := app2 genuineCertOf v3 v2)) :) : ExtDerivation Symbol _ (isCert v2)))
    ((lam2_elim (hyp0 (Γ := certs :: goals :: cert :: goal :: Γ)
      (φ := app2 genuineCertsOf v1 v0)) :) : ExtDerivation Symbol _ (isCerts v0))

theorem acceptedGenuine_derivation {Δ : List (Sentence Γ)} :
    ExtDerivation Symbol Δ acceptedGenuine := by
  refine .allI (.allI (.impI ?_))
  exact ((lam2_elim (ExtDerivation.impE (ExtDerivation.impE (ExtDerivation.impE
    (acc_elim genuineCertOf genuineCertsOf (hyp0 (Γ := goal :: cert :: Γ) (φ := acc v0 v1)))
    genuine_nodeClosed) genuine_nilClosed) genuine_consClosed) :) :
      ExtDerivation Symbol _ (isCert v1))

/-- Soundness of every solution of the replay equations on genuine
certificates: `∀ A B. equations → ∀ c. isCert c → ∀ g. A g c → der g`. -/
def genuineSolutionSoundness : Sentence Γ :=
  solutions (.all (σ := cert) (.imp (isCert v0)
    (.all (σ := goal) (.imp (app2 v3 v0 v1) (der v0)))))

/-- **On genuine certificates, every solution of the replay equations is
sound, with no assumption.**  The induction it needs is induction on the
inductive subset, which is a theorem. -/
theorem genuineSolutionSoundness_derivation {Δ : List (Sentence Γ)} :
    ExtDerivation Symbol Δ genuineSolutionSoundness := by
  refine .allI (.allI (.impI (.impI (.impI ?_))))
  refine .impE (φ := .all (σ := cert) (.imp (isCert v0) (app2 belowCert v2 v0)))
    (.impI (.allI (.impI (.allI (.impI ?_))))) ?_
  · show ExtDerivation Symbol
      (app2 v3 v0 v1 :: isCert v1 ::
        .all (σ := cert) (.imp (isCert v0) (app2 belowCert v4 v0)) :: _)
      (der v0)
    exact .impE (allE2 v1 v0 (soundness_derivation
      (Γ := goal :: cert :: listAcceptance :: acceptance :: Γ)))
      ((ExtDerivation.impE (allE_inst2 v3 v1 v0 (lam2_elim
        ((ExtDerivation.impE (ExtDerivation.allE v1 (hyp2
          (Γ := goal :: cert :: listAcceptance :: acceptance :: Γ)
          (φ := .all (σ := cert) (.imp (isCert v0) (app2 belowCert v4 v0)))))
          (hyp1 (Γ := goal :: cert :: listAcceptance :: acceptance :: Γ)
            (φ := isCert v1)) :) : ExtDerivation Symbol _ (app2 belowCert v3 v1))))
        (hyp0 (Γ := goal :: cert :: listAcceptance :: acceptance :: Γ)
          (φ := app2 v3 v0 v1)) :) : ExtDerivation Symbol _ (acc v0 v1))
  · exact .impE (.impE (.impE (allE2 (.app belowCert v1) (.app belowCerts v0)
        (genuineInduction_derivation (Γ := listAcceptance :: acceptance :: Γ)))
        (.impE solutionsBelow_nodeCase hyp2)) (.impE solutionsBelow_nilCase hyp1))
      (.impE solutionsBelow_consCase hyp0)

/-! ## Semantics in standard models

With full predicate domains, the defined predicates denote the least
relations closed under their clauses. -/

section Models

variable {Const : Ty BaseSort → Type}

/-- Satisfaction of a closed sentence does not depend on how the empty
valuation is presented. -/
theorem models_eq_denote (M : HenkinModel.{0, 0, w} BaseSort Const) (φ : Formula Const [])
    (ρ : HenkinModel.Valuation M []) : M.models φ = (M.denote φ ρ).down := by
  unfold HenkinModel.models PreModel.models
  apply congrArg ULift.down
  apply congrArg (PreModel.denote M.toPreModel φ)
  funext τ v
  nomatch v

/-- Object derivations from closed hypotheses are valid in every Henkin model
of the hypotheses whose functions respect extensional equality. -/
theorem models_of_derivation (M : HenkinModel.{0, 0, w} BaseSort Const)
    (extensional : M.FunctionsRespectEqv) {Δ : List (Formula Const [])}
    {φ : Formula Const []} (proof : ExtDerivation Const Δ φ)
    (hypotheses : ∀ ψ ∈ Δ, M.models ψ) : M.models φ :=
  Eq.mpr (models_eq_denote M φ (fun {_} v => nomatch v))
    (Soundness.extDerivation_sound proof (M := M) (ρ := fun {_} v => nomatch v) extensional
      (by intro τ v; nomatch v)
      (by
        intro ψ membership
        exact Eq.mp (models_eq_denote M ψ _) (hypotheses ψ membership)))

/-- A standard model of some hypotheses that refutes a sentence shows that
the sentence is not derivable from them. -/
theorem not_derivable_of_standard (carrier : BaseSort → Type (max 1 w))
    (constant : {τ : Ty BaseSort} → Const τ → Ty.denote.{0, w} carrier τ)
    {Δ : List (Formula Const [])} {φ : Formula Const []}
    (hypotheses : ∀ ψ ∈ Δ, (HenkinModel.standard carrier constant).models ψ)
    (refuted : ¬ (HenkinModel.standard carrier constant).models φ) :
    ¬ ExtDerivation Const Δ φ := fun proof =>
  refuted (models_of_derivation _
    (HenkinModel.functionsRespectEqv_of_fullDomains _
      (HenkinModel.fullDomains_standard carrier constant)) proof hypotheses)

end Models

namespace StandardSemantics

variable {carrier : BaseSort → Type (max 1 w)}
  (constant : {τ : Ty BaseSort} → Symbol τ → Ty.denote.{0, w} carrier τ)

/-- A pair of semantic relations closed under the acceptance clauses. -/
def AccClosed (A : Ty.denote carrier acceptance) (B : Ty.denote carrier listAcceptance) : Prop :=
  (∀ l ps g cs, (constant Symbol.rule l ps g).down → (B ps cs).down →
      (A g (constant Symbol.node l cs)).down) ∧
    (B (constant Symbol.goalsNil) (constant Symbol.nil)).down ∧
    (∀ g c gs cs, (A g c).down → (B gs cs).down →
      (B (constant Symbol.goalsCons g gs) (constant Symbol.cons c cs)).down)

/-- A pair of semantic predicates closed under the rule clauses. -/
def DerClosed (D : Ty.denote carrier goalPredicate) (E : Ty.denote carrier goalsPredicate) :
    Prop :=
  (∀ l ps g, (constant Symbol.rule l ps g).down → (E ps).down → (D g).down) ∧
    (E (constant Symbol.goalsNil)).down ∧
    (∀ g gs, (D g).down → (E gs).down → (E (constant Symbol.goalsCons g gs)).down)

/-- A pair of semantic predicates closed under the certificate constructors. -/
def CertClosed (P : Ty.denote carrier certPredicate) (Q : Ty.denote carrier certsPredicate) :
    Prop :=
  (∀ l cs, (Q cs).down → (P (constant Symbol.node l cs)).down) ∧
    (Q (constant Symbol.nil)).down ∧
    (∀ c cs, (P c).down → (Q cs).down → (Q (constant Symbol.cons c cs)).down)

/-- The genuine certificates of the model. -/
def LeastCert (c : Ty.denote carrier cert) : Prop :=
  ∀ P Q, CertClosed constant P Q → (P c).down

/-- The least acceptance relation of the model. -/
def LeastAcc (g : Ty.denote carrier goal) (c : Ty.denote carrier cert) : Prop :=
  ∀ A B, AccClosed constant A B → (A g c).down

/-- The least list acceptance relation of the model. -/
def LeastAccs (ps : Ty.denote carrier goals) (cs : Ty.denote carrier certs) : Prop :=
  ∀ A B, AccClosed constant A B → (B ps cs).down

/-- The least derivability predicate of the model. -/
def LeastDer (g : Ty.denote carrier goal) : Prop :=
  ∀ D E, DerClosed constant D E → (D g).down

/-- The least list derivability predicate of the model. -/
def LeastDers (ps : Ty.denote carrier goals) : Prop :=
  ∀ D E, DerClosed constant D E → (E ps).down

variable {Γ : Ctx BaseSort}
  (ρ : HenkinModel.Valuation (HenkinModel.standard carrier constant) Γ)

theorem denote_accDef (g : Ty.denote carrier goal) (c : Ty.denote carrier cert) :
    (((HenkinModel.standard carrier constant).denote (accDef (Γ := Γ)) ρ) g c).down ↔
      LeastAcc constant g c := by
  constructor
  · intro h A B closed
    exact h A trivial B trivial (fun l _ ps _ g _ cs _ => closed.1 l ps g cs) closed.2.1
      (fun g _ c _ gs _ cs _ => closed.2.2 g c gs cs)
  · intro h A _ B _ nodeCase nilCase consCase
    exact h A B ⟨fun l ps g cs => nodeCase l trivial ps trivial g trivial cs trivial, nilCase,
      fun g c gs cs => consCase g trivial c trivial gs trivial cs trivial⟩

theorem denote_accsDef (ps : Ty.denote carrier goals) (cs : Ty.denote carrier certs) :
    (((HenkinModel.standard carrier constant).denote (accsDef (Γ := Γ)) ρ) ps cs).down ↔
      LeastAccs constant ps cs := by
  constructor
  · intro h A B closed
    exact h A trivial B trivial (fun l _ ps _ g _ cs _ => closed.1 l ps g cs) closed.2.1
      (fun g _ c _ gs _ cs _ => closed.2.2 g c gs cs)
  · intro h A _ B _ nodeCase nilCase consCase
    exact h A B ⟨fun l ps g cs => nodeCase l trivial ps trivial g trivial cs trivial, nilCase,
      fun g c gs cs => consCase g trivial c trivial gs trivial cs trivial⟩

theorem denote_derDef (g : Ty.denote carrier goal) :
    (((HenkinModel.standard carrier constant).denote (derDef (Γ := Γ)) ρ) g).down ↔
      LeastDer constant g := by
  constructor
  · intro h D E closed
    exact h D trivial E trivial (fun l _ ps _ g _ => closed.1 l ps g) closed.2.1
      (fun g _ gs _ => closed.2.2 g gs)
  · intro h D _ E _ ruleCase nilCase consCase
    exact h D E ⟨fun l ps g => ruleCase l trivial ps trivial g trivial, nilCase,
      fun g gs => consCase g trivial gs trivial⟩

theorem denote_dersDef (ps : Ty.denote carrier goals) :
    (((HenkinModel.standard carrier constant).denote (dersDef (Γ := Γ)) ρ) ps).down ↔
      LeastDers constant ps := by
  constructor
  · intro h D E closed
    exact h D trivial E trivial (fun l _ ps _ g _ => closed.1 l ps g) closed.2.1
      (fun g _ gs _ => closed.2.2 g gs)
  · intro h D _ E _ ruleCase nilCase consCase
    exact h D E ⟨fun l ps g => ruleCase l trivial ps trivial g trivial, nilCase,
      fun g gs => consCase g trivial gs trivial⟩

theorem denote_certDef (c : Ty.denote carrier cert) :
    (((HenkinModel.standard carrier constant).denote (certDef (Γ := Γ)) ρ) c).down ↔
      LeastCert constant c := by
  constructor
  · intro h P Q closed
    exact h P trivial Q trivial (fun l _ cs _ => closed.1 l cs) closed.2.1
      (fun c _ cs _ => closed.2.2 c cs)
  · intro h P _ Q _ nodeCase nilCase consCase
    exact h P Q ⟨fun l cs => nodeCase l trivial cs trivial, nilCase,
      fun c cs => consCase c trivial cs trivial⟩

end StandardSemantics

/-! ## A junk model with free constructors and a loop

Goals and labels have one element each.  Certificates are finite trees plus
one extra element, the loop, which the node operation produces from the
one-child list containing the loop itself.  The node operation is injective,
so the three freeness axioms hold, but induction fails.  The relation "is
the loop" solves the replay equations and accepts the loop, while nothing is
derivable: a solution of the replay equations is unsound without induction.
The least acceptance rejects the loop, as it must. -/

namespace FreeJunkModel

/-- Finite trees and one extra loop. -/
inductive Tree where
  | loop
  | tree (children : List Tree)

/-- The node operation: the loop is the node whose only child is the loop. -/
def attach : List Tree → Tree
  | [.loop] => .loop
  | children => .tree children

theorem attach_eq_loop_iff : ∀ children : List Tree, attach children = .loop ↔ children = [.loop]
  | [] => ⟨fun h => (nomatch h), fun h => (nomatch h)⟩
  | [.loop] => ⟨fun _ => rfl, fun _ => rfl⟩
  | [.tree _] => ⟨fun h => (nomatch h), fun h => (nomatch List.head_eq_of_cons_eq h)⟩
  | .loop :: _ :: _ =>
      ⟨fun h => (nomatch h), fun h => (nomatch List.tail_eq_of_cons_eq h)⟩
  | .tree _ :: _ :: _ =>
      ⟨fun h => (nomatch h), fun h => (nomatch List.head_eq_of_cons_eq h)⟩

theorem attach_of_ne : ∀ children : List Tree, children ≠ [.loop] → attach children = .tree children
  | [], _ => rfl
  | [.loop], h => absurd rfl h
  | [.tree _], _ => rfl
  | .loop :: _ :: _, _ => rfl
  | .tree _ :: _ :: _, _ => rfl

theorem attach_eq_tree : ∀ {children result : List Tree}, attach children = .tree result →
    children = result
  | [], _, h => Tree.tree.inj h
  | [.loop], _, h => nomatch h
  | [.tree _], _, h => Tree.tree.inj h
  | .loop :: _ :: _, _, h => Tree.tree.inj h
  | .tree _ :: _ :: _, _, h => Tree.tree.inj h

/-- The node operation is injective; by cases on its value, without a
decision procedure for equality of trees. -/
theorem attach_injective {first second : List Tree} (h : attach first = attach second) :
    first = second := by
  match hfirst : attach first with
  | .loop =>
      have hsecond : attach second = .loop := h.symm.trans hfirst
      rw [(attach_eq_loop_iff first).mp hfirst, (attach_eq_loop_iff second).mp hsecond]
  | .tree result =>
      have hsecond : attach second = .tree result := h.symm.trans hfirst
      rw [attach_eq_tree hfirst, attach_eq_tree hsecond]

abbrev Lifted (α : Type) := ULift.{1, 0} α

/-- Carriers of the model. -/
def carrier : BaseSort → Type 1
  | .goal => Lifted Unit
  | .label => Lifted Unit
  | .cert => Lifted Tree
  | .certs => Lifted (List Tree)
  | .goals => Lifted (List Unit)

/-- Interpretation of the constants. -/
def constant : {τ : Ty BaseSort} → Symbol τ → Ty.denote.{0, 0} carrier τ
  | _, .node => fun _ children => ⟨attach children.down⟩
  | _, .nil => ⟨[]⟩
  | _, .cons => fun child children => ⟨child.down :: children.down⟩
  | _, .goalsNil => ⟨[]⟩
  | _, .goalsCons => fun premise premises => ⟨premise.down :: premises.down⟩
  | _, .rule => fun _ premises _ => ⟨premises.down = [()]⟩

/-- The model, with full predicate domains. -/
def model : HenkinModel.{0, 0, 0} BaseSort Symbol := HenkinModel.standard carrier constant

/-- The loop is the node of the one label whose only child is the loop. -/
theorem loop_eq_node : constant Symbol.node ⟨()⟩ ⟨[Tree.loop]⟩ = (⟨Tree.loop⟩ : Lifted Tree) :=
  rfl

theorem nodeInjective_valid : model.models nodeInjective := by
  intro l _ children _ l' _ children' _ h
  change (⟨attach children.down⟩ : Lifted Tree) = ⟨attach children'.down⟩ at h
  obtain ⟨⟨⟩⟩ := l
  obtain ⟨⟨⟩⟩ := l'
  exact ⟨rfl, congrArg ULift.up (attach_injective (congrArg ULift.down h))⟩

theorem consInjective_valid : model.models consInjective := by
  intro child _ children _ child' _ children' _ h
  change (⟨child.down :: children.down⟩ : Lifted (List Tree)) =
    ⟨child'.down :: children'.down⟩ at h
  have h' := List.cons.inj (congrArg ULift.down h)
  exact ⟨congrArg ULift.up h'.1, congrArg ULift.up h'.2⟩

theorem consNotNil_valid : model.models consNotNil := by
  intro child _ children _ h
  change (⟨child.down :: children.down⟩ : Lifted (List Tree)) = ⟨[]⟩ at h
  exact nomatch congrArg ULift.down h

theorem freeness_valid : ∀ φ ∈ freeness (Γ := []), model.models φ := by
  intro φ membership
  simp only [freeness, List.mem_cons, List.mem_nil_iff, or_false] at membership
  rcases membership with rfl | rfl | rfl
  · exact nodeInjective_valid
  · exact consInjective_valid
  · exact consNotNil_valid

/-- "Not the loop" is closed under the constructors but excludes the loop. -/
theorem certInduction_invalid : ¬ model.models certInduction := by
  intro h
  have everyCertificate := h (fun certificate => ⟨certificate.down ≠ .loop⟩) trivial
    (fun children => ⟨∀ child ∈ children.down, child ≠ .loop⟩) trivial
    (by
      intro _ _ children _ notLoops hloop
      change ∀ child ∈ children.down, child ≠ .loop at notLoops
      change attach children.down = .loop at hloop
      have single := (attach_eq_loop_iff children.down).mp hloop
      exact notLoops .loop (by rw [single]; exact List.mem_cons_self) rfl)
    (by
      intro child member
      exact absurd member List.not_mem_nil)
    (by
      intro child _ children _ hchild hchildren member hmember
      rcases List.mem_cons.mp hmember with rfl | hmember
      · exact hchild
      · exact hchildren member hmember)
  exact everyCertificate ⟨.loop⟩ trivial rfl

/-- Children accepted for premises: equal lengths, every child the loop. -/
def loops : List Unit → List Tree → Prop
  | [], [] => True
  | _ :: premises, child :: children => child = .loop ∧ loops premises children
  | _, _ => False

theorem loops_single (children : List Tree) : loops [()] children ↔ children = [.loop] := by
  rcases children with _ | ⟨child, _ | ⟨next, rest⟩⟩
  · exact ⟨fun h => False.elim h, fun h => nomatch h⟩
  · constructor
    · rintro ⟨rfl, -⟩
      rfl
    · intro h
      cases h
      exact ⟨rfl, trivial⟩
  · constructor
    · rintro ⟨-, h⟩
      exact False.elim h
    · intro h
      cases h

/-- The junk solution: accept exactly the loop. -/
def loopAcc : Ty.denote.{0, 0} carrier acceptance :=
  fun _ certificate => ⟨certificate.down = .loop⟩

/-- The junk solution on lists. -/
def loopAccs : Ty.denote.{0, 0} carrier listAcceptance :=
  fun premises children => ⟨loops premises.down children.down⟩

/-- Nothing is derivable in the model. -/
theorem not_leastDer (g : Ty.denote.{0, 0} carrier goal) :
    ¬ StandardSemantics.LeastDer constant g := by
  intro derivable
  refine derivable (fun _ => ⟨False⟩) (fun premises => ⟨premises.down = []⟩)
    ⟨?_, rfl, fun _ _ falsity _ => False.elim falsity⟩
  intro _ premises _ ruleHolds premisesHold
  change premises.down = [()] at ruleHolds
  change premises.down = [] at premisesHold
  rw [ruleHolds] at premisesHold
  exact nomatch premisesHold

/-- The least acceptance rejects the loop. -/
theorem not_leastAcc_loop (g : Ty.denote.{0, 0} carrier goal) :
    ¬ StandardSemantics.LeastAcc constant g ⟨.loop⟩ := by
  intro accepted
  refine accepted (fun _ _ => ⟨False⟩)
    (fun premises children => ⟨premises.down = [] ∧ children.down = []⟩)
    ⟨?_, ⟨rfl, rfl⟩, fun _ _ _ _ falsity _ => False.elim falsity⟩
  intro _ premises _ _ ruleHolds premisesHold
  change premises.down = [()] at ruleHolds
  change premises.down = [] ∧ _ at premisesHold
  rw [ruleHolds] at premisesHold
  exact nomatch premisesHold.1

/-- **A solution of the replay equations is unsound without induction.** -/
theorem solutionSoundness_invalid : ¬ model.models solutionSoundness := by
  intro h
  have derivable := h loopAcc trivial loopAccs trivial
    (by
      intro _ _ children _ _ _
      change attach children.down = .loop ↔
        ∃ premises : Lifted (List Unit), True ∧
          (premises.down = [()] ∧ loops premises.down children.down)
      rw [attach_eq_loop_iff]
      constructor
      · intro single
        exact ⟨⟨[()]⟩, trivial, rfl, (loops_single _).mpr single⟩
      · rintro ⟨⟨premises⟩, -, hpremises, hloops⟩
        change premises = [()] at hpremises
        subst hpremises
        exact (loops_single _).mp hloops)
    (by
      intro premises _
      change loops premises.down [] ↔ premises = ⟨[]⟩
      rcases premises with ⟨_ | ⟨premise, rest⟩⟩
      · exact ⟨fun _ => rfl, fun _ => trivial⟩
      · exact ⟨fun h => False.elim h, fun h => by cases h⟩)
    (by
      intro child _ children _ premises _
      change loops premises.down (child.down :: children.down) ↔
        ∃ g : Lifted Unit, True ∧ ∃ gs : Lifted (List Unit), True ∧
          (premises = ⟨g.down :: gs.down⟩ ∧ child.down = .loop ∧ loops gs.down children.down)
      rcases premises with ⟨_ | ⟨premise, rest⟩⟩
      · constructor
        · intro h
          exact False.elim h
        · rintro ⟨g, -, gs, -, h, -⟩
          exact nomatch (congrArg ULift.down h : ([] : List Unit) = g.down :: gs.down)
      · constructor
        · rintro ⟨hchild, hrest⟩
          exact ⟨⟨premise⟩, trivial, ⟨rest⟩, trivial, rfl, hchild, hrest⟩
        · rintro ⟨g, -, gs, -, h, hchild, hrest⟩
          have hrest' : rest = gs.down := (List.cons.inj (congrArg ULift.down h)).2
          rw [hrest']
          exact ⟨hchild, hrest⟩)
    ⟨.loop⟩ trivial ⟨()⟩ trivial rfl
  exact not_leastDer ⟨()⟩ ((StandardSemantics.denote_derDef constant _ ⟨()⟩).mp derivable)

end FreeJunkModel

/-- **Induction is needed for the soundness of a checker given by its replay
equations**, even with free constructors: freeness does not derive it. -/
theorem freeness_do_not_derive_solutionSoundness :
    ¬ ExtDerivation Symbol (freeness (Γ := [])) solutionSoundness :=
  not_derivable_of_standard FreeJunkModel.carrier FreeJunkModel.constant
    FreeJunkModel.freeness_valid FreeJunkModel.solutionSoundness_invalid

/-- Freeness does not derive induction. -/
theorem freeness_do_not_derive_certInduction :
    ¬ ExtDerivation Symbol (freeness (Γ := [])) certInduction :=
  not_derivable_of_standard FreeJunkModel.carrier FreeJunkModel.constant
    FreeJunkModel.freeness_valid FreeJunkModel.certInduction_invalid

/-! ## Each freeness axiom is needed for its equation

Three standard models, each validating induction and two of the three
freeness axioms, refute the third freeness axiom and the acceptance equation
that depends on it. -/

namespace CollapsedNodeModel

abbrev Lifted (α : Type) := ULift.{1, 0} α

/-- Two labels, one certificate: the node operation forgets its label. -/
def carrier : BaseSort → Type 1
  | .goal => Lifted Unit
  | .label => Lifted Bool
  | .cert => Lifted Unit
  | .certs => Lifted (List Unit)
  | .goals => Lifted (List Unit)

/-- Only the label `true`, with no premises, is a rule. -/
def constant : {τ : Ty BaseSort} → Symbol τ → Ty.denote.{0, 0} carrier τ
  | _, .node => fun _ _ => ⟨()⟩
  | _, .nil => ⟨[]⟩
  | _, .cons => fun child children => ⟨child.down :: children.down⟩
  | _, .goalsNil => ⟨[]⟩
  | _, .goalsCons => fun premise premises => ⟨premise.down :: premises.down⟩
  | _, .rule => fun l premises _ => ⟨l.down = true ∧ premises.down = []⟩

def model : HenkinModel.{0, 0, 0} BaseSort Symbol := HenkinModel.standard carrier constant

theorem certInduction_valid : model.models certInduction := by
  intro P _ Q _ nodeCase nilCase _ certificate _
  obtain ⟨⟨⟩⟩ := certificate
  exact nodeCase ⟨true⟩ trivial ⟨[]⟩ trivial nilCase

theorem consInjective_valid : model.models consInjective := by
  intro child _ children _ child' _ children' _ h
  change (⟨child.down :: children.down⟩ : Lifted (List Unit)) =
    ⟨child'.down :: children'.down⟩ at h
  have h' := List.cons.inj (congrArg ULift.down h)
  exact ⟨congrArg ULift.up h'.1, congrArg ULift.up h'.2⟩

theorem consNotNil_valid : model.models consNotNil := by
  intro child _ children _ h
  change (⟨child.down :: children.down⟩ : Lifted (List Unit)) = ⟨[]⟩ at h
  exact nomatch congrArg ULift.down h

theorem nodeInjective_invalid : ¬ model.models nodeInjective := by
  intro h
  have labels := (h ⟨true⟩ trivial ⟨[]⟩ trivial ⟨false⟩ trivial ⟨[]⟩ trivial rfl).1
  exact nomatch congrArg ULift.down labels

/-- The one goal is accepted for the one certificate. -/
theorem leastAcc_unit : StandardSemantics.LeastAcc constant ⟨()⟩ ⟨()⟩ := fun _ _ closed =>
  closed.1 ⟨true⟩ ⟨[]⟩ ⟨()⟩ ⟨[]⟩ ⟨rfl, rfl⟩ closed.2.1

/-- The node equation fails at the label `false`. -/
theorem accNode_invalid : ¬ model.models accNode := by
  intro h
  obtain ⟨premises, -, rulesHold, -⟩ := (h ⟨false⟩ trivial ⟨[]⟩ trivial ⟨()⟩ trivial).mp
    ((StandardSemantics.denote_accDef constant _ ⟨()⟩ ⟨()⟩).mpr leastAcc_unit)
  exact nomatch rulesHold.1

theorem hypotheses_valid :
    ∀ φ ∈ [certInduction, consInjective, consNotNil (Γ := [])], model.models φ := by
  intro φ membership
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at membership
  rcases membership with rfl | rfl | rfl
  · exact certInduction_valid
  · exact consInjective_valid
  · exact consNotNil_valid

end CollapsedNodeModel

/-- Injectivity of the node constructor is needed for the node equation. -/
theorem nodeInjective_needed :
    ¬ ExtDerivation Symbol [certInduction, consInjective, consNotNil (Γ := [])] accNode :=
  not_derivable_of_standard CollapsedNodeModel.carrier CollapsedNodeModel.constant
    CollapsedNodeModel.hypotheses_valid CollapsedNodeModel.accNode_invalid

namespace CollapsedListModel

abbrev Lifted (α : Type) := ULift.{1, 0} α

/-- One certificate and one certificate list: `cons c cs = nil`. -/
def carrier : BaseSort → Type 1
  | .goal => Lifted Unit
  | .label => Lifted Unit
  | .cert => Lifted Unit
  | .certs => Lifted Unit
  | .goals => Lifted (List Unit)

/-- The one label is a rule with no premises. -/
def constant : {τ : Ty BaseSort} → Symbol τ → Ty.denote.{0, 0} carrier τ
  | _, .node => fun _ _ => ⟨()⟩
  | _, .nil => ⟨()⟩
  | _, .cons => fun _ _ => ⟨()⟩
  | _, .goalsNil => ⟨[]⟩
  | _, .goalsCons => fun premise premises => ⟨premise.down :: premises.down⟩
  | _, .rule => fun _ premises _ => ⟨premises.down = []⟩

def model : HenkinModel.{0, 0, 0} BaseSort Symbol := HenkinModel.standard carrier constant

theorem certInduction_valid : model.models certInduction := by
  intro P _ Q _ nodeCase nilCase _ certificate _
  obtain ⟨⟨⟩⟩ := certificate
  exact nodeCase ⟨()⟩ trivial ⟨()⟩ trivial nilCase

theorem nodeInjective_valid : model.models nodeInjective := by
  intro l _ children _ l' _ children' _ _
  obtain ⟨⟨⟩⟩ := l
  obtain ⟨⟨⟩⟩ := l'
  obtain ⟨⟨⟩⟩ := children
  obtain ⟨⟨⟩⟩ := children'
  exact ⟨rfl, rfl⟩

theorem consInjective_valid : model.models consInjective := by
  intro child _ children _ child' _ children' _ _
  obtain ⟨⟨⟩⟩ := child
  obtain ⟨⟨⟩⟩ := child'
  obtain ⟨⟨⟩⟩ := children
  obtain ⟨⟨⟩⟩ := children'
  exact ⟨rfl, rfl⟩

theorem consNotNil_invalid : ¬ model.models consNotNil := fun h =>
  h ⟨()⟩ trivial ⟨()⟩ trivial rfl

/-- The one-premise list is accepted for the empty list. -/
theorem leastAccs_single : StandardSemantics.LeastAccs constant ⟨[()]⟩ ⟨()⟩ := fun _ _ closed =>
  closed.2.2 ⟨()⟩ ⟨()⟩ ⟨[]⟩ ⟨()⟩ (closed.1 ⟨()⟩ ⟨[]⟩ ⟨()⟩ ⟨()⟩ rfl closed.2.1) closed.2.1

/-- The empty-list equation fails at the one-premise list. -/
theorem accsNil_invalid : ¬ model.models accsNil := by
  intro h
  have emptied := (h ⟨[()]⟩ trivial).mp
    ((StandardSemantics.denote_accsDef constant _ ⟨[()]⟩ ⟨()⟩).mpr leastAccs_single)
  exact nomatch congrArg ULift.down emptied

theorem hypotheses_valid :
    ∀ φ ∈ [certInduction, nodeInjective, consInjective (Γ := [])], model.models φ := by
  intro φ membership
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at membership
  rcases membership with rfl | rfl | rfl
  · exact certInduction_valid
  · exact nodeInjective_valid
  · exact consInjective_valid

end CollapsedListModel

/-- `cons c cs ≠ nil` is needed for the empty-list equation. -/
theorem consNotNil_needed :
    ¬ ExtDerivation Symbol [certInduction, nodeInjective, consInjective (Γ := [])] accsNil :=
  not_derivable_of_standard CollapsedListModel.carrier CollapsedListModel.constant
    CollapsedListModel.hypotheses_valid CollapsedListModel.accsNil_invalid

namespace CollapsedConsModel

abbrev Lifted (α : Type) := ULift.{1, 0} α

/-- Boolean certificates and lists: `nil = false`, every `cons` is `true`,
and the node operation returns its children. -/
def carrier : BaseSort → Type 1
  | .goal => Lifted Unit
  | .label => Lifted Unit
  | .cert => Lifted Bool
  | .certs => Lifted Bool
  | .goals => Lifted (List Unit)

def constant : {τ : Ty BaseSort} → Symbol τ → Ty.denote.{0, 0} carrier τ
  | _, .node => fun _ children => ⟨children.down⟩
  | _, .nil => ⟨false⟩
  | _, .cons => fun _ _ => ⟨true⟩
  | _, .goalsNil => ⟨[]⟩
  | _, .goalsCons => fun premise premises => ⟨premise.down :: premises.down⟩
  | _, .rule => fun _ premises _ => ⟨premises.down = []⟩

def model : HenkinModel.{0, 0, 0} BaseSort Symbol := HenkinModel.standard carrier constant

theorem certInduction_valid : model.models certInduction := by
  intro P _ Q _ nodeCase nilCase consCase certificate _
  have atFalse : (P ⟨false⟩).down := nodeCase ⟨()⟩ trivial ⟨false⟩ trivial nilCase
  have listTrue : (Q ⟨true⟩).down := consCase ⟨false⟩ trivial ⟨false⟩ trivial atFalse nilCase
  have atTrue : (P ⟨true⟩).down := nodeCase ⟨()⟩ trivial ⟨true⟩ trivial listTrue
  obtain ⟨b⟩ := certificate
  cases b
  · exact atFalse
  · exact atTrue

theorem nodeInjective_valid : model.models nodeInjective := by
  intro l _ children _ l' _ children' _ h
  obtain ⟨⟨⟩⟩ := l
  obtain ⟨⟨⟩⟩ := l'
  exact ⟨rfl, h⟩

theorem consNotNil_valid : model.models consNotNil := by
  intro _ _ _ _ h
  change (⟨true⟩ : Lifted Bool) = ⟨false⟩ at h
  exact nomatch congrArg ULift.down h

theorem consInjective_invalid : ¬ model.models consInjective := by
  intro h
  have heads := (h ⟨false⟩ trivial ⟨false⟩ trivial ⟨true⟩ trivial ⟨false⟩ trivial rfl).1
  exact nomatch congrArg ULift.down heads

/-- The one-premise list is accepted for the list `true`. -/
theorem leastAccs_single : StandardSemantics.LeastAccs constant ⟨[()]⟩ ⟨true⟩ :=
  fun _ _ closed => closed.2.2 ⟨()⟩ ⟨false⟩ ⟨[]⟩ ⟨false⟩
    (closed.1 ⟨()⟩ ⟨[]⟩ ⟨()⟩ ⟨false⟩ rfl closed.2.1) closed.2.1

/-- Which certificate lists a premise list can accept. -/
def listShape : List Unit → Bool → Prop
  | [], b => b = false
  | _ :: _, b => b = true

/-- The certificate `true` is accepted for no goal. -/
theorem not_leastAcc_true (g : Ty.denote.{0, 0} carrier goal) :
    ¬ StandardSemantics.LeastAcc constant g ⟨true⟩ := by
  intro accepted
  refine nomatch (accepted (fun _ certificate => ⟨certificate.down = false⟩)
    (fun premises children => ⟨listShape premises.down children.down⟩)
    ⟨?_, rfl, fun _ _ _ _ _ _ => rfl⟩ : true = false)
  intro _ premises _ children ruleHolds childrenHold
  change premises.down = [] at ruleHolds
  change listShape premises.down children.down at childrenHold
  rw [ruleHolds] at childrenHold
  exact childrenHold

/-- The nonempty-list equation fails at `cons true false`. -/
theorem accsCons_invalid : ¬ model.models accsCons := by
  intro h
  obtain ⟨g, -, _, -, -, headAccepted, -⟩ := (h ⟨true⟩ trivial ⟨false⟩ trivial ⟨[()]⟩ trivial).mp
    ((StandardSemantics.denote_accsDef constant _ ⟨[()]⟩ ⟨true⟩).mpr leastAccs_single)
  exact not_leastAcc_true g ((StandardSemantics.denote_accDef constant _ g ⟨true⟩).mp headAccepted)

theorem hypotheses_valid :
    ∀ φ ∈ [certInduction, nodeInjective, consNotNil (Γ := [])], model.models φ := by
  intro φ membership
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at membership
  rcases membership with rfl | rfl | rfl
  · exact certInduction_valid
  · exact nodeInjective_valid
  · exact consNotNil_valid

end CollapsedConsModel

/-- Injectivity of `cons` is needed for the nonempty-list equation. -/
theorem consInjective_needed :
    ¬ ExtDerivation Symbol [certInduction, nodeInjective, consNotNil (Γ := [])] accsCons :=
  not_derivable_of_standard CollapsedConsModel.carrier CollapsedConsModel.constant
    CollapsedConsModel.hypotheses_valid CollapsedConsModel.accsCons_invalid

/-! ## Leastness is what completeness needs

In the old signature derivability is a constant closed under the rule clauses,
not the least such predicate.  A model of the whole old theory, with
induction, interprets it as "everything", has no rules, and refutes
completeness.  Its translation is a theorem with no assumption. -/

/-- Completeness in the old signature: `∀ g. der g → ∃ c. acc g c`. -/
def oldCompleteness : ReplayCore.Sentence [] :=
  .all (σ := goal) (.imp (ReplayCore.der ReplayCore.v0)
    (.ex (σ := cert) (ReplayCore.acc ReplayCore.v1 ReplayCore.v0)))

theorem translate_oldCompleteness : translate oldCompleteness = completeness := rfl

namespace OldTopModel

abbrev Lifted (α : Type) := ULift.{1, 0} α

def carrier : BaseSort → Type 1
  | .goal => Lifted Unit
  | .label => Lifted Unit
  | .cert => Lifted Unit
  | .certs => Lifted (List Unit)
  | .goals => Lifted (List Unit)

/-- No rules, no accepted certificate, and every goal "derivable". -/
def constant : {τ : Ty BaseSort} → ReplayCore.Symbol τ → Ty.denote.{0, 0} carrier τ
  | _, .node => fun _ _ => ⟨()⟩
  | _, .nil => ⟨[]⟩
  | _, .cons => fun child children => ⟨child.down :: children.down⟩
  | _, .goalsNil => ⟨[]⟩
  | _, .goalsCons => fun premise premises => ⟨premise.down :: premises.down⟩
  | _, .rule => fun _ _ _ => ⟨False⟩
  | _, .acc => fun _ _ => ⟨False⟩
  | _, .accs => fun premises children => ⟨premises.down = [] ∧ children.down = []⟩
  | _, .der => fun _ => ⟨True⟩
  | _, .ders => fun _ => ⟨True⟩

def model : HenkinModel.{0, 0, 0} BaseSort ReplayCore.Symbol :=
  HenkinModel.standard carrier constant

theorem theory_valid : ∀ φ ∈ ReplayCore.theory (Γ := []), model.models φ := by
  intro φ membership
  simp only [ReplayCore.theory, ReplayCore.clauses, List.mem_cons, List.mem_nil_iff,
    or_false] at membership
  rcases membership with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · intro P _ Q _ nodeCase nilCase _ certificate _
    obtain ⟨⟨⟩⟩ := certificate
    exact nodeCase ⟨()⟩ trivial ⟨[]⟩ trivial nilCase
  · intro _ _ _ _ _ _
    exact ⟨False.elim, fun ⟨_, _, ruleHolds, _⟩ => ruleHolds⟩
  · intro premises _
    change premises.down = [] ∧ ([] : List Unit) = [] ↔ premises = ⟨[]⟩
    exact ⟨fun h => congrArg ULift.up h.1, fun h => ⟨congrArg ULift.down h, rfl⟩⟩
  · intro _ _ _ _ _ _
    exact ⟨fun h => (nomatch h.2), fun ⟨_, _, _, _, _, accepted, _⟩ => False.elim accepted⟩
  · intro _ _ _ _ _ _ _ _
    trivial
  · trivial
  · intro _ _ _ _ _ _
    trivial

theorem oldCompleteness_invalid : ¬ model.models oldCompleteness := by
  intro h
  obtain ⟨_, _, accepted⟩ := h ⟨()⟩ trivial trivial
  exact accepted

end OldTopModel

/-- **The old theory does not derive completeness**: its derivability need
not be least.  The translation of the same sentence is a theorem of the new
theory with no assumption (`completeness_derivation`). -/
theorem oldTheory_does_not_derive_completeness :
    ¬ ExtDerivation ReplayCore.Symbol (ReplayCore.theory (Γ := [])) oldCompleteness :=
  not_derivable_of_standard OldTopModel.carrier OldTopModel.constant
    OldTopModel.theory_valid OldTopModel.oldCompleteness_invalid

/-- The translated completeness sentence is a theorem. -/
theorem translated_completeness :
    ExtDerivation Symbol ([] : List (Sentence [])) (translate oldCompleteness) :=
  translate_oldCompleteness ▸ completeness_derivation

end Mettapedia.Logic.HOL.ReplayCoreDefined
