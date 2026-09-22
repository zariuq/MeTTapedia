import Mettapedia.Languages.OpenTheory.TheoryClosure
import Mettapedia.Logic.HOL.TypeSubstitutionDerivation
import Mettapedia.Logic.HOL.CanonicalTheory
import Mettapedia.Logic.HOL.Semantics.HeytingGeneral

/-!
# The OpenTheory primitive kernel in extensional higher-order logic

The nine primitive OpenTheory rules of `PrimitiveRules.lean` are interpreted
in the extensional higher-order calculus `HOL.ExtDerivation`.  Every theorem
of the least policy closure of `TheoryClosure.lean` has a translated sequent
whose conclusion is provable from its translated hypotheses and from
background sentences that prove its axiom tags.

## Design

* Types: `bool` becomes the proposition type, `a -> b` an arrow, and every
  other OpenTheory type (type variables and all other type-operator
  applications) is a base type.  The base types are exactly the atomic
  OpenTheory types (`AtomicTy`); the type translation is injective and
  surjective.
* Constants and free variables: every OpenTheory constant occurrence, with
  its provenance and type annotation, and every free OpenTheory variable
  (name and type) is a constant symbol of the target (`Symbol`).  Sequents
  therefore translate to closed formulas.  The freshness condition of `abs`
  becomes the hypothesis of the theorem on constants
  (`HOL.ExtDerivation.abstractConstAt_deriv`), and term substitution becomes
  substitution of closed terms for symbols (`HOL.substConst`) after the type
  substitution (`HOL.mapTypes`).
* Bound variables: canonical de Bruijn indices become typed de Bruijn
  variables at the same position.
* Equality: a full application `(= : a -> a -> bool) l r` becomes the target
  equality `l = r`; an unapplied or partially applied occurrence becomes
  `λ x y. x = y`.  An occurrence of `=` at any other annotation is an ordinary
  constant symbol.  The compositional variant (`TranslatesCompositionally`)
  uses `λ x y. x = y` for every occurrence and commutes with abstraction,
  instantiation and substitution syntactically; the two translations agree up
  to provable equality (`Translates.extDerivation_eq_compositional`).
* Terms: both translations are relations whose type premises are equations;
  they are functional (`Translates.unique`), and exactly the well-typed terms
  translate (`exists_translates_iff_inferType_isSome`).
* Hypotheses: a finite hypothesis set becomes a set of closed formulas, and
  provability is `ClosedTheorySet.Provable`, derivability by
  `HOL.ExtDerivation` from a finite list of members.
* Axioms: an axiom tag is a sequent schema, since `subst` instantiates it.
  Tags are interpreted by background sentences `Θ` that mention no
  free-variable symbol and are closed under the target image of every
  admitted substitution (`VariableFreeSubstitutionClosed`); every tag of a
  theorem must be provable from `Θ`.  Untagged theorems use `Θ = ∅`.

## Main results

* `derives_translatedProvable`: the interpretation of the policy closure.
* `checkPrimitive_translatedProvable`: one step of the executable checker.
* `derives_heytingConsequence_of_emptyAxiomPolicy`, `derives_models`:
  soundness over Heyting-valued substitutional models and over extensional
  Henkin models.
* `falsity_not_derivable`: the axiom-free kernel does not derive `⊢ F`.
* `InterpretationExamples.unrestrictedAbs_step_leaves_untagged_closure`:
  without its freshness condition, `abs` maps a derivable theorem to a
  sequent that fails in a two-element model.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.OpenTheory

open Mettapedia.Logic

/-! ## Types -/

namespace Ty

theorem eq_function_of_destFunction? {ty domain codomain : Ty}
    (h : ty.destFunction? = some (domain, codomain)) :
    ty = .function domain codomain := by
  cases ty with
  | var name => simp [destFunction?] at h
  | op operator arguments =>
      match arguments, h with
      | [first, second], h =>
          simp only [destFunction?] at h
          split at h
          · rename_i same
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            have := (TypeOp.same_eq_true_iff _ _).mp same
            subst this
            rfl
          · contradiction

@[simp] theorem destFunction?_bool : Ty.bool.destFunction? = none := rfl

theorem function_inj {domain codomain domain' codomain' : Ty}
    (h : Ty.function domain codomain = Ty.function domain' codomain') :
    domain = domain' ∧ codomain = codomain' := by
  simp only [Ty.function, Ty.op.injEq, List.cons.injEq] at h
  exact ⟨h.2.1, h.2.2.1⟩

theorem sizeOf_domain_lt (domain codomain : Ty) :
    sizeOf domain < sizeOf (Ty.function domain codomain) := by
  simp only [Ty.function, Ty.op.sizeOf_spec, List.cons.sizeOf_spec]
  omega

theorem sizeOf_codomain_lt (domain codomain : Ty) :
    sizeOf codomain < sizeOf (Ty.function domain codomain) := by
  simp only [Ty.function, Ty.op.sizeOf_spec, List.cons.sizeOf_spec]
  omega

/-- A type is atomic for the higher-order translation when it is neither the
exact primitive Boolean type nor an exact function type.  Type variables and
all other type-operator applications are atomic. -/
def IsAtomic (ty : Ty) : Prop := ty.destFunction? = none ∧ ty.isBool = false

end Ty

/-- The base types of the target calculus: exactly the atomic OpenTheory
types. -/
abbrev AtomicTy : Type := {ty : Ty // ty.IsAtomic}

namespace Ty

/-- Translate an OpenTheory type: `bool` to the proposition type, `a -> b`
to an arrow, and every atomic type to itself as a base type. -/
def toHOL (ty : Ty) : HOL.Ty AtomicTy :=
  match hfunction : ty.destFunction? with
  | some (domain, codomain) => .arr domain.toHOL codomain.toHOL
  | none =>
      if hbool : ty.isBool then .prop
      else .base ⟨ty, hfunction, Bool.eq_false_iff.mpr hbool⟩
termination_by sizeOf ty
decreasing_by
  all_goals
    rw [eq_function_of_destFunction? hfunction]
    first
    | exact sizeOf_domain_lt _ _
    | exact sizeOf_codomain_lt _ _

@[simp] theorem toHOL_function (domain codomain : Ty) :
    (Ty.function domain codomain).toHOL = .arr domain.toHOL codomain.toHOL := by
  rw [toHOL]
  split
  · rename_i domain' codomain' h
    rw [destFunction?_function] at h
    cases h
    rfl
  · rename_i h
    rw [destFunction?_function] at h
    contradiction

@[simp] theorem toHOL_bool : Ty.bool.toHOL = .prop := by
  rw [toHOL]
  split
  · rename_i h
    simp at h
  · rw [dif_pos ((Ty.isBool_eq_true_iff _).mpr rfl)]

theorem toHOL_of_isAtomic {ty : Ty} (atomic : ty.IsAtomic) :
    ty.toHOL = .base ⟨ty, atomic⟩ := by
  rw [toHOL]
  split
  · rename_i h
    rw [atomic.1] at h
    contradiction
  · rw [dif_neg (by simp [atomic.2])]

/-- Every OpenTheory type is a function type, `bool`, or atomic. -/
theorem function_or_bool_or_isAtomic (ty : Ty) :
    (∃ domain codomain, ty = .function domain codomain) ∨ ty = Ty.bool ∨
      ty.IsAtomic := by
  cases hfunction : ty.destFunction? with
  | some pair =>
      exact Or.inl ⟨pair.1, pair.2, eq_function_of_destFunction? hfunction⟩
  | none =>
      cases hbool : ty.isBool with
      | true => exact Or.inr (Or.inl ((isBool_eq_true_iff ty).mp hbool))
      | false => exact Or.inr (Or.inr ⟨hfunction, hbool⟩)

theorem toHOL_eq_arr_iff {ty : Ty} {σ τ : HOL.Ty AtomicTy} :
    ty.toHOL = .arr σ τ ↔
      ∃ domain codomain, ty = .function domain codomain ∧
        domain.toHOL = σ ∧ codomain.toHOL = τ := by
  constructor
  · intro h
    rcases function_or_bool_or_isAtomic ty with
      ⟨domain, codomain, rfl⟩ | rfl | atomic
    · rw [toHOL_function] at h
      cases h
      exact ⟨domain, codomain, rfl, rfl, rfl⟩
    · simp at h
    · rw [toHOL_of_isAtomic atomic] at h
      cases h
  · rintro ⟨domain, codomain, rfl, rfl, rfl⟩
    exact toHOL_function domain codomain

theorem toHOL_eq_prop_iff {ty : Ty} : ty.toHOL = .prop ↔ ty = Ty.bool := by
  constructor
  · intro h
    rcases function_or_bool_or_isAtomic ty with
      ⟨domain, codomain, rfl⟩ | rfl | atomic
    · simp at h
    · rfl
    · rw [toHOL_of_isAtomic atomic] at h
      cases h
  · rintro rfl
    exact toHOL_bool

theorem toHOL_eq_base_iff {ty : Ty} {base : AtomicTy} :
    ty.toHOL = .base base ↔ ty = base.1 := by
  constructor
  · intro h
    rcases function_or_bool_or_isAtomic ty with
      ⟨domain, codomain, rfl⟩ | rfl | atomic
    · simp at h
    · simp at h
    · rw [toHOL_of_isAtomic atomic] at h
      cases h
      rfl
  · rintro rfl
    exact toHOL_of_isAtomic base.2

/-- The type translation is injective. -/
theorem toHOL_injective : ∀ {left right : Ty}, left.toHOL = right.toHOL → left = right
  | left, right, h => by
    rcases function_or_bool_or_isAtomic left with
      ⟨domain, codomain, rfl⟩ | rfl | atomic
    · rw [toHOL_function] at h
      obtain ⟨domain', codomain', rfl, hdomain, hcodomain⟩ :=
        toHOL_eq_arr_iff.mp h.symm
      have : sizeOf domain < sizeOf (Ty.function domain codomain) :=
        sizeOf_domain_lt domain codomain
      have : sizeOf codomain < sizeOf (Ty.function domain codomain) :=
        sizeOf_codomain_lt domain codomain
      rw [toHOL_injective hdomain.symm, toHOL_injective hcodomain.symm]
    · rw [toHOL_bool] at h
      exact (toHOL_eq_prop_iff.mp h.symm).symm
    · rw [toHOL_of_isAtomic atomic] at h
      exact (toHOL_eq_base_iff.mp h.symm).symm
termination_by left => sizeOf left

/-- Every target type is the translation of an OpenTheory type. -/
theorem toHOL_surjective : ∀ τ : HOL.Ty AtomicTy, ∃ ty : Ty, ty.toHOL = τ
  | .prop => ⟨Ty.bool, toHOL_bool⟩
  | .base base => ⟨base.1, toHOL_of_isAtomic base.2⟩
  | .arr σ τ => by
      obtain ⟨domain, rfl⟩ := toHOL_surjective σ
      obtain ⟨codomain, rfl⟩ := toHOL_surjective τ
      exact ⟨.function domain codomain, toHOL_function domain codomain⟩

@[simp] theorem toHOL_equality (operand : Ty) :
    (Ty.equality operand).toHOL =
      .arr operand.toHOL (.arr operand.toHOL .prop) := by
  simp [Ty.equality]

end Ty

/-! ## Type substitution -/

namespace TypeSubst

@[simp] theorem apply_bool (substitution : TypeSubst) :
    substitution.apply Ty.bool = Ty.bool := by
  simp [Ty.bool]

@[simp] theorem apply_equality (substitution : TypeSubst) (operand : Ty) :
    substitution.apply (Ty.equality operand) =
      Ty.equality (substitution.apply operand) := by
  simp [Ty.equality]

/-- The base-type interpretation induced by an OpenTheory type substitution. -/
def baseInstance (substitution : TypeSubst) (base : AtomicTy) :
    HOL.Ty AtomicTy :=
  (substitution.apply base.1).toHOL

/-- Target type substitution agrees with OpenTheory type substitution. -/
theorem substitute_toHOL (substitution : TypeSubst) :
    ∀ ty : Ty, HOL.Ty.substitute substitution.baseInstance ty.toHOL =
      (substitution.apply ty).toHOL
  | ty => by
    rcases Ty.function_or_bool_or_isAtomic ty with
      ⟨domain, codomain, rfl⟩ | rfl | atomic
    · have : sizeOf domain < sizeOf (Ty.function domain codomain) :=
        Ty.sizeOf_domain_lt domain codomain
      have : sizeOf codomain < sizeOf (Ty.function domain codomain) :=
        Ty.sizeOf_codomain_lt domain codomain
      rw [Ty.toHOL_function, apply_function, Ty.toHOL_function,
        HOL.Ty.substitute_arr, substitute_toHOL substitution domain,
        substitute_toHOL substitution codomain]
    · rw [Ty.toHOL_bool, apply_bool, Ty.toHOL_bool]
      rfl
    · rw [Ty.toHOL_of_isAtomic atomic]
      rfl
termination_by ty => sizeOf ty

end TypeSubst

/-! ## Target signature -/

/-- Constant symbols of the target calculus.  An OpenTheory constant occurrence
keeps its provenance and type annotation, and a free OpenTheory variable is a
constant symbol as well.  The index is the translated annotation type. -/
inductive Symbol : HOL.Ty AtomicTy → Type
  | constant (constant : Const) (annotation : Ty) {τ : HOL.Ty AtomicTy}
      (typed : annotation.toHOL = τ) : Symbol τ
  | variable (sourceVar : SourceVar) {τ : HOL.Ty AtomicTy}
      (typed : sourceVar.ty.toHOL = τ) : Symbol τ

namespace Symbol

/-- The target symbol of one free OpenTheory variable at its own type. -/
abbrev ofVar (sourceVar : SourceVar) : Symbol sourceVar.ty.toHOL :=
  .variable sourceVar rfl

end Symbol

/-- Recognize the primitive equality constant at an exact equality type
`a -> a -> bool`, returning the operand type `a`. -/
def equalityOperand? (constant : Const) (annotation : Ty) : Option Ty :=
  if Const.same constant Const.equality then
    match annotation.destFunction? with
    | some (operand, rest) =>
        match rest.destFunction? with
        | some (operand', result) =>
            if Ty.same operand operand' && result.isBool then some operand else none
        | none => none
    | none => none
  else
    none

theorem equalityOperand?_eq_some_iff (constant : Const) (annotation operand : Ty) :
    equalityOperand? constant annotation = some operand ↔
      constant = Const.equality ∧ annotation = Ty.equality operand := by
  constructor
  · intro h
    unfold equalityOperand? at h
    split at h
    · rename_i hconstant
      refine ⟨(Const.same_eq_true_iff _ _).mp hconstant, ?_⟩
      split at h
      · rename_i operand₁ rest hfunction
        split at h
        · rename_i operand₂ result hrest
          split at h
          · rename_i hcheck
            simp only [Bool.and_eq_true, Ty.same_eq_true_iff,
              Ty.isBool_eq_true_iff] at hcheck
            obtain ⟨rfl, rfl⟩ := hcheck
            cases h
            rw [Ty.eq_function_of_destFunction? hfunction,
              Ty.eq_function_of_destFunction? hrest]
            rfl
          · contradiction
        · contradiction
      · contradiction
    · contradiction
  · rintro ⟨rfl, rfl⟩
    have hconstant : Const.same Const.equality Const.equality = true :=
      (Const.same_eq_true_iff _ _).mpr rfl
    simp [equalityOperand?, hconstant, Ty.equality, Ty.isBool_eq_true_iff]

theorem equalityOperand?_equality (operand : Ty) :
    equalityOperand? Const.equality (Ty.equality operand) = some operand :=
  (equalityOperand?_eq_some_iff _ _ _).mpr ⟨rfl, rfl⟩

/-- The de Bruijn index of a typed target variable. -/
def deBruijnIndex {B : Type} : {Γ : HOL.Ctx B} → {τ : HOL.Ty B} → HOL.Var Γ τ → Nat
  | _, _, .vz => 0
  | _, _, .vs x => deBruijnIndex x + 1

theorem deBruijnIndex_injective {B : Type} :
    ∀ {Γ : HOL.Ctx B} {τ τ' : HOL.Ty B} (x : HOL.Var Γ τ) (y : HOL.Var Γ τ'),
      deBruijnIndex x = deBruijnIndex y → τ = τ' ∧ HEq x y
  | _, _, _, .vz, .vz, _ => ⟨rfl, HEq.rfl⟩
  | _, _, _, .vz, .vs _, h => by simp [deBruijnIndex] at h
  | _, _, _, .vs _, .vz, h => by simp [deBruijnIndex] at h
  | _, _, _, .vs x, .vs y, h => by
      simp only [deBruijnIndex, Nat.add_right_cancel_iff] at h
      obtain ⟨rfl, hxy⟩ := deBruijnIndex_injective x y h
      cases hxy
      exact ⟨rfl, HEq.rfl⟩

/-- The target variable at an OpenTheory binder position. -/
theorem exists_var_of_getElem? :
    ∀ {context : List Ty} {index : Nat} {ty : Ty}, context[index]? = some ty →
      ∃ x : HOL.Var (context.map Ty.toHOL) ty.toHOL, deBruijnIndex x = index
  | [], _, _, h => by simp at h
  | head :: tail, 0, ty, h => by
      simp only [List.getElem?_cons_zero, Option.some.injEq] at h
      subst h
      exact ⟨.vz, rfl⟩
  | head :: tail, index + 1, ty, h => by
      simp only [List.getElem?_cons_succ] at h
      obtain ⟨x, hx⟩ := exists_var_of_getElem? h
      exact ⟨.vs x, by simp [deBruijnIndex, hx]⟩

theorem getElem?_of_var :
    ∀ {Γ : HOL.Ctx AtomicTy} {τ : HOL.Ty AtomicTy} (x : HOL.Var Γ τ)
      {context : List Ty}, context.map Ty.toHOL = Γ →
        ∃ ty, context[deBruijnIndex x]? = some ty ∧ ty.toHOL = τ
  | _, _, .vz, [], h => by simp at h
  | _, _, .vz, head :: tail, h => by
      simp only [List.map_cons, List.cons.injEq] at h
      exact ⟨head, rfl, h.1⟩
  | _, _, .vs x, [], h => by simp at h
  | _, _, .vs x, head :: tail, h => by
      simp only [List.map_cons, List.cons.injEq] at h
      obtain ⟨ty, hty, htoHOL⟩ := getElem?_of_var x h.2
      exact ⟨ty, by simpa [deBruijnIndex] using hty, htoHOL⟩

/-- Eta-expanded primitive equality `λ x y. x = y` at one operand type. -/
def equalityLambda {Γ : HOL.Ctx AtomicTy} (σ : HOL.Ty AtomicTy) :
    HOL.Term Symbol Γ (.arr σ (.arr σ .prop)) :=
  .lam (.lam (.eq (.var (.vs .vz)) (.var .vz)))

/-! ## Typing of canonical terms -/

namespace DBTerm

theorem inferType_app_eq_some_iff {context : List Ty} {function argument : DBTerm}
    {ty : Ty} :
    (DBTerm.app function argument).inferType context = some ty ↔
      ∃ domain, function.inferType context = some (.function domain ty) ∧
        argument.inferType context = some domain := by
  constructor
  · intro h
    simp only [DBTerm.inferType.eq_4, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨functionTy, hfunction, argumentTy, hargument, ⟨domain, codomain⟩,
      hdest, hresult⟩ := h
    split at hresult
    · rename_i hsame
      cases hresult
      have hdomain := (Ty.same_eq_true_iff _ _).mp hsame
      subst hdomain
      rw [Ty.eq_function_of_destFunction? hdest] at hfunction
      exact ⟨domain, hfunction, hargument⟩
    · contradiction
  · rintro ⟨domain, hfunction, hargument⟩
    simp only [DBTerm.inferType.eq_4, Option.bind_eq_bind, Option.bind_eq_some_iff]
    refine ⟨_, hfunction, _, hargument, (domain, ty), Ty.destFunction?_function _ _, ?_⟩
    simp [(Ty.same_eq_true_iff domain domain).mpr rfl]

theorem inferType_abs_eq_some_iff {context : List Ty} {domain : Ty} {body : DBTerm}
    {ty : Ty} :
    (DBTerm.abs domain body).inferType context = some ty ↔
      ∃ codomain, body.inferType (domain :: context) = some codomain ∧
        ty = .function domain codomain := by
  simp only [DBTerm.inferType.eq_5]
  cases body.inferType (domain :: context) with
  | none => simp
  | some codomain =>
      simp only [Option.pure_def, Option.bind_eq_bind, Option.bind_some,
        Option.some.injEq]
      constructor
      · intro h
        exact ⟨codomain, rfl, h.symm⟩
      · rintro ⟨codomain', hcodomain, rfl⟩
        cases hcodomain
        rfl

/-- Every loose bound index is below the given binder depth. -/
def LooseBelow : Nat → DBTerm → Prop
  | depth, .bound index => index < depth
  | depth, .app function argument =>
      LooseBelow depth function ∧ LooseBelow depth argument
  | depth, .abs _ body => LooseBelow (depth + 1) body
  | _, .const _ _ => True
  | _, .free _ => True

theorem looseBelow_of_inferType :
    ∀ {context : List Ty} {term : DBTerm} {ty : Ty},
      term.inferType context = some ty → term.LooseBelow context.length
  | _, .const _ _, _, _ => trivial
  | _, .free _, _, _ => trivial
  | context, .bound index, ty, h => by
      simp only [DBTerm.inferType.eq_3] at h
      exact (List.getElem?_eq_some_iff.mp h).1
  | _, .app function argument, _, h => by
      obtain ⟨domain, hfunction, hargument⟩ := inferType_app_eq_some_iff.mp h
      exact ⟨looseBelow_of_inferType hfunction, looseBelow_of_inferType hargument⟩
  | _, .abs domain body, _, h => by
      obtain ⟨codomain, hbody, _⟩ := inferType_abs_eq_some_iff.mp h
      exact looseBelow_of_inferType (term := body) hbody

end DBTerm

/-! ## Compositional translation

The compositional translation interprets every occurrence of primitive
equality at an exact equality type by its eta-expansion `λ x y. x = y`; all
other constants and all free variables become constant symbols, and bound
variables become typed de Bruijn variables.  It is a relation whose type
premises are equations, so substitution lemmas need no transport of terms.
-/

inductive TranslatesCompositionally :
    (Γ : HOL.Ctx AtomicTy) → DBTerm → (τ : HOL.Ty AtomicTy) →
      HOL.Term Symbol Γ τ → Prop
  | equality {Γ : HOL.Ctx AtomicTy} {constant : Const} {annotation operand : Ty}
      {σ : HOL.Ty AtomicTy}
      (recognized : equalityOperand? constant annotation = some operand)
      (typed : operand.toHOL = σ) :
      TranslatesCompositionally Γ (.const constant annotation)
        (.arr σ (.arr σ .prop)) (equalityLambda σ)
  | constant {Γ : HOL.Ctx AtomicTy} {constant : Const} {annotation : Ty}
      {τ : HOL.Ty AtomicTy}
      (unrecognized : equalityOperand? constant annotation = none)
      (typed : annotation.toHOL = τ) :
      TranslatesCompositionally Γ (.const constant annotation) τ
        (.const (.constant constant annotation typed))
  | free {Γ : HOL.Ctx AtomicTy} {sourceVar : SourceVar} {τ : HOL.Ty AtomicTy}
      (typed : sourceVar.ty.toHOL = τ) :
      TranslatesCompositionally Γ (.free sourceVar) τ
        (.const (.variable sourceVar typed))
  | bound {Γ : HOL.Ctx AtomicTy} {τ : HOL.Ty AtomicTy} (x : HOL.Var Γ τ) :
      TranslatesCompositionally Γ (.bound (deBruijnIndex x)) τ (.var x)
  | app {Γ : HOL.Ctx AtomicTy} {function argument : DBTerm}
      {σ τ : HOL.Ty AtomicTy} {function' : HOL.Term Symbol Γ (.arr σ τ)}
      {argument' : HOL.Term Symbol Γ σ} :
      TranslatesCompositionally Γ function (.arr σ τ) function' →
      TranslatesCompositionally Γ argument σ argument' →
      TranslatesCompositionally Γ (.app function argument) τ
        (.app function' argument')
  | abs {Γ : HOL.Ctx AtomicTy} {domain : Ty} {body : DBTerm}
      {σ τ : HOL.Ty AtomicTy} {body' : HOL.Term Symbol (σ :: Γ) τ}
      (typed : domain.toHOL = σ) :
      TranslatesCompositionally (σ :: Γ) body τ body' →
      TranslatesCompositionally Γ (.abs domain body) (.arr σ τ) (.lam body')

namespace TranslatesCompositionally

/-- The compositional translation is a partial function. -/
theorem unique {Γ : HOL.Ctx AtomicTy} {term : DBTerm} {τ : HOL.Ty AtomicTy}
    {target : HOL.Term Symbol Γ τ}
    (translation : TranslatesCompositionally Γ term τ target) :
    ∀ {τ' : HOL.Ty AtomicTy} {target' : HOL.Term Symbol Γ τ'},
      TranslatesCompositionally Γ term τ' target' → τ = τ' ∧ HEq target target' := by
  induction translation with
  | equality recognized typed =>
      intro τ' target' other
      cases other with
      | equality recognized' typed' =>
          rw [recognized] at recognized'
          cases recognized'
          subst typed typed'
          exact ⟨rfl, HEq.rfl⟩
      | constant unrecognized' _ =>
          rw [recognized] at unrecognized'
          cases unrecognized'
  | constant unrecognized typed =>
      intro τ' target' other
      cases other with
      | equality recognized' _ =>
          rw [unrecognized] at recognized'
          cases recognized'
      | constant _ typed' =>
          subst typed typed'
          exact ⟨rfl, HEq.rfl⟩
  | free typed =>
      intro τ' target' other
      cases other with
      | free typed' =>
          subst typed typed'
          exact ⟨rfl, HEq.rfl⟩
  | bound x =>
      intro τ' target' other
      generalize hindex : deBruijnIndex x = index at other
      cases other with
      | bound y =>
          obtain ⟨rfl, hxy⟩ := deBruijnIndex_injective x y hindex
          cases hxy
          exact ⟨rfl, HEq.rfl⟩
  | app _ _ functionIH argumentIH =>
      intro τ' target' other
      cases other with
      | app function' argument' =>
          obtain ⟨hfunctionTy, hfunction⟩ := functionIH function'
          cases hfunctionTy
          cases hfunction
          obtain ⟨-, hargument⟩ := argumentIH argument'
          cases hargument
          exact ⟨rfl, HEq.rfl⟩
  | abs typed _ bodyIH =>
      intro τ' target' other
      cases other with
      | abs typed' body' =>
          subst typed typed'
          obtain ⟨rfl, hbody⟩ := bodyIH body'
          cases hbody
          exact ⟨rfl, HEq.rfl⟩

theorem unique_eq {Γ : HOL.Ctx AtomicTy} {term : DBTerm} {τ : HOL.Ty AtomicTy}
    {target target' : HOL.Term Symbol Γ τ}
    (translation : TranslatesCompositionally Γ term τ target)
    (translation' : TranslatesCompositionally Γ term τ target') :
    target = target' :=
  eq_of_heq (translation.unique translation').2

/-- Every well-typed canonical term has a compositional translation at its
translated type. -/
theorem exists_of_inferType :
    ∀ {context : List Ty} {term : DBTerm} {ty : Ty},
      term.inferType context = some ty →
        ∃ target, TranslatesCompositionally (context.map Ty.toHOL) term ty.toHOL target
  | _, .const head annotation, ty, h => by
      simp only [DBTerm.inferType.eq_1, Option.some.injEq] at h
      subst h
      cases hrecognized : equalityOperand? head annotation with
      | some operand =>
          have hannotation :=
            ((equalityOperand?_eq_some_iff _ _ _).mp hrecognized).2
          rw [hannotation, Ty.toHOL_equality]
          exact ⟨_, .equality (hannotation ▸ hrecognized) rfl⟩
      | none => exact ⟨_, .constant hrecognized rfl⟩
  | _, .free sourceVar, ty, h => by
      simp only [DBTerm.inferType.eq_2, Option.some.injEq] at h
      subst h
      exact ⟨_, .free rfl⟩
  | _, .bound index, ty, h => by
      simp only [DBTerm.inferType.eq_3] at h
      obtain ⟨x, rfl⟩ := exists_var_of_getElem? h
      exact ⟨_, .bound x⟩
  | _, .app function argument, ty, h => by
      obtain ⟨domain, hfunction, hargument⟩ :=
        DBTerm.inferType_app_eq_some_iff.mp h
      have hfunctionExists := exists_of_inferType hfunction
      rw [Ty.toHOL_function] at hfunctionExists
      obtain ⟨function', hfunction'⟩ := hfunctionExists
      obtain ⟨argument', hargument'⟩ := exists_of_inferType hargument
      exact ⟨_, .app hfunction' hargument'⟩
  | context, .abs domain body, ty, h => by
      obtain ⟨codomain, hbody, rfl⟩ := DBTerm.inferType_abs_eq_some_iff.mp h
      obtain ⟨body', hbody'⟩ := exists_of_inferType hbody
      rw [Ty.toHOL_function]
      exact ⟨_, .abs rfl hbody'⟩

/-- A translated term is well typed, at the type whose translation is the
target type. -/
theorem inferType_eq {Γ : HOL.Ctx AtomicTy} {term : DBTerm} {τ : HOL.Ty AtomicTy}
    {target : HOL.Term Symbol Γ τ}
    (translation : TranslatesCompositionally Γ term τ target) :
    ∀ {context : List Ty}, context.map Ty.toHOL = Γ →
      ∃ ty, term.inferType context = some ty ∧ ty.toHOL = τ := by
  induction translation with
  | @equality Γ head annotation operand σ recognized typed =>
      intro context _
      obtain ⟨rfl, rfl⟩ := (equalityOperand?_eq_some_iff _ _ _).mp recognized
      exact ⟨Ty.equality operand, by simp, by rw [Ty.toHOL_equality, typed]⟩
  | constant _ typed =>
      intro context _
      exact ⟨_, by simp, typed⟩
  | free typed =>
      intro context _
      exact ⟨_, by simp, typed⟩
  | bound x =>
      intro context hcontext
      obtain ⟨ty, hty, htoHOL⟩ := getElem?_of_var x hcontext
      exact ⟨ty, by simpa using hty, htoHOL⟩
  | app _ _ functionIH argumentIH =>
      intro context hcontext
      obtain ⟨functionTy, hfunction, hfunctionTy⟩ := functionIH hcontext
      obtain ⟨argumentTy, hargument, hargumentTy⟩ := argumentIH hcontext
      obtain ⟨domain, codomain, rfl, hdomain, hcodomain⟩ :=
        Ty.toHOL_eq_arr_iff.mp hfunctionTy
      have : domain = argumentTy := Ty.toHOL_injective (hdomain.trans hargumentTy.symm)
      subst this
      exact ⟨codomain, DBTerm.inferType_app_eq_some_iff.mpr ⟨_, hfunction, hargument⟩,
        hcodomain⟩
  | @abs Γ domain body σ τ body' typed _ bodyIH =>
      intro context hcontext
      obtain ⟨codomain, hbody, hcodomain⟩ :=
        bodyIH (context := domain :: context) (by simp [hcontext, typed])
      exact ⟨.function domain codomain,
        DBTerm.inferType_abs_eq_some_iff.mpr ⟨codomain, hbody, rfl⟩,
        by rw [Ty.toHOL_function, typed, hcodomain]⟩

/-- Exactly the well-typed terms translate. -/
theorem exists_iff_inferType_isSome (context : List Ty) (term : DBTerm) :
    (∃ τ target, TranslatesCompositionally (context.map Ty.toHOL) term τ target) ↔
      (term.inferType context).isSome = true := by
  constructor
  · rintro ⟨τ, target, translation⟩
    obtain ⟨ty, hty, _⟩ := translation.inferType_eq rfl
    simp [hty]
  · intro h
    obtain ⟨ty, hty⟩ := Option.isSome_iff_exists.mp h
    obtain ⟨target, htarget⟩ := exists_of_inferType hty
    exact ⟨_, target, htarget⟩

theorem looseBelow {Γ : HOL.Ctx AtomicTy} {term : DBTerm} {τ : HOL.Ty AtomicTy}
    {target : HOL.Term Symbol Γ τ}
    (translation : TranslatesCompositionally Γ term τ target) :
    term.LooseBelow Γ.length := by
  induction translation with
  | equality => trivial
  | constant => trivial
  | free => trivial
  | bound x =>
      show deBruijnIndex x < _
      clear * -
      induction x with
      | vz => simp [deBruijnIndex]
      | vs x ih => simpa [deBruijnIndex] using ih
  | app _ _ functionIH argumentIH => exact ⟨functionIH, argumentIH⟩
  | abs _ _ bodyIH => exact bodyIH

/-- Renaming the target context along a map that preserves every loose de
Bruijn index of the source term preserves the translation. -/
theorem rename {Γ : HOL.Ctx AtomicTy} {term : DBTerm} {τ : HOL.Ty AtomicTy}
    {target : HOL.Term Symbol Γ τ}
    (translation : TranslatesCompositionally Γ term τ target) :
    ∀ {depth : Nat} {Γ' : HOL.Ctx AtomicTy} (ρ : HOL.Rename AtomicTy Γ Γ'),
      term.LooseBelow depth →
      (∀ {σ : HOL.Ty AtomicTy} (x : HOL.Var Γ σ), deBruijnIndex x < depth →
        deBruijnIndex (ρ x) = deBruijnIndex x) →
      TranslatesCompositionally Γ' term τ (HOL.rename ρ target) := by
  induction translation with
  | equality recognized typed =>
      intro depth Γ' ρ _ _
      exact .equality recognized typed
  | constant unrecognized typed =>
      intro depth Γ' ρ _ _
      exact .constant unrecognized typed
  | free typed =>
      intro depth Γ' ρ _ _
      exact .free typed
  | bound x =>
      intro depth Γ' ρ hloose hρ
      have hindex := hρ x hloose
      rw [← hindex]
      exact .bound (ρ x)
  | app _ _ functionIH argumentIH =>
      intro depth Γ' ρ hloose hρ
      exact .app (functionIH ρ hloose.1 hρ) (argumentIH ρ hloose.2 hρ)
  | abs typed _ bodyIH =>
      intro depth Γ' ρ hloose hρ
      refine .abs typed (bodyIH (depth := depth + 1) (HOL.Rename.lift ρ) hloose ?_)
      intro σ x hx
      cases x with
      | vz => rfl
      | vs x =>
          simp only [HOL.Rename.lift, deBruijnIndex]
          rw [hρ x (by simp only [deBruijnIndex] at hx; omega)]

/-- A closed translation is available in every context, by weakening. -/
theorem weakenCtx {term : DBTerm} {τ : HOL.Ty AtomicTy}
    {target : HOL.ClosedTerm Symbol τ}
    (translation : TranslatesCompositionally [] term τ target)
    (Γ : HOL.Ctx AtomicTy) :
    TranslatesCompositionally Γ term τ (HOL.weakenCtx Γ target) := by
  have renamed := translation.rename (depth := 0)
    (fun x => nomatch x : HOL.Rename AtomicTy [] Γ) translation.looseBelow
    (fun x => nomatch x)
  rwa [show HOL.rename (fun x => nomatch x : HOL.Rename AtomicTy [] Γ) target =
      HOL.weakenCtx Γ target from HOL.rename_weakenCtx _ target] at renamed

/-- Translations of terms without loose bound variables commute with arbitrary
target renaming. -/
theorem rename_of_closed {Γ : HOL.Ctx AtomicTy} {term : DBTerm}
    {τ : HOL.Ty AtomicTy} {target : HOL.Term Symbol Γ τ}
    (translation : TranslatesCompositionally Γ term τ target)
    (closed : term.LooseBelow 0) {Γ' : HOL.Ctx AtomicTy}
    (ρ : HOL.Rename AtomicTy Γ Γ') :
    TranslatesCompositionally Γ' term τ (HOL.rename ρ target) :=
  translation.rename ρ closed (fun _ h => absurd h (Nat.not_lt_zero _))

end TranslatesCompositionally

/-! ## Symbol discrimination and constant abstraction -/

namespace Symbol

/-- The free OpenTheory variable named by a symbol, if any. -/
def sourceVar? : {τ : HOL.Ty AtomicTy} → Symbol τ → Option SourceVar
  | _, .constant .. => none
  | _, .variable sourceVar _ => some sourceVar

theorem sigma_constant_ne_ofVar (constant : Const) (annotation : Ty)
    {τ : HOL.Ty AtomicTy} (typed : annotation.toHOL = τ) (sourceVar : SourceVar) :
    (⟨τ, .constant constant annotation typed⟩ : Sigma Symbol) ≠
      ⟨_, Symbol.ofVar sourceVar⟩ := by
  intro h
  have := congrArg (fun symbol : Sigma Symbol => symbol.2.sourceVar?) h
  simp [sourceVar?] at this

theorem sigma_variable_ne_ofVar {other : SourceVar} {τ : HOL.Ty AtomicTy}
    (typed : other.ty.toHOL = τ) {sourceVar : SourceVar} (different : other ≠ sourceVar) :
    (⟨τ, .variable other typed⟩ : Sigma Symbol) ≠ ⟨_, Symbol.ofVar sourceVar⟩ := by
  intro h
  have := congrArg (fun symbol : Sigma Symbol => symbol.2.sourceVar?) h
  simp [sourceVar?] at this
  exact different this

theorem noConstOccurrence_const {Γ : HOL.Ctx AtomicTy} {τ σ : HOL.Ty AtomicTy}
    (symbol : Symbol τ) (target : Symbol σ)
    (different : (⟨τ, symbol⟩ : Sigma Symbol) ≠ ⟨σ, target⟩) :
    HOL.NoConstOccurrence target (.const symbol : HOL.Term Symbol Γ τ) := by
  by_cases htype : σ = τ
  · subst htype
    exact .const_same_ne symbol (fun h => different (by rw [h]))
  · exact .const_diff_type htype symbol

end Symbol

theorem deBruijnIndex_varAtDepth {B : Type} {Γ : HOL.Ctx B} {σ : HOL.Ty B} :
    ∀ Ξ : HOL.Ctx B, deBruijnIndex (HOL.varAtDepth (Γ := Γ) (σ := σ) Ξ) = Ξ.length
  | [] => rfl
  | _ :: Ξ => by
      simp only [HOL.varAtDepth, deBruijnIndex, List.length_cons]
      rw [deBruijnIndex_varAtDepth Ξ]

theorem deBruijnIndex_insertRen {B : Type} {σ : HOL.Ty B} :
    ∀ (Ξ : HOL.Ctx B) {τ : HOL.Ty B} (x : HOL.Var (Ξ ++ []) τ),
      deBruijnIndex (HOL.insertRen (Γ := []) (σ := σ) Ξ x) = deBruijnIndex x
  | [], _, x => nomatch x
  | _ :: _, _, .vz => rfl
  | _ :: Ξ, _, .vs x => by
      simp only [HOL.insertRen, HOL.Rename.lift, deBruijnIndex]
      rw [deBruijnIndex_insertRen Ξ x]

theorem deBruijnIndex_mapTypes {B B' : Type} (θ : B → HOL.Ty B') :
    ∀ {Γ : HOL.Ctx B} {τ : HOL.Ty B} (x : HOL.Var Γ τ),
      deBruijnIndex (x.mapTypes θ) = deBruijnIndex x
  | _, _, .vz => rfl
  | _, _, .vs x => by
      simp only [HOL.Var.mapTypes, deBruijnIndex]
      rw [deBruijnIndex_mapTypes θ x]

theorem abstractConstAt_equalityLambda {τ : HOL.Ty AtomicTy} (symbol : Symbol τ)
    (Ξ : HOL.Ctx AtomicTy) (σ : HOL.Ty AtomicTy) :
    HOL.abstractConstAt (Γ := []) symbol Ξ (equalityLambda σ) = equalityLambda σ := by
  unfold equalityLambda
  rw [HOL.ExtDerivation.abstractConstAt_lam, HOL.ExtDerivation.abstractConstAt_lam,
    HOL.ExtDerivation.abstractConstAt_eq, HOL.ExtDerivation.abstractConstAt_var,
    HOL.ExtDerivation.abstractConstAt_var]
  rfl

theorem abstractConstAt_const_of_ne {Γ : HOL.Ctx AtomicTy} {σ τ : HOL.Ty AtomicTy}
    (target : Symbol σ) (Ξ : HOL.Ctx AtomicTy) (symbol : Symbol τ)
    (different : (⟨τ, symbol⟩ : Sigma Symbol) ≠ ⟨σ, target⟩) :
    HOL.abstractConstAt (Γ := Γ) target Ξ (.const symbol) = .const symbol := by
  rw [HOL.abstractConstAt, dif_neg different]

theorem abstractConstAt_const_self {Γ : HOL.Ctx AtomicTy} {σ : HOL.Ty AtomicTy}
    (target : Symbol σ) (Ξ : HOL.Ctx AtomicTy) :
    HOL.abstractConstAt (Γ := Γ) target Ξ (.const target) =
      .var (HOL.varAtDepth Ξ) := by
  rw [HOL.abstractConstAt, dif_pos rfl]
  rfl

namespace TranslatesCompositionally

/-- Closing a free variable into a binder corresponds to abstracting its
constant symbol. -/
theorem closeFreeAt (sourceVar : SourceVar) :
    ∀ {Ξ : HOL.Ctx AtomicTy} {term : DBTerm} {τ : HOL.Ty AtomicTy}
      {target : HOL.Term Symbol (Ξ ++ []) τ},
      TranslatesCompositionally (Ξ ++ []) term τ target →
      TranslatesCompositionally (Ξ ++ [sourceVar.ty.toHOL])
        (DBTerm.closeFreeAt sourceVar Ξ.length term) τ
        (HOL.abstractConstAt (Symbol.ofVar sourceVar) Ξ target) := by
  intro Ξ term
  induction term generalizing Ξ with
  | const head annotation =>
      intro τ target translation
      cases translation with
      | equality recognized typed =>
          simp only [DBTerm.closeFreeAt]
          rw [abstractConstAt_equalityLambda]
          exact .equality recognized typed
      | constant unrecognized typed =>
          simp only [DBTerm.closeFreeAt]
          rw [abstractConstAt_const_of_ne _ _ _
            (Symbol.sigma_constant_ne_ofVar _ _ _ _)]
          exact .constant unrecognized typed
  | free other =>
      intro τ target translation
      cases translation with
      | free typed =>
          by_cases same : other = sourceVar
          · subst same
            subst typed
            simp only [DBTerm.closeFreeAt_exact]
            rw [abstractConstAt_const_self]
            have := TranslatesCompositionally.bound
              (Γ := Ξ ++ [other.ty.toHOL]) (HOL.varAtDepth (Γ := []) Ξ)
            rwa [deBruijnIndex_varAtDepth] at this
          · rw [DBTerm.closeFreeAt_other _ _ _ (Ne.symm same),
              abstractConstAt_const_of_ne _ _ _
                (Symbol.sigma_variable_ne_ofVar typed same)]
            exact .free typed
  | bound index =>
      intro τ target translation
      generalize hindex : DBTerm.bound index = term at translation
      cases translation with
      | bound x =>
          cases hindex
          simp only [DBTerm.closeFreeAt]
          rw [HOL.ExtDerivation.abstractConstAt_var]
          have := TranslatesCompositionally.bound
            (HOL.insertRen (Γ := []) (σ := sourceVar.ty.toHOL) Ξ x)
          rwa [deBruijnIndex_insertRen] at this
      | _ => cases hindex
  | app function argument functionIH argumentIH =>
      intro τ target translation
      cases translation with
      | app hfunction hargument =>
          simp only [DBTerm.closeFreeAt]
          rw [HOL.ExtDerivation.abstractConstAt_app]
          exact .app (functionIH hfunction) (argumentIH hargument)
  | abs domain body bodyIH =>
      intro τ target translation
      cases translation with
      | @abs _ _ _ σ τ body' typed hbody =>
          simp only [DBTerm.closeFreeAt]
          rw [HOL.ExtDerivation.abstractConstAt_lam]
          exact .abs typed (bodyIH (Ξ := σ :: Ξ) hbody)

/-- If a variable does not occur freely, its symbol does not occur in the
translation. -/
theorem noConstOccurrence {Γ : HOL.Ctx AtomicTy} {term : DBTerm}
    {τ : HOL.Ty AtomicTy} {target : HOL.Term Symbol Γ τ}
    (translation : TranslatesCompositionally Γ term τ target)
    (sourceVar : SourceVar) (absent : ¬ DBTerm.FreeOccurrence sourceVar term) :
    HOL.NoConstOccurrence (Symbol.ofVar sourceVar) target := by
  induction translation with
  | equality => exact .lam (.lam (.eq .var .var))
  | constant _ typed =>
      exact Symbol.noConstOccurrence_const _ _
        (Symbol.sigma_constant_ne_ofVar _ _ typed _)
  | @free _ other _ typed =>
      have different : other ≠ sourceVar := by
        rintro rfl
        exact absent .here
      exact Symbol.noConstOccurrence_const _ _
        (Symbol.sigma_variable_ne_ofVar typed different)
  | bound => exact .var
  | app _ _ functionIH argumentIH =>
      exact .app (functionIH fun found => absent (.appFunction found))
        (argumentIH fun found => absent (.appArgument found))
  | abs _ _ bodyIH =>
      exact .lam (bodyIH fun found => absent (.absBody found))

/-- Binder instantiation at the split point. -/
theorem substAt_var {σ : HOL.Ty AtomicTy} {argument : DBTerm}
    {argument' : HOL.ClosedTerm Symbol σ}
    (argumentTranslation : TranslatesCompositionally [] argument σ argument') :
    ∀ (Ξ : HOL.Ctx AtomicTy) {τ : HOL.Ty AtomicTy} (x : HOL.Var ((Ξ ++ [σ]) ++ []) τ),
      (deBruijnIndex x = Ξ.length ∧
        TranslatesCompositionally ((Ξ ++ []) ++ []) argument τ
          (HOL.substAt (Γ := []) Ξ [] argument' x)) ∨
      (deBruijnIndex x < Ξ.length ∧
        ∃ y : HOL.Var ((Ξ ++ []) ++ []) τ,
          HOL.substAt (Γ := []) Ξ [] argument' x = .var y ∧
            deBruijnIndex y = deBruijnIndex x)
  | [], _, .vz => Or.inl ⟨rfl, argumentTranslation⟩
  | [], _, .vs x => nomatch x
  | _ :: _, _, .vz => Or.inr ⟨by simp [deBruijnIndex], .vz, rfl, rfl⟩
  | _ :: Ξ, _, .vs x => by
      rcases substAt_var argumentTranslation Ξ x with ⟨hindex, htranslation⟩ |
          ⟨hindex, y, hy, hyindex⟩
      · refine Or.inl ⟨by simp [deBruijnIndex, hindex], ?_⟩
        exact htranslation.rename_of_closed argumentTranslation.looseBelow
          HOL.Rename.weaken
      · refine Or.inr ⟨by simp only [deBruijnIndex, List.length_cons]; omega,
          .vs y, ?_, by simp [deBruijnIndex, hyindex]⟩
        change HOL.rename HOL.Rename.weaken
          (HOL.substAt (Γ := []) Ξ [] argument' x) = _
        rw [hy]
        rfl

/-- OpenTheory binder instantiation corresponds to target substitution at the
same binder depth. -/
theorem instantiateAt {σ : HOL.Ty AtomicTy} {argument : DBTerm}
    {argument' : HOL.ClosedTerm Symbol σ}
    (argumentTranslation : TranslatesCompositionally [] argument σ argument') :
    ∀ {Ξ : HOL.Ctx AtomicTy} {body : DBTerm} {τ : HOL.Ty AtomicTy}
      {target : HOL.Term Symbol ((Ξ ++ [σ]) ++ []) τ},
      TranslatesCompositionally ((Ξ ++ [σ]) ++ []) body τ target →
      TranslatesCompositionally ((Ξ ++ []) ++ [])
        (DBTerm.instantiateAt argument Ξ.length body) τ
        (HOL.subst (HOL.substAt (Γ := []) Ξ [] argument') target) := by
  intro Ξ body
  induction body generalizing Ξ with
  | const head annotation =>
      intro τ target translation
      cases translation with
      | equality recognized typed =>
          simp only [DBTerm.instantiateAt]
          exact .equality recognized typed
      | constant unrecognized typed =>
          simp only [DBTerm.instantiateAt]
          exact .constant unrecognized typed
  | free other =>
      intro τ target translation
      cases translation with
      | free typed =>
          simp only [DBTerm.instantiateAt]
          exact .free typed
  | bound index =>
      intro τ target translation
      generalize hindex : DBTerm.bound index = term at translation
      cases translation with
      | bound x =>
          cases hindex
          rcases substAt_var argumentTranslation Ξ x with ⟨hx, htranslation⟩ |
              ⟨hx, y, hy, hyindex⟩
          · rw [hx, DBTerm.instantiateAt_target]
            exact htranslation
          · rw [DBTerm.instantiateAt_other _ _ _ (Nat.ne_of_lt hx)]
            change TranslatesCompositionally _ _ _
              (HOL.substAt (Γ := []) Ξ [] argument' x)
            rw [hy, ← hyindex]
            exact .bound y
      | _ => cases hindex
  | app function argument functionIH argumentIH =>
      intro τ target translation
      cases translation with
      | app hfunction hargument =>
          simp only [DBTerm.instantiateAt]
          exact .app (functionIH hfunction) (argumentIH hargument)
  | abs domain body bodyIH =>
      intro τ target translation
      cases translation with
      | @abs _ _ _ ρ τ body' typed hbody =>
          simp only [DBTerm.instantiateAt]
          exact .abs typed (bodyIH (Ξ := ρ :: Ξ) hbody)

end TranslatesCompositionally

/-! ## Substitution -/

namespace TypeSubst

/-- The action of an OpenTheory type substitution on target symbols. -/
def symbolInstance (substitution : TypeSubst) :
    {τ : HOL.Ty AtomicTy} → Symbol τ →
      Symbol (HOL.Ty.substitute substitution.baseInstance τ)
  | _, .constant constant annotation typed =>
      .constant constant (substitution.apply annotation)
        (by rw [← typed, substitute_toHOL])
  | _, .variable sourceVar typed =>
      .variable (substitution.applyVar sourceVar)
        (by rw [← typed, substitute_toHOL]; rfl)

end TypeSubst

/-- A closed translation selected from a proof that one exists.  By
`TranslatesCompositionally.unique`, it equals every other such translation. -/
noncomputable def closedTranslation (term : DBTerm) {τ : HOL.Ty AtomicTy}
    (translatable : ∃ target : HOL.ClosedTerm Symbol τ,
      TranslatesCompositionally [] term τ target) :
    HOL.ClosedTerm Symbol τ :=
  Classical.choose translatable

theorem closedTranslation_spec (term : DBTerm) {τ : HOL.Ty AtomicTy}
    (translatable : ∃ target : HOL.ClosedTerm Symbol τ,
      TranslatesCompositionally [] term τ target) :
    TranslatesCompositionally [] term τ (closedTranslation term translatable) :=
  Classical.choose_spec translatable

namespace TermSubst

/-- The canonical OpenTheory term a substitution puts in place of an already
type-substituted free variable. -/
def variableReplacement (substitution : TermSubst) (sourceVar : SourceVar) : DBTerm :=
  match substitution.lookup sourceVar with
  | some replacement => replacement.canonical.term
  | none => .free sourceVar

theorem variableReplacement_of_lookup_some {substitution : TermSubst}
    {sourceVar : SourceVar} {replacement : CheckedSourceTerm}
    (found : substitution.lookup sourceVar = some replacement) :
    substitution.variableReplacement sourceVar = replacement.canonical.term := by
  unfold variableReplacement
  rw [found]

theorem variableReplacement_of_lookup_none {substitution : TermSubst}
    {sourceVar : SourceVar} (missing : substitution.lookup sourceVar = none) :
    substitution.variableReplacement sourceVar = .free sourceVar := by
  unfold variableReplacement
  rw [missing]

theorem applyDB_free (substitution : TermSubst) (sourceVar : SourceVar) :
    substitution.applyDB (.free sourceVar) =
      substitution.variableReplacement (substitution.types.applyVar sourceVar) := by
  cases hlookup : substitution.lookup (substitution.types.applyVar sourceVar) with
  | some replacement =>
      rw [applyDB_free_of_lookup_some _ _ _ hlookup,
        variableReplacement_of_lookup_some hlookup]
  | none =>
      rw [applyDB_free_of_lookup_none _ _ hlookup,
        variableReplacement_of_lookup_none hlookup]

/-- The canonical OpenTheory term that a substitution puts in place of an
already type-substituted symbol. -/
def symbolReplacement (substitution : TermSubst) :
    {τ : HOL.Ty AtomicTy} → Symbol τ → DBTerm
  | _, .constant constant annotation _ => .const constant annotation
  | _, .variable sourceVar _ => substitution.variableReplacement sourceVar

theorem symbolReplacement_translatable {substitution : TermSubst}
    (correct : substitution.TypeCorrect) :
    ∀ {τ : HOL.Ty AtomicTy} (symbol : Symbol τ),
      ∃ target : HOL.ClosedTerm Symbol τ,
        TranslatesCompositionally [] (substitution.symbolReplacement symbol) τ target
  | _, .constant constant annotation typed => by
      subst typed
      exact TranslatesCompositionally.exists_of_inferType (context := [])
        (term := .const constant annotation) (by simp)
  | _, .variable sourceVar typed => by
      subst typed
      show ∃ target, TranslatesCompositionally []
        (substitution.variableReplacement sourceVar) _ target
      cases hlookup : substitution.lookup sourceVar with
      | some replacement =>
          rw [variableReplacement_of_lookup_some hlookup]
          have htype := typeCorrect_lookup correct hlookup
          have hchecked := replacement.canonical.checked
          change replacement.canonical.term.inferType [] = some replacement.ty at hchecked
          rw [htype] at hchecked
          exact TranslatesCompositionally.exists_of_inferType (context := []) hchecked
      | none =>
          rw [variableReplacement_of_lookup_none hlookup]
          exact TranslatesCompositionally.exists_of_inferType (context := [])
            (term := .free sourceVar) (by simp)

end TermSubst

namespace TypeCorrectTermSubstitution

/-- The closed target term replacing one type-substituted symbol. -/
noncomputable def symbolImage (substitution : TypeCorrectTermSubstitution)
    {τ : HOL.Ty AtomicTy} (symbol : Symbol τ) : HOL.ClosedTerm Symbol τ :=
  closedTranslation (substitution.raw.symbolReplacement symbol)
    (TermSubst.symbolReplacement_translatable substitution.typeCorrect symbol)

/-- The target image of an OpenTheory substitution: retype by its type
component, then replace symbols by the translations of the OpenTheory terms
the substitution puts in their place. -/
noncomputable def targetMap (substitution : TypeCorrectTermSubstitution)
    {Γ : HOL.Ctx AtomicTy} {τ : HOL.Ty AtomicTy} (term : HOL.Term Symbol Γ τ) :
    HOL.Term Symbol (Γ.map (HOL.Ty.substitute substitution.raw.types.baseInstance))
      (HOL.Ty.substitute substitution.raw.types.baseInstance τ) :=
  HOL.substConst substitution.symbolImage
    (HOL.mapTypes substitution.raw.types.baseInstance
      substitution.raw.types.symbolInstance term)

/-- Extensional derivations are preserved by the target image of an
OpenTheory substitution. -/
theorem extDerivation_targetMap (substitution : TypeCorrectTermSubstitution)
    {Δ : List (HOL.ClosedFormula Symbol)} {φ : HOL.ClosedFormula Symbol}
    (derivation : HOL.ExtDerivation Symbol Δ φ) :
    HOL.ExtDerivation Symbol (Δ.map substitution.targetMap)
      (substitution.targetMap φ) := by
  have retyped := HOL.ExtDerivation.mapTypes substitution.raw.types.baseInstance
    substitution.raw.types.symbolInstance derivation
  have replaced := HOL.ExtDerivation.substConst_derivation
    substitution.symbolImage retyped
  refine HOL.ExtDerivation.mono ?_ replaced
  intro χ hχ
  obtain ⟨ψ', hψ', rfl⟩ := List.mem_map.mp hχ
  obtain ⟨ψ, hψ, rfl⟩ := List.mem_map.mp hψ'
  exact List.mem_map.mpr ⟨ψ, hψ, rfl⟩

end TypeCorrectTermSubstitution

namespace TranslatesCompositionally

theorem of_term_eq {Γ : HOL.Ctx AtomicTy} {term term' : DBTerm} {τ : HOL.Ty AtomicTy}
    {target : HOL.Term Symbol Γ τ}
    (translation : TranslatesCompositionally Γ term τ target) (equal : term = term') :
    TranslatesCompositionally Γ term' τ target :=
  equal ▸ translation

/-- OpenTheory substitution corresponds to its target image. -/
theorem applyDB (substitution : TypeCorrectTermSubstitution)
    {Γ : HOL.Ctx AtomicTy} {term : DBTerm} {τ : HOL.Ty AtomicTy}
    {target : HOL.Term Symbol Γ τ}
    (translation : TranslatesCompositionally Γ term τ target) :
    TranslatesCompositionally
      (Γ.map (HOL.Ty.substitute substitution.raw.types.baseInstance))
      (substitution.raw.applyDB term)
      (HOL.Ty.substitute substitution.raw.types.baseInstance τ)
      (substitution.targetMap target) := by
  induction translation with
  | @equality Γ head annotation operand σ recognized typed =>
      obtain ⟨rfl, rfl⟩ := (equalityOperand?_eq_some_iff _ _ _).mp recognized
      rw [TermSubst.applyDB_const, TypeSubst.apply_equality]
      exact .equality (equalityOperand?_equality _)
        (by rw [← typed, TypeSubst.substitute_toHOL])
  | @constant Γ head annotation τ unrecognized typed =>
      rw [TermSubst.applyDB_const]
      have hselected := closedTranslation_spec
        (substitution.raw.symbolReplacement
          (substitution.raw.types.symbolInstance
            (Symbol.constant head annotation typed)))
        (TermSubst.symbolReplacement_translatable substitution.typeCorrect _)
      exact hselected.weakenCtx _
  | @free Γ sourceVar τ typed =>
      have hselected := closedTranslation_spec
        (substitution.raw.symbolReplacement
          (substitution.raw.types.symbolInstance (Symbol.variable sourceVar typed)))
        (TermSubst.symbolReplacement_translatable substitution.typeCorrect _)
      have hweak := hselected.weakenCtx
        (Γ.map (HOL.Ty.substitute substitution.raw.types.baseInstance))
      exact hweak.of_term_eq (TermSubst.applyDB_free _ _).symm
  | bound x =>
      have := TranslatesCompositionally.bound
        (x.mapTypes substitution.raw.types.baseInstance)
      rw [deBruijnIndex_mapTypes] at this
      rw [TermSubst.applyDB_bound]
      exact this
  | app _ _ functionIH argumentIH =>
      rw [TermSubst.applyDB_app]
      exact .app functionIH argumentIH
  | abs typed _ bodyIH =>
      rw [TermSubst.applyDB_abs]
      exact .abs (by rw [← typed, TypeSubst.substitute_toHOL]) bodyIH

/-- Translation of the primitive equality form. -/
theorem equalityDB {Γ : HOL.Ctx AtomicTy} {operand : Ty} {left right : DBTerm}
    {σ : HOL.Ty AtomicTy} {left' right' : HOL.Term Symbol Γ σ}
    (typed : operand.toHOL = σ)
    (leftTranslation : TranslatesCompositionally Γ left σ left')
    (rightTranslation : TranslatesCompositionally Γ right σ right') :
    TranslatesCompositionally Γ (CanonicalTerm.equalityDB operand left right) .prop
      (.app (.app (equalityLambda σ) left') right') :=
  .app (.app (.equality (equalityOperand?_equality operand) typed) leftTranslation)
    rightTranslation

/-- Inversion of the translation of the primitive equality form. -/
theorem equalityDB_inv {Γ : HOL.Ctx AtomicTy} {operand : Ty} {left right : DBTerm}
    {φ : HOL.Formula Symbol Γ}
    (translation : TranslatesCompositionally Γ
      (CanonicalTerm.equalityDB operand left right) .prop φ) :
    ∃ (σ : HOL.Ty AtomicTy) (left' right' : HOL.Term Symbol Γ σ),
      operand.toHOL = σ ∧ TranslatesCompositionally Γ left σ left' ∧
        TranslatesCompositionally Γ right σ right' ∧
          φ = .app (.app (equalityLambda σ) left') right' := by
  unfold CanonicalTerm.equalityDB at translation
  cases translation with
  | app hfunction hright =>
      cases hfunction with
      | app hhead hleft =>
          cases hhead with
          | @equality _ _ _ operand' σ' recognized typed =>
              obtain ⟨-, hannotation⟩ :=
                (equalityOperand?_eq_some_iff _ _ _).mp recognized
              have hoperand : operand = operand' := by
                have := congrArg Ty.toHOL hannotation
                simp only [Ty.toHOL_equality, HOL.Ty.arr.injEq] at this
                exact Ty.toHOL_injective this.1
              subst hoperand
              exact ⟨_, _, _, typed, hleft, hright, rfl⟩
          | constant unrecognized typed =>
              rw [equalityOperand?_equality] at unrecognized
              cases unrecognized

end TranslatesCompositionally

namespace CanonicalTerm

theorem exists_translation (term : CanonicalTerm) :
    ∃ target, TranslatesCompositionally [] term.term term.ty.toHOL target :=
  TranslatesCompositionally.exists_of_inferType (context := []) term.checked

theorem isBool_of_translation {term : CanonicalTerm} {φ : HOL.ClosedFormula Symbol}
    (translation : TranslatesCompositionally [] term.term .prop φ) : term.IsBool := by
  obtain ⟨ty, hty, htoHOL⟩ := translation.inferType_eq (context := []) rfl
  have : ty = term.ty := Option.some.inj (hty.symm.trans term.checked)
  subst this
  exact Ty.toHOL_eq_prop_iff.mp htoHOL

theorem exists_formula {term : CanonicalTerm} (hbool : term.IsBool) :
    ∃ φ : HOL.ClosedFormula Symbol, TranslatesCompositionally [] term.term .prop φ := by
  have hexists := term.exists_translation
  rw [show term.ty = Ty.bool from hbool, Ty.toHOL_bool] at hexists
  exact hexists

end CanonicalTerm

/-! ## Derivation helpers -/

section DerivationHelpers

variable {B : Type} {C : HOL.Ty B → Type}

/-- Cut for finite-context provability. -/
theorem provable_of_extDerivation {T : HOL.ClosedTheorySet C} :
    ∀ {premises : List (HOL.ClosedFormula C)} {φ : HOL.ClosedFormula C},
      HOL.ExtDerivation C premises φ →
      (∀ ψ ∈ premises, HOL.ClosedTheorySet.Provable T ψ) →
      HOL.ClosedTheorySet.Provable T φ
  | [], φ, derivation, _ => ⟨[], by simp, derivation⟩
  | ψ :: premises, φ, derivation, hpremises => by
      have himp := provable_of_extDerivation (.impI derivation)
        (fun χ hχ => hpremises χ (List.mem_cons_of_mem _ hχ))
      exact HOL.ClosedTheorySet.provable_mp himp (hpremises ψ List.mem_cons_self)

theorem provable_mono {T U : HOL.ClosedTheorySet C} (subset : T ⊆ U)
    {φ : HOL.ClosedFormula C} (provable : HOL.ClosedTheorySet.Provable T φ) :
    HOL.ClosedTheorySet.Provable U φ :=
  HOL.ClosedTheorySet.provable_mono (fun h => subset h) provable

end DerivationHelpers

/-- The eta-expanded equality applied to two arguments is provably their
equality. -/
theorem extDerivation_equalityLambda_app_app {Γ : HOL.Ctx AtomicTy}
    (Δ : List (HOL.Formula Symbol Γ)) {σ : HOL.Ty AtomicTy}
    (left right : HOL.Term Symbol Γ σ) :
    HOL.ExtDerivation Symbol Δ
      (.eq (.app (.app (equalityLambda σ) left) right) (.eq left right)) := by
  have first : HOL.ExtDerivation Symbol Δ
      (.eq (.app (equalityLambda σ) left)
        (.lam (.eq (HOL.weaken (σ := σ) left) (.var .vz)))) :=
    .beta left (.lam (.eq (.var (.vs .vz)) (.var .vz)))
  have second : HOL.ExtDerivation Symbol Δ
      (.eq (.app (.lam (.eq (HOL.weaken (σ := σ) left) (.var .vz))) right)
        (.eq left right)) := by
    have := HOL.ExtDerivation.beta (Δ := Δ) right
      (.eq (HOL.weaken (σ := σ) left) (.var .vz))
    change HOL.ExtDerivation Symbol Δ
      (.eq _ (.eq (HOL.instantiate right (HOL.weaken (σ := σ) left)) right)) at this
    rwa [HOL.instantiate_weaken] at this
  exact .eqTrans (.eqApp right first) second

theorem extDerivation_equalityLambda_iff {Γ : HOL.Ctx AtomicTy}
    {Δ : List (HOL.Formula Symbol Γ)} {σ : HOL.Ty AtomicTy}
    {left right : HOL.Term Symbol Γ σ} :
    HOL.ExtDerivation Symbol Δ (.app (.app (equalityLambda σ) left) right) ↔
      HOL.ExtDerivation Symbol Δ (.eq left right) :=
  ⟨fun derivation => HOL.ExtDerivation.eqProp_mp_left
      (extDerivation_equalityLambda_app_app Δ left right) derivation,
    fun derivation => HOL.ExtDerivation.eqProp_mp_right
      (extDerivation_equalityLambda_app_app Δ left right) derivation⟩

theorem provable_equalityLambda_iff {T : HOL.ClosedTheorySet Symbol}
    {σ : HOL.Ty AtomicTy} {left right : HOL.ClosedTerm Symbol σ} :
    HOL.ClosedTheorySet.Provable T (.app (.app (equalityLambda σ) left) right) ↔
      HOL.ClosedTheorySet.Provable T (.eq left right) := by
  constructor
  · rintro ⟨premises, hpremises, derivation⟩
    exact ⟨premises, hpremises, extDerivation_equalityLambda_iff.mp derivation⟩
  · rintro ⟨premises, hpremises, derivation⟩
    exact ⟨premises, hpremises, extDerivation_equalityLambda_iff.mpr derivation⟩

/-! ## Provability of compositionally translated sequents -/

/-- The compositional translations of the Boolean members of a hypothesis
set. -/
def compositionalHypotheses (hyp : Finset CanonicalTerm) : HOL.ClosedTheorySet Symbol :=
  {φ | ∃ term ∈ hyp, TranslatesCompositionally [] term.term .prop φ}

theorem compositionalHypotheses_mono {left right : Finset CanonicalTerm}
    (subset : left ⊆ right) :
    compositionalHypotheses left ⊆ compositionalHypotheses right := by
  rintro φ ⟨term, hterm, htranslation⟩
  exact ⟨term, subset hterm, htranslation⟩

/-- A sequent's compositionally translated conclusion is provable from the
background sentences `Θ` together with its translated hypotheses. -/
def CompositionallyProvable (Θ : HOL.ClosedTheorySet Symbol) (sequent : Sequent) : Prop :=
  ∃ φ, TranslatesCompositionally [] sequent.concl.term .prop φ ∧
    HOL.ClosedTheorySet.Provable (Θ ∪ compositionalHypotheses sequent.hyp) φ

/-- Background sentences suitable for OpenTheory axioms: they mention no
free-variable symbol, and they are closed under the target image of every
admitted OpenTheory substitution. -/
structure VariableFreeSubstitutionClosed (Θ : HOL.ClosedTheorySet Symbol) : Prop where
  variableFree :
    ∀ ψ ∈ Θ, ∀ sourceVar : SourceVar, HOL.NoConstOccurrence (Symbol.ofVar sourceVar) ψ
  substitutionClosed :
    ∀ (substitution : TypeCorrectTermSubstitution), ∀ ψ ∈ Θ,
      (substitution.targetMap ψ : HOL.ClosedFormula Symbol) ∈ Θ

theorem variableFreeSubstitutionClosed_empty :
    VariableFreeSubstitutionClosed (∅ : HOL.ClosedTheorySet Symbol) :=
  ⟨fun _ h => absurd h (Set.notMem_empty _), fun _ _ h => absurd h (Set.notMem_empty _)⟩

section RulePreservation

variable {Θ : HOL.ClosedTheorySet Symbol}

theorem provable_union_left {hyp hyp' : Finset CanonicalTerm} (subset : hyp ⊆ hyp')
    {φ : HOL.ClosedFormula Symbol}
    (provable : HOL.ClosedTheorySet.Provable (Θ ∪ compositionalHypotheses hyp) φ) :
    HOL.ClosedTheorySet.Provable (Θ ∪ compositionalHypotheses hyp') φ :=
  provable_mono (Set.union_subset_union_right Θ (compositionalHypotheses_mono subset))
    provable

theorem compositionallyProvable_assume {term : CanonicalTerm} (hbool : term.IsBool) :
    CompositionallyProvable Θ ⟨{term}, term⟩ := by
  obtain ⟨φ, hφ⟩ := CanonicalTerm.exists_formula hbool
  exact ⟨φ, hφ, HOL.ClosedTheorySet.provable_of_mem
    (Or.inr ⟨term, Finset.mem_singleton_self term, hφ⟩)⟩

theorem compositionallyProvable_refl {term equality : CanonicalTerm}
    (construction : CanonicalTerm.EqualityConstructionSemantics term term equality) :
    CompositionallyProvable Θ ⟨∅, equality⟩ := by
  obtain ⟨target, htarget⟩ := term.exists_translation
  refine ⟨_, by rw [construction.2]; exact .equalityDB rfl htarget htarget, ?_⟩
  exact provable_equalityLambda_iff.mpr ⟨[], by simp, .eqRefl target⟩

theorem compositionallyProvable_betaConv {redex reduced equality : CanonicalTerm}
    (reduction : CanonicalTerm.BetaReductionSemantics redex reduced)
    (construction : CanonicalTerm.EqualityConstructionSemantics redex reduced equality) :
    CompositionallyProvable Θ ⟨∅, equality⟩ := by
  obtain ⟨domain, body, argument, hredex, hreduced⟩ := reduction
  obtain ⟨target, htarget⟩ := redex.exists_translation
  have htarget' := htarget.of_term_eq hredex
  cases htarget' with
  | app hlambda hargument =>
      cases hlambda with
      | abs typed hbody =>
          have hinstance := TranslatesCompositionally.instantiateAt hargument
            (Ξ := []) hbody
          have hreducedTranslation := hinstance.of_term_eq hreduced.symm
          refine ⟨_, by
            rw [construction.2]
            exact .equalityDB rfl htarget hreducedTranslation, ?_⟩
          exact provable_equalityLambda_iff.mpr ⟨[], by simp, .beta _ _⟩

/-- The translated type of a checked term, read off from any translation. -/
theorem CanonicalTerm.toHOL_ty_of_translation {term : CanonicalTerm}
    {τ : HOL.Ty AtomicTy} {target : HOL.ClosedTerm Symbol τ}
    (translation : TranslatesCompositionally [] term.term τ target) :
    term.ty.toHOL = τ := by
  obtain ⟨ty, hty, htoHOL⟩ := translation.inferType_eq (context := []) rfl
  rw [← Option.some.inj (hty.symm.trans term.checked), htoHOL]

theorem compositionallyProvable_app {functionEquality argumentEquality : Theorem}
    {functionLeft functionRight argumentLeft argumentRight applicationLeft
      applicationRight equality : CanonicalTerm}
    (functionView : CanonicalTerm.EqualityViewSemantics
      functionEquality.sequent.concl functionLeft functionRight)
    (argumentView : CanonicalTerm.EqualityViewSemantics
      argumentEquality.sequent.concl argumentLeft argumentRight)
    (leftApplication : CanonicalTerm.ApplicationSemantics
      functionLeft argumentLeft applicationLeft)
    (rightApplication : CanonicalTerm.ApplicationSemantics
      functionRight argumentRight applicationRight)
    (construction : CanonicalTerm.EqualityConstructionSemantics
      applicationLeft applicationRight equality)
    (functionProvable : CompositionallyProvable Θ functionEquality.sequent)
    (argumentProvable : CompositionallyProvable Θ argumentEquality.sequent) :
    CompositionallyProvable Θ
      ⟨functionEquality.sequent.hyp ∪ argumentEquality.sequent.hyp, equality⟩ := by
  obtain ⟨φf, hφf, pf⟩ := functionProvable
  obtain ⟨σf, fl, fr, hσf, hfl, hfr, rfl⟩ :=
    (hφf.of_term_eq functionView.2).equalityDB_inv
  obtain ⟨φx, hφx, px⟩ := argumentProvable
  obtain ⟨σx, xl, xr, hσx, hxl, hxr, rfl⟩ :=
    (hφx.of_term_eq argumentView.2).equalityDB_inv
  obtain ⟨domain, codomain, hdest, hdomain, hleftTerm⟩ := leftApplication
  obtain ⟨domain', codomain', hdest', hdomain', hrightTerm⟩ := rightApplication
  have hfunctionTy := Ty.eq_function_of_destFunction? hdest
  have hfunctionTy' := Ty.eq_function_of_destFunction? hdest'
  rw [← functionView.1, hfunctionTy] at hfunctionTy'
  obtain ⟨rfl, rfl⟩ := Ty.function_inj hfunctionTy'
  have hσf' : σf = .arr domain.toHOL codomain.toHOL := by
    rw [← hσf, hfunctionTy, Ty.toHOL_function]
  subst hσf'
  have hσx' : σx = domain.toHOL := by rw [← hσx, hdomain]
  subst hσx'
  have hleft : TranslatesCompositionally [] applicationLeft.term codomain.toHOL
      (.app fl xl) := (TranslatesCompositionally.app hfl hxl).of_term_eq hleftTerm.symm
  have hright : TranslatesCompositionally [] applicationRight.term codomain.toHOL
      (.app fr xr) := (TranslatesCompositionally.app hfr hxr).of_term_eq hrightTerm.symm
  refine ⟨_, (TranslatesCompositionally.equalityDB
    (CanonicalTerm.toHOL_ty_of_translation hleft) hleft hright).of_term_eq
      construction.2.symm, ?_⟩
  apply provable_equalityLambda_iff.mpr
  refine provable_of_extDerivation (premises := [.eq fl fr, .eq xl xr])
    (HOL.ExtDerivation.eqAppCongr (.hyp (by simp)) (.hyp (by simp))) ?_
  intro ψ hψ
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hψ
  rcases hψ with rfl | rfl
  · exact provable_union_left Finset.subset_union_left (provable_equalityLambda_iff.mp pf)
  · exact provable_union_left Finset.subset_union_right (provable_equalityLambda_iff.mp px)

/-- Discharging one hypothesis: its translation becomes an antecedent. -/
theorem provable_imp_of_erase {hyp : Finset CanonicalTerm} {discharged : CanonicalTerm}
    {p q : HOL.ClosedFormula Symbol}
    (hp : TranslatesCompositionally [] discharged.term .prop p)
    (provable : HOL.ClosedTheorySet.Provable (Θ ∪ compositionalHypotheses hyp) q) :
    HOL.ClosedTheorySet.Provable
      (Θ ∪ compositionalHypotheses (hyp.erase discharged)) (.imp p q) := by
  classical
  obtain ⟨premises, hpremises, derivation⟩ := provable
  refine ⟨premises.filter (fun ψ => ψ ≠ p), ?_, .impI (HOL.ExtDerivation.mono ?_ derivation)⟩
  · intro ψ hψ
    obtain ⟨hmem, hne⟩ := List.mem_filter.mp hψ
    have hne : ψ ≠ p := by simpa using hne
    rcases hpremises ψ hmem with hΘ | ⟨term, hterm, htranslation⟩
    · exact Or.inl hΘ
    · refine Or.inr ⟨term, Finset.mem_erase.mpr ⟨?_, hterm⟩, htranslation⟩
      rintro rfl
      exact hne (htranslation.unique_eq hp)
  · intro χ hχ
    by_cases hχp : χ = p
    · subst hχp
      exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (List.mem_filter.mpr ⟨hχ, by simpa using hχp⟩)

theorem compositionallyProvable_deductAntisym {left right : Theorem}
    {equality : CanonicalTerm}
    (construction : CanonicalTerm.EqualityConstructionSemantics
      left.sequent.concl right.sequent.concl equality)
    (leftProvable : CompositionallyProvable Θ left.sequent)
    (rightProvable : CompositionallyProvable Θ right.sequent) :
    CompositionallyProvable Θ
      ⟨(left.sequent.hyp.erase right.sequent.concl) ∪
          (right.sequent.hyp.erase left.sequent.concl), equality⟩ := by
  obtain ⟨p, hp, pp⟩ := leftProvable
  obtain ⟨q, hq, pq⟩ := rightProvable
  refine ⟨_, (TranslatesCompositionally.equalityDB
    (CanonicalTerm.toHOL_ty_of_translation hp) hp hq).of_term_eq
      construction.2.symm, ?_⟩
  apply provable_equalityLambda_iff.mpr
  have forward : HOL.ClosedTheorySet.Provable
      (Θ ∪ compositionalHypotheses ((left.sequent.hyp.erase right.sequent.concl) ∪
        (right.sequent.hyp.erase left.sequent.concl))) (.imp p q) :=
    provable_union_left Finset.subset_union_right (provable_imp_of_erase hp pq)
  have backward : HOL.ClosedTheorySet.Provable
      (Θ ∪ compositionalHypotheses ((left.sequent.hyp.erase right.sequent.concl) ∪
        (right.sequent.hyp.erase left.sequent.concl))) (.imp q p) :=
    provable_union_left Finset.subset_union_left (provable_imp_of_erase hq pp)
  refine provable_of_extDerivation (premises := [.imp p q, .imp q p])
    (.eqPropI (.hyp (by simp)) (.hyp (by simp))) ?_
  intro ψ hψ
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hψ
  rcases hψ with rfl | rfl
  · exact forward
  · exact backward

theorem compositionallyProvable_eqMp {equality premise : Theorem}
    {left right : CanonicalTerm}
    (view : CanonicalTerm.EqualityViewSemantics equality.sequent.concl left right)
    (hmatch : left = premise.sequent.concl)
    (equalityProvable : CompositionallyProvable Θ equality.sequent)
    (premiseProvable : CompositionallyProvable Θ premise.sequent) :
    CompositionallyProvable Θ
      ⟨equality.sequent.hyp ∪ premise.sequent.hyp, right⟩ := by
  obtain ⟨φe, hφe, pe⟩ := equalityProvable
  obtain ⟨σ, l, r, hσ, hl, hr, rfl⟩ := (hφe.of_term_eq view.2).equalityDB_inv
  obtain ⟨φp, hφp, pp⟩ := premiseProvable
  subst hmatch
  obtain ⟨rfl, hheq⟩ := hl.unique hφp
  cases hheq
  refine ⟨r, hr, ?_⟩
  refine provable_of_extDerivation (premises := [.eq φp r, φp])
    (HOL.ExtDerivation.eqProp_mp_left (p := φp) (q := r) (.hyp (by simp))
      (.hyp (by simp))) ?_
  intro ψ hψ
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hψ
  rcases hψ with rfl | rfl
  · exact provable_union_left Finset.subset_union_left (provable_equalityLambda_iff.mp pe)
  · exact provable_union_left Finset.subset_union_right pp

theorem compositionallyProvable_abs (background : VariableFreeSubstitutionClosed Θ)
    {sourceVar : SourceVar} {input : Theorem}
    {left right leftAbs rightAbs equality : CanonicalTerm}
    (fresh : ¬ FreeInHypotheses sourceVar input.sequent.hyp)
    (view : CanonicalTerm.EqualityViewSemantics input.sequent.concl left right)
    (leftAbstraction : CanonicalTerm.AbstractionSemantics sourceVar left leftAbs)
    (rightAbstraction : CanonicalTerm.AbstractionSemantics sourceVar right rightAbs)
    (construction : CanonicalTerm.EqualityConstructionSemantics leftAbs rightAbs equality)
    (inputProvable : CompositionallyProvable Θ input.sequent) :
    CompositionallyProvable Θ ⟨input.sequent.hyp, equality⟩ := by
  obtain ⟨φ, hφ, premises, hpremises, derivation⟩ := inputProvable
  obtain ⟨σ, l, r, hσ, hl, hr, rfl⟩ := (hφ.of_term_eq view.2).equalityDB_inv
  have hequation := extDerivation_equalityLambda_iff.mp derivation
  have habstracted := HOL.ExtDerivation.abstractConstAt_deriv (Ξ := []) (Γ := [])
    (Symbol.ofVar sourceVar) hequation
  rw [HOL.ExtDerivation.abstractConstAt_eq] at habstracted
  have hpremisesFree : ∀ ψ ∈ premises,
      HOL.NoConstOccurrence (Symbol.ofVar sourceVar) ψ := by
    intro ψ hψ
    rcases hpremises ψ hψ with hΘ | ⟨term, hterm, htranslation⟩
    · exact background.variableFree ψ hΘ sourceVar
    · exact htranslation.noConstOccurrence sourceVar
        (fun found => fresh ⟨term, hterm, found⟩)
  have hweaken : premises.map (HOL.abstractConstAt (Γ := []) (Symbol.ofVar sourceVar) []) =
      HOL.weakenHyps (σ := sourceVar.ty.toHOL) premises :=
    List.map_congr_left fun ψ hψ =>
      HOL.abstractConstAt_noOccurrence [] ψ (hpremisesFree ψ hψ)
  rw [hweaken] at habstracted
  have hlambda := HOL.ExtDerivation.eqLam habstracted
  have hleftAbs : TranslatesCompositionally [] leftAbs.term
      (.arr sourceVar.ty.toHOL σ)
      (.lam (HOL.abstractConstAt (Γ := []) (Symbol.ofVar sourceVar) [] l)) :=
    (TranslatesCompositionally.abs rfl
      (TranslatesCompositionally.closeFreeAt sourceVar (Ξ := []) hl)).of_term_eq
        leftAbstraction.symm
  have hrightAbs : TranslatesCompositionally [] rightAbs.term
      (.arr sourceVar.ty.toHOL σ)
      (.lam (HOL.abstractConstAt (Γ := []) (Symbol.ofVar sourceVar) [] r)) :=
    (TranslatesCompositionally.abs rfl
      (TranslatesCompositionally.closeFreeAt sourceVar (Ξ := []) hr)).of_term_eq
        rightAbstraction.symm
  refine ⟨_, (TranslatesCompositionally.equalityDB
    (CanonicalTerm.toHOL_ty_of_translation hleftAbs) hleftAbs hrightAbs).of_term_eq
      construction.2.symm, ?_⟩
  exact ⟨premises, hpremises, extDerivation_equalityLambda_iff.mpr hlambda⟩

theorem compositionallyProvable_subst (background : VariableFreeSubstitutionClosed Θ)
    (substitution : TypeCorrectTermSubstitution) {input : Theorem}
    (inputProvable : CompositionallyProvable Θ input.sequent) :
    CompositionallyProvable Θ
      ⟨substitution.applyHypotheses input.sequent.hyp,
        substitution.apply input.sequent.concl⟩ := by
  obtain ⟨φ, hφ, premises, hpremises, derivation⟩ := inputProvable
  refine ⟨substitution.targetMap φ, hφ.applyDB substitution,
    premises.map substitution.targetMap, ?_,
    substitution.extDerivation_targetMap derivation⟩
  intro ψ' hψ'
  obtain ⟨ψ, hψ, rfl⟩ := List.mem_map.mp hψ'
  rcases hpremises ψ hψ with hΘ | ⟨term, hterm, htranslation⟩
  · exact Or.inl (background.substitutionClosed substitution ψ hΘ)
  · exact Or.inr ⟨substitution.apply term,
      Finset.mem_image_of_mem _ hterm, htranslation.applyDB substitution⟩

/-- One primitive step preserves compositional provability, given
compositional provability of its theorem premises (under their own axiom tags)
and of every axiom tag of the result. -/
theorem PrimitiveEvidence.compositionallyProvable
    (background : VariableFreeSubstitutionClosed Θ)
    {request : PrimitiveRequest} {out : Theorem}
    (evidence : PrimitiveEvidence request out)
    (premisesProvable : ∀ premise ∈ request.premises,
      (∀ tagged ∈ premise.axioms, CompositionallyProvable Θ tagged) →
        CompositionallyProvable Θ premise.sequent)
    (axiomsProvable : ∀ tagged ∈ out.axioms, CompositionallyProvable Θ tagged) :
    CompositionallyProvable Θ out.sequent := by
  cases evidence with
  | core evidence =>
      cases evidence with
      | «axiom» hbool parts =>
          rw [parts.sequent_eq]
          exact axiomsProvable _ (by rw [parts.1]; exact Finset.mem_singleton_self _)
      | «assume» hbool parts =>
          rw [parts.sequent_eq]
          exact compositionallyProvable_assume hbool
      | refl equality construction parts =>
          rw [parts.sequent_eq]
          exact compositionallyProvable_refl construction
      | app functionLeft functionRight argumentLeft argumentRight applicationLeft
          applicationRight equality functionView argumentView leftApplication
          rightApplication construction parts =>
          rw [parts.sequent_eq]
          exact compositionallyProvable_app functionView argumentView leftApplication
            rightApplication construction
            (premisesProvable _ (by simp [PrimitiveRequest.premises]) fun tagged htagged =>
              axiomsProvable tagged (by rw [parts.1]; exact Finset.mem_union_left _ htagged))
            (premisesProvable _ (by simp [PrimitiveRequest.premises]) fun tagged htagged =>
              axiomsProvable tagged (by rw [parts.1]; exact Finset.mem_union_right _ htagged))
      | deductAntisym equality construction parts =>
          rw [parts.sequent_eq]
          exact compositionallyProvable_deductAntisym construction
            (premisesProvable _ (by simp [PrimitiveRequest.premises]) fun tagged htagged =>
              axiomsProvable tagged (by rw [parts.1]; exact Finset.mem_union_left _ htagged))
            (premisesProvable _ (by simp [PrimitiveRequest.premises]) fun tagged htagged =>
              axiomsProvable tagged (by rw [parts.1]; exact Finset.mem_union_right _ htagged))
      | eqMp left right view hmatch parts =>
          rw [parts.sequent_eq]
          exact compositionallyProvable_eqMp view hmatch
            (premisesProvable _ (by simp [PrimitiveRequest.premises]) fun tagged htagged =>
              axiomsProvable tagged (by rw [parts.1]; exact Finset.mem_union_left _ htagged))
            (premisesProvable _ (by simp [PrimitiveRequest.premises]) fun tagged htagged =>
              axiomsProvable tagged (by rw [parts.1]; exact Finset.mem_union_right _ htagged))
  | binding evidence =>
      cases evidence with
      | abs fresh left right leftAbs rightAbs equality view leftAbstraction
          rightAbstraction construction parts =>
          rw [parts.sequent_eq]
          exact compositionallyProvable_abs background fresh view leftAbstraction
            rightAbstraction construction
            (premisesProvable _ (by simp [PrimitiveRequest.premises]) fun tagged htagged =>
              axiomsProvable tagged (by rw [parts.1]; exact htagged))
      | betaConv reduced equality reduction construction parts =>
          rw [parts.sequent_eq]
          exact compositionallyProvable_betaConv reduction construction
  | subst evidence =>
      obtain ⟨haxioms, hhyp, hconcl⟩ := evidence
      have hsequent : out.sequent =
          ⟨_ , (TypeCorrectTermSubstitution.apply _ _)⟩ :=
        Sequent.ext
          ((applyHypotheses_semantics _ _).unique hhyp).symm
          ((apply_eq_iff_termSubstitutionSemantics _ _ _).mpr hconcl).symm
      rw [hsequent]
      exact compositionallyProvable_subst background _
        (premisesProvable _ (by simp [PrimitiveRequest.premises]) fun tagged htagged =>
          axiomsProvable tagged (by rw [haxioms]; exact htagged))

/-- Every theorem in the least closure of the primitive kernel under any axiom
policy has a compositionally provable current sequent, provided its axiom tags
do. -/
theorem derives_compositionallyProvable (background : VariableFreeSubstitutionClosed Θ)
    {policy : AxiomPolicy} {out : Theorem}
    (derivation : Mettapedia.Logic.Derives (PolicyPrimitiveRule policy) out) :
    (∀ tagged ∈ out.axioms, CompositionallyProvable Θ tagged) →
      CompositionallyProvable Θ out.sequent := by
  induction derivation with
  | node premises conclusion rule _ ih =>
      intro axiomsProvable
      obtain ⟨request, rfl, -, ⟨evidence⟩⟩ := rule
      exact evidence.compositionallyProvable background ih axiomsProvable

end RulePreservation

/-! ## Translation with primitive equality

This is the translation used in the main statements.  A full application
`(= : a -> a -> bool) l r` of primitive equality becomes the target equality
`l = r`; an unapplied or partially applied occurrence of primitive equality is
eta-expanded exactly as in the compositional translation.
-/

namespace DBTerm

/-- The operand type when a term is primitive equality at an exact equality
type applied to one argument. -/
def equalityHeadOperand? : DBTerm → Option Ty
  | .app (.const constant annotation) _ => equalityOperand? constant annotation
  | _ => none

theorem equalityHeadOperand?_eq_some_iff {term : DBTerm} {operand : Ty} :
    term.equalityHeadOperand? = some operand ↔
      ∃ constant annotation left, term = .app (.const constant annotation) left ∧
        equalityOperand? constant annotation = some operand := by
  constructor
  · intro h
    match term, h with
    | .app (.const constant annotation) left, h => exact ⟨constant, annotation, left, rfl, h⟩
  · rintro ⟨constant, annotation, left, rfl, h⟩
    exact h

end DBTerm

inductive Translates :
    (Γ : HOL.Ctx AtomicTy) → DBTerm → (τ : HOL.Ty AtomicTy) →
      HOL.Term Symbol Γ τ → Prop
  | equality {Γ : HOL.Ctx AtomicTy} {constant : Const} {annotation operand : Ty}
      {σ : HOL.Ty AtomicTy}
      (recognized : equalityOperand? constant annotation = some operand)
      (typed : operand.toHOL = σ) :
      Translates Γ (.const constant annotation) (.arr σ (.arr σ .prop))
        (equalityLambda σ)
  | constant {Γ : HOL.Ctx AtomicTy} {constant : Const} {annotation : Ty}
      {τ : HOL.Ty AtomicTy}
      (unrecognized : equalityOperand? constant annotation = none)
      (typed : annotation.toHOL = τ) :
      Translates Γ (.const constant annotation) τ
        (.const (.constant constant annotation typed))
  | free {Γ : HOL.Ctx AtomicTy} {sourceVar : SourceVar} {τ : HOL.Ty AtomicTy}
      (typed : sourceVar.ty.toHOL = τ) :
      Translates Γ (.free sourceVar) τ (.const (.variable sourceVar typed))
  | bound {Γ : HOL.Ctx AtomicTy} {τ : HOL.Ty AtomicTy} (x : HOL.Var Γ τ) :
      Translates Γ (.bound (deBruijnIndex x)) τ (.var x)
  | equalityApp {Γ : HOL.Ctx AtomicTy} {constant : Const} {annotation operand : Ty}
      {left right : DBTerm} {σ : HOL.Ty AtomicTy} {left' right' : HOL.Term Symbol Γ σ}
      (recognized : equalityOperand? constant annotation = some operand)
      (typed : operand.toHOL = σ) :
      Translates Γ left σ left' → Translates Γ right σ right' →
      Translates Γ (.app (.app (.const constant annotation) left) right) .prop
        (.eq left' right')
  | app {Γ : HOL.Ctx AtomicTy} {function argument : DBTerm}
      {σ τ : HOL.Ty AtomicTy} {function' : HOL.Term Symbol Γ (.arr σ τ)}
      {argument' : HOL.Term Symbol Γ σ}
      (notEquality : function.equalityHeadOperand? = none) :
      Translates Γ function (.arr σ τ) function' →
      Translates Γ argument σ argument' →
      Translates Γ (.app function argument) τ (.app function' argument')
  | abs {Γ : HOL.Ctx AtomicTy} {domain : Ty} {body : DBTerm}
      {σ τ : HOL.Ty AtomicTy} {body' : HOL.Term Symbol (σ :: Γ) τ}
      (typed : domain.toHOL = σ) :
      Translates (σ :: Γ) body τ body' →
      Translates Γ (.abs domain body) (.arr σ τ) (.lam body')

namespace Translates

/-- The translation with primitive equality is a partial function. -/
theorem unique {Γ : HOL.Ctx AtomicTy} {term : DBTerm} {τ : HOL.Ty AtomicTy}
    {target : HOL.Term Symbol Γ τ} (translation : Translates Γ term τ target) :
    ∀ {τ' : HOL.Ty AtomicTy} {target' : HOL.Term Symbol Γ τ'},
      Translates Γ term τ' target' → τ = τ' ∧ HEq target target' := by
  induction translation with
  | equality recognized typed =>
      intro τ' target' other
      cases other with
      | equality recognized' typed' =>
          rw [recognized] at recognized'
          cases recognized'
          subst typed typed'
          exact ⟨rfl, HEq.rfl⟩
      | constant unrecognized' _ =>
          rw [recognized] at unrecognized'
          cases unrecognized'
  | constant unrecognized typed =>
      intro τ' target' other
      cases other with
      | equality recognized' _ =>
          rw [unrecognized] at recognized'
          cases recognized'
      | constant _ typed' =>
          subst typed typed'
          exact ⟨rfl, HEq.rfl⟩
  | free typed =>
      intro τ' target' other
      cases other with
      | free typed' =>
          subst typed typed'
          exact ⟨rfl, HEq.rfl⟩
  | bound x =>
      intro τ' target' other
      generalize hindex : deBruijnIndex x = index at other
      cases other with
      | bound y =>
          obtain ⟨rfl, hxy⟩ := deBruijnIndex_injective x y hindex
          cases hxy
          exact ⟨rfl, HEq.rfl⟩
  | equalityApp recognized typed _ _ leftIH rightIH =>
      intro τ' target' other
      cases other with
      | equalityApp recognized' typed' left' right' =>
          rw [recognized] at recognized'
          cases recognized'
          subst typed typed'
          obtain ⟨-, hleft⟩ := leftIH left'
          obtain ⟨-, hright⟩ := rightIH right'
          cases hleft
          cases hright
          exact ⟨rfl, HEq.rfl⟩
      | app notEquality _ _ =>
          simp only [DBTerm.equalityHeadOperand?, recognized] at notEquality
          cases notEquality
  | app notEquality _ _ functionIH argumentIH =>
      intro τ' target' other
      cases other with
      | equalityApp recognized' _ _ _ =>
          simp only [DBTerm.equalityHeadOperand?, recognized'] at notEquality
          cases notEquality
      | app _ function' argument' =>
          obtain ⟨hfunctionTy, hfunction⟩ := functionIH function'
          cases hfunctionTy
          cases hfunction
          obtain ⟨-, hargument⟩ := argumentIH argument'
          cases hargument
          exact ⟨rfl, HEq.rfl⟩
  | abs typed _ bodyIH =>
      intro τ' target' other
      cases other with
      | abs typed' body' =>
          subst typed typed'
          obtain ⟨rfl, hbody⟩ := bodyIH body'
          cases hbody
          exact ⟨rfl, HEq.rfl⟩

theorem unique_eq {Γ : HOL.Ctx AtomicTy} {term : DBTerm} {τ : HOL.Ty AtomicTy}
    {target target' : HOL.Term Symbol Γ τ} (translation : Translates Γ term τ target)
    (translation' : Translates Γ term τ target') : target = target' :=
  eq_of_heq (translation.unique translation').2

/-- Every translation with primitive equality has a compositional counterpart
at the same type. -/
theorem exists_compositional {Γ : HOL.Ctx AtomicTy} {term : DBTerm}
    {τ : HOL.Ty AtomicTy} {target : HOL.Term Symbol Γ τ}
    (translation : Translates Γ term τ target) :
    ∃ target', TranslatesCompositionally Γ term τ target' := by
  induction translation with
  | equality recognized typed => exact ⟨_, .equality recognized typed⟩
  | constant unrecognized typed => exact ⟨_, .constant unrecognized typed⟩
  | free typed => exact ⟨_, .free typed⟩
  | bound x => exact ⟨_, .bound x⟩
  | equalityApp recognized typed _ _ leftIH rightIH =>
      obtain ⟨left', hleft⟩ := leftIH
      obtain ⟨right', hright⟩ := rightIH
      exact ⟨_, .app (.app (.equality recognized typed) hleft) hright⟩
  | app _ _ _ functionIH argumentIH =>
      obtain ⟨function', hfunction⟩ := functionIH
      obtain ⟨argument', hargument⟩ := argumentIH
      exact ⟨_, .app hfunction hargument⟩
  | abs typed _ bodyIH =>
      obtain ⟨body', hbody⟩ := bodyIH
      exact ⟨_, .abs typed hbody⟩

end Translates

namespace TranslatesCompositionally

/-- Every compositional translation has a counterpart with primitive
equality at the same type. -/
theorem exists_translates {Γ : HOL.Ctx AtomicTy} {term : DBTerm}
    {τ : HOL.Ty AtomicTy} {target : HOL.Term Symbol Γ τ}
    (translation : TranslatesCompositionally Γ term τ target) :
    ∃ target', Translates Γ term τ target' := by
  induction translation with
  | equality recognized typed => exact ⟨_, .equality recognized typed⟩
  | constant unrecognized typed => exact ⟨_, .constant unrecognized typed⟩
  | free typed => exact ⟨_, .free typed⟩
  | bound x => exact ⟨_, .bound x⟩
  | @app Γ function argument σ τ _ _ _ _ functionIH argumentIH =>
      obtain ⟨function', hfunction⟩ := functionIH
      obtain ⟨argument', hargument⟩ := argumentIH
      cases hhead : function.equalityHeadOperand? with
      | none => exact ⟨_, .app hhead hfunction hargument⟩
      | some operand =>
          obtain ⟨head, annotation, left, rfl, recognized⟩ :=
            DBTerm.equalityHeadOperand?_eq_some_iff.mp hhead
          cases hfunction with
          | app _ hconstant hleft =>
              cases hconstant with
              | equality recognized' typed =>
                  exact ⟨_, .equalityApp recognized' typed hleft hargument⟩
              | constant unrecognized _ =>
                  rw [recognized] at unrecognized
                  cases unrecognized
  | abs typed _ bodyIH =>
      obtain ⟨body', hbody⟩ := bodyIH
      exact ⟨_, .abs typed hbody⟩

end TranslatesCompositionally

theorem extDerivation_eq_congr {Γ : HOL.Ctx AtomicTy} {Δ : List (HOL.Formula Symbol Γ)}
    {τ : HOL.Ty AtomicTy} {left left' right right' : HOL.Term Symbol Γ τ}
    (hleft : HOL.ExtDerivation Symbol Δ (.eq left left'))
    (hright : HOL.ExtDerivation Symbol Δ (.eq right right')) :
    HOL.ExtDerivation Symbol Δ (.eq (.eq left right) (.eq left' right')) := by
  have weaken : ∀ {χ : HOL.Formula Symbol Γ} {φ : HOL.Formula Symbol Γ},
      HOL.ExtDerivation Symbol Δ φ → HOL.ExtDerivation Symbol (χ :: Δ) φ :=
    fun derivation => HOL.ExtDerivation.mono (fun h => List.mem_cons_of_mem _ h) derivation
  refine .eqPropI (.impI ?_) (.impI ?_)
  · exact .eqTrans (.eqTrans (.eqSymm (weaken hleft)) (.hyp List.mem_cons_self))
      (weaken hright)
  · exact .eqTrans (.eqTrans (weaken hleft) (.hyp List.mem_cons_self))
      (.eqSymm (weaken hright))

namespace Translates

/-- The two translations agree up to provable equality in every
hypothesis context. -/
theorem extDerivation_eq_compositional {Γ : HOL.Ctx AtomicTy} {term : DBTerm}
    {τ : HOL.Ty AtomicTy} {target : HOL.Term Symbol Γ τ}
    (translation : Translates Γ term τ target) :
    ∀ {target' : HOL.Term Symbol Γ τ}, TranslatesCompositionally Γ term τ target' →
      ∀ Δ : List (HOL.Formula Symbol Γ), HOL.ExtDerivation Symbol Δ (.eq target target') := by
  induction translation with
  | equality recognized typed =>
      intro target' other Δ
      cases other with
      | equality recognized' typed' => exact .eqRefl _
      | constant unrecognized' _ =>
          rw [recognized] at unrecognized'
          cases unrecognized'
  | constant unrecognized typed =>
      intro target' other Δ
      cases other with
      | equality recognized' _ =>
          rw [unrecognized] at recognized'
          cases recognized'
      | constant _ typed' => exact .eqRefl _
  | free typed =>
      intro target' other Δ
      cases other with
      | free typed' => exact .eqRefl _
  | bound x =>
      intro target' other Δ
      generalize hindex : deBruijnIndex x = index at other
      cases other with
      | bound y =>
          obtain ⟨-, hxy⟩ := deBruijnIndex_injective x y hindex
          cases hxy
          exact .eqRefl _
  | equalityApp recognized typed _ _ leftIH rightIH =>
      intro target' other Δ
      cases other with
      | app hfunction hright =>
          cases hfunction with
          | app hhead hleft =>
              cases hhead with
              | equality recognized' typed' =>
                  rw [recognized] at recognized'
                  cases recognized'
                  subst typed typed'
                  exact .eqTrans (extDerivation_eq_congr (leftIH hleft Δ) (rightIH hright Δ))
                    (.eqSymm (extDerivation_equalityLambda_app_app Δ _ _))
              | constant unrecognized _ =>
                  rw [recognized] at unrecognized
                  cases unrecognized
  | app _ hfunctionTranslation _ functionIH argumentIH =>
      intro target' other Δ
      cases other with
      | app hfunction hargument =>
          obtain ⟨function'', hfunction''⟩ := hfunctionTranslation.exists_compositional
          obtain ⟨hty, -⟩ := hfunction''.unique hfunction
          cases hty
          exact HOL.ExtDerivation.eqAppCongr (functionIH hfunction Δ) (argumentIH hargument Δ)
  | abs typed _ bodyIH =>
      intro target' other Δ
      cases other with
      | abs typed' hbody =>
          subst typed
          exact .eqLam (bodyIH hbody _)

end Translates

/-! ## Provability of translated sequents -/

/-- The translations of the Boolean members of a hypothesis set. -/
def translatedHypotheses (hyp : Finset CanonicalTerm) : HOL.ClosedTheorySet Symbol :=
  {φ | ∃ term ∈ hyp, Translates [] term.term .prop φ}

/-- A sequent's translated conclusion is provable in the extensional
higher-order calculus from the background sentences `Θ` together with its
translated hypotheses. -/
def TranslatedProvable (Θ : HOL.ClosedTheorySet Symbol) (sequent : Sequent) : Prop :=
  ∃ φ, Translates [] sequent.concl.term .prop φ ∧
    HOL.ClosedTheorySet.Provable (Θ ∪ translatedHypotheses sequent.hyp) φ

section Transfer

variable {B : Type} {C : HOL.Ty B → Type}

theorem provable_of_forall_provable {T U : HOL.ClosedTheorySet C} {φ : HOL.ClosedFormula C}
    (provable : HOL.ClosedTheorySet.Provable T φ)
    (members : ∀ ψ ∈ T, HOL.ClosedTheorySet.Provable U ψ) :
    HOL.ClosedTheorySet.Provable U φ := by
  obtain ⟨premises, hpremises, derivation⟩ := provable
  exact provable_of_extDerivation derivation fun ψ hψ => members ψ (hpremises ψ hψ)

end Transfer

theorem provable_of_eq_provable {T : HOL.ClosedTheorySet Symbol}
    {φ ψ : HOL.ClosedFormula Symbol}
    (equal : HOL.ExtDerivation Symbol [] (.eq φ ψ))
    (provable : HOL.ClosedTheorySet.Provable T ψ) :
    HOL.ClosedTheorySet.Provable T φ :=
  provable_of_extDerivation (premises := [ψ])
    (HOL.ExtDerivation.eqProp_mp_right (HOL.ExtDerivation.ofTheorem equal)
      (.hyp List.mem_cons_self))
    (fun χ hχ => by
      rw [List.mem_singleton] at hχ
      subst hχ
      exact provable)

theorem provable_of_provable_eq {T : HOL.ClosedTheorySet Symbol}
    {φ ψ : HOL.ClosedFormula Symbol}
    (equal : HOL.ExtDerivation Symbol [] (.eq φ ψ))
    (provable : HOL.ClosedTheorySet.Provable T φ) :
    HOL.ClosedTheorySet.Provable T ψ :=
  provable_of_extDerivation (premises := [φ])
    (HOL.ExtDerivation.eqProp_mp_left (HOL.ExtDerivation.ofTheorem equal)
      (.hyp List.mem_cons_self))
    (fun χ hχ => by
      rw [List.mem_singleton] at hχ
      subst hχ
      exact provable)

/-- Provability of a translated sequent does not depend on which of the two
translations is used. -/
theorem translatedProvable_iff_compositionallyProvable
    (Θ : HOL.ClosedTheorySet Symbol) (sequent : Sequent) :
    TranslatedProvable Θ sequent ↔ CompositionallyProvable Θ sequent := by
  constructor
  · rintro ⟨φ, hφ, provable⟩
    obtain ⟨φ', hφ'⟩ := hφ.exists_compositional
    refine ⟨φ', hφ', provable_of_provable_eq (hφ.extDerivation_eq_compositional hφ' [])
      (provable_of_forall_provable provable ?_)⟩
    rintro ψ (hΘ | ⟨term, hterm, htranslation⟩)
    · exact HOL.ClosedTheorySet.provable_of_mem (Or.inl hΘ)
    · obtain ⟨ψ', hψ'⟩ := htranslation.exists_compositional
      exact provable_of_eq_provable (htranslation.extDerivation_eq_compositional hψ' [])
        (HOL.ClosedTheorySet.provable_of_mem (Or.inr ⟨term, hterm, hψ'⟩))
  · rintro ⟨φ', hφ', provable⟩
    obtain ⟨φ, hφ⟩ := hφ'.exists_translates
    refine ⟨φ, hφ, provable_of_eq_provable (hφ.extDerivation_eq_compositional hφ' [])
      (provable_of_forall_provable provable ?_)⟩
    rintro ψ' (hΘ | ⟨term, hterm, htranslation⟩)
    · exact HOL.ClosedTheorySet.provable_of_mem (Or.inl hΘ)
    · obtain ⟨ψ, hψ⟩ := htranslation.exists_translates
      exact provable_of_provable_eq (hψ.extDerivation_eq_compositional htranslation [])
        (HOL.ClosedTheorySet.provable_of_mem (Or.inr ⟨term, hterm, hψ⟩))

/-! ## Interpretation of the primitive kernel -/

/-- **Interpretation of the OpenTheory primitive kernel.**  Every theorem in
the least closure of the nine primitive rules, under any axiom policy, has a
translated sequent that is provable in the extensional higher-order calculus
from `Θ`, provided `Θ` is variable-free and substitution-closed and every axiom
tag of the theorem is provable from `Θ` in the same sense. -/
theorem derives_translatedProvable {Θ : HOL.ClosedTheorySet Symbol}
    (background : VariableFreeSubstitutionClosed Θ) {policy : AxiomPolicy}
    {out : Theorem}
    (derivation : Mettapedia.Logic.Derives (PolicyPrimitiveRule policy) out)
    (axiomsProvable : ∀ tagged ∈ out.axioms, TranslatedProvable Θ tagged) :
    TranslatedProvable Θ out.sequent :=
  (translatedProvable_iff_compositionallyProvable Θ out.sequent).mpr
    (derives_compositionallyProvable background derivation fun tagged htagged =>
      (translatedProvable_iff_compositionallyProvable Θ tagged).mp
        (axiomsProvable tagged htagged))

/-- Policy form: if every sequent admitted by the axiom policy is provable from
`Θ`, then every theorem of the policy's closure is. -/
theorem derives_translatedProvable_of_policy {Θ : HOL.ClosedTheorySet Symbol}
    (background : VariableFreeSubstitutionClosed Θ) {policy : AxiomPolicy}
    (policyProvable : ∀ sequent, policy sequent → TranslatedProvable Θ sequent)
    {out : Theorem}
    (derivation : Mettapedia.Logic.Derives (PolicyPrimitiveRule policy) out) :
    TranslatedProvable Θ out.sequent :=
  derives_translatedProvable background derivation fun tagged htagged =>
    policyProvable tagged (derives_only_authorized_axioms policy derivation tagged htagged)

/-- A theorem of the closure that carries no axiom tag has a translated
sequent provable from its translated hypotheses alone. -/
theorem derives_translatedProvable_of_axioms_eq_empty {policy : AxiomPolicy}
    {out : Theorem}
    (derivation : Mettapedia.Logic.Derives (PolicyPrimitiveRule policy) out)
    (untagged : out.axioms = ∅) :
    TranslatedProvable ∅ out.sequent :=
  derives_translatedProvable variableFreeSubstitutionClosed_empty derivation
    fun tagged htagged => by
      rw [untagged] at htagged
      exact absurd htagged (Finset.notMem_empty _)

theorem axioms_eq_empty_of_emptyAxiomPolicy {out : Theorem}
    (derivation : Mettapedia.Logic.Derives (PolicyPrimitiveRule emptyAxiomPolicy) out) :
    out.axioms = ∅ :=
  Finset.eq_empty_of_forall_notMem fun tagged htagged =>
    derives_only_authorized_axioms emptyAxiomPolicy derivation tagged htagged

/-- The axiom-free kernel: every theorem of the closure under the empty axiom
policy has a translated sequent provable from its translated hypotheses. -/
theorem derives_translatedProvable_of_emptyAxiomPolicy {out : Theorem}
    (derivation : Mettapedia.Logic.Derives (PolicyPrimitiveRule emptyAxiomPolicy) out) :
    TranslatedProvable ∅ out.sequent :=
  derives_translatedProvable_of_axioms_eq_empty derivation
    (axioms_eq_empty_of_emptyAxiomPolicy derivation)

/-- The executable checker: one accepted primitive request preserves
translated provability. -/
theorem checkPrimitive_translatedProvable {Θ : HOL.ClosedTheorySet Symbol}
    (background : VariableFreeSubstitutionClosed Θ)
    {request : PrimitiveRequest} {out : Theorem}
    (accepted : checkPrimitive request = some out)
    (premisesProvable : ∀ premise ∈ request.premises,
      TranslatedProvable Θ premise.sequent)
    (axiomsProvable : ∀ tagged ∈ out.axioms, TranslatedProvable Θ tagged) :
    TranslatedProvable Θ out.sequent := by
  obtain ⟨evidence⟩ := (checkPrimitive_eq_some_iff request out).mp accepted
  exact (translatedProvable_iff_compositionallyProvable Θ out.sequent).mpr
    (evidence.compositionallyProvable background
      (fun premise hpremise _ =>
        (translatedProvable_iff_compositionallyProvable Θ premise.sequent).mp
          (premisesProvable premise hpremise))
      fun tagged htagged =>
        (translatedProvable_iff_compositionallyProvable Θ tagged).mp
          (axiomsProvable tagged htagged))

/-! ## Booleanity of the closure -/

/-- Every theorem of the primitive closure has a Boolean current sequent. -/
theorem derives_isBool {policy : AxiomPolicy} {out : Theorem}
    (derivation : Mettapedia.Logic.Derives (PolicyPrimitiveRule policy) out) :
    out.sequent.IsBool := by
  induction derivation with
  | node premises conclusion rule _ ih =>
      obtain ⟨request, rfl, -, ⟨evidence⟩⟩ := rule
      cases evidence with
      | core evidence =>
          apply CoreStep.outputIsBool ⟨evidence⟩
          cases evidence with
          | «axiom» => exact .axiom
          | «assume» => exact .assume
          | refl => exact .refl
          | app =>
              exact .app (ih _ (by simp [PrimitiveRequest.premises]))
                (ih _ (by simp [PrimitiveRequest.premises]))
          | deductAntisym =>
              exact .deductAntisym (ih _ (by simp [PrimitiveRequest.premises]))
                (ih _ (by simp [PrimitiveRequest.premises]))
          | eqMp =>
              exact .eqMp (ih _ (by simp [PrimitiveRequest.premises]))
                (ih _ (by simp [PrimitiveRequest.premises]))
      | binding evidence =>
          cases evidence with
          | abs fresh left right leftAbs rightAbs equality view leftAbstraction
              rightAbstraction construction parts =>
              rw [parts.sequent_eq]
              exact ⟨construction.resultIsBool,
                (ih _ (by simp [PrimitiveRequest.premises])).2⟩
          | betaConv reduced equality reduction construction parts =>
              rw [parts.sequent_eq]
              exact ⟨construction.resultIsBool, by simp⟩
      | @subst substitution input _ evidence =>
          obtain ⟨-, hhyp, hconcl⟩ := evidence
          have inputBool := ih input (by simp [PrimitiveRequest.premises])
          have hconcl' := (apply_eq_iff_termSubstitutionSemantics _ _ _).mpr hconcl
          refine ⟨?_, ?_⟩
          · rw [← hconcl']
            show substitution.raw.types.apply input.sequent.concl.ty = Ty.bool
            rw [show input.sequent.concl.ty = Ty.bool from inputBool.1,
              TypeSubst.apply_bool]
          · intro hypothesis hmember
            obtain ⟨source, hsource, hsemantics⟩ := (hhyp hypothesis).mp hmember
            rw [← (apply_eq_iff_termSubstitutionSemantics _ _ _).mpr hsemantics]
            show substitution.raw.types.apply source.ty = Ty.bool
            rw [show source.ty = Ty.bool from inputBool.2 source hsource,
              TypeSubst.apply_bool]

/-- Every hypothesis of a Boolean sequent has a translated formula in
`translatedHypotheses`. -/
theorem exists_translatedHypothesis {sequent : Sequent} (hbool : sequent.IsBool)
    {hypothesis : CanonicalTerm} (hmember : hypothesis ∈ sequent.hyp) :
    ∃ ψ, Translates [] hypothesis.term .prop ψ ∧ ψ ∈ translatedHypotheses sequent.hyp := by
  obtain ⟨ψ', hψ'⟩ := CanonicalTerm.exists_formula (hbool.2 hypothesis hmember)
  obtain ⟨ψ, hψ⟩ := hψ'.exists_translates
  exact ⟨ψ, hψ, hypothesis, hmember, hψ⟩

/-! ## Semantic consequences -/

/-- Soundness over Heyting-valued substitutional models: the translated
conclusion of every theorem of the closure is a Heyting-valued consequence of
`Θ` and its translated hypotheses. -/
theorem derives_heytingConsequence {Θ : HOL.ClosedTheorySet Symbol}
    (background : VariableFreeSubstitutionClosed Θ) {policy : AxiomPolicy}
    {out : Theorem}
    (derivation : Mettapedia.Logic.Derives (PolicyPrimitiveRule policy) out)
    (axiomsProvable : ∀ tagged ∈ out.axioms, TranslatedProvable Θ tagged) :
    ∃ φ, Translates [] out.sequent.concl.term .prop φ ∧
      HOL.HeytingSem.HeytingConsequence (Base := AtomicTy)
        (Θ ∪ translatedHypotheses out.sequent.hyp) φ := by
  obtain ⟨φ, hφ, provable⟩ := derives_translatedProvable background derivation axiomsProvable
  exact ⟨φ, hφ, HOL.HeytingSem.heytingConsequence_of_provable provable⟩

/-- The axiom-free kernel is sound for every Heyting-valued substitutional
model: each translated conclusion is a consequence of the translated
hypotheses. -/
theorem derives_heytingConsequence_of_emptyAxiomPolicy {out : Theorem}
    (derivation : Mettapedia.Logic.Derives (PolicyPrimitiveRule emptyAxiomPolicy) out) :
    ∃ φ, Translates [] out.sequent.concl.term .prop φ ∧
      HOL.HeytingSem.HeytingConsequence (Base := AtomicTy)
        (translatedHypotheses out.sequent.hyp) φ := by
  obtain ⟨φ, hφ, provable⟩ := derives_translatedProvable_of_emptyAxiomPolicy derivation
  rw [Set.empty_union] at provable
  exact ⟨φ, hφ, HOL.HeytingSem.heytingConsequence_of_provable provable⟩

section ImplicationChains

variable {B : Type} {C : HOL.Ty B → Type}

/-- Discharge a finite list of closed hypotheses into implications. -/
theorem extDerivation_foldr_imp {Δ : List (HOL.ClosedFormula C)} :
    ∀ {premises : List (HOL.ClosedFormula C)} {φ : HOL.ClosedFormula C},
      HOL.ExtDerivation C (premises ++ Δ) φ →
        HOL.ExtDerivation C Δ (premises.foldr .imp φ)
  | [], _, derivation => derivation
  | ψ :: premises, _, derivation => .impI
      (extDerivation_foldr_imp (Δ := ψ :: Δ) (premises := premises)
        (HOL.ExtDerivation.mono (fun {χ} hχ => by
          simp only [List.cons_append, List.mem_cons, List.mem_append] at hχ ⊢
          tauto) derivation))

end ImplicationChains

theorem models_of_foldr_imp (model : HOL.HenkinModel AtomicTy Symbol) :
    ∀ {premises : List (HOL.ClosedFormula Symbol)} {φ : HOL.ClosedFormula Symbol},
      model.models (premises.foldr .imp φ) → (∀ ψ ∈ premises, model.models ψ) →
        model.models φ
  | [], _, holds, _ => holds
  | ψ :: premises, _, holds, premisesHold => by
      rw [List.foldr_cons, HOL.HenkinModel.models_imp] at holds
      exact models_of_foldr_imp model (holds (premisesHold ψ List.mem_cons_self))
        fun χ hχ => premisesHold χ (List.mem_cons_of_mem _ hχ)

/-- Finite-context provability is sound for extensional Henkin models. -/
theorem provable_models {T : HOL.ClosedTheorySet Symbol} {φ : HOL.ClosedFormula Symbol}
    (provable : HOL.ClosedTheorySet.Provable T φ)
    (model : HOL.HenkinModel AtomicTy Symbol) (extensional : model.FunctionsRespectEqv)
    (theoryHolds : ∀ ψ ∈ T, model.models ψ) : model.models φ := by
  obtain ⟨premises, hpremises, derivation⟩ := provable
  have closed : HOL.ExtDerivation.Theorem Symbol (premises.foldr .imp φ) :=
    extDerivation_foldr_imp (Δ := []) (by simpa using derivation)
  exact models_of_foldr_imp model (HOL.Soundness.extTheorem_sound closed model extensional)
    fun ψ hψ => theoryHolds ψ (hpremises ψ hψ)

/-- Soundness over extensional Henkin models: in every Henkin model whose
functions respect extensional equality and which satisfies `Θ`, the
translated conclusion of every theorem of the closure holds whenever its
translated hypotheses do. -/
theorem derives_models {Θ : HOL.ClosedTheorySet Symbol}
    (background : VariableFreeSubstitutionClosed Θ) {policy : AxiomPolicy}
    {out : Theorem}
    (derivation : Mettapedia.Logic.Derives (PolicyPrimitiveRule policy) out)
    (axiomsProvable : ∀ tagged ∈ out.axioms, TranslatedProvable Θ tagged)
    (model : HOL.HenkinModel AtomicTy Symbol) (extensional : model.FunctionsRespectEqv)
    (backgroundHolds : ∀ ψ ∈ Θ, model.models ψ) :
    ∃ φ, Translates [] out.sequent.concl.term .prop φ ∧
      ((∀ ψ ∈ translatedHypotheses out.sequent.hyp, model.models ψ) → model.models φ) := by
  obtain ⟨φ, hφ, provable⟩ := derives_translatedProvable background derivation axiomsProvable
  refine ⟨φ, hφ, fun hypothesesHold => provable_models provable model extensional ?_⟩
  rintro ψ (hΘ | hhyp)
  · exact backgroundHolds ψ hΘ
  · exact hypothesesHold ψ hhyp

/-! ## A two-point standard model -/

/-- A fixed value of every type over the two-element base carrier. -/
def twoPointDefault :
    (τ : HOL.Ty AtomicTy) → HOL.Ty.denote.{0, 0} (fun _ : AtomicTy => ULift.{1} Bool) τ
  | .prop => ULift.up True
  | .base _ => ULift.up false
  | .arr _ τ => fun _ => twoPointDefault τ

/-- The standard model whose every base type is the two-element carrier
`Bool` and whose every symbol denotes a fixed default value. -/
def twoPointModel : HOL.HenkinModel.{0, 0, 0} AtomicTy Symbol :=
  HOL.HenkinModel.standard (fun _ => ULift.{1} Bool) (fun {τ} _ => twoPointDefault τ)

theorem twoPointModel_functionsRespectEqv : twoPointModel.FunctionsRespectEqv :=
  HOL.HenkinModel.functionsRespectEqv_of_fullDomains _
    (HOL.HenkinModel.fullDomains_standard _ _)

/-- A closed translated sequent without background sentences holds in the
two-point model whenever its hypotheses do. -/
theorem translatedProvable_twoPointModel {sequent : Sequent}
    (provable : TranslatedProvable ∅ sequent) :
    ∃ φ, Translates [] sequent.concl.term .prop φ ∧
      ((∀ ψ ∈ translatedHypotheses sequent.hyp, twoPointModel.models ψ) →
        twoPointModel.models φ) := by
  obtain ⟨φ, hφ, provable⟩ := provable
  refine ⟨φ, hφ, fun hypothesesHold =>
    provable_models provable twoPointModel twoPointModel_functionsRespectEqv ?_⟩
  rintro ψ (hempty | hhyp)
  · exact absurd hempty (Set.notMem_empty _)
  · exact hypothesesHold ψ hhyp

/-! ## Consistency of the axiom-free kernel -/

namespace PrimitiveSentences

/-- `λ p : bool. p`. -/
def identityBool : DBTerm := .abs Ty.bool (.bound 0)

/-- Truth expanded to primitive equality: `T = ((λ p. p) = (λ p. p))`. -/
def truthDB : DBTerm :=
  CanonicalTerm.equalityDB (.function Ty.bool Ty.bool) identityBool identityBool

/-- Falsity `F = (∀ p. p)` with `∀ = λ P. P = (λ x. T)` expanded to primitive
equality: `(λ p. p) = (λ x. T)`. -/
def falsityDB : DBTerm :=
  CanonicalTerm.equalityDB (.function Ty.bool Ty.bool) identityBool (.abs Ty.bool truthDB)

/-- The target formula `(λ p. p) = (λ p. p)`. -/
def truthFormula {Γ : HOL.Ctx AtomicTy} : HOL.Formula Symbol Γ :=
  .eq (.lam (.var .vz) : HOL.Term Symbol Γ (.arr .prop .prop)) (.lam (.var .vz))

/-- The target formula `(λ p. p) = (λ x. (λ p. p) = (λ p. p))`. -/
def falsityFormula : HOL.ClosedFormula Symbol :=
  .eq (.lam (.var .vz)) (.lam truthFormula)

theorem identityBool_translates (Γ : HOL.Ctx AtomicTy) :
    Translates Γ identityBool (.arr .prop .prop) (.lam (.var .vz)) :=
  .abs Ty.toHOL_bool (.bound .vz)

theorem truthDB_translates (Γ : HOL.Ctx AtomicTy) :
    Translates Γ truthDB .prop truthFormula :=
  .equalityApp (equalityOperand?_equality _) (by simp)
    (identityBool_translates Γ) (identityBool_translates Γ)

theorem falsityDB_translates : Translates [] falsityDB .prop falsityFormula :=
  .equalityApp (equalityOperand?_equality _) (by simp) (identityBool_translates [])
    (.abs Ty.toHOL_bool (truthDB_translates _))

end PrimitiveSentences

/-- A canonical Boolean term obtained from a translation to a formula; the
translation certifies the type check. -/
def CanonicalTerm.ofFormulaTranslation (term : DBTerm) {φ : HOL.ClosedFormula Symbol}
    (translation : Translates [] term .prop φ) : CanonicalTerm :=
  ⟨term, Ty.bool, by
    obtain ⟨_, hcompositional⟩ := translation.exists_compositional
    obtain ⟨ty, hty, htoHOL⟩ := hcompositional.inferType_eq (context := []) rfl
    rw [hty, Ty.toHOL_eq_prop_iff.mp htoHOL]⟩

/-- OpenTheory falsity, expanded to primitive equality. -/
def falsity : CanonicalTerm :=
  CanonicalTerm.ofFormulaTranslation PrimitiveSentences.falsityDB
    PrimitiveSentences.falsityDB_translates

theorem twoPointModel_not_models_falsityFormula :
    ¬ twoPointModel.models PrimitiveSentences.falsityFormula := by
  intro holds
  have atFalse := holds (ULift.up False) trivial
  exact atFalse.mpr fun _ _ => Iff.rfl

/-- **Consistency.**  No theorem of the primitive closure that carries no axiom
tag has the sequent `⊢ F`. -/
theorem falsity_not_derivable_of_axioms_eq_empty {policy : AxiomPolicy} {out : Theorem}
    (derivation : Mettapedia.Logic.Derives (PolicyPrimitiveRule policy) out)
    (untagged : out.axioms = ∅) :
    out.sequent ≠ ⟨∅, falsity⟩ := by
  intro hsequent
  have provable := derives_translatedProvable_of_axioms_eq_empty derivation untagged
  rw [hsequent] at provable
  obtain ⟨φ, hφ, holds⟩ := translatedProvable_twoPointModel provable
  have hφ' : φ = PrimitiveSentences.falsityFormula :=
    hφ.unique_eq PrimitiveSentences.falsityDB_translates
  subst hφ'
  exact twoPointModel_not_models_falsityFormula
    (holds fun ψ ⟨term, hterm, _⟩ => absurd hterm (Finset.notMem_empty _))

/-- The axiom-free kernel does not derive `⊢ F`. -/
theorem falsity_not_derivable {out : Theorem}
    (derivation : Mettapedia.Logic.Derives (PolicyPrimitiveRule emptyAxiomPolicy) out) :
    out.sequent ≠ ⟨∅, falsity⟩ :=
  falsity_not_derivable_of_axioms_eq_empty derivation
    (axioms_eq_empty_of_emptyAxiomPolicy derivation)

/-! ## Well-typedness boundary -/

theorem Translates.inferType_isSome {context : List Ty} {term : DBTerm}
    {τ : HOL.Ty AtomicTy} {target : HOL.Term Symbol (context.map Ty.toHOL) τ}
    (translation : Translates (context.map Ty.toHOL) term τ target) :
    (term.inferType context).isSome = true := by
  obtain ⟨target', htarget'⟩ := translation.exists_compositional
  exact (TranslatesCompositionally.exists_iff_inferType_isSome context term).mp
    ⟨τ, target', htarget'⟩

/-- Exactly the well-typed canonical terms translate. -/
theorem exists_translates_iff_inferType_isSome (context : List Ty) (term : DBTerm) :
    (∃ τ target, Translates (context.map Ty.toHOL) term τ target) ↔
      (term.inferType context).isSome = true := by
  constructor
  · rintro ⟨τ, target, translation⟩
    exact translation.inferType_isSome
  · intro h
    obtain ⟨τ, target', htarget'⟩ :=
      (TranslatesCompositionally.exists_iff_inferType_isSome context term).mpr h
    obtain ⟨target, htarget⟩ := htarget'.exists_translates
    exact ⟨τ, target, htarget⟩

theorem TranslatedProvable.provable {Θ : HOL.ClosedTheorySet Symbol} {sequent : Sequent}
    (provable : TranslatedProvable Θ sequent) {φ : HOL.ClosedFormula Symbol}
    (translation : Translates [] sequent.concl.term .prop φ) :
    HOL.ClosedTheorySet.Provable (Θ ∪ translatedHypotheses sequent.hyp) φ := by
  obtain ⟨φ', hφ', provable'⟩ := provable
  rwa [hφ'.unique_eq translation] at provable'

/-- Abstraction with the hypothesis-freshness condition removed. -/
def UnrestrictedAbsSemantics (sourceVar : SourceVar) (input out : Theorem) : Prop :=
  ∃ left right leftAbs rightAbs equality,
    CanonicalTerm.EqualityViewSemantics input.sequent.concl left right ∧
      CanonicalTerm.AbstractionSemantics sourceVar left leftAbs ∧
      CanonicalTerm.AbstractionSemantics sourceVar right rightAbs ∧
      CanonicalTerm.EqualityConstructionSemantics leftAbs rightAbs equality ∧
      HasParts out input.axioms input.sequent.hyp equality

theorem absSemantics_iff_fresh_and_unrestricted (sourceVar : SourceVar)
    (input out : Theorem) :
    AbsSemantics sourceVar input out ↔
      ¬ FreeInHypotheses sourceVar input.sequent.hyp ∧
        UnrestrictedAbsSemantics sourceVar input out :=
  Iff.rfl

/-- In the two-point model, the identity on a base type is not a constant
function. -/
theorem twoPointModel_not_models_identity_eq_constant {τ : HOL.Ty AtomicTy}
    (symbol : Symbol τ) (base : ∃ b, τ = .base b) :
    ¬ twoPointModel.models
      (.eq (.lam (.var .vz) : HOL.ClosedTerm Symbol (.arr τ τ)) (.lam (.const symbol))) := by
  obtain ⟨b, rfl⟩ := base
  intro holds
  have atTrue := holds (ULift.up true) trivial
  exact Bool.noConfusion (congrArg ULift.down atTrue)

/-! ## Examples -/

namespace InterpretationExamples

open BindingExamples BindingRuleExamples SequentExamples

/-- The target symbol of the free variable `x : ind`. -/
abbrev xSymbol : HOL.ClosedTerm Symbol xIndividual.ty.toHOL :=
  .const (Symbol.ofVar xIndividual)

/-- The target symbol of the free variable `y : ind`. -/
abbrev ySymbol {Γ : HOL.Ctx AtomicTy} : HOL.Term Symbol Γ yIndividual.ty.toHOL :=
  .const (Symbol.ofVar yIndividual)

/-! ### Reflexivity -/

theorem freeXRefl_derives :
    Mettapedia.Logic.Derives (PolicyPrimitiveRule emptyAxiomPolicy) freeXRefl :=
  derives_of_nullary_check emptyAxiomPolicy (.core (.refl freeX)) freeXRefl rfl
    (empty_allows_refl_request freeX)
    (by simp [checkPrimitive, checkCore, checkRefl, freeXEqualityResult, freeXRefl])

/-- `⊢ x = x` translates to the target equality `x = x`. -/
theorem freeXRefl_translation :
    Translates [] freeXRefl.sequent.concl.term .prop (.eq xSymbol xSymbol) := by
  have construction :=
    (CanonicalTerm.mkEquality?_eq_some_iff _ _ _).mp freeXEqualityResult
  change Translates [] freeXEquality.term _ _
  rw [construction.2]
  exact .equalityApp (equalityOperand?_equality _) rfl (.free rfl) (.free rfl)

theorem freeXRefl_provable :
    HOL.ClosedTheorySet.Provable (∅ ∪ translatedHypotheses freeXRefl.sequent.hyp)
      (.eq xSymbol xSymbol) :=
  (derives_translatedProvable_of_emptyAxiomPolicy freeXRefl_derives).provable
    freeXRefl_translation

/-! ### Beta conversion -/

theorem betaTheorem_accepted : checkBetaConv identityAppliedToY = some betaTheorem := by
  apply (checkBetaConv_eq_some_iff _ _).mpr
  have reduction :
      CanonicalTerm.BetaReductionSemantics identityAppliedToY freeY := by
    exact ⟨Examples.individual, .bound 0, freeY, by
      simp [identityAppliedToY, freeY], by simp [freeY]⟩
  have construction :
      CanonicalTerm.EqualityConstructionSemantics identityAppliedToY freeY betaEquality :=
    (CanonicalTerm.mkEquality?_eq_some_iff _ _ _).mp betaEqualityResult
  exact ⟨freeY, betaEquality, reduction, construction, ⟨rfl, rfl, rfl⟩⟩

theorem betaTheorem_derives :
    Mettapedia.Logic.Derives (PolicyPrimitiveRule emptyAxiomPolicy) betaTheorem :=
  derives_of_nullary_check emptyAxiomPolicy (.binding (.betaConv identityAppliedToY))
    betaTheorem rfl trivial
    (by simpa [checkPrimitive, checkBinding] using betaTheorem_accepted)

/-- `⊢ (λ x. x) y = y` translates to the target equality `(λ x. x) y = y`. -/
theorem betaTheorem_translation :
    Translates [] betaTheorem.sequent.concl.term .prop
      (.eq (.app (.lam (.var .vz)) ySymbol) ySymbol) := by
  have construction :=
    (CanonicalTerm.mkEquality?_eq_some_iff _ _ _).mp betaEqualityResult
  change Translates [] betaEquality.term _ _
  rw [construction.2]
  exact .equalityApp (equalityOperand?_equality _) rfl
    (.app rfl (.abs rfl (.bound .vz)) (.free rfl)) (.free rfl)

theorem betaTheorem_provable :
    HOL.ClosedTheorySet.Provable (∅ ∪ translatedHypotheses betaTheorem.sequent.hyp)
      (.eq (.app (.lam (.var .vz)) ySymbol) ySymbol) :=
  (derives_translatedProvable_of_emptyAxiomPolicy betaTheorem_derives).provable
    betaTheorem_translation

/-! ### Deduction antisymmetry -/

/-- The free Boolean variable `p`. -/
def pTerm : CanonicalTerm := boolVariable "p"

def pVar : SourceVar := ⟨Name.global "p", Ty.bool⟩

/-- The target symbol of `p`, a proposition. -/
abbrev pSymbol : HOL.ClosedFormula Symbol := .const (.variable pVar Ty.toHOL_bool)

def assumeP : Theorem := Theorem.emptyResult {pTerm} pTerm

theorem assumeP_accepted : checkAssume pTerm = some assumeP := by
  have hbool : pTerm.isBoolB = true :=
    (CanonicalTerm.isBoolB_eq_true_iff _).mpr rfl
  simp [checkAssume, hbool, assumeP]

theorem assumeP_derives :
    Mettapedia.Logic.Derives (PolicyPrimitiveRule emptyAxiomPolicy) assumeP :=
  derives_of_nullary_check emptyAxiomPolicy (.core (.assume pTerm)) assumeP rfl trivial
    (by simpa [checkPrimitive, checkCore] using assumeP_accepted)

private theorem pEqualityAvailable : (pTerm.mkEquality? pTerm).isSome = true := by
  simp [CanonicalTerm.mkEquality?, pTerm, boolVariable]

def pEquality : CanonicalTerm := (pTerm.mkEquality? pTerm).get pEqualityAvailable

theorem pEqualityResult : pTerm.mkEquality? pTerm = some pEquality :=
  (Option.some_get pEqualityAvailable).symm

/-- `deductAntisym` applied to `p ⊢ p` twice discharges both hypotheses. -/
def pSelfEquality : Theorem :=
  Theorem.unionResult assumeP assumeP
    ((assumeP.sequent.hyp.erase pTerm) ∪ (assumeP.sequent.hyp.erase pTerm)) pEquality

theorem pSelfEquality_accepted : checkDeductAntisym assumeP assumeP = some pSelfEquality := by
  simp [checkDeductAntisym, assumeP, Theorem.emptyResult, pEqualityResult, pSelfEquality]

theorem pSelfEquality_hyp : pSelfEquality.sequent.hyp = ∅ := by
  simp [pSelfEquality, Theorem.unionResult, assumeP, Theorem.emptyResult]

theorem pSelfEquality_derives :
    Mettapedia.Logic.Derives (PolicyPrimitiveRule emptyAxiomPolicy) pSelfEquality := by
  refine Mettapedia.Logic.Derives.node [assumeP, assumeP] pSelfEquality
    ⟨.core (.deductAntisym assumeP assumeP), rfl, ?_,
      (checkPrimitive_eq_some_iff _ _).mp pSelfEquality_accepted⟩ ?_
  · exact ⟨fun _ h => by simp [assumeP, Theorem.emptyResult] at h,
      fun _ h => by simp [assumeP, Theorem.emptyResult] at h⟩
  · intro premise hpremise
    simp only [List.mem_cons, List.not_mem_nil, or_false, or_self] at hpremise
    subst hpremise
    exact assumeP_derives

/-- `⊢ p = p` translates to the target equality of propositions `p = p`. -/
theorem pSelfEquality_translation :
    Translates [] pSelfEquality.sequent.concl.term .prop (.eq pSymbol pSymbol) := by
  have construction := (CanonicalTerm.mkEquality?_eq_some_iff _ _ _).mp pEqualityResult
  change Translates [] pEquality.term _ _
  rw [construction.2]
  exact .equalityApp (equalityOperand?_equality _) Ty.toHOL_bool (.free Ty.toHOL_bool)
    (.free Ty.toHOL_bool)

theorem pSelfEquality_provable :
    HOL.ClosedTheorySet.Provable (∅ ∪ translatedHypotheses pSelfEquality.sequent.hyp)
      (.eq pSymbol pSymbol) :=
  (derives_translatedProvable_of_emptyAxiomPolicy pSelfEquality_derives).provable
    pSelfEquality_translation

/-! ### Ill-typed terms do not translate -/

theorem illTypedApplication_not_translates :
    ¬ ∃ τ, ∃ target : HOL.ClosedTerm Symbol τ,
      Translates [] (Examples.illTypedApplication.toDB []) τ target := by
  rintro ⟨τ, target, translation⟩
  have typed := translation.inferType_isSome (context := [])
  rw [show DBTerm.inferType [] (Examples.illTypedApplication.toDB []) =
      Examples.illTypedApplication.inferType from
    by simpa using DBTerm.inferType_toDB [] Examples.illTypedApplication] at typed
  simp [Examples.illTypedApplication, Examples.individual, SourceTerm.inferType,
    Ty.destFunction?] at typed

theorem wellTypedApplication_translates :
    ∃ τ, ∃ target : HOL.ClosedTerm Symbol τ,
      Translates [] (Examples.wellTypedApplication.toDB []) τ target := by
  apply (exists_translates_iff_inferType_isSome [] _).mpr
  rw [show DBTerm.inferType [] (Examples.wellTypedApplication.toDB []) =
      Examples.wellTypedApplication.inferType from
    by simpa using DBTerm.inferType_toDB [] Examples.wellTypedApplication]
  simp [Examples.wellTypedApplication, SourceTerm.inferType]

/-! ### The freshness condition of `abs` carries weight -/

private theorem xEqYAvailable : (freeX.mkEquality? freeY).isSome = true := by
  simp [CanonicalTerm.mkEquality?, freeX, freeY]

/-- The Boolean term `x = y` for `x y : ind`. -/
def xEqY : CanonicalTerm := (freeX.mkEquality? freeY).get xEqYAvailable

theorem xEqYResult : freeX.mkEquality? freeY = some xEqY :=
  (Option.some_get xEqYAvailable).symm

/-- `x = y ⊢ x = y`. -/
def assumeXEqY : Theorem := Theorem.emptyResult {xEqY} xEqY

theorem assumeXEqY_derives :
    Mettapedia.Logic.Derives (PolicyPrimitiveRule emptyAxiomPolicy) assumeXEqY := by
  have hbool : xEqY.isBoolB = true :=
    (CanonicalTerm.isBoolB_eq_true_iff _).mpr
      ((CanonicalTerm.mkEquality?_eq_some_iff _ _ _).mp xEqYResult).resultIsBool
  exact derives_of_nullary_check emptyAxiomPolicy (.core (.assume xEqY)) assumeXEqY rfl
    trivial (by simp [checkPrimitive, checkCore, checkAssume, hbool, assumeXEqY])

/-- The executable kernel rejects abstraction over `x`, which is free in the
hypothesis `x = y`. -/
theorem assumeXEqY_abs_rejected : checkAbs xIndividual assumeXEqY = none := by
  have construction := (CanonicalTerm.mkEquality?_eq_some_iff _ _ _).mp xEqYResult
  have occurs : FreeInHypotheses xIndividual assumeXEqY.sequent.hyp := by
    refine ⟨xEqY, Finset.mem_singleton_self _, ?_⟩
    rw [construction.2]
    exact .appFunction (.appArgument .here)
  have occursB := (hasFreeInHypothesesB_eq_true_iff _ _).mpr occurs
  simp [checkAbs, occursB]

/-- `λ x. x`. -/
def leftAbs : CanonicalTerm := freeX.abstractFree xIndividual

/-- `λ x. y`. -/
def rightAbs : CanonicalTerm := freeY.abstractFree xIndividual

private theorem relaxedEqualityAvailable :
    (leftAbs.mkEquality? rightAbs).isSome = true := by
  simp [CanonicalTerm.mkEquality?, leftAbs, rightAbs, CanonicalTerm.abstractFree,
    freeX, freeY]

/-- `(λ x. x) = (λ x. y)`. -/
def relaxedEquality : CanonicalTerm :=
  (leftAbs.mkEquality? rightAbs).get relaxedEqualityAvailable

theorem relaxedEqualityResult : leftAbs.mkEquality? rightAbs = some relaxedEquality :=
  (Option.some_get relaxedEqualityAvailable).symm

/-- `x = y ⊢ (λ x. x) = (λ x. y)`, the output of abstraction over `x`
without the freshness condition. -/
def relaxedTheorem : Theorem :=
  Theorem.preserveAxiomsResult assumeXEqY assumeXEqY.sequent.hyp relaxedEquality

theorem relaxedTheorem_unrestrictedAbs :
    UnrestrictedAbsSemantics xIndividual assumeXEqY relaxedTheorem :=
  ⟨freeX, freeY, leftAbs, rightAbs, relaxedEquality,
    (CanonicalTerm.mkEquality?_eq_some_iff _ _ _).mp xEqYResult,
    (CanonicalTerm.abstractionSemantics_iff_eq _ _ _).mpr rfl,
    (CanonicalTerm.abstractionSemantics_iff_eq _ _ _).mpr rfl,
    (CanonicalTerm.mkEquality?_eq_some_iff _ _ _).mp relaxedEqualityResult,
    ⟨rfl, rfl, rfl⟩⟩

theorem xEqY_translation :
    Translates [] xEqY.term .prop (.eq xSymbol ySymbol) := by
  rw [((CanonicalTerm.mkEquality?_eq_some_iff _ _ _).mp xEqYResult).2]
  exact .equalityApp (equalityOperand?_equality _) rfl (.free rfl) (.free rfl)

theorem relaxedEquality_translation :
    Translates [] relaxedEquality.term .prop
      (.eq (.lam (.var .vz)) (.lam ySymbol)) := by
  have different : xIndividual ≠ yIndividual := by
    simp [xIndividual, yIndividual, Name.global]
  rw [((CanonicalTerm.mkEquality?_eq_some_iff _ _ _).mp relaxedEqualityResult).2]
  have hleft : leftAbs.term = .abs Examples.individual (.bound 0) := by
    simp [leftAbs, CanonicalTerm.abstractFree, freeX, xIndividual]
  have hright : rightAbs.term = .abs Examples.individual (.free yIndividual) := by
    simp only [rightAbs, CanonicalTerm.abstractFree, freeY, xIndividual]
    congr 1
    exact DBTerm.closeFreeAt_other xIndividual yIndividual 0 different
  rw [hleft, hright]
  exact .equalityApp (equalityOperand?_equality _) (Ty.toHOL_function _ _)
    (.abs rfl (.bound .vz)) (.abs rfl (.free rfl))

/-- **The freshness condition of `abs` carries weight.**  From the derivable
theorem `x = y ⊢ x = y`, abstraction over `x` without the freshness condition
yields `x = y ⊢ (λ x. x) = (λ x. y)`.  The kernel rejects that step, and no
theorem of the primitive closure without axiom tags has this sequent: in the
two-point model the hypothesis holds and the conclusion fails. -/
theorem unrestrictedAbs_step_leaves_untagged_closure :
    Mettapedia.Logic.Derives (PolicyPrimitiveRule emptyAxiomPolicy) assumeXEqY ∧
      checkAbs xIndividual assumeXEqY = none ∧
      UnrestrictedAbsSemantics xIndividual assumeXEqY relaxedTheorem ∧
      ∀ {policy : AxiomPolicy} {out : Theorem},
        Mettapedia.Logic.Derives (PolicyPrimitiveRule policy) out → out.axioms = ∅ →
          out.sequent ≠ relaxedTheorem.sequent := by
  refine ⟨assumeXEqY_derives, assumeXEqY_abs_rejected, relaxedTheorem_unrestrictedAbs, ?_⟩
  intro policy out derivation untagged hsequent
  have provable := derives_translatedProvable_of_axioms_eq_empty derivation untagged
  rw [hsequent] at provable
  obtain ⟨φ, hφ, holds⟩ := translatedProvable_twoPointModel provable
  have hφ' : φ = .eq (.lam (.var .vz)) (.lam ySymbol) :=
    hφ.unique_eq relaxedEquality_translation
  subst hφ'
  refine twoPointModel_not_models_identity_eq_constant (Symbol.ofVar yIndividual)
    ⟨_, Ty.toHOL_of_isAtomic ⟨rfl, ?_⟩⟩ (holds ?_)
  · exact Bool.eq_false_iff.mpr fun h => by
      simp [Ty.isBool_eq_true_iff, yIndividual, Examples.individual, Ty.bool,
        TypeOp.bool, Name.global] at h
  · rintro ψ ⟨term, hterm, htranslation⟩
    have hterm' : term = xEqY := Finset.mem_singleton.mp hterm
    subst hterm'
    rw [htranslation.unique_eq xEqY_translation]
    exact HOL.PreModel.eqv_refl _ trivial

end InterpretationExamples

end Mettapedia.Languages.OpenTheory
