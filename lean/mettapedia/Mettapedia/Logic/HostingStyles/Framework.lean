import Mettapedia.GSLT.Contexts.ContextMorphism
import Mathlib.Logic.Relation

/-!
# A logical framework with a declared conversion

The framework is one fixed calculus: the typed lambda calculus over a family
of base types, with typed constants, and with beta as its declared
computation rule.  An object logic is given to it as a *signature*: which
base types there are and which constants.  In a judgments-as-types encoding
the base types are the judgments of the object logic, a constant is a rule,
and a term of a base type is a proof of that judgment.

Relation to LF and to the lambda-Pi calculus modulo.  In LF a judgment is a
type family applied to object-language terms, `pf A`.  Here the base types
are indexed directly by a type `B` of the host, so a base type `pf A` is
`Ty.base A` for the formula `A` itself and a rule schema is a family of
constants, one per instance.  This is the fragment of LF in which type
families are applied to closed object-language terms.  It has the features
the comparison needs: terms with binding, a typing discipline in which a
proof is a term of its judgment's type, a conversion relation that the
framework treats as identity, and non-canonical terms.  It does not have
dependent function types, so it does not host object-language variables or
schematic derivations.

* `Tm signature holes context type` are the terms, intrinsically typed.  A
  term may contain *holes*: closed metavariables, each of a declared type.
  A term with holes is a context in the sense of `ContextTheory`; a term
  without holes is a term.
* `Step` is one beta step anywhere in a term, and `Conv` is the equivalence
  it generates: the declared conversion.
* `Tm.fill` fills the holes with closed terms.  Filling commutes with
  renaming, substitution and conversion.
* `frameworkTheory signature` is the framework over a signature as a theory
  presented through its contexts.  Its static equivalence is conversion and
  it has no reduction: the framework checks terms up to conversion, and
  computing is not something a proof is observed doing.

The typing discipline is intrinsic, so a step relates two terms of one type
by construction: preservation of types under the declared computation rule is
the content of the well-typed substitution `Tm.subst`.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HostingStyles.Framework

open Mettapedia.GSLT

/-- The types of the framework over base types `B`. -/
inductive Ty (B : Type) : Type where
  | base : B → Ty B
  | arrow : Ty B → Ty B → Ty B

variable {B : Type}

/-- The type of a constant with the given argument types and result. -/
def curried : (count : Nat) → (Fin count → Ty B) → B → Ty B
  | 0, _, result => .base result
  | count + 1, arguments, result =>
      .arrow (arguments 0) (curried count (fun index => arguments index.succ) result)

/-- A signature: constants, each with finitely many argument types and a
base result type. -/
structure Signature (B : Type) where
  Const : Type
  arity : Const → Nat
  argument : (constant : Const) → Fin (arity constant) → Ty B
  result : Const → B

/-- The type of a constant. -/
def Signature.constType (signature : Signature B) (constant : signature.Const) : Ty B :=
  curried (signature.arity constant) (signature.argument constant) (signature.result constant)

/-- Typed de Bruijn variables; the newest variable is first. -/
inductive Var : List (Ty B) → Ty B → Type where
  | zero {type : Ty B} {context : List (Ty B)} : Var (type :: context) type
  | succ {context : List (Ty B)} {type other : Ty B} :
      Var context type → Var (other :: context) type

/-- The terms of the framework over a signature, with holes of declared
types. -/
inductive Tm (signature : Signature B) {Hole : Type} (holes : Hole → Ty B) :
    List (Ty B) → Ty B → Type where
  | var {context : List (Ty B)} {type : Ty B} : Var context type → Tm signature holes context type
  | con {context : List (Ty B)} (constant : signature.Const) :
      Tm signature holes context (signature.constType constant)
  | hole {context : List (Ty B)} (hole : Hole) : Tm signature holes context (holes hole)
  | lam {context : List (Ty B)} {domain codomain : Ty B} :
      Tm signature holes (domain :: context) codomain →
        Tm signature holes context (.arrow domain codomain)
  | app {context : List (Ty B)} {domain codomain : Ty B} :
      Tm signature holes context (.arrow domain codomain) → Tm signature holes context domain →
        Tm signature holes context codomain

variable {signature : Signature B} {Hole : Type} {holes : Hole → Ty B}

/-! ## Renaming -/

/-- A renaming of variables. -/
abbrev Renaming (source target : List (Ty B)) : Type :=
  ∀ type : Ty B, Var source type → Var target type

/-- Extend a renaming under a binder. -/
def Renaming.lift {source target : List (Ty B)} (rho : Renaming source target)
    (bound : Ty B) : Renaming (bound :: source) (bound :: target)
  | _, .zero => .zero
  | _, .succ name => .succ (rho _ name)

/-- The renaming that skips a new variable. -/
def Renaming.weaken (context : List (Ty B)) (bound : Ty B) : Renaming context (bound :: context) :=
  fun _ name => .succ name

/-- The renaming out of the empty context. -/
def Renaming.empty (target : List (Ty B)) : Renaming [] target :=
  fun _ name => nomatch name

theorem Renaming.lift_id (context : List (Ty B)) (bound : Ty B) :
    Renaming.lift (fun _ name => name : Renaming context context) bound =
      fun _ name => name := by
  funext type name
  cases name <;> rfl

theorem Renaming.lift_comp {first second third : List (Ty B)} (earlier : Renaming first second)
    (later : Renaming second third) (bound : Ty B) :
    (fun type name => (later.lift bound) type ((earlier.lift bound) type name)) =
      Renaming.lift (fun type name => later type (earlier type name)) bound := by
  funext type name
  cases name <;> rfl

theorem Renaming.empty_eq {target : List (Ty B)} (rho : Renaming [] target) :
    rho = Renaming.empty target := by
  funext type name
  exact nomatch name

/-- Rename the variables of a term. -/
def Tm.rename : {source target : List (Ty B)} → {type : Ty B} → Renaming source target →
    Tm signature holes source type → Tm signature holes target type
  | _, _, _, rho, .var name => .var (rho _ name)
  | _, _, _, _, .con constant => .con constant
  | _, _, _, _, .hole slot => .hole slot
  | _, _, _, rho, .lam body => .lam (body.rename (rho.lift _))
  | _, _, _, rho, .app function argument =>
      .app (function.rename rho) (argument.rename rho)

theorem Tm.rename_id {context : List (Ty B)} {type : Ty B}
    (term : Tm signature holes context type) :
    term.rename (fun _ name => name) = term := by
  induction term with
  | var name => rfl
  | con constant => rfl
  | hole hole => rfl
  | lam body ih => simp only [Tm.rename, Renaming.lift_id, ih]
  | app function argument ihFunction ihArgument =>
      simp only [Tm.rename, ihFunction, ihArgument]

theorem Tm.rename_rename {first second third : List (Ty B)} {type : Ty B}
    (term : Tm signature holes first type) (earlier : Renaming first second)
    (later : Renaming second third) :
    (term.rename earlier).rename later =
      term.rename (fun type name => later type (earlier type name)) := by
  induction term generalizing second third with
  | var name => rfl
  | con constant => rfl
  | hole hole => rfl
  | lam body ih => simp only [Tm.rename, ih, Renaming.lift_comp]
  | app function argument ihFunction ihArgument =>
      simp only [Tm.rename, ihFunction, ihArgument]

/-- A closed term is unchanged by the renaming out of the empty context. -/
theorem Tm.rename_closed {type : Ty B} (term : Tm signature holes [] type)
    (rho : Renaming ([] : List (Ty B)) []) : term.rename rho = term := by
  have same : rho = fun _ name => name := by
    funext type name
    exact nomatch name
  rw [same, Tm.rename_id]

/-! ## Substitution -/

/-- A substitution of terms for variables. -/
abbrev Subst (signature : Signature B) {Hole : Type} (holes : Hole → Ty B)
    (source target : List (Ty B)) : Type :=
  ∀ type : Ty B, Var source type → Tm signature holes target type

/-- Extend a substitution under a binder. -/
def Subst.lift {source target : List (Ty B)} (substitution : Subst signature holes source target)
    (bound : Ty B) : Subst signature holes (bound :: source) (bound :: target)
  | _, .zero => .var .zero
  | _, .succ name => (substitution _ name).rename (Renaming.weaken target bound)

/-- Substitute terms for the variables of a term. -/
def Tm.subst : {source target : List (Ty B)} → {type : Ty B} →
    Subst signature holes source target → Tm signature holes source type →
      Tm signature holes target type
  | _, _, _, substitution, .var name => substitution _ name
  | _, _, _, _, .con constant => .con constant
  | _, _, _, _, .hole slot => .hole slot
  | _, _, _, substitution, .lam body => .lam (body.subst (substitution.lift _))
  | _, _, _, substitution, .app function argument =>
      .app (function.subst substitution) (argument.subst substitution)

/-- The substitution of one term for the newest variable. -/
def Subst.single {context : List (Ty B)} {bound : Ty B}
    (argument : Tm signature holes context bound) : Subst signature holes (bound :: context) context
  | _, .zero => argument
  | _, .succ name => .var name

/-- Instantiate the newest variable of a body. -/
def Tm.inst {context : List (Ty B)} {bound type : Ty B}
    (body : Tm signature holes (bound :: context) type)
    (argument : Tm signature holes context bound) : Tm signature holes context type :=
  body.subst (Subst.single argument)

theorem Tm.rename_subst {first second third : List (Ty B)} {type : Ty B}
    (term : Tm signature holes first type) (substitution : Subst signature holes first second)
    (rho : Renaming second third) :
    (term.subst substitution).rename rho =
      term.subst (fun type name => (substitution type name).rename rho) := by
  induction term generalizing second third with
  | var name => rfl
  | con constant => rfl
  | hole hole => rfl
  | lam body ih =>
      simp only [Tm.rename, Tm.subst, ih]
      congr 2
      funext type name
      cases name with
      | zero => rfl
      | succ name =>
          simp only [Subst.lift, Tm.rename_rename]
          rfl
  | app function argument ihFunction ihArgument =>
      simp only [Tm.rename, Tm.subst, ihFunction, ihArgument]

theorem Tm.subst_rename {first second third : List (Ty B)} {type : Ty B}
    (term : Tm signature holes first type) (rho : Renaming first second)
    (substitution : Subst signature holes second third) :
    (term.rename rho).subst substitution =
      term.subst (fun type name => substitution type (rho type name)) := by
  induction term generalizing second third with
  | var name => rfl
  | con constant => rfl
  | hole hole => rfl
  | lam body ih =>
      simp only [Tm.rename, Tm.subst, ih]
      congr 2
      funext type name
      cases name <;> rfl
  | app function argument ihFunction ihArgument =>
      simp only [Tm.rename, Tm.subst, ihFunction, ihArgument]

theorem Tm.subst_var {source target : List (Ty B)} {type : Ty B}
    (term : Tm signature holes source type) (rho : Renaming source target) :
    term.subst (fun type name => .var (rho type name)) = term.rename rho := by
  induction term generalizing target with
  | var name => rfl
  | con constant => rfl
  | hole hole => rfl
  | lam body ih =>
      simp only [Tm.rename, Tm.subst, ← ih]
      congr 2
      funext type name
      cases name <;> rfl
  | app function argument ihFunction ihArgument =>
      simp only [Tm.rename, Tm.subst, ihFunction, ihArgument]

theorem Tm.subst_id {context : List (Ty B)} {type : Ty B}
    (term : Tm signature holes context type) :
    term.subst (fun _ name => .var name) = term :=
  (term.subst_var fun _ name => name).trans term.rename_id

theorem Tm.subst_subst {first second third : List (Ty B)} {type : Ty B}
    (term : Tm signature holes first type) (earlier : Subst signature holes first second)
    (later : Subst signature holes second third) :
    (term.subst earlier).subst later =
      term.subst (fun type name => (earlier type name).subst later) := by
  induction term generalizing second third with
  | var name => rfl
  | con constant => rfl
  | hole slot => rfl
  | lam body ih =>
      simp only [Tm.subst, ih]
      congr 2
      funext type name
      cases name with
      | zero => rfl
      | succ name =>
          simp only [Subst.lift, Tm.subst_rename, Tm.rename_subst]
          rfl
  | app function argument ihFunction ihArgument =>
      simp only [Tm.subst, ihFunction, ihArgument]

/-- Extend a substitution by a term for the newest variable. -/
def Subst.cons {source target : List (Ty B)} {bound : Ty B}
    (argument : Tm signature holes target bound) (substitution : Subst signature holes source target) :
    Subst signature holes (bound :: source) target
  | _, .zero => argument
  | _, .succ name => substitution _ name

/-- Renaming commutes with instantiation. -/
theorem Tm.inst_rename {source target : List (Ty B)} {bound type : Ty B}
    (body : Tm signature holes (bound :: source) type)
    (argument : Tm signature holes source bound) (rho : Renaming source target) :
    (body.inst argument).rename rho =
      (body.rename (rho.lift bound)).inst (argument.rename rho) := by
  rw [Tm.inst, Tm.inst, Tm.rename_subst, Tm.subst_rename]
  congr 1
  funext type name
  cases name <;> rfl

/-- Instantiating a variable that does not occur changes nothing. -/
theorem Tm.inst_weaken {context : List (Ty B)} {bound type : Ty B}
    (term : Tm signature holes context type) (argument : Tm signature holes context bound) :
    (term.rename (Renaming.weaken context bound)).inst argument = term := by
  rw [Tm.inst, Tm.subst_rename]
  exact term.subst_id

/-- Substituting under a binder and then instantiating it is one
substitution. -/
theorem Tm.subst_lift_inst {source target : List (Ty B)} {bound type : Ty B}
    (body : Tm signature holes (bound :: source) type)
    (substitution : Subst signature holes source target)
    (argument : Tm signature holes target bound) :
    (body.subst (substitution.lift bound)).inst argument =
      body.subst (Subst.cons argument substitution) := by
  rw [Tm.inst, Tm.subst_subst]
  congr 1
  funext type name
  cases name with
  | zero => rfl
  | succ name => exact Tm.inst_weaken _ _

/-- A closed term is unchanged by the substitution out of the empty context. -/
theorem Tm.subst_closed {type : Ty B} (term : Tm signature holes [] type)
    (substitution : Subst signature holes [] []) : term.subst substitution = term := by
  have same : substitution = fun _ name => .var name := by
    funext type name
    exact nomatch name
  rw [same, Tm.subst_id]

/-! ## Filling holes -/

variable {Hole' : Type} {holes' : Hole' → Ty B}

/-- Fill the holes of a term with closed terms. -/
def Tm.fill (filling : (hole : Hole) → Tm signature holes' [] (holes hole)) :
    {context : List (Ty B)} → {type : Ty B} → Tm signature holes context type →
      Tm signature holes' context type
  | _, _, .var name => .var name
  | _, _, .con constant => .con constant
  | context, _, .hole slot => (filling slot).rename (Renaming.empty context)
  | _, _, .lam body => .lam (body.fill filling)
  | _, _, .app function argument => .app (function.fill filling) (argument.fill filling)

theorem Tm.fill_rename (filling : (hole : Hole) → Tm signature holes' [] (holes hole))
    {source target : List (Ty B)} {type : Ty B} (term : Tm signature holes source type)
    (rho : Renaming source target) :
    (term.rename rho).fill filling = (term.fill filling).rename rho := by
  induction term generalizing target with
  | var name => rfl
  | con constant => rfl
  | hole hole =>
      simp only [Tm.rename, Tm.fill, Tm.rename_rename]
      congr 1
      exact (Renaming.empty_eq _).symm
  | lam body ih => simp only [Tm.rename, Tm.fill, ih]
  | app function argument ihFunction ihArgument =>
      simp only [Tm.rename, Tm.fill, ihFunction, ihArgument]

theorem Tm.fill_subst (filling : (hole : Hole) → Tm signature holes' [] (holes hole))
    {source target : List (Ty B)} {type : Ty B} (term : Tm signature holes source type)
    (substitution : Subst signature holes source target) :
    (term.subst substitution).fill filling =
      (term.fill filling).subst fun type name => (substitution type name).fill filling := by
  induction term generalizing target with
  | var name => rfl
  | con constant => rfl
  | hole hole =>
      simp only [Tm.subst, Tm.fill, Tm.subst_rename]
      rw [← Tm.subst_var]
      congr 1
      funext type name
      exact nomatch name
  | lam body ih =>
      simp only [Tm.subst, Tm.fill, ih]
      congr 2
      funext type name
      cases name with
      | zero => rfl
      | succ name => exact Tm.fill_rename filling _ _
  | app function argument ihFunction ihArgument =>
      simp only [Tm.subst, Tm.fill, ihFunction, ihArgument]

/-- Filling commutes with instantiation. -/
theorem Tm.fill_inst (filling : (hole : Hole) → Tm signature holes' [] (holes hole))
    {context : List (Ty B)} {bound type : Ty B}
    (body : Tm signature holes (bound :: context) type)
    (argument : Tm signature holes context bound) :
    (body.inst argument).fill filling = (body.fill filling).inst (argument.fill filling) := by
  rw [Tm.inst, Tm.inst, Tm.fill_subst]
  congr 1
  funext type name
  cases name <;> rfl

theorem Tm.fill_fill {Hole'' : Type} {holes'' : Hole'' → Ty B}
    (first : (hole : Hole) → Tm signature holes' [] (holes hole))
    (second : (hole : Hole') → Tm signature holes'' [] (holes' hole))
    {context : List (Ty B)} {type : Ty B} (term : Tm signature holes context type) :
    (term.fill first).fill second = term.fill fun hole => (first hole).fill second := by
  induction term with
  | var name => rfl
  | con constant => rfl
  | hole hole => exact Tm.fill_rename second _ _
  | lam body ih => simp only [Tm.fill, ih]
  | app function argument ihFunction ihArgument => simp only [Tm.fill, ihFunction, ihArgument]

/-- Filling every hole with itself changes nothing. -/
theorem Tm.fill_hole {context : List (Ty B)} {type : Ty B}
    (term : Tm signature holes context type) :
    term.fill (fun hole => .hole hole) = term := by
  induction term with
  | var name => rfl
  | con constant => rfl
  | hole hole => rfl
  | lam body ih => simp only [Tm.fill, ih]
  | app function argument ihFunction ihArgument => simp only [Tm.fill, ihFunction, ihArgument]

/-! ## The declared conversion -/

/-- One beta step, anywhere in a term. -/
inductive Step : {context : List (Ty B)} → {type : Ty B} →
    Tm signature holes context type → Tm signature holes context type → Prop where
  | beta {context : List (Ty B)} {domain codomain : Ty B}
      (body : Tm signature holes (domain :: context) codomain)
      (argument : Tm signature holes context domain) :
      Step (.app (.lam body) argument) (body.inst argument)
  | lam {context : List (Ty B)} {domain codomain : Ty B}
      {body body' : Tm signature holes (domain :: context) codomain} :
      Step body body' → Step (.lam body) (.lam body')
  | appLeft {context : List (Ty B)} {domain codomain : Ty B}
      {function function' : Tm signature holes context (.arrow domain codomain)}
      {argument : Tm signature holes context domain} :
      Step function function' → Step (.app function argument) (.app function' argument)
  | appRight {context : List (Ty B)} {domain codomain : Ty B}
      {function : Tm signature holes context (.arrow domain codomain)}
      {argument argument' : Tm signature holes context domain} :
      Step argument argument' → Step (.app function argument) (.app function argument')

/-- **The declared conversion**: the equivalence generated by the steps. -/
abbrev Conv {context : List (Ty B)} {type : Ty B}
    (first second : Tm signature holes context type) : Prop :=
  Relation.EqvGen Step first second

theorem Conv.of_eq {context : List (Ty B)} {type : Ty B}
    {first second : Tm signature holes context type} (same : first = second) :
    Conv first second := by
  subst same
  exact .refl _

/-- A term is normal when it has no step. -/
def Normal {context : List (Ty B)} {type : Ty B} (term : Tm signature holes context type) : Prop :=
  ∀ next, ¬ Step term next

/-- An operation that carries steps to steps carries conversion to
conversion. -/
theorem Conv.map {context context' : List (Ty B)} {type type' : Ty B}
    {Hole₂ : Type} {holes₂ : Hole₂ → Ty B}
    (operation : Tm signature holes context type → Tm signature holes₂ context' type')
    (steps : ∀ first second, Step first second → Step (operation first) (operation second))
    {first second : Tm signature holes context type} (convertible : Conv first second) :
    Conv (operation first) (operation second) := by
  induction convertible with
  | rel first second step => exact .rel _ _ (steps first second step)
  | refl term => exact .refl _
  | symm first second _ ih => exact .symm _ _ ih
  | trans first second third _ _ ihFirst ihSecond => exact .trans _ _ _ ihFirst ihSecond

theorem Conv.lam {context : List (Ty B)} {domain codomain : Ty B}
    {body body' : Tm signature holes (domain :: context) codomain} (convertible : Conv body body') :
    Conv (Tm.lam body) (Tm.lam body') :=
  Conv.map Tm.lam (fun _ _ step => .lam step) convertible

theorem Conv.app {context : List (Ty B)} {domain codomain : Ty B}
    {function function' : Tm signature holes context (.arrow domain codomain)}
    {argument argument' : Tm signature holes context domain}
    (functions : Conv function function') (arguments : Conv argument argument') :
    Conv (Tm.app function argument) (Tm.app function' argument') :=
  .trans _ _ _ (Conv.map (fun term => Tm.app term argument) (fun _ _ step => .appLeft step) functions)
    (Conv.map (fun term => Tm.app function' term) (fun _ _ step => .appRight step) arguments)

theorem Step.rename {source target : List (Ty B)} {type : Ty B}
    {first second : Tm signature holes source type} (step : Step first second)
    (rho : Renaming source target) : Step (first.rename rho) (second.rename rho) := by
  induction step generalizing target with
  | beta body argument =>
      rw [Tm.inst_rename]
      exact .beta _ _
  | lam _ ih => exact .lam (ih _)
  | appLeft _ ih => exact .appLeft (ih _)
  | appRight _ ih => exact .appRight (ih _)

theorem Step.fill (filling : (hole : Hole) → Tm signature holes' [] (holes hole))
    {context : List (Ty B)} {type : Ty B} {first second : Tm signature holes context type}
    (step : Step first second) : Step (first.fill filling) (second.fill filling) := by
  induction step with
  | beta body argument =>
      rw [Tm.fill_inst]
      exact .beta _ _
  | lam _ ih => exact .lam ih
  | appLeft _ ih => exact .appLeft ih
  | appRight _ ih => exact .appRight ih

/-- Filling by convertible terms gives convertible terms. -/
theorem Conv.fill {first second : (hole : Hole) → Tm signature holes' [] (holes hole)}
    (convertible : ∀ hole, Conv (first hole) (second hole))
    {context : List (Ty B)} {type : Ty B} (term : Tm signature holes context type) :
    Conv (term.fill first) (term.fill second) := by
  induction term with
  | var name => exact .refl _
  | con constant => exact .refl _
  | hole hole =>
      exact Conv.map (fun term => term.rename (Renaming.empty _))
        (fun _ _ step => step.rename _) (convertible hole)
  | lam body ih => exact Conv.lam ih
  | app function argument ihFunction ihArgument => exact Conv.app ihFunction ihArgument

/-! ## The framework as a theory presented through its contexts -/

/-- No hole. -/
def noHoles : Empty → Ty B := fun hole => nomatch hole

/-- The closed terms without holes. -/
abbrev Closed (signature : Signature B) (type : Ty B) : Type :=
  Tm signature (noHoles (B := B)) [] type

/-- A closed term without holes, as a term over any family of holes. -/
def Tm.lift {type : Ty B} (term : Closed signature type) : Tm signature holes [] type :=
  term.fill fun hole => nomatch hole

/-- **The framework over a signature**, as a theory presented through its
contexts.  An interface is a type, a term is a closed term, a context is a
closed term with holes, the static equivalence is the declared conversion,
and nothing reduces. -/
def frameworkTheory (signature : Signature B) : ContextTheory.{0} where
  Interface := Ty B
  Term := Closed signature
  equations := fun _ => ⟨Conv, Relation.EqvGen.is_equivalence _⟩
  rewrites := fun _ _ => False
  rewrites_resp_left := fun _ step => step.elim
  rewrites_resp_right := fun step _ => step
  Context := fun holes result => Tm signature holes [] result
  fill := fun context filling => context.fill filling
  fill_resp := fun context _ _ related => Conv.fill related context
  identity := fun type => Tm.hole (holes := fun _ : Unit => type) ()
  fill_identity := fun _ filling => (filling ()).rename_closed _
  plug := fun {_ _ _ _ innerHoles} context inner =>
    context.fill fun index => (inner index).fill fun position =>
      Tm.hole (holes := fun position : Σ index, _ => innerHoles position.1 position.2)
        ⟨index, position⟩
  fill_plug := fun context inner filling => by
    rw [Tm.fill_fill]
    congr 1
    funext index
    rw [Tm.fill_fill]
    congr 1
    funext position
    exact (filling ⟨index, position⟩).rename_closed _
  relabel := fun {_ _ holes _} rename _ context =>
    context.fill fun index => Tm.hole (holes := holes) (rename index)
  fill_relabel := fun rename _ context filling => by
    rw [Tm.fill_fill]
    congr 1
    funext index
    exact (filling (rename index)).rename_closed _
  constant := fun term => term.lift
  fill_constant := fun term filling => by
    rw [Tm.lift, Tm.fill_fill]
    have same : (fun hole : Empty =>
        ((nomatch hole : Tm signature _ [] (noHoles hole)).fill filling :
          Tm signature (noHoles (B := B)) [] (noHoles hole))) = fun hole => .hole hole := by
      funext hole
      exact nomatch hole
    rw [same, Tm.fill_hole]

#print axioms Tm.rename_subst
#print axioms Tm.fill_subst
#print axioms Tm.fill_fill
#print axioms Step.rename
#print axioms Conv.fill
#print axioms frameworkTheory

end Mettapedia.Logic.HostingStyles.Framework
