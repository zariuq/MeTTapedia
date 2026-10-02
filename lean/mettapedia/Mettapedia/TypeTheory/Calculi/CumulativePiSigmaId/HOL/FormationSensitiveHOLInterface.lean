import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Examples.DeclarationFormation
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Examples.SignatureExtensions
import Mettapedia.Logic.HOL.Soundness

/-!
# A declared logical interface for the actual HOL syntax

This interface represents HOL variables, constants, application, abstraction,
implication, universal quantification and equality in the existing presentation
grammar. Equality is an explicitly declared HOL proposition-former, not the
native identity former or a semantic extensionality assumption.
Logical operators are closed typed terms supplied by a declaration signature;
quantification is application to a lambda, not dependent-product formation.
The independently checked symbol types imply formation-sensitive typing of
every successfully represented term. Other HOL constructors remain explicitly
unsupported by this interface.

Binding operations commute with representation. Their Henkin meaning remains
the meaning of the intrinsic source term, with the existing semantic
substitution law. This is neither a semantics of arbitrary presentation terms
nor a translation of HOL derivations into dependent inhabitants. The choice of
symbols and proposition carrier is parameterized, not a selected the cumulative Π/Σ/Id profile profile.
-/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.FormationSensitiveHOLInterface

open Presentation Presentation.Declaration Presentation.FormationSensitive
open Mettapedia.Logic

universe u v w

/-- Closed interpretations of the source's proposition and base types. -/
structure TypeInterpretation (Base : Type u) where
  proposition : Tower.Tm 0
  base : Base → Tower.Tm 0

variable {Base : Type u} {Const : HOL.Ty Base → Type v}

def typeAt (types : TypeInterpretation Base) (n : Nat) : HOL.Ty Base → Tower.Tm n
  | .prop => liftClosed types.proposition
  | .base b => liftClosed (types.base b)
  | .arr a b => .pi (typeAt types n a) (typeAt types (n + 1) b)

@[simp] theorem typeAt_rename (types : TypeInterpretation Base) {n m : Nat}
    (rho : Ren n m) (type : HOL.Ty Base) :
    Presentation.rename rho (typeAt types n type) = typeAt types m type := by
  induction type generalizing n m with
  | prop => exact rename_liftClosed _ _
  | base b => exact rename_liftClosed _ _
  | arr a b ia ib => simp only [typeAt, Presentation.rename, ia, ib]

@[simp] theorem typeAt_subst (types : TypeInterpretation Base) {n m : Nat}
    (sigma : Sub Tower.Head n m) (type : HOL.Ty Base) :
    Presentation.subst sigma (typeAt types n type) = typeAt types m type := by
  induction type generalizing n m with
  | prop => exact subst_liftClosed _ _
  | base b => exact subst_liftClosed _ _
  | arr a b ia ib => simp only [typeAt, Presentation.subst, ia, ib]

/-- Only independently typed closed symbols are required. There is no field
assuming the translation theorem or any logical validity judgment. -/
structure LogicalSignature (Base : Type u) (Const : HOL.Ty Base → Type v) where
  declarations : Signature Tower.Head
  types : TypeInterpretation Base
  proposition_formed : Typing (extendRules Tower.rules declarations) .nil
    types.proposition (sortTm Tower.zero)
  base_formed : ∀ b, Typing (extendRules Tower.rules declarations) .nil
    (types.base b) (sortTm Tower.zero)
  constant : ∀ {type}, Const type → Tower.Tm 0
  constant_typed : ∀ {type} (symbol : Const type),
    Typing (extendRules Tower.rules declarations) .nil (constant symbol) (typeAt types 0 type)
  implication : Tower.Tm 0
  implication_typed : Typing (extendRules Tower.rules declarations) .nil implication
    (typeAt types 0 (.arr .prop (.arr .prop .prop)))
  universal : HOL.Ty Base → Tower.Tm 0
  universal_typed : ∀ type, Typing (extendRules Tower.rules declarations) .nil
    (universal type) (typeAt types 0 (.arr (.arr type .prop) .prop))
  equality : HOL.Ty Base → Tower.Tm 0
  equality_typed : ∀ type, Typing (extendRules Tower.rules declarations) .nil
    (equality type) (typeAt types 0 (.arr type (.arr type .prop)))

def LogicalSignature.rules (signature : LogicalSignature Base Const) : Rules Tower.Head :=
  extendRules Tower.rules signature.declarations

/-- Closed typing is usable in every ambient context by actual renaming. -/
theorem closed_typed {R : Rules Tower.Head} {term type : Tower.Tm 0}
    (typed : Typing R .nil term type) {n : Nat} (context : Tower.Ctx n) :
    Typing R context (liftClosed term) (liftClosed type) :=
  typed.renameTyping (fun index => Fin.elim0 index)

theorem typeAt_formed_of_atoms (declarations : Signature Tower.Head)
    (types : TypeInterpretation Base)
    (proposition : Typing (extendRules Tower.rules declarations) .nil
      types.proposition (sortTm Tower.zero))
    (base : ∀ b, Typing (extendRules Tower.rules declarations) .nil
      (types.base b) (sortTm Tower.zero)) (type : HOL.Ty Base)
    {n : Nat} (context : Tower.Ctx n) :
    Typing (extendRules Tower.rules declarations) context (typeAt types n type)
      (sortTm Tower.zero) := by
  induction type generalizing n with
  | prop => exact closed_typed proposition context
  | base b => exact closed_typed (base b) context
  | arr a b ia ib =>
      apply Typing.cumul
        (.piForm (ia context) (.sort Tower.zero)
          (ib (.snoc context (typeAt types n a))) (.sort Tower.zero)
          (.sorts Tower.zero Tower.zero))
      intro valuation
      simp [LevelExpr.eval, LevelTower.zero]

theorem typeAt_formed (signature : LogicalSignature Base Const) (type : HOL.Ty Base)
    {n : Nat} (context : Tower.Ctx n) :
    Typing signature.rules context (typeAt signature.types n type) (sortTm Tower.zero) :=
  typeAt_formed_of_atoms signature.declarations signature.types
    signature.proposition_formed signature.base_formed type context

/-- A single declared equality operator takes a small type and two of its
elements, returning the chosen proposition carrier. This is ordinary native
Pi syntax; it does not identify HOL equality with the native identity type. -/
def equalityDeclarationType (proposition : Tower.Tm 0) : Tower.Tm 0 :=
  .pi (sortTm Tower.zero) (.pi (.var 0) (.pi (.var (Fin.succ 0)) (liftClosed proposition)))

/-- Formation of the polymorphic equality declaration follows from formation
of its proposition carrier, independently of any equations for equality. -/
theorem equalityDeclarationType_formed (declarations : Signature Tower.Head)
    (proposition : Tower.Tm 0)
    (formed : Typing (extendRules Tower.rules declarations) .nil proposition
      (sortTm Tower.zero)) :
    Typing (extendRules Tower.rules declarations) .nil
      (equalityDeclarationType proposition)
      (sortTm (.max (.succ Tower.zero) Tower.zero)) := by
  have piZero {n : Nat} {gamma : Tower.Ctx n} {a : Tower.Tm n}
      {b : Tower.Tm (n + 1)}
      (domain : Typing (extendRules Tower.rules declarations) gamma a (sortTm Tower.zero))
      (codomain : Typing (extendRules Tower.rules declarations) (.snoc gamma a) b
        (sortTm Tower.zero)) :
      Typing (extendRules Tower.rules declarations) gamma (.pi a b) (sortTm Tower.zero) := by
    apply Typing.cumul (.piForm domain (.sort Tower.zero) codomain (.sort Tower.zero)
      (.sorts Tower.zero Tower.zero))
    intro valuation
    simp [LevelExpr.eval, LevelTower.zero]
  apply Typing.piForm (R := extendRules Tower.rules declarations)
    (.headType (.sort Tower.zero)) (.sort (.succ Tower.zero))
    (w := .sort (.max (.succ Tower.zero) Tower.zero))
  · exact piZero (.var 0) (piZero (.var 1) (closed_typed formed _))
  · exact .sort Tower.zero
  · exact .sorts (.succ Tower.zero) Tower.zero

def context (types : TypeInterpretation Base) : (gamma : HOL.Ctx Base) → Tower.Ctx gamma.length
  | [] => .nil
  | type :: gamma => .snoc (context types gamma) (typeAt types gamma.length type)

def variableIndex : {gamma : HOL.Ctx Base} → {type : HOL.Ty Base} →
    HOL.Var gamma type → Fin gamma.length
  | _, _, .vz => 0
  | _, _, .vs prior => (variableIndex prior).succ

theorem context_lookup (types : TypeInterpretation Base) {gamma : HOL.Ctx Base}
    {type : HOL.Ty Base} (index : HOL.Var gamma type) :
    Ctx.lookup (context types gamma) (variableIndex index) = typeAt types gamma.length type := by
  induction index with
  | vz => simp [context, variableIndex]
  | vs prior ih => simp [context, variableIndex, ih]

theorem context_formed (signature : LogicalSignature Base Const) (gamma : HOL.Ctx Base) :
    ContextFormation signature.rules (context signature.types gamma) := by
  induction gamma with
  | nil => exact .nil
  | cons a gamma ih => exact .snoc ih (typeAt_formed signature a _) (.sort Tower.zero)

private def apply? {n : Nat} (function argument : Option (Tower.Tm n)) : Option (Tower.Tm n) := do
  let f ← function
  let a ← argument
  pure (.app f a)

/-- Partial representation of the actual HOL term, not a replacement source IR. -/
def represent (signature : LogicalSignature Base Const) :
    {gamma : HOL.Ctx Base} → {type : HOL.Ty Base} →
    HOL.Term Const gamma type → Option (Tower.Tm gamma.length)
  | _, _, .var index => some (.var (variableIndex index))
  | _, _, .const symbol => some (liftClosed (signature.constant symbol))
  | _, _, .app f a => apply? (represent signature f) (represent signature a)
  | _, _, .lam body => (represent signature body).map Tm.lam
  | _, _, .imp p q => apply? (apply? (some (liftClosed signature.implication))
      (represent signature p)) (represent signature q)
  | _, _, @HOL.Term.all _ _ type _ body =>
      apply? (some (liftClosed (signature.universal type)))
        ((represent signature body).map Tm.lam)
  | _, _, @HOL.Term.eq _ _ _ type left right =>
      apply? (apply? (some (liftClosed (signature.equality type)))
        (represent signature left)) (represent signature right)
  | _, _, .top | _, _, .bot | _, _, .and .. | _, _, .or ..
  | _, _, .not .. | _, _, .ex .. => none

private theorem apply?_eq_some {n : Nat} {f a : Option (Tower.Tm n)} {out : Tower.Tm n} :
    apply? f a = some out ↔ ∃ f' a', f = some f' ∧ a = some a' ∧ out = .app f' a' := by
  cases f <;> cases a <;> simp [apply?, eq_comm]

/-- Representation preserves object-language application whenever both
constituents are representable. -/
theorem represent_app (signature : LogicalSignature Base Const)
    {gamma : HOL.Ctx Base} {domain codomain : HOL.Ty Base}
    (function : HOL.Term Const gamma (.arr domain codomain))
    (argument : HOL.Term Const gamma domain)
    {functionCode argumentCode : Tower.Tm gamma.length}
    (functionRepresented : represent signature function = some functionCode)
    (argumentRepresented : represent signature argument = some argumentCode) :
    represent signature (.app function argument) =
      some (.app functionCode argumentCode) := by
  simp [represent, apply?, functionRepresented, argumentRepresented]

/-- Representation preserves object-language abstraction whenever its body
is representable. -/
theorem represent_lam (signature : LogicalSignature Base Const)
    {gamma : HOL.Ctx Base} {domain codomain : HOL.Ty Base}
    (body : HOL.Term Const (domain :: gamma) codomain)
    {bodyCode : Tower.Tm (gamma.length + 1)}
    (bodyRepresented : represent signature body = some bodyCode) :
    represent signature (.lam body) = some (.lam bodyCode) := by
  simp [represent, bodyRepresented]

/-- Equality is represented at every source type whenever both operands are
represented, including equality of higher-order functions and propositions. -/
theorem represent_eq (signature : LogicalSignature Base Const)
    {gamma : HOL.Ctx Base} {type : HOL.Ty Base}
    (left right : HOL.Term Const gamma type) {leftCode rightCode : Tower.Tm gamma.length}
    (leftRepresented : represent signature left = some leftCode)
    (rightRepresented : represent signature right = some rightCode) :
    represent signature (.eq left right) =
      some (.app (.app (liftClosed (signature.equality type)) leftCode) rightCode) := by
  simp [represent, apply?, leftRepresented, rightRepresented]

theorem represent_typed (signature : LogicalSignature Base Const)
    {gamma : HOL.Ctx Base} {type : HOL.Ty Base} (term : HOL.Term Const gamma type)
    {out : Tower.Tm gamma.length} (success : represent signature term = some out) :
    Typing signature.rules (context signature.types gamma) out
      (typeAt signature.types gamma.length type) := by
  induction term with
  | var index =>
      simp only [represent, Option.some.injEq] at success
      subst out
      simpa only [context_lookup] using Typing.var (R := signature.rules)
        (Γ := context signature.types _) (variableIndex index)
  | const symbol =>
      simp only [represent, Option.some.injEq] at success
      subst out
      simpa only [LogicalSignature.rules, liftClosed, typeAt_rename] using
        closed_typed (signature.constant_typed symbol) (context signature.types _)
  | app f a ihf iha =>
      obtain ⟨f', a', hf, ha, rfl⟩ := apply?_eq_some.mp success
      simpa only [inst0, typeAt_subst] using Typing.appElim (ihf hf) (iha ha)
  | @lam a gamma b body ih =>
      obtain ⟨body', hb, rfl⟩ := Option.map_eq_some_iff.mp success
      exact .lamIntro (typeAt_formed signature (.arr a b) _) (.sort Tower.zero) (ih hb)
  | @imp gamma p q ihp ihq =>
      obtain ⟨f', q', hf, hq, rfl⟩ := apply?_eq_some.mp success
      obtain ⟨f'', p', hsymbol, hp, rfl⟩ := apply?_eq_some.mp hf
      cases Option.some.inj hsymbol
      have hs := closed_typed signature.implication_typed (context signature.types gamma)
      simp only [liftClosed, typeAt_rename] at hs
      have first := Typing.appElim hs (ihp hp)
      simp only [inst0, typeAt_subst] at first
      simpa only [LogicalSignature.rules, liftClosed, HOL.propTy, inst0, typeAt_subst]
        using Typing.appElim first (ihq hq)
  | @all a gamma body ih =>
      obtain ⟨f', a', hf, ha, rfl⟩ := apply?_eq_some.mp success
      cases Option.some.inj hf
      obtain ⟨body', hb, rfl⟩ := Option.map_eq_some_iff.mp ha
      have bodyTyped := Typing.lamIntro (typeAt_formed signature (.arr a .prop) _)
        (.sort Tower.zero) (ih hb)
      have hs := closed_typed (signature.universal_typed a) (context signature.types gamma)
      simp only [liftClosed, typeAt_rename] at hs
      simpa only [LogicalSignature.rules, liftClosed, HOL.propTy, inst0, typeAt_subst]
        using Typing.appElim hs bodyTyped
  | @eq gamma a left right ihLeft ihRight =>
      obtain ⟨function, right', functionEq, rightEq, rfl⟩ := apply?_eq_some.mp success
      obtain ⟨operator, left', operatorEq, leftEq, rfl⟩ := apply?_eq_some.mp functionEq
      cases Option.some.inj operatorEq
      have symbol := closed_typed (signature.equality_typed a) (context signature.types gamma)
      simp only [liftClosed, typeAt_rename] at symbol
      have first := Typing.appElim symbol (ihLeft leftEq)
      simp only [inst0, typeAt_subst] at first
      simpa only [LogicalSignature.rules, liftClosed, HOL.propTy, inst0, typeAt_subst]
        using Typing.appElim first (ihRight rightEq)
  | top | bot | and | or | not | ex => simp [represent] at success

/-- Successful representation carries both the formed context and typing. -/
theorem represent_judgment (signature : LogicalSignature Base Const)
    {gamma : HOL.Ctx Base} {type : HOL.Ty Base} (term : HOL.Term Const gamma type)
    {out : Tower.Tm gamma.length} (success : represent signature term = some out) :
    Judgment signature.rules (context signature.types gamma) out
      (typeAt signature.types gamma.length type) :=
  ⟨context_formed signature gamma, represent_typed signature term success⟩

/-- Renaming commutes exactly, including explicit unsupported results. -/
theorem represent_rename (signature : LogicalSignature Base Const)
    {gamma delta : HOL.Ctx Base} {type : HOL.Ty Base}
    (rho : HOL.Rename Base gamma delta) (raw : Ren gamma.length delta.length)
    (compatible : ∀ {a} (index : HOL.Var gamma a),
      variableIndex (rho index) = raw (variableIndex index))
    (term : HOL.Term Const gamma type) :
    represent signature (HOL.rename rho term) =
      (represent signature term).map (Presentation.rename raw) := by
  induction term generalizing delta with
  | var index => simp [HOL.rename, represent, compatible, Presentation.rename]
  | const symbol => simp [HOL.rename, represent]
  | app f a ihf iha =>
      simp only [HOL.rename, represent, ihf rho raw compatible, iha rho raw compatible]
      cases represent signature f <;> cases represent signature a <;> rfl
  | @lam a gamma b body ih =>
      have liftCompatible : ∀ {t} (index : HOL.Var (a :: gamma) t),
          variableIndex (HOL.Rename.lift rho index) = liftRen raw (variableIndex index) := by
        intro t index
        cases index with
        | vz => rfl
        | vs prior => exact congrArg Fin.succ (compatible prior)
      simp only [HOL.rename, represent, ih _ _ liftCompatible]
      cases represent signature body <;> rfl
  | imp p q ihp ihq =>
      simp only [HOL.rename, represent, ihp rho raw compatible, ihq rho raw compatible]
      cases represent signature p <;> cases represent signature q <;>
        simp [apply?, Presentation.rename]
  | @all a gamma body ih =>
      have liftCompatible : ∀ {t} (index : HOL.Var (a :: gamma) t),
          variableIndex (HOL.Rename.lift rho index) = liftRen raw (variableIndex index) := by
        intro t index
        cases index with
        | vz => rfl
        | vs prior => exact congrArg Fin.succ (compatible prior)
      simp only [HOL.rename, represent, ih _ _ liftCompatible]
      cases represent signature body <;> simp [apply?, Presentation.rename]
  | eq left right ihLeft ihRight =>
      simp only [HOL.rename, represent, ihLeft rho raw compatible, ihRight rho raw compatible]
      cases represent signature left <;> cases represent signature right <;>
        simp [apply?, Presentation.rename]
  | top | bot | and | or | not | ex => rfl

/-- Represented simultaneous substitution uses the existing raw substitution,
not a second binder calculus. Compatibility is only pointwise on variables. -/
theorem represent_subst (signature : LogicalSignature Base Const)
    {gamma delta : HOL.Ctx Base} {type : HOL.Ty Base}
    (sigma : HOL.Subst Const gamma delta) (raw : Sub Tower.Head gamma.length delta.length)
    (compatible : ∀ {a} (index : HOL.Var gamma a),
      represent signature (sigma index) = some (raw (variableIndex index)))
    (term : HOL.Term Const gamma type) :
    represent signature (HOL.subst sigma term) =
      (represent signature term).map (Presentation.subst raw) := by
  induction term generalizing delta with
  | var index => exact compatible index
  | const symbol => simp [HOL.subst, represent]
  | app f a ihf iha =>
      simp only [HOL.subst, represent, ihf sigma raw compatible, iha sigma raw compatible]
      cases represent signature f <;> cases represent signature a <;> rfl
  | @lam a gamma b body ih =>
      have liftCompatible : ∀ {t} (index : HOL.Var (a :: gamma) t),
          represent signature (HOL.Subst.lift sigma index) =
            some (liftSub raw (variableIndex index)) := by
        intro t index
        cases index with
        | vz => rfl
        | vs prior =>
            change represent signature (HOL.rename HOL.Rename.weaken (sigma prior)) = _
            rw [represent_rename signature HOL.Rename.weaken wk (fun _ => rfl), compatible prior]
            rfl
      simp only [HOL.subst, represent, ih _ _ liftCompatible]
      cases represent signature body <;> rfl
  | imp p q ihp ihq =>
      simp only [HOL.subst, represent, ihp sigma raw compatible, ihq sigma raw compatible]
      cases represent signature p <;> cases represent signature q <;>
        simp [apply?, Presentation.subst]
  | @all a gamma body ih =>
      have liftCompatible : ∀ {t} (index : HOL.Var (a :: gamma) t),
          represent signature (HOL.Subst.lift sigma index) =
            some (liftSub raw (variableIndex index)) := by
        intro t index
        cases index with
        | vz => rfl
        | vs prior =>
            change represent signature (HOL.rename HOL.Rename.weaken (sigma prior)) = _
            rw [represent_rename signature HOL.Rename.weaken wk (fun _ => rfl), compatible prior]
            rfl
      simp only [HOL.subst, represent, ih _ _ liftCompatible]
      cases represent signature body <;> simp [apply?, Presentation.subst]
  | eq left right ihLeft ihRight =>
      simp only [HOL.subst, represent, ihLeft sigma raw compatible, ihRight sigma raw compatible]
      cases represent signature left <;> cases represent signature right <;>
        simp [apply?, Presentation.subst]
  | top | bot | and | or | not | ex => rfl

/-- Weakening in the source is exactly weakening of the represented term.
This is a property of the representation, independent of any proof-family
extension that may later consume it. -/
theorem represent_weaken (signature : LogicalSignature Base Const)
    {gamma : HOL.Ctx Base} {type extra : HOL.Ty Base}
    (term : HOL.Term Const gamma type) :
    represent signature (HOL.weaken (σ := extra) term) =
      (represent signature term).map (Presentation.rename wk) :=
  represent_rename signature HOL.Rename.weaken wk (fun _ => rfl) term

/-- Implication representation is assembled solely from the declared source
operator and the representations of its arguments. -/
theorem represent_imp (signature : LogicalSignature Base Const)
    {gamma : HOL.Ctx Base} (left right : HOL.Formula Const gamma) :
    represent signature (.imp left right) = (do
      let leftCode ← represent signature left
      let rightCode ← represent signature right
      pure (.app (.app (liftClosed signature.implication) leftCode) rightCode)) := by
  simp only [represent]
  cases represent signature left <;> cases represent signature right <;> rfl

/-- Universal representation is the declared quantifier applied to the
represented lambda body. -/
theorem represent_all (signature : LogicalSignature Base Const)
    {gamma : HOL.Ctx Base} {type : HOL.Ty Base}
    (body : HOL.Formula Const (type :: gamma)) :
    represent signature (.all body) =
      (represent signature body).map
        (fun code => .app (liftClosed (signature.universal type)) (.lam code)) := by
  simp only [represent]
  cases represent signature body <;> rfl

/-- Instantiation in the source is native de Bruijn instantiation of the
represented body whenever the argument is representable. -/
theorem represent_instantiate (signature : LogicalSignature Base Const)
    {gamma : HOL.Ctx Base} {type argumentType : HOL.Ty Base}
    (term : HOL.Term Const gamma argumentType)
    (body : HOL.Term Const (argumentType :: gamma) type)
    {code : Tower.Tm gamma.length}
    (represented : represent signature term = some code) :
    represent signature (HOL.instantiate term body) =
      (represent signature body).map (inst0 code) := by
  apply represent_subst signature (HOL.Subst.single term) (subst0 code)
  intro found index
  cases index with
  | vz => exact represented
  | vs _ => rfl

/-- The two substitution routes yield the same represented term, while the
source's independently chosen Henkin model satisfies semantic substitution.
No semantic interpretation of arbitrary raw target terms is asserted. -/
theorem substitution_interface (signature : LogicalSignature Base Const)
    {gamma delta : HOL.Ctx Base} {type : HOL.Ty Base}
    (sigma : HOL.Subst Const gamma delta) (raw : Sub Tower.Head gamma.length delta.length)
    (compatible : ∀ {a} (index : HOL.Var gamma a),
      represent signature (sigma index) = some (raw (variableIndex index)))
    (term : HOL.Term Const gamma type) {out : Tower.Tm gamma.length}
    (success : represent signature term = some out)
    (model : HOL.HenkinModel.{u, v, w} Base Const)
    (valuation : HOL.HenkinModel.Valuation model delta) :
    represent signature (HOL.subst sigma term) = some (Presentation.subst raw out) ∧
      Typing signature.rules (context signature.types delta) (Presentation.subst raw out)
        (typeAt signature.types delta.length type) ∧
      model.denote (HOL.subst sigma term) valuation =
        model.denote term (HOL.Soundness.substVal model sigma valuation) := by
  have equation := represent_subst signature sigma raw compatible term
  rw [success] at equation
  exact ⟨equation, represent_typed signature _ equation,
    HOL.Soundness.denote_subst model sigma term valuation⟩

#print axioms equalityDeclarationType_formed
#print axioms represent_eq
#print axioms represent_typed
#print axioms represent_judgment
#print axioms represent_rename
#print axioms represent_subst
#print axioms represent_weaken
#print axioms represent_imp
#print axioms represent_all
#print axioms represent_instantiate
#print axioms substitution_interface

end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.FormationSensitiveHOLInterface
