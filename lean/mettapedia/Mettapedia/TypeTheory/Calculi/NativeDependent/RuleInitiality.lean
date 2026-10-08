import Mettapedia.TypeTheory.Calculi.NativeDependent.PresheafInterpretation
import Mettapedia.TypeTheory.JudgmentDerivation

/-!
# The native quantifier proof grammar as an initial rule algebra

The indexed signature is written independently from the generated proof
terms. Their equivalence retains the primitive declaration and each rule
node. The actual native presheaf interpretation is a model of these local
rules, and is the unique rule homomorphism from the proof grammar.

This is initiality for the stated declaration/substitution/Pi-introduction/
application/Sigma-pair rules. It is not classifying initiality for arbitrary
context comprehension, nor does it identify proof trees before computation.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.NativeDependent.RuleInitiality

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open Mettapedia.TypeTheory.JudgmentDerivation
open Mettapedia.TypeTheory.DisplayedPresheafTransport
open Mettapedia.TypeTheory.DisplayedPresheafComprehension
open Mettapedia.TypeTheory.DisplayedPresheafPi
open ObjectInterpretation PresheafInterpretation

universe u v
variable {Constant Predicate : Type u}
variable (Declaration : (n : Nat) → Formula Constant Predicate n → Type u)

abbrev Judgment := Σ n : Nat, Formula Constant Predicate n

/-- A rule records its scoped conclusion and names its single proof
premise; a declared primitive has no premise. -/
inductive Rule : (n : Nat) → Formula Constant Predicate n → Type u where
  | declaration {n : Nat} {formula : Formula Constant Predicate n}
      (name : Declaration n formula) : Rule n formula
  | substitute {n m : Nat} (formula : Formula Constant Predicate m)
      (replacements : ObjectSubstitution Constant n m) :
      Rule n (.substitute formula replacements)
  | lam {n : Nat} (body : Formula Constant Predicate (n + 1)) : Rule n (.pi body)
  | app {n : Nat} (body : Formula Constant Predicate (n + 1)) (argument : ObjectTerm Constant n) :
      Rule n (.substitute body (ObjectSubstitution.instantiate argument))
  | pair {n : Nat} (body : Formula Constant Predicate (n + 1)) (first : ObjectTerm Constant n) :
      Rule n (.sigma body)

/-- The actual premise position is retained even for unary rules. -/
def Premise : {n : Nat} → {formula : Formula Constant Predicate n} → Rule Declaration n formula → Type u
  | _, _, .declaration _ => PEmpty
  | _, _, .substitute _ _ => PUnit
  | _, _, .lam _ => PUnit
  | _, _, .app _ _ => PUnit
  | _, _, .pair _ _ => PUnit

def hypothesis : {n : Nat} → {formula : Formula Constant Predicate n} →
    (rule : Rule Declaration n formula) → Premise Declaration rule → Judgment (Constant := Constant) (Predicate := Predicate)
  | _, _, .declaration _, position => PEmpty.elim position
  | _, _, .substitute formula _, _ => ⟨_, formula⟩
  | _, _, .lam body, _ => ⟨_, body⟩
  | _, _, .app body _, _ => ⟨_, .pi body⟩
  | _, _, .pair body first, _ => ⟨_, .substitute body (ObjectSubstitution.instantiate first)⟩

def signature : Signature.{u} where
  Judgment := Judgment (Constant := Constant) (Predicate := Predicate)
  Rule judgment := Rule Declaration judgment.1 judgment.2
  Premise rule := Premise Declaration rule
  hypothesis rule position := hypothesis Declaration rule position

/-- The independently authored proof grammar is a nontrivial rule model. -/
def syntaxAlgebra : Algebra.{u, u} (signature Declaration) where
  Carrier judgment := Proof Declaration judgment.1 judgment.2
  conclude := by
    rintro ⟨n, formula⟩ rule premises
    change Rule Declaration n formula at rule
    cases rule with
    | declaration name => exact .declaration name
    | substitute _ replacements => exact .substitute (premises PUnit.unit) replacements
    | lam _ => exact .lam (premises PUnit.unit)
    | app _ argument => exact .app (premises PUnit.unit) argument
    | pair _ first => exact .pair first (premises PUnit.unit)

/-- Encode the original source proof, retaining its literal declaration
and node structure, into the generic indexed derivation grammar. -/
def encode {n : Nat} {formula : Formula Constant Predicate n} :
    Proof Declaration n formula → Derivation (signature Declaration) ⟨n, formula⟩
  | .declaration name => .node (.declaration name) (fun position => PEmpty.elim position)
  | .substitute body replacements => .node (.substitute _ replacements) (fun _ => encode body)
  | .lam body => .node (.lam _) (fun _ => encode body)
  | .app function argument => .node (.app _ argument) (fun _ => encode function)
  | .pair first second => .node (.pair _ first) (fun _ => encode second)

def decode {n : Nat} {formula : Formula Constant Predicate n}
    (tree : Derivation (signature Declaration) ⟨n, formula⟩) : Proof Declaration n formula :=
  interpret (syntaxAlgebra Declaration) tree

@[simp] theorem decode_encode {n : Nat} {formula : Formula Constant Predicate n}
    (term : Proof Declaration n formula) : decode Declaration (encode Declaration term) = term := by
  induction term with
  | declaration name => rfl
  | substitute _ replacements ih => exact congrArg (fun body => Proof.substitute body replacements) ih
  | lam _ ih => exact congrArg Proof.lam ih
  | app _ argument ih => exact congrArg (fun function => Proof.app function argument) ih
  | pair first _ ih => exact congrArg (Proof.pair first) ih

def encodeHom : Hom (syntaxAlgebra Declaration) (generated (signature Declaration)) where
  map term := encode Declaration term
  map_conclude := by
    rintro ⟨n, formula⟩ rule premises
    change Rule Declaration n formula at rule
    cases rule <;> apply congrArg (Derivation.node _) <;> funext position
    · exact PEmpty.elim position
    · cases position; rfl
    · cases position; rfl
    · cases position; rfl
    · cases position; rfl

@[simp] theorem encode_decode {n : Nat} {formula : Formula Constant Predicate n}
    (tree : Derivation (signature Declaration) ⟨n, formula⟩) :
    encode Declaration (decode Declaration tree) = tree := by
  have canonical := interpretation_unique (generated (signature Declaration))
    (Hom.comp (interpretation (syntaxAlgebra Declaration)) (encodeHom Declaration))
  have identity := interpretation_unique (generated (signature Declaration))
    (Hom.identity (generated (signature Declaration)))
  exact congrArg (fun morphism : Hom (generated (signature Declaration))
    (generated (signature Declaration)) => morphism.map tree) (canonical.trans identity.symm)

/-- This equivalence compares two independently declared syntactic objects. -/
def proofEquiv {n : Nat} {formula : Formula Constant Predicate n} :
    Proof Declaration n formula ≃ Derivation (signature Declaration) ⟨n, formula⟩ where
  toFun := encode Declaration
  invFun := decode Declaration
  left_inv := decode_encode Declaration
  right_inv := encode_decode Declaration

/-- Any local-rule model has an interpreter from the authored proof grammar. -/
def syntaxInterpretation (A : Algebra.{u, v} (signature Declaration)) :
    Hom (syntaxAlgebra Declaration) A :=
  Hom.comp (encodeHom Declaration) (interpretation A)

set_option backward.isDefEq.respectTransparency false in
theorem syntaxInterpretation_unique (A : Algebra.{u, v} (signature Declaration))
    (f : Hom (syntaxAlgebra Declaration) A) : f = syntaxInterpretation Declaration A := by
  apply Hom.ext
  intro judgment value
  have unique := interpretation_unique A
    (Hom.comp (interpretation (syntaxAlgebra Declaration)) f)
  have atValue := congrArg (fun morphism : Hom (generated (signature Declaration)) A =>
    morphism.map (encode Declaration value)) unique
  change f.map (decode Declaration (encode Declaration value)) =
    interpret A (encode Declaration value) at atValue
  rw [decode_encode] at atValue
  exact atValue

/-- The original independently authored proof grammar is initial for these
actual local-rule models. No semantic interpretation is used to define it. -/
def syntaxIsInitial : IsInitial (syntaxAlgebra Declaration) :=
  IsInitial.ofUniqueHom (syntaxInterpretation Declaration)
    (fun A f => syntaxInterpretation_unique Declaration A f)

variable {C : Type u} [Category.{u} C]
variable (D : Cᵒᵖ ⥤ Type u) (constants : Constant → D.sections)
variable (predicates : Predicate → DisplayedFamily.{u, u, u, u} D)
variable (declarations : ∀ {n : Nat} {formula : Formula Constant Predicate n},
  Declaration n formula → (family D constants predicates formula).sections)

/-- The native model supplies only genuine local operations for each rule. -/
noncomputable def nativeAlgebra : Algebra.{u, u} (signature Declaration) where
  Carrier judgment := (family D constants predicates judgment.2).sections
  conclude := by
    rintro ⟨n, formula⟩ rule premises
    change Rule Declaration n formula at rule
    cases rule with
    | declaration name => exact declarations name
    | substitute _ replacements => exact reindexDisplayedSection (substitution D constants replacements) _ (premises PUnit.unit)
    | lam _ => exact lamDisplayed (premises PUnit.unit)
    | app body argument => exact application D constants predicates body (premises PUnit.unit) argument
    | pair body first => exact pairing D constants predicates body first (premises PUnit.unit)

/-- The constructed native interpreter preserves the individual rules. -/
noncomputable def nativeHom :
    Hom (syntaxAlgebra Declaration) (nativeAlgebra Declaration D constants predicates declarations) where
  map term := proof D constants predicates declarations term
  map_conclude := by
    rintro ⟨n, formula⟩ rule premises
    change Rule Declaration n formula at rule
    cases rule <;> rfl

/-- Generated-rule interpretation computes the same actual native value
as the independently constructed structural proof interpreter. -/
theorem native_interpreter_agreement {n : Nat} {formula : Formula Constant Predicate n}
    (term : Proof Declaration n formula) :
    interpret (nativeAlgebra Declaration D constants predicates declarations)
      (encode Declaration term) = proof D constants predicates declarations term := by
  have calculation := interpret_naturality (nativeHom Declaration D constants predicates declarations)
    (encode Declaration term)
  change proof D constants predicates declarations (decode Declaration (encode Declaration term)) =
    interpret (nativeAlgebra Declaration D constants predicates declarations)
      (encode Declaration term) at calculation
  rw [decode_encode] at calculation
  exact calculation.symm

end Mettapedia.TypeTheory.Calculi.NativeDependent.RuleInitiality
