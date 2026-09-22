import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.HOLLeibnizZFSetInterpretation

/-!
# An alternative native presentation of HOL equality

The existing declarations support predicate equality as a closed lambda
term built from universal quantification and implication. Its independent
formation-sensitive typing supplies an alternative logical signature. The
primitive-equality signature is unchanged, and no decoder, native identity
equation or new declaration is installed.

The retained source comparison and its Henkin/set interpretation justify
comparing these presentations. They do not by themselves provide a model
of arbitrary native terms or complete proof compilation in this signature.
-/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

set_option autoImplicit false


namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.FormationSensitiveHOLLeibnizInterface

open Presentation Presentation.Declaration Presentation.FormationSensitive
open FormationSensitiveHOLInterface Mettapedia.Logic HOL.UniformListInduction
open FormationSensitiveHOLUniformList (types rawAll rawImp)

abbrev rules := FormationSensitiveHOLUniformList.rules

def rawLeibniz {n : Nat} (type : HOL.Ty BaseSort) (x y : Tower.Tm n) : Tower.Tm n :=
  rawAll (.arr type .prop)
    (rawImp (.app (.var 0) (rename wk x)) (.app (.var 0) (rename wk y)))

@[simp] theorem rawLeibniz_rename {n m : Nat} (rho : Ren n m)
    (type : HOL.Ty BaseSort) (x y : Tower.Tm n) :
    rename rho (rawLeibniz type x y) = rawLeibniz type (rename rho x) (rename rho y) := by
  simp [rawLeibniz, rawAll, rawImp, rename, rename_comp, liftRen, wk]

@[simp] theorem rawLeibniz_subst {n m : Nat} (sigma : Sub Tower.Head n m)
    (type : HOL.Ty BaseSort) (x y : Tower.Tm n) :
    subst sigma (rawLeibniz type x y) = rawLeibniz type (subst sigma x) (subst sigma y) := by
  simp [rawLeibniz, rawAll, rawImp, subst, subst_rename, rename_subst, liftSub, wk]

def sourceEquality (type : HOL.Ty BaseSort) : Expr [] (.arr type (.arr type .prop)) :=
  .lam (.lam (HOLLeibnizProofComparison.Source.leibniz (.var (.vs .vz)) (.var .vz)))

def equality (type : HOL.Ty BaseSort) : Tower.Tm 0 :=
  .lam (.lam (rawLeibniz type (.var (Fin.succ 0)) (.var 0)))

theorem sourceEquality_represented (type : HOL.Ty BaseSort) :
    represent FormationSensitiveHOLUniformList.signature (sourceEquality type) =
      some (equality type) := rfl

/-- This typing certificate is constructed before the alternative signature.
Its source term contains only lambda, universal, implication and variables. -/
theorem equality_typed (type : HOL.Ty BaseSort) :
    Typing rules .nil (equality type) (typeAt types 0 (.arr type (.arr type .prop))) :=
  represent_typed FormationSensitiveHOLUniformList.signature (sourceEquality type)
    (sourceEquality_represented type)

def signature : LogicalSignature BaseSort Symbol :=
  { FormationSensitiveHOLUniformList.signature with
    equality := equality
    equality_typed := equality_typed }

theorem equality_typed_at (type : HOL.Ty BaseSort) {n : Nat} (context : Tower.Ctx n) :
    Typing rules context (liftClosed (equality type))
      (typeAt types n (.arr type (.arr type .prop))) := by
  simpa only [typeAt_rename, liftClosed] using closed_typed (equality_typed type) context

theorem lifted_equality {n : Nat} (type : HOL.Ty BaseSort) :
    (liftClosed (equality type) : Tower.Tm n) =
      .lam (.lam (rawLeibniz type (.var (Fin.succ 0)) (.var 0))) := by
  simp only [equality, liftClosed, rename, rawLeibniz_rename,
    liftRen, Fin.cases_zero, Fin.cases_succ]

/-- Two ordinary native beta steps expose the predicate formula. No new
equation is installed for equality or for the proof-family decoder. -/
theorem equality_application_conversion {n : Nat} (type : HOL.Ty BaseSort)
    (x y : Tower.Tm n) :
    Conv rules.headEq (.app (.app (liftClosed (equality type)) x) y)
      (rawLeibniz type x y) rules.computation := by
  rw [lifted_equality]
  have first : Conv rules.headEq
      (.app (.lam (.lam (rawLeibniz type (.var (Fin.succ 0)) (.var 0)))) x)
      (.lam (rawLeibniz type (rename wk x) (.var 0))) rules.computation := by
    simpa only [inst0, subst, rawLeibniz_subst, liftSub, subst0,
      Fin.cases_succ, Fin.cases_zero] using
      (Relation.EqvGen.rel _ _ (Step.betaPi (root := rules.computation)
        (headEq := rules.headEq)
        (.lam (rawLeibniz type (.var (Fin.succ 0)) (.var 0))) x))
  have second : Conv rules.headEq
      (.app (.lam (rawLeibniz type (rename wk x) (.var 0))) y)
      (rawLeibniz type x y) rules.computation := by
    have weakened : subst (subst0 y) (rename wk x) = x := inst0_rename_wk y x
    simpa only [inst0, rawLeibniz_subst, subst, subst0, Fin.cases_zero,
      weakened] using
      (Relation.EqvGen.rel _ _ (Step.betaPi (root := rules.computation)
        (headEq := rules.headEq) (rawLeibniz type (rename wk x) (.var 0)) y))
  exact .trans _ _ _ (Conv.congApp first (.refl _)) second

theorem weakened_represented {gamma : HOL.Ctx BaseSort} {a type : HOL.Ty BaseSort}
    {term : Expr gamma type} {code : Tower.Tm gamma.length}
    (represented : represent signature term = some code) :
    represent signature (HOL.weaken (σ := a) term) = some (rename wk code) := by
  have commutes := represent_rename signature
    (HOL.Rename.weaken : HOL.Rename BaseSort gamma (a :: gamma)) wk (fun _ => rfl) term
  rw [represented] at commutes
  exact commutes

theorem leibniz_represented {gamma : HOL.Ctx BaseSort} {type : HOL.Ty BaseSort}
    {x y : Expr gamma type} {xc yc : Tower.Tm gamma.length}
    (hx : represent signature x = some xc) (hy : represent signature y = some yc) :
    represent signature (HOLLeibnizProofComparison.Source.leibniz x y) =
      some (rawLeibniz type xc yc) := by
  have xw := weakened_represented (a := .arr type .prop) hx
  have yw := weakened_represented (a := .arr type .prop) hy
  simp only [HOLLeibnizProofComparison.Source.leibniz, represent, xw, yw]
  rfl

/-- Both displayed sides are independently formed represented propositions.
The conversion between them is computation, not an assumed comparison law. -/
theorem represented_equality_conversion {gamma : HOL.Ctx BaseSort} {type : HOL.Ty BaseSort}
    {x y : Expr gamma type} {xc yc : Tower.Tm gamma.length}
    (hx : represent signature x = some xc) (hy : represent signature y = some yc) :
    ∃ code, represent signature (.eq x y) = some code ∧
      Judgment rules (context types gamma) code (typeAt types gamma.length .prop) ∧
      Judgment rules (context types gamma) (rawLeibniz type xc yc)
        (typeAt types gamma.length .prop) ∧
      Conv rules.headEq code (rawLeibniz type xc yc) rules.computation := by
  have equalityRep := represent_eq signature x y hx hy
  exact ⟨_, equalityRep, represent_judgment signature (.eq x y) equalityRep,
    represent_judgment signature _ (leibniz_represented hx hy),
    equality_application_conversion type xc yc⟩

/-- The alternative uses the same proven capture-avoiding substitution
interface; operands may themselves contain represented equality. -/
theorem representation_substitution {gamma delta : HOL.Ctx BaseSort} {type : HOL.Ty BaseSort}
    (sigma : HOL.Subst Symbol gamma delta) (raw : Sub Tower.Head gamma.length delta.length)
    (compatible : ∀ {a} (index : HOL.Var gamma a),
      represent signature (sigma index) = some (raw (variableIndex index)))
    (term : Expr gamma type) {code : Tower.Tm gamma.length}
    (represented : represent signature term = some code) :
    represent signature (HOL.subst sigma term) = some (subst raw code) := by
  rw [represent_subst signature sigma raw compatible, represented]
  rfl

namespace Decoded

open FormationSensitiveHOLProofFamily (proof implicationFamily)

theorem include_conversion {n : Nat} {left right : Tower.Tm n}
    (converted : Conv rules.headEq left right rules.computation) :
    Conv FormationSensitiveHOLProofFamily.rules.headEq left right
      FormationSensitiveHOLProofFamily.rules.computation := by
  have lifted := converted.mapHead (targetEq := FormationSensitiveHOLProofFamily.rules.headEq)
    (fun head => head) FormationSensitiveHOLProofFamily.sourceMorphism.headEq
    FormationSensitiveHOLProofFamily.sourceMorphism.computation
  simpa only [Tm.mapHead_id] using lifted

/-- The existing two decoder equations expose predicate transport. Equality
adds only two lambda applications before those equations; it adds no root. -/
theorem equality_proof_conversion {n : Nat} (type : HOL.Ty BaseSort)
    (x y : Tower.Tm n) :
    Conv FormationSensitiveHOLProofFamily.rules.headEq
      (proof (.app (.app (liftClosed (equality type)) x) y))
      (.pi (typeAt types n (.arr type .prop))
        (implicationFamily (.app (.var 0) (rename wk x))
          (.app (.var 0) (rename wk y))))
      FormationSensitiveHOLProofFamily.rules.computation := by
  have equalityBeta := Conv.congApp (.refl (.const FormationSensitiveHOLProofFamily.proofName))
    (include_conversion (equality_application_conversion type x y))
  have universal := FormationSensitiveHOLProofFamily.rawAll_conversion (.arr type .prop)
    (rawImp (.app (.var 0) (rename wk x)) (.app (.var 0) (rename wk y)))
  have implication := Conv.congPi (.refl (typeAt types n (.arr type .prop)))
    (FormationSensitiveHOLProofFamily.implication_conversion
      (.app (.var 0) (rename wk x)) (.app (.var 0) (rename wk y)))
  exact .trans _ _ _ equalityBeta (.trans _ _ _ universal implication)

end Decoded

#print axioms equality_typed
#print axioms signature
#print axioms rawLeibniz_subst
#print axioms equality_application_conversion
#print axioms leibniz_represented
#print axioms represented_equality_conversion
#print axioms representation_substitution
#print axioms Decoded.equality_proof_conversion

end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.FormationSensitiveHOLLeibnizInterface
