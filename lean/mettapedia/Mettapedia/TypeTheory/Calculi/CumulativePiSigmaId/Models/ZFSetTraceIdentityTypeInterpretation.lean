import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Models.ZFSetTypeExpressionInterpretation
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Models.ZFSetTraceIdentityDeclaration

/-!
# The native identity declaration type denotes its constructed set code

Interpret the existing declaration syntax structurally, and compare it with
the independently constructed six-argument trace function type. The two
routes share actual set codes, not just isomorphic decoded types.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.ZFSetTraceIdentityTypeInterpretation

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation
open ZFSetTypeExpressionInterpretation
open Mettapedia.TypeTheory.UniverseLevel
open Mettapedia.TypeTheory.UniverseLevel.ZFSetInterpretation
open Mettapedia.Logic.HOL.Embedding
open ZFSetUniverseClosure (CofinalInaccessibles)
open ZFSetTraceProducts (tracePiSet traceApp)
open ZFSetTraceProofDecoding (truthCode)
open ZFSetTraceUniverseInterpretation
open ZFSetTraceIdentityDeclaration
open NativeIndexedFamilies.Intrinsic

universe u
variable {h : CofinalInaccessibles.{u}} {seed : ZFSet.{u}} {i j : Nat}

theorem path_code_agreement (a : Code h seed i) (x y : El a) :
    truthCode (x.1 = y.1) = (pathCode a x y).1 := by
  simp only [pathCode, proofCode]
  congr 1
  exact propext Subtype.ext_iff.symm

theorem motive_supported : supported identityMotiveType = true := by decide
theorem declaration_supported : supported identityEliminateType = true := by decide
theorem result_supported : supported identityEliminateResultType = true := by decide

theorem motive_interpretation (ground : ZFSet.{u}) (valuation : Nat → Nat)
    (constants : DeclName → ZFSet.{u})
    (a : Code h seed (valuation 0)) (x : El a) :
    interpret (interpretHead h seed ground valuation) constants identityMotiveType motive_supported
      (extend (extend Fin.elim0 a.1) x.1) = (motiveCode (valuation 1) a x).1 := by
  change tracePiSet a.1 (fun y => tracePiSet (truthCode (x.1 = y))
    (fun _ => universeSet h seed (valuation 1))) = _
  apply tracePiSet_eq_piCodeWithin
  intro y
  rw [path_code_agreement a x y]
  apply tracePiSet_eq_piCodeWithin
  intro q
  rfl

theorem result_interpretation (ground : ZFSet.{u}) (valuation : Nat → Nat)
    (constants : DeclName → ZFSet.{u})
    (a : Code h seed (valuation 0)) (x : El a)
    (p : El (motiveCode (valuation 1) a x))
    (d : El (motiveAt a x p x (reflValue a x))) :
    interpret (interpretHead h seed ground valuation) constants identityEliminateResultType result_supported
      (extend (extend (extend (extend Fin.elim0 a.1) x.1) p.1) d.1) =
        (resultCode a x p).1 := by
  change tracePiSet a.1 (fun y => tracePiSet (truthCode (x.1 = y))
    (fun q => traceApp (traceApp p.1 y) q)) = _
  apply tracePiSet_eq_piCodeWithin
  intro y
  rw [path_code_agreement a x y]
  apply tracePiSet_eq_piCodeWithin
  intro q
  exact (motiveAt_value a x p y q).symm

/-- Structural interpretation of the actual native declaration type yields
the independently constructed six-argument function code literally. -/
theorem declaration_interpretation (ground : ZFSet.{u}) (valuation : Nat → Nat)
    (constants : DeclName → ZFSet.{u}) :
    interpret (interpretHead h seed ground valuation) constants identityEliminateType declaration_supported
      Fin.elim0 = (declarationCode h seed (valuation 0) (valuation 1)).1 := by
  change tracePiSet (universeSet h seed (valuation 0)) _ = _
  apply tracePiSet_eq_piCodeWithin (Nat.le_max_left (valuation 0 + 1) (valuation 1 + 1))
    (universeCode h seed (valuation 0)) (pointFunctionCode (valuation 1))
  intro a
  change Code h seed (valuation 0) at a
  change tracePiSet a.1 _ = _
  apply tracePiSet_eq_piCodeWithin
  intro x
  change tracePiSet (interpret (interpretHead h seed ground valuation) constants
    identityMotiveType motive_supported (extend (extend Fin.elim0 a.1) x.1)) _ = _
  rw [motive_interpretation ground valuation constants a x]
  apply tracePiSet_eq_piCodeWithin
  intro p
  let body := fun d => interpret (interpretHead h seed ground valuation) constants
    identityEliminateResultType result_supported
      (extend (extend (extend (extend Fin.elim0 a.1) x.1) p.1) d)
  change tracePiSet (traceApp (traceApp p.1 x.1) ∅) body = _
  exact (congrArg (fun domain => tracePiSet domain body)
    (motiveAt_value a x p x (reflValue a x)).symm).trans
      (tracePiSet_eq_piCodeWithin (motive_below (valuation 0) (valuation 1))
        (motiveAt a x p x (reflValue a x)) (fun _ => resultCode a x p) body
          (fun d => result_interpretation ground valuation constants a x p d))

/-- The model value belongs to the interpretation of the source declaration
type. This conclusion uses the syntax/code comparison, not just its level. -/
theorem declaration_value_typed (ground : ZFSet.{u}) (valuation : Nat → Nat)
    (constants : DeclName → ZFSet.{u}) :
    (declarationValue h seed (valuation 0) (valuation 1)).1 ∈
      interpret (interpretHead h seed ground valuation) constants identityEliminateType
        declaration_supported Fin.elim0 := by
  rw [declaration_interpretation]
  exact (declarationValue h seed (valuation 0) (valuation 1)).2

/-- The declaration schema can be specialized in syntax or in the model's
valuation, with literal agreement of the resulting function codes. -/
theorem instantiated_declaration_interpretation (ground : ZFSet.{u})
    (valuation : Nat → Nat) (theta : Nat → LevelExpr) (constants : DeclName → ZFSet.{u}) :
    interpret (interpretHead h seed ground valuation) constants
      (RussellTarski.substLevelsTm theta identityEliminateType)
      ((supported_mapHead (RussellTarski.substLevelsHead theta) identityEliminateType).trans
        declaration_supported) Fin.elim0 =
      (declarationCode h seed ((theta 0).eval valuation) ((theta 1).eval valuation)).1 :=
  (interpret_substLevels h seed ground valuation theta constants identityEliminateType
    declaration_supported Fin.elim0).trans
      (declaration_interpretation ground (fun index => (theta index).eval valuation) constants)

/-- Interpret a fixed universe instance of the declared J by the constructed
six-argument set function. Other declarations retain the caller's values;
this does not identify different universe instances of the same name. -/
noncomputable def identityConstants (h : CofinalInaccessibles.{u}) (seed : ZFSet.{u})
    (i j : Nat) (constants : DeclName → ZFSet.{u}) : DeclName → ZFSet.{u} :=
  Function.update constants identityEliminateName (declarationValue h seed i j).1

theorem application_supported {n : Nat} (a x p d y q : Tower.Tm n)
    (ha : supported a = true) (hx : supported x = true) (hp : supported p = true)
    (hd : supported d = true) (hy : supported y = true) (hq : supported q = true) :
    supported (identityEliminateApp a x p d y q) = true := by
  simp only [identityEliminateApp, supported, ha, hx, hp, hd, hy, hq, Bool.and_self]

/-- A native application of the actual declared name computes to the
constructed eliminator on the values of its six supplied arguments. -/
theorem application_interpretation {n : Nat}
    (headValues : Tower.Head → ZFSet.{u}) (constants : DeclName → ZFSet.{u})
    (environment : Environment.{u} n) (A X P D Y Q : Tower.Tm n)
    (hA : supported A = true) (hX : supported X = true) (hP : supported P = true)
    (hD : supported D = true) (hY : supported Y = true) (hQ : supported Q = true)
    (a : Code h seed i) (x : El a) (p : El (motiveCode j a x))
    (d : El (motiveAt a x p x (reflValue a x))) (y : El a) (q : El (pathCode a x y))
    (atA : interpret headValues (identityConstants h seed i j constants) A hA environment = a.1)
    (atX : interpret headValues (identityConstants h seed i j constants) X hX environment = x.1)
    (atP : interpret headValues (identityConstants h seed i j constants) P hP environment = p.1)
    (atD : interpret headValues (identityConstants h seed i j constants) D hD environment = d.1)
    (atY : interpret headValues (identityConstants h seed i j constants) Y hY environment = y.1)
    (atQ : interpret headValues (identityConstants h seed i j constants) Q hQ environment = q.1) :
    interpret headValues (identityConstants h seed i j constants)
      (identityEliminateApp A X P D Y Q)
      (application_supported A X P D Y Q hA hX hP hD hY hQ) environment =
        (eliminate a x p d y q).1 := by
  simp only [identityEliminateApp, interpret]
  rw [atA, atX, atP, atD, atY, atQ]
  rw [identityConstants, Function.update_self]
  exact six_applications a x p d y q

/-- The very redex used by `IotaEvidence.identity` retains its meaning.
Premises interpret its actual arguments; no arbitrary product-code cast is
used to recover their domains. -/
theorem identity_iota_interpretation {n : Nat}
    (headValues : Tower.Head → ZFSet.{u}) (constants : DeclName → ZFSet.{u})
    (environment : Environment.{u} n) (A X P D : Tower.Tm n)
    (hA : supported A = true) (hX : supported X = true)
    (hP : supported P = true) (hD : supported D = true)
    (a : Code h seed i) (x : El a) (p : El (motiveCode j a x))
    (d : El (motiveAt a x p x (reflValue a x)))
    (atA : interpret headValues (identityConstants h seed i j constants) A hA environment = a.1)
    (atX : interpret headValues (identityConstants h seed i j constants) X hX environment = x.1)
    (atP : interpret headValues (identityConstants h seed i j constants) P hP environment = p.1)
    (atD : interpret headValues (identityConstants h seed i j constants) D hD environment = d.1) :
    interpret headValues (identityConstants h seed i j constants)
      (identityEliminateApp A X P D X (.refl X))
      (application_supported A X P D X (.refl X) hA hX hP hD hX hX) environment =
        interpret headValues (identityConstants h seed i j constants) D hD environment :=
  (application_interpretation headValues constants environment A X P D X (.refl X)
    hA hX hP hD hX hX a x p d x (reflValue a x) atA atX atP atD atX rfl).trans atD.symm

namespace Controls

open Mettapedia.TypeTheory.UniverseLevel.ZFSetInterpretation.Controls (twoCode)
open ZFSetTraceIdentityDeclaration.Controls (zeroPoint universeMotive universeMethod)

/-- The existing native J rule, with all four parameters supplied by an
environment. The method is a type code, not a proof token. -/
def universeRedex : Tower.Tm 4 :=
  identityEliminateApp (.var 3) (.var 2) (.var 1) (.var 0) (.var 2) (.refl (.var 2))

theorem universeRedex_supported : supported universeRedex = true := by decide

def universeRedex_iota : IotaEvidence 4 universeRedex (.var 0) :=
  .identity (.var 3) (.var 2) (.var 1) (.var 0)

noncomputable def universeEnvironment (h : CofinalInaccessibles.{u}) : Environment.{u} 4 :=
  extend (extend (extend (extend Fin.elim0 (twoCode h).1) (zeroPoint h).1)
    (universeMotive h).1) (universeMethod h).1

theorem universe_type_returned (h : CofinalInaccessibles.{u})
    (headValues : Tower.Head → ZFSet.{u}) (constants : DeclName → ZFSet.{u}) :
    interpret headValues (identityConstants h ∅ 0 1 constants)
      universeRedex universeRedex_supported (universeEnvironment h) = (twoCode h).1 :=
  identity_iota_interpretation headValues constants (universeEnvironment h)
    (.var 3) (.var 2) (.var 1) (.var 0) rfl rfl rfl rfl
    (twoCode h) (zeroPoint h) (universeMotive h) (universeMethod h) rfl rfl rfl rfl

/-- Replacing the computed type by the proof-irrelevant reflexivity value
does not preserve meaning. -/
theorem reflexivity_value_is_not_result (h : CofinalInaccessibles.{u})
    (headValues : Tower.Head → ZFSet.{u}) (constants : DeclName → ZFSet.{u}) :
    interpret headValues (identityConstants h ∅ 0 1 constants)
      universeRedex universeRedex_supported (universeEnvironment h) ≠ ∅ := by
  rw [universe_type_returned]
  intro empty
  have member : (∅ : ZFSet.{u}) ∈ (twoCode h).1 :=
    ZFSetDependentProducts.Controls.empty_mem_two
  rw [empty] at member
  exact ZFSet.notMem_empty _ member

end Controls

#print axioms motive_interpretation
#print axioms declaration_interpretation
#print axioms declaration_value_typed
#print axioms instantiated_declaration_interpretation
#print axioms application_interpretation
#print axioms identity_iota_interpretation
#print axioms Controls.universe_type_returned
#print axioms Controls.reflexivity_value_is_not_result

end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.ZFSetTraceIdentityTypeInterpretation
