import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.FormationSensitiveHOLLeibnizInterface

/-!
# Syntactic expansion of primitive equality into Leibniz equality

The expansion is independent of any semantic model.  It replaces primitive
HOL equality by the formed Leibniz formula and leaves every other constructor
structural.  Its representation theorem relates the established primitive and
Leibniz native encodings without importing either operational preservation or
a particular denotational semantics.
-/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

set_option autoImplicit false


namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOLLeibnizRepresentationSemantics

open Mettapedia.Logic HOL.UniformListInduction
open Presentation FormationSensitiveHOLInterface

namespace Old
abbrev signature := FormationSensitiveHOLUniformList.signature
end Old
namespace New
abbrev signature := FormationSensitiveHOLLeibnizInterface.signature
end New

def equalityAt (gamma : HOL.Ctx BaseSort) (type : HOL.Ty BaseSort) :
    Expr gamma (.arr type (.arr type .prop)) :=
  HOL.rename (fun {a} (index : HOL.Var [] a) => nomatch index)
    (FormationSensitiveHOLLeibnizInterface.sourceEquality type)

def expand : {gamma : HOL.Ctx BaseSort} → {type : HOL.Ty BaseSort} →
    Expr gamma type → Expr gamma type
  | _, _, .var index => .var index
  | _, _, .const symbol => .const symbol
  | _, _, .app f x => .app (expand f) (expand x)
  | _, _, .lam body => .lam (expand body)
  | _, _, .top => .top
  | _, _, .bot => .bot
  | _, _, .and p q => .and (expand p) (expand q)
  | _, _, .or p q => .or (expand p) (expand q)
  | _, _, .imp p q => .imp (expand p) (expand q)
  | _, _, .not p => .not (expand p)
  | _, _, .all p => .all (expand p)
  | _, _, .ex p => .ex (expand p)
  | gamma, _, @HOL.Term.eq _ _ _ type x y =>
      .app (.app (equalityAt gamma type) (expand x)) (expand y)

theorem equalityAt_represented (gamma : HOL.Ctx BaseSort) (type : HOL.Ty BaseSort) :
    represent Old.signature (equalityAt gamma type) =
      some (liftClosed (FormationSensitiveHOLLeibnizInterface.equality type)) := by
  rw [equalityAt, represent_rename Old.signature _ Fin.elim0
    (fun {a} (index : HOL.Var [] a) => nomatch index),
    FormationSensitiveHOLLeibnizInterface.sourceEquality_represented]
  rfl

theorem representation_expand {gamma : HOL.Ctx BaseSort} {type : HOL.Ty BaseSort}
    (term : Expr gamma type) :
    represent Old.signature (expand term) = represent New.signature term := by
  induction term with
  | var | const | top | bot | «and» | «or» | «not» | ex => rfl
  | app f x ihf ihx => simp only [expand, represent, ihf, ihx]
  | lam body ih => simp only [expand, represent, ih]
  | imp p q ihp ihq => simp only [expand, represent, ihp, ihq]; rfl
  | all p ih => simp only [expand, represent, ih]; rfl
  | eq x y ihx ihy =>
      simp only [expand, represent, equalityAt_represented, ihx, ihy]
      rfl

#print axioms equalityAt_represented
#print axioms representation_expand

end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOLLeibnizRepresentationSemantics
