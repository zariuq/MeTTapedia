import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.HostedDefinitions.ControlProtocol

/-! # Composition of the existing scoped contexts and their literal stack encoding -/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.ContextOperations

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation
open SourceLanguage.Elaboration
open ComputationSyntax

/-- Fill the first context's hole with the second context, retaining all
intrinsic ambient indices. This uses the existing Context datatype. -/
def append {Head : Type} : {n m p : Nat} → Context Head n m → Context Head m p → Context Head n p
  | _, _, _, .hole, later => later
  | _, _, _, .piDom inner codomain, later => .piDom (append inner later) codomain
  | _, _, _, .piCod domain inner, later => .piCod domain (append inner later)
  | _, _, _, .sigmaDom inner codomain, later => .sigmaDom (append inner later) codomain
  | _, _, _, .sigmaCod domain inner, later => .sigmaCod domain (append inner later)
  | _, _, _, .idType inner left right, later => .idType (append inner later) left right
  | _, _, _, .idLeft carrier inner right, later => .idLeft carrier (append inner later) right
  | _, _, _, .idRight carrier left inner, later => .idRight carrier left (append inner later)
  | _, _, _, .lam inner, later => .lam (append inner later)
  | _, _, _, .appFun inner argument, later => .appFun (append inner later) argument
  | _, _, _, .appArg function inner, later => .appArg function (append inner later)
  | _, _, _, .pairFst inner second, later => .pairFst (append inner later) second
  | _, _, _, .pairSnd first inner, later => .pairSnd first (append inner later)
  | _, _, _, .fst inner, later => .fst (append inner later)
  | _, _, _, .snd inner, later => .snd (append inner later)
  | _, _, _, .refl inner, later => .refl (append inner later)

theorem plug_append {Head : Type} {n m p : Nat} (first : Context Head n m) (second : Context Head m p)
    (term : Tm Head p) : (append first second).plug term = first.plug (second.plug term) := by
  induction first <;> simp_all only [append, Context.plug]

theorem code_append {n m p : Nat} (first : Context Tower.Head n m) (second : Context Tower.Head m p)
    (rest : MClosed) : contextCode (append first second) rest = contextCode second (contextCode first rest) := by
  induction first generalizing rest <;> simp_all only [append, contextCode]

theorem append_hole {Head : Type} {n m : Nat} (context : Context Head n m) : append context .hole = context := by
  induction context <;> simp_all only [append]

theorem append_assoc {Head : Type} {n m p q : Nat} (first : Context Head n m)
    (second : Context Head m p) (third : Context Head p q) :
    append (append first second) third = append first (append second third) := by
  induction first <;> simp_all only [append]

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.ContextOperations
