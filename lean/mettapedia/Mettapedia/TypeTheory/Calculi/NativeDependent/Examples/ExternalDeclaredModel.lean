import Mettapedia.TypeTheory.Calculi.NativeDependent.ExternalEvidenceExtraction
import Mettapedia.TypeTheory.Calculi.NativeDependent.Examples.ExternalHeaderControls

/-!
# Actual model realization of dependent primitive declarations

The independently authored profile declares a scalar, a family indexed by a
function, a family over a complete dependent pair, and a supplied section of
the full pair motive. These primitive data determine real parameter telescopes
and a model realization whose header/result equations are derived here.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.NativeDependent.External.DeclaredModel

open Mettapedia.GSLT.Core.ContextualLadder
open Mettapedia.TypeTheory.ContextualModelTelescopes
open Mettapedia.TypeTheory.ContextualSumComprehension
open Mettapedia.TypeTheory.ContextualTypeOperations
open Mettapedia.TypeTheory.ContextualPiEta

universe c s t m

variable {C : CwfWithTerminal.{c, s, t, m}}

def functionDomain (products : PiOperations C.toCwf) (scalar : C.toCwf.Ty C.empty) :
    C.toCwf.Ty C.empty :=
  products.pi scalar (C.toCwf.tySub scalar (C.toEmpty (C.toCwf.ext C.empty scalar)))

/-- Primitive data over the actual declared parameter contexts. -/
structure Declarations (products : PiOperations C.toCwf) (sums : StableSums C.toCwf) where
  scalar : C.toCwf.Ty C.empty
  fibre : C.toCwf.Ty (C.toCwf.ext C.empty (functionDomain products scalar))
  motive : C.toCwf.Ty (C.toCwf.ext C.empty (sums.operations.sigma (functionDomain products scalar) fibre))
  branch : C.toCwf.Tm (tupleContext (functionDomain products scalar) fibre)
    (C.toCwf.tySub motive (pack sums (functionDomain products scalar) fibre))

namespace Declarations

variable {products : PiOperations C.toCwf} {sums : StableSums C.toCwf}
  (declarations : Declarations products sums)

abbrev functionContext : Context C 1 := (Context.nil C).snoc (functionDomain products declarations.scalar)

abbrev pairContext : Context C 1 :=
  (Context.nil C).snoc (sums.operations.sigma (functionDomain products declarations.scalar) declarations.fibre)

abbrev componentContext : Context C 2 := declarations.functionContext.snoc declarations.fibre

def model : ModelData Controls.symbols C where
  products := products
  sums := sums
  typeParameters
    | .scalar => Context.nil C
    | .fibre => declarations.functionContext
    | .pairMotive => declarations.pairContext
  typeFamily
    | .scalar => declarations.scalar
    | .fibre => declarations.fibre
    | .pairMotive => declarations.motive
  termParameters := fun _ => declarations.componentContext
  termType := fun _ => C.toCwf.tySub declarations.motive (pack sums (functionDomain products declarations.scalar) declarations.fibre)
  termValue := fun _ => declarations.branch

theorem scalar_read {n : Nat} (Γ : Context C n) :
    declarations.model.evaluateType Γ (Controls.scalar n) =
      some (C.toCwf.tySub declarations.scalar (C.toEmpty Γ.1)) :=
  declarations.model.evaluate_family Γ .scalar Fin.elim0 (C.toEmpty Γ.1) (fun index => Fin.elim0 index)

theorem scalar_empty_read : declarations.model.evaluateType (Context.nil C) (Controls.scalar 0) =
    some declarations.scalar := by
  have evaluated := declarations.scalar_read (Context.nil C)
  rw [← C.toEmpty_unique C.empty (C.toCwf.idS C.empty), C.toCwf.tySub_id] at evaluated
  exact evaluated

theorem domain_empty_read : declarations.model.evaluateType (Context.nil C) (Controls.domain 0) =
    some (functionDomain products declarations.scalar) :=
  declarations.model.evaluate_pi (Context.nil C) (Controls.scalar 0) (Controls.scalar 1)
    declarations.scalar (C.toCwf.tySub declarations.scalar (C.toEmpty (C.toCwf.ext C.empty declarations.scalar)))
    declarations.scalar_empty_read (declarations.scalar_read ((Context.nil C).snoc declarations.scalar))

theorem function_header_read : declarations.model.evaluateContext (.snoc .nil (Controls.domain 0)) =
    some declarations.functionContext :=
  declarations.model.evaluateContext_snoc .nil (Controls.domain 0) (Context.nil C) _ rfl declarations.domain_empty_read

theorem fibre_read : declarations.model.evaluateType declarations.functionContext (Controls.body 0) =
    some declarations.fibre := by
  have arguments : (fun _ : Fin 1 => TermExpr.var (S := Controls.symbols) 0) = TermExpr.var := by
    funext index
    exact congrArg TermExpr.var (Subsingleton.elim _ _)
  have evaluated := declarations.model.evaluate_family declarations.functionContext .fibre
    TermExpr.var (C.toCwf.idS declarations.functionContext.1)
    ((declarations.model.evaluateSubstitution_eq_some_iff declarations.functionContext
      declarations.functionContext TermExpr.var _).mp
        (declarations.model.evaluateSubstitution_identity declarations.functionContext))
  change declarations.model.evaluateType declarations.functionContext
    (.family (S := Controls.symbols) .fibre (fun _ : Fin 1 => TermExpr.var 0)) = some declarations.fibre
  rw [arguments]
  have familyRead : declarations.model.familyAt .fibre
      (C.toCwf.idS declarations.functionContext.1) = declarations.fibre :=
    C.toCwf.tySub_id declarations.fibre
  exact evaluated.trans (congrArg some familyRead)

theorem sum_empty_read : declarations.model.evaluateType (Context.nil C) (Controls.sum 0) =
    some (sums.operations.sigma (functionDomain products declarations.scalar) declarations.fibre) :=
  declarations.model.evaluate_sigma (Context.nil C) (Controls.domain 0) (Controls.body 0)
    (functionDomain products declarations.scalar) declarations.fibre declarations.domain_empty_read declarations.fibre_read

theorem pair_header_read : declarations.model.evaluateContext (.snoc .nil (Controls.sum 0)) =
    some declarations.pairContext :=
  declarations.model.evaluateContext_snoc .nil (Controls.sum 0) (Context.nil C) _ rfl declarations.sum_empty_read

theorem motive_read : declarations.model.evaluateType declarations.pairContext (Controls.motive 0) =
    some declarations.motive := by
  have arguments : (fun _ : Fin 1 => TermExpr.var (S := Controls.symbols) 0) = TermExpr.var := by
    funext index
    exact congrArg TermExpr.var (Subsingleton.elim _ _)
  have evaluated := declarations.model.evaluate_family declarations.pairContext .pairMotive
    TermExpr.var (C.toCwf.idS declarations.pairContext.1)
    ((declarations.model.evaluateSubstitution_eq_some_iff declarations.pairContext
      declarations.pairContext TermExpr.var _).mp
        (declarations.model.evaluateSubstitution_identity declarations.pairContext))
  change declarations.model.evaluateType declarations.pairContext
    (.family (S := Controls.symbols) .pairMotive (fun _ : Fin 1 => TermExpr.var 0)) = some declarations.motive
  rw [arguments]
  have familyRead : declarations.model.familyAt .pairMotive
      (C.toCwf.idS declarations.pairContext.1) = declarations.motive :=
    C.toCwf.tySub_id declarations.motive
  exact evaluated.trans (congrArg some familyRead)

theorem component_header_read : declarations.model.evaluateContext (Controls.componentContext 0 .nil) =
    some declarations.componentContext :=
  declarations.model.evaluateContext_snoc (.snoc .nil (Controls.domain 0)) (Controls.body 0)
    declarations.functionContext declarations.fibre declarations.function_header_read declarations.fibre_read

theorem branch_result_read (stable : StrictPiSubstitution products) :
    declarations.model.evaluateType declarations.componentContext (Controls.signature.termResult .fullBranch) =
      some (C.toCwf.tySub declarations.motive (pack sums (functionDomain products declarations.scalar) declarations.fibre)) :=
  declarations.model.evaluateType_substitute stable (Controls.motive 0) declarations.componentContext
    declarations.pairContext (packSubstitution (Controls.domain 0) (Controls.body 0))
    (ModelSubstitution.packPair stable (Context.nil C) (Controls.domain 0) (Controls.body 0)
      (functionDomain products declarations.scalar) declarations.fibre declarations.domain_empty_read declarations.fibre_read)
    declarations.motive declarations.motive_read

theorem realization (stable : StrictPiSubstitution products) : SignatureRealization declarations.model Controls.signature where
  typeHeader symbol := by
    cases symbol with
    | scalar => rfl
    | fibre => exact declarations.function_header_read
    | pairMotive => exact declarations.pair_header_read
  termHeader symbol := by cases symbol; exact declarations.component_header_read
  termResult symbol := by cases symbol; exact declarations.branch_result_read stable

theorem sound (stable : StrictPiSubstitution products) (beta : PiBeta products)
    (eta : PiEta products stable.1) {judgment : Judgment Controls.symbols}
    (derivation : Derivation Controls.signature judgment) : Interprets declarations.model judgment :=
  derivation.sound declarations.model (declarations.realization stable) stable beta eta

theorem generated_full_motive_sound (stable : StrictPiSubstitution products) (beta : PiBeta products)
    (eta : PiEta products stable.1) :
    Interprets declarations.model (.term .nil Controls.fullMotiveFunction
      (.pi (Controls.sum 0) (Controls.motive 0))) :=
  declarations.sound stable beta eta Controls.fullMotiveFunctionTyped

theorem branch_read : declarations.model.evaluateTerm declarations.componentContext (Controls.fullBranch 0) =
    some ⟨C.toCwf.tySub declarations.motive
      (pack sums (functionDomain products declarations.scalar) declarations.fibre), declarations.branch⟩ := by
  have arguments : Controls.componentArguments 0 = TermExpr.var := by
    funext position
    fin_cases position <;> rfl
  have evaluated := declarations.model.evaluate_primitive declarations.componentContext .fullBranch
    TermExpr.var (C.toCwf.idS declarations.componentContext.1)
    ((declarations.model.evaluateSubstitution_eq_some_iff declarations.componentContext
      declarations.componentContext TermExpr.var _).mp
        (declarations.model.evaluateSubstitution_identity declarations.componentContext))
  change declarations.model.evaluateTerm declarations.componentContext
    (.primitive (S := Controls.symbols) .fullBranch (Controls.componentArguments 0)) = _
  rw [arguments]
  exact evaluated.trans (congrArg some (Value.substitute_identity
    (⟨C.toCwf.tySub declarations.motive
      (pack sums (functionDomain products declarations.scalar) declarations.fibre), declarations.branch⟩)))

theorem branch_section_recovers_supplied (stable : StrictPiSubstitution products) (beta : PiBeta products)
    (eta : PiEta products stable.1) :
    (Controls.fullBranchTyped Controls.emptyContext).termSection declarations.model
        (declarations.realization stable) stable beta eta declarations.componentContext
        (C.toCwf.tySub declarations.motive
          (pack sums (functionDomain products declarations.scalar) declarations.fibre))
        declarations.component_header_read (declarations.branch_result_read stable) = declarations.branch :=
  (Controls.fullBranchTyped Controls.emptyContext).termSection_unique declarations.model
    (declarations.realization stable) stable beta eta declarations.componentContext _
    declarations.component_header_read (declarations.branch_result_read stable) declarations.branch declarations.branch_read

def pairElimination : TermExpr Controls.symbols 2 :=
  Controls.fullElimination (genericPair (Controls.domain 0) (Controls.body 0))

def pairEliminationEquation : Derivation Controls.signature (.termEq (Controls.componentContext 0 .nil)
    pairElimination (Controls.fullBranch 0) (Controls.signature.termResult .fullBranch)) := by
  have branchSame : (Controls.fullBranch 2).substitute (instantiateComponents (.var 1) (.var 0)) =
      Controls.fullBranch 0 := by
    apply congrArg (TermExpr.primitive (S := Controls.symbols) Controls.TermSymbol.fullBranch)
    funext position
    fin_cases position <;> rfl
  have typeSame : (Controls.motive 2).substitute
      (instantiate (.pair (Controls.domain 2) (Controls.body 2) (.var 1) (.var 0))) =
      Controls.signature.termResult .fullBranch := by
    change (TypeExpr.family (S := Controls.symbols) Controls.TypeSymbol.pairMotive
      (fun _ => .pair (Controls.domain 2) (Controls.body 2) (.var 1) (.var 0))) =
      .family .pairMotive (fun _ => genericPair (Controls.domain 0) (Controls.body 0))
    rw [Controls.genericPair_uniform]
  have equation := Controls.fullPairBeta
  rw [branchSame, typeSame] at equation
  simpa only [pairElimination, Controls.genericPair_uniform] using equation

theorem pair_elimination_read (stable : StrictPiSubstitution products) (beta : PiBeta products)
    (eta : PiEta products stable.1) :
    declarations.model.evaluateTerm declarations.componentContext pairElimination =
      some ⟨C.toCwf.tySub declarations.motive
        (pack sums (functionDomain products declarations.scalar) declarations.fibre), declarations.branch⟩ := by
  rcases (pairEliminationEquation.sound declarations.model (declarations.realization stable)
    stable beta eta).termEqAt declarations.componentContext _ declarations.component_header_read
      (declarations.branch_result_read stable) with ⟨value, firstRead, secondRead⟩
  exact firstRead.trans (secondRead.symm.trans declarations.branch_read)

end Declarations

end Mettapedia.TypeTheory.Calculi.NativeDependent.External.DeclaredModel
