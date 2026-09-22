import Mettapedia.Logic.HOL.ImpredicativeProofTranslation
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.HOLNativeProofCompilerCompleteness
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.HOLNativeGenericProofCompilerTyping
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.HOLNativeGenericProofCompilerSemantics
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.HOLNativeGenericProofCompilerSubstitution
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.HOLNativeGenericProofCompilerUniformList
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.HOLNativeGenericProofCompilerNaturalityControls

/-!
# Total retained HOL proof compilation into a dependent host

Every constructor of retained extensional HOL is translated through the proved
impredicative encoding and the existing native compiler. Totality is proved
when all eight host equality capabilities are available; the existing uniform
List host supplies a concrete law-bearing instance. The output is computed,
typed at the represented conclusion, and interpreted by the same displayed
semantic algebra as the original compiler.

This is a theorem about supplied, intrinsically typed source proof trees. It
does not infer such a tree from a proposition, certify the truth of source
axioms, or require a runtime to rebuild a proof at every evaluation step.
-/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false


namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOLImpredicativeProofCompilation

open Presentation Presentation.FormationSensitive FormationSensitiveHOLInterface
open Mettapedia.Logic HOL.ImpredicativeConnectives HOLNativeGenericProofCompiler

universe u v
variable {Base : Type u} {Const : HOL.Ty Base → Type v}

/-- There is one native compiler; this entry point expands its source. -/
def compileExpanded (signature : LogicalSignature Base Const) (proofName : DeclName)
    (operations : Operations signature proofName)
    {Γ : HOL.Ctx Base} {Δ : List (HOL.Formula Const Γ)} {φ : HOL.Formula Const Γ}
    (source : HOL.ProofSyntax Const Δ φ)
    {n : Nat} (objects : Sub Tower.Head Γ.length n)
    (hypotheses : Fin (Δ.map expand).length → Tower.Tm n) : Option (Tower.Tm n) :=
  compile signature proofName operations (expandProof source) objects hypotheses

theorem compileExpanded_isSome (signature : LogicalSignature Base Const)
    (proofName : DeclName) (operations : Operations signature proofName)
    (total : operations.raw.Total)
    {Γ : HOL.Ctx Base} {Δ : List (HOL.Formula Const Γ)} {φ : HOL.Formula Const Γ}
    (source : HOL.ProofSyntax Const Δ φ)
    {n : Nat} (objects : Sub Tower.Head Γ.length n)
    (hypotheses : Fin (Δ.map expand).length → Tower.Tm n) :
    (compileExpanded signature proofName operations source objects hypotheses).isSome :=
  compile_core_isSome signature proofName operations total _ (expandProof_isCore source)
    objects hypotheses

/-- Extract the computed result of the actual compiler using its totality
proof. There is no classical choice of a native proof and no default value. -/
def translateProof (signature : LogicalSignature Base Const) (proofName : DeclName)
    (operations : Operations signature proofName) (total : operations.raw.Total)
    {Γ : HOL.Ctx Base} {Δ : List (HOL.Formula Const Γ)} {φ : HOL.Formula Const Γ}
    (source : HOL.ProofSyntax Const Δ φ)
    {n : Nat} (objects : Sub Tower.Head Γ.length n)
    (hypotheses : Fin (Δ.map expand).length → Tower.Tm n) : Tower.Tm n :=
  (compileExpanded signature proofName operations source objects hypotheses).get
    (compileExpanded_isSome signature proofName operations total source objects hypotheses)

theorem translateProof_eq (signature : LogicalSignature Base Const) (proofName : DeclName)
    (operations : Operations signature proofName) (total : operations.raw.Total)
    {Γ : HOL.Ctx Base} {Δ : List (HOL.Formula Const Γ)} {φ : HOL.Formula Const Γ}
    (source : HOL.ProofSyntax Const Δ φ)
    {n : Nat} (objects : Sub Tower.Head Γ.length n)
    (hypotheses : Fin (Δ.map expand).length → Tower.Tm n) :
    compileExpanded signature proofName operations source objects hypotheses =
      some (translateProof signature proofName operations total source objects hypotheses) :=
  (Option.some_get (compileExpanded_isSome signature proofName operations total source
    objects hypotheses)).symm

/-- Substitution commutes with the actual computed native proof, including
the rules introduced by connective expansion. -/
theorem translateProof_substitute (signature : LogicalSignature Base Const)
    (proofName : DeclName) (operations : Operations signature proofName)
    (total : operations.raw.Total) (natural : operations.raw.Natural)
    {Γ : HOL.Ctx Base} {Δ : List (HOL.Formula Const Γ)} {φ : HOL.Formula Const Γ}
    (source : HOL.ProofSyntax Const Δ φ)
    {n m : Nat} (objects : Sub Tower.Head Γ.length n)
    (hypotheses : Fin (Δ.map expand).length → Tower.Tm n) (sigma : Sub Tower.Head n m) :
    translateProof signature proofName operations total source
        (fun i => subst sigma (objects i)) (fun i => subst sigma (hypotheses i)) =
      subst sigma (translateProof signature proofName operations total source objects hypotheses) := by
  apply Option.some.inj
  rw [← translateProof_eq]
  change compile signature proofName operations (expandProof source) _ _ = _
  rw [compile_substitute signature proofName operations natural]
  change (compileExpanded signature proofName operations source objects hypotheses).map _ = _
  rw [translateProof_eq]
  rfl

theorem translateProof_typed (signature : LogicalSignature Base Const) (proofName : DeclName)
    (operations : Operations signature proofName) (total : operations.raw.Total)
    {Γ : HOL.Ctx Base} {Δ : List (HOL.Formula Const Γ)} {φ : HOL.Formula Const Γ}
    (source : HOL.ProofSyntax Const Δ φ)
    {n : Nat} {target : Tower.Ctx n} {objects : Sub Tower.Head Γ.length n}
    {hypotheses : Fin (Δ.map expand).length → Tower.Tm n}
    (objectTyped : GenericTyping.Objects signature target objects)
    (hypothesisTyped : GenericTyping.Hypotheses signature operations
      target objects hypotheses) :
    Typing operations.target target
      (translateProof signature proofName operations total source objects hypotheses)
      (FormationSensitiveHOLGenericProofFamily.proof proofName
        (subst objects (HOLImpredicativeRepresentation.translate signature φ))) := by
  obtain ⟨code, represented, typed⟩ := GenericTyping.compile_typed signature proofName
    operations (expandProof source) objectTyped hypothesisTyped
      (translateProof_eq signature proofName operations total source objects hypotheses)
  rw [HOLImpredicativeRepresentation.translate_eq] at represented
  cases Option.some.inj represented
  exact typed

theorem translateProof_closed_typed (signature : LogicalSignature Base Const)
    (proofName : DeclName) (operations : Operations signature proofName)
    (total : operations.raw.Total)
    {φ : HOL.Formula Const []} (source : HOL.ProofSyntax Const [] φ) :
    Typing operations.target .nil
      (translateProof signature proofName operations total source Fin.elim0 Fin.elim0)
      (FormationSensitiveHOLGenericProofFamily.proof proofName
        (HOLImpredicativeRepresentation.translate signature φ)) := by
  obtain ⟨code, represented, typed⟩ := GenericTyping.compile_closed signature proofName
    operations (expandProof source)
      (translateProof_eq signature proofName operations total source Fin.elim0 Fin.elim0)
  rw [HOLImpredicativeRepresentation.translate_eq] at represented
  cases Option.some.inj represented
  exact typed

/-- Semantic correctness at the exact expanded conclusion. Relating this
formula to its original Henkin meaning uses `denote_expand`, not an assumed
invariance of arbitrary displayed semantic algebras. -/
theorem translateProof_denotes (signature : LogicalSignature Base Const)
    (proofName : DeclName) (operations : Operations signature proofName)
    (total : operations.raw.Total) (semantics : GenericSemantics.Algebra signature proofName operations)
    {Γ : HOL.Ctx Base} {Δ : List (HOL.Formula Const Γ)} {φ : HOL.Formula Const Γ}
    (source : HOL.ProofSyntax Const Δ φ)
    {n : Nat} {objects : Sub Tower.Head Γ.length n}
    {hypotheses : Fin (Δ.map expand).length → Tower.Tm n}
    (state : semantics.State objects)
    (hypothesesMeaning : GenericSemantics.Hypotheses semantics state hypotheses) :
    semantics.Denotes state
      (translateProof signature proofName operations total source objects hypotheses) (expand φ) :=
  GenericSemantics.compile_denotes signature proofName operations semantics (expandProof source)
    (translateProof_eq signature proofName operations total source objects hypotheses)
    state hypothesesMeaning

/-- The existing declared extensional host supplies every capability with
its previously verified typing laws. Totality is discharged by its actual
operation definitions, not postulated by a client. -/
theorem uniformList_total : UniformList.operations.raw.Total := by
  constructor <;> intros <;> rfl

theorem uniformList_natural : UniformList.operations.raw.Natural :=
  UniformList.rawOperations_natural

namespace Controls

open HOL.UniformListInduction

def splitConclusion : HOL.Formula Symbol [] :=
    .imp (.ex (.and (.eq (.var (HOL.Var.vz (τ := HOL.Ty.prop))) (.var .vz)) .top))
      (.and (.ex (.eq (.var (HOL.Var.vz (τ := HOL.Ty.prop))) (.var .vz)))
        (.ex (σ := HOL.Ty.prop) .top))

def split : HOL.ProofSyntax Symbol [] splitConclusion :=
  ProofControls.splitExistential _ _

theorem split_compiles_typed :
    Typing UniformList.operations.target .nil
      (translateProof FormationSensitiveHOLLeibnizInterface.signature UniformList.proofName
        UniformList.operations uniformList_total split Fin.elim0 Fin.elim0)
      (FormationSensitiveHOLGenericProofFamily.proof UniformList.proofName
        (HOLImpredicativeRepresentation.translate FormationSensitiveHOLLeibnizInterface.signature
          splitConclusion)) :=
  translateProof_closed_typed _ _ _ uniformList_total split

theorem unexpanded_split_rejected :
    compile FormationSensitiveHOLLeibnizInterface.signature UniformList.proofName
      UniformList.operations split (n := 0) Fin.elim0 Fin.elim0 = none := rfl

theorem missing_equality_capabilities_rejected :
    compileExpanded FormationSensitiveHOLLeibnizInterface.signature UniformList.proofName
      (Operations.logicalOnly _ _ UniformList.operations.fresh)
      (HOL.ProofSyntax.andI .topI .topI :
        HOL.ProofSyntax Symbol (Γ := []) [] (.and .top .top))
      (n := 0) Fin.elim0 Fin.elim0 = none := rfl

end Controls

#print axioms compileExpanded_isSome
#print axioms translateProof_typed
#print axioms translateProof_substitute
#print axioms translateProof_closed_typed
#print axioms translateProof_denotes
#print axioms uniformList_total
#print axioms uniformList_natural
#print axioms Controls.split_compiles_typed
#print axioms Controls.unexpanded_split_rejected
#print axioms Controls.missing_equality_capabilities_rejected

end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOLImpredicativeProofCompilation
