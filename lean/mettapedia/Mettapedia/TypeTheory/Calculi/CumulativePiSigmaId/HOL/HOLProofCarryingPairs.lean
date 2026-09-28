import Mettapedia.Logic.HOL.ProofCarryingPipeline
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.HOLDependentProofExecution

/-!
# Retained HOL invariants as native dependent pairs

The object component is the representation of the computed source expression;
the evidence component is the output of the existing total HOL proof compiler.
The Sigma type indexes the proof by that same object. Formation is derived
from the logical signature, not requested as a new client assumption.
Arbitrary typed object substitutions and retained source hypotheses are
supported. This construction does not validate the source assumptions.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOLProofCarryingPairs

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel
open Presentation Presentation.FormationSensitive FormationSensitiveHOLInterface
open Mettapedia.Logic HOLNativeGenericProofCompiler
open HOLImpredicativeRepresentation HOLImpredicativeProofCompilation

universe u v
variable {Base : Type u} {Const : HOL.Ty Base → Type v}
  {Γ : HOL.Ctx Base} {Δ : List (HOL.Formula Const Γ)} {σ : HOL.Ty Base}

def predicateBody (predicate : HOL.Term Const Γ (.arr σ .prop)) :
    HOL.Formula Const (σ :: Γ) := .app (HOL.weaken predicate) (.var .vz)

theorem instantiate_predicateBody (predicate : HOL.Term Const Γ (.arr σ .prop))
    (value : HOL.Term Const Γ σ) :
    HOL.instantiate value (predicateBody predicate) = .app predicate value := by
  simp only [predicateBody, HOL.instantiate, HOL.subst, HOL.Subst.single]
  rw [← HOL.instantiate, HOL.instantiate_weaken]

def family (signature : LogicalSignature Base Const) (proofName : DeclName)
    (predicate : HOL.Term Const Γ (.arr σ .prop))
    {n : Nat} (objects : Sub Tower.Head Γ.length n) : Tower.Tm (n + 1) :=
  FormationSensitiveHOLGenericProofFamily.proof proofName
    (subst (liftSub objects) (translate signature (predicateBody predicate)))

def pairType (signature : LogicalSignature Base Const) (proofName : DeclName)
    (predicate : HOL.Term Const Γ (.arr σ .prop))
    {n : Nat} (objects : Sub Tower.Head Γ.length n) : Tower.Tm n :=
  .sigma (typeAt signature.types n σ) (family signature proofName predicate objects)

def pack (signature : LogicalSignature Base Const) (proofName : DeclName)
    (operations : Operations signature proofName) (total : operations.raw.Total)
    {predicate : HOL.Term Const Γ (.arr σ .prop)}
    (value : HOL.ProofCarryingPipeline.Value predicate Δ)
    {n : Nat} (objects : Sub Tower.Head Γ.length n)
    (hypotheses : Fin (Δ.map HOL.ImpredicativeConnectives.expand).length → Tower.Tm n) : Tower.Tm n :=
  .pair (subst objects (translate signature value.term))
    (translateProof signature proofName operations total value.evidence objects hypotheses)

theorem family_instantiate (signature : LogicalSignature Base Const) (proofName : DeclName)
    (predicate : HOL.Term Const Γ (.arr σ .prop)) (value : HOL.Term Const Γ σ)
    {n : Nat} (objects : Sub Tower.Head Γ.length n) :
    inst0 (subst objects (translate signature value)) (family signature proofName predicate objects) =
      FormationSensitiveHOLGenericProofFamily.proof proofName
        (subst objects (translate signature (.app predicate value))) := by
  simp only [family, FormationSensitiveHOLGenericProofFamily.proof, inst0, subst]
  congr 1
  change inst0 (subst objects (translate signature value))
    (subst (liftSub objects) (translate signature (predicateBody predicate))) = _
  rw [← subst_inst0, ← translate_instantiate, instantiate_predicateBody]

theorem pairType_formed (signature : LogicalSignature Base Const) (proofName : DeclName)
    (operations : Operations signature proofName)
    (predicate : HOL.Term Const Γ (.arr σ .prop))
    {n : Nat} {target : Tower.Ctx n} {objects : Sub Tower.Head Γ.length n}
    (objectTyped : GenericTyping.Objects signature target objects) :
    Typing operations.target target (pairType signature proofName predicate objects)
      (sortTm (.max Tower.zero Tower.zero)) := by
  have propositionTyped := GenericTyping.represented_typed signature operations
    (translate_eq signature (predicateBody predicate)) (objectTyped.lift signature σ)
  have proofFormed := FormationSensitiveHOLGenericProofFamily.proof_formed
    signature proofName operations.fresh
    (propositionTyped.includeSignature
      (FormationSensitiveHOLGenericProofFamily.declarations signature proofName))
  exact .sigmaForm (operations.includeSourceTyping (typeAt_formed signature σ target))
    operations.zeroUniverse (operations.includeProofTyping proofFormed) operations.zeroUniverse
    (operations.sourceMorphism.join (.sorts Tower.zero Tower.zero))

/-- The result inhabits the actual formed Sigma, with the compiled source
proof in its second field. No unrelated witness is selected. -/
theorem pack_typed (signature : LogicalSignature Base Const) (proofName : DeclName)
    (operations : Operations signature proofName) (total : operations.raw.Total)
    {predicate : HOL.Term Const Γ (.arr σ .prop)}
    (value : HOL.ProofCarryingPipeline.Value predicate Δ)
    {n : Nat} {target : Tower.Ctx n} {objects : Sub Tower.Head Γ.length n}
    {hypotheses : Fin (Δ.map HOL.ImpredicativeConnectives.expand).length → Tower.Tm n}
    (objectTyped : GenericTyping.Objects signature target objects)
    (hypothesisTyped : GenericTyping.Hypotheses signature operations target objects hypotheses) :
    Typing operations.target target (pack signature proofName operations total value objects hypotheses)
      (pairType signature proofName predicate objects) := by
  apply Typing.pairIntro (pairType_formed signature proofName operations predicate objectTyped)
    (operations.sourceMorphism.isUniverse (.sort (.max Tower.zero Tower.zero)))
  · exact operations.includeSourceTyping
      (GenericTyping.represented_typed signature operations (translate_eq signature value.term) objectTyped)
  · rw [family_instantiate]
    exact translateProof_typed signature proofName operations total value.evidence objectTyped hypothesisTyped

/-- Ordinary computation extracts the value that the retained proof certifies. -/
theorem pack_fst (signature : LogicalSignature Base Const) (proofName : DeclName)
    (operations : Operations signature proofName) (total : operations.raw.Total)
    {predicate : HOL.Term Const Γ (.arr σ .prop)}
    (value : HOL.ProofCarryingPipeline.Value predicate Δ)
    {n : Nat} (objects : Sub Tower.Head Γ.length n)
    (hypotheses : Fin (Δ.map HOL.ImpredicativeConnectives.expand).length → Tower.Tm n) :
    Step operations.target.headEq (.fst (pack signature proofName operations total value objects hypotheses))
      (subst objects (translate signature value.term)) operations.target.computation := .betaSigmaFst _ _

theorem pack_snd (signature : LogicalSignature Base Const) (proofName : DeclName)
    (operations : Operations signature proofName) (total : operations.raw.Total)
    {predicate : HOL.Term Const Γ (.arr σ .prop)}
    (value : HOL.ProofCarryingPipeline.Value predicate Δ)
    {n : Nat} (objects : Sub Tower.Head Γ.length n)
    (hypotheses : Fin (Δ.map HOL.ImpredicativeConnectives.expand).length → Tower.Tm n) :
    Step operations.target.headEq (.snd (pack signature proofName operations total value objects hypotheses))
      (translateProof signature proofName operations total value.evidence objects hypotheses)
      operations.target.computation := .betaSigmaSnd _ _

/-- Whole-pair substitution preserves the actual compiled evidence, not just
its proposition or an existentially supplied replacement. -/
theorem pack_substitute (signature : LogicalSignature Base Const) (proofName : DeclName)
    (operations : Operations signature proofName) (total : operations.raw.Total)
    (natural : operations.raw.Natural)
    {predicate : HOL.Term Const Γ (.arr σ .prop)}
    (value : HOL.ProofCarryingPipeline.Value predicate Δ)
    {n m : Nat} (objects : Sub Tower.Head Γ.length n)
    (hypotheses : Fin (Δ.map HOL.ImpredicativeConnectives.expand).length → Tower.Tm n)
    (substitution : Sub Tower.Head n m) :
    subst substitution (pack signature proofName operations total value objects hypotheses) =
      pack signature proofName operations total value
        (fun i => subst substitution (objects i)) (fun i => subst substitution (hypotheses i)) := by
  simp only [pack, subst, subst_comp,
    translateProof_substitute signature proofName operations total natural]

/-- A native dependent continuation consumes the whole certified pair. Its
result type is instantiated with that pair, including the retained proof. -/
theorem consume_typed (signature : LogicalSignature Base Const) (proofName : DeclName)
    (operations : Operations signature proofName) (total : operations.raw.Total)
    {predicate : HOL.Term Const Γ (.arr σ .prop)}
    (value : HOL.ProofCarryingPipeline.Value predicate Δ)
    {n : Nat} {target : Tower.Ctx n} {objects : Sub Tower.Head Γ.length n}
    {hypotheses : Fin (Δ.map HOL.ImpredicativeConnectives.expand).length → Tower.Tm n}
    (objectTyped : GenericTyping.Objects signature target objects)
    (hypothesisTyped : GenericTyping.Hypotheses signature operations target objects hypotheses)
    {body resultFamily : Tower.Tm (n + 1)}
    (bodyTyped : Typing operations.target
      (.snoc target (pairType signature proofName predicate objects)) body resultFamily) :
    Typing operations.target target
      (inst0 (pack signature proofName operations total value objects hypotheses) body)
      (inst0 (pack signature proofName operations total value objects hypotheses) resultFamily) :=
  bodyTyped.instantiate
    (pack_typed signature proofName operations total value objectTyped hypothesisTyped)

theorem consume_beta (signature : LogicalSignature Base Const) (proofName : DeclName)
    (operations : Operations signature proofName) (total : operations.raw.Total)
    {predicate : HOL.Term Const Γ (.arr σ .prop)}
    (value : HOL.ProofCarryingPipeline.Value predicate Δ)
    {n : Nat} (objects : Sub Tower.Head Γ.length n)
    (hypotheses : Fin (Δ.map HOL.ImpredicativeConnectives.expand).length → Tower.Tm n)
    (body : Tower.Tm (n + 1)) :
    Step operations.target.headEq
      (.app (.lam body) (pack signature proofName operations total value objects hypotheses))
      (inst0 (pack signature proofName operations total value objects hypotheses) body)
      operations.target.computation := .betaPi _ _

/-- Substitution acts coherently on both the returned certified pair and
the program using it. -/
theorem consume_substitute (signature : LogicalSignature Base Const) (proofName : DeclName)
    (operations : Operations signature proofName) (total : operations.raw.Total)
    (natural : operations.raw.Natural)
    {predicate : HOL.Term Const Γ (.arr σ .prop)}
    (value : HOL.ProofCarryingPipeline.Value predicate Δ)
    {n m : Nat} (objects : Sub Tower.Head Γ.length n)
    (hypotheses : Fin (Δ.map HOL.ImpredicativeConnectives.expand).length → Tower.Tm n)
    (body : Tower.Tm (n + 1)) (substitution : Sub Tower.Head n m) :
    subst substitution (inst0 (pack signature proofName operations total value objects hypotheses) body) =
      inst0 (pack signature proofName operations total value
        (fun i => subst substitution (objects i)) (fun i => subst substitution (hypotheses i)))
        (subst (liftSub substitution) body) := by
  rw [subst_inst0, pack_substitute signature proofName operations total natural]

namespace Controls

open HOL.UniformListInduction HOLNativeGenericProofCompiler.UniformList

def zeroPredicate : Expr [] (.arr count .prop) :=
  .lam (.eq (.var .vz) (.const .zero))

def certifiedZero : HOL.ProofCarryingPipeline.Value zeroPredicate [] where
  term := .const .zero
  evidence := .impE (.eqPropER (.beta (.const Symbol.zero) (.eq (.var .vz) (.const Symbol.zero))))
    (.eqRefl (.const Symbol.zero))

/-- Discharge the host capabilities at the existing concrete List signature.
The second field is a compiled beta/equality proof, not an assumed inhabitant. -/
theorem closed_pair_typed :
    Typing operations.target .nil
      (pack FormationSensitiveHOLLeibnizInterface.signature proofName operations uniformList_total
        certifiedZero Fin.elim0 Fin.elim0)
      (pairType FormationSensitiveHOLLeibnizInterface.signature proofName zeroPredicate Fin.elim0) :=
  pack_typed FormationSensitiveHOLLeibnizInterface.signature proofName operations uniformList_total
    certifiedZero (fun i => Fin.elim0 i) (fun i => Fin.elim0 i)

/-- A native consumer computes with the pair, not merely with its Boolean
acceptance. The dependent result mentions the same packed term twice. -/
theorem reflexive_pair_consumer_typed :
    Typing operations.target .nil
      (inst0 (pack FormationSensitiveHOLLeibnizInterface.signature proofName operations
        uniformList_total certifiedZero Fin.elim0 Fin.elim0) (.refl (.var 0)))
      (.id (pairType FormationSensitiveHOLLeibnizInterface.signature proofName zeroPredicate Fin.elim0)
        (pack FormationSensitiveHOLLeibnizInterface.signature proofName operations
          uniformList_total certifiedZero Fin.elim0 Fin.elim0)
        (pack FormationSensitiveHOLLeibnizInterface.signature proofName operations
          uniformList_total certifiedZero Fin.elim0 Fin.elim0)) := by
  simpa only [inst0, subst, subst0, Fin.cases_zero] using Typing.reflIntro closed_pair_typed

end Controls

#print axioms pairType_formed
#print axioms pack_typed
#print axioms pack_fst
#print axioms pack_snd
#print axioms pack_substitute
#print axioms consume_typed
#print axioms consume_beta
#print axioms consume_substitute
#print axioms Controls.closed_pair_typed
#print axioms Controls.reflexive_pair_consumer_typed

end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOLProofCarryingPairs
