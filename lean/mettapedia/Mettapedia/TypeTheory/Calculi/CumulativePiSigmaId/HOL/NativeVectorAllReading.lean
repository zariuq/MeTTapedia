import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.NativeVectorGuardedFamily
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorAllAnnotatedTransport
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.AnnotatedPredicateStructuralProfile

/-!
# Reading the actual universe-valued Vector All program

The existing vector recursor is specialized to a predicate-valued result.
The element, predicate-result and recursor universe heads have explicit lexical
codes. Their separation is a profile condition, not a global universe model.
The source programme retains its original annotations and dependent family.
Reading establishes exact syntax translation; source formation and the vector
recursor's semantic/computation premises remain independently required.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeVectorAll.Reading

open Mettapedia.Logic
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel
open Presentation TypedEquality.Annotated NativeNaturalVectorFamilies
open AnnotatedPredicateReading
local infixr:60 " ⇒ " => HOL.Ty.arr
universe u v
variable {Base : Type u} {Const : HOL.Ty Base → Type v}

/-- Changing the recursion result requires its own selection operation;
the original vector constructors and projections are retained exactly. -/
def typeOperations (original : NativeVectorComputationRows.Operations Base Const)
    (evidence : HOL.Ty Base)
    (selection : HOL.ClosedTerm Const
      (HOL.SelectionProofs.Selection (original.number ⇒ original.vector ⇒ (evidence ⇒ .prop)))) :
    NativeVectorComputationRows.Operations Base Const :=
  { original with result := evidence ⇒ .prop, selection := selection }

structure ProfileLevels (element result : LevelExpr Nat) : Prop where
  element_result : element ≠ result
  element_recursor : element ≠ Annotated.Profile.recursorLevel element result
  result_recursor : result ≠ Annotated.Profile.recursorLevel element result

variable [DecidableEq Base]
    (original : NativeVectorComputationRows.Operations Base Const)
    {evidence : HOL.Ty Base} (pairs : HOL.PredicateSigma.Operations Const evidence)
    (witness : HOL.ClosedTerm Const evidence)
    (selection : HOL.ClosedTerm Const
      (HOL.SelectionProofs.Selection (original.number ⇒ original.vector ⇒ (evidence ⇒ .prop))))
    (element result : LevelExpr Nat)

abbrev operations := typeOperations original evidence selection

def lexical : LexicalReading Tower.Head Base Const where
  constCode? := (NativeVectorComputationRows.GuardedFamily.lexical (operations original selection)).constCode?
  headCode? head :=
    if head = .sort element then some ⟨_, HOL.PredicateProducts.full original.elementPredicate⟩
    else if head = .sort result then some ⟨_, HOL.PredicateProducts.full (evidence ⇒ .prop)⟩
    else if head = .sort (Annotated.Profile.recursorLevel element result) then
      some ⟨_, HOL.PredicateProducts.full ((evidence ⇒ .prop) ⇒ .prop)⟩
    else none
  structuralCode? := StructuralProfile.code? pairs witness

variable {Γ : HOL.Ctx Base}

theorem natural_reads : Reads (lexical original pairs witness selection element result)
    (Γ := Γ) (.const natName) (HOL.weakenCtx Γ (HOL.PredicateProducts.full original.number)) :=
  .constant (by simp [lexical, NativeVectorComputationRows.GuardedFamily.lexical,
    NativeVectorComputationRows.Operations.lexicalReading, natName, vecName, operations, typeOperations])

theorem zero_reads : Reads (lexical original pairs witness selection element result)
    (Γ := Γ) (.const zeroName) (HOL.weakenCtx Γ original.zero) :=
  .constant (by simp [lexical, NativeVectorComputationRows.GuardedFamily.lexical,
    NativeVectorComputationRows.Operations.lexicalReading, natName, zeroName, vecName, operations, typeOperations])

theorem vector_reads : Reads (lexical original pairs witness selection element result)
    (Γ := Γ) (.const vecName)
    (HOL.weakenCtx Γ (NativeVectorComputationRows.GuardedFamily.familyCode (operations original selection))) :=
  .constant (by simp [lexical, NativeVectorComputationRows.GuardedFamily.lexical])

theorem eliminator_reads : Reads (lexical original pairs witness selection element result)
    (Γ := Γ) (.const vecEliminateName)
    (HOL.weakenCtx Γ (operations original selection).eliminator) :=
  .constant (by simp [lexical, NativeVectorComputationRows.GuardedFamily.lexical,
    NativeVectorComputationRows.Operations.lexicalReading,
    natName, zeroName, succName, vnilName, vconsName, vecName, vecEliminateName])

def fullCode (carrier : HOL.Ty Base) : HOL.Term Const Γ (carrier ⇒ .prop) :=
  HOL.weakenCtx Γ (HOL.PredicateProducts.full carrier)

def vectorCode (A : HOL.Term Const Γ original.elementPredicate) (index : HOL.Term Const Γ original.number) :
    HOL.Term Const Γ (original.vector ⇒ .prop) :=
  .app (.app (HOL.weakenCtx Γ (NativeVectorComputationRows.GuardedFamily.familyCode
    (operations original selection))) A) index

theorem vector_application {A index : CTm Tower.Head Γ.length}
    {elementCode : HOL.Term Const Γ original.elementPredicate} {indexCode : HOL.Term Const Γ original.number}
    (first : Reads (lexical original pairs witness selection element result) A elementCode)
    (second : Reads (lexical original pairs witness selection element result) index indexCode) :
    Reads (lexical original pairs witness selection element result) (Annotated.vector A index)
      (vectorCode original selection elementCode indexCode) :=
  .application (.application (vector_reads original pairs witness selection element result) first) second

theorem result_reads (levels : ProfileLevels element result) :
    Reads (lexical original pairs witness selection element result) (Γ := Γ)
      (Annotated.Formation.resultSort result) (fullCode (evidence ⇒ .prop)) := by
  exact .head (by simp [lexical, levels.element_result.symm])

def motiveCode : HOL.Term Const Γ (operations original selection).motive :=
  .lam (.lam (fullCode (evidence ⇒ .prop)))

theorem motive_reads (levels : ProfileLevels element result) {A : CTm Tower.Head Γ.length}
    {elementCode : HOL.Term Const Γ original.elementPredicate}
    (elementRead : Reads (lexical original pairs witness selection element result) A elementCode) :
    Reads (lexical original pairs witness selection element result)
      (Annotated.Formation.universeMotive result A) (motiveCode original selection) := by
  apply Reads.abstraction (natural_reads original pairs witness selection element result)
  apply Reads.abstraction
    (vector_application original pairs witness selection element result
      (elementRead.rename HOL.Rename.weaken wk (fun _ => rfl)) (.var .vz))
  exact result_reads original pairs witness selection element result levels

def unitCode : HOL.Term Const Γ (evidence ⇒ .prop) :=
  .app (.app (.app (HOL.weakenCtx Γ (StructuralProfile.identityCode witness original.number))
    (fullCode original.number)) (HOL.weakenCtx Γ original.zero)) (HOL.weakenCtx Γ original.zero)

theorem unit_reads : Reads (lexical original pairs witness selection element result)
    (Γ := Γ) Annotated.Formation.unitType (unitCode original witness) :=
  .identity rfl (natural_reads original pairs witness selection element result)
    (zero_reads original pairs witness selection element result) (zero_reads original pairs witness selection element result)

def consCode (predicate : HOL.Term Const Γ (original.element ⇒ evidence ⇒ .prop)) :
    HOL.Term Const Γ (operations original selection).method :=
  .lam (.lam (.lam (.lam
    (.app (.app (HOL.weakenCtx _ (StructuralProfile.sigmaCode pairs))
      (.app (HOL.weaken (HOL.weaken (HOL.weaken (HOL.weaken predicate)))) (.var (.vs (.vs .vz)))))
      (.lam (.var (.vs .vz)))))))

theorem cons_reads (levels : ProfileLevels element result) {A predicate : CTm Tower.Head Γ.length}
    {elementCode : HOL.Term Const Γ original.elementPredicate}
    {predicateCode : HOL.Term Const Γ (original.element ⇒ evidence ⇒ .prop)}
    (elementRead : Reads (lexical original pairs witness selection element result) A elementCode)
    (predicateRead : Reads (lexical original pairs witness selection element result) predicate predicateCode) :
    Reads (lexical original pairs witness selection element result)
      (Annotated.Formation.consCase result A predicate) (consCode original pairs selection predicateCode) := by
  have lengthRead : Reads (lexical original pairs witness selection element result)
      (Γ := original.element :: original.number :: Γ) (.var 1) (.var (.vs .vz)) := by
    convert (Reads.var (lex := lexical original pairs witness selection element result)
      (Γ := original.element :: original.number :: Γ) (.vs .vz)) using 1
    congr 1
  have headRead : Reads (lexical original pairs witness selection element result)
      (Γ := (evidence ⇒ .prop) :: original.vector :: original.element :: original.number :: Γ)
      (.var 2) (.var (.vs (.vs .vz))) := by
    convert (Reads.var (lex := lexical original pairs witness selection element result)
      (Γ := (evidence ⇒ .prop) :: original.vector :: original.element :: original.number :: Γ)
      (.vs (.vs .vz))) using 1
    congr 1
  have ihRead : Reads (lexical original pairs witness selection element result)
      (Γ := evidence :: (evidence ⇒ .prop) :: original.vector :: original.element :: original.number :: Γ)
      (.var 1) (.var (.vs .vz)) := by
    convert (Reads.var (lex := lexical original pairs witness selection element result)
      (Γ := evidence :: (evidence ⇒ .prop) :: original.vector :: original.element :: original.number :: Γ)
      (.vs .vz)) using 1
    congr 1
  apply Reads.abstraction (natural_reads original pairs witness selection element result)
  apply Reads.abstraction (elementRead.rename HOL.Rename.weaken wk (fun _ => rfl))
  apply Reads.abstraction
    (vector_application original pairs witness selection element result
      ((elementRead.rename HOL.Rename.weaken wk (fun _ => rfl)).rename HOL.Rename.weaken wk (fun _ => rfl))
      lengthRead)
  apply Reads.abstraction (result_reads original pairs witness selection element result levels)
  apply Reads.dependentSum (by exact StructuralProfile.code_sigma pairs witness)
    (Reads.application
      ((((predicateRead.rename HOL.Rename.weaken wk (fun _ => rfl)).rename HOL.Rename.weaken wk (fun _ => rfl)).rename
        HOL.Rename.weaken wk (fun _ => rfl)).rename HOL.Rename.weaken wk (fun _ => rfl)) headRead)
  exact ihRead

def allCode (A : HOL.Term Const Γ original.elementPredicate)
    (predicate : HOL.Term Const Γ (original.element ⇒ evidence ⇒ .prop))
    (index : HOL.Term Const Γ original.number) (value : HOL.Term Const Γ original.vector) :
    HOL.Term Const Γ (evidence ⇒ .prop) :=
  .app (.app (.app (.app (.app (.app (HOL.weakenCtx Γ (operations original selection).eliminator)
    A) (motiveCode original selection)) (unitCode original witness)) (consCode original pairs selection predicate)) index) value

theorem all_reads (levels : ProfileLevels element result) {A predicate index value : CTm Tower.Head Γ.length}
    {elementCode : HOL.Term Const Γ original.elementPredicate}
    {predicateCode : HOL.Term Const Γ (original.element ⇒ evidence ⇒ .prop)}
    {indexCode : HOL.Term Const Γ original.number} {valueCode : HOL.Term Const Γ original.vector}
    (elementRead : Reads (lexical original pairs witness selection element result) A elementCode)
    (predicateRead : Reads (lexical original pairs witness selection element result) predicate predicateCode)
    (indexRead : Reads (lexical original pairs witness selection element result) index indexCode)
    (valueRead : Reads (lexical original pairs witness selection element result) value valueCode) :
    Reads (lexical original pairs witness selection element result)
      (Annotated.Formation.allType result A predicate index value)
      (allCode original pairs witness selection elementCode predicateCode indexCode valueCode) :=
  .application (.application (.application (.application (.application (.application
    (eliminator_reads original pairs witness selection element result) elementRead)
    (motive_reads original pairs witness selection element result levels elementRead))
    (unit_reads original pairs witness selection element result))
    (cons_reads original pairs witness selection element result levels elementRead predicateRead)) indexRead) valueRead

theorem all_readback (levels : ProfileLevels element result) {A predicate index value : CTm Tower.Head Γ.length}
    {elementCode : HOL.Term Const Γ original.elementPredicate}
    {predicateCode : HOL.Term Const Γ (original.element ⇒ evidence ⇒ .prop)}
    {indexCode : HOL.Term Const Γ original.number} {valueCode : HOL.Term Const Γ original.vector}
    (elementRead : Reads (lexical original pairs witness selection element result) A elementCode)
    (predicateRead : Reads (lexical original pairs witness selection element result) predicate predicateCode)
    (indexRead : Reads (lexical original pairs witness selection element result) index indexCode)
    (valueRead : Reads (lexical original pairs witness selection element result) value valueCode) :
    Reader.infer? (lexical original pairs witness selection element result) Γ
      (Annotated.Formation.allType result A predicate index value) =
      some ⟨evidence ⇒ .prop, allCode original pairs witness selection elementCode predicateCode indexCode valueCode⟩ :=
  Reader.infer?_complete (all_reads original pairs witness selection element result levels
    elementRead predicateRead indexRead valueRead)

#print axioms all_reads
#print axioms all_readback

end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeVectorAll.Reading
