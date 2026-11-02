import Mettapedia.GSLT.LanguageDef.AdmittedContainerNonbottom
import Mettapedia.GSLT.LanguageDef.AdmittedContainerInductionControls
import Mettapedia.Languages.HOLLight.AdmittedInductionCompilation
import Mettapedia.Languages.HOLLight.AdmittedMembershipCompilation
import Mettapedia.Logic.HOL.ConstructorProgramRows
import Mettapedia.Logic.HOL.IndexedConstructorNonbottom
import Mettapedia.Tools.StageData

/-!
# Native compilation of original admitted-family induction

The actual admitted Vector declaration instantiates the generic case builder.
Selective elaboration extracts its finite proof data. An explicit typed
interpretation supplies the native operations; the source representation laws
remain premises until their checked native cache roots discharge them.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.HOLLight.AdmittedNonbottomCompilation

open Mettapedia.Logic Mettapedia.Languages.OpenTheory Mettapedia.TypeTheory
open HOL Mettapedia.GSLT.LanguageDef

def inputContext : Ctx AdmittedContainerGeneratedControls.BaseCode :=
  [AdmittedContainerGeneratedControls.number, AdmittedContainerGeneratedControls.space]

namespace Source

open AdmittedContainerGeneratedControls AdmittedContainerInductionControls

noncomputable def original : ProofSyntax AdmittedContainerGeneratedControls.Symbol
    [AdmittedContainerInductionControls.injectivity, AdmittedContainerInductionControls.separation]
    AdmittedContainerInductionControls.statement := by
  apply ProofSyntax.allI
  apply ProofSyntax.allI
  apply ProofSyntax.castIndices ?_ rfl
    (AdmittedContainerNonbottom.proof block registered guards initial num
      (.const .zero) (.const .successor) bottom ctor (.var (.vs .vz)) (.var .vz))
  rfl

theorem original_free : original.FunctionExtensionalityFree := by
  unfold original
  apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
  exact AdmittedContainerNonbottom.proof_free _ _ _ _ _ _ _ _ _ _ _

end Source

local macro "stageInduction% " value:term : term =>
  `(stageValue% [
    Mettapedia.Languages.HOLLight.AdmittedNonbottomCompilation.Source,
    Mettapedia.GSLT.LanguageDef.AdmittedContainerNonbottom,
    Mettapedia.GSLT.LanguageDef.AdmittedContainerInductionControls,
    Mettapedia.GSLT.LanguageDef.AdmittedContainerInduction,
    Mettapedia.GSLT.LanguageDef.AdmittedContainerProofs,
    Mettapedia.GSLT.LanguageDef.AdmittedContainerPredicate,
    Mettapedia.GSLT.LanguageDef.AdmittedContainerGeneratedControls,
    Mettapedia.GSLT.LanguageDef.AdmittedContainerGenerated,
    Mettapedia.GSLT.LanguageDef.AdmittedContainerHOL,
    Mettapedia.GSLT.LanguageDef.IndexedInductiveHOLRealization,
    Mettapedia.GSLT.LanguageDef.IndexedInductiveHOLTerms,
    Mettapedia.GSLT.LanguageDef.IndexedInductiveNatVec,
    Mettapedia.GSLT.LanguageDef.PositiveInductiveBlockBridge,
    Mettapedia.Logic.HOL.IndexedContainerPositionTerms,
    Mettapedia.Logic.HOL.IndexedContainerFieldGuards,
    Mettapedia.Logic.HOL.IndexedConstructorTerms,
    Mettapedia.Logic.HOL.IndexedConstructorGuards,
    Mettapedia.Logic.HOL.IndexedConstructorInduction,
    Mettapedia.Logic.HOL.ConstructorDataPredicates,
    Mettapedia.Logic.HOL.CurriedPredicates,
    Mettapedia.Logic.HOL.FiniteConstructorEncoding,
    Mettapedia.Logic.HOL.IndexedConstructorGuards.ProgramRows,
    Mettapedia.TypeTheory, List, Fin] $value)

namespace Source
open AdmittedContainerGeneratedControls AdmittedContainerInductionControls
noncomputable def constructors : IndexedConstructorGuards.ConstructorPrograms AdmittedContainerGeneratedControls.Symbol inputContext :=
  AdmittedContainerHOL.inventory block registered guards (initial (Γ := inputContext)) (num (Γ := inputContext))
noncomputable def positions : IndexedConstructorGuards.PositionPrograms constructors :=
  guards.positions (AdmittedContainerHOL.codes block registered)
    (initial (Γ := inputContext)) (num (Γ := inputContext)) (.const .zero) (.const .successor)
end Source

def arities : List (List (Ty AdmittedContainerGeneratedControls.BaseCode)) :=
  stagedData% (stageInduction% Source.constructors.fields)

def rows : IndexedConstructorGuards.ProgramRows AdmittedContainerGeneratedControls.Symbol inputContext
    AdmittedContainerGeneratedControls.number AdmittedContainerGeneratedControls.number arities :=
  stagedData% (stageInduction% (IndexedConstructorGuards.ProgramRows.ofPrograms Source.constructors Source.positions))

theorem arities_source : arities = Source.constructors.fields :=
  eq_of_heq (stagedHEq% arities, Source.constructors.fields)

theorem rows_source : HEq rows (IndexedConstructorGuards.ProgramRows.ofPrograms Source.constructors Source.positions) :=
  stagedHEq% rows, (IndexedConstructorGuards.ProgramRows.ofPrograms Source.constructors Source.positions)

def closedNumeral : Nat → ClosedTerm AdmittedContainerGeneratedControls.Symbol AdmittedContainerGeneratedControls.number
  | 0 => .const .zero
  | n + 1 => .app (.const .successor) (closedNumeral n)

theorem closedNumeral_source (n : Nat) : closedNumeral n = AdmittedContainerGeneratedControls.numeral n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [closedNumeral, AdmittedContainerGeneratedControls.numeral, ih]

def numeral (n : Nat) : HOL.Term AdmittedContainerGeneratedControls.Symbol inputContext AdmittedContainerGeneratedControls.number :=
  weakenCtx inputContext (closedNumeral n)

theorem numeral_source : numeral = AdmittedContainerInductionControls.num (Γ := inputContext) :=
  funext (fun n => congrArg (weakenCtx inputContext) (closedNumeral_source n))

def constructors := rows.constructors numeral
def positions := rows.positions numeral

private theorem constructors_of_extracted
    {Base : Type} {Const : Ty Base → Type} {Γ : Ctx Base}
    (inventory : IndexedConstructorGuards.ConstructorPrograms Const Γ)
    (positions : IndexedConstructorGuards.PositionPrograms inventory)
    {fields : List (List (Ty Base))}
    (data : IndexedConstructorGuards.ProgramRows Const Γ inventory.number inventory.index fields)
    (fieldSame : fields = inventory.fields)
    (dataSame : HEq data (IndexedConstructorGuards.ProgramRows.ofPrograms inventory positions))
    (numeral : Nat → HOL.Term Const Γ inventory.number) (numeralSame : numeral = inventory.numeral) :
    data.constructors numeral = inventory := by
  cases fieldSame
  rw [eq_of_heq dataSame, numeralSame]
  exact IndexedConstructorGuards.ProgramRows.constructors_ofPrograms inventory positions

private theorem positions_of_extracted
    {Base : Type} {Const : Ty Base → Type} {Γ : Ctx Base}
    (inventory : IndexedConstructorGuards.ConstructorPrograms Const Γ)
    (positions : IndexedConstructorGuards.PositionPrograms inventory)
    {fields : List (List (Ty Base))}
    (data : IndexedConstructorGuards.ProgramRows Const Γ inventory.number inventory.index fields)
    (fieldSame : fields = inventory.fields)
    (dataSame : HEq data (IndexedConstructorGuards.ProgramRows.ofPrograms inventory positions))
    (numeral : Nat → HOL.Term Const Γ inventory.number) (numeralSame : numeral = inventory.numeral) :
    HEq (data.positions numeral) positions := by
  cases fieldSame
  rw [eq_of_heq dataSame, numeralSame]
  exact IndexedConstructorGuards.ProgramRows.positions_ofPrograms inventory positions

theorem constructors_source : constructors = Source.constructors :=
  constructors_of_extracted Source.constructors Source.positions rows arities_source rows_source numeral numeral_source

theorem positions_source : HEq positions Source.positions :=
  positions_of_extracted Source.constructors Source.positions rows arities_source rows_source numeral numeral_source

def constructor : HOL.Term AdmittedContainerGeneratedControls.Symbol inputContext
    (constructors.number ⇒ FiniteConstructorEncoding.payloadType constructors.fields ⇒
      (constructors.number ⇒ AdmittedContainerGeneratedControls.space) ⇒ AdmittedContainerGeneratedControls.space) :=
  .const .construct
def bottom : HOL.Term AdmittedContainerGeneratedControls.Symbol inputContext AdmittedContainerGeneratedControls.space :=
  .const .bottom
def value : HOL.Term AdmittedContainerGeneratedControls.Symbol inputContext AdmittedContainerGeneratedControls.space :=
  .var (.vs .vz)
def index : HOL.Term AdmittedContainerGeneratedControls.Symbol inputContext constructors.index := .var .vz
def member : HOL.Formula AdmittedContainerGeneratedControls.Symbol inputContext :=
  positions.nonbottomMember bottom constructor value index

private theorem member_of_equal_programs
    {Base : Type} {Const : Ty Base → Type} {Γ : Ctx Base}
    {first second : IndexedConstructorGuards.ConstructorPrograms Const Γ}
    (same : first = second)
    (firstPositions : IndexedConstructorGuards.PositionPrograms first)
    (secondPositions : IndexedConstructorGuards.PositionPrograms second)
    (positionsSame : HEq firstPositions secondPositions)
    {space : Ty Base} (bottom : HOL.Term Const Γ space)
    (firstConstructor : HOL.Term Const Γ (first.number ⇒ FiniteConstructorEncoding.payloadType first.fields ⇒
      (first.number ⇒ space) ⇒ space))
    (secondConstructor : HOL.Term Const Γ (second.number ⇒ FiniteConstructorEncoding.payloadType second.fields ⇒
      (second.number ⇒ space) ⇒ space))
    (constructorSame : HEq firstConstructor secondConstructor)
    (value : HOL.Term Const Γ space)
    (firstIndex : HOL.Term Const Γ first.index) (secondIndex : HOL.Term Const Γ second.index)
    (indexSame : HEq firstIndex secondIndex) :
    firstPositions.nonbottomMember bottom firstConstructor value firstIndex =
      secondPositions.nonbottomMember bottom secondConstructor value secondIndex := by
  cases same
  cases positionsSame
  cases constructorSame
  cases indexSame
  rfl

theorem member_source : member = AdmittedContainerInductionControls.member
    (Γ := inputContext) (.var (.vs .vz)) (.var .vz) := by
  exact member_of_equal_programs constructors_source positions Source.positions positions_source bottom
    constructor (AdmittedContainerInductionControls.ctor (Γ := inputContext)) HEq.rfl
    value index (.var .vz) HEq.rfl

def assumptions : List (ClosedFormula AdmittedContainerGeneratedControls.Symbol) :=
  [AdmittedContainerInductionControls.injectivity, AdmittedContainerInductionControls.separation]

def statement : ClosedFormula AdmittedContainerGeneratedControls.Symbol :=
  .all (.all (.imp member (.not (.eq value bottom))))

theorem statement_source : statement = AdmittedContainerInductionControls.statement := by
  unfold statement AdmittedContainerInductionControls.statement
  rw [member_source]
  rfl

def program : ProofSyntax AdmittedContainerGeneratedControls.Symbol assumptions statement := by
  apply ProofSyntax.allI
  apply ProofSyntax.allI
  apply ProofSyntax.castIndices ?_ rfl (positions.nonbottomProof bottom constructor value index)
  rfl

theorem program_free : program.FunctionExtensionalityFree := by
  unfold program
  apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
  exact positions.nonbottomProof_free bottom constructor value index

variable (operations : AdmittedMembershipCompilation.Operations)

def compile := InterpretedCompilation.compile (AdmittedMembershipCompilation.interpretation operations)
  program program_free ReverseTranslation.Naming.empty ("admitted-family-nonbottom", 0)

theorem compiled_conclusion :
    (compile operations).proof.result.sequent.concl =
      ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty
        (ImpredicativeConnectives.expand
          ((AdmittedMembershipCompilation.interpretation operations).term AdmittedContainerInductionControls.statement)) :=
  (compile operations).conclusion_exact.trans
    (congrArg (fun (formula : ClosedFormula AdmittedContainerGeneratedControls.Symbol) =>
      ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty
      (ImpredicativeConnectives.expand ((AdmittedMembershipCompilation.interpretation operations).term formula)))
      statement_source)

#print axioms rows_source
#print axioms constructors_source
#print axioms positions_source
#print axioms statement_source
#print axioms program_free
#print axioms compiled_conclusion

end Mettapedia.Languages.HOLLight.AdmittedNonbottomCompilation
