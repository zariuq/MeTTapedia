import Mettapedia.OSLF.NativeTypes.Instances.MeTTaHE.FrontDoor
import Mettapedia.OSLF.NativeTypes.Instances.PeTTa.FrontDoor
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.DeclaredReadings
import Mettapedia.Languages.MeTTa.PeTTa.BoundCallControls

/-!
# Controls: the MeTTa dialects at the front door

HE MeTTa and PeTTa asked through the front door `ask`:

- **HE MeTTa**, with no relations supplied: the state `⟨InterpFunc(ExprNil, AtomType, UndefinedType) | space(ExprNil) |
  Empty⟩` steps to `⟨Return(ExprNil) | … | …⟩` by the premise-free rule `IF_Nil`, so it is not stuck, while the returned
  state has no step (kernel-evaluated: `he_interpNil_returns`, `he_interpNil_not_stuck`, `he_returned_stuck`).
- **PeTTa**, on the bound-call fixture program (`BoundCallControls`): its initial configuration has a step, is not
  stuck, and steps to exactly the configuration its executable evaluator `Eval.step` computes (`#guard`).
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Instances.MeTTaDialectControls

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine (RelationEnv)
open Mettapedia.OSLF.NativeTypes.GeneratedLogic
open Mettapedia.OSLF.NativeTypes.GeneratedLogic.DeclaredReadings (verdictOf)
open Mettapedia.Languages.MeTTa.HE.LanguageDef (mettaHE)
open Mettapedia.Languages.MeTTa.PeTTa

/-- A proved verdict of the front door holds. -/
theorem sat_of_verdict {relEnv : RelationEnv} {language : LanguageDef} {fuel rounds : ℕ} {formula : Formula 0}
    {term : Pattern} (decided : verdictOf (ask relEnv [] language fuel formula term none rounds) = some true) :
    (referenceStructure relEnv language).sat Env.closed formula term := by
  cases answered : ask relEnv [] language fuel formula term none rounds with
  | proved _ => exact ask_proved answered
  | refuted _ => simp [answered, verdictOf] at decided
  | unknown _ => simp [answered, verdictOf] at decided

/-- A refuted verdict of the front door fails. -/
theorem not_sat_of_verdict {relEnv : RelationEnv} {language : LanguageDef} {fuel rounds : ℕ} {formula : Formula 0}
    {term : Pattern} (decided : verdictOf (ask relEnv [] language fuel formula term none rounds) = some false) :
    ¬ (referenceStructure relEnv language).sat Env.closed formula term := by
  cases answered : ask relEnv [] language fuel formula term none rounds with
  | proved _ => simp [answered, verdictOf] at decided
  | refuted _ => exact ask_refuted answered
  | unknown _ => simp [answered, verdictOf] at decided

/-! ## HE MeTTa -/

def emptySpace : Pattern := .apply "Space" [.apply "ExprNil" []]

def interpNil : Pattern :=
  .apply "State" [.apply "InterpFunc" [.apply "ExprNil" [], .apply "AtomType" [], .apply "UndefinedType" []], emptySpace,
    .apply "Empty" []]

def returned : Pattern := .apply "State" [.apply "Return" [.apply "ExprNil" []], emptySpace, .apply "Empty" []]

theorem he_returns_row :
    verdictOf (ask RelationEnv.empty [] mettaHE 4 (.possibly .any (.is returned)) interpNil none 2) = some true := by
  decide +kernel

theorem he_not_stuck_row :
    verdictOf (ask RelationEnv.empty [] mettaHE 4 (.necessarily .any .bot) interpNil none 2) = some false := by
  decide +kernel

theorem he_returned_row :
    verdictOf (ask RelationEnv.empty [] mettaHE 4 (.possibly .any .top) returned none 2) = some false := by
  decide +kernel

/-- **The empty function application returns**, at the front door. -/
theorem he_interpNil_returns : (MeTTaHE.Machine RelationEnv.empty).sat Env.closed (.possibly .any (.is returned)) interpNil :=
  sat_of_verdict he_returns_row

/-- **It is not stuck.** -/
theorem he_interpNil_not_stuck : ¬ (MeTTaHE.Machine RelationEnv.empty).sat Env.closed (.necessarily .any .bot) interpNil :=
  not_sat_of_verdict he_not_stuck_row

/-- **The returned state has no step without relations.** -/
theorem he_returned_stuck : ¬ (MeTTaHE.Machine RelationEnv.empty).sat Env.closed (.possibly .any .top) returned :=
  not_sat_of_verdict he_returned_row

/-! ## PeTTa -/

/-- The bound-call fixture's initial configuration, encoded. -/
def initial : Pattern := ConfigurationEncoding.encode BoundCallControls.initial []

/-- What PeTTa's executable evaluator computes from it, encoded. -/
def evaluated : Option Pattern :=
  (Eval.step BoundCallControls.program BoundCallControls.initial).map fun after =>
    ConfigurationEncoding.encode after (ConfigurationEncoding.cellSupportAfter BoundCallControls.initial [])

/-- The front door asked about the fixture program. -/
def askPeTTa (formula : Formula 0) (term : Pattern) : Option Bool :=
  verdictOf (ask (ConfigurationLanguageDef.relationEnv BoundCallControls.program) [] ConfigurationLanguageDef.language 4
    formula term none 2)

#guard askPeTTa (.possibly .any .top) initial = some true
#guard askPeTTa (.necessarily .any .bot) initial = some false
#guard evaluated.isSome
#guard (evaluated.map fun target => askPeTTa (.possibly .any (.is target)) initial) = some (some true)

end Mettapedia.OSLF.NativeTypes.Instances.MeTTaDialectControls
