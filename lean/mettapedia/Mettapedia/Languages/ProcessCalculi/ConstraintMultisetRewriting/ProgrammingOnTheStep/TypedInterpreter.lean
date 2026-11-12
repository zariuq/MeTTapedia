import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ProgrammingOnTheStep.VectorPackage

/-!
# A tiny dependently typed interpreter on the step

A typed object language: types `ty` with the code `tnat`, expressions `exp : ty → U0` with literals
`lit : nat → exp tnat`, values `val : ty → U0`, and the interpreter
`eval : Π (t : ty). exp t → val t`. All constants are rigid, so the package is within the tree's
normalization model, as in `VectorPackage`.

**The interpreter runs** (`eval_admitted`). The rule `eval tnat (lit n) = n`, with the telescope
`n : nat`, fires on the call `eval tnat (lit 3)`, and the solution reads the made row as `3`
(`eval_answer`).

**Its answer never has its declared type** (`return_refused`). The call has type `val tnat`; the
answer `n` has type `nat`. A firing that hands the answer to a hole of the declared type, telling
`(r : val tnat) ≐ (n : nat)`, is refused: `val tnat` and `nat` are types headed by different rigid
constants, equal in no frame (`val_not_nat`). A typed interpreter needs its value types to compute
in conversion (`val tnat ≡ nat`, a large elimination); computed by firings, they never meet.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ProgrammingOnTheStep.TypedInterpreter

open _root_.CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.UniverseLevel
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta
open Interface.DependentFull
open VectorPackage (natN zeroN succN u0 U0 natC zeroC succC collapse universe_typed pi0)

/-! ## The package -/

def tyN : DeclName := .mkSimple "ty"
def tnatN : DeclName := .mkSimple "tnat"
def expN : DeclName := .mkSimple "exp"
def litN : DeclName := .mkSimple "lit"
def valN : DeclName := .mkSimple "val"
def evalN : DeclName := .mkSimple "eval"

def tyC {n : Nat} : Tower.Tm n := .const tyN
def tnatC {n : Nat} : Tower.Tm n := .const tnatN
def expC {n : Nat} (t : Tower.Tm n) : Tower.Tm n := .app (.const expN) t
def litC {n : Nat} (k : Tower.Tm n) : Tower.Tm n := .app (.const litN) k
def valC {n : Nat} (t : Tower.Tm n) : Tower.Tm n := .app (.const valN) t
def evalC {n : Nat} (t e : Tower.Tm n) : Tower.Tm n := .app (.app (.const evalN) t) e

def familyTy : Tower.Tm 0 := .pi tyC U0
def litTy : Tower.Tm 0 := .pi natC (expC tnatC)
def evalTy : Tower.Tm 0 := .pi tyC (.pi (expC (.var 0)) (valC (.var 1)))

def declared (name : DeclName) : Option (Tower.Tm 0) :=
  if name = natN then some U0 else
  if name = zeroN then some natC else
  if name = succN then some (.pi natC natC) else
  if name = tyN then some U0 else
  if name = tnatN then some tyC else
  if name = expN then some familyTy else
  if name = litN then some litTy else
  if name = valN then some familyTy else
  if name = evalN then some evalTy else none

/-- **The package**: the cumulative tower with the interpreter's declarations, no computation. -/
def rules : Rules Tower.Head := { Tower.rules with constantType := declared }

def roles : Roles Tower.Head := fun _ => .rigid

theorem shape : RootShape rules roles where
  spine := fun step => False.elim step
  deterministic := fun step => False.elim step

def levels : LevelModel rules Nat := { TowerModel.levels (L := Nat) (fun _ => 0) with }

def setting : Setting Tower.Head Nat where
  R := rules
  roles := roles
  E := declarative rules
  levels := levels
  shape := shape
  constructors := .of_no_inductive fun _ _ role => by cases role

theorem rigid (name : DeclName) : setting.roles name = .rigid := rfl

theorem laws : setting.E.Laws setting.R setting.roles := declarative_laws roles levels

theorem constants : SemanticConstants setting := SemanticConstants.of_rigid laws fun _ => rfl

theorem facts : FormFacts rules roles := .ofSemantic (S := setting) laws constants

theorem algebra : CumulativeAlgebra rules := { TowerModel.algebra (L := Nat) with }

theorem heads : HeadPreserving rules := by
  intro n Γ h h' A same typing
  obtain ⟨u, headTyping, le⟩ := Typed.generation typing
  change LevelTower.HeadTyping h u at headTyping
  change LevelTower.HeadEq h h' at same
  cases headTyping with
  | legacyGround =>
      cases h' with
      | legacyGround => exact Typed.subsume (.headType .legacyGround) le
      | sort _ => exact same.elim
  | sort l =>
      cases h' with
      | legacyGround => exact same.elim
      | sort r =>
          have raise : rules.cumulative (.sort (.succ r)) (.sort (.succ l)) := by
            intro ν
            show UniverseLevel.LevelOrder.succ (LevelExpr.eval ν r) ≤
              UniverseLevel.LevelOrder.succ (LevelExpr.eval ν l)
            exact UniverseLevel.LevelOrder.succ_le_succ (le_of_eq (same ν).symm)
          exact Typed.subsume (.cumul (.headType (.sort r)) raise) le

theorem roots : RootPreserving rules := by
  intro n Γ l r A _ step
  exact False.elim step

theorem algorithmicConstants : SemanticConstants (algorithmicSetting setting) :=
  SemanticConstants.of_rigid
    (algorithmicSetting_laws (S := setting) laws constants roots heads algebra) fun _ => rfl

theorem complete : AlgorithmicComplete rules roles :=
  AlgorithmicComplete.ofSemantic (S := setting) laws constants roots heads algebra
    algorithmicConstants

instance headEqDecidable : DecidableRel setting.R.headEq := fun left right =>
  LevelTower.instDecidableHeadEq left right

instance universeDecidable (head : Tower.Head) : Decidable (setting.R.isUniverse head) :=
  inferInstanceAs (Decidable (Tower.IsUniverse head))

/-! ## Typing -/

theorem declared_nat : rules.constantType natN = some U0 := by decide
theorem declared_zero : rules.constantType zeroN = some natC := by decide
theorem declared_succ : rules.constantType succN = some (.pi natC natC) := by decide
theorem declared_ty : rules.constantType tyN = some U0 := by decide
theorem declared_tnat : rules.constantType tnatN = some tyC := by decide
theorem declared_exp : rules.constantType expN = some familyTy := by decide
theorem declared_lit : rules.constantType litN = some litTy := by decide
theorem declared_val : rules.constantType valN = some familyTy := by decide
theorem declared_eval : rules.constantType evalN = some evalTy := by decide

theorem collapse' : rules.cumulative (.sort (.max Tower.zero Tower.zero)) (.sort Tower.zero) := by
  change LevelTower.Cumulative (.sort (.max Tower.zero Tower.zero)) (.sort Tower.zero)
  intro valuation
  simp [LevelExpr.eval]

theorem nat_typed {n : Nat} (Γ : Tower.Ctx n) : Typed rules Γ natC U0 :=
  .const declared_nat (.headType (.sort _)) (.sort _)

theorem ty_typed {n : Nat} (Γ : Tower.Ctx n) : Typed rules Γ tyC U0 :=
  .const declared_ty (.headType (.sort _)) (.sort _)

theorem small_pi {n : Nat} {Γ : Tower.Ctx n} {A : Tower.Tm n} {B : Tower.Tm (n + 1)}
    (typedA : Typed rules Γ A U0) (typedB : Typed rules (.snoc Γ A) B U0) : Typed rules Γ (.pi A B) U0 :=
  .cumul (.piForm typedA (.sort _) typedB (.sort _) (.sorts _ _)) collapse'

theorem familyTy_typed : Typed rules .nil familyTy (.head (.sort (.max Tower.zero (.succ Tower.zero)))) :=
  .piForm (ty_typed _) (.sort _) (.headType (.sort _)) (.sort _) (.sorts _ _)

theorem zero_typed {n : Nat} (Γ : Tower.Ctx n) : Typed rules Γ zeroC natC :=
  .const declared_zero (nat_typed .nil) (.sort _)

theorem succ_typed {n : Nat} {Γ : Tower.Ctx n} {t : Tower.Tm n} (typed : Typed rules Γ t natC) :
    Typed rules Γ (succC t) natC :=
  .appElim (.const declared_succ (small_pi (nat_typed _) (nat_typed _)) (.sort _)) typed

theorem tnat_typed {n : Nat} (Γ : Tower.Ctx n) : Typed rules Γ tnatC tyC :=
  .const declared_tnat (ty_typed .nil) (.sort _)

theorem exp_typed {n : Nat} {Γ : Tower.Ctx n} {t : Tower.Tm n} (typed : Typed rules Γ t tyC) :
    Typed rules Γ (expC t) U0 :=
  .appElim (.const declared_exp familyTy_typed (.sort _)) typed

theorem val_typed {n : Nat} {Γ : Tower.Ctx n} {t : Tower.Tm n} (typed : Typed rules Γ t tyC) :
    Typed rules Γ (valC t) U0 :=
  .appElim (.const declared_val familyTy_typed (.sort _)) typed

theorem litTy_typed : Typed rules .nil litTy U0 := small_pi (nat_typed _) (exp_typed (tnat_typed _))

theorem evalTy_typed : Typed rules .nil evalTy U0 :=
  small_pi (ty_typed _) (small_pi (exp_typed (Derivable.var 0)) (val_typed (Derivable.var 1)))

theorem lit_typed {n : Nat} {Γ : Tower.Ctx n} {k : Tower.Tm n} (typed : Typed rules Γ k natC) :
    Typed rules Γ (litC k) (expC tnatC) :=
  .appElim (.const declared_lit litTy_typed (.sort _)) typed

/-! ## The interpreter's rule, firing -/

/-- `3`. -/
def three {n : Nat} : Tower.Tm n := succC (succC (succC zeroC))

theorem three_typed {n : Nat} (Γ : Tower.Ctx n) : Typed rules Γ three natC :=
  succ_typed (succ_typed (succ_typed (zero_typed Γ)))

theorem call_typed {n : Nat} {Γ : Tower.Ctx n} {k : Tower.Tm n} (typed : Typed rules Γ k natC) :
    Typed rules Γ (evalC tnatC (litC k)) (valC tnatC) := by
  have e := Derivable.appElim (Derivable.appElim (.const declared_eval evalTy_typed (.sort _)) (tnat_typed Γ))
    (lit_typed typed)
  exact e

def valOf (Γ : Context rules) : TypeOver Γ := ⟨valC tnatC, u0, .sort _, val_typed (tnat_typed _)⟩
def natOf (Γ : Context rules) : TypeOver Γ := ⟨natC, u0, .sort _, nat_typed _⟩

/-- The call `eval tnat (lit 3) : val tnat`. -/
def callRow : TotalTerm (empty rules) := ⟨valOf _, ⟨evalC tnatC (litC three), call_typed (three_typed _)⟩⟩

def callState : State rules Nat := ⟨empty rules, [], {0}, fun _ => callRow⟩

/-- The frame `n : nat`. -/
abbrev ruleFrame : Context rules := extend (empty rules) (natOf _)

/-- The left side `eval tnat (lit n) : val tnat`. -/
def evalPattern : TotalTerm ruleFrame :=
  ⟨valOf _, ⟨evalC tnatC (litC (.var 0)), call_typed (Derivable.var (0 : Fin 1))⟩⟩

/-- **The rule `eval tnat (lit n) = n`**: take the call, make row `1 : n : nat`. -/
def evalFiring : Firing levels callState where
  helpers := .cons (natOf _) (.nil _)
  taken := [0]
  read := []
  takes := [evalPattern]
  reads := []
  makes := [(1, ⟨natOf _, (.var 0 : Tower.Tm 1)⟩)]
  tells := []
  guards := []
  queries := []

def evalSolution : empty rules ⟶ ruleFrame := pair (toEmpty (empty rules)) ⟨three, three_typed _⟩

theorem evalFiring_information : evalFiring.information = [(evalPattern, evalFiring.row 0)] := rfl

theorem eval_identifies : evalPattern.reindex evalSolution = (evalFiring.row 0).reindex evalSolution :=
  totalTerm_ext (TypeOver.ext rfl rfl) rfl

/-- **The interpreter's rule fires on the call.** -/
theorem eval_admitted : (step levels Nat).Admits evalFiring := by
  refine ⟨⟨List.nodup_singleton _, List.nodup_singleton _, rfl, rfl, fun m member => ?_⟩,
    (enabled_iff evalFiring).mpr ⟨fun o member => ?_, fun _ member => absurd member List.not_mem_nil,
      fun _ _ readToo => absurd readToo List.not_mem_nil, fun o member inside => ?_⟩,
    ⟨empty rules, evalSolution, ?_⟩, ?_⟩
  · obtain rfl := List.mem_singleton.mp member
    exact Derivable.var (0 : Fin 1)
  · obtain rfl := List.mem_singleton.mp member
    exact Finset.mem_singleton_self 0
  · obtain rfl := List.mem_singleton.mp member
    exact absurd (Finset.mem_singleton.mp inside) (by decide)
  · rw [evalFiring_information]
    intro e member
    obtain rfl := List.mem_singleton.mp member
    show (frames levels).E (evalPattern.reindex evalSolution) ((evalFiring.row 0).reindex evalSolution)
    rw [eval_identifies]
    exact ((frames levels).equivalence _).refl _
  · intro b τ _
    exact ⟨fun _ member => absurd member List.not_mem_nil, fun _ member => absurd member List.not_mem_nil⟩

/-- **The answer**: the solution reads the made row as `3`. -/
theorem eval_answer : subst evalSolution.substitution (.var 0 : Tower.Tm 1) = three := rfl

/-! ## The answer and the declared type never meet -/

/-- **`val tnat` and `nat` are equal types in no frame**: they are headed by different rigid
constants. -/
theorem val_not_nat {n : Nat} {Γ : Tower.Ctx n} (formed : CtxFormed rules Γ) :
    ¬ TypeEq rules Γ (valC tnatC) natC := by
  have clash : ContextualDependentRigid.shapeClashes setting.R (valC tnatC : Tower.Tm 0) natC = true := by
    decide
  exact ContextualDependentRigid.not_typeEq_of_shapeClashes (S := setting) rigid facts complete formed
    (ContextualDependentRigid.shapeClashes_subst setting.R (fun i : Fin 0 => i.elim0) clash)

/-- The frame `r : val tnat, n : nat`: a hole of the declared type and an answer. -/
abbrev returnFrame : Context rules := extend (extend (empty rules) (valOf _)) (natOf _)

/-- The empty state. -/
def emptyState : State rules Nat := ⟨empty rules, [], ∅, fun _ => callRow⟩

/-- The hole `r : val tnat`. -/
def holeRow : TotalTerm returnFrame := ⟨valOf _, ⟨.var 1, Derivable.var (1 : Fin 2)⟩⟩

/-- The answer `n : nat`. -/
def answerRow : TotalTerm returnFrame := ⟨natOf _, ⟨.var 0, Derivable.var (0 : Fin 2)⟩⟩

/-- **Hand the answer to a hole of the declared type**: tell `(r : val tnat) ≐ (n : nat)`. -/
def returnFiring : Firing levels emptyState where
  helpers := .cons (valOf _) (.cons (natOf _) (.nil _))
  taken := []
  read := []
  takes := []
  reads := []
  makes := []
  tells := [(holeRow, answerRow)]
  guards := []
  queries := []

/-- **The return is refused**: no solution makes `val tnat` equal to `nat`. -/
theorem return_refused : ¬ (step levels Nat).Admits returnFiring := by
  rintro ⟨-, -, ⟨Δ, σ, solved⟩, -⟩
  have equation := solved _ (List.mem_append_right _ (List.mem_singleton_self _))
  obtain ⟨types, -⟩ := (equivalent_iff levels _ _).mp equation
  exact val_not_nat Δ.formed types

end ProgrammingOnTheStep.TypedInterpreter

#print axioms ProgrammingOnTheStep.TypedInterpreter.eval_admitted
#print axioms ProgrammingOnTheStep.TypedInterpreter.eval_answer
#print axioms ProgrammingOnTheStep.TypedInterpreter.val_not_nat
#print axioms ProgrammingOnTheStep.TypedInterpreter.return_refused

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
