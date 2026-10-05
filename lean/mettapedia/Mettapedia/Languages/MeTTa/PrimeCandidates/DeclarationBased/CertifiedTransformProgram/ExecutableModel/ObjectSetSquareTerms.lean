import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel.ObjectSetSquare
import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel.SNValueSteps
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Impredicative.Consistency.Binders
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Impredicative.Consistency.Coherence

/-!
# The square on code terms

The square between the two readings of the object package's codes (`ObjectSetSquare`) lifts from
the code formers to code terms: for every closed code term built from the code constants over
the carriers of `NumCarrier`, model SN's truth reading of the code holds exactly when the empty
proof lies in the set tower's value of the decoded type `holds c` (`square_code`, for model SN of
the object package `square_code_modelSN`, for its consistency model `square_code_consistency`).

**The code terms** (`CodeTerm`), intrinsically typed by their carriers: variables, the data
`zero`, `suc` and `add`, the code constants `imp`, `all@A` and `eq@A` at every carrier `A`,
application, and abstraction. Each is mapped to an annotated term of the object package
(`CodeTerm.toC`): the constants by their names, and each abstraction annotated by the simple type
of its domain. The erasure of that term is the code, the term model SN reads; its annotated form is
the term the tower evaluates.

**The induction.** Model SN reads a code through weak-head reduction: an abstraction at a generic
carrier is opened at a fresh generic of every meaning, and at the numbers at every term computing
a numeral, in every world reached by a morphism (`Read.lam_gen`, `Read.lam_data`); a sum is read
by computing it, through the recursion of `add` in the reduction. The tower evaluates the
annotated term at an environment of sets. Neither reading is defined by recursion on raw terms of
the package, and the tower needs the domains of abstractions, which raw terms do not carry. The
syntax of code terms gives both what they need: a carrier for every subterm, and an annotation for
every abstraction. The induction is on that syntax, with one meaning (`CodeTerm.meaning`, the
reading over model SN's meanings at the carriers) that both sides compute:

* model SN reads the code, under every substitution of terms reading at the meanings of the free
  variables, at its meaning (`CodeTerm.read`);
* the tower's value of the annotated term, at the sets of the free variables' meanings, is the
  set of its meaning (`CodeTerm.ev_toC`).

The meaning of a sum is the addition of the values of the numbers that the setting's reduction
computes (`addClass`): the class of the sum of representatives. Both reductions of the object
package compute addition (`modelSN_computesAdd`, `consistency_computesAdd`).

At a closed code of `prop` the meaning is a proposition `P`; model SN reads the code at `P`
(`truth_closed`), and the tower's value is `truthCode P` (`ev_closed`), which the decoder `holds`
keeps.

**The scope, exactly.** Every closed code term of the syntax, β-redexes and partial applications
of the code constants included. Two restrictions, each shown needed by a control
(`ObjectSetSquareControls`, `ObjectSetSquareChoice`):

* the carriers are those of `NumCarrier`; at the sets, at `prop → num` and at `num → num` the
  square fails;
* the data are built from variables at the numbers, `zero`, `suc` and `add`; a term of the
  package that model SN computes to a numeral but whose instance is not typed can have another
  value in the tower.

`Classical.choice` enters only through the set layer.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TowerInterpretation
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId
open Presentation
open Presentation.TypedEquality
open Presentation.TypedEquality.Normalization
open Presentation.TypedEquality.Annotated
open Presentation.TypedEquality.Impredicative.Consistency (Carrier Kind Setting Q numClass sucClass
  Truth Read World Morph DataEq dataValue InterpAt Interp levelsBelow NumVal numVal_numeral)
open Mettapedia.Logic.HOL.Embedding
open ZFSetUniverseClosure (CofinalInaccessibles)
open ZFSetDependentProducts (graph)
open ZFSetTraceProducts (traceLam traceApp traceApp_graph_beta)
open ZFSetTraceProofDecoding (truthCode)
open FormationSensitiveHOLInterface (typeAt)
open Mettapedia.Logic

universe u

namespace CodeModel
namespace SetSquare

/-! ## The setting of the object package's codes -/

/-- The setting of a reduction with the object package's numbers and codes. The consistency
model of the object package and the consistency model of its model SN are of this form, each with
its own reduction. -/
def objSetting (rules : Rules Tower.Head) (roles : Roles Tower.Head) : Setting Tower.Head where
  rules := rules
  roles := roles
  zero := zeroN
  suc := sucN
  imp := impN
  allCarrier := allCarrierOf
  eqCarrier := eqCarrierOf

/-! ## Addition of the values of the numbers -/

/-- A setting computes addition when the sum of two terms computing numerals computes the
numeral of the sum. -/
def ComputesAdd (S : Setting Tower.Head) : Prop :=
  ∀ {n : Nat} {x y : Tm Tower.Head n} {i j : Nat}, NumVal S x i → NumVal S y j →
    NumVal S (.app (.app (.const addN) x) y) (i + j)

/-- The sum of two terms related to themselves at the numbers is related to itself. -/
theorem ComputesAdd.related {S : Setting Tower.Head} (hadd : ComputesAdd S) {n : Nat}
    {a b : Tm Tower.Head n} (ra : DataEq S.numerals .num a a) (rb : DataEq S.numerals .num b b) :
    DataEq S.numerals .num (.app (.app (.const addN) a) b) (.app (.app (.const addN) a) b) := by
  obtain ⟨i, va, -⟩ := ra
  obtain ⟨j, vb, -⟩ := rb
  exact ⟨i + j, hadd va vb, hadd va vb⟩

/-- **The addition of the values of the numbers** of a setting that computes addition: the class
of the sum of representatives. -/
def addClass (S : Setting Tower.Head) (hadd : ComputesAdd S) :
    Q S.numerals .num → Q S.numerals .num → Q S.numerals .num :=
  Quot.lift₂ (fun a b => Quot.mk _ ⟨.app (.app (.const addN) a.1) b.1, hadd.related a.2 b.2⟩)
    (fun a _ _ related => Quot.sound (by
      obtain ⟨i, va, -⟩ := a.2
      obtain ⟨k, v₁, v₂⟩ := related
      exact ⟨i + k, hadd va v₁, hadd va v₂⟩))
    (fun _ _ b related => Quot.sound (by
      obtain ⟨j, vb, -⟩ := b.2
      obtain ⟨k, v₁, v₂⟩ := related
      exact ⟨k + j, hadd v₁ vb, hadd v₂ vb⟩))

/-- The addition of the classes of two numerals is the class of the numeral of the sum. -/
theorem addClass_numClass (S : Setting Tower.Head) (hadd : ComputesAdd S) (i j : Nat) :
    addClass S hadd (numClass S.numerals i) (numClass S.numerals j) =
      numClass S.numerals (i + j) :=
  Quot.sound ⟨i + j, hadd (numVal_numeral i) (numVal_numeral j), numVal_numeral (i + j)⟩

/-- The value of a sum is the addition of the values of its summands. -/
theorem dataValue_add {S : Setting Tower.Head} (hadd : ComputesAdd S) {n : Nat}
    {a b : Tm Tower.Head n} (ra : DataEq S.numerals .num a a) (rb : DataEq S.numerals .num b b) :
    dataValue (P := Prop) S.numerals .num (.app (.app (.const addN) a) b) (hadd.related ra rb) =
      addClass S hadd (dataValue (P := Prop) S.numerals .num a ra)
        (dataValue (P := Prop) S.numerals .num b rb) :=
  rfl

/-- **Model SN's reduction computes addition.** -/
theorem modelSN_computesAdd (v : Nat → Nat) : ComputesAdd (tmodelC v).toSetting := by
  intro n x y i j left right
  induction right with
  | zero red =>
      exact left.expand (Relation.ReflTransGen.tail (objectTExt.add_scrutinee v x red) (objectTExt.add_zero_step v x))
  | suc red _ ih =>
      exact .suc (Relation.ReflTransGen.tail (objectTExt.add_scrutinee v x red) (objectTExt.add_suc_step v x _)) ih

/-- **The consistency model's reduction computes addition.** -/
theorem consistency_computesAdd (v : Nat → Nat) : ComputesAdd (model v).toSetting :=
  fun left right => numVal_add v left right

/-! ## Code terms -/

/-- A context of carriers, the newest first. -/
abbrev SCtx : Type := List (Σ k : Kind, NumCarrier k)

/-- A variable of a context at its carrier. -/
inductive SVar : SCtx → {k : Kind} → NumCarrier k → Type where
  | zero {Γ : SCtx} {k : Kind} {A : NumCarrier k} : SVar (⟨k, A⟩ :: Γ) A
  | succ {Γ : SCtx} {k k' : Kind} {A : NumCarrier k} {B : NumCarrier k'} :
      SVar Γ A → SVar (⟨k', B⟩ :: Γ) A

/-- The de Bruijn index of a variable. -/
def SVar.index : {Γ : SCtx} → {k : Kind} → {A : NumCarrier k} → SVar Γ A → Fin Γ.length
  | _, _, _, .zero => 0
  | _, _, _, .succ i => i.index.succ

/-- **The code terms over the carriers of `NumCarrier`**, typed by their carriers: variables,
the data `zero`, `suc` and `add`, the code constants `imp`, `all@A` and `eq@A`, application into a
generic carrier, and abstraction. -/
inductive CodeTerm : SCtx → {k : Kind} → NumCarrier k → Type where
  | var {Γ : SCtx} {k : Kind} {A : NumCarrier k} : SVar Γ A → CodeTerm Γ A
  | zero {Γ : SCtx} : CodeTerm Γ .num
  | suc {Γ : SCtx} : CodeTerm Γ .num → CodeTerm Γ .num
  | add {Γ : SCtx} : CodeTerm Γ .num → CodeTerm Γ .num → CodeTerm Γ .num
  | imp {Γ : SCtx} : CodeTerm Γ (.arr .prop (.arr .prop .prop))
  | all {Γ : SCtx} {k : Kind} (A : NumCarrier k) : CodeTerm Γ (.arr (.arr A .prop) .prop)
  | eq {Γ : SCtx} {k : Kind} (A : NumCarrier k) : CodeTerm Γ (.arr A (.arr A .prop))
  | app {Γ : SCtx} {k : Kind} {A : NumCarrier k} {B : NumCarrier .gen} :
      CodeTerm Γ (.arr A B) → CodeTerm Γ A → CodeTerm Γ B
  | lam {Γ : SCtx} {k : Kind} {A : NumCarrier k} {B : NumCarrier .gen} :
      CodeTerm (⟨k, A⟩ :: Γ) B → CodeTerm Γ (.arr A B)

namespace CodeTerm

/-- `imp p q`. -/
abbrev impOf {Γ : SCtx} (p q : CodeTerm Γ .prop) : CodeTerm Γ .prop := .app (.app .imp p) q

/-- `all@A (λx. body)`. -/
abbrev allOf {Γ : SCtx} {k : Kind} (A : NumCarrier k) (body : CodeTerm (⟨k, A⟩ :: Γ) .prop) :
    CodeTerm Γ .prop :=
  .app (.all A) (.lam body)

/-- `eq@A x y`. -/
abbrev eqOf {Γ : SCtx} {k : Kind} {A : NumCarrier k} (x y : CodeTerm Γ A) : CodeTerm Γ .prop :=
  .app (.app (.eq A) x) y

/-- **The annotated term of a code term**: the constants by their names, and each abstraction
annotated by the simple type of its domain. Its erasure is the code. -/
def toC : {Γ : SCtx} → {k : Kind} → {A : NumCarrier k} → CodeTerm Γ A →
    CTm Tower.Head Γ.length
  | _, _, _, .var i => .var i.index
  | _, _, _, .zero => .const zeroN
  | _, _, _, .suc t => .app (.const sucN) t.toC
  | _, _, _, .add a b => .app (.app (.const addN) a.toC) b.toC
  | _, _, _, .imp => .const impN
  | _, _, _, .all A => .const (SetProfile.allName A.toTy)
  | _, _, _, .eq A => .const (SetProfile.eqName A.toTy)
  | _, _, _, .app f a => .app f.toC a.toC
  | Γ, _, _, @CodeTerm.lam _ _ A _ b =>
      .lam (liftTm (typeAt SetProfile.types Γ.length A.toTy)) b.toC

end CodeTerm

/-! ## The meaning of a code term -/

section Meaning

variable {Head : Type}

/-- Meanings of the variables of a context. -/
abbrev MEnv (S : Setting Head) (Γ : SCtx) : Type :=
  ∀ {k : Kind} {A : NumCarrier k}, SVar Γ A → Val S A

/-- The empty context has no variables. -/
def MEnv.nil {S : Setting Head} : MEnv S [] := fun i => nomatch i

/-- An environment extended by a meaning for the newest variable. -/
def MEnv.cons {S : Setting Head} {Γ : SCtx} {k : Kind} {A : NumCarrier k} (v : Val S A)
    (vals : MEnv S Γ) : MEnv S (⟨k, A⟩ :: Γ)
  | _, _, .zero => v
  | _, _, .succ i => vals i

/-- **The meaning of a code term** over the meanings of the truth reading, with an addition of
the values of the numbers: the class of a numeral, its successor and the addition at the numbers,
and the reading's implication, quantifier and equation for the code constants; application and
abstraction are those of functions of meanings. -/
def CodeTerm.meaning (S : Setting Head)
    (plus : Q S.numerals .num → Q S.numerals .num → Q S.numerals .num) :
    {Γ : SCtx} → {k : Kind} → {A : NumCarrier k} → CodeTerm Γ A → MEnv S Γ → Val S A
  | _, _, _, .var i, vals => vals i
  | _, _, _, .zero, _ => numClass S.numerals 0
  | _, _, _, .suc t, vals => sucClass S.numerals (t.meaning S plus vals)
  | _, _, _, .add a b, vals => plus (a.meaning S plus vals) (b.meaning S plus vals)
  | _, _, _, .imp, _ => fun P Q => S.truthReading.impMeaning P Q
  | _, _, _, .all A, _ => fun φ => S.truthReading.allMeaning A.toCarrier φ
  | _, _, _, .eq A, _ => fun v w => S.truthReading.eqMeaning A.toCarrier v w
  | _, _, _, .app f a, vals => (f.meaning S plus vals) (a.meaning S plus vals)
  | _, _, _, .lam b, vals => fun v => b.meaning S plus (MEnv.cons v vals)

end Meaning

/-! ## Model SN reads a code term at its meaning -/

section Reading

variable {rules : Rules Tower.Head} {roles : Roles Tower.Head}

/-- The terms a substitution assigns to the variables of a context read, in a world, at the
meanings an environment gives them. -/
def ReadsAt {Γ : SCtx} {m : Nat} (ξ : World (objSetting rules roles).truthReading m)
    (σ : Sub Tower.Head Γ.length m) (vals : MEnv (objSetting rules roles) Γ) : Prop :=
  ∀ {k : Kind} {A : NumCarrier k} (i : SVar Γ A),
    Read (objSetting rules roles).truthReading ξ (σ i.index) A.toCarrier (vals i)

/-- Under a binder at a generic carrier, the newest variable reads at a fresh generic. -/
theorem ReadsAt.lift {Γ : SCtx} {m : Nat} {ξ : World (objSetting rules roles).truthReading m}
    {σ : Sub Tower.Head Γ.length m} {vals : MEnv (objSetting rules roles) Γ}
    (reads : ReadsAt ξ σ vals) {A : NumCarrier .gen} (v : Val (objSetting rules roles) A) :
    ReadsAt (ξ.snoc ⟨A.toCarrier, v⟩) (liftSub σ) (MEnv.cons v vals) := by
  intro k' A' i
  cases i with
  | zero => exact Read.generic' _ rfl
  | succ j => exact (reads j).rename (Morph.wk ξ _)

/-- Under a binder at the numbers, the newest variable is a term computing a numeral. -/
theorem ReadsAt.consData {Γ : SCtx} {m : Nat} {ξ : World (objSetting rules roles).truthReading m}
    {σ : Sub Tower.Head Γ.length m} {vals : MEnv (objSetting rules roles) Γ}
    (reads : ReadsAt ξ σ vals) {m' : Nat} {ξ' : World (objSetting rules roles).truthReading m'}
    {ρ : Ren m m'} (morph : Morph ξ ξ' ρ) {s : Tm Tower.Head m'}
    (related : DataEq (objSetting rules roles).numerals .num s s) :
    ReadsAt ξ' (consSub s fun i => Presentation.rename ρ (σ i))
      (MEnv.cons (A := NumCarrier.num) (dataValue (P := Prop) (objSetting rules roles).numerals
        .num s related) vals) := by
  intro k' A' i
  cases i with
  | zero => exact .data related
  | succ j => exact (reads j).rename morph

/-- `all@A` is read at its own carrier. -/
theorem allCarrier_toTy {k : Kind} (A : NumCarrier k) :
    (objSetting rules roles).truthReading.allCarrier (SetProfile.allName A.toTy) =
      some ⟨k, A.toCarrier⟩ := by
  change (SetProfile.allInstance? (SetProfile.allName A.toTy)).map carrierOf = _
  rw [SetProfile.allInstance?_allName, Option.map_some, NumCarrier.carrierOf_toTy]

/-- `eq@A` is read at its own carrier. -/
theorem eqCarrier_toTy {k : Kind} (A : NumCarrier k) :
    (objSetting rules roles).truthReading.eqCarrier (SetProfile.eqName A.toTy) =
      some ⟨k, A.toCarrier⟩ := by
  change (SetProfile.eqInstance? (SetProfile.eqName A.toTy)).map carrierOf = _
  rw [SetProfile.eqInstance?_eqName, Option.map_some, NumCarrier.carrierOf_toTy]

/-- Model SN reads the constant `imp` at implication. -/
theorem read_imp {m : Nat} (ξ : World (objSetting rules roles).truthReading m) :
    Read (objSetting rules roles).truthReading ξ (.const impN)
      (NumCarrier.arr .prop (.arr .prop .prop)).toCarrier
      (fun P Q => (objSetting rules roles).truthReading.impMeaning P Q) :=
  .genericArg fun _ => .genericArg fun _ => .prop
    (.imp .refl (Read.prop_inv (Read.generic' _ rfl)) (Read.prop_inv (Read.generic' _ rfl)))

/-- Model SN reads the constant `all@A` at the quantifier over the meanings at `A`. -/
theorem read_all {m : Nat} (ξ : World (objSetting rules roles).truthReading m) {k : Kind}
    (A : NumCarrier k) :
    Read (objSetting rules roles).truthReading ξ (.const (SetProfile.allName A.toTy))
      (NumCarrier.arr (.arr A .prop) .prop).toCarrier
      (fun φ => (objSetting rules roles).truthReading.allMeaning A.toCarrier φ) :=
  .genericArg fun _ => .prop (.all (allCarrier_toTy A) .refl (Read.generic' _ rfl))

/-- Model SN reads `eq@A` at a generic carrier at the equation of meanings. -/
theorem read_eq_gen {m : Nat} (ξ : World (objSetting rules roles).truthReading m)
    (A : NumCarrier .gen) :
    Read (objSetting rules roles).truthReading ξ (.const (SetProfile.eqName A.toTy))
      (NumCarrier.arr A (.arr A .prop)).toCarrier
      (fun v w => (objSetting rules roles).truthReading.eqMeaning A.toCarrier v w) :=
  .genericArg fun _ => .genericArg fun _ => .prop
    (.eq (eqCarrier_toTy A) .refl (Read.generic' _ rfl) (Read.generic' _ rfl))

/-- Model SN reads `eq@num` at the equation of values of the numbers. -/
theorem read_eq_num {m : Nat} (ξ : World (objSetting rules roles).truthReading m) :
    Read (objSetting rules roles).truthReading ξ (.const (SetProfile.eqName NumCarrier.num.toTy))
      (NumCarrier.arr .num (.arr .num .prop)).toCarrier
      (fun v w => (objSetting rules roles).truthReading.eqMeaning Carrier.num v w) :=
  .dataArg fun {_ _ _} _ {_} related => .dataArg fun {_ _ ρ'} _ {_} related' => .prop
    (.eq (eqCarrier_toTy .num) .refl (Read.data_rename related ρ') (.data related'))

/-- Model SN reads `eq@A` at the equation of meanings at `A`. -/
theorem read_eq {m : Nat} (ξ : World (objSetting rules roles).truthReading m) :
    ∀ {k : Kind} (A : NumCarrier k),
      Read (objSetting rules roles).truthReading ξ (.const (SetProfile.eqName A.toTy))
        (NumCarrier.arr A (.arr A .prop)).toCarrier
        (fun v w => (objSetting rules roles).truthReading.eqMeaning A.toCarrier v w)
  | _, .prop => read_eq_gen ξ .prop
  | _, .arr A B => read_eq_gen ξ (.arr A B)
  | _, .num => read_eq_num ξ

variable (hadd : ComputesAdd (objSetting rules roles))

/-- **Model SN reads a code term at its meaning**, under every substitution whose terms read at
the meanings of the free variables, with sums read by the addition the reduction computes. -/
theorem CodeTerm.read {Γ : SCtx} {k : Kind} {A : NumCarrier k} (t : CodeTerm Γ A) :
    ∀ {m : Nat} {ξ : World (objSetting rules roles).truthReading m}
      {σ : Sub Tower.Head Γ.length m} {vals : MEnv (objSetting rules roles) Γ},
      ReadsAt ξ σ vals →
      Read (objSetting rules roles).truthReading ξ (Presentation.subst σ t.toC.erase) A.toCarrier
        (t.meaning (objSetting rules roles) (addClass _ hadd) vals) := by
  induction t with
  | var i => exact fun reads => reads i
  | zero => exact fun _ => .data DataEq.zero
  | suc t ih =>
      intro m ξ σ vals reads
      obtain ⟨related, value⟩ := Read.data_inv (ih reads)
      show Read _ ξ (.app (.const sucN) (Presentation.subst σ t.toC.erase)) Carrier.num
        (sucClass (objSetting rules roles).numerals (t.meaning _ _ vals))
      rw [value]
      exact .data (DataEq.suc related)
  | add a b iha ihb =>
      intro m ξ σ vals reads
      obtain ⟨ra, va⟩ := Read.data_inv (iha reads)
      obtain ⟨rb, vb⟩ := Read.data_inv (ihb reads)
      have value : (CodeTerm.add a b).meaning (objSetting rules roles) (addClass _ hadd) vals =
          dataValue (P := Prop) (objSetting rules roles).numerals .num
            (.app (.app (.const addN) (Presentation.subst σ a.toC.erase))
              (Presentation.subst σ b.toC.erase)) (hadd.related ra rb) := by
        show addClass _ hadd (a.meaning _ _ vals) (b.meaning _ _ vals) = _
        rw [va, vb]
        rfl
      rw [value]
      exact .data (hadd.related ra rb)
  | imp => exact fun _ => read_imp _
  | all A => exact fun _ => read_all _ A
  | eq A => exact fun _ => read_eq _ A
  | app f a ihf iha => exact fun reads => Read.app (ihf reads) (iha reads)
  | @lam Γ k A B b ih =>
      intro m ξ σ vals reads
      cases A with
      | prop => exact Read.lam_gen fun v => ih (reads.lift v)
      | arr A₁ B₁ => exact Read.lam_gen fun v => ih (reads.lift v)
      | num =>
          exact Read.lam_data fun {_ _ _} morph {_} related => ih (reads.consData morph related)

/-- **Model SN reads a closed code at its meaning.** -/
theorem truth_closed (φ : CodeTerm [] .prop) :
    Truth (objSetting rules roles).truthReading World.closed φ.toC.erase
      (φ.meaning (objSetting rules roles) (addClass _ hadd) MEnv.nil) := by
  have read := CodeTerm.read hadd φ (σ := Presentation.ids) (ξ := World.closed)
    (vals := MEnv.nil) (fun i => nomatch i)
  rw [Presentation.subst_ids] at read
  exact Read.prop_inv read

end Reading

/-! ## The tower's value of a code term is the set of its meaning -/

section Tower

variable (h : CofinalInaccessibles.{u}) {Head : Type} {S : Setting Head} (laws : S.Laws)

/-- An environment of sets matches an environment of meanings when each variable's set is the
set of its meaning. -/
def EnvMatch {Γ : SCtx} (vals : MEnv S Γ) (η : Env.{u} Γ.length) : Prop :=
  ∀ {k : Kind} {A : NumCarrier k} (i : SVar Γ A), η i.index = (valEquiv laws A (vals i)).1

theorem EnvMatch.cons {Γ : SCtx} {vals : MEnv S Γ} {η : Env.{u} Γ.length}
    (matched : EnvMatch laws vals η) {k : Kind} {A : NumCarrier k} (v : Val S A) :
    EnvMatch laws (MEnv.cons v vals) (extend η (valEquiv laws A v).1) := by
  intro k' A' i
  cases i with
  | zero => rfl
  | succ j => exact matched j

variable {plus : Q S.numerals .num → Q S.numerals .num → Q S.numerals .num}
  (plusNumerals : ∀ i j, plus (numClass S.numerals i) (numClass S.numerals j) =
    numClass S.numerals (i + j))

include plusNumerals in
/-- **The tower's value of a code term is the set of its meaning**, at every environment of
sets matching an environment of meanings, for an addition that adds numerals. -/
theorem CodeTerm.ev_toC {Γ : SCtx} {k : Kind} {A : NumCarrier k} (t : CodeTerm Γ A) :
    ∀ {vals : MEnv S Γ} {η : Env.{u} Γ.length}, EnvMatch laws vals η →
      ev (objHeads h) (objectSetConsts h) t.toC η =
        (valEquiv laws A (t.meaning S plus vals)).1 := by
  induction t with
  | var i => exact fun matched => matched i
  | zero =>
      intro vals η _
      show objectSetConsts h zeroN = _
      rw [setConst_zero h]
      exact (valEquiv_numClass laws 0).symm
  | suc t ih =>
      intro vals η matched
      show traceApp (objectSetConsts h sucN) (ev (objHeads h) (objectSetConsts h) t.toC η) = _
      rw [ih matched, suc_apply h (valEquiv laws .num _).2]
      exact (valEquiv_sucClass laws _).symm
  | add a b iha ihb =>
      intro vals η matched
      show traceApp (traceApp (objectSetConsts h addN)
        (ev (objHeads h) (objectSetConsts h) a.toC η))
        (ev (objHeads h) (objectSetConsts h) b.toC η) =
          (valEquiv laws .num (plus (a.meaning S plus vals) (b.meaning S plus vals))).1
      rw [iha matched, ihb matched]
      obtain ⟨i, hi⟩ := Presentation.TypedEquality.Impredicative.Consistency.Q.eq_numClass
        (a.meaning S plus vals)
      obtain ⟨j, hj⟩ := Presentation.TypedEquality.Impredicative.Consistency.Q.eq_numClass
        (b.meaning S plus vals)
      rw [hi, hj, plusNumerals, valEquiv_numClass, valEquiv_numClass, valEquiv_numClass,
        add_apply h (numeral_mem_omega i) (numeral_mem_omega j), natOf_numeral, natOf_numeral]
  | imp => exact fun _ => impConst_square h laws
  | all A => exact fun _ => allConst_square h laws A
  | eq A => exact fun _ => eqConst_square h laws A
  | app f a ihf iha =>
      intro vals η matched
      show traceApp (ev (objHeads h) (objectSetConsts h) f.toC η)
        (ev (objHeads h) (objectSetConsts h) a.toC η) = _
      rw [ihf matched, iha matched, valEquiv_arr_apply]
      rfl
  | @lam Γ k A B b ih =>
      intro vals η matched
      show traceLam (graph (ev (objHeads h) (objectSetConsts h)
          (liftTm (typeAt SetProfile.types Γ.length A.toTy)) η)
          fun x => ev (objHeads h) (objectSetConsts h) b.toC (extend η x)) = _
      rw [ev_objTypeAt h]
      apply eq_valEquiv_arr laws A B
      · exact traceLam_graph_mem fun x hx => by
          obtain ⟨v, rfl⟩ := exists_valEquiv laws A hx
          rw [ih (matched.cons laws v)]
          exact (valEquiv laws B _).2
      · intro v
        rw [traceApp_graph_beta _ (valEquiv laws A v).2, ih (matched.cons laws v)]
        rfl

include laws plusNumerals in
/-- **The tower's value of a closed code is the truth value of its meaning.** -/
theorem ev_closed (φ : CodeTerm [] .prop) :
    ev (objHeads h) (objectSetConsts h) φ.toC Fin.elim0 =
      truthCode (φ.meaning S plus MEnv.nil) :=
  φ.ev_toC h laws plusNumerals (vals := MEnv.nil) fun i => nomatch i

end Tower

/-! ## The square on code terms -/

section Square

variable (h : CofinalInaccessibles.{u})

/-- **Model SN's side**: the truth reading holds of a closed code exactly when its meaning
does. -/
theorem truth_holds_iff {rules : Rules Tower.Head} {roles : Roles Tower.Head}
    (laws : (objSetting rules roles).Laws) (hadd : ComputesAdd (objSetting rules roles))
    (φ : CodeTerm [] .prop) :
    (∃ P, Truth (objSetting rules roles).truthReading World.closed φ.toC.erase P ∧ P) ↔
      φ.meaning (objSetting rules roles) (addClass _ hadd) MEnv.nil :=
  Truth.holds_iff laws.truthReading (truth_closed hadd φ)

/-- **The tower's side**: the empty proof lies in the value of `holds c` exactly when the
meaning of the closed code `c` holds, for the meanings of any setting with laws and an addition
that adds numerals. -/
theorem tower_holds_iff {Head : Type} {S : Setting Head} (laws : S.Laws)
    {plus : Q S.numerals .num → Q S.numerals .num → Q S.numerals .num}
    (plusNumerals : ∀ i j, plus (numClass S.numerals i) (numClass S.numerals j) =
      numClass S.numerals (i + j))
    (φ : CodeTerm [] .prop) :
    (∅ : ZFSet.{u}) ∈ ev (objHeads h) (objectSetConsts h)
        (CTm.app (.const holdsN) φ.toC) Fin.elim0 ↔ φ.meaning S plus MEnv.nil := by
  show (∅ : ZFSet.{u}) ∈ traceApp (objectSetConsts h holdsN)
    (ev (objHeads h) (objectSetConsts h) φ.toC Fin.elim0) ↔ _
  rw [ev_closed h laws plusNumerals φ, holds_apply h (Square.truthCode_mem_omega _),
    Square.square_truth_iff]

/-- **The square on code terms.** For every closed code term over the carriers of `NumCarrier`,
the truth reading of a setting with the object package's names, whose reduction computes
addition, holds of the code exactly when the empty proof lies in the tower's value of the decoded
type `holds c`: the value of `c` is the true truth value. Both are the truth of the code's
meaning. -/
theorem square_code {rules : Rules Tower.Head} {roles : Roles Tower.Head}
    (laws : (objSetting rules roles).Laws) (hadd : ComputesAdd (objSetting rules roles))
    (φ : CodeTerm [] .prop) :
    (∃ P, Truth (objSetting rules roles).truthReading World.closed φ.toC.erase P ∧ P) ↔
      (∅ : ZFSet.{u}) ∈ ev (objHeads h) (objectSetConsts h)
        (CTm.app (.const holdsN) φ.toC) Fin.elim0 :=
  (truth_holds_iff laws hadd φ).trans
    (tower_holds_iff h laws (addClass_numClass _ hadd) φ).symm

/-- **The square on code terms for model SN of the object package**: model SN reads codes by the
truth reading of its consistency model, the transport value model `tmodelC`. -/
theorem square_code_modelSN (v : Nat → Nat) (φ : CodeTerm [] .prop) :
    (∃ P, Truth (vmodel v).toModel.reading World.closed φ.toC.erase P ∧ P) ↔
      (∅ : ZFSet.{u}) ∈ ev (objHeads h) (objectSetConsts h)
        (CTm.app (.const holdsN) φ.toC) Fin.elim0 :=
  square_code (rules := tmodelRules v) (roles := tmodelRoles) h (tmodelC_laws v).truth
    (modelSN_computesAdd v) φ

/-- **The square on code terms for the consistency model of the object package.** -/
theorem square_code_consistency (v : Nat → Nat) (φ : CodeTerm [] .prop) :
    (∃ P, Truth (model v).reading World.closed φ.toC.erase P ∧ P) ↔
      (∅ : ZFSet.{u}) ∈ ev (objHeads h) (objectSetConsts h)
        (CTm.app (.const holdsN) φ.toC) Fin.elim0 :=
  square_code (rules := modelRules) (roles := modelRoles) h (model_laws v).truth
    (consistency_computesAdd v) φ

/-- **The decoded type.** Model SN's consistency model interprets the type `holds c` of a closed
code by the relation that relates all terms when the empty proof lies in the tower's value of
`holds c`, and no terms otherwise. -/
theorem interp_holds_modelSN (v : Nat → Nat) (l : Nat) (φ : CodeTerm [] .prop) :
    InterpAt (vmodel v).toModel l World.closed (.app (.const holdsN) φ.toC.erase)
      (fun _ _ => (∅ : ZFSet.{u}) ∈ ev (objHeads h) (objectSetConsts h)
        (CTm.app (.const holdsN) φ.toC) Fin.elim0) := by
  have interp := Interp.holds (M := (vmodel v).toModel) (l := l)
    (below := levelsBelow (vmodel v).toModel l) (ξ := World.closed) (A := .app (.const holdsN)
      φ.toC.erase) .refl
      ⟨_, truth_closed (rules := tmodelRules v) (roles := tmodelRoles) (modelSN_computesAdd v) φ⟩
  have same : (fun _ _ : Tm Tower.Head 0 =>
      ∃ P, Truth (vmodel v).toModel.reading World.closed φ.toC.erase P ∧ P) =
      (fun _ _ => (∅ : ZFSet.{u}) ∈ ev (objHeads h) (objectSetConsts h)
        (CTm.app (.const holdsN) φ.toC) Fin.elim0) := by
    funext _ _
    exact propext (square_code_modelSN h v φ)
  rw [same] at interp
  exact interp

end Square

end SetSquare
end CodeModel

end Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel
