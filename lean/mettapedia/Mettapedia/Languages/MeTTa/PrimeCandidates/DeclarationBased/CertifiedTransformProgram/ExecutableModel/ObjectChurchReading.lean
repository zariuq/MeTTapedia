import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel.ObjectChurchRelation
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Annotated.Soundness
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Annotated.CodeDecoding
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Impredicative.Domain.ChurchDefinitions
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Impredicative.Domain.AlignedEliminator

/-!
# The reading of the object package in the domain

Every universe head denotes the universe and the ground head a ground type
(`objectHead`). Every declared constant denotes its **Church constant**: a function,
projected onto the denotation of the constant's annotated declared type
(`stageValue`). The functions (`ObjConst.raw`) are

* the numbers, the sets and the type of proposition codes: the numbers, a ground type
  and the universe of codes; zero, and the successor;
* `add`, `pow`, `num-rec` and `iterCert`: numeral recursion. The declared type of
  `num-rec` is the recursor's annotated type (`liftTm_numRecType`). The iterator's
  recursion is function-valued: its successor step receives the recursive value,
  projected onto the iterator's type at a count (`iterSucc`);
* the identity eliminator: the method at the point of a reflexivity path
  (`jAlignedRaw`), at its declared type, the eliminator's annotated type at the lowest
  universe (`liftTm_jType`);
* the definitions by one equation (`eqAt`, `sucMove`, `keepCert`, `transportCert`,
  `composeCert`, `returnIter`, `sucStep`): the abstraction of the elaborated right
  side over the annotated telescope (`defConst`);
* the decoder, implication, and the quantifier and equation codes at every simple
  type: the identity on codes, the dependent function type with a constant family,
  the quantifier over the simple type's denotation (`simpleI`), and the identity type.

A declared type mentions earlier constants, and a definition's right side mentions
constants of earlier stages (`ObjConst.stage`). The reading is built stage by stage
(`valUpTo`), each stage reading its constants in the reading of the stages before;
the result is a fixed point (`objectChurchReading_const`): every constant denotes its
Church constant in the whole reading.

So a declared constant denotes an element of the denotation of its declared type
(`objectChurchReading_constants`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId
open Mettapedia.TypeTheory.UniverseLevel
open Presentation
open Presentation.TypedEquality
open Presentation.TypedEquality.Normalization
open Presentation.TypedEquality.Annotated
open Presentation.TypedEquality.Impredicative.Domain
open Presentation.TypedEquality.Impredicative.Domain.Ideal (projT TypeGenerated principal univIdeal
  codesIdeal natI zeroI groundI cpi csigma clam instPi SpineTyped natRec former ident)
open TelescopeAbstraction (applyClosed)
open FormationSensitiveHOLInterface (typeAt)
open Package (jName numRecName eqAtName sucMoveName keepName transportName composeName
  iterName returnIterName sucStepName numT U0 eqAtTelescope transportTelescope composeTelescope)
open Mettapedia.Logic

namespace CodeModel

/-! ## The constants -/

/-- The constants of the object package, as the domain reads them. -/
inductive ObjConst where
  | num | set | prop | zero | suc | add | power | pow | numRec | j | eqAt | sucMove | keep
  | transport | compose | iter | returnIter | sucStep | holds | imp
  | all (type : HOL.Ty SetProfile.SetBase)
  | eq (type : HOL.Ty SetProfile.SetBase)
  | other
  deriving DecidableEq

/-- The constant a name denotes. -/
def objConst (c : DeclName) : ObjConst :=
  match SetProfile.allInstance? c with
  | some type => .all type
  | none =>
      match SetProfile.eqInstance? c with
      | some type => .eq type
      | none =>
          if c = numN then .num else if c = setN then .set else if c = propN then .prop
          else if c = zeroN then .zero else if c = sucN then .suc else if c = addN then .add
          else if c = powerN then .power else if c = powN then .pow
          else if c = numRecName then .numRec else if c = jName then .j
          else if c = eqAtName then .eqAt else if c = sucMoveName then .sucMove
          else if c = keepName then .keep else if c = transportName then .transport
          else if c = composeName then .compose else if c = iterName then .iter
          else if c = returnIterName then .returnIter else if c = sucStepName then .sucStep
          else if c = holdsN then .holds else if c = impN then .imp else .other

theorem objConst_allName (type : HOL.Ty SetProfile.SetBase) :
    objConst (SetProfile.allName type) = .all type := by
  simp only [objConst, SetProfile.allInstance?_allName]

theorem objConst_eqName (type : HOL.Ty SetProfile.SetBase) :
    objConst (SetProfile.eqName type) = .eq type := by
  simp only [objConst, SetProfile.allInstance?_eqName, SetProfile.eqInstance?_eqName]

/-- The stage at which a constant is read: after the constants its declared type and
its definition mention. -/
def ObjConst.stage : ObjConst → Nat
  | .num | .set | .prop | .other => 0
  | .zero | .suc | .power | .j | .keep | .transport | .compose | .holds | .imp | .all _
  | .eq _ => 1
  | .add | .pow | .numRec | .iter => 2
  | .eqAt => 3
  | .sucMove | .returnIter => 4
  | .sucStep => 5

theorem ObjConst.stage_le : ∀ tag : ObjConst, tag.stage ≤ 5 := by
  intro tag
  cases tag <;> exact Nat.le_of_ble_eq_true rfl

/-- Whether every constant a term mentions is read before stage `s`. -/
def stagedBelow (s : Nat) {n : Nat} (t : CTm Tower.Head n) : Bool :=
  (termConsts t).all fun c => decide ((objConst c).stage < s)

theorem stagedBelow_spec {s n : Nat} {t : CTm Tower.Head n} (h : stagedBelow s t = true) :
    ∀ c ∈ termConsts t, (objConst c).stage < s := by
  simpa [stagedBelow] using h

/-! ## The simple types -/

/-- The denotation of a simple type of the profile. -/
def simpleI : HOL.Ty SetProfile.SetBase → Ideal
  | .prop => codesIdeal
  | .base .num => natI
  | .base .set => groundI
  | .arr a b => cpi (simpleI a) fun _ => simpleI b

theorem typeGenerated_simpleI : ∀ type : HOL.Ty SetProfile.SetBase, TypeGenerated (simpleI type)
  | .prop => Ideal.typeGenerated_codesIdeal
  | .base .num => Ideal.typeGenerated_natI
  | .base .set => Ideal.typeGenerated_groundI
  | .arr a b => Ideal.typeGenerated_cpi (Ideal.Cont.const _) (typeGenerated_simpleI a)
      fun _ _ => typeGenerated_simpleI b

/-- A simple type, annotated, denotes its denotation in every reading of the numbers, the
sets and the codes. -/
theorem cinterp_typeAt {Rd : Reading Tower.Head} (hprop : Rd.const propN = codesIdeal)
    (hnum : Rd.const numN = natI) (hset : Rd.const setN = groundI) :
    ∀ (type : HOL.Ty SetProfile.SetBase) {n : Nat} (ρ : Env n),
      cinterp Rd (liftTm (typeAt SetProfile.types n type)) ρ =
        simpleI type
  | .prop, _, _ => hprop
  | .base .num, _, _ => hnum
  | .base .set, _, _ => hset
  | .arr a b, n, ρ => by
      show cpi (cinterp Rd (liftTm (typeAt SetProfile.types n a)) ρ)
          (fun y => cinterp Rd
            (liftTm (typeAt SetProfile.types (n + 1) b))
            (Env.cons y ρ)) = cpi (simpleI a) fun _ => simpleI b
      rw [cinterp_typeAt hprop hnum hset a ρ]
      congr 1
      funext y
      exact cinterp_typeAt hprop hnum hset b (Env.cons y ρ)

/-- The constants of a simple type are the codes, the numbers and the sets. -/
theorem termConsts_typeAt :
    ∀ (type : HOL.Ty SetProfile.SetBase) {n : Nat} {c : DeclName},
      c ∈ termConsts (liftTm (typeAt SetProfile.types n type) :
        CTm Tower.Head n) → c = propN ∨ c = numN ∨ c = setN
  | .prop, _, _, h => .inl (List.mem_singleton.1 h)
  | .base .num, _, _, h => .inr (.inl (List.mem_singleton.1 h))
  | .base .set, _, _, h => .inr (.inr (List.mem_singleton.1 h))
  | .arr a b, n, _, h => by
      rcases List.mem_append.1 h with h | h
      · exact termConsts_typeAt a h
      · exact termConsts_typeAt b (n := n + 1) h

theorem stage_typeAt {type : HOL.Ty SetProfile.SetBase} {n : Nat} {c : DeclName}
    (h : c ∈ termConsts (liftTm (typeAt SetProfile.types n type) :
      CTm Tower.Head n)) : (objConst c).stage = 0 := by
  rcases termConsts_typeAt type h with rfl | rfl | rfl <;> decide

/-! ## The functions of the constants -/

/-- The names the numeral recursor's declared type refers to. -/
def numNames : NumNames Tower.Head := ⟨.sort Tower.zero, numN, zeroN, sucN⟩

/-- The function of addition, by numeral recursion on its second argument with the
successor `s`. -/
def addRaw (s : Ideal) : Ideal :=
  Ideal.lam fun N => Ideal.lam fun M =>
    natRec (principal N) (fun _ r => Ideal.app s r) (principal M)

/-- The function of the power set: the least element. -/
def powerRaw : Ideal := Ideal.lam fun _ => Ideal.bot

/-- The function of the iterated power set, by numeral recursion on its first argument
with the power set `w`. -/
def powRaw (w : Ideal) : Ideal :=
  Ideal.lam fun N => Ideal.lam fun X =>
    natRec (principal X) (fun _ r => Ideal.app w r) (principal N)

/-- The step type `Π (x : A). P x → Σ (y : A). P y` over the carrier `A` and the family
`P`, annotated. -/
abbrev cStep {n : Nat} : CTm Tower.Head (n + 2) :=
  .pi (.var 1) (.pi (.app (.var 1) (.var 0)) (.sigma (.var 3) (.app (.var 3) (.var 0))))

/-- The iterator's parameters after its count: the carrier, the family, the step, the
value and its evidence. -/
def iterTele : CCtx Tower.Head 5 :=
  .snoc (.snoc (.snoc (.snoc (.snoc .nil cU0) (.pi (.var 0) cU0)) cStep) (.var 2))
    (.app (.var 2) (.var 0))

/-- The iterator's codomain, `Σ (y : A). P y`. -/
abbrev iterCod : CTm Tower.Head 5 := .sigma (.var 4) (.app (.var 4) (.var 0))

/-- The type of the iterator at a count. -/
def iterTail : CTm Tower.Head 0 := pisCtx iterTele iterCod

/-- The parameters of the iterator's successor step: the recursive value, then the
iterator's parameters after its count. -/
def iterStepTele : CCtx Tower.Head 6 :=
  .snoc (.snoc (.snoc (.snoc (.snoc (.snoc .nil iterTail) cU0) (.pi (.var 0) cU0)) cStep)
    (.var 2)) (.app (.var 2) (.var 0))

/-- The body of the iterator's successor step: the step at the value and its evidence,
and the recursive value at the carrier, the family, the step and the components of
that pack. -/
def iterStepBody : CTm Tower.Head 6 :=
  .app (.lam (.sigma (.var 4) (.app (.var 4) (.var 0)))
      (.app (.app (.app (.app (.app (.var 6) (.var 5)) (.var 4)) (.var 3)) (.fst (.var 0)))
        (.snd (.var 0))))
    (.app (.app (.var 2) (.var 1)) (.var 0))

/-- The iterator at zero: `λ A P step x e. (x, e)`. -/
def iterZero (Rd : Reading Tower.Head) : Ideal :=
  cinterp Rd (lamsCtx iterTele (.pair (.var 1) (.var 0))) Env.nil

/-- The iterator's successor step, as a function of the recursive value. -/
def iterSucc (Rd : Reading Tower.Head) : Ideal :=
  cinterp Rd (lamsCtx iterStepTele iterStepBody) Env.nil

/-- The function of the iterator: numeral recursion on the count, with functions of the
remaining parameters as values. -/
def iterRaw (Rd : Reading Tower.Head) : Ideal :=
  Ideal.lam fun N => natRec (iterZero Rd) (fun _ r => Ideal.app (iterSucc Rd) r) (principal N)

/-- The right side of a definition by one equation, elaborated as the object package's
annotation elaborates it. -/
abbrev defRhs (f : DeclName) {k : Nat} (Θ : Tower.Ctx k) (rhs : Tower.Tm k) : CTm Tower.Head k :=
  elabRight objectDecls (applyClosed Θ Presentation.ids (.const f)) rhs

/-- The function of a definition by one equation: its elaborated right side, abstracted
over its annotated telescope. -/
def defRaw (Rd : Reading Tower.Head) (f : DeclName) {k : Nat} (Θ : Tower.Ctx k)
    (rhs : Tower.Tm k) : Ideal :=
  cinterp Rd (lamsCtx (liftCtx Θ) (defRhs f Θ rhs)) Env.nil

/-- The annotated declared type of each constant. -/
def ObjConst.declType : ObjConst → CTm Tower.Head 0
  | .num | .set | .prop | .other => cU0
  | .zero => cnum
  | .suc => liftTm (.pi numT numT)
  | .add => liftTm addType
  | .power => liftTm powerType
  | .pow => liftTm powType
  | .numRec => liftTm Package.numRecType
  | .j => liftTm Package.jType
  | .eqAt => liftTm Package.eqAtType
  | .sucMove => liftTm Package.sucMoveType
  | .keep => liftTm Package.keepType
  | .transport => liftTm Package.transportType
  | .compose => liftTm Package.composeType
  | .iter => liftTm Package.iterType
  | .returnIter => liftTm Package.returnIterType
  | .sucStep => liftTm Package.sucStepType
  | .holds => liftTm programCodes.holdsType
  | .imp => liftTm programCodes.impType
  | .all type => liftTm (SetProfile.allType type)
  | .eq type => liftTm (SetProfile.eqType type)

/-- The function of each constant, in a reading of the constants of earlier stages. -/
def ObjConst.raw (Rd : Reading Tower.Head) : ObjConst → Ideal
  | .num => natI
  | .set => groundI
  | .prop => codesIdeal
  | .zero => zeroI
  | .suc => Ideal.sucRaw
  | .add => addRaw (Rd.const sucN)
  | .power => powerRaw
  | .pow => powRaw (Rd.const powerN)
  | .numRec => Ideal.nrRaw
  | .j => Ideal.jAlignedRaw
  | .eqAt => defRaw Rd eqAtName eqAtTele eqAtRhs
  | .sucMove => defRaw Rd sucMoveName eqAtTelescope sucMoveRhs
  | .keep => defRaw Rd keepName keepTele keepRhs
  | .transport => defRaw Rd transportName transportTelescope transportRhs
  | .compose => defRaw Rd composeName composeTelescope composeRhs
  | .iter => iterRaw Rd
  | .returnIter => defRaw Rd returnIterName returnIterTele returnIterRhs
  | .sucStep => defRaw Rd sucStepName eqAtTelescope sucStepRhs
  | .holds => Ideal.lam fun X => principal X
  | .imp => Ideal.lam fun P => Ideal.lam fun Q => former .pi (principal P) fun _ => principal Q
  | .all type => Ideal.allRaw (simpleI type)
  | .eq type => Ideal.lam fun X => Ideal.lam fun Y =>
      ident (simpleI type) (principal X) (principal Y)
  | .other => Ideal.bot

/-- **The Church constant of each constant**: its function, projected onto the
denotation of its declared type. -/
def stageValue (Rd : Reading Tower.Head) (tag : ObjConst) : Ideal :=
  projT (cinterp Rd tag.declType Env.nil) (tag.raw Rd)

/-! ## The reading -/

/-- Every universe denotes the universe, and the ground head a ground type. -/
def objectHead : Tower.Head → List Tok
  | .sort _ => Elem.univ
  | .legacyGround => Elem.ground

/-- The reading of the heads, and of each name through the constant it denotes. -/
def tagReading (v : ObjConst → Ideal) : Reading Tower.Head :=
  ⟨objectHead, fun c => v (objConst c)⟩

/-- The reading up to a stage: the constants of each stage read in the reading of the
stages before. -/
def valUpTo : Nat → ObjConst → Ideal
  | 0 => stageValue (tagReading fun _ => Ideal.bot)
  | k + 1 => fun tag =>
      if tag.stage ≤ k then valUpTo k tag else stageValue (tagReading (valUpTo k)) tag

/-- **The reading of the object package.** -/
def objectChurchReading : Reading Tower.Head := tagReading (valUpTo 5)

theorem valUpTo_stable {k : Nat} {tag : ObjConst} (hs : tag.stage ≤ k) :
    ∀ {j : Nat}, k ≤ j → valUpTo j tag = valUpTo k tag := by
  intro j hj
  induction j, hj using Nat.le_induction with
  | base => rfl
  | succ j hkj ih =>
      show (if tag.stage ≤ j then valUpTo j tag else _) = _
      rw [if_pos (Nat.le_trans hs hkj), ih]

/-! ## The fixed point -/

theorem stagedBelow_declType : ∀ tag : ObjConst, ∀ c ∈ termConsts tag.declType,
    (objConst c).stage < tag.stage := by
  intro tag
  cases tag with
  | all type =>
      intro c hc
      rw [show (objConst c).stage = 0 from stage_typeAt (type := .arr (.arr type .prop) .prop)
        (n := 0) hc]
      exact Nat.zero_lt_one
  | eq type =>
      intro c hc
      rw [show (objConst c).stage = 0 from stage_typeAt (type := .arr type (.arr type .prop))
        (n := 0) hc]
      exact Nat.zero_lt_one
  | num => exact fun _ h => absurd h List.not_mem_nil
  | set => exact fun _ h => absurd h List.not_mem_nil
  | prop => exact fun _ h => absurd h List.not_mem_nil
  | other => exact fun _ h => absurd h List.not_mem_nil
  | zero => exact stagedBelow_spec (by decide)
  | suc => exact stagedBelow_spec (by decide)
  | add => exact stagedBelow_spec (by decide)
  | power => exact stagedBelow_spec (by decide)
  | pow => exact stagedBelow_spec (by decide)
  | numRec => exact stagedBelow_spec (by decide)
  | j => exact stagedBelow_spec (by decide)
  | eqAt => exact stagedBelow_spec (by decide)
  | sucMove => exact stagedBelow_spec (by decide)
  | keep => exact stagedBelow_spec (by decide)
  | transport => exact stagedBelow_spec (by decide)
  | compose => exact stagedBelow_spec (by decide)
  | iter => exact stagedBelow_spec (by decide)
  | returnIter => exact stagedBelow_spec (by decide)
  | sucStep => exact stagedBelow_spec (by decide)
  | holds => exact stagedBelow_spec (by decide)
  | imp => exact stagedBelow_spec (by decide)

/-- The function of a definition by one equation reads only the constants of earlier
stages. -/
theorem defRaw_congr {Rd Rd' : Reading Tower.Head} (heads : Rd.head = Rd'.head) {s : Nat}
    (agree : ∀ c, (objConst c).stage < s → Rd.const c = Rd'.const c) (f : DeclName) {k : Nat}
    (Θ : Tower.Ctx k) (rhs : Tower.Tm k)
    (staged : stagedBelow s (lamsCtx (liftCtx Θ) (defRhs f Θ rhs)) = true) :
    defRaw Rd f Θ rhs = defRaw Rd' f Θ rhs := by
  unfold defRaw
  rw [cinterp_congr heads _ fun c hc => agree c (stagedBelow_spec staged c hc)]

theorem raw_congr {Rd Rd' : Reading Tower.Head} (heads : Rd.head = Rd'.head) (tag : ObjConst)
    (agree : ∀ c, (objConst c).stage < tag.stage → Rd.const c = Rd'.const c) :
    tag.raw Rd = tag.raw Rd' := by
  cases tag with
  | add => exact congrArg addRaw (agree sucN (by decide))
  | pow => exact congrArg powRaw (agree powerN (by decide))
  | eqAt => exact defRaw_congr heads agree _ _ _ (by decide)
  | sucMove => exact defRaw_congr heads agree _ _ _ (by decide)
  | keep => exact defRaw_congr heads agree _ _ _ (by decide)
  | transport => exact defRaw_congr heads agree _ _ _ (by decide)
  | compose => exact defRaw_congr heads agree _ _ _ (by decide)
  | returnIter => exact defRaw_congr heads agree _ _ _ (by decide)
  | sucStep => exact defRaw_congr heads agree _ _ _ (by decide)
  | iter =>
      show Ideal.lam (fun N =>
          natRec (iterZero Rd) (fun _ r => Ideal.app (iterSucc Rd) r) (principal N)) =
        Ideal.lam (fun N =>
          natRec (iterZero Rd') (fun _ r => Ideal.app (iterSucc Rd') r) (principal N))
      have z : termConsts (lamsCtx iterTele (.pair (.var 1) (.var 0) : CTm Tower.Head 5)) = [] := by
        decide
      have s : termConsts (lamsCtx iterStepTele iterStepBody) = [] := by decide
      have e₁ : iterZero Rd = iterZero Rd' := by
        unfold iterZero
        rw [cinterp_congr heads _ fun c hc => absurd (z ▸ hc) List.not_mem_nil]
      have e₂ : iterSucc Rd = iterSucc Rd' := by
        unfold iterSucc
        rw [cinterp_congr heads _ fun c hc => absurd (s ▸ hc) List.not_mem_nil]
      rw [e₁, e₂]
  | num => rfl
  | set => rfl
  | prop => rfl
  | zero => rfl
  | suc => rfl
  | power => rfl
  | numRec => rfl
  | j => rfl
  | holds => rfl
  | imp => rfl
  | all _ => rfl
  | eq _ => rfl
  | other => rfl

/-- The Church constant of a constant reads only the constants of earlier stages. -/
theorem stageValue_congr {Rd Rd' : Reading Tower.Head} (heads : Rd.head = Rd'.head)
    (tag : ObjConst) (agree : ∀ c, (objConst c).stage < tag.stage → Rd.const c = Rd'.const c) :
    stageValue Rd tag = stageValue Rd' tag := by
  unfold stageValue
  rw [cinterp_congr heads tag.declType fun c hc => agree c (stagedBelow_declType tag c hc),
    raw_congr heads tag agree]

/-- **The reading is a fixed point**: every constant denotes its Church constant in the
whole reading. -/
theorem objectChurchReading_const (c : DeclName) :
    objectChurchReading.const c = stageValue objectChurchReading (objConst c) := by
  show valUpTo 5 (objConst c) = _
  generalize objConst c = tag
  rw [valUpTo_stable (Nat.le_refl tag.stage) (ObjConst.stage_le tag)]
  have agreeUpTo : ∀ k, k ≤ 5 → ∀ c', (objConst c').stage ≤ k →
      (tagReading (valUpTo k)).const c' = objectChurchReading.const c' := fun _ hk _ hc' =>
    (valUpTo_stable hc' hk).symm
  have h5 := ObjConst.stage_le tag
  match hs : tag.stage with
  | 0 =>
      show stageValue (tagReading fun _ => Ideal.bot) tag = _
      exact stageValue_congr (Rd := tagReading fun _ => Ideal.bot) (Rd' := objectChurchReading)
        rfl tag fun c' h => absurd (hs ▸ h) (Nat.not_lt_zero _)
  | k + 1 =>
      show (if tag.stage ≤ k then valUpTo k tag else stageValue (tagReading (valUpTo k)) tag) = _
      rw [if_neg (by omega)]
      exact stageValue_congr (Rd := tagReading (valUpTo k)) (Rd' := objectChurchReading) rfl tag
        fun c' h => agreeUpTo k (by omega) c' (by omega)

/-! ## The values of the constants -/

section Values

/-- The value of a constant named by a tag. -/
theorem objectChurchReading_const_of {c : DeclName} {tag : ObjConst} (h : objConst c = tag) :
    objectChurchReading.const c = stageValue objectChurchReading tag :=
  h ▸ objectChurchReading_const c

theorem cinterp_sort {n : Nat} (l : LevelExpr Nat) (ρ : Env n) :
    cinterp objectChurchReading (.head (.sort l) : CTm Tower.Head n) ρ = univIdeal := rfl

theorem objectChurchReading_num : objectChurchReading.const numN = natI := by
  rw [objectChurchReading_const_of (show objConst numN = .num by decide)]
  exact Ideal.projT_univ_eq_self_iff.2 Ideal.typeGenerated_natI

theorem objectChurchReading_set : objectChurchReading.const setN = groundI := by
  rw [objectChurchReading_const_of (show objConst setN = .set by decide)]
  exact Ideal.projT_univ_eq_self_iff.2 Ideal.typeGenerated_groundI

theorem objectChurchReading_prop : objectChurchReading.const propN = codesIdeal := by
  rw [objectChurchReading_const_of (show objConst propN = .prop by decide)]
  exact Ideal.projT_univ_eq_self_iff.2 Ideal.typeGenerated_codesIdeal

theorem cinterp_cnum {n : Nat} (ρ : Env n) :
    cinterp objectChurchReading (cnum : CTm Tower.Head n) ρ = natI := objectChurchReading_num

theorem cinterp_cset {n : Nat} (ρ : Env n) :
    cinterp objectChurchReading (cset : CTm Tower.Head n) ρ = groundI := objectChurchReading_set

theorem cinterp_propT {n : Nat} (ρ : Env n) :
    cinterp objectChurchReading (.const propN : CTm Tower.Head n) ρ = codesIdeal :=
  objectChurchReading_prop

theorem objectChurchReading_zero : objectChurchReading.const zeroN = zeroI := by
  rw [objectChurchReading_const_of (show objConst zeroN = .zero by decide)]
  show projT (objectChurchReading.const numN) zeroI = zeroI
  rw [objectChurchReading_num]
  exact Ideal.projT_natI_zeroI

theorem objectChurchReading_suc :
    objectChurchReading.const sucN = sucConst objectChurchReading numNames :=
  objectChurchReading_const_of (show objConst sucN = .suc by decide)

/-- **The declared type of numeral recursion** is the recursor's annotated type at the
numbers. -/
theorem liftTm_numRecType : (liftTm Package.numRecType : CTm Tower.Head 0) = nrTypeC numNames :=
  rfl

/-- **The declared type of the identity eliminator** is the eliminator's annotated type at
the lowest universe. -/
theorem liftTm_jType : (liftTm Package.jType : CTm Tower.Head 0) = jTypeC (.sort Tower.zero) :=
  rfl

theorem objectChurchReading_numRec :
    objectChurchReading.const numRecName = nrConst objectChurchReading numNames :=
  objectChurchReading_const_of (show objConst numRecName = .numRec by decide)

theorem objectChurchReading_j :
    objectChurchReading.const jName = jAlignedConst objectChurchReading (.sort Tower.zero) :=
  objectChurchReading_const_of (show objConst jName = .j by decide)

theorem objectChurchReading_holds : objectChurchReading.const holdsN = Ideal.holdsConst := by
  rw [objectChurchReading_const_of (show objConst holdsN = .holds by decide)]
  show projT (cpi (objectChurchReading.const propN) fun _ => univIdeal) _ = _
  rw [objectChurchReading_prop]
  rfl

theorem objectChurchReading_imp : objectChurchReading.const impN = Ideal.impConst := by
  rw [objectChurchReading_const_of (show objConst impN = .imp by decide)]
  show projT (cpi (objectChurchReading.const propN) fun _ =>
    cpi (objectChurchReading.const propN) fun _ => objectChurchReading.const propN) _ = _
  rw [objectChurchReading_prop]
  rfl

/-- A simple type denotes its denotation. -/
theorem cinterp_objectTypeAt (type : HOL.Ty SetProfile.SetBase) {n : Nat} (ρ : Env n) :
    cinterp objectChurchReading (liftTm (typeAt SetProfile.types n type)) ρ = simpleI type :=
  cinterp_typeAt objectChurchReading_prop objectChurchReading_num objectChurchReading_set type ρ

theorem objectChurchReading_all (type : HOL.Ty SetProfile.SetBase) :
    objectChurchReading.const (SetProfile.allName type) = Ideal.allConst (simpleI type) := by
  rw [objectChurchReading_const_of (objConst_allName type)]
  show projT (cinterp objectChurchReading (liftTm (typeAt SetProfile.types 0
    (.arr (.arr type .prop) .prop))) Env.nil) _ = _
  rw [cinterp_objectTypeAt]
  rfl

theorem objectChurchReading_eq (type : HOL.Ty SetProfile.SetBase) :
    objectChurchReading.const (SetProfile.eqName type) = Ideal.eqConst (simpleI type) := by
  rw [objectChurchReading_const_of (objConst_eqName type)]
  show projT (cinterp objectChurchReading (liftTm (typeAt SetProfile.types 0
    (.arr type (.arr type .prop)))) Env.nil) _ = _
  rw [cinterp_objectTypeAt]
  rfl

/-- The declared type of addition, `num → num → num`, denoted. -/
def addT : Ideal := cpi natI fun _ => cpi natI fun _ => natI

/-- The declared type of the power set, `set → set`, denoted. -/
def powerT : Ideal := cpi groundI fun _ => groundI

/-- The declared type of the iterated power set, `num → set → set`, denoted. -/
def powT : Ideal := cpi natI fun _ => cpi groundI fun _ => groundI

theorem cinterp_addType : cinterp objectChurchReading (liftTm addType) Env.nil = addT := by
  show (cpi (objectChurchReading.const numN) fun _ => cpi (objectChurchReading.const numN) fun _ =>
    objectChurchReading.const numN) = _
  rw [objectChurchReading_num]
  rfl

theorem cinterp_powerType : cinterp objectChurchReading (liftTm powerType) Env.nil = powerT := by
  show (cpi (objectChurchReading.const setN) fun _ => objectChurchReading.const setN) = _
  rw [objectChurchReading_set]
  rfl

theorem cinterp_powType : cinterp objectChurchReading (liftTm powType) Env.nil = powT := by
  show (cpi (objectChurchReading.const numN) fun _ => cpi (objectChurchReading.const setN) fun _ =>
    objectChurchReading.const setN) = _
  rw [objectChurchReading_num, objectChurchReading_set]
  rfl

/-- **The power set** denotes the Church constant of the least element. -/
theorem objectChurchReading_power : objectChurchReading.const powerN = projT powerT powerRaw := by
  rw [objectChurchReading_const_of (show objConst powerN = .power by decide)]
  show projT (cinterp objectChurchReading (liftTm powerType) Env.nil) powerRaw = _
  rw [cinterp_powerType]

/-- **Addition** denotes numeral recursion on its second argument with the successor. -/
theorem objectChurchReading_add :
    objectChurchReading.const addN =
      projT addT (addRaw (sucConst objectChurchReading numNames)) := by
  rw [objectChurchReading_const_of (show objConst addN = .add by decide)]
  show projT (cinterp objectChurchReading (liftTm addType) Env.nil)
    (addRaw (objectChurchReading.const sucN)) = _
  rw [cinterp_addType, objectChurchReading_suc]

/-- **The iterated power set** denotes numeral recursion on its first argument with the
power set. -/
theorem objectChurchReading_pow :
    objectChurchReading.const powN = projT powT (powRaw (projT powerT powerRaw)) := by
  rw [objectChurchReading_const_of (show objConst powN = .pow by decide)]
  show projT (cinterp objectChurchReading (liftTm powType) Env.nil)
    (powRaw (objectChurchReading.const powerN)) = _
  rw [cinterp_powType, objectChurchReading_power]

/-- **The iterator** denotes function-valued numeral recursion on its count. -/
theorem objectChurchReading_iter :
    objectChurchReading.const iterName =
      projT (cinterp objectChurchReading (liftTm Package.iterType) Env.nil)
        (iterRaw objectChurchReading) :=
  objectChurchReading_const_of (show objConst iterName = .iter by decide)

/-- **A definition by one equation** denotes the Church constant of its right side. -/
theorem objectChurchReading_def {f : DeclName} {tag : ObjConst} (h : objConst f = tag) {k : Nat}
    {Θ : Tower.Ctx k} {rhs : Tower.Tm k} {T : CTm Tower.Head k}
    (declType : tag.declType = pisCtx (liftCtx Θ) T)
    (raw : tag.raw objectChurchReading = defRaw objectChurchReading f Θ rhs) :
    objectChurchReading.const f =
      defConst objectChurchReading (liftCtx Θ) T (defRhs f Θ rhs) := by
  rw [objectChurchReading_const_of h, stageValue, raw, declType]
  rfl

end Values

/-! ## The constants denote elements of their declared types -/

section Constants

/-- The constants of the object package with fixed names, and their declared types. -/
def fixedDecls : List (DeclName × Tower.Tm 0) :=
  [(propN, U0), (holdsN, programCodes.holdsType), (impN, programCodes.impType)] ++ declarations

theorem mem_of_lookup {c : DeclName} {T : Tower.Tm 0} :
    ∀ {l : List (DeclName × Tower.Tm 0)}, l.lookup c = some T → (c, T) ∈ l
  | [], h => nomatch h
  | (k, v) :: rest, h => by
      simp only [List.lookup] at h
      split at h
      · rename_i heq
        cases h
        obtain rfl := eq_of_beq heq
        exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (mem_of_lookup h)

/-- **Every declared constant of the object package** is a quantifier or an equation
instance, or has a fixed name. -/
theorem objectRules_constantType_cases {c : DeclName} {T : Tower.Tm 0}
    (h : objectRules.constantType c = some T) :
    (∃ type, c = SetProfile.allName type ∧ T = SetProfile.allType type) ∨
      (∃ type, c = SetProfile.eqName type ∧ T = SetProfile.eqType type) ∨
      (c, T) ∈ fixedDecls := by
  change ((programCodes.codeType c).orElse fun _ => rules.constantType c) = some T at h
  cases hcode : programCodes.codeType c with
  | none =>
      rw [hcode] at h
      change (if true = true then allTypes c else none) = some T at h
      rw [if_pos rfl] at h
      exact .inr (.inr (List.mem_append_right _ (mem_of_lookup h)))
  | some T' =>
      rw [hcode] at h
      obtain rfl : T' = T := Option.some.inj h
      simp only [Impredicative.Codes.codeType] at hcode
      by_cases hp : c = programCodes.prop
      · rw [if_pos hp] at hcode
        obtain rfl := Option.some.inj hcode
        subst hp
        exact .inr (.inr (List.mem_append_left _ List.mem_cons_self))
      rw [if_neg hp] at hcode
      by_cases hh : c = programCodes.holds
      · rw [if_pos hh] at hcode
        obtain rfl := Option.some.inj hcode
        subst hh
        exact .inr (.inr (List.mem_append_left _ (List.mem_cons_of_mem _ List.mem_cons_self)))
      rw [if_neg hh] at hcode
      by_cases hi : c = programCodes.imp
      · rw [if_pos hi] at hcode
        obtain rfl := Option.some.inj hcode
        subst hi
        exact .inr (.inr (List.mem_append_left _
          (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))))
      rw [if_neg hi] at hcode
      cases hq : programCodes.quantifiers c with
      | some A =>
          rw [hq] at hcode
          obtain rfl := Option.some.inj hcode
          change (SetProfile.allInstance? c).map typeTerm = some A at hq
          cases hall : SetProfile.allInstance? c with
          | none => rw [hall] at hq; cases hq
          | some type =>
              rw [hall] at hq
              obtain rfl := Option.some.inj hq
              exact .inl ⟨type, SetProfile.allInstance?_eq_some hall, rfl⟩
      | none =>
          rw [hq] at hcode
          change ((if true = true then (SetProfile.eqInstance? c).map typeTerm else none).map
            programCodes.eqType) = some T' at hcode
          rw [if_pos rfl] at hcode
          cases heq : SetProfile.eqInstance? c with
          | none => rw [heq] at hcode; cases hcode
          | some type =>
              rw [heq] at hcode
              obtain rfl := Option.some.inj hcode
              refine .inr (.inl ⟨type, SetProfile.eqInstance?_eq_some heq, ?_⟩)
              change Tm.pi (typeTerm type) (Tm.pi (Presentation.rename wk (typeTerm type))
                (.const propN)) = typeAt SetProfile.types 0 (.arr type (.arr type .prop))
              rw [typeTerm, FormationSensitiveHOLInterface.typeAt_rename]
              rfl

theorem fixedDecls_lamFree : ∀ p ∈ fixedDecls, lamFree p.2 = true := by decide

theorem fixedDecls_declType : ∀ p ∈ fixedDecls, liftTm p.2 = (objConst p.1).declType := by
  decide

/-- **The annotated declared type of every constant** is the declared type of the constant it
denotes. -/
theorem declType_of_declared {c : DeclName} {D : CTm Tower.Head 0}
    (declared : objectChurch.constantType c = some D) : D = (objConst c).declType := by
  rw [objectChurch_constantType] at declared
  unfold elabDeclarations at declared
  cases hT : objectRules.constantType c with
  | none => rw [hT] at declared; cases declared
  | some T =>
      rw [hT, Option.map_some] at declared
      obtain rfl := Option.some.inj declared
      rcases objectRules_constantType_cases hT with
        ⟨type, rfl, rfl⟩ | ⟨type, rfl, rfl⟩ | hmem
      · rw [elabClosed, elab_lamFree _ (show lamFree (SetProfile.allType type) = true from
          lamFree_typeAt (.arr (.arr type .prop) .prop) 0), objConst_allName]
        rfl
      · rw [elabClosed, elab_lamFree _ (show lamFree (SetProfile.eqType type) = true from
          lamFree_typeAt (.arr type (.arr type .prop)) 0), objConst_eqName]
        rfl
      · rw [elabClosed, elab_lamFree _ (fixedDecls_lamFree _ hmem)]
        exact fixedDecls_declType _ hmem

/-- **Every declared constant denotes an element of its declared type.** -/
theorem objectChurchReading_constants {c : DeclName} {D : CTm Tower.Head 0}
    (declared : objectChurch.constantType c = some D) :
    projT (cinterp objectChurchReading D Env.nil) (objectChurchReading.const c) =
      objectChurchReading.const c := by
  rw [objectChurchReading_const c, declType_of_declared declared]
  exact Ideal.projT_projT _ _

end Constants

end CodeModel

end Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel
