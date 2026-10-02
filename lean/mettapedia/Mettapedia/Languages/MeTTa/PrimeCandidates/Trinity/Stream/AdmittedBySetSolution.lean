import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel.ObjectRecursiveDefinitions
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TowerInterpretation.SetDefinitions

/-!
# The endless stream by its written equation, admitted on its solution in sets

The stream of the numbers from `n` on is written

    from n ⟶ scons n (from (suc n))

Read as a rewrite rule the equation never stops: every use of it produces another call. A
check for structural recursion refuses it, and among the finite lists it has no value. It
still has a type and a meaning. A stream of numbers is a function from positions to numbers,
`num → num`; `scons a s` is the stream with `a` at position zero and `s` one position later,

    scons a s zero    ⟶ a
    scons a s (suc k) ⟶ s k

and `from n` is the function `k ↦ n + k`.

A definition by equations asks three different things: that both sides of each equation have
one type; that some value satisfies the equations; that the equations stop when run as rules.
For this stream the first two hold and the third fails. This module admits `scons` and `from`
into the candidate with exactly the equations above as their computation steps, on the
evidence that a set value satisfies them (`scons_valid`, `from_valid`), by the general
criterion `definition_setModel_of_value`. So the package with both has a set model
(`objectFrom_model`) and is consistent (`objectFrom_consistent`), relative to
`CofinalInaccessibles`.

**Finite observations are derivable**: in the judgment the first element of `from n` is `n`
(`from_first`) and its second is `suc n` (`from_second`), each by finitely many uses of the
equations. Reading a stream at a position stops although unfolding the stream does not.

**Negative example**: the same equation at the type of lists,
`fromList n ⟶ cons n (fromList (suc n))`, has no set model at any assignment that reads the
numbers as the object package does (`fromList_no_setModel`). The length of `fromList n` would
be one more than the length of `fromList (suc n)` for every `n`, so the length at zero would
exceed every number. The stream is not a finite list.

What this does not give: a rule that tells a checker when a definition of this kind is
productive, and equality of two streams by conversion. Here two streams are equal when they
are proved equal position by position.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.Trinity.Stream

open Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel
open Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel.CodeModel
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TowerInterpretation
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId
open Mettapedia.TypeTheory.UniverseLevel
open Presentation
open Presentation.TypedEquality
open Presentation.TypedEquality.Normalization
open Presentation.TypedEquality.Annotated
open Mettapedia.Logic.HOL.Embedding
open ZFSetUniverseClosure (CofinalInaccessibles)
open ZFSetDependentProducts (graph)
open ZFSetTraceProducts (traceApp traceLam tracePiSet traceApp_graph_beta)

universe u

/-! ## The two definitions -/

/-- The name of the operation that puts a number before a stream. -/
def sconsN : DeclName := .str .anonymous "scons"

/-- The name of the stream of the numbers from a number on. -/
def fromN : DeclName := .str .anonymous "from"

section Terms

variable {n : Nat}

/-- **The type of streams of numbers**: the functions from positions to numbers. -/
abbrev streamT : CTm Tower.Head n := .pi cnum cnum

/-- The type of `scons`: a number, a stream, a stream. -/
abbrev sconsType : CTm Tower.Head n := .pi cnum (.pi streamT streamT)

/-- The type of `from`: a number, a stream. -/
abbrev fromType : CTm Tower.Head n := .pi cnum streamT

/-- `scons` applied to a number and a stream. -/
abbrev cscons (a s : CTm Tower.Head n) : CTm Tower.Head n := .app (.app (.const sconsN) a) s

/-- `from` applied to a number. -/
abbrev cfrom (x : CTm Tower.Head n) : CTm Tower.Head n := .app (.const fromN) x

end Terms

/-- `scons a s zero ⟶ a`: the first element. -/
def sconsFirst : DefiningEquation Tower.Head where
  arity := 2
  telescope := .snoc (.snoc .nil cnum) streamT
  left := .app (cscons (.var 1) (.var 0)) czero
  right := .var 1

/-- `scons a s (suc k) ⟶ s k`: a later element. -/
def sconsLater : DefiningEquation Tower.Head where
  arity := 3
  telescope := .snoc (.snoc (.snoc .nil cnum) streamT) cnum
  left := .app (cscons (.var 2) (.var 1)) (csuc (.var 0))
  right := .app (.var 1) (.var 0)

/-- The equations of `scons`: what it holds at each position. -/
def sconsEquations : List (DefiningEquation Tower.Head) := [sconsFirst, sconsLater]

/-- **The object package with `scons`.** -/
abbrev objectScons := withDefinition objectChurch sconsN sconsType sconsEquations

/-- `from n ⟶ scons n (from (suc n))`: the written equation of the endless stream. -/
def fromEquation : DefiningEquation Tower.Head where
  arity := 1
  telescope := .snoc .nil cnum
  left := cfrom (.var 0)
  right := cscons (.var 0) (cfrom (csuc (.var 0)))

/-- **The package with `scons` and the endless stream `from`.** -/
abbrev objectFrom := withDefinition objectScons fromN fromType [fromEquation]

/-- The name of `scons` is new to the object package. -/
theorem scons_new : objectChurch.constantType sconsN = none := by decide

/-- The name of `from` is new to the package with `scons`. -/
theorem from_new : objectScons.constantType fromN = none := by decide

/-! ## Streams as sets -/

section Streams

/-- **The set of streams of numbers**: the functions from the natural numbers to the natural
numbers. -/
noncomputable def streams : ZFSet.{u} := tracePiSet ZFSet.omega (fun _ => ZFSet.omega)

/-- What `scons a s` holds at a position: the number at position zero, and the stream one
position earlier after that. -/
noncomputable def sconsAt (a s k : ZFSet.{u}) : ZFSet.{u} :=
  if natOf k = 0 then a else traceApp s (numeral (natOf k - 1))

/-- The stream `scons a s`. -/
noncomputable def sconsStream (a s : ZFSet.{u}) : ZFSet.{u} :=
  traceLam (graph ZFSet.omega fun k => sconsAt a s k)

/-- `scons` as a set. -/
noncomputable def sconsValue : ZFSet.{u} :=
  traceLam (graph ZFSet.omega fun a => traceLam (graph streams fun s => sconsStream a s))

/-- **The stream of the numbers from `n` on**: position `k` holds `n + k`. -/
noncomputable def fromStream (n : ZFSet.{u}) : ZFSet.{u} :=
  traceLam (graph ZFSet.omega fun k => numeral (natOf n + natOf k))

/-- `from` as a set. -/
noncomputable def fromValue : ZFSet.{u} := traceLam (graph ZFSet.omega fromStream)

theorem sconsAt_mem {a s k : ZFSet.{u}} (ha : a ∈ ZFSet.omega) (hs : s ∈ streams) :
    sconsAt a s k ∈ ZFSet.omega := by
  unfold sconsAt
  by_cases first : natOf k = 0
  · rw [if_pos first]
    exact ha
  · rw [if_neg first]
    exact traceApp_mem_fibre hs (numeral_mem_omega _)

theorem sconsStream_mem {a s : ZFSet.{u}} (ha : a ∈ ZFSet.omega) (hs : s ∈ streams) :
    sconsStream a s ∈ streams :=
  traceLam_graph_mem fun _ _ => sconsAt_mem ha hs

theorem sconsValue_mem :
    sconsValue.{u} ∈ tracePiSet ZFSet.omega (fun _ => tracePiSet streams (fun _ => streams)) :=
  traceLam_graph_mem fun _ ha => traceLam_graph_mem fun _ hs => sconsStream_mem ha hs

/-- `scons` applied to a number and a stream is the stream that puts the number first. -/
theorem sconsValue_apply {a s : ZFSet.{u}} (ha : a ∈ ZFSet.omega) (hs : s ∈ streams) :
    traceApp (traceApp sconsValue a) s = sconsStream a s := by
  unfold sconsValue
  rw [traceApp_graph_beta _ ha, traceApp_graph_beta _ hs]

/-- A stream that puts a number first, read at a position. -/
theorem sconsStream_apply {a s k : ZFSet.{u}} (hk : k ∈ ZFSet.omega) :
    traceApp (sconsStream a s) k = sconsAt a s k :=
  traceApp_graph_beta _ hk

theorem fromStream_mem (n : ZFSet.{u}) : fromStream n ∈ streams :=
  traceLam_graph_mem fun _ _ => numeral_mem_omega _

theorem fromValue_mem : fromValue.{u} ∈ tracePiSet ZFSet.omega (fun _ => streams) :=
  traceLam_graph_mem fun n _ => fromStream_mem n

theorem fromValue_apply {n : ZFSet.{u}} (hn : n ∈ ZFSet.omega) :
    traceApp fromValue n = fromStream n :=
  traceApp_graph_beta _ hn

/-- The stream from `n` on, read at a position. -/
theorem fromStream_apply {n k : ZFSet.{u}} (hk : k ∈ ZFSet.omega) :
    traceApp (fromStream n) k = numeral (natOf n + natOf k) :=
  traceApp_graph_beta _ hk

/-- **The written equation between sets**: the stream from `n` on is `n` before the stream from
its successor on. Position by position: `n + 0 = n`, and `n + (j + 1) = (n + 1) + j`. -/
theorem fromStream_unfold {n : ZFSet.{u}} (hn : n ∈ ZFSet.omega) :
    fromStream n = sconsStream n (fromStream (insert n n)) := by
  unfold fromStream sconsStream
  refine congrArg traceLam (graph_congr fun k _ => ?_)
  show numeral (natOf n + natOf k) =
    sconsAt n (traceLam (graph ZFSet.omega fun j => numeral (natOf (insert n n) + natOf j))) k
  unfold sconsAt
  by_cases first : natOf k = 0
  · rw [if_pos first, first, Nat.add_zero, numeral_natOf hn]
  · rw [if_neg first, traceApp_graph_beta _ (numeral_mem_omega _), natOf_insert hn,
      natOf_numeral]
    congr 1
    omega

end Streams

/-! ## The values of the object package that the equations mention -/

section Values

variable (h : CofinalInaccessibles.{u}) {consts : DeclName → ZFSet.{u}}

theorem num_value
    (agrees : ∀ c, objectChurch.constantType c ≠ none → consts c = objectSetConsts h c) :
    consts numN = ZFSet.omega := by
  rw [agrees numN (objectChurch_constantType_ne_none (by decide))]
  exact setConst_num h

theorem zero_value
    (agrees : ∀ c, objectChurch.constantType c ≠ none → consts c = objectSetConsts h c) :
    consts zeroN = numeral 0 := by
  rw [agrees zeroN (objectChurch_constantType_ne_none (by decide))]
  exact setConst_zero h

theorem suc_value
    (agrees : ∀ c, objectChurch.constantType c ≠ none → consts c = objectSetConsts h c)
    {x : ZFSet.{u}} (hx : x ∈ ZFSet.omega) : traceApp (consts sucN) x = insert x x := by
  rw [agrees sucN (objectChurch_constantType_ne_none (by decide))]
  exact suc_apply h hx

end Values

/-! ## The set model of `scons` -/

section Model

variable (h : CofinalInaccessibles.{u})

/-- The first equation of `scons` between sets: position zero holds the number. -/
theorem sconsFirst_valid {consts : DeclName → ZFSet.{u}}
    (agrees : ∀ c, objectChurch.constantType c ≠ none → consts c = objectSetConsts h c)
    (atScons : consts sconsN = sconsValue) (η : Env.{u} 2)
    (sat : Sat (objHeads h) consts (.snoc (.snoc .nil cnum) streamT : CCtx Tower.Head 2) η) :
    ev (objHeads h) consts (.app (cscons (.var 1) (.var 0)) czero : CTm Tower.Head 2) η =
      ev (objHeads h) consts (.var 1 : CTm Tower.Head 2) η := by
  have numbers := num_value h agrees
  have ha : η 1 ∈ ZFSet.omega := by
    have member := sat 1
    change η 1 ∈ consts numN at member
    rwa [numbers] at member
  have hs : η 0 ∈ streams := by
    have member := sat 0
    change η 0 ∈ tracePiSet (consts numN) (fun _ => consts numN) at member
    rwa [numbers] at member
  show traceApp (traceApp (traceApp (consts sconsN) (η 1)) (η 0)) (consts zeroN) = η 1
  rw [atScons, zero_value h agrees, sconsValue_apply ha hs,
    sconsStream_apply (numeral_mem_omega 0)]
  unfold sconsAt
  rw [if_pos (natOf_numeral 0)]

/-- The second equation of `scons` between sets: a later position holds what the stream holds
one position earlier. -/
theorem sconsLater_valid {consts : DeclName → ZFSet.{u}}
    (agrees : ∀ c, objectChurch.constantType c ≠ none → consts c = objectSetConsts h c)
    (atScons : consts sconsN = sconsValue) (η : Env.{u} 3)
    (sat : Sat (objHeads h) consts
      (.snoc (.snoc (.snoc .nil cnum) streamT) cnum : CCtx Tower.Head 3) η) :
    ev (objHeads h) consts (.app (cscons (.var 2) (.var 1)) (csuc (.var 0)) : CTm Tower.Head 3) η =
      ev (objHeads h) consts (.app (.var 1) (.var 0) : CTm Tower.Head 3) η := by
  have numbers := num_value h agrees
  have ha : η 2 ∈ ZFSet.omega := by
    have member := sat 2
    change η 2 ∈ consts numN at member
    rwa [numbers] at member
  have hs : η 1 ∈ streams := by
    have member := sat 1
    change η 1 ∈ tracePiSet (consts numN) (fun _ => consts numN) at member
    rwa [numbers] at member
  have hk : η 0 ∈ ZFSet.omega := by
    have member := sat 0
    change η 0 ∈ consts numN at member
    rwa [numbers] at member
  show traceApp (traceApp (traceApp (consts sconsN) (η 2)) (η 1))
      (traceApp (consts sucN) (η 0)) = traceApp (η 1) (η 0)
  rw [atScons, suc_value h agrees hk, sconsValue_apply ha hs,
    sconsStream_apply (insert_mem_omega hk)]
  unfold sconsAt
  rw [if_neg (by rw [natOf_insert hk]; exact Nat.succ_ne_zero _), natOf_insert hk,
    Nat.add_sub_cancel, numeral_natOf hk]

/-- **The set value of `scons` satisfies its two equations** at every typed instance. -/
theorem scons_valid {consts : DeclName → ZFSet.{u}}
    (agrees : ∀ c, objectChurch.constantType c ≠ none → consts c = objectSetConsts h c)
    (atScons : consts sconsN = sconsValue) :
    ∀ e ∈ sconsEquations, ∀ η : Env.{u} e.arity, Sat (objHeads h) consts e.telescope η →
      ev (objHeads h) consts e.left η = ev (objHeads h) consts e.right η := by
  intro e member η sat
  have cases : e = sconsFirst ∨ e = sconsLater := by
    simpa [sconsEquations] using member
  rcases cases with rfl | rfl
  · exact sconsFirst_valid h agrees atScons η sat
  · exact sconsLater_valid h agrees atScons η sat

/-- The set of the type of `scons`. -/
theorem ev_sconsType {consts : DeclName → ZFSet.{u}}
    (agrees : ∀ c, objectChurch.constantType c ≠ none → consts c = objectSetConsts h c) :
    ev (objHeads h) consts (sconsType : CTm Tower.Head 0) Fin.elim0 =
      tracePiSet ZFSet.omega (fun _ => tracePiSet streams (fun _ => streams)) := by
  show tracePiSet (consts numN) (fun _ =>
    tracePiSet (tracePiSet (consts numN) (fun _ => consts numN))
      (fun _ => tracePiSet (consts numN) (fun _ => consts numN))) = _
  rw [num_value h agrees]
  rfl

/-- The assignment of the model with `scons`. -/
noncomputable def sconsConsts : DeclName → ZFSet.{u} :=
  Function.update (objectSetConsts h) sconsN sconsValue

/-- **The package with `scons` has a set model**, relative to `CofinalInaccessibles`. -/
theorem objectScons_model (consts : DeclName → ZFSet.{u})
    (agrees : ∀ c, objectScons.constantType c ≠ none → consts c = sconsConsts h c) :
    SetModel (objHeads h) consts objectScons :=
  definition_setModel_of_value objectChurch (object_baseModel h) scons_new sconsValue
    (fun _ agreesBase _ => by
      rw [ev_sconsType h agreesBase]
      exact sconsValue_mem)
    (fun _ agreesBase atScons => scons_valid h agreesBase atScons) consts agrees

/-! ## The set model of the endless stream -/

/-- An assignment that agrees with the model with `scons` on the names it declares agrees with
the object package's on the names that one declares. -/
theorem agrees_object {consts : DeclName → ZFSet.{u}}
    (agrees : ∀ c, objectScons.constantType c ≠ none → consts c = sconsConsts h c) :
    ∀ c, objectChurch.constantType c ≠ none → consts c = objectSetConsts h c := by
  intro c declared
  have other : c ≠ sconsN := fun same => declared (same ▸ scons_new)
  have inSum : objectScons.constantType c ≠ none := by
    cases found : objectChurch.constantType c with
    | none => exact absurd found declared
    | some type =>
      have known : objectScons.constantType c = some type := sumDecls_left found
      rw [known]
      exact Option.some_ne_none type
  rw [agrees c inSum]
  exact Function.update_of_ne other _ _

/-- Such an assignment gives `scons` its set value. -/
theorem scons_at {consts : DeclName → ZFSet.{u}}
    (agrees : ∀ c, objectScons.constantType c ≠ none → consts c = sconsConsts h c) :
    consts sconsN = sconsValue := by
  have declared : objectScons.constantType sconsN ≠ none := by
    rw [withDefinition_defined objectChurch scons_new]
    exact Option.some_ne_none _
  rw [agrees sconsN declared]
  exact Function.update_self _ _ _

/-- **The written equation of the endless stream between sets**, at every number: the
equation that never stops as a rule holds between sets. -/
theorem fromEquation_valid {consts : DeclName → ZFSet.{u}}
    (agrees : ∀ c, objectScons.constantType c ≠ none → consts c = sconsConsts h c)
    (atFrom : consts fromN = fromValue) (η : Env.{u} 1)
    (sat : Sat (objHeads h) consts (.snoc .nil cnum : CCtx Tower.Head 1) η) :
    ev (objHeads h) consts (cfrom (.var 0) : CTm Tower.Head 1) η =
      ev (objHeads h) consts (cscons (.var 0) (cfrom (csuc (.var 0))) : CTm Tower.Head 1) η := by
  have base := agrees_object h agrees
  have hn : η 0 ∈ ZFSet.omega := by
    have member := sat 0
    change η 0 ∈ consts numN at member
    rwa [num_value h base] at member
  show traceApp (consts fromN) (η 0) =
    traceApp (traceApp (consts sconsN) (η 0))
      (traceApp (consts fromN) (traceApp (consts sucN) (η 0)))
  rw [atFrom, scons_at h agrees, suc_value h base hn, fromValue_apply hn,
    fromValue_apply (insert_mem_omega hn), sconsValue_apply hn (fromStream_mem _)]
  exact fromStream_unfold hn

/-- **The set value of `from` satisfies its written equation** at every typed instance. -/
theorem from_valid {consts : DeclName → ZFSet.{u}}
    (agrees : ∀ c, objectScons.constantType c ≠ none → consts c = sconsConsts h c)
    (atFrom : consts fromN = fromValue) :
    ∀ e ∈ [fromEquation], ∀ η : Env.{u} e.arity, Sat (objHeads h) consts e.telescope η →
      ev (objHeads h) consts e.left η = ev (objHeads h) consts e.right η := by
  intro e member η sat
  obtain rfl : e = fromEquation := by simpa using member
  exact fromEquation_valid h agrees atFrom η sat

/-- The set of the type of `from`. -/
theorem ev_fromType {consts : DeclName → ZFSet.{u}}
    (agrees : ∀ c, objectChurch.constantType c ≠ none → consts c = objectSetConsts h c) :
    ev (objHeads h) consts (fromType : CTm Tower.Head 0) Fin.elim0 =
      tracePiSet ZFSet.omega (fun _ => streams) := by
  show tracePiSet (consts numN) (fun _ => tracePiSet (consts numN) (fun _ => consts numN)) = _
  rw [num_value h agrees]
  rfl

/-- The assignment of the model: `scons` and `from` as their set values. -/
noncomputable def fromConsts : DeclName → ZFSet.{u} :=
  Function.update (sconsConsts h) fromN fromValue

/-- **The package with the endless stream, defined by its written equation, has a set
model**, relative to `CofinalInaccessibles`. -/
theorem objectFrom_model (consts : DeclName → ZFSet.{u})
    (agrees : ∀ c, objectFrom.constantType c ≠ none → consts c = fromConsts h c) :
    SetModel (objHeads h) consts objectFrom :=
  definition_setModel_of_value objectScons (objectScons_model h) from_new fromValue
    (fun _ agreesScons _ => by
      rw [ev_fromType h (agrees_object h agreesScons)]
      exact fromValue_mem)
    (fun _ agreesScons atFrom => from_valid h agreesScons atFrom) consts agrees

/-- The model at the assignment itself. -/
theorem objectFrom_model_read : SetModel (objHeads h) (fromConsts h) objectFrom :=
  objectFrom_model h (fromConsts h) fun _ _ => rfl

include h in
/-- **Consistency**, relative to `CofinalInaccessibles`: no closed term of the package with the
endless stream has the type `Π (X : U₀). X`. -/
theorem objectFrom_consistent (t : CTm Tower.Head 0) : ¬ CTyped objectFrom .nil t emptyType :=
  CDerivable.no_closed_inhabitant (objectFrom_model_read h)
    (ev_emptyType h ZFSet.omega ∅ (fun _ => 0) (fromConsts h)) t

end Model

/-! ## Finite observations in the judgment -/

section Rules

variable {n : Nat} {Γ : CCtx Tower.Head n}

/-- A derivation of the object package is one of the package with the endless stream. -/
theorem ofObjectFrom {s : CStatement Tower.Head} (derivation : CDerivable objectChurch s) :
    CDerivable objectFrom s :=
  CDerivable.sum_left _ (CDerivable.sum_left _ derivation)

/-- The type of streams is a type of the lowest universe. -/
theorem stream_formed : CTyped objectChurch Γ streamT cU0 := cpiT cnum_typed cnum_typed

/-- `scons` is declared at its type in the package with the endless stream. -/
theorem scons_declared : objectFrom.constantType sconsN = some sconsType :=
  (ChurchRulesSub.sum_left objectScons _).constantType
    (withDefinition_defined objectChurch scons_new)

/-- **`scons` has its declared type.** -/
theorem scons_typed : CTyped objectFrom Γ (.const sconsN) sconsType :=
  definition_typed scons_declared
    (ofObjectFrom (cpiT cnum_typed (cpiT stream_formed stream_formed)))
    (LevelTower.IsUniverse.sort _)

/-- **`from` has its declared type**: from a number, a stream. -/
theorem from_typed : CTyped objectFrom Γ (.const fromN) fromType :=
  definition_typed (withDefinition_defined objectScons from_new)
    (ofObjectFrom (cpiT cnum_typed stream_formed)) (LevelTower.IsUniverse.sort _)

theorem cfrom_typed {x : CTm Tower.Head n} (hx : CTyped objectFrom Γ x cnum) :
    CTyped objectFrom Γ (cfrom x) streamT :=
  .appElim (B := streamT) from_typed hx

theorem cscons_typed {a s : CTm Tower.Head n} (ha : CTyped objectFrom Γ a cnum)
    (hs : CTyped objectFrom Γ s streamT) : CTyped objectFrom Γ (cscons a s) streamT :=
  .appElim (B := streamT) (.appElim (B := .pi streamT streamT) scons_typed ha) hs

theorem csuc_typed_from {x : CTm Tower.Head n} (hx : CTyped objectFrom Γ x cnum) :
    CTyped objectFrom Γ (csuc x) cnum :=
  .appElim (B := cnum) (ofObjectFrom csucConst_typed) hx

/-- **The written equation in the judgment**: at a number, `from` is the number before `from`
at its successor. -/
theorem from_rule {x : CTm Tower.Head n} (hx : CTyped objectFrom Γ x cnum) :
    CEqual objectFrom Γ (cfrom x) (cscons x (cfrom (csuc x))) streamT :=
  have typed : CSubstMor objectFrom (CCtx.snoc .nil cnum) Γ (fun _ : Fin 1 => x) :=
    fun j => match j with
      | ⟨0, _⟩ => hx
  equation_holds _ (StepsWithin.sum_right _ _) (e := fromEquation) List.mem_cons_self
    (fun _ => x) typed (cfrom_typed hx) (cscons_typed hx (cfrom_typed (csuc_typed_from hx)))

/-- The first equation of `scons` in the judgment. -/
theorem scons_first_rule {a s : CTm Tower.Head n} (ha : CTyped objectFrom Γ a cnum)
    (hs : CTyped objectFrom Γ s streamT) :
    CEqual objectFrom Γ (.app (cscons a s) czero) a cnum :=
  have typed : CSubstMor objectFrom (CCtx.snoc (.snoc .nil cnum) streamT) Γ
      (fun i : Fin 2 => [s, a].getD i.val a) :=
    fun j => match j with
      | ⟨0, _⟩ => hs
      | ⟨1, _⟩ => ha
  equation_holds _
    ((StepsWithin.sum_right objectChurch _).trans (StepsWithin.sum_left objectScons _))
    (e := sconsFirst) List.mem_cons_self (fun i => [s, a].getD i.val a) typed
    (.appElim (B := cnum) (cscons_typed ha hs) (ofObjectFrom czero_typed)) ha

/-- The second equation of `scons` in the judgment. -/
theorem scons_later_rule {a s k : CTm Tower.Head n} (ha : CTyped objectFrom Γ a cnum)
    (hs : CTyped objectFrom Γ s streamT) (hk : CTyped objectFrom Γ k cnum) :
    CEqual objectFrom Γ (.app (cscons a s) (csuc k)) (.app s k) cnum :=
  have typed : CSubstMor objectFrom (CCtx.snoc (.snoc (.snoc .nil cnum) streamT) cnum) Γ
      (fun i : Fin 3 => [k, s, a].getD i.val a) :=
    fun j => match j with
      | ⟨0, _⟩ => hk
      | ⟨1, _⟩ => hs
      | ⟨2, _⟩ => ha
  equation_holds _
    ((StepsWithin.sum_right objectChurch _).trans (StepsWithin.sum_left objectScons _))
    (e := sconsLater) (List.mem_cons_of_mem _ List.mem_cons_self)
    (fun i => [k, s, a].getD i.val a) typed
    (.appElim (B := cnum) (cscons_typed ha hs) (csuc_typed_from hk))
    (.appElim (B := cnum) hs hk)

/-- **The first element of the stream from `x` on is `x`**: two uses of the equations. Reading
at a position stops, although unfolding the stream does not. -/
theorem from_first {x : CTm Tower.Head n} (hx : CTyped objectFrom Γ x cnum) :
    CEqual objectFrom Γ (.app (cfrom x) czero) x cnum :=
  .trans (.appCong (B := cnum) (from_rule hx) (.refl (ofObjectFrom czero_typed)))
    (scons_first_rule hx (cfrom_typed (csuc_typed_from hx)))

/-- **The second element of the stream from `x` on is the successor of `x`.** -/
theorem from_second {x : CTm Tower.Head n} (hx : CTyped objectFrom Γ x cnum) :
    CEqual objectFrom Γ (.app (cfrom x) (csuc czero)) (csuc x) cnum :=
  have next := csuc_typed_from hx
  have zero : CTyped objectFrom Γ czero cnum := ofObjectFrom czero_typed
  .trans (.appCong (B := cnum) (from_rule hx) (.refl (csuc_typed_from zero)))
    (.trans (scons_later_rule hx (cfrom_typed next) zero) (from_first next))

/-- Positive example: the second element of the stream from zero on is one, also in the set
model. -/
theorem from_zero_second_holds (h : CofinalInaccessibles.{u}) :
    Holds (objHeads h) (fromConsts h)
      (.equality .nil (.app (cfrom czero) (csuc czero)) (csuc czero) cnum) :=
  CDerivable.sound (objectFrom_model_read h) (from_second (ofObjectFrom czero_typed))

end Rules

/-! ## The same equation among the finite lists -/

/-- The name of the would-be list of the numbers from a number on. -/
def fromListN : DeclName := .str .anonymous "fromList"

/-- `fromList n ⟶ cons n (fromList (suc n))`: the written equation at the type of lists. -/
def fromListEquation : DefiningEquation Tower.Head where
  arity := 1
  telescope := .snoc .nil cnum
  left := .app (.const fromListN) (.var 0)
  right := ccons (.var 0) (.app (.const fromListN) (csuc (.var 0)))

/-- The package with the lists, their length, and `fromList : num → list` with that
equation. -/
abbrev objectFromList :=
  withDefinition objectLength fromListN (.pi cnum clist) [fromListEquation]

/-- The numerals of the candidate. -/
def numeralTerm : Nat → CTm Tower.Head 0
  | 0 => czero
  | k + 1 => csuc (numeralTerm k)

/-- `fromList` applied to a numeral. -/
abbrev fromListAt (k : Nat) : CTm Tower.Head 0 := .app (.const fromListN) (numeralTerm k)

section NoList

/-- A derivation of the package with the length is one of the package with `fromList`. -/
theorem ofLength {s : CStatement Tower.Head} (derivation : CDerivable objectLength s) :
    CDerivable objectFromList s :=
  CDerivable.sum_left _ derivation

theorem fromList_typed : CTyped objectFromList .nil (.const fromListN) (.pi cnum clist) :=
  definition_typed (withDefinition_defined objectLength (by decide))
    (ofLength (ofListsLength (lpiT num_typed_one list_typed_one))) (LevelTower.IsUniverse.sort _)

theorem numeralTerm_typed : ∀ k : Nat, CTyped objectFromList .nil (numeralTerm k) cnum
  | 0 => ofLength (ofListsLength (ofObject czero_typed))
  | k + 1 => .appElim (B := cnum) (ofLength (ofListsLength (ofObject csucConst_typed)))
      (numeralTerm_typed k)

theorem fromListAt_typed (k : Nat) : CTyped objectFromList .nil (fromListAt k) clist :=
  .appElim (B := clist) fromList_typed (numeralTerm_typed k)

theorem lengthAt_typed (k : Nat) : CTyped objectFromList .nil (clength (fromListAt k)) cnum :=
  .appElim (B := cnum) (ofLength length_typed) (fromListAt_typed k)

/-- **In the judgment the length of `fromList` at a numeral is one more than at the next**:
the written equation, then the second equation of the length. -/
theorem length_fromList (k : Nat) :
    CEqual objectFromList .nil (clength (fromListAt k)) (csuc (clength (fromListAt (k + 1))))
      cnum := by
  have consTyped : CTyped objectFromList .nil (ccons (numeralTerm k) (fromListAt (k + 1))) clist :=
    .appElim (B := clist)
      (.appElim (B := .pi clist clist) (ofLength (ofListsLength consConst_typed))
        (numeralTerm_typed k))
      (fromListAt_typed (k + 1))
  have unfolded : CEqual objectFromList .nil (fromListAt k)
      (ccons (numeralTerm k) (fromListAt (k + 1))) clist :=
    equation_holds _ (StepsWithin.sum_right _ _) (e := fromListEquation) List.mem_cons_self
      (fun _ => numeralTerm k)
      (fun j => match j with
        | ⟨0, _⟩ => numeralTerm_typed k)
      (fromListAt_typed k) consTyped
  have lengths : CEqual objectFromList .nil (clength (fromListAt k))
      (clength (ccons (numeralTerm k) (fromListAt (k + 1)))) cnum :=
    .appCong (B := cnum) (.refl (ofLength length_typed)) unfolded
  have typed : CSubstMor objectFromList (CCtx.snoc (.snoc .nil cnum) clist) .nil
      (fun i : Fin 2 => [fromListAt (k + 1), numeralTerm k].getD i.val (numeralTerm k)) :=
    fun j => match j with
      | ⟨0, _⟩ => fromListAt_typed (k + 1)
      | ⟨1, _⟩ => numeralTerm_typed k
  have consRule : CEqual objectFromList .nil
      (clength (ccons (numeralTerm k) (fromListAt (k + 1))))
      (csuc (clength (fromListAt (k + 1)))) cnum :=
    equation_holds _
      ((StepsWithin.sum_right objectLists _).trans (StepsWithin.sum_left objectLength _))
      (e := recursionEquation lengthN listN consN [.closed (.const numN), .recursive]
        (lengthBody consN [.closed (.const numN), .recursive]))
      (List.mem_cons_of_mem _ List.mem_cons_self)
      (fun i => [fromListAt (k + 1), numeralTerm k].getD i.val (numeralTerm k)) typed
      (.appElim (B := cnum) (ofLength length_typed) consTyped)
      (.appElim (B := cnum) (ofLength (ofListsLength (ofObject csucConst_typed)))
        (lengthAt_typed (k + 1)))
  exact .trans lengths consRule

/-- Negative example: **the written equation at the type of lists has no set model**, at any
assignment that agrees with the object package's on the names that one declares. In a model
the length of `fromList` at each numeral is a natural number one above the length at the
next, so the length at zero is above every natural number. -/
theorem fromList_no_setModel (h : CofinalInaccessibles.{u}) (consts : DeclName → ZFSet.{u})
    (agrees : ∀ c, objectDeclared c = true → objectSetConsts h c = consts c) :
    ¬ SetModel (objHeads h) consts objectFromList := by
  intro model
  have numbers : ev (objHeads h) consts (cnum : CTm Tower.Head 0) Fin.elim0 = ZFSet.omega := by
    show consts numN = ZFSet.omega
    rw [← agrees numN (by decide), setConst_num]
  have member : ∀ k : Nat,
      ev (objHeads h) consts (clength (fromListAt k)) Fin.elim0 ∈ ZFSet.omega := by
    intro k
    have typed := CDerivable.sound model (lengthAt_typed k) Fin.elim0 (sat_nil _ _ _)
    rwa [numbers] at typed
  have step : ∀ k : Nat, ev (objHeads h) consts (clength (fromListAt k)) Fin.elim0 =
      insert (ev (objHeads h) consts (clength (fromListAt (k + 1))) Fin.elim0)
        (ev (objHeads h) consts (clength (fromListAt (k + 1))) Fin.elim0) := by
    intro k
    refine (CDerivable.sound model (length_fromList k) Fin.elim0 (sat_nil _ _ _)).1.trans ?_
    show traceApp (consts sucN) _ = _
    rw [← agrees sucN (by decide)]
    exact suc_apply h (member (k + 1))
  have size : ∀ k : Nat,
      natOf (ev (objHeads h) consts (clength (fromListAt 0)) Fin.elim0) =
        natOf (ev (objHeads h) consts (clength (fromListAt k)) Fin.elim0) + k := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [ih, step k, natOf_insert (member (k + 1))]
      omega
  have beyond := size (natOf (ev (objHeads h) consts (clength (fromListAt 0)) Fin.elim0) + 1)
  omega

end NoList

end Mettapedia.Languages.MeTTa.PrimeCandidates.Trinity.Stream
