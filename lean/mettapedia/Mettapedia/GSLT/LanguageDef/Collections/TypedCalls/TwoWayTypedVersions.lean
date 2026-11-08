import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.GroundUninterpretedVersions

/-!
# Trusted versions with typed entry facts, under logic variables

The two-way model of `GroundUninterpretedVersions` (one substitution for every
parameter, head unification, bodies binding any variable, ANY arguments
included) extended to the entry facts that claim groundness and types: GROUND
and INSTANCE at a closed formal, the polymorphic pair (UNINTERPRETED), ANY, and
the space parameter (UNINTERPRETED_SPACE); and to the claims a version reads at
them, types included (`ContractValue.type`).

* **The analysis** (`TAdmits`) is the C's `contract_eval` with its type claims:
  a head variable's type from `contract_invert` (`eqTypes`, `PatFact`), a
  literal's class, a constructor's declared result (`CtorTyped`,
  `contract_constructed_type`), an operation's class, a version's closed range
  (`calleeValue`), joins keeping agreeing types (`tjoin`); a call to itself
  checked per position (`SelfMeets`, `contract_self_call`), a call into another
  version too (`EnterPos`, `contract_meets_version`, which never enters a space
  parameter); a `match` only over a space variable or a space named in the
  version (`matchVar`, `matchNamed`, `contract_match`).
* **Soundness** (`tadmits_run`): every claim of groundness holds in every run,
  with its uninterpreted and type claims; and two runs whose calls agree where the
  versions admit them, and whose spaces agree on the rows of every space the entry
  admits, have the same outcomes. A type is read only together with groundness,
  which no binding changes.
* **Entry** (`tentry_ground`, `entry_types`, `entry_spaces`, `entry_pair`): two-way
  head unification of admitted arguments keeps the entry marks, the type facts
  (`patFact_subst`: the constructor inversion at the argument the pattern was
  unified with), the space variables and the polymorphic pattern's argument.
* **The version theorem** (`typed_version_eq_protocol`): at admitted arguments the
  version is the protocol at every fuel, multiplicity included, whenever the
  protocol's row reduces to the body there (`RowReduces`). The rows that do:
  closed rows with GROUND and unguarded ANY or space formals
  (`ground_typed_version_eq_protocol`), the pair beside them
  (`pair_typed_version_eq_protocol`), and a signature's instance
  (`instance_typed_version_eq_protocol`, `contract_instance_version`). A checked
  call whose guards and entry test pass answers through the version as through
  the protocol (`checked_ground_call_eq`).
* **Controls**: `(down 3)` (a GROUND countdown) answers `0`; the version entered at
  the open argument `$v` of a GROUND parameter, which the protocol's guard passes
  once and the entry test refuses, answers `1` twice where the protocol answers it
  once (`ground_entry_needed`); `build`'s instance version is the protocol of
  `(-> Number (List $a) (List $a))` (`build_version`); `tag`, the pair beside a
  GROUND parameter and an ANY parameter the body binds to the declared `inc`, is
  the protocol of `(-> $t Number %Undefined% $t)` (`tag_version`).

Calls answer values only; a callee binding its arguments is outside the model.
GROUND at a private formal (`contract_private_formal`) and ANY or space parameters at
private type variables reduce to these rows (`PrivateSpaceVersions`).
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.TwoWayTypedVersions

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open UnifyingRegions UnifyingFrames OpenFrameEffects CapturedUninterpretedRegions
open ContractBindingFacts (Flags Facts ValueFlags mergeFlags patternUninterpreted
  patternKeepsClaims bindPattern_equation ground_pattern_marks uninterpreted_substituted_variable)
open GroundUninterpretedVersions

/-! ## Values, positions, programs -/

/-- What the analysis claims of every answer of an occurrence (`ContractValue`):
its flags and a closed type, which a reader uses only together with the ground
claim. -/
structure TValue where
  flags : ValueFlags
  type : Option (Ty Empty)

/-- No answer: `(empty)`, or a branch that never returns. -/
def noAnswer : TValue := ⟨bottomValue, none⟩

/-- `contract_join`: the flags joined; a type kept where both branches give it,
or where one of them has no answer. -/
def tjoin (a b : TValue) : TValue :=
  ⟨join a.flags b.flags,
    if a.flags.bottom then b.type else if b.flags.bottom then a.type
    else if a.type = b.type then a.type else none⟩

/-- A parameter's entry fact (`PettaContractEntryFact`): ANY; a space a `match`
reads (UNINTERPRETED_SPACE); GROUND, or INSTANCE once the instance is applied, at
a closed formal; the polymorphic pair (UNINTERPRETED). -/
inductive Pos where
  | any
  | space
  | ground (A : Ty Empty)
  | pair
  deriving DecidableEq

/-- What a version proves of its answers: a ground value of its closed range; the
argument at its polymorphic pair; nothing, where the range is not checked. -/
inductive Result where
  | closed (R : Ty Empty)
  | pair
  | free

/-- What the analysis knows of the program: the relation's positions and result,
the versions other relations offer, the operations PeTTa provides with the class
of their values (`contract_pure_operation`), and the spaces the equations match
by name (`PettaContractVersion.spaces`). -/
structure TProgram where
  positions : List Pos
  result : Result
  versions : String → Option (List Pos × Result)
  prim : String → ℕ → Option String
  spaces : List String

def tAnyBottom (vs : List TValue) : Bool := anyBottom (vs.map (·.flags))

/-- The element at the first polymorphic pair. -/
def pairAt {α : Type} : List Pos → List α → Option α
  | .pair :: _, a :: _ => some a
  | _ :: ps, _ :: as => pairAt ps as
  | _, _ => none

/-- The flags of the value at the polymorphic pair (`contract_call`'s loop). -/
def pairFlags (qs : List Pos) (vs : List TValue) : Flags :=
  match pairAt qs vs with
  | some v => v.flags.toFlags
  | none => ⟨false, false⟩

/-- What a call into a version claims (`contract_self_call`, `contract_call`). -/
def calleeValue (qs : List Pos) (res : Result) (vs : List TValue) : TValue :=
  if tAnyBottom vs then noAnswer
  else match res with
    | .closed R => ⟨⟨⟨true, false⟩, false⟩, some R⟩
    | .pair => ⟨⟨pairFlags qs vs, false⟩, none⟩
    | .free => ⟨⟨⟨false, false⟩, false⟩, none⟩

/-- `contract_self_call` at one position: ANY asks nothing; a space parameter is
passed a variable holding a space; GROUND and INSTANCE a ground value of the
formal; the pair a ground uninterpreted value. -/
def SelfPos (Sp : String → Prop) : Pos → Expr → TValue → Prop
  | .any, _, _ => True
  | .space, e, _ => ∃ x, e = .var x ∧ Sp x
  | .ground A, _, v => v.flags.ground = true ∧ v.type = some A
  | .pair, _, v => v.flags.ground = true ∧ v.flags.uninterpreted = true

inductive SelfMeets (Sp : String → Prop) : List Pos → List Expr → List TValue → Prop
  | nil : SelfMeets Sp [] [] []
  | cons {p : Pos} {ps : List Pos} {e : Expr} {es : List Expr} {v : TValue} {vs : List TValue} :
      SelfPos Sp p e v → SelfMeets Sp ps es vs → SelfMeets Sp (p :: ps) (e :: es) (v :: vs)

/-- `contract_meets_version` at one position: a version with a space parameter is
never entered from another relation. -/
def EnterPos : Pos → TValue → Prop
  | .any, _ => True
  | .space, _ => False
  | .ground A, v => v.flags.ground = true ∧ v.type = some A
  | .pair, v => v.flags.ground = true ∧ v.flags.uninterpreted = true

/-- `contract_constructed_type`: a constructor whose one declaration is in the
class, each field that is not free given a part typed at its instance, which is
no metatype name. -/
def CtorTyped (Γ : Decls) (c : String) (vs : List TValue) (T : Ty Empty) : Prop :=
  ∃ (Bs : List (Ty String)) (R : Ty String) (σ : String → Ty Empty),
    Γ c = [arrow Bs R] ∧ Constructor Bs R ∧
    List.Forall₂ (fun B v => ¬ FreeField R B → ¬ MetaName (B.bind σ) ∧
      TValue.type v = some (B.bind σ)) Bs vs ∧
    T = R.bind σ

/-! ## The analysis -/

mutual
/-- **The analysis** (`contract_eval`) with its type claims, under the type facts
`Φ` of the head patterns (`contract_invert`) and the space variables `Sp`. -/
inductive TAdmits (Γ : Decls) (grounded : String → Bool) (P : TProgram)
    (Φ : String → Ty Empty → Prop) (Sp : String → Prop) : Facts → Expr → TValue → Facts → Prop
  | var (F : Facts) (x : String) (t : Option (Ty Empty)) (typed : ∀ U, t = some U → Φ x U) :
      TAdmits Γ grounded P Φ Sp F (.var x) ⟨varValue F x, t⟩ F
  | const (F : Facts) (a : Atom) (t : Option (Ty Empty))
      (typed : ∀ T, t = some T → support a = ∅ ∧ Holds Γ grounded a T) :
      TAdmits Γ grounded P Φ Sp F (.const a) ⟨⟨atomFlags Γ F a, false⟩, t⟩ F
  | ctor {F F' : Facts} {c : String} {args : List Expr} {vs : List TValue} {t : Option (Ty Empty)} :
      TAdmitsAll Γ grounded P Φ Sp F args vs F' → (∀ T, t = some T → CtorTyped Γ c vs T) →
      TAdmits Γ grounded P Φ Sp F (.ctor c args) ⟨dataValue Γ c (vs.map (·.flags)), t⟩ F'
  | self {F F' : Facts} {args : List Expr} {vs : List TValue} :
      TAdmitsAll Γ grounded P Φ Sp F args vs F' →
      (tAnyBottom vs = true ∨ SelfMeets Sp P.positions args vs) →
      TAdmits Γ grounded P Φ Sp F (.self args) (calleeValue P.positions P.result vs) F'
  | prim {F F' : Facts} {op : String} {args : List Expr} {vs : List TValue} {c : String} :
      TAdmitsAll Γ grounded P Φ Sp F args vs F' → P.prim op args.length = some c →
      TAdmits Γ grounded P Φ Sp F (.prim op args) ⟨primValue (vs.map (·.flags)), some (.sym c)⟩ F'
  | call {F F' : Facts} {f : String} {args : List Expr} {vs : List TValue} (t : Option (Ty Empty)) :
      TAdmitsAll Γ grounded P Φ Sp F args vs F' →
      TAdmits Γ grounded P Φ Sp F (.call f args) ⟨keptValue (vs.map (·.flags)), t⟩ F'
  | enter {F F' : Facts} {f : String} {args : List Expr} {vs : List TValue} {qs : List Pos}
      {res : Result} :
      TAdmitsAll Γ grounded P Φ Sp F args vs F' → P.versions f = some (qs, res) →
      (tAnyBottom vs = true ∨ List.Forall₂ EnterPos qs vs) →
      TAdmits Γ grounded P Φ Sp F (.enter f args) (calleeValue qs res vs) F'
  | letBottom {F F' : Facts} {p : Pat} {val body : Expr} {vv : TValue} :
      TAdmits Γ grounded P Φ Sp F val vv F' → vv.flags.bottom = true →
      TAdmits Γ grounded P Φ Sp F (.letE p val body) vv F'
  | letE {F F₁ F₂ F₃ : Facts} {p : Pat} {val body : Expr} {vv bv : TValue} :
      TAdmits Γ grounded P Φ Sp F val vv F₁ → vv.flags.bottom = false →
      BindAny Γ F₁ p vv.flags F₂ → TAdmits Γ grounded P Φ Sp F₂ body bv F₃ →
      TAdmits Γ grounded P Φ Sp F (.letE p val body) bv F₃
  | ifE {F F₁ Ft Fe : Facts} {c t e : Expr} {cv tv ev : TValue} :
      TAdmits Γ grounded P Φ Sp F c cv F₁ → TAdmits Γ grounded P Φ Sp F₁ t tv Ft →
      TAdmits Γ grounded P Φ Sp F₁ e ev Fe → TAdmits Γ grounded P Φ Sp F (.ifE c t e) (tjoin tv ev) F₁
  | empty (F : Facts) : TAdmits Γ grounded P Φ Sp F .empty noAnswer F
  | caseBottom {F F₁ : Facts} {key : Expr} {ps : List Pat} {bs : List Expr} {kv : TValue} :
      TAdmits Γ grounded P Φ Sp F key kv F₁ → kv.flags.bottom = true →
      TAdmits Γ grounded P Φ Sp F (.caseE key ps bs) kv F₁
  | caseE {F F₁ : Facts} {key : Expr} {ps : List Pat} {bs : List Expr} {kv v : TValue} :
      TAdmits Γ grounded P Φ Sp F key kv F₁ → kv.flags.bottom = false →
      TAdmitsArms Γ grounded P Φ Sp F₁ kv ps bs v →
      TAdmits Γ grounded P Φ Sp F (.caseE key ps bs) v F₁
  | matchVar {F F₂ : Facts} {x : String} {p : Pat} {t : Expr} {tv : TValue} :
      Sp x → patternUninterpreted Γ F p.toAtom = true →
      TAdmits Γ grounded P Φ Sp (markPat F p ⟨false, true⟩) t tv F₂ →
      TAdmits Γ grounded P Φ Sp F (.matchE (.var x) p t) tv F₂
  | matchNamed {F F₂ : Facts} {s : String} {p : Pat} {t : Expr} {tv : TValue} :
      s ∈ P.spaces → patternUninterpreted Γ F p.toAtom = true →
      TAdmits Γ grounded P Φ Sp (markPat F p ⟨false, true⟩) t tv F₂ →
      TAdmits Γ grounded P Φ Sp F (.matchE (.const (.symbol s)) p t) tv F₂

/-- Arguments, left to right. -/
inductive TAdmitsAll (Γ : Decls) (grounded : String → Bool) (P : TProgram)
    (Φ : String → Ty Empty → Prop) (Sp : String → Prop) :
    Facts → List Expr → List TValue → Facts → Prop
  | nil (F : Facts) : TAdmitsAll Γ grounded P Φ Sp F [] [] F
  | cons {F F₁ F₂ : Facts} {e : Expr} {es : List Expr} {v : TValue} {vs : List TValue} :
      TAdmits Γ grounded P Φ Sp F e v F₁ → TAdmitsAll Γ grounded P Φ Sp F₁ es vs F₂ →
      TAdmitsAll Γ grounded P Φ Sp F (e :: es) (v :: vs) F₂

/-- The arms of a `case`, each from the facts after the key. -/
inductive TAdmitsArms (Γ : Decls) (grounded : String → Bool) (P : TProgram)
    (Φ : String → Ty Empty → Prop) (Sp : String → Prop) :
    Facts → TValue → List Pat → List Expr → TValue → Prop
  | nil (F : Facts) (kv : TValue) : TAdmitsArms Γ grounded P Φ Sp F kv [] [] noAnswer
  | cons {F F₂ F₃ : Facts} {kv : TValue} {p : Pat} {ps : List Pat} {b : Expr} {bs : List Expr}
      {bv rest : TValue} :
      BindAny Γ F p kv.flags F₂ → TAdmits Γ grounded P Φ Sp F₂ b bv F₃ →
      TAdmitsArms Γ grounded P Φ Sp F kv ps bs rest →
      TAdmitsArms Γ grounded P Φ Sp F kv (p :: ps) (b :: bs) (tjoin bv rest)
end

/-! ## What the claims say -/

section Claims

variable (Γ : Decls) (grounded : String → Bool)

/-- A value's claims hold of an outcome: its flags, and, where it claims ground,
the type it claims. -/
def TFaithful (out : Outcome) (v : TValue) : Prop :=
  Faithful Γ out v.flags ∧
    (v.flags.ground = true → ∀ T, v.type = some T → Holds Γ grounded (substA out.2 out.1) T)

def TArgsFaithful (σ : Substitution) (as : List Atom) (vs : List TValue) : Prop :=
  List.Forall₂ (fun a v => TFaithful Γ grounded (a, σ) v) as vs

/-- The type facts of the head patterns hold, of ground values. -/
def TypeSound (Φ : String → Ty Empty → Prop) (σ : Substitution) : Prop :=
  ∀ x U, Φ x U → support (σ x) = ∅ ∧ Holds Γ grounded (σ x) U

/-- Every space variable holds a ground value the entry admitted. -/
def SpaceSound (Ok : Atom → Prop) (Sp : String → Prop) (σ : Substitution) : Prop :=
  ∀ x, Sp x → support (σ x) = ∅ ∧ Ok (σ x)

/-- **The entry facts at a position**: what the protocol's guards and the version's
entry test establish (`oem_entry_facts_hold`). `Ok` is the test of a space. -/
def PosAdmits (Ok : Atom → Prop) : Pos → Atom → Prop
  | .any, _ => True
  | .space, w => support w = ∅ ∧ Ok w
  | .ground A, w => support w = ∅ ∧ Holds Γ grounded w A
  | .pair, w => support w = ∅ ∧ Uninterp Γ w

/-- Arguments a version admits. -/
def TAdmitted (Ok : Atom → Prop) (ps : List Pos) (ws : List Atom) : Prop :=
  List.Forall₂ (PosAdmits Γ grounded Ok) ps ws

/-- What a version's call answers at arguments it admits. -/
def Answers : Result → List Pos → List Atom → Atom → Prop
  | .closed R, _, _, r => support r = ∅ ∧ Holds Γ grounded r R
  | .pair, ps, ws, r => pairAt ps ws = some r
  | .free, _, _, _ => True

/-- What a run assumes of its calls: a version's call answers what its version
proves at the arguments it admits; PeTTa's operations answer literals of their
class. -/
structure TOraclesOK (Ok : Atom → Prop) (P : TProgram) (E : Env) (O : Oracle) : Prop where
  self : ∀ ws, TAdmitted Γ grounded Ok P.positions ws →
    ∀ r ∈ O.self ws, Answers Γ grounded P.result P.positions ws r
  enter : ∀ f qs res, P.versions f = some (qs, res) → ∀ ws, TAdmitted Γ grounded Ok qs ws →
    ∀ r ∈ O.enter f ws, Answers Γ grounded res qs ws r
  prim : ∀ op ws c, P.prim op ws.length = some c → ∀ r ∈ E.prim op ws, Literal c r

/-- Two runs whose calls agree where the versions admit them, whose operations and
kept calls agree, and whose spaces agree on the rows of the spaces the entry
admits. -/
structure TAgree (Ok : Atom → Prop) (P : TProgram) (E E' : Env) (O O' : Oracle) : Prop where
  self : ∀ ws, TAdmitted Γ grounded Ok P.positions ws → O.self ws = O'.self ws
  enter : ∀ f qs res, P.versions f = some (qs, res) → ∀ ws, TAdmitted Γ grounded Ok qs ws →
    O.enter f ws = O'.enter f ws
  prim : E.prim = E'.prim
  kept : E.kept = E'.kept
  rows : ∀ w, Ok w → E.rows w = E'.rows w
  named : ∀ s ∈ P.spaces, Ok (.symbol s)

end Claims

/-! ## Elementary facts -/

section Elementary

variable {Γ : Decls} {grounded : String → Bool}

theorem TAgree.refl {Ok : Atom → Prop} {P : TProgram} {E : Env} {O : Oracle}
    (named : ∀ s ∈ P.spaces, Ok (.symbol s)) : TAgree Γ grounded Ok P E E O O :=
  ⟨fun _ _ => rfl, fun _ _ _ _ _ _ => rfl, rfl, rfl, fun _ _ => rfl, named⟩

theorem TFaithful.keep {σ τ : Substitution} {a : Atom} {v : TValue}
    (faithful : TFaithful Γ grounded (a, σ) v) (keeps : KeepsGround σ τ) :
    TFaithful Γ grounded (a, τ) v := by
  refine ⟨faithful.1.keep keeps, fun ground T typed => ?_⟩
  have isGround : support (substA σ a) = ∅ := (faithful.1.2 ground).1
  change Holds Γ grounded (substA τ a) T
  rw [keeps.observe isGround]
  exact faithful.2 ground T typed

theorem TArgsFaithful.keep {σ τ : Substitution} {as : List Atom} {vs : List TValue}
    (faithful : TArgsFaithful Γ grounded σ as vs) (keeps : KeepsGround σ τ) :
    TArgsFaithful Γ grounded τ as vs :=
  faithful.imp fun _ _ each => each.keep keeps

theorem TArgsFaithful.flags {σ : Substitution} {as : List Atom} {vs : List TValue}
    (faithful : TArgsFaithful Γ grounded σ as vs) : ArgsFaithful Γ σ as (vs.map (·.flags)) :=
  List.forall₂_map_right_iff.mpr (faithful.imp fun _ _ each => each.1)

theorem TArgsFaithful.anyBottom_false {σ : Substitution} {as : List Atom} {vs : List TValue}
    (faithful : TArgsFaithful Γ grounded σ as vs) : tAnyBottom vs = false :=
  faithful.flags.anyBottom_false

theorem TypeSound.keep {Φ : String → Ty Empty → Prop} {σ τ : Substitution}
    (sound : TypeSound Γ grounded Φ σ) (keeps : KeepsGround σ τ) : TypeSound Γ grounded Φ τ := by
  intro x U fact
  obtain ⟨isGround, holds⟩ := sound x U fact
  rw [keeps x isGround]
  exact ⟨isGround, holds⟩

theorem SpaceSound.keep {Ok : Atom → Prop} {Sp : String → Prop} {σ τ : Substitution}
    (sound : SpaceSound Ok Sp σ) (keeps : KeepsGround σ τ) : SpaceSound Ok Sp τ := by
  intro x space
  obtain ⟨isGround, admitted⟩ := sound x space
  rw [keeps x isGround]
  exact ⟨isGround, admitted⟩

theorem tfaithful_tjoin_left {out : Outcome} {a : TValue} (b : TValue)
    (faithful : TFaithful Γ grounded out a) : TFaithful Γ grounded out (tjoin a b) := by
  refine ⟨faithful_join_left _ faithful.1, fun ground T typed => ?_⟩
  have notBottom : a.flags.bottom = false := faithful.1.1
  by_cases hb : b.flags.bottom = true
  · simp only [tjoin, join, notBottom, hb, Bool.false_eq_true, if_false, if_true] at ground typed
    exact faithful.2 ground T typed
  · have hb' : b.flags.bottom = false := by simpa using hb
    simp only [tjoin, join, notBottom, hb', Bool.false_eq_true, if_false] at ground typed
    have ga : a.flags.ground = true := (Bool.and_eq_true_iff.mp ground).1
    split_ifs at typed
    · exact faithful.2 ga T typed

theorem tfaithful_tjoin_right {out : Outcome} (a : TValue) {b : TValue}
    (faithful : TFaithful Γ grounded out b) : TFaithful Γ grounded out (tjoin a b) := by
  refine ⟨faithful_join_right _ faithful.1, fun ground T typed => ?_⟩
  have notBottom : b.flags.bottom = false := faithful.1.1
  by_cases ha : a.flags.bottom = true
  · simp only [tjoin, join, ha, if_true] at ground typed
    exact faithful.2 ground T typed
  · have ha' : a.flags.bottom = false := by simpa using ha
    simp only [tjoin, join, ha', notBottom, Bool.false_eq_true, if_false] at ground typed
    have gb : b.flags.ground = true := (Bool.and_eq_true_iff.mp ground).2
    split_ifs at typed with same
    · exact faithful.2 gb T (same ▸ typed)

theorem literal_ground {c : String} {r : Atom} (literal : Literal c r) : support r = ∅ := by
  cases r with
  | grounded _ => simp [support, UnifyAtoms.encode, Mettapedia.Logic.LP.Term.freeVars]
  | symbol _ => exact (literal : False).elim
  | var _ => exact (literal : False).elim
  | expression _ => exact (literal : False).elim

/-- Data's flags, from its parts' (`contract_eval_parts`). -/
theorem data_faithful {σ : Substitution} (c : String) {values : List Atom} {vs : List ValueFlags}
    (faithful : ArgsFaithful Γ σ values vs) :
    Faithful Γ (.expression (.symbol c :: values), σ) (dataValue Γ c vs) := by
  unfold dataValue
  rw [if_neg (by simp [ArgsFaithful.anyBottom_false faithful])]
  refine ⟨rfl, fun ground => ?_⟩
  have grounds : ∀ a ∈ values, support (substA σ a) = ∅ := by
    intro a member
    obtain ⟨w, wMember, fa⟩ := faithful.mem a member
    exact (fa.2 (List.all_eq_true.mp ground w wMember)).1
  refine ⟨?_, fun unint => ?_⟩
  · apply Finset.eq_empty_iff_forall_notMem.mpr
    intro y present
    change y ∈ support (substA σ (.expression (.symbol c :: values))) at present
    rw [substA, UnifyAtoms.substL_eq_map, List.map_cons, support_expression] at present
    obtain ⟨part, partMember, occurs⟩ := present
    rcases List.mem_cons.mp partMember with same | mapped
    · rw [same] at occurs
      simp [substA, support, UnifyAtoms.encode, Mettapedia.Logic.LP.Term.freeVars] at occurs
    · obtain ⟨a, aMember, rfl⟩ := List.mem_map.mp mapped
      rw [grounds a aMember] at occurs
      exact Finset.notMem_empty y occurs
  · have parts := Bool.and_eq_true_iff.mp unint
    change Uninterp Γ (substA σ (.expression (.symbol c :: values)))
    rw [substA, UnifyAtoms.substL_eq_map, List.map_cons]
    apply UnifyAtoms.uninterp_of_all
    intro part partMember
    rcases List.mem_cons.mp partMember with same | mapped
    · rw [same]
      exact List.isEmpty_iff.mp parts.1
    · obtain ⟨a, aMember, rfl⟩ := List.mem_map.mp mapped
      obtain ⟨w, wMember, fa⟩ := faithful.mem a aMember
      exact (fa.2 (List.all_eq_true.mp ground w wMember)).2
        (List.all_eq_true.mp parts.2 w wMember)

theorem fields_counted (hΓ : Functional Γ) {σ : Substitution} {R : Ty String}
    {θ : String → Ty Empty} :
    ∀ {Bs : List (Ty String)} {vs : List TValue} {values : List Atom},
      List.Forall₂ (fun B v => ¬ FreeField R B → ¬ MetaName (B.bind θ) ∧
        TValue.type v = some (B.bind θ)) Bs vs →
      TArgsFaithful Γ grounded σ values vs → (∀ v ∈ vs, v.flags.ground = true) →
      List.Forall₂ (fun B w => ¬ FreeField R B → count (info Γ w) (B.bind θ) = 1) Bs
        (values.map (substA σ))
  | _, _, _, .nil, .nil, _ => .nil
  | _, _, _, .cons field fields, .cons faithful rest, grounds =>
      .cons (fun notFree => by
          obtain ⟨notMeta, typed⟩ := field notFree
          exact (faithful.2 (grounds _ (by simp)) _ typed).count notMeta)
        (fields_counted hΓ fields rest fun w member => grounds w (by simp [member]))

/-- **A construction claimed typed is typed** (`contract_constructed_type`): its
parts, ground, hold their fields' types, and the constructor builds the type. -/
theorem ctor_typed_holds (hΓ : Functional Γ) {σ : Substitution} {c : String}
    {values : List Atom} {vs : List TValue} {T : Ty Empty}
    (faithful : TArgsFaithful Γ grounded σ values vs)
    (grounds : ∀ v ∈ vs, v.flags.ground = true) (typed : CtorTyped Γ c vs T) :
    Holds Γ grounded (substA σ (.expression (.symbol c :: values))) T := by
  obtain ⟨Bs, R, θ, row, cls, fields, rfl⟩ := typed
  have counted := fields_counted hΓ fields faithful grounds
  have shape : substA σ (.expression (.symbol c :: values)) =
      .expression (.symbol c :: values.map (substA σ)) := by
    rw [substA, UnifyAtoms.substL_eq_map, List.map_cons]
    rfl
  rw [shape]
  apply Holds.of_count
  exact ctor_construction hΓ row cls (values.map (substA σ)) counted.length_eq.symm θ
    fun p hp hf => (List.forall₂_iff_zip.mp counted).2 hp hf

theorem SelfMeets.length {Sp : String → Prop} :
    ∀ {ps : List Pos} {es : List Expr} {vs : List TValue}, SelfMeets Sp ps es vs →
      ps.length = vs.length
  | _, _, _, .nil => rfl
  | _, _, _, .cons _ rest => by simp [rest.length]

/-- The recipes of variables are themselves. -/
theorem evalAll_recipes (E : Env) (O : Oracle) :
    ∀ (es : List Expr) (σ : Substitution), ∀ out ∈ evalAll E O es σ,
      List.Forall₂ (fun e a => ∀ x, e = .var x → a = .var x) es out.1
  | [], σ, out, member => by
      simp only [evalAll, Multiset.mem_singleton] at member
      subst member
      exact .nil
  | e :: es, σ, out, member => by
      simp only [evalAll, Multiset.mem_bind, Multiset.mem_map] at member
      obtain ⟨first, present, rest, restPresent, rfl⟩ := member
      refine .cons (fun x isVar => ?_) (evalAll_recipes E O es first.2 rest restPresent)
      subst isVar
      simp only [eval, Multiset.mem_singleton] at present
      rw [present]

/-- **A call to itself the analysis admits is at arguments the version admits.** -/
theorem admitted_of_selfMeets {Ok : Atom → Prop} {Sp : String → Prop} {σ : Substitution}
    (spaces : SpaceSound Ok Sp σ) :
    ∀ {ps : List Pos} {es : List Expr} {as : List Atom} {vs : List TValue},
      SelfMeets Sp ps es vs → TArgsFaithful Γ grounded σ as vs →
      List.Forall₂ (fun e a => ∀ x, e = .var x → a = .var x) es as →
      TAdmitted Γ grounded Ok ps (as.map (substA σ))
  | _, _, _, _, .nil, .nil, .nil => .nil
  | p :: _, _, _, _, .cons here rest, .cons faithful faithfuls, .cons recipe recipes => by
      refine .cons ?_ (admitted_of_selfMeets spaces rest faithfuls recipes)
      cases p with
      | any => trivial
      | space =>
          obtain ⟨x, rfl, isSpace⟩ := here
          rw [recipe x rfl]
          exact spaces x isSpace
      | ground A =>
          obtain ⟨ground, typed⟩ := here
          exact ⟨(faithful.1.2 ground).1, faithful.2 ground A typed⟩
      | pair =>
          obtain ⟨ground, unint⟩ := here
          obtain ⟨isGround, clean⟩ := faithful.1.2 ground
          exact ⟨isGround, clean unint⟩

/-- **A call into another version the analysis admits is at arguments that
version admits.** -/
theorem admitted_of_enter {Ok : Atom → Prop} {σ : Substitution} :
    ∀ {qs : List Pos} {as : List Atom} {vs : List TValue},
      List.Forall₂ EnterPos qs vs → TArgsFaithful Γ grounded σ as vs →
      TAdmitted Γ grounded Ok qs (as.map (substA σ))
  | _, _, _, .nil, .nil => .nil
  | p :: _, _, _, .cons here rest, .cons faithful faithfuls => by
      refine .cons ?_ (admitted_of_enter rest faithfuls)
      cases p with
      | any => trivial
      | space => exact (here : False).elim
      | ground A =>
          obtain ⟨ground, typed⟩ := here
          exact ⟨(faithful.1.2 ground).1, faithful.2 ground A typed⟩
      | pair =>
          obtain ⟨ground, unint⟩ := here
          obtain ⟨isGround, clean⟩ := faithful.1.2 ground
          exact ⟨isGround, clean unint⟩

theorem pairAt_map {α β : Type} (f : α → β) :
    ∀ (ps : List Pos) (as : List α), pairAt ps (as.map f) = (pairAt ps as).map f
  | .pair :: _, _ :: _ => rfl
  | .any :: ps, _ :: as => pairAt_map f ps as
  | .space :: ps, _ :: as => pairAt_map f ps as
  | .ground _ :: ps, _ :: as => pairAt_map f ps as
  | [], _ => rfl
  | p :: _, [] => by cases p <;> rfl

theorem pairAt_forall₂ {α β : Type} {R : α → β → Prop} :
    ∀ {ps : List Pos} {as : List α} {bs : List β}, List.Forall₂ R as bs →
      ∀ {a : α}, pairAt ps as = some a → ∃ b, pairAt ps bs = some b ∧ R a b
  | .pair :: _, _ :: _, _ :: _, .cons head _, _, found => by
      simp only [pairAt, Option.some.injEq] at found
      subst found
      exact ⟨_, rfl, head⟩
  | .any :: _, _ :: _, _ :: _, .cons _ rest, _, found => pairAt_forall₂ rest found
  | .space :: _, _ :: _, _ :: _, .cons _ rest, _, found => pairAt_forall₂ rest found
  | .ground _ :: _, _ :: _, _ :: _, .cons _ rest, _, found => pairAt_forall₂ rest found
  | [], _, _, _, _, found => by simp [pairAt] at found
  | _ :: _, [], [], .nil, _, found => by simp [pairAt] at found

/-- **A version's answer carries the claims its call makes.** -/
theorem callee_faithful {σ : Substitution} {qs : List Pos} {res : Result} {as : List Atom}
    {vs : List TValue} {r : Atom} (faithful : TArgsFaithful Γ grounded σ as vs)
    (answers : Answers Γ grounded res qs (as.map (substA σ)) r) :
    TFaithful Γ grounded (r, σ) (calleeValue qs res vs) := by
  unfold calleeValue
  rw [if_neg (by simp [faithful.anyBottom_false])]
  cases res with
  | closed R =>
      obtain ⟨isGround, holds⟩ := answers
      refine ⟨⟨rfl, fun _ => ⟨?_, fun u => by cases u⟩⟩, fun _ T typed => ?_⟩
      · change support (substA σ r) = ∅
        rw [subst_ground isGround]
        exact isGround
      · cases typed
        change Holds Γ grounded (substA σ r) _
        rw [subst_ground isGround]
        exact holds
  | pair =>
      refine ⟨⟨rfl, fun ground => ?_⟩, fun _ T typed => by cases typed⟩
      change pairAt qs (as.map (substA σ)) = some r at answers
      rw [pairAt_map] at answers
      obtain ⟨a, found, rfl⟩ := Option.map_eq_some_iff.mp answers
      obtain ⟨v, vFound, fa⟩ := pairAt_forall₂ faithful found
      have flagsEq : pairFlags qs vs = v.flags.toFlags := by
        unfold pairFlags
        rw [vFound]
      change (pairFlags qs vs).ground = true at ground
      rw [flagsEq] at ground
      obtain ⟨isGround, clean⟩ := fa.1.2 ground
      change support (substA σ (substA σ a)) = ∅ ∧
        ((pairFlags qs vs).uninterpreted = true → Uninterp Γ (substA σ (substA σ a)))
      rw [flagsEq, subst_ground isGround]
      exact ⟨isGround, clean⟩
  | free => exact ⟨⟨rfl, fun ground => by cases ground⟩, fun ground => by cases ground⟩

end Elementary

/-! ## Soundness of the analysis -/

section Runs

variable {Γ : Decls} {grounded : String → Bool} {Ok : Atom → Prop} {P : TProgram}
  {Φ : String → Ty Empty → Prop} {Sp : String → Prop} {E E' : Env} {O O' : Oracle}

mutual
/-- **The typed analysis is sound, and a run reads its calls only where the
versions admit them and its spaces only where the entry admits them**: every
outcome keeps the ground facts and the value's claims, types included, and two
runs that agree there have the same outcomes. -/
theorem tadmits_run (hΓ : Functional Γ) (ok : TOraclesOK Γ grounded Ok P E O)
    (agree : TAgree Γ grounded Ok P E E' O O') :
    ∀ {F F' : Facts} {e : Expr} {v : TValue}, TAdmits Γ grounded P Φ Sp F e v F' →
      ∀ σ, GroundSound Γ σ F → TypeSound Γ grounded Φ σ → SpaceSound Ok Sp σ →
        eval E O e σ = eval E' O' e σ ∧
          ∀ out ∈ eval E O e σ, GroundSound Γ out.2 F' ∧ TFaithful Γ grounded out v
  | _, _, _, _, .var F x t typed, σ, sound, types, _ => by
      refine ⟨rfl, fun out member => ?_⟩
      simp only [eval, Multiset.mem_singleton] at member
      subst member
      refine ⟨sound, ?_, fun _ U hU => (types x U (typed U hU)).2⟩
      unfold varValue
      cases found : F.lookup x with
      | none => exact ⟨rfl, fun ground => by cases ground⟩
      | some flags => exact ⟨rfl, fun ground => sound x flags found ground⟩
  | _, _, _, _, .const F a t typed, σ, sound, _, _ => by
      refine ⟨rfl, fun out member => ?_⟩
      simp only [eval, Multiset.mem_singleton] at member
      subst member
      refine ⟨sound, const_faithful sound a, fun _ T hT => ?_⟩
      obtain ⟨isGround, holds⟩ := typed T hT
      change Holds Γ grounded (substA σ a) T
      rw [subst_ground isGround]
      exact holds
  | _, _, _, _, .ctor (c := c) (vs := vs) all typedCtor, σ, sound, types, spaces => by
      obtain ⟨same, each⟩ := tadmitsAll_run hΓ ok agree all σ sound types spaces
      refine ⟨by simp only [eval, same], fun out member => ?_⟩
      simp only [eval, Multiset.mem_map] at member
      obtain ⟨values, present, rfl⟩ := member
      obtain ⟨after, faithful⟩ := each values present
      refine ⟨after, data_faithful c faithful.flags, fun ground T hT => ?_⟩
      have grounds : ∀ w ∈ vs, w.flags.ground = true := by
        unfold dataValue at ground
        rw [if_neg (by simp [faithful.flags.anyBottom_false])] at ground
        intro w member
        exact List.all_eq_true.mp ground w.flags (List.mem_map_of_mem member)
      exact ctor_typed_holds hΓ faithful grounds (typedCtor T hT)
  | _, _, _, _, .self (args := args) (vs := vs) all meets, σ, sound, types, spaces => by
      obtain ⟨same, each⟩ := tadmitsAll_run hΓ ok agree all σ sound types spaces
      have admitted : ∀ out ∈ evalAll E O args σ,
          TAdmitted Γ grounded Ok P.positions (out.1.map (substA out.2)) ∧
            TArgsFaithful Γ grounded out.2 out.1 vs := by
        intro out member
        obtain ⟨_, faithful⟩ := each out member
        rcases meets with bottom | checked
        · rw [faithful.anyBottom_false] at bottom
          cases bottom
        · exact ⟨admitted_of_selfMeets (spaces.keep (evalAll_keeps E O args σ out member)) checked
            faithful (evalAll_recipes E O args σ out member), faithful⟩
      refine ⟨?_, fun out member => ?_⟩
      · simp only [eval]
        rw [← same]
        refine Multiset.bind_congr fun out member => ?_
        rw [agree.self _ (admitted out member).1]
      · simp only [eval, Multiset.mem_bind, Multiset.mem_map] at member
        obtain ⟨values, present, r, answer, rfl⟩ := member
        obtain ⟨after, faithful⟩ := each values present
        exact ⟨after, callee_faithful faithful (ok.self _ (admitted values present).1 r answer)⟩
  | _, _, _, _, .prim (op := op) (args := args) (vs := vs) (c := c) all known, σ, sound, types,
      spaces => by
      obtain ⟨same, each⟩ := tadmitsAll_run hΓ ok agree all σ sound types spaces
      refine ⟨by simp only [eval, same, agree.prim], fun out member => ?_⟩
      simp only [eval, Multiset.mem_bind, Multiset.mem_map] at member
      obtain ⟨values, present, r, answer, rfl⟩ := member
      obtain ⟨after, faithful⟩ := each values present
      have len : (values.1.map (substA values.2)).length = args.length := by
        rw [List.length_map, evalAll_length E O args σ values present]
      have literal := ok.prim op _ c (len ▸ known) r answer
      have isGround := literal_ground literal
      refine ⟨after, ?_, fun _ T hT => ?_⟩
      · unfold primValue
        rw [if_neg (by simp [faithful.flags.anyBottom_false])]
        refine ⟨rfl, fun _ => ⟨?_, fun u => by cases u⟩⟩
        change support (substA values.2 r) = ∅
        rw [subst_ground isGround]
        exact isGround
      · obtain rfl := Option.some.inj hT
        change Holds Γ grounded (substA values.2 r) (.sym c)
        rw [subst_ground isGround]
        exact holds_literal literal
  | _, _, _, _, .call (vs := vs) t all, σ, sound, types, spaces => by
      obtain ⟨same, each⟩ := tadmitsAll_run hΓ ok agree all σ sound types spaces
      refine ⟨by simp only [eval, same, agree.kept], fun out member => ?_⟩
      simp only [eval, Multiset.mem_bind, Multiset.mem_map] at member
      obtain ⟨values, present, r, _, rfl⟩ := member
      obtain ⟨after, faithful⟩ := each values present
      have notGround : (keptValue (vs.map (·.flags))).ground = false := by
        unfold keptValue
        split <;> rfl
      refine ⟨after, ?_, fun ground => by rw [notGround] at ground; cases ground⟩
      unfold keptValue
      rw [if_neg (by simp [faithful.flags.anyBottom_false])]
      exact ⟨rfl, fun ground => by cases ground⟩
  | _, _, _, _, .enter (f := f) (args := args) (vs := vs) (qs := qs) (res := res) all offered meets,
      σ, sound, types, spaces => by
      obtain ⟨same, each⟩ := tadmitsAll_run hΓ ok agree all σ sound types spaces
      have admitted : ∀ out ∈ evalAll E O args σ,
          TAdmitted Γ grounded Ok qs (out.1.map (substA out.2)) ∧
            TArgsFaithful Γ grounded out.2 out.1 vs := by
        intro out member
        obtain ⟨_, faithful⟩ := each out member
        rcases meets with bottom | checked
        · rw [faithful.anyBottom_false] at bottom
          cases bottom
        · exact ⟨admitted_of_enter checked faithful, faithful⟩
      refine ⟨?_, fun out member => ?_⟩
      · simp only [eval]
        rw [← same]
        refine Multiset.bind_congr fun out member => ?_
        rw [agree.enter f qs res offered _ (admitted out member).1]
      · simp only [eval, Multiset.mem_bind, Multiset.mem_map] at member
        obtain ⟨values, present, r, answer, rfl⟩ := member
        obtain ⟨after, faithful⟩ := each values present
        exact ⟨after, callee_faithful faithful
          (ok.enter f qs res offered _ (admitted values present).1 r answer)⟩
  | _, _, _, _, .letBottom value bottom, σ, sound, types, spaces => by
      obtain ⟨same, each⟩ := tadmits_run hΓ ok agree value σ sound types spaces
      have empty : eval E O _ σ = 0 := no_outcomes fun out member => by
        have := (each out member).2.1.1
        rw [bottom] at this
        cases this
      refine ⟨?_, fun out member => ?_⟩
      · simp only [eval]
        rw [← same, empty, Multiset.zero_bind, Multiset.zero_bind]
      · simp only [eval, empty, Multiset.zero_bind] at member
        exact absurd member (Multiset.notMem_zero out)
  | _, _, _, _, .letE (p := p) value _ bind body, σ, sound, types, spaces => by
      obtain ⟨same, each⟩ := tadmits_run hΓ ok agree value σ sound types spaces
      refine ⟨?_, fun out member => ?_⟩
      · simp only [eval]
        rw [← same]
        refine Multiset.bind_congr fun first member => ?_
        obtain ⟨after, faithful⟩ := each first member
        have keepsFirst := eval_keeps E O _ σ first member
        cases bound : bindPattern first.2 p first.1 with
        | none => rfl
        | some τ =>
            have keeps := keepsFirst.trans (KeepsGround.bind bound)
            exact (tadmits_run hΓ ok agree body τ (bindAny_sound bind after faithful.1 bound)
              (types.keep keeps) (spaces.keep keeps)).1
      · simp only [eval, Multiset.mem_bind] at member
        obtain ⟨first, present, member⟩ := member
        obtain ⟨after, faithful⟩ := each first present
        have keepsFirst := eval_keeps E O _ σ first present
        cases bound : bindPattern first.2 p first.1 with
        | none => simp [bound] at member
        | some τ =>
            rw [bound] at member
            have keeps := keepsFirst.trans (KeepsGround.bind bound)
            exact (tadmits_run hΓ ok agree body τ (bindAny_sound bind after faithful.1 bound)
              (types.keep keeps) (spaces.keep keeps)).2 out member
  | _, _, _, _, .ifE (t := t) (e := e) condition yes no, σ, sound, types, spaces => by
      obtain ⟨same, each⟩ := tadmits_run hΓ ok agree condition σ sound types spaces
      refine ⟨?_, fun out member => ?_⟩
      · simp only [eval]
        rw [← same]
        refine Multiset.bind_congr fun first member => ?_
        obtain ⟨after, _⟩ := each first member
        have keeps := eval_keeps E O _ σ first member
        rw [(tadmits_run hΓ ok agree yes first.2 after (types.keep keeps) (spaces.keep keeps)).1,
          (tadmits_run hΓ ok agree no first.2 after (types.keep keeps) (spaces.keep keeps)).1]
      · simp only [eval, Multiset.mem_bind] at member
        obtain ⟨first, present, member⟩ := member
        obtain ⟨after, _⟩ := each first present
        have keeps := eval_keeps E O _ σ first present
        split at member
        · exact ⟨after.keep (eval_keeps E O t first.2 out member), tfaithful_tjoin_left _
            ((tadmits_run hΓ ok agree yes first.2 after (types.keep keeps)
              (spaces.keep keeps)).2 out member).2⟩
        · exact ⟨after.keep (eval_keeps E O e first.2 out member), tfaithful_tjoin_right _
            ((tadmits_run hΓ ok agree no first.2 after (types.keep keeps)
              (spaces.keep keeps)).2 out member).2⟩
  | _, _, _, _, .empty F, σ, sound, _, _ => ⟨rfl, fun out member => by simp [eval] at member⟩
  | _, _, _, _, .caseBottom key bottom, σ, sound, types, spaces => by
      obtain ⟨same, each⟩ := tadmits_run hΓ ok agree key σ sound types spaces
      have empty : eval E O _ σ = 0 := no_outcomes fun out member => by
        have := (each out member).2.1.1
        rw [bottom] at this
        cases this
      refine ⟨?_, fun out member => ?_⟩
      · simp only [eval]
        rw [← same, empty, Multiset.zero_bind, Multiset.zero_bind]
      · simp only [eval, empty, Multiset.zero_bind] at member
        exact absurd member (Multiset.notMem_zero out)
  | _, _, _, _, .caseE (ps := ps) (bs := bs) key _ arms, σ, sound, types, spaces => by
      obtain ⟨same, each⟩ := tadmits_run hΓ ok agree key σ sound types spaces
      refine ⟨?_, fun out member => ?_⟩
      · simp only [eval]
        rw [← same]
        refine Multiset.bind_congr fun first member => ?_
        obtain ⟨after, faithful⟩ := each first member
        have keeps := eval_keeps E O _ σ first member
        exact (tadmitsArms_run hΓ ok agree arms first.2 first.1 after (types.keep keeps)
          (spaces.keep keeps) faithful).1
      · simp only [eval, Multiset.mem_bind] at member
        obtain ⟨first, present, member⟩ := member
        obtain ⟨after, faithful⟩ := each first present
        have keeps := eval_keeps E O _ σ first present
        exact ⟨after.keep (evalArms_keeps E O first.2 first.1 ps bs out member),
          (tadmitsArms_run hΓ ok agree arms first.2 first.1 after (types.keep keeps)
            (spaces.keep keeps) faithful).2 out member⟩
  | _, _, _, _, .matchVar (F := F) (x := x) (p := p) isSpace clean template, σ, sound, types,
      spaces => by
      have bindRow : ∀ row τ, bindPattern σ p row = some τ →
          GroundSound Γ τ (markPat F p ⟨false, true⟩) := fun row τ bound =>
        bindAny_sound (v := ⟨⟨false, true⟩, false⟩) (.clean rfl clean) sound
          ⟨rfl, fun ground => by cases ground⟩ bound
      have rowsSame : E.rows (σ x) = E'.rows (σ x) := agree.rows _ (spaces x isSpace).2
      refine ⟨?_, fun out member => ?_⟩
      · simp only [eval, Multiset.singleton_bind]
        change (E.rows (σ x)).bind _ = (E'.rows (σ x)).bind _
        rw [rowsSame]
        refine Multiset.bind_congr fun row _ => ?_
        cases bound : bindPattern σ p row with
        | none => rfl
        | some τ =>
            have keeps := KeepsGround.bind bound
            exact (tadmits_run hΓ ok agree template τ (bindRow row τ bound) (types.keep keeps)
              (spaces.keep keeps)).1
      · simp only [eval, Multiset.singleton_bind, Multiset.mem_bind] at member
        obtain ⟨row, _, member⟩ := member
        cases bound : bindPattern σ p row with
        | none => simp [bound] at member
        | some τ =>
            rw [bound] at member
            have keeps := KeepsGround.bind bound
            exact (tadmits_run hΓ ok agree template τ (bindRow row τ bound) (types.keep keeps)
              (spaces.keep keeps)).2 out member
  | _, _, _, _, .matchNamed (F := F) (s := s) (p := p) named clean template, σ, sound, types,
      spaces => by
      have bindRow : ∀ row τ, bindPattern σ p row = some τ →
          GroundSound Γ τ (markPat F p ⟨false, true⟩) := fun row τ bound =>
        bindAny_sound (v := ⟨⟨false, true⟩, false⟩) (.clean rfl clean) sound
          ⟨rfl, fun ground => by cases ground⟩ bound
      have rowsSame : E.rows (.symbol s) = E'.rows (.symbol s) :=
        agree.rows _ (agree.named s named)
      refine ⟨?_, fun out member => ?_⟩
      · simp only [eval, Multiset.singleton_bind]
        change (E.rows (.symbol s)).bind _ = (E'.rows (.symbol s)).bind _
        rw [rowsSame]
        refine Multiset.bind_congr fun row _ => ?_
        cases bound : bindPattern σ p row with
        | none => rfl
        | some τ =>
            have keeps := KeepsGround.bind bound
            exact (tadmits_run hΓ ok agree template τ (bindRow row τ bound) (types.keep keeps)
              (spaces.keep keeps)).1
      · simp only [eval, Multiset.singleton_bind, Multiset.mem_bind] at member
        obtain ⟨row, _, member⟩ := member
        cases bound : bindPattern σ p row with
        | none => simp [bound] at member
        | some τ =>
            rw [bound] at member
            have keeps := KeepsGround.bind bound
            exact (tadmits_run hΓ ok agree template τ (bindRow row τ bound) (types.keep keeps)
              (spaces.keep keeps)).2 out member

theorem tadmitsAll_run (hΓ : Functional Γ) (ok : TOraclesOK Γ grounded Ok P E O)
    (agree : TAgree Γ grounded Ok P E E' O O') :
    ∀ {F F' : Facts} {es : List Expr} {vs : List TValue},
      TAdmitsAll Γ grounded P Φ Sp F es vs F' →
      ∀ σ, GroundSound Γ σ F → TypeSound Γ grounded Φ σ → SpaceSound Ok Sp σ →
        evalAll E O es σ = evalAll E' O' es σ ∧
          ∀ out ∈ evalAll E O es σ, GroundSound Γ out.2 F' ∧ TArgsFaithful Γ grounded out.2 out.1 vs
  | _, _, _, _, .nil F, σ, sound, _, _ => by
      refine ⟨rfl, fun out member => ?_⟩
      simp only [evalAll, Multiset.mem_singleton] at member
      subst member
      exact ⟨sound, .nil⟩
  | _, _, _, _, .cons (es := es) first rest, σ, sound, types, spaces => by
      obtain ⟨same, each⟩ := tadmits_run hΓ ok agree first σ sound types spaces
      refine ⟨?_, fun out member => ?_⟩
      · simp only [evalAll]
        rw [← same]
        refine Multiset.bind_congr fun head member => ?_
        have keeps := eval_keeps E O _ σ head member
        rw [(tadmitsAll_run hΓ ok agree rest head.2 (each head member).1 (types.keep keeps)
          (spaces.keep keeps)).1]
      · simp only [evalAll, Multiset.mem_bind, Multiset.mem_map] at member
        obtain ⟨head, present, tail, tailPresent, rfl⟩ := member
        obtain ⟨after, faithful⟩ := each head present
        have keeps := eval_keeps E O _ σ head present
        obtain ⟨final, faithfuls⟩ := (tadmitsAll_run hΓ ok agree rest head.2 after
          (types.keep keeps) (spaces.keep keeps)).2 tail tailPresent
        exact ⟨final, .cons (faithful.keep (evalAll_keeps E O es head.2 tail tailPresent)) faithfuls⟩

theorem tadmitsArms_run (hΓ : Functional Γ) (ok : TOraclesOK Γ grounded Ok P E O)
    (agree : TAgree Γ grounded Ok P E E' O O') :
    ∀ {F : Facts} {kv : TValue} {ps : List Pat} {bs : List Expr} {v : TValue},
      TAdmitsArms Γ grounded P Φ Sp F kv ps bs v →
      ∀ σ key, GroundSound Γ σ F → TypeSound Γ grounded Φ σ → SpaceSound Ok Sp σ →
        TFaithful Γ grounded (key, σ) kv →
          evalArms E O σ key ps bs = evalArms E' O' σ key ps bs ∧
            ∀ out ∈ evalArms E O σ key ps bs, TFaithful Γ grounded out v
  | _, _, _, _, _, .nil F kv, σ, key, _, _, _, _ =>
      ⟨rfl, fun out member => by simp [evalArms] at member⟩
  | _, _, _, _, _, .cons (p := p) bind body rest, σ, key, sound, types, spaces, keyFaithful => by
      obtain ⟨restSame, restEach⟩ :=
        tadmitsArms_run hΓ ok agree rest σ key sound types spaces keyFaithful
      cases bound : bindPattern σ p key with
      | none =>
          simp only [evalArms, bound]
          exact ⟨restSame, fun out member => tfaithful_tjoin_right _ (restEach out member)⟩
      | some τ =>
          simp only [evalArms, bound]
          have keeps := KeepsGround.bind bound
          obtain ⟨same, each⟩ := tadmits_run hΓ ok agree body τ
            (bindAny_sound bind sound keyFaithful.1 bound) (types.keep keeps) (spaces.keep keeps)
          exact ⟨same, fun out member => tfaithful_tjoin_left _ (each out member).2⟩
end

end Runs

/-! ## Entry: head unification at admitted arguments -/

/-- The flags `contract_equation` marks a parameter's pattern with. -/
def Pos.entryFlags : Pos → Flags
  | .ground _ => ⟨true, false⟩
  | .pair => ⟨true, true⟩
  | _ => ⟨false, false⟩

/-- `contract_equation`'s entry marks, position by position. -/
def tEntryFacts : List Pos → List Pat → Facts → Facts
  | p :: ps, q :: pats, F => tEntryFacts ps pats (markPat F q p.entryFlags)
  | _, _, F => F

/-- The type facts `contract_invert` reads from the patterns at GROUND and
INSTANCE positions. -/
def eqTypes (Γ : Decls) (ps : List Pos) (pats : List Pat) (x : String) (U : Ty Empty) : Prop :=
  ∃ A q, (Pos.ground A, q) ∈ List.zip ps pats ∧ PatFact Γ q A x U

/-- The variables of the space positions (`fact->space`). -/
def eqSpaces (ps : List Pos) (pats : List Pat) (x : String) : Prop :=
  (Pos.space, Pat.var x) ∈ List.zip ps pats

/-- Every claim of an uninterpreted value is a claim of a ground one: the shape
of the entry marks, which `markPat` keeps. -/
def UninterpGround (F : Facts) : Prop :=
  ∀ x flags, F.lookup x = some flags → Flags.uninterpreted flags = true → Flags.ground flags = true

theorem uninterpGround_nil : UninterpGround [] := fun _ _ found => by simp at found

theorem UninterpGround.mark {F : Facts} {q : Pat} {fl : Flags} (clean : UninterpGround F)
    (flClean : fl.uninterpreted = true → fl.ground = true) : UninterpGround (markPat F q fl) := by
  intro y flags found u
  rw [lookup_markPat] at found
  split at found
  · cases oldFound : F.lookup y with
    | none =>
        simp only [oldFound, mergeInto, Option.some.injEq] at found
        subst found
        exact flClean u
    | some o =>
        simp only [oldFound, mergeInto, Option.some.injEq] at found
        subst found
        simp only [mergeFlags, Bool.or_eq_true] at u ⊢
        rcases u with u | u
        · exact Or.inl (clean y o oldFound u)
        · exact Or.inr (flClean u)
  · exact clean y flags found u

theorem Pos.entryFlags_clean (p : Pos) :
    p.entryFlags.uninterpreted = true → p.entryFlags.ground = true := by
  cases p <;> simp [Pos.entryFlags]

theorem bindPattern_extends {σ τ : Substitution} {q : Pat} {v : Atom}
    (bound : bindPattern σ q v = some τ) :
    ∃ δ : Substitution, ∀ a, substA τ a = substA δ (substA σ a) := by
  unfold bindPattern at bound
  cases h : UnifyAtoms.unify (substA σ q.toAtom) (substA σ v) with
  | none => simp [h] at bound
  | some θ =>
      have state : compose (UnifyAtoms.readBack θ) σ = τ := by simpa [h] using bound
      subst state
      exact ⟨UnifyAtoms.readBack θ, fun a => (substA_compose _ σ a).symm⟩

theorem binds_extends :
    ∀ {σ τ : Substitution} {pats : List Pat} {args : List Atom}, binds σ pats args = some τ →
      ∃ δ : Substitution, ∀ a, substA τ a = substA δ (substA σ a)
  | σ, τ, _ :: _, _ :: _, bound => by
      simp only [binds, Option.bind_eq_some_iff] at bound
      obtain ⟨τ₁, first, later⟩ := bound
      obtain ⟨δ₁, h₁⟩ := bindPattern_extends first
      obtain ⟨δ₂, h₂⟩ := binds_extends later
      exact ⟨compose δ₂ δ₁, fun b => by rw [h₂, h₁, substA_compose]⟩
  | σ, τ, [], _, bound => by
      simp only [binds, Option.some.injEq] at bound
      subst bound
      exact ⟨Atom.var, fun a => (substA_var_self _).symm⟩
  | σ, τ, _ :: _, [], bound => by
      simp only [binds, Option.some.injEq] at bound
      subst bound
      exact ⟨Atom.var, fun a => (substA_var_self _).symm⟩

/-- **Head unification leaves every pattern its argument's instance.** -/
theorem binds_equations :
    ∀ {σ τ : Substitution} {pats : List Pat} {args : List Atom}, pats.length = args.length →
      binds σ pats args = some τ →
        List.Forall₂ (fun q a => substA τ q.toAtom = substA τ a) pats args
  | σ, τ, _ :: _, _ :: _, len, bound => by
      simp only [binds, Option.bind_eq_some_iff] at bound
      obtain ⟨τ₁, first, later⟩ := bound
      obtain ⟨δ, hδ⟩ := binds_extends later
      refine .cons ?_ (binds_equations (by simpa using len) later)
      rw [hδ, hδ, bindPattern_equation first]
  | _, _, [], [], _, _ => .nil
  | _, _, [], _ :: _, len, _ => by simp at len
  | _, _, _ :: _, [], len, _ => by simp at len

theorem var_ground_of_subst {τ : Substitution} {a : Atom} (ground : support (substA τ a) = ∅)
    {x : String} (occurs : x ∈ support a) : support (τ x) = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro y present
  have escaped := (support_subst τ a y).mpr ⟨x, occurs, present⟩
  rw [ground] at escaped
  exact Finset.notMem_empty y escaped

mutual
theorem mem_support_of_vars : ∀ (q : Pat) (x : String), x ∈ Pat.vars q → x ∈ support q.toAtom
  | .var y, x, h => by
      simp only [Pat.vars, List.mem_singleton] at h
      subst h
      simp [Pat.toAtom, support, UnifyAtoms.encode, Mettapedia.Logic.LP.Term.freeVars]
  | .const _, x, h => by simp [Pat.vars] at h
  | .ctor _ qs, x, h => by
      rw [Pat.toAtom, support_expression]
      obtain ⟨a, member, occurs⟩ := mem_support_of_varsAll qs x (by simpa [Pat.vars] using h)
      exact ⟨a, List.mem_cons_of_mem _ member, occurs⟩

theorem mem_support_of_varsAll :
    ∀ (qs : List Pat) (x : String), x ∈ Pat.varsAll qs → ∃ a ∈ Pat.toAtoms qs, x ∈ support a
  | [], x, h => by simp [Pat.varsAll] at h
  | q :: qs, x, h => by
      rw [Pat.varsAll, List.mem_append] at h
      rcases h with h | h
      · exact ⟨q.toAtom, by simp [Pat.toAtoms], mem_support_of_vars q x h⟩
      · obtain ⟨a, member, occurs⟩ := mem_support_of_varsAll qs x h
        exact ⟨a, by simp [Pat.toAtoms, member], occurs⟩
end

theorem toAtoms_eq_map : ∀ qs : List Pat, Pat.toAtoms qs = qs.map Pat.toAtom
  | [] => rfl
  | q :: qs => by rw [Pat.toAtoms, toAtoms_eq_map qs]; rfl

section Entry

variable {Γ : Decls} {grounded : String → Bool} {Ok : Atom → Prop}

/-- **A type fact read from a pattern holds of the variable after two-way
unification**: whichever argument the pattern was unified with, typed once at the
formal, every variable holds its fact (`contract_invert`, with logic variables). -/
theorem patFact_subst (hΓ : Functional Γ) {q : Pat} {T : Ty Empty} {x : String} {U : Ty Empty}
    (h : PatFact Γ q T x U) :
    ∀ {τ : Substitution}, Holds Γ grounded (substA τ q.toAtom) T → Holds Γ grounded (τ x) U := by
  induction h with
  | var x T => intro τ holds; exact holds
  | @ctor c Bs R ps T σ x U B p row cls len notMeta named hmatch field fixed inner ih =>
      intro τ holds
      have shape : substA τ (Pat.ctor c ps).toAtom =
          .expression (.symbol c :: ps.map fun q => substA τ q.toAtom) := by
        rw [Pat.toAtom, substA, UnifyAtoms.substL_eq_map, List.map_cons, toAtoms_eq_map, List.map_map]
        rfl
      rw [shape] at holds
      have lenVs : (ps.map fun q => substA τ q.toAtom).length = Bs.length := by
        rw [List.length_map, len]
      obtain ⟨σ', hσ', fields⟩ := ctor_inversion hΓ row _ lenVs T named (holds.count notMeta)
      have member : (B, substA τ p.toAtom) ∈ List.zip Bs (ps.map fun q => substA τ q.toAtom) := by
        rw [List.zip_map_right]
        exact List.mem_map.mpr ⟨(B, p), field, rfl⟩
      have typed := fields _ member (checked_of_not_free fixed)
      have fixedB : ∀ y ∈ B.vars, y ∈ R.vars := by
        rcases cls.fields B (List.of_mem_zip field).1 with free | fixedB
        · exact absurd free fixed
        · exact fixedB
      have same : B.bind σ' = B.bind σ := fixed_instance_unique fixedB (hσ'.trans hmatch.symm)
      rw [same] at typed
      exact ih (Holds.of_count typed)

theorem forall₂_zip_mem {α β γ : Type} {R : α → γ → Prop} {S : β → γ → Prop} :
    ∀ {xs : List α} {ys : List β} {zs : List γ}, List.Forall₂ R xs zs → List.Forall₂ S ys zs →
      ∀ {x : α} {y : β}, (x, y) ∈ List.zip xs ys → ∃ z, R x z ∧ S y z
  | _, _, _, .cons hr rr, .cons hs rs, _, _, member => by
      rcases List.mem_cons.mp member with same | later
      · simp only [Prod.mk.injEq] at same
        obtain ⟨rfl, rfl⟩ := same
        exact ⟨_, hr, hs⟩
      · exact forall₂_zip_mem rr rs later
  | _, _, _, .nil, .nil, _, _, member => by simp at member

/-- One position's entry mark keeps the ground facts at the admitted argument. -/
theorem markEntry_sound {F : Facts} {q : Pat} {σ τ : Substitution} {a : Atom} (p : Pos)
    (sound : GroundSound Γ σ F) (clean : UninterpGround F) (bound : bindPattern σ q a = some τ)
    (admitted : PosAdmits Γ grounded Ok p a) : GroundSound Γ τ (markPat F q p.entryFlags) := by
  cases p with
  | any => exact markNothing_sound sound bound
  | space => exact markNothing_sound sound bound
  | pair => exact markActive_sound sound bound admitted.1 admitted.2
  | ground A =>
      have keeps := KeepsGround.bind bound
      have old := sound.keep keeps
      intro y flags found ground
      rw [lookup_markPat] at found
      split at found
      · next occurs =>
          refine ⟨ground_pattern_marks bound (by rw [subst_ground admitted.1]; exact admitted.1) y
            occurs, fun u => ?_⟩
          cases oldFound : F.lookup y with
          | none =>
              simp only [oldFound, mergeInto, Option.some.injEq] at found
              subst found
              cases u
          | some o =>
              simp only [oldFound, mergeInto, Option.some.injEq] at found
              subst found
              have ou : o.uninterpreted = true := by simpa [mergeFlags, Pos.entryFlags] using u
              exact (old y o oldFound (clean y o oldFound ou)).2 ou
      · exact old y flags found ground

/-- **The entry marks hold after head unification of admitted arguments.** -/
theorem tentry_ground :
    ∀ {ps : List Pos} {args : List Atom} (pats : List Pat) (F : Facts) (σ τ : Substitution),
      TAdmitted Γ grounded Ok ps args → GroundSound Γ σ F → UninterpGround F →
        binds σ pats args = some τ → GroundSound Γ τ (tEntryFacts ps pats F)
  | [], [], pats, F, σ, τ, .nil, sound, _, bound => by
      have same : τ = σ := by
        cases pats <;> simp only [binds, Option.some.injEq] at bound <;> exact bound.symm
      subst same
      cases pats <;> exact sound
  | p :: ps, a :: as, [], F, σ, τ, .cons _ _, sound, _, bound => by
      simp only [binds, Option.some.injEq] at bound
      subst bound
      exact sound
  | p :: ps, a :: as, q :: pats, F, σ, τ, .cons here rest, sound, clean, bound => by
      simp only [binds, Option.bind_eq_some_iff] at bound
      obtain ⟨τ₁, first, later⟩ := bound
      exact tentry_ground pats _ τ₁ τ rest (markEntry_sound p sound clean first here)
        (clean.mark p.entryFlags_clean) later

/-- **The type facts hold after head unification** of admitted arguments. -/
theorem entry_types (hΓ : Functional Γ) {ps : List Pos} {pats : List Pat} {args : List Atom}
    {σ τ : Substitution} (admitted : TAdmitted Γ grounded Ok ps args)
    (len : pats.length = args.length) (bound : binds σ pats args = some τ) :
    TypeSound Γ grounded (eqTypes Γ ps pats) τ := by
  rintro x U ⟨A, q, member, fact⟩
  obtain ⟨a, adm, eqn⟩ := forall₂_zip_mem admitted (binds_equations len bound) member
  obtain ⟨aGround, holds⟩ := adm
  rw [subst_ground aGround] at eqn
  rw [← eqn] at aGround holds
  exact ⟨var_ground_of_subst aGround (mem_support_of_vars q x fact.mem_vars),
    patFact_subst hΓ fact holds⟩

/-- **The space variables hold the admitted spaces** after head unification. -/
theorem entry_spaces {ps : List Pos} {pats : List Pat} {args : List Atom} {σ τ : Substitution}
    (admitted : TAdmitted Γ grounded Ok ps args) (len : pats.length = args.length)
    (bound : binds σ pats args = some τ) : SpaceSound Ok (eqSpaces ps pats) τ := by
  intro x member
  obtain ⟨a, adm, eqn⟩ := forall₂_zip_mem admitted (binds_equations len bound) member
  obtain ⟨aGround, admittedSpace⟩ := adm
  rw [subst_ground aGround] at eqn
  change τ x = a at eqn
  rw [eqn]
  exact ⟨aGround, admittedSpace⟩

theorem pairAt_admitted :
    ∀ {ps : List Pos} {args : List Atom}, TAdmitted Γ grounded Ok ps args →
      ∀ {a : Atom}, pairAt ps args = some a → support a = ∅ ∧ Uninterp Γ a
  | .pair :: _, _ :: _, .cons here _, _, found => by
      simp only [pairAt, Option.some.injEq] at found
      subst found
      exact here
  | .any :: _, _ :: _, .cons _ rest, _, found => pairAt_admitted rest found
  | .space :: _, _ :: _, .cons _ rest, _, found => pairAt_admitted rest found
  | .ground _ :: _, _ :: _, .cons _ rest, _, found => pairAt_admitted rest found
  | [], [], .nil, _, found => by simp [pairAt] at found

/-- **The polymorphic pattern observes its argument** after head unification. -/
theorem entry_pair {ps : List Pos} {pats : List Pat} {args : List Atom} {σ τ : Substitution}
    (admitted : TAdmitted Γ grounded Ok ps args) (len : pats.length = args.length)
    (bound : binds σ pats args = some τ) {pu : Pat} (found : pairAt ps pats = some pu) :
    ∃ a, pairAt ps args = some a ∧ substA τ pu.toAtom = a ∧ support a = ∅ := by
  have equations := binds_equations len bound
  have lenPs : ps.length = pats.length := admitted.length_eq.trans len.symm
  have aligned : List.Forall₂ (fun q a => substA τ q.toAtom = substA τ a) pats args := equations
  obtain ⟨a, aFound, eqn⟩ := pairAt_forall₂ aligned found
  obtain ⟨aGround, _⟩ := pairAt_admitted admitted aFound
  rw [subst_ground aGround] at eqn
  exact ⟨a, aFound, eqn, aGround⟩

end Entry

/-! ## Accepted equations and their activations -/

/-- The result condition of `contract_equation`: no answer, or a ground value of
the closed range, or an uninterpreted value returning the polymorphic pattern. -/
def ResultOK (P : TProgram) (eq : Equation) (v : TValue) : Prop :=
  v.flags.bottom = true ∨
    match P.result with
    | .closed R => v.flags.ground = true ∧ v.type = some R
    | .pair => v.flags.uninterpreted = true ∧
        ∃ pu, pairAt P.positions eq.pats = some pu ∧ ReturnsPat (Pat.toExpr pu) eq.rhs
    | .free => True

/-- **An equation the analysis accepts** (`contract_equation`): from the entry marks,
the type facts of the patterns and the space variables, its right-hand side's value
meets the result condition. -/
def TAccepted (Γ : Decls) (grounded : String → Bool) (P : TProgram) (eq : Equation) : Prop :=
  eq.pats.length = P.positions.length ∧
    ∃ v F', TAdmits Γ grounded P (eqTypes Γ P.positions eq.pats) (eqSpaces P.positions eq.pats)
      (tEntryFacts P.positions eq.pats []) eq.rhs v F' ∧ ResultOK P eq v

section Activation

variable {Γ : Decls} {grounded : String → Bool} {Ok : Atom → Prop} {P : TProgram}
  {E E' : Env} {O O' : Oracle}

/-- **An accepted equation at admitted arguments**: two runs that agree where the
versions and the entry admit have its answers alike, and each answer is what the
version proves. -/
theorem tactivation (hΓ : Functional Γ) (ok : TOraclesOK Γ grounded Ok P E O)
    (agree : TAgree Γ grounded Ok P E E' O O') {eq : Equation} (accepted : TAccepted Γ grounded P eq)
    {args : List Atom} (admitted : TAdmitted Γ grounded Ok P.positions args) :
    activation E O eq args = activation E' O' eq args ∧
      ∀ r ∈ activation E O eq args, Answers Γ grounded P.result P.positions args r := by
  obtain ⟨plen, v, F', admits, result⟩ := accepted
  unfold activation
  split
  · next len =>
      rw [eval_headLets, eval_headLets]
      cases bound : binds Atom.var eq.pats args with
      | none => exact ⟨rfl, fun r member => by simp at member⟩
      | some τ =>
          simp only
          have entered := tentry_ground eq.pats [] Atom.var τ admitted (GroundSound.nil Γ _)
            uninterpGround_nil bound
          obtain ⟨same, each⟩ := tadmits_run hΓ ok agree admits τ entered
            (entry_types hΓ admitted len bound) (entry_spaces admitted len bound)
          refine ⟨by rw [same], fun r member => ?_⟩
          obtain ⟨out, present, rfl⟩ := Multiset.mem_map.mp member
          obtain ⟨_, faithful⟩ := each out present
          rcases result with bottom | result
          · have notBottom := faithful.1.1
            rw [bottom] at notBottom
            cases notBottom
          · revert result
            cases hres : P.result with
            | closed R =>
                rintro ⟨ground, typed⟩
                exact ⟨(faithful.1.2 ground).1, faithful.2 ground R typed⟩
            | pair =>
                rintro ⟨_, pu, found, returns⟩
                obtain ⟨a, aFound, observed, aGround⟩ := entry_pair admitted len bound found
                have recipe := returns_recipe E O returns τ out present
                have keeps := eval_keeps E O eq.rhs τ out present
                change pairAt P.positions args = some (substA out.2 out.1)
                rw [recipe, keeps.observe (by rw [observed]; exact aGround), observed]
                exact aFound
            | free => intro _; trivial
  · exact ⟨rfl, fun r member => absurd member (Multiset.notMem_zero r)⟩

end Activation

/-! ## The version is the protocol -/

section Version

variable (Γ : Decls) (grounded : String → Bool)

/-- **The protocol's row reduces to the body** at admitted arguments, when every
answer of the body is what the version proves: its argument guards pass once and
its result guard keeps each answer once. -/
def RowReduces (Ok : Atom → Prop) (P : TProgram) (row : Ty String) : Prop :=
  ∀ (b : List Atom → Multiset Atom) ws, TAdmitted Γ grounded Ok P.positions ws →
    (∀ r ∈ b ws, Answers Γ grounded P.result P.positions ws r) →
      chainCall Γ (metatype grounded) b row ws = b ws

/-- The hypotheses of the version theorem: functional declarations, every equation
accepted, the versions it enters proved (they agree with their protocols where they
admit and answer what they prove), PeTTa's operations answering their classes, and
the protocol's environment `E` and the version's `E'` agreeing on operations, kept
calls and the rows of every space the entry admits. -/
structure TVersionHyps (Ok : Atom → Prop) (P : TProgram) (E E' : Env) (eqs : List Equation)
    (enP enV : String → List Atom → Multiset Atom) : Prop where
  functional : Functional Γ
  accepted : ∀ eq ∈ eqs, TAccepted Γ grounded P eq
  enterAgree : ∀ f qs res, P.versions f = some (qs, res) → ∀ ws, TAdmitted Γ grounded Ok qs ws →
    enP f ws = enV f ws
  enterAnswers : ∀ f qs res, P.versions f = some (qs, res) → ∀ ws, TAdmitted Γ grounded Ok qs ws →
    ∀ r ∈ enV f ws, Answers Γ grounded res qs ws r
  prim : ∀ op ws c, P.prim op ws.length = some c → ∀ r ∈ E'.prim op ws, Literal c r
  primSame : E.prim = E'.prim
  keptSame : E.kept = E'.kept
  rows : ∀ w, Ok w → E.rows w = E'.rows w
  named : ∀ s ∈ P.spaces, Ok (.symbol s)

variable {Γ grounded} {Ok : Atom → Prop} {P : TProgram} {E E' : Env} {eqs : List Equation}
  {enP enV : String → List Atom → Multiset Atom}

/-- **The version answers what it proves** at every fuel. -/
theorem typed_version_answers (h : TVersionHyps Γ grounded Ok P E E' eqs enP enV) :
    ∀ n ws, TAdmitted Γ grounded Ok P.positions ws →
      ∀ r ∈ versionRun (relBody E' enV eqs) n ws, Answers Γ grounded P.result P.positions ws r
  | 0, _, _, r, member => absurd member (Multiset.notMem_zero r)
  | n + 1, ws, admitted, r, member => by
      simp only [versionRun, relBody, Multiset.mem_bind] at member
      obtain ⟨eq, eqMember, member⟩ := member
      exact (tactivation h.functional ⟨typed_version_answers h n, h.enterAnswers, h.prim⟩
        (TAgree.refl h.named) (h.accepted eq (Multiset.mem_coe.mp eqMember)) admitted).2 r member

/-- **The version is the protocol, multiplicity included**: at arguments the
version admits, the run whose calls to itself and discharged calls skip their
protocols has, at every fuel, exactly the answers of the run whose every call
runs the protocol of `row`, whenever that row reduces to the body there. -/
theorem typed_version_eq_protocol (h : TVersionHyps Γ grounded Ok P E E' eqs enP enV)
    {row : Ty String} (reduces : RowReduces Γ grounded Ok P row) :
    ∀ n ws, TAdmitted Γ grounded Ok P.positions ws →
      protocolRun Γ grounded (relBody E enP eqs) row n ws = versionRun (relBody E' enV eqs) n ws
  | 0, _, _ => rfl
  | n + 1, ws, admitted => by
      have ih := typed_version_eq_protocol h reduces n
      have okP : TOraclesOK Γ grounded Ok P E ⟨protocolRun Γ grounded (relBody E enP eqs) row n, enP⟩ :=
        ⟨fun ws' adm r member => typed_version_answers h n ws' adm r (by rw [← ih ws' adm]; exact member),
          fun f qs res offered ws' adm r member => h.enterAnswers f qs res offered ws' adm r
            (by rw [← h.enterAgree f qs res offered ws' adm]; exact member),
          fun op ws' c known r member => h.prim op ws' c known r (by rw [← h.primSame]; exact member)⟩
      have agree : TAgree Γ grounded Ok P E E' ⟨protocolRun Γ grounded (relBody E enP eqs) row n, enP⟩
          ⟨versionRun (relBody E' enV eqs) n, enV⟩ :=
        ⟨ih, h.enterAgree, h.primSame, h.keptSame, h.rows, h.named⟩
      have same : relBody E enP eqs (protocolRun Γ grounded (relBody E enP eqs) row n) ws =
          relBody E' enV eqs (versionRun (relBody E' enV eqs) n) ws := by
        unfold relBody
        refine Multiset.bind_congr fun eq eqMember => ?_
        exact (tactivation h.functional okP agree (h.accepted eq (Multiset.mem_coe.mp eqMember))
          admitted).1
      simp only [protocolRun, versionRun]
      rw [reduces _ ws admitted (fun r member => typed_version_answers h (n + 1) ws admitted r
        (by simp only [versionRun]; rw [← same]; exact member)), same]

end Version

/-! ## The protocol's rows -/

/-- A closed formal at a position: GROUND and INSTANCE at their closed, guarded
formal; ANY and space parameters at a formal the protocol does not guard. -/
def ClosedFormal : Pos → Ty Empty → Prop
  | .ground A, B => B = A ∧ demand A.lift = .guarded
  | .any, B => demand B.lift ≠ .guarded
  | .space, B => demand B.lift ≠ .guarded
  | .pair, _ => False

/-- A closed range: guarded where the version proves it, unguarded where it
proves nothing. -/
def RangeFormal : Result → Ty Empty → Prop
  | .closed R, B => B = R ∧ ResultGuarded R.lift
  | .free, B => ¬ ResultGuarded B.lift
  | .pair, _ => False

section Rows

variable {Γ : Decls} {grounded : String → Bool} {Ok : Atom → Prop}

theorem entryFacts_of_admitted :
    ∀ {ps : List Pos} {As : List (Ty Empty)} {ws : List Atom},
      List.Forall₂ ClosedFormal ps As → TAdmitted Γ grounded Ok ps ws → EntryFacts Γ grounded As ws
  | _, _, _, .nil, .nil => .nil
  | p :: _, _ :: _, _ :: _, .cons formal formals, .cons adm adms => by
      refine .cons (fun guarded => ?_) (entryFacts_of_admitted formals adms)
      cases p with
      | ground A =>
          obtain ⟨rfl, _⟩ := formal
          exact adm.2
      | any => exact absurd guarded formal
      | space => exact absurd guarded formal
      | pair => exact formal.elim

/-- **GROUND and ANY rows reduce**: the closed row's argument guards pass once at
admitted arguments, and its result guard keeps each answer the version proves. -/
theorem rowReduces_closed {P : TProgram} {As : List (Ty Empty)} {R : Ty Empty}
    (formals : List.Forall₂ ClosedFormal P.positions As) (range : RangeFormal P.result R) :
    RowReduces Γ grounded Ok P (arrow (As.map Ty.lift) R.lift) := by
  intro b ws admitted answers
  rw [chainCall_closed, argCount_of_entryFacts (entryFacts_of_admitted formals admitted), one_nsmul]
  refine (Multiset.bind_congr (g := fun r => ({r} : Multiset Atom)) fun r member => ?_).trans
    (by rw [Multiset.bind_singleton, Multiset.map_id'])
  have answer := answers r member
  revert range answer
  cases P.result with
  | closed R' =>
      rintro ⟨rfl, guarded⟩ ⟨_, holds⟩
      rw [if_pos guarded, holds.guardCount, one_nsmul]
  | free =>
      intro unguarded _
      rw [if_neg unguarded]
  | pair => intro impossible; exact impossible.elim

theorem split_admitted :
    ∀ {pre post : List Pos} {ws : List Atom}, TAdmitted Γ grounded Ok (pre ++ .pair :: post) ws →
      ∃ us v rest, ws = us ++ v :: rest ∧ TAdmitted Γ grounded Ok pre us ∧
        (support v = ∅ ∧ Uninterp Γ v) ∧ TAdmitted Γ grounded Ok post rest
  | [], _, _ :: _, .cons here rest => ⟨[], _, _, rfl, .nil, here, rest⟩
  | _ :: _, _, _ :: _, .cons here rest => by
      obtain ⟨us, v, more, rfl, pre, mid, post⟩ := split_admitted rest
      exact ⟨_ :: us, v, more, rfl, .cons here pre, mid, post⟩

theorem pairAt_shape {α : Type} :
    ∀ {pre : List Pos} {us : List α} (post : List Pos) (v : α) (rest : List α),
      (∀ p ∈ pre, p ≠ .pair) → pre.length = us.length → pairAt (pre ++ .pair :: post) (us ++ v :: rest) = some v
  | [], [], _, _, _, _, _ => rfl
  | p :: pre, _ :: us, post, v, rest, notPair, len => by
      have here : p ≠ .pair := notPair p (by simp)
      have later := pairAt_shape (pre := pre) (us := us) post v rest
        (fun q member => notPair q (List.mem_cons_of_mem _ member)) (by simpa using len)
      cases p with
      | pair => exact absurd rfl here
      | any => exact later
      | space => exact later
      | ground _ => exact later
  | [], _ :: _, _, _, _, _, len => by simp at len
  | _ :: _, [], _, _, _, _, len => by simp at len

theorem closedFormal_not_pair :
    ∀ {ps : List Pos} {As : List (Ty Empty)}, List.Forall₂ ClosedFormal ps As → ∀ p ∈ ps, p ≠ .pair
  | _, _, .nil, _, member => by cases member
  | _ :: _, _ :: _, .cons formal formals, q, member => by
      rcases List.mem_cons.mp member with rfl | later
      · rintro rfl
        exact formal
      · exact closedFormal_not_pair formals q later

/-- **Pair rows reduce** (`(-> A₁ … $t … Aₖ $t)` with closed `Aᵢ`): the guards at the
closed formals pass once at admitted arguments, and the guard pair at `$t` keeps the
polymorphic argument, which is every answer. -/
theorem rowReduces_pair {P : TProgram} {pre post : List Pos} {Apre Apost : List (Ty Empty)}
    (t : String) (shape : P.positions = pre ++ .pair :: post) (result : P.result = .pair)
    (preFormals : List.Forall₂ ClosedFormal pre Apre)
    (postFormals : List.Forall₂ ClosedFormal post Apost) :
    RowReduces Γ grounded Ok P (arrow (Apre.map Ty.lift ++ .var t :: Apost.map Ty.lift) (.var t)) := by
  intro b ws admitted answers
  rw [shape] at admitted
  obtain ⟨us, v, rest, rfl, preAdm, here, postAdm⟩ := split_admitted admitted
  have len : Apre.length = us.length := preFormals.length_eq.symm.trans preAdm.length_eq
  have isV : ∀ r ∈ b (us ++ v :: rest), r = v := by
    intro r member
    have answer := answers r member
    rw [result, shape] at answer
    change pairAt (pre ++ .pair :: post) (us ++ v :: rest) = some r at answer
    rw [pairAt_shape post v rest (closedFormal_not_pair preFormals)
      (preFormals.length_eq.trans len)] at answer
    exact (Option.some.inj answer).symm
  rw [UninterpretedLocalMultiplicity.pair_protocol_clean (metatype grounded) Apre Apost t b us rest v
      len here.2 (fun r member => ⟨Atom.var, by rw [isV r member, substA_var_self], fun _ => trivial⟩),
    argCount_of_entryFacts (entryFacts_of_admitted preFormals preAdm),
    argCount_of_entryFacts (entryFacts_of_admitted postFormals postAdm), mul_one, one_nsmul]

theorem allTyped_of_admitted {Fs : List (Ty String)} {ws : List Atom} {θ : String → Ty Empty}
    (hFs : ∀ F ∈ Fs, demand F = .guarded ∧ NoMeta F)
    (admitted : TAdmitted Γ grounded Ok (Fs.map fun F => .ground (F.bind θ)) ws) :
    AllTyped Γ Fs ws θ := by
  have each : List.Forall₂ (fun F w => Holds Γ grounded w (F.bind θ)) Fs ws :=
    (List.forall₂_map_left_iff.mp admitted).imp fun _ _ adm => adm.2
  intro p hp
  exact ((List.forall₂_iff_zip.mp each).2 hp).count ((hFs p.1 (List.of_mem_zip hp).1).2 θ)

/-- **Instance rows reduce** (`contract_instance_version`): the signature's guards,
with fresh variables at every call, allow the version's instance `θ` at arguments
typed there, and the answers of the instance's closed range meet the signature's
result guard once. -/
theorem rowReduces_instance (hΓ : Functional Γ) {P : TProgram} {Fs : List (Ty String)}
    {R : Ty String} (θ : String → Ty Empty) (positions : P.positions = Fs.map fun F => .ground (F.bind θ))
    (result : P.result = .closed (R.bind θ)) (hFs : ∀ F ∈ Fs, demand F = .guarded ∧ NoMeta F)
    (hR : ResultGuarded R) (noMetaR : NoMeta R) : RowReduces Γ grounded Ok P (arrow Fs R) := by
  intro b ws admitted answers
  rw [positions] at admitted
  have len : Fs.length = ws.length := by simpa using admitted.length_eq
  rw [chainCall_shared hΓ grounded b Fs R ws len hFs hR noMetaR]
  refine (Multiset.bind_congr (g := fun r => ({r} : Multiset Atom)) fun r member => ?_).trans
    (by rw [Multiset.bind_singleton, Multiset.map_id'])
  have answer := answers r member
  rw [result] at answer
  rw [if_pos ⟨θ, allTyped_of_admitted hFs admitted, answer.2.count (noMetaR θ)⟩]

/-- The version's own entry test (`oem_entry_facts_hold`), after the protocol's
guards: groundness at GROUND and INSTANCE, groundness and uninterpretedness at the
pair, the space test at a space parameter, nothing at ANY. -/
def RuntimeTest (Γ : Decls) (Ok : Atom → Prop) : Pos → Atom → Prop
  | .any, _ => True
  | .space, w => support w = ∅ ∧ Ok w
  | .ground _, w => support w = ∅
  | .pair, w => support w = ∅ ∧ Uninterp Γ w

/-- **A checked call that passes its guards and the entry test is admitted**: under
functional declarations the guards give the type facts, the test the rest. -/
theorem admitted_of_checked (hΓ : Functional Γ) :
    ∀ {ps : List Pos} {As : List (Ty Empty)} {ws : List Atom},
      List.Forall₂ ClosedFormal ps As → argCount Γ (metatype grounded) As ws ≠ 0 →
        List.Forall₂ (RuntimeTest Γ Ok) ps ws → TAdmitted Γ grounded Ok ps ws := by
  intro ps As ws formals passes test
  have facts := entryFacts_of_argCount hΓ passes
  clear passes
  induction formals generalizing ws with
  | nil => cases test; exact .nil
  | @cons p B ps As formal formals ih =>
      cases test with
      | @cons _ w _ ws here rest =>
          cases facts with
          | cons fact facts =>
              refine .cons ?_ (ih rest facts)
              cases p with
              | any => trivial
              | space => exact here
              | pair => exact here
              | ground A =>
                  obtain ⟨rfl, guarded⟩ := formal
                  exact ⟨here, fact guarded⟩

end Rows

/-! ## The theorems -/

section Theorems

variable {Γ : Decls} {grounded : String → Bool} {Ok : Atom → Prop} {P : TProgram} {E E' : Env}
  {eqs : List Equation} {enP enV : String → List Atom → Multiset Atom}

/-- **GROUND entry facts under logic variables**: for a relation whose row is closed
(`(-> A₁ … Aₖ R)`, GROUND parameters at their guarded formals, ANY and space
parameters at unguarded ones), at arguments that are ground and typed at the GROUND
positions, the version is the protocol at every fuel, multiplicity included,
however the body binds the other parameters. -/
theorem ground_typed_version_eq_protocol (h : TVersionHyps Γ grounded Ok P E E' eqs enP enV)
    {As : List (Ty Empty)} {R : Ty Empty} (formals : List.Forall₂ ClosedFormal P.positions As)
    (range : RangeFormal P.result R) (n : ℕ) (ws : List Atom)
    (admitted : TAdmitted Γ grounded Ok P.positions ws) :
    protocolRun Γ grounded (relBody E enP eqs) (arrow (As.map Ty.lift) R.lift) n ws =
      versionRun (relBody E' enV eqs) n ws :=
  typed_version_eq_protocol h (rowReduces_closed formals range) n ws admitted

/-- **The polymorphic pair beside GROUND parameters**: for `(-> A₁ … $t … Aₖ $t)`
with closed `Aᵢ`, the version is the protocol at every fuel, multiplicity included. -/
theorem pair_typed_version_eq_protocol (h : TVersionHyps Γ grounded Ok P E E' eqs enP enV)
    {pre post : List Pos} {Apre Apost : List (Ty Empty)} (t : String)
    (shape : P.positions = pre ++ .pair :: post) (result : P.result = .pair)
    (preFormals : List.Forall₂ ClosedFormal pre Apre) (postFormals : List.Forall₂ ClosedFormal post Apost)
    (n : ℕ) (ws : List Atom) (admitted : TAdmitted Γ grounded Ok P.positions ws) :
    protocolRun Γ grounded (relBody E enP eqs) (arrow (Apre.map Ty.lift ++ .var t :: Apost.map Ty.lift)
      (.var t)) n ws = versionRun (relBody E' enV eqs) n ws :=
  typed_version_eq_protocol h (rowReduces_pair t shape result preFormals postFormals) n ws admitted

/-- **INSTANCE entry facts under logic variables**: the version of a closed instance
`θ` of the signature `(-> F₁ … Fₖ R)`, analysed at the instance, is the signature's
own protocol at every fuel, multiplicity included, at arguments ground and typed at
the instance. -/
theorem instance_typed_version_eq_protocol (h : TVersionHyps Γ grounded Ok P E E' eqs enP enV)
    {Fs : List (Ty String)} {R : Ty String} (θ : String → Ty Empty)
    (positions : P.positions = Fs.map fun F => .ground (F.bind θ))
    (result : P.result = .closed (R.bind θ)) (hFs : ∀ F ∈ Fs, demand F = .guarded ∧ NoMeta F)
    (hR : ResultGuarded R) (noMetaR : NoMeta R) (n : ℕ) (ws : List Atom)
    (admitted : TAdmitted Γ grounded Ok P.positions ws) :
    protocolRun Γ grounded (relBody E enP eqs) (arrow Fs R) n ws = versionRun (relBody E' enV eqs) n ws :=
  typed_version_eq_protocol h
    (rowReduces_instance h.functional θ positions result hFs hR noMetaR) n ws admitted

/-- **A checked call through the version is the protocol's call** (closed rows): where
the guards pass and the entry test passes, the call entering the version answers the
protocol's answers; where the guards fail, both answer nothing. -/
theorem checked_ground_call_eq (h : TVersionHyps Γ grounded Ok P E E' eqs enP enV)
    {As : List (Ty Empty)} {R : Ty Empty} (formals : List.Forall₂ ClosedFormal P.positions As)
    (range : RangeFormal P.result R) (n : ℕ) (ws : List Atom)
    (test : List.Forall₂ (RuntimeTest Γ Ok) P.positions ws) :
    protocolRun Γ grounded (relBody E enP eqs) (arrow (As.map Ty.lift) R.lift) (n + 1) ws =
      chainCall Γ (metatype grounded) (relBody E' enV eqs (versionRun (relBody E' enV eqs) n))
        (arrow (As.map Ty.lift) R.lift) ws := by
  by_cases passes : argCount Γ (metatype grounded) As ws = 0
  · simp only [protocolRun]
    rw [chainCall_closed, chainCall_closed, passes, zero_nsmul, zero_nsmul]
  · have admitted := admitted_of_checked h.functional formals passes test
    rw [ground_typed_version_eq_protocol h formals range (n + 1) ws admitted,
      rowReduces_closed formals range (relBody E' enV eqs (versionRun (relBody E' enV eqs) n)) ws
        admitted (fun r member => typed_version_answers h (n + 1) ws admitted r member)]
    rfl

end Theorems

/-! ## Controls -/

namespace Controls

open TypedCalls.Controls (decls decls_functional sym num str app listOf listNumber cons_row
  cons_constructor env env_ok noRes noCallee listA atNumber count_nil)

/-- `Number`. -/
abbrev number : Ty Empty := .sym "Number"

theorem holds_num (grounded : String → Bool) (k : ℤ) : Holds decls grounded (num k) number :=
  Holds.of_count (count_int decls k)

theorem num_ground (k : ℤ) : support (num k) = ∅ :=
  literal_ground (show Literal "Number" (num k) from rfl)

/-! ### A countdown at a GROUND parameter -/

/-- `(= (down $n) (if (== $n 0) 0 (down (- $n 1))))` at `(: down (-> Number Number))`. -/
def downEq : Equation :=
  ⟨[.var "n"], .ifE (.prim "==" [.var "n", .const (num 0)]) (.const (num 0))
    (.self [.prim "-" [.var "n", .const (num 1)]])⟩

def downProgram : TProgram := ⟨[.ground number], .closed number, fun _ => none, primClass, []⟩

/-- **`down` is accepted**: `$n` is ground and a `Number` at entry, `(- $n 1)` is a
ground `Number`, so the call to itself meets the GROUND fact, and both branches give
a ground `Number`. -/
theorem down_accepted (grounded : String → Bool) : TAccepted decls grounded downProgram downEq := by
  refine ⟨rfl, _, _, .ifE (.prim (.cons (.var _ "n" none fun _ h => by cases h)
      (.cons (.const _ _ none fun _ h => by cases h) (.nil _))) rfl)
    (.const _ _ (some number) fun T h => ?_)
    (.self (.cons (.prim (.cons (.var _ "n" none fun _ h => by cases h)
      (.cons (.const _ _ none fun _ h => by cases h) (.nil _))) rfl) (.nil _))
      (Or.inr (.cons ⟨by decide +kernel, rfl⟩ .nil))), Or.inr ⟨by decide +kernel, rfl⟩⟩
  cases h
  exact ⟨num_ground 0, holds_num grounded 0⟩

def noEnter : String → List Atom → Multiset Atom := fun _ _ => 0

theorem down_hyps (grounded : String → Bool) :
    TVersionHyps decls grounded (fun _ => False) downProgram env env [downEq] noEnter noEnter where
  functional := decls_functional
  accepted eq member := by
    simp only [List.mem_singleton] at member
    subst member
    exact down_accepted grounded
  enterAgree _ _ _ offered := by cases offered
  enterAnswers _ _ _ offered := by cases offered
  prim := (env_ok (Γ := decls) grounded noRes).prim
  primSame := rfl
  keptSame := rfl
  rows _ _ := rfl
  named _ member := by cases member

/-- **`down`'s version is its protocol** at every fuel and every number. -/
theorem down_version (grounded : String → Bool) (n : ℕ) (k : ℤ) :
    protocolRun decls grounded (relBody env noEnter [downEq])
        (arrow (([number] : List (Ty Empty)).map Ty.lift) number.lift) n [num k] =
      versionRun (relBody env noEnter [downEq]) n [num k] :=
  ground_typed_version_eq_protocol (down_hyps grounded) (.cons ⟨rfl, by decide⟩ .nil)
    ⟨rfl, by decide⟩ n [num k] (.cons ⟨num_ground k, holds_num grounded k⟩ .nil)

/-- `(down 3)` answers `0`, once. -/
theorem down_answers : versionRun (relBody env noEnter [downEq]) 5 [num 3] = {num 0} := by
  cbv

/-! ### The ground fact is needed -/

/-- `(= (fs "s") 1)` at `(: fs (-> Number Number))`. -/
def sOne : Equation := ⟨[.const (str "s")], .const (num 1)⟩

/-- `(= (fs $x) (let $x "s" (fs $x)))`. -/
def sLet : Equation := ⟨[.var "x"], .letE (.var "x") (.const (str "s")) (.self [.var "x"])⟩

def fsProgram : TProgram := ⟨[.ground number], .closed number, fun _ => none, fun _ _ => none, []⟩

theorem sOne_accepted (grounded : String → Bool) : TAccepted decls grounded fsProgram sOne :=
  ⟨rfl, _, _, .const _ _ (some number) (fun T h => by
      cases h
      exact ⟨num_ground 1, holds_num grounded 1⟩), Or.inr ⟨by decide +kernel, rfl⟩⟩

/-- **The analysis accepts `(let $x "s" (fs $x))`**: `$x` is ground and a `Number` at
entry, binding a ground value keeps every claim, so the call to itself meets the
GROUND fact (as `contract_bind_any` and `contract_self_call` read it). -/
theorem sLet_accepted (grounded : String → Bool) : TAccepted decls grounded fsProgram sLet := by
  refine ⟨rfl, _, _, .letE (.const _ _ none fun _ h => by cases h) rfl
      (.keeps (fun _ => by decide +kernel) (by decide +kernel))
      (.self (.cons (.var _ "x" (some number) fun U h => ?_) (.nil _))
        (Or.inr (.cons ⟨by decide +kernel, rfl⟩ .nil))), Or.inr ⟨by decide +kernel, rfl⟩⟩
  cases h
  exact ⟨number, .var "x", by simp [fsProgram, sLet], .var "x" number⟩

/-- At the open `$v`, a call whose oracle answers nothing at `"s"` answers `1` once. -/
theorem fs_body_v_zero (o : List Atom → Multiset Atom) (enter : String → List Atom → Multiset Atom)
    (ho : o [str "s"] = 0) : relBody env enter [sOne, sLet] o [.var "v"] = {num 1} := by
  cbv
  rw [ho]
  rfl

theorem var_open (x : String) : support (Atom.var x) ≠ ∅ := by
  simp [support, UnifyAtoms.encode, Mettapedia.Logic.LP.Term.freeVars]

/-- **Groundness is a GROUND entry fact, not a convenience**: the protocol's guard at
`Number` passes once on the open argument `$v`, and the entry test refuses it. Entered
there anyway, the version's head unification binds `$v` to `"s"`, its call to itself
skips the guard that `"s"` fails, and it answers `1` twice where the protocol answers
it once. -/
theorem ground_entry_needed (grounded : String → Bool) :
    count (info decls (.var "v")) number = 1 ∧
      ¬ TAdmitted decls grounded (fun _ => False) fsProgram.positions [.var "v"] ∧
      versionRun (relBody env noEnter [sOne, sLet]) 2 [.var "v"] = {num 1} + {num 1} ∧
      protocolRun decls grounded (relBody env noEnter [sOne, sLet])
        (arrow (([number] : List (Ty Empty)).map Ty.lift) number.lift) 2 [.var "v"] = {num 1} := by
  have guarded : demand (number.lift : Ty String) = .guarded := by decide
  have resultGuarded : ResultGuarded (number.lift : Ty String) := by decide
  have stringZero : chainCall decls (metatype grounded) (relBody env noEnter [sOne, sLet] fun _ => 0)
      (arrow (([number] : List (Ty Empty)).map Ty.lift) number.lift) [str "s"] = 0 := by
    rw [chainCall_closed]
    have none : count (info decls (str "s")) number = 0 := by
      have h := count_class decls (g := .string "s") (c := "String") rfl number
      simpa using h
    have guard : guardCount (info decls (str "s")) number (metatype grounded (str "s")) = 0 := by
      unfold guardCount
      rw [if_pos none]
      rfl
    simp [argCount, guard, guarded]
  refine ⟨count_var decls "v" number, fun admitted => ?_, ?_, ?_⟩
  · cases admitted with
    | cons here _ => exact var_open "v" here.1
  · cbv
  · simp only [protocolRun]
    rw [chainCall_closed, fs_body_v_zero _ _ stringZero]
    have once : guardCount (info decls (.var "v")) number (metatype grounded (.var "v")) = 1 := by
      unfold guardCount
      rw [count_var]
      rfl
    have numOnce : guardCount (info decls (num 1)) number (metatype grounded (num 1)) = 1 := by
      unfold guardCount
      rw [count_int]
      rfl
    simp [argCount, once, numOnce, guarded, resultGuarded, one_nsmul]

/-! ### An instance version -/

/-- `(= (build $n $acc) (if (> $n 0) (build (- $n 1) (Cons $n $acc)) $acc))` at
`(: build (-> Number (List $a) (List $a)))`, read at the instance `$a := Number`. -/
def buildEq : Equation :=
  ⟨[.var "n", .var "acc"],
    .ifE (.prim ">" [.var "n", .const (num 0)])
      (.self [.prim "-" [.var "n", .const (num 1)], .ctor "Cons" [.var "n", .var "acc"]])
      (.var "acc")⟩

def buildProgram : TProgram :=
  ⟨[.ground number, .ground listNumber], .closed listNumber, fun _ => none, primClass, []⟩

/-- **`build` is accepted at the instance**: `(Cons $n $acc)` is a ground list of
numbers by its constructor's declaration (`contract_constructed_type`), so the call to
itself meets both INSTANCE facts and both branches give a ground `(List Number)`. -/
theorem build_accepted (grounded : String → Bool) : TAccepted decls grounded buildProgram buildEq := by
  have factN : eqTypes decls buildProgram.positions buildEq.pats "n" number :=
    ⟨number, .var "n", by simp [buildProgram, buildEq], .var _ _⟩
  have factAcc : eqTypes decls buildProgram.positions buildEq.pats "acc" listNumber :=
    ⟨listNumber, .var "acc", by simp [buildProgram, buildEq], .var _ _⟩
  refine ⟨rfl, _, _, .ifE (.prim (.cons (.var _ "n" none fun _ h => by cases h)
      (.cons (.const _ _ none fun _ h => by cases h) (.nil _))) rfl)
    (.self (.cons (.prim (.cons (.var _ "n" none fun _ h => by cases h)
        (.cons (.const _ _ none fun _ h => by cases h) (.nil _))) rfl)
      (.cons (.ctor (t := some listNumber) (.cons (.var _ "n" (some number) fun _ h => by
          cases h
          exact factN) (.cons (.var _ "acc" (some listNumber) fun _ h => by
          cases h
          exact factAcc) (.nil _))) fun T h => ?_) (.nil _)))
      (Or.inr (.cons ⟨by decide +kernel, rfl⟩ (.cons ⟨by decide +kernel, rfl⟩ .nil))))
    (.var _ "acc" (some listNumber) fun _ h => by
      cases h
      exact factAcc), Or.inr ⟨by decide +kernel, by decide +kernel⟩⟩
  cases h
  exact ⟨[.var "a", listOf (.var "a")], listOf (.var "a"), atNumber, cons_row, cons_constructor,
    .cons (fun _ => ⟨by decide, rfl⟩) (.cons (fun _ => ⟨by decide, rfl⟩) .nil), rfl⟩

theorem build_hyps (grounded : String → Bool) :
    TVersionHyps decls grounded (fun _ => False) buildProgram env env [buildEq] noEnter noEnter where
  functional := decls_functional
  accepted eq member := by
    simp only [List.mem_singleton] at member
    subst member
    exact build_accepted grounded
  enterAgree _ _ _ offered := by cases offered
  enterAnswers _ _ _ offered := by cases offered
  prim := (env_ok (Γ := decls) grounded noRes).prim
  primSame := rfl
  keptSame := rfl
  rows _ _ := rfl
  named _ member := by cases member

theorem number_noMeta : NoMeta (Ty.sym "Number" : Ty String) := by
  intro σ
  show ¬ MetaName (.sym "Number")
  decide

/-- **`build`'s instance version is its signature's protocol**: the protocol of
`(-> Number (List $a) (List $a))`, its calls to itself included, at every fuel, on a
number and a ground list of numbers. -/
theorem build_version (grounded : String → Bool) (n : ℕ) (ws : List Atom)
    (admitted : TAdmitted decls grounded (fun _ => False) buildProgram.positions ws) :
    protocolRun decls grounded (relBody env noEnter [buildEq]) (arrow [.sym "Number", listA] listA) n ws =
      versionRun (relBody env noEnter [buildEq]) n ws :=
  instance_typed_version_eq_protocol (build_hyps grounded) (Fs := [.sym "Number", listA]) (R := listA)
    atNumber rfl rfl (fun F member => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact ⟨by decide, number_noMeta⟩
      · exact ⟨by decide, noMeta_app _⟩) (by decide) (noMeta_app _) n ws admitted

theorem build_admitted (grounded : String → Bool) (k : ℤ) :
    TAdmitted decls grounded (fun _ => False) buildProgram.positions [num k, sym "Nil"] :=
  .cons ⟨num_ground k, holds_num grounded k⟩
    (.cons ⟨by simp [support, UnifyAtoms.encode, Mettapedia.Logic.LP.Term.freeVars],
      Holds.of_count (count_nil _)⟩ .nil)

/-- `(build 2 Nil)` is `(Cons 1 (Cons 2 Nil))`, once. -/
theorem build_answers :
    versionRun (relBody env noEnter [buildEq]) 3 [num 2, sym "Nil"] =
      {app "Cons" [num 1, app "Cons" [num 2, sym "Nil"]]} := by
  cbv

/-! ### The pair beside a GROUND and an ANY parameter -/

/-- `(= (tag $a $n $b) (let $b inc (let $r (if (== $n 0) 0 (tag $a (- $n 1) $b)) $a)))`
at `(: tag (-> $t Number %Undefined% $t))`: the body binds the ANY parameter to the
declared `inc`, which an open argument there shares with the caller. -/
def tagEq : Equation :=
  ⟨[.var "a", .var "n", .var "b"],
    .letE (.var "b") (.const (sym "inc"))
      (.letE (.var "r")
        (.ifE (.prim "==" [.var "n", .const (num 0)]) (.const (num 0))
          (.self [.var "a", .prim "-" [.var "n", .const (num 1)], .var "b"]))
        (.var "a"))⟩

def tagProgram : TProgram := ⟨[.pair, .ground number, .any], .pair, fun _ => none, primClass, []⟩

/-- **`tag` is accepted**: the call to itself passes the ground uninterpreted argument,
a ground `Number`, and anything at ANY; the equation returns the polymorphic pattern. -/
theorem tag_accepted (grounded : String → Bool) : TAccepted decls grounded tagProgram tagEq := by
  refine ⟨rfl, _, _, .letE (.const _ _ none fun _ h => by cases h) rfl
      (.keeps (fun _ => by decide +kernel) (by decide +kernel))
      (.letE (.ifE (.prim (.cons (.var _ "n" none fun _ h => by cases h)
          (.cons (.const _ _ none fun _ h => by cases h) (.nil _))) rfl)
        (.const _ _ none fun _ h => by cases h)
        (.self (.cons (.var _ "a" none fun _ h => by cases h)
          (.cons (.prim (.cons (.var _ "n" none fun _ h => by cases h)
            (.cons (.const _ _ none fun _ h => by cases h) (.nil _))) rfl)
          (.cons (.var _ "b" none fun _ h => by cases h) (.nil _))))
          (Or.inr (.cons ⟨by decide +kernel, by decide +kernel⟩
            (.cons ⟨by decide +kernel, rfl⟩ (.cons trivial .nil))))))
        (by decide +kernel) (.clean (by decide +kernel) (by decide +kernel))
        (.var _ "a" none fun _ h => by cases h)),
    Or.inr ⟨by decide +kernel, .var "a", rfl, .letE (.letE .refl)⟩⟩

theorem tag_hyps (grounded : String → Bool) :
    TVersionHyps decls grounded (fun _ => False) tagProgram env env [tagEq] noEnter noEnter where
  functional := decls_functional
  accepted eq member := by
    simp only [List.mem_singleton] at member
    subst member
    exact tag_accepted grounded
  enterAgree _ _ _ offered := by cases offered
  enterAnswers _ _ _ offered := by cases offered
  prim := (env_ok (Γ := decls) grounded noRes).prim
  primSame := rfl
  keptSame := rfl
  rows _ _ := rfl
  named _ member := by cases member

/-- **`tag`'s version is the protocol of `(-> $t Number %Undefined% $t)`** at every fuel,
at a ground uninterpreted argument, a number, and anything at the ANY position: an
open variable there is bound to the declared `inc` by the body. -/
theorem tag_version (grounded : String → Bool) (n : ℕ) (ws : List Atom)
    (admitted : TAdmitted decls grounded (fun _ => False) tagProgram.positions ws) :
    protocolRun decls grounded (relBody env noEnter [tagEq])
        (arrow (([] : List (Ty Empty)).map Ty.lift ++ .var "a" ::
          ([number, .sym "%Undefined%"] : List (Ty Empty)).map Ty.lift) (.var "a")) n ws =
      versionRun (relBody env noEnter [tagEq]) n ws :=
  pair_typed_version_eq_protocol (tag_hyps grounded) (pre := []) (post := [.ground number, .any])
    "a" rfl rfl .nil (.cons ⟨rfl, by decide⟩
      (.cons (show demand ((Ty.sym "%Undefined%" : Ty Empty).lift : Ty String) ≠ .guarded by decide) .nil))
    n ws admitted

def boxOne : Atom := app "plainbox" [num 1]

theorem tag_admitted (grounded : String → Bool) (k : ℤ) (y : String) :
    TAdmitted decls grounded (fun _ => False) tagProgram.positions [boxOne, num k, .var y] :=
  .cons ⟨Finset.eq_empty_iff_forall_notMem.mpr fun z occurs => by
      obtain ⟨part, member, occurs⟩ := (support_expression _ z).mp occurs
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl <;>
        simp [support, UnifyAtoms.encode, Mettapedia.Logic.LP.Term.freeVars] at occurs,
    by simp [boxOne, Uninterp, Safe, SafeAll, HeadFree, substA, decls, sym, num, app]⟩
    (.cons ⟨num_ground k, holds_num grounded k⟩ (.cons trivial .nil))

/-- `(tag (plainbox 1) 2 $y)` answers `(plainbox 1)`, once, binding `$y` to `inc`
inside. -/
theorem tag_answers : versionRun (relBody env noEnter [tagEq]) 4 [boxOne, num 2, .var "y"] = {boxOne} := by
  cbv

end Controls

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.TwoWayTypedVersions
