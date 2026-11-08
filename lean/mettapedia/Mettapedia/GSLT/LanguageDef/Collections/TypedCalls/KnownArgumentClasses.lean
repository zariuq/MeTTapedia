import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.DeclaredBuiltins

/-!
# Argument checks decided when the call is compiled

The prepared machine checks a typed call's arguments before it enters the
callee (`prepared_pure_typed_arguments_accepted`, `prepared_pure_structural_arguments_accepted`)
and declines the run where a check fails. Two rules skip a check whose verdict
compilation already knows.

**Classes known at compilation** (`prepared_pure_typed_arguments_known`). The
class reader `prepared_pure_node_value_class` (`classify`) gives a node the
class of a literal, of an integer or boolean register, of a call to a typed head
whose range is a value class, of an `if` whose arms agree, of a `let`'s body,
and of a slot through the slot classes it is given; anything else is unknown. A
call site skips the typed argument check when every argument at a value-class
parameter is read at that class, and the argument at the parameter whose class
the answer takes is read at some class (`known`).

The machine (`step`, `run`) evaluates nodes eagerly left to right, enters an
equation of the callee at the argument values, runs its body one level of fuel
down, and checks the answer's class at return where the head owes one
(`retOK`). A head owes none exactly where every equation's body is read at the
range's class with its parameters' slots at their formals' classes
(`WF.shown`, the C's `checks_return`); the slots of bare parameters hold the
arguments (`WF.enter`); a `let` binds new slots only (`WF.bindKeeps`).

* `step_sound`, `run_sound`: in every run, a node the reader gives a class has a
  value of that class (a slot read `PARAMETER` has the activation's parameter
  class). A typed call's value has its range's class by the return check, or,
  where the check is not compiled, by the reader on the body: the two facts are
  proved together, by induction on fuel.
* `known_accepts`: at a call site the reader decides, every argument vector the
  machine produces passes the check.
* **`run_skip`**: the machine that skips the decided checks has, at every fuel,
  every slot and every node, exactly the outcome of the machine that runs them,
  answers, empty answers and declines alike.
* **The check it skips is PeTTa's guard** (`known_literals`, `known_guard_once`):
  each argument there is a literal of its formal's class, so the guard
  `get-type *-> true ; get-metatype` continues exactly once at that formal,
  whatever the declarations (`guardCount_literal`, T4), under the condition the
  machine admits typed heads on (`prepared_pure_petta_intrinsic_type_guard`: no
  `get-type` or `get-metatype` rule, symbol subjects only). HE's cast at a value
  class is the same class test (`HEReturns.evalAtom_grounded`).
* `Controls`: a literal, a typed call's range, agreeing arms and a `let` whose
  body is a literal are known; arms that disagree, a slot and a `let` whose body
  is a slot are not. **The return check is needed**: a head `bad : (-> Number
  Number)` answering `"s"` with its check dropped makes the machine that skips
  answer `7` where the machine that checks declines (`skip_needs_shown`).

**Structural checks decided at compilation**
(`prepared_pure_structural_arguments_known`, `structKnown`). The check
(`structAccepted`) passes every call to a head without a trusted structural
version, every call a PeTTa head makes to itself, and, at each structural
position, an argument whose check the caller discharged, or (HE) whose formal the
open range's instance reads. Compilation decides it exactly where the head has
no version or calls itself, or every structural position is discharged (or an
instance formal in HE): then the check passes on every argument vector, whatever
its type tests answer (`structKnown_accepts`), so skipping it changes no outcome
(`structKnown_skip`). This needs the frame running the code to be the head it
was compiled for (`frame->head == lowering->head`), which holds for equation
bodies, the root body and producer steps.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.KnownArgumentClasses

open Mettapedia.Languages.MeTTa.OSLFCore (Atom GroundedValue)

/-! ## Classes -/

/-- The classes the prepared machine reads (`PreparedPureValueClass`, in its
order): `%Undefined%`, the three value classes, nothing known, the parameter
whose class the answer takes, and a structural type. -/
inductive VCls where
  | undefined
  | number
  | string
  | bool
  | unknown
  | parameter
  | structural
  deriving DecidableEq, Repr

namespace VCls

/-- The value classes. -/
def isValue : VCls → Bool
  | .number | .string | .bool => true
  | _ => false

/-- The type a value class names. -/
def name : VCls → String
  | .number => "Number"
  | .string => "String"
  | .bool => "Bool"
  | _ => ""

end VCls

/-- The class of a value (`prepared_pure_value_class`): a grounded number,
string or truth value has its class, every other value none. -/
def valueCls : Atom → VCls
  | .grounded (.int _) => .number
  | .grounded (.string _) => .string
  | .grounded (.bool _) => .bool
  | _ => .unknown

theorem valueCls_ne_undefined (v : Atom) : valueCls v ≠ .undefined := by
  unfold valueCls; split <;> simp

theorem valueCls_ne_parameter (v : Atom) : valueCls v ≠ .parameter := by
  unfold valueCls; split <;> simp

theorem valueCls_ne_structural (v : Atom) : valueCls v ≠ .structural := by
  unfold valueCls; split <;> simp

/-- A value of a value class is a literal of the type it names. -/
theorem literal_of_valueCls {c : VCls} (hc : c.isValue = true) {v : Atom} (hv : valueCls v = c) :
    Literal c.name v := by
  match v, c, hc, hv with
  | .grounded (.int _), .number, _, _ => rfl
  | .grounded (.string _), .string, _, _ => rfl
  | .grounded (.bool _), .bool, _, _ => rfl

theorem isValueClass_name {c : VCls} (hc : c.isValue = true) : IsValueClass c.name := by
  cases c <;> simp_all [VCls.isValue, VCls.name, IsValueClass]

/-! ## Outcomes -/

/-- An outcome of the machine: a value, no value (an empty answer), or a decline
of the run to the reference route. -/
inductive Res (α : Type) where
  | ok (a : α)
  | fail
  | decline

namespace Res

/-- Sequencing: a value continues, no value and a decline stop. -/
def bind {α β : Type} : Res α → (α → Res β) → Res β
  | .ok a, f => f a
  | .fail, _ => .fail
  | .decline, _ => .decline

@[simp] theorem ok_bind {α β : Type} (a : α) (f : α → Res β) : (ok a).bind f = f a := rfl

@[simp] theorem fail_bind {α β : Type} (f : α → Res β) : (fail : Res α).bind f = fail := rfl

@[simp] theorem decline_bind {α β : Type} (f : α → Res β) : (decline : Res α).bind f = decline := rfl

theorem bind_eq_ok {α β : Type} {r : Res α} {f : α → Res β} {b : β} :
    r.bind f = .ok b ↔ ∃ a, r = .ok a ∧ f a = .ok b := by
  cases r with
  | ok a => simp
  | fail => simp [bind]
  | decline => simp [bind]

theorem bind_congr {α β : Type} {r : Res α} {f g : α → Res β} (h : ∀ a, r = .ok a → f a = g a) :
    r.bind f = r.bind g := by
  cases r with
  | ok a => exact h a rfl
  | fail => rfl
  | decline => rfl

end Res

/-! ## Programs -/

/-- The kind of value a register computes (`CETTA_GSLT_REGISTER_RESULT_*`). -/
inductive RegKind where
  | exactInt
  | boolean
  | other
  deriving DecidableEq

/-- Nodes of a prepared body, as the class reader sees them: a literal, a
register, a slot, a call of a head, an `if`, a `let` (binder `b`, the bound
value, the body), a selection among arms (`case`, a match with an else), and any
other node, whose children are values (builds, intrinsics). -/
inductive Node where
  | lit (a : Atom)
  | reg (k : RegKind) (op : String) (args : List Node)
  | slot (i : ℕ)
  | call (h : ℕ) (args : List Node)
  | ite (c t e : Node)
  | bind (b : ℕ) (val body : Node)
  | sel (s : ℕ) (key : Node) (arms : List Node)
  | other (tag : ℕ) (args : List Node)

/-- An activation's slots. -/
abbrev Slots := ℕ → Option Atom

/-- A head's policy (`PreparedPureHead`): typed or not, the classes of its
parameters and of its range, the position of the parameter whose class the
answer takes, and whether its answers are checked at return. -/
structure Head where
  typed : Bool
  formals : List VCls
  range : VCls
  rangeParam : ℕ
  checksReturn : Bool

/-- The equation a call enters: its body, its first slots, and the classes the
reader gives those slots (a bare parameter's slot its formal's class). -/
structure Entered where
  body : Node
  slots : Slots
  classes : ℕ → VCls

/-- A program: its heads, the equation a call enters at its argument values,
what registers compute, what `if` reads as true or false, how a `let` binds its
pattern, how a selection picks an arm, and what other nodes compute. -/
structure Program where
  heads : ℕ → Head
  enter : ℕ → List Atom → Res Entered
  reg : RegKind → String → List Atom → Res Atom
  truth : Atom → Option Bool
  bindPat : ℕ → Slots → Atom → Option Slots
  select : ℕ → Slots → Atom → Option (ℕ × Slots)
  other : ℕ → List Atom → Res Atom

/-! ## The checks -/

/-- Whether a head checks its arguments (`checks_arguments`): typed, with some
parameter not `%Undefined%`. -/
def checksArguments (hd : Head) : Bool := hd.typed && hd.formals.any (· != .undefined)

/-- One position of the typed argument check: nothing at `%Undefined%` or a
structural formal, some class at the parameter whose class the answer takes,
the formal's class elsewhere. -/
def argOK : VCls → Atom → Bool
  | .undefined, _ => true
  | .structural, _ => true
  | .parameter, v => valueCls v != .unknown
  | c, v => valueCls v == c

/-- **The typed argument check** (`prepared_pure_typed_arguments_accepted`). -/
def accepts (hd : Head) (vs : List Atom) : Bool :=
  !checksArguments hd || (vs.length == hd.formals.length && (hd.formals.zip vs).all fun p => argOK p.1 p.2)

/-- The class of the argument whose class the answer takes. -/
def paramCls (hd : Head) (vs : List Atom) : VCls :=
  match vs[hd.rangeParam]? with
  | some v => valueCls v
  | none => .unknown

/-- **The return check** (`return_class`): where the head checks its answers, the
answer has its range's class, or its parameter's class at a `PARAMETER` range. -/
def retOK (hd : Head) (vs : List Atom) (v : Atom) : Bool :=
  !hd.checksReturn ||
    match hd.range with
    | .parameter => valueCls v == paramCls hd vs
    | .number => valueCls v == .number
    | .string => valueCls v == .string
    | .bool => valueCls v == .bool
    | _ => true

/-- The class of a register's value by its kind. -/
def regCls : RegKind → VCls
  | .exactInt => .number
  | .boolean => .bool
  | .other => .unknown

/-- **What compilation knows of a node's class** (`prepared_pure_node_value_class`),
its slots read through `sc`. -/
def classify (P : Program) (sc : ℕ → VCls) : Node → VCls
  | .lit a => valueCls a
  | .reg k _ _ => regCls k
  | .slot i => sc i
  | .call h _ => if ((P.heads h).typed && (P.heads h).range.isValue) = true then (P.heads h).range else .unknown
  | .ite _ t e => if classify P sc t = classify P sc e then classify P sc t else .unknown
  | .bind _ _ body => classify P sc body
  | .sel _ _ _ => .unknown
  | .other _ _ => .unknown

/-- One position of `prepared_pure_typed_arguments_known`. -/
def knownAt : VCls → VCls → Bool
  | .undefined, _ => true
  | .structural, _ => true
  | .parameter, k => k != .unknown
  | c, k => k == c

/-- **A call site whose typed argument check compilation decides**
(`prepared_pure_typed_arguments_known`), its arguments read with no slot classes. -/
def known (P : Program) (h : ℕ) (args : List Node) : Bool :=
  !checksArguments (P.heads h) ||
    (args.length == (P.heads h).formals.length &&
      ((P.heads h).formals.zip args).all fun p => knownAt p.1 (classify P (fun _ => .unknown) p.2))

/-! ## The machine -/

mutual
/-- **One level of the machine**: a node's outcome in slots `ρ`, the bodies of the
heads it calls run by `inner`. A call evaluates its arguments, checks them unless
`skip` is set and the call site is `known`, enters an equation and checks the
answer at return. -/
def step (P : Program) (skip : Bool) (inner : Slots → Node → Res Atom) :
    Slots → Node → Res Atom
  | _, .lit a => .ok a
  | ρ, .reg k op args => (stepAll P skip inner ρ args).bind (P.reg k op)
  | ρ, .slot i =>
      match ρ i with
      | some v => .ok v
      | none => .decline
  | ρ, .call h args => (stepAll P skip inner ρ args).bind fun vs =>
      if (!(skip && known P h args) && !accepts (P.heads h) vs) = true then .decline
      else (P.enter h vs).bind fun en => (inner en.slots en.body).bind fun v =>
        if retOK (P.heads h) vs v = true then .ok v else .decline
  | ρ, .ite c t e => (step P skip inner ρ c).bind fun w =>
      match P.truth w with
      | some true => step P skip inner ρ t
      | some false => step P skip inner ρ e
      | none => .decline
  | ρ, .bind b val body => (step P skip inner ρ val).bind fun w =>
      match P.bindPat b ρ w with
      | some ρ' => step P skip inner ρ' body
      | none => .fail
  | ρ, .sel s key arms => (step P skip inner ρ key).bind fun w =>
      match P.select s ρ w with
      | some (i, ρ') => stepArm P skip inner ρ' i arms
      | none => .fail
  | ρ, .other tag args => (stepAll P skip inner ρ args).bind (P.other tag)

/-- The values of a list of nodes, left to right. -/
def stepAll (P : Program) (skip : Bool) (inner : Slots → Node → Res Atom) :
    Slots → List Node → Res (List Atom)
  | _, [] => .ok []
  | ρ, e :: es => (step P skip inner ρ e).bind fun v =>
      (stepAll P skip inner ρ es).bind fun vs => .ok (v :: vs)

/-- The selected arm. -/
def stepArm (P : Program) (skip : Bool) (inner : Slots → Node → Res Atom) :
    Slots → ℕ → List Node → Res Atom
  | _, _, [] => .decline
  | ρ, 0, a :: _ => step P skip inner ρ a
  | ρ, i + 1, _ :: as => stepArm P skip inner ρ i as
end

/-- **The machine at fuel `n`**: a call's body runs one level down, and at the
last level a call declines. -/
def run (P : Program) (skip : Bool) : ℕ → Slots → Node → Res Atom
  | 0 => step P skip fun _ _ => .decline
  | n + 1 => step P skip (run P skip n)

/-! ## What a class claims -/

/-- What a class claims of a value in an activation whose parameter class is
`pc`: a value class its class, `PARAMETER` the parameter's class, which is a
value class; the other classes nothing. -/
def Meets (pc : VCls) : VCls → Atom → Prop
  | .number, v => valueCls v = .number
  | .string, v => valueCls v = .string
  | .bool, v => valueCls v = .bool
  | .parameter, v => valueCls v = pc ∧ pc.isValue = true
  | .undefined, _ => True
  | .unknown, _ => True
  | .structural, _ => True

/-- The classes that claim something. -/
def Claims : VCls → Prop
  | .number | .string | .bool | .parameter => True
  | .undefined | .unknown | .structural => False

theorem meets_of_not_claims {pc c : VCls} (h : ¬ Claims c) (v : Atom) : Meets pc c v := by
  cases c <;> simp_all [Claims, Meets]

theorem meets_isValue {pc c : VCls} (hc : c.isValue = true) {v : Atom} :
    Meets pc c v ↔ valueCls v = c := by
  cases c <;> simp_all [VCls.isValue, Meets]

theorem meets_valueCls (pc : VCls) (a : Atom) : Meets pc (valueCls a) a := by
  cases a with
  | grounded g => cases g <;> simp [Meets, valueCls]
  | symbol _ => simp [Meets, valueCls]
  | var _ => simp [Meets, valueCls]
  | expression _ => simp [Meets, valueCls]

/-- **An activation's slots meet their classes**: every slot the reader gives a
class that claims something is bound, to a value meeting it. -/
structure Frame (sc : ℕ → VCls) (pc : VCls) (ρ : Slots) : Prop where
  bound : ∀ i, Claims (sc i) → ρ i ≠ none
  meets : ∀ i v, ρ i = some v → Meets pc (sc i) v

/-- No slot class claims anything: the reader at a call site. -/
theorem frame_unknown (pc : VCls) (ρ : Slots) : Frame (fun _ => .unknown) pc ρ where
  bound := fun _ h => h.elim
  meets := fun _ _ _ => trivial

/-- **What compilation guarantees of a program**: registers compute their kind's
class, a `let` binds only slots not yet bound, no parameter's class is
`unknown`, a bare parameter's slot holds its argument when the arguments pass the
check, and a typed head with a value-class range that checks no answer has every
equation's body read at its range's class. -/
structure WF (P : Program) : Prop where
  regInt : ∀ op vs v, P.reg .exactInt op vs = .ok v → valueCls v = .number
  regBool : ∀ op vs v, P.reg .boolean op vs = .ok v → valueCls v = .bool
  bindKeeps : ∀ b ρ w ρ', P.bindPat b ρ w = some ρ' → ∀ i, ρ i ≠ none → ρ' i = ρ i
  formals : ∀ h, ∀ f ∈ (P.heads h).formals, f ≠ .unknown
  enter : ∀ h vs en, accepts (P.heads h) vs = true → P.enter h vs = .ok en →
    Frame en.classes (paramCls (P.heads h) vs) en.slots
  shown : ∀ h vs en, (P.heads h).typed = true → (P.heads h).checksReturn = false →
    (P.heads h).range.isValue = true → P.enter h vs = .ok en →
    classify P en.classes en.body = (P.heads h).range

/-- A `let` keeps an activation's slots meeting their classes. -/
theorem Frame.bindPat {P : Program} (hP : WF P) {sc : ℕ → VCls} {pc : VCls} {ρ ρ' : Slots}
    (fr : Frame sc pc ρ) {b : ℕ} {w : Atom} (hb : P.bindPat b ρ w = some ρ') : Frame sc pc ρ' where
  bound i hi := by
    rw [hP.bindKeeps b ρ w ρ' hb i (fr.bound i hi)]
    exact fr.bound i hi
  meets i v hv := by
    by_cases hρ : ρ i = none
    · exact meets_of_not_claims (fun hc => fr.bound i hc hρ) v
    · rw [hP.bindKeeps b ρ w ρ' hb i hρ] at hv
      exact fr.meets i v hv

/-! ## The reader is sound -/

/-- An evaluator of bodies whose values meet what the reader gives them. -/
def InnerSound (P : Program) (inner : Slots → Node → Res Atom) : Prop :=
  ∀ (sc : ℕ → VCls) (pc : VCls) (ρ : Slots) (e : Node) (v : Atom),
    Frame sc pc ρ → inner ρ e = .ok v → Meets pc (classify P sc e) v

theorem retOK_value {hd : Head} {vs : List Atom} {v : Atom} (hr : hd.checksReturn = true)
    (hc : hd.range.isValue = true) (h : retOK hd vs v = true) : valueCls v = hd.range := by
  unfold retOK at h
  rw [hr] at h
  cases hrange : hd.range <;> simp_all [VCls.isValue]

/-- **The reader is sound for one level of the machine that checks**: given
bodies whose values meet the reader, every node's value meets the class the
reader gives it. A typed call's value has its range's class: by the return
check, or, where none is compiled, by the reader on the entered body, whose
slots the argument check made meet their classes. -/
theorem step_sound {P : Program} (hP : WF P) {inner : Slots → Node → Res Atom}
    (hi : InnerSound P inner) :
    ∀ (e : Node) (sc : ℕ → VCls) (pc : VCls) (ρ : Slots) (v : Atom), Frame sc pc ρ →
      step P false inner ρ e = .ok v → Meets pc (classify P sc e) v
  | .lit a, _, pc, _, v, _, h => by
      simp only [step, Res.ok.injEq] at h
      subst h
      exact meets_valueCls pc a
  | .reg k op args, _, pc, ρ, v, _, h => by
      simp only [step] at h
      obtain ⟨vs, -, hv⟩ := Res.bind_eq_ok.mp h
      cases k with
      | exactInt => exact (meets_isValue rfl).mpr (hP.regInt op vs v hv)
      | boolean => exact (meets_isValue rfl).mpr (hP.regBool op vs v hv)
      | other => trivial
  | .slot i, _, _, ρ, v, fr, h => by
      simp only [step] at h
      split at h
      · next w hw =>
          simp only [Res.ok.injEq] at h
          subst h
          exact fr.meets i w hw
      · cases h
  | .call h args, sc, pc, ρ, v, _, hrun => by
      simp only [step] at hrun
      obtain ⟨vs, -, hvs⟩ := Res.bind_eq_ok.mp hrun
      simp only [Bool.false_and, Bool.not_false, Bool.true_and] at hvs
      split at hvs
      · cases hvs
      · next hacc =>
          have acc : accepts (P.heads h) vs = true := by simpa using hacc
          obtain ⟨en, hen, hbody⟩ := Res.bind_eq_ok.mp hvs
          obtain ⟨v', hv', hret⟩ := Res.bind_eq_ok.mp hbody
          split at hret
          · next hr =>
              simp only [Res.ok.injEq] at hret
              subst hret
              simp only [classify]
              split
              · next hty =>
                  simp only [Bool.and_eq_true] at hty
                  rw [meets_isValue hty.2]
                  cases hc : (P.heads h).checksReturn
                  · have shown := hP.shown h vs en hty.1 hc hty.2 hen
                    have := hi en.classes (paramCls (P.heads h) vs) en.slots en.body v'
                      (hP.enter h vs en acc hen) hv'
                    rw [shown, meets_isValue hty.2] at this
                    exact this
                  · exact retOK_value hc hty.2 hr
              · trivial
          · cases hret
  | .ite c t e, sc, pc, ρ, v, fr, hrun => by
      simp only [step] at hrun
      obtain ⟨w, -, hw⟩ := Res.bind_eq_ok.mp hrun
      simp only [classify]
      split
      · next heq =>
          split at hw
          · exact step_sound hP hi t sc pc ρ v fr hw
          · rw [heq]
            exact step_sound hP hi e sc pc ρ v fr hw
          · cases hw
      · trivial
  | .bind b val body, sc, pc, ρ, v, fr, hrun => by
      simp only [step] at hrun
      obtain ⟨w, -, hw⟩ := Res.bind_eq_ok.mp hrun
      simp only [classify]
      split at hw
      · next ρ' hb => exact step_sound hP hi body sc pc ρ' v (fr.bindPat hP hb) hw
      · cases hw
  | .sel _ _ _, _, _, _, _, _, _ => trivial
  | .other _ _, _, _, _, _, _, _ => trivial

/-- The reader is sound for every level of the machine that checks. -/
theorem run_sound {P : Program} (hP : WF P) : ∀ n, InnerSound P (run P false n)
  | 0 => fun sc pc ρ e v fr h =>
      step_sound hP (fun _ _ _ _ _ _ h' => by cases h') e sc pc ρ v fr h
  | n + 1 => fun sc pc ρ e v fr h => step_sound hP (run_sound hP n) e sc pc ρ v fr h

/-! ## The decided check passes -/

theorem stepAll_ok {P : Program} {skip : Bool} {inner : Slots → Node → Res Atom} {ρ : Slots} :
    ∀ {es : List Node} {vs : List Atom}, stepAll P skip inner ρ es = .ok vs →
      List.Forall₂ (fun e v => step P skip inner ρ e = .ok v) es vs
  | [], vs, h => by
      simp only [stepAll, Res.ok.injEq] at h
      subst h
      exact .nil
  | e :: es, vs, h => by
      simp only [stepAll] at h
      obtain ⟨v, hv, h⟩ := Res.bind_eq_ok.mp h
      obtain ⟨vs', hvs', h⟩ := Res.bind_eq_ok.mp h
      simp only [Res.ok.injEq] at h
      subst h
      exact .cons hv (stepAll_ok hvs')

/-- Reading the reader's class with no slot classes: a value class or nothing. -/
def Plain : VCls → Prop
  | .number | .string | .bool | .unknown => True
  | .undefined | .parameter | .structural => False

theorem plain_valueCls (a : Atom) : Plain (valueCls a) := by
  unfold valueCls
  split <;> trivial

theorem classify_plain (P : Program) : ∀ e : Node, Plain (classify P (fun _ => .unknown) e)
  | .lit a => plain_valueCls a
  | .reg k _ _ => by cases k <;> trivial
  | .slot _ => trivial
  | .call h _ => by
      simp only [classify]
      split
      · next hty =>
          simp only [Bool.and_eq_true] at hty
          have := hty.2
          cases hr : (P.heads h).range <;> simp_all [VCls.isValue, Plain]
      · trivial
  | .ite _ t e => by
      simp only [classify]
      split
      · exact classify_plain P t
      · trivial
  | .bind _ _ body => classify_plain P body
  | .sel _ _ _ => trivial
  | .other _ _ => trivial

/-- A position the reader decides passes the check on a value meeting the read class. -/
theorem argOK_of_knownAt {f k : VCls} (hf : f ≠ .unknown) (hk : Plain k) {pc : VCls} {v : Atom}
    (hknown : knownAt f k = true) (hm : Meets pc k v) : argOK f v = true := by
  cases f with
  | undefined => rfl
  | structural => rfl
  | unknown => exact absurd rfl hf
  | parameter =>
      simp only [knownAt, bne_iff_ne, ne_eq] at hknown
      simp only [argOK, bne_iff_ne, ne_eq]
      cases k <;> simp_all [Plain, Meets]
  | number =>
      simp only [knownAt, beq_iff_eq] at hknown
      subst hknown
      simpa [argOK, Meets] using hm
  | string =>
      simp only [knownAt, beq_iff_eq] at hknown
      subst hknown
      simpa [argOK, Meets] using hm
  | bool =>
      simp only [knownAt, beq_iff_eq] at hknown
      subst hknown
      simpa [argOK, Meets] using hm

theorem zip_all_of_forall₂ {α β γ : Type} {R : β → γ → Prop} {p : α × β → Bool} {q : α × γ → Bool}
    (hpq : ∀ a b c, R b c → p (a, b) = true → q (a, c) = true) :
    ∀ {as : List α} {bs : List β} {cs : List γ}, List.Forall₂ R bs cs →
      (as.zip bs).all p = true → (as.zip cs).all q = true
  | [], _, _, _, _ => by simp
  | _ :: _, [], [], .nil, _ => by simp
  | a :: as, b :: bs, c :: cs, .cons hbc hrest, h => by
      simp only [List.zip_cons_cons, List.all_cons, Bool.and_eq_true] at h ⊢
      exact ⟨hpq a b c hbc h.1, zip_all_of_forall₂ hpq hrest h.2⟩

/-- **At a call site compilation decides, the check passes**: every argument
vector the machine that checks produces passes the typed argument check. -/
theorem known_accepts {P : Program} (hP : WF P) {inner : Slots → Node → Res Atom}
    (hi : InnerSound P inner) {h : ℕ} {args : List Node} {ρ : Slots} {vs : List Atom}
    (hk : known P h args = true) (hvs : stepAll P false inner ρ args = .ok vs) :
    accepts (P.heads h) vs = true := by
  unfold known at hk
  unfold accepts
  cases hc : checksArguments (P.heads h)
  · rfl
  · rw [hc] at hk
    simp only [Bool.not_true, Bool.false_or, Bool.and_eq_true, beq_iff_eq] at hk
    have hall := stepAll_ok hvs
    simp only [Bool.not_true, Bool.false_or, Bool.and_eq_true, beq_iff_eq]
    refine ⟨hall.length_eq ▸ hk.1, ?_⟩
    have pairs : ∀ f ∈ (P.heads h).formals, f ≠ .unknown := hP.formals h
    clear hc
    -- Walk the formals together with the arguments and their values.
    have key : ∀ (fs : List VCls) (es : List Node) (ws : List Atom), (∀ f ∈ fs, f ≠ .unknown) →
        List.Forall₂ (fun e v => step P false inner ρ e = .ok v) es ws →
        (fs.zip es).all (fun p => knownAt p.1 (classify P (fun _ => .unknown) p.2)) = true →
        (fs.zip ws).all (fun p => argOK p.1 p.2) = true := by
      intro fs
      induction fs with
      | nil => intros; simp
      | cons f fs ih =>
          intro es ws hfs hew hz
          cases hew with
          | nil => simp
          | cons hev hrest =>
              simp only [List.zip_cons_cons, List.all_cons, Bool.and_eq_true] at hz ⊢
              refine ⟨?_, ih _ _ (fun g hg => hfs g (List.mem_cons_of_mem _ hg)) hrest hz.2⟩
              exact argOK_of_knownAt (hfs f (by simp)) (classify_plain P _) hz.1
                (step_sound hP hi _ (fun _ => .unknown) .unknown ρ _ (frame_unknown _ ρ) hev)
    exact key _ _ _ pairs hall hk.2

/-! ## Skipping the decided check changes no outcome -/

mutual
/-- **One level of the machine that skips is the machine that checks**, given
bodies whose values meet the reader. -/
theorem step_skip {P : Program} (hP : WF P) {inner : Slots → Node → Res Atom}
    (hi : InnerSound P inner) : ∀ (ρ : Slots) (e : Node), step P true inner ρ e = step P false inner ρ e
  | _, .lit _ => rfl
  | ρ, .reg k op args => by
      simp only [step]
      rw [stepAll_skip hP hi ρ args]
  | _, .slot _ => rfl
  | ρ, .call h args => by
      simp only [step]
      rw [stepAll_skip hP hi ρ args]
      refine Res.bind_congr fun vs hvs => ?_
      cases hk : known P h args
      · simp
      · simp [known_accepts hP hi hk hvs]
  | ρ, .ite c t e => by
      simp only [step]
      rw [step_skip hP hi ρ c]
      refine Res.bind_congr fun w _ => ?_
      split
      · exact step_skip hP hi ρ t
      · exact step_skip hP hi ρ e
      · rfl
  | ρ, .bind b val body => by
      simp only [step]
      rw [step_skip hP hi ρ val]
      refine Res.bind_congr fun w _ => ?_
      split
      · next ρ' _ => exact step_skip hP hi ρ' body
      · rfl
  | ρ, .sel s key arms => by
      simp only [step]
      rw [step_skip hP hi ρ key]
      refine Res.bind_congr fun w _ => ?_
      split
      · next i ρ' _ => exact stepArm_skip hP hi ρ' i arms
      · rfl
  | ρ, .other tag args => by
      simp only [step]
      rw [stepAll_skip hP hi ρ args]

theorem stepAll_skip {P : Program} (hP : WF P) {inner : Slots → Node → Res Atom}
    (hi : InnerSound P inner) :
    ∀ (ρ : Slots) (es : List Node), stepAll P true inner ρ es = stepAll P false inner ρ es
  | _, [] => rfl
  | ρ, e :: es => by
      simp only [stepAll]
      rw [step_skip hP hi ρ e, stepAll_skip hP hi ρ es]

theorem stepArm_skip {P : Program} (hP : WF P) {inner : Slots → Node → Res Atom}
    (hi : InnerSound P inner) :
    ∀ (ρ : Slots) (i : ℕ) (arms : List Node), stepArm P true inner ρ i arms = stepArm P false inner ρ i arms
  | _, _, [] => rfl
  | ρ, 0, a :: _ => by
      simp only [stepArm]
      exact step_skip hP hi ρ a
  | ρ, i + 1, _ :: as => by
      simp only [stepArm]
      exact stepArm_skip hP hi ρ i as
end

/-- **Skipping the checks compilation decides is exact**
(`prepared_pure_typed_arguments_known`): at every fuel, in every slots and on
every node, the machine that skips them has the outcome of the machine that runs
them, values, empty answers and declines alike. -/
theorem run_skip {P : Program} (hP : WF P) : ∀ n, run P true n = run P false n
  | 0 => by
      funext ρ e
      exact step_skip hP (fun _ _ _ _ _ _ h => by cases h) ρ e
  | n + 1 => by
      funext ρ e
      simp only [run]
      rw [run_skip hP n]
      exact step_skip hP (run_sound hP n) ρ e

/-! ## The skipped check is PeTTa's guard -/

/-- **Each argument at a value-class formal of a decided call site is a literal of
its class.** -/
theorem known_literals {P : Program} (hP : WF P) {inner : Slots → Node → Res Atom}
    (hi : InnerSound P inner) {h : ℕ} {args : List Node} {ρ : Slots} {vs : List Atom}
    (hk : known P h args = true) (hvs : stepAll P false inner ρ args = .ok vs)
    (hcheck : checksArguments (P.heads h) = true) :
    ∀ p ∈ (P.heads h).formals.zip vs, p.1.isValue = true → Literal p.1.name p.2 := by
  have acc := known_accepts hP hi hk hvs
  unfold accepts at acc
  rw [hcheck] at acc
  simp only [Bool.not_true, Bool.false_or, Bool.and_eq_true, List.all_eq_true] at acc
  intro p hp hv
  have := acc.2 p hp
  obtain ⟨f, v⟩ := p
  refine literal_of_valueCls hv ?_
  cases f <;> simp_all [VCls.isValue, argOK]

/-- **The guard the decided check stands for continues exactly once**: PeTTa's
guard at each value-class formal of a decided call site passes its argument once,
whatever the declarations (T4, `guardCount_literal`). -/
theorem known_guard_once {P : Program} (hP : WF P) {inner : Slots → Node → Res Atom}
    (hi : InnerSound P inner) {h : ℕ} {args : List Node} {ρ : Slots} {vs : List Atom}
    (hk : known P h args = true) (hvs : stepAll P false inner ρ args = .ok vs)
    (hcheck : checksArguments (P.heads h) = true) (Γ : Decls) (grounded : String → Bool) :
    ∀ p ∈ (P.heads h).formals.zip vs, p.1.isValue = true →
      guardCount (info Γ p.2) (.sym p.1.name) (metatype grounded p.2) = 1 := fun p hp hv =>
  guardCount_literal grounded (isValueClass_name hv) (known_literals hP hi hk hvs hcheck p hp hv)

/-! ## Structural checks decided at compilation -/

/-- A head's structural policy: an HE head with structural formals, a PeTTa head
with a trusted structural version, its parameters' classes, and the formals an
open range's instance reads. -/
structure SHead where
  heStructural : Bool
  selfTrusted : Bool
  formals : List VCls
  instanceFormal : ℕ → Bool

/-- Whether position `i` is structural. -/
def SHead.structuralAt (hd : SHead) (i : ℕ) : Bool := hd.formals[i]? == some .structural

/-- **The structural argument check** (`prepared_pure_structural_arguments_accepted`):
in HE every structural argument that is neither an instance formal nor
discharged has HE's type there; in PeTTa a head without a trusted version, or a
call to itself, passes, and otherwise every structural argument not discharged
is ground and typed once at its formal. The type tests are oracles. -/
def structAccepted (hd : SHead) (args : List Atom) (selfCall : Bool) (discharged : ℕ → Bool)
    (heHasType typedOnce : ℕ → Atom → Bool) (ground : Atom → Bool) : Bool :=
  if hd.heStructural then
    args.length == hd.formals.length &&
      (List.range args.length).all fun i => !hd.structuralAt i ||
        (decide (i < 64) && hd.instanceFormal i) || (decide (i < 8) && discharged i) ||
          heHasType i (args.getD i (.symbol ""))
  else if (!hd.selfTrusted || selfCall) = true then true
  else
    args.length == hd.formals.length &&
      (List.range args.length).all fun i => !hd.structuralAt i ||
        (decide (i < 8) && discharged i) ||
          (ground (args.getD i (.symbol "")) && typedOnce i (args.getD i (.symbol "")))

/-- **What compilation decides of it** (`prepared_pure_structural_arguments_known`),
in the code of head `lowered`, at a call of `callee` with `count` arguments. -/
def structKnown (hd : SHead) (lowered callee count : ℕ) (discharged : ℕ → Bool) : Bool :=
  if (!hd.heStructural && (!hd.selfTrusted || lowered == callee)) = true then true
  else
    count == hd.formals.length &&
      (List.range count).all fun i => !hd.structuralAt i ||
        (hd.heStructural && decide (i < 64) && hd.instanceFormal i) || (decide (i < 8) && discharged i)

theorem all_imp {α : Type} {l : List α} {p q : α → Bool} (himp : ∀ a ∈ l, p a = true → q a = true)
    (h : l.all p = true) : l.all q = true :=
  List.all_eq_true.mpr fun a ha => himp a ha (List.all_eq_true.mp h a ha)

/-- **A decided structural check passes** on every argument vector of the call,
whatever its type tests answer, where the frame running the code is the head it
was compiled for. -/
theorem structKnown_accepts {hd : SHead} {lowered callee frame : ℕ} {discharged : ℕ → Bool}
    {args : List Atom} (hk : structKnown hd lowered callee args.length discharged = true)
    (hframe : frame = lowered) (heHasType typedOnce : ℕ → Atom → Bool) (ground : Atom → Bool) :
    structAccepted hd args (frame == callee) discharged heHasType typedOnce ground = true := by
  subst hframe
  unfold structKnown at hk
  unfold structAccepted
  cases hhe : hd.heStructural
  · cases hst : hd.selfTrusted
    · simp
    · cases hself : (frame == callee)
      · simp only [hhe, hst, hself, Bool.not_false, Bool.not_true, Bool.false_or, Bool.true_and,
          Bool.false_eq_true, if_false, Bool.and_eq_true] at hk ⊢
        refine ⟨hk.1, all_imp (fun i _ hi => ?_) hk.2⟩
        simp only [Bool.or_eq_true, Bool.false_and, Bool.or_false] at hi ⊢
        tauto
      · simp
  · simp only [hhe, Bool.not_true, Bool.false_and, Bool.false_eq_true, if_false, if_true,
      Bool.and_eq_true, Bool.true_and] at hk ⊢
    refine ⟨hk.1, all_imp (fun i _ hi => ?_) hk.2⟩
    simp only [Bool.or_eq_true] at hi ⊢
    tauto

/-- **Skipping a decided structural check is exact**: for any continuation, the
call that skips it where it is decided has the outcome of the call that runs it. -/
theorem structKnown_skip {α : Type} {hd : SHead} {lowered callee : ℕ} {discharged : ℕ → Bool}
    {args : List Atom} (heHasType typedOnce : ℕ → Atom → Bool) (ground : Atom → Bool)
    (k : Res α) :
    (if (!structKnown hd lowered callee args.length discharged &&
          !structAccepted hd args (lowered == callee) discharged heHasType typedOnce ground) = true
      then .decline else k) =
      (if (!structAccepted hd args (lowered == callee) discharged heHasType typedOnce ground) = true
        then .decline else k) := by
  cases hk : structKnown hd lowered callee args.length discharged
  · simp
  · simp [structKnown_accepts hk rfl heHasType typedOnce ground]

/-! ## Controls -/

namespace Controls

/-- A grounded integer. -/
abbrev int (z : ℤ) : Atom := .grounded (.int z)

/-- A grounded string. -/
abbrev str (s : String) : Atom := .grounded (.string s)

/-- PeTTa's truth values. -/
def truthOf : Atom → Option Bool
  | .grounded (.bool b) => some b
  | _ => none

/-- Integer addition, the one register the controls use. -/
def addReg : RegKind → String → List Atom → Res Atom
  | .exactInt, "+", [.grounded (.int a), .grounded (.int b)] => .ok (int (a + b))
  | _, _, _ => .decline

/-- A `let` binding slot `5`. -/
def bindFresh : ℕ → Slots → Atom → Option Slots
  | _, ρ, w => match ρ 5 with
    | none => some fun i => if i = 5 then some w else ρ i
    | some _ => none

/-- `(: inc (-> Number Number))` with `(= (inc $x) (+ $x 1))` (head `0`), and
`(: bad (-> Number Number))` with `(= (bad $x) "s")` (head `1`), whose body the
reader gives `String`, so its answers are checked. -/
def heads (badChecks : Bool) : ℕ → Head
  | 0 => ⟨true, [.number], .number, 0, false⟩
  | 1 => ⟨true, [.number], .number, 0, badChecks⟩
  | _ => ⟨false, [], .undefined, 0, false⟩

/-- The slots of a one-parameter equation: the argument in slot `0`, read at
`Number`. -/
def oneSlot (v : Atom) : Slots := fun i => if i = 0 then some v else none

def oneClass : ℕ → VCls := fun i => if i = 0 then .number else .unknown

/-- The program, with `inc`'s body `incBody`. -/
def prog (badChecks : Bool) (incBody : Node) : Program where
  heads := heads badChecks
  enter := fun h vs => match h, vs with
    | 0, [v] => .ok ⟨incBody, oneSlot v, oneClass⟩
    | 1, [v] => .ok ⟨.lit (str "s"), oneSlot v, oneClass⟩
    | _, _ => .decline
  reg := addReg
  truth := truthOf
  bindPat := bindFresh
  select := fun _ _ _ => none
  other := fun _ _ => .decline

/-- `inc`'s body `(+ $x 1)`. -/
def incBody : Node := .reg .exactInt "+" [.slot 0, .lit (int 1)]

/-- **Known call sites**: a literal, a typed call's range, agreeing arms and a
`let` whose body is a literal are read at `Number`. -/
theorem known_cases :
    known (prog true incBody) 0 [.lit (int 5)] = true ∧
      known (prog true incBody) 0 [.call 0 [.lit (int 5)]] = true ∧
      known (prog true incBody) 0 [.ite (.lit (.grounded (.bool true))) (.lit (int 1)) (.lit (int 2))] = true ∧
      known (prog true incBody) 0 [.bind 0 (.lit (int 3)) (.lit (int 4))] = true := by
  refine ⟨rfl, rfl, rfl, rfl⟩

/-- **Call sites left to the check**: arms that disagree, a slot (read with no slot
classes) and a `let` whose body is a slot. -/
theorem unknown_cases :
    known (prog true incBody) 0 [.ite (.lit (.grounded (.bool true))) (.lit (int 1)) (.lit (str "s"))] = false ∧
      known (prog true incBody) 0 [.slot 0] = false ∧
      known (prog true incBody) 0 [.bind 0 (.lit (int 3)) (.slot 5)] = false := by
  refine ⟨rfl, rfl, rfl⟩

theorem bindFresh_keeps : ∀ b ρ w ρ', bindFresh b ρ w = some ρ' → ∀ i, ρ i ≠ none → ρ' i = ρ i := by
  intro b ρ w ρ' h i hi
  unfold bindFresh at h
  cases h5 : ρ 5 with
  | none =>
      simp only [h5, Option.some.injEq] at h
      subst h
      by_cases hi5 : i = 5
      · subst hi5
        exact absurd h5 hi
      · simp [hi5]
  | some _ => simp [h5] at h

/-- The program with `bad`'s answers checked meets the guarantees. -/
theorem prog_wf (incBody' : Node) (shownInc : classify (prog true incBody') oneClass incBody' = .number) :
    WF (prog true incBody') where
  regInt op vs v h := by
    simp only [prog] at h
    unfold addReg at h
    split at h
    · simp only [Res.ok.injEq] at h
      subst h
      rfl
    · cases h
  regBool op vs v h := by
    simp only [prog, addReg] at h
    cases h
  bindKeeps := bindFresh_keeps
  formals h f hf := by
    simp only [prog] at hf
    match h, hf with
    | 0, hf => simp [heads] at hf; subst hf; decide
    | 1, hf => simp [heads] at hf; subst hf; decide
    | _ + 2, hf => simp [heads] at hf
  enter h vs en hacc hen := by
    match h, vs, hen with
    | 0, [v], hen =>
        simp only [prog, Res.ok.injEq] at hen
        subst hen
        simp [prog, heads, accepts, checksArguments, argOK] at hacc
        exact {
          bound := fun i hi => by
            by_cases h0 : i = 0
            · simp [oneSlot, h0]
            · simp [oneClass, h0, Claims] at hi
          meets := fun i w hw => by
            by_cases h0 : i = 0
            · subst h0
              simp only [oneSlot, if_true, Option.some.injEq] at hw
              subst hw
              simpa [oneClass, Meets] using hacc
            · simp [oneSlot, h0] at hw }
    | 1, [v], hen =>
        simp only [prog, Res.ok.injEq] at hen
        subst hen
        simp [prog, heads, accepts, checksArguments, argOK] at hacc
        exact {
          bound := fun i hi => by
            by_cases h0 : i = 0
            · simp [oneSlot, h0]
            · simp [oneClass, h0, Claims] at hi
          meets := fun i w hw => by
            by_cases h0 : i = 0
            · subst h0
              simp only [oneSlot, if_true, Option.some.injEq] at hw
              subst hw
              simpa [oneClass, Meets] using hacc
            · simp [oneSlot, h0] at hw }
  shown h vs en hty hc hval hen := by
    match h, vs, hen with
    | 0, [v], hen =>
        simp only [prog, Res.ok.injEq] at hen
        subst hen
        simpa [prog, heads] using shownInc
    | 1, [v], hen => simp [prog, heads] at hc

/-- `inc`'s body `(+ $x 1)` is read at `Number`: no return check is compiled. -/
theorem incBody_shown : classify (prog true incBody) oneClass incBody = .number := rfl

/-- `(inc (inc 5))` answers `7` on both machines. -/
theorem inc_inc : run (prog true incBody) true 2 (fun _ => none) (.call 0 [.call 0 [.lit (int 5)]]) = .ok (int 7) ∧
    run (prog true incBody) false 2 (fun _ => none) (.call 0 [.call 0 [.lit (int 5)]]) = .ok (int 7) :=
  ⟨rfl, rfl⟩

/-- `(inc (bad 1))`: `bad`'s answer `"s"` fails its return check, and both machines
decline, though the call site is decided by `bad`'s range. -/
theorem inc_bad : known (prog true incBody) 0 [.call 1 [.lit (int 1)]] = true ∧
    run (prog true incBody) true 2 (fun _ => none) (.call 0 [.call 1 [.lit (int 1)]]) = .decline ∧
    run (prog true incBody) false 2 (fun _ => none) (.call 0 [.call 1 [.lit (int 1)]]) = .decline :=
  ⟨rfl, rfl, rfl⟩

/-- `inc`'s body `7`, which reads nothing of its argument. -/
def constBody : Node := .lit (int 7)

/-- **The return check is needed**: with `bad`'s check dropped (its body read at
`String` though its range is `Number`, against `WF.shown`), the machine that
skips answers `(inc (bad 1))` with `7` where the machine that checks declines at
`inc`'s argument `"s"`. -/
theorem skip_needs_shown :
    run (prog false constBody) true 2 (fun _ => none) (.call 0 [.call 1 [.lit (int 1)]]) = .ok (int 7) ∧
      run (prog false constBody) false 2 (fun _ => none) (.call 0 [.call 1 [.lit (int 1)]]) = .decline ∧
      ¬ WF (prog false constBody) := by
  refine ⟨rfl, rfl, fun hP => ?_⟩
  have := hP.shown 1 [int 1] ⟨.lit (str "s"), oneSlot (int 1), oneClass⟩ rfl rfl rfl rfl
  simp [classify, valueCls, prog, heads] at this

/-- **Structural checks**: a PeTTa head's call to itself, a call to a head without
a trusted version and a call whose one structural argument is discharged are
decided; a call from another head with an undischarged structural argument is
not, and its check runs; in HE an instance formal is decided. -/
theorem structural_cases :
    structKnown ⟨false, true, [.structural], fun _ => false⟩ 3 3 1 (fun _ => false) = true ∧
      structKnown ⟨false, false, [.structural], fun _ => false⟩ 2 3 1 (fun _ => false) = true ∧
      structKnown ⟨false, true, [.structural], fun _ => false⟩ 2 3 1 (fun i => i == 0) = true ∧
      structKnown ⟨false, true, [.structural], fun _ => false⟩ 2 3 1 (fun _ => false) = false ∧
      structAccepted ⟨false, true, [.structural], fun _ => false⟩ [.symbol "Leaf"] false
        (fun _ => false) (fun _ _ => false) (fun _ _ => false) (fun _ => true) = false ∧
      structKnown ⟨true, false, [.structural], fun i => i == 0⟩ 2 3 1 (fun _ => false) = true :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

end Controls

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.KnownArgumentClasses
