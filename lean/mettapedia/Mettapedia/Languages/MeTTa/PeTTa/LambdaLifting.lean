import Mettapedia.Languages.MeTTa.PeTTa.PrivateCode
import Mettapedia.Languages.MeTTa.PeTTa.ScopedSource
import Mettapedia.Data.FirstFreshName
import Std.Data.String.ToNat

/-!
# One staged lambda: exact name, ordered captures and private code

This is the ordinary, non-eta-expanded clause-formation profile of SWI-PeTTa's translator: inspect the
original body's key identities, exclude argument variables, keep first
occurrences, and install one generated equation outside `&self`. Captures
remain held variables until ordinary execution resolves them.

The supplied body is the body installed at this boundary. A recursive source
translator must first translate nested bodies and preserve raw/quoted syntax;
eta expansion and recursive source-compiler adequacy remain separate obligations.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.LambdaLifting

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (atomFreeVars)
open SpaceSemantics (Equation Program)

def name (ordinal : Nat) : String := "lambda_" ++ Nat.repr ordinal

theorem name_injective : Function.Injective name := by
  intro first second same
  exact Nat.repr_injective ((String.append_right_inj "lambda_").mp same)

def scan (bound seen : List String) : List String → List String
  | [] => []
  | key :: rest =>
      if key ∈ bound ∨ key ∈ seen then scan bound seen rest
      else key :: scan bound (key :: seen) rest

/-- Independent first-occurrence rules, retaining the source key order. -/
inductive CaptureScan (bound : List String) : List String → List String → List String → Prop where
  | nil {seen} : CaptureScan bound seen [] []
  | bound {seen key rest output} :
      key ∈ bound → CaptureScan bound seen rest output →
      CaptureScan bound seen (key :: rest) output
  | seen {seen key rest output} :
      key ∈ seen → CaptureScan bound seen rest output →
      CaptureScan bound seen (key :: rest) output
  | capture {seen key rest output} :
      key ∉ bound → key ∉ seen → CaptureScan bound (key :: seen) rest output →
      CaptureScan bound seen (key :: rest) (key :: output)

theorem captureScan_computes {bound seen input output : List String}
    (source : CaptureScan bound seen input output) : scan bound seen input = output := by
  induction source with
  | nil => rfl
  | bound present _ ih => simp [scan,present,ih]
  | seen present _ ih => simp [scan,present,ih]
  | capture notBound notSeen _ ih => simp [scan,notBound,notSeen,ih]

theorem captureScan_of_computed (bound seen input : List String) :
    CaptureScan bound seen input (scan bound seen input) := by
  induction input generalizing seen with
  | nil => exact .nil
  | cons key rest ih =>
      by_cases boundMember : key ∈ bound
      · simpa [scan,boundMember] using CaptureScan.bound boundMember (ih seen)
      · by_cases seenMember : key ∈ seen
        · simpa [scan,seenMember] using CaptureScan.seen seenMember (ih seen)
        · simpa [scan,boundMember,seenMember] using
            CaptureScan.capture boundMember seenMember (ih (key :: seen))

theorem captureScan_iff (bound seen input output : List String) :
    CaptureScan bound seen input output ↔ scan bound seen input = output := by
  constructor
  · exact captureScan_computes
  · rintro rfl; exact captureScan_of_computed bound seen input

theorem scan_mem (bound seen input : List String) (key : String) :
    key ∈ scan bound seen input ↔ key ∈ input ∧ key ∉ bound ∧ key ∉ seen := by
  induction input generalizing seen with
  | nil => simp [scan]
  | cons first rest ih =>
      by_cases same : key = first
      · subst key
        by_cases excluded : first ∈ bound ∨ first ∈ seen
        · rcases excluded with inside | earlier
          · simp [scan,inside,ih]
          · simp [scan,earlier,ih]
        · simp_all [scan]
      · by_cases excluded : first ∈ bound ∨ first ∈ seen <;> simp_all [scan]

theorem scan_nodup (bound seen input : List String) : (scan bound seen input).Nodup := by
  induction input generalizing seen with
  | nil => exact .nil
  | cons first rest ih =>
      by_cases excluded : first ∈ bound ∨ first ∈ seen
      · simpa only [scan,if_pos excluded] using ih seen
      · simp only [scan,if_neg excluded]
        apply List.Nodup.cons _ (ih (first :: seen))
        intro present
        exact ((scan_mem bound (first :: seen) rest first).mp present).2.2 (by simp)

def captures (arguments : List Atom) (body : Atom) : List String :=
  scan (atomFreeVars (.expression arguments)) [] (atomFreeVars body)

theorem captures_mem (arguments : List Atom) (body : Atom) (key : String) :
    key ∈ captures arguments body ↔
      key ∈ atomFreeVars body ∧ key ∉ atomFreeVars (.expression arguments) := by
  simp [captures,scan_mem]

def equation (generated : String) (arguments : List Atom) (body : Atom) (captured : List String) : Equation :=
  ⟨generated,captured.map Atom.var ++ arguments,body⟩

def value (generated : String) : List String → Atom
  | [] => .symbol generated
  | captured => Eval.partialValue generated (captured.map Atom.var)

structure Table where
  code : List Equation := []
  cursor : Nat := 0
  occupied : Finset String := ∅

structure Lifted where
  table : Table
  ordinal : Nat
  captured : List String
  installed : Equation
  closure : Atom

/-- Current public/foreign function names and prior private names are exact
spellings. Looking like a generated name does not itself reserve a name. -/
def occupied (table : Table) (registry : Program) (foreign : Finset String) : Finset String :=
  table.occupied ∪ foreign ∪ (registry.equations.map (·.head)).toFinset ∪
    (table.code.map (·.head)).toFinset

def lift (table : Table) (registry : Program) (foreign : Finset String)
    (arguments : List Atom) (originalBody compiledBody : Atom) : Lifted :=
  let ordinal := Mettapedia.FirstFreshName.choose name name_injective
    (occupied table registry foreign) (table.cursor + 1)
  let captured := captures arguments originalBody
  let installed := equation (name ordinal) arguments compiledBody captured
  ⟨⟨table.code ++ [installed],ordinal,insert (name ordinal) (occupied table registry foreign)⟩,
    ordinal,captured,installed,value (name ordinal) captured⟩

/-- Source formation specifies the first fresh ordinal and independently
derives captures. It does not mention the executable `lift`. -/
inductive LiftRel (table : Table) (registry : Program) (foreign : Finset String)
    (arguments : List Atom) (originalBody compiledBody : Atom) : Lifted → Prop where
  | formed {ordinal captured} :
      table.cursor + 1 ≤ ordinal → name ordinal ∉ occupied table registry foreign →
      (∀ earlier, table.cursor + 1 ≤ earlier → earlier < ordinal →
        name earlier ∈ occupied table registry foreign) →
      CaptureScan (atomFreeVars (.expression arguments)) [] (atomFreeVars originalBody) captured →
      LiftRel table registry foreign arguments originalBody compiledBody
        ⟨⟨table.code ++ [equation (name ordinal) arguments compiledBody captured],ordinal,
          insert (name ordinal) (occupied table registry foreign)⟩,
          ordinal,captured,equation (name ordinal) arguments compiledBody captured,
          value (name ordinal) captured⟩

theorem lift_source (table : Table) (registry : Program) (foreign : Finset String)
    (arguments : List Atom) (originalBody compiledBody : Atom) :
    LiftRel table registry foreign arguments originalBody compiledBody
      (lift table registry foreign arguments originalBody compiledBody) := by
  have fresh := Mettapedia.FirstFreshName.choose_spec name name_injective
    (occupied table registry foreign) (table.cursor + 1)
  exact .formed fresh.1 fresh.2
    (Mettapedia.FirstFreshName.choose_minimal name name_injective
      (occupied table registry foreign) (table.cursor + 1))
    (captureScan_of_computed _ _ _)

theorem lift_iff (table : Table) (registry : Program) (foreign : Finset String)
    (arguments : List Atom) (originalBody compiledBody : Atom) (result : Lifted) :
    LiftRel table registry foreign arguments originalBody compiledBody result ↔
      lift table registry foreign arguments originalBody compiledBody = result := by
  constructor
  · intro source
    cases source with
    | formed lower fresh earlier captured =>
        have ordinal := (Mettapedia.FirstFreshName.choose_eq_iff name name_injective
          (occupied table registry foreign) (table.cursor + 1) _).mpr ⟨lower,fresh,earlier⟩
        have capture := captureScan_computes captured
        simp only [lift,ordinal,captures,capture]
  · rintro rfl; exact lift_source table registry foreign arguments originalBody compiledBody

theorem lift_fresh (table : Table) (registry : Program) (foreign : Finset String)
    (arguments : List Atom) (originalBody compiledBody : Atom) :
    (lift table registry foreign arguments originalBody compiledBody).installed.head ∉
      occupied table registry foreign :=
  (Mettapedia.FirstFreshName.choose_spec name name_injective
    (occupied table registry foreign) (table.cursor + 1)).2

/-- Admit source variables before invoking the actual evaluator. The scope
supply is explicit when earlier requests or retained values already exist. -/
def enterAt (scope : Nat) (result : Lifted) (state : Effects.State)
    (expression : Atom) : Unifying.Configuration :=
  ScopedSource.enter scope result.table.code state expression

/-- Initial source request with private clauses. No equation is added as a
public atom; the request's own names receive the first activation scope. -/
def enter (result : Lifted) (state : Effects.State) (expression : Atom) : Unifying.Configuration :=
  enterAt 0 result state expression

theorem enter_public_store (result : Lifted) (state : Effects.State) (expression : Atom) :
    (enter result state expression).state = state := rfl

end Mettapedia.Languages.MeTTa.PeTTa.LambdaLifting
