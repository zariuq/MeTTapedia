import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Machines.TermRewriting
import Mettapedia.Languages.PartrecMachine.Realization

/-!
# The machine of the partial recursive functions is one finite positive program of the step

`Mettapedia.Languages.PartrecMachine` authors Mathlib's `Turing.ToPartrec` machine (codes of partial recursive
functions on lists of naturals, evaluated by a continuation-passing small step) as a language definition with
nineteen premise-free first-order rewrites, and proves that a pending evaluation of a code `c` on `v` reduces to
the halted configuration with output `w` exactly when `w ∈ c.eval v` (`PartrecMachine.adequacy`).

This module hosts that machine on `RuleSyntax.step`, at the one first-order frame over rows with unknowns.

* **The program** (`program`): nineteen rules, one per rewrite of the authored machine (`rule`, transcribed
  from `PartrecMachine.rewrites`; that the transcription is the authored reduction on the encoded image is the
  theorem `rewrites_iff` with `reduces_iff_successor`). Each takes one row and makes one row. No rule has a read, a tell, an equation guard,
  a none check, a count check or a query pattern (`rule_fragment`): the tests of the machine (the code, the
  continuation, the empty list, a zero head, a successor head) are patterns, so positive rules suffice. The program does not depend on the function computed: the code of the function is data in the row.
  The machine is a term-rewriting machine in the sense of `Machines.TermRewriting` (`program_eq_rootRules`).
* **The row of a configuration** (`Point.row`): a pending evaluation or a configuration of the machine, as one
  ground row; `Point.pattern` is its term in the authored language.
* **One reduction is one rewrite of the one-row bag** (`rewrites_iff`): forward by exhibiting the rule and its
  instantiation; backward because the left sides are pairwise without a common instance (`ruleOf?_lhs`), a
  halted row is an instance of none (`ruleOf?_halt`), and the unknowns of a right side occur in the left side.
* **One reduction is one firing, and no other firing is admitted** (`firing_of_reduction`,
  `reduction_of_firing`), at every state that reads as the row of the configuration
  (`Machines.ReadsBag`): the composite of `rewrites_iff` with `Machines.readsBag_forward` and
  `Machines.readsBag_backward`. The successor is a function of the configuration (`successor`), so the runs of
  the program from such a state are determined up to the made identities and the fresh openings
  (`deterministic`). Halting is the row of a halted configuration, and no firing is admitted there
  (`halted_stuck`).
* **As a correspondence** (`hosted`, `composite`): an `OperationalCorrespondence` from the generated theory of
  the authored machine to rewriting of bags, composed by `OperationalCorrespondence.comp` with
  `Machines.correspondence` into one from the authored machine to the step of the program.
* **What the program computes** (`halts_iff`): the program, run from the one-row state of the pending
  evaluation of `c` on `v`, reaches a state that reads as the halted row with output `w` exactly when
  `w ∈ c.eval v`. This is `PartrecMachine.adequacy` transported along `composite`.
* **Every partial recursive function** (`computes_partrec`): for every `f` with `Nat.Partrec' f` there is a code
  such that the program, run from that code's pending evaluation on the arguments, halts with `[m]` exactly when
  `m ∈ f v`. This is Mathlib's `Turing.ToPartrec.Code.exists_code` composed with `halts_iff`.

Cost: one firing for one reduction of the authored machine. A step of Mathlib's machine is one or more
reductions, because the authored language reduces the pending evaluations that Mathlib's `stepNormal` evaluates
at once (`PartrecMachine.step_simulated`). Numbers are unary rows, as in the authored language: a firing matches
a successor in one step, and the size of the row is the size of the configuration.

## Controls

* A run to its end (`succ_two_halts`): successor on `[2]` halts with `[3]`.
* Without the rule for the successor of the empty list the program is stuck where Mathlib's machine returns
  `[1]` (`withoutSuccOnEmpty_stuck`).
* A case rule that does not test the head for zero (`caseUntested`) fires at a successor head and takes the
  wrong branch (`caseUntested_wrong`, `caseUntested_fires`): the zero test is needed, and it is a pattern.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Machines.PartialRecursive

open Mettapedia.Logic.LP
open Mettapedia.GSLT
open Mettapedia.GSLT.IndexedOperational
open Mettapedia.OSLF.Framework.TypeSynthesis (langGSLT)
open Mettapedia.Languages.PartrecMachine
open Turing.ToPartrec
open NamesOnTheStep (Expr)
open Presentation.Schematic

/-! ## Patterns of rows -/

/-- A constant of rows, as a pattern. -/
def con (k : ℕ) : Tm := .const (.sym k)

/-- An unknown of a rule. -/
def unk (x : ℕ) : Tm := .var x

/-- An application, as a pattern. -/
def ap (f a : Tm) : Tm := .app .app (args2 f a)

/-- An instantiation of the unknowns `0, 1, ...` by a list of rows. -/
def assign : List Expr → ℕ → Expr
  | [], _ => .sym 0
  | e :: _, 0 => e
  | _ :: es, n + 1 => assign es n

/-! ## The rows of the machine -/

/-- A natural number, as a unary row. -/
def eNat : ℕ → Expr
  | 0 => .sym 0
  | n + 1 => .app (.sym 1) (eNat n)

/-- A list of naturals, as a row. -/
def eNats : List ℕ → Expr
  | [] => .sym 2
  | n :: v => .app (.app (.sym 3) (eNat n)) (eNats v)

/-- A code, as a row. -/
def eCode : Code → Expr
  | .zero' => .sym 4
  | .succ => .sym 5
  | .tail => .sym 6
  | .cons f fs => .app (.app (.sym 7) (eCode f)) (eCode fs)
  | .comp f g => .app (.app (.sym 8) (eCode f)) (eCode g)
  | .case f g => .app (.app (.sym 9) (eCode f)) (eCode g)
  | .fix f => .app (.sym 10) (eCode f)

/-- A continuation, as a row. -/
def eCont : Cont → Expr
  | .halt => .sym 11
  | .cons₁ fs as k => .app (.app (.app (.sym 12) (eCode fs)) (eNats as)) (eCont k)
  | .cons₂ ns k => .app (.app (.sym 13) (eNats ns)) (eCont k)
  | .comp f k => .app (.app (.sym 14) (eCode f)) (eCont k)
  | .fix f k => .app (.app (.sym 15) (eCode f)) (eCont k)

/-- A configuration, as a row. -/
def eCfg : Cfg → Expr
  | .halt v => .app (.sym 16) (eNats v)
  | .ret k v => .app (.app (.sym 17) (eCont k)) (eNats v)

/-- A pending evaluation, as a row. -/
def eNormal (c : Code) (k : Cont) (v : List ℕ) : Expr :=
  .app (.app (.app (.sym 18) (eCode c)) (eCont k)) (eNats v)

theorem eNat_injective : ∀ {m n : ℕ}, eNat m = eNat n → m = n
  | 0, 0, _ => rfl
  | 0, _ + 1, same => by cases same
  | _ + 1, 0, same => by cases same
  | _ + 1, _ + 1, same => congrArg Nat.succ (eNat_injective (Expr.app.inj same).2)

theorem eNats_injective : ∀ {v w : List ℕ}, eNats v = eNats w → v = w
  | [], [], _ => rfl
  | [], _ :: _, same => by cases same
  | _ :: _, [], same => by cases same
  | _ :: _, _ :: _, same => by
      have parts := Expr.app.inj same
      rw [eNat_injective (Expr.app.inj parts.1).2, eNats_injective parts.2]

/-- **A point of the encoded image**: a pending evaluation or a configuration. -/
inductive Point where
  | normal (c : Code) (k : Cont) (v : List ℕ)
  | config (cfg : Cfg)

/-- The term of a point in the authored language. -/
def Point.pattern : Point → Mettapedia.OSLF.MeTTaIL.Syntax.Pattern
  | .normal c k v => normalTerm c k v
  | .config cfg => encCfg cfg

/-- **The row of a point.** -/
def Point.row : Point → Expr
  | .normal c k v => eNormal c k v
  | .config cfg => eCfg cfg

/-- What a pending evaluation becomes in one reduction. -/
def afterNormal : Code → Cont → List ℕ → Point
  | .zero', k, v => .config (.ret k (0 :: v))
  | .succ, k, [] => .config (.ret k [1])
  | .succ, k, n :: _ => .config (.ret k [n + 1])
  | .tail, k, [] => .config (.ret k [])
  | .tail, k, _ :: w => .config (.ret k w)
  | .cons f fs, k, v => .normal f (.cons₁ fs v k) v
  | .comp f g, k, v => .normal g (.comp f k) v
  | .case f _, k, [] => .normal f k []
  | .case f _, k, 0 :: w => .normal f k w
  | .case _ g, k, (y + 1) :: w => .normal g k (y :: w)
  | .fix f, k, v => .normal f (.fix f k) v

/-- What a returning configuration becomes in one reduction. -/
def afterRet : Cont → List ℕ → Point
  | .halt, v => .config (.halt v)
  | .cons₁ fs as k, v => .normal fs (.cons₂ v k) as
  | .cons₂ [] k, v => .config (.ret k (0 :: v))
  | .cons₂ (n :: _) k, v => .config (.ret k (n :: v))
  | .comp f k, v => .normal f k v
  | .fix _ k, [] => .config (.ret k [])
  | .fix _ k, 0 :: w => .config (.ret k w)
  | .fix f k, (_ + 1) :: w => .normal f (.fix f k) w

/-- **The successor of a point**: a halted configuration has none. -/
def successor : Point → Option Point
  | .normal c k v => some (afterNormal c k v)
  | .config (.ret k v) => some (afterRet k v)
  | .config (.halt _) => none

theorem pattern_afterNormal (c : Code) (k : Cont) (v : List ℕ) :
    (afterNormal c k v).pattern = normalReduct c k v := by
  cases c with
  | zero' => rfl
  | succ => cases v <;> rfl
  | tail => cases v <;> rfl
  | cons f fs => rfl
  | comp f g => rfl
  | case f g => rcases v with _ | ⟨_ | y, w⟩ <;> rfl
  | fix f => rfl

theorem pattern_afterRet (k : Cont) (v : List ℕ) : (afterRet k v).pattern = retReduct k v := by
  cases k with
  | halt => rfl
  | cons₁ fs as k => rfl
  | cons₂ ns k => cases ns <;> rfl
  | comp f k => rfl
  | fix f k => rcases v with _ | ⟨_ | n, w⟩ <;> rfl

/-- **Reduction of the authored language on the encoded image is the successor.** -/
theorem reduces_iff_successor (p : Point) (target : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern) :
    Reduces p.pattern target ↔ ∃ p', successor p = some p' ∧ target = p'.pattern := by
  cases p with
  | normal c k v =>
      show Reduces (normalTerm c k v) target ↔ _
      rw [reduces_normal_iff, ← pattern_afterNormal]
      constructor
      · intro same
        exact ⟨afterNormal c k v, rfl, same⟩
      · rintro ⟨p', stepped, same⟩
        rw [Option.some.inj stepped]
        exact same
  | config cfg =>
      cases cfg with
      | halt v =>
          constructor
          · intro reduces
            exact absurd reduces (halt_irreducible v target)
          · rintro ⟨p', stepped, -⟩
            cases stepped
      | ret k v =>
          show Reduces (encCfg (.ret k v)) target ↔ _
          rw [reduces_ret_iff, ← pattern_afterRet]
          constructor
          · intro same
            exact ⟨afterRet k v, rfl, same⟩
          · rintro ⟨p', stepped, same⟩
            rw [Option.some.inj stepped]
            exact same

/-! ## The rules -/

/-- The pattern of a pending evaluation. -/
def normalP (c k v : Tm) : Tm := ap (ap (ap (con 18) c) k) v

/-- The pattern of a returning configuration. -/
def retP (k v : Tm) : Tm := ap (ap (con 17) k) v

/-- The pattern of a non-empty list. -/
def consP (n v : Tm) : Tm := ap (ap (con 3) n) v

/-- **The names of the rules**: the names of the rewrites of the authored machine. -/
inductive RuleName where
  | zeroCode | succOnEmpty | succOnCons | tailOnEmpty | tailOnCons | consCode | compCode
  | caseOnEmpty | caseOnZero | caseOnSucc | fixCode
  | returnHalt | returnCons1 | returnCons2OnEmpty | returnCons2OnCons | returnComp
  | returnFixOnEmpty | returnFixOnZero | returnFixOnSucc
  deriving DecidableEq

/-- **The row a rule takes.** -/
def lhs : RuleName → Tm
  | .zeroCode => normalP (con 4) (unk 0) (unk 1)
  | .succOnEmpty => normalP (con 5) (unk 0) (con 2)
  | .succOnCons => normalP (con 5) (unk 0) (consP (unk 1) (unk 2))
  | .tailOnEmpty => normalP (con 6) (unk 0) (con 2)
  | .tailOnCons => normalP (con 6) (unk 0) (consP (unk 1) (unk 2))
  | .consCode => normalP (ap (ap (con 7) (unk 0)) (unk 1)) (unk 2) (unk 3)
  | .compCode => normalP (ap (ap (con 8) (unk 0)) (unk 1)) (unk 2) (unk 3)
  | .caseOnEmpty => normalP (ap (ap (con 9) (unk 0)) (unk 1)) (unk 2) (con 2)
  | .caseOnZero => normalP (ap (ap (con 9) (unk 0)) (unk 1)) (unk 2) (consP (con 0) (unk 3))
  | .caseOnSucc => normalP (ap (ap (con 9) (unk 0)) (unk 1)) (unk 2) (consP (ap (con 1) (unk 3)) (unk 4))
  | .fixCode => normalP (ap (con 10) (unk 0)) (unk 1) (unk 2)
  | .returnHalt => retP (con 11) (unk 0)
  | .returnCons1 => retP (ap (ap (ap (con 12) (unk 0)) (unk 1)) (unk 2)) (unk 3)
  | .returnCons2OnEmpty => retP (ap (ap (con 13) (con 2)) (unk 0)) (unk 1)
  | .returnCons2OnCons => retP (ap (ap (con 13) (consP (unk 0) (unk 1))) (unk 2)) (unk 3)
  | .returnComp => retP (ap (ap (con 14) (unk 0)) (unk 1)) (unk 2)
  | .returnFixOnEmpty => retP (ap (ap (con 15) (unk 0)) (unk 1)) (con 2)
  | .returnFixOnZero => retP (ap (ap (con 15) (unk 0)) (unk 1)) (consP (con 0) (unk 2))
  | .returnFixOnSucc => retP (ap (ap (con 15) (unk 0)) (unk 1)) (consP (ap (con 1) (unk 2)) (unk 3))

/-- **The row a rule makes.** -/
def rhs : RuleName → Tm
  | .zeroCode => retP (unk 0) (consP (con 0) (unk 1))
  | .succOnEmpty => retP (unk 0) (consP (ap (con 1) (con 0)) (con 2))
  | .succOnCons => retP (unk 0) (consP (ap (con 1) (unk 1)) (con 2))
  | .tailOnEmpty => retP (unk 0) (con 2)
  | .tailOnCons => retP (unk 0) (unk 2)
  | .consCode => normalP (unk 0) (ap (ap (ap (con 12) (unk 1)) (unk 3)) (unk 2)) (unk 3)
  | .compCode => normalP (unk 1) (ap (ap (con 14) (unk 0)) (unk 2)) (unk 3)
  | .caseOnEmpty => normalP (unk 0) (unk 2) (con 2)
  | .caseOnZero => normalP (unk 0) (unk 2) (unk 3)
  | .caseOnSucc => normalP (unk 1) (unk 2) (consP (unk 3) (unk 4))
  | .fixCode => normalP (unk 0) (ap (ap (con 15) (unk 0)) (unk 1)) (unk 2)
  | .returnHalt => ap (con 16) (unk 0)
  | .returnCons1 => normalP (unk 0) (ap (ap (con 13) (unk 3)) (unk 2)) (unk 1)
  | .returnCons2OnEmpty => retP (unk 0) (consP (con 0) (unk 1))
  | .returnCons2OnCons => retP (unk 2) (consP (unk 0) (unk 3))
  | .returnComp => normalP (unk 0) (unk 1) (unk 2)
  | .returnFixOnEmpty => retP (unk 1) (con 2)
  | .returnFixOnZero => retP (unk 1) (unk 2)
  | .returnFixOnSucc => normalP (unk 0) (ap (ap (con 15) (unk 0)) (unk 1)) (unk 3)

/-- **A rule of the machine**: take the left row, make the right row. -/
def rule (n : RuleName) : SRule := rowRule (lhs n) (rhs n)

/-- Every name. -/
def names : List RuleName :=
  [.zeroCode, .succOnEmpty, .succOnCons, .tailOnEmpty, .tailOnCons, .consCode, .compCode, .caseOnEmpty,
    .caseOnZero, .caseOnSucc, .fixCode, .returnHalt, .returnCons1, .returnCons2OnEmpty, .returnCons2OnCons,
    .returnComp, .returnFixOnEmpty, .returnFixOnZero, .returnFixOnSucc]

theorem mem_names (n : RuleName) : n ∈ names := by
  cases n <;> decide

/-- **The program of the machine**: its nineteen rules. -/
def program : List SRule := names.map rule

theorem range (n : RuleName) : ∀ x ∈ unknowns (rhs n), x ∈ unknowns (lhs n) := by
  cases n <;> decide

/-- **Every rule of the machine is range-restricted and positive**: it has no read, no tell and no check. -/
theorem rule_fragment (n : RuleName) : RangeRestrictedPositive (rule n) := rowRule_fragment (range n)

theorem program_fragment : ∀ r ∈ program, RangeRestrictedPositive r := by
  intro r member
  obtain ⟨n, -, rfl⟩ := List.mem_map.mp member
  exact rule_fragment n

/-- **The machine is a term-rewriting machine**: its program is the program of its nineteen schemas. -/
theorem program_eq_rootRules : program = rootRules (names.map fun n => (lhs n, rhs n)) :=
  (List.map_map (g := fun p : Tm × Tm => rowRule p.1 p.2) (f := fun n : RuleName => (lhs n, rhs n))
    (l := names)).symm

/-! ## Which rule a row is an instance of -/

/-- The rule a pending evaluation is an instance of, from its code and its list. -/
def normalRule? (code v : Expr) : Option RuleName :=
  match code, v with
  | .sym 4, _ => some .zeroCode
  | .sym 5, .sym 2 => some .succOnEmpty
  | .sym 5, .app (.app (.sym 3) _) _ => some .succOnCons
  | .sym 6, .sym 2 => some .tailOnEmpty
  | .sym 6, .app (.app (.sym 3) _) _ => some .tailOnCons
  | .app (.app (.sym 7) _) _, _ => some .consCode
  | .app (.app (.sym 8) _) _, _ => some .compCode
  | .app (.app (.sym 9) _) _, .sym 2 => some .caseOnEmpty
  | .app (.app (.sym 9) _) _, .app (.app (.sym 3) (.sym 0)) _ => some .caseOnZero
  | .app (.app (.sym 9) _) _, .app (.app (.sym 3) (.app (.sym 1) _)) _ => some .caseOnSucc
  | .app (.sym 10) _, _ => some .fixCode
  | _, _ => none

/-- The rule a returning configuration is an instance of, from its continuation and its list. -/
def retRule? (cont v : Expr) : Option RuleName :=
  match cont, v with
  | .sym 11, _ => some .returnHalt
  | .app (.app (.app (.sym 12) _) _) _, _ => some .returnCons1
  | .app (.app (.sym 13) (.sym 2)) _, _ => some .returnCons2OnEmpty
  | .app (.app (.sym 13) (.app (.app (.sym 3) _) _)) _, _ => some .returnCons2OnCons
  | .app (.app (.sym 14) _) _, _ => some .returnComp
  | .app (.app (.sym 15) _) _, .sym 2 => some .returnFixOnEmpty
  | .app (.app (.sym 15) _) _, .app (.app (.sym 3) (.sym 0)) _ => some .returnFixOnZero
  | .app (.app (.sym 15) _) _, .app (.app (.sym 3) (.app (.sym 1) _)) _ => some .returnFixOnSucc
  | _, _ => none

/-- **The rule a row is an instance of**, if any. -/
def ruleOf? : Expr → Option RuleName
  | .app (.app (.app (.sym 18) code) _) v => normalRule? code v
  | .app (.app (.sym 17) cont) v => retRule? cont v
  | _ => none

/-- **An instance of the left row of a rule is an instance of no other**: the left rows are pairwise without
a common instance. -/
theorem ruleOf?_lhs (n : RuleName) (θ : ℕ → Expr) : ruleOf? (inst θ (lhs n)) = some n := by
  cases n <;> rfl

/-- **A halted row is an instance of no left row.** -/
theorem ruleOf?_halt (v : List ℕ) : ruleOf? (eCfg (.halt v)) = none := rfl

/-- Instantiations that agree on the left row of a rule agree on its right row. -/
theorem rhs_determined (n : RuleName) {θ θ' : ℕ → Expr} (same : inst θ (lhs n) = inst θ' (lhs n)) :
    inst θ (rhs n) = inst θ' (rhs n) :=
  inst_congr (rhs n) fun x vars =>
    agree_of_inst_eq (lhs n) same x (vars_of_mem_unknowns (lhs n) (range n x (mem_unknowns (rhs n) vars)))

/-! ## One reduction is one rewrite of the one-row bag -/

/-- **A pending evaluation is an instance of a left row, and the right row's instance is its successor.** -/
theorem fires_normal (c : Code) (k : Cont) (v : List ℕ) :
    ∃ (n : RuleName) (θ : ℕ → Expr), inst θ (lhs n) = eNormal c k v ∧ inst θ (rhs n) = (afterNormal c k v).row := by
  cases c with
  | zero' => exact ⟨.zeroCode, assign [eCont k, eNats v], rfl, rfl⟩
  | succ =>
      cases v with
      | nil => exact ⟨.succOnEmpty, assign [eCont k], rfl, rfl⟩
      | cons n w => exact ⟨.succOnCons, assign [eCont k, eNat n, eNats w], rfl, rfl⟩
  | tail =>
      cases v with
      | nil => exact ⟨.tailOnEmpty, assign [eCont k], rfl, rfl⟩
      | cons n w => exact ⟨.tailOnCons, assign [eCont k, eNat n, eNats w], rfl, rfl⟩
  | cons f fs => exact ⟨.consCode, assign [eCode f, eCode fs, eCont k, eNats v], rfl, rfl⟩
  | comp f g => exact ⟨.compCode, assign [eCode f, eCode g, eCont k, eNats v], rfl, rfl⟩
  | case f g =>
      rcases v with _ | ⟨_ | y, w⟩
      · exact ⟨.caseOnEmpty, assign [eCode f, eCode g, eCont k], rfl, rfl⟩
      · exact ⟨.caseOnZero, assign [eCode f, eCode g, eCont k, eNats w], rfl, rfl⟩
      · exact ⟨.caseOnSucc, assign [eCode f, eCode g, eCont k, eNat y, eNats w], rfl, rfl⟩
  | fix f => exact ⟨.fixCode, assign [eCode f, eCont k, eNats v], rfl, rfl⟩

/-- **A returning configuration is an instance of a left row, and the right row's instance is its successor.** -/
theorem fires_ret (k : Cont) (v : List ℕ) :
    ∃ (n : RuleName) (θ : ℕ → Expr), inst θ (lhs n) = eCfg (.ret k v) ∧ inst θ (rhs n) = (afterRet k v).row := by
  cases k with
  | halt => exact ⟨.returnHalt, assign [eNats v], rfl, rfl⟩
  | cons₁ fs as k => exact ⟨.returnCons1, assign [eCode fs, eNats as, eCont k, eNats v], rfl, rfl⟩
  | cons₂ ns k =>
      cases ns with
      | nil => exact ⟨.returnCons2OnEmpty, assign [eCont k, eNats v], rfl, rfl⟩
      | cons n ns => exact ⟨.returnCons2OnCons, assign [eNat n, eNats ns, eCont k, eNats v], rfl, rfl⟩
  | comp f k => exact ⟨.returnComp, assign [eCode f, eCont k, eNats v], rfl, rfl⟩
  | fix f k =>
      rcases v with _ | ⟨_ | n, w⟩
      · exact ⟨.returnFixOnEmpty, assign [eCode f, eCont k], rfl, rfl⟩
      · exact ⟨.returnFixOnZero, assign [eCode f, eCont k, eNats w], rfl, rfl⟩
      · exact ⟨.returnFixOnSucc, assign [eCode f, eCont k, eNat n, eNats w], rfl, rfl⟩

/-- A point with a successor is an instance of a left row whose right row's instance is the successor. -/
theorem fires_of_successor {p p' : Point} (stepped : successor p = some p') :
    ∃ (n : RuleName) (θ : ℕ → Expr), inst θ (lhs n) = p.row ∧ inst θ (rhs n) = p'.row := by
  cases p with
  | normal c k v =>
      rw [← Option.some.inj stepped]
      exact fires_normal c k v
  | config cfg =>
      cases cfg with
      | halt v => cases stepped
      | ret k v =>
          rw [← Option.some.inj stepped]
          exact fires_ret k v

/-- **Every instance of a left row at the row of a point makes the row of the point's successor.** -/
theorem successor_of_instance {p : Point} {n : RuleName} {θ : ℕ → Expr} (matched : inst θ (lhs n) = p.row) :
    ∃ p', successor p = some p' ∧ inst θ (rhs n) = p'.row := by
  have found : ruleOf? p.row = some n := by
    rw [← matched]
    exact ruleOf?_lhs n θ
  cases stepped : successor p with
  | none =>
      cases p with
      | normal c k v => cases stepped
      | config cfg =>
          cases cfg with
          | halt v => exact absurd ((ruleOf?_halt v).symm.trans found) (by intro impossible; cases impossible)
          | ret k v => cases stepped
  | some p' =>
      obtain ⟨m, θ', matched', made⟩ := fires_of_successor stepped
      have foundToo : ruleOf? p.row = some m := by
        rw [← matched']
        exact ruleOf?_lhs m θ'
      have sameRule : n = m := Option.some.inj (found.symm.trans foundToo)
      subst sameRule
      exact ⟨p', rfl, (rhs_determined _ (matched.trans matched'.symm)).trans made⟩

/-- **One rewrite of the one-row bag of a point is its successor**, and the successor is one rewrite. -/
theorem rewrites_iff (p : Point) (bag' : Multiset Expr) :
    Rewrites program {p.row} bag' ↔ ∃ p', successor p = some p' ∧ bag' = {p'.row} := by
  constructor
  · rintro ⟨r, member, θ, rest, split, -, -, rfl⟩
    obtain ⟨n, -, rfl⟩ := List.mem_map.mp member
    obtain ⟨matched, restEmpty⟩ := row_of_singleton split
    obtain ⟨p', stepped, made⟩ := successor_of_instance matched
    refine ⟨p', stepped, ?_⟩
    rw [restEmpty]
    exact (add_zero _).trans (congrArg (fun e => ({e} : Multiset Expr)) made)
  · rintro ⟨p', stepped, rfl⟩
    obtain ⟨n, θ, matched, made⟩ := fires_of_successor stepped
    exact ⟨rule n, List.mem_map_of_mem (mem_names n), θ, 0,
      (add_zero _).trans (congrArg (fun e => ({e} : Multiset Expr)) matched),
      fun q member => absurd member List.not_mem_nil, fun e member => absurd member List.not_mem_nil,
      ((add_zero _).trans (congrArg (fun e => ({e} : Multiset Expr)) made)).symm⟩

/-! ## One reduction is one firing -/

/-- **A reduction of the authored machine is one admitted firing of the program**, at every state that reads
as the row of the point, and the result reads as the row of the reduct. -/
theorem firing_of_reduction {p : Point} {s : SState ℕ} (reads : ReadsBag s {p.row})
    {target : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern} (reduces : Reduces p.pattern target) :
    ∃ (g : Firing ℕ E {r | r ∈ program} s.frame) (admitted : (schematicStep ℕ program).Admits (s := s) g)
      (p' : Point), target = p'.pattern ∧ ReadsBag ((schematicStep ℕ program).result g admitted) {p'.row} := by
  obtain ⟨p', stepped, rfl⟩ := (reduces_iff_successor p target).mp reduces
  obtain ⟨g, admitted, reads'⟩ :=
    readsBag_forward program_fragment reads ((rewrites_iff p _).mpr ⟨p', stepped, rfl⟩)
  exact ⟨g, admitted, p', rfl, reads'⟩

/-- **Every admitted firing of the program is the reduction of the authored machine**: at a state that reads
as the row of a point, the result of an admitted firing reads as the row of the point's successor, which is
its one reduct. -/
theorem reduction_of_firing {p : Point} {s : SState ℕ} (reads : ReadsBag s {p.row})
    (g : Firing ℕ E {r | r ∈ program} s.frame) (admitted : (schematicStep ℕ program).Admits (s := s) g) :
    ∃ p' : Point, successor p = some p' ∧ Reduces p.pattern p'.pattern ∧
      ReadsBag ((schematicStep ℕ program).result g admitted) {p'.row} := by
  obtain ⟨bag', rewrites, reads'⟩ := readsBag_backward program_fragment reads g admitted
  obtain ⟨p', stepped, rfl⟩ := (rewrites_iff p bag').mp rewrites
  exact ⟨p', stepped, (reduces_iff_successor p _).mpr ⟨p', stepped, rfl⟩, reads'⟩

/-- **The runs are determined up to the made identities and the openings**: two admitted firings at a state
that reads as the row of a point have results that read as one and the same row. -/
theorem deterministic {p : Point} {s : SState ℕ} (reads : ReadsBag s {p.row})
    (g g' : Firing ℕ E {r | r ∈ program} s.frame)
    (admitted : (schematicStep ℕ program).Admits (s := s) g)
    (admitted' : (schematicStep ℕ program).Admits (s := s) g') :
    ∃ p' : Point, ReadsBag ((schematicStep ℕ program).result g admitted) {p'.row} ∧
      ReadsBag ((schematicStep ℕ program).result g' admitted') {p'.row} := by
  obtain ⟨p', stepped, -, reads'⟩ := reduction_of_firing reads g admitted
  obtain ⟨p'', stepped', -, reads''⟩ := reduction_of_firing reads g' admitted'
  have same : p' = p'' := Option.some.inj (stepped.symm.trans stepped')
  subst same
  exact ⟨p', reads', reads''⟩

/-- **A halted row admits no firing**: halting is the row of a halted configuration, and the program stops
there. -/
theorem halted_stuck {w : List ℕ} {s : SState ℕ} (halted : ReadsBag s {eCfg (.halt w)})
    (g : Firing ℕ E {r | r ∈ program} s.frame) : ¬ (schematicStep ℕ program).Admits (s := s) g := by
  intro admitted
  obtain ⟨p', stepped, -, -⟩ := reduction_of_firing (p := .config (.halt w)) halted g admitted
  cases stepped

/-! ## The correspondence -/

/-- **A term of the authored language is hosted by a bag**: it is the term of a point, and the bag is the
point's one row. -/
def Hosts (term : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern) (bag : Multiset Expr) : Prop :=
  ∃ p : Point, term = p.pattern ∧ bag = {p.row}

/-- **The authored machine and rewriting of one-row bags**: one reduction for one rewrite, both ways. The
source is the generated theory of the authored machine, `PartrecMachine.machineTheory`. -/
def hosted : OperationalCorrespondence machineTheory (rewriting program) where
  related := Hosts
  readStep := by
    rintro term bag bag' ⟨p, rfl, rfl⟩ stepped
    obtain ⟨p', advanced, rfl⟩ := (rewrites_iff p bag').mp stepped
    exact Or.inr ⟨p'.pattern,
      (reduces_iff_generatedStep _ _).mp ((reduces_iff_successor p _).mpr ⟨p', advanced, rfl⟩), p', rfl, rfl⟩
  forward := by
    rintro term after bag ⟨p, rfl, rfl⟩ stepped
    obtain ⟨p', advanced, rfl⟩ :=
      (reduces_iff_successor p after).mp ((reduces_iff_generatedStep _ _).mpr stepped)
    exact ⟨({p'.row} : Multiset Expr), (executionPath_nonempty_iff_multiStep (rewriting program) _ _).mpr
      (.step ((rewrites_iff p _).mpr ⟨p', advanced, rfl⟩) (.refl _)), p', rfl, rfl⟩

/-- **The authored machine and the step of the program**: the composite of `hosted` with the correspondence
between rewriting of bags and the step. -/
def composite : OperationalCorrespondence machineTheory (stepSystem ℕ program) :=
  hosted.comp (correspondence (O := ℕ) program_fragment)

theorem pattern_halt {p : Point} {w : List ℕ} (same : p.pattern = encCfg (.halt w)) :
    p = .config (.halt w) := by
  cases p with
  | normal c k v => exact absurd same (normalTerm_ne_encCfg c k v _)
  | config cfg => exact congrArg Point.config (encCfg_injective same)

theorem row_halt {p : Point} {w : List ℕ} (same : p.row = eCfg (.halt w)) : p = .config (.halt w) := by
  cases p with
  | normal c k v => cases (Expr.app.inj same).1
  | config cfg =>
      cases cfg with
      | halt v => rw [eNats_injective (Expr.app.inj same).2]
      | ret k v => cases (Expr.app.inj same).1

/-- **A state is halted with an output**: it reads as the one row of the halted configuration. -/
def HaltedWith (w : List ℕ) (s : SState ℕ) : Prop := ReadsBag s {eCfg (.halt w)}

/-- Related terms and states agree on being halted with an output. -/
theorem observes (w : List ℕ) {term : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern} {s : SState ℕ}
    (related : ∃ bag, Hosts term bag ∧ ReadsBag s bag) : term = encCfg (.halt w) ↔ HaltedWith w s := by
  obtain ⟨bag, ⟨p, rfl, rfl⟩, reads⟩ := related
  constructor
  · intro same
    have isHalt : p = .config (.halt w) := pattern_halt same
    rw [isHalt] at reads
    exact reads
  · intro halted
    have sameBag : ({p.row} : Multiset Expr) = {eCfg (.halt w)} :=
      readsAs_unique (ReadsBag.readsAs reads).1 (ReadsBag.readsAs reads).2 (ReadsBag.readsAs halted).2
    have isHalt : p = .config (.halt w) := row_halt (Multiset.singleton_inj.mp sameBag)
    subst isHalt
    rfl

/-! ## What the program computes -/

/-- **The start state**: one row, the pending evaluation of a code on a list. -/
def start (c : Code) (v : List ℕ) : SState ℕ := rowState (eNormal c .halt v)

/-- **The program halts with an output**: run from the pending evaluation of `c` on `v`, it reaches a state
that reads as the halted row with output `w`. -/
def Halts (c : Code) (v w : List ℕ) : Prop :=
  ∃ s, (stepSystem ℕ program).MultiStep (start c v) s ∧ HaltedWith w s

/-- **The program computes the evaluation of codes**: it halts with `w` from the pending evaluation of `c` on
`v` exactly when `w ∈ c.eval v`. -/
theorem halts_iff (c : Code) (v w : List ℕ) : Halts c v w ↔ w ∈ c.eval v := by
  rw [← adequacy c v w, reflTransGen_reduces_iff_multiStep]
  have transfer := composite.reachable_iff
    (fun term : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern => term = encCfg (.halt w)) (HaltedWith w)
    (fun {origin current} related => observes w (term := origin) (s := current) related)
    (origin := normalTerm c .halt v) (current := start c v)
    ⟨({eNormal c .halt v} : Multiset Expr), ⟨.normal c .halt v, rfl, rfl⟩, rowState_reads _⟩
  constructor
  · intro halts
    obtain ⟨after, path, rfl⟩ := transfer.mpr halts
    exact path
  · intro path
    exact transfer.mp ⟨_, path, rfl⟩

/-- **A code that diverges has no halted state.** -/
theorem diverges_iff (c : Code) (v : List ℕ) : (∀ w, ¬ Halts c v w) ↔ c.eval v = Part.none := by
  constructor
  · intro never
    exact Part.eq_none_iff.mpr fun w member => never w ((halts_iff c v w).mpr member)
  · intro diverges w halts
    have member := (halts_iff c v w).mp halts
    rw [diverges] at member
    exact Part.notMem_none w member

/-- **Every partial recursive function is computed by the program**: for every `f` with `Nat.Partrec' f` there
is a code such that the program, run from that code's pending evaluation on the arguments, halts with `[m]`
exactly when `m ∈ f v`. -/
theorem computes_partrec {arity : ℕ} {f : List.Vector ℕ arity →. ℕ} (partrec : Nat.Partrec' f) :
    ∃ c : Code, ∀ (v : List.Vector ℕ arity) (m : ℕ), Halts c v.1 [m] ↔ m ∈ f v := by
  obtain ⟨c, evaluates⟩ := Code.exists_code partrec
  refine ⟨c, fun v m => ?_⟩
  rw [halts_iff, evaluates v]
  constructor
  · intro member
    obtain ⟨a, inside, same⟩ := (Part.mem_map_iff _).mp member
    have equal : [a] = [m] := same
    rw [← (List.cons.inj equal).1]
    exact inside
  · intro member
    exact (Part.mem_map_iff _).mpr ⟨m, member, rfl⟩

/-! ## Controls -/

/-- **A run to its end**: successor on `[2]` halts with `[3]`. -/
theorem succ_two_halts : Halts .succ [2] [3] :=
  (halts_iff .succ [2] [3]).mpr (by simp [Code.eval])

/-- The program without the rule for the successor of the empty list. -/
def withoutSuccOnEmpty : List SRule := (names.filter fun n => n != .succOnEmpty).map rule

theorem withoutSuccOnEmpty_fragment : ∀ r ∈ withoutSuccOnEmpty, RangeRestrictedPositive r := by
  intro r member
  obtain ⟨n, -, rfl⟩ := List.mem_map.mp member
  exact rule_fragment n

/-- **Without the rule for the successor of the empty list the program is stuck** at the pending evaluation of
the successor on the empty list, where Mathlib's machine returns `[1]`. -/
theorem withoutSuccOnEmpty_stuck :
    [1] ∈ Code.succ.eval [] ∧
      ∀ g : Firing ℕ E {r | r ∈ withoutSuccOnEmpty} (start .succ []).frame,
        ¬ (schematicStep ℕ withoutSuccOnEmpty).Admits (s := start .succ []) g := by
  refine ⟨by simp [Code.eval], fun g admitted => ?_⟩
  obtain ⟨bag', ⟨r, member, θ, rest, split, -, -, -⟩, -⟩ :=
    readsBag_backward withoutSuccOnEmpty_fragment (rowState_reads (eNormal .succ .halt [])) g admitted
  obtain ⟨n, inNames, rfl⟩ := List.mem_map.mp member
  have matched : inst θ (lhs n) = eNormal .succ .halt [] := (row_of_singleton split).1
  have found : ruleOf? (eNormal .succ .halt []) = some n := by
    rw [← matched]
    exact ruleOf?_lhs n θ
  have isSucc : RuleName.succOnEmpty = n := Option.some.inj found
  subst isSucc
  exact absurd (List.mem_filter.mp inNames).2 (by decide)

/-- A case rule that takes the first branch at every non-empty list, without testing its head for zero. -/
def caseUntested : SRule :=
  rowRule (normalP (ap (ap (con 9) (unk 0)) (unk 1)) (unk 2) (consP (unk 3) (unk 4)))
    (normalP (unk 0) (unk 2) (unk 4))

theorem caseUntested_fragment : ∀ r ∈ [caseUntested], RangeRestrictedPositive r := by
  intro r member
  rw [List.mem_singleton.mp member]
  exact rowRule_fragment (by decide)

/-- **The untested case rule takes the wrong branch at a successor head**: it rewrites the pending evaluation
to the first branch on the tail, which is not the row of the machine's successor. -/
theorem caseUntested_wrong (f g : Code) (k : Cont) (y : ℕ) (w : List ℕ) :
    Rewrites [caseUntested] {eNormal (.case f g) k ((y + 1) :: w)} {eNormal f k w} ∧
      eNormal f k w ≠ (afterNormal (.case f g) k ((y + 1) :: w)).row := by
  refine ⟨⟨caseUntested, List.mem_cons_self, assign [eCode f, eCode g, eCont k, eNat (y + 1), eNats w], 0,
    add_zero _, fun q member => absurd member List.not_mem_nil,
    fun e member => absurd member List.not_mem_nil, (add_zero _).symm⟩, fun same => ?_⟩
  exact List.cons_ne_self y w (eNats_injective (Expr.app.inj same).2).symm

/-- **The untested case rule fires on `RuleSyntax.step`**, with a result that reads as the wrong branch. -/
theorem caseUntested_fires (f g : Code) (k : Cont) (y : ℕ) (w : List ℕ) :
    ∃ (h : Firing ℕ E {r | r ∈ [caseUntested]} (rowState (eNormal (.case f g) k ((y + 1) :: w))).frame)
      (admitted : (schematicStep ℕ [caseUntested]).Admits
        (s := rowState (eNormal (.case f g) k ((y + 1) :: w))) h),
      ReadsBag ((schematicStep ℕ [caseUntested]).result h admitted) {eNormal f k w} :=
  readsBag_forward caseUntested_fragment (rowState_reads _) (caseUntested_wrong f g k y w).1

#print axioms program_eq_rootRules
#print axioms reduces_iff_successor
#print axioms rule_fragment
#print axioms ruleOf?_lhs
#print axioms rewrites_iff
#print axioms firing_of_reduction
#print axioms reduction_of_firing
#print axioms deterministic
#print axioms halted_stuck
#print axioms hosted
#print axioms composite
#print axioms halts_iff
#print axioms diverges_iff
#print axioms computes_partrec
#print axioms succ_two_halts
#print axioms withoutSuccOnEmpty_stuck
#print axioms caseUntested_wrong
#print axioms caseUntested_fires

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Machines.PartialRecursive
