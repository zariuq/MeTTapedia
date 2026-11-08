import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.Protocol
import Mettapedia.Machines.AdmissionRewriting.LocalDeclines

/-!
# Callee demand per call site

A call through a variable, `($f a₁ … aₖ)`, learns its callee only when it runs.
PeTTa delivers each argument by the callee's demand: as written to a parameter
typed `Atom`, evaluated otherwise. CeTTa decides each call by its callee's
declarations before evaluating any argument: a callee with an `Atom` parameter
takes the host route, and every other callee runs natively.

* **Delivery** (`deliver`): a row delivers each argument as written at an `Atom`
  parameter and evaluated at any other; the **host route** delivers by each row
  and runs its protocol (`hostRoute`); the **native route** evaluates every
  argument once and runs the typed call (`nativeRoute`).
* **The native route is the host route** for every callee whose rows have no
  `Atom` parameter (`nativeRoute_eq_hostRoute`), whatever the arguments: the
  decision reads the callee's declarations only, so it is made before any
  argument is evaluated, and a callee without declarations runs natively.
* **The decision observes the host route and never costs more**, through
  `Machines.AdmissionRewriting.LocalDeclines`: deciding per call observes
  exactly what the host route does (`perCall_observes`), and the tier that
  admits per call observes the general engine (`perCall_observes_general`); it
  costs at most the program-wide rule that hosts every call once any
  declaration has an `Atom` parameter (`perCall_le_programWide`), strictly less
  on the lambda loop with an uncalled `(: quoteit (-> Atom Atom))`
  (`Controls.lambda_loop`); a declaration of a head that no call reaches costs
  nothing (`perCall_uncalled`), and a declaration without an `Atom` parameter
  costs nothing at the calls it declares (`perCall_type_monotone`).

Control: with `(: q (-> Atom Atom))`, `(app2 q 1)` with `(= (app2 $f $x) ($f (+ $x 0)))`
delivers `(+ 1 0)` as written, as in the probe `sem_dyn`
(`Controls.raw_delivery`); with an untyped lambda the argument is evaluated
(`Controls.lambda_evaluates`).
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls

open Mettapedia.Languages.MeTTa.OSLFCore (Atom GroundedValue)

/-! ## Delivery and the two routes -/

section Routes

variable (Γ : Decls) (kind : Atom → String)

/-- The values a row delivers: each argument as written at an `Atom` parameter,
evaluated at any other, one list per choice of the values. -/
def deliver (eval : Atom → Multiset Atom) : List (Ty String) → List Atom → Multiset (List Atom)
  | [], [] => {[]}
  | A :: As, a :: as =>
      (if demand A = .raw then {a} else eval a).bind fun v => (deliver eval As as).map (v :: ·)
  | [], _ :: _ => 0
  | _ :: _, [] => 0

theorem deliver_of_length_ne (eval : Atom → Multiset Atom) :
    ∀ (As : List (Ty String)) (args : List Atom), As.length ≠ args.length → deliver eval As args = 0
  | [], [], h => absurd rfl h
  | A :: As, a :: as, h => by
      simp only [deliver]
      rw [deliver_of_length_ne eval As as (by simpa using h)]
      simp
  | [], _ :: _, _ => rfl
  | _ :: _, [], _ => rfl

/-- Every argument evaluated, one list per choice of the values. -/
def evalArgs (eval : Atom → Multiset Atom) : List Atom → Multiset (List Atom)
  | [] => {[]}
  | a :: as => (eval a).bind fun v => (evalArgs eval as).map (v :: ·)

/-- The parameters of a row. -/
def params (τ : Ty String) : List (Ty String) :=
  match arrowSplit τ with
  | some (As, _) => As
  | none => []

/-- A callee has an `Atom` parameter in some row. -/
def RawDemand (rows : List (Ty String)) : Prop := ∃ τ ∈ rows, ∃ A ∈ params τ, demand A = .raw

instance (rows : List (Ty String)) : Decidable (RawDemand rows) := by
  unfold RawDemand
  infer_instance

/-- **The host route**: each row delivers the arguments by its own demand and
runs its protocol; a callee without rows evaluates every argument and runs its
body. -/
noncomputable def hostRoute (eval : Atom → Multiset Atom) (body : List Atom → Multiset Atom)
    (rows : List (Ty String)) (args : List Atom) : Multiset Atom :=
  if rows = [] then (evalArgs eval args).bind body
  else ((dedupAlpha rows : List (Ty String)) : Multiset (Ty String)).bind fun τ =>
    (deliver eval (params τ) args).bind (chainCall Γ kind body τ)

/-- **The native route**: every argument evaluated once, then the typed call. -/
noncomputable def nativeRoute (eval : Atom → Multiset Atom) (body : List Atom → Multiset Atom)
    (rows : List (Ty String)) (args : List Atom) : Multiset Atom :=
  if rows = [] then (evalArgs eval args).bind body
  else (evalArgs eval args).bind (typedCall Γ kind body rows)

theorem deliver_of_no_raw (eval : Atom → Multiset Atom) :
    ∀ (As : List (Ty String)) (args : List Atom), As.length = args.length →
      (∀ A ∈ As, demand A ≠ .raw) → deliver eval As args = evalArgs eval args
  | [], [], _, _ => rfl
  | A :: As, a :: as, len, h => by
      simp only [deliver, evalArgs, if_neg (h A (by simp))]
      rw [deliver_of_no_raw eval As as (by simpa using len) fun B hB => h B (by simp [hB])]
  | [], _ :: _, len, _ => by simp at len
  | _ :: _, [], len, _ => by simp at len

theorem chainCall_of_params_length (body : List Atom → Multiset Atom) (τ : Ty String)
    (vs : List Atom) (h : (params τ).length ≠ vs.length) : chainCall Γ kind body τ vs = 0 := by
  unfold chainCall
  unfold params at h
  split
  · next As R hs =>
      rw [hs] at h
      have : guards Γ kind 0 As vs [] = 0 := by
        clear hs
        revert vs
        suffices ∀ (k : ℕ) (As : List (Ty String)) (vs : List Atom) (S : List (Eqn CallVar)),
            As.length ≠ vs.length → guards Γ kind k As vs S = 0 from fun vs h => this 0 As vs [] h
        intro k As vs S h
        induction As generalizing k vs S with
        | nil => cases vs with
          | nil => exact absurd rfl h
          | cons _ _ => rfl
        | cons A As ih => cases vs with
          | nil => rfl
          | cons v vs =>
              simp only [guards]
              split_ifs
              · rw [Multiset.bind_congr (g := fun _ => 0) fun S' _ => ih (k + 1) vs S' (by simpa using h),
                  Multiset.bind_zero]
              · exact ih (k + 1) vs S (by simpa using h)
      rw [this, Multiset.zero_bind]
  · rfl

theorem evalArgs_length (eval : Atom → Multiset Atom) :
    ∀ (args : List Atom), ∀ vs ∈ evalArgs eval args, vs.length = args.length
  | [], vs, h => by
      simp only [evalArgs, Multiset.mem_singleton] at h
      subst h
      rfl
  | a :: as, vs, h => by
      simp only [evalArgs, Multiset.mem_bind, Multiset.mem_map] at h
      obtain ⟨v, -, vs', hvs', rfl⟩ := h
      simp [evalArgs_length eval as vs' hvs']

/-- **The native route is the host route** for a callee whose rows have no `Atom`
parameter. -/
theorem nativeRoute_eq_hostRoute (eval : Atom → Multiset Atom) (body : List Atom → Multiset Atom)
    (rows : List (Ty String)) (args : List Atom) (noRaw : ¬ RawDemand rows) :
    nativeRoute Γ kind eval body rows args = hostRoute Γ kind eval body rows args := by
  unfold nativeRoute hostRoute typedCall
  split_ifs with h0
  · rfl
  · rw [Multiset.bind_bind]
    refine Multiset.bind_congr fun τ hτ => ?_
    have hτ' : τ ∈ rows := dedupAlpha_subset rows τ (Multiset.mem_coe.mp hτ)
    by_cases len : (params τ).length = args.length
    · rw [deliver_of_no_raw eval (params τ) args len fun A hA hraw => noRaw ⟨τ, hτ', A, hA, hraw⟩]
    · rw [Multiset.bind_congr (g := fun _ => 0) fun vs hvs =>
        chainCall_of_params_length Γ kind body τ vs (by rw [evalArgs_length eval args vs hvs]; exact len),
        Multiset.bind_zero, deliver_of_length_ne eval _ _ len, Multiset.zero_bind]

/-- **The per-call decision observes the host route**: a call whose callee has an
`Atom` parameter takes the host route, every other call the native route, and
the answers are the host route's. -/
theorem perCall_observes (eval : Atom → Multiset Atom) (body : List Atom → Multiset Atom)
    (rows : List (Ty String)) (args : List Atom) :
    (if RawDemand rows then hostRoute Γ kind eval body rows args
      else nativeRoute Γ kind eval body rows args) = hostRoute Γ kind eval body rows args := by
  split_ifs with h
  · rfl
  · exact nativeRoute_eq_hostRoute Γ kind eval body rows args h

end Routes

/-! ## Per call against program-wide -/

section Cost

open Mettapedia.Machines.AdmissionRewriting.LocalDeclines

variable {ι H : Type}

/-- **Per-call admission**: a call runs natively unless its callee's rows have an
`Atom` parameter; a callee without declarations runs natively. The decision
reads the callee's declarations only. -/
def perCall (head : ι → H) : SiteAdmission ι H (List (Ty String)) where
  head := head
  admit od _ := match od with
    | some rows => !decide (RawDemand rows)
    | none => true
  check _ _ := 0

/-- **The program-wide rule** being replaced: every call through a variable
takes the host route once any declared head has an `Atom` parameter. -/
def programWide (declared : List H) (Γd : Mettapedia.Machines.AdmissionRewriting.LocalDeclines.Decls H (List (Ty String))) : Bool :=
  declared.all fun f => match Γd f with
    | some rows => !decide (RawDemand rows)
    | none => true

variable {σf σg : Type}

/-- **Deciding per call never costs more than the program-wide rule.** -/
theorem perCall_le_programWide (head : ι → H) (E : Engines ι σf σg) (declared : List H)
    (sites : List ι) (cf cg : ι → ℕ) (Γd : Mettapedia.Machines.AdmissionRewriting.LocalDeclines.Decls H (List (Ty String)))
    (hle : ∀ i, (perCall head).adm Γd i = true → cf i ≤ cg i) (run : List ι)
    (hsub : ∀ i ∈ run, i ∈ sites) :
    localCost (perCall head) E cf cg Γd run ≤
      wholeCost (perCall head) (programWide declared) sites cf cg Γd run :=
  localCost_le_wholeCost (perCall head) E (programWide declared) sites cf cg Γd
    (fun i h => by simpa [SiteAdmission.cost, perCall] using hle i h) run hsub

/-- **A declaration of a head no call reaches costs nothing per call**, while the
program-wide rule can host every call for it. -/
theorem perCall_uncalled [DecidableEq H] (head : ι → H) (E : Engines ι σf σg) (cf cg : ι → ℕ)
    (Γd : Mettapedia.Machines.AdmissionRewriting.LocalDeclines.Decls H (List (Ty String))) (f : H) (od : Option (List (Ty String))) (run : List ι)
    (uncalled : ∀ i ∈ run, head i ≠ f) :
    localCost (perCall head) E cf cg (Function.update Γd f od) run =
      localCost (perCall head) E cf cg Γd run :=
  type_neutral_unexecuted (perCall head) E cf cg Γd f od run uncalled

/-- **The per-call tier observes the general engine**, whatever it admits
(`LocalDeclines.local_observes`). -/
theorem perCall_observes_general (head : ι → H) (E : Engines ι σf σg)
    (Γd : Mettapedia.Machines.AdmissionRewriting.LocalDeclines.Decls H (List (Ty String)))
    (run : List ι) (s : σf) :
    Mettapedia.Machines.TierDeoptimization.runTiered (tierOf E ((perCall head).adm Γd)) run s =
      Mettapedia.Machines.TierDeoptimization.runGen (tierOf E ((perCall head).adm Γd)) run (E.enc s) :=
  local_observes E _ run s

/-- **A declaration without an `Atom` parameter costs nothing per call**: the
calls of its head stay native (`LocalDeclines.type_monotone`, with no checks). -/
theorem perCall_type_monotone [DecidableEq H] (head : ι → H) (E : Engines ι σf σg) (cf cg : ι → ℕ)
    (hfg : ∀ i, cf i ≤ cg i)
    (Γd : Mettapedia.Machines.AdmissionRewriting.LocalDeclines.Decls H (List (Ty String)))
    (f : H) (rows : List (Ty String)) (undeclared : Γd f = none) (noRaw : ¬ RawDemand rows)
    (run : List ι) :
    localCost (perCall head) E cf cg (Function.update Γd f (some rows)) run ≤
      localCost (perCall head) E cf cg Γd run := by
  have := type_monotone (perCall head) E cf cg hfg Γd f rows undeclared (fun _ => rfl)
    (fun i _ _ => by simp [perCall, noRaw]) run
  simpa [perCall] using this

end Cost

/-! ## Controls -/

namespace Controls

open Mettapedia.Machines.AdmissionRewriting.LocalDeclines
open TypedCalls.Controls (decls num sym)

/-- `(: q (-> Atom Atom))`. -/
abbrev quoteRow : Ty String := arrow [.sym "Atom"] (.sym "Atom")

/-- **Raw delivery**: `q`, declared `(-> Atom Atom)`, receives `(+ 1 0)` as written,
not its value, as in the probe `sem_dyn`. -/
theorem raw_delivery (eval : Atom → Multiset Atom) :
    deliver eval (params quoteRow) [.expression [sym "+", num 1, num 0]] =
      {[.expression [sym "+", num 1, num 0]]} := by
  simp [deliver, params, quoteRow, demand]

theorem quote_raw : RawDemand [quoteRow] := ⟨quoteRow, by simp, .sym "Atom", by simp [params], by
  simp [demand]⟩

/-- A lambda has no declarations: its arguments are evaluated, natively. -/
theorem lambda_evaluates (Γ : Decls) (kind : Atom → String) (eval : Atom → Multiset Atom)
    (body : List Atom → Multiset Atom) (args : List Atom) :
    nativeRoute Γ kind eval body [] args = (evalArgs eval args).bind body ∧ ¬ RawDemand [] := by
  refine ⟨by simp [nativeRoute], ?_⟩
  rintro ⟨τ, hτ, -⟩
  exact absurd hτ List.not_mem_nil

/-- The heads of the lambda loop: the loop, the lambda it calls, and an uncalled
`quoteit`. -/
inductive LoopHead where
  | loop
  | lambda
  | quoteit
  deriving DecidableEq

/-- The steps of the lambda loop. -/
inductive LoopStep where
  | loop
  | callee
  deriving DecidableEq

def headOf : LoopStep → LoopHead
  | .loop => .loop
  | .callee => .lambda

/-- Three iterations of the loop, each calling the lambda through a variable. -/
def run : List LoopStep := [.loop, .callee, .loop, .callee, .loop, .callee]

/-- `(: quoteit (-> Atom Atom))`, never called; nothing else is declared. -/
def quoteitDecls : Mettapedia.Machines.AdmissionRewriting.LocalDeclines.Decls LoopHead (List (Ty String)) :=
  fun h => if h = .quoteit then some [quoteRow] else none

def engines : Engines LoopStep Unit Unit where
  gen := fun _ _ => ()
  fast := fun _ _ => ()
  enc := id
  dec := some
  sim := fun _ _ => rfl
  dec_enc := fun _ _ h => (Option.some.inj h).symm

/-- **The lambda loop**: per call it runs natively, 6 units; the program-wide rule
hosts every call for the uncalled `quoteit`, 180 units, as `lam_quoteit_10000`
went from the plain loop's cost to 329M. -/
theorem lambda_loop :
    localCost (perCall headOf) engines (fun _ => 1) (fun _ => 30) quoteitDecls run = 6 ∧
      wholeCost (perCall headOf) (programWide [LoopHead.loop, LoopHead.lambda, LoopHead.quoteit])
        [.loop, .callee] (fun _ => 1) (fun _ => 30) quoteitDecls run = 180 := by
  have noRaw : ¬ RawDemand ([] : List (Ty String)) := by
    rintro ⟨τ, hτ, -⟩
    exact absurd hτ List.not_mem_nil
  constructor
  · rw [localCost_eq]
    simp [run, SiteAdmission.adm, SiteAdmission.cost, perCall, headOf, quoteitDecls]
  · have refused : programWide [LoopHead.loop, LoopHead.lambda, LoopHead.quoteit] quoteitDecls = false := by
      simp [programWide, quoteitDecls, quote_raw]
    simp [wholeCost, refused, run]

end Controls

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls
