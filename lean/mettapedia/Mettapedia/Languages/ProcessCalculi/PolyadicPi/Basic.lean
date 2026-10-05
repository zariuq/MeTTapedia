import Mettapedia.OSLF.Syntax.ContextualRootEvents
import Mettapedia.OSLF.Syntax.BinderExchange

/-!
# The unary/binary asynchronous pi fragment of Native Type Theory

Example 31 and Proposition 32 of Williams and Stay use two arities of
communication, unary fetches and binary calls. Here their arities are part of
the shared binding signature; a binary receiver opens both names together.
This fragment is not identified with the one-sort, monadic `piCalc`.

Both communication schemas are authored as intrinsic rewrite rules. The
context-indexed operational relation below adds precisely parallel and
restriction descent. The separate static relation includes unused-scope
elimination, scope extrusion and binder exchange, and guarded replication.
An exact identification with the canonical LanguageDef equation engine
remains separate from this scoped operational interpretation.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi

open Mettapedia.OSLF.Binding

inductive Srt where
  | nm
  | pr
  deriving DecidableEq, Repr

inductive Op : Srt → Type where
  | nil : Op .pr
  | par : Op .pr
  | inp1 : Op .pr
  | inp2 : Op .pr
  | out1 : Op .pr
  | out2 : Op .pr
  | nu : Op .pr
  | rep : Op .pr

abbrev sig : Signature where
  Srt := Srt
  Op := Op
  arity := fun {_} o => match o with
    | .nil => []
    | .par => [([], .pr), ([], .pr)]
    | .inp1 => [([], .nm), ([.nm], .pr)]
    | .inp2 => [([], .nm), ([.nm, .nm], .pr)]
    | .out1 => [([], .nm), ([], .nm)]
    | .out2 => [([], .nm), ([], .nm), ([], .nm)]
    | .nu => [([.nm], .pr)]
    | .rep => [([], .pr)]

abbrev Name (Γ : Ctx sig) := Term sig Γ .nm
abbrev Proc (Γ : Ctx sig) := Term sig Γ .pr

def nil {Γ : Ctx sig} : Proc Γ := .op .nil .nil
def par {Γ : Ctx sig} (p q : Proc Γ) : Proc Γ :=
  .op .par (.cons p (.cons q .nil))
def inp1 {Γ : Ctx sig} (channel : Name Γ) (body : Proc (.nm :: Γ)) : Proc Γ :=
  .op .inp1 (.cons channel (.cons body .nil))
def inp2 {Γ : Ctx sig} (channel : Name Γ) (body : Proc (.nm :: .nm :: Γ)) : Proc Γ :=
  .op .inp2 (.cons channel (.cons body .nil))
def out1 {Γ : Ctx sig} (channel datum : Name Γ) : Proc Γ :=
  .op .out1 (.cons channel (.cons datum .nil))
def out2 {Γ : Ctx sig} (channel first second : Name Γ) : Proc Γ :=
  .op .out2 (.cons channel (.cons first (.cons second .nil)))
def nu {Γ : Ctx sig} (body : Proc (.nm :: Γ)) : Proc Γ :=
  .op .nu (.cons body .nil)
def rep {Γ : Ctx sig} (p : Proc Γ) : Proc Γ := .op .rep (.cons p .nil)

/-- Exchange adjacent private names by the shared sorted binder operation. -/
abbrev swapRen {Γ : Ctx sig} : Ren sig (.nm :: .nm :: Γ) (.nm :: .nm :: Γ) :=
  exchangeRen (S := sig) (Γ := Γ) Srt.nm Srt.nm

@[simp] theorem rename_par {Γ Δ : Ctx sig} (ρ : Ren sig Γ Δ) (p q : Proc Γ) :
    rename ρ (par p q) = par (rename ρ p) (rename ρ q) := rfl
@[simp] theorem rename_inp1 {Γ Δ : Ctx sig} (ρ : Ren sig Γ Δ)
    (n : Name Γ) (body : Proc (.nm :: Γ)) :
    rename ρ (inp1 n body) =
      inp1 (rename ρ n) (rename (liftRen ρ [.nm]) body) := rfl
@[simp] theorem rename_inp2 {Γ Δ : Ctx sig} (ρ : Ren sig Γ Δ)
    (n : Name Γ) (body : Proc (.nm :: .nm :: Γ)) :
    rename ρ (inp2 n body) =
      inp2 (rename ρ n) (rename (liftRen ρ [.nm, .nm]) body) := rfl
@[simp] theorem rename_out1 {Γ Δ : Ctx sig} (ρ : Ren sig Γ Δ) (n a : Name Γ) :
    rename ρ (out1 n a) = out1 (rename ρ n) (rename ρ a) := rfl
@[simp] theorem rename_out2 {Γ Δ : Ctx sig} (ρ : Ren sig Γ Δ) (n a b : Name Γ) :
    rename ρ (out2 n a b) = out2 (rename ρ n) (rename ρ a) (rename ρ b) := rfl
@[simp] theorem rename_nu {Γ Δ : Ctx sig} (ρ : Ren sig Γ Δ)
    (body : Proc (.nm :: Γ)) :
    rename ρ (nu body) = nu (rename (liftRen ρ [.nm]) body) := rfl
@[simp] theorem rename_rep {Γ Δ : Ctx sig} (ρ : Ren sig Γ Δ) (p : Proc Γ) :
    rename ρ (rep p) = rep (rename ρ p) := rfl

/-- Simultaneously open the two receiver binders in their authored order. -/
def pairSub {Γ : Ctx sig} (first second : Name Γ) :
    Sub sig (.nm :: .nm :: Γ) Γ
  | _, .zero => first
  | s, .succ old => extend second s old

def openPair {Γ : Ctx sig} (body : Proc (.nm :: .nm :: Γ))
    (first second : Name Γ) : Proc Γ := bind (pairSub first second) body

/-- Variable-only communication agrees with the shared renaming action. -/
def nameRen {Γ : Ctx sig} (name : Var Γ .nm) : Ren sig (.nm :: Γ) Γ
  | _, .zero => name
  | _, .succ old => old

def pairRen {Γ : Ctx sig} (first second : Var Γ .nm) :
    Ren sig (.nm :: .nm :: Γ) Γ
  | _, .zero => first
  | s, .succ old => nameRen second s old

theorem openPair_variables {Γ : Ctx sig} (body : Proc (.nm :: .nm :: Γ))
    (first second : Var Γ .nm) :
    openPair body (.var first) (.var second) = rename (pairRen first second) body := by
  unfold openPair
  have environments : pairSub (.var first) (.var second) =
      (fun s x => Term.var (pairRen first second s x)) := by
    funext s x
    cases x with
    | zero => rfl
    | succ x => cases x <;> rfl
  rw [environments, bind_var_eq_rename]

theorem rename_openPair {Γ Δ : Ctx sig} (ρ : Ren sig Γ Δ)
    (body : Proc (.nm :: .nm :: Γ)) (first second : Name Γ) :
    rename ρ (openPair body first second) =
      openPair (rename (liftRen ρ [.nm, .nm]) body)
        (rename ρ first) (rename ρ second) := by
  simp only [openPair, rename_bind, bind_rename]
  congr 1
  funext sort x
  cases x with
  | zero => rfl
  | succ x => cases x <;> rfl

abbrev metas : List (MetaArity sig) :=
  [([Srt.nm], Srt.pr), ([Srt.nm, Srt.nm], Srt.pr)]
abbrev schemaSig : Signature := withMetas sig metas

def unaryContinuation {Γ : Ctx schemaSig} (argument : Term schemaSig Γ .nm) :
    Term schemaSig Γ .pr :=
  .op (Sum.inr (MetaOp.mk (M := metas) 0)) (.cons argument .nil)

def binaryContinuation {Γ : Ctx schemaSig}
    (first second : Term schemaSig Γ .nm) : Term schemaSig Γ .pr :=
  .op (Sum.inr (MetaOp.mk (M := metas) 1)) (.cons first (.cons second .nil))

def comm1 : UnpositionedRewrite schemaSig where
  ctx := [.nm, .nm]
  sort := .pr
  lhs := .op (.inl .par)
    (.cons
      (.op (.inl .out1) (.cons (.var .zero) (.cons (.var (.succ .zero)) .nil)))
      (.cons (.op (.inl .inp1)
        (.cons (.var .zero) (.cons (unaryContinuation (.var .zero)) .nil))) .nil))
  rhs := unaryContinuation (.var (.succ .zero))

def comm2 : UnpositionedRewrite schemaSig where
  ctx := [.nm, .nm, .nm]
  sort := .pr
  lhs := .op (.inl .par)
    (.cons
      (.op (.inl .out2) (.cons (.var .zero)
        (.cons (.var (.succ .zero)) (.cons (.var (.succ (.succ .zero))) .nil))))
      (.cons (.op (.inl .inp2)
        (.cons (.var .zero)
          (.cons (binaryContinuation (.var .zero) (.var (.succ .zero))) .nil))) .nil))
  rhs := binaryContinuation (.var (.succ .zero)) (.var (.succ (.succ .zero)))

/-- Commutativity of parallel composition, with arbitrary process arguments. -/
def eqParComm : EqAxiom sig metas where
  ctx := [.pr, .pr]
  sort := .pr
  lhs := .op (.inl .par) (.cons (.var .zero) (.cons (.var (.succ .zero)) .nil))
  rhs := .op (.inl .par) (.cons (.var (.succ .zero)) (.cons (.var .zero) .nil))

/-- Associativity retains each of the three selected processes. -/
def eqParAssoc : EqAxiom sig metas where
  ctx := [.pr, .pr, .pr]
  sort := .pr
  lhs := .op (.inl .par)
    (.cons (.op (.inl .par) (.cons (.var .zero) (.cons (.var (.succ .zero)) .nil)))
      (.cons (.var (.succ (.succ .zero))) .nil))
  rhs := .op (.inl .par) (.cons (.var .zero)
    (.cons (.op (.inl .par)
      (.cons (.var (.succ .zero)) (.cons (.var (.succ (.succ .zero))) .nil))) .nil))

def eqParUnit : EqAxiom sig metas where
  ctx := [.pr]
  sort := .pr
  lhs := .op (.inl .par) (.cons (.var .zero) (.cons (.op (.inl .nil) .nil) .nil))
  rhs := .var .zero

/-- The process argument is outside the eliminated private-name binder. -/
def eqNuUnused : EqAxiom sig metas where
  ctx := [.pr]
  sort := .pr
  lhs := .op (.inl .nu) (.cons (.var (.succ .zero)) .nil)
  rhs := .var .zero

/-- Extrusion supplies the private name only to the dependent process;
the parallel frame remains outside its scope in the schema. -/
def eqNuPar : EqAxiom sig metas where
  ctx := [.pr]
  sort := .pr
  lhs := .op (.inl .par)
    (.cons (.op (.inl .nu) (.cons (unaryContinuation (.var .zero)) .nil))
      (.cons (.var .zero) .nil))
  rhs := .op (.inl .nu)
    (.cons (.op (.inl .par)
      (.cons (unaryContinuation (.var .zero)) (.cons (.var (.succ .zero)) .nil))) .nil)

/-- Exchange private binders by exchanging the arguments of the dependent
metavariable, rather than by a raw permutation of its body. -/
def eqNuSwap : EqAxiom sig metas where
  ctx := []
  sort := .pr
  lhs := .op (.inl .nu) (.cons (.op (.inl .nu)
    (.cons (binaryContinuation (.var .zero) (.var (.succ .zero))) .nil)) .nil)
  rhs := .op (.inl .nu) (.cons (.op (.inl .nu)
    (.cons (binaryContinuation (.var (.succ .zero)) (.var .zero)) .nil)) .nil)

def eqRepUnfold : EqAxiom sig metas where
  ctx := [.pr]
  sort := .pr
  lhs := .op (.inl .rep) (.cons (.var .zero) .nil)
  rhs := .op (.inl .par) (.cons (.var .zero)
    (.cons (.op (.inl .rep) (.cons (.var .zero) .nil)) .nil))

def equations : List (EqAxiom sig metas) :=
  [eqParComm, eqParAssoc, eqParUnit, eqNuUnused, eqNuPar, eqNuSwap, eqRepUnfold]

def presentation : UnpositionedPresentation sig where
  metas := metas
  eqs := equations
  rules := [comm1, comm2]

/-- The contextual directed operational relation, prior to scope equations. -/
inductive Step : {Γ : Ctx sig} → Proc Γ → Proc Γ → Prop where
  | comm1 {Γ} (channel datum : Name Γ) (body : Proc (.nm :: Γ)) :
      Step (par (out1 channel datum) (inp1 channel body)) (inst body datum)
  | comm2 {Γ} (channel first second : Name Γ) (body : Proc (.nm :: .nm :: Γ)) :
      Step (par (out2 channel first second) (inp2 channel body))
        (openPair body first second)
  | parL {Γ} {p p' : Proc Γ} (q : Proc Γ) : Step p p' → Step (par p q) (par p' q)
  | parR {Γ} (p : Proc Γ) {q q' : Proc Γ} : Step q q' → Step (par p q) (par p q')
  | nu {Γ} {p p' : Proc (.nm :: Γ)} : Step p p' → Step (nu p) (nu p')

/-- The target structural equations needed by the displayed translation. -/
inductive StructuralEq : {Γ : Ctx sig} → Proc Γ → Proc Γ → Prop where
  | refl {Γ} (p : Proc Γ) : StructuralEq p p
  | symm {Γ} {p q : Proc Γ} : StructuralEq p q → StructuralEq q p
  | trans {Γ} {p q r : Proc Γ} : StructuralEq p q → StructuralEq q r → StructuralEq p r
  | parComm {Γ} (p q : Proc Γ) : StructuralEq (par p q) (par q p)
  | parAssoc {Γ} (p q r : Proc Γ) : StructuralEq (par (par p q) r) (par p (par q r))
  | parUnit {Γ} (p : Proc Γ) : StructuralEq (par p nil) p
  | nuUnused {Γ} (p : Proc Γ) : StructuralEq (nu (weaken p)) p
  | nuPar {Γ} (p : Proc (.nm :: Γ)) (q : Proc Γ) :
      StructuralEq (par (nu p) q) (nu (par p (weaken q)))
  | nuSwap {Γ} (p : Proc (.nm :: .nm :: Γ)) :
      StructuralEq (nu (nu p)) (nu (nu (rename swapRen p)))
  | repUnfold {Γ} (p : Proc Γ) : StructuralEq (rep p) (par p (rep p))
  | par {Γ} {p p' q q' : Proc Γ} :
      StructuralEq p p' → StructuralEq q q' → StructuralEq (par p q) (par p' q')
  | nu {Γ} {p p' : Proc (.nm :: Γ)} : StructuralEq p p' → StructuralEq (nu p) (nu p')
  | inp1 {Γ} (channel : Name Γ) {p p' : Proc (.nm :: Γ)} :
      StructuralEq p p' → StructuralEq (inp1 channel p) (inp1 channel p')
  | inp2 {Γ} (channel : Name Γ) {p p' : Proc (.nm :: .nm :: Γ)} :
      StructuralEq p p' → StructuralEq (inp2 channel p) (inp2 channel p')
  | rep {Γ} {p p' : Proc Γ} : StructuralEq p p' → StructuralEq (rep p) (rep p')

/-- Scope equations remain valid under simultaneous name reindexing;
fresh binders are fixed and exchanged with their actual positions. -/
theorem StructuralEq.rename {Γ Δ : Ctx sig} (ρ : Ren sig Γ Δ)
    {first second : Proc Γ} (equal : StructuralEq first second) :
    StructuralEq (Mettapedia.OSLF.Binding.rename ρ first) (Mettapedia.OSLF.Binding.rename ρ second) := by
  induction equal generalizing Δ with
  | refl process => exact .refl _
  | symm _ ih => exact .symm (ih ρ)
  | trans _ _ firstIH secondIH => exact .trans (firstIH ρ) (secondIH ρ)
  | parComm first second => exact .parComm _ _
  | parAssoc first second third => exact .parAssoc _ _ _
  | parUnit process => exact .parUnit _
  | nuUnused process =>
      change StructuralEq (Mettapedia.Languages.ProcessCalculi.PolyadicPi.nu (Mettapedia.OSLF.Binding.rename (liftRen ρ [.nm]) (weaken process)))
        (Mettapedia.OSLF.Binding.rename ρ process)
      rw [Mettapedia.OSLF.Binding.rename_weaken (fresh := Srt.nm) ρ process]
      exact .nuUnused _
  | nuPar process frame =>
      change StructuralEq (Mettapedia.Languages.ProcessCalculi.PolyadicPi.par (Mettapedia.Languages.ProcessCalculi.PolyadicPi.nu (Mettapedia.OSLF.Binding.rename (liftRen ρ [.nm]) process)) (Mettapedia.OSLF.Binding.rename ρ frame))
        (Mettapedia.Languages.ProcessCalculi.PolyadicPi.nu (Mettapedia.Languages.ProcessCalculi.PolyadicPi.par (Mettapedia.OSLF.Binding.rename (liftRen ρ [.nm]) process)
          (Mettapedia.OSLF.Binding.rename (liftRen ρ [.nm]) (weaken frame))))
      rw [Mettapedia.OSLF.Binding.rename_weaken (fresh := Srt.nm) ρ frame]
      exact .nuPar _ _
  | nuSwap process =>
      simp only [rename_nu, liftRen_two]
      change StructuralEq (Mettapedia.Languages.ProcessCalculi.PolyadicPi.nu (Mettapedia.Languages.ProcessCalculi.PolyadicPi.nu (Mettapedia.OSLF.Binding.rename (liftRen ρ [.nm, .nm]) process)))
        (Mettapedia.Languages.ProcessCalculi.PolyadicPi.nu (Mettapedia.Languages.ProcessCalculi.PolyadicPi.nu (Mettapedia.OSLF.Binding.rename (liftRen ρ [.nm, .nm]) (Mettapedia.OSLF.Binding.rename swapRen process))))
      rw [Mettapedia.OSLF.Binding.rename_exchange_lift ρ Srt.nm Srt.nm process]
      exact .nuSwap _
  | repUnfold process => exact .repUnfold _
  | par _ _ firstIH secondIH => exact .par (firstIH ρ) (secondIH ρ)
  | nu _ ih => exact .nu (ih (liftRen ρ [.nm]))
  | inp1 channel _ ih => exact .inp1 _ (ih (liftRen ρ [.nm]))
  | inp2 channel _ ih => exact .inp2 _ (ih (liftRen ρ [.nm, .nm]))
  | rep _ ih => exact .rep (ih ρ)

/-- One actual communication/descent, with structural changes at its endpoints. -/
def StepModulo {Γ : Ctx sig} (p q : Proc Γ) : Prop :=
  ∃ source target, StructuralEq p source ∧ Step source target ∧ StructuralEq target q

theorem Step.toModulo {Γ : Ctx sig} {p q : Proc Γ} (step : Step p q) : StepModulo p q :=
  ⟨p, q, .refl p, step, .refl q⟩

/-- Communication and active descent commute with sorted name reindexing. -/
theorem Step.rename {Γ Δ : Ctx sig} (ρ : Ren sig Γ Δ)
    {first second : Proc Γ} (step : Step first second) :
    Step (Mettapedia.OSLF.Binding.rename ρ first)
      (Mettapedia.OSLF.Binding.rename ρ second) := by
  induction step generalizing Δ with
  | comm1 channel datum body =>
      simpa only [rename_par, rename_out1, rename_inp1, rename_inst] using
        Step.comm1 (Mettapedia.OSLF.Binding.rename ρ channel)
          (Mettapedia.OSLF.Binding.rename ρ datum)
          (Mettapedia.OSLF.Binding.rename (liftRen ρ [.nm]) body)
  | comm2 channel first second body =>
      simpa only [rename_par, rename_out2, rename_inp2, rename_openPair] using
        Step.comm2 (Mettapedia.OSLF.Binding.rename ρ channel)
          (Mettapedia.OSLF.Binding.rename ρ first)
          (Mettapedia.OSLF.Binding.rename ρ second)
          (Mettapedia.OSLF.Binding.rename (liftRen ρ [.nm, .nm]) body)
  | parL frame _ ih => exact .parL _ (ih ρ)
  | parR frame _ ih => exact .parR _ (ih ρ)
  | nu _ ih => exact .nu (ih (liftRen ρ [.nm]))

theorem StepModulo.rename {Γ Δ : Ctx sig} (ρ : Ren sig Γ Δ)
    {first second : Proc Γ} (step : StepModulo first second) :
    StepModulo (Mettapedia.OSLF.Binding.rename ρ first)
      (Mettapedia.OSLF.Binding.rename ρ second) := by
  obtain ⟨source, target, before, firing, after⟩ := step
  exact ⟨_, _, before.rename ρ, firing.rename ρ, after.rename ρ⟩

/-- A supplied unary redex has exactly its instantiated continuation as endpoint. -/
theorem unary_communication_iff {Γ : Ctx sig} (channel datum : Name Γ)
    (body : Proc (.nm :: Γ)) (endpoint : Proc Γ) :
    Step (par (out1 channel datum) (inp1 channel body)) endpoint ↔
      endpoint = inst body datum := by
  constructor
  · intro step
    cases step with
    | comm1 => rfl
    | parL _ impossible => cases impossible
    | parR _ impossible => cases impossible
  · rintro rfl
    exact .comm1 _ _ _

theorem binary_communication_iff {Γ : Ctx sig} (channel first second : Name Γ)
    (body : Proc (.nm :: .nm :: Γ)) (endpoint : Proc Γ) :
    Step (par (out2 channel first second) (inp2 channel body)) endpoint ↔
      endpoint = openPair body first second := by
  constructor
  · intro step
    cases step with
    | comm2 => rfl
    | parL _ impossible => cases impossible
    | parR _ impossible => cases impossible
  · rintro rfl
    exact .comm2 _ _ _ _

theorem mismatched_unary_channel_no_step {Γ : Ctx sig}
    (channel other datum : Name Γ) (different : channel ≠ other)
    (body : Proc (.nm :: Γ)) {endpoint : Proc Γ} :
    ¬ Step (par (out1 channel datum) (inp1 other body)) endpoint := by
  intro step
  cases step with
  | comm1 => exact different rfl
  | parL _ impossible => cases impossible
  | parR _ impossible => cases impossible

theorem nil_no_step {Γ : Ctx sig} {target : Proc Γ} : ¬ Step nil target := by
  intro step
  cases step

/-- Unary and binary communication cannot accidentally consume each other. -/
theorem mismatched_arity_no_step {Γ : Ctx sig} (channel datum : Name Γ)
    (body : Proc (.nm :: .nm :: Γ)) {target : Proc Γ} :
    ¬ Step (par (out1 channel datum) (inp2 channel body)) target := by
  intro step
  cases step with
  | parL q impossible => cases impossible
  | parR p impossible => cases impossible

end Mettapedia.Languages.ProcessCalculi.PolyadicPi
