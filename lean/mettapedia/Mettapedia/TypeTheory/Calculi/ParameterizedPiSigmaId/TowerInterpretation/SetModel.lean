import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Annotated.Judgment
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Models.ZFSetReplayUniverseModel
import Mettapedia.Logic.HOL.Embedding.ZFSetTraceProofDecoding
import Mettapedia.SetTheory.ZFSet.OrderedPair

/-!
# The set interpretation of annotated terms

The candidate calculus writes a λ-abstraction without its domain, so a set
value cannot be read off a term: `λ x. x` denotes a different graph at every
domain. The annotated terms `Annotated.CTm` record the domain of every
abstraction. Every annotated term has a value in `ZFSet` at every environment
of values for its free variables (`ev`), given sets for the universe heads and
for the declared constants:

* a dependent function type is the set of Aczel traces of the dependent
  functions (`tracePiSet`), an abstraction the trace of its graph over the
  value of its domain, and application reads the trace at the argument;
* a dependent pair type is the set of Kuratowski pairs (`sigmaSet`), with the
  two projections of `ZFSetOrderedPair`;
* an identity type is the truth value of the equality of its endpoints
  (`truthCode`), a subset of `{∅}`, and reflexivity is `∅`.

The interpretation reads renaming and substitution as precomposition
(`ev_rename`, `ev_subst`, `ev_inst0`, `ev_liftClosed`). A context is
satisfied by an environment when every variable lies in the value of its type
(`Sat`); extending a context extends its environments (`sat_snoc`).

The set facts the soundness proof uses are proved here: trace functions are
determined by their values on the domain (`tracePiSet_ext`), products are
monotone in their fibres (`tracePiSet_mono`, `sigmaSet_mono`), pairs are
determined by their projections (`sigmaSet_ext`). Outside its domain a trace
function gives the empty set (`traceApp_eq_empty_of_not_mem`).

`replacement` (through `ZFSet.image` with `Classical.allZFSetDefinable`) is
the source of `Classical.choice` in this module; every set value built with a
graph, a family union or a trace product depends on it.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TowerInterpretation

open Presentation Presentation.TypedEquality.Annotated
open Mettapedia.Logic.HOL.Embedding
open ZFSetDependentProducts (graph sigmaSet piSet familyUnion mem_sigmaSet mem_piSet
  graph_mem_piSet mem_graph pair_mem_graph mem_familyUnion)
open ZFSetTraceProducts (traceLam traceApp tracePiSet mem_tracePiSet mem_traceApp mem_traceLam
  traceApp_graph_beta traceApp_mem)
open ZFSetTraceProofDecoding (truthCode mem_truthCode truthCode_subset)
open Mettapedia.SetTheory

universe u

variable {Head : Type}

/-! ## Environments -/

/-- Values of the free variables. -/
abbrev Env (n : Nat) := Fin n → ZFSet.{u}

/-- Extend an environment by a value for the new variable `0`. -/
def extend {n : Nat} (ρ : Env.{u} n) (x : ZFSet.{u}) : Env.{u} (n + 1) :=
  Fin.cases (motive := fun _ => ZFSet.{u}) x ρ

@[simp] theorem extend_zero {n : Nat} (ρ : Env.{u} n) (x : ZFSet.{u}) : extend ρ x 0 = x := rfl

@[simp] theorem extend_succ {n : Nat} (ρ : Env.{u} n) (x : ZFSet.{u}) (i : Fin n) :
    extend ρ x i.succ = ρ i := rfl

theorem extend_comp_succ {n : Nat} (ρ : Env.{u} n) (x : ZFSet.{u}) :
    extend ρ x ∘ Fin.succ = ρ := rfl

theorem extend_comp_liftRen {n m : Nat} (ρ : Env.{u} m) (r : Ren n m) (x : ZFSet.{u}) :
    extend ρ x ∘ liftRen r = extend (ρ ∘ r) x := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · rfl
  · rfl

/-! ## The interpretation -/

section Interpretation

variable (heads : Head → ZFSet.{u}) (consts : DeclName → ZFSet.{u})

/-- The value of an annotated term at an environment. -/
noncomputable def ev : {n : Nat} → CTm Head n → Env.{u} n → ZFSet.{u}
  | _, .var i, ρ => ρ i
  | _, .const c, _ => consts c
  | _, .head h, _ => heads h
  | _, .pi A B, ρ => tracePiSet (ev A ρ) (fun x => ev B (extend ρ x))
  | _, .sigma A B, ρ => sigmaSet (ev A ρ) (fun x => ev B (extend ρ x))
  | _, .id _ a b, ρ => truthCode (ev a ρ = ev b ρ)
  | _, .lam A body, ρ => traceLam (graph (ev A ρ) (fun x => ev body (extend ρ x)))
  | _, .app f a, ρ => traceApp (ev f ρ) (ev a ρ)
  | _, .pair a b, ρ => ZFSet.pair (ev a ρ) (ev b ρ)
  | _, .fst p, ρ => ZFSetOrderedPair.first (ev p ρ)
  | _, .snd p, ρ => ZFSetOrderedPair.second (ev p ρ)
  | _, .refl _, _ => ∅

/-- Renaming is precomposition of the environment. -/
theorem ev_rename {n m : Nat} (r : Ren n m) (t : CTm Head n) (ρ : Env.{u} m) :
    ev heads consts (t.rename r) ρ = ev heads consts t (ρ ∘ r) := by
  induction t generalizing m with
  | var i => rfl
  | const c => rfl
  | head h => rfl
  | pi A B ihA ihB =>
      simp only [CTm.rename, ev, ihA]
      congr 1
      funext x
      rw [ihB, extend_comp_liftRen]
  | sigma A B ihA ihB =>
      simp only [CTm.rename, ev, ihA]
      congr 1
      funext x
      rw [ihB, extend_comp_liftRen]
  | id A a b _ iha ihb => simp only [CTm.rename, ev, iha, ihb]
  | lam A body ihA ihBody =>
      simp only [CTm.rename, ev, ihA]
      congr 2
      funext x
      rw [ihBody, extend_comp_liftRen]
  | app f a ihf iha => simp only [CTm.rename, ev, ihf, iha]
  | pair a b iha ihb => simp only [CTm.rename, ev, iha, ihb]
  | fst p ih => simp only [CTm.rename, ev, ih]
  | snd p ih => simp only [CTm.rename, ev, ih]
  | refl a _ => rfl

/-- Weakening is invisible to the extended environment. -/
theorem ev_rename_wk {n : Nat} (t : CTm Head n) (ρ : Env.{u} n) (x : ZFSet.{u}) :
    ev heads consts (t.rename wk) (extend ρ x) = ev heads consts t ρ := by
  rw [ev_rename]
  rfl

theorem ev_liftSub {n m : Nat} (σ : CSub Head n m) (ρ : Env.{u} m) (x : ZFSet.{u}) :
    (fun i => ev heads consts (CTm.liftSub σ i) (extend ρ x)) =
      extend (fun i => ev heads consts (σ i) ρ) x := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · rfl
  · exact ev_rename_wk heads consts (σ j) ρ x

/-- Substitution is evaluation of the substituted terms. -/
theorem ev_subst {n m : Nat} (σ : CSub Head n m) (t : CTm Head n) (ρ : Env.{u} m) :
    ev heads consts (t.subst σ) ρ = ev heads consts t (fun i => ev heads consts (σ i) ρ) := by
  induction t generalizing m with
  | var i => rfl
  | const c => rfl
  | head h => rfl
  | pi A B ihA ihB =>
      simp only [CTm.subst, ev, ihA]
      congr 1
      funext x
      rw [ihB, ev_liftSub]
  | sigma A B ihA ihB =>
      simp only [CTm.subst, ev, ihA]
      congr 1
      funext x
      rw [ihB, ev_liftSub]
  | id A a b _ iha ihb => simp only [CTm.subst, ev, iha, ihb]
  | lam A body ihA ihBody =>
      simp only [CTm.subst, ev, ihA]
      congr 2
      funext x
      rw [ihBody, ev_liftSub]
  | app f a ihf iha => simp only [CTm.subst, ev, ihf, iha]
  | pair a b iha ihb => simp only [CTm.subst, ev, iha, ihb]
  | fst p ih => simp only [CTm.subst, ev, ih]
  | snd p ih => simp only [CTm.subst, ev, ih]
  | refl a _ => rfl

/-- Opening a binder is extending the environment by the argument's value. -/
theorem ev_inst0 {n : Nat} (a : CTm Head n) (body : CTm Head (n + 1)) (ρ : Env.{u} n) :
    ev heads consts (CTm.inst0 a body) ρ =
      ev heads consts body (extend ρ (ev heads consts a ρ)) := by
  rw [CTm.inst0, ev_subst]
  congr 1
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · rfl
  · rfl

/-- A lifted closed term has its closed value. -/
theorem ev_liftClosed {n : Nat} (t : CTm Head 0) (ρ : Env.{u} n) :
    ev heads consts (CTm.liftClosed t) ρ = ev heads consts t Fin.elim0 := by
  rw [CTm.liftClosed, ev_rename]
  congr 1
  funext i
  exact i.elim0

/-- **Changing the heads of a term before interpreting it is interpreting it with the heads
changed.** -/
theorem ev_mapHead {Head' : Type} (g : Head' → Head) {n : Nat} (t : CTm Head' n)
    (ρ : Env.{u} n) :
    ev heads consts (t.mapHead g) ρ = ev (fun h => heads (g h)) consts t ρ := by
  induction t with
  | var i => rfl
  | const c => rfl
  | head h => rfl
  | pi A B ihA ihB => simp only [CTm.mapHead, ev, ihA, ihB]
  | sigma A B ihA ihB => simp only [CTm.mapHead, ev, ihA, ihB]
  | id A a b _ iha ihb => simp only [CTm.mapHead, ev, iha, ihb]
  | lam A b ihA ihb => simp only [CTm.mapHead, ev, ihA, ihb]
  | app f a ihf iha => simp only [CTm.mapHead, ev, ihf, iha]
  | pair a b iha ihb => simp only [CTm.mapHead, ev, iha, ihb]
  | fst p ih => simp only [CTm.mapHead, ev, ih]
  | snd p ih => simp only [CTm.mapHead, ev, ih]
  | refl a _ => simp only [CTm.mapHead, ev]

/-! ## Contexts -/

/-- An environment satisfies a context when each variable lies in the value
of its type. -/
def Sat {n : Nat} (Γ : CCtx Head n) (ρ : Env.{u} n) : Prop :=
  ∀ i, ρ i ∈ ev heads consts (Γ.lookup i) ρ

theorem sat_nil (ρ : Env.{u} 0) : Sat heads consts (.nil : CCtx Head 0) ρ :=
  fun i => i.elim0

theorem sat_snoc {n : Nat} {Γ : CCtx Head n} {A : CTm Head n} {ρ : Env.{u} n} {x : ZFSet.{u}} :
    Sat heads consts (Γ.snoc A) (extend ρ x) ↔ Sat heads consts Γ ρ ∧ x ∈ ev heads consts A ρ := by
  constructor
  · intro sat
    refine ⟨fun j => ?_, ?_⟩
    · have := sat j.succ
      change ρ j ∈ ev heads consts ((Γ.lookup j).rename wk) (extend ρ x) at this
      rwa [ev_rename_wk] at this
    · have := sat 0
      change x ∈ ev heads consts (A.rename wk) (extend ρ x) at this
      rwa [ev_rename_wk] at this
  · rintro ⟨sat, hx⟩ i
    refine Fin.cases ?_ (fun j => ?_) i
    · change x ∈ ev heads consts (A.rename wk) (extend ρ x)
      rwa [ev_rename_wk]
    · change ρ j ∈ ev heads consts ((Γ.lookup j).rename wk) (extend ρ x)
      rw [ev_rename_wk]
      exact sat j

end Interpretation

/-! ## Set facts used by the soundness proof -/

/-- A graph depends only on the values on its domain. -/
theorem graph_congr {a : ZFSet.{u}} {f g : ZFSet.{u} → ZFSet.{u}}
    (same : ∀ x ∈ a, f x = g x) : graph a f = graph a g := by
  apply ZFSet.ext
  intro z
  simp only [mem_graph]
  constructor <;> rintro ⟨x, hx, rfl⟩
  · exact ⟨x, hx, by rw [same x hx]⟩
  · exact ⟨x, hx, by rw [same x hx]⟩

/-- Application of a trace function to a point of its domain lies in the
fibre. -/
theorem traceApp_mem_fibre {a t x : ZFSet.{u}} {b : ZFSet.{u} → ZFSet.{u}}
    (ht : t ∈ tracePiSet a b) (hx : x ∈ a) : traceApp t x ∈ b x :=
  traceApp_mem ⟨t, ht⟩ ⟨x, hx⟩

/-- The abstraction of a family of fibre elements is a trace function. -/
theorem traceLam_graph_mem {a : ZFSet.{u}} {b f : ZFSet.{u} → ZFSet.{u}}
    (hf : ∀ x ∈ a, f x ∈ b x) : traceLam (graph a f) ∈ tracePiSet a b :=
  mem_tracePiSet.mpr ⟨graph a f, graph_mem_piSet hf, rfl⟩

private theorem first_mem_of_pair_mem_piSet {a f x y : ZFSet.{u}} {b : ZFSet.{u} → ZFSet.{u}}
    (hf : f ∈ piSet a b) (hxy : ZFSet.pair x y ∈ f) : x ∈ a :=
  (ZFSet.pair_mem_prod.mp ((mem_piSet.mp hf).1.1 hxy)).1

/-- A member of a trace function is a pair of a point of the domain with a
member of the value there. -/
theorem mem_of_mem_tracePiSet {a t z : ZFSet.{u}} {b : ZFSet.{u} → ZFSet.{u}}
    (ht : t ∈ tracePiSet a b) (hz : z ∈ t) :
    ∃ x ∈ a, ∃ w ∈ traceApp t x, z = ZFSet.pair x w := by
  obtain ⟨f, hf, rfl⟩ := mem_tracePiSet.mp ht
  obtain ⟨x, y, w, hxy, hwy, rfl⟩ := mem_traceLam.mp hz
  exact ⟨x, first_mem_of_pair_mem_piSet hf hxy, w, mem_traceApp.mpr hz, rfl⟩

/-- A trace function has no value outside its domain: applied there it gives the
empty set. So a trace function reads its arguments only through the domain of
the type it is a member of. -/
theorem traceApp_eq_empty_of_not_mem {a t x : ZFSet.{u}} {b : ZFSet.{u} → ZFSet.{u}}
    (ht : t ∈ tracePiSet a b) (hx : x ∉ a) : traceApp t x = ∅ := by
  apply ZFSet.ext
  intro w
  simp only [ZFSet.notMem_empty, iff_false]
  intro hw
  obtain ⟨x', hx', w', -, same⟩ := mem_of_mem_tracePiSet ht (mem_traceApp.mp hw)
  exact hx ((ZFSet.pair_inj.mp same).1 ▸ hx')

/-- **Function extensionality for trace functions**: two trace functions of
one type with the same values on the domain are equal. -/
theorem tracePiSet_ext {a t t' : ZFSet.{u}} {b : ZFSet.{u} → ZFSet.{u}}
    (ht : t ∈ tracePiSet a b) (ht' : t' ∈ tracePiSet a b)
    (same : ∀ x ∈ a, traceApp t x = traceApp t' x) : t = t' := by
  apply ZFSet.ext
  intro z
  constructor
  · intro hz
    obtain ⟨x, hx, w, hw, rfl⟩ := mem_of_mem_tracePiSet ht hz
    rw [same x hx] at hw
    exact mem_traceApp.mp hw
  · intro hz
    obtain ⟨x, hx, w, hw, rfl⟩ := mem_of_mem_tracePiSet ht' hz
    rw [← same x hx] at hw
    exact mem_traceApp.mp hw

private theorem isFunc_mono {a c c' f : ZFSet.{u}} (sub : c ⊆ c') (hf : ZFSet.IsFunc a c f) :
    ZFSet.IsFunc a c' f := by
  refine ⟨fun z hz => ?_, hf.2⟩
  obtain ⟨x, hx, y, hy, rfl⟩ := ZFSet.mem_prod.mp (hf.1 hz)
  exact ZFSet.pair_mem_prod.mpr ⟨hx, sub hy⟩

/-- Dependent functions are monotone in their fibres. -/
theorem piSet_mono {a : ZFSet.{u}} {b c : ZFSet.{u} → ZFSet.{u}}
    (sub : ∀ x ∈ a, b x ⊆ c x) : piSet a b ⊆ piSet a c := by
  intro f hf
  obtain ⟨functional, fibres⟩ := mem_piSet.mp hf
  refine mem_piSet.mpr ⟨isFunc_mono (fun y hy => ?_) functional,
    fun x hx y hy => sub x hx (fibres x hx y hy)⟩
  obtain ⟨x, hx, hyx⟩ := mem_familyUnion.mp hy
  exact mem_familyUnion.mpr ⟨x, hx, sub x hx hyx⟩

/-- Trace functions are monotone in their fibres. -/
theorem tracePiSet_mono {a : ZFSet.{u}} {b c : ZFSet.{u} → ZFSet.{u}}
    (sub : ∀ x ∈ a, b x ⊆ c x) : tracePiSet a b ⊆ tracePiSet a c := by
  intro t ht
  obtain ⟨f, hf, rfl⟩ := mem_tracePiSet.mp ht
  exact mem_tracePiSet.mpr ⟨f, piSet_mono sub hf, rfl⟩

/-- Dependent pairs are monotone in the base and the fibres. -/
theorem sigmaSet_mono {a a' : ZFSet.{u}} {b c : ZFSet.{u} → ZFSet.{u}}
    (base : a ⊆ a') (sub : ∀ x ∈ a, b x ⊆ c x) : sigmaSet a b ⊆ sigmaSet a' c := by
  intro p hp
  obtain ⟨x, hx, y, hy, rfl⟩ := mem_sigmaSet.mp hp
  exact mem_sigmaSet.mpr ⟨x, base hx, y, sub x hx hy, rfl⟩

/-- The first projection of a dependent pair lies in the base. -/
theorem first_mem_sigmaSet {a p : ZFSet.{u}} {b : ZFSet.{u} → ZFSet.{u}}
    (hp : p ∈ sigmaSet a b) : ZFSetOrderedPair.first p ∈ a := by
  obtain ⟨x, hx, y, _, rfl⟩ := mem_sigmaSet.mp hp
  rwa [ZFSetOrderedPair.first_pair]

/-- The second projection of a dependent pair lies in the fibre at the first. -/
theorem second_mem_sigmaSet {a p : ZFSet.{u}} {b : ZFSet.{u} → ZFSet.{u}}
    (hp : p ∈ sigmaSet a b) : ZFSetOrderedPair.second p ∈ b (ZFSetOrderedPair.first p) := by
  obtain ⟨x, _, y, hy, rfl⟩ := mem_sigmaSet.mp hp
  rwa [ZFSetOrderedPair.first_pair, ZFSetOrderedPair.second_pair]

/-- A dependent pair is determined by its projections. -/
theorem sigmaSet_ext {a p q : ZFSet.{u}} {b : ZFSet.{u} → ZFSet.{u}}
    (hp : p ∈ sigmaSet a b) (hq : q ∈ sigmaSet a b)
    (first : ZFSetOrderedPair.first p = ZFSetOrderedPair.first q)
    (second : ZFSetOrderedPair.second p = ZFSetOrderedPair.second q) : p = q := by
  obtain ⟨x, _, y, _, rfl⟩ := mem_sigmaSet.mp hp
  obtain ⟨x', _, y', _, rfl⟩ := mem_sigmaSet.mp hq
  simp only [ZFSetOrderedPair.first_pair, ZFSetOrderedPair.second_pair] at first second
  rw [first, second]

/-- Reflexivity is the member of every true identity value. -/
theorem empty_mem_truthCode_eq (x : ZFSet.{u}) : (∅ : ZFSet.{u}) ∈ truthCode (x = x) :=
  (mem_truthCode _ _).mpr ⟨rfl, rfl⟩

end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TowerInterpretation
