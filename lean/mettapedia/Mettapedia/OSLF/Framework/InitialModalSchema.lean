import Mettapedia.OSLF.Framework.SimulationPreservation
import Mettapedia.OSLF.Framework.DerivedModalities
import Mettapedia.GSLT.LanguageDef.KernelAuthority
import Mettapedia.Logic.Derivation

/-!
# The OSLF schema as an initial modal algebra; derivability as the least rule-closed set

Two free objects sit under every hosted logic, and neither is an object logic.

1. **Formulas.**  `OSLFFormula` is the term algebra over the fixed signature
   `⊤ ⊥ atom ∧ ∨ → ◇ □`.  For every algebra of that signature there is exactly
   one homomorphism out of it (`Unique (ModalHom formulas A)`).  The standard
   satisfaction relation `sem R I` is that unique homomorphism into the predicate
   algebra of a reduction relation (`sem_eq_fold`), and the change-of-base
   modalities `derivedDiamond`/`derivedBox` are its `dia`/`box`
   (`derivedDiamond_relSpan`, `derivedBox_relSpan`).  Transport of modal meaning
   along a bisimulation map is forced by universality
   (`sem_transport_of_initiality`).  Initiality is minimal weakness in the
   failed-distinction sense: the term algebra identifies no two distinct formulas
   (`identifies_formulas_iff`), every interpretation identifies at least as much
   (`identifies_formulas_le`), and homomorphisms only lose distinctions
   (`identifies_mono`).

2. **Derivations.**  For a specified rule predicate, `Derives` is the least
   rule-closed set (`Derives.least`).  A certificate is a rule-witnessing tree;
   replaying it is an exact authority for derivability
   (`replayChecker_authority`).  The checker never mentions a semantics, and it is
   sound in every model in which the rules are sound (`replay_sound_in_every_model`).

Metamath Zero and Isabelle/Pure are instances of the second object.  MM0: rules are
substitution instances of specified axiom schemata, and the substitution is the
certificate's witness (`SchematicRules`, `schematicWitness`).  Pure: hypothetical
judgments `Γ ⊢ A` closed under assumption, specified object rules, and
meta-implication introduction/elimination (`HypotheticalRules`,
`hypotheticalWitness`); Pure's schematic variables are `SchematicRules` applied to
the object rules, which this file does not compose.  OSLF adds the first object on
top of the second: the rules of a hosted OSLF proof system are sound for the
initial-algebra semantics as soon as each rule is (`oslf_rules_sound_by_initiality`).
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Framework.InitialModalSchema

open Mettapedia.OSLF.Formula
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.Framework.DerivedModalities
open Mettapedia.OSLF.Framework.SimulationPreservation
open Mettapedia.GSLT.LanguageDef.KernelAuthority
open Mettapedia.Logic

universe u v w

/-! ## Modal algebras over the OSLF signature -/

/-- An algebra of the OSLF formula signature.  No laws: this is the raw
signature, so that the term algebra is initial on the nose. -/
structure ModalAlgebra : Type (u + 1) where
  Carrier : Type u
  top : Carrier
  bot : Carrier
  and : Carrier → Carrier → Carrier
  or : Carrier → Carrier → Carrier
  imp : Carrier → Carrier → Carrier
  dia : Carrier → Carrier
  box : Carrier → Carrier
  atom : String → Carrier
  /-- A scope variable is a constant of the signature; the binding it refers to
  lives in the interpretation, not in the syntax, which is what keeps the term
  algebra initial on the nose once a generator is present. -/
  var : Nat → Carrier
  /-- A generator is a unary operation on the signature. -/
  mu : Carrier → Carrier
  /-- The empty collection of a kind: a constant of the signature, one per
  collection kind. -/
  emptyColl : CollType → Carrier
  /-- The cut of a kind: the binary structural operation. -/
  cut : CollType → Carrier → Carrier → Carrier
  /-- Application under a named head: one unary operation per head. -/
  headed : String → Carrier → Carrier

/-- A homomorphism of modal algebras. -/
structure ModalHom (A : ModalAlgebra.{u}) (B : ModalAlgebra.{v}) : Type (max u v) where
  map : A.Carrier → B.Carrier
  map_top : map A.top = B.top
  map_bot : map A.bot = B.bot
  map_and : ∀ x y, map (A.and x y) = B.and (map x) (map y)
  map_or : ∀ x y, map (A.or x y) = B.or (map x) (map y)
  map_imp : ∀ x y, map (A.imp x y) = B.imp (map x) (map y)
  map_dia : ∀ x, map (A.dia x) = B.dia (map x)
  map_box : ∀ x, map (A.box x) = B.box (map x)
  map_atom : ∀ a, map (A.atom a) = B.atom a
  map_var : ∀ k, map (A.var k) = B.var k
  map_mu : ∀ x, map (A.mu x) = B.mu (map x)
  map_emptyColl : ∀ kind, map (A.emptyColl kind) = B.emptyColl kind
  map_cut : ∀ kind x y, map (A.cut kind x y) = B.cut kind (map x) (map y)
  map_headed : ∀ label x, map (A.headed label x) = B.headed label (map x)

namespace ModalHom

variable {A : ModalAlgebra.{u}} {B : ModalAlgebra.{v}} {C : ModalAlgebra.{w}}

theorem ext {f g : ModalHom A B} (h : ∀ x, f.map x = g.map x) : f = g := by
  obtain ⟨fm, _, _, _, _, _, _, _, _, _, _, _, _, _⟩ := f
  obtain ⟨gm, _, _, _, _, _, _, _, _, _, _, _, _, _⟩ := g
  have e : fm = gm := funext h
  subst e
  rfl

def id (A : ModalAlgebra.{u}) : ModalHom A A where
  map := fun x => x
  map_top := rfl
  map_bot := rfl
  map_and := fun _ _ => rfl
  map_or := fun _ _ => rfl
  map_imp := fun _ _ => rfl
  map_dia := fun _ => rfl
  map_box := fun _ => rfl
  map_atom := fun _ => rfl
  map_var := fun _ => rfl
  map_mu := fun _ => rfl
  map_emptyColl := fun _ => rfl
  map_cut := fun _ _ _ => rfl
  map_headed := fun _ _ => rfl

def comp (f : ModalHom A B) (g : ModalHom B C) : ModalHom A C where
  map := fun x => g.map (f.map x)
  map_top := by rw [f.map_top, g.map_top]
  map_bot := by rw [f.map_bot, g.map_bot]
  map_and := fun x y => by rw [f.map_and, g.map_and]
  map_or := fun x y => by rw [f.map_or, g.map_or]
  map_imp := fun x y => by rw [f.map_imp, g.map_imp]
  map_dia := fun x => by rw [f.map_dia, g.map_dia]
  map_box := fun x => by rw [f.map_box, g.map_box]
  map_atom := fun a => by rw [f.map_atom, g.map_atom]
  map_var := fun k => by rw [f.map_var, g.map_var]
  map_mu := fun x => by rw [f.map_mu, g.map_mu]
  map_emptyColl := fun kind => by rw [f.map_emptyColl, g.map_emptyColl]
  map_cut := fun kind x y => by rw [f.map_cut, g.map_cut]
  map_headed := fun label x => by rw [f.map_headed, g.map_headed]

end ModalHom

/-! ## The term algebra is initial -/

/-- Formulas with their own constructors: the term algebra. -/
def formulas : ModalAlgebra.{0} where
  Carrier := OSLFFormula
  top := .top
  bot := .bot
  and := .and
  or := .or
  imp := .imp
  dia := .dia
  box := .box
  atom := .atom
  var := .var
  mu := .mu
  emptyColl := .emptyColl
  cut := .cut
  headed := .headed

/-- Evaluation of a formula in an arbitrary modal algebra. -/
def fold (A : ModalAlgebra.{u}) : OSLFFormula → A.Carrier
  | .top => A.top
  | .bot => A.bot
  | .atom a => A.atom a
  | .and φ ψ => A.and (fold A φ) (fold A ψ)
  | .or φ ψ => A.or (fold A φ) (fold A ψ)
  | .imp φ ψ => A.imp (fold A φ) (fold A ψ)
  | .dia φ => A.dia (fold A φ)
  | .box φ => A.box (fold A φ)
  | .var k => A.var k
  | .mu φ => A.mu (fold A φ)
  | .emptyColl kind => A.emptyColl kind
  | .cut kind φ ψ => A.cut kind (fold A φ) (fold A ψ)
  | .headed label φ => A.headed label (fold A φ)

def foldHom (A : ModalAlgebra.{u}) : ModalHom formulas A where
  map := fold A
  map_top := rfl
  map_bot := rfl
  map_and := fun _ _ => rfl
  map_or := fun _ _ => rfl
  map_imp := fun _ _ => rfl
  map_dia := fun _ => rfl
  map_box := fun _ => rfl
  map_atom := fun _ => rfl
  map_var := fun _ => rfl
  map_mu := fun _ => rfl
  map_emptyColl := fun _ => rfl
  map_cut := fun _ _ _ => rfl
  map_headed := fun _ _ => rfl

/-- Every homomorphism out of the term algebra is evaluation. -/
theorem hom_eq_fold (A : ModalAlgebra.{u}) (h : ModalHom formulas A) :
    ∀ φ, h.map φ = fold A φ
  | .top => h.map_top
  | .bot => h.map_bot
  | .atom a => h.map_atom a
  | .and φ ψ => by
      erw [show OSLFFormula.and φ ψ = formulas.and φ ψ from rfl, h.map_and,
        hom_eq_fold A h φ, hom_eq_fold A h ψ]
      rfl
  | .or φ ψ => by
      erw [show OSLFFormula.or φ ψ = formulas.or φ ψ from rfl, h.map_or,
        hom_eq_fold A h φ, hom_eq_fold A h ψ]
      rfl
  | .imp φ ψ => by
      erw [show OSLFFormula.imp φ ψ = formulas.imp φ ψ from rfl, h.map_imp,
        hom_eq_fold A h φ, hom_eq_fold A h ψ]
      rfl
  | .dia φ => by
      erw [show OSLFFormula.dia φ = formulas.dia φ from rfl, h.map_dia, hom_eq_fold A h φ]
      rfl
  | .var k => h.map_var k
  | .mu φ => by
      erw [show OSLFFormula.mu φ = formulas.mu φ from rfl, h.map_mu, hom_eq_fold A h φ]
      rfl
  | .box φ => by
      erw [show OSLFFormula.box φ = formulas.box φ from rfl, h.map_box, hom_eq_fold A h φ]
      rfl
  | .emptyColl kind => h.map_emptyColl kind
  | .cut kind φ ψ => by
      erw [show OSLFFormula.cut kind φ ψ = formulas.cut kind φ ψ from rfl, h.map_cut,
        hom_eq_fold A h φ, hom_eq_fold A h ψ]
      rfl
  | .headed label φ => by
      erw [show OSLFFormula.headed label φ = formulas.headed label φ from rfl, h.map_headed,
        hom_eq_fold A h φ]
      rfl

/-- **Initiality.**  The term algebra has exactly one homomorphism into every
modal algebra. -/
instance instUniqueHom (A : ModalAlgebra.{u}) : Unique (ModalHom formulas A) where
  default := foldHom A
  uniq h := ModalHom.ext (fun φ => hom_eq_fold A h φ)

theorem fold_formulas (φ : OSLFFormula) : fold formulas φ = φ :=
  (hom_eq_fold formulas (ModalHom.id formulas) φ).symm

/-! ### Initiality as minimal weakness

An interpretation's failed-distinction relation on formulas is the kernel of
evaluation.  The term algebra's kernel is the diagonal; every other kernel
contains it; homomorphisms can only enlarge kernels. -/

/-- The failed-distinction relation of an interpretation: formulas it cannot
tell apart. -/
def Identifies (A : ModalAlgebra.{u}) (φ ψ : OSLFFormula) : Prop :=
  fold A φ = fold A ψ

theorem identifies_formulas_iff (φ ψ : OSLFFormula) :
    Identifies formulas φ ψ ↔ φ = ψ := by
  unfold Identifies
  rw [fold_formulas, fold_formulas]
  exact Iff.rfl

theorem identifies_of_eq (A : ModalAlgebra.{u}) {φ ψ : OSLFFormula} (h : φ = ψ) :
    Identifies A φ ψ :=
  congrArg (fold A) h

/-- The term algebra is the least-weak interpretation: whatever it identifies,
every interpretation identifies. -/
theorem identifies_formulas_le (A : ModalAlgebra.{u}) {φ ψ : OSLFFormula}
    (h : Identifies formulas φ ψ) : Identifies A φ ψ :=
  identifies_of_eq A ((identifies_formulas_iff φ ψ).mp h)

/-- Homomorphisms only lose distinctions (weakness is monotone along
morphisms). -/
theorem identifies_mono {A : ModalAlgebra.{u}} {B : ModalAlgebra.{v}}
    (h : ModalHom A B) {φ ψ : OSLFFormula} (e : Identifies A φ ψ) :
    Identifies B φ ψ := by
  have factor : ∀ χ, fold B χ = h.map (fold A χ) :=
    fun χ => (hom_eq_fold B ((foldHom A).comp h) χ).symm
  unfold Identifies at e ⊢
  rw [factor φ, factor ψ, e]

/-- A genuine loss of distinction: the one-point algebra identifies `⊤` and `⊥`,
which the term algebra keeps apart. -/
def pointAlgebra : ModalAlgebra.{0} where
  Carrier := Unit
  top := ()
  bot := ()
  and := fun _ _ => ()
  or := fun _ _ => ()
  imp := fun _ _ => ()
  dia := fun _ => ()
  box := fun _ => ()
  atom := fun _ => ()
  var := fun _ => ()
  mu := fun _ => ()
  emptyColl := fun _ => ()
  cut := fun _ _ _ => ()
  headed := fun _ _ => ()

theorem point_identifies_top_bot : Identifies pointAlgebra .top .bot := rfl

theorem formulas_distinguishes_top_bot : ¬ Identifies formulas .top .bot := by
  rw [identifies_formulas_iff]
  exact OSLFFormula.noConfusion

/-! ## Satisfaction is the unique homomorphism -/

/-- The predicate algebra of a reduction relation with an atom interpretation.

Its carrier is the environment-indexed predicates, not the bare predicates: a
generator reads its body under one more binding than itself, so the operation
interpreting it cannot be a function of the body's meaning at a single
environment.  This is the same fact that makes generator length a function of
syntax, seen on the algebraic side. -/
def relAlgebra (R : Pattern → Pattern → Prop) (F : PredFrame) (I : AtomSem) :
    ModalAlgebra.{0} where
  Carrier := ScopeEnv → Pattern → Prop
  top := fun _ _ => True
  bot := fun _ _ => False
  and := fun φ ψ env p => φ env p ∧ ψ env p
  or := fun φ ψ env p => φ env p ∨ ψ env p
  imp := fun φ ψ env p => φ env p → ψ env p
  dia := fun φ env p => ∃ q, R p q ∧ φ env q
  box := fun φ env p => ∀ q, R q p → φ env q
  atom := fun a _ => I a
  var := fun k env => env k
  mu := fun φ env p =>
    ∀ candidate : Pattern → Prop, F.Mem candidate →
      (∀ t, φ (ScopeEnv.push candidate env) t → candidate t) → candidate p
  emptyColl := fun kind _ p =>
    F.close (fun term => term = .collection kind [] none) p
  cut := fun kind left right env p =>
    F.close
      (fun term => ∃ leftParts rightParts : List Pattern,
        term = .collection kind (leftParts ++ rightParts) none ∧
          left env (.collection kind leftParts none) ∧
          right env (.collection kind rightParts none)) p
  headed := fun label body env p =>
    F.close
      (fun term => ∃ inner : Pattern, term = .apply label [inner] ∧ body env inner) p

/-- `semEnv` is evaluation in the predicate algebra: the unique homomorphism. -/
theorem semEnv_eq_fold (R : Pattern → Pattern → Prop) (F : PredFrame) (I : AtomSem) :
    ∀ (φ : OSLFFormula) (env : ScopeEnv) (p : Pattern),
      semEnv R F I env φ p = fold (relAlgebra R F I) φ env p
  | .top, _, _ => rfl
  | .bot, _, _ => rfl
  | .atom _, _, _ => rfl
  | .var _, _, _ => rfl
  | .and φ ψ, env, p => by
      simp only [semEnv, fold, relAlgebra, semEnv_eq_fold R F I φ env p,
        semEnv_eq_fold R F I ψ env p]
  | .or φ ψ, env, p => by
      simp only [semEnv, fold, relAlgebra, semEnv_eq_fold R F I φ env p,
        semEnv_eq_fold R F I ψ env p]
  | .imp φ ψ, env, p => by
      simp only [semEnv, fold, relAlgebra, semEnv_eq_fold R F I φ env p,
        semEnv_eq_fold R F I ψ env p]
  | .dia φ, env, p => by
      simp only [semEnv, fold, relAlgebra, semEnv_eq_fold R F I φ env]
  | .box φ, env, p => by
      simp only [semEnv, fold, relAlgebra, semEnv_eq_fold R F I φ]
  | .mu φ, env, p => by
      simp only [semEnv, fold, relAlgebra, semEnv_eq_fold R F I φ]
  | .emptyColl _, _, _ => rfl
  | .cut _ φ ψ, env, p => by
      simp only [semEnv, fold, relAlgebra, semEnv_eq_fold R F I φ env,
        semEnv_eq_fold R F I ψ env]
  | .headed _ φ, env, p => by
      simp only [semEnv, fold, relAlgebra, semEnv_eq_fold R F I φ env]

/-- `sem` is evaluation in the predicate algebra at the empty environment. -/
theorem sem_eq_fold (R : Pattern → Pattern → Prop) (I : AtomSem) (φ : OSLFFormula) :
    sem R I φ = fold (relAlgebra R fullFrame I) φ ScopeEnv.empty :=
  funext fun p => semEnv_eq_fold R fullFrame I φ ScopeEnv.empty p

theorem sem_eq_foldHom (R : Pattern → Pattern → Prop) (I : AtomSem) (φ : OSLFFormula) :
    sem R I φ =
      (default : ModalHom formulas (relAlgebra R fullFrame I)).map φ ScopeEnv.empty :=
  sem_eq_fold R I φ

/-- The graph span of a relation. -/
def relSpan (R : Pattern → Pattern → Prop) : ReductionSpan.{0, 0} Pattern where
  Edge := { pq : Pattern × Pattern // R pq.1 pq.2 }
  source := fun e => e.1.1
  target := fun e => e.1.2

/-- The change-of-base diamond over the graph span is the algebra's `dia`. -/
theorem derivedDiamond_relSpan (R : Pattern → Pattern → Prop) (F : PredFrame)
    (I : AtomSem) (φ : Pattern → Prop) (env : ScopeEnv) :
    derivedDiamond (relSpan R) φ = (relAlgebra R F I).dia (fun _ => φ) env := by
  funext p
  apply propext
  simp only [derivedDiamond, di, pb, relSpan, relAlgebra, Function.comp]
  constructor
  · rintro ⟨⟨⟨a, b⟩, hab⟩, ha, hφ⟩
    exact ⟨b, ha ▸ hab, hφ⟩
  · rintro ⟨q, hR, hφ⟩
    exact ⟨⟨(p, q), hR⟩, rfl, hφ⟩

/-- The change-of-base box over the graph span is the algebra's `box`. -/
theorem derivedBox_relSpan (R : Pattern → Pattern → Prop) (F : PredFrame)
    (I : AtomSem) (φ : Pattern → Prop) (env : ScopeEnv) :
    derivedBox (relSpan R) φ = (relAlgebra R F I).box (fun _ => φ) env := by
  funext p
  apply propext
  simp only [derivedBox, ui, pb, relSpan, relAlgebra, Function.comp]
  constructor
  · intro h q hR
    exact h ⟨(q, p), hR⟩ rfl
  · rintro h ⟨⟨a, b⟩, hab⟩ hb
    exact h a (hb ▸ hab)

/-! ## Transport is forced by universality -/

/-- A bisimulation map pulls the target predicate algebra back to the source
one on every operation of the base signature.

It does **not** extend to a homomorphism of the full signature, and the reason
is structural rather than technical: the carrier of `relAlgebra` is indexed by
scope environments, a bisimulation map acts on terms and so has no action on
environments, and the generator's operation reads its argument at an
environment one binding deeper.  The base-signature statement is therefore what
initiality can deliver here, and the transport theorem below is stated on the
formulas the base signature generates. -/
structure PullbackBaseHom {R₁ R₂ : Pattern → Pattern → Prop} {I₁ I₂ : AtomSem}
    (sim : BisimulationMap R₁ R₂ I₁ I₂) : Prop where
  dia : ∀ (φ : ScopeEnv → Pattern → Prop) (env : ScopeEnv) (p : Pattern),
    (relAlgebra R₂ fullFrame I₂).dia φ env (sim.f p)
      ↔ (relAlgebra R₁ fullFrame I₁).dia (fun e q => φ e (sim.f q)) env p
  box : ∀ (φ : ScopeEnv → Pattern → Prop) (env : ScopeEnv) (p : Pattern),
    (relAlgebra R₂ fullFrame I₂).box φ env (sim.f p)
      ↔ (relAlgebra R₁ fullFrame I₁).box (fun e q => φ e (sim.f q)) env p
  atom : ∀ (a : String) (env : ScopeEnv) (p : Pattern),
    (relAlgebra R₂ fullFrame I₂).atom a env (sim.f p)
      ↔ (relAlgebra R₁ fullFrame I₁).atom a env p

theorem pullbackBaseHom {R₁ R₂ : Pattern → Pattern → Prop} {I₁ I₂ : AtomSem}
    (sim : BisimulationMap R₁ R₂ I₁ I₂) : PullbackBaseHom sim where
  dia := by
    intro φ env p
    show (∃ q, R₂ (sim.f p) q ∧ φ env q) ↔ ∃ q, R₁ p q ∧ φ env (sim.f q)
    constructor
    · rintro ⟨q₂, h, hφ⟩
      obtain ⟨q₁, hR, rfl⟩ := sim.backward_succ p q₂ h
      exact ⟨q₁, hR, hφ⟩
    · rintro ⟨q₁, h, hφ⟩
      exact ⟨sim.f q₁, sim.forward p q₁ h, hφ⟩
  box := by
    intro φ env p
    show (∀ q, R₂ q (sim.f p) → φ env q) ↔ ∀ q, R₁ q p → φ env (sim.f q)
    constructor
    · intro h q₁ hR
      exact h _ (sim.forward q₁ p hR)
    · intro h q₂ hR
      obtain ⟨q₁, hR₁, rfl⟩ := sim.backward_pred p q₂ hR
      exact h q₁ hR₁
  atom := by
    intro a env p
    exact (sim.atoms a p).symm

/-- Bisimulation transport of modal meaning on the formulas the base signature
generates.  The generator is excluded for the reason recorded above, not by
oversight: past it the two readings are taken in different lattices. -/
theorem sem_transport_of_initiality {R₁ R₂ : Pattern → Pattern → Prop}
    {I₁ I₂ : AtomSem} (sim : BisimulationMap R₁ R₂ I₁ I₂)
    (φ : OSLFFormula) (free : OSLFFormula.modalOnly φ = true) (p : Pattern) :
    sem R₁ I₁ φ p ↔ sem R₂ I₂ φ (sim.f p) :=
  bisimulation_map_preserves_sem sim φ free p

/-! ## Derivability is the least rule-closed set -/

section Derivations

variable {J : Type u}

/-- The replay checker: a certificate is accepted for a claim when it replays
and concludes that claim. -/
def replayChecker [DecidableEq J] {rules : List J → J → Prop}
    (rw : RuleWitness.{u, v} rules) : Checker J (Derivation J rw.W) where
  check := fun j d => d.valid rw && decide (d.concl = j)

/-- **Replay is an exact authority for derivability.**  This is the whole
contract of a schematic framework's verifier. -/
theorem replayChecker_authority [DecidableEq J] {rules : List J → J → Prop}
    (rw : RuleWitness.{u, v} rules) :
    (replayChecker rw).Authority (Derives rules) where
  sound := by
    intro j d h
    simp only [replayChecker, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨hv, hc⟩ := h
    exact hc ▸ Derivation.valid_sound rw d hv
  complete := by
    intro j hj
    obtain ⟨d, hv, hc⟩ := Derives.exists_derivation rw hj
    exact ⟨d, by simp [replayChecker, hv, hc]⟩

/-- **Profile blindness.**  The same replay checker is sound for every model in
which the specified rules are sound; no semantics enters the checker. -/
theorem replay_sound_in_every_model [DecidableEq J] {rules : List J → J → Prop}
    (rw : RuleWitness.{u, v} rules) (M : J → Prop)
    (rulesSound : ∀ hyps concl, rules hyps concl → (∀ h ∈ hyps, M h) → M concl) :
    (replayChecker rw).Sound M := by
  intro j d h
  exact Derives.least M rulesSound ((replayChecker_authority rw).sound j d h)

end Derivations

/-! ## The two free objects compose -/

/-- A hosted OSLF proof system is sound for the initial-algebra semantics as
soon as each of its rules is. -/
theorem oslf_rules_sound_by_initiality
    (rules : List OSLFFormula → OSLFFormula → Prop)
    (R : Pattern → Pattern → Prop) (I : AtomSem)
    (hvalid : ∀ hyps concl, rules hyps concl →
      (∀ h ∈ hyps, ∀ p, sem R I h p) → ∀ p, sem R I concl p) :
    ∀ {φ : OSLFFormula}, Derives rules φ → ∀ p, sem R I φ p :=
  fun d => Derives.least (fun χ => ∀ p, sem R I χ p) hvalid d

/-! ## Metamath Zero shape: substitution instances of specified schemata -/

section Schematic

variable {J : Type u} {Subst : Type v}

/-- Rules of a Metamath/MM0-style database: every substitution instance of a
specified axiom schema. -/
def SchematicRules (axioms : List (List J × J)) (act : Subst → J → J) :
    List J → J → Prop :=
  fun hyps concl =>
    ∃ ax ∈ axioms, ∃ σ : Subst, hyps = ax.1.map (act σ) ∧ concl = act σ ax.2

/-- The MM0 certificate witness: which axiom, and which substitution. -/
def schematicWitness [DecidableEq J] (axioms : List (List J × J)) (act : Subst → J → J) :
    RuleWitness.{u, v} (SchematicRules axioms act) where
  W := Fin axioms.length × Subst
  isInstance := fun iσ hyps concl =>
    decide (hyps = (axioms[iσ.1]).1.map (act iσ.2) ∧ concl = act iσ.2 (axioms[iσ.1]).2)
  sound := by
    rintro ⟨i, σ⟩ hyps concl h
    simp only [decide_eq_true_eq] at h
    exact ⟨axioms[i], List.getElem_mem i.isLt, σ, h⟩
  complete := by
    rintro hyps concl ⟨ax, hax, σ, h1, h2⟩
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hax
    exact ⟨(⟨i, hi⟩, σ), decide_eq_true ⟨h1, h2⟩⟩

end Schematic

/-! ### A Metamath-flavoured instance over OSLF formulas -/

namespace SchematicCanary

/-- Atom substitution on formulas: the MM0 `act`. -/
def substAtoms (σ : String → OSLFFormula) : OSLFFormula → OSLFFormula
  | .top => .top
  | .bot => .bot
  | .atom a => σ a
  | .and φ ψ => .and (substAtoms σ φ) (substAtoms σ ψ)
  | .or φ ψ => .or (substAtoms σ φ) (substAtoms σ ψ)
  | .imp φ ψ => .imp (substAtoms σ φ) (substAtoms σ ψ)
  | .dia φ => .dia (substAtoms σ φ)
  | .box φ => .box (substAtoms σ φ)
  | .var k => .var k
  | .mu φ => .mu (substAtoms σ φ)
  | .emptyColl kind => .emptyColl kind
  | .cut kind φ ψ => .cut kind (substAtoms σ φ) (substAtoms σ ψ)
  | .headed label φ => .headed label (substAtoms σ φ)

/-- Substitution lemma: substituting then evaluating is evaluating under the
substituted atom interpretation.

The substituted formulas must be closed and frame-blind, which membership in
the modal fragment delivers: an atom stands inside any number of binders, so a
substituted formula that read a scope variable would read a different one at
each occurrence, and one that read shape would be read in a different frame at
each occurrence. -/
theorem semEnv_substAtoms (R : Pattern → Pattern → Prop) (F : PredFrame) (I : AtomSem)
    (σ : String → OSLFFormula) (closed : ∀ a, OSLFFormula.modalOnly (σ a) = true) :
    ∀ φ env, semEnv R F I env (substAtoms σ φ)
      = semEnv R F (fun a => sem R I (σ a)) env φ
  | .top, _ => rfl
  | .bot, _ => rfl
  | .var _, _ => rfl
  | .atom a, env => by
      simpa [substAtoms, semEnv, sem] using
        semEnv_frame_irrelevant R F fullFrame I (σ a) (closed a) env ScopeEnv.empty
  | .and φ ψ, env => by
      funext p
      simp only [substAtoms, semEnv, semEnv_substAtoms R F I σ closed φ env,
        semEnv_substAtoms R F I σ closed ψ env]
  | .or φ ψ, env => by
      funext p
      simp only [substAtoms, semEnv, semEnv_substAtoms R F I σ closed φ env,
        semEnv_substAtoms R F I σ closed ψ env]
  | .imp φ ψ, env => by
      funext p
      simp only [substAtoms, semEnv, semEnv_substAtoms R F I σ closed φ env,
        semEnv_substAtoms R F I σ closed ψ env]
  | .dia φ, env => by
      funext p
      simp only [substAtoms, semEnv, semEnv_substAtoms R F I σ closed φ env]
  | .box φ, env => by
      funext p
      simp only [substAtoms, semEnv, semEnv_substAtoms R F I σ closed φ env]
  | .mu φ, env => by
      funext p
      simp only [substAtoms, semEnv]
      apply propext
      constructor
      · intro holds candidate memc pre
        refine holds candidate memc ?_
        intro u hu
        rw [semEnv_substAtoms R F I σ closed φ (ScopeEnv.push candidate env)] at hu
        exact pre u hu
      · intro holds candidate memc pre
        refine holds candidate memc ?_
        intro u hu
        rw [← semEnv_substAtoms R F I σ closed φ (ScopeEnv.push candidate env)] at hu
        exact pre u hu
  | .emptyColl _, _ => rfl
  | .cut _ φ ψ, env => by
      funext p
      simp only [substAtoms, semEnv, semEnv_substAtoms R F I σ closed φ env,
        semEnv_substAtoms R F I σ closed ψ env]
  | .headed _ φ, env => by
      funext p
      simp only [substAtoms, semEnv, semEnv_substAtoms R F I σ closed φ env]

theorem sem_substAtoms (R : Pattern → Pattern → Prop) (I : AtomSem)
    (σ : String → OSLFFormula) (closed : ∀ a, OSLFFormula.modalOnly (σ a) = true)
    (φ : OSLFFormula) :
    sem R I (substAtoms σ φ) = sem R (fun a => sem R I (σ a)) φ :=
  semEnv_substAtoms R fullFrame I σ closed φ ScopeEnv.empty

/-- Any inhabitant of the state type, to instantiate a universally quantified
model statement. -/
def somePattern : Pattern := .bvar 0

/-- Modus ponens and Hilbert's K, as schemata over atoms `A`, `B`. -/
def axioms : List (List OSLFFormula × OSLFFormula) :=
  [ ([.atom "A", .imp (.atom "A") (.atom "B")], .atom "B"),
    ([], .imp (.atom "A") (.imp (.atom "B") (.atom "A"))) ]

abbrev rules := SchematicRules axioms substAtoms

abbrev witness := schematicWitness axioms substAtoms

abbrev checker := replayChecker witness

/-- The instance `⊤ → (⊤ → ⊤)` of K. -/
def σ₀ : String → OSLFFormula := fun _ => .top

def kInstance : OSLFFormula := .imp .top (.imp .top .top)

def kCertificate : Derivation OSLFFormula witness.W :=
  .node kInstance (⟨1, by decide⟩, σ₀) 0 Fin.elim0

/-- Positive control: the certificate replays. -/
theorem kCertificate_accepted : checker.check kInstance kCertificate = true := by
  decide +kernel

theorem kInstance_derivable : Derives rules kInstance :=
  (replayChecker_authority witness).sound _ _ kCertificate_accepted

/-- Negative control at the certificate boundary: the same certificate does
not establish `⊥`. -/
theorem kCertificate_rejected_for_bot : checker.check .bot kCertificate = false := by
  decide +kernel

/-- Negative control at the derivability boundary: `⊥` is not derivable,
by leastness against the empty-reduction, all-true-atoms model. -/
theorem bot_not_derivable : ¬ Derives rules .bot := by
  intro d
  have valid : ∀ p, sem (fun _ _ => False) (fun _ _ => True) OSLFFormula.bot p := by
    refine oslf_rules_sound_by_initiality rules (fun _ _ => False) (fun _ _ => True) ?_ d
    rintro hyps concl ⟨ax, hax, σ, rfl, rfl⟩ hhyps p
    simp only [axioms, List.mem_cons, List.mem_nil_iff, or_false] at hax
    rcases hax with rfl | rfl
    · have hA := hhyps (substAtoms σ (.atom "A")) (by simp) p
      have hAB := hhyps (substAtoms σ (.imp (.atom "A") (.atom "B"))) (by simp) p
      simp only [substAtoms, sem] at hA hAB ⊢
      exact hAB hA
    · simp only [substAtoms, sem]
      intro hA _
      exact hA
  exact valid somePattern

end SchematicCanary

/-! ## Isabelle/Pure shape: hypothetical judgments under meta-implication -/

section Hypothetical

variable {Atom : Type u}

/-- Object formulas with meta-implication only. -/
inductive PureForm (Atom : Type u) : Type u where
  | atom : Atom → PureForm Atom
  | imp : PureForm Atom → PureForm Atom → PureForm Atom
  deriving DecidableEq

/-- A hypothetical judgment `Γ ⊢ A`. -/
abbrev Hyp (Atom : Type u) : Type u := List (PureForm Atom) × PureForm Atom

/-- Pure's rule set over specified object rules: assumption, object rules under
a context, `⟹`-introduction, `⟹`-elimination. -/
def HypotheticalRules (objectRules : List (List (PureForm Atom) × PureForm Atom)) :
    List (Hyp Atom) → Hyp Atom → Prop :=
  fun hyps concl =>
    (hyps = [] ∧ concl.2 ∈ concl.1) ∨
    (∃ r ∈ objectRules, hyps = r.1.map (fun A => (concl.1, A)) ∧ concl.2 = r.2) ∨
    (∃ A B, hyps = [(A :: concl.1, B)] ∧ concl.2 = .imp A B) ∨
    (∃ A, hyps = [(concl.1, .imp A concl.2), (concl.1, A)])

/-- The witness names the rule kind. -/
inductive PureStep (Atom : Type u) (n : Nat) : Type u where
  | assumption
  | objectRule (i : Fin n)
  | impIntro (A B : PureForm Atom)
  | impElim (A : PureForm Atom)

def hypotheticalWitness [DecidableEq Atom]
    (objectRules : List (List (PureForm Atom) × PureForm Atom)) :
    RuleWitness.{u, u} (HypotheticalRules objectRules) where
  W := PureStep Atom objectRules.length
  isInstance := fun step hyps concl =>
    match step with
    | .assumption => decide (hyps = [] ∧ concl.2 ∈ concl.1)
    | .objectRule i =>
        decide (hyps = (objectRules[i]).1.map (fun A => (concl.1, A)) ∧
          concl.2 = (objectRules[i]).2)
    | .impIntro A B => decide (hyps = [(A :: concl.1, B)] ∧ concl.2 = .imp A B)
    | .impElim A => decide (hyps = [(concl.1, .imp A concl.2), (concl.1, A)])
  sound := by
    intro step hyps concl h
    cases step with
    | assumption =>
      simp only [decide_eq_true_eq] at h
      exact Or.inl h
    | objectRule i =>
      simp only [decide_eq_true_eq] at h
      exact Or.inr (Or.inl ⟨objectRules[i], List.getElem_mem i.isLt, h⟩)
    | impIntro A B =>
      simp only [decide_eq_true_eq] at h
      exact Or.inr (Or.inr (Or.inl ⟨A, B, h⟩))
    | impElim A =>
      simp only [decide_eq_true_eq] at h
      exact Or.inr (Or.inr (Or.inr ⟨A, h⟩))
  complete := by
    intro hyps concl h
    rcases h with h | ⟨r, hr, h⟩ | ⟨A, B, h⟩ | ⟨A, h⟩
    · exact ⟨.assumption, decide_eq_true h⟩
    · obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hr
      exact ⟨.objectRule ⟨i, hi⟩, decide_eq_true h⟩
    · exact ⟨.impIntro A B, decide_eq_true h⟩
    · exact ⟨.impElim A, decide_eq_true h⟩

end Hypothetical

namespace HypotheticalCanary

abbrev rules := HypotheticalRules (Atom := String) []

abbrev witness := hypotheticalWitness (Atom := String) []

abbrev checker := replayChecker witness

def a : PureForm String := .atom "a"

/-- `⊢ a ⟹ a` by introduction then assumption. -/
def identityCertificate : Derivation (Hyp String) witness.W :=
  .node ([], .imp a a) (.impIntro a a) 1
    (fun _ => .node ([a], a) .assumption 0 Fin.elim0)

theorem identity_accepted : checker.check ([], .imp a a) identityCertificate = true := by
  decide +kernel

theorem identity_derivable : Derives rules ([], .imp a a) :=
  (replayChecker_authority witness).sound _ _ identity_accepted

/-- Truth under a valuation, the invariant that refutes `⊢ a`. -/
def eval (v : String → Prop) : PureForm String → Prop
  | .atom x => v x
  | .imp A B => eval v A → eval v B

def Valid (j : Hyp String) : Prop :=
  ∀ v : String → Prop, (∀ B ∈ j.1, eval v B) → eval v j.2

theorem rules_valid : ∀ hyps concl, rules hyps concl →
    (∀ h ∈ hyps, Valid h) → Valid concl := by
  rintro hyps ⟨Γ, C⟩ h hhyps v hΓ
  rcases h with ⟨_, hmem⟩ | ⟨r, hr, _⟩ | ⟨A, B, rfl, rfl⟩ | ⟨A, rfl⟩
  · exact hΓ C hmem
  · simp at hr
  · intro hA
    exact hhyps (A :: Γ, B) (by simp) v (by
      intro B' hB
      simp only [List.mem_cons] at hB
      rcases hB with rfl | hB
      · exact hA
      · exact hΓ B' hB)
  · have hAC := hhyps (Γ, .imp A C) (by simp) v hΓ
    have hA := hhyps (Γ, A) (by simp) v hΓ
    exact hAC hA

/-- Negative control: a bare atom is not derivable from no hypotheses. -/
theorem atom_not_derivable : ¬ Derives rules ([], a) := by
  intro d
  have := Derives.least Valid rules_valid d (fun _ => False) (by simp)
  exact this

end HypotheticalCanary

/-! ## Axiom audit -/

#print axioms instUniqueHom
#print axioms sem_eq_fold
#print axioms derivedDiamond_relSpan
#print axioms sem_transport_of_initiality
#print axioms identifies_mono
#print axioms replayChecker_authority
#print axioms replay_sound_in_every_model
#print axioms oslf_rules_sound_by_initiality
#print axioms SchematicCanary.bot_not_derivable
#print axioms HypotheticalCanary.atom_not_derivable

end Mettapedia.OSLF.Framework.InitialModalSchema
