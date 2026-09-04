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

namespace ModalHom

variable {A : ModalAlgebra.{u}} {B : ModalAlgebra.{v}} {C : ModalAlgebra.{w}}

theorem ext {f g : ModalHom A B} (h : ∀ x, f.map x = g.map x) : f = g := by
  obtain ⟨fm, _, _, _, _, _, _, _, _⟩ := f
  obtain ⟨gm, _, _, _, _, _, _, _, _⟩ := g
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

/-- Every homomorphism out of the term algebra is evaluation. -/
theorem hom_eq_fold (A : ModalAlgebra.{u}) (h : ModalHom formulas A) :
    ∀ φ, h.map φ = fold A φ
  | .top => h.map_top
  | .bot => h.map_bot
  | .atom a => h.map_atom a
  | .and φ ψ => by
      rw [show OSLFFormula.and φ ψ = formulas.and φ ψ from rfl, h.map_and,
        hom_eq_fold A h φ, hom_eq_fold A h ψ]
      rfl
  | .or φ ψ => by
      rw [show OSLFFormula.or φ ψ = formulas.or φ ψ from rfl, h.map_or,
        hom_eq_fold A h φ, hom_eq_fold A h ψ]
      rfl
  | .imp φ ψ => by
      rw [show OSLFFormula.imp φ ψ = formulas.imp φ ψ from rfl, h.map_imp,
        hom_eq_fold A h φ, hom_eq_fold A h ψ]
      rfl
  | .dia φ => by
      rw [show OSLFFormula.dia φ = formulas.dia φ from rfl, h.map_dia, hom_eq_fold A h φ]
      rfl
  | .box φ => by
      rw [show OSLFFormula.box φ = formulas.box φ from rfl, h.map_box, hom_eq_fold A h φ]
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

theorem point_identifies_top_bot : Identifies pointAlgebra .top .bot := rfl

theorem formulas_distinguishes_top_bot : ¬ Identifies formulas .top .bot := by
  rw [identifies_formulas_iff]
  exact OSLFFormula.noConfusion

/-! ## Satisfaction is the unique homomorphism -/

/-- The predicate algebra of a reduction relation with an atom interpretation. -/
def relAlgebra (R : Pattern → Pattern → Prop) (I : AtomSem) : ModalAlgebra.{0} where
  Carrier := Pattern → Prop
  top := fun _ => True
  bot := fun _ => False
  and := fun φ ψ p => φ p ∧ ψ p
  or := fun φ ψ p => φ p ∨ ψ p
  imp := fun φ ψ p => φ p → ψ p
  dia := fun φ p => ∃ q, R p q ∧ φ q
  box := fun φ p => ∀ q, R q p → φ q
  atom := fun a => I a

/-- `sem` is evaluation in the predicate algebra: the unique homomorphism. -/
theorem sem_eq_fold (R : Pattern → Pattern → Prop) (I : AtomSem) :
    ∀ φ, sem R I φ = fold (relAlgebra R I) φ
  | .top => rfl
  | .bot => rfl
  | .atom _ => rfl
  | .and φ ψ => by
      funext p
      simp only [sem, fold, relAlgebra, sem_eq_fold R I φ, sem_eq_fold R I ψ]
  | .or φ ψ => by
      funext p
      simp only [sem, fold, relAlgebra, sem_eq_fold R I φ, sem_eq_fold R I ψ]
  | .imp φ ψ => by
      funext p
      simp only [sem, fold, relAlgebra, sem_eq_fold R I φ, sem_eq_fold R I ψ]
  | .dia φ => by
      funext p
      simp only [sem, fold, relAlgebra, sem_eq_fold R I φ]
  | .box φ => by
      funext p
      simp only [sem, fold, relAlgebra, sem_eq_fold R I φ]

theorem sem_eq_foldHom (R : Pattern → Pattern → Prop) (I : AtomSem) (φ : OSLFFormula) :
    sem R I φ = (default : ModalHom formulas (relAlgebra R I)).map φ :=
  sem_eq_fold R I φ

/-- The graph span of a relation. -/
def relSpan (R : Pattern → Pattern → Prop) : ReductionSpan.{0, 0} Pattern where
  Edge := { pq : Pattern × Pattern // R pq.1 pq.2 }
  source := fun e => e.1.1
  target := fun e => e.1.2

/-- The change-of-base diamond over the graph span is the algebra's `dia`. -/
theorem derivedDiamond_relSpan (R : Pattern → Pattern → Prop) (I : AtomSem)
    (φ : Pattern → Prop) :
    derivedDiamond (relSpan R) φ = (relAlgebra R I).dia φ := by
  funext p
  apply propext
  simp only [derivedDiamond, di, pb, relSpan, relAlgebra, Function.comp]
  constructor
  · rintro ⟨⟨⟨a, b⟩, hab⟩, ha, hφ⟩
    exact ⟨b, ha ▸ hab, hφ⟩
  · rintro ⟨q, hR, hφ⟩
    exact ⟨⟨(p, q), hR⟩, rfl, hφ⟩

/-- The change-of-base box over the graph span is the algebra's `box`. -/
theorem derivedBox_relSpan (R : Pattern → Pattern → Prop) (I : AtomSem)
    (φ : Pattern → Prop) :
    derivedBox (relSpan R) φ = (relAlgebra R I).box φ := by
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
one, homomorphically. -/
def pullbackHom {R₁ R₂ : Pattern → Pattern → Prop} {I₁ I₂ : AtomSem}
    (sim : BisimulationMap R₁ R₂ I₁ I₂) :
    ModalHom (relAlgebra R₂ I₂) (relAlgebra R₁ I₁) where
  map := fun φ p => φ (sim.f p)
  map_top := rfl
  map_bot := rfl
  map_and := fun _ _ => rfl
  map_or := fun _ _ => rfl
  map_imp := fun _ _ => rfl
  map_dia := fun φ => by
    funext p
    apply propext
    show (∃ q, R₂ (sim.f p) q ∧ φ q) ↔ ∃ q, R₁ p q ∧ φ (sim.f q)
    constructor
    · rintro ⟨q₂, h, hφ⟩
      obtain ⟨q₁, hR, rfl⟩ := sim.backward_succ p q₂ h
      exact ⟨q₁, hR, hφ⟩
    · rintro ⟨q₁, h, hφ⟩
      exact ⟨sim.f q₁, sim.forward p q₁ h, hφ⟩
  map_box := fun φ => by
    funext p
    apply propext
    show (∀ q, R₂ q (sim.f p) → φ q) ↔ ∀ q, R₁ q p → φ (sim.f q)
    constructor
    · intro h q₁ hR
      exact h _ (sim.forward q₁ p hR)
    · intro h q₂ hR
      obtain ⟨q₁, hR₁, rfl⟩ := sim.backward_pred p q₂ hR
      exact h q₁ hR₁
  map_atom := fun a => by
    funext p
    exact propext (sim.atoms a p).symm

/-- Bisimulation transport of modal meaning, derived from initiality alone:
both `sem R₁ I₁` and `(pullbackHom sim).map ∘ sem R₂ I₂` are homomorphisms out
of the term algebra, hence equal. -/
theorem sem_transport_of_initiality {R₁ R₂ : Pattern → Pattern → Prop}
    {I₁ I₂ : AtomSem} (sim : BisimulationMap R₁ R₂ I₁ I₂)
    (φ : OSLFFormula) (p : Pattern) :
    sem R₁ I₁ φ p ↔ sem R₂ I₂ φ (sim.f p) := by
  have factor : ∀ χ, fold (relAlgebra R₁ I₁) χ =
      (pullbackHom sim).map (fold (relAlgebra R₂ I₂) χ) :=
    fun χ => (hom_eq_fold _ ((foldHom _).comp (pullbackHom sim)) χ).symm
  rw [sem_eq_fold R₁ I₁ φ, sem_eq_fold R₂ I₂ φ, factor φ]
  exact Iff.rfl

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

/-- Substitution lemma: substituting then evaluating is evaluating under the
substituted atom interpretation. -/
theorem sem_substAtoms (R : Pattern → Pattern → Prop) (I : AtomSem)
    (σ : String → OSLFFormula) :
    ∀ φ, sem R I (substAtoms σ φ) = sem R (fun a => sem R I (σ a)) φ
  | .top => rfl
  | .bot => rfl
  | .atom _ => rfl
  | .and φ ψ => by
      funext p
      simp only [substAtoms, sem, sem_substAtoms R I σ φ, sem_substAtoms R I σ ψ]
  | .or φ ψ => by
      funext p
      simp only [substAtoms, sem, sem_substAtoms R I σ φ, sem_substAtoms R I σ ψ]
  | .imp φ ψ => by
      funext p
      simp only [substAtoms, sem, sem_substAtoms R I σ φ, sem_substAtoms R I σ ψ]
  | .dia φ => by
      funext p
      simp only [substAtoms, sem, sem_substAtoms R I σ φ]
  | .box φ => by
      funext p
      simp only [substAtoms, sem, sem_substAtoms R I σ φ]

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
