import Mettapedia.AutoBooks.Codex.Henkin1950.CanonicalPropClasses
import Mettapedia.AutoBooks.Codex.Henkin1950.TheoremTransport

namespace Mettapedia.AutoBooks.Codex.Henkin1950

open Mettapedia.Logic.HOL

/-!
Paper-faithful canonical class model for Henkin pp. 86-88.

The existing Codex development already provides the pieces of Henkin's
canonical semantics:

- `TermClass` quotient carriers,
- the canonical truth relation `Holds`,
- class-based denotation of terms and proposition-valued terms,
- and theorem transport for open schemata under representative substitution.

This file packages those ingredients into a single class-model object so later
work on the description operator and the truth lemma can target a stable
interface.
-/

/-- A paper-faithful canonical class model packages the exact closed-theory
assumptions Henkin uses after the maximal-consistent-set step. -/
structure CanonicalClassModel where
  T : ClosedTheorySet
  completeConsistent : CompleteConsistentTheory T
  existsWitness : ExistentialWitnessClosed T
  allCounterexample : UniversalCounterexampleClosed T

namespace CanonicalClassModel

/-- The underlying closed-theory world already packaged in the trusted HOL
canonical-theory interface. -/
def toWorld (M : CanonicalClassModel) :
    Mettapedia.Logic.HOL.ClosedTheorySet.World Primitive :=
  M.completeConsistent.toWorld M.existsWitness M.allCounterexample

/-- The canonical carrier at type `τ`. -/
abbrev Carrier (M : CanonicalClassModel) (τ : HTy) : Type :=
  CanonicalFrame.Carrier M.T τ

/-- Quotient-valued assignments into the canonical class model. -/
abbrev Assignment (M : CanonicalClassModel) (Γ : Ctx Atom) : Type :=
  CanonicalFrame.Assignment M.T Γ

/-- The unique assignment into the empty context. -/
def emptyAssignment (M : CanonicalClassModel) : Assignment M [] := by
  intro τ v
  cases v

/-- Constants denote as closed-term quotient classes. -/
def constValue (M : CanonicalClassModel) {τ : HTy} (c : Primitive τ) :
    Carrier M τ :=
  CanonicalFrame.constValue (T := M.T) c

/-- The proposition class of truth in the canonical model. -/
abbrev trueClass (M : CanonicalClassModel) : Carrier M o :=
  CanonicalFrame.trueClass (T := M.T)

/-- The proposition class of falsity in the canonical model. -/
abbrev falseClass (M : CanonicalClassModel) : Carrier M o :=
  CanonicalFrame.falseClass (T := M.T)

/-- Proposition classes hold exactly when they are the canonical truth class. -/
def PropClassHolds (M : CanonicalClassModel) (p : Carrier M o) : Prop :=
  CanonicalFrame.PropClassHolds M.completeConsistent p

/-- Open terms denote by closing under the chosen representatives of a class
assignment and quotienting the resulting closed term. -/
noncomputable def denoteTerm
    (M : CanonicalClassModel)
    (ν : Assignment M Γ) (t : Term Γ τ) :
    Carrier M τ :=
  CanonicalFrame.denoteTerm (T := M.T) ν t

/-- Open formulas denote by the canonical truth relation. -/
def denoteFormula
    (M : CanonicalClassModel)
    (ν : Assignment M Γ) (φ : Formula Γ) : Prop :=
  CanonicalFrame.denoteFormula M.T ν φ

/-- The description constant at type `α` as a canonical class-model value. -/
def iotaValue (M : CanonicalClassModel) (α : HTy) :
    Carrier M (Pred α ⇒ α) :=
  M.constValue (.iota α)

/-- A closed always-true predicate used as a canary witness for nonemptiness of
every canonical carrier. -/
def topPredicate (α : HTy) : ClosedTerm (Pred α) :=
  .lam (.top : Formula [α])

/-- Every canonical carrier is inhabited by applying the description constant to
the always-true predicate. -/
def defaultElement (M : CanonicalClassModel) (α : HTy) : Carrier M α :=
  appClass (T := M.T) (M.iotaValue α) (classOf (T := M.T) (topPredicate α))

theorem carrier_nonempty (M : CanonicalClassModel) (α : HTy) :
    Nonempty (Carrier M α) :=
  ⟨M.defaultElement α⟩

/-- Assignment of a single predicate variable to a chosen proposition-valued
carrier element. -/
def predicateAssignment
    (M : CanonicalClassModel)
    {α : HTy}
    (p : Carrier M (Pred α)) :
    Assignment M [Pred α] :=
  ClassAssignment.extend (M.emptyAssignment) p

/-- Assignment of a point and predicate to the context used by Henkin's
description axiom. -/
def pointPredicateAssignment
    (M : CanonicalClassModel)
    {α : HTy}
    (x : Carrier M α) (p : Carrier M (Pred α)) :
    Assignment M [α, Pred α] :=
  ClassAssignment.extend (M.predicateAssignment p) x

@[simp] theorem pointPredicateAssignment_var0
    (M : CanonicalClassModel)
    {α : HTy}
    (x : Carrier M α) (p : Carrier M (Pred α)) :
    M.pointPredicateAssignment x p (.vz : Var [α, Pred α] α) = x :=
  rfl

@[simp] theorem pointPredicateAssignment_var1
    (M : CanonicalClassModel)
    {α : HTy}
    (x : Carrier M α) (p : Carrier M (Pred α)) :
    M.pointPredicateAssignment x p (.vs (.vz : Var [Pred α] (Pred α))) = p :=
  rfl

@[simp] theorem denoteTerm_var
    (M : CanonicalClassModel)
    (ν : Assignment M Γ) (v : Var Γ τ) :
    M.denoteTerm ν (.var v : Term Γ τ) = ν v :=
  CanonicalFrame.denoteTerm_var (T := M.T) ν v

@[simp] theorem denoteTerm_const
    (M : CanonicalClassModel)
    (ν : Assignment M Γ) (c : Primitive τ) :
    M.denoteTerm ν (.const c : Term Γ τ) = M.constValue c := by
  exact CanonicalFrame.denoteTerm_const (T := M.T) ν c

@[simp] theorem denoteTerm_app
    (M : CanonicalClassModel)
    (ν : Assignment M Γ)
    (f : Term Γ (σ ⇒ τ)) (t : Term Γ σ) :
    M.denoteTerm ν (.app f t) =
      appClass (T := M.T) (M.denoteTerm ν f) (M.denoteTerm ν t) :=
  CanonicalFrame.denoteTerm_app (T := M.T) ν f t

@[simp] theorem denoteTerm_weaken
    (M : CanonicalClassModel)
    (ν : Assignment M Γ) (x : Carrier M σ) (t : Term Γ τ) :
    M.denoteTerm (ClassAssignment.extend ν x)
      (weaken (Base := Atom) (Const := Primitive) (σ := σ) t) =
        M.denoteTerm ν t := by
  apply congrArg (classOf (T := M.T))
  unfold ClassAssignment.closeTerm
  unfold Mettapedia.AutoBooks.Codex.Henkin1950.closeTerm
  rw [weaken, subst_rename]
  apply subst_ext
  intro α v
  simp [Rename.weaken, RepresentativeAssignment.extend]

@[simp] theorem denoteTerm_iotaTerm
    (M : CanonicalClassModel)
    (ν : Assignment M Γ)
    (p : Term Γ (Pred α)) :
    M.denoteTerm ν (iotaTerm p) =
      appClass (T := M.T) (M.iotaValue α) (M.denoteTerm ν p) := by
  rw [iotaTerm, M.denoteTerm_app, M.denoteTerm_const, iotaValue]

@[simp] theorem denoteFormula_eq_iff
    (M : CanonicalClassModel)
    (ν : Assignment M Γ)
    {τ : HTy} (t u : Term Γ τ) :
    M.denoteFormula ν (eq t u) ↔
      M.denoteTerm ν t = M.denoteTerm ν u :=
  CanonicalFrame.denoteFormula_eq_iff (T := M.T) M.completeConsistent ν t u

theorem denoteFormula_top
    (M : CanonicalClassModel)
    (ν : Assignment M Γ) :
    M.denoteFormula ν (.top : Formula Γ) :=
  CanonicalFrame.denoteFormula_top (T := M.T) M.completeConsistent ν

@[simp] theorem denoteFormula_bot_iff_false
    (M : CanonicalClassModel)
    (ν : Assignment M Γ) :
    M.denoteFormula ν (.bot : Formula Γ) ↔ False :=
  CanonicalFrame.denoteFormula_bot_iff_false (T := M.T) M.completeConsistent ν

@[simp] theorem denoteFormula_not_iff
    (M : CanonicalClassModel)
    (ν : Assignment M Γ)
    (φ : Formula Γ) :
    M.denoteFormula ν (not φ) ↔ ¬ M.denoteFormula ν φ :=
  CanonicalFrame.denoteFormula_not_iff (T := M.T) M.completeConsistent ν φ

@[simp] theorem denoteFormula_and_iff
    (M : CanonicalClassModel)
    (ν : Assignment M Γ)
    (φ ψ : Formula Γ) :
    M.denoteFormula ν (and φ ψ) ↔
      M.denoteFormula ν φ ∧ M.denoteFormula ν ψ :=
  CanonicalFrame.denoteFormula_and_iff (T := M.T) M.completeConsistent ν φ ψ

@[simp] theorem denoteFormula_or_iff
    (M : CanonicalClassModel)
    (ν : Assignment M Γ)
    (φ ψ : Formula Γ) :
    M.denoteFormula ν (or φ ψ) ↔
      M.denoteFormula ν φ ∨ M.denoteFormula ν ψ :=
  CanonicalFrame.denoteFormula_or_iff (T := M.T) M.completeConsistent ν φ ψ

@[simp] theorem denoteFormula_imp_iff
    (M : CanonicalClassModel)
    (ν : Assignment M Γ)
    (φ ψ : Formula Γ) :
    M.denoteFormula ν (imp φ ψ) ↔
      (M.denoteFormula ν φ → M.denoteFormula ν ψ) :=
  CanonicalFrame.denoteFormula_imp_iff (T := M.T) M.completeConsistent ν φ ψ

@[simp] theorem denoteFormula_all_iff
    (M : CanonicalClassModel)
    (ν : Assignment M Γ)
    {σ : HTy} (φ : Formula (σ :: Γ)) :
    M.denoteFormula ν (.all φ) ↔
      ∀ c : Carrier M σ, M.denoteFormula (ClassAssignment.extend ν c) φ :=
  CanonicalFrame.denoteFormula_all_iff
    (T := M.T) M.completeConsistent M.existsWitness M.allCounterexample ν φ

@[simp] theorem denoteFormula_ex_iff
    (M : CanonicalClassModel)
    (ν : Assignment M Γ)
    {σ : HTy} (φ : Formula (σ :: Γ)) :
    M.denoteFormula ν (.ex φ) ↔
      ∃ c : Carrier M σ, M.denoteFormula (ClassAssignment.extend ν c) φ :=
  CanonicalFrame.denoteFormula_ex_iff
    (T := M.T) M.completeConsistent M.existsWitness M.allCounterexample ν φ

@[simp] theorem propClassHolds_denoteTerm_iff
    (M : CanonicalClassModel)
    (ν : Assignment M Γ)
    (φ : Formula Γ) :
    M.PropClassHolds (M.denoteTerm ν φ) ↔ M.denoteFormula ν φ :=
  CanonicalFrame.propClassHolds_denoteTerm_iff (T := M.T) M.completeConsistent ν φ

/-- Model-layer truth-lemma canary: denotation of an open formula agrees with
closed-theory membership of any realizing representative substitution. -/
theorem denoteFormula_iff_closeFormula_mem_of_realizes
    (M : CanonicalClassModel)
    {ν : Assignment M Γ}
    {ρ : RepresentativeAssignment Γ}
    (hρ : RepresentativeAssignment.Realizes M.T ρ ν)
    (φ : Formula Γ) :
    M.denoteFormula ν φ ↔ closeFormula ρ φ ∈ M.T := by
  simpa [CanonicalClassModel.denoteFormula, CanonicalFrame.denoteFormula] using
    (holds_iff_closeFormula_of_realizes
      (T := M.T)
      M.completeConsistent
      M.existsWitness
      M.allCounterexample
      hρ
      φ)

/-- Proposition-class truth of a denoted open formula is equivalent to closed
theory membership of any realizing representative substitution. -/
theorem propClassHolds_denoteTerm_iff_closeFormula_mem_of_realizes
    (M : CanonicalClassModel)
    {ν : Assignment M Γ}
    {ρ : RepresentativeAssignment Γ}
    (hρ : RepresentativeAssignment.Realizes M.T ρ ν)
    (φ : Formula Γ) :
    M.PropClassHolds (M.denoteTerm ν φ) ↔ closeFormula ρ φ ∈ M.T := by
  rw [M.propClassHolds_denoteTerm_iff]
  exact M.denoteFormula_iff_closeFormula_mem_of_realizes hρ φ

@[simp] theorem denoteTerm_eq_falseClass_iff_not_denoteFormula
    (M : CanonicalClassModel)
    (ν : Assignment M Γ)
    (φ : Formula Γ) :
    M.denoteTerm ν φ = M.falseClass ↔ ¬ M.denoteFormula ν φ :=
  CanonicalFrame.denoteTerm_eq_falseClass_iff_not_denoteFormula
    (T := M.T) M.completeConsistent ν φ

/-- Falsity of a denoted open formula is equivalent to non-membership of any
realizing representative substitution in the canonical theory. -/
theorem denoteTerm_eq_falseClass_iff_not_mem_of_realizes
    (M : CanonicalClassModel)
    {ν : Assignment M Γ}
    {ρ : RepresentativeAssignment Γ}
    (hρ : RepresentativeAssignment.Realizes M.T ρ ν)
    (φ : Formula Γ) :
    M.denoteTerm ν φ = M.falseClass ↔ closeFormula ρ φ ∉ M.T := by
  rw [M.denoteTerm_eq_falseClass_iff_not_denoteFormula]
  simpa using not_congr (M.denoteFormula_iff_closeFormula_mem_of_realizes hρ φ)

@[simp] theorem propClassHolds_appClass_iff
    (M : CanonicalClassModel)
    (ν : Assignment M Γ)
    {σ : HTy}
    (p : Term Γ (Pred σ)) (t : Term Γ σ) :
    M.PropClassHolds
      (appClass (T := M.T) (M.denoteTerm ν p) (M.denoteTerm ν t)) ↔
        M.denoteFormula ν (.app p t) :=
  CanonicalFrame.propClassHolds_appClass_iff
    (T := M.T) M.completeConsistent ν p t

/-- The first open axiom-schema canary holds in every canonical class model. -/
theorem axiom5_holds
    (M : CanonicalClassModel)
    (ν : Assignment M [α, Pred α]) :
    M.denoteFormula ν (axiom5 (α := α)) :=
  holds_axiom5 (T := M.T) M.completeConsistent ν

/-- The extensionality axiom-schema canary also holds in every canonical class
model. -/
theorem axiom10_holds
    (M : CanonicalClassModel)
    (ν : Assignment M [σ ⇒ τ, σ ⇒ τ]) :
    M.denoteFormula ν (axiom10 (σ := σ) (τ := τ)) :=
  holds_axiom10 (T := M.T) M.completeConsistent ν

/-- At empty context, canonical class-model truth is exactly closed-theory
membership. This is the sentence-level truth lemma already available from the
current pp. 86-88 quotient-and-membership semantics. -/
theorem denoteFormula_emptyAssignment_iff_mem
    (M : CanonicalClassModel)
    (φ : Sentence) :
    M.denoteFormula M.emptyAssignment φ ↔ φ ∈ M.T := by
  change
    Mettapedia.AutoBooks.Codex.Henkin1950.closeFormula
        (ClassAssignment.chooseRepresentatives M.emptyAssignment) φ ∈ M.T ↔
      φ ∈ M.T
  exact Iff.of_eq <|
    congrArg (fun ψ : Sentence => ψ ∈ M.T) <|
      closeFormula_closed
        (ρ := ClassAssignment.chooseRepresentatives M.emptyAssignment)
        (φ := φ)

/-- Theorem 1 milestone: once Henkin's pp. 86-88 closed-theory hypotheses are
packaged into a canonical class model, every sentence already in that theory is
true in the canonical semantics under the empty assignment. The remaining gap
to the paper's full Theorem 1 is the bridge from this class-based semantics to
the paper-facing `GeneralModel` interface. -/
theorem theorem1_canonicalClassModel_milestone
    (M : CanonicalClassModel)
    {φ : Sentence}
    (hφ : φ ∈ M.T) :
    M.denoteFormula M.emptyAssignment φ := by
  exact (M.denoteFormula_emptyAssignment_iff_mem φ).2 hφ

/-- Theorem 1, class-model form: a closed theory is satisfiable when some
packaged canonical class model makes every sentence in the theory true at the
empty assignment. This isolates the current exact Codex endpoint before the
remaining bridge to `GeneralModel`. -/
def ClassSatisfiable (T : ClosedTheorySet) : Prop :=
  ∃ M : CanonicalClassModel,
    M.T = T ∧
      ∀ φ : Sentence, φ ∈ T → M.denoteFormula M.emptyAssignment φ

/-- Theorem 1 in the currently reached class-model form: every closed theory
satisfying Henkin's pp. 86-88 maximal-theory hypotheses is satisfiable in the
packaged canonical class semantics. -/
theorem theorem1_canonicalClassSatisfiable
    {T : ClosedTheorySet}
    (hT : CompleteConsistentTheory T)
    (hEx : ExistentialWitnessClosed T)
    (hAll : UniversalCounterexampleClosed T) :
    ClassSatisfiable T := by
  refine ⟨
    { T := T
      completeConsistent := hT
      existsWitness := hEx
      allCounterexample := hAll },
    rfl,
    ?_⟩
  intro φ hφ
  exact theorem1_canonicalClassModel_milestone
    (M := {
      T := T
      completeConsistent := hT
      existsWitness := hEx
      allCounterexample := hAll
    })
    hφ

/-- A canonical class model enriched with Henkin's description axiom at the
open-formula level. This is the paper-facing assumption needed to make the
description operator select witnesses in the class-based canonical semantics. -/
structure CanonicalDescriptionModel extends CanonicalClassModel where
  axiom11_holds :
    ∀ {α : HTy} (ν : ClassAssignment T [α, Pred α]),
      Holds T ν (axiom11 (α := α))

namespace CanonicalDescriptionModel

/-- Henkin's description axiom holds in the packaged class-model interface. -/
theorem denoteFormula_axiom11
    (M : CanonicalDescriptionModel)
    {α : HTy}
    (ν : M.toCanonicalClassModel.Assignment [α, Pred α]) :
    M.toCanonicalClassModel.denoteFormula ν (axiom11 (α := α)) :=
  M.axiom11_holds ν

/-- Paper-faithful description-operator witness condition in the packaged
canonical class model. If a predicate class holds of some element, it also
holds of the element selected by `ι`. -/
theorem iota_sound
    (M : CanonicalDescriptionModel)
    {α : HTy}
    {p : M.toCanonicalClassModel.Carrier (Pred α)} :
    (∃ x : M.toCanonicalClassModel.Carrier α,
      M.toCanonicalClassModel.PropClassHolds
        (appClass (T := M.T) p x)) →
      M.toCanonicalClassModel.PropClassHolds
        (appClass (T := M.T) p
          (appClass (T := M.T) (M.toCanonicalClassModel.iotaValue α) p)) := by
  intro hp
  rcases hp with ⟨x, hx⟩
  let ν : M.toCanonicalClassModel.Assignment [α, Pred α] :=
    M.toCanonicalClassModel.pointPredicateAssignment x p
  have hAnte :
      M.toCanonicalClassModel.denoteFormula ν
        (.app (.var (.vs .vz)) (.var .vz) : Formula [α, Pred α]) := by
    exact
      (M.toCanonicalClassModel.propClassHolds_appClass_iff
        (ν := ν)
        (p := (.var (.vs .vz) : Term [α, Pred α] (Pred α)))
        (t := (.var .vz : Term [α, Pred α] α))).1 <|
        by
          simpa [ν] using hx
  have hCons :
      M.toCanonicalClassModel.denoteFormula ν
        (.app (.var (.vs .vz)) (iotaTerm (.var (.vs .vz))) : Formula [α, Pred α]) := by
    exact
      ((M.toCanonicalClassModel.denoteFormula_imp_iff
        (ν := ν)
        (.app (.var (.vs .vz)) (.var .vz))
        (.app (.var (.vs .vz)) (iotaTerm (.var (.vs .vz))))).1
        (M.denoteFormula_axiom11 ν))
        hAnte
  exact
    by
      simpa [ν] using
        (M.toCanonicalClassModel.propClassHolds_appClass_iff
          (ν := ν)
          (p := (.var (.vs .vz) : Term [α, Pred α] (Pred α)))
          (t := iotaTerm (.var (.vs .vz) : Term [α, Pred α] (Pred α)))).2 hCons

/-- Formula-level description canary in the one-predicate context. If the
predicate variable holds of some class-model element, it also holds of the
element chosen by `ι`. -/
theorem denoteFormula_app_iotaTerm_of_exists
    (M : CanonicalDescriptionModel)
    {α : HTy}
    (ν : M.toCanonicalClassModel.Assignment [Pred α]) :
    (∃ x : M.toCanonicalClassModel.Carrier α,
      M.toCanonicalClassModel.denoteFormula (ClassAssignment.extend ν x)
        (.app (.var (.vs .vz)) (.var .vz) : Formula [α, Pred α])) →
      M.toCanonicalClassModel.denoteFormula ν
        (.app (.var .vz) (iotaTerm (.var .vz)) : Formula [Pred α]) := by
  intro hp
  have hWitness :
      ∃ x : M.toCanonicalClassModel.Carrier α,
        M.toCanonicalClassModel.PropClassHolds
          (appClass (T := M.T) (ν (.vz : Var [Pred α] (Pred α))) x) := by
    rcases hp with ⟨x, hx⟩
    refine ⟨x, ?_⟩
    simpa [ClassAssignment.extend] using
      (M.toCanonicalClassModel.propClassHolds_appClass_iff
        (ν := ClassAssignment.extend ν x)
        (p := (.var (.vs .vz) : Term [α, Pred α] (Pred α)))
        (t := (.var .vz : Term [α, Pred α] α))).2 hx
  have hChosen :
      M.toCanonicalClassModel.PropClassHolds
        (appClass (T := M.T)
          (ν (.vz : Var [Pred α] (Pred α)))
          (appClass (T := M.T)
            (M.toCanonicalClassModel.iotaValue α)
            (ν (.vz : Var [Pred α] (Pred α))))) :=
    M.iota_sound (α := α) (p := ν (.vz : Var [Pred α] (Pred α))) hWitness
  exact
    (M.toCanonicalClassModel.propClassHolds_appClass_iff
      (ν := ν)
      (p := (.var (.vz : Var [Pred α] (Pred α)) : Term [Pred α] (Pred α)))
      (t := iotaTerm (.var (.vz : Var [Pred α] (Pred α)) : Term [Pred α] (Pred α)))).1 <|
      by
        simpa using hChosen

/-- General-context description canary: if a predicate term has a witness under
an extended assignment, then the same predicate term holds of its `ι`-chosen
element in the original assignment. -/
theorem denoteFormula_app_iotaTerm_of_exists_general
    (M : CanonicalDescriptionModel)
    {Γ : Ctx Atom} {α : HTy}
    (ν : M.toCanonicalClassModel.Assignment Γ)
    (p : Term Γ (Pred α)) :
    (∃ x : M.toCanonicalClassModel.Carrier α,
      M.toCanonicalClassModel.denoteFormula (ClassAssignment.extend ν x)
        (.app (weaken (Base := Atom) (Const := Primitive) (σ := α) p) (.var .vz)
          : Formula (α :: Γ))) →
      M.toCanonicalClassModel.denoteFormula ν (.app p (iotaTerm p) : Formula Γ) := by
  intro hp
  have hWitness :
      ∃ x : M.toCanonicalClassModel.Carrier α,
        M.toCanonicalClassModel.PropClassHolds
          (appClass (T := M.T) (M.toCanonicalClassModel.denoteTerm ν p) x) := by
    rcases hp with ⟨x, hx⟩
    refine ⟨x, ?_⟩
    simpa [ClassAssignment.extend] using
      (M.toCanonicalClassModel.propClassHolds_appClass_iff
        (ν := ClassAssignment.extend ν x)
        (p := weaken (Base := Atom) (Const := Primitive) (σ := α) p)
        (t := (.var .vz : Term (α :: Γ) α))).2 hx
  have hChosen :
      M.toCanonicalClassModel.PropClassHolds
        (appClass (T := M.T)
          (M.toCanonicalClassModel.denoteTerm ν p)
          (appClass (T := M.T)
            (M.toCanonicalClassModel.iotaValue α)
            (M.toCanonicalClassModel.denoteTerm ν p))) :=
    M.iota_sound (α := α) (p := M.toCanonicalClassModel.denoteTerm ν p) hWitness
  exact
    (M.toCanonicalClassModel.propClassHolds_appClass_iff
      (ν := ν)
      (p := p)
      (t := iotaTerm p)).1 <|
      by
        simpa using hChosen

/-- Semantic description-axiom instance for an arbitrary predicate term in the
packaged canonical description model. -/
theorem denoteFormula_description_instance
    (M : CanonicalDescriptionModel)
    {Γ : Ctx Atom} {α : HTy}
    (ν : M.toCanonicalClassModel.Assignment Γ)
    (p : Term Γ (Pred α)) :
    M.toCanonicalClassModel.denoteFormula ν
      (imp
        (.ex (.app (weaken (Base := Atom) (Const := Primitive) (σ := α) p) (.var .vz)))
        (.app p (iotaTerm p)) : Formula Γ) := by
  rw [M.toCanonicalClassModel.denoteFormula_imp_iff]
  intro hEx
  exact
    M.denoteFormula_app_iotaTerm_of_exists_general ν p <|
      (M.toCanonicalClassModel.denoteFormula_ex_iff
        (ν := ν)
        (.app (weaken (Base := Atom) (Const := Primitive) (σ := α) p) (.var .vz))).1 hEx

/-- The arbitrary-context semantic description instance belongs to the closed
theory for any quotient-valued class assignment. -/
theorem classAssignment_closeFormula_description_instance_mem
    (M : CanonicalDescriptionModel)
    {Γ : Ctx Atom} {α : HTy}
    (ν : M.toCanonicalClassModel.Assignment Γ)
    (p : Term Γ (Pred α)) :
    ClassAssignment.closeFormula ν
      (imp
        (.ex (.app (weaken (Base := Atom) (Const := Primitive) (σ := α) p) (.var .vz)))
        (.app p (iotaTerm p)) : Formula Γ) ∈ M.T := by
  simpa [CanonicalClassModel.denoteFormula, CanonicalFrame.denoteFormula, Holds] using
    M.denoteFormula_description_instance ν p

/-- Stronger truth-lemma canary: any realizing representative assignment closes
the arbitrary-context semantic description instance to a formula already in the
canonical theory. -/
theorem closeFormula_description_instance_mem_of_realizes
    (M : CanonicalDescriptionModel)
    {Γ : Ctx Atom} {α : HTy}
    {ν : M.toCanonicalClassModel.Assignment Γ}
    {ρ : RepresentativeAssignment Γ}
    (hρ : RepresentativeAssignment.Realizes M.T ρ ν)
    (p : Term Γ (Pred α)) :
    closeFormula ρ
      (imp
        (.ex (.app (weaken (Base := Atom) (Const := Primitive) (σ := α) p) (.var .vz)))
        (.app p (iotaTerm p)) : Formula Γ) ∈ M.T := by
  exact
    (holds_iff_closeFormula_of_realizes
      (T := M.T)
      M.toCanonicalClassModel.completeConsistent
      M.toCanonicalClassModel.existsWitness
      M.toCanonicalClassModel.allCounterexample
      hρ
      (imp
        (.ex (.app (weaken (Base := Atom) (Const := Primitive) (σ := α) p) (.var .vz)))
        (.app p (iotaTerm p)) : Formula Γ)).mp <|
      M.denoteFormula_description_instance ν p

/-- Specialization of the arbitrary-context description instance to Henkin's
open axiom 11 context. -/
theorem classAssignment_closeFormula_axiom11_mem
    (M : CanonicalDescriptionModel)
    {α : HTy}
    (ν : M.toCanonicalClassModel.Assignment [α, Pred α]) :
    ClassAssignment.closeFormula ν (axiom11 (α := α)) ∈ M.T := by
  simpa [CanonicalClassModel.denoteFormula, CanonicalFrame.denoteFormula, Holds] using
    M.denoteFormula_axiom11 ν

/-- Realizing-representative specialization of the arbitrary-context
description-instance membership theorem to axiom 11. -/
theorem closeFormula_axiom11_mem_of_realizes
    (M : CanonicalDescriptionModel)
    {α : HTy}
    {ν : M.toCanonicalClassModel.Assignment [α, Pred α]}
    {ρ : RepresentativeAssignment [α, Pred α]}
    (hρ : RepresentativeAssignment.Realizes M.T ρ ν) :
    closeFormula ρ (axiom11 (α := α)) ∈ M.T := by
  exact
    (holds_iff_closeFormula_of_realizes
      (T := M.T)
      M.toCanonicalClassModel.completeConsistent
      M.toCanonicalClassModel.existsWitness
      M.toCanonicalClassModel.allCounterexample
      hρ
      (axiom11 (α := α))).mp <|
      M.denoteFormula_axiom11 ν

end CanonicalDescriptionModel

end CanonicalClassModel

end Mettapedia.AutoBooks.Codex.Henkin1950
