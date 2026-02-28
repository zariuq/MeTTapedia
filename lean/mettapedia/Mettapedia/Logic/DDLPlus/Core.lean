import Mathlib.Tactic

/-!
# Carmo-Jones Dyadic Deontic Logic (DDL+) — Core Types and Operators

Shallow semantic embedding of Carmo and Jones' Dyadic Deontic Logic (DDL),
extended with Kaplanian two-dimensional semantics. This is a Lean 4 port of
the Isabelle/HOL formalization from `GewirthPGCProof/CJDDLplus.thy` and
`GewirthPGCProof/ExtendedDDL.thy`.

## Architecture

- §1 Types: worlds, entities, contexts, propositions, meanings
- §2 DDLPlusFrame: accessibility relations + obligation with semantic conditions
- §3 Set-theoretic operations on world-propositions
- §4 Propositional logic connectives in the embedding
- §5 Modal operators: □ₐ, ◇ₐ, □ₚ, ◇ₚ, □ˢ⁵, ◇ˢ⁵
- §6 Deontic operators: O⟨φ|σ⟩, Oₐ, Oᵢ
- §7 Validity: modal validity, Kaplanian context, LD validity, □ᴰ
- §8 Higher-order quantifiers in the embedding

## References

- Carmo, J. & Jones, A. (2002). "Deontic Logic and Contrary-to-Duties"
- Kaplan, D. (1989). "Demonstratives"
- Benzmüller, C. et al. (2018). "A Dyadic Deontic Logic in HOL"
- `GewirthPGCProof/CJDDLplus.thy` (Isabelle source)
- `GewirthPGCProof/ExtendedDDL.thy` (Isabelle source)
-/

namespace Mettapedia.Logic.DDLPlus.Core

/-! ## §1 Types

Propositions are truth-sets over worlds (shallow embedding).
Meanings are context-dependent propositions (Kaplan's "characters"). -/

/-- World-proposition: a proposition identified with its truth-set over worlds `w`.
    Corresponds to Isabelle type `wo = w ⇒ bool`. -/
abbrev WProp (w : Type*) := w → Prop

/-- Meaning (Kaplan's "character"): a context-dependent world-proposition.
    Corresponds to Isabelle type `m = c ⇒ w ⇒ bool`. -/
abbrev Meaning (c w : Type*) := c → w → Prop

/-! ## §2 DDLPlusFrame

The semantic foundation of DDL+. A frame bundles two accessibility relations
(`av`, `pv`) and a dyadic obligation relation (`ob`) satisfying the five
semantic conditions from Carmo & Jones (2002), pp. 290ff.

All conditions are **structure fields** (not axioms), so every theorem
about frames is a genuine theorem, not an axiom consequence. -/

/-- A Carmo-Jones DDL+ frame over possible worlds `w`.

    - `av`: actual-version accessibility ("open alternatives")
    - `pv`: possible-version accessibility ("potential alternatives")
    - `ob`: dyadic obligation on world-propositions

    The semantic conditions `sem_3a`–`sem_5e` match `CJDDLplus.thy:51–59`. -/
structure DDLPlusFrame (w : Type*) where
  /-- Actual-version accessibility: `av v v'` means `v'` is an open alternative of `v`. -/
  av : w → w → Prop
  /-- Possible-version accessibility: `pv v v'` means `v'` is a potential alternative of `v`. -/
  pv : w → w → Prop
  /-- Dyadic obligation: `ob X Y` means "Y is obligatory in context X". -/
  ob : WProp w → WProp w → Prop
  /-- sem_3a: `av` is serial (every world has an open alternative).
      CJDDLplus.thy:52 -/
  sem_3a : ∀ v, ∃ v', av v v'
  /-- sem_4a: open alternatives are possible alternatives (`av ⊆ pv`).
      CJDDLplus.thy:53 -/
  sem_4a : ∀ v v', av v v' → pv v v'
  /-- sem_4b: `pv` is reflexive.
      CJDDLplus.thy:54 -/
  sem_4b : ∀ v, pv v v
  /-- sem_5a: contradictions cannot be obligatory.
      CJDDLplus.thy:55 -/
  sem_5a : ∀ X, ¬ ob X (fun _ => False)
  /-- sem_5b: obligation respects set-equality of intersections.
      CJDDLplus.thy:56 -/
  sem_5b : ∀ X Y Z, (∀ v, (X v ∧ Y v) ↔ (X v ∧ Z v)) → (ob X Y ↔ ob X Z)
  /-- sem_5c: if X ∩ Y ∩ Z is instantiated and both ob(X,Y) and ob(X,Z),
      then ob(X, Y ∩ Z). CJDDLplus.thy:57 -/
  sem_5c : ∀ X Y Z, (∃ v, X v ∧ Y v ∧ Z v) → ob X Y → ob X Z →
    ob X (fun v => Y v ∧ Z v)
  /-- sem_5d: obligation transfer under subset inclusion.
      CJDDLplus.thy:58 -/
  sem_5d : ∀ X Y Z, (∀ v, Y v → X v) → ob X Y → (∀ v, X v → Z v) →
    ob Z (fun v => (Z v ∧ ¬ X v) ∨ Y v)
  /-- sem_5e: obligation restriction to subsets.
      CJDDLplus.thy:59 -/
  sem_5e : ∀ X Y Z, (∀ v, Y v → X v) → ob X Z → (∃ v, Y v ∧ Z v) → ob Y Z

namespace DDLPlusFrame

variable {w : Type*} (F : DDLPlusFrame w)

/-! ### Derived semantic lemmas (from CJDDLplus.thy:65–75) -/

/-- sem_5b1: `ob X Y → ob X (Y ∩ X)`. CJDDLplus.thy:65 -/
theorem sem_5b1 {X Y : WProp w} (h : F.ob X Y) : F.ob X (fun v => Y v ∧ X v) := by
  have key : ∀ v, (X v ∧ Y v) ↔ (X v ∧ (Y v ∧ X v)) := fun v =>
    ⟨fun ⟨hx, hy⟩ => ⟨hx, hy, hx⟩, fun ⟨hx, hy, _⟩ => ⟨hx, hy⟩⟩
  exact (F.sem_5b X Y _ key).mp h

/-- sem_5b2: `ob X (Y ∩ X) → ob X Y`. CJDDLplus.thy:66 -/
theorem sem_5b2 {X Y : WProp w} (h : F.ob X (fun v => Y v ∧ X v)) : F.ob X Y := by
  have key : ∀ v, (X v ∧ (Y v ∧ X v)) ↔ (X v ∧ Y v) := fun v =>
    ⟨fun ⟨hx, hy, _⟩ => ⟨hx, hy⟩, fun ⟨hx, hy⟩ => ⟨hx, hy, hx⟩⟩
  exact (F.sem_5b X _ Y key).mp h

/-- sem_5ab: `ob X Y → ∃ v, X v ∧ Y v` (obligation implies instantiation).
    CJDDLplus.thy:67 -/
theorem sem_5ab {X Y : WProp w} (h : F.ob X Y) : ∃ v, X v ∧ Y v := by
  by_contra hc
  push_neg at hc
  have key : ∀ v, (X v ∧ Y v) ↔ (X v ∧ False) := fun v =>
    ⟨fun ⟨hx, hy⟩ => absurd hy (hc v hx), fun ⟨_, hf⟩ => hf.elim⟩
  exact F.sem_5a X ((F.sem_5b X Y _ key).mp h)

/-- sem_5bd2: `ob X Y ∧ X ⊆ Z → ob Z ((Z ∩ ¬X) ∪ Y)`.
    CJDDLplus.thy:69 -/
theorem sem_5bd2 {X Y Z : WProp w} (hob : F.ob X Y) (hsub : ∀ v, X v → Z v) :
    F.ob Z (fun v => (Z v ∧ ¬ X v) ∨ Y v) := by
  have h1 := F.sem_5b1 hob  -- ob X (Y ∩ X)
  have h2 := F.sem_5d X (fun v => Y v ∧ X v) Z (fun v h => h.2) h1 hsub
  -- h2 : ob Z (fun v => (Z v ∧ ¬ X v) ∨ (Y v ∧ X v))
  -- Bridge via sem_5b: (Y ∧ X) → Y weakens the disjunct under Z-intersection
  exact (F.sem_5b Z _ _ (fun v => ⟨
    fun ⟨hz, hor⟩ => ⟨hz, hor.elim (fun h => Or.inl h) (fun ⟨hy, _⟩ => Or.inr hy)⟩,
    fun ⟨hz, hor⟩ => ⟨hz, hor.elim Or.inl (fun hy => by
      by_cases hx : X v
      · exact Or.inr ⟨hy, hx⟩
      · exact Or.inl ⟨hz, hx⟩)⟩⟩)).mp h2

/-- sem_5bd3: `ob X Y ∧ X ⊆ Z → ob Z (¬X ∪ Y)`.
    CJDDLplus.thy:70 -/
theorem sem_5bd3 {X Y Z : WProp w} (hob : F.ob X Y) (hsub : ∀ v, X v → Z v) :
    F.ob Z (fun v => ¬ X v ∨ Y v) := by
  have h := F.sem_5bd2 hob hsub
  exact (F.sem_5b Z _ _ (fun v => by
    constructor
    · intro ⟨hz, hor⟩
      exact ⟨hz, hor.elim (fun ⟨_, hnx⟩ => Or.inl hnx) Or.inr⟩
    · intro ⟨hz, hor⟩
      exact ⟨hz, hor.elim (fun hnx => Or.inl ⟨hz, hnx⟩) Or.inr⟩)).1 h

/-- sem_5bd4: `ob X Y ∧ X ⊆ Z → ob Z (¬X ∪ (X ∩ Y))`.
    CJDDLplus.thy:71 -/
theorem sem_5bd4 {X Y Z : WProp w} (hob : F.ob X Y) (hsub : ∀ v, X v → Z v) :
    F.ob Z (fun v => ¬ X v ∨ (X v ∧ Y v)) := by
  have h := F.sem_5bd3 hob hsub  -- ob Z (¬X ∨ Y)
  exact (F.sem_5b Z _ _ (fun v => by
    constructor
    · intro ⟨hz, hor⟩
      exact ⟨hz, hor.elim Or.inl (fun hy => by
        by_cases hx : X v
        · exact Or.inr ⟨hx, hy⟩
        · exact Or.inl hx)⟩
    · intro ⟨hz, hor⟩
      exact ⟨hz, hor.elim Or.inl (fun ⟨_, hy⟩ => Or.inr hy)⟩)).1 h

end DDLPlusFrame

/-! ## §3 Set-Theoretic Operations on WProp

Named operations matching the Isabelle abbreviations (CJDDLplus.thy:35–42). -/

section SetOps

variable {w : Type*}

/-- Subset relation on world-propositions. -/
abbrev WProp.subset (α β : WProp w) : Prop := ∀ v, α v → β v

/-- Intersection of world-propositions. -/
abbrev WProp.inter (α β : WProp w) : WProp w := fun v => α v ∧ β v

/-- Union of world-propositions. -/
abbrev WProp.union (α β : WProp w) : WProp w := fun v => α v ∨ β v

/-- Complement of a world-proposition. -/
abbrev WProp.compl (α : WProp w) : WProp w := fun v => ¬ α v

/-- A world-proposition is instantiated if it holds at some world. -/
abbrev WProp.instantiated (α : WProp w) : Prop := ∃ v, α v

/-- Set-equality of world-propositions. -/
abbrev WProp.setEq (α β : WProp w) : Prop := ∀ v, α v ↔ β v

end SetOps

/-! ## §4 Propositional Logic in the Embedding

Pointwise lifting of propositional connectives to `Meaning c w`.
Matches CJDDLplus.thy:80–84. -/

section PropLogic

variable {c w : Type*}

/-- Conjunction in the embedding. -/
abbrev pand (φ ψ : Meaning c w) : Meaning c w := fun ctx v => φ ctx v ∧ ψ ctx v

/-- Disjunction in the embedding. -/
abbrev por (φ ψ : Meaning c w) : Meaning c w := fun ctx v => φ ctx v ∨ ψ ctx v

/-- Implication in the embedding. -/
abbrev pimp (φ ψ : Meaning c w) : Meaning c w := fun ctx v => φ ctx v → ψ ctx v

/-- Biconditional in the embedding. -/
abbrev pequ (φ ψ : Meaning c w) : Meaning c w := fun ctx v => φ ctx v ↔ ψ ctx v

/-- Negation in the embedding. -/
abbrev pnot (φ : Meaning c w) : Meaning c w := fun ctx v => ¬ φ ctx v

/-- Verum in the embedding. -/
abbrev ptop : Meaning c w := fun _ _ => True

/-- Falsum in the embedding. -/
abbrev pbot : Meaning c w := fun _ _ => False

end PropLogic

/-! ## §5 Modal Operators

Box and diamond for the two accessibility relations (`av`, `pv`) and
the unrestricted S5 quantification. Matches CJDDLplus.thy:87–93, 125–126. -/

section ModalOps

variable {c w : Type*} (F : DDLPlusFrame w)

/-- Actual necessity: □ₐφ = "φ holds in all actual alternatives".
    CJDDLplus.thy:87 -/
def box_a (φ : Meaning c w) : Meaning c w :=
  fun ctx v => ∀ v', F.av v v' → φ ctx v'

/-- Actual possibility: ◇ₐφ = "φ holds in some actual alternative".
    CJDDLplus.thy:88 -/
def dia_a (φ : Meaning c w) : Meaning c w :=
  fun ctx v => ∃ v', F.av v v' ∧ φ ctx v'

/-- Possible/ideal necessity: □ₚφ = "φ holds in all possible alternatives".
    CJDDLplus.thy:89 -/
def box_p (φ : Meaning c w) : Meaning c w :=
  fun ctx v => ∀ v', F.pv v v' → φ ctx v'

/-- Possible/ideal possibility: ◇ₚφ = "φ holds in some possible alternative".
    CJDDLplus.thy:90 -/
def dia_p (φ : Meaning c w) : Meaning c w :=
  fun ctx v => ∃ v', F.pv v v' ∧ φ ctx v'

/-- S5 necessity: □ˢ⁵φ = "φ holds at all worlds" (unrestricted).
    CJDDLplus.thy:125 -/
def box_S5 (φ : Meaning c w) : Meaning c w :=
  fun ctx _ => ∀ v, φ ctx v

/-- S5 possibility: ◇ˢ⁵φ = "φ holds at some world" (unrestricted).
    CJDDLplus.thy:126 -/
def dia_S5 (φ : Meaning c w) : Meaning c w :=
  fun ctx _ => ∃ v, φ ctx v

end ModalOps

/-! ## §6 Deontic Operators

The three deontic operators: conditional obligation O⟨φ|σ⟩,
actual obligation Oₐ, and ideal obligation Oᵢ.
Matches CJDDLplus.thy:95–97. -/

section DeonticOps

variable {c w : Type*} (F : DDLPlusFrame w)

/-- Conditional obligation: O⟨φ|σ⟩ = "φ is obligatory given context σ".
    Uses the ground-level `ob` on world-propositions.
    CJDDLplus.thy:95 -/
def cond_obl (φ σ : Meaning c w) : Meaning c w :=
  fun ctx _ => F.ob (σ ctx) (φ ctx)

/-- Actual obligation: Oₐφ = "φ is obligatory given actual alternatives,
    and there exists an actual alternative where φ fails" (violation possible).
    CJDDLplus.thy:96 -/
def actual_obl (φ : Meaning c w) : Meaning c w :=
  fun ctx v => F.ob (F.av v) (φ ctx) ∧ ∃ v', F.av v v' ∧ ¬ φ ctx v'

/-- Ideal obligation: Oᵢφ = "φ is obligatory given possible alternatives,
    and there exists a possible alternative where φ fails" (violation possible).
    CJDDLplus.thy:97 -/
def ideal_obl (φ : Meaning c w) : Meaning c w :=
  fun ctx v => F.ob (F.pv v) (φ ctx) ∧ ∃ v', F.pv v v' ∧ ¬ φ ctx v'

end DeonticOps

/-! ## §7 Validity

Two notions of validity and truth in context. -/

section Validity

variable {c w : Type*}

/-- Classical modal validity: true at all contexts and all worlds.
    CJDDLplus.thy:101 -/
def modal_valid (φ : Meaning c w) : Prop := ∀ ctx v, φ ctx v

/-- Context-dependent modal validity: true at all worlds for a given context.
    CJDDLplus.thy:100 -/
def modal_valid_ctx (φ : Meaning c w) (ctx : c) : Prop := ∀ v, φ ctx v

end Validity

/-! ### Kaplanian Context

A Kaplanian context pairs an agent with a world. This enables two-dimensional
semantics where LD validity (truth in all contexts at their own worlds) is
strictly weaker than classical modal validity. ExtendedDDL.thy:35–46. -/

/-- A Kaplanian context structure pairing agents with worlds.
    ExtendedDDL.thy:35–36 -/
structure KaplanianContext (c w e : Type*) where
  /-- Retrieves the agent of context `ctx`. -/
  agent : c → e
  /-- Retrieves the world of context `ctx`. -/
  world : c → w

namespace KaplanianContext

variable {c w e : Type*} (kc : KaplanianContext c w e)

/-- Truth in a given context: φ evaluated at context `ctx` and its world.
    ExtendedDDL.thy:42 -/
def ldTrue (φ : Meaning c w) (ctx : c) : Prop := φ ctx (kc.world ctx)

/-- LD validity (indexical validity): true in every context at its own world.
    Strictly weaker than classical modal validity.
    ExtendedDDL.thy:46 -/
def ld_valid (φ : Meaning c w) : Prop := ∀ ctx, kc.ldTrue φ ctx

/-- A priori necessity operator: □ᴰφ is true iff φ is LD-valid.
    Works analogously to S5 box over contexts.
    ExtendedDDL.thy:66 -/
def box_D (φ : Meaning c w) : Meaning c w :=
  fun _ _ => kc.ld_valid φ

/-- LD validity is weaker than modal validity.
    ExtendedDDL.thy:49 -/
theorem modal_implies_ld (φ : Meaning c w) :
    modal_valid φ → kc.ld_valid φ :=
  fun h ctx => h ctx (kc.world ctx)

/-- Necessitation works for LD validity with □ᴰ.
    ExtendedDDL.thy:70 -/
theorem NecLD (φ : Meaning c w) :
    kc.ld_valid φ → kc.ld_valid (kc.box_D φ) :=
  fun h _ => h

/-- □ᴰφ at context C is equivalent to ∀ ctx, φ at its world.
    ExtendedDDL.thy:67 -/
theorem box_D_unfold (φ : Meaning c w) (C : c) :
    kc.ldTrue (kc.box_D φ) C ↔ (∀ ctx, kc.ldTrue φ ctx) :=
  Iff.rfl

end KaplanianContext

/-! ## §8 Higher-Order Quantifiers

Quantifiers lifted to the embedding, matching ExtendedDDL.thy:78–81. -/

section Quantifiers

variable {c w : Type*}

/-- Universal quantification in the embedding. -/
abbrev mforall {α : Type*} (Φ : α → Meaning c w) : Meaning c w :=
  fun ctx v => ∀ x, Φ x ctx v

/-- Existential quantification in the embedding. -/
abbrev mexists {α : Type*} (Φ : α → Meaning c w) : Meaning c w :=
  fun ctx v => ∃ x, Φ x ctx v

end Quantifiers

/-! ## §9 Necessitation Rules

Classical necessitation (valid only under modal validity, not LD validity).
CJDDLplus.thy:120–121. -/

section Necessitation

variable {c w : Type*} (F : DDLPlusFrame w)

/-- Necessitation for □ₐ under modal validity.
    CJDDLplus.thy:120 -/
theorem NecDDLa (φ : Meaning c w) :
    modal_valid φ → modal_valid (box_a F φ) :=
  fun h ctx _ _ _ => h ctx _

/-- Necessitation for □ₚ under modal validity.
    CJDDLplus.thy:121 -/
theorem NecDDLp (φ : Meaning c w) :
    modal_valid φ → modal_valid (box_p F φ) :=
  fun h ctx _ _ _ => h ctx _

end Necessitation

end Mettapedia.Logic.DDLPlus.Core
