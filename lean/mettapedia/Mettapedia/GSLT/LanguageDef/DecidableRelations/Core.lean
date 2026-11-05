import Mettapedia.OSLF.MeTTaIL.ReferenceStep
import Mathlib.Data.Set.Lattice

/-!
# Complemented relations in a region

A GSLT's premises are positive: a premise holds when it has a derivation. A rule can still depend on the failure of a
relation where the relation is **complemented** in a region. That means it is paired with a complement relation, also
positive, such that wherever the region holds exactly one of the two does. In the lattice of predicates on the region
the two are complements (`complemented_iff_isCompl`).

Inside the region the facts are complete, so the failure of the relation is witnessed by a derivation of its
complement:
- a rule premise on the complement is negation as failure, sound and complete there
  (`Complemented.complement_iff_not`);
- the relation is decidable there (`Complemented.decidable`).

Outside the region, reasoning stays open-world.

Complemented relations in one region form a Boolean algebra of witnessed facts. They are closed under:
- complement (`Complemented.symm`);
- conjunction and disjunction (`Complemented.and`, `Complemented.or`);
- quantification over finite lists (`Complemented.all`, `Complemented.any`).

They also restrict to smaller regions and pull back along maps.

A language has two sources of complemented relations:
- **judgments** it derives by its own rules. `Derives relEnv language judgment arguments` holds when the language
  steps `judgment(arguments)` to `Yes`.
- **stores** answering relation queries. `Answers relEnv language relation arguments` holds when the relation
  environment, or a built-in relation, answers `relation(arguments)`.

A `Decision` is a computable verdict, witnessed on both sides in the region.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.DecidableRelations

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine

universe u v

/-! ## Complemented relations -/

/-- **A relation complemented in a region**: wherever `region` holds, exactly one of `holds` and `fails` does. -/
structure Complemented {α : Type u} (holds fails region : α → Prop) : Prop where
  disjoint : ∀ a, region a → holds a → fails a → False
  exhaustive : ∀ a, region a → holds a ∨ fails a

namespace Complemented

variable {α : Type u} {holds fails region : α → Prop}

/-- **Negation as failure, in the region**: the complement holds exactly where the relation fails. -/
theorem complement_iff_not (complemented : Complemented holds fails region) {a : α} (inside : region a) :
    fails a ↔ ¬ holds a :=
  ⟨fun failed held => complemented.disjoint a inside held failed,
    fun notHeld => (complemented.exhaustive a inside).resolve_left notHeld⟩

/-- The relation holds exactly where its complement fails. -/
theorem holds_iff_not_complement (complemented : Complemented holds fails region) {a : α} (inside : region a) :
    holds a ↔ ¬ fails a :=
  ⟨fun held failed => complemented.disjoint a inside held failed,
    fun notFailed => (complemented.exhaustive a inside).resolve_right notFailed⟩

/-- **A complemented relation is decidable in the region**, constructively: it holds or it does not. -/
theorem decidable (complemented : Complemented holds fails region) {a : α} (inside : region a) :
    holds a ∨ ¬ holds a :=
  (complemented.exhaustive a inside).imp id fun failed held => complemented.disjoint a inside held failed

/-- The complement is complemented, with the relation as its complement. -/
theorem symm (complemented : Complemented holds fails region) : Complemented fails holds region :=
  ⟨fun a inside failed held => complemented.disjoint a inside held failed,
    fun a inside => (complemented.exhaustive a inside).symm⟩

/-- A relation complemented in a region is complemented in every smaller one. -/
theorem restrict (complemented : Complemented holds fails region) {smaller : α → Prop}
    (within : ∀ a, smaller a → region a) : Complemented holds fails smaller :=
  ⟨fun a inside => complemented.disjoint a (within a inside), fun a inside => complemented.exhaustive a (within a inside)⟩

/-- A complemented relation pulls back along a map. -/
theorem comap {β : Type v} (complemented : Complemented holds fails region) (map : β → α) :
    Complemented (fun b => holds (map b)) (fun b => fails (map b)) (fun b => region (map b)) :=
  ⟨fun b inside => complemented.disjoint (map b) inside, fun b inside => complemented.exhaustive (map b) inside⟩

variable {holds₁ fails₁ holds₂ fails₂ : α → Prop}

/-- **Conjunction**: both hold, or one of the complements does. -/
theorem and (first : Complemented holds₁ fails₁ region) (second : Complemented holds₂ fails₂ region) :
    Complemented (fun a => holds₁ a ∧ holds₂ a) (fun a => fails₁ a ∨ fails₂ a) region where
  disjoint a inside held failed := failed.elim (first.disjoint a inside held.1) (second.disjoint a inside held.2)
  exhaustive a inside :=
    match first.exhaustive a inside, second.exhaustive a inside with
    | .inl held₁, .inl held₂ => .inl ⟨held₁, held₂⟩
    | .inr failed₁, _ => .inr (.inl failed₁)
    | _, .inr failed₂ => .inr (.inr failed₂)

/-- **Disjunction**: one holds, or both complements do. -/
theorem or (first : Complemented holds₁ fails₁ region) (second : Complemented holds₂ fails₂ region) :
    Complemented (fun a => holds₁ a ∨ holds₂ a) (fun a => fails₁ a ∧ fails₂ a) region :=
  (first.symm.and second.symm).symm

/-- **Every element of a finite list**: all hold, or some element's complement does. -/
theorem all (complemented : Complemented holds fails region) :
    Complemented (fun as : List α => ∀ a ∈ as, holds a) (fun as => ∃ a ∈ as, fails a)
      (fun as => ∀ a ∈ as, region a) where
  disjoint as inside held failed := by
    obtain ⟨a, member, failedAt⟩ := failed
    exact complemented.disjoint a (inside a member) (held a member) failedAt
  exhaustive as inside := by
    by_cases some : ∃ a ∈ as, fails a
    · exact .inr some
    · refine .inl fun a member => ?_
      exact (complemented.exhaustive a (inside a member)).resolve_right fun failedAt => some ⟨a, member, failedAt⟩

/-- **Some element of a finite list**: one holds, or every element's complement does. -/
theorem any (complemented : Complemented holds fails region) :
    Complemented (fun as : List α => ∃ a ∈ as, holds a) (fun as => ∀ a ∈ as, fails a)
      (fun as => ∀ a ∈ as, region a) :=
  complemented.symm.all.symm

end Complemented

/-- **Complemented relations are complements** in the lattice of predicates on the region. -/
theorem complemented_iff_isCompl {α : Type u} {holds fails region : α → Prop} :
    Complemented holds fails region ↔
      IsCompl {a : {a // region a} | holds a.1} {a : {a // region a} | fails a.1} := by
  rw [isCompl_iff, Set.disjoint_iff, codisjoint_iff]
  constructor
  · intro complemented
    refine ⟨fun a both => complemented.disjoint a.1 a.2 both.1 both.2, eq_top_iff.mpr fun a _ => ?_⟩
    exact complemented.exhaustive a.1 a.2
  · rintro ⟨separate, cover⟩
    refine ⟨fun a inside held failed => @separate ⟨a, inside⟩ ⟨held, failed⟩, fun a inside => ?_⟩
    have covered : (⟨a, inside⟩ : {a // region a}) ∈
        ({a : {a // region a} | holds a.1} ⊔ {a : {a // region a} | fails a.1}) := by
      rw [cover]; trivial
    exact covered

/-- **A decision** for a relation in a region: a computable verdict, witnessed on both sides there. -/
structure Decision {α : Type u} (holds fails region : α → Prop) where
  decide : α → Bool
  holds_of_true : ∀ a, region a → decide a = true → holds a
  fails_of_false : ∀ a, region a → decide a = false → fails a

/-- A decision together with exclusivity decides the relation. -/
theorem Decision.complemented {α : Type u} {holds fails region : α → Prop} (decision : Decision holds fails region)
    (disjoint : ∀ a, region a → holds a → fails a → False) : Complemented holds fails region where
  disjoint := disjoint
  exhaustive a inside := by
    cases verdict : decision.decide a
    · exact .inr (decision.fails_of_false a inside verdict)
    · exact .inl (decision.holds_of_true a inside verdict)

/-- In the region of a complemented relation, a decision's verdict is the truth of the relation. -/
theorem Decision.decide_eq_true_iff {α : Type u} {holds fails region : α → Prop}
    (decision : Decision holds fails region) (complemented : Complemented holds fails region) {a : α} (inside : region a) :
    decision.decide a = true ↔ holds a := by
  constructor
  · exact decision.holds_of_true a inside
  · intro held
    cases verdict : decision.decide a
    · exact (complemented.disjoint a inside held (decision.fails_of_false a inside verdict)).elim
    · rfl

/-! ## Judgments and stores -/

/-- The verdict a judgment steps to when it holds. -/
def yes : Pattern := .apply "Yes" []

/-- **A judgment of the language**: the language steps `judgment(arguments)` to `Yes`. -/
def Derives (relEnv : RelationEnv) (language : LanguageDef) (judgment : String) (arguments : List Pattern) : Prop :=
  ∃ witness, Mettapedia.OSLF.MeTTaIL.ReferenceStep.StepValid relEnv language (.apply judgment arguments) witness yes

/-- **A store's answer**: the relation environment, or a built-in relation, answers the query `relation(arguments)`
from no bindings, as a rule's premise `relation(arguments)` is answered. -/
def Answers (relEnv : RelationEnv) (language : LanguageDef) (relation : String) (arguments : List Pattern) : Prop :=
  relationQueryStep relEnv language [] relation arguments ≠ []

end Mettapedia.GSLT.LanguageDef.DecidableRelations
