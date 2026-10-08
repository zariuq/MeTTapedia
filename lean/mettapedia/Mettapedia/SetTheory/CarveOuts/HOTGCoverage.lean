import Mettapedia.Logic.HOL.Embedding.ZFSetUniverseInterpretation
import Mettapedia.SetTheory.Profiles.Ledger
import Mettapedia.SetTheory.CarveOuts.WellFoundedBubble

/-!
# HOTG as a child of the well-founded bubble: the coverage table

The Megalodon HOTG profile of the C draft seeds eleven laws: extensionality, the empty set,
union, power set, separation, replacement, membership induction, and four laws of the
least-universe operator `UnivOf`; it declares `Eps_set` with its type and no choice law.
This module records, for each law and for the two operators, the Lean theorem that
validates it in Mathlib's `ZFSet`, read as a full higher-order model, and what that theorem
depends on.

**The table** (`coverage`) is a list of rows whose citations are declaration names checked by
the compiler. A row is `proved` (a formula and its validity theorem) or `pending` with the
missing statement in words; no row is a placeholder. Each row also records the law's status
in the Megalodon foundation the profile copies (an axiom, a theorem derived from the choice
operator, or a constant), and keeps an empty place for evidence from an external checker.

**The statements themselves** are packed in `HOTGLawsInZFSet`, a structure whose fields are
the validity statements, filled by `hotgLawsInZFSet`.

**Three commitments** separate HOTG from the bubble (`HOTGCommitments`). They are declared,
never theorems of the top:
* **universes**: `CofinalInaccessibles`, a hypothesis of every universe law;
* **choice**: a global choice operator with its law; in the Lean model it is
  `Classical.choose` (`ZFSetHenkinInterpretation.epsilonSet`);
* **higher-order logic over a set-sized slice**: the higher-order quantifiers of
  separation, replacement and induction range over all predicates and functions of the
  carrier (`ZFSetHenkinInterpretation.fullDomains`), and on a universe a separated
  higher-order refinement stays in the universe (`ZFSetUniverseClosure.predicateSet_mem_univOf`).

Separation is a seeded law of the C profile, but in the Megalodon foundation it is a
derived theorem: `Sep` is defined from replacement and the choice operator, as is excluded
middle. The Lean model proves separation from Mathlib's `ZFSet.sep`, without the choice
operator `Eps_set`. Host choice is present in every row all the same: the model's
replacement operation is Mathlib's `ZFSet.image`, made available for every function by
`Classical.allZFSetDefinable`, so every validity statement about the model depends on
`Classical.choice`.

The logic of the Megalodon foundation also has function and propositional extensionality,
which the C profile does not seed. In the Lean model they hold because its equality is
extensional at every type (`funcExt_valid`, `propExt_valid`).

The statement correspondence between a C seed and the Lean formula of the same name is by
name and by the impredicative expansion of connectives
(`ZFSetUniverseInterpretation.expanded_universeTheory_valid`); it is not checked against
the C text by the kernel.
-/

set_option autoImplicit false

namespace Mettapedia.SetTheory.CarveOuts.HOTGCoverage

open Lean (Name)
open Mettapedia.Logic.HOL
open Mettapedia.Logic.HOL.Embedding
open Mettapedia.Logic.HOL.Embedding.ZFSetHenkinInterpretation
open Mettapedia.Logic.HOL.Embedding.ZFSetUniverseClosure
open Mettapedia.Logic.HOL.Embedding.ZFSetUniverseInterpretation

universe u

/-! ## The two logic laws the profile does not seed -/

/-- Function extensionality for set functions: `∀ f g, (∀ x, f x = g x) → f = g`. -/
def funcExt : ClosedFormula Symbol :=
  .all (σ := mapping) (.all (σ := mapping) (.imp
    (.all (σ := set) (.eq (.app (.var (.vs (.vs .vz))) (.var .vz))
      (.app (.var (.vs .vz)) (.var .vz))))
    (.eq (.var (.vs .vz)) (.var .vz))))

/-- Propositional extensionality: `∀ p q, (p ↔ q) → p = q`. -/
def propExt : ClosedFormula Symbol :=
  .all (σ := .prop) (.all (σ := .prop) (.imp
    (iffFormula (.var (.vs .vz)) (.var .vz))
    (.eq (.var (.vs .vz)) (.var .vz))))

theorem funcExt_valid : model.{u}.models funcExt := by
  intro f _ g _ h x hx
  exact h x hx

theorem propExt_valid : model.{u}.models propExt := by
  intro p _ q _ h
  exact ⟨h.1, h.2⟩

/-! ## The statements -/

/-- **The HOTG laws in `ZFSet`.** The seven set laws hold in the full higher-order model on
`ZFSet`; the four universe laws hold under `CofinalInaccessibles`; the universe operator is
the least closed universe; the choice law holds for `Classical.choose`. -/
structure HOTGLawsInZFSet : Prop where
  extensionality : model.{u}.models extensionality
  emptyLaw : model.{u}.models emptyLaw
  unionLaw : model.{u}.models unionLaw
  powerLaw : model.{u}.models powerLaw
  separationLaw : model.{u}.models separationLaw
  replacementLaw : model.{u}.models replacementLaw
  setInduction : model.{u}.models setInduction
  universeIn : ∀ h : CofinalInaccessibles.{u}, (universeModel h).models universeIn
  universeTransitive :
    ∀ h : CofinalInaccessibles.{u}, (universeModel h).models universeTransitive
  universeClosed : ∀ h : CofinalInaccessibles.{u}, (universeModel h).models universeClosed
  universeMinimal : ∀ h : CofinalInaccessibles.{u}, (universeModel h).models universeMinimal
  univOf : ∀ (h : CofinalInaccessibles.{u}) (N : ZFSet.{u}),
    N ∈ univOf h N ∧ Closed (univOf h N) ∧ ∀ U, N ∈ U → Closed U → univOf h N ⊆ U
  epsSet : choiceModel.{u}.models choiceLaw
  funcExt : model.{u}.models funcExt
  propExt : model.{u}.models propExt

theorem hotgLawsInZFSet : HOTGLawsInZFSet.{u} where
  extensionality := extensionality_valid
  emptyLaw := emptyLaw_valid
  unionLaw := unionLaw_valid
  powerLaw := powerLaw_valid
  separationLaw := separationLaw_valid
  replacementLaw := replacementLaw_valid
  setInduction := setInduction_valid
  universeIn := universeIn_valid
  universeTransitive := universeTransitive_valid
  universeClosed := universeClosed_valid
  universeMinimal := universeMinimal_valid
  univOf h N := ⟨mem_univOf h N, univOf_closed h N, fun _ hN hU => univOf_minimal h hN hU⟩
  epsSet := choiceLaw_valid
  funcExt := funcExt_valid
  propExt := propExt_valid

/-! ## The commitments, declared -/

/-- **The three commitments HOTG adds to the well-founded bubble**, as hypotheses: cofinally
many inaccessibles at the level of `ZFSet`, a global choice operator with its law, and
higher-order quantification over every predicate and function of the carrier. -/
structure HOTGCommitments : Type (u + 1) where
  universes : CofinalInaccessibles.{u}
  choice : (ZFSet.{u} → Prop) → ZFSet.{u}
  choiceLaw : ∀ (P : ZFSet.{u} → Prop) (x : ZFSet.{u}), P x → P (choice P)
  higherOrder : model.{u}.FullDomains

/-- With the commitments, every set lies in a closed universe, and the chosen set satisfies
any satisfiable predicate. Diaconescu's argument then gives excluded middle from the bubble's
set principles and the choice operator (`Profiles.lem_of_choice`). -/
theorem HOTGCommitments.consequences (c : HOTGCommitments.{u}) :
    (∀ N : ZFSet.{u}, ∃ U, N ∈ U ∧ Closed U) ∧
      ∀ (P : ZFSet.{u} → Prop), (∃ x, P x) → P (c.choice P) :=
  ⟨fun N => ⟨univOf c.universes N, mem_univOf _ N, univOf_closed _ N⟩,
    fun P ⟨x, hx⟩ => c.choiceLaw P x hx⟩

/-! ## The table -/

/-- The commitment a law depends on, beyond the bubble's first-order set principles. -/
inductive Commitment where
  | universes
  | choice
  | higherOrder
  deriving DecidableEq, Repr

/-- The status of a law in the Megalodon foundation the profile copies. -/
inductive MegalodonStatus where
  | axiom
  /-- A theorem of the foundation, derived using the choice operator. -/
  | derivedFromChoice
  | primitiveConstant
  /-- An axiom of the foundation's logic that the C profile does not seed. -/
  | logicAxiomNotSeeded
  deriving DecidableEq, Repr

/-- Evidence from an external proof checker. -/
structure ExternalCheck where
  checker : String
  file : String
  declaration : String
  command : String
  exitCode : Nat
  deriving Repr

/-- How a row is covered in Lean. -/
inductive Coverage where
  /-- The HOL formula and its validity theorem, or the operator and its defining theorems. -/
  | proved (statement : Name) (theorems : List Name)
  /-- The missing statement, in words. -/
  | pending (statement : String)
  deriving Repr

/-- One row of the table. -/
structure Row where
  /-- The seed name in the C profile, or `-` when the profile does not seed it. -/
  cName : String
  /-- The name in the Megalodon preamble. -/
  megalodonName : String
  megalodonStatus : MegalodonStatus
  coverage : Coverage
  /-- The commitments the Lean theorem depends on. -/
  commitments : List Commitment
  /-- Whether the axioms of the cited theorems include `Classical.choice`. For every row they
  do: the model's own operations use host choice (its replacement is Mathlib's `ZFSet.image`
  with definability supplied by `Classical.allZFSetDefinable`), whatever the law. -/
  hostChoice : Bool
  /-- Evidence from an external checker; empty until it is supplied. -/
  external : List ExternalCheck := []
  note : String := ""
  deriving Repr

/-- **The coverage table.** -/
def coverage : List Row := [
  { cName := "extensionality", megalodonName := "set_ext", megalodonStatus := .axiom
    coverage := .proved ``ZFSetHenkinInterpretation.extensionality
      [``ZFSetHenkinInterpretation.extensionality_valid]
    commitments := [], hostChoice := true
    note := "Two inclusions in the preamble; one equivalence in the C seed and in Lean." },
  { cName := "emptyLaw", megalodonName := "EmptyAx", megalodonStatus := .axiom
    coverage := .proved ``ZFSetHenkinInterpretation.emptyLaw
      [``ZFSetHenkinInterpretation.emptyLaw_valid]
    commitments := [], hostChoice := true
    note := "The C seed and Lean have the form of the library theorem EmptyE." },
  { cName := "unionLaw", megalodonName := "UnionEq", megalodonStatus := .axiom
    coverage := .proved ``ZFSetHenkinInterpretation.unionLaw
      [``ZFSetHenkinInterpretation.unionLaw_valid]
    commitments := [], hostChoice := true },
  { cName := "powerLaw", megalodonName := "PowerEq", megalodonStatus := .axiom
    coverage := .proved ``ZFSetHenkinInterpretation.powerLaw
      [``ZFSetHenkinInterpretation.powerLaw_valid]
    commitments := [], hostChoice := true },
  { cName := "separationLaw", megalodonName := "SepI; SepE"
    megalodonStatus := .derivedFromChoice
    coverage := .proved ``ZFSetHenkinInterpretation.separationLaw
      [``ZFSetHenkinInterpretation.separationLaw_valid]
    commitments := [.higherOrder], hostChoice := true
    note := "A seeded law of the C profile. In the Megalodon foundation Sep is defined from \
      Repl and the choice operator, so separation is a theorem that depends on choice. In \
      Lean it is Mathlib's ZFSet.sep, with no choice operator; the separating predicate \
      ranges over all predicates of the carrier." },
  { cName := "replacementLaw", megalodonName := "ReplEq", megalodonStatus := .axiom
    coverage := .proved ``ZFSetHenkinInterpretation.replacementLaw
      [``ZFSetHenkinInterpretation.replacementLaw_valid]
    commitments := [.higherOrder], hostChoice := true
    note := "The replacing function ranges over all functions of the carrier." },
  { cName := "setInduction", megalodonName := "In_ind", megalodonStatus := .axiom
    coverage := .proved ``ZFSetHenkinInterpretation.setInduction
      [``ZFSetHenkinInterpretation.setInduction_valid]
    commitments := [.higherOrder], hostChoice := true
    note := "The induction predicate ranges over all predicates of the carrier. On the \
      hypersets it fails, and the bubble is where it holds (CarveOuts.hsetBubble)." },
  { cName := "universeIn", megalodonName := "UnivOf_In", megalodonStatus := .axiom
    coverage := .proved ``ZFSetUniverseInterpretation.universeIn
      [``ZFSetUniverseInterpretation.universeIn_valid]
    commitments := [.universes], hostChoice := true },
  { cName := "universeTransitive", megalodonName := "UnivOf_TransSet"
    megalodonStatus := .axiom
    coverage := .proved ``ZFSetUniverseInterpretation.universeTransitive
      [``ZFSetUniverseInterpretation.universeTransitive_valid]
    commitments := [.universes], hostChoice := true },
  { cName := "universeClosed", megalodonName := "UnivOf_ZF_closed", megalodonStatus := .axiom
    coverage := .proved ``ZFSetUniverseInterpretation.universeClosed
      [``ZFSetUniverseInterpretation.universeClosed_valid]
    commitments := [.universes, .higherOrder], hostChoice := true },
  { cName := "universeMinimal", megalodonName := "UnivOf_Min", megalodonStatus := .axiom
    coverage := .proved ``ZFSetUniverseInterpretation.universeMinimal
      [``ZFSetUniverseInterpretation.universeMinimal_valid]
    commitments := [.universes, .higherOrder], hostChoice := true },
  { cName := "UnivOf", megalodonName := "UnivOf", megalodonStatus := .primitiveConstant
    coverage := .proved ``ZFSetUniverseClosure.univOf
      [``ZFSetUniverseClosure.mem_univOf, ``ZFSetUniverseClosure.univOf_closed,
        ``ZFSetUniverseClosure.univOf_minimal, ``ZFSetUniverseClosure.univOf_independent]
    commitments := [.universes], hostChoice := true
    note := "The least closed universe containing a set, by separation inside an \
      inaccessible rank; its value does not depend on the enclosure chosen." },
  { cName := "Eps_set", megalodonName := "Eps_i; Eps_i_ax", megalodonStatus := .axiom
    coverage := .proved ``ZFSetHenkinInterpretation.choiceLaw
      [``ZFSetHenkinInterpretation.choiceLaw_valid, ``ZFSetHenkinInterpretation.epsilonSet_spec]
    commitments := [.choice], hostChoice := true
    note := "The C profile declares Eps_set with its type and seeds no choice law. The Lean \
      operator is Classical.choose, with the empty set when nothing satisfies the \
      predicate." },
  { cName := "-", megalodonName := "func_ext", megalodonStatus := .logicAxiomNotSeeded
    coverage := .proved ``funcExt [``funcExt_valid]
    commitments := [.higherOrder], hostChoice := true
    note := "Stated at set functions. The model's equality is extensional at every type." },
  { cName := "-", megalodonName := "prop_ext", megalodonStatus := .logicAxiomNotSeeded
    coverage := .proved ``propExt [``propExt_valid]
    commitments := [], hostChoice := true }
]

/-- The eleven seeded laws, `UnivOf` and `Eps_set` are the first thirteen rows. -/
theorem coverage_profile_names :
    (coverage.take 13).map (·.cName) =
      ["extensionality", "emptyLaw", "unionLaw", "powerLaw", "separationLaw",
        "replacementLaw", "setInduction", "universeIn", "universeTransitive",
        "universeClosed", "universeMinimal", "UnivOf", "Eps_set"] := by
  decide

/-- No row of the table is pending. -/
def Row.isProved (row : Row) : Bool :=
  match row.coverage with
  | .proved .. => true
  | .pending _ => false

theorem coverage_all_proved : coverage.all Row.isProved = true := by
  decide

/-- Exactly the rows whose Lean theorem depends on the universe commitment are the four
universe laws and `UnivOf`. -/
theorem coverage_universe_rows :
    (coverage.filter fun row => row.commitments.contains .universes).map (·.cName) =
      ["universeIn", "universeTransitive", "universeClosed", "universeMinimal", "UnivOf"] := by
  decide

end Mettapedia.SetTheory.CarveOuts.HOTGCoverage
