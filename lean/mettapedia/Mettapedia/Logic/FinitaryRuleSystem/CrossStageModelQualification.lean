import Mettapedia.Logic.FinitaryRuleSystem.DirectedUnion

/-!
# Cross-stage semantic qualification of finitary rule systems

A bottom-rejecting model of one rule system proves its no-bottom property.
An alternating qualification tower records the more specific architecture in
which the model at the next stage and opposite polarity qualifies the current
stage's rules.

The indexing is not itself a consistency proof: each stage still owes an
actual rule-sound, bottom-rejecting model.  Nor is this same-level
self-soundness.  The positive canary shows the indexing laws on a growing
family of bounded axioms; the negative canary shows that a direct-bottom rule
cannot be hidden inside a qualification record.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.FinitaryRuleSystem

open Mettapedia.Logic

universe u v w

variable {J : Type u}

/-- A semantic structure for judgments.  Satisfaction may depend on a world;
the rule-soundness condition below quantifies over every world. -/
structure RuleModel (J : Type u) where
  World : Type v
  Holds : World → J → Prop

/-- Every instance of a finitary rule preserves truth at each model world. -/
def RulesSoundIn (model : RuleModel.{u, v} J)
    (rules : List J → J → Prop) : Prop :=
  ∀ world premises conclusion, rules premises conclusion →
    (∀ premise ∈ premises, model.Holds world premise) →
    model.Holds world conclusion

/-- Independent semantic qualification of a rule system: a model validates
all rules, and a selected world refutes bottom. -/
structure ModelQualification (rules : List J → J → Prop) (bottom : J) where
  model : RuleModel.{u, v} J
  witness : model.World
  rulesSound : RulesSoundIn model rules
  rejectsBottom : ¬ model.Holds witness bottom

namespace ModelQualification

variable {rules : List J → J → Prop} {bottom : J}

/-- Every derivable judgment holds at every world of a qualified model. -/
theorem derives_holds (qualification : ModelQualification.{u, v} rules bottom)
    (world : qualification.model.World) {judgment : J}
    (derivation : Derives rules judgment) :
    qualification.model.Holds world judgment :=
  Derives.least (qualification.model.Holds world)
    (qualification.rulesSound world) derivation

/-- A rule-sound model with one bottom-refuting world proves no-bottom. -/
theorem noBottom (qualification : ModelQualification.{u, v} rules bottom) :
    NoBottom rules bottom := by
  intro derivation
  exact qualification.rejectsBottom
    (qualification.derives_holds qualification.witness derivation)

end ModelQualification

/-- A two-sided alternation law.  Fixed-point-free involution makes the
opposite polarity genuinely distinct, rather than a renamed same-level
model. -/
structure AlternatingPolarity (P : Type v) where
  opposite : P → P
  opposite_opposite : ∀ p, opposite (opposite p) = p
  opposite_ne : ∀ p, opposite p ≠ p

/-- Later-opposite semantic qualification for a family of rule systems.
`model (opposite p) (n+1)` validates `rules p n`; no claim is made that a
stage validates its own soundness or consistency statement. -/
structure AlternatingModelQualification
    {P : Type v} (polarity : AlternatingPolarity P)
    (rules : P → Nat → List J → J → Prop) (bottom : J) where
  model : P → Nat → RuleModel.{u, w} J
  witness : ∀ p n, (model p n).World
  nextOppositeRulesSound : ∀ p n,
    RulesSoundIn (model (polarity.opposite p) (n + 1)) (rules p n)
  nextOppositeRejectsBottom : ∀ p n,
    ¬ (model (polarity.opposite p) (n + 1)).Holds
      (witness (polarity.opposite p) (n + 1)) bottom

namespace AlternatingModelQualification

variable {P : Type v} {polarity : AlternatingPolarity P}
variable {rules : P → Nat → List J → J → Prop} {bottom : J}

/-- Extract the ordinary model qualification owed by one source stage. -/
def atSource
    (tower : AlternatingModelQualification.{u, v, w} polarity rules bottom)
    (p : P) (n : Nat) : ModelQualification.{u, w} (rules p n) bottom where
  model := tower.model (polarity.opposite p) (n + 1)
  witness := tower.witness (polarity.opposite p) (n + 1)
  rulesSound := tower.nextOppositeRulesSound p n
  rejectsBottom := tower.nextOppositeRejectsBottom p n

/-- Each source stage is bottom-free because its strictly later, opposite
model supplies a genuine semantic qualification. -/
theorem stage_noBottom
    (tower : AlternatingModelQualification.{u, v, w} polarity rules bottom)
    (p : P) (n : Nat) : NoBottom (rules p n) bottom :=
  (tower.atSource p n).noBottom

/-- If one polarity's rule family also grows monotonically, finite support
lifts its stagewise semantic qualifications to the directed union. -/
theorem directedUnion_noBottom
    (tower : AlternatingModelQualification.{u, v, w} polarity rules bottom)
    (p : P) (monotone : MonotoneRules (rules p)) :
    NoBottom (UnionRules (rules p)) bottom :=
  Mettapedia.Logic.FinitaryRuleSystem.directedUnion_noBottom
    monotone bottom (tower.stage_noBottom p)

end AlternatingModelQualification

namespace Canary

/-! ### Positive control: a growing two-polarity index -/

/-- Boolean opposition is a genuine fixed-point-free involution. -/
def boolPolarity : AlternatingPolarity Bool where
  opposite := not
  opposite_opposite p := Bool.not_not p
  opposite_ne p := by cases p <;> decide

/-- A one-world model in which exactly the inhabited optional naturals hold.
It genuinely rejects `none`. -/
def inhabitedOptionModel : RuleModel (Option Nat) where
  World := Unit
  Holds _ judgment := ∃ n, judgment = some n

theorem inhabitedOptionModel_rulesSound (bound : Nat) :
    RulesSoundIn inhabitedOptionModel (BoundedAxioms bound) := by
  intro world premises conclusion rule _subderivations
  rcases rule with ⟨_rfl, n, _hn, rfl⟩
  exact ⟨n, rfl⟩

/-- Minimal indexing canary for the alternating interface.  The rules grow
with the stage, while the same independently described model validates every
stage.  This demonstrates the qualification law, not increasing
proof-theoretic strength. -/
def boundedAxiomAlternatingCanary : AlternatingModelQualification
    boolPolarity (fun _p n => BoundedAxioms n) none where
  model _p _n := inhabitedOptionModel
  witness _p _n := ()
  nextOppositeRulesSound _p n := inhabitedOptionModel_rulesSound n
  nextOppositeRejectsBottom _p _n := by simp [inhabitedOptionModel]

theorem boundedAxiomAlternatingCanary_stage_noBottom (p : Bool) (n : Nat) :
    NoBottom (BoundedAxioms n) none :=
  boundedAxiomAlternatingCanary.stage_noBottom p n

theorem boundedAxiomAlternatingCanary_union_noBottom (p : Bool) :
    NoBottom (UnionRules BoundedAxioms) none :=
  boundedAxiomAlternatingCanary.directedUnion_noBottom p
    boundedAxioms_monotone

/-! ### Negative control: bottom cannot be semantically laundered -/

inductive DirectBottom : List Bool → Bool → Prop where
  | bottom : DirectBottom [] false

/-- No rule-sound model can both validate a direct-bottom rule and refute
bottom. -/
theorem directBottom_has_no_qualification :
    ¬ Nonempty (ModelQualification DirectBottom false) := by
  rintro ⟨qualification⟩
  have holdsBottom := qualification.rulesSound qualification.witness
    [] false DirectBottom.bottom (by simp)
  exact qualification.rejectsBottom holdsBottom

/-- Consequently a purported alternating tower containing a direct-bottom
source stage cannot be constructed. -/
theorem directBottom_has_no_alternating_qualification :
    ¬ Nonempty (AlternatingModelQualification boolPolarity
      (fun _p _n => DirectBottom) false) := by
  rintro ⟨tower⟩
  exact directBottom_has_no_qualification ⟨tower.atSource false 0⟩

end Canary

/-! ## Axiom audit -/

#print axioms ModelQualification.derives_holds
#print axioms ModelQualification.noBottom
#print axioms AlternatingModelQualification.stage_noBottom
#print axioms AlternatingModelQualification.directedUnion_noBottom
#print axioms Canary.boundedAxiomAlternatingCanary_union_noBottom
#print axioms Canary.directBottom_has_no_qualification
#print axioms Canary.directBottom_has_no_alternating_qualification

end Mettapedia.Logic.FinitaryRuleSystem
