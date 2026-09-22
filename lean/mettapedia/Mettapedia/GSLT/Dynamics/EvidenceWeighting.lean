import Mettapedia.GSLT.Dynamics.WeightCost
import Mettapedia.GSLT.Core.ProofRelevantGSLT
import Mettapedia.OSLF.MeTTaIL.Match

/-!
# Weights over derivations, not over steps

A weighting assigns a quantity to a reduction.  Which reduction — the *pair of
endpoints*, or the *derivation* that got from one to the other?  The existing
`WeightMap` answers the first, because it is indexed by `S.Step t u`, and that
is a `Prop`.

That is not a presentational detail.  Proof irrelevance makes every function out
of a proposition constant on it, so a `Prop`-indexed weight **cannot** give two
derivations of the same step different weights, whatever the author intends.
`weightMap_proof_irrelevant` below is that fact, and it is not a limitation of
any particular weight map but of the type it is a function out of.

The repair is already in the tree: `StepEvidence` equips a theory with a
`Type`-valued family whose inhabitants *are* the derivations, tied to the step
relation by `erases_iff` so that no event is invented and none is lost.  A
weighting indexed by that family can separate derivations, and the canary at the
foot of this file exhibits a theory where it does and where no `Prop`-indexed
weighting can.

What this file does **not** claim: nothing here makes a weighting adaptive, and
nothing here is a summability condition.  Both are part of the same programme
and neither is written.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.EvidenceWeighting

open Mettapedia.GSLT
open Mettapedia.GSLT.LooseRelationEquipment
open Mettapedia.GSLT.ProofRelevant

/-! ## Why a step-indexed weighting cannot see a derivation -/

/-- **A weight indexed by the step relation is constant on derivations.**  Two
proofs of the same step are equal, so the weight map cannot tell them apart.
This holds for every weight map and every weight type: it is a property of
indexing by a `Prop`. -/
theorem weightMap_proof_irrelevant {S : GSLT} {W : Type*}
    (weights : WeightMap S W) {source target : S.Term}
    (first second : S.Step source target) :
    weights.weight first = weights.weight second := by
  congr 1

/-- The same for cost maps. -/
theorem costMap_proof_irrelevant {S : GSLT} {A : Type*} {k : Nat}
    (costs : CostMap S A k) {source target : S.Term}
    (first second : S.Step source target) :
    costs.cost first = costs.cost second := by
  congr 1

/-! ## Weights over evidence -/

/-- A weighting of the derivations of a proof-relevant theory.  Its index is the
authored evidence family, whose inhabitants are the derivations themselves, so a
weighting may depend on *which* derivation was taken. -/
structure EvidenceWeightMap (system : ProofRelevantGSLT.{0}) (W : Type*) where
  /-- The weight of one authored derivation. -/
  weight : {source target : system.theory.Term} →
    system.steps.Evidence source target → W

/-- A weighting of derivations by resource cost. -/
structure EvidenceCostMap (system : ProofRelevantGSLT.{0}) (A : Type*) (k : Nat) where
  /-- The cost of one authored derivation. -/
  cost : {source target : system.theory.Term} →
    system.steps.Evidence source target → VectorialAccount A k

/-- A path of authored derivations. -/
inductive EvidencePath (system : ProofRelevantGSLT.{0}) :
    system.theory.Term → system.theory.Term → Type where
  | nil (term : system.theory.Term) : EvidencePath system term term
  | cons {source middle target : system.theory.Term} :
      system.steps.Evidence source middle →
      EvidencePath system middle target →
      EvidencePath system source target

/-- The amplitude of a path of derivations. -/
def evidenceAmplitude {system : ProofRelevantGSLT.{0}} {W : Type*} [Monoid W]
    (weights : EvidenceWeightMap system W) :
    {source target : system.theory.Term} → EvidencePath system source target → W
  | _, _, .nil _ => 1
  | _, _, .cons evidence rest => weights.weight evidence * evidenceAmplitude weights rest

/-- The total cost of a path of derivations. -/
def evidenceTotalCost {system : ProofRelevantGSLT.{0}} {A : Type*} {k : Nat}
    [Add A] [Zero A] (costs : EvidenceCostMap system A k) :
    {source target : system.theory.Term} →
      EvidencePath system source target → VectorialAccount A k
  | _, _, .nil _ => 0
  | _, _, .cons evidence rest => costs.cost evidence + evidenceTotalCost costs rest

/-- Every path of derivations erases to a path of steps: the evidence layer adds
information and loses none. -/
def EvidencePath.erase {system : ProofRelevantGSLT.{0}} :
    {source target : system.theory.Term} →
      EvidencePath system source target →
      system.theory.RewritePath source target
  | _, _, .nil term => .nil term
  | _, _, .cons evidence rest => .cons (system.steps.erase evidence) rest.erase

/-- The number of derivations in a path. -/
def EvidencePath.length {system : ProofRelevantGSLT.{0}} :
    {source target : system.theory.Term} →
      EvidencePath system source target → Nat
  | _, _, .nil _ => 0
  | _, _, .cons _ rest => 1 + rest.length

/-- Erasure keeps the length: the two layers count the same reductions. -/
theorem EvidencePath.erase_length {system : ProofRelevantGSLT.{0}} :
    ∀ {source target : system.theory.Term} (path : EvidencePath system source target),
      path.erase.length = path.length
  | _, _, .nil _ => rfl
  | _, _, .cons _ rest => by
      simp only [EvidencePath.erase, GSLT.RewritePath.length, EvidencePath.length,
        EvidencePath.erase_length rest]

/-! ## The step-indexed weighting is the first-order shadow

Every weighting of steps induces one of derivations, by forgetting which
derivation was taken.  That map is the sense in which the existing `WeightMap`
layer is the first-order shadow of this one: it lands exactly in the weightings
that are constant on derivations, and the canary below exhibits a weighting
outside its image. -/

/-- The evidence weighting a step weighting casts. -/
def EvidenceWeightMap.ofStepIndexed {system : ProofRelevantGSLT.{0}} {W : Type*}
    (weights : WeightMap system.theory W) : EvidenceWeightMap system W where
  weight := fun {_ _} evidence => weights.weight (system.steps.erase evidence)

/-- The evidence cost map a step cost map casts. -/
def EvidenceCostMap.ofStepIndexed {system : ProofRelevantGSLT.{0}} {A : Type*}
    {k : Nat} (costs : CostMap system.theory A k) : EvidenceCostMap system A k where
  cost := fun {_ _} evidence => costs.cost (system.steps.erase evidence)

/-- **A shadow is blind to derivations.**  Whatever the step weighting, the
weighting it casts gives any two derivations of one reduction one value. -/
theorem ofStepIndexed_constant {system : ProofRelevantGSLT.{0}} {W : Type*}
    (weights : WeightMap system.theory W) {source target : system.theory.Term}
    (first second : system.steps.Evidence source target) :
    (EvidenceWeightMap.ofStepIndexed weights).weight first =
      (EvidenceWeightMap.ofStepIndexed weights).weight second :=
  weightMap_proof_irrelevant weights _ _

/-! ## Alternatives, and what adaptation costs

A rule offers a term several matches, and a weighting of the alternatives may
read only the alternative or also the alternatives already taken.  The two
readings are the external and internal forms, and they differ in a way that is
not a matter of taste: the external one totals to something independent of the
order the alternatives were enumerated in, and the internal one does not. -/

/-- The external total: each alternative weighed on its own. -/
def externalTotal {A W : Type*} [AddCommMonoid W] (weigh : A → W)
    (alternatives : List A) : W :=
  (alternatives.map weigh).sum

/-- **The external form is invariant under permuting the alternatives.**  The
total does not depend on the order they were enumerated in, which is what makes
enumeration an implementation detail. -/
theorem externalTotal_perm_invariant {A W : Type*} [AddCommMonoid W]
    (weigh : A → W) {first second : List A} (permutation : first.Perm second) :
    externalTotal weigh first = externalTotal weigh second :=
  (permutation.map weigh).sum_eq

/-- The internal, adaptive total: each alternative is weighed against the ones
already taken.  The first argument is the prefix already seen. -/
def adaptiveTotal {A W : Type*} [AddMonoid W] (weigh : List A → A → W) :
    List A → List A → W
  | _, [] => 0
  | seen, alternative :: rest =>
      weigh seen alternative + adaptiveTotal weigh (seen ++ [alternative]) rest

/-- Summability is not a side condition here and the reason is structural: the
alternatives a rule offers are a *list*, so the total is a finite sum and exists
outright.  A presentation whose alternatives are not finitely enumerated needs
the side condition; this one does not, and saying so is not the same as
discharging it in general. -/
theorem adaptiveTotal_nil {A W : Type*} [AddMonoid W] (weigh : List A → A → W)
    (seen : List A) : adaptiveTotal weigh seen [] = 0 := rfl

/-! ### Adaptation as a transformation

The two forms above are compared by their totals, which leaves the difference
between them implicit.  It is better to name it: an internal weighting is an
external one plus a correction that may read the prefix, the correction is a
thing in its own right, and the failure of invariance is located in it exactly.
-/

/-- **An adaptation.**  The internal weighting an external one becomes when a
correction is added — a correction that may read the alternatives already taken. -/
def adapt {A W : Type*} [AddCommMonoid W] (weigh : A → W)
    (delta : List A → A → W) : List A → A → W :=
  fun seen alternative => weigh alternative + delta seen alternative

/-- The zero adaptation changes nothing. -/
theorem adapt_zero {A W : Type*} [AddCommMonoid W] (weigh : A → W)
    (seen : List A) (alternative : A) :
    adapt weigh (fun _ _ => 0) seen alternative = weigh alternative := by
  simp [adapt]

/-- **The total splits.**  An adapted weighting totals to the external total
plus the correction's own adaptive total, and nothing else is added — so the
delta *is* the difference between the two forms rather than a comparison of
them. -/
theorem adaptiveTotal_adapt {A W : Type*} [AddCommMonoid W] (weigh : A → W)
    (delta : List A → A → W) (seen alternatives : List A) :
    adaptiveTotal (adapt weigh delta) seen alternatives =
      externalTotal weigh alternatives + adaptiveTotal delta seen alternatives := by
  induction alternatives generalizing seen with
  | nil => simp [adaptiveTotal, externalTotal]
  | cons alternative rest inductionHypothesis =>
      simp only [adaptiveTotal, externalTotal, adapt, List.map_cons, List.sum_cons,
        inductionHypothesis]
      ac_rfl

/-- A correction that does not read the prefix is an external weighting in
disguise, and totals like one. -/
theorem adaptiveTotal_of_prefixBlind {A W : Type*} [AddCommMonoid W]
    (delta : List A → A → W)
    (blind : ∀ seen alternative, delta seen alternative = delta [] alternative)
    (seen alternatives : List A) :
    adaptiveTotal delta seen alternatives = externalTotal (delta []) alternatives := by
  induction alternatives generalizing seen with
  | nil => simp [adaptiveTotal, externalTotal]
  | cons alternative rest inductionHypothesis =>
      simp only [adaptiveTotal, externalTotal, List.map_cons, List.sum_cons,
        blind seen alternative, inductionHypothesis]

/-- **So what breaks invariance is the reading of the prefix, and only that.**
An adaptation blind to the prefix leaves the total invariant under permuting the
alternatives, however large the correction is. -/
theorem adaptiveTotal_adapt_perm_invariant_of_prefixBlind {A W : Type*}
    [AddCommMonoid W] (weigh : A → W) (delta : List A → A → W)
    (blind : ∀ seen alternative, delta seen alternative = delta [] alternative)
    {first second : List A} (permutation : first.Perm second) (seen : List A) :
    adaptiveTotal (adapt weigh delta) seen first =
      adaptiveTotal (adapt weigh delta) seen second := by
  rw [adaptiveTotal_adapt, adaptiveTotal_adapt,
    adaptiveTotal_of_prefixBlind delta blind,
    adaptiveTotal_of_prefixBlind delta blind,
    externalTotal_perm_invariant weigh permutation,
    externalTotal_perm_invariant (delta []) permutation]

namespace Adaptation

/-- An adaptive weighting: an alternative is charged by how many were taken
before it. -/
def byPosition : List Nat → Nat → Nat :=
  fun seen alternative => seen.length * alternative

/-- Two alternatives, in the two orders. -/
theorem alternatives_perm : [1, 2].Perm [2, 1] :=
  List.Perm.swap 2 1 []

/-- **Internal adaptation breaks permutation invariance of the alternatives.**
The same two alternatives, enumerated the other way round, total differently —
so an adaptive weighting makes the enumeration order observable. -/
theorem adaptive_not_perm_invariant :
    adaptiveTotal byPosition [] [1, 2] ≠ adaptiveTotal byPosition [] [2, 1] := by
  decide

/-- And the external form of the same charge is invariant, so the failure is
adaptation's and not the alternatives'. -/
theorem external_is_perm_invariant :
    externalTotal (fun alternative => alternative) [1, 2] =
      externalTotal (fun alternative => alternative) [2, 1] :=
  externalTotal_perm_invariant _ alternatives_perm

/-- The adaptive charge of `byPosition`, read as a correction to the zero
external weighting: it reads the prefix, which is why the total moves. -/
theorem byPosition_not_prefixBlind :
    ¬ ∀ seen alternative, byPosition seen alternative = byPosition [] alternative := by
  intro blind
  have applied := blind [0] 1
  simp [byPosition] at applied

/-- **And the characterisation is sharp at this witness.**  The same charge made
blind to the prefix — each alternative weighed on its own — is invariant. -/
theorem blinded_is_perm_invariant :
    adaptiveTotal (adapt (fun alternative : Nat => alternative) (fun _ _ => 0)) []
        [1, 2] =
      adaptiveTotal (adapt (fun alternative : Nat => alternative) (fun _ _ => 0)) []
        [2, 1] :=
  adaptiveTotal_adapt_perm_invariant_of_prefixBlind _ _ (fun _ _ => rfl)
    alternatives_perm []

end Adaptation

/-! ## Where-weights, and the binder arities they read

A weight attached to one *match* of one rule is a where-weight.  What it is
allowed to read decides what it can charge for, and the arity of the binders the
rule's parameters introduce is the part that is easy to leave out: a weighting
that reads only the bindings a match produced cannot see it, because two rules
can produce the same bindings while binding different numbers of names. -/

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match

/-- How many names one declared parameter binds. -/
def binderCount : TermParam → Nat
  | .simple _ _ => 0
  | .abstractionNamed _ _ _ => 1
  | .multiAbstractionNamed names _ _ => names.length

/-- **The binder arity of a declared former**: how many names its parameters
bind between them. -/
def binderArity (rule : GrammarRule) : Nat :=
  (rule.params.map binderCount).sum

/-- A where-weight reads only the match when it is some function of the bindings
alone, with the rule forgotten. -/
def ReadsOnlyMatch {W : Type*} (weigh : GrammarRule → Bindings → W) : Prop :=
  ∃ underlying : Bindings → W, ∀ rule bindings, weigh rule bindings = underlying bindings

/-- The where-weight that charges a match by the binder arity of the rule it
matched. -/
def byBinderArity : GrammarRule → Bindings → Nat := fun rule _ => binderArity rule

namespace BinderArity

/-- A former that binds nothing. -/
def output : GrammarRule where
  label := "Out"
  category := "Proc"
  params := [.simple "chan" TypeExpr.name, .simple "val" TypeExpr.proc]
  syntaxPattern := [.terminal "Out"]

/-- A former that binds one name. -/
def input : GrammarRule where
  label := "In"
  category := "Proc"
  params := [.simple "chan" TypeExpr.name,
    .abstraction "body" (TypeExpr.funType TypeExpr.name TypeExpr.proc)]
  syntaxPattern := [.terminal "In"]

theorem output_arity : binderArity output = 0 := by decide

theorem input_arity : binderArity input = 1 := by decide

/-- **So a where-weight that reads the binder arity is not one that reads only
the match.**  The two formers above are charged differently at the same
bindings, which a weighting of the bindings alone cannot do. -/
theorem byBinderArity_not_readsOnlyMatch : ¬ ReadsOnlyMatch byBinderArity := by
  rintro ⟨underlying, factorisation⟩
  have outputCharge := factorisation output []
  have inputCharge := factorisation input []
  rw [byBinderArity, output_arity] at outputCharge
  rw [byBinderArity, input_arity] at inputCharge
  omega

/-- And it does separate them, at the empty match. -/
theorem byBinderArity_separates :
    byBinderArity output [] ≠ byBinderArity input [] := by decide

/-- A weighting that reads only the match charges them alike, whatever it is —
so the separation above is the arity's and not the witness's. -/
theorem readsOnlyMatch_cannot_separate {W : Type*}
    {weigh : GrammarRule → Bindings → W} (blind : ReadsOnlyMatch weigh)
    (bindings : Bindings) : weigh output bindings = weigh input bindings := by
  obtain ⟨underlying, factorisation⟩ := blind
  rw [factorisation, factorisation]

end BinderArity

/-! ## The difference is real

A theory with one step and two derivations of it.  An evidence-indexed weighting
separates them; `weightMap_proof_irrelevant` says no step-indexed weighting can.
-/

namespace Canary

/-- Two terms, the second reachable from the first. -/
inductive Point where
  | start
  | finish
  deriving DecidableEq, Repr

/-- The theory: exactly one reduction. -/
def oneStep : GSLT where
  Term := Point
  equations :=
    { r := Eq
      iseqv := { refl := Eq.refl, symm := Eq.symm, trans := Eq.trans } }
  rewrites := fun source target => source = .start ∧ target = .finish
  rewrites_resp_left := by
    rintro t t' u equal ⟨hs, ht⟩
    subst equal
    exact ⟨u, ⟨hs, ht⟩, rfl⟩
  rewrites_resp_right := by
    rintro t u u' ⟨hs, ht⟩ equal
    subst equal
    exact ⟨hs, ht⟩

/-- Two derivations of that one reduction, told apart by a tag. -/
inductive Route : Point → Point → Type where
  | left : Route .start .finish
  | right : Route .start .finish

/-- The authored evidence family: exactly the two routes, and nothing where
there is no step. -/
def routes : StepEvidence oneStep where
  Evidence := Route
  erases_iff := by
    intro source target
    constructor
    · rintro ⟨route⟩
      cases route
      · exact ⟨rfl, rfl⟩
      · exact ⟨rfl, rfl⟩
    · rintro ⟨hs, ht⟩
      subst hs; subst ht
      exact ⟨.left⟩

/-- The proof-relevant theory. -/
def system : ProofRelevantGSLT where
  theory := oneStep
  steps := routes

/-- A weighting that charges the two routes differently. -/
def tollByRoute : EvidenceWeightMap system Nat where
  weight := fun {_ _} route =>
    match route with
    | .left => 1
    | .right => 2

/-- **The evidence-indexed weighting separates the two derivations.** -/
theorem tollByRoute_separates :
    tollByRoute.weight (.left : Route .start .finish) ≠
      tollByRoute.weight (.right : Route .start .finish) := by
  decide

/-- **And the two derivations really are of the same step**, so there is nothing
for a step-indexed weighting to index on: by `weightMap_proof_irrelevant` every
such weighting gives them one value. -/
theorem routes_erase_to_one_step :
    system.steps.erase (.left : Route .start .finish) =
      system.steps.erase (.right : Route .start .finish) :=
  Subsingleton.elim _ _

/-- The impossibility, stated at the canary: no step-indexed weighting
reproduces `tollByRoute`, because it would have to give one step two values. -/
theorem no_stepIndexed_weighting_separates (weights : WeightMap oneStep Nat)
    (first second : oneStep.Step .start .finish) :
    weights.weight first = weights.weight second :=
  weightMap_proof_irrelevant weights first second


/-- **And therefore `tollByRoute` is not a shadow.**  No step weighting casts it,
so the evidence layer is strictly larger than the step layer rather than a
relabelling of it. -/
theorem tollByRoute_not_a_shadow :
    ¬ ∃ weights : WeightMap oneStep Nat,
        ∀ {source target : Point} (route : system.steps.Evidence source target),
          (EvidenceWeightMap.ofStepIndexed (system := system) weights).weight route =
            tollByRoute.weight route := by
  rintro ⟨weights, agrees⟩
  refine tollByRoute_separates ?_
  calc tollByRoute.weight (.left : Route .start .finish)
      = (EvidenceWeightMap.ofStepIndexed (system := system) weights).weight
          (.left : Route .start .finish) := (agrees .left).symm
    _ = (EvidenceWeightMap.ofStepIndexed (system := system) weights).weight
          (.right : Route .start .finish) :=
        ofStepIndexed_constant (system := system) weights
          (.left : Route .start .finish) (.right : Route .start .finish)
    _ = tollByRoute.weight (.right : Route .start .finish) := agrees .right

end Canary

end Mettapedia.GSLT.EvidenceWeighting
