import Mettapedia.Languages.MeTTa.HE.LeaTTaLoopPersistence
import Mettapedia.Languages.MeTTa.HE.SigmaCanonicalTransfer

/-!
# Direct repaired-LeaTTa soundness assembly

This module sits downstream of both direct human/LeaTTa conformance and
semantic completeness of the executable-independent human matcher.  It keeps
the remaining repaired-LeaTTa output-satisfiability obligation separate from
the representation-independent soundness assembly.
-/

namespace Mettapedia.Languages.MeTTa.HE.LeaTTaHumanConformance

open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.HE.LeaTTaBridge
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)

/-! ## Direct LeaTTa output satisfiability -/

/-! ### Semantic specialization -/

/-- A principal model is a satisfying valuation through which every other
model factors by one further homomorphic substitution. -/
private def PrincipalModel
    (theory : (String → Metta.Atom) → Prop)
    (general : String → Metta.Atom) : Prop :=
  theory general ∧
    ∀ specific, theory specific →
      HumanMatchModelTheory.ValuationRefines specific general

/-- Inhabited principal solution theory.  This is the sole semantic payload
threaded through the direct Lea matcher induction. -/
private def HasPrincipalModel
    (theory : (String → Metta.Atom) → Prop) : Prop :=
  ∃ general, PrincipalModel theory general

/-- Canonical accumulator alignment strengthens principality by fixing the
general valuation to LeaTTa's own equality-class resolver.  This rules out a
merely satisfiable but unreconciled presentation whose apparently valueless
class is already constrained indirectly. -/
def LeaCanonicalSolutionInvariant (bindings : Metta.Bindings) : Prop :=
  LeaBindingSatisfied (leaClassSolution bindings) bindings ∧
    ∀ specific, LeaBindingSatisfied specific bindings →
      HumanMatchModelTheory.ValuationRefines specific
        (leaClassSolution bindings)

private abbrev CanonicallyPrincipal := LeaCanonicalSolutionInvariant

/-- Principal-model existence depends only on the extensional solution
theory, never on a particular binding presentation. -/
private theorem hasPrincipalModel_congr
    {left right : (String → Metta.Atom) → Prop}
    (htheory : ∀ valuation, left valuation ↔ right valuation)
    (hleft : HasPrincipalModel left) :
    HasPrincipalModel right := by
  obtain ⟨general, hgeneral, hprincipal⟩ := hleft
  refine ⟨general, (htheory general).mp hgeneral, ?_⟩
  intro specific hspecific
  exact hprincipal specific ((htheory specific).mpr hspecific)

/-- Homomorphic specialization preserves every repaired-LeaTTa binding
equation.  This is the Lea-side companion of the corresponding human-binding
lemma and is independent of any matcher representation. -/
private theorem valuationRefines_leaBindingSatisfied
    {specific general : String → Metta.Atom}
    {bindings : Metta.Bindings}
    (hrefines : HumanMatchModelTheory.ValuationRefines specific general)
    (hsatisfied : LeaBindingSatisfied general bindings) :
    LeaBindingSatisfied specific bindings := by
  obtain ⟨post, happly⟩ :=
    HumanMatchModelTheory.ValuationRefines.apply_eq_applyClassSolution
      hrefines
  constructor
  · intro key value hvalue
    have hgeneral := hsatisfied.1 key value hvalue
    have hkey : specific key = applyClassSolution post (general key) := by
      simpa [applyClassSolution] using happly (.var key)
    calc
      specific key = applyClassSolution post (general key) := hkey
      _ = applyClassSolution post
          (applyClassSolution general value) :=
        congrArg (applyClassSolution post) hgeneral
      _ = applyClassSolution specific value := (happly value).symm
  · intro left right hequality
    have hgeneral := hsatisfied.2 left right hequality
    have hleft : specific left = applyClassSolution post (general left) := by
      simpa [applyClassSolution] using happly (.var left)
    have hright : specific right = applyClassSolution post (general right) := by
      simpa [applyClassSolution] using happly (.var right)
    exact hleft.trans
      ((congrArg (applyClassSolution post) hgeneral).trans hright.symm)

/-- Homomorphic specialization likewise preserves one atom equation. -/
private theorem valuationRefines_mettaEquationSatisfied
    {specific general : String → Metta.Atom}
    {equation : Metta.Atom × Metta.Atom}
    (hrefines : HumanMatchModelTheory.ValuationRefines specific general)
    (hsatisfied : MettaEquationSatisfied general equation) :
    MettaEquationSatisfied specific equation := by
  obtain ⟨post, happly⟩ :=
    HumanMatchModelTheory.ValuationRefines.apply_eq_applyClassSolution
      hrefines
  unfold MettaEquationSatisfied at hsatisfied ⊢
  rw [happly equation.1, happly equation.2, hsatisfied]

/-- Specialization is closed under finite conjunctions of atom equations. -/
private theorem valuationRefines_mettaEquationsSatisfied
    {specific general : String → Metta.Atom}
    {equations : List (Metta.Atom × Metta.Atom)}
    (hrefines : HumanMatchModelTheory.ValuationRefines specific general)
    (hsatisfied : MettaEquationsSatisfied general equations) :
    MettaEquationsSatisfied specific equations := by
  intro equation hequation
  exact valuationRefines_mettaEquationSatisfied hrefines
    (hsatisfied equation hequation)

/-- Variable constraints are also stable under homomorphic specialization. -/
private theorem valuationRefines_mettaConstraintsSatisfied
    {specific general : String → Metta.Atom}
    {constraints : List (String × Metta.Atom)}
    (hrefines : HumanMatchModelTheory.ValuationRefines specific general)
    (hsatisfied : MettaConstraintsSatisfied general constraints) :
    MettaConstraintsSatisfied specific constraints := by
  intro constraint hconstraint
  obtain ⟨post, happly⟩ :=
    HumanMatchModelTheory.ValuationRefines.apply_eq_applyClassSolution
      hrefines
  have hgeneral := hsatisfied constraint hconstraint
  have hkey : specific constraint.1 =
      applyClassSolution post (general constraint.1) := by
    simpa [applyClassSolution] using happly (.var constraint.1)
  calc
    specific constraint.1 =
        applyClassSolution post (general constraint.1) := hkey
    _ = applyClassSolution post
        (applyClassSolution general constraint.2) :=
      congrArg (applyClassSolution post) hgeneral
    _ = applyClassSolution specific constraint.2 :=
      (happly constraint.2).symm

/-- Pulling one equation back along a principal model and solving that pulled
equation produces a principal model of the conjoined theory.  This is the
semantic composition law used by fresh accumulator extensions: the second
solve acts only on the free parameters of the first one. -/
private theorem principalModel_and_equation_of_pullback
    {theory : (String → Metta.Atom) → Prop}
    {general postGeneral : String → Metta.Atom}
    {equation : Metta.Atom × Metta.Atom}
    (htheorySpecializes : ∀ {specific general},
      HumanMatchModelTheory.ValuationRefines specific general →
        theory general → theory specific)
    (hgeneral : PrincipalModel theory general)
    (hpost : PrincipalModel
      (fun post => MettaEquationSatisfied post
        (applyClassSolution general equation.1,
          applyClassSolution general equation.2))
      postGeneral) :
    PrincipalModel
      (fun valuation => theory valuation ∧
        MettaEquationSatisfied valuation equation)
      (fun name => applyClassSolution postGeneral (general name)) := by
  let composed : String → Metta.Atom := fun name =>
    applyClassSolution postGeneral (general name)
  have hrefinesGeneral :
      HumanMatchModelTheory.ValuationRefines composed general := by
    exact ⟨postGeneral, fun name => rfl⟩
  refine ⟨⟨htheorySpecializes hrefinesGeneral hgeneral.1, ?_⟩, ?_⟩
  · unfold MettaEquationSatisfied at hpost ⊢
    simpa only [composed, HumanMatchModelTheory.applyClassSolution_comp]
      using hpost.1
  · intro specific hspecific
    have hrefines := hgeneral.2 specific hspecific.1
    obtain ⟨post, happly⟩ :=
      HumanMatchModelTheory.ValuationRefines.apply_eq_applyClassSolution
        hrefines
    have hpulled : MettaEquationSatisfied post
        (applyClassSolution general equation.1,
          applyClassSolution general equation.2) := by
      unfold MettaEquationSatisfied at hspecific ⊢
      simpa only [happly equation.1, happly equation.2] using hspecific.2
    obtain ⟨after, hafter⟩ :=
      HumanMatchModelTheory.ValuationRefines.apply_eq_applyClassSolution
        (hpost.2 post hpulled)
    refine ⟨after, fun name => ?_⟩
    have hname : specific name =
        applyClassSolution post (general name) := by
      simpa [applyClassSolution] using happly (.var name)
    exact hname.trans (hafter (general name))

/-! ### Canonical resolver absorption -/

/-- LeaTTa's selected stable representative belongs to the equality class it
represents. -/
private theorem leaEqRepresentative_mem_eqClassOrdered
    (bindings : Metta.Bindings) (key : String) :
    Metta.Bindings.eqRepresentative bindings key ∈
      Metta.Bindings.eqClassOrdered bindings key := by
  have hself : key ∈ Metta.Bindings.eqClassOrdered bindings key := by
    apply mem_leaEqClassOrdered_iff.mpr
    rw [mem_leaEqClass_iff_reachable]
  unfold Metta.Bindings.eqRepresentative
  cases hclass : Metta.Bindings.eqClassOrdered bindings key with
  | nil => simp [hclass] at hself
  | cons representative rest => simp

/-- One stable-order update for the equality endpoints contributed by a Lea
binding relation. -/
private def leaEqOrderUpdate
    (names : List String) (relation : Metta.BindingRel) : List String :=
  match relation with
  | .val _ _ => names
  | .eq left right =>
      let names := if names.contains right then names else names ++ [right]
      if names.contains left then names else names ++ [left]

/-- Equality endpoints contributed by one Lea binding relation. -/
private def leaEqRelationNodes : Metta.BindingRel → List String
  | .val _ _ => []
  | .eq left right => [left, right]

private theorem mem_leaEqOrderUpdate_iff
    {names : List String} {relation : Metta.BindingRel} {name : String} :
    name ∈ leaEqOrderUpdate names relation ↔
      name ∈ names ∨ name ∈ leaEqRelationNodes relation := by
  cases relation with
  | val key value => simp [leaEqOrderUpdate, leaEqRelationNodes]
  | eq left right =>
      simp only [leaEqOrderUpdate, leaEqRelationNodes, List.mem_cons]
      split <;> split <;> simp_all <;> aesop

private theorem mem_foldl_leaEqOrderUpdate_iff
    (relations : List Metta.BindingRel) (names : List String)
    (name : String) :
    name ∈ relations.foldl leaEqOrderUpdate names ↔
      name ∈ names ∨ name ∈ relations.flatMap leaEqRelationNodes := by
  induction relations generalizing names with
  | nil => simp
  | cons relation relations ih =>
      rw [List.foldl_cons, ih, mem_leaEqOrderUpdate_iff]
      simp [or_assoc]

/-- LeaTTa's stable equality ordering contains exactly the endpoints of its
explicit equality graph. -/
private theorem mem_leaEqVarsInOrder_iff
    {bindings : Metta.Bindings} {name : String} :
    name ∈ Metta.Bindings.eqVarsInOrder bindings ↔
      name ∈ bindings.flatMap leaEqRelationNodes := by
  unfold Metta.Bindings.eqVarsInOrder
  let actualUpdate := fun (names : List String)
      (relation : Metta.BindingRel) =>
    match relation with
    | .eq left right =>
        let names := if names.contains right then names else names ++ [right]
        if names.contains left then names else names ++ [left]
    | _ => names
  have hupdate : actualUpdate = leaEqOrderUpdate := by
    funext names relation
    cases relation <;> rfl
  change name ∈ bindings.reverse.foldl actualUpdate [] ↔ _
  rw [hupdate, mem_foldl_leaEqOrderUpdate_iff]
  simp only [List.not_mem_nil, false_or]
  rw [List.mem_flatMap, List.mem_flatMap]
  constructor <;> rintro ⟨relation, hrelation, hname⟩
  · exact ⟨relation, List.mem_reverse.mp hrelation, hname⟩
  · exact ⟨relation, List.mem_reverse.mpr hrelation, hname⟩

private theorem leaEqRelationNodes_eq_edgeNodes
    (bindings : Metta.Bindings) :
    bindings.flatMap leaEqRelationNodes =
      EqualityClosure.edgeNodes (leaEqualityEdges bindings) := by
  induction bindings with
  | nil => rfl
  | cons relation bindings ih =>
      cases relation with
      | val key value =>
          simpa [leaEqRelationNodes, leaEqualityEdges] using ih
      | eq left right =>
          simp [leaEqRelationNodes, leaEqualityEdges,
            EqualityClosure.edgeNodes, ih]

private theorem reachable_ne_finish_mem_edgeNodes
    {edges : List (String × String)} {start finish : String}
    (hne : start ≠ finish)
    (hreach : (EqualityClosure.edgeGraph edges).Reachable start finish) :
    finish ∈ EqualityClosure.edgeNodes edges := by
  apply hreach.elim
  intro walk
  have hfinish : finish ∈ start :: EqualityClosure.edgeNodes edges :=
    EqualityClosure.walk_support_subset_start_edgeNodes walk
      (SimpleGraph.Walk.end_mem_support walk)
  rcases List.mem_cons.mp hfinish with heq | hmem
  · exact (hne heq.symm).elim
  · exact hmem

/-- Connected Lea variables have one stable ordered equality class. -/
private theorem leaEqClassOrdered_eq_of_mem_eqClass
    {bindings : Metta.Bindings} {left right : String}
    (hmem : right ∈ Metta.Bindings.eqClass bindings left) :
    Metta.Bindings.eqClassOrdered bindings left =
      Metta.Bindings.eqClassOrdered bindings right := by
  have hreach :
      (EqualityClosure.edgeGraph (leaEqualityEdges bindings)).Reachable
        left right :=
    mem_leaEqClass_iff_reachable.mp hmem
  have hcontains : ∀ name,
      (Metta.Bindings.eqClass bindings left).contains name =
        (Metta.Bindings.eqClass bindings right).contains name := by
    intro name
    rw [Bool.eq_iff_iff, List.contains_iff_mem, List.contains_iff_mem,
      mem_leaEqClass_iff_reachable, mem_leaEqClass_iff_reachable]
    constructor
    · exact fun h => hreach.symm.trans h
    · exact fun h => hreach.trans h
  have hfilter :
      (Metta.Bindings.eqVarsInOrder bindings).filter
          (fun name =>
            (Metta.Bindings.eqClass bindings left).contains name) =
        (Metta.Bindings.eqVarsInOrder bindings).filter
          (fun name =>
            (Metta.Bindings.eqClass bindings right).contains name) := by
    apply List.filter_congr
    intro name _
    exact hcontains name
  unfold Metta.Bindings.eqClassOrdered
  rw [hfilter]
  generalize hfiltered :
      (Metta.Bindings.eqVarsInOrder bindings).filter
        (fun name =>
          (Metta.Bindings.eqClass bindings right).contains name) = filtered
  cases filtered with
  | nil =>
      by_cases heq : left = right
      · simp [heq]
      · exfalso
        have hleftNodes : left ∈
            EqualityClosure.edgeNodes (leaEqualityEdges bindings) :=
          reachable_ne_finish_mem_edgeNodes (Ne.symm heq) hreach.symm
        have hleftOrder :
            left ∈ Metta.Bindings.eqVarsInOrder bindings := by
          apply mem_leaEqVarsInOrder_iff.mpr
          rw [leaEqRelationNodes_eq_edgeNodes]
          exact hleftNodes
        have hleftClass :
            left ∈ Metta.Bindings.eqClass bindings right := by
          rw [mem_leaEqClass_iff_reachable]
          exact hreach.symm
        have hleftFilter : left ∈
            (Metta.Bindings.eqVarsInOrder bindings).filter
              (fun name =>
                (Metta.Bindings.eqClass bindings right).contains name) := by
          exact List.mem_filter.mpr
            ⟨hleftOrder, by simpa using hleftClass⟩
        rw [hfiltered] at hleftFilter
        simp at hleftFilter
  | cons first rest => rfl

private theorem mem_leaVars_of_mem_equalityNodes
    {bindings : Metta.Bindings} {name : String}
    (hname : name ∈
      EqualityClosure.edgeNodes (leaEqualityEdges bindings)) :
    name ∈ Metta.Bindings.vars bindings := by
  unfold EqualityClosure.edgeNodes at hname
  obtain ⟨edge, hedge, hendpoint⟩ := List.mem_flatMap.mp hname
  rcases edge with ⟨left, right⟩
  have hrelation : Metta.BindingRel.eq left right ∈ bindings :=
    mem_leaEqualityEdges_iff.mp hedge
  unfold Metta.Bindings.vars
  rw [List.mem_eraseDups, List.mem_flatMap]
  refine ⟨Metta.BindingRel.eq left right, hrelation, ?_⟩
  simpa using hendpoint

/-- On an acyclic Lea record, the executable class solution is constant on
each explicit equality class.  Thus every equality relation is satisfied
independently of the representative selected by stable relation order. -/
private theorem leaClassSolution_eq_of_mem_eqClass
    {bindings : Metta.Bindings} {left right : String}
    (hloop : bindings.hasLoop = false)
    (hmem : right ∈ Metta.Bindings.eqClass bindings left) :
    leaClassSolution bindings left = leaClassSolution bindings right := by
  by_cases heq : left = right
  · subst right
    rfl
  have hordered := leaEqClassOrdered_eq_of_mem_eqClass hmem
  have hleftMem : left ∈ Metta.Bindings.eqClassOrdered bindings left :=
    mem_leaEqClassOrdered_iff.mpr (by
      rw [mem_leaEqClass_iff_reachable])
  have hrightMem : right ∈ Metta.Bindings.eqClassOrdered bindings left :=
    mem_leaEqClassOrdered_iff.mpr hmem
  have hnotLeft :
      Metta.Bindings.eqClassOrdered bindings left ≠ [left] := by
    intro hsingle
    rw [hsingle] at hrightMem
    simp only [List.mem_singleton] at hrightMem
    exact heq hrightMem.symm
  have hnotRight :
      Metta.Bindings.eqClassOrdered bindings right ≠ [right] := by
    intro hsingle
    rw [hordered, hsingle] at hleftMem
    simp only [List.mem_singleton] at hleftMem
    exact heq hleftMem
  have hvalues :
      Metta.Bindings.classValues bindings left =
        Metta.Bindings.classValues bindings right := by
    unfold Metta.Bindings.classValues
    rw [hordered]
  have hfuel :
      Metta.Bindings.resolutionFuel bindings (.var left) =
        Metta.Bindings.resolutionFuel bindings (.var right) := by
    simp [Metta.Bindings.resolutionFuel, Metta.Atom.size]
  let leftAux := Metta.Bindings.resolveAtomAux bindings
    (Metta.Bindings.resolutionFuel bindings (.var left)) [] (.var left)
  let rightAux := Metta.Bindings.resolveAtomAux bindings
    (Metta.Bindings.resolutionFuel bindings (.var right)) [] (.var right)
  have hauxEq : leftAux = rightAux := by
    simp only [leftAux, rightAux]
    rw [hfuel]
    cases hfuelValue :
        Metta.Bindings.resolutionFuel bindings (.var right) with
    | zero =>
        simp [Metta.Bindings.resolutionFuel, Metta.Atom.size] at hfuelValue
    | succ fuel =>
        simp only [Metta.Bindings.resolveAtomAux]
        rw [hordered, hvalues]
        unfold Metta.Bindings.eqRepresentative
        rw [hordered]
        cases hclass : Metta.Bindings.eqClassOrdered bindings right with
        | nil =>
            rw [hordered, hclass] at hleftMem
            simp at hleftMem
        | cons representative rest => simp
  have hrecursive :
      (Metta.Bindings.vars bindings).any (fun name =>
        (Metta.Bindings.resolveAtomAux bindings
          (Metta.Bindings.resolutionFuel bindings (.var name)) []
          (.var name)).isNone) = false :=
    (Bool.or_eq_false_iff.mp hloop).2
  rw [List.any_eq_false] at hrecursive
  have hreach :
      (EqualityClosure.edgeGraph (leaEqualityEdges bindings)).Reachable
        left right :=
    mem_leaEqClass_iff_reachable.mp hmem
  have hleftNodes : left ∈
      EqualityClosure.edgeNodes (leaEqualityEdges bindings) :=
    reachable_ne_finish_mem_edgeNodes (Ne.symm heq) hreach.symm
  have hleftVars : left ∈ Metta.Bindings.vars bindings :=
    mem_leaVars_of_mem_equalityNodes hleftNodes
  have hleftSome : ∃ resolved, leftAux = some resolved := by
    have hnotNone := hrecursive left hleftVars
    cases haux : leftAux with
    | none =>
        exact (hnotNone (by simpa [leftAux] using haux)).elim
    | some resolved => exact ⟨resolved, rfl⟩
  obtain ⟨resolved, hleftSome⟩ := hleftSome
  have hrightSome : rightAux = some resolved :=
    hauxEq.symm.trans hleftSome
  unfold leaClassSolution Metta.Bindings.resolve
  have hguardLeft :
      ¬(Metta.Bindings.eqClassOrdered bindings left == [left]) = true := by
    simpa using hnotLeft
  have hguardRight :
      ¬(Metta.Bindings.eqClassOrdered bindings right == [right]) = true := by
    simpa using hnotRight
  simp only [hguardLeft, hguardRight]
  simp [leftAux, rightAux, hleftSome, hrightSome]

/-- The loop-free class resolver satisfies every explicit Lea equality edge. -/
private theorem leaClassSolution_satisfies_equalities
    {bindings : Metta.Bindings}
    (hloop : bindings.hasLoop = false) :
    ∀ left right, Metta.BindingRel.eq left right ∈ bindings →
      leaClassSolution bindings left = leaClassSolution bindings right := by
  intro left right hedge
  apply leaClassSolution_eq_of_mem_eqClass hloop
  rw [mem_leaEqClass_iff_reachable]
  by_cases heq : left = right
  · subst right
    exact .rfl
  · exact (show
      (EqualityClosure.edgeGraph (leaEqualityEdges bindings)).Adj left right
        from ⟨heq, Or.inl (mem_leaEqualityEdges_iff.mpr hedge)⟩).reachable

/-- Consequently value-class coherence is the only remaining obligation for
the executable class solution to model a loop-free Lea binding record. -/
private theorem leaClassSolution_satisfied_of_values
    {bindings : Metta.Bindings}
    (hloop : bindings.hasLoop = false)
    (hvalues : ∀ key value, Metta.BindingRel.val key value ∈ bindings →
      leaClassSolution bindings key =
        applyClassSolution (leaClassSolution bindings) value) :
    LeaBindingSatisfied (leaClassSolution bindings) bindings := by
  exact ⟨hvalues, leaClassSolution_satisfies_equalities hloop⟩

/-- A stored value relation guarantees that direct lookup at the same key
returns some value, possibly an earlier relation for that key. -/
private theorem exists_lookupVal_of_val_mem
    {bindings : Metta.Bindings} {key : String} {value : Metta.Atom}
    (hvalue : Metta.BindingRel.val key value ∈ bindings) :
    ∃ stored, Metta.Bindings.lookupVal bindings key = some stored := by
  induction bindings with
  | nil => simp at hvalue
  | cons relation bindings ih =>
    cases relation with
    | eq left right =>
      obtain ⟨stored, hlookup⟩ := ih (by simpa using hvalue)
      exact ⟨stored, by simpa [Metta.Bindings.lookupVal] using hlookup⟩
    | val storedKey storedValue =>
      by_cases hkey : key = storedKey
      · subst storedKey
        exact ⟨storedValue, by simp [Metta.Bindings.lookupVal]⟩
      · have htail : Metta.BindingRel.val key value ∈ bindings := by
          simpa [hkey] using hvalue
        obtain ⟨stored, hlookup⟩ := ih htail
        have hbeq : (key == storedKey) = false := by simp [hkey]
        exact ⟨stored, by
          simpa [Metta.Bindings.lookupVal, hbeq] using hlookup⟩

/-- Any two successful executions of the recursive Lea resolver on the same
atom return the same normal form, independently of fuel and visited context. -/
private theorem resolveAtomAux_some_unique
    (bindings : Metta.Bindings) :
    ∀ (leftFuel rightFuel : Nat) (leftVisited rightVisited : List String)
      (atom leftResult rightResult : Metta.Atom),
      Metta.Bindings.resolveAtomAux bindings leftFuel leftVisited atom =
          some leftResult →
      Metta.Bindings.resolveAtomAux bindings rightFuel rightVisited atom =
          some rightResult →
      leftResult = rightResult := by
  intro leftFuel
  induction leftFuel with
  | zero =>
    intro rightFuel leftVisited rightVisited atom leftResult rightResult
      hleft hright
    simp [Metta.Bindings.resolveAtomAux] at hleft
  | succ leftFuel ih =>
    intro rightFuel
    cases rightFuel with
    | zero =>
      intro leftVisited rightVisited atom leftResult rightResult hleft hright
      simp [Metta.Bindings.resolveAtomAux] at hright
    | succ rightFuel =>
      intro leftVisited rightVisited atom leftResult rightResult hleft hright
      cases atom with
      | sym symbol =>
        simp [Metta.Bindings.resolveAtomAux] at hleft hright
        subst leftResult
        subst rightResult
        rfl
      | gnd ground =>
        simp [Metta.Bindings.resolveAtomAux] at hleft hright
        subst leftResult
        subst rightResult
        rfl
      | var key =>
        simp only [Metta.Bindings.resolveAtomAux] at hleft hright
        cases hleftOverlap :
            (Metta.Bindings.eqClassOrdered bindings key).any
              leftVisited.contains with
        | true => simp [hleftOverlap] at hleft
        | false =>
          cases hrightOverlap :
              (Metta.Bindings.eqClassOrdered bindings key).any
                rightVisited.contains with
          | true => simp [hrightOverlap] at hright
          | false =>
            cases hvalues : Metta.Bindings.classValues bindings key with
            | nil =>
              simp [hleftOverlap, hrightOverlap, hvalues] at hleft hright
              subst leftResult
              subst rightResult
              rfl
            | cons value rest =>
              cases value with
              | var target =>
                cases hcontains :
                    (Metta.Bindings.eqClassOrdered bindings key).contains target with
                | true =>
                  cases hlength :
                      (Metta.Bindings.eqClassOrdered bindings key).length == 1 with
                  | true =>
                    have htargetMem : target ∈
                        Metta.Bindings.eqClassOrdered bindings key := by
                      simpa using hcontains
                    simp [hleftOverlap, hvalues, hlength] at hleft
                    exact (hleft.1 htargetMem).elim
                  | false =>
                    have htargetMem : target ∈
                        Metta.Bindings.eqClassOrdered bindings key := by
                      simpa using hcontains
                    simp [hleftOverlap, hrightOverlap, hvalues, hlength,
                      htargetMem] at hleft hright
                    subst leftResult
                    subst rightResult
                    rfl
                | false =>
                  simp only [hleftOverlap, hrightOverlap, hvalues, hcontains,
                    Bool.false_eq_true, ↓reduceIte] at hleft hright
                  exact ih rightFuel _ _ _ _ _ hleft hright
              | sym symbol | gnd symbol | expr symbol =>
                simp only [hleftOverlap, hrightOverlap, hvalues,
                  Bool.false_eq_true, ↓reduceIte] at hleft hright
                exact ih rightFuel _ _ _ _ _ hleft hright
      | expr atoms =>
        simp only [Metta.Bindings.resolveAtomAux] at hleft hright
        cases hleftMap : atoms.mapM
            (Metta.Bindings.resolveAtomAux bindings leftFuel leftVisited) with
        | none => simp [hleftMap] at hleft
        | some leftAtoms =>
          cases hrightMap : atoms.mapM
              (Metta.Bindings.resolveAtomAux bindings rightFuel rightVisited) with
          | none => simp [hrightMap] at hright
          | some rightAtoms =>
            simp [hleftMap] at hleft
            simp [hrightMap] at hright
            subst leftResult
            subst rightResult
            congr 1
            induction atoms generalizing leftAtoms rightAtoms with
            | nil =>
              simp at hleftMap hrightMap
              subst leftAtoms
              subst rightAtoms
              rfl
            | cons head tail tailIH =>
              simp only [List.mapM_cons] at hleftMap hrightMap
              cases hleftHead : Metta.Bindings.resolveAtomAux bindings
                  leftFuel leftVisited head with
              | none => simp [hleftHead] at hleftMap
              | some leftHead =>
                cases hrightHead : Metta.Bindings.resolveAtomAux bindings
                    rightFuel rightVisited head with
                | none => simp [hrightHead] at hrightMap
                | some rightHead =>
                  cases hleftTail : tail.mapM
                      (Metta.Bindings.resolveAtomAux bindings
                        leftFuel leftVisited) with
                  | none => simp [hleftHead, hleftTail] at hleftMap
                  | some leftTail =>
                    cases hrightTail : tail.mapM
                        (Metta.Bindings.resolveAtomAux bindings
                          rightFuel rightVisited) with
                    | none => simp [hrightHead, hrightTail] at hrightMap
                    | some rightTail =>
                      simp [hleftHead, hleftTail] at hleftMap
                      simp [hrightHead, hrightTail] at hrightMap
                      subst leftAtoms
                      subst rightAtoms
                      exact congrArg₂ List.cons
                        (ih rightFuel _ _ _ _ _ hleftHead hrightHead)
                        (tailIH leftTail hleftTail rightTail hrightTail)

private theorem mem_leaVars_of_val_key
    {bindings : Metta.Bindings} {key : String} {value : Metta.Atom}
    (hvalue : Metta.BindingRel.val key value ∈ bindings) :
    key ∈ Metta.Bindings.vars bindings := by
  unfold Metta.Bindings.vars
  rw [List.mem_eraseDups, List.mem_flatMap]
  exact ⟨Metta.BindingRel.val key value, hvalue, by simp⟩

private theorem mem_leaVars_of_mem_val_vars
    {bindings : Metta.Bindings} {key name : String} {value : Metta.Atom}
    (hvalue : Metta.BindingRel.val key value ∈ bindings)
    (hname : name ∈ value.vars) :
    name ∈ Metta.Bindings.vars bindings := by
  unfold Metta.Bindings.vars
  rw [List.mem_eraseDups, List.mem_flatMap]
  exact ⟨Metta.BindingRel.val key value, hvalue, by simp [hname]⟩

/-- Loop rejection guarantees a successful top-level recursive resolution
for every variable mentioned by the binding record. -/
private theorem exists_resolveAtomAux_of_hasLoop_false
    {bindings : Metta.Bindings} (hloop : bindings.hasLoop = false)
    {key : String} (hkey : key ∈ Metta.Bindings.vars bindings) :
    ∃ resolved, Metta.Bindings.resolveAtomAux bindings
      (Metta.Bindings.resolutionFuel bindings (.var key)) [] (.var key) =
        some resolved := by
  have hrecursive := (Bool.or_eq_false_iff.mp hloop).2
  rw [List.any_eq_false] at hrecursive
  have hnotNone := hrecursive key hkey
  cases hresolve : Metta.Bindings.resolveAtomAux bindings
      (Metta.Bindings.resolutionFuel bindings (.var key)) [] (.var key) with
  | none => exact (hnotNone (by simp [hresolve])).elim
  | some resolved => exact ⟨resolved, rfl⟩

/-- A successful top-level recursive resolution is exactly the value exposed
by `leaClassSolution`, including the deliberately unresolved singleton case. -/
private theorem leaClassSolution_eq_of_resolveAtomAux_some
    {bindings : Metta.Bindings} {key : String} {resolved : Metta.Atom}
    (hresolve : Metta.Bindings.resolveAtomAux bindings
      (Metta.Bindings.resolutionFuel bindings (.var key)) [] (.var key) =
        some resolved) :
    leaClassSolution bindings key = resolved := by
  cases hguard :
      ((Metta.Bindings.eqClassOrdered bindings key == [key]) &&
        (Metta.Bindings.classValues bindings key).isEmpty) with
  | false =>
    simp [leaClassSolution, Metta.Bindings.resolve, hguard, hresolve]
  | true =>
    have hparts :
        (Metta.Bindings.eqClassOrdered bindings key == [key]) = true ∧
          (Metta.Bindings.classValues bindings key).isEmpty = true := by
      simpa only [Bool.and_eq_true] using hguard
    have hclass : Metta.Bindings.eqClassOrdered bindings key = [key] := by
      simpa using hparts.1
    have hvalues : Metta.Bindings.classValues bindings key = [] := by
      cases hvalues : Metta.Bindings.classValues bindings key with
      | nil => rfl
      | cons value rest => simp [hvalues] at hparts
    cases hfuel : Metta.Bindings.resolutionFuel bindings (.var key) with
    | zero =>
      simp [Metta.Bindings.resolutionFuel, Metta.Atom.size] at hfuel
    | succ fuel =>
      rw [hfuel] at hresolve
      simp only [Metta.Bindings.resolveAtomAux] at hresolve
      simp [hclass, hvalues] at hresolve
      subst resolved
      have hrepresentative :
          Metta.Bindings.eqRepresentative bindings key = key := by
        simp [Metta.Bindings.eqRepresentative, hclass]
      simp [leaClassSolution, Metta.Bindings.resolve, hguard,
        hrepresentative]

/-- Successful contextual resolution agrees with homomorphic application of
the total class solution whenever all atom variables occur in the binding. -/
private theorem resolveAtomAux_eq_applyClassSolution_of_hasLoop_false
    {bindings : Metta.Bindings} (hloop : bindings.hasLoop = false) :
    ∀ atom : Metta.Atom,
      (∀ name, name ∈ atom.vars → name ∈ Metta.Bindings.vars bindings) →
      ∀ fuel visited resolved,
        Metta.Bindings.resolveAtomAux bindings fuel visited atom =
            some resolved →
          resolved = applyClassSolution (leaClassSolution bindings) atom := by
  intro atom
  induction atom with
  | sym symbol =>
    intro hvars fuel visited resolved hresolve
    cases fuel with
    | zero => simp [Metta.Bindings.resolveAtomAux] at hresolve
    | succ fuel =>
      simp [Metta.Bindings.resolveAtomAux] at hresolve
      subst resolved
      simp [applyClassSolution]
  | gnd ground =>
    intro hvars fuel visited resolved hresolve
    cases fuel with
    | zero => simp [Metta.Bindings.resolveAtomAux] at hresolve
    | succ fuel =>
      simp [Metta.Bindings.resolveAtomAux] at hresolve
      subst resolved
      simp [applyClassSolution]
  | var key =>
    intro hvars fuel visited resolved hresolve
    have hkey : key ∈ Metta.Bindings.vars bindings :=
      hvars key (by simp [Metta.Atom.vars])
    obtain ⟨top, htop⟩ :=
      exists_resolveAtomAux_of_hasLoop_false hloop hkey
    have heq : resolved = top :=
      resolveAtomAux_some_unique bindings fuel
        (Metta.Bindings.resolutionFuel bindings (.var key))
        visited [] (.var key) resolved top hresolve htop
    have hcanonical : leaClassSolution bindings key = top :=
      leaClassSolution_eq_of_resolveAtomAux_some htop
    simpa only [applyClassSolution, hcanonical] using heq
  | expr atoms ih =>
    intro hvars fuel visited resolved hresolve
    cases fuel with
    | zero => simp [Metta.Bindings.resolveAtomAux] at hresolve
    | succ fuel =>
      simp only [Metta.Bindings.resolveAtomAux] at hresolve
      cases hmap : atoms.mapM
          (Metta.Bindings.resolveAtomAux bindings fuel visited) with
      | none => simp [hmap] at hresolve
      | some resolvedAtoms =>
        simp [hmap] at hresolve
        subst resolved
        simp only [applyClassSolution, Metta.Atom.expr.injEq]
        induction atoms generalizing resolvedAtoms with
        | nil =>
          simp at hmap
          subst resolvedAtoms
          rfl
        | cons head tail tailIH =>
          simp only [List.mapM_cons] at hmap
          cases hhead : Metta.Bindings.resolveAtomAux bindings fuel
              visited head with
          | none => simp [hhead] at hmap
          | some resolvedHead =>
            cases htail : tail.mapM
                (Metta.Bindings.resolveAtomAux bindings fuel visited) with
            | none => simp [hhead, htail] at hmap
            | some resolvedTail =>
              simp [hhead, htail] at hmap
              subst resolvedAtoms
              simp only [List.map_cons, List.cons.injEq]
              constructor
              · apply ih head (by simp) (fun name hname => hvars name (by
                    simp only [Metta.Atom.vars, List.mem_flatten, List.mem_map]
                    exact ⟨head.vars, ⟨head, by simp, rfl⟩, hname⟩))
                  fuel visited resolvedHead hhead
              · apply tailIH
                · intro child hchild
                  exact ih child (by simp [hchild])
                · intro name hname
                  apply hvars name
                  simp only [Metta.Atom.vars, List.mem_flatten,
                    List.mem_map] at hname ⊢
                  rcases hname with ⟨variableList, hlist, hname⟩
                  rcases hlist with ⟨child, hchild, rfl⟩
                  exact ⟨child.vars, ⟨child, by simp [hchild], rfl⟩, hname⟩
                · exact htail

/-- In a loop-free binding, the class resolver unfolds through the selected
first non-variable class value. -/
private theorem leaClassSolution_eq_apply_firstClassValue
    {bindings : Metta.Bindings} {key : String}
    {first : Metta.Atom} {tail : List Metta.Atom}
    (hloop : bindings.hasLoop = false)
    (hvalues : Metta.Bindings.classValues bindings key = first :: tail)
    (hfirstNonvar : ∀ target, first ≠ .var target) :
    leaClassSolution bindings key =
      applyClassSolution (leaClassSolution bindings) first := by
  have hfirstMem : first ∈ Metta.Bindings.classValues bindings key := by
    rw [hvalues]
    simp
  obtain ⟨storedKey, hstoredClass, hstored⟩ :=
    leaClassValue_relation hfirstMem
  have hkeyVars : key ∈ Metta.Bindings.vars bindings := by
    have hclass : storedKey ∈ Metta.Bindings.eqClass bindings key :=
      mem_leaEqClassOrdered_iff.mp hstoredClass
    by_cases heq : key = storedKey
    · subst storedKey
      exact mem_leaVars_of_val_key hstored
    · have hreach :
          (EqualityClosure.edgeGraph (leaEqualityEdges bindings)).Reachable
            key storedKey :=
        mem_leaEqClass_iff_reachable.mp hclass
      have hkeyNode : key ∈
          EqualityClosure.edgeNodes (leaEqualityEdges bindings) :=
        reachable_ne_finish_mem_edgeNodes (Ne.symm heq) hreach.symm
      exact mem_leaVars_of_mem_equalityNodes hkeyNode
  have hfirstVars : ∀ name, name ∈ first.vars →
      name ∈ Metta.Bindings.vars bindings := by
    intro name hname
    exact mem_leaVars_of_mem_val_vars hstored hname
  obtain ⟨resolved, htop⟩ :=
    exists_resolveAtomAux_of_hasLoop_false hloop hkeyVars
  have hcanonical : leaClassSolution bindings key = resolved :=
    leaClassSolution_eq_of_resolveAtomAux_some htop
  have hfuelPos : 0 <
      Metta.Bindings.resolutionFuel bindings (.var key) := by
    simp [Metta.Bindings.resolutionFuel, Metta.Atom.size]
  have hfuel : Metta.Bindings.resolutionFuel bindings (.var key) =
      (Metta.Bindings.resolutionFuel bindings (.var key)).pred + 1 :=
    (Nat.succ_pred_eq_of_pos hfuelPos).symm
  rw [hfuel] at htop
  simp only [Metta.Bindings.resolveAtomAux] at htop
  have hoverlap :
      (Metta.Bindings.eqClassOrdered bindings key).any
        ([] : List String).contains = false := by simp
  simp only [hoverlap, Bool.false_eq_true, ↓reduceIte, hvalues] at htop
  cases first with
  | var target => exact (hfirstNonvar target rfl).elim
  | sym symbol | gnd symbol | expr symbol =>
    exact hcanonical.trans
      (resolveAtomAux_eq_applyClassSolution_of_hasLoop_false hloop _
        hfirstVars _ _ _ htop)

/-- Every successful recursive Lea resolver path is semantically inert in
every model of the binding equations.  The resolver may choose a stable class
representative and recursively normalize class values, but those choices do
not change their interpretation. -/
private theorem applyClassSolution_resolveAtomAux_eq_of_satisfied
    {bindings : Metta.Bindings} {valuation : String → Metta.Atom}
    (hsatisfied : LeaBindingSatisfied valuation bindings) :
    ∀ (fuel : Nat) (visited : List String)
      (atom resolved : Metta.Atom),
      Metta.Bindings.resolveAtomAux bindings fuel visited atom =
          some resolved →
        applyClassSolution valuation resolved =
          applyClassSolution valuation atom := by
  intro fuel
  induction fuel with
  | zero =>
      intro visited atom resolved hresolve
      simp [Metta.Bindings.resolveAtomAux] at hresolve
  | succ fuel ih =>
      intro visited atom resolved hresolve
      cases atom with
      | sym symbol =>
          simp [Metta.Bindings.resolveAtomAux] at hresolve
          subst resolved
          rfl
      | gnd ground =>
          simp [Metta.Bindings.resolveAtomAux] at hresolve
          subst resolved
          rfl
      | var key =>
          simp only [Metta.Bindings.resolveAtomAux] at hresolve
          cases hoverlap :
              (Metta.Bindings.eqClassOrdered bindings key).any
                visited.contains with
          | true => simp [hoverlap] at hresolve
          | false =>
              cases hvalues : Metta.Bindings.classValues bindings key with
              | nil =>
                  simp [hoverlap, hvalues] at hresolve
                  subst resolved
                  simpa [applyClassSolution] using
                    (hsatisfied.eq_of_mem_eqClass
                      (mem_leaEqClassOrdered_iff.mp
                        (leaEqRepresentative_mem_eqClassOrdered
                          bindings key))).symm
              | cons value rest =>
                  have hvalueMem : value ∈
                      Metta.Bindings.classValues bindings key := by
                    rw [hvalues]
                    simp
                  have hvalueEquation : valuation key =
                      applyClassSolution valuation value :=
                    leaBindingSatisfied_classValue hsatisfied hvalueMem
                  cases value with
                  | var target =>
                      simp only [hoverlap, Bool.false_eq_true, ↓reduceIte,
                        hvalues] at hresolve
                      cases hcontains :
                          (Metta.Bindings.eqClassOrdered bindings key).contains
                            target with
                      | true =>
                          simp only [hcontains, ↓reduceIte] at hresolve
                          cases hlength :
                              (Metta.Bindings.eqClassOrdered bindings key).length ==
                                1 with
                          | true => simp [hlength] at hresolve
                          | false =>
                              simp [hlength] at hresolve
                              subst resolved
                              simpa [applyClassSolution] using
                                (hsatisfied.eq_of_mem_eqClass
                                  (mem_leaEqClassOrdered_iff.mp
                                    (leaEqRepresentative_mem_eqClassOrdered
                                      bindings key))).symm
                      | false =>
                          simp only [hcontains, Bool.false_eq_true,
                            ↓reduceIte] at hresolve
                          exact (ih _ _ _ hresolve).trans (by
                            simpa [applyClassSolution] using
                              hvalueEquation.symm)
                  | sym symbol =>
                      simp only [hoverlap, Bool.false_eq_true, ↓reduceIte,
                        hvalues] at hresolve
                      exact (ih _ _ _ hresolve).trans (by
                        simpa [applyClassSolution] using hvalueEquation.symm)
                  | gnd ground =>
                      simp only [hoverlap, Bool.false_eq_true, ↓reduceIte,
                        hvalues] at hresolve
                      exact (ih _ _ _ hresolve).trans (by
                        simpa [applyClassSolution] using hvalueEquation.symm)
                  | expr atoms =>
                      simp only [hoverlap, Bool.false_eq_true, ↓reduceIte,
                        hvalues] at hresolve
                      exact (ih _ _ _ hresolve).trans (by
                        simpa [applyClassSolution] using hvalueEquation.symm)
      | expr atoms =>
          simp only [Metta.Bindings.resolveAtomAux] at hresolve
          cases hmap : atoms.mapM
              (Metta.Bindings.resolveAtomAux bindings fuel visited) with
          | none => simp [hmap] at hresolve
          | some resolvedAtoms =>
              simp [hmap] at hresolve
              subst resolved
              simp only [applyClassSolution]
              congr 1
              have hmaps : List.map (applyClassSolution valuation)
                    resolvedAtoms =
                  List.map (applyClassSolution valuation) atoms := by
                induction atoms generalizing resolvedAtoms with
                | nil =>
                    simp at hmap
                    subst resolvedAtoms
                    rfl
                | cons head tail tailIH =>
                    simp only [List.mapM_cons] at hmap
                    cases hhead : Metta.Bindings.resolveAtomAux bindings fuel
                        visited head with
                    | none => simp [hhead] at hmap
                    | some resolvedHead =>
                        cases htail : tail.mapM
                            (Metta.Bindings.resolveAtomAux bindings fuel visited) with
                        | none => simp [hhead, htail] at hmap
                        | some resolvedTail =>
                            simp [hhead, htail] at hmap
                            subst resolvedAtoms
                            simp [ih _ _ _ hhead,
                              tailIH resolvedTail htail]
              exact hmaps

/-- On normalized satisfiable bindings, every concrete model absorbs
LeaTTa's total class-solution valuation.  Runtime termination comes from the
existing semantic rank theorem; the preceding lemma supplies the semantic
equality of the selected result. -/
private theorem applyClassSolution_leaClassSolution_eq_of_satisfied
    {bindings : Metta.Bindings} {valuation : String → Metta.Atom}
    (hsatisfied : LeaBindingSatisfied valuation bindings)
    (hnonvariable : LeaAssignmentsNonVariable bindings) :
    ∀ name,
      applyClassSolution valuation (leaClassSolution bindings name) =
        valuation name := by
  intro name
  cases hguard :
      ((Metta.Bindings.eqClassOrdered bindings name == [name]) &&
        (Metta.Bindings.classValues bindings name).isEmpty) with
  | true =>
      simp [leaClassSolution, Metta.Bindings.resolve, hguard,
        applyClassSolution]
  | false =>
      obtain ⟨resolved, hresolved⟩ :=
        leaResolveAtomAux_some_of_satisfied hsatisfied hnonvariable name
      have hresolve : Metta.Bindings.resolve bindings name = some resolved := by
        simp [Metta.Bindings.resolve, hguard, hresolved]
      have hsemantic :=
        applyClassSolution_resolveAtomAux_eq_of_satisfied hsatisfied
          (Metta.Bindings.resolutionFuel bindings (.var name)) []
          (.var name) resolved hresolved
      simpa [leaClassSolution, hresolve, applyClassSolution] using hsemantic

/-- Therefore canonical-model satisfaction is the only remaining obligation
for canonical principality: factorization follows uniformly from resolver
absorption. -/
private theorem canonicallyPrincipal_of_canonical_satisfied
    {bindings : Metta.Bindings}
    (hsatisfied : LeaBindingSatisfied (leaClassSolution bindings) bindings)
    (hnonvariable : LeaAssignmentsNonVariable bindings) :
    CanonicallyPrincipal bindings := by
  refine ⟨hsatisfied, ?_⟩
  intro specific hspecific
  refine ⟨specific, fun name => ?_⟩
  exact (applyClassSolution_leaClassSolution_eq_of_satisfied
    hspecific hnonvariable name).symm

/-! ### Principal whole-binding reconciliation -/

/-- If the valuation synthesized from an elimination trace sends one
variable to another, the trace's variable edges connect them. -/
private theorem eliminationTraceValuation_eq_var_reachable :
    ∀ (trace : List (String × Metta.Atom)) (start finish : String),
      eliminationTraceValuation trace start = .var finish →
        (EqualityClosure.edgeGraph
          (eliminationTraceAliases trace)).Reachable start finish := by
  intro trace
  induction trace with
  | nil =>
    intro start finish hvalue
    simp only [eliminationTraceValuation] at hvalue
    cases hvalue
    exact .rfl
  | cons binding trace ih =>
    rcases binding with ⟨key, value⟩
    intro start finish hvalue
    have liftTail : ∀ {left right : String},
        (EqualityClosure.edgeGraph
          (eliminationTraceAliases trace)).Reachable left right →
        (EqualityClosure.edgeGraph
          (eliminationTraceAliases ((key, value) :: trace))).Reachable
            left right := by
      intro left right hreach
      apply hreach.mono
      intro first second hadj
      rw [EqualityClosure.edgeGraph_adj_iff] at hadj ⊢
      rcases hadj with ⟨hne, hforward | hreverse⟩
      · refine ⟨hne, Or.inl ?_⟩
        cases value <;> simp [eliminationTraceAliases, hforward]
      · refine ⟨hne, Or.inr ?_⟩
        cases value <;> simp [eliminationTraceAliases, hreverse]
    by_cases hstart : start = key
    · subst start
      simp only [eliminationTraceValuation, Function.update_self] at hvalue
      cases value with
      | var target =>
        simp only [applyClassSolution] at hvalue
        have htail := liftTail (ih target finish hvalue)
        by_cases hsame : key = target
        · subst target
          exact htail
        · have hhead :
              (EqualityClosure.edgeGraph
                (eliminationTraceAliases
                  ((key, Metta.Atom.var target) :: trace))).Reachable
                    key target := by
            apply (show
              (EqualityClosure.edgeGraph
                (eliminationTraceAliases
                  ((key, Metta.Atom.var target) :: trace))).Adj
                    key target by
              rw [EqualityClosure.edgeGraph_adj_iff]
              exact ⟨hsame, Or.inl (by
                simp [eliminationTraceAliases])⟩).reachable
          exact hhead.trans htail
      | sym symbol | gnd symbol | expr symbol =>
        simp only [applyClassSolution] at hvalue
        exact Metta.Atom.noConfusion hvalue
    · have htailValue :
          eliminationTraceValuation trace start = .var finish := by
        simpa [eliminationTraceValuation, Function.update, hstart] using hvalue
      exact liftTail (ih start finish htailValue)

/-- The canonical resolver of a loop-free reconciliation rebuild identifies
every variable-to-variable step of the reconciliation trace valuation. -/
private theorem reconciliationTraceValuation_var_classSolution_eq
    {candidate source : Metta.Bindings}
    {extra : List (Metta.Atom × Metta.Atom)} {result : Metta.Subst}
    (hreconcile : wholeBindingReconciliation source extra = some result)
    (hloop : (Metta.Bindings.rebuildFromReconciliation
      candidate source extra result).hasLoop = false) :
    let trace := unificationEliminationTrace
      (Metta.Bindings.equationFuel
        (Metta.Bindings.equations source ++ extra))
      (Metta.Bindings.equations source ++ extra)
    ∀ start finish,
      eliminationTraceValuation trace start = .var finish →
        leaClassSolution
            (Metta.Bindings.rebuildFromReconciliation
              candidate source extra result) start =
          leaClassSolution
            (Metta.Bindings.rebuildFromReconciliation
              candidate source extra result) finish := by
  dsimp only
  intro start finish hvalue
  have htraceReach :=
    eliminationTraceValuation_eq_var_reachable _ start finish hvalue
  have htargetReach :
      (EqualityClosure.edgeGraph
        (leaEqualityEdges candidate ++
          Metta.Bindings.reconciliationAliases source extra result)).Reachable
          start finish := by
    apply htraceReach.mono
    intro left right hadj
    rw [EqualityClosure.edgeGraph_adj_iff] at hadj ⊢
    rcases hadj with ⟨hne, hforward | hreverse⟩
    · exact ⟨hne, Or.inl (List.mem_append_right _
        (eliminationTraceAliases_subset_reconciliationAliases hreconcile
          (left, right) hforward))⟩
    · exact ⟨hne, Or.inr (List.mem_append_right _
        (eliminationTraceAliases_subset_reconciliationAliases hreconcile
          (right, left) hreverse))⟩
  have hclass : finish ∈ Metta.Bindings.eqClass
      (Metta.Bindings.rebuildFromReconciliation
        candidate source extra result) start :=
    (rebuildFromReconciliation_class_iff hreconcile).mpr htargetReach
  exact leaClassSolution_eq_of_mem_eqClass hloop hclass

/-- Trace-variable connectivity embeds into the equality class of every
successful reconciliation rebuild. -/
private theorem eliminationTraceReachable_mem_rebuildEqClass
    {candidate source : Metta.Bindings}
    {extra : List (Metta.Atom × Metta.Atom)} {result : Metta.Subst}
    (hreconcile : wholeBindingReconciliation source extra = some result)
    {start finish : String}
    (hreach : (EqualityClosure.edgeGraph
      (eliminationTraceAliases
        (unificationEliminationTrace
          (Metta.Bindings.equationFuel
            (Metta.Bindings.equations source ++ extra))
          (Metta.Bindings.equations source ++ extra)))).Reachable
        start finish) :
    finish ∈ Metta.Bindings.eqClass
      (Metta.Bindings.rebuildFromReconciliation
        candidate source extra result) start := by
  apply (rebuildFromReconciliation_class_iff hreconcile).mpr
  apply hreach.mono
  intro left right hadj
  rw [EqualityClosure.edgeGraph_adj_iff] at hadj ⊢
  rcases hadj with ⟨hne, hforward | hreverse⟩
  · exact ⟨hne, Or.inl (List.mem_append_right _
      (eliminationTraceAliases_subset_reconciliationAliases hreconcile
        (left, right) hforward))⟩
  · exact ⟨hne, Or.inr (List.mem_append_right _
      (eliminationTraceAliases_subset_reconciliationAliases hreconcile
        (right, left) hreverse))⟩

/-- A non-variable image of a triangular elimination-trace valuation comes
from a non-variable trace entry in the same variable-edge component. -/
private theorem eliminationTraceValuation_nonvar_origin :
    ∀ (trace : List (String × Metta.Atom)),
      EliminationTraceTriangular trace →
      (∀ key value, (key, value) ∈ trace → key ∉ value.vars) →
      ∀ start, (∀ target,
        eliminationTraceValuation trace start ≠ .var target) →
      ∃ key value,
        (key, value) ∈ trace ∧
          (∀ target, value ≠ .var target) ∧
          eliminationTraceValuation trace start =
            eliminationTraceValuation trace key ∧
          (EqualityClosure.edgeGraph
            (eliminationTraceAliases trace)).Reachable start key := by
  intro trace
  induction trace with
  | nil =>
    intro htriangular hoccurs start hnonvar
    exact (hnonvar start (by simp [eliminationTraceValuation])).elim
  | cons binding trace ih =>
    rcases binding with ⟨headKey, headValue⟩
    intro htriangular hoccurs start hnonvar
    have htriangularTail : EliminationTraceTriangular trace := by
      simpa only [EliminationTraceTriangular] using htriangular.2
    have hheadFresh : headKey ∉ mettaConstraintVars trace := by
      simpa only [EliminationTraceTriangular] using htriangular.1
    have hoccursHead : headKey ∉ headValue.vars :=
      hoccurs headKey headValue (by simp)
    have hoccursTail : ∀ key value, (key, value) ∈ trace →
        key ∉ value.vars := by
      intro key value hmem
      exact hoccurs key value (by simp [hmem])
    have originKey_ne_headKey : ∀ {key value},
        (key, value) ∈ trace → key ≠ headKey := by
      intro key value hmem heq
      subst key
      apply hheadFresh
      unfold mettaConstraintVars
      apply List.mem_flatMap.mpr
      exact ⟨(headKey, value), hmem, by simp⟩
    have liftTail : ∀ {left right : String},
        (EqualityClosure.edgeGraph
          (eliminationTraceAliases trace)).Reachable left right →
        (EqualityClosure.edgeGraph
          (eliminationTraceAliases
            ((headKey, headValue) :: trace))).Reachable left right := by
      intro left right hreach
      apply hreach.mono
      intro first second hadj
      rw [EqualityClosure.edgeGraph_adj_iff] at hadj ⊢
      rcases hadj with ⟨hne, hforward | hreverse⟩
      · refine ⟨hne, Or.inl ?_⟩
        cases headValue <;> simp [eliminationTraceAliases, hforward]
      · refine ⟨hne, Or.inr ?_⟩
        cases headValue <;> simp [eliminationTraceAliases, hreverse]
    by_cases hstart : start = headKey
    · subst start
      cases headValue with
      | var target =>
        have htargetNe : headKey ≠ target := by
          intro heq
          subst target
          exact hoccursHead (by simp [Metta.Atom.vars])
        have htailNonvar : ∀ result,
            eliminationTraceValuation trace target ≠ .var result := by
          intro result hresult
          apply hnonvar result
          simpa [eliminationTraceValuation, applyClassSolution] using hresult
        obtain ⟨key, value, hmem, hvalueNonvar, heq, hreach⟩ :=
          ih htriangularTail hoccursTail target htailNonvar
        have hkeyNe := originKey_ne_headKey hmem
        refine ⟨key, value, by simp [hmem], hvalueNonvar, ?_, ?_⟩
        · simpa [eliminationTraceValuation, applyClassSolution,
            htargetNe, hkeyNe] using heq
        · have hhead :
              (EqualityClosure.edgeGraph
                (eliminationTraceAliases
                  ((headKey, Metta.Atom.var target) :: trace))).Reachable
                    headKey target := by
            apply (show
              (EqualityClosure.edgeGraph
                (eliminationTraceAliases
                  ((headKey, Metta.Atom.var target) :: trace))).Adj
                    headKey target by
              rw [EqualityClosure.edgeGraph_adj_iff]
              exact ⟨htargetNe, Or.inl (by
                simp [eliminationTraceAliases])⟩).reachable
          exact hhead.trans (liftTail hreach)
      | sym symbol =>
        refine ⟨headKey, .sym symbol, by simp, ?_, rfl, .rfl⟩
        intro target h
        cases h
      | gnd grounded =>
        refine ⟨headKey, .gnd grounded, by simp, ?_, rfl, .rfl⟩
        intro target h
        cases h
      | expr atoms =>
        refine ⟨headKey, .expr atoms, by simp, ?_, rfl, .rfl⟩
        intro target h
        cases h
    · have htailNonvar : ∀ target,
          eliminationTraceValuation trace start ≠ .var target := by
        intro target hvalue
        apply hnonvar target
        simpa [eliminationTraceValuation, Function.update, hstart] using hvalue
      obtain ⟨key, value, hmem, hvalueNonvar, heq, hreach⟩ :=
        ih htriangularTail hoccursTail start htailNonvar
      have hkeyNe := originKey_ne_headKey hmem
      refine ⟨key, value, by simp [hmem], hvalueNonvar, ?_, liftTail hreach⟩
      simpa [eliminationTraceValuation, Function.update, hstart, hkeyNe]
        using heq

/-- Once the canonical resolver is known to unfold through the first value
of each nonempty class, every non-variable trace image has the canonical pick
required by `sigma_canonical_transfer`. -/
private theorem reconciliationTraceValuation_nonvar_pick
    {candidate source : Metta.Bindings}
    {extra : List (Metta.Atom × Metta.Atom)} {result : Metta.Subst}
    (hreconcile : wholeBindingReconciliation source extra = some result)
    (hsatisfied :
      let trace := unificationEliminationTrace
        (Metta.Bindings.equationFuel
          (Metta.Bindings.equations source ++ extra))
        (Metta.Bindings.equations source ++ extra)
      LeaBindingSatisfied (eliminationTraceValuation trace)
        (Metta.Bindings.rebuildFromReconciliation
          candidate source extra result))
    (hfirstUnfold : ∀ start first tail,
      Metta.Bindings.classValues
          (Metta.Bindings.rebuildFromReconciliation
            candidate source extra result) start = first :: tail →
        (∀ target, first ≠ Metta.Atom.var target) →
        leaClassSolution
            (Metta.Bindings.rebuildFromReconciliation
              candidate source extra result) start =
          applyClassSolution
            (leaClassSolution
              (Metta.Bindings.rebuildFromReconciliation
                candidate source extra result)) first) :
    let trace := unificationEliminationTrace
      (Metta.Bindings.equationFuel
        (Metta.Bindings.equations source ++ extra))
      (Metta.Bindings.equations source ++ extra)
    ∀ start, (∀ target,
      eliminationTraceValuation trace start ≠ .var target) →
      ∃ value, (∀ target, value ≠ Metta.Atom.var target) ∧
        applyClassSolution (eliminationTraceValuation trace) value =
          eliminationTraceValuation trace start ∧
        leaClassSolution
            (Metta.Bindings.rebuildFromReconciliation
              candidate source extra result) start =
          applyClassSolution
            (leaClassSolution
              (Metta.Bindings.rebuildFromReconciliation
                candidate source extra result)) value := by
  dsimp only at hsatisfied ⊢
  intro start hnonvar
  let trace := unificationEliminationTrace
    (Metta.Bindings.equationFuel
      (Metta.Bindings.equations source ++ extra))
    (Metta.Bindings.equations source ++ extra)
  have htriangular : EliminationTraceTriangular trace := by
    simpa [trace] using
      wholeBindingReconciliation_eliminationTrace_triangular hreconcile
  have hoccurs : ∀ key value, (key, value) ∈ trace →
      key ∉ value.vars := by
    intro key value hmem
    exact unificationEliminationTrace_key_not_mem_value_vars _ _
      key value (by simpa [trace] using hmem)
  obtain ⟨key, origin, horigin, horiginNonvar, _hsame, hreach⟩ :=
    eliminationTraceValuation_nonvar_origin trace htriangular hoccurs
      start (by simpa [trace] using hnonvar)
  have hresult : (key, origin) ∈ result :=
    (wholeBindingReconciliation_result_mem_iff_eliminationTrace
      hreconcile).mpr (by simpa [trace] using horigin)
  have hstored : Metta.BindingRel.val key origin ∈
      Metta.Bindings.rebuildFromReconciliation
        candidate source extra result :=
    val_mem_rebuildFromReconciliation_iff.mpr
      ⟨hresult, horiginNonvar⟩
  have hclass : key ∈ Metta.Bindings.eqClass
      (Metta.Bindings.rebuildFromReconciliation
        candidate source extra result) start :=
    eliminationTraceReachable_mem_rebuildEqClass hreconcile
      (by simpa [trace] using hreach)
  obtain ⟨stored, hlookup⟩ := exists_lookupVal_of_val_mem hstored
  have hstoredValue : stored ∈ Metta.Bindings.classValues
      (Metta.Bindings.rebuildFromReconciliation
        candidate source extra result) start := by
    unfold Metta.Bindings.classValues
    apply List.mem_filterMap.mpr
    exact ⟨key, mem_leaEqClassOrdered_iff.mpr hclass, hlookup⟩
  cases hvalues : Metta.Bindings.classValues
      (Metta.Bindings.rebuildFromReconciliation
        candidate source extra result) start with
  | nil => simp [hvalues] at hstoredValue
  | cons first tail =>
    have hfirstMem : first ∈ Metta.Bindings.classValues
        (Metta.Bindings.rebuildFromReconciliation
          candidate source extra result) start := by
      rw [hvalues]
      simp
    have hassignmentsNonvariable : LeaAssignmentsNonVariable
        (Metta.Bindings.rebuildFromReconciliation
          candidate source extra result) := by
      intro storedKey target hmem
      exact (val_mem_rebuildFromReconciliation_iff.mp hmem).2 target rfl
    have hfirstNonvar : ∀ target, first ≠ .var target :=
      leaClassValue_nonvariable hassignmentsNonvariable hfirstMem
    have hsigma := leaBindingSatisfied_classValue hsatisfied hfirstMem
    exact ⟨first, hfirstNonvar, by simpa [trace] using hsigma.symm,
      hfirstUnfold start first tail hvalues hfirstNonvar⟩

/-- A loop-free successful reconciliation rebuild is satisfied by its own
canonical class resolver whenever the elimination-trace valuation satisfies
that rebuild. -/
private theorem reconciliationRebuild_canonical_satisfied
    {candidate source : Metta.Bindings}
    {extra : List (Metta.Atom × Metta.Atom)} {result : Metta.Subst}
    (hreconcile : wholeBindingReconciliation source extra = some result)
    (hloop : (Metta.Bindings.rebuildFromReconciliation
      candidate source extra result).hasLoop = false)
    (htraceSatisfied :
      let trace := unificationEliminationTrace
        (Metta.Bindings.equationFuel
          (Metta.Bindings.equations source ++ extra))
        (Metta.Bindings.equations source ++ extra)
      LeaBindingSatisfied (eliminationTraceValuation trace)
        (Metta.Bindings.rebuildFromReconciliation
          candidate source extra result)) :
    LeaBindingSatisfied
      (leaClassSolution
        (Metta.Bindings.rebuildFromReconciliation
          candidate source extra result))
      (Metta.Bindings.rebuildFromReconciliation
        candidate source extra result) := by
  let trace := unificationEliminationTrace
    (Metta.Bindings.equationFuel
      (Metta.Bindings.equations source ++ extra))
    (Metta.Bindings.equations source ++ extra)
  let out := Metta.Bindings.rebuildFromReconciliation
    candidate source extra result
  have hsigma : LeaBindingSatisfied
      (eliminationTraceValuation trace) out := by
    simpa only [trace, out] using htraceSatisfied
  have hvv : ∀ start finish,
      eliminationTraceValuation trace start = .var finish →
        leaClassSolution out start = leaClassSolution out finish := by
    simpa only [trace, out] using
      reconciliationTraceValuation_var_classSolution_eq hreconcile hloop
  have hpick : ∀ start,
      (∀ finish, eliminationTraceValuation trace start ≠ .var finish) →
      ∃ value, (∀ finish, value ≠ Metta.Atom.var finish) ∧
        applyClassSolution (eliminationTraceValuation trace) value =
          eliminationTraceValuation trace start ∧
        leaClassSolution out start =
          applyClassSolution (leaClassSolution out) value := by
    simpa only [trace, out] using
      reconciliationTraceValuation_nonvar_pick hreconcile hsigma
        (fun start first tail hvalues hnonvar =>
          leaClassSolution_eq_apply_firstClassValue hloop hvalues hnonvar)
  have htransfer := sigma_canonical_transfer
    (eliminationTraceValuation trace) (leaClassSolution out) hvv hpick
  apply leaClassSolution_satisfied_of_values hloop
  intro key value hvalue
  have hsigmaEquation := hsigma.1 key value hvalue
  have hcanonical := htransfer (.var key) value (by
    simpa only [applyClassSolution] using hsigmaEquation)
  simpa only [applyClassSolution] using hcanonical

/-- Reversal changes only the presentation order of a finite constraint
theory. -/
private theorem mettaConstraintsSatisfied_reverse_iff
    (valuation : String → Metta.Atom)
    (constraints : List (String × Metta.Atom)) :
    MettaConstraintsSatisfied valuation constraints.reverse ↔
      MettaConstraintsSatisfied valuation constraints := by
  unfold MettaConstraintsSatisfied
  simp

/-- Every concrete model absorbs the recursively constructed valuation of a
constraint trace.  This factorization statement is independent of how the
trace was produced. -/
private theorem apply_eliminationTraceValuation_eq_of_satisfied
    {specific : String → Metta.Atom}
    {trace : List (String × Metta.Atom)}
    (hsatisfied : MettaConstraintsSatisfied specific trace) :
    ∀ name,
      applyClassSolution specific (eliminationTraceValuation trace name) =
        specific name := by
  induction trace with
  | nil =>
      intro name
      simp [eliminationTraceValuation, applyClassSolution]
  | cons binding trace ih =>
      rcases binding with ⟨key, value⟩
      have htail : MettaConstraintsSatisfied specific trace := by
        intro constraint hconstraint
        exact hsatisfied constraint (by simp [hconstraint])
      have hfactorTail := ih htail
      intro name
      by_cases hname : name = key
      · subst name
        have hhead := hsatisfied (key, value) (by simp)
        simp only [eliminationTraceValuation, Function.update_self]
        rw [HumanMatchModelTheory.applyClassSolution_comp]
        have hfunctions :
            (fun dependency =>
              applyClassSolution specific
                (eliminationTraceValuation trace dependency)) = specific :=
          funext hfactorTail
        rw [hfunctions]
        exact hhead.symm
      · simp [eliminationTraceValuation, hname, hfactorTail]

/-- Whenever the trace valuation satisfies its own constraints, it is their
principal model. -/
private theorem eliminationTraceValuation_principal
    (trace : List (String × Metta.Atom))
    (hsatisfied : MettaConstraintsSatisfied
      (eliminationTraceValuation trace) trace) :
    PrincipalModel
      (fun valuation => MettaConstraintsSatisfied valuation trace)
      (eliminationTraceValuation trace) := by
  refine ⟨hsatisfied, ?_⟩
  intro specific hspecific
  refine ⟨specific, fun name => ?_⟩
  exact (apply_eliminationTraceValuation_eq_of_satisfied
    hspecific name).symm

/-- A successful whole-binding reconciliation returns a constraint theory
with an explicit principal model.  Only the already-proved triangular trace
interface is used here. -/
private theorem wholeBindingReconciliation_result_hasPrincipal
    {source : Metta.Bindings}
    {extra : List (Metta.Atom × Metta.Atom)}
    {result : Metta.Subst}
    (hreconcile : wholeBindingReconciliation source extra = some result) :
    HasPrincipalModel
      (fun valuation => MettaConstraintsSatisfied valuation result) := by
  let trace := unificationEliminationTrace
    (Metta.Bindings.equationFuel
      (Metta.Bindings.equations source ++ extra))
    (Metta.Bindings.equations source ++ extra)
  let general := eliminationTraceValuation trace
  have htrace : MettaConstraintsSatisfied general trace :=
    eliminationTraceValuation_satisfies trace
      (by
        simpa [trace] using
          wholeBindingReconciliation_eliminationTrace_triangular hreconcile)
      (by
        intro key value hmem
        exact unificationEliminationTrace_key_not_mem_value_vars _ _
          key value (by simpa [trace] using hmem))
  have hprincipal := eliminationTraceValuation_principal trace htrace
  have hresult : result = trace.reverse := by
    simpa [trace] using
      wholeBindingReconciliation_result_eq_eliminationTrace_reverse hreconcile
  refine ⟨general, ?_, ?_⟩
  · rw [hresult]
    exact (mettaConstraintsSatisfied_reverse_iff general trace).mpr htrace
  · intro specific hspecific
    apply hprincipal.2 specific
    apply (mettaConstraintsSatisfied_reverse_iff specific trace).mp
    simpa [hresult] using hspecific

/-- The principal result model transports across the exact reconciliation
solution theorem to the conjunction of the source binding theory and the new
equations. -/
private theorem wholeBindingReconciliation_input_hasPrincipal
    {source : Metta.Bindings}
    {extra : List (Metta.Atom × Metta.Atom)}
    {result : Metta.Subst}
    (hsourceNoFloat : LeaBindingsNoFloat source)
    (hextraNoFloat : ∀ equation ∈ extra,
      MettaAtomNoFloat equation.1 ∧ MettaAtomNoFloat equation.2)
    (hreconcile : wholeBindingReconciliation source extra = some result) :
    HasPrincipalModel (fun valuation =>
      LeaBindingSatisfied valuation source ∧
        MettaEquationsSatisfied valuation extra) := by
  obtain ⟨general, hgeneralResult, hprincipalResult⟩ :=
    wholeBindingReconciliation_result_hasPrincipal hreconcile
  refine ⟨general, ?_, ?_⟩
  · exact (wholeBindingReconciliation_solution_iff general
      hsourceNoFloat hextraNoFloat hreconcile).mp hgeneralResult
  · intro specific hspecific
    apply hprincipalResult specific
    exact (wholeBindingReconciliation_solution_iff specific
      hsourceNoFloat hextraNoFloat hreconcile).mpr hspecific

/-- A successful whole-binding reconciliation carries a concrete model of
its normalized substitution result.  This is the model extracted from the
triangular elimination trace above, not an appeal to another matcher. -/
private theorem wholeBindingReconciliation_result_satisfiable
    {source : Metta.Bindings}
    {extra : List (Metta.Atom × Metta.Atom)}
    {result : Metta.Subst}
    (hreconcile : wholeBindingReconciliation source extra = some result) :
    ∃ valuation : String → Metta.Atom,
      MettaConstraintsSatisfied valuation result := by
  obtain ⟨valuation, hsatisfied, _hprincipal⟩ :=
    wholeBindingReconciliation_result_hasPrincipal hreconcile
  exact ⟨valuation, hsatisfied⟩

/-- The concrete value-conflict rebuild emitted by `addVarBinding` is
satisfiable.  The successful reconciliation model is transported through the
exact normalized-rebuild and alias-restoration interfaces. -/
private theorem valueReconciliationRebuild_satisfiable
    {source : Metta.Bindings} {key : String} {value : Metta.Atom}
    {result : Metta.Subst}
    (hsourceNoFloat : LeaBindingsNoFloat source)
    (hvalueNoFloat : MettaAtomNoFloat value)
    (hreconcile : wholeBindingReconciliation source
      [(.var key, value)] = some result) :
    ∃ valuation : String → Metta.Atom,
      LeaBindingSatisfied valuation
        (Metta.Bindings.rebuildFromReconciliation source source
          [(.var key, value)] result) := by
  obtain ⟨valuation, hresult⟩ :=
    wholeBindingReconciliation_result_satisfiable hreconcile
  have hextraNoFloat : ∀ equation ∈ [(.var key, value)],
      MettaAtomNoFloat equation.1 ∧ MettaAtomNoFloat equation.2 := by
    intro equation hmem
    simp only [List.mem_singleton] at hmem
    subst equation
    exact ⟨by simp [MettaAtomNoFloat], hvalueNoFloat⟩
  have hinput : LeaBindingSatisfied valuation source ∧
      MettaEquationsSatisfied valuation [(.var key, value)] :=
    (wholeBindingReconciliation_solution_iff valuation
      hsourceNoFloat hextraNoFloat hreconcile).mp hresult
  refine ⟨valuation,
    (rebuildFromReconciliation_solution_iff valuation
      hsourceNoFloat hextraNoFloat hreconcile).mpr ?_⟩
  exact (rebuildBindingsFromUnifier_solution_iff valuation
    hsourceNoFloat hextraNoFloat hreconcile).mpr hinput

/-- The equality-conflict rebuild has the same concrete-model property.  Its
candidate differs only by the explicitly inserted equality skeleton. -/
private theorem equalityReconciliationRebuild_satisfiable
    {source : Metta.Bindings} {left right : String}
    {result : Metta.Subst}
    (hsourceNoFloat : LeaBindingsNoFloat source)
    (hreconcile : wholeBindingReconciliation source
      [(.var left, .var right)] = some result) :
    ∃ valuation : String → Metta.Atom,
      LeaBindingSatisfied valuation
        (Metta.Bindings.rebuildFromReconciliation
          (Metta.Bindings.addEqRaw source left right) source
          [(.var left, .var right)] result) := by
  obtain ⟨valuation, hresult⟩ :=
    wholeBindingReconciliation_result_satisfiable hreconcile
  have hextraNoFloat : ∀ equation ∈ [(.var left, .var right)],
      MettaAtomNoFloat equation.1 ∧ MettaAtomNoFloat equation.2 := by
    intro equation hmem
    simp only [List.mem_singleton] at hmem
    subst equation
    simp [MettaAtomNoFloat]
  have hinput : LeaBindingSatisfied valuation source ∧
      valuation left = valuation right := by
    simpa [MettaEquationsSatisfied, MettaEquationSatisfied,
      applyClassSolution] using
        (wholeBindingReconciliation_solution_iff valuation
          hsourceNoFloat hextraNoFloat hreconcile).mp hresult
  refine ⟨valuation,
    (rebuildFromReconciliation_solution_iff valuation
      hsourceNoFloat hextraNoFloat hreconcile).mpr ?_⟩
  exact (rebuildBindingsFromUnifier_addEq_solution_iff valuation
    hsourceNoFloat hreconcile).mpr hinput

/-- A successful value insertion has a principal output theory whenever the
same source-plus-value equation has a successful whole-binding
reconciliation.  The insertion's concrete output presentation is eliminated
through its exact solution theorem. -/
private theorem leaAddVarBinding_hasPrincipal_of_reconciliation
    {source out : Metta.Bindings}
    {key : String} {value : Metta.Atom} {result : Metta.Subst}
    (hsourceNoFloat : LeaBindingsNoFloat source)
    (hvalueNoFloat : MettaAtomNoFloat value)
    (hout : out ∈ Metta.Bindings.addVarBinding source key value)
    (hreconcile : wholeBindingReconciliation source
      [(.var key, value)] = some result) :
    HasPrincipalModel
      (fun valuation => LeaBindingSatisfied valuation out) := by
  apply hasPrincipalModel_congr
    (left := fun valuation =>
      LeaBindingSatisfied valuation source ∧
        MettaEquationsSatisfied valuation [(.var key, value)])
  · intro valuation
    rw [leaAddVarBinding_solution_iff valuation
      hsourceNoFloat hvalueNoFloat hout]
    simp [MettaEquationsSatisfied, MettaEquationSatisfied,
      applyClassSolution]
  · exact wholeBindingReconciliation_input_hasPrincipal
      hsourceNoFloat
      (by
        intro equation hequation
        simp only [List.mem_singleton] at hequation
        subst equation
        exact ⟨by simp [MettaAtomNoFloat], hvalueNoFloat⟩)
      hreconcile

/-- The concrete elimination-trace valuation satisfies the normalized result
of every successful reconciliation. -/
private theorem wholeBindingReconciliation_traceValuation_satisfied
    {source : Metta.Bindings}
    {extra : List (Metta.Atom × Metta.Atom)} {result : Metta.Subst}
    (hreconcile : wholeBindingReconciliation source extra = some result) :
    let trace := unificationEliminationTrace
      (Metta.Bindings.equationFuel
        (Metta.Bindings.equations source ++ extra))
      (Metta.Bindings.equations source ++ extra)
    MettaConstraintsSatisfied (eliminationTraceValuation trace) result := by
  dsimp only
  let trace := unificationEliminationTrace
    (Metta.Bindings.equationFuel
      (Metta.Bindings.equations source ++ extra))
    (Metta.Bindings.equations source ++ extra)
  have htrace : MettaConstraintsSatisfied
      (eliminationTraceValuation trace) trace :=
    eliminationTraceValuation_satisfies trace
      (by
        simpa [trace] using
          wholeBindingReconciliation_eliminationTrace_triangular hreconcile)
      (by
        intro key value hmem
        exact unificationEliminationTrace_key_not_mem_value_vars _ _
          key value (by simpa [trace] using hmem))
  rw [wholeBindingReconciliation_result_eq_eliminationTrace_reverse
    hreconcile]
  exact (mettaConstraintsSatisfied_reverse_iff
    (eliminationTraceValuation trace) trace).mpr htrace

/-- The same trace valuation satisfies the concrete value-conflict rebuild. -/
private theorem valueReconciliationRebuild_traceValuation_satisfied
    {source : Metta.Bindings} {key : String} {value : Metta.Atom}
    {result : Metta.Subst}
    (hsourceNoFloat : LeaBindingsNoFloat source)
    (hvalueNoFloat : MettaAtomNoFloat value)
    (hreconcile : wholeBindingReconciliation source
      [(.var key, value)] = some result) :
    let trace := unificationEliminationTrace
      (Metta.Bindings.equationFuel
        (Metta.Bindings.equations source ++ [(.var key, value)]))
      (Metta.Bindings.equations source ++ [(.var key, value)])
    LeaBindingSatisfied (eliminationTraceValuation trace)
      (Metta.Bindings.rebuildFromReconciliation source source
        [(.var key, value)] result) := by
  dsimp only
  let trace := unificationEliminationTrace
    (Metta.Bindings.equationFuel
      (Metta.Bindings.equations source ++ [(.var key, value)]))
    (Metta.Bindings.equations source ++ [(.var key, value)])
  have hresult : MettaConstraintsSatisfied
      (eliminationTraceValuation trace) result := by
    simpa only [trace] using
      wholeBindingReconciliation_traceValuation_satisfied hreconcile
  have hextraNoFloat : ∀ equation ∈ [(.var key, value)],
      MettaAtomNoFloat equation.1 ∧ MettaAtomNoFloat equation.2 := by
    intro equation hmem
    simp only [List.mem_singleton] at hmem
    subst equation
    exact ⟨by simp [MettaAtomNoFloat], hvalueNoFloat⟩
  have hinput : LeaBindingSatisfied
        (eliminationTraceValuation trace) source ∧
      MettaEquationsSatisfied (eliminationTraceValuation trace)
        [(.var key, value)] :=
    (wholeBindingReconciliation_solution_iff
      (eliminationTraceValuation trace) hsourceNoFloat
      hextraNoFloat hreconcile).mp hresult
  apply (rebuildFromReconciliation_solution_iff
    (eliminationTraceValuation trace) hsourceNoFloat
      hextraNoFloat hreconcile).mpr
  exact (rebuildBindingsFromUnifier_solution_iff
    (eliminationTraceValuation trace) hsourceNoFloat
      hextraNoFloat hreconcile).mpr hinput

/-- The trace valuation also satisfies the equality-conflict candidate
skeleton and its repaired alias-restoring rebuild. -/
private theorem equalityReconciliationRebuild_traceValuation_satisfied
    {source : Metta.Bindings} {left right : String}
    {result : Metta.Subst}
    (hsourceNoFloat : LeaBindingsNoFloat source)
    (hreconcile : wholeBindingReconciliation source
      [(.var left, .var right)] = some result) :
    let trace := unificationEliminationTrace
      (Metta.Bindings.equationFuel
        (Metta.Bindings.equations source ++ [(.var left, .var right)]))
      (Metta.Bindings.equations source ++ [(.var left, .var right)])
    LeaBindingSatisfied (eliminationTraceValuation trace)
      (Metta.Bindings.rebuildFromReconciliation
        (Metta.Bindings.addEqRaw source left right) source
        [(.var left, .var right)] result) := by
  dsimp only
  let trace := unificationEliminationTrace
    (Metta.Bindings.equationFuel
      (Metta.Bindings.equations source ++ [(.var left, .var right)]))
    (Metta.Bindings.equations source ++ [(.var left, .var right)])
  have hresult : MettaConstraintsSatisfied
      (eliminationTraceValuation trace) result := by
    simpa only [trace] using
      wholeBindingReconciliation_traceValuation_satisfied hreconcile
  have hextraNoFloat : ∀ equation ∈ [(.var left, .var right)],
      MettaAtomNoFloat equation.1 ∧ MettaAtomNoFloat equation.2 := by
    intro equation hmem
    simp only [List.mem_singleton] at hmem
    subst equation
    simp [MettaAtomNoFloat]
  have hinput : LeaBindingSatisfied
        (eliminationTraceValuation trace) source ∧
      eliminationTraceValuation trace left =
        eliminationTraceValuation trace right := by
    simpa [MettaEquationsSatisfied, MettaEquationSatisfied,
      applyClassSolution] using
        (wholeBindingReconciliation_solution_iff
          (eliminationTraceValuation trace) hsourceNoFloat
          hextraNoFloat hreconcile).mp hresult
  apply (rebuildFromReconciliation_solution_iff
    (eliminationTraceValuation trace) hsourceNoFloat
      hextraNoFloat hreconcile).mpr
  exact (rebuildBindingsFromUnifier_addEq_solution_iff
    (eliminationTraceValuation trace) hsourceNoFloat hreconcile).mpr hinput

private theorem rebuildFromReconciliation_assignmentsNonVariable
    {candidate source : Metta.Bindings}
    {extra : List (Metta.Atom × Metta.Atom)} {result : Metta.Subst} :
    LeaAssignmentsNonVariable
      (Metta.Bindings.rebuildFromReconciliation
        candidate source extra result) := by
  intro key target hvalue
  exact (val_mem_rebuildFromReconciliation_iff.mp hvalue).2 target rfl

/-- A retained, loop-free value-conflict rebuild is canonically principal. -/
private theorem valueReconciliationRebuild_canonicallyPrincipal
    {source : Metta.Bindings} {key : String} {value : Metta.Atom}
    {result : Metta.Subst}
    (hsourceNoFloat : LeaBindingsNoFloat source)
    (hvalueNoFloat : MettaAtomNoFloat value)
    (hreconcile : wholeBindingReconciliation source
      [(.var key, value)] = some result)
    (hloop : (Metta.Bindings.rebuildFromReconciliation source source
      [(.var key, value)] result).hasLoop = false) :
    CanonicallyPrincipal
      (Metta.Bindings.rebuildFromReconciliation source source
        [(.var key, value)] result) := by
  apply canonicallyPrincipal_of_canonical_satisfied
  · exact reconciliationRebuild_canonical_satisfied hreconcile hloop
      (valueReconciliationRebuild_traceValuation_satisfied
        hsourceNoFloat hvalueNoFloat hreconcile)
  · exact rebuildFromReconciliation_assignmentsNonVariable

/-- A retained, loop-free equality-conflict rebuild is canonically
principal as well. -/
private theorem equalityReconciliationRebuild_canonicallyPrincipal
    {source : Metta.Bindings} {left right : String}
    {result : Metta.Subst}
    (hsourceNoFloat : LeaBindingsNoFloat source)
    (hreconcile : wholeBindingReconciliation source
      [(.var left, .var right)] = some result)
    (hloop : (Metta.Bindings.rebuildFromReconciliation
      (Metta.Bindings.addEqRaw source left right) source
      [(.var left, .var right)] result).hasLoop = false) :
    CanonicallyPrincipal
      (Metta.Bindings.rebuildFromReconciliation
        (Metta.Bindings.addEqRaw source left right) source
        [(.var left, .var right)] result) := by
  apply canonicallyPrincipal_of_canonical_satisfied
  · exact reconciliationRebuild_canonical_satisfied hreconcile hloop
      (equalityReconciliationRebuild_traceValuation_satisfied
        hsourceNoFloat hreconcile)
  · exact rebuildFromReconciliation_assignmentsNonVariable

/-! ### Canonical preservation under fresh raw extension -/

private theorem lookupVal_removeVal_of_ne
    (bindings : Metta.Bindings) {removed key : String}
    (hne : key ≠ removed) :
    Metta.Bindings.lookupVal
        (Metta.Bindings.removeVal bindings removed) key =
      Metta.Bindings.lookupVal bindings key := by
  induction bindings with
  | nil => rfl
  | cons relation rest ih =>
      cases relation with
      | val stored value =>
          by_cases hstored : stored = removed
          · subst stored
            simpa [Metta.Bindings.removeVal, Metta.Bindings.lookupVal,
              hne] using ih
          · by_cases hkey : key = stored
            · subst stored
              simp [Metta.Bindings.removeVal, Metta.Bindings.lookupVal,
                hstored]
            · simpa [Metta.Bindings.removeVal,
                Metta.Bindings.lookupVal, hstored, hkey] using ih
      | eq left right =>
          simpa [Metta.Bindings.removeVal,
            Metta.Bindings.lookupVal] using ih

@[simp] private theorem lookupVal_addValRaw_of_ne
    (bindings : Metta.Bindings) {inserted key : String}
    (value : Metta.Atom) (hne : key ≠ inserted) :
    Metta.Bindings.lookupVal
        (Metta.Bindings.addValRaw bindings inserted value) key =
      Metta.Bindings.lookupVal bindings key := by
  simp [Metta.Bindings.addValRaw, Metta.Bindings.lookupVal, hne,
    lookupVal_removeVal_of_ne bindings hne]

private theorem eqVarsInOrder_removeVal
    (bindings : Metta.Bindings) (removed : String) :
    Metta.Bindings.eqVarsInOrder
        (Metta.Bindings.removeVal bindings removed) =
      Metta.Bindings.eqVarsInOrder bindings := by
  let step : List String → Metta.BindingRel → List String :=
    fun acc relation => match relation with
      | Metta.BindingRel.eq left right =>
          let acc := if acc.contains right then acc else acc ++ [right]
          if acc.contains left then acc else acc ++ [left]
      | _ => acc
  have hfold : ∀ (rest : Metta.Bindings) (acc : List String),
      (Metta.Bindings.removeVal rest removed).reverse.foldl step acc =
        rest.reverse.foldl step acc := by
    intro rest
    induction rest with
    | nil => intro acc; rfl
    | cons relation tail ih =>
        intro acc
        cases relation with
        | val key value =>
            by_cases hkey : key = removed
            · have hremove : Metta.Bindings.removeVal
                  (Metta.BindingRel.val key value :: tail) removed =
                  Metta.Bindings.removeVal tail removed := by
                simp [Metta.Bindings.removeVal, hkey]
              simp only [hremove, List.reverse_cons,
                List.foldl_append, ih]
              rfl
            · have hremove : Metta.Bindings.removeVal
                  (Metta.BindingRel.val key value :: tail) removed =
                  Metta.BindingRel.val key value ::
                    Metta.Bindings.removeVal tail removed := by
                simp [Metta.Bindings.removeVal, hkey]
              simp only [hremove, List.reverse_cons,
                List.foldl_append, ih]
        | eq left right =>
            have hremove : Metta.Bindings.removeVal
                (Metta.BindingRel.eq left right :: tail) removed =
                Metta.BindingRel.eq left right ::
                  Metta.Bindings.removeVal tail removed := by
              simp [Metta.Bindings.removeVal]
            simp only [hremove, List.reverse_cons,
              List.foldl_append, ih]
  change (Metta.Bindings.removeVal bindings removed).reverse.foldl
      step [] = bindings.reverse.foldl step []
  exact hfold bindings []

@[simp] private theorem eqVarsInOrder_addValRaw
    (bindings : Metta.Bindings) (key : String) (value : Metta.Atom) :
    Metta.Bindings.eqVarsInOrder
        (Metta.Bindings.addValRaw bindings key value) =
      Metta.Bindings.eqVarsInOrder bindings := by
  change Metta.Bindings.eqVarsInOrder
      (Metta.BindingRel.val key value ::
        Metta.Bindings.removeVal bindings key) = _
  rw [show Metta.Bindings.eqVarsInOrder
      (Metta.BindingRel.val key value ::
        Metta.Bindings.removeVal bindings key) =
      Metta.Bindings.eqVarsInOrder
        (Metta.Bindings.removeVal bindings key) by
    simp [Metta.Bindings.eqVarsInOrder, List.foldl_append]]
  exact eqVarsInOrder_removeVal bindings key

private theorem eqClassOrdered_addValRaw
    (bindings : Metta.Bindings) (inserted : String)
    (value : Metta.Atom) (start : String) :
    Metta.Bindings.eqClassOrdered
        (Metta.Bindings.addValRaw bindings inserted value) start =
      Metta.Bindings.eqClassOrdered bindings start := by
  unfold Metta.Bindings.eqClassOrdered
  rw [eqVarsInOrder_addValRaw]
  have hfilter :
      (Metta.Bindings.eqVarsInOrder bindings).filter
          (fun finish =>
            (Metta.Bindings.eqClass
              (Metta.Bindings.addValRaw bindings inserted value) start).contains
                finish) =
        (Metta.Bindings.eqVarsInOrder bindings).filter
          (fun finish =>
            (Metta.Bindings.eqClass bindings start).contains finish) := by
    apply List.filter_congr
    intro finish _hfinish
    apply Bool.eq_iff_iff.mpr
    rw [List.contains_iff_mem, List.contains_iff_mem]
    rw [mem_leaEqClass_iff_reachable, mem_leaEqClass_iff_reachable]
    simp [Metta.Bindings.addValRaw, leaEqualityEdges,
      leaEqualityEdges_removeVal]
  rw [hfilter]

private theorem mem_eqClass_addValRaw_iff
    {bindings : Metta.Bindings} {inserted : String}
    {value : Metta.Atom} {start finish : String} :
    finish ∈ Metta.Bindings.eqClass
        (Metta.Bindings.addValRaw bindings inserted value) start ↔
      finish ∈ Metta.Bindings.eqClass bindings start := by
  rw [mem_leaEqClass_iff_reachable, mem_leaEqClass_iff_reachable]
  simp [Metta.Bindings.addValRaw, leaEqualityEdges,
    leaEqualityEdges_removeVal]

private theorem eqRepresentative_mem_eqClass
    (bindings : Metta.Bindings) (start : String) :
    Metta.Bindings.eqRepresentative bindings start ∈
      Metta.Bindings.eqClass bindings start := by
  apply mem_leaEqClassOrdered_iff.mp
  have hstart : start ∈
      Metta.Bindings.eqClassOrdered bindings start :=
    mem_leaEqClassOrdered_iff.mpr (by
      rw [mem_leaEqClass_iff_reachable])
  unfold Metta.Bindings.eqRepresentative
  cases hclass : Metta.Bindings.eqClassOrdered bindings start with
  | nil => simp [hclass] at hstart
  | cons first rest => simp

private theorem leaClassSolution_eq_representative_of_classValues_nil
    {bindings : Metta.Bindings} {start : String}
    (hvalues : Metta.Bindings.classValues bindings start = []) :
    leaClassSolution bindings start =
      .var (Metta.Bindings.eqRepresentative bindings start) := by
  unfold leaClassSolution Metta.Bindings.resolve
  cases hguard :
      ((Metta.Bindings.eqClassOrdered bindings start == [start]) &&
        (Metta.Bindings.classValues bindings start).isEmpty) with
  | true =>
      have hparts := Bool.and_eq_true_iff.mp hguard
      have hclass : Metta.Bindings.eqClassOrdered bindings start = [start] := by
        simpa using hparts.1
      have hrepresentative :
          Metta.Bindings.eqRepresentative bindings start = start := by
        simp [Metta.Bindings.eqRepresentative, hclass]
      simp [hguard, hrepresentative]
  | false =>
      have hclass :
          Metta.Bindings.eqClassOrdered bindings start ≠ [start] := by
        intro heq
        have :
            ((Metta.Bindings.eqClassOrdered bindings start == [start]) &&
              (Metta.Bindings.classValues bindings start).isEmpty) = true := by
          simp [heq, hvalues]
        exact Bool.false_ne_true (hguard.symm.trans this)
      cases hfuel : Metta.Bindings.resolutionFuel bindings (.var start) with
      | zero =>
          simp [Metta.Bindings.resolutionFuel, Metta.Atom.size] at hfuel
      | succ fuel =>
          simp [Metta.Bindings.resolveAtomAux, hvalues, hclass]

/-- A normalized loop-free canonical resolver can return a bare variable only
from the same explicit equality class. -/
private theorem leaClassSolution_eq_var_mem_eqClass
    {bindings : Metta.Bindings} {start finish : String}
    (hloop : bindings.hasLoop = false)
    (hnonvariable : LeaAssignmentsNonVariable bindings)
    (hresult : leaClassSolution bindings start = .var finish) :
    finish ∈ Metta.Bindings.eqClass bindings start := by
  cases hvalues : Metta.Bindings.classValues bindings start with
  | nil =>
      have hrepresentative :=
        leaClassSolution_eq_representative_of_classValues_nil hvalues
      rw [hresult] at hrepresentative
      simp only [Metta.Atom.var.injEq] at hrepresentative
      subst finish
      exact eqRepresentative_mem_eqClass bindings start
  | cons first tail =>
      have hfirstMem : first ∈
          Metta.Bindings.classValues bindings start := by
        rw [hvalues]
        simp
      have hfirstNonvar : ∀ target, first ≠ .var target :=
        leaClassValue_nonvariable hnonvariable hfirstMem
      have hunfold := leaClassSolution_eq_apply_firstClassValue
        hloop hvalues hfirstNonvar
      rw [hresult] at hunfold
      cases first with
      | var target => exact (hfirstNonvar target rfl).elim
      | sym symbol => simp [applyClassSolution] at hunfold
      | gnd ground => simp [applyClassSolution] at hunfold
      | expr atoms => simp [applyClassSolution] at hunfold

private theorem classValues_eq_of_mem_eqClass
    {bindings : Metta.Bindings} {left right : String}
    (hmem : right ∈ Metta.Bindings.eqClass bindings left) :
    Metta.Bindings.classValues bindings left =
      Metta.Bindings.classValues bindings right := by
  unfold Metta.Bindings.classValues
  rw [leaEqClassOrdered_eq_of_mem_eqClass hmem]

private theorem classValues_addValRaw_of_not_mem_eqClass
    {bindings : Metta.Bindings} {inserted start : String}
    (value : Metta.Atom)
    (hnotmem : inserted ∉ Metta.Bindings.eqClass bindings start) :
    Metta.Bindings.classValues
        (Metta.Bindings.addValRaw bindings inserted value) start =
      Metta.Bindings.classValues bindings start := by
  unfold Metta.Bindings.classValues
  rw [eqClassOrdered_addValRaw]
  apply List.filterMap_congr
  intro key hkey
  apply lookupVal_addValRaw_of_ne
  intro heq
  subst key
  exact hnotmem (mem_leaEqClassOrdered_iff.mp hkey)

private theorem inserted_mem_classValues_addValRaw
    (bindings : Metta.Bindings) (inserted : String)
    (value : Metta.Atom) :
    value ∈ Metta.Bindings.classValues
      (Metta.Bindings.addValRaw bindings inserted value) inserted := by
  unfold Metta.Bindings.classValues
  apply List.mem_filterMap.mpr
  refine ⟨inserted, ?_, ?_⟩
  · rw [eqClassOrdered_addValRaw]
    apply mem_leaEqClassOrdered_iff.mpr
    rw [mem_leaEqClass_iff_reachable]
  · exact Metta.Bindings.lookupVal_addValRaw_self bindings inserted value

private theorem classValue_addValRaw_fresh_eq
    {bindings : Metta.Bindings} {inserted : String}
    {value first : Metta.Atom}
    (hsourceValues : Metta.Bindings.classValues bindings inserted = [])
    (hfirst : first ∈ Metta.Bindings.classValues
      (Metta.Bindings.addValRaw bindings inserted value) inserted) :
    first = value := by
  unfold Metta.Bindings.classValues at hsourceValues hfirst
  obtain ⟨storedKey, hstoredClass, hlookup⟩ :=
    List.mem_filterMap.mp hfirst
  rw [eqClassOrdered_addValRaw] at hstoredClass
  by_cases hkey : storedKey = inserted
  · subst storedKey
    rw [Metta.Bindings.lookupVal_addValRaw_self] at hlookup
    exact Option.some.inj hlookup.symm
  · have hsourceNone :
        Metta.Bindings.lookupVal bindings storedKey = none :=
      List.filterMap_eq_nil_iff.mp hsourceValues storedKey hstoredClass
    rw [lookupVal_addValRaw_of_ne bindings value hkey,
      hsourceNone] at hlookup
    contradiction

private theorem freshExtension_sigma_var_agrees
    {bindings : Metta.Bindings} {inserted : String}
    {value : Metta.Atom}
    (hsourceLoop : bindings.hasLoop = false)
    (hsourceNonvariable : LeaAssignmentsNonVariable bindings)
    (houtLoop : (Metta.Bindings.addValRaw bindings inserted value).hasLoop =
      false) :
    ∀ start finish,
      leaClassSolution bindings start = .var finish →
        leaClassSolution
            (Metta.Bindings.addValRaw bindings inserted value) start =
          leaClassSolution
            (Metta.Bindings.addValRaw bindings inserted value) finish := by
  intro start finish hresult
  apply leaClassSolution_eq_of_mem_eqClass houtLoop
  apply mem_eqClass_addValRaw_iff.mpr
  exact leaClassSolution_eq_var_mem_eqClass
    hsourceLoop hsourceNonvariable hresult

private theorem freshExtension_sigma_nonvar_pick
    {bindings : Metta.Bindings} {inserted : String}
    {value : Metta.Atom}
    (hsourceValues : Metta.Bindings.classValues bindings inserted = [])
    (hsourceLoop : bindings.hasLoop = false)
    (hsourceNonvariable : LeaAssignmentsNonVariable bindings)
    (houtLoop : (Metta.Bindings.addValRaw bindings inserted value).hasLoop =
      false) :
    ∀ start, (∀ target,
      leaClassSolution bindings start ≠ .var target) →
      ∃ selected, (∀ target, selected ≠ Metta.Atom.var target) ∧
        applyClassSolution (leaClassSolution bindings) selected =
          leaClassSolution bindings start ∧
        leaClassSolution
            (Metta.Bindings.addValRaw bindings inserted value) start =
          applyClassSolution
            (leaClassSolution
              (Metta.Bindings.addValRaw bindings inserted value)) selected := by
  intro start hnonvar
  cases hvalues : Metta.Bindings.classValues bindings start with
  | nil =>
      have hrepresentative :=
        leaClassSolution_eq_representative_of_classValues_nil hvalues
      exact (hnonvar _ hrepresentative).elim
  | cons first tail =>
      have hfirstMem : first ∈
          Metta.Bindings.classValues bindings start := by
        rw [hvalues]
        simp
      have hfirstNonvar : ∀ target, first ≠ .var target :=
        leaClassValue_nonvariable hsourceNonvariable hfirstMem
      have hinsertedNotClass :
          inserted ∉ Metta.Bindings.eqClass bindings start := by
        intro hclass
        have hsame := classValues_eq_of_mem_eqClass hclass
        rw [hsourceValues] at hsame
        simp [hvalues] at hsame
      have houtValues : Metta.Bindings.classValues
          (Metta.Bindings.addValRaw bindings inserted value) start =
            first :: tail := by
        rw [classValues_addValRaw_of_not_mem_eqClass value
          hinsertedNotClass]
        exact hvalues
      refine ⟨first, hfirstNonvar, ?_, ?_⟩
      · exact (leaClassSolution_eq_apply_firstClassValue
          hsourceLoop hvalues hfirstNonvar).symm
      · exact leaClassSolution_eq_apply_firstClassValue
          houtLoop houtValues hfirstNonvar

/-- Fresh non-variable insertion preserves canonical principality whenever
the completed extension passes the repaired loop check. -/
private theorem addValRaw_fresh_canonicallyPrincipal
    {bindings : Metta.Bindings} {inserted : String}
    {value : Metta.Atom}
    (hsource : CanonicallyPrincipal bindings)
    (hsourceNonvariable : LeaAssignmentsNonVariable bindings)
    (hsourceLoop : bindings.hasLoop = false)
    (hsourceValues : Metta.Bindings.classValues bindings inserted = [])
    (hvalueNonvar : ∀ target, value ≠ .var target)
    (houtLoop : (Metta.Bindings.addValRaw bindings inserted value).hasLoop =
      false) :
    CanonicallyPrincipal
      (Metta.Bindings.addValRaw bindings inserted value) := by
  let sigma := leaClassSolution bindings
  let chi := leaClassSolution
    (Metta.Bindings.addValRaw bindings inserted value)
  have htransfer : ∀ left right,
      applyClassSolution sigma left = applyClassSolution sigma right →
        applyClassSolution chi left = applyClassSolution chi right :=
    sigma_canonical_transfer sigma chi
      (freshExtension_sigma_var_agrees hsourceLoop
        hsourceNonvariable houtLoop)
      (freshExtension_sigma_nonvar_pick hsourceValues hsourceLoop
        hsourceNonvariable houtLoop)
  have hsourceSatisfied : LeaBindingSatisfied chi bindings := by
    constructor
    · intro key stored hstored
      have hold := hsource.1.1 key stored hstored
      have hnew := htransfer (.var key) stored (by
        simpa [sigma, applyClassSolution] using hold)
      simpa [chi, applyClassSolution] using hnew
    · intro left right hedge
      have hold := hsource.1.2 left right hedge
      have hnew := htransfer (.var left) (.var right) (by
        simpa [sigma, applyClassSolution] using hold)
      simpa [chi, applyClassSolution] using hnew
  have hnewEquation : chi inserted = applyClassSolution chi value := by
    have hvalueMem := inserted_mem_classValues_addValRaw
      bindings inserted value
    cases houtValues : Metta.Bindings.classValues
        (Metta.Bindings.addValRaw bindings inserted value) inserted with
    | nil => simp [houtValues] at hvalueMem
    | cons first tail =>
        have hfirstMem : first ∈ Metta.Bindings.classValues
            (Metta.Bindings.addValRaw bindings inserted value) inserted := by
          rw [houtValues]
          simp
        have hfirstEq : first = value :=
          classValue_addValRaw_fresh_eq hsourceValues hfirstMem
        subst first
        exact leaClassSolution_eq_apply_firstClassValue
          houtLoop houtValues hvalueNonvar
  apply canonicallyPrincipal_of_canonical_satisfied
  · have hlookup : Metta.Bindings.lookupVal bindings inserted = none := by
      unfold Metta.Bindings.classValues at hsourceValues
      apply List.filterMap_eq_nil_iff.mp hsourceValues inserted
      apply mem_leaEqClassOrdered_iff.mpr
      rw [mem_leaEqClass_iff_reachable]
    exact (leaBindingSatisfied_addValRaw_fresh_iff
      chi bindings inserted value hlookup).mpr
        ⟨hsourceSatisfied, hnewEquation⟩
  · exact hsourceNonvariable.addValRaw hvalueNonvar

/-! ### Canonical preservation under a no-substitution alias join -/

@[simp] private theorem lookupVal_addEqRaw
    (bindings : Metta.Bindings) (left right key : String) :
    Metta.Bindings.lookupVal
        (Metta.Bindings.addEqRaw bindings left right) key =
      Metta.Bindings.lookupVal bindings key := by
  by_cases heq : left = right
  · subst right
    simp [Metta.Bindings.addEqRaw]
  · simp [Metta.Bindings.addEqRaw, heq, Metta.Bindings.lookupVal]

private theorem mem_eqClass_addEqRaw_of_mem
    {bindings : Metta.Bindings} {left right start finish : String}
    (hmem : finish ∈ Metta.Bindings.eqClass bindings start) :
    finish ∈ Metta.Bindings.eqClass
      (Metta.Bindings.addEqRaw bindings left right) start := by
  rw [mem_leaEqClass_iff_reachable] at hmem ⊢
  apply hmem.mono
  intro x y hadj
  rw [EqualityClosure.edgeGraph_adj_iff] at hadj ⊢
  by_cases heq : left = right
  · subst right
    simpa [Metta.Bindings.addEqRaw] using hadj
  · simp only [Metta.Bindings.addEqRaw, beq_iff_eq, heq,
      ↓reduceIte, leaEqualityEdges, List.mem_cons]
    refine ⟨hadj.1, ?_⟩
    rcases hadj.2 with hforward | hreverse
    · exact Or.inl (Or.inr hforward)
    · exact Or.inr (Or.inr hreverse)

private theorem reachable_cons_of_not_reachable_left
    {edges : List (String × String)} {left right start finish : String}
    (hnot : ¬(EqualityClosure.edgeGraph ((left, right) :: edges)).Reachable
      start left)
    (hreach :
      (EqualityClosure.edgeGraph ((left, right) :: edges)).Reachable
        start finish) :
    (EqualityClosure.edgeGraph edges).Reachable start finish := by
  apply hreach.elim
  intro walk
  revert hnot
  induction walk with
  | nil => intro _; exact .rfl
  | @cons start next finish hadj tail ih =>
      intro hnot
      have hnotNext :
          ¬(EqualityClosure.edgeGraph ((left, right) :: edges)).Reachable
            next left := by
        intro hnext
        exact hnot (hadj.reachable.trans hnext)
      have hold : (EqualityClosure.edgeGraph edges).Adj start next := by
        rw [EqualityClosure.edgeGraph_adj_iff] at hadj ⊢
        rcases hadj with ⟨hne, hforward | hreverse⟩
        · rcases List.mem_cons.mp hforward with hnew | hold
          · cases hnew
            exact (hnot .rfl).elim
          · exact ⟨hne, Or.inl hold⟩
        · rcases List.mem_cons.mp hreverse with hnew | hold
          · cases hnew
            exact (hnotNext .rfl).elim
          · exact ⟨hne, Or.inr hold⟩
      exact hold.reachable.trans (ih tail.reachable hnotNext)

private theorem classValue_addEqRaw_of_source
    {bindings : Metta.Bindings} {left right start : String}
    {value : Metta.Atom}
    (hvalue : value ∈ Metta.Bindings.classValues bindings start) :
    value ∈ Metta.Bindings.classValues
      (Metta.Bindings.addEqRaw bindings left right) start := by
  unfold Metta.Bindings.classValues at hvalue ⊢
  obtain ⟨storedKey, hclass, hlookup⟩ := List.mem_filterMap.mp hvalue
  apply List.mem_filterMap.mpr
  refine ⟨storedKey, ?_, ?_⟩
  · apply mem_leaEqClassOrdered_iff.mpr
    exact mem_eqClass_addEqRaw_of_mem
      (mem_leaEqClassOrdered_iff.mp hclass)
  · simpa using hlookup

private theorem classValue_source_of_addEqRaw_of_not_joined
    {bindings : Metta.Bindings} {left right start : String}
    (hne : left ≠ right)
    (hnot : left ∉ Metta.Bindings.eqClass
      (Metta.Bindings.addEqRaw bindings left right) start)
    {value : Metta.Atom}
    (hvalue : value ∈ Metta.Bindings.classValues
      (Metta.Bindings.addEqRaw bindings left right) start) :
    value ∈ Metta.Bindings.classValues bindings start := by
  unfold Metta.Bindings.classValues at hvalue ⊢
  obtain ⟨storedKey, hclass, hlookup⟩ := List.mem_filterMap.mp hvalue
  apply List.mem_filterMap.mpr
  refine ⟨storedKey, ?_, ?_⟩
  · apply mem_leaEqClassOrdered_iff.mpr
    rw [mem_leaEqClass_iff_reachable]
    apply reachable_cons_of_not_reachable_left
    · simpa [mem_leaEqClass_iff_reachable,
        Metta.Bindings.addEqRaw, hne, leaEqualityEdges] using hnot
    · have hreach :=
          mem_leaEqClass_iff_reachable.mp
            (mem_leaEqClassOrdered_iff.mp hclass)
      simpa [Metta.Bindings.addEqRaw, hne, leaEqualityEdges] using hreach
  · simpa using hlookup

private theorem mettaClassValueEquations_pair_eq
    {valuation : String → Metta.Atom} {values : List Metta.Atom}
    (hsatisfied : MettaEquationsSatisfied valuation
      (mettaClassValueEquations values))
    {left right : Metta.Atom}
    (hleft : left ∈ values) (hright : right ∈ values) :
    applyClassSolution valuation left =
      applyClassSolution valuation right := by
  cases values with
  | nil => simp at hleft
  | cons first rest =>
      have hfirstEq : ∀ value ∈ first :: rest,
          applyClassSolution valuation first =
            applyClassSolution valuation value := by
        intro value hvalue
        rcases List.mem_cons.mp hvalue with rfl | hvalue
        · rfl
        · exact hsatisfied (first, value) (by
            simp [mettaClassValueEquations, hvalue])
      exact (hfirstEq left hleft).symm.trans (hfirstEq right hright)

private theorem aliasJoin_sigma_var_agrees
    {bindings : Metta.Bindings} {left right : String}
    (hsourceLoop : bindings.hasLoop = false)
    (hsourceNonvariable : LeaAssignmentsNonVariable bindings)
    (houtLoop : (Metta.Bindings.addEqRaw bindings left right).hasLoop =
      false) :
    ∀ start finish,
      leaClassSolution bindings start = .var finish →
        leaClassSolution
            (Metta.Bindings.addEqRaw bindings left right) start =
          leaClassSolution
            (Metta.Bindings.addEqRaw bindings left right) finish := by
  intro start finish hresult
  apply leaClassSolution_eq_of_mem_eqClass houtLoop
  apply mem_eqClass_addEqRaw_of_mem
  exact leaClassSolution_eq_var_mem_eqClass
    hsourceLoop hsourceNonvariable hresult

private theorem aliasJoin_sigma_nonvar_pick
    {bindings : Metta.Bindings} {left right : String}
    (hne : left ≠ right)
    (hsource : CanonicallyPrincipal bindings)
    (hsourceNoFloat : LeaBindingsNoFloat bindings)
    (hsourceNonvariable : LeaAssignmentsNonVariable bindings)
    (hsourceLoop : bindings.hasLoop = false)
    (houtLoop : (Metta.Bindings.addEqRaw bindings left right).hasLoop =
      false)
    (hunify : Metta.Bindings.unifyValues
      (Metta.Bindings.classValues
        (Metta.Bindings.addEqRaw bindings left right) left) = some []) :
    ∀ start, (∀ target,
      leaClassSolution bindings start ≠ .var target) →
      ∃ selected, (∀ target, selected ≠ Metta.Atom.var target) ∧
        applyClassSolution (leaClassSolution bindings) selected =
          leaClassSolution bindings start ∧
        leaClassSolution
            (Metta.Bindings.addEqRaw bindings left right) start =
          applyClassSolution
            (leaClassSolution
              (Metta.Bindings.addEqRaw bindings left right)) selected := by
  intro start hnonvar
  cases hsourceValues : Metta.Bindings.classValues bindings start with
  | nil =>
      have hrepresentative :=
        leaClassSolution_eq_representative_of_classValues_nil hsourceValues
      exact (hnonvar _ hrepresentative).elim
  | cons sourceFirst sourceTail =>
      have hsourceFirstMem : sourceFirst ∈
          Metta.Bindings.classValues bindings start := by
        rw [hsourceValues]
        simp
      have hsourceFirstCandidate : sourceFirst ∈
          Metta.Bindings.classValues
            (Metta.Bindings.addEqRaw bindings left right) start :=
        classValue_addEqRaw_of_source hsourceFirstMem
      cases hcandidateValues : Metta.Bindings.classValues
          (Metta.Bindings.addEqRaw bindings left right) start with
      | nil => simp [hcandidateValues] at hsourceFirstCandidate
      | cons selected tail =>
          have hselectedMem : selected ∈
              Metta.Bindings.classValues
                (Metta.Bindings.addEqRaw bindings left right) start := by
            rw [hcandidateValues]
            simp
          have hcandidateNonvariable : LeaAssignmentsNonVariable
              (Metta.Bindings.addEqRaw bindings left right) :=
            hsourceNonvariable.addEqRaw left right
          have hselectedNonvar : ∀ target, selected ≠ .var target :=
            leaClassValue_nonvariable hcandidateNonvariable hselectedMem
          have hsigmaSelected :
              applyClassSolution (leaClassSolution bindings) selected =
                leaClassSolution bindings start := by
            by_cases hjoined : left ∈ Metta.Bindings.eqClass
                (Metta.Bindings.addEqRaw bindings left right) start
            · have hselectedJoined : selected ∈
                  Metta.Bindings.classValues
                    (Metta.Bindings.addEqRaw bindings left right) left := by
                rw [← classValues_eq_of_mem_eqClass hjoined]
                exact hselectedMem
              have hsourceFirstJoined : sourceFirst ∈
                  Metta.Bindings.classValues
                    (Metta.Bindings.addEqRaw bindings left right) left := by
                rw [← classValues_eq_of_mem_eqClass hjoined]
                exact hsourceFirstCandidate
              have hcandidateNoFloat : LeaBindingsNoFloat
                  (Metta.Bindings.addEqRaw bindings left right) :=
                leaBindingsNoFloat_addEqRaw hsourceNoFloat
              have hclassNoFloat : ∀ atom ∈
                    Metta.Bindings.classValues
                      (Metta.Bindings.addEqRaw bindings left right) left,
                    MettaAtomNoFloat atom := by
                intro atom hatom
                exact leaClassValue_noFloat hcandidateNoFloat hatom
              have hclassSatisfied : MettaEquationsSatisfied
                  (leaClassSolution bindings)
                  (mettaClassValueEquations
                    (Metta.Bindings.classValues
                      (Metta.Bindings.addEqRaw bindings left right) left)) :=
                (unifyValues_solution_iff (leaClassSolution bindings)
                  hclassNoFloat hunify).mp (by
                    simp [MettaConstraintsSatisfied])
              have hpair := mettaClassValueEquations_pair_eq
                hclassSatisfied hselectedJoined hsourceFirstJoined
              exact hpair.trans
                (leaClassSolution_eq_apply_firstClassValue
                  hsourceLoop hsourceValues
                  (leaClassValue_nonvariable hsourceNonvariable
                    hsourceFirstMem)).symm
            · have hselectedSource :=
                classValue_source_of_addEqRaw_of_not_joined
                  hne hjoined hselectedMem
              exact (leaBindingSatisfied_classValue
                hsource.1 hselectedSource).symm
          refine ⟨selected, hselectedNonvar, hsigmaSelected, ?_⟩
          exact leaClassSolution_eq_apply_firstClassValue
            houtLoop hcandidateValues hselectedNonvar

/-- A successful alias join needing no substitution preserves canonical
principality.  The empty local unifier says all newly joined class values are
already syntactically coherent. -/
private theorem addEqRaw_nochange_canonicallyPrincipal
    {bindings : Metta.Bindings} {left right : String}
    (hne : left ≠ right)
    (hsource : CanonicallyPrincipal bindings)
    (hsourceNoFloat : LeaBindingsNoFloat bindings)
    (hsourceNonvariable : LeaAssignmentsNonVariable bindings)
    (hsourceLoop : bindings.hasLoop = false)
    (hunify : Metta.Bindings.unifyValues
      (Metta.Bindings.classValues
        (Metta.Bindings.addEqRaw bindings left right) left) = some [])
    (houtLoop : (Metta.Bindings.addEqRaw bindings left right).hasLoop =
      false) :
    CanonicallyPrincipal
      (Metta.Bindings.addEqRaw bindings left right) := by
  let sigma := leaClassSolution bindings
  let chi := leaClassSolution
    (Metta.Bindings.addEqRaw bindings left right)
  have htransfer : ∀ first second,
      applyClassSolution sigma first = applyClassSolution sigma second →
        applyClassSolution chi first = applyClassSolution chi second :=
    sigma_canonical_transfer sigma chi
      (aliasJoin_sigma_var_agrees hsourceLoop
        hsourceNonvariable houtLoop)
      (aliasJoin_sigma_nonvar_pick hne hsource hsourceNoFloat
        hsourceNonvariable hsourceLoop houtLoop hunify)
  have hsourceSatisfied : LeaBindingSatisfied chi bindings := by
    constructor
    · intro key value hvalue
      have hold := hsource.1.1 key value hvalue
      have hnew := htransfer (.var key) value (by
        simpa [sigma, applyClassSolution] using hold)
      simpa [chi, applyClassSolution] using hnew
    · intro first second hedge
      have hold := hsource.1.2 first second hedge
      have hnew := htransfer (.var first) (.var second) (by
        simpa [sigma, applyClassSolution] using hold)
      simpa [chi, applyClassSolution] using hnew
  have hnewEquality : chi left = chi right := by
    apply leaClassSolution_satisfies_equalities houtLoop left right
    simp [Metta.Bindings.addEqRaw, hne]
  apply canonicallyPrincipal_of_canonical_satisfied
  · exact (leaBindingSatisfied_addEqRaw_iff
      chi bindings left right).mpr ⟨hsourceSatisfied, hnewEquality⟩
  · exact hsourceNonvariable.addEqRaw left right

private theorem leaAddVarEquality_canonicallyPrincipal
    {bindings out : Metta.Bindings} {left right : String}
    (hsource : CanonicallyPrincipal bindings)
    (hsourceNoFloat : LeaBindingsNoFloat bindings)
    (hsourceNonvariable : LeaAssignmentsNonVariable bindings)
    (hsourceIrreflexive : LeaEqualitiesIrreflexive bindings)
    (hout : out ∈ Metta.Bindings.addVarEquality bindings left right)
    (houtLoop : out.hasLoop = false) :
    CanonicallyPrincipal out := by
  have hsourceLoop : bindings.hasLoop = false :=
    leaBindings_hasLoop_false_of_satisfied
      hsource.1 hsourceNonvariable hsourceIrreflexive
  cases hunify : Metta.Bindings.unifyValues
      (Metta.Bindings.classValues
        (Metta.Bindings.addEqRaw bindings left right) left) with
  | none => simp [Metta.Bindings.addVarEquality, hunify] at hout
  | some result =>
      cases result with
      | nil =>
          simp [Metta.Bindings.addVarEquality, hunify] at hout
          subst out
          by_cases heq : left = right
          · subst right
            simpa [Metta.Bindings.addEqRaw] using hsource
          · exact addEqRaw_nochange_canonicallyPrincipal
              heq hsource hsourceNoFloat hsourceNonvariable
              hsourceLoop hunify houtLoop
      | cons binding rest =>
          cases hreconcile : wholeBindingReconciliation bindings
              [(.var left, .var right)] with
          | none =>
              simp [Metta.Bindings.addVarEquality, hunify,
                hreconcile] at hout
          | some sigma =>
              simp [Metta.Bindings.addVarEquality, hunify,
                hreconcile] at hout
              subst out
              exact equalityReconciliationRebuild_canonicallyPrincipal
                hsourceNoFloat hreconcile houtLoop

private theorem leaAddVarBinding_canonicallyPrincipal
    {bindings out : Metta.Bindings} {key : String} {value : Metta.Atom}
    (hsource : CanonicallyPrincipal bindings)
    (hsourceNoFloat : LeaBindingsNoFloat bindings)
    (hsourceNonvariable : LeaAssignmentsNonVariable bindings)
    (hsourceIrreflexive : LeaEqualitiesIrreflexive bindings)
    (hvalueNoFloat : MettaAtomNoFloat value)
    (hout : out ∈ Metta.Bindings.addVarBinding bindings key value)
    (houtLoop : out.hasLoop = false) :
    CanonicallyPrincipal out := by
  have hsourceLoop : bindings.hasLoop = false :=
    leaBindings_hasLoop_false_of_satisfied
      hsource.1 hsourceNonvariable hsourceIrreflexive
  cases value with
  | var target =>
      apply leaAddVarEquality_canonicallyPrincipal
        hsource hsourceNoFloat hsourceNonvariable hsourceIrreflexive
        (left := key) (right := target)
      · simpa [Metta.Bindings.addVarBinding] using hout
      · exact houtLoop
  | sym symbol =>
      cases hvalues : Metta.Bindings.classValues bindings key with
      | nil =>
          simp [Metta.Bindings.addVarBinding, hvalues] at hout
          subst out
          exact addValRaw_fresh_canonicallyPrincipal
            hsource hsourceNonvariable hsourceLoop hvalues
              (by intro target h; cases h) houtLoop
      | cons first rest =>
          cases hunify : Metta.Bindings.unifyValues
              (first :: (rest ++ [.sym symbol])) with
          | none =>
              simp [Metta.Bindings.addVarBinding, hvalues, hunify] at hout
          | some result =>
              cases result with
              | nil =>
                  simp [Metta.Bindings.addVarBinding, hvalues, hunify] at hout
                  subst out
                  exact hsource
              | cons binding resultRest =>
                  cases hreconcile : wholeBindingReconciliation bindings
                      [(.var key, .sym symbol)] with
                  | none =>
                      simp [Metta.Bindings.addVarBinding, hvalues,
                        hunify, hreconcile] at hout
                  | some sigma =>
                      simp [Metta.Bindings.addVarBinding, hvalues,
                        hunify, hreconcile] at hout
                      subst out
                      exact valueReconciliationRebuild_canonicallyPrincipal
                        hsourceNoFloat hvalueNoFloat hreconcile houtLoop
  | gnd ground =>
      cases hvalues : Metta.Bindings.classValues bindings key with
      | nil =>
          simp [Metta.Bindings.addVarBinding, hvalues] at hout
          subst out
          exact addValRaw_fresh_canonicallyPrincipal
            hsource hsourceNonvariable hsourceLoop hvalues
              (by intro target h; cases h) houtLoop
      | cons first rest =>
          cases hunify : Metta.Bindings.unifyValues
              (first :: (rest ++ [.gnd ground])) with
          | none =>
              simp [Metta.Bindings.addVarBinding, hvalues, hunify] at hout
          | some result =>
              cases result with
              | nil =>
                  simp [Metta.Bindings.addVarBinding, hvalues, hunify] at hout
                  subst out
                  exact hsource
              | cons binding resultRest =>
                  cases hreconcile : wholeBindingReconciliation bindings
                      [(.var key, .gnd ground)] with
                  | none =>
                      simp [Metta.Bindings.addVarBinding, hvalues,
                        hunify, hreconcile] at hout
                  | some sigma =>
                      simp [Metta.Bindings.addVarBinding, hvalues,
                        hunify, hreconcile] at hout
                      subst out
                      exact valueReconciliationRebuild_canonicallyPrincipal
                        hsourceNoFloat hvalueNoFloat hreconcile houtLoop
  | expr atoms =>
      cases hvalues : Metta.Bindings.classValues bindings key with
      | nil =>
          simp [Metta.Bindings.addVarBinding, hvalues] at hout
          subst out
          exact addValRaw_fresh_canonicallyPrincipal
            hsource hsourceNonvariable hsourceLoop hvalues
              (by intro target h; cases h) houtLoop
      | cons first rest =>
          cases hunify : Metta.Bindings.unifyValues
              (first :: (rest ++ [.expr atoms])) with
          | none =>
              simp [Metta.Bindings.addVarBinding, hvalues, hunify] at hout
          | some result =>
              cases result with
              | nil =>
                  simp [Metta.Bindings.addVarBinding, hvalues, hunify] at hout
                  subst out
                  exact hsource
              | cons binding resultRest =>
                  cases hreconcile : wholeBindingReconciliation bindings
                      [(.var key, .expr atoms)] with
                  | none =>
                      simp [Metta.Bindings.addVarBinding, hvalues,
                        hunify, hreconcile] at hout
                  | some sigma =>
                      simp [Metta.Bindings.addVarBinding, hvalues,
                        hunify, hreconcile] at hout
                      subst out
                      exact valueReconciliationRebuild_canonicallyPrincipal
                        hsourceNoFloat hvalueNoFloat hreconcile houtLoop

/-- Folding one relation into a family of canonical accumulators preserves
canonical principality for every loop-free surviving branch. -/
private theorem leaMergeOne_canonicallyPrincipal
    {seeds : List Metta.Bindings} {relation : Metta.BindingRel}
    {out : Metta.Bindings}
    (hseeds : ∀ seed ∈ seeds, CanonicallyPrincipal seed)
    (hseedsNoFloat : ∀ seed ∈ seeds, LeaBindingsNoFloat seed)
    (hseedsNonvariable : ∀ seed ∈ seeds,
      LeaAssignmentsNonVariable seed)
    (hseedsIrreflexive : ∀ seed ∈ seeds,
      LeaEqualitiesIrreflexive seed)
    (hrelationNoFloat : LeaBindingsNoFloat [relation])
    (hout : out ∈ Metta.Bindings.mergeOne seeds relation)
    (houtLoop : out.hasLoop = false) :
    CanonicallyPrincipal out := by
  unfold Metta.Bindings.mergeOne at hout
  obtain ⟨seed, hseed, hout⟩ := List.mem_flatMap.mp hout
  cases relation with
  | val key value =>
      apply leaAddVarBinding_canonicallyPrincipal
        (hseeds seed hseed)
        (hseedsNoFloat seed hseed)
        (hseedsNonvariable seed hseed)
        (hseedsIrreflexive seed hseed)
        (hrelationNoFloat key value (by simp))
        hout houtLoop
  | eq left right =>
      apply leaAddVarEquality_canonicallyPrincipal
        (hseeds seed hseed)
        (hseedsNoFloat seed hseed)
        (hseedsNonvariable seed hseed)
        (hseedsIrreflexive seed hseed)
        hout houtLoop

/-- Equality insertion has the identical principal reconciliation property. -/
private theorem leaAddVarEquality_hasPrincipal_of_reconciliation
    {source out : Metta.Bindings}
    {left right : String} {result : Metta.Subst}
    (hsourceNoFloat : LeaBindingsNoFloat source)
    (hout : out ∈ Metta.Bindings.addVarEquality source left right)
    (hreconcile : wholeBindingReconciliation source
      [(.var left, .var right)] = some result) :
    HasPrincipalModel
      (fun valuation => LeaBindingSatisfied valuation out) := by
  apply hasPrincipalModel_congr
    (left := fun valuation =>
      LeaBindingSatisfied valuation source ∧
        MettaEquationsSatisfied valuation [(.var left, .var right)])
  · intro valuation
    rw [leaAddVarEquality_solution_iff valuation hsourceNoFloat hout]
    simp [MettaEquationsSatisfied, MettaEquationSatisfied,
      applyClassSolution]
  · exact wholeBindingReconciliation_input_hasPrincipal
      hsourceNoFloat
      (by
        intro equation hequation
        simp only [List.mem_singleton] at hequation
        subst equation
        simp [MettaAtomNoFloat])
      hreconcile

/-- Every surviving equality insertion reflects loop-freedom back to its
source.  The raw empty-unifier branch uses syntactic replay; a reconciliation
branch supplies a satisfying source model through its principal output. -/
private theorem leaAddVarEquality_source_hasLoop_false
    {source out : Metta.Bindings} {left right : String}
    (hsourceNoFloat : LeaBindingsNoFloat source)
    (hsourceNonvariable : LeaAssignmentsNonVariable source)
    (hsourceIrreflexive : LeaEqualitiesIrreflexive source)
    (hout : out ∈ Metta.Bindings.addVarEquality source left right)
    (houtLoop : out.hasLoop = false) :
    source.hasLoop = false := by
  cases hunify : Metta.Bindings.unifyValues
      (Metta.Bindings.classValues
        (Metta.Bindings.addEqRaw source left right) left) with
  | none =>
      simp [Metta.Bindings.addVarEquality, hunify] at hout
  | some result =>
      cases result with
      | nil =>
          have houtEq : out = Metta.Bindings.addEqRaw source left right := by
            simpa [Metta.Bindings.addVarEquality, hunify] using hout
          subst out
          exact hasLoop_false_of_addEqRaw_emptyUnifier
            hsourceNonvariable hsourceNoFloat hunify houtLoop
      | cons binding rest =>
          cases hreconcile : wholeBindingReconciliation source
              [(.var left, .var right)] with
          | none =>
              simp [Metta.Bindings.addVarEquality, hunify,
                hreconcile] at hout
          | some sigma =>
              obtain ⟨general, houtSatisfied, _⟩ :=
                leaAddVarEquality_hasPrincipal_of_reconciliation
                  hsourceNoFloat hout hreconcile
              have hsourceSatisfied :
                  LeaBindingSatisfied general source :=
                ((leaAddVarEquality_solution_iff general
                  hsourceNoFloat hout).mp houtSatisfied).1
              exact leaBindings_hasLoop_false_of_satisfied
                hsourceSatisfied hsourceNonvariable hsourceIrreflexive

/-- Every surviving value insertion likewise reflects loop-freedom to the
source.  Fresh raw values use success replay, unchanged branches are
immediate, and reconciliation branches project a source model from the exact
solution theorem. -/
private theorem leaAddVarBinding_source_hasLoop_false
    {source out : Metta.Bindings} {key : String} {value : Metta.Atom}
    (hsourceNoFloat : LeaBindingsNoFloat source)
    (hsourceNonvariable : LeaAssignmentsNonVariable source)
    (hsourceIrreflexive : LeaEqualitiesIrreflexive source)
    (hvalueNoFloat : MettaAtomNoFloat value)
    (hout : out ∈ Metta.Bindings.addVarBinding source key value)
    (houtLoop : out.hasLoop = false) :
    source.hasLoop = false := by
  cases value with
  | var target =>
      exact leaAddVarEquality_source_hasLoop_false
        hsourceNoFloat hsourceNonvariable hsourceIrreflexive
        (by simpa [Metta.Bindings.addVarBinding] using hout) houtLoop
  | sym symbol =>
      cases hvalues : Metta.Bindings.classValues source key with
      | nil =>
          have houtEq : out =
              Metta.Bindings.addValRaw source key (.sym symbol) := by
            simpa [Metta.Bindings.addVarBinding, hvalues] using hout
          subst out
          exact hasLoop_false_of_addValRaw_fresh hvalues houtLoop
      | cons first rest =>
          cases hunify : Metta.Bindings.unifyValues
              (first :: (rest ++ [.sym symbol])) with
          | none =>
              simp [Metta.Bindings.addVarBinding, hvalues, hunify] at hout
          | some result =>
              cases result with
              | nil =>
                  have houtEq : out = source := by
                    simpa [Metta.Bindings.addVarBinding, hvalues,
                      hunify] using hout
                  subst out
                  exact houtLoop
              | cons binding resultRest =>
                  cases hreconcile : wholeBindingReconciliation source
                      [(.var key, .sym symbol)] with
                  | none =>
                      simp [Metta.Bindings.addVarBinding, hvalues,
                        hunify, hreconcile] at hout
                  | some sigma =>
                      obtain ⟨general, houtSatisfied, _⟩ :=
                        leaAddVarBinding_hasPrincipal_of_reconciliation
                          hsourceNoFloat hvalueNoFloat hout hreconcile
                      have hsourceSatisfied :
                          LeaBindingSatisfied general source :=
                        ((leaAddVarBinding_solution_iff general
                          hsourceNoFloat hvalueNoFloat hout).mp
                            houtSatisfied).1
                      exact leaBindings_hasLoop_false_of_satisfied
                        hsourceSatisfied hsourceNonvariable
                          hsourceIrreflexive
  | gnd ground =>
      cases hvalues : Metta.Bindings.classValues source key with
      | nil =>
          have houtEq : out =
              Metta.Bindings.addValRaw source key (.gnd ground) := by
            simpa [Metta.Bindings.addVarBinding, hvalues] using hout
          subst out
          exact hasLoop_false_of_addValRaw_fresh hvalues houtLoop
      | cons first rest =>
          cases hunify : Metta.Bindings.unifyValues
              (first :: (rest ++ [.gnd ground])) with
          | none =>
              simp [Metta.Bindings.addVarBinding, hvalues, hunify] at hout
          | some result =>
              cases result with
              | nil =>
                  have houtEq : out = source := by
                    simpa [Metta.Bindings.addVarBinding, hvalues,
                      hunify] using hout
                  subst out
                  exact houtLoop
              | cons binding resultRest =>
                  cases hreconcile : wholeBindingReconciliation source
                      [(.var key, .gnd ground)] with
                  | none =>
                      simp [Metta.Bindings.addVarBinding, hvalues,
                        hunify, hreconcile] at hout
                  | some sigma =>
                      obtain ⟨general, houtSatisfied, _⟩ :=
                        leaAddVarBinding_hasPrincipal_of_reconciliation
                          hsourceNoFloat hvalueNoFloat hout hreconcile
                      have hsourceSatisfied :
                          LeaBindingSatisfied general source :=
                        ((leaAddVarBinding_solution_iff general
                          hsourceNoFloat hvalueNoFloat hout).mp
                            houtSatisfied).1
                      exact leaBindings_hasLoop_false_of_satisfied
                        hsourceSatisfied hsourceNonvariable
                          hsourceIrreflexive
  | expr atoms =>
      cases hvalues : Metta.Bindings.classValues source key with
      | nil =>
          have houtEq : out =
              Metta.Bindings.addValRaw source key (.expr atoms) := by
            simpa [Metta.Bindings.addVarBinding, hvalues] using hout
          subst out
          exact hasLoop_false_of_addValRaw_fresh hvalues houtLoop
      | cons first rest =>
          cases hunify : Metta.Bindings.unifyValues
              (first :: (rest ++ [.expr atoms])) with
          | none =>
              simp [Metta.Bindings.addVarBinding, hvalues, hunify] at hout
          | some result =>
              cases result with
              | nil =>
                  have houtEq : out = source := by
                    simpa [Metta.Bindings.addVarBinding, hvalues,
                      hunify] using hout
                  subst out
                  exact houtLoop
              | cons binding resultRest =>
                  cases hreconcile : wholeBindingReconciliation source
                      [(.var key, .expr atoms)] with
                  | none =>
                      simp [Metta.Bindings.addVarBinding, hvalues,
                        hunify, hreconcile] at hout
                  | some sigma =>
                      obtain ⟨general, houtSatisfied, _⟩ :=
                        leaAddVarBinding_hasPrincipal_of_reconciliation
                          hsourceNoFloat hvalueNoFloat hout hreconcile
                      have hsourceSatisfied :
                          LeaBindingSatisfied general source :=
                        ((leaAddVarBinding_solution_iff general
                          hsourceNoFloat hvalueNoFloat hout).mp
                            houtSatisfied).1
                      exact leaBindings_hasLoop_false_of_satisfied
                        hsourceSatisfied hsourceNonvariable
                          hsourceIrreflexive

/-- Conditional fold step: a source accumulator only needs canonical
principality when its branch is loop-free.  A loop-free insertion output
reflects that condition backward before the existing insertion theorem is
applied. -/
private theorem leaMergeOne_canonicallyPrincipal_of_loop
    {seeds : List Metta.Bindings} {relation : Metta.BindingRel}
    {out : Metta.Bindings}
    (hseeds : ∀ seed ∈ seeds, seed.hasLoop = false →
      CanonicallyPrincipal seed)
    (hseedsNoFloat : ∀ seed ∈ seeds, LeaBindingsNoFloat seed)
    (hseedsNonvariable : ∀ seed ∈ seeds,
      LeaAssignmentsNonVariable seed)
    (hseedsIrreflexive : ∀ seed ∈ seeds,
      LeaEqualitiesIrreflexive seed)
    (hrelationNoFloat : LeaBindingsNoFloat [relation])
    (hout : out ∈ Metta.Bindings.mergeOne seeds relation)
    (houtLoop : out.hasLoop = false) :
    CanonicallyPrincipal out := by
  unfold Metta.Bindings.mergeOne at hout
  obtain ⟨seed, hseed, hout⟩ := List.mem_flatMap.mp hout
  cases relation with
  | val key value =>
      have hvalueNoFloat : MettaAtomNoFloat value :=
        hrelationNoFloat key value (by simp)
      have hseedLoop : seed.hasLoop = false :=
        leaAddVarBinding_source_hasLoop_false
          (hseedsNoFloat seed hseed)
          (hseedsNonvariable seed hseed)
          (hseedsIrreflexive seed hseed)
          hvalueNoFloat hout houtLoop
      exact leaAddVarBinding_canonicallyPrincipal
        (hseeds seed hseed hseedLoop)
        (hseedsNoFloat seed hseed)
        (hseedsNonvariable seed hseed)
        (hseedsIrreflexive seed hseed)
        hvalueNoFloat hout houtLoop
  | eq left right =>
      have hseedLoop : seed.hasLoop = false :=
        leaAddVarEquality_source_hasLoop_false
          (hseedsNoFloat seed hseed)
          (hseedsNonvariable seed hseed)
          (hseedsIrreflexive seed hseed)
          hout houtLoop
      exact leaAddVarEquality_canonicallyPrincipal
        (hseeds seed hseed hseedLoop)
        (hseedsNoFloat seed hseed)
        (hseedsNonvariable seed hseed)
        (hseedsIrreflexive seed hseed)
        hout houtLoop

/-- The conditional invariant is stable under the complete right-binding
fold.  Only the branch that actually survives to a loop-free result is asked
to supply a canonical source accumulator. -/
private theorem leaMergeFold_canonicallyPrincipal_of_loop
    {relations : Metta.Bindings} {seeds : List Metta.Bindings}
    {out : Metta.Bindings}
    (hseeds : ∀ seed ∈ seeds, seed.hasLoop = false →
      CanonicallyPrincipal seed)
    (hseedsNoFloat : ∀ seed ∈ seeds, LeaBindingsNoFloat seed)
    (hseedsNonvariable : ∀ seed ∈ seeds,
      LeaAssignmentsNonVariable seed)
    (hseedsIrreflexive : ∀ seed ∈ seeds,
      LeaEqualitiesIrreflexive seed)
    (hrelationsNoFloat : LeaBindingsNoFloat relations)
    (hout : out ∈ relations.foldl Metta.Bindings.mergeOne seeds)
    (houtLoop : out.hasLoop = false) :
    CanonicallyPrincipal out := by
  induction relations generalizing seeds out with
  | nil =>
      simp only [List.foldl_nil] at hout
      exact hseeds out hout houtLoop
  | cons relation rest ih =>
      simp only [List.foldl_cons] at hout
      have hrelationNoFloat : LeaBindingsNoFloat [relation] := by
        intro key value hmem
        apply hrelationsNoFloat key value
        exact List.mem_cons.mpr (Or.inl (by simpa using hmem))
      have hrestNoFloat : LeaBindingsNoFloat rest := by
        intro key value hmem
        exact hrelationsNoFloat key value
          (List.mem_cons_of_mem relation hmem)
      have hnextCanonical : ∀ next ∈
          Metta.Bindings.mergeOne seeds relation,
          next.hasLoop = false → CanonicallyPrincipal next := by
        intro next hnext hnextLoop
        exact leaMergeOne_canonicallyPrincipal_of_loop
          hseeds hseedsNoFloat hseedsNonvariable hseedsIrreflexive
          hrelationNoFloat hnext hnextLoop
      have hnextNoFloat : ∀ next ∈
          Metta.Bindings.mergeOne seeds relation,
          LeaBindingsNoFloat next := by
        intro next hnext
        unfold Metta.Bindings.mergeOne at hnext
        obtain ⟨seed, hseed, hnext⟩ := List.mem_flatMap.mp hnext
        cases relation with
        | val key value =>
            exact leaAddVarBinding_result_noFloat
              (hseedsNoFloat seed hseed)
              (hrelationNoFloat key value (by simp)) hnext
        | eq left right =>
            exact leaAddVarEquality_result_noFloat
              (hseedsNoFloat seed hseed) hnext
      have hnextNonvariable : ∀ next ∈
          Metta.Bindings.mergeOne seeds relation,
          LeaAssignmentsNonVariable next := by
        intro next hnext
        unfold Metta.Bindings.mergeOne at hnext
        obtain ⟨seed, hseed, hnext⟩ := List.mem_flatMap.mp hnext
        cases relation with
        | val key value =>
            exact leaAddVarBinding_result_assignmentsNonVariable
              (hseedsNonvariable seed hseed) hnext
        | eq left right =>
            exact leaAddVarEquality_result_assignmentsNonVariable
              (hseedsNonvariable seed hseed) hnext
      have hnextIrreflexive : ∀ next ∈
          Metta.Bindings.mergeOne seeds relation,
          LeaEqualitiesIrreflexive next := by
        intro next hnext
        unfold Metta.Bindings.mergeOne at hnext
        obtain ⟨seed, hseed, hnext⟩ := List.mem_flatMap.mp hnext
        cases relation with
        | val key value =>
            exact leaAddVarBinding_result_equalitiesIrreflexive
              (hseedsIrreflexive seed hseed) hnext
        | eq left right =>
            exact leaAddVarEquality_result_equalitiesIrreflexive
              (hseedsIrreflexive seed hseed) hnext
      exact ih hnextCanonical hnextNoFloat hnextNonvariable
        hnextIrreflexive hrestNoFloat hout houtLoop

/-- A successful loop-free merge is canonically principal whenever its left
input is conditionally canonical and its right input is host-float-free. -/
private theorem leaMerge_canonicallyPrincipal_of_loop
    {left right out : Metta.Bindings}
    (hleft : left.hasLoop = false → CanonicallyPrincipal left)
    (hleftNoFloat : LeaBindingsNoFloat left)
    (hleftNonvariable : LeaAssignmentsNonVariable left)
    (hleftIrreflexive : LeaEqualitiesIrreflexive left)
    (hrightNoFloat : LeaBindingsNoFloat right)
    (hout : out ∈ Metta.Bindings.merge left right)
    (houtLoop : out.hasLoop = false) :
    CanonicallyPrincipal out := by
  apply leaMergeFold_canonicallyPrincipal_of_loop
    (relations := right) (seeds := [left]) (out := out)
  · intro seed hseed
    simp only [List.mem_singleton] at hseed
    subst seed
    exact hleft
  · intro seed hseed
    simp only [List.mem_singleton] at hseed
    subst seed
    exact hleftNoFloat
  · intro seed hseed
    simp only [List.mem_singleton] at hseed
    subst seed
    exact hleftNonvariable
  · intro seed hseed
    simp only [List.mem_singleton] at hseed
    subst seed
    exact hleftIrreflexive
  · exact hrightNoFloat
  · simpa [Metta.Bindings.merge] using hout
  · exact houtLoop

/-- Updating a valuation outside an atom's variable support leaves its
homomorphic interpretation unchanged. -/
private theorem applyClassSolution_update_of_not_mem_vars
    (valuation : String → Metta.Atom) (key : String)
    (replacement : Metta.Atom) :
    ∀ atom : Metta.Atom, key ∉ atom.vars →
      applyClassSolution (Function.update valuation key replacement) atom =
        applyClassSolution valuation atom := by
  intro atom
  induction atom with
  | sym symbol => intro _; simp [applyClassSolution]
  | var name =>
      intro hnotmem
      have hne : name ≠ key := by
        intro heq
        subst name
        exact hnotmem (by simp [Metta.Atom.vars])
      simp [applyClassSolution, Function.update, hne]
  | gnd grounded => intro _; simp [applyClassSolution]
  | expr atoms ih =>
      intro hnotmem
      simp only [applyClassSolution]
      congr 1
      apply List.map_congr_left
      intro child hchild
      apply ih child hchild
      intro hkey
      apply hnotmem
      simpa [Metta.Atom.vars] using
        (List.mem_flatten.mpr
          ⟨child.vars, List.mem_map.mpr ⟨child, hchild, rfl⟩, hkey⟩)

/-- The variable-identity valuation is principal for the empty Lea binding
theory. -/
private theorem emptyBindings_principal :
    ∃ general : String → Metta.Atom,
      LeaBindingSatisfied general [] ∧
        ∀ specific, LeaBindingSatisfied specific [] →
          HumanMatchModelTheory.ValuationRefines specific general := by
  refine ⟨fun name => .var name, by simp [LeaBindingSatisfied], ?_⟩
  intro specific _hsatisfied
  refine ⟨specific, fun name => ?_⟩
  simp [applyClassSolution]

/-- The empty binding presentation is aligned with LeaTTa's canonical class
resolver, not only principal up to an arbitrary witness. -/
private theorem emptyBindings_canonicallyPrincipal :
    CanonicallyPrincipal Metta.Bindings.empty := by
  have hcanonical : leaClassSolution Metta.Bindings.empty =
      (fun name => Metta.Atom.var name) := by
    funext name
    simp [leaClassSolution, Metta.Bindings.empty,
      Metta.Bindings.resolve, Metta.Bindings.eqClassOrdered,
      Metta.Bindings.eqVarsInOrder]
  unfold CanonicallyPrincipal LeaCanonicalSolutionInvariant
  rw [hcanonical]
  constructor
  · simp [LeaBindingSatisfied, Metta.Bindings.empty]
  · intro specific _hsatisfied
    refine ⟨specific, fun name => ?_⟩
    simp [applyClassSolution]

/-! ### Runtime binding-state invariant -/

/-- The semantic and representation invariants carried by every loop-filtered
runtime binding state on the repaired query path.  Canonical principality is
the load-bearing field: its canonical resolver is an explicit model, while
the remaining fields are exactly the preservation hypotheses consumed by the
next merge. -/
structure LeaRuntimeBindingInvariant (bindings : Metta.Bindings) : Prop where
  loopFree : bindings.hasLoop = false
  canonical : LeaCanonicalSolutionInvariant bindings
  noFloat : LeaBindingsNoFloat bindings
  assignmentsNonVariable : LeaAssignmentsNonVariable bindings
  equalitiesIrreflexive : LeaEqualitiesIrreflexive bindings

/-- Empty runtime bindings establish the base of the reachable-state
invariant. -/
theorem leaRuntimeBindingInvariant_empty :
    LeaRuntimeBindingInvariant Metta.Bindings.empty := by
  refine ⟨?_, emptyBindings_canonicallyPrincipal, ?_, ?_, ?_⟩
  · simp [Metta.Bindings.empty, Metta.Bindings.hasLoop,
      Metta.Bindings.vars]
  · simp [LeaBindingsNoFloat, Metta.Bindings.empty]
  · exact leaAssignmentsNonVariable_empty
  · exact leaEqualitiesIrreflexive_empty

/-- One successful, loop-filtered merge of a reachable accumulator with an
actual repaired matcher output preserves the complete runtime binding-state
invariant.  The canonical model of the result is obtained from the direct
Lea-only merge induction; no HE executable matcher or merge is involved. -/
theorem LeaRuntimeBindingInvariant.merge_matchOutput
    {left matched out : Metta.Bindings} {pattern query : Metta.Atom}
    (hinvariant : LeaRuntimeBindingInvariant left)
    (hpatternNoFloat : MettaAtomNoFloat pattern)
    (hqueryNoFloat : MettaAtomNoFloat query)
    (hmatch : matched ∈ Metta.matchAtoms pattern query)
    (hmerge : out ∈ Metta.Bindings.merge left matched)
    (houtLoop : out.hasLoop = false) :
    LeaRuntimeBindingInvariant out := by
  have hmatchedNoFloat : LeaBindingsNoFloat matched :=
    leaMatchAtoms_result_noFloat hpatternNoFloat hqueryNoFloat hmatch
  refine ⟨houtLoop, ?_, ?_, ?_, ?_⟩
  · exact leaMerge_canonicallyPrincipal_of_loop
      (fun _ => hinvariant.canonical)
      hinvariant.noFloat hinvariant.assignmentsNonVariable
      hinvariant.equalitiesIrreflexive hmatchedNoFloat hmerge houtLoop
  · exact leaMerge_result_noFloat
      hinvariant.noFloat hmatchedNoFloat hmerge
  · exact leaMerge_result_assignmentsNonVariable
      hinvariant.assignmentsNonVariable hmerge
  · exact leaMerge_result_equalitiesIrreflexive
      hinvariant.equalitiesIrreflexive hmerge

/-- An occurs-clean singleton value equation has an explicit principal
Herbrand model.  Any other model is obtained by homomorphically specializing
the still-free variables of this one. -/
private theorem singletonValueBinding_principal
    {key : String} {value : Metta.Atom}
    (hoccurs : Metta.Subst.occurs key value = false) :
    ∃ general : String → Metta.Atom,
      LeaBindingSatisfied general [Metta.BindingRel.val key value] ∧
        ∀ specific,
          LeaBindingSatisfied specific [Metta.BindingRel.val key value] →
            HumanMatchModelTheory.ValuationRefines specific general := by
  let identity : String → Metta.Atom := fun name => .var name
  let general := Function.update identity key value
  have hnotmem : key ∉ value.vars :=
    not_mem_vars_of_occurs_eq_false key value hoccurs
  have hvalue : applyClassSolution general value = value := by
    calc
      applyClassSolution general value =
          applyClassSolution identity value :=
        applyClassSolution_update_of_not_mem_vars
          identity key value value hnotmem
      _ = value := HumanMatchModelTheory.applyClassSolution_identity value
  refine ⟨general, ?_, ?_⟩
  · constructor
    · intro storedKey storedValue hmem
      simp only [List.mem_singleton, Metta.BindingRel.val.injEq] at hmem
      rcases hmem with ⟨rfl, rfl⟩
      simpa [general, Function.update] using hvalue.symm
    · intro left right hmem
      simp at hmem
  · intro specific hspecific
    refine ⟨specific, fun name => ?_⟩
    by_cases hname : name = key
    · subst name
      have hkey := hspecific.1 key value (by simp)
      simpa [general, Function.update, applyClassSolution] using hkey
    · simp [general, identity, hname, applyClassSolution]

/-- The explicit singleton MGU is exactly LeaTTa's own class-solution map. -/
private theorem singletonValueBinding_canonicallyPrincipal
    {key : String} {value : Metta.Atom}
    (hoccurs : Metta.Subst.occurs key value = false) :
    CanonicallyPrincipal [Metta.BindingRel.val key value] := by
  let identity : String → Metta.Atom := fun name => .var name
  let general := Function.update identity key value
  have hnotmem : key ∉ value.vars :=
    not_mem_vars_of_occurs_eq_false key value hoccurs
  have hcanonical :
      leaClassSolution [Metta.BindingRel.val key value] = general := by
    funext name
    by_cases hname : name = key
    · subst name
      simp [leaClassSolution, general, identity,
        Metta.Bindings.resolve_singleton_val_self_of_not_mem key value
          hnotmem]
    · simp [leaClassSolution, general, identity, hname,
        Metta.Bindings.resolve_singleton_val_ne hname]
  have hvalue : applyClassSolution general value = value := by
    calc
      applyClassSolution general value =
          applyClassSolution identity value :=
        applyClassSolution_update_of_not_mem_vars
          identity key value value hnotmem
      _ = value := HumanMatchModelTheory.applyClassSolution_identity value
  unfold CanonicallyPrincipal LeaCanonicalSolutionInvariant
  rw [hcanonical]
  constructor
  · constructor
    · intro storedKey storedValue hmem
      simp only [List.mem_singleton, Metta.BindingRel.val.injEq] at hmem
      rcases hmem with ⟨rfl, rfl⟩
      simpa [general, Function.update] using hvalue.symm
    · intro left right hmem
      simp at hmem
  · intro specific hspecific
    refine ⟨specific, fun name => ?_⟩
    by_cases hname : name = key
    · subst name
      have hkey := hspecific.1 key value (by simp)
      simpa [general, Function.update, applyClassSolution] using hkey
    · simp [general, identity, hname, applyClassSolution]

/-- A singleton alias is principal as well: orienting the presentation toward
the right endpoint does not constrain any later specialization. -/
private theorem singletonEqualityBinding_principal
    (left right : String) :
    ∃ general : String → Metta.Atom,
      LeaBindingSatisfied general [Metta.BindingRel.eq left right] ∧
        ∀ specific,
          LeaBindingSatisfied specific [Metta.BindingRel.eq left right] →
            HumanMatchModelTheory.ValuationRefines specific general := by
  let identity : String → Metta.Atom := fun name => .var name
  let general := Function.update identity left (.var right)
  refine ⟨general, ?_, ?_⟩
  · constructor
    · intro key value hmem
      simp at hmem
    · intro storedLeft storedRight hmem
      simp only [List.mem_singleton, Metta.BindingRel.eq.injEq] at hmem
      rcases hmem with ⟨rfl, rfl⟩
      simp [general, identity, Function.update]
  · intro specific hspecific
    refine ⟨specific, fun name => ?_⟩
    by_cases hname : name = left
    · subst name
      have hedge := hspecific.2 left right (by simp)
      simpa [general, Function.update, applyClassSolution] using hedge
    · simp [general, identity, hname, applyClassSolution]

/-- A non-reflexive singleton alias is canonically oriented to LeaTTa's
stable equality-class representative. -/
private theorem singletonEqualityBinding_canonicallyPrincipal
    {left right : String} (hne : left ≠ right) :
    CanonicallyPrincipal [Metta.BindingRel.eq left right] := by
  let identity : String → Metta.Atom := fun name => .var name
  let general := Function.update identity left (.var right)
  have hcanonical :
      leaClassSolution [Metta.BindingRel.eq left right] = general := by
    funext name
    by_cases hleft : name = left
    · subst name
      simp [leaClassSolution, general, identity, Metta.Bindings.resolve,
        Metta.Bindings.resolveAtomAux, Metta.Bindings.resolutionFuel,
        Metta.Bindings.relationResolutionFuel,
        Metta.Bindings.eqRepresentative, Metta.Bindings.eqClassOrdered,
        Metta.Bindings.classValues, Metta.Bindings.lookupVal,
        Metta.Bindings.eqVarsInOrder, Metta.Bindings.eqClass,
        Metta.Bindings.eqClassAux, Metta.Bindings.eqStep, hne, Ne.symm hne]
    · by_cases hright : name = right
      · subst name
        simp [leaClassSolution, general, identity, Metta.Bindings.resolve,
          Metta.Bindings.resolveAtomAux, Metta.Bindings.resolutionFuel,
          Metta.Bindings.relationResolutionFuel,
          Metta.Bindings.eqRepresentative, Metta.Bindings.eqClassOrdered,
          Metta.Bindings.classValues, Metta.Bindings.lookupVal,
          Metta.Bindings.eqVarsInOrder, Metta.Bindings.eqClass,
          Metta.Bindings.eqClassAux, Metta.Bindings.eqStep, hne, Ne.symm hne]
      · have hclass : Metta.Bindings.eqClassOrdered
            [Metta.BindingRel.eq left right] name = [name] := by
          have hleft' : left ≠ name := Ne.symm hleft
          have hright' : right ≠ name := Ne.symm hright
          have horder : Metta.Bindings.eqVarsInOrder
              [Metta.BindingRel.eq left right] = [right, left] := by
            simp [Metta.Bindings.eqVarsInOrder, hne]
          have hraw : Metta.Bindings.eqClass
              [Metta.BindingRel.eq left right] name = [name] := by
            simp [Metta.Bindings.eqClass, Metta.Bindings.eqClassAux,
              Metta.Bindings.eqStep, hleft', hright']
          simp [Metta.Bindings.eqClassOrdered, horder, hraw,
            hleft', hright']
        have hvalues : Metta.Bindings.classValues
            [Metta.BindingRel.eq left right] name = [] := by
          simp [Metta.Bindings.classValues, Metta.Bindings.lookupVal]
        simp [leaClassSolution, general, identity, hleft,
          Metta.Bindings.resolve, hclass, hvalues]
  unfold CanonicallyPrincipal LeaCanonicalSolutionInvariant
  rw [hcanonical]
  constructor
  · constructor
    · intro key value hmem
      simp at hmem
    · intro storedLeft storedRight hmem
      simp only [List.mem_singleton, Metta.BindingRel.eq.injEq] at hmem
      rcases hmem with ⟨rfl, rfl⟩
      simp [general, identity, Function.update]
  · intro specific hspecific
    refine ⟨specific, fun name => ?_⟩
    by_cases hname : name = left
    · subst name
      have hedge := hspecific.2 left right (by simp)
      simpa [general, Function.update, applyClassSolution] using hedge
    · simp [general, identity, hname, applyClassSolution]

/-- Pointwise matching preserves the conditional canonical accumulator
invariant.  Child matches are loop-filtered public matcher outputs, so their
host-float-free shape can be reused directly; principality is threaded only
through the merge accumulator that survives to the final result. -/
private theorem leaMatchAll_canonicallyPrincipal
    (lefts : List Metta.Atom) :
    ∀ {rights : List Metta.Atom} {seeds : List Metta.Bindings}
      {out : Metta.Bindings},
      (∀ left ∈ lefts, MettaAtomNoFloat left) →
      (∀ right ∈ rights, MettaAtomNoFloat right) →
      (∀ seed ∈ seeds, seed.hasLoop = false →
        CanonicallyPrincipal seed) →
      (∀ seed ∈ seeds, LeaBindingsNoFloat seed) →
      (∀ seed ∈ seeds, LeaAssignmentsNonVariable seed) →
      (∀ seed ∈ seeds, LeaEqualitiesIrreflexive seed) →
      out ∈ Metta.matchAll none seeds lefts rights →
      out.hasLoop = false →
      CanonicallyPrincipal out := by
  induction lefts with
  | nil =>
      intro rights seeds out _hlefts hrights hseedsCanonical
        _hseedsNoFloat _hseedsNonvariable _hseedsIrreflexive
        hout houtLoop
      cases rights with
      | nil =>
          simp only [Metta.matchAll] at hout
          exact hseedsCanonical out hout houtLoop
      | cons right rights =>
          simp [Metta.matchAll] at hout
  | cons left lefts ih =>
      intro rights seeds out hlefts hrights hseedsCanonical
        hseedsNoFloat hseedsNonvariable hseedsIrreflexive
        hout houtLoop
      cases rights with
      | nil =>
          simp [Metta.matchAll] at hout
      | cons right rights =>
          let subs := (Metta.matchAtomsWith none left right).filter
            (fun bindings => !bindings.hasLoop)
          let next := seeds.flatMap fun seed =>
            subs.flatMap fun matched => Metta.Bindings.merge seed matched
          have houtTail :
              out ∈ Metta.matchAll none next lefts rights := by
            simpa [Metta.matchAll, subs, next] using hout
          have hleftNoFloat : MettaAtomNoFloat left :=
            hlefts left List.mem_cons_self
          have hrightNoFloat : MettaAtomNoFloat right :=
            hrights right List.mem_cons_self
          have hleftsNoFloat : ∀ atom ∈ lefts,
              MettaAtomNoFloat atom := by
            intro atom hmem
            exact hlefts atom (List.mem_cons_of_mem left hmem)
          have hrightsNoFloat : ∀ atom ∈ rights,
              MettaAtomNoFloat atom := by
            intro atom hmem
            exact hrights atom (List.mem_cons_of_mem right hmem)
          have hnextDecompose : ∀ candidate ∈ next,
              ∃ seed matched,
                seed ∈ seeds ∧
                  matched ∈ Metta.matchAtoms left right ∧
                    candidate ∈ Metta.Bindings.merge seed matched := by
            intro candidate hcandidate
            have hdecompose : ∃ seed ∈ seeds, ∃ matched ∈ subs,
                candidate ∈ Metta.Bindings.merge seed matched := by
              simpa [next] using hcandidate
            obtain ⟨seed, hseed, matched, hmatched, hmerge⟩ := hdecompose
            refine ⟨seed, matched, hseed, ?_, hmerge⟩
            simpa [subs, Metta.matchAtoms] using hmatched
          have hnextCanonical : ∀ candidate ∈ next,
              candidate.hasLoop = false →
                CanonicallyPrincipal candidate := by
            intro candidate hcandidate hcandidateLoop
            obtain ⟨seed, matched, hseed, hmatched, hmerge⟩ :=
              hnextDecompose candidate hcandidate
            have hmatchedNoFloat : LeaBindingsNoFloat matched :=
              leaMatchAtoms_result_noFloat
                hleftNoFloat hrightNoFloat hmatched
            exact leaMerge_canonicallyPrincipal_of_loop
              (hseedsCanonical seed hseed)
              (hseedsNoFloat seed hseed)
              (hseedsNonvariable seed hseed)
              (hseedsIrreflexive seed hseed)
              hmatchedNoFloat hmerge hcandidateLoop
          have hnextNoFloat : ∀ candidate ∈ next,
              LeaBindingsNoFloat candidate := by
            intro candidate hcandidate
            obtain ⟨seed, matched, hseed, hmatched, hmerge⟩ :=
              hnextDecompose candidate hcandidate
            exact leaMerge_result_noFloat
              (hseedsNoFloat seed hseed)
              (leaMatchAtoms_result_noFloat
                hleftNoFloat hrightNoFloat hmatched)
              hmerge
          have hnextNonvariable : ∀ candidate ∈ next,
              LeaAssignmentsNonVariable candidate := by
            intro candidate hcandidate
            obtain ⟨seed, matched, hseed, _hmatched, hmerge⟩ :=
              hnextDecompose candidate hcandidate
            exact leaMerge_result_assignmentsNonVariable
              (hseedsNonvariable seed hseed) hmerge
          have hnextIrreflexive : ∀ candidate ∈ next,
              LeaEqualitiesIrreflexive candidate := by
            intro candidate hcandidate
            obtain ⟨seed, matched, hseed, _hmatched, hmerge⟩ :=
              hnextDecompose candidate hcandidate
            exact leaMerge_result_equalitiesIrreflexive
              (hseedsIrreflexive seed hseed) hmerge
          exact ih hleftsNoFloat hrightsNoFloat hnextCanonical
            hnextNoFloat hnextNonvariable hnextIrreflexive
            houtTail houtLoop

/-- Every non-expression raw LeaTTa match output has a principal model
directly.  This is the leaf base for the public-output semantic induction; it
does not invoke another matcher or a declarative match relation. -/
private theorem leaMatchAtomsWith_leaf_canonicallyPrincipal
    {left right : Metta.Atom} {out : Metta.Bindings}
    (hleftNoFloat : MettaAtomNoFloat left)
    (hrightNoFloat : MettaAtomNoFloat right)
    (hout : out ∈ Metta.matchAtomsWith none left right)
    (hleaf : ¬∃ lefts rights,
      left = .expr lefts ∧ right = .expr rights) :
    CanonicallyPrincipal out := by
  cases left with
  | sym symbol =>
      cases right with
      | sym other =>
          by_cases heq : symbol = other
          · subst other
            simp [Metta.matchAtomsWith] at hout
            subst out
            exact emptyBindings_canonicallyPrincipal
          · simp [Metta.matchAtomsWith, heq] at hout
      | var key =>
          simp [Metta.matchAtomsWith] at hout
          subst out
          exact singletonValueBinding_canonicallyPrincipal (by
            simp)
      | gnd grounded =>
          simp [Metta.matchAtomsWith, Metta.Atom.equiv] at hout
      | expr atoms =>
          simp [Metta.matchAtomsWith, Metta.Atom.equiv] at hout
  | var key =>
      cases right with
      | sym symbol =>
          simp [Metta.matchAtomsWith] at hout
          subst out
          exact singletonValueBinding_canonicallyPrincipal (by
            simp)
      | var other =>
          by_cases heq : key = other
          · subst other
            simp [Metta.matchAtomsWith] at hout
            subst out
            exact emptyBindings_canonicallyPrincipal
          · have hbeq : (key == other) = false := by simp [heq]
            simp [Metta.matchAtomsWith, hbeq] at hout
            subst out
            exact singletonEqualityBinding_canonicallyPrincipal heq
      | gnd grounded =>
          simp [Metta.matchAtomsWith] at hout
          subst out
          exact singletonValueBinding_canonicallyPrincipal (by
            simp)
      | expr atoms =>
          cases hoccurs : Metta.Subst.occurs key (.expr atoms) with
          | true => simp [Metta.matchAtomsWith, hoccurs] at hout
          | false =>
              simp [Metta.matchAtomsWith, hoccurs] at hout
              subst out
              exact singletonValueBinding_canonicallyPrincipal hoccurs
  | gnd grounded =>
      cases right with
      | sym symbol =>
          simp [Metta.matchAtomsWith, Metta.Atom.equiv] at hout
      | var key =>
          simp [Metta.matchAtomsWith] at hout
          subst out
          exact singletonValueBinding_canonicallyPrincipal (by
            simp)
      | gnd other =>
          cases hequiv : Metta.Ground.equiv grounded other with
          | false =>
              simp [Metta.matchAtomsWith, Metta.Atom.equiv, hequiv] at hout
          | true =>
              simp [Metta.matchAtomsWith, Metta.Atom.equiv, hequiv] at hout
              subst out
              exact emptyBindings_canonicallyPrincipal
      | expr atoms =>
          simp [Metta.matchAtomsWith, Metta.Atom.equiv] at hout
  | expr atoms =>
      cases right with
      | sym symbol =>
          simp [Metta.matchAtomsWith, Metta.Atom.equiv] at hout
      | var key =>
          cases hoccurs : Metta.Subst.occurs key (.expr atoms) with
          | true => simp [Metta.matchAtomsWith, hoccurs] at hout
          | false =>
              simp [Metta.matchAtomsWith, hoccurs] at hout
              subst out
              exact singletonValueBinding_canonicallyPrincipal hoccurs
      | gnd grounded =>
          simp [Metta.matchAtomsWith, Metta.Atom.equiv] at hout
      | expr rights =>
          exact (hleaf ⟨atoms, rights, rfl, rfl⟩).elim

/-- Every loop-free raw default matcher output is canonically principal.  The
only recursive case delegates to the conditional `matchAll` accumulator
invariant; every other constructor pair is the sealed leaf theorem. -/
private theorem leaMatchAtomsWith_canonicallyPrincipal
    {left right : Metta.Atom} {out : Metta.Bindings}
    (hleftNoFloat : MettaAtomNoFloat left)
    (hrightNoFloat : MettaAtomNoFloat right)
    (hout : out ∈ Metta.matchAtomsWith none left right)
    (houtLoop : out.hasLoop = false) :
    CanonicallyPrincipal out := by
  by_cases hexpr : ∃ lefts rights,
      left = .expr lefts ∧ right = .expr rights
  · obtain ⟨lefts, rights, rfl, rfl⟩ := hexpr
    apply leaMatchAll_canonicallyPrincipal lefts
      (rights := rights) (seeds := [[]]) (out := out)
    · simpa only [MettaAtomNoFloat] using hleftNoFloat
    · simpa only [MettaAtomNoFloat] using hrightNoFloat
    · intro seed hseed _hseedLoop
      simp only [List.mem_singleton] at hseed
      subst seed
      exact emptyBindings_canonicallyPrincipal
    · intro seed hseed
      simp only [List.mem_singleton] at hseed
      subst seed
      simp [LeaBindingsNoFloat]
    · intro seed hseed
      simp only [List.mem_singleton] at hseed
      subst seed
      exact leaAssignmentsNonVariable_empty
    · intro seed hseed
      simp only [List.mem_singleton] at hseed
      subst seed
      exact leaEqualitiesIrreflexive_empty
    · simpa [Metta.matchAtomsWith] using hout
    · exact houtLoop
  · exact leaMatchAtomsWith_leaf_canonicallyPrincipal
      hleftNoFloat hrightNoFloat hout hexpr

/-- Existential projection of canonical principality for arbitrary raw
default matcher outputs that survive the complete loop check. -/
private theorem leaMatchAtomsWith_satisfiable
    {left right : Metta.Atom} {out : Metta.Bindings}
    (hleftNoFloat : MettaAtomNoFloat left)
    (hrightNoFloat : MettaAtomNoFloat right)
    (hout : out ∈ Metta.matchAtomsWith none left right)
    (houtLoop : out.hasLoop = false) :
    ∃ valuation : String → Metta.Atom,
      LeaBindingSatisfied valuation out := by
  have hcanonical := leaMatchAtomsWith_canonicallyPrincipal
    hleftNoFloat hrightNoFloat hout houtLoop
  exact ⟨leaClassSolution out, hcanonical.1⟩

/-- Existential projection of the principal leaf theorem. -/
private theorem leaMatchAtomsWith_leaf_satisfiable
    {left right : Metta.Atom} {out : Metta.Bindings}
    (hleftNoFloat : MettaAtomNoFloat left)
    (hrightNoFloat : MettaAtomNoFloat right)
    (hout : out ∈ Metta.matchAtomsWith none left right)
    (hleaf : ¬∃ lefts rights,
      left = .expr lefts ∧ right = .expr rights) :
    ∃ valuation : String → Metta.Atom,
      LeaBindingSatisfied valuation out := by
  have hcanonical := leaMatchAtomsWith_leaf_canonicallyPrincipal
    hleftNoFloat hrightNoFloat hout hleaf
  exact ⟨leaClassSolution out, hcanonical.1⟩

/-- Every public repaired-LeaTTa match outside the expression/expression case
has an inhabited binding solution theory.  The public membership supplies the
raw matcher witness; the loop filter needs no additional semantic premise in
this direction. -/
theorem leaMatchAtoms_leaf_output_satisfiable
    {left right : Metta.Atom} {out : Metta.Bindings}
    (hleftNoFloat : MettaAtomNoFloat left)
    (hrightNoFloat : MettaAtomNoFloat right)
    (hout : out ∈ Metta.matchAtoms left right)
    (hleaf : ¬∃ lefts rights,
      left = .expr lefts ∧ right = .expr rights) :
    ∃ valuation : String → Metta.Atom,
      LeaBindingSatisfied valuation out := by
  have hraw : out ∈ Metta.matchAtomsWith none left right :=
    ((by simpa [Metta.matchAtoms] using hout) :
      out ∈ Metta.matchAtomsWith none left right ∧
        out.hasLoop = false).1
  exact leaMatchAtomsWith_leaf_satisfiable
    hleftNoFloat hrightNoFloat hraw hleaf

/-- **Repaired-LeaTTa output satisfiability.**  Every public default matcher
output on the HE-translatable fragment has an explicit canonical model.  The
public membership supplies both the raw recursive output and the complete
whole-binding loop check used by the conditional accumulator induction. -/
theorem leaMatchAtoms_output_satisfiable
    {left right : Metta.Atom} {out : Metta.Bindings}
    (hleftNoFloat : MettaAtomNoFloat left)
    (hrightNoFloat : MettaAtomNoFloat right)
    (hout : out ∈ Metta.matchAtoms left right) :
    ∃ valuation : String → Metta.Atom,
      LeaBindingSatisfied valuation out := by
  have hraw : out ∈ Metta.matchAtomsWith none left right ∧
      out.hasLoop = false := by
    simpa [Metta.matchAtoms] using hout
  exact leaMatchAtomsWith_satisfiable
    hleftNoFloat hrightNoFloat hraw.1 hraw.2

/-- A satisfiable repaired-LeaTTa matcher output has a matching derivation in
the executable-independent human specification with the same complete binding
solution theory. -/
theorem leaMatch_observational_sound_of_satisfiable
    {query pattern : Atom} {leaOut : Metta.Bindings}
    (hlea : leaOut ∈ Metta.matchAtoms
      (toLeaTTaAtom pattern) (toLeaTTaAtom query))
    (hsatisfiable : ∃ valuation : String → Metta.Atom,
      LeaBindingSatisfied valuation leaOut) :
    ∃ humanOut,
      HumanMatchMergeSpec.MatchRel
          HumanMatchMergeSpec.equalityGroundedSemantic
          query pattern humanOut ∧
        LeaBindingSolutionTheoryEquiv humanOut leaOut := by
  obtain ⟨valuation, hleaSatisfied⟩ := hsatisfiable
  have hmettaEquation : MettaEquationSatisfied valuation
      (toLeaTTaAtom pattern, toLeaTTaAtom query) :=
    (leaMatchAtoms_solution_iff valuation
      (toLeaTTaAtom_noFloat pattern)
      (toLeaTTaAtom_noFloat query) hlea).mp hleaSatisfied
  have hhumanEquation : HEAtomEquationSatisfied valuation query pattern := by
    simpa [HEAtomEquationSatisfied, MettaEquationSatisfied] using
      hmettaEquation.symm
  obtain ⟨humanOut, hhuman, _hhumanSatisfied⟩ :=
    HumanMatchCompleteness.exists_humanMatch_of_solution hhumanEquation
  exact ⟨humanOut, hhuman,
    HumanMatchSolutionTheory.humanMatch_leaMatch_solutionTheoryEquiv
      hhuman hlea⟩

/-- **Direct repaired-LeaTTa observational soundness.**  Every executable
default matcher output for translated human atoms has a derivation in the
executable-independent human specification and presents exactly the same
complete binding solution theory. -/
theorem leaMatch_observational_sound
    {query pattern : Atom} {leaOut : Metta.Bindings}
    (hlea : leaOut ∈ Metta.matchAtoms
      (toLeaTTaAtom pattern) (toLeaTTaAtom query)) :
    ∃ humanOut,
      HumanMatchMergeSpec.MatchRel
          HumanMatchMergeSpec.equalityGroundedSemantic
          query pattern humanOut ∧
        LeaBindingSolutionTheoryEquiv humanOut leaOut := by
  apply leaMatch_observational_sound_of_satisfiable hlea
  exact leaMatchAtoms_output_satisfiable
    (toLeaTTaAtom_noFloat pattern)
    (toLeaTTaAtom_noFloat query) hlea

/-- **Repaired-LeaTTa ↔ human-spec observational conformance seal.**  The
first projection is direct soundness of every public LeaTTa output.  The
second projection is direct completeness of every human derivation under the
variable-disjointness established by rule freshening.  Both directions use
the same complete binding solution-theory equivalence. -/
theorem humanLeaMatch_observational_conformance
    (query pattern : Atom) :
    (∀ {leaOut : Metta.Bindings},
      leaOut ∈ Metta.matchAtoms
          (toLeaTTaAtom pattern) (toLeaTTaAtom query) →
        ∃ humanOut,
          HumanMatchMergeSpec.MatchRel
              HumanMatchMergeSpec.equalityGroundedSemantic
              query pattern humanOut ∧
            LeaBindingSolutionTheoryEquiv humanOut leaOut) ∧
    (∀ {humanOut : Bindings},
      HumanMatchMergeSpec.MatchRel
          HumanMatchMergeSpec.equalityGroundedSemantic
          query pattern humanOut →
        VarsDisjoint query pattern →
          ∃ leaOut,
            leaOut ∈ Metta.matchAtoms
                (toLeaTTaAtom pattern) (toLeaTTaAtom query) ∧
              LeaBindingSolutionTheoryEquiv humanOut leaOut) := by
  constructor
  · intro leaOut hlea
    exact leaMatch_observational_sound hlea
  · intro humanOut hhuman hdisjoint
    exact humanMatch_observational_complete hhuman hdisjoint

/-- Direct observational soundness is unconditional for every translated
human atom pair outside expression/expression matching. -/
theorem leaMatch_observational_sound_leaf
    {query pattern : Atom} {leaOut : Metta.Bindings}
    (hlea : leaOut ∈ Metta.matchAtoms
      (toLeaTTaAtom pattern) (toLeaTTaAtom query))
    (_hleaf : ¬∃ patterns queries,
      toLeaTTaAtom pattern = .expr patterns ∧
        toLeaTTaAtom query = .expr queries) :
    ∃ humanOut,
      HumanMatchMergeSpec.MatchRel
          HumanMatchMergeSpec.equalityGroundedSemantic
          query pattern humanOut ∧
        LeaBindingSolutionTheoryEquiv humanOut leaOut := by
  exact leaMatch_observational_sound hlea

end Mettapedia.Languages.MeTTa.HE.LeaTTaHumanConformance
