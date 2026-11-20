import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.ReflQuotientFrame
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.FiniteComm
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.TranslationFrames

/-!
# The finite COMM hosting, transported to the frame modulo the bag laws

`ReflQuotientFrame` gives the quotient frame `QX`: the one frame of structural substitution on patterns,
compared modulo the bag laws. Here the finite program of `FiniteComm` runs at it.

## The arrow from the syntactic frame

* `quotientMap`: the identity is a map of frame instances (`Translation.FrameMap`) from the syntactic frame
  `X` to `QX`: the action commutes exactly and syntactic equality is equality modulo the bag laws. It does not
  reflect the equality (`quotientMap_not_reflects`).
* `quotient_admits`: for every rule without checks and collect query, an admitted firing at `X` is admitted at `QX`,
  with the same result. Every rule of the finite program is such a rule (`program_quotient_admits`): the
  transitions of the syntactic step are transitions of the quotient step, a functional simulation. The
  hypothesis excludes checks and collect query: a none check asks that no row be equal to a pattern, and `QX`
  equates more terms than `X`.

## COMM at the quotient frame

At `QX` a solution identifies terms modulo the bag laws, so the patterns of a redex are unified modulo the
bag laws. The corrected semantics compares names as written, and its canonical order is exact for ground
names only. The named hypothesis here is that the written ground names are canonical: every parallel bag of
the two patterns is ground (`groundBags`) and the patterns are canonical (`bagCanon t = t`). On such patterns canonicalizing commutes with
substitution (`bagCanon_psubst_of_groundBags`), so a solution modulo the bag laws, read canonically, is a
syntactic unifier (`canonSubst_unifies`), and the ground principal unifier determines every pattern variable
modulo the bag laws (`agrees_of_groundPrincipal`).

* `comm_admits_bag`, `comm_reads_bag`: admission and the read-off at `QX`, for rows of any input shape read
  modulo the bag laws.
* `comm_one_firing_bag`: the analogue of `FiniteProgram.comm_one_firing` at `QX`: the firing is admitted, the
  manuscript's COMM relates the redex to its dotted reduct (as written and in the corrected semantics), and
  every solution reads the made rows as the representations of the dotted continuations, modulo the bag laws.
  With closed continuations they read as the dotted continuations themselves (`comm_one_firing_closed_bag`).
* `comm_one_transition_bag`: a fresh opening exists, and the transition reaches a state with the made rows,
  a solvable knowledge, and that read-off.

What separates `QX` from the corrected semantics outside the hypothesis is in `ReflQuotientControls`.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.ReflQuotient

open Mettapedia.OSLF.MeTTaIL.Syntax (Pattern CollType)
open Mettapedia.OSLF.MeTTaIL.Match (Bindings)
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus (pFor par pZero nQuote applyDot SC pPar)
open MeTTaOperationsComm (psubst pcomp psubst_comp psubst_none psubst_of_pvars_nil pvars patternAction PSubst
  quoteOn dotted commSelection GroundPrincipal applyDot_eq psubst_nQuote psubst_pFor firstOrder
  lookup_eq_none_of_keys)
open MeTTaCalculus.Corrected (psubst_getD_congr_on binders Apart psubstList_eq_map pvars_apply pvarsList_eq_flatMap
  components pvars_of_mem_components codeOrder codeOrder_perm mem_pvars_apply_of mem_pvars_collection_of)
open FiniteProgram (predot predot_pFor predot_psubst GroundValued mem_keys_of_lookup mem_pvars_predot commAt
  commRule commRule_mem program mem_program commInstance commInstance_firstPattern commInstance_secondPattern
  commInstance_channel commInstance_firstBody commInstance_secondBody firstPattern secondPattern channelUnknown
  firstBody secondBody keys_of_apart exists_fresh_opening)
open MeTTaCalculus.OccurrenceCommits (fire)
open Comm (X E)
open OneFrame (embed)
open LogicOverTheStep.StepSpan (Succ)
open MeTTaCalculus.Corrected.BagControls (atomA atomB)

/-! ## The arrow from the syntactic frame -/

/-- **The identity, from the syntactic frame to the quotient frame**: a map of frame instances. -/
def quotientMap : Interface.Translation.FrameMap X QX where
  obj a := a
  tm t := t
  hom f := f
  act _ _ := BagLaws.refl _
  preserves same := bagLaws_of_eq same

theorem quotientMap_store (K : EquationStore Pattern) : quotientMap.store (a := PUnit.unit) K = K := by
  simp [Interface.Translation.FrameMap.store, quotientMap]

/-- The arrow does not reflect the equality: `a | b` and `b | a` are equal modulo the bag laws only. -/
theorem quotientMap_not_reflects : ¬ quotientMap.Reflects := by
  intro reflects
  have same : par atomA atomB = par atomB atomA :=
    reflects (a := PUnit.unit) (s := par atomA atomB) (t := par atomB atomA) (bagLaws_par_comm _ _)
  exact absurd same (by decide +kernel)

variable {O : Type*}

/-- A firing of a program at the syntactic frame, read at the quotient frame: the same rule, opening,
selection and seen sets. -/
def quotientFiring {P : Program (OneFrame.Terms Pattern)} (f : Firing O E P PUnit.unit) :
    Firing O QE P PUnit.unit :=
  ⟨f.rule, f.member, PUnit.unit, f.opening, f.selection, f.seen⟩

/-- A fresh opening at the syntactic frame is fresh at the quotient frame. -/
theorem fresh_quotient {label : O → Pattern} {C : Configuration Pattern O} {P : Program (OneFrame.Terms Pattern)}
    {f : Firing O E P PUnit.unit} (fresh : f.Fresh X (embed label C)) :
    (quotientFiring f).Fresh QX (embed label C) := by
  intro b g h
  obtain ⟨u, onState, onRule⟩ := fresh b g h
  exact ⟨u, fun t mentions => bagLaws_of_eq (onState t mentions), fun t member => bagLaws_of_eq (onRule t member)⟩

variable [DecidableEq O]

/-- **Admission is carried to the quotient frame** for a rule without checks and collect query, with the same
result. -/
theorem quotient_admits {P : Program (OneFrame.Terms Pattern)} (label : O → Pattern) (C : Configuration Pattern O)
    (f : Firing O E P PUnit.unit) (noChecks : f.rule.body.checks = []) (noCollect : f.rule.collect = [])
    (admitted : (RuleSyntax.step X O E P).Admits (s := embed label C) f) :
    (RuleSyntax.step QX O QE P).Admits (s := embed label C) (quotientFiring f) ∧
      (quotientFiring f).result QX (embed label C) = f.result X (embed label C) := by
  obtain ⟨fresh, shapes, enabled, solvable, -, -⟩ := (RuleSyntax.admits_iff f).mp admitted
  have solvableQ := quotientMap.solvable solvable
  rw [quotientMap_store] at solvableQ
  refine ⟨(RuleSyntax.admits_iff _).mpr ⟨fresh_quotient fresh, shapes, enabled, solvableQ, ?_, ?_⟩, rfl⟩
  · intro c member
    simp [Firing.opened, RuleInstance.map, quotientFiring, noChecks] at member
  · intro q member
    simp [Firing.collectOpened, quotientFiring, noCollect] at member

theorem program_rules_plain {r : Rule (OneFrame.Terms Pattern)} (member : r ∈ program) :
    r.body.checks = [] ∧ r.collect = [] := by
  rcases mem_program.mp member with rfl | rfl | rfl <;> exact ⟨rfl, rfl⟩

/-- **Every transition of the finite program at the syntactic frame is one at the quotient frame**, with the
same result: a functional simulation of the steps. -/
theorem program_quotient_admits (label : O → Pattern) (C : Configuration Pattern O)
    (f : Firing O E program PUnit.unit) (admitted : (RuleSyntax.step X O E program).Admits (s := embed label C) f) :
    (RuleSyntax.step QX O QE program).Admits (s := embed label C) (quotientFiring f) ∧
      (quotientFiring f).result QX (embed label C) = f.result X (embed label C) :=
  quotient_admits label C f (program_rules_plain f.member).1 (program_rules_plain f.member).2 admitted

/-! ## Ground canonical bags -/

mutual
/-- Every parallel bag in the term is ground. -/
def groundBags : Pattern → Bool
  | .bvar _ => true
  | .fvar _ => true
  | .apply _ args => groundBagsList args
  | .lambda _ body => groundBags body
  | .multiLambda _ _ body => groundBags body
  | .subst body repl => groundBags body && groundBags repl
  | .collection ct elems rest =>
      (if ct = .hashBag ∧ rest = none then (pvars.pvarsList elems).isEmpty else true) && groundBagsList elems
/-- Every parallel bag in every term of the list is ground. -/
def groundBagsList : List Pattern → Bool
  | [] => true
  | p :: ps => groundBags p && groundBagsList ps
end

theorem groundBagsList_iff (ps : List Pattern) : groundBagsList ps = true ↔ ∀ p ∈ ps, groundBags p = true := by
  induction ps with
  | nil => simp [groundBagsList]
  | cons p ps ih => simp [groundBagsList, ih]

theorem pvars_bagOf {L : List Pattern} {x : String} (occurs : x ∈ pvars (bagOf L)) : ∃ c ∈ L, x ∈ pvars c := by
  match L, occurs with
  | [], occurs => simp [bagOf, pZero, pvars, pvars.pvarsList] at occurs
  | [c], occurs => exact ⟨c, List.mem_cons_self, occurs⟩
  | c :: d :: cs, occurs =>
      simp only [bagOf, pPar, pvars, pvarsList_eq_flatMap, List.mem_flatMap] at occurs
      exact occurs

/-- **Canonicalizing adds no variable.** -/
theorem mem_pvars_bagCanon {p : Pattern} {x : String} (occurs : x ∈ pvars (bagCanon p)) : x ∈ pvars p := by
  revert occurs
  induction p using Pattern.rec (motive_2 := fun ps => ∀ q ∈ ps, x ∈ pvars (bagCanon q) → x ∈ pvars q) with
  | bvar n => exact id
  | fvar y => exact id
  | apply c args ih =>
      intro occurs
      rw [bagCanon_apply, pvars_apply, pvarsList_eq_flatMap] at occurs
      obtain ⟨q', inMap, inQ⟩ := List.mem_flatMap.mp occurs
      obtain ⟨q, member, rfl⟩ := List.mem_map.mp inMap
      exact mem_pvars_apply_of member (ih q member inQ)
  | lambda nm body ih =>
      intro occurs
      simp only [bagCanon, pvars] at occurs ⊢
      exact ih occurs
  | multiLambda n nms body ih =>
      intro occurs
      simp only [bagCanon, pvars] at occurs ⊢
      exact ih occurs
  | subst body repl ihb ihr =>
      intro occurs
      simp only [bagCanon, pvars, List.mem_append] at occurs ⊢
      rcases occurs with inBody | inRepl
      · exact .inl (ihb inBody)
      · exact .inr (ihr inRepl)
  | collection ct elems rest ih =>
      intro occurs
      rw [bagCanon_collection] at occurs
      unfold bagNode at occurs
      split_ifs at occurs with bag
      · obtain ⟨c, inSorted, inC⟩ := pvars_bagOf occurs
        obtain ⟨q', inMap, inComps⟩ := List.mem_flatMap.mp ((codeOrder_perm _).subset inSorted)
        obtain ⟨q, member, rfl⟩ := List.mem_map.mp inMap
        exact mem_pvars_collection_of member (ih q member (pvars_of_mem_components inComps inC))
      · simp only [pvars, pvarsList_eq_flatMap, List.mem_flatMap] at occurs
        obtain ⟨q', inMap, inQ⟩ := occurs
        obtain ⟨q, member, rfl⟩ := List.mem_map.mp inMap
        exact mem_pvars_collection_of member (ih q member inQ)
  | nil => simp_all
  | cons p ps head tail =>
      rename_i q member inQ
      rcases List.mem_cons.mp member with rfl | later
      · exact head inQ
      · exact tail q later inQ

theorem pvars_bagCanon_nil {p : Pattern} (closed : pvars p = []) : pvars (bagCanon p) = [] :=
  List.eq_nil_iff_forall_not_mem.mpr fun x occurs => by
    have inP := mem_pvars_bagCanon occurs
    rw [closed] at inP
    exact List.not_mem_nil inP

/-- The canonical forms of a substitution's values. -/
def canonSubst (σ : PSubst) : PSubst := fun x => (σ x).map bagCanon

/-- **On terms whose parallel bags are ground, canonicalizing commutes with substitution**, the values read
canonically. -/
theorem bagCanon_psubst_of_groundBags (σ : PSubst) (p : Pattern) (ground : groundBags p = true) :
    bagCanon (psubst σ p) = psubst (canonSubst σ) (bagCanon p) := by
  revert ground
  induction p using Pattern.rec (motive_2 := fun ps => ∀ q ∈ ps, groundBags q = true →
      bagCanon (psubst σ q) = psubst (canonSubst σ) (bagCanon q)) with
  | bvar n => intro _; rfl
  | fvar x =>
      intro _
      show bagCanon ((σ x).getD (.fvar x)) = (canonSubst σ x).getD (.fvar x)
      cases found : σ x with
      | some v => simp [canonSubst, found]
      | none => simp [canonSubst, found, bagCanon]
  | apply c args ih =>
      intro ground
      simp only [groundBags, groundBagsList_iff] at ground
      simp only [psubst, psubstList_eq_map, bagCanon_apply, List.map_map]
      exact congrArg _ (List.map_congr_left fun q member => ih q member (ground q member))
  | lambda nm body ih =>
      intro ground
      simp only [groundBags] at ground
      simp only [psubst, bagCanon, ih ground]
  | multiLambda n nms body ih =>
      intro ground
      simp only [groundBags] at ground
      simp only [psubst, bagCanon, ih ground]
  | subst body repl ihb ihr =>
      intro ground
      simp only [groundBags, Bool.and_eq_true] at ground
      simp only [psubst, bagCanon, ihb ground.1, ihr ground.2]
  | collection ct elems rest ih =>
      intro ground
      by_cases bag : ct = .hashBag ∧ rest = none
      · obtain ⟨rfl, rfl⟩ := bag
        have flat : pvars.pvarsList elems = [] ∧ groundBagsList elems = true := by
          simpa [groundBags] using ground
        have closed : pvars (.collection .hashBag elems none) = [] := by
          simp only [pvars]
          exact flat.1
        rw [psubst_of_pvars_nil σ _ closed, psubst_of_pvars_nil _ _ (pvars_bagCanon_nil closed)]
      · simp only [groundBags, Bool.and_eq_true, groundBagsList_iff] at ground
        simp only [psubst, psubstList_eq_map, bagCanon_collection]
        unfold bagNode
        rw [if_neg bag, if_neg bag]
        simp only [psubst, psubstList_eq_map, List.map_map]
        exact congrArg (fun L => Pattern.collection ct L rest)
          (List.map_congr_left fun q member => ih q member (ground.2 q member))
  | nil => simp_all
  | cons p ps head tail =>
      rename_i q member groundQ
      rcases List.mem_cons.mp member with rfl | later
      · exact head groundQ
      · exact tail q later groundQ

/-- **A solution modulo the bag laws, read canonically, is a syntactic unifier** of patterns whose bags are
ground and which are canonical. -/
theorem canonSubst_unifies {t u : Pattern} (groundT : groundBags t = true) (groundU : groundBags u = true)
    (canonicalT : bagCanon t = t) (canonicalU : bagCanon u = u) {σ : PSubst}
    (equal : BagLaws (psubst σ t) (psubst σ u)) : psubst (canonSubst σ) t = psubst (canonSubst σ) u := by
  have same := bagCanon_eq_of_bagLaws equal
  rw [bagCanon_psubst_of_groundBags σ t groundT, bagCanon_psubst_of_groundBags σ u groundU, canonicalT,
    canonicalU] at same
  exact same

/-! ## Substitutions related value by value -/

theorem forall₂_map_map {f g : Pattern → Pattern} :
    ∀ {xs : List Pattern}, (∀ q ∈ xs, BagLaws (f q) (g q)) → List.Forall₂ BagLaws (xs.map f) (xs.map g)
  | [], _ => .nil
  | x :: _, h => .cons (h x List.mem_cons_self)
      (forall₂_map_map fun q member => h q (List.mem_cons_of_mem _ member))

/-- **Substitutions whose values are related modulo the bag laws give related instances.** -/
theorem psubst_bagLaws_congr {σ τ : PSubst} (p : Pattern)
    (agree : ∀ x ∈ pvars p, BagLaws ((σ x).getD (.fvar x)) ((τ x).getD (.fvar x))) :
    BagLaws (psubst σ p) (psubst τ p) := by
  revert agree
  induction p using Pattern.rec (motive_2 := fun ps => ∀ q ∈ ps,
      (∀ x ∈ pvars q, BagLaws ((σ x).getD (.fvar x)) ((τ x).getD (.fvar x))) →
        BagLaws (psubst σ q) (psubst τ q)) with
  | bvar n => intro _; exact BagLaws.refl _
  | fvar x => intro agree; exact agree x (by simp [pvars])
  | apply c args ih =>
      intro agree
      simp only [psubst, psubstList_eq_map]
      exact bagLaws_apply c (forall₂_map_map fun q member => ih q member fun x occurs =>
        agree x (mem_pvars_apply_of member occurs))
  | lambda nm body ih =>
      intro agree
      simp only [psubst]
      exact BagLaws.map (f := .lambda nm) (fun r => .lambda nm r) (ih fun x occurs => agree x (by
        simp only [pvars]
        exact occurs))
  | multiLambda n nms body ih =>
      intro agree
      simp only [psubst]
      exact BagLaws.map (f := .multiLambda n nms) (fun r => .multiLambda n nms r) (ih fun x occurs => agree x (by
        simp only [pvars]
        exact occurs))
  | subst body repl ihb ihr =>
      intro agree
      simp only [psubst]
      exact (BagLaws.map (f := fun a => .subst a (psubst σ repl)) (fun r => .substBody _ r)
          (ihb fun x occurs => agree x (by simp [pvars, occurs]))).trans
        (BagLaws.map (f := fun a => .subst (psubst τ body) a) (fun r => .substRepl _ r)
          (ihr fun x occurs => agree x (by simp [pvars, occurs])))
  | collection ct elems rest ih =>
      intro agree
      simp only [psubst, psubstList_eq_map]
      exact bagLaws_collection ct rest (forall₂_map_map fun q member => ih q member fun x occurs =>
        agree x (mem_pvars_collection_of member occurs))
  | nil => simp_all
  | cons p ps head tail =>
      rename_i q member agreeQ
      rcases List.mem_cons.mp member with rfl | later
      · exact head agreeQ
      · exact tail q later agreeQ

/-- Canonicalizing a substitution's images does not change its action
modulo the bag laws, even on open instances. -/
theorem psubst_canonSubst_rel (σ : PSubst) (p : Pattern) :
    BagLaws (psubst σ p) (psubst (canonSubst σ) p) := by
  apply psubst_bagLaws_congr
  intro x _
  cases image : σ x with
  | none => simpa only [canonSubst, image, Option.map_none, Option.getD_none] using BagLaws.refl (.fvar x)
  | some v => simpa only [canonSubst, image, Option.map_some, Option.getD_some] using bagLaws_bagCanon v

/-- On canonical patterns with ground bags, every quotient solution
absorbs the written principal substitution modulo the bag laws. The
unifier's values can contain variables. -/
theorem principal_absorbed_mod_bags {t u : Pattern} {bs : Bindings}
    (principal : MeTTaCalculus.Corrected.Principal t u bs)
    (groundT : groundBags t = true) (groundU : groundBags u = true)
    (canonicalT : bagCanon t = t) (canonicalU : bagCanon u = u) {σ : PSubst}
    (equal : BagLaws (psubst σ t) (psubst σ u)) (p : Pattern) :
    BagLaws (psubst σ (psubst bs.lookup p)) (psubst σ p) := by
  have read := psubst_canonSubst_rel σ (psubst bs.lookup p)
  rw [principal.general (canonSubst σ)
    (canonSubst_unifies groundT groundU canonicalT canonicalU equal) p] at read
  exact read.trans (psubst_canonSubst_rel σ p).symm

/-- Ground readback is the specialization where the retained image is
unchanged by the final solution. -/
theorem agrees_of_groundPrincipal {t u : Pattern} {bs : Bindings} (gp : GroundPrincipal t u bs)
    (groundT : groundBags t = true) (groundU : groundBags u = true)
    (canonicalT : bagCanon t = t) (canonicalU : bagCanon u = u) {σ : PSubst}
    (equal : BagLaws (psubst σ t) (psubst σ u)) :
    ∀ x ∈ pvars t ++ pvars u, ∀ v, bs.lookup x = some v → BagLaws (psubst σ (.fvar x)) v := by
  intro x inside v found
  have read := (principal_absorbed_mod_bags (Comm.principal_of_groundPrincipal gp) groundT groundU
    canonicalT canonicalU equal (.fvar x)).symm
  have closed : pvars v = [] := by
    obtain ⟨w, same, ground⟩ := gp.covers x inside
    rw [found] at same
    exact (Option.some.inj same).symm ▸ ground
  rwa [show psubst bs.lookup (.fvar x) = v by simp [psubst, found], psubst_of_pvars_nil σ v closed] at read

/-- **A solution that agrees modulo the bag laws with a ground binding list reads a pre-dotted continuation as
the representation of its dot, modulo the bag laws**, under the hypotheses of `dotted_reads_predot`. -/
theorem dotted_reads_predot_bag {bs : Bindings} {keys vs : List String} (keysOf : ∀ e ∈ bs, e.1 ∈ keys)
    (bound : ∀ x ∈ keys, ∃ v, bs.lookup x = some v ∧ pvars v = [])
    {σ : PSubst} (agrees : ∀ x ∈ keys, ∀ v, bs.lookup x = some v → BagLaws (psubst σ (.fvar x)) v)
    (A : Pattern) (fo : firstOrder A = true) (sub : ∀ x ∈ vs, x ∈ keys)
    (reads : ∀ x ∈ pvars A, x ∈ keys → x ∈ vs) (kept : ∀ x ∈ keys, x ∉ binders A) :
    BagLaws (psubst σ (dotted vs (predot A))) (psubst σ (predot (applyDot bs A))) := by
  rw [applyDot_eq bs A fo]
  have ground : GroundValued (fun x => (bs.lookup x).map nQuote) := by
    intro x v found
    change (bs.lookup x).map nQuote = some v at found
    obtain ⟨w, look, rfl⟩ := Option.map_eq_some_iff.mp found
    obtain ⟨w', look', closed⟩ := bound x (mem_keys_of_lookup keysOf look)
    rw [look] at look'
    obtain rfl := Option.some.inj look'
    simp [nQuote, pvars, MeTTaOperationsComm.pvars.pvarsList, closed]
  have untouched : ∀ x ∈ binders A, (fun x => (bs.lookup x).map nQuote) x = Option.none := by
    intro x inside
    have outside : x ∉ keys := fun inKeys => kept x inKeys inside
    simp [lookup_eq_none_of_keys keysOf outside]
  rw [predot_psubst ground A untouched]
  unfold dotted
  rw [psubst_comp, psubst_comp]
  apply psubst_bagLaws_congr
  intro x occurs
  have inA := mem_pvars_predot occurs
  by_cases inKeys : x ∈ keys
  · have inVs := reads x inA inKeys
    obtain ⟨v, found, closed⟩ := bound x inKeys
    simp only [pcomp, quoteOn, if_pos inVs, Option.getD_some, psubst_nQuote, found, Option.map_some]
    rw [psubst_of_pvars_nil σ v closed]
    exact bagLaws_quote (agrees x inKeys v found)
  · have notVs : x ∉ vs := fun inVs => inKeys (sub x inVs)
    have look : bs.lookup x = none := lookup_eq_none_of_keys keysOf inKeys
    simp only [pcomp, quoteOn, if_neg notVs, look, Option.map_none]
    exact BagLaws.refl _

/-! ## COMM at the quotient frame -/

/-- An input modulo the bag laws is an input, part by part. -/
theorem bagLaws_pFor_iff {t x k t' x' k' : Pattern} :
    BagLaws (pFor t x k) (pFor t' x' k') ↔ BagLaws t t' ∧ BagLaws x x' ∧ BagLaws k k' := by
  simp only [bagLaws_iff, pFor, bagCanon_apply, List.map_cons, List.map_nil, Pattern.apply.injEq,
    List.cons.injEq, and_true, true_and]

/-- **The COMM firing of the finite program at the quotient frame.** -/
def commAtQ (ρ : PSubst) (first second made₁ made₂ : O) : Firing O QE program PUnit.unit :=
  ⟨commRule, commRule_mem, PUnit.unit, ρ, commSelection first second made₁ made₂, []⟩

omit [DecidableEq O] in
theorem commAtQ_eq (ρ : PSubst) (first second made₁ made₂ : O) :
    commAtQ ρ first second made₁ made₂ = quotientFiring (commAt ρ first second made₁ made₂) := rfl

omit [DecidableEq O] in
theorem commAtQ_information (label : O → Pattern) (C : Configuration Pattern O) (ρ : PSubst)
    (first second made₁ made₂ : O) :
    (commAtQ ρ first second made₁ made₂).information QX (embed label C) =
      C.equations ++ [(psubst ρ (pFor firstPattern channelUnknown firstBody), label first),
        (psubst ρ (pFor secondPattern channelUnknown secondBody), label second)] ++ [] ++
        [(psubst ρ firstPattern, psubst ρ secondPattern)] := by
  rw [OneFrame.information_eq]
  rfl

theorem commAtQ_label₁ (label : O → Pattern) (C : Configuration Pattern O) (ρ : PSubst)
    (first second made₁ made₂ : O) :
    ((commAtQ ρ first second made₁ made₂).result QX (embed label C)).label made₁ = psubst ρ firstBody := by
  show (if made₁ = made₁ then psubst ρ firstBody else _) = _
  rw [if_pos rfl]

theorem commAtQ_label₂ (label : O → Pattern) (C : Configuration Pattern O) (ρ : PSubst)
    (first second : O) {made₁ made₂ : O} (madeDistinct : made₁ ≠ made₂) :
    ((commAtQ ρ first second made₁ made₂).result QX (embed label C)).label made₂ = psubst ρ secondBody := by
  show (if made₂ = made₁ then _ else if made₂ = made₂ then psubst ρ secondBody else _) = _
  rw [if_neg (Ne.symm madeDistinct), if_pos rfl]

/-- **Admission of the COMM firing at the quotient frame, for rows of any input shape**: the taken rows are
distinct, present, and read as two inputs on one channel modulo the bag laws at every solution of the
knowledge; the made identities are distinct and not present; some solution of the knowledge unifies the
patterns modulo the bag laws; the opening is fresh. -/
theorem comm_admits_bag (label : O → Pattern) (t u channel K₁ K₂ : Pattern) (C : Configuration Pattern O)
    (first second made₁ made₂ : O)
    (readsFirst : ∀ σ : PSubst, bagAction.Models σ C.equations →
      BagLaws (psubst σ (label first)) (psubst σ (pFor t channel K₁)))
    (readsSecond : ∀ σ : PSubst, bagAction.Models σ C.equations →
      BagLaws (psubst σ (label second)) (psubst σ (pFor u channel K₂)))
    (distinct : first ≠ second) (madeDistinct : made₁ ≠ made₂)
    (present₁ : first ∈ C.present) (present₂ : second ∈ C.present)
    (fresh₁ : made₁ ∉ C.present) (fresh₂ : made₂ ∉ C.present)
    {σ₀ : PSubst} (known : bagAction.Models σ₀ C.equations) (unifies : BagLaws (psubst σ₀ t) (psubst σ₀ u))
    {ρ : PSubst} (opensFreshly : (commAtQ ρ first second made₁ made₂).Fresh QX (embed label C)) :
    (RuleSyntax.step QX O QE program).Admits (s := embed label C) (commAtQ ρ first second made₁ made₂) := by
  let h : PSubst := commInstance (psubst σ₀ t) (psubst σ₀ u) (psubst σ₀ channel) (psubst σ₀ K₁) (psubst σ₀ K₂)
  obtain ⟨w, solved, -, -⟩ := Comm.information_amalgamates_matched (Y := QX) (s := embed label C)
    (commAtQ ρ first second made₁ made₂) opensFreshly (b := PUnit.unit) σ₀ h known
    (fun e member => by
      obtain rfl := List.mem_singleton.mp member
      show BagLaws (psubst h firstPattern) (psubst h secondPattern)
      rw [commInstance_firstPattern, commInstance_secondPattern]
      exact unifies)
    (fun o member => by
      rcases List.mem_cons.mp member with rfl | member
      · exact present₁
      · obtain rfl := List.mem_singleton.mp member
        exact present₂)
    (fun _ member => (List.not_mem_nil member).elim)
    (fun q member => by
      rcases List.mem_cons.mp member with rfl | member
      · show BagLaws (psubst h (pFor firstPattern channelUnknown firstBody)) (psubst σ₀ (label first))
        rw [psubst_pFor, commInstance_firstPattern, commInstance_channel, commInstance_firstBody]
        exact (readsFirst σ₀ known).symm
      · obtain rfl := List.mem_singleton.mp member
        show BagLaws (psubst h (pFor secondPattern channelUnknown secondBody)) (psubst σ₀ (label second))
        rw [psubst_pFor, commInstance_secondPattern, commInstance_channel, commInstance_secondBody]
        exact (readsSecond σ₀ known).symm)
    (fun _ member => (List.not_mem_nil member).elim)
  refine (RuleSyntax.admits_iff _).mpr ⟨opensFreshly,
    ⟨by simp [commAtQ, commSelection, distinct], by simp [commAtQ, commSelection, madeDistinct],
      rfl, rfl, rfl, rfl⟩,
    ⟨?_, ?_, ?_, ?_, fun query member => by simp [Selection.commit] at member⟩,
    ⟨PUnit.unit, w, solved⟩, fun _ member => (List.not_mem_nil member).elim,
    fun _ member => (List.not_mem_nil member).elim⟩
  · intro o member
    simp only [commAtQ, commSelection, Selection.commit, List.toFinset_cons, List.toFinset_nil,
      insert_empty_eq, Finset.mem_insert, Finset.mem_singleton] at member
    rcases member with rfl | rfl
    · exact present₁
    · exact present₂
  · intro o member
    simp [commAtQ, commSelection, Selection.commit] at member
  · simp [commAtQ, commSelection, Selection.commit]
  · rw [Finset.disjoint_left]
    intro o member
    simp only [commAtQ, commSelection, Selection.commit, List.toFinset_cons, List.toFinset_nil,
      insert_empty_eq, Finset.mem_insert, Finset.mem_singleton] at member
    rcases member with rfl | rfl
    · exact fresh₁
    · exact fresh₂

/-- **What every solution modulo the bag laws says after the COMM firing**: it solves the knowledge before,
unifies the patterns modulo the bag laws, and reads each made row as the continuation its taken row holds,
modulo the bag laws. -/
theorem comm_reads_bag (label : O → Pattern) (t u channel₁ channel₂ K₁ K₂ : Pattern)
    (C : Configuration Pattern O) (first second made₁ made₂ : O)
    (readsFirst : ∀ σ : PSubst, bagAction.Models σ C.equations →
      BagLaws (psubst σ (label first)) (psubst σ (pFor t channel₁ K₁)))
    (readsSecond : ∀ σ : PSubst, bagAction.Models σ C.equations →
      BagLaws (psubst σ (label second)) (psubst σ (pFor u channel₂ K₂)))
    (madeDistinct : made₁ ≠ made₂) (ρ : PSubst) {σ : PSubst}
    (solved : bagAction.Models σ ((commAtQ ρ first second made₁ made₂).result QX (embed label C)).knowledge) :
    bagAction.Models σ C.equations ∧ BagLaws (psubst σ t) (psubst σ u) ∧
      BagLaws (psubst σ (((commAtQ ρ first second made₁ made₂).result QX (embed label C)).label made₁))
        (psubst σ K₁) ∧
      BagLaws (psubst σ (((commAtQ ρ first second made₁ made₂).result QX (embed label C)).label made₂))
        (psubst σ K₂) := by
  have info : ((commAtQ ρ first second made₁ made₂).result QX (embed label C)).knowledge =
      (commAtQ ρ first second made₁ made₂).information QX (embed label C) := rfl
  rw [info, commAtQ_information] at solved
  have known : bagAction.Models σ C.equations := fun e member => solved e (by simp [member])
  have take₁ : BagLaws (psubst σ (psubst ρ (pFor firstPattern channelUnknown firstBody))) (psubst σ (label first)) :=
    solved (psubst ρ (pFor firstPattern channelUnknown firstBody), label first) (by simp)
  have take₂ : BagLaws (psubst σ (psubst ρ (pFor secondPattern channelUnknown secondBody)))
      (psubst σ (label second)) :=
    solved (psubst ρ (pFor secondPattern channelUnknown secondBody), label second) (by simp)
  have told : BagLaws (psubst σ (psubst ρ firstPattern)) (psubst σ (psubst ρ secondPattern)) :=
    solved (psubst ρ firstPattern, psubst ρ secondPattern) (by simp)
  have row₁ := take₁.trans (readsFirst σ known)
  have row₂ := take₂.trans (readsSecond σ known)
  simp only [psubst_pFor] at row₁ row₂
  obtain ⟨pattern₁, -, body₁⟩ := bagLaws_pFor_iff.mp row₁
  obtain ⟨pattern₂, -, body₂⟩ := bagLaws_pFor_iff.mp row₂
  refine ⟨known, pattern₁.symm.trans (told.trans pattern₂), ?_, ?_⟩
  · rw [commAtQ_label₁]
    exact body₁
  · rw [commAtQ_label₂ label C ρ first second madeDistinct]
    exact body₂

/-- **COMM as one firing of the finite program at the quotient frame.** Under the side conditions of
`FiniteProgram.comm_one_firing`, read modulo the bag laws (a ground principal unifier `gp`, the variable
convention, first-order continuations, rows that read as the represented inputs modulo the bag laws at every
solution, distinct made identities that are not present, some solution unifying the patterns modulo the bag
laws, a fresh opening), and the named hypothesis that the written patterns have ground bags and are
canonical: the firing is admitted, the manuscript's COMM relates the redex to its dotted reduct, and every
solution of the result reads the made rows as the representations of the dotted continuations, modulo the
bag laws. -/
theorem comm_one_firing_bag (label : O → Pattern) (t u channel A B : Pattern) (bs : Bindings)
    (gp : GroundPrincipal t u bs) (convention : Apart t A u B)
    (foA : firstOrder A = true) (foB : firstOrder B = true)
    (groundT : groundBags t = true) (groundU : groundBags u = true)
    (canonicalT : bagCanon t = t) (canonicalU : bagCanon u = u)
    (C : Configuration Pattern O) (first second made₁ made₂ : O)
    (readsFirst : ∀ σ : PSubst, bagAction.Models σ C.equations →
      BagLaws (psubst σ (label first)) (psubst σ (predot (pFor t channel A))))
    (readsSecond : ∀ σ : PSubst, bagAction.Models σ C.equations →
      BagLaws (psubst σ (label second)) (psubst σ (predot (pFor u channel B))))
    (distinct : first ≠ second) (madeDistinct : made₁ ≠ made₂)
    (present₁ : first ∈ C.present) (present₂ : second ∈ C.present)
    (fresh₁ : made₁ ∉ C.present) (fresh₂ : made₂ ∉ C.present)
    (glued : ∃ σ₀ : PSubst, bagAction.Models σ₀ C.equations ∧ BagLaws (psubst σ₀ t) (psubst σ₀ u))
    {ρ : PSubst} (opensFreshly : (commAtQ ρ first second made₁ made₂).Fresh QX (embed label C)) :
    (RuleSyntax.step QX O QE program).Admits (s := embed label C) (commAtQ ρ first second made₁ made₂) ∧
      MeTTaCalculus.ReflectionClosure.Step GroundPrincipal SC (par (pFor t channel A) (pFor u channel B))
        (par (applyDot bs A) (applyDot bs B)) ∧
      MeTTaCalculus.Corrected.Step MeTTaCalculus.Corrected.conventional
        (par (pFor t channel A) (pFor u channel B)) (par (applyDot bs A) (applyDot bs B)) ∧
      ∀ σ : PSubst, bagAction.Models σ
          ((commAtQ ρ first second made₁ made₂).result QX (embed label C)).knowledge →
        BagLaws (psubst σ (((commAtQ ρ first second made₁ made₂).result QX (embed label C)).label made₁))
            (psubst σ (predot (applyDot bs A))) ∧
          BagLaws (psubst σ (((commAtQ ρ first second made₁ made₂).result QX (embed label C)).label made₂))
            (psubst σ (predot (applyDot bs B))) := by
  obtain ⟨σ₀, known, unifies⟩ := glued
  have rowFirst : ∀ σ : PSubst, bagAction.Models σ C.equations →
      BagLaws (psubst σ (label first)) (psubst σ (pFor t (predot channel) (dotted (pvars t) (predot A)))) :=
    fun σ solved => by
      have read := readsFirst σ solved
      rw [predot_pFor] at read
      exact read
  have rowSecond : ∀ σ : PSubst, bagAction.Models σ C.equations →
      BagLaws (psubst σ (label second)) (psubst σ (pFor u (predot channel) (dotted (pvars u) (predot B)))) :=
    fun σ solved => by
      have read := readsSecond σ solved
      rw [predot_pFor] at read
      exact read
  refine ⟨comm_admits_bag label t u (predot channel) (dotted (pvars t) (predot A)) (dotted (pvars u) (predot B)) C
      first second made₁ made₂ rowFirst rowSecond distinct madeDistinct present₁ present₂ fresh₁ fresh₂ known
      unifies opensFreshly,
    .comm t u channel A B bs gp,
    .comm t u channel A B bs (Comm.principal_of_groundPrincipal gp) convention, fun σ solved => ?_⟩
  obtain ⟨-, unify, body₁, body₂⟩ := comm_reads_bag label t u (predot channel) (predot channel)
    (dotted (pvars t) (predot A)) (dotted (pvars u) (predot B)) C first second made₁ made₂ rowFirst rowSecond
    madeDistinct ρ solved
  have agrees := agrees_of_groundPrincipal gp groundT groundU canonicalT canonicalU unify
  obtain ⟨keptA, keptB⟩ := keys_of_apart convention
  refine ⟨body₁.trans ?_, body₂.trans ?_⟩
  · refine dotted_reads_predot_bag gp.keys gp.covers agrees A foA (fun x inside => List.mem_append_left _ inside)
      ?_ keptA
    intro x inA inKeys
    rcases List.mem_append.mp inKeys with inT | inU
    · exact inT
    · exact absurd inA (convention.rightOutside x inU)
  · refine dotted_reads_predot_bag gp.keys gp.covers agrees B foB (fun x inside => List.mem_append_right _ inside)
      ?_ keptB
    intro x inB inKeys
    rcases List.mem_append.mp inKeys with inT | inU
    · exact absurd inB (convention.leftOutside x inT)
    · exact inU

/-- **Closed continuations read a fixed pattern, modulo the bag laws.** Under the side conditions of
`comm_one_firing_bag`, with each continuation's variables its own pattern's (`closedA`, `closedB`): every solution
reads the made rows as the manuscript's dotted continuations, modulo the bag laws. -/
theorem comm_one_firing_closed_bag (label : O → Pattern) (t u channel A B : Pattern) (bs : Bindings)
    (gp : GroundPrincipal t u bs) (convention : Apart t A u B)
    (foA : firstOrder A = true) (foB : firstOrder B = true)
    (closedA : ∀ x ∈ pvars A, x ∈ pvars t) (closedB : ∀ x ∈ pvars B, x ∈ pvars u)
    (groundT : groundBags t = true) (groundU : groundBags u = true)
    (canonicalT : bagCanon t = t) (canonicalU : bagCanon u = u)
    (C : Configuration Pattern O) (first second made₁ made₂ : O)
    (readsFirst : ∀ σ : PSubst, bagAction.Models σ C.equations →
      BagLaws (psubst σ (label first)) (psubst σ (predot (pFor t channel A))))
    (readsSecond : ∀ σ : PSubst, bagAction.Models σ C.equations →
      BagLaws (psubst σ (label second)) (psubst σ (predot (pFor u channel B))))
    (distinct : first ≠ second) (madeDistinct : made₁ ≠ made₂)
    (present₁ : first ∈ C.present) (present₂ : second ∈ C.present)
    (fresh₁ : made₁ ∉ C.present) (fresh₂ : made₂ ∉ C.present)
    (glued : ∃ σ₀ : PSubst, bagAction.Models σ₀ C.equations ∧ BagLaws (psubst σ₀ t) (psubst σ₀ u))
    {ρ : PSubst} (opensFreshly : (commAtQ ρ first second made₁ made₂).Fresh QX (embed label C)) :
    (RuleSyntax.step QX O QE program).Admits (s := embed label C) (commAtQ ρ first second made₁ made₂) ∧
      MeTTaCalculus.ReflectionClosure.Step GroundPrincipal SC (par (pFor t channel A) (pFor u channel B))
        (par (applyDot bs A) (applyDot bs B)) ∧
      ∀ σ : PSubst, bagAction.Models σ
          ((commAtQ ρ first second made₁ made₂).result QX (embed label C)).knowledge →
        BagLaws (psubst σ (((commAtQ ρ first second made₁ made₂).result QX (embed label C)).label made₁))
            (applyDot bs A) ∧
          BagLaws (psubst σ (((commAtQ ρ first second made₁ made₂).result QX (embed label C)).label made₂))
            (applyDot bs B) := by
  obtain ⟨admitted, manuscript, -, reads⟩ := comm_one_firing_bag label t u channel A B bs gp convention foA foB
    groundT groundU canonicalT canonicalU C first second made₁ made₂ readsFirst readsSecond distinct madeDistinct
    present₁ present₂ fresh₁ fresh₂ glued opensFreshly
  have groundA : pvars (applyDot bs A) = [] :=
    Comm.applyDot_ground gp A foA fun x inside => List.mem_append_left _ (closedA x inside)
  have groundB : pvars (applyDot bs B) = [] :=
    Comm.applyDot_ground gp B foB fun x inside => List.mem_append_right _ (closedB x inside)
  refine ⟨admitted, manuscript, fun σ solved => ?_⟩
  obtain ⟨read₁, read₂⟩ := reads σ solved
  rw [FiniteProgram.predot_ground _ groundA, psubst_of_pvars_nil σ _ groundA] at read₁
  rw [FiniteProgram.predot_ground _ groundB, psubst_of_pvars_nil σ _ groundB] at read₂
  exact ⟨read₁, read₂⟩

/-- **The COMM transition at the quotient frame, with its result.** Under the side conditions of
`comm_one_firing_bag` (no opening is assumed: a fresh one exists), the step of the finite program at the
quotient frame moves the embedded configuration to a state whose present rows replace the inputs by the made
identities, whose other labels are unchanged, whose knowledge has a solution, and every solution of whose
knowledge reads the made rows as the representations of the dotted continuations, modulo the bag laws. -/
theorem comm_one_transition_bag (label : O → Pattern) (t u channel A B : Pattern) (bs : Bindings)
    (gp : GroundPrincipal t u bs) (convention : Apart t A u B)
    (foA : firstOrder A = true) (foB : firstOrder B = true)
    (groundT : groundBags t = true) (groundU : groundBags u = true)
    (canonicalT : bagCanon t = t) (canonicalU : bagCanon u = u)
    (C : Configuration Pattern O) (first second made₁ made₂ : O)
    (readsFirst : ∀ σ : PSubst, bagAction.Models σ C.equations →
      BagLaws (psubst σ (label first)) (psubst σ (predot (pFor t channel A))))
    (readsSecond : ∀ σ : PSubst, bagAction.Models σ C.equations →
      BagLaws (psubst σ (label second)) (psubst σ (predot (pFor u channel B))))
    (distinct : first ≠ second) (madeDistinct : made₁ ≠ made₂)
    (present₁ : first ∈ C.present) (present₂ : second ∈ C.present)
    (fresh₁ : made₁ ∉ C.present) (fresh₂ : made₂ ∉ C.present)
    (glued : ∃ σ₀ : PSubst, bagAction.Models σ₀ C.equations ∧ BagLaws (psubst σ₀ t) (psubst σ₀ u)) :
    ∃ s' : State (OneFrame.Terms Pattern) O, Succ (RuleSyntax.step QX O QE program).toStep (embed label C) s' ∧
      s'.present = (C.present \ {first, second}) ∪ {made₁, made₂} ∧
      (∀ o, o ≠ made₁ → o ≠ made₂ → s'.label o = label o) ∧
      (∃ σ : PSubst, bagAction.Models σ s'.knowledge) ∧
      ∀ σ : PSubst, bagAction.Models σ s'.knowledge →
        BagLaws (psubst σ (s'.label made₁)) (psubst σ (predot (applyDot bs A))) ∧
          BagLaws (psubst σ (s'.label made₂)) (psubst σ (predot (applyDot bs B))) := by
  obtain ⟨ρ, opensFreshly⟩ := exists_fresh_opening label C first second made₁ made₂
  have freshQ : (commAtQ ρ first second made₁ made₂).Fresh QX (embed label C) := fresh_quotient opensFreshly
  obtain ⟨admitted, -, -, reads⟩ := comm_one_firing_bag label t u channel A B bs gp convention foA foB groundT
    groundU canonicalT canonicalU C first second made₁ made₂ readsFirst readsSecond distinct madeDistinct
    present₁ present₂ fresh₁ fresh₂ glued freshQ
  obtain ⟨_, σ, solvedσ⟩ := ((RuleSyntax.admits_iff _).mp admitted).2.2.2.1
  refine ⟨(commAtQ ρ first second made₁ made₂).result QX (embed label C), ⟨_, admitted, rfl⟩, ?_,
    fun o other₁ other₂ => ?_, ⟨σ, solvedσ⟩, reads⟩
  · show fire C.present ((commSelection first second made₁ made₂).commit (T := Unit)) = _
    simp [fire, Selection.commit, commSelection]
  · have missing : o ∉ (commAtQ ρ first second made₁ made₂).selection.made := by
      simp [commAtQ, commSelection, other₁, other₂]
    exact (Firing.result_label_other (X := QX) (s := embed label C) _ missing).trans (psubst_none (label o))

#print axioms quotientMap
#print axioms quotientMap_not_reflects
#print axioms quotient_admits
#print axioms program_quotient_admits
#print axioms mem_pvars_bagCanon
#print axioms bagCanon_psubst_of_groundBags
#print axioms canonSubst_unifies
#print axioms agrees_of_groundPrincipal
#print axioms psubst_bagLaws_congr
#print axioms dotted_reads_predot_bag
#print axioms bagLaws_pFor_iff
#print axioms comm_admits_bag
#print axioms comm_reads_bag
#print axioms comm_one_firing_bag
#print axioms comm_one_firing_closed_bag
#print axioms comm_one_transition_bag

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.ReflQuotient
