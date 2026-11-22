import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.ReflNameFrame
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.ReflQuotientTransport
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.ReflUniformNames

/-!
# The finite COMM hosting at the name frame

`ReflNameFrame` gives the name frame `QN`: patterns compared modulo the bag laws of the processes they quote,
the spine as written. Here the finite program of `FiniteComm` runs at it, with the results that
`ReflQuotientTransport` proves at `QX`, one for one.

## The arrow from the syntactic frame

`nameFiring` reads a firing of the syntactic frame at `QN`; a fresh opening stays fresh (`fresh_name`). For a
rule without checks and collect query an admitted firing of the syntactic frame is admitted at `QN` with the same
result (`name_admits`); every rule of the finite program is such a rule (`program_name_admits`).

## COMM at the name frame

The named hypothesis is H-REFL1's, at its exact strength: every parallel bag of the two patterns is ground
(`groundBags`) and the patterns are canonical (`bagCanon t = t`). It suffices at `QN` unchanged. A solution
modulo the name laws is a solution modulo the bag laws (`bagLaws_of_nameLaws`), so the ground principal
unifier determines every pattern variable modulo the bag laws (`ReflQuotient.agrees_of_groundPrincipal`).
The dot puts every pattern variable under a quote, where the name laws are the bag laws (`nameLaws_nQuote`),
so the made rows read modulo the name laws (`dotted_reads_predot_name`), a finer reading than at `QX`.

* `comm_admits_name`, `comm_reads_name`: admission and the read-off at `QN`, for rows of any input shape read
  modulo the name laws.
* `comm_one_firing_name`: the firing is admitted, the manuscript's COMM relates the redex to its dotted
  reduct (as written and in the corrected semantics), and every solution reads the made rows as the
  representations of the dotted continuations, modulo the name laws. With closed continuations they read as
  the dotted continuations themselves (`comm_one_firing_closed_name`).
* `comm_one_transition_name`: a fresh opening exists, and the transition reaches a state with the made rows,
  a solvable knowledge, and that read-off.

What separates `QN` from the corrected semantics and from `QX` is in `ReflNameTransportControls`.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.ReflNames

open Mettapedia.OSLF.MeTTaIL.Syntax (Pattern CollType)
open Mettapedia.OSLF.MeTTaIL.Match (Bindings)
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus (pFor par pZero nQuote applyDot SC pPar)
open MeTTaOperationsComm (psubst pcomp psubst_comp psubst_none psubst_of_pvars_nil pvars PSubst
  quoteOn dotted commSelection GroundPrincipal applyDot_eq psubst_nQuote psubst_pFor firstOrder
  lookup_eq_none_of_keys)
open MeTTaCalculus.Corrected (binders Apart psubstList_eq_map mem_pvars_apply_of mem_pvars_collection_of)
open FiniteProgram (predot predot_pFor predot_psubst GroundValued mem_keys_of_lookup mem_pvars_predot commAt
  commRule commRule_mem program commInstance commInstance_firstPattern commInstance_secondPattern
  commInstance_channel commInstance_firstBody commInstance_secondBody firstPattern secondPattern channelUnknown
  firstBody secondBody keys_of_apart exists_fresh_opening)
open MeTTaCalculus.OccurrenceCommits (fire)
open Comm (X E)
open OneFrame (embed)
open LogicOverTheStep.StepSpan (Succ)
open ReflQuotient (BagLaws bagCanon groundBags agrees_of_groundPrincipal program_rules_plain)
open ReflUniform (predotU predotU_psubst_of_stable predotU_nQuote pvars_predotU)

/-! ## The arrow from the syntactic frame -/

variable {O : Type*}

/-- A firing of a program at the syntactic frame, read at the name frame: the same rule, opening, selection
and seen sets. -/
def nameFiring {P : Program (OneFrame.Terms Pattern)} (f : Firing O E P PUnit.unit) :
    Firing O QNE P PUnit.unit :=
  ⟨f.rule, f.member, PUnit.unit, f.opening, f.selection, f.seen⟩

/-- A fresh opening at the syntactic frame is fresh at the name frame. -/
theorem fresh_name {label : O → Pattern} {C : Configuration Pattern O} {P : Program (OneFrame.Terms Pattern)}
    {f : Firing O E P PUnit.unit} (fresh : f.Fresh X (embed label C)) :
    (nameFiring f).Fresh QN (embed label C) := by
  intro b g h
  obtain ⟨u, onState, onRule⟩ := fresh b g h
  exact ⟨u, fun t mentions => nameLaws_of_eq (onState t mentions), fun t member => nameLaws_of_eq (onRule t member)⟩

/-- **Admission is carried to the name frame** for a rule without checks and collect query, with the same result. -/
theorem name_admits [DecidableEq O] {P : Program (OneFrame.Terms Pattern)} (label : O → Pattern)
    (C : Configuration Pattern O) (f : Firing O E P PUnit.unit) (noChecks : f.rule.body.checks = [])
    (noCollect : f.rule.collect = []) (admitted : (RuleSyntax.step X O E P).Admits (s := embed label C) f) :
    (RuleSyntax.step QN O QNE P).Admits (s := embed label C) (nameFiring f) ∧
      (nameFiring f).result QN (embed label C) = f.result X (embed label C) := by
  obtain ⟨fresh, shapes, enabled, ⟨b, σ, solved⟩, -, -⟩ := (RuleSyntax.admits_iff f).mp admitted
  refine ⟨(RuleSyntax.admits_iff _).mpr ⟨fresh_name fresh, shapes, enabled,
    ⟨b, σ, fun e member => nameLaws_of_eq (solved e member)⟩, ?_, ?_⟩, rfl⟩
  · intro c member
    simp [Firing.opened, RuleInstance.map, nameFiring, noChecks] at member
  · intro q member
    simp [Firing.collectOpened, nameFiring, noCollect] at member

/-- **Every transition of the finite program at the syntactic frame is one at the name frame**, with the same
result: a functional simulation of the steps. -/
theorem program_name_admits [DecidableEq O] (label : O → Pattern) (C : Configuration Pattern O)
    (f : Firing O E program PUnit.unit) (admitted : (RuleSyntax.step X O E program).Admits (s := embed label C) f) :
    (RuleSyntax.step QN O QNE program).Admits (s := embed label C) (nameFiring f) ∧
      (nameFiring f).result QN (embed label C) = f.result X (embed label C) :=
  name_admits label C f (program_rules_plain f.member).1 (program_rules_plain f.member).2 admitted

/-! ## Substitutions related value by value -/

theorem forall₂_map_map {f g : Pattern → Pattern} :
    ∀ {xs : List Pattern}, (∀ q ∈ xs, NameLaws (f q) (g q)) → List.Forall₂ NameLaws (xs.map f) (xs.map g)
  | [], _ => .nil
  | x :: _, h => .cons (h x List.mem_cons_self)
      (forall₂_map_map fun q member => h q (List.mem_cons_of_mem _ member))

/-- **Substitutions whose values are related modulo the name laws give related instances.** -/
theorem psubst_nameLaws_congr {σ τ : PSubst} (p : Pattern)
    (agree : ∀ x ∈ pvars p, NameLaws ((σ x).getD (.fvar x)) ((τ x).getD (.fvar x))) :
    NameLaws (psubst σ p) (psubst τ p) := by
  revert agree
  induction p using Pattern.rec (motive_2 := fun ps => ∀ q ∈ ps,
      (∀ x ∈ pvars q, NameLaws ((σ x).getD (.fvar x)) ((τ x).getD (.fvar x))) →
        NameLaws (psubst σ q) (psubst τ q)) with
  | bvar n => intro _; exact NameLaws.refl _
  | fvar x => intro agree; exact agree x (by simp [pvars])
  | apply c args ih =>
      intro agree
      simp only [psubst, psubstList_eq_map]
      exact nameLaws_apply c (forall₂_map_map fun q member => ih q member fun x occurs =>
        agree x (mem_pvars_apply_of member occurs))
  | lambda nm body ih =>
      intro agree
      simp only [psubst]
      exact NameLaws.map (f := .lambda nm) (fun r => .lambda nm r) (ih fun x occurs => agree x (by
        simp only [pvars]
        exact occurs))
  | multiLambda n nms body ih =>
      intro agree
      simp only [psubst]
      exact NameLaws.map (f := .multiLambda n nms) (fun r => .multiLambda n nms r) (ih fun x occurs => agree x (by
        simp only [pvars]
        exact occurs))
  | subst body repl ihb ihr =>
      intro agree
      simp only [psubst]
      exact (NameLaws.map (f := fun a => .subst a (psubst σ repl)) (fun r => .substBody _ r)
          (ihb fun x occurs => agree x (by simp [pvars, occurs]))).trans
        (NameLaws.map (f := fun a => .subst (psubst τ body) a) (fun r => .substRepl _ r)
          (ihr fun x occurs => agree x (by simp [pvars, occurs])))
  | collection ct elems rest ih =>
      intro agree
      simp only [psubst, psubstList_eq_map]
      exact nameLaws_collection ct rest (forall₂_map_map fun q member => ih q member fun x occurs =>
        agree x (mem_pvars_collection_of member occurs))
  | nil => simp_all
  | cons p ps head tail =>
      rename_i q member agreeQ
      rcases List.mem_cons.mp member with rfl | later
      · exact head agreeQ
      · exact tail q later agreeQ

/-- **A solution that agrees modulo the bag laws with a ground binding list reads a pre-dotted continuation as
the representation of its dot, modulo the name laws**, under the hypotheses of `dotted_reads_predot`: the dot
puts each agreeing value under a quote. -/
theorem dotted_reads_predot_name {bs : Bindings} {keys vs : List String} (keysOf : ∀ e ∈ bs, e.1 ∈ keys)
    (bound : ∀ x ∈ keys, ∃ v, bs.lookup x = some v ∧ pvars v = [])
    {σ : PSubst} (agrees : ∀ x ∈ keys, ∀ v, bs.lookup x = some v → BagLaws (psubst σ (.fvar x)) v)
    (A : Pattern) (fo : firstOrder A = true) (sub : ∀ x ∈ vs, x ∈ keys)
    (reads : ∀ x ∈ pvars A, x ∈ keys → x ∈ vs) (kept : ∀ x ∈ keys, x ∉ binders A) :
    NameLaws (psubst σ (dotted vs (predot A))) (psubst σ (predot (applyDot bs A))) := by
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
  apply psubst_nameLaws_congr
  intro x occurs
  have inA := mem_pvars_predot occurs
  by_cases inKeys : x ∈ keys
  · have inVs := reads x inA inKeys
    obtain ⟨v, found, closed⟩ := bound x inKeys
    simp only [pcomp, quoteOn, if_pos inVs, Option.getD_some, psubst_nQuote, found, Option.map_some]
    rw [psubst_of_pvars_nil σ v closed]
    exact nameLaws_nQuote (agrees x inKeys v found)
  · have notVs : x ∉ vs := fun inVs => inKeys (sub x inVs)
    have look : bs.lookup x = none := lookup_eq_none_of_keys keysOf inKeys
    simp only [pcomp, quoteOn, if_neg notVs, look, Option.map_none]
    exact NameLaws.refl _

/-- Read the completed written match through uniform pre-dotting.
The domain test protects inner binders; the image tests allow residual
variables without inserting them under a binder that would dot them. -/
theorem dotted_reads_predotU_name {bs : Bindings} {keys vs : List String} (keysOf : ∀ e ∈ bs, e.1 ∈ keys)
    (bound : ∀ x ∈ keys, ∃ v, bs.lookup x = some v)
    (stable : ∀ x v, bs.lookup x = some v → predotU v = v)
    (relevant : ∀ x v, bs.lookup x = some v → ∀ y ∈ pvars v, y ∈ keys)
    {σ : PSubst} (agrees : ∀ x v, bs.lookup x = some v → BagLaws (psubst σ (.fvar x)) (psubst σ v))
    (A : Pattern) (fo : firstOrder A = true) (sub : ∀ x ∈ vs, x ∈ keys)
    (reads : ∀ x ∈ pvars A, x ∈ keys → x ∈ vs) (kept : ∀ x ∈ keys, x ∉ binders A) :
    NameLaws (psubst σ (dotted vs (predotU A))) (psubst σ (predotU (applyDot bs A))) := by
  let τ : PSubst := fun x => (bs.lookup x).map nQuote
  have fixed : ∀ x v, τ x = some v → predotU v = v := by
    intro x v image
    obtain ⟨w, found, rfl⟩ := Option.map_eq_some_iff.mp image
    rw [predotU_nQuote, stable x w found]
  have safe : ∀ y ∈ binders A, τ y = none ∧ ∀ x v, τ x = some v → y ∉ pvars v := by
    intro y inside
    have notKey : y ∉ keys := fun key => kept y key inside
    refine ⟨by simp [τ, lookup_eq_none_of_keys keysOf notKey], ?_⟩
    intro x v image occurs
    obtain ⟨w, found, rfl⟩ := Option.map_eq_some_iff.mp image
    rw [MeTTaCalculus.Corrected.pvars_nQuote] at occurs
    exact notKey (relevant x w found y occurs)
  rw [applyDot_eq bs A fo]
  change NameLaws _ (psubst σ (predotU (psubst τ A)))
  rw [predotU_psubst_of_stable fixed A safe]
  unfold dotted
  rw [psubst_comp, psubst_comp]
  apply psubst_nameLaws_congr
  intro x occurs
  rw [pvars_predotU] at occurs
  by_cases key : x ∈ keys
  · obtain ⟨value, found⟩ := bound x key
    simp only [τ, pcomp, quoteOn, if_pos (reads x occurs key), Option.getD_some, psubst_nQuote, found,
      Option.map_some]
    exact nameLaws_nQuote (agrees x value found)
  · have notDotted : x ∉ vs := fun m => key (sub x m)
    simp only [τ, pcomp, quoteOn, if_neg notDotted, lookup_eq_none_of_keys keysOf key, Option.map_none]
    exact NameLaws.refl _

/-- The syntactic solver is called on the written pair, before its
variables are instantiated by a name-frame solution. Completing its
bindings preserves principality and keeps the residual names. -/
theorem written_principal_reads {t u A B : Pattern} {bs : Bindings}
    (found : MeTTaCalculus.Corrected.unify t u = some bs)
    (apart : Apart t A u B) (foA : firstOrder A = true) (foB : firstOrder B = true)
    (stable : ∀ entry ∈ bs, predotU entry.2 = entry.2)
    (groundT : groundBags t = true) (groundU : groundBags u = true)
    (canonT : bagCanon t = t) (canonU : bagCanon u = u)
    {σ : PSubst} (solved : NameLaws (psubst σ t) (psubst σ u)) :
    let completed := MeTTaCalculus.Corrected.completeBindings (pvars t ++ pvars u) bs
    NameLaws (psubst σ (dotted (pvars t) (predotU A))) (psubst σ (predotU (applyDot completed A))) ∧
    NameLaws (psubst σ (dotted (pvars u) (predotU B))) (psubst σ (predotU (applyDot completed B))) := by
  intro completed
  have principal := MeTTaCalculus.Corrected.principal_completeBindings
    (MeTTaCalculus.Corrected.unify_principal found)
  have covers (x : String) (key : x ∈ pvars t ++ pvars u) : ∃ v, completed.lookup x = some v :=
    Option.isSome_iff_exists.mp (MeTTaCalculus.Corrected.complete_completeBindings t u bs x key)
  have safeImages (x : String) (v : Pattern) (image : completed.lookup x = some v) :
      predotU v = v ∧ ∀ y ∈ pvars v, y ∈ pvars t ++ pvars u := by
    change (MeTTaCalculus.Corrected.completeBindings _ bs).lookup x = some v at image
    rw [MeTTaCalculus.Corrected.lookup_completeBindings] at image
    cases fromSolver : bs.lookup x with
    | some w =>
      simp only [fromSolver, Option.some.injEq] at image
      subst v
      obtain ⟨entry, selected, rfl⟩ := Option.map_eq_some_iff.mp fromSolver
      have member := List.mem_of_find?_eq_some selected
      exact ⟨stable entry member, MeTTaCalculus.Corrected.unify_value_vars found entry member⟩
    | none =>
      by_cases relevant : x ∈ pvars t ++ pvars u
      · simp only [fromSolver, if_pos relevant, Option.some.injEq] at image
        subst v
        exact ⟨rfl, by simpa [pvars] using relevant⟩
      · simp [fromSolver, relevant] at image
  have agrees (x : String) (v : Pattern) (image : completed.lookup x = some v) :
      BagLaws (psubst σ (.fvar x)) (psubst σ v) := by
    have read := (ReflQuotient.principal_absorbed_mod_bags principal groundT groundU canonT canonU
      (bagLaws_of_nameLaws solved) (.fvar x)).symm
    rw [show psubst completed.lookup (.fvar x) = v by simp [psubst, image]] at read
    exact read
  obtain ⟨keptA, keptB⟩ := keys_of_apart apart
  refine ⟨dotted_reads_predotU_name principal.keys covers (fun x v h => (safeImages x v h).1)
      (fun x v h => (safeImages x v h).2) agrees A foA (fun _ => List.mem_append_left _) ?_ keptA,
    dotted_reads_predotU_name principal.keys covers (fun x v h => (safeImages x v h).1)
      (fun x v h => (safeImages x v h).2) agrees B foB (fun _ => List.mem_append_right _) ?_ keptB⟩
  · intro x inA key
    exact (List.mem_append.mp key).elim id (fun inU => absurd inA (apart.rightOutside x inU))
  · intro x inB key
    exact (List.mem_append.mp key).elim (fun inT => absurd inB (apart.leftOutside x inT)) id

/-! ## COMM at the name frame -/

/-- An input modulo the name laws is an input, part by part. -/
theorem nameLaws_pFor_iff {t x k t' x' k' : Pattern} :
    NameLaws (pFor t x k) (pFor t' x' k') ↔ NameLaws t t' ∧ NameLaws x x' ∧ NameLaws k k' := by
  rw [pFor, pFor, nameLaws_apply_iff (by unfold IsQuote; decide)]
  simp

/-- **The COMM firing of the finite program at the name frame.** -/
def commAtN (ρ : PSubst) (first second made₁ made₂ : O) : Firing O QNE program PUnit.unit :=
  ⟨commRule, commRule_mem, PUnit.unit, ρ, commSelection first second made₁ made₂, []⟩

theorem commAtN_eq (ρ : PSubst) (first second made₁ made₂ : O) :
    commAtN ρ first second made₁ made₂ = nameFiring (commAt ρ first second made₁ made₂) := rfl

theorem commAtN_information (label : O → Pattern) (C : Configuration Pattern O) (ρ : PSubst)
    (first second made₁ made₂ : O) :
    (commAtN ρ first second made₁ made₂).information QN (embed label C) =
      C.equations ++ [(psubst ρ (pFor firstPattern channelUnknown firstBody), label first),
        (psubst ρ (pFor secondPattern channelUnknown secondBody), label second)] ++ [] ++
        [(psubst ρ firstPattern, psubst ρ secondPattern)] := by
  rw [OneFrame.information_eq]
  rfl

theorem commAtN_label₁ [DecidableEq O] (label : O → Pattern) (C : Configuration Pattern O) (ρ : PSubst)
    (first second made₁ made₂ : O) :
    ((commAtN ρ first second made₁ made₂).result QN (embed label C)).label made₁ = psubst ρ firstBody := by
  show (if made₁ = made₁ then psubst ρ firstBody else _) = _
  rw [if_pos rfl]

theorem commAtN_label₂ [DecidableEq O] (label : O → Pattern) (C : Configuration Pattern O) (ρ : PSubst)
    (first second : O) {made₁ made₂ : O} (madeDistinct : made₁ ≠ made₂) :
    ((commAtN ρ first second made₁ made₂).result QN (embed label C)).label made₂ = psubst ρ secondBody := by
  show (if made₂ = made₁ then _ else if made₂ = made₂ then psubst ρ secondBody else _) = _
  rw [if_neg (Ne.symm madeDistinct), if_pos rfl]

/-- **Admission of the COMM firing at the name frame, for rows of any input shape**: the taken rows are
distinct, present, and read as two inputs on one channel modulo the name laws at every solution of the
knowledge; the made identities are distinct and not present; some solution of the knowledge unifies the
patterns modulo the name laws; the opening is fresh. -/
theorem comm_admits_name [DecidableEq O] (label : O → Pattern) (t u channel K₁ K₂ : Pattern)
    (C : Configuration Pattern O) (first second made₁ made₂ : O)
    (readsFirst : ∀ σ : PSubst, nameAction.Models σ C.equations →
      NameLaws (psubst σ (label first)) (psubst σ (pFor t channel K₁)))
    (readsSecond : ∀ σ : PSubst, nameAction.Models σ C.equations →
      NameLaws (psubst σ (label second)) (psubst σ (pFor u channel K₂)))
    (distinct : first ≠ second) (madeDistinct : made₁ ≠ made₂)
    (present₁ : first ∈ C.present) (present₂ : second ∈ C.present)
    (fresh₁ : made₁ ∉ C.present) (fresh₂ : made₂ ∉ C.present)
    {σ₀ : PSubst} (known : nameAction.Models σ₀ C.equations) (unifies : NameLaws (psubst σ₀ t) (psubst σ₀ u))
    {ρ : PSubst} (opensFreshly : (commAtN ρ first second made₁ made₂).Fresh QN (embed label C)) :
    (RuleSyntax.step QN O QNE program).Admits (s := embed label C) (commAtN ρ first second made₁ made₂) := by
  let h : PSubst := commInstance (psubst σ₀ t) (psubst σ₀ u) (psubst σ₀ channel) (psubst σ₀ K₁) (psubst σ₀ K₂)
  obtain ⟨w, solved, -, -⟩ := Comm.information_amalgamates_matched (Y := QN) (s := embed label C)
    (commAtN ρ first second made₁ made₂) opensFreshly (b := PUnit.unit) σ₀ h known
    (fun e member => by
      obtain rfl := List.mem_singleton.mp member
      show NameLaws (psubst h firstPattern) (psubst h secondPattern)
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
      · show NameLaws (psubst h (pFor firstPattern channelUnknown firstBody)) (psubst σ₀ (label first))
        rw [psubst_pFor, commInstance_firstPattern, commInstance_channel, commInstance_firstBody]
        exact (readsFirst σ₀ known).symm
      · obtain rfl := List.mem_singleton.mp member
        show NameLaws (psubst h (pFor secondPattern channelUnknown secondBody)) (psubst σ₀ (label second))
        rw [psubst_pFor, commInstance_secondPattern, commInstance_channel, commInstance_secondBody]
        exact (readsSecond σ₀ known).symm)
    (fun _ member => (List.not_mem_nil member).elim)
  refine (RuleSyntax.admits_iff _).mpr ⟨opensFreshly,
    ⟨by simp [commAtN, commSelection, distinct], by simp [commAtN, commSelection, madeDistinct],
      rfl, rfl, rfl, rfl⟩,
    ⟨?_, ?_, ?_, ?_, fun query member => by simp [Selection.commit] at member⟩,
    ⟨PUnit.unit, w, solved⟩, fun _ member => (List.not_mem_nil member).elim,
    fun _ member => (List.not_mem_nil member).elim⟩
  · intro o member
    simp only [commAtN, commSelection, Selection.commit, List.toFinset_cons, List.toFinset_nil,
      insert_empty_eq, Finset.mem_insert, Finset.mem_singleton] at member
    rcases member with rfl | rfl
    · exact present₁
    · exact present₂
  · intro o member
    simp [commAtN, commSelection, Selection.commit] at member
  · simp [commAtN, commSelection, Selection.commit]
  · rw [Finset.disjoint_left]
    intro o member
    simp only [commAtN, commSelection, Selection.commit, List.toFinset_cons, List.toFinset_nil,
      insert_empty_eq, Finset.mem_insert, Finset.mem_singleton] at member
    rcases member with rfl | rfl
    · exact fresh₁
    · exact fresh₂

/-- **What every solution modulo the name laws says after the COMM firing**: it solves the knowledge before,
unifies the patterns modulo the name laws, and reads each made row as the continuation its taken row holds,
modulo the name laws. -/
theorem comm_reads_name [DecidableEq O] (label : O → Pattern) (t u channel₁ channel₂ K₁ K₂ : Pattern)
    (C : Configuration Pattern O) (first second made₁ made₂ : O)
    (readsFirst : ∀ σ : PSubst, nameAction.Models σ C.equations →
      NameLaws (psubst σ (label first)) (psubst σ (pFor t channel₁ K₁)))
    (readsSecond : ∀ σ : PSubst, nameAction.Models σ C.equations →
      NameLaws (psubst σ (label second)) (psubst σ (pFor u channel₂ K₂)))
    (madeDistinct : made₁ ≠ made₂) (ρ : PSubst) {σ : PSubst}
    (solved : nameAction.Models σ ((commAtN ρ first second made₁ made₂).result QN (embed label C)).knowledge) :
    nameAction.Models σ C.equations ∧ NameLaws (psubst σ t) (psubst σ u) ∧
      NameLaws (psubst σ (((commAtN ρ first second made₁ made₂).result QN (embed label C)).label made₁))
        (psubst σ K₁) ∧
      NameLaws (psubst σ (((commAtN ρ first second made₁ made₂).result QN (embed label C)).label made₂))
        (psubst σ K₂) := by
  have info : ((commAtN ρ first second made₁ made₂).result QN (embed label C)).knowledge =
      (commAtN ρ first second made₁ made₂).information QN (embed label C) := rfl
  rw [info, commAtN_information] at solved
  have known : nameAction.Models σ C.equations := fun e member => solved e (by simp [member])
  have take₁ : NameLaws (psubst σ (psubst ρ (pFor firstPattern channelUnknown firstBody))) (psubst σ (label first)) :=
    solved (psubst ρ (pFor firstPattern channelUnknown firstBody), label first) (by simp)
  have take₂ : NameLaws (psubst σ (psubst ρ (pFor secondPattern channelUnknown secondBody)))
      (psubst σ (label second)) :=
    solved (psubst ρ (pFor secondPattern channelUnknown secondBody), label second) (by simp)
  have told : NameLaws (psubst σ (psubst ρ firstPattern)) (psubst σ (psubst ρ secondPattern)) :=
    solved (psubst ρ firstPattern, psubst ρ secondPattern) (by simp)
  have row₁ := take₁.trans (readsFirst σ known)
  have row₂ := take₂.trans (readsSecond σ known)
  simp only [psubst_pFor] at row₁ row₂
  obtain ⟨pattern₁, -, body₁⟩ := nameLaws_pFor_iff.mp row₁
  obtain ⟨pattern₂, -, body₂⟩ := nameLaws_pFor_iff.mp row₂
  refine ⟨known, pattern₁.symm.trans (told.trans pattern₂), ?_, ?_⟩
  · rw [commAtN_label₁]
    exact body₁
  · rw [commAtN_label₂ label C ρ first second madeDistinct]
    exact body₂

/-- **COMM as one firing of the finite program at the name frame.** Under the side conditions of
`FiniteProgram.comm_one_firing`, read modulo the name laws (a ground principal unifier `gp`, the variable
convention, first-order continuations, rows that read as the represented inputs modulo the name laws at every
solution, distinct made identities that are not present, some solution unifying the patterns modulo the name
laws, a fresh opening), and H-REFL1's named hypothesis that the written patterns have ground bags and are
canonical: the firing is admitted, the manuscript's COMM relates the redex to its dotted reduct, and every
solution of the result reads the made rows as the representations of the dotted continuations, modulo the
name laws. -/
theorem comm_one_firing_name [DecidableEq O] (label : O → Pattern) (t u channel A B : Pattern) (bs : Bindings)
    (gp : GroundPrincipal t u bs) (convention : Apart t A u B)
    (foA : firstOrder A = true) (foB : firstOrder B = true)
    (groundT : groundBags t = true) (groundU : groundBags u = true)
    (canonicalT : bagCanon t = t) (canonicalU : bagCanon u = u)
    (C : Configuration Pattern O) (first second made₁ made₂ : O)
    (readsFirst : ∀ σ : PSubst, nameAction.Models σ C.equations →
      NameLaws (psubst σ (label first)) (psubst σ (predot (pFor t channel A))))
    (readsSecond : ∀ σ : PSubst, nameAction.Models σ C.equations →
      NameLaws (psubst σ (label second)) (psubst σ (predot (pFor u channel B))))
    (distinct : first ≠ second) (madeDistinct : made₁ ≠ made₂)
    (present₁ : first ∈ C.present) (present₂ : second ∈ C.present)
    (fresh₁ : made₁ ∉ C.present) (fresh₂ : made₂ ∉ C.present)
    (glued : ∃ σ₀ : PSubst, nameAction.Models σ₀ C.equations ∧ NameLaws (psubst σ₀ t) (psubst σ₀ u))
    {ρ : PSubst} (opensFreshly : (commAtN ρ first second made₁ made₂).Fresh QN (embed label C)) :
    (RuleSyntax.step QN O QNE program).Admits (s := embed label C) (commAtN ρ first second made₁ made₂) ∧
      MeTTaCalculus.ReflectionClosure.Step GroundPrincipal SC (par (pFor t channel A) (pFor u channel B))
        (par (applyDot bs A) (applyDot bs B)) ∧
      MeTTaCalculus.Corrected.Step MeTTaCalculus.Corrected.conventional
        (par (pFor t channel A) (pFor u channel B)) (par (applyDot bs A) (applyDot bs B)) ∧
      ∀ σ : PSubst, nameAction.Models σ
          ((commAtN ρ first second made₁ made₂).result QN (embed label C)).knowledge →
        NameLaws (psubst σ (((commAtN ρ first second made₁ made₂).result QN (embed label C)).label made₁))
            (psubst σ (predot (applyDot bs A))) ∧
          NameLaws (psubst σ (((commAtN ρ first second made₁ made₂).result QN (embed label C)).label made₂))
            (psubst σ (predot (applyDot bs B))) := by
  obtain ⟨σ₀, known, unifies⟩ := glued
  have rowFirst : ∀ σ : PSubst, nameAction.Models σ C.equations →
      NameLaws (psubst σ (label first)) (psubst σ (pFor t (predot channel) (dotted (pvars t) (predot A)))) :=
    fun σ solved => by
      have read := readsFirst σ solved
      rw [predot_pFor] at read
      exact read
  have rowSecond : ∀ σ : PSubst, nameAction.Models σ C.equations →
      NameLaws (psubst σ (label second)) (psubst σ (pFor u (predot channel) (dotted (pvars u) (predot B)))) :=
    fun σ solved => by
      have read := readsSecond σ solved
      rw [predot_pFor] at read
      exact read
  refine ⟨comm_admits_name label t u (predot channel) (dotted (pvars t) (predot A)) (dotted (pvars u) (predot B))
      C first second made₁ made₂ rowFirst rowSecond distinct madeDistinct present₁ present₂ fresh₁ fresh₂ known
      unifies opensFreshly,
    .comm t u channel A B bs gp,
    .comm t u channel A B bs (Comm.principal_of_groundPrincipal gp) convention, fun σ solved => ?_⟩
  obtain ⟨-, unify, body₁, body₂⟩ := comm_reads_name label t u (predot channel) (predot channel)
    (dotted (pvars t) (predot A)) (dotted (pvars u) (predot B)) C first second made₁ made₂ rowFirst rowSecond
    madeDistinct ρ solved
  have agrees := agrees_of_groundPrincipal gp groundT groundU canonicalT canonicalU (bagLaws_of_nameLaws unify)
  obtain ⟨keptA, keptB⟩ := keys_of_apart convention
  refine ⟨body₁.trans ?_, body₂.trans ?_⟩
  · refine dotted_reads_predot_name gp.keys gp.covers agrees A foA (fun x inside => List.mem_append_left _ inside)
      ?_ keptA
    intro x inA inKeys
    rcases List.mem_append.mp inKeys with inT | inU
    · exact inT
    · exact absurd inA (convention.rightOutside x inU)
  · refine dotted_reads_predot_name gp.keys gp.covers agrees B foB (fun x inside => List.mem_append_right _ inside)
      ?_ keptB
    intro x inB inKeys
    rcases List.mem_append.mp inKeys with inT | inU
    · exact absurd inB (convention.leftOutside x inT)
    · exact inU

/-- **Closed continuations read a fixed pattern, modulo the name laws.** Under the side conditions of
`comm_one_firing_name`, with each continuation's variables its own pattern's (`closedA`, `closedB`): every
solution reads the made rows as the manuscript's dotted continuations, modulo the name laws. -/
theorem comm_one_firing_closed_name [DecidableEq O] (label : O → Pattern) (t u channel A B : Pattern)
    (bs : Bindings) (gp : GroundPrincipal t u bs) (convention : Apart t A u B)
    (foA : firstOrder A = true) (foB : firstOrder B = true)
    (closedA : ∀ x ∈ pvars A, x ∈ pvars t) (closedB : ∀ x ∈ pvars B, x ∈ pvars u)
    (groundT : groundBags t = true) (groundU : groundBags u = true)
    (canonicalT : bagCanon t = t) (canonicalU : bagCanon u = u)
    (C : Configuration Pattern O) (first second made₁ made₂ : O)
    (readsFirst : ∀ σ : PSubst, nameAction.Models σ C.equations →
      NameLaws (psubst σ (label first)) (psubst σ (predot (pFor t channel A))))
    (readsSecond : ∀ σ : PSubst, nameAction.Models σ C.equations →
      NameLaws (psubst σ (label second)) (psubst σ (predot (pFor u channel B))))
    (distinct : first ≠ second) (madeDistinct : made₁ ≠ made₂)
    (present₁ : first ∈ C.present) (present₂ : second ∈ C.present)
    (fresh₁ : made₁ ∉ C.present) (fresh₂ : made₂ ∉ C.present)
    (glued : ∃ σ₀ : PSubst, nameAction.Models σ₀ C.equations ∧ NameLaws (psubst σ₀ t) (psubst σ₀ u))
    {ρ : PSubst} (opensFreshly : (commAtN ρ first second made₁ made₂).Fresh QN (embed label C)) :
    (RuleSyntax.step QN O QNE program).Admits (s := embed label C) (commAtN ρ first second made₁ made₂) ∧
      MeTTaCalculus.ReflectionClosure.Step GroundPrincipal SC (par (pFor t channel A) (pFor u channel B))
        (par (applyDot bs A) (applyDot bs B)) ∧
      ∀ σ : PSubst, nameAction.Models σ
          ((commAtN ρ first second made₁ made₂).result QN (embed label C)).knowledge →
        NameLaws (psubst σ (((commAtN ρ first second made₁ made₂).result QN (embed label C)).label made₁))
            (applyDot bs A) ∧
          NameLaws (psubst σ (((commAtN ρ first second made₁ made₂).result QN (embed label C)).label made₂))
            (applyDot bs B) := by
  obtain ⟨admitted, manuscript, -, reads⟩ := comm_one_firing_name label t u channel A B bs gp convention foA foB
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

/-- **The COMM transition at the name frame, with its result.** Under the side conditions of
`comm_one_firing_name` (no opening is assumed: a fresh one exists), the step of the finite program at the name
frame moves the embedded configuration to a state whose present rows replace the inputs by the made
identities, whose other labels are unchanged, whose knowledge has a solution, and every solution of whose
knowledge reads the made rows as the representations of the dotted continuations, modulo the name laws. -/
theorem comm_one_transition_name [DecidableEq O] (label : O → Pattern) (t u channel A B : Pattern) (bs : Bindings)
    (gp : GroundPrincipal t u bs) (convention : Apart t A u B)
    (foA : firstOrder A = true) (foB : firstOrder B = true)
    (groundT : groundBags t = true) (groundU : groundBags u = true)
    (canonicalT : bagCanon t = t) (canonicalU : bagCanon u = u)
    (C : Configuration Pattern O) (first second made₁ made₂ : O)
    (readsFirst : ∀ σ : PSubst, nameAction.Models σ C.equations →
      NameLaws (psubst σ (label first)) (psubst σ (predot (pFor t channel A))))
    (readsSecond : ∀ σ : PSubst, nameAction.Models σ C.equations →
      NameLaws (psubst σ (label second)) (psubst σ (predot (pFor u channel B))))
    (distinct : first ≠ second) (madeDistinct : made₁ ≠ made₂)
    (present₁ : first ∈ C.present) (present₂ : second ∈ C.present)
    (fresh₁ : made₁ ∉ C.present) (fresh₂ : made₂ ∉ C.present)
    (glued : ∃ σ₀ : PSubst, nameAction.Models σ₀ C.equations ∧ NameLaws (psubst σ₀ t) (psubst σ₀ u)) :
    ∃ s' : State (OneFrame.Terms Pattern) O, Succ (RuleSyntax.step QN O QNE program).toStep (embed label C) s' ∧
      s'.present = (C.present \ {first, second}) ∪ {made₁, made₂} ∧
      (∀ o, o ≠ made₁ → o ≠ made₂ → s'.label o = label o) ∧
      (∃ σ : PSubst, nameAction.Models σ s'.knowledge) ∧
      ∀ σ : PSubst, nameAction.Models σ s'.knowledge →
        NameLaws (psubst σ (s'.label made₁)) (psubst σ (predot (applyDot bs A))) ∧
          NameLaws (psubst σ (s'.label made₂)) (psubst σ (predot (applyDot bs B))) := by
  obtain ⟨ρ, opensFreshly⟩ := exists_fresh_opening label C first second made₁ made₂
  have freshN : (commAtN ρ first second made₁ made₂).Fresh QN (embed label C) := fresh_name opensFreshly
  obtain ⟨admitted, -, -, reads⟩ := comm_one_firing_name label t u channel A B bs gp convention foA foB groundT
    groundU canonicalT canonicalU C first second made₁ made₂ readsFirst readsSecond distinct madeDistinct
    present₁ present₂ fresh₁ fresh₂ glued freshN
  obtain ⟨_, σ, solvedσ⟩ := ((RuleSyntax.admits_iff _).mp admitted).2.2.2.1
  refine ⟨(commAtN ρ first second made₁ made₂).result QN (embed label C), ⟨_, admitted, rfl⟩, ?_,
    fun o other₁ other₂ => ?_, ⟨σ, solvedσ⟩, reads⟩
  · show fire C.present ((commSelection first second made₁ made₂).commit (T := Unit)) = _
    simp [fire, Selection.commit, commSelection]
  · have absent : o ∉ (commAtN ρ first second made₁ made₂).selection.made := by
      simp [commAtN, commSelection, other₁, other₂]
    exact (Firing.result_label_other (X := QN) (s := embed label C) _ absent).trans (psubst_none (label o))

#print axioms nameFiring
#print axioms fresh_name
#print axioms name_admits
#print axioms program_name_admits
#print axioms psubst_nameLaws_congr
#print axioms dotted_reads_predot_name
#print axioms nameLaws_pFor_iff
#print axioms comm_admits_name
#print axioms comm_reads_name
#print axioms comm_one_firing_name
#print axioms comm_one_firing_closed_name
#print axioms comm_one_transition_name

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.ReflNames
