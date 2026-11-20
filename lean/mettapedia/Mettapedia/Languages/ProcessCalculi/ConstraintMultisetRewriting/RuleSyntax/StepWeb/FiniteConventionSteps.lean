import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.FiniteConventionTame

/-!
# Steps respect alpha-equivalence, and the variable convention along runs

The step is the single-firing step of the three-rule `program` of `FiniteComm` at the one frame of structural
substitution on patterns, with the five choices stated there.

## Steps respect alpha-equivalence

* `step_respects_alpha`: the tree's corrected semantics (`Corrected.Step`) has the manuscript's EQUIV rule with
  alpha-equivalence; so alpha-equivalent sources have the same reducts, for every admission. Nothing is to prove.
  That EQUIV compares closed forms on all syntax, codes included: with the admission `conventional` it reaches a
  reduct with a code that is not alpha-equivalent to the manuscript's (`corrected_step_reaches_a_code` in
  `FiniteConventionControls`).
* The hosting's source `BagComm` takes the literal parts of a bag; it is not closed under alpha-equivalence. On
  tame bags it respects it (`bagComm_respects_alpha`): a COMM step of a tame alpha-variant of a tame hosted bag
  that satisfies the convention is matched by a COMM step of the bag itself, and the two dotted reducts are
  equal. The ingredients: a tame alpha-variant of a tame hosted part is hosted (`hosted_of_alphaEq`);
  alpha-equivalent tame hosted inputs are renamings of each other, read off their common canonical form
  (`hosted_alpha_renaming`); a ground principal unifier transports along a renaming injective on the patterns'
  variables (`groundPrincipal_of_rename`); the dot commutes with it (`applyDot_rename`).

## The convention along runs

* `Convention M`: every variable occurs in at most one part of the bag `M`.
* `bagComm_keeps_convention`: a COMM step of the bag presentation keeps the parts hosted and the convention: the
  dotted continuations of hosted inputs have no variable. In the corrected semantics the target of a step is
  determined only up to alpha-equivalence, and there a step need not keep the convention
  (`FiniteConventionControls`); renaming re-establishes it (`renaming_into_the_convention`).
* `CommUpToAlpha`: the manuscript's COMM on bags up to alpha-equivalence of the parts, from tame bags.
  `runs_up_to_alpha`: every run of it is matched by a run of the bag presentation from any tame hosted
  conventional alpha-variant of its start, with alpha-equivalent bags at every stage; the bags stay tame
  (`bagComm_keeps_tame`), hosted and under the convention. `hosted_runs_up_to_alpha`: for every tame process with
  hosted parts, every such run from its parts is matched by a run of the single-firing step from the initial
  state of the renamed process, ending at a state that represents an alpha-variant of the run's end.

Tameness is needed: `FiniteConventionControls` gives two alpha-equivalent processes, one of them with a code,
whose COMM reducts in the bag presentation are not alpha-equivalent.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.FiniteConvention

open Mettapedia.OSLF.MeTTaIL.Syntax (Pattern)
open Mettapedia.OSLF.MeTTaIL.Match (Bindings)
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus (pFor par pZero nQuote applyDot)
open MeTTaOperationsComm (psubst pvars firstOrder PSubst GroundPrincipal applyDot_eq)
open MeTTaCalculus.Corrected (binders Apart tame tameList tameFor tameList_iff tame_pFor canon canonList canonFor
  canonList_eq_map canon_pFor named canon_eq_named canonicalName canonicalName_injective AvoidsCanonical
  levelRename Alpha AlphaEq close closeIn frame frame_of_guardFree rename rename_apply rename_collection
  rename_rename rename_of_fixed rename_congr pvars_rename psubst_rename psubst_getD_congr_on freshName
  freshName_not_mem pvars_pFor asGuard asGuard_closeIn closeIn_pFor alpha_alphaEq calcTerm_rename
  guardFree_rename)
open FiniteProgram (parts Hosted HostedProcess BagComm IsPar pFor_inj hosted_applyDot bagOf RepresentsBy Represents
  parts_par parts_pFor eq_of_mem_parts_of_not_par pvars_of_mem_parts mem_keys_of_lookup program Communicates
  Administers communication_complete succ_iff succ_of_administers initial initial_represents)
open Comm (Tm X E)
open LogicOverTheStep.StepSpan (Succ)

/-! ## The corrected step respects alpha-equivalence -/

/-- **The corrected step respects alpha-equivalence.** Its EQUIV rule (`Corrected.Step.congruence`) closes it
under alpha-equivalence of the source, for every admission: alpha-equivalent sources have the same reducts. -/
theorem step_respects_alpha {admission : MeTTaCalculus.Corrected.Admission} {P P' Q : Pattern}
    (same : AlphaEq P P') (step : MeTTaCalculus.Corrected.Step admission P Q) :
    MeTTaCalculus.Corrected.Step admission P' Q :=
  .congruence (MeTTaCalculus.Corrected.AlphaEq.symm same) step (MeTTaCalculus.Corrected.AlphaEq.refl Q)

/-- The same for the manuscript's renaming rule. -/
theorem step_respects_renaming {admission : MeTTaCalculus.Corrected.Admission} {P P' Q : Pattern}
    (alpha : Alpha P P') (step : MeTTaCalculus.Corrected.Step admission P Q) :
    MeTTaCalculus.Corrected.Step admission P' Q :=
  step_respects_alpha (alpha_alphaEq alpha) step

/-! ## Inverting a renaming on a list -/

/-- An inverse of `g` on the list `l`: the first member of `l` that `g` sends to `w`, if any. -/
def invOn (g : String → String) (l : List String) (w : String) : String :=
  (l.find? fun v => g v == w).getD w

theorem invOn_apply {g : String → String} {l : List String} (inj : ∀ a ∈ l, ∀ b ∈ l, g a = g b → a = b)
    {v : String} (member : v ∈ l) : invOn g l (g v) = v := by
  unfold invOn
  cases found : l.find? (fun w => g w == g v) with
  | none =>
      exfalso
      have := List.find?_eq_none.mp found v member
      simp at this
  | some w =>
      have wIn := List.mem_of_find?_eq_some found
      have same := List.find?_some found
      simp only [beq_iff_eq] at same
      exact inj w wIn v member same

theorem rename_invOn {g : String → String} {l : List String} (inj : ∀ a ∈ l, ∀ b ∈ l, g a = g b → a = b)
    {p : Pattern} (inside : ∀ v ∈ pvars p, v ∈ l) : rename (invOn g l) (rename g p) = p := by
  rw [rename_rename]
  exact rename_of_fixed _ p fun v occurs => invOn_apply inj (inside v occurs)

/-- **A renaming injective on the variables cancels.** -/
theorem rename_cancel {g : String → String} {l : List String} (inj : ∀ a ∈ l, ∀ b ∈ l, g a = g b → a = b)
    {p q : Pattern} (insideP : ∀ v ∈ pvars p, v ∈ l) (insideQ : ∀ v ∈ pvars q, v ∈ l)
    (same : rename g p = rename g q) : p = q := by
  rw [← rename_invOn inj insideP, same, rename_invOn inj insideQ]

theorem levelRename_injOn (n : ℕ → ℕ → String) (inj : ∀ L i L' i', n L i = n L' i' → L = L' ∧ i = i') (D : ℕ)
    (l : List String) : ∀ a ∈ l, ∀ b ∈ l, levelRename n D l a = levelRename n D l b → a = b := by
  intro a ha b hb same
  simp only [levelRename, if_pos ha, if_pos hb] at same
  exact (List.idxOf_inj ha).mp (inj _ _ _ _ same).2

/-! ## Ground principal unifiers along a renaming -/

theorem lookup_graph (vs : List String) (f : String → Pattern) (x : String) :
    Bindings.lookup (vs.map fun v => (v, f v)) x = if x ∈ vs then some (f x) else none := by
  induction vs with
  | nil => rfl
  | cons w ws ih =>
      by_cases same : w = x
      · subst same; simp [Bindings.lookup]
      · have : (w == x) = false := by simpa using same
        simp only [List.map_cons, List.mem_cons]
        unfold Bindings.lookup at ih ⊢
        simp only [List.find?_cons, this, ih, Ne.symm same, false_or]

/-- **A ground principal unifier transports along a renaming injective on the patterns' variables.** The unifier
of the renamed patterns, read back through the renaming, is a ground principal unifier of the patterns. -/
theorem groundPrincipal_of_rename {t u : Pattern} {G : String → String} {bs' : Bindings}
    (inj : ∀ a ∈ pvars t ++ pvars u, ∀ b ∈ pvars t ++ pvars u, G a = G b → a = b)
    (gp : GroundPrincipal (rename G t) (rename G u) bs') :
    ∃ bs : Bindings, GroundPrincipal t u bs ∧ ∀ v ∈ pvars t ++ pvars u, bs.lookup v = bs'.lookup (G v) := by
  have mapped : ∀ v ∈ pvars t ++ pvars u, G v ∈ pvars (rename G t) ++ pvars (rename G u) := by
    intro v member
    rw [pvars_rename, pvars_rename, ← List.map_append]
    exact List.mem_map_of_mem member
  have value : ∀ v ∈ pvars t ++ pvars u, ∃ w, bs'.lookup (G v) = some w ∧ pvars w = [] := fun v member =>
    gp.covers (G v) (mapped v member)
  obtain ⟨bs, look, keys⟩ : ∃ bs : Bindings, (∀ v ∈ pvars t ++ pvars u, bs.lookup v = bs'.lookup (G v)) ∧
      ∀ e ∈ bs, e.1 ∈ pvars t ++ pvars u :=
    ⟨(pvars t ++ pvars u).map fun v => (v, (bs'.lookup (G v)).getD (.fvar v)), fun v member => by
      rw [lookup_graph, if_pos member]
      obtain ⟨w, found, -⟩ := value v member
      simp [found], fun e member => by
      obtain ⟨v, inVs, rfl⟩ := List.mem_map.mp member
      exact inVs⟩
  have agree : ∀ p : Pattern, (∀ v ∈ pvars p, v ∈ pvars t ++ pvars u) →
      psubst bs.lookup p = psubst bs'.lookup (rename G p) := by
    intro p inside
    rw [psubst_rename]
    apply psubst_getD_congr_on
    intro v occurs
    obtain ⟨w, found, -⟩ := value v (inside v occurs)
    rw [look v (inside v occurs)]
    simp [psubst, found]
  refine ⟨bs, ⟨keys, fun v member => ?_, ?_, ?_⟩, look⟩
  · obtain ⟨w, found, closed⟩ := value v member
    exact ⟨w, (look v member).trans found, closed⟩
  · rw [agree t fun v occurs => List.mem_append_left _ occurs,
      agree u fun v occurs => List.mem_append_right _ occurs]
    exact gp.solves
  · intro σ solves v member w found
    let τ : PSubst := fun z => some (psubst σ (.fvar (invOn G (pvars t ++ pvars u) z)))
    have back : ∀ p : Pattern, (∀ v ∈ pvars p, v ∈ pvars t ++ pvars u) → psubst τ (rename G p) = psubst σ p := by
      intro p inside
      rw [psubst_rename]
      apply psubst_getD_congr_on
      intro v occurs
      show psubst σ (.fvar (invOn G (pvars t ++ pvars u) (G v))) = psubst σ (.fvar v)
      rw [invOn_apply inj (inside v occurs)]
    have unifies : psubst τ (rename G t) = psubst τ (rename G u) := by
      rw [back t fun v occurs => List.mem_append_left _ occurs,
        back u fun v occurs => List.mem_append_right _ occurs]
      exact solves
    have read := gp.principal τ unifies (G v) (mapped v member) w ((look v member).symm.trans found)
    rw [← read]
    show psubst σ (.fvar v) = psubst σ (.fvar (invOn G (pvars t ++ pvars u) (G v)))
    rw [invOn_apply inj member]

/-- **The dot commutes with a renaming** of the continuation's variables, when the two binding lists agree along
it and bind every variable of the continuation. -/
theorem applyDot_rename {bs bs' : Bindings} {G : String → String} {A : Pattern} (fo : firstOrder A = true)
    (agree : ∀ v ∈ pvars A, ∃ w, bs.lookup v = some w ∧ bs'.lookup (G v) = some w) :
    applyDot bs' (rename G A) = applyDot bs A := by
  rw [applyDot_eq bs' _ (firstOrder_rename G A fo), applyDot_eq bs A fo, psubst_rename]
  apply psubst_getD_congr_on
  intro v occurs
  obtain ⟨w, found, found'⟩ := agree v occurs
  simp [psubst, found, found']

/-! ## Alpha-equivalent hosted inputs are renamings of each other -/

/-- Only an input is alpha-equivalent to an input. -/
theorem input_of_alphaEq {c t x A : Pattern} (same : AlphaEq c (pFor t x A)) : ∃ t₀ x₀ A₀, c = pFor t₀ x₀ A₀ := by
  have found : asGuard (closeIn [] c) = some (closeIn [frame t] t, closeIn [] x, closeIn [frame t] A) := by
    show asGuard (close c) = _
    rw [show close c = close (pFor t x A) from same]
    show asGuard (closeIn [] (pFor t x A)) = _
    rw [closeIn_pFor]
    rfl
  obtain ⟨t₀, x₀, A₀, rfl, -⟩ := asGuard_closeIn found
  exact ⟨t₀, x₀, A₀, rfl⟩

/-- **Alpha-equivalent tame hosted inputs are renamings of each other.** They have one channel, and a renaming
injective on the first pattern's variables carries its pattern and its continuation to the second's. It is read
off their common canonical form. -/
theorem hosted_alpha_renaming {t x A t' x' A' : Pattern}
    (tame₁ : tame (pFor t x A) = true) (tame₂ : tame (pFor t' x' A') = true)
    (hosted₁ : Hosted (pFor t x A)) (hosted₂ : Hosted (pFor t' x' A'))
    (same : AlphaEq (pFor t x A) (pFor t' x' A')) :
    x' = x ∧ ∃ G : String → String, (∀ a ∈ pvars t, ∀ b ∈ pvars t, G a = G b → a = b) ∧
      rename G t = t' ∧ rename G A = A' := by
  let n := canonicalName (pvars (pFor t x A) ++ pvars (pFor t' x' A'))
  have inj := canonicalName_injective (pvars (pFor t x A) ++ pvars (pFor t' x' A'))
  have fresh₁ : AvoidsCanonical n (pvars (pFor t x A)) := fun v occurs L i eq =>
    freshName_not_mem (pvars (pFor t x A) ++ pvars (pFor t' x' A')) (Nat.pair L i) (by
      rw [show freshName (pvars (pFor t x A) ++ pvars (pFor t' x' A')) (Nat.pair L i) = v from eq]
      exact List.mem_append_left _ occurs)
  have fresh₂ : AvoidsCanonical n (pvars (pFor t' x' A')) := fun v occurs L i eq =>
    freshName_not_mem (pvars (pFor t x A) ++ pvars (pFor t' x' A')) (Nat.pair L i) (by
      rw [show freshName (pvars (pFor t x A) ++ pvars (pFor t' x' A')) (Nat.pair L i) = v from eq]
      exact List.mem_append_right _ occurs)
  have meet : canon n 0 (pFor t x A) = canon n 0 (pFor t' x' A') := by
    rw [canon_eq_named n _ tame₁ fresh₁, canon_eq_named n _ tame₂ fresh₂]
    exact congrArg (named n 0) same
  rw [canon_hosted_input n 0 hosted₁, canon_hosted_input n 0 hosted₂] at meet
  obtain ⟨patterns, channels, bodies⟩ := pFor_inj meet
  obtain ⟨-, freeT, -, -⟩ := tame_pFor.mp tame₁
  obtain ⟨-, freeT', -, -⟩ := tame_pFor.mp tame₂
  rw [frame_of_guardFree t freeT, frame_of_guardFree t' freeT'] at patterns bodies
  obtain ⟨-, closed₁, -, -⟩ := hosted₁.input
  obtain ⟨-, closed₂, -, -⟩ := hosted₂.input
  let h := levelRename n 0 (pvars t)
  let h' := levelRename n 0 (pvars t')
  have injH : ∀ a ∈ pvars t, ∀ b ∈ pvars t, h a = h b → a = b := levelRename_injOn n inj 0 (pvars t)
  have injH' : ∀ a ∈ pvars t', ∀ b ∈ pvars t', h' a = h' b → a = b := levelRename_injOn n inj 0 (pvars t')
  have images : (pvars t).map h = (pvars t').map h' := by
    have := congrArg pvars patterns
    rwa [pvars_rename, pvars_rename] at this
  let G : String → String := fun v => invOn h' (pvars t') (h v)
  have hit : ∀ v ∈ pvars t, G v ∈ pvars t' ∧ h' (G v) = h v := by
    intro v member
    have inImage : h v ∈ (pvars t').map h' := by
      rw [← images]
      exact List.mem_map_of_mem member
    obtain ⟨w, wIn, hw⟩ := List.mem_map.mp inImage
    have back : G v = w := by
      show invOn h' (pvars t') (h v) = w
      rw [← hw]
      exact invOn_apply injH' wIn
    exact ⟨back ▸ wIn, by rw [back, hw]⟩
  have moved : ∀ p : Pattern, (∀ v ∈ pvars p, v ∈ pvars t) → rename h' (rename G p) = rename h p := by
    intro p inside
    rw [rename_rename]
    exact rename_congr fun v occurs => (hit v (inside v occurs)).2
  have landed : ∀ p : Pattern, (∀ v ∈ pvars p, v ∈ pvars t) → ∀ v ∈ pvars (rename G p), v ∈ pvars t' := by
    intro p inside v occurs
    rw [pvars_rename] at occurs
    obtain ⟨w, wIn, rfl⟩ := List.mem_map.mp occurs
    exact (hit w (inside w wIn)).1
  refine ⟨channels.symm, G, fun a ha b hb same => injH a ha b hb ?_, ?_, ?_⟩
  · rw [← (hit a ha).2, ← (hit b hb).2, same]
  · exact rename_cancel injH' (landed t fun _ occurs => occurs) (fun _ occurs => occurs)
      ((moved t fun _ occurs => occurs).trans patterns)
  · exact rename_cancel injH' (landed A closed₁) closed₂ ((moved A closed₁).trans bodies)

/-! ## The variable convention on a bag -/

/-- **The variable convention across the parts of a bag**: every variable occurs in at most one part. -/
def Convention (M : Multiset Pattern) : Prop := ∀ y : String, (M.filter fun c => y ∈ pvars c).card ≤ 1

/-- Two parts of a bag under the convention share no variable. -/
theorem Convention.disjoint {c d : Pattern} {rest : Multiset Pattern} (convention : Convention (c ::ₘ d ::ₘ rest))
    {y : String} (inC : y ∈ pvars c) (inD : y ∈ pvars d) : False := by
  have bound := convention y
  rw [Multiset.filter_cons_of_pos (p := fun c => y ∈ pvars c) _ inC,
    Multiset.filter_cons_of_pos (p := fun c => y ∈ pvars c) _ inD] at bound
  simp only [Multiset.card_cons] at bound
  omega

/-- **The convention of a hosted process**: its parts pairwise share no variable. -/
theorem convention_of_pairwise : ∀ (L : List Pattern), L.Pairwise (fun c d => ∀ y ∈ pvars c, y ∉ pvars d) →
    Convention (L : Multiset Pattern)
  | [], _ => fun y => by simp
  | a :: L, pairwise => by
      intro y
      rw [List.pairwise_cons] at pairwise
      have rest := convention_of_pairwise L pairwise.2 y
      rw [← Multiset.cons_coe]
      by_cases inA : y ∈ pvars a
      · rw [Multiset.filter_cons_of_pos (p := fun c => y ∈ pvars c) _ inA, Multiset.card_cons]
        have none : ((L : Multiset Pattern).filter fun c => y ∈ pvars c) = 0 :=
          Multiset.filter_eq_nil.mpr fun d member inD => pairwise.1 d (Multiset.mem_coe.mp member) y inA inD
        rw [none]
        simp
      · rw [Multiset.filter_cons_of_neg (p := fun c => y ∈ pvars c) _ inA]
        exact rest

theorem firstOrder_of_mem_parts (p : Pattern) : ∀ c ∈ parts p, firstOrder p = true → firstOrder c = true := by
  induction p using Pattern.rec
    (motive_2 := fun ps => ∀ q ∈ ps, ∀ c ∈ parts q, firstOrder q = true → firstOrder c = true) with
  | collection ct elems rest ih =>
      intro c member fo
      by_cases isPar : IsPar (.collection ct elems rest)
      · obtain ⟨a, b, same⟩ := isPar
        simp only [par, MeTTaCalculus.pPar, Pattern.collection.injEq] at same
        obtain ⟨rfl, rfl, rfl⟩ := same
        rw [show Pattern.collection .hashBag [a, b] none = par a b from rfl] at member fo
        rw [parts_par] at member
        obtain ⟨foA, foB⟩ := FiniteProgram.firstOrder_par.mp fo
        rcases List.mem_append.mp member with inA | inB
        · exact ih a (by simp) c inA foA
        · exact ih b (by simp) c inB foB
      · rw [eq_of_mem_parts_of_not_par isPar member]
        exact fo
  | bvar n =>
      intro c member fo
      rw [eq_of_mem_parts_of_not_par (by rintro ⟨a, b, same⟩; cases same) member]
      exact fo
  | fvar x =>
      intro c member fo
      rw [eq_of_mem_parts_of_not_par (by rintro ⟨a, b, same⟩; cases same) member]
      exact fo
  | apply f args ih =>
      intro c member fo
      rw [eq_of_mem_parts_of_not_par (by rintro ⟨a, b, same⟩; cases same) member]
      exact fo
  | lambda nm body ih =>
      intro c member fo
      rw [eq_of_mem_parts_of_not_par (by rintro ⟨a, b, same⟩; cases same) member]
      exact fo
  | multiLambda n nms body ih =>
      intro c member fo
      rw [eq_of_mem_parts_of_not_par (by rintro ⟨a, b, same⟩; cases same) member]
      exact fo
  | subst body repl ihb ihr =>
      intro c member fo
      rw [eq_of_mem_parts_of_not_par (by rintro ⟨a, b, same⟩; cases same) member]
      exact fo
  | nil => simp_all
  | cons p ps head tail =>
      rename_i q member c inC foQ
      rcases List.mem_cons.mp member with rfl | later
      · exact head c inC foQ
      · exact tail q later c inC foQ

/-- **The parts of a hosted part are hosted.** -/
theorem hosted_of_mem_parts {p c : Pattern} (hosted : Hosted p) (member : c ∈ parts p) : Hosted c := by
  rcases hosted.2 with ground | ⟨t, x, A, rfl, -⟩
  · refine ⟨firstOrder_of_mem_parts p c member hosted.1, .inl ?_⟩
    exact List.eq_nil_iff_forall_not_mem.mpr fun y inC => by
      have := pvars_of_mem_parts p c member y inC
      rw [ground] at this
      exact List.not_mem_nil this
  · rw [parts_pFor, List.mem_singleton] at member
    subst member
    exact hosted

/-- A hosted part has at most one part with a given variable. -/
theorem card_filter_parts_le_one {c : Pattern} (hosted : Hosted c) (y : String) :
    ((parts c : Multiset Pattern).filter fun d => y ∈ pvars d).card ≤ 1 := by
  rcases hosted.2 with ground | ⟨t, x, A, rfl, -⟩
  · have none : ((parts c : Multiset Pattern).filter fun d => y ∈ pvars d) = 0 := by
      rw [Multiset.filter_eq_nil]
      intro d member inD
      have := pvars_of_mem_parts c d (Multiset.mem_coe.mp member) y inD
      rw [ground] at this
      exact List.not_mem_nil this
    rw [none]
    simp
  · rw [parts_pFor]
    exact (Multiset.card_le_card (Multiset.filter_le _ _)).trans (by simp)

theorem card_filter_bagOf (p : Pattern → Prop) [DecidablePred p] (comp : ℕ → Pattern) (S : Finset ℕ) :
    ((bagOf S comp).filter p).card = ∑ o ∈ S, ((parts (comp o) : Multiset Pattern).filter p).card := by
  unfold bagOf
  induction S using Finset.induction_on with
  | empty => simp
  | insert a S notMem ih =>
      rw [Finset.sum_insert notMem, Finset.sum_insert notMem, Multiset.filter_add, Multiset.card_add, ih]

/-- **A represented bag is hosted.** -/
theorem representsBy_hosted {s : State Tm ℕ} {M : Multiset Pattern} {comp : ℕ → Pattern}
    (represented : RepresentsBy s M comp) : ∀ c ∈ M, Hosted c := by
  intro c member
  rw [← represented.bag] at member
  unfold bagOf at member
  obtain ⟨o, present, inParts⟩ := Multiset.mem_sum.mp member
  exact hosted_of_mem_parts (represented.hosted o present) (Multiset.mem_coe.mp inParts)

/-- **A represented bag satisfies the convention.** -/
theorem representsBy_convention {s : State Tm ℕ} {M : Multiset Pattern} {comp : ℕ → Pattern}
    (represented : RepresentsBy s M comp) : Convention M := by
  intro y
  rw [← represented.bag, card_filter_bagOf]
  by_cases found : ∃ o ∈ s.present, y ∈ pvars (comp o)
  · obtain ⟨o, present, inside⟩ := found
    rw [Finset.sum_eq_single o (fun o' present' different => ?_) (fun missing => absurd present missing)]
    · exact card_filter_parts_le_one (represented.hosted o present) y
    · rw [Multiset.card_eq_zero, Multiset.filter_eq_nil]
      intro d member inD
      exact represented.apart_vars present present' (Ne.symm different) inside
        (pvars_of_mem_parts _ d (Multiset.mem_coe.mp member) y inD)
  · rw [Finset.sum_eq_zero fun o present => ?_]
    · simp
    · rw [Multiset.card_eq_zero, Multiset.filter_eq_nil]
      intro d member inD
      exact found ⟨o, present, pvars_of_mem_parts _ d (Multiset.mem_coe.mp member) y inD⟩

/-! ## The bag presentation respects alpha-equivalence on tame hosted bags -/

/-- A part matched by its closed form. -/
theorem exists_match {M : Multiset Pattern} {b : Pattern} {N₀ : Multiset Pattern}
    (same : M.map close = (b ::ₘ N₀).map close) :
    ∃ a M₀, M = a ::ₘ M₀ ∧ AlphaEq a b ∧ M₀.map close = N₀.map close := by
  rw [Multiset.map_cons] at same
  have member : close b ∈ M.map close := by
    rw [same]
    exact Multiset.mem_cons_self _ _
  obtain ⟨a, inM, closeA⟩ := Multiset.mem_map.mp member
  refine ⟨a, M.erase a, (Multiset.cons_erase inM).symm, closeA, ?_⟩
  have split : M.map close = close a ::ₘ (M.erase a).map close := by
    conv_lhs => rw [← Multiset.cons_erase inM]
    rw [Multiset.map_cons]
  rw [split, closeA] at same
  exact (Multiset.cons_inj_right _).mp same

/-- **The bag presentation respects alpha-equivalence on tame bags.** Let `M` be a bag of tame hosted parts under
the convention, and `N` a bag of tame parts with the same closed forms. Every COMM step of `N` is matched by a COMM
step of `M`, to a bag with the same closed forms whose every part is a part of `M` or of the target: the dotted
reducts are equal. -/
theorem bagComm_respects_alpha {M N N' : Multiset Pattern}
    (tameM : ∀ c ∈ M, tame c = true) (hostedM : ∀ c ∈ M, Hosted c) (conventionM : Convention M)
    (tameN : ∀ c ∈ N, tame c = true) (same : M.map close = N.map close) (step : BagComm N N') :
    ∃ M', BagComm M M' ∧ M'.map close = N'.map close ∧ ∀ c ∈ M', c ∈ M ∨ c ∈ N' := by
  obtain ⟨t', u', x, A', B', bs', rest', gp', apart', values'⟩ := step
  obtain ⟨c₁, M₁, rfl, alpha₁, same₁⟩ := exists_match same
  obtain ⟨c₂, rest, rfl, alpha₂, sameRest⟩ := exists_match same₁
  obtain ⟨t, x₁, A, rfl⟩ := input_of_alphaEq alpha₁
  obtain ⟨u, x₂, B, rfl⟩ := input_of_alphaEq alpha₂
  have inFirst : ∀ {a b : Pattern} {r : Multiset Pattern}, a ∈ a ::ₘ b ::ₘ r := Multiset.mem_cons_self _ _
  have inSecond : ∀ {a b : Pattern} {r : Multiset Pattern}, b ∈ a ::ₘ b ::ₘ r :=
    Multiset.mem_cons_of_mem (Multiset.mem_cons_self _ _)
  obtain ⟨chan₁, G₁, inj₁, patT, bodyA⟩ := hosted_alpha_renaming (tameM _ inFirst) (tameN _ inFirst)
    (hostedM _ inFirst) (hosted_of_alphaEq (tameM _ inFirst) (tameN _ inFirst) (hostedM _ inFirst) alpha₁) alpha₁
  obtain ⟨chan₂, G₂, inj₂, patU, bodyB⟩ := hosted_alpha_renaming (tameM _ inSecond) (tameN _ inSecond)
    (hostedM _ inSecond) (hosted_of_alphaEq (tameM _ inSecond) (tameN _ inSecond) (hostedM _ inSecond) alpha₂)
    alpha₂
  subst x₁ x₂
  subst patT bodyA patU bodyB
  obtain ⟨-, closedA, noA, foA⟩ := (hostedM _ inFirst).input
  obtain ⟨-, closedB, noB, foB⟩ := (hostedM _ inSecond).input
  -- the convention of `M` gives the convention of its redex
  have disjoint : ∀ v, v ∈ pvars (pFor t x A) → v ∉ pvars (pFor u x B) := fun v first second =>
    conventionM.disjoint first second
  have inC : ∀ v, v ∈ pvars t ∨ v ∈ pvars A → v ∈ pvars (pFor t x A) := by
    intro v occurs
    rw [pvars_pFor]
    rcases occurs with inT | inA'
    · exact List.mem_append_left _ (List.mem_append_left _ inT)
    · exact List.mem_append_right _ inA'
  have inD : ∀ v, v ∈ pvars u ∨ v ∈ pvars B → v ∈ pvars (pFor u x B) := by
    intro v occurs
    rw [pvars_pFor]
    rcases occurs with inU | inB'
    · exact List.mem_append_left _ (List.mem_append_left _ inU)
    · exact List.mem_append_right _ inB'
  have apart : Apart t A u B :=
    ⟨fun v inT inU => disjoint v (inC v (.inl inT)) (inD v (.inl inU)),
      fun v inT inB => disjoint v (inC v (.inl inT)) (inD v (.inr inB)),
      fun v inU inA => disjoint v (inC v (.inr inA)) (inD v (.inl inU)),
      fun v _ bound => by rw [noA] at bound; exact List.not_mem_nil bound,
      fun v _ bound => by rw [noB] at bound; exact List.not_mem_nil bound⟩
  -- one renaming for both inputs
  let G : String → String := fun v => if v ∈ pvars t then G₁ v else G₂ v
  have onT : ∀ v ∈ pvars t, G v = G₁ v := fun v member => if_pos member
  have onU : ∀ v ∈ pvars u, G v = G₂ v := fun v member => if_neg fun inT => apart.patterns v inT member
  have renameT : rename G t = rename G₁ t := rename_congr onT
  have renameU : rename G u = rename G₂ u := rename_congr onU
  have injG : ∀ a ∈ pvars t ++ pvars u, ∀ b ∈ pvars t ++ pvars u, G a = G b → a = b := by
    intro a ha b hb sameG
    have crossed : ∀ a ∈ pvars t, ∀ b ∈ pvars u, G₁ a ≠ G₂ b := fun a ha b hb sameAB =>
      apart'.patterns (G₁ a) (by rw [pvars_rename]; exact List.mem_map_of_mem ha)
        (by rw [pvars_rename, sameAB]; exact List.mem_map_of_mem hb)
    rcases List.mem_append.mp ha with ta | ua <;> rcases List.mem_append.mp hb with tb | ub
    · rw [onT a ta, onT b tb] at sameG
      exact inj₁ a ta b tb sameG
    · rw [onT a ta, onU b ub] at sameG
      exact absurd sameG (crossed a ta b ub)
    · rw [onU a ua, onT b tb] at sameG
      exact absurd sameG.symm (crossed b tb a ua)
    · rw [onU a ua, onU b ub] at sameG
      exact inj₂ a ua b ub sameG
  have gpG : GroundPrincipal (rename G t) (rename G u) bs' := by
    rw [renameT, renameU]
    exact gp'
  obtain ⟨bs, gp, look⟩ := groundPrincipal_of_rename injG gpG
  have values : ∀ y v, bs.lookup y = some v → firstOrder v = true := by
    intro y v found
    have key := mem_keys_of_lookup gp.keys found
    exact values' (G y) v ((look y key).symm.trans found)
  have dotA : applyDot bs' (rename G₁ A) = applyDot bs A := by
    rw [← rename_congr (fun v occurs => onT v (closedA v occurs))]
    refine applyDot_rename foA fun v occurs => ?_
    obtain ⟨w, found, -⟩ := gp.covers v (List.mem_append_left _ (closedA v occurs))
    exact ⟨w, found, (look v (List.mem_append_left _ (closedA v occurs))).symm.trans found⟩
  have dotB : applyDot bs' (rename G₂ B) = applyDot bs B := by
    rw [← rename_congr (fun v occurs => onU v (closedB v occurs))]
    refine applyDot_rename foB fun v occurs => ?_
    obtain ⟨w, found, -⟩ := gp.covers v (List.mem_append_right _ (closedB v occurs))
    exact ⟨w, found, (look v (List.mem_append_right _ (closedB v occurs))).symm.trans found⟩
  refine ⟨_, BagComm.comm t u x A B bs rest gp apart values, ?_, ?_⟩
  · rw [dotA, dotB]
    simp only [Multiset.map_add, sameRest]
  · intro c member
    rw [dotA, dotB]
    rcases Multiset.mem_add.mp member with dotted | old
    · exact .inr (Multiset.mem_add.mpr (.inl dotted))
    · exact .inl (Multiset.mem_cons_of_mem (Multiset.mem_cons_of_mem old))

/-! ## The convention along runs -/

/-- **A COMM step of the bag presentation keeps the parts hosted and the convention**: the dotted continuations of
hosted inputs have no variable, and the other parts stay. -/
theorem bagComm_keeps_convention {M M' : Multiset Pattern} (step : BagComm M M')
    (hosted : ∀ c ∈ M, Hosted c) (convention : Convention M) :
    (∀ c ∈ M', Hosted c) ∧ Convention M' := by
  obtain ⟨t, u, x, A, B, bs, rest, gp, apart, values⟩ := step
  have hostedA := hosted (pFor t x A) (Multiset.mem_cons_self _ _)
  have hostedB := hosted (pFor u x B) (Multiset.mem_cons_of_mem (Multiset.mem_cons_self _ _))
  obtain ⟨-, closedA, -, foA⟩ := hostedA.input
  obtain ⟨-, closedB, -, foB⟩ := hostedB.input
  obtain ⟨hostedDotA, groundA⟩ :=
    hosted_applyDot gp values foA fun y inside => List.mem_append_left _ (closedA y inside)
  obtain ⟨hostedDotB, groundB⟩ :=
    hosted_applyDot gp values foB fun y inside => List.mem_append_right _ (closedB y inside)
  have groundParts : ∀ {d : Pattern}, pvars d = [] → ∀ y : String,
      ((parts d : Multiset Pattern).filter fun c => y ∈ pvars c) = 0 := by
    intro d ground y
    rw [Multiset.filter_eq_nil]
    intro c member inC
    have := pvars_of_mem_parts d c (Multiset.mem_coe.mp member) y inC
    rw [ground] at this
    exact List.not_mem_nil this
  refine ⟨fun c member => ?_, fun y => ?_⟩
  · rcases Multiset.mem_add.mp member with dotted | old
    · rcases Multiset.mem_add.mp dotted with fromA | fromB
      · exact hosted_of_mem_parts hostedDotA (Multiset.mem_coe.mp fromA)
      · exact hosted_of_mem_parts hostedDotB (Multiset.mem_coe.mp fromB)
    · exact hosted c (Multiset.mem_cons_of_mem (Multiset.mem_cons_of_mem old))
  · rw [Multiset.filter_add, Multiset.filter_add, groundParts groundA, groundParts groundB, zero_add, zero_add]
    have restLe : rest ≤ pFor t x A ::ₘ pFor u x B ::ₘ rest :=
      (Multiset.le_cons_self rest _).trans (Multiset.le_cons_self _ _)
    exact (Multiset.card_le_card (Multiset.filter_le_filter _ restLe)).trans (convention y)

/-- **The manuscript's COMM on bags up to alpha-equivalence**: a COMM step of the bag presentation from a tame
alpha-variant of the parts, to an alpha-variant of the target. -/
def CommUpToAlpha (M M' : Multiset Pattern) : Prop :=
  ∃ N N' : Multiset Pattern, (∀ c ∈ N, tame c = true) ∧ M.map close = N.map close ∧ BagComm N N' ∧
    N'.map close = M'.map close

/-- **Every run of the manuscript's COMM up to alpha is matched by a run of the bag presentation** from any
alpha-variant of its start whose parts are tame and hosted and which satisfies the convention. The bags stay
alpha-equivalent, tame, hosted and under the convention. -/
theorem runs_up_to_alpha {M₀ M M₁ : Multiset Pattern} (start : M₀.map close = M.map close)
    (tame₀ : ∀ c ∈ M₀, tame c = true) (hosted₀ : ∀ c ∈ M₀, Hosted c) (convention₀ : Convention M₀)
    (run : Relation.ReflTransGen CommUpToAlpha M M₁) :
    ∃ M₀', Relation.ReflTransGen BagComm M₀ M₀' ∧ M₀'.map close = M₁.map close ∧
      (∀ c ∈ M₀', tame c = true) ∧ (∀ c ∈ M₀', Hosted c) ∧ Convention M₀' := by
  induction run with
  | refl => exact ⟨M₀, .refl, start, tame₀, hosted₀, convention₀⟩
  | tail _ step earlier =>
      obtain ⟨K, run₀, sameK, tameK, hostedK, conventionK⟩ := earlier
      obtain ⟨N, N', tameN, sameN, comm, sameN'⟩ := step
      obtain ⟨K', commK, closeK', -⟩ :=
        bagComm_respects_alpha tameK hostedK conventionK tameN (sameK.trans sameN) comm
      obtain ⟨hostedK', conventionK'⟩ := bagComm_keeps_convention commK hostedK conventionK
      exact ⟨K', run₀.tail commK, closeK'.trans sameN', bagComm_keeps_tame commK tameK, hostedK', conventionK'⟩

/-- Runs of the bag presentation from a represented bag are runs of the single-firing step. -/
theorem runs_of_bagComm_runs {s : State Tm ℕ} {M M' : Multiset Pattern} (represented : Represents s M)
    (run : Relation.ReflTransGen BagComm M M') :
    ∃ s', Relation.ReflTransGen (Succ (RuleSyntax.step X ℕ E program).toStep) s s' ∧ Represents s' M' := by
  induction run with
  | refl => exact ⟨s, .refl, represented⟩
  | tail _ step earlier =>
      obtain ⟨s₁, run₁, comp₁, represented₁⟩ := earlier
      obtain ⟨s₂, s₃, housekeeping, fires, represented₃⟩ := communication_complete represented₁ step
      exact ⟨s₃, run₁.trans ((succ_of_administers housekeeping).tail ((succ_iff s₂ s₃).mpr (.inl fires))),
        represented₃⟩

theorem map_close_of_forall₂ {L L' : List Pattern} (each : List.Forall₂ Alpha L L') :
    L.map close = L'.map close := by
  induction each with
  | nil => rfl
  | cons head _ ih =>
      rw [List.map_cons, List.map_cons, ih]
      congr 1
      exact alpha_alphaEq head

/-- **The bag of a tame process with hosted parts, renamed apart**: tame, hosted, under the convention, and with
the closed forms of the process's parts. -/
theorem renamed_bag (P : Pattern) (tameP : tame P = true) (hostedParts : ∀ c ∈ parts P, Hosted c) :
    (parts (renameApart P) : Multiset Pattern).map close = (parts P : Multiset Pattern).map close ∧
      (∀ c ∈ (parts (renameApart P) : Multiset Pattern), tame c = true) ∧
      (∀ c ∈ (parts (renameApart P) : Multiset Pattern), Hosted c) ∧
      Convention (parts (renameApart P) : Multiset Pattern) := by
  obtain ⟨-, hostedP', parts₂⟩ := renaming_into_the_convention P tameP hostedParts
  refine ⟨?_, fun c member => tame_of_mem_parts_renameApart P tameP c (Multiset.mem_coe.mp member),
    fun c member => hostedP'.hosted c (Multiset.mem_coe.mp member), convention_of_pairwise _ hostedP'.disjoint⟩
  rw [Multiset.map_coe, Multiset.map_coe, map_close_of_forall₂ parts₂]

/-- **Every run of the manuscript's COMM up to alpha, from a tame process with hosted parts, is matched by a run of
the single-firing step** from the initial state of the process renamed apart. The run of the step ends at a state
that represents an alpha-variant of the run's end. -/
theorem hosted_runs_up_to_alpha (P : Pattern) (tameP : tame P = true) (hostedParts : ∀ c ∈ parts P, Hosted c)
    {M₁ : Multiset Pattern} (run : Relation.ReflTransGen CommUpToAlpha (parts P : Multiset Pattern) M₁) :
    ∃ (s' : State Tm ℕ) (M' : Multiset Pattern),
      Relation.ReflTransGen (Succ (RuleSyntax.step X ℕ E program).toStep) (initial (parts (renameApart P))) s' ∧
        Represents s' M' ∧ M'.map close = M₁.map close := by
  obtain ⟨start, tame₀, hosted₀, convention₀⟩ := renamed_bag P tameP hostedParts
  obtain ⟨M', bagRun, closeSame, -, -, -⟩ := runs_up_to_alpha start tame₀ hosted₀ convention₀ run
  have hostedP' := (renaming_into_the_convention P tameP hostedParts).2.1
  obtain ⟨s', stepRun, represented⟩ := runs_of_bagComm_runs ⟨_, initial_represents (renameApart P) hostedP'⟩ bagRun
  exact ⟨s', M', stepRun, represented, closeSame⟩

#print axioms step_respects_alpha
#print axioms step_respects_renaming
#print axioms invOn_apply
#print axioms rename_cancel
#print axioms groundPrincipal_of_rename
#print axioms applyDot_rename
#print axioms input_of_alphaEq
#print axioms hosted_alpha_renaming
#print axioms convention_of_pairwise
#print axioms hosted_of_mem_parts
#print axioms representsBy_hosted
#print axioms representsBy_convention
#print axioms bagComm_respects_alpha
#print axioms bagComm_keeps_convention
#print axioms runs_up_to_alpha
#print axioms runs_of_bagComm_runs
#print axioms renamed_bag
#print axioms hosted_runs_up_to_alpha

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.FiniteConvention
