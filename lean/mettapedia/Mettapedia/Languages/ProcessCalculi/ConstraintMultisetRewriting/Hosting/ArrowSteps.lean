import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting.Arrows

/-!
# The two `let` moves, one firing each, both ways; and the control for hygiene

* `simulation_letStart`, `reflection_bindStart`: the source's `letStart` and the rule
  `bindStartRule` match one to one, for every represented alternative.
* `simulation_letBind`, `reflection_bindValue`: the source's `letBind` at a fresh scope and the rule
  `bindValueRule` match one to one, for every represented alternative whose pending frame is
  hygienic (`FramePrivate`).
* `hygiene_needed`: an alternative that is not hygienic, on which the rule's readings are empty and
  the source's bind has a reading: without hygiene the bind's correspondence can fail.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open SourceLanguage

variable {S : Signature} {Γ : Ctx S} {star : S.Srt} (N : Nodes S Γ star)
variable {κ : Keys S}

section Members

variable {Ty : Type} (P : SourceLanguage.Program κ Γ star Ty)

theorem bindStartRule_mem : bindStartRule N ∈ translate N P :=
  (mem_translate N).mpr (.inl ((mem_controlRules N).mpr (.inr (.inr (.inr (.inr (.inl rfl)))))))
theorem bindValueRule_mem : bindValueRule N ∈ translate N P :=
  (mem_translate N).mpr (.inl ((mem_controlRules N).mpr (.inr (.inr (.inr (.inr (.inr rfl)))))))

end Members

section Fresh

variable {Ty : Type}

theorem branchBelow_letStart {n : ℕ} {K : List (Constraint κ Γ star)} {s : κ.Site} {p : Data κ Γ star}
    {c k : Comp κ Γ star Ty} {fs : List (SourceLanguage.Frame κ Γ star Ty)}
    {ps : List (Data κ Γ star × Comp κ Γ star Ty)} (below : BranchBelow n ⟨K, .eval (.let_ s p c k), fs, ps⟩) :
    BranchBelow n ⟨K, .eval c, .bindTo s p k :: fs, ps⟩ := by
  refine ⟨below.1, fun t member => below.2.1 t ?_, ?_⟩
  · simp only [focusData, Comp.data, List.mem_cons, List.mem_append] at member ⊢
    exact .inr (.inl member)
  · intro fr member t inside
    rcases List.mem_cons.mp member with rfl | old
    · apply below.2.1 t
      simp only [frameData, List.mem_cons] at inside
      simp only [focusData, Comp.data, List.mem_cons, List.mem_append]
      rcases inside with rfl | inK
      · exact .inl rfl
      · exact .inr (.inr inK)
    · exact below.2.2 fr old t inside

theorem branchBelow_letBind {n : ℕ} {K : List (Constraint κ Γ star)} {v : Data κ Γ star} {s : κ.Site}
    {p : Data κ Γ star} {k : Comp κ Γ star Ty} {fs : List (SourceLanguage.Frame κ Γ star Ty)}
    {ps : List (Data κ Γ star × Comp κ Γ star Ty)} (below : BranchBelow n ⟨K, .value v, .bindTo s p k :: fs, ps⟩) :
    BranchBelow (n + 1) ⟨K ++ [(instantiate (openAt κ s n) p, v)], .eval (k.inst (openAt κ s n)), fs, ps⟩ := by
  have vBelow : DependsBelow n v := below.2.1 v (by simp [focusData])
  have pBelow : DependsBelow n p := below.2.2 _ List.mem_cons_self p (by simp [frameData])
  refine ⟨?_, ?_, ?_⟩
  · intro e member
    rcases List.mem_append.mp member with old | new
    · exact ⟨DependsBelow.mono (below.1 e old).1 (Nat.le_succ n),
        DependsBelow.mono (below.1 e old).2 (Nat.le_succ n)⟩
    · rw [List.mem_singleton.mp new]
      exact ⟨dependsBelow_open s pBelow, DependsBelow.mono vBelow (Nat.le_succ n)⟩
  · intro t member
    change t ∈ (k.mapData (instantiate (openAt κ s n))).data at member
    rw [comp_data_mapData] at member
    obtain ⟨original, inside, rfl⟩ := List.mem_map.mp member
    exact dependsBelow_open s (below.2.2 _ List.mem_cons_self original (by simp [frameData, inside]))
  · intro fr member t inside
    exact DependsBelow.mono (below.2.2 fr (List.mem_cons_of_mem _ member) t inside) (Nat.le_succ n)

end Fresh

/-! ## Simulation of the `let` moves -/

section Simulation

variable {Ty : Type} {P : SourceLanguage.Program κ Γ star Ty}

/-- **`letStart` is one firing of `bindStartRule`.** -/
theorem simulation_letStart {n : ℕ} {K : List (Constraint κ Γ star)} {s : κ.Site} {p : Data κ Γ star}
    {c k : Comp κ Γ star Ty} {fs : List (SourceLanguage.Frame κ Γ star Ty)}
    {ps : List (Data κ Γ star × Comp κ Γ star Ty)} {st : HostState S} {a : ℕ}
    (rep : Represents N P n ⟨K, .eval (.let_ s p c k), fs, ps⟩ st a) (live : Solvable K) :
    ∃ st' a', Fires N P st st' ∧ Represents N P n ⟨K, .eval c, .bindTo s p k :: fs, ps⟩ st' a' :=
  fire_simple N (bindStartRule_mem N P) rfl rfl rfl rfl rep (fun _ q => transfer_bindStart N rfl q) live
    (entails_of_no_checks rfl rfl) (branchBelow_letStart rep.fresh) rep.noPending

/-- **`letBind` at a fresh scope is one firing of `bindValueRule`**, for a hygienic frame. -/
theorem simulation_letBind {n : ℕ} {K : List (Constraint κ Γ star)} {v : Data κ Γ star} {s : κ.Site}
    {p : Data κ Γ star} {k : Comp κ Γ star Ty} {fs : List (SourceLanguage.Frame κ Γ star Ty)}
    {ps : List (Data κ Γ star × Comp κ Γ star Ty)} {st : HostState S} {a : ℕ}
    (rep : Represents N P n ⟨K, .value v, .bindTo s p k :: fs, ps⟩ st a)
    (hygienic : FramePrivate s p k K v fs) (live : Solvable (K ++ [(instantiate (openAt κ s n) p, v)])) :
    ∃ st' a', Fires N P st st' ∧
      Represents N P (n + 1) ⟨K ++ [(instantiate (openAt κ s n) p, v)], .eval (k.inst (openAt κ s n)), fs, ps⟩ st' a' :=
  fire_simple N (bindValueRule_mem N P) rfl rfl rfl rfl rep (fun _ q => transfer_bindValue N rep.fresh hygienic q)
    live (entails_of_no_checks rfl rfl) (branchBelow_letBind rep.fresh) rep.noPending

end Simulation

/-! ## Reflection of the `let` rules -/

section Reflection

variable {D : Discipline S Γ star} {P : SourceLanguage.Program κ Γ star D.Ty} {supply : ℕ → Term S Γ star}

/-- **Every firing of `bindStartRule` is a source `letStart`.** -/
theorem reflection_bindStart {w : World κ Γ star} {b : Branch κ Γ star D.Ty} {st : HostState S} {a : ℕ}
    (rep : Represents N P w.scope b st a) {member : bindStartRule N ∈ translate N P}
    {ext : (RuleSyntax.Contextual.declarations S).Ext st.frame}
    {opening : Assignment (bindStartRule N).locals.arity ((RuleSyntax.Contextual.declarations S).target ext).arity}
    {selection : Selection ℕ} {seen : List (Finset ℕ)}
    (admitted : RuleSyntax.Firing.Admits (Interface.Frames.contextual S) st
      (⟨bindStartRule N, member, ext, opening, selection, seen⟩ :
        RuleSyntax.Firing ℕ (RuleSyntax.Contextual.declarations S) (translate N P) st.frame)) :
    ∃ w' bs b' a', Move D P supply w b w' bs ∧ b' ∈ bs ∧
      Represents N P w'.scope b' (RuleSyntax.Firing.result (Interface.Frames.contextual S) st
        (⟨bindStartRule N, member, ext, opening, selection, seen⟩ :
          RuleSyntax.Firing ℕ (RuleSyntax.Contextual.declarations S) (translate N P) st.frame)) a' := by
  obtain ⟨K, focus, fs, ps⟩ := b
  obtain ⟨a', simple, fresh, B, h, reads, _⟩ := admitted_takes_alternative N rep admitted rfl rfl rfl
    (fun h => ⟨_, _, congrArg observe (instantiate_altN N h _ _)⟩)
  obtain ⟨s, p, c, k, rfl⟩ := shape_bindStart N reads
  exact ⟨w, _, _, a', .letStart w K s p c k fs ps, Multiset.mem_singleton_self _,
    represents_after N rep simple admitted.1 fresh (fun B q => transfer_bindStart N rfl q)
      (branchBelow_letStart rep.fresh) rep.noPending⟩

/-- **Every firing of `bindValueRule` is a source `letBind`**, at a hygienic frame. -/
theorem reflection_bindValue {w : World κ Γ star} {b : Branch κ Γ star D.Ty} {st : HostState S} {a : ℕ}
    (rep : Represents N P w.scope b st a)
    (hygienic : ∀ K v s p k fs ps, b = ⟨K, .value v, .bindTo s p k :: fs, ps⟩ → FramePrivate s p k K v fs)
    {member : bindValueRule N ∈ translate N P}
    {ext : (RuleSyntax.Contextual.declarations S).Ext st.frame}
    {opening : Assignment (bindValueRule N).locals.arity ((RuleSyntax.Contextual.declarations S).target ext).arity}
    {selection : Selection ℕ} {seen : List (Finset ℕ)}
    (admitted : RuleSyntax.Firing.Admits (Interface.Frames.contextual S) st
      (⟨bindValueRule N, member, ext, opening, selection, seen⟩ :
        RuleSyntax.Firing ℕ (RuleSyntax.Contextual.declarations S) (translate N P) st.frame)) :
    ∃ w' bs b' a', Move D P supply w b w' bs ∧ b' ∈ bs ∧
      Represents N P w'.scope b' (RuleSyntax.Firing.result (Interface.Frames.contextual S) st
        (⟨bindValueRule N, member, ext, opening, selection, seen⟩ :
          RuleSyntax.Firing ℕ (RuleSyntax.Contextual.declarations S) (translate N P) st.frame)) a' := by
  obtain ⟨K, focus, frames, ps⟩ := b
  obtain ⟨a', simple, fresh, B, h, reads, _⟩ := admitted_takes_alternative N rep admitted rfl rfl rfl
    (fun h => ⟨_, _, congrArg observe (instantiate_altN N h _ _)⟩)
  obtain ⟨s, p, k, fs, rfl⟩ := shape_bindValue N reads
  have readsV := reads
  change branchReads N _ B (observe (instantiate h _)) at readsV
  rw [instantiate_altN, instantiate_valueN] at readsV
  obtain ⟨σ, _, same⟩ := (branchReads_observe N).mp readsV
  obtain ⟨onFocus, _⟩ := alt_eq_encAlt N (instantiate σ) same.symm
  obtain ⟨v, rfl, _⟩ := value_eq_encFocus N (instantiate σ) onFocus
  exact ⟨w.fresh, _, _, a', .letBind w K v s p k fs ps, Multiset.mem_singleton_self _,
    represents_after N rep simple admitted.1 fresh
      (fun B q => transfer_bindValue N rep.fresh (hygienic K v s p k fs ps rfl) q)
      (branchBelow_letBind rep.fresh) rep.noPending⟩

end Reflection

/-! ## Hygiene is needed -/

section Control

open SourceLanguage.Elaboration SourceLanguage.Toolkit

/-- The name `x` of the site `[7]`, unopened. -/
abbrev xName : MData := foD [] [7] 0

/-- An alternative whose store already binds the frame's own name `x` to `two`, receiving `one` for
the frame `let x = □ in (ret x)`. -/
def unhygienic : Branch mkeys [] () MTy :=
  ⟨[(xName, sym "two")], .value (sym "one"), [.bindTo [7] xName (.ret xName)], []⟩

/-- The alternative the source's bind at scope `0` makes: a fresh copy of `x` is bound to `one`. -/
def unhygienicChild : Branch mkeys [] () MTy :=
  ⟨[(xName, sym "two"), (instantiate (openAt mkeys [7] 0) xName, sym "one")],
    .eval ((Comp.ret xName).inst (openAt mkeys [7] 0)), [], []⟩

/-- **Hygiene cannot be dropped**: on this alternative the frame's own name occurs in the store, the
source's bind has a reading, and the rule's made row has none. -/
theorem hygiene_needed :
    ¬ FramePrivate [7] xName (.ret xName) [(xName, sym "two")] (sym "one") ([] : List (SourceLanguage.Frame mkeys [] () MTy)) ∧
    (∃ (B : Interface.Frames.Frame MSig) (q : Observation MSig B.arity), branchReads mettaNodes unhygienicChild B q) ∧
    ∀ (B : Interface.Frames.Frame MSig) (q : Observation MSig B.arity),
      ¬ ∃ h : Assignment (unknownArity [] ()) B.arity,
        branchReads mettaNodes unhygienic B (instantiateObservation h (bindValuePattern mettaNodes)) ∧
        (Interface.Frames.contextual MSig).Models (a := controlFrame [] ()) (b := B) h
          (bindValueTell (S := MSig) (Γ := []) (star := ())) ∧
        instantiateObservation h (bindValueMade mettaNodes) = q := by
  refine ⟨?_, ?_, ?_⟩
  · intro private'
    -- two assignments that differ only on `x`
    let one : Assignment (fam mkeys) noNames := closeNames [] (csym "two")
    let two : Assignment (fam mkeys) noNames := closeNames [(([], [7], 0), csym "one")] (csym "two")
    obtain ⟨onStore, _, _⟩ := private' one two (by
      intro y notOwn
      rcases y with ⟨scopes, ⟨site, index, ⟨Δ, u⟩⟩⟩
      cases u
      cases Δ with
      | cons _ _ => rfl
      | nil =>
          by_cases hit : scopes = [] ∧ site = [7] ∧ index = 0
          · obtain ⟨rfl, rfl, rfl⟩ := hit
            exact absurd ⟨rfl, .inl (by decide)⟩ notOwn
          · simp only [one, two, closeNames, List.lookup]
            split
            · rename_i heq
              simp only [beq_iff_eq, Prod.mk.injEq] at heq
              exact absurd heq hit
            · rfl)
    have := (onStore _ (List.mem_singleton_self _)).1
    change Rigid.includeTerm noNames (csym "two") = Rigid.includeTerm noNames (csym "one") at this
    have := Rigid.include_injective _ _ _ this
    simp [csym] at this
  · refine ⟨⟨Empty, noNames⟩, _, closeNames [(([], [7], 0), csym "two"), (([0], [7], 0), csym "one")] (csym "a"),
      ?_, rfl⟩
    intro e member
    simp only [unhygienicChild, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> rfl
  · intro B q exists'
    obtain ⟨σ, solved, matched, _⟩ := (bindValue_rule_side mettaNodes (K := [(xName, sym "two")])
      (v := sym "one") (s := [7]) (p := xName) (k := .ret xName) (fs := []) (ps := []) q).mp exists'
    have two := solved _ (List.mem_singleton_self _)
    change instantiate σ xName = instantiate σ (sym "two") at two
    change instantiate σ xName = instantiate σ (sym "one") at matched
    have := two.symm.trans matched
    change (Term.op (Sum.inl (MOp.sym "two")) .nil : Term (signature MSig B.arity) [] ()) =
      Term.op (Sum.inl (MOp.sym "one")) .nil at this
    simp at this

end Control

#print axioms simulation_letStart
#print axioms simulation_letBind
#print axioms reflection_bindStart
#print axioms reflection_bindValue
#print axioms hygiene_needed

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting
