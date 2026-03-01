import Mettapedia.Logic.LP.Semantics

/-!
# Logic Programming Kernel: SLD Resolution

SLD (Selective Linear Definite clause) resolution for logic programs.

## Design

- `Grounding.compSubst` — composition of a grounding with a substitution,
  yielding a new grounding. Key bridge between SLD steps and model theory.
- `SLDTree prog goals θ` — big-step SLD refutation tree (leftmost selection).
  An SLD refutation reduces goals to empty via clause resolution steps.
- `SLDTree_sound` — soundness: if there is a refutation with computed answer θ,
  then every goal atom, grounded via θ and any further grounding, is in the
  least Herbrand model (Lloyd's Soundness Theorem, FLP Theorem 3.1).
- Variable freshening is not formalized; the standard "standardized apart"
  convention is assumed at each resolution step.

## References

- Lloyd, *Foundations of Logic Programming*, 2nd ed., Ch. 3
- Apt, "Logic Programming", Ch. 4 (SLD Trees)
- van Emden & Kowalski, "Semantics of predicate logic as a programming language", 1976
-/

namespace Mettapedia.Logic.LP

/-! ## Section 1: Grounding-substitution composition -/

/-- Compose a grounding with a substitution: first apply θ to get terms,
    then ground the resulting terms. -/
def Grounding.compSubst {σ : LPSignature} (g : Grounding σ) (θ : Subst σ) : Grounding σ :=
  fun v => g.groundTerm (θ v)

/-- Grounding a substituted term equals applying the composed grounding. -/
theorem Grounding.groundTerm_applyTerm {σ : LPSignature}
    (g : Grounding σ) (θ : Subst σ) (t : Term σ) :
    g.groundTerm (θ.applyTerm t) = (g.compSubst θ).groundTerm t := by
  induction t with
  | var v => rfl
  | const _ => rfl
  | app f ts ih =>
    simp only [Subst.applyTerm, Grounding.groundTerm]
    congr 1; funext i; exact ih i

/-- Grounding a substituted atom equals applying the composed grounding. -/
theorem Grounding.groundAtom_applyAtom {σ : LPSignature}
    (g : Grounding σ) (θ : Subst σ) (a : Atom σ) :
    g.groundAtom (θ.applyAtom a) = (g.compSubst θ).groundAtom a := by
  unfold Grounding.groundAtom Subst.applyAtom
  congr 1; funext i; exact g.groundTerm_applyTerm θ (a.args i)

/-- Composing with a composition of substitutions equals composing stepwise. -/
theorem Grounding.compSubst_comp {σ : LPSignature}
    (g : Grounding σ) (θ₁ θ₂ : Subst σ) :
    g.compSubst (θ₁ ∘ₛ θ₂) = (g.compSubst θ₁).compSubst θ₂ := by
  funext v
  exact g.groundTerm_applyTerm θ₁ (θ₂ v)

/-- Key equation: grounding via a composed substitution equals grounding the
    substituted atom. Combines `compSubst_comp` and `groundAtom_applyAtom`. -/
private theorem ground_comp_eq {σ : LPSignature}
    (g : Grounding σ) (θ₁ θ₂ : Subst σ) (a : Atom σ) :
    (g.compSubst (θ₁ ∘ₛ θ₂)).groundAtom a = (g.compSubst θ₁).groundAtom (θ₂.applyAtom a) := by
  rw [Grounding.compSubst_comp, ← Grounding.groundAtom_applyAtom]

/-! ## Section 2: SLD derivation trees -/

/-- SLD refutation tree (big-step, leftmost selection rule).

    `SLDTree prog goals θ` means there is an SLD refutation of `← goals`
    using clauses from `prog`, with computed answer substitution `θ`.

    At each step, the leftmost goal atom is selected, unified with a clause
    head, and replaced by the (substituted) clause body. The computed answer
    is the composition of all unifiers.

    **Variable freshening**: This definition assumes clauses are appropriately
    renamed at each step (standard "standardized apart" convention from Lloyd).
    Soundness holds regardless of freshening. -/
inductive SLDTree {σ : LPSignature} (prog : Program σ) :
    List (Atom σ) → Subst σ → Prop where
  /-- Empty goal list: refutation found with identity substitution. -/
  | nil : SLDTree prog [] (Subst.id σ)
  /-- Resolution step: unify leftmost goal with clause head, continue with
      the substituted clause body prepended to the remaining goals. -/
  | cons (a : Atom σ) (goals : List (Atom σ)) (c : Clause σ) (θ θ' : Subst σ) :
      c ∈ prog →
      θ.applyAtom a = θ.applyAtom c.head →
      SLDTree prog (θ.applyAtoms (c.body ++ goals)) θ' →
      SLDTree prog (a :: goals) (θ' ∘ₛ θ)

/-! ## Section 3: Soundness -/

/-- **Soundness of SLD resolution** (Lloyd, FLP Theorem 3.1):
    if there is an SLD refutation of `← goals` with computed answer `θ`,
    then for any grounding `g`, every goal atom grounded via `g ∘ θ`
    is in the least Herbrand model.

    Formally: `(g.compSubst θ).groundAtom a ∈ leastHerbrandModel kb`
    for every `a ∈ goals`. -/
theorem SLDTree_sound {σ : LPSignature} (kb : KnowledgeBase σ)
    (goals : List (Atom σ)) (θ : Subst σ) (h : SLDTree kb.prog goals θ) :
    ∀ g : Grounding σ, ∀ a ∈ goals,
      (g.compSubst θ).groundAtom a ∈ leastHerbrandModel kb := by
  induction h with
  | nil => intro _ _ ha; simp at ha
  | cons a goals c θ θ' hc hunif _ ih =>
    intro g a' ha'
    simp only [List.mem_cons] at ha'
    -- Rewrite: (g.compSubst (θ' ∘ₛ θ)).groundAtom a'
    --        = (g.compSubst θ').groundAtom (θ.applyAtom a')
    rw [ground_comp_eq]
    rcases ha' with rfl | ha'
    · -- Selected atom: use clause soundness
      -- (g.compSubst θ').groundAtom (θ.applyAtom a)
      -- = (g.compSubst θ').groundAtom (θ.applyAtom c.head)  [by hunif]
      rw [hunif]
      -- = (g.compSubst (θ' ∘ₛ θ)).groundAtom c.head        [by ground_comp_eq⁻¹]
      rw [← ground_comp_eq]
      -- Apply leastHerbrandModel_clause
      apply leastHerbrandModel_clause kb c hc (g.compSubst (θ' ∘ₛ θ))
      -- Need: ∀ b ∈ c.body, (g.compSubst (θ' ∘ₛ θ)).groundAtom b ∈ model
      intro b hb
      rw [ground_comp_eq]
      -- (g.compSubst θ').groundAtom (θ.applyAtom b) ∈ model
      -- θ.applyAtom b ∈ θ.applyAtoms (c.body ++ goals)
      exact ih g (θ.applyAtom b)
        (List.mem_map.mpr ⟨b, List.mem_append_left goals hb, rfl⟩)
    · -- Remaining goals: directly from IH
      exact ih g (θ.applyAtom a')
        (List.mem_map.mpr ⟨a', List.mem_append_right c.body ha', rfl⟩)

/-- Soundness for single-atom queries: if we can refute `← a`, then
    any grounding of the computed answer produces a model element. -/
theorem SLDTree_sound_single {σ : LPSignature} (kb : KnowledgeBase σ)
    (a : Atom σ) (θ : Subst σ) (h : SLDTree kb.prog [a] θ) (g : Grounding σ) :
    (g.compSubst θ).groundAtom a ∈ leastHerbrandModel kb :=
  SLDTree_sound kb [a] θ h g a (List.mem_cons_self ..)

/-! ## Section 4: Derived properties -/

/-- An SLD refutation with identity substitution means the goals were
    already ground consequences. -/
theorem SLDTree_id_ground {σ : LPSignature} (kb : KnowledgeBase σ)
    (goals : List (Atom σ)) (h : SLDTree kb.prog goals (Subst.id σ)) :
    ∀ g : Grounding σ, ∀ a ∈ goals,
      g.groundAtom a ∈ leastHerbrandModel kb := by
  intro g a ha
  have := SLDTree_sound kb goals (Subst.id σ) h g a ha
  simp only [Subst.id] at this
  convert this using 1

/-- SLD refutation of empty goals is trivially constructible. -/
theorem SLDTree_nil {σ : LPSignature} (prog : Program σ) :
    SLDTree prog [] (Subst.id σ) :=
  SLDTree.nil

/-- If we can refute `← body` and the clause `head :- body` is in the program,
    then we can construct a refutation involving the head. -/
theorem SLDTree_clause {σ : LPSignature} (prog : Program σ)
    (c : Clause σ) (hc : c ∈ prog) (θ θ' : Subst σ)
    (_hunif : θ.applyAtom c.head = θ.applyAtom c.head)
    (hbody : SLDTree prog (θ.applyAtoms (c.body ++ [])) θ') :
    SLDTree prog [c.head] (θ' ∘ₛ θ) := by
  exact SLDTree.cons c.head [] c θ θ' hc (by rfl) (by simpa using hbody)

end Mettapedia.Logic.LP
