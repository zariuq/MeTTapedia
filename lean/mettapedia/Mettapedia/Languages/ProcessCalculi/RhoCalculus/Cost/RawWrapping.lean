import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.RuntimeProperties

/-!
# Raw wrapping preservation

The independent executable syntax accepts exactly the wrapped pure cost-rho
grammar.  Lifting, COMM substitution, structural normalization, and component
reassembly preserve that grammar.  In particular, substitution opens only a
matched bound `drop`; quoted and free drops remain wrapped syntax.
-/

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost

/-! ## Lifting and substitution -/

mutual
  theorem RawCostName.wellFormed_lift (amount cutoff : Nat) :
      ∀ name : RawCostName, name.wellFormed = true →
        (name.lift amount cutoff).wellFormed = true
    | .bvar index, _ => by
        simp only [RawCostName.lift]
        split <;> rfl
    | .quote term, supported => by
        simpa [RawCostName.lift, RawCostName.wellFormed] using supported
    | .signature sig, supported => by
        simpa [RawCostName.lift, RawCostName.wellFormed] using supported

  theorem RawCostProc.wellFormed_lift (amount cutoff : Nat) :
      ∀ proc : RawCostProc, proc.wellFormed = true →
        (proc.lift amount cutoff).wellFormed = true
    | .nil, _ => rfl
    | .par left right, supported => by
        simp only [RawCostProc.wellFormed, Bool.and_eq_true] at supported ⊢
        exact ⟨
          RawCostProc.wellFormed_lift amount cutoff left supported.1,
          RawCostProc.wellFormed_lift amount cutoff right supported.2⟩
    | .send channel payload, supported => by
        simp only [RawCostProc.wellFormed, Bool.and_eq_true] at supported ⊢
        exact ⟨
          RawCostName.wellFormed_lift amount cutoff channel supported.1,
          RawCostTerm.wellFormed_lift amount cutoff payload supported.2⟩
    | .recv channel body, supported => by
        simp only [RawCostProc.wellFormed, Bool.and_eq_true] at supported ⊢
        exact ⟨
          RawCostName.wellFormed_lift amount cutoff channel supported.1,
          RawCostTerm.wellFormed_lift amount (cutoff + 1) body supported.2⟩

  theorem RawCostTerm.wellFormed_lift (amount cutoff : Nat) :
      ∀ term : RawCostTerm, term.wellFormed = true →
        (term.lift amount cutoff).wellFormed = true
    | .nil, _ => rfl
    | .signed proc sig, supported => by
        simp only [RawCostTerm.wellFormed, Bool.and_eq_true] at supported ⊢
        exact ⟨RawCostProc.wellFormed_lift amount cutoff proc supported.1,
          supported.2⟩
    | .par left right, supported => by
        simp only [RawCostTerm.wellFormed, Bool.and_eq_true] at supported ⊢
        exact ⟨RawCostTerm.wellFormed_lift amount cutoff left supported.1,
          RawCostTerm.wellFormed_lift amount cutoff right supported.2⟩
    | .drop name, supported =>
        RawCostName.wellFormed_lift amount cutoff name supported
    | .purse location stack, supported => by
        simp only [RawCostTerm.wellFormed, Bool.and_eq_true] at supported ⊢
        exact ⟨RawCostName.wellFormed_lift amount cutoff location supported.1,
          supported.2⟩
end

mutual
  theorem RawCostName.wellFormed_substitute
      (replacement : RawCostTerm) (replacement_supported : replacement.wellFormed = true)
      (depth : Nat) : ∀ name : RawCostName, name.wellFormed = true →
        (name.substitute replacement depth).wellFormed = true
    | .bvar index, _ => by
        simp only [RawCostName.substitute]
        split
        · exact RawCostTerm.wellFormed_lift depth 0 replacement replacement_supported
        · split <;> rfl
    | .quote term, supported => by
        simpa [RawCostName.substitute, RawCostName.wellFormed] using supported
    | .signature sig, supported => by
        simpa [RawCostName.substitute, RawCostName.wellFormed] using supported

  theorem RawCostProc.wellFormed_substitute
      (replacement : RawCostTerm) (replacement_supported : replacement.wellFormed = true)
      (depth : Nat) : ∀ proc : RawCostProc, proc.wellFormed = true →
        (proc.substitute replacement depth).wellFormed = true
    | .nil, _ => rfl
    | .par left right, supported => by
        simp only [RawCostProc.wellFormed, Bool.and_eq_true] at supported ⊢
        exact ⟨
          RawCostProc.wellFormed_substitute replacement replacement_supported depth
            left supported.1,
          RawCostProc.wellFormed_substitute replacement replacement_supported depth
            right supported.2⟩
    | .send channel payload, supported => by
        simp only [RawCostProc.wellFormed, Bool.and_eq_true] at supported ⊢
        exact ⟨
          RawCostName.wellFormed_substitute replacement replacement_supported depth
            channel supported.1,
          RawCostTerm.wellFormed_substitute replacement replacement_supported depth
            payload supported.2⟩
    | .recv channel body, supported => by
        simp only [RawCostProc.wellFormed, Bool.and_eq_true] at supported ⊢
        exact ⟨
          RawCostName.wellFormed_substitute replacement replacement_supported depth
            channel supported.1,
          RawCostTerm.wellFormed_substitute replacement replacement_supported (depth + 1)
            body supported.2⟩

  theorem RawCostTerm.wellFormed_substitute
      (replacement : RawCostTerm) (replacement_supported : replacement.wellFormed = true)
      (depth : Nat) : ∀ term : RawCostTerm, term.wellFormed = true →
        (RawCostTerm.substitute replacement depth term).wellFormed = true
    | .nil, _ => rfl
    | .signed proc sig, supported => by
        simp only [RawCostTerm.wellFormed, Bool.and_eq_true] at supported ⊢
        exact ⟨
          RawCostProc.wellFormed_substitute replacement replacement_supported depth
            proc supported.1,
          supported.2⟩
    | .par left right, supported => by
        simp only [RawCostTerm.wellFormed, Bool.and_eq_true] at supported ⊢
        exact ⟨
          RawCostTerm.wellFormed_substitute replacement replacement_supported depth
            left supported.1,
          RawCostTerm.wellFormed_substitute replacement replacement_supported depth
            right supported.2⟩
    | .drop (.bvar index), _ => by
        simp only [RawCostTerm.substitute]
        split
        · exact RawCostTerm.wellFormed_lift depth 0 replacement replacement_supported
        · split <;> rfl
    | .drop (.quote term), supported => by
        simpa [RawCostTerm.substitute, RawCostTerm.wellFormed] using supported
    | .drop (.signature sig), supported => by
        simpa [RawCostTerm.substitute, RawCostTerm.wellFormed] using supported
    | .purse location stack, supported => by
        simp only [RawCostTerm.wellFormed, Bool.and_eq_true] at supported ⊢
        exact ⟨
          RawCostName.wellFormed_substitute replacement replacement_supported depth
            location supported.1,
          supported.2⟩
end

/-- Raw COMM substitution preserves the accepted wrapped grammar. -/
theorem RawCostTerm.wellFormed_commSubst {body payload : RawCostTerm}
    (body_supported : body.wellFormed = true)
    (payload_supported : payload.wellFormed = true) :
    (body.commSubst payload).wellFormed = true :=
  RawCostTerm.wellFormed_substitute payload payload_supported 0 body body_supported

/-! ## Transparent stable sorting preserves grammar predicates -/

theorem stableInsertBy_forall {Alpha : Type} (before : Alpha → Alpha → Bool)
    {predicate : Alpha → Prop} {item : Alpha} {items : List Alpha}
    (item_ok : predicate item) (items_ok : items.Forall predicate) :
    (stableInsertBy before item items).Forall predicate := by
  induction items with
  | nil =>
      change predicate item
      exact item_ok
  | cons head tail ih =>
      obtain ⟨head_ok, tail_ok⟩ :=
        (List.forall_cons predicate head tail).mp items_ok
      simp only [stableInsertBy]
      split
      · exact (List.forall_cons predicate item (head :: tail)).mpr
          ⟨item_ok, (List.forall_cons predicate head tail).mpr
            ⟨head_ok, tail_ok⟩⟩
      · exact (List.forall_cons predicate head
          (stableInsertBy before item tail)).mpr ⟨head_ok, ih tail_ok⟩

theorem foldl_stableInsertBy_forall {Alpha : Type}
    (before : Alpha → Alpha → Bool) {predicate : Alpha → Prop} :
    ∀ (source accumulator : List Alpha),
      source.Forall predicate → accumulator.Forall predicate →
      (List.foldl (fun sorted item => stableInsertBy before item sorted)
        accumulator source).Forall predicate
  | [], accumulator, _, accumulator_ok => accumulator_ok
  | head :: tail, accumulator, source_ok, accumulator_ok => by
      obtain ⟨head_ok, tail_ok⟩ :=
        (List.forall_cons predicate head tail).mp source_ok
      exact foldl_stableInsertBy_forall before tail
        (stableInsertBy before head accumulator) tail_ok
        (stableInsertBy_forall before head_ok accumulator_ok)

theorem stableSortBy_forall {Alpha : Type} (before : Alpha → Alpha → Bool)
    {predicate : Alpha → Prop} {items : List Alpha}
    (items_ok : items.Forall predicate) :
    (stableSortBy before items).Forall predicate := by
  exact foldl_stableInsertBy_forall before items [] items_ok trivial

/-! ## Structural normalization -/

@[simp]
theorem stableInsertBy_length {Alpha : Type} (before : Alpha → Alpha → Bool)
    (item : Alpha) : ∀ items : List Alpha,
    (stableInsertBy before item items).length = items.length + 1
  | [] => rfl
  | head :: tail => by
      simp only [stableInsertBy]
      split
      · simp
      · simp [stableInsertBy_length before item tail,
          Nat.add_comm, Nat.add_left_comm]

theorem foldl_stableInsertBy_length {Alpha : Type}
    (before : Alpha → Alpha → Bool) : ∀ source accumulator : List Alpha,
    (List.foldl (fun sorted item => stableInsertBy before item sorted)
      accumulator source).length = accumulator.length + source.length
  | [], accumulator => by simp
  | head :: tail, accumulator => by
      rw [List.foldl_cons, foldl_stableInsertBy_length before tail]
      rw [stableInsertBy_length]
      simp only [List.length_cons]
      omega

@[simp]
theorem stableSortBy_length {Alpha : Type} (before : Alpha → Alpha → Bool)
    (items : List Alpha) :
    (stableSortBy before items).length = items.length := by
  simpa [stableSortBy] using foldl_stableInsertBy_length before items []

theorem RawCostSig.normalize_valid {sig : RawCostSig}
    (valid : sig.valid = true) : sig.normalize.valid = true := by
  have source_nonempty : sig ≠ [] := by
    simpa [RawCostSig.valid] using valid
  have normalized_nonempty : sig.normalize ≠ [] := by
    intro normalized_empty
    have lengths := stableSortBy_length
      (fun left right : String => decide (left < right)) sig
    unfold RawCostSig.normalize at normalized_empty
    rw [normalized_empty] at lengths
    exact source_nonempty (List.eq_nil_of_length_eq_zero lengths.symm)
  simpa [RawCostSig.valid] using normalized_nonempty

theorem RawCostStack.normalize_all_valid : ∀ stack : RawCostStack,
    stack.all RawCostSig.valid = true →
      (stack.map RawCostSig.normalize).all RawCostSig.valid = true
  | [], _ => rfl
  | sig :: rest, valid => by
      simp only [List.map_cons, List.all_cons, Bool.and_eq_true] at valid ⊢
      exact ⟨RawCostSig.normalize_valid valid.1,
        RawCostStack.normalize_all_valid rest valid.2⟩

theorem RawCostProc.components_forall_wellFormed : ∀ proc : RawCostProc,
    proc.wellFormed = true →
      proc.components.Forall (fun component => component.wellFormed = true)
  | .nil, _ => trivial
  | .par left right, supported => by
      simp only [RawCostProc.wellFormed, Bool.and_eq_true] at supported
      simp only [RawCostProc.components, List.forall_append]
      exact ⟨RawCostProc.components_forall_wellFormed left supported.1,
        RawCostProc.components_forall_wellFormed right supported.2⟩
  | .send channel payload, supported => by
      simpa [RawCostProc.components] using supported
  | .recv channel body, supported => by
      simpa [RawCostProc.components] using supported

theorem RawCostTerm.components_forall_wellFormed : ∀ term : RawCostTerm,
    term.wellFormed = true →
      term.components.Forall (fun component => component.wellFormed = true)
  | .nil, _ => trivial
  | .par left right, supported => by
      simp only [RawCostTerm.wellFormed, Bool.and_eq_true] at supported
      simp only [RawCostTerm.components, List.forall_append]
      exact ⟨RawCostTerm.components_forall_wellFormed left supported.1,
        RawCostTerm.components_forall_wellFormed right supported.2⟩
  | .signed proc sig, supported => by
      simpa [RawCostTerm.components] using supported
  | .drop name, supported => by
      simpa [RawCostTerm.components] using supported
  | .purse location stack, supported => by
      simpa [RawCostTerm.components] using supported

theorem RawCostProc.fromComponents_wellFormed : ∀ items : List RawCostProc,
    items.Forall (fun component => component.wellFormed = true) →
      (RawCostProc.fromComponents items).wellFormed = true
  | [], _ => rfl
  | head :: [], supported => by
      simpa [RawCostProc.fromComponents] using supported
  | head :: next :: rest, supported => by
      obtain ⟨head_ok, tail_ok⟩ :=
        (List.forall_cons (fun component : RawCostProc =>
          component.wellFormed = true) head (next :: rest)).mp supported
      simp only [RawCostProc.wellFormed, Bool.and_eq_true]
      exact ⟨head_ok,
        RawCostProc.fromComponents_wellFormed (next :: rest) tail_ok⟩

theorem RawCostTerm.fromComponents_wellFormed : ∀ items : List RawCostTerm,
    items.Forall (fun component => component.wellFormed = true) →
      (RawCostTerm.fromComponents items).wellFormed = true
  | [], _ => rfl
  | head :: [], supported => by
      simpa [RawCostTerm.fromComponents] using supported
  | head :: next :: rest, supported => by
      obtain ⟨head_ok, tail_ok⟩ :=
        (List.forall_cons (fun component : RawCostTerm =>
          component.wellFormed = true) head (next :: rest)).mp supported
      simp only [RawCostTerm.wellFormed, Bool.and_eq_true]
      exact ⟨head_ok,
        RawCostTerm.fromComponents_wellFormed (next :: rest) tail_ok⟩

mutual
  theorem RawCostName.wellFormed_normalize : ∀ name : RawCostName,
      name.wellFormed = true → name.normalize.wellFormed = true
    | .bvar _, _ => rfl
    | .quote term, supported => by
        have normalized_ok :=
          RawCostTerm.wellFormed_normalize term supported
        simp only [RawCostName.normalize]
        generalize normalized_eq : term.normalize = normalized at normalized_ok ⊢
        cases normalized <;>
          simp_all [RawCostName.wellFormed, RawCostTerm.wellFormed]
    | .signature sig, supported => by
        simpa [RawCostName.normalize, RawCostName.wellFormed] using
          RawCostSig.normalize_valid supported

  theorem RawCostProc.wellFormed_normalize : ∀ proc : RawCostProc,
      proc.wellFormed = true → proc.normalize.wellFormed = true
    | .nil, _ => rfl
    | .par left right, supported => by
        simp only [RawCostProc.wellFormed, Bool.and_eq_true] at supported
        have left_ok := RawCostProc.wellFormed_normalize left supported.1
        have right_ok := RawCostProc.wellFormed_normalize right supported.2
        apply RawCostProc.fromComponents_wellFormed
        apply stableSortBy_forall
        rw [List.forall_append]
        exact ⟨RawCostProc.components_forall_wellFormed left.normalize left_ok,
          RawCostProc.components_forall_wellFormed right.normalize right_ok⟩
    | .send channel payload, supported => by
        simp only [RawCostProc.wellFormed, Bool.and_eq_true] at supported ⊢
        exact ⟨RawCostName.wellFormed_normalize channel supported.1,
          RawCostTerm.wellFormed_normalize payload supported.2⟩
    | .recv channel body, supported => by
        simp only [RawCostProc.wellFormed, Bool.and_eq_true] at supported ⊢
        exact ⟨RawCostName.wellFormed_normalize channel supported.1,
          RawCostTerm.wellFormed_normalize body supported.2⟩

  theorem RawCostTerm.wellFormed_normalize : ∀ term : RawCostTerm,
      term.wellFormed = true → term.normalize.wellFormed = true
    | .nil, _ => rfl
    | .signed proc sig, supported => by
        simp only [RawCostTerm.wellFormed, Bool.and_eq_true] at supported ⊢
        exact ⟨RawCostProc.wellFormed_normalize proc supported.1,
          RawCostSig.normalize_valid supported.2⟩
    | .par left right, supported => by
        simp only [RawCostTerm.wellFormed, Bool.and_eq_true] at supported
        have left_ok := RawCostTerm.wellFormed_normalize left supported.1
        have right_ok := RawCostTerm.wellFormed_normalize right supported.2
        apply RawCostTerm.fromComponents_wellFormed
        apply stableSortBy_forall
        rw [List.forall_append]
        exact ⟨RawCostTerm.components_forall_wellFormed left.normalize left_ok,
          RawCostTerm.components_forall_wellFormed right.normalize right_ok⟩
    | .drop name, supported =>
        RawCostName.wellFormed_normalize name supported
    | .purse location stack, supported => by
        simp only [RawCostTerm.wellFormed, Bool.and_eq_true] at supported ⊢
        exact ⟨RawCostName.wellFormed_normalize location supported.1,
          RawCostStack.normalize_all_valid stack supported.2⟩
end

/-- Every normalized top-level component remains in the accepted grammar. -/
theorem RawCostTerm.normalizeConfig_forall_wellFormed {term : RawCostTerm}
    (supported : term.wellFormed = true) :
    term.normalizeConfig.Forall (fun component => component.wellFormed = true) := by
  apply stableSortBy_forall
  exact RawCostTerm.components_forall_wellFormed term.normalize
    (RawCostTerm.wellFormed_normalize term supported)

/-! ## Purse extraction and successor preservation -/

structure RawIndexedPurse.WellFormed (purse : RawIndexedPurse) : Prop where
  location : purse.location.wellFormed = true
  head : purse.head.valid = true
  tail : purse.tail.all RawCostSig.valid = true

theorem collectPursesAux_forall_wellFormed :
    ∀ (config : RawCostConfig) (index : Nat),
      config.Forall (fun term => term.wellFormed = true) →
      (collectPursesAux config index).Forall RawIndexedPurse.WellFormed
  | [], _, _ => trivial
  | term :: rest, index, supported => by
      obtain ⟨term_ok, rest_ok⟩ :=
        (List.forall_cons (fun item : RawCostTerm => item.wellFormed = true)
          term rest).mp supported
      have tail_ok := collectPursesAux_forall_wellFormed rest (index + 1) rest_ok
      cases term with
      | purse location stack =>
          cases stack with
          | nil => exact tail_ok
          | cons head tail =>
              simp only [RawCostTerm.wellFormed, List.all_cons,
                Bool.and_eq_true] at term_ok
              exact (List.forall_cons RawIndexedPurse.WellFormed
                ⟨index, location, head, tail⟩
                (collectPursesAux rest (index + 1))).mpr
                ⟨⟨term_ok.1, term_ok.2.1, term_ok.2.2⟩, tail_ok⟩
      | _ => exact tail_ok

theorem RawCostConfig.purses_forall_wellFormed {config : RawCostConfig}
    (supported : config.Forall (fun term => term.wellFormed = true)) :
    config.purses.Forall RawIndexedPurse.WellFormed :=
  collectPursesAux_forall_wellFormed config 0 supported

theorem eraseIndices_forall {predicate : RawCostTerm → Prop}
    {config : RawCostConfig} (supported : config.Forall predicate)
    (indices : List Nat) : (eraseIndices config indices).Forall predicate := by
  rw [List.forall_iff_forall_mem]
  intro term member
  simp only [eraseIndices, List.mem_map] at member
  obtain ⟨entry, entry_member, rfl⟩ := member
  have zipped := (List.mem_filter.mp entry_member).1
  exact List.forall_iff_forall_mem.mp supported entry.1
    (List.fst_mem_of_mem_zipIdx zipped)

theorem selected_tails_forall_wellFormed
    {config : RawCostConfig} (config_ok : config.Forall
      (fun term => term.wellFormed = true))
    {selected : List RawSelectedPurse} (selected_source : selected.Sublist config.purses) :
    (selected.map fun purse => RawCostTerm.purse purse.location purse.tail).Forall
      (fun term => term.wellFormed = true) := by
  rw [List.forall_iff_forall_mem]
  intro term term_member
  obtain ⟨purse, purse_member, rfl⟩ := List.mem_map.mp term_member
  have all_purses := config.purses_forall_wellFormed config_ok
  have purse_ok := List.forall_iff_forall_mem.mp all_purses purse
    (selected_source.mem purse_member)
  simp only [RawCostTerm.wellFormed, Bool.and_eq_true]
  exact ⟨purse_ok.location, purse_ok.tail⟩

/-- Generic successor construction preserves the raw wrapped grammar when its
contractum is supported and its selected purse occurrences came from the
source configuration. -/
theorem residualFor_wellFormed
    {config : RawCostConfig}
    (config_ok : config.Forall (fun term => term.wellFormed = true))
    (participants : List Nat) {selected : List RawSelectedPurse}
    (selected_source : selected.Sublist config.purses)
    {contractum : RawCostTerm} (contractum_ok : contractum.wellFormed = true) :
    (residualFor config participants selected contractum).wellFormed = true := by
  have retained_ok := eraseIndices_forall config_ok
    (participants ++ selected.map RawIndexedPurse.index)
  have normalized_contractum_ok :=
    RawCostTerm.wellFormed_normalize contractum contractum_ok
  have contractum_components_ok :=
    RawCostTerm.components_forall_wellFormed contractum.normalize
      normalized_contractum_ok
  have tails_ok := selected_tails_forall_wellFormed config_ok selected_source
  have all_components :
      (eraseIndices config (participants ++ selected.map RawIndexedPurse.index) ++
        contractum.normalize.components ++
        selected.map (fun purse => RawCostTerm.purse purse.location purse.tail)).Forall
        (fun term => term.wellFormed = true) := by
    simp only [List.forall_append]
    exact ⟨⟨retained_ok, contractum_components_ok⟩, tails_ok⟩
  unfold residualFor
  exact RawCostTerm.wellFormed_normalize _
    (RawCostTerm.fromComponents_wellFormed _ all_components)

structure RawWholeRedex.WellFormed (redex : RawWholeRedex) : Prop where
  body : redex.body.wellFormed = true
  payload : redex.payload.wellFormed = true
  sig : redex.sig.valid = true

structure RawRecvEndpoint.WellFormed (endpoint : RawRecvEndpoint) : Prop where
  body : endpoint.body.wellFormed = true
  sig : endpoint.sig.valid = true

structure RawSendEndpoint.WellFormed (endpoint : RawSendEndpoint) : Prop where
  payload : endpoint.payload.wellFormed = true
  sig : endpoint.sig.valid = true

theorem wholeAt?_wellFormed (index : Nat) :
    ∀ term redex, term.wellFormed = true →
      wholeAt? index term = some redex → redex.WellFormed
  | .signed (.par (.recv recvLocation body) (.send sendLocation payload)) sig,
      redex, supported, found => by
      simp only [RawCostTerm.wellFormed, RawCostProc.wellFormed,
        Bool.and_eq_true] at supported
      simp only [wholeAt?] at found
      split at found
      · simp only [Option.some.injEq] at found
        subst redex
        exact ⟨supported.1.1.2, supported.1.2.2,
          RawCostSig.normalize_valid supported.2⟩
      · contradiction
  | .signed (.par (.send sendLocation payload) (.recv recvLocation body)) sig,
      redex, supported, found => by
      simp only [RawCostTerm.wellFormed, RawCostProc.wellFormed,
        Bool.and_eq_true] at supported
      simp only [wholeAt?] at found
      split at found
      · simp only [Option.some.injEq] at found
        subst redex
        exact ⟨supported.1.2.2, supported.1.1.2,
          RawCostSig.normalize_valid supported.2⟩
      · contradiction
  | term, redex, _supported, found => by
      cases term with
      | signed proc sig =>
          cases proc with
          | par left right =>
              cases left <;> cases right <;> simp [wholeAt?] at found
              all_goals
                rcases found with ⟨_locations, rfl⟩
                simp only [RawCostTerm.wellFormed, RawCostProc.wellFormed,
                  Bool.and_eq_true] at _supported
                refine ⟨?_, ?_, RawCostSig.normalize_valid _supported.2⟩ <;>
                  aesop
          | _ => simp [wholeAt?] at found
      | _ => simp [wholeAt?] at found

theorem recvAt?_wellFormed (index : Nat) :
    ∀ term endpoint, term.wellFormed = true →
      recvAt? index term = some endpoint → endpoint.WellFormed
  | .signed (.recv location body) sig, endpoint, supported, found => by
      simp only [RawCostTerm.wellFormed, RawCostProc.wellFormed,
        Bool.and_eq_true] at supported
      simp only [recvAt?, Option.some.injEq] at found
      subst endpoint
      exact ⟨supported.1.2, RawCostSig.normalize_valid supported.2⟩
  | term, endpoint, _supported, found => by
      cases term <;> simp [recvAt?] at found
      rename_i proc sig
      cases proc <;> simp at found
      all_goals
        subst endpoint
        simp only [RawCostTerm.wellFormed, RawCostProc.wellFormed,
          Bool.and_eq_true] at _supported
        exact ⟨_supported.1.2, RawCostSig.normalize_valid _supported.2⟩

theorem sendAt?_wellFormed (index : Nat) :
    ∀ term endpoint, term.wellFormed = true →
      sendAt? index term = some endpoint → endpoint.WellFormed
  | .signed (.send location payload) sig, endpoint, supported, found => by
      simp only [RawCostTerm.wellFormed, RawCostProc.wellFormed,
        Bool.and_eq_true] at supported
      simp only [sendAt?, Option.some.injEq] at found
      subst endpoint
      exact ⟨supported.1.2, RawCostSig.normalize_valid supported.2⟩
  | term, endpoint, _supported, found => by
      cases term <;> simp [sendAt?] at found
      rename_i proc sig
      cases proc <;> simp at found
      all_goals
        subst endpoint
        simp only [RawCostTerm.wellFormed, RawCostProc.wellFormed,
          Bool.and_eq_true] at _supported
        exact ⟨_supported.1.2, RawCostSig.normalize_valid _supported.2⟩

theorem collectWholesAux_forall_wellFormed :
    ∀ (config : RawCostConfig) (index : Nat),
      config.Forall (fun term => term.wellFormed = true) →
      (collectWholesAux config index).Forall RawWholeRedex.WellFormed
  | [], _, _ => trivial
  | term :: rest, index, supported => by
      obtain ⟨term_ok, rest_ok⟩ :=
        (List.forall_cons (fun item : RawCostTerm => item.wellFormed = true)
          term rest).mp supported
      have tail_ok := collectWholesAux_forall_wellFormed rest (index + 1) rest_ok
      cases found : wholeAt? index term with
      | none => simpa [collectWholesAux, found] using tail_ok
      | some redex =>
          rw [collectWholesAux, found]
          exact (List.forall_cons RawWholeRedex.WellFormed redex
            (collectWholesAux rest (index + 1))).mpr
            ⟨wholeAt?_wellFormed index term redex term_ok found, tail_ok⟩

theorem collectRecvsAux_forall_wellFormed :
    ∀ (config : RawCostConfig) (index : Nat),
      config.Forall (fun term => term.wellFormed = true) →
      (collectRecvsAux config index).Forall RawRecvEndpoint.WellFormed
  | [], _, _ => trivial
  | term :: rest, index, supported => by
      obtain ⟨term_ok, rest_ok⟩ :=
        (List.forall_cons (fun item : RawCostTerm => item.wellFormed = true)
          term rest).mp supported
      have tail_ok := collectRecvsAux_forall_wellFormed rest (index + 1) rest_ok
      cases found : recvAt? index term with
      | none => simpa [collectRecvsAux, found] using tail_ok
      | some endpoint =>
          rw [collectRecvsAux, found]
          exact (List.forall_cons RawRecvEndpoint.WellFormed endpoint
            (collectRecvsAux rest (index + 1))).mpr
            ⟨recvAt?_wellFormed index term endpoint term_ok found, tail_ok⟩

theorem collectSendsAux_forall_wellFormed :
    ∀ (config : RawCostConfig) (index : Nat),
      config.Forall (fun term => term.wellFormed = true) →
      (collectSendsAux config index).Forall RawSendEndpoint.WellFormed
  | [], _, _ => trivial
  | term :: rest, index, supported => by
      obtain ⟨term_ok, rest_ok⟩ :=
        (List.forall_cons (fun item : RawCostTerm => item.wellFormed = true)
          term rest).mp supported
      have tail_ok := collectSendsAux_forall_wellFormed rest (index + 1) rest_ok
      cases found : sendAt? index term with
      | none => simpa [collectSendsAux, found] using tail_ok
      | some endpoint =>
          rw [collectSendsAux, found]
          exact (List.forall_cons RawSendEndpoint.WellFormed endpoint
            (collectSendsAux rest (index + 1))).mpr
            ⟨sendAt?_wellFormed index term endpoint term_ok found, tail_ok⟩

theorem RawCostConfig.wholeRedexes_forall_wellFormed {config : RawCostConfig}
    (supported : config.Forall (fun term => term.wellFormed = true)) :
    config.wholeRedexes.Forall RawWholeRedex.WellFormed :=
  collectWholesAux_forall_wellFormed config 0 supported

theorem RawCostConfig.recvEndpoints_forall_wellFormed {config : RawCostConfig}
    (supported : config.Forall (fun term => term.wellFormed = true)) :
    config.recvEndpoints.Forall RawRecvEndpoint.WellFormed :=
  collectRecvsAux_forall_wellFormed config 0 supported

theorem RawCostConfig.sendEndpoints_forall_wellFormed {config : RawCostConfig}
    (supported : config.Forall (fun term => term.wellFormed = true)) :
    config.sendEndpoints.Forall RawSendEndpoint.WellFormed :=
  collectSendsAux_forall_wellFormed config 0 supported

theorem RawCostSig.append_valid_left {left right : RawCostSig}
    (left_valid : left.valid = true) : (left ++ right).valid = true := by
  have left_nonempty : left ≠ [] := by
    simpa [RawCostSig.valid] using left_valid
  have append_nonempty : left ++ right ≠ [] := by
    intro empty
    exact left_nonempty (List.append_eq_nil_iff.mp empty).1
  simpa [RawCostSig.valid] using append_nonempty

private theorem wholeCandidates_wellWrapped
    {config : RawCostConfig}
    (config_ok : config.Forall (fun term => term.wellFormed = true))
    {redex : RawWholeRedex} (redex_ok : redex.WellFormed)
    {step : RawRuntimeStep}
    (member : step ∈ wholeCandidates config config.purses redex) :
    step.spend.valid = true ∧ step.contractum.wellFormed = true ∧
      step.residual.wellFormed = true := by
  simp only [wholeCandidates] at member
  obtain ⟨cover, cover_member, rfl⟩ := List.mem_map.mp member
  have selected_source : cover.Sublist config.purses :=
    (exactPurseCovers_sublist cover_member).trans List.filter_sublist
  have opened_ok := RawCostTerm.wellFormed_commSubst redex_ok.body redex_ok.payload
  have contractum_ok := RawCostTerm.wellFormed_normalize _ opened_ok
  exact ⟨redex_ok.sig, contractum_ok,
    residualFor_wellFormed config_ok [redex.index] selected_source contractum_ok⟩

private theorem splitCandidates_wellWrapped
    {config : RawCostConfig}
    (config_ok : config.Forall (fun term => term.wellFormed = true))
    {recv : RawRecvEndpoint} (recv_ok : recv.WellFormed)
    {send : RawSendEndpoint} (send_ok : send.WellFormed)
    {step : RawRuntimeStep}
    (member : step ∈ splitCandidates config config.purses recv send) :
    step.spend.valid = true ∧ step.contractum.wellFormed = true ∧
      step.residual.wellFormed = true := by
  unfold splitCandidates at member
  split at member
  · obtain ⟨cover, cover_member, rfl⟩ := List.mem_map.mp member
    have selected_source : cover.Sublist config.purses :=
      (exactPurseCovers_sublist cover_member).trans List.filter_sublist
    have spend_ok := RawCostSig.normalize_valid
      (RawCostSig.append_valid_left (left := recv.sig) (right := send.sig)
        recv_ok.sig)
    have opened_ok := RawCostTerm.wellFormed_commSubst recv_ok.body send_ok.payload
    have contractum_ok := RawCostTerm.wellFormed_normalize _ opened_ok
    exact ⟨spend_ok, contractum_ok,
      residualFor_wellFormed config_ok [recv.index, send.index]
        selected_source contractum_ok⟩
  · contradiction

/-- Every occurrence-sensitive candidate preserves the raw wrapped grammar. -/
theorem runtimeCostCandidatesFromConfig_wellWrapped
    {config : RawCostConfig}
    (config_ok : config.Forall (fun term => term.wellFormed = true))
    {step : RawRuntimeStep}
    (member : step ∈ runtimeCostCandidatesFromConfig config) :
    step.spend.valid = true ∧ step.contractum.wellFormed = true ∧
      step.residual.wellFormed = true := by
  simp only [runtimeCostCandidatesFromConfig, List.mem_append] at member
  rcases member with whole | split
  · obtain ⟨redex, redex_member, step_member⟩ := List.mem_flatMap.mp whole
    have redex_ok := List.forall_iff_forall_mem.mp
      (config.wholeRedexes_forall_wellFormed config_ok) redex redex_member
    exact wholeCandidates_wellWrapped config_ok redex_ok step_member
  · obtain ⟨recv, recv_member, send_branch⟩ := List.mem_flatMap.mp split
    obtain ⟨send, send_member, step_member⟩ := List.mem_flatMap.mp send_branch
    have recv_ok := List.forall_iff_forall_mem.mp
      (config.recvEndpoints_forall_wellFormed config_ok) recv recv_member
    have send_ok := List.forall_iff_forall_mem.mp
      (config.sendEndpoints_forall_wellFormed config_ok) send send_member
    exact splitCandidates_wellWrapped config_ok recv_ok send_ok step_member

/-- Public frontier deduplication never invents a firing occurrence. -/
private theorem foldl_deduplicate_mem
    (target : RawRuntimeStep) : ∀ (source retained : List RawRuntimeStep),
    target ∈ source.foldl (fun kept candidate =>
      if kept.any (samePublicTransition candidate) then kept
      else kept ++ [candidate]) retained →
    target ∈ retained ∨ target ∈ source
  | [], retained, member => Or.inl member
  | candidate :: rest, retained, member => by
      simp only [List.foldl_cons] at member
      have tail_result := foldl_deduplicate_mem target rest
        (if retained.any (samePublicTransition candidate) then retained
          else retained ++ [candidate]) member
      rcases tail_result with prior | later
      · split at prior
        · exact Or.inl prior
        · have inserted : target ∈ retained ∨ target = candidate := by
            simpa using prior
          rcases inserted with old | rfl
          · exact Or.inl old
          · exact Or.inr (by simp)
      · exact Or.inr (by simp [later])

theorem mem_of_mem_deduplicatePublicTransitions
    {target : RawRuntimeStep} {source : List RawRuntimeStep}
    (member : target ∈ deduplicatePublicTransitions source) : target ∈ source := by
  have result := foldl_deduplicate_mem target source [] member
  simpa [deduplicatePublicTransitions] using result

/-- The checked public frontier returns only supported contracta and residuals. -/
theorem runtimeCostFrontier_wellWrapped
    {term : RawCostTerm} {frontier : List RawRuntimeStep}
    (result : runtimeCostFrontier term = some frontier)
    {step : RawRuntimeStep} (member : step ∈ frontier) :
    step.spend.valid = true ∧ step.contractum.wellFormed = true ∧
      step.residual.wellFormed = true := by
  unfold runtimeCostFrontier runtimeCostCandidates at result
  split at result <;> rename_i term_ok
  · change some (deduplicatePublicTransitions
      (runtimeCostCandidatesFromConfig term.normalizeConfig)) = some frontier at result
    injection result with result
    subst frontier
    have candidate_member := mem_of_mem_deduplicatePublicTransitions member
    have wellFormed : term.wellFormed = true := by
      simp only [RawCostTerm.supported, Bool.and_eq_true] at term_ok
      exact term_ok.1
    exact runtimeCostCandidatesFromConfig_wellWrapped
      (RawCostTerm.normalizeConfig_forall_wellFormed wellFormed) candidate_member
  · simp at result

/-- Public one-step execution preserves the accepted wrapped grammar. -/
theorem wellWrapped_preserved
    {term : RawCostTerm} {frontier : List RawRuntimeStep}
    (result : runtimeCostFrontier term = some frontier)
    {step : RawRuntimeStep} (member : step ∈ frontier) :
    step.spend.valid = true ∧ step.contractum.wellFormed = true ∧
      step.residual.wellFormed = true :=
  runtimeCostFrontier_wellWrapped result member

/-- A free drop is inert.  COMM substitution may open a matched bound drop,
but the executable frontier never unwraps a standalone drop. -/
theorem no_free_redex (name : RawCostName)
    (supported : name.wellFormed = true)
    (scopeSafe : name.runtimeBinderSafeAt 0 = true) :
    runtimeCostFrontier (.drop name) = some [] := by
  simp [runtimeCostFrontier, runtimeCostCandidates, RawCostTerm.supported,
    RawCostTerm.runtimeBinderSafe, supported, scopeSafe,
    RawCostTerm.normalizeConfig, RawCostTerm.normalize,
    RawCostTerm.components, stableKeySort, stableSortBy,
    runtimeCostCandidatesFromConfig, RawCostConfig.purses,
    RawCostConfig.wholeRedexes, RawCostConfig.recvEndpoints,
    RawCostConfig.sendEndpoints, collectPursesAux, collectWholesAux,
    collectRecvsAux, collectSendsAux, deduplicatePublicTransitions]

/-- A public executable firing has no ambient funding source. -/
theorem runtimeCostFrontier_no_ambient_funding
    {term : RawCostTerm} {frontier : List RawRuntimeStep}
    (result : runtimeCostFrontier term = some frontier)
    {step : RawRuntimeStep} (member : step ∈ frontier) :
    step.selectedPurses ≠ [] := by
  unfold runtimeCostFrontier runtimeCostCandidates at result
  split at result <;> rename_i term_ok
  · change some (deduplicatePublicTransitions
      (runtimeCostCandidatesFromConfig term.normalizeConfig)) = some frontier at result
    injection result with result
    subst frontier
    have candidate_member := mem_of_mem_deduplicatePublicTransitions member
    have funding := runtimeCostCandidatesFromConfig_funding_valid candidate_member
    have wellFormed : term.wellFormed = true := by
      simp only [RawCostTerm.supported, Bool.and_eq_true] at term_ok
      exact term_ok.1
    have wrapped := runtimeCostCandidatesFromConfig_wellWrapped
      (RawCostTerm.normalizeConfig_forall_wellFormed wellFormed) candidate_member
    exact funding.no_ambient_funding wrapped.1
  · simp at result

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost
