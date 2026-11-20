import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Examples

/-!
# Renaming names: the step is equivariant

A **name** is a constant or a function symbol of the term syntax. Renaming the names of a system renames
every term of its rules, of its knowledge and of its labels; the program is renamed with the state. The
occurrence identities, the selections, the collect claims and the numbers of the count queries stay: they
are not terms. (Law 1, `Equivalence.Renaming`, renames the occurrence identities instead.)

The setting is the step of a program at one frame (`OneFrame`), over any substitution action
`A : SubstitutionAction T S`.

* **A renaming of the action** (`Renaming`): bijections `term : T ≃ T` and `subst : S ≃ S` such that
  substituting commutes with renaming, `A.apply (subst σ) (term t) = term (A.apply σ t)`, and the
  declared equality `A.E` is preserved and reflected. **An automorphism** (`Automorphism`) is a renaming
  that also fixes the identity substitution and preserves composition.
* **Syntax is renamed by maps** (`renameStore`, `renameRule`, `renameProgram`, `renameState`,
  `renameFiring`): every term by the term map, the opening by the substitution map. A count query keeps
  its number, a numeral of the syntax and not a term (`renameCheck_count`).

## The step is equivariant

For every renaming `ρ` of the action, a firing renamed by `ρ`

* is fresh at the renamed state exactly when the original is (`fresh_renameFiring`);
* has the renamed information (`information_renameFiring`), the same checks and collect query at the renamed
  solutions (`holds_renameFiring`), and the same enabling (`enabled_renameFiring`);
* is admitted exactly when the original is (`admits_renameFiring`), with the renamed result
  (`result_renameFiring`).

Every firing of the renamed program is a renamed firing (`exists_renameFiring`).

## Runs and outcomes correspond

The successors (`succ_rename_iff`, `succ_of_rename`), the reachable states (`reachable_rename`) and the
terminal outcomes (`terminal_rename_iff`, `outcomes_rename`) of the renamed system are the renamed ones.
Runs are renamed as dependent words of admitted firings (`renameRun`): a renamed run ends at the renamed
state (`last_renameRun`) and fires the renamed firings in the same order (`word_renameRun`).
`step_equivariant` collects admission, results, firings, reachable states and terminal outcomes. The
program is renamed with the state; when the renaming fixes every rule of the program
(`renameProgram_eq_of_fixed`), the same program relates a state and its renamed copy
(`reachable_rename_of_fixed`, `outcomes_rename_of_fixed`).

The identity and composition laws of an automorphism are used only here: the morphism of frames that a
firing moves along (`along_renameFiring`), and that a run moves along (`toLast_renameRun`), is renamed by
the substitution map. Admission, results, reachable states and outcomes need only a renaming.

## First-order terms

A permutation of the constants with an arity-preserving permutation of the function symbols
(`NamePermutation`) renames first-order terms (`NamePermutation.rename`; variables are unknowns, not
names, and stay) and substitutions (`σ ↦ rename ∘ σ`). It is an automorphism of `FirstOrder.action`,
the substitution action of the existing unifier `unifyTotal` (`NamePermutation.automorphism`). Hence
`names_equivariant`, with its parts `admits_renameNames`, `result_renameNames`,
`reachable_renameNames` and `outcomes_renameNames`. Finitely many names suffice to give one: distinct
constants matched position by position, and distinct function symbols matched with equal arities, extend
to a permutation of names (`NamePermutation.exists_of_lists`, from `exists_perm_map_eq`). Permuting the
unknowns among themselves is an automorphism too (`unknownsAutomorphism`), and renamings compose
(`Renaming.trans`), so names and unknowns may be renamed together, each kind among itself.

## Controls

* **Positive** (`PositiveControl`): the rule `consume` (take a token `1`, make a `2`) at a token `1`,
  with the names `1` and `3` exchanged. The renamed firing is admitted at the renamed state
  (`renamed_admitted`), while the original firing is refused there (`original_refused_at_renamed`); a
  run reaches a terminal outcome (`consumeOnly_outcome`), and its renamed copy is a terminal outcome of
  the renamed system (`renamed_outcome`).
* **Negative** (`NegativeControl`): over `collapsing`, a substitution action whose declared equality
  identifies the constants `0` and `1`, exchanging the names `1` and `2` commutes with substitution,
  fixes the identity and preserves composition, but does not respect the declared equality
  (`swapOneTwo_laws`). The firing that takes a row `0` for the pattern `1` is admitted
  (`takeFiring_admitted`); its renamed copy, which takes the row `0` for the pattern `2`, is refused
  (`renamed_takeFiring_refused`). Here the declared equality interprets the names `0` and `1` beyond
  equality of names, and the exchange of `1` and `2` does not respect it.
* **Negative** (`UnknownControl`): exchanging the unknown `x` with the name `5` is a bijection of the
  first-order terms that keeps their equality, but substituting does not commute with it, so it is no
  renaming of the action (`unknownToName_laws`). The firing that reads a row `7` for the pattern `x` is
  admitted (`readFiring_admitted`); its copy, which reads the row `7` for the pattern `5`, is refused
  (`renamed_readFiring_refused`). Exchanging an unknown with a name is not a renaming of names.
  Permuting the unknowns among themselves is a renaming (`unknownsAutomorphism`), and renamings compose
  (`Renaming.trans`): the answer of the examples with the names `5`, `7` and the unknowns `0`, `1`
  exchanged together is admitted at the renamed request (`answer_admitted_renamed`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Equivalence.NameRenaming

open Interface (Frames)
open MeTTaCalculus.OccurrenceCommits (Enabled fire)
open LogicOverTheStep.StepSpan (Succ)
open OneFrame (Terms frames ext)

universe uT uS uO

/-! ## Renaming syntax -/

section Syntax

variable {T : Type uT} {S : Type uS} {O : Type uO}

/-- The equations of a store, with their terms renamed. -/
def renameStore (ρ : T → T) (store : EquationStore T) : EquationStore T :=
  store.map fun e => (ρ e.1, ρ e.2)

/-- **A rule with its names renamed**: every term of its body (`RuleInstance.map`) and every collect query
pattern renamed. The number of a count query is a numeral of the syntax, not a term, and stays
(`renameCheck_count`). -/
def renameRule (ρ : T → T) (r : Rule (Terms T)) : Rule (Terms T) :=
  ⟨r.locals, r.body.map ρ, r.collect.map ρ⟩

/-- **Count numerals are syntax, not terms**: renaming a count query renames its pattern and keeps its
number. -/
theorem renameCheck_count (ρ : T → T) (pattern : T) (number : ℕ) :
    Check.map ρ (.count pattern number) = .count (ρ pattern) number :=
  rfl

/-- **A program with its names renamed**: its rules, renamed. -/
def renameProgram (ρ : T → T) (P : Program (Terms T)) : Program (Terms T) :=
  renameRule ρ '' P

/-- **A state with its names renamed**: its knowledge and its labels renamed; the frame and the present
occurrences stay. -/
def renameState (ρ : T → T) (s : State (Terms T) O) : State (Terms T) O :=
  ⟨s.frame, renameStore ρ s.knowledge, s.present, fun o => ρ (s.label o)⟩

/-- **A firing with its names renamed**: the renamed rule, a rule of the renamed program; the same
extension; the renamed opening; the same selection and collect claims. -/
def renameFiring {A : SubstitutionAction T S} (ρ : T → T) (ρS : S → S) {P : Program (Terms T)}
    {a : PUnit.{1}} (f : Firing O (ext A) P a) : Firing O (ext A) (renameProgram ρ P) a :=
  ⟨renameRule ρ f.rule, Set.mem_image_of_mem (renameRule ρ) f.member, f.ext, ρS f.opening,
    f.selection, f.seen⟩

theorem check_map_map (f g : T → T) :
    ∀ c : Check T, Check.map g (Check.map f c) = Check.map (fun t => g (f t)) c
  | .equal _ _ => rfl
  | .predicate _ _ => rfl
  | .count _ _ => rfl

theorem ruleInstance_map_map (f g : T → T) (r : RuleInstance T) :
    (r.map f).map g = r.map (fun t => g (f t)) := by
  cases r
  simp only [RuleInstance.map, List.map_map, Function.comp_def, check_map_map]

theorem checkTerms_map (ρ : T → T) : ∀ c : Check T, checkTerms (Check.map ρ c) = (checkTerms c).map ρ
  | .equal _ _ => rfl
  | .predicate _ _ => rfl
  | .count _ _ => rfl

/-- **A renamed rule has the renamed terms.** -/
theorem terms_renameRule (ρ : T → T) (r : Rule (Terms T)) :
    (renameRule ρ r).terms = r.terms.map ρ := by
  simp only [Rule.terms, renameRule, RuleInstance.map, List.map_append, List.map_map,
    Function.comp_def, List.flatMap_map, List.map_flatMap, checkTerms_map]

theorem renameState_comp (ρ ρ' : T → T) (s : State (Terms T) O) :
    renameState ρ' (renameState ρ s) = renameState (fun t => ρ' (ρ t)) s := by
  simp only [renameState, renameStore, List.map_map, Function.comp_def]

theorem renameState_id (s : State (Terms T) O) : renameState (fun t => t) s = s := by
  cases s
  simp only [renameState, renameStore, Prod.mk.eta, List.map_id']

end Syntax

/-! ## Renamings and automorphisms of a substitution action -/

section Renamings

variable {T : Type uT} {S : Type uS}

/-- **A renaming of a substitution action**: bijections of the terms and of the substitutions such that
substituting commutes with renaming, and the declared equality is preserved and reflected. -/
structure Renaming (A : SubstitutionAction T S) where
  /-- The renaming of terms. -/
  term : T ≃ T
  /-- The renaming of substitutions. -/
  subst : S ≃ S
  /-- Substituting commutes with renaming. -/
  apply_rename : ∀ σ t, A.apply (subst σ) (term t) = term (A.apply σ t)
  /-- The declared equality is preserved and reflected. -/
  E_rename : ∀ s t, A.E (term s) (term t) ↔ A.E s t

/-- **An automorphism of a substitution action**: a renaming that also fixes the identity substitution
and preserves composition. -/
structure Automorphism (A : SubstitutionAction T S) extends Renaming A where
  /-- The identity substitution is fixed. -/
  identity_rename : subst A.identity = A.identity
  /-- Composition is preserved. -/
  compose_rename : ∀ σ τ, subst (A.compose σ τ) = A.compose (subst σ) (subst τ)

namespace Renaming

variable {A : SubstitutionAction T S} (ρ : Renaming A)

/-- **The inverse renaming.** -/
def symm : Renaming A where
  term := ρ.term.symm
  subst := ρ.subst.symm
  apply_rename σ t := by
    rw [Equiv.eq_symm_apply, ← ρ.apply_rename, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  E_rename s t := by
    rw [← ρ.E_rename, Equiv.apply_symm_apply, Equiv.apply_symm_apply]

/-- **Renamings compose**: first `ρ₁`, then `ρ₂`. -/
def trans (ρ₁ ρ₂ : Renaming A) : Renaming A where
  term := ρ₁.term.trans ρ₂.term
  subst := ρ₁.subst.trans ρ₂.subst
  apply_rename σ t := by
    simp only [Equiv.trans_apply]
    rw [ρ₂.apply_rename, ρ₁.apply_rename]
  E_rename s t := by
    simp only [Equiv.trans_apply]
    rw [ρ₂.E_rename, ρ₁.E_rename]

/-- The declared equality of two substituted terms is unchanged when the substitutions and the terms are
renamed. -/
theorem E_apply (σ τ : S) (s t : T) :
    A.E (A.apply (ρ.subst σ) (ρ.term s)) (A.apply (ρ.subst τ) (ρ.term t)) ↔
      A.E (A.apply σ s) (A.apply τ t) := by
  rw [ρ.apply_rename, ρ.apply_rename, ρ.E_rename]

end Renaming

namespace Automorphism

variable {A : SubstitutionAction T S} (α : Automorphism A)

/-- The morphism a firing at one frame moves along after a morphism `x`, renamed. -/
theorem compose_identity_rename (x : S) :
    α.subst (A.compose x (A.compose A.identity A.identity)) =
      A.compose (α.subst x) (A.compose A.identity A.identity) := by
  rw [α.compose_rename, α.compose_rename, α.identity_rename]

end Automorphism

end Renamings

/-! ## The step is equivariant -/

section Step

variable {T : Type uT} {S : Type uS} {A : SubstitutionAction T S} (ρ : Renaming A) {O : Type uO}

/-- **A renamed state mentions exactly the renamed terms.** -/
theorem mentions_renameState (s : State (Terms T) O) (t : T) :
    (renameState ρ.term s).Mentions (ρ.term t) ↔ s.Mentions t := by
  simp only [State.Mentions, renameState, renameStore, List.map_map, Function.comp_def, List.mem_map,
    Equiv.apply_eq_iff_eq]

theorem mentions_renameState_iff (s : State (Terms T) O) (t : T) :
    (renameState ρ.term s).Mentions t ↔ s.Mentions (ρ.term.symm t) := by
  rw [← mentions_renameState ρ s (ρ.term.symm t), Equiv.apply_symm_apply]

/-- **A renamed firing is fresh at the renamed state exactly when the original is.** -/
theorem fresh_renameFiring {P : Program (Terms T)} {s : State (Terms T) O}
    (f : Firing O (ext A) P s.frame) :
    (renameFiring ρ.term ρ.subst f).Fresh (frames A) (renameState ρ.term s) ↔
      f.Fresh (frames A) s := by
  constructor
  · intro fresh b g h
    obtain ⟨u, state, rule⟩ := fresh b (ρ.subst g) (ρ.subst h)
    refine ⟨ρ.subst.symm u, fun t mentioned => ?_, fun t member => ?_⟩
    · have renamed : A.E (A.apply u (A.apply A.identity (ρ.term t))) (A.apply (ρ.subst g) (ρ.term t)) :=
        state (ρ.term t) ((mentions_renameState ρ s t).mpr mentioned)
      show A.E (A.apply (ρ.subst.symm u) (A.apply A.identity t)) (A.apply g t)
      rw [A.apply_identity] at renamed ⊢
      rw [← Equiv.apply_symm_apply ρ.subst u] at renamed
      exact (ρ.E_apply _ _ _ _).mp renamed
    · have member' : ρ.term t ∈ (renameFiring ρ.term ρ.subst f).rule.terms := by
        show ρ.term t ∈ (renameRule ρ.term f.rule).terms
        rw [terms_renameRule]
        exact List.mem_map_of_mem member
      have renamed : A.E (A.apply u (A.apply (ρ.subst f.opening) (ρ.term t)))
          (A.apply (ρ.subst h) (ρ.term t)) := rule (ρ.term t) member'
      show A.E (A.apply (ρ.subst.symm u) (A.apply f.opening t)) (A.apply h t)
      rw [ρ.apply_rename f.opening t, ← Equiv.apply_symm_apply ρ.subst u] at renamed
      exact (ρ.E_apply _ _ _ _).mp renamed
  · intro fresh b g h
    obtain ⟨u, state, rule⟩ := fresh b (ρ.subst.symm g) (ρ.subst.symm h)
    refine ⟨ρ.subst u, fun t mentioned => ?_, fun t member => ?_⟩
    · have original : A.E (A.apply u (A.apply A.identity (ρ.term.symm t)))
          (A.apply (ρ.subst.symm g) (ρ.term.symm t)) :=
        state (ρ.term.symm t) ((mentions_renameState_iff ρ s t).mp mentioned)
      show A.E (A.apply (ρ.subst u) (A.apply A.identity t)) (A.apply g t)
      rw [A.apply_identity] at original ⊢
      have renamed := (ρ.E_apply u (ρ.subst.symm g) (ρ.term.symm t) (ρ.term.symm t)).mpr original
      rwa [Equiv.apply_symm_apply, Equiv.apply_symm_apply] at renamed
    · change t ∈ (renameRule ρ.term f.rule).terms at member
      rw [terms_renameRule] at member
      obtain ⟨t', member', rfl⟩ := List.mem_map.mp member
      have original : A.E (A.apply u (A.apply f.opening t')) (A.apply (ρ.subst.symm h) t') :=
        rule t' member'
      show A.E (A.apply (ρ.subst u) (A.apply (ρ.subst f.opening) (ρ.term t'))) (A.apply h (ρ.term t'))
      rw [ρ.apply_rename f.opening t']
      have renamed := (ρ.E_apply u (ρ.subst.symm h) (A.apply f.opening t') t').mpr original
      rwa [Equiv.apply_symm_apply] at renamed

/-- **A renamed firing opens to the renamed rule instance.** -/
theorem opened_renameFiring {P : Program (Terms T)} {a : PUnit.{1}} (f : Firing O (ext A) P a) :
    (renameFiring ρ.term ρ.subst f).opened (frames A) = (f.opened (frames A)).map ρ.term := by
  show (f.rule.body.map ρ.term).map (A.apply (ρ.subst f.opening)) =
    (f.rule.body.map (A.apply f.opening)).map ρ.term
  rw [ruleInstance_map_map, ruleInstance_map_map]
  exact congrArg (fun g : T → T => f.rule.body.map g) (funext fun t => ρ.apply_rename f.opening t)

/-- **A renamed firing opens to the renamed collect patterns.** -/
theorem collectOpened_renameFiring {P : Program (Terms T)} {a : PUnit.{1}} (f : Firing O (ext A) P a) :
    (renameFiring ρ.term ρ.subst f).collectOpened (frames A) =
      (f.collectOpened (frames A)).map ρ.term := by
  show (f.rule.collect.map ρ.term).map (A.apply (ρ.subst f.opening)) =
    (f.rule.collect.map (A.apply f.opening)).map ρ.term
  rw [List.map_map, List.map_map]
  exact List.map_congr_left fun t _ => ρ.apply_rename f.opening t

/-- **A renamed firing reads the renamed rows.** -/
theorem row_renameFiring {P : Program (Terms T)} {s : State (Terms T) O}
    (f : Firing O (ext A) P s.frame) (o : O) :
    (renameFiring ρ.term ρ.subst f).row (frames A) (renameState ρ.term s) o =
      ρ.term (f.row (frames A) s o) := by
  show A.apply A.identity (ρ.term (s.label o)) = ρ.term (A.apply A.identity (s.label o))
  rw [A.apply_identity, A.apply_identity]

/-- **A renamed firing has the renamed information.** -/
theorem information_renameFiring {P : Program (Terms T)} {s : State (Terms T) O}
    (f : Firing O (ext A) P s.frame) :
    (renameFiring ρ.term ρ.subst f).information (frames A) (renameState ρ.term s) =
      renameStore ρ.term (f.information (frames A) s) := by
  show List.map (fun e => (A.apply A.identity e.1, A.apply A.identity e.2))
        (renameStore ρ.term s.knowledge) ++
      List.zipWith (fun p o => (p, A.apply A.identity (ρ.term (s.label o))))
        (List.map (A.apply (ρ.subst f.opening)) (List.map ρ.term f.rule.body.take))
        f.selection.taken ++
      List.zipWith (fun p o => (p, A.apply A.identity (ρ.term (s.label o))))
        (List.map (A.apply (ρ.subst f.opening)) (List.map ρ.term f.rule.body.read))
        f.selection.read ++
      List.map (fun e => (A.apply (ρ.subst f.opening) e.1, A.apply (ρ.subst f.opening) e.2))
        (List.map (fun e => (ρ.term e.1, ρ.term e.2)) f.rule.body.tell) =
    renameStore ρ.term
      (List.map (fun e => (A.apply A.identity e.1, A.apply A.identity e.2)) s.knowledge ++
        List.zipWith (fun p o => (p, A.apply A.identity (s.label o)))
          (List.map (A.apply f.opening) f.rule.body.take) f.selection.taken ++
        List.zipWith (fun p o => (p, A.apply A.identity (s.label o)))
          (List.map (A.apply f.opening) f.rule.body.read) f.selection.read ++
        List.map (fun e => (A.apply f.opening e.1, A.apply f.opening e.2)) f.rule.body.tell)
  simp only [renameStore, List.map_append, List.map_map, List.map_zipWith, List.zipWith_map_left,
    Function.comp_def, A.apply_identity, ρ.apply_rename]

/-- The rows a renamed solution equates with a renamed pattern are the rows the solution equates with
the pattern. -/
theorem matchesAt_rename {a b : PUnit.{1}} (σ : S) (row row' : O → T)
    (renamed : ∀ o, row' o = ρ.term (row o)) (W : Finset O) (p : T) :
    matchesAt (frames A) (a := a) (b := b) (ρ.subst σ) row' W (ρ.term p) =
      matchesAt (frames A) (a := a) (b := b) σ row W p := by
  ext o
  rw [mem_matchesAt, mem_matchesAt, renamed]
  exact and_congr_right fun _ => ρ.E_apply σ σ p (row o)

/-- A renamed check holds at a renamed solution exactly when the check holds at the solution. A count
query keeps its number. -/
theorem checkHolds_rename {a b : PUnit.{1}} (σ : S) (row row' : O → T)
    (renamed : ∀ o, row' o = ρ.term (row o)) (W : Finset O) (c : Check T) :
    checkHolds (frames A) (a := a) (b := b) (ρ.subst σ) row' W (Check.map ρ.term c) ↔
      checkHolds (frames A) (a := a) (b := b) σ row W c := by
  cases c with
  | equal left right => exact ρ.E_apply σ σ left right
  | predicate quantifier pattern =>
      show quantifier.Holds W _ ↔ quantifier.Holds W _
      exact quantifier.holds_congr fun o _ => by
        rw [renamed]
        exact ρ.E_apply σ σ pattern (row o)
  | count pattern number =>
      show (matchesAt (frames A) (a := a) (b := b) (ρ.subst σ) row' W (ρ.term pattern)).card = number ↔
        (matchesAt (frames A) (a := a) (b := b) σ row W pattern).card = number
      rw [matchesAt_rename ρ σ row row' renamed W pattern]

/-- **A renamed firing has the same checks and collect query at the renamed solutions.** The checks are the
renamed checks, a count query keeping its number; the collect claims are the same sets of rows. -/
theorem holds_renameFiring {P : Program (Terms T)} {s : State (Terms T) O}
    (f : Firing O (ext A) P s.frame) {b : PUnit.{1}} (σ : S) :
    (renameFiring ρ.term ρ.subst f).Holds (frames A) (renameState ρ.term s) (b := b) (ρ.subst σ) ↔
      f.Holds (frames A) s (b := b) σ := by
  have checks : ((renameFiring ρ.term ρ.subst f).opened (frames A)).checks =
      (f.opened (frames A)).checks.map (Check.map ρ.term) :=
    congrArg RuleInstance.checks (opened_renameFiring ρ f)
  have collect : ((renameFiring ρ.term ρ.subst f).collectOpened (frames A)).zip
        (renameFiring ρ.term ρ.subst f).seen =
      ((f.collectOpened (frames A)).zip (renameFiring ρ.term ρ.subst f).seen).map
        (Prod.map ρ.term id) := by
    rw [collectOpened_renameFiring, List.zip_map_left]
  unfold Firing.Holds
  rw [checks, collect, List.forall_mem_map, List.forall_mem_map]
  apply and_congr
  · exact forall₂_congr fun c _ => checkHolds_rename ρ σ _ _ (row_renameFiring ρ f) s.present c
  · refine forall₂_congr fun q _ => ?_
    have same := matchesAt_rename ρ (a := s.frame) (b := b) σ (f.row (frames A) s) _
      (row_renameFiring ρ f) s.present q.1
    exact ⟨fun holds => same.symm.trans holds, fun holds => same.trans holds⟩

/-- A renamed store has the renamed solutions. -/
theorem models_renameStore {a b : PUnit.{1}} (σ : S) (store : EquationStore T) :
    (frames A).Models (a := a) (b := b) (ρ.subst σ) (renameStore ρ.term store) ↔
      (frames A).Models (a := a) (b := b) σ store := by
  unfold Frames.Models renameStore
  rw [List.forall_mem_map]
  exact forall₂_congr fun e _ => ρ.E_apply σ σ e.1 e.2

/-- **A renamed store is solvable exactly when the store is.** -/
theorem solvable_renameStore {a : PUnit.{1}} (store : EquationStore T) :
    (frames A).Solvable (a := a) (renameStore ρ.term store) ↔ (frames A).Solvable (a := a) store := by
  constructor
  · rintro ⟨b, σ, solved⟩
    refine ⟨b, ρ.subst.symm σ, (models_renameStore ρ _ store).mp ?_⟩
    rw [Equiv.apply_symm_apply]
    exact solved
  · rintro ⟨b, σ, solved⟩
    exact ⟨b, ρ.subst σ, (models_renameStore ρ σ store).mpr solved⟩

/-- **A renamed store entails a renamed observation exactly when the store entails the observation.** -/
theorem entails_renameStore {a : PUnit.{1}} (store : EquationStore T)
    (observation observation' : (b : PUnit.{1}) → S → Prop)
    (renamed : ∀ b σ, observation' b (ρ.subst σ) ↔ observation b σ) :
    (frames A).Entails (a := a) (renameStore ρ.term store) observation' ↔
      (frames A).Entails (a := a) store observation := by
  constructor
  · intro asked b σ solved
    exact (renamed b σ).mp (asked b (ρ.subst σ) ((models_renameStore ρ σ store).mpr solved))
  · intro asked b σ solved
    have pulled : (frames A).Models (a := a) (b := b) (ρ.subst (ρ.subst.symm σ))
        (renameStore ρ.term store) := by
      rw [Equiv.apply_symm_apply]
      exact solved
    have holds := (renamed b (ρ.subst.symm σ)).mpr
      (asked b (ρ.subst.symm σ) ((models_renameStore ρ _ store).mp pulled))
    rwa [Equiv.apply_symm_apply] at holds

/-- **A renamed firing is enabled at the renamed state exactly when the original is**: renaming names
does not touch occurrences. -/
theorem enabled_renameFiring [DecidableEq O] {P : Program (Terms T)} {s : State (Terms T) O}
    (f : Firing O (ext A) P s.frame) :
    Enabled (fun _ : O => ()) (renameState ρ.term s).present
        ((renameFiring ρ.term ρ.subst f).selection.commit (T := Unit)) ↔
      Enabled (fun _ : O => ()) s.present (f.selection.commit (T := Unit)) :=
  Iff.rfl

/-- **A renamed firing is admitted at the renamed state exactly when the original is.** -/
theorem admits_renameFiring [DecidableEq O] {P : Program (Terms T)} {s : State (Terms T) O}
    (f : Firing O (ext A) P s.frame) :
    (renameFiring ρ.term ρ.subst f).Admits (frames A) (renameState ρ.term s) ↔
      f.Admits (frames A) s := by
  have info := information_renameFiring ρ f
  refine and_congr (and_congr (fresh_renameFiring ρ f) ?_)
    (and_congr (enabled_renameFiring ρ f) (and_congr ?_ ?_))
  · simp only [renameFiring, renameRule, RuleInstance.map, List.length_map]
  · rw [info]
    exact solvable_renameStore ρ _
  · rw [info]
    exact entails_renameStore ρ _ _ _ fun b σ => holds_renameFiring ρ f σ

/-- Relabelling commutes with renaming. -/
theorem relabel_rename [DecidableEq O] (ρ' : T → T) {a : PUnit.{1}} (old : O → Terms T a) :
    ∀ (made : List O) (rows : List (Terms T a)) (o : O),
      relabel (Tm := Terms T) (a := a) (fun o => ρ' (old o)) made (rows.map ρ') o =
        ρ' (relabel old made rows o)
  | [], _, _ => rfl
  | _ :: _, [], _ => rfl
  | m :: rest, t :: ts, o => by
      simp only [List.map_cons, relabel]
      split_ifs
      · rfl
      · exact relabel_rename ρ' old rest ts o

/-- **A renamed firing has the renamed result.** -/
theorem result_renameFiring [DecidableEq O] {P : Program (Terms T)} {s : State (Terms T) O}
    (f : Firing O (ext A) P s.frame) :
    (renameFiring ρ.term ρ.subst f).result (frames A) (renameState ρ.term s) =
      renameState ρ.term (f.result (frames A) s) := by
  have row : (renameFiring ρ.term ρ.subst f).row (frames A) (renameState ρ.term s) =
      fun o => ρ.term (f.row (frames A) s o) := funext (row_renameFiring ρ f)
  have produce : ((renameFiring ρ.term ρ.subst f).opened (frames A)).produce =
      (f.opened (frames A)).produce.map ρ.term :=
    congrArg RuleInstance.produce (opened_renameFiring ρ f)
  unfold Firing.result
  rw [information_renameFiring ρ f, row, produce]
  exact congrArg (State.mk _ _ _) (funext fun o =>
    relabel_rename ρ.term (f.row (frames A) s) f.selection.made (f.opened (frames A)).produce o)

/-- **Every firing of the renamed program is a renamed firing.** -/
theorem exists_renameFiring {P : Program (Terms T)} {a : PUnit.{1}}
    (g : Firing O (ext A) (renameProgram ρ.term P) a) :
    ∃ f : Firing O (ext A) P a, renameFiring ρ.term ρ.subst f = g := by
  obtain ⟨rule, member, extension, opening, selection, seen⟩ := g
  obtain ⟨original, inside, rfl⟩ := member
  exact ⟨⟨original, inside, extension, ρ.subst.symm opening, selection, seen⟩, by
    simp only [renameFiring, Equiv.apply_symm_apply]⟩

theorem renameState_symm (s : State (Terms T) O) :
    renameState ρ.term.symm (renameState ρ.term s) = s := by
  have same : (fun t => ρ.term.symm (ρ.term t)) = fun t => t := funext ρ.term.symm_apply_apply
  rw [renameState_comp, same, renameState_id]

theorem renameState_injective : Function.Injective (renameState (O := O) ρ.term) := by
  intro s t same
  have back := congrArg (renameState ρ.term.symm) same
  rwa [renameState_symm, renameState_symm] at back

end Step

/-! ## Runs and outcomes correspond -/

section Runs

variable {T : Type uT} {S : Type uS} {A : SubstitutionAction T S} (ρ : Renaming A) {O : Type uO}
  [DecidableEq O] {P : Program (Terms T)}

/-- **A step of the system is a step of the renamed system between the renamed states.** -/
theorem succ_rename {s t : State (Terms T) O}
    (moved : Succ (step (frames A) O (ext A) P).toStep s t) :
    Succ (step (frames A) O (ext A) (renameProgram ρ.term P)).toStep (renameState ρ.term s)
      (renameState ρ.term t) := by
  obtain ⟨f, admitted, reached⟩ := moved
  refine ⟨renameFiring ρ.term ρ.subst f, (admits_renameFiring ρ f).mpr admitted, ?_⟩
  show (renameFiring ρ.term ρ.subst f).result (frames A) (renameState ρ.term s) = renameState ρ.term t
  rw [result_renameFiring]
  exact congrArg (renameState ρ.term) reached

/-- **Every step of the renamed system from a renamed state reaches a renamed state.** -/
theorem succ_of_rename {s u : State (Terms T) O}
    (moved : Succ (step (frames A) O (ext A) (renameProgram ρ.term P)).toStep (renameState ρ.term s) u) :
    ∃ t, Succ (step (frames A) O (ext A) P).toStep s t ∧ u = renameState ρ.term t := by
  obtain ⟨g, admitted, reached⟩ := moved
  obtain ⟨f, rfl⟩ := exists_renameFiring ρ g
  refine ⟨f.result (frames A) s, ⟨f, (admits_renameFiring ρ (s := s) f).mp admitted, rfl⟩, ?_⟩
  rw [← reached]
  exact result_renameFiring ρ (s := s) f

theorem succ_rename_iff {s t : State (Terms T) O} :
    Succ (step (frames A) O (ext A) (renameProgram ρ.term P)).toStep (renameState ρ.term s)
        (renameState ρ.term t) ↔
      Succ (step (frames A) O (ext A) P).toStep s t := by
  constructor
  · intro moved
    obtain ⟨t', moved', same⟩ := succ_of_rename ρ moved
    rwa [renameState_injective ρ same]
  · exact succ_rename ρ

/-- **A run of the system is a run of the renamed system between the renamed states.** -/
theorem reaches_rename {s t : State (Terms T) O}
    (run : Relation.ReflTransGen (Succ (step (frames A) O (ext A) P).toStep) s t) :
    Relation.ReflTransGen (Succ (step (frames A) O (ext A) (renameProgram ρ.term P)).toStep)
      (renameState ρ.term s) (renameState ρ.term t) := by
  induction run with
  | refl => exact .refl
  | tail _ moved reached => exact reached.tail (succ_rename ρ moved)

/-- **Every run of the renamed system from a renamed state reaches a renamed state.** -/
theorem reaches_of_rename {s u : State (Terms T) O}
    (run : Relation.ReflTransGen (Succ (step (frames A) O (ext A) (renameProgram ρ.term P)).toStep)
      (renameState ρ.term s) u) :
    ∃ t, Relation.ReflTransGen (Succ (step (frames A) O (ext A) P).toStep) s t ∧
      u = renameState ρ.term t := by
  induction run with
  | refl => exact ⟨s, .refl, rfl⟩
  | tail _ moved reached =>
      obtain ⟨t, run, rfl⟩ := reached
      obtain ⟨t', moved', rfl⟩ := succ_of_rename ρ moved
      exact ⟨t', run.tail moved', rfl⟩

/-- **The reachable states of the renamed system are the renamed reachable states.** -/
theorem reachable_rename (s : State (Terms T) O) :
    {u | Relation.ReflTransGen (Succ (step (frames A) O (ext A) (renameProgram ρ.term P)).toStep)
        (renameState ρ.term s) u} =
      renameState ρ.term '' {t | Relation.ReflTransGen (Succ (step (frames A) O (ext A) P).toStep) s t} := by
  ext u
  constructor
  · intro run
    obtain ⟨t, run', rfl⟩ := reaches_of_rename ρ run
    exact ⟨t, run', rfl⟩
  · rintro ⟨t, run, rfl⟩
    exact reaches_rename ρ run

/-- **A renamed state is terminal for the renamed program exactly when the state is terminal.** -/
theorem terminal_rename_iff {s : State (Terms T) O} :
    (∀ u, ¬ Succ (step (frames A) O (ext A) (renameProgram ρ.term P)).toStep (renameState ρ.term s) u) ↔
      ∀ t, ¬ Succ (step (frames A) O (ext A) P).toStep s t := by
  constructor
  · intro terminal t moved
    exact terminal _ (succ_rename ρ moved)
  · intro terminal u moved
    obtain ⟨t, moved', -⟩ := succ_of_rename ρ moved
    exact terminal t moved'

/-- **The terminal outcomes of the renamed system are the renamed terminal outcomes**: the states it
reaches and cannot leave. -/
theorem outcomes_rename (s : State (Terms T) O) :
    {u | Relation.ReflTransGen (Succ (step (frames A) O (ext A) (renameProgram ρ.term P)).toStep)
          (renameState ρ.term s) u ∧
        ∀ v, ¬ Succ (step (frames A) O (ext A) (renameProgram ρ.term P)).toStep u v} =
      renameState ρ.term '' {t | Relation.ReflTransGen (Succ (step (frames A) O (ext A) P).toStep) s t ∧
        ∀ v, ¬ Succ (step (frames A) O (ext A) P).toStep t v} := by
  ext u
  constructor
  · rintro ⟨run, terminal⟩
    obtain ⟨t, run', rfl⟩ := reaches_of_rename ρ run
    exact ⟨t, ⟨run', (terminal_rename_iff ρ).mp terminal⟩, rfl⟩
  · rintro ⟨t, ⟨run, terminal⟩, rfl⟩
    exact ⟨reaches_rename ρ run, (terminal_rename_iff ρ).mpr terminal⟩

/-- A renaming that fixes every rule of a program fixes the program. -/
theorem renameProgram_eq_of_fixed (fixed : ∀ r ∈ P, renameRule ρ.term r = r) :
    renameProgram ρ.term P = P := by
  ext r
  constructor
  · rintro ⟨r', inside, rfl⟩
    rw [fixed r' inside]
    exact inside
  · intro inside
    exact ⟨r, inside, fixed r inside⟩

/-- **Renaming a state under a program whose rules it fixes**: the reachable states of the renamed state
are the renamed reachable states, for the same program. -/
theorem reachable_rename_of_fixed (fixed : ∀ r ∈ P, renameRule ρ.term r = r)
    (s : State (Terms T) O) :
    {u | Relation.ReflTransGen (Succ (step (frames A) O (ext A) P).toStep) (renameState ρ.term s) u} =
      renameState ρ.term '' {t | Relation.ReflTransGen (Succ (step (frames A) O (ext A) P).toStep) s t} := by
  have renamed := reachable_rename ρ (P := P) s
  rwa [renameProgram_eq_of_fixed ρ fixed] at renamed

/-- **The terminal outcomes of a renamed state under a program whose rules the renaming fixes** are the
renamed terminal outcomes, for the same program. -/
theorem outcomes_rename_of_fixed (fixed : ∀ r ∈ P, renameRule ρ.term r = r)
    (s : State (Terms T) O) :
    {u | Relation.ReflTransGen (Succ (step (frames A) O (ext A) P).toStep) (renameState ρ.term s) u ∧
        ∀ v, ¬ Succ (step (frames A) O (ext A) P).toStep u v} =
      renameState ρ.term '' {t | Relation.ReflTransGen (Succ (step (frames A) O (ext A) P).toStep) s t ∧
        ∀ v, ¬ Succ (step (frames A) O (ext A) P).toStep t v} := by
  have renamed := outcomes_rename ρ (P := P) s
  rwa [renameProgram_eq_of_fixed ρ fixed] at renamed

/-- **The step is equivariant under a renaming.** Every firing is admitted exactly when its renamed copy
is admitted at the renamed state, with the renamed result; every firing of the renamed program is such a
copy; the reachable states and the terminal outcomes of the renamed system are the renamed ones. -/
theorem step_equivariant (s : State (Terms T) O) :
    (∀ f : Firing O (ext A) P s.frame,
        ((renameFiring ρ.term ρ.subst f).Admits (frames A) (renameState ρ.term s) ↔
          f.Admits (frames A) s) ∧
        (renameFiring ρ.term ρ.subst f).result (frames A) (renameState ρ.term s) =
          renameState ρ.term (f.result (frames A) s)) ∧
      (∀ g : Firing O (ext A) (renameProgram ρ.term P) s.frame,
        ∃ f : Firing O (ext A) P s.frame, renameFiring ρ.term ρ.subst f = g) ∧
      {u | Relation.ReflTransGen (Succ (step (frames A) O (ext A) (renameProgram ρ.term P)).toStep)
          (renameState ρ.term s) u} =
        renameState ρ.term '' {t | Relation.ReflTransGen (Succ (step (frames A) O (ext A) P).toStep) s t} ∧
      {u | Relation.ReflTransGen (Succ (step (frames A) O (ext A) (renameProgram ρ.term P)).toStep)
            (renameState ρ.term s) u ∧
          ∀ v, ¬ Succ (step (frames A) O (ext A) (renameProgram ρ.term P)).toStep u v} =
        renameState ρ.term '' {t | Relation.ReflTransGen (Succ (step (frames A) O (ext A) P).toStep) s t ∧
          ∀ v, ¬ Succ (step (frames A) O (ext A) P).toStep t v} :=
  ⟨fun f => ⟨admits_renameFiring ρ f, result_renameFiring ρ f⟩, fun g => exists_renameFiring ρ g,
    reachable_rename ρ s, outcomes_rename ρ s⟩

/-- **For an automorphism, the morphism of frames a firing moves along is renamed.** -/
theorem along_renameFiring (α : Automorphism A) {s : State (Terms T) O}
    (f : Firing O (ext A) P s.frame) (admitted : f.Admits (frames A) s) :
    (step (frames A) O (ext A) (renameProgram α.term P)).toStep.along (s := renameState α.term s)
        (renameFiring α.term α.subst f) ((admits_renameFiring α.toRenaming f).mpr admitted) =
      α.subst ((step (frames A) O (ext A) P).toStep.along f admitted) := by
  show A.compose A.identity A.identity = α.subst (A.compose A.identity A.identity)
  rw [α.compose_rename, α.identity_rename]

/-- **A run with its names renamed**: each firing renamed, at the renamed states. -/
def renameRun : {s : State (Terms T) O} → (step (frames A) O (ext A) P).toStep.Run s →
    (step (frames A) O (ext A) (renameProgram ρ.term P)).toStep.Run (renameState ρ.term s)
  | _, .nil s => .nil (renameState ρ.term s)
  | _, .cons f admitted rest =>
      .cons (renameFiring ρ.term ρ.subst f) ((admits_renameFiring ρ f).mpr admitted)
        ((congrArg (step (frames A) O (ext A) (renameProgram ρ.term P)).toStep.Run
          (result_renameFiring ρ f)).mpr (renameRun rest))

theorem last_mpr {Q : Program (Terms T)} {s t : State (Terms T) O} (same : s = t)
    (r : (step (frames A) O (ext A) Q).toStep.Run t) :
    ((congrArg (step (frames A) O (ext A) Q).toStep.Run same).mpr r).last = r.last := by
  subst same
  rfl

theorem word_mpr {Q : Program (Terms T)} {s t : State (Terms T) O} (same : s = t)
    (r : (step (frames A) O (ext A) Q).toStep.Run t) :
    ((congrArg (step (frames A) O (ext A) Q).toStep.Run same).mpr r).word = r.word := by
  subst same
  rfl

/-- **A renamed run ends at the renamed state.** -/
theorem last_renameRun :
    ∀ {s : State (Terms T) O} (r : (step (frames A) O (ext A) P).toStep.Run s),
      (renameRun ρ r).last = renameState ρ.term r.last
  | _, .nil _ => rfl
  | _, .cons f _ rest => (last_mpr (result_renameFiring ρ f) (renameRun ρ rest)).trans
      (last_renameRun rest)

/-- **A renamed run fires the renamed firings, at the renamed states, in the same order.** -/
theorem word_renameRun :
    ∀ {s : State (Terms T) O} (r : (step (frames A) O (ext A) P).toStep.Run s),
      (renameRun ρ r).word = r.word.map fun x =>
        (⟨renameState ρ.term x.1, renameFiring ρ.term ρ.subst x.2⟩ :
          (t : State (Terms T) O) × Firing O (ext A) (renameProgram ρ.term P) t.frame)
  | _, .nil _ => rfl
  | _, .cons f _ rest => congrArg (List.cons _)
      ((word_mpr (result_renameFiring ρ f) (renameRun ρ rest)).trans (word_renameRun rest))

theorem toLast_mpr {Q : Program (Terms T)} {s t : State (Terms T) O} (same : s = t)
    (r : (step (frames A) O (ext A) Q).toStep.Run t) :
    ((congrArg (step (frames A) O (ext A) Q).toStep.Run same).mpr r).toLast = r.toLast := by
  subst same
  rfl

/-- **For an automorphism, a renamed run moves along the renamed morphism of frames.** -/
theorem toLast_renameRun (α : Automorphism A) :
    ∀ {s : State (Terms T) O} (r : (step (frames A) O (ext A) P).toStep.Run s),
      (renameRun α.toRenaming r).toLast = α.subst r.toLast
  | _, .nil _ => α.identity_rename.symm
  | _, .cons f _ rest =>
      (congrArg (fun y : S => A.compose y (A.compose A.identity A.identity))
        ((toLast_mpr (result_renameFiring α.toRenaming f) (renameRun α.toRenaming rest)).trans
          (toLast_renameRun α rest))).trans
        (α.compose_identity_rename rest.toLast).symm

end Runs

/-! ## Finitely many names: a bijection extends to a permutation -/

section Extension

variable {α : Type*} [DecidableEq α] {β : Type*}

/-- Exchanging two elements of the same weight keeps every weight. -/
theorem swap_weight (w : α → β) {p q : α} (same : w p = w q) (a : α) :
    w (Equiv.swap p q a) = w a := by
  rw [Equiv.swap_apply_def]
  split_ifs with first second
  · rw [first, same]
  · rw [second, same]
  · rfl

/-- **A bijection between finitely many names extends to a permutation of all names**: two lists of
distinct elements with the same weights, position by position, are related by a permutation that keeps
every weight. -/
theorem exists_perm_map_eq (w : α → β) :
    ∀ (xs ys : List α), xs.Nodup → ys.Nodup → xs.map w = ys.map w →
      ∃ π : Equiv.Perm α, xs.map π = ys ∧ ∀ a, w (π a) = w a
  | [], [], _, _, _ => ⟨1, rfl, fun _ => rfl⟩
  | [], _ :: _, _, _, same => by simp at same
  | _ :: _, [], _, _, same => by simp at same
  | x :: xs, y :: ys, distinctX, distinctY, same => by
      obtain ⟨headWeight, restWeight⟩ := List.cons.inj same
      obtain ⟨π, mapped, weights⟩ := exists_perm_map_eq w xs ys (List.nodup_cons.mp distinctX).2
        (List.nodup_cons.mp distinctY).2 restWeight
      refine ⟨π.trans (Equiv.swap (π x) y), ?_, fun a => ?_⟩
      · have kept : ∀ x' ∈ xs, Equiv.swap (π x) y (π x') = π x' := by
          intro x' inside
          apply Equiv.swap_apply_of_ne_of_ne
          · intro equal
            exact (List.nodup_cons.mp distinctX).1 (π.injective equal ▸ inside)
          · intro equal
            apply (List.nodup_cons.mp distinctY).1
            rw [← equal, ← mapped]
            exact List.mem_map_of_mem inside
        rw [List.map_cons, Equiv.trans_apply, Equiv.swap_apply_left, ← mapped]
        exact congrArg (List.cons y) (List.map_congr_left kept)
      · rw [Equiv.trans_apply, swap_weight w ((weights x).trans headWeight) (π a), weights a]

omit [DecidableEq α] in
theorem map_unit_eq : ∀ (xs ys : List α), xs.length = ys.length →
    xs.map (fun _ => ()) = ys.map (fun _ => ())
  | [], [], _ => rfl
  | [], _ :: _, same => by simp at same
  | _ :: _, [], same => by simp at same
  | _ :: xs, _ :: ys, same => congrArg (List.cons ()) (map_unit_eq xs ys (Nat.succ.inj same))

end Extension

/-! ## First-order terms: permutations of names -/

section FirstOrderNames

open Mettapedia.Logic.LP

variable {signature : LPSignature}

/-- **A permutation of the names of first-order terms**: a permutation of the constants and an
arity-preserving permutation of the function symbols. Variables are unknowns, not names. -/
structure NamePermutation (signature : LPSignature) where
  /-- The permutation of the constants. -/
  constants : Equiv.Perm signature.constants
  /-- The permutation of the function symbols. -/
  functions : Equiv.Perm signature.functionSymbols
  /-- Function symbols keep their arity. -/
  arity : ∀ f, signature.functionArity (functions f) = signature.functionArity f

namespace NamePermutation

variable (π : NamePermutation signature)

/-- **A term with its names renamed**: constants and function symbols renamed, variables kept. -/
def rename : Term signature → Term signature
  | .var v => .var v
  | .const k => .const (π.constants k)
  | .app f ts => .app (π.functions f) fun i => rename (ts (Fin.cast (π.arity f) i))

/-- **A substitution with its names renamed**: `σ ↦ rename ∘ σ`. -/
def renameSubst (σ : Subst signature) : Subst signature := fun v => π.rename (σ v)

/-- The inverse permutation of names. -/
def symm : NamePermutation signature where
  constants := π.constants.symm
  functions := π.functions.symm
  arity f := by
    have same := π.arity (π.functions.symm f)
    rw [Equiv.apply_symm_apply] at same
    exact same.symm

theorem app_cast {f g : signature.functionSymbols} (same : f = g)
    (ts : Fin (signature.functionArity g) → Term signature) :
    Term.app f (fun i => ts (Fin.cast (congrArg signature.functionArity same) i)) = Term.app g ts := by
  subst same
  rfl

/-- Two permutations of names inverse on constants and function symbols are inverse on terms. -/
theorem rename_rename_of_inverse (first second : NamePermutation signature)
    (constants : ∀ k, second.constants (first.constants k) = k)
    (functions : ∀ f, second.functions (first.functions f) = f) (t : Term signature) :
    second.rename (first.rename t) = t := by
  induction t with
  | var _ => rfl
  | const k => exact congrArg Term.const (constants k)
  | app f ts ih =>
      calc second.rename (first.rename (.app f ts))
          = .app (second.functions (first.functions f))
              (fun i => ts (Fin.cast (congrArg signature.functionArity (functions f)) i)) :=
            congrArg (Term.app (second.functions (first.functions f))) (funext fun _ => ih _)
        _ = .app f ts := app_cast (functions f) ts

/-- The renaming of terms, as a bijection. -/
def termEquiv : Term signature ≃ Term signature where
  toFun := π.rename
  invFun := π.symm.rename
  left_inv := rename_rename_of_inverse π π.symm (fun k => π.constants.symm_apply_apply k)
    (fun f => π.functions.symm_apply_apply f)
  right_inv := rename_rename_of_inverse π.symm π (fun k => π.constants.apply_symm_apply k)
    (fun f => π.functions.apply_symm_apply f)

/-- The renaming of substitutions, as a bijection. -/
def substEquiv : Subst signature ≃ Subst signature where
  toFun := π.renameSubst
  invFun := π.symm.renameSubst
  left_inv σ := funext fun v => π.termEquiv.left_inv (σ v)
  right_inv σ := funext fun v => π.termEquiv.right_inv (σ v)

/-- **Substituting commutes with renaming names.** -/
theorem rename_applyTerm (σ : Subst signature) (t : Term signature) :
    (π.renameSubst σ).applyTerm (π.rename t) = π.rename (σ.applyTerm t) := by
  induction t with
  | var _ => rfl
  | const _ => rfl
  | app f _ ih => exact congrArg (Term.app (π.functions f)) (funext fun _ => ih _)

/-- **A permutation of names is an automorphism of the first-order substitution action**, the action of
the existing unifier `unifyTotal`. -/
def automorphism : Automorphism (FirstOrder.action signature) where
  term := π.termEquiv
  subst := π.substEquiv
  apply_rename σ t := π.rename_applyTerm σ t
  E_rename _ _ := π.termEquiv.apply_eq_iff_eq
  identity_rename := rfl
  compose_rename σ τ := funext fun v => (π.rename_applyTerm σ (τ v)).symm

/-- **Finitely many names extend to a permutation of names**: lists of distinct constants of the same
length, and lists of distinct function symbols with the same arities position by position, are related
by a permutation of names. -/
theorem exists_of_lists [DecidableEq signature.constants] [DecidableEq signature.functionSymbols]
    (ks ks' : List signature.constants) (fs fs' : List signature.functionSymbols)
    (distinctK : ks.Nodup) (distinctK' : ks'.Nodup) (lengths : ks.length = ks'.length)
    (distinctF : fs.Nodup) (distinctF' : fs'.Nodup)
    (arities : fs.map signature.functionArity = fs'.map signature.functionArity) :
    ∃ ν : NamePermutation signature, ks.map ν.constants = ks' ∧ fs.map ν.functions = fs' := by
  obtain ⟨κ, constantsMapped, -⟩ :=
    exists_perm_map_eq (fun _ => ()) ks ks' distinctK distinctK' (map_unit_eq ks ks' lengths)
  obtain ⟨φ, functionsMapped, arity⟩ :=
    exists_perm_map_eq signature.functionArity fs fs' distinctF distinctF' arities
  exact ⟨⟨κ, φ, arity⟩, constantsMapped, functionsMapped⟩

end NamePermutation

variable {O : Type uO} [DecidableEq O] (π : NamePermutation signature)
  {P : Program (Terms (Term signature))}

/-- **The first-order step is equivariant under every permutation of names**: `step_equivariant` at the
automorphism `NamePermutation.automorphism` of the action of `unifyTotal`. -/
theorem names_equivariant (s : State (Terms (Term signature)) O) :
    (∀ f : Firing O (ext (FirstOrder.action signature)) P s.frame,
        ((renameFiring π.rename π.renameSubst f).Admits (frames (FirstOrder.action signature))
            (renameState π.rename s) ↔
          f.Admits (frames (FirstOrder.action signature)) s) ∧
        (renameFiring π.rename π.renameSubst f).result (frames (FirstOrder.action signature))
            (renameState π.rename s) =
          renameState π.rename (f.result (frames (FirstOrder.action signature)) s)) ∧
      (∀ g : Firing O (ext (FirstOrder.action signature)) (renameProgram π.rename P) s.frame,
        ∃ f : Firing O (ext (FirstOrder.action signature)) P s.frame,
          renameFiring π.rename π.renameSubst f = g) ∧
      {u | Relation.ReflTransGen
          (Succ (step (frames (FirstOrder.action signature)) O (ext (FirstOrder.action signature))
            (renameProgram π.rename P)).toStep) (renameState π.rename s) u} =
        renameState π.rename '' {t | Relation.ReflTransGen
          (Succ (step (frames (FirstOrder.action signature)) O (ext (FirstOrder.action signature))
            P).toStep) s t} ∧
      {u | Relation.ReflTransGen
            (Succ (step (frames (FirstOrder.action signature)) O (ext (FirstOrder.action signature))
              (renameProgram π.rename P)).toStep) (renameState π.rename s) u ∧
          ∀ v, ¬ Succ (step (frames (FirstOrder.action signature)) O
            (ext (FirstOrder.action signature)) (renameProgram π.rename P)).toStep u v} =
        renameState π.rename '' {t | Relation.ReflTransGen
            (Succ (step (frames (FirstOrder.action signature)) O (ext (FirstOrder.action signature))
              P).toStep) s t ∧
          ∀ v, ¬ Succ (step (frames (FirstOrder.action signature)) O
            (ext (FirstOrder.action signature)) P).toStep t v} :=
  step_equivariant π.automorphism.toRenaming s

/-- **Renaming names keeps admission**, for first-order terms. -/
theorem admits_renameNames {s : State (Terms (Term signature)) O}
    (f : Firing O (ext (FirstOrder.action signature)) P s.frame) :
    (renameFiring π.rename π.renameSubst f).Admits (frames (FirstOrder.action signature))
        (renameState π.rename s) ↔
      f.Admits (frames (FirstOrder.action signature)) s :=
  admits_renameFiring π.automorphism.toRenaming f

/-- **Renaming names renames results**, for first-order terms. -/
theorem result_renameNames {s : State (Terms (Term signature)) O}
    (f : Firing O (ext (FirstOrder.action signature)) P s.frame) :
    (renameFiring π.rename π.renameSubst f).result (frames (FirstOrder.action signature))
        (renameState π.rename s) =
      renameState π.rename (f.result (frames (FirstOrder.action signature)) s) :=
  result_renameFiring π.automorphism.toRenaming f

/-- **Renaming names renames the reachable states**, for first-order terms. -/
theorem reachable_renameNames (s : State (Terms (Term signature)) O) :
    {u | Relation.ReflTransGen
        (Succ (step (frames (FirstOrder.action signature)) O (ext (FirstOrder.action signature))
          (renameProgram π.rename P)).toStep) (renameState π.rename s) u} =
      renameState π.rename '' {t | Relation.ReflTransGen
        (Succ (step (frames (FirstOrder.action signature)) O (ext (FirstOrder.action signature))
          P).toStep) s t} :=
  reachable_rename π.automorphism.toRenaming s

/-- **Renaming names renames the terminal outcomes**, for first-order terms. -/
theorem outcomes_renameNames (s : State (Terms (Term signature)) O) :
    {u | Relation.ReflTransGen
          (Succ (step (frames (FirstOrder.action signature)) O (ext (FirstOrder.action signature))
            (renameProgram π.rename P)).toStep) (renameState π.rename s) u ∧
        ∀ v, ¬ Succ (step (frames (FirstOrder.action signature)) O
          (ext (FirstOrder.action signature)) (renameProgram π.rename P)).toStep u v} =
      renameState π.rename '' {t | Relation.ReflTransGen
          (Succ (step (frames (FirstOrder.action signature)) O (ext (FirstOrder.action signature))
            P).toStep) s t ∧
        ∀ v, ¬ Succ (step (frames (FirstOrder.action signature)) O
          (ext (FirstOrder.action signature)) P).toStep t v} :=
  outcomes_rename π.automorphism.toRenaming s

end FirstOrderNames

/-! ## First-order terms: permutations of unknowns -/

section FirstOrderUnknowns

open Mettapedia.Logic.LP

variable {signature : LPSignature}

/-- **A term with its unknowns permuted**: variables renamed, names kept. -/
def permuteUnknowns (τ : Equiv.Perm signature.vars) : Term signature → Term signature
  | .var v => .var (τ v)
  | .const k => .const k
  | .app f ts => .app f fun i => permuteUnknowns τ (ts i)

/-- **A substitution with its unknowns permuted**: `σ ↦ permute ∘ σ ∘ τ⁻¹`. -/
def permuteUnknownsSubst (τ : Equiv.Perm signature.vars) (σ : Subst signature) : Subst signature :=
  fun v => permuteUnknowns τ (σ (τ.symm v))

theorem permuteUnknowns_of_inverse (τ τ' : Equiv.Perm signature.vars) (inverse : ∀ v, τ' (τ v) = v)
    (t : Term signature) : permuteUnknowns τ' (permuteUnknowns τ t) = t := by
  induction t with
  | var v => exact congrArg Term.var (inverse v)
  | const _ => rfl
  | app f _ ih => exact congrArg (Term.app f) (funext fun i => ih i)

/-- The permutation of the unknowns of terms, as a bijection. -/
def permuteUnknownsEquiv (τ : Equiv.Perm signature.vars) : Term signature ≃ Term signature where
  toFun := permuteUnknowns τ
  invFun := permuteUnknowns τ.symm
  left_inv := permuteUnknowns_of_inverse τ τ.symm τ.symm_apply_apply
  right_inv := permuteUnknowns_of_inverse τ.symm τ τ.apply_symm_apply

/-- **Substituting commutes with permuting unknowns.** -/
theorem permuteUnknowns_applyTerm (τ : Equiv.Perm signature.vars) (σ : Subst signature)
    (t : Term signature) :
    (permuteUnknownsSubst τ σ).applyTerm (permuteUnknowns τ t) =
      permuteUnknowns τ (σ.applyTerm t) := by
  induction t with
  | var v =>
      show permuteUnknowns τ (σ (τ.symm (τ v))) = permuteUnknowns τ (σ v)
      rw [Equiv.symm_apply_apply]
  | const _ => rfl
  | app f _ ih => exact congrArg (Term.app f) (funext fun i => ih i)

/-- The permutation of the unknowns of substitutions, as a bijection. -/
def permuteUnknownsSubstEquiv (τ : Equiv.Perm signature.vars) : Subst signature ≃ Subst signature where
  toFun := permuteUnknownsSubst τ
  invFun := permuteUnknownsSubst τ.symm
  left_inv σ := funext fun v => by
    show permuteUnknowns τ.symm (permuteUnknowns τ (σ (τ.symm (τ.symm.symm v)))) = σ v
    rw [Equiv.symm_symm, Equiv.symm_apply_apply,
      permuteUnknowns_of_inverse τ τ.symm τ.symm_apply_apply]
  right_inv σ := funext fun v => by
    show permuteUnknowns τ (permuteUnknowns τ.symm (σ (τ.symm.symm (τ.symm v)))) = σ v
    rw [Equiv.symm_symm, Equiv.apply_symm_apply,
      permuteUnknowns_of_inverse τ.symm τ τ.apply_symm_apply]

/-- **A permutation of unknowns is an automorphism of the first-order substitution action.** With
`Renaming.trans`, names and unknowns may be renamed together, each kind among itself. -/
def unknownsAutomorphism (τ : Equiv.Perm signature.vars) :
    Automorphism (FirstOrder.action signature) where
  term := permuteUnknownsEquiv τ
  subst := permuteUnknownsSubstEquiv τ
  apply_rename σ t := permuteUnknowns_applyTerm τ σ t
  E_rename _ _ := (permuteUnknownsEquiv τ).apply_eq_iff_eq
  identity_rename := funext fun v => congrArg Term.var (τ.apply_symm_apply v)
  compose_rename σ σ' := funext fun v => (permuteUnknowns_applyTerm τ σ (σ' (τ.symm v))).symm

end FirstOrderUnknowns

/-! ## Controls -/

section PositiveControl

open _root_.Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Controls
  (atoms action)
open Mettapedia.Logic.LP
open Examples (c consume tokenState fresh_of_ground)

/-- Exchange the names `1` and `3`. -/
def swapOneThree : NamePermutation atoms where
  constants := Equiv.swap 1 3
  functions := Equiv.refl _
  arity _ := rfl

/-- The program whose one rule is `consume`: take a token `1`, make a `2`. -/
def consumeOnly : Program (Terms (Term atoms)) := {consume}

/-- Take the token at identity `0`, make identity `1`. -/
def consumeOnlyFiring : Firing ℕ (ext action) consumeOnly PUnit.unit :=
  ⟨consume, Set.mem_singleton consume, PUnit.unit, Subst.id atoms, ⟨[0], [], [1]⟩, []⟩

theorem consumeOnly_information :
    consumeOnlyFiring.information (frames action) tokenState = [(c 1, c 1)] :=
  rfl

theorem consumeOnly_admitted :
    (step (frames action) ℕ (ext action) consumeOnly).Admits (s := tokenState) consumeOnlyFiring := by
  refine (admits_iff consumeOnlyFiring).mpr ⟨?_, ⟨List.nodup_singleton 0, List.nodup_singleton 1, rfl,
    rfl, rfl, rfl⟩, ?_, ?_, ?_, ?_⟩
  · apply fresh_of_ground action tokenState consumeOnlyFiring
    intro t member σ
    simp [consumeOnlyFiring, consume, Rule.terms] at member
    rcases member with rfl | rfl <;> rfl
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp [consumeOnlyFiring, tokenState, Selection.commit]
  · rw [consumeOnly_information]
    exact ⟨PUnit.unit, Subst.id atoms, fun e member => by
      obtain rfl := List.mem_singleton.mp member
      rfl⟩
  · intro check member
    simp [consumeOnlyFiring, consume, Firing.opened, RuleInstance.map] at member
  · intro q member
    simp [consumeOnlyFiring, consume, Firing.collectOpened] at member

/-- **The run ends**: after the token is taken, no firing of `consume` is admitted, since the only row
is `2` and the pattern `1` is a different name. -/
theorem consumeOnly_terminal (v : State (Terms (Term atoms)) ℕ) :
    ¬ Succ (step (frames action) ℕ (ext action) consumeOnly).toStep
      (consumeOnlyFiring.result (frames action) tokenState) v := by
  rintro ⟨⟨rule, member, extension, opening, ⟨taken, read, made⟩, seen⟩, admitted, -⟩
  have same : rule = consume := member
  subst same
  obtain ⟨⟨-, -, -, takeLength, -, -, -⟩, enabled, ⟨_, σ, solved⟩, -⟩ := admitted
  have one : taken.length = 1 := takeLength.symm
  obtain ⟨o, rfl⟩ := List.length_eq_one_iff.mp one
  have inside : o ∈ (consumeOnlyFiring.result (frames action) tokenState).present :=
    enabled.taken_subset (by simp [Selection.commit])
  have isOne : o = 1 := by
    simpa [Firing.result, consumeOnlyFiring, tokenState, fire, Selection.commit] using inside
  subst isOne
  have key := solved _ (List.mem_append_left _ (List.mem_append_left _
    (List.mem_append_right _ (List.mem_singleton_self _))))
  change (Term.const (1 : ℕ) : Term atoms) = Term.const (2 : ℕ) at key
  exact absurd (Term.const.inj key) (by decide)

/-- **A run reaches a terminal outcome.** -/
theorem consumeOnly_outcome :
    consumeOnlyFiring.result (frames action) tokenState ∈
      {t | Relation.ReflTransGen (Succ (step (frames action) ℕ (ext action) consumeOnly).toStep)
          tokenState t ∧
        ∀ v, ¬ Succ (step (frames action) ℕ (ext action) consumeOnly).toStep t v} :=
  ⟨Relation.ReflTransGen.single ⟨consumeOnlyFiring, consumeOnly_admitted, rfl⟩, consumeOnly_terminal⟩

/-- The renamed state is a token `3`, and the renamed rule takes a `3`. -/
theorem renamed_state_and_rule :
    (renameState swapOneThree.rename tokenState).label 0 = c 3 ∧
      (renameRule swapOneThree.rename consume).body.take = [c 3] :=
  ⟨rfl, rfl⟩

/-- **The renamed firing is admitted at the renamed state.** -/
theorem renamed_admitted :
    (renameFiring swapOneThree.rename swapOneThree.renameSubst consumeOnlyFiring).Admits (frames action)
      (renameState swapOneThree.rename tokenState) :=
  (admits_renameNames swapOneThree (s := tokenState) consumeOnlyFiring).mpr consumeOnly_admitted

/-- **The original firing is refused at the renamed state**: the renamed token `3` is not the pattern
`1`. -/
theorem original_refused_at_renamed :
    ¬ consumeOnlyFiring.Admits (frames action) (renameState swapOneThree.rename tokenState) := by
  rintro ⟨-, -, ⟨_, σ, solved⟩, -⟩
  have key := solved _ (List.mem_append_left _ (List.mem_append_left _
    (List.mem_append_right _ (List.mem_singleton_self _))))
  change (Term.const (1 : ℕ) : Term atoms) = Term.const (3 : ℕ) at key
  exact absurd (Term.const.inj key) (by decide)

/-- **The renamed run reaches the renamed terminal outcome**, whose made row is still `2`. -/
theorem renamed_outcome :
    renameState swapOneThree.rename (consumeOnlyFiring.result (frames action) tokenState) ∈
        {u | Relation.ReflTransGen
            (Succ (step (frames action) ℕ (ext action)
              (renameProgram swapOneThree.rename consumeOnly)).toStep)
            (renameState swapOneThree.rename tokenState) u ∧
          ∀ v, ¬ Succ (step (frames action) ℕ (ext action)
            (renameProgram swapOneThree.rename consumeOnly)).toStep u v} ∧
      (renameState swapOneThree.rename (consumeOnlyFiring.result (frames action) tokenState)).label 1 =
        c 2 := by
  refine ⟨?_, rfl⟩
  exact (Set.ext_iff.mp (outcomes_renameNames (P := consumeOnly) swapOneThree tokenState) _).mpr
    (Set.mem_image_of_mem _ consumeOnly_outcome)

end PositiveControl

section NegativeControl

open _root_.Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Controls (atoms)
open Mettapedia.Logic.LP
open Examples (c fresh_of_ground)

/-- Read the name `1` as `0`; every other term stays. -/
def collapse : Term atoms → Term atoms
  | .var v => .var v
  | .const k => .const (if k = 1 then 0 else k)
  | .app f _ => Empty.elim f

theorem collapse_applyTerm (σ : Subst atoms) :
    ∀ t : Term atoms, collapse (σ.applyTerm t) = Subst.applyTerm (fun v => collapse (σ v)) (collapse t)
  | .var _ => rfl
  | .const _ => rfl
  | .app f _ => Empty.elim f

/-- **A substitution action that interprets names beyond equality**: its declared equality identifies
the constants `0` and `1`. -/
def collapsing : SubstitutionAction (Term atoms) (Subst atoms) where
  E s t := collapse s = collapse t
  equivalence := ⟨fun _ => rfl, Eq.symm, Eq.trans⟩
  apply := Subst.applyTerm
  identity := Subst.id atoms
  compose := Subst.comp
  apply_identity := Subst.applyTerm_id
  apply_compose := Subst.applyTerm_comp
  preserves := fun σ {s t} same => by
    have same' : collapse s = collapse t := same
    show collapse (σ.applyTerm s) = collapse (σ.applyTerm t)
    rw [collapse_applyTerm, collapse_applyTerm, same']

/-- Exchange the names `1` and `2`. -/
def swapOneTwo : NamePermutation atoms where
  constants := Equiv.swap 1 2
  functions := Equiv.refl _
  arity _ := rfl

/-- **Exactly one law fails**: over `collapsing`, exchanging `1` and `2` commutes with substitution,
fixes the identity and preserves composition, but the declared equality is not respected. -/
theorem swapOneTwo_laws :
    (∀ σ t, collapsing.apply (swapOneTwo.substEquiv σ) (swapOneTwo.termEquiv t) =
        swapOneTwo.termEquiv (collapsing.apply σ t)) ∧
      swapOneTwo.substEquiv collapsing.identity = collapsing.identity ∧
      (∀ σ τ, swapOneTwo.substEquiv (collapsing.compose σ τ) =
        collapsing.compose (swapOneTwo.substEquiv σ) (swapOneTwo.substEquiv τ)) ∧
      ¬ ∀ s t, collapsing.E (swapOneTwo.termEquiv s) (swapOneTwo.termEquiv t) ↔ collapsing.E s t := by
  refine ⟨swapOneTwo.automorphism.apply_rename, swapOneTwo.automorphism.identity_rename,
    swapOneTwo.automorphism.compose_rename, fun respects => ?_⟩
  have zeroOne : collapsing.E (c 0) (c 1) := rfl
  have zeroTwo := (respects (c 0) (c 1)).mpr zeroOne
  change (Term.const (0 : ℕ) : Term atoms) = Term.const (2 : ℕ) at zeroTwo
  exact absurd (Term.const.inj zeroTwo) (by decide)

/-- **No renaming of `collapsing` exchanges the names `1` and `2`.** -/
theorem swapOneTwo_not_renaming : ¬ ∃ ρ : Renaming collapsing, ⇑ρ.term = swapOneTwo.rename := by
  rintro ⟨ρ, same⟩
  have respects := ρ.E_rename (c 0) (c 1)
  rw [same] at respects
  have zeroOne : collapsing.E (c 0) (c 1) := rfl
  have zeroTwo := respects.mpr zeroOne
  change (Term.const (0 : ℕ) : Term atoms) = Term.const (2 : ℕ) at zeroTwo
  exact absurd (Term.const.inj zeroTwo) (by decide)

/-- Take a row for the pattern `1`. -/
def takeOne : Rule (Terms (Term atoms)) := ⟨PUnit.unit, ⟨[c 1], [], [], [], []⟩, []⟩

/-- One row `0`, at identity `0`. -/
def zeroRow : State (Terms (Term atoms)) ℕ := ⟨PUnit.unit, [], {0}, fun _ => c 0⟩

/-- Take the row `0` for the pattern `1`. -/
def takeFiring : Firing ℕ (ext collapsing) {takeOne} PUnit.unit :=
  ⟨takeOne, Set.mem_singleton takeOne, PUnit.unit, Subst.id atoms, ⟨[0], [], []⟩, []⟩

theorem takeFiring_information :
    takeFiring.information (frames collapsing) zeroRow = [(c 1, c 0)] :=
  rfl

theorem renamed_takeFiring_information :
    (renameFiring swapOneTwo.rename swapOneTwo.renameSubst takeFiring).information (frames collapsing)
      (renameState swapOneTwo.rename zeroRow) = [(c 2, c 0)] :=
  rfl

/-- **The firing is admitted**: `collapsing` equates the pattern `1` with the row `0`. -/
theorem takeFiring_admitted :
    (step (frames collapsing) ℕ (ext collapsing) {takeOne}).Admits (s := zeroRow) takeFiring := by
  refine (admits_iff takeFiring).mpr ⟨?_, ⟨List.nodup_singleton 0, List.nodup_nil, rfl, rfl, rfl,
    rfl⟩, ?_, ?_, ?_, ?_⟩
  · apply fresh_of_ground collapsing zeroRow takeFiring
    intro t member σ
    simp [takeFiring, takeOne, Rule.terms] at member
    subst member
    rfl
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp [takeFiring, zeroRow, Selection.commit]
  · rw [takeFiring_information]
    exact ⟨PUnit.unit, Subst.id atoms, fun e member => by
      obtain rfl := List.mem_singleton.mp member
      rfl⟩
  · intro check member
    simp [takeFiring, takeOne, Firing.opened, RuleInstance.map] at member
  · intro q member
    simp [takeFiring, takeOne, Firing.collectOpened] at member

/-- **Its renamed copy is refused**: `collapsing` does not equate the pattern `2` with the row `0`. -/
theorem renamed_takeFiring_refused :
    ¬ (renameFiring swapOneTwo.rename swapOneTwo.renameSubst takeFiring).Admits (frames collapsing)
      (renameState swapOneTwo.rename zeroRow) := by
  rintro ⟨-, -, ⟨_, σ, solved⟩, -⟩
  rw [renamed_takeFiring_information] at solved
  have key : collapse (Subst.applyTerm σ (c 2)) = collapse (Subst.applyTerm σ (c 0)) :=
    solved _ List.mem_cons_self
  change (Term.const (2 : ℕ) : Term atoms) = Term.const (0 : ℕ) at key
  exact absurd (Term.const.inj key) (by decide)

end NegativeControl

section UnknownControl

open _root_.Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Controls
  (atoms action)
open Mettapedia.Logic.LP
open Examples (c x everywhere)

/-- Exchange the unknown `x` with the name `5`; every other term stays. -/
def unknownToName (t : Term atoms) : Term atoms :=
  match t with
  | .var v => if v = 0 then .const 5 else .var v
  | .const k => if k = 5 then .var 0 else .const k
  | .app f _ => Empty.elim f

theorem unknownToName_involutive (t : Term atoms) : unknownToName (unknownToName t) = t := by
  match t with
  | .var v =>
      by_cases zero : v = 0
      · subst zero
        rfl
      · simp [unknownToName, zero]
  | .const k =>
      by_cases five : k = 5
      · subst five
        rfl
      · simp [unknownToName, five]
  | .app f _ => exact Empty.elim f

/-- The exchange, as a bijection of the terms. -/
def unknownToNameEquiv : Term atoms ≃ Term atoms :=
  ⟨unknownToName, unknownToName, unknownToName_involutive, unknownToName_involutive⟩

/-- **No renaming of the first-order action exchanges an unknown with a name**: substituting does not
commute with the exchange. -/
theorem unknownToName_not_renaming : ¬ ∃ ρ : Renaming action, ⇑ρ.term = unknownToName := by
  rintro ⟨ρ, same⟩
  have law := ρ.apply_rename (everywhere 7) x
  rw [same] at law
  change (Term.const (5 : ℕ) : Term atoms) = Term.const (7 : ℕ) at law
  exact absurd (Term.const.inj law) (by decide)

/-- **Exactly one law fails**: the exchange is a bijection of the terms that keeps their equality, and
it is not a renaming of the action. -/
theorem unknownToName_laws :
    (∀ s t, action.E (unknownToNameEquiv s) (unknownToNameEquiv t) ↔ action.E s t) ∧
      ¬ ∃ ρ : Renaming action, ⇑ρ.term = unknownToName :=
  ⟨fun _ _ => unknownToNameEquiv.apply_eq_iff_eq, unknownToName_not_renaming⟩

/-- Read any row. -/
def readAny : Rule (Terms (Term atoms)) := ⟨PUnit.unit, ⟨[], [x], [], [], []⟩, []⟩

/-- One row `7`, at identity `0`. -/
def sevenRow : State (Terms (Term atoms)) ℕ := ⟨PUnit.unit, [], {0}, fun _ => c 7⟩

/-- Read the row `7` for the pattern `x`. -/
def readFiring : Firing ℕ (ext action) {readAny} PUnit.unit :=
  ⟨readAny, Set.mem_singleton readAny, PUnit.unit, Subst.id atoms, ⟨[], [0], []⟩, []⟩

theorem readFiring_information :
    readFiring.information (frames action) sevenRow = [(x, c 7)] :=
  rfl

theorem renamed_readFiring_information :
    (renameFiring unknownToName id readFiring).information (frames action)
      (renameState unknownToName sevenRow) = [(c 5, c 7)] :=
  rfl

theorem readFiring_fresh : readFiring.Fresh (frames action) sevenRow := by
  intro b g h
  refine ⟨h, ?_, ?_⟩
  · rintro t (inside | inside | ⟨o, -, rfl⟩)
    · simp [sevenRow] at inside
    · simp [sevenRow] at inside
    · rfl
  · intro t member
    simp [readFiring, readAny, Rule.terms] at member
    subst member
    rfl

/-- **The firing is admitted**: the pattern `x` reads the row `7`. -/
theorem readFiring_admitted :
    (step (frames action) ℕ (ext action) {readAny}).Admits (s := sevenRow) readFiring := by
  refine (admits_iff readFiring).mpr ⟨readFiring_fresh, ⟨List.nodup_nil, List.nodup_nil, rfl, rfl, rfl,
    rfl⟩, ?_, ?_, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp [readFiring, sevenRow, Selection.commit]
  · rw [readFiring_information]
    exact ⟨PUnit.unit, everywhere 7, fun e member => by
      obtain rfl := List.mem_singleton.mp member
      rfl⟩
  · intro check member
    simp [readFiring, readAny, Firing.opened, RuleInstance.map] at member
  · intro q member
    simp [readFiring, readAny, Firing.collectOpened] at member

/-- **Its copy with the unknown exchanged for the name `5` is refused**: the pattern `5` does not read
the row `7`. -/
theorem renamed_readFiring_refused :
    ¬ (renameFiring unknownToName id readFiring).Admits (frames action)
      (renameState unknownToName sevenRow) := by
  rintro ⟨-, -, ⟨_, σ, solved⟩, -⟩
  rw [renamed_readFiring_information] at solved
  have key : Subst.applyTerm σ (c 5) = Subst.applyTerm σ (c 7) := solved _ List.mem_cons_self
  change (Term.const (5 : ℕ) : Term atoms) = Term.const (7 : ℕ) at key
  exact absurd (Term.const.inj key) (by decide)

/-- Exchange the names `5` and `7`. -/
def swapFiveSeven : NamePermutation atoms where
  constants := Equiv.swap 5 7
  functions := Equiv.refl _
  arity _ := rfl

/-- Exchange the names `5` and `7` and the unknowns `0` and `1`, together. -/
def namesAndUnknowns : Renaming action :=
  swapFiveSeven.automorphism.toRenaming.trans
    (unknownsAutomorphism (Equiv.swap 0 1 : Equiv.Perm atoms.vars)).toRenaming

/-- **Names and unknowns renamed together, each kind among itself, keep admission**: the answer of the
examples (read the request `x`, tell `x = 5`) becomes "read the unknown `1`, tell it `= 7`", and it is
admitted at the renamed request, whose row is the unknown `1`. -/
theorem answer_admitted_renamed :
    (renameFiring namesAndUnknowns.term namesAndUnknowns.subst Examples.answerFiring).Admits
        (frames action) (renameState namesAndUnknowns.term Examples.openRequest) ∧
      (renameState namesAndUnknowns.term Examples.openRequest).label 0 = .var 1 ∧
      (renameRule namesAndUnknowns.term Examples.answer).body.tell = [(.var 1, c 7)] :=
  ⟨(admits_renameFiring namesAndUnknowns (s := Examples.openRequest) Examples.answerFiring).mpr
      Examples.answer_admitted, rfl, rfl⟩

end UnknownControl

#print axioms renameCheck_count
#print axioms terms_renameRule
#print axioms Renaming.E_apply
#print axioms mentions_renameState
#print axioms fresh_renameFiring
#print axioms opened_renameFiring
#print axioms collectOpened_renameFiring
#print axioms information_renameFiring
#print axioms matchesAt_rename
#print axioms checkHolds_rename
#print axioms holds_renameFiring
#print axioms models_renameStore
#print axioms solvable_renameStore
#print axioms entails_renameStore
#print axioms enabled_renameFiring
#print axioms admits_renameFiring
#print axioms relabel_rename
#print axioms result_renameFiring
#print axioms exists_renameFiring
#print axioms renameState_injective
#print axioms succ_rename
#print axioms succ_of_rename
#print axioms succ_rename_iff
#print axioms reaches_rename
#print axioms reaches_of_rename
#print axioms reachable_rename
#print axioms terminal_rename_iff
#print axioms outcomes_rename
#print axioms step_equivariant
#print axioms renameProgram_eq_of_fixed
#print axioms reachable_rename_of_fixed
#print axioms outcomes_rename_of_fixed
#print axioms along_renameFiring
#print axioms NamePermutation.rename_rename_of_inverse
#print axioms NamePermutation.rename_applyTerm
#print axioms NamePermutation.automorphism
#print axioms exists_perm_map_eq
#print axioms NamePermutation.exists_of_lists
#print axioms names_equivariant
#print axioms admits_renameNames
#print axioms result_renameNames
#print axioms reachable_renameNames
#print axioms outcomes_renameNames
#print axioms consumeOnly_admitted
#print axioms consumeOnly_terminal
#print axioms consumeOnly_outcome
#print axioms renamed_state_and_rule
#print axioms renamed_admitted
#print axioms original_refused_at_renamed
#print axioms renamed_outcome
#print axioms swapOneTwo_laws
#print axioms swapOneTwo_not_renaming
#print axioms takeFiring_admitted
#print axioms renamed_takeFiring_refused
#print axioms last_renameRun
#print axioms word_renameRun
#print axioms toLast_renameRun
#print axioms unknownToName_laws
#print axioms readFiring_admitted
#print axioms renamed_readFiring_refused
#print axioms permuteUnknowns_applyTerm
#print axioms unknownsAutomorphism
#print axioms answer_admitted_renamed

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Equivalence.NameRenaming
