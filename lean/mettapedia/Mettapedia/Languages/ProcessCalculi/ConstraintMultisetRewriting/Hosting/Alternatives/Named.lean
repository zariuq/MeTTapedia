import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting.Alternatives.Chains

/-!
# Named firings and named moves

A program of the step is a set of rules, so the step does not know which equation a schema came
from: two equations that differ only in their site have one schema. To count alternatives, the
firings of a translated program are **named**: the four control rules of the first fragment by their
tags, and an equation's schema by the equation's position in the program (`RuleName`, `ruleNamed`).
Reading the program as a family indexed by these names is the one piece of information the set of
rules forgets.

* `FiresNamed`: a firing by the rule a name denotes.
* `NamedMove`: the source's move of an alternative of the first fragment, restricted to the child a
  name selects.
* `move_names`: **every move of an alternative of the fragment is its named moves**: a list of
  distinct names whose children are the bag the move makes, each child the name's only one; a move
  makes no child exactly when the alternative fails, and otherwise makes a live child.
* `plain_moves`: an alternative of the fragment that has not finished can move.
* `simulation_named`, `reflection_named`: a named move to a live child is one firing by the same
  name, to any fresh identity, and every named firing from a represented alternative is the named
  move of that alternative.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting.Alternatives

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open SourceLanguage
open MeTTaCalculus.OccurrenceCommits (Enabled fire)

variable {S : Signature} {Γ : Ctx S} {star : S.Srt} (N : Nodes S Γ star)
variable {κ : Keys S}

/-! ## Names -/

/-- **The names of the firings of a translated program of the first fragment**: the control rules by
their tags, and an equation's schema by the equation's position. -/
inductive RuleName where
  | ret
  | unmatched
  | left
  | right
  | eqn (i : ℕ)
  deriving DecidableEq

/-- The rule a name denotes; a position past the program's end denotes none. -/
def ruleNamed {Ty : Type} (P : SourceLanguage.Program κ Γ star Ty) : RuleName → Option (CRule S)
  | .ret => some (retRule N)
  | .unmatched => some (unmatchedRule N)
  | .left => some (choiceLeftRule N)
  | .right => some (choiceRightRule N)
  | .eqn i => (P.equations[i]?).map (schema N)

/-- **A named firing**: a firing by the rule the name denotes, taking `o` and making `o'`. -/
def FiresNamed {Ty : Type} (P : SourceLanguage.Program κ Γ star Ty) (n : RuleName) (s : HostState S)
    (o : ℕ) (s' : HostState S) (o' : ℕ) : Prop :=
  ∃ r, ruleNamed N P n = some r ∧ FiresAt (translate N P) r s o s' o'

theorem firesNamed_fires {Ty : Type} {P : SourceLanguage.Program κ Γ star Ty} {n : RuleName}
    {s s' : HostState S} {o o' : ℕ} (fired : FiresNamed N P n s o s' o') : Fires N P s s' := by
  obtain ⟨_, _, firedAt⟩ := fired
  exact fires_of_firesAt N firedAt

/-- **Forgetting names**: a named chain is a chain of the rules its names denote. -/
theorem chain_forget {Ty : Type} {P : SourceLanguage.Program κ Γ star Ty} {s s' : HostState S} {o o' : ℕ}
    {word : List RuleName} (chain : Chain (FiresNamed N P) s o word s' o') :
    Chain (FiresAt (translate N P)) s o (word.filterMap (ruleNamed N P)) s' o' := by
  induction chain with
  | nil => exact .nil _ _
  | snoc _ last ih =>
      obtain ⟨r, named, fired⟩ := last
      rw [List.filterMap_append, List.filterMap_cons_some named, List.filterMap_nil]
      exact .snoc ih fired

/-! ## Named moves of the source -/

section Moves

variable {D : Discipline S Γ star} {P : SourceLanguage.Program κ Γ star D.Ty}
  {supply : ℕ → Term S Γ star}

variable (P) in
/-- **A named move**: the move of an alternative of the first fragment, restricted to the child the
name selects. -/
inductive NamedMove (w : World κ Γ star) :
    Branch κ Γ star D.Ty → RuleName → World κ Γ star → Branch κ Γ star D.Ty → Prop
  | ret (K : List (Constraint κ Γ star)) (t : Data κ Γ star) (fs ps) :
      NamedMove w ⟨K, .eval (.ret t), fs, ps⟩ .ret w ⟨K, .value t, fs, ps⟩
  | unmatched (K : List (Constraint κ Γ star)) (t : Data κ Γ star) (fs ps)
      (none : ∀ e ∈ P.equations, ¬ Solvable (K ++ [(instantiate (copyAt κ w.scope) e.lhs, t)])) :
      NamedMove w ⟨K, .eval (.apply t), fs, ps⟩ .unmatched w ⟨K, .value t, fs, ps⟩
  | left (K : List (Constraint κ Γ star)) (c d : Comp κ Γ star D.Ty) (fs ps) :
      NamedMove w ⟨K, .eval (.choice c d), fs, ps⟩ .left w ⟨K, .eval c, fs, ps⟩
  | right (K : List (Constraint κ Γ star)) (c d : Comp κ Γ star D.Ty) (fs ps) :
      NamedMove w ⟨K, .eval (.choice c d), fs, ps⟩ .right w ⟨K, .eval d, fs, ps⟩
  | eqn (K : List (Constraint κ Γ star)) (t : Data κ Γ star) (fs ps) (i : ℕ)
      (e : SourceLanguage.Equation κ Γ star D.Ty) (get : P.equations[i]? = some e)
      (matched : ∃ e' ∈ P.equations, Solvable (K ++ [(instantiate (copyAt κ w.scope) e'.lhs, t)])) :
      NamedMove w ⟨K, .eval (.apply t), fs, ps⟩ (.eqn i) w.fresh (callBranch D w.scope K t fs ps e)

/-- **A name selects one child**: two named moves of one alternative by one name agree. -/
theorem NamedMove.unique {w w₁ w₂ : World κ Γ star} {b b₁ b₂ : Branch κ Γ star D.Ty} {n : RuleName}
    (first : NamedMove P w b n w₁ b₁) (second : NamedMove P w b n w₂ b₂) : w₁ = w₂ ∧ b₁ = b₂ := by
  cases first with
  | ret => cases second; exact ⟨rfl, rfl⟩
  | unmatched => cases second; exact ⟨rfl, rfl⟩
  | left => cases second; exact ⟨rfl, rfl⟩
  | right => cases second; exact ⟨rfl, rfl⟩
  | eqn K t fs ps i e get matched =>
      cases second with
      | eqn _ _ _ _ _ e' get' _ =>
          rw [get] at get'
          cases get'
          exact ⟨rfl, rfl⟩

/-- **A move of the fragment is its named moves.** The names are distinct, their children are the
bag the move makes, and each name has exactly that child; the move makes no child exactly when the
alternative fails, and otherwise one of its children is live. -/
theorem move_names {w w' : World κ Γ star} {b : Branch κ Γ star D.Ty} {bs : Multiset (Branch κ Γ star D.Ty)}
    (plain : PlainBranch b) (live : Solvable b.store) (move : Move D P supply w b w' bs) :
    ∃ (ns : List RuleName) (child : RuleName → Branch κ Γ star D.Ty), ns.Nodup ∧
      bs = ((ns.map child : List (Branch κ Γ star D.Ty)) : Multiset (Branch κ Γ star D.Ty)) ∧
      (∀ n ∈ ns, NamedMove P w b n w' (child n)) ∧
      (∀ n w'' b'', NamedMove P w b n w'' b'' → n ∈ ns ∧ w'' = w' ∧ b'' = child n) ∧
      (ns = [] → b.focus = .eval .fail) ∧
      (ns ≠ [] → ∃ n ∈ ns, Solvable (child n).store) := by
  obtain ⟨noFrames, shape⟩ := plain
  cases move
  case ret K t fs ps =>
    refine ⟨[.ret], fun _ => ⟨K, .value t, fs, ps⟩, List.nodup_singleton _, rfl,
      fun n member => by rw [List.mem_singleton.mp member]; exact .ret K t fs ps, ?_,
      fun none => by simp at none, fun _ => ⟨.ret, List.mem_singleton_self _, live⟩⟩
    intro n w'' b'' named
    cases named
    exact ⟨List.mem_singleton_self _, rfl, rfl⟩
  case apply K t fs ps matched =>
    let child : RuleName → Branch κ Γ star D.Ty := fun n => match n with
      | .eqn i => ((P.equations[i]?).map (callBranch D w.scope K t fs ps)).getD ⟨K, .eval (.apply t), fs, ps⟩
      | _ => ⟨K, .eval (.apply t), fs, ps⟩
    have childAt : ∀ i (small : i < P.equations.length),
        child (.eqn i) = callBranch D w.scope K t fs ps P.equations[i] := by
      intro i small
      simp [child, List.getElem?_eq_getElem small]
    refine ⟨(List.range P.equations.length).map .eqn, child, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact List.Nodup.map (by intro x y same; cases same; rfl) List.nodup_range
    · apply congrArg (fun l : List (Branch κ Γ star D.Ty) => (l : Multiset (Branch κ Γ star D.Ty)))
      apply List.ext_getElem
      · simp
      · intro k small _
        simp only [List.length_map] at small
        simp only [List.getElem_map, List.getElem_range]
        exact (childAt k small).symm
    · intro n member
      obtain ⟨i, small, rfl⟩ := List.mem_map.mp member
      have small' := List.mem_range.mp small
      rw [childAt i small']
      exact .eqn K t fs ps i _ (List.getElem?_eq_getElem small') matched
    · intro n w'' b'' named
      cases named with
      | unmatched _ _ _ _ none =>
          obtain ⟨e, member, solvable⟩ := matched
          exact absurd solvable (none e member)
      | eqn _ _ _ _ i e get _ =>
          have small : i < P.equations.length := by
            by_contra big
            rw [List.getElem?_eq_none (not_lt.mp big)] at get
            cases get
          refine ⟨List.mem_map.mpr ⟨i, List.mem_range.mpr small, rfl⟩, rfl, ?_⟩
          rw [childAt i small]
          rw [List.getElem?_eq_getElem small] at get
          cases get
          rfl
    · intro none
      exfalso
      obtain ⟨e, member, _⟩ := matched
      have : P.equations.length ≠ 0 := List.length_pos_of_mem member |>.ne'
      simp [List.map_eq_nil_iff, List.range_eq_nil, this] at none
    · intro _
      obtain ⟨e, member, solvable⟩ := matched
      obtain ⟨i, small, rfl⟩ := List.getElem_of_mem member
      exact ⟨.eqn i, List.mem_map.mpr ⟨i, List.mem_range.mpr small, rfl⟩, by rw [childAt i small]; exact solvable⟩
  case unmatched K t fs ps none =>
    refine ⟨[.unmatched], fun _ => ⟨K, .value t, fs, ps⟩, List.nodup_singleton _, rfl,
      fun n member => by rw [List.mem_singleton.mp member]; exact .unmatched K t fs ps none, ?_,
      fun nil => by simp at nil, fun _ => ⟨.unmatched, List.mem_singleton_self _, live⟩⟩
    intro n w'' b'' named
    cases named with
    | unmatched => exact ⟨List.mem_singleton_self _, rfl, rfl⟩
    | eqn _ _ _ _ i e get matched =>
        obtain ⟨e', member, solvable⟩ := matched
        exact absurd solvable (none e' member)
  case choice K c d fs ps =>
    let child : RuleName → Branch κ Γ star D.Ty := fun n => match n with
      | .right => ⟨K, .eval d, fs, ps⟩
      | _ => ⟨K, .eval c, fs, ps⟩
    refine ⟨[.left, .right], child, by decide, rfl, ?_, ?_, fun nil => by simp at nil,
      fun _ => ⟨.left, by simp, live⟩⟩
    · intro n member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact .left K c d fs ps
      · exact .right K c d fs ps
    · intro n w'' b'' named
      cases named with
      | left => exact ⟨by simp, rfl, rfl⟩
      | right => exact ⟨by simp, rfl, rfl⟩
  case fail K fs ps =>
    refine ⟨[], fun _ => ⟨K, .eval .fail, fs, ps⟩, List.nodup_nil, rfl, fun n member => (by cases member),
      ?_, fun _ => rfl, fun nonempty => absurd rfl nonempty⟩
    intro n w'' b'' named
    cases named
  all_goals first
    | exact False.elim (plain_eval shape)
    | (simp at noFrames)

/-- **An alternative of the fragment that has not finished can move.** -/
theorem plain_moves (w : World κ Γ star) {b : Branch κ Γ star D.Ty} (plain : PlainBranch b)
    (notFinished : ¬ b.Finished (D := D)) : ∃ w' bs, Move D P supply w b w' bs := by
  obtain ⟨K, focus, fs, ps⟩ := b
  obtain ⟨frames, shape⟩ := plain
  simp only at frames
  subst frames
  rcases shape with ⟨c, same, pc⟩ | ⟨t, same⟩
  · simp only at same
    subst same
    cases c with
    | ret t => exact ⟨_, _, .ret w K t [] ps⟩
    | apply t =>
        by_cases matched : ∃ e ∈ P.equations, Solvable (K ++ [(instantiate (copyAt κ w.scope) e.lhs, t)])
        · exact ⟨_, _, .apply w K t [] ps matched⟩
        · exact ⟨_, _, .unmatched w K t [] ps fun e member solvable => matched ⟨e, member, solvable⟩⟩
    | choice c d => exact ⟨_, _, .choice w K c d [] ps⟩
    | fail => exact ⟨_, _, .fail w K [] ps⟩
    | _ => exact pc.elim
  · simp only at same
    subst same
    exact absurd ⟨rfl, t, rfl⟩ notFinished

end Moves

/-! ## Named firings and named moves correspond -/

section Correspond

/-- **Firing a simple rule canonically to any fresh identity**: the canonical firing of the rule (the
canonical extension and opening of `RuleSyntax.Contextual.canonical`), taking `a` and making `k`, is
admitted, and its result represents the child. -/
theorem fire_simple_canonical {Ty : Type} {P : SourceLanguage.Program κ Γ star Ty} {r : CRule S}
    (member : r ∈ translate N P) {pat out : Observation S r.locals.arity} (simple : SimpleRule r pat out)
    (hcollect : r.collect = []) {n n' : ℕ} {b b' : Branch κ Γ star Ty} {s : HostState S} {a : ℕ}
    (rep : Represents N P n b s a)
    (moves : ∀ (B : Interface.Frames.Frame S) (q : Observation S B.arity),
      (∃ h : Assignment r.locals.arity B.arity, branchReads N b B (instantiateObservation h pat) ∧
        (Interface.Frames.contextual S).Models h r.body.tell ∧ instantiateObservation h out = q) ↔
      branchReads N b' B q)
    (live : Solvable b'.store) {k : ℕ} (hk : k ∉ s.present)
    (guard : (Interface.Frames.contextual S).Entails
      ((RuleSyntax.Contextual.canonical (F := s.frame) r member ⟨[a], [], [k]⟩ []).information
        (Interface.Frames.contextual S) s)
      (fun _ σ => (RuleSyntax.Contextual.canonical (F := s.frame) r member ⟨[a], [], [k]⟩ []).Holds
        (Interface.Frames.contextual S) s σ))
    (fresh : BranchBelow n' b') (noPending : b'.pending = []) :
    (RuleSyntax.Contextual.canonical (F := s.frame) r member ⟨[a], [], [k]⟩ []).Admits
        (Interface.Frames.contextual S) s ∧
      Represents N P n' b'
        ((RuleSyntax.Contextual.canonical (F := s.frame) r member ⟨[a], [], [k]⟩ []).result
          (Interface.Frames.contextual S) s) k := by
  let f : RuleSyntax.Firing ℕ (RuleSyntax.Contextual.declarations S) (translate N P) s.frame :=
    RuleSyntax.Contextual.canonical (F := s.frame) r member ⟨[a], [], [k]⟩ []
  have simpleF : Simple f a k pat out := ⟨rfl, rfl, rfl, simple.take, simple.noRead, simple.produce⟩
  have shapes : f.Shapes (Interface.Frames.contextual S) s := by
    refine ⟨RuleSyntax.Contextual.canonical_fresh s r member _ _, List.nodup_singleton a,
      List.nodup_singleton k, ?_, ?_, ?_, ?_⟩
    · change r.body.take.length = 1; rw [simple.take]; rfl
    · change r.body.read.length = 0; rw [simple.noRead]; rfl
    · change r.body.produce.length = 1; rw [simple.produce]; rfl
    · change r.collect.length = 0; rw [hcollect]; rfl
  have aPresent : a ∈ s.present := by rw [rep.present]; exact Finset.mem_insert_self _ _
  have solvable : (Interface.Frames.contextual S).Solvable (f.information (Interface.Frames.contextual S) s) := by
    obtain ⟨W, target, σ, solved⟩ := live
    have reads : branchReads N b' ⟨W, target⟩ (observe (encBranch N (instantiate σ) b')) := ⟨σ, solved, rfl⟩
    obtain ⟨h, readsB, told, _⟩ := (moves _ _).mpr reads
    obtain ⟨g, known, matched⟩ := (rep.reads _ _).mpr readsB
    obtain ⟨u, solvedU, _⟩ := simple_amalgamate simpleF shapes.1 aPresent g h known told matched.symm
    exact ⟨_, u, solvedU⟩
  exact ⟨⟨shapes, enabled_single aPresent hk, solvable, guard⟩,
    represents_after N rep simpleF shapes hk moves fresh noPending⟩

/-- **Firing a simple rule to any fresh identity**: as `fire_simple`, with the made row's identity
any identity not present. -/
theorem fire_simple_at {Ty : Type} {P : SourceLanguage.Program κ Γ star Ty} {r : CRule S}
    (member : r ∈ translate N P) {pat out : Observation S r.locals.arity} (simple : SimpleRule r pat out)
    (hcollect : r.collect = []) {n n' : ℕ} {b b' : Branch κ Γ star Ty} {s : HostState S} {a : ℕ}
    (rep : Represents N P n b s a)
    (moves : ∀ (B : Interface.Frames.Frame S) (q : Observation S B.arity),
      (∃ h : Assignment r.locals.arity B.arity, branchReads N b B (instantiateObservation h pat) ∧
        (Interface.Frames.contextual S).Models h r.body.tell ∧ instantiateObservation h out = q) ↔
      branchReads N b' B q)
    (live : Solvable b'.store) {k : ℕ} (hk : k ∉ s.present)
    (guard : (Interface.Frames.contextual S).Entails
      ((RuleSyntax.Contextual.canonical (F := s.frame) r member ⟨[a], [], [k]⟩ []).information
        (Interface.Frames.contextual S) s)
      (fun _ σ => (RuleSyntax.Contextual.canonical (F := s.frame) r member ⟨[a], [], [k]⟩ []).Holds
        (Interface.Frames.contextual S) s σ))
    (fresh : BranchBelow n' b') (noPending : b'.pending = []) :
    ∃ s', FiresAt (translate N P) r s a s' k ∧ Represents N P n' b' s' k := by
  obtain ⟨admitted, rep'⟩ :=
    fire_simple_canonical N member simple hcollect rep moves live hk guard fresh noPending
  exact ⟨_, ⟨RuleSyntax.Contextual.canonical (F := s.frame) r member ⟨[a], [], [k]⟩ [], rfl, admitted,
    rfl, rfl, rfl⟩, rep'⟩

/-- **A canonical named firing**: the canonical firing (the canonical extension and opening of
`RuleSyntax.Contextual.canonical`) of the rule the name denotes, taking `o` and making `o'`, admitted,
with result `s'`. -/
def FiresNamedCanonical {Ty : Type} (P : SourceLanguage.Program κ Γ star Ty) (n : RuleName)
    (s : HostState S) (o : ℕ) (s' : HostState S) (o' : ℕ) : Prop :=
  ∃ (r : CRule S) (member : r ∈ translate N P), ruleNamed N P n = some r ∧
    (RuleSyntax.Contextual.canonical (F := s.frame) r member ⟨[o], [], [o']⟩ []).Admits
      (Interface.Frames.contextual S) s ∧
    (RuleSyntax.Contextual.canonical (F := s.frame) r member ⟨[o], [], [o']⟩ []).result
      (Interface.Frames.contextual S) s = s'

/-- A canonical named firing is a named firing. -/
theorem FiresNamedCanonical.firesNamed {Ty : Type} {P : SourceLanguage.Program κ Γ star Ty}
    {n : RuleName} {s s' : HostState S} {o o' : ℕ} (fired : FiresNamedCanonical N P n s o s' o') :
    FiresNamed N P n s o s' o' := by
  obtain ⟨r, member, named, admitted, result⟩ := fired
  exact ⟨r, named, RuleSyntax.Contextual.canonical (F := s.frame) r member ⟨[o], [], [o']⟩ [], rfl,
    admitted, rfl, rfl, result⟩

variable {D : Discipline S Γ star} {P : SourceLanguage.Program κ Γ star D.Ty}

/-- **Canonical named simulation**: a named move of a represented alternative to a live child is the
canonical firing of the rule the name denotes, to any fresh identity, whose result represents the
child. -/
theorem simulation_named_canonical (plainP : PlainProgram P) {w w' : World κ Γ star}
    {b b' : Branch κ Γ star D.Ty} {n : RuleName} (move : NamedMove P w b n w' b') {s : HostState S}
    {a : ℕ} (rep : Represents N P w.scope b s a) (plain : PlainBranch b) (live : Solvable b'.store)
    {k : ℕ} (hk : k ∉ s.present) :
    ∃ s', FiresNamedCanonical N P n s a s' k ∧ Represents N P w'.scope b' s' k ∧ PlainBranch b' := by
  obtain ⟨noFrames, shape⟩ := plain
  cases move with
  | ret K t fs ps =>
      obtain ⟨admitted, rep'⟩ := fire_simple_canonical N (retRule_mem N P) ⟨rfl, rfl, rfl⟩ rfl rep
        (fun B q => transfer_ret N rfl q) live hk (entails_of_no_checks rfl rfl)
        (branchBelow_focus rep.fresh rfl rfl (by simp [focusData, Comp.data])) rep.noPending
      exact ⟨_, ⟨_, retRule_mem N P, rfl, admitted, rfl⟩, rep', noFrames, .inr ⟨t, rfl⟩⟩
  | unmatched K t fs ps none =>
      obtain ⟨admitted, rep'⟩ := fire_simple_canonical N (unmatchedRule_mem N P) ⟨rfl, rfl, rfl⟩ rfl rep
        (fun B q => transfer_unmatched N rfl q) live hk (unmatched_guard N rep none)
        (branchBelow_focus rep.fresh rfl rfl (by simp [focusData, Comp.data])) rep.noPending
      exact ⟨_, ⟨_, unmatchedRule_mem N P, rfl, admitted, rfl⟩, rep', noFrames, .inr ⟨t, rfl⟩⟩
  | left K c d fs ps =>
      have plainCD : PlainComp c ∧ PlainComp d := by
        rcases shape with ⟨c', same, pc⟩ | ⟨_, same⟩
        · cases same; exact pc
        · cases same
      obtain ⟨admitted, rep'⟩ := fire_simple_canonical N (choiceLeftRule_mem N P) ⟨rfl, rfl, rfl⟩ rfl rep
        (fun B q => transfer_choiceLeft N rfl q) live hk (entails_of_no_checks rfl rfl)
        (branchBelow_focus rep.fresh rfl rfl
          (fun t' member => by simp only [focusData, Comp.data] at member ⊢; exact List.mem_append_left _ member))
        rep.noPending
      exact ⟨_, ⟨_, choiceLeftRule_mem N P, rfl, admitted, rfl⟩, rep', noFrames, .inl ⟨c, rfl, plainCD.1⟩⟩
  | right K c d fs ps =>
      have plainCD : PlainComp c ∧ PlainComp d := by
        rcases shape with ⟨c', same, pc⟩ | ⟨_, same⟩
        · cases same; exact pc
        · cases same
      obtain ⟨admitted, rep'⟩ := fire_simple_canonical N (choiceRightRule_mem N P) ⟨rfl, rfl, rfl⟩ rfl rep
        (fun B q => transfer_choiceRight N rfl q) live hk (entails_of_no_checks rfl rfl)
        (branchBelow_focus rep.fresh rfl rfl
          (fun t' member => by simp only [focusData, Comp.data] at member ⊢; exact List.mem_append_right _ member))
        rep.noPending
      exact ⟨_, ⟨_, choiceRightRule_mem N P, rfl, admitted, rfl⟩, rep', noFrames, .inl ⟨d, rfl, plainCD.2⟩⟩
  | eqn K t fs ps i e get matched =>
      have eMember : e ∈ P.equations := List.mem_of_getElem? get
      obtain ⟨admitted, rep'⟩ := fire_simple_canonical N (schema_mem N P eMember) ⟨rfl, rfl, rfl⟩ rfl rep
        (fun B q => transfer_schema N e rfl rep.fresh q) live hk (entails_of_no_checks rfl rfl)
        (branchBelow_call rep.fresh e) rep.noPending
      refine ⟨_, ⟨_, schema_mem N P eMember, by simp [ruleNamed, get], admitted, rfl⟩, rep', noFrames,
        .inl ⟨_, rfl, ?_⟩⟩
      exact plainComp_mapData _ _ (plainP e eMember)

/-- **Named simulation**: a named move of a represented alternative to a live child is one firing by
the same name, to any fresh identity, whose result represents the child. -/
theorem simulation_named (plainP : PlainProgram P) {w w' : World κ Γ star} {b b' : Branch κ Γ star D.Ty}
    {n : RuleName} (move : NamedMove P w b n w' b') {s : HostState S} {a : ℕ}
    (rep : Represents N P w.scope b s a) (plain : PlainBranch b) (live : Solvable b'.store) {k : ℕ}
    (hk : k ∉ s.present) :
    ∃ s', FiresNamed N P n s a s' k ∧ Represents N P w'.scope b' s' k ∧ PlainBranch b' := by
  obtain ⟨s', fired, rep', plain'⟩ := simulation_named_canonical N plainP move rep plain live hk
  exact ⟨s', FiresNamedCanonical.firesNamed N fired, rep', plain'⟩

/-- **Named reflection**: every named firing from a represented alternative of the fragment is the
named move of that alternative, and its result represents the move's child. -/
theorem reflection_named (plainP : PlainProgram P) {w : World κ Γ star} {b : Branch κ Γ star D.Ty}
    {n : RuleName} {s s' : HostState S} {a a' : ℕ} (rep : Represents N P w.scope b s a)
    (plain : PlainBranch b) (fired : FiresNamed N P n s a s' a') :
    ∃ w' b', NamedMove P w b n w' b' ∧ Represents N P w'.scope b' s' a' ∧ PlainBranch b' := by
  obtain ⟨r, named, ⟨rl, member, ext, opening, selection, seen⟩, rule, admitted, _, made, rfl⟩ := fired
  simp only at rule made
  subst rule
  obtain ⟨K, focus, fs, ps⟩ := b
  obtain ⟨noFrames, shape⟩ := plain
  simp only at noFrames
  subst noFrames
  cases n with
  | ret =>
      simp only [ruleNamed, Option.some.injEq] at named
      subst named
      obtain ⟨a'', simple, fresh, B, h, reads, _⟩ := admitted_takes_alternative N rep admitted rfl rfl rfl
        (fun h => ⟨_, _, congrArg observe (instantiate_altN N h _ _)⟩)
      have same : a'' = a' := by simpa using simple.madeOne.symm.trans made
      subst same
      obtain ⟨t, rfl⟩ := shape_ret N reads
      refine ⟨w, _, .ret K t [] ps, ?_, rfl, .inr ⟨t, rfl⟩⟩
      exact represents_after N rep simple admitted.1 fresh (fun B q => transfer_ret N rfl q)
        (branchBelow_focus rep.fresh rfl rfl (by simp [focusData, Comp.data])) rep.noPending
  | unmatched =>
      simp only [ruleNamed, Option.some.injEq] at named
      subst named
      obtain ⟨a'', simple, fresh, B, h, reads, _⟩ := admitted_takes_alternative N rep admitted rfl rfl rfl
        (fun h => ⟨_, _, congrArg observe (instantiate_altN N h _ _)⟩)
      have same : a'' = a' := by simpa using simple.madeOne.symm.trans made
      subst same
      change branchReads N _ B (observe (instantiate h _)) at reads
      rw [instantiate_altN, instantiate_evalN, instantiate_applyN] at reads
      obtain ⟨t, σ, rfl, _, _⟩ := shape_apply N reads
      refine ⟨w, _, .unmatched K t [] ps (unmatched_none N rep simple admitted), ?_, rfl, .inr ⟨t, rfl⟩⟩
      exact represents_after N rep simple admitted.1 fresh (fun B q => transfer_unmatched N rfl q)
        (branchBelow_focus rep.fresh rfl rfl (by simp [focusData, Comp.data])) rep.noPending
  | left =>
      simp only [ruleNamed, Option.some.injEq] at named
      subst named
      obtain ⟨a'', simple, fresh, B, h, reads, _⟩ := admitted_takes_alternative N rep admitted rfl rfl rfl
        (fun h => ⟨_, _, congrArg observe (instantiate_altN N h _ _)⟩)
      have same : a'' = a' := by simpa using simple.madeOne.symm.trans made
      subst same
      obtain ⟨c, d, rfl⟩ := shape_choice N reads
      have plainCD : PlainComp c ∧ PlainComp d := by
        rcases shape with ⟨c', same, pc⟩ | ⟨_, same⟩
        · cases same; exact pc
        · cases same
      refine ⟨w, _, .left K c d [] ps, ?_, rfl, .inl ⟨c, rfl, plainCD.1⟩⟩
      exact represents_after N rep simple admitted.1 fresh (fun B q => transfer_choiceLeft N rfl q)
        (branchBelow_focus rep.fresh rfl rfl
          (fun t' member => by simp only [focusData, Comp.data] at member ⊢; exact List.mem_append_left _ member))
        rep.noPending
  | right =>
      simp only [ruleNamed, Option.some.injEq] at named
      subst named
      obtain ⟨a'', simple, fresh, B, h, reads, _⟩ := admitted_takes_alternative N rep admitted rfl rfl rfl
        (fun h => ⟨_, _, congrArg observe (instantiate_altN N h _ _)⟩)
      have same : a'' = a' := by simpa using simple.madeOne.symm.trans made
      subst same
      obtain ⟨c, d, rfl⟩ := shape_choice N reads
      have plainCD : PlainComp c ∧ PlainComp d := by
        rcases shape with ⟨c', same, pc⟩ | ⟨_, same⟩
        · cases same; exact pc
        · cases same
      refine ⟨w, _, .right K c d [] ps, ?_, rfl, .inl ⟨d, rfl, plainCD.2⟩⟩
      exact represents_after N rep simple admitted.1 fresh (fun B q => transfer_choiceRight N rfl q)
        (branchBelow_focus rep.fresh rfl rfl
          (fun t' member => by simp only [focusData, Comp.data] at member ⊢; exact List.mem_append_right _ member))
        rep.noPending
  | eqn i =>
      obtain ⟨e, get, rfl⟩ := Option.map_eq_some_iff.mp named
      have eMember : e ∈ P.equations := List.mem_of_getElem? get
      obtain ⟨a'', simple, fresh, B, h, reads, _⟩ := admitted_takes_alternative N rep admitted rfl rfl rfl
        (fun h => ⟨_, _, congrArg observe (instantiate_altN N h _ _)⟩)
      have same : a'' = a' := by simpa using simple.madeOne.symm.trans made
      subst same
      change branchReads N _ B (observe (instantiate h _)) at reads
      rw [instantiate_altN, instantiate_evalN, instantiate_applyN, instantiate_asUnknowns] at reads
      obtain ⟨t, σ, rfl, solved, onCall⟩ := shape_apply N reads
      have callBelow : DependsBelow w.scope t := rep.fresh.2.1 t (by simp [focusData, Comp.data])
      have matched : ∃ e' ∈ P.equations, Solvable (K ++ [(instantiate (copyAt κ w.scope) e'.lhs, t)]) :=
        ⟨e, eMember, (solvable_copy_iff e.lhs rep.fresh.1 callBelow).mpr ⟨_, _, σ, _, solved, onCall.symm⟩⟩
      refine ⟨w.fresh, _, .eqn K t [] ps i e get matched, ?_, rfl,
        .inl ⟨_, rfl, plainComp_mapData _ _ (plainP e eMember)⟩⟩
      exact represents_after N rep simple admitted.1 fresh (fun B q => transfer_schema N e rfl rep.fresh q)
        (branchBelow_call rep.fresh e) rep.noPending

end Correspond

#print axioms chain_forget
#print axioms move_names
#print axioms plain_moves
#print axioms fire_simple_canonical
#print axioms fire_simple_at
#print axioms FiresNamedCanonical.firesNamed
#print axioms simulation_named_canonical
#print axioms simulation_named
#print axioms reflection_named

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting.Alternatives
