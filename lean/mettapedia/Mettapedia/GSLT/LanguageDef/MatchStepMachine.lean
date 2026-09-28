import Mettapedia.GSLT.LanguageDef.HostCallMachine

/-!
# Match steps over a space

In the compiled open equation tier, `(match S P T)` inside an equation body is a
step of its own.  The space is read once and its atoms, in order and with
duplicates, become the alternatives of one choice.  For each candidate atom the
step gives the atom's variables new store variables, unifies `P` with the fresh
copy, two-sided and with the occurs check, in the current store, and on success
continues with `T` in the same activation, with the match's destination.  This
module models that step on the output-first machine of
`DestinationPassingActivation` and proves it equivalent to a call of a relation
whose equations are the space's facts.

**Spaces as fact relations.**  A stored atom (`Atom`) is a template whose slots
are the atom's own variables; a ground atom has none.  A program with match
sites has the relations `Rel ⊕ Sp`: its own, and one per space.  The fact of an
atom `A` (`fact`) is the equation `(= (m) A)`: `A`'s variables are its slots and
its body returns `A`.  Extended by its exposed output (`Equation.withOutput`) its
head is the atom, `(m A)` (`withOutput_fact`), which is how the output-first
machine activates it: the destination is a head parameter.  `spaceFacts atoms s`
lists one fact per atom of the snapshot `atoms s`, in order, and
`withFacts P spaces atoms` is the translated program: `P`'s equations for its own
relations and the facts of every space in `spaces`.  A match site is
`matchSite s P T`, the call `letCall P (m s) [] T` of the space's relation, whose
answers `P` receives and whose continuation is `T`.  In a nested source body it
is `(let P (m) T)` (`sourceMatchSite`), which both normalizations turn into the
site (`norm_sourceMatchSite`).  A conjunctive pattern `(, P₁ P₂)` is lowered to
`matchSite s P₁ (matchSite s P₂ T)` (`conjunctionSite`); the lowering is stated,
not proved against a separate semantics of conjunctive patterns.

**The candidate step.**  `candidate S A p σ` allocates `A`'s variables in `σ` and
unifies the fresh copy with the pattern's instance `p`.  Activating the fact with
the atom as its head against the argument `p` is this step (`activate_fact`); the
output-first activation of the fact against the destination `p` is that
activation (`activateOut_fact`), and activating a space's facts at a match site
is the step, atom by atom (`activateOut_site`).  Over an exact store
(`ExactStore`) the step is exact: its store denotes the entry store's solutions
of `p = A'` and has the supply after allocation (`candidate_exact`).  Unifying in
the other orientation, pattern first, as the C does, succeeds exactly when the
step does, with the same solutions and supply (`candidate_symm`).  Hence
`activate_fact_exact`: activating one fact against `P` is two-sided unification
of `P` with a fresh copy of the atom, up to `SameAnswer`.

**The machine** `matching` (the instance of `matchingBy` for the candidate step)
runs the output-first machine except at a match site, a call of a space's
relation with no arguments (`siteOf?`).  The site becomes a last call of its
choice (`MatchCall.site`), whose alternatives are the candidates the step
accepts, in snapshot order, each continuing the site's code on the frames of the
running task: no frame is pushed and no fact returns.  Any other call of a
space's relation is served by the snapshot's facts (`serving`).

**Correctness.**  `expand_related`: from the same task, one step of each machine
gives the same successors and answers away from match sites.  At a match site
the translated run's fact activations and the match step's continuations
correspond one to one, in snapshot order, each fact to the continuation its
return resumes (`Resumes`).  With the stuttering simulation of `HostCallMachine`
(`simulates_repeats_stutter`) this gives both directions, `matching_follows` and
`translated_follows`, when every space is listed once (`spaces.count s = 1`).
The two runs deliver the same answers, in order: `matching_answers` and
`translated_answers` state equal answer lists, not only corresponding ones.  One
run exhausts its frontier exactly when the other does (`matching_terminates`,
`translated_terminates`, `terminates_iff`).  Step counts differ by one step per
resumed fact; no bound between them is stated.

**The output-first laws.**  Adding the same facts keeps programs aligned
(`withFacts_bindsAhead`), so `outputFirst_answers` and `outputFirst_terminates`
apply to the translated programs unchanged.  `matching_refines` and
`matching_refines_terminates` state the prefix and termination laws for the
machine with match steps against the output-at-return machine on the program
with its facts, and `source_matching_answers` does so for nested source
programs.

**Correspondence with the C.**

* The snapshot at entry: the site's choice computes its alternatives once, when
  the site is reached, from `atoms s`; the frontier then holds all of them, and
  no later step adds or removes one.
* Freshening per candidate: every candidate renames its atom's variables to
  variables newly allocated in the store it is tried in (`candidate`), and each
  candidate runs in its own branch store, so no binding made for one candidate
  reaches another.  `MatchStepControls` shows that a step without freshening
  delivers a different stream.
* First-occurrence pattern cells before the choice: `P`'s slots were allocated
  when the activation began, and the choice carries `P` instantiated in the
  activation's frame, computed once (`inspectOut_site`).  Every candidate
  unifies with that term, each in its own branch store.
* The template's code in the same activation: every candidate continues the
  site's code `T` with the activation's destination, on the activation's slots
  that `P` and `T` read (`inspectOut_site`, `reconstruct_capture`).

**Not modelled.**  Mutation of a space between answers (a space's snapshot is
fixed), the resolution of a space expression and concrete space backends, step
costs, and conformance of the C code: this is a model of the step, not a
verified translation of CeTTa's C.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.MatchSteps

open Mettapedia.Machines.SharedContinuation
open Mettapedia.GSLT.LanguageDef.DefunctionalizedEquationBodies
open Mettapedia.GSLT.LanguageDef.DestinationPassing
open Mettapedia.GSLT.LanguageDef.HostCalls (ExpandsTo simulates_repeats_stutter)
open Mettapedia.GSLT.Dynamics.ContextIndexedSwitching (repeats)

/-! ## Spaces as fact relations -/

section Facts

variable {Term Rel Sp Op : Type} (L : TemplateLanguage Term)

/-- A stored atom: a template whose slots are the atom's own variables.  A
ground atom has no slots. -/
abbrev Atom := Σ k, L.Tmpl k

/-- The fact of a stored atom: the atom's variables are the equation's slots,
it has no parameters, and its body returns the atom.  Extended by its exposed
output, its head is the atom (`withOutput_fact`). -/
def fact {R : Type} (A : Atom L) : Equation L R Op := ⟨A.1, [], .ret A.2⟩

/-- The relation of the space `s`: one fact per atom of the snapshot, in order,
duplicates included. -/
def spaceFacts (atoms : Sp → List (Atom L)) (s : Sp) : EqProgram L (Rel ⊕ Sp) Op :=
  (atoms s).map fun A => (.inr s, fact L A)

/-- The translated program: the program's equations for its own relations, and
the facts of every space listed in `spaces`. -/
def withFacts (P : EqProgram L (Rel ⊕ Sp) Op) (spaces : List Sp)
    (atoms : Sp → List (Atom L)) : EqProgram L (Rel ⊕ Sp) Op :=
  P.filter (fun e => e.1.isLeft) ++ spaces.flatMap (spaceFacts L atoms)

/-- The match site `(match s P T)` in an equation body: a call of the space's
relation with no arguments, whose answers the pattern `P` receives and whose
continuation is `T`. -/
abbrev matchSite {k : Nat} (s : Sp) (pattern : L.Tmpl k) (continuation : Code L (Rel ⊕ Sp) Op k) :
    Code L (Rel ⊕ Sp) Op k :=
  .letCall pattern (.inr s) [] continuation

/-- A conjunctive pattern `(, P₁ P₂)` over one space, lowered to nested match
sites: `(match s P₁ (match s P₂ T))`. -/
abbrev conjunctionSite {k : Nat} (s : Sp) (first second : L.Tmpl k)
    (continuation : Code L (Rel ⊕ Sp) Op k) : Code L (Rel ⊕ Sp) Op k :=
  matchSite L s first (matchSite L s second continuation)

/-- The match site in a nested source body: `(let P (m) T)` for the space's
relation `m`. -/
abbrev sourceMatchSite {k : Nat} (s : Sp) (pattern : L.Tmpl k)
    (continuation : Source L (Rel ⊕ Sp) Op k) : Source L (Rel ⊕ Sp) Op k :=
  .letE pattern (.call (.inr s) []) continuation

end Facts

/-! ## The machine with match steps -/

section Machine

variable {Term Store Rel Sp Op : Type} (L : TemplateLanguage Term)

variable {L} in
/-- One candidate of a match step: freshen the atom's variables into new store
variables, then unify the fresh copy with the pattern's instance, in the store
after allocation. -/
def candidate (S : StoreAlgebra Term Store Op) (A : Atom L) (pattern : Term) (σ : Store) :
    Option Store :=
  S.unify (L.inst A.2 (S.fresh σ A.1).1) pattern (S.fresh σ A.1).2

/-- A call of the machine with match steps: a call of the output-first machine,
or the choice of a match site: the space, the pattern's instance, the store,
and the frame of the continuation. -/
inductive MatchCall (L : TemplateLanguage Term) (Rel Sp Op Store : Type) where
  | base (call : DestCall Term Store (Rel ⊕ Sp))
  | site (space : Sp) (pattern : Term) (store : Store) (resume : DestFrame L (Rel ⊕ Sp) Op)

/-- A match site among calls: a call of a space's relation with no arguments,
whose destination is the pattern's instance. -/
def siteOf? : DestCall Term Store (Rel ⊕ Sp) → Option (Sp × Term × Store)
  | (.inr s, [], σ, some p) => some (s, p, σ)
  | _ => none

/-- A match site does not call: its choice is a last call, so the candidates
continue on the frames of the running task. -/
def toMatch :
    Instruction (DestCall Term Store (Rel ⊕ Sp)) (DestFrame L (Rel ⊕ Sp) Op) (Answer Term Store) →
      Instruction (MatchCall L Rel Sp Op Store) (DestFrame L (Rel ⊕ Sp) Op) (Answer Term Store)
  | .ret a => .ret a
  | .fail => .fail
  | .call c f =>
      match siteOf? c with
      | some (s, p, σ) => .tail (.site s p σ f)
      | none => .call (.base c) f
  | .tail c => .tail (.base c)

/-- The equations serving a call of the machine with match steps: the program's
for its own relations, the snapshot's facts for a space's relation. -/
def serving (P : EqProgram L (Rel ⊕ Sp) Op) (atoms : Sp → List (Atom L)) :
    Rel ⊕ Sp → EqProgram L (Rel ⊕ Sp) Op
  | .inl _ => P
  | .inr s => spaceFacts L atoms s

variable (S : StoreAlgebra Term Store Op) [DecidableEq Rel] [DecidableEq Sp] [Inhabited Term]

/-- **The machine with match steps**, for a candidate step `choose`.  It runs the
output-first machine, except at a match site: the site takes the snapshot of
its space, and every candidate that `choose` accepts continues the site's code
in the resulting store, on the frames of the running task, in snapshot order. -/
def matchingBy (choose : Atom L → Term → Store → Option Store) (P : EqProgram L (Rel ⊕ Sp) Op)
    (atoms : Sp → List (Atom L)) :
    Program Unit (DestControl L (Rel ⊕ Sp) Op Store) (MatchCall L Rel Sp Op Store)
      (DestFrame L (Rel ⊕ Sp) Op) (Answer Term Store) where
  inspect c := toMatch L (inspectOut L S c.frame c.dest c.store c.code)
  branches _ call :=
    match call with
    | .base c => (activateOut L S (serving L P atoms c.1) c).map fun a => ((), a)
    | .site s p σ f => (atoms s).filterMap fun A =>
        (choose A p σ).map fun σ' => ((), ⟨⟨f.slots, f.body, reconstruct f.captured, σ'⟩, f.dest⟩)
  resume _ f a := ((), ⟨⟨f.slots, f.body, reconstruct f.captured, a.2⟩, f.dest⟩)

/-- The machine with match steps whose candidate step freshens the atom. -/
abbrev matching (P : EqProgram L (Rel ⊕ Sp) Op) (atoms : Sp → List (Atom L)) :=
  matchingBy L S (candidate S) P atoms

end Machine

/-! ## Correspondence of tasks -/

section Correspondence

variable {Term Store R Op : Type} (L : TemplateLanguage Term) [Inhabited Term]

/-- A task of the translated run and a task of the run with match steps: the same
task, or a fact about to return to the frame of a match site's continuation and
that continuation, resumed in the fact's store. -/
inductive Resumes :
    Task Unit (DestControl L R Op Store) (DestFrame L R Op) →
      Task Unit (DestControl L R Op Store) (DestFrame L R Op) → Prop
  | same (t : Task Unit (DestControl L R Op Store) (DestFrame L R Op)) : Resumes t t
  | fact {k : Nat} (A : L.Tmpl k) (frame : Fin k → Term) (σ : Store) (dest : Option Term)
      (f : DestFrame L R Op) (returns : List (DestFrame L R Op)) :
      Resumes ⟨(), ⟨⟨k, .ret A, frame, σ⟩, dest⟩, f :: returns⟩
        ⟨(), ⟨⟨f.slots, f.body, reconstruct f.captured, σ⟩, f.dest⟩, returns⟩

end Correspondence

/-! ## The translated program's equations -/

section Equations

variable {Term Rel Sp Op : Type} (L : TemplateLanguage Term) [DecidableEq Rel] [DecidableEq Sp]

theorem equations_append {R : Type} [DecidableEq R] (P Q : EqProgram L R Op) (r : R) :
    (P ++ Q).equations r = P.equations r ++ Q.equations r := by
  simp [EqProgram.equations, List.filter_append]

/-- A space's relation has the snapshot's facts, and no other relation has any. -/
theorem spaceFacts_equations (atoms : Sp → List (Atom L)) (s : Sp) (r : Rel ⊕ Sp) :
    (spaceFacts (Op := Op) L atoms s).equations r =
      if r = .inr s then (atoms s).map (fact L) else [] := by
  by_cases h : r = .inr s
  · subst h
    simp [spaceFacts, EqProgram.equations, List.filter_map, Function.comp_def]
  · have h' : ¬ (Sum.inr s : Rel ⊕ Sp) = r := fun e => h e.symm
    simp [spaceFacts, EqProgram.equations, List.filter_map, Function.comp_def, h, h']

theorem flatMap_ite_eq {α : Type} (spaces : List Sp) (s : Sp) (g : Sp → List α) :
    spaces.flatMap (fun s' => if s = s' then g s' else []) =
      (List.replicate (spaces.count s) (g s)).flatten := by
  induction spaces with
  | nil => rfl
  | cons s' rest ih =>
      by_cases h : s = s'
      · subst h
        simp [ih, List.replicate_succ]
      · have h' : ¬ s' = s := fun e => h e.symm
        simp [ih, h, h']

/-- **The translated program serves every relation as the machine with match
steps does**, when every space is listed once. -/
theorem withFacts_equations (P : EqProgram L (Rel ⊕ Sp) Op) (spaces : List Sp)
    (atoms : Sp → List (Atom L)) (once : ∀ s, spaces.count s = 1) (r : Rel ⊕ Sp) :
    (withFacts L P spaces atoms).equations r = (serving L P atoms r).equations r := by
  have facts : EqProgram.equations (spaces.flatMap (spaceFacts (Op := Op) L atoms)) r =
      spaces.flatMap fun s => if r = .inr s then (atoms s).map (fact L) else [] := by
    simp only [EqProgram.equations, List.filter_flatMap, List.map_flatMap]
    congr 1
    funext s
    exact spaceFacts_equations L atoms s r
  rw [withFacts, equations_append, facts]
  cases r with
  | inl x =>
      have own : EqProgram.equations (P.filter fun e => e.1.isLeft) (.inl x) =
          P.equations (.inl x) := by
        simp only [EqProgram.equations, List.filter_filter]
        congr 1
        apply List.filter_congr
        intro e _
        cases e.1 <;> simp
      simp [own, serving]
  | inr s =>
      have own : EqProgram.equations (P.filter fun e => e.1.isLeft) (.inr s) = [] := by
        simp only [EqProgram.equations, List.filter_filter]
        rw [List.filter_eq_nil_iff.mpr]
        · rfl
        · intro e _
          cases e.1 <;> simp
      have pick := flatMap_ite_eq spaces s fun s => (atoms s).map (fact (R := Rel ⊕ Sp) (Op := Op) L)
      simp only [Sum.inr.injEq] at pick ⊢
      rw [own, pick, once s, serving, spaceFacts_equations]
      simp

end Equations

/-! ## One step of each machine -/

section Expansion

variable {Term Store Rel Sp Op : Type} (L : TemplateLanguage Term) (S : StoreAlgebra Term Store Op)
variable [DecidableEq Rel] [DecidableEq Sp] [Inhabited Term]

omit [DecidableEq Rel] [DecidableEq Sp] [Inhabited Term] in
theorem siteOf?_eq_some {c : DestCall Term Store (Rel ⊕ Sp)} {s : Sp} {p : Term} {σ : Store}
    (h : siteOf? c = some (s, p, σ)) : c = (.inr s, [], σ, some p) := by
  rcases c with ⟨r, args, σ', d⟩
  cases r with
  | inl x => simp [siteOf?] at h
  | inr s' =>
      cases args with
      | cons a as => simp [siteOf?] at h
      | nil =>
          cases d with
          | none => simp [siteOf?] at h
          | some p' =>
              simp only [siteOf?, Option.some.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, rfl, rfl⟩ := h
              rfl

omit [DecidableEq Rel] [DecidableEq Sp] [Inhabited Term] in
/-- The output-first activation reads a program only through the called
relation's equations. -/
theorem activateOut_congr {R : Type} [DecidableEq R] {P Q : EqProgram L R Op}
    (c : DestCall Term Store R) (same : P.equations c.1 = Q.equations c.1) :
    activateOut L S P c = activateOut L S Q c := by
  rcases c with ⟨rel, args, σ, dest⟩
  dsimp only at same
  simp only [activateOut, same]

omit [Inhabited Term] in
theorem activateOut_withFacts (P : EqProgram L (Rel ⊕ Sp) Op) (spaces : List Sp)
    (atoms : Sp → List (Atom L)) (once : ∀ s, spaces.count s = 1)
    (c : DestCall Term Store (Rel ⊕ Sp)) :
    activateOut L S (withFacts L P spaces atoms) c = activateOut L S (serving L P atoms c.1) c :=
  activateOut_congr L S c (withFacts_equations L P spaces atoms once c.1)

omit [Inhabited Term] in
/-- **The facts at a match site are the candidate step.**  Activating the
space's facts against the site's destination `p` yields, atom by atom in
snapshot order, the fact of every atom whose fresh copy the candidate step
unifies with `p`, in the store the candidate step produces. -/
theorem activateOut_site (P : EqProgram L (Rel ⊕ Sp) Op) (atoms : Sp → List (Atom L)) (s : Sp)
    (p : Term) (σ : Store) :
    activateOut L S (serving L P atoms (.inr s)) (.inr s, [], σ, some p) =
      (atoms s).filterMap fun A => (candidate S A p σ).map fun σ' =>
        (⟨⟨A.1, .ret A.2, (S.fresh σ A.1).1, σ'⟩, some p⟩ : DestControl L (Rel ⊕ Sp) Op Store) := by
  have facts : (serving L P atoms (Sum.inr s)).equations (Sum.inr s) = (atoms s).map (fact L) := by
    simp [serving, spaceFacts_equations]
  simp only [activateOut, facts, List.filterMap_map]
  rfl

omit [DecidableEq Rel] [DecidableEq Sp] in
/-- A fact about to return resumes its caller's frame, delivering nothing. -/
theorem expand_fact {R : Type} [DecidableEq R] (Q : EqProgram L R Op) {k : Nat} (A : L.Tmpl k)
    (frame : Fin k → Term) (σ : Store) (dest : Option Term) (f : DestFrame L R Op)
    (returns : List (DestFrame L R Op)) :
    expand (outputFirst L S Q) ⟨(), ⟨⟨k, .ret A, frame, σ⟩, dest⟩, f :: returns⟩ =
      ([⟨(), ⟨⟨f.slots, f.body, reconstruct f.captured, σ⟩, f.dest⟩, returns⟩], []) := rfl

theorem forall₂_filterMap_map {α β γ δ : Type} {R : γ → δ → Prop} (o : α → Option β)
    (h₁ : α → β → γ) (h₂ : α → β → δ) (rel : ∀ x y, R (h₁ x y) (h₂ x y)) :
    ∀ l : List α, List.Forall₂ R (l.filterMap fun x => (o x).map (h₁ x))
      (l.filterMap fun x => (o x).map (h₂ x))
  | [] => .nil
  | x :: rest => by
      cases hx : o x with
      | none =>
          rw [List.filterMap_cons_none (by simp [hx]), List.filterMap_cons_none (by simp [hx])]
          exact forall₂_filterMap_map o h₁ h₂ rel rest
      | some y =>
          rw [List.filterMap_cons_some (b := h₁ x y) (by simp [hx]),
            List.filterMap_cons_some (b := h₂ x y) (by simp [hx])]
          exact .cons (rel x y) (forall₂_filterMap_map o h₁ h₂ rel rest)

/-- **One step of each machine on the same task.**  Away from match sites the two
machines expand a task identically.  At a match site the translated run
activates the space's facts, each pushing the site's frame, while the run with
match steps continues the site's code directly: the successors correspond one to
one, in snapshot order, each fact to the continuation it will resume. -/
theorem expand_related (P : EqProgram L (Rel ⊕ Sp) Op) (spaces : List Sp)
    (atoms : Sp → List (Atom L)) (once : ∀ s, spaces.count s = 1)
    (t : Task Unit (DestControl L (Rel ⊕ Sp) Op Store) (DestFrame L (Rel ⊕ Sp) Op)) :
    List.Forall₂ (Resumes L) (expand (outputFirst L S (withFacts L P spaces atoms)) t).1
        (expand (matching L S P atoms) t).1 ∧
      (expand (outputFirst L S (withFacts L P spaces atoms)) t).2 =
        (expand (matching L S P atoms) t).2 := by
  rcases t with ⟨⟨⟩, c, returns⟩
  have hi : (matching L S P atoms).inspect c =
      toMatch L ((outputFirst L S (withFacts L P spaces atoms)).inspect c) := rfl
  simp only [expand]
  rw [hi]
  generalize (outputFirst L S (withFacts L P spaces atoms)).inspect c = i
  cases i with
  | ret a =>
      cases returns with
      | nil => exact ⟨.nil, rfl⟩
      | cons f pending => exact ⟨.cons (.same _) .nil, rfl⟩
  | fail => exact ⟨.nil, rfl⟩
  | call callee f =>
      cases hs : siteOf? callee with
      | none =>
          simp only [toMatch, hs, expandWith, outputFirst, matchingBy,
            activateOut_withFacts L S P spaces atoms once]
          exact ⟨List.forall₂_same.mpr fun x _ => .same x, trivial⟩
      | some x =>
          obtain ⟨s, p, σ⟩ := x
          obtain rfl := siteOf?_eq_some hs
          simp only [toMatch, hs, expandWith, outputFirst, matchingBy,
            activateOut_withFacts L S P spaces atoms once, activateOut_site, List.map_filterMap,
            Option.map_map, Function.comp_def]
          exact ⟨forall₂_filterMap_map _ _ _ (fun A σ' => .fact A.2 _ σ' _ f returns) (atoms s),
            trivial⟩
  | tail callee =>
      simp only [toMatch, expandWith, outputFirst, matchingBy,
        activateOut_withFacts L S P spaces atoms once]
      exact ⟨List.forall₂_same.mpr fun x _ => .same x, trivial⟩

end Expansion

/-! ## Runs -/

section Runs

variable {Term Store Rel Sp Op : Type} (L : TemplateLanguage Term) (S : StoreAlgebra Term Store Op)
variable [DecidableEq Rel] [DecidableEq Sp] [Inhabited Term]
variable (P : EqProgram L (Rel ⊕ Sp) Op) (spaces : List Sp) (atoms : Sp → List (Atom L))

theorem embeds_of_forall₂ {α β : Type} {R : α → β → Prop} {D : α → Prop} :
    ∀ {as : List α} {bs : List β}, List.Forall₂ R as bs → Embeds R D as bs
  | _, _, .nil => .nil
  | _, _, .cons r rest => .keep r (embeds_of_forall₂ rest)

omit [DecidableEq Rel] [DecidableEq Sp] in
/-- Every state corresponds to itself, in both directions. -/
theorem simulates_same
    (s : State Unit (DestControl L (Rel ⊕ Sp) Op Store) (DestFrame L (Rel ⊕ Sp) Op)
      (Answer Term Store)) :
    Simulates (Resumes L) (fun _ => False) (· = ·) s s ∧
      Simulates (fun a b => Resumes L b a) (fun _ => False) (· = ·) s s :=
  ⟨⟨embeds_of_forall₂ (List.forall₂_same.mpr fun t _ => .same t),
      List.forall₂_same.mpr fun _ _ => rfl⟩,
    ⟨embeds_of_forall₂ (List.forall₂_same.mpr fun t _ => .same t),
      List.forall₂_same.mpr fun _ _ => rfl⟩⟩

/-- **The run with match steps follows the translated run.**  After `n` steps of
the output-first machine on the translated program, the machine with match
steps has taken some number of steps, and the two states still correspond: the
frontiers task by task (`Resumes`), the answers delivered so far equal. -/
theorem matching_follows (once : ∀ s, spaces.count s = 1) (n : ℕ)
    {s₁ s₂ : State Unit (DestControl L (Rel ⊕ Sp) Op Store) (DestFrame L (Rel ⊕ Sp) Op)
      (Answer Term Store)}
    (start : Simulates (Resumes L) (fun _ => False) (· = ·) s₁ s₂) :
    ∃ n', Simulates (Resumes L) (fun _ => False) (· = ·)
      (repeats (step (outputFirst L S (withFacts L P spaces atoms))) n s₁)
      (repeats (step (matching L S P atoms)) n' s₂) := by
  refine simulates_repeats_stutter _ _ (fun _ => True) ?_ (fun _ absurd => absurd.elim) n s₁ s₂
    start (fun _ _ _ _ => trivial)
  intro a b related _
  match related with
  | .same t =>
      obtain ⟨tasks, answers⟩ := expand_related L S P spaces atoms once t
      refine ⟨_, _, .one t, embeds_of_forall₂ tasks, ?_⟩
      rw [answers]
      exact List.forall₂_same.mpr fun _ _ => rfl
  | .fact A frame σ dest f returns =>
      refine ⟨_, [], .stay _, ?_, ?_⟩
      · rw [expand_fact]
        exact .keep (.same _) .nil
      · rw [expand_fact]
        exact .nil

/-- **The translated run follows the run with match steps.**  Each match step is
matched by the call of the space's relation; each continuation the match step
starts is matched by the fact's return into it, then the same step. -/
theorem translated_follows (once : ∀ s, spaces.count s = 1) (n : ℕ)
    {s₁ s₂ : State Unit (DestControl L (Rel ⊕ Sp) Op Store) (DestFrame L (Rel ⊕ Sp) Op)
      (Answer Term Store)}
    (start : Simulates (fun a b => Resumes L b a) (fun _ => False) (· = ·) s₁ s₂) :
    ∃ n', Simulates (fun a b => Resumes L b a) (fun _ => False) (· = ·)
      (repeats (step (matching L S P atoms)) n s₁)
      (repeats (step (outputFirst L S (withFacts L P spaces atoms))) n' s₂) := by
  refine simulates_repeats_stutter _ _ (fun _ => True) ?_ (fun _ absurd => absurd.elim) n s₁ s₂
    start (fun _ _ _ _ => trivial)
  intro a b related _
  match related with
  | .same t =>
      obtain ⟨tasks, answers⟩ := expand_related L S P spaces atoms once t
      refine ⟨_, _, .one t, embeds_of_forall₂ (List.Forall₂.flip tasks), ?_⟩
      rw [← answers]
      exact List.forall₂_same.mpr fun _ _ => rfl
  | .fact A frame σ dest f returns =>
      obtain ⟨tasks, answers⟩ := expand_related L S P spaces atoms once
        ⟨(), ⟨⟨f.slots, f.body, reconstruct f.captured, σ⟩, f.dest⟩, returns⟩
      refine ⟨_, _, .stutter (expand_fact L S _ A frame σ dest f returns) (.one _),
        embeds_of_forall₂ (List.Forall₂.flip tasks), ?_⟩
      rw [← answers]
      exact List.forall₂_same.mpr fun _ _ => rfl

/-- **Match steps deliver the translated program's answers**, in order: every
answer list the translated run has delivered, the run with match steps delivers
too. -/
theorem matching_answers (once : ∀ s, spaces.count s = 1)
    (s : State Unit (DestControl L (Rel ⊕ Sp) Op Store) (DestFrame L (Rel ⊕ Sp) Op)
      (Answer Term Store)) (n : ℕ) :
    ∃ n', (repeats (step (outputFirst L S (withFacts L P spaces atoms))) n s).emitted =
      (repeats (step (matching L S P atoms)) n' s).emitted := by
  obtain ⟨n', _, answers⟩ := matching_follows L S P spaces atoms once n (simulates_same L s).1
  exact ⟨n', by rwa [List.forall₂_eq_eq_eq] at answers⟩

/-- Conversely, every answer list the run with match steps has delivered, the
translated run delivers too. -/
theorem translated_answers (once : ∀ s, spaces.count s = 1)
    (s : State Unit (DestControl L (Rel ⊕ Sp) Op Store) (DestFrame L (Rel ⊕ Sp) Op)
      (Answer Term Store)) (n : ℕ) :
    ∃ n', (repeats (step (matching L S P atoms)) n s).emitted =
      (repeats (step (outputFirst L S (withFacts L P spaces atoms))) n' s).emitted := by
  obtain ⟨n', _, answers⟩ := translated_follows L S P spaces atoms once n (simulates_same L s).2
  exact ⟨n', by rwa [List.forall₂_eq_eq_eq] at answers⟩

/-- When the translated run exhausts its frontier, so does the run with match
steps, having delivered the same answers. -/
theorem matching_terminates (once : ∀ s, spaces.count s = 1)
    (s : State Unit (DestControl L (Rel ⊕ Sp) Op Store) (DestFrame L (Rel ⊕ Sp) Op)
      (Answer Term Store)) (n : ℕ)
    (done : (repeats (step (outputFirst L S (withFacts L P spaces atoms))) n s).frontier = []) :
    ∃ n', (repeats (step (matching L S P atoms)) n' s).frontier = [] ∧
      (repeats (step (outputFirst L S (withFacts L P spaces atoms))) n s).emitted =
        (repeats (step (matching L S P atoms)) n' s).emitted := by
  obtain ⟨n', embeds, answers⟩ :=
    matching_follows L S P spaces atoms once n (simulates_same L s).1
  rw [done] at embeds
  exact ⟨n', embeds.eq_nil, by rwa [List.forall₂_eq_eq_eq] at answers⟩

/-- When the run with match steps exhausts its frontier, so does the translated
run, having delivered the same answers. -/
theorem translated_terminates (once : ∀ s, spaces.count s = 1)
    (s : State Unit (DestControl L (Rel ⊕ Sp) Op Store) (DestFrame L (Rel ⊕ Sp) Op)
      (Answer Term Store)) (n : ℕ)
    (done : (repeats (step (matching L S P atoms)) n s).frontier = []) :
    ∃ n', (repeats (step (outputFirst L S (withFacts L P spaces atoms))) n' s).frontier = [] ∧
      (repeats (step (matching L S P atoms)) n s).emitted =
        (repeats (step (outputFirst L S (withFacts L P spaces atoms))) n' s).emitted := by
  obtain ⟨n', embeds, answers⟩ :=
    translated_follows L S P spaces atoms once n (simulates_same L s).2
  rw [done] at embeds
  exact ⟨n', embeds.eq_nil, by rwa [List.forall₂_eq_eq_eq] at answers⟩

/-- **The same termination.**  The translated run exhausts its frontier exactly
when the run with match steps does. -/
theorem terminates_iff (once : ∀ s, spaces.count s = 1)
    (s : State Unit (DestControl L (Rel ⊕ Sp) Op Store) (DestFrame L (Rel ⊕ Sp) Op)
      (Answer Term Store)) :
    (∃ n, (repeats (step (outputFirst L S (withFacts L P spaces atoms))) n s).frontier = []) ↔
      ∃ n, (repeats (step (matching L S P atoms)) n s).frontier = [] :=
  ⟨fun ⟨n, done⟩ => let ⟨n', done', _⟩ := matching_terminates L S P spaces atoms once s n done
      ⟨n', done'⟩,
    fun ⟨n, done⟩ => let ⟨n', done', _⟩ := translated_terminates L S P spaces atoms once s n done
      ⟨n', done'⟩⟩

end Runs

/-! ## One fact, one candidate -/

section Candidate

variable {Term Store Op : Type} (L : TemplateLanguage Term) (S : StoreAlgebra Term Store Op)

/-- Extended by its exposed output, the fact's head is the atom. -/
theorem withOutput_fact {R : Type} (A : Atom L) :
    Equation.withOutput L (fact (R := R) (Op := Op) L A) = ⟨A.1, [A.2], .ret A.2⟩ := rfl

/-- **Activating a fact with the atom as its head is the candidate step.**  Against
the argument `p`, the fact of `A` allocates `A`'s variables and unifies the fresh
copy with `p`: it is activated exactly when the candidate step accepts, in the
store the candidate step produces, on the fresh frame. -/
theorem activate_fact {R : Type} [DecidableEq R] (m : R) (A : Atom L) (p : Term) (σ : Store) :
    activate L S [(m, Equation.withOutput L (fact L A))] (m, [p], σ) =
      ((candidate S A p σ).map fun σ' =>
        (⟨A.1, (S.fresh σ A.1).1, σ', .ret A.2⟩ : Activation L R Op Store)).toList := by
  have head : unifyAll S (instArgs L [A.2] (S.fresh σ A.1).1) [p] (S.fresh σ A.1).2 =
      candidate S A p σ := by
    simp only [instArgs, List.map_cons, List.map_nil, unifyAll, candidate]
    cases S.unify (L.inst A.2 (S.fresh σ A.1).1) p (S.fresh σ A.1).2 <;> rfl
  simp only [activate, EqProgram.equations, List.filter_cons, decide_true, ↓reduceIte,
    List.filter_nil, List.map_cons, List.map_nil, withOutput_fact, List.filterMap_cons,
    List.filterMap_nil]
  rw [head]
  cases candidate S A p σ <;> rfl

/-- The output-first activation of a fact against the destination `p` is the
activation of the fact extended by its exposed output, whose head is the atom,
against the argument `p`. -/
theorem activateOut_fact {R : Type} [DecidableEq R] (m : R) (A : Atom L) (p : Term) (σ : Store) :
    activateOut L S [(m, fact L A)] (m, [], σ, some p) =
      (activate L S [(m, Equation.withOutput L (fact L A))] (m, [p], σ)).map
        fun a => ⟨⟨a.slots, a.code, a.frame, a.store⟩, some p⟩ :=
  activateOut_withOutputs S L [(m, fact L A)] m [] p σ fun e member => by
    simp only [EqProgram.equations, List.filter_cons, decide_true, ↓reduceIte, List.filter_nil,
      List.map_cons, List.map_nil, List.mem_singleton] at member
    subst member
    rfl

variable {L S}

/-- **The candidate step is exact.**  In a well-formed store, it succeeds exactly
when some solution of the store solves `p = A'` for the fresh copy `A'`; its
store then denotes exactly those solutions, is well formed, and has the supply
after allocating `A`'s variables. -/
theorem candidate_exact (X : ExactStore S) (A : Atom L) (p : Term) {σ : Store}
    (good : X.WellFormed σ) :
    (∀ σ', candidate S A p σ = some σ' →
      X.solutions σ' = X.solutions σ ∩ {v | X.solves v p (L.inst A.2 (S.fresh σ A.1).1)} ∧
        X.supply σ' = X.supply (S.fresh σ A.1).2 ∧ X.WellFormed σ') ∧
    (candidate S A p σ = none ↔
      X.solutions σ ∩ {v | X.solves v p (L.inst A.2 (S.fresh σ A.1).1)} = ∅) := by
  have fresh := X.fresh_wellFormed A.1 good
  have sols := X.fresh_solutions σ A.1
  have swap : {v | X.solves v (L.inst A.2 (S.fresh σ A.1).1) p} =
      {v | X.solves v p (L.inst A.2 (S.fresh σ A.1).1)} :=
    Set.ext fun v => X.solves_comm v _ _
  refine ⟨fun σ' accepted => ?_, ?_⟩
  · refine ⟨?_, X.unify_supply accepted, X.unify_wellFormed fresh accepted⟩
    rw [X.unify_some fresh accepted, sols, swap]
  · unfold candidate
    rw [X.unify_eq_none_iff fresh, sols, swap]

/-- **Either orientation.**  Unifying the pattern with the fresh atom, as the C
does, succeeds exactly when the candidate step does, and the two stores give
corresponding answers: the same solutions and the same supply. -/
theorem candidate_symm (X : ExactStore S) (A : Atom L) (p : Term) {σ : Store}
    (good : X.WellFormed σ) :
    ((candidate S A p σ).isSome ↔
        (S.unify p (L.inst A.2 (S.fresh σ A.1).1) (S.fresh σ A.1).2).isSome) ∧
      ∀ σ₁ σ₂, candidate S A p σ = some σ₁ →
        S.unify p (L.inst A.2 (S.fresh σ A.1).1) (S.fresh σ A.1).2 = some σ₂ →
          ∀ v : Term, SameAnswer X ((), (v, σ₁)) ((), (v, σ₂)) := by
  have fresh := X.fresh_wellFormed A.1 good
  have sols := X.fresh_solutions σ A.1
  obtain ⟨accept, reject⟩ := candidate_exact X A p good
  have rejectC : S.unify p (L.inst A.2 (S.fresh σ A.1).1) (S.fresh σ A.1).2 = none ↔
      X.solutions σ ∩ {v | X.solves v p (L.inst A.2 (S.fresh σ A.1).1)} = ∅ := by
    rw [X.unify_eq_none_iff fresh, sols]
  refine ⟨?_, fun σ₁ σ₂ first second v => ?_⟩
  · rw [← Bool.not_eq_false, ← Bool.not_eq_false (Option.isSome _), Option.isSome_eq_false_iff,
      Option.isSome_eq_false_iff, Option.isNone_iff_eq_none, Option.isNone_iff_eq_none, reject,
      rejectC]
  · obtain ⟨sols₁, supply₁, good₁⟩ := accept σ₁ first
    refine ⟨rfl, ?_, ?_, good₁, X.unify_wellFormed fresh second⟩
    · rw [sols₁, X.unify_some fresh second, sols]
    · rw [supply₁, X.unify_supply second]

/-- **Activating one fact is two-sided unification of the argument with a fresh
copy of the atom**, up to the store's solutions: the activation exists exactly
when unifying `p` with the fresh copy succeeds, and its store then gives the
same answers, with the same solutions and supply. -/
theorem activate_fact_exact (X : ExactStore S) {R : Type} [DecidableEq R] (m : R) (A : Atom L)
    (p : Term) {σ : Store} (good : X.WellFormed σ) :
    (activate L S [(m, Equation.withOutput L (fact L A))] (m, [p], σ) = [] ↔
        S.unify p (L.inst A.2 (S.fresh σ A.1).1) (S.fresh σ A.1).2 = none) ∧
      ∀ σ₂, S.unify p (L.inst A.2 (S.fresh σ A.1).1) (S.fresh σ A.1).2 = some σ₂ →
        ∃ σ₁, activate L S [(m, Equation.withOutput L (fact L A))] (m, [p], σ) =
            [⟨A.1, (S.fresh σ A.1).1, σ₁, .ret A.2⟩] ∧
          ∀ v : Term, SameAnswer X ((), (v, σ₁)) ((), (v, σ₂)) := by
  obtain ⟨same, answers⟩ := candidate_symm X A p good
  rw [activate_fact]
  refine ⟨?_, fun σ₂ second => ?_⟩
  · cases hc : candidate S A p σ with
    | none =>
        simp only [Option.map_none, Option.toList_none, true_iff]
        rw [hc] at same
        cases hu : S.unify p (L.inst A.2 (S.fresh σ A.1).1) (S.fresh σ A.1).2 with
        | none => rfl
        | some _ => rw [hu] at same; simp at same
    | some σ₁ =>
        simp only [Option.map_some, Option.toList_some, reduceCtorEq, false_iff]
        rw [hc] at same
        intro hu
        rw [hu] at same
        simp at same
  · cases hc : candidate S A p σ with
    | none =>
        rw [hc, second] at same
        simp at same
    | some σ₁ => exact ⟨σ₁, rfl, answers σ₁ σ₂ hc second⟩

end Candidate

/-! ## Where a match step continues -/

section Site

variable {Term Store Rel Sp Op : Type} (L : TemplateLanguage Term) (S : StoreAlgebra Term Store Op)

theorem toMatch_site
    {i : Instruction (DestCall Term Store (Rel ⊕ Sp)) (DestFrame L (Rel ⊕ Sp) Op)
      (Answer Term Store)}
    {s : Sp} {p : Term} {σ : Store} {f : DestFrame L (Rel ⊕ Sp) Op}
    (h : toMatch L i = .tail (.site s p σ f)) : i = .call (.inr s, [], σ, some p) f := by
  cases i with
  | ret a => simp [toMatch] at h
  | fail => simp [toMatch] at h
  | call c g =>
      cases hs : siteOf? c with
      | none => simp [toMatch, hs] at h
      | some x =>
          obtain ⟨s', p', σ'⟩ := x
          simp only [toMatch, hs, Instruction.tail.injEq, MatchCall.site.injEq] at h
          obtain ⟨rfl, rfl, rfl, rfl⟩ := h
          rw [siteOf?_eq_some hs]
  | tail c => simp [toMatch] at h

/-- **A match step continues in its own activation.**  When a control reaches a
match site, the site is one of its code's resume sites `(P, T)`; the choice
carries `P` instantiated in the control's frame, once, before any candidate;
and every candidate continues `T` with the control's destination, on the
control's frame restricted to the slots `P` and `T` read
(`reconstruct_capture`). -/
theorem inspectOut_site {k : Nat} (frame : Fin k → Term) (dest : Option Term) :
    ∀ (σ : Store) (code : Code L (Rel ⊕ Sp) Op k) {s : Sp} {p : Term} {σ' : Store}
      {f : DestFrame L (Rel ⊕ Sp) Op},
      toMatch L (inspectOut L S frame dest σ code) = .tail (.site s p σ' f) →
      ∃ (pattern : L.Tmpl k) (body : Code L (Rel ⊕ Sp) Op k),
        (pattern, body) ∈ code.sites ∧ p = L.inst pattern frame ∧
          f = ⟨⟨k, pattern, body, capture frame (frameSupport L pattern body)⟩, dest⟩ := by
  intro σ code
  induction code generalizing σ with
  | ret t => intro s p σ' f h; simp [inspectOut, toMatch] at h
  | fail => intro s p σ' f h; simp [inspectOut, toMatch] at h
  | letCall q rel args body _ =>
      intro s p σ' f h
      have hc := toMatch_site L h
      simp only [inspectOut, Instruction.call.injEq, Prod.mk.injEq] at hc
      obtain ⟨⟨-, -, -, hp⟩, rfl⟩ := hc
      exact ⟨q, body, by simp [Code.sites], (Option.some.inj hp).symm, rfl⟩
  | letPrim q op args body ih =>
      intro s p σ' f h
      simp only [inspectOut] at h
      split at h
      · simp [toMatch] at h
      · split at h
        · obtain ⟨pattern, b, mem, hp, hf⟩ := ih _ h
          exact ⟨pattern, b, by simpa [Code.sites] using mem, hp, hf⟩
        · simp [toMatch] at h
  | bind q v body ih =>
      intro s p σ' f h
      simp only [inspectOut] at h
      split at h
      · obtain ⟨pattern, b, mem, hp, hf⟩ := ih _ h
        exact ⟨pattern, b, by simpa [Code.sites] using mem, hp, hf⟩
      · simp [toMatch] at h
  | ite op args yes no ihYes ihNo =>
      intro s p σ' f h
      simp only [inspectOut] at h
      split at h
      · split at h
        · obtain ⟨pattern, b, mem, hp, hf⟩ := ihYes _ h
          exact ⟨pattern, b, by simp [Code.sites, mem], hp, hf⟩
        · simp [toMatch] at h
      · split at h
        · obtain ⟨pattern, b, mem, hp, hf⟩ := ihNo _ h
          exact ⟨pattern, b, by simp [Code.sites, mem], hp, hf⟩
        · simp [toMatch] at h
      · simp [toMatch] at h
  | tail rel args => intro s p σ' f h; simp [inspectOut, toMatch] at h

end Site

/-! ## The output-first laws for programs with match steps -/

section OutputFirst

variable {Term Store Rel Sp Op : Type} (L : TemplateLanguage Term) {S : StoreAlgebra Term Store Op}
variable (X : ExactStore S) [DecidableEq Rel] [DecidableEq Sp] [Inhabited Term]
variable (spaces : List Sp) (atoms : Sp → List (Atom L))

theorem forall₂_filter {α β : Type} {Q : α → β → Prop} {p : α → Bool} {p' : β → Bool}
    (same : ∀ a b, Q a b → p a = p' b) :
    ∀ {l : List α} {l' : List β}, List.Forall₂ Q l l' → List.Forall₂ Q (l.filter p) (l'.filter p')
  | _, _, .nil => .nil
  | a :: _, b :: _, .cons q rest => by
      rw [List.filter_cons, List.filter_cons, same a b q]
      split
      · exact .cons q (forall₂_filter same rest)
      · exact forall₂_filter same rest

omit [DecidableEq Rel] [DecidableEq Sp] [Inhabited Term] in
/-- Adding the same facts keeps two programs aligned. -/
theorem withFacts_bindsAhead {PA PF : EqProgram L (Rel ⊕ Sp) Op}
    (aligned : ProgramBindsAhead L PA PF) :
    ProgramBindsAhead L (withFacts L PA spaces atoms) (withFacts L PF spaces atoms) := by
  unfold ProgramBindsAhead withFacts
  refine List.rel_append (forall₂_filter (fun a f h => by rw [h.1]) aligned) ?_
  refine List.forall₂_same.mpr fun e mem => ⟨rfl, ?_⟩
  simp only [List.mem_flatMap, spaceFacts, List.mem_map] at mem
  obtain ⟨s, -, A, -, rfl⟩ := mem
  exact .mk [] (BindsAhead.refl (.ret A.2))

/-- **The prefix law with match steps.**  For programs aligned by
`ProgramBindsAhead`, from corresponding states and on a moded reference run:
every answer list the output-at-return machine has delivered on the program with
its facts, the machine with match steps has delivered too, answer for answer. -/
theorem matching_refines (once : ∀ s, spaces.count s = 1) {PA PF : EqProgram L (Rel ⊕ Sp) Op}
    (aligned : ProgramBindsAhead L PA PF)
    {sA : State Unit (Control L (Rel ⊕ Sp) Op Store) (ReturnFrame L (Rel ⊕ Sp) Op)
      (Answer Term Store)}
    {sF : State Unit (DestControl L (Rel ⊕ Sp) Op Store) (DestFrame L (Rel ⊕ Sp) Op)
      (Answer Term Store)}
    (start : Simulates (Related L X) (Doomed L X) (SameAnswer X) sA sF)
    (moded : ∀ m, ∀ t ∈ (repeats (step (compiled L S (withFacts L PA spaces atoms))) m sA).frontier,
      Moded L X t)
    (n : ℕ) :
    ∃ n', List.Forall₂ (SameAnswer X)
      (repeats (step (compiled L S (withFacts L PA spaces atoms))) n sA).emitted
      (repeats (step (matching L S PF atoms)) n' sF).emitted := by
  obtain ⟨n₁, -, answers⟩ :=
    outputFirst_answers X (withFacts_bindsAhead L spaces atoms aligned) start moded n
  obtain ⟨n', same⟩ := matching_answers L S PF spaces atoms once sF n₁
  exact ⟨n', same ▸ answers⟩

/-- **Termination with match steps.**  When the reference run exhausts its
frontier, so does the run with match steps, with corresponding answers in the
same order. -/
theorem matching_refines_terminates (once : ∀ s, spaces.count s = 1)
    {PA PF : EqProgram L (Rel ⊕ Sp) Op} (aligned : ProgramBindsAhead L PA PF)
    {sA : State Unit (Control L (Rel ⊕ Sp) Op Store) (ReturnFrame L (Rel ⊕ Sp) Op)
      (Answer Term Store)}
    {sF : State Unit (DestControl L (Rel ⊕ Sp) Op Store) (DestFrame L (Rel ⊕ Sp) Op)
      (Answer Term Store)}
    (start : Simulates (Related L X) (Doomed L X) (SameAnswer X) sA sF)
    (moded : ∀ m, ∀ t ∈ (repeats (step (compiled L S (withFacts L PA spaces atoms))) m sA).frontier,
      Moded L X t)
    (n : ℕ) (done : (repeats (step (compiled L S (withFacts L PA spaces atoms))) n sA).frontier = []) :
    ∃ n', (repeats (step (matching L S PF atoms)) n' sF).frontier = [] ∧
      List.Forall₂ (SameAnswer X)
        (repeats (step (compiled L S (withFacts L PA spaces atoms))) n sA).emitted
        (repeats (step (matching L S PF atoms)) n' sF).emitted := by
  obtain ⟨n₁, -, done₁, answers⟩ :=
    outputFirst_terminates X (withFacts_bindsAhead L spaces atoms aligned) start moded n done
  obtain ⟨n', done', same⟩ := matching_terminates L S PF spaces atoms once sF n₁ done₁
  exact ⟨n', done', same ▸ answers⟩

omit [DecidableEq Rel] [DecidableEq Sp] [Inhabited Term] in
/-- A source match site `(let P (m) T)` normalizes to the match site, both ways. -/
theorem norm_sourceMatchSite {k : Nat} (s : Sp) (pattern : L.Tmpl k)
    (continuation : Source L (Rel ⊕ Sp) Op k) :
    norm L (sourceMatchSite L s pattern continuation) = matchSite L s pattern (norm L continuation) ∧
      normFirst L (sourceMatchSite L s pattern continuation) =
        matchSite L s pattern (normFirst L continuation) :=
  ⟨rfl, rfl⟩

/-- **Source programs with match sites.**  For a nested source program, the
machine with match steps on its output-first normalization refines the
output-at-return machine on its normalization with the facts, from a query
control. -/
theorem source_matching_answers (P : SProgram L (Rel ⊕ Sp) Op) (once : ∀ s, spaces.count s = 1)
    {k : Nat} (query : Code L (Rel ⊕ Sp) Op k) (frame : Fin k → Term) (σ : Store)
    (good : X.WellFormed σ)
    (moded : ∀ m, ∀ t ∈ (repeats (step (compiled L S (withFacts L (SProgram.normalize L P) spaces atoms)))
      m (queryState L query frame σ)).frontier, Moded L X t) (n : ℕ) :
    ∃ n', List.Forall₂ (SameAnswer X)
      (repeats (step (compiled L S (withFacts L (SProgram.normalize L P) spaces atoms))) n
        (queryState L query frame σ)).emitted
      (repeats (step (matching L S (SProgram.normalizeFirst L P) atoms)) n'
        (queryStateOut L query frame σ)).emitted :=
  matching_refines L X spaces atoms once (programBindsAhead_normalize P)
    (simulates_query X (BindsAhead.refl query) frame σ good) moded n

end OutputFirst

end Mettapedia.GSLT.LanguageDef.MatchSteps

#print axioms Mettapedia.GSLT.LanguageDef.MatchSteps.activate_fact_exact
#print axioms Mettapedia.GSLT.LanguageDef.MatchSteps.candidate_exact
#print axioms Mettapedia.GSLT.LanguageDef.MatchSteps.candidate_symm
#print axioms Mettapedia.GSLT.LanguageDef.MatchSteps.activateOut_site
#print axioms Mettapedia.GSLT.LanguageDef.MatchSteps.activateOut_fact
#print axioms Mettapedia.GSLT.LanguageDef.MatchSteps.expand_related
#print axioms Mettapedia.GSLT.LanguageDef.MatchSteps.matching_follows
#print axioms Mettapedia.GSLT.LanguageDef.MatchSteps.translated_follows
#print axioms Mettapedia.GSLT.LanguageDef.MatchSteps.matching_answers
#print axioms Mettapedia.GSLT.LanguageDef.MatchSteps.translated_answers
#print axioms Mettapedia.GSLT.LanguageDef.MatchSteps.matching_terminates
#print axioms Mettapedia.GSLT.LanguageDef.MatchSteps.translated_terminates
#print axioms Mettapedia.GSLT.LanguageDef.MatchSteps.terminates_iff
#print axioms Mettapedia.GSLT.LanguageDef.MatchSteps.inspectOut_site
#print axioms Mettapedia.GSLT.LanguageDef.MatchSteps.matching_refines
#print axioms Mettapedia.GSLT.LanguageDef.MatchSteps.matching_refines_terminates
#print axioms Mettapedia.GSLT.LanguageDef.MatchSteps.source_matching_answers
