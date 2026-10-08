import Mettapedia.GSLT.LanguageDef.TemplateScope.SpectrumTheorems

/-!
# Template scope, part 8: every option is a default plus a list

An ownership option is a **profile**: a default inference that computes, for
each region, the list of names it introduces (its owned list; the rest of the
names written in it are shared with the enclosing region, and the owned ones
are kept apart from it).  A construct's written crossing set, the names it
shares with the outside, overrides the default under every profile
(`crossOwn`): a lambda then owns every other name its region uses, and a
`let` makes every other name of its pattern fresh.  `elabWith` elaborates
under any profile and stores the lists in the term.

* `elabMS_eq`, `elabEC_eq`, `elabQ_eq`, `elabLF_eq` — the four ownership
  options of the spectrum are profiles.
* `elabWith_lam_crossing`, `elabWith_let_crossing` — **a crossing set
  overrides the default under every profile**: a lambda owns every other name
  its region uses (the explicit rule `ownRuleEC`), a `let` introduces every
  other name of its pattern.
* `elabWith_congr` / `answers_eq_of_agree` — **elaborated metadata determines
  meaning**: two profiles that store the same lists on a program elaborate it
  to the same term, hence agree on every observation (the answer bag with
  the final stores, under every readout and every program of equations).
* `elabWith_fullyWritten_profile`, `elabWith_fullyWritten_context`,
  `elabWith_allWritten_profile` — on a program whose every lambda carries a
  crossing set, the profiles whose `let`s introduce alike elaborate alike, and
  no profile reads the enclosing context; with every `let` written too, all
  profiles elaborate alike: crossing sets restore modularity.

## Lexical inventory

Introduction is separated from constraint: a region's inventory is fixed at
elaboration, and patterns inside the region only constrain resolved slots
(`letOwn = []`).  The variants differ only in how a lambda region obtains
its inventory, which is exactly the boundary rule:

* (i) implicit introduction over the declared region, apart by default,
  connected by the crossing set: `profLIi` (= explicit capture);
* (i') implicit introduction, connected by spelling: `profLIc` (= rule M);
* (ii) explicit fresh introduction: the inventory is stated on the construct.
  With one written list, the crossing set, the inventory is every used name
  outside it; with crossing sets overriding under every profile, this is any
  profile with every lambda's crossing set written; `profLIii` is the
  query-wide default it starts from;
* (iii) reference patterns that only refer: the resolution of (ii) together
  with an admission check that every pattern name is introduced somewhere,
  which changes no admitted program's meaning and is not modeled further.

`boundary_tension` restates the 4-versus-5 tension for spellings that cross
a region boundary.  For a spelling introduced by the region alone, every
rule that owns what nothing outside writes keeps it owned, and patterns in
the region constrain it implicitly; the corpus (`ListsCorpus`) checks both
properties on such names.
-/

namespace Mettapedia.GSLT.LanguageDef.TemplateScope

universe u v

variable {S : Type u} {X : Type v}

/-- A profile: the defaults of the lists a region stores.  `lamOwn body E` is
a lambda region's owned list when no crossing set is written on the lambda,
from its body text and the names quantified at enclosing regions;
`letOwn pattern cr` is the list a `let` introduces when none is written, given
the crossing names `cr` in force (empty: the `let` only constrains). -/
structure Profile (S : Type u) (X : Type v) where
  lamOwn : Src S X → List X → List X
  letOwn : Src S X → List X → List X

variable [DecidableEq X]

/-- The own list a profile stores at a lambda: by the crossing set when one is
written, else the profile's default. -/
def Profile.own (P : Profile S X) (xs : Option (List X)) (b : Src S X) (E : List X) : List X :=
  crossOwn xs (Src.uses b) (P.lamOwn b E)

/-- The names a `let` introduces under a profile: by the crossing set when one
is written, else the profile's default. -/
def Profile.letIntro (P : Profile S X) (xs : Option (List X)) (p : Src S X) (cr : List X) :
    List X :=
  crossOwn xs (Src.patNames p) (P.letOwn p cr)

/-- Elaboration under a profile, storing its lists.  Inside a lambda, every
spelling it owns or writes directly is quantified; inside a construct, its
crossing names are in force (`cr`). -/
def elabWith (P : Profile S X) (E cr : List X) (env : REnv X) (pos : Owner) :
    Src S X → Tm S (Slot X)
  | .sym s => .sym s
  | .fn F => .fn F
  | .sv y => slotVar env y
  | .par z => .pvar (parName z)
  | .lam z xs b =>
      .lam (parName z) ((P.own xs b E).map fun y => (pos ++ [0], y))
        (elabWith P (P.own xs b E ++ Src.direct b ++ E) (crossIn xs (P.own xs b E) cr)
          (env.update (P.own xs b E) (pos ++ [0])) (pos ++ [0]) b)
  | .app f a => .app (elabWith P E cr env (pos ++ [0]) f) (elabWith P E cr env (pos ++ [1]) a)
  | .quote c => .quote (codeOf c)
  | .pquote c => .pquote (sealParams (codeAt (some env) [] [] [] c))
  | .letS p w b xs =>
      match P.letIntro xs p cr with
      | [] =>
          .letP (elabWith P E (crossIn xs [] cr) env (pos ++ [0]) p)
            (elabWith P E cr env (pos ++ [1]) w)
            (elabWith P E (crossIn xs [] cr) env (pos ++ [2]) b)
      | y₀ :: ys =>
          .app
            (.lam (letParam (pos ++ [2]) y₀) ((y₀ :: ys).map fun y => (pos ++ [2], y))
              (.letP (elabWith P ((y₀ :: ys) ++ E) (crossIn xs (y₀ :: ys) cr)
                  (env.update (y₀ :: ys) (pos ++ [2])) (pos ++ [0]) p)
                (.pvar (letParam (pos ++ [2]) y₀))
                (elabWith P ((y₀ :: ys) ++ E) (crossIn xs (y₀ :: ys) cr)
                  (env.update (y₀ :: ys) (pos ++ [2])) (pos ++ [2]) b)))
            (elabWith P E cr env (pos ++ [1]) w)
  | .unify p w b =>
      .letP (elabWith P E cr env (pos ++ [0]) p) (elabWith P E cr env (pos ++ [1]) w)
        (elabWith P E cr env (pos ++ [2]) b)
  | .alt t₁ t₂ =>
      .alt (elabWith P E cr env (pos ++ [0]) t₁) (elabWith P E cr env (pos ++ [1]) t₂)
  | .new [] b => elabWith P E cr env (pos ++ [0]) b
  | .new (y₀ :: ys) b =>
      newBlock pos y₀ ys (elabWith P ((y₀ :: ys) ++ E) (cr.filter fun y => decide (y ∉ y₀ :: ys))
        (env.update (y₀ :: ys) (pos ++ [0])) (pos ++ [0]) b)
  | .form z b =>
      formedLam z (elabWith P E cr (env.update [] (pos ++ [0])) (pos ++ [0]) b)

/-! ## The options as profiles -/

/-- Query-wide: nothing is owned below the form. -/
def profQ : Profile S X := ⟨fun _ _ => [], fun _ _ => []⟩

/-- Rule M: a lambda owns what it writes directly and enclosing regions do
not quantify; `let`s constrain. -/
def profM : Profile S X := ⟨fun b E => ownRuleMDefault E b, fun _ _ => []⟩

/-- Explicit capture: a lambda owns everything its region uses; `let`s
constrain. -/
def profEC : Profile S X := ⟨fun b _ => (Src.uses b).dedup, fun _ _ => []⟩

/-- Lexical fresh: lambdas own nothing; each `let` introduces its pattern's
names, except those in force from an enclosing crossing set. -/
def profLF : Profile S X :=
  ⟨fun _ _ => [], fun p cr => ((Src.patNames p).filter fun y => decide (y ∉ cr)).dedup⟩

/-- Lexical inventory (i): implicit introduction over the lambda region,
apart by default, connected by the shared list. -/
def profLIi : Profile S X := profEC

/-- Lexical inventory (i'): implicit introduction, connected by spelling. -/
def profLIc : Profile S X := profM

/-- Lexical inventory (ii): explicit fresh introduction.  A lambda's inventory
is every name its region uses outside its crossing set, and every other name
refers outward; with no crossing set a lambda introduces nothing, which is
query-wide's default. -/
def profLIii : Profile S X := profQ

omit [DecidableEq X] in
@[simp] theorem profQ_lamOwn (b : Src S X) (E : List X) :
    (profQ : Profile S X).lamOwn b E = [] := rfl
omit [DecidableEq X] in
@[simp] theorem profQ_letOwn (p : Src S X) (cr : List X) :
    (profQ : Profile S X).letOwn p cr = [] := rfl
@[simp] theorem profM_lamOwn (b : Src S X) (E : List X) :
    (profM : Profile S X).lamOwn b E = ownRuleMDefault E b := rfl
@[simp] theorem profM_letOwn (p : Src S X) (cr : List X) :
    (profM : Profile S X).letOwn p cr = [] := rfl
@[simp] theorem profEC_lamOwn (b : Src S X) (E : List X) :
    (profEC : Profile S X).lamOwn b E = (Src.uses b).dedup := rfl
@[simp] theorem profEC_letOwn (p : Src S X) (cr : List X) :
    (profEC : Profile S X).letOwn p cr = [] := rfl
@[simp] theorem profLF_lamOwn (b : Src S X) (E : List X) :
    (profLF : Profile S X).lamOwn b E = [] := rfl
@[simp] theorem profLF_letOwn (p : Src S X) (cr : List X) :
    (profLF : Profile S X).letOwn p cr =
      ((Src.patNames p).filter fun y => decide (y ∉ cr)).dedup := rfl

theorem REnv.update_nil (env : REnv X) (o : Owner) : env.update [] o = env := by
  funext y
  simp [REnv.update]

theorem elabMS_eq : ∀ (t : Src S X) (E cr : List X) (env : REnv X) (pos : Owner),
    elabMS E env pos t = elabWith profM E cr env pos t
  | .sym _, _, _, _, _ => rfl
  | .fn _, _, _, _, _ => rfl
  | .sv _, _, _, _, _ => rfl
  | .par _, _, _, _, _ => rfl
  | .lam z xs b, E, cr, env, pos => by
      simp only [elabMS, elabWith, Profile.own, profM_lamOwn]
      congr 1
      exact elabMS_eq b _ _ _ _
  | .app f a, E, cr, env, pos => by
      simp only [elabMS, elabWith]
      rw [elabMS_eq f E cr, elabMS_eq a E cr]
  | .quote _, _, _, _, _ => rfl
  | .pquote _, _, _, _, _ => rfl
  | .letS p w b xs, E, cr, env, pos => by
      simp only [elabMS, elabWith, Profile.letIntro, profM_letOwn]
      cases crossOwn xs (Src.patNames p) [] with
      | nil =>
          rw [elabMS_eq p E (crossIn xs [] cr), elabMS_eq w E cr, elabMS_eq b E (crossIn xs [] cr)]
      | cons y₀ ys =>
          dsimp only
          rw [elabMS_eq p _ (crossIn xs (y₀ :: ys) cr), elabMS_eq w E cr,
            elabMS_eq b _ (crossIn xs (y₀ :: ys) cr)]
  | .unify p w b, E, cr, env, pos => by
      simp only [elabMS, elabWith]
      rw [elabMS_eq p E cr, elabMS_eq w E cr, elabMS_eq b E cr]
  | .alt t₁ t₂, E, cr, env, pos => by
      simp only [elabMS, elabWith]
      rw [elabMS_eq t₁ E cr, elabMS_eq t₂ E cr]
  | .new [] b, E, cr, env, pos => by
      simp only [elabMS, elabWith]
      exact elabMS_eq b E cr env _
  | .new (y₀ :: ys) b, E, cr, env, pos => by
      simp only [elabMS, elabWith]
      rw [elabMS_eq b _ (cr.filter fun y => decide (y ∉ y₀ :: ys))]
  | .form _ b, E, cr, env, pos => by
      simp only [elabMS, elabWith]
      rw [elabMS_eq b]

theorem elabEC_eq : ∀ (t : Src S X) (E cr : List X) (env : REnv X) (pos : Owner),
    elabEC env pos t = elabWith profEC E cr env pos t
  | .sym _, _, _, _, _ => rfl
  | .fn _, _, _, _, _ => rfl
  | .sv _, _, _, _, _ => rfl
  | .par _, _, _, _, _ => rfl
  | .lam z xs b, E, cr, env, pos => by
      simp only [elabEC, elabWith, Profile.own, profEC_lamOwn]
      congr 1
      exact elabEC_eq b _ _ _ _
  | .app f a, E, cr, env, pos => by
      simp only [elabEC, elabWith]
      rw [elabEC_eq f E cr, elabEC_eq a E cr]
  | .quote _, _, _, _, _ => rfl
  | .pquote _, _, _, _, _ => rfl
  | .letS p w b xs, E, cr, env, pos => by
      simp only [elabEC, elabWith, Profile.letIntro, profEC_letOwn]
      cases crossOwn xs (Src.patNames p) [] with
      | nil =>
          rw [elabEC_eq p E (crossIn xs [] cr), elabEC_eq w E cr, elabEC_eq b E (crossIn xs [] cr)]
      | cons y₀ ys =>
          dsimp only
          rw [elabEC_eq p (y₀ :: ys ++ E) (crossIn xs (y₀ :: ys) cr), elabEC_eq w E cr,
            elabEC_eq b (y₀ :: ys ++ E) (crossIn xs (y₀ :: ys) cr)]
  | .unify p w b, E, cr, env, pos => by
      simp only [elabEC, elabWith]
      rw [elabEC_eq p E cr, elabEC_eq w E cr, elabEC_eq b E cr]
  | .alt t₁ t₂, E, cr, env, pos => by
      simp only [elabEC, elabWith]
      rw [elabEC_eq t₁ E cr, elabEC_eq t₂ E cr]
  | .new [] b, E, cr, env, pos => by
      simp only [elabEC, elabWith]
      exact elabEC_eq b E cr env _
  | .new (y₀ :: ys) b, E, cr, env, pos => by
      simp only [elabEC, elabWith]
      rw [elabEC_eq b ((y₀ :: ys) ++ E) (cr.filter fun y => decide (y ∉ y₀ :: ys))]
  | .form _ b, E, cr, env, pos => by
      simp only [elabEC, elabWith]
      rw [elabEC_eq b]

theorem elabQ_eq : ∀ (t : Src S X) (E cr : List X) (env : REnv X) (pos : Owner),
    elabQ env pos t = elabWith profQ E cr env pos t
  | .sym _, _, _, _, _ => rfl
  | .fn _, _, _, _, _ => rfl
  | .sv _, _, _, _, _ => rfl
  | .par _, _, _, _, _ => rfl
  | .lam z xs b, E, cr, env, pos => by
      simp only [elabQ, elabWith, Profile.own, profQ_lamOwn]
      congr 1
      exact elabQ_eq b _ _ _ _
  | .app f a, E, cr, env, pos => by
      simp only [elabQ, elabWith]
      rw [elabQ_eq f E cr, elabQ_eq a E cr]
  | .quote _, _, _, _, _ => rfl
  | .pquote _, _, _, _, _ => rfl
  | .letS p w b xs, E, cr, env, pos => by
      simp only [elabQ, elabWith, Profile.letIntro, profQ_letOwn]
      cases crossOwn xs (Src.patNames p) [] with
      | nil =>
          rw [elabQ_eq p E (crossIn xs [] cr), elabQ_eq w E cr, elabQ_eq b E (crossIn xs [] cr)]
      | cons y₀ ys =>
          dsimp only
          rw [elabQ_eq p (y₀ :: ys ++ E) (crossIn xs (y₀ :: ys) cr), elabQ_eq w E cr,
            elabQ_eq b (y₀ :: ys ++ E) (crossIn xs (y₀ :: ys) cr)]
  | .unify p w b, E, cr, env, pos => by
      simp only [elabQ, elabWith]
      rw [elabQ_eq p E cr, elabQ_eq w E cr, elabQ_eq b E cr]
  | .alt t₁ t₂, E, cr, env, pos => by
      simp only [elabQ, elabWith]
      rw [elabQ_eq t₁ E cr, elabQ_eq t₂ E cr]
  | .new [] b, E, cr, env, pos => by
      simp only [elabQ, elabWith]
      exact elabQ_eq b E cr env _
  | .new (y₀ :: ys) b, E, cr, env, pos => by
      simp only [elabQ, elabWith]
      rw [elabQ_eq b ((y₀ :: ys) ++ E) (cr.filter fun y => decide (y ∉ y₀ :: ys))]
  | .form _ b, E, cr, env, pos => by
      simp only [elabQ, elabWith]
      rw [elabQ_eq b]

theorem elabLF_eq : ∀ (t : Src S X) (E : List X) (env : REnv X) (cr : List X) (pos : Owner),
    elabLF env cr pos t = elabWith profLF E cr env pos t
  | .sym _, _, _, _, _ => rfl
  | .fn _, _, _, _, _ => rfl
  | .sv _, _, _, _, _ => rfl
  | .par _, _, _, _, _ => rfl
  | .lam z xs b, E, env, cr, pos => by
      simp only [elabLF, elabWith, Profile.own, profLF_lamOwn]
      congr 1
      exact elabLF_eq b _ _ _ _
  | .app f a, E, env, cr, pos => by
      simp only [elabLF, elabWith]
      rw [elabLF_eq f E, elabLF_eq a E]
  | .quote _, _, _, _, _ => rfl
  | .pquote _, _, _, _, _ => rfl
  | .letS p w b xs, E, env, cr, pos => by
      simp only [elabLF, elabWith, Profile.letIntro, profLF_letOwn, lfIntro]
      cases crossOwn xs (Src.patNames p) ((Src.patNames p).filter fun y => decide (y ∉ cr)).dedup with
      | nil => rw [elabLF_eq p E, elabLF_eq w E, elabLF_eq b E]
      | cons y₀ ys =>
          dsimp only
          rw [elabLF_eq p (y₀ :: ys ++ E), elabLF_eq w E, elabLF_eq b (y₀ :: ys ++ E)]
  | .unify p w b, E, env, cr, pos => by
      simp only [elabLF, elabWith]
      rw [elabLF_eq p E, elabLF_eq w E, elabLF_eq b E]
  | .alt t₁ t₂, E, env, cr, pos => by
      simp only [elabLF, elabWith]
      rw [elabLF_eq t₁ E, elabLF_eq t₂ E]
  | .new [] b, E, env, cr, pos => by
      simp only [elabLF, elabWith]
      exact elabLF_eq b E env cr _
  | .new (y₀ :: ys) b, E, env, cr, pos => by
      simp only [elabLF, elabWith]
      rw [elabLF_eq b ((y₀ :: ys) ++ E)]
  | .form _ b, E, env, cr, pos => by
      simp only [elabLF, elabWith]
      rw [elabLF_eq b E]

/-! ## A crossing set overrides the default under every profile -/

/-- **A lambda with a crossing set owns every other name its region uses**,
under every profile and in every context: the explicit rule `ownRuleEC`.
Inside it, its crossing names are in force. -/
theorem elabWith_lam_crossing (P : Profile S X) (E cr : List X) (env : REnv X) (pos : Owner)
    (z : X) (sh : List X) (b : Src S X) :
    elabWith P E cr env pos (.lam z (some sh) b) =
      .lam (parName z) ((ownRuleEC sh b E).map fun y => (pos ++ [0], y))
        (elabWith P (ownRuleEC sh b E ++ Src.direct b ++ E) (crossIn (some sh) (ownRuleEC sh b E) cr)
          (env.update (ownRuleEC sh b E) (pos ++ [0])) (pos ++ [0]) b) := rfl

/-- **A `let` with a crossing set makes every other name of its pattern
fresh**, under every profile and whatever is in force around it. -/
theorem elabWith_let_crossing (P : Profile S X) (sh : List X) (p : Src S X) (cr : List X) :
    P.letIntro (some sh) p cr = ((Src.patNames p).filter fun y => decide (y ∉ sh)).dedup := rfl

/-- **A name in force is never made fresh** by a `let` without a crossing
set, under lexical fresh: the crossing set of an enclosing construct shares it
with the outside instead. -/
theorem profLF_letIntro_in_force (p : Src S X) {cr : List X} {y : X} (hy : y ∈ cr) :
    y ∉ (profLF : Profile S X).letIntro none p cr := by
  simp [Profile.letIntro, profLF, List.mem_dedup, hy]

/-- With no crossing set, the profile's default decides. -/
theorem elabWith_lam_none (P : Profile S X) (E cr : List X) (env : REnv X) (pos : Owner) (z : X)
    (b : Src S X) :
    elabWith P E cr env pos (.lam z none b) =
      .lam (parName z) ((P.lamOwn b E).map fun y => (pos ++ [0], y))
        (elabWith P (P.lamOwn b E ++ Src.direct b ++ E) (crossIn none (P.lamOwn b E) cr)
          (env.update (P.lamOwn b E) (pos ++ [0])) (pos ++ [0]) b) := rfl

/-! ## Elaborated metadata determines meaning -/

/-- Whether two profiles store the same lists on a program: at every lambda
and every `let` met during elaboration (with the scope and the crossing names
then in force). -/
def agree (P₁ P₂ : Profile S X) : List X → List X → Src S X → Bool
  | E, cr, .lam _ xs b => decide (P₁.own xs b E = P₂.own xs b E) &&
      agree P₁ P₂ (P₁.own xs b E ++ Src.direct b ++ E) (crossIn xs (P₁.own xs b E) cr) b
  | E, cr, .app f a => agree P₁ P₂ E cr f && agree P₁ P₂ E cr a
  | E, cr, .pquote c => agree P₁ P₂ E cr c
  | E, cr, .letS p w b xs => decide (P₁.letIntro xs p cr = P₂.letIntro xs p cr) &&
      agree P₁ P₂ (P₁.letIntro xs p cr ++ E) (crossIn xs (P₁.letIntro xs p cr) cr) p &&
      agree P₁ P₂ E cr w &&
      agree P₁ P₂ (P₁.letIntro xs p cr ++ E) (crossIn xs (P₁.letIntro xs p cr) cr) b
  | E, cr, .unify p w b => agree P₁ P₂ E cr p && agree P₁ P₂ E cr w && agree P₁ P₂ E cr b
  | E, cr, .alt t₁ t₂ => agree P₁ P₂ E cr t₁ && agree P₁ P₂ E cr t₂
  | E, cr, .new [] b => agree P₁ P₂ E cr b
  | E, cr, .new (y₀ :: ys) b =>
      agree P₁ P₂ ((y₀ :: ys) ++ E) (cr.filter fun y => decide (y ∉ y₀ :: ys)) b
  | E, cr, .form _ b => agree P₁ P₂ E cr b
  | _, _, .sym _ => true
  | _, _, .fn _ => true
  | _, _, .sv _ => true
  | _, _, .par _ => true
  | _, _, .quote _ => true

/-- **Elaborated metadata determines meaning, at elaboration.**  Profiles that
store the same lists on a program elaborate it to the same term. -/
theorem elabWith_congr (P₁ P₂ : Profile S X) :
    ∀ (t : Src S X) (E cr : List X) (env : REnv X) (pos : Owner), agree P₁ P₂ E cr t = true →
      elabWith P₁ E cr env pos t = elabWith P₂ E cr env pos t
  | .sym _, _, _, _, _, _ => rfl
  | .fn _, _, _, _, _, _ => rfl
  | .sv _, _, _, _, _, _ => rfl
  | .par _, _, _, _, _, _ => rfl
  | .lam z xs b, E, cr, env, pos, h => by
      simp only [agree, Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨hown, hb⟩ := h
      simp only [elabWith]
      rw [← hown, elabWith_congr P₁ P₂ b _ _ _ _ hb]
  | .app f a, E, cr, env, pos, h => by
      simp only [agree, Bool.and_eq_true] at h
      simp only [elabWith]
      rw [elabWith_congr P₁ P₂ f E cr env _ h.1, elabWith_congr P₁ P₂ a E cr env _ h.2]
  | .quote _, _, _, _, _, _ => rfl
  | .pquote _, _, _, _, _, _ => rfl
  | .letS p w b xs, E, cr, env, pos, h => by
      simp only [agree, Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨⟨⟨hown, hp⟩, hw⟩, hb⟩ := h
      simp only [elabWith]
      rw [← hown]
      split
      · next hnil =>
          rw [hnil] at hp hb
          rw [elabWith_congr P₁ P₂ p E _ env _ hp, elabWith_congr P₁ P₂ w E cr env _ hw,
            elabWith_congr P₁ P₂ b E _ env _ hb]
      · next y₀ ys hcons =>
          rw [hcons] at hp hb
          rw [elabWith_congr P₁ P₂ p _ _ _ _ hp, elabWith_congr P₁ P₂ b _ _ _ _ hb,
            elabWith_congr P₁ P₂ w E cr env _ hw]
  | .unify p w b, E, cr, env, pos, h => by
      simp only [agree, Bool.and_eq_true] at h
      simp only [elabWith]
      rw [elabWith_congr P₁ P₂ p E cr env _ h.1.1, elabWith_congr P₁ P₂ w E cr env _ h.1.2,
        elabWith_congr P₁ P₂ b E cr env _ h.2]
  | .alt t₁ t₂, E, cr, env, pos, h => by
      simp only [agree, Bool.and_eq_true] at h
      simp only [elabWith]
      rw [elabWith_congr P₁ P₂ t₁ E cr env _ h.1, elabWith_congr P₁ P₂ t₂ E cr env _ h.2]
  | .new [] b, E, cr, env, pos, h => by
      simp only [agree] at h
      simp only [elabWith]
      rw [elabWith_congr P₁ P₂ b E cr env _ h]
  | .new (y₀ :: ys) b, E, cr, env, pos, h => by
      simp only [agree] at h
      simp only [elabWith]
      rw [elabWith_congr P₁ P₂ b _ _ _ _ h]
  | .form _ b, E, cr, env, pos, h => by
      simp only [agree] at h
      simp only [elabWith]
      rw [elabWith_congr P₁ P₂ b E cr (env.update [] (pos ++ [0])) _ h]

/-- **Elaborated metadata determines meaning.**  Profiles that store the same
lists on a query have the same observation under every readout and every
program of equations: the evaluator reads the stored lists, never the
profile. -/
theorem answers_eq_of_agree [DecidableEq S] (P₁ P₂ : Profile S X) (t : Src S X)
    (E cr : List X) (env : REnv X) (pos : Owner) (h : agree P₁ P₂ E cr t = true) (d : Disc)
    (prog : S → Option (Tm S (Slot X))) (n : ℕ) :
    answers d prog n (elabWith P₁ E cr env pos t) =
      answers d prog n (elabWith P₂ E cr env pos t) := by
  rw [elabWith_congr P₁ P₂ t E cr env pos h]

/-! ## Fully written programs -/

/-- Every lambda carries a crossing set (sealed code is not elaborated). -/
def Src.FullyWritten : Src S X → Bool
  | .lam _ xs b => xs.isSome && FullyWritten b
  | .app f a => FullyWritten f && FullyWritten a
  | .pquote c => FullyWritten c
  | .letS p w b _ => FullyWritten p && FullyWritten w && FullyWritten b
  | .unify p w b => FullyWritten p && FullyWritten w && FullyWritten b
  | .alt t₁ t₂ => FullyWritten t₁ && FullyWritten t₂
  | .new _ b => FullyWritten b
  | .form _ b => FullyWritten b
  | _ => true

/-- Every lambda and every `let` carries a crossing set. -/
def Src.AllWritten : Src S X → Bool
  | .lam _ xs b => xs.isSome && AllWritten b
  | .app f a => AllWritten f && AllWritten a
  | .pquote c => AllWritten c
  | .letS p w b xs => xs.isSome && AllWritten p && AllWritten w && AllWritten b
  | .unify p w b => AllWritten p && AllWritten w && AllWritten b
  | .alt t₁ t₂ => AllWritten t₁ && AllWritten t₂
  | .new _ b => AllWritten b
  | .form _ b => AllWritten b
  | _ => true

/-- **A fully written program elaborates alike under every two profiles whose
`let`s introduce alike** (by default; a written crossing set decides for
itself): rule M, explicit capture, query-wide and the lexical inventories,
whose `let`s only constrain, give the same term. -/
theorem elabWith_fullyWritten_profile (P₁ P₂ : Profile S X)
    (hlet : ∀ p cr, P₁.letOwn p cr = P₂.letOwn p cr) :
    ∀ (t : Src S X) (E cr : List X) (env : REnv X) (pos : Owner), t.FullyWritten = true →
      elabWith P₁ E cr env pos t = elabWith P₂ E cr env pos t
  | .sym _, _, _, _, _, _ => rfl
  | .fn _, _, _, _, _, _ => rfl
  | .sv _, _, _, _, _, _ => rfl
  | .par _, _, _, _, _, _ => rfl
  | .lam z xs b, E, cr, env, pos, h => by
      simp only [Src.FullyWritten, Bool.and_eq_true] at h
      have hown : P₁.own xs b E = P₂.own xs b E := crossOwn_of_isSome h.1 _ _ _
      simp only [elabWith]
      rw [← hown, elabWith_fullyWritten_profile P₁ P₂ hlet b _ _ _ _ h.2]
  | .app f a, E, cr, env, pos, h => by
      simp only [Src.FullyWritten, Bool.and_eq_true] at h
      simp only [elabWith]
      rw [elabWith_fullyWritten_profile P₁ P₂ hlet f E cr env _ h.1,
        elabWith_fullyWritten_profile P₁ P₂ hlet a E cr env _ h.2]
  | .quote _, _, _, _, _, _ => rfl
  | .pquote _, _, _, _, _, _ => rfl
  | .letS p w b xs, E, cr, env, pos, h => by
      simp only [Src.FullyWritten, Bool.and_eq_true] at h
      have hi : P₁.letIntro xs p cr = P₂.letIntro xs p cr := by
        simp [Profile.letIntro, hlet p cr]
      simp only [elabWith]
      rw [← hi]
      split
      · rw [elabWith_fullyWritten_profile P₁ P₂ hlet p E _ env _ h.1.1,
          elabWith_fullyWritten_profile P₁ P₂ hlet w E cr env _ h.1.2,
          elabWith_fullyWritten_profile P₁ P₂ hlet b E _ env _ h.2]
      · rw [elabWith_fullyWritten_profile P₁ P₂ hlet p _ _ _ _ h.1.1,
          elabWith_fullyWritten_profile P₁ P₂ hlet w E cr env _ h.1.2,
          elabWith_fullyWritten_profile P₁ P₂ hlet b _ _ _ _ h.2]
  | .unify p w b, E, cr, env, pos, h => by
      simp only [Src.FullyWritten, Bool.and_eq_true] at h
      simp only [elabWith]
      rw [elabWith_fullyWritten_profile P₁ P₂ hlet p E cr env _ h.1.1,
        elabWith_fullyWritten_profile P₁ P₂ hlet w E cr env _ h.1.2,
        elabWith_fullyWritten_profile P₁ P₂ hlet b E cr env _ h.2]
  | .alt t₁ t₂, E, cr, env, pos, h => by
      simp only [Src.FullyWritten, Bool.and_eq_true] at h
      simp only [elabWith]
      rw [elabWith_fullyWritten_profile P₁ P₂ hlet t₁ E cr env _ h.1,
        elabWith_fullyWritten_profile P₁ P₂ hlet t₂ E cr env _ h.2]
  | .new [] b, E, cr, env, pos, h => by
      simp only [Src.FullyWritten] at h
      simp only [elabWith]
      rw [elabWith_fullyWritten_profile P₁ P₂ hlet b E cr env _ h]
  | .new (y₀ :: ys) b, E, cr, env, pos, h => by
      simp only [Src.FullyWritten] at h
      simp only [elabWith]
      rw [elabWith_fullyWritten_profile P₁ P₂ hlet b _ _ _ _ h]
  | .form _ b, E, cr, env, pos, h => by
      simp only [Src.FullyWritten] at h
      simp only [elabWith]
      rw [elabWith_fullyWritten_profile P₁ P₂ hlet b E cr (env.update [] (pos ++ [0])) _ h]

/-- **A program whose every lambda and `let` carries a crossing set
elaborates alike under every two profiles**, lexical fresh included. -/
theorem elabWith_allWritten_profile (P₁ P₂ : Profile S X) :
    ∀ (t : Src S X) (E cr : List X) (env : REnv X) (pos : Owner), t.AllWritten = true →
      elabWith P₁ E cr env pos t = elabWith P₂ E cr env pos t
  | .sym _, _, _, _, _, _ => rfl
  | .fn _, _, _, _, _, _ => rfl
  | .sv _, _, _, _, _, _ => rfl
  | .par _, _, _, _, _, _ => rfl
  | .lam z xs b, E, cr, env, pos, h => by
      simp only [Src.AllWritten, Bool.and_eq_true] at h
      have hown : P₁.own xs b E = P₂.own xs b E := crossOwn_of_isSome h.1 _ _ _
      simp only [elabWith]
      rw [← hown, elabWith_allWritten_profile P₁ P₂ b _ _ _ _ h.2]
  | .app f a, E, cr, env, pos, h => by
      simp only [Src.AllWritten, Bool.and_eq_true] at h
      simp only [elabWith]
      rw [elabWith_allWritten_profile P₁ P₂ f E cr env _ h.1,
        elabWith_allWritten_profile P₁ P₂ a E cr env _ h.2]
  | .quote _, _, _, _, _, _ => rfl
  | .pquote _, _, _, _, _, _ => rfl
  | .letS p w b xs, E, cr, env, pos, h => by
      simp only [Src.AllWritten, Bool.and_eq_true] at h
      have hi : P₁.letIntro xs p cr = P₂.letIntro xs p cr := crossOwn_of_isSome h.1.1.1 _ _ _
      simp only [elabWith]
      rw [← hi]
      split
      · rw [elabWith_allWritten_profile P₁ P₂ p E _ env _ h.1.1.2,
          elabWith_allWritten_profile P₁ P₂ w E cr env _ h.1.2,
          elabWith_allWritten_profile P₁ P₂ b E _ env _ h.2]
      · rw [elabWith_allWritten_profile P₁ P₂ p _ _ _ _ h.1.1.2,
          elabWith_allWritten_profile P₁ P₂ w E cr env _ h.1.2,
          elabWith_allWritten_profile P₁ P₂ b _ _ _ _ h.2]
  | .unify p w b, E, cr, env, pos, h => by
      simp only [Src.AllWritten, Bool.and_eq_true] at h
      simp only [elabWith]
      rw [elabWith_allWritten_profile P₁ P₂ p E cr env _ h.1.1,
        elabWith_allWritten_profile P₁ P₂ w E cr env _ h.1.2,
        elabWith_allWritten_profile P₁ P₂ b E cr env _ h.2]
  | .alt t₁ t₂, E, cr, env, pos, h => by
      simp only [Src.AllWritten, Bool.and_eq_true] at h
      simp only [elabWith]
      rw [elabWith_allWritten_profile P₁ P₂ t₁ E cr env _ h.1,
        elabWith_allWritten_profile P₁ P₂ t₂ E cr env _ h.2]
  | .new [] b, E, cr, env, pos, h => by
      simp only [Src.AllWritten] at h
      simp only [elabWith]
      rw [elabWith_allWritten_profile P₁ P₂ b E cr env _ h]
  | .new (y₀ :: ys) b, E, cr, env, pos, h => by
      simp only [Src.AllWritten] at h
      simp only [elabWith]
      rw [elabWith_allWritten_profile P₁ P₂ b _ _ _ _ h]
  | .form _ b, E, cr, env, pos, h => by
      simp only [Src.AllWritten] at h
      simp only [elabWith]
      rw [elabWith_allWritten_profile P₁ P₂ b E cr (env.update [] (pos ++ [0])) _ h]

/-- **A fully written program does not read its context**: under every
profile, the spellings quantified at the enclosing regions change nothing.
Rule M's same-spelled outsiders lose their hold once the crossing sets are
written. -/
theorem elabWith_fullyWritten_context (P : Profile S X) :
    ∀ (t : Src S X) (E E' cr : List X) (env : REnv X) (pos : Owner), t.FullyWritten = true →
      elabWith P E cr env pos t = elabWith P E' cr env pos t
  | .sym _, _, _, _, _, _, _ => rfl
  | .fn _, _, _, _, _, _, _ => rfl
  | .sv _, _, _, _, _, _, _ => rfl
  | .par _, _, _, _, _, _, _ => rfl
  | .lam z xs b, E, E', cr, env, pos, h => by
      simp only [Src.FullyWritten, Bool.and_eq_true] at h
      have hown : P.own xs b E = P.own xs b E' := crossOwn_of_isSome h.1 _ _ _
      simp only [elabWith]
      rw [← hown, elabWith_fullyWritten_context P b (P.own xs b E ++ Src.direct b ++ E)
        (P.own xs b E ++ Src.direct b ++ E') _ _ _ h.2]
  | .app f a, E, E', cr, env, pos, h => by
      simp only [Src.FullyWritten, Bool.and_eq_true] at h
      simp only [elabWith]
      rw [elabWith_fullyWritten_context P f E E' cr env _ h.1,
        elabWith_fullyWritten_context P a E E' cr env _ h.2]
  | .quote _, _, _, _, _, _, _ => rfl
  | .pquote _, _, _, _, _, _, _ => rfl
  | .letS p w b xs, E, E', cr, env, pos, h => by
      simp only [Src.FullyWritten, Bool.and_eq_true] at h
      simp only [elabWith]
      split
      · rw [elabWith_fullyWritten_context P p E E' _ env _ h.1.1,
          elabWith_fullyWritten_context P w E E' cr env _ h.1.2,
          elabWith_fullyWritten_context P b E E' _ env _ h.2]
      · rename_i y₀ ys _
        rw [elabWith_fullyWritten_context P p (y₀ :: ys ++ E) (y₀ :: ys ++ E') _ _ _ h.1.1,
          elabWith_fullyWritten_context P w E E' cr env _ h.1.2,
          elabWith_fullyWritten_context P b (y₀ :: ys ++ E) (y₀ :: ys ++ E') _ _ _ h.2]
  | .unify p w b, E, E', cr, env, pos, h => by
      simp only [Src.FullyWritten, Bool.and_eq_true] at h
      simp only [elabWith]
      rw [elabWith_fullyWritten_context P p E E' cr env _ h.1.1,
        elabWith_fullyWritten_context P w E E' cr env _ h.1.2,
        elabWith_fullyWritten_context P b E E' cr env _ h.2]
  | .alt t₁ t₂, E, E', cr, env, pos, h => by
      simp only [Src.FullyWritten, Bool.and_eq_true] at h
      simp only [elabWith]
      rw [elabWith_fullyWritten_context P t₁ E E' cr env _ h.1,
        elabWith_fullyWritten_context P t₂ E E' cr env _ h.2]
  | .new [] b, E, E', cr, env, pos, h => by
      simp only [Src.FullyWritten] at h
      simp only [elabWith]
      rw [elabWith_fullyWritten_context P b E E' cr env _ h]
  | .new (y₀ :: ys) b, E, E', cr, env, pos, h => by
      simp only [Src.FullyWritten] at h
      simp only [elabWith]
      rw [elabWith_fullyWritten_context P b ((y₀ :: ys) ++ E) ((y₀ :: ys) ++ E') _ _ _ h]
  | .form _ b, E, E', cr, env, pos, h => by
      simp only [Src.FullyWritten] at h
      simp only [elabWith]
      rw [elabWith_fullyWritten_context P b E E' cr (env.update [] (pos ++ [0])) _ h]

/-! ## Lexical inventory: the boundary rule -/

/-- The boundary rule of a lambda region, read from a profile: its owned list
when no list is written. -/
def Profile.boundary (P : Profile S X) : OwnRule S X := fun b E => P.lamOwn b E

/-- A spelling crosses the boundary of a lambda region when the region writes
it and an enclosing region quantifies it too. -/
def Crosses (b : Src S X) (E : List X) (y : X) : Prop := y ∈ Src.direct b ∧ y ∈ E

omit [DecidableEq X] in
/-- **The tension, for crossing spellings.**  A boundary rule that keeps every
crossing spelling owned (modular for those spellings, and owning what nothing
outside writes) never connects a crossing spelling without a crossing set:
annotation-free relational refinement across a boundary is impossible for
it. -/
theorem boundary_tension (R : OwnRule S X)
    (hpriv : ∀ b y, y ∈ Src.direct b → y ∈ R b [])
    (hcross : ∀ b E y, Crosses b E y → (y ∈ R b E ↔ y ∈ R b [])) :
    ∀ b E y, Crosses b E y → y ∈ R b E := by
  intro b E y hy
  exact (hcross b E y hy).2 (hpriv b y hy.1)

/-- Rule M (inventory connected by spelling) owns region-internal names and
connects every crossing spelling. -/
theorem profLIc_boundary (b : Src S X) (E : List X) (y : X) :
    (y ∈ Src.direct b → y ∉ E → y ∈ (profLIc : Profile S X).boundary b E) ∧
    (Crosses b E y → y ∉ (profLIc : Profile S X).boundary b E) := by
  constructor
  · intro hy hE
    simp [Profile.boundary, profLIc, profM, ownRuleMDefault, List.mem_dedup, hy, hE]
  · intro hc
    simp [Profile.boundary, profLIc, profM, ownRuleMDefault, List.mem_dedup, hc.2]

/-- The apart-by-default inventory owns every spelling the region writes,
crossing or not: it is modular, and connects only through its crossing set. -/
theorem profLIi_boundary (b : Src S X) (E : List X) (y : X) (hy : y ∈ Src.direct b) :
    y ∈ (profLIi : Profile S X).boundary b E := by
  simp [Profile.boundary, profLIi, profEC, Src.uses, List.mem_dedup, hy]

/-- With explicit introduction the inventory is stated on the construct:
every name its region uses outside its crossing set, whatever the context and
the profile's default. -/
theorem crossing_states_inventory (sh U d d' : List X) :
    crossOwn (some sh) U d = (U.filter fun y => decide (y ∉ sh)).dedup ∧
      crossOwn (some sh) U d = crossOwn (some sh) U d' :=
  ⟨rfl, rfl⟩

end Mettapedia.GSLT.LanguageDef.TemplateScope
