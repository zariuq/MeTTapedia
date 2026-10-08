import Mettapedia.GSLT.LanguageDef.ScopePolicies.Explication

/-!
# Translators between scope policies, as maps of theories

A translator from a policy `c` to a policy `c'` is a map of programs whose
translation elaborates, under `c'`, to the judgment that the source elaborates
to under `c`, up to the static equivalence of the core (`Translates`).  The
condition may hold on a domain of programs only.

* `policyOn` — the theory of a policy on a domain of programs: the core read
  along the policy's elaboration, restricted to the domain.
* `translator`, `translator_hosting` — **a translator is a hosting map of
  theories** between them.  `translator_exhausting_iff`: it is exhausting
  exactly when every program of the target domain elaborates, under the target
  policy, to what some program of the source domain elaborates to under the
  source policy.
* `Translates.comp`, `Translates.mono` — translators compose and restrict.

## The translators

| From | To | Map | Domain | Theorem |
|---|---|---|---|---|
| rule M | lexical fresh | `toLexical` | admissible programs | `translates_toLexical` |
| explicit capture | every ownership policy | `explicateEC` | all programs | `translates_explicateEC` |
| query-wide | every ownership policy | `explicateQ` | lambdas without crossing set | `translates_explicateQ` |
| lexical fresh | every ownership policy | `explicateLF` | lambdas without crossing set | `translates_explicateLF` |
| rule M | every ownership policy | `explicateLF ∘ toLexical` | admissible, lambdas without crossing set | `translates_mercury` |
| any ownership policy | any ownership policy | the identity | explicit programs | `translates_explicit` |

The source and the target share their lifetime and readout, per call and
reference for the two rows of rule M.

`toLexical` is exact in the identity model and not in the slot model: the two
elaborations are different terms of the core, statically equivalent because
one judgment of the identity model reads both (`toLexical_core_equiv`).  The
operational half of hosting is `IdSlot.transfer`, restated as
`toLexical_transfer`.

## In the hosting preorder

`explicit_hosted`: the theory of explicit programs is hosted by every
ownership policy, by the identity.  `explicitCapture_hosted_by_explicit`,
`explicit_hosts_explicitCapture_exhausting`: explicit capture is hosted by the
theory of explicit programs, and that map is exhausting, so the two are one
degree.  The query-wide policy, lexical fresh and rule M are hosted by it on
the domains of the table.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ScopePolicies

open Mettapedia.GSLT
open Mettapedia.GSLT.LanguageDef.SequentialBindingDiscipline
open Mettapedia.GSLT.LanguageDef.TemplateScope
open Mettapedia.GSLT.LanguageDef.TemplateScope.IdSlot

universe u v

variable {S : Type u} {X : Type v}

/-! ## The theory of a policy on a domain of programs -/

/-- An authored term whose program, if it is one, lies in a domain. -/
def Authored.Within (domain : Program S X → Prop) : Authored S X → Prop
  | .program text => domain text
  | .done _ => True

/-- Map the program of an authored term; an observation is unchanged. -/
def Authored.mapProgram (convert : Program S X → Program S X) : Authored S X → Authored S X
  | .program text => .program (convert text)
  | .done bag => .done bag

theorem Authored.Within.mapProgram {domain domain' : Program S X → Prop}
    {convert : Program S X → Program S X} (maps : ∀ text, domain text → domain' (convert text)) :
    ∀ {term : Authored S X}, term.Within domain → (term.mapProgram convert).Within domain'
  | .program text, within => maps text within
  | .done _, _ => trivial

/-- Map the programs of the authored terms within a domain. -/
def convertWithin {domain domain' : Program S X → Prop} (convert : Program S X → Program S X)
    (maps : ∀ text, domain text → domain' (convert text)) :
    {term : Authored S X // term.Within domain} → {term : Authored S X // term.Within domain'} :=
  fun term => ⟨term.1.mapProgram convert, term.2.mapProgram maps⟩

variable [DecidableEq X]

/-- The elaboration of a policy, on the authored terms within a domain. -/
def elabWithin (c : Config) (u : X) (unit : S) (domain : Program S X → Prop) :
    {term : Authored S X // term.Within domain} → Core S X :=
  fun term => elabState c u unit term.1

/-- **A translator.**  The translation of a program of the domain elaborates,
under `c'`, to the judgment that the program elaborates to under `c`, up to
the static equivalence of the core. -/
def Translates (c c' : Config) (u : X) (unit : S) (domain : Program S X → Prop)
    (convert : Program S X → Program S X) : Prop :=
  ∀ text, domain text →
    CoreEquiv (elabState c' u unit (.program (convert text))) (elabState c u unit (.program text))

/-- A translator on a domain is a translator on every smaller one. -/
theorem Translates.mono {c c' : Config} {u : X} {unit : S} {domain smaller : Program S X → Prop}
    {convert : Program S X → Program S X} (translates : Translates c c' u unit domain convert)
    (within : ∀ text, smaller text → domain text) : Translates c c' u unit smaller convert :=
  fun text inside => translates text (within text inside)

/-- **Translators compose.** -/
theorem Translates.comp {c c' c'' : Config} {u : X} {unit : S}
    {domain domain' : Program S X → Prop} {first second : Program S X → Program S X}
    (firstTranslates : Translates c c' u unit domain first)
    (secondTranslates : Translates c' c'' u unit domain' second)
    (maps : ∀ text, domain text → domain' (first text)) :
    Translates c c'' u unit domain fun text => second (first text) :=
  fun text inside =>
    (secondTranslates (first text) (maps text inside)).trans (firstTranslates text inside)

/-- The identity translates a policy into itself. -/
theorem Translates.id (c : Config) (u : X) (unit : S) (domain : Program S X → Prop) :
    Translates c c u unit domain fun text => text :=
  fun _ _ => .refl _

/-- A translator agrees with the elaborations on every authored term. -/
theorem Translates.agrees {c c' : Config} {u : X} {unit : S}
    {domain domain' : Program S X → Prop} {convert : Program S X → Program S X}
    (translates : Translates c c' u unit domain convert)
    (maps : ∀ text, domain text → domain' (convert text))
    (origin : {term : Authored S X // term.Within domain}) :
    CoreEquiv (elabWithin c' u unit domain' (convertWithin convert maps origin))
      (elabWithin c u unit domain origin) := by
  obtain ⟨term, within⟩ := origin
  cases term with
  | program text => exact translates text within
  | done bag => exact .refl _

variable [DecidableEq S]

/-- **The theory of a policy on a domain of programs.** -/
def policyOn (c : Config) (u : X) (unit : S) (domain : Program S X → Prop) : GSLT.{max u v} :=
  (coreGSLT S X).readAlong (elabWithin c u unit domain)

/-- Its readings are closed under reduction. -/
theorem elabWithin_readingClosed (c : Config) (u : X) (unit : S)
    (domain : Program S X → Prop) :
    GSLT.ReadingClosed (target := coreGSLT S X) (elabWithin c u unit domain) := by
  intro origin value step
  obtain ⟨bag, rfl⟩ := core_rewrites_target step
  exact ⟨⟨.done bag, trivial⟩, .refl _⟩

/-- The elaboration of a policy on a domain is a hosting map into the core. -/
theorem policyOn_hosting (c : Config) (u : X) (unit : S) (domain : Program S X → Prop) :
    (GSLT.reading (target := coreGSLT S X) (elabWithin c u unit domain)).Hosting :=
  GSLT.reading_hosting _ (elabWithin_readingClosed c u unit domain)

/-- **A translator, as a map of theories.** -/
def translator {c c' : Config} {u : X} {unit : S} {domain domain' : Program S X → Prop}
    {convert : Program S X → Program S X} (translates : Translates c c' u unit domain convert)
    (maps : ∀ text, domain text → domain' (convert text)) :
    ContextMap (policyOn c u unit domain).termsAlone (policyOn c' u unit domain').termsAlone :=
  GSLT.translate (target := coreGSLT S X) (elabWithin c u unit domain)
    (elabWithin c' u unit domain') (convertWithin convert maps) (translates.agrees maps)

/-- **A translator is a hosting map.** -/
theorem translator_hosting {c c' : Config} {u : X} {unit : S}
    {domain domain' : Program S X → Prop} {convert : Program S X → Program S X}
    (translates : Translates c c' u unit domain convert)
    (maps : ∀ text, domain text → domain' (convert text)) :
    (translator translates maps).Hosting :=
  GSLT.translate_hosting _ _ _ _ (elabWithin_readingClosed c u unit domain)

/-- **A translator is exhausting exactly when every program of the target
domain elaborates to what some program of the source domain elaborates to**,
up to the static equivalence. -/
theorem translator_exhausting_iff {c c' : Config} {u : X} {unit : S}
    {domain domain' : Program S X → Prop} {convert : Program S X → Program S X}
    (translates : Translates c c' u unit domain convert)
    (maps : ∀ text, domain text → domain' (convert text)) :
    (translator translates maps).Exhausting ↔
      ∀ text', domain' text' → ∃ text, domain text ∧
        CoreEquiv (elabState c u unit (.program text)) (elabState c' u unit (.program text')) := by
  refine Iff.trans (GSLT.translate_exhausting_iff (target := coreGSLT S X) _ _ _ _) ?_
  constructor
  · intro reached text' inside
    obtain ⟨⟨origin, within⟩, related⟩ := reached ⟨.program text', inside⟩
    cases origin with
    | program text => exact ⟨text, within, related⟩
    | done bag => exact absurd related.symm coreEquiv_kind
  · rintro reached ⟨value, within⟩
    cases value with
    | program text' =>
        obtain ⟨text, inside, related⟩ := reached text' within
        exact ⟨⟨.program text, inside⟩, related⟩
    | done bag => exact ⟨⟨.done bag, trivial⟩, .refl _⟩

/-- **What a translator keeps**: the two policies evaluate a program of the
domain and its translation together, to equivalent observations. -/
theorem Translates.evaluates {c c' : Config} {u : X} {unit : S}
    {domain : Program S X → Prop} {convert : Program S X → Program S X}
    (translates : Translates c c' u unit domain convert) {text : Program S X}
    (inside : domain text) {n : ℕ} {bag : Result S (Slot X)}
    (defined : run c.disc (progSlot c u unit text.clauses) n [] Store.empty
      (elabCfg c [] text.query) = some bag) :
    ∃ n' bag', run c'.disc (progSlot c' u unit (convert text).clauses) n' [] Store.empty
        (elabCfg c' [] (convert text).query) = some bag' ∧
      CoreEquiv (.done bag : Core S X) (.done bag') := by
  obtain ⟨observed, evaluates, related⟩ :=
    (coreEquiv_evaluates (translates text inside)).2 (.done bag) (evaluates_run_done.mpr ⟨n, defined⟩)
  cases observed with
  | run _ _ _ => exact evaluates.elim
  | done bag' =>
      obtain ⟨n', defined'⟩ := evaluates_run_done.mp evaluates
      exact ⟨n', bag', defined', related.symm⟩

/-- A translator keeps the number of results. -/
theorem Translates.bag_length {c c' : Config} {u : X} {unit : S}
    {domain : Program S X → Prop} {convert : Program S X → Program S X}
    (translates : Translates c c' u unit domain convert) {text : Program S X}
    (inside : domain text) {n n' : ℕ} {bag bag' : Result S (Slot X)}
    (defined : run c.disc (progSlot c u unit text.clauses) n [] Store.empty
      (elabCfg c [] text.query) = some bag)
    (defined' : run c'.disc (progSlot c' u unit (convert text).clauses) n' [] Store.empty
      (elabCfg c' [] (convert text).query) = some bag') :
    bag.length = bag'.length := by
  obtain ⟨m, other, definedOther, related⟩ := translates.evaluates inside defined
  have same : (Core.done other : Core S X) = .done bag' :=
    Evaluates.unique (evaluates_run_done.mpr ⟨m, definedOther⟩)
      (evaluates_run_done.mpr ⟨n', defined'⟩)
  cases same
  exact coreEquiv_done_length related

/-! ## Explicit text -/

omit [DecidableEq S] in
/-- **On explicit programs the identity translates every ownership policy into
every other**, at one lifetime and readout. -/
theorem translates_explicit (o o' : Ownership) (l : Lifetime) (r : Readout) (u : X) (unit : S) :
    Translates ⟨o, l, r⟩ ⟨o', l, r⟩ u unit Program.Explicit fun text => text := by
  intro text inside
  rw [elabState_explicit o' o l r u unit inside]
  exact .refl _

omit [DecidableEq S] in
/-- **Explicit capture into every ownership policy**, on every program. -/
theorem translates_explicateEC (o' : Ownership) (l : Lifetime) (r : Readout) (u : X) (unit : S) :
    Translates ⟨.explicitCapture, l, r⟩ ⟨o', l, r⟩ u unit (fun _ => True)
      (Program.map explicateEC) := by
  intro text _
  rw [elabState_explicateEC o' l r u unit text]
  exact .refl _

omit [DecidableEq S] in
/-- **The query-wide policy into every ownership policy**, on programs whose
lambdas carry no crossing set. -/
theorem translates_explicateQ (o' : Ownership) (l : Lifetime) (r : Readout) (u : X) (unit : S) :
    Translates ⟨.queryWide, l, r⟩ ⟨o', l, r⟩ u unit
      (Program.All fun t => lamPlain t = true) (Program.map explicateQ) := by
  intro text inside
  rw [elabState_explicateQ o' l r u unit inside]
  exact .refl _

omit [DecidableEq S] in
/-- **Lexical fresh into every ownership policy**, on programs whose lambdas
carry no crossing set. -/
theorem translates_explicateLF (o' : Ownership) (l : Lifetime) (r : Readout) (u : X) (unit : S) :
    Translates ⟨.lexicalFresh, l, r⟩ ⟨o', l, r⟩ u unit
      (Program.All fun t => lamPlain t = true) (Program.map (explicateLF [])) := by
  intro text inside
  rw [elabState_explicateLF o' l r u unit inside]
  exact .refl _

/-! ## The translator from rule M to lexical fresh -/

/-- **The translator from rule M to lexical fresh**, on programs: the existing
`toLexical` on the query and `toLexicalProg` on the equations. -/
def toLexProgram (text : Program S X) : Program S X :=
  ⟨toLexicalProg text.clauses, toLexical text.query⟩

omit [DecidableEq S] in
/-- The translation of an admissible program is admissible. -/
theorem toLexProgram_admissible {text : Program S X} (admissible : text.Admissible) :
    (toLexProgram text).Admissible := by
  refine ⟨fun F body found => ?_, admissible_toLexAt admissible.2 _ _ _ _ _⟩
  simp only [toLexProgram, toLexicalProg, Option.map_eq_some_iff] at found
  obtain ⟨source, sourceFound, rfl⟩ := found
  exact admissible_toLexAt (admissible.1 F source sourceFound) _ _ _ _ _

omit [DecidableEq S] in
/-- **The translation is the identity up to the static equivalence of the
core.**  The slot-model elaboration of the translation under lexical fresh and
that of the source under rule M are read by one judgment of the identity
model: rule M's elaboration of the source, which is lexical fresh's
elaboration of the translation, term for term (`elabLFFormAt_toLexicalAt`,
`progLF_toLexicalProg`). -/
theorem toLexical_core_equiv (u : X) (unit : S) {text : Program S X}
    (admissible : text.Admissible) :
    CoreEquiv (elabState cfgLF u unit (.program (toLexProgram text)))
      (elabState cfgM u unit (.program text)) := by
  have translated := reads_of_admissible u unit .lexicalFresh (toLexProgram_admissible admissible)
  have source := reads_of_admissible u unit .mercury admissible
  have programs : Reading.lexicalFresh.idProg u unit (toLexProgram text).clauses =
      Reading.mercury.idProg u unit text.clauses := progLF_toLexicalProg u unit text.clauses
  have queries : Reading.lexicalFresh.idQuery (toLexProgram text).query =
      Reading.mercury.idQuery text.query := elabLFFormAt_toLexicalAt [] text.query
  rw [programs, queries] at translated
  exact .of_link (.run translated source)

omit [DecidableEq S] in
/-- **`toLexical` translates rule M into lexical fresh**, on admissible
programs. -/
theorem translates_toLexical (u : X) (unit : S) :
    Translates cfgM cfgLF u unit Program.Admissible toLexProgram :=
  fun _ admissible => toLexical_core_equiv u unit admissible

/-- **`toLexical`, as a map of theories from the Mercury policy to the
lexical-fresh policy**, on admissible programs. -/
def toLexicalMap (u : X) (unit : S) :
    ContextMap (policyOn cfgM u unit (Program.Admissible (S := S) (X := X))).termsAlone
      (policyOn cfgLF u unit (Program.Admissible (S := S) (X := X))).termsAlone :=
  translator (translates_toLexical u unit) fun _ admissible => toLexProgram_admissible admissible

/-- **`toLexical` is a hosting map.** -/
theorem toLexicalMap_hosting (u : X) (unit : S) : (toLexicalMap (S := S) u unit).Hosting :=
  translator_hosting _ _

/-- **The operational half, from `IdSlot.transfer`.**  The translated program
under lexical fresh and the source under rule M are defined together, and
their observations are equivalent in the core: both bags are renamings, result
by result, of one bag of the identity model. -/
theorem toLexical_transfer (u : X) (unit : S) {text : Program S X}
    (admissible : text.Admissible) :
    ((∃ n bag, run .static (progSlot cfgLF u unit (toLexProgram text).clauses) n [] Store.empty
        (elabCfg cfgLF [] (toLexProgram text).query) = some bag) ↔
      ∃ n bag, run .static (progSlot cfgM u unit text.clauses) n [] Store.empty
        (elabCfg cfgM [] text.query) = some bag) ∧
    ∀ {n n' : ℕ} {bag bag' : Result S (Slot X)},
      run .static (progSlot cfgLF u unit (toLexProgram text).clauses) n [] Store.empty
        (elabCfg cfgLF [] (toLexProgram text).query) = some bag →
      run .static (progSlot cfgM u unit text.clauses) n' [] Store.empty
        (elabCfg cfgM [] text.query) = some bag' →
      CoreEquiv (.done bag : Core S X) (.done bag') := by
  obtain ⟨together, renamed⟩ :=
    transfer u unit text.clauses text.query admissible.1 admissible.2
  refine ⟨together, fun defined defined' => ?_⟩
  obtain ⟨_, bag₂, -, first, second⟩ := renamed defined defined'
  exact .of_link (.done first second)

/-- **`toLexical` in the identity model is exact** (`run_toLexical`): the same
bag at every fuel, path, store and discipline, with no condition on the
text. -/
theorem toLexical_identity_exact (u : X) (unit : S) (text : Program S X) (d : Disc) (n : ℕ)
    (π : Path) (σ : GStore S (BId X)) :
    run d (Reading.lexicalFresh.idProg u unit (toLexProgram text).clauses) n π σ
        (Reading.lexicalFresh.idQuery (toLexProgram text).query) =
      run d (Reading.mercury.idProg u unit text.clauses) n π σ
        (Reading.mercury.idQuery text.query) :=
  run_toLexical u unit text.clauses text.query d n π σ

/-! ## Rule M into every ownership policy -/

omit [DecidableEq X] [DecidableEq S] in
theorem lamPlain_wrapNew (ys : List X) (b : Src S X) : lamPlain (wrapNew ys b) = lamPlain b := by
  cases ys <;> rfl

omit [DecidableEq S] in
/-- The translator from rule M writes no crossing set on a lambda. -/
theorem lamPlain_toLexAt : ∀ (t : Src S X) (E cr : List X) (env : IEnv X) (fr pos : Owner),
    lamPlain (toLexAt E cr env fr pos t) = lamPlain t
  | .sym _, _, _, _, _, _ => rfl
  | .fn _, _, _, _, _, _ => rfl
  | .sv _, _, _, _, _, _ => rfl
  | .par _, _, _, _, _, _ => rfl
  | .quote _, _, _, _, _, _ => rfl
  | .pquote _, _, _, _, _, _ => rfl
  | .lam _ none b, _, _, _, _, _ => by
      simp only [toLexAt, lamPlain, lamPlain_wrapNew, lamPlain_toLexAt b]
  | .lam _ (some _) b, _, _, _, _, _ => by
      simp only [toLexAt, lamPlain, lamPlain_toLexAt b]
  | .app f a, _, _, _, _, _ => by
      simp only [toLexAt, lamPlain, lamPlain_toLexAt f, lamPlain_toLexAt a]
  | .letS p w b none, _, _, _, _, _ => by
      simp only [toLexAt, lamPlain, lamPlain_toLexAt p, lamPlain_toLexAt w, lamPlain_toLexAt b]
  | .letS p w b (some _), _, _, _, _, _ => by
      simp only [toLexAt, lamPlain, lamPlain_toLexAt p, lamPlain_toLexAt w, lamPlain_toLexAt b]
  | .unify p w b, _, _, _, _, _ => by
      simp only [toLexAt, lamPlain, lamPlain_toLexAt p, lamPlain_toLexAt w, lamPlain_toLexAt b]
  | .alt t₁ t₂, _, _, _, _, _ => by
      simp only [toLexAt, lamPlain, lamPlain_toLexAt t₁, lamPlain_toLexAt t₂]
  | .new _ b, _, _, _, _, _ => by simp only [toLexAt, lamPlain, lamPlain_toLexAt b]
  | .form _ b, _, _, _, _, _ => by simp only [toLexAt, lamPlain, lamPlain_toLexAt b]

omit [DecidableEq S] in
/-- The translation of a program whose lambdas carry no crossing set is such a
program. -/
theorem toLexProgram_lamPlain {text : Program S X}
    (plain : text.All fun t => lamPlain t = true) :
    (toLexProgram text).All fun t => lamPlain t = true := by
  refine ⟨fun F body found => ?_, ?_⟩
  · simp only [toLexProgram, toLexicalProg, Option.map_eq_some_iff] at found
    obtain ⟨source, sourceFound, rfl⟩ := found
    simp only [toLexicalAt, lamPlain_toLexAt]
    exact plain.1 F source sourceFound
  · simp only [toLexProgram, toLexical, toLexicalAt, lamPlain_toLexAt]
    exact plain.2

omit [DecidableEq S] in
/-- **Rule M into every ownership policy**: translate into lexical fresh, then
write the result out.  On admissible programs whose lambdas carry no crossing
set; per call, reference. -/
theorem translates_mercury (o' : Ownership) (u : X) (unit : S) :
    Translates cfgM ⟨o', .perCall, .reference⟩ u unit
      (fun text => text.Admissible ∧ text.All fun t => lamPlain t = true)
      (fun text => (toLexProgram text).map (explicateLF [])) :=
  Translates.comp (domain' := Program.All fun t => lamPlain t = true)
    ((translates_toLexical u unit).mono fun _ inside => inside.1)
    (translates_explicateLF o' .perCall .reference u unit)
    fun _ inside => toLexProgram_lamPlain inside.2

/-! ## In the hosting preorder -/

/-- **The theory of explicit programs is hosted by every ownership policy**,
by the identity on text. -/
theorem explicit_hosted (o o' : Ownership) (l : Lifetime) (r : Readout) (u : X) (unit : S)
    (domain' : Program S X → Prop) (covers : ∀ text, Program.Explicit text → domain' text) :
    (translator (translates_explicit (S := S) o o' l r u unit) covers).Hosting :=
  translator_hosting _ _

/-- **Explicit capture is hosted by the theory of explicit programs.** -/
theorem explicitCapture_hosted_by_explicit (o' : Ownership) (l : Lifetime) (r : Readout)
    (u : X) (unit : S) :
    (translator (domain' := Program.Explicit) (translates_explicateEC (S := S) o' l r u unit)
      fun text _ => text.explicit_map_explicateEC).Hosting :=
  translator_hosting _ _

/-- **And that map is exhausting**: every explicit program is, under every
ownership policy, what it is under explicit capture.  So explicit capture and
the explicit form are one degree of the hosting preorder. -/
theorem explicit_hosts_explicitCapture_exhausting (o' : Ownership) (l : Lifetime)
    (r : Readout) (u : X) (unit : S) :
    (translator (domain' := Program.Explicit) (translates_explicateEC (S := S) o' l r u unit)
      fun text _ => text.explicit_map_explicateEC).Exhausting := by
  rw [translator_exhausting_iff]
  intro text' inside
  refine ⟨text', trivial, ?_⟩
  rw [elabState_explicit .explicitCapture o' l r u unit inside]
  exact .refl _

/-- **On explicit programs the identity is exhausting too**: every pair of
ownership policies has the same theory of explicit programs. -/
theorem explicit_identity_exhausting (o o' : Ownership) (l : Lifetime) (r : Readout) (u : X)
    (unit : S) :
    (translator (domain' := Program.Explicit) (translates_explicit (S := S) o o' l r u unit)
      fun _ inside => inside).Exhausting := by
  rw [translator_exhausting_iff]
  intro text' inside
  refine ⟨text', inside, ?_⟩
  rw [elabState_explicit o o' l r u unit inside]
  exact .refl _

/-! ## Is `toLexical` exhausting? -/

omit [DecidableEq S] in
theorem spineNewFree_explicateLF : ∀ (t : Src S X) (cr : List X),
    (explicateLF cr t).spineNewFree = t.spineNewFree
  | .sym _, _ => rfl
  | .fn _, _ => rfl
  | .sv _, _ => rfl
  | .par _, _ => rfl
  | .quote _, _ => rfl
  | .pquote _, _ => rfl
  | .lam _ none _, _ => rfl
  | .lam _ (some _) _, _ => rfl
  | .app f a, cr => by
      simp only [explicateLF, Src.spineNewFree, spineNewFree_explicateLF f,
        spineNewFree_explicateLF a]
  | .letS p _ _ _, cr => by simp only [explicateLF, Src.spineNewFree, spineNewFree_explicateLF p]
  | .unify p _ _, cr => by simp only [explicateLF, Src.spineNewFree, spineNewFree_explicateLF p]
  | .alt _ _, _ => rfl
  | .new [] b, cr => by simp only [explicateLF, Src.spineNewFree, spineNewFree_explicateLF b]
  | .new (_ :: _) _, _ => rfl
  | .form _ _, _ => rfl

omit [DecidableEq S] in
theorem patsNewFree_explicateLF : ∀ (t : Src S X) (cr : List X),
    (explicateLF cr t).patsNewFree = t.patsNewFree
  | .sym _, _ => rfl
  | .fn _, _ => rfl
  | .sv _, _ => rfl
  | .par _, _ => rfl
  | .quote _, _ => rfl
  | .pquote _, _ => rfl
  | .lam _ none b, cr => by simp only [explicateLF, Src.patsNewFree, patsNewFree_explicateLF b]
  | .lam _ (some _) b, cr => by simp only [explicateLF, Src.patsNewFree, patsNewFree_explicateLF b]
  | .app f a, cr => by
      simp only [explicateLF, Src.patsNewFree, patsNewFree_explicateLF f, patsNewFree_explicateLF a]
  | .letS p w b _, cr => by
      simp only [explicateLF, Src.patsNewFree, spineNewFree_explicateLF p,
        patsNewFree_explicateLF p, patsNewFree_explicateLF w, patsNewFree_explicateLF b]
  | .unify p w b, cr => by
      simp only [explicateLF, Src.patsNewFree, spineNewFree_explicateLF p,
        patsNewFree_explicateLF p, patsNewFree_explicateLF w, patsNewFree_explicateLF b]
  | .alt t₁ t₂, cr => by
      simp only [explicateLF, Src.patsNewFree, patsNewFree_explicateLF t₁,
        patsNewFree_explicateLF t₂]
  | .new _ b, cr => by simp only [explicateLF, Src.patsNewFree, patsNewFree_explicateLF b]
  | .form _ b, cr => by simp only [explicateLF, Src.patsNewFree, patsNewFree_explicateLF b]

omit [DecidableEq S] in
theorem freePars_explicateLF : ∀ (t : Src S X) (cr : List X),
    (explicateLF cr t).freePars = t.freePars
  | .sym _, _ => rfl
  | .fn _, _ => rfl
  | .sv _, _ => rfl
  | .par _, _ => rfl
  | .quote _, _ => rfl
  | .pquote _, _ => rfl
  | .lam _ none b, cr => by simp only [explicateLF, Src.freePars, freePars_explicateLF b]
  | .lam _ (some _) b, cr => by simp only [explicateLF, Src.freePars, freePars_explicateLF b]
  | .app f a, cr => by
      simp only [explicateLF, Src.freePars, freePars_explicateLF f, freePars_explicateLF a]
  | .letS p w b _, cr => by
      simp only [explicateLF, Src.freePars, freePars_explicateLF p, freePars_explicateLF w,
        freePars_explicateLF b]
  | .unify p w b, cr => by
      simp only [explicateLF, Src.freePars, freePars_explicateLF p, freePars_explicateLF w,
        freePars_explicateLF b]
  | .alt t₁ t₂, cr => by
      simp only [explicateLF, Src.freePars, freePars_explicateLF t₁, freePars_explicateLF t₂]
  | .new _ b, cr => by simp only [explicateLF, Src.freePars, freePars_explicateLF b]
  | .form _ b, cr => by simp only [explicateLF, Src.freePars, freePars_explicateLF b]

omit [DecidableEq S] in
/-- Writing crossing sets keeps text admissible. -/
theorem admissible_explicateLF {t : Src S X} (admissible : t.Admissible) (cr : List X) :
    (explicateLF cr t).Admissible :=
  ⟨by rw [patsNewFree_explicateLF]; exact admissible.1,
    by rw [freePars_explicateLF]; exact admissible.2⟩

/-- **`toLexical` is exhausting exactly when every admissible program of
lexical fresh elaborates to what some admissible program elaborates to under
rule M**, up to the static equivalence. -/
theorem toLexicalMap_exhausting_iff (u : X) (unit : S) :
    (toLexicalMap (S := S) u unit).Exhausting ↔
      ∀ text' : Program S X, text'.Admissible → ∃ text : Program S X, text.Admissible ∧
        CoreEquiv (elabState cfgM u unit (.program text))
          (elabState cfgLF u unit (.program text')) :=
  translator_exhausting_iff _ _

omit [DecidableEq S] in
/-- **Reached, when the lambdas carry no crossing set**: the explicit form of
an admissible program of lexical fresh is an admissible program that rule M
elaborates to the same judgment. -/
theorem lexicalFresh_plain_reached (u : X) (unit : S) {text' : Program S X}
    (admissible : text'.Admissible) (plain : text'.All fun t => lamPlain t = true) :
    ∃ text : Program S X, text.Admissible ∧
      elabState cfgM u unit (.program text) = elabState cfgLF u unit (.program text') := by
  refine ⟨text'.map (explicateLF []), ?_, ?_⟩
  · exact Program.All.map (good := Src.Admissible) (good' := Src.Admissible) admissible
      fun t ht => admissible_explicateLF ht []
  · exact elabState_explicateLF .mercury .perCall .reference u unit plain

omit [DecidableEq S] in
/-- **Reached, when the program is explicit**: rule M elaborates it as lexical
fresh does. -/
theorem lexicalFresh_explicit_reached (u : X) (unit : S) {text' : Program S X}
    (admissible : text'.Admissible) (written : text'.Explicit) :
    ∃ text : Program S X, text.Admissible ∧
      elabState cfgM u unit (.program text) = elabState cfgLF u unit (.program text') :=
  ⟨text', admissible, elabState_explicit .mercury .lexicalFresh .perCall .reference u unit written⟩

#print axioms translator_hosting
#print axioms translator_exhausting_iff
#print axioms Translates.bag_length
#print axioms toLexical_core_equiv
#print axioms toLexicalMap_hosting
#print axioms toLexical_transfer
#print axioms translates_explicit
#print axioms translates_explicateEC
#print axioms translates_explicateQ
#print axioms translates_explicateLF
#print axioms translates_mercury
#print axioms explicit_hosts_explicitCapture_exhausting
#print axioms toLexicalMap_exhausting_iff
#print axioms lexicalFresh_plain_reached

end Mettapedia.GSLT.LanguageDef.ScopePolicies
