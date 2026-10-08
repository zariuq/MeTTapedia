import Mettapedia.GSLT.LanguageDef.ModuleAlgebra.Gluing
import Mettapedia.GSLT.LanguageDef.ScopePolicies.Witnesses

/-!
# Two regions of one file under two policies

A region is a set of equations written under one policy.  A file is the join
of its regions.  The declarations are those of the module algebra
(`ModuleAlgebra.Entry`, `Presentation`, `join`): the origin of a declaration is
its region and its name, its label the name it defines, its body the policy and
the text.

## What gluing needs

1. **No clash of names.**  Two regions join exactly when they are compatible
   (`ModuleAlgebra.join_eq_none_iff`): a name declared in both is one
   declaration.  `clash_no_join`: two regions that each define `mk`, under two
   policies, have no join.
2. **Elaboration by declaration.**  Each equation is elaborated as its own
   form under its own region's policy (`elabEntry`), so the equations of a
   join are those of its regions: `realizes_join`, and the universal property
   of the join for the elaborated clauses, `elabEntry_glue`.  Ownership and
   lifetime are carried by the elaborated clause; nothing more is needed for
   them.  In the identity model a file with a rule-M region and a
   lexical-fresh region is the lexical-fresh file whose rule-M equations are
   translated, term for term (`mixed_is_lexicalFresh`, `run_mixed`).
3. **One readout.**  The readout is not in the elaborated text.  A file runs
   under one discipline, and a region written for the other readout changes
   meaning: `readout_not_in_region`.
4. **Every name a region calls is declared where it is glued.**  A compatible
   join exists and is still not conservative: an equation name that a region
   calls and does not declare evaluates to itself in the region alone and to
   the other region's equation in the join (`join_not_conservative`).  This
   is the warning of `Dedukti.Composition.joined_not_confluentAt` in this
   setting: the join of two modules is a module, and has behaviour that
   neither has.

`two_regions_glue` is the positive example: a rule-M region and a
lexical-fresh region with different names join, and a query that calls the
rule-M equation has the same answers in the region and in the join.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ScopePolicies

open Mettapedia.GSLT
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.SequentialBindingDiscipline
open Mettapedia.GSLT.LanguageDef.TemplateScope
open Mettapedia.GSLT.LanguageDef.TemplateScope.IdSlot
open Mettapedia.GSLT.LanguageDef.TemplateScope.SpectrumCorpus

/-! ## Regions as declarations -/

/-- **A declaration of a region**: its origin is the region and the name; its
label is the name it defines; its body is the policy and the text. -/
abbrev RegionEntry (R S X : Type) := ModuleAlgebra.Entry (R × S) S (Config × Src S X)

/-- **A region, or a file**: a conflict-free finite set of declarations. -/
abbrev Regions (R S X : Type) [DecidableEq R] [DecidableEq S] [DecidableEq X] :=
  ModuleAlgebra.Presentation (R × S) S (Config × Src S X)

variable {R S X : Type} [DecidableEq R] [DecidableEq S] [DecidableEq X]

/-- **The elaborated clause of a declaration**, under its own region's
policy. -/
def elabEntry (u : X) (unit : S) (entry : RegionEntry R S X) : Tm S (Slot X) :=
  clauseOf entry.body.1 [5] u unit entry.body.2

/-- **A program realizes a file**: at each declared name it has the clause of
the declaration, and it has nothing at a name that is not declared. -/
def Realizes (u : X) (unit : S) (file : Regions R S X) (prog : S → Option (Tm S (Slot X))) :
    Prop :=
  (∀ entry ∈ file.val, prog entry.label = some (elabEntry u unit entry)) ∧
    ∀ F, (∀ entry ∈ file.val, entry.label ≠ F) → prog F = none

/-- A file has at most one program. -/
theorem Realizes.unique {u : X} {unit : S} {file : Regions R S X}
    {first second : S → Option (Tm S (Slot X))} (firstRealizes : Realizes u unit file first)
    (secondRealizes : Realizes u unit file second) : first = second := by
  funext F
  by_cases declared : ∃ entry ∈ file.val, entry.label = F
  · obtain ⟨entry, member, rfl⟩ := declared
    rw [firstRealizes.1 entry member, secondRealizes.1 entry member]
  · have absent : ∀ entry ∈ file.val, entry.label ≠ F :=
      fun entry member same => declared ⟨entry, member, same⟩
    rw [firstRealizes.2 F absent, secondRealizes.2 F absent]

/-- **The equations of a join are those of its regions.**  The program of the
first region, completed by the program of the second, realizes the join. -/
theorem realizes_join {u : X} {unit : S} {p q r : Regions R S X}
    (joined : ModuleAlgebra.join p q = some r) {first second : S → Option (Tm S (Slot X))}
    (firstRealizes : Realizes u unit p first) (secondRealizes : Realizes u unit q second) :
    Realizes u unit r fun F => (first F).orElse fun _ => second F := by
  have value := ModuleAlgebra.join_eq_some_iff.mp joined
  refine ⟨fun entry member => ?_, fun F absent => ?_⟩
  · have inUnion : entry ∈ p.val ∪ q.val := value ▸ member
    rcases Finset.mem_union.mp inUnion with inFirst | inSecond
    · simp only [firstRealizes.1 entry inFirst, Option.orElse_some]
    · by_cases declared : ∃ other ∈ p.val, other.label = entry.label
      · obtain ⟨other, otherMember, sameLabel⟩ := declared
        have same : other = entry :=
          r.property other (value ▸ Finset.mem_union_left _ otherMember) entry member
            (Or.inr sameLabel)
        subst same
        simp only [firstRealizes.1 other otherMember, Option.orElse_some]
      · have absent : ∀ other ∈ p.val, other.label ≠ entry.label :=
          fun other otherMember same => declared ⟨other, otherMember, same⟩
        simp only [firstRealizes.2 entry.label absent, Option.orElse_none,
          secondRealizes.1 entry inSecond]
  · have absentFirst : ∀ entry ∈ p.val, entry.label ≠ F :=
      fun entry member => absent entry (value ▸ Finset.mem_union_left _ member)
    have absentSecond : ∀ entry ∈ q.val, entry.label ≠ F :=
      fun entry member => absent entry (value ▸ Finset.mem_union_right _ member)
    simp only [firstRealizes.2 F absentFirst, Option.orElse_none, secondRealizes.2 F absentSecond]

/-- **The elaborated clauses glue along the join**: the map that elaborates
each declaration of the join is the one map that extends the elaboration of
the declarations of each region. -/
theorem elabEntry_glue {u : X} {unit : S} {p q r : Regions R S X}
    (joined : ModuleAlgebra.join p q = some r) :
    (fun entry : ModuleAlgebra.Member r => elabEntry u unit entry.val) =
      ModuleAlgebra.glue joined (fun entry : ModuleAlgebra.Member p => elabEntry u unit entry.val)
        (fun entry : ModuleAlgebra.Member q => elabEntry u unit entry.val) :=
  ModuleAlgebra.glue_unique joined _ _ _ (fun _ => rfl) (fun _ => rfl)

/-- **Gluing needs no clash of names**: two regions that declare one name
differently have no join. -/
theorem clash_no_join (p q : Regions R S X) {first second : RegionEntry R S X}
    (inFirst : first ∈ p.val) (inSecond : second ∈ q.val) (sameName : first.label = second.label)
    (differ : first ≠ second) : ModuleAlgebra.join p q = none :=
  (ModuleAlgebra.join_eq_none_iff p q).mpr fun compatible =>
    differ (compatible first inFirst second inSecond (Or.inr sameName))

/-! ## A file of one policy, and a file of two ownership policies -/

/-- The equations of a file whose equations each carry their policy. -/
def progRegions (u : X) (unit : S) (clauses : S → Option (Config × Src S X)) :
    S → Option (Tm S (Slot X)) :=
  fun F => (clauses F).map fun declaration => clauseOf declaration.1 [5] u unit declaration.2

omit [DecidableEq S] in
/-- A file of one policy has the equations of that policy. -/
theorem progRegions_uniform (c : Config) (u : X) (unit : S) (clauses : S → Option (Src S X)) :
    progRegions u unit (fun F => (clauses F).map fun body => (c, body)) =
      progSlot c u unit clauses := by
  funext F
  simp only [progRegions, progSlot, Option.map_map]
  rfl

/-- The identity-model equations of a file whose equations are each under rule
M or under lexical fresh. -/
def progMixed (u : X) (unit : S) (clauses : S → Option (Reading × Src S X)) :
    S → Option (Tm S (BId X)) :=
  fun F => (clauses F).map fun declaration =>
    clauseId [5] u unit
      (match declaration.1 with
        | .mercury => elabMFormAt [5] declaration.2
        | .lexicalFresh => elabLFFormAt [5] declaration.2)

/-- Translate the rule-M equations of such a file; keep the others. -/
def unifyRegions (clauses : S → Option (Reading × Src S X)) : S → Option (Src S X) :=
  fun F => (clauses F).map fun declaration =>
    match declaration.1 with
    | .mercury => toLexicalAt [5] declaration.2
    | .lexicalFresh => declaration.2

omit [DecidableEq S] in
/-- **A file with a rule-M region and a lexical-fresh region is the
lexical-fresh file whose rule-M equations are translated**, term for term, in
the identity model. -/
theorem mixed_is_lexicalFresh (u : X) (unit : S) (clauses : S → Option (Reading × Src S X)) :
    progMixed u unit clauses = progLF u unit (unifyRegions clauses) := by
  funext F
  simp only [progMixed, progLF, unifyRegions]
  cases clauses F with
  | none => rfl
  | some declaration =>
      obtain ⟨reading, body⟩ := declaration
      cases reading
      · simp only [Option.map_some, elabLFFormAt_toLexicalAt]
      · rfl

/-- So the two files run alike, at every discipline, fuel, path and store. -/
theorem run_mixed (u : X) (unit : S) (clauses : S → Option (Reading × Src S X)) (d : Disc)
    (n : ℕ) (π : Path) (σ : GStore S (BId X)) (t : Tm S (BId X)) :
    run d (progMixed u unit clauses) n π σ t =
      run d (progLF u unit (unifyRegions clauses)) n π σ t := by
  rw [mixed_is_lexicalFresh]

/-! ## Examples on the corpus -/

/-- The region `mercury`: `(= (mk) L)`, under rule M. -/
def mercuryEntry : RegionEntry String Sy Sp := ⟨("mercury", .mk), .mk, (cfgM, L)⟩

/-- The region `fresh`: `(= (Lf) L)`, under lexical fresh. -/
def freshEntry : RegionEntry String Sy Sp := ⟨("fresh", .Lf), .Lf, (cfgLF, L)⟩

/-- A second definition of `mk`, in the region `fresh`: two answers. -/
def clashEntry : RegionEntry String Sy Sp :=
  ⟨("fresh", .mk), .mk, (cfgLF, .alt (k .ok) (k .ok))⟩

theorem singleton_valid (entry : RegionEntry String Sy Sp) :
    ModuleAlgebra.Valid ({entry} : Finset (RegionEntry String Sy Sp)) := by
  intro first firstMember second secondMember _
  rw [Finset.mem_singleton.mp firstMember, Finset.mem_singleton.mp secondMember]

/-- The three regions. -/
def mercuryRegion : Regions String Sy Sp := ⟨{mercuryEntry}, singleton_valid _⟩
def freshRegion : Regions String Sy Sp := ⟨{freshEntry}, singleton_valid _⟩
def clashRegion : Regions String Sy Sp := ⟨{clashEntry}, singleton_valid _⟩

/-- The empty region. -/
def emptyRegion : Regions String Sy Sp := ModuleAlgebra.empty

/-- The program of a one-declaration region. -/
def singleProgram (entry : RegionEntry String Sy Sp) : Sy → Option T :=
  fun F => if F = entry.label then some (elabEntry Sp.u Sy.unit entry) else none

theorem singleProgram_realizes (entry : RegionEntry String Sy Sp) :
    Realizes Sp.u Sy.unit ⟨{entry}, singleton_valid entry⟩ (singleProgram entry) := by
  refine ⟨fun other member => ?_, fun F absent => ?_⟩
  · rw [Finset.mem_singleton.mp member]
    simp [singleProgram]
  · have differ : F ≠ entry.label := fun same =>
      absent entry (Finset.mem_singleton.mpr rfl) same.symm
    simp [singleProgram, differ]

theorem emptyProgram_realizes : Realizes Sp.u Sy.unit emptyRegion fun _ => none :=
  ⟨fun _ member => absurd member (Finset.notMem_empty _), fun _ _ => rfl⟩

/-- **Positive: a rule-M region and a lexical-fresh region join.** -/
theorem two_regions_join :
    ∃ file : Regions String Sy Sp, ModuleAlgebra.join mercuryRegion freshRegion = some file := by
  have compatible : ModuleAlgebra.Compatible mercuryRegion.val freshRegion.val := by
    intro first firstMember second secondMember overlap
    rw [Finset.mem_singleton.mp firstMember, Finset.mem_singleton.mp secondMember] at overlap ⊢
    rcases overlap with sameOrigin | sameLabel
    · exact absurd sameOrigin (by decide)
    · exact absurd sameLabel (by decide)
  exact ⟨⟨mercuryRegion.val ∪ freshRegion.val,
    ModuleAlgebra.valid_union_iff.mpr ⟨mercuryRegion.property, freshRegion.property, compatible⟩⟩,
    ModuleAlgebra.join_eq_some_iff.mpr rfl⟩

/-- The program of the joined file. -/
def joinedProgram : Sy → Option T :=
  fun F => (singleProgram mercuryEntry F).orElse fun _ => singleProgram freshEntry F

/-- It realizes every join of the two regions. -/
theorem joinedProgram_realizes {file : Regions String Sy Sp}
    (joined : ModuleAlgebra.join mercuryRegion freshRegion = some file) :
    Realizes Sp.u Sy.unit file joinedProgram :=
  realizes_join joined (singleProgram_realizes mercuryEntry) (singleProgram_realizes freshEntry)

set_option maxRecDepth 100000 in
/-- **Positive: the query of the rule-M region keeps its answers in the
join.**  `(let $f (mk) (Pair ($f 1) ($f 2)))` (row 13a) calls the equation of
the rule-M region only. -/
theorem two_regions_glue :
    answers .static joinedProgram 80 (elabCfg cfgM [] row13a) =
      answers .static (singleProgram mercuryEntry) 80 (elabCfg cfgM [] row13a) ∧
    (answers .static joinedProgram 80 (elabCfg cfgM [] row13a)).map List.length = some 1 := by
  refine ⟨?_, ?_⟩ <;> decide +kernel

/-- **Negative: a clash.**  The regions `mercury` and `fresh`, each defining
`mk`, have no join. -/
theorem clash_example : ModuleAlgebra.join mercuryRegion clashRegion = none :=
  clash_no_join mercuryRegion clashRegion (first := mercuryEntry) (second := clashEntry)
    (Finset.mem_singleton.mpr rfl) (Finset.mem_singleton.mpr rfl) rfl (by decide)

set_option maxRecDepth 100000 in
/-- **Negative: a join that exists and is not conservative.**  The empty
region and the region that defines `mk` with two answers are compatible.  The
query `(mk)` has one result in the empty region, the name itself, and two in
the join. -/
theorem join_not_conservative :
    ModuleAlgebra.join emptyRegion clashRegion = some clashRegion ∧
    Realizes Sp.u Sy.unit emptyRegion (fun _ => none) ∧
    Realizes Sp.u Sy.unit clashRegion (singleProgram clashEntry) ∧
    (run .static (fun _ => none) 80 [] Store.empty (.fn .mk : T)).map List.length = some 1 ∧
    (run .static (singleProgram clashEntry) 80 [] Store.empty (.fn .mk : T)).map List.length =
      some 2 := by
  refine ⟨?_, emptyProgram_realizes, singleProgram_realizes clashEntry, ?_, ?_⟩
  · exact ModuleAlgebra.join_eq_some_iff.mpr (Finset.empty_union _)
  · decide +kernel
  · decide +kernel

/-- **Negative: the readout is not in a region's text.**  Row 6 elaborates to
one judgment up to the discipline under the two readouts of rule M; under the
reference discipline it has no result, under the snapshot discipline one. -/
theorem readout_not_in_region :
    progSlot cfgM Sp.u Sy.unit clauses = progSlot cfgSN Sp.u Sy.unit clauses ∧
    elabCfg cfgM [] row6 = elabCfg cfgSN [] row6 ∧
    (∃ bag, run .static (progSlot cfgM Sp.u Sy.unit clauses) 80 [] Store.empty
        (elabCfg cfgM [] row6) = some bag ∧ bag.length = 0) ∧
    ∃ bag, run .copyAtCall (progSlot cfgM Sp.u Sy.unit clauses) 80 [] Store.empty
        (elabCfg cfgM [] row6) = some bag ∧ bag.length = 1 := by
  obtain ⟨none, answer, one⟩ := row6_answers
  obtain ⟨bag, defined, length⟩ := run_of_answersCfg none
  obtain ⟨bag', defined', length'⟩ := run_of_answersCfg one
  exact ⟨rfl, rfl, ⟨bag, defined, length⟩, ⟨bag', defined', length'⟩⟩

#print axioms realizes_join
#print axioms elabEntry_glue
#print axioms clash_no_join
#print axioms mixed_is_lexicalFresh
#print axioms two_regions_glue
#print axioms join_not_conservative
#print axioms readout_not_in_region

end Mettapedia.GSLT.LanguageDef.ScopePolicies
