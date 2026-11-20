import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting.Composition.Neighbours
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting.Composition.Systems
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting.Divergence.Systems

/-!
# The hosted program beside a neighbour, as a readback with silent steps; the union of two programs

* `programSystem Prog`: the step of any program at the contextual frames, as a system.
* `neighbourReadback`: **the union of a translated program with a disciplined neighbour's rules reads
  back to the source** (`GSLT.IndexedOperational.OperationalReadback`): a state tracks a configuration
  when it represents one of its alternatives beside rows that never read as alternatives' rows; a
  firing of the translated program is one step of the configuration, and a firing of the neighbour is
  silent (the configuration stays). `Neighbours.runs_reflected_neighbour` is its reflection of runs.
  So it composes with every readback of the tree (`OperationalReadback.comp`). There is no forward
  half at this relation: a configuration is followed by a frontier of several states
  (`runs_forward_beside`).
* `besideCorrespondence`: **alternative by alternative, beside rows that never read as alternatives'
  rows or as equation rows, the hosting is an operational correspondence**
  (`GSLT.IndexedOperational.OperationalCorrespondence`): `simulation_beside` is its forward law and
  `reflection_beside` its readback, with no silent step.
* `union_answers`: **the union of the hosted systems of two programs answers as the union of the
  programs**: from the start of the union of the systems (`hosted_union`, `start_union`), the answers
  the step shows are, as a set, the source's answers of the union. What the union answers is the
  source language's law, and it is not what either program answers alone: an equation of one program
  that matches a call of the other changes that call's answer (`Controls.only_d` against
  `Controls.p0_only_g`).
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting.Composition

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open SourceLanguage
open Mettapedia.GSLT.IndexedOperational (OperationalReadback)

variable {S : Signature} {Γ : Ctx S} {star : S.Srt} (N : Nodes S Γ star) {κ : Keys S}

/-- **The step of a program at the contextual frames, as a system.** -/
def programSystem (Prog : RuleSyntax.Program (RuleSyntax.Contextual.Terms S)) : Mettapedia.GSLT.GSLT where
  Term := HostState S
  equations := ⟨Eq, ⟨Eq.refl, Eq.symm, Eq.trans⟩⟩
  rewrites := FiresIn Prog
  rewrites_resp_left := by
    rintro t t' u same step
    subst same
    exact ⟨u, step, rfl⟩
  rewrites_resp_right := by
    rintro t u u' step same
    subst same
    exact step

variable {D : Discipline S Γ star} {P : SourceLanguage.Program κ Γ star D.Ty} {supply : ℕ → Term S Γ star}
  (spaces : Term S Γ star → Multiset (Row κ Γ star)) (q : Comp κ Γ star D.Ty)

/-- **A state tracks a configuration beside other rows**: the configuration is reached from the query,
and the state represents one of its alternatives beside rows that never read as alternatives' rows. -/
def TracksBeside (P : SourceLanguage.Program κ Γ star D.Ty) (supply : ℕ → Term S Γ star)
    (C : Config κ Γ star D.Ty) (w : HostState S) : Prop :=
  Runs D P supply (Config.initial spaces q) C ∧
    ∃ b a others, b ∈ C.branches ∧ Beside N P C.world.scope b w a others ∧
      NeverReads (IsAlternative N) w others ∧ ArrowBranch b

/-- **The union with a disciplined neighbour's rules reads back to the source**, with the neighbour's
firings silent. -/
def neighbourReadback
    (equations : ∀ e ∈ P.equations, e.Scoped ∧ (e.site :: e.rhs.sites).Nodup ∧ ArrowComp e.rhs)
    {qsite : κ.Site} (qScoped : q.Scoped [qsite]) (qDistinct : (qsite :: q.sites).Nodup)
    (arrowQ : ArrowComp q) {R : RuleSyntax.Program (RuleSyntax.Contextual.Terms S)}
    (disciplined : Disciplined N P R) :
    OperationalReadback (Divergence.sourceSystem D P supply) (programSystem (translate N P ∪ R)) where
  related := TracksBeside N spaces q P supply
  readStep := by
    rintro C w w' ⟨runs, b, a, others, member, beside, quiet, arrow⟩ fires
    rcases (firesIn_union _ _ _ _).mp fires with hosted | ⟨f, admitted, rfl⟩
    · have hygienic := reachableHygienic_of_scoped spaces q equations qScoped qDistinct arrowQ C runs b member
      obtain ⟨v', bs, b', a', move, child, beside', kept, arrow'⟩ :=
        reflection_beside N (supply := supply) (fun e inside => (equations e inside).2.2) beside quiet arrow
          hygienic hosted
      obtain ⟨rest, split⟩ := Multiset.exists_cons_of_mem member
      have step : SourceLanguage.Step D P supply C ⟨v', bs + rest⟩ := by
        obtain ⟨world, branches⟩ := C
        simp only at split
        subst split
        exact .move world v' b rest bs (live_beside N beside hosted) move
      exact .inr ⟨⟨v', bs + rest⟩, step, runs.tail step, b', a', others, Multiset.mem_add.mpr (.inl child),
        beside', kept _ quiet, arrow'⟩
    · obtain ⟨apart, made⟩ := disciplined f beside quiet admitted
      exact .inl ⟨runs, b, a, _, member, beside_after_other N beside admitted apart,
        neverReads_fire admitted (others_sub N beside) quiet made, arrow⟩

/-- **A state represents an alternative with its world beside the rows `others`**, which never read as
alternatives' rows or as equation rows. -/
def RepresentsBeside (P : SourceLanguage.Program κ Γ star D.Ty) (others : Finset ℕ)
    (x : World κ Γ star × Branch κ Γ star D.Ty) (w : HostState S) : Prop :=
  ∃ a, Beside N P x.1.scope x.2 w a others ∧ ArrowBranch x.2 ∧ Scoping x.1.scope x.2 ∧
    NeverReads (IsAlternative N) w others ∧ NeverReads (IsEquationRow N) w others

/-- **Beside rows that never read as alternatives' rows or as equation rows, the hosting is an
operational correspondence, alternative by alternative**: every firing of the translated program is
one move, and every move is one firing. Beside no row it is `Divergence.alternativesCorrespondence`. -/
def besideCorrespondence
    (equations : ∀ e ∈ P.equations, e.Scoped ∧ (e.site :: e.rhs.sites).Nodup ∧ ArrowComp e.rhs)
    (others : Finset ℕ) :
    Mettapedia.GSLT.IndexedOperational.OperationalCorrespondence (Divergence.alternativeSystem D P supply)
      (Divergence.hostSystem N P) where
  related := RepresentsBeside N P others
  readStep := by
    rintro ⟨v, b⟩ w w' ⟨a, beside, arrow, ⟨Vis, L, Ls, inv⟩, noAlternative, noEquationRow⟩ fires
    obtain ⟨v', bs, b', a', move, child, beside', kept, arrow'⟩ :=
      reflection_beside N (supply := supply) (fun e inside => (equations e inside).2.2) beside noAlternative
        arrow (hygienic_of_scopedAt inv) fires
    have live' : Solvable b'.store := by
      obtain ⟨f, admitted, rfl⟩ := fires
      obtain ⟨B, u, solved⟩ := admitted.2.2.1
      obtain ⟨σ, solvedσ, _⟩ := (beside'.hosted.reads B _).mp ⟨u, solved, rfl⟩
      exact ⟨B.Names, B.arity, σ, solvedσ⟩
    exact .inr ⟨(v', b'), ⟨live_beside N beside fires, bs, move, child, live'⟩, a', beside', arrow',
      scopedAt_children equations move inv b' child, kept _ noAlternative, kept _ noEquationRow⟩
  forward := by
    rintro ⟨v, b⟩ ⟨v', b'⟩ w ⟨a, beside, arrow, ⟨Vis, L, Ls, inv⟩, noAlternative, noEquationRow⟩
      ⟨_, bs, move, child, live⟩
    obtain ⟨w', a', fires, beside', kept, arrow'⟩ :=
      simulation_beside N (fun e inside => (equations e inside).2.2) move beside arrow
        (hygienic_of_scopedAt inv) (fun _ _ _ => noMatchingRow_of_neverReads N noEquationRow) child live
    exact ⟨w', ⟨.cons ⟨fires⟩ (.refl _)⟩, a', beside', arrow', scopedAt_children equations move inv b' child,
      kept _ noAlternative, kept _ noEquationRow⟩

/-- **The union of the hosted systems of two programs answers as the union of the programs**: from the
start of the union of the two systems, the answers the step shows are, as a set, the source's answers
of the union of the programs. -/
theorem union_answers {Q : SourceLanguage.Program κ Γ star D.Ty}
    (equations : ∀ e ∈ (P.union Q).equations, e.Scoped ∧ (e.site :: e.rhs.sites).Nodup ∧ ArrowComp e.rhs)
    {qsite : κ.Site} (qScoped : q.Scoped [qsite]) (qDistinct : (qsite :: q.sites).Nodup)
    (arrowQ : ArrowComp q) :
    stepAnswersFrom N (P.union Q) (((hosted N P).union (hosted N Q)).start N q) =
      Answers.sourceAnswers D (P.union Q) supply spaces q := by
  rw [← start_union, stepAnswersFrom_start]
  exact Answers.arrow_answers_as_sets N spaces q equations qScoped qDistinct arrowQ

#print axioms neighbourReadback
#print axioms besideCorrespondence
#print axioms union_answers

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting.Composition
