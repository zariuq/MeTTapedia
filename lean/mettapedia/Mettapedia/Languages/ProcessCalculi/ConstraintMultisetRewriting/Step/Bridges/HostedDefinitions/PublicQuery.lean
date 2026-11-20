import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.HostedDefinitions.ProgramLayout
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.HostedDefinitions.PublicReadout
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.HostedDefinitions.ContinuationLift
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.HostedDefinitions.TerminalAnswers
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting.ArrowHosting

/-!
# The public query filters interpreter replies through an actual source bind

The result key belongs to a real fixed library equation. The query uses it
at its own fresh bind scope and returns only the payload of a done reply.
No extra equation is added to allocate a key or to hide helper residuals.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.PublicQuery

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open SourceLanguage SourceLanguage.Elaboration

local instance msigClosed : ProgramBinders.ClosedTerms MSig where
  closed := fun | () => csym "unused"

variable (helpers authored : List ProgramLayout.Rule)

abbrev rows := ProgramLayout.rows helpers authored
abbrev keys := BinderCore.keys (rows helpers authored)
abbrev result := ProgramLayout.resultDatum helpers authored
abbrev site := ProgramLayout.resultSite helpers authored

def query {Ty : Type} (call : MClosed) : Comp (keys helpers authored) [] () Ty :=
  .let_ (site helpers authored) (PublicReadout.pattern (result helpers authored))
    (.apply (Rigid.includeTerm (fam (keys helpers authored)) call)) (.ret (result helpers authored))

def frame {Ty : Type} : Frame (keys helpers authored) [] () Ty :=
  .bindTo (site helpers authored) (PublicReadout.pattern (result helpers authored))
    (.ret (result helpers authored))

theorem initial_step (D : Discipline MSig [] ()) (supply : Nat → MClosed) (call : MClosed) :
    SourceLanguage.Step D (BinderCore.program (rows helpers authored)) supply
      (Config.initial (fun _ => 0) (query helpers authored (Ty := D.Ty) call))
      (ContinuationLift.configuration (frame helpers authored)
        (BinderCore.start (rows helpers authored) (Ty := D.Ty) call)) := by
  have live : Solvable ([] : List (Constraint (keys helpers authored) [] ())) :=
    ⟨Empty, ProgramBinders.ground MSig, ProgramBinders.close (fam (keys helpers authored)),
      fun _ inside => False.elim (List.not_mem_nil inside)⟩
  have moved := Move.letStart (D := D) (P := BinderCore.program (rows helpers authored)) (supply := supply)
    (⟨0, 0, fun _ => 0⟩ : World (keys helpers authored) [] ()) [] (site helpers authored)
    (PublicReadout.pattern (result helpers authored))
    (.apply (Rigid.includeTerm (fam (keys helpers authored)) call)) (.ret (result helpers authored)) [] []
  have one := SourceLanguage.Step.move (D := D) (P := BinderCore.program (rows helpers authored))
    (supply := supply) _ _ _ 0 _ live moved
  simpa [Config.initial, query, frame, BinderCore.start, ContinuationLift.configuration,
    ContinuationLift.branch] using one

theorem runs_inside (D : Discipline MSig [] ()) (supply : Nat → MClosed)
    [ProgramBinders.ClosedTerms MSig] {call : MClosed}
    {after : Config (keys helpers authored) [] () D.Ty}
    (executed : Runs D (BinderCore.program (rows helpers authored)) supply
      (BinderCore.start (rows helpers authored) call) after) :
    Runs D (BinderCore.program (rows helpers authored)) supply
      (Config.initial (fun _ => 0) (query helpers authored call))
      (ContinuationLift.configuration (frame helpers authored) after) :=
  (Relation.ReflTransGen.single (initial_step helpers authored D supply call)).trans
    (ContinuationLift.runs (rows helpers authored) D supply (frame helpers authored) executed)

theorem result_names (allowed : List (keys helpers authored).Site)
    (inside : site helpers authored ∈ allowed) :
    NamesIn allowed (result helpers authored) := by
  intro name member
  have same : name = ⟨[], ProgramLayout.resultKey helpers authored⟩ := by
    change name ∈ support (generator (fam (keys helpers authored))
      ⟨[], ProgramLayout.resultKey helpers authored⟩) at member
    simpa only [support_generator, List.mem_singleton] using member
  subst name
  exact ⟨rfl, inside⟩

theorem query_scoped (call : MClosed) {Ty : Type} :
    (query helpers authored (Ty := Ty) call).Scoped [ProgramLayout.querySite helpers authored] := by
  refine ⟨?_, ?_, result_names helpers authored _ List.mem_cons_self⟩
  · intro name member
    rw [Rigid.support_include] at member
    exact False.elim (List.not_mem_nil member)
  · intro name member
    have own := result_names helpers authored
      [site helpers authored, ProgramLayout.querySite helpers authored] List.mem_cons_self
    have used : name ∈ support (result helpers authored) := by
      simpa only [PublicReadout.pattern, Toolkit.tupleAt, Toolkit.tupleArgsAt, Toolkit.symAt,
        support, supportArgs, List.nil_append, List.append_nil] using member
    exact own name used

theorem query_distinct (call : MClosed) {Ty : Type} :
    (ProgramLayout.querySite helpers authored :: (query helpers authored (Ty := Ty) call).sites).Nodup := by
  exact List.nodup_cons.mpr ⟨by
    simpa only [query, Comp.sites, List.nil_append, List.append_nil, List.mem_singleton] using
      ProgramLayout.sites_distinct helpers authored,
    List.nodup_singleton _⟩

theorem query_arrows (call : MClosed) {Ty : Type} :
    Hosting.ArrowComp (query helpers authored (Ty := Ty) call) := by trivial

theorem opened_result (scope : Nat) :
    instantiate (openAt (keys helpers authored) (site helpers authored) scope) (result helpers authored) =
      instantiate (BinderCore.stamp (rows helpers authored) scope (site helpers authored))
        (RuleBuilder.slot (ProgramLayout.resultHole helpers authored)) := by
  change instantiate (openAt (keys helpers authored) (site helpers authored) scope)
    (generator (fam (keys helpers authored)) ⟨[], ProgramLayout.resultKey helpers authored⟩) =
      instantiate (BinderCore.stamp (rows helpers authored) scope (site helpers authored))
        (generator ((rows helpers authored).get (site helpers authored)).arity
          (ProgramLayout.resultHole helpers authored))
  rw [instantiate_generator, instantiate_generator]
  change generator (fam (keys helpers authored))
    ⟨if site helpers authored = site helpers authored then [scope] else [],
      ProgramLayout.resultKey helpers authored⟩ =
    generator (fam (keys helpers authored)) ⟨[scope], ProgramLayout.resultKey helpers authored⟩
  rw [if_pos rfl]

def groundResult (value : MClosed) : ((rows helpers authored).get (site helpers authored)).Ground :=
  fun _ => value

theorem extended_reads_result {X : Type} {family : X → MetaArity MSig}
    (assignment : Assignment (fam (keys helpers authored)) family) (scope : Nat) (value : MClosed) :
    instantiate
      (BinderCore.extend (rows helpers authored) assignment scope (site helpers authored)
        (groundResult helpers authored value))
      (instantiate (openAt (keys helpers authored) (site helpers authored) scope) (result helpers authored)) =
        Rigid.includeTerm family value := by
  rw [opened_result, BinderCore.extend_new]
  change instantiate
    ((fun _ : Fin 3 => Rigid.includeTerm family value) : Assignment (RuleBuilder.FoArity 3) family)
    (RuleBuilder.slot (0 : Fin 3)) = Rigid.includeTerm family value
  rw [RuleBuilder.instantiate_slot]

theorem bind_has_result {scope : Nat} {store : List (Constraint (keys helpers authored) [] ())}
    {reply : Data (keys helpers authored) [] ()} {value : MClosed}
    (fresh : BinderCore.Fresh (rows helpers authored) scope store reply)
    (read : Reads store reply (doneC value)) :
    Reads (store ++ [(instantiate (openAt (keys helpers authored) (site helpers authored) scope)
      (PublicReadout.pattern (result helpers authored)), reply)])
      (instantiate (openAt (keys helpers authored) (site helpers authored) scope) (result helpers authored)) value := by
  obtain ⟨X, family, assignment, solved, replyRead⟩ := read
  let extension := BinderCore.extend (rows helpers authored) assignment scope (site helpers authored)
    (groundResult helpers authored value)
  have output := extended_reads_result helpers authored assignment scope value
  have original : instantiate extension reply = Rigid.includeTerm family (doneC value) :=
    (BinderCore.extend_old (rows helpers authored) assignment scope (site helpers authored)
      (groundResult helpers authored value) fresh.2).trans replyRead
  refine ⟨X, family, extension, (models_append extension _ _).mpr ⟨?_, ?_⟩, output⟩
  · intro equation member
    rw [BinderCore.extend_old _ _ _ _ _ (fresh.1 equation member).1,
      BinderCore.extend_old _ _ _ _ _ (fresh.1 equation member).2]
    exact solved equation member
  · apply (models_singleton extension _).mpr
    rw [PublicReadout.instantiate_pattern, PublicReadout.instantiate_pattern, output, original]
    exact PublicReadout.include_done family value

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.PublicQuery

#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.PublicQuery.runs_inside
#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.PublicQuery.bind_has_result
