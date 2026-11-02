import Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalogPrinterAtomLaws

/-! Rule printing retains the ordered premise list and the head through
source projection, including anonymous arguments and comparison guards. -/

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalog.SourcePrinter

open Mettapedia.OSLF.MeTTaIL Syntax
open Mettapedia.Languages.Datalog
open ProgramProjection

theorem body_projection (first : Pattern) (rest : List Pattern) :
    Reference.body? (nonemptySeparated "body-one" "body-more" first rest) =
      (first :: rest).mapM Reference.positiveLiteral? := by
  induction rest generalizing first with
  | nil =>
      change (Reference.positiveLiteral? first).map (· :: []) = _
      cases read : Reference.positiveLiteral? first <;> simp [List.mapM_cons, read]
  | cons second tail ih =>
      change ((Reference.positiveLiteral? first).bind fun head =>
        (Reference.body? (nonemptySeparated "body-one" "body-more" second tail)).bind
          fun rest => some (head :: rest)) = _
      rw [ih]
      simp only [List.mapM_cons, Option.bind_eq_bind, Option.pure_def]

theorem body_read (values : List Mettapedia.Languages.Datalog.Premise) (first : Pattern) (rest : List Pattern)
    (built : values.mapM premise? = .ok (first :: rest)) :
    (Reference.body? (nonemptySeparated "body-one" "body-more" first rest)).bind Frontend.normalizeChildren? =
      some (values.map IRCodec.premise) := by
  rw [body_projection]
  simp_rw [normalize_children_mapM]
  rw [mapM_bind]
  exact mapM_read premise? _ IRCodec.premise premise_read values (first :: rest) built

theorem clause_read (clause : Clause) (source : Pattern) (built : clause? clause = .ok source) :
    (Reference.rule? source).bind Frontend.normalize? = some (.apply "PositiveRule" [IRCodec.clause clause]) := by
  by_cases emptyBody : clause.body.isEmpty = true
  · simp only [clause?, emptyBody, ↓reduceIte] at built
    cases built
  · cases headRead : atom? clause.head with
    | error reason => simp only [clause?, emptyBody, headRead] at built; cases built
    | ok head =>
        cases bodyRead : clause.body.mapM premise? with
        | error reason => simp only [clause?, emptyBody, headRead, bodyRead] at built; cases built
        | ok body =>
            cases body with
            | nil => simp only [clause?, emptyBody, headRead, bodyRead] at built; cases built
            | cons first rest =>
                simp only [clause?, emptyBody, headRead, bodyRead] at built
                have same : node "rule" [head,space,space,nonemptySeparated "body-one" "body-more" first rest] = source :=
                  Except.ok.inj built
                subst source
                obtain ⟨name,arguments,headProjected,nameNormalized,argsNormalized⟩ := atom_read clause.head head headRead
                have bodyNormalized := body_read clause.body first rest bodyRead
                cases bodyProjected : Reference.body? (nonemptySeparated "body-one" "body-more" first rest) with
                | none => simp [bodyProjected] at bodyNormalized
                | some bodyCode =>
                    simp only [bodyProjected, Option.bind_some] at bodyNormalized
                    have projected : Reference.rule? (node "rule"
                        [head,space,space,nonemptySeparated "body-one" "body-more" first rest]) =
                        some (.apply "PositiveRule" [.apply "Clause" [name,arguments,Reference.vector bodyCode]]) := by
                      change ((Reference.atom? head).bind fun pair =>
                        (Reference.body? (nonemptySeparated "body-one" "body-more" first rest)).bind fun body =>
                          some (Pattern.apply "PositiveRule" [.apply "Clause" [pair.1,pair.2,Reference.vector body]])) = _
                      rw [headProjected, bodyProjected]
                      rfl
                    rw [projected]
                    change Frontend.normalize? (.apply "PositiveRule" [.apply "Clause" [name,arguments,Reference.vector bodyCode]]) = _
                    have clauseNormalized : Frontend.normalize? (.apply "Clause" [name,arguments,Reference.vector bodyCode]) =
                        some (IRCodec.clause clause) := by
                      apply normalize_node _ _ _ (by simp [SourceMeaning.PlainNode])
                      simp only [Frontend.normalizeChildren?, nameNormalized, argsNormalized,
                        normalize_vector _ _ bodyNormalized, Option.bind_eq_bind, Option.bind_some]
                      rfl
                    apply normalize_node _ _ _ (by simp [SourceMeaning.PlainNode])
                    simp only [Frontend.normalizeChildren?, clauseNormalized, Option.bind_eq_bind, Option.bind_some]
                    rfl

end Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalog.SourcePrinter
