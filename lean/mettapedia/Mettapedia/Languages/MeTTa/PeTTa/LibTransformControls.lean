import Mettapedia.Languages.MeTTa.PeTTa.LibTransform

/-!
# Controls for the laws of PeTTa's transform library

Each law of `LibTransform` with a positive and a negative control, computed by the kernel:

* Law 1. Reads alone answer as `match` does: duplicates (`reads_keep_duplicates`), a join
  (`reads_join`), an `all` extension giving every pair (`reads_all_every_pair`). A value
  bound to a comma expression is one instance (`comma_value_one_instance`); a `,` template
  gives one answer per component where `match` gives one (`comma_template_splits`), and a
  `once` among the reads answers the first match only (`reads_with_once_differ_from_match`).
* Law 2. Two takes of one atom need two stored copies (`double_take_one_copy`,
  `double_take_two_copies`); a read and a take of one atom need a spare copy
  (`read_and_take_one_copy`, `read_and_take_two_copies`). The copies a firing does not take
  are stored back after the others (`take_one_of_two_moves_the_rest`).
* Law 3. Two branches contend for one token: the first fires, the second fires nothing
  (`tokens_contend`). Each stored copy of a token is its own match, so two copies give the
  first reader two proposals, which take both (`tokens_copies_are_matches`); branches with
  disjoint takes all fire (`tokens_disjoint`).
* Law 4. `once` skips a proposal whose firing does not validate (`once_skips_invalid`) and
  into the store answers the first firing's count (`once_into_counts`). A firing with no
  instance answers nothing, so `once` goes on and fires the next branch too
  (`once_after_empty_firing`).
* Law 5. `(all (take p))` and `(collect (take p) C)` take every match in one firing
  (`all_take_everything`, `collect_take_everything`); a firing that also reads a collected
  atom never validates (`collect_take_and_read`). `(once (take p))` takes one copy
  (`once_take_one_copy`), where a kernel `(take p)` fires once per proposal
  (`kernel_take_every_copy`); `(, (once p) (all q))` commits the first `p` with all its
  `q` (`once_then_all`).
* Conditions at firing. A `unique` branch whose pattern gained a second match before it
  ran fires nothing (`unique_counted_at_firing`), and one whose unique atom was replaced by
  another fires nothing although the count holds again (`unique_needs_its_atom`,
  `unique_replaced_fires_nothing`). Re-checking the proposal's substitution
  instead would fire it (`substitution_recheck_fires`). A `collect` is rebound at firing
  (`collect_rebound_at_firing`, `collect_after_a_take`), and a `collect` pattern variable
  bound by a later conjunct is free when it is collected (`collect_bound_later_fires`,
  `collect_bound_before_fires`).
* Law 6, after the library's `transform_conjunctions` tests. `(absent (, (p $x) (q $x)))`
  holds on `(p 1) (q 2)`, where `absent` of either part blocks (`absent_joint_holds`), and
  blocks once `(q 1)` is stored (`absent_joint_blocks`). One stored `a` is a joint match of
  `(, a a)`: `absent` blocks, a read `unique` fires, a read `collect` collects `(, a a)`
  (`reads_meet_one_occurrence_twice`). A `unique` over two parts with exactly one tuple
  proposes both parts and takes them (`unique_joint_one_tuple`); with two tuples it fires
  nothing (`unique_joint_two_tuples`). A take `unique` of `(, a a)` does not validate on one
  copy and has four tuples on two, while `(, a b)` takes both
  (`unique_take_needs_distinct_occurrences`). A branch whose joint tuple was replaced before
  it ran fires nothing (`unique_joint_replaced_fires_nothing`). A `collect` over a
  conjunction binds the list of tuples (`collect_joint`); a take-mode one after a read takes
  the tuples' atoms (`collect_take_joint_after_read`), every stored copy of each
  participant, shared or stored twice (`collect_take_every_copy`); over `(, a a)` it keeps
  and takes nothing on one copy and both copies on two
  (`collect_take_needs_fitting_tuples`).
* Law 7. A one-part conjunction collects one-part tuples where its pattern collects atoms,
  and in take mode leaves the same store (`collect_one_part_wraps`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.LibTransform.Controls

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)

private def sym (name : String) : Atom := .symbol name
private def v (name : String) : Atom := .var name
private def ex (items : List Atom) : Atom := .expression items
private def p (x : Atom) : Atom := ex [sym "p", x]
private def q (x : Atom) : Atom := ex [sym "q", x]
private def tok : Atom := ex [sym "tok"]

/-! ## Law 1: reads alone -/

theorem reads_keep_duplicates :
    (transform (readSources [p (v "x")] none) (v "x")
      [p (sym "1"), p (sym "2"), p (sym "1")]).drain =
    ([sym "1", sym "2", sym "1"], [p (sym "1"), p (sym "2"), p (sym "1")]) ∧
    matchAnswers [p (sym "1"), p (sym "2"), p (sym "1")] [p (v "x")] (v "x") =
      [sym "1", sym "2", sym "1"] := by
  decide

private def joinStore : Store := [p (sym "1"), p (sym "2"), q (sym "2"), q (sym "2")]

theorem reads_join :
    (transform (readSources [p (v "x"), q (v "x")] none) (ex [sym "both", v "x"])
      joinStore).drain =
      (matchAnswers joinStore [p (v "x"), q (v "x")] (ex [sym "both", v "x"]), joinStore) ∧
    matchAnswers joinStore [p (v "x"), q (v "x")] (ex [sym "both", v "x"]) =
      [ex [sym "both", sym "2"], ex [sym "both", sym "2"]] := by
  decide

theorem reads_all_every_pair :
    (transform (readSources [p (v "x")] (some [q (v "y")])) (ex [sym "pair", v "x", v "y"])
      [p (sym "1"), q (sym "a"), q (sym "b"), p (sym "2")]).drain =
    ([ex [sym "pair", sym "1", sym "a"], ex [sym "pair", sym "1", sym "b"],
      ex [sym "pair", sym "2", sym "a"], ex [sym "pair", sym "2", sym "b"]],
      [p (sym "1"), q (sym "a"), q (sym "b"), p (sym "2")]) := by
  decide

private def commaValue : Atom := ex [sym ",", sym "a", sym "b"]

/-- A value bound to a comma expression is one instance, to the caller and into a space. -/
theorem comma_value_one_instance :
    (transform (readSources [ex [sym "v", v "x"]] none) (v "x")
      [ex [sym "v", commaValue]]).drain = ([commaValue], [ex [sym "v", commaValue]]) ∧
    matchAnswers [ex [sym "v", commaValue]] [ex [sym "v", v "x"]] (v "x") = [commaValue] ∧
    (transformInto (readSources [ex [sym "v", v "x"]] none) (v "x")
      [ex [sym "v", commaValue]]).drain = ([1], [ex [sym "v", commaValue], commaValue]) := by
  decide

/-- A `,` template is a conjunction of instances: two answers per match where `match`
answers one. -/
theorem comma_template_splits :
    (transform (readSources [p (v "x")] none) (ex [sym ",", v "x", v "x"]) [p (sym "1")]).drain =
      ([sym "1", sym "1"], [p (sym "1")]) ∧
    matchAnswers [p (sym "1")] [p (v "x")] (ex [sym ",", v "x", v "x"]) =
      [ex [sym ",", sym "1", sym "1"]] := by
  decide

private def pq : Store := [p (sym "1"), p (sym "2"), q (sym "a"), q (sym "b")]

private def readsOnce : Sources :=
  { kernel := [.pat .read (p (v "x"))], choice := [.pat .read (q (v "y"))] }

/-- `(, (p $x) (once (q $y)))` only reads, yet answers the first `q` for each `p`, where
`match` on `(, (p $x) (q $y))` answers every pair. -/
theorem reads_with_once_differ_from_match :
    (transform readsOnce (ex [sym "pair", v "x", v "y"]) pq).drain =
      ([ex [sym "pair", sym "1", sym "a"], ex [sym "pair", sym "2", sym "a"]], pq) ∧
    (matchAnswers pq [p (v "x"), q (v "y")] (ex [sym "pair", v "x", v "y"])).length = 4 := by
  decide

/-! ## Law 2: atomicity -/

private def twoTakes : Sources := { kernel := [.pat .take (sym "a"), .pat .take (sym "a")] }

theorem double_take_one_copy :
    proposals [sym "a"] twoTakes = [[(.take, sym "a"), (.take, sym "a")]] ∧
    fire [sym "a"] [(.take, sym "a"), (.take, sym "a")] twoTakes (instances (sym "done")) =
      none ∧
    (transform twoTakes (sym "done") [sym "a"]).drain = ([], [sym "a"]) := by
  decide

theorem double_take_two_copies :
    (transform twoTakes (sym "done") [sym "a", sym "a"]).drain = ([sym "done"], []) ∧
    (proposals [sym "a", sym "a"] twoTakes).length = 4 := by
  decide

private def readAndTake : Sources := { kernel := [.pat .read (sym "a"), .pat .take (sym "a")] }

theorem read_and_take_one_copy :
    (transform readAndTake (sym "done") [sym "a"]).drain = ([], [sym "a"]) := by
  decide

theorem read_and_take_two_copies :
    (transform readAndTake (sym "done") [sym "a", sym "a"]).drain =
      ([sym "done"], [sym "a"]) := by
  decide

theorem take_one_of_two_moves_the_rest :
    fire [sym "a", sym "b", sym "a"] [(.take, sym "a")] { kernel := [.pat .take (sym "a")] }
      (instances (sym "done")) = some ([sym "b", sym "a"], [sym "done"]) := by
  decide

/-! ## Law 3: branches -/

private def contend : Sources :=
  { kernel := [.pat .read (ex [sym "who", v "w"]), .pat .take tok] }

theorem tokens_contend :
    (transform contend (ex [sym "got", v "w"])
      [ex [sym "who", sym "x"], ex [sym "who", sym "y"], tok]).drain =
    ([ex [sym "got", sym "x"]], [ex [sym "who", sym "x"], ex [sym "who", sym "y"]]) := by
  decide

/-- Each copy of the token is a separate match, so `(who x)` has two proposals, and they
take both copies before `(who y)` runs. -/
theorem tokens_copies_are_matches :
    (transform contend (ex [sym "got", v "w"])
      [ex [sym "who", sym "x"], ex [sym "who", sym "y"], tok, tok]).drain =
    ([ex [sym "got", sym "x"], ex [sym "got", sym "x"]],
      [ex [sym "who", sym "x"], ex [sym "who", sym "y"]]) := by
  decide

/-- Branches whose takes are disjoint all fire. -/
theorem tokens_disjoint :
    (transform
        { kernel := [.pat .read (ex [sym "who", v "w"]), .pat .take (ex [sym "tok", v "w"])] }
      (ex [sym "got", v "w"])
      [ex [sym "who", sym "x"], ex [sym "who", sym "y"], ex [sym "tok", sym "x"],
        ex [sym "tok", sym "y"]]).drain =
    ([ex [sym "got", sym "x"], ex [sym "got", sym "y"]],
      [ex [sym "who", sym "x"], ex [sym "who", sym "y"]]) := by
  decide

/-! ## Law 4: `once` -/

private def c (x : Atom) : Atom := ex [sym "c", x]

/-- The first proposal, `$x = 1`, takes `(c 1)` twice and does not validate; the first that
holds is `$x = 2`. -/
theorem once_skips_invalid :
    (Search.once (transform { kernel := [.pat .take (c (v "x")), .pat .take (c (v "x"))] }
      (v "x")) [c (sym "1"), c (sym "2"), c (sym "2")]).first? =
      some (sym "2", [c (sym "1")]) := by
  decide

theorem once_into_counts :
    (Search.once (transformInto { kernel := [.pat .take (c (v "x"))] } (ex [sym "d", v "x"]))
      [c (sym "1"), c (sym "2")]).first? =
      some (1, [c (sym "2"), ex [sym "d", sym "1"]]) := by
  decide

/-- The first proposal fires but its `all` has no extension, so it answers nothing; `once`
goes on, and the second proposal fires too: both `(k 1)` and `(k 2)` are taken. -/
theorem once_after_empty_firing :
    (Search.once (transform
        { kernel := [.pat .take (ex [sym "k", v "x"])],
          every := some [.pat .read (ex [sym "m", v "x"])] }
        (ex [sym "out", v "x"]))
      [ex [sym "k", sym "1"], ex [sym "k", sym "2"], ex [sym "m", sym "2"]]).first? =
      some (ex [sym "out", sym "2"], [ex [sym "m", sym "2"]]) := by
  decide

/-! ## Law 5: `all` and `collect` takes -/

theorem all_take_everything :
    (transform (allTake (p (v "x"))) (v "x")
      [p (sym "1"), q (sym "1"), p (sym "2"), p (sym "1")]).drain =
    ([sym "1", sym "2", sym "1"], [q (sym "1")]) := by
  decide

theorem collect_take_everything :
    (transform (collectTake (p (v "x")) "C") (ex [sym "got", v "C"])
      [p (sym "1"), q (sym "1"), p (sym "2"), p (sym "1")]).drain =
    ([ex [sym "got", ex [p (sym "1"), p (sym "2"), p (sym "1")]]], [q (sym "1")]) := by
  decide

/-- Reading `(p 1)` and collecting-taking every `(p $x)` needs one more copy of `(p 1)`
than are stored, so it never fires. -/
theorem collect_take_and_read :
    (transform { kernel := [.pat .read (p (sym "1")), .collect .take (.one (p (v "x"))) (v "C")] }
      (v "C") [p (sym "1"), p (sym "2")]).drain = ([], [p (sym "1"), p (sym "2")]) := by
  decide

theorem once_take_one_copy :
    (transform (onceTake tok) (sym "done") [tok, tok]).drain = ([sym "done"], [tok]) := by
  decide

theorem kernel_take_every_copy :
    (transform { kernel := [.pat .take tok] } (sym "done") [tok, tok]).drain =
      ([sym "done", sym "done"], []) := by
  decide

private def onceAll : Sources :=
  { kernel := [], choice := [.pat .read (p (v "x"))], every := some [.pat .read (q (v "y"))] }

/-- `(, (once (p $x)) (all (q $y)))`: one branch, whose firing commits the first `p` with
all of its `q` extensions. -/
theorem once_then_all :
    (transform onceAll (ex [sym "pair", v "x", v "y"]) pq).drain =
      ([ex [sym "pair", sym "1", sym "a"], ex [sym "pair", sym "1", sym "b"]], pq) := by
  decide

/-! ## Conditions are those of the store at firing -/

private def grow (third : Conj) : Sources :=
  { kernel := [.pat .read (ex [sym "tok", v "t"]), third] }

private def start : Store := [ex [sym "tok", sym "a"], ex [sym "tok", sym "b"], p (sym "1")]

/-- The first branch routes `(p 2)` into the store; at the second branch `(p $x)` has two
matches, so its `(unique (p $x))` fails and it fires nothing. -/
theorem unique_counted_at_firing :
    (transformInto (grow (.unique .read (.one (p (v "x"))))) (p (sym "2")) start).drain =
      ([1], start ++ [p (sym "2")]) := by
  decide

/-- The branch of the proposal that found `(p 1)` unique does not fire on `(p 1) (p 2)`,
nor on `(p 2)` alone, and fires on `(p 1)`. -/
theorem unique_needs_its_atom :
    fire [p (sym "1"), p (sym "2")] [(.read, p (sym "1"))]
      { kernel := [.unique .read (.one (p (v "x")))] } (instances (v "x")) = none ∧
    fire [p (sym "2")] [(.read, p (sym "1"))] { kernel := [.unique .read (.one (p (v "x")))] }
      (instances (v "x")) = none ∧
    fire [p (sym "1")] [(.read, p (sym "1"))] { kernel := [.unique .read (.one (p (v "x")))] }
      (instances (v "x")) = some ([p (sym "1")], [sym "1"]) := by
  decide

/-- The first branch takes the unique `(p 1)` and routes `(p 2)` into the store. At the
second branch `(p $x)` again has exactly one match, `(p 2)`, but it is not the atom of that
branch's proposal, so the branch fires nothing. -/
theorem unique_replaced_fires_nothing :
    (transformInto (grow (.unique .take (.one (p (v "x"))))) (p (sym "2")) start).drain =
      ([1], [ex [sym "tok", sym "a"], ex [sym "tok", sym "b"], p (sym "2")]) ∧
    (matchesIn [ex [sym "tok", sym "a"], ex [sym "tok", sym "b"], p (sym "2")] []
      (p (v "x"))).length = 1 := by
  decide

/-- Re-checking the proposal's substitution, `$x = 1`, instead of firing the guided sources
counts `(unique (p 1))` and finds one match, so it would fire on `(p 1) (p 2)`. -/
theorem substitution_recheck_fires :
    walk [p (sym "1"), p (sym "2")] true [("x", sym "1")] [.unique .read (.one (p (v "x")))] =
      [([("x", sym "1")], [(.read, p (sym "1"))])] := by
  decide

/-- The same growth does not stop a `collect` branch: its variable is bound to the list at
firing, so both branches fire. -/
theorem collect_rebound_at_firing :
    (transformInto (grow (.collect .read (.one (p (v "x"))) (v "C"))) (p (sym "2")) start).drain =
      ([1, 1], start ++ [p (sym "2"), p (sym "2")]) := by
  decide

/-- After the first branch takes `(tok a)`, the second branch collects only `(tok b)`. -/
theorem collect_after_a_take :
    (transform { kernel := [.pat .take (ex [sym "tok", v "t"]),
        .collect .read (.one (ex [sym "tok", v "u"])) (v "C")] } (ex [sym "got", v "t", v "C"])
      [ex [sym "tok", sym "a"], ex [sym "tok", sym "b"]]).drain =
    ([ex [sym "got", sym "a", ex [ex [sym "tok", sym "a"], ex [sym "tok", sym "b"]]],
      ex [sym "got", sym "b", ex [ex [sym "tok", sym "b"]]]], []) := by
  decide

/-- `(collect (q $y) $C)` collects with `$y` free, then `(r $y)` binds `$y`. -/
theorem collect_bound_later_fires :
    (transform { kernel := [.collect .read (.one (q (v "y"))) (v "C"),
        .pat .read (ex [sym "r", v "y"])] } (ex [sym "got", v "C", v "y"])
      [q (sym "1"), q (sym "2"), ex [sym "r", sym "1"]]).drain =
      ([ex [sym "got", ex [q (sym "1"), q (sym "2")], sym "1"]],
        [q (sym "1"), q (sym "2"), ex [sym "r", sym "1"]]) := by
  decide

theorem collect_bound_before_fires :
    (transform { kernel := [.pat .read (ex [sym "r", v "y"]),
        .collect .read (.one (q (v "y"))) (v "C")] } (v "C")
      [q (sym "1"), q (sym "2"), ex [sym "r", sym "1"]]).drain =
      ([ex [q (sym "1")]], [q (sym "1"), q (sym "2"), ex [sym "r", sym "1"]]) := by
  decide

/-! ## Conditions over joint matches -/

private def r (x : Atom) : Atom := ex [sym "r", x]
private def tuple (items : List Atom) : Atom := ex (sym "," :: items)
private def pxqx : Query := .conj [p (v "x"), q (v "x")]

/-- `(absent (, (p $x) (q $x)))` holds on `(p 1) (q 2)`: no joint match, though each part
alone has one, so `absent` of either part blocks. -/
theorem absent_joint_holds :
    (transform { kernel := [.absent pxqx] } (sym "none") [p (sym "1"), q (sym "2")]).drain =
      ([sym "none"], [p (sym "1"), q (sym "2")]) ∧
    (transform { kernel := [.absent (.one (p (v "x")))] } (sym "none")
      [p (sym "1"), q (sym "2")]).drain = ([], [p (sym "1"), q (sym "2")]) ∧
    (transform { kernel := [.absent (.one (q (v "x")))] } (sym "none")
      [p (sym "1"), q (sym "2")]).drain = ([], [p (sym "1"), q (sym "2")]) := by
  decide

/-- Once `(q 1)` is stored, `(p 1) (q 1)` is a joint match and `absent` blocks. -/
theorem absent_joint_blocks :
    (transform { kernel := [.absent pxqx] } (sym "none")
      [p (sym "1"), q (sym "2"), q (sym "1")]).drain =
      ([], [p (sym "1"), q (sym "2"), q (sym "1")]) := by
  decide

/-- One stored `a` is a joint match of `(, a a)`, met at both parts: `absent` blocks, a read
`unique` fires, and a read `collect` collects `(, a a)`. -/
theorem reads_meet_one_occurrence_twice :
    (transform { kernel := [.absent (.conj [sym "a", sym "a"])] } (sym "found")
      [sym "a"]).drain = ([], [sym "a"]) ∧
    (transform { kernel := [.unique .read (.conj [sym "a", sym "a"])] } (sym "found")
      [sym "a"]).drain = ([sym "found"], [sym "a"]) ∧
    (transform { kernel := [.collect .read (.conj [sym "a", sym "a"]) (v "c")] } (v "c")
      [sym "a"]).drain = ([ex [tuple [sym "a", sym "a"]]], [sym "a"]) := by
  decide

/-- `(unique (take (, (p $x) (q $x))))` on `(p 1) (q 1) (q 2)`: exactly one joint tuple; the
proposal's guide is its two parts, and the firing takes both. -/
theorem unique_joint_one_tuple :
    proposals [p (sym "1"), q (sym "1"), q (sym "2")] { kernel := [.unique .take pxqx] } =
      [[(.take, p (sym "1")), (.take, q (sym "1"))]] ∧
    (transform { kernel := [.unique .take pxqx] } (ex [v "x", sym "took"])
      [p (sym "1"), q (sym "1"), q (sym "2")]).drain =
      ([ex [sym "1", sym "took"]], [q (sym "2")]) := by
  decide

/-- `(unique (, (p $x) (q $y)))` on the same store has two joint tuples and fires nothing. -/
theorem unique_joint_two_tuples :
    (jointIn [p (sym "1"), q (sym "1"), q (sym "2")] [] [p (v "x"), q (v "y")]).length = 2 ∧
    (transform { kernel := [.unique .read (.conj [p (v "x"), q (v "y")])] }
      (ex [v "x", v "y"]) [p (sym "1"), q (sym "1"), q (sym "2")]).drain =
      ([], [p (sym "1"), q (sym "1"), q (sym "2")]) := by
  decide

/-- Takes need distinct occurrences. `(unique (take (, a a)))` on one `a` has one tuple, which
meets the one copy twice and does not validate; on two copies it has four tuples; and
`(unique (take (, a b)))` takes both atoms. -/
theorem unique_take_needs_distinct_occurrences :
    (transform { kernel := [.unique .take (.conj [sym "a", sym "a"])] } (sym "found")
      [sym "a"]).drain = ([], [sym "a"]) ∧
    (jointIn [sym "a", sym "a"] [] [sym "a", sym "a"]).length = 4 ∧
    (transform { kernel := [.unique .take (.conj [sym "a", sym "a"])] } (sym "found")
      [sym "a", sym "a"]).drain = ([], [sym "a", sym "a"]) ∧
    (transform { kernel := [.unique .take (.conj [sym "a", sym "b"])] } (sym "found")
      [sym "a", sym "b"]).drain = ([sym "found"], []) := by
  decide

/-- A branch guided by its joint `unique` tuple fires nothing when the tuple is replaced before
it runs: the first branch takes `(p 1) (q 1)` and routes `(p 2) (q 2)` into the store; at the
second branch the query again has exactly one tuple, `(p 2) (q 2)`, which is not its guide. -/
theorem unique_joint_replaced_fires_nothing :
    (transformInto { kernel := [.pat .read (ex [sym "tok", v "t"]), .unique .take pxqx] }
      (tuple [p (sym "2"), q (sym "2")])
      [ex [sym "tok", sym "a"], ex [sym "tok", sym "b"], p (sym "1"), q (sym "1")]).drain =
      ([2], [ex [sym "tok", sym "a"], ex [sym "tok", sym "b"], p (sym "2"), q (sym "2")]) := by
  decide

/-- `(collect (, (p $x) (q $x)) $all)` binds the list of the joint tuples, in order. -/
theorem collect_joint :
    (transform { kernel := [.collect .read pxqx (v "all")] } (v "all")
      [p (sym "1"), q (sym "1"), p (sym "2"), q (sym "2")]).drain =
      ([ex [tuple [p (sym "1"), q (sym "1")], tuple [p (sym "2"), q (sym "2")]]],
        [p (sym "1"), q (sym "1"), p (sym "2"), q (sym "2")]) := by
  decide

/-- `(, (r $n) (collect (take (, (p $x) (q $x))) $all))` collects the two joint tuples and
takes their atoms, leaving `(r 0)`. -/
theorem collect_take_joint_after_read :
    (transform { kernel := [.pat .read (r (v "n")), .collect .take pxqx (v "all")] } (v "all")
      [p (sym "1"), q (sym "1"), p (sym "2"), q (sym "2"), r (sym "0")]).drain =
      ([ex [tuple [p (sym "1"), q (sym "1")], tuple [p (sym "2"), q (sym "2")]]],
        [r (sym "0")]) := by
  decide

/-- A participant shared by two tuples, and a participant stored twice: every stored copy of
each participating atom is taken, once. -/
theorem collect_take_every_copy :
    (transform (collectTakeJoint [p (v "x"), q (v "y")] "c") (v "c")
      [p (sym "1"), q (sym "1"), q (sym "2")]).drain =
      ([ex [tuple [p (sym "1"), q (sym "1")], tuple [p (sym "1"), q (sym "2")]]], []) ∧
    (transform (collectTakeJoint [p (v "x"), q (v "y")] "c") (v "c")
      [p (sym "1"), p (sym "1"), q (sym "1")]).drain =
      ([ex [tuple [p (sym "1"), q (sym "1")], tuple [p (sym "1"), q (sym "1")]]], []) := by
  decide

/-- `(collect (take (, a a)) $c)`: on one `a` its tuple meets the one copy twice and does not
fit, so nothing is kept and nothing taken; on two copies the four tuples fit and both copies
are taken. -/
theorem collect_take_needs_fitting_tuples :
    (transform (collectTakeJoint [sym "a", sym "a"] "c") (v "c") [sym "a"]).drain =
      ([ex []], [sym "a"]) ∧
    (transform (collectTakeJoint [sym "a", sym "a"] "c") (v "c") [sym "a", sym "a"]).drain =
      ([ex [tuple [sym "a", sym "a"], tuple [sym "a", sym "a"], tuple [sym "a", sym "a"],
        tuple [sym "a", sym "a"]]], []) := by
  decide

/-- A one-part conjunction collects one-part tuples, where its pattern collects the atoms;
taking, both leave the same store. -/
theorem collect_one_part_wraps :
    (transform { kernel := [.collect .read (.conj [p (v "x")]) (v "c")] } (v "c")
      [p (sym "1"), p (sym "2")]).drain =
      ([ex [tuple [p (sym "1")], tuple [p (sym "2")]]], [p (sym "1"), p (sym "2")]) ∧
    (transform { kernel := [.collect .read (.one (p (v "x"))) (v "c")] } (v "c")
      [p (sym "1"), p (sym "2")]).drain =
      ([ex [p (sym "1"), p (sym "2")]], [p (sym "1"), p (sym "2")]) ∧
    (transform (collectTakeJoint [p (v "x")] "c") (v "c") [p (sym "1"), q (sym "1")]).drain.2 =
      (transform (collectTake (p (v "x")) "c") (v "c") [p (sym "1"), q (sym "1")]).drain.2 := by
  decide

end Mettapedia.Languages.MeTTa.PeTTa.LibTransform.Controls
