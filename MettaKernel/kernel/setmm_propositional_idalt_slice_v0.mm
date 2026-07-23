$( Bounded source slice from the propositional-calculus region of set.mm. $)

$c ( $.
$c ) $.
$c -> $.
$c -. $.
$c wff $.
$c |- $.

$v ph $.
$v ps $.
$v ch $.

wph $f wff ph $.
wps $f wff ps $.
wch $f wff ch $.

wn $a wff -. ph $.
wi $a wff ( ph -> ps ) $.

ax-1 $a |- ( ph -> ( ps -> ph ) ) $.
ax-2 $a |- ( ( ph -> ( ps -> ch ) ) ->
  ( ( ph -> ps ) -> ( ph -> ch ) ) ) $.

${
  min $e |- ph $.
  maj $e |- ( ph -> ps ) $.
  ax-mp $a |- ps $.
$}

idALT $p |- ( ph -> ph ) $=
  ( wi ax-1 ax-2 ax-mp ) AAABZBZFAACAFABBGFBAFCAFADEE $.
