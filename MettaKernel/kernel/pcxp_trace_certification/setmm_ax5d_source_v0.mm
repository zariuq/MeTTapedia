$c ( ) -> wff |- A. setvar $.
$v ph ps x y $.
wph $f wff ph $.
wps $f wff ps $.
vx $f setvar x $.
vy $f setvar y $.

wi $a wff ( ph -> ps ) $.

${
  min $e |- ph $.
  maj $e |- ( ph -> ps ) $.
  ax-mp $a |- ps $.
$}

ax-1 $a |- ( ph -> ( ps -> ph ) ) $.

${
  a1i.1 $e |- ph $.
  a1i $p |- ( ps -> ph ) $=
    ( wi ax-1 ax-mp ) ABADCABEF $.
$}

wal $a wff A. x ph $.

${
  $d x ph $.
  ax-5 $a |- ( ph -> A. x ph ) $.
$}

${
  $d x ps $.
  ax5d $p |- ( ph -> ( ps -> A. x ps ) ) $=
    ( wal wi ax-5 a1i ) BBCDEABCFG $.
$}
