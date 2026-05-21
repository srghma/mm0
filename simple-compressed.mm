$( Declare the constant symbols we will use $)
  $c 0 + = -> ( ) term wff |- $.

$( Define the MM0 sorts and provability symbol $)
$( $j syntax 'term'; syntax 'wff'; syntax '|-' as 'wff'; $)

$( Declare the metavariables we will use $)
  $v t r s P Q $.
$( Specify properties of the metavariables $)
  tt $f term t $.
  tr $f term r $.
  ts $f term s $.
  wp $f wff P $.
  wq $f wff Q $.
$( Define "term" and "wff" $)
  tze $a term 0 $.
  tpl $a term ( t + r ) $.
  weq $a wff t = r $.
  wim $a wff ( P -> Q ) $.
$( State the axioms $)
  a1 $a |- ( t = r -> ( t = s -> r = s ) ) $.
  a2 $a |- ( t + 0 ) = t $.
$( Define the modus ponens inference rule $)
  ${
    min $e |- P $.
    maj $e |- ( P -> Q ) $.
    mp $a |- Q $.
  $}
$( Prove a theorem
     (Contributed by ?who?, 11-Jan-2026.) $)
  th1 $p |- t = t $=
    ( tze tpl weq a2 wim a1 mp ) ABCZADZAADZAEZJJKFLIAAGHH $.
