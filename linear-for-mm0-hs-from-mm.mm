$(
Updated 9/7 - Replaced axiom labels with better names and made theorem labels more consistent
Updated 9/8 - Added some missing proofs and more deduction form proofs
$)

$( $j syntax 'nilad'; syntax 'var'; syntax 'wff'; syntax '|-' as 'wff'; $)

$(
###############################################################################
Hilbert-style axiomatisation of Linear Logic
###############################################################################

This is an implementation of Girard's linear logic based on _Axioms and Models of Linear Logic_ by Wim H. Hesselink.

Thanks to the dual nature of linear logic, many of the operators are redundant. Only the `%`, `&`, `?`, and `~` operators and the units `_|_` and ` ``|`` ` are needed to construct any expression. The only problem is that to write the definitions of the composite operators, the linear biconditional `O-O` is needed, which in turn depends on `~`, `%`, and `&`. Because of this, any proofs that use the composite operators are presented after all the axioms and definitions.
$)

$(
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
Pre-logic
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
$)

$c |- wff $.
$v ph ps ch th ta et ze si $.
wph $f wff ph $.
wps $f wff ps $.
wch $f wff ch $.
wth $f wff th $.
wta $f wff ta $.
wet $f wff et $.
wze $f wff ze $.
wsi $f wff si $.

$(
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
Basic stuff
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#

Here the operators `_|_`, `%`, ` ``|`` `, `&`, `?`, and `~` are defined. Later, the duals `1`, `(+)`, `0`, `(X)`, `!` are defined, plus the implication operators `-O`, `O-O`, and the intuitionistic operators `/\`, `\/`, `-.`, `->`, and `<->`.

Due to the way defenitions work in Metamath (i.e. they don't), my first priority is to get the linear biconditional `O-O` working so that it can be used to define the other operators. Unfortunately, the definition of the linear biconditional depends on `%`, `&`, and `~`, so those need to be defined first. Proofs are generally most useful in the syllogism form `( ph -O ps ) -> ( ph -O ch )`, so I'll avoid proving stuff here only to prove it again once `-O` is defined.

Since linear implication is not available, inferences will be presented in deduction form ` ( ph % ps ) /\ ( ph % ch ) -> ( ph % th ) `. This is equivalent to ` ( ! ps (X) ! ch ) -O th `. This allows proofs to be used with the cut rule.
$)

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
Multiplicatives
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=

There are two multiplicative binary connectives: `(X)` and `%`. In the resource interpretation, these correspond to treating the resources involved in a parallel manner. Here we characterize `%`, and ~df-mc will define `(X)` as its dual.
$)

$c _|_ % ~ ( ) $.

$( Bottom, the unit of `%`. In the resource interpretation, this represents an impossibility. Characterized by ~ax-ibot and ~ax-ebot . $)
wbot $a wff _|_ $.
$( Par, multiplicative disjunction. In the resource interpretation, this represents resources that are to be used in parallel. Characterized by ~ax-init , ~ax-cut , ~ax-mdco , ~ax-mdas . $)
wmd $a wff ( ph % ps ) $.
$( Linear negation. For any statement `ph`, `~ ph` is its dual. In the resource interpretation, this represents demand for something (sort of kind of). Combining `ph` and `~ ph` yields `_|_`. $)
wneg $a wff ~ ph $.

${
  ax-ibot.1 $e |- ph $.
  $( Add a `_|_`. Inverse of ~ax-ebot . $)
  ax-ibot $a |- ( _|_ % ph ) $.
$}
${
  ax-ebot.1 $e |- ( _|_ % ph ) $.
  $( Remove a `_|_`. Inverse of ~ax-ibot . $)
  ax-ebot $a |- ph $.
$}
${
  ax-cut.1 $e |- ( ph % ps ) $.
  ax-cut.2 $e |- ( ~ ps % ch ) $.
  $( The cut rule is akin to syllogism in classical logic. It allows `~ ph % ps` to act like an implication, so that an `ph` can be removed and traded for a `ps`. $)
  ax-cut $a |- ( ph % ch ) $.
$}

$( The _init_ rule. This innocent-looking rule looks similar to the Law of Excluded Middle in classical logic, but don't be fooled. This allows us to turn any deduction into its dual by simply performing operations on the `~ ph` side and flipping it around to get the reverse implication. This is analogous to using modus tollens in classical logic, but it's especially useful in linear logic because it allows each operator to be defined as its dual with all of the deductions negated and backwards. $)
ax-init $a |- ( ~ ph % ph ) $.
$( `%` is commutative. $)
ax-mdco $a |- ( ~ ( ph % ps ) % ( ps % ph ) ) $.
$( `%` is associative. $)
ax-mdas $a |- ( ~ ( ( ph % ps ) % ch ) % ( ph % ( ps % ch ) ) ) $.

${
  cut1.1 $e |- ph $.
  cut1.2 $e |- ( ~ ph % ps ) $.
  $( Modus ponens like inference. $)
  cut1 $p |- ps $=
  ( wbot ax-ibot ax-cut ax-ebot ) BEABACFDGH $.
$}
${
  mdcod.1 $e |- ( th % ( ph % ps ) ) $.
  $( `%` is commutative. Deduction form of ~ax-mdco . $)
  mdcod $p |- ( th % ( ps % ph ) ) $=
  ( wmd ax-mdco ax-cut ) CABEBAEDABFG $.
$}
${
  mdcoi.1 $e |- ( ph % ps ) $.
  $( `%` is commutative. Inference form of ~ax-mdco . $)
  mdcoi $p |- ( ps % ph ) $=
  ( wmd ax-mdco cut1 ) ABDBADCABEF $.
$}
${
  mdasd.1 $e |- ( th % ( ( ph % ps ) % ch ) ) $.
  $( `%` is associative. Deduction form of ~ax-mdas . $)
  mdasd $p |- ( th % ( ph % ( ps % ch ) ) ) $=
  ( wmd ax-mdas ax-cut ) DABFCFABCFFEABCGH $.
$}
${
  mdasi.1 $e |- ( ( ph % ps ) % ch ) $.
  $( `%` is associative. Inference form of ~ax-mdas . $)
  mdasi $p |- ( ph % ( ps % ch ) ) $=
  ( wmd ax-mdas cut1 ) ABECEABCEEDABCFG $.
$}
${
  $( `%` is associative. Reverse of ~ax-mdas . $)
  mdasr $p |- ( ~ ( ph % ( ps % ch ) ) % ( ( ph % ps ) % ch ) ) $=
  ( wmd wneg ax-mdco ax-mdas ax-cut ) ABCDZDEZCABDZDZKCDJCADZBDZLJB
    MDZNJIADOAIFBCAGHBMFHCABGHCKFH $.
$}
${
  mdasrd.1 $e |- ( th % ( ph % ( ps % ch ) ) ) $.
  $( `%` is associative. Deduction form of ~mdasr . $)
  mdasrd $p |- ( th % ( ( ph % ps ) % ch ) ) $=
  ( wmd mdasr ax-cut ) DABCFFABFCFEABCGH $.
$}
${
  mdasri.1 $e |- ( ph % ( ps % ch ) ) $.
  $( `%` is associative. Inference form of ~mdasrd . $)
  mdasri $p |- ( ( ph % ps ) % ch ) $=
  ( wmd wbot ax-ibot mdasrd ax-ebot ) ABECEABCFABCEEDGHI $.
$}
${
  ibotr.1 $e |- ph $.
  $( Add a `_|_`, right hand side. See ~ax-ibot . $)
  ibotr $p |- ( ph % _|_ ) $=
  ( wbot ax-ibot mdcoi ) CAABDE $.
$}
${
  ebotr.1 $e |- ( ph % _|_ ) $.
  $( Remove a `_|_`, right hand side. See ~ax-ebot . $)
  ebotr $p |- ph $=
  ( wbot mdcoi ax-ebot ) AACBDE $.
$}
$( Infer `~ _|_` (secretly `1`). $)
nebot $p |- ~ _|_ $=
 ( wbot wneg ax-init ebotr ) ABACD $.
${
  cutneg.1 $e |- ( ph % ~ ps ) $.
  cutneg.2 $e |- ( ps % ch ) $.
  $( Negated version of ~ax-cut . $)
  cutneg $p |- ( ph % ch ) $=
  ( mdcoi wneg ax-cut ) CACBABCEFABGDFHF $.
$}
${
  cutf.1 $e |- ( ps % ph ) $.
  cutf.2 $e |- ( ~ ps % ch ) $.
  $( Left-hand version of ~ax-cut . $)
  cutf $p |- ( ch % ph ) $=
  ( mdcoi ax-cut ) ACABCBADFEGF $.
$}
${
  dnid.1 $e |- ( ph % ps ) $.
  $( Double negation introduction. $)
  dnid $p |- ( ph % ~ ~ ps ) $=
  ( wneg ax-init mdcoi ax-cut ) ABBDZDZCIHHEFG $.
$}
${
  dned.1 $e |- ( ph % ~ ~ ps ) $.
  $( Double negation elimination. $)
  dned $p |- ( ph % ps ) $=
  ( wneg ax-init mdcoi dnid ax-cut ) ABDZDZBCBJDBIIBBEFGFH $.
$}
${
  dni1.1 $e |- ( ph % ps ) $.
  $( Double negation introduction, left hand side. $)
  dni1 $p |- ( ~ ~ ph % ps ) $=
  ( wneg mdcoi dnid ) BADDBAABCEFE $.
$}
${
  dne1.1 $e |- ( ~ ~ ph % ps ) $.
  $( Double negation elimination, left hand side. $)
  dne1 $p |- ( ph % ps ) $=
  ( wneg mdcoi dned ) BABAADDBCEFE $.
$}
${
  inenebot.1 $e |- ph $.
  $( Add a `~ ~ _|_`. See ~ax-ibot . This is useful for dealing with deductions where the antecedent is negated. $)
  inenebot $p |- ( ~ ~ _|_ % ph ) $=
  ( wbot ax-ibot dni1 ) CAABDE $.
$}
${
  enenebot.1 $e |- ( ~ ~ _|_ % ph ) $.
  $( Remove a `~ ~ _|_`. Inverse of ~inenebot . $)
  enenebot $p |- ph $=
  ( wbot dne1 ax-ebot ) ACABDE $.
$}

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
Additives
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=

There are two additive binary connectives: `&` and `(+)`. These relate to treating the involved expressions independently. Here we characterize `&`, and ~df-ad will define `(+)` as its dual.
$)

$c `|` & $.

$( Top, the unit of `&`. In the resource interpretation, this represents an unknown collection of objects. Characterized by ~ax-top . $)
wtop $a wff `|` $.
$( With, additive conjunction. In the resource interpretation, this represents a choice between two resources. Characterized by ~ax-iac , ~ax-eac1 , ~ax-eac2 . $)
wac $a wff ( ph & ps ) $.

$( Anything can turn into ` ``|`` `. $)
ax-top $a |- ( ~ ph % `|` ) $.
${
  ax-iac.1 $e |- ( ~ ph % ps ) $.
  ax-iac.2 $e |- ( ~ ph % ch ) $.
  $( `&` introduction rule. $)
  ax-iac $a |- ( ~ ph % ( ps & ch ) ) $.
$}
${
  ax-eac1.1 $e |- ( ~ ph % ( ps & ch ) ) $.
  $( `&` elimination rule, left hand side. $)
  ax-eac1 $a |- ( ~ ph % ps ) $.
$}
${
  ax-eac2.1 $e |- ( ~ ph % ( ps & ch ) ) $.
  $( `&` elimination rule, right hand side. $)
  ax-eac2 $a |- ( ~ ph % ch ) $.
$}

${
  iac.1 $e |- ( ph % ps ) $.
  iac.2 $e |- ( ph % ch ) $.
  $( `&` introduction rule. ~ax-iac has a negation for some reason, this one doesn't. $)
  iac $p |- ( ph % ( ps & ch ) ) $=
  ( wac wneg dni1 ax-iac dne1 ) ABCFAGBCABDHACEHIJ $.
$}
${
  iaci.1 $e |- ph $.
  iaci.2 $e |- ps $.
  $( `&` introduction rule. Inference form of ~ax-iac . $)
  iaci $p |- ( ph & ps ) $=
  ( wac wbot ax-ibot iac ax-ebot ) ABEFABACGBDGHI $.
$}
${
  eac1d.1 $e |- ( ph % ( ps & ch ) ) $.
  $( `&` elimination rule, left hand side. ~ax-eac1 has a negation for some reason, this one doesn't. $)
  eac1d $p |- ( ph % ps ) $=
  ( wneg wac dni1 ax-eac1 dne1 ) ABAEBCABCFDGHI $.
$}
${
  eac1i.1 $e |- ( ph & ps ) $.
  $( `&` elimination rule, left hand side. Inference form of ~ax-eac1 . $)
  eac1i  $p |- ph $=
  ( wbot wneg wac inenebot ax-eac1 enenebot ) ADEABABFCGHI $.
$}
${
  eac2d.1 $e |- ( ph % ( ps & ch ) ) $.
  $( `&` elimination rule, right hand side. ~ax-eac2 has a negation for some reason, this one doesn't. $)
  eac2d  $p |- ( ph % ch ) $=
  ( wneg wac dni1 ax-eac2 dne1 ) ACAEBCABCFDGHI $.
$}
${
  eac2i.1 $e |- ( ph & ps ) $.
  $( `&` elimination rule, right hand side. Inference form of ~ax-eac2 . $)
  eac2i  $p |- ps $=
  ( wbot wneg wac inenebot ax-eac2 enenebot ) BDEABABFCGHI $.
$}

${
  itopi.1 $e |- ph $.
  $( Insert Top into With. Inverse of ~etopi . $)
  itopi $p |- ( ph & `|` ) $=
  ( wtop wac ax-init ax-top ax-iac cut1 ) AACDBAACAEAFGH $.
$}
${
  etopi.1 $e |- ( ph & `|` ) $.
  $( Remove Top from With. This is, of course, just a special case of ~ax-eac1 . $)
  etopi $p |- ph $=
  ( wtop eac1i ) ACBD $.
$}
${
  acco.1 $e |- ( ph % ( ps & ch ) ) $.
  $( `&` is commutative. $)
  acco $p |- ( ph % ( ch & ps ) ) $=
  ( eac2d eac1d iac ) ACBABCDEABCDFG $.
$}
${
  acas.1 $e |- ( ph % ( ( ps & ch ) & th ) ) $.
  $( `&` is associative. $)
  acas $p |- ( ph % ( ps & ( ch & th ) ) ) $=
  ( wac eac1d eac2d iac ) ABCDFABCABCFZDEGZGACDABCKHAJDEHII $.
$}
${
  acasr.1 $e |- ( ph % ( ps & ( ch & th ) ) ) $.
  $( `&` is associative. Reverse of ~acas . $)
  acasr $p |- ( ph % ( ( ps & ch ) & th ) ) $=
  ( wac eac1d eac2d iac ) ABCFDABCABCDFZEGACDABJEHZGIACDKHI $.
$}
${
  dismdac.1 $e |- ( ph % ( ps % ( ch & th ) ) ) $.
  $( `%` distributes over `&`. $)
  dismdac $p |- ( ph % ( ( ps % ch ) & ( ps % th ) ) ) $=
  ( wmd wac mdasri eac1d mdasi eac2d iac ) ABCFBDFABCABFZCDABCDGEHZ
    IJABDMCDNKJL $.
$}
${
  extmdac.1 $e |- ( ph % ( ( ps % ch ) & ( ps % th ) ) ) $.
  $( `%` extracts out of `&`. Converse of ~dismdac . $)
  extmdac $p |- ( ph % ( ps % ( ch & th ) ) ) $=
  ( wac wmd eac1d mdasri eac2d iac mdasi ) ABCDFABGCDABCABCGZBDGZEH
    IABDAMNEJIKL $.
$}

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
Exponentials
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=

There are two exponential connectives: `?` and `!`. These allow expressions to be duplicated and deleted. Here we characterize `?`, and ~df-pe will define `!` as its dual.
$)

$c ? $.

$( "Why not", negative exponential. Characterized by ~ax-ipe , ~ax-epe , ~ax-weak , ~ax-contr , ~ax-pemc , ~ax-dig . $)
wne $a wff ? ph $.

${
  ax-ipe.1 $e |- ( ~ ph % ? ps ) $.
  $( Add a `?` (secretly a `!`). Inverse of ~ax-epe . $)
  ax-ipe $a |- ( ~ ? ph % ? ps ) $.
$}
${
  ax-epe.1 $e |- ( ~ ? ph % ? ps ) $.
  $( Remove a `?` (secretly a `!`). Inverse of ~ax-ipe . $)
  ax-epe $a |- ( ~ ph % ? ps ) $.
$}
$( `? ph` can be added into any statement. $)
ax-weak $a |- ( ~ _|_ % ? ph ) $.
$( `? ph` can be contracted. $)
ax-contr $a |- ( ~ ( ? ph % ? ph ) % ? ph ) $.
$( `! 1`. This is needed to let ~ax-ipe and ~ax-epe work on single items. $)
ax-pemc $a |- ~ ? _|_ $.
$( If all the elements of a multiplicative disjunction have `?`, then `?` can be removed from that disjunction. $)
ax-dig $a |- ( ~ ? ( ? ph % ? ps ) % ( ? ph % ? ps ) ) $.



$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
Implication
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=

Yay, implication!

The linear implication operator `ph -O ps` reads as, "Given a `ph`, I can exchange it for a `ps`." This is closely related to the logical implication `->` which can be interpreted as, "Given a proof of `ph`, I can prove `ps`." The important difference is that the linear implication and the antecedent are both consumed by this action. The linear biconditional can work either way; the choice is given to you by the `&` in its definition.

The linear biconditional is used to write all definitions, except itself (~df-lb ).
$)

$c -O O-O $.

$( Linear biconditional, defined by ~df-lb . This is the operator used for definitions, so its definition will be a little unusual... $)
wlb $a wff ( ph O-O ps ) $.

$( Definition of linear biconditional. Since the linear implication has not been defined, this is a mouthfull. The good news is, once the properties of the linear biconditional are proven, it will be much easier to express other definitions. See ~dflb for a cleaner form of the definition. $)

df-lb $a |- ( ( ~ ( ph O-O ps ) % ( ( ~ ph % ps ) & ( ~ ps % ph ) ) ) & ( ~ ( ( ~ ph % ps ) & ( ~ ps % ph ) ) % ( ph O-O ps ) ) ) $.

${
  lb1d.1 $e |- ( ph % ps ) $.
  lb1d.2 $e |- ( ps O-O ch ) $.
  $( Forward deduction using `O-O`. $)
  lb1d $p |- ( ph % ch ) $=
  ( wneg wmd wlb wac df-lb eac1i cut1 ax-cut ) ABCDBFCGZCFBGZBCHZ
    NOIZEPFQGQFPGBCJKLKM $.
$}
${
  lb2d.1 $e |- ( ph % ch ) $.
  lb2d.2 $e |- ( ps O-O ch ) $.
  $( Reverse deduction using `O-O`. $)
  lb2d $p |- ( ph % ps ) $=
  ( wneg wmd wlb wac df-lb eac1i cut1 eac2i ax-cut ) ACBDBFCGZCFB
    GZBCHZOPIZEQFRGRFQGBCJKLMN $.
$}
${
  lb1i.1 $e |- ph $.
  lb1i.2 $e |- ( ph O-O ps ) $.
  $( Forward inference using `O-O`. $)
  lb1i $p |- ps $=
  ( wbot ax-ibot lb1d ax-ebot ) BEABACFDGH $.
$}
${
  lb2i.1 $e |- ps $.
  lb2i.2 $e |- ( ph O-O ps ) $.
  $( Reverse inference using `O-O`. $)
  lb2i $p |- ph $=
  ( wbot ax-ibot lb2d ax-ebot ) AEABBCFDGH $.
$}

$( Linear implication, defined by ~df-li . Now that linear implication exists, we can finally put things in syllogism form from here on. $)
wli $a wff ( ph -O ps ) $.
$( Definition of linear implication. $)
df-li $a |- ( ( ph -O ps ) O-O ( ~ ph % ps ) ) $.

${
  dfli1.1 $e |- ( ph % ( ps -O ch ) ) $.
  $( Convert from linear implication. $)
  dfli1 $p |- ( ph % ( ~ ps % ch ) ) $=
  ( wli wneg wmd df-li lb1d ) ABCEBFCGDBCHI $.
$}
${
  dfli2.1 $e |- ( ph % ( ~ ps % ch ) ) $.
  $( Convert to linear implication. $)
  dfli2 $p |- ( ph % ( ps -O ch ) ) $=
  ( wli wneg wmd df-li lb2d ) ABCEBFCGDBCHI $.
$}
${
  dfli1i.1 $e |- ( ps -O ch ) $.
  $( Convert from linear implication. Inference for ~dfli1 . $)
  dfli1i $p |- ( ~ ps % ch ) $=
  ( wneg wmd wbot wli ax-ibot dfli1 ax-ebot ) ADBEFABABGCHIJ $.
$}
${
  dfli2i.1 $e |- ( ~ ps % ch ) $.
  $( Convert to linear implication. Inference for ~dfli2 . $)
  dfli2i $p |- ( ps -O ch ) $=
  ( wli wbot wneg wmd ax-ibot dfli2 ax-ebot ) ABDEABAFBGCHIJ $.
$}
${
  lb1s.1 $e |- ( ph -O ps ) $.
  lb1s.2 $e |- ( ps O-O ch ) $.
  $( Forward syllogism using `O-O`. $)
  lb1s $p |- ( ph -O ch ) $=
  ( wneg dfli1i lb1d dfli2i ) ACAFBCABDGEHI $.
$}
${
  lb2s.1 $e |- ( ph -O ch ) $.
  lb2s.2 $e |- ( ps O-O ch ) $.
  $( Reverse syllogism using `O-O`. $)
  lb2s $p |- ( ph -O ps ) $=
  ( wneg dfli1i lb2d dfli2i ) ABAFBCACDGEHI $.
$}
${
  mdm2.1 $e |- ( th % ( ph % ps ) ) $.
  mdm2.2 $e |- ( ps -O ch ) $.
  $( Par is monotone in its second argument. $)
  mdm2 $p |- ( th % ( ph % ch ) ) $=
  ( wmd mdasri wli wneg df-li lb1i ax-cut mdasi ) DACDAGBCDABEHBC
    IBJCGFBCKLMN $.
$}
${
  mdm1.1 $e |- ( th % ( ph % ps ) ) $.
  mdm1.2 $e |- ( ph -O ch ) $.
  $( Par is monotone in its first argument. $)
  mdm1 $p |- ( th % ( ch % ps ) ) $=
  ( mdcod mdm2 ) BCDBACDABDEGFHG $.
$}
${
  mdm1i.1 $e |- ( ph % ps ) $.
  mdm1i.2 $e |- ( ph -O ch ) $.
  $( Par is monotone in its first argument. Inference form of ~mdm1 . $)
  mdm1i $p |- ( ch % ps ) $=
  ( wmd wbot ax-ibot mdm1 ax-ebot ) CBFABCGABFDHEIJ $.
$}
${
  mdm2i.1 $e |- ( ph % ps ) $.
  mdm2i.2 $e |- ( ps -O ch ) $.
  $( Par is monotone in its second argument. Inference form of ~mdm2 . Essentially ~ax-cut using linear implication. $)
  mdm2i $p |- ( ph % ch ) $=
  ( wmd wbot ax-ibot mdm2 ax-ebot ) ACFABCGABFDHEIJ $.
$}
${
  mdm1s.1 $e |- ( ph -O ch ) $.
  $( Par is monotone in its first argument. Syllogism form of ~mdm1 . $)
  mdm1s $p |- ( ( ph % ps ) -O ( ch % ps ) ) $=
  ( wmd wneg ax-init mdm1 dfli2i ) ABEZCBEABCJFJGDHI $.
$}
${
  mdm2s.1 $e |- ( ps -O ch ) $.
  $( Par is monotone in its second argument. Syllogism form of ~mdm2 . $)
  mdm2s $p |- ( ( ph % ps ) -O ( ph % ch ) ) $=
  ( wmd wneg ax-init mdm2 dfli2i ) ABEZACEABCJFJGDHI $.
$}
${
  syl.1 $e |- ( ph -O ps ) $.
  syl.2 $e |- ( ps -O ch ) $.
  $( Syllogism using linear implication. $)
  syl $p |- ( ph -O ch ) $=
  ( wli wneg wmd df-li lb1i ax-cut lb2i ) ACFAGZCHMBCABFMBHDABIJB
    CFBGCHEBCIJKACIL $.
$}
${
  lmp.min $e |- ph $.
  lmp.maj $e |- ( ph -O ps ) $.
  $( Modus ponens like inference using linear implication. $)
  lmp $p |- ps $=
  ( wbot ax-ibot mdm2i ax-ebot ) BEABACFDGH $.
$}
$( Identity rule for linear implication. Syllogism form of ~ax-init . $)
id $p |- ( ph -O ph ) $=
 ( wli wneg wmd ax-init df-li lb2i ) AABACADAEAAFG $.

$( Double negation introduction. Syllogism form of ~dnid . $)
dnis $p |- ( ph -O ~ ~ ph ) $=
 ( wneg wli wmd ax-init mdcoi df-li lb2i ) AABZBZCIJDJIIEFAJGH $.
$( Double negation elimination. Syllogism form of ~dned . $)
dnes $p |- ( ~ ~ ph -O ph ) $=
 ( wneg wli wmd ax-init mdcoi ax-cut df-li lb2i ) ABZBZACKBZADALAJLJAAEF
  LKKEFGFKAHI $.

${
  acm1.1 $e |- ( th % ( ph & ps ) ) $.
  acm1.2 $e |- ( ph -O ch ) $.
  $( With is monotone in its first argument. $)
  acm1 $p |- ( th % ( ch & ps ) ) $=
  ( eac1d mdm2i eac2d iac ) DCBDACDABEGFHDABEIJ $.
$}
${
  acm2.1 $e |- ( th % ( ph & ps ) ) $.
  acm2.2 $e |- ( ps -O ch ) $.
  $( With is monotone in its second argument. $)
  acm2 $p |- ( th % ( ph & ch ) ) $=
  ( acco acm1 ) DCABACDDABEGFHG $.
$}
${
  acm1i.1 $e |- ( ph & ps ) $.
  acm1i.2 $e |- ( ph -O ch ) $.
  $( With is monotone in its first argument. Inference form of ~acm1 . $)
  acm1i $p |- ( ch & ps ) $=
  ( wac wbot ax-ibot acm1 ax-ebot ) CBFABCGABFDHEIJ $.
$}
${
  acm2i.1 $e |- ( ph & ps )  $.
  acm2i.2 $e |- ( ps -O ch ) $.
  $( With is monotone in its second argument. Inference form of ~acm2 . $)
  acm2i $p |- ( ph & ch ) $=
  ( wac wbot ax-ibot acm2 ax-ebot ) ACFABCGABFDHEIJ $.
$}
${
  acm1s.1 $e |- ( ph -O ch ) $.
  $( With is monotone in its first argument. Syllogism form of ~acm1 . $)
  acm1s $p |- ( ( ph & ps ) -O ( ch & ps ) ) $=
  ( wac wneg ax-init acm1 dfli2i ) ABEZCBEABCJFJGDHI $.
$}
${
  acm2s.1 $e |- ( ps -O ch ) $.
  $( With is monotone in its second argument. Syllogism form of ~acm2 . $)
  acm2s $p |- ( ( ph & ps ) -O ( ph & ch ) ) $=
  ( wac wneg ax-init acm2 dfli2i ) ABEZACEABCJFJGDHI $.
$}

${
  nems.1 $e |- ( ph -O ps ) $.
  $( "Why not" is monotone. $)
  nems $p |- ( ? ph -O ? ps ) $=
  ( wne wneg dfli1i ax-init ax-epe ax-cut ax-ipe dfli2i ) ADBDZAB
    AEBLABCFBBLGHIJK $.
$}

$( Extract forward implication from biconditional. Syllogism form of ~ lb1i . $)
lbi1s $p |- ( ( ph O-O ps ) -O ( ph -O ps ) ) $=
 ( wlb wli wneg wmd wac df-lb eac1i ax-eac1 df-li cut1 eac2i ax-cut
  lb2i ) ABCZABDZDPEZQFRAEBFZQPSBEAFZRSTGZFUAEPFABHIJQESFZSEQFZQSCZUB
  UCGZABKUDEUEFUEEUDFQSHILMNPQKO $.
$( Extract reverse implication from biconditional. Syllogism form of ~ lb2i . $)
lbi2s $p |- ( ( ph O-O ps ) -O ( ps -O ph ) ) $=
 ( wlb wli wneg wmd wac df-lb eac1i ax-eac2 df-li cut1 ax-cut lb2i ) A
  BCZBADZDOEZPFQBEAFZPOAEBFZRQSRGZFTEOFABHIJPRCZREPFZBAKUAPERFZUBUAEU
  CUBGZFUDEUAFPRHIJLMOPKN $.
${
  lbi1.1 $e |- ( ph O-O ps ) $.
  $( Extract forward implication from biconditional. Alternate form of ~ lb1i . $)
  lbi1 $p |- ( ph -O ps ) $=
  ( wlb wli lbi1s lmp ) ABDABECABFG $.
$}
${
  lbi2.1 $e |- ( ph O-O ps ) $.
  $( Extract reverse implication from biconditional. Alternate form of ~ lb2i . $)
  lbi2 $p |- ( ps -O ph ) $=
  ( wlb wli lbi2s lmp ) ABDBAECABFG $.
$}
$( Forward implication of biconditional definition. $)
dflb1s $p |- ( ( ph O-O ps ) -O ( ( ph -O ps ) & ( ps -O ph ) ) ) $=
 ( wlb wli wac lbi1s dfli1i lbi2s ax-iac dfli2i ) ABCZABDZBADZEKLMKLA
  BFGKMABHGIJ $.
$( Reverse implication of biconditional definition. $)
dflb2s $p |- ( ( ( ph -O ps ) & ( ps -O ph ) ) -O ( ph O-O ps ) ) $=
( wli wac wneg wmd wlb ax-init dfli1 dfli2i acm1s acm2s df-lb
  eac2i syl ) ABCZBACZDZAEBFZBEAFZDZABGZRSQDUAPQSPSPEABPHIJKSQTQTQEBA
  QHIJLOUAUBUBEUAFUAEUBFABMNJO $.

$( Nicer definition of biconditional. Uses `O-O` and `-O`. $)
dflb $p |- ( ( ph O-O ps ) O-O ( ( ph -O ps ) & ( ps -O ph ) ) ) $=
 ( wlb wli wac dflb1s dflb2s iaci lmp ) ABCZABDBADEZDZKJDZEJKCLMABFA
  BGHJKGI $.

$( Contrapositive rule for linear implication. This follows quite neatly from ~df-li . $)
licon $p |- ( ( ph -O ps ) -O ( ~ ps -O ~ ph ) ) $= ( wli wneg wmd id df-li lb1s dnis mdm2s dfli1i mdcod dfli2i lb2s
  syl ) ABCZADZBEZBDZQCZPPRPFABGHRTSDZQEZRUBQUARDRQUAEQBUABIJKLMSQGNO
  $.

${
  licond.1 $e |- ( ch % ( ph -O ps ) ) $.
  $( Deduction form of ~licon . $)
  licond $p |- ( ch % ( ~ ps -O ~ ph ) ) $=
  ( wneg wmd dfli1 mdasri dnid mdasi mdcod dfli2 ) CBEZAEZNMEZCCNOC
    NFBCNBCABDGHIJKL $.
$}

${
  ilb.1 $e |- ( ph -O ps ) $.
  ilb.2 $e |- ( ps -O ph ) $.
  $( Construct a biconditional from its forward and reverse implications. $)
  ilb $p |- ( ph O-O ps ) $=
  ( wlb wli wac iaci dflb lb2i ) ABEABFZBAFZGKLCDHABIJ $.
$}

${
  ilbd.1 $e |- ( ph -O ( ps -O ch ) ) $.
  ilbd.2 $e |- ( ph -O ( ch -O ps ) ) $.
  $( Construct a biconditional from its forward and reverse implications. $)
  ilbd $p |- ( ph -O ( ps O-O ch ) ) $=
  ( wlb wneg wli wac dfli1i ax-iac dflb lb2d dfli2i ) ABCFZAGOBCHZC
    BHZIAPQAPDJAQEJKBCLMN $.
$}

$( Linear biconditional is reflexive. This could be thought of as "both directions" of ~id . $)
lbrf $p |- ( ph O-O ph ) $= ( id ilb ) AAABZDC $.
${
  lbeui.1 $e |- ( ph O-O ps ) $.
  lbeui.2 $e |- ( ph O-O ch ) $.
  $( Linear biconditional is Euclidean. Inference for ~lbeu . $)
  lbeui $p |- ( ps O-O ch ) $=
  ( lbi2 lbi1 syl ilb ) BCBACABDFACEGHCABACEFABDGHI $.
$}
${
  lbsymi.1 $e |- ( ph O-O ps ) $.
  $( Linear biconditional is symmetric. Inference for ~lbsym . $)
  lbsymi $p |- ( ps O-O ph ) $= ( lbrf lbeui ) ABACADE $.
$}
${
  lbtri.1 $e |- ( ph O-O ps ) $.
  lbtri.2 $e |- ( ps O-O ch ) $.
  $( Linear biconditional is transitive. Inference for ~lbtr . $)
  lbtri $p |- ( ph O-O ch ) $= ( lbsymi lbeui ) BACABDFEG $.
$}
${
  lbsymd.1 $e |- ( ph -O ( ps O-O ch ) ) $.
  $( Linear biconditional is symmetric. Deduction for ~lbsym . $)
  lbsymd $p |- ( ph -O ( ch O-O ps ) ) $=
  ( wli wneg wlb wac dfli1i dflb lb1d ax-eac2 dfli2i ax-eac1 ilbd )
    ACBACBEZABCEZPAFBCGZQPHARDIBCJKZLMAQAQPSNMO $.
$}

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
Operator properties and duals
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=

All operators in linear logic have a dual. The dual operator is the same as its corresponding operator but negated, similar to ` ph /\ ps <-> -. ( -. ph \/ -. ps ) ` in classical logic. Here we will characterize the dual operators.

Also, now that we finally have the underpinnings for linear logic completely set up, we can finally establish the properties of the operators alongside their duals. This will make it much easier to do more interesting proofs.
$)

$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
Multiplicatives revisited
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

$c 1 (X) $.

$( One, the unit of `(X)`. Defined by ~df-one . $)
wone $a wff 1 $.
$( One is the dual of Bottom. $)
df-one $a |- ( 1 O-O ~ _|_ ) $.

$( Times, multiplicative conjunction. Defined by ~df-mc . $)
wmc $a wff ( ph (X) ps ) $.
$( Times is the dual of Par. $)
df-mc $a |- ( ( ph (X) ps ) O-O ~ ( ~ ph % ~ ps ) ) $.

$( Double negation elimination and introduction. $)
dn $p |- ( ph O-O ~ ~ ph ) $= ( wneg dnis dnes ilb ) AABBACADE $.
$( `%` is commutative. $)
mdco $p |- ( ( ph % ps ) -O ( ps % ph ) ) $=
( wmd wneg ax-init mdcod dfli2i ) ABCZBACABHDHEFG $.
$( `%` is commutative. Biconditional version of ~mdco . $)
mdcob $p |- ( ( ph % ps ) O-O ( ps % ph ) ) $=
( wmd mdco ilb ) ABCBACABDBADE $.
$( `%` is associative. $)
mdas $p |- ( ( ( ph % ps ) % ch ) -O ( ph % ( ps % ch ) ) ) $= ( wmd ax-mdas dfli2i ) ABDCDABCDDABCEF $.
$( `%` is associative. Reverse of ~mdas . $)
$( mdasrNEW $p |- ( ( ph % ( ps % ch ) ) -O ( ( ph % ps ) % ch ) ) $= ? $. $)
$( mdasb $p |- ( ( ( ph % ps ) % ch ) O-O ( ph % ( ps % ch ) ) ) $= ? $. $)
$( `_|_` is the unit of `%` (left side). $)
md1 $p |- ( ph O-O ( _|_ % ph ) ) $=
( wbot wmd wneg ax-init ax-ibot mdcoi mdasi mdcod dfli2i mdasri
  ilb ebotr ) ABACZANABADZOABBOACZPAEFGHIJNANDZACQABBAQNEIKMJL $.
$( `_|_` is the unit of `%` (right side). $)
md2 $p |- ( ph O-O ( ph % _|_ ) ) $=
( wbot wmd md1 lbi1 mdcob lbi2 syl lb2s ilb ) AABCZABACZKALADZEKLA
  BFZGHKALKLNEMIJ $.
$( `(X)` is commutative. TODO extract double negation theorems, ~licon alternate forms $)
mcco $p |- ( ( ph (X) ps ) -O ( ps (X) ph ) ) $=
( wmc wneg wmd dnis wli ax-mdco dfli2i id df-mc lb1s licon lmp
  lb2s syl ) ABCZBACBDZADZEZDZQQDZDZUAQFTUBGUCUAGTSREZUBTUDRSHIUDUDDZ
  DZUBUDFQUEGUFUBGQQUEQJABKLQUEMNPPTUBMNPBAKO $.
$( `(X)` is commutative. Biconditional version of ~mcco . $)
mccob $p |- ( ( ph (X) ps ) O-O ( ps (X) ph ) ) $=
( wmc mcco ilb ) ABCBACABDBADE $.
$( `(X)` is associative. $)
$( mcas $p |- ( ( ( ph (X) ps ) (X) ch ) -O ( ps (X) ( ps (X) ch ) ) ) $= ? $. $)
$( `(X)` is associative. $)
$( mcasb $p |- ( ( ( ph (X) ps ) (X) ch ) O-O ( ps (X) ( ps (X) ch ) ) ) $= ? $. $)
$( `1` is the unit of `(X)` (left side). $)
$( mc1 $p |- ( ph O-O ( 1 (X) ph ) ) $= ? $. $)
$( `1` is the unit of `(X)` (right side). $)
$( mc2 $p |- ( ph O-O ( ph (X) 1 ) ) $= ? $. $)

$( `1`. It's very true, but is it as true as ` ``|`` ` ( ~itop , ~top )? Discuss. $)
$( one $p |- 1 $= ? $. $)

$( Creation of `ph` and its dual from `1`. Dual of ~initr . $)
$( init $p |- ( 1 -O ( ph % ~ ph ) ) $= ? $. $)
$( Annihilation of `ph` and its dual into `_|_`. Dual of ~init . $)
$( initr $p |- ( ( ph (X) ~ ph ) -O _|_ ) $= ? $. $)
$( Association of `(X)` into `%`. The converse of this rule does not hold.

This theorem is its own dual: By flipping the `-O` around and swapping `(X)` and `%`, you end up with the same theorem. $)
$( mcmd $p |- ( ( ph (X) ( ps % ch ) ) -O ( ( ph (X) ps ) % ch ) ) $= ? $. $)
$( Combine `%` statements by a single term. $)
$( merge $p |- ( ( ( ph % ps ) (X) ( ch % th ) ) -O ( ( ph % ( ps (X) ch ) ) % th ) ) $= ? $. $)

$( Linear biconditional is Euclidean. $)
$( lbeu $p |- ( ( ( ph O-O ps ) (X) ( ph O-O ch ) ) -O ( ps O-O ch ) ) $= ? $. $)
$( Linear biconditional is symmetric. $)
$( lbsym $p |- ( ( ph O-O ps ) -O ( ps O-O ph ) ) $= ? $. $)
$( Linear biconditional is transitive. $)
$( lbtr $p |- ( ( ( ph O-O ps ) (X) ( ps O-O ch ) ) -O ( ph O-O ch ) ) $= ? $. $)

$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
Additives revisited
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

$c 0 (+) $.

$( Zero, the unit of `(+)`. Defined by ~df-zero . $)
wzero $a wff 0 $.
$( Zero is the dual of Top. $)
df-zero $a |- ( 0 O-O ~ `|` ) $.

$( Plus, additive disjunction. Defined by ~df-ad . $)
wad $a wff ( ph (+) ps ) $.
$( Plus is the dual of With. $)
df-ad $a |- ( ( ph (+) ps ) O-O ~ ( ~ ph & ~ ps ) ) $.

$( `(+)` is commutative. $)
$( adcob $p |- ( ( ph (+) ps ) O-O ( ps (+) ph ) ) $= ? $. $)
$( $( `(+)` is associative. $) $)
$( adasb $p |- ( ( ( ph (+) ps ) (+) ch ) O-O ( ps (+) ( ps (+) ch ) ) ) $= ? $. $)
$( $( `0` is the unit of `(+)` (left side). $) $)
$( ad1 $p |- ( ph O-O ( 0 (+) ph ) ) $= ? $. $)
$( $( `0` is the unit of `(+)` (right side). $) $)
$( ad2 $p |- ( ph O-O ( ph (+) 0 ) ) $= ? $. $)
$( $( `&` is commutative. $) $)
$( accob $p |- ( ( ph & ps ) O-O ( ps & ph ) ) $= ? $. $)
$( $( `&` is associative. $) $)
$( acasb $p |- ( ( ( ph & ps ) & ch ) O-O ( ps & ( ps & ch ) ) ) $= ? $. $)
$( $( ` ``|`` ` is the unit of `&` (left side). $) $)
$( ac1 $p |- ( ph O-O ( `|` & ph ) ) $= ? $. $)
$( $( ` ``|`` ` is the unit of `&` (right side). $) $)
$( ac2 $p |- ( ph O-O ( ph & `|` ) ) $= ? $. $)
$( $( Select the left side of `&`. Dual of ~iad1 . $) $)
$( eac1 $p |- ( ( ph & ps ) -O ph ) $= ? $. $)
$( $( Select the left side of `&`. Dual of ~iad2 . $) $)
$( eac2 $p |- ( ( ph & ps ) -O ps ) $= ? $. $)
$( $( Introduce a `(+)` (left side). Dual of ~eac1 . $) $)
$( iad1 $p |- ( ph -O ( ph (+) ps ) ) $= ? $. $)
$( $( Introduce a `(+)` (right side). Dual of ~eac2 . $) $)
$( iad2 $p |- ( ps -O ( ph (+) ps ) ) $= ? $. $)
$( $( From `0`, infer all. $) $)
$( ezer $p |- ( 0 -O ph ) $= ? $. $)
$( $( Everything can be turned into ` ``|`` `. $) $)
$( itop $p |- ( ph -O `|` ) $= ? $. $)
$( $( Hey, that's ` ``|`` `. A direct consequence of ~itop . $) $)
$( top $p |- `|` $= ? $. $)



$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
Exponentials revisited
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

$c ! $.

$( "Of course", positive exponential. Defined by ~df-pe . $)
wpe $a wff ! ph $.
$( "Of course" is the dual of "Why not". $)
df-pe $a |- ( ! ph O-O ~ ? ~ ph ) $.

$( Create `? ph` from `_|_`. $)
$( weak $p |- ( _|_ -O ? ph ) $= ? $. $)
$( $( Unduplicate `? ph`. $) $)
$( dupr $p |- ( ( ? ph (X) ? ph ) -O ? ph ) $= ? $. $)
$( $( Dig out a `?` from `%`. $) $)
$( dig $p |- ( ? ( ? ph (X) ? ph ) -O ( ? ph (X) ? ph ) ) $= ? $. $)
$( $( Dig out a `?` from a single term. $) $)
$( dig1 $p |- ( ? ? ph -O ? ph ) $= ? $. $)
$( $( Promote `ph` to `? ph`. $) $)
$( ine $p |- ( ph -O ? ph ) $= ? $. $)
$( $( Destroy `! ph`. $) $)
$( weakr $p |- ( ! ph -O 1 ) $= ? $. $)
$( $( Duplicate `! ph`. $) $)
$( dup $p |- ( ! ph -O ( ! ph (X) ! ph ) ) $= ? $. $)
$( $( Bury `%` with `!`. $) $)
$( bury $p |- ( ( ! ph (X) ! ph ) -O ! ( ! ph (X) ! ph ) ) $= ? $. $)
$( $( Bury a single term with `!`. $) $)
$( bury1 $p |- ( ! ph -O ! ! ph ) $= ? $. $)
$( $( Demote `! ph` to `ph`. $) $)
$( epe $p |- ( ! ph -O ph ) $= ? $. $)
$( $( `! 1`. It's like `1` but even more. $) $)
$( peone $p |- ! 1 $= ? $. $)
$( $( `! ``|`` `. It's like ` ``|`` ` but even more. $) $)
$( petop $p |- ! `|` $= ? $. $)

${
  ipe.1 $e |- ph $.
  $( Introduce positive exponential at the top level. TODO: Extract lemmas for double negation, intro `? ph`, and more. Also get the proof back because it exploded $)
  $( ipe $p |- ! ph $= ? $. $)
$}

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
Miscellaneous theorems
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=

Here are some old uncategorized theorems. They need to be placed into an appropriate section and renamed.
$)

${
  ionei.1 $e |- ph $.
  $( Insert One into Times. $)
  $( ionei $p |- ( ph (X) 1 ) $= ? $. $)
$}
${
  eonei.1 $e |- ( ph (X) 1 ) $.
  $( Remove One from Times. $)
  $( eonei $p |- ph $= ? $. $)
$}
${
  mcasd.1 $e |- ( ph % ( ( ps (X) ch ) (X) th ) ) $.
  $( Times is associative. $)
  $( mcasd $p |- ( ph % ( ps (X) ( ch (X) th ) ) ) $= ? $. $)
$}
${
  mcasrd.1 $e |- ( ph % ( ps (X) ( ch (X) th ) ) ) $.
  $( Times is associative. $)
  $( mcasrd $p |- ( ph % ( ( ps (X) ch ) (X) th ) ) $= ? $. $)
$}
${
  mccod.1 $e |- ( ph % ( ps (X) ch ) ) $.
  $( Times is commutative. $)
  $( mccod $p |- ( ph % ( ch (X) ps ) ) $= ? $. $)
$}
${
  mcm1s.1 $e |- ( ph -O ch ) $.
  $( Times is monotone in its first argument. $)
  $( mcm1s $p |- ( ( ph (X) ps ) -O ( ch (X) ps ) ) $= ? $. $)
$}
${
  mcm2s.1 $e |- ( ps -O ch ) $.
  $( Times is monotone in its second argument. $)
  $( mcm2s $p |- ( ( ph (X) ps ) -O ( ph (X) ch ) ) $= ? $. $)
$}


${
  izerOLD.1 $e |- ph $.
  $( Insert Zero into Plus. $)
  $( izerOLD $p |- ( ph (+) 0 ) $= ? $. $)
$}
${
  ezerOLD.1 $e |- ( ph (+) 0 ) $.
  $( Remove Zero from Plus. $)
  $( ezerOLD $p |- ph $= ? $. $)
$}
${
  adas.1 $e |- ( ph % ( ( ps (+) ch ) (+) th ) ) $.
  $( Plus is associative. $)
  $( adas $p |- ( ph % ( ps (+) ( ch (+) th ) ) ) $= ? $. $)
$}
${
  adasr.1 $e |- ( ph % ( ps (+) ( ch (+) th ) ) ) $.
  $( Plus is associative. $)
  $( adasr $p |- ( ph % ( ( ps (+) ch ) (+) th ) ) $= ? $. $)
$}
${
  adco.1 $e |- ( ph % ( ps (+) ch ) ) $.
  $( Plus is commutative. $)
  $( adco $p |- ( ph % ( ch (+) ps ) ) $= ? $. $)
$}
${
  adm1s.1 $e |- ( ph -O ch ) $.
  $( Plus is monotone in its first argument. $)
  $( adm1s $p |- ( ( ph (+) ps ) -O ( ch (+) ps ) ) $= ? $. $)
$}
${
  adm2s.1 $e |- ( ps -O ch ) $.
  $( Plus is monotone in its second argument. $)
  $( adm2s $p |- ( ( ph (+) ps ) -O ( ph (+) ch ) ) $= ? $. $)
$}
${
  pems.1 $e |- ( ph -O ps ) $.
  $( "Of Course" is monotone. $)
  $( pems $p |- ( ! ph -O ! ps ) $= ? $. $)
$}

$( Absorption of Plus into With. Together with ~abs2 , this shows the additive operators form a lattice. $)
abs1 $p |- ( ( ph (+) ( ph & ps ) ) O-O ph ) $=
( wac wad wlb wli wneg df-ad lbi1 ax-init ax-eac1 dnid ax-iac
  dfli2i mdcoi dned syl eac1d lb2s iaci dflb lb2i ) AABCZDZAEUDAFZAUDFZ
  CUEUFUDAGZUCGZCZGZAUDUJAUCHZIUJAUJGZAUGGZULUMUIUGUGUHUGJUHUMUHAUCAB
  UCJKLOMLOPNQAUDUJAUJUJUGUJUGUHUIJRONUKSTUDAUAUB $.
$( Absorption into Plus. Together with ~abs1 , this shows the additive operators form a lattice. $)
$( abs2 $p |- ( ( ph & ( ph (+) ps ) ) O-O ph ) $= ? $. $)

$(
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
Intuitionistic logic
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#

There exists a nice conversion between statements in intuitionistic logic to statements in linear logic. Basically, just throw a bunch of `!` exponentials everywhere and you're good to go. Classical logic can then be recovered using the magic of double negatives.

This conversion relies on the fact that all statements on the "top level", meaning all axioms, proofs, and hypotheses, have an implicit `!` as shown by ~ax-ipe . The rules of classical and intuitionistic logic dictate that all expressions can be duplicated in this manner, which is accomplished by filling the subexpressions with lots of `!`.

In this section, all of the axioms of intuitionistic logic used in the Metamath iset.mm database are proven. This means that linear logic could feasibly be used as a background logic for set theory. I wonder what interesting consequences would come from this?
$)

$c /\ \/ -. -> <-> $.
$( Logical implication. Defined by ~df-im . $)
wim $a wff ( ph -> ps ) $.
$( Definition of `->`. It's `-O` but with some `!` splashed in for good measure. Note that only `ph` needs the exponential. When this statement is beneath a `!` or at the top level, this is equivalent to both sides having the exponential, because of  $)
df-im $a |- ( ( ph -> ps ) O-O ( ! ph -O ps ) ) $.

$( Logical conjunction. Defined by ~df-and . $)
wand $a wff ( ph /\ ps ) $.
$( Definition of `/\`. It's `&` but with some `!` splashed in for good measure. $)
df-and $a |- ( ( ph /\ ps ) O-O ( ! ph & ! ps ) ) $.
$( Logical disjunction. Defined by ~df-or . $)
wor $a wff ( ph \/ ps ) $.
$( Definition of `\/`. It's `(+)` but with some `!` splashed in for good measure. $)
df-or $a |- ( ( ph \/ ps ) O-O ( ! ph (+) ! ps ) ) $.
$( Logical negation. Defined by ~df-not . $)
wnot $a wff -. ph $.
$( Definition of `-.`. It's `~` but with some `!` splashed in for good measure. $)
df-not $a |- ( -. ph O-O ~ ! ph ) $.
$( Logical biconditional. Defined by ~df-bi . $)
wbi $a wff ( ph <-> ps ) $.
$( Definition of `<->`, in terms of the other logical connectives. $)
df-bi $a |- ( ( ph <-> ps ) O-O ( ( ph -> ps ) /\ ( ps -> ph ) ) ) $.

$( Principle of simplification. Allows discarding an unneeded antecedent. This is not possible with linear implication, since such a move would be non-linear; the `!` exponentials in the definition of the logical implication operator allow `ps` to be discarded. Axiom 1 in the Metamath iset.mm database. $)
$( simp $p |- ( ph -> ( ps -> ph ) ) $= ? $. $)
$( Axiom 2 in the Metamath iset.mm database. This uses the other property of the positive exponential, which is that it can be duplicated. $)
$( frege $p |- ( ( ph -> ( ps -> ch ) ) -> ( ( ph -> ps ) -> ( ph -> ch ) ) ) $= ? $. $)
${
  mp.min $e |- ph $.
  mp.maj $e |- ( ph -> ps ) $.
  $( Good ol' classic modus ponendo ponens. Doesn't it feel weird to have this be a theorem rather than an axiom? $)
  $( mp $p |- ps $= ? $. $)
$}
$( Left 'and' elimination. Axiom ia1 in iset.mm. $)
$( ea1 $p |- ( ( ph /\ ps ) -> ph ) $= ? $. $)
$( Right 'and' elimination. Axiom ia2 in iset.mm. $)
$( ea2 $p |- ( ( ph /\ ps ) -> ps ) $= ? $. $)
$( 'And' introduction. Axiom ia3 in iset.mm. $)
$( ia $p |- ( ph -> ( ps -> ( ph /\ ps ) ) ) $= ? $. $)
$( 'Or' elimination, and its converse. Axiom io in iset.mm. $)
$( or $p |- ( ( ( ph \/ ps ) -> ch ) <-> ( ( ph -> ch ) /\ ( ps -> ch ) ) ) $= ? $. $)
$( 'Not' introduction. Axiom in1 in iset.mm. $)
$( inot $p |- ( ( ph -> -. ph ) -> -. ph ) $= ? $. $)
$( 'Not' elimination. Axiom in2 in iset.mm. $)
$( enot $p |- ( -. ph -> ( ph -> ps ) ) $= ? $. $)


${
simpi.1 $e |- ph $.
$( Inference using simplification. Adds an unneeded antecedent. Inference for ~simp . $)
$( simpi $p |- ( ps -> ph ) $= ? $. $)
$}
${
fregei.1 $e |- ( ph -> ( ps -> ch ) ) $.
$( Inference using transposition. Inference for ~frege . $)
$( fregei $p |- ( ( ph -> ps ) -> ( ph -> ch ) ) $= ? $. $)
$}
${
  lbtrimd.1 $e |- ( ph -> ( ps O-O ch ) ) $.
  lbtrimd.2 $e |- ( ph -> ( ch O-O th ) ) $.
  $( Linear biconditional is transitive. Intuitionistic deduction for ~lbtr . $)
  $( lbtrimd $p |- ( ph -> ( ps O-O th ) ) $= ? $. $)
$}
${
  lbsymimd.1 $e |- ( ph -> ( ps O-O ch ) ) $.
  $( Linear biconditional is transitive. Intuitionistic deduction for ~lbsym . $)
  $( lbsymimd $p |- ( ph -> ( ch O-O ps ) ) $= ? $. $)
$}

$(
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
Message passing
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#

So, y'know, I was thinking to myself one day. I was thinking, hey, linear logic is pretty cool. You know what else is cool? Pi calculus. So I thought, hey, they seem pretty simiar, and maybe two great flavors go great together. So I figured I would add message passing to linear logic, since a stateful process is a great example of a resource. So let's see what happens.

In pi calculus, every object is a channel. Channels are given meaning by processes, which read from and write to them. Since processes are stateful, we can consider them to be the resources manipulated by linear logic. We will say that a process is valid, i.e. can appear in front of `|-`, if it always halts.

Pi calculus introduces three new operators, which operate on channel variables. They are:

<HTML>
<table class='desc-table'><tr>
<th>Name</th>     <th>Ref</th>                       <th>Description</th>
</tr><tr>
<td>Input   </td> <td>~wse : ` [ X << Y ] ph `</td>  <td>Writes to a channel and blocks</td>
</tr><tr>
<td>Output  </td> <td>~wre : ` [ X >> y ] ph `</td>  <td>Reads from a channel and blocks (binding a new name in the process)</td>
</tr><tr>
<td>Creation</td> <td>~wnu : ` v. x ph `</td>        <td>Creates a new channel</td>
</tr></table>
</HTML>

The remaining operators of pi calculus are directly implemented by the connectives of linear logic:

<HTML>
<table class='desc-table'><tr>
<th>Name</th>         <th>Ref</th>                       <th>Description</th>
</tr><tr>
<td>Concurrency</td>  <td>~wmc : ` ( ph (X) ps ) `</td>  <td>Run `ph` and `ps` in parallel, allowing communication over channels</td>
</tr><tr>
<td>Choice</td>       <td>~wac : ` ( ph & ps ) `</td>    <td>Nondeterministically run either `ph` or `ps`</td>
</tr><tr>
<td>Replication</td>  <td>~wpe : ` ! ph `</td>           <td>Run infinite copies of `ph` in parallel</td>
</tr><tr>
<td>Termination</td>  <td>~wone : ` 1 `</td>             <td>Halt the current process</td>
</tr></table>
</HTML>

Note that some of the channel variables are pink and capital like `X`, while others are red and lowercase like `y`. The only difference is that the red ones must be a literal channel name (similar to setvar variables in set.mm), while the pink ones can also be compound expressions. These compound expressions are known as nilads, because they act like functions that are evaluated as soon as they are encountered.

I'm almost certain that some of the axioms are redundant (or at least can be weakened), and it's very likely that this system is inconsistent, but hopefully it'll all work out.

$)

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
Axioms for message passing
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

$c var [ ] >> << := v. $.
$v a b c d f g h r s t u v w x y z $.
va $f var a $.
vb $f var b $.
vc $f var c $.
vd $f var d $.
vf $f var f $.
vg $f var g $.
vh $f var h $.
vr $f var r $.
vs $f var s $.
vt $f var t $.
vu $f var u $.
vv $f var v $.
vw $f var w $.
vx $f var x $.
vy $f var y $.
vz $f var z $.

$c nilad { } | $.
$c \. ' A. E. F. = e. $.
$v A B C D F G P Q X Y Z $.
na $f nilad A $.
nb $f nilad B $.
nc $f nilad C $.
nd $f nilad D $.
nf $f nilad F $.
ng $f nilad G $.
np $f nilad P $.
nq $f nilad Q $.
nx $f nilad X $.
ny $f nilad Y $.
nz $f nilad Z $.

$( A variable can be used as a nilad. $)
nvar $a nilad x $.
$( Sending operator. Writes `Y` to the channel `X`. $)
wse $a wff [ X << Y ] ph $.
$( Recieving operator. Reads from `X` and scopes the result to `y`. $)
wre $a wff [ X >> y ] ph $.
$( Creation operator. Creates and scopes a new channel `x`. It also has a dual ` ~ v. x ~ ph `, which has a meaning I don't quite understand. $)
wnu $a wff v. x ph $.

$( Proper substitution of `x` with `Y`. Although used as a primitive token in the axioms, it can actually be treated as a defined symbol; see ~dfsub . See ~nsub for proper substitution in nilads. $)
wsub $a wff [ x := Y ] ph $.

$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
Creation operator
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-

These axioms characterize the channel creation operator, `v.`. Its behavior resembles that of the `E.` quantifier in predicate logic, but its actual semantics are quite different. `v.` essentially isolates variable scopes, forbidding communication along a specific variable. On its own, though, it pretty much acts like any run-of-the-mill quantifier.
$)

${
  ax-int.1 $e |- ph $.
  $( Generalization. An "anti variable abstraction" can be removed from a "top-level" wff. What does that even mean? $)
  ax-int $a |- ~ v. x ~ ph $.
$}

${ $d x ph $.
$( A variable abstraction can be eliminated if the expression is free in that variable. $)
ax-nue $a |- ( v. x ph -O ph ) $.
$}
$( x is free in ` v. x `. $)
ax-nuf  $a |- ( v. x v. x ph -O v. x ph  ) $.
$( x is free in ` [ a >> x ] `. $)
ax-ref  $a |- ( v. x [ a >> x ] ph -O [ a >> x ] ph ) $.
$( x is free in ` ~ v. x ph `. There's that weird "anti variable abstraction" again... $)
ax-nnuf $a |- ( v. x ~ v. x ph -O ~ v. x ph ) $.

$( A wff can be surrounded by a variable abstraction $)
ax-nui $a |- ( ph -O v. x ph ) $.
$( Variables can be renamed without changing the meaning of an expression. $)
ax-nur $a |- ( v. x [ u << x ] ph -O v. y [ u << y ] ph ) $.

$( Commutation of `v.` with `<<`. $)
ax-nuse $a |- ( v. x [ u << v ] ph O-O [ u << v ] v. x ph ) $.
$( Commutation of `v.` with `>>`. $)
ax-nure $a |- ( v. x [ u >> v ] ph O-O [ u >> v ] v. x ph ) $.
$( Distribution of `v.` over `(+)`. $)
ax-nuad  $a |- ( v. x ( ph (+) ps ) O-O ( v. x ph (+) v. x ps ) ) $.
$( Commutation of `v.` into `(X)`. Note that `x` can only be bound in one factor. $)
ax-numc  $a |- ( v. x ( ph (X) v. x ps ) O-O ( v. x ph (X) v. x ps ) ) $.
$( Commutation of `v.` with `v.`. There is no need for a distinct variable condition on `x` and `y`, since ` ( v. x v. x ph O-O v. x v. x ph ) ` is a valid theorem. $)
ax-nunu $a |- ( v. x v. y ph O-O v. y v. x ph ) $.


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
Communication
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

${
$d a b x $. $d a b y $.
$( Abstraction on `<<`, left side. $)
$( ax-abse1 $a |- ( v. a v. b [ x << y ] ph O-O v. a ( [ a << y ] 1 (X) [ a >> b ] [ x << b ] v. b ph ) ) $. $)
$( Abstraction on `<<`, right side. $)
$( ax-abse2 $a |- ( [ x << y ] v. a v. b ph O-O v. a ( [ a << x ] 1 (X) [ a >> b ] [ b << y ] v. b ph ) ) $. $)
$( Abstraction on `>>`. $)
$( ax-abre  $a |- ( [ x >> y ] v. a v. b ph O-O v. a ( [ a << x ] 1 (X) [ a >> b ] [ b >> y ] v. b ph ) ) $. $)
$( Abstraction on an expression free of that variable. $)
$( ax-abf   $a |- ( v. x       v. a v. b ph O-O v. a ( [ a << x ] 1 (X) [ a >> b ] v. x       v. b ph ) ) $. $)
$}

${
$d u x $. $d u y $. $d v x $. $d v y $.
ax-subse1 $a |- ( [ x := y ] [ x << a ] ph O-O [ x := y ] [ y << a ] ph ) $.
ax-subse2 $a |- ( [ x := y ] [ a << x ] ph O-O [ x := y ] [ a << y ] ph ) $.
ax-subse3 $a |- ( [ x := y ] [ u << v ] ph O-O [ u << v ] [ x := y ] ph ) $.
ax-subre1 $a |- ( [ x := y ] [ x >> a ] ph O-O [ x := y ] [ y >> a ] ph ) $.
ax-subre2 $a |- ( [ x := y ] [ u >> v ] ph O-O [ u >> v ] [ x := y ] ph ) $.
ax-subnu1 $a |- ( [ x := y ] v. x ph O-O v. x ph ) $.
ax-subnu2 $a |- ( [ x := y ] v. u ph O-O v. u [ x := y ] ph ) $.
ax-subid  $a |- ( [ x := x ] ph O-O ph ) $.
$}

$( Message passing. $)
ax-send $a |- ( ( [ z << y ] ph (X) [ z >> x ] ps ) -O ( ph (X) [ x := y ] ps ) ) $.

$( If a blocked expression halts, both the block and the expression halt. $)
$( ax-wait  $a |- ( [ z << y ] ph (X) v. a [ z >> x ] ps ) -O ( ph (X) v. a ( [ a << y ] 1 (X) [ a >> x ] ps ) ) $. $)
$( Reading from a channel with nothing writing to it causes a deadlock. $)
ax-lock1 $a |- ( v. x ? [ x >> a ] 1 -O 0 ) $.
$( Writing to a channel with nothing reading from it causes a deadlock. $)
ax-lock2 $a |- ( v. x ? [ x << a ] 1 -O 0 ) $.



$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
Message passing theorems
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

$( Distribution of sending over `(+)`. $)
$( sead $p |- ( ( [ x << y ] 1 (X) ( ph (+) ps ) ) O-O ( ( [ x << y ] 1 (X) ph ) (+) ( [ x << y ] 1 (X) ps ) ) ) $= ? $. $)
$( Writing to a channel being read in multiple places causes a nondeterministic choice. $)
$( rech $p |- ( ( [ x << x ] ph (X) ( [ x >> x ] ps (X) [ x >> x ] ch ) ) O-O ( ph (X) ( ps (+) ch ) ) ) $= ? $. $)

$( $)
$( $p ( [ a >> b ] ph O-O $= ? $. $)

${
  $d z x $.
  $d z Y $.
  $d z ph $.
  $(  "Definition" of proper substitution. Or at least it would be, if I implemented proper substitution as a defined operator...

  This simply sends the desired value `Y` along a temporary channel `a`, and then reads it to the desired name `x`. $)
  $( dfsub $p |- ( [ x := Y ] ph O-O v. z ( [ z << Y ] 1 (X) [ z >> x ] ph ) ) $= ? $. $)
$}

${
$d x a $. $d y a $.
$( Proper substitution into the left side of `<<`. $)
$( abse1 $p |- ( [ x << y ] v. a ph O-O [ a := x ] [ a << y ] v. a ph ) $= ? $. $)
$( Proper substitution into the right side of `<<`. $)
$( abse2 $p |- ( [ x >> y ] v. a ph O-O [ a := y ] [ x >> a ] v. a ph ) $= ? $. $)
$( Proper substitution into the left side of `>>`. $)
$( abre1 $p |- ( [ x << y ] v. a ph O-O [ a := x ] [ a << y ] v. a ph ) $= ? $. $)
$( Proper substitution into an expression free of that variable. $)
$( abf $p |- ( v. x v. a ph O-O [ a := x ] v. x v. a ph ) $= ? $. $)
$( Proper substitution into the right side of `>>` (which is free of that variable). $)
$( abre2 $p |- ( [ x >> y ] v. a ph O-O [ a := y ] [ x >> y ] v. a ph ) $= ? $. $)
$}

$( Proper substitution of a variable for itself. $)
$( abid $p |- ( ph O-O [ x := x ] ph ) $= ? $. $)

$( TODO $)

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
Message passing dual operators
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=

One interesting consequence of adding pi calculus operators to linear logic is that the dualism of linear logic now applies to these operators. What even??? Wow this is crazy.
$)

$c <| |> ^. $.

$( Dual write operator. $)
wnse $a wff [ X <| Y ] ph $.
$( Dual read operator. $)
wnre $a wff [ X |> y ] ph $.
$( Dual creation operator. $)
wnnu $a wff ^. x ph $.

$( Definition of the dual write operator. $)
df-nse $a |- ( [ X <| Y ] ph O-O ~ [ X << Y ] ~ ph ) $.
$( Definition of the dual read operator. $)
df-nre $a |- ( [ X |> y ] ph O-O ~ [ X >> y ] ~ ph ) $.
$( Definition of the dual creation operator. $)
df-nnu $a |- ( ^. x ph O-O ~ v. x ~ ph ) $.

$( Nilad equality. $)
weq $a wff X = Y $.
${
  $d a x $. $d b x $.
  $d a y $. $d b y $.
  $( Definition of channel equality. Two nilads are equivalent if, when written to an arbitrary channel, that channel behaves the same way. We measure this by seeing if we can successfully read from it. $)
  df-eq $a |- ( X = Y O-O ^. a ( [ a << X ] [ a >> b ] 1 O-O [ a << Y ] [ a >> b ] 1 ) ) $.
$}


$( Equality can be `!`-ified. $)
$( eqpe $p |- ( X = Y -O ! X = Y ) $= ? $. $)
$( Equality is Euclidean. $)
$( eqeu $p |- ( ( X = Y (X) Y = Z ) -O X = Z ) $= ? $. $)
$( Equality is transitive. $)
$( eqtr $p |- ( ( X = Y (X) Y = Z ) -O X = Z ) $= ? $. $)
$( Equality is symmetric. $)
$( eqsym $p |- ( X = Y -O Y = X ) $= ? $. $)
${
  eqeui.1 $e |- X = Y $.
  eqeui.2 $e |- X = Z $.
  $( Equality is Euclidean. Inference for ~eqtr . $)
  $( eqeui $p |- Y = Z $= ? $. $)
$}
${
  eqtri.1 $e |- X = Y $.
  eqtri.2 $e |- Y = Z $.
  $( Equality is transitive. Inference for ~eqtr . $)
  $( eqtri $p |- X = Z $= ? $. $)
$}
${
  eqsymi.1 $e |- X = Y $.
  $( Equality is symmetric. Inference for ~eqsym . $)
  $( eqsymi $p |- Y = X $= ? $. $)
$}
${
  eqeud.1 $e |- ( ph -O X = Y ) $.
  eqeud.2 $e |- ( ph -O X = Z ) $.
  $( Equality is Euclidean. Deduction for ~eqeu . $)
  $( eqeud $p |- ( ph -O Y = Z ) $= ? $. $)
$}
${
  eqtrd.1 $e |- ( ph -O X = Y ) $.
  eqtrd.2 $e |- ( ph -O Y = Z ) $.
  $( Equality is transitive. Deduction for ~eqtr . $)
  $( eqtrd $p |- ( ph -O X = Z ) $= ? $. $)
$}
${
  eqsymd.1 $e |- ( ph -O X = Y ) $.
  $( Equality is symmetric. Deduction for ~eqsym . $)
  $( eqsymd $p |- ( ph -O Y = X ) $= ? $. $)
$}
${
  eqeuimd.1 $e |- ( ph -> X = Y ) $.
  eqeuimd.2 $e |- ( ph -> X = Z ) $.
  $( Equality is Euclidean. Intuitionistic deduction for ~eqeu . $)
  $( eqeuimd $p |- ( ph -> Y = Z ) $= ? $. $)
$}
${
  eqtrimd.1 $e |- ( ph -> X = Y ) $.
  eqtrimd.2 $e |- ( ph -> Y = Z ) $.
  $( Equality is transitive. Intuitionistic deduction for ~eqtr . $)
  $( eqtrimd $p |- ( ph -> X = Z ) $= ? $. $)
$}
${
  eqsymimd.1 $e |- ( ph -> X = Y ) $.
  $( Equality is symmetric. Intuitionistic deduction for ~eqsym . $)
  $( eqsymimd $p |- ( ph -> Y = X ) $= ? $. $)
$}

$( Sending is closed under equality (left side). $)
$( eqse1 $p |- ( X = Y -O ( [ X << a ] ph O-O [ Y << a ] ph ) ) $= ? $. $)
$( Sending is closed under equality (right side). $)
$( eqse2 $p |- ( X = Y -O ( [ a << X ] ph O-O [ a << Y ] ph ) ) $= ? $. $)
$( Recieving is closed under equality. $)
$( eqre  $p |- ( X = Y -O ( [ X >> a ] ph O-O [ Y >> a ] ph ) ) $= ? $. $)

$( Restatement of ~dfsub with nilad equality. $)
$( dfsub1 $p |- ( [ x := Y ] ph O-O ^. x ( x = Y -O ph ) ) $= ? $. $)

$( test $p |- ( v. b [ a << b ] 1 (X) ( [ a >> c ] 1 (X) [ c << a ] 1 ) ) $= ? $. $)

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
Nilad abstractions
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

$( A nilad abstraction. When used where a variable would normally belong, the variable used is instead the first one written by `ph` to `x`. (Any other operations on `x` will block indefinitely, as they would on a fresh channel.) This is a very useful concept, since this allows us to reason about expressions which carry values.

Keep in mind that these must be treated linearly like everything else, so using nilad variables multiple times may carry unintended consequences. Use `:=` as necessary to avoid this.

The nilad abstraction is characterized by ~df-nab . $)
nnab $a nilad { x | ph } $.

${
  $d a ph $.
  $d a ps $.
  $d a X $.
  $d a Y $.
  $d a x $.
  $d a y $.

  $( Using a nilad abstraction is the same as running the associated process `ph` and using its "return value" instead. Since the input to all other operators can be modeled using `<<`, this is enough to fully describe nilad abstractions.

  Unlike most defined operators, the nilad abstraction cannot directly be expanded to primitive symbols. Despite this, it is always possible to mechanically eliminate nilads from any expression that contains them by simply moving the process `ph` to before the variable `y` is used. $)
  df-nab $a |- ( [ x << { y | ph } ] ps O-O ( ph (X) [ y >> a ] [ x << a ] ps ) ) $.

  $( ~df-nab also works on nilads. $)
  $( dfnab1 $p |- ( [ X << { y | ph } ] ps O-O ( ph (X) [ y >> a ] [ X << a ] ps ) ) $= ? $. $)
  $( Read from a nilad. $)
  $( dfnab2 $p |- ( [ { x | ph } >> y ] ps O-O ( ph (X) [ x >> a ] [ a >> y ] ps ) ) $= ? $. $)
  $( Write to a nilad. $)
  $( dfnab3 $p |- ( [ { x | ph } << Y ] ps O-O ( ph (X) [ x >> a ] [ a << Y ] ps ) ) $= ? $. $)
$}

$( A simple nilad abstraction. Ordinary nilad abstractions use the bound channel as a sort of return channel, while this version immediately returns a fresh channel. $)
nvnab $a nilad { v. x | ph } $.
$( Definition of simple nilads. $)
df-vnab $a |- { v. x | ph } = { r | v. x [ r << x ] ph } $.

${
  $d a ph $.
  $d a ps $.
  $d a X $.
  $d a Y $.
  $d a x $.
  $d a y $.

  $( Write a simple nilad abstraction along a channel. $)
  $( vnab1 $p |- ( [ X << { v. y | ph } ] ps O-O v. y ( ph (X) [ X << y ] ps ) ) $= ? $. $)
  $( Read from a simple nilad abstraction. $)
  $( vnab2 $p |- ( [ { v. x | ph } >> y ] ps O-O v. x ( ph (X) [ x >> y ] ps ) ) $= ? $. $)
  $( Write to a simple nilad abstraction. $)
  $( vnab3 $p |- ( [ { v. x | ph } << Y ] ps O-O v. x ( ph (X) [ x << Y ] ps ) ) $= ? $. $)
$}

${
  $d x r $.
  $( A variable is equivalent to a nilad which always returns that variable. $)
  $( nvarjust $p |- x = { r | [ r << x ] 1 } $= ? $. $)
$}

$( Proper substitution of `x` with `Y` in the nilad `A`. See also ~wsub . $)
nsub $a nilad [ x := Y ] A $.
${
  $d r a x $.
  $d r a Y $.
  $d r a F $.
  $( The proper substitution of `x` with `Y` in `F`. $)
  df-nsub $a |- [ x := Y ] F = { r | v. a [ x := y ] [ F >> f ] [ r << f ] 1 } $.
$}

$(
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
Lambda calculus
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
$)

$( Lambda abstraction. $)
nla $a nilad \. x Y $.
${
  $d r f a x $.
  $d r f a Y $.
  $( Definition of lambda abstraction. The lambda exposes a "handle" `f` which reads a temporary communication channel `a`. The resulting function's input `x` and output `Y` are passed along `a`. The `!` exponential creates infinite instances of this function "provider", which can all run in parallel. Compare with ~df-fv to see how this function is called. $)
  df-la $a |- \. x Y = { v. f | ! [ f >> a ] [ a >> x ] [ a << Y ] 1 } $.
$}
$( Function application. $)
nfv $a nilad ( F ' X ) $.
${
  $d r a y F $.
  $d r a y X $.
  $( Definition of function application. This sends a temporary communication channel `a` to `F`, and communicates the input `X` and output `y`. Compare with ~df-la to see how functions are defined. $)
  df-fv $a |- ( F ' X ) = { r | v. a [ F << a ] [ a << X ] [ a >> y ] [ r << y ] 1 } $.
$}

$( Lambda evaluation theorem. $)
$( lav $p |- ( \. x F ' Y ) = [ x := Y ] F $= ? $. $)

$( Operator application. $)
nov $a nilad ( A F B ) $.
${
  $d r a y F $.
  $d r a y X $.
  $( Definition of operator application. It's simply two curried function applications. $)
  df-ov $a |- ( A F B ) = ( ( F ' A ) ' B ) $.
$}

$( Relation application. $)
$( TODO $)

$( Compose operator. $)
$( TODO $)

$c SS KK II ii $.
$( S combinator, the input distributor. $)
nss $a nilad SS $.
$( K combinator, the constant generator. $)
nkk $a nilad KK $.
$( I combinator, the identity function. $)
nii $a nilad II $.
$( Iota combinator, from which the S, K, and I combinators can be derived. $)
niota $a nilad ii $.
${
  $d a b c f $.
  $( Definition of the S combinator. $)
  df-ss $a |- SS = \. a \. b \. c ( ( b ' a ) ' ( c ' a ) ) $.
  $( Definition of the K combinator. $)
  df-kk $a |- KK = \. a \. b a $.
  $( Definition of the I combinator. $)
  df-ii $a |- II = \. a a $.
  $( Definition of the iota combinator in terms of `SS` and `KK`. $)
  df-iota $a |- ii = \. f ( ( f ' SS ) ' KK ) $.
$}

$( Construction of `II` from `ii`. $)
$( iiiota $p |- II = ( ii ' ii ) $= ? $. $)
$( Construction of `KK` from `ii`. $)
$( kkiota $p |- KK = ( ii ' ( ii ' ( ii ' ii ) ) ) $= ? $. $)
$( Construction of `SS` from `ii`. $)
$( ssiota $p |- SS = ( ii ' ( ii ' ( ii ' ( ii ' ii ) ) ) ) $= ? $. $)

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
Intuitionistic logic but with lambda calculus
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

$c True False |= |/= Impl And Or Not Iff $.

$( Function representing truth. $)
ntru $a nilad True $.
$( Function representing falsity. $)
nfal $a nilad False $.
${
  $d x y $.
  $( Church-encoding of truth. It takes two (curried) arguments and returns the first. Happens to be identical to ~nkk . $)
  df-tru $a |- True = \. x \. y x $.
  $( Church-encoding of falsity. It takes two (curried) arguments and returns the second. $)
  df-fal $a |- False = \. x \. y y $.
$}

$( Truth judgement. $)
weqtru $a wff |= P $.
$( Falsity judgement. $)
weqfal $a wff |/= P $.
$( A shorthand way of saying that a church-encoded value is true. I would totally use this as a new typecode, so I could prove statements with `|=` instead of `|-`, but it turns out that adds needless complexity (and mmj2 doesn't like it). $)
df-eqtru $a |- ( P = True O-O |= P ) $.
$( A shorthand way of saying that a church-encoded value is false. Note that this is not the opposite of ~df-eqtru (although they do exclude each other), since there are many more things an expression could equal. $)
df-eqfal $a |- ( P = False O-O |/= P ) $.
${
dfeqtru1i.1 $e |- P = True $.
$( Introduce `|=`. $)
$( dfeqtru1i $p |- |= P $= ? $. $)
$}
${
dfeqtru2i.1 $e |- |= P $.
$( Eliminate `|=`. $)
$( dfeqtru2i $p |- P = True $= ? $. $)
$}

$( `True` is true. Who'd've thunk it. $)
$( tru $p |- |= True $= ? $. $)

$( Function representing logical implication. $)
nlimpl $a nilad Impl $.
$( Function representing logical conjunction. $)
nland $a nilad And $.
$( Function representing logical disjunction. $)
nlor $a nilad Or $.
$( Function representing logical negation. $)
nlnot $a nilad Not $.
$( Function representing logical biconditional. $)
nliff $a nilad Iff $.
${
  $d a b x y $.
  $( Church-encoding of logical conjunction. $)
  df-limpl $a |- Impl = \. a \. b ( b a True ) $.
  $( Church-encoding of logical conjunction. $)
  df-land $a |- And = \. a \. b ( b a False ) $.
  $( Church-encoding of logical disjunction. $)
  df-lor $a |- Or = \. a \. b ( True a b ) $.
  $( Church-encoding of logical negation. $)
  df-lnot $a |- Not = \. a \. x \. y ( y a x ) $.
  $( Church-encoding of logical biconditional. $)
  df-liff $a |- Iff = \. a \. b ( b a ( Not ' b ) ) $.
$}



$(
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
Naive set theory
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
$)

$(
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
Quantifiers and equality
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#

Oh boy. This is unexplored territory for me.

I'm just going to copy all the FOL axioms from set.mm and hope that works. I'm preeety sure that all those are valid theorems in linear logic; I'm just not sure whether they're sufficient. I think they are. Probably.
$)

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
Axioms for predicate logic with equality
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

$( Universal quantifier. Characterized by ~ax-genOLD , ~ax-almd , ~ax-dis , ~ax-ex , ~ax-negf , ~ax-alcom . $)
wal $a wff A. x ph $.
$( Existential quantifier. Defined by ~df-ex . $)
wex $a wff E. x ph $.
$( Not-free predicate. Defined by ~df-nf . $)
wnf $a wff F. x ph $.
$( Equality. Charactrized by ~ax-ex , ~ax-sub , ~ax-aleq , ~ax-eqeu . $)
$( weqOLD $p |- ( ph -O ph ) $= ? $. $)
$( Set element predicate. For the purposes of predicate logic, it's just an arbitrary operator. $)
wel $a wff x e. y $.

${
  ax-genOLD.1 $e |- ph $.
  $( Axiom of generalization. Universal quantifiers can be freely added to the start of an expression. $)
  ax-genOLD $a |- A. x ph $.
$}

$( Quantified multiplicative disjunction. This "distributes" a quantifier over linear implication. $)
ax-almd $a |- ( A. x ( ph -O ps ) -O ( A. x ph -O A. x ps ) ) $.

${
  $d x ph $.
  $( Distinctness principle. When the value of `ph` is independent of `x`, a quantifier can be added. $)
  ax-dis $a |- ( ph -O A. x ph ) $.
$}

$( Axiom of existence. This axiom is secretly two useful axioms in one. It states that any `y` has an `x` that is equal to it. It also states that there exists something equal to itself, when `y` is substituted for `x`. $)
ax-ex $a |- ~ A. x ~ x = y $.

$( Equality is Euclidean. Combined with ~ax-ex , this implies that equality is symmetric and transitive. $)
ax-eqeu $a |- ( x = y -O ( x = z -O y = z ) ) $.

$( Left equality for binary predicate. This consumes the equality. $)
ax-eleq1 $a |- ( x = y -O ( x e. z -O y e. z ) ) $.

$( Right equality for binary predicate. This consumes the equality. $)
ax-eleq2 $a |- ( x = y -O ( z e. x -O z e. y ) ) $.

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
Auxiliary axioms for predicate logic with equality
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

$( Axiom of quantified negation. $)
ax-negf $a |- ( ~ A. x ph -O A. x ~ A. x ph ) $.

$( Quantifier commutation. $)
ax-alcom $a |- ( A. x A. y ph -O A. y A. x ph ) $.

$( Axiom of variable substitution. $)
ax-sub $a |- ( x = y -O ( A. y ph -O A. x ( x = y -O ph ) ) ) $.

$( Quantified equality. $)
ax-aleq $a |- ( ~ x = y -O ( y = z -O A. x y = z ) ) $.

$( Definition of existential quantifier. Dual of `A.`. $)
df-ex $a |- ( E. x ph O-O ~ A. x ~ ph ) $.
$( Definition of not-free predicate. $)
df-nf $a |- ( F. x ph O-O ( ~ ph -O A. x ph ) ) $.

$( $t
htmlcss '<STYLE TYPE="text/css">\n' +
  '<!--\n' +
  '  .wff { color: blue; }\n' +
  '  .var { color: red; }\n' +
  '  .nilad { color: #C3C; }\n' +
  '  .symvar { border-bottom:1px dotted;color:#C3C}\n' +
  '  .typecode { color: gray }\n' +
  '  .hidden { color: gray }\n' +
  '  @font-face {\n' +
  '    font-family: XITSMath-Regular;\n' +
  '    src: url(xits-math.woff);\n' +
  '  }\n' +
  '  .math { font-family: XITSMath-Regular }\n' +
  '  .desc-table { border: 1px outset grey }\n' +
  '  .desc-table td, .desc-table th { border: 1px inset grey }\n' +
  '  .command {\n' +
  '    border: 1px solid black;\n' +
  '    padding: 0em 0.1em;\n' +
  '    margin: 0em 0.1em;\n' +
  '    border-radius: 2px;\n' +
  '  }\n' +
  '-->\n' +
  '</STYLE>\n';

htmltitle "Linear Logic Proof Explorer";
htmlhome '<A HREF="..">Home</A>';


htmlvarcolor '<SPAN CLASS=wff>wff</SPAN> '
  + '<SPAN CLASS=var>var</SPAN> '
  + '<SPAN CLASS=nilad>nilad</SPAN> ';

althtmldef "|-"  as "<span class='typecode'>&#x22a6;</span> ";
althtmldef "wff" as "<span class='typecode'>wff</span> ";
althtmldef "var" as "<span class='typecode'>var</span> ";
althtmldef "nilad" as "<span class='typecode'>nilad</span> ";
althtmldef "("   as "(";
althtmldef ")"   as ")";


althtmldef "1"   as "1";
althtmldef "(X)" as " &otimes; ";
althtmldef "_|_" as "&#x22a5;";
althtmldef "%"   as " &#x214b; ";
althtmldef "`|`" as "&#x22a4;";
althtmldef "&"   as " &amp; ";
althtmldef "0"   as "0";
althtmldef "(+)" as " &oplus; ";
/*
althtmldef "1"   as "1";
althtmldef "(X)" as " &times; ";
althtmldef "_|_" as "0";
althtmldef "%"   as " + ";
althtmldef "`|`" as "&#x22a4;";
althtmldef "&"   as " &#x2293; ";
althtmldef "0"   as "&#x22a5;";
althtmldef "(+)" as " &#x2294; ";
*/

althtmldef "~"   as "~ ";
althtmldef "-O"  as " &#x22b8; ";
althtmldef "O-O" as " &#x29df; ";
althtmldef "?"   as "? ";
althtmldef "!"   as "! ";

althtmldef "->"  as " &rarr; ";
althtmldef "<->" as " &harr; ";
althtmldef "/\"  as " &and; ";
althtmldef "\/"  as " &or; ";
althtmldef "-."  as "&not; ";

althtmldef "["   as "[";
althtmldef "]"   as "] ";
/*althtmldef "["   as "<span class='command'>";
althtmldef "]"   as "</span>";*/
althtmldef ">>"  as " &#x226b; ";
althtmldef "<<"  as " &#x226a; ";
/*althtmldef ":="  as " := ";*/
althtmldef ":="  as " &#x2254; ";
althtmldef "v."  as "&nu;";
althtmldef "|>"  as " &#x25b7; ";
althtmldef "<|"  as " &#x25c1; ";
althtmldef "^."  as "&nabla;";
althtmldef "{"   as "{";
althtmldef "}"   as "}";
althtmldef "|"   as " | ";

althtmldef "\."  as "&lambda;";
althtmldef "'"   as "' ";
althtmldef "A."  as "&forall;";
althtmldef "E."  as "&exist;";
althtmldef "F."  as "&#8498;";
althtmldef "e."  as " &isin; ";
althtmldef "="   as " = ";

althtmldef "True"  as "True";
althtmldef "False"   as "False";
althtmldef "|="  as "&#x22a8; ";
althtmldef "|/="  as "&#x22ad; ";
althtmldef "Impl"  as " Impl ";
althtmldef "And"  as " And ";
althtmldef "Or"  as " Or ";
althtmldef "Not"  as "Not";
althtmldef "Iff"  as " Iff ";
althtmldef "SS"  as "S";
althtmldef "KK"  as "K";
althtmldef "II"  as "I";
althtmldef "ii"  as "&iota;";

althtmldef "ph"  as "<span class=wff>&#x1d711;</span>";
althtmldef "ps"  as "<span class=wff>&#x1d713;</span>";
althtmldef "ch"  as "<span class=wff>&#x1d712;</span>";
althtmldef "th"  as "<span class=wff>&#x1d703;</span>";
althtmldef "ta"  as "<span class=wff>&#x1d70f;</span>";
althtmldef "et"  as "<span class=wff>&#x1d702;</span>";
althtmldef "ze"  as "<span class=wff>&#x1d701;</span>";
althtmldef "si"  as "<span class=wff>&#x1d70e;</span>";
althtmldef "A"   as "<span class=nilad>A</span>";
althtmldef "B"   as "<span class=nilad>B</span>";
althtmldef "C"   as "<span class=nilad>C</span>";
althtmldef "D"   as "<span class=nilad>D</span>";
althtmldef "P"   as "<span class=nilad>P</span>";
althtmldef "Q"   as "<span class=nilad>Q</span>";
althtmldef "F"   as "<span class=nilad>F</span>";
althtmldef "G"   as "<span class=nilad>G</span>";
althtmldef "X"   as "<span class=nilad>X</span>";
althtmldef "Y"   as "<span class=nilad>Y</span>";
althtmldef "Z"   as "<span class=nilad>Z</span>";
althtmldef "a"   as "<span class=var>a</span>";
althtmldef "b"   as "<span class=var>b</span>";
althtmldef "c"   as "<span class=var>c</span>";
althtmldef "d"   as "<span class=var>d</span>";
althtmldef "f"   as "<span class=var>f</span>";
althtmldef "g"   as "<span class=var>g</span>";
althtmldef "h"   as "<span class=var>h</span>";
althtmldef "r"   as "<span class=var>r</span>";
althtmldef "s"   as "<span class=var>s</span>";
althtmldef "t"   as "<span class=var>t</span>";
althtmldef "u"   as "<span class=var>u</span>";
althtmldef "v"   as "<span class=var>v</span>";
althtmldef "w"   as "<span class=var>w</span>";
althtmldef "x"   as "<span class=var>x</span>";
althtmldef "y"   as "<span class=var>y</span>";
althtmldef "z"   as "<span class=var>z</span>";
$)
