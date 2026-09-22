$[ set.mm $]

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Translation invariance of Lebesgue measure on n-dimensional real numbers
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    vontranslem1.a $e |- ( ph -> A e. RR ) $.
    vontranslem1.b $e |- ( ph -> B e. RR ) $.
    vontranslem1.v $e |- ( ph -> V e. RR ) $.
    $( Lemma for ~ vontrans : the measure of a left-closed, right-open real
       interval is unchanged by translation.  (Contributed by Xander Mackay and
       Claude, 16-Sep-2026.) $)
    vontranslem1 $p |- ( ph -> ( vol ` ( ( A + V ) [,) ( B + V ) ) ) = ( vol `
      ( A [,) B ) ) )
                     $=
      ( caddc co clt wbr cmin cc0 cif cico cvol cfv recnd cr wcel pnpcan2d wceq
      ltadd1d bicomd ifbieq1d readdcld volico syl2anc 3eqtr4d ) ABDHIZCDHIZJKZU
      KUJLIZMNZBCJKZCBLIZMNZUJUKOIPQZBCOIPQZAULUOUMUPMAUOULABCDEFGUCUDACBDACFRA
      BERADGRUAUEAUJSTUKSTURUNUBABDEGUFACDFGUFUJUKUGUHABSTCSTUSUQUBEFBCUGUHUI
      $.
  $}

  ${
    $d X k $.  $d k ph $.
    vontranslem2.a $e |- ( ph -> A : X --> RR ) $.
    vontranslem2.b $e |- ( ph -> B : X --> RR ) $.
    vontranslem2.v $e |- ( ph -> V : X --> RR ) $.
    $( Lemma for ~ vontrans : the volume of a half-open box, the product of its
       edge lengths, is unchanged by translation.  (Contributed by Xander
       Mackay and Claude, 16-Sep-2026.) $)
    vontranslem2 $p |- ( ph -> prod_ k e. X ( vol ` ( ( ( A ` k ) + ( V ` k ) )
      [,) ( ( B ` k ) + ( V ` k ) ) ) ) = prod_ k e. X ( vol ` ( ( A ` k ) [,)
      ( B ` k ) ) ) )
                     $=
      ( cv cfv caddc co cico cvol wcel wa cr ffvelcdmda vontranslem1 prodeq2dv
      ) AFDJZBKZUBEKZLMUBCKZUDLMNMOKUCUENMOKDAUBFPQUCUEUDAFRUBBGSAFRUBCHSAFRUBE
      ISTUA $.
  $}

  ${
    elicoshift.a $e |- ( ph -> A e. RR ) $.
    elicoshift.b $e |- ( ph -> B e. RR ) $.
    elicoshift.v $e |- ( ph -> V e. RR ) $.
    elicoshift.y $e |- ( ph -> Y e. RR ) $.
    $( Membership in a left-closed, right-open real interval is unchanged by
       translating the point and the interval together.  (Contributed by Xander
       Mackay and Claude, 16-Sep-2026.) $)
    elicoshift $p |- ( ph -> ( ( Y - V ) e. ( A [,) B ) <-> Y e. ( ( A + V )
      [,) ( B + V ) ) ) )
                     $=
      ( co cr wcel cle wbr clt w3a caddc cico wb cxr cmin resubcld 2thd syl3anc
      leaddsub bicomd ltsubaddd 3anbi123d rexrd elico2 syl2anc readdcld 3bitr4d
      ) AEDUAJZKLZBUNMNZUNCONZPZEKLZBDQJZEMNZECDQJZONZPZUNBCRJLZEUTVBRJLZAUOUSU
      PVAUQVCAUOUSAEDIHUBIUCAVAUPABKLZDKLUSVAUPSFHIBDEUEUDUFAEDCIHGUGUHAVGCTLVE
      URSFACGUIBCUNUJUKAUTKLVBTLVFVDSABDFHULAVBACDGHULUIUTVBEUJUKUM $.
  $}

  ${
    $d V k $.  $d X k $.  $d Y k $.  $d k ph $.
    elixpshift.x $e |- ( ph -> X e. _V ) $.
    elixpshift.a $e |- ( ph -> A : X --> RR ) $.
    elixpshift.b $e |- ( ph -> B : X --> RR ) $.
    elixpshift.v $e |- ( ph -> V : X --> RR ) $.
    elixpshift.y $e |- ( ph -> Y : X --> RR ) $.
    $( Membership in an infinite Cartesian product of left-closed, right-open
       real intervals is unchanged by translating the point and every factor
       together.  (Contributed by Xander Mackay and Claude, 16-Sep-2026.) $)
    elixpshift $p |- ( ph -> ( ( Y oF - V ) e. X_ k e. X ( ( A ` k ) [,) ( B
      ` k ) ) <-> Y e. X_ k e. X ( ( ( A ` k ) + ( V ` k ) ) [,) ( ( B ` k ) +
      ( V ` k ) ) ) ) )
                     $=
      ( cmin co cfv wcel wa cvv cr ffvelcdmda cof cico wral caddc cixp wfn wceq
      cv ffnd adantr simpr fnfvof syl22anc eleq1d elicoshift bitrd ralbidva w3a
      wb df-3an a1i elixp2 ovexd inidm offn jca biantrurd 3bitr4d fexd ) ADUHZG
      EMUAZNZOZVJBOZVJCOZUBNZPZDFUCZVJGOZVNVJEOZUDNVOVTUDNUBNZPZDFUCZVLDFVPUEPZ
      GDFWAUEPZAVQWBDFAVJFPZQZVQVSVTMNZVPPWBWGVMWHVPWGGFUFZEFUFZFRPZWFVMWHUGAWI
      WFAFSGLUIZUJAWJWFAFSEKUIZUJAWKWFHUJAWFUKFMGERVJULUMUNWGVNVOVTVSAFSVJBITAF
      SVJCJTAFSVJEKTAFSVJGLTUOUPUQAVLRPZVLFUFZVRURZWNWOQZVRQZWDVRWPWRUSAWNWOVRU
      TVAWDWPUSADFVPVLVBVAAWQVRAWNWOAGEVKVCAFFMFGERRWLWMHHFVDVEVFVGVHAGRPZWIWCU
      RZWSWIQZWCQZWEWCWTXBUSAWSWIWCUTVAWEWTUSADFWAGVBVAAXAWCAWSWIAFSRGLHVIWLVFV
      GVHVH $.
  $}

  ${
    $d X k $.  $d k ph $.
    vontranslem5.t $e |- ( ph -> T = ( k e. X |-> <. ( ( 1st ` ( I ` k ) ) + (
      V ` k ) ) , ( ( 2nd ` ( I ` k ) ) + ( V ` k ) ) >. ) )
                       $.
    vontranslem5.i $e |- ( ph -> I : X --> ( RR X. RR ) ) $.
    vontranslem5.v $e |- ( ph -> V : X --> RR ) $.
    $( Lemma for ~ vontrans : the translate of a finite family of half-open
       interval endpoints is such a family.  (Contributed by Xander Mackay and
       Claude, 16-Sep-2026.) $)
    vontranslem5 $p |- ( ph -> T : X --> ( RR X. RR ) ) $=
      ( cv cfv c1st caddc co c2nd cr wcel ffvelcdmda syl readdcld cop cxp xp1st
      wa xp2nd opelxpd fmpt3d ) ACFCJZDKZLKZUHEKZMNZUIOKZUKMNZUAPPUBZBGAUHFQUDZ
      ULUNPPUPUJUKUPUIUOQZUJPQAFUOUHDHRZUIPPUCSAFPUHEIRZTUPUMUKUPUQUMPQURUIPPUE
      SUSTUFUG $.
  $}

  ${
    $d X k $.  $d k ph $.
    vontranslem6.t $e |- ( ph -> T = ( k e. X |-> <. ( ( 1st ` ( I ` k ) ) + (
      V ` k ) ) , ( ( 2nd ` ( I ` k ) ) + ( V ` k ) ) >. ) )
                       $.
    vontranslem6.i $e |- ( ph -> I : X --> ( RR X. RR ) ) $.
    vontranslem6.v $e |- ( ph -> V : X --> RR ) $.
    $( Lemma for ~ vontrans : the projection of the translated family onto one
       dimension is the translated half-open interval.  (Contributed by Xander
       Mackay and Claude, 16-Sep-2026.) $)
    vontranslem6 $p |- ( ( ph /\ k e. X ) -> ( ( [,) o. T ) ` k ) = ( ( ( 1st `
      ( I ` k ) ) + ( V ` k ) ) [,) ( ( 2nd ` ( I ` k ) ) + ( V ` k ) ) ) )
                     $=
      ( wcel cico cfv c1st c2nd co caddc cr wceq ffvelcdmda syl cv vontranslem5
      wa ccom cxp adantr simpr fvovco xp1st readdcld xp2nd opelxpd fvmpt2d ovex
      wf cop op1std op2ndd oveq12d eqtrd ) ACUAZFJZUCZVAKBUDLVABLZMLZVDNLZKOVAD
      LZMLZVAELZPOZVGNLZVIPOZKOVCBKQQFVAAFQQUEZBUOVBABCDEFGHIUBUFAVBUGUHVCVEVJV
      FVLKVCVDVJVLUPZRZVEVJRACFVNBVMGVCVJVLQQVCVHVIVCVGVMJZVHQJAFVMVADHSZVGQQUI
      TAFQVAEISZUJVCVKVIVCVPVKQJVQVGQQUKTVRUJULUMZVJVLVDVHVIPUNZVKVIPUNZUQTVCVO
      VFVLRVSVJVLVDVTWAURTUSUT $.
  $}

  ${
    $d X k $.  $d k ph $.
    vontranslem7.t $e |- ( ph -> T = ( k e. X |-> <. ( ( 1st ` ( I ` k ) ) + (
      V ` k ) ) , ( ( 2nd ` ( I ` k ) ) + ( V ` k ) ) >. ) )
                       $.
    vontranslem7.i $e |- ( ph -> I : X --> ( RR X. RR ) ) $.
    vontranslem7.v $e |- ( ph -> V : X --> RR ) $.
    $( Lemma for ~ vontrans : the measure of one edge of a half-open box is
       unchanged by translation.  (Contributed by Xander Mackay and Claude,
       16-Sep-2026.) $)
    vontranslem7 $p |- ( ( ph /\ k e. X ) -> ( vol ` ( ( [,) o. T ) ` k ) ) = (
      vol ` ( ( [,) o. I ) ` k ) ) )
                     $=
      ( wcel cfv caddc co cico cvol ccom cr ffvelcdmda syl fveq2d c1st c2nd cxp
      cv wa xp1st xp2nd vontranslem1 vontranslem6 adantr simpr fvovco 3eqtr4d
      wf ) ACUDZFJZUEZUODKZUAKZUOEKZLMURUBKZUTLMNMZOKUSVANMZOKUONBPKZOKUONDPKZO
      KUQUSVAUTUQURQQUCZJZUSQJAFVFUODHRZURQQUFSUQVGVAQJVHURQQUGSAFQUOEIRUHUQVDV
      BOABCDEFGHIUITUQVEVCOUQDNQQFUOAFVFDUNUPHUJAUPUKULTUM $.
  $}

  ${
    $d X k $.  $d k ph $.
    vontranslem8.t $e |- ( ph -> T = ( k e. X |-> <. ( ( 1st ` ( I ` k ) ) + (
      V ` k ) ) , ( ( 2nd ` ( I ` k ) ) + ( V ` k ) ) >. ) )
                       $.
    vontranslem8.i $e |- ( ph -> I : X --> ( RR X. RR ) ) $.
    vontranslem8.v $e |- ( ph -> V : X --> RR ) $.
    $( Lemma for ~ vontrans : the volume of a half-open box, given by its
       endpoint family, is unchanged by translation.  (Contributed by Xander
       Mackay and Claude, 16-Sep-2026.) $)
    vontranslem8 $p |- ( ph -> prod_ k e. X ( vol ` ( ( [,) o. T ) ` k ) ) =
      prod_ k e. X ( vol ` ( ( [,) o. I ) ` k ) ) )
                     $=
      ( cv cico ccom cfv cvol vontranslem7 prodeq2dv ) AFCJZKBLMNMQKDLMNMCABCDE
      FGHIOP $.
  $}

  ${
    $d V k $.  $d X k $.  $d Y k $.  $d k ph $.
    ofsubpreim.x $e |- ( ph -> X e. _V ) $.
    ofsubpreim.v $e |- ( ph -> V : X --> RR ) $.
    ofsubpreim.y $e |- ( ph -> Y : X --> RR ) $.
    ofsubpreim.c $e |- ( ( ph /\ k e. X ) -> ( ( ( Y ` k ) - ( V ` k ) ) e. C
      <-> ( Y ` k ) e. D ) )
                       $.
    $( Translating a point by ` V ` and testing coordinatewise membership in
       ` C ` is the same as testing the untranslated point against the class
       ` D ` the translation carries ` C ` to, coordinatewise, over an infinite
       index set.  (Contributed by Xander Mackay and Claude, 16-Sep-2026.) $)
    ofsubpreim $p |- ( ph -> ( ( Y oF - V ) e. X_ k e. X C <-> Y e. X_ k e. X
      D ) )
                     $=
      ( cmin cfv wcel wa wfn cvv cr wb a1i cv cof co wral cixp wceq ffnd adantr
      simpr fnfvof syl22anc eleq1d bitrd ralbidva w3a df-3an elixp2 ovexd inidm
      offn jca biantrurd 3bitr4d fexd ) ADUAZGELUBZUCZMZBNZDFUDZVEGMZCNZDFUDZVG
      DFBUENZGDFCUENZAVIVLDFAVEFNZOZVIVKVEEMLUCZBNVLVQVHVRBVQGFPZEFPZFQNZVPVHVR
      UFAVSVPAFRGJUGZUHAVTVPAFREIUGZUHAWAVPHUHAVPUIFLGEQVEUJUKULKUMUNAVGQNZVGFP
      ZVJUOZWDWEOZVJOZVNVJWFWHSAWDWEVJUPTVNWFSADFBVGUQTAWGVJAWDWEAGEVFURAFFLFGE
      QQWBWCHHFUSUTVAVBVCAGQNZVSVMUOZWIVSOZVMOZVOVMWJWLSAWIVSVMUPTVOWJSADFCGUQT
      AWKVMAWIVSAFRQGJHVDWBVAVBVCVC $.
  $}

  ${
    $d V k $.  $d X k $.  $d Y k $.  $d k ph $.
    vontranslem10.t $e |- ( ph -> T = ( k e. X |-> <. ( ( 1st ` ( I ` k ) ) + (
      V ` k ) ) , ( ( 2nd ` ( I ` k ) ) + ( V ` k ) ) >. ) )
                        $.
    vontranslem10.x $e |- ( ph -> X e. _V ) $.
    vontranslem10.i $e |- ( ph -> I : X --> ( RR X. RR ) ) $.
    vontranslem10.v $e |- ( ph -> V : X --> RR ) $.
    vontranslem10.y $e |- ( ph -> Y : X --> RR ) $.
    $( Lemma for ~ vontrans : a point lies in a translated half-open box
       exactly when its translate back lies in the box.  (Contributed by Xander
       Mackay and Claude, 16-Sep-2026.) $)
    vontranslem10 $p |- ( ph -> ( ( Y oF - V ) e. X_ k e. X ( ( [,) o. I ) ` k
      ) <-> Y e. X_ k e. X ( ( [,) o. T ) ` k ) ) )
                      $=
      ( cico ccom cfv wcel co caddc cr ffvelcdmda cv wa cmin c1st cxp xp1st syl
      c2nd xp2nd elicoshift wf adantr fvovco eleq2d vontranslem6 ofsubpreim
      simpr 3bitr4d ) ACUAZMDNOZUSMBNOZCEFGIKLAUSFPZUBZUSGOZUSEOZUCQZUSDOZUDOZV
      GUHOZMQZPVDVHVERQVIVERQMQZPVFUTPVDVAPVCVHVIVEVDVCVGSSUEZPZVHSPAFVLUSDJTZV
      GSSUFUGVCVMVISPVNVGSSUIUGAFSUSEKTAFSUSGLTUJVCUTVJVFVCDMSSFUSAFVLDUKVBJULA
      VBUQUMUNVCVAVKVDABCDEFHJKUOUNURUP $.
  $}

  ${
    $d X k $.
    vontranslem11.j $e |- ( ph -> J = ( j e. NN |-> ( k e. X |-> <. ( ( 1st ` (
      ( I ` j ) ` k ) ) + ( V ` k ) ) , ( ( 2nd ` ( ( I ` j ) ` k ) ) + ( V ` k
      ) ) >. ) ) )
                        $.
    vontranslem11.x $e |- ( ph -> X e. _V ) $.
    $( Lemma for ~ vontrans : the value of the translated cover family at one
       index is the translated endpoint family.  (Contributed by Xander Mackay
       and Claude, 16-Sep-2026.) $)
    vontranslem11 $p |- ( ( ph /\ j e. NN ) -> ( J ` j ) = ( k e. X |-> <. ( (
      1st ` ( ( I ` j ) ` k ) ) + ( V ` k ) ) , ( ( 2nd ` ( ( I ` j ) ` k ) ) +
      ( V ` k ) ) >. ) )
                      $=
      ( cn cv cfv c1st caddc co c2nd cop cmpt cvv wcel mptexd adantr fvmpt2d )
      ABJCGCKZBKZDLLZMLUDFLZNOUFPLUGNOQZRZESHAUISTUEJTACGUHSIUAUBUC $.
  $}

  ${
    $d X j k $.  $d j k ph $.
    vontranslem12.j $e |- ( ph -> J = ( j e. NN |-> ( k e. X |-> <. ( ( 1st ` (
      ( I ` j ) ` k ) ) + ( V ` k ) ) , ( ( 2nd ` ( ( I ` j ) ` k ) ) + ( V ` k
      ) ) >. ) ) )
                        $.
    vontranslem12.x $e |- ( ph -> X e. _V ) $.
    vontranslem12.i $e |- ( ph -> I e. ( ( ( RR X. RR ) ^m X ) ^m NN ) ) $.
    vontranslem12.v $e |- ( ph -> V : X --> RR ) $.
    $( Lemma for ~ vontrans : the translate of a countable family of half-open
       boxes is such a family.  (Contributed by Xander Mackay and Claude,
       16-Sep-2026.) $)
    vontranslem12 $p |- ( ph -> J e. ( ( ( RR X. RR ) ^m X ) ^m NN ) ) $=
      ( cr cmap co cn cvv wcel a1i cfv wf cxp ovexd nnex cv c1st caddc c2nd cop
      cmpt wa vontranslem11 reex xpex adantr elmapi syl ffvelcdmda vontranslem5
      elmapdd eqeltrrd fmpt3d ) ALLUAZGMNZOEPPAVBGMUBOPQAUCRABOCGCUDZBUDZDSZSZU
      ESVDFSZUFNVGUGSVHUFNUHUIZVCEHAVEOQZUJZVEESZVIVCABCDEFGHIUKZVKVBGVLPPVBPQV
      KLLULULUMRAGPQVJIUNVKVLCVFFGVMVKVFVCQGVBVFTAOVCVEDADVCOMNQOVCDTJDVCOUOUPU
      QVFVBGUOUPAGLFTVJKUNURUSUTVAUS $.
  $}

  ${
    $d X k $.  $d j k ph $.
    vontranslem13.j $e |- ( ph -> J = ( j e. NN |-> ( k e. X |-> <. ( ( 1st ` (
      ( I ` j ) ` k ) ) + ( V ` k ) ) , ( ( 2nd ` ( ( I ` j ) ` k ) ) + ( V ` k
      ) ) >. ) ) )
                        $.
    vontranslem13.x $e |- ( ph -> X e. _V ) $.
    vontranslem13.i $e |- ( ph -> I e. ( ( ( RR X. RR ) ^m X ) ^m NN ) ) $.
    vontranslem13.v $e |- ( ph -> V : X --> RR ) $.
    $( Lemma for ~ vontrans : the sum of the volumes of a countable family of
       half-open boxes is unchanged by translation.  (Contributed by Xander
       Mackay and Claude, 16-Sep-2026.) $)
    vontranslem13 $p |- ( ph -> ( sum^ ` ( j e. NN |-> prod_ k e. X ( vol ` ( (
      [,) o. ( J ` j ) ) ` k ) ) ) ) = ( sum^ ` ( j e. NN |-> prod_ k e. X (
      vol ` ( ( [,) o. ( I ` j ) ) ` k ) ) ) ) )
                      $=
      ( cn cv cico cfv ccom cvol wcel cr wf cprod cmpt csumge0 wa vontranslem11
      cxp cmap co elmapi syl ffvelcdmda adantr vontranslem8 mpteq2dva fveq2d )
      ABLGCMZNBMZEOZPOQOCUAZUBBLGUPNUQDOZPOQOCUAZUBUCABLUSVAAUQLRZUDZURCUTFGABC
      DEFGHIUEVCUTSSUFZGUGUHZRGVDUTTALVEUQDADVELUGUHRLVEDTJDVELUIUJUKUTVDGUIUJA
      GSFTVBKULUMUNUO $.
  $}

  ${
    $d V j k $.  $d X k $.  $d Y j k $.  $d j k ph $.
    vontranslem14.j $e |- ( ph -> J = ( j e. NN |-> ( k e. X |-> <. ( ( 1st ` (
      ( I ` j ) ` k ) ) + ( V ` k ) ) , ( ( 2nd ` ( ( I ` j ) ` k ) ) + ( V ` k
      ) ) >. ) ) )
                        $.
    vontranslem14.x $e |- ( ph -> X e. _V ) $.
    vontranslem14.i $e |- ( ph -> I e. ( ( ( RR X. RR ) ^m X ) ^m NN ) ) $.
    vontranslem14.v $e |- ( ph -> V : X --> RR ) $.
    vontranslem14.y $e |- ( ph -> Y : X --> RR ) $.
    $( Lemma for ~ vontrans : a point lies in the union of a translated
       countable family of half-open boxes exactly when its translate back lies
       in the union of the original family.  (Contributed by Xander Mackay and
       Claude, 16-Sep-2026.) $)
    vontranslem14 $p |- ( ph -> ( ( Y oF - V ) e. U_ j e. NN X_ k e. X ( ( [,)
      o. ( I ` j ) ) ` k ) <-> Y e. U_ j e. NN X_ k e. X ( ( [,) o. ( J ` j ) )
      ` k ) ) )
                      $=
      ( co cfv wcel cn adantr cr wf cmin cico ccom cixp wrex ciun vontranslem11
      cof cv wa cvv cxp cmap elmapi syl ffvelcdmda vontranslem10 rexbidva eliun
      3bitr4g ) AHFUAUHNZCGCUIZUBBUIZDOZUCOUDZPZBQUEHCGVBUBVCEOZUCOUDZPZBQUEVAB
      QVEUFPHBQVHUFPAVFVIBQAVCQPZUJZVGCVDFGHABCDEFGIJUGAGUKPVJJRVKVDSSULZGUMNZP
      GVLVDTAQVMVCDADVMQUMNPQVMDTKDVMQUNUOUPVDVLGUNUOAGSFTVJLRAGSHTVJMRUQURBVAQ
      VEUSBHQVHUSUT $.
  $}

  ${
    $d A k $.  $d V k $.  $d X k $.  $d k ph $.
    ofaddsubidd.x $e |- ( ph -> X e. _V ) $.
    ofaddsubidd.a $e |- ( ph -> A : X --> RR ) $.
    ofaddsubidd.v $e |- ( ph -> V : X --> RR ) $.
    $( Translating a function by ` V ` and then back by ` V ` recovers the
       function.  (Contributed by Xander Mackay and Claude, 16-Sep-2026.) $)
    ofaddsubidd $p |- ( ph -> ( ( A oF + V ) oF - V ) = A ) $=
      ( vk caddc cof co cmin cvv cr ffnd offn wcel cfv wfn adantr inidm cv wceq
      wa simpr fnfvof syl22anc oveq1d ffvelcdmda recnd pncand 3eqtrd eqfnfvd )
      AHDBCIJKZCLJKZBADDLDUNCMMADDIDBCMMADNBFOZADNCGOZEEDUAZPZUQEEURPUPAHUBZDQZ
      UDZUTUORZUTUNRZUTCRZLKZUTBRZVEIKZVELKVGVBUNDSZCDSZDMQZVAVCVFUCAVIVAUSTAVJ
      VAUQTZAVKVAETZAVAUEZDLUNCMUTUFUGVBVDVHVELVBBDSZVJVKVAVDVHUCAVOVAUPTVLVMVN
      DIBCMUTUFUGUHVBVGVEVBVGADNUTBFUIUJVBVEADNUTCGUIUJUKULUM $.
  $}

  ${
    $d I y $.  $d J y $.  $d S y $.  $d V j k $.  $d X j k y $.  $d j k ph y $.
    vontranslem16.j $e |- ( ph -> J = ( j e. NN |-> ( k e. X |-> <. ( ( 1st ` (
      ( I ` j ) ` k ) ) + ( V ` k ) ) , ( ( 2nd ` ( ( I ` j ) ` k ) ) + ( V ` k
      ) ) >. ) ) )
                        $.
    vontranslem16.x $e |- ( ph -> X e. _V ) $.
    vontranslem16.i $e |- ( ph -> I e. ( ( ( RR X. RR ) ^m X ) ^m NN ) ) $.
    vontranslem16.v $e |- ( ph -> V : X --> RR ) $.
    $( Lemma for ~ vontrans : a cover of a set gives a cover of its translate.
       (Contributed by Xander Mackay and Claude, 16-Sep-2026.) $)
    vontranslem16 $p |- ( ( ph /\ S C_ U_ j e. NN X_ k e. X ( ( [,) o. ( I ` j
      ) ) ` k ) ) -> { y e. ( RR ^m X ) | ( y oF - V ) e. S } C_ U_ j e. NN X_
      k e. X ( ( [,) o. ( J ` j ) ) ` k ) )
                      $=
      ( cn cv cfv co wcel cr adantr cico ccom cixp ciun wss wa cmin cmap simp1r
      cof w3a simp3 sseldd wb c1st caddc c2nd cop cmpt cvv cxp wf elmapi adantl
      wceq vontranslem14 adantlr 3adant3 mpbid rabssdv ) ACDNEIEOZUADOZFPZUBPUC
      UDZUEZUFZBOZHUGUJQZCRZBSIUHQZDNEIVKUAVLGPUBPUCUDZVPVQVTRZVSUKZVRVNRZVQWAR
      ZWCCVNVRAVOWBVSUIVPWBVSULUMVPWBWDWEUNZVSAWBWFVOAWBUFDEFGHIVQAGDNEIVKVMPZU
      OPVKHPZUPQWGUQPWHUPQURUSUSVEWBJTAIUTRWBKTAFSSVAIUHQNUHQRWBLTAISHVBWBMTWBI
      SVQVBAVQSIVCVDVFVGVHVIVJ $.
  $}

  ${
    $d I x $.  $d J x $.  $d S j k x $.  $d S u v x $.  $d S x y $.
    $d V j k x $.  $d V v x $.  $d V x y $.  $d X k x $.  $d X x y $.
    $d j k ph x $.  $d ph u v x $.
    vontranslem17.j $e |- ( ph -> J = ( j e. NN |-> ( k e. X |-> <. ( ( 1st ` (
      ( I ` j ) ` k ) ) + ( V ` k ) ) , ( ( 2nd ` ( ( I ` j ) ` k ) ) + ( V ` k
      ) ) >. ) ) )
                        $.
    vontranslem17.x $e |- ( ph -> X e. _V ) $.
    vontranslem17.i $e |- ( ph -> I e. ( ( ( RR X. RR ) ^m X ) ^m NN ) ) $.
    vontranslem17.v $e |- ( ph -> V : X --> RR ) $.
    vontranslem17.s $e |- ( ph -> S C_ ( RR ^m X ) ) $.
    $( Lemma for ~ vontrans : a cover of the translate of a set gives a cover
       of the set.  (Contributed by Xander Mackay and Claude, 16-Sep-2026.) $)
    vontranslem17 $p |- ( ( ph /\ { y e. ( RR ^m X ) | ( y oF - V ) e. S } C_
      U_ j e. NN X_ k e. X ( ( [,) o. ( J ` j ) ) ` k ) ) -> S C_ U_ j e. NN X_
      k e. X ( ( [,) o. ( I ` j ) ) ` k ) )
                      $=
      ( cv co wcel cr cfv cvv vx vu vv cmin cof cmap crab cn cico ccom cixp wss
      ciun wa caddc wceq adantr wf sselda elmapi syl ofaddsubidd simplr oveq1
      adantlr eleq1d reex a1i readdcl adantl inidm elmapdd simpr eqeltrd elrabd
      off sseldd wb c1st c2nd cop cmpt cxp vontranslem14 mpbird eqeltrrd ssd )
      ABOZHUDUEZPZCQZBRIUFPZUGZDUHEIEOZUIDOZGSUJSUKUMZULZUNZUACDUHEIWNUIWOFSZUJ
      SUKUMZWRUAOZCQZUNZXAHUOUEPZHWIPZXAWTAXBXEXAUPWQAXBUNZXAHIAITQXBKUQZXFXAWL
      QIRXAURACWLXANUSXARIUTVAZAIRHURXBMUQZVBZVEXCXEWTQZXDWPQZXCWMWPXDAWQXBVCAX
      BXDWMQWQXFWKXECQBXDWLWHXDUPWJXECWHXDHWIVDVFXFRIXDTTRTQXFVGVHXGXFUBUCIIIUO
      RRRXAHTTUBOZRQUCOZRQUNXMXNUOPRQXFXMXNVIVJXHXIXGXGIVKVPZVLXFXEXACXJAXBVMVN
      VOVEVQAXBXKXLVRWQXFDEFGHIXDAGDUHEIWNWSSZVSSWNHSZUOPXPVTSXQUOPWAWBWBUPXBJU
      QXGAFRRWCIUFPUHUFPQXBLUQXIXOWDVEWEWFWG $.
  $}

  ${
    $d I y $.  $d J y $.  $d S j k y $.  $d V j k y $.  $d X j k y $.
    $d j k ph y $.
    vontranslem18.j $e |- ( ph -> J = ( j e. NN |-> ( k e. X |-> <. ( ( 1st ` (
      ( I ` j ) ` k ) ) + ( V ` k ) ) , ( ( 2nd ` ( ( I ` j ) ` k ) ) + ( V ` k
      ) ) >. ) ) )
                        $.
    vontranslem18.x $e |- ( ph -> X e. _V ) $.
    vontranslem18.i $e |- ( ph -> I e. ( ( ( RR X. RR ) ^m X ) ^m NN ) ) $.
    vontranslem18.v $e |- ( ph -> V : X --> RR ) $.
    vontranslem18.s $e |- ( ph -> S C_ ( RR ^m X ) ) $.
    $( Lemma for ~ vontrans : a countable family of half-open boxes covers a
       set exactly when its translate covers the translate of the set.
       (Contributed by Xander Mackay and Claude, 16-Sep-2026.) $)
    vontranslem18 $p |- ( ph -> ( S C_ U_ j e. NN X_ k e. X ( ( [,) o. ( I ` j
      ) ) ` k ) <-> { y e. ( RR ^m X ) | ( y oF - V ) e. S } C_ U_ j e. NN X_ k
      e. X ( ( [,) o. ( J ` j ) ) ` k ) ) )
                      $=
      ( cn cv cico cfv ccom cixp ciun wss cmin cof wcel cmap crab vontranslem16
      co cr vontranslem17 impbida ) ACDOEIEPZQDPZFRSRTUAUBBPHUCUDUICUEBUJIUFUIU
      GDOEIUMQUNGRSRTUAUBABCDEFGHIJKLMUHABCDEFGHIJKLMNUKUL $.
  $}

  ${
    $d S f i y $.  $d S i j k y $.  $d V f i m n r s $.  $d V i j k m n r s $.
    $d V f i r s y $.  $d X f i m n r s $.  $d X i j k m n r s $.
    $d X f i r s y $.  $d f i y z $.  $d i j k ph y z $.
    vontranslem19.x $e |- ( ph -> X e. _V ) $.
    vontranslem19.v $e |- ( ph -> V : X --> RR ) $.
    vontranslem19.s $e |- ( ph -> S C_ ( RR ^m X ) ) $.
    vontranslem19.m $e |- M = { z e. RR* | E. i e. ( ( ( RR X. RR ) ^m X ) ^m
      NN ) ( S C_ U_ j e. NN X_ k e. X ( ( [,) o. ( i ` j ) ) ` k ) /\ z = (
      sum^ ` ( j e. NN |-> prod_ k e. X ( vol ` ( ( [,) o. ( i ` j ) ) ` k ) )
      ) ) ) }
                        $.
    vontranslem19.n $e |- N = { z e. RR* | E. f e. ( ( ( RR X. RR ) ^m X ) ^m
      NN ) ( { y e. ( RR ^m X ) | ( y oF - V ) e. S } C_ U_ n e. NN X_ m e. X (
      ( [,) o. ( f ` n ) ) ` m ) /\ z = ( sum^ ` ( n e. NN |-> prod_ m e. X (
      vol ` ( ( [,) o. ( f ` n ) ) ` m ) ) ) ) ) }
                        $.
    $( Lemma for ~ vontrans : every candidate outer measure sum for a set is
       one for its translate.  (Contributed by Xander Mackay and Claude,
       16-Sep-2026.) $)
    vontranslem19 $p |- ( ph -> M C_ N ) $=
      ( cfv vr vs cn cv cico ccom cixp ciun wss cvol cprod cmpt csumge0 wceq wa
      cr cxp cmap wrex cxr crab cmin cof wcel c1st caddc c2nd cop coeq2d fveq1d
      co fveq1 ixpeq2dv iuneq2d sseq2d adantr fveq2d prodeq2dv mpteq2dv anbi12d
      eqeq2d fveq2 oveq1d opeq12d cbvmptv 2fveq3 oveq12d mpteq2i eqtri ad2antrr
      weq a1i cvv simpr wf vontranslem12 simprl wb vontranslem18 cbvixpv eqtrid
      mpbid cbviunv sseqtrdi simprr vontranslem13 eqtr4d cbvprodv fveq2i eqtrdi
      jca rspcedvdw rexlimdva2 ss2rabdv 3sstr4g ) ADGUCHNHUDZUEGUDZFUDZTZUFTZUG
      UHUIZCUDZGUCNXTUJTHUKULUMTZUNZUOZFUPUPUQNURVKUCURVKZUSZCUTVABUDMVBVCVKDVD
      BUPNURVKZVAZJUCINIUDZUEJUDZEUDZTZUFZTZUGZUHZUIZYBJUCNYOUJTZIUKZULZUMTZUNZ
      UOZEYFUSZCUTVAKLAYGUUECUTAYBUTVDZUOZYEUUEFYFUUGXRYFVDZUOZYEUOZUUDYIJUCINY
      JUEYKUAUCUBNUBUDZUAUDZXRTZTZVETZUUKMTZVFVKZUUNVGTZUUPVFVKZVHZULZULZTZUFZT
      ZUGZUHZUIZYBJUCNUVEUJTZIUKZULZUMTZUNZUOEUVBYFYLUVBUNZYRUVHUUCUVMUVNYQUVGY
      IUVNJUCYPUVFUVNINYOUVEUVNYJYNUVDUVNYMUVCUEYKYLUVBVLVIVJZVMVNVOUVNUUBUVLYB
      UVNUUAUVKUMUVNJUCYTUVJUVNNYSUVIIUVNYJNVDZUOYOUVEUJUVNYOUVEUNUVPUVOVPVQVRV
      SVQWAVTUUIUVBYFVDYEUUIGHXRUVBMNUVBGUCHNXPXSTZVETZXPMTZVFVKZUVQVGTZUVSVFVK
      ZVHZULZULZUNUUIUVBGUCUBNUUKXSTZVETZUUPVFVKZUWFVGTZUUPVFVKZVHZULZULUWEUAGU
      CUVAUWLUAGWKZUBNUUTUWKUWMUUQUWHUUSUWJUWMUUOUWGUUPVFUWMUUNUWFVEUWMUUKUUMXS
      UULXQXRWBVJZVQWCUWMUURUWIUUPVFUWMUUNUWFVGUWNVQWCWDVSWEGUCUWLUWDUBHNUWKUWC
      UBHWKZUWHUVTUWJUWBUWOUWGUVRUUPUVSVFUUKXPVEXSWFUUKXPMWBZWGUWOUWIUWAUUPUVSV
      FUUKXPVGXSWFUWPWGWDWEWHWIWLZANWMVDUUFUUHOWJZUUGUUHWNZANUPMWOUUFUUHPWJZWPV
      PUUJUVHUVMUUJYIGUCHNXPUEXQUVBTZUFZTZUGZUHZUVGUUJYAYIUXEUIZUUIYAYDWQUUIYAU
      XFWRYEUUIBDGHXRUVBMNUWQUWRUWSUWTADYHUIUUFUUHQWJWSVPXBGJUCUXDUVFGJWKZUXDIN
      YJUXBTZUGUVFHINUXCUXHXPYJUXBWBWTUXGINUXHUVEUXGYJUXBUVDUXGUXAUVCUEXQYKUVBW
      BVIVJZVMXAXCXDUUJYBGUCNUXCUJTZHUKZULZUMTZUVLUUJYBYCUXMUUIYAYDXEUUIUXMYCUN
      YEUUIGHXRUVBMNUWQUWRUWSUWTXFVPXGUXLUVKUMGJUCUXKUVJUXGUXKNUXHUJTZIUKUVJNUX
      JUXNHIXPYJUJUXBWFXHUXGNUXNUVIIUXGUVPUOUXHUVEUJUXGUXHUVEUNUVPUXIVPVQVRXAWE
      XIXJXKXLXMXNRSXO $.
  $}

  ${
    $d A k $.  $d V k $.  $d W k $.  $d X k $.  $d k ph $.
    ofsubneg.x $e |- ( ph -> X e. _V ) $.
    ofsubneg.a $e |- ( ph -> A : X --> RR ) $.
    ofsubneg.v $e |- ( ph -> V : X --> RR ) $.
    ofsubneg.w $e |- ( ph -> W = ( k e. X |-> -u ( V ` k ) ) ) $.
    $( Translating by the pointwise negation of ` V ` is the same as
       translating by ` V ` in the other direction.  (Contributed by Xander
       Mackay and Claude, 16-Sep-2026.) $)
    ofsubneg $p |- ( ph -> ( A oF - W ) = ( A oF + V ) ) $=
      ( cmin cof co caddc cvv cr ffnd cfv wfn adantr cv cneg wcel wa ffvelcdmda
      renegcld fmpt3d inidm offn wceq simpr fnfvof fvmpt2d oveq2d recnd subnegd
      syl22anc 3eqtrd eqtr4d eqfnfvd ) ACFBEKLMZBDNLMZAFFKFBEOOAFPBHQZAFPEACFCU
      AZDRZUBZPEJAVDFUCZUDZVEAFPVDDIUEZUFZUGQZGGFUHZUIAFFNFBDOOVCAFPDIQZGGVLUIV
      HVDVARZVDBRZVENMZVDVBRZVHVNVOVDERZKMZVOVFKMVPVHBFSZEFSZFOUCZVGVNVSUJAVTVG
      VCTZAWAVGVKTAWBVGGTZAVGUKZFKBEOVDULUQVHVRVFVOKACFVFEPJVJUMUNVHVOVEVHVOAFP
      VDBHUEUOVHVEVIUOUPURVHVTDFSZWBVGVQVPUJWCAWFVGVMTWDWEFNBDOVDULUQUSUT $.
  $}

  ${
    $d S t u y $.  $d V b t $.  $d V k t $.  $d V t u y $.  $d W k t $.
    $d W t u y $.  $d X a b t $.  $d X k t $.  $d X t u y $.  $d a b ph t $.
    $d k ph t $.
    vontranslem21.x $e |- ( ph -> X e. _V ) $.
    vontranslem21.v $e |- ( ph -> V : X --> RR ) $.
    vontranslem21.s $e |- ( ph -> S C_ ( RR ^m X ) ) $.
    vontranslem21.w $e |- ( ph -> W = ( k e. X |-> -u ( V ` k ) ) ) $.
    $( Lemma for ~ vontrans : translating a set and then translating it back
       gives the original set.  (Contributed by Xander Mackay and Claude,
       16-Sep-2026.) $)
    vontranslem21 $p |- ( ph -> { u e. ( RR ^m X ) | ( u oF - W ) e. { y e. (
      RR ^m X ) | ( y oF - V ) e. S } } = S )
                      $=
      ( cv co wcel cr wa caddc cvv adantr vt va vb cmin cof cmap crab wf elmapi
      adantl cfv cneg cmpt wceq ofsubneg a1i readdcl inidm elmapdd eqeltrd
      off oveq1 eleq1d elrab mpbirand oveq1d ofaddsubidd eqtrd bitrd pm5.32da
      reex wb sseld pm4.71rd 3bitr4d eqrdv ) AUACMZGUDUEZNZBMZFVRNZDOZBPHUFNZUG
      ZOZCWCUGZDAUAMZWCOZWGGVRNZWDOZQZWHWGDOZQWGWFOZWLAWHWJWLAWHQZWJWIFVRNZDOZW
      LWNWJWIWCOZWPWNWIWGFRUENZWCWNWGEFGHAHSOWHITZWHHPWGUHAWGPHUIUJZAHPFUHWHJTZ
      AGEHEMFUKULUMUNWHLTUOZWNPHWRSSPSOWNVKUPWSWNUBUCHHHRPPPWGFSSUBMZPOUCMZPOQX
      CXDRNPOWNXCXDUQUJWTXAWSWSHURVAUSUTWJWQWPQVLWNWBWPBWIWCVTWIUNWAWODVTWIFVRV
      BVCVDUPVEWNWOWGDWNWOWRFVRNWGWNWIWRFVRXBVFWNWGFHWSWTXAVGVHVCVIVJWMWKVLAWEW
      JCWGWCVQWGUNVSWIWDVQWGGVRVBVCVDUPAWLWHADWCWGKVMVNVOVP $.
  $}

  ${
    $d S f i u y $.  $d S f m n u y $.  $d V f i k $.  $d V f k m n $.
    $d V f i u y $.  $d W f i j k $.  $d W f j k m n $.  $d W f i u y $.
    $d X f i j k $.  $d X f j k m n $.  $d X f i u y $.  $d f i k ph $.
    $d f i ph u z $.  $d m n ph u z $.
    vontranslem22.x $e |- ( ph -> X e. _V ) $.
    vontranslem22.v $e |- ( ph -> V : X --> RR ) $.
    vontranslem22.s $e |- ( ph -> S C_ ( RR ^m X ) ) $.
    vontranslem22.w $e |- ( ph -> W = ( k e. X |-> -u ( V ` k ) ) ) $.
    vontranslem22.m $e |- M = { z e. RR* | E. i e. ( ( ( RR X. RR ) ^m X ) ^m
      NN ) ( S C_ U_ j e. NN X_ k e. X ( ( [,) o. ( i ` j ) ) ` k ) /\ z = (
      sum^ ` ( j e. NN |-> prod_ k e. X ( vol ` ( ( [,) o. ( i ` j ) ) ` k ) )
      ) ) ) }
                        $.
    vontranslem22.n $e |- N = { z e. RR* | E. f e. ( ( ( RR X. RR ) ^m X ) ^m
      NN ) ( { y e. ( RR ^m X ) | ( y oF - V ) e. S } C_ U_ n e. NN X_ m e. X (
      ( [,) o. ( f ` n ) ) ` m ) /\ z = ( sum^ ` ( n e. NN |-> prod_ m e. X (
      vol ` ( ( [,) o. ( f ` n ) ) ` m ) ) ) ) ) }
                        $.
    $( Lemma for ~ vontrans : every candidate outer measure sum for the
       translate of a set is one for the set.  (Contributed by Xander Mackay
       and Claude, 16-Sep-2026.) $)
    vontranslem22 $p |- ( ph -> N C_ M ) $=
      ( vu cv cmin cof co wcel cr cmap crab cn cico cfv ccom cixp ciun wss cvol
      cprod cmpt csumge0 wceq wa cxp wrex cxr ffvelcdmda renegcld fmpt3d ssrab2
      cneg a1i eqid vontranslem19 vontranslem21 rexbidv rabbidv eqtr4di sseqtrd
      sseq1d anbi1d ) ALUBUCNUDUEZUFBUCMWBUFDUGZBUHOUIUFZUJZUGUBWDUJZGUKHOHUCZU
      LGUCFUCUMUNUMZUOUPZUQZCUCGUKOWHURUMHUSUTVAUMVBZVCZFUHUHVDOUIUFUKUIUFZVEZC
      VFUJZKAUBCWEFEJIHGLWONOPAHOWGMUMZVKUHNSAWGOUGVCWPAOUHWGMQVGVHVIWEWDUQAWCB
      WDVJVLUAWOVMVNAWODWIUQZWKVCZFWMVEZCVFUJKAWNWSCVFAWLWRFWMAWJWQWKAWFDWIABUB
      DHMNOPQRSVOVTWAVPVQTVRVS $.
  $}

  ${
    $d S f i j k m n y $.  $d V f i j k m n y $.  $d W f i j k m n y $.
    $d X f i j k m n y $.  $d f i j k m n ph y z $.
    vontranslem23.x $e |- ( ph -> X e. _V ) $.
    vontranslem23.v $e |- ( ph -> V : X --> RR ) $.
    vontranslem23.s $e |- ( ph -> S C_ ( RR ^m X ) ) $.
    vontranslem23.w $e |- ( ph -> W = ( k e. X |-> -u ( V ` k ) ) ) $.
    vontranslem23.m $e |- M = { z e. RR* | E. i e. ( ( ( RR X. RR ) ^m X ) ^m
      NN ) ( S C_ U_ j e. NN X_ k e. X ( ( [,) o. ( i ` j ) ) ` k ) /\ z = (
      sum^ ` ( j e. NN |-> prod_ k e. X ( vol ` ( ( [,) o. ( i ` j ) ) ` k ) )
      ) ) ) }
                        $.
    vontranslem23.n $e |- N = { z e. RR* | E. f e. ( ( ( RR X. RR ) ^m X ) ^m
      NN ) ( { y e. ( RR ^m X ) | ( y oF - V ) e. S } C_ U_ n e. NN X_ m e. X (
      ( [,) o. ( f ` n ) ) ` m ) /\ z = ( sum^ ` ( n e. NN |-> prod_ m e. X (
      vol ` ( ( [,) o. ( f ` n ) ) ` m ) ) ) ) ) }
                        $.
    $( Lemma for ~ vontrans : a set and its translate have the same candidate
       outer measure sums.  (Contributed by Xander Mackay and Claude,
       16-Sep-2026.) $)
    vontranslem23 $p |- ( ph -> M = N ) $=
      ( vontranslem19 vontranslem22 eqssd ) AKLABCDEFGHIJKLMOPQRTUAUBABCDEFGHIJ
      KLMNOPQRSTUAUCUD $.
  $}

  $( The preimage of an intersection under a coordinatewise translation is the
     intersection of the preimages.  (Contributed by Xander Mackay and Claude,
     16-Sep-2026.) $)
  ofsubpreimin $p |- { y e. ( RR ^m X ) | ( y oF - V ) e. ( A i^i B ) } = ( {
    y e. ( RR ^m X ) | ( y oF - V ) e. A } i^i { y e. ( RR ^m X ) | ( y oF - V
    ) e. B } )
                    $=
    ( cv cmin cof co cin wcel cr cmap crab wa elin rabbii inrab eqtr4i ) AFDGHI
    ZBCJKZALEMIZNTBKZTCKZOZAUBNUCAUBNUDAUBNJUAUEAUBTBCPQUCUDAUBRS $.

  $( The preimage of a class difference under a coordinatewise translation is
     the difference of the preimages.  (Contributed by Xander Mackay and
     Claude, 16-Sep-2026.) $)
  ofsubpreimdif $p |- { y e. ( RR ^m X ) | ( y oF - V ) e. ( A \ B ) } = ( { y
    e. ( RR ^m X ) | ( y oF - V ) e. A } \ { y e. ( RR ^m X ) | ( y oF - V ) e.
    B } )
                    $=
    ( cv cmin cof co cdif wcel cr cmap crab wn wa eldif rabbii difrab eqtr4i )
    AFDGHIZBCJKZALEMIZNUABKZUACKZOPZAUCNUDAUCNUEAUCNJUBUFAUCUABCQRUDUEAUCST $.

  ${
    $d V k $.  $d X k $.  $d k ph $.
    vontranslem26.v $e |- ( ph -> V : X --> RR ) $.
    vontranslem26.w $e |- ( ph -> W = ( k e. X |-> -u ( V ` k ) ) ) $.
    $( Lemma for ~ vontrans : the pointwise negation of the pointwise negation
       of a vector is the vector.  (Contributed by Xander Mackay and Claude,
       16-Sep-2026.) $)
    vontranslem26 $p |- ( ph -> V = ( k e. X |-> -u ( W ` k ) ) ) $=
      ( cv cfv cmpt cneg cr feqmptd wa ffvelcdmda renegcld fvmpt2d negeqd recnd
      wcel negnegd eqtr2d mpteq2dva eqtrd ) ACBEBHZCIZJBEUEDIZKZJABELCFMABEUFUH
      AUEETNZUHUFKZKUFUIUGUJABEUJDLGUIUFAELUECFOZPQRUIUFUIUFUKSUAUBUCUD $.
  $}

  ${
    $d S u y $.  $d V k $.  $d V u y $.  $d W k $.  $d W u y $.  $d X k $.
    $d X u y $.  $d k ph $.
    vontranslem27.x $e |- ( ph -> X e. _V ) $.
    vontranslem27.v $e |- ( ph -> V : X --> RR ) $.
    vontranslem27.s $e |- ( ph -> S C_ ( RR ^m X ) ) $.
    vontranslem27.w $e |- ( ph -> W = ( k e. X |-> -u ( V ` k ) ) ) $.
    $( Lemma for ~ vontrans : translating a set back and then translating it
       gives the original set.  (Contributed by Xander Mackay and Claude,
       16-Sep-2026.) $)
    vontranslem27 $p |- ( ph -> { u e. ( RR ^m X ) | ( u oF - V ) e. { y e. (
      RR ^m X ) | ( y oF - W ) e. S } } = S )
                      $=
      ( cv cfv cneg cr wcel wa ffvelcdmda renegcld vontranslem26 vontranslem21
      fmpt3d ) ABCDEGFHIAEHEMZFNZOPGLAUDHQRUEAHPUDFJSTUCKAEFGHJLUAUB $.
  $}

  ${
    $d S f i j k m n y z $.  $d V c f i j k m n y $.  $d V f i j k m n y z $.
    $d X c f i j k m n y $.  $d X f i j k m n y z $.  $d f i j k m n ph y z $.
    ovntrans.x $e |- ( ph -> X e. Fin ) $.
    ovntrans.v $e |- ( ph -> V : X --> RR ) $.
    ovntrans.s $e |- ( ph -> S C_ ( RR ^m X ) ) $.
    $( The Lebesgue outer measure of a subset of the space of multidimensional
       real numbers is invariant under translation.  (Contributed by Xander
       Mackay and Claude, 16-Sep-2026.) $)
    ovntrans $p |- ( ph -> ( ( voln* ` X ) ` { y e. ( RR ^m X ) | ( y oF - V )
      e. S } ) = ( ( voln* ` X ) ` S ) )
                 $=
      ( vj vk vi vz vn vm vf wceq cn cv cfv cxr vc cc0 cico ccom cixp ciun cvol
      c0 wss cprod cmpt csumge0 wa cr cxp cmap wrex crab clt cinf cif cmin wcel
      cof covoln cneg cfn elexd fveq2 negeqd cbvmptv eqid vontranslem23 infeq1d
      co a1i ifeq2d ovnval2 ssrab2 3eqtr4rd ) AEUHPZUBCIQJEJRZUCIRKRSUDSZUEUFUI
      LRZIQEWCUGSJUJUKULSPUMKUNUNUOEUPVOQUPVOZUQLTURZTUSUTZVAWAUBBRDVBVDVOCVCZB
      UNEUPVOZURZMQNENRUCMRORSUDSZUEUFUIWDMQEWKUGSNUJUKULSPUMOWEUQLTURZTUSUTZVA
      CEVESZSWJWNSAWAWGWMUBATWFWLUSABLCOKIJNMWFWLDUAEUARZDSZVFZUKZEAEVGFVHGHWRJ
      EWBDSZVFZUKPAUAJEWQWTWOWBPWPWSWOWBDVIVJVKVPWFVLZWLVLZVMVNVQALCKIJWFEFHXAV
      RALWJOMNWLEFWJWIUIAWHBWIVSVPXBVRVT $.
  $}

  ${
    $d A a t $.  $d A t y $.  $d S a $.  $d S y $.  $d V k $.  $d V t y $.
    $d W a t $.  $d W k $.  $d W t y $.  $d X a t $.  $d X k $.  $d X t y $.
    $d k ph $.  $d ph y $.
    vontranslem28.x $e |- ( ph -> X e. Fin ) $.
    vontranslem28.v $e |- ( ph -> V : X --> RR ) $.
    vontranslem28.s $e |- ( ph -> S C_ ( RR ^m X ) ) $.
    vontranslem28.w $e |- ( ph -> W = ( k e. X |-> -u ( V ` k ) ) ) $.
    vontranslem28.c $e |- ( ph -> A. a e. ~P ( RR ^m X ) ( ( ( voln* ` X ) ` (
      a i^i S ) ) +e ( ( voln* ` X ) ` ( a \ S ) ) ) = ( ( voln* ` X ) ` a ) )
                        $.
    vontranslem28.a $e |- ( ph -> A e. ~P ( RR ^m X ) ) $.
    $( Lemma for ~ vontrans : the translate of a set splits every subset of the
       space in the Caratheodory sense, when the set itself does.  (Contributed
       by Xander Mackay and Claude, 16-Sep-2026.) $)
    vontranslem28 $p |- ( ph -> ( ( ( voln* ` X ) ` ( A i^i { y e. ( RR ^m X )
      | ( y oF - V ) e. S } ) ) +e ( ( voln* ` X ) ` ( A \ { y e. ( RR ^m X ) |
      ( y oF - V ) e. S } ) ) ) = ( ( voln* ` X ) ` A ) )
                      $=
      ( vt co wcel crab cfv cv cmin cof cmap cin covoln cdif cxad ofsubpreimin
      cr cfn elpwid vontranslem27 ineq1d eqtrid fveq2d ssinss2d ovntrans eqtr3d
      elexd ofsubpreimdif difeq1d wss ssrab2 ssdifssd oveq12d wceq ineq1 difeq1
      a1i cpw fveq2 eqeq12d cvv ovex rabex elpwd rspcdva eqtrd 3eqtr2d ) ACBUAF
      UBUCZQZDRBUJHUDQZSZUEZHUFTZTZCWDUGZWFTZUHQZPUAGWAQCRZPWCSZWFTZWBWLRBWCSZW
      FTCWFTAWJWLDUEZWFTZWLDUGZWFTZUHQZWMAWGWPWIWRUHAWBWORBWCSZWFTWGWPAWTWEWFAW
      TWNWDUEWEBWLDFHUIAWNCWDAPBCEFGHAHUKJUTKACWCOULMUMZUNUOUPABWOFHJKAWLDWCLUQ
      URUSAWBWQRBWCSZWFTWIWRAXBWHWFAXBWNWDUGWHBWLDFHVAAWNCWDXAVBUOUPABWQFHJKAWL
      WCDWLWCVCAWKPWCVDVJZVEURUSVFAIUAZDUEZWFTZXDDUGZWFTZUHQZXDWFTZVGWSWMVGIWCV
      KWLXDWLVGZXIWSXJWMXKXFWPXHWRUHXKXEWOWFXDWLDVHUPXKXGWQWFXDWLDVIUPVFXDWLWFV
      LVMNAWLWCVNWLVNRAWKPWCUJHUDVOVPVJXCVQVRVSABWLFHJKXCURAWNCWFXAUPVT $.
  $}

  ${
    $d S a b $.  $d S a y $.  $d V a b $.  $d V b c $.  $d V a k $.
    $d V a y $.  $d X a b $.  $d X b c $.  $d X a k $.  $d X a y $.
    $d a k ph $.  $d c k $.  $d c y $.  $d ph y $.
    vontranslem29.x $e |- ( ph -> X e. Fin ) $.
    vontranslem29.v $e |- ( ph -> V : X --> RR ) $.
    vontranslem29.s $e |- ( ph -> S e. dom ( voln ` X ) ) $.
    $( Lemma for ~ vontrans : the translate of a Lebesgue measurable set is
       Lebesgue measurable.  (Contributed by Xander Mackay and Claude,
       16-Sep-2026.) $)
    vontranslem29 $p |- ( ph -> { y e. ( RR ^m X ) | ( y oF - V ) e. S } e. dom
      ( voln ` X ) )
                      $=
      ( va vk vc vb cv co wcel cr cfv wss wceq adantr cmin cof cmap crab covoln
      cvoln cdm cin cdif cxad cpw wral ssrab2 a1i wa cneg cfn wf isvonmbl mpbid
      cmpt simpld fveq2 negeqd cbvmptv simprd vontranslem28 ralrimiva mpbir2and
      simpr ) ABMDUAUBNCOZBPEUCNZUDZEUFQUGZOVMVLRZIMZVMUHEUEQZQVPVMUIVQQUJNVPVQ
      QSZIVLUKZULVOAVKBVLUMUNAVRIVSAVPVSOZUOZBVPCJDKEKMZDQZUPZVAZELAEUQOVTFTAEP
      DURVTGTACVLRZVTAWFLMZCUHVQQWGCUIVQQUJNWGVQQSLVSULZACVNOWFWHUOHACELFUSUTZV
      BTWEJEJMZDQZUPZVASWAKJEWDWLWBWJSWCWKWBWJDVCVDVEUNAWHVTAWFWHWIVFTAVTVJVGVH
      AVMEIFUSVI $.
  $}

  ${
    $d S y $.  $d V y $.  $d X y $.  $d ph y $.
    vontrans.x $e |- ( ph -> X e. Fin ) $.
    vontrans.v $e |- ( ph -> V : X --> RR ) $.
    vontrans.s $e |- ( ph -> S e. dom ( voln ` X ) ) $.
    $( The Lebesgue measure of a subset of the space of multidimensional real
       numbers is invariant under translation.  (Contributed by Xander Mackay
       and Claude, 16-Sep-2026.) $)
    vontrans $p |- ( ph -> ( ( voln ` X ) ` { y e. ( RR ^m X ) | ( y oF - V )
      e. S } ) = ( ( voln ` X ) ` S ) )
                 $=
      ( cv cmin cof co wcel cr cmap crab covoln cfv cvoln mblvon cdm cpw sseldd
      vonmblss elpwid ovntrans vontranslem29 3eqtr4d ) ABIDJKLCMBNEOLZPZEQRZRCU
      KRUJESRZRCULRABCDEFGACUIAULUAUIUBCAEFUDHUCUEUFAUJEFABCDEFGHUGTACEFHTUH $.
  $}

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Scaling of Lebesgue measure on n-dimensional real numbers
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    vonsmullem1.a $e |- ( ph -> A e. RR ) $.
    vonsmullem1.b $e |- ( ph -> B e. RR ) $.
    vonsmullem1.c $e |- ( ph -> C e. RR+ ) $.
    $( Lemma for ~ vonsmul : scaling a left-closed, right-open real interval by
       a positive real multiplies its measure by that real.  (Contributed by
       Xander Mackay and Claude, 16-Sep-2026.) $)
    vonsmullem1 $p |- ( ph -> ( vol ` ( ( A x. C ) [,) ( B x. C ) ) ) = ( C x.
      ( vol ` ( A [,) B ) ) ) )
                    $=
      ( cmul co clt wbr cmin cc0 cif cico cvol cfv recnd cr wcel ltmul1d bicomd
      rpred subcld mulcomd subdird eqtr2d mul01d eqcomd ifbieq12d wceq remulcld
      volico syl2anc oveq2d ovif2 eqtrdi 3eqtr4d ) ABDHIZCDHIZJKZUTUSLIZMNZBCJK
      ZDCBLIZHIZDMHIZNZUSUTOIPQZDBCOIPQZHIZAVAVDVBMVFVGAVDVAABCDEFGUAUBAVFVEDHI
      VBADVEADADGUCZRZACBACFRZABERZUDUEACBDVNVOVMUFUGAVGMADVMUHUIUJAUSSTUTSTVIV
      CUKABDEVLULACDFVLULUSUTUMUNAVKDVDVEMNZHIVHAVJVPDHABSTCSTVJVPUKEFBCUMUNUOV
      DDVEMHUPUQUR $.
  $}

  ${
    $d C k $.  $d X k $.  $d k ph $.
    vonsmullem2.x $e |- ( ph -> X e. Fin ) $.
    vonsmullem2.a $e |- ( ph -> A : X --> RR ) $.
    vonsmullem2.b $e |- ( ph -> B : X --> RR ) $.
    vonsmullem2.c $e |- ( ph -> C e. RR+ ) $.
    $( Lemma for ~ vonsmul : scaling a half-open box by a positive real
       multiplies its volume, the product of its edge lengths, by that real
       raised to the dimension.  (Contributed by Xander Mackay and Claude,
       16-Sep-2026.) $)
    vonsmullem2 $p |- ( ph -> prod_ k e. X ( vol ` ( ( ( A ` k ) x. C ) [,) ( (
      B ` k ) x. C ) ) ) = ( ( C ^ ( # ` X ) ) x. prod_ k e. X ( vol ` ( ( A `
      k ) [,) ( B ` k ) ) ) ) )
                    $=
      ( cfv cmul co cico cvol cprod wcel cr ffvelcdmda rpcnd cv chash wa adantr
      cexp crp vonsmullem1 prodeq2dv volicorecl syl2anc recnd fprodmul cfn wceq
      cc fprodconst oveq1d 3eqtrd ) AFEUAZBKZDLMUSCKZDLMNMOKZEPFDUTVANMOKZLMZEP
      FDEPZFVCEPZLMDFUBKUEMZVFLMAFVBVDEAUSFQZUCZUTVADAFRUSBHSZAFRUSCISZADUFQVHJ
      UDZUGUHAFDVCEGVIDVLTVIVCVIUTRQVARQVCRQVJVKUTVAUIUJUKULAVEVGVFLAFUMQDUOQVE
      VGUNGADJTFDEUPUJUQUR $.
  $}

  ${
    elicodiv.a $e |- ( ph -> A e. RR ) $.
    elicodiv.b $e |- ( ph -> B e. RR ) $.
    elicodiv.c $e |- ( ph -> C e. RR+ ) $.
    elicodiv.y $e |- ( ph -> Y e. RR ) $.
    $( Membership in a left-closed, right-open real interval is unchanged by
       scaling the point and the interval together.  (Contributed by Xander
       Mackay and Claude, 16-Sep-2026.) $)
    elicodiv $p |- ( ph -> ( ( Y / C ) e. ( A [,) B ) <-> Y e. ( ( A x. C )
      [,) ( B x. C ) ) ) )
                    $=
      ( co cr wcel cle wbr clt w3a cmul cico cxr wb cdiv rerpdivcld 2thd bicomd
      lemuldivd ltdivmul2d 3anbi123d rexrd elico2 syl2anc remulcld 3bitr4d
      rpred ) AEDUAJZKLZBUNMNZUNCONZPZEKLZBDQJZEMNZECDQJZONZPZUNBCRJLZEUTVBRJLZ
      AUOUSUPVAUQVCAUOUSAEDIHUBIUCAVAUPABEDFIHUEUDAECDIGHUFUGABKLCSLVEURTFACGUH
      BCUNUIUJAUTKLVBSLVFVDTABDFADHUMZUKAVBACDGVGUKUHUTVBEUIUJUL $.
  $}

  ${
    $d V k $.  $d X k $.  $d Y k $.  $d k ph $.
    elixpdiv.x $e |- ( ph -> X e. _V ) $.
    elixpdiv.a $e |- ( ph -> A : X --> RR ) $.
    elixpdiv.b $e |- ( ph -> B : X --> RR ) $.
    elixpdiv.v $e |- ( ph -> V : X --> RR+ ) $.
    elixpdiv.y $e |- ( ph -> Y : X --> RR ) $.
    $( Membership in an infinite Cartesian product of left-closed, right-open
       real intervals is unchanged by scaling the point and every factor
       together.  (Contributed by Xander Mackay and Claude, 16-Sep-2026.) $)
    elixpdiv $p |- ( ph -> ( ( Y oF / V ) e. X_ k e. X ( ( A ` k ) [,) ( B `
      k ) ) <-> Y e. X_ k e. X ( ( ( A ` k ) x. ( V ` k ) ) [,) ( ( B ` k ) x.
      ( V ` k ) ) ) ) )
                    $=
      ( cdiv co cfv wcel wa cvv cr ffvelcdmda cof cico wral cmul cixp wceq ffnd
      cv wfn adantr crp simpr fnfvof syl22anc eleq1d elicodiv bitrd ralbidva wb
      w3a df-3an a1i elixp2 ovexd inidm offn jca biantrurd 3bitr4d fexd ) ADUHZ
      GEMUAZNZOZVKBOZVKCOZUBNZPZDFUCZVKGOZVOVKEOZUDNVPWAUDNUBNZPZDFUCZVMDFVQUEP
      ZGDFWBUEPZAVRWCDFAVKFPZQZVRVTWAMNZVQPWCWHVNWIVQWHGFUIZEFUIZFRPZWGVNWIUFAW
      JWGAFSGLUGZUJAWKWGAFUKEKUGZUJAWLWGHUJAWGULFMGERVKUMUNUOWHVOVPWAVTAFSVKBIT
      AFSVKCJTAFUKVKEKTAFSVKGLTUPUQURAVMRPZVMFUIZVSUTZWOWPQZVSQZWEVSWQWSUSAWOWP
      VSVAVBWEWQUSADFVQVMVCVBAWRVSAWOWPAGEVLVDAFFMFGERRWMWNHHFVEVFVGVHVIAGRPZWJ
      WDUTZWTWJQZWDQZWFWDXAXCUSAWTWJWDVAVBWFXAUSADFWBGVCVBAXBWDAWTWJAFSRGLHVJWM
      VGVHVIVI $.
  $}

  ${
    $d D y $.  $d K y $.  $d ph y $.
    vonsmullem5.k $e |- ( ph -> K e. RR+ ) $.
    vonsmullem5.s $e |- ( ( ph /\ y e. D ) -> S e. RR ) $.
    $( Lemma for ~ vonsmul : one half of extended-real supremum scaling: the
       supremum of a scaled family of reals is at most the scale of the
       supremum.  (Contributed by Xander Mackay and Claude, 16-Sep-2026.) $)
    vonsmullem5 $p |- ( ph -> sup ( ran ( y e. D |-> ( K x. S ) ) , RR* , < )
      <_ ( K *e sup ( ran ( y e. D |-> S ) , RR* , < ) ) )
                    $=
      ( co cmpt crn cxr clt csup cxmu cle wbr wcel cr adantr nfcv cmul wral crp
      cv wa wceq rpred rexmul syl2anc wss nfv eqid rexrd rnmptssd simpr supxrub
      elrnmpt1d supxrcl syl xlemul2 syl3anc mpbid breq1dd ralrimiva nfmpt1 nfrn
      wb nfsup nfov remulcld rpxrd xmulcld supxrleubrnmptf mpbird ) ABCEDUAHZIJ
      KLMEBCDIZJZKLMZNHZOPVOVSOPZBCUBAVTBCABUDCQZUEZEDNHZVOVSOWBERQDRQWCVOUFWBE
      AEUCQZWAFSZUGZGEDUHUIWBDVROPZWCVSOPZWBVQKUJZDVQQWGAWIWAABCDKVPABUKZVPULZW
      BDGUMZUNZSWBBCDVPRWKAWAUOGUQVQDUPUIWBDKQVRKQZWDWGWHVGWLAWNWAAWIWNWMVQURUS
      ZSWEDVREUTVAVBVCVDABCVOVSWJBCTBEVRNBETBNTBVQKLBVPBCDVEVFBKTBLTVHVIWBVOWBE
      DWFGVJUMAEVRAEFVKWOVLVMVN $.
  $}

  ${
    xmulrecd.k $e |- ( ph -> K e. RR+ ) $.
    xmulrecd.w $e |- ( ph -> W e. RR* ) $.
    $( Extended-real multiplication by a positive real and then by its
       reciprocal recovers the original extended real, in deduction form.
       (Contributed by Xander Mackay and Claude, 16-Sep-2026.) $)
    xmulrecd $p |- ( ph -> ( K *e ( ( 1 / K ) *e W ) ) = W ) $=
      ( c1 cdiv co cxmu cmul cr wcel wceq rpred rpreccld rexmul rpcnd cxr rpxrd
      syl2anc rpne0d recidd eqtrd oveq1d xmulass syl3anc xmullid syl 3eqtr3d )
      ABFBGHZIHZCIHZFCIHZBUJCIHIHZCAUKFCIAUKBUJJHZFABKLUJKLUKUOMABDNAUJABDOZNBU
      JPTABABDQABDUAUBUCUDABRLUJRLCRLZULUNMABDSAUJUPSEBUJCUEUFAUQUMCMECUGUHUI
      $.
  $}

  ${
    $d D y $.  $d K y $.  $d ph y $.
    vonsmullem7.k $e |- ( ph -> K e. RR+ ) $.
    vonsmullem7.s $e |- ( ( ph /\ y e. D ) -> S e. RR ) $.
    $( Lemma for ~ vonsmul : scaling a family of reals by a positive real
       scales its extended-real supremum.  Proved by applying ~ vonsmullem5
       twice, the second time with the reciprocal scale.  (Contributed by
       Xander Mackay and Claude, 16-Sep-2026.) $)
    vonsmullem7 $p |- ( ph -> sup ( ran ( y e. D |-> ( K x. S ) ) , RR* , < ) =
      ( K *e sup ( ran ( y e. D |-> S ) , RR* , < ) ) )
                    $=
      ( cmul co cmpt crn cxr clt csup cxmu wss wcel eqid c1 cle nfv cv wa rpred
      crp adantr remulcld rexrd rnmptssd supxrcl rpxrd xmulcld vonsmullem5 cdiv
      syl rpcnd rpne0d recid2d rpreccld recnd mulassd mullidd 3eqtr3d mpteq2dva
      oveq1d rneqd supeq1d breq1dd wb xlemul2 syl3anc mpbid xmulrecd breqtrd
      wbr xrletrid ) ABCEDHIZJZKZLMNZEBCDJZKZLMNZOIZAVSLPVTLQABCVQLVRABUAZVRRAB
      UBCQZUCZVQWGEDWGEAEUEQZWFFUFZUDGUGZUHUIVSUJUOZAEWCAEFUKAWBLPWCLQZABCDLWAW
      EWARWGDGUHUIWBUJUOZULABCDEFGUMAWDESEUNIZVTOIZOIZVTTAWCWOTVOZWDWPTVOZABCWN
      VQHIZJZKZLMNWCWOTALXAWBMAWTWAABCWSDWGWNEHIZDHISDHIWSDWGXBSDHWGEWGEWIUPZWG
      EWIUQURVEWGWNEDWGWNWGEWIUSUPXCWGDGUTZVAWGDXDVBVCVDVFVGABCVQWNAEFUSZWJUMVH
      AWLWOLQWHWQWRVIWMAWNVTAWNXEUKWKULFWCWOEVJVKVLAEVTFWKVMVNVP $.
  $}

  ${
    $d A x y $.  $d B y $.  $d K x y $.  $d ph x y $.
    vonsmullem8.a $e |- ( ph -> A e. V ) $.
    vonsmullem8.b $e |- ( ( ph /\ x e. A ) -> B e. ( 0 [,) +oo ) ) $.
    vonsmullem8.k $e |- ( ph -> K e. RR+ ) $.
    $( Lemma for ~ vonsmul : scaling a nonnegative extended-real function by a
       positive real scales its ~ df-sumge0 sum.  This is the multiplicative
       counterpart of ~ sge0xadd , which set.mm does not have.  (Contributed by
       Xander Mackay and Claude, 16-Sep-2026.) $)
    vonsmullem8 $p |- ( ph -> ( sum^ ` ( x e. A |-> ( K x. B ) ) ) = ( K *e (
      sum^ ` ( x e. A |-> B ) ) ) )
                    $=
      ( vy co cmpt cfn crn cxr clt csup cxmu wcel wa csumge0 cfv cpw cin cv csu
      cmul nfv cr cc0 cle wbr cpnf cico crp adantr rpred elrege0 sylib remulcld
      simpld rpge0d simprd sge0revalmpt simpr elin2d rpcnd simpll elin1d elpwid
      mulge0d sylanbrc sselda syl2anc recnd fsummulc2 eqcomd mpteq2dva fsumrecl
      rneqd supeq1d vonsmullem7 eqtrd oveq2d 3eqtrd ) ABCEDUGKZLUAUBJCUCZMUDZJU
      EZWFBUFZLZNZOPQZEJWHWIDBUFZLNOPQZRKZEBCDLUAUBZRKABJCWFFABUHZGABUEZCSZTZWF
      UISUJWFUKULWFUJUMUNKZSXAEDXAEAEUOSZWTIUPZUQZXADUISZUJDUKULZXADXBSXFXGTHDU
      RUSZVAZUTXAEDXEXIXAEXDVBXAXFXGXHVCVKWFURVLVDAWMJWHEWNUGKZLZNZOPQWPAOWLXLP
      AWKXKAJWHWJXJAWIWHSZTZXJWJXNWIDEBXNWGMWIAXMVEZVFZXNEAXCXMIUPVGXNWSWISZTZD
      XRAWTXFAXMXQVHXNWICWSXNWICXNWGMWIXOVIVJVMXIVNZVOVPVQVRVTWAAJWHWNEIXNWIDBX
      PXSVSWBWCAWOWQERAWQWOABJCDFWRGHVDVQWDWE $.
  $}

  ${
    $d D y $.  $d K y $.  $d W y $.  $d ph y $.
    vonsmullem9.k $e |- ( ph -> K e. RR+ ) $.
    vonsmullem9.w $e |- ( ph -> W e. RR* ) $.
    vonsmullem9.s $e |- ( ( ph /\ y e. D ) -> S e. RR* ) $.
    vonsmullem9.l $e |- ( ( ph /\ y e. D ) -> W <_ S ) $.
    $( Lemma for ~ vonsmul : scaling a lower bound of an indexed family of
       extended reals by a positive real gives a lower bound of the scaled
       family's infimum.  (Contributed by Xander Mackay and Claude,
       16-Sep-2026.) $)
    vonsmullem9 $p |- ( ph -> ( K *e W ) <_ inf ( ran ( y e. D |-> ( K *e S ) )
      , RR* , < ) )
                    $=
      ( cxmu co cmpt crn cxr cle wbr wcel adantr xmulcld clt cinf wral cv wa wb
      crp xlemul2 syl3anc mpbid ralrimiva nfv rpxrd infxrgelbrnmpt mpbird ) AEF
      KLZBCEDKLZMNOUAUBPQUPUQPQZBCUCAURBCABUDCRZUEZFDPQZURJUTFORZDOREUGRZVAURUF
      AVBUSHSIAVCUSGSFDEUHUIUJUKABCUQUPABULUTEDAEORUSAEGUMZSITAEFVDHTUNUO $.
  $}

  ${
    $d D y $.  $d K y $.  $d ph y $.
    vonsmullem10.k $e |- ( ph -> K e. RR+ ) $.
    vonsmullem10.s $e |- ( ( ph /\ y e. D ) -> S e. RR* ) $.
    $( Lemma for ~ vonsmul : one half of extended-real supremum scaling: the
       supremum of a scaled indexed family of extended reals is at most the
       scale of the supremum.  (Contributed by Xander Mackay and Claude,
       16-Sep-2026.) $)
    vonsmullem10 $p |- ( ph -> sup ( ran ( y e. D |-> ( K *e S ) ) , RR* , < )
      <_ ( K *e sup ( ran ( y e. D |-> S ) , RR* , < ) ) )
                     $=
      ( cxmu co cmpt crn cxr clt csup cle wbr wcel adantr nfcv xmulcld wral wss
      cv nfv eqid rnmptssd simpr elrnmpt1d supxrub syl2an2r crp supxrcl xlemul2
      wa wb syl syl3anc mpbid ralrimiva nfmpt1 nfrn nfsup rpxrd supxrleubrnmptf
      nfov mpbird ) ABCEDHIZJKLMNEBCDJZKZLMNZHIZOPVGVKOPZBCUAAVLBCABUCCQZUNZDVJ
      OPZVLAVILUBZVMDVIQVOABCDLVHABUDZVHUEZGUFZVNBCDVHLVRAVMUGGUHVIDUIUJVNDLQVJ
      LQZEUKQZVOVLUOGAVTVMAVPVTVSVIULUPZRAWAVMFRDVJEUMUQURUSABCVGVKVQBCSBEVJHBE
      SBHSBVILMBVHBCDUTVABLSBMSVBVEVNEDAELQVMAEFVCZRGTAEVJWCWBTVDVF $.
  $}

  ${
    $d D y $.  $d K y $.  $d ph y $.
    vonsmullem11.k $e |- ( ph -> K e. RR+ ) $.
    vonsmullem11.s $e |- ( ( ph /\ y e. D ) -> S e. RR* ) $.
    $( Lemma for ~ vonsmul : scaling an indexed family of extended reals by a
       positive real scales its supremum.  Proved by applying ~ vonsmullem10
       twice, the second time with the reciprocal scale.  (Contributed by
       Xander Mackay and Claude, 16-Sep-2026.) $)
    vonsmullem11 $p |- ( ph -> sup ( ran ( y e. D |-> ( K *e S ) ) , RR* , < )
      = ( K *e sup ( ran ( y e. D |-> S ) , RR* , < ) ) )
                     $=
      ( cxmu co cmpt crn cxr clt csup wss wcel eqid rpxrd xmulcld cle nfv cv wa
      crp adantr rnmptssd supxrcl syl vonsmullem10 cdiv wbr wceq rpne0d recrecd
      rpcnd oveq1d oveq2d rpreccld xmulrecd eqtr3d mpteq2dva supeq1d breq1dd
      c1 rneqd wb xlemul2 syl3anc mpbid breqtrd xrletrid ) ABCEDHIZJZKZLMNZEBCD
      JZKZLMNZHIZAVNLOVOLPABCVLLVMABUAZVMQABUBCPZUCZEDWBEAEUDPZWAFUEZRGSZUFVNUG
      UHZAEVRAEFRAVQLOVRLPZABCDLVPVTVPQGUFVQUGUHZSABCDEFGUIAVSEVDEUJIZVOHIZHIZV
      OTAVRWJTUKZVSWKTUKZABCWIVLHIZJZKZLMNVRWJTALWPVQMAWOVPABCWNDWBWIVDWIUJIZDH
      IZHIWNDWBWRVLWIHWBWQEDHAWQEULWAAEAEFUOAEFUMUNUEUPUQWBWIDWBEWDURGUSUTVAVEV
      BABCVLWIAEFURZWEUIVCAWGWJLPWCWLWMVFWHAWIVOAWIWSRWFSFVRWJEVGVHVIAEVOFWFUSV
      JVK $.
  $}

  ${
    $d D y $.  $d K y $.  $d ph y $.
    vonsmullem12.k $e |- ( ph -> K e. RR+ ) $.
    vonsmullem12.s $e |- ( ( ph /\ y e. D ) -> S e. RR* ) $.
    $( Lemma for ~ vonsmul : scaling an indexed family of extended reals by a
       positive real scales its infimum.  Proved from ~ vonsmullem11 through
       ~ supminfxrrnmpt , which turns the infimum into the negation of the
       supremum of the negated family.  (Contributed by Xander Mackay and
       Claude, 16-Sep-2026.) $)
    vonsmullem12 $p |- ( ph -> inf ( ran ( y e. D |-> ( K *e S ) ) , RR* , < )
      = ( K *e inf ( ran ( y e. D |-> S ) , RR* , < ) ) )
                     $=
      ( cxmu co cmpt crn cxr clt cinf cxne wceq csup wcel mpteq2dva eqtrd cv wa
      xnegcld vonsmullem11 nfv supminfxrrnmpt xnegneg syl rneqd infeq1d xnegeqd
      oveq2d crp adantr xmulneg2 syl2anc supeq1d xmulcld eqid rnmptssd infxrcld
      rpxrd 3eqtr3d wb xneg11 mpbid ) ABCEDHIZJZKZLMNZOZEBCDJZKZLMNZHIZOZPZVJVO
      PZABCEDOZHIZJZKZLMQZEVNOZHIZVKVPAWCEBCVSJKLMQZHIWEABCVSEFABUACRZUBZDGUCZU
      DAWFWDEHAWFBCVSOZJZKZLMNZOWDABCVSABUEZWIUFAWMVNALWLVMMAWKVLABCWJDWHDLRZWJ
      DPGDUGUHSUIUJUKTULTAWCBCVGOZJZKZLMQZVKALWBWRMAWAWQABCVTWPWHELRZWOVTWPPWHE
      AEUMRWGFUNVBZGEDUOUPSUIUQAWSBCWPOZJZKZLMNZOVKABCWPWNWHVGWHEDXAGURZUCUFAXE
      VJALXDVIMAXCVHABCXBVGWHVGLRXBVGPXFVGUGUHSUIUJUKTTAWTVNLRWEVPPAEFVBZAVMABC
      DLVLWNVLUSGUTVAZEVNUOUPVCAVJLRVOLRVQVRVDAVIABCVGLVHWNVHUSXFUTVAAEVNXGXHUR
      VJVOVEUPVF $.
  $}

  ${
    $d X k $.  $d k ph $.
    vonsmullem13.t $e |- ( ph -> T = ( k e. X |-> <. ( ( 1st ` ( I ` k ) ) x. (
      V ` k ) ) , ( ( 2nd ` ( I ` k ) ) x. ( V ` k ) ) >. ) )
                       $.
    vonsmullem13.i $e |- ( ph -> I : X --> ( RR X. RR ) ) $.
    vonsmullem13.v $e |- ( ph -> V : X --> RR+ ) $.
    $( Lemma for ~ vonsmul : the scaling of a finite family of half-open
       interval endpoints is such a family.  (Contributed by Xander Mackay and
       Claude, 16-Sep-2026.) $)
    vonsmullem13 $p |- ( ph -> T : X --> ( RR X. RR ) ) $=
      ( cv cfv c1st cmul co c2nd cr wcel ffvelcdmda syl remulcld cop cxp wa crp
      xp1st rpred xp2nd opelxpd fmpt3d ) ACFCJZDKZLKZUJEKZMNZUKOKZUMMNZUAPPUBZB
      GAUJFQUCZUNUPPPURULUMURUKUQQZULPQAFUQUJDHRZUKPPUESURUMAFUDUJEIRUFZTURUOUM
      URUSUOPQUTUKPPUGSVATUHUI $.
  $}

  ${
    $d X k $.  $d k ph $.
    vonsmullem14.t $e |- ( ph -> T = ( k e. X |-> <. ( ( 1st ` ( I ` k ) ) x. (
      V ` k ) ) , ( ( 2nd ` ( I ` k ) ) x. ( V ` k ) ) >. ) )
                       $.
    vonsmullem14.i $e |- ( ph -> I : X --> ( RR X. RR ) ) $.
    vonsmullem14.v $e |- ( ph -> V : X --> RR+ ) $.
    $( Lemma for ~ vonsmul : the projection of the scaled family onto one
       dimension is the scaled half-open interval.  (Contributed by Xander
       Mackay and Claude, 16-Sep-2026.) $)
    vonsmullem14 $p |- ( ( ph /\ k e. X ) -> ( ( [,) o. T ) ` k ) = ( ( ( 1st `
      ( I ` k ) ) x. ( V ` k ) ) [,) ( ( 2nd ` ( I ` k ) ) x. ( V ` k ) ) ) )
                     $=
      ( wcel cico cfv c1st c2nd co cmul cr wceq ffvelcdmda syl cxp vonsmullem13
      cv wa ccom adantr simpr fvovco cop xp1st crp rpred remulcld xp2nd opelxpd
      wf fvmpt2d ovex op1std op2ndd oveq12d eqtrd ) ACUCZFJZUDZVCKBUELVCBLZMLZV
      FNLZKOVCDLZMLZVCELZPOZVINLZVKPOZKOVEBKQQFVCAFQQUAZBUPVDABCDEFGHIUBUFAVDUG
      UHVEVGVLVHVNKVEVFVLVNUIZRZVGVLRACFVPBVOGVEVLVNQQVEVJVKVEVIVOJZVJQJAFVOVCD
      HSZVIQQUJTVEVKAFUKVCEISULZUMVEVMVKVEVRVMQJVSVIQQUNTVTUMUOUQZVLVNVFVJVKPUR
      ZVMVKPURZUSTVEVQVHVNRWAVLVNVFWBWCUTTVAVB $.
  $}

  ${
    $d X k $.  $d k ph $.
    vonsmullem15.t $e |- ( ph -> T = ( k e. X |-> <. ( ( 1st ` ( I ` k ) ) x. (
      V ` k ) ) , ( ( 2nd ` ( I ` k ) ) x. ( V ` k ) ) >. ) )
                       $.
    vonsmullem15.i $e |- ( ph -> I : X --> ( RR X. RR ) ) $.
    vonsmullem15.v $e |- ( ph -> V : X --> RR+ ) $.
    vonsmullem15.c $e |- ( ph -> C e. RR+ ) $.
    vonsmullem15.cv $e |- ( ph -> V = ( X X. { C } ) ) $.
    $( Lemma for ~ vonsmul : the measure of one edge of a half-open box is
       multiplied by the scale factor.  (Contributed by Xander Mackay and
       Claude, 16-Sep-2026.) $)
    vonsmullem15 $p |- ( ( ph /\ k e. X ) -> ( vol ` ( ( [,) o. T ) ` k ) ) = (
      C x. ( vol ` ( ( [,) o. I ) ` k ) ) ) )
                     $=
      ( wcel cfv cmul co cico cvol cr crp cv wa c1st c2nd ccom ffvelcdmda xp1st
      cxp syl xp2nd vonsmullem1 wceq adantr fveq1d fvconst2g sylan eqtrd oveq1d
      csn vonsmullem14 fveq2d wf simpr fvovco oveq2d 3eqtr4d ) ADUAZGMZUBZVGENZ
      UCNZVGFNZOPVJUDNZVLOPQPZRNZBVKVMQPZRNZOPZVGQCUENZRNBVGQEUENZRNZOPVIVOVLVQ
      OPVRVIVKVMVLVIVJSSUHZMZVKSMAGWBVGEIUFZVJSSUGUIVIWCVMSMWDVJSSUJUIAGTVGFJUF
      UKVIVLBVQOVIVLVGGBUSUHZNZBVIVGFWEAFWEULVHLUMUNABTMVHWFBULKGBVGTUOUPUQURUQ
      VIVSVNRACDEFGHIJUTVAVIWAVQBOVIVTVPRVIEQSSGVGAGWBEVBVHIUMAVHVCVDVAVEVF $.
  $}

  ${
    $d C k $.  $d X k $.  $d k ph $.
    vonsmullem16.t $e |- ( ph -> T = ( k e. X |-> <. ( ( 1st ` ( I ` k ) ) x. (
      V ` k ) ) , ( ( 2nd ` ( I ` k ) ) x. ( V ` k ) ) >. ) )
                       $.
    vonsmullem16.i $e |- ( ph -> I : X --> ( RR X. RR ) ) $.
    vonsmullem16.v $e |- ( ph -> V : X --> RR+ ) $.
    vonsmullem16.c $e |- ( ph -> C e. RR+ ) $.
    vonsmullem16.cv $e |- ( ph -> V = ( X X. { C } ) ) $.
    vonsmullem16.x $e |- ( ph -> X e. Fin ) $.
    $( Lemma for ~ vonsmul : the volume of a half-open box, given by its
       endpoint family, is multiplied by the scale factor raised to the
       dimension.  (Contributed by Xander Mackay and Claude, 16-Sep-2026.) $)
    vonsmullem16 $p |- ( ph -> prod_ k e. X ( vol ` ( ( [,) o. T ) ` k ) ) = (
      ( C ^ ( # ` X ) ) x. prod_ k e. X ( vol ` ( ( [,) o. I ) ` k ) ) ) )
                     $=
      ( cico cfv cvol cprod co wcel cr cv ccom cmul cexp vonsmullem15 prodeq2dv
      chash wa crp adantr rpcnd c1st c2nd cxp wf simpr fvovco fveq2d ffvelcdmda
      xp1st syl xp2nd volicorecl syl2anc eqeltrd recnd fprodmul wceq fprodconst
      cfn cc oveq1d 3eqtrd ) AGDUAZNCUBOPOZDQGBVNNEUBOZPOZUCRZDQGBDQZGVQDQZUCRB
      GUGOUDRZVTUCRAGVOVRDABCDEFGHIJKLUEUFAGBVQDMAVNGSZUHZBABUISWBKUJUKWCVQWCVQ
      VNEOZULOZWDUMOZNRZPOZTWCVPWGPWCENTTGVNAGTTUNZEUOWBIUJAWBUPUQURWCWETSZWFTS
      ZWHTSWCWDWISZWJAGWIVNEIUSZWDTTUTVAWCWLWKWMWDTTVBVAWEWFVCVDVEVFVGAVSWAVTUC
      AGVJSBVKSVSWAVHMABKUKGBDVIVDVLVM $.
  $}

  ${
    $d V k $.  $d X k $.  $d Y k $.  $d k ph $.
    ofdivpreim.x $e |- ( ph -> X e. _V ) $.
    ofdivpreim.v $e |- ( ph -> V : X --> RR+ ) $.
    ofdivpreim.y $e |- ( ph -> Y : X --> RR ) $.
    ofdivpreim.c $e |- ( ( ph /\ k e. X ) -> ( ( ( Y ` k ) / ( V ` k ) ) e. C
      <-> ( Y ` k ) e. D ) )
                       $.
    $( Scaling a point by ` V ` and testing coordinatewise membership in ` C `
       is the same as testing the unscaled point against the class ` D ` the
       scaling carries ` C ` to, coordinatewise, over an infinite index set.
       (Contributed by Xander Mackay and Claude, 16-Sep-2026.) $)
    ofdivpreim $p |- ( ph -> ( ( Y oF / V ) e. X_ k e. X C <-> Y e. X_ k e. X
      D ) )
                     $=
      ( cdiv cfv wcel wa wfn cvv adantr wb a1i cv cof co wral cixp wceq cr ffnd
      crp simpr fnfvof syl22anc eleq1d bitrd ralbidva df-3an elixp2 ovexd inidm
      w3a offn jca biantrurd 3bitr4d fexd ) ADUAZGELUBZUCZMZBNZDFUDZVFGMZCNZDFU
      DZVHDFBUENZGDFCUENZAVJVMDFAVFFNZOZVJVLVFEMLUCZBNVMVRVIVSBVRGFPZEFPZFQNZVQ
      VIVSUFAVTVQAFUGGJUHZRAWAVQAFUIEIUHZRAWBVQHRAVQUJFLGEQVFUKULUMKUNUOAVHQNZV
      HFPZVKUTZWEWFOZVKOZVOVKWGWISAWEWFVKUPTVOWGSADFBVHUQTAWHVKAWEWFAGEVGURAFFL
      FGEQQWCWDHHFUSVAVBVCVDAGQNZVTVNUTZWJVTOZVNOZVPVNWKWMSAWJVTVNUPTVPWKSADFCG
      UQTAWLVNAWJVTAFUGQGJHVEWCVBVCVDVD $.
  $}

  ${
    $d V k $.  $d X k $.  $d Y k $.  $d k ph $.
    vonsmullem18.t $e |- ( ph -> T = ( k e. X |-> <. ( ( 1st ` ( I ` k ) ) x. (
      V ` k ) ) , ( ( 2nd ` ( I ` k ) ) x. ( V ` k ) ) >. ) )
                       $.
    vonsmullem18.x $e |- ( ph -> X e. _V ) $.
    vonsmullem18.i $e |- ( ph -> I : X --> ( RR X. RR ) ) $.
    vonsmullem18.v $e |- ( ph -> V : X --> RR+ ) $.
    vonsmullem18.y $e |- ( ph -> Y : X --> RR ) $.
    $( Lemma for ~ vonsmul : a point lies in a scaled half-open box exactly
       when the point divided back lies in the box.  (Contributed by Xander
       Mackay and Claude, 16-Sep-2026.) $)
    vonsmullem18 $p |- ( ph -> ( ( Y oF / V ) e. X_ k e. X ( ( [,) o. I ) ` k )
      <-> Y e. X_ k e. X ( ( [,) o. T ) ` k ) ) )
                     $=
      ( cico ccom cfv wcel co cmul cr ffvelcdmda cv wa cdiv c1st c2nd cxp xp1st
      syl xp2nd crp elicodiv adantr simpr fvovco eleq2d vonsmullem14 3bitr4d
      wf ofdivpreim ) ACUAZMDNOZUTMBNOZCEFGIKLAUTFPZUBZUTGOZUTEOZUCQZUTDOZUDO
      ZVHUEOZMQZPVEVIVFRQVJVFRQMQZPVGVAPVEVBPVDVIVJVFVEVDVHSSUFZPZVISPAFVMUTDJT
      ZVHSSUGUHVDVNVJSPVOVHSSUIUHAFUJUTEKTAFSUTGLTUKVDVAVKVGVDDMSSFUTAFVMDURVCJ
      ULAVCUMUNUOVDVBVLVEABCDEFHJKUPUOUQUS $.
  $}

  ${
    $d X k $.
    vonsmullem19.j $e |- ( ph -> J = ( j e. NN |-> ( k e. X |-> <. ( ( 1st ` (
      ( I ` j ) ` k ) ) x. ( V ` k ) ) , ( ( 2nd ` ( ( I ` j ) ` k ) ) x. ( V `
      k ) ) >. ) ) )
                       $.
    vonsmullem19.x $e |- ( ph -> X e. _V ) $.
    $( Lemma for ~ vonsmul : the value of the scaled cover family at one index
       is the scaled endpoint family.  (Contributed by Xander Mackay and
       Claude, 16-Sep-2026.) $)
    vonsmullem19 $p |- ( ( ph /\ j e. NN ) -> ( J ` j ) = ( k e. X |-> <. ( (
      1st ` ( ( I ` j ) ` k ) ) x. ( V ` k ) ) , ( ( 2nd ` ( ( I ` j ) ` k ) )
      x. ( V ` k ) ) >. ) )
                     $=
      ( cn cv cfv c1st cmul co c2nd cop cmpt cvv wcel mptexd adantr fvmpt2d ) A
      BJCGCKZBKZDLLZMLUDFLZNOUFPLUGNOQZRZESHAUISTUEJTACGUHSIUAUBUC $.
  $}

  ${
    $d X j k $.  $d j k ph $.
    vonsmullem20.j $e |- ( ph -> J = ( j e. NN |-> ( k e. X |-> <. ( ( 1st ` (
      ( I ` j ) ` k ) ) x. ( V ` k ) ) , ( ( 2nd ` ( ( I ` j ) ` k ) ) x. ( V `
      k ) ) >. ) ) )
                       $.
    vonsmullem20.x $e |- ( ph -> X e. _V ) $.
    vonsmullem20.i $e |- ( ph -> I e. ( ( ( RR X. RR ) ^m X ) ^m NN ) ) $.
    vonsmullem20.v $e |- ( ph -> V : X --> RR+ ) $.
    $( Lemma for ~ vonsmul : the scaling of a countable family of half-open
       boxes is such a family.  (Contributed by Xander Mackay and Claude,
       16-Sep-2026.) $)
    vonsmullem20 $p |- ( ph -> J e. ( ( ( RR X. RR ) ^m X ) ^m NN ) ) $=
      ( cr cmap co cn cvv wcel a1i cfv wf cxp ovexd nnex cv c1st cmul c2nd cmpt
      cop vonsmullem19 reex xpex adantr syl ffvelcdmda crp vonsmullem13 elmapdd
      wa elmapi eqeltrrd fmpt3d ) ALLUAZGMNZOEPPAVCGMUBOPQAUCRABOCGCUDZBUDZDSZS
      ZUESVEFSZUFNVHUGSVIUFNUIUHZVDEHAVFOQZUSZVFESZVJVDABCDEFGHIUJZVLVCGVMPPVCP
      QVLLLUKUKULRAGPQVKIUMVLVMCVGFGVNVLVGVDQGVCVGTAOVDVFDADVDOMNQOVDDTJDVDOUTU
      NUOVGVCGUTUNAGUPFTVKKUMUQURVAVBUR $.
  $}

  ${
    $d C j k $.  $d X j k $.  $d j k ph $.
    vonsmullem21.j $e |- ( ph -> J = ( j e. NN |-> ( k e. X |-> <. ( ( 1st ` (
      ( I ` j ) ` k ) ) x. ( V ` k ) ) , ( ( 2nd ` ( ( I ` j ) ` k ) ) x. ( V `
      k ) ) >. ) ) )
                       $.
    vonsmullem21.x $e |- ( ph -> X e. Fin ) $.
    vonsmullem21.i $e |- ( ph -> I e. ( ( ( RR X. RR ) ^m X ) ^m NN ) ) $.
    vonsmullem21.v $e |- ( ph -> V : X --> RR+ ) $.
    vonsmullem21.c $e |- ( ph -> C e. RR+ ) $.
    vonsmullem21.cv $e |- ( ph -> V = ( X X. { C } ) ) $.
    $( Lemma for ~ vonsmul : the candidate sum of a scaled countable family of
       half-open boxes is the scale factor raised to the dimension, times the
       candidate sum of the original family.  (Contributed by Xander Mackay and
       Claude, 16-Sep-2026.) $)
    vonsmullem21 $p |- ( ph -> ( sum^ ` ( j e. NN |-> prod_ k e. X ( vol ` ( (
      [,) o. ( J ` j ) ) ` k ) ) ) ) = ( ( C ^ ( # ` X ) ) *e ( sum^ ` ( j e.
      NN |-> prod_ k e. X ( vol ` ( ( [,) o. ( I ` j ) ) ` k ) ) ) ) ) )
                     $=
      ( cn cfv csumge0 co wcel adantr cico ccom cvol cprod cmpt chash cexp cmul
      cv cxmu wa cfn elexd vonsmullem19 cr cxp wf elmapi syl ffvelcdmda crp csn
      cmap wceq vonsmullem16 mpteq2dva fveq2d cvv nnex a1i nfv hoiprodcl hashcl
      cn0 nn0zd rpexpcld vonsmullem8 eqtrd ) ACOHDUIZUACUIZFPZUBPUCPDUDZUEZQPCO
      BHUFPZUGRZHVSUAVTEPZUBPUCPDUDZUHRZUEZQPWECOWGUEQPUJRAWCWIQACOWBWHAVTOSZUK
      ZBWADWFGHACDEFGHIAHULJUMUNWKWFUOUOUPZHVCRZSHWLWFUQAOWMVTEAEWMOVCRSOWMEUQK
      EWMOURUSUTWFWLHURUSZAHVAGUQWJLTABVASWJMTAGHBVBUPVDWJNTAHULSZWJJTZVEVFVGAC
      OWGWEVHOVHSAVIVJWKDWFHWKDVKWPWNVLABWDMAWDAWOWDVNSJHVMUSVOVPVQVR $.
  $}

  ${
    $d V j k $.  $d X k $.  $d Y j k $.  $d j k ph $.
    vonsmullem22.j $e |- ( ph -> J = ( j e. NN |-> ( k e. X |-> <. ( ( 1st ` (
      ( I ` j ) ` k ) ) x. ( V ` k ) ) , ( ( 2nd ` ( ( I ` j ) ` k ) ) x. ( V `
      k ) ) >. ) ) )
                       $.
    vonsmullem22.x $e |- ( ph -> X e. _V ) $.
    vonsmullem22.i $e |- ( ph -> I e. ( ( ( RR X. RR ) ^m X ) ^m NN ) ) $.
    vonsmullem22.v $e |- ( ph -> V : X --> RR+ ) $.
    vonsmullem22.y $e |- ( ph -> Y : X --> RR ) $.
    $( Lemma for ~ vonsmul : a point lies in the union of a scaled countable
       family of half-open boxes exactly when the point divided back lies in
       the union of the original family.  (Contributed by Xander Mackay and
       Claude, 16-Sep-2026.) $)
    vonsmullem22 $p |- ( ph -> ( ( Y oF / V ) e. U_ j e. NN X_ k e. X ( ( [,)
      o. ( I ` j ) ) ` k ) <-> Y e. U_ j e. NN X_ k e. X ( ( [,) o. ( J ` j ) )
      ` k ) ) )
                     $=
      ( co cfv wcel cn adantr cr wf cdiv cv cico ccom cixp wrex wa vonsmullem19
      cof ciun cvv cxp cmap elmapi syl ffvelcdmda vonsmullem18 rexbidva 3bitr4g
      crp eliun ) AHFUAUINZCGCUBZUCBUBZDOZUDOUEZPZBQUFHCGVCUCVDEOZUDOUEZPZBQUFV
      BBQVFUJPHBQVIUJPAVGVJBQAVDQPZUGZVHCVEFGHABCDEFGIJUHAGUKPVKJRVLVESSULZGUMN
      ZPGVMVETAQVNVDDADVNQUMNPQVNDTKDVNQUNUOUPVEVMGUNUOAGUTFTVKLRAGSHTVKMRUQURB
      VBQVFVABHQVIVAUS $.
  $}

  ${
    $d A k $.  $d V k $.  $d X k $.  $d k ph $.
    ofmuldividd.x $e |- ( ph -> X e. _V ) $.
    ofmuldividd.a $e |- ( ph -> A : X --> RR ) $.
    ofmuldividd.v $e |- ( ph -> V : X --> RR+ ) $.
    $( Scaling a function by ` V ` and then dividing back by ` V ` recovers the
       function.  (Contributed by Xander Mackay and Claude, 16-Sep-2026.) $)
    ofmuldividd $p |- ( ph -> ( ( A oF x. V ) oF / V ) = A ) $=
      ( vk cmul cof co cdiv cvv cr ffnd crp offn cfv wfn adantr inidm wcel wceq
      cv wa simpr fnfvof syl22anc oveq1d ffvelcdmda recnd rpcnd rpne0d divcan4d
      3eqtrd eqfnfvd ) AHDBCIJKZCLJKZBADDLDUQCMMADDIDBCMMADNBFOZADPCGOZEEDUAZQZ
      UTEEVAQUSAHUDZDUBZUEZVCURRZVCUQRZVCCRZLKZVCBRZVHIKZVHLKVJVEUQDSZCDSZDMUBZ
      VDVFVIUCAVLVDVBTAVMVDUTTZAVNVDETZAVDUFZDLUQCMVCUGUHVEVGVKVHLVEBDSZVMVNVDV
      GVKUCAVRVDUSTVOVPVQDIBCMVCUGUHUIVEVJVHVEVJADNVCBFUJUKVEVHADPVCCGUJZULVEVH
      VSUMUNUOUP $.
  $}

  ${
    $d I y $.  $d J y $.  $d S y $.  $d V j k $.  $d X j k y $.  $d j k ph y $.
    vonsmullem24.j $e |- ( ph -> J = ( j e. NN |-> ( k e. X |-> <. ( ( 1st ` (
      ( I ` j ) ` k ) ) x. ( V ` k ) ) , ( ( 2nd ` ( ( I ` j ) ` k ) ) x. ( V `
      k ) ) >. ) ) )
                       $.
    vonsmullem24.x $e |- ( ph -> X e. _V ) $.
    vonsmullem24.i $e |- ( ph -> I e. ( ( ( RR X. RR ) ^m X ) ^m NN ) ) $.
    vonsmullem24.v $e |- ( ph -> V : X --> RR+ ) $.
    $( Lemma for ~ vonsmul : a cover of a set gives a cover of its scaling.
       (Contributed by Xander Mackay and Claude, 16-Sep-2026.) $)
    vonsmullem24 $p |- ( ( ph /\ S C_ U_ j e. NN X_ k e. X ( ( [,) o. ( I ` j )
      ) ` k ) ) -> { y e. ( RR ^m X ) | ( y oF / V ) e. S } C_ U_ j e. NN X_ k
      e. X ( ( [,) o. ( J ` j ) ) ` k ) )
                     $=
      ( cn cv cfv co wcel cr adantr cico ccom cixp ciun wss wa cdiv cmap simp1r
      cof w3a simp3 sseldd wb c1st cmul c2nd cop cmpt cvv cxp crp elmapi adantl
      wceq wf vonsmullem22 adantlr 3adant3 mpbid rabssdv ) ACDNEIEOZUADOZFPZUBP
      UCUDZUEZUFZBOZHUGUJQZCRZBSIUHQZDNEIVLUAVMGPUBPUCUDZVQVRWARZVTUKZVSVORZVRW
      BRZWDCVOVSAVPWCVTUIVQWCVTULUMVQWCWEWFUNZVTAWCWGVPAWCUFDEFGHIVRAGDNEIVLVNP
      ZUOPVLHPZUPQWHUQPWIUPQURUSUSVEWCJTAIUTRWCKTAFSSVAIUHQNUHQRWCLTAIVBHVFWCMT
      WCISVRVFAVRSIVCVDVGVHVIVJVK $.
  $}

  ${
    $d I x $.  $d J x $.  $d S j k x $.  $d S u v x $.  $d S x y $.
    $d V j k x $.  $d V v x $.  $d V x y $.  $d X k x $.  $d X x y $.
    $d j k ph x $.  $d ph u v x $.
    vonsmullem25.j $e |- ( ph -> J = ( j e. NN |-> ( k e. X |-> <. ( ( 1st ` (
      ( I ` j ) ` k ) ) x. ( V ` k ) ) , ( ( 2nd ` ( ( I ` j ) ` k ) ) x. ( V `
      k ) ) >. ) ) )
                       $.
    vonsmullem25.x $e |- ( ph -> X e. _V ) $.
    vonsmullem25.i $e |- ( ph -> I e. ( ( ( RR X. RR ) ^m X ) ^m NN ) ) $.
    vonsmullem25.v $e |- ( ph -> V : X --> RR+ ) $.
    vonsmullem25.s $e |- ( ph -> S C_ ( RR ^m X ) ) $.
    $( Lemma for ~ vonsmul : a cover of the scaling of a set gives a cover of
       the set.  (Contributed by Xander Mackay and Claude, 16-Sep-2026.) $)
    vonsmullem25 $p |- ( ( ph /\ { y e. ( RR ^m X ) | ( y oF / V ) e. S } C_ U_
      j e. NN X_ k e. X ( ( [,) o. ( J ` j ) ) ` k ) ) -> S C_ U_ j e. NN X_ k
      e. X ( ( [,) o. ( I ` j ) ) ` k ) )
                     $=
      ( cv co wcel cr cfv cvv vx vu vv cdiv cof cmap crab cn cico ccom cixp wss
      ciun wa cmul wceq adantr wf sselda elmapi syl ofmuldividd adantlr simplr
      crp oveq1 eleq1d reex a1i remulcl adantl rpssre inidm off elmapdd eqeltrd
      fssd elrabd sseldd wb c1st c2nd cop cmpt cxp vonsmullem22 mpbird eqeltrrd
      simpr ssd ) ABOZHUDUEZPZCQZBRIUFPZUGZDUHEIEOZUIDOZGSUJSUKUMZULZUNZUACDUHE
      IWQUIWRFSZUJSUKUMZXAUAOZCQZUNZXDHUOUEPZHWLPZXDXCAXEXHXDUPWTAXEUNZXDHIAITQ
      XEKUQZXIXDWOQIRXDURACWOXDNUSXDRIUTVAZAIVEHURXEMUQZVBZVCXFXHXCQZXGWSQZXFWP
      WSXGAWTXEVDAXEXGWPQWTXIWNXHCQBXGWOWKXGUPWMXHCWKXGHWLVFVGXIRIXGTTRTQXIVHVI
      XJXIUBUCIIIUORRRXDHTTUBOZRQUCOZRQUNXPXQUOPRQXIXPXQVJVKXKXIIVERHXLVERULXIV
      LVIVQXJXJIVMVNZVOXIXHXDCXMAXEWIVPVRVCVSAXEXNXOVTWTXIDEFGHIXGAGDUHEIWQXBSZ
      WASWQHSZUOPXSWBSXTUOPWCWDWDUPXEJUQXJAFRRWEIUFPUHUFPQXELUQXLXRWFVCWGWHWJ
      $.
  $}

  ${
    $d I y $.  $d J y $.  $d S j k y $.  $d V j k y $.  $d X j k y $.
    $d j k ph y $.
    vonsmullem26.j $e |- ( ph -> J = ( j e. NN |-> ( k e. X |-> <. ( ( 1st ` (
      ( I ` j ) ` k ) ) x. ( V ` k ) ) , ( ( 2nd ` ( ( I ` j ) ` k ) ) x. ( V `
      k ) ) >. ) ) )
                       $.
    vonsmullem26.x $e |- ( ph -> X e. _V ) $.
    vonsmullem26.i $e |- ( ph -> I e. ( ( ( RR X. RR ) ^m X ) ^m NN ) ) $.
    vonsmullem26.v $e |- ( ph -> V : X --> RR+ ) $.
    vonsmullem26.s $e |- ( ph -> S C_ ( RR ^m X ) ) $.
    $( Lemma for ~ vonsmul : a countable family of half-open boxes covers a set
       exactly when its scaling covers the scaling of the set.  (Contributed by
       Xander Mackay and Claude, 16-Sep-2026.) $)
    vonsmullem26 $p |- ( ph -> ( S C_ U_ j e. NN X_ k e. X ( ( [,) o. ( I ` j )
      ) ` k ) <-> { y e. ( RR ^m X ) | ( y oF / V ) e. S } C_ U_ j e. NN X_ k
      e. X ( ( [,) o. ( J ` j ) ) ` k ) ) )
                     $=
      ( cn cv cico cfv ccom cixp ciun wss cdiv cof co wcel cr cmap vonsmullem24
      crab vonsmullem25 impbida ) ACDOEIEPZQDPZFRSRTUAUBBPHUCUDUECUFBUGIUHUEUJD
      OEIUMQUNGRSRTUAUBABCDEFGHIJKLMUIABCDEFGHIJKLMNUKUL $.
  $}

  ${
    $d C f i z $.  $d C i j k z $.  $d S f i y z $.  $d S i j k y z $.
    $d V f i m n r s $.  $d V i j k m n r s $.  $d V f i r s y $.
    $d V f i m n z $.  $d X f i m n r s $.  $d X i j k m n r s $.
    $d X f i r s y $.  $d X f i m n z $.  $d f i w y z $.  $d i j k ph y $.
    $d j k w y z $.
    vonsmullem27.x $e |- ( ph -> X e. Fin ) $.
    vonsmullem27.c $e |- ( ph -> C e. RR+ ) $.
    vonsmullem27.cv $e |- ( ph -> V = ( X X. { C } ) ) $.
    vonsmullem27.v $e |- ( ph -> V : X --> RR+ ) $.
    vonsmullem27.s $e |- ( ph -> S C_ ( RR ^m X ) ) $.
    vonsmullem27.m $e |- M = { z e. RR* | E. i e. ( ( ( RR X. RR ) ^m X ) ^m NN
      ) ( S C_ U_ j e. NN X_ k e. X ( ( [,) o. ( i ` j ) ) ` k ) /\ z = ( sum^
      ` ( j e. NN |-> prod_ k e. X ( vol ` ( ( [,) o. ( i ` j ) ) ` k ) ) ) ) )
      }
                       $.
    vonsmullem27.n $e |- N = { z e. RR* | E. f e. ( ( ( RR X. RR ) ^m X ) ^m NN
      ) ( { y e. ( RR ^m X ) | ( y oF / V ) e. S } C_ U_ n e. NN X_ m e. X ( (
      [,) o. ( f ` n ) ) ` m ) /\ z = ( sum^ ` ( n e. NN |-> prod_ m e. X ( vol
      ` ( ( [,) o. ( f ` n ) ) ` m ) ) ) ) ) }
                       $.
    $( Lemma for ~ vonsmul : each candidate sum for a set scales, by the factor
       raised to the dimension, to a candidate sum for the scaled set.
       (Contributed by Xander Mackay and Claude, 16-Sep-2026.) $)
    vonsmullem27 $p |- ( ( ph /\ w e. M ) -> ( ( C ^ ( # ` X ) ) *e w ) e. N )
                     $=
      ( vr vs cv wcel wa chash cfv cexp co cxmu cdiv cof cr cmap crab cico ccom
      cn cixp ciun wss cvol cprod cmpt csumge0 wceq cxp wrex cxr anbi2d rexbidv
      eqeq1 crp adantr cfn cn0 hashcl nn0zd rpexpcld rpxrd elrab2 bilani simpld
      syl weq xmulcld simprd wi c1st cmul c2nd cop fveq1 coeq2d fveq1d ixpeq2dv
      iuneq2d sseq2d fveq2d mpteq2dv eqeq2d anbi12d fveq2 oveq1d opeq12d 2fveq3
      prodeq2dv cbvmptv oveq12d mpteq2i eqtri ad2antrr elexd simpr vonsmullem20
      a1i wf simprl wb vonsmullem26 mpbid cbvixpv eqtrid sseqtrdi simprr oveq2d
      cbviunv csn vonsmullem21 eqtr4d fveq2i eqtrdi rspcedvdw rexlimdva2 syldan
      cbvprodv jca mpd elrabd eleqtrrdi ) ADUFZMUGZUHZEPUIUJZUKULZUUDUMULZBUFOU
      NUOULFUGBUPPUQULZURZLVAKPKUFZUSLUFZGUFZUJZUTZUJZVBZVCZVDZCUFZLVAPUUQVEUJZ
      KVFZVGZVHUJZVIZUHZGUPUPVJPUQULVAUQULZVKZCVLURNUUFUVIUUTUUIUVEVIZUHZGUVHVK
      ZCUUIVLUVAUUIVIZUVGUVKGUVHUVMUVFUVJUUTUVAUUIUVEVOVMVNUUFUUHUUDUUFUUHUUFEU
      UGAEVPUGZUUERVQUUFUUGUUFPVRUGZUUGVSUGAUVOUUEQVQPVTWGWAWBWCUUFUUDVLUGZFIVA
      JPJUFZUSIUFZHUFZUJZUTUJZVBVCVDZUUDIVAPUWAVEUJJVFVGVHUJZVIZUHZHUVHVKZUUEUV
      PUWFUHAUWBUVAUWCVIZUHZHUVHVKUWFCUUDVLMCDWHZUWHUWEHUVHUWIUWGUWDUWBUVAUUDUW
      CVOVMVNUBWDWEZWFZWIUUFUWFUVLUUFUVPUWFUWJWJAUUEUVPUWFUVLWKUWKAUVPUHZUWEUVL
      HUVHUWLUVSUVHUGZUHZUWEUHZUVKUUKLVAKPUULUSUUMUDVAUEPUEUFZUDUFZUVSUJZUJZWLU
      JZUWPOUJZWMULZUWSWNUJZUXAWMULZWOZVGZVGZUJZUTZUJZVBZVCZVDZUUILVAPUXJVEUJZK
      VFZVGZVHUJZVIZUHGUXGUVHUUNUXGVIZUUTUXMUVJUXRUXSUUSUXLUUKUXSLVAUURUXKUXSKP
      UUQUXJUXSUULUUPUXIUXSUUOUXHUSUUMUUNUXGWPWQWRZWSWTXAUXSUVEUXQUUIUXSUVDUXPV
      HUXSLVAUVCUXOUXSPUVBUXNKUXSUULPUGZUHUUQUXJVEUXSUUQUXJVIUYAUXTVQXBXJXCXBXD
      XEUWNUXGUVHUGUWEUWNIJUVSUXGOPUXGIVAJPUVQUVTUJZWLUJZUVQOUJZWMULZUYBWNUJZUY
      DWMULZWOZVGZVGZVIUWNUXGIVAUEPUWPUVTUJZWLUJZUXAWMULZUYKWNUJZUXAWMULZWOZVGZ
      VGUYJUDIVAUXFUYQUDIWHZUEPUXEUYPUYRUXBUYMUXDUYOUYRUWTUYLUXAWMUYRUWSUYKWLUY
      RUWPUWRUVTUWQUVRUVSXFWRZXBXGUYRUXCUYNUXAWMUYRUWSUYKWNUYSXBXGXHXCXKIVAUYQU
      YIUEJPUYPUYHUEJWHZUYMUYEUYOUYGUYTUYLUYCUXAUYDWMUWPUVQWLUVTXIUWPUVQOXFZXLU
      YTUYNUYFUXAUYDWMUWPUVQWNUVTXIVUAXLXHXKXMXNXSZUWNPVRAUVOUVPUWMQXOZXPZUWLUW
      MXQZAPVPOXTUVPUWMTXOZXRVQUWOUXMUXRUWOUUKIVAJPUVQUSUVRUXGUJZUTZUJZVBZVCZUX
      LUWOUWBUUKVUKVDZUWNUWBUWDYAUWNUWBVULYBUWEUWNBFIJUVSUXGOPVUBVUDVUEVUFAFUUJ
      VDUVPUWMUAXOYCVQYDILVAVUJUXKILWHZVUJKPUULVUHUJZVBUXKJKPVUIVUNUVQUULVUHXFY
      EVUMKPVUNUXJVUMUULVUHUXIVUMVUGUXHUSUVRUUMUXGXFWQWRZWSYFYJYGUWOUUIIVAPVUIV
      EUJZJVFZVGZVHUJZUXQUWOUUIUUHUWCUMULZVUSUWOUUDUWCUUHUMUWNUWBUWDYHYIUWNVUSV
      UTVIUWEUWNEIJUVSUXGOPVUBVUCVUEVUFAUVNUVPUWMRXOAOPEYKVJVIUVPUWMSXOYLVQYMVU
      RUXPVHILVAVUQUXOVUMVUQPVUNVEUJZKVFUXOPVUPVVAJKUVQUULVEVUHXIYSVUMPVVAUXNKV
      UMUYAUHVUNUXJVEVUMVUNUXJVIUYAVUOVQXBXJYFXKYNYOYTYPYQYRUUAUUBUCUUC $.
  $}

  ${
    $d C f i w z $.  $d C i j k w z $.  $d M w $.  $d N w $.  $d S f i y z $.
    $d S i j k y z $.  $d V f i m n z $.  $d V i j k m n z $.  $d V f i y z $.
    $d X f i m n z $.  $d X i j k m n z $.  $d X f i w y z $.
    $d i j k ph w y $.
    vonsmullem28.x $e |- ( ph -> X e. Fin ) $.
    vonsmullem28.c $e |- ( ph -> C e. RR+ ) $.
    vonsmullem28.cv $e |- ( ph -> V = ( X X. { C } ) ) $.
    vonsmullem28.v $e |- ( ph -> V : X --> RR+ ) $.
    vonsmullem28.s $e |- ( ph -> S C_ ( RR ^m X ) ) $.
    vonsmullem28.m $e |- M = { z e. RR* | E. i e. ( ( ( RR X. RR ) ^m X ) ^m NN
      ) ( S C_ U_ j e. NN X_ k e. X ( ( [,) o. ( i ` j ) ) ` k ) /\ z = ( sum^
      ` ( j e. NN |-> prod_ k e. X ( vol ` ( ( [,) o. ( i ` j ) ) ` k ) ) ) ) )
      }
                       $.
    vonsmullem28.n $e |- N = { z e. RR* | E. f e. ( ( ( RR X. RR ) ^m X ) ^m NN
      ) ( { y e. ( RR ^m X ) | ( y oF / V ) e. S } C_ U_ n e. NN X_ m e. X ( (
      [,) o. ( f ` n ) ) ` m ) /\ z = ( sum^ ` ( n e. NN |-> prod_ m e. X ( vol
      ` ( ( [,) o. ( f ` n ) ) ` m ) ) ) ) ) }
                       $.
    $( Lemma for ~ vonsmul : the outer measure of the scaled set is at most the
       scale factor raised to the dimension, times the outer measure of the
       set.  (Contributed by Xander Mackay and Claude, 16-Sep-2026.) $)
    vonsmullem28 $p |- ( ph -> inf ( N , RR* , < ) <_ ( ( C ^ ( # ` X ) ) *e
      inf ( M , RR* , < ) ) )
                     $=
      ( vw cxr clt cinf chash cfv cexp co cv cxmu cmpt crn cle wss vonsmullem27
      wbr wcel wral ralrimiva eqid rnmptss syl cdiv cr cmap crab cico ccom cixp
      cof cn ciun cvol cprod csumge0 wceq wa cxp ssrab3 infxrss sylancl cfn cn0
      wrex hashcl nn0zd rpexpcld sselda vonsmullem12 cres mptresid rneqi rnresi
      a1i cid eqtr3i infeq1i oveq2i eqtrdi breqtrd ) AMUDUEUFZUCLDOUGUHZUIUJZUC
      UKZULUJZUMZUNZUDUEUFZXELUDUEUFZULUJZUOAXIMUPZMUDUPXCXJUOURAXGMUSZUCLUTXMA
      XNUCLABCUCDEFGHIJKLMNOPQRSTUAUBUQVAUCLXGMXHXHVBVCVDBUKNVEVLUJEUSBVFOVGUJV
      HKVMJOJUKVIKUKFUKUHVJUHZVKVNUPCUKZKVMOXOVOUHJVPUMVQUHVRVSFVFVFVTOVGUJVMVG
      UJZWFCUDMUBWAXIMWBWCAXJXEUCLXFUMZUNZUDUEUFZULUJXLAUCLXFXEADXDQAXDAOWDUSXD
      WEUSPOWGVDWHWIALUDXFLUDUPAEHVMIOIUKVIHUKGUKUHVJUHZVKVNUPXPHVMOYAVOUHIVPUM
      VQUHVRVSGXQWFCUDLUAWAWPWJWKXTXKXEULUDXSLUEWQLWLZUNXSLYBXRUCLWMWNLWOWRWSWT
      XAXB $.
  $}

  ${
    $d A k $.  $d V k $.  $d W k $.  $d X k $.  $d k ph $.
    ofdivrecip.x $e |- ( ph -> X e. _V ) $.
    ofdivrecip.a $e |- ( ph -> A : X --> RR ) $.
    ofdivrecip.v $e |- ( ph -> V : X --> RR+ ) $.
    ofdivrecip.w $e |- ( ph -> W = ( k e. X |-> ( 1 / ( V ` k ) ) ) ) $.
    $( Dividing by the pointwise reciprocal of ` V ` is the same as scaling by
       ` V ` in the other direction.  (Contributed by Xander Mackay and Claude,
       16-Sep-2026.) $)
    ofdivrecip $p  |- ( ph -> ( A oF / W ) = ( A oF x. V ) ) $=
      ( cdiv co cmul cvv cr ffnd cfv crp wfn adantr c1 wcel ffvelcdmda rpreccld
      cof cv wa rpred fmpt3d inidm offn wceq simpr fnfvof syl22anc oveq2d recnd
      fvmpt2d rpcnd rpne0d divrecd recrecd eqtrd 3eqtrd eqtr4d eqfnfvd ) ACFBEK
      UELZBDMUELZAFFKFBENNAFOBHPZAFOEACFUACUFZDQZKLZOEJAVJFUBZUGZVLVNVKAFRVJDIU
      CZUDZUHUIPZGGFUJZUKAFFMFBDNNVIAFRDIPZGGVRUKVNVJVGQZVJBQZVKMLZVJVHQZVNVTWA
      VJEQZKLZWAVLKLZWBVNBFSZEFSZFNUBZVMVTWEULAWGVMVITZAWHVMVQTAWIVMGTZAVMUMZFK
      BENVJUNUOVNWDVLWAKACFVLERJVPURUPVNWFWAUAVLKLZMLWBVNWAVLVNWAAFOVJBHUCUQVNV
      LVPUSVNVLVPUTVAVNWMVKWAMVNVKVNVKVOUSVNVKVOUTVBUPVCVDVNWGDFSZWIVMWCWBULWJA
      WNVMVSTWKWLFMBDNVJUNUOVEVF $.
  $}

  ${
    $d S t u y $.  $d V b t $.  $d V k t $.  $d V t u y $.  $d W k t $.
    $d W t u y $.  $d X a b t $.  $d X k t $.  $d X t u y $.  $d a b ph t $.
    $d k ph t $.
    vonsmullem30.x $e |- ( ph -> X e. _V ) $.
    vonsmullem30.v $e |- ( ph -> V : X --> RR+ ) $.
    vonsmullem30.s $e |- ( ph -> S C_ ( RR ^m X ) ) $.
    vonsmullem30.w $e |- ( ph -> W = ( k e. X |-> ( 1 / ( V ` k ) ) ) ) $.
    $( Lemma for ~ vonsmul : scaling a set and then scaling back by the
       reciprocal gives the set.  (Contributed by Xander Mackay and Claude,
       16-Sep-2026.) $)
    vonsmullem30 $p |- ( ph -> { u e. ( RR ^m X ) | ( u oF / W ) e. { y e. ( RR
      ^m X ) | ( y oF / V ) e. S } } = S )
                     $=
      ( cv co wcel cr wa cmul cvv a1i vt va vb cdiv cof cmap crab adantr elmapi
      wf adantl crp c1 cfv cmpt wceq ofdivrecip reex remulcl wss rpssre inidm
      off elmapdd eqeltrd oveq1 eleq1d elrab mpbirand oveq1d ofmuldividd eqtrd
      fssd wb bitrd pm5.32da sseld pm4.71rd 3bitr4d eqrdv ) AUACMZGUDUEZNZBMZFW
      BNZDOZBPHUFNZUGZOZCWGUGZDAUAMZWGOZWKGWBNZWHOZQZWLWKDOZQWKWJOZWPAWLWNWPAWL
      QZWNWMFWBNZDOZWPWRWNWMWGOZWTWRWMWKFRUENZWGWRWKEFGHAHSOWLIUHZWLHPWKUJAWKPH
      UIUKZAHULFUJWLJUHZAGEHUMEMFUNUDNUOUPWLLUHUQZWRPHXBSSPSOWRURTXCWRUBUCHHHRP
      PPWKFSSUBMZPOUCMZPOQXGXHRNPOWRXGXHUSUKXDWRHULPFXEULPUTWRVATVMXCXCHVBVCVDV
      EWNXAWTQVNWRWFWTBWMWGWDWMUPWEWSDWDWMFWBVFVGVHTVIWRWSWKDWRWSXBFWBNWKWRWMXB
      FWBXFVJWRWKFHXCXDXEVKVLVGVOVPWQWOVNAWIWNCWKWGWAWKUPWCWMWHWAWKGWBVFVGVHTAW
      PWLADWGWKKVQVRVSVT $.
  $}

  ${
    $d C f i k z $.  $d C f k m n z $.  $d S f i u y z $.  $d S f m n u y z $.
    $d V f i k z $.  $d V f k m n z $.  $d V f i u y z $.  $d W f i j k z $.
    $d W f j k m n z $.  $d W f i u y z $.  $d X f i j k z $.
    $d X f j k m n z $.  $d X f i u y z $.  $d f i k ph z $.  $d m n ph u z $.
    vonsmullem31.x $e |- ( ph -> X e. Fin ) $.
    vonsmullem31.c $e |- ( ph -> C e. RR+ ) $.
    vonsmullem31.cv $e |- ( ph -> V = ( X X. { C } ) ) $.
    vonsmullem31.v $e |- ( ph -> V : X --> RR+ ) $.
    vonsmullem31.s $e |- ( ph -> S C_ ( RR ^m X ) ) $.
    vonsmullem31.w $e |- ( ph -> W = ( k e. X |-> ( 1 / ( V ` k ) ) ) ) $.
    vonsmullem31.m $e |- M = { z e. RR* | E. i e. ( ( ( RR X. RR ) ^m X ) ^m NN
      ) ( S C_ U_ j e. NN X_ k e. X ( ( [,) o. ( i ` j ) ) ` k ) /\ z = ( sum^
      ` ( j e. NN |-> prod_ k e. X ( vol ` ( ( [,) o. ( i ` j ) ) ` k ) ) ) ) )
      }
                       $.
    vonsmullem31.n $e |- N = { z e. RR* | E. f e. ( ( ( RR X. RR ) ^m X ) ^m NN
      ) ( { y e. ( RR ^m X ) | ( y oF / V ) e. S } C_ U_ n e. NN X_ m e. X ( (
      [,) o. ( f ` n ) ) ` m ) /\ z = ( sum^ ` ( n e. NN |-> prod_ m e. X ( vol
      ` ( ( [,) o. ( f ` n ) ) ` m ) ) ) ) ) }
                       $.
    $( Lemma for ~ vonsmul : the outer measure of the set is at most the
       reciprocal scale factor raised to the dimension, times the outer measure
       of the scaled set.  (Contributed by Xander Mackay and Claude,
       16-Sep-2026.) $)
    vonsmullem31 $p |- ( ph -> inf ( M , RR* , < ) <_ ( ( ( 1 / C ) ^ ( # ` X )
      ) *e inf ( N , RR* , < ) ) )
                     $=
      ( vu cxr clt cinf cv cdiv cof co wcel cr cmap crab cn cico ccom cixp ciun
      cfv wss cvol cprod cmpt csumge0 wceq wa cxp wrex c1 chash cexp cxmu elexd
      cle cfn vonsmullem30 sseq1d anbi1d rexbidv rabbidv eqtr4id infeq1d fveq1d
      rpreccld csn adantr crp fvconst2g sylan eqtrd mpteq2dva fconstmpt eqtr4di
      oveq2d ffvelcdmda fmpt3d ssrab2 a1i eqid vonsmullem28 eqbrtrd ) ALUFUGUHU
      EUIOUJUKZULBUINXEULEUMZBUNPUOULZUPZUMUEXGUPZHUQIPIUIZURHUIGUIVBUSVBZUTVAZ
      VCZCUIHUQPXKVDVBIVEVFVGVBVHZVIZGUNUNVJPUOULUQUOULZVKZCUFUPZUFUGUHVLDUJULZ
      PVMVBVNULMUFUGUHVOULVQAUFLXRUGALEXLVCZXNVIZGXPVKZCUFUPXRUCAXQYBCUFAXOYAGX
      PAXMXTXNAXIEXLABUEEINOPAPVRQVPTUAUBVSVTWAWBWCWDWEAUECXSXHGFKJIHMXROPQADRW
      GAOIPXSVFZPXSWHVJAOIPVLXJNVBZUJULZVFYCUBAIPYEXSAXJPUMZVIZYDDVLUJYGYDXJPDW
      HVJZVBZDAYDYIVHYFAXJNYHSWFWIADWJUMYFYIDVHRPDXJWJWKWLWMWQWNWMIPXSWOWPAIPYE
      WJOUBYGYDAPWJXJNTWRWGWSXHXGVCAXFBXGWTXAUDXRXBXCXD $.
  $}

  ${
    $d C f i k z $.  $d C f k m n z $.  $d S f i y z $.  $d S f m n y z $.
    $d V f i k z $.  $d V f k m n z $.  $d V f i y z $.  $d W f i j k z $.
    $d W f j k m n z $.  $d W f i y z $.  $d X f i j k z $.
    $d X f j k m n z $.  $d X f i y z $.  $d f i k ph z $.  $d m n ph z $.
    vonsmullem32.x $e |- ( ph -> X e. Fin ) $.
    vonsmullem32.c $e |- ( ph -> C e. RR+ ) $.
    vonsmullem32.cv $e |- ( ph -> V = ( X X. { C } ) ) $.
    vonsmullem32.v $e |- ( ph -> V : X --> RR+ ) $.
    vonsmullem32.s $e |- ( ph -> S C_ ( RR ^m X ) ) $.
    vonsmullem32.w $e |- ( ph -> W = ( k e. X |-> ( 1 / ( V ` k ) ) ) ) $.
    vonsmullem32.m $e |- M = { z e. RR* | E. i e. ( ( ( RR X. RR ) ^m X ) ^m NN
      ) ( S C_ U_ j e. NN X_ k e. X ( ( [,) o. ( i ` j ) ) ` k ) /\ z = ( sum^
      ` ( j e. NN |-> prod_ k e. X ( vol ` ( ( [,) o. ( i ` j ) ) ` k ) ) ) ) )
      }
                       $.
    vonsmullem32.n $e |- N = { z e. RR* | E. f e. ( ( ( RR X. RR ) ^m X ) ^m NN
      ) ( { y e. ( RR ^m X ) | ( y oF / V ) e. S } C_ U_ n e. NN X_ m e. X ( (
      [,) o. ( f ` n ) ) ` m ) /\ z = ( sum^ ` ( n e. NN |-> prod_ m e. X ( vol
      ` ( ( [,) o. ( f ` n ) ) ` m ) ) ) ) ) }
                       $.
    $( Lemma for ~ vonsmul : the scale factor raised to the dimension, times
       the outer measure of the set, is at most the outer measure of the scaled
       set.  (Contributed by Xander Mackay and Claude, 16-Sep-2026.) $)
    vonsmullem32 $p |- ( ph -> ( ( C ^ ( # ` X ) ) *e inf ( M , RR* , < ) ) <_
      inf ( N , RR* , < ) )
                     $=
      ( chash cfv cexp co cxr clt cinf cxmu c1 cdiv cle wbr vonsmullem31 rpne0d
      rpcnd cfn wcel cn0 hashcl syl nn0zd exprecd oveq1d breqtrd crp wb cn cico
      wss cv ccom cixp ciun cvol cprod cmpt csumge0 wceq wa cr cmap wrex ssrab3
      cxp a1i infxrcld rpexpcld rpreccld rpxrd cof crab xmulcld xlemul2 syl3anc
      mpbid xmulrecd ) ADPUEUFZUGUHZLUIUJUKZULUHZXBUMXBUNUHZMUIUJUKZULUHZULU
      HZXFUOAXCXGUOUPZXDXHUOUPZAXCUMDUNUHXAUGUHZXFULUHXGUOABCDEFGHIJKLMNOPQRSTU
      AUBUCUDUQAXKXEXFULADXAADRUSADRURAXAAPUTVAXAVBVAQPVCVDVEZVFVGVHAXCUIVAXGUI
      VAXBVIVAXIXJVJALLUIVMAEHVKIPIVNVLHVNGVNUFVOUFZVPVQVMCVNZHVKPXMVRUFIVSVTWA
      UFWBWCGWDWDWHPWEUHVKWEUHZWFCUILUCWGWIWJAXEXFAXEAXBADXARXLWKZWLWMAMMUIVMAB
      VNNUNWNUHEVABWDPWEUHWOKVKJPJVNVLKVNFVNUFVOUFZVPVQVMXNKVKPXQVRUFJVSVTWAUFW
      BWCFXOWFCUIMUDWGWIWJZWPXPXCXGXBWQWRWSAXBXFXPXRWTVH $.
  $}

  ${
    $d C f i j k m n z $.  $d S f i j k m n y z $.  $d V f i j k m n y z $.
    $d W f i j k m n y z $.  $d X f i j k m n y z $.  $d f i j k m n ph y z $.
    vonsmullem33.x $e |- ( ph -> X e. Fin ) $.
    vonsmullem33.c $e |- ( ph -> C e. RR+ ) $.
    vonsmullem33.cv $e |- ( ph -> V = ( X X. { C } ) ) $.
    vonsmullem33.v $e |- ( ph -> V : X --> RR+ ) $.
    vonsmullem33.s $e |- ( ph -> S C_ ( RR ^m X ) ) $.
    vonsmullem33.w $e |- ( ph -> W = ( k e. X |-> ( 1 / ( V ` k ) ) ) ) $.
    vonsmullem33.m $e |- M = { z e. RR* | E. i e. ( ( ( RR X. RR ) ^m X ) ^m NN
      ) ( S C_ U_ j e. NN X_ k e. X ( ( [,) o. ( i ` j ) ) ` k ) /\ z = ( sum^
      ` ( j e. NN |-> prod_ k e. X ( vol ` ( ( [,) o. ( i ` j ) ) ` k ) ) ) ) )
      }
                       $.
    vonsmullem33.n $e |- N = { z e. RR* | E. f e. ( ( ( RR X. RR ) ^m X ) ^m NN
      ) ( { y e. ( RR ^m X ) | ( y oF / V ) e. S } C_ U_ n e. NN X_ m e. X ( (
      [,) o. ( f ` n ) ) ` m ) /\ z = ( sum^ ` ( n e. NN |-> prod_ m e. X ( vol
      ` ( ( [,) o. ( f ` n ) ) ` m ) ) ) ) ) }
                       $.
    $( Lemma for ~ vonsmul : the scale factor raised to the dimension, times
       the outer measure of the set, is the outer measure of the scaled set, as
       an equality of the two candidate infima.  (Contributed by Xander Mackay
       and Claude, 16-Sep-2026.) $)
    vonsmullem33 $p |- ( ph -> ( ( C ^ ( # ` X ) ) *e inf ( M , RR* , < ) ) =
      inf ( N , RR* , < ) )
                     $=
      ( chash cfv cexp cxr clt cinf cxmu cfn wcel cn0 hashcl syl nn0zd rpexpcld
      co rpxrd wss cn cv cico ccom cixp ciun cvol cprod cmpt csumge0 wceq wa cr
      cxp cmap wrex ssrab3 infxrcld xmulcld cdiv crab vonsmullem32 vonsmullem28
      a1i cof xrletrid ) ADPUEUFZUGUSZLUHUIUJZUKUSMUHUIUJAWIWJAWIADWHRAWHAPULUM
      WHUNUMQPUOUPUQURUTALLUHVAAEHVBIPIVCVDHVCGVCUFVEUFZVFVGVACVCZHVBPWKVHUFIVI
      VJVKUFVLVMGVNVNVOPVPUSVBVPUSZVQCUHLUCVRWEVSVTAMMUHVAABVCNWAWFUSEUMBVNPVPU
      SWBKVBJPJVCVDKVCFVCUFVEUFZVFVGVAWLKVBPWNVHUFJVIVJVKUFVLVMFWMVQCUHMUDVRWEV
      SABCDEFGHIJKLMNOPQRSTUAUBUCUDWCABCDEFGHIJKLMNPQRSTUAUCUDWDWG $.
  $}

  $( The preimage of an intersection under a coordinatewise scaling is the
     intersection of the preimages.  (Contributed by Xander Mackay and Claude,
     16-Sep-2026.) $)
  ofdivpreimin $p |- { y e. ( RR ^m X ) | ( y oF / V ) e. ( A i^i B ) } = ( { y
    e. ( RR ^m X ) | ( y oF / V ) e. A } i^i { y e. ( RR ^m X ) | ( y oF / V )
    e. B } )
                   $=
    ( cv cdiv cof co cin wcel cr cmap crab wa elin rabbii inrab eqtr4i ) AFDGHI
    ZBCJKZALEMIZNTBKZTCKZOZAUBNUCAUBNUDAUBNJUAUEAUBTBCPQUCUDAUBRS $.

  $( The preimage of a class difference under a coordinatewise scaling is the
     difference of the preimages.  (Contributed by Xander Mackay and Claude,
     16-Sep-2026.) $)
  ofdivpreimdif $p |- { y e. ( RR ^m X ) | ( y oF / V ) e. ( A \ B ) } = ( { y
    e. ( RR ^m X ) | ( y oF / V ) e. A } \ { y e. ( RR ^m X ) | ( y oF / V ) e.
    B } )
                   $=
    ( cv cdiv cof co cdif wcel cr cmap crab wn wa eldif rabbii difrab eqtr4i )
    AFDGHIZBCJKZALEMIZNUABKZUACKZOPZAUCNUDAUCNUEAUCNJUBUFAUCUABCQRUDUEAUCST $.

  ${
    $d V k $.  $d X k $.  $d k ph $.
    vonsmullem36.v $e |- ( ph -> V : X --> RR+ ) $.
    vonsmullem36.w $e |- ( ph -> W = ( k e. X |-> ( 1 / ( V ` k ) ) ) ) $.
    $( Lemma for ~ vonsmul : the pointwise reciprocal of the pointwise
       reciprocal of a positive scaling is the scaling.  (Contributed by Xander
       Mackay and Claude, 16-Sep-2026.) $)
    vonsmullem36 $p |- ( ph -> ( k e. X |-> ( 1 / ( W ` k ) ) ) = V ) $=
      ( c1 cv cfv cdiv co cmpt wcel wa crp ffvelcdmda rpreccld fvmpt2d oveq2d
      rpcnd rpne0d recrecd eqtrd mpteq2dva feqmptd eqtr4d ) ABEHBIZDJZKLZMBEUHC
      JZMCABEUJUKAUHENOZUJHHUKKLZKLUKULUIUMHKABEUMDPGULUKAEPUHCFQZRSTULUKULUKUN
      UAULUKUNUBUCUDUEABEPCFUFUG $.
  $}

  ${
    $d S u y $.  $d V k $.  $d V u y $.  $d W k $.  $d W u y $.  $d X k $.
    $d X u y $.  $d k ph $.
    vonsmullem37.x $e |- ( ph -> X e. _V ) $.
    vonsmullem37.v $e |- ( ph -> V : X --> RR+ ) $.
    vonsmullem37.s $e |- ( ph -> S C_ ( RR ^m X ) ) $.
    vonsmullem37.w $e |- ( ph -> W = ( k e. X |-> ( 1 / ( V ` k ) ) ) ) $.
    $( Lemma for ~ vonsmul : scaling and then scaling back by the pointwise
       reciprocal gives the set, the other way round.  (Contributed by Xander
       Mackay and Claude, 16-Sep-2026.) $)
    vonsmullem37 $p |- ( ph -> { u e. ( RR ^m X ) | ( u oF / V ) e. { y e. ( RR
      ^m X ) | ( y oF / W ) e. S } } = S )
                     $=
      ( c1 cv cfv cdiv co crp wcel wa rpreccld fmpt3d vonsmullem36 vonsmullem30
      ffvelcdmda cmpt eqcomd ) ABCDEGFHIAEHMENZFOZPQRGLAUHHSTUIAHRUHFJUEUAUBKAE
      HMUHGOPQUFFAEFGHJLUCUGUD $.
  $}

  ${
    $d C c f i j k m n y z $.  $d S f i j k m n y z $.
    $d X c f i j k m n y z $.  $d f i j k m n ph y z $.
    ovnsmul.x $e |- ( ph -> X e. Fin ) $.
    ovnsmul.c $e |- ( ph -> C e. RR+ ) $.
    ovnsmul.s $e |- ( ph -> S C_ ( RR ^m X ) ) $.
    $( The Lebesgue outer measure of a scaling of a subset of the space of
       multidimensional real numbers is the scale factor raised to the
       dimension, times the outer measure of the set.  (Contributed by Xander
       Mackay and Claude, 16-Sep-2026.) $)
    ovnsmul $p |- ( ph -> ( ( voln* ` X ) ` { y e. ( RR ^m X ) | ( y oF / ( X
      X. { C } ) ) e. S } ) = ( ( C ^ ( # ` X ) ) *e ( ( voln* ` X ) ` S ) ) )
                $=
      ( vj vk vz vn vm cfv co wceq cc0 cn cv cxmu vi vf vc chash cexp cico ccom
      c0 cixp ciun wss cvol cprod cmpt csumge0 wa cr cxp cmap wrex cxr crab clt
      cinf cif csn cdiv cof wcel covoln ovif2 cfn cn0 hashcl syl nn0zd rpexpcld
      rpxrd xmul01 c1 eqidd crp fconst6g fveq2 oveq2d cbvmptv eqid vonsmullem33
      wf a1i ifeq12d eqtrid ovnval2 ssrab2 3eqtr4rd ) ACEUDNZUEOZEUHPZQDIRJEJSZ
      UFISUASNUGNZUIUJUKKSZIREWTULNJUMUNUONPUPUAUQUQUREUSORUSOZUTKVAVBZVAVCVDZV
      EZTOZWRQBSECVFURZVGVHODVIZBUQEUSOZVBZLRMEMSUFLSUBSNUGNZUIUJUKXALREXKULNMU
      MUNUONPUPUBXBUTKVAVBZVAVCVDZVEZWQDEVJNZNZTOXJXONAXFWRWQQTOZWQXDTOZVEXNWRW
      QQXDTVKAWRXQQXRXMAWQVAVIXQQPAWQACWPGAWPAEVLVIWPVMVIFEVNVOVPVQVRWQVSVOABKC
      DUBUAIJMLXCXLXGUCEVTUCSZXGNZVGOZUNZEFGAXGWAACWBVIEWBXGWIGECWBWCVOHYBJEVTW
      SXGNZVGOZUNPAUCJEYAYDXSWSPXTYCVTVGXSWSXGWDWEWFWJXCWGZXLWGZWHWKWLAXPXEWQTA
      KDUAIJXCEFHYEWMWEAKXJUBLMXLEFXJXIUKAXHBXIWNWJYFWMWO $.
  $}

  ${
    $d A a t $.  $d A t y $.  $d C k $.  $d C t y $.  $d S a $.  $d S y $.
    $d W a t $.  $d W k $.  $d W t y $.  $d X a t $.  $d X k $.  $d X t y $.
    $d k ph $.  $d ph y $.
    vonsmullem38.x $e |- ( ph -> X e. Fin ) $.
    vonsmullem38.c $e |- ( ph -> C e. RR+ ) $.
    vonsmullem38.s $e |- ( ph -> S C_ ( RR ^m X ) ) $.
    vonsmullem38.w $e |- ( ph -> W = ( k e. X |-> ( 1 / ( ( X X. { C } ) ` k )
      ) ) )
                       $.
    vonsmullem38.r $e |- ( ph -> A. a e. ~P ( RR ^m X ) ( ( ( voln* ` X ) ` ( a
      i^i S ) ) +e ( ( voln* ` X ) ` ( a \ S ) ) ) = ( ( voln* ` X ) ` a ) )
                       $.
    vonsmullem38.a $e |- ( ph -> A e. ~P ( RR ^m X ) ) $.
    $( Lemma for ~ vonsmul : the Caratheodory splitting equation for the
       scaling of a measurable set, obtained from the splitting equation for
       the set itself.  (Contributed by Xander Mackay and Claude,
       16-Sep-2026.) $)
    vonsmullem38 $p |- ( ph -> ( ( ( voln* ` X ) ` ( A i^i { y e. ( RR ^m X ) |
      ( y oF / ( X X. { C } ) ) e. S } ) ) +e ( ( voln* ` X ) ` ( A \ { y e. (
      RR ^m X ) | ( y oF / ( X X. { C } ) ) e. S } ) ) ) = ( ( voln* ` X ) ` A
      ) )
                     $=
      ( vt co wcel cfv cxad cv csn cxp cdiv cof cmap crab cin covoln cdif chash
      cr cexp ofdivpreimin cfn elexd crp wf fconst6g elpwid vonsmullem37 ineq1d
      syl eqtrid fveq2d ssinss2d ovnsmul eqtr3d ofdivpreimdif difeq1d wss
      ssrab2 cxmu a1i ssdifssd oveq12d cxr wceq cn0 hashcl nn0zd rpexpcld rpred
      xadddi ovnxrcl syl3anc cpw ineq1 difeq1 fveq2 eqeq12d rabex elpwd rspcdva
      oveq2d cvv ovex 3eqtr2d ) ACBUAHDUBUCZUDUEZQZERBULHUFQZUGZUHZHUISZSZCXCUJ
      ZXESZTQZDHUKSZUMQZPUAGWTQCRZPXBUGZXESZVMQZXAXMRBXBUGZXESCXESAXIXKXMEUHZXE
      SZVMQZXKXMEUJZXESZVMQZTQZXKXRYATQZVMQZXOAXFXSXHYBTAXAXQRBXBUGZXESXFXSAYFX
      DXEAYFXPXCUHXDBXMEWSHUNAXPCXCAPBCFWSGHAHUOJUPADUQRHUQWSURKHDUQUSVCACXBOUT
      MVAZVBVDVEABDXQHJKAXMEXBLVFZVGVHAXAXTRBXBUGZXESXHYBAYIXGXEAYIXPXCUJXGBXME
      WSHVIAXPCXCYGVJVDVEABDXTHJKAXMXBEXMXBVKAXLPXBVLVNZVOZVGVHVPAXKULRXRVQRYAV
      QRYEYCVRAXKADXJKAXJAHUORXJVSRJHVTVCWAWBWCAXQHJYHWEAXTHJYKWEXKXRYAWDWFAYDX
      NXKVMAIUAZEUHZXESZYLEUJZXESZTQZYLXESZVRYDXNVRIXBWGXMYLXMVRZYQYDYRXNYSYNXR
      YPYATYSYMXQXEYLXMEWHVEYSYOXTXEYLXMEWIVEVPYLXMXEWJWKNAXMXBWPXMWPRAXLPXBULH
      UFWQWLVNYJWMWNWOWRABDXMHJKYJVGAXPCXEYGVEWR $.
  $}

  ${
    $d C a b $.  $d C b c $.  $d C a k $.  $d C a y $.  $d S a b $.
    $d S a y $.  $d X a b $.  $d X b c $.  $d X a k $.  $d X a y $.
    $d a k ph $.  $d c k $.  $d c y $.  $d ph y $.
    vonsmullem39.x $e |- ( ph -> X e. Fin ) $.
    vonsmullem39.c $e |- ( ph -> C e. RR+ ) $.
    vonsmullem39.s $e |- ( ph -> S e. dom ( voln ` X ) ) $.
    $( Lemma for ~ vonsmul : the scaling of a Lebesgue measurable set is
       Lebesgue measurable.  (Contributed by Xander Mackay and Claude,
       16-Sep-2026.) $)
    vonsmullem39 $p |- ( ph -> { y e. ( RR ^m X ) | ( y oF / ( X X. { C } ) )
      e. S } e. dom ( voln ` X ) )
                     $=
      ( va vk vc vb cv cdiv co wcel cfv wceq c1 adantr csn cxp cof cr cmap crab
      cdm wss cin covoln cdif cxad cpw wral ssrab2 a1i wa cmpt cfn crp isvonmbl
      cvoln mpbid simpld oveq2d cbvmptv simprd vonsmullem38 ralrimiva mpbir2and
      fveq2 simpr ) ABMECUAUBZNUCODPZBUDEUEOZUFZEVBQUGZPVPVOUHZIMZVPUIEUJQZQVSV
      PUKVTQULOVSVTQRZIVOUMZUNVRAVNBVOUOUPAWAIWBAVSWBPZUQZBVSCDJKESKMZVMQZNOZUR
      ZELAEUSPWCFTACUTPWCGTADVOUHZWCAWILMZDUIVTQWJDUKVTQULOWJVTQRLWBUNZADVQPWIW
      KUQHADELFVAVCZVDTWHJESJMZVMQZNOZURRWDKJEWGWOWEWMRWFWNSNWEWMVMVKVEVFUPAWKW
      CAWIWKWLVGTAWCVLVHVIAVPEIFVAVJ $.
  $}

  ${
    $d C y $.  $d S y $.  $d X y $.  $d ph y $.
    vonsmul.x $e |- ( ph -> X e. Fin ) $.
    vonsmul.c $e |- ( ph -> C e. RR+ ) $.
    vonsmul.s $e |- ( ph -> S e. dom ( voln ` X ) ) $.
    $( The Lebesgue measure of a scaling of a measurable subset of the space of
       multidimensional real numbers is the scale factor raised to the
       dimension, times the measure of the set.  (Contributed by Xander Mackay
       and Claude, 16-Sep-2026.) $)
    vonsmul $p |- ( ph -> ( ( voln ` X ) ` { y e. ( RR ^m X ) | ( y oF / ( X X.
      { C } ) ) e. S } ) = ( ( C ^ ( # ` X ) ) *e ( ( voln ` X ) ` S ) ) )
                $=
      ( cv csn cxp cdiv cof co wcel cr cmap cfv cxmu mblvon crab chash cexp cdm
      covoln cvoln vonmblss sseldd elpwid ovnsmul vonsmullem39 oveq2d 3eqtr4d
      cpw ) ABIECJKLMNDOBPEQNZUAZEUERZRCEUBRUCNZDUQRZSNUPEUFRZRURDUTRZSNABCDEFG
      ADUOAUTUDUOUNDAEFUGHUHUIUJAUPEFABCDEFGHUKTAVAUSURSADEFHTULUM $.
  $}

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Lebesgue measure adds over the integer translates of the unit cube
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    $d X k $.  $d k ph $.
    vonziunlem1.x $e |- ( ph -> X e. Fin ) $.
    $( Lemma for ~ vonziun : the half-open unit cube is Lebesgue measurable.
       (Contributed by Xander Mackay and Claude, 16-Sep-2026.) $)
    vonziunlem1 $p |- ( ph -> X_ k e. X ( 0 [,) 1 ) e. dom ( voln ` X ) ) $=
      ( cc0 csn cxp cfv c1 cico co cixp wcel wceq 0re fvconst2g mpan adantl 1re
      cr cv cvoln cdm wa oveq12d ixpeq2dva eqid wf fconst6 a1i hoimbl eqeltrrd
      ) ABCBUAZCEFGZHZUMCIFGZHZJKZLBCEIJKZLCUBHUCZABCURUSAUMCMZUDUOEUQIJVAUOENZ
      AETMVAVBOCEUMTPQRVAUQINZAITMVAVCSCIUMTPQRUEUFAUNUPUTBCDUTUGCTUNUHACETOUIU
      JCTUPUHACITSUIUJUKUL $.
  $}

  ${
    $d V y $.  $d X k y $.  $d k ph y $.
    vonziunlem2.x $e |- ( ph -> X e. Fin ) $.
    vonziunlem2.v $e |- ( ph -> V : X --> RR ) $.
    $( Lemma for ~ vonziun : the translate of a measurable set by a fixed real
       function is measurable, applied to the half-open unit cube itself: the
       set of points whose distance from ` V ` lands in the cube is measurable.
       (Contributed by Xander Mackay and Claude, 18-Sep-2026.) $)
    vonziunlem2 $p |- ( ph -> { y e. ( RR ^m X ) | ( y oF - V ) e. X_ k e. X (
      0 [,) 1 ) } e. dom ( voln ` X ) )
                    $=
      ( cc0 c1 cico co cixp vonziunlem1 vontranslem29 ) ABCEHIJKLDEFGACEFMN $.
  $}

  ${
    $d X k $.  $d k ph $.  $d k y $.
    vonziunlem3.x $e |- ( ph -> X e. Fin ) $.
    $( Lemma for ~ vonziun : the pointwise negated floor of a function
       ` y : X --> RR ` is an integer-valued function on ` X ` .  (Contributed
       by Xander Mackay and Claude, 18-Sep-2026.) $)
    vonziunlem3 $p |- ( ( ph /\ y e. ( RR ^m X ) ) -> ( k e. X |-> -u ( |_ ` (
      y ` k ) ) ) e. ( ZZ ^m X ) )
                    $=
      ( cv cr cmap co wcel wa cz cfv cfl cneg cmpt cvv cfn zex a1i adantr flcld
      wf elmapi adantl ffvelcdmda znegcld fmpttd elmapdd ) ABFZGDHIJZKZLDCDCFZU
      JMZNMZOZPQRLQJULSTADRJUKEUAULCDUPLULUMDJKZUOUQUNULDGUMUJUKDGUJUCAUJGDUDUE
      UFUBUGUHUI $.
  $}

  ${
    $d X j k $.  $d j k ph $.  $d j k y $.
    vonziunlem4.x $e |- ( ph -> X e. Fin ) $.
    $( Lemma for ~ vonziun : the floor argument.  Translating ` y ` by the
       pointwise negated floor of ` y ` puts the result in the half-open unit
       cube, coordinatewise via ~ fracge0 and ~ fraclt1 .  (Contributed by
       Xander Mackay and Claude, 18-Sep-2026.) $)
    vonziunlem4 $p |- ( ( ph /\ y e. ( RR ^m X ) ) -> ( y oF + ( k e. X |-> -u
      ( |_ ` ( y ` k ) ) ) ) e. X_ j e. X ( 0 [,) 1 ) )
                    $=
      ( cv cr co wcel cfv cfl caddc cvv wfn cc0 c1 syl cz adantr cmap cneg cmpt
      wa cof cico wral cixp ovexd simpr elmapi ffnd vonziunlem3 cfn elexd inidm
      wf offn cxr 0xr a1i 1xr cmin wceq fnfvof syl22anc 2fveq3 ffvelcdmda flcld
      eqid negeqd znegcld fvmptd3 oveq2d recnd zcnd negsubd 3eqtrd zred eqeltrd
      resubcld rexrd cle wbr fracge0 breqtrrd clt fraclt1 eqbrtrd elicod elixp2
      ralrimiva syl3anbrc ) ABGZHEUAIJZUDZWNDEDGZWNKLKZUBZUCZMUEZIZNJXBEOCGZXBK
      ZPQUFIZJZCEUGXBCEXEUHJWPWNWTXAUIWPEEMEWNWTNNWPEHWNWPWOEHWNUQAWOUJWNHEUKRZ
      ULZWPESWTWPWTSEUAIJESWTUQABDEFUMWTSEUKRULZWPEUNAEUNJWOFTUOZXJEUPURWPXFCEW
      PXCEJZUDZPQXDPUSJXLUTVAQUSJXLVBVAXLXDXLXDXCWNKZXMLKZVCIZHXLXDXMXCWTKZMIZX
      MXNUBZMIXOXLWNEOZWTEOZENJZXKXDXQVDWPXSXKXHTWPXTXKXITWPYAXKXJTWPXKUJZEMWNW
      TNXCVEVFXLXPXRXMMXLDXCWSXREWTSWTVJWQXCVDWRXNWQXCLWNVGVKYBXLXNXLXMWPEHXCWN
      XGVHZVIZVLVMVNXLXMXNXLXMYCVOXLXNYDVPVQVRZXLXMXNYCXLXNYDVSWAVTWBXLPXOXDWCX
      LXMHJZPXOWCWDYCXMWERYEWFXLXDXOQWGYEXLYFXOQWGWDYCXMWHRWIWJWLCEXEXBWKWM $.
  $}

  ${
    $d X j $.  $d Y j $.  $d Z j $.
    ofziundisjlem1.x $e |- ( ph -> X e. Fin ) $.
    ofziundisjlem1.y $e |- ( ph -> Y e. ( RR ^m X ) ) $.
    ofziundisjlem1.z $e |- ( ph -> Z e. ( ZZ ^m X ) ) $.
    ofziundisjlem1.q $e |- ( ph -> ( Y oF + Z ) e. X_ j e. X ( 0 [,) 1 ) ) $.
    $( Lemma for ~ ofziundisj : if translating a real point by an
       integer-valued function lands it in the half-open unit cube, that
       integer function is determined coordinatewise as the pointwise negated
       floor of the point.  (Contributed by Xander Mackay and Claude,
       18-Sep-2026.) $)
    ofziundisjlem1 $p |- ( ( ph /\ j e. X ) -> ( |_ ` ( Y ` j ) ) = -u ( Z ` j
                    ) )
                    $=
      ( wcel cfv cle wbr c1 caddc co clt cc0 cr cz cv cfl cneg wceq cmin df-neg
      wa cof cico w3a wral cvv wfn cixp adantr elixp2 sylib simp3d sylancom cxr
      rspa wb 0re 1xr elico2 mp2an simp2d cmap elmapi syl ffnd cfn elexd fnfvof
      wf simpr syl22anc breqtrd ffvelcdmda zred lesubaddd mpbird eqbrtrid recnd
      a1i zcnd subnegd eqbrtrrd eqbrtrd renegcld 1red ltsubadd2d mpbid jca flbi
      znegcld syl2anc ) ABUAZCJZUGZWRDKZUBKWREKZUCZUDZXCXALMZXAXCNOPQMZUGZWTXEX
      FWTXCRXBUEPZXALXBUFWTXHXALMRXAXBOPZLMWTRWRDEOUHPZKZXILWTXKSJZRXKLMZXKNQMZ
      WTXKRNUIPZJZXLXMXNUJZAWSXPBCUKZXPWTXJULJZXJCUMZXRWTXJBCXOUNJZXSXTXRUJAYAW
      SIUOBCXOXJUPUQURXPBCVAUSRSJZNUTJXPXQVBVCVDRNXKVEVFUQZVGWTDCUMZECUMZCULJZW
      SXKXIUDAYDWSACSDADSCVHPJCSDVOGDSCVIVJZVKUOAYEWSACTEAETCVHPJCTEVOHETCVIVJZ
      VKUOAYFWSACVLFVMUOAWSVPCODEULWRVNVQZVRWTRXBXAYBWTVCWEWTXBACTWREYHVSZVTZAC
      SWRDYGVSZWAWBWCWTXAXCUEPZNQMXFWTYMXINQWTXAXBWTXAYLWDWTXBYJWFWGWTXKXINQYIW
      TXLXMXNYCURWHWIWTXAXCNYLWTXBYKWJWTWKWLWMWNWTXASJXCTJXDXGVBYLWTXBYJWPXAXCW
      OWQWB $.
  $}

  ${
    $d W j $.  $d X j $.  $d Y j $.  $d Z j $.  $d j ph $.
    ofziundisjlem2.x $e |- ( ph -> X e. Fin ) $.
    ofziundisjlem2.y $e |- ( ph -> Y e. ( RR ^m X ) ) $.
    ofziundisjlem2.z $e |- ( ph -> Z e. ( ZZ ^m X ) ) $.
    ofziundisjlem2.q $e |- ( ph -> ( Y oF + Z ) e. X_ j e. X ( 0 [,) 1 ) ) $.
    ofziundisjlem2.w $e |- ( ph -> W e. ( ZZ ^m X ) ) $.
    ofziundisjlem2.r $e |- ( ph -> ( Y oF + W ) e. X_ j e. X ( 0 [,) 1 ) ) $.
    $( Lemma for ~ ofziundisj : the integer translate landing a point in the
       half-open unit cube is unique.  (Contributed by Xander Mackay and
       Claude, 18-Sep-2026.) $)
    ofziundisjlem2 $p   |- ( ph -> Z = W ) $=
      ( cz wcel wf elmapi syl ffnd cfv ffvelcdmda cmap co cv cfl ofziundisjlem1
      wa zcnd cneg eqtr3d neg11d eqfnfvd ) ABDFCADMFAFMDUAUBZNDMFOIFMDPQZRADMCA
      CULNDMCOKCMDPQZRABUCZDNUFZUOFSZUOCSZUPUQADMUOFUMTUGUPURADMUOCUNTUGUPUOESU
      DSUQUHURUHABDEFGHIJUEABDECGHKLUEUIUJUK $.
  $}

  ${
    $d X j k u w y z $.  $d j ph u w z $.
    ofziundisj.x $e |- ( ph -> X e. Fin ) $.
    $( The integer-lattice translates of the half-open unit cube are pairwise
       disjoint.  (Contributed by Xander Mackay and Claude, 18-Sep-2026.) $)
    ofziundisj $p |- ( ph -> Disj_ z e. ( ZZ ^m X ) { y e. ( RR ^m X ) | ( y
      oF + z ) e. X_ k e. X ( 0 [,) 1 ) } )
                    $=
      ( vw vu vj weq cv co cixp wcel cmap crab wral wa ad2antrr eleq1d caddc c1
      cof cc0 cico cr cin c0 wceq wo cz wdisj wn simplr cfn oveq1 bilani simpld
      elrab adantr simplrl simprd eqidd cbvixpv eleqtrdi simplrr ofziundisjlem2
      mtand ralrimiva disj sylibr ex orrd ralrimivva oveq2 rabbidv disjor ) ACG
      JZBKZCKZUAUCZLZDEUDUBUELZMZNZBUFEOLZPZVSGKZWALZWDNZBWFPZUGUHUIZUJZGUKEOLZ
      QCWNQCWNWGULAWMCGWNWNAVTWNNZWHWNNZRZRZVRWLWRVRUMZWLWRWSRZHKZWKNZUMZHWGQWL
      WTXCHWGWTXAWGNZRZXBVRWRWSXDUNXEXBRZIWHEXAVTWTEUONZXDXBAXGWQWSFSSXEXAWFNZX
      BXEXHXAVTWALZWDNZXDXHXJRWTWEXJBXAWFBHJZWBXIWDVSXAVTWAUPTUSUQZURUTWTWOXDXB
      AWOWPWSVASXFXIWDIEWCMZXEXJXBXEXHXJXLVBUTDIEWCWCDIJWCVCVDZVEWTWPXDXBAWOWPW
      SVFSXFXAWHWALZWDXMXFXHXOWDNZXBXHXPRXEWJXPBXAWFXKWIXOWDVSXAWHWAUPTUSUQVBXN
      VEVGVHVIHWGWKVJVKVLVMVNWNWGWKCGVRWEWJBWFVRWBWIWDVTWHVSWAVOTVPVQVK $.
  $}

  ${
    $d S a $.  $d S z $.  $d X a $.  $d X j k u $.  $d X k u y z $.
    $d j k ph u $.
    vonziunlem8.x $e |- ( ph -> X e. Fin ) $.
    vonziunlem8.s $e |- ( ph -> S e. dom ( voln ` X ) ) $.
    $( Lemma for ~ vonziun : a measurable set ` S ` is the disjoint union, over
       the integer lattice ` z ` , of its intersection with the pullback of the
       unit cube translated by ` z ` .  Every point of ` ( RR ^m X ) ` lands in
       some cube translate by ~ vonziunlem3 and ~ vonziunlem4 , so the
       translates cover ` ( RR ^m X ) ` and hence, met with ` S ` , cover ` S `
       itself.  (Contributed by Xander Mackay and Claude, 18-Sep-2026.) $)
    vonziunlem8 $p |- ( ph -> S = U_ z e. ( ZZ ^m X ) ( S i^i { y e. ( RR ^m X
      ) | ( y oF + z ) e. X_ k e. X ( 0 [,) 1 ) } ) )
                    $=
      ( va vu vj cmap co cin cv cixp wcel wss wceq cfv cr cz caddc cof cc0 cico
      c1 crab ciun covoln cdif cxad cpw wral cvoln cdm wa isvonmbl mpbid simpld
      dfss2 sylib cneg cmpt oveq2 eleq1d rabbidv eleq2d vonziunlem3 oveq1 simpr
      cfl vonziunlem4 eqidd cbvixpv eleqtrdi elrabd rspcedvdw eliund ssd ssrab2
      iunss a1i mprgbir eqssd ineq2d iunin2 eqtr4di eqtr3d ) ADUAFLMZNZDCUBFLMZ
      DBOZCOZUCUDZMZEFUEUGUFMZPZQZBWJUHZNUIZADWJRZWKDSAXBIOZDNFUJTZTXCDUKXDTULM
      XCXDTSIWJUMUNZADFUOTUPQXBXEUQHADFIGURUSUTDWJVAVBAWKDCWLWTUIZNXAAWJXFDAWJX
      FAJWJXFAJOZWJQZUQZCXGWLWTXIXGWTQXGWMEFEOZXGTVLTVCVDZWOMZWRQZBWJUHZQCXKWLW
      NXKSZWTXNXGXOWSXMBWJXOWPXLWRWNXKWMWOVEVFVGVHAJEFGVIXIXMXGXKWOMZWRQBXGWJWM
      XGSXLXPWRWMXGXKWOVJVFAXHVKXIXPKFWQPWRAJKEFGVMKEFWQWQKOXJSWQVNVOVPVQVRVSVT
      XFWJRZAXQWTWJRZCWLCWLWTWJWBXRWNWLQWSBWJWAWCWDWCWEWFCWLDWTWGWHWI $.
  $}

  ${
    vonziunlem9.x $e |- ( ph -> X e. Fin ) $.
    $( Lemma for ~ vonziun : the integer lattice ` ( ZZ ^m X ) ` is countable,
       since ` ZZ ` is countable and ` X ` is finite.  (Contributed by Xander
       Mackay and Claude, 18-Sep-2026.) $)
    vonziunlem9 $p |- ( ph -> ( ZZ ^m X ) ~<_ _om ) $=
      ( cz com cdom wbr zct a1i mpct ) ADBDEFGAHICJ $.
  $}

  ${
    $d X k n y $.  $d k n ph y $.  $d k n y z $.
    vonziunlem10.x $e |- ( ph -> X e. Fin ) $.
    vonziunlem10.s $e |- ( ph -> S e. dom ( voln ` X ) ) $.
    $( Lemma for ~ vonziun : each piece ` S i^i { y | ( y oF + z ) e. Q } ` ,
       the part of ` S ` landing in the cube translate at lattice point ` z ` ,
       is itself measurable.  The pullback set is measurable by ~ vonziunlem2 ,
       and ` dom ( voln `` X ) ` is a sigma-algebra, so meeting it with ` S `
       stays inside.  (Contributed by Xander Mackay and Claude,
       18-Sep-2026.) $)
    vonziunlem10 $p |- ( ( ph /\ z e. ( ZZ ^m X ) ) -> ( S i^i { y e. ( RR ^m X
      ) | ( y oF + z ) e. X_ k e. X ( 0 [,) 1 ) } ) e. dom ( voln ` X ) )
                     $=
      ( vn cv cz co wcel wa cfv caddc cr adantr cmin cvv cmap cvoln cdm cof cc0
      c1 cico cixp crab cfn eqid dmovnsal cneg cmpt wf elmapi adantl ffvelcdmda
      ffnd znegcld zred fmpttd elexd inidm offn recnd zcnd subnegd simpr fnfvof
      wceq syl22anc fveq2d negeqd fvmptd2 oveq2d eqtrd 3eqtr4d eqfnfvd rabbidva
      wfn eleq1d vonziunlem2 eqeltrrd salincld ) ACJZKFUALMZNZFUBOUCZDBJZWFPUDL
      ZEFUEUFUGLUHZMZBQFUALZUIZWHWIFAFUJMZWGGRZWIUKULADWIMWGHRWHWJIFIJZWFOZUMZU
      NZSUDLZWLMZBWNUIWOWIWHXCWMBWNWHWJWNMZNZXBWKWLXEEFXBWKXEFFSFWJXATTXEFQWJXD
      FQWJUOWHWJQFUPUQZUSZXEFQXAWHFQXAUOXDWHIFWTQWHWRFMNZWTXHWSWHFKWRWFWGFKWFUO
      ZAWFKFUPUQZURUTVAVBZRUSZXEFUJWHWPXDWQRVCZXMFVDZVEXEFFPFWJWFTTXGXEFKWFWHXI
      XDXJRZUSZXMXMXNVEXEEJZFMZNZXQWJOZXQWFOZUMZSLZXTYAPLZXQXBOZXQWKOZXSXTYAXSX
      TXEFQXQWJXFURVFXSYAXEFKXQWFXOURZVGVHXSYEXTXQXAOZSLZYCXSWJFWAZXAFWAZFTMZXR
      YEYIVKXEYJXRXGRZXEYKXRXLRXEYLXRXMRZXEXRVIZFSWJXATXQVJVLXSYHYBXTSXSIXQWTYB
      FXAKXAUKXSWRXQVKZNZWSYAYQWRXQWFXSYPVIVMVNYOXSYAYGUTVOVPVQXSYJWFFWAZYLXRYF
      YDVKYMXEYRXRXPRYNYOFPWJWFTXQVJVLVRVSWBVTWHBEXAFWQXKWCWDWE $.
  $}

  ${
    $d S z $.
    $d X k $.
    $d X y $.
    $d X z $.
    $d k ph $.
    $d k y $.
    $d k z $.
    $d ph y $.
    $d ph z $.
    $d y z $.
    vonziunlem11.x $e |- ( ph -> X e. Fin ) $.
    vonziunlem11.s $e |- ( ph -> S e. dom ( voln ` X ) ) $.
    $( Lemma for ~ vonziun : assembling ~ ofziundisj through ~ vonziunlem10
       via ~ meadjiun , the measure of ` S ` is the sum over the integer
       lattice of the measures of its pieces
       ` S i^i { y | ( y oF + z ) e. Q } ` .  The pieces are pairwise disjoint
       by ~ ofziundisj (extended to the intersected form), their union is
       ` S ` by ~ vonziunlem8 , the lattice is countable by ~ vonziunlem9 , and
       each piece is measurable by ~ vonziunlem10 .  (Contributed by Xander
       Mackay and Claude, 18-Sep-2026.) $)
    vonziunlem11 $p |- ( ph -> ( ( voln ` X ) ` S ) = ( sum^ ` ( z e. ( ZZ ^m X
      ) |-> ( ( voln ` X ) ` ( S i^i { y e. ( RR ^m X ) | ( y oF + z ) e. X_ k
      e. X ( 0 [,) 1 ) } ) ) ) ) )
                     $=
      ( cvoln cfv cz cmap co cv caddc cof cc0 c1 wcel wdisj cico cixp crab ciun
      cr cin csumge0 vonziunlem8 fveq2d cdm nfv vonmea vonziunlem10 vonziunlem9
      cmpt eqid ofziundisj wss wi disjss2 inss2 a1i mprg syl meadjiun eqtrd )
      ADFIJZJCKFLMZDBNCNZOPMEFQRUAMUBSBUEFLMUCZUFZUDZVGJCVHVKVGJUOUGJADVLVGABCD
      EFGHUHUIAVHVKVGUJZCVGACUKAFGULVMUPABCDEFGHUMAFGUNACVHVJTZCVHVKTZABCEFGUQV
      KVJURZVNVOUSCVHCVHVKVJUTVPVIVHSDVJVAVBVCVDVEVF $.
  $}

  ${
    $d W k t y $.  $d X k t y $.  $d k ph t y $.  $d k t y z $.
    vonziunlem12.x $e |- ( ph -> X e. Fin ) $.
    vonziunlem12.w $e |- ( ph -> W = ( k e. X |-> -u ( z ` k ) ) ) $.
    $( Lemma for ~ vonziun : the translate of the intersection of a piece with
       the shifted cube equals the intersection of the piece's own translate
       with the cube.  (Contributed by Xander Mackay and Claude,
       18-Sep-2026.) $)
    vonziunlem12 $p |- ( ( ph /\ z e. ( ZZ ^m X ) ) -> { t e. ( RR ^m X ) | ( t
      oF - z ) e. ( S i^i { y e. ( RR ^m X ) | ( y oF + z ) e. X_ k e. X ( 0
      [,) 1 ) } ) } = ( { t e. ( RR ^m X ) | ( t oF - z ) e. S } i^i X_ k e. X
      ( 0 [,) 1 ) ) )
                     $=
      ( cv cz co wcel cc0 c1 cr crab adantr cvv cmap wa cmin cof caddc cico cin
      cixp wceq cfn elexd wf elmapi adantl wss zssre a1i fssd cfv ofsubneg
      cneg cmpt eleq1d rabbidva eqcomd ineq2d eleq2d ofsubpreimin eqtrdi ovexd
      ixpconstg syl2anc reex cxr 0re icossre mp2an mapss eqsstrdi vontranslem27
      1xr eqtrd ) ACKZLHUAMNZUBZDKZWCUCUDZMZEBKZWCUEUDMZFHOPUFMZUHZNZBQHUAMZRZU
      GZNZDWNRZWHENDWNRZWHWIGWGMZWLNZBWNRZNDWNRZUGZWSWLUGWEWRWHEXBUGZNZDWNRXDWE
      WQXFDWNWEWFWNNZUBWPXEWHWEWPXEUIXGWEWOXBEWEXBWOWEXAWMBWNWEWIWNNZUBZWTWJWLX
      IWIFWCGHXIHUJWEHUJNZXHAXJWDISZSUKXHHQWIULWEWIQHUMUNWEHQWCULXHWEHLQWCWDHLW
      CULAWCLHUMUNLQUOWEUPUQURZSWEGFHFKWCUSVAVBUIZXHAXMWDJSZSUTVCVDVEVFSVGVDDEX
      BWCHVHVIWEXCWLWSWEBDWLFWCGHWEHUJXKUKZXLWEWLWKHUAMZWNWEHTNWKTNWLXPUIXOWEOP
      UFVJFHWKTTVKVLQTNWKQUOZXPWNUOVMOQNPVNNXQVOWAOPVPVQWKQHTVRVQVSXNVTVFWB $.
  $}

  ${
    $d S t y $.  $d W k t y $.  $d X k t u y $.  $d k ph t y $.
    $d k t u y z $.
    vonziunlem13.x $e |- ( ph -> X e. Fin ) $.
    vonziunlem13.s $e |- ( ph -> S e. dom ( voln ` X ) ) $.
    vonziunlem13.w $e |- ( ph -> W = ( k e. X |-> -u ( z ` k ) ) ) $.
    $( Lemma for ~ vonziun : the piece's Lebesgue measure is unchanged by
       trading its translate by ` z ` for the equivalent,
       translate-of-the-cube-by-negative-z form.  (Contributed by Xander Mackay
       and Claude, 18-Sep-2026.) $)
    vonziunlem13 $p |- ( ( ph /\ z e. ( ZZ ^m X ) ) -> ( ( voln ` X ) ` ( S i^i
      { y e. ( RR ^m X ) | ( y oF + z ) e. X_ k e. X ( 0 [,) 1 ) } ) ) = ( (
      voln ` X ) ` ( { y e. ( RR ^m X ) | ( y oF - z ) e. S } i^i X_ k e. X ( 0
      [,) 1 ) ) ) )
                     $=
      ( vu vt cv cz co wcel cr crab cin cfv cmap wa cmin cof caddc c1 cico cixp
      cc0 cvoln cfn adantr wf elmapi adantl wss zssre a1i fssd cdm oveq1 eleq1d
      wceq cbvrabv ineq2i vonziunlem10 eqeltrrid vontrans rabbidva vonziunlem12
      eleq2d eqtr3d ineq1i 3eqtr3g fveq2d eqcomd 3eqtr3rd ) ACMZNGUAOPZUBZBMZVR
      UCUDZOZDKMZVRUEUDZOZEGUIUFUGOUHZPZKQGUAOZRZSZPZBWIRZGUJTZTWKWNTWCDPZBWIRZ
      WGSZWNTDWAVRWEOZWGPZBWIRZSZWNTVTBWKVRGAGUKPVSHULVTGNQVRVSGNVRUMAVRNGUNUON
      QUPVTUQURUSVTWKXAWNUTWTWJDWSWHBKWIWAWDVCWRWFWGWAWDVRWEVAVBVDVEZABCDEGHIVF
      VGVHVTWMWQWNVTLMZVRWBOZWKPZLWIRZXDDPZLWIRZWGSZWMWQVTXDXAPZLWIRXFXIVTXJXEL
      WIVTXCWIPUBZXAWKXDXAWKVCZXKXBURVKVIABCLDEFGHJVJVLXEWLLBWIXCWAVCZXDWCWKXCW
      AVRWBVAZVBVDXHWPWGXGWOLBWIXMXDWCDXNVBVDVMVNVOVTWKXAWNVTXAWKXLVTXBURVPVOVQ
      $.
  $}

  ${
    $d S y z $.  $d X j k y z $.  $d k ph y z $.
    vonziun.x $e |- ( ph -> X e. Fin ) $.
    vonziun.s $e |- ( ph -> S e. dom ( voln ` X ) ) $.
    $( The Lebesgue measure of a measurable subset of the space of
       multidimensional real numbers is the sum, over the integer lattice, of
       the measures of the lattice translates of the set met with the unit
       cube.  This is the countable additivity half of Blichfeldt's lemma: the
       integer translates of the half-open unit cube ` X_ k e. X ( 0 [,) 1 ) `
       partition ` ( RR ^m X ) ` , so ` S ` is the disjoint union of its pieces
       in them, and ~ vontrans carries each piece back into the cube without
       changing its measure.  (Contributed by Xander Mackay and Claude,
       18-Sep-2026.) $)
    vonziun $p |- ( ph -> ( ( voln ` X ) ` S ) = ( sum^ ` ( z e. ( ZZ ^m X )
      |-> ( ( voln ` X ) ` ( { y e. ( RR ^m X ) | ( y oF - z ) e. S } i^i X_ k
      e. X ( 0 [,) 1 ) ) ) ) ) )
                $=
      ( vj cfv cmap co cv cof wcel crab cin cmpt csumge0 cneg cvoln cz caddc c1
      cc0 cico cixp cr cmin vonziunlem11 wceq fveq2 negeqd cbvmptv vonziunlem13
      a1i mpteq2dva fveq2d eqtrd ) ADFUAJZJCUBFKLZDBMZCMZUCNLEFUEUDUFLUGZOBUHFK
      LZPQUTJZRZSJCVAVBVCUINLDOBVEPVDQUTJZRZSJABCDEFGHUJAVGVISACVAVFVHABCDEIFIM
      ZVCJZTZRZFGHVMEFEMZVCJZTZRUKAIEFVLVPVJVNUKVKVOVJVNVCULUMUNUPUOUQURUS $.
  $}

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Blichfeldt's lemma
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    $d X a b k x $.  $d a b k ph x $.
    blichfeldtlem1.x $e |- ( ph -> X e. Fin ) $.
    blichfeldtlem1.n $e |- ( ph -> X =/= (/) ) $.
    $( Lemma for ~ blichfeldt : the unit cube ` X_ k e. X ( 0 [,) 1 ) ` has
       Lebesgue measure ` 1 ` , computed as ` ( X X. { 0 } ) ` to
       ` ( X X. { 1 } ) ` via ~ vonhoi and ~ hoidmvn0val , each coordinate's
       edge measure being ` 1 ` by ~ volico and its factors multiplying to
       ` 1 ` by ~ prod1 .  (Contributed by Xander Mackay and Claude,
       18-Sep-2026.) $)
    blichfeldtlem1 $p |- ( ph -> ( ( voln ` X ) ` X_ k e. X ( 0 [,) 1 ) ) = 1 )
                       $=
      ( vx va vb cc0 c1 cico co cfv cv cvol cprod cr wceq wcel eqtrd cixp cvoln
      csn cxp cfn cmap c0 cif cmpo cmpt 0re fvconst2g mpan adantl 1re ixpeq2dva
      wa oveq12d eqcomd fveq2d fconst6 a1i eqid vonhoi hoidmvn0val clt wbr cmin
      wf volico mp2an 0lt1 iftruei 1m0e1 3eqtri eqtrdi prodeq2dv cuz olcd prod1
      wss wo syl ) ABCIJKLZUAZCUBMZMZCBNZCIUCUDZMZWHCJUCUDZMZKLZOMZBPZJAWGWIWKC
      FUEGHQFNZUFLZWQWPUGRIWPWHGNMWHHNMKLOMBPUHUIUJZMLZWOAWGBCWMUAZWFMWSAWEWTWF
      AWTWEABCWMWDAWHCSZUQZWJIWLJKXAWJIRZAIQSZXAXCUKCIWHQULUMUNXAWLJRZAJQSZXAXE
      UOCJWHQULUMUNURZUPUSUTAFWIWKBWTWRCGHDCQWIVIACIQUKVAVBZCQWKVIACJQUOVAVBZWT
      VCWRVCZVDTAFWIWKBWRCGHXJDEXHXIVETAWOCJBPZJACWNJBXBWNWDOMZJXBWMWDOXGUTXLIJ
      VFVGZJIVHLZIUHZXNJXDXFXLXORUKUOIJVJVKXMXNIVLVMVNVOVPVQACCVRMWAZCUESZWBXKJ
      RAXQXPDVSCBCVTWCTT $.
  $}

  ${
    $d S y $.  $d X k $.  $d X y $.  $d k ph $.  $d ph y $.  $d y z $.
    blichfeldtlem2.x $e |- ( ph -> X e. Fin ) $.
    blichfeldtlem2.s $e |- ( ph -> S e. dom ( voln ` X ) ) $.
    blichfeldtlem2.z $e |- ( ph -> z e. ( ZZ ^m X ) ) $.
    $( Lemma for ~ blichfeldt : each piece for lattice point ` z ` , the
       pullback under translation by the negation of ` z ` of the fixed
       measurable set ` S ` intersected with the unit cube, is itself
       measurable, by ~ vontranslem29 for the translated piece and
       ~ vonziunlem1 for the cube, met inside the sigma-algebra
       ` dom ( voln `` X ) ` via ~ salincl .  (Contributed by Xander Mackay and
       Claude, 18-Sep-2026.) $)
    blichfeldtlem2 $p |- ( ph -> ( { y e. ( RR ^m X ) | ( y oF - z ) e. S } i^i
      X_ k e. X ( 0 [,) 1 ) ) e. dom ( voln ` X ) )
                       $=
      ( cvoln cfv cdm cv cmin cof co wcel cr cmap cz crab cc0 c1 cico cixp eqid
      dmovnsal elmapi syl wss zssre a1i fssd vontranslem29 vonziunlem1 salincld
      wf ) AFJKLZBMCMZNOPDQBRFSPUAEFUBUCUDPUEAURFGURUFUGABDUSFGAFTRUSAUSTFSPQFT
      USUQIUSTFUHUITRUJAUKULUMHUNAEFGUOUP $.
  $}

  ${
    $d X k $.  $d k ph $.  $d k u $.  $d k w $.  $d k z $.
    ofblichfdisjlem1.x $e |- ( ph -> X e. Fin ) $.
    ofblichfdisjlem1.z $e |- ( ph -> z e. ( ZZ ^m X ) ) $.
    ofblichfdisjlem1.w $e |- ( ph -> w e. ( ZZ ^m X ) ) $.
    ofblichfdisjlem1.u $e |- ( ph -> u e. ( RR ^m X ) ) $.
    $( Lemma for ~ ofblichfdisj : the pointwise difference of two
       lattice-translate differences of a common point collapses to the
       difference of the lattice points themselves.  (Contributed by Xander
       Mackay and Claude, 18-Sep-2026.) $)
    ofblichfdisjlem1 $p |- ( ph -> ( k e. X |-> ( ( ( u oF - z ) ` k ) - ( ( u
      oF
      - w ) ` k ) ) ) = ( w oF - z ) )
                       $=
      ( cv cmin co cfv wcel cr cfn wf elmapi cz cof cmpt wa cmap syl ffvelcdmda
      wss zssre a1i feqmptd offval2 resubcld fvmpt2d oveq12d nnncan1d mpteq2dva
      fssd recnd eqtrd eqtr4d ) AEFEKZDKZBKZLUAZMZNZVAVBCKZVDMZNZLMZUBEFVAVGNZV
      AVCNZLMZUBVGVCVDMAEFVJVMAVAFOUCZVJVAVBNZVLLMZVOVKLMZLMVMVNVFVPVIVQLAEFVPV
      EPAEFVOVLLVBVCQPPGAFPVAVBAVBPFUDMOFPVBRJVBPFSUEZUFZAFPVAVCAFTPVCAVCTFUDMZ
      OFTVCRHVCTFSUEZTPUGAUHUIZUQUFZAEFPVBVRUJZAEFTVCWAUJZUKVNVOVLVSWCULUMAEFVQ
      VHPAEFVOVKLVBVGQPPGVSAFPVAVGAFTPVGAVGVTOFTVGRIVGTFSUEZWBUQUFZWDAEFTVGWFUJ
      ZUKVNVOVKVSWGULUMUNVNVOVLVKVNVOVSURVNVLWCURVNVKWGURUOUSUPAEFVKVLLVGVCQPPG
      WGWCWHWEUKUT $.
  $}

  ${
    $d X k $.  $d k ph $.  $d k w $.  $d k z $.
    ofblichfdisjlem2.x $e |- ( ph -> X e. Fin ) $.
    ofblichfdisjlem2.z $e |- ( ph -> z e. ( ZZ ^m X ) ) $.
    ofblichfdisjlem2.w $e |- ( ph -> w e. ( ZZ ^m X ) ) $.
    $( Lemma for ~ ofblichfdisj : the pointwise difference of two integer
       lattice points is again an integer lattice point.  (Contributed by
       Xander Mackay and Claude, 18-Sep-2026.) $)
    ofblichfdisjlem2 $p |- ( ph -> ( w oF - z ) e. ( ZZ ^m X ) ) $=
      ( vk cv cmin co cfv cz cfn wcel wf elmapi syl ffvelcdmda feqmptd cof cmpt
      cmap offval2 cvv zex a1i wa zsubcld fmpttd elmapdd eqeltrd ) ACIZBIZJUAKH
      DHIZUMLZUOUNLZJKZUBZMDUCKZAHDUPUQJUMUNNMMEADMUOUMAUMUTODMUMPGUMMDQRZSZADM
      UOUNAUNUTODMUNPFUNMDQRZSZAHDMUMVATAHDMUNVCTUDAMDUSUENMUEOAUFUGEAHDURMAUOD
      OUHUPUQVBVDUIUJUKUL $.
  $}

  ${
    $d S s t $.  $d S y $.  $d X k s t $.  $d X y $.  $d k ph $.  $d k s t u $.
    $d k t w $.  $d k s t z $.  $d u y $.  $d w y $.  $d y z $.
    ofblichfdisjlem3.x $e |- ( ph -> X e. Fin ) $.
    ofblichfdisjlem3.d $e |- ( ph -> A. s e. S A. t e. S ( ( k e. X |-> ( ( s `
      k
      ) - ( t ` k ) ) ) e. ( ZZ ^m X ) -> s = t ) )
                         $.
    ofblichfdisjlem3.z $e |- ( ph -> z e. ( ZZ ^m X ) ) $.
    ofblichfdisjlem3.w $e |- ( ph -> w e. ( ZZ ^m X ) ) $.
    ofblichfdisjlem3.uz $e |- ( ph -> u e. ( { y e. ( RR ^m X ) | ( y oF - z )
      e.
      S } i^i X_ k e. X ( 0 [,) 1 ) ) )
                          $.
    ofblichfdisjlem3.uw $e |- ( ph -> u e. ( { y e. ( RR ^m X ) | ( y oF - w )
      e.
      S } i^i X_ k e. X ( 0 [,) 1 ) ) )
                          $.
    $( Lemma for ~ ofblichfdisj : a point common to two integer-lattice
       translates of a set that meets every lattice translate at most once
       forces the two translating lattice points to be equal.  (Contributed by
       Xander Mackay and Claude, 18-Sep-2026.) $)
    ofblichfdisjlem3 $p |- ( ph -> z = w ) $=
      ( cz co wcel cr cv cmap wfn elmapfn syl wa cfv wf cmin cof crab cico cixp
      cc0 c1 elin1d oveq1 eleq1d elrab sylib simpld elmapi ffvelcdmda recnd wss
      wceq zssre a1i fssd cmpt ofblichfdisjlem1 ofblichfdisjlem2 eqeltrd oveq1d
      fveq1 mpteq2dv eqeq1 imbi12d oveq2d elrabrd rspc2dv mpd fveq1d adantr cfn
      wi eqeq2 feqmptd offval2 resubcld fvmpt2d 3eqtr3d subcand eqfnfvd ) AHICU
      AZDUAZAWOQIUBRZSZWOIUCMWOQIUDUEAWPWQSZWPIUCNWPQIUDUEAHUAZISZUFZWTEUAZUGZW
      TWOUGZWTWPUGZXBXDAITWTXCAXCTIUBRZSZITXCUHAXHXCWOUIUJZRZGSZAXCBUAZWOXIRZGS
      ZBXGUKZSXHXKUFAXOHIUNUOULRUMZXCOUPZXNXKBXCXGXLXCVFZXMXJGXLXCWOXIUQURZUSUT
      VAZXCTIVBUEZVCZVDXBXEAITWTWOAIQTWOAWRIQWOUHMWOQIVBUEZQTVEAVGVHZVIVCZVDXBX
      FAITWTWPAIQTWPAWSIQWPUHNWPQIVBUEZYDVIVCZVDXBWTXJUGZWTXCWPXIRZUGZXDXEUIRZX
      DXFUIRZAYHYJVFXAAWTXJYIAHIYHYJUIRZVJZWQSZXJYIVFZAYNWPWOXIRWQACDEHIKMNXTVK
      ACDIKMNVLVMAHIWTJUAZUGZWTFUAZUGZUIRZVJZWQSZYQYSVFZWFYOYPWFHIYHYTUIRZVJZWQ
      SZXJYSVFZWFJFXJYIGGYQXJVFZUUCUUGUUDUUHUUIUUBUUFWQUUIHIUUAUUEUUIYRYHYTUIWT
      YQXJVOVNVPURYQXJYSVQVRYSYIVFZUUGYOUUHYPUUJUUFYNWQUUJHIUUEYMUUJYTYJYHUIWTY
      SYIVOVSVPURYSYIXJWGVRLAXNXKBXCXGXSXQVTAXLWPXIRZGSZYIGSBXCXGXRUUKYIGXLXCWP
      XIUQURAUULBXGUKXPXCPUPVTWAWBWCWDAHIYKXJTAHIXDXEUIXCWOWETTKYBYEAHITXCYAWHZ
      AHIQWOYCWHWIXBXDXEYBYEWJWKAHIYLYITAHIXDXFUIXCWPWETTKYBYGUUMAHIQWPYFWHWIXB
      XDXFYBYGWJWKWLWMWN $.
  $}

  ${
    $d S k s t u z $.  $d S k t u w z $.  $d S k u w y z $.  $d X j k u $.
    $d X k s t u z $.  $d X k t u w z $.  $d X k u w y z $.  $d k ph u w z $.
    ofblichfdisj.x $e |- ( ph -> X e. Fin ) $.
    ofblichfdisj.d $e |- ( ph -> A. s e. S A. t e. S ( ( k e. X |-> ( ( s ` k
      ) - ( t ` k ) ) ) e. ( ZZ ^m X ) -> s = t ) )
                         $.
    $( If a set meets every integer-lattice translate of itself, restricted to
       the half-open unit cube, at most in points forcing equal translates,
       then its integer-lattice translates restricted to that cube are pairwise
       disjoint.  (Contributed by Xander Mackay and Claude, 18-Sep-2026.) $)
    ofblichfdisj $p |- ( ph -> Disj_ z e. ( ZZ ^m X ) ( { y e. ( RR ^m X ) |
      ( y oF - z ) e. S } i^i X_ k e. X ( 0 [,) 1 ) ) )
                       $=
      ( vw vj vu weq cv co wcel cin wral wa cmin cof cr cmap crab cc0 cico cixp
      c1 c0 wceq wo cz wdisj wn simplr cfn ad4antr cfv cmpt wi simprl ad3antrrr
      simprr eqidd cbvixpv eleqtrdi simpr ofblichfdisjlem3 mtand ralrimiva disj
      ineq2i sylibr ex orrd ineq12i eqeq1i orbi2i sylib ralrimivva oveq2 eleq1d
      rabbidv ineq1d disjor ) ACKNZBOZCOZUAUBZPZEQZBUCGUDPZUEZFGUFUIUGPZUHZRZWH
      KOZWJPZEQZBWMUEZWPRZRZUJUKZULZKUMGUDPZSCXFSCXFWQUNAXECKXFXFAWIXFQZWRXFQZT
      ZTZWGWNLGWOUHZRZXAXKRZRZUJUKZULXEXJWGXOXJWGUOZXOXJXPTZMOZXMQZUOZMXLSXOXQX
      TMXLXQXRXLQZTZXSWGXJXPYAUPYBXSTZBCKMDEFGHAGUQQXIXPYAXSIURAFGFOZHOUSYDDOUS
      UAPUTXFQHDNVADESHESXIXPYAXSJURXJXGXPYAXSAXGXHVBVCXJXHXPYAXSAXGXHVDVCYCXRX
      LWQXQYAXSUPXKWPWNLFGWOWOLFNWOVEVFZVMZVGYCXRXMXBYBXSVHXKWPXAYEVMZVGVIVJVKM
      XLXMVLVNVOVPXOXDWGXNXCUJXLWQXMXBYFYGVQVRVSVTWAXFWQXBCKWGWNXAWPWGWLWTBWMWG
      WKWSEWIWRWHWJWBWCWDWEWFVN $.
  $}

  ${
    $d S k $.
    $d S s $.
    $d S t $.
    $d S y $.
    $d S z $.
    $d X k $.
    $d X s $.
    $d X t $.
    $d X y $.
    $d X z $.
    $d k ph $.
    $d k s $.
    $d k t $.
    $d k y $.
    $d k z $.
    $d ph y $.
    $d ph z $.
    $d s t $.
    $d s z $.
    $d t z $.
    $d y z $.
    blichfeldtlem7.x $e |- ( ph -> X e. Fin ) $.
    blichfeldtlem7.s $e |- ( ph -> S e. dom ( voln ` X ) ) $.
    blichfeldtlem7.d $e |- ( ph -> A. s e. S A. t e. S ( ( k e. X |-> ( ( s ` k
      ) - ( t ` k ) ) ) e. ( ZZ ^m X ) -> s = t ) )
                         $.
    $( Lemma for ~ blichfeldt : the sum of the pieces' measures is at most the
       unit cube's, by ~ meadjiun for the disjoint union's measure (its own
       ` $d B i y ` dodged by a ~ cbvrabv rename of the piece's rab, converted
       back after) and ~ meassle against the cube via ~ saliuncl and ~ iunss /
       ~ inss2 .  (Contributed by Xander Mackay and Claude, 18-Sep-2026.) $)
    blichfeldtlem7 $p |- ( ph -> ( sum^ ` ( z e. ( ZZ ^m X ) |-> ( ( voln ` X )
      ` ( { y e. ( RR ^m X ) | ( y oF - z ) e. S } i^i X_ k e. X ( 0 [,) 1 ) )
      ) ) ) <_ ( ( voln ` X ) ` X_ k e. X ( 0 [,) 1 ) ) )
                       $=
      ( cz cmap co cv wcel cfv adantr wss a1i cmin cof cr crab cc0 c1 cico cixp
      cin ciun cvoln cmpt csumge0 cle cdm nfv vonmea eqid wa cfn blichfeldtlem2
      vonziunlem9 ofblichfdisj meadjiun dmovnsal saliuncl vonziunlem1 mprgbir
      simpr iunss inss2 meassle eqbrtrrd ) ACLGMNZBOCOZUAUBNEPBUCGMNUDZFGUEUFUG
      NUHZUIZUJZGUKQZQCVNVRVTQULUMQVQVTQUNAVNVRVTUOZCVTACUPAGIUQZWAURZAVOVNPZUS
      BCEFGAGUTPWDIRAEWAPWDJRAWDVIVAZAGIVBZABCDEFGHIKVCVDAVSVQWAVTWBWCAWACVRVNA
      WAGIWCVEWFWEVFAFGIVGVSVQSZAWGVRVQSZCVNCVNVRVQVJWHWDVPVQVKTVHTVLVM $.
  $}

  ${
    $d S k s t z $.  $d S k y z $.  $d X k s t z $.  $d X k y z $.
    $d k ph y z $.
    blichfeldtlem8.x $e |- ( ph -> X e. Fin ) $.
    blichfeldtlem8.n $e |- ( ph -> X =/= (/) ) $.
    blichfeldtlem8.s $e |- ( ph -> S e. dom ( voln ` X ) ) $.
    blichfeldtlem8.d $e |- ( ph -> A. s e. S A. t e. S ( ( k e. X |-> ( ( s ` k
      ) - ( t ` k ) ) ) e. ( ZZ ^m X ) -> s = t ) )
                         $.
    $( Lemma for ~ blichfeldt : a set ` S ` in which no two points differ by a
       lattice point has measure at most ` 1 ` , by ~ vonziun and
       ~ blichfeldtlem7 against ~ blichfeldtlem1 's unit-cube measure.
       (Contributed by Xander Mackay and Claude, 18-Sep-2026.) $)
    blichfeldtlem8 $p |- ( ph -> ( ( voln ` X ) ` S ) <_ 1 ) $=
      ( vz vy cvoln cfv cc0 c1 co cle cmap cv cico cixp cz cmin cof wcel cr cin
      crab cmpt csumge0 vonziun blichfeldtlem7 eqbrtrd blichfeldtlem1 breqtrd )
      ACEMNZNZDEOPUAQUBZUQNZPRAURKUCESQLTKTUDUEQCUFLUGESQUIUSUHUQNUJUKNUTRALKCD
      EGIULALKBCDEFGIJUMUNADEGHUOUP $.
  $}

  ${
    $d I k $.
    $d I x $.
    $d I y $.
    $d I z $.
    $d S x $.
    $d S y $.
    $d S z $.
    $d k x $.
    $d k y $.
    $d k z $.
    $d ph z $.
    $d x y $.
    $d x z $.
    $d y z $.
    blicht.n $e |- ( ph -> N e. NN ) $.
    blicht.i $e |- I = ( 1 ... N ) $.
    blicht.m $e |- ( ph -> S e. dom ( voln ` I ) ) $.
    blicht.v $e |- ( ph -> 1 < ( ( voln ` I ) ` S ) ) $.
    $( Blichfeldt's lemma, the measure-theoretic half of ~ minkowski : a
       measurable set of measure greater than ` 1 ` contains two distinct
       points whose difference is a lattice point.  (Contributed by Xander
       Mackay and Claude, 18-Sep-2026.) $)
    blichfeldt $p |- ( ph -> E. x e. S E. y e. S ( x =/= y /\ ( k e. I |-> ( (
      x ` k ) - ( y ` k ) ) ) e. ( ZZ ^m I ) ) )
                   $=
      ( vz cv cfv co wcel c1 wn adantr wral wne cmin cmpt cz cmap wa wrex cvoln
      cle wbr cfn cfz fzfid eqeltrid c0 eqcomi cuz cn nnuz eleqtrdi fzn0 sylibr
      eqnetrrid cdm weq wi ralnex2 con2b imnan nne imbi2i 3bitr3i bitr3i bilani
      2ralbii fveq2 oveq12d cbvmptv eleq1i sylib blichfeldtlem8 clt cxr 1xr a1i
      imbi1i vonmea eqid meaxrcl xrltnled mpbid condan ) ABMZCMZUAZEFEMZWMNZWPW
      NNZUBOZUCZUDFUEOZPZUFZCDUGBDUGZDFUHNZNZQUIUJZAXDRZUFZCDLFBAFUKPXHAFQGULOZ
      UKIAQGUMUNZSAFUOUAXHAFXJUOFXJIUPAGQUQNZPXJUOUAAGURXLHUSUTQGVAVBVCSADXEVDZ
      PXHJSXIXBBCVEZVFZCDTBDTZLFLMZWMNZXQWNNZUBOZUCZXAPZXNVFZCDTBDTXHXPAXHXCRZC
      DTBDTXPXCBCDDVGYDXOBCDDWOXBRVFXBWORZVFYDXOWOXBVHWOXBVIYEXNXBWMWNVJVKVLVOV
      MVNXOYCBCDDXBYBXNWTYAXAELFWSXTELVEWQXRWRXSUBWPXQWMVPWPXQWNVPVQVRVSWFVOVTW
      AAXGRZXHAQXFWBUJYFKAQXFQWCPAWDWEADXMXEAFXKWGXMWHJWIWJWKSWL $.
  $}

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  The half-set
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    $d S y $.  $d X y $.  $d ph y $.
    minkhalflem1.x $e |- ( ph -> X e. Fin ) $.
    minkhalflem1.s $e |- ( ph -> S e. dom ( voln ` X ) ) $.
    $( Lemma for ~ minkhalf : the half-set of a Lebesgue-measurable set is
       Lebesgue-measurable, ~ vonsmullem39 at ` C = ( 1 / 2 ) ` .  (Contributed
       by Xander Mackay and Claude, 18-Sep-2026.) $)
    minkhalflem1 $p |- ( ph -> { y e. ( RR ^m X ) | ( y oF / ( X X. { ( 1 / 2 )
      } ) ) e. S } e. dom ( voln ` X ) )
                     $=
      ( c1 c2 cdiv co cr wcel halfre a1i cc0 clt wbr halfgt0 elrpd vonsmullem39
      ) ABGHIJZCDEAUAUAKLAMNOUAPQARNSFT $.
  $}

  ${
    $d X y $.
    $( Lemma for ~ minkhalf : the half-set is a set of points of
       ` ( RR ^m X ) ` , which is what ~ blichfeldt asks of it.  (Contributed
       by Xander Mackay and Claude, 18-Sep-2026.) $)
    minkhalflem2 $p |- { y e. ( RR ^m X ) | ( y oF / ( X X. { ( 1 / 2 ) } ) )
      e. S } C_ ( RR ^m X )
                     $=
      ( cv c1 c2 cdiv co csn cxp cof wcel cr cmap ssrab2 ) ADCEFGHIJGKHBLAMCNHO
      $.
  $}

  ${
    $d S y $.  $d X y $.  $d ph y $.
    minkhalf.x $e |- ( ph -> X e. Fin ) $.
    minkhalf.s $e |- ( ph -> S e. dom ( voln ` X ) ) $.
    minkhalf.v $e |- ( ph -> ( 2 ^ ( # ` X ) ) < ( ( voln ` X ) ` S ) ) $.
    $( The half-set of a measurable set of measure greater than
       ` ( 2 ^ ( # `` X ) ) ` has measure greater than ` 1 ` : ~ vonsmul at
       ` C = ( 1 / 2 ) ` scales the measure by ` ( ( 1 / 2 ) ^ ( # `` X ) ) ` ,
       and ~ xltmul2 scales the hypothesis by the same positive real.
       (Contributed by Xander Mackay and Claude, 18-Sep-2026.) $)
    minkhalf $p |- ( ph -> 1 < ( ( voln ` X ) ` { y e. ( RR ^m X ) | ( y oF / (
      X X. { ( 1 / 2 ) } ) ) e. S } ) )
                 $=
      ( c1 c2 cdiv co cfv cexp cxmu wcel cr clt cmul a1i wbr chash cvoln cv csn
      cxp cof cmap crab wceq halfre cfn cn0 hashcl syl reexpcld 2re rexmul 2cnd
      syl2anc cc0 wne 2ne0 recid2d oveq1d recnd mulexpd cz 1exp 3eqtr3rd eqtr4d
      nn0zd cxr crp wb rexrd vonmea eqid meaxrcl halfgt0 elrpd rpexpcld xltmul2
      cdm syl3anc mpbid eqbrtrrd vonsmul breqtrrd ) AHHIJKZDUALZMKZCDUBLZLZNKZB
      UCDWIUDUEJUFKCOBPDUGKUHWLLQAWKIWJMKZNKZHWNQAWPWKWORKZHAWKPOWOPOWPWQUIAWIW
      JWIPOAUJSZADUKOWJULOEDUMUNZUOAIWJIPOAUPSWSUOZWKWOUQUSAWIIRKZWJMKHWJMKZWQH
      AXAHWJMAIAURZIUTVAAVBSVCVDAWIIWJAWIWRVEXCWSVFAWJVGOXBHUIAWJWSVKZWJVHUNVIV
      JAWOWMQTZWPWNQTZGAWOVLOWMVLOWKVMOXEXFVNAWOWTVOACWLWCZWLADEVPXGVQFVRAWIWJA
      WIWRUTWIQTAVSSVTZXDWAWOWMWKWBWDWEWFABWICDEXHFWGWH $.
  $}

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  The difference of two points of the half-set lies in the set
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    $d I y $.  $d S y $.  $d V y $.
    minkcvxlem1.v $e |- ( ph -> V e. { y e. ( RR ^m I ) | ( y oF / ( I X. { ( 1
      / 2 ) } ) ) e. S } )
                      $.
    $( Lemma for ~ minkcvx : a point of the half-set is a point of
       ` ( RR ^m I ) ` whose double lies in ` S ` .  (Contributed by Xander
       Mackay and Claude, 18-Sep-2026.) $)
    minkcvxlem1 $p |- ( ph -> ( V e. ( RR ^m I ) /\ ( V oF / ( I X. { ( 1 / 2 )
      } ) ) e. S ) )
                    $=
      ( cv c1 c2 cdiv co csn cxp cof wcel cr cmap crab wa wceq oveq1 eleq1d
      elrab sylib ) AEBGZDHIJKLMZJNZKZCOZBPDQKZROEUJOEUFUGKZCOZSFUIULBEUJUEETUH
      UKCUEEUFUGUAUBUCUD $.
  $}

  ${
    minkcvxlem2.v $e |- ( ph -> V e. ( RR ^m I ) ) $.
    $( Lemma for ~ minkcvx : a coordinate of the doubled point.  (Contributed
       by Xander Mackay and Claude, 18-Sep-2026.) $)
    minkcvxlem2 $p |- ( ( ph /\ k e. I ) -> ( ( V oF / ( I X. { ( 1 / 2 ) } ) )
      ` k ) = ( ( V ` k ) / ( 1 / 2 ) ) )
                    $=
      ( cv cfv c1 c2 cdiv co csn cxp cvv cr cmap wcel wfn syl wa elmapfn simprd
      ovex fnconstg mp1i elmapex inidm eqidd wceq fvconst2 adantl ofval ) ACCBF
      ZDGZHIJKZJCDCUOLMZNNUMADOCPKQZDCREDOCUASUONQUPCRAHIJUCZCUONUDUEAONQZCNQZA
      UQUSUTTEDOCUFSUBZVACUGAUMCQZTUNUHVBUMUPGUOUIACUOUMURUJUKUL $.
  $}

  ${
    $d I t $.  $d I x $.  $d I y $.  $d S t $.  $d S x $.  $d S y $.  $d X k $.
    $d X t $.  $d X x $.  $d X y $.  $d Y k $.  $d Y t $.  $d Y y $.  $d k t $.
    $d k x $.  $d k y $.  $d t x $.  $d t y $.  $d x y $.
    minkcvxlem3.c $e |- ( ph -> A. x e. S A. y e. S A. t e. ( 0 [,] 1 ) ( k e.
      I |-> ( ( t x. ( x ` k ) ) + ( ( 1 - t ) x. ( y ` k ) ) ) ) e. S )
                      $.
    minkcvxlem3.x $e |- ( ph -> X e. S ) $.
    minkcvxlem3.y $e |- ( ph -> Y e. S ) $.
    $( Lemma for ~ minkcvx : the convexity hypothesis at ` t = ( 1 / 2 ) ` ,
       the midpoint of two points of ` S ` is in ` S ` .  (Contributed by
       Xander Mackay and Claude, 18-Sep-2026.) $)
    minkcvxlem3 $p |- ( ph -> ( k e. I |-> ( ( ( 1 / 2 ) x. ( X ` k ) ) + ( ( 1
      - ( 1 / 2 ) ) x. ( Y ` k ) ) ) ) e. S )
                    $=
      ( c1 co wcel cv cfv cmul caddc cmpt c2 cdiv cc0 cicc cmin wral cr cle wbr
      halfre halfge0 halflt1 ltleii elicc01 mpbir3an wceq fveq1 oveq2d mpteq2dv
      1re oveq1d eleq1d ralbidv rspc2dv oveq1 oveq2 oveq12d rspcv mpsyl ) MUAUB
      NZUCMUDNZOZAFGDPZFPZHQZRNZMVMUENZVNIQZRNZSNZTZEOZDVKUFZFGVJVORNZMVJUENZVR
      RNZSNZTZEOZVLVJUGOUCVJUHUIVJMUHUIUJUKVJMUJUTULUMVJUNUOAFGVMVNBPZQZRNZVQVN
      CPZQZRNZSNZTZEOZDVKUFWCFGVPWOSNZTZEOZDVKUFBCHIEEWJHUPZWRXADVKXBWQWTEXBFGW
      PWSXBWLVPWOSXBWKVOVMRVNWJHUQURVAUSVBVCWMIUPZXAWBDVKXCWTWAEXCFGWSVTXCWOVSV
      PSXCWNVRVQRVNWMIUQURURUSVBVCJKLVDWBWIDVJVKVMVJUPZWAWHEXDFGVTWGXDVPWDVSWFS
      VMVJVORVEXDVQWEVRRVMVJMUEVFVAVGUSVBVHVI $.
  $}

  ${
    $d I j $.  $d I k $.  $d I x $.  $d S x $.  $d X j $.  $d X k $.  $d X x $.
    $d j k $.  $d k x $.
    minkcvxlem4.o $e |- ( ph -> A. x e. S ( k e. I |-> -u ( x ` k ) ) e. S ) $.
    minkcvxlem4.x $e |- ( ph -> X e. S ) $.
    $( Lemma for ~ minkcvx : the symmetry hypothesis at a point of ` S ` , with
       the negated point written over a fresh binder ` j ` .  (Contributed by
       Xander Mackay and Claude, 18-Sep-2026.) $)
    minkcvxlem4 $p |- ( ph -> ( j e. I |-> -u ( X ` j ) ) e. S ) $=
      ( cv cfv cneg cmpt wceq fveq2 negeqd cbvmptv wcel fveq1 mpteq2dv rspcdva
      eleq1d eqeltrrid ) ADFDJZGKZLZMEFEJZGKZLZMZCEDFUIUFUGUDNUHUEUGUDGOPQAEFUG
      BJZKZLZMZCRUJCRBCGUKGNZUNUJCUOEFUMUIUOULUHUGUKGSPTUBHIUAUC $.
  $}

  $( Lemma for ~ minkcvx : the coordinate algebra, half the double of ` A `
     plus half the negated double of ` B ` is ` ( A - B ) ` .  (Contributed by
     Xander Mackay and Claude, 18-Sep-2026.) $)
  minkcvxlem5 $p |- ( ( A e. CC /\ B e. CC ) -> ( ( ( 1 / 2 ) x. ( A / ( 1 / 2
    ) ) ) + ( ( 1 - ( 1 / 2 ) ) x. -u ( B / ( 1 / 2 ) ) ) ) = ( A - B ) )
                  $=
    ( cc wcel wa c1 c2 cdiv co cmul cmin cneg caddc simpl halfcn a1i cc0 halfre
    wne divcan2d halfgt0 gt0ne0ii 1mhlfehlf oveq1d simpr divcld mulneg2d negeqd
    wceq 3eqtrd oveq12d negsub eqtrd ) ACDZBCDZEZFGHIZAUQHIJIZFUQKIZBUQHIZLZJIZ
    MIABLZMIABKIUPURAVBVCMUPAUQUNUONUQCDUPOPZUQQSUPUQRUAUBPZTUPVBUQVAJIUQUTJIZL
    VCUPUSUQVAJUSUQUIUPUCPUDUPUQUTVDUPBUQUNUOUEZVDVEUFUGUPVFBUPBUQVGVDVETUHUJUK
    ABULUM $.

  ${
    $d I j $.  $d I k $.  $d I t $.  $d I x $.  $d I y $.  $d S j $.  $d S k $.
    $d S t $.  $d S x $.  $d S y $.  $d V k $.  $d V t $.  $d V x $.  $d V y $.
    $d W j $.  $d W k $.  $d W t $.  $d W x $.  $d W y $.  $d j k $.
    $d j ph $.  $d j t $.  $d j x $.  $d j y $.  $d k ph $.  $d k t $.
    $d k x $.  $d k y $.  $d ph t $.  $d ph x $.  $d ph y $.  $d t x $.
    $d t y $.  $d x y $.
    minkcvx.c $e |- ( ph -> A. x e. S A. y e. S A. t e. ( 0 [,] 1 ) ( k e. I
      |-> ( ( t x. ( x ` k ) ) + ( ( 1 - t ) x. ( y ` k ) ) ) ) e. S )
                  $.
    minkcvx.o $e |- ( ph -> A. x e. S ( k e. I |-> -u ( x ` k ) ) e. S ) $.
    minkcvx.v $e |- ( ph -> V e. { y e. ( RR ^m I ) | ( y oF / ( I X. { ( 1 / 2
      ) } ) ) e. S } )
                  $.
    minkcvx.w $e |- ( ph -> W e. { y e. ( RR ^m I ) | ( y oF / ( I X. { ( 1 / 2
      ) } ) ) e. S } )
                  $.
    $( The convexity step used in the proof of Minkowski's theorem on lattice
       points: the difference of two points of the half-set of a convex,
       centrally symmetric ` S ` lies in ` S ` , as the midpoint of the double
       of one and the negated double of the other.  (Contributed by Xander
       Mackay and Claude, 18-Sep-2026.) $)
    minkcvx $p |- ( ph -> ( k e. I |-> ( ( V ` k ) - ( W ` k ) ) ) e. S )
                $=
      ( vj cdiv co cfv cmul wcel cr c1 c2 csn cxp cof cmin cneg cmpt caddc cmap
      cv minkcvxlem1 simpld minkcvxlem2 oveq2d cvv eqid wceq fveq2 negeqd simpr
      wa negex a1i fvmptd3 eqtrd oveq12d cc elmapi ffvelcdmda recnd minkcvxlem5
      wf syl syl2anc mpteq2dva simprd minkcvxlem4 minkcvxlem3 eqeltrrd ) AFGUAU
      BOPZFUKZHGWAUCUDZOUEZPZQZRPZUAWAUFPZWBNGNUKZIWCWDPZQZUGZUHZQZRPZUIPZUHFGW
      BHQZWBIQZUFPZUHEAFGWPWSAWBGSZVBZWPWAWQWAOPZRPZWHWRWAOPZUGZRPZUIPZWSXAWGXC
      WOXFUIXAWFXBWARAFGHAHTGUJPZSZWEESZACEGHLULZUMZUNUOXAWNXEWHRXAWNWBWJQZUGZX
      EXANWBWLXNGWMUPWMUQWIWBURWKXMWIWBWJUSUTAWTVAXNUPSXAXMVCVDVEXAXMXDAFGIAIXH
      SZWJESZACEGIMULZUMZUNUTVFUOVGXAWQVHSWRVHSXGWSURXAWQAGTWBHAXIGTHVMXLHTGVIV
      NVJVKXAWRAGTWBIAXOGTIVMXRITGVIVNVJVKWQWRVLVOVFVPABCDEFGWEWMJAXIXJXKVQABEN
      FGWJKAXOXPXQVQVRVSVT $.
  $}

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Minkowski's fundamental theorem
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    $d I j $.
    $d I k $.
    $d I m $.
    $d U j $.
    $d U k $.
    $d U m $.
    $d V j $.
    $d V k $.
    $d V m $.
    $d j k $.
    $d j m $.
    $d j ph $.
    $d k m $.
    minkowskilem1.u $e |- ( ph -> U e. ( RR ^m I ) ) $.
    minkowskilem1.v $e |- ( ph -> V e. ( RR ^m I ) ) $.
    minkowskilem1.n $e |- ( ph -> U =/= V ) $.
    $( Lemma for ~ minkowski : the coordinatewise difference of two distinct
       points of ` ( RR ^m I ) ` is not the zero vector.  (Contributed by
       Xander Mackay and Claude, 18-Sep-2026.) $)
    minkowskilem1 $p |- ( ph -> ( k e. I |-> ( ( U ` k ) - ( V ` k ) ) ) =/= (
      I X. { 0 } ) )
                      $=
      ( vj vm cv cfv cmin co cc0 wceq cr wcel syl fveq2 cmpt csn cxp wa elmapfn
      wfn adantr wf elmapi ad2antrr simpr ffvelcdmd recnd simplr fveq1d oveq12d
      cmap cbvmptv ovexd fvmptd3 c0ex fvconst2 3eqtr3d subeq0d eqfnfvd mteqand
      cvv ) ACDCKZBLZVHELZMNZUAZDOUBUCZBEHAVLVMPZUDZIDBEABDUFZVNABQDUQNZRZVPFBQ
      DUESUGAEDUFZVNAEVQRZVSGEQDUESUGVOIKZDRZUDZWABLZWAELZWCWDWCDQWABADQBUHZVNW
      BAVRWFFBQDUISUJVOWBUKZULUMWCWEWCDQWAEADQEUHZVNWBAVTWHGEQDUISUJWGULUMWCWAV
      LLWAVMLZWDWEMNZOWCWAVLVMAVNWBUNUOWCJWAJKZBLZWKELZMNZWJDVLVGCJDVKWNVHWKPVI
      WLVJWMMVHWKBTVHWKETUPURWKWAPWLWDWMWEMWKWABTWKWAETUPWGWCWDWEMUSUTWCWBWIOPW
      GDOWAVAVBSVCVDVEVF $.
  $}

  ${
    $d I y $.  $d S y $.  $d ph y $.
    minkowskilem2.n $e |- ( ph -> N e. NN ) $.
    minkowskilem2.i $e |- I = ( 1 ... N ) $.
    minkowskilem2.m $e |- ( ph -> S e. dom ( voln ` I ) ) $.
    minkowskilem2.v $e |- ( ph -> ( 2 ^ N ) < ( ( voln ` I ) ` S ) ) $.
    $( Lemma for ~ minkowski : the half-set has measure greater than ` 1 ` ,
       ~ minkhalf at ` X = I ` with ` N ` for ` ( # `` I ) ` .  (Contributed by
       Xander Mackay and Claude, 18-Sep-2026.) $)
    minkowskilem2 $p |- ( ph -> 1 < ( ( voln ` I ) ` { y e. ( RR ^m I ) | ( y
      oF / ( I X. { ( 1 / 2 ) } ) ) e. S } ) )
                      $=
      ( c1 cfz co cfn fzfid eqeltrid c2 chash cfv cexp cvoln fveq2i wcel nnnn0d
      clt cn0 wceq hashfz1 syl eqtrid oveq2d eqbrtrd minkhalf ) ABCDADJEKLZMGAJ
      ENOHAPDQRZSLPESLCDTRRUDAUNEPSAUNUMQRZEDUMQGUAAEUEUBUOEUFAEFUCEUGUHUIUJIUK
      UL $.
  $}

  ${
    $d I k $.
    $d I t $.
    $d I u $.
    $d I v $.
    $d I x $.
    $d I y $.
    $d I z $.
    $d N k $.
    $d N u $.
    $d N v $.
    $d S k $.
    $d S t $.
    $d S u $.
    $d S v $.
    $d S x $.
    $d S y $.
    $d S z $.
    $d k ph $.
    $d k t $.
    $d k u $.
    $d k v $.
    $d k x $.
    $d k y $.
    $d k z $.
    $d ph t $.
    $d ph u $.
    $d ph v $.
    $d ph x $.
    $d ph y $.
    $d t u $.
    $d t v $.
    $d t x $.
    $d t y $.
    $d u v $.
    $d u x $.
    $d u y $.
    $d u z $.
    $d v x $.
    $d v y $.
    $d v z $.
    $d x y $.
    minkow.n $e |- ( ph -> N e. NN ) $.
    minkow.i $e |- I = ( 1 ... N ) $.
    minkow.m $e |- ( ph -> S e. dom ( voln ` I ) ) $.
    minkow.c $e |- ( ph -> A. x e. S A. y e. S A. t e. ( 0 [,] 1 ) ( k e. I |->
      ( ( t x. ( x ` k ) ) + ( ( 1 - t ) x. ( y ` k ) ) ) ) e. S )
                 $.
    minkow.o $e |- ( ph -> A. x e. S ( k e. I |-> -u ( x ` k ) ) e. S ) $.
    minkow.v $e |- ( ph -> ( 2 ^ N ) < ( ( voln ` I ) ` S ) ) $.
    $( Minkowski's fundamental theorem of the geometry of numbers: a convex,
       centrally symmetric measurable subset ` S ` of ` RR ^ N ` whose ` N `
       -dimensional Lebesgue measure exceeds ` 2 ^ N ` contains a lattice point
       other than the origin.  Wiedijk #40.  This is Metamath 100 proof #40.
       (Contributed by Xander Mackay and Claude, 18-Sep-2026.) $)
    minkowski $p |- ( ph -> E. z e. S ( z e. ( ZZ ^m I ) /\ z =/= ( I X. { 0 }
      ) ) )
                  $=
      ( cv co wcel wa c1 vu vv wne cfv cmin cmpt cz cmap c2 cdiv csn cxp cof cr
      crab wrex cc0 cfz cfn eqeltrid minkhalflem1 minkowskilem2 blichfeldt wceq
      fzfid eleq1 neeq1 anbi12d simpll simplrl oveq1 eleq1d elrab sylib simplrr
      cmul caddc cicc wral adantr cneg simprl sylibr simprr syl12anc elrabi syl
      minkcvx minkowskilem1 jca rspcedvdw ex rexlimdvva mpd ) AUAPZUBPZUCZGHGPZ
      WOUDWRWPUDUEQUFZUGHUHQZRZSZUBCPZHTUIUJQUKULZUJUMZQZFRZCUNHUHQZUOZUPUAXIUP
      DPZWTRZXJHUQUKULZUCZSZDFUPZAUAUBXIGHIJKACFHAHTIURQUSKATIVEUTLVAACFHIJKLOV
      BVCAXBXOUAUBXIXIAWOXIRZWPXIRZSZSZXBXOXSXBSZXNXAWSXLUCZSDWSFXJWSVDXKXAXMYA
      XJWSWTVFXJWSXLVGVHXTAWOXHRZWOXDXEQZFRZSZWPXHRZWPXDXEQZFRZSZWSFRAXRXBVIXTX
      PYEAXPXQXBVJZXGYDCWOXHXCWOVDXFYCFXCWOXDXEVKVLVMZVNXTXQYIAXPXQXBVOZXGYHCWP
      XHXCWPVDXFYGFXCWPXDXEVKVLVMZVNAYEYISZSZBCEFGHWOWPAGHEPZWRBPUDZVPQTYPUEQWR
      XCUDVPQVQQUFFREUQTVRQVSCFVSBFVSYNMVTAGHYQWAUFFRBFVSYNNVTYOYEXPAYEYIWBYKWC
      YOYIXQAYEYIWDYMWCWHWEXTXAYAXSWQXAWDXTWOGHWPXTXPYBYJXGCWOXHWFWGXTXQYFYLXGC
      WPXHWFWGXSWQXAWBWIWJWKWLWMWN $.
  $}

