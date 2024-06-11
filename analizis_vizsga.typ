#import "@preview/cetz:0.2.2"

#let colorS = color.rgb("#B4D3B4")
#let colorQ = color.rgb("#FB772A")
#let colorT = color.rgb("#8AEAFD")

#set page(
  paper: "a4",
  numbering: "1.",
  margin: (x: 40pt, y: 40pt)
)

#set document(
  author: "Krasznai Dániel & Tóth Zalán",
  title: "Analízis vizsga tételek"
)

#set text(
  size: 15pt,
  font: "Times New Roman"
)

#set par(justify: true)

#set enum(numbering: "1.)")

#show heading.where(level: 1): it => align(center)[
  #it
  #v(10pt)
]

#show heading.where(level: 2): it => block(
  fill: colorS,
  inset: 10pt,
  radius: 4pt,
)[#it]

#show heading.where(level: 3): it => [#underline[#it]]

#let color_description(color, desc) = [
  #grid(
    columns: (auto,auto,auto),
    gutter: 4pt,
    align: horizon + center,
    rect(width: 20pt, height: 20pt, fill: color, radius: (rest: 5pt)), [-], [#desc]
  )
]

= Analízis vizsga bizonyítással kért tételek

#grid(
  columns: (auto, auto, auto),
  gutter: 10pt,
  color_description(colorS, "Sorozat"),
  color_description(colorT, "Sorok"),
  color_description(colorQ, "Vegyes")
)

== Teljes indukció elve

Tegyük fel, hogy minden $n$ természetes számra adott egy $A(n)$ állítás, és azt tudjuk, hogy

+ $A(0)$ igaz
+ ha $A(n)$ állítás igaz, akkor $A(n+1)$ is igaz

Ekkor az $A(n)$ állítás minden $n$ természetes számra igaz.

=== Bizonyítás

Legyen

$ S colon.eq {n in NN bar A(n) "igaz"} $

Ekkor $S subset NN$ és $S$ induktív halmaz, hiszen $0 in S$, és ha $n in S$, azaz $A(n)$ igaz, akkor $A(n + 1)$ is igaz, ezért $n + 1 in S$ teljesül, következésképpen $S$ induktív halmaz. Mivel $NN$ a legszűkebb induktív halmaz, ezért az $NN subset S$ tartalmazás is fennáll, tehát $S eq NN$. Ez pedig azt jelenti, hogy minden $n$ természetes számra igaz.

#pagebreak()

== A szuprémum elv

Legyen $H subset RR$ és tegyük fel, hogy

+ $H eq.not emptyset$
+ $H$ felülről korlátos

Ekkor

$ exists min{K in RR bar K "felsőkorlátja" H"-nak"} $

=== Bizonyítás

Legyen

$ A colon.eq H space "és" space B colon.eq {K in RR bar K "felsőkorlátja" H"-nak"} $

A feltételek miatt $A eq.not emptyset "és" B eq.not emptyset$, továbbá

$ forall a in A "és" forall K in B: a lt.eq K $

A teljességi axiómából következik, hogy

$ exists epsilon in RR: a lt.eq epsilon lt.eq K space (a in A, K in B) $

Erre az $epsilon$-ra az teljesül, hogy

+ $epsilon$ felsőkorlátja $H$-nak, hiszen $a lt.eq epsilon$ minden $a in A$ esetén
+ $epsilon$ a legkisebb felső korlát, ui. ha $K$ egy felső korlát (azaz $K in B$), akkor $K gt.eq epsilon$.

Ez pedig pontosan azt jelenti, hogy $epsilon$ a $H$ halmaz legkisebb felső korlátja.

#pagebreak()

== Az arkhimédészi tulajdonság

Minden $a gt 0$ és minden $b$ valós számhoz létezik olyan $n$ természetes szám, hogy $b lt n dot a$, azaz

$ forall a gt 0 "és" forall b in RR: exists n in NN: b lt n dot a $

=== Bizonyítás (indirekt módon)

Tegyük fel, hogy

$ exists a gt 0 "és" exists b in RR: forall n in NN: b gt.eq n dot a $

Legyen

$ H colon.eq {n dot a in RR bar n in NN} $

Ekkor $H eq.not emptyset$ és $H$ felülről korlátos, hiszen $n dot a lt.eq b$ minden $n in NN$-re. A szuprémum elv szerint:

$ exists sup H eq.colon epsilon $

Ekkor $epsilon$ a legkisebb felsőkorlátja $H$-nak, tehát $epsilon - a$ nem felső korlát. Ez azt jelenti, hogy:

$ exists n_0 in NN: n_0 dot a gt epsilon - a arrow.double.r.l.long (n_0 + 1) dot a gt epsilon $

Azonban $(n_0 + 1) dot a in H$, tehát $(n_0 + 1) dot a lt.eq epsilon$, hiszen $epsilon$ felső korlátja a $H$ halmaznak. Így ellentmondáshoz jutunk.

#pagebreak()

== A Cantor-tulajdonság

Tegyük fel, hogy minden n természetes számra adott az $[a_n,b_n] subset RR$ korlátos és zárt intervallum úgy, hogy

$ [a_(n+1),b_(n+1)] subset [a_n,b_n] space (n in NN) $

Ekkor

$ sect.big_(n in NN)[a_n,b_n] eq.not emptyset $

=== Bizonyítás (teljességi axiómát alkalmazva)

Legyen

$ A colon.eq {a_n bar n in NN} "és" B colon.eq {b_n bar n in NN} $

Először belátjuk, hogy

$ a_n lt.eq b_m "tetszőleges" n,m in NN "esetén" $

Valóban,

+ ha $n lt.eq m$, akkor $a_n lt.eq a_m lt.eq b_m$
+ ha $m lt n$, akkor $a_n lt.eq b_n lt.eq b_m$

Mivel $A eq.not emptyset "és" B eq.not emptyset$, ezért "$a_n lt.eq b_m "tetszőleges" n,m in NN "esetén"$" miatt a teljességi axióma feltételei teljesülnek, így

$ exists epsilon in RR: a_n lt.eq epsilon lt.eq b_m space space forall n,m in NN "indexre" $

Ha $n eq m$, akkor azt kapjuk, hogy

$ a_n lt.eq epsilon lt.eq b_n space arrow.double.l.r.long space epsilon in [a_n,b_n] space space forall n in NN "esetén" $

és azt jelenti, hogy

$ epsilon in sect.big_(n in NN)[a_n,b_n] eq.not emptyset $

#pagebreak()

== Konvergens sorozatok határértékének egyértelműsége

(\*) #h(weak: true,20pt) $exists A in RR: forall epsilon gt 0: exists n_0 in NN: forall n gt n_0 "indexre" |a_n - A| lt epsilon$

Ha az $(a_n) : NN → RR$ sorozat konvergens, akkor a konvergencia definíciójában szereplő $A$ szám egyértelműen létezik.

=== Bizonyítás

Tegyük fel, hogy az $(a_n)$ sorozatra (\*) az $A_1$ és az $A_2$ számokkal is teljesül.
Indirekt módon tegyük fel azt is, hogy $A_1 eq.not A_2$.

Ekkor $forall epsilon gt 0$ számhoz

$ exists n_1 in NN: forall n gt n_1 : abs(a_n − A_1) lt epsilon $
$ exists n_2 in NN: forall n gt n_2 : abs(a_n − A_2) lt epsilon $

Válasszuk itt speciálisan az

$ epsilon colon.eq abs(A_1 - A_2)/2 $

(pozitív) számot. Az ennek megfelelő $n_1, n_2$ indexeket figyelembe véve legyen

$ n_0 colon.eq max{n_1,n_2} $

Ha $n in NN "és" n gt n_0$, akkor nyilván $n gt n_1 "és" n gt n_2$ is fennáll, következésképpen

$ abs(A_1 - A_2) eq abs((A_1 - a_n) + (a_n - A_2))lt.eq abs(a_n - A_1) + abs(a_n - A_2) \ lt epsilon + epsilon eq 2epsilon eq abs(A_1 - A_2) $

amiből (a nyilván nem igaz) $abs(A_1 − A_2) lt abs(A_1 - A_2)$
következne. Ezért csak $A_1 eq A_2$ lehet.

#pagebreak()

== A konvergencia és a korlátosság kapcsolata

Ha az $(a_n)$ sorozat konvergens, akkor korlátos is.

=== Bizonyítás

Tegyük fel, hogy $(a_n)$ konvergens és $lim(a_n) eq A in RR$. Válasszuk a konvergencia definíciója szerinti jelöléssel $epsilon$-t 1-nek. Ehhez a hibakorláthoz

$ exists n_0 in NN, forall n gt n_0: abs(a_n - A) lt 1 $

Így

$ abs(a_n) eq abs((a_n - A) + A) lt.eq abs(a_n - A) + abs(A) lt 1 + abs(A) space space space (n gt n_0) $

Ha $n lt.eq n_0$, akkor

$ abs(a_n) lt.eq max{abs(a_0),abs(a_1),dots,abs(a_n_0)} $

Legyen

$ K colon.eq max{abs(a_0),abs(a_1),dots,abs(a_n_0), 1 + abs(A)} $

Ekkor $abs(a_n) lt.eq K$ minden $n in NN$ indexre,és ez azt jelenti, hogy $(a_n)$ sorozat korlátos.

#pagebreak()

== Monoton részsorozatok létezésére vonatkozó tétel

Minden $a eq (a_n)$ valós sorozatnak létezik monoton részsorozata, azaz létezik olyan $v eq (v_n)$ indexsorozat, amellyel $a compose v$ monoton növekvő vagy monoton csökkenő.

=== Bizonyítás

Az állítás igazolásához bevezetjük egy sorozat csúcsának a fogalmát: Azt mondjuk, hogy $a_n_0$ az $(a_n)$ sorozat csúcsa (vagy csúcseleme), ha

$ forall n gt.eq n_0 "indexre" a_n lt.eq a_n_0 $


Két eset lehetséges:

+ A sorozatnak végtelen sok csúcsa van. Ez azt jelenti, hogy $ exists v_0 in NN: a_v_0 "csúcselem, azaz " forall n gt.eq v_0: a_n lt.eq a_v_0 $ $ exists v_1 gt v_0: a_v_1 "csúcselem, azaz " forall n gt.eq v_1: a_n lt.eq a_v_1 (lt.eq a_v_0) $ Ezek a lépések folytathatók, mert végtelen sok csúcselem van. Így olyan $v_0 lt v_1 lt v_2 lt dots$ indexsorozatot kapunk, amelyre $ a_v_0 gt.eq a_v_1 gt.eq a_v_2 gt.eq dots"," $ ezért a csúcsok $(a_v_n)$ sorozata $(a_n)$-nek egy monoton csökkenő részsorozata.

+ A sorozatnak legfejlebb véges sok csúcsa van. Ez azt jelenti, hogy $ exists N in NN, forall n gt.eq N "esetén" a_n "már nem csúcs" $ Mivel $a_N$ nem csúcselem, ezért $ exists v_0 gt N: a_v_0 gt a_N $ Azonban $a_v_0$ sem csúcselem, ezért $ exists v_1 gt v_0: a_v_1 gt a_v_0 (gt a_N) $ Az eljárást folytatva most olyan $v_0 lt v_1 lt v_2 lt dots$ indexsorozatot kapunk, amelyre $ a_v_0 lt a_v_1 lt a_v_2 lt dots $ Ebben az esetben tehát $(a_v_0)$ sorozat $(a_n)$-nek egy (szigorúan) monoton növekvő részsorozata.

#pagebreak()

== A sorozatokra vonatkozó közrefogási elv

Tegyük fel, hogy az $(a_n), (b_n), (c_n)$ sorozatokra teljesülnek a következők:

#list(
  $ exists N in NN, forall n gt N: a_n lt.eq b_n lt.eq c_n$,
  $ "az" (a_n) "és a" (c_n) "sorozatnak van határértéke, továbbá"$
)

$ lim(a_n) eq lim(c_n)  eq A in macron(RR) $

Ekkor a $(b_n)$ sorozatnak is van határértéke és $lim(b_n) eq A$



#set enum(numbering: "1.")

=== Bizonyítás
Három eset lehetséges:\
*1. eset:* $A in RR$ Legyen $epsilon gt 0$  tetszőleges valós szám. $lim(a_n) = lim(c_n) = A$ azt jelenti, hogy $(a_n) "és" (c_n)$ azonos A határértékkel rendelkező konvergens sorozatok. A konvergencia definíciója szerint tehát

$ exists n_1 in NN, forall n gt n_1 : A - epsilon lt a_n lt A + epsilon $
$ exists n_2 in NN, forall n gt n_2 : A - epsilon lt c_n lt A + epsilon $

Legyen $n_0 colon.eq max{N, n_1, n_2}.$ Ekkor $forall n gt n_0$ indexre

$ A - epsilon lt a_n lt.eq b_n lt.eq c_n lt A + epsilon $

Ez az jelenti, hogy

$ abs(b_n - A) lt epsilon, space "ha" n gt n_0 $

azaz a $(b_n)$ sorozat konvergens, tehát van határértéke, és $lim(b_n) = A$

*2. eset:* $A eq +infinity$ Tegyük fel, hogy $P gt 0$ tetszőleges valós szám. A $lim(a_n) eq +infinity$ értelmezése szerint

$ exists n_1 in NN, forall n gt n_1 : a_n gt P $

Legyen $n_0 colon.eq max{N, n_1}.$ Ekkor $forall n gt n_0$ indexre

$ P lt a_n lt.eq b_n $

és ez azt jelenti hogy $lim(b_n) eq +infinity$

*3. eset:* $A eq -infinity$ Tegyük fel, hogy $P lt 0$ tetszőleges valós szám. A $lim(c_n) eq -infinity$ értelemzése szerint

$ exists n_1 in NN, forall n gt n_1 : c_n lt P $

Legyen $n_0 colon.eq max{N,n_1}$, akkor $forall n gt n_0$ indexre

$ P gt c_n gt.eq b_n $

Ez pedig azt jelenti, hogy $lim(b_n) eq -infinity$

#pagebreak()

== Műveletek nullsorozatokkal

Tegyük fel, hogy $lim(a_n) = 0 "és" lim(b_n) = 0$

Ekkor

+ $(a_n + b_n)$ is nullsorozat,
+ ha $(c_n)$ korlátos sorozat, akkor $(c_n dot.op a_n)$ is nullsorozat
+ $(a_n dot.op b_n)$ is nullsorozat

=== Bizonyítás

*1.* Mivel $lim(a_n) = lim(b_n) = 0, "ezért" forall epsilon gt 0"-hoz"$
$ exists n_1 in NN, forall n gt n_1 : abs(a_n) lt epsilon/2 $

$ exists n_2 in NN, forall n gt n_2 : abs(b_n) lt epsilon/2 $

Legyen $n_0 colon.eq max{n_1,n_2}$. Ekkor $forall n gt n_0$ indexre

$ abs(a_n + b_n) lt.eq abs(a_n) + abs(b_n) lt epsilon/2 + epsilon/2 eq epsilon, $

és ez azt jelenti, hogy $lim(a_n + b_n) = 0$, azaz $(a_n + b_n)$ valóban nullsorozat.

*2.* A $(c_n)$ sorozat korlátos, ezért

$ exists K gt 0 : abs(c_n) lt K (n in NN) $

Mivel $(a_n)$ nullsorozat, ezért

$ forall epsilon gt 0"-hoz" exists n_0 in NN,  forall n gt n_0 : abs(a_n) lt epsilon/K, $

következésképpen minden $ n gt n_0$ indexre

$ abs(c_n dot.op a_n) eq abs(c_n) dot.op abs(a_n) lt K dot.op epsilon/K eq epsilon, $

azaz $lim(c_n dot.op a_n) eq 0.$

*3.* Mivel minden konvergens sorozat korlátos, ezért a $lim(b_n) = 0$ feltételből következik, hogy $(b_n)$ korlátos sorozat. Az állítás tehát a 2. állítás közvetlen következménye.

#pagebreak()

== Konvergens sorozatok szorzatára vonatkozó tétel

Tegyük fel, hogy az $(a_n)$ és a $(b_n)$ sorozat konvergens. Legyen

$ lim(a_n) = A in RR "és" lim(b_n) = B in RR $

Ekkor

$(a_n dot.op b_n)$ is konvergens és $lim(a_n dot.op b_n) = lim(a_n) dot.op lim(b_n) = A dot.op B$

#set math.cases(reverse: true)
=== Bizonyítás

(\*) #h(weak: true,20pt)$(x_n)$ konvergens, és $alpha in RR$ a határértéke $arrow.r.l.double.long (x_n - alpha)$ nullsorozat

(\*) miatt elég megmutatni, hogy $(a_n b_n - A B)$ nullsorozat. Ez a következő átalakítással igazolható:

$ a_n b_n - A B = a_n b_n - A b_n + A b_n - A B = underbrace(underbrace(underbrace(b_n, "korlátos") dot.op underbrace((a_n - A),"nullsorozat"),"nullsorozat") + underbrace(underbrace(A,"korlátos") dot.op underbrace((b_n - B),"nullsorozat"), "nullsorozat"),"nullsorozat") $

A fenti gondolatmenetben a $(b_n)$ sorozat azért korlátos, mert konvergens.

#pagebreak()

== Konvergens sorozatok hányadosára vonatkozó tétel

Tegyük fel, hogy az $(a_n) "és a" (b_n)$ sorozat konvergens. Legyen
$ lim(a_n) = A in RR "és" lim(b_n) = B in RR $

Ekkor ha $b_n != 0 (n in NN) "és" lim(b_n) != 0$, akkor
$ (a_n/b_n) "is konvergens, és" lim(a_n/b_n) = lim(a_n)/lim(b_n) = A/B $

=== Bizonyítás
(\*) $(x_n)$ konvergens, és $alpha in RR$ a határértéke $arrow.r.l.long.double (x_n - alpha)$ nullsorozat.
=== Segédtélel:
Ha $b_n != 0 (n in NN)$ és $(b_n)$ konvergens, továbbá $B colon.eq lim(b_n) != 0$, akkor az
$ (1/b_n) $
reciprok-sorozat korlátos.\
Ennek bizonyításához legyen $epsilon colon.eq abs(B)/2$. Ekkor egy alkalmas $n_0 in NN$ küszöbindex mellett
$ abs(b_n - B) lt epsilon eq abs(B)/2 space space forall n gt n_0 "indexre." $
Így minden $n gt n_0$ esetén
$ abs(b_n) gt.eq abs(B) - abs(b_n - B) gt abs(B) - abs(B)/2 = abs(B)/2 $

hiszen $abs(B) eq abs(B - b_n + b_n) lt.eq abs(B-b_n) + abs(b_n)$. Tehát

$ abs(1/b_n) lt 2/abs(B)," ha " n gt n_0, $
következésképpen az
$ abs(1/b_n) lt.eq max{1/abs(b_0),1/abs(b_1),....,1/abs(b_n_0), 2/abs(B)} $
egyenlőtlenség már minden $n in NN$ számra teljesül, ezért az $(a/b_n)$ sorozat valóban korlátos. A segédtételt tehát bebizonyítottuk.\
\
Most az látjuk be, hogy az
$ (1/b_n) "sorozat konvergens és" lim(1/b_n) = 1/B $
Ez (\*)-ből következik az alábbi átalakítással:
$ 1/b_n - 1/B eq (B - b_n)/(B dot.op b_n) eq underbrace(underbrace(1/(B dot.op b_n),"korlátos") dot.op underbrace((B - b_n),"nullsorozat"),"nullsorozat") $
Az állítás bizonyításának a befejezéséhez már csak azt kell figyelembe venni, hogy
$ a_n/b_n eq a_n dot.op 1/b_n space space space (n in NN) $
más szóval az $(a_n/b_n)$ hányados-sorozat két konvergens sorozat szorzata. Így a 2. állítás (konvergens sorozat szorzata) és a reciprok sorozatról az előbb mondottak miatt
$ (a_n/b_n) "is konvergens és" lim(a_n/b_n) eq A dot.op 1/B = A/B = lim(a_n)/lim(b_n) $

#pagebreak()

== Monoton növekvő sorozatok határértékére vonatkozó tétel (véges és végtelen eset)

Minden $(a_n)$ monoton sorozatnak van határértéke.
1. Ha $(a_n) arrow.tr$ és felülről korlátos, akkor $(a_n)$ konvergens és
$ lim(a_n) = sup{a_n | n in NN} $
2. Ha $(a_n) arrow.tr$ és felülről nem korlátos, akkor $lim(a_n) = +infinity$

=== Bizonyítás

1. Tegyük fel, hogy az $(a_n)$ sorozat monoton növekvő és felülről korlátos. Legyen
$ A colon.eq sup{a_n | n in NN} in RR. $
Ez azt jelenti, hogy $A$ a szóban forgó halmaznak a legkisebb felső korlátja, azaz
#list($forall n in NN : a_n lt.eq A "és"$,
$forall epsilon gt 0"-hoz" exists n_0 in NN : A - epsilon lt a_"n0" lt.eq A.$)
Mivel a feltételezésünk szerint az $(a_n)$ sorozat monoton növekvő, ezért az
$ A - epsilon lt a_"n0" lt.eq a_n lt.eq A. $
becslés is igaz minden $n gt n_0$ indexre. Azt kaptuk tehát, hogy
$ forall epsilon gt 0"-hoz" exists n_0 in NN, forall n gt n_0 : abs(a_n -A) lt epsilon. $
Ez pontosan azt jelenti, hogy az $(a_n)$ sorozat konvergens, és $lim(a_n) = A$.\
\
2. Tegyük fel, hogy az $(a_n)$ sorozat monoton növekvő és felülről nem korlátos. Ekkor
$ forall P > 0"-hoz" exists n_0 in NN : a_"n0" gt P. $
A monotonitás miatt ezért egyúttal az is igaz, hogy
$ forall n gt n_0 : a_n gt.eq a_"n0" gt P, $
és ez pontosan azt jelenti, hogy $lim(a_n) eq +infinity.$

#pagebreak()

== Az $a_n colon.eq (1 + 1 / n)^n (n in NN^(+))$ sorozat konvergenciája

Az $ a_n colon.eq (1 + 1 / n)^n (n in NN^(+)) $ sorozat szigorúan monoton növekvő és felülről korlátos, tehát konvergens. Legyen
$ e colon.eq limits(lim)_(n arrow.r +infinity)(1+1/n)^n. $

=== Bizonyítás
Az állítást a számtani és a mértani közép közötti egyenlőtlenség „ötletes”
felhasználásaival bizonyítjuk.
- A monotonitás igazolásához az egyenlőtlenséget az $(n+1)$ darab
$ 1, 1+1/n, 1+ 1/n, ... space, 1+1/n $
számra alkalmazzuk. Mivel ezek nem mind egyenlők, ezért
$ root(n+1,1 dot.op (1+1/n)^n) lt (1+n dot.op (1+1/n))/(n+1) eq (n+2)/(n+1) = 1 +1/(n+1) $
Mindkét oldalt $(n+1)$-edik hatványra emelve azt kapjuk, hogy
$ a_n eq (1+1/n)^n lt (1+ 1/(n+1))^(n+1) eq a_(n+1) (n in NN^(+)) $
amivel beláttuk, hogy a sorozat szigorúan monoton növekvő.
- A korlátosság bebizonyításához most az $(n+2)$ darab
$ 1/2, 1/2, 1+1/n, 1+ 1/n, ... space, 1+1/n  $
számra alkalmazzuk ismét a számtani és a mértani közép közötti egyenlőtlenséget:
$ root(n+2,1/2 dot.op 1/2 dot.op (1+1/n)^n) lt (2 dot.op 1/2 + n dot.op (1+1/n))/(n+2) eq (n+2)/(n+2) = 1 $
Ebből következik, hogy
$ a_n eq (1+1/n)^n lt 4 space space(n in NN^(+)) $
ezért a sorozat felülről korlátos.\
A monoton sorozatok határértékére vonatkozó tételből következik, hogy a sorozat konvergens.

#pagebreak()

#show heading.where(level: 2): it => it.body
#show heading.where(level: 2): it => block(
  fill: colorT,
  inset: 10pt,
  radius: 4pt,
)[#it]

== A végtelen sorokra vonatkozó Cauchy-féle konvergenciakritérium

A $sum a_n$ sor akkor és csak akkor konvergens, ha

$ forall epsilon gt 0"-hoz" exists n_0 in NN, forall m gt n gt n_0 colon abs(a_(n plus 1) plus a_(n plus 2) plus dots plus a_m) lt epsilon $

=== Bizonyítás

Tudjuk, hogy

$ sum a_n "konvergens" &arrow.double.l.r.long &(s_n) "konvergens" &arrow.double.l.r.long (s_n) "Cauchy-sorozat" $

azaz

$ forall epsilon gt 0"-hoz" exists n_0 in NN, forall n, m gt n_0 colon abs(s_m minus s_n) lt epsilon $

teljesül. Állításunk abból következik, hogy ha $m gt n$, akkor

$ s_m minus s_n eq a_(n plus 1) plus a_(n plus 2) plus dots plus a_m $

#pagebreak()

== Végtelen sorokra vonatkozó összehasonlító kritériumok
\
Legyenek $sum(a_n) " és " sum(b_n)$ nemnegatív tagú sorok. Tegyük fel, hogy

$ exists N in NN, forall n gt.eq N : 0 lt.eq a_n lt.eq b_n $

Ekkor

1. #strong("Majoráns kritérium"): ha a $sum(b_n)$ sor konvergens, akkor $sum(a_n)$ sor is konvergens.
2. #strong("Minoráns kritérium"): ha a $sum(a_n)$ sor divergens, akkor $sum(b_n)$ sor is divergens

=== Bizonyítás

Az általánosság megszorítása nélkül feltehetjük, hogy $a_n lt.eq b_n$ minden
$n in NN$ esetén, hiszen véges sok tag megváltozásával egy sor konvergenciája nem változik. Jelölje $(s_n)$, illetve $(t_n)$ a $sum(a_n)$, illetve a $sum(b_n)$ sorok részletösszegeiből álló sorozatokat. A feltevésünk miatt $s_n lt.eq t_n (n in NN)$. Ekkor a nemnegatív tagú sorok konvergenciáról szóló tétel szerint

1. ha a $sum(b_n)$ sor konvergens, akkor $(t_n)$ korlátos, így $(s_n)$ is az. Ezért a $sum(a_n)$ sor is konvergens.

2. ha $sum(a_n)$ sor divergens, akkor $(s_n)$ nem korlátos, így $(t_n)$ sem az. Ezért a $sum(b_n)$ sor is divergens.
#pagebreak()

== A Cauchy-féle gyökkritérium

Tekintsük a $sum(a_n)$ végtelen sort, és tegyük fel, hogy létezik az

$ A := lim_(n arrow +infinity) root(n,abs(a_n)) in macron(RR) $

határérték. Ekkor

1. $0 lt.eq A lt 1$ esetén a $sum(a_n)$ sor abszolút konvergens (tehát konvergens is),
2. $A gt 1$ esetén a $sum(a_n)$ sor divergens
3. $A eq 1$ esetén a $sum(a_n)$ sor lehet konvergens is, divergens is

=== Bizonyítás
Mivel $root(n, abs(a_n)) gt.eq 0 (n in NN)$, ezért $A gt.eq 0$.

1. Tegyük fel, hogy $0 lt.eq A lt 1$
Vegyünk egy $A$ és 1 közötti $q$ számot!

$ lim(root(n,abs(a_n))) lt q arrow.double.long exists n_0 in NN, forall n gt n_0 : root(n,abs(a_n)) lt q, "azaz" abs(a_n) lt q^n $

Mivel $0 lt q lt 1$, ezért a $sum(q^n)$ mértani sor konvergens. Így a majoráns kritérium szerint a $sum(abs(a_n))$ sor is konvegens, és ez azt jelenti, hogy a $sum(a_n)$ végtelen sor abszolút konvergens.

2. Tegyük fel, hogy $A gt 1$
Vegyünk most egy 1 és $A$ közötti $q$ számot!

$ lim(root(n, abs(a_n))) gt q arrow.r.double.long exists n_0 in NN, forall n gt n_0 : root(n, abs(a_n)) gt q, "azaz" abs(a_n) gt q^n $

Tehát, véges sok $n$ indextől eltekintve $abs(a_n) gt q^n gt 1$\
Ebből következik, hogy $lim(a_n) != 0$, és így a $sum(a_n)$ sor divergens.

3. Tegyük fel, hogy $A eq 1$. Ekkor

a $sum(1/n)$ divergens sor esetében $abs(a_n) eq 1/n$, azaz $ lim_(n arrow +infinity)root(n,abs(a_n)) eq lim_(n arrow + infinity)1/(root(n,n)) eq 1 $

a $sum(1/n^2)$ konvegens sor esetében $abs(a_n) eq 1/n^2$, azaz $ lim_(n arrow +infinity)root(n,abs(a_n)) eq lim_(n arrow + infinity)1/(root(n,n^2)) eq 1 $

#pagebreak()
== A d'Alembert-féle hányadoskritérium
\
Tegyük fel, hogy a $sum(a_n)$ végtelen sor tagjai közül egyik sem 0 és létezik az
$ A := lim_(n arrow + infinity)abs(a_(n+1)/a_n) in macron(RR) $
határérték. Ekkor\
1. $0 lt.eq A lt 1$ esetén a $sum(a_n)$ sor abszolút konvergens (tehát konvergens is),

2. $A > 1$ esetén a $sum(a_n)$ sor divergens,

3. $A eq 1$ esetén a $sum(a_n)$ sor lehet konvegens is, divergens is.

=== Bizonyítás
\
Világos, hogy $A gt.eq 0$.\
1. Legyen $0 lt.eq A lt 1$ és vegyünk egy olyan $q$ számot, amire $A lt q lt 1$ teljesül. Ekkor

$ lim_(n arrow +infinity)(abs(a_(n+1)))/(abs(a_n)) lt q arrow.double.long exists n_0 in NN, forall n gt.eq n_0 : (abs(a_(n+1)))/(abs(a_n)) lt q, "azaz" abs(a_(n+1)) lt q abs(a_n) $

Ez azt jelenti, hogy

$ abs(a_(n_0+1)) lt q abs(a_n_0), abs(a_(n_0+2)) lt q abs(a_(n_0+1)), ... , abs(a_(n-1)) lt q abs(a_(n-2)), abs(a_(n)) lt q abs(a_(n-1)) $

minden $n gt.eq n_0$ esetén. Így

$ abs(a_n) lt q abs(a_(n-1)) lt q^2 abs(a_(n-2)) lt ... lt q^(n-n_0) abs(a_n_0) eq q^(-n_0) abs(a_n_0) q^n eq a q^n $

ahol $a := q^(-n_0) abs(a_n_0)$ egy n-től független konstans. A $sum(a q^n)$ mértani sor konvergens, mert $0 lt q lt 1$. Ezért a majoráns kritérium szerint a $sum(abs(a_n))$ sor is konvergens, vagyis a $sum(a_n)$ végtelen sor abszolút konvergens.

2. Legyen $A gt 1$ és vegyünk most egy olyan $q$ számot, amire $1 lt q lt A$ teljesül. Ekkor

$ lim_(n arrow +infinity) (abs(a_(n+1)))/(abs(a_n)) gt q arrow.double.long exists n_0 in NN, forall n gt.eq n_0 : (abs(a_(n+1)))/(abs(a_n)) gt q, "azaz" abs(a_(n+1)) gt q abs(a_n) gt abs(a_n) $

Ebből következik, hogy a $lim(a_n) != 0$, így a $sum(a_n)$ sor divergens.

3. Tegyük fel, hogy $A eq 1$. Ekkor
\
$sum(1/n)$ divergens sor esetében $abs(a_n) = 1/n$, azaz $lim_(n arrow +infinity) abs(a_(n+1))/abs(a_n) eq lim_(n arrow + infinity) n/(n+1) eq 1$
\
\
$sum(1/n^2)$ konvergens sor esetében $abs(a_n) eq 1/n^2$azaz $lim_(n arrow infinity) abs(a_(n+1))/abs(a_n) eq lim_(n arrow infinity) n^2/(n+1)^2 eq 1$
#pagebreak()

== Leibniz-típusú sorok konvergenciája

=== Definíció

A $0 lt.eq a_(n+1) lt.eq a_n (n in NN^+)$ feltételt kielégítő sorozatból képzett

$ ∑_(n eq 1) (−1)^(n + 1) a_n eq a_1 − a_2 + a_3 − a_4 + dots $

váltakozó előjelű sort *Leibniz-típusú sornak* nevezzük.

*Konvergencia:* A $sum_(n eq 1) (−1)^(n + 1) a_n$ Leibniz-típusú sor akkor és csak akkor konvergens, ha $lim(a_n) eq 0$.

=== Bizonyítás

$arrow.double$) A sorok konvergenciájának szükséges feltétele értelmében, ha a $sum (−1)^(n + 1) a_n$ sor konvergens, akkor $lim((−1)^(n + 1) a_n) eq 0$, ami csak akkor lehetséges, ha $lim(a_n) eq 0$.

$arrow.double.l$) Tegyük fel, hogy $sum_(n eq 1) (−1)^(n + 1)a_n$ egy Leibniz-típusú sor, és $lim(a_n) eq 0$. Igazoljuk, hogy a sor konvergens. Legyen

$ s_n colon.eq sum_(k eq 1)^n (-1)^(k + 1) a_k eq a_1 - a_2 + a_3 - a_4 + a_5 - dots + (-1)^(n + 1) a_n space space (n in NN^+) $

Szemléltessük az $(s_n)$ részletösszeg-sorozat első néhány tagját!

#v(20pt)

#grid(
  columns: (auto, auto),
  gutter: 75pt,
  [
    #cetz.canvas({
      import cetz.draw: *

      set-style(mark: (end: "straight"))
      line((), (rel: (10, 0), update: true), name: "tengely")
      content(
        "tengely.end",
        [
          #v(25pt)
          $RR$
        ]
      )
      circle(
        ("tengely.start",1,"tengely.end"),
        radius: .1,
        name: "s2",
        fill: black,
      )
      content(
        "s2.center",
        (0,0),
        [$s_2$]
      )
      circle(
        ("tengely.start",2.47,"tengely.end"),
        radius: .1,
        name: "s4",
        fill: black,
      )
      content(
        "s4.center",
        (0,0),
        [$s_4$]
      )
      circle(
        ("tengely.start",4,"tengely.end"),
        radius: .1,
        name: "s5",
        fill: black,
      )
      content(
        "s5.center",
        (0,-1),
        padding: -.7,
        [$s_5$]
      )
      circle(
        ("tengely.start",5.75,"tengely.end"),
        radius: .1,
        name: "s3",
        fill: black,
      )
      content(
        "s3.center",
        (0,-1),
        padding: -.7,
        [$s_3$]
      )
      circle(
        ("tengely.start",7.75,"tengely.end"),
        radius: .1,
        name: "s1",
        fill: black,
      )
      content(
        "s1.center",
        (0,0),
        [$s_1 eq a_1$]
      )
      arc(
        "s2.center",
        start: -180deg,
        stop: 0deg,
        radius: 2.38,
        name: "s2tos3"
      )
      content(
        (
          name: "s2tos3",
          anchor: 50%,
        ),
        [
          #pad(top: 25pt)[
            $a_3 (lt.eq a_2)$
          ]
        ]
      )
      arc(
        "s4.center",
        start: -180deg,
        stop: 0deg,
        radius: .78,
        name: "s4tos5"
      )
        content(
        (
          name: "s4tos5",
          anchor: 50%,
        ),
        [
          #pad(top: 25pt)[
            $a_5 (lt.eq a_4)$
          ]
        ]
      )
      arc(
        "s1.center",
        start: 0deg,
        stop: 180deg,
        radius: 3.38,
        name: "s1tos2"
      )
      content(
        (
          name: "s1tos2",
          anchor: 50%,
        ),
        [
          #pad(top: -15pt)[
            $a_2 (lt.eq a_1)$
          ]
        ]
      )
      arc(
        "s3.center",
        start: 0deg,
        stop: 180deg,
        radius: 1.65,
        name: "s3tos4"
      )
      content(
        (
          name: "s3tos4",
          anchor: 50%,
        ),
        [
          #pad(top: -15pt)[
            $a_4 (lt.eq a_3)$
          ]
        ]
      )
    })
  ],
  [
    #show math.equation: set align(left)

    $ s_1 eq a_1 \
    s_2 eq a_1 - a_2 eq s_1 - a_2 \
    s_3 eq a_1 - a_2 + a_3 eq s_2 + a_3 \
    s_4 eq a_1 - a_2 + a_3 - a_4 eq s_3 - a_4 \
    s_5 eq a_1 - a_2 + a_3 - a_4 + a_5 eq s_4 + a_5 \
    $
  ]
)

Most megmutatjuk, hogy az ábra alapján sejthető tendencia valóban igaz, azaz, hogy
az $(s_(2n))$ sorozat monoton növekvő, és az $(s_(2n+1))$ sorozat monoton csökkenő.

#pagebreak()

- A páros indexű részsorozatnál a következő csoportosításból látható, hogy $ s_(2n) eq overbrace(underbrace((a_1 − a_2), gt.eq 0) + underbrace((a_3 − a_4), gt.eq 0) + dots + underbrace((a_(2n−3) − a_(2n−2)), gt.eq 0), s_(2n-2)) + underbrace((a_(2n−1) − a_(2n)), gt.eq 0) $ minden $n in NN^+$ esetén, tehát $(s_(2n))$ valóban monoton növekvő.
- Hasonlóan, a páratlan indexű részsorozatnál $ s_(2n+1) eq overbrace(a_1 + underbrace((-a_2 + a_3), lt.eq 0) + underbrace((-a_4 + a_5), lt.eq 0) + dots + underbrace((-a_(2n−2) + a_(2n−1)), lt.eq 0), s_(2n-1)) + underbrace((-a_(2n) + a_(2n+1)), lt.eq 0) $ minden $n in NN^+$ esetén, tehát $(s_(2n+1))$ monoton csökkenő sorozat.

Másrészt, az $s_0 colon.eq 0$ értelmezés mellett

$ s_(2n+1) − s_(2n) eq a_(2n+1) gt.eq 0 space space (n in NN) $

teljesül, amiből következik, hogy $s_(2n) lt.eq s_(2n+1)$ minden $n in NN$ esetén. Ekkor

$ (1) space space space s_2 lt.eq s_4 lt.eq s_6 lt.eq dots lt.eq s_(2n) lt.eq s_(2n+1) lt.eq dots lt.eq s_5 lt.eq s_3 lt.eq s_1 $

Tehát $(s_(2n))$ és $(s_(2n+1))$ korlátos sorozatok. Mivel mindkettő monoton és korlátos, ezért
konvergens is. Jelölje $A eq lim(s_(2n+1))$ és $B eq lim(s_(2n))$ a határértéküket. Ekkor

$ A - B eq lim_(n arrow + infinity) s_(2n+1) - lim_(n arrow + infinity) s_(2n) eq lim_(n arrow + infinity) (s_(2n+1) - s_(2n) ) eq lim_(n arrow + infinity) a_(2n+1) eq lim_(n arrow + infinity) a_n eq 0, $

hiszen $(a_(2n+1))$ részsorozata az $(a_n)$ sorozatnak. Ezért $A eq B$, tehát az $(s_(2n))$ és az
$(s_(2n+1))$ részsorozatok határértéke megegyezik. Ebből következik, hogy az $(s_n)$ sorozat
konvergens. Ez pedig azt jelenti, hogy a Leibniz-típusú sor valóban konvergens.

#pagebreak()

== Sorok téglányszorzatának konvergenciája
\
Tegyük fel, hogy a $sum_(n eq 0) a_n$ és a $sum_(n eq 0) b_n$ végtelen sorok konvergensek. Ekkor a $sum_(n eq 0) t_n$ téglányszorzatuk is konvergens és

$ sum_(n eq 0)^(+infinity) t_n eq sum_(n eq 0)^(+infinity) a_n dot.op sum_(n eq 0)^(+infinity) b_n $

azaz konvergens sorok téglányszorzata is konvergens, és a téglányszorzat összege a két sor összegének szorzatával egyezik meg.

=== Bizonyítás
\
A bizonyítás alapja a sorozatoknál tanult műveletek és határátmenet felcserélhetőségére vonatkozó tétel. Jelölje $A_n, B_n "és " T_n$ rendre a $sum_(n eq 0) a_n, sum_(n eq 0) b_n "és " sum_(n eq 0) t_n$ sorok n-edik részletösszegeit. Ekkor

$ T_n eq sum_(k eq 0)^n t_k eq sum_(k eq 0)^n (sum_(max{i,j} eq k) a_i b_j) eq sum_(max{i,j} lt.eq n) a_i b_j eq (sum_(i eq 0)^n a_i) dot.op (sum_(j eq 0)^n b_j) eq $
$ eq A_n B_n arrow (sum_(n eq 0)^(+infinity) a_n) dot.op (sum_(n eq 0)^(+infinity) b_n), "ha " n arrow +infinity $

Ez azt jelenti, hogy a $(T_n)$ sorozat konvergens, és így a $sum t_n$ végtelen sor is konvergens, és

$ sum_(n eq 0)^(+infinity) t_n eq lim(T_n) eq (sum_(n eq 0)^(+infinity) a_n) dot.op (sum_(n eq 0)^(+infinity) b_n) $
#pagebreak()

== Hatványsorok konvergenciasugara
Tetszőleges $sum_(n eq 0) alpha_n (x-a)^n$ hatványsor konvergenciahalmazára a következő három eset egyike áll fenn:

1. $exists 0 lt R lt +infinity$, hogy a haványsor $forall x in RR : abs(x-a) lt R$ pontban abszolút konvegens és $forall x in RR : abs(x-a) gt R$ pontban divergens.

2. A hatványsor csak az $x eq a$ pontban konvergens. Ekkor legyen $R := 0$

3. A hatványsor abszolút konvergens $forall x in RR$ esetében. Ekkor legyen $R := +infinity$.

R-et a hatványsor konvergenciasugarának nevezzük.

=== Bizonyítás
Az állítás elég $a eq 0$ esetén igazolni.

==== Segédtétel
Tegyük fel, hogy a $sum alpha_n x^n$ hatványsor konvergens egy $x_0 eq.not 0$ pontban. Ekkor $forall x in RR : abs(x) lt abs(x_0)$ esetén a hatványsor abszolút konvegens az x pontban.

==== Segédtétel bizonyítása
Mivel a $sum alpha_n x_0^n$ végtelen sor konvergens, ezért $lim(a_n x_0^n) eq 0$, így az $(a_n x_0^n)$ sorozat korlátos, azaz

$ exists M gt 0 : abs(alpha_n x_0^n) lt.eq M lt +infinity space (n in NN) $

Legyen $x in RR$ olyen, amire $abs(x) lt abs(x_0)$ teljesül. Ekkor

$ abs(alpha_n x^n) eq abs(alpha_n x_0^n) dot.op abs(x/x_0)^n lt.eq M dot.op abs(x/x_0)^n =: M q^n space (n in NN) $

A $sum abs(alpha_n x^n) $ végtelen sor tehát majorálható a $sum(M q^n)$ mértani sorral, ami konvergens, mert $abs(q) eq abs(x/x_0) lt 1$. Így a majoráns kritérium szerint a $sum abs(alpha_n x^n)$ sor is konvergens, tehát a $sum(alpha_n x^n)$ végtelen sor is konvergens.

==== Tétel bizonyítása
Tekintsük a $sum alpha_n x^n$ hatványsort. Ez $x eq 0$-ban nyilván konvergens, ezért $K H(sum alpha_n x^n) eq.not emptyset$, és így

$ exists sup K H (sum_(n eq 0) alpha_n x^n) =: R in macron(RR) "és " R gt.eq 0 $

A következő három eset lehetséges

1. $0 lt R lt +infinity$. Legyen $abs(x) lt R$ tetszőleges. Ekkor a szuprémum definíciója szerint $exists x_0 gt 0 : abs(x) lt x_0 lt R$ és $x_0$ a konvergenciahalmaz eleme, azaz $sum alpha_n x_0^n$ konvergens. Ekkor a segédtétel szerint $sum alpha_n x^n$ abszolút konvergens. Ha $abs(x) gt R$ tetszőleges, akkor az R szám definíciója és a segédtétel szerint a $sum alpha_n x^n$ sor divergens.

2. $R eq 0$. A $sum alpha_n x^n$ hatványsor az $x eq 0$ pontban nyilván konvergens. Tegyük fel, hogy $x eq.not 0$ olyan pont ahol $sum alpha_n x^n$ konvergens. Ekkor a segédtétel szerint a hatványsor konvergens az $abs(x)/2 gt 0$ pontban, ami nem lehetségesm mert $R = 0$. A hatványsor tehát csak az $x eq 0$ pontban konvergens.

3. $R eq +infinity$. Legyen $x in RR$ tetszőleges. Ekkor a szuprémum definíciója értelmében $exists x_0 gt 0 : abs(x) lt x_0$ és $x_0$ a konvergenciahalmaz eleme, azaz $sum alpha_n x_0^n$ konvergens. Ekkor a segédtétel szerint $sum alpha_n x^n$ abszolút konvergens.

#pagebreak()

== A Cauchy-Hadamard-tétel
\
Tekintsük a $sum_(n eq 0) alpha_n (x-a)^n$ hatványsort, és tegyük fel, hogy

$ exists lim(root(n, abs(alpha_n))) =: A in macron(RR) $

Ekkor a hatványsor konvergenciasugara

$ R = 1/A space (1 / (+infinity) := 0, 1/0 := +infinity) $

=== Bizonyítás
\
Nyilvánvaló, hogy $A gt.eq 0$. Rögzítsük tetszőlegesen az $x in RR$ számot, és alkamazzuk a Cauchy-féle gyökkritériumot a $ sum alpha_n(x-a)^n$ végtelen számsorra:

$ lim_(n arrow +infinity) root(n, abs(alpha_n (x-a)^n)) eq (lim_(n arrow +infinity) root(n, abs(alpha_n)) dot.op abs(x-a) eq A abs(x-a), "és így" $

$ A abs(x-a) lt 1 arrow.long.double "a sor konvergens", space A abs(x-a) gt 1 arrow.long.double "a sor divergens." $

1. Ha $0 lt a lt +infinity$, akkor A-val lehet osztani, és akkor
$ x in ( a - 1/A, a+ 1/A) arrow.double.long " a sor konv.," x in.not [a - 1/A, a+ 1/A] arrow.long.double "a sor div." $

amiből következik, hogy $R eq 1/A$

2. Ha $ A eq +infinity$, akkor $forall x in RR, x != a: A abs(x-a) eq (+infinity) dot.op abs(x-a) eq +infinity gt 1$\
Ezért a hatványsor az $x eq a$ pont kivételével divergens, azaz $R eq 0$

3. Ha $A eq 0$, akkor $forall x in RR: A abs(x-a) eq 0 dot.op abs(x-a) eq  eq 0 lt 1$\
Ezért a hatványsor minden $x in RR$ pontban konvergens, azaz $R eq +infinity$
#pagebreak()

== Függvények határértékének egyértelműsége
\
Ha az $f in RR arrow.long RR$ függvénynek az $a in D^'_f$ pontban van határértéke, akkor a definícióban szereplő $A in macron(RR)$ egyértelműen létezik.

=== Bizonyítás
\
Tegyük fel, hogy két különböző $A_1, A_2 in macron(RR)$ elem eleget tesz a definíció feltételeinek. Mivel két különböző $macron(RR)$-beli elem diszjunkt környezetekkel szétválasztható ezért

$ exists epsilon gt 0 : K_epsilon (A_1) sect K_epsilon (A_2) eq emptyset $

A határérték definíciója szerint egy ilyen $epsilon$-hoz

$ exists delta_1 gt 0, forall x in K_delta_1 (a) sect D_f : f(x) in K_epsilon (A_1) $

$ exists delta_2 gt 0, forall x in K_delta_2 (a) sect D_f : f(x) in K_epsilon (A_2) $

Legyen $delta := min{delta_1, delta_2}$. Ekkor

$ forall x in K_delta (a) sect D_f : f(x) in K_epsilon (A_1) sect K_epsilon (A_2) eq emptyset, "de " K_delta (a) sect D_f != emptyset, "mert " a in D^'_f. $

Ellentmondásra jutottunk, és ezzel a határérték egyértelműségét igazoltuk.
#pagebreak()
== A határértékre vonatkozó átviteli elv
\
Legyen $f in RR arrow RR, a in D^'_f "és " A in macron(RR)$. Ekkor

$ lim_a f eq A arrow.l.r.double.long forall(x_n) : NN arrow D_f \\ {a}, lim_(n arrow +infinity) x_n eq a "esetében " lim_(n arrow +infinity) f(x_n) eq A $

=== Bizonyítás
$arrow.double.r space space lim_a f eq A arrow.double.long forall epsilon gt 0"-hoz" exists delta gt 0, forall x in K_delta (a) sect D_f : f(x) in K_epsilon (A).$

Legyen $(x_n)$ egy, a tételben szereplő sorozat, és $epsilon gt 0$ egy tetszőleges rögzített érték.

$ lim x_n eq a arrow.long.double delta"-hoz" exists n_0 in NN, forall n gt n_0 : x_n in K_delta (a) $

Mivel $x_n in D_f \\ {a}$, így $x_n in K_delta (a) sect D_f$, amiből $f(x_n) in K_epsilon (A)$ teljesül minden $n gt n_0$ indexre. Ez azt jelenti, hogy az $(f(x_n))$ sorozatnak van határértéke, és $lim_(n arrow +infinity) f(x_n) eq A$

$arrow.l.double$ Tegyük fel, hogy

$ forall(x_n) : NN arrow D_f \\ {a}, lim_(n arrow +infinity) x_n eq a "esetén " lim_(n arrow +infinity) f(x_n) eq A. $

Megmutatjuk, hogy $lim_a f = A$

Indirekt módon tegyük fel, hogy a $lim_a f = A$ egyenlőség nem igaz. Ez pontosan azt jelenti, hogy

$ exists epsilon gt 0, forall delta gt 0"-hoz" exists x_delta in K_delta (a) sect D_f : f(x_delta) in.not K_epsilon (A) $

A $delta eq 1/n (n in NN^+)$ választással ez azt jelenti, hogy

$ exists epsilon gt 0, forall n in NN^+"-hoz" exists x_n in K_(1/n) (a) sect D_f : f(x_n) in.not K_epsilon (A) $

Legyen $x_0 in D_f \\ {a}$ tetszőleges. Az $(x_n) : NN arrow D_f \\ {a}$ sorozat nyilván a-hoz tart (hiszen $x_n in K_(1/n) (a)$), de a függvényértékek $(f(x_n))$ sorozata nem tart A-hoz (hiszen $f(x_n) in.not K_epsilon (A)$), ami ellentmond a feltételünknek.
#pagebreak()
== Monoton függvények hatértékei
\
Legyen $(alpha, beta) subset RR$ tetszőleges (korlátos vagy nem korlátos) nyílt intervallum.
Ha az f függvény monoton $(alpha, beta)$-n, akkor f-nek $forall a in (alpha, beta)$ pontban létezik a jobb oldali,
illetve a bal oldali határértéke, és ezek végesek.
\
1. Ha f $arrow.tr (alpha,beta)$-n, akkor

$ lim_(a+0) f eq inf{f(x) | x in (alpha, beta), x gt a} $
$ lim_(a-0) f eq sup{f(x) | x in (alpha, beta), x lt a} $

2, Ha f $arrow.br (alpha, beta)$-n, akkor

$ lim_(a+0) f = sup{f(x) | x in (alpha, beta), x gt a} $
$ lim_(a-0) f = inf{f(x) | x in (alpha,beta), x lt a} $
=== Bizonyítás
Tegyük fel, hogy $f arrow.tr (alpha,beta)-n$. A jobb oldali határértékre vonatkozó állítást igazoljuk.
Legyen

$ m := inf{f(x) | x in (alpha,beta), x gt a} $

Világos, hogy $m in RR$. Az infimum definíciójából következik, hogy


1. $forall x in (alpha, beta), x gt a : m lt.eq f(x)$
2. $forall epsilon gt 0"-hoz" exists x_1 in (alpha,beta), x_1 gt a : f(x_1) lt m + epsilon$

Így $m lt.eq f(x_1) lt.eq m + epsilon$. Mivel $f arrow.tr (alpha,beta)$-n, ezért

$ m lt.eq f(x) lt.eq f(x_1) lt m + epsilon space (x in (a, x_1)) $

A $delta := x_1 - a gt 0$ választással tehát azt mutattuk meg, hogy

$ forall epsilon gt 0"-hoz" exists delta gt 0, forall x in (alpha,beta), a lt x lt a + delta : 0 lt.eq f(x) - m lt epsilon eq f(x) in K_epsilon (m) $

Ez pedig azt jelenti, hogy f-nek a-ban van jobb oldali határértéke, és az m-mel egyenlő, azaz

$ lim_(a+0) f eq m eq inf{f(x) | x in (alpha,beta), x gt a}. $

A tétel többi állítása hasonlóan bizonyítható.
#pagebreak()

== Az összetett függvény folytonossága
\
Tegyük fel, hogy $f,g in RR arrow.long RR, g in C{a} "és " f in C{g(a)}.$ Ekkor $f space circle.small space g in C{a}$, azaz az összetett föggvény örökli a belső- és a külső függvény folytonosságát.

=== Bizonyítás
\
A feltételek szerint $g(a) in D_f$, ezért $g(a) in R_g sect D_f$, azaz $R_g sect D_f != emptyset$. Így valóban beszélgetünk az $f circle.small space g$ összetett függvényről, és $a in D_(f circle.small g)$ is igaz.
\

Legyen $(x_n) : NN arrow D_(f circle.small g) subset D_g$ egy olyan sorozat, amelyre $lim(x_n) eq a$. Mivel\ $g in C{a}$, így a folytonosságra vonatkozó átviteli elv szerint $lim(g(x_n)) eq g(a)$. Jelölje

$ b := g(a) "és " y_n := g(x_n) space (n in NN) $

Ekkor $(y_n) : NN arrow D_f$ és $lim(y_n) eq b$. Mivel $f in C{b}$, így a folytonosságra vonatkozó átviteli elv szerint $lim(f(y_n)) eq f(b)$. Ugyanakkor

$ f(b) eq f(g(a)) eq (f circle.small g)(a) "és " f(y_n) eq f(g(x_n)) eq (f circle.small g)(x_n) space (n in NN) $

Azt igazoltuk tehát, hogy $forall (x_n) : NN arrow D_(f circle.small g), lim(x_n) eq a$ sorozat esetén igaz, hogy

$ lim_(n arrow +infinity) (f circle.small g)(x_n) eq lim_(x arrow +infinity) (f(y_n)) eq f(b) eq (f circle.small g)(a) $

Ezért a folytonosságra vonatkozó átviteli elv szerint $f circle.small g in C{a}$

#pagebreak()

#show heading.where(level: 2): it => it.body
#show heading.where(level: 2): it => block(
  fill: colorQ,
  inset: 10pt,
  radius: 4pt,
)[#it]

== Korlátos és zárt intervallumon értelmezett folytonos függvény korlátossága.
Ha $f in C[a,b]$, akkor $f$ korlátos az $[a,b]$ intervallumon

=== Bizonyítás
Az $f$ függvény korlátos $[a,b]$-n, ha

$ exists K gt 0, forall x in [a,b] : abs(f(x)) lt.eq K $

Az állítást indirekt módon bizonyítjuk: tegyük fel, hogy $f$ nem korlátos $[a,b]$-n, azaz

$ forall K gt 0"-hoz" exists x in [a,b]:abs(f(x)) gt K $

Ekkor a $K eq n in NN$ választással azt kapjuk, hogy

$ (\*) space forall n in NN"-hez" exists x_n in [a,b]:abs(f(x_n)) gt n $

Az $(f(x_n))$ sorozat tehát nem korlátos

Mivel $x_n in [a,b]$ korlátos sorozat, ezért a Bolzano-Weierstrass kiválasztási tétel szerint létezik ennek egy $(x_n_k)$ konvergens részsorozata. Legyen $alpha eq lim(x_n_k)$. Ekkor $alpha in [a,b]$. Ugyanakkor $f in C{a}$. Így a folytonosságra vonatkozó átviteli elv szerint létezik a

$ lim(f(x_n_k)) eq f(alpha) $

véges határérték. Ebből következik az, hogy az $(f(x_n_k))$ sorozat korlátos, ami ellentmond (\*)-nak. Ezzel a tétel állítását bebizonyítottuk.
#pagebreak()
== Weierstrass tétele.
Egy korlátos és zárt intervallumon értelmezett folytonos függvénynek mindig van abszolút maximum- és abszolút minimumhelye, azaz
$ f in C[a,b] arrow.long.double exists alpha,beta in [a,b], forall x in [a,b] : f(beta) lt.eq f(x) lt.eq f(alpha) $

=== Bizonyítás
Már igazoltuk, hogy ha $f$ folytonos $[a,b]$-n, akkor $f$ korlátos $[a,b]$-n. Ezért

$ m eq inf{f(x) | x in [a,b]} in RR space "és " space M eq sup{f(x) | x in [a,b]} in RR $

Igazoljuk, hogy az $f$ függvénynek van abszolút maximumhelye, azaz \ $exists alpha in [a,b]:f(alpha) eq M$ A szuprémum definíciójából következik, hogy

$ forall n in NN^+"-hez" exists y_n in R_f : M - 1/n lt y_n lt.eq M $

Viszont:

$ y_n in R_f (n in NN^+)  arrow.long.double forall n in NN^+"-hez" exists x_n in [a,b]:f(x_n) eq y_n $

Az így értelmezett $(x_n):NN^+ arrow [a,b]$ sorozat korlátos, ezért a Bolzano-Weierstrass-féle kiválasztási tétel miatt a sorozatnak van $(x_n_k)$ konvergens részsorozata. Jelölje $alpha eq lim(x_n_k)$. Ekkor $alpha in [a,b]$. Ugyanakkor $f in C{alpha}$. Így a folytonosságra vonatkozó átviteli elv szerint

$ lim_(k arrow +infinity) f(x_n_k) eq f(alpha) $

Mivel minden $n_k$-ra

$ M - 1/n_k lt f(x_n_k) eq y_n_k lt.eq M $
teljesül, ezért $limits(lim)_(k arrow + infinity) y_n_k eq M$, így $f(alpha) eq M$. Megmutattuk tehát azt, hogy $alpha$ az $f$ függvénynek egy maximumhelye. Hasonlóan bizonyítható az abszolút minimum létezése.
#pagebreak()
== A Bolzano-tétel
Ha egy korlátos és zárt intervallumon értelmezett folytonos
függvény az intervallum két végpontjában különböző előjelű, akkor a függvénynek legalább
egy zérushelye van, azaz

$ f in C[a,b] "és " f(a) dot.op f(b) < 0 arrow.long.double exists xi in (a,b) : f(xi) eq 0 $

=== Bizonyítás
Az állítás bizonyításának az alapja az ún. _#strong("Bolzano-féle felezési eljárás.")_\
Tegyük fel, hogy

$ f(a) lt 0 lt f(b) $
#grid(
  columns: (auto,auto),
  gutter: 5pt,
  align: horizon,
  
  box()[
  Legyen

  $ [x_0,y_0] eq [a,b] $

  Az intervallumot megfelezzük. Legyen $z_0 eq (x_0 + y_0)/2$

  Három eset lehetséges:
  1. $f(z_0) eq 0$, ekkor $xi eq z_0$ zérushelye $f$-nek
  2. $f(z_0) gt 0$ esetén legyen $[x_1,y_1] eq [x_0,z_0]$
  3. $f(z_0) lt 0$ esetén legyen $[x_1,y_1] eq [z_0, y_0]$

  ],
  image("bolzano.png")
)

Ha $f(z_0) eq.not 0$, akkor olyan $[x_1,y_1]$ intervallumot sikerült megadni, amire

$ f(x_1) lt 0 lt f(y_1) $

teljesül, ezért átveheti az $[x_0,y_0]$ intervallum szerepét, de a hossza ennek fele, azaz $(b-a)/2$

Az $[x_1,y_1]$ intervallumot megfelezve is ugyanaz a három eset lehetséges. Ha a $z_1$ felezőpontban $f(z_1) eq.not 0$ akkor az intervallumból azt a felét tartjuk meg, amelynek két végpontjában $f$ különböző előjelű. Ez lesz az $[x_2,y_2]$ intervallum, amivel az eljárás megismételhető.

Folytassuk az eljárást! Ekkor vagy véges sok lépésben találunk olyan $xi$-t amelyre $f(xi) eq 0$, vagy nem. Az utóbbi esetben olyan $[x_n, y_n]$ intervallumsorozatot kapunk, amire minden $n in NN$ esetén

1. $[x_(n+1), y_(n+1)] subset [x_n,y_n]$,
2. $f(x_n) lt 0 "és " f(y_n) gt 0$,
3. $y_n - x_n eq (b-a)/2^n arrow.long_(n arrow +infinity) 0$

A valós számok Cantor-tulajdonsága szerint az 1) tulajdonságból következik, hogy a fenti
egymásba skatulyázott intervallumsorozat metszete nem üres. A 3) tulajdonságból következik, hogy ez a metszet egyelemű halmaz, hiszen minden eleme $x_n$ és $y_n$ között található.

Jelölje $xi$ a metszet egyedüli elemét, azaz

$ sect.big_(n in NN) [x_n,y_n] eq {xi} $

A konstrukcióból következik, hogy

$ lim_(n arrow +infinity) f(x_n) eq xi eq lim_(n arrow +infinity) y_n $

Mivel $f$ folytonos $xi$-ben, ezért az átvételi elv szerint

$ lim_(n arrow +infinity) f(x_n) eq f(xi) eq lim_(n arrow +infinity) f(y_n) $

De a 2) tulajdonságból következik, hogy

$ lim_(n arrow +infinity) f(x_n) lt.eq 0 lt.eq lim_(n arrow +infinity) f(y_n) $

azaz $f(xi) lt.eq 0$ és $f(xi) gt.eq 0$, ami csak úgy teljesülhet, ha $f(xi) eq 0$.
A bizonyítás hasonló, ha $f(a) gt 0$ és $f(b) lt 0$.
#pagebreak()
== Az $e$ szám irracionalitása.

Az $e$ szám irracionális.

=== Bizonyítás
Azt már tudjuk, hogy

$ e eq sum_(n eq 0)^(+infinity) 1/n! eq 1+1/1!+1/2!+1/3!+... $

Az állítással ellentétben tegyük fel, hogy $e$ racionális, azaz
$ e eq p/q, "  ahol " p,q in NN^+ " és " q gt.eq 2 $

(a $q gt.eq 2$ feltehető, egyébként bővítjük a törtet). Az

$ s_n := 1 + 1/1! + 1/2! + 1/3! + ... + 1/n! space (n in NN^+) $

sorozat szigorúan monoton növekvő módon tart $e$-hez, ha $n arrow.long +infinity$. Legyen $n gt q$ tetszőleges egész. Ekkor

$ 0 gt q! dot.op (s_n - s_q) eq q! dot.op (1/(q+1)! + 1/(q+2)! + ... + 1/n!) eq $
$ eq 1/(q+1) + 1/((q+1)(q+2)) + ... + 1/((q+1)dot.op ... dot.op n) lt.eq $
$ lt.eq 1/(q+1) dot.op (1 + 1/(q+1) + 1/(q+1)^2 + ... + 1/(q+1)^(n-q-1)) lt.eq $
$ lt.eq 1/(q+1) dot.op 1/(1- 1/(q+1)) eq 1/q lt.eq 1/2 $

Ebből az $n arrow.long +infinity$ határátmenetet véve azt kapjuk, hogy
$ (\#) space space 0 lt q! dot.op (e - s_q) lt.eq 1/2 $

hiszen $q! dot.op (e - s_q) eq.not 0$, mert $s_q lt e$

Az indirekt feltételből az következik, hogy
$ q! dot.op (e -s_q) eq q! dot.op (p/q - s_q) eq q! dot.op (p/q -1 -1/1! -1/2! - ... - 1/q!) $
egész szám. Ez viszont (\#) alapján nem lehetséges.
#pagebreak()
== A $pi$ szám értelmezésére vonatkozó tétel

A $cos$ függvénynek a $[0,2]$ intervallumban pontosan egy zérushelye van, azaz $[0,2]$-nek pontosan egy $xi$ pontjában áll fenn a $cos xi eq 0$ egyenlőség. Ennek a $xi$ számnak a kétszereseként *értelmezzük a $pi$ számot:*

$ pi := 2 xi $

=== Bizonyítás

A Bolzano-tételt alkamazzuk. Világos, hogy $cos in C[0,2]$ és $cos 0 eq 1$. Másrészt

$ cos 2 eq 1 - 2^2/2! + 2^4/4! - 2^6/6! + 2^8/8! - 2^10/10! + 2^12/12! - ... eq $
$ eq underbrace(1- 2 + 2/3, eq "-1/3") - 2^6/6! dot.op underbrace((1 - 2^2/(7 dot.op 8)), gt 0) - 2^10/10! dot.op underbrace((1-2^2/(11 dot.op 12)), gt 0) - ... lt -1/3 lt 0 $

A Bolzano-tétel feltételei tehát teljesülnek, ezért $exists xi in (0,2): cos xi eq 0$.

A $xi$ pont egyértelműsége következik abból, hogy a $cos arrow.b$ a $[0,2]$ intervallumban, azaz

$ (\*) "ha " 0 lt.eq x lt y lt.eq 2 ", akkor " cos x gt cos y $

Ezt fogjuk most igazolni. Az eddigiekből következik, hogy

$ cos x gt cos y arrow.long.l.r.double cos x - cos y eq -2 dot.op sin (x+y)/2 dot.op sin (x-y)/2 eq $
$ eq 2 dot.op sin (x+y)/2 dot.op sin (y-x)/2 gt 0 $

Mivel

$ 0 lt.eq x lt y lt.eq 2 arrow.long.double 0 lt (x+y)/2 lt 2 "és " 0 lt (y-x)/2 lt 2, $

ezért a (\*) állítás a 

$ sin z eq z - z^3/3! + z^5/5! - z^7/7! + ... eq z dot.op underbrace((1- z^2/(2 dot.op 3)), gt 0) + z^5/5! dot.op underbrace((1 - z^2/(6 dot.op 7)), gt 0) + ... gt 0 (z in (0,2)) $

egyenlőtlenség következménye.