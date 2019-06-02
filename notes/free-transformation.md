---
title: |
  Übersetzung von Haskell nach Coq \protect\
  Verwendung der Free Monade
author: Justin Andresen
lang: de-DE
pandoc-minted:
  default-attributes:
    escapeinside: "\\\\[\\\\]"
    mathescape: "true"
    tabsize: "2"
    breaklines: "true"
  default-block-attributes:
    numbersep: "5pt"
    frame: "lines"
    framesep: "2mm"
---

\newcommand{\lift}[1]{{#1}^{\dagger}}
\newcommand{\liftT}[1]{{#1}^{ * }}
\newcommand{\free}[1]{\texttt{Free}\;C_F\;{#1}}
\newcommand{\pure}[1]{\texttt{pure}\;{#1}}

\newcommand{\type}{ * }
\newcommand{\Int}{\texttt{Int}}
\newcommand{\Bool}{\texttt{Bool}}
\newcommand{\bool}{\texttt{bool}}
\newcommand{\True}{\texttt{True}}
\newcommand{\true}{\texttt{true}}
\newcommand{\False}{\texttt{False}}
\newcommand{\false}{\texttt{false}}
\newcommand{\List}{\texttt{List}}
\newcommand{\Pair}{\texttt{Pair}}
\newcommand{\undefined}{\texttt{undefined}}
\newcommand{\error}[1]{\texttt{error #1}}

\newpage
# Eineitung

In diesem Dokument wird beschrieben, wie die Haskellmodule, -ausdrücke und
-typen nach Coq übersetzt werden können und wie dabei die Free Monade
eingesetzt werden kann, sodass die Semantik des Haskellprogramms (insbesondere
in Bezug auf partielle Funktionen und Lazy Auswertung) beibehalten wird. Dabei
wird davon ausgegangen, dass der Haskellcode wie in `notes/input-format.md`
beschrieben aufgebaut ist.

Dieses Dokument basiert auf der monadischen Transformation, wie sie in
`notes/monadic-transformation.md` beschrieben worden ist. In diesem Dokument
wird nun jedoch konkret auf die Verwendung der *Free* Monade eingegangen.
Wir gehen hier davon aus, dass Datentypen und Operationen, wie sie in
[One Monad to Prove Them All][Dylus2019] vorgestellt worden sind, bereits
vordefiniert sind. Insbesondere werden die `Free`{.coq} Monade, die
`Container`{.coq} Typklasse, die Funktoren `Zero` und `One` sowie deren
`Container` Instanzen `C__Zero` bzw. `C__One` benötigt. Auf der *Free* Monade
seien die Operationen `>>=`{.coq} und `pure`{.coq} (statt `m_return`{.coq})
vordefiniert.

Die hier skizzierten Übersetzungsregeln sowie die dabei verwendete Notation
orientiert sich an der von [Abel et al.][Abel2005] vorgestellten Übersetzung
von Haskell zu Agda. Dabei bedeutet $\lift{H} = G$, dass das
Sprachkonstrukt $H$ aus Haskell mit $G$ in Coq übersetzt werden kann.
Zugunsten der Verwendung von Syntaxhighlighting wird hier in der Regel darauf
verzichtet diese Gleichungen explizit zu notieren.
Eine solche Gleichung wird in diesem Dokument stattdessen häufig durch zwei
aufeinander folgende Code Blöcke dargestellt:

```haskell
[$H$]
```

```coq
[$G$]
```

Ziel dieses Dokuments ist es nicht eine vollständig formale Beschreibung der
Übersetzung anzugeben, sondern zu skizzieren, wie sich die spätere
Implementierung verhalten sollte. Anhand der hier beschriebenen Regeln sollte
es aber dennoch möglich sein einfache Haskellfunktionen per Hand zu
konvertieren (z.B. um weitere Fehler in der
[bestehenden Implementierung][Jessen2019] zu finden oder Probleme bei der
Übersetzung zu identifizieren).

\newpage
# Übersetzung von Typausdrücken

Ein Typ $\tau :: \type$ wird übersetzt, indem er in den monadischen Kontext
gehoben wird.

$$
  \lift{\tau} = \free{\liftT{\tau}}
$$

wobei $C_F$ die `Container`{.coq} Instanz des im jeweiligen Kontext[^context]
betrachteten Funktors $F$ bezeichne.

[^context]: $C_F$ und $F$ werden als Argumente an Funktions-, Typsynonym- und
            Datentypdeklarationen übergeben.

Darüber hinaus muss rekursiv (mithilfe von $\liftT{\tau}$) der Argument- und
Rückgabetyp von jedem in $\tau$ enthaltenen Funtionstypen übersetzt werden
sowie die `Container`{.coq} Instanz $C_F$ an genutzte Datentypen weitergereicht
werden.

- Für alle Typen $\tau_1, \tau_2 :: \type$:

    $$
      \liftT{(\tau_1 \to \tau_2)} = \lift{\tau_1} \to \lift{\tau_2}
    $$

- Für alle Datentypen $D$ und Typsynonymen $S$:

    $$
      \begin{aligned}
        \liftT{D}    &= D\;C_F      \\
        \liftT{S}    &= S\;C_F      \\
      \end{aligned}
    $$

Ansonsten bleibt der Typausdruck unverändert:

- Für alle Typvariablen $\alpha$:

    $$
      \liftT{\alpha} = \alpha
    $$

- Für alle Typkonstruktoren $\tau_1 :: \type \to \kappa$ und Typen
  $\tau_2 :: \type$:

    $$
      \liftT{(\tau_1\;\tau_2)} = \liftT{\tau_1} \; \liftT{\tau_2}
    $$

## Vordefinierte Datentypen

Alle vordefinierten Datentypen werden auf Typen abgebildet, die in einem
standardmäßig importierten Modul geeignet vordefiniert werden müssen.

- $\liftT{\Int} = \Int$

    In Coq wird in der Regel `nat`{.coq} zur Darstellung von Zahlen verwendet,
    jedoch können mit `nat`{.coq} im Gegensatz zu `Int`{.haskell} aus Haskell
    keine negativen Zahlen repräsentiert werden. Daher ist `nat`{.coq} für
    die Übersetzung nicht geeignet. In [hs-to-coq][hs-to-coq-int] wird
    `Int`{.coq} in Coq wie folgt definiert:

    ```Coq
    Require Export ZArith.
    Definition Int := Z.
    ```

    Mit dieser Definition kann man positive und negative Zahlen unterscheiden,
    aber das Verhalten von Haskell wird nach wie vor nicht korrekt abgebildet,
    da `Z`{.coq} beliebig große Zahlen darstellen kann während `Int`{.haskell}
    in Haskell aber auf 32 bzw. 64 Bit beschränkt ist. `Z`{.coq} entspricht
    also eher `Integer`{.haskell}. Wir übernehmen dennoch vorerst diese
    Definition.

    [hs-to-coq-int]: https://github.com/antalsz/hs-to-coq/blob/master/examples/base-src/manual/GHC/Num.v#L6

- $\liftT{\Bool} = \bool$

    Der Typ `bool`{.coq} ist in Coq vordefiniert und hat die Konstruktoren
    `true`{.coq} und `false`{.coq}. Um die auf `bool`{.coq} definierten
    Funktionen und bereits existierenden Beweise beizubehalten, verwenden
    wir diesen Datentyp bei der Übersetzung.

### Listen

$$
  \liftT{[\tau]} = \List\;C_F\;\liftT{\tau}
$$

wobei $\tau :: \type$

Dabei sollte der Typ `List`{.coq} genau so definiert werden, wie der
Compiler die folgende Datentypdeklaration übersetzen würde:

```haskell
data List a = Nil | Cons a (List a)
```

Hier gehen wir von folgender Übersetzung aus:

```coq
Inductive List {[$F$] : Type-> Type} ([$C_F$] : Container [$F$])
  (a : Type) :=
  | Nil  : List [$C_F$] a
  | Cons : Free [$C_F$] a -> Free [$C_F$] (List [$C_F$] a) -> List [$C_F$] a.

Arguments Nil  {[$F$]} {[$C_F$]} {a}.
Arguments Cons {[$F$]} {[$C_F$]} {a}.
```

### Tupel

- $\liftT{()} = unit$

    Der Typ `unit`{.coq} ist in Coq vordefiniert und hat nur den Konstruktor
    `tt`{.coq}.

- $\liftT{(\tau_1, \tau_2)} = \Pair\;C_F\;\liftT{\tau_1}\;\liftT{\tau_2}$,
  wobei $\tau_1, \tau_2 :: \type$ Typen sind.

    Dabei sollte der Typ `Pair`{.coq} genau so definiert werden, wie der
    Compiler die folgende Datentypdeklaration übersetzen würde:

    ```haskell
    data Pair a b = Pair a b
    ```

    Hier gehen wir von folgender Übersetzung aus:

    ```coq
    Inductive Pair {[$F$] : Type -> Type} ([$C_F$] : Container [$F$])
      (a b : Type) :=
      | Pair_ : Free [$C_F$] a -> Free [$C_F$] b -> Pair [$C_F$] a b.
    Arguments Pair_ {[$F$]} {[$C_F$]} {a} {b}.
    ```

\newpage
# Übersetzung von Modulen
## Übersetzung von Datentypdeklarationen

```haskell
data [$D$] [$\alpha_1$] [$\ldots$] [$\alpha_m$] =
    [$C_1$] [$\tau_{1,1}$] [$\ldots$]  [$\tau_{1,p_1}$]
  | [$C_2$] [$\tau_{2,1}$] [$\ldots$]  [$\tau_{2,p_2}$]
  | [$\ldots$]
  | [$C_n$] [$\tau_{n,1}$] [$\ldots$]  [$\tau_{n,p_n}$]
```

```coq
Inductive [$D$] {[$F$] : Type -> Type} ([$C_F$] : Container [$F$])
  ([$\alpha_1$] [$\ldots$] [$\alpha_m$] : Type) : Type :=
  | [$C_1$] : [$\lift{\tau_{1,1}}$] -> [$\ldots$] -> [$\lift{\tau_{1,p_1}}$] -> [$D$] [$C_F$] [$\alpha_1$] [$\ldots$] [$\alpha_m$]
  | [$C_2$] : [$\lift{\tau_{2,1}}$] -> [$\ldots$] -> [$\lift{\tau_{2,p_2}}$] -> [$D$] [$C_F$] [$\alpha_1$] [$\ldots$] [$\alpha_m$]
  | [$\ldots$]
  | [$C_n$] : [$\lift{\tau_{n,1}}$] -> [$\ldots$] -> [$\lift{\tau_{n,p_n}}$] -> [$D$] [$C_F$] [$\alpha_1$] [$\ldots$] [$\alpha_m$].
```

wobei $\alpha_1, \ldots, \alpha_n$ Typvariablen, $C_1, \ldots, C_m$
die Konstruktoren von $D$, und $\tau_{i,1}, \ldots \tau_{i,p_i}$ für alle
$i \in \{\, 1, \ldots, m \,\}$ Typen sind.

Zusätzlich wird für jeden Konstruktor spezifiziert, dass die Typparameter
optional sind. Die `Container`{.coq} Instanz übergeben wir jedoch immer
explizit.

```coq
Arguments [$C_1$] {[$F$]} {[$C_F$]} {[$\alpha_1$]} [$\ldots$] {[$\alpha_m$]}.
[$\vdots$]
Arguments [$C_n$] {[$F$]} {[$C_F$]} {[$\alpha_1$]} [$\ldots$] {[$\alpha_m$]}.
```

\newpage
## Übersetzung von Typsynoymdeklarationen

```haskell
type [$S$] [$\alpha_1$] [$\ldots$] [$\alpha_m$] = [$\tau$]
```

```coq
Definition [$S$]
  {[$F$] : Type -> Type} ([$C_F$] : Container [$F$])
  ([$\alpha_1$] [$\ldots$] [$\alpha_m$] : Type) := [$\liftT{\tau}$].
```

wobei $\alpha_1, \ldots, \alpha_n$ Typvariablen sind und $\tau$ ein Typ oder
Typkonstruktor ist.

Wir übersetzen hier $\tau$ als $\liftT{\tau}$ und nicht als
$\lift{\tau}$, da es egal sein soll, ob zuerst übersetzt und dann das Typsynonym
expandiert wird oder an­ders­he­r­um.
Übersetzt man zunächst $S$ zu $\lift{S} = \free{\liftT{S}} = \free{S}$ und expandiert
dann $S$ zu $\liftT{\tau}$, erhält man $\free{\liftT{\tau}}$. Andersherum würde
man zunächst $S$ zu $\tau$ expandieren und dann zu
$\lift{\tau} = \free{\liftT{\tau}}$ übersetzten. Würde man in der
Tysynonymdeklaration hingegen $\tau$ zu $\lift{\tau} = \free{\liftT{\tau}}$
übersetzen, so erhilte man beim Expandieren von $S$ im Coq Code
$\free{(\free{\liftT{\tau}})}$.

\newpage
## Übersetzung von Funktionsdeklaration

Wir müssen Funktionen die total und partiell definiert sind separat betrachten,
da totale Funktionen mit beliebigen Monaden instanziert werden können, aber
partielle Funktionen nicht mit der `Identity`{.coq} Monade. Insbesondere
benötigen partielle Funktionen weitere Informationen darüber, wie mit
Fehlertermen (`undefined`{.haskell} und `error "..."`{.haskell}) umgegangen
werden soll.

Wir betrachten zunächst totale Funktionsdeklarationen und unterscheiden
weiter, ob die Funktion rekursiv definiert ist oder nicht.

### Nicht-rekursive Funktionen

```haskell
[$f$] :: [$\tau_1$] -> [$\ldots$] -> [$\tau_n$] -> [$\tau$]
[$f$] [$x_1$] [$\ldots$] [$x_n$] = [$e$]
```

```coq
Definition [$f$]
  {[$F$] : Type -> Type} ([$C_F$] : Container [$F$])
  {[$\alpha_1$] [$\ldots$] [$\alpha_m$] : Type} ([$x_1$] : [$\lift{\tau_1}$]) [$\ldots$] ([$x_n$] : [$\lift{\tau_n}$]) : [$\lift{\tau}$]
  := [$\lift{e}$].
```

wobei $\tau_1, \ldots, \tau_n$ sowie $\tau$ Typen und $x_1, \ldots, x_n$
Variablenpattern sind, $e$ ein Ausdruck ist und $\alpha_1, \ldots, \alpha_m$
die Typvariablen in der Typsignatur von $f$ sind.

Diese Übersetzung entspricht der von [Abel et al.][Abel2005] beschriebenen
Optimierung. Ohne die Optimierung wäre der Typ von $f$ nach der Übersetzung:

$$
  \lift{(\tau_1 \to \ldots \to \tau_n \to \tau)}
  = \free{(\lift{\tau_1} \to \free{(\ldots \to \free{(\lift{\tau_n} \to \tau)})} \ldots)}
$$

mit der Optimierung entfallen die monadischen Zwischenergebnisse:

$$
  \lift{\tau_1} \to \ldots \to \lift{\tau_n} \to \lift{\tau}
$$

Dadurch lässt sich die Funktion in der Praxis einfacher aufrufen, aber
es müssen bei der Übersetzung partielle Applikationen separat betrachtet
werden.

### Rekursive Funktionen

Die Definition einer rekursiven Funktion wird mithilfe von Hilfsfunktionen
übersetzt, in denen sich das Argument, welches strukturell abgebaut wird nicht
in einem monadischem Kontext befindet.

Betrachte eine $n$-stellige Funktion $f$, die auf ihrem $i$-tem Argument
rekursiv definiert ist:

```haskell
[$f$] :: [$\tau_1$] -> [$\ldots$] -> [$\tau_n$] -> [$\tau$]
[$f$] [$x_1$] [$\ldots$] [$x_n$] = [$e$]
```

Für den $j$-ten `case`{.haskell}-Ausdruck in $e$ der Form

```haskell
case [$x_i$] of
  [$\vdots$]
```

erzeugen wir eine Hilfsfunktion der Form

```coq
Fixpoint [$f^{(j)}$]
  {[$F$] : Type -> Type} ([$C_F$] : Container [$F$])
  {[$\alpha_1$] [$\ldots$] [$\alpha_m$] : Type} ([$x_1$] : [$\lift{\tau_1}$]) [$\ldots$] ([$x_{i-1}$] : [$\lift{\tau_{i-1}}$])
  ([$x_i$] : [$\liftT{\tau_i}$]) ([$x_{i+1}$] : [$\lift{\tau_{i+1}}$]) [$\ldots$] ([$x_n$] : [$\lift{\tau_n}$]) : [$\lift{\tau}$] :=
  match [$x_i$] with
  | [$\vdots$]
  end.
```

wobei $\alpha_1, \ldots, \alpha_m$ die in der Funktionssignatur von $f$
enthaltenden Typvariablen sind.

Innerhalb der Hilfsfunktion wird eine modifizierte Übersetzung durchgeführt:

- Es ist zu beachten, dass $x_i$ innerhalb der Hilfsfunktion sich nicht in der
  Monade befindet:

  $$
    \lift{x_i} = \pure{x_i}
  $$

- Alle rekursiven Aufrufe innerhalb der Hilfsfunktionen werden ersetzt, indem
  die Definition der Hauptfunktion (siehe unten) eingesetzt wird (*inlining*).
  Daher sind alle Hilfsfunktionen gegenseitig rekursiv und müssen in einem
  einzigen `Fixpoint [$\ldots$] with [$\ldots$]` Sentence zusammengefasst
  werden.

Bei der Übersetzung der Hauptfunktion

```coq
Definition [$f$]
  {[$F$] : Type -> Type} ([$C_F$] : Container [$F$])
  {[$\alpha_1$] [$\ldots$] [$\alpha_m$] : Type} ([$x_1$] : [$\lift{\tau_1}$]) [$\ldots$] ([$x_n$] : [$\lift{\tau_n}$]) : [$\lift{\tau}$] := [$\lift{e}$]
```

wird der $j$-te `case`{.haskell}-Ausdruck der Form

```haskell
case [$x_i$] of
  [$\vdots$]
```

durch einen Aufruf der entsprechenden Hilfsfunktion ersetzt:

```coq
[$x_i$] >>= fun([$x_i'$] : [$\liftT{\tau_i}$]) =>
  [$f^{(j)}$] [$C_F$] [$x_1$] [$\ldots$] [$x_{i-1}$] [$x_i'$] [$x_{i+1}$] [$\ldots$] [$x_n$]
```

## Übersetzung von partiellen Funktionen

Wir bezeichnen die Definition einer Funktion $f$ als partiell, wenn in $e$
ein Fehlerterm vorkommt oder eine partielle Funktion verwendet wird. Beide
der folgenden Funktionen sind also partiell definiert:

```haskell
-- Contains an error term.
head :: [a] -> a
head xs = case xs of
  []      -> undefined
  x : xs' -> x

-- Uses a partial function.
last :: [a] -> a
last xs = head (reverse xs)
```

Es ist hingegen unproblematisch, wenn eine als Argument übergebene Funktion
aufgerufen wird, obwohl diese auch partiell definiert sein könnte.
Folgende Funktion ist also nicht partiell sondern total definiert:

```haskell
map :: (a -> b) -> [a] -> [b]
map f xs = case xs of
  []    -> []
  x:xs' -> f x : map f xs'
  --       ^ Allowed even though `f` might be defined partially.
```

Bei der Übersetzung von partiellen Funktionen weitere Informationen darüber,
wie mit den Fehlertermen `undefined`{.haskell} und `error "..."`{.haskell}
umgegangen werden soll. Dazu definieren wir in Coq eine Typklasse die für einen
Funktor $F$ neben der `Container`{.coq} Instanz $C_F$ auch Operationen
bereitstellt, mit denen die Fehlerterme übersetzt werden können.

```coq
Require Import Coq.Strings.String.

Class Partial ([$F$] : Type -> Type) :=
  {
    [$C_F$] : Container [$F$];
    undefined : forall {A : Type}, Free [$C_F$] A;
    error : forall {A : Type}, string -> Free [$C_F$] A
  }.
```

Instanzen dieser Typklasse bezeichnen wir im folgenden mit $P_F$.
Für den Funktor `One`{.coq} sähe eine mögliche Instanz wie folgt aus:

```coq
Instance [$P_{One}$] : Partial One :=
  {
    [$C_F$] := [$C_{One}$];
    undefined := fun {A : Type} => Nothing;
    error     := fun {A : Type} (msg : string) => Nothing
  }.
```

Nun muss in der Übersetzung von $f$ nur die Typklasse ausgewechselt werden.
Die Vorkommen von $C_F$ werden von Coq automatisch inferiert.

```coq
Definition [$f$]
  {[$F$] : Type -> Type} ([$P_F$] : Partial [$F$])
  {[$\alpha_1$] [$\ldots$] [$\alpha_m$] : Type} ([$x_1$] : [$\lift{\tau_1}$]) [$\ldots$] ([$x_n$] : [$\lift{\tau_n}$]) : [$\lift{\tau}$]
  := [$\lift{e}$].
```

Analog ist bei der Übersetzung von rekursiv definierten Funktionen und deren
Hilfsfunktionen vorzugehen.

Beim Aufruf partieller Funktionen innerhalb von $f$ muss darauf geachtet werden,
dass $P_F$ statt $C_F$ übergeben wird (siehe dazu den Abschnitt über
Funktionsanwendungen). Betrachte beispielsweise den Aufruf:

```haskell
map head xss
```

Dieser wird zunächst per $\eta$-Konversion wie folgt umgewandelt:

```haskell
map (\xs -> head xs) xss
```

Da `head`{.haskell} partiell definiert ist, muss nach der Übersetzung $P_F$
übergeben werden, aber `map`{.haskell} nur $C_F$, da es sich um eine total
definierte Funktion handelt.

```coq
map [$C_F$] (pure (fun(xs) => head [$P_F$] xs)) xss
```

Dieses Beispiel verdeutlicht auch, warum `map`{.haskell} tatsächlich als total
behandelt werden darf: alle Zusatzinformationen, die `head`{.coq} benötigt
wurden bereits vor dem Aufruf von `map`{.coq} übergeben. Also muss `map`{.coq}
selber nicht über diese Informationen Verfügen, um die Funktion aufrufen zu
können.

## Übersetzung von gegenseitig rekursiven Deklarationen

Wenn mehrere Datentyp- oder Funktionsdeklarationen gegenseitig
voneinander abhängen, dann müssen sie in einen gemeinsamen `Inductive`{.coq}
bzw. `Fixpoint`{.coq} Sentence definiert werden. Z.B.:

```coq
Fixpoint f (* ... *) := (* ... *)
with     g (* ... *) := (* ... *)
with     h (* ... *) := (* ... *).
```

Bei Funktionsdeklarationen muss dabei beachtet werden, dass nun in den
Hilfsfunktionen auch die rekursiven Aufrufe der anderen Funktionen korrekt
auf die entsprechenden Hilfsfunktionen umgeleitet werden müssen.

Bei einer rekursiven Abhängigkeit zwischen Typsynonym- und
Datentypdeklarationen müssen die Typsynonyme zwangsläufig expandiert werden,
da ein `Inductive` und `Definition` Senetence nicht mit `with` gemischt werden
kann.

\newpage
# Übersetzung von Ausdrücken

## Funktions- und Konstruktoranwendungen

### Partielle Anwendung

Aufgrund der oben beschriebenen Optimierung für die Übersetzung von
Funktionsdeklarationen muss bei der Übersetzung von Funktionsanwendungen
unterschieden werden, ob es sich um eine partielle Anwendung handelt oder
alle erwarteten Argumente angegeben worden sind.

Wenn $f$ ein $n$-steliges Funktions- oder Konstruktorsymbol ist, welches auf
$i < n$ Ausdrücke $e_1, \ldots, e_i$ angewendet wird, muss eine $\eta$-
Transformation durchgeführt werden, d.h. die fehlenden Argumente werden
mithilfe einer Lambda-Abstraktion hinzugefügt.

```haskell
[$f$] [$e_1$] [$\ldots$] [$e_i$]
```

muss genau so übersetzt werden, wie

```haskell
\[$x_{i+1}$] [$\ldots$] [$x_n$] -> [$f$] [$e_1$] [$\ldots$] [$e_i$] [$x_{i+1}$] [$\ldots$] [$x_n$]
```

wobei $x_{i+1}, \ldots, x_n$ frische Variablen sind.

Im folgenden können wir also davon ausgehen, dass jede zu übersetzende
Funktionsanwendung vollständig ist.

### Anwendung definierter Funktionen

Bei einer vollständigen Anwendung einer definierten Funktion
`[$f$] :: [$\tau_1$] -> [$\ldots$] -> [$\tau_n$] -> [$\tau$]`{.haskell}
auf Ausdrücke $e_1 :: \tau_1$, $\ldots$, $e_n :: \tau_n$
müssen nur die Argumente rekursiv übersetzt werden und die `Container`{.coq}
Instanz propagiert werden.

Dazu unterscheiden wir, ob es sich um eine partiell oder total definierte
Funktion handelt. Totalen Funktionen wird nur die `Container`{.coq} Instanz
$C_F$ übergeben, wohingegen partielle Funktionen die Zusatzinformationen aus
der `Partial`{.coq} Instanz $P_F$ benötigen.

> Meine bisherigen Tests suggerieren, dass es auch möglich wäre in der
> Funktionsdeklaration $C_F$ bzw. $P_F$ als implizit zu kennzeichnen.
> Dann müsste man bei den Funktionsaufrufen keine solche Unterscheidung mehr
> machen und der generierte Code wäre lesbarer. Die Frage ist jedoch, ob Coq in
> jedem Fall in der Lage ist diese Parameter zu inferien. Coq ist
> beispielsweise nicht in der Lage $C_F$ in einem Typausdruck korrekt zu
> inferien, falls bereits eine `Container`{.coq} Instanz definiert wurde.
> Ein Vorteil des bisherigen Ansatzes ist, dass in indirekt partiell
> definierten sichtbar ist, aufgrund der VErwendung welcher Funktion sie nicht
> total ist.

#### Totale Funktionen

```haskell
[$f$] [$e_1$] [$\ldots$] [$e_n$]
```

```coq
[$f$] [$C_F$] [$\lift{e_1}$] [$\ldots$] [$\lift{e_n}$]
```

#### Partielle Funktionen

```haskell
[$f$] [$e_1$] [$\ldots$] [$e_n$]
```

```coq
[$f$] [$P_F$] [$\lift{e_1}$] [$\ldots$] [$\lift{e_n}$]
```

### Anwendung von Konstruktoren

Falls `[$C$] [$\tau_1$] [$\ldots$] [$\tau_n$]`{.haskell} ein Konstruktor des
Datentyps `[$D$] [$\tau_{\alpha_1}$] [$\ldots$] [$\tau_{\alpha_m}$]`{.haskell}
ist und $e_1 :: \tau_1$, $\ldots$, $e_n :: \tau_n$ Ausdrücke sind, dann hat $C$
in Coq den Typ `[$\lift{\tau_1}$] -> [$\ldots$] -> [$\lift{\tau_n}$] -> [$D$] [$\tau_{\alpha_1}$] [$\ldots$] [$\tau_{\alpha_m}$]`{.coq}.
Das Ergebnis der Konstruktoranwendung befindet sich also nicht in einem
monadischen Kontext. Daher kann die oben stehende Übersetzungsregel für
definierte Funktionen nicht verwendet werden, sondern es muss ein weiteres
`pure`{.coq} eingefügt werden.

```haskell
[$C$] [$e_1$] [$\ldots$] [$e_n$]
```

```coq
pure ([$C$] [$\lift{e_1}$] [$\ldots$] [$\lift{e_n}$])
```

Dies gilt auch bei nullstelligen Konstruktoren:

```coq
pure [$C$]
```

Da wir für jeden Konstruktor $C$ festgelegt haben, dass Typargumente sowie
der Funktor und die `Container`{.coq} Instanz implizit sind

```coq
Arguments [$C$] {[$F$]} {[$C_F$]} {[$\alpha_1$]} [$\ldots$] {[$\alpha_m$]}
```

muss oben in beiden Fällen [$C_F$] nicht übergeben werden.

> Auch hier stellt sich die Frage, ob Coq in jedem Fall in der Lage ist $C_F$
> zu inferien. Im Gegensatz zu Funktionsanwendungen wurde sich hier vorest
> dagegen entschieden $C_F$ explizit zu übergeben, da ansonsten im Pattern
> Matching dieses zusätzliche Argument behandelt werden müsste (mit einem
> zusätzlichen `_`{.coq} Pattern).

### Anwendung vordefinierter Funktionen

Zum derzeitigen Zeitpunkt existieren ausschließlich vordefinierte Funktionen
in Form von Präfix- und Infixoperationen wie z.B. `(+)`{.haskell}. Die
Gegenstücke dieser Operationen in Coq kann man nicht direkt auf die monadischen
Werte anwenden:

```coq
Fail Compute (pure 42) + (pure 1337).
(*
  ==> The command has indeed failed with message:
  The term "pure 42" has type "Free ?C__F nat"
  while it is expected to have type "nat".
*)
```

Die Argumente müssen also zuvor aus der Monade "herausgeholt" werden.

Die (vollständige) Anwendung einer in Haskell vordefinierte Funktion
$f :: \tau_1 \to \ldots \to \tau_n \to \tau$ auf die Ausdrücke
$e_1 :: \tau_1$, $\ldots$, $e_n :: \tau_n$ kann man wie folgt in eine
Anwendung auf das Coq Gegenstück
$\lift{f} :: \liftT{\tau_1} \to \ldots \to \liftT{\tau_n} \to \liftT{\tau}$
übersetzen:

```haskell
  [$f$] [$e_1$] [$\ldots$] [$e_n$]
```

```coq
[$\lift{e_1}$] >>= fun([$x_1$] : [$\liftT{\tau_1}$]) => ( [$\ldots$] (
  [$\lift{e_n}$] >>= fun([$x_n$] : [$\liftT{\tau_n}$]) =>
    pure ([$\lift{f}$] [$x_1$] [$\ldots$] [$x_n$])
) [$\ldots$] )
```

wobei $x_1, \ldots, x_n$ frische Variablen sind.

Dadurch wird der entstehende Code unleserlich. Im Fall von partiellen
Anwendungen wird der Effekt aufgrund der $\eta$-Transformationen noch
verstärkt. Das Problem lässt sich umgehen, indem in Coq nicht die eingebauten
Operationen verwendet werden, sondern eigene *wrapper* Funktionen vordefiniert
werden, deren Interface dem einer regulär übersetzten Funktion entspricht.
Für `(+)`{.haskell} könnte man in Coq beispielsweise folgende Funktion
in Coq auf `nat` definieren:

```coq
Definition plus
  {[$F$] : Type -> Type} ([$C_F$] : Container[$F$])
  (n1 : Free [$C_F$] nat) (n2 : Free [$C_F$] nat) : Free [$C_F$] nat :=
  n1 >>= fun(n1' : nat) =>
    n2 >>= fun(n2' : nat) =>
      pure (n1' + n2').
```

`plus`{.coq} kann genauso verwendet werden, wie jede in Haskell definierte
Funktion. Der Compiler muss also nicht mehr zwischen definierten und
vordefinierten Funktionen unterscheiden.

Dieser Ansatz erlaubt uns nun auch einfach die Basisdatentypen auszuwechseln.
Z.B. soll `Int`{.haskell} mit `Z`{.coq} und nicht mit `nat`{.coq} übersetzt
werden. Es muss dazu nicht die Übersetzung von Funktionsanwendungen angepasst
werden sondern lediglich die vordefinierte Funktion `plus`{.coq}:

```coq
Definition plus
  {[$F$] : Type -> Type} ([$C_F$] : Container[$F$])
  (z1 : Free [$C_F$] Z) (z2 : Free [$C_F$] Z) : Free [$C_F$] Z :=
  z1 >>= fun(z1' : Z) =>
    z2 >>= fun(z2' : Z) =>
      pure (Z.add z1' z2').
```

### Sonstige Funktionsanwendungen

Aufgrund der Unterstützung von Funktionen höherer Ordnung kann auf der linken
Seite einer Funktionsanwendung neben einem Funktions- oder
Konstruktorsymbol auch ein Ausdruck stehen.

$$
  \begin{aligned}
    e_1 &:: \tau \to \tau' \\
    e_2 &:: \tau
  \end{aligned}
$$

Durch die Übersetzung wird dieser in einen monadischen Kontext gehoben:

$$
  \begin{aligned}
    \lift{e_1} &:: \free{(\lift{\tau} \to \lift{\tau'})} \\
    \lift{e_2} &:: \lift{\tau}
  \end{aligned}
$$

D.h. die Funktion die angewendet werden soll muss zuvor aus der Monade
herausgeholt werden.

```haskell
[$e_1$] [$e_2$]
```

```coq
[$\lift{e_1}$] >>= fun([$f$] : [$\liftT{\tau}$] -> [$\lift{\tau'}$]) => [$f$] [$e_2$]
```

wobei $f$ eine frische Variable ist.

## Operatoren

### Infixoperatoren

Die Infixschreibweise wird als *syntaxktischer Zucker* behandelt und in die
Anwendung von Funktionen übersetzt.

Für definierte Funktionen $f :: \tau_1 \to \tau_2 \to \tau$  und
Ausrücke $e_1 :: \tau_1$ sowie $e_2 :: \tau_2$:

- ``[$e_1$] `[$f$]` [$e_2$]``{.haskell} wird genauso wie
  `[$f$] [${e_1}$] [$e_2$]`{.haskell} übersetzt
- ``([$e_1$] `[$f$]`)``{.haskell} wird genauso wie
  `[$f$] [${e_1}$]`{.haskell} übersetzt
- ``(`[$f$]` [$e_2$])``{.haskell} wird genauso wie
  `\[$x$] -> ([$f$]) [$x$] [$e_2$]`{.haskell} übersetzt wobei $x$ eine
  frische Variable ist.

Für vordefinierte Infixoperationen $(\circ) :: \tau_1 \to \tau_2 \to \tau$ und
Ausrücke $e_1 :: \tau_1$ sowie $e_2 :: \tau_2$:

- `[$e_1$] [$\circ$] [$e_2$]`{.haskell} wird genauso wie
  `([$\circ$]) [${e_1}$] [$e_2$]`{.haskell} übersetzt
- `([$e_1$] [$\circ$])`{.haskell} wird genauso wie
  `([$\circ$]) [${e_1}$]`{.haskell} übersetzt
- `([$\circ$] [$e_2$])`{.haskell} wird genauso wie
  `\[$x$] -> ([$\circ$]) [$x$] [$e_2$]`{.haskell} übersetzt wobei $x$ eine
  frische Variable ist

Desweiteren wird

```haskell
([$\circ$]) [$e_1$] [$e_2$]
```

mit

```haskell
[$f_{\circ}$] [$\lift{e_1}$] [$\lift{e_2}$]
```

übersetzt, wobei $f_{\circ}$ der Bezeichner der vordefinierten Funktion für
$\circ$ in Coq ist.

| $(\circ)$        | $f_{\circ}$      |
|------------------|------------------|
| `(+)`{.haskell}  | `addInt`{.coq}   |
| `(-)`{.haskell}  | `subInt`{.coq}   |
| `(*)`{.haskell}  | `mulInt`{.coq}   |
| `(^)`{.haskell}  | `powInt`{.coq}   |
| `(&&)`{.haskell} | `andBool`{.coq}  |
| `(||)`{.haskell} | `orBool`{.coq}   |
| `(<=)`{.haskell} | `leInt`{.coq}    |
| `(<)`{.haskell}  | `ltInt`{.coq}    |
| `(==)`{.haskell} | `eqInt`{.coq}    |
| `(/=)`{.haskell} | `neqInt`{.coq}   |
| `(>=)`{.haskell} | `geInt`{.coq}    |
| `(>)`{.haskell}  | `gtInt`{.coq}    |

Alternativ könnten für die Funktionen $f_{\circ}$ auch Notationen eingeführt
werden, sodass die Syntax der resultierenden Ausdrücke an die aus Haskell
erinnert.

### Prefixoperatoren

Das unäre Minus ist *syntaktischer Zucker* für die `negate`{.haskell} Funktion.

```haskell
-[$e_1$]
```

```coq
negate [$\lift{e_1}$]
```

wobei $e_1 :: \Int$ ein Ausdruck ist.

Diese wird in Coq wie folgt vordefiniert:

```coq
Definition negate
  {[$F$] : Type -> Type} ([$C_F$] : Container [$F$])
  (n : Free [$C_F$] Int) : Free [$C_F$] Int :=
  n >>= fun(n' : Int) => pure (Z.opp n').
```

## Bedingungen

In einem `if`{.coq}-Ausdruck muss aus der Monade der boolsche Wert von der
Bedingung herausgeholt werden.

```haskell
if [$e_1$] then [$e_2$] else [$e_3$]
```

```coq
[$\lift{e_1}$] >>= fun([$x_1$] : bool) => if [$x_1$] then [$\lift{e_2}$] else [$\lift{e_3}$]
```

wobei $e_1 :: \Bool$, $e_2, e_3 :: \tau$ Ausdrücke sind und $x_1$ eine
frische Variable ist.

## Fallunterscheidung

Bevor eine Fallunterscheidung auf einem Wert durchgeführt werden kann muss
dieser ebenfalls aus der Monade herausgeholt werden:

```haskell
case [$e$] of
  [$C_1$] [$x_{1,1}$] [$\ldots$] [$x_{1,p_1}$] -> [$e_1$]
  [$C_2$] [$x_{2,1}$] [$\ldots$] [$x_{2,p_2}$] -> [$e_2$]
  [$\ldots$]
  [$C_m$] [$x_{m,1}$] [$\ldots$] [$x_{m,p_m}$] -> [$e_m$]
```

```coq
[$\lift{e}$] >>= fun(x : [$\liftT{\tau}$]) =>
  match [$x$] with
  | [$C_1$] [$x_{1,1}$] [$\ldots$] [$x_{1,p_1}$] => [$\lift{e_1}$]
  | [$C_2$] [$x_{2,1}$] [$\ldots$] [$x_{2,p_2}$] => [$\lift{e_2}$]
  | [$\ldots$]
  | [$C_m$] [$x_{m,1}$] [$\ldots$] [$x_{m,p_m}$] => [$\lift{e_m}$]
  end
```

wobei $e :: \tau$ sowie $e_1, \ldots, e_m :: \tau'$ Ausdrücke,
$C_1, \ldots, C_m$ die Konstruktoren von $\tau$ sind und $x$ eine frische
Variable ist.

#### Fehlerterme

Die `Partial`{.coq} Typklasse ermöglicht es die Fehlerterme sehr einfach zu
übersetzen:

- $\lift{\undefined} = \undefined$
- $\lift{(\error{"<error message>")}} = \error{"<error message>"}$

## Lambda Abstraktionen

```haskell
\[$x_1$] [$\ldots$] [$x_n$] -> [$e$]
```

```coq
pure (fun([$x_1$] [$\ldots$] [$x_n$]) => [$\lift{e}$])
```

wobei $x_1, \ldots x_n$ Variablenpattern sind und $e$ ein Ausdruck ist.

## Literale

- In Coq sind die Zahlenliterale standardmäßig vom Typ `nat`{.coq}, da wir aber
  Zahlen immer mit dem Typ `Z`{.coq} darstellen wollen, wird das Suffix
  `%Z`{.coq} angehängt. Coq unterstützt außerdem nur die Angabe von Zahlen in
  der Basis $10$. Die Zahlen müssen schließlich noch in die Monade gehoben
  werden.

    ```haskell
    0
    42
    0xA2
    0o755
    ```

    ```coq
    pure 0%Z
    pure 42%Z
    pure 162%Z
    pure 493%Z
    ```

- Boolsche Werte müssen bei der Übersetzung nur umbenannt und in die Monade
  gehoben werden:

    + $\lift{\True} = \pure{\true}$
    + $\lift{\False} = \pure{\false}$

### Listen

Die Listenkonstruktoren `[]`{.haskell escapeinside="||"} und `(:)`{.haskell}
werden in die vordefinierten Konstruktoren `Nil`{.coq} bzw. `Cons`{.coq}
übersetzt. Für die Anwendung dieser Konstruktoren gelten dann die oben
stehenden Übersetzungsregeln. D.h.

- `[]`{.haskell escapeinside="||"} wird mit `pure Nil`{.coq} und
- `[$e_1$] : [$e_2$]`{.haskell}, wobei $e_1 :: \tau$ und $e_2 :: [\tau]$
  Ausdrücke sind, wird mit `pure (Cons [$\lift{e_1}$] [$\lift{e_2}$])`

übersetzt.

Die Kurzschreibweise für eine Liste mit den Elementen $e_1, \ldots, e_n$

```{.haskell escapeinside="||"}
[|$e_1$|, |$\ldots$|, |$e_n$|]
```

muss genauso übersetzt werden wie

```{.haskell escapeinside="||"}
|$e_1$| : (|$\ldots$| : (|$e_n$| : []))
```

da das [language-coq][] Packet es momentan noch nicht erlaubt Code zu
generieren, der eigene Notationen wie

```coq
Notation "[]" := Nil.
Notation "[ x0 ]" := (Cons x0 (pure Nil)).
Notation "[ x0 ; x1 ; .. ; xn ]" :=
  (Cons x0 (pure (Cons x1 .. (pure (Cons xn (pure Nil))) ..))).
```

verwenden. Dennoch könnten die oben stehende Notationen dazu genutzt werden,
um Code innerhalb von Beweisen lesbarer zu machen. Alternativ kann auch der
`pure` Konstruktor "versteck" werden:

```coq
Notation "[]" := (pure Nil).
Notation "[ x0 ; .. ; xn ]" :=
  (pure (Cons x0 .. (pure (Cons xn (pure Nil))) ..)).
```

### Tuple

Die Konstruktoren für nullelementige Tupel `()`{.haskell} und Paare
`(,)`{.haskell} werden in die vordefinierten Konstruktoren `tt`{.coq}
bzw. `Pair_`{.coq} übersetzt. Für die Anwendung dieser Konstruktoren gelten
dann die oben stehenden Übersetzungsregeln.D.h.

- `()`{.haskell} wird mit `pure tt`{.coq} und
- `([$e_1$], [$e_2$])`{.haskell}, wobei $e_1$ und $e_2$ Ausdrücke sind,
  wird mit `pure (Pair_ [$\lift{e_1}$] [$\lift{e_2}$])`{.coq}

übersetzt.

Auch in diesem Fall wäre es möglich über eigene Notationen die Lesbarkeit
zu verbessern:

```coq
Notation "()" := (pure tt).
Notation "( x , y )" := (pure (Pair_ x y)).
```

[Abel2005]: http://www2.tcs.ifi.lmu.de/~abel/haskell05.pdf
[Dylus2019]: https://arxiv.org/pdf/1805.08059.pdf
[Jessen2019]: https://github.com/beje8442/haskellToCoqCompiler
[language-coq]: https://github.com/just95/language-coq
