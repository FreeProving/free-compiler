---
title: |
  Übersetzung von Haskell nach Coq \protect\
  Monadische Transformation
author: Justin Andresen
lang: de-DE
pandoc-minted:
  default-attributes:
    escapeinside: "\\\\[\\\\]"
    mathescape: "true"
  default-block-attributes:
    numbersep: "5pt"
    frame: "lines"
    framesep: "2mm"
    tabsize: "2"
    breaklines: "true"
---

\newcommand{\lift}[1]{{#1}^{\dagger}}
\newcommand{\liftT}[1]{{#1}^{ * }}
\newcommand{\m}[1]{m\,{#1}}
\newcommand{\mreturn}[1]{\texttt{m\_return}\,{#1}}

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

\newpage
# Eineitung

In diesem Dokument wird beschrieben, wie die Haskellmodule, -ausdrücke und
-typen nach Coq übersetzt werden können und wie dabei Monaden eingesetzt
werden müssen, sodass die Semantik des Haskellprogramms (insbesondere in Bezug
auf partielle Funktionen und Lazy Auswertung) beibehalten wird. Dabei wird
davon ausgegangen, dass der Haskellcode wie in `notes/input-format.md`
beschrieben aufgebaut ist.

In diesem Dokument wird noch nicht konkret auf die *Free* Monade eingegangen.
Hier bezeichne $m$ eine beliebige (konfigurierte) Monade mit den
Operationen `>>=`{.coq} und `m_return`{.coq}.
Das Prefix `m_`{.coq} wird benötigt, da da es sich bei `return`{.coq} um ein
Schlüsselwort in Coq handelt.

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
  \lift{\tau} = \m{\liftT{\tau}}
$$

Darüber hinaus muss rekursiv (mithilfe von $\liftT{\tau}$) der Argument- und
Rückgabetyp von jedem in $\tau$ enthaltenen Funtionstypen übersetzt werden.

- Für alle Typen $\tau_1, \tau_2 :: \type$:

    $$
      \liftT{(\tau_1 \to \tau_2)} = \lift{\tau_1} \to \lift{\tau_2}
    $$

Ansonsten bleibt der Typausdruck unverändert:

- Für alle Typvariablen $\alpha$, Datentypen $D$ und Typsynonymen $S$:

    \begin{align*}
      \liftT{\alpha} &= \alpha \\
      \liftT{D}    &= D      \\
      \liftT{S}    &= S      \\
    \end{align*}

- Für alle Typkonstruktoren $\tau_1 :: \type \to \kappa$ und Typen
  $\tau_2 :: \type$:

    $$
      \liftT{(\tau_1\,\tau_2)} = \liftT{\tau_1} \, \liftT{\tau_2}
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

$\liftT{[\tau]} = \List\,\liftT{\tau}$, wobei $\tau :: \type$

Dabei sollte der Typ `List`{.coq} genau so definiert werden, wie der
Compiler die folgende Datentypdeklaration übersetzen würde:

```haskell
data List a = Nil | Cons a (List a)
```

Hier gehen wir von folgender Übersetzung aus:

```coq
Inductive List (a : Type) :=
  | Nil : List a
  | Cons : [$m$] a -> [$m$] (List a) -> List a.
Arguments Nil {a}.
Arguments Cons {a}.
```

### Tupel

- $\liftT{()} = unit$

    Der Typ `unit`{.coq} ist in Coq vordefiniert und hat nur den Konstruktor
    `tt`{.coq}.

- $\liftT{(\tau_1, \tau_2)} = \Pair\,\liftT{\tau_1}\,\liftT{\tau_2}$,
  wobei $\tau_1, \tau_2 :: \type$ Typen sind.

    Dabei sollte der Typ `Pair`{.coq} genau so definiert werden, wie der
    Compiler die folgende Datentypdeklaration übersetzen würde:

    ```haskell
    data Pair a b = Pair a b
    ```

    Hier gehen wir von folgender Übersetzung aus:

    ```coq
    Inductive Pair (a b : Type) :=
      | Pair_ : [$m$] a -> [$m$] b -> Pair a b.
    Arguments Pair_ {a} {b}.
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
Inductive [$D$] ([$\alpha_1$] [$\ldots$] [$\alpha_m$] : Type) : Type :=
  | [$C_1$] : [$\lift{\tau_{1,1}}$] -> [$\ldots$] -> [$\lift{\tau_{1,p_1}}$] -> [$D$] [$\alpha_1$] [$\ldots$] [$\alpha_m$]
  | [$C_2$] : [$\lift{\tau_{2,1}}$] -> [$\ldots$] -> [$\lift{\tau_{2,p_2}}$] -> [$D$] [$\alpha_1$] [$\ldots$] [$\alpha_m$]
  | [$\ldots$]
  | [$C_n$] : [$\lift{\tau_{n,1}}$] -> [$\ldots$] -> [$\lift{\tau_{n,p_n}}$] -> [$D$] [$\alpha_1$] [$\ldots$] [$\alpha_m$].
```

wobei $\alpha_1, \ldots, \alpha_n$ Typvariablen, $C_1, \ldots, C_m$
die Konstruktoren von $D$, und $\tau_{i,1}, \ldots \tau_{i,p_i}$ für alle
$i \in \{\, 1, \ldots, m \,\}$ Typen sind.

Zusätzlich wird für jeden Konstruktor spezifiziert, dass die Typparameter
optional sind.

```coq
Arguments [$C_1$] {[$\alpha_1$]} [$\ldots$] {[$\alpha_m$]}.
[$\vdots$]
Arguments [$C_n$] {[$\alpha_1$]} [$\ldots$] {[$\alpha_m$]}.
```

\newpage
## Übersetzung von Typsynoymdeklarationen

```haskell
type [$S$] [$\alpha_1$] [$\ldots$] [$\alpha_m$] = [$\tau$]
```

```coq
Definition [$S$] ([$\alpha_1$] [$\ldots$] [$\alpha_m$] : Type) := [$\liftT{\tau}$].
```

wobei $\alpha_1, \ldots, \alpha_n$ Typvariablen sind und $\tau$ ein Typ oder
Typkonstruktor ist.

Wir übersetzen hier $\tau$ als $\liftT{\tau}$ und nicht als
$\lift{\tau}$, da es egal sein soll, ob zuerst übersetzt und dann das Typsynonym
expandiert wird oder an­ders­he­r­um.
Übersetzt man zunächst $S$ zu $\lift{S} = \m{\liftT{S}} = \m{S}$ und expandiert
dann $S$ zu $\liftT{\tau}$, erhält man $\m{\liftT{\tau}}$. Andersherum würde
man zunächst $S$ zu $\tau$ expandieren und dann zu
$\lift{\tau} = \m{\liftT{\tau}}$ übersetzten. Würde man in der
Tysynonymdeklaration hingegen $\tau$ zu $\lift{\tau} = \m{\liftT{\tau}}$
übersetzen, so erhilte man beim Expandieren von $S$ im Coq Code
$\m{(\m{\liftT{\tau}})}$.

\newpage
## Übersetzung von Funktionsdeklaration
### Nicht-rekursive Funktionen

```haskell
[$f$] :: [$\tau_1$] -> [$\ldots$] -> [$\tau_n$] -> [$\tau$]
[$f$] [$x_1$] [$\ldots$] [$x_n$] = [$e$]
```

```coq
Definition [$f$] {[$\alpha_1$] [$\ldots$] [$\alpha_m$] : Type} ([$x_1$] : [$\lift{\tau_1}$]) [$\ldots$] ([$x_n$] : [$\lift{\tau_n}$]) : [$\lift{\tau}$]
  := [$\lift{e}$].
```

wobei $\tau_1, \ldots, \tau_n$ sowie $\tau$ Typen und $x_1, \ldots, x_n$
Variablenpattern sind, $e$ ein Ausdruck ist und $\alpha_1, \ldots, \alpha_m$
die Typvariablen in der Typsignatur von $f$ sind.

Diese Übersetzung entspricht der von [Abel et al.][Abel2005] beschriebenen
Optimierung. Ohne die Optimierung wäre der Typ von $f$ nach der Übersetzung:

$$
  \lift{(\tau_1 \to \ldots \to \tau_n \to \tau)}
  = \m{(\lift{\tau_1} \to \m{(\ldots \to \m{(\lift{\tau_n} \to \tau)})} \ldots)}
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

wobei $\tau_1, \ldots, \tau_n$ sowie $\tau$ Typen und $x_1, \ldots, x_n$
Variablenpattern sind und $e$ ein Ausdruck ist.

Für den $j$-ten `case`{.haskell}-Ausdruck in $e$ der Form

```haskell
case [$x_i$] of
  [$\vdots$]
```

erzeugen wir eine Hilfsfunktion der Form

```coq
Fixpoint [$f^{(j)}$] {[$\alpha_1$] [$\ldots$] [$\alpha_m$] : Type} ([$x_1$] : [$\lift{\tau_1}$]) [$\ldots$] ([$x_{i-1}$] : [$\lift{\tau_{i-1}}$])
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
    \lift{x_i} = \mreturn{x_i}
  $$

- Alle rekursiven Aufrufe innerhalb der Hilfsfunktionen werden ersetzt, indem
  die Definition der Hauptfunktion (siehe unten) eingesetzt wird (*inlining*).
  Daher sind alle Hilfsfunktionen gegenseitig rekursiv und müssen in einem
  einzigen `Fixpoint [$\ldots$] with [$\ldots$]` Sentence zusammengefasst
  werden.

Bei der Übersetzung der Hauptfunktion

```coq
Definition [$f$] {[$\alpha_1$] [$\ldots$] [$\alpha_m$] : Type} ([$x_1$] : [$\lift{\tau_1}$]) [$\ldots$] ([$x_n$] : [$\lift{\tau_n}$]) : [$\lift{\tau}$] := [$\lift{e}$]
```

wird der $j$-te `case`{.haskell}-Ausdruck der Form

```haskell
case [$x_i$] of
  [$\vdots$]
```

durch einen Aufruf der entsprechenden Hilfsfunktion ersetzt:

```coq
[$x_i$] >>= fun([$x_i'$] : [$\liftT{\tau_i}$]) =>
  [$f^{(j)}$] [$x_1$] [$\ldots$] [$x_{i-1}$] [$x_i'$] [$x_{i+1}$] [$\ldots$] [$x_n$]
```

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
Konversion durchgeführt werden, d.h. die fehlenden Argumente werden
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
müssen nur die Argumente rekursiv übersetzt werden:

```haskell
[$f$] [$e_1$] [$\ldots$] [$e_n$]
```

```coq
[$f$] [$\lift{e_1}$] [$\ldots$] [$\lift{e_n}$]
```

### Anwendung von Konstruktoren

Falls `[$C$] [$\tau_1$] [$\ldots$] [$\tau_n$]`{.haskell} ein Konstruktor des
Datentyps `[$D$] [$\tau_{\alpha_1}$] [$\ldots$] [$\tau_{\alpha_m}$]`{.haskell}
ist und $e_1 :: \tau_1$, $\ldots$, $e_n :: \tau_n$ Ausdrücke sind, dann hat $C$
in Coq den Typ `[$\lift{\tau_1}$] -> [$\ldots$] -> [$\lift{\tau_n}$] -> [$D$] [$\tau_{\alpha_1}$] [$\ldots$] [$\tau_{\alpha_m}$]`{.coq}.
Das Ergebnis der Konstruktoranwendung befindet sich also nicht in einem
monadischen Kontext. Daher kann die oben stehende Übersetzungsregel für
definierte Funktionen nicht verwendet werden, sondern es muss ein weiteres
`m_return`{.coq} eingefügt werden.

```haskell
[$C$] [$e_1$] [$\ldots$] [$e_n$]
```

```coq
m_return ([$C$] [$\lift{e_1}$] [$\ldots$] [$\lift{e_n}$])
```

Dies gilt auch bei nullstelligen Konstruktoren:

```coq
m_return [$C$]
```

### Anwendung vordefinierter Funktionen

Zum derzeitigen Zeitpunkt existieren ausschließlich vordefinierte Funktionen
in Form von Präfix- und Infixoperationen wie z.B. `(+)`{.haskell}. Die
Gegenstücke dieser Operationen in Coq kann man nicht direkt auf die monadischen
Werte anwenden:

```coq
Fail Compute None + None.
(*
  ==> The command has indeed failed with message:
  The term "None" has type "option ?A" while it is expected to have type "nat".
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
    m_return ([$\lift{f}$] [$x_1$] [$\ldots$] [$x_n$])
) [$\ldots$] )
```

wobei $x_1, \ldots, x_n$ frische Variablen sind.

Dadurch wird der entstehende Code unleserlich. Im Fall von partiellen
Anwendungen wird der Effekt aufgrund der $\eta$-Konversionen noch
verstärkt. Das Problem lässt sich umgehen, indem in Coq nicht die eingebauten
Operationen verwendet werden, sondern eigene *wrapper* Funktionen vordefiniert
werden, deren Interface dem einer regulär übersetzten Funktion entspricht.
Für `(+)`{.haskell} könnte man in Coq beispielsweise folgende Funktion
in Coq auf `nat` definieren:

```coq
Definition plus (n1 : [$m$] nat) (n2 : [$m$] nat) : [$m$] nat :=
  n1 >>= fun(n1' : nat) =>
    n2 >>= fun(n2' : nat) =>
      m_return (n1' + n2').
```

`plus`{.coq} kann genauso verwendet werden, wie jede in Haskell definierte
Funktion. Der Compiler muss also nicht mehr zwischen definierten und
vordefinierten Funktionen unterscheiden.

Dieser Ansatz erlaubt uns nun auch einfach die Basisdatentypen auszuwechseln.
Z.B. soll `Int`{.haskell} mit `Z`{.coq} und nicht mit `nat`{.coq} übersetzt
werden. Es muss dazu nicht die Übersetzung von Funktionsanwendungen angepasst
werden sondern lediglich die vordefinierte Funktion `plus`{.coq}:

```coq
Definition plus (z1 : [$m$] Z) (z2 : [$m$] Z) : [$m$] Z :=
  z1 >>= fun(z1' : Z) =>
    z2 >>= fun(z2' : Z) =>
      m_return (Z.add z1' z2').
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
    \lift{e_1} &:: \m{(\lift{\tau} \to \lift{\tau'})} \\
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
Definition negate (n : [$m$] Int) : [$m$] Int :=
  n >>= fun(n' : Int) => m_return (Z.opp n').
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

### Fehlerterme

Die Übersetzung der Fehlerterme hängt von der konfigurierten Monade ab.

## Lambda Abstraktionen

```haskell
\[$x_1$] [$\ldots$] [$x_n$] -> [$e$]
```

```coq
m_return (fun([$x_1$] [$\ldots$] [$x_n$]) => [$\lift{e}$])
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
    m_return 0%Z
    m_return 42%Z
    m_return 162%Z
    m_return 493%Z
    ```

- Boolsche Werte müssen bei der Übersetzung nur umbenannt und in die Monade
  gehoben werden:

    + $\lift{\True} = \mreturn \true$
    + $\lift{\False} = \mreturn \false$

### Listen

Die Listenkonstruktoren `[]`{.haskell escapeinside="||"} und `(:)`{.haskell}
werden in die vordefinierten Konstruktoren `Nil`{.coq} bzw. `Cons`{.coq}
übersetzt. Für die Anwendung dieser Konstruktoren gelten dann die oben
stehenden Übersetzungsregeln. D.h.

- `[]`{.haskell escapeinside="||"} wird mit `m_return Nil`{.coq} und
- `[$e_1$] : [$e_2$]`{.haskell}, wobei $e_1 :: \tau$ und $e_2 :: [\tau]$
  Ausdrücke sind, wird mit `m_return (Cons [$\lift{e_1}$] [$\lift{e_2}$])`

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
Notation "[ x0 ]" := (Cons x0 (m_return Nil)).
Notation "[ x0 ; x1 ; .. ; xn ]" :=
  (Cons x0 (m_return (Cons x1 .. (m_return (Cons xn (m_return Nil))) ..))).
```

verwenden. Dennoch könnten die oben stehende Notationen dazu genutzt werden,
um Code innerhalb von Beweisen lesbarer zu machen. Alternativ kann auch das
`m_return` "versteck" werden:

```coq
Notation "[]" := (m_return Nil).
Notation "[ x0 ; .. ; xn ]" :=
  (m_return (Cons x0 .. (m_return (Cons xn (m_return Nil))) ..)).
```

### Tuple

Die Konstruktoren für nullelementige Tupel `()`{.haskell} und Paare
`(,)`{.haskell} werden in die vordefinierten Konstruktoren `tt`{.coq}
bzw. `Pair_`{.coq} übersetzt. Für die Anwendung dieser Konstruktoren gelten
dann die oben stehenden Übersetzungsregeln.D.h.

- `()`{.haskell} wird mit `m_return tt`{.coq} und
- `([$e_1$], [$e_2$])`{.haskell}, wobei $e_1$ und $e_2$ Ausdrücke sind,
  wird mit `m_return (Pair_ [$\lift{e_1}$] [$\lift{e_2}$])`{.coq}

übersetzt.

Auch in diesem Fall wäre es möglich über eigene Notationen die Lesbarkeit
zu verbessern:

```coq
Notation "()" := (m_return tt).
Notation "( x , y )" := (m_return (Pair_ x y)).
```

[Abel2005]: http://www2.tcs.ifi.lmu.de/~abel/haskell05.pdf
[Jessen2019]: https://github.com/beje8442/haskellToCoqCompiler
[language-coq]: https://github.com/just95/language-coq
