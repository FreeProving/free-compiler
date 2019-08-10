---
title: |
  Übersetzung von Haskell nach Coq \protect\
  QuickCheck Eingenschaften übersetzen
author: Justin Andresen
lang: de-DE
pandoc-minted:
  default-attributes:
    escapeinside: "@@"
    mathescape: "true"
    tabsize: "2"
    breaklines: "true"
  default-block-attributes:
    numbersep: "5pt"
    frame: "lines"
    framesep: "2mm"
---

\newcommand{\lift}[1]{{#1}^{\dagger}}
\newcommand{\liftProp}[1]{{#1}^{\ddagger}}

\newpage
# Eineitung

Der eigentliche Zweck der Übersetzung von Haskell Programmen zu Coq ist es
in Coq Eigenschaften über die übersetzten Programme zu beweisen. Während der
Entwicklung des Haskell Programms sollten die Entwickler sich dabei bereits
durch Tests davon überzeugt haben, dass diese Eigenschaften wahrscheinlich
erfüllt sind. Nur wenn die Tests erfolgreich sind lohnt es sich mithilfe von
Coq zu verifizieren, dass die Eigenschaften auch im Allgemeinen gelten. In
Haskell ist es üblich solche Eigenschaften mithilfe der QuickCheck
Bibliothek auszudrücken. Es wäre daher erstrebenswert die bereits für die
Tests verwendeten QuickCheck Eigenschaften mit nach Coq zu übersetzen.

In diesem Dokument wird eine optionale Erweiterung der Übersetzung
beschrieben, die es erlaubt in Haskell definierte QuickCheck Eigenschaften
automatisch zu entsprechenden Aussagen in Coq zu übersetzen.

\newpage
# Erkennung von QuickCheck

Ein Haskell Programm, in dem QuickCheck verwendet wird importiert in der
Regel die QuickCheck Bibliothek.

```haskell
import Test.QuickCheck
```

Nur wenn in einem Modul diese `import`{.haskell} Anweisung gefunden wird
sollten die in diesem Dokument beschriebenen Übersetzungsschritte durchgeführt
werden. Da ansonsten keine `import`{.haskell}s unterstützt werden, dürfen
in dem restlichen Modul die von QuickCheck definierten Funktionen und
Datentypen nur eingeschränkt verwendet werden. Insbesondere wird nur der
Datentyp `Property`{.haskell} sowie die Operatoren

- `(==>)`{.haskell},
- `(===)`{.haskell},
- `(=/=)`{.haskell},
- `(.&&.)`{.haskell} und
- `(.||.)`{.haskell}

unterstützt. Diese Operatoren dürfen genauso wie der Datentyp
`Property`{.haskell} ausschließlich innerhalb von QuickCheck Eigenschaften
verwendet werden.

\newpage
# Übersetzung

## Übersetzung von Eigenschaftsdeklarationen

In QuickCheck beginnen die Namen der Funktionen, durch die eine zu testende
Eigenschaft definiert wird, mit dem Prefix `prop_`{.haskell}.
Wenn QuickCheck Unterstützung erkannt wurde, sollten solche
Funktionsdeklarationen durch den Compiler gesondert behandelt werden.

Eine von $n$ Parametern abhängige Eigenschaft mit dem Namen $P$ wird durch eine
Funktionsdeklaration der folgenden Form festgelegt.

```haskell
prop_@$P$@ :: @$\tau_1$@ -> @$\ldots$@ -> @$\tau_n$@ -> @$\tau$@
prop_@$P$@ @$x_1$@ @$\ldots$@ @$x_n$@ = @$p$@
```

wobei $\tau$ entweder der Typ `Bool`{.haskell} oder `Property`{.haskell}
sein muss. Die Deklaration wird in ein Coq `Theorem`{.haskell} der
folgenden Form übersetzt.

```coq
Theorem prop_@$P$@:
  forall {@$\alpha_1$@ @$\ldots$@ @$\alpha_m$@ : Type} (@$x_1$@ : @$\lift{tau_1}$@) @$\ldots$@ (@$x_n$@ : @$\lift{tau_n}$@), @$\liftProp{p}$@.
Proof.
  (* FILL IN HERE *)
Admitted.
```

Dabei seien $\alpha_1, \ldots, \alpha_m$ die Typvariablen in der Typsignatur
und $\liftProp{p}$ bezeichne die in den nachfolgenden Abschnitten beschriebene
Übersetzung von QuickCheck Eigenschaften zu Aussagen in Coq.

## Übersetzung von Eigenschaften

### Boolsche Eigenschaften

Bei der Übersetzung einer Eigenschaft $p$ muss unterschieden werden, ob diese
den Typ `Bool`{.haskell} oder `Property`{.haskell} hat.

Alle Eigenschaften `@$p$@ :: Bool`{.haskell} werden zu einer Aussage übersetzt,
die genau dann erfüllt ist, wenn der Ausdruck $p$ zu `True`{.haskell} auswertet.

```coq
@$\lift{p}$@ = True_
```

### Properties

In der QuickCheck Bibliothek werden außerdem Operatoren definiert, die
es erlauben komplexere Eigenschaften zu konstruieren. Einige dieser Operationen
können wir versuchen zu erkennen und in entsprechende Coq Aussagen übersetzen.

Ausdrücke für solche Eigenschaften haben dann den Typ `Property`{.haskell}.
Da wir jedoch keine Typinferenz durchführen und Eigenschaften auch
verschachtelt sein können, müssen wir hier davon ausgehen, dass jede Eigenschaft
den Typ `Bool`{.haskell} hat, es sei denn, dass einer der hier beschriebenen
Operatoren von QuickCheck verwendet wird.

#### Vorbedingungen

Eine häufig genutzte Operation ist die Vorbedingung

```haskell
@$p_1$@ ==> @$p_2$@
```

Diese können wir in Coq direkt als als Implikation ausdrücken:

```coq
@$\liftProp{p_1}$@ -> @$\liftProp{p_2}$@
```

#### Gleichheit

Es ist des Weiteren üblich in QuickCheck die Gleichheit von zwei Ausdrücken
zu fordern. Unser Übersetzer erlaubt es momentan nur `Int`{.haskell}s
miteinander zu vergleichen, da Typklassen nicht unterstützt werden. Desweiteren
wäre es unpraktisch für Beweise, wenn die Gleichheit in Coq über `eqb`{.coq}
ausgedrückt werden würde. Wir könnten den QuickCheck Operator `(===)`{.haskell}
nutzen, um eine Unterscheidung von dem regulären Gleichheitsoperator zu
ermöglichen und direkt in die reflexive Gleichheit zu übersetzen.

```haskell
@$e_1$@ === @$e_2$@
```

```coq
@$\lift{e_1}$@ = @$\lift{e_2}$@
```

Analog können wir auch für die Ungleichheit vorgehen:

```haskell
@$e_1$@ =/= @$e_2$@
```

```coq
@$\lift{e_1}$@ <> @$\lift{e_2}$@
```

#### Konjunktion und Disjunktion

Auch die Konjunktion und Disjunktion von QuickCheck Eigenschaften können in
Coq direkt als Konjunktion bzw. Disjunktion von Aussagen dargestellt werden
statt den Umweg über die Boolschen Operationen `andb`{.coq} und `orb`{.coq}
zu nehmen.

```haskell
@$p_1$@ .&&. @$p_2$@
@$p_1$@ .||. @$p_2$@
```

```coq
@$\liftProp{p_1}$@ /\ @$\liftProp{p_2}$@
@$\liftProp{p_1}$@ \/ @$\liftProp{p_2}$@
```
