---
title: |
  Übersetzung von Haskell nach Coq
  Eingabeformat
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
---

\newcommand{\type}{ * }

\newpage
# Einleitung

In diesem Dokument wird beschrieben, wie die Haskellmodule aufgebaut sein
müssen, damit sie zu Coq übersetzt werden können. Ist eine dieser Anforderungen
nicht erfüllt, sollte von dem Compiler eine Fehlermeldung erzeugt werden.

Allgemein werden keine Spracherweiterungen unterstützt und es wird davon
ausgegangen, dass das Programm syntaktisch korrekt und typkorrekt ist.

Zu den Haupteinschränkungen zählt, dass vorerst keine Typklassen unterstützt
werden und Typkonstruktoren selber keine Typkonstruktoren als Argument erhalten
können (keine *higher-order type operators*). Es wird nur eine kleine Auswahl
von Ausdrücken unterstützt und Pattern-Matching kann nur explizit mithilfe
von `case`{.haskell}-Ausdrücken durchgeführt werden.

Die Spezifikationen in diesem Dokument sind nicht final, sondern beschreibt den
minimalen Umfang des durch den späteren Compiler unterstützten Sprachumfangs.
Es ist möglich, dass in Laufe der Bearbeitung weitere Sprachkonstrukte
aufgenommen werden oder Anforderungen in diesem Dokument noch gelockert bzw.
verschärft werden.

\newpage
# Module

```haskell
-- Optional module header with optional export list.
module [$M$] ([$\ldots$]) where

-- No imports.

-- Declarations ...
```

- Der Modulkopf ist optional. Wenn ein Modulkopf angegeben worden ist, darf
  dieser eine Liste von exportierten Symbolen enthalten, diese wird jedoch
  bei der Übersetzung nicht beachtet.

- Das Importieren von Modulen wird nicht unterstützt.
  Daher dürfen keine `import`{.haskell} Anweisungen vorkommen.

- Das Modul darf nur die unten aufgeführten Deklarationen enthalten.
  Dazu zählen Datentyp-, Typsynonym- und Funktionsdeklarationen.
  Es werden insbesondere noch keine Typklassen unterstützt.

## Datentypdeklarationen

Die Deklaration eines Datentyps $D$ hat die folgende Form:

```haskell
data [$D$] [$\alpha_1$] [$\ldots$] [$\alpha_n$] =
    [$C_1$] [$\tau_{1,1}$] [$\ldots$] [$\tau_{1,p_1}$]
  | [$C_2$] [$\tau_{2,1}$] [$\ldots$] [$\tau_{2,p_2}$]
  | [$\ldots$]
  | [$C_m$] [$\tau_{m,1}$] [$\ldots$] [$\tau_{m,p_m}$]
```

wobei $\alpha_1, \ldots, \alpha_n$ Typvariablen, $C_1, \ldots, C_m$
die Konstruktoren von $D$, und $\tau_{i,1}, \ldots \tau_{i,p_i}$ für alle
$i \in \{\, 1, \ldots, m \,\}$ Typen sind.

- Es werden vorerst keine mit `newtype`{.haskell} deklarierten Datentypen
  unterstützt und die Argumente der Konstruktoren können nicht mit `!` als
  strikt markiert werden.

- Es werden keine *record* oder *infix* Konstruktoren unterstützt.

- Für die Sorten der Typvariablen sind die im Abschnitt über Typausdrücke
  angegebenen Einschränkungen zu beachten.

- Da Typklassen nicht unterstützt werden, gibt es keinen Typklassenkontext
  wie z.B. `Eq a => [$\ldots$]`{.haskell} und es kann nicht mit
  `deriving`{.haskell} gerarbeitet werden.

## Typsynonymdeklarationen

Die Deklaration eines Typsynonyms $S$ hat die folgende Form:

```haskell
type [$S$] [$\alpha_1$] [$\ldots$] [$\alpha_n$] = [$\tau$]
```

wobei $\alpha_1, \ldots, \alpha_n$ Typvariablen sind und $\tau$ ein Typ oder
Typkonstruktor ist.

Für die Sorten der Typvariablen sind die im Abschnitt über Typausdrücke
angegebenen Einschränkungen zu beachten.

## Funktionsdeklarationen

Eine Funktionsdeklaration für eine $n$-stellige Funktion $f$ hat folgende Form:

```haskell
[$f$] :: [$\tau_1$] -> [$\ldots$] -> [$\tau_n$] -> [$\tau$]
[$f$] [$x_1$] [$\ldots$] [$x_n$] = [$e$]
```

wobei $\tau_1, \ldots, \tau_n$ sowie $\tau$ Typen und $x_1, \ldots, x_n$
Variablenpattern sind und $e$ ein Ausdruck ist. Der Ausdurck $e$ muss vom Typ
$\tau$ sein, wenn für alle $i \in \{\, 1, \ldots, n \,\}$ der Typ $\tau_i$ für
die Variable $x_i$ angenommen wird.

Unter dem Begriff der Funktionsdeklaration zählen wir hier auch nullstellige
Funktionen ($n = 0$, in `haskell-src-ext` *Pattern Bindings* genannt).
Diese haben die Form

```haskell
[$f$] :: [$\tau$]
[$f$] = e
```

wobei $\tau$ ein Typ ist und $e$ ein Ausdruck vom Typ $\tau$ ist.

### Typsignaturen

- Zu jeder deklarierten Funktion ist die Typsignatur explizit anzugeben.
  Die Funktion muss bezüglich dieser Typsignatur korrekt getypt sein.
  Sie wird benötigt, um die Typen der Argumente abzulesen.
  Eine Überprüfung der angegeben Typen oder das Inferieren nicht angegebener
  Typen ist nicht geplant.

- Die Typsignatur einer Funktion kann an beliebiger Stelle im Modul stehen.

- Es existieren keine Typsignaturen, für die keine Funktion deklariert ist.

- Da keine Typklassen unterstützt werden, enthält die Typsignatur keinen
  Typklassenkontext wie z.B. `Eq a => [$\ldots$]`{.haskell}.

- Polymorphe Funktionen werden unterstützt, d.h. die Typsignatur kann
  Typvariablen enthalten. Es sind jedoch die im Abschnitt über Typausdrücke
  angegebenen Einschränkungen für die Sorten der Typvariablen zu beachten.

Mit der oben festgelegten Form für Typsignaturen

```haskell
[$f$] :: [$\tau_1$] -> [$\ldots$] -> [$\tau_n$] -> [$\tau$]
```

ist im folgenden Codebeispiel die Typsignatur von der Funktion
`idSubst`{.haskell} nicht erlaubt, da das $\tau_1$ nicht direkt abgelesen
werden kann:

```haskell
data Term = Var String | [$\ldots$]
type Subst = String -> Term

idSubst :: Subst
idSubst s = Var s
```

Ein möglicher Ansatz zur Lösung dieses Problems wäre es, Typsynonyme in
Typsignaturen bedarfsgesteuert zu expandieren. Falls dieser Ansatz umgesetzt
wird, hätte eine Typsignatur im Allgemeinen die Form:

```haskell
[$f$] :: [$\tau$]
```

wobei $\tau$ ein beliebiger Typ ist.

### Funktionsregeln

- Es werden keine Deklarationen von *infix* Funktionen unterstützt.

- Jede Funktion wird durch genau eine Regel definiert.

- Guards werden nicht unterstützt.

- Auf der linken Regelseite einer $n$-stelligen Funktionsdeklaration steht der
  Funktionsname gefolgt von $n$ disjunkten Variablenpattern.

- Auf der rechten Regelseite steht ein Ausdruck in dem unten beschriebenen
  Format.

- Die Regel hat keinen `where`{.haskell}-clause.

### Rekursive Funktionen

- Funktionen dürfen rekursiv definiert werden.
- Es wird angestrebt, dass Funktionen auch gegenseitig rekursiv definiert
  werden können.
- Wenn eine Funktion rekursiv definiert ist, dann muss sie eines ihrer
  Argumente strukturell mithilfe eines `case`{.haskell}-Ausdrucks abbauen.

Wir gehen davon aus, dass die Fallunterscheidung "ganz außen" durchgeführt
wird, d.h. eine $n$-stellige rekursive Funktion $f$ hat die Form:

```haskell
[$f$] [$x_1$] [$\ldots$] [$x_n$] =
  case [$x_i$] of
    [$\vdots$]
```

wobei $i \in \{\, 1, \ldots, n \,\}$.

\newpage
# Ausdrücke

## Funktionsanwendungen

Eine Funktionsanwendung hat die Form:

```haskell
[$e_1$] [$e_2$]
```

wobei $e_1 :: \tau -> \tau'$ und $e_2 :: \tau$ Ausdrücke sind.

## Infixoperationen

Es werden Infixoperationen für vordefinierte Operatoren unterstützt. wie z.B. , `&&`{.haskell} und `||`{.haskell}
sowie ggf. weitere übliche Operatoren wie z.B. `++`{.haskell} unterstützt.

- `[$e_1$] [$\circ$] [$e_2$]`{.haskell}
- `([$\circ$] [$e_2$])`{.haskell}
- `([$e_1$] [$\circ$])`{.haskell}
- `([$\circ$]) [$e_1$] [$e_2$]`{.haskell}

wobei $(\circ) :: \tau_1 \to \tau_2 \to \tau$ eine vordefinierte Infixoperation
ist und $e_1 :: \tau_1$ sowie $e_2 :: \tau_2$ Ausdrücke sind.

Zu den unterstützten Operatoren zählen:

- **Arithmetische Operationen**:
  `+`{.haskell}, `-`{.haskell}, `*`{.haskell}, `/`{.haskell}
- **Bool'sche Operationen**:
  `&&`{.haskell}, `||`{.haskell}
- **Vergleich auf `Int`{.haskell}**:
  `<=`{.haskell}, `<`{.haskell},
  `==`{.haskell}, `/=`{.haskell},
  `>=`{.haskell}, `>`{.haskell}

## Bedingungen

Ein Bedingter Ausdruck hat die Form:

```haskell
if [$e_1$] then [$e_2$] else [$e_3$]
```

wobei $e_1 :: Bool$ und $e_2, e_3 :: \tau$ Ausdrücke sind.

## Fallunterscheidung

- Die Muster in einer Fallunterscheidung müssen Konstruktormuster sein und
  alle Teilmuster sind ausschließlich Variablenmuster.

- Es werden kein Guards unterstützt.

- Es müssen alle Konstruktoren aufgeführt werden.
  Die rechte Seite von `->` muss bei nicht implementierten Fällen ein
  Fehlerterm sein.

Ein erlaubter `case`-Ausdruck hat also folgende Form:

```haskell
case [$e$] of
  [$C_1$] [$x_{1,1}$] [$\ldots$] [$x_{1,p_1}$] -> [$e_1$]
  [$C_2$] [$x_{2,1}$] [$\ldots$] [$x_{2,p_2}$] -> [$e_2$]
  [$\ldots$]
  [$C_m$] [$x_{m,1}$] [$\ldots$] [$x_{m,p_m}$] -> [$e_m$]
```

wobei $e :: \tau$ sowie $e_1, \ldots, e_m :: \tau'$ Ausdrücke und
$C_1, \ldots, C_m$ die Konstruktoren von $\tau$ sind.

### Fehlerterme

Die Fehlerterme von nicht abgedeckten Fällen haben die Form:

- `undefined`{.haskell} oder
- `error "<error message>"`{.haskell}

Bei Varianten dürfen auch an anderen Stellen im Programm verwendet werden.

## Lambda Abstraktionen

- In dem Argumenten einer Lambda Abstraktion dürfen nur Variablenpattern
  verwendet werden.

Eine erlaubte Lambda Abstraktion hat also die folgende Form:

```haskell
\[$x_1$] [$\ldots$] [$x_n$] -> [$e$]
```

wobei $x_1, \ldots, x_n$ Variablenpattern sind und $e$ ein Ausdruck ist.

## Literale

- **Ganzzahlen** können in dezimaler, hexadezimaler und oktaler Schreibweise
  angegeben werden:

    ```haskell
    0
    42
    0xA2
    0o755
    ```
- Zum Erzeugen von **Boolsche Werten**  können wie üblich die Konstruktoren
  `True`{.haskell} und `False`{.haskell} verwendet werden.

### Listen

Listen können mit den Listenkonstruktoren

- `[]`{.haskell escapeinside=""} und
- `[$e_1$] : [$e_2$]`{.haskell} wobei $e_1 :: \tau$ und $e_2 :: [\tau]$
  Ausdrücke sind

sowie mit der Kurzschreibweise

- `[|$e_1$|, |$\ldots$|, |$e_n$|]`{.haskell escapeinside="||"}
  wobei $e_1, \ldots e_n$ Ausdrücke sind

erzeugt werden. Für den Listenkonstruktor `(:)`{.haskell} sind auch die
Schreibweisen

- `(:) [$e_1$] [$e_2$]`{.haskell},
- `([$e_1$] :)`{.haskell} sowie
- `(: [$e_2$])`{.haskell}

erlaubt.

Insbesondere werden *List Comprehensions* und Enumerationen aber nicht
unterstützt.

### Tuple

Es werden ausschließlich nullelementige Tuple und Paare unterstützt.

- `()`{.haskell}
- `([$e_1$], [$e_2$])`{.haskell}, wobei $e_1$ und $e_2$ Ausdrücke sind

Es bestünde die Möglichkeit weitere Tupelgrößen zu unterstützen, dann müssten
aber entsprechende Datentypdeklarationen dynamisch erzeugt werden. Alternativ
könnten weitere Tupeltypen statisch vordefiniert werden. Der GHC unterstützt
Tuple mit bis zu $62$ Elementen.

```haskell
GHCi> :t (,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,,)

[\text{<interactive>:1:1: error:}]
[\text{    A 63-tuple is too large for GHC}]
[\text{      (max size is 62)}]
[\text{      Workaround: use nested tuples or define a data type}]
```

\newpage
# Typausdrücke

## Vordefinierte Datentypen

Die folgenden Datentypen sind vordefiniert:

- `Int`{.haskell}
- `Bool`{.haskell}
- `[|$\tau$|]`{.haskell escapeinside="||"}
  wobei $\tau :: \type$ ein Typ ist.
- `()`{.haskell} (*Unit*) und
- `([$\tau_1$], [$\tau_2$])`{.haskell}
  wobei $\tau_1, \tau_2 :: \type$ Typen sind.
- `[$\tau_1$] -> [$\tau_2$]`{.haskell}
  wobei $\tau_1, \tau_2 :: \type$ Typen sind.


## Benutzerdefinierte Datentypen

- Für alle **Datentypdeklaration** mit dem Bezeichner $D$ und $n$ Typparametern
  ```haskell
  data [$D$] [$\alpha_1$] [$\ldots$] [$\alpha_n$] = [$\ldots$]
  ```
  darf $D$ als $n$-stelliger Typkonstruktor verwendet werden.

- Für alle **Typsynonymdeklaration** mit dem Bezeichner $S$ und $n$
  Typparametern, auf dessen rechten Seite ein $m$-stelliger Typkonstruktor
  $\tau$ steht
  ```haskell
  type [$S$] [$\alpha_1$] [$\ldots$] [$\alpha_n$] = [$\tau$]
  ```
  darf $S$ als $(n+m)$-stelliger Typkonstruktor verwendet werden.

## Typvariablen

Wenn $\alpha$ eine Typvariable ist, dann gehen wir davon aus, dass $\alpha$
einen Typ bezeichnet und keinen Typkonstruktor, d.h. $\alpha :: \type$.
In dem Typausdruck `m [$\tau$]`{.haskell} ist die Verwendung von `m` als
Typkonstruktor also nicht erlaubt.

Für diese Einschränkung wurde sich entschieden, da wir sonst zu jeder
Typvariable die Sorte bestimmen müssten (*kind inference*), da in Coq die Sorte
explizit angegeben wird, in Haskell diese Information jedoch nicht vorliegt.
Wenn $\alpha$ z.B. die Sorte $\type$ hat, dann muss sie in Coq als
`[$\alpha$] : Type`{.coq} eingeführt werden, aber wenn $\alpha$ die Sorte
$\type \to \type$ hat, dann muss sie als mit `[$\alpha$] : Type -> Type`{.coq}
eingeführt werden.

## Typkonstruktoranwendungen

Aufgrund der Einschränkung für die Sorten von Typvariablen gibt es grundsätzlich
keine Möglichkeit Typkonstruktoren mithilfe von Datentypdeklarationen zu
erzeugen, deren Argumente selber Typkonstruktoren sind. Es gibt also keine
*higher-order type operators*, bzw. alle $n$-stelligen Typkonstruktoren $\tau$
haben die Sorte:

$$
  \tau ::\underbrace{\type \to \ldots \to \type}_{n\text{-Mal}} \to \type
$$

Entsprechend hat die Anwendung eines Typkonstruktors immer die Form:

```haskell
[$\tau_1$] [$\tau_2$]
```

wobei $\tau_1 :: \type \to \kappa$ ein Typkonstruktor ist und $\tau_2 :: \type$
ein Typ.
