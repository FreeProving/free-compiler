---
title: HaskellToCoq - Fehler und Probleme
author: Justin Andresen
---

## Fehler bei der Übersetzung
### Funktionen
#### Funktionen als Rückgabewert

Der Compiler kann nicht mit Funktionen umgehen, die selber Funktionen
zurück geben:

```haskell
pair :: a -> b -> (a, b)
pair x y = (x, y)

pair' :: a -> b -> (a, b)
pair' x = pair x
```

```coq
Definition pair' (a b : Type) (ox : option a) : option (Pair a b) := (* ... *)
                                              ^^^^^^^^^^^^^^^^^^^
```

#### Funktionen als Argument

Wie im Fazit erwähnt wird, werden Funktionen, die als Parameter übergeben
werden nicht korrekt geliftet.

```haskell
apply :: (a -> b) -> a -> b
apply f x = f x
```

```coq
Definition apply (a b : Type) (f : (option a -> option b)) (ox : option a)
  : option b := (* ... *)      ^^^^^^^^^^^^^^^^^^^^^^^^^^
```

#### Funktionen in Typsynonymen

Man kann um das oben genannte Problem mit Hilfe von Typsynonymen herum arbeiten,
dann werden aber die Argumente des Typkonstruktors `->` in `Fun` nicht korrekt
geliftet.

```haskell
type Fun a b = a -> b

apply :: (Fun a b) -> a -> b
apply f x = f x
```

```coq
Definition Fun (a : Type) (b : Type) :=
  a -> b.

Definition apply (a b : Type) (of : (option (Fun a b))) (ox : option a)
  : option b := (* ... *)     ^^^^^^^^^^^^^^^^^^^^^^^^^
```

#### Lazy Evaluation

Anders als in der Arbeit behauptet wird, bildet die monadische
Transformation die Lazy Auswertung von Haskell nicht korrekt in Coq ab.

```haskell
constTrue :: a -> Bool
constTrue x = True
```

```haskell
GHCi> constTrue (head [])
True
```

```coq
Definition constTrue (a : Type) (ox : option a) : option bool :=
  ox >>= (fun (x : a) => o_return true).

Compute (constTrue (head (o_return (@Nil nat)))).
 (* ==> None *)
```

Um diesen Fehler zu beheben, müsste `ox` nur dann "ausgepackt" werden,
wenn `x` auch tatsächlich in dem Term verwendet wird.

### *Pattern-Bindings*

#### Liften in Pattern-Bindings

In "Pattern-Bindings" werden Ausdrücke unnötiger Weise geliftet:

```haskell
id :: Int -> Int
id x = x

zero :: Int
zero = id 0
```

```coq
Definition id (ox : option nat) : option nat :=
  ox >>= (fun (x : nat) => o_return x).

Definition zero : option nat :=
  o_return (id (o_return 0)).
  ^^^^^^^^
```

Wäre `zero` eine Funktionsdefinition, dann würde das Ergebnis von `id 0`
korrekter Weise nicht geliftet.

#### Rekursion in Pattern-Bindings

In "Pattern-Bindings" kann man Rekursion verwenden, ohne dass es zu einem
Compile-Zeit-Fehler kommt. Der Resultierende Code Kompiliert dann nicht in
Coq, obwohl dies eine Zielsetzung war.

```haskell
loop :: a
loop = loop
```

```coq
Definition loop (a : Type) : option a :=
  o_return loop.
```

### Pattern-Matching
#### Liften von Variablenpattern

Per Pattern-Matching gebundene Variablen ("catch all" Fälle) werden nicht
korrekt geliftet:

```haskell
id :: a -> a
id x =
  case x of
    y -> y
```

```coq
Definition id (a : Type) (ox : option a) : option a :=
  ox >>= (fun (x : a) => match x with | y => y | _ => None end).
                                        ^^^^^^
```

#### Redundanter `_` Fall

Außerdem wird ein redundanter Fall (`_`) hinzugefügt, wenn es bereits einen
"catch all" Fall gibt:

```coq
Definition id (a : Type) (ox : option a) : option a :=
  ox >>= (fun (x : a) => match x with | y => y | _ => None end).
                                                 ^^^^^^^^^
```

### Typsignaturen
#### Klammern

Wenn ein Typ Klammern enthält, wird er zwar geliftet, aber dies wird nicht
rückgängig gemacht, wenn der Typ von dem Argument der Lambda-Funktion
beim `>>=` bestimmt wird.

```haskell
id :: (a) -> a
id x = x
```

```coq
Definition id (a : Type) (ox : (option a)) : option a :=
  ox >>= (fun (x : (option a)) => o_return x).
                   ^^^^^^^^^^
```

#### `->` rechts Klammern

Wenn man `->` klammert, werden Argumente nicht erkannt.

```haskell
plus :: Int -> (Int -> Int)
plus a b = a + b
```

```coq
Definition plus (oa : option nat) : (option nat -> option nat) :=
  oa >>= (fun (a : nat) => o_return (a + b)).
```

#### Großgeschriebene Typvariablen

Für einen nicht definierten Typen `A` wird in der Signatur `foo :: A -> A`
angenommen, dass `A` eine Typvariable wäre, obwohl diese in Haskell
kleingeschrieben werden müssen. `foo :: A -> A` ist daher ein
Compile-Zeit-Fehler, aber in HaskellToCoq wird `foo (A : Type) ...` erzeugt.

### Module

Wenn der Modulkopf weggelassen wird, dann scheint sich HaskellToCoq die
definierten Datentypen nicht zu merken (nimmt an, dass es sich um
Typvariablen handelt).

```haskell
data Maybe a = Nothing | Just a

isNothing :: Maybe a -> Bool
isNothing m = case m of
  Nothing -> True
  _       -> False
```

```coq
Definition isNothing (Maybe a : Type) (om : option (Maybe a)) : option bool
  := (* ... *)        ^^^^^^^^^^^^^^
```

## Weitere Probleme bei der Übersetzung
### Namenskonflikte
#### Namenskonflikte bei Hilfsfunktionen (Rekursion)

Bei Hilfsfunktionen (Suffix `'`) wurde bereits in der Arbeit festgestellt,
dass es zu Namenskonflikten kommen kann.

```haskell
append :: [a] -> [a] -> [a]  -- Rekursive Definition
append' :: [a] -> [a] -> [a] -- Konflikt mit generierter Hilfsfunktion
```

#### Namenskonflikte mit Parametern

Auch bei der Umbenennung von Parametern (Prefix `o` bzw. `i`) kann es zu
Namenskonflikten kommen.

- Durch das Anhängen des Suffixes kann der resultierende Bezeichner mit
  existierenden Parametern oder Funktionen kollidieren.
- Durch das Anhängen des Suffixes kann ein Schlüsselwort von Coq
  resultieren (`if` oder `in`).

#### Namenskonflikte mit Typvariablen

In Haskell sind die Namensräume für Typen und Funktionen/Variablen separat,
aber in Coq nicht. Eine Typvariable `a` würde also mit einem gleichnamigen
Parameter kollidieren.

#### Namenskonflikte bei Umbenennung von Konstruktoren

Dasselbe Problem besteht für Datentypen mit gleichnamigen Konstruktoren und
wird in HaskellToCoq durch das Suffix `_` gelöst. Durch diese Umbenennung kann
es wieder zu Namenskonflikten kommen.

### Limitierungen bei eingebauten Datentypen

### Listen

Es können nur leere und einelementige Listen (`[]` und `[x]`) übersetzt werden,
ohne `:` explizit zu verwenden.

Eine `Notation` für Listen wie in *Software Foundations* eigeführt wurde, wäre
hilfreich, um die generierten Listen lesbar zu machen.

### Tuple

Es werden nur Paare und $0$-Tuple unterstützt.

#### Ganzzahlen
##### Ganzzahlen eignen sich nicht für Beweise

`Int` wird als `nat` übersetzt, aber im Gegensatz zu Natürlichen Zahlen können
Ganzzahlen auch negativ sein. Haskell Code, der arithmetische Ausdrücke
verwendet, verhält sich daher grundlegend anders als der generierte Coq Code.
Beweist man eine Eigenschaft des Codes in Coq kann man daher keine Rückschlüsse
auf das Haskell Programm ziehen.

```haskell
zero :: Int -> Int
zero n = 0 - n + n

> zero 1
0
```

```coq
Compute zero (Some 1).
  (* ==> = Some 1
         : option nat *)
```
- Es kann zu Namenskonflikten kommen.


    + Es kann zu Konflikten zwischen Parametern und Typvariablen kommen.


###### Ganzzahlen eigenen sich nicht für Rekursion

In Rekursiven Funktionen benötigt man ein `case`, kann aber kein Pattern
Matching auf Zahlen machen.

```haskell
-- Kompiliert nicht, da kein `case` verwendet wird.
fac :: Int -> Int
fac n = if n == 0 then 1 else fac (n - 1)

-- Kompiliert nicht, da Pattern Matching auf Zahlen nicht implementiert wurde.
fac' :: Int -> Int
fac' n =
  case n of
    0  -> 1
    n' -> fac' (n' - 1)
```

Selbst wenn `fac'` kompilieren würde, könnte Coq wahrscheinlich in diesem Fall
das *decreasing Argument* nicht bestimmen.

### etc.
#### Zielenumbrüche

Der generierte Code enthält als Zeilenumbrüche `"\n \r"` (LF space CR).
Es wird also weder die Unix (LF), Mac (CR) noch Windows (CRLF) Konvention
gefolgt.

#### LoadPath

Das `Add LoadPath "../ImportedFiles".` Kommando funktioniert nicht richtig
in CoqIDE, da das *Working Directory* standardmäßig  das Home Verzeichnis
des Nutzers ist.

Man muss also entweder einen absoluten Pfad angeben oder CoqIDE über die
Konsole im `CoqFiles/OutputFiles` Ordner starten.
