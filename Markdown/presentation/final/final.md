---
title: |
  Übersetzung
  <small>von Haskell nach Coq</small>
author: Justin Andresen
date: ??.09.2019
lang: de-DE
pandoc-minted:
  default-attributes:
    escapeinside: "@@"
    mathescape: "true"
  default-block-attributes:
    tabsize: "2"
    breaklines: "true"

# Beamer options:
# theme: CAU2013
# themeoptions: tf

# Reveal.js options:
theme: serif
history: true
include-before: |
  <style>
  .reveal, .reveal h1, .reveal h2 {
    font-family: sans-serif !important;
  }
  .reveal pre code {
    overflow: hidden;
  }
  .reveal blockquote {
    font: 60% monospace;
  }
  .reveal .small-heading h1 {
    font-size: 2.11em !important;
  }
  .reveal .small-heading h2 {
    font-size: 1.55em !important;
  }
  .reveal .hidden {
    visibility: hidden;
  }
  .reveal .fix-height {
    height: 90%;
  }
  .reveal .fix-height-sm {
    height: 75%;
  }
  .reveal .fix-ul-width ul {
    width: 100%;
  }
  </style>
---

# Motivation

## Was ist Coq? {.fix-height data-transition="slide-in none-out"}

- Funktionalle Spezifikationssprache Gallina

  ::: fragment
  ```coq
  Inductive list (X : Type) : Type
    := nil  : list X
     | cons : X -> list X -> list X.

  Definition null {X : Type} (xs : list X) : bool
    := match xs with
       | nil        => true
       | cons x xs' => false
       end.
  ```
  :::

## Was ist Coq? {.fix-height data-transition="fade-in none-out"}

- Funktionalle Spezifikationssprache Gallina

- Beweisassistenzsystem

  ::: fragment
  ```coq
  Theorem null_length:
    forall (X : Type) (xs : list X),
    null xs = true -> length xs = 0.
  Proof. (* ... *) Qed.
  ```
  :::

## Was ist Coq? {.fix-height data-transition="fade-in slide-out"}

- Funktionalle Spezifikationssprache Gallina

- Beweisassistenzsystem

- Extraktion der verifizierten Programme  
  (z.B. Coq → Haskell)

::: {.fragment}
- **Ziel:** Verifikation bestehender Programme  
  (d.h. Haskell → Coq)
:::

## Unterschiede zu Haskell {.fix-ul-width .fix-height data-transition="slide-in none-out"}

::: fragment
- In Coq ist die **Deklarationsreihenfolge** wichtig.

  ```coq
  Definition null {X : Type} (xs : list X) : bool
    := match xs with               ^^^^^^
       | nil        => true
       | cons x xs' => false
       end.

  Inductive list (X : Type) : Type
    := nil  : list X
     | cons : X -> list X -> list X.
  ```
:::

## Unterschiede zu Haskell {.fix-ul-width .fix-height data-transition="fade-in none-out"}

- In Coq ist die **Deklarationsreihenfolge** wichtig.

- In Coq muss Pattern-Matching **vollständig** sein.

  ::: fragment
  ```coq
  Definition head {X : Type} (xs : list X) : X
    := match xs with
       | cons x xs' => x
       end.
  ```
  :::

## Unterschiede zu Haskell {.fix-ul-width .fix-height data-transition="fade-in none-out"}

- In Coq ist die **Deklarationsreihenfolge** wichtig.

- In Coq muss Pattern-Matching **vollständig** sein.

  ```coq
  Definition head {X : Type} (xs : list X) : X
    := match xs with
       | nil        => (* ??? *)
       | cons x xs' => x
       end.
  ```

## Unterschiede zu Haskell {.fix-ul-width .fix-height data-transition="fade-in none-out"}

- In Coq ist die **Deklarationsreihenfolge** wichtig.

- In Coq müssen alle Funktionen **total** sein.

  ```haskell
  undefined :: a
  ```

  ::: fragment
  ```coq
  Theorem contradiction: False.
  Proof. apply undefined. Qed.
  ```
  :::

## Unterschiede zu Haskell {.fix-ul-width .fix-height data-transition="fade-in slide-out"}

- In Coq ist die **Deklarationsreihenfolge** wichtig.

- In Coq müssen alle Funktionen **total** sein.

- In Coq müssen alle Funktionen  **terminieren**.

  ::: fragment
  ```haskell
  loop :: a
  loop = loop
  ```
  :::

# Existierende Ansätze

<!--
  - Welche Implementierungen existieren bereits?
  - Was sind die Probleme dieser existierenden Implementierungen?
  - Was soll meine Implementierung anders/besser machen?
-->

## [hs-to-coq](https://github.com/antalsz/hs-to-coq) {.fragile .fix-ul-width}

- Entwickelt an der Universität von Pennsylvania

::: incremental

- Übersetzt **totale** Haskell Programme zu Coq

- Zusätzliche Axiome für partielle Funktionen

    ```coq
    Axiom patternFailure : forall {a}, a .
    ```

:::

## [haskellToCoqCompiler](https://github.com/beje8442/haskellToCoqCompiler) {.fragile}

- Bachlorarbeit aus Flensburg

- Monadische Transformation nach [Abel et al.](http://www2.tcs.ifi.lmu.de/~abel/haskell05.pdf)

## Monadische Transformation {.fragile .small-heading .fix-height-sm data-transition="slide-in none-out"}

```coq
Definition head {X : Type} (xs : list X) : X
  := match xs with
     | nil        => (* ??? *)
     | cons x xs' => x
     end.
```

::: fragment
```coq
Definition head {X : Type} (xs : list X) : option X
  := match xs with
     | nil        => None
     | cons x xs' => Some x
     end.
```
:::

::: fragment
```coq
head (head xss)
```
:::

## Monadische Transformation {.fragile .small-heading .fix-height-sm data-transition="fade-in none-out"}

::: hidden
```coq
Inductive list (X : Type) : Type
  := nil  : list X
   | cons : option X -> option (list X) -> list X.
```
:::

```coq
Definition head {X : Type} (xs : option (list X)) : option X
  := xs >>= fun xs_0 => (
       match xs with
       | nil        => None
       | cons x xs' => Some x
       end).
```

## Monadische Transformation {.fragile .small-heading .fix-height-sm data-transition="fade-in slide-out"}

```coq
Inductive list (X : Type) : Type
  := nil  : list X
   | cons : option X -> option (list X) -> list X.
```

```coq
Definition head {X : Type} (xs : option (list X)) : option X
  := xs >>= fun xs_0 => (
       match xs with
       | nil        => None
       | cons x xs' => x
       end).
```


## [haskellToCoqCompiler](https://github.com/beje8442/haskellToCoqCompiler) {.fragile .fix-ul-width}

- Bachlorarbeit aus Flensburg
- Monadische Transformation nach [Abel et al.](http://www2.tcs.ifi.lmu.de/~abel/haskell05.pdf)

::: fragment
- Prototypische Umsetzung
:::

::: fragment
- Nur `Maybe`{.haskell} und `Identity`{.haskell} Monade
:::

# Umsetzung

## Zielsetzung {.fix-ul-width}

- Erweitung auf Effekt generischen Ansatz

## Effekt generischer Ansatz {.fragile}

```coq
Inductive List (M : Type -> Type) (X : Type) : Type
  := nil  : List M X
   | cons : M X -> M (List M X) -> List M X.
```

::: fragment
> Error: Non strictly positive occurrence of "List" in
> "M X -> M (List M X) -> List M X".
:::

## Freie Monade {.fragile}

```haskell
data Free f a = Pure a | Impure (f (Free f a))
```

::: fragment
```coq
Inductive List (@$Shape$@ : Type) (@$Pos$@ : @$Shape$@ -> Type) (X : Type)
  := nil  : List @$Shape$@ @$Pos$@ X
   | cons : Free @$Shape$@ @$Pos$@ X
            -> Free @$Shape$@ @$Pos$@ (List @$Shape$@ @$Pos$@ X)
            -> List @$Shape$@ @$Pos$@ X.
```
:::

## Zielsetzung {.fix-ul-width}

- Erweitung auf Effekt generischen Ansatz

::: fragment
- Zunächst nur kleiner Sprachumfang
:::

## Annahmen {.fragile}

- Zu jeder Funktion wird die **Typsignatur** explizit angegeben.

::: incremental

- Vordefinierte Typen: `Integer`{.haskell}, `Bool`{.haskell}, `[a]`{.haskell},
  `()`{.haskell} und `(a, b)`{.haskell}
- Benutzerdefinierte Typen mit `data`{.haskell} und `type`{.haskell},
  aber nicht `newtype`{.haskell}

:::

## Annahmen {.fragile .fix-ul-width}

- Jede Funktion wird durch **genau eine Regel** definiert.

  ```haskell
  @$f$@ :: @$\tau_1$@ -> @$\ldots$@ -> @$\tau_n$@ -> @$\tau$@
  @$f$@ @$x_1$@ @$\ldots$@ @$x_n$@ = @$e$@
  ```

::: incremental
- Keine lokalen Deklarationen mit `where`{.haskell}

- Explizites und vollständiges Pattern-Matching

  ```haskell
  case xs of
    []      -> undefined
    x : xs' -> x
  ```

- Keine verschachtelten Pattern
:::

## Annahmen {.fragile}

- Keine `let`{.haskell} oder `do`{.haskell} Ausdrücke

- Keine Typklassen

- Keine `import`{.haskell}s

<!-- ... -->

# Fragen?

<!-- Backup slides: -->

# Beispiele für freie Monaden {.small-heading}

## `Identity`{.haskell} $\approx$ `Free Zero`{.coq}  {.small-heading .fragile}

```haskell
data Free f a = Pure a | Impure (f (Free f a))

data Zero a

data Identity a = Identity a
```

## `Maybe`{.haskell} $\approx$ `Free One`{.coq} {.small-heading .fragile}

```haskell
data Free f a = Pure a | Impure (f (Free f a))

type One a = ()

data Maybe a = Just a | Nothing
```
