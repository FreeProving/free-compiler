---
title: |
  Übersetzung
  <small>von Haskell nach Coq</small>
author: Justin Andresen
date: 13.06.2019
lang: de-DE
# Beamer options:
# theme: CAU2013
# themeoptions: tf
pandoc-minted:
  default-attributes:
    escapeinside: "@@"
    mathescape: "true"
  default-block-attributes:
    tabsize: "2"
    breaklines: "true"
# Reveal.js options:
theme: serif
history: true
---

# Annahmen

<!--
  - Welche Haskell Features sollen unterstützt werden?
-->

## Annahmen {.fragile}

- Zu jeder Funktion wird die **Typsignatur** explizit angegeben.

> - Vordefinierte Typen: `Int`{.haskell}, `Bool`{.haskell}, `[a]`{.haskell},
>   `()`{.haskell} und `(a, b)`{.haskell}
> - Benutzerdefinierte Typen mit `data`{.haskell} und `type`{.haskell},
>   aber nicht `newtype`{.haskell}

## Annahmen {.fragile}

- Jede Funktion wird durch **genau eine Regel** definiert.

    ```haskell
    @$f$@ :: @$\tau_1$@ -> @$\ldots$@ -> @$\tau_n$@ -> @$\tau$@
    @$f$@ @$x_1$@ @$\ldots$@ @$x_n$@ = @$e$@
    ```
- Explizites und vollständiges Pattern-Matching

    ```haskell
    case xs of
      []      -> undefined
      x : xs' -> x
    ```

## Annahmen {.fragile}

- Keine `let`{.haskell} oder `do`{.haskell} Ausdrücke

- Keine Typklassen

- Keine `import`{.haskell}s

# Übersetzung

## Beispiel {.fragile}

```haskell
head :: [a] -> a
head x:_ = x
```

<div class="fragment">
```haskell
head :: [a] -> a
head xs = case xs of
  []    -> undefined
  x:xs' -> x
```
</div>

## Beispiel {.fragile}

```haskell
head :: [a] -> a
head xs = case xs of
  []    -> undefined
  x:xs' -> x
```

<div class="fragment">
```coq
Definition head {a : Type} (xs : List a) : a :=
  match xs with
  | nil        => (* ??? *)
  | cons x xs' => x
  end.
```
</div>

<div class="fragment">
```coq
Definition head {a : Type} (xs : List a) : option a :=
  match xs with
  | nil        => None
  | cons x xs' => Some x
  end.
```
</div>

## Beispiel {.fragile}

<div class="fragment">
```coq
Inductive List (a : Type) : Type :=
  | nil  : List a
  | cons : option a -> option (List a) -> List a.
```
</div>

```coq
Definition head {a : Type} (oxs : option (List a)) : option a :=
  oxs >>= fun(xs : List a) =>
    match xs with
    | nil          => None
    | cons ox oxs' => ox
    end.
```
