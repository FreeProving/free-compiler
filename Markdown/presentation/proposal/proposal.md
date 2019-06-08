---
title: |
  <small>Übersetzung von Haskell nach Coq</small>
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

# Annahmen {.fragile}

<!--
  - Welche Haskell Features sollen unterstützt werden?
-->

- Zu jeder Funktion wird die **Typsignatur** explizit angegeben.

- Vordefinierte Typen: `Int`{.haskell}, `Bool`{.haskell}, `[a]`{.haskell},
  `()`{.haskell} und `(a, b)`{.haskell}

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

- Keine `let`{.haskell} oder `do`{.haskell} Ausdrücke

- Keine Typklassen

- Keine `import`{.haskell}s
