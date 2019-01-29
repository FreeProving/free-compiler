# Haskell To Coq Compiler

# Benötigte Software

  * Haskell Platform
  * Coq IDE 8.8.1

## Installation des Compilers
Zur Installation des Compilers sollte das Cabal build system verwendet werden, welches in der Haskell Platform enthalten ist.
Im Projektordner muss `cabal install -j` ausgeführt werden um die importierten Module zu installieren.

## Verwendung des Compilers
Zur Verwendung des Compilers muss `cabal repl` ausgeführt werden um alle Module zu komiplieren. Die zum Kompilieren benötigten Funktionen sind im Modul `Main`.
Um zu diesem Modul zu wechseln kann `:module Main` verwendet werden. Zum beenden der repl genügt der Befehl `:quit`.

Im Main Modul gibt es eine Reihe an Funktionen zum kompilieren von Haskell-Code:
  * `compileAndPrintFile`: Benötigt einen Dateipfad. Kompiliert das eingelesene Haskell-Modul und gibt das Ergebnis in der Konsole aus.
  * `compileAndSaveFile` : Benötigt einen Dateipfad. Kompiliert das eingelesene Haskell-Modul und speichert eine Coq-Datei im Ordner `CoqFiles/OutputFiles`.

Der Compiler hat auch einige Funktionen, die über Flags gesteuert werden können. Damit Flags in der repl angewendet werden, muss vorher der Aufruf `:set args` zusammen mit den gewünschten Flags ausgeführt werden.
Mögliche Flags sind:
  * `-o`: Zum Verwenden der option-Monade.
  * `-i`: Zum Verwenden der identity-Monade.
  * `-h`: Zum Kompilieren von rekursiven Funktionen mit einer Hilfsfunktion (HelperFunctions).
  * `-f`: Zum Kompilieren von Funktionen mit einem fuel-Argument (FueledFunctions).
Dabei können jeweils immer nur option-Monade oder identity-Monade aktiv sein. Und die Konvertierung ist nur mit HelperFunctions oder FueledFunctions möglich. Die Standartkonfiguration ist: option-Monade und FueledFunctions. 

## Fehlerbehandlung
Wenn eine andere Version von Coq verwendet wird kann das bei jedem Modul importierte Coq-Modul `Monad` nicht geladen werden. Um diesen Fehler zu beheben muss die Datei `CoqFiles/ImportedFiles/ImportModules.v` mit der genutzten Coq-Version neu kompiliert werden.   
