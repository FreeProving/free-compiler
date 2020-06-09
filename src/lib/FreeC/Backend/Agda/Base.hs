-- | This module contains the Agda identifiers of types, constructors and
--   functions defined in the Base library that accompanies the compiler.

module FreeC.Backend.Agda.Base
  ( -- * Library imports
    baseLibName
  , generatedLibName
  , imports
    -- * Free Monad
  , free
  , free'
  , freeArgs
  , pure
  , impure
  , shape
  , position
  , addTVars
    -- * reserved identifiers
  , reservedIdents
  )
where

-- We always import this module qualified, therefore clashing with the Prelude
-- isn't a problem.
import           Prelude                 hiding ( pure )

import qualified FreeC.Backend.Agda.Syntax     as Agda

-------------------------------------------------------------------------------
-- Library imports                                                           --
-------------------------------------------------------------------------------

-- | The name of the Agda Base library.
baseLibName :: Agda.Name
baseLibName = Agda.name "Base"

-- | The name of the Agda library where generated Agda files are placed.
generatedLibName :: Agda.Name
generatedLibName = Agda.name "Generated"

-- | Import declaration for the @Free@ module from the Base Agda library.
imports :: Agda.Declaration
imports = Agda.simpleImport $ Agda.qname [baseLibName] $ Agda.name "Free"

-------------------------------------------------------------------------------
-- Free Monad                                                                --
-------------------------------------------------------------------------------

-- | Identifier for the @Free@ monad.
free :: Agda.Name
free = Agda.name "Free"

-- | Lifts a type in the free monad.
free' :: Agda.Expr -> Agda.Expr
free' = Agda.app $ freeArgs $ Agda.qname' free

-- | Apply the @Shape@ and @Position@ argument to the given type constructor.
--
-- > c ↦ c @S @P
freeArgs :: Agda.QName -> Agda.Expr
freeArgs qname = foldl1
  Agda.app
  [ Agda.Ident qname
  , Agda.Ident (Agda.qname' shape)
  , Agda.Ident (Agda.qname' position)
  ]

-- | Identifier for the @Pure@ constructor of the @Free@ monad.
pureConName :: Agda.Name
pureConName = Agda.name "pure"

-- | Applies the @Pure@ constructor of the free monad to the given expression.
pure :: Agda.Expr -> Agda.Expr
pure = Agda.app $ Agda.Ident $ Agda.qname [Agda.name "Free"] pureConName

-- | Identifier for the @Impure@ constructor of the @Free@ monad.
impureConName :: Agda.Name
impureConName = Agda.name "impure"

-- | Applies the @Impure@ constructor of the free monad to the given expression.
impure :: Agda.Expr -> Agda.Expr
impure = Agda.app $ Agda.Ident $ Agda.qname [Agda.name "Free"] impureConName

-- | Reserved name for the @Shape@ type variable.
shape :: Agda.Name
shape = Agda.name "S"

-- | Reserved name for the @Position@ type variable.
position :: Agda.Name
position = Agda.name "P"

-- | Adds the @Shape@ and @Position@ type variables to a list of variables.
addTVars :: [Agda.Name] -> [Agda.Name]
addTVars ts = shape : position : ts

-------------------------------------------------------------------------------
-- Reserved identifiers                                                      --
-------------------------------------------------------------------------------

-- | All Agda identifiers that are reserved for the Base library.
--
--   This does only include identifiers without corresponding Haskell name.
reservedIdents :: [Agda.Name]
reservedIdents = [free, pureConName, impureConName, shape, position]
