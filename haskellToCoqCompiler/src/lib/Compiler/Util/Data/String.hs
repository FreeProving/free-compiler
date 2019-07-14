module Compiler.Util.Data.String where

import           Data.Char                      ( toUpper
                                                , toLower
                                                )

-- | Converts the first letter of the given string to uppercase.
capitalize :: String -> String
capitalize (c : cs) = toUpper c : cs
capitalize []       = []

-- | Converts the  the first letter of the given string to lowercase.
uncapitalize :: String -> String
uncapitalize (c : cs) = toLower c : cs
uncapitalize []       = []
