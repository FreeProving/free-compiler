module DemoErrorMessages where

null :: [a] -> Bool
null []        = True
null (x : xs') = False
