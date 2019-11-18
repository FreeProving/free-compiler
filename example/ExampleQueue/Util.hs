module ExampleQueue.Util where

null :: [a] -> Bool
null [] = True
null _  = False

not :: Bool -> Bool
not True  = False
not False = True

append :: [a] -> [a] -> [a]
append []        ys = ys
append (x : xs') ys = x : (append xs' ys)

reverse :: [a] -> [a]
reverse []        = []
reverse (x : xs') = reverse xs' `append` [x]
