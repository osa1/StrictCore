{-# LANGUAGE NoImplicitPrelude #-}

module Lib where

data Bool = True | False

not :: Bool -> Bool
not True  = False
not False = True

data E = E1 | E2

f :: Bool -> E
f x = case not x of True -> E1; False -> E2
