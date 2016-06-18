{-# LANGUAGE NoImplicitPrelude #-}

module Lib where

import Prelude (Int, (+))

data LList a = LCons a (LList a) | LNil

lsingleton :: a -> LList a
lsingleton a = LCons a LNil

lrev :: LList a -> LList a
lrev LNil         = LNil
lrev (LCons x xs) = lrev xs `lappend` lsingleton x

lappend :: LList a -> LList a -> LList a
lappend LNil         l = l
lappend (LCons x xs) l = LCons x (lappend xs l)

llength :: LList a -> Int
llength LNil = 0
llength (LCons _ l) = 1 + llength l

-- Strict variant

data SList a = SCons !a !(SList a) | SNil

ssingleton :: a -> SList a
ssingleton a = SCons a SNil

srev :: SList a -> SList a
srev SNil         = SNil
srev (SCons x xs) = srev xs `sappend` ssingleton x

sappend :: SList a -> SList a -> SList a
sappend SNil         l = l
sappend (SCons x xs) l = SCons x (sappend xs l)

slength :: SList a -> Int
slength SNil = 0
slength (SCons _ l) = 1 + slength l
