{-# LANGUAGE UnicodeSyntax #-}
module Main ({-compile-}) where

import Emitter
import Parser
import Semantic

import Control.Monad

import Data.Foldable
import Text.PrettyPrint

process ∷ Alex [(String, Doc)]
process = parser >>= liftM programEmitter . typecheck

compile = execute process >=> traverse_ go
  where
    go (name, doc) = writeFile ("/Users/yoeight/dev/haskell/" ++ name ++ ".java") (render doc)

