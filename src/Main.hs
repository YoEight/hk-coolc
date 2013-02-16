{-# LANGUAGE UnicodeSyntax #-}
module Main where

import Compiler.Emitter
import Compiler.Parser
import Compiler.Semantic

import Control.Monad

import Data.Foldable
import Text.PrettyPrint

main = print "Hello World"

process ∷ Alex [(String, Doc)]
process = parser >>= liftM programEmitter . typecheck

compile = execute process >=> traverse_ go
  where
    go (name, doc) = writeFile ("/Users/yoeight/dev/haskell/" ++ name ++ ".java") (render doc)
