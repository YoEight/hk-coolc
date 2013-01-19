module Main (compile) where

import Parser
import Semantic

process = parser >>= typecheck

compile = execute process 
