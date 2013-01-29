{-# LANGUAGE UnicodeSyntax #-}
module CodeGen where

import Control.Monad.Trans
import Semantic.Model

codegen ∷ MonadIO m ⇒ Program (Scoped (String, Type)) → m ()
codegen = error "todo"
