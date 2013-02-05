{-# LANGUAGE UnicodeSyntax #-}
module Emitter where

import AST

import Codegen.Model
import Control.Arrow       hiding ((<+>))
import Control.Monad.State

import Data.Foldable
import Data.List
import Data.Maybe
import Data.Traversable

import Semantic.Model
import Text.PrettyPrint

programEmitter ∷ Program (Scoped (String, Type)) → [(String, Doc)]
programEmitter = fmap (className &&& (pretty . classEmitter)) . programClasses

classEmitter ∷ Class (Scoped (String, Type)) → JDecl
classEmitter (Class name parent attrs meths) =
  let mbrs = fmap attrEmitter attrs
      mtds = fmap methEmitter meths
  in JClass [JPublic] name (Just parent) (mbrs, mtds)

attrEmitter ∷ Attr (Scoped (String, Type)) → JDecl
attrEmitter (Attr name typ expr) =
  let expr' = fmap exprJExpr  expr
  in JMember [JPublic] typ name expr'

methEmitter ∷ Method (Scoped (String, Type)) → JDecl
methEmitter (Method name typ formals expr) =
  let formals' = fmap (formalName &&& formalType) formals
      expr' = exprJStmt expr
  in JMethod [JPublic] typ name formals' expr'

exprJExpr ∷ Expr (Scoped (String, Type)) → JExpr
exprJExpr (Comp expr) = exprJExpr expr
exprJExpr (Dispatch name mcast target params) =
  let dispatch = JDispatch (exprJExpr target) name (fmap exprJExpr params)
  in case mcast of
    Nothing  -> dispatch
    Just typ -> JCast typ dispatch
exprJExpr (Divide l r) = JBin (exprJExpr l) "/" (exprJExpr r)
exprJExpr (Eq l r) = JBin (exprJExpr l) "==" (exprJExpr r)
exprJExpr (Leq l r) = JBin (exprJExpr l) "<=" (exprJExpr r)
exprJExpr (Lt l r) = JBin (exprJExpr l) "<" (exprJExpr r)
exprJExpr (Gt l r) = JBin (exprJExpr l) ">" (exprJExpr r)
exprJExpr (Geq l r) = JBin (exprJExpr l) ">=" (exprJExpr r)
exprJExpr (Mul l r) = JBin (exprJExpr l) "*" (exprJExpr r)
exprJExpr (Plus l r) = JBin (exprJExpr l) "+" (exprJExpr r)
exprJExpr (Sub l r) = JBin (exprJExpr l) "-" (exprJExpr r)
exprJExpr (IntConst i) = JAtom (show i)
exprJExpr (New typ) = JNew typ
exprJExpr (Isvoid expr) = JInvoke (JAtom "isvoid") [(exprJExpr expr)]
exprJExpr (Object (Scoped (name, _) _)) = JAtom name
exprJExpr (StaticDispatch (Scoped (name, _) _) params) = JInvoke (JAtom name) (fmap exprJExpr params)
exprJExpr (StringConst s) = JAtom ("\"" ++ s ++ "\"")
exprJExpr (BoolConst b)
  | b          = JAtom "true"
  | otherwise  = JAtom "false"
exprJExpr (Not expr) = JUnop "!" (exprJExpr expr)
exprJExpr e = error ("not implemented JExpr for " ++ (show e))

exprJStmt ∷ Expr (Scoped (String, Type)) → JStmt
exprJStmt (Assign (Scoped (name, _) _) expr) = JAssign (JAtom name) (exprJExpr expr)
exprJStmt (Block exprs) = JBlock (fmap exprJStmt exprs)
exprJStmt (Cond pred texpr eexpr) =
  let if_ = JCond "if" (exprJExpr pred) [exprJStmt texpr]
  in JBlock $ maybe [if_] (\x -> [if_, JBlockX "else" [exprJStmt x]]) eexpr
exprJStmt (Loop pred expr) = JCond "while" (exprJExpr pred) [exprJStmt expr]
exprJStmt e = JEx (exprJExpr e)

class Pretty a where
  pretty ∷ a → Doc

instance Pretty JExpr where
  pretty (JAtom a) = text a
  pretty (JNew typ) = text "new" <+> text typ
  pretty (JDispatch e t p) =
    let p' = foldMap id (fmap pretty p)
    in braces (pretty e) <> text "." <> text t <> braces p'
  pretty (JCast typ e) = braces (text typ) <> braces (pretty e)
  pretty (JUnop op e) = text op <> braces (pretty e)
  pretty (JBin l op r) = (pretty l) <+> text op <+> (pretty r)
  pretty (JInvoke e p) =
    let p' = foldMap id (fmap pretty p)
    in (pretty e) <> braces p'

instance Pretty JAttr where
  pretty JFinal = text "final"
  pretty JPrivate = text "private"
  pretty JPublic = text "public"
  pretty JProtected = text "protected"
  pretty JStatic = text "static"

instance Pretty JDecl where
  pretty (JClass a n p (m, mt)) =
    let m'  = fmap (nest 4 . pretty) m
        mt' = fmap (nest 4 . pretty) mt
        p'  = foldMap ((text "extends" <+>) . text) p
        cls = prettyAttrs a <+>
              text n <+>
              p' <+>
              lbrace
        imp = text "import" <+> text "cool.lang.*" <> semi
    in vcat (imp:newline:cls:(m' ++ (newline:mt') ++ [rbrace]))
  pretty (JMethod a t n f s) =
    let s'  = nest 4 (pretty s)
        mth = prettyAttrs a <+>
              text t <+>
              text n <>
              parens (prettyFormals f) <+>
              lbrace
    in vcat [mth, s', rbrace]
  pretty (JConstr a n f s) =
    let s'  = nest 4 (pretty s)
        cst = prettyAttrs a <+>
              text n <>
              parens (prettyFormals f) <+>
              lbrace
    in vcat [cst, newline, s', newline, rbrace]
  pretty (JMember a t n e) =
    let e' = foldMap ((equals <+>) . pretty) e
    in prettyAttrs a <+>
       text t <+>
       text n <+>
       e' <>
       semi

instance Pretty JStmt where
  pretty JEmpty = empty
  pretty (JBlock xs) = vcat (lbrace:((fmap (nest 4 . pretty) xs) ++ [rbrace]))
  pretty (JReturn e) = text "return" <+> (pretty e) <> semi
  pretty (JEx e) = (pretty e) <> semi
  pretty (JAssign l r) = (pretty l) <+> equals <+> (pretty r) <> semi
  pretty (JLocal d) = pretty d
  pretty (JCond n e s) = text n <> braces (pretty e) <+> pretty (JBlock s)
  pretty (JBlockX n s) = text n <+> pretty (JBlock s)

prettyAttrs ∷ [JAttr] → Doc
prettyAttrs = foldMap id . punctuate space . fmap pretty

prettyFormals ∷ [JFormal] → Doc
prettyFormals = foldMap id . punctuate (comma <> space) . fmap go
  where
    go (n, typ) = text typ <+> text n

newline = nest 4 space
