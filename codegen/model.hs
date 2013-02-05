{-# LANGUAGE UnicodeSyntax #-}
module Codegen.Model where

data JExpr = JAtom String
           | JNew String
           | JDispatch JExpr String [JExpr]
           | JCast String JExpr
           | JUnop String JExpr
           | JBin JExpr String JExpr
           | JInvoke JExpr [JExpr]

data JAttr = JFinal
           | JPrivate
           | JPublic
           | JProtected
           | JStatic

type JAttrs = [JAttr]
type JFormal = (String, JType)
type JType = String

data JDecl = JClass JAttrs String (Maybe String) ([JDecl], [JDecl])
           | JMethod JAttrs JType String [JFormal] JStmt
           | JConstr JAttrs String [JFormal] JStmt
           | JMember JAttrs JType String (Maybe JExpr)

data JStmt = JEmpty
           | JBlock [JStmt]
           | JReturn JExpr
           | JEx JExpr
           | JAssign JExpr JExpr
           | JLocal JDecl
           | JCond String JExpr [JStmt]
           | JBlockX String [JStmt]
