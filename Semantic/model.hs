module Semantic.Model (module AST
                      ,module Unique
                      ,module UniqueFM
                      ,Name(..)
                      ,Object(..)
                      ,Scoped(..)
                      ,CompilerError(..)
                      ,ScopedEnv(..)
                      ,TypecheckEnv(..)
                      ,ClassName
                      ,ClassMap
                      ,MethodMap
                      ,AttrMap
                      ,ObjectMap
                      ,Type) where

import AST
import Unique
import UniqueFM
import Control.Monad.Error.Class

type Type = String
type ClassName = String
type ClassMap a = UniqueFM (Class a)
type MethodMap a = UniqueFM (Method a, ClassName)
type AttrMap a = UniqueFM (Attr a, ClassName)
type ObjectMap a = UniqueFM (Object a)

data Name = Name { nameLabel  :: String
                 , nameHash   :: String  
                 , nameUnique :: Unique } deriving Show

data Object a = Obj { objectName  :: String
                    , objectTyp   :: String 
                    , objectExpr  :: Maybe (Expr a)} deriving Show

data Scoped a = Scoped { scopedValue     :: a
                       , scopedObjects   :: UniqueFM (Object String) } deriving Show

data CompilerError = Runtime
                   | ClassDuplicate String
                   | UnknownClass String
                   | IllegalInheritance String
                   | InvalidFeatureType String String String
                   | DuplicateFormalDeclaration String
                   | DuplicateVarDeclaration String
                   | DuplicateAttrDeclaration String
                   | DuplicateMethodDeclaration String
                   | UnknownVariable String
                   | UnknownMethod String String
                   | InvalidIdDeclaration
                   | TypeError String
                   | CyclicInheritanceGraph String deriving Eq

data ScopedEnv = SPEnv { spCurrentClass :: Class String
                       , spClassMap     :: ClassMap String
                       , spMethodMap    :: MethodMap String
                       , spObjMap       :: ObjectMap String}

data TypecheckEnv = TCEnv { tcCurrentClass :: Class (Scoped String)
                          , tcClassMap :: ClassMap (Scoped String)
                          , tcMethodMap :: MethodMap String }

instance Show CompilerError where
  show (ClassDuplicate name) = "Class " ++ name ++ " already exists"
  show (UnknownClass name) = "Class " ++ name ++ " is undeclared"
  show (IllegalInheritance name) = "Illegal inheritance on class " ++ name
  show (InvalidFeatureType name cType eType) = "Invalid attribute/method type definition named " ++ name ++ ": " ++ cType ++ " should be " ++ eType
  show (DuplicateFormalDeclaration name) = "Formal parameter " ++ name ++ " is already declared"
  show (DuplicateVarDeclaration name) = "Variable " ++ name ++ " is already declared"
  show (DuplicateAttrDeclaration name) = "Attribute " ++ name ++ " is already declared"
  show (DuplicateMethodDeclaration name) = "Method " ++ name ++ " is already declared"
  show (UnknownVariable name) = "Variable " ++ name ++ " is unknown"
  show (UnknownMethod name cName) = "Method " ++ name ++ " is unknown on class " ++ cName
  show InvalidIdDeclaration = "You can't declare a variable/attribute/method \"self\""
  show (CyclicInheritanceGraph name) = "Cyclic inheritance on class " ++ name
  show (TypeError msg) = "Type error: " ++ msg

instance Error CompilerError where
  strMsg _ = Runtime 
