module Semantic where

import Prelude hiding (foldr, foldl)
import Data.Foldable
import Data.Traversable
import Parser
import qualified Data.IntMap as I

import Control.Monad

type Type   = String
type Parent = String
type ClassDecls = Table String
type InheritanceGraph = I.IntMap Int
type ClassSyms = [(String, ClassSym)]

data Graph k n

data InheritNode = InheritNode {inhKey :: Int
                               ,inhType :: Type
                               ,inhParent :: Maybe Int }

data AnoClass = AnoClass Class

data ClassSym = ClassSym {className :: String
                         ,classParent :: Maybe String
                         ,classVars :: [(String, String)]
                         ,classMethods :: [(String, MethodSym)]} deriving Show

data MethodSym = MethodSym {methodName :: String
                           ,methodType :: String
                           ,methodParams :: [(String, String)]} deriving Show

data Table a = Table {tableSeed :: Int
                     ,tableMap  :: I.IntMap a}

instance Show a => Show (Table a) where
  show (Table _ as) = show as

addSym :: a -> Table a -> Table a
addSym a (Table seed as) = let table' = I.insert seed a as in Table (succ seed) table'

lookupSym :: Int -> Table a -> Maybe a
lookupSym key (Table _ table) = I.lookup key table  

lookupByValue :: Eq v => v -> [(k, v)] -> Maybe (k, v)
lookupByValue _ [] = Nothing
lookupByValue v ((k, v'):xs)
  | v == v'   = Just (k, v)
  | otherwise = lookupByValue v xs


objectClassSym =
  let abort_meth    = ("abort", MethodSym "abord" "Object" [])
      typename_meth = ("type_name", MethodSym "type_name" "String" [])
      copy_meth     = ("copy", MethodSym "copy" "SELF_TYPE" [])
  in ("Object", ClassSym "Object" Nothing [] [abort_meth, typename_meth, copy_meth]) 

ioClassSym =
  let out_string_meth = ("out_string", MethodSym "out_string" "SELF_TYPE" [("x", "String")])
      out_int_meth    = ("out_int", MethodSym "out_int"  "SELF_TYPE" [("x", "Int")])
      in_string_meth  = ("in_string", MethodSym "in_string" "String" [])
      in_int_meth     = ("in_int", MethodSym "in_int" "Int" [])
  in ("IO", ClassSym "IO" (Just "Object") [] [out_string_meth, out_string_meth, in_string_meth, in_int_meth])

intClassSym = ("Int", ClassSym "Int" (Just "Object") [] [])

stringClassSym =
  let length_meth = ("length", MethodSym "length" "Int" [])
      concat_meth = ("concat", MethodSym "concat" "String" [])
      substr_meth = ("substr", MethodSym "substr" "String" [("i", "Int"), ("l", "Int")])
  in ("String", ClassSym "String" (Just "Object") [] [length_meth, concat_meth, substr_meth])

boolClassSym = ("Bool", ClassSym "Bool" (Just "Object") [] [])

initClassSyms = [objectClassSym
                ,ioClassSym
                ,intClassSym
                ,stringClassSym
                ,boolClassSym]

validateInhGraph :: ClassSyms -> ClassSyms -> Either String ClassSyms
validateInhGraph graph refs = let xs = graph ++ refs in fmap (const xs) (traverse (go xs . snd) graph)
  where
    go xs classSym = validateHierarchy classSym [] xs

validateHierarchy :: ClassSym -> [(String, ())] -> ClassSyms -> Either String ()
validateHierarchy ClassSym{className=name, classParent=(Just parent)} passed graph =
  case lookup name passed of
    Nothing -> maybe (Left $ "unknown class " ++ parent) (\sym -> validateHierarchy sym ((name, ()):passed) graph) (lookup parent graph)
    Just _  -> Left $ "Cyclic inheritance dependency on " ++ name
validateHierarchy _ _ _ = Right ()

--semantic :: Alex (InheritanceGraph, ClassDecls)
--semantic :: Alex [(String, ClassSym)]
semantic :: Alex (Either String ClassSyms)
semantic = liftM (validation . foldr go [] . getClasses) parser
  where
    getClasses (Program xs) = xs
    validation graph = validateInhGraph graph initClassSyms
    go (Class name parent features) acc = let (attrs, methods) = attr_methods features
                                          in (name, ClassSym name (Just parent) attrs methods) : acc

attr_methods :: [Feature] -> ([(String, String)], [(String, MethodSym)])
attr_methods features = foldr go ([], []) features
  where
    go (Attr name typ _) (attrs, methods)           = ((name, typ):attrs, methods)
    go (Method name formals typ _) (attrs, methods) = (attrs, (name, MethodSym name typ (methodFormalSym formals)):methods)

methodFormalSym :: [Formal] -> [(String, String)]
methodFormalSym = fmap (\(Formal name typ) -> (name, typ))

classes :: Program -> ClassDecls
classes (Program xs) = foldl go initClasseTable xs
  where
    go table (Class t p _) = addSym t table


inheritanceGraph :: Program -> ClassDecls -> InheritanceGraph
inheritanceGraph (Program xs) (Table _ decls) = go initInheritance xs
  where
    go inh_map [] = inh_map
    go inh_map ((Class t p _):xs) = let (Just (type_index, _))  = lookupByValue t (I.assocs decls)
                                        (Just (parent_index,_)) = lookupByValue p (I.assocs decls)
                                        inh_map' = I.insert type_index parent_index inh_map
                                    in go inh_map' xs

rowGraph :: (InheritanceGraph, ClassDecls) -> String
rowGraph (graph, r@(Table _ table)) = foldl go "" (I.keys table)
  where
    go acc classIndex = acc ++ "\n"  ++ (classGraph classIndex graph r)

classGraph :: Int -> InheritanceGraph -> ClassDecls -> String
classGraph 0 _ _ = "Object"
classGraph classIndex graph table = let parent_index = graph I.! classIndex
                                        (Just label) = lookupSym classIndex table
                                    in label ++ " => " ++ (classGraph parent_index graph table)