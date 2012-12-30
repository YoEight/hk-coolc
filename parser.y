{
  module Parser (parser
                ,lexerP
                ,execute
                ,Alex(..)
                ,Program(..)
                ,Class(..)
                ,Feature(..)
                ,Formal(..)
                ,Expr(..)) where

import Prelude hiding (Ordering(..))
import Lexer

}

%name parser
%tokentype { Token }
%monad { Alex } { thenAlex } { returnAlex }
%lexer { lexer } { EOF }
%error { parseError }

%token
  class           { CLASS }
  inherits        { INHERITS }
  while           { WHILE }
  let             { LET }
  if              { IF }
  fi              { FI }
  case            { CASE }
  esac            { ESAC }
  loop            { LOOP }
  pool            { POOL }
  in              { IN }
  of              { OF }
  else            { ELSE }
  isvoid          { ISVOID }
  new             { NEW }
  then            { THEN }
  not             { NOT }
  '~'             { TILD }
  '{'             { LBRACE }
  '}'             { RBRACE }
  '('             { LPAREN }
  ')'             { RPAREN }
  '+'             { PLUS }
  '-'             { NEG }
  '*'             { MUL }
  '/'             { DIV }
  ':'             { COLON }
  ','             { COMMA }
  ';'             { SEMI }
  '.'             { PERIOD }
  '@'             { AT }
  '<-'            { ASSIGN }
  '=>'            { LARROW }
  '<'             { LT }
  '>'             { GT }
  '<='            { LEQ }
  '>='            { GEQ }
  '='             { EQ }
  typeid          { TYPE $$ }
  objectid        { ID $$ }
  int             { INT $$ }
  string          { STRING $$ }
  true            { TRUE }
  false           { FALSE }

%right '<-'
%left not
%nonassoc '<' '=' '<=' '>' '>='
%left '+' '-'
%left '*' '/'
%left '@'
%left '.'

%%

Program : Classes                                             { Program $1 }

Classes : Class ';' ClassList                                 { $1 : $3 }

ClassList : Classes                                           { $1 }
          |                                                   { [] }

Class : class typeid Parent '{' Features                      { Class $2 $3 $5 } 

Parent : inherits typeid                                      { $2 }
       |                                                      { "Object" }

Features : Feature ';' Features                               { $1 : $3 }
         | '}'                                                { [] }

Feature : Method                                              { $1 }
        | Attr                                                { $1 }

Method : objectid '(' Formals ')' ':' typeid '{' MethodBody   { Method $1 $3 $6 $8 }

MethodBody : Expr '}'                                         { $1 }

Formals : Formal ',' Formals                                  { $1 : $3 }
        | Formal                                              { [$1] }
        |                                                     { [] }

Formal  : objectid ':' typeid                                 { Formal $1 $3 }

Attr : objectid ':' typeid                                    { Attr $1 $3 Nothing }

Assign : objectid '<-' Expr1                                  { Assign $1 $3 }

Dispatch : Expr1 '.' objectid '(' Params                      { Dispatch $3 Nothing $1 $5 }
         | Expr1 '@' typeid '.' objectid '(' Params           { Dispatch $5 (Just $3) $1 $7 }

StaticDispatch : objectid '(' Params                          { StaticDispatch $1 $3 }

While : while Expr1 loop Expr1 pool                           { Loop $2 $4 }

Condition : if Expr1 then Expr1 fi                            { Cond $2 $4 Nothing }
          | if Expr1 then Expr1 else Expr1 fi                 { Cond $2 $4 (Just $6) }

Block : '{' BlockContent                                      { Block $2 }

Let : let Decl Decls in Expr1                                 { Let ($2 : $3) $5 }    

Case : case Expr1 of Alt Alts esac                            { Case $2 ($4 : $5) }

New : new typeid                                              { New $2 }

Isvoid : isvoid Expr1                                         { Isvoid $2 }

Alts : Alt Alts                                               { $1 : $2 }
     |                                                        { [] }

Alt : objectid ':' typeid '=>' Expr1 ';'                      { ($1, $3, $5) }    

Decls : ',' Decl Decls                                        { $2 : $3 }
      |                                                       { [] } 

Decl : objectid ':' typeid                                    { ($1, $3, Nothing) }
     | objectid ':' typeid '<-' Expr1                         { ($1, $3, Just $5) }                    

BlockContent : Expr1 ';' BlockContent                         { $1 : $3 }
             | Expr1 ';' '}'                                  { [$1] }

Params : Param ',' Params                                     { $1 : $3 }
       | Param ')'                                            { [$1] }
       | ')'                                                  { [] }

Param : Expr1                                                 { $1 }

Expr : Expr1                                                  { $1 }
     |                                                        { NoExpr }

Expr1 : Assign                                                 { $1 }
      | Dispatch                                               { $1 }
      | StaticDispatch                                         { $1 }
      | While                                                  { $1 }
      | Block                                                  { $1 }
      | Condition                                              { $1 }
      | Let                                                    { $1 }
      | Case                                                   { $1 }
      | New                                                    { $1 }
      | Isvoid                                                 { $1 }
      | Expr1 '*' Expr1                                        { Mul $1 $3 }
      | Expr1 '/' Expr1                                        { Divide $1 $3 }
      | Expr1 '+' Expr1                                        { Plus $1 $3 }
      | Expr1 '-' Expr1                                        { Sub $1 $3 }
      | Expr1 '<' Expr1                                        { Lt $1 $3 }
      | Expr1 '<=' Expr1                                       { Leq $1 $3 }
      | Expr1 '>' Expr1                                        { Gt $1 $3 }
      | Expr1 '>=' Expr1                                       { Geq $1 $3 }
      | Expr1 '=' Expr1                                        { Eq $1 $3 }
      | not Expr1                                              { Not $2 }
      | '~' Expr1                                              { Tild $2 }
      | '(' Expr1 ')'                                          { $2 }
      | objectid                                               { Object $1 }
      | string                                                 { StringConst $1 }
      | int                                                    { IntConst $1 }
      | true                                                   { BoolConst True }
      | false                                                  { BoolConst False}

{

thenAlex :: Alex a -> (a -> Alex b) -> Alex b
thenAlex = (>>=)

returnAlex :: a -> Alex a
returnAlex = return

type Line = Int
type Name = String
type Type = String
type Parent = String
type Predicate = Expr
type Identifier = String
type Init = Expr
type Body = Expr

data Program = Program [Class] deriving Show
data Class = Class Type Parent [Feature] deriving Show
data Feature = Attr Name Type (Maybe Expr) | Method Name [Formal] Type Expr deriving Show
data Formal = Formal Name Type deriving Show

data Expr = Assign Name Expr
          | Block [Expr]
          | BoolConst Bool
          | Comp Expr
          | Cond Predicate Expr (Maybe Expr)
          | Dispatch Name (Maybe Type) Expr [Expr]
          | Divide Expr Expr
          | Eq Expr Expr
          | IntConst Int
          | Isvoid Expr
          | Leq Expr Expr
          | Let [(Identifier, Type, Maybe Init)] Body 
          | Loop Predicate Body
          | Lt Expr Expr
          | Gt Expr Expr
          | Geq Expr Expr
          | Mul Expr Expr
          | Neg Expr
          | New Type
          | NoExpr
          | Object Name
          | Plus Expr Expr
          | StaticDispatch Name [Expr]
          | StringConst String
          | Sub Expr Expr
          | Tild Expr
          | Not Expr
          | Case Expr [(Name, Type, Expr)] deriving Show

makeName :: Token -> Name
makeName (TYPE x) = x
makeName (ID x)   = x

mkString :: Token -> String
mkString (STRING x) = x

makeInt :: Token -> Int
makeInt (INT x) = x

parseError t = do
  (_, l, c) <- getPosn
  failAlex ("l" ++ (show l) ++ ", c" ++ (show c) ++ " on token " ++ (show t))


happyError = do
  (_, l, c) <- getPosn
  error ("Parse error on line " ++ (show l) ++ " and column " ++ (show c) ++ " \n")
}
