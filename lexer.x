{
module Lexer where

import Prelude hiding (Ordering(..))
import Control.Monad
import Data.Either

}

%wrapper "monadUserState"

$digit = 0-9
$upper = [A-Z]
$lower = [a-z]
$space = $white # \n

@blank = \n $space*
$alpha = [$lower $upper]
@type  = $upper [$alpha $digit \_]*
@id    = $lower [$alpha $digit \_]*

tokens :-
  <0, comment> $white+                      { skip }
  <0> [cC][lL][aA][sS][sS]                  { tk CLASS }
  <0> [iI][nN][hH][eE][rR][iI][tT][sS]      { tk INHERITS }
  <0> [tT][hH][eE][nN]                      { tk THEN }
  <0> [iI][fF]                              { tk IF }
  <0> [fF][iI]                              { tk FI }
  <0> [iI][nN]                              { tk IN }
  <0> [eE][lL][sS][eE]                      { tk ELSE }
  <0> [lL][oO][oO][pP]                      { tk LOOP }
  <0> [pP][oO][oO][lL]                      { tk POOL }
  <0> [wW][hH][iI][lL][eE]                  { tk WHILE }
  <0> [lL][eE][tT]                          { tk LET }
  <0> [cC][aA][sS][eE]                      { tk CASE }
  <0> [eE][sS][aA][cC]                      { tk ESAC }
  <0> [oO][fF]                              { tk OF }
  <0> [nN][eE][wW]                          { tk NEW }
  <0> [nN][oO][tT]                          { tk NOT }
  <0> [iI][sS][vV][oO][iI][dD]              { tk ISVOID }
  <0> true                                  { tk TRUE }
  <0> false                                 { tk FALSE }
  <0> @type                                 { token (\(_,_,s) n -> TYPE (take n s)) }
  <0> @id                                   { token (\(_,_,s) n -> ID (take n s)) }
  <0> $digit+                               { token (\(_,_,s) n -> INT (read $ take n s)) } 
  <0> \+                                    { tk PLUS }
  <0> \-                                    { tk NEG }
  <0> \*                                    { tk MUL }
  <0> \/                                    { tk DIV }
  <0> \@                                    { tk AT }
  <0> \~                                    { tk TILD }
  <0> \.                                    { tk PERIOD }
  <0> \:                                    { tk COLON }
  <0> \;                                    { tk SEMI }
  <0> \,                                    { tk COMMA }
  <0> \(                                    { tk LPAREN }
  <0> \)                                    { tk RPAREN }
  <0> \{                                    { tk LBRACE }
  <0> \}                                    { tk RBRACE }
  <0> \<                                    { tk LT }
  <0> \>                                    { tk GT }
  <0> \<\=                                  { tk LEQ }
  <0> \>\=                                  { tk GEQ }
  <0> \=                                    { tk EQ }
  <0> \<\-                                  { tk ASSIGN }
  <0> \=\>                                  { tk LARROW }
  <0> \-\-.*                                { skip }
  <0> \(\*                                  { incrementCommentDepth `andBegin` comment }
  <0> \"                                    { startString `andBegin` string }
  <0> .                                     { tk ERROR }
  <comment> \(\*                            { incrementCommentDepth }
  <comment> \*\)                            { decrementCommentDepth }
  <comment> .                               { skip }
  <string> \\(\n)+                          { skip }
  <string> \0                               { \_ _ -> alexError "string contains null character" }
  <string> (\n)+                            { \_ _ -> alexError "String contains non-escaped newline" }
  <string> \\n                              { appendStringValueWith "\\n" }
  <string> \\b                              { appendStringValueWith "\\b" }
  <string> \\t                              { appendStringValueWith "\\t" }
  <string> \\f                              { appendStringValueWith "\\f" }
  <string> \\.                              { appendEscapedChar }
  <string> (. # [\\\"])+                    { appendStringValue }
  <string> \"                               { makeString `andBegin` 0 } 
{
data Token = CLASS
           | INHERITS
           | LARROW
           | LPAREN
           | RPAREN
           | COLON
           | LBRACE
           | RBRACE
           | ASSIGN
           | AT
           | COMMA
           | LT
           | GT
           | LEQ
           | GEQ
           | EQ
           | IF
           | FI
           | THEN
           | IN
           | ELSE
           | LOOP
           | POOL
           | WHILE
           | LET
           | CASE
           | ESAC
           | OF
           | NEW
           | NOT
           | TRUE
           | FALSE
           | ISVOID
           | PLUS
           | NEG
           | MUL
           | DIV
           | TILD
           | PERIOD
           | SEMI
           | TYPE String
           | ID String
           | INT Int
           | STRING String
           | ERROR
           | EOF deriving Show

tk x = token (\_ _ -> x)

data AlexUserState = AlexUserState {commentDepth :: Int
                                   ,stringValue  :: String
                                   ,stringPosn   :: (Line, Column) } 

alexInitUserState = AlexUserState 0 "" (-1, -1)

type Line   = Int
type Column = Int

--data Lexeme = Lexeme Line Column Token deriving Show

get = Alex $ \s   -> Right (s, alex_ust s)
put u = Alex $ \s -> Right (s{alex_ust=u}, ())
modify f = put . f =<< get

getCommentDepth = liftM commentDepth get
getStringValue  = liftM stringValue get
getStringPosn   = liftM stringPosn get

putStringPosn v = modify go
  where
    go s = s{stringPosn=v}

modifyStringValue f = modify go
  where
    go s@(AlexUserState{stringValue=v}) = s{stringValue=(f v)}

putStringValue v = modifyStringValue (const v)

appendStringValue r@(_,_,i) l = do
   modifyStringValue (++ (take l i))
   skip r l

appendStringValueWith str i l = do
   modifyStringValue (++ str)
   skip i l

appendEscapedChar r@(_,_,i) l = do
  let (_:c:_) = take l i
  appendStringValueWith [c] r l

makeString _ _ = do
  v     <- getStringValue
  (l,c) <- getStringPosn
  return $ STRING v

startString i@((AlexPn _ l c),_,_) r = do
  putStringValue ""
  putStringPosn (l,c)
  skip i r

incr (AlexUserState d s p) = AlexUserState (d+1) s p
decr (AlexUserState d s p) = AlexUserState (d-1) s p

incrementCommentDepth i l = do
  modify incr
  skip i l

decrementCommentDepth i l = do
  modify decr
  depth <- getCommentDepth
  if depth == 0 then begin 0 i l else skip i l

alexEOF = return EOF

--lexer input = runAlex input loop
lexerP = loop
  where
    loop = let go EOF = do
                 state <- alexGetStartCode
                 case state of
                   0 -> return [EOF]
                   x | x == comment -> alexError "Unterminated comment section"
                     | x == string  -> alexError "Unterminated string section"
               go x   = liftM (x:) loop
           in alexMonadScan >>= go

lexer :: (Token -> Alex a) -> Alex a
lexer k = alexMonadScan >>= go
  where
    go EOF = do
      state <- alexGetStartCode
      case state of
        0 -> k EOF
        x | x == comment -> alexError "Unterminated comment section"
          | x == string  -> alexError "Unterminated string section"
    go x = k x

getState = Alex $ \x -> Right (x, x)

getPosn = do
  AlexState (AlexPn x l c) _ _ _ _ <- getState
  return (x, l, c)

execute :: Show a => Alex a -> String -> IO ()
execute action input = either print print (runAlex input action)

failAlex msg = Alex $ \_ -> Left msg

--run :: String -> IO ()
--run input = either print (mapM_ print) (lexer input)
}