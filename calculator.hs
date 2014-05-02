import Text.ParserCombinators.Parsec
import Control.Monad

data Expr = Value Double
          | BinOp String Expr Expr
          | UnOp String Expr

instance Show Expr where
    show (Value i) = show i
    show (BinOp o a b) = "(" ++ show a ++ o ++ show b ++ ")"
    show (UnOp f a) = f ++ "(" ++ show a ++ ")"

eval :: Expr -> Double
eval (Value i) = i
eval (BinOp o a b) = case o of
                         "+" -> eval a + eval b
                         "-" -> eval a - eval b
                         "*" -> eval a * eval b
                         "/" -> eval a / eval b
                         "^" -> eval a ** eval b
eval (UnOp f a) = case f of
                      "sin" -> sin $ eval a
                      "cos" -> cos $ eval a

inLine :: Parser [[Expr]]
inLine = endBy statements newline

semiColon :: Parser Char
semiColon = char ';'

statements :: Parser [Expr]
statements = sepBy statement semiColon

statement :: Parser Expr
statement = exprP

function :: Parser String
function = string "cos"
       <|> string "sin"

atom :: Parser Expr
atom = parenTerm
   <|> fun
   <|> value
   where parenTerm = do char '('; a <- statement; char ')'; return a

fun :: Parser Expr
fun = do f <- function
         a <- atom
         return (UnOp f a)

value :: Parser Expr
value = liftM (Value . read) $ many1 digit

data OpType = BinRight
            | BinLeft
            | Unary

data Operator = Operator { opType :: OpType
                         , name :: String
                         }

exprP :: Parser Expr
exprP = inner lst where 
    lst = [ [Operator BinLeft  "+",  -- level 1
             Operator BinLeft  "-"]
          , [Operator BinLeft  "*",  -- level 2
             Operator BinLeft  "/"]
          , [Operator BinRight "^"]  -- level 3
          ]
    inner [] = atom
    inner (level:levels) = 
        do a <- inner levels
           parseRest level a <|> return a
        where 
            parseRest [] a = return a
            parseRest ops a = leftOrRight opP a where

                leftOrRight = case opType $ head ops of
                    BinLeft -> leftA
                    BinRight -> rightA
                
                opP = choice $ fmap infixP ops
                
                infixP op = case op of
                    (Operator BinLeft n)  -> (string n)
                    (Operator BinRight n) -> (string n)

            leftA op a = do o <- op
                            b <- inner levels
                            leftA op (BinOp o a b)
                            <|> return a
            rightA op a = do o <- op
                             b <- do c <- atom
                                     rightA op c <|> return c
                             return (BinOp o a b)

parseLine :: String -> Either ParseError [[Expr]]
parseLine input = parse inLine "(unknown)" input

main :: IO ()
main = forever $ 
           do l <- getLine
              case parseLine (l ++ "\n") of
                  (Right es) -> do let e = (head $ head es)
                                   print $ show $ e
                                   print $ show $ eval e
                  (Left err) -> print $ show $ err

