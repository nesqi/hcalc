import Text.ParserCombinators.Parsec
import Control.Monad

data Expr = Value Double
          | BinOp Char Expr Expr
          | UnOp String Expr

instance Show Expr where
    show (Value i) = show i
    show (BinOp o a b) = "(" ++ show a ++ [o] ++ show b ++ ")"
    show (UnOp f a) = f ++ "(" ++ show a ++ ")"

eval :: Expr -> Double
eval (Value i) = i
eval (BinOp o a b) = case o of
                         '+' -> (eval a) + (eval b)
                         '-' -> (eval a) - (eval b)
                         '*' -> (eval a) * (eval b)
                         '/' -> (eval a) / (eval b)
                         '^' -> (eval a) ** (eval b)

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
statement = term

operator1 :: Parser Char
operator1 = char '+'
        <|> char '-'

operator2 :: Parser Char
operator2 = char '*'
        <|> char '/'

operator3 :: Parser Char
operator3 = char '^'

function :: Parser String
function = string "cos"
       <|> string "sin"

leftA op exp a = do o <- op
                    b <- exp
                    leftA op exp (BinOp o a b)
                 <|> return a

rightA op a = do o <- op
                 b <- do c <- atom
                         rightA op c <|> return c
                 return (BinOp o a b)

termRest = leftA operator1 prod
prodRest = leftA operator2 expT
expRest = rightA operator3
       
atom :: Parser Expr
atom = parenTerm
   <|> fun
   <|> value
   where parenTerm = do char '('; a <- term; char ')'; return a

term :: Parser Expr
term = do a <- prod
          termRest a <|> return a

prod :: Parser Expr
prod = do a <- expT
          prodRest a <|> return a

expT :: Parser Expr
expT = do a <- atom
          expRest a <|> return a

fun :: Parser Expr
fun = do f <- function
         a <- atom
         return (UnOp f a)

value :: Parser Expr
value = liftM (Value . read) $ many1 digit

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

