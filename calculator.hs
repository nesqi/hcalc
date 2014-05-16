import Text.ParserCombinators.Parsec
import Control.Monad
import Data.Char
import Data.Ratio
import Data.List
import qualified Data.Map.Lazy as ML

--TODO: 
-- Nice printouts
-- Evaluation (Simplification + evaluation)
-- Tests (quick check)
-- Print out mode (Dec, Hex, Oct, ...)
-- Variables
-- Functions
-- Modulo operator

data Expr = Value Rational
          | Neg Expr
          | Inv Expr
          | Op String Expr [ Expr ]
          | UnOp String Expr
    deriving (Eq, Show, Ord)

transform :: (Expr -> Expr) -> Expr -> Expr
transform f old = let new = case old of
                                (Op op a b) -> f (Op op (transform f a) (fmap (transform f) b))
                                (UnOp op a) -> f (UnOp op (transform f a))
                                a -> f a
                  in if new == old then old else transform f new 

flatten :: Expr -> Expr
flatten = transform f
    where f (Op "/" a b) = (Op "*" a $ fmap (Inv) b)
          f (Op "*" (Op "*" a b) c) = (Op "*" a (b ++ c))
          f (Op "*" a b) = (Op "*" a (extract "*" b))
          f (Op "-" a b) = (Op "+" a $ fmap (Neg) b)
          f (Op "+" (Op "+" a b) c) = (Op "+" a (b ++ c))
          f (Op "+" a b) = (Op "+" a (extract "+" b))
          f (Op op a b) = (Op op a b)
          f (UnOp op a) = (UnOp op a)
          f a = a
          
          extract op l = (foldl (++) [] $ fmap (unWrap op) l)
          unWrap op expr = case expr of
                               (Op o x y) -> if o == op then (x:extract op y) else [(Op o x y)]
                               x          -> [x]

data Ent a = CombineE Expr a -- Expression that should be combined
           | CombineI a      -- No expression needed just combine
           | Pass Expr       -- Don't combine just pass along
    deriving (Eq)

simplify :: Expr -> Expr
simplify = transform f
    where f (Op "^" (Value a) [(Value b)]) = case (b >= 0, (denominator b) == 1) of
                                                 (True,  True) -> (Value $ a ^ (numerator b))
                                                 _             -> (Op "^" (Value a) [(Value b)])

          f (Op "-" (Value x) [Value y]) = Value $ x - y

          -- Addition of 0
          f (Op "+" (Value 0) a) = toOp "+" a
          f (Op "+" a [Value 0]) = a
          f (Inv (Value a)) = Value $ 1/a
          f (Neg (Value a)) = Value $ -a

          f (Op "+" a b) = toOp "+" $ merge lowerT liftT (a:b)
                           where
                               liftT (Op "*" (Value x) [y]) = [CombineE y (x+)]
                               liftT (Op "*" y [Value x]) = [CombineE y (x+)]
                               liftT (Value x) = [CombineI (x+)]
                               liftT (Neg x) = [CombineE x (-1+)]
                               liftT (x) = [CombineE x (1+)]
                               
                               lowerT (Pass x) = [x]
                               lowerT (CombineI n)
                                   | (n 0) == 0 = []
                                   | otherwise = [Value (n 0)]
                               lowerT (CombineE x n)
                                   | (n 0) == 0 = []
                                   | (n 0) == -1 = [Neg x]
                                   | (n 0) == 1 = [x]
                                   | otherwise = [Op "*" (Value $ n 0) [x]]

          -- Reduce integer devisions
          f (Op "/" (Value a) [Value b]) = (Value $ a / b)

          -- Multiplication by 1 or 0
          f (Op "*" (Value 1) a) = toOp "*" a
          f (Op "*" a [Value 1]) = a
          f (Op "*" (Value 0) _) = Value 0
          f (Op "*" _ [Value 0]) = Value 0

          f (Op "*" a b) = toOp "*" $ merge lowerE liftE (a:b)
                           where
                               -- Values
                               liftE (Op "*" (Value x) [y]) = [CombineI (x*), Pass y]
                               liftE (Op "*" y [Value x])   = [CombineI (x*), Pass y] 
                               liftE (Neg x) = [CombineI ((-1)*)] ++ liftE x
                               liftE (Value x)       = [CombineI (x*)]
                               liftE (Inv (Value x)) = [CombineI ((1/x)*)]
                               -- Expr
                               liftE (Op "^" (Value x) [y]) = [CombineE y (x+)]
                               liftE (Op "^" y [Value x])   = [CombineE y (x+)] 
                               liftE (Inv x) = [CombineE x (-1+)]
                               liftE (x) = [CombineE x (1+)]

                               lowerE (Pass x)  = [x]
                               lowerE (CombineI x)  = [Value $ x 1]
                               lowerE (CombineE x n) 
                                   | (n 0) == 0 = []
                                   | (n 0) == 1 = [x]
                                   | otherwise  = [Op "^" x [Value $ n 0]]
          f x = x

          merge down up l = let (pass, process) = partition passQ $ foldl1 (++) $ fmap up l
                                merged = fmap (toComb) $ ML.toList . ML.fromListWith (.) $ fmap (toPair) process
                                passQ (Pass _) = True
                                passQ _        = False
                                toPair (CombineI n) = ([], n)
                                toPair (CombineE e n) = ([e], n)
                                toComb ([], n) = CombineI n
                                toComb ([e], n) = CombineE e n
                            in foldl (++) [] $ fmap down $ merged ++ pass
          
          toOp op lst = case lst of
                            [] -> Value 0
                            [x] -> x
                            (x:xs) -> (Op op x xs)


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
   <|> valueP
   where parenTerm = do char '('; a <- statement; char ')'; return a

fun :: Parser Expr
fun = do f <- function
         a <- atom
         return (UnOp f a)

valueP :: Parser Expr 
valueP = (char '-' >> do v <- valueP
                         return (Neg v))
     <|> (try $ string "0x" >> integerP 16)
     <|> (try $ string "0o" >> integerP 8)
     <|> (try $ string "0b" >> integerP 2)
     <|> integerP 10
     where
        integerP base = do v <- many1 $ choice $ map (charValP) [0..(base-1)]
                           return $ Value (fromIntegral (calc base v))
        calc base vs = sum $ zipWith (*) (baseList base) (reverse vs)
        baseList base = map (base^) [0..]
        charValP i = if i < 10 then
                        char (chr $ ord '0' + i) >> return i
                     else
                        ((char (chr $ ord 'A' + (i-10))) 
                        <|> (char (chr $ ord 'a' + (i-10)))) >> return i
                    

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
                            leftA op (Op o a [b])
                            <|> return a

            rightA op a = do o <- op
                             b <- do c <- atom
                                     rightA op c <|> return c
                             return (Op o a [b])

parseLine :: String -> Either ParseError [[Expr]]
parseLine input = parse inLine "(unknown)" input

main :: IO ()
main = do print "HCalc"
          forever $
              do l <- getLine
                 case parseLine (l ++ "\n") of
                     (Right es) -> do let e = (head $ head es)
                                      print $ e
                                      print $ simplify $ flatten e
                     (Left err) -> print $ err
