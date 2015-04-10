module Main where

import Text.ParserCombinators.Parsec
import Control.Monad
import Data.Char
import Data.List
import qualified Data.Map.Lazy as ML

import Data.IORef
import Test.QuickCheck

--TODO: 
-- Nice printouts
-- Evaluation (Simplification + evaluation)
-- Print out mode (Dec, Hex, Oct, ...)
-- Variables
-- Functions
-- Modulo operator

data Oper = ADD
          | SUB
          | MUL
          | DIV
          | EXP
          | Fun String
    deriving (Eq, Show, Ord)

operToStr :: Oper -> String
operToStr ADD = "+"
operToStr SUB = "-"
operToStr MUL = "*"
operToStr DIV = "/"
operToStr EXP = "^"
operToStr (Fun s) = s

data Expr = Value (NonNegative Integer)
          | BinOp Oper Expr Expr
          | UnOp Oper Expr
    deriving (Eq, Show, Ord)

-- For quickCheck
instance Arbitrary Expr where
    arbitrary = sized exprTree
        where exprTree 0 = liftM Value arbitrary
              exprTree n = oneof [ liftM2 UnOp someUnOp (exprTree $ n-1),
                                   liftM3 BinOp someBinOp (exprTree $ n `div` 2)
                                                          (exprTree $ n `div` 2) ]
              someBinOp = elements [ ADD, SUB, MUL, DIV, EXP ]
              someUnOp  = elements [ SUB, Fun "sin", Fun "cos" ]

    shrink (Value x) = []
    shrink (UnOp op x) = [x] ++ [UnOp op x' | x' <- shrink x]
    shrink (BinOp op x y)  = [BinOp op x' y' | (x', y') <- shrink (x, y)]

exprToString :: Expr -> String
exprToString (Value x) = show $ getNonNegative x
exprToString (BinOp op a b) = "(" ++ exprToString a ++ operToStr op ++ exprToString b ++ ")"
exprToString (UnOp (Fun f) a) = "(" ++ f ++ (exprToString a) ++ ")"
exprToString (UnOp op a) = "(" ++ operToStr op ++ (exprToString a) ++ ")"

transform :: (Expr -> Expr) -> Expr -> Expr
transform f old = let new = case old of
                                (BinOp op a b) -> f (BinOp op (transform f a) (transform f b))
                                (UnOp op a) -> f (UnOp op (transform f a))
                                a -> f a
                  in if new == old then old else transform f new 

{- transform this into some kind of access-function
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
-}

data Ent a = CombineE Expr a -- Expression that should be combined
           | CombineI a      -- No expression needed just combine
           | Pass Expr       -- Don't combine just pass along
    deriving (Eq)

expNumOfDigitsInBase10 :: Floating a => (NonNegative Integer) -> (NonNegative Integer) -> a
expNumOfDigitsInBase10 a b = fromNN b * (log $ fromNN a) / (log 10)
                             where fromNN = fromInteger . getNonNegative

simplify :: Expr -> Expr
simplify = transform f where 
    -- Exponent
    f (BinOp EXP (Value 0) _) = Value 0
    f (BinOp EXP _ (Value 0)) = Value 1
    f (BinOp EXP (Value a) (Value b)) | expNumOfDigitsInBase10 a b < 50 = (Value $ a ^ b)

    f (BinOp SUB (Value x) (Value y)) = Value $ x - y

    -- Double negation
    f (UnOp SUB (UnOp SUB x)) = x
    
{-
    f (Op "+" a b) = toOp "+" $ merge lowerT liftT (a:b)
        where liftT (Op "*" (Value x) [y]) = [CombineE y (x+)]
              liftT (Op "*" y [Value x]) = [CombineE y (x+)]
              liftT (Value x) = [CombineI (x+)]
              liftT (Neg x) = [CombineE x (-1+)]
              liftT (x) = [CombineE x (1+)]

              lowerT (Pass x) = [x]
              lowerT (CombineI n) | (n 0) == 0 = []
              | otherwise = [Value (n 0)]

              lowerT (CombineE x n) | (n 0) == 0 = []
              | (n 0) == -1 = [Neg x]
              | (n 0) == 1 = [x]
              | otherwise = [Op "*" (Value $ n 0) [x]]
-}
    -- Reduce integer divisions
    f (BinOp DIV (Value a) (Value b)) | a `rem` b == 0 = (Value $ a `div` b)

{-
    -- Multiplication by 1 or 0
    f (Op "*" (Value 1) a) = toOp "*" a
    f (Op "*" a [Value 1]) = a
    f (Op "*" (Value 0) _) = Value 0
    f (Op "*" _ [Value 0]) = Value 0
-}

{-
    f (Op "*" a b) = toOp "*" $ merge lowerE liftE (a:b)
    where
    -- Values
    liftE (Op "*" (Value x) [y]) = [CombineI (x*), Pass y]
    liftE (Op "*" y [Value x])   = [CombineI (x*), Pass y] 
    liftE (Neg x) = [CombineI ((-1)*)] ++ liftE x
    liftE (Value x)       = [CombineI (x*)]
    liftE (Inv (Value x)) = [CombineI ((1/x)*)]
    -- Expr
    --liftE (Op "^" (Value x) [y]) = [CombineE (Value x) (y+)]
    liftE (Op "^" y [Value x])   = [CombineE y (x+)] 
    liftE (Inv x) = [CombineE x (-1+)]
    liftE (x) = [CombineE x (1+)]

    lowerE (Pass x)  = [x]
    lowerE (CombineI x)  = [Value $ x 1]
lowerE (CombineE x n) 
    | (n 0) == 0 = []
    | (n 0) == 1 = [x]
    | otherwise  = [Op "^" x [Value $ n 0]]
-}
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


inLine :: Parser [[Expr]]
inLine = endBy statements newline

semiColon :: Parser Char
semiColon = char ';'

statements :: Parser [Expr]
statements = sepBy statement semiColon

statement :: Parser Expr
statement = exprP

function :: Parser Oper
function = do s <- funStr
              return $ Fun s
           where funStr = string "cos" 
                      <|> string "sin"

atom :: Parser Expr
atom = parenTerm
   <|> unOp
   <|> fun
   <|> valueP
   where parenTerm = do char '('; a <- statement; char ')'; return a

unOp :: Parser Expr
unOp = do op <- opParser "-" SUB
          a <- atom
          return $ (UnOp op a)

fun :: Parser Expr
fun = do f <- function
         a <- atom
         return (UnOp f a)

valueP :: Parser Expr 
valueP = (try $ string "0x" >> integerP 16)
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
                         , parser :: Parser Oper
                         }

opParser :: String -> Oper -> Parser Oper
opParser str op = do string str
                     return $ op

exprP :: Parser Expr
exprP = inner lst where
    lst = [ [Operator BinLeft  $ opParser "+" ADD,  -- level 1
             Operator BinLeft  $ opParser "-" SUB]
          , [Operator BinLeft  $ opParser "*" MUL,  -- level 2
             Operator BinLeft  $ opParser "/" DIV]
          , [Operator BinRight $ opParser "^" EXP]  -- level 3
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
                    (Operator BinLeft n)  -> n
                    (Operator BinRight n) -> n

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

parseString :: String -> Maybe Expr
parseString str = case parseLine $ str ++ "\n" of
                      (Right [[e]]) -> Just e
                      _ -> Nothing

-- QuickCheck
prop_simplify :: Expr -> Bool
prop_simplify x = simplify (BinOp MUL (Value 2) x) == simplify (BinOp ADD x x)

prop_print_and_parse :: Expr -> Bool
prop_print_and_parse x = maybe False (\y -> xStr == exprToString y) (parseString xStr)
                         where xStr = exprToString x

repl :: IO ()
repl = do putStr "HCalc\n"
          forever $
              do l <- getLine
                 case parseLine (l ++ "\n") of
                     (Right [[e]]) -> do 
                         putStrLn $ show e
                         putStrLn $ maybe "Could not parse" exprToString (parseString $ exprToString e)
                         putStrLn $ exprToString e
                         putStrLn $ (exprToString $ simplify e)
                     (Right _) -> putStr "Error: no input.\n"
                     (Left err) -> putStr $ show err

main :: IO ()
main = repl
