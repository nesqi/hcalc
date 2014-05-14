import Text.ParserCombinators.Parsec
import Control.Monad
import Data.Char
import Data.Ratio
import Data.List
import qualified Data.Map.Lazy as ML

data Expr = Value Rational
          | Neg Expr
          | Inv Expr
          | Op String Expr [ Expr ]
          | UnOp String Expr
    deriving (Eq, Show, Ord)

isValue :: Expr -> Bool
isValue (Value _) = True
isValue _ = False

isInvValue :: Expr -> Bool
isInvValue (Inv (Value _)) = True
isInvValue _ = False

isNegValue :: Expr -> Bool
isNegValue (Neg (Value _)) = True
isNegValue _ = False

isOp :: Expr -> Bool
isOp (Op _ _ _) = True
isOp _ = False

isUnOp :: Expr -> Bool
isUnOp (UnOp _ _) = True
isUnOp _ = False

--instance Show Expr where
--    show (Value i) = show i
--    show (BinOp o a b) = "(" ++ show a ++ o ++ show b ++ ")"
--    show (UnOp f a) = f ++ "(" ++ show a ++ ")"

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

simplify :: Expr -> Expr
simplify = transform f
    where f (Op "^" (Value a) [(Value b)]) = case (b >= 0, (denominator b) == 1) of
                                                 (True,  True) -> (Value $ a ^ (numerator b))
                                                 _             -> (Op "^" (Value a) [(Value b)])

          f (Op "-" (Value x) [Value y]) = Value $ x - y

          -- Addition of 0
          f (Op "+" (Value 0) a) = toOp "+" a
          f (Op "+" a [Value 0]) = a
       
          f (Neg (Value a)) = Value $ -a

          f (Op "+" a b) = toOp "+" $ merge (+) lowerT liftT (a:b)
                           where
                               liftT (Op "*" (Value x) [y]) = (y, Just x)
                               liftT (Op "*" y [Value x]) = (y, Just x)
                               liftT (Value x) = (Value 1, Just x)
                               liftT (Neg x) = (x, Just (-1))
                               liftT (x) = (x, Just 1)
                               
                               lowerT (_, Just 0)  = []
                               lowerT ((Value 1), Just x)  = [(Value x)]
                               lowerT (x, Just (-1)) = [Neg x]
                               lowerT (x, Just 1)  = [x]
                               lowerT (x, Just y)  = [(Op "*" (Value $ y) [x])]

          -- Reduce integer devisions
          f (Op "/" (Value a) [Value b]) = (Value $ a / b)

          -- Multiplication by 1 or 0
          f (Op "*" (Value 1) a) = toOp "*" a
          f (Op "*" a [Value 1]) = a
          f (Op "*" (Value 0) _) = Value 0
          f (Op "*" _ [Value 0]) = Value 0

          f (Op "*" a b) = toOp "*" $ mergeValues (a:b)
                           where
                               -- Merge values
                               mergeValues = merge (*) lowerVal liftVal
                               
                               liftVal (Value x)       = (Value 1, Just x)
                               liftVal (Inv (Value x)) = (Value 1, Just $ 1 / x)
                               liftVal (x) = (x, Nothing)
                               
                               lowerVal (_, Just 0) = []
                               lowerVal ((Value 1), Just x)  = [(Value x)]
                               lowerVal (x, Nothing)  = [x]
                               
                               -- Merge Expressions
                               mergeExpr = merge (+) lowerExpr liftExpr
                               
                               liftExpr (Value x)       = (Value x, Nothing)
                               liftExpr (Inv (Value x)) = (Inv (Value x), Nothing)
                               liftExpr (Op "*" (Value x) [y]) = (y, Just x)
                               liftExpr (Op "*" y [Value x]) = (y, Just x)
                               liftExpr (Neg x) = (x, Just (-1))
                               liftExpr (x) = (x, Just 1)
                               
                               lowerExpr (_, Just 0)  = []
                               lowerExpr ((Value 1), Just x)  = [(Value x)]
                               lowerExpr (x, Just (-1)) = [Neg x]
                               lowerExpr (x, Just 1)  = [x]
                               lowerExpr (x, Just y)  = [(Op "^" x [Value $ y])]
                               lowerExpr (x, Nothing)  = [x]
          
          f x = x

          merge cOp down up l = let (process, pass) = partition hasValue $ fmap up l
                                    merged = ML.toList . ML.fromListWith (liftM2 cOp) $ process
                                    hasValue (_, Just _) = True
                                    hasValue _           = False
                                in foldl1 (++) $ fmap down $ merged ++ pass
          
          toOp op lst = case lst of
                            [] -> Value 0
                            [x] -> x
                            (x:xs) -> (Op op x xs)


-- a/b*c -> (a*c)/b
--simplify (BinOp "*" (BinOp "/" a b) c) = simplify $ BinOp "/" (simplify $ BinOp "*" a c) (simplify b)
-- a/b+c -> (a+c*b)/b | b, c are Values
--simplify (BinOp "+" (BinOp "/" a (Value b)) (Value c)) = simplify $ BinOp "/" (simplify $ BinOp "+" a (Value $ b * c)) (Value b)
--simplify (BinOp "+" (Value c) (BinOp "/" a (Value b))) = simplify $ BinOp "/" (simplify $ BinOp "+" a (Value $ b * c)) (Value b)
-- a/b+c/d -> (a*d+c*b)/b*d | a, b, c, d are Values
--simplify (BinOp "+" (BinOp "/" (Value a) (Value b)) (BinOp "/" (Value c) (Value d))) = 
--    simplify $ BinOp "/" (simplify $ BinOp "+" (Value $ a * d) (Value $ c * b)) (Value $ b * d)
--simplify (BinOp "*" (Value a) (Value b)) = (Value $ a * b)
--simplify (BinOp "*" b (Value a)) = (BinOp "*" e (Value $ a*v)) where (e, v) = collect b
--simplify (BinOp "*" (Value a) b) = (BinOp "*" (Value $ v*a) e) where (e, v) = collect b

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
                                      print $ flatten e
                                      print $ simplify $ flatten e
                     (Left err) -> print $ err
