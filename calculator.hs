import Text.ParserCombinators.Parsec
import Control.Monad
import Numeric
import Data.Char
import Data.List
import qualified Data.Map.Lazy as ML

data Expr = Value Integer
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
    where f (Op "^" (Value a) [(Value b)]) = if b < 0 then
                                                 Op "/" (Value 1) [(Value $ a ^ (-b))]
                                             else
                                                 (Value $ a ^ b)

          f (Op "-" (Value x) [Value y]) = Value $ x - y

          -- Addition of 0
          f (Op "+" (Value 0) a) = case a of
                                       [x]    -> x
                                       (x:xs) -> (Op "+" x xs)
          f (Op "+" a [Value 0]) = a
       
          f (Neg (Value a)) = Value $ -a

          f (Op "+" a b) = collectSame $ mergeValues (Op "+" a b)
                           where
                               mergeValues = merge (isValue) addVal (Value 0)
                               addVal (Value x) (Value y) = Value $ x + y

                               collectSame = mergeEq multExpr
                               multExpr (x, 1) = x
                               multExpr (x, y) = (Op "*" (Value $ toInteger y) [x])

          -- Reduce integer devisions
          f (Op "/" (Value a) [Value b]) = if d == b then 
                                               Value $ div a b
                                           else
                                               (Op "/" (Value $ div a d) [Value $ div b d])
                                           where d = gcd a b

          -- Multiplication by 1 or 0
          f (Op "*" (Value 1) a) = case a of
                                       [x] -> x
                                       (x:xs) -> (Op "*" x xs)
          f (Op "*" a [Value 1]) = a
          f (Op "*" (Value 0) _) = Value 0
          f (Op "*" _ [Value 0]) = Value 0

          f (Op "*" a b) = merge isInvOrValue mulVal (Op "/" (Value 1) [Value 1]) (Op "*" a b)
                           where
                               isInvOrValue x = or [isInvValue x, isValue x]
                               mulVal (Value x)       (Op "/" (Value t) [Value n]) = (Op "/" (Value $ t * x) [Value n])
                               mulVal (Inv (Value x)) (Op "/" (Value t) [Value n]) = (Op "/" (Value t) [Value $ n * x])
                               mulVal (Op "/" (Value t) [Value n]) (Value x)       = (Op "/" (Value $ t * x) [Value n])
                               mulVal (Op "/" (Value t) [Value n]) (Inv (Value x)) = (Op "/" (Value t) [Value $ n * x])
                               mulVal (Op "/" (Value t) [Value n]) (Op "/" (Value x) [Value y]) = (Op "/" (Value $ t * x) [Value $ n * y])
          
          f x = x

          -- Merge different expressions
          merge collect combine ident (Op op a b) =
              let (vals, rest) = partition collect (a:b)
                  lst = if length vals > 1 then
                            (foldr combine ident vals):rest
                        else
                            a:b
              in case lst of
                  [x]    -> x
                  (x:xs) -> (Op op x xs)
          
          -- Merge equal expressions
          mergeEq :: ((Expr, Int) -> Expr) -> Expr -> Expr
          mergeEq f (Op op a b) = let lst = fmap f $ nubCount (a:b)
                                  in case lst of
                                      [x]    -> x
                                      (x:xs) -> (Op op x xs)

          nubCount :: Ord a => [a] -> [(a, Int)]
          nubCount = ML.toList . ML.fromListWith (+) . flip zip (repeat 1)


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
