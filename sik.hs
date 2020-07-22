-- Sik syntax:
-- usual   + - * / % ^ < > = ! | & (no unary minus, use `0 foo -`)
-- choose  ? (`condition if_true if_false ?`) (pops three values, then pushes one)
-- pop     , (stack must be non-empty (or do nothing with empty stack?))
-- lift    \ (pushes n-th value of stack, counting downward from zero (last pushed))
-- print   : (prints value on top of stack and does NOT pop it)
-- input   ; (pushes string from stdin on stack as an array of chars)
-- apply   ' (top val must be fn; the fn will be popped before it's executed)
-- fn      ( fn_code )   (` ( fn_code ) ' ` does the same thing as just ` fn_code `.)
-- array   [ elem1 elem2 elem3 ] (an array is part of a table)
-- get     @ (`table key @`)     (`key` can be a number, a character or a string)
-- set     $ (`table key new_val $`) (a string is part of an array)
-- length  # (`table #`)   (`["abcd"] #` is 4, `[ 1 2 3 4x,]#` is 3)
-- num     1234.1234 or just 1234 (.1234 or 1234. isn't allowed, all numbers are floats)
-- char    "c" ("abc" is syntactic sugar for "a" "b" "c".)

-- : should print code that would create the value on top of the stack, for example
-- ["Hello world!"] or 3.14159 or [0.5x,1.0y,].

-- Unused: {} (brackets), ` (grave accent) and ~ (tilde); use $ for lift and \ for set?
-- Use ~ to get an array with all of the keys of the table on top of the stack?
-- Or use ~ to get a substring or subarray?
-- Or use ~ to get the n-th element on the stack (like lift), but also
-- remove it from its previous position?  (then 0~ does nothing and swap is 1~)
-- Use . as syntactic sugar? (`.usually_an_id` is `["usually_an_id"]`.)
-- Allow array concat with + (overloading) or use . ?

-- SikValue types: number, character, table, function, nil. (Functions are closures.)
-- Everything except nil is truthy. Use `truthy_val!` to create nil. `truthy_val!!` is 1.
-- Function returning closure: 5(x,(x))'pushes_five,6pushes_five'   --> 6 5

-- Permissive mode: do nothing when an error would occur.
-- Use `[" comment about foo "],` to write comments (push then pop string). 

-- Within [], everything is the same, except the array part of the table is
-- used instead of the default stack. Top-level ids used in [] become table
-- keys and can't be used as ids after the closing ]. An array is the part
-- of the table accessed by contiguous integers starting from zero. A string
-- is the initial part of an array that contains only chars, so "ab" is the
-- string of ["a"x,"ab"1"cd"]. When using a table as a key, everything
-- except its string part will be ignored.
-- $ (set) effectively pops `new_val`, `key` and `table` and then pushes
-- a new table with `new_val` stored at `key`. Using @ with a key that doesn't
-- have a value will push nil. Set keys to nil to delete them.

-- Using an identifier the first time assigns it the value on the top of the stack.
-- The value is NOT popped. Subsequent uses push the value on the stack. The value
-- that will be pushed on the stack when a certain identifier is written cannot be
-- changed, even though the value on the top of the stack can be changed after
-- pushing it there. Identifiers have function scope. There is no way to create an
-- identifier that shadows another.
-- For example: ( x , y , x y ) swap , 1 2 swap '  --> 2 1
-- With minimal whitespace: (x,y,x y)swap,1 2swap'

-- dup with variable: 1(x x)'  --> 1 1
-- Without variables: 1(0\)'

-- factorial: 4(n n2<(,1)(n1-fac'*)?')fac'  --> 24

-- A note about identifier scope: the compiler needs to look at all ids in
-- a function before looking at subfunctions in order for code like
-- `initial_code' (condition' base_case recursive_function ?') recursive_function'`
-- to work, since `recursive_function` is used in itself before `recursive_function`
-- is bound in the outer function. That is, ids need to be bound using breadth-
-- first search. Otherwise `recursive_function` would bind the value on top of the
-- stack inside of the subfunction, instead of pushing the subfunction on the stack.

-- What about `(()(x)?')f,1f'2x,1!f'`? Here an id from an outer scope is used only
-- if the top value of the stack is nil when f is applied. f is applied before the id
-- from the outer scope x is bound, but f doesn't actually use x, because the top
-- value is 1 when it is first applied. Then x is bound and f is applied again, this
-- time actually using the value of x, which is 2.
-- We could also take user input to choose whether to use the id or not. For example:
-- `(()(x)?')f, ;"a"= f' 2x, ;"a"= f'`
-- Then it is unknown at compile time whether x will be used before binding.
-- To be consistent with tables, trying to push an unbound identifier will push nil.

module Main where
import System.Environment
import System.IO
import Control.Exception (assert)
import Debug.Trace (trace)
import Text.Show
import Data.Char
import Data.List
import Data.Fixed (mod') -- mod for floating point numbers
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set

--- Frontend

isWhitespace :: Char -> Bool
isWhitespace = (`elem` " \n\t\r") -- TODO: Use `isSeparator` from `Data.Char` instead?

-- Lex types:
-- w whitespace
-- n number
-- i identifier
-- e escape
-- s string
-- b block start or end (parentheses, braces or brackets)
-- p punctuation (anything that isn't any of the other types)
-- x no type (used to indicate no special state or error)

-- Actual output part types are b, n, i, p and s.

type LexType = Char

-- Takes current char and state. Returns char type and next state.
getCharType :: Char -> LexType -> (LexType, LexType)
getCharType _    'e' = ('s', 's') -- was backslash -> escape one char, return to string
getCharType '\\' 's' = ('s', 'e') -- in string, backslash -> remember backslash
getCharType '"'  's' = ('s', 'x') -- in string, char is quote -> end string
getCharType _    's' = ('s', 's') -- in string, anything else -> still in string
getCharType '"'  _   = ('s', 's') -- not in string, quote -> start string
getCharType c 'x'
    | isLetter(c) || (c == '_') = ('i', 'x')
    | isDigit(c)  || (c == '.') = ('n', 'x')
    | isWhitespace(c)           = ('w', 'x')
    | (c `elem` "()[]{}")       = ('b', 'x')
    | otherwise                 = ('p', 'x')
getCharType _ s = ('x', s) -- Error: unknown type 'x'

getCharTypes :: [Char] -> LexType -> [LexType]
getCharTypes [] _ = []
getCharTypes (c:cs) state =
    let (charType, nextState) = getCharType c state in
        charType : getCharTypes cs nextState

type Part = (LexType, String)

getPartTypes :: [LexType] -> [LexType]
getPartTypes []  = []
getPartTypes [t] = [t]
getPartTypes (t:ts) = let rest = getPartTypes ts in
    if t == head rest then rest else t : rest

getPartStrs :: [Char] -> [LexType] -> [[Char]] 
getPartStrs []  _ = []
getPartStrs [c] _ = [[c]]
getPartStrs (c:cs) (t:ts) = let (p:ps) = getPartStrs cs ts in
    if t == head ts then (c:p):ps else [c]:p:ps

explodeParts :: LexType -> [Part] -> [Part]
explodeParts _ [] = []
explodeParts e ((t,[c]):ps) = (t,[c]) : explodeParts e ps
explodeParts e ((t,(c:cs)):ps)
    | (t == e)  = (t, [c])   : explodeParts e ((t, cs) : ps)
    | otherwise = (t,(c:cs)) : explodeParts e ps
    
-- Group chars into parts by type. Discard comments and whitespace.
getParts :: String -> [Part]
getParts str =
    let charTypes = getCharTypes str 'x'
        rawParts  = zip (getPartTypes charTypes) (getPartStrs str charTypes) in
        explodeParts 'b' $ filter ((/= 'w') . fst) rawParts
        
data FnParts = FnParts [Part] [FnParts] deriving (Show)

parseFn :: [Part] -> (FnParts, [Part])
parseFn [] = (FnParts [] [], [])
parseFn ((_,")"):ps) = (FnParts [] [], ps)
parseFn ((_,"("):ps) = (FnParts (('b',"()"):rest) (sub:subs), afterFn)
    where (sub,               afterSub) = parseFn ps
          (FnParts rest subs, afterFn)  = parseFn afterSub
parseFn (p:ps) = (FnParts (p:rest) subs, afterFn)
    where (FnParts rest subs, afterFn) = parseFn ps 
--parseFn x f c = trace ("px " ++ show x) (Fn f c [], x)

parseFns :: [Part] -> FnParts
parseFns = fst . parseFn

-- parseTables

--- Backend

escapeStr :: String -> String
escapeStr [] = []
escapeStr ('\\':'\\':cs) = '\\' : escapeStr cs
escapeStr ('\\':'n' :cs) = '\n' : escapeStr cs
escapeStr ('\\':'t' :cs) = '\t' : escapeStr cs
escapeStr ('\\':'"' :cs) = '\"' : escapeStr cs
escapeStr (c:cs)         = c    : escapeStr cs

readStr :: String -> String
readStr = (init . tail . escapeStr) -- Remove quotes at start and end of string.

data Cmd = Apply | Height | Pop | Lift | Choose | Not | And | Or | Equal | Lt | Gt |
           Plus | Minus | Mult | Div | Mod | Pow | Print | Input |
           PushNum Double | PushStr String | PushFn Int | PushID String | InitID String
           deriving (Show)
           
-- TODO: [] @ $ ~ ` . {}

getOp :: Char -> Cmd
getOp '\'' = Apply
getOp '#'  = Height -- TODO: Change to Len after implementing [].
getOp ','  = Pop
getOp '\\' = Lift
getOp '?'  = Choose
getOp '!'  = Not
getOp '&'  = And
getOp '|'  = Or
getOp '='  = Equal
getOp '<'  = Lt
getOp '>'  = Gt
getOp '+'  = Plus
getOp '-'  = Minus
getOp '*'  = Mult
getOp '/'  = Div
getOp '%'  = Mod
getOp '^'  = Pow
getOp ':'  = Print
getOp ';'  = Input

getOps :: String -> [Cmd]
getOps [] = []
getOps (c:cs) = getOp c : getOps cs

getPartCmds :: Part -> [Cmd]
getPartCmds ('n', n) = [PushNum (read n)]
getPartCmds ('p', p) = getOps p
getPartCmds ('s', s) = [PushStr (readStr s)]
getPartCmds x = trace ("p " ++ show x) []

data FnCmds = FnCmds [Cmd] [String] [FnCmds] deriving (Show)

getLocalCmds :: [Part] -> Set String -> Set String -> Int -> ([Cmd], [String], Set String)
getLocalCmds [] ids _ _ = ([], [], ids)
getLocalCmds (('b',"()"):ps) ids localIds f = (PushFn f : cs, newCap, newIds)
    where (cs, newCap, newIds) = getLocalCmds ps ids localIds (f + 1)
getLocalCmds (('i',i):ps) ids localIds f =
    if Set.member i ids then
        let (cs, newCap, newIds) = getLocalCmds ps ids localIds f in
            (PushID i : cs, if Set.member i localIds then newCap else i : newCap, newIds)
    else
        let nextIds      = Set.insert i ids
            nextLocalIds = Set.insert i localIds
            (cs, newCap, newIds) = getLocalCmds ps nextIds nextLocalIds f in
            (InitID i : cs, newCap, newIds)
getLocalCmds (p:ps) ids localIds f = (getPartCmds p ++ cs, newCap, newIds)
    where (cs, newCap, newIds) = getLocalCmds ps ids localIds f

getCmds :: Set String -> FnParts -> FnCmds
getCmds ids (FnParts ps sub) = FnCmds cs cap $ map (getCmds newIds) sub
    where (cs, cap, newIds) = getLocalCmds ps ids Set.empty 0

--- Optimization

-- apply ret    => ret to different address (tail-call optimization)
-- push pop     => nothing
-- truthy not   => push nil
-- nil not      => push 1

-- inlining

--- Evaluation

data SikVal = SikNum Double |
              SikChar Char  |
              SikFn [Cmd] (Map String SikVal) [FnCmds] |
              Nil deriving (Show)

toSikChars :: [Char] -> [SikVal]
toSikChars []     = []
toSikChars (c:cs) = SikChar c : toSikChars cs

evalCmd :: [SikVal] -> Cmd -> [SikVal]
evalCmd vs Height = (SikNum $ fromIntegral $ length vs) : vs
evalCmd (v:vs) Pop = vs
evalCmd ((SikNum v) : vs) Lift          -- Error if v is not an integer
    | (v == fromIntegral n) = (vs !! n) : vs where n = truncate v
evalCmd (v:_:Nil:vs) Choose = v : vs
evalCmd (_:v:_:vs)   Choose = v : vs
evalCmd (Nil : vs)       Not = (SikNum 1) : vs
evalCmd (_   : vs)       Not = Nil        : vs
evalCmd (Nil : _   : vs) And = Nil        : vs
evalCmd (_   : Nil : vs) And = Nil        : vs
evalCmd (_   : _   : vs) And = (SikNum 1) : vs
evalCmd (Nil : Nil : vs) Or  = Nil        : vs
evalCmd (_   : _   : vs) Or  = (SikNum 1) : vs
evalCmd (SikNum  vb : SikNum  va : vs) Equal = (if va == vb then SikNum 1 else Nil) : vs
evalCmd (SikChar vb : SikChar va : vs) Equal = (if va == vb then SikNum 1 else Nil) : vs
evalCmd (Nil        : Nil        : vs) Equal = (SikNum 1) : vs
evalCmd (_          : _          : vs) Equal = Nil : vs
evalCmd (SikNum  vb : SikNum  va : vs) Lt = (if va < vb then SikNum 1 else Nil) : vs
evalCmd (SikChar vb : SikChar va : vs) Lt = (if va < vb then SikNum 1 else Nil) : vs
evalCmd (SikNum  vb : SikNum  va : vs) Gt = (if va > vb then SikNum 1 else Nil) : vs
evalCmd (SikChar vb : SikChar va : vs) Gt = (if va > vb then SikNum 1 else Nil) : vs
evalCmd (SikNum vb : SikNum va : vs) Plus  = (SikNum (va + vb))      : vs
evalCmd (SikNum vb : SikNum va : vs) Minus = (SikNum (va - vb))      : vs
evalCmd (SikNum vb : SikNum va : vs) Mult  = (SikNum (va * vb))      : vs
evalCmd (SikNum vb : SikNum va : vs) Div   = (SikNum (va / vb))      : vs
evalCmd (SikNum vb : SikNum va : vs) Mod   = (SikNum (va `mod'` vb)) : vs
evalCmd (SikNum vb : SikNum va : vs) Pow   = (SikNum (va ** vb))     : vs
evalCmd vs (PushNum n) = (SikNum n) : vs
evalCmd vs (PushStr s) = toSikChars (reverse s) ++ vs
evalCmd vs c = trace ("Trace: \tvs " ++ (show $ reverse vs) ++ "\n\t c " ++ (show c) ++ "\n") vs

capFn :: Map String SikVal -> FnCmds -> SikVal
capFn ids (FnCmds cs [] sub) = SikFn cs Map.empty sub
capFn ids (FnCmds cs (c:cap) sub) = SikFn cs (Map.insert c capVal newCap) sub
    where (SikFn _ newCap _) = capFn ids (FnCmds cs cap sub)
          capVal = case Map.lookup c ids of Just x  -> x
                                            Nothing -> Nil

evalFn :: [SikVal] -> Map String SikVal -> SikVal -> IO [SikVal]
evalFn vs _ (SikFn [] _ _) = return vs
evalFn (v:vs) ids (SikFn (Print:cs) cap sub) = do
    putStrLn $ show v
    evalFn (v:vs) ids (SikFn cs cap sub)
evalFn vs ids (SikFn (Input:cs) cap sub) = do
    x <- getChar
    evalFn (SikChar x : vs) ids (SikFn cs cap sub)
evalFn (f:vs) ids (SikFn (Apply:cs) cap sub) = do
    newvs <- evalFn vs ids f
    evalFn newvs ids (SikFn cs cap sub)
evalFn vs ids (SikFn (PushFn i : cs) cap sub) = let new = capFn ids (sub !! i) in
    evalFn (new:vs) ids (SikFn cs cap sub)
evalFn vs ids (SikFn (PushID s : cs) cap sub) = evalFn (new:vs) ids (SikFn cs cap sub)
    where capVal = Map.lookup s cap
          new = case capVal of Just x  -> x
                               Nothing -> case Map.lookup s ids of Just x  -> x
                                                                   Nothing -> Nil
evalFn (v:vs) ids (SikFn (InitID s : cs) cap sub) = let newMap = (Map.insert s v ids) in
    evalFn (v:vs) newMap (SikFn cs cap sub)
evalFn vs ids (SikFn (c:cs) cap sub) = evalFn (evalCmd vs c) ids (SikFn cs cap sub)

evalCmds :: FnCmds -> IO [SikVal]   -- Top-level function can't capture anything.
evalCmds (FnCmds cs [] sub) = evalFn [] Map.empty (SikFn cs Map.empty sub)

-- Debugging

dbgCharTypes :: [Char] -> IO ()
dbgCharTypes str = putStrLn $ (getCharTypes str 'x') ++ "\n" ++ str

dbgPartTypes :: [Char] -> IO ()
dbgPartTypes str = putStrLn $ (getPartTypes $ getCharTypes str 'x')

dbgPartStrs :: [Char] -> IO ()
dbgPartStrs str = let ps = show (getPartStrs str (getCharTypes str 'x')) in
    putStrLn $ ps ++ "\n\n" ++ str

dbgParts :: [Char] -> IO ()
dbgParts = putStrLn . show . getParts

dbgFns :: [Char] -> IO ()
dbgFns = putStrLn . show . parseFns . getParts

dbgCmds :: [Char] -> IO ()
dbgCmds = putStrLn . show . (getCmds Set.empty) . parseFns . getParts

sik :: String -> IO [SikVal]
sik = evalCmds . (getCmds Set.empty) . parseFns . getParts

dbgSik :: [Char] -> IO ()
dbgSik str = do
    stack <- sik str
    putStrLn $ "Result: " ++ show (reverse stack)

main :: IO ()
main = do
    args <- getArgs
    code <-
        if "-f" == args !! 0 then
            readFile $ args !! 1 ++ ".sk"
        else
            return $ unwords args
    dbgSik code