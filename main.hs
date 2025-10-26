import Data.Map as M
import Debug.Trace
import Text.ParserCombinators.ReadP

type Name = String
type Lab  = String

-- dp0 ::= x₀
-- dp1 ::= x₁
-- era ::= &{}
-- sup ::= &L{a,b}
-- dup ::= !x&L=v;t
-- var ::= x
-- lam ::= λx.f
-- app ::= (f x)
data Term
  = Nam String
  | Dp0 String
  | Dp1 String
  | Era
  | Sup Lab Term Term
  | Dup String Lab Term Term
  | Var String
  | Lam String Term
  | App Term Term

-- TODO: implement a Show instance for Terms.
instance Show Term where
  show (Nam k)       = k
  show (Dp0 k)       = k ++ "₀"
  show (Dp1 k)       = k ++ "₁"
  show Era           = "&{}"
  show (Sup l a b)   = "&" ++ l ++ "{" ++ show a ++ "," ++ show b ++ "}"
  show (Dup k l v t) = "!" ++ k ++ "&" ++ l ++ "=" ++ show v ++ ";" ++ show t
  show (Var k)       = k
  show (Lam k f)     = "λ" ++ k ++ "." ++ show f
  show (App f x)     = "(" ++ show f ++ " " ++ show x ++ ")"

data Env = Env
  { var_fresh  :: Int
  , dup_fresh  :: Int
  , var_subst  :: M.Map String Term
  , dp0_subst  :: M.Map String Term
  , dp1_subst  :: M.Map String Term
  } deriving Show

names :: [String]
names = [""] ++ concatMap (\s -> Prelude.map (:s) ['a'..'z']) names

new_env :: Env
new_env = (Env 0 0 M.empty M.empty M.empty)

fresh_var :: Env -> (Env, String)
fresh_var s = (s { var_fresh = var_fresh s + 1 }, names !! (var_fresh s))

fresh_dup :: Env -> (Env, String)
fresh_dup s = (s { dup_fresh = dup_fresh s + 1 }, names !! (dup_fresh s))

subst_var :: Env -> String -> Term -> Env
subst_var s k v = s { var_subst = M.insert k v (var_subst s) }

subst_dp0 :: Env -> String -> Term -> Env
subst_dp0 s k v = s { dp0_subst = M.insert k v (dp0_subst s) }

subst_dp1 :: Env -> String -> Term -> Env
subst_dp1 s k v = s { dp1_subst = M.insert k v (dp1_subst s) }

-- Interactions
-- ============

wnf :: Env -> Term -> (Env,Term)
wnf s (App f x)     = let (s',f') = wnf s f in app s' f' x
wnf s (Dup k l v t) = let (s',v') = wnf s v in dup s' k l v' t
wnf s (Var x)       = var s x
wnf s (Dp0 x)       = dp0 s x
wnf s (Dp1 x)       = dp1 s x
wnf s f             = (s,f)

app :: Env -> Term -> Term -> (Env,Term)
app s (Lam fk ff)    x = app_lam s fk ff x
app s (Sup fl fa fb) x = app_sup s fl fa fb x
app s f              x = (s , App f x)

dup :: Env -> String -> Lab -> Term -> Term -> (Env,Term)
dup s k l (Lam vk vf)    t = dup_lam s k l vk vf t
dup s k l (Sup vl va vb) t = dup_sup s k l vl va vb t
dup s k l v              t = (s , Dup k l v t)

-- (λx.f v)
-- ---------- app-lam
-- x ← v
-- f
app_lam s fx ff v = 
  let s0 = subst_var s fx v in
  wnf s0 ff

-- (&fL{fa,fb} v)
-- -------------------- app-sup
-- ! x &fL = v
-- &fL{(fa x₀),(fa x₁)}
app_sup s fL fa fb v =
  let (s0,x) = fresh_dup s in
  let app0   = App fa (Dp0 x) in
  let app1   = App fb (Dp1 x) in
  let sup    = Sup fL app0 app1 in
  let dup    = Dup x fL v sup in
  (s0 , dup)

-- ! k &L = λvk.vf; t
-- ------------------ dup-lam
-- k₀ ← λx0.g0
-- k₁ ← λx1.g1
-- x0 ← k₀
-- x1 ← k₁
-- ! g &L = vf
-- t
dup_lam s k l vk vf t =
  let (s1, x0) = fresh_var s in
  let (s2, x1) = fresh_var s1 in
  let (s3, g)  = fresh_dup s2 in
  let s4       = subst_var s3 vk (Var x0) in
  let s5       = subst_dp0 s4 k (Lam x0 (Dp0 g)) in
  let s6       = subst_dp1 s5 k (Lam x1 (Dp1 g)) in
  let dup      = Dup g l vf t in
  wnf s6 dup

-- ! k &L = &vL{va,vb}; t
-- ---------------------- dup-sup (==)
-- if l == vL:
--   k₀ ← va
--   k₁ ← vb
--   t
-- else:
--   k₀ ← &vL{a₀,b₀}
--   k₁ ← &vL{a₁,b₁}
--   ! a &L = va
--   ! b &L = vb
--   t
dup_sup s k l vl va vb t
  | l == vl =
    let s0 = subst_dp0 s k va in
    let s1 = subst_dp1 s0 k vb in
    wnf s1 t
  | l /= vl =
    let (s1, a) = fresh_dup s in
    let (s2, b) = fresh_dup s1 in
    let s3      = subst_dp0 s2 k (Sup vl (Dp0 a) (Dp0 b)) in
    let s4      = subst_dp1 s3 k (Sup vl (Dp1 a) (Dp1 b)) in
    let dup     = Dup a l va (Dup b l vb t) in
    wnf s4 dup

var :: Env -> String -> (Env,Term)
var s k = case M.lookup k (var_subst s) of
  Just t  -> wnf (s { var_subst = M.delete k (var_subst s) }) t
  Nothing -> (s, Var k)

dp0 :: Env -> String -> (Env,Term)
dp0 s k = case M.lookup k (dp0_subst s) of
  Just t  -> wnf (s { dp0_subst = M.delete k (dp0_subst s) }) t
  Nothing -> (s, Dp0 k)

dp1 :: Env -> String -> (Env,Term)
dp1 s k = case M.lookup k (dp1_subst s) of
  Just t  -> wnf (s { dp1_subst = M.delete k (dp1_subst s) }) t
  Nothing -> (s, Dp1 k)

nf :: Env -> Term -> (Env,Term)
nf s x = let (s',x') = wnf s x in trace (">> " ++ show x ++ " → " ++ show x') $ go s' x' where
  go s (App f x) = let (s',f') = nf s f in let (s'',x') = nf s' x in (s'', App f' x')
  go s (Lam k f) = let (s',f') = nf s f in (s', Lam k f')
  go s (Var k)   = (s, Var k)

-- Parsing
-- -------

parseTerm :: ReadP Term
parseTerm = do
  skipSpaces
  t <- choice
    [ parseLam
    , parseDup
    , parseApp
    , parseSup
    , parseEra
    , parseVar
    ]
  skipSpaces
  return t

parseApp :: ReadP Term
parseApp = do
  char '('
  skipSpaces
  ts <- many1 (parseAtom <* skipSpaces)
  char ')'
  case ts of
    (t1:t2:rest) -> return (Prelude.foldl App t1 (t2:rest))
    _            -> pfail

parseAtom :: ReadP Term
parseAtom = choice
  [ parseLam
  , parseDup
  , parseSup
  , parseEra
  , parseVar
  , parseApp
  ]

parseLam :: ReadP Term
parseLam = do
  choice [char 'λ', char '\\']
  skipSpaces
  k <- parseIdent
  skipSpaces
  char '.'
  skipSpaces
  body <- parseTerm
  return $ Lam k body

parseDup :: ReadP Term
parseDup = do
  char '!'
  k <- parseIdent
  skipSpaces
  char '&'
  l <- parseIdent
  skipSpaces
  char '='
  skipSpaces
  v <- parseTerm
  skipSpaces
  char ';'
  skipSpaces
  t <- parseTerm
  return $ Dup k l v t

parseSup :: ReadP Term
parseSup = do
  char '&'
  l <- parseIdent
  skipSpaces
  char '{'
  skipSpaces
  a <- parseTerm
  skipSpaces
  char ','
  skipSpaces
  b <- parseTerm
  skipSpaces
  char '}'
  return $ Sup l a b

parseEra :: ReadP Term
parseEra = string "&{}" >> return Era

parseVar :: ReadP Term
parseVar = do
  k <- parseIdent
  choice
    [ string "₀"  >> return (Dp0 k)
    , string "₁"  >> return (Dp1 k)
    , string "_0" >> return (Dp0 k)
    , string "_1" >> return (Dp1 k)
    , return (Var k)
    ]

parseIdent :: ReadP String
parseIdent = many1 (satisfy (\c -> c `elem` (['a'..'z'] ++ ['A'..'Z'] ++ ['0'..'9'])))

readTerm :: String -> Term
readTerm s = case readP_to_S (parseTerm <* eof) s of
  [(t, "")] -> t
  _         -> error "bad-parse"

-- Main
-- ====

main :: IO ()
main = do
  let not = readTerm "λNx. λNt. λNf. (Nx Nf Nt)"
  print not


-- This parser didn't work. Rewrite it and make it right.
-- Remember: there is no parseParen. there is just a parseApp that handles multiple arguments

-- Rewritten parser






















