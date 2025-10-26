import Data.Char (isAlphaNum)
import qualified Data.Map as M
import Debug.Trace
import Text.ParserCombinators.ReadP
import Data.Function (fix)

type Lab   = String
type Name  = String
type Map a = M.Map String a

-- dp0 ::= x₀
-- dp1 ::= x₁
-- era ::= &{}
-- sup ::= &L{a,b}
-- dup ::= !x&L=v;t
-- var ::= x
-- lam ::= λx.f
-- app ::= (f x)
-- nam ::= name
-- dry ::= (name arg)
data Term
  = Nam Name
  | Var Name
  | Dp0 Name
  | Dp1 Name
  | Era
  | Sup Lab Term Term
  | Dup Name Lab Term Term
  | Lam Name Term
  | Abs Name Term
  | Dry Term Term
  | App Term Term
  -- deriving Show

instance Show Term where
  show (Nam k)       = "^" ++ k
  show (Dry f x)     = "(" ++ show f ++ " " ++ show x ++ ")"
  show (Var k)       = k
  show (Dp0 k)       = k ++ "₀"
  show (Dp1 k)       = k ++ "₁"
  show Era           = "&{}"
  show (Sup l a b)   = "&" ++ l ++ "{" ++ show a ++ "," ++ show b ++ "}"
  show (Dup k l v t) = "!" ++ k ++ "&" ++ l ++ "=" ++ show v ++ ";" ++ show t
  show (Lam k f)     = "λ" ++ k ++ "." ++ show f
  show (Abs k f)     = "λ" ++ k ++ "." ++ show f
  show (App f x)     = "(" ++ show f ++ " " ++ show x ++ ")"

-- Environment
-- ===========

data Env = Env
  { var_new :: Int
  , dup_new :: Int
  , var_map :: Map Term
  , dp0_map :: Map Term
  , dp1_map :: Map Term
  , dup_map :: Map (Lab,Term)
  } deriving Show

names :: String -> [String]
names abc = fix $ \x -> [""] ++ concatMap (\s -> Prelude.map (:s) abc) x

new_env :: Env
new_env = Env 0 0 M.empty M.empty M.empty M.empty

fresh_var :: Env -> (Env, String)
fresh_var s = (s { var_new = var_new s + 1 }, "$" ++ (names ['a'..'z']) !! (var_new s + 1))

fresh_dup :: Env -> (Env, String)
fresh_dup s = (s { dup_new = dup_new s + 1 }, "$" ++ (names ['A'..'Z']) !! (dup_new s + 1))

subst_var :: Env -> String -> Term -> Env
subst_var s k v = s { var_map = M.insert k v (var_map s) }

subst_dp0 :: Env -> String -> Term -> Env
subst_dp0 s k v = s { dp0_map = M.insert k v (dp0_map s) }

subst_dp1 :: Env -> String -> Term -> Env
subst_dp1 s k v = s { dp1_map = M.insert k v (dp1_map s) }

delay_dup :: Env -> String -> (Lab,Term) -> Env
delay_dup s k v = s { dup_map = M.insert k v (dup_map s) }

-- Evaluation
-- ==========

wnf :: Env -> Term -> (Env,Term)
wnf s (App f x)     = let (s',f') = wnf s f in app s' f' x
wnf s (Dup k l v t) = wnf (delay_dup s k (l,v)) t
wnf s (Var x)       = var s x
wnf s (Dp0 x)       = dp0 s x
wnf s (Dp1 x)       = dp1 s x
wnf s f             = (s,f)

app :: Env -> Term -> Term -> (Env,Term)
app s (Nam fk)       x = app_nam s fk x
app s (Dry df dx)    x = app_dry s df dx x
app s (Lam fk ff)    x = app_lam s fk ff x
app s (Sup fl fa fb) x = app_sup s fl fa fb x
app s f              x = (s , App f x)

dup :: Env -> String -> Lab -> Term -> Term -> (Env,Term)
dup s k l (Nam vk)       t = dup_nam s k l vk t
dup s k l (Dry vf vx)    t = dup_dry s k l vf vx t
dup s k l (Lam vk vf)    t = dup_lam s k l vk vf t
dup s k l (Sup vl va vb) t = dup_sup s k l vl va vb t
dup s k l v              t = (s , Dup k l v t)

-- Interactions
-- ============

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

-- (fk v)
-- ------ app-nam
-- (fk v)
app_nam s fk v = (s, Dry (Nam fk) v)

-- ((df dx) v)
-- ----------- app-dry
-- ((df dx) v)
app_dry s df dx v = (s, Dry (Dry df dx) v)

-- ! k &L = λvk.vf; t
-- ------------------ dup-lam
-- k₀ ← λx0.g0
-- k₁ ← λx1.g1
-- vk ← &L{x0,x1}
-- ! g &L = vf
-- t
dup_lam s k l vk vf t =
  let (s1, x0) = fresh_var s in
  let (s2, x1) = fresh_var s1 in
  let (s3, g)  = fresh_dup s2 in
  let s4       = subst_dp0 s3 k  (Lam x0 (Dp0 g)) in
  let s5       = subst_dp1 s4 k  (Lam x1 (Dp1 g)) in
  let s6       = subst_var s5 vk (Sup l (Var x0) (Var x1)) in
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

-- ! k &L = vk; t
-- -------------- dup-nam
-- k₀ ← vk
-- k₁ ← vk
-- t
dup_nam s k l vk t =
  let s0 = subst_dp0 s  k (Nam vk) in
  let s1 = subst_dp1 s0 k (Nam vk) in
  wnf s1 t

-- ! k &L = (vf vx); t
-- --------------------- dup-dry
-- ! f &L = vf
-- ! x &L = vx
-- k₀ ← (f₀ x₀)
-- k₁ ← (f₁ x₁)
-- t
dup_dry s k l vf vx t =
  let (s1, f) = fresh_dup s in
  let (s2, x) = fresh_dup s1 in
  let s3      = subst_dp0 s2 k (Dry (Dp0 f) (Dp0 x)) in
  let s4      = subst_dp1 s3 k (Dry (Dp1 f) (Dp1 x)) in
  let dup     = Dup f l vf (Dup x l vx t) in
  wnf s4 dup

-- x
-- ------------ var
-- var_map[x]
var :: Env -> String -> (Env,Term)
var s k = case M.lookup k (var_map s) of
  Just t  -> wnf (s { var_map = M.delete k (var_map s) }) t
  Nothing -> (s, Var k)

-- x₀
-- ---------- dp0
-- dp0_map[x]
dp0 :: Env -> String -> (Env,Term)
dp0 s k = case M.lookup k (dp0_map s) of
  Just t  -> wnf (s { dp0_map = M.delete k (dp0_map s) }) t
  Nothing -> case M.lookup k (dup_map s) of
    Just (l,v) -> let (s',v') = wnf (s { dup_map = M.delete k (dup_map s) }) v in dup s' k l v' (Dp0 k)
    Nothing    -> (s , Dp0 k)

-- x₁
-- ---------- dp1
-- dp1_map[x]
dp1 :: Env -> String -> (Env,Term)
dp1 s k = case M.lookup k (dp1_map s) of
  Just t  -> wnf (s { dp1_map = M.delete k (dp1_map s) }) t
  Nothing -> case M.lookup k (dup_map s) of
    Just (l,v) -> let (s',v') = wnf (s { dup_map = M.delete k (dup_map s) }) v in dup s' k l v' (Dp1 k)
    Nothing    -> (s , Dp1 k)

-- Normalization
-- =============

nf :: Env -> Term -> (Env,Term)
nf s x = let (s0,x0) = wnf s x in trace ("nf: " ++ show x ++ " | " ++ show s ++ "\n→→→ " ++ show x0 ++ " | " ++ show s0) $ go s0 x0 where
  go s (Nam k)       = (s, Nam k)
  go s (Dry f x)     = let (s0,f0) = nf s f in let (s1,x0) = nf s0 x in (s1, Dry f0 x0)
  go s (Var k)       = (s, Var k)
  go s (Dp0 k)       = (s, Dp0 k)
  go s (Dp1 k)       = (s, Dp1 k)
  go s Era           = (s, Era)
  go s (Sup l a b)   = let (s0,a0) = nf s a in let (s1,b0) = nf s0 b in (s1, Sup l a0 b0)
  go s (Dup k l v t) = let (s0,v0) = nf s v in let (s1,t0) = nf s0 t in (s1, Dup k l v0 t0)
  go s (Lam k f)     = let (s0,f0) = nf (subst_var s k (Nam k)) f in (s0, Lam k f0)
  go s (Abs k f)     = let (s0,f0) = nf s f in (s0, Abs k f0)
  go s (App f x)     = let (s0,f0) = nf s f in let (s1,x0) = nf s0 x in (s1, App f0 x0)

-- Parsing
-- =======

lexeme :: ReadP a -> ReadP a
lexeme p = skipSpaces *> p

name :: ReadP String
name = lexeme parse_nam

parse_term :: ReadP Term
parse_term = lexeme $ choice
  [ parse_lam
  , parse_dup
  , parse_app
  , parse_sup
  , parse_era
  , parse_var
  ]

parse_app :: ReadP Term
parse_app = do
  lexeme (char '(')
  ts <- many1 parse_term
  lexeme (char ')')
  case ts of
    (t:rest) -> return (Prelude.foldl App t rest)
    _        -> pfail

parse_lam :: ReadP Term
parse_lam = do
  lexeme (choice [char 'λ', char '\\'])
  k <- name
  lexeme (char '.')
  body <- parse_term
  return $ Lam k body

parse_dup :: ReadP Term
parse_dup = do
  lexeme (char '!')
  k <- name
  lexeme (char '&')
  l <- name
  lexeme (char '=')
  v <- parse_term
  lexeme (char ';')
  t <- parse_term
  return $ Dup k l v t

parse_sup :: ReadP Term
parse_sup = do
  lexeme (char '&')
  l <- name
  lexeme (char '{')
  a <- parse_term
  lexeme (char ',')
  b <- parse_term
  lexeme (char '}')
  return $ Sup l a b

parse_era :: ReadP Term
parse_era = lexeme (string "&{}") >> return Era

parse_var :: ReadP Term
parse_var = do
  k <- name
  choice
    [ string "₀"  >> return (Dp0 k)
    , string "₁"  >> return (Dp1 k)
    , return (Var k)
    ]

-- Names should not swallow Unicode subscripts so constructs like F₀ are parsed as Dp0/Dp1.
isNameChar :: Char -> Bool
isNameChar c = isAlphaNum c && not (isSubscriptDigit c)

isSubscriptDigit :: Char -> Bool
isSubscriptDigit c = c >= '₀' && c <= '₉'

parse_nam :: ReadP String
parse_nam = munch1 isNameChar

read_term :: String -> Term
read_term s = case readP_to_S (parse_term <* skipSpaces <* eof) s of
  [(t, "")] -> t
  _         -> error "bad-parse"

-- Main
-- ====

main :: IO ()
main = do
  let not     = read_term "! F &L = λNx. λNt. λNf. ((Nx Nf) Nt); &L{F₀,F₁}"
  let (s0,f0) = nf new_env not
  -- let (s1,f1) = nf s0 f0
  print $ s0
  print $ f0
  -- print $ s1
  -- print $ f1


































