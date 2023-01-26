
--------------------------------------------
--                                        --
-- CM20256/CM50262 Functional Programming --
--                                        --
--         Coursework 2020/2021           --
--                                        --
--------------------------------------------


------------------------- Auxiliary functions

find :: (Show a,Eq a) => a -> [(a,b)] -> b
find x [] = error ("find: " ++ show x ++ " not found")
find x ((y,z):zs)
  | x == y    = z
  | otherwise = find x zs


merge :: Ord a => [a] -> [a] -> [a]
merge xs [] = xs
merge [] ys = ys
merge (x:xs) (y:ys)
    | x == y    = x : merge xs ys
    | x <= y    = x : merge xs (y:ys)
    | otherwise = y : merge (x:xs) ys

minus :: Ord a => [a] -> [a] -> [a]
minus xs [] = xs
minus [] ys = []
minus (x:xs) (y:ys)
    | x <  y    = x : minus    xs (y:ys)
    | x == y    =     minus    xs    ys
    | otherwise =     minus (x:xs)   ys


------------------------- Lambda-terms

type Var = String

data Term =
    Variable Var
  | Lambda   Var  Term
  | Apply    Term Term
  deriving Eq


instance Show Term where
  show = f 0
    where
      f i (Variable x) = x
      f i (Lambda x m) = if i /= 0 then "(" ++ s ++ ")" else s where s = "\\" ++ x ++ ". " ++ f 0 m 
      f i (Apply  n m) = if i == 2 then "(" ++ s ++ ")" else s where s = f 1 n ++ " " ++ f 2 m

free :: Term -> [Var]
free (Variable x) = [x]
free (Lambda x n) = free n `minus` [x]
free (Apply  n m) = free n `merge` free m


------------------------- Types

infixr 5 :->

type Atom = String
data Type = At Atom | Type :-> Type
  deriving Eq

instance Show Type where
  show (At a)       = a
  show (At a :-> s) = a ++ " -> " ++ show s
  show    (t :-> s) = "(" ++ show t ++ ") -> " ++ show s


atoms :: [Atom]
atoms = map (:[]) ['a'..'z'] ++ [ a : show i | i <- [1..], a <- ['a'..'z'] ]

t1 :: Type
t1 = At "a" :-> At "b"

t2 :: Type
t2 = (At "c" :-> At "d") :-> At "e"

t3 :: Type
t3 = At "a" :-> At "c" :-> At "c"


------------------------- Assignment 1

occurs :: Atom -> Type -> Bool
occurs x (At s) = s == x
occurs x (y :-> s) =  occurs x y || occurs x s


findAtoms :: Type -> [Atom]
findAtoms (At x) = [x]
findAtoms (y :-> z) = merge (findAtoms y) (findAtoms z)

------------------------- Type substitution

type Sub = (Atom,Type)

s1 :: Sub
s1 = ("a", At "e")

s2 :: Sub
s2 = ("e", At "b" :-> At "c")

s3 :: Sub
s3 = ("c", At "a" :-> At "a")


------------------------- Assignment 2

sub :: Sub -> Type -> Type
sub (x, y) (At a)
  | a == x    = y
  | otherwise = At a
sub (x) (a :-> b) = sub(x) a :-> sub(x) b

subs :: [Sub] -> Type -> Type
subs list (At x)      = foldr sub (At x) list
subs list (x :-> y)   = foldr sub x list :-> foldr sub y list


------------------------- Unification

type Upair = (Type,Type)
type State = ([Sub],[Upair])

u1 :: Upair
u1 = (t1,At "c")

u2 :: Upair
u2 = (At "a" :-> At "a",At "a" :-> At "c")

u3 :: Upair
u3 = (t1,t2)

u4 :: Upair
u4 = (t2,t3)

st1 :: State
st1 = ([],[u1,u2])


------------------------- Assignment 3

sub_u :: Sub -> [Upair] -> [Upair]
sub_u s [(type1, type2)] = [(subs [s] type1, subs [s] type2)]
sub_u s ((type1, type2) : xs) = (subs [s] type1, subs [s] type2) : sub_u s xs
sub_u s [] = []

step :: State -> State
step (a, (typ2, typ3) : ys)
  | typ2 == typ3 = (a, ys)
step (a, (At b, typ3) : ys)
  | occurs b typ3 == False = (((b, typ3) : a), sub_u (b, typ3) ys) 
  | otherwise = error ("Step: atom " ++ b ++ " occurs in " ++ show typ3)
step (a, (typ3, At b) : ys)
  | occurs b typ3 == False = (((b, typ3) : a), sub_u (b, typ3) ys) 
  | otherwise = error ("Step: atom " ++ b ++ " occurs in " ++ show typ3)
step (a, (g :-> h, j :-> k) : ys) = (a, (g, j) : (h, k) : ys)


unify :: [Upair] -> [Sub]
unify u = aux ([], u)
  where
    aux (a, []) = a
    aux (a, b) = aux(step(a, b))


------------------------- Assignment 4

type Context   = [(Var, Type)]
type Judgement = (Context, Term, Type)

data Derivation = 
  Axiom         Judgement
  | Abstraction Judgement Derivation
  | Application Judgement Derivation Derivation

n1 = Apply (Lambda "x" (Variable "x")) (Variable "y")


d1 = Application ([("y",At "a")], n1 , At "a") (
       Abstraction ([("y",At "a")],Lambda "x" (Variable "x"),At "a" :-> At "a") (
         Axiom ([("x",At "a"),("y",At "a")],Variable "x",At "a")
     ) ) (
       Axiom ([("y",At "a")], Variable "y", At "a")
     )

d2 = Application ([("y",At "b")],Apply (Lambda "x" (Apply (Variable "x") (Variable "y"))) (Lambda "z" (Variable "z")),At "a") (
       Abstraction ([("y",At "b")],Lambda "x" (Apply (Variable "x") (Variable "y")),At "c") (
         Application ([("x",At "d"),("y",At "b")],Apply (Variable "x") (Variable "y"),At "e") (
           Axiom ([("x",At "d"),("y",At "b")],Variable "x",At "f")
         ) (
           Axiom ([("x",At "d"),("y",At "b")],Variable "y",At "g")
     ) ) ) (
       Abstraction ([("y",At "b")],Lambda "z" (Variable "z"),At "h") (
         Axiom ([("z",At "i"),("y",At "b")],Variable "z",At "j")
     ) )


conclusion :: Derivation -> Judgement
conclusion (Axiom x) = x
conclusion (Abstraction x y) = x
conclusion (Application x y z) = x

subs_ctx :: [Sub] -> Context -> Context
subs_ctx _ [] = []
subs_ctx x ((a, b) : ys)
  | ys == []  = [(a, subs x b)] 
  | otherwise = (a, subs x b) : subs_ctx x ys

subs_jdg :: [Sub] -> Judgement -> Judgement
subs_jdg x (i, g, h) = ((subs_ctx x i), g, subs x h)

subs_der :: [Sub] -> Derivation -> Derivation
subs_der x (Application a b c) = Application (subs_jdg x a) (subs_der x b) (subs_der x c)
subs_der x (Abstraction y z) = Abstraction (subs_jdg x y) (subs_der x z)
subs_der x (Axiom y) = Axiom (subs_jdg x y)


------------------------- Typesetting derivations


instance Show Derivation where
  show d = unlines (reverse strs)
    where
      (_,_,_,strs) = showD d

      showC :: Context -> String
      showC [] = []
      showC [(x,t)]    = x ++ ": " ++ show t
      showC ((x,t):cx) = x ++ ": " ++ show t  ++ " , " ++ showC cx

      showJ :: Judgement -> String
      showJ ([],n,t) =              "|- " ++ show n ++ " : " ++ show t
      showJ (cx,n,t) = showC cx ++ " |- " ++ show n ++ " : " ++ show t

      showL :: Int -> Int -> Int -> String
      showL l m r = replicate l ' ' ++ replicate m '-' ++ replicate r ' '

      showD :: Derivation -> (Int,Int,Int,[String])
      showD (Axiom j) = (0,k,0,[s,showL 0 k 0]) where s = showJ j; k = length s
      showD (Abstraction j d)   = addrule (showJ j) (showD d)
      showD (Application j d e) = addrule (showJ j) (sidebyside (showD d) (showD e))

      addrule :: String -> (Int,Int,Int,[String]) -> (Int,Int,Int,[String])
      addrule x (l,m,r,xs)
        | k <= m     = (ll,k,rr, (replicate ll ' ' ++ x ++ replicate rr ' ') : showL  l m r  : xs)
        | k <= l+m+r = (ll,k,rr, (replicate ll ' ' ++ x ++ replicate rr ' ') : showL ll k rr : xs)
        | otherwise  = (0,k,0, x : replicate k '-' : [ replicate (-ll) ' ' ++ y ++ replicate (-rr) ' ' | y <- xs])
        where
          k = length x
          i = div (m - k) 2
          ll = l+i
          rr = r+m-k-i

      extend :: Int -> [String] -> [String]
      extend i strs = strs ++ repeat (replicate i ' ')

      sidebyside :: (Int,Int,Int,[String]) -> (Int,Int,Int,[String]) -> (Int,Int,Int,[String])
      sidebyside (l1,m1,r1,d1) (l2,m2,r2,d2)
        | length d1 > length d2 = ( l1 , m1+r1+2+l2+m2 , r2 , [ x ++ "  " ++ y | (x,y) <- zip d1 (extend (l2+m2+r2) d2)])
        | otherwise             = ( l1 , m1+r1+2+l2+m2 , r2 , [ x ++ "  " ++ y | (x,y) <- zip (extend (l1+m1+r1) d1) d2])
        

------------------------- Assignment 5

derive0 :: Term -> Derivation
derive0 x = aux([(var, At "") | var <- free x], x, At "")
  where
    aux :: Judgement -> Derivation
    aux (x, Variable y, z) = Axiom (x, Variable y, z)
    aux (x, Lambda y a, z) = Abstraction (x, Lambda y a, z) (aux ((y, At "") : [(b, u) | (b, u) <- x, b /= y], a, z))
    aux (x, Apply y a, z) = Application (x, Apply y a, z) (aux(x, y, z)) (aux(x, a, z)) 


derive1 :: Term -> Derivation
derive1 term = aux (drop (length (free term)) (tail atoms)) (zip (free term) ([At x | x <- tail atoms]), term, At (head atoms))
  where
    aux :: [Atom] -> Judgement -> Derivation
    aux x (ctxt, Variable var, typ) = Axiom (ctxt, Variable var, typ)
    aux x (ctxt, Lambda var term, typ) = Abstraction (ctxt, Lambda var term, typ) (aux (tail(tail x)) ((var, At (head x)) : [(b, u) | (b, u) <- ctxt, b /= var], term, At (x !! 1)))
    aux x (ctxt, Apply term1 term2, typ) = Application (ctxt, Apply term1 term2, typ) (aux ([ j | (i, j) <- zip [1..] (tail (tail x)), even i]) (ctxt, term1, At (head x))) (aux ([ j | (i, j) <- zip [1..] (tail (tail x)), odd i]) (ctxt, term2, At (x !! 1)))


gtype :: Derivation -> Type
gtype (Application (a, b, typ) c d) = typ
gtype (Abstraction (a, b, typ) c)   = typ
gtype (Axiom (a, b, typ))           = typ

sup :: Derivation -> Type
sup (Application ((y:ys), a, b) c d)    = snd(y)
sup (Abstraction ((y:ys), a, b) c)      = snd(y)
sup (Axiom ((y:ys), (Variable var), typ))
  | fst(y) == var                       = snd(y)
  | otherwise                           = sup (Axiom(ys, (Variable var), typ))
 
upairs :: Derivation -> [Upair]
upairs (Axiom ((x:xs), v, typ))      = [(typ, sup (Axiom ((x:xs), v, typ)))]
upairs (Abstraction (s, v, typ) x)   = [(typ, sup(x) :-> gtype(x))] ++ upairs(x)
upairs (Application (s, v, typ) x y) = [(gtype(x), gtype(y) :-> typ)] ++ upairs(x) ++ upairs(y)

derive :: Term -> Derivation
derive term = subs_der (unify(upairs (derive1 term))) (derive1 term)
