module SSGEP-IR-crib where

open import Agda.Primitive
open import SSGEP-crib

{- A sudden immersion in induction-recursion. -}

-- a wha-what?

-- standard example -- FreshList

_=Nat_ : Nat -> Nat -> Two
zero =Nat zero = tt
zero =Nat suc y = ff
suc x =Nat zero = ff
suc x =Nat suc y = x =Nat y

not : Two -> Two
not tt = ff
not ff = tt

_&&_ : Two -> Two -> Two
tt && b = b
ff && b = ff

data Fresh : Set
_%_ : Nat -> Fresh -> Two

data Fresh where
  <>  : Fresh
  _,_ : (x : Nat)(xs : Fresh){{_ : So (x % xs)}} -> Fresh

y % <> = tt
y % (x , xs) = not (y =Nat x) && (y % xs)

try : Fresh
try = 1 , 2 , 3 , 4 , 5 , <>

{-+}
fry : Fresh
fry = 1 , 2 , 3 , 4 , 3 , <>
{+-}

-- so we can define datatypes and functions mutually
-- the function gives a helpful interpretation of the
-- data, just in time.

-- could write

data FreshI : (Nat -> Two) -> Set where
  <>  : FreshI \ _ -> tt
  _,_ : forall {f}(x : Nat)(xs : FreshI f){{_ : So (f x)}} ->
        FreshI \ y -> not (y =Nat x) && f y

try' : Sg _ FreshI
try' = _ , 1 , 2 , 3 , 4 , 5 , <>

{-+}
fry' : Sg _ FreshI
fry' = _ , 1 , 2 , 3 , 4 , 3 , <>
{+-}

-- So, when the "decoding" is *small*, you can turn it into an index.
-- We call that "Small IR" and it's handy but adds no real power.
-- Coq doesn't let you do IR, but you can fake up *Small* IR by indexing.

-- What can you do with *Large* IR?

data Uni0 : Set
El0 : Uni0 -> Set

data Uni0 where
  nat : Uni0
  pi  : (S : Uni0)(T : El0 S -> Uni0) -> Uni0

El0 nat = Nat
El0 (pi S T) = (s : El0 S) -> El0 (T s)

-- compare with

{-+}
data Rep : Set -> Set where
  nat : Rep Nat
  pi  : forall {S}{T : S -> Set} ->
        Rep S -> ((s : S) -> Rep (T s)) -> Rep ((s : S) -> T s)
{+-}

-- type theory in a bottle

data NextU (U : Set)(El : U -> Set) : Set
NextEl : forall {U}{El} -> NextU U El -> Set

data NextU U El where
  enum : Nat -> NextU U El
  pi sg ww : (S : NextU U El)(T : NextEl S -> NextU U El) -> NextU U El
  uu : NextU U El
  el : U -> NextU U El

NextEl (enum n) = In n
NextEl (pi S T) = (s : NextEl S) -> NextEl (T s)
NextEl (sg S T) = Sg (NextEl S) \ s -> NextEl (T s)
NextEl (ww S T) = W (NextEl S) \ s -> NextEl (T s)
NextEl {U = U} uu = U
NextEl {El = El} (el X) = El X

SET : Nat -> Set
EL  : (n : Nat) -> SET n -> Set
SET' : Nat -> Set
EL'  : (n : Nat) -> SET' n -> Set

SET n = NextU  (SET' n) (EL' n)
EL  n = NextEl

SET' zero     = Zero
SET' (suc n)  = SET n
EL'  zero     X = magic
EL'  (suc n)  X = EL n X

-- let's put induction-recursion in a bottle

data IR (I : Set1) : Set1          -- descriptions of IR sets
INFO : forall I -> IR I -> Set1    -- the information you can get from a set

data IR I where
  rec : IR I
  kon : Set -> IR I
  pi  : (A : Set)(T : A -> IR I) -> IR I
  sg  : (S : IR I)(T : INFO I S -> IR I) -> IR I

INFO I rec      = I
INFO I (kon A)  = UP A
INFO I (pi A T) = (a : A) -> INFO I (T a)
INFO I (sg S T) = SG (INFO I S) \ s -> INFO I (T s)

Node   : forall {I}(T : IR I) ->
           (X : Set)(d : X -> I) -> Set
decode : forall {I}(T : IR I) ->
           (X : Set)(d : X -> I) -> Node T X d -> INFO I T
Node rec X d = X
Node (kon A) X d = A
Node (pi A T) X d = (a : A) -> Node (T a) X d
Node (sg S T) X d = Sg (Node S X d) \ s -> Node (T (decode S X d s)) X d
decode rec X d x = d x
decode (kon A) X d a = up a
decode (pi A T) X d f = \ a -> decode (T a) X d (f a)
decode (sg S T) X d (s , t) = s' , decode (T s') X d t where
  s' = decode S X d s
