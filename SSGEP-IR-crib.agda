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

record FAM (I : Set1) : Set1 where
  constructor _&_
  field
    RawData  : Set
    Meaning  : RawData -> I
open FAM

IF : forall {I} -> I -> FAM I
IF i     = One
         & \ _ -> i

KF : forall A -> FAM (UP A)
KF A     = A
         & up

SgF : forall {I : Set1} {J : I -> Set1}
             (S : FAM I)(T : (i : I) -> FAM (J i))
        -> FAM (SG I J)
SgF S T  = (Sg (RawData S) \ s -> RawData (T (Meaning S s)))
         & \ { (s , t) ->
           let i = Meaning S     s
               j = Meaning (T i) t
           in  i , j }

PiF : forall (A : Set)   {J : A -> Set1}
                         (T : (a : A) -> FAM (J a))
        -> FAM ((a : A) -> J a)
PiF A T  = ((a : A) -> RawData (T a))
         & \ { f a -> Meaning (T a) (f a) }

data IR (I : Set1) : Set1          -- descriptions of IR sets
INFO : forall {I} -> IR I -> Set1    -- the information you can get from a set

data IR I where
  rec : IR I
  kon : Set -> IR I
  pi  : (A : Set)(T : A -> IR I) -> IR I
  sg  : (S : IR I)(T : INFO S -> IR I) -> IR I

INFO {I} rec      = I
INFO     (kon A)  = UP A
INFO     (pi A T) = (a : A) -> INFO (T a)
INFO     (sg S T) = SG (INFO S) \ s -> INFO (T s)

NODE : forall {I}(T : IR I) -> FAM I -> FAM (INFO T)
NODE rec      F = F
NODE (kon A)  F = KF A
NODE (pi A T) F = PiF A \ a -> NODE (T a) F
NODE (sg S T) F = SgF (NODE S F) \ i -> NODE (T i) F

record IRDesc (I : Set1) : Set1 where
  constructor _/_
  field
    Structure   : IR I
    Process     : INFO Structure -> I
open IRDesc

{-
data MU {I}(D : IRDesc I) : Set
[_]M : forall {I D} -> MU {I} D -> I
{-
MUFAM : forall {I}(D : IRDesc I) -> FAM I
MUFAM D = MU D & [_]M

data MU {I} D where
  <_> : RawData (NODE (Structure D) (MUFAM D)) -> MU D

[_]M {I}{D} < d > = Process D (Meaning (NODE (Structure D) (MUFAM D)) d)
-}

NODEMU : forall {I}(T : IR I)(D : IRDesc I) -> FAM (INFO T)

data MU {I} D where
  <_> : RawData (NODEMU (Structure D) D) -> MU D

[_]M {I}{D} < d > = Process D (Meaning (NODEMU (Structure D) D) d)

NODEMU rec      D = MU D & \ d -> [ d ]M
NODEMU (kon A)  D = KF A
NODEMU (pi A T) D = PiF A \ a -> NODEMU (T a) D
NODEMU (sg S T) D = SgF (NODEMU S D) \ i -> NODEMU (T i) D
-}

data MU {I}(D : IRDesc I) : Set
[_]M : forall {I D} -> MU {I} D -> I
NodeMU   : forall {I}(T : IR I)(D : IRDesc I) ->
              Set
decodeMU  : forall {I}(T : IR I)(D : IRDesc I) ->
              NodeMU T D -> INFO T

data MU {I} D where
  <_> : NodeMU (Structure D) D -> MU D

[_]M {I}{D} < d > = Process D (decodeMU (Structure D) D d) where
NodeMU rec      D = MU D
NodeMU (kon A)  D = A
NodeMU (pi A T) D = (a : A) -> NodeMU (T a) D
NodeMU (sg S T) D = Sg (NodeMU S D) \ s -> NodeMU (T (decodeMU S D s)) D
decodeMU rec      D x       = [ x ]M
decodeMU (kon A)  D a       = up a
decodeMU (pi A T) D f       = \ a -> decodeMU (T a) D (f a)
decodeMU (sg S T) D (s , t) = s' , t' where
  s' = decodeMU S      D s
  t' = decodeMU (T s') D t
