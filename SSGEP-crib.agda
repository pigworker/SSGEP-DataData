module SSGEP-crib where
open import Agda.Primitive

{-

                        Datatypes of Datatypes

                            Conor McBride
                      University of Strathclyde


          Summer School on Generic and Effectful Programming
                         University of Oxford
                              July 2015

-}

{-

                         1. normal functors
                         2. containers

                         3. indexed containers
                         4. levitation

                         5. induction-recursion
                         6. ornaments

-}





{--------------------------------------------------------------------}
{- 0. some stuff we just need to have around                        -}
{--------------------------------------------------------------------}


-- IDENTITY AND COMPOSITION

id : forall {k}{X : Set k} -> X -> X
id x = x

_o_ : forall {i j k}
        {A : Set i}{B : A -> Set j}{C : (a : A) -> B a -> Set k} ->
        (f : {a : A}(b : B a) -> C a b) ->
        (g : (a : A) -> B a) ->
        (a : A) -> C a (g a)
f o g = \ a -> f (g a)


-- SOME SMALL TYPES

data Zero : Set where

magic : forall {l}{A : Set l} -> {{_ : Zero}} -> A
magic {{()}}

record One : Set where constructor <>
open One public

data Two : Set where tt ff : Two


-- SIGMA TYPES GENERALIZE BINARY SUMS AND PRODUCTS

record Sg (S : Set)(T : S -> Set) : Set where
  constructor _,_
  field
    fst : S
    snd : T fst
open Sg public

uncurry :  forall {l}{S : Set}{T : S -> Set}{P : Sg S T -> Set l} ->
      ((s : S)(t : T s) -> P (s , t)) ->
      (p : Sg S T) -> P p
uncurry p (s , t) = p s t

_+_ : Set -> Set -> Set
S + T = Sg Two \ { tt -> S ; ff -> T }

_*_ : Set -> Set -> Set
S * T = Sg S \ _ -> T


-- NUMBERS

data Nat : Set where
  zero  :         Nat
  suc   : Nat ->  Nat

_+Nat_ : Nat -> Nat -> Nat
zero  +Nat y = y
suc x +Nat y = suc (x +Nat y)

{-# BUILTIN NATURAL Nat #-}


-- VECTORS

data Vec (X : Set) : Nat -> Set where
  <>   : Vec X zero
  _,_  : {n : Nat} -> X -> Vec X n -> Vec X (suc n)

_+Vec_ : forall {m n X} -> Vec X m -> Vec X n -> Vec X (m +Nat n)
<>       +Vec ys = ys
(x , xs) +Vec ys = x , xs +Vec ys

infixr 4 _,_ _+Vec_


-- INVERSE IMAGE

data _~_ {S T : Set}(f : S -> T) : T -> Set where
  from : (s : S) -> f ~ f s

chop : forall m n {X} (xs : Vec X (m +Nat n)) -> uncurry (_+Vec_ {m}{n}) ~ xs
chop zero    n xs                                   = from (<> , xs)
chop (suc m) n (x , xs)         with chop m n xs
chop (suc m) n (x , .(xs +Vec ys)) | from (xs , ys) = from ((x , xs) , ys)


-- IDIOM STRUCTURE

vec : forall {n X} -> X -> Vec X n
vec {zero} x  = <>
vec {suc n} x = x , vec x

vapp : forall {n S T} -> Vec (S -> T) n -> Vec S n -> Vec T n
vapp <> ss = <>
vapp (f , fs) (s , ss) = f s , vapp fs ss

record Idiom (F : Set -> Set) : Set1 where
  field
    pure  : forall {X} -> X -> F X
    _<*>_ : forall {S T} -> F (S -> T) -> F S -> F T
  infixl 9 _<*>_

VecIdiom : {n : Nat} -> Idiom \ X -> Vec X n
VecIdiom = record { pure = vec ; _<*>_ = vapp }

idIdiom : Idiom \ X -> X
idIdiom = record { pure = id ; _<*>_ = id }

-- what are Idiom homomorphisms?
--   polymorphic functions  h : forall {X} -> F X -> G X
--   such that
--          pureG x = h (pureF x)
--     h f <*>G h s = h (f <*>F s)

-- what are the laws?
--   pure f <*> pure s = pure (f s)             -- pure is a homomorphism
--   pure id <*> s = s                                -- <*> is a functor
--   (pure _o_ <*> f <*> g) <*> s = f <*> (g <*> s)   -- <*> is a functor
--   f <*> pure s = pure (\ f -> f s) <*> f


-- TRAVERSABILITY

record Traverse (F : Set -> Set) : Set1 where
  field
    traverse : {G : Set -> Set} -> Idiom G ->
               forall {S T} -> (S -> G T) -> F S -> G (F T)

module VECTRAVERSE {G : Set -> Set}(iG : Idiom G){S T : Set}(g : S -> G T) where
  open Idiom iG
  gs : {n : Nat} -> Vec S n -> G (Vec T n)
  gs <> = pure <>
  gs (s , ss) = pure _,_ <*> g s <*> gs ss

VecTraverse : {n : Nat} -> Traverse \ X -> Vec X n
VecTraverse = record { traverse = \ iG g -> VECTRAVERSE.gs iG g }

travMap : forall {F}(tF : Traverse F){X Y} -> (X -> Y) -> F X -> F Y
travMap tF = traverse idIdiom where open Traverse tF

-- laws?
--   traverse is really weaponized distributivity
--   dist : {G : Set -> Set} -> Idiom G -> forall {X} -> F (G X) -> G (F X)
--   traverse iG g = dist o F g
--   Idioms are monoidal with respect to identity and composition
--   distributive laws for F, (G, g) are monoidal with respect to
--     (I, id) and (G , g) o (H , h) = (G o H , G h o g)
--   dist must be a monoid homomorphism
--   dist must be natural in the idiom, ie if h is an idiom homomorphism
--     from G to H, then h o dist = dist o F h


-- MONOIDAL CRUSHING

record Monoid (X : Set) : Set where
  field
    neu : X
    _&_ : X -> X -> X

sumMonoid : Monoid Nat
sumMonoid = record { neu = 0 ; _&_ = _+Nat_ }

MonoidIdiom : {X : Set} -> Monoid X -> Idiom \ _ -> X
MonoidIdiom mX = record { pure = \ _ -> neu ; _<*>_ = _&_ }
  where open Monoid mX

-- and a monoid homomorphism induces an idiom homomorphism

crush : forall {F X Y} -> Traverse F -> Monoid Y -> (X -> Y) -> F X -> Y
crush tF mX = traverse (MonoidIdiom mX) {T = One} where open Traverse tF

-- crush respects monoid homomorphisms

_*Nat_ : Nat -> Nat -> Nat
m *Nat n = crush VecTraverse sumMonoid id (vec {m} n)


-- BOUNDED NUMBERS

_<_ : Nat -> Nat -> Set
m < zero = Zero
zero < suc n = One
suc m < suc n = m < n

record Sub (S : Set)(T : S -> Set) : Set where
  constructor !_
  field
    wit       : S            -- visible
    {{fact}}  : T wit        -- to be inferred from context
open Sub
infix 1 !_

In : Nat -> Set
In n = Sub Nat \ m -> m < n

zeIn : {n : Nat} -> In (suc n)
zeIn = ! zero

suIn : {n : Nat} -> In n -> In (suc n)
suIn (! i) = ! suc i

index : forall {n X} -> Vec X n -> In n -> X
index <>       (! _)      = magic
index (x , xs) (! zero)   = x
index (x , xs) (! suc i)  = index xs (! i)

table : forall {n X} -> (In n -> X) -> Vec X n
table {zero} f = <>
table {suc n} f = f zeIn , table (f o suIn)


{--------------------------------------------------------------------}
{- 1. normal functors                                               -}
{--------------------------------------------------------------------}

record Normal : Set1 where
  constructor _/_
  field
    Shape : Set
    size  : Shape -> Nat
open Normal

[_]N : Normal -> Set -> Set
[ Shape / size ]N X = Sg Shape (Vec X o size)

NormalTraverse : (F : Normal) -> Traverse [ F ]N
NormalTraverse F = record { traverse = \ {iG g (s , xs) ->
  let open Idiom iG in pure (_,_ s) <*> traverse VecTraverse iG g xs} }
  where open Traverse

mapN : forall {F X Y} -> (X -> Y) -> [ F ]N X -> [ F ]N Y
mapN {F} = travMap (NormalTraverse F)


-- CLOSURE PROPERTIES

KN : Set -> Normal
KN A = A / \ a -> 0

IN : Normal
IN = One / \ _ -> 1

SgN : (S : Set)(T : S -> Normal) -> Normal
SgN S T = Sg S (Shape o T) / \ { (s , t) -> size (T s) t }

_+N_ : Normal -> Normal -> Normal
S +N T = SgN Two \ { tt -> S ; ff -> T }

_*N_ : Normal -> Normal -> Normal
(ShS / sizeS) *N (ShT / sizeT) =
  (ShS * ShT) / \ { (s , t) -> sizeS s +Nat sizeT t }

pairN : forall {S T X} -> [ S ]N X * [ T ]N X -> [ S *N T ]N X
pairN ((s , xs) , (t , xs')) = (s , t) , xs +Vec xs'

splitN : forall {S T X}(st : [ S *N T ]N X) -> pairN {S}{T} ~ st
splitN {S}{T} ((s , t) , xs) with chop (size S s) (size T t) xs
splitN ((s , t) , .(xs +Vec ys)) | from (xs , ys) = from ((s , xs) , (t , ys))

_><N_ : Normal -> Normal -> Normal
(ShS / sizeS) ><N (ShT / sizeT) = 
  (ShS * ShT) / \ { (s , t) -> sizeS s *Nat sizeT t }


-- FIXPOINTS

data Tree (F : Normal) : Set where
  <_> : [ F ]N (Tree F) -> Tree F

NAT : Set
NAT = Tree (KN One +N IN)

zeN : NAT
zeN = < ((tt , <>) , <>) >

suN : NAT -> NAT
suN n = < ((ff , <>) , (n , <>)) >


-- closure under composition?

_oN_ : Normal -> Normal -> Normal
F oN G = [ F ]N (Shape G) / crush (NormalTraverse F) sumMonoid (size G)

TravN : {F : Set -> Set} -> Traverse F -> Normal
TravN {F} tF = F One / crush tF sumMonoid \ _ -> 1

ListN : Normal
ListN = Nat / id

[] : forall {X} -> [ ListN ]N X
[] = 0 , <>

_::_ : forall {X} -> X -> [ ListN ]N X -> [ ListN ]N X
x :: (n , xs) = suc n , x , xs

listMonoid : {X : Set} -> Monoid ([ ListN ]N X)
listMonoid = record
  { neu = []
  ; _&_ = \ { (m , xs) (n , ys) -> (m +Nat n) , (xs +Vec ys) }
  } 

contents : forall {F}(tF : Traverse F){X} -> F X -> [ ListN ]N X
contents tF = crush tF listMonoid (\ x -> x :: [])

{-
toNormal :  forall {F}(tF : Traverse F){X} -> F X -> [ TravN tF ]N X
toNormal tF {X} xf = travMap tF _ xf , {!snd (contents tF xf)!}
    -- fst is a monoid homomorphism from lists to numbers
-}


-- NORMAL MORPHISMS

Pos : (F : Normal) -> Shape F -> Set
Pos F = In o size F

record _-N>_ (F G : Normal) : Set where
  field
    planN : (s : Shape F) -> [ G ]N (Pos F s)
open _-N>_

_N$_ : forall {F G} -> F -N> G -> forall {X} -> [ F ]N X -> [ G ]N X
fg N$ (s , xs) = mapN (index xs) (planN fg s)

findPlanN : forall {F G} -> (forall {X} -> [ F ]N X -> [ G ]N X) -> F -N> G
findPlanN fg = record { planN = \ s -> fg (s , table id) }


-- DERIVATIVES OF NORMAL FUNCTORS

_-1_ : (n : Nat) -> In n -> Nat
zero -1 (! _) = magic
suc n -1 _ = n

dN : Normal -> Normal
dN F = Sg (Shape F) (Pos F) / \ { (s , i) -> size F s -1 i }

-- rotate n i
-- 0 .. i-1 i i+1 .. n-1
--  \ .. \  |  |      |
-- ,-~-..-~-'  |      |
-- |  \    \   |      |
-- 0   1    i i+1 .. n-1

rotate : (n : Nat) -> In n -> In n -> In n
rotate 0 (! _) _ = magic
rotate 1 _ _ = ! 0
rotate (suc (suc n)) (! 0)     j     = j
rotate (suc (suc n)) (! suc i) (! 0) = ! 1
rotate (suc (suc n)) (! suc i) (! suc j) with rotate (suc n) (! i) (! j)
rotate (suc (suc n)) (! suc i) (! suc j) | ! 0 = ! 0
rotate (suc (suc n)) (! suc i) (! suc j) | ! k = ! suc k

hack : (n : Nat)(i : In n) -> In n -> In (suc (n -1 i))
hack zero (! i) j = magic
hack (suc n) (! i) j = ! i

plug : (F : Normal) -> (IN *N dN F) -N> F
plug F = record { planN = \ { (<> , s , i) -> s ,
                   table (hack (size F s) i o rotate (size F s) i) } }


{--------------------------------------------------------------------}
{- 2. containers                                                    -}
{--------------------------------------------------------------------}

record Cont : Set1 where
  constructor _<|_
  field
    Sh : Set
    Po : Sh -> Set
open Cont

[_]C : Cont -> Set -> Set
[ S <| P ]C X = Sg S \ s -> P s -> X

record _-C>_ (F G : Cont) : Set where
  field
    planC : (s : Sh F) -> [ G ]C (Po F s)
open _-C>_

_C$_ : forall {F G} -> F -C> G -> forall {X} -> [ F ]C X -> [ G ]C X
fg C$ (s , k) with planC fg s
fg C$ (s , k) | s' , j = s' , k o j

findPlanC : forall {F G} -> (forall {X} -> [ F ]C X -> [ G ]C X) -> F -C> G
findPlanC fg = record { planC = \ s -> fg (s , id) }


-- closure properties

SgC : (S : Set)(T : S -> Cont) -> Cont
SgC S T = Sg S (Sh o T) <| \ { (s , t) -> Po (T s) t }

PiC : (S : Set)(T : S -> Cont) -> Cont
PiC S T = ((s : S) -> Sh (T s)) <| \ { f -> Sg S \ s -> Po (T s) (f s) }

IC : Cont
IC = One <| \ _ -> One

_oC_ : Cont -> Cont -> Cont
F oC G = SgC (Sh F) \ s -> PiC (Po F s) \ p -> G


ListC : Cont
ListC = Nat <| In





-- Hancock's Tensor
{-(-}
_><C_ : Cont -> Cont -> Cont
(S0 <| P0) ><C (S1 <| P1) = (S0 * S1) <| \ { (s0 , s1) -> P0 s0 * P1 s1 }
-- unlike composition, you issue command 1 before you see response 0

MatrixC : Cont
MatrixC = ListC ><C ListC   -- gives rectangular matrices

-- iterating ><C ????
{-)-}









{-(-}
data List (X : Set) : Set where
  <> : List X
  _,_ : X -> List X -> List X

All : {X : Set}(P : X -> Set) -> List X -> Set
All P <> = One
All P (x , xs) = P x * All P xs

_><*C : Cont -> Cont
(S <| P) ><*C = List S <| All P
{-)-}

-- but what's that, then?



{-(-}
_+List_ : forall {X} -> List X -> List X -> List X
<>       +List ys = ys
(x , xs) +List ys = x , (xs +List ys)

chopAll : forall {X P}(xs ys : List X) -> All P (xs +List ys) ->
             All P xs * All P ys
chopAll <> ys ps = <> , ps
chopAll (x , xs) ys (px , ps) with chopAll xs ys ps
chopAll (x , xs) ys (px , ps) | pxs , pys = (px , pxs) , pys

FreeIdiom : (C : Cont) -> Idiom [ C ><*C ]C
FreeIdiom C = record
  { pure = \ x -> <> , \ <> -> x
  ; _<*>_ = \ { (fs , fk) (ss , sk) ->
      (fs +List ss) , \ ps ->
       let pp = chopAll fs ss ps in fk (fst pp) (sk (snd pp)) }
  }
{-)-}




data _o*_ (F : Cont)(X : Set) : Set where
  [_] : X -> F o* X
  <_> : [ F ]C (F o* X) -> F o* X

_o*C : Cont -> Cont
F o*C = (F o* One) <| Leaves where
  Leaves : F o* One -> Set
  Leaves [ <> ] = One
  Leaves < s , k > = Sg (Po F s) \ p -> Leaves (k p)



-- W types

{-(-}
W : (A : Set)(B : A -> Set) -> Set
W A B = (A <| B) o* Zero

So : Two -> Set
So tt = One
So ff = Zero

NatW : Set
NatW = W Two So

zeW : NatW
zeW = < ff , (\ ()) >

suW : NatW -> NatW
suW n = < tt , (\ x -> n) >
{-)-}



dualC : Cont -> Cont
dualC (S <| P) = ((s : S) -> P s) <| \ _ -> S

record _o%_ (F : Cont)(Y : Set) : Set where
  coinductive
  field
    out : Y
    go  : [ F ]C (F o% Y)
open _o%_

_||_ : forall {F X Y} -> F o* X -> dualC F o% Y ->
       (X * [ ListN ]N Y) * (dualC F o% Y)
[ x ]     || server = (x , 0 , <>) , server 
< s , k > || server with out server | go server 
< s , k > || server | y | f , j with k (f s) || j s
< s , k > || server | y | f , j | (x , n , ys) , server'
  = (x , suc n , (y , ys)) , server'


{--------------------------------------------------------------------}
{- 3. indexed containers                                            -}
{--------------------------------------------------------------------}

-- moving into the indexed world

{-(-}
_-:>_ : {I : Set} -> (I -> Set) -> (I -> Set) -> Set
X -:> Y = forall {i} -> X i -> Y i
{-)-}

-- just figure out what "arrows" are, and breathe normally

-- try thinking of (I -> Set) as "predicates on I"
-- mapping each i to the set of proofs that it's acceptable

-- try thinking of (I -> Set) as a bunch of sorts of stuff


-- an indexed container is...
-- ...a container that you've indexed...

{-(-}
record IxCon (I : Set) : Set1 where
  constructor _/_
  field
    Node : Cont
    next : (s : Sh Node)(p : Po Node s) -> I
infixl 3 _/_

-- ...like you plug different sorts of stuff into different "ports"

_<I_ : Set -> Set -> Set1
J <I I = J -> IxCon I       -- for every "peg", give the containers

[_]I : forall {I J} -> J <I I -> (I -> Set) -> (J -> Set)
[ F ]I X j
  =   Sg (Sh (Node (F j))) \ s    -- shape     that's  peg-appropriate
  ->  (p : Po (Node (F j)) s)     -- position  that's  shape-appropriate
  ->  X (next (F j) s p)          -- element   that's  port-appropriate
  where open IxCon
{-)-}
-- or it's a PREDICATE TRANSFORMER taking postconditions to preconditions
-- and it's monotone
{-(-}
mapI : forall {I J}(F : J <I I){X Y} -> (X -:> Y) -> [ F ]I X -:> [ F ]I Y
mapI F h (s , k) = s , h o k
{-)-}


-- what's a morphism?

module MORPH where
  open IxCon
  record _-I>_ {I J}(F G : J <I I) : Set where
    constructor _/_
    field
      planI : forall {j}(s : Sh (Node (F j))) ->
              [ G ]I (\ i -> next (F j) s ~ i) j


-- it's a DEVICE DRIVER from the F interface to the G interface
--   for any initial state j,
--     we translate *valid* F commands to *valid* G commands, and then
--     we translate *valid* G responses which *induce* final state i
--               to *valid* F responses which *ensure* final state i

-- closure properties

-- place for an element
elI : forall {I} -> I -> IxCon I
elI i = IC / \ _ _ -> i

-- choose an A
SgI : forall {I} A -> (A -> IxCon I) -> IxCon I
SgI {I} A B
  =  SgC A (Node o B)
  /  \ { (a , s) p -> next (B a) s p }
  where open IxCon

-- offer the choice of an A
PiI : forall {I} A -> (A -> IxCon I) -> IxCon I
PiI {I} A B
  =  PiC A (Node o B)
  /  \ { f (a , p) -> next (B a) (f a) p }
  where open IxCon

-- reindex
ReI : forall {I H} -> IxCon I -> (I -> H) -> IxCon H
ReI F h = Node / \ s p -> h (next s p)
  where open IxCon F

-- non-goldfish composition of containers
_thenC_ : (F : Cont)(G : (s : Sh F)(p : Po F s) -> Cont) -> Cont
F thenC G = SgC (Sh F) \ s -> PiC (Po F s) \ p -> G s p

-- composition of indexed containers
_oI_ : forall {I J K} -> K <I J -> J <I I -> K <I I
(F oI G) k
  = (Node (F k) thenC \ s p -> Node (G (next (F k) s p)))
  / (\ { (s , s') (p , p') -> next (G (next (F k) s p)) (s' p) p' })
  where open IxCon


-- trees
Child : forall {I J} -> J <I (I + J) -> (I -> Set) -> I + J -> Set
data Mu {I J}(F : J <I (I + J))(X : I -> Set)(j : J) : Set where
  <_> : [ F ]I (Child F X) j -> Mu F X j

Child F X (tt , i) = X i
Child F X (ff , j) = Mu F X j

pattern inl x = tt , x
pattern inr x = ff , x

_<?>_ : forall {l}{P : Two -> Set l} -> P tt -> P ff -> (b : Two) -> P b
(t <?> f) tt = t
(t <?> f) ff = f
infixr 4 _<?>_

VECF : Nat <I (One + Nat)
VECF n = One <| VecSh n / VecNx n where
  VecSh : Nat -> One -> Set
  VecSh zero _ = Zero
  VecSh (suc n) _ = Two
  VecNx : (n : Nat)(s : One) -> VecSh n s -> One + Nat
  VecNx zero    <> = \ _ -> magic
  VecNx (suc n) <> = (inl <>) <?> (inr n)

VEC : Set -> Nat -> Set
VEC X = Mu VECF (\ _ -> X)

vnil : {X : Set} -> VEC X zero
vnil = < <> , (\ _ -> magic) >

vcons : {X : Set}{n : Nat} -> X -> VEC X n -> VEC X (suc n)
vcons x xs = < <> , x <?> xs >



-- free monads on indexed containers
{-(-}
StopOrGo : forall {I} -> (I <I I) -> (I <I (I + I))
StopOrGo F i = SgI Two (elI (inl i) <?> ReI (F i) inr)

_I*_ : forall {I} -> (I <I I) -> (I -> Set) -> (I -> Set)
(F I* X) i = Mu (StopOrGo F) X i

skip :  forall {I}(F : I <I I){X : I -> Set} ->
        X -:> (F I* X)
skip F x = < (tt , <>) , (\ _ -> x) >

extend : forall {I}(F : I <I I){X Y : I -> Set}  ->
        (X -:> (F I* Y)) -> (F I* X) -:> (F I* Y)
extend F k < (tt , <>) , j > = k (j <>)
extend F k < (ff , s) , j > = < (ff , s) , (\ p -> extend F k (j p)) >

bind : forall {I}(F : I <I I){X Y : I -> Set}{i}  ->
        (F I* X) i -> (X -:> (F I* Y)) -> (F I* Y) i
bind F xF k = extend F k xF

semi : forall {I}(F : I <I I){X Y Z : I -> Set} ->
       (X -:> (F I* Y)) -> (Y -:> (F I* Z)) -> (X -:> (F I* Z))
semi F f g = extend F g o f

one : forall {I}(F : I <I I){X : I -> Set} ->
        ([ F ]I X) -:> (F I* X)
one F (s , k) = < (ff , s) , skip F o k >
{-)-}

{-(-}
module CALL {I}(F : I <I I){i} where
  open IxCon (F i)
  call : (s : Sh Node) -> (F I* \ i' -> next s ~ i') i
  call s = one F (s , from)
open CALL

{-)-}

{-(-}
data DoorState : Set where opened closed : DoorState

data DoorCommand : DoorState -> Set where
  knock    : DoorCommand closed
  tryOpen  : DoorCommand closed
  close    : DoorCommand opened

DoorResponse : (i : DoorState) -> DoorCommand i -> Set
DoorResponse .closed knock    = One
DoorResponse .closed tryOpen  = DoorState
DoorResponse .opened close    = One

doorNext : (i : DoorState)(c : DoorCommand i)(r : DoorResponse i c) -> DoorState
doorNext .closed knock r = closed
doorNext .closed tryOpen r = r
doorNext .opened close r = closed
{-)-}

{-(-}
DOOR : DoorState <I DoorState
DOOR i = (DoorCommand i <| DoorResponse i) / doorNext i

data _==_ {l}{X : Set l}(x : X) : X -> Set l where
  refl : x == x

doorFun : (DOOR I* (_==_ closed)) closed
doorFun =
  bind DOOR (call DOOR knock) \ { {.closed} (from <>) ->
  bind DOOR (call DOOR tryOpen) \
    { {.opened} (from opened) ->
      bind DOOR (call DOOR close) \ { {.closed} (from <>) ->
      skip DOOR refl }
    ; {.closed} (from closed) ->
      skip DOOR refl
    }
  }
{-)-}



module SCRIPT {I J}(F : J <I (I + J)) where

  open module Ij (j : J) = IxCon (F j)

  Script : J -> Set
  Script j = Mu F (\ _ -> One) j 

  Path : forall j -> Script j -> Set
  More : forall x -> Child F (\ _ -> One) x -> Set
  Path j < s , k > = Sg (Po (Node j) s) \ p -> More (next j s p) (k p)
  More (tt , i) <>  = One
  More (ff , j) t   = Path j t

  leaf : forall j (t : Script j) -> Path j t -> I
  lead : forall x (c : Child F (\ _ -> One) x) -> More x c -> I
  leaf j < s , k > (p , ps) = lead (next j s p) (k p) ps
  lead (tt , i) <> <> = i
  lead (ff , j) t  ps = leaf j t ps

  MuI : J <I I
  MuI j = Script j <| Path j / leaf j


_-[_] : (X : Set)(x : X) -> Set
X -[ x ] = Sg X \ x' -> x == x' -> Zero

Jacobian : forall {I J} -> J <I I -> (J * I) <I I
Jacobian {I}{J} F (j , i) =  JSh j i <| JPo j i / jIx j i
  where
    open module Ij j = IxCon (F j)
    JSh : J -> I -> Set                   -- peg j; hole at port i
    JSh j i = Sg (Sh (Node j)) \ s -> next j s ~ i
    JPo : forall j i -> JSh j i -> Set    -- anywhere but the hole
    JPo j .(next j s p) (s , from p) = Po (Node j) s -[ p ]
    jIx : forall j i -> (s : JSh j i) -> JPo j i s -> I
    jIx j ._ (s , from _) (p , _) = next j s p


{--------------------------------------------------------------------}
{- 4. levitation                                                    -}
{--------------------------------------------------------------------}

data Desc (I : Set) : Set1 where
  var : (i : I) -> Desc I
  sg : (A : Set)(B : A -> Desc I) -> Desc I
  pi : (A : Set)(B : A -> Desc I) -> Desc I
  d1 : Desc I
  _d*_ : Desc I -> Desc I -> Desc I

[_]d : forall {I} -> Desc I -> (I -> Set) -> Set

[ sg A B ]d  X = Sg A \ a -> [ B a ]d X
[ d1 ]d      X = One
[ A d* B ]d  X = [ A ]d X * [ B ]d X
[ var i ]d   X = X i
[ pi A B ]d  X = (a : A) -> [ B a ]d X

mapD : forall {I}(A : Desc I){X Y : I -> Set}(f : X -:> Y) ->
       [ A ]d X -> [ A ]d Y
mapD (var i)  f x          = f x
mapD (sg A B) f (a , xB)   = a , mapD (B a) f xB
mapD (pi A B) f xB         = \ a -> mapD (B a) f (xB a)
mapD d1       f <>         = <>
mapD (A d* B) f (xA , xB)  = mapD A f xA , mapD B f xB

data Data I (F : I -> Desc I)(i : I) : Set where
  <_> : [ F i ]d (Data I F) -> Data I F i

KD : forall {I} -> Set -> Desc I
KD X = sg X \ _ -> d1

data DL (I : Set) : Set1 where
  <> : DL I
  _,_ : Desc I -> DL I -> DL I

len : forall {I} -> DL I -> Nat
len <> = 0
len (_ , Ds) = suc (len Ds)

get : forall {I}(Ds : DL I) -> In (len Ds) -> Desc I
get <> (! _) = magic
get (D , Ds) (! zero) = D
get (D , Ds) (! suc i) = get Ds (! i)

DataC_:>_$$_ : forall I -> I -> (I -> DL I) -> Set
DataC I :> i $$ Ds = Data I (\ i -> sg (In (len (Ds i))) (get (Ds i))) i
infix 1 DataC_:>_$$_

%% : forall {I} -> I -> DL I
%% i = <>
_//_ : forall {I} -> (I -> Desc I) -> (I -> DL I) -> (I -> DL I)
(D // Ds) i = D i , Ds i
infixr 3 _//_

TY : Set
TY = DataC One :> <> $$
  (\ _ -> d1) //
  (\ _ -> var <> d* var <>) //
  %%

-- baseC : TY
pattern baseC     = < (! 0) , <> >

-- arrC : TY -> TY -> TY
pattern arrC s t  = < (! 1) , s , t >

CX : Set
CX = DataC One :> <> $$
  (\ _ -> d1) // 
  (\ _ -> var <> d* KD TY) //
  %%

-- nilC : CX
pattern nilC = < (! 0) , <> >
-- snocC : CX -> TY -> CX
pattern snocC gam t = < (! 1) , gam , t , <> >

HAS : CX -> TY -> Set
HAS gam t = DataC CX :> gam $$
  (\ { nilC          -> <>
     ; (snocC gam s) -> KD (s == t)
                      , var gam
                      , <>
     ; < (! suc (suc wit)) , y > -> magic 
     })

-- top : forall {gam t} -> HAS (snocC gam t) t
pattern top = < (! 0) , refl , <> >

-- pop : forall {gam s t} -> HAS gam t -> HAS (snocC gam s) t
pattern pop i = < (! 1) , i >

TERM : CX -> TY -> Set
TERM gam t = DataC (CX * TY) :> (gam , t) $$
  uncurry (\ gam t -> KD (HAS gam t)) //
  uncurry (\ gam t -> sg TY \ s -> var (gam , arrC s t) d* var (gam , s)) //
  uncurry REST where
  REST : CX -> TY -> DL (CX * TY)
  REST gam (arrC s t) = var (snocC gam s , t) , <>
  REST _ _ = <>

varC : forall {gam t} -> HAS gam t -> TERM gam t
varC i = < (! 0) , i , <> >

appC : forall {gam s t} -> TERM gam (arrC s t) -> TERM gam s -> TERM gam t
appC f s = < (! 1) , _ , f , s >

lamC : forall {gam s t} -> TERM (snocC gam s) t -> TERM gam (arrC s t)
lamC t = < (! 2) , t >

{-
fooC : forall {gam s} -> TERM gam s
fooC = {!< (! 2) , ? >!}
-}

module DESCICSTUFF {I : Set} where
  SHAPE : Desc I -> Set
  SHAPE A = [ A ]d \ _ -> One
  POS : (A : Desc I) -> SHAPE A -> Set
  POS (var i)  <>      = One
  POS (sg A B) (a , b) = POS (B a) b
  POS (pi A B) f       = Sg A \ a -> POS (B a) (f a)
  POS d1       <>      = Zero
  POS (A d* B) (a , b) = POS A a + POS B b
  NEXT : (A : Desc I)(s : SHAPE A) -> POS A s -> I
  NEXT (var i) <> <> = i
  NEXT (sg A B) (a , s) p = NEXT (B a) s p
  NEXT (pi A B) f (a , p) = NEXT (B a) (f a) p
  NEXT d1 s p = magic
  NEXT (A d* B) (s , _) (tt , p) = NEXT A s p
  NEXT (A d* B) (_ , s) (ff , p) = NEXT B s p
open DESCICSTUFF

DescIC : forall {I J} -> (J -> Desc I) -> J <I I
DescIC {I}{J} D j = (SHAPE (D j) <| POS (D j)) / NEXT (D j) where

toIC : forall {I J}(D : J -> Desc I){X}{j} -> [ D j ]d X -> [ DescIC D ]I X j
toIC {I}{J} D {X}{j} xD = mapD (D j) _ xD , outIC (D j) xD where
  outIC : (A : Desc I)(xD : [ A ]d X)(p : POS A (mapD A _ xD)) -> X (NEXT A (mapD A _ xD) p)
  outIC (var i) x <> = x
  outIC (sg A B) (a , b) p = outIC (B a) b p
  outIC (pi A B) f (a , b) = outIC (B a) (f a) b
  outIC d1 s p = magic
  outIC (A d* B) (a , b) (tt , p) = outIC A a p
  outIC (A d* B) (a , b) (ff , p) = outIC B b p

fromIC : forall {I J}(D : J -> Desc I){X}{j} -> [ DescIC D ]I X j -> [ D j ]d X
fromIC {I}{J} D {X}{j} (s , k) = inIC (D j) s k where
  inIC : (A : Desc I)(s : [ A ]d \ _ -> One) -> ((p : POS A s) -> X (NEXT A s p)) -> [ A ]d X
  inIC (var i) <> k = k <>
  inIC (sg A B) (a , s) k = a , inIC (B a) s k
  inIC (pi A B) f k a = inIC (B a) (f a) (\ p -> k (a , p))
  inIC d1 <> k = <>
  inIC (A d* B) (a , b) k = (inIC A a (\ p -> k (tt , p))) , (inIC B b (\ p -> k (ff , p)))

record SG {l}(S : Set l)(T : S -> Set l) : Set l where
  constructor _,_
  field
    FST : S
    SND : T FST
open SG

record ONE {l} : Set l where
  constructor <>

record UP {l}(X : Set l) : Set (lsuc l) where
  constructor up
  field
    down : X
open UP

data DESC {l}(I : Set l) : Set (lsuc l) where
  var : (i : I) -> DESC I
  sg : (A : Set l)(B : A -> DESC I) -> DESC I
  pi : (A : Set l)(B : A -> DESC I) -> DESC I
  d1 : DESC I
  _d*_ : DESC I -> DESC I -> DESC I

[_]D : forall {l I} -> DESC {l} I -> (I -> Set l) -> Set l

[ sg A B ]D  X = SG A \ a -> [ B a ]D X
[ d1 ]D      X = ONE
[ A d* B ]D  X = SG ([ A ]D X) \ _ -> [ B ]D X
[ var i ]D   X = X i
[ pi A B ]D  X = (a : A) -> [ B a ]D X

data DATA {l} I (F : I -> DESC {l} I)(i : I) : Set l where
  <_> : [ F i ]D (DATA I F) -> DATA I F i

data EnumDESC {l} : Set l where var sg pi d1 ** : EnumDESC
DESCDESC : forall {l}(I : Set l) -> ONE {lsuc l} -> DESC {lsuc l} ONE
DESCDESC I <> = sg EnumDESC (\
  { var -> sg (UP I) (\ _ -> d1)
  ; sg  -> sg (Set _) \ A -> pi (UP A) \ _ -> var <>
  ; pi  -> sg (Set _) \ A -> pi (UP A) \ _ -> var <>
  ; d1  -> d1
  ; **  -> var <> d* var <>
  })

DESC' : forall {l}(I : Set l) -> Set (lsuc l)
DESC' I = DATA ONE (DESCDESC I) <>

var' : forall {l I} -> (i : I) -> DESC' {l} I
var' i = < var , up i , <> >
sg' : forall {l I} -> (A : Set l)(B : A -> DESC' I) -> DESC' {l} I
sg' A B = < sg , A , B o down >
pi' : forall {l I} -> (A : Set l)(B : A -> DESC' I) -> DESC' {l} I
pi' A B = < pi , A , B o down >
d1' : forall {l I} -> DESC' {l} I
d1' = < d1 , <> >
_d*'_ : forall {l I} -> DESC' I -> DESC' I -> DESC' {l} I
A d*' B = < ** , A , B >

BLUE : forall {l}{I} -> DESC' {l} I -> DESC {l} I
BLUE < var , up i , <> > = var i
BLUE < sg , A , B > = sg A \ a -> BLUE (B (up a))
BLUE < pi , A , B > = pi A \ a -> BLUE (B (up a))
BLUE < d1 , <> > = d1
BLUE < ** , A , B > = BLUE A d* BLUE B

DATA' : forall {l} I (F : I -> DESC' {l} I)(i : I) -> Set l
DATA' I F i = DATA I (BLUE o F) i
DESCDESC' : forall {l}(I : Set l) -> ONE {lsuc l} -> DESC' {lsuc l} ONE
DESCDESC' I <> = sg' EnumDESC (\
  { var -> sg' (UP I) (\ _ -> d1')
  ; sg  -> sg' (Set _) \ A -> pi' (UP A) \ _ -> var' <>
  ; pi  -> sg' (Set _) \ A -> pi' (UP A) \ _ -> var' <>
  ; d1  -> d1'
  ; **  -> var' <> d*' var' <>
  })

{-
gimme : forall {l} I -> (BLUE o DESCDESC' {l} I) == DESCDESC {l} I
gimme I = {!refl!}
-}
