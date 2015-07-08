module SSGEP where
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

{-(-}
id : forall {k}{X : Set k} -> X -> X
id x = x

_o_ : forall {i j k}
        {A : Set i}{B : A -> Set j}{C : (a : A) -> B a -> Set k} ->
        (f : {a : A}(b : B a) -> C a b) ->
        (g : (a : A) -> B a) ->
        (a : A) -> C a (g a)
f o g = \ a -> f (g a)
{-)-}


-- SOME SMALL TYPES

{-(-}
data Zero : Set where

magic : forall {l}{A : Set l} -> {{_ : Zero}} -> A
magic {{()}}

record One : Set where constructor <>
open One public

data Two : Set where tt ff : Two
{-)-}


-- SIGMA TYPES GENERALIZE BINARY SUMS AND PRODUCTS

{-(-}
record Sg (S : Set)(T : S -> Set) : Set where
  constructor _,_
  field
    fst : S
    snd : T fst
open Sg public
infixr 4 _,_

uncurry :  forall {l}{S : Set}{T : S -> Set}{P : Sg S T -> Set l} ->
      ((s : S)(t : T s) -> P (s , t)) ->
      (p : Sg S T) -> P p
uncurry p (s , t) = p s t

_+_ : Set -> Set -> Set
S + T = Sg Two \ { tt -> S ; ff -> T }

_*_ : Set -> Set -> Set
S * T = Sg S \ s -> T
{-)-}


-- NUMBERS

{-(-}
data Nat : Set where
  zero  :         Nat
  suc   : Nat ->  Nat

_+Nat_ : Nat -> Nat -> Nat
zero  +Nat y = y
suc x +Nat y = suc (x +Nat y)  -- ask Agsy for a laugh

{-# BUILTIN NATURAL Nat #-}
{-)-}


-- VECTORS

{-(-}
data Vec (X : Set) : Nat -> Set where
  <>   : Vec X zero
  _,_  : {n : Nat} -> X -> Vec X n -> Vec X (suc n)

_+Vec_ : forall {m n X} -> Vec X m -> Vec X n -> Vec X (m +Nat n)
<> +Vec ys = ys
(x , xs) +Vec ys = x , xs +Vec ys  -- ask Agsy for a laugh

infixr 4 _+Vec_
{-)-}

-- INVERSE IMAGE

{-(-}
data _~_ {S T : Set}(f : S -> T) : T -> Set where
  from : (s : S) -> f ~ f s

chop : forall m n {X} (xs : Vec X (m +Nat n)) -> uncurry (_+Vec_ {m}{n}) ~ xs
chop zero n xs = from ((<> , xs))
chop (suc m) n (x , xs) with chop m n xs
chop (suc m) n (x , .(xs +Vec ys)) | from (xs , ys) = from ((x , xs) , ys)
{-)-}


-- IDIOM STRUCTURE

{-(-}
vec : forall {n X} -> X -> Vec X n
vec {zero} x = <>
vec {suc x} x₁ = x₁ , vec x₁

vapp : forall {n S T} -> Vec (S -> T) n -> Vec S n -> Vec T n
vapp <> ss = <>
vapp (x , x₁) (x₂ , x₃) = x x₂ , vapp x₁ x₃

record Idiom (F : Set -> Set) : Set1 where
  field
    pure  : forall {X} -> X -> F X
    _<*>_ : forall {S T} -> F (S -> T) -> F S -> F T
  infixl 9 _<*>_

VecIdiom : {n : Nat} -> Idiom \ X -> Vec X n
VecIdiom = record { pure = vec ; _<*>_ = vapp }

idIdiom : Idiom \ X -> X
idIdiom = record { pure = id ; _<*>_ = id }
{-)-}

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

{-(-}
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
{-)-}

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

{-(-}
record Monoid (X : Set) : Set where
  field
    neu : X
    _&_ : X -> X -> X

sumMonoid : Monoid Nat
sumMonoid = record { neu = 0 ; _&_ = _+Nat_ }

MonoidIdiom : {X : Set} -> Monoid X -> Idiom \ _ -> X
MonoidIdiom mX = record { pure = \ _ -> neu ; _<*>_ = _&_ }
  where open Monoid mX

-- and a monoid homomorphism induces an idiom homomorphism...

crush : forall {F X Y} -> Traverse F -> Monoid Y -> (X -> Y) -> F X -> Y
crush tF mX = traverse (MonoidIdiom mX) {T = Zero} where open Traverse tF

-- ... so crush respects monoid homomorphisms
{-)-}

-- go forth and multiply

{-(-}
_*Nat_ : Nat -> Nat -> Nat
m *Nat n = crush VecTraverse sumMonoid id (vec {m} n)

mulMonoid : Monoid Nat
mulMonoid = record { neu = 1 ; _&_ = _*Nat_ }
{-)-}


-- BOUNDED NUMBERS

{-(-}
record Sub (S : Set)(T : S -> Set) : Set where
  constructor !_
  field
    wit       : S            -- visible
    {{fact}}  : T wit        -- to be inferred from context
open Sub
infix 1 !_

_<_ : Nat -> Nat -> Set
m < zero = Zero
zero < suc n = One
suc m < suc n = m < n

In : Nat -> Set
In n = Sub Nat \ m -> m < n
{-)-}

{-(-}
zeIn : {n : Nat} -> In (suc n)
zeIn = ! zero

suIn : {n : Nat} -> In n -> In (suc n)
suIn (! i) = ! suc i
{-)-}

{-(-}
index : forall {n X} -> Vec X n -> In n -> X
index <> (! _) = magic
index (x , xs) (! zero) = x
index (x , xs) (! suc i) = index xs (! i)

table : forall {n X} -> (In n -> X) -> Vec X n
table {zero} f = <>
table {suc n} f = f zeIn , table (f o suIn)

-- exercise, show that every vector is in the inverse image of table
{-)-}

{--------------------------------------------------------------------}
{- 1. normal functors                                               -}
{--------------------------------------------------------------------}

{-(-}
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
{-)-}


-- CLOSURE PROPERTIES

{-(-}
KN : Set -> Normal
KN A = A / \ a -> 0

IN : Normal
IN = One / \ _ -> 1

SgN : (S : Set)(T : S -> Normal) -> Normal
SgN S T = (Sg S (Shape o T)) / (\ { (s , t) -> size (T s) t })

_+N_ : Normal -> Normal -> Normal
S +N T = SgN Two \ { tt -> S ; ff -> T }

_*N_ : Normal -> Normal -> Normal
(ShS / sizeS) *N (ShT / sizeT) =
  (ShS * ShT) / (\ { (s , t) -> sizeS s +Nat sizeT t }) 

pairN : forall {S T X} -> [ S ]N X * [ T ]N X -> [ S *N T ]N X
pairN ((s , xs) , (t , xs')) = (s , t) , (xs +Vec xs')

splitN : forall {S T X}(st : [ S *N T ]N X) -> pairN {S}{T} ~ st
splitN {Shape / sizeS} {Shape₁ / sizeT} ((s , t) , xs) with chop (sizeS s) (sizeT t) xs
splitN {Shape / sizeS} {Shape₁ / sizeT} ((s , t) , .(ys +Vec zs)) | from (ys , zs)
  = from ((s , ys) , (t , zs))
{-)-}

-- ????


-- FIXPOINTS

{-(-}
data Tree (F : Normal) : Set where
  <_> : [ F ]N (Tree F) -> Tree F

NAT : Set
NAT = Tree (KN One +N IN)

zeN : NAT
zeN = < ((tt , <>) , <>) >

suN : NAT -> NAT
suN n = < ((ff , <>) , n , <>) >
{-)-}

-- closure under composition?

{-(-}
_oN_ : Normal -> Normal -> Normal
F oN G = ([ F ]N (Shape G)) / (crush (NormalTraverse F) sumMonoid (size G))
{-)-}

-- traversability is normality

{-(-}
TravN : {F : Set -> Set} -> Traverse F -> Normal
TravN {F} tF = (F One) / (crush tF sumMonoid (\ _ -> 1))

ListN : Normal
ListN = Nat / id

[] : forall {X} -> [ ListN ]N X
[] = zero , <>

_::_ : forall {X} -> X -> [ ListN ]N X -> [ ListN ]N X
x :: (n , xs) = suc n , x , xs

listMonoid : {X : Set} -> Monoid ([ ListN ]N X)
listMonoid = record
  { neu = []
  ; _&_ = \ { (m , xs) (n , ys) -> (m +Nat n) , (xs +Vec ys) }
  } 

contents : forall {F}(tF : Traverse F){X} -> F X -> [ ListN ]N X
contents tF = crush tF listMonoid (\ x -> x :: [])
{-)-}

{-(-}
toNormal :  forall {F}(tF : Traverse F){X} -> F X -> [ TravN tF ]N X
toNormal tF {X} xf = travMap tF _ xf , {!snd (contents tF xf)!}
    -- fst is a monoid homomorphism from lists to numbers
{-)-}



-- NORMAL MORPHISMS

{-(-}
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
{-)-}


-- DERIVATIVES OF NORMAL FUNCTORS
{-(-}
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

rotate : (n : Nat)(i : In n) -> In n -> In (suc (n -1 i)) -- In n
rotate 0 (! _) _ = magic
rotate 1 _ _ = ! 0
rotate (suc (suc n)) (! 0)     j     = j
rotate (suc (suc n)) (! suc i) (! 0) = ! 1
rotate (suc (suc n)) (! suc i) (! suc j) with rotate (suc n) (! i) (! j)
rotate (suc (suc n)) (! suc i) (! suc j) | ! 0 = ! 0
rotate (suc (suc n)) (! suc i) (! suc j) | ! k = ! suc k

plug : (F : Normal) -> (IN *N dN F) -N> F
plug F = record { planN = \ { (<> , s , i) -> s ,
                   table (rotate (size F s) i) } }
{-)-}

{--------------------------------------------------------------------}
{- 2. containers                                                    -}
{--------------------------------------------------------------------}

{-(-}
record Cont : Set1 where
  constructor _<|_
  field                 -- data view        effect view
    Sh : Set            -- shapes           commands
    Po : Sh -> Set      -- positions        responses
open Cont

[_]C : Cont -> Set -> Set
[ S <| P ]C X = Sg S \ s -> P s -> X
{-)-}

{-+}
record _-C>_ (F G : Cont) : Set where
  field
    planC : (s : Sh F) -> [ G ]C (Po F s)
open _-C>_

_C$_ : forall {F G} -> F -C> G -> forall {X} -> [ F ]C X -> [ G ]C X
fg C$ xf = {!!}

findPlanC : forall {F G} -> (forall {X} -> [ F ]C X -> [ G ]C X) -> F -C> G
findPlanC fg = {!!}
{+-}

-- closure properties
{-+}
SgC : (S : Set)(T : S -> Cont) -> Cont
SgC S T = {!!}

PiC : (S : Set)(T : S -> Cont) -> Cont
PiC S T = {!!}

_oC_ : Cont -> Cont -> Cont
F oC G = {!!}
-- normalize and see!
{+-}

{-+}
data _o*_ (F : Cont)(X : Set) : Set where
  [_] : X -> F o* X
  <_> : [ F ]C (F o* X) -> F o* X

_o*C : Cont -> Cont
F o*C = (F o* One) <| Leaves where
  Leaves : F o* One -> Set
  Leaves t = {!!}
{+-}

-- LET's GO FULL ON HANCOCK
{-+}
dualC : Cont -> Cont
dualC (S <| P) = ?

record _o%_ (F : Cont)(Y : Set) : Set where
  coinductive
  field
    out : Y
    go  : [ F ]C (F o% Y)
open _o%_

_||_ : forall {F X Y} -> F o* X -> dualC F o% Y ->
                    --   client    server
                        (X * [ ListN ]N Y) * (dualC F o% Y)
                    -- output     log        survivor
client || server = ?
{+-}
