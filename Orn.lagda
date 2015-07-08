%if False
\begin{code}
module Orn where

open import Agda.Primitive
open import Vec public
open import Normal public
open import STLC public
open import Containers public
open import IxCon public
\end{code}
%endif

\emph{This is new lecture material for 2015. It will probably be a bit
sketchy in the printed version of the notes.}

This chapter re-examines the presentation of datatypes in dependently
typed languages, addressing in particular the issue of what it means
for one datatype to be in various ways more informative than another.
Informal human observations like `lists are natural numbers with extra
decoration' and `vectors are lists indexed by length' are expressed in
a first class language of \emph{ornaments}
--- presentations of fancy new types based on plain old ones ---
encompassing both decoration and, in the sense of Tim Freeman and
Frank Pfenning~\cite{freeman.pfenning:refinementML},
refinement.

Each ornament adds information, so it comes with a forgetful function
from fancy data back to plain, expressible as the fold of its
\emph{ornamental algebra}: lists built from numbers acquire the
`length' algebra. Conversely, each algebra for a datatype induces a
way to index it --- an \emph{algebraic ornament}. The length algebra
for lists induces the construction of the paradigmatic dependent
vector types.

Dependent types thus provide not only a new `axis of diversity' ---
indexing --- for data structures, but also new abstractions to manage
and exploit that diversity. In the spirit of `the new
programming'~\cite{conor.james:viewfromleft}, the engineering of
coincidence is replaced by the propagation of consequence.


\section{Numbers, Lists and Vectors}

If you stare at the inductive definition of |List|, you might notice
that it looks a lot like the inductive definition of natural numbers.
There is a trivial `base-constructor', and there is a
`step-constructor' with one recursive position. The |List| step
carries a label from the given element type; the |Nat| step constructor
is unlabelled. Indeed |List One| makes a perfectly good copy of the
natural numbers. The |length| operation throws away the labelling.

Meanwhile, if we revisit the inductive definition of |Vec|, or `|List|
indexed by |length|', we see that vectors carry exactly the information
which is present in a |List| but absent from its |length| --- the correct
number of elements with which to label the |suc|s. In some sense, the
idea of labelling numbers to get lists \emph{induces} the notion of
vectors.

Now that we have a universe of first-class descriptions for data, it makes
sense to explore more formally these structural relationships between
datatypes.


\section{A Datatype of Datatype Ornaments}

%format *O = "\C{\times}_{\!\C{O}}"
%format _*O_ = "\us{" *O "}"
%format kO = "\C{\upkappa}"
%format !>O = !> "_{\!\F{O}}"
%format <!_!>O = <! _ !>O
%format Inv = "\D{Inv}"
%format inv = "\C{inv}"
%format Orn = "\D{Orn}"
%format inssg = "\C{ins}" sg
%format ins*D = "\C{ins}" *D
%format delsg = "\C{del}" sg
%format delk = "\C{del}" kD
%format cata = "\F{cata}"
%format Alg = "\F{Alg}"
%format erase = "\F{erase}"
%format ornAlg = "\F{ornAlg}"
%format mapCata = "\F{mapCata}"
%format NATD = "\F{NAT}_{\F{D}}"
%format LISTD = "\F{LIST}_{\F{D}}"
%format LISTO = "\F{LIST}_{\F{O}}"
%format lengthD = "\F{length}_{\F{D}}"

A datatype ornament is a way to make an existing datatype more informative.
We might make a datatype \emph{more interestingly indexed} (e.g., |Vec| is more
interestingly indexed than |List|). To increase interest from indexing on
|I| to indexing on |J|, we will need to give a function which forgets,
|f : J -> I|, and we will need to target specific old indices |i| with
new indices chosen from $|f|^{ -1} |i|$. We can define that notion thus.

\begin{code}
data Inv {l}{I J : Set l}(f : J -> I) : I -> Set l where
  inv : (j : J) -> Inv f (f j)
\end{code}

There are other ways in which ornaments make datatypes more informative.
New fields can be added. Old fields can be specialised. What we must
retain is the underlying tree-like structure of the data. We can give
a datatype which explains how to ornament a given |Desc|.

\begin{code}
data Orn {l}{I J : Set l}(f : J -> I) : Desc I -> Set (lsuc l) where
  var    : {i : I} -> Inv f i -> Orn f (var i)
  sg     : {A : Set l}{D : A -> Desc I}(D' : (a : A) -> Orn f (D a)) ->
             Orn f (sg A D)
  pi     : {A : Set l}{D : A -> Desc I}(D' : (a : A) -> Orn f (D a)) ->
             Orn f (pi A D)
  _*O_   : {S T : Desc I}(S' : Orn f S)(T' : Orn f T) -> Orn f (S *D T)
  kO     : {A : Set l}(B : Set l)(k : B -> A) -> Orn f (kD A)
  inssg  : {D : Desc I}(A : Set l)(D' : A -> Orn f D) -> Orn f D
  delsg  : {A : Set l}{D : A -> Desc I}(a : A)(D' : Orn f (D a)) ->
             Orn f (sg A D)
\end{code}

The first five constructors retain the structure of the original description,
just refining the index in the |var| case. The last three modify the tuple
structure of the data. Wherever a field is inserted, the rest of the
ornament can depend on the new field's value. Wherever a field is deleted,
the ornament chooses its value.

We obtain the new datatype from the old by interpreting |Orn|s as |Desc|s at
index |J|.

\begin{code}
<!_!>O :  forall {l}{I J : Set l}{f : J -> I}{D : Desc I} ->
          Orn f D -> Desc J
<! var (inv j)  !>O  = var j
<! sg D'        !>O  = sg _ \ a -> <! D' a !>O
<! pi D'        !>O  = pi _ \ a -> <! D' a !>O
<! D' *O D''    !>O  = <! D' !>O *D <! D'' !>O
<! kO {_} B _   !>O  = kD B
<! inssg A D'   !>O  = sg A \ a -> <! D' a !>O
<! delsg a D'   !>O  = <! D' !>O
\end{code}

For example, the description of natural numbers is given as follows.

\begin{code}
NATD : One -> Desc One
NATD i = sg Two \ { tt -> var i ; ff -> kD One }
\end{code}

We can describe how lists relate to numbers, following the structure
until we reach the step case, where we insert a label.

\begin{code}
LISTO : (A : Set) -> (i : One) -> Orn id (NATD i)
LISTO A i = sg (\ { tt -> inssg A (\ _ -> var (inv i)) ; ff -> kO One id })

LISTD : Set -> One -> Desc One
LISTD A i = <! LISTO A i !>O
\end{code}

Now, every described datatype has a \emph{catamorphism} --- a structural
`fold' operator, parametrised by an \emph{algebra} for its description
which explains how to compute an |X| given a node structure full of |X|s.

\begin{code}
Alg : forall {l}{I : Set l}(F : I -> Desc I)(X : I -> Set l) -> Set l
Alg F X = forall {i} -> <! F i !>D X -> X i

cata :  forall {l}{I : Set l}(F : I -> Desc I)(X : I -> Set l) ->
        Alg F X -> forall {i} -> Data F i -> X i
cata F X phi {i} <$ d $> = phi (mapCata (F i) d) where
  mapCata : (D : Desc _) -> <! D !>D (Data F) -> <! D !>D X
  mapCata (var i)    d         = cata F X phi d
  mapCata (sg A D)   (a , d)   = a , mapCata (D a) d
  mapCata (pi A D)   f         = \ a -> mapCata (D a) (f a)
  mapCata (D *D D')  (d , d')  = mapCata D d , mapCata D' d'
  mapCata (kD A)     a         = a
\end{code}


\section{Ornamental Algebras}

An ornament determines an erasure operation, mapping new nodes to old
by throwing away the extra data.

\begin{code}
erase :  forall {l}{I J : Set l}{f : J -> I}{D : Desc I}{X : I -> Set l}
         (D' : Orn f D) -> <! <! D' !>O !>D (X o f) -> <! D !>D X
erase (var (inv j))  x           = x
erase (sg D')        (a , d')    = a , erase (D' a) d'
erase (pi D')        f'          = \ a -> erase (D' a) (f' a)
erase (D' *O D'')    (d' , d'')  = erase D' d' , erase D'' d''
erase (kO B k)       b           = k b
erase (inssg A D')   (a , d')    = erase (D' a) d'
erase (delsg a D')   d'          = a , erase D' d'
\end{code}

We can use |erase| to construct the \emph{ornamental algebra}
for new nodes, computing old data.

\begin{code}
ornAlg :  forall {l}{I J : Set l}{f : J -> I}{F : I -> Desc I}
          (F' : (j : J) -> Orn f (F (f j))) -> Alg (\ j -> <! F' j !>O) (Data F o f)
ornAlg F' {j} d' = <$ erase (F' j) d' $>
\end{code}

For example, we obtain |length|.

\begin{code}
lengthD : {X : Set} -> Data (LISTD X) <> -> Data NATD <>
lengthD {X} = cata (LISTD X) _ (ornAlg (LISTO X))
\end{code}


\section{Algebraic Ornaments}

Not only does every ornament deliver an algebra: every algebra determines an ornament,
telling us how to index over the carrier of the algebra, as well
as our original indices.

%format algOrn = "\F{algOrn}"
%format help = "\F{help}"

At each node, we demand the data required by the algebra and check
that the correct index is computed. We then delete from the data
the information which is already determined by the algebra's input.

\begin{code}
algOrn : forall {l}{I : Set l}{F : I -> Desc I}(X : I -> Set l) ->
  Alg F X -> (ix : Sg I X) -> Orn {l}{I}{Sg I X} fst (F (fst ix))
algOrn {I = I}{F = F} X phi (i , x) =
    inssg (<! F i !>D X)  \ xs  ->
    inssg (phi xs == x)   \ q   -> help (F i) xs
  where
    help : (D : Desc I)(xs : <! D !>D X) -> Orn fst D
    help (var i)    x           = var (inv (i , x))
    help (sg A D)   (a , xs)    = delsg a (help (D a) xs)
    help (pi A D)   f           = pi \ a -> help (D a) (f a)
    help (D *D D')  (xs , xs')  = help D xs *O help D' xs'
    help (kD A)     a           = kO One (\ _ -> a)
\end{code}
