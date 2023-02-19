* Patrik Jansson: Dimension analysis and graded algebras
+ Talk 2023-02-21
+ at the [[https://ifipwg21wiki.cs.kuleuven.be/IFIP21/OnlineFeb23][online meeting]] of WG 2.1 on Algorithmic Languages and Calculi 
+ Joint work with Nicola Botta and Guilherme Silva.
+ Abstract:
  This talk describes work in progress aimed at understanding dimension analysis
  though coding it up using dependent types (in Agda). I will talk you through
  definitions of physical quantities, systems of units, dimensions, dimensional
  analysis, and an example of applying it to modelling a simple pendulum
  experiment. 
+ Some history: I did an Agda tutorial at the WG2.1 meeting #63 in Kyoto
  (in 2007) and I found mentions of Agda in 8 other physical meetings after
  that.
+ Source code: https://github.com/DSLsofMath/dimensionanalysis
** Agda version etc.
+ This file loads in Agda 2.6.2.2 with Agda stdlib-1.7
+ It is a literate Agda file with emacs org-mode syntax for outlining.
** Skip some imports and setup
*** Basic imports: equality, integers
\begin{code}
module JanssonDimensions2023 where
open Agda.Primitive using (lzero)
open import Relation.Binary.PropositionalEquality renaming (_≡_ to _==_)
open import Relation.Nullary renaming (¬_ to Not)
Type = Set
Type1 = Set1

import Data.Integer using (ℤ; 0ℤ; 1ℤ; -1ℤ; +0; +_; -[1+_])
open Data.Integer renaming (ℤ to Integer)
2ℤ = + 2
\end{code}
*** Lift |Ring| operations to vectors
\begin{code}
import Algebra
Ring = Algebra.Ring lzero lzero
open import Data.Nat hiding (_^_) renaming (ℕ to Nat; _+_ to _+n_; _*_ to _*n_)
open import Data.Vec renaming (foldr to depFoldr)
foldr : ∀ {A : Type} {B : Type} {m} →
        (A → B → B) → B → Vec A m → B
foldr {A} {B} op = depFoldr (\_ -> B) (\{m} -> op)
module VectScope (r : Ring) where

  A = Algebra.Ring.Carrier r
  open Algebra.Ring r

  0v : {n : Nat} -> Vec A n
  0v = replicate 0#

  _+v_  :  {n : Nat} ->
           Vec A n -> Vec A n -> Vec A n
  _+v_  =  zipWith _+_

  _-v_  :  {n : Nat} ->
           Vec A n -> Vec A n -> Vec A n
  _-v_  =  zipWith _-_

  _*v_  :  {n : Nat} ->
           A -> Vec A n -> Vec A n
  x *v v =  map (x *_) v
\end{code}
*** Postulate a Ring of reals
+ implemented using |module Data.Float| and some postulates
+ *NOTE* - this is not true but used for pragmatic reasons
\begin{code}
import Data.Float using (Float)
Real : Type
Real = Data.Float.Float

import Data.Float.Base

module RealRingPostulates where
  Carrier = Real
  _≈_ = _==_
  _+_ = Data.Float.Base._+_
  _*_ = Data.Float.Base._*_
  -_  = Data.Float.Base.-_
  0#  = 0.0
  1#  = 1.0
  postulate isRing : Algebra.IsRing _≈_ _+_ _*_ -_ 0# 1#

RealRing : Ring
RealRing = record { RealRingPostulates }
open Data.Float.Base renaming (_*_ to _*r_; _+_ to _+r_; _-_ to _-r_; _÷_ to _/r_)
\end{code}
*** Raw Field record type + Real field record
\begin{code}
record RawField (S : Type) : Type where
  -- TODO redo with reuse of Ring structure?
  field
    0s 1s : S
    _+s_ : S -> S -> S
    _*s_ : S -> S -> S
    _/s_ : S -> S -> S

  _^_ : S → Nat → S
  s ^ zero   = 1s
  s ^ suc n  = (s ^ n) *s s

  pow : S -> Integer -> S
  pow s  ( + n )  =        s ^ n
  pow s -[1+ n ]  = 1s /s (s ^ (suc n))

rfReal : RawField Real
rfReal = record {0s = 0.0; 1s = 1.0; _+s_ = _+r_; _*s_ = _*r_; _/s_ = _/r_}

RealPlus3 : Type
RealPlus3 = Vec Real 3
\end{code}
** Physical quantities and systems of units
+ We can assign a "dimension" to each physical quantity:
  informally |dim : Q -> D| (later an indexed type |Q d|).
+ Physical quantities like length, speed, force, etc. are usually
  measured with respect to a system of units of measurement, one unit
  per "base dimension".
*** These systems can be grouped into classes
+ For geometry, just one base dimension of length is needed and the
  class is usually called just L.
+ For kinematics (the class LT) we have a length and a time.
+ For mechancics (the class LTM) we have length, time, and mass.
+ Etc.
** Dimensions and dimension functions
+ Usually dimensions are decribed by monomials: acceleration "has
  dimension |L/T^2|". The formal reading is that the dimension
  *function* is |\L T M -> L/T^2|. This function describes how the
  measured value of the acceleration changes when we change the units
  of measurements.
+ If we start with a simpler case it is easier to see: if we measure
  my height (of dimension L) in meters the value is 1.78 but if we
  divide the unit by 100 (to get cm) my height is measured to 178.
+ In general, if we make the unit of measurement L times smaller, we
  make the measured height L times bigger.
+ This is usually described as saying that the height is actually
  invariant, but the measured value changes in the opposite direction
  of the measuring rod.
+ This simplest (linear scaling) relation holds for quantities of one
  of the base dimensions, but changes if we move to derived dimensions
  like that for area or acceleration.
+ In general, if we make the unit of length |L| times smaller, the
  unit of time |T| times smaller and the unit of mass |M| times
  smaller, the measuread acceleration becomes |L/T^2| times bigger and
  the measured force |M*L/T^2| times bigger.
** Physics and dimensions
+ In an equation like |F = m * a| (force equals mass times
  acceleration) in physics, the dimensions must match up: 
  |dim F = dim (m * a)|.
+ Similarly for addition.
+ For multiplication we don't need to require matching
  dimension: |dim| is a homomorphism: |dim (m * a) = dim m * dim a|.
+ Now, how do we type this? We clearly need to be able to multiply and
  divide dimensions, and we also need a value to denote
  "dimensionless".
*** DimStuff
\begin{code}
record DimStuff : Type1 where
  field
    Dim : Type
    Dimless : Dim
    _*d_ : Dim -> Dim -> Dim
    _/d_ : Dim -> Dim -> Dim

  _^d_ : Dim -> Integer -> Dim
\end{code}
(We will get back to laws later, and to concrete implementations.)
*** Skip details (exponentiation)
\begin{code}
  _^dn_ : Dim -> Nat -> Dim
  d ^dn zero   = Dimless
  d ^dn suc n  = (d ^dn n) *d d

  d ^d  ( + n )  = d ^dn n
  d ^d -[1+ n ]  = Dimless /d (d ^dn suc n)
\end{code}
** Quantities indexed by dimensions
Then we need to make sure the type for "quantities" is indexed by
dimensions. We assume a type for dimensions, and a type of
scalars |S|.
\begin{code}
module Quantities (dimstuff : DimStuff) (S : Type) where
  open DimStuff dimstuff

  variable d d1 d2 : Dim
  record Qstuff : Type1 where
    field
      Q      : Dim -> Type
      dim    : Q d -> Dim
             
      0Q     : Q d
      _+q_   : Q d  -> Q d  -> Q d
      scale  : S    -> Q d  -> Q d
\end{code}
** Quantities are almost a field
\begin{code}
      1q    : Q Dimless
      _*q_  : Q d1 -> Q d2 -> Q (d1 *d d2)
      _/q_  : Q d1 -> Q d2 -> Q (d1 /d d2)
\end{code}

Here we see that the value of the dimension index tracks the
operations performed on the quantities.

*** Skip (fixities, exponentiation)
\begin{code}
    infixl 7 _*q_
    infixl 7 _/q_
    infixl 6 _+q_

    _^qn_ : Q d -> (n : Nat) -> Q (d ^dn n)
    s ^qn zero   = 1q
    s ^qn suc n  = (s ^qn n) *q s

    _^q_ : Q d -> (i : Integer) -> Q (d ^d i)
    s ^q  ( + n )  = s ^qn n
    s ^q -[1+ n ]  = 1q /q (s ^qn (suc n))
  open Qstuff
\end{code}

** Dimension structure
The algebraic structures at play for the dimensions part is a group:
and we can use a vector of integers to keep track of the exponents of
the base dimensions:

** Concrete example: the LTM class
*** Skip module header / imports
\begin{code}
module LTM (S : Type) (rf : RawField S) where
  open RawField rf public
  module LTMDim where
    open import Data.Integer.Properties using (+-*-ring) public
    open module V = VectScope +-*-ring public
\end{code}
*** LTM Dim implementation example
\begin{code}
    Dim = Vec Integer 3
    Dimless : Dim
    Dimless  = 0ℤ ∷ 0ℤ ∷ 0ℤ ∷ [] -- zero vector
    _*d_ = _+v_
    _/d_ = _-v_
    L T M : Dim -- base vectors / base dimensions
    L        = 1ℤ ∷ 0ℤ ∷ 0ℤ ∷ []
    T        = 0ℤ ∷ 1ℤ ∷ 0ℤ ∷ []
    M        = 0ℤ ∷ 0ℤ ∷ 1ℤ ∷ []
\end{code}
** Quantities
*** Skip details (module end + opens)
\begin{code}
  dimstuff : DimStuff
  dimstuff = record { LTMDim }

  open Quantities dimstuff S public
  open LTMDim
\end{code}
*** |Q| record type: just a wrapper around a scalar value
\begin{code}
  module LTMQ where
    record Q (d : Dim) : Type where
      constructor Val
      field
        val : S
    open Q public
    dim : Q d -> Dim
    dim {d} _ = d
\end{code}
*** |Q d| is a 1D vector space for each |d : Dim|
\begin{code}
    0Q : Q d
    0Q = Val 0s
    _+q_ : Q d  -> Q d  -> Q d
    Val x +q Val y = Val (x +s y)
    scale : S -> Q d -> Q d
    scale s (Val x) = Val (s *s x)
\end{code}
*** |Q| is a graded field (informally - no proofs)
\begin{code}
    1q  : Q Dimless
    1q = Val 1s
    _*q_ : Q d1 -> Q d2 -> Q (d1 *d d2)
    Val x *q Val y = Val (x *s y)
    _/q_ : Q d1 -> Q d2 -> Q (d1 /d d2)
    Val x /q Val y = Val (x /s y)
\end{code}
*** Skip (module end, open)
\begin{code}
  qstuff : Qstuff
  qstuff = record { LTMQ }
  open Qstuff qstuff
\end{code}

** Discussion: field or not a field?
For the scalars we need an underlying field |S| and we get a field
back for |Q Dimless| but not for |Q d| for other |d|. But we get (yet
another) example of an indexed structure: an indexed, or graded, field.

Example of why |Q L| is not a field: the multiplication operation
does not stay within the type:

\begin{code}
  mul : Q L -> Q L -> Q (L *d L) -- Q Area
  mul x y = x *q y
\end{code}

** Measuring quantities

There is one operation missing from |Q d|: measuring the quantity in a
particular system of units. A system of units consists of one scale
factor for each base dimension.
*** System of units
\begin{code}
  SysUnit : Type
  SysUnit = Vec S 3   -- for the LTM class n=3
\end{code}
We will later implement these two examples:
\begin{spec}
  si  : SysUnit  -- m, kg, second
  cgs : SysUnit  -- cm, gram, second
\end{spec}

Now we can interpret a "syntactic dimension" (a vector of exponents of
the base dimensions) as its "dimension function" - the corresponding
monomial which computes the change in measured value for a change in
units.

*** Dimension function and measure implemented
\begin{code}
  dimfun : Dim -> (SysUnit -> S)
  dimfun d su = foldr _*s_ 1s (zipWith pow su d)
\end{code}

Finally we can define the |measure| of a quantity in a system of
units:

\begin{code}
  measure : Q d -> SysUnit -> S
  measure q su = dimfun (dim q) su *s (LTMQ.val q)
\end{code}

** Example quantities
To make this a bit more concrete we introduce a few quantities:
*** Skip module / opens
\begin{code}
module Examples where
  open LTM Real rfReal
  open LTMDim using (L; T; M)
  open DimStuff dimstuff
  open Qstuff qstuff using (_^q_)
  open LTMQ
\end{code}
*** Length and Acceleration
\begin{code}
  hei : Q L
  hei = Val 1.78

  Acceleration : Dim
  Acceleration = L /d (T ^d 2ℤ)
  g : Q Acceleration
  g = Val 9.82

  si : SysUnit   -- m, kg, second
  si  =   1.0 ∷ 1.0 ∷    1.0 ∷ []
  cgs : SysUnit  -- cm, gram, second
  cgs = 100.0 ∷ 1.0 ∷ 1000.0 ∷ []
\end{code}
*** Mass and Force
\begin{code}
  mass : Q M
  mass = Val 76.0

  Force : Dim
  Force = M *d Acceleration
  f : Q Force
  f = mass *q g
\end{code}
*** Unit conversion (measure)
\begin{code}
  test1 : Real
  test1 = measure hei cgs
  check1 : test1 == 178.0
  check1 = refl
  test2 : Real
  test2 = measure f cgs
  check2 : test2 == 7.4632e7
  check2 = refl
\end{code}
** Dimension analysis (Pi theorem example)
OK, now we have dimensions, quantities, the dimension function and
some examples. Time to get to the core of dimension analysis: the Pi
theorem.

*** Pendulum example intro
+ Assume we are experimenting with an ideal pendulum:
+ a point mass |m| hanging from
+ a piece of string of length |x|,
+ the time |t| for one period
+ when starting from an angle |theta|.
+ We want to find how the gravitational constant |g| can be computed
  from the other four parameters.

\begin{spec}
  gravity : Q M -> Q L -> Q T -> Q Dimless -> Q Acceleration
  gravity m x t theta = ?
\end{spec}

*** Pi theorem for this example
+ The core theorem of dimension analysis says that such a function can
  be simplified significantly.
+ First, pick three quantities of independent dimension:
  here |m|, |x|, and |t|.
+ Second, make the remaining quantities dimensionless by combining
  them with monomials in the first three.
+ Here |theta| is already dimensionless, but |g = gravity m x theta t|
  is replaced by |a = g *q (t ^q 2ℤ) /q x : Q Dimless|.
+ Finally, the function |gravity| is factored into a function |acc|
  from just |theta| to |a|, and a monomial factor used to translate
  back to a quantity of the correct dimension.
\begin{code}
  acc : Q Dimless -> Q Dimless
  gravity : Q M -> Q L -> Q T -> Q Dimless -> Q Acceleration
  gravity m x t theta = monomial  *q  acc theta
    where  monomial : Q Acceleration --
           monomial = {!!} -- TODO fill in during the talk
\end{code}
*** Pi theorem implications
+ If we want to figure out the *4-argument* function |gravity| from
  experiments, we actually only need to figure out the *1-argument*
  function |acc|.
+ Experiments (or numerical simulations with the proper differential
  equations) further show that the remaining function is constant for
  small angles |theta|.

\begin{code}
  twoPiSq : Q Dimless
  acc theta = twoPiSq

  twoPiSq = scale 39.5 1q
\end{code}

** Summary & future work
+ Dimension analysis can be usefully expressed done with dep. types
+ Physical quantities form a field graded by an abelian group of
  dimensions.
+ Other example: tensors are graded by their rank
*** TODO Library code and paper is work in progress (mostly in Idris).
*** TODO Multiple grading: |T r (Q d s)| or |Q d (T r s)|?
+ tensors with rank containing quantities with dimensions?
+ or quantities with dimensions containing tensors with rank?
+ or ...
