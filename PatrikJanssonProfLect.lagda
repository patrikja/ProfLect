% -*- Latex -*-
\documentclass[colorhighlight,coloremph]{beamer}
\usetheme{boxes}
\usetheme{Madrid} % Lots of space (good), but no section headings
%\usetheme{Hannover}% Sections heading but too much wasted space
%\usetheme{Dresden}
%\usetheme{Warsaw}
% \usepackage{appendixnumberbeamer}
\usepackage[utf8x]{inputenc}
\usepackage[T1]{fontenc}
\usepackage{natbib}
\usepackage{color,soul}
\usepackage{graphicx}
\usepackage{tikz}
\usetikzlibrary{cd}
\usepackage{hyperref} %% for run: links
\hypersetup{pdfpagemode={FullScreen}}
%include dslmagda.fmt
%include PatrikJanssonProfLect.format

% Changing the way code blocks are presented:
% \renewcommand\hscodestyle{%
%    \setlength\leftskip{-1cm}%
%    \small
% }

\newcommand{\backupbegin}{
   \newcounter{finalframe}
   \setcounter{finalframe}{\value{framenumber}}
}
\newcommand{\backupend}{
   \setcounter{framenumber}{\value{finalframe}}
}


\pgfdeclareimage[height=3cm]{Tall}{images/Tall_i_sol_Langvind.jpg}
\pgfdeclareimage[height=3cm]{Ekorre}{images/Ekorre_smultron_Langvind.jpg}
\pgfdeclareimage[height=1.5cm]{university-logo}{images/ChalmGUmarke}

\newenvironment{myquote}
  {\begin{exampleblock}{}}
  {\end{exampleblock}}

\logo{\pgfuseimage{university-logo}}

\setbeamertemplate{navigation symbols}{}

\addheadbox{section}{\quad \tiny ProfLect P. Jansson, 2015-08-21}
\title{Strongly Typed Programs and Proofs}

\author[P. Jansson]
       {Patrik Jansson, fp.st.cse.chalmers.se}
\institute[Chalmers\&GU]
          {Chalmers University of Technology
           and University of Gothenburg
          }
\date {
    2015-08-21
      }

\begin{document}
\begin{frame}
  \maketitle

\begin{minipage}{4.8cm}
\pgfuseimage{Tall}
~
\pgfuseimage{Ekorre}
\end{minipage}
~
\begin{minipage}{6.5cm}
``It is one of the first duties of a professor, in any subject, to
exaggerate a little both the importance of his subject and his own
importance in it'' [A Mathematician’s Apology, G.~H.~Hardy]\\
~
\end{minipage}


This talk: \url{https://github.com/patrikja/ProfLect}
\end{frame}
\section{Best results}
\begin{frame}{My best results over the years (part 1)}
Among my best results I count
\begin{itemize}
\item early work on Generic Programming \citep{backhouseetal98, janssonjeuring1997a} (well cited)
\item Polytypic Data Conversion Programs \citep{janssonjeuring-dataconv}
\item the Bologna structure (3y BSc + 2y MSc) at cse.chalmers.se
 in my role as Vice Head of Department
\item self-evaluation reports for the CSE degrees (in my role as Head of the CSE programme).
      The BSc got ``very high quality''.
\item Global Systems Science work \citep{jaeger13:GSSshort}\\ leading to the FETPROACT1 call, the GRACeFUL\\ project and the CoEGSS project.
\end{itemize}
\end{frame}
\begin{frame}{My best results over the years (part 2)}
\ldots continued
\begin{itemize}
\item my PhD graduates: Norell, Danielsson, and Bernardy
\item Fast and Loose Reasoning \citep{danielssonetal06:fastandloose}
\item Parametricity and dependent types \citep{bernardy_parametricity_2010}
\item Algebra of Programming in Agda \citep{MuKoJansson2009AoPA}
\item Feat: functional enumeration of algebraic types \citep{duregardHaskell12Feat}
\end{itemize}

\end{frame}

\begin{frame}{Functional Polytypic Programming (1995--2000)}

% My PhD thesis was a monograph based on eight papers on different aspects of a generic programming extensions to Haskell called PolyP.
What is a ``polytypic function''?

Start from the normal |sum| function on lists:

> sum :: Num a => [a] -> a
> sum  []       =   0
> sum  (x:xs)   =   x + sum xs

then generalise to other datatypes like these

< data [a]      =  []       | a : [a]
< data Tree a   =  Leaf a   | Bin (Tree a) (Tree a)
< data Maybe a  =  Nothing  | Just a
< data Rose a   =  Fork a [Rose a]

\end{frame}
\begin{frame}{The Haskell language extension PolyP (POPL'97)}

We obtain

> psum :: (Regular d, Num a) => d a -> a
> psum  = cata fsum

where |fsum| is defined by induction over the pattern functor |f|
of the regular datatype |d a|.

< polytypic fsum :: Num a => f a a -> a
<   = case  f of
<           g + h    ->  either fsum fsum
<           g * h    ->  \(x,y) -> fsum x + fsum y
<           Empty    ->  \x -> 0
<           Par      ->  id
<           Rec      ->  id
<           d @ g    ->  psum . pmap fsum
<           Const t  ->  \x -> 0

\end{frame}

\newcommand{\cata}[1]{\ensuremath{(\![{#1}]\!)}}
%format alpha = "\alpha"
%format beta  = "\beta"
%format muF   = "\mu" F
%format (cata alg) = "\cata{" alg "}"
%format cataT = cata
%format alg = alpha
\begin{frame}[fragile]{Polytypic $\leadsto$ Generic Programming}
Summer schools lecture notes (|>150| citations each):
  \begin{itemize}
  \item Polytypic Programming [Jeuring \& Jansson, 1996]
  \item Generic Programming - An Introduction [Backhouse, Jansson, Jeuring \& Meertens, 1999]
  \end{itemize}


\begin{tikzcd}
|F muF| \arrow{r}{|inn|} \arrow{d}{|F (cata alg)|}  &|muF| \arrow{d}{|cata alg|}\\
|F A| \arrow{r}{|alg|}                    &A
\end{tikzcd}

Notation:
> cata alg  = cataT alg
> F h       = fmap h

% The smiley face signifies that the diagram \tterm{commutes}: the two
% paths from $F A$ to $B$ are equivalent.

\end{frame}
\section{Tools and methods}
\begin{frame}[fragile]{Theoretical tools}

\begin{exampleblock}{Categories, functors and algebras}
Category |C|, (endo-)functor |F : C -> C|, |F|-algebra |(A, alpha : F A -> A)|,
\end{exampleblock}
\pause
\begin{exampleblock}{Homomorphisms between algebras}
|h : (A, alpha) -> (B, beta)| \quad with \quad
%
\begin{tikzcd}
|F A| \arrow{r}{|alpha|} \arrow{d}{|F h|}  &|A| \arrow{d}{|h|}\\
|F B| \arrow{r}{|beta|}                    &|B|
\end{tikzcd}
%
\end{exampleblock}
\pause

\begin{exampleblock}{Catamorphisms}
|cata _ : (F A -> A) -> (muF -> A)| \quad with \qquad
%
\begin{tikzcd}
|F muF| \arrow{r}{|inn|} \arrow{d}{|F (cata alg)|}  &|muF| \arrow{d}{|cata alg|}\\
|F A| \arrow{r}{|alg|}                    &A
\end{tikzcd}
\end{exampleblock}

\end{frame}

\begin{frame}[fragile]{Implementing the theory (|cataT = cata| in Haskell)}

\begin{exampleblock}{Catamorphisms towards implementation}
% For some reason, the uncover version gives an error (but would be prettier).
% \begin{tikzcd}
% \uncover<3->{|F (F muF)| \arrow{d}{|F (F (cata alg))|}}
%       & |F muF| \arrow{d}{|F (cata alg)|} \uncover<3->{\arrow{l}{|F out|}} \uncover<1>{\arrow{r}{|inn|}}
%             &|muF| \uncover<2->{\arrow{l}{|out|}} \arrow{d}{|cata alg|}\\
% \uncover<3->{|F (F A)| \arrow{r}{|F alg|}}
%       & |F A| \arrow{r}{|alg|}
%             &A
% \end{tikzcd}
\begin{tikzcd}
\only<3->{|F (F muF)|} \only<3->{\arrow{d}{|F (F (cata alg))|}}
      & |F muF| \arrow{d}{|F (cata alg)|} \only<3->{\arrow{l}{|F out|}} \only<1>{\arrow{r}{|inn|}}
            &|muF| \only<2->{\arrow{l}{|out|}} \arrow{d}{|cata alg|}\\
\only<3->{|F (F A)| \arrow{r}{|F alg|}}
      & |F A| \arrow{r}{|alg|}
            &A
\end{tikzcd}
\end{exampleblock}
\pause
\begin{code}
data Mu f where                -- Notation: |Mu f = muF|
  Inn :: f (Mu f) -> Mu f

out :: Mu f -> f (Mu f)        -- The inverse of |Inn|
out (Inn x) = x

cataT :: Functor f => (f a -> a) -> (Mu f -> a)
cataT alg = alg . fmap (cataT alg) . out
\end{code}
\end{frame}

\begin{frame}{Implementing the theory (|cataT = cata| in Haskell)}

\begin{code}
data Mu f where
  Inn :: f (Mu f) -> Mu f

out :: Mu f -> f (Mu f)
out (Inn x) = x

cataT :: Functor f => (f a -> a) -> (Mu f -> A)
cataT alg = alg . fmap (cataT alg) . out
\end{code}

Example:
|Mu FTree| is the datatype of binary trees with |Int| leaves.

\begin{code}
data FTree subtree where
  Leaf  :: Int -> FTree subtree
  Bin   :: subtree -> subtree -> FTree subtree
\end{code}
\end{frame}


\begin{frame}{Implementing the theory (arrows in Haskell)}

> class Category cat where -- In the Haskell library |Control.Category|
>     id   :: cat a a                          -- the identity arrow
>     (.)  :: cat b c -> cat a b -> cat a c    -- arrow composition
>  -- Identity laws: |id . p = p = p . id = p|
>  -- Associativity: |(p . q) . r = p . (q . r)|

\pause

> instance Category  (->)     where id x = x; (f . g) x = f (g x)
> instance Category  (SA s)   where -- ...
> data SA s a b = SA ((a,s) -> (b,s))  -- ``Stateful functions''

and many other instances.

\end{frame}

\begin{frame}{Polytypic Data Conversion Programs}

While John Hughes wrote ``Generalising Monads to Arrows'' [SCP'00]
we used them for data conversion [SCP'02].

Motivation:
\begin{itemize}
\item save / load documents in editors should preserve the meaning
\item but the source code for saving is not connected to that for loading
\item proofs of pretty-print / parse round-trip properties are rare
\end{itemize}

Observations / contributions:
\begin{itemize}
\item we can describe both the saving and the loading using arrows
\item we formalize the properties required
\item we provide generic proofs of the round-trip properties
\end{itemize}

\end{frame}

\begin{frame}{Polytypic Data Conversion Programs (cont.)}

The starting point was separation of a datastructure (of type |d a|)
into its shape (|d ()|) and contents (|[a]|).

> separate  :: Regular d => SA [a]  (d a)    (d ())
> separate  = pmapAr put
>
> combine   :: Regular d => SA [a]  (d ())   (d a)
> combine   = pmapAl get
>
> put  ::  SA [a]  a   ()
> get  ::  SA [a]  ()  a
>
> put  =   SA (\(a,   xs    )  -> ((),   a:xs  ))
> get  =   SA (\((),  a:xs  )  -> (a,    xs    ))

\end{frame}

\begin{frame}{Pedagogical development and leadership (2002--)}

  \begin{itemize}
  \item 2002: Director of studies
  \item 2005: Vice Head of Department for education
  \item 2008: Deputy project leader of ``Pedagogical development of Master’s Programmes for the Bologna Structure at Chalmers'' %(\textbf{30M SEK})
  \item 2011: Head of the 5-year education programme in Computer Science and Engineering (Civilingenjör Datateknik, Chalmers). %On average 40\% of full time / year.
  \item 2013: Head of the Division of Software Technology
  \end{itemize}
\end{frame}

\newcommand\textGamma{\ensuremath{\gamma}}
\begin{frame}{My PhD graduates: Norell, Danielsson, and Bernardy}
%\begin{frame}{My PhD graduates: Norell ('07), Danielsson ('07), and Bernardy ('11)}

I worked on
\begin{itemize}
\item generic programs and proofs with Norell \pause\\ {\Huge ~ $\Rightarrow$ Agda},
\pause
\item on program correctness through types with Danielsson \pause\\
$\Rightarrow$ Fast'n Loose Reasoning, %~\cite{danielssonetal06:fastandloose},
\pause Chasing Bottoms, %~\citep{danielssonjansson04:chasingbottoms},
\ldots
\pause
\item parametricity for dependent types \& testing with Bernardy\pause
%format Gamma = "\Gamma"
% %format Abar  = "\bar{A}"
%format Abar  = "\overline{A}"

Proofs for free:
> ⟦_⟧ : PTS → PTS
> Gamma ⊢ A : B   =>   ⟦ Gamma ⟧ ⊢ ⟦A⟧ : ⟦B⟧ Abar
> where
>   ⟦A⟧         is the free proof and
>   ⟦B⟧ Abar    is the free theorem
and |PTS| = Pure Type System (Barendregt, et al.)

\end{itemize}
% Norell: ICFP invited talk 2013

% Upper triangular matrix: https://twitter.com/patrikja/status/408974543873921024/photo/1

\end{frame}

\begin{frame}{Global Systems Science (GSS)}{with the Potsdam institute for Climate Impact Research (PIK)}

  \begin{itemize}
  \item Collaboration from 2007 onwards (main contact: Cezar Ionescu)
  \item Aim: \emph{correct} software models for simulating global
    systems
\pause
  \item Algebra of Programming [PhD course and two papers]
  \item Global Systems Dynamics and Policy (GSDP) [FET-Open 2010--13]
  \item Workshops including ``Domain Specific Languages for Economical
    and Environmental Modelling'', 2011
\pause
  \item The call
    \textbf{\href{http://ec.europa.eu/research/participants/portal/desktop/en/opportunities/h2020/topics/2074-fetproact-1-2014.html}{FETPROACT1}}
    (Future and Emerging Technology, Proactive support for GSS) in
    Horizon 2020 is concrete evidence on the success of this line of
    work.
  \item Project GRACeFUL: ``Global systems Rapid Assessment tools
    through Constraint FUnctional Languages'' granted 2015--2018 by the FETPROACT1 call.
\pause
  \item Upcoming project CoEGSS: ``Center of Excellence\\ for Global
    Systems Science'', start 2015-10-01, 3y.
  \end{itemize}
\end{frame}

\begin{frame}{Algebra of Programming in Agda}

  While Agda was implemented by Norell, Danielsson et al.  we used it
  for the Algebra of Programming.

One highlight is the notation for equality proofs

> begin
>   term1
> ≡⟨ step1 ⟩   -- |step1 :   term1 ≡ term2|
>   term2
> ≡⟨ step2 ⟩   -- |step2 :   term2 ≡ term3|
>   term3
> ∎

%This notation is actually equivalent to just one application of transitivity of equality and could thus be shortened to |trans step1 step2|.

Roughly equivalent to |trans step1 step2| but often \\
more readable (at least in more complicated cases).

\end{frame}

\begin{frame}{An example proof in Agda, part 1}

\begin{code}
expLemma :  (x : Real) -> (m n  : Nat)  -> (x ^ m  *R  x ^ n ≡ x ^ (m + n))
baseCase :  (x : Real) -> (n    : Nat)  -> (x ^ Z  *R  x ^ n ≡ x ^ (Z + n))
stepCase :  (x : Real) -> (m n  : Nat)  ->
            (ih :  x ^ m      *R  x ^ n ≡ x ^ (m + n))      ->
            (      x ^ (S m)  *R  x ^ n ≡ x ^ ((S m) + n))

expLemma x Z      n = baseCase x n
expLemma x (S m)  n = stepCase x m n (expLemma x m n)
\end{code}

%TODO: link to more lemmas: http://www.cse.chalmers.se/~patrikj/talks/Parsing_Agda_OrderLemmas.utf8.agda
\end{frame}

\begin{frame}{An example proof in Agda, part 2}

\begin{code}
baseCase :  (x : Real) -> (n    : Nat)  -> (x ^ Z  *R  x ^ n ≡ x ^ (Z + n))
baseCase x n =
  begin
     x ^ Z  *R  x ^ n
  ≡⟨ refl ⟩                         -- By definition of |_^_|
     one *R x ^ n
  ≡⟨ unitMult (x ^ n) ⟩             -- Use |one *R y = y| for |y = x ^ n|
       x ^ n
  ≡⟨ refl ⟩                         -- By definition of |_+_|
     x ^ (Z + n)
  ∎
\end{code}



\end{frame}

\begin{frame}[fragile]{Feat: functional enumeration of algebraic types}
{\small [with Duregård and Wang, Haskell Symposium 2012]}
\vfill
%format indexT t = index "_{" t "}"

An efficiently computable bijective function
|indexT a :: Nat -> a|, much like |toEnum| in the |Enum| class.
\vfill

Example: enumerate ``raw abstract syntax trees'' for Haskell.
\begin{myquote}
\begin{verbatim}
*Main> index (10^5) :: Exp
AppE (LitE (StringL ""))
     (CondE (ListE []) (ListE []) (LitE (IntegerL 1)))
\end{verbatim}
\end{myquote}
\pause
\begin{myquote}
\begin{verbatim}
*Main> index (10^100) :: Exp
ArithSeqE (FromR (AppE (AppE (ArithSeqE (FromR (ListE [])))
... -- and 20 more lines!
\end{verbatim}
\end{myquote}


\end{frame}

\begin{frame}{Ongoing work}

\begin{exampleblock}{DSLM: Presenting Math.~Analysis Using Functional Programming}
\vspace{-0.2cm}
\begin{spec}
Forall (eps elemOf Real) ((eps > 0)  =>  (Exists (a elemOf A) ((abs(a - sup A)) < eps)))
\end{spec}
\vspace*{-0.2cm}
\end{exampleblock}
\begin{exampleblock}{Sequential Decision Problems}

``Sequential Decision Problems, dependent types and generic solutions''

``A computational theory of policy advice and avoidability''

\end{exampleblock}

\begin{exampleblock}{AUTOSAR calculus}
``A semantics of core AUTOSAR''

(AUTOSAR = AUTomotive Open System ARchitecture)
\end{exampleblock}

\begin{exampleblock}{ValiantAgda}
Certified Context-Free Parsing: A form. of Valiant's Algorithm in Agda

Solve |C  =  W  +  C * C| for matrices of sets of non-terminals!
\end{exampleblock}


\end{frame}

%format · = "\!\!\cdot\!\!"
\begin{frame}{ValiantAgda (a part in the middle)}

[Valiant, 1975] provides a rather awkward interated
def. for all bracketings:

\begin{code}
  C =  W + W · W +  W ·(W · W) + (W · W) · W +
       (W · W) ·(W · W) + ...
\end{code}

We use the smallest solution to the following equation:

\begin{code}
   C == W + C · C
\end{code}

(for strictly upper triangular |W|). Or more precisely

\begin{code}
Clo : U -> U ->  Set
Clo   W    C  =  C == W + C · C

LowerBound : {A : Set} -> (A -> Set) -> A -> Set
LowerBound P x = ∀ z -> (P z -> x ≤ z)

Minimal    : {A : Set} -> (A -> Set) -> A -> Set
Minimal P x =  P x  /\  LowerBound P x

Spec =  ∀ (W : U) → ∃ \(C : U) ->
        Minimal (Clo W) C
\end{code}
\end{frame}

\begin{frame}{ValiantAgda (the chocolate part;-)}

\includegraphics[width=0.45\textwidth]{images/UpperTriangularChocolateTwitter.png}
\pause
\includegraphics[width=0.5\textwidth]{images/StrictlyUpperTriangularChocolateTwitter.png}
\vfill
\end{frame}

\begin{frame}[fragile]{Summary}
\newcommand{\Dure}{\text{\emph{Duregård}}}
\newcommand{\R}{\arrow[r]}
\newcommand{\RB}{\arrow[r, "Bologna"]}
\newcommand{\RR}{\arrow[rr, bend left=15]}
\newcommand{\D}{\arrow[d]}
\newcommand{\DR}{\arrow[dr]}
\newcommand{\DL}{\arrow[dl]}
\newcommand{\UR}{\arrow[ur]}
\begin{tikzcd}
PolyP  \D\R & DataConv & AoP Agda \R   & ValiantAgda\\
Norell \D   & Danielsson \D\DL& Bernardy \D\UR& \Dure \D \\
Agda \ar[rruu, bend left=20]       & Fast 'n Loose & ParaDep       & Feat      \\
\only<2->{DoS \R      & VPref.Gru \RB  & PA@@D  \R     & DivHead   \\}
\only<3->{PIK \R \DR  & GSDP \R \RR \D& GRACeFUL      & CoEGSS    \\
            & Ionescu \UR \R& DSLsofMath}
\end{tikzcd}
\end{frame}

\backupbegin
%\appendix
\section{Spare slides}

% \section[DSLsofMath]{DSLM: Presenting Mathematical Analysis Using Functional Programming}

\begin{frame}{DSLM: Domain Specific Languages of Mathematics}
\begin{exampleblock}{Style example}
\begin{spec}
Forall (eps elemOf Real) ((eps > 0)  =>  (Exists (a elemOf A) ((abs(a - sup A)) < eps)))
\end{spec}
\end{exampleblock}

\end{frame}



%% -------------------------------------------------------------------
\subsection{Intro}

\begin{frame}
\frametitle{Background}
\vfill

\emph{Domain-Specific Languages of Mathematics}
\citep{dslmcourseplan}: is a course currently developed at Chalmers in
response to difficulties faced by third-year students in learning and
applying classical mathematics (mainly real and complex analysis)

Main idea: encourage students to approach mathematical domains from a
functional programming perspective (similar to
\cite{wells1995communicating}).

\vfill

\begin{exampleblock}{}
``... ideally, the course would improve the mathematical education of computer scientists and the computer science education of mathematicians.''
\end{exampleblock}

\url{https://github.com/DSLsofMath/DSLsofMath/blob/master/DSLsofMath.md}

\vfill
\vfill

\end{frame}


%% -------------------------------------------------------------------

\begin{frame}
\frametitle{Introduction}

\begin{itemize}
\item make functions and types explicit

\item use types as carriers of semantic information, not just variable
  names

\item introduce functions and types for implicit operations such as
  the power series interpretation of a sequence

\item use a calculational style for proofs

\item organize the types and functions in DSLs
\end{itemize}

Not working code, rather working understanding of concepts

\end{frame}

%% -------------------------------------------------------------------

\subsection{Types}
\begin{frame}
\frametitle{Complex numbers}
\begin{myquote}
  We begin by defining the symbol |i|, called \textbf{the imaginary unit}, to
  have the property

>      square i = -1

  Thus, we could also call |i| the square root of |-1| and denote it
  |sqrt (-1)|. Of course, |i| is not a real number; no real number has
  a negative square.
\end{myquote}

\hfill (\cite{adams2010calculus}, Appendix I)

\pause

> data I = i

\end{frame}

%% -------------------------------------------------------------------

\begin{frame}
\frametitle{Complex numbers}

\begin{myquote}
  \textbf{Definition:} A \textbf{complex number} is an expression of
  the form

>  a + bi {-"\qquad \mathrm{or} \qquad"-} a + ib,

  where |a| and |b| are real numbers, and |i| is the imaginary unit.
\end{myquote}

\pause

> data Complex  =  Plus1 Real Real I
>               |  Plus2 Real I Real

> show :  Complex     ->  String
> show (Plus1 x y i)  =   show x ++ " + " ++ show y ++ "i"
> show (Plus2 x i y)  =   show x ++ " + " ++ "i" ++ show y

\end{frame}

%% -------------------------------------------------------------------

\begin{frame}
\frametitle{Complex numbers examples}

\begin{myquote}
  \textbf{Definition:} A \textbf{complex number} is an expression of
  the form

>  a + bi {-"\qquad \mathrm{or} \qquad"-} a + ib,

  where |a| and |b| are real numbers, and |i| is the imaginary unit.
\end{myquote}

\begin{myquote}
  For example, |3 + 2i|, |div 7 2 - (div 2 3)i| , |i(pi) = 0 + i(pi)| , and |-3 =
  -3 + 0i| are all complex numbers.  The last of these examples shows
  that every real number can be regarded as a complex number.
\end{myquote}



\end{frame}

%% -------------------------------------------------------------------



\begin{frame}
\frametitle{Complex numbers examples}
\begin{myquote}
  For example, |3 + 2i|, |div 7 2 - (div 2 3)i| , |i(pi) = 0 + i(pi)| , and |-3 =
  -3 + 0i| are all complex numbers.  The last of these examples shows
  that every real number can be regarded as a complex number.
\end{myquote}


> data Complex  =  Plus1 Real Real I
>               |  Plus2 Real I Real

> toComplex : Real -> Complex
> toComplex x = Plus1 x 0 i


\begin{itemize}
\item what about |i| by itself?
\item what about, say, |2i|?
\end{itemize}

\end{frame}

%% -------------------------------------------------------------------

\begin{frame}
\frametitle{Complex numbers version 2.0}
\begin{myquote}
  (We will normally use |a + bi| unless |b| is a complicated
  expression, in which case we will write |a + ib| instead. Either
  form is acceptable.)
\end{myquote}


> data Complex = Plus Real Real I

> data Complex = PlusI Real Real

\end{frame}

%% -------------------------------------------------------------------

\begin{frame}
\frametitle{Name and reuse}
\begin{myquote}
  It is often convenient to represent a complex number by a single
  letter; |w| and |z| are frequently used for this purpose. If |a|,
  |b|, |x|, and |y| are real numbers, and |w = a + bi| and |z = x +
  yi|, then we can refer to the complex numbers |w| and |z|. Note that
  |w = z| if and only if |a = x| and |b = y|.
\end{myquote}

> newtype Complex = C (Real, Real)

\end{frame}

%% -------------------------------------------------------------------

\begin{frame}
\frametitle{Equality and pattern-matching}
\begin{myquote}
  \textbf{Definition:} If |z = x + yi| is a complex number (where |x|
  and |y| are real), we call |x| the \textbf{real part} of |z| and denote it
  |Re (z)|. We call |y| the \textbf{imaginary part} of |z| and denote it |Im
  (z)|:

> Re(z)  =  Re (x+yi)    =  x
> Im(z)  =  Im (x + yi)  =  y

\end{myquote}

> Re : Complex       ->  Real
> Re z @ (C (x, y))  =   x

> Im : Complex       ->  Real
> Im z @ (C (x, y))  =   y

\end{frame}


%% -------------------------------------------------------------------

\begin{frame}
\frametitle{Shallow vs. deep embeddings}
%{
%format == = "{=}"
\begin{myquote}
  \textbf{The sum and difference of complex numbers}

  If |w == a + bi| and |z == x + yi|, where |a|, |b|, |x|, and |y| are real numbers,
  then

> w  +  z  =  (a + x)  +  (b + y)i
>
> w  -  z  =  (a - x)  +  (b - y)i
\end{myquote}
%}
\begin{overprint}
\onslide<1>
\textbf{Shallow embedding}:

> (+)  :  Complex -> Complex -> Complex
> (C (a, b)) + (C (x, y))  =  C ((a + x), (b + y))
>
> newtype Complex = C (Real, Real)

\onslide<2>
\textbf{Deep embedding (buggy)}:

> (+)  :  Complex -> Complex -> Complex
> (+) = Plus
>
> data ComplexDeep  =  i
>                   |  ToComplex Real
>                   |  Plus   Complex  Complex
>                   |  Times  Complex  Complex
>                   |  ...

\onslide<3>
\textbf{Deep embedding}:

> (+)  :  Complex -> Complex -> Complex
> (+) = Plus
>
> data Complex  =  i
>               |  ToComplex Real
>               |  Plus   Complex  Complex
>               |  Times  Complex  Complex
>               |  ...

\end{overprint}
\end{frame}



%% -------------------------------------------------------------------
\subsection{Proofs}

\begin{frame}
\frametitle{Completeness property of |Real|}

Next: start from a more ``mathematical'' quote from the book:

\begin{myquote}

    The \emph{completeness} property of the real number system is more
    subtle and difficult to understand. One way to state it is as
    follows: if |A| is any set of real numbers having at least one
    number in it, and if there exists a real number |y| with the
    property that |x <= y| for every |x elemOf A| (such a number |y| is
    called an \textbf{upper bound} for |A|), then there exists a
    smallest such number, called the \textbf{least upper bound} or
    \textbf{supremum} of |A|, and denoted |sup(A)|. Roughly speaking,
    this says that there can be no holes or gaps on the real
    line---every point corresponds to a real number.

\end{myquote}

\hfill (\cite{adams2010calculus}, page 4)

\end{frame}

%% -------------------------------------------------------------------

\begin{frame}
\frametitle{Min (``smallest such number'')}

Specification (not implementation)

> min    :  PS+ Real -> Real
> min A  =  x ifandonlyif x elemOf A && ((Forall (a elemOf A) (x <= a)))

Example consequence (which will be used later):

\begin{quote}
  If |y < min A|, then |y notElemOf A|.
\end{quote}
\end{frame}

%% -------------------------------------------------------------------

\begin{frame}
\frametitle{Upper bounds}

> ubs    :  PS Real -> PS Real
> ubs A  =  { x | x elemOf Real, x upper bound of A }
>        =  { x | x elemOf Real, (Forall (a elemOf A) (a <= x)) }

The completeness axiom can be stated as

\begin{quote}
  Assume an |A : PS+ Real| with an upper bound |u elemOf ubs A|.

  Then |s = sup A = min (ubs A)| exists.
\end{quote}

\noindent
where

> sup : PS+ Real -> Real
> sup = min . ubs

\end{frame}

\begin{frame}
\frametitle{Completeness and ``gaps''}

\begin{quote}
Assume an |A : PS+ Real| with an upper bound |u elemOf ubs A|.

Then |s = sup A = min (ubs A)| exists.
\end{quote}

But |s| need not be in |A| --- could there be a ``gap''?

\pause

With ``gap'' = ``an |eps|-neighbourhood between |A| and |s|'' we can
show there is no ``gap''.

\end{frame}


%% -------------------------------------------------------------------

\begin{frame}
\frametitle{A proof: Completeness implications step-by-step}
%\setlength{\parskip}{0cm}
\def\commentbegin{\quad\{\ }
\def\commentend{\}}
\newcommand{\gap}{\pause\vspace{-0.8cm}}
\begin{spec}
   eps > 0

=> {- arithmetic -}

   s - eps < s
\end{spec}
\gap
\begin{spec}
=> {- |s = min (ubs A)|, property of |min| -}

   s - eps notElemOf ubs A
\end{spec}
\gap
\begin{spec}
=> {- set membership -}

   not (Forall (a elemOf A) (a <= s - eps))
\end{spec}
\gap
\begin{spec}
=> {- quantifier negation -}

   (Exists (a elemOf A) (s - eps < a))
\end{spec}
\gap
\begin{spec}
=> {- definition of upper bound -}

   (Exists (a elemOf A) (s - eps < a <= s))
\end{spec}
\gap
\begin{spec}
=> {- absolute value -}

   (Exists (a elemOf A) ((abs(a - s)) < eps))
\end{spec}
% More details:
%   (Exists (a elemOf A) (- eps < a - s <= 0))
%   (Exists (a elemOf A) (- eps < a - s < eps))
%   (Exists (a elemOf A) (abs (a - s) < eps))

\end{frame}

%% -------------------------------------------------------------------

\begin{frame}
\frametitle{Completeness: proof interpretation (``no gaps'')}

To sum up the proof says that the completeness axiom implies:
\begin{spec}
proof : (Forall (eps elemOf Real) ((eps > 0)  =>  (Exists (a elemOf A) ((abs(a - sup A)) < eps))))
\end{spec}
\pause
\textbf{More detail:}

Assume a non-empty |A : PS Real| with an upper bound |u elemOf ubs A|.

Then |s = sup A = min (ubs A)| exists.

We know that |s| need not be in |A| --- could there be a ``gap''?

\pause

No, |proof| will give us an |a elemOf A| arbitrarily close to the
supremum.

So, there is no ``gap''.

\end{frame}



%% -------------------------------------------------------------------

\begin{frame}
\frametitle{Conclusions}

\begin{itemize}
\item make functions and types explicit: |Re : Complex -> Real|, |min
  : PS+ Real -> Real|

\item use types as carriers of semantic information, not just variable
  names

\item introduce functions and types for implicit operations such as
  |toComplex : Real -> Complex|

\item use a calculational style for proofs

\item organize the types and functions in DSLs (for |Complex|, limits,
  power series, etc.)
\end{itemize}

\end{frame}


%% -------------------------------------------------------------------

\begin{frame}
\frametitle{Future work}

Partial implementation in Agda:

\begin{itemize}
\item errors caught by formalization (but no ``royal road'')
  \begin{itemize}
  \item |ComplexDeep|
  \item |choice| function
  \end{itemize}
\item subsets and coercions
  \begin{itemize}
  \item |eps : RPos|, different type from |RPosz| and |Real| and |CC|
  \item what is the type of |abs|? (|CC -> RPosz|?)
  \item other subsets of |Real| or |CC| are common, but closure
    properties unclear
  \end{itemize}
\end{itemize}
\end{frame}

%% -------------------------------------------------------------------

%\appendix
\section{Bibliography}
\begin{frame}
\frametitle{Bibliography}

\bibliographystyle{abbrvnat}
\bibliography{PatrikJanssonProfLect}
\end{frame}

\backupend

\end{document}

%% -------------------------------------------------------------------

\begin{frame}
\frametitle{}
\vfill
\vfill
\end{frame}

%% -------------------------------------------------------------------
