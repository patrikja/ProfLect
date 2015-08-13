% -*- Latex -*-
\documentclass[colorhighlight,coloremph]{beamer}
\usetheme{boxes}
\usetheme{Madrid} % Lots of space (good), but no section headings
%\usetheme{Hannover}% Sections heading but too much wasted space
%\usetheme{Dresden}
%\usetheme{Warsaw}
\usepackage[utf8x]{inputenc}
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
\begin{frame}{My best results over the years}
Among my best results I count
\begin{itemize}
\item early work on Generic Programming \citep{backhouseetal98, janssonjeuring1997a} (well cited)
\item Polytypic Data Conversion Programs \citep{janssonjeuring-dataconv}
\item the Bologna structure (3y BSc + 2y MSc) at cse.chalmers.se
 in my role as Vice Head of Department
\item my PhD graduates: Norell, Danielsson, and Bernardy
\item Fast and Loose Reasoning \citep{danielssonetal06:fastandloose}
\item Algebra of Programming in Agda \citep{MuKoJansson2009AoPA}
\item Parametricity and dependent types \citep{bernardy_parametricity_2010}
\item Feat: functional enumeration of algebraic types \citep{duregardHaskell12Feat}
\item self-evaluation reports for the CSE degrees (in my role as Head of the CSE programme).
      The BSc got ``very high quality''.
\item Global Systems Science work \citep{jaeger13:GSSshort}\\ leading to the FETPROACT1 call, the GRACeFUL\\ project and the CoEGSS project.
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

%TODO Practical tools: Strongly typed functional programming: Haskell, Agda, Idris

\begin{frame}{Polytypic Data Conversion Programs}
TODO

  Polytypic Data Conversion Programs \citep{janssonjeuring-dataconv}

arrows, correctness proofs, etc.

\end{frame}

\begin{frame}{Pedagogical development and leadership (2002--)}

  \begin{itemize}
  \item 2002: Director of studies
  \item 2005: Vice Head of Department for education
  \item 2008: Deputy project leader of ``Pedagogical development of Master’s Programmes for the Bologna Structure at Chalmers'' (\textbf{30M SEK})
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
Chasing Bottoms, %~\citep{danielssonjansson04:chasingbottoms},
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

\begin{frame}{Algebra of Programming in Agda}
TODO
\end{frame}

\begin{frame}{Feat: functional enumeration of algebraic types}
TODO:

  Jonas Duregård

\end{frame}

\begin{frame}{Global Systems Science}

Global Systems Science work \citep{jaeger13:GSSshort}\\ leading to the FETPROACT1 call, the GRACeFUL\\ project and the CoEGSS project.

\end{frame}

\begin{frame}{Ongoing work}

DSLM: Presenting Mathematical Analysis Using Functional Programming

Sequential Decision Problems, dependent types and generic solutions

A computational theory of policy advice and avoidability

Certified Context-Free Parsing: A formalisation of Valiant's Algorithm in Agda

\end{frame}

\section[DSLsofMath]{DSLM: Presenting Mathematical Analysis Using Functional Programming}

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

\appendix
\section{Bibliography}
\begin{frame}
\frametitle{Bibliography}

\bibliographystyle{abbrvnat}
\bibliography{PatrikJanssonProfLect}
\end{frame}


\end{document}

%% -------------------------------------------------------------------

\begin{frame}
\frametitle{}
\vfill
\vfill
\end{frame}

%% -------------------------------------------------------------------
