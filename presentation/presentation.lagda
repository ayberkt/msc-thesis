\documentclass[xcolor={dvipsnames}]{beamer}

\usetheme{metropolis}

\usepackage{ebproof}
\usepackage{wasysym}
\usepackage{tikz}
\usepackage{tikz-cd}
\usetikzlibrary{tikzmark}
\usepackage{latex/agda}
\usepackage[backend=biber]{biblatex}
\addbibresource{references.bib}

\title{Formal Topology in Univalent Foundations}
\date{\today}
\author{Ayberk Tosun}
\institute{Chalmers University of Technology}

\setmonofont[Scale=0.85]{PragmataPro Mono Liga}

\definecolor{AgdaFunction}{HTML}{0000CD}
\definecolor{AgdaString}{HTML}{B22222}
\definecolor{codecolour}{RGB}{27, 134, 236}
\definecolor{gerbesred}{RGB}{164, 30, 50}
\definecolor{darkred}{rgb}{0.45,0,0}

\definecolor{darkgreen}{rgb}{0,0.45,0}
\definecolor{hottviolet}{rgb}{0.45,0,0.45}
\definecolor{hottblue}{rgb}{0,0.45,0.45}

\hypersetup{
  linktoc    = page,
  citecolor  = hottblue,
  urlcolor   = hottviolet
}

\newcommand{\fnname}[1]{{\color{codecolour} {\tt #1}}}
\newcommand{\prgoutput}[1]{{\color{codecolour} {\tt #1}}}

\newcommand{\pity}[3]{\prod_{(#1~:~#2)} #3}
\newcommand{\sigmaty}[3]{\sum_{(#1~:~#2)} #3}
\newcommand{\pow}[1]{\mathcal{P}\left(#1\right)}
\newcommand{\univ}{\mathsf{Type}}
\newcommand{\trunc}[1]{\left\| #1 \right\|}
\newcommand{\abs}[1]{\left| #1 \right|}
\newcommand{\nuclnm}{\mathbf{j}}
\newcommand{\nuclapp}[1]{\nuclnm{}\left(#1\right)}

\newcommand{\fix}[2]{\mathfrak{fix}\left(#1, #2\right)}

\newcommand{\rulename}[1]{{\color{darkred} \mathsf{#1}}}
\newcommand{\ruledir}{{\color{gerbesred} \mathsf{dir}}}
\newcommand{\rulebranch}{{\color{gerbesred} \mathsf{branch}}}
\newcommand{\rulesquash}{{\color{gerbesred} \mathsf{squash}}}
\newcommand{\hprop}{\mathsf{hProp}}

\newcommand{\McF}{\mathcal{F}}

\newcommand{\is}{:\equiv}

\newcommand{\covers}[2]{#1 \lhd #2}
\newcommand{\badcovers}[2]{#1~\LHD~#2}

%% Color customisation.

\begin{document}

\maketitle

\section{What is topology?}

\begin{frame}{What is topology?}
  \large
  A topological space is a set $X$ together with a collection $\Omega(X)$ of its subsets
  such that
  \begin{itemize}
    \item $\emptyset, X \in \Omega(X)$,
    \item $\Omega(X)$ is closed under \alert{finite} intersections, and
    \item $\Omega(X)$ is closed under \alert{arbitrary} unions.
  \end{itemize}
\end{frame}

\begin{frame}[c]{What is topology?}
  \large
  \vspace{3em}

  Let \fnname{P} be a program. When run, it starts printing out a sequence of integers:

  \begin{center}
  \prgoutput{7~~11~~2~~2~~8~~42~~}~$\cdots$
  \end{center}

  We can consider certain properties of \fnname{P}, such as:
  \begin{center}
    ``\tikzmarknode{a}{\fnname{P}} eventually prints \fnname{17}'', or\\
    \vspace{1em}
    ``\fnname{P} prints no more than two \fnname{2}s\tikzmarknode{b}{''}.
  \end{center}

  \uncover<2>{
    {\color{gerbesred}
      \tikzmarknode{txt}{Observable}%
      \hspace{14.4em}%
      \tikzmarknode{not-obs}{\textbf{Not} observable}
    \begin{tikzpicture}[remember picture, overlay]
      \draw[->, line width=0.3mm] (txt.north) to[out=90, in=-210] (a.west);
      \draw[->, line width=0.3mm] (not-obs.north) to[out=70, in=40] (b.east);
    \end{tikzpicture}
    }
  }
\end{frame}

\begin{frame}{What is topology?}
  \large
  \begin{center}
    ``$\phi$ is an \alert{observable property} of a program.''

    \vspace{0.5em}
    $\leftrightarrow$
    \vspace{0.5em}

    There exists a prefix $i$ of the output $\sigma$ at which the program is \alert{verified}
    to satisfy $\phi$: all extensions of $\sigma_i$ satisfy $\phi$.
  \end{center}
\end{frame}

\begin{frame}{What is topology?}
  Let $\phi_0, \cdots ,\phi_n$ be a \alert{finite} number of observable properties.

  \vspace{1em}

  Suppose $\phi_0 \wedge \cdots \wedge \phi_n$ holds.

  \vspace{1em}

  There must be \alert{stages} $i_0, \cdots , i_n$ such that $\phi_k$ is verified at stage $i_k$.

  \vspace{1em}

  $\phi_0 \wedge \cdots \wedge \phi_n$ must then be verified at $\max(i_0, \cdots, i_n)$.

  \vspace{1em}

  $\phi_0 \wedge \cdots \wedge \phi_n$ is \alert{observable}.
\end{frame}

\begin{frame}{What is topology?}
    Let $\{~\psi_i ~|~ i \in I~\}$ be an \alert{arbitrary} number of observable properties.

    \vspace{1em}

    Suppose $\bigvee_i \psi_i$ holds.

    \vspace{1em}

    Some $\psi_i$ holds meaning it must be verified at some stage $m$.

    \vspace{1em}

    $\bigvee_i \psi_i$ is hence verified at stage $m$.

    \vspace{1em}

    This means that $\bigvee_i \psi_i$ is \alert{observable}.
\end{frame}

\begin{frame}{What is topology?}
  \huge
  \begin{center}
    Topology is a mathematical theory of \alert{observable} properties.
  \end{center}
\end{frame}

\section{Frames}

\begin{frame}{Frames}
  \large
  \vspace{1.5em}

  A \alert{frame} is a poset $\mathcal{O}$ such that
  \begin{itemize}
    \item \alert{finite subsets} of $\mathcal{O}$ have \alert{meets},
    \item \tikzmarknode{a}{\alert{arbitrary subsets}} of $\mathcal{O}$ have \alert{joins},
      and
    \item binary meets distribute over arbitrary joins:
      \begin{equation*}
        a \wedge \left( \bigvee_{i~\in~I} b_i \right) = \bigvee_{i~\in~I} \left( a \wedge b_i \right),
      \end{equation*}
      for any $a \in \mathcal{O}$ and family $\{ b_i ~|~ i \in I \}$ over $\mathcal{O}$.
  \end{itemize}

  \vspace{1em}

  \uncover<2>{
    {\color{gerbesred}
    \begin{center}
    {\Large
      \tikzmarknode{b}{In} type theory, the quantification over arbitrary subsets is
      problematic.
    }
    \end{center}
    \begin{tikzpicture}[remember picture, overlay]
      \draw[->, line width=0.3mm] (b.west) to[out=180, in=-230] (a.west);
    \end{tikzpicture}
    }
  }
\end{frame}

\begin{frame}{Frames --- a prime example}
  \large

  Given a poset
  \begin{align*}
    A &\quad:\quad \univ{}_m\\
    \sqsubseteq &\quad:\quad A \rightarrow A \rightarrow \mathsf{hProp}_m
  \end{align*}
  the type of \alert{downwards-closed subsets} of $A$ is:
  \[ \sigmaty{U}{\pow{A}}{\pity{x~y}{A}{x \in U \rightarrow y \sqsubseteq x \rightarrow y \in U}}, \]
  \begin{center}
    where
  \end{center}
  \begin{alignat*}{2}
    \mathcal{P}    \quad&:\quad   && \univ{}_m \rightarrow \univ{}_{m+1} \\
    \mathcal{P}(X) \quad&\is\quad && X \rightarrow \mathsf{hProp}_m     . 
  \end{alignat*}
\end{frame}

\begin{frame}{Frames --- a prime example}
  \large

  This forms a \alert{frame} defined as:
  \begin{align*}
    \top           &\quad\is{}\quad \lambda \_.~ \mathsf{Unit}\\
    A \wedge B       &\quad\is{}\quad \lambda x.~ (x \in A) \times (x \in B)\\
    \bigvee_{i~:~I} B_i &\quad\is{}\quad \lambda x.~ \trunc{\sigmaty{i}{I}{x \in B_i}}.
  \end{align*}
\end{frame}

\begin{frame}{Frames --- a prime example}
  \large

  \textbf{Question}: can we get any frame out of a poset in this way?

  \vspace{1em}

  \uncover<2>{
    One way is to employ the notion of a \alert{nucleus} on a frame.

    \vspace{1em}

    For this, we need to enrich the notion of a poset with a structure that gives rise to
    an appropriate \alert{nucleus}\\
    (on its frame of downwards-closed subsets).

    \vspace{1em}

    For us, that structure will be a \alert{formal topology}.
  }
\end{frame}

\section{Formal Topology}

\begin{frame}{Formal Topologies --- as Interaction Systems}
  \large

  An \alert{interaction structure} on some type $A$ comprises three functions:
  \begin{align*}
    B  &\quad:\quad A \rightarrow \univ{}                               && \text{(1)},           \\
    C  &\quad:\quad \pity{a}{A}{B(a) \rightarrow \univ{}}               && \text{(2)}, \text{and}\\
    d  &\quad:\quad \pity{a}{A}{\pity{b}{B(a)}{C(a, b) \rightarrow A}}  && \text{(3)}.
  \end{align*}

  An \alert{interaction system} is a type $A$ equipped with an interaction structure.
\end{frame}

\begin{frame}{Formal Topologies --- as Interaction Systems}
  \large

  A \alert{formal topology} is an interaction system $(B, C, d)$ on some poset $P$ that
  satisfies the following two conditions.

  \begin{enumerate}
    \item \textbf{Monotonicity}:
      \begin{equation*}
        \pity{a~b~c}{A}{d(a, b, c) \sqsubseteq a}.
      \end{equation*}
    \item \textbf{Simulation}:
      \begin{align*}
        &\pity{a'~a}{A}{
          a' \sqsubseteq a \rightarrow\\
            &\quad\pity{b}{B(a)}{%
              \sigmaty{b'}{B(a')}{
                \pity{c'}{C(a', b')}{
                  d(a', b', c') \sqsubseteq d(a, b, c)
                }
              }
            }
        }.
      \end{align*}
  \end{enumerate}
\end{frame}

\begin{frame}{Nuclei}
  \large
  A \alert{nucleus} on a frame $F$ is an endofunction $\nuclnm : \abs{F} \rightarrow \abs{F}$ such
  that:
  \begin{alignat*}{4}
    &\pity{x~y}{\abs{F}}{~&& \nuclapp{x \wedge y}       \quad&&=\quad \nuclapp{x} \wedge \nuclapp{y}}
      &&\qquad\text{[meet preservation],}\\
    &\pity{x~~}{\abs{F}}{~&& x                     \quad&&\sqsubseteq\quad \nuclapp{x}}
      &&\qquad\text{[extensiveness], and}\\
    &\pity{x~~}{\abs{F}}{~&& \nuclapp{\nuclapp{x}} \quad&&\sqsubseteq\quad \nuclapp{x}}
      &&\qquad\text{[idempotence].}
  \end{alignat*}

  \vspace{0.5em}

  \uncover<2>{\Large
    \begin{center}
      This is a meet-preserving, \alert{idempotent monad}!
    \end{center}
  }
\end{frame}

\begin{frame}{Nuclei}
  \large

  \hrule
  \begin{quote}
    A Grothendieck ``topology'' appears most naturally as a modal operator, of the nature
    ``it is locally the case that''.
    \begin{flushright}
      \emph{--- Lawvere~\cite{quantifiers-and-sheaves}}
    \end{flushright}
  \end{quote}
  \hrule

  \vspace{1.5em}

  The set of \alert{fixed points of a nucleus} on a frame is itself a frame.

  \vspace{1em}

  \uncover<2>{
    In the posetal case, we will pick this operator to be the \alert{covering} relation of
    a formal topology.
  }
\end{frame}

\begin{frame}{The covering nucleus --- naive attempt}
  \large

  Let\\
  \quad$\McF{}$ be a formal topology with underlying poset $P$,\\
  \quad$a : \abs{P}$, and\\
  \quad$U : \pow{\abs{P}}$, a downwards-closed subset of $P$.

  \vspace{\baselineskip}

  $\covers{a}{U}$ is inductively defined via two rules.

  \[
    \begin{prooftree}
      \hypo{ a \in U }
      \infer1[$\ruledir{}$]{\covers{a}{U}}
    \end{prooftree}
    \qquad
    \begin{prooftree}
      \hypo{b : B(a)}
      \hypo{\pity{c}{C(a, b)}{\covers{d(a, b, c)}{U}}}
      \infer2[$\rulebranch{}$]{\covers{a}{U}}
    \end{prooftree}
  \]

  \vspace{1em}

  \uncover<2>{%
    \emph{Notice: $\covers{a}{U}$ is a \textbf{structure} and not a \textbf{property}.}
  }
\end{frame}

\begin{frame}{The covering nucleus --- naive attempt}
  $\rhd$ could be shown to be a \alert{nucleus}, \textbf{if it had the type}
  \begin{align*}
    \lhd \quad&:\quad \pow{\abs{P}} \rightarrow \abs{P} \rightarrow \hprop{} \\
    \rhd \quad&:\quad \pow{\abs{P}} \rightarrow \pow{\abs{P}}
  \end{align*}
  but its type is
  \begin{align*}
    \lhd \quad&:\quad \pow{\abs{P}} \rightarrow \abs{P} \rightarrow \univ{}.
  \end{align*}

  \uncover<2>{%
    \Large
    \begin{center}
      \emph{Idea: use propositional truncation.}
    \end{center}
  }
\end{frame}

\begin{frame}{The covering nucleus --- naive attempt}
  \large

  \textbf{Need to show}: $\trunc{\_ \lhd \_}$ is a nucleus.

  \vspace{1em}

  This involves showing it is idempotent:
  \begin{equation*}
    \trunc{\_ \lhd \trunc{\_ \lhd U}} \quad\subseteq\quad \trunc{\_ \lhd U},
  \end{equation*}
  for which we need to prove a lemma stating:
  \begin{equation*}
    \covers{a}{U}
    \times
    \left(\pity{u}{\abs{P}}{u \in U \rightarrow \trunc{\covers{u}{V}}\right) \rightarrow \trunc{\covers{a}{V}}}.
  \end{equation*}
\end{frame}

\begin{frame}{The covering nucleus --- naive attempt}
  In the $\rulebranch{}$ case of an attempted proof, the inductive hypothesis gives us
  \begin{equation*}
    \pity{c}{C(a, b)}{\trunc{\covers{d(a, b, c)}{V}}},
  \end{equation*}
  but what we need is:
  \begin{equation*}
    \trunc{\pity{c}{C(a, b)}{\covers{d(a, b, c)}{V}}}.
  \end{equation*}

  \vspace{1em}

  \uncover<2->{
    \begin{center}
      \Large
      This would require (a form of) the Axiom of Choice.

      In fact, the form of choice needed is \textbf{provably}
      false~\cite[pg.~120, Lemma 3.8.5]{hottbook}.
    \end{center}
  }
\end{frame}

\begin{frame}{The covering nucleus --- fixed}
  As we cannot truncate, we \emph{revise} the inductive definition of $\lhd$ to be a
  \alert{higher inductive type}.

  \vspace{\baselineskip}

  \hrule
  \begin{equation*}
    {
      \begin{prooftree}
        \hypo{ a \in U }
        \infer1[$\ruledir{}$]{\covers{a}{U}}
      \end{prooftree}
    }
    \qquad
    {
      \begin{prooftree}
        \hypo{b : B(a)}
        \hypo{\pity{c}{C(a, b)}{\covers{d(a, b, c)}{U}}}
        \infer2[$\rulebranch{}$]{\covers{a}{U}}
      \end{prooftree}
    }
  \end{equation*}
  \vspace{1em}
  \begin{equation*}
    {
      \begin{prooftree}
        \hypo{p : \covers{a}{U}}
        \hypo{q : \covers{a}{U}}
        \infer2[$\rulesquash{}$]{p = q}
      \end{prooftree}
    }
  \end{equation*}
  \hrule

  \uncover<2>{%
    \begin{center}
      \Large
      The mentioned lemma is now provable without choice \emph{and} the type is
      propositional!
    \end{center}
  }
\end{frame}

\begin{frame}{Generating frames from formal topologies}
  \large

  We can now summarise the procedure for generating a frame from a formal topology.
  \begin{enumerate}
    \item Start with formal topology $\McF{}$ with underlying poset $P$.
    \item Take the frame of downwards-closed subsets of $P$, denoted $P\downarrow$.
    \item $\rhd : P\downarrow \rightarrow P\downarrow$ is a nucleus.
    \item The generated frame is the \alert{frame of fixed points} of this nucleus
      (denoted $\mathfrak{fix}\left(P\downarrow, \rhd\right)$).
  \end{enumerate}
\end{frame}

\section{Formal topologies present}

\begin{frame}{Flat monotonic maps}
  To state the presentation theorem, we will have to talk about meet-preserving monotonic
  maps between posets.

  \vspace{0.5em}

  However, we are working with posets which may or may not have meets.

  \vspace{0.5em}

  The solution is to consider those monotonic maps preserving \alert{latent meets}: these
  are called \alert{flat monotonic maps}.
  \begin{alignat*}{4}
    & &&\top_F &&= &&\hspace{0.55em}\bigvee \{ f(a) ~|~ a : \abs{P} \}\\
    &\pity{a~b}{\abs{P}}{&&f(a) \wedge f(b) &&= &&\bigvee_{(i, \_) : I} f(i)}.
  \end{alignat*}
\end{frame}

\begin{frame}{Representation}
  Let $\McF{}$ be a formal topology, $R$, a frame, and $f : \abs{\McF{}} \rightarrow \abs{F}$, a
  function.

  \vspace{1em}

  We say that $f$ \alert{represents} $\McF{}$ in $R$ if:
  \begin{equation*}
    \pity{a}{A}{\pity{b}{B(a)}{f(a) \sqsubseteq \bigvee_{c : C(a, b)} f(d(a, b, c))}}.
  \end{equation*}
\end{frame}

\begin{frame}[fragile]{The main theorem}
  \textbf{Theorem.} Given
  \begin{itemize}
    \item a formal topology $\McF{}$ with underlying poset $P$,
    \item a frame $R$, and
    \item a \textbf{flat} monotonic map $f : \abs{\McF{}} \rightarrow \abs{R}$;
  \end{itemize}
  \begin{center}
    if $f$ represents $\McF{}$ in $R$, then there exists a \textbf{unique} frame
    homomorphism $g : \fix{P\downarrow}{\rhd} \rightarrow R$ making the following diagram commute.
  \end{center}

  \begin{center}
    \begin{tikzcd}[row sep=40pt, column sep=40pt]\label{fig:comm-diag}
      \McF{} \arrow[swap, rd, "f"] \arrow[r, "\eta"]
        & \fix{P\downarrow}{\rhd} \arrow[d, dashed, "g"] \\
        & R
    \end{tikzcd}
  \end{center}
\end{frame}

\begin{frame}{Closing remarks}
  Conclusion.
  \begin{itemize}
    \item We have reconstructed the notion of a covering in the univalent context as an
      HIT.
    \item We have sketched the beginnings of an approach for carrying out formal topology
      in univalent type theory.
  \end{itemize}
\end{frame}

\section{QEF}

\begin{frame}[noframenumbering]{References}
  \printbibliography[heading=none]
\end{frame}

\end{document}
