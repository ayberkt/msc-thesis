\documentclass[xcolor={dvipsnames}]{beamer}
\usepackage{amsmath}
\usepackage{latex/agda}
\usepackage{wasysym}
\usetheme{metropolis}

\title{Formal Topology in Univalent Foundations}
\date{\today}
\author{Ayberk Tosun}
\institute{Chalmers University of Technology}

\setmonofont[Scale=0.85]{PragmataPro Mono Liga}

\definecolor{AgdaFunction}{HTML}{0000CD}
\definecolor{AgdaString}{HTML}{B22222}
\definecolor{codecolour}{RGB}{27, 134, 236}
\definecolor{gerbesred}{RGB}{164, 30, 50}

\newcommand{\fnname}[1]{{\color{codecolour} {\tt #1}}}
\newcommand{\prgoutput}[1]{{\color{codecolour} {\tt #1}}}

\newcommand{\pity}[3]{\prod_{(#1~:~#2)} #3}
\newcommand{\sigmaty}[3]{\sum_{(#1~:~#2)} #3}
\newcommand{\pow}[1]{\mathcal{P}\left(#1\right)}
\newcommand{\univ}{\mathsf{Type}}
\newcommand{\trunc}[1]{\left\| #1 \right\|}
\newcommand{\is}{:\equiv}

\newcommand{\covers}[2]{#1 \LHD #2}

%% Color customisation.

\begin{document}

\maketitle

\begin{frame}{What is topology?}
  \Large
  A topological space is a set $X$ together with a collection $\Omega(X)$ of its subsets
  such that
  \begin{itemize}
    \item $\emptyset, X \in \Omega(X)$,
    \item $\Omega(X)$ is closed under \alert{finite} intersections, and
    \item $\Omega(x)$ is closed under \alert{arbitrary} unions.
  \end{itemize}
\end{frame}

\begin{frame}{What is topology?}
  \Large
  \fnname{P}: a program that prints out a sequence of integers.

  \begin{center}
  \prgoutput{7~~11~~2~~2~~8~~42~~}~$\cdots$
  \end{center}

  We can consider certain properties \fnname{P}:
  \begin{center}
    ``\fnname{P} eventually prints \fnname{17}''\\
    \vspace{1em}
    ``\fnname{P} prints no more than two \fnname{2}s''
  \end{center}
\end{frame}

\begin{frame}{What is topology?}
  \Large
  \begin{center}
    ``$P$ is an \alert{observable property}''

    \vspace{0.5em}
    $\leftrightarrow$
    \vspace{0.5em}

    There exists a prefix $i$ of the output $\sigma$ at which $P$ is \alert{verified} to
    satisfy $P$: all extensions of $\sigma_i$ satisfy $P$.
  \end{center}
\end{frame}

\begin{frame}{What is topology?}
  Let $\phi_0, \ldots \phi_n$ be a \alert{finite} number of observable properties.

  \vspace{1em}

  Suppose $\phi_0 \wedge \ldots \wedge \phi_n$ holds.

  \vspace{1em}

  There must be \alert{stages} $i_0, \cdots, i_n$ such that $\phi_k$ is verified at stage $i_k$.

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

    Some $\psi_k$ must hold so there exists a stage $i$ at which $\psi_k$ is verified.

    \vspace{1em}

    $\bigvee_i \psi_i$ is hence verified at stage $i$.

    \vspace{1em}

    This means that $\bigvee_i \psi_i$ is \alert{observable}.
\end{frame}

\begin{frame}{What is topology?}
  \Huge
  \begin{center}
    Topology is a mathematical theory of \alert{observable} properties.
  \end{center}
\end{frame}

\begin{frame}{Frames}
  A \alert{frame} is a poset $\mathcal{O}$ such that
  \begin{itemize}
    \item \alert{finite subsets} of $\mathcal{O}$ have \alert{meets},
    \item \alert{all subsets} of $\mathcal{O}$ have \alert{joins}, and
    \item binary meets distribute over arbitrary joins:
      \begin{equation*}
        a \wedge \left( \bigvee_{i~\in~I} b_i \right) = \bigvee_{i~\in~I} \left( a \wedge b_i \right),
      \end{equation*}
      for any $a \in \mathcal{O}$ and $I$-indexed family $b$ over $\mathcal{O}$.
  \end{itemize}

  \uncover<2>{
    {\large
      In \alert{type theory}, the quantification over subsets is problematic.
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
  the type of \alert{downward-closed subsets} of $A$ is:
  \[ \sigmaty{U}{\pow{A}}{\pity{x~y}{A}{x \in U \rightarrow y \sqsubseteq x \rightarrow y \in U}}, \]
  \begin{center}
    where
  \end{center}
  \begin{align*}
    &\mathcal{P} : \univ{}_m \rightarrow \univ{}_{m+1}\\
    &\mathcal{P}(A) \is A \rightarrow \mathsf{hProp}_m.
  \end{align*}
\end{frame}

\begin{frame}{Frames --- a prime example}
  This forms a \alert{locale}:
  \begin{align*}
    \top           &\quad\is{}\quad \lambda \_.~ \mathsf{Unit}\\
    A \wedge B       &\quad\is{}\quad \lambda x.~ (x \in A) \times (x \in B)\\
    \bigvee_{i~:~I} B_i &\quad\is{}\quad \lambda x.~ \trunc{\sigmaty{i}{I}{x \in B_i}}
  \end{align*}
\end{frame}

\begin{frame}{Formal Topologies}
  \large
  \begin{quote}
    ``What is formal topology? A good approximation to the correct answer is: formal
    topology is topology as developed in (Martin-Löf's) type theory.''
  \end{quote}

  \vspace{2em}

  \uncover<2>{
    One way to interpret frames \alert{predicatively} is to restrict attention to their
    presentations as \alert{formal topologies}.
  }
\end{frame}

\begin{frame}{Formal Topologies --- as Interaction Systems}
  \large

  An \alert{interaction structure} on some type $A$ comprises three functions.

  \begin{align*}
    B  &\quad:\quad A \rightarrow \univ{}                              \\
    C  &\quad:\quad \pity{a}{A}{B(a) \rightarrow \univ{}}              \\
    d  &\quad:\quad \pity{a}{A}{\pity{b}{B(a)}{C(a, b) \rightarrow A}}
  \end{align*}

  An \alert{interaction system} is a type $A$ equipped with an interaction structure.
\end{frame}

\begin{frame}{Formal Topologies --- as Interaction Systems}
  \large

  A \alert{formal topology} is an interaction system $(B, C, d)$ on some poset $P$ that
  satisfies the following two conditions.

  \begin{enumerate}
    \item \textbf{Monotonicity}: $\forall a~b~c.~d(a, b, c) \sqsubseteq a$.
    \item \textbf{Simulation}:
  \end{enumerate}
\end{frame}

\begin{frame}{Formal Topologies --- as Interaction Systems}
  \begin{code}[hide]
    {-# OPTIONS --cubical #-}

    open import Cubical.Core.Everything renaming (ℓ-max to _⊔_)
    open import Cubical.Foundations.HLevels
    open import Cubical.Foundations.Logic hiding (_⊔_)
    open import Cubical.Data.Sigma using (Σ; Σ-syntax; _×_)

    private
      variable
        ℓ ℓ₀ ℓ₁ ℓ₂ : Level

    postulate
      Poset : (ℓ₀ ℓ₁ : Level) → Type ((ℓ-suc ℓ₀) ⊔ (ℓ-suc ℓ₁))
      ∣_∣ₚ  : Poset ℓ₀ ℓ₁ → Type ℓ₀
      rel   : (P : Poset ℓ₀ ℓ₁) → ∣ P ∣ₚ → ∣ P ∣ₚ → hProp ℓ₁

    infix 9 rel
    syntax rel P x y = x ⊑[ P ] y
  \end{code}
  \begin{code}
    InteractionStr : (A : Type ℓ) → Type (ℓ-suc ℓ)
    InteractionStr {ℓ = ℓ} A = Σ[ B ∈ (A → Type ℓ)             ]
                                Σ[ C ∈ ({x : A} → B x → Type ℓ) ]
                                  ({x : A} → {y : B x} → C y → A)

    InteractionSys : (ℓ : Level) → Type (ℓ-suc ℓ)
    InteractionSys ℓ = Σ[ A ∈ Type ℓ ] InteractionStr A
  \end{code}
\end{frame}

\begin{frame}{Formal Topologies --- as Interaction Systems}
  \begin{code}
    hasMono : (P : Poset ℓ₀ ℓ₁) → InteractionStr ∣ P ∣ₚ → Type _
    hasMono P i@(B , C , d) =
      (a : ∣ P ∣ₚ) (b : B a) (c : C b) → [ d c ⊑[ P ] a ]

    hasSimulation : (P : Poset ℓ₀ ℓ₁) → InteractionStr ∣ P ∣ₚ → Type _
    hasSimulation P (B , C , d) =
      (a′ a : ∣ P ∣ₚ) → [ a′ ⊑[ P ] a ] →
        (b : B a) → Σ[ b′ ∈ B a′ ]
          ((c′ : C b′) → Σ[ c ∈ C b ] [ d c′ ⊑[ P ] d c ])

    FormalTopology : (ℓ₀ ℓ₁ : Level) → Type _
    FormalTopology ℓ₀ ℓ₁ = Σ[ P ∈ Poset ℓ₀ ℓ₁ ]
                             Σ[ ℐ ∈ InteractionStr ∣ P ∣ₚ ]
                               hasMono P ℐ × hasSimulation P ℐ
  \end{code}
\end{frame}

\begin{frame}{Cover}
  \large

  Let $\mathcal{F}$ be a formal topology with underlying poset $P$

  \[ \covers{x}{U} \]

  This relation expresses the property of being an \alert{open cover}.
\end{frame}

\end{document}
