\chapter{Formal Topology}\label{chap:formal-topo}

\paragraphsummary{Motivate formal topology.}
Our motivation for pointless topology was that it allows us to interpret topology in
constructive terms. The goal of developing topology in type theory presents further
challenges: we must be able to develop our results in a completely predicative way as
well. The definition of a frame we have seen suffers from impredicativity. We will not be
able to instantiate it to topologies we are interested in, the culprit being the join
operator.

\paragraphsummary{Introduce the tree type.}
To present frames, we will make use of the idea of tree set constructors, originally due
to Petersson and Synek~\cite{tree-sets}, who were trying to generalise Martin-Löf's
$\mathsf{W}$ type so that it could accommodate mutually inductive types. It is remarkable
that these structures embody the essence of a Post system in type theory. Tree set
constructors are also called interaction systems~\cite{hancock-interaction-systems} and
indexed containers~\cite{indexed-containers}; we will prefer the term interaction systems.
This chapter corresponds to the Agda module \texttt{TreeType} in the formal development.

\section{Petersson and Synek's tree set constructors}

\paragraphsummary{Explain the idea of the tree type.}
The fundamental idea of an interaction system is simple. Consider the progression of a
two-player game. First, there is a type of \emph{game states}; call it $A$:
\begin{equation*}
  A~:~\univ.
\end{equation*}
At each state of the game, there are certain moves the player can take. In other words,
for every game state $x~:~A$, there is a type of possible moves the player may take.
Formally, this is a function:
\begin{equation*}
  B~:~A \rightarrow \univ.
\end{equation*}
Furthermore, for every move the player may take, the opponent can take certain
counter-moves in response. Formally:
\begin{equation*}
  C~:~\pity{x}{A}{B(x) \rightarrow \univ}.
\end{equation*}
Finally, given the counter-move in response to a certain move at some state, we proceed to
a new game state. This is given by some function:
\begin{equation*}
  d~:~\pity{x}{A}{\pity{y}{B(x)}{C(x, y) \rightarrow A}}.
\end{equation*}
In four pieces, namely $(A, B, C, d)$, we express a ``game-like system'' in a very general
way. Even though the game analogy is very useful, the tree type is more general: it
expresses \emph{anything} that is like a dialogue i.e., two subjects interacting with each
other.

\paragraphsummary{Explain how we will use the tree type.}
Our presentation of frames will be based on this notion of interaction system, based upon
an idea of Coquand~\cite{coq-posets}. We will have to impose three additional requirements
on an interaction system.
\begin{enumerate}
  \item The type $A$ is equipped with a partial order. We will view this order as ranking
    states with respect to how \emph{refined} they are. This might be counter-intuitive at
    first: the more informative the states are, the smaller they will be. The sense of
    this ordering is: the more informative a state is, there will be less sequences of
    interactions that pass through that state. It is like an open ball that encircles its
    center more tightly; hence it is smaller.
  \item The ordering on $A$ satisfies the \emph{monotonicity} requirement: for every state
    $x~:~A$, $d(x) \sqsubseteq x$. In other words, the states that we proceed to via interaction are
    always at least as informative as the previous ones.
\end{enumerate}
We will call an interaction system that satisfies (1) and (2) a \emph{discipline}, (in the
sense that the states resemble a discipline of knowledge, which we will explain later).
The final requirement is (3):
\begin{enumerate}
  \item The poset satisfies the \emph{simulation property} which states that at any state
    we simulate the previous states.
\end{enumerate}

\paragraphsummary{Formally define the tree type.}
Let us now formally define the tree type.
\begin{defn}[Tree type]
  For simplicity, we will require all types to be at the same level $m$ and omit this fact
  in the notation.
  \begin{align*}
    \treestr{A} &\quad\is\quad
      \sigmaty{B}{A \rightarrow \univ}{
        \sigmaty{C}{\pity{x}{A}{B(x) \rightarrow C}}{
          \pity{x}{A}{\pity{y}{B(x)}{C(x, y) \rightarrow A}}
        }
      }\\
    \mathsf{Tree} &\quad\is\quad \sigmaty{A}{~~~~\univ}{\treestr{A}}
  \end{align*}
  Given a tree type structure $\mathcal{T}$, we will refer to its components as
  $B_{\mathcal{T}}, C_{\mathcal{T}}$, and $d_{\mathcal{T}}$.
\end{defn}

\paragraphsummary{Formally define disciplines.}
\begin{defn}[Discipline]
  \begin{align*}
    \mathsf{Discipline} \quad&\is\quad \sigmaty{P}{\poset{}}{\disciplinestr{P}}                 \\
    \disciplinestr{P}   \quad&\is\quad \hspace{-0.9em}\sigmaty{\mathcal{T}}{\treestr{\abs{P}}}{
      \pity{x}{\abs{P}}{\pity{y}{B_{\mathcal{T}}(x)}{
          \pity{z}{C_{\mathcal{T}}(x, y)}{d_{\mathcal{T}}(x, y, z) \sqsubseteq x}}
      }
    }
  \end{align*}
  We will refer to this as the monotonicity property \emph{of a discipline}. This is not
  to be confused with the monotonicity of a monotonic map.
\end{defn}

\paragraphsummary{Formally define the simulation property.}
The only remaining thing towards our definition of formal topology is the aforementioned
property of simulation. We will first define this formally and justify it conceptually
afterwards.
\begin{defn}[Simulation property]
  Given a discipline $D$, we will say that it satisfies the simulation property if the
  following type is inhabited:
  \begin{equation*}
    \pity{x~x'}{\abs{D}}{
      x' \sqsubseteq x \rightarrow \pity{y}{B(x)}{
        \sigmaty{y'}{B(x')}{
          \pity{z'}{C(x', y')}{
            \sigmaty{z}{C(x, y)}{
              d(x', y', z') \sqsubseteq d(x, y, z)
            }
          }
        }
      }
    }.
  \end{equation*}
\end{defn}

\paragraphsummary{Intuitive justification.}
What does this say intuitively? At more refined stages we can always find a counterpart to
any experiment from a less refined stage, in the sense that that experiment will lead to a
more refined stage. To put it more succinctly:
\begin{quote}
  \emph{lower stages can always simulate upper stages}.
\end{quote}

\paragraphsummary{Define formal topology.}
Once the property of simulation has been defined it is easy to state our
definition of a formal topology.
\begin{defn}[Formal topology]
  A formal topology is a discipline satisfying the simulation property.
\end{defn}

\section{Cover relation}

\paragraphsummary{Motivate and provide historical summary.} The reason we defined the
notion of a formal topology is that it admits a cover relation. This method goes back to
Johnstone's~\cite{stone-spaces} adaptation of the notion of a Grothendieck topology, that
was subsequently developed by Martin-L\"{o}f and Sambin~\cite{int-formal-spaces}. The
original formulation of Sambin suffered from the problem that it was not possible to
define the coproduct of two frames using it. This problem was solved by Coquand, Sambin,
and others~\cite{coq-sambin} by defining the cover relation inductively. It is this method
that we will follow in this development.

\paragraphsummary{Defn.~of coverage.}
First, we define the cover relation on a given formal topology. Given a formal topology
$\mathcal{F}$ on set $A$, and given $a~:~A$, $U : \pow{A}$, the type $\covers{a}{U}$ may
be inhabited via the following rules.
\begin{defn}[Cover relation]
  \[
  \begin{prooftree}
    \hypo{ a \epsilon U }
    \infer1[\textsf{dir}]{\covers{a}{U}}
  \end{prooftree}
  \qquad
  \begin{prooftree}
    \hypo{ \left(
      \pity{b}{B(a)}{
        \pity{c}{B(a, b)}{\covers{d(a, b, c)}{U}} \right) \rightarrow \covers{a}{U}
      }
    }
    \infer1[\textsf{branch}]{\covers{a}{U}}
  \end{prooftree}
  \]
\end{defn}

\paragraphsummary{Cover is a nucleus.}
This coverage relation gives us a way of obtaining a frame from a formal topology. Let us
examine its type:
\begin{equation*}
  \_\covernm{}\_ : A \rightarrow \pow{A} \rightarrow \univ{},
\end{equation*}
which we can flip to get
\begin{equation*}
  \_\RHD\_ : \pow{A} \rightarrow A \rightarrow \univ{}.
\end{equation*}
\emph{If only} this had codomain $\hprop{}$ rather than $\univ{}$, we would have been able
to write it like:
\begin{equation*}
  \_\RHD\_ : \pow{A} \rightarrow \pow{A}.
\end{equation*}
We could then restrict this to get an endofunction on the set of downwards-closed subsets:
\begin{equation*}
  \_\RHD\_ : \dcsubset{A} \rightarrow \dcsubset{A}.
\end{equation*}
which of course requires us to show that given a downwards-closed subset $U$,
$\covers{\_}{U}$ is a subset that is downwards-closed. But first, we have to deal with the
problem that the codomain of $\LHD$ is not $\hprop{}$. It turns out that this is not a
straightforward problem to solve.

The $\covers{}{}$ relation has two constructors so it is not propositional. One would then
be tempted to define this relation as the truncation of $\covers{}{}$. When we do this, it
becomes impossible to prove the idempotence law for the purported nucleus $\RHD :
\dcsubset{A} \rightarrow \dcsubset{A}$. Why exactly is that? To prove the idempotence law:
\begin{equation*}
  \trunc{\covers{a}{\trunc{\covers{-}{U}}}} \rightarrow \trunc{\covers{a}{U}},
\end{equation*}
we need a lemma that says, given any $a$, and subsets $U, V$,
\begin{center}
  if $\trunc{\covers{a}{U}}$ and $\trunc{\covers{a'}{V}}$, for every $a'$, then
  $\trunc{\covers{a}{V}}$.
\end{center}
The $\mathsf{dir}$ case is easily verified. The $\mathsf{branch}$ case, however, results
in a situation where we are trying to show
\begin{equation*}
  \trunc{\pity{c}{C(a, b)}{\covers{d(a, b, c)}{V}}}
\end{equation*}
whereas all we get from the inductive hypothesis is
\begin{equation*}
  \pity{c}{C(a, b)}{\trunc{\covers{d(a, b, c)}{V}}}.
\end{equation*}
An inference of the former of the latter would require exactly the axiom of countable
choice~\cite{axiom-of-choice}.

One way to solve this problem is by using HITs. The idea is due to Thierry Coquand.
\todo{Explain the solution.}

\begin{thm}
  Given any subset $U$, $\covers{\_}{U}$ is a downwards-closed subset.
\end{thm}
\begin{proof}
  \todo{Complete the proof.}
\end{proof}

Now, our method of obtaining a frame out of a formal topology is the following.
\begin{enumerate}
  \item Start with a formal topology $\mathcal{T}$ on type $A$.
  \item $\mathcal{T}$ has an underlying poset $P$; construct its frame of downwards-closed
    subsets.
  \item Note: $\covers{\_}{\_}$ is a nucleus on the frame of downwards-closed subsets.
  \item We have shown (in Theorem~\ref{thm:fixed-point-frame}) that the set of
    fixed-points of every nucleus is a frame. The final frame is this fixed-point frame
    on the frame of downwards-closed subsets by the nucleus $\covers{\_}{\_}$.
\end{enumerate}

\section{Discipline presentations present}

\paragraphsummary{Explain the aim.}
We are now ready to shift our focus on what can be called main theorem of this thesis: our
notion of a formal topology is capable of presenting a frame. Let $A$ be a formal topology
and $L$ a frame. Consider a monotonic function $f : \abs{A} \rightarrow \abs{L}$ on the underlying
posets. We will define a notion of $f$ representing $F$ in $L$ which is to say $f$ encodes
crucial information about $F$ inside $L$.

\begin{defn}[Representation]
  \begin{equation*}
  \pity{x}{A}{\pity{y}{B(x)}{f(x) \sqsubseteq \left( \bigvee_{z~:~C(x, y)} f(d(x, y, z))}} \right)
  \end{equation*}
\end{defn}

\todo{State and prove the main theorem.}
