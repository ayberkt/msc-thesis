\chapter{Formal Topology}\label{chap:formal-topo}

\paragraphsummary{Motivate formal topology.}
We remarked that the motivation for pointless topology is to attain a constructive
understanding of topology, and that this is a prerequisite for being able to express
topology in type theory in a natural way i.e., without postulating classical axioms. This
task of making type-theoretical sense of topology presents another challenge: we must be
able to develop our results in a completely predicative way as well. To address this, we
will use formal topologies which give us a way of \emph{presenting} frames. Instead of
working with frames directly, we will work with formal topologies from which the frames
are freely generated.

This impredicativity springs from the axioms for a \hyperref[defn:frame]{frame} that
quantify over subsets. The LUB axiom for instance requires us to say

\paragraphsummary{Introduce the tree type.}
Our definition of a formal topology will make use of the notion of an interaction system,
first formulated by Petersson and Synek~\cite{tree-sets}, the motivation of whom was to
generalise $\mathsf{W}$ types to be able to accommodate mutual recursion. Other names for
interaction systems include \emph{tree set constructors} (which is the name that Petersson
and Synek~\cite{tree-sets}), and \emph{indexed containers}~\cite{indexed-containers}. The
idea of doing formal topology with interaction systems is due to Coquand~\cite{coq-posets}
who was inspired by Dragalin~\cite{dragalin}.

This chapter corresponds to the Agda module \texttt{TreeType} in the formal development.

\section{Interaction systems}

\paragraphsummary{Explain the idea of the tree type.}
The fundamental idea of an interaction system is simple. Consider the progression of a
two-player game. First, there is a type of \emph{game states}; call it $A$:
\begin{equation*}
  A~:~\univ.
\end{equation*}
At each state of the game, there are certain moves the player can take. In other words,
for every game state $\oftyI{x}{A}$, there is a type of possible moves the player may take.
Formally, this is a function:
\begin{equation*}
  \oftyI{B}{A \rightarrow \univ}.
\end{equation*}
Furthermore, for every move the player may take, the opponent can take certain
counter-moves in response. Formally:
\begin{equation*}
  \oftyI{C}{\pity{x}{A}{B(x) \rightarrow \univ}}.
\end{equation*}
Finally, given the counter-move in response to a certain move at some state, we proceed to
a new game state. This is given by some function:
\begin{equation*}
  \oftyI{d}{\pity{x}{A}{\pity{y}{B(x)}{C(x, y) \rightarrow A}}}.
\end{equation*}

In four pieces, namely $(A, B, C, d)$, we characterise structures that involve some kind
of ``interaction''. Even though the game analogy is useful, interaction systems are more
general than that games: they express anything that is like a dialogue i.e., involving
two parties interacting with each other.

\paragraphsummary{Explain how we will use the tree type.}
To define a formal topology, we will require the type of states ($A$) to be not just a
set, but a poset. The idea of this is the same as in the case of frames, we would like to
view these states as stages of information ranked with respect to how refined they are.
In addition, we will expect such a poset equipped with an interaction system to satisfy
the following two properties:
\begin{enumerate}
\item the monotonicity property: for every state $\oftyI{x}{A}$, experiment
  $y$ on $x$, and outcome $z$ of $y$, $d(x, y, z) \sqsubseteq x$.
  \item the simulation property which states that at any state we simulate the previous
    states.
\end{enumerate}

Once we have imposed the requirement that the set of stages be a poset, it makes sense to
use some more suggestive terminology due to Martin-Löf\footnote{Attributed to
  Martin-Löf in the note~\cite{coq-poset}}.
\begin{itemize}
  \item $A$: a type of stages of \emph{knowledge}.
  \item $\oftyI{B}{A \rightarrow \univ{}}$: a type of \emph{experiments} $B(x)$ that one can perform at a
    certain stage $x$.
  \item $\oftyI{C}{\pity{x}{A}{B(x) \rightarrow \univ{}}}$: a type of \emph{outcomes} of an
    experiment $\oftyI{y}{B(x)}$ for some stage of knowledge $x$.
  \item $d$: a function that expresses the act of \emph{revising} one's belief state based
    on the outcome from an experiment performed at a stage of knowledge.
\end{itemize}
Once we adopt this view, what the monotonicity property says becomes much more clear: if
we perform an experiment $y$ while we have knowledge $x$ and revise our knowledge based on
some outcome $z$ of $y$, the new knowledge we arrive at must contain at least as much
information. In fact, if we would like to view things sensibly as experiments, it makes
sense to reserve this terminology to interaction structures that satisfy this monotonicity
property as experiments must always increase the knowledge state, if they have any effect
at all.

Now, to proceed towards the definition of formal topology, let us first formally define
interaction systems.
\paragraphsummary{Formally define the tree type.}
Let us now formally define the tree type.
\begin{defn}[Interaction system]\label{defn:intr-sys}
  For simplicity, we will require all types to be at the same level $m$ and omit this fact
  in the notation.
  \begin{align*}
    \treestr{A} &\quad\is\quad
      \sigmaty{B}{A \rightarrow \univ}{
        \sigmaty{C}{\pity{x}{A}{B(x) \rightarrow C}}{
          \pity{x}{A}{\pity{y}{B(x)}{C(x, y) \rightarrow A}}
        }
      }\\
    \mathsf{IntrSys} &\quad\is\quad \sigmaty{A}{~~~~\univ}{\treestr{A}}
  \end{align*}
  Given an interaction system $\mathcal{I}$, we will refer to its components as
  $B_{\mathcal{I}}, C_{\mathcal{I}}$, and $d_{\mathcal{I}}$ in context where the possibility of
  ambiguity is present.
\end{defn}

Given an interaction system $\mathcal{I}$, the monotonicity property is then formally
expressed as in the following definition.
\begin{defn}[Monotonicity property of an interaction system]\label{defn:mono}
  Given an interaction system $\mathcal{I}$, it is said to have the monotonicity property
  if the following type is inhabited
  \begin{equation*}
    \mathsf{HasMono}\left( \mathcal{I} \right) \quad\is\quad
    \pity{x}{A_{\mathcal{I}}}{\pity{y}{B_{\mathcal{I}}(x)}{\pity{z}{C_{\mathcal{I}}(x, y)}{
      d(x, y, z) \sqsubseteq x}}.
    }
  \end{equation*}
\end{defn}

Unlike the simpler monotonicity property, we have not yet fully explained the simulation
property. Let us first provide its formal definition.
\begin{defn}[Simulation property]\label{defn:sim}
  Given an interaction system $\mathcal{I}$, we will say that it satisfies the simulation
  property if the following type is inhabited:
  \begin{align*}
    &\mathsf{HasSim}\left( \mathcal{I} \right) \quad\is\\
    &\pity{x~x'}{\abs{D}}{
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
  \end{align*}
\end{defn}
What does this say intuitively? At more refined stages we can always find a counterpart to
any experiment from a less refined stage, in the sense that that experiment will lead to a
finer stage. In other words, as we perform certain experiments and proceed to more refined
stages, we do not lose the ability to perform the experiments we previously did not
perform.

\begin{defn}[Formal Topology]\label{defn:formal-topo}
  A \emph{formal topology} is simply an interaction system satisfying the \vermono{} and
  \versim{} properties.
  \begin{align*}
    \mathsf{FT} \quad\is\quad \sigmaty{\mathcal{I}}{\mathsf{IntrSys}}{
        \hasmono{\mathcal{I}} \times \hassim{\mathcal{I}}
    }
  \end{align*}
\end{defn}

\section{Cover relation}

The real reason we are interested in formal topologies is that the structure they contain,
along with the \vermono{} and \versim{} properties, induces a \emph{covering relation}.
This is a method going back Johnstone's~\cite{stone-spaces} adaptation of the notion of a
Grothendieck topology to the context of locale theory, that was subsequently developed by
Martin-L\"{o}f and Sambin~\cite{int-formal-spaces}.

The idea is as follows: given a set $A$ that we view like a set of \emph{basic opens}
(i.e., opens not made up using the join operator) we require a relation $\_\LHD\_ : A \rightarrow
\pow{A} \rightarrow \Omega$. This relation is expected to pointlessly express the relation of being an
\emph{open cover} i.e., $x \LHD V$ iff $V$ is an open cover of $x$: $x = \bigcup_i V_i$. In
other words, we are specifying which basic opens can be expressed as the union of which
others. The information contained by this relation is sufficient to generate the opens.
In our case, the covering relation will be determined by the interaction system.

The original formulation of formal topology by Sambin suffered from the problem that it
was not possible to define the coproduct of two frames using it. This problem was solved
by Coquand et al.~\cite{coq-sambin} by defining the covering relation inductively.

Now, we will define the cover relation on a given formal topology. However, our
presentation will recapitulate our development: we first explain our naive attempt, that
we found out to not work in \UF{}, and its remedied form that circumvents this problem by
using an HIT.
\begin{defn}[Cover relation (naive)]
  Given a formal topology
  $\mathcal{F}$ on type $A$, and given $\oftyI{a}{A}$, $U : \pow{A}$, the type
  $\covers{a}{U}$ may be inhabited via the following rules.
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

One way of reading $\covers{a}{U}$ is as a relaxation of $a \in U$ to ``it is eventually the
case that $a \in U$''. In other words, it might not be that $a \in U$ but once the knowledge
at level $a$ has been attained, paths that do not lead to $U$ have been ruled out:
regardless of what experiments are run, they will eventually lead to a stage in $U$.

Let us consider the how we will go from a formal topology to a frame via its cover
relation. The cover relation has the following type:
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
  \_\RHD\_ : \pow{A} \rightarrow \pow{A},
\end{equation*}
but it does not as it has two constructors. We could then restrict this to get an
endofunction on the set of downwards-closed subsets:
\begin{equation*}
  \_\RHD\_ : \dcsubset{A} \rightarrow \dcsubset{A}.
\end{equation*}
which of course requires us to show that given a downwards-closed subset $U$,
$\covers{\_}{U}$ is a subset that is downwards-closed. But first, we have to deal with the
problem that the codomain of $\LHD$ is not $\hprop{}$.

It is tempting to try to achieve this by truncating $\covers{}{}$. When we do this, it
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
An inference of the former from the latter would require the use of a well-studied
classical reasoning principle: the axiom of countable choice~\cite{axiom-of-choice}:
\begin{equation*}
  \pity{x}{A}{\trunc{B(x)}} \rightarrow \trunc{\pity{x}{A}{B(x)}}
\end{equation*}

A remedy for this situation was proposed by the supervisor. Instead of truncating the
naive form of the cover relation, we add a higher constructor that \emph{squashes} the
difference between the $\mathsf{dir}$ and $\mathsf{branch}$ constructors. We now provide
the revised form.
\begin{defn}[Cover relation]\label{defn:covering}
  Given a formal topology
  $\mathcal{F}$ on type $A$, and given $\oftyI{a}{A}$, $U : \pow{A}$, the type
  $\covers{a}{U}$ is inductively defined with the following two constructors:
  \[
  \begin{prooftree}
    \hypo{ a \in U }
    \infer1[$\ruledir{}$]{\covers{a}{U}}
  \end{prooftree}
  \qquad
  \begin{prooftree}
    \hypo{\oftyI{b}{B(a)}}
    \hypo{\pity{c}{C(a, b)}{\covers{d(a, b, c)}{U}}}
    \infer2[$\rulebranch{}$]{\covers{a}{U}}
  \end{prooftree}
  \]
  In addition to the constructors, the type $\covers{a}{U}$ contains the following path:
  \begin{equation*}
    \begin{prooftree}
      \hypo{\oftyI{p}{\covers{a}{U}}}
      \hypo{\oftyI{q}{\covers{a}{U}}}
      \infer2[$\rulesquash{}$]{p =_{\covers{a}{U}} q}
    \end{prooftree}
  \end{equation*}
\end{defn}

When trying to prove the idempotence law with this, we get from the inductive hypothesis a
family $\pity{c}{C(a, b)}{d(a, b, c) \LHD V}$ where $d(a, b, c) \LHD V$ is still
``squashed'', but this squashing is an integral part of $\LHD$ rather than a truncation
that is imposed extrinsically upon it. This is sufficient for circumventing the problem
that would have required the axiom of countable choice, and allows us to successfully
complete the idempotence proof. The type of $\_\LHD\_$ can be seen directly to be
$\pow{A} \rightarrow \pow{A} \rightarrow \Omega$ by the existence of the $\mathsf{squash}$ constructor.

Notice that, given a downwards-closed subset $U$, the subset of elements that are covered
by $U$ ($\_ \LHD U$) is itself downwards-closed.
\begin{prop}
  Let $\mathcal{F}$ be an \verintrsys{} and $U$ a downwards-closed subset of its
  underlying poset. $\covers{\_}{U}$ is a downwards-closed subset.
\end{prop}
\begin{proof}
  Let $\oftyII{x}{y}{A}$ such that $\covers{x}{U}$ and $y \sqsubseteq x$. We need to show
  $\covers{y}{U}$. Our proof proceeds by (higher) induction on the proof of
  $\covers{x}{U}$.
  \begin{itemize}
    \item Case $\mathsf{dir}$. It must be that $x \in U$ and hence by the downwards-closure
      of $U$, $y \in U$ meaning $\covers{y}{U}$ by $\mathsf{dir}$.
    \item Case $\mathsf{branch}$. We have some experiment $b$ on $x$ and a function
      $$\oftyI{f}{\pity{c}{C(a, b)}{d(a, b, c) \LHD U}}.$$
      Using the $\mathsf{branch}$ rule, we are done if we can exhibit some experiment
      $\oftyI{b'}{B(y)}$ along with a function
      $$\oftyI{g}{\pity{c'}{C(a, b')}{d(y, b', c') \LHD U}}.$$
      Pick $b'$ to be the experiment given by appealing to the \versim{} property with
      $b$. Let $\oftyI{c'}{C(a, b')}$. It remains to be shown that $d(y, b', c') \LHD U$.
      By the inductive hypothesis, we are done if we can show that $z \sqsubseteq d(y, b', c')$
      for some $z \LHD U$. Pick $z \is d(x, b, c)$ where $c$ is the outcome of $b$ given
      by the \versim{} property. We have $d(x, b, c) \sqsubseteq d(y, b', c')$, directly by the
      \versim{} property and that $d(x, b, c) \LHD U$ by $f(c)$.
    \item Case $\mathsf{squash}$. We are done by appealing to the $\mathsf{squash}$ rule
      with both of the inductive hypothesis.
  \end{itemize}
\end{proof}

\begin{prop}\label{prop:lem1}
\end{prop}
\begin{proof}
  \todo{Complete}.
\end{proof}

\begin{prop}\label{prop:lem3}
\end{prop}
\begin{proof}
  \todo{Complete}
\end{proof}

\begin{prop}\label{prop:lem4}
  Let $\mathcal{F}$ be an \verintrsys{} and $U, V$ be subsets of its underlying poset. If
  $U \subseteq \_ \LHD V$ then $\_ \LHD U \subseteq \_ \LHD V$.
\end{prop}
\begin{proof}
  Let $U, V$ be be subsets of $A$ such that $U \subseteq \_ V$. Let $x \LHD U$. We must show that
  $x \LHD V$. Our proof proceeds by induction on the proof of $x \LHD U$.
  \begin{itemize}
    \item Case: $\mathsf{dir}$. It must be that $x \in U$. We are done since
      $U \subseteq \_ \LHD V$.
    \item Case: $\mathsf{branch}$. By the premises we have an experiment $b$ and a
      function $f$ that gives us $d(a, b, c) \LHD U$ for any outcome $c$ of $b$. By
      appealing to the $\mathsf{branch}$ rule on experiment $b$, we will be done if we can
      exhibit a function
      \begin{equation*}
        \oftyI{g}{\pity{c}{C(x, b)}{d(a, b, c) \LHD V}}.
      \end{equation*}
      Let $\oftyI{c}{C(x, b)}$. $\oftyI{f(c)}{d(x, b, c) \LHD U}$ and hence by the IH:
      $d(x, b, c) \LHD V$.
    \item Case: $\mathsf{squash}$. We combine both inductive hypotheses by the
      $\mathsf{squash}$ rule.
  \end{itemize}
\end{proof}

Our method of obtaining a frame out of a formal topology comprises four steps.
\begin{enumerate}
  \item Start with a formal topology $\mathcal{T}$ on type $A$.
  \item $\mathcal{T}$ has an underlying poset $P$; construct its frame of downwards-closed
    subsets.
  \item Note: $\covers{\_}{\_}$ is a nucleus on the frame of downwards-closed subsets.
  \item We have shown (in Theorem~\ref{thm:fixed-point-frame}) that the set of
    fixed-points of every nucleus is a frame. The final frame is this fixed-point frame
    on the frame of downwards-closed subsets by the nucleus $\covers{\_}{\_}$.
\end{enumerate}
The only missing step is (3): we have not yet shown that the covering relation is a
nucleus. We will do exactly this in the following section.

\section{The covering relation is a nucleus}

$\_\RHD\_ : \pow{A} \rightarrow \pow{A}$ is a endofunction on the powerset of $A$. By restricting
our attention to subsets that are downwards-closed, we can view as an endofunction on a
frame
\begin{equation*}
  \oftyI{\_\RHD\_}{\dcsubset{A} \rightarrow \dcsubset{A}}.
\end{equation*}
The natural question to be asked is then: is this a \vernucleus{} on the frame of
downwards-closed subsets of $A$? Let us recapitulate what this means before we proceed
to the proof.
\begin{itemize}
  \item $N_0$: $\pity{a}{A}{a \LHD U \cap V = (a \LHD U) \cap (a \LHD V)}$,
  \item $N_1$: $U \subseteq \_ \LHD U$, and
  \item $N_2$: $\_ \LHD (\_ \LHD U) \subseteq \_ \LHD U$.
\end{itemize}

\begin{thm}\label{thm:covering-nucleus}
  The covering relation satisfies the nuclearity axioms.
\end{thm}
\begin{proof}
  $N_1$ is direct using the $\mathsf{dir}$ rule. $N_2$ is a direct application of
  Proposition~\ref{prop:lem4}.

  For $N_0$, we construct a proof by induction. Let $\oftyII{U}{V}{\pow{A}}$. We will show
  that $\_ \LHD (U \cap V) = (\_ \LHD U) \cap (\_ \LHD V)$ by antisymmetry. The $(\_ \LHD U) \cap
  (\_ \LHD V) \subseteq \_ \LHD (U \cap V)$ direction follows by Proposition~\ref{prop:lem3}. For the
  other direction, let $\oftyI{a}{A}$ such that $a \LHD U \cap V$. We proceed by induction on
  this proof.
  \begin{itemize}
    \item Case $\mathsf{dir}$. $a \in U \cap V$ meaning $a \in U$ and $a \in V$ hence we are done
      by an two applications of $\mathsf{dir}$.
    \item Case $\mathsf{branch}$. Two appeals to the inductive hypothesis, followed by
      applications of the $\mathsf{branch}$ rule.
    \item Case $\mathsf{squash}$. We combine the two inductive hypothesis using the
      $\mathsf{squash}$ rule.
  \end{itemize}
\end{proof}

\section{Generating a frame from a formal topology}

Now that we have shown the nuclearity of the covering relation $\covers{\_}{\_}$, we have
everything we need for the procedure of generating a \verframe{} from a formal topology.

Let $\McF{}$ be a formal topology. We know by Theorem~\ref{thm:down-set-frame} that the
set of downwards-closed subsets of the underlying poset of $\McF{}$ is a frame; denote
this by $\McF{}\downarrow$. As we know that $\covers{\_}{\_}$ is a nucleus on this frame (by
Theorem~\ref{thm:covering-nucleus}), we know that the set of fixed points for
$\covers{\_}{\_}$ is a frame as well; denote this by $L$. Now, notice that we can define
a map $\eta : A_{\McF{}} \rightarrow \abs{L}$ as follows:
\begin{align*}
  \eta    \quad&:\quad A_{\McF{}} \rightarrow \pow{A_{\McF{}}}\\
  \eta(x) \quad&\is\quad \covers{\_}{x\downarrow}
\end{align*}
where $x\downarrow$ denotes the \emph{downwards-closure} of $x$: $\{ y~|~y \sqsubseteq x \}$. So $y \in \eta(x) \equiv
\covers{y}{x\downarrow}$ is to say ``$y$ leads to a ramification of $x$''. In fact, one can see
that $\eta(x)$ is downwards-closed and a fixed point for $\covers{\_}{\_}$, meaning its type
can be refined to $\oftyI{\eta}{A_{\McF{}} \rightarrow \abs{L}}$.

\begin{defn}[$\eta$]
  Let $\McF{}$ be a formal topology and denote its cover relation by $\covers{\_}{\_}$.
  Let $L \is \fix{\dcsubset{A}}{\_\RHD\_}$. There exists a monotonic map from the
  underlying poset of $P$ of $\McF{}$ to the underlying poset of $L$:
  \begin{align*}
    \eta    \quad&:\quad P \rightarrow_m (\abs{L}, \_\sqsubseteq_L\_)\\
    \eta(a) \quad&\is\quad \covers{\_}{a\downarrow}.
  \end{align*}
  The fact that $\eta$ is monotonic follows from Proposition~\ref{prop:lem1}. It remains to
  be shown that it is a fixed point for $\_\RHD\_$. Let $\oftyI{a}{A_{\McF{}}}$. We need
  to show that $\covers{\_}{(\covers{\_}{a})} = \covers{\_}{a}$. We proceed by
  antisymmetry. $\covers{\_}{a\downarrow} \subseteq \covers{\_}{(\covers{\_}{a\downarrow})}$ follows by $N_1$. The
  other direction is a direct application of Proposition~\ref{prop:lem4}.
\end{defn}

\section{Formal topologies present}

\paragraphsummary{Explain the aim.} We are now ready to shift our focus on what can be
called main theorem of this thesis: our notion of a formal topology is capable of
presenting a frame. Let $\mathcal{F}$ be a formal topology and $F$ a frame. Consider a
monotonic function $f : A_{\mathcal{F}} \rightarrow \abs{F}$ on the underlying posets. We will
define a notion of $f$ representing $F$ in $L$.

\begin{defn}[Representation]\label{defn:rep}
  Given a formal topology $\mathcal{F} = (A, B, C, d)$, a frame $F$, and a function
  $\oftyI{f}{A \rightarrow \abs{F}}$ we say that $f$ represents $\mathcal{F}$ in $F$ if the
  following type is inhabited:
  \begin{equation*}
    \mathsf{represents}\left(\mathcal{F}, F, f\right) \quad\is\quad
      \pity{x}{A}{
        \pity{y}{B(x)}{
          f(x) \sqsubseteq \bigvee_{\oftyI{z}{C(x, y)}} f(d(x, y, z)).
        }
      }
  \end{equation*}
\end{defn}

To state the universal property, we will work with \emph{flat} monotonic maps. This is the
special case of the notion of a \emph{flat functor}~\cite{nlab-flat-functor} in the case
where the categories we are working with are posets. Consider a monotonic map $f : P \rightarrow Q$,
where $Q$ has (finite) products but $P$ does not. We would like to assert somehow that $f$
preserves finite meets but we cannot mention the meets of $P$ because they do not exist.
So what we want to do is to state that $f$ preserves products that \emph{do not exist yet}
which we can do by requiring the following conditions:
\begin{enumerate}
  \item $\top_Q = \bigvee f(P)$, and
  \item $\pity{a~b}{P}{f(a) \wedge f(b) =
           \bigvee f \left( \left\{ z~|~ z \sqsubseteq x\ \text{and}\ z \sqsubseteq y \right\} \right)}$
\end{enumerate}

In our case, we will of course be interested in monotonic maps whose codomains are frames.
\begin{defn}[Flat monotonic map]
  Let $P$ be a \verposet{} and $F$ a \verframe{}. Denote by $I$ the type
  $\sigmaty{z}{\abs{F}}{z \sqsubseteq x \times z \sqsubseteq y}$.
  A monotonic map $f : P \rightarrow F$ from $P$
  to the underlying poset of the frame is called \emph{flat} if the following type is
  inhabited: 
  \begin{align*}
    \isflat{f} \quad&\is\quad \top_F = \bigvee f(P)\\
                &\hspace{0.6em}\times
                \pity{a~b}{P}{f(a) \wedge f(b) = \bigvee_{\oftyI{(i, p)}{I}} f(i)}.
  \end{align*}
\end{defn}

\begin{figure}
  \centering
  \caption{The universal property}
  \begin{tikzcd}[row sep=40pt, column sep=40pt]\label{fig:comm-diag}
    \McF{} \arrow[swap, rd, "f"] \arrow[r, "\eta"] & L \arrow[d, dashed, "g"] \\
                                                & R
  \end{tikzcd}
\end{figure}

Using flat monotonic maps, the universal property can now be stated.

\begin{thm}[Universal property for formal topologies]
  Given any formal topology $\McF{}$, frame $R$, flat monotonic map $f : A_{\McF{}} \rightarrow R$
  from the underlying \verposet{} of $\McF{}$ to the underlying \verposet{} of $R$, that
  \hyperref[defn:rep]{represents} $\McF{}$ in $R$, there exists a unique \textbf{frame
    homomorphism} $\oftyI{g}{L \rightarrow R}$ such that $f = g \circ \eta$, as summarised in
  Fig.~\ref{fig:comm-diag}
\end{thm}
