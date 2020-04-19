\chapter{Frames}\label{chap:frames}

In this chapter, we develop the notion of a frame in \UF{}. In Chapter~\ref{chap:intro},
we explained that a frame is the algebra of a logic of finitely verifiable properties.
Recall that a frame consists of the following:
\begin{itemize}
  \item a set $O$ of \emph{opens},
  \item a partial order $\_\sqsubseteq\_ \subseteq O \times O$, corresponding to the set-inclusion order of the
    open subsets,
  \item finite meets, and
  \item arbitrary joins.
\end{itemize}

In addition to these, there is a law that is needed to ensure the correct interplay
between meets and joins. Suppose that we have the observable property $\phi$ and the family
of observable properties $\psi_0, \psi_1, \cdots$. Consider the expression:
\begin{equation*}
  A \cap (\bigcup_i B_i).
\end{equation*}
where $A$ is a set and $B$ is a family of sets. By set-theoretic reasoning, this is the
same thing as:
\begin{equation*}
  \bigvee_i (\phi \wedge \psi_i).
\end{equation*}
As we are trying to characterise the behaviour of open ``sets'' without defining them as
sets of points, we have to explicitly add this distributivity law into the definition of
frame:
\begin{center}
  \emph{binary meets must distribute over arbitrary joins.}
\end{center}

As a brief digression, let us note that it is natural to consider the question: what
happens if we leave out this requirement of distributivity? The resulting structure is
called a \emph{basic topology} and is studied in the work of Sambin

\paragraphsummary{Structure of chapter.}
We now start presenting our formal development of frames. We start with partially ordered
sets in Section~\ref{sec:poset}, which underlie frames. In Section~\ref{sec:frame}, we
present the definition of a frame. In Section~\ref{sec:frame-univ}, we present an
important theorem unique to \UF{}: isomorphic frames are equal. In Sections
\ref{sec:down-set-frame} and \ref{sec:nuclei}, we prove two important theorems in
preparation for the succeeding Chapter~\ref{chap:formal-topo} on formal topology: (1) the
set of downward-closed subsets of a poset forms a frame and (2) given a nucleus (a
technical notion to be introduced) on a frame, its set of fixed points is itself a frame.

\section{Partially ordered sets}\label{sec:poset}

\begin{defn}[Poset]\label{defn:poset}
  Given some $\oftyI{A}{\univ{}_m}$, let $\order{n}{A} \is A \rightarrow A \rightarrow \hprop{}_n$. Notice the
  generality of the universes: the codomain of the relation is permitted to be on a level
  different than that of the carrier set. A poset at carrier level $m$ and relation level
  $n$ is then defined as:
  \begin{equation*}
    \mathsf{Poset}_{m, n} \quad\is\quad \sigmaty{A}{\univ_m}{\posetstr{n}{A}},
  \end{equation*}
  \begin{center}
  where
  \end{center}
  \begin{align*}
    \posetstr{n}{A} \quad\is&\quad \sigmaty{R}{\order{n}{A}}{\posetax{A, R}}\\
    \posetaxnm \quad:&\quad \pity{A}{\univ{}_m}{\order{n}{A} \rightarrow \univ_{\max(m, n)}}\\
    \posetax{A, R} \quad\is&\quad ~\pity{x}{A}{R(x, x)}\\
                      \times&~\pity{x~y~z}{A}{R(x, y) \rightarrow R(y, z) \rightarrow R(x, z)}\\
                      \times&~\pity{x~y}{A}{R(x, y) \rightarrow R(y, x) \rightarrow x =_A y}\\
                      \times&~\isaset{A}
  \end{align*}
\end{defn}

\paragraphsummary{Clarify notation.}
Given a poset $P$, we will refer to its relation as $\_\sqsubseteq_P\_$ (in cases where there might
be ambiguity) and the underlying set of $P$ as $\abs{P}$. Notice that the fourth component
of $\posetax{A, R}$ requires the carrier set to be an \hyperref[defn:hset]{h-set}.

Given a poset $P$ we will talk about its \emph{downward-closed subsets}: sets that include
all elements below their elements. This notion embodies the idea of verification at a
certain stage of information. Take a certain element $x : \abs{P}$, that we view as a
stage of information. For some other $y~:~\abs{P}$, $y \sqsubseteq x$ expresses the idea that $y$ is
a \emph{more refined} stage of information i.e., it contains more information hence ruling
out more approximations meaning it admits \emph{less}. Let $U$ be a subset of $\abs{P}$.
The property that $U$ is downward-closed is then expressed as:
\begin{equation*}
  x \epsilon U \rightarrow y \sqsubseteq x \rightarrow y \epsilon U,
\end{equation*}
the intuitive reading of which is: $U$ contains all stages that are ramifications of the
stages it contains. This means that $U$ is an \emph{observable} property: it is secured at
a certain stage in the sense that the reception of more information does not disrupt it.
Let us write this down formally.
\begin{defn}[Downward-closed subset]\label{defn:dc-subset}
  We first define a predicate expressing that a given subset of $P$ is downwards-closed:
  \begin{align*}
    \isdcnm{}   &\quad:\quad  Poset_{m, n} \rightarrow \pow{\abs{P}} \rightarrow \Omega\\
    \isdc{P, U} &\quad\is{}\quad \pity{x~y}{\abs{P}}{x \in U \rightarrow y \sqsubseteq x \rightarrow y \in U}.
  \end{align*}
  By multiple appeals to Proposition~\ref{prop:pi-prop}, it suffices to show that the
  inner-most expression inside the nested $\prod$ type is propositional which is immediate
  since the codomain of $U$ is \hyperref[defn:hprop]{propositional}. We then define the
  type of downwards-closed subsets of a poset as:
  \begin{align*}
    \dcsubsetnm{} &\quad:\quad \mathsf{Poset}_{m, n} \rightarrow \univ_{\max(m+1, n)}\\
    \dcsubset{P}  &\quad\is{}\quad \sigmaty{U}{\pow{\abs{P}}}{\isdc{P, U}}.
  \end{align*}
\end{defn}

So far we have dealt with two notions of \emph{observable property} throughout the
development:
\begin{enumerate}
  \item element of a poset which we will eventually view like pointless versions of an
    open set with the order corresponding to the subset-inclusion order, and
  \item the notion of downwards-closed subset which expresses that a property of the poset
    of opens behaves like an observational property.
\end{enumerate}
We will now start relating these two by showing that the set of downwards-closed subsets
of a poset is itself a poset, and indeed, we will prove later (in
Sec.~\ref{sec:down-set-frame}) that it actually forms a frame meaning downwards-closed
subsets satisfy our expectations from properties we view as observable.

Let us start by showing that $\dcsubset{P}$ is a set.
\begin{prop}\label{isSetDCSubset}
  $\dcsubset{P}$ is a set for every poset $P$.
\end{prop}
\begin{proof}
  By Proposition~\ref{prop:sigma-set}, it suffices to show that $\pow{\abs{P}}$ is a set
  and $$\isdc{P, U}$$ is a set for every $\oftyI{U}{\pow{\abs{P}}}$. The former holds by
  Proposition~\ref{prop:pow-set}. For the latter, observe that every $\isdc{P, U}$ is a
  proposition by definition meaning it is also set by Proposition~\ref{prop:prop-is-set}.
\end{proof}

Now we can proceed to construct the poset of downwards-closed subsets.
\begin{thm}(Poset of downward-closed subsets)\label{thm:dc-poset}
  Let $P$ be a poset. The type $\dcsubset{P}$ forms a poset under the
  inclusion relation.
\end{thm}
\begin{proof}
  The fact that $\dcsubset{P}$ is a set is given by Proposition~\ref{isSetDCSubset} so it
  suffices to show that the poset axioms are satisfied. Reflexivity and transitivity are
  immediate. For antisymmetry, let $U, V \in \pow{\abs{P}}$ and assume $U \subseteq V$, $V \subseteq U$. By
  function extensionality, it suffices to show that for every $x : \abs{P}$, $U(x) =
  V(x)$. Since $\oftyII{U(x)}{V(x)}{\Omega}$, it is sufficient to show $U(x) \leftrightarrow V(x)$ which is
  immediate
  by assumptions.
\end{proof}

\subsection{Monotonic functions}

The morphisms between two partially ordered sets are monotonic functions.

\begin{defn}[Monotonic function]
  Let $P, Q$ be posets. A function $f : \abs{P} \rightarrow \abs{Q}$ is monotonic if the following
  type is inhabited:
  \begin{equation*}
    \ismonotonic{f} \quad\is\quad \pity{x~y}{\abs{P}}{x \sqsubseteq_P y \rightarrow f(x) \sqsubseteq_Q f(y)}.
  \end{equation*}
  We collect the type of monotonic functions between $P$ and $Q$ in the following type:
  \begin{equation*}
    \monotonicmap{P}{Q} \quad\is\quad \sigmaty{f}{\abs{P} \rightarrow \abs{Q}}{\ismonotonic{f}}
  \end{equation*}
\end{defn}

\begin{defn}[Poset isomorphism]
  An isomorphism between two posets is a monotonic function with a monotonic inverse.
\end{defn}

\section{Definition of a frame}\label{sec:frame}

We now proceed to define frames.
\begin{defn}[Frame]\label{defn:frame}
  A frame structure on some type $A$ consists of (1) a poset structure, (2) a top element
  (3) a binary meet operation, and (4) a join operation of arbitrary arity, which we
  define using families:
  \begin{equation*}
    \rawframestr{n}{o}{A} \quad\is\quad \posetstr{n}{A} \times A \times (A \rightarrow A \rightarrow A) \times (\sub{o}{A} \rightarrow A).
  \end{equation*}
  This raw structure must be subject to the following axioms
  \begin{align*}
    \frameax{\sqsubseteq, \top, \wedge, \bigvee} \quad&\is\quad
      \mathsf{IsTop}(\top) \times \mathsf{IsGLB}(\wedge) \times \mathsf{IsLUB}\left( \bigvee \right)
      \mathsf{IsDistr}(\wedge, \bigvee)\\
    \mathsf{isTop}(\top) \quad&\is\quad \pity{x}{A}{x \sqsubseteq \top}\\
    \mathsf{isGLB}(\wedge) \quad&\is\quad \pity{x~y}{A}{(x \wedge y \sqsubseteq x) \times (x \wedge y \sqsubseteq y)}\\
                       &\hspace{0.5em}\times\quad \pity{z~~}{A}{(z \sqsubseteq x) \times (z \sqsubseteq y) \rightarrow z \sqsubseteq x \wedge y}\\
    \mathsf{isLUB}\left(\bigvee\right) \quad&\is\quad
         \pity{F}{\sub{n}{A}}{\pity{x}{A}{x \epsilon F \rightarrow x \sqsubseteq \bigvee_i F_i}}\\
         &\hspace{0.5em}\times \pity{F}{\sub{n}{A}}{\pity{x}{A}{
               \left( \pity{y}{A}{y \epsilon F \rightarrow y \sqsubseteq x}\right) \rightarrow \bigvee_i F \sqsubseteq x
             }}\\
    \mathsf{isDistr}(\wedge, \bigvee) \quad&\is\quad
      \pity{x}{A}{\pity{F}{\sub{n}{A}}{
          x \wedge \bigvee_i F_i} =_A \bigvee_i \left( x \wedge F_i \right)
      }
  \end{align*}
\end{defn}

We will use the notation $\abs{F}$ for referring to the underlying set of a frame, as we
do for posets. Similarly, we will refer to the underlying partial order as $\_\sqsubseteq_F\_$, in
possibly ambiguous contexts.

\begin{prop}
  For every raw frame structure $(\sqsubseteq, \top, \wedge, \bigvee)$, $\frameax{\sqsubseteq, \top, \wedge, \bigvee}$ is a proposition.
\end{prop}
\begin{proof}[Proof sketch]
  By Proposition~\ref{prop:sigma-prop}, it suffices to show that each component is an
  h-prop. For $\mathsf{isTop}$, $\mathsf{isGLB}$, and $\mathsf{isLUB}$ this can be
  concluded by using Proposition~\ref{prop:sigma-prop} and Proposition~\ref{prop:pi-prop}.
  For $\mathsf{isDistr}$, we use Proposition~\ref{prop:pi-prop} followed by the fact that
  the underlying set of a poset is an h-set (by the definition of $\posetaxnm{}$ from
  Definition~\ref{defn:poset}).
\end{proof}

\section{Isomorphic frames are equal}\label{sec:frame-univ}

\todo{
  Prove that isomorphic frames are equal using the structure identity principle developed
  in Section~\ref{sec:sip}. This will consist in showing that definition of a frame with
  frame isomorphism forms a standard notion of structure and that frame axioms are
  propositions.
}

\section{Frame of downward-closed subsets}\label{sec:down-set-frame}

We have constructed, in Theorem~\ref{thm:dc-poset}, the poset of downwards-closed subsets,
where the relation is the subset inclusion relation. We will now construct the
\emph{frame} of downwards-closed subsets, in which the meet is subset intersection and the
join is subset union.

\begin{thm}
  Given a poset $P$, the poset of downwards-closed subsets of $P$ (as constructed in
  Theorem~\ref{thm:dc-poset}), is a frame.
\end{thm}
\begin{proof}
  We start by defining the following $\top, \wedge, and \bigvee$ operations:
  \begin{align*}
    \top       \quad&\is\quad \top_A   && \text{(as constructed in Defn.~\ref{defn:full-set})} \\
    U \wedge V   \quad&\is\quad U \cap V && \text{(as constructed in Defn.~\ref{defn:intersection})}\\
    \bigvee \bF{} \quad&\is\quad \lambda x.~ \trunc{\sigmaty{i}{\indexset{\bF{}}}{x \epsilon \bF{}_i}}
                         && \text{(using truncation as defined in Defn.~\ref{defn:truncation})}
  \end{align*}
  $\top$ and $\cap$ are propositional by construction whereas $\bigvee$ requires a truncation to be
  forced to be propositional. Downwards-closure and the LUB/GLB properties are easy to
  verify. We focus on showing that the distributivity law is satisfied. Let $U$ be a
  downwards-closed subset and $\bF{}$, a family of downward-closed subsets. We must show
  \begin{align*}
    U \cap \left(\lambda x.~ \trunc{\sigmaty{i}{\indexset{\bF{}}}{x \epsilon \bF{}_i}}\right)
      &= \bigvee \left( U \cap \left( \lambda x.~ \trunc{\sigmaty{i}{\indexset{\bF{}}}{x \epsilon \bF{}_i}}\right) \right)\\
      &\equiv \bigvee \left( \lambda x.~ \trunc{\sigmaty{i}{\indexset{\bF{}}}{x \epsilon \bF{}_i}} \times x \epsilon U \right)
  \end{align*}
  which follows by antisymmetry.

  \todo{revise and expand}.
\end{proof}

\section{Nuclei and their fixed points}\label{sec:nuclei}

To prepare for formal topology, we will now define a technical notion called a
\emph{nucleus}. Nuclei are used to describe quotient frames of a frame, which one views as
subspaces of the space corresponding to that frame. They are presented by Johnstone
in~\cite[Sec.~II.2]{stone-spaces}.

The reason we are interested in nuclei is that in Chapter~\ref{chap:formal-topo} we will
be focusing on a particular nucleus on the frame of downward-closed subsets. It is this
nucleus that will allow us to describe the topological structure of our frame by letting
us specify laws that are expected to hold in the resulting frame.
\begin{defn}[Nucleus]\label{defn:nucleus}
  Let $F : \mathsf{Frame}_{m, n, o}$ and $j : \abs{F} \rightarrow \abs{F}$ and endofunction on it.
  We say that $F$ is \emph{nuclear} if the following condition holds:
  \begin{align*}
    \isnuclearnm{}\quad&:\quad (\abs{F} \rightarrow \abs{F}) \rightarrow \Omega                   \\
    \isnuclear{j} \quad&\is\quad
       \pity{x~y}{\abs{F}}{j(\meet{x}{y}) = \meet{j(x)}{j(y)}}  \\
      &\hspace{0.55em}\times\quad \pity{x~~}{\abs{F}}{x \sqsubseteq j(x)}          \\
      &\hspace{0.55em}\times\quad \pity{x~~}{\abs{F}}{j(j(x)) \sqsubseteq j(x)}.
  \end{align*}
  The propositionality is, as usual, a consequence of Proposition~\ref{prop:sigma-prop},
  Proposition~\ref{prop:pi-prop}, and the fact that the carrier set is a set (by the
  definition of $\posetaxnm{}$ from Defn.~\ref{defn:poset}).

  The type of nuclei is then just the $\sum$ type collecting all nuclear endofunctions on a
  frame:
  \begin{equation*}
    \mathsf{Nucleus} \quad\is\quad \sigmaty{j}{\abs{F} \rightarrow \abs{F}}{\isnuclear{j}}.
  \end{equation*}
\end{defn}

\begin{prop}\label{prop:nucleus-mono}
  Every nucleus is monotonic.
\end{prop}
\begin{proof}
  Let $F$ be a frame and $j : \abs{F} \rightarrow \abs{F}$ a nucleus on it. Let
  $\oftyII{x}{y}{\abs{F}}$ and suppose $x \sqsubseteq y$. We need to show that $j(x) \sqsubseteq j(y)$. First,
  notice that $x = \meet{x}{y}$ by antisymmetry since $\meet{x}{y} \sqsubseteq x$ and $x \sqsubseteq
  \meet{x}{y}$ as $\meet{x}{y}$ is greater than any other lower bound and $x$ is a lower
  bound as it is less than both itself and $y$.
  \begin{align*}
    j(x) &\quad\sqsubseteq\quad j(\meet{x}{y})                 && [x = \meet{x}{y}]                      \\
         &\quad\sqsubseteq\quad \meet{j(x)}{j(y)}              && [\text{nuclei preserve meets}]         \\
         &\quad\sqsubseteq\quad {j(y)}                         && [\text{$\meet{}{}$ is a lower bound}]  .
  \end{align*}
\end{proof}

We will be interested in the type of inhabitants of a frame that are \emph{fixed} points
for a given nucleus on the frame, i.e., given a frame $F$ and a nucleus $j$ on it,
the type $$\sigmaty{x}{F}{j(x) = x}.$$

\begin{prop}
  The set of fixed points of a nucleus forms a poset.
\end{prop}
\begin{proof}[Proof sketch]
  The proof amounts to forgetting the information of being a fixed point. For
  antisymmetry, we use Proposition~\ref{prop:sigma-prop} along with the fact that the
  carrier set is an h-set (by the definition of $\posetaxnm{}$ from
  Defn.~\ref{defn:poset}).
\end{proof}

Now, we are ready to prove the main theorem of this section: this poset of fixed points
for a nucleus on a frame is itself a frame. The proof we will present has been adapted to
the type-theoretic setting from Johnstone's proof in \cite[II.2.2, pg.~49]{stone-spaces}.

\begin{thm}\label{thm:fixed-point-frame}
  The set of fixed points for a nucleus $j$ on some frame $F$ forms a frame.
\end{thm}
\begin{proof}
  The binary meets and the top element are taken directly from the frame $F$. The fact
  that the top element is a fixed point of $j$ is easy to verify: $\top \sqsubseteq j(\top)$ by nuclearity
  (Defn.~\ref{defn:nucleus}). For the meet operation, let $\oftyII{x}{y}{\abs{F}}$ such
  that $j(x) = x$ and $j(y) = y$. $x \wedge y \sqsubseteq j(x \wedge y)$ by $N_1$ so it suffices to show $j(x
  \wedge y) \sqsubseteq x \wedge y$. Nuclei preserve meets so $j(x \wedge y) = j(x) \wedge j(y) \sqsubseteq j(x) = x$ and $j(x \wedge
  y) = j(x) \wedge j(y) \sqsubseteq j(y) = y$. This means that $j(x \wedge y)$ is an upper bound of $x$ and
  $y$ hence $j(x \wedge y) \sqsubseteq x \wedge y$.

  We define the LUB on a family $\mathbf{G}$, making use of the LUB $\bigvee^F$ of $F$ but
  applying $j$ on the result:
  \begin{equation*}
    \bigvee \mathbf{G} \quad\is\quad j \left( \bigvee^F \mathbf{G} \right).
  \end{equation*}
  Notice that this is a LUB operator. Let $\bG{}$ be a family of fixed points for $j$ and
  let $x~\epsilon~\bG{}$. $\bigvee^F \mathbf{G}$ is an upper bound of $\bG{}$ so $x \sqsubseteq \bigvee^F \mathbf{G}$.
  Notice also that $\bigvee^F \mathbf{G} \sqsubseteq j \left( \bigvee^F \mathbf{G} \right)$ by ($N_1$). This
  means that $\bigvee$ is an upper operator. Let $u$ be some other upper bound of $\bG{}$ such
  that $j(u) = u$. We need to show that $j \left( \bigvee^F \mathbf{G} \right) \sqsubseteq u$. Since $u =
  j(u)$ it suffices by the monotonicity of $j$ (Prop.~\ref{prop:nucleus-mono}) to show
  $\bigvee^F \mathbf{G} \sqsubseteq u$. As $\bigvee^F \bG{}$ is a LUB, we are done since $u$ is an upper bound
  of $\bG{}$

  It remains to be shown that the infinite distributivity law is satisfied. Let
  $\oftyI{x}{\abs{F}}$ such that $j(x) = x$ and let $\bG{}$ be a family.
  \begin{align*}
    x \wedge \left( \bigvee \bG{} \right)
      &\quad\equiv\quad x    \wedge j\left( \bigvee^F \bG{} \right)      && [x = j(x)]                     \\
      &\quad=\quad j(x) \wedge j\left( \bigvee^F \bG{} \right)      && [N_1]                          \\
      &\quad=\quad j \left( x \wedge \bigvee^F \bG{} \right)        && [\text{distributivity of}\ F]  \\
      &\quad=\quad j \left( \bigvee^F_i x \wedge \bG{}_i \right)                                      \\
      &\quad\equiv\quad \bigvee_i x \wedge \bG{}_i
  \end{align*}
\end{proof}

In the next chapter, we will make use of nuclei to a generate frame from a formal
topology.

\section{Comparison to the Agda formalisation}

In this section, we provide a brief overview of how these constructions look in the Agda
formalisation. Our aim in doing this is to merely give a feel of what the formal
development looks like. The reader uninterested in the Agda formalisation can safely skip
this section.

The definition of posets corresponds directly to the one Sec.~\ref{sec:poset}. Note that
we adopt the convention of using $\mathscr{l}_0$ for the level of the carrier set and
$\mathscr{l}_1$ for the level of relation result.
\begin{code}
{-# OPTIONS --cubical #-}

open import basis

Order : (ℓ₁ : Level) → Type ℓ → Type (ℓ ⊔ suc ℓ₁)
Order ℓ₁ A = A → A → hProp ℓ₁

isReflexive : {A : Type ℓ₀} → Order ℓ₁ A → hProp (ℓ₀ ⊔ ℓ₁)
isReflexive {A = X} _⊑_ =
  ((x : X) → x ⊑ x is-true) , ∏-prop λ x → is-true-prop (x ⊑ x)

isTransitive : {A : Type ℓ₀} → Order ℓ₁ A → hProp (ℓ₀ ⊔ ℓ₁)
isTransitive {ℓ₀ = ℓ₀} {ℓ₁ = ℓ₁} {A = X} _⊑_ = φ , φ-prop
  where
    φ        : Type (ℓ₀ ⊔ ℓ₁)
    φ        = (x y z : X) → (x ⊑ y ⇒ y ⊑ z ⇒ x ⊑ z) is-true
    φ-prop   : isProp φ
    φ-prop   = ∏-prop λ x → ∏-prop λ y → ∏-prop λ z →
                 is-true-prop (x ⊑ y ⇒ y ⊑ z ⇒ x ⊑ z)

isAntisym : {A : Type ℓ₀} → IsSet A → Order ℓ₁ A → hProp (ℓ₀ ⊔ ℓ₁)
isAntisym {ℓ₀ = ℓ₀} {ℓ₁ = ℓ₁} {A = X} A-set _⊑_ = φ , φ-prop
  where
    φ        : Type (ℓ₀ ⊔ ℓ₁)
    φ        = (x y : X) → (x ⊑ y) is-true → (y ⊑ x) is-true → x ≡ y
    φ-prop   : isProp φ
    φ-prop   = ∏-prop λ x → ∏-prop λ y → ∏-prop λ p → ∏-prop λ q → A-set x y

PosetAx : (ℓ₁ : Level) (A : Type ℓ₀) → Order ℓ₁ A → hProp (ℓ₀ ⊔ ℓ₁)
PosetAx {ℓ₀ = ℓ₀} ℓ₁ A _⊑_ = φ , φ-prop
  where
    isPartial  : IsSet A → hProp (ℓ₀ ⊔ ℓ₁)
    isPartial  = λ hset → isReflexive _⊑_ ∧ isTransitive _⊑_ ∧ isAntisym hset _⊑_
    φ          = Σ[ A-set ∈ IsSet A ] (isPartial A-set) is-true
    φ-prop     = isOfHLevelΣ 1 isPropIsSet (is-true-prop ∘ isPartial)

PosetStr : (ℓ₁ : Level) → Type ℓ → Type (ℓ ⊔ suc ℓ₁)
PosetStr ℓ₁ = add-to-structure (Order ℓ₁) (λ A RP → PosetAx ℓ₁ A RP is-true)

Poset : (ℓ₀ ℓ₁ : Level) → Type (suc ℓ₀ ⊔ suc ℓ₁)
Poset ℓ₀ ℓ₁ = Σ (Type ℓ₀) (PosetStr ℓ₁)
\end{code}

The {\color{AgdaFunction} \texttt{add-to-structure}} function is imported from the
\texttt{cubical} library. It is a direct implementation of Mart\'{i}n Escard\'{o}'s
SIP~\cite[Sec.~3.33.1]{escardo-uf-intro}.

It would have been more idiomatic to use records to represent posets in Agda. $\sum$ types
have been used to avoid repeating h-level theorems such as
Proposition~\ref{prop:sigma-set}.
