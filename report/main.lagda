\input{/home/ayberkt/academic/thesis/report/template/template}
\usepackage{agda}

\usepackage{ebproof}
\usepackage{wasysym}
\usepackage{tikz-cd}

\tikzcdset{
  arrow style=tikz,
  diagrams={>={Straight Barb[scale=0.8]}}
}

\title{Formal Topology in Univalent Foundations}
\author{Ayberk Tosun}

\supervisor{Thierry Coquand}
\departmentofsupervisor{Computer Science and Engineering}

\examiner{Nils Anders Danielsson}
\departmentofexaminer{Computer Science and Engineering}

\division{Logic and Types}

\keywords{topology, domain theory}

\definecolor{darkgreen}{rgb}{0,0.45,0}
\definecolor{darkred}{rgb}{0.45,0,0}
\definecolor{hottviolet}{rgb}{0.45,0,0.45}
\definecolor{hottblue}{rgb}{0,0.45,0.45}

\hypersetup{
  colorlinks = true,
  linkcolor  = darkgreen,
  citecolor  = hottblue
}

\newcommand{\reals}{\mathbb{R}}
\newcommand{\nats}{\mathbb{N}}
\newcommand{\bool}{\mathbf{Bool}}
\newcommand{\ball}[2]{\mathfrak{A}(#1, #2)}
\newcommand{\neighbourhood}[1]{\mathbf{N}(#1)}

\newcommand{\oftyI}[2]{#1\hspace{0.1mm}:\hspace{0.1mm}#2}
\newcommand{\oftyII}[3]{#1~#2:#3}
\newcommand{\refl}{\mathsf{refl}}
\newcommand{\zero}{\mathsf{zero}}
\newcommand{\suc}[1]{\mathsf{suc}\left(#1\right)}

\newcommand{\fiber}[2]{\mathsf{fiber}\left(#1, #2\right)}
\newcommand{\isequiv}[1]{\mathsf{isEquiv}\left(#1\right)}
\newcommand{\idtoeqvnm}{\mathsf{idToEquiv}}
\newcommand{\idtoeqv}[1]{\idtoeqvnm{}\left(#1\right)}
\newcommand{\isdec}[1]{\mathsf{isDecidable}\left(#1\right)}
\newcommand{\isdisc}[1]{\mathsf{isDiscrete}\left(#1\right)}
\newcommand{\typequiv}[2]{#1 \simeq #2}
\newcommand{\logequiv}[2]{#1 \leftrightarrow #2}

\newcommand{\unit}{\mathsf{Unit}}

%% Homotopy levels.
\newcommand{\iscontr}[1]{\mathsf{isContr}\left(#1\right)}
\newcommand{\isprop}[1]{\mathsf{isProp}\left(#1\right)}
\newcommand{\isset}[1]{\mathsf{isSet}\left(#1\right)}
\newcommand{\isofhlevel}[2]{\mathsf{isOfHLevel}\left(#1, #2\right)}

\newcommand{\pity}[3]{\prod_{(#1~:~#2)} #3}
\newcommand{\sigmaty}[3]{\sum_{(#1~:~#2)} #3}
\newcommand{\univ}{\mathcal{U}}
\newcommand{\isaprop}[1]{\mathsf{IsProp}\left(#1\right)}
\newcommand{\hprop}{Ω}
\newcommand{\isaset}[1]{\mathsf{IsSet}\left(#1\right)}
\newcommand{\abs}[1]{\left| #1 \right|}
\newcommand{\trunc}[1]{\left\| #1 \right\|}
\newcommand{\pow}[1]{\mathcal{P}\left(#1\right)}
\newcommand{\sub}[2]{\mathsf{Fam}_{#1}\left(#2\right)}
\newcommand{\indexnm}{\mathsf{index}}
\newcommand{\indexset}[1]{\indexnm{}\left(#1\right)}
\newcommand{\pair}[2]{\langle #1 , #2 \rangle}

\newcommand{\isdcnm}{\hyperref[defn:dc-subset]{\mathsf{DownwardsClosed}}}
\newcommand{\isdc}[1]{\isdcnm{}\left(#1\right)}
\newcommand{\dcsubsetnm}{\mathsf{DCSubset}}
\newcommand{\dcsubset}[1]{\dcsubsetnm{}\left(#1\right)}

\newcommand{\ordernm}{\mathsf{Order}}
\newcommand{\order}[2]{\ordernm{}_{#1}\left(#2\right)}

\newcommand{\posetstrnm}{\mathsf{PosetStr}}
\newcommand{\posetstr}[2]{\posetstrnm{}_{#1}\left(#2\right)}

\newcommand{\posetaxnm}{\mathsf{PosetAx}}
\newcommand{\posetax}[1]{\posetaxnm{}\left(#1\right)}

\newcommand{\poset}{\mathsf{Poset}}

\newcommand{\ismonotonicnm}{\mathsf{IsMonotonic}}
\newcommand{\ismonotonic}[1]{\ismonotonicnm{}\left(#1\right)}

\newcommand{\hasmono}[1]{\mathsf{hasMono}\left(#1\right)}
\newcommand{\hassim}[1]{\mathsf{hasSim}\left(#1\right)}

\newcommand{\vermono}{\hyperref[defn:mono]{monotonicity}}
\newcommand{\versim}{{\color{black} \hyperref[defn:sim]{simulation}}}
\newcommand{\vernucleus}{\hyperref[defn:nucleus]{nucleus}}
\newcommand{\verframe}{\hyperref[defn:frame]{frame}}
\newcommand{\verposet}{\hyperref[defn:poset]{poset}}
\newcommand{\verintrsys}{\hyperref[defn:intr-sys]{interaction system}}

\newcommand{\ruledir}{{\color{darkred} \mathsf{dir}}}
\newcommand{\rulebranch}{{\color{darkred} \mathsf{branch}}}
\newcommand{\rulesquash}{{\color{darkred} \mathsf{squash}}}

\newcommand{\fix}[2]{\mathsf{fix}\left(#1, #2\right)}

\newcommand{\monotonicmapnm}{\rightarrow_m}
\newcommand{\monotonicmap}[2]{#1 \rightarrow_m #2}

\newcommand{\isflat}[1]{\mathsf{isFlat}\left(#1\right)}

\newcommand{\framestrnm}{\mathsf{FrameStr}}
\newcommand{\framestr}[1]{\framestrnm{}\left(#1\right)}
\newcommand{\frameax}[1]{\mathsf{FrameAx}\left(#1\right)}

\newcommand{\treestrnm}{\mathsf{TreeStr}}
\newcommand{\treestr}[1]{\treestrnm{}\left(#1\right)}

\newcommand{\stumpnm}{\mathsf{Stump}}
\newcommand{\stump}[1]{\stumpnm\left(#1\right)}

\newcommand{\refines}[2]{#1~\mathcal{R}~#2}

\newcommand{\disciplinestrnm}{\mathsf{DisciplineStr}}
\newcommand{\disciplinestr}[1]{\disciplinestrnm{}\left(#1\right)}

\newcommand{\rawframestrnm}{\mathsf{RawFrameStr}}
\newcommand{\rawframestr}[3]{\rawframestrnm{}_{#1, #2}\left(#3\right)}

\newcommand{\isnuclearnm}{\mathsf{isNuclear}}
\newcommand{\isnuclear}[1]{\isnuclearnm{}\left(#1\right)}
\newcommand{\nucleus}[1]{\mathsf{Nucleus}}

\newcommand{\meet}[2]{#1 \wedge #2}
\newcommand{\joinnm}[3]{\bigvee}
\newcommand{\join}[3]{\joinnm{}_{#1~:~#2} #3}

\newcommand{\covernm}{\LHD}
\newcommand{\covers}[2]{#1 \covernm{} #2}

\newcommand{\bF}{\mathbf{F}}
\newcommand{\bG}{\mathbf{G}}
\newcommand{\McF}{\mathcal{F}}

\newcommand{\is}{:\equiv}

%% Names.
\newcommand{\UF}{Univalent Foundations}

%% \newcommand{\paragraphsummary}[1]{{\color{orange} \textsc{#1}}}
\newcommand{\paragraphsummary}[1]{}
\newcommand{\todo}[1]{
  {\color{red} \texttt{TODO: #1}}
}

\setmainfont{XITS}
\setmathfont{XITS Math}
\setmonofont[Scale=0.85]{PragmataPro Mono Liga}

\begin{document}

\maketitlepage{}

\begin{abstract}
  \todo{Write an abstract.}
\end{abstract}

\begin{acknowledgements}
  \todo{Add acknowledgements here.}
\end{acknowledgements}

\makelists{}

\input{introduction}

\input{foundations}

\input{frames}

\input{formal-topology}

%% \input{examples}

\makebackmatter{}

\end{document}
