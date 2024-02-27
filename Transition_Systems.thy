(*<*)
theory Transition_Systems
  imports Main
"HOL-Library.Countable_Set"
begin
(*>*)

section \<open>Labeled Transition Systems\<close>
text \<open>\label{sec:LTS}\<close>

text \<open>As described in \cref{chap::introduction}, labeled transition systems are formal models used to describe the behavior of reactive systems.
A LTS consists of three components: processes, actions, and transitions. Processes represent momentary states or configurations of a system. 
Actions denote the events or operations that can occur within the system. The outgoing transitions of each process 
correspond to the actions the system can perform in that state, yielding a subsequent state. A process may have multiple outgoing transitions labeled with the same or different actions. This signifies that the system can choose any of these transitions non-deterministically
\footnote{Note that "non-determinism" has been used differently in some of the literature (citation needed). In the context of reactive systems, 
all transitions are directly triggered by external actions or events and represent synchronization with the environment.
The next state of the system is then uniquely determined by its current state and the external action. In that sense the behavior of the system is deterministic.}.
The semantic equivalences treated in \cite{GLABBEEK20013} are defined entirely in terms of action relations.
We treat processes as being \textit{sequential}, meaning it can perform at most one action at a time, and instantanious.
Note that many modeling methods of systems use a special $\tau$-action to represent internal behavior. However, in our definition of LTS, 
internal behavior is not considered.\<close>

subsubsection \<open>Definition 2.1.1 (Labeled transition Systems)\<close>

text \<open>A \textit{Labeled Transition System} (LTS) is a tuple $\mathcal{S} = (\Proc, \Act, \rightarrow)$ where $\Proc$ is the set of processes, 
$\Act$ is the set of actions and $\cdot\xrightarrow{\cdot}\cdot$ $\subseteq \Proc \times \Act \times \Proc$ is a transition relation.
We write $p \xrightarrow{\alpha} p'$ for $(p, \alpha, p')\in \rightarrow$.\<close>

text \<open>Actions and processes are formalized using type variable \<open>'a\<close> and \<open>'s\<close>, respectively. As only actions and states involved in the transition relation are relevant, 
the set of transitions uniquely defines a specific LTS. We express this relationship using the predicate \<open>tran\<close>. In Isabelle we associate \<open>tran\<close> with a more readable notation, \<open>p \<mapsto>\<alpha> p'\<close> for $p \xrightarrow{\alpha} p'$.\<close>

locale lts = 
  fixes tran :: \<open>'s \<Rightarrow> 'a \<Rightarrow> 's \<Rightarrow> bool\<close> 
    ("_ \<mapsto>_ _" [70, 70, 70] 80)
begin

text \<open>\textbf{Example 1} (Taken from (Glabbeeck, counterex. 3)) A simple LTS. Depending on how ``close'' we look, we might consider the observable behaviors of $p_1$ and $q_2$ equivalent or not.\<close>

text \<open>
\begin{center}
\begin{tikzpicture}[auto,node distance=1.5cm]
  \coordinate (p1) at (-3,0);
  \node at (-3, 0.2) {$p_1$}; 
  \node[below left of=p1] (p2) {$p_2$};
  \node[below right of=p1] (p3) {$p_3$};
  \node[below of=p2] (p4) {$p_4$};
  \node[below left of=p3] (p5) {$p_5$};
  \node[below right of=p3] (p6) {$p_6$};
  
  \draw[->] (p1) -- node[above] {a} (p2);
  \draw[->] (p1) -- node[above] {a} (p3);
  \draw[->] (p2) -- node[left] {b} (p4);
  \draw[->] (p3) -- node[right] {b} (p5);
  \draw[->] (p3) -- node[left] {c} (p6);

\coordinate (q1) at (3,0);
  \node at (3, 0.2) {$q_1$}; 
  \node[below of=q1] (q2) {$q_2$};
  \node[below left of=q2] (q3) {$q_3$};
  \node[below right of=q2] (q4) {$q_4$};
  
  \draw[->] (q1) -- node[left] {a} (q2);
  \draw[->] (q2) -- node[above] {b} (q3);
  \draw[->] (q2) -- node[right] {c} (q4);
\end{tikzpicture}
\end{center}\<close>

text \<open>If we compare the states $p_1$ and $q_1$ of (ref example 1) we can see many similarities but also differences between their behavior.
They can perform the same set of action-sequences, however the $p_1$ can take a a-transition to $p_2$ where only a b-transition is possible, 
while $q_1$ can only has one a-transition into $q_2$ where both b and c are possible actions.
Abstracting away details of the inner workings of a system leads us to a notion of equivalence that focuses solely on its externally observable behavior, called \textit{trace equivalence}. 
We can imagine an observer that simply writes down the events of a process as they occur. 
This observer views two processes as equivalent iff they allow the same sequences of actions. As discussed, $p_1$ and $q_1$ are clearly trace-equivalent.
Opposite to that we can define a equivalence that also captures internal behavior. \textit{Strong bisimilarity}\footnote{Behavioral equivalences are commonly denoted as strong, as opposed to weak, if they do not take internal behavior into account. Since we are only concerned with concrete processes we omit such qualifiers.} considers two states equivalent if, 
for every possible action of one state, there exists a corresponding action of the other and vice versa. 
Additionally, the resulting states after taking these actions must also be bisimilar. The states $p_1$ and $q_1$ are not bisimilar, since for an a-transition from $q_1$ to $q_2$, $p_1$ can perform an a-transition to $p_2$
and $q_2$ and $p_2$ do not have the same possible actions. Bisimilarity is the finest commonly used \textit{extensional behavioral equivalence}.
In extensional equivalences, only observable behavior is taken into account, without considering the
identity of the processes. This sets bisimilarity apart from stronger graph equivalences like \textit{graph isomorphism}, 
where the (intensional) identity of processes is relevant.\<close>

text \<open>We introduce some concepts to better talk about LTS. Note that these Isabelle definitions are only defined in the \<open>context\<close> of LTS.\<close>

subsubsection \<open>Definition 2.1.2\<close>

text \<open>The \textit{$\alpha$-derivatives} of a state refer to the set of states that can be reached with an $\alpha$-transition:
$$\mathit{Der} (p, \alpha) = \{ p' \mid p \xrightarrow{\alpha} p' \}.$$\<close>

abbreviation derivatives :: \<open>'s \<Rightarrow> 'a \<Rightarrow> 's set\<close>
  where
\<open>derivatives p \<alpha> \<equiv> {p'. p \<mapsto>\<alpha> p'}\<close>

text \<open>The set of \textit{initial actions} of a process $p$ is defined by: 
$$I(p)=\{\alpha \in Act \mid \exists p'. p \xrightarrow{\alpha} p'\}$$\<close>

abbreviation initial_actions:: \<open>'s \<Rightarrow> 'a set\<close>
  where
\<open>initial_actions p \<equiv> {\<alpha>|\<alpha>. (\<exists>p'. p \<mapsto>\<alpha> p')}\<close>

text \<open>The step sequence relation $\xrightarrow{\sigma}^*$ for $\sigma \in \Act^*$ is the reflexive transitive closure of $p \xrightarrow{\alpha} p'$.
It is defined recursively by:
\begin{align*}
  p &\xrightarrow{\varepsilon}^* p \\
  p &\xrightarrow{\alpha} p' \text{ with } \alpha \in \text{Act} \text{ and } p' \xrightarrow{\sigma}^* p'' \text{ implies } p' \xrightarrow{\sigma}^* p''
\end{align*}
\<close>

inductive step_sequence :: \<open>'s \<Rightarrow> 'a list \<Rightarrow> 's \<Rightarrow> bool\<close> (\<open>_ \<mapsto>$ _ _\<close>[70,70,70] 80) where
\<open>p \<mapsto>$ [] p\<close> |
\<open>p \<mapsto>$ (a#rt) p''\<close> if \<open>\<exists>p'. p \<mapsto> a p' \<and> p' \<mapsto>$ rt p''\<close> 

text \<open>We call a sequence of states $s_0, s_1, s_2, ...$ a \textit{path} if there are such that \<close>
inductive paths :: \<open>'s list \<Rightarrow> bool\<close> where
  \<open>paths [p, p]\<close> |
  \<open>paths (p#p'#ps)\<close> if \<open>\<exists>a. p \<mapsto> a p' \<and> paths (p'#ps)\<close>

lemma
  assumes \<open>paths (p # ps @ [p''])\<close>
  shows \<open>\<exists>tr. p \<mapsto>$ tr p''\<close>
  using assms
proof (induct ps arbitrary: p)
  case Nil
  hence \<open>paths [p, p'']\<close>
    by simp
  hence \<open>p = p''\<close>
    by (metis list.discI list.sel(1) list.sel(3) paths.cases)
  hence \<open>p \<mapsto>$ [] p''\<close>
    using step_sequence.intros(1) by blast
  then show ?case
    by blast
next
  case (Cons p' ps)
  obtain a where \<open>p \<mapsto> a p'\<close> \<open>paths (p' # ps @ [p''])\<close>
    using Cons.prems paths.simps[of \<open>p # (p' # ps) @ [p'']\<close>]
    by auto
  obtain tr where \<open>p' \<mapsto>$ tr p''\<close>
    using Cons.hyps \<open>paths (p' # ps @ [p''])\<close>
    by blast
  then show ?case
    using \<open>p \<mapsto> a p'\<close> step_sequence.intros(2)
    by blast
qed

text \<open>A step sequence from $p$ to $p''$ implies...\<close>
lemma
  assumes \<open>p \<mapsto>$ tr p''\<close>
  shows \<open>\<exists>ps. paths (p # ps @ [p''])\<close>
  using assms
proof (induct rule:step_sequence.induct)
  case (1 p)
  have \<open>paths (p # [] @ [p])\<close>
    using paths.intros(1)
    by simp
  then show ?case by blast
next
  case (2 p a rt p'')
  then show ?case
    using paths.intros(2) append_Cons
    by metis
qed

text \<open>$p$ is image-finite if for each $\alpha \in \Act$ the set $mathit{Der} (p, \alpha)$ is finite.
An LTS is image-finite if each $p \in \Proc$ is image-finite:
"$$\forall p \in\Proc, \alpha \in \Act. mathit{Der} (p, \alpha)$$ is finite.\<close>

definition image_finite where
\<open>image_finite \<equiv> (\<forall>p \<alpha>. finite (derivatives p \<alpha>))\<close>

text \<open>nötig?\<close>

definition image_countable :: \<open>bool\<close>
  where \<open>image_countable \<equiv> (\<forall> p \<alpha>. countable (derivatives p \<alpha>))\<close>

text \<open>stimmt definition? definition benötigt nach umstieg auf sets?\<close>
definition lts_finite where
\<open>lts_finite \<equiv> (finite (UNIV :: 's set))\<close>

text \<open>We say that a process is in a \textit{deadlock} if no observation is possible. That is:
$$\mathit{deadlock} (p) = (\forall\alpha .\mathit{Der} (p, \alpha) = \varnothing)$$\<close>

abbreviation deadlock :: \<open>'s \<Rightarrow> bool\<close> where
\<open>deadlock p \<equiv> (\<forall>\<alpha>. derivatives p \<alpha> = {})\<close>

abbreviation relevant_actions :: \<open>'a set\<close>
  where
\<open>relevant_actions \<equiv> {a. \<exists>p p'. p \<mapsto>a p'}\<close>

text \<open>\textbf{Example 2} (van Glaabeeck counterex. 1)\<close>

text \<open>
\begin{center}
\begin{tikzpicture}[auto,node distance=1.5cm]
  \coordinate (p1) at (-3,0);
  \node at (-3, 0.2) {$p$}; 
  \node[draw, circle, fill=black, inner sep=1pt, below left of=p1] (p2) {};
  \node[draw, circle, fill=black, inner sep=1pt, below of=p1] (p3) {};
  \node[draw, circle, fill=black, inner sep=1pt, below right of=p1] (p4) {};
  \node[draw, circle, fill=black, inner sep=1pt, below of=p3] (p5) {};
  \node[draw, circle, fill=black, inner sep=1pt, below of=p4] (p6) {};
  \node[draw, circle, fill=black, inner sep=1pt, below of=p6] (p7) {};

  
  \draw[->] (p1) -- node[above] {a} (p2);
  \draw[->] (p1) -- node[left] {a} (p3);
  \draw[->] (p1) -- node[right] {a} (p4);
  \draw[->] (p3) -- node[left] {a} (p5);
  \draw[->] (p4) -- node[left] {a} (p6);
  \draw[->] (p6) -- node[left] {a} (p7);
  \node[] (dot1) at (-1.1,-1) {$\dots$};

\coordinate (q1) at (3,0);
  \node at (3, 0.2) {$q$}; 
  \node[draw, circle, fill=black, inner sep=1pt, below left of=q1] (q2) {};
  \node[draw, circle, fill=black, inner sep=1pt, below of=q1] (q3) {};
  \node[draw, circle, fill=black, inner sep=1pt, below right of=q1] (q4) {};
  \node[draw, circle, fill=black, inner sep=1pt, below of=q3] (q5) {};
  \node[draw, circle, fill=black, inner sep=1pt, below of=q4] (q6) {};
  \node[draw, circle, fill=black, inner sep=1pt, below of=q6] (q7) {};
  \node[draw, circle, fill=black, inner sep=1pt, right of=q4] (q8) {};
  \node[draw, circle, fill=black, inner sep=1pt, below of=q8] (q9) {};
  \node[draw, circle, fill=black, inner sep=1pt, below of=q9] (q10) {};
  
  \draw[->] (q1) -- node[left] {a} (q2);
  \draw[->] (q1) -- node[left] {a} (q3);
  \draw[->] (q1) -- node[right] {a} (q4);
  \draw[->] (q1) -- node[right] {a} (q8);
  \draw[->] (q3) -- node[left] {a} (q5);
  \draw[->] (q4) -- node[right] {a} (q6);
  \draw[->] (q6) -- node[right] {a} (q7);
  \draw[->] (q8) -- node[right] {a} (q9);
  \draw[->, dotted] (q9) -- node[right] {} (q10);
  \draw[->, dotted] (q10) -- +(0,-1) node[right] {};
  \node[] (dot2) at (4.7,-1) {$\ldots$};
\end{tikzpicture}
\end{center}\<close>

text \<open>Our definition of LTS allows for an unrestricted number of states, all of which can be arbitrarily branching. This means that they have unlimited ways to proceed. 
Given the possibility of infinity in sequential and branching behavior, we must consider how we identify processes that only differ in their infinite behavior. 
Take the states $p$ and $q$ of (ref example 2). They have the same (finite) step sequences, however only $q$ has an infinite trace. Do we consider them trace equivalent?
We will investigate this further in (Trace Semantics, Simulation?).\<close>

end
(*<*)
end
(*>*)