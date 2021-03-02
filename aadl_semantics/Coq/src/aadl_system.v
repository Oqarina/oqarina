(**
%\section{AADL System Category}\label{chap::aadl_system}%

%\textit{Note: the following is inspired from AADLv2.2 \S 13.3. We heavily simplified it to the bare minimal level of information. We also corrected some of this description to better reflect the modular nature of AADL instance hierarchy.}\\
\noindent\rule{4cm}{0.4pt}
%

The %\texttt{system}% component category denotes an assembly of interacting application
software, execution platform, and system components. Systems may be hierarchically nested.

%\subsection{System behavioral semantics}%

Figure%~\ref{fig:aadl_system_beh}% defines the behavior of system component category.

%
\tikzset{elliptic state/.style={draw,ellipse}, -Triangle, node distance=2cm}

\begin{figure}[!h]
\begin{tikzpicture}
\node[elliptic state, very thick] (s0) {system offline};
\node[elliptic state, below=1cm of s0] (s1) {system starting};
\node[elliptic state, right=1cm of s1] (s2) {system stoping};
\node[elliptic state, below of=s1] (s3) {system operational};
\draw (s0) edge[bend left, right] node{\textbf{start(system)}} (s1);
\draw (s1) edge[bend left, left] node{\textbf{abort(system)}} (s0);
\draw (s1) edge[, right] node{\textbf{started(system)}} (s3);
\draw (s3) -| node[below]{\textbf{stop(system)}} (s2);
\draw (s2) |- node[above]{\textbf{stopped(system)}} (s0);
\draw (s3) -| ++(-4,2) node[left]{\textbf{abort(system)}} |- (s0);

\end{tikzpicture}
\caption{AADL \texttt{system} automata behavior} \label{fig:aadl_system_beh}
\end{figure}
%

This automata semantics can also be described as follows:

- %\textit{"system offline"}% is the system initial state.

- On system startup the system instance transitions from %\textit{"system offline"}% to %\textit{system starting}% through the action %\textbf{start(system)}%

- When in state %\textit{"system starting"}%, the system perform the initialization of the system subcomponents. In case of an error during this step, the system goes back to %\textit{"system offline"}% through the the %\textbf{abort(system)}% action. When all subsystems have been successfully initialized, the system moves to the state %\textit{"system operational"}% through the %\textbf{started(system)}% action.

- When in state %\textit{"system operational"}%, the system is under operation, the system and its subcomponents execute their nominal behavior. In case of an error during the execution, the system goes back to %\textit{"system offline"}% through the %\textbf{abort(system)}% action.

- Upon completion of its execution, a system may perform a graceful shutdowm (%\textbf{stop(system)}% action) and moves to the state %\textit{"system stoping"}%. When all subsystems are successfully stoped, the system moves to the state %\textit{"system offline"}% through the %\textbf{stopped(system)}% action.

*)

Inductive system_states :=
    system_offline | system_starting | system_operational | system_stoping.



(** *)