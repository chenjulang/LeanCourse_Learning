(*  Title:      SqrtTutor1.thy
    Author:     G. Dalton Bentley
    We wrote an Isabelle tutorial that steps through (and modifies superficially
    by using different proof steps at times) a proof developed
    by Markus Wenzel and Tobias Nipkow and provided in HOL/ex/Sqrt.thy
    of the Isabelle distribution. The current theory document SqrtTutor1.thy
    is a demonstration vehicle for Isabelle document preparation.
*)

section \<open>Square root of prime\<close>
(*<*)
theory SqrtTutor1
  imports Complex_Main "HOL-Computational_Algebra.Primes"
begin
(*>*)

text \<open>
  We wrote an Isabelle tutorial\<^footnote>\<open>\<^url>\<open>https://github.com/AncientZygote/izzie/blob/main/IsabelleTutorial.pdf\<close>\<close> using a proof provided in the \<^verbatim>\<open>HOL/ex/Sqrt.thy\<close> file (developed by Markus Wenzel and Tobias Nipkow) of the Isabelle distribution. This proof demonstrates that the square root of a prime number cannot be a rational number.\<^footnote>\<open>The authors present several such proofs in that theory document. We selected the proof that they described as using mostly linear forward-reasoning, that appearing more like a mathematical proof rather than a prover tactic script.\<close>

Our statement of the theory and proof is:

$\mathbf{Theorem.}\,\,\,$\<^emph>\<open>
If $p$ is prime, i.e., $p \in \mathbb{Z}_{\small{>0}}$ with $p >1$ and having only factors $1$ and itself, then $\sqrt{\smash[b]{p}} \notin \mathbb{Q}$, where $\mathbb{Q} = \lbrace \frac{a}{b} | \, a \in \mathbb{Z} \, \mathrm{and} \, b \in \mathbb{Z} \, \mathrm{and} \, b \ne 0 \rbrace $ and there is a unique (reduced) representation such that $\gcd(a,b)=1$, i.e., $(a,b)$ are relatively prime.\<close>

$\mathbf{Proof.}\,\,\,$ Assume on the contrary that $\sqrt{\smash[b]{p}} \in \mathbb{Q}$: Then $\exists m, n \in \mathbb{Z}$ with $n \ne 0$ such that $\sqrt{\smash[b]{p}} = m/n $ with $\gcd(m,n)=1$, i.e., $(m,n)$ are relatively prime. In that case, $m = \lvert\sqrt{\smash[b]{p}}\rvert n$. It follows that $m^2 = (\sqrt{\smash[b]{p}})^2 n^2$ and $m^2 = p n^2$. In that case we may say that $p | m^2$ and also that $p | m$, since a prime divisor of a product of integers must divide one of the integer factors, which are identical in the case of a square. That being so, there must be an integer $k$ such that $m = p k$. Since we established that  $m^2 = p n^2$ and we can square $m = p k$ to obtain $m^2 = p^2 k^2$, we have $p n^2 = p^2 k^2$. We can divide that last result by $p$ to obtain  $n^2 = p k^2$. That tells us that $p | n^2$ and therefore $p | n$ (as above, prime divisor of product of integers divides at least one of the factors). We have therefore shown that $p$ prime divides both $m$ and $n$ and therefore must divide the greatest common divisor of $m,n$, i.e., $p | \mathrm{gcd}(m,n)$. However, we stipulated that $m,n$ are relatively prime, i.e., that $\mathrm{gcd}(m,n)=1$. In that case, $p=1$, a contradiction since we stated $p$ is prime and must therefore be greater than $1$, i.e.,  $p > 1$ by definition of primality. Our assumption that $\sqrt{\smash[b]{p}} \in \mathbb{Q}$ is therefore false and therefore  $\sqrt{\smash[b]{p}} \notin \mathbb{Q}$. $\square$

\<close>

section \<open>Isabelle/Isar proof\<close>

text \<open>

The following is the actual Isabelle/Isar proof which we worked through step-by-step in our tutorial cited above. It must be emphasized that the words you are reading here are text inserted into the actual  \<^verbatim>\<open>SqrtTutor1.thy\<close> theory file that executes as a formal proof in Isabelle/jEdit.

\<close>

theorem
  assumes \<open>prime (p::nat)\<close>
  shows \<open>sqrt p \<notin> \<rat>\<close>
proof
  from \<open>prime p\<close> have p: \<open>1 < p\<close> by (rule prime_gt_1_nat)

  assume \<open>sqrt p \<in> \<rat>\<close>
  then obtain m n :: nat where
    n: \<open>n \<noteq> 0 \<close> and sqrt_rat: \<open>\<bar>sqrt p\<bar> = m/n\<close>
    and \<open>coprime m n\<close> by (rule Rats_abs_nat_div_natE)

  from n and sqrt_rat have \<open>m = \<bar> sqrt p \<bar> * n \<close> by simp

  then have "m^2 = (sqrt p)^2 * n^2"
    by (simp add: power_mult_distrib)
  also have \<open>(sqrt p)^2 = p\<close> by simp

  also have \<open>... * n^2 = p * n^2\<close> by simp

  finally have eq: \<open>m^2 = p * n^2\<close>
    using of_nat_eq_iff by blast

  then have \<open>p dvd m^2\<close> ..

  with \<open>prime p\<close> have dvd_m: \<open>p dvd m\<close>
    using prime_dvd_power_nat by blast

  then obtain k where \<open>m = p * k\<close> ..

  with eq have \<open>p * n^2 = p^2 * k^2\<close>
  proof -
    show ?thesis
      by (metis (full_types) \<open>m = p * k\<close> \<open>m\<^sup>2 = p * n\<^sup>2\<close> mult.commute mult.left_commute power2_eq_square)
  qed

  with p have \<open>n^2 = p * k^2\<close>
proof -
have "\<not> (1::nat) < 0"
by blast
then show ?thesis
  by (metis (no_types) \<open>1 < p\<close> \<open>p * n\<^sup>2 = p\<^sup>2 * k\<^sup>2\<close> mult.assoc nonzero_mult_div_cancel_left power2_eq_square)
qed
  then have \<open>p dvd n^2\<close> ..
  with \<open>prime p\<close> have \<open>p dvd n\<close> by (rule prime_dvd_power_nat)
  with dvd_m have \<open>p dvd gcd m n\<close> by (rule gcd_greatest)
  with \<open>coprime m n\<close> have \<open>p = 1\<close> by simp
  with p show False
    by simp
qed

section \<open>How to print this theory document\<close>

text \<open>

Relevant Isabelle system documentation includes Chapter 2 and Chapter 3 of @{cite "isabelle-system"}, and \S4.2 in @{cite "isa-tutorial"}\<^footnote>\<open>The cited document, \<^emph>\<open>Isabelle/HOL: A Proof Assistant for Higher-Order Logic\<close>, also accompanies the Isabelle distribution as \<^verbatim>\<open>tutorial.pdf\<close>.\<close>. Let us assume you have a copy of this theory file \<^verbatim>\<open>SqrtTutor1.thy\<close>\<^footnote>\<open>Downloaded at \<^url>\<open>https://github.com/AncientZygote/izzie/\<close>\<close>) (or a theory file of your own making that you are interested in printing within Isabelle).

    \<^item> Go to your home directory area, e.g., \<^verbatim>\<open>/home/dalton/IsabelleStuff\<close>.

    \<^item> Open a terminal (we are going to use Linux-oriented language) session there.

    \<^item> Execute the following command string in the terminal (is a single line):
    \<^verbatim>\<open> isabelle mkroot -n TestSess -T "A Tutorial" -A "Dalton Bentley" Test \<close>

    \<^item> If you do not want a session name (e.g., \<^verbatim>\<open>TestSess\<close>) different from the directory name to be created (here the directory to be created is \<^verbatim>\<open>Test\<close>, the last token on the command string), do not want to specify the title of the pdf document (\<^verbatim>\<open>"A Tutorial"\<close> here), do not want to specify the author in the pdf (\<^verbatim>\<open>"Dalton Bentley"\<close> here) use instead the following command string in the terminal:
    \<^verbatim>\<open> isabelle mkroot Test \<close>

Your terminal output should indicate the result of the \<^verbatim>\<open>mkroot\<close> command (we used the first, longer line with options\<^footnote>\<open>See \S3.2 in @{cite "isabelle-system"} for those options.\<close>):

\<^verbatim>\<open>Preparing session "TestSess" in "Test"\<close>\\*
\<^verbatim>\<open>  creating "Test/ROOT"\<close>\\*
\<^verbatim>\<open>  creating "Test/document/root.tex"\<close>

We obtain a new directory (which will be the \<^emph>\<open>session root\<close>) named \<^verbatim>\<open>Test\<close> as we specified with the final token of the invocation line above. Place a copy of the \<^verbatim>\<open>SqrtTutor1.thy\<close> file\<^footnote>\<open>Obtain at our GitHub area: \<^url>\<open>https://github.com/AncientZygote/izzie/\<close>\<close> in the new \<^verbatim>\<open>Test\<close> directory. We see \<^verbatim>\<open>mkroot\<close> creates a \<^verbatim>\<open>ROOT\<close> file in that directory (the \<^emph>\<open>session root\<close> directory), along with a subfolder named \<^verbatim>\<open>document\<close> with a contained \LaTeX{} file \<^verbatim>\<open>root.tex\<close>.

The \<^verbatim>\<open>ROOT\<close> file (a text file) has our optional session name  \<^verbatim>\<open>TestSess\<close> differing from the root directory name itself \<^verbatim>\<open>Test \<close> in the default text inserted:

\<^verbatim>\<open>
session TestSess = HOL +
  options [document = pdf, document_output = "output"]
(*theories [document = false]
    A
    B
  theories
    C
    D*)
  document_files
    "root.tex"
\<close>%close verbatim

Edit the \<^verbatim>\<open>ROOT\<close> file, keeping the first two lines identifying the session and options, and insert our theory \<^verbatim>\<open>SqrtTutor1\<close> below a  \<^verbatim>\<open>theories\<close>  heading. Remove the  \<^verbatim>\<open>.thy\<close> suffix or you will get complaints. Be sure to observe the indentations indicated, i.e., maintain the same block structure. We note that it is possible to edit \<^verbatim>\<open>ROOT\<close> files in Isabelle/jEdit@{cite "isabelle-jedit"} and thereby obtain syntax indentation and painting, however, we find it more convenient to simply use a text editor in the current context since we are using Isabelle batch mode facilities for theory document preparation.

We leave the $\mathtt{document\_files}$ entry alone for now, knowing the Isabelle document commands default to looking in the \<^verbatim>\<open>document\<close> subdirectory of the root directory created by \<^verbatim>\<open>mkroot\<close> (if we used documents in other directories we could provide the path under a $\mathtt{document\_files}$ heading in \<^verbatim>\<open>ROOT\<close>).\<^footnote>\<open>We note that the Isabelle distribution contains many \<^verbatim>\<open>ROOT\<close> files which provide examples of possible configurations, all considerably more sophisticated than our usage here. See \<^verbatim>\<open>$ISABELLE_HOME/src/HOL/ROOT\<close> and \<^verbatim>\<open>$ISABELLE_HOME/src/Doc/ROOT\<close>. \<^verbatim>\<open>$ISABELLE_HOME\<close> is the location of the top-level Isabelle distribution directory. You can see its value with terminal command \<^verbatim>\<open>isabelle getenv ISABELLE_HOME\<close>, typically it is \<^verbatim>\<open>/usr/local/Isabelle2020\<close>. \<close> We obtain in our \<^verbatim>\<open>ROOT\<close> then:

\<^verbatim>\<open>
session TestSess = HOL +
  options [document = pdf, document_output = "output"]
  theories
    SqrtTutor1
  document_files
    "root.tex"
\<close>%close verbatim

If we run \<^verbatim>\<open>isabelle build -D Test\<close> now (from our terminal open above the \<^verbatim>\<open>Test\<close> directory level), that will fail with error:

\<^verbatim>\<open>
*** Cannot load theory "HOL-Computational_Algebra.Primes"
*** The error(s) above occurred in session "TestSess" (line 1 of "/home/dalton/IsabelleStuff/Test/ROOT")
\<close>%close verbatim

Why? We have hidden some of the theory file text to make this printed document cleaner. If you open this file \<^verbatim>\<open>SqrtTutor1.thy\<close> in your text editor (or jEdit), you will see that in the first few lines the theory imports a theory from a session not in the current namespace:

\<^verbatim>\<open>imports\<close> $\mathtt{Complex\_Main}$ "$\mathtt{HOL}\text{-}\mathtt{Computational\_Algebra.Primes}$"

Notice the format \<^verbatim>\<open>HOL\<close>-, signifying found within the \<^verbatim>\<open>HOL\<close> object logic folder. $\mathtt{Computational\_Algebra}$ is a session folder within the \<^verbatim>\<open>HOL\<close> directory (but not part of the default \<^verbatim>\<open>HOL\<close> heap load). The period ``.'' attaches the theory \<^verbatim>\<open>Primes.thy\<close> to its containing session $\mathtt{Computational\_Algebra}$ (we do not include the \<^verbatim>\<open>.thy\<close> suffix when naming theory files in \<^verbatim>\<open>imports\<close> or \<^verbatim>\<open>ROOT\<close> lists).

We must edit our \<^verbatim>\<open>ROOT\<close> file to inform Isabelle to include this session:\<^footnote>\<open>Why are some of the entities enclosed in quotation marks? We do not have a specific answer, other than that, heuristically, the \<^verbatim>\<open>build\<close> may fail otherwise.\<close>

\<^verbatim>\<open>
session TestSess = HOL +
  options [document = pdf, document_output = "output"]
  sessions
    "HOL-Computational_Algebra"
  theories
     SqrtTutor1
  document_files
    "root.tex"
    "root.bib"
\<close>%close verbatim

You see we inserted a \<^verbatim>\<open>sessions\<close> heading, indented to the same level as other major keywords below the initial new \<^verbatim>\<open>session\<close> declaration (we define a new session \<^verbatim>\<open>TestSess\<close> with parent session \<^verbatim>\<open>HOL\<close>).\<^footnote>\<open>See \S2.1 of @{cite "isabelle-system"}.\<close>


You also should notice that we inserted a bibliography file reference (it must be named \<^verbatim>\<open>root.bib\<close> if we want to obtain Isabelle default bibliography processing without having to write a \<^verbatim>\<open>build\<close> script) under the $\mathtt{document\_files}$ heading. This seems a good time to take care of that requirement also and to discuss the required modifications to the default \<^verbatim>\<open>root.tex\<close> file. If you examine our theory file \<^verbatim>\<open>SqrtTutor1.thy\<close> in your text editor, you will see the form of the reference cites, e.g., \<^verbatim>\<open>@{\<close>\<open>cite\<close>~\<^verbatim>\<open>"isabelle-system"\<close>\<^verbatim>\<open>}\<close>.

Download the \<^verbatim>\<open>root.bib\<close> file from our GitHub Isabelle-related area\<^footnote>\<open> \<^url>\<open>https://github.com/AncientZygote/izzie/\<close>\<close> if you have not done so. It is a text file that can be edited in a text editor or in a \TeX{} editor like \TeX{works}. We will not digress to discuss {Bib}\TeX, but point you at the \<^verbatim>\<open>$ISABELLE_HOME/src/Doc/manual.bib\<close> file, which contains a {Bib}\TeX database for the Isabelle documentation with on the order of $300$ bibliography entries of all types (and the shell scripts in that directory illustrate how to specify bibliography and other document preparation tasks rather than use the default behavior).

The default \<^verbatim>\<open>root.tex\<close> file (recall that \<^verbatim>\<open>mkroot\<close> created it in the \<^verbatim>\<open>document\<close> subdirectory earlier) requires two modifications for our specific case here. We use the AMS (\<^emph>\<open>American Mathematical Society\<close>) \LaTeX{} packages \<^verbatim>\<open>amssymb\<close> and \<^verbatim>\<open>amsmath\<close> (probably most of our usage could be replaced with equivalent Isabelle symbols, but we already know AMS). So insert the the following lines after the \<^verbatim>\<open>\usepackage{isabelle,isabellesym}\<close> line in \<^verbatim>\<open>root.tex\<close>:

\<^verbatim>\<open>
\usepackage{amssymb}
\usepackage{amsmath}
\usepackage{xspace}
\<close>

Finally, uncomment the optional bibliography lines at the end of the \<^verbatim>\<open>root.tex\<close> file:

\<^verbatim>\<open>
% optional bibliography
\bibliographystyle{abbrv}
\bibliography{root}
\<close>

You could also modify \<^verbatim>\<open>\title\<close>, \<^verbatim>\<open>\author\<close> and other \LaTeX{} fields if desired. Recall that \<^verbatim>\<open>mkroot\<close> populated those fields earlier.

The \<^verbatim>\<open>Test/document\<close> directory should now contain:

\<^verbatim>\<open>
root.bib  root.tex
\<close>

We are ready to run \<^verbatim>\<open>isabelle build -D Test\<close> now (from our terminal open above the \<^verbatim>\<open>Test\<close> directory level) and create a pdf document from our theory file:

\<^verbatim>\<open>
dalton@dalton-Precision-3541:$ isabelle build -D Test
Running TestSess ...
Document at /home/dalton/IsabelleStuff/Test/output/document.pdf
Finished TestSess (0:00:22 elapsed time, 0:00:43 cpu time, factor 1.91)
0:00:27 elapsed time, 0:00:43 cpu time, factor 1.55
\<close>

The \<^verbatim>\<open>Test\<close> directory should now contain:

\<^verbatim>\<open>
document  output  ROOT  SqrtTutor1.thy
\<close>

The \<^verbatim>\<open>output\<close> directory should now contain:

\<^verbatim>\<open>
document  document.pdf
\<close>

\<^verbatim>\<open>document.pdf\<close> should be a seven page pdf document with title, author, hyperlinked table of contents, three chapters and References (did not bother to include that in the TOC). The \<^verbatim>\<open>document\<close> subfolder (\<^verbatim>\<open>Test/output/document\<close>) should contain:

\<^verbatim>\<open>
Cancellation.tex         isabelletags.sty  root.bbl  root.tex
comment.sty              Multiset.tex      root.bib  root.toc
Euclidean_Algorithm.tex  pdfsetup.sty      root.blg  session_graph.pdf
Factorial_Ring.tex       Primes.tex        root.log  session.tex
isabelle.sty             railsetup.sty     root.out  SqrtTutor1.tex
isabellesym.sty          root.aux          root.pdf
\<close>

That concludes this brief tutorial on \LaTeX{} printing an Isabelle theory file.

\<close>

(*<*)
end
(*>*)