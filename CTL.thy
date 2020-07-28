theory CTL
  imports Main

begin
text\<open>Define and verify a model checker of properties defined in CTL on FTS.
Proofs are often provided twice, a slegehammer found one, and the more-manual
 one from the tutorial\<close>

text\<open>state is a type parameter of the theory\<close>
typedecl state

text\<open>arbitrary but fixed transition systems defined as a
relation between states\<close>
consts M :: "(state \<times> state) set"

text\<open>type of atomic propositions\<close>
typedecl "atom"

text\<open>The labelling function that defines what subset of atoms
hold in a particular state\<close>
consts L :: "state \<Rightarrow> atom set"

text\<open>Formulae of Proposition Dynamic Logic are built up from atoms, negation,
conjunction and temporal connectives "all branches next" and "some branches
eventually\<close>
datatype formula = Atom "atom"
  | Neg formula
  | And formula formula
  | AX formula
  | EF formula

text\<open>Validity relation, when a particular PDL formul holds\<close>
primrec valid :: "state \<Rightarrow> formula \<Rightarrow> bool" ("(_ \<Turnstile> _)" [80, 80] 80)
where 
"s \<Turnstile> Atom a  = (a \<in> L s)" |
"s \<Turnstile> Neg f   = (\<not>(s \<Turnstile> f))" |
"s \<Turnstile> And f g = (s \<Turnstile> f \<and> s \<Turnstile> g)" |
"s \<Turnstile> AX f    = (\<forall> t. (s, t) \<in> M \<longrightarrow> t \<Turnstile> f)" |
"s \<Turnstile> EF f    = (\<exists> t. (s, t) \<in> M\<^sup>* \<and> t \<Turnstile> f)"

text\<open>Now we define our model checker\<close>
primrec mc :: "formula \<Rightarrow> state set" where
"mc(Atom a)  = {s. a \<in> L s}" |
"mc(Neg f)   = -mc f" |
"mc(And f g) = mc f \<inter> mc g" |
"mc(AX f)    = {s. \<forall> t. (s, t) \<in> M \<longrightarrow> t \<in> mc f}" |
"mc(EF f)    = lfp(\<lambda>T. mc f \<union> (M^-1 `` T))"

text\<open>Proove that mc(EF _) is monotonic, and therefore has a least fixed point\<close>
lemma mono_ef: "mono(\<lambda>T. A \<union> (M^-1 `` T))"
  by (smt Image_Un Un_iff monoI subsetI sup.order_iff)

lemma mono_ef': "mono(\<lambda>T. A \<union> (M^-1 `` T))"
  apply (rule monoI)
  by blast

text\<open>relate model checking with the logical semantics\<close>
lemma EF_lemma: "lfp(\<lambda>T. A \<union> (M^-1 `` T)) = {s. \<exists>t. (s, t) \<in> M\<^sup>* \<and> t \<in> A}"
  by try

end