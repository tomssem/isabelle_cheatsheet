# isabelle_cheatsheet
A cheat sheet for Isabelle/ Isar/ HOL

| Items | Explanation | Example | Notes |
|---|---|---|---|
|`theory`|Named collection of types functions and theorems| <pre>Theory MyTheory<br>Imports Main Groups<br>begin<br>...<br>end</pre>|Name of file must be same as name of theory (so this example would go in `MyTheory.thy`.<br>Imported theoreies are called _parent theories_.<br>Can qualify clashing theories using, e.g., `MyTheory.foo` or `Main.foo`.|
| base types | | `bool`, `nat` etc. | |
| type constructors | Used to construct new types from existing types | `nat list` | Are written postfix |
| function types | | `T1 ⇒ T2 ⇒ T3 ⇒ T4` or equivalently `[T1, T2, T3] ⇒ T4` |Total functions only<br>`⇒` is right associative|
| type variables | Used in polymorphic types | `'a ⇒ 'a`<br>`list 'a`| Always preceded by `'` |
| if statement | | `if b the t1 else t2`\| `b` is of type bool, `t1` and `t2` are of the same type | Need to be enclosed in parentheses |
| let statement | substitute all free occurences of a variable in an expression with another expression | `let x = 0 in x + x` | This example would get reduced to `0 + 0` |
| case statement | allows matching on the structual form of a term  | <pre>case l of<br> nil ⇒ ...\|<br> Cons x xs ⇒ ...</pre> | Complex case patterns tend to yield complex proofs<br>Need to be enclosed in parentheses |
| lambda abstraction | allows definition of anonymous functions | λ x. x + 1 | |
| formulae | terms of type `bool` | `A ∧ B --> A ` | Have logical connectives ¬ (negation), ∧ (conjunction),∨ (disjunction), and --> (implication). <br> Have quantifiers ∀ (universal quantification) ∃ (existential quantification). Nested quantifications are abreviated: `∀ x y z. P` is the same as `∀ x. ∀ y. ∀ z. P`|
| type constraints | gives explicit information on type of variable when type inference fails | `[]::(nat list)` | |
| schematic variable | A free variable that may become instantiated during proof process | | Like _logical variables_ in Prolog |
| `infixr` | defines an infix operator that is right associative | `infixr "@" 65` | final number is precendence level, higher is tighter binding |
| `infixl` | defines an infix operator that is left associative | | |
| comments | | `(* ... *)` | |
| `value` | Lets you run an expression | `value (1 + 1)` | Can evaluate terms with variables in them. |
| simplification rules | Tells Isabelle which rewrites it can perform when simplifyin expressions | `theorem []:"rev (rev xs) = xs"`| RHS should always be simpler than LHS.|
| `defer` | Moves first subgoal to end | | |
| `prefer <n>` | moves the nth subgoal to the front | | |
| `thm theorem1 ... theoremn` | prints the specified theorems | | |
| `datatype` | Provides an inductive definition for a type | <pre>dataype 'a list = Nil<br>\| Cons 'a "'a list"</pre> | |
| linear arithmetic | Formulas that involve only ¬, ∧, ∨, −→, =, ∀, ∃, =, ≤, <, +, -, `min` and `max` || |
| `arith` | proof methods that can solve linear arithmetic | | Exponential in number of -, `min` and `max`, since they are eliminated by case distinctions |
| tuples | simulated by nested pairs | `(1, "a", 1.0):: nat×string×real ≡  (1, ("a", 1.0)):: nat×(string×real)` | Therefore have, e.g.,  `fst(snd(1, "a", 1.0)) = "a"`.<br>Large tuples become unweildy, best to prefer records  |
| `unit` | types which contains exactly one element: `()` | | |
| `type_synonym` | Used to create new type that corresponds to an existing type | `type_synonym number = nat` | Used to improve readability of theories |
| dead/ live type arguments | type constructors allow recursion on a subset of their type arguments, these are called the _live_ arguments, all others are called _dead_ | `datatype (dead 'a, 'i) bigtree = Tip \| Br 'a "'i ⇒ ('a,'i)bigtree"`| In example `'a` is type of what is being stored, `'i` is the index over which tree branches |
| mutual recursion | Used to define two dataypes that depend on each other | <pre>datatype T1 = ...<br/>and<br/> T2 =...</pre> | |
| nested recursion | Recursive datatype occurs nested in itself | <pre>datatype ('v, 'f)"term" = Var 'v | App 'f ('v,'f)term list" </pre></br>A recursive function over this structure is then defined thus:</br><pre>primrec ('v 'f)term => ('v, 'f) term"</br>and substs:: ('v, 'f)term list => ('v, 'f)term list"</br>where</br>"subst s ..."|</br>"substs s ..."</pre> | Can always unfold nesting to become mutually recursive.</br> When proving fact about a term, need to simuntanesouly proove fact about nested term. |
| `declare Let_def[simp]` | tell rewriter to expand lets | | |
| `declare option.split[split]` | tell rewriter to split all `case`-constructs over options | | |
| apply(...[!]) | apply tactic to all sub-goals | | |
| size of a datatype | every datatype is equipped with a `size` function, defined as 0 for all constructors without an argument or 1 plus the sum of the sizes of all constructor arguments | | this is the size that is used in proofs of termination of recursive functions |
|termination of total recursive functions | any lexicographic combination of size measures across arguments (c.f. Ackerman function) | | |
|recursion induction | inducting on a datatype using the the structural form implied by a recursive equations  | `apply(indduction xs rule: f.induct)` | |
| infix definitions | | <pre>definition xor :: "bool ⇒  bool ⇒ bool"   (infixl "[+]" 60)</br>where "A [+] B ≡ (A ∧ ¬B) ∨ (¬A ∧ B)"</pre> | Can turn infix operator into prefix function by: `([+])` |
| named control symbols | all of form `\<^ident>`, for declaring how output will be typeset | | |
| abbreviations | allows a complex term to be abbreviated with nice notation | <pre>abbreviation sim2 :: "'a => 'a => bool" (infix "≈" 50)</br>where "x ≈ y ≡ (x, y) ∈ sim"| Appropriate when defined concept is a simple variation on an existing one.</br>Not appropriate  |
| source comments | like comments in other languages | `(*...*)` | |
| formal comments | actually show up when in proof document, `-- <comment>`. Formal markup command | <pre>lemma "A --> A"</br>-- super simple, barely an inconvenience</br> by (rule impI)</pre> | |
| major premise | The first premise in an assumption list | | In `⟦P1; ...; Pn⟧ ⟹  ...` `P1` is the major premise |
| .. | Denotes a _trivial proof_, one that holds by definition | `lift_definition sub_list :: "my_list ⇒ my_list ⇒ bool" is Set.subset .` | |
| . | Denotes _immediate proof_ finishing a proof by single application of a standard rule | | |
| `setup_lifting` | Declares a context when where you can use `lift_definition` | `setup_lifting type_definition_my_view` | Also allows the `transfer` tactic, which allows many proofs to be dispatched as trivial using `.` |
| meta logic | high-level formalism used at the Pure level | | contains the operators ∧ (arbitrary value), ⟹  (express inference rules and for assumptions) , and ≡ (defines constants) |
| `apply(rule_tac x="..." in exI)` | Instantiate existentially bound variable in conclusion with provied expression | | |
| THE | definite description operator `THE x. P x` refers to the unique x s.t. `P x` is true | | |
| SOME | Hilbert's ε-operator | | `∃ x. A x ≡ A(SOME x. A x)`</br>∀ x. A x ≡ A(SOME x. ¬A x)|
| LEAST | least number operator, deontest the least x satisfying P | | `(LEAST x. P x) = (THE x. P x ⋀ (∀ y. P y⟶    x≤y))` |
| `oops` | abandons proof | | |
| `lemma [iff]....` | like `lemma [simp]...` but adds both ways of the equality | | |
| `!x` | a unique x | `∃!x. ?P x ⟹ ?P (THE x. ?P x)` | |
| `of` | allows instantiation of unbound variables by position in theorems, identifies variables in the order they appear | `mult_assoc [of x 1] | In our example `?a` gets bound to x, `?b` to `, `?c` remains unbound. To "skip" a variable and leave it unbound can do: `mult_assoc of [_ 1]`, now `?a` remains unbound. |
| `where` | allows named instantiation of unbound variables in theorems | `mult_assoc [where b = 1]` | equivalent to `mult_assoc of [_ 1 _]` |
| `THEN` | applies specified rule to the given theorem | `mult_1 [THEN sym]` | Given example forms a rule that is the same as `?a = 1 * ?a`. Useful patterns are: `... [THEN sym]`, `[THEN spec]` (removes universal quantifier), `... [THEN mp]` which turns implication into an inference rule |
| `OF` | allows specialisation of facts in premise | `conjI [OF _ "x = 1"]` | given example yields the theorem: `⟦?P; (x = 1)⟧ ⟹  ?P ∧ (x = 1)`
| `insert` | methods that allows us to insert an additional fact to our premises | `apply (insert dvd_mult [of 2 8]` | Example will insert the premise: `⋀b 8 dvd 2 ⟹   8 dvd b * 2` into list of premises. Any unknown variables in theorem will be universally quantified |
| `subgoal_tac` | allows us to insert an arbitrary formula that we can use to prove the current goal, but we will have to prove later as a separate subgoal | `apply (subgoal_tac "1=0")` | In the given example, we can use `1 = 0` to (trivially) prove the current goal, but we will then have to prove it as a separate subgoal given the current premises |
| `+` | suffixing a method with `+` expresses one or more repetitions | `by (drule mp, assumption)+` | |
| `\|` | separating two methods by `\|` tries applying the first, and if that fails applies the second | `by (drule mp, (assumption|arith))+`  | |
| `?` | suffixing a method with `?` expresses zero or one repetitions of a method | | `(m+)?` expresses zero or more repetitions of method `m` |
| `pr` | changes the number of subgoals shown in output | | |
| `defer` | moves current subgoal to the last position | | |
| `prefer` | moves the specified subgoal to be the current subgoal | | useful for tring to prove a doubtful subgoal before moving onto the easier ones |

## Proof methods
### Simplification
Definition: "repeated application of equations from left to right" or equivalently "repeated applciation as `term rewriting` according to `rewriting rules`"
- more accurate to call it rewriting, expressions may not necessarily become simpler
- theorems declared as simplificaiton rules using `[simp]` attribute
- `datatype`, `fun` implicityly declare some simplification rules. TODO: what are the resulting rules called and how does one find them?
- `definition`s are by default not added to rewrite rules
    * defining `f x y ≡ t` means `f` can only be unfolded when it is applied to two arguments, instead define as `f ≡ λx y.t` to unfold all occurences
    * Also have `unfold` method that will just unfold specified definitions: `apply (unfold xor_def)` 
    * To simplify let expressions: `apply (simp add: Let_def)`
- Tool used to perform simplification in Isabelle is called *simplifier*
- simplification can not terminate if for example `f(x) = g(x)` and `g(x) = f(x)` are in rewrite rules
- assumptions are included in simplification rules.
    * Assumptions can also lead to non-termination of rewrite process
    * In which case tell rewriting to ignore assumptions: `apply (simp (no_asm))`
Simplification is performed by the `simp` method, of the form: `simp <list_of_modifiers>`
Modifiers:
- `add`: list of theorems to add to rewriting rules
- `del`: list of theorems to remove from rewriting rules
- `only`: list of theorems that will only be used as rewriting rules
Case splits allow simplifier to reason about each form an expression can take
- to split an if-expression: `apply (split if_split)`
    * done automatically by `simp`
- to simplify while performing case analysis on a type T: `apply (simp split: T.split)`
    - can explicitly split statements: `apply (split T.split)`
Good idea to enable rewrite tracing to get an idea what's going on`declare [[simp_trace]]` and maybe increase the trace depth limit: `declare [[simp_trace_depth_limit=4]]`
In order to apply a rewrite exactly once (and avoid looping): `apply (subst <rule>)`
### Induction
Heuristics:
- Induction used for proving theorems about recursive functions
- Induct on the argument that is recursed on
- generalize goal before induction by replacing constants with variables
- generalize goals for induction by universally quantifying all free variables
- the RHS of an equation should be simpler than the LHSdead
- `apply(induct_tac a and b)` used to induct on mutually recursive datatype

## Tactics
| `rename_tac` | renames arbitrary variables (⋀ - quantified) to the provided names | `apply (rename_tac v w)` | If the number of provided variables is less than the number of arbitrary variables, the rightmost ones are renamed |
| fruel | acts like `drule`, but copies the selected assumption rather than replacing it | |

## Rules
All of the supplied rules will be applied automatically by automation procedures.
You can see a full list of the types of all rules using `print_rules`
### Introduction and elimination rules
Introduction (introduce a logical operator, applies to conclusion) rules are applied by `apply (rule ...)` elimination (eliminate logical operator, applies to premise) rules can also be applied by `apply (erule ...)` (which automatically matches assumption of rule with one from current premise).
Act on instance of major premise.
`apply (intro <intro_rule>)` repeatedly applys the provied introduction rule
| rule name | explaination | type | notes |
|---|---|---|---|
| `conjI` | introduction rule for conjunction |  ⟦?P; ?Q⟧ ⟹  ?P ∧ ?Q | |
| `conjE` | elimination rule for conjunction |   ⟦?P ∧ ?Q; ⟦?P; ?Q⟧ ⟹  ?R⟧ ⟹  ?R | |
| `disjE` | elimination rule for disjunc | ⟦?P ∨ ?Q; ?P ⟹ ?R; ?Q ⟹ ?R⟧ ⟹ ?R | |
| `disjI1 | introduction rule for left operand of disjunction | ?P ⟹ ?P ∨ ?Q | |
| `disjI2 | intrdocution rule for right operand of disjunction | ?Q ⟹ ?P ∨ ?Q | |
| `discjCI` | a form of disjunction introduction | (¬?Q=⇒?P)=⇒?P∨?Q | Allows removal of disjunction without deciding which disjunction to prove |
| `allI` | introduction fulre of universal quantification | (⋀x. ?P x) ⟹ ∀x. ?P x | |
| `allE` | eliminatino rule for universal quantification | ⟦∀x. ?P x; ?P ?x ⟹  ?R⟧ ⟹  ?R | |
| `impI` | introduction rule for implication | (?P ⟹ ?Q) ⟹ ?P ⟶ ?Q | |
| `impE` | elimination rule for implication |  ⟦?P ⟶ ?Q; ?P; ?Q ⟹ ?R⟧ ⟹ ?R | |
| `notI` | introduction rule for negation | (?P ⟹ False) ⟹ ¬ ?P | |
| `notE` | elimination rule for negation |  ⟦¬ ?P; ?P⟧ ⟹ ?R | |
| `exE` | elimination rule for existential quantification | ?P ?x ⟹ ∃x. ?P x | |
| `exI` | introduction rule for existential quantification | ⟦∃x. ?P x; ⋀x. ?P x ⟹ ?Q⟧ ⟹ ?Q | |

### Destruction rules
Take apart and destroy a premise. Applied by : `apply (drule ...)`
| rule name | explanation | type |
|---|---|---|
| `conjunct1` | exposes first operand of conjunction | ?P ∧ ?Q ⟹ ?P |
| `conjunct2` | exposes second operand of conjunction | ?P ∧ ?Q ⟹ ?Q |
| `spec` | specialise universal formula to a particular term | ∀x. ?P x ⟹ ?P ?x |
| `mp` | modus ponens | ⟦?P ⟶ ?Q; ?P⟧ ⟹ ?Q |
| `the_equality` | definition of definite description | ⟦?P ?a; ⋀x. ?P x ⟹ x = ?a⟧ ⟹ (THE x. ?P x) = ?a
| `some_equality` | definition of Hilbert's ε-operator | ⟦?P ?a; ⋀x. ?P x ⟹ x = ?a⟧ ⟹ (SOME x. ?P x) = ?a |

### Other rules
| rule name | explaination | type | |
|---|---|---|
| ssubst | Substitution rule: a predicate / function holds given the appropriate substiution | ⟦?t = ?s; ?P ?s⟧ ⟹ ?P ?t | Provides more control than simplification |

## Automation
Search works by backtracking to most recent application of unsafe rule:
- safe rule: a rule that can be applied backwards without losing information
- unsafe rule: a rule that loses information, maybe transforming sub-goal to be unsolvable
`clarify`: automatically simplifies the goal as much as possible using safe rules
`clarisimp`: interleaves `clarify` and `simp`
`force`: like auto combines classical reasoning and simplificaiton, but will fail (rather than change proof-state) when it can't fully prove goal. Also tries harder than `auto`, so can take longer to terminate. Also performs higher-order unification (unlike `blast`)
`best`: like `fast`, but uses best-first search rather than depth first search. Slower, but less susceptile to divergence.
TODO: maybe a table comparing automation methods?



## Finding help
### Query in jEdit
- `(_::nat)` is wildcard matching anything that is of type `nat`
- `simp: "..."`: searches specifically for rewrite rules
- `name: ...` searches for theorems by name
- can negate search criteria: `-name: foo` mathes all theorems who's name does not contain foo
- can find rules that much current goal using search criteria: `intro`, `elim` and `dest`


## Tips:
- function application binds more strongly than anything else `f x + y` means `(f x) + y`
- `=` binds very strongly. `¬¬P = P` means `¬¬(P = P)`
- need spaces after dots: `λx. x` not `λx.x`
- must define something before you use it
- best way to quantify over a variable `x` in list `xs` is to do, `x ∈ set xs`
- best to stick to using `Suc` and `O`, since definition of constant `1::nat` is not automatically unfolded by all commands

## Gotchas
- Simplification may not terminate due to automatic splitting of if-statements, may need to rewrite function to use `case` statements instead

## Misc
- <pre>apply <something else> by <assumption></pre> tries to proove all remaining subgoals using assumption (if successful no need for `done`)

## Jedit shortcuts
| symbol | what to enter |
|---|---|
|α | `\<alpha> |
| ι | THE |
| ε | SOME |
etc for greek letters
\<A>
\<AA>
|\<^sub> | subscript|
|\<^sup> | superscript|
| [| | ⟦ |
⇒ 
λ
¬
∧
∨
∈
×
≡ 
