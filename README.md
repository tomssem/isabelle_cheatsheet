# isabelle_cheatsheet
A cheat sheet for Isabelle/ Isar/ HOL

| Items | Explanation | Example | Notes |
|---|---|---|---|
|`theory`|Named collection of types functions and theorems| <pre>Theory MyTheory<br>Imports Main Groups<br>begin<br>...<br>end</pre>|Name of file must be same as name of theory (so this example would go in `MyTheory.thy`.<br>Imported theoreies are called _parent theories_.<br>Can qualify clashing theories using, e.g., `MyTheory.foo` or `Main.foo`.|
| base types | | `bool`, `nat` etc. | |
| type constructors | Used to construct new types from existing types | `nat list` | Are written postfix |
| function types | | `T1 ⇒ T2 ⇒ T3 ⇒ T4` or equivalently `[T1, T2, T3] ⇒ T4` |Total functions only<br>`⇒` is right associative|
| type variables | Used in polymorphic types | `'a ⇒ 'a`<br>`list 'a`| Always preceded by `'` |
| if statement | | `if b the t1 else t2`| `b` is of type bool, `t1` and `t2` are of the same type | Need to be enclosed in parentheses |
| let statement | substitute all free occurences of a variable in an expression with another expression | `let x = 0 in x + x` | This example would get reduced to `0 + 0` |
| case statement | allows matching on the structual form of a term  | <pre>case l of<br> nil ⇒ ...|<br> Cons x xs ⇒ ...</pre> | Complex case patterns tend to yield complex proofs<br>Need to be enclosed in parentheses |
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
| `datatype` | Provides an inductive definition for a type | <pre>dataype 'a list = Nil<br>| Cons 'a "'a list"</pre> | |
| linear arithmetic | Formulas that involve only ¬, ∧, ∨, −→, =, ∀, ∃, =, ≤, <, +, -, `min` and `max` || |
| `arith` | proof methods that can solve linear arithmetic | | Exponential in number of -, `min` and `max`, since they are eliminated by case distinctions |
| tuples | simulated by nested pairs | `(1, "a", 1.0)::nat×string×real ` ≡ `(1, ("a", 1.0))::nat×(string×real)` | Therefore have, e.g.,  `fst(snd(1, "a", 1.0)) = "a"`.<br>Large tuples become unweildy, best to prefer records  |
| `unit` | types which contains exactly one element: `()` | | |
| `type_synonym` | Used to create new type that corresponds to an existing type | `type_synonym number = nat` | Used to improve readability of theories |
| dead/ live type arguments | type constructors allow recursion on a subset of their type arguments, these are called the _live_ arguments, all others are called _dead_ | `datatype (dead 'a, 'i) bigtree = Tip | Br 'a "'i ⇒ ('a,'i)bigtree"`| In example `'a` is type of what is being stored, `'i` is the index over which tree branches |
| Mutual recursion | Sed to define two dataypes that depend on each other | <pre>datatype T1 = ...<br/>and T2 =...</pre> | |

##Proof methods
###Simplification
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
###Induction
Heuristics:
- Induction used for proving theorems about recursive functions
- Induct on the argument that is recursed on
- generalize goal before induction by replacing constants with variables
- generalize goals for induction by universally quantifying all free variables
- the RHS of an equation should be simpler than the LHSdead
- `apply(induct_tac a and b)` used to induct on mutually recursive datatype

##Finding help
###Query in jEdit
- `(_::nat)` is wildcard matching anything that is of type `nat`
- `simp: "..."`: searches specifically for rewrite rules
- `name: ...` searches for theorems by name
- can negate search criteria: `-name: foo` mathes all theorems who's name does not contain foo


##Tips:
- function application binds more strongly than anything else `f x + y` means `(f x) + y`
- `=` binds very strongly. `¬¬P = P` means `¬¬(P = P)`
- need spaces after dots: `λx. x` not `λx.x`
- must define something before you use it
- best way to quantify over a variable `x` in list `xs` is to do, `x ∈ set xs`
- best to stick to using `Suc` and `O`, since definition of constant `1::nat` is not automatically unfolded by all commands

##Jedit shortcuts
⇒ 
λ
¬
∧
∨
∈
×
≡ 
