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
| `datatype` | Provides an inductive definition for a type | <pre>dataype 'a list = Nil<br>| Cons 'a "'a list"<pre> | |

Tips:
- function application binds more strongly than anything else `f x + y` means `(f x) + y`
- `=` binds very strongly. `¬¬P = P` means `¬¬(P = P)`
- need spaces after dots: `λx. x` not `λx.x`
- must define something before you use it
- best way to quantify over a variable `x` in list `xs` is to do, `x ∈ set xs`

Jedit shortcuts
⇒ 
λ
¬
∧
∨
∈
